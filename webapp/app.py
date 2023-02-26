from jinja2.filters import FILTERS
from sanic import Sanic, Request, Websocket
from sanic import response
from sanic import exceptions

import json
import re
import os

from coqtop import Coqtop


def format_code_in_text(text):
    return re.sub(r"`(.*?)`", r"<code>\1</code>", text)


def format_paragraphs_in_text(text):
    return "<p>" + re.sub(r"\s*\n\s*\n\s*", "</p><p>", text) + "</p>"

SECURE = "SECURE" not in os.environ or int(os.environ["SECURE"])

app = Sanic(__name__)
app.static("/static", "./static")
app.ext.environment.filters["format_code_in_text"]       = format_code_in_text
app.ext.environment.filters["format_paragraphs_in_text"] = format_paragraphs_in_text
app.ext.environment.globals["WEBSOCKET_SCHEME"] = "wss" if SECURE else "ws"

from game import *


@app.get("/")
@app.ext.template("index.html")
async def index(req):
    return {}


@app.get("/level")
async def level_redirect(request: Request):
    return response.redirect(app.url_for("level", world=0, level=0))


@app.get("/level/<_world:int>/<_level:int>")
@app.ext.template("level.html")
async def level(request: Request, _world: int, _level: int):
    try:
        world, level = get_level(_world, _level)
    except IndexError as e:
        raise exceptions.NotFound(*e.args)

    tactics  = get_tactics(world, level)
    theorems = get_theorems(world, level)

    return {
        "host": request.host,
        "tactics": tactics,
        "theorems": theorems,
        "world": world,
        "_world": _world,
        "level": level,
        "_level": _level,
        "WORLDS": WORLDS
    }


_EMPTY_LAST_TACTIC = re.compile(r"([^\.]+)\Z")
_VERNACULAR_LIST = [
    'Abort', 'About', 'Add', 'All', 'Arguments', 'Asymmetric', 'Axiom',
    'Bind',
    'Canonical', 'Check', 'Class', 'Close', 'Coercion', 'CoFixpoint', 'Comments',
    'CoInductive', 'Context', 'Constructors', 'Contextual', 'Corollary',
    'Defined', 'Definition', 'Delimit',
    'Fail',
    'Eval',
    'End', 'Example', 'Export',
    'Fact', 'Fixpoint', 'From',
    'Global', 'Goal', 'Graph',
    'Hint', 'Hypotheses', 'Hypothesis',
    'Implicit', 'Implicits', 'Import', 'Inductive', 'Infix', 'Instance',
    'Lemma', 'Let', 'Local', 'Ltac',
    'Module', 'Morphism',
    'Next', 'Notation',
    'Obligation', 'Open',
    'Parameter', 'Parameters', 'Prenex', 'Print', 'Printing', 'Program',
    'Patterns', 'Projections', 'Proof',
    'Proposition',
    'Qed',
    'Record', 'Relation', 'Remark', 'Require', 'Reserved', 'Resolve', 'Rewrite',
    'Save', 'Scope', 'Search', 'SearchAbout', 'Section', 'Set', 'Show', 'Strict', 'Structure',
    'Tactic', 'Time', 'Theorem', 'Types',
    'Unset',
    'Variable', 'Variables', 'View'
]
_VERNACULAR = re.compile(r"(\W|\A)(" + "|".join(_VERNACULAR_LIST) + r")(\W|\Z)")

@app.websocket("/compile/<_world:int>/<_level:int>")
async def compile(request: Request, ws: Websocket, _world: int, _level: int):
    try:
        world, level = get_level(_world, _level)
    except IndexError as e:
        raise exceptions.NotFound(*e.args)

    coqtop = await Coqtop.create()

    # feed (reduced) world source file up to level
    goal = None
    for line in world["reduced_file"]:
        if isinstance(line, int):
            if line == level["level"]:
                break
        else:
            goal = await coqtop.feed_line(line)
    if goal is None:
        raise EOFError(f"No goal in level {_level} in world {_world}")

    # start proof
    goal = await coqtop.feed_line("Proof.")

    async def send(goal=None, messages=None, errors=None):
        await ws.send(json.dumps({
            "goal": goal or "",
            "messages": messages or [],
            "errors": errors or []
        }))
    
    prev_code = None
    while True:
        code = (await ws.recv()).strip()

        # proof must end in .
        code = re.sub(_EMPTY_LAST_TACTIC, "", code)

        # don't allow any keywords
        if re.search(_VERNACULAR, code):
            await send(messages=["Do not send any vernacular in your code!"])
            continue 

        # prevent unnecessary processing
        if code == prev_code:
            continue
        prev_code = code
        if not code:
            continue
      
        # restart proof
        await coqtop.feed_line("Restart.")

        # feed current proof output
        output = None
        for line in code.split("\n"):
            output = await coqtop.feed_line(line)

        await send(goal=output)

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=80)