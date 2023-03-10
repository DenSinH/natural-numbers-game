from jinja2.filters import FILTERS
from sanic import Sanic, Request, Websocket
from sanic import response
from sanic import exceptions
import asyncio
from websockets.exceptions import ConnectionClosed

import json
import re
import os

from coqtop import *
from game import *



def _format_paragraphs(text):
    return re.sub(r"\s*\n\s*\n\s*", "</br></br>", text.strip("\n"))

def _format_inline_code(text):
    return re.sub(r"`(.*?)`", r'<pre class="inline-code"><code class="language-coq">\1</code></pre>', text)

def format_text(text):
    sections  = text.split("```")
    formatted = []
    for i, section in enumerate(sections):
        code = (i % 2) == 1
        if code:
            if section.startswith("plaintext"):
                plaintext = section.split("plaintext", 1)[1].strip("\n")
                formatted.append(f'<pre><code class="language-plaintext">{plaintext}</code></pre>')
            else:
                stripped = section.strip("\n")
                formatted.append(f'<pre><code class="language-coq">{stripped}</code></pre>')
        else:
            formatted.append(_format_paragraphs(_format_inline_code(section)))
    return "\n".join(formatted)

def split_theorem_line(text):
    return ":\n    ".join(text.rsplit(":", 1))


SECURE = "SECURE" not in os.environ or int(os.environ["SECURE"])

app = Sanic(__name__)
app.static("/static", "./static")
app.ext.environment.filters["format_text"] = format_text
app.ext.environment.filters["split_theorem_line"] = split_theorem_line
app.ext.environment.globals["WEBSOCKET_SCHEME"] = "wss" if SECURE else "ws"


@app.get("/")
@app.ext.template("index.html")
async def index(req):
    return {
        "WORLDS": WORLDS
    }


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

    convert_level_data = lambda x : x if x is None else dict(zip(("_world", "_level"), x))
    next_level = convert_level_data(get_next_level(world, level))
    prev_level = convert_level_data(get_prev_level(world, level))

    return {
        "host": request.host,
        "tactics": tactics,
        "theorems": theorems,
        "world": world,
        "_world": _world,
        "level": level,
        "_level": _level,
        "next_level": next_level,
        "prev_level": prev_level,
        "WORLDS": WORLDS
    }


_NON_ASCII_FILTER = re.compile(r"[^ -~\n]")

@app.websocket("/compile/<_world:int>/<_level:int>")
async def compile(request: Request, ws: Websocket, _world: int, _level: int):
    try:
        world, level = get_level(_world, _level)
    except IndexError as e:
        raise exceptions.NotFound(*e.args)

    coqtop = await Coqtop.create()

    # feed (reduced) world source file up to level
    default_goal = None
    for line in world["reduced_file"]:
        if isinstance(line, int):
            if line == level["level"]:
                break
        else:
            default_goal = await coqtop.feed_line(line)
    if default_goal is None:
        raise EOFError(f"No goal in level {_level} in world {_world}")

    # start proof
    await coqtop.feed_line("Proof.")

    async def send(goal=None, messages=None, errors=None):
        await ws.send(json.dumps({
            "goal": goal or "",
            "messages": messages or [],
            "errors": errors or [],
            "completed": goal.strip() == "No more subgoals."
        }))
    # send default goal to start proof
    await send(goal=default_goal)

    # keep track of previous code to reduce coqtop usage
    cache = {}
    try:
        async for msg in ws:
            try:
                # commas in input (rewrite add_zero, zero_add) give double output
                # filter out any non-ascii characters to prevent people messing
                # with coqtop
                code = reduce_code(re.sub(_NON_ASCII_FILTER, "", msg).replace(",", ",\n").strip())
            except VernacularError:
                await send(messages=["Do not send any vernacular in your code!"])
                continue

            if len(code) > 500:
                await send(messages=["Code too long, try to stay under 500 characters"])
                continue

            # prevent unnecessary processing
            # check if result has been gotten before
            if code in cache:
                await send(goal=cache[code])
                continue
            if not code:
                # empty editor, send default goal
                await send(goal=default_goal)
                continue
        
            # restart proof
            # first feed dot to "finish" any in progress commands
            # also feed comment end marker to cut off any comments
            await coqtop.feed_line("*).")
            await coqtop.feed_line("Restart.")
            
            # feed current proof output
            for line in code.split("\n"):
                output = await coqtop.feed_line(line)

                # break if an error happens in a line
                if "Toplevel input" in output:
                    break
            
            # get current goal
            output = output.strip()
            
            # if there was no error message
            if "Toplevel input" not in output:
                output = await coqtop.feed_line("Show.")

            cache[code] = output
            await send(goal=output)
    except asyncio.CancelledError:
        # connection closed
        pass
    finally:
        # close coqtop whenever something happens
        await coqtop.close()

if __name__ == "__main__":
    import sys

    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 80)), debug="--debug" in sys.argv)