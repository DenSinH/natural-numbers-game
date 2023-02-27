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
            "errors": errors or []
        }))

    # send default goal to start proof
    await send(goal=default_goal)

    # keep track of previous code to reduce coqtop usage
    cache = {}
    try:
        async for msg in ws:
            try:
                code = reduce_code(msg.strip())
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
            await coqtop.feed_line("Restart.")

            # feed current proof output
            for line in code.split("\n"):
                output = await coqtop.feed_line(line)
            
            output = output.strip()
            if not output:
                # get current goal
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
    app.run(host="0.0.0.0", port=80)