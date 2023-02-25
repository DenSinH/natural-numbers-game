from jinja2.filters import FILTERS
from sanic import Sanic, Request, Websocket
from sanic import response
from sanic import exceptions

import json
import re
import os


def format_code_in_text(text):
    return re.sub(r"`(.*?)`", r"<code>\1</code>", text)

SECURE = "SECURE" not in os.environ or int(os.environ["SECURE"])

app = Sanic(__name__)
app.static("/static", "./static")
app.ext.environment.filters["format_code_in_text"] = format_code_in_text
app.ext.environment.globals["WEBSOCKET_SCHEME"] = "wss" if SECURE else "ws"

from game import *


@app.get("/")
@app.ext.template("index.html")
async def index(req):
    return {}


@app.get("/level")
async def level_redirect(request: Request):
    return response.redirect(app.url_for("level", world=0, level=0))


@app.get("/level/<world:int>/<level:int>")
@app.ext.template("level.html")
async def level(request: Request, world: int, level: int):
    try:
        world, level = get_level(world, level)
    except IndexError as e:
        raise exceptions.NotFound(*e.args)

    tactics  = get_tactics(world, level)
    theorems = get_theorems(world, level)

    return {
        "host": request.host,
        "tactics": tactics,
        "theorems": theorems,
        "world": world,
        "level": level,
        "WORLDS": WORLDS
    }


@app.websocket("/compile")
async def compile(request: Request, ws: Websocket):
    while True:
        code = await ws.recv()
        # todo: coqtop

        await ws.send(json.dumps({
            "goal": "goal",
            "messages": [],
            "errors": []
        }))

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=80)