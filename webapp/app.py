from sanic import Sanic, Request, Websocket
from sanic import response as res

import json

app = Sanic(__name__)
app.static("/static", "./static")

@app.route("/")
@app.ext.template("index.html")
async def index(req):
    return {}

@app.route("/level")
@app.ext.template("level.html")
async def level(request: Request):
    return {
        "host": request.host,
        "protocol": "ws" if request.scheme == "http" else "wss"
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