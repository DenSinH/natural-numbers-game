from sanic import Sanic, Request, Websocket
from sanic import response as res

import json

app = Sanic(__name__)
app.static("/static", "./static")

@app.route("/")
async def test(req):
    return res.text("I\'m a teapot", status=418)

@app.route("/test")
@app.ext.template("level.html")
async def level(request: Request):
    return {"host": request.host}

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