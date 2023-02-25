from sanic import Sanic, Request
from sanic import response as res

import os

app = Sanic(__name__)
app.static("/static", "./static")

@app.route("/")
async def test(req):
    return res.text("I\'m a teapot", status=418)

@app.route("/test")
@app.ext.template("level.html")
async def level(request: Request):
    return {}

if __name__ == "__main__":
    port = int(os.environ.get('PORT', 5000))
    app.run(host="0.0.0.0", port=port)