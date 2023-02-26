import asyncio
import asyncio.subprocess as subprocess


class Coqtop():

    def __init__(self, proc):
        self._proc = proc

    @classmethod
    async def create(cls):
        self = cls(await Coqtop._spawn())
        await self._wait_for_command_complete()
        return self

    @staticmethod
    async def _spawn():
        return await subprocess.create_subprocess_shell(
            "coqtop -Q . NaturalNumbers",
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            cwd="./coq"
        )

    async def _wait_for_command_complete(self):
        out = (await self._proc.stdout.readuntil(b"< ")).decode()
        # remove last line (state <)
        return "\n".join(out.split("\n")[:-1])

    async def feed_line(self, line: str) -> str:
        line = line.strip()
        self._proc.stdin.write(f"{line}\n".encode())
        await self._proc.stdin.drain()
        return await self._wait_for_command_complete()

    async def close(self):
        # ctrl-Z exit command
        self._proc.stdin.write(b"\x1a\n")
        await self._proc.stdin.drain()
        out, err = await self._proc.communicate()