import asyncio
import asyncio.subprocess as subprocess

import re


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

    async def _flush_stdout(self):
        # kind of hacky
        await self._proc.stdout.read(len(self._proc.stdout._buffer))

    async def _wait_for_command_complete(self):
        out = (await self._proc.stdout.readuntil(b"< ")).decode()
        # wait until last line does not start with a space
        while True:
            if "\n" not in out:
                break
            last_line = out.rsplit("\n", 1)[1]
            if not last_line:
                # this should not happen, but just in case
                break
            if not last_line[0].isspace():
                # not of the form goal <
                break

            out += (await self._proc.stdout.readuntil(b"< ")).decode()

        # remove last line (state <)
        return out.rsplit("\n", 1)[0]

    async def _write_stdin(self, bytes):
        await self._flush_stdout()
        self._proc.stdin.write(bytes)
        await self._proc.stdin.drain()

    async def feed_line(self, line: str) -> str:
        line = line.strip()
        if not line:
            return ""
        await self._write_stdin(f"{line}\n".encode())
        return await self._wait_for_command_complete()

    async def close(self):
        # ctrl-Z exit command
        await self._write_stdin(b"\x1a\n")
        out, err = await self._proc.communicate()


_EMPTY_LAST_TACTIC = re.compile(r"([\s\w,\[\]\|\>?(){};]+)\Z")
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

class VernacularError(Exception):
    pass


def reduce_code(code):
    # proof must end in . or - or something
    # remove any tactics that are not done writing
    code = re.sub(_EMPTY_LAST_TACTIC, "", code)

    # don't allow any keywords
    if re.search(_VERNACULAR, code):
        raise VernacularError()
    return code
