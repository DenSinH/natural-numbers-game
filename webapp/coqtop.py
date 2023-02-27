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

class VernacularError(Exception):
    pass


def reduce_code(code):
    # proof must end in .
    code = re.sub(_EMPTY_LAST_TACTIC, "", code)

    # don't allow any keywords
    if re.search(_VERNACULAR, code):
        raise VernacularError()
    return code
