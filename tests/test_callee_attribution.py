r"""A callee row names a declaration the citing theory can SEE
[callee-attribution].

Issue #18: NDTHT declares `sim_tape` twice, in two sessions that do not import
each other, and `callees pass_block_count` reported the one its theory cannot
reach.  The call graph is keyed by NAME and `--reach closure` keeps an edge
when SOME declaration is visible; the row then named one first-wins, by load
order.  A row now lists every declaration the seed's theory can see, nearest
by import depth first.

Here `Arms` loads first and declares `tape`; `Guess` declares it too.  Only
`Guess` is in `Sim`'s closure, so first-wins named the wrong one.  Real files,
because visibility reads `imports` clauses off disk.
"""

import contextlib
import io
import os
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, os.path.dirname(__file__))
from isabelle_query import cli, commands  # noqa: E402
from isabelle_query.model import CmdFlags  # noqa: E402

THYS = {
    "Arms": 'theory Arms\nimports Main\nbegin\n'
            'definition tape :: "nat" where "tape = 0"\nend\n',
    "Guess": 'theory Guess\nimports Main\nbegin\n'
             'definition tape :: "nat" where "tape = 1"\n'
             'lemma local_use: "tape = 1" by (simp add: tape_def)\nend\n',
    "Sim": 'theory Sim\nimports Guess\nbegin\n'
           'lemma pass_lemma: "tape = 1" by (simp add: tape_def)\nend\n',
    "Top": 'theory Top\nimports Sim\nbegin\n'
           'lemma top_lemma: "True" using pass_lemma by simp\nend\n',
    # Both visible: `Guess` directly, `Arms` through `Mid`.
    "Mid": 'theory Mid\nimports Arms\nbegin\nend\n',
    "Near": 'theory Near\nimports Mid Guess\nbegin\n'
            'lemma near_lemma: "tape = tape" by simp\nend\n',
}

ARMS = "tape (DEF) — Arms [L4]"
GUESS = "tape (DEF) — Guess [L4]"


class Fixture(unittest.TestCase):

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        d = Path(self._tmp.name)
        for name, text in THYS.items():
            (d / f"{name}.thy").write_text(text, encoding="utf-8")
        (d / "ROOT").write_text(
            "session Demo = HOL +\n  theories\n"
            + "".join(f"    {n}\n" for n in THYS), encoding="utf-8")
        cli._ROOT_OVERRIDE = d
        self.sections = cli.load_index()

    def tearDown(self):
        cli._ROOT_OVERRIDE = None
        self._tmp.cleanup()

    def rows(self, name, **kw):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            commands.cmd_callees(self.sections, name, CmdFlags(**kw))
        return [ln.strip() for ln in out.getvalue().splitlines()
                if ln.strip().startswith("tape")]


class TheVisibleDeclaration(Fixture):

    def test_first_wins_would_name_the_invisible_one(self):
        # The premise of the fixture: load order puts `Arms` first.
        self.assertEqual("Arms", self.sections[0].theory)

    def test_direct(self):
        self.assertEqual(self.rows("pass_lemma"), [GUESS])

    def test_recursive(self):
        # Whatever `Sim` sees, `Top` sees: the seed's closure scopes every depth.
        self.assertEqual(self.rows("top_lemma", recursive=True), [GUESS])

    def test_several_visible_nearest_first(self):
        # `Guess` is a direct import, `Arms` two hops away: depth beats load
        # order.
        self.assertEqual(self.rows("near_lemma"), [GUESS, ARMS])

    def test_name_mode_lists_every_declaration(self):
        self.assertEqual(self.rows("pass_lemma", reach="name"), [ARMS, GUESS])

    def test_external_asks_the_visible_declaration(self):
        # `local_use` cites its own theory's `tape`; first-wins called it
        # cross-theory because `Arms` is not `Guess`.
        self.assertEqual(self.rows("local_use", external=True), [])


if __name__ == "__main__":
    unittest.main()
