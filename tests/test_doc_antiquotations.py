r"""Antiquotations that name a declaration are build dependencies [doc-antiq].

Issue #44: `@{const foo}` is checked when its theory is processed, so it
fails the build when `foo` is gone, yet `unused` listed `foo` with no
evidence.  Only fact antiquotations (`@{thm bar}`) counted.  Now `const`,
`term`, `typ` and `type` count too, in both spellings, read by one scanner
whose bodies may hold a `}` (`@{term "{x. P x}"}`) and span lines.

Hand-computed for the fixture: `Client` imports `Base` and names `bar`,
`only_cart`, `only_at`, `in_term`, `in_set` and `in_list` in prose, so each
carries `doc` evidence.  `quiet` is named nowhere, and `foo` only as part of
`foo\<^sub>1`, which is a different name.
"""

import contextlib
import io
import os
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, os.path.dirname(__file__))
from isabelle_query import cli, commands, graph  # noqa: E402
from isabelle_query.model import CmdFlags  # noqa: E402

BASE = """\
theory Base
  imports Main
begin

lemma bar: "True" by simp
definition only_cart :: nat where "only_cart = 0"
definition only_at :: nat where "only_at = 0"
definition in_term :: "nat \\<Rightarrow> nat" where "in_term n = n"
definition in_set :: nat where "in_set = 0"
definition in_list :: nat where "in_list = 0"
definition quiet :: nat where "quiet = 0"
definition foo :: nat where "foo = 0"

end
"""

CLIENT = """\
theory Client
  imports Base
begin

text \\<open>The fact @{thm bar} is named here, in prose only.
  So are \\<^const>\\<open>only_cart\\<close> and @{const only_at}, and
  @{term "in_term
    0"} spans a line, @{term "{x. x = in_set}"} holds a brace,
  and @{term [show_types] "[in_list]"} has options and a list.
  @{term "foo\\<^sub>1"} names another constant.\\<close>

end
"""


class TheScanner(unittest.TestCase):

    def found(self, text):
        return [(k, b) for k, _s, _e, b in graph.doc_antiquotations(text)]

    def test_a_brace_in_a_string_is_the_body_s(self):
        self.assertEqual(self.found('@{term "{x. P x}"} @{const c}'),
                         [("term", ' "{x. P x}"'), ("const", " c")])

    def test_the_cartouche_spelling_nests(self):
        text = "\\<^term>\\<open>f \\<open>x\\<close>\\<close> after"
        self.assertEqual(self.found(text),
                         [("term", "\\<open>f \\<open>x\\<close>\\<close>")])

    def test_a_longer_kind_is_not_read_as_a_shorter_one(self):
        # `typeof` is no antiquotation; `thms` is not `thm` plus an `s`.
        self.assertEqual([k for k, _ in self.found(
            "@{typeof x} @{thms a b} @{lemma \"P\" by simp}")], ["thms"])

    def test_term_names(self):
        names = graph.antiquotation_names
        self.assertEqual(names("term", ' [show_types] "f [g, h] x"'),
                         {"f", "g", "h", "x"})
        self.assertEqual(names("typ", " \"'a list\""), {"list"})
        self.assertEqual(names("term", ' "?x + f\\<^sub>1"'),
                         {"f\\<^sub>1"})
        self.assertEqual(names("thm", " foo(2)[OF bar] Thy.baz"),
                         {"foo", "baz"})


class UnusedCountsThem(unittest.TestCase):

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        d = Path(self._tmp.name)
        (d / "Base.thy").write_text(BASE, encoding="utf-8")
        (d / "Client.thy").write_text(CLIENT, encoding="utf-8")
        (d / "ROOT").write_text("session Repro = HOL +\n  theories Client\n",
                                encoding="utf-8")
        cli._ROOT_OVERRIDE = d
        self.sections = cli.load_index()

    def tearDown(self):
        cli._ROOT_OVERRIDE = None
        self._tmp.cleanup()

    def test_every_named_entry_has_doc_evidence(self):
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            commands.cmd_unused(self.sections, CmdFlags())
        rows = {ln.split()[1]: ln for ln in buf.getvalue().splitlines()
                if "lines)" in ln}
        named = {n for n, r in rows.items() if r.endswith("[evidence: doc]")}
        self.assertEqual(named, {"bar", "only_cart", "only_at", "in_term",
                                 "in_set", "in_list"})
        self.assertEqual(set(rows) - named, {"quiet", "foo"})


if __name__ == "__main__":
    unittest.main()
