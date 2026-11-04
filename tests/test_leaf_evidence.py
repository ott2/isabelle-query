r"""`unused` reports evidence per uncited entry, not a verdict [leaf-evidence].

Issue #22: a dead-code audit keeps the results a development is for.  The
keyword is one sign of that — `theorem`, `corollary`, `proposition` — but a
weak one, since some theorems are scaffolding and a lemma proved "for
independent interest" is not dead.  So `unused` names what it found rather
than deciding: an entry with evidence is live for the `-r` cascade, as a
`--keep` name is, and `--evidence mark` (the default) lists it tagged while
`hide` leaves only the entries with none.

Hand-computed for the fixture: `headline` is uncited and stated as a
corollary, so `helper` (cited only by it) must not cascade; `scaffold` is a
plain uncited lemma, so `helper2` (cited only by it) cascades at depth 1.

`doc` evidence is a fact antiquotation naming the entry, which the citation
graph deliberately does not count.  It is scoped as a citation is: `Other`
does not import `Base`, so its `@{thm unseen}` names some other `unseen`.
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

LEAF = """\
theory Leaf
  imports Main
begin

lemma helper: "True \\<or> False"
  by simp

corollary headline: "True \\<or> False"
  by (rule helper)

lemma helper2: "False \\<longrightarrow> True"
  by simp

lemma scaffold: "False \\<longrightarrow> True"
  by (rule helper2)

end
"""


class EvidencePerLeaf(unittest.TestCase):

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        d = Path(self._tmp.name)
        (d / "Leaf.thy").write_text(LEAF, encoding="utf-8")
        (d / "ROOT").write_text("session Leaf = HOL +\n  theories Leaf\n",
                                encoding="utf-8")
        cli._ROOT_OVERRIDE = d
        self.sections = cli.load_index()

    def tearDown(self):
        cli._ROOT_OVERRIDE = None
        self._tmp.cleanup()

    def rows(self, **kw):
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            commands.cmd_unused(self.sections, CmdFlags(**kw))
        return [" ".join(ln.split()) for ln in buf.getvalue().splitlines()[4:]
                if ln.strip()]

    def test_mark(self):
        rows = self.rows()
        self.assertEqual([r.split()[:2] for r in rows],
                         [["COROLLARY", "headline"], ["LEMMA", "scaffold"]])
        self.assertTrue(rows[0].endswith("[evidence: corollary]"))
        self.assertNotIn("evidence", rows[1])

    def test_the_cascade_stops_at_a_corollary(self):
        rows = self.rows(recursive=True)
        self.assertEqual([r.split()[1] for r in rows],
                         ["headline", "helper2", "scaffold"])
        self.assertTrue(any(r.startswith("LEMMA helper2 ")
                            and "[cascade depth 1]" in r for r in rows))

    def test_hide_leaves_the_candidates(self):
        self.assertEqual([r.split()[1] for r in
                          self.rows(recursive=True, evidence="hide")],
                         ["helper2", "scaffold"])

    def test_keep_wins(self):
        # A name the user keeps is not reported at all, evidence or not.
        rows = self.rows(keep=frozenset({"headline", "scaffold"}))
        self.assertEqual(rows, [])

    def test_the_old_flag_spelling_still_parses(self):
        p = cli._build_parser()
        for flag in ("--evidence", "--implicit"):
            ns = p.parse_args(["unused", flag, "hide"])
            self.assertEqual(cli._flags_from_ns(ns).evidence, "hide")


CHAIN = """\
theory Chain
  imports Main
begin

lemma base: "True"
  by simp

theorem mid: "True"
  by (rule base)

theorem head: "True"
  by (rule mid)

corollary cor: "True"
  by (rule head)

theorem t2: "True"
  by simp

lemma sc: "True"
  by (rule t2)

end
"""


class EvidenceEndsTheCascade(unittest.TestCase):
    """Issue #41: an entry with evidence is live for the entries it cites,
    and that includes entries that carry evidence of their own.  `cor` is
    uncited, but `head` is a theorem it cites, so `head` is not dead, nor is
    anything below it.  `t2` is a theorem cited only by `sc`, a dead plain
    lemma, so it is listed at depth 1: the one way an entry with evidence
    joins the cascade."""

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        d = Path(self._tmp.name)
        (d / "Chain.thy").write_text(CHAIN, encoding="utf-8")
        (d / "ROOT").write_text("session C = HOL +\n  theories Chain\n",
                                encoding="utf-8")
        cli._ROOT_OVERRIDE = d
        self.sections = cli.load_index()

    def tearDown(self):
        cli._ROOT_OVERRIDE = None
        self._tmp.cleanup()

    def rows(self, **kw):
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            commands.cmd_unused(self.sections, CmdFlags(**kw))
        return {ln.split()[1]: " ".join(ln.split())
                for ln in buf.getvalue().splitlines() if "lines)" in ln}

    def test_a_theorem_cited_by_a_theorem_is_live(self):
        rows = self.rows(recursive=True)
        self.assertEqual(sorted(rows), ["cor", "sc", "t2"])
        self.assertNotIn("cascade depth", rows["cor"])
        self.assertIn("[cascade depth 1]", rows["t2"])

    def test_it_agrees_with_keep(self):
        # Keeping the corollary by name leaves the same cascade below it.
        rows = self.rows(recursive=True, keep=frozenset({"cor"}))
        self.assertEqual(sorted(rows), ["sc", "t2"])


BASE = """\
theory Base
  imports Main
begin

lemma shown: "True \\<or> False"
  by simp

lemma cart_one: "True \\<or> True"
  by simp

lemma unseen: "False \\<longrightarrow> False"
  by simp

end
"""

DOC = """\
theory Doc
  imports Base
begin

text \\<open>The result: @{thm [display] shown(1)}, and \\<^thm>\\<open>Base.cart_one\\<close>,
  and @{lemma "True" by simp}.\\<close>

end
"""

OTHER = """\
theory Other
  imports Main
begin

text \\<open>@{thm unseen}\\<close>

end
"""


class DocEvidence(unittest.TestCase):

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        d = Path(self._tmp.name)
        for name, text in (("Base", BASE), ("Doc", DOC), ("Other", OTHER)):
            (d / f"{name}.thy").write_text(text, encoding="utf-8")
        (d / "ROOT").write_text("session S = HOL +\n  theories Doc Other\n",
                                encoding="utf-8")
        cli._ROOT_OVERRIDE = d
        self.sections = cli.load_index()

    def tearDown(self):
        cli._ROOT_OVERRIDE = None
        self._tmp.cleanup()

    def rows(self, **kw):
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            commands.cmd_unused(self.sections, CmdFlags(**kw))
        return {ln.split()[1]: " ".join(ln.split())
                for ln in buf.getvalue().splitlines() if "lines)" in ln}

    def test_a_visible_mention_is_evidence(self):
        rows = self.rows()
        self.assertEqual(sorted(rows), ["cart_one", "shown", "unseen"])
        self.assertTrue(rows["shown"].endswith("[evidence: doc]"))
        self.assertTrue(rows["cart_one"].endswith("[evidence: doc]"))
        self.assertNotIn("evidence", rows["unseen"])

    def test_name_reach_counts_the_unscoped_mention(self):
        # The control: without the closure rule, `Other`'s mention lands.
        self.assertTrue(self.rows(reach="name")["unseen"]
                        .endswith("[evidence: doc]"))


if __name__ == "__main__":
    unittest.main()
