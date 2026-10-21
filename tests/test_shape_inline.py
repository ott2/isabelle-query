r"""Proofs written on the goal statement's own line (issue #5).

`lemma a: "P" by simp` and the same proof written on the next line are the same
proof, and must produce the same shape record.  They did not: `_scan_steps` read
the shared line from column 0, `_command_prefix` cut it at the statement's first
quote, and the resulting `lemma a: ` led no step family — so the scan returned
no steps, `analyze_proof` returned None, and the entry left the census entirely.
Because the spelling is preferred for *trivial* proofs, the loss biased every
aggregate rather than thinning it evenly: 1,870 proofs over 120 AFP entries.

Three spellings put a proof on a statement line, and they need different
evidence to recognise (see `shape._inline_proof_col`), so each is pinned here:
the declaration line, a later line of a multi-line declaration, and a bare
statement term past `decl_end_line`.  The equivalence tests are written against
the OTHER spelling rather than against literal expected values, since "the two
spellings agree" is the property that matters and it cannot drift.

What is NOT pinned here, deliberately: the two statement-text guards inside
`_inline_proof_col`.  They are unreachable on real sources (0 of 43,828 AFP
proofs take a different column without them), so no fixture can exercise them —
a test asserting otherwise would be testing a case Isar does not produce.  The
guards exist to keep a future `parsing` change from turning a step into a mask,
and that is stated in the function, not simulated here.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(__file__))
from support import section_from  # noqa: E402
from isabelle_query import shape  # noqa: E402


def _sec(body):
    return section_from(f"theory T imports Main begin\n{body}\nend\n", "T")


def _entry(sec, name):
    return next(e for e in sec.entries if e.name == name)


def _steps(sec, name):
    return shape._scan_steps(sec, _entry(sec, name))


def _shape(steps):
    """(kw, kind) per step — the classification skeleton, line numbers dropped
    so the two spellings of one proof are directly comparable."""
    return [(s.kw, s.kind) for s in steps]


class InlineProofIsScanned(unittest.TestCase):
    """The three ways a proof can share a line with its statement."""

    def test_on_the_declaration_line(self):
        # `lemma a: "P a" by simp` — the common one-liner.
        sec = _sec('lemma a: "P a" by simp\n'
                   'lemma b: "P b"\n'
                   '  by simp')
        self.assertEqual(_shape(_steps(sec, "a")), [("by", "closing")])
        self.assertEqual(_shape(_steps(sec, "a")), _shape(_steps(sec, "b")))

    def test_on_a_later_line_of_the_declaration(self):
        # `parsing` scans the whole declaration span for an inline proof, so the
        # shared line need not be the first one.  74 AFP facts.
        sec = _sec('lemma g:\n'
                   '  assumes "A g"\n'
                   '  shows "P g" by simp')
        e = _entry(sec, "g")
        self.assertGreater(e.proof_line, e.thy_line)      # not the decl line
        self.assertLessEqual(e.proof_line, e.decl_end_line)  # still the decl
        self.assertEqual(_shape(_steps(sec, "g")), [("by", "closing")])

    def test_after_a_bare_term_past_the_declaration_end(self):
        # `lemma c:` / `"P c" by auto`.  The outer view of the second line
        # STARTS with `by`, so `PROOF_RE` claims it through the ordinary branch
        # and `decl_end_line` never covers it — a declaration-span test alone
        # cannot see this form, yet statement text still precedes the proof.
        # 324 AFP facts, more than the previous case.
        sec = _sec('lemma c:\n'
                   '  "P c" by auto')
        e = _entry(sec, "c")
        self.assertGreater(e.proof_line, e.decl_end_line)
        self.assertEqual(_shape(_steps(sec, "c")), [("by", "closing")])

    def test_a_one_liner_reaches_the_census(self):
        """The user-visible consequence: `analyze_proof` yields a record, so the
        entry appears in `shape census` / `steps` instead of vanishing."""
        sec = _sec('lemma a: "P a" by simp')
        self.assertIsNotNone(shape.analyze_proof(sec, _entry(sec, "a")))

    def test_inline_plumbing_and_block_openers(self):
        # Whatever the shared line would classify as on a line of its own, it
        # classifies as here — `using` leads plumbing, not closing.
        sec = _sec('lemma d: "P d" using refl by simp\n'
                   'lemma e: "P e"\n'
                   '  using refl by simp')
        self.assertEqual(_shape(_steps(sec, "d")),
                         [("using", "plumbing"), ("by", "closing")])
        self.assertEqual(_shape(_steps(sec, "d")), _shape(_steps(sec, "e")))


class OnlyStatementTextIsBlanked(unittest.TestCase):
    """The prefix is blanked only when it is statement text.  Masking a command
    would DELETE a step, which is worse than the bug being fixed."""

    def test_a_structured_proof_is_unchanged(self):
        # The regression guard, and only that: a proof whose body carries a
        # mid-line ` by` (`from a have b: "R i" by simp` — a column the naive
        # rule would mask) keeps every step.  It does NOT exercise the
        # statement-text guards: `_inline_proof_col` is asked only about
        # `proof_line`, which here is the `proof -` line, so the body lines are
        # never candidates for masking in the first place.
        sec = _sec('lemma i: "P i"\n'
                   'proof -\n'
                   '  from a have b: "R i" by simp\n'
                   '  show "P i" by (simp add: b)\n'
                   'qed')
        self.assertEqual(shape._inline_proof_col(sec, _entry(sec, "i")), 0)
        self.assertEqual(_shape(_steps(sec, "i")),
                         [("from", "plumbing"), ("have", "goal"),
                          ("by", "closing"), ("show", "goal"),
                          ("by", "closing"), ("qed", "closing")])

    def test_an_ordinary_indented_proof_line_needs_no_column(self):
        """0 for the ordinary case is also what keeps the scan from copying the
        theory's line list once per proof."""
        sec = _sec('lemma b: "P b"\n'
                   '  by simp')
        self.assertEqual(shape._inline_proof_col(sec, _entry(sec, "b")), 0)

    def test_the_column_lands_on_the_proof_keyword(self):
        sec = _sec('lemma a: "P a" by simp')
        col = shape._inline_proof_col(sec, _entry(sec, "a"))
        line = sec.source()[_entry(sec, "a").proof_line - 1]
        self.assertEqual(line[col:].strip(), "by simp")


class StatementSpansAndLineNumbers(unittest.TestCase):
    r"""What the masking must not disturb: a goal step's own proposition, and
    the line numbers consumers resolve against `source()`.

    Blanking vs. slicing the prefix is NOT pinned here, because the two cannot
    be told apart: `_extract_statement` reads the same mutated list the scan
    built, so a slice is self-consistent too.  Blanking is a robustness choice
    (a column in this view keeps meaning what it means in `source()`), and it is
    argued in the function rather than asserted by a test that would pass either
    way.
    """

    def test_an_inline_goal_extracts_its_own_proposition(self):
        # The FIRST `"` on this line belongs to the lemma's own statement.  Read
        # from column 0 the step would report `P e`; the proposition of the
        # `show` is `Q e`.
        sec = _sec('lemma e: "P e" proof - show "Q e" by simp qed')
        steps = _steps(sec, "e")
        self.assertEqual([s.stmt_text for s in steps if s.kind == "goal"],
                         ["Q e"])
        # And the `proof` in mid-line opens a block, which the `qed` closes.
        self.assertEqual([(s.kw, s.depth) for s in steps],
                         [("show", 0), ("by", 0), ("qed", 0)])

    def test_step_lines_are_real_source_lines(self):
        sec = _sec('lemma a: "P a" by simp')
        step, = _steps(sec, "a")
        self.assertEqual(step.line, _entry(sec, "a").thy_line)
        self.assertIn("by simp", sec.source()[step.line - 1])


if __name__ == "__main__":
    unittest.main()
