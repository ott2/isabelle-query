r"""`proposition` declares a fact, exactly as `lemma` does [decl-commands].

Isabelle's `Pure.thy:54` declares `theorem` `lemma` `corollary` `proposition`
together on ONE line as `thy_goal_stmt`, and `Pure.thy:574-577` registers all
four through the same combinator with the same `false` flag — they differ only
in the word they print.  `DECL_RE` knew three of them and stopped, so a
`proposition` was not an entry.

The loss is not just the missing record, and that is what makes it worth
fixing rather than tidy.  A command `query` cannot see also does not BOUND the
entry above it: `compute_spans` sets `thy_end` from the next entry's
`src_start`, so the preceding `lemma` swallowed the proposition's proof and
`shape` counted those steps as the lemma's.  Measured corpus-wide before the
fix: 1,700 propositions over 11,604 theories, owning 6,798 lines of proof text
that were either uncounted or billed to the wrong entry.

The tag is `LEMMA`, riding with `corollary` rather than with `theorem`.  The
LEMMA/THEOREM split is presentational — it feeds `summary`'s two counts — and
has no counterpart in Isabelle, where all four are one command.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(__file__))
from support import names, section_from, tags_by_name  # noqa: E402
from isabelle_query import shape  # noqa: E402

# `above` and `below` are deliberately IDENTICAL one-line proofs, bracketing a
# proposition with a multi-step one.  That symmetry is the hand-computable
# invariant: whatever a `by simp` proof scans to, both must scan to the same,
# and before the fix `above` ran through line 12 and scanned to more.
#
#  1 theory Prop
#  2 imports Main
#  3 begin
#  4
#  5 lemma above: "True"
#  6   by simp
#  7
#  8 proposition mid: "True"
#  9 proof -
# 10   have a: "True" by simp
# 11   show "True" by simp
# 12 qed
# 13
# 14 lemma below: "True"
# 15   by simp
# 16
# 17 end
PROP = '''theory Prop
imports Main
begin

lemma above: "True"
  by simp

proposition mid: "True"
proof -
  have a: "True" by simp
  show "True" by simp
qed

lemma below: "True"
  by simp

end
'''


class PropositionIsADeclaration(unittest.TestCase):
    def setUp(self):
        self.sec = section_from(PROP, theory="Prop")
        self.by_name = {e.name: e for e in self.sec.entries}

    def test_it_is_indexed_in_source_order(self):
        self.assertEqual(names(self.sec), ["above", "mid", "below"])

    def test_it_tags_as_a_lemma(self):
        # Not THEOREM: `corollary` is declared on Pure.thy's same line and maps
        # here, and the split is query's presentation rather than Isabelle's.
        self.assertEqual(tags_by_name(self.sec)["mid"], "LEMMA")

    def test_it_starts_where_it_is_written(self):
        self.assertEqual(self.by_name["mid"].thy_line, 8)

    def test_it_bounds_the_declaration_above_it(self):
        # The knock-on half.  Unseen, `above` ran to the next entry it COULD
        # see (`below`, line 14) and took the proposition's proof with it.
        self.assertLess(self.by_name["above"].thy_end, 8)


class ItsProofIsScannedAsItsOwn(unittest.TestCase):
    """The census half: steps land on the proposition, not on the lemma above."""

    def setUp(self):
        self.sec = section_from(PROP, theory="Prop")
        self.by_name = {e.name: e for e in self.sec.entries}

    def steps(self, name):
        return shape._scan_steps(self.sec, self.by_name[name])

    def test_identical_proofs_scan_identically(self):
        # The invariant that needs no hand-computed step taxonomy: `above` and
        # `below` are the same proof, so they must scan to the same steps.
        self.assertEqual([s.kind for s in self.steps("above")],
                         [s.kind for s in self.steps("below")])

    def test_the_propositions_own_proof_has_more_than_one_step(self):
        # Non-vacuity: if `mid` scanned to nothing, the test above would pass
        # while the proof stayed invisible — which is the bug, not the fix.
        self.assertGreater(len(self.steps("mid")), 1)

    def test_the_lemma_above_does_not_swallow_them(self):
        self.assertLess(len(self.steps("above")), len(self.steps("mid")))


if __name__ == "__main__":
    unittest.main()
