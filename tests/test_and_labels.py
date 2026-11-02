r"""Every label of an `and`-joined introduction is a fact (#38).

`have a: "P" and b: "Q"` binds `a` and `b`, as do `assume`, `obtain … where`
and `note a = … and b = …`; live-fact space read the first label only, so
`b` was never born.  When the first fact is unlabelled, the labelled second
one was missed entirely.  Labels after `if` / `when` / `for` are the step's
own premises, local to its proof, and introduce nothing.  `live_max` by
hand: 2 for each of the issue's five lemmas, as for `have_separate`.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(__file__))
from support import section_from  # noqa: E402

from isabelle_query import shape  # noqa: E402

# The issue's fixture, then a wrapped clause, `note`, premises after `if`,
# and `this` chaining the facts.
SRC = r'''theory Fixture_And imports Main
begin

lemma have_and:
  assumes p: "P" and q: "Q"
  shows "P \<and> Q"
proof -
  have a: "P" and b: "Q" using p q by auto
  show ?thesis using a b by auto
qed

lemma have_separate:
  assumes p: "P" and q: "Q"
  shows "P \<and> Q"
proof -
  have a: "P" using p by auto
  have b: "Q" using q by auto
  show ?thesis using a b by auto
qed

lemma assume_and:
  shows "P \<Longrightarrow> Q \<Longrightarrow> P \<and> Q"
proof -
  assume a: "P" and b: "Q"
  show ?thesis using a b by auto
qed

lemma obtain_and:
  assumes "\<exists>x::nat. x > 0 \<and> x < 2"
  shows "True"
proof -
  obtain x :: nat where a: "x > 0" and b: "x < 2" using assms by auto
  have "x = 1" using a b by auto
  show ?thesis by simp
qed

lemma anon_then_label:
  assumes p: "P" and q: "Q"
  shows "P \<and> Q"
proof -
  have "P" and b: "Q" using p q by auto
  have c: "P" using p by auto
  show ?thesis using b c by auto
qed

lemma wrapped:
  assumes p: "P" and q: "Q"
  shows "P \<and> Q"
proof -
  have a: "P"
    and b [simp]: "Q"
    using p q by auto
  show ?thesis using a b by auto
qed

lemma note_and:
  assumes p: "P" and q: "Q"
  shows "P \<and> Q"
proof -
  note a = p and b = q
  show ?thesis using a b by auto
qed

lemma premises:
  assumes p: "P" and q: "Q"
  shows "P \<and> Q"
proof -
  have c: "P \<and> Q" if a: "P" and b: "Q" for x using a b by auto
  show ?thesis using c p q by auto
qed

lemma chained:
  assumes p: "P" and q: "Q"
  shows "P \<and> Q"
proof -
  have a: "P" and b: "Q" using p q by auto
  then show ?thesis by auto
qed

end
'''


def _steps(name):
    sec = section_from(SRC, theory="Fixture_And")
    entry = next(e for e in sec.entries if e.name == name)
    steps = shape._scan_steps(sec, entry)
    return sec, steps


def _live_max(name):
    sec, steps = _steps(name)
    return shape.live_fact_space(steps, sec)[0]


class TheIssueCase(unittest.TestCase):

    def test_live_max(self):
        for name in ("have_and", "have_separate", "assume_and", "obtain_and",
                     "anon_then_label"):
            with self.subTest(name):
                self.assertEqual(_live_max(name), 2)


class EveryClause(unittest.TestCase):

    def test_a_wrapped_clause_and_its_attribute(self):
        self.assertEqual(_live_max("wrapped"), 2)

    def test_note(self):
        self.assertEqual(_live_max("note_and"), 2)

    def test_a_premise_after_if_is_the_steps_own(self):
        self.assertEqual(_live_max("premises"), 1)

    def test_this_carries_every_fact(self):
        sec, steps = _steps("chained")
        shape.live_fact_space(steps, sec)
        self.assertEqual([s.live for s in steps if s.kw == "then"], [2])

    def test_the_first_label_is_unchanged(self):
        _, steps = _steps("anon_then_label")
        self.assertEqual([s.label for s in steps if s.kw == "have"],
                         ["", "c"])


if __name__ == "__main__":
    unittest.main()
