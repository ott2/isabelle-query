r"""A fact list runs on past `and` and past an attribute nested in `[OF …]`
(#36).

Isar reads a fact list as `and`-separated groups, so `from a and b` is
`from a b`; the fan-in walk ended the list at the `and`, citing `a` alone.
And `r[OF a[simplified] b]` passes `a[simplified]` and `b` to `OF`, but the
inner `]` ended the `OF` list, losing `b`.  Fan-in by hand: `plain` and
`with_and` cite `a`, `b`; `nested_attribute` and `flat_OF` cite `r`, `a`,
`b`.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(__file__))
from support import section_from  # noqa: E402

from isabelle_query import proof_locals, shape  # noqa: E402
from isabelle_query.graph import _cited_facts_on_line  # noqa: E402

# The issue's fixture, then the same in `unused facts`' view.
SRC = r'''theory Fl imports Main
begin

lemma plain:
  assumes a: "A" and b: "B"
  shows "A \<and> B"
proof -
  from a b show ?thesis by simp
qed

lemma with_and:
  assumes a: "A" and b: "B"
  shows "A \<and> B"
proof -
  from a and b show ?thesis by simp
qed

lemma nested_attribute:
  assumes a: "A" and b: "B" and r: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B"
  shows "A \<and> B"
proof -
  from r[OF a[simplified] b] show ?thesis .
qed

lemma flat_OF:
  assumes a: "A" and b: "B" and r: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B"
  shows "A \<and> B"
proof -
  from r[OF a b] show ?thesis .
qed

lemma local_and:
  assumes "A" "B"
  shows "A \<and> B"
proof -
  have *: "A" using assms by simp
  have **: "B" using assms by simp
  show ?thesis using * and ** by simp
qed

end
'''


def _fanin_mean(name):
    sec = section_from(SRC, theory="Fl")
    entry = next(e for e in sec.entries if e.name == name)
    steps = shape._scan_steps(sec, entry)
    shape.annotate_fanin(steps, sec)
    goals = [s.fanin for s in steps if s.kind == "goal"]
    return sum(goals) / len(goals)


def _cited(line):
    return _cited_facts_on_line(line)[0]


class TheIssueCase(unittest.TestCase):

    def test_fanin_mean(self):
        for name, want in (("plain", 2.0), ("with_and", 2.0)):
            with self.subTest(name):
                self.assertEqual(_fanin_mean(name), want)


class AndSeparatesFacts(unittest.TestCase):

    def test_after_every_cite_keyword(self):
        for line, want in (("from a and b show ?thesis", {"a", "b"}),
                           ("with a and b have x", {"a", "b"}),
                           ("using a and b c by simp", {"a", "b", "c"}),
                           ("unfolding d and e by simp", {"d", "e"}),
                           ("from * and ** show x", {"*", "**"}),
                           ("from a[OF x] and b have y", {"a", "x", "b"})):
            with self.subTest(line):
                self.assertEqual(_cited(line), want)

    def test_a_literal_after_and(self):
        self.assertEqual(_cited(r"from \<open>A\<close> and \<open>B\<close>"
                                " show x"), {"`A`", "`B`"})

    def test_a_goal_keyword_still_ends_the_list(self):
        self.assertEqual(_cited("from a have A and B by simp"), {"a"})

    def test_unused_facts_reads_it(self):
        sec = section_from(SRC, theory="Fl")
        self.assertEqual(
            [b.name for _, b in proof_locals.unread_locals([sec])
             if b.entry == "local_and"], [])


if __name__ == "__main__":
    unittest.main()
