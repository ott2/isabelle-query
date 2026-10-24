r"""A fact literal is a citation, however it is quoted [fact-literal] (#31).

`from \<open>A\<close>` and `` from `A` `` cite the fact whose proposition is
`A`, as `from a` cites it by name.  The cartouche was blanked with the
propositions and cited nothing; the backquoted form counted only by
accident, its words read as names, so `` `x < y` `` cited `x` and `y`.  In
the Isabelle2025-2 AFP about 98% of fact literals are cartouches.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(__file__))
from support import section_from  # noqa: E402

from isabelle_query import shape  # noqa: E402
from isabelle_query.graph import _cited_facts_on_line  # noqa: E402

SRC = r'''theory Bq imports Main
begin

lemma backquote:
  assumes "A" and "B"
  shows "A \<and> B"
proof -
  from `A` `B` show ?thesis by simp
qed

lemma cartouche:
  assumes "A" and "B"
  shows "A \<and> B"
proof -
  from \<open>A\<close> \<open>B\<close> show ?thesis by simp
qed

lemma named:
  assumes a: "A" and b: "B"
  shows "A \<and> B"
proof -
  from a b show ?thesis by simp
qed

lemma using_cartouche:
  assumes "A" and "B"
  shows "A \<and> B"
proof -
  show ?thesis using \<open>A\<close> \<open>B\<close> by simp
qed

lemma method_cartouche:
  assumes "A" and "B"
  shows "A \<and> B"
proof -
  show ?thesis by (simp add: \<open>A\<close> \<open>B\<close>)
qed

lemma method_backquote:
  assumes "A" and "B"
  shows "A \<and> B"
proof -
  show ?thesis by (simp add: `A` `B`)
qed

lemma backquoted_term:
  assumes "x < y" and "y < z"
  shows "x < z"
proof -
  from `x < y` `y < z` show ?thesis by simp
qed

end
'''


def _fanin(name):
    sec = section_from(SRC)
    entry = next(e for e in sec.entries if e.name == name)
    steps = shape._scan_steps(sec, entry)
    shape.annotate_fanin(steps, sec)
    return [s.fanin for s in steps if s.kind == "goal"]


def _cited(line):
    return _cited_facts_on_line(line)[0]


class AFactLiteralIsCited(unittest.TestCase):

    def test_the_issue_case(self):
        for name in ("backquote", "cartouche", "named", "using_cartouche",
                     "method_cartouche", "method_backquote"):
            with self.subTest(name):
                self.assertEqual(_fanin(name), [2])

    def test_a_backquote_is_one_fact_not_its_words(self):
        # Was 3: `x`, `y`, `z`.
        self.assertEqual(_fanin("backquoted_term"), [2])

    def test_both_spellings_are_one_fact(self):
        self.assertEqual(_cited(r"from `A`  \<open>A\<close> have B"), {"`A`"})
        self.assertEqual(_cited("from `x  <\ty` show"), {"`x < y`"})
        self.assertEqual(_cited("using ‹A› by simp"), {"`A`"})

    def test_a_fact_position_reads_it(self):
        for line in (r"with \<open>A\<close> show ?thesis",
                     r"unfolding \<open>A\<close> by simp",
                     r"by (rule \<open>A\<close>)",
                     r"by (metis \<open>A\<close>)",
                     r"by (simp add: foo \<open>A\<close>)",
                     r"using r[OF \<open>A\<close>] by simp"):
            with self.subTest(line):
                self.assertIn("`A`", _cited(line))

    def test_a_term_position_does_not(self):
        for line in (r"have \<open>A\<close> by simp",
                     r"using r[of \<open>A\<close>] by simp",
                     r"by (cases \<open>A\<close>)",
                     r'have "\<open>A\<close>" by simp'):
            with self.subTest(line):
                self.assertNotIn("`A`", _cited(line))

    def test_an_unknown_method_leaves_coverage_as_it_was(self):
        # A literal argument may be a term as well as a fact: no citation,
        # and no loss of coverage.
        self.assertEqual(_cited_facts_on_line(r"by (foo \<open>A\<close>)"),
                         (set(), True))

    def test_a_nested_cartouche_is_inside_the_literal(self):
        self.assertEqual(
            _cited(r"from \<open>f \<open>x\<close> = y\<close> p show"),
            {r"`f \<open>x\<close> = y`", "p"})

    def test_a_literal_open_at_the_line_end_is_one_fact(self):
        self.assertEqual(_cited(r"from p \<open>A \<and>"), {"p", r"`A \<and>`"})


if __name__ == "__main__":
    unittest.main()
