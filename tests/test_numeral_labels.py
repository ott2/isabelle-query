r"""A numeral is a fact name [numeral-label] (#32).

Isar's `name` admits `nat`, so `assumes 1: "P"` binds `1` and `using 1`
reads it.  The scan's tokens had to start with a letter, so `1` was never
read and every numeral premise was reported unread: a script that deletes
reported premises deleted one the proof needs.  In a selection `1(2)` the
`2` is an index, not the fact `2`.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(__file__))
from support import section_from  # noqa: E402

from isabelle_query import proof_locals  # noqa: E402

SRC = r'''theory N imports Main
begin

lemma f:
  assumes 1: "A" and 2: "B" and eb: "C"
  shows "A \<and> B \<and> C"
proof -
  have "A \<and> B"
    using 1 2 by simp
  then show ?thesis using eb by simp
qed

lemma method_args:
  assumes 1: "A" and 2: "B"
  shows "A \<and> B"
  by (simp add: 1 2)

lemma glued:
  assumes 1: "A" and 2: "B"
  shows "A \<and> B"
  by(simp add: 1 2)

lemma attribute:
  assumes 1: "A" and 2: "A \<Longrightarrow> B"
  shows "B"
  by (rule 2[OF 1])

lemma chained:
  assumes 1: "A" and 2: "B"
  shows "A \<and> B"
proof -
  from 1 2 show ?thesis by simp
qed

lemma selection:
  assumes 1: "A" "B" and 2: "C"
  shows "A \<and> B"
  using 1(1) 1(2) by simp

lemma unread:
  assumes 1: "A" and 2: "B"
  shows "A"
  by (simp add: 3)

lemma local_numeral: "True"
proof -
  have 1: "True" by simp
  have 2: "True" by simp
  show ?thesis using 1 by simp
qed

lemma quoted:
  assumes 0: "A" and 1: "B"
  shows "A \<and> B"
  by (metis "0" "1")

lemma quoted_in_proof: "True"
proof -
  obtain x where 2: "x = (0::nat)" by simp
  have "x = 0" by (meson "2")
  then show ?thesis by simp
qed

lemma quoted_term:
  assumes i: "A" and p: "B"
  shows "True"
proof -
  let ?a = "p"
  have "True" using conjI[of "i"] by simp
  then show ?thesis by simp
qed

lemma priorities: "True"
proof -
  define c (\<open>C _\<close> [80]) where "c = (\<lambda>n::nat. n)"
  show ?thesis by simp
qed

end
'''


class ANumeralNamesAFact(unittest.TestCase):

    def setUp(self):
        sec = section_from(SRC, theory="N")
        self.rows = {(b.entry, b.name)
                     for _, b in proof_locals.unread_locals([sec])}

    def unread(self, entry):
        return sorted(n for e, n in self.rows if e == entry)

    def test_the_issue_case(self):
        self.assertEqual(self.unread("f"), [])

    def test_every_citing_position_reads_it(self):
        for entry in ("method_args", "glued", "attribute", "chained"):
            with self.subTest(entry):
                self.assertEqual(self.unread(entry), [])

    def test_a_selection_index_is_not_a_fact(self):
        self.assertEqual(self.unread("selection"), ["2"])

    def test_an_unread_numeral_is_still_reported(self):
        self.assertEqual(self.unread("unread"), ["1", "2"])

    def test_a_quoted_name_reads(self):
        # Sledgehammer quotes a numeral name: `metis "0"`.
        self.assertEqual(self.unread("quoted"), [])
        self.assertEqual(self.unread("quoted_in_proof"), [])

    def test_a_quoted_term_does_not(self):
        # `?a` is unread too: nothing uses it.
        self.assertEqual(self.unread("quoted_term"), ["?a", "i", "p"])

    def test_a_numeral_is_no_variable(self):
        self.assertEqual(self.unread("priorities"), ["c"])

    def test_a_numeral_have_binds(self):
        self.assertEqual(self.unread("local_numeral"), ["2"])


if __name__ == "__main__":
    unittest.main()
