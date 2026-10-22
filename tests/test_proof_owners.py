r"""`shape` measures every proof, not only the proofs of facts [proof-owners].

A command that proves something but declares no fact — `instance`,
`sublocale`, `interpretation`, `termination`, `typedef`, `notepad`, ... — was
not an `Entry`, and `shape` rode on the entry index, so its proof was
measured by nothing: 1.6% of the AFP's proof text, by accident of the entry
model rather than by decision.  The population is Isabelle's: every built-in
command Pure and HOL declare with a goal kind that is not already a goal
entry, plus `notepad` (`parsing.PROOF_OWNERS`).

They are `TheorySection.proof_owners`, not entries, so `outline`, `find`,
`unused` and the call graph see exactly what they saw before.  A census
record says what owns its proof (`tag`) and where (`line`).
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(__file__))
from support import section_from  # noqa: E402
from isabelle_query import shape  # noqa: E402

# Inline rather than in fixtures/: the directory is loaded whole by other
# tests, and these declarations would collide with theirs.
THY = r'''theory Owners imports Main
begin

class foo = fixes f :: "'a \<Rightarrow> 'a"

instantiation nat :: foo
begin
definition "f (n::nat) = n"
instance ..
end

instance nat :: order
proof -
  show "OFCLASS(nat, order_class)" by intro_classes
qed

locale L = fixes x :: nat assumes "x = x"

interpretation L0: L 0
  by unfold_locales simp

sublocale L \<subseteq> L1: L x
proof
  show "x = x" by simp
qed

function g :: "nat \<Rightarrow> nat" where
  "g 0 = 0" | "g (Suc n) = g n"
  by pat_completeness auto
termination by lexicographic_order

typedef (overloaded) 'a box = "UNIV :: 'a set"
  by simp

notepad
begin
  have a: "True" by simp
  have "True"
  proof -
    show ?thesis using a by simp
  qed
end

lemma after: "True" by simp

end
'''


def records():
    sec = section_from(THY, "Owners")
    return [shape.summary_record(shape.summarize(pm))
            for pm in shape.analyze_sections([sec])], sec


class EveryProofIsMeasured(unittest.TestCase):

    def setUp(self):
        self.recs, self.sec = records()

    def test_owners_in_source_order(self):
        self.assertEqual(
            [(r["line"], r["tag"], r["lemma"]) for r in self.recs],
            [(9, "INSTANCE", "?"), (12, "INSTANCE", "?"),
             (19, "INTERPRETATION", "?"), (22, "SUBLOCALE", "?"),
             (27, "FUNCTION", "g"), (30, "TERMINATION", "?"),
             (32, "TYPEDEF", "box"), (35, "NOTEPAD", "?"),
             (44, "LEMMA", "after")])

    def test_each_proof_is_its_own(self):
        by_line = {r["line"]: r for r in self.recs}
        # `instance ..` | `proof - show ... by ... qed` | `by unfold_locales`.
        self.assertEqual(by_line[9]["methods"], {"..": 1})
        self.assertEqual((by_line[12]["n_steps"], by_line[12]["n_goals"]),
                         (3, 1))
        self.assertEqual(by_line[19]["methods"], {"by:unfold_locales": 1})
        # The function's own proof, and its termination proof, apart.
        self.assertEqual(by_line[27]["methods"], {"by:pat_completeness": 1})
        self.assertEqual(by_line[30]["methods"],
                         {"by:lexicographic_order": 1})

    def test_a_notepad_is_a_proof_context(self):
        # have a | by | have | show | using | by | qed — three goals, and its
        # nested `proof` one level down, as in a lemma's own proof.
        r = next(r for r in self.recs if r["tag"] == "NOTEPAD")
        self.assertEqual((r["n_steps"], r["n_goals"], r["depth_max"]),
                         (7, 3, 2))


class NothingElseSeesThem(unittest.TestCase):

    def test_the_entry_index_is_unchanged(self):
        _recs, sec = records()
        self.assertEqual([(e.tag, e.name) for e in sec.entries],
                         [("CLASS", "foo"), ("DEF", "f"), ("LOCALE", "L"),
                          ("FUN", "g"), ("LEMMA", "after")])
        self.assertTrue(all(o.proof_line for o in sec.proof_owners))


if __name__ == "__main__":
    unittest.main()
