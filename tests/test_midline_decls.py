r"""A declaration need not start its line [midline-decl] (#29).

Isabelle reads a command wherever a token starts, so `by simp lemma b: True`
declares `b`.  A line-start test missed 36 AFP declarations, and the entry
before each one took it into its span and `cut_span`: deleting
`Simpl/Semantic.thy:Seq_NoFaultStuckD2` through it removed two lemmas.
Lines cannot separate two declarations that share one, so both get
`shares_line` and no cut span.
"""

import os
import sys
import unittest
from pathlib import Path

sys.path.insert(0, os.path.dirname(__file__))
from isabelle_query import api  # noqa: E402

THY = ('theory S imports Main begin\n'                              # 1
       'lemma a: True\n'                                            # 2
       '  by simp lemma b: True by simp\n'                          # 3
       '\n'                                                         # 4
       'lemma c: True by simp\n'                                    # 5
       'abbreviation "p == (0::nat)"   abbreviation "q == Suc p"\n'  # 6
       'text \\<open>major\\<close> lemma m:\n'                      # 7
       '  "True" by simp\n'                                         # 8
       '\n'                                                         # 9
       'lemma n: True\n'                                            # 10
       '  by simp private lemma o: True\n'                          # 11
       '  by simp\n'                                                # 12
       'locale zz begin definition "z = ()"\n'                      # 13
       'end\n'                                                      # 14
       'lemma u: "let ?fun = id in True" by simp\n'                 # 15
       'end\n')


class ADeclarationAfterATokenStarts(unittest.TestCase):

    def setUp(self):
        sec = api.parse_theory("S", Path("<test>"), THY.splitlines())
        self.by = {e.name: e for e in sec.entries}

    def test_every_declaration_is_an_entry(self):
        self.assertEqual(list(self.by), ["a", "b", "c", "p", "q", "m", "n",
                                         "o", "zz", "z", "u"])
        self.assertEqual([self.by[n].thy_line for n in ("b", "q", "m", "o",
                                                        "z")],
                         [3, 6, 7, 11, 13])

    def test_the_issue_case(self):
        # `a`'s `by` is on 3, so its span reaches 3; neither has a cut span.
        a, b = self.by["a"], self.by["b"]
        self.assertEqual((a.thy_end, a.body_end_line, b.thy_end), (3, 3, 4))
        for e in (a, b):
            self.assertTrue(e.shares_line)
            self.assertIsNone(e.cut_span)
        self.assertEqual(self.by["c"].cut_span, (5, 5))

    def test_each_entry_reads_only_its_own_part(self):
        self.assertEqual(self.by["b"].proof_line, 3)
        self.assertEqual(self.by["o"].visibility, "private")
        self.assertEqual((self.by["n"].proof_line, self.by["n"].thy_end),
                         (11, 11))
        self.assertEqual((self.by["o"].proof_line, self.by["o"].thy_end),
                         (12, 12))

    def test_text_ahead_of_it_belongs_to_no_entry(self):
        # `text` opens a command of its own: `q`, the entry before, keeps
        # line 6 to itself and is flagged only for sharing it with `p`.
        self.assertEqual(self.by["q"].thy_end, 6)
        self.assertFalse(self.by["q"].runs_into_next)
        self.assertTrue(self.by["m"].shares_line)

    def test_a_schematic_variable_is_no_command(self):
        self.assertFalse(self.by["u"].shares_line)
        self.assertEqual(self.by["u"].cut_span, (15, 15))


if __name__ == "__main__":
    unittest.main()
