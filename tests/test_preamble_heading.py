r"""A preamble under a heading may introduce the section [preamble-heading].

#28: `cut_span` starts at the entry's preamble, so moving the first lemma of
a section carried the section's introduction away (three times in NDTHT).
Whether a `text` directly under a heading documents the lemma or the
section is not in the source, so `Entry.preamble_follows_heading` says the
case is ambiguous and `cut_span` stays as it was.
"""

import os
import sys
import unittest
from pathlib import Path

sys.path.insert(0, os.path.dirname(__file__))
from isabelle_query import api  # noqa: E402

THY = ('theory Base imports Main begin\n'                         # 1
       'lemma corge: "True" by simp\n'                            # 2
       'subsection \\<open>A section\\<close>\n'                   # 3
       'text \\<open>Introduces the section.\\<close>\n'           # 4
       'lemma first: "True" by simp\n'                            # 5
       'text \\<open>Doc for second.\\<close>\n'                   # 6
       'lemma second: "True" by simp\n'                           # 7
       'section \\<open>Next\\<close>\n'                           # 8
       'text \\<open>An introduction.\\<close>\n'                  # 9
       '\n'                                                       # 10
       'text \\<open>Doc for third.\\<close>\n'                    # 11
       'lemma third: "True" by simp\n'                            # 12
       'lemma inner: "True \\<and> True"\n'                        # 13
       'proof\n'                                                  # 14
       '  paragraph \\<open>In the proof\\<close>\n'               # 15
       '  show True by simp\n'                                    # 16
       '  show True by simp\n'                                    # 17
       'qed\n'                                                    # 18
       'text \\<open>Doc for after.\\<close>\n'                    # 19
       'lemma after: "True" by simp\n'                            # 20
       'subsection \\<open>Instances\\<close>\n'                   # 21
       'instance nat :: type ..\n'                                # 22
       'text \\<open>Doc for last.\\<close>\n'                     # 23
       'lemma last: "True" by simp\n'                             # 24
       'end\n')


class APreambleUnderAHeading(unittest.TestCase):

    def setUp(self):
        sec = api.parse_theory("Base", Path("<test>"), THY.splitlines())
        self.by = {e.name: e for e in sec.entries}

    def flag(self, name):
        return self.by[name].preamble_follows_heading

    def test_the_issue_case(self):
        self.assertEqual(self.by["first"].preamble, (4, 4))
        self.assertTrue(self.flag("first"))
        # The span a tool writes through is unchanged; the flag says ask.
        self.assertEqual(self.by["first"].cut_span, (4, 5))

    def test_an_entry_between_clears_it(self):
        self.assertFalse(self.flag("second"))

    def test_another_text_block_between_does_not(self):
        # Only 11 is the preamble; 9 is not, and no entry lies between.
        self.assertEqual(self.by["third"].preamble, (11, 11))
        self.assertTrue(self.flag("third"))

    def test_a_heading_inside_the_previous_proof_does_not_count(self):
        self.assertEqual(self.by["after"].preamble, (19, 19))
        self.assertFalse(self.flag("after"))

    def test_a_proof_between_clears_it(self):
        self.assertEqual(self.by["last"].preamble, (23, 23))
        self.assertFalse(self.flag("last"))

    def test_no_preamble_no_flag(self):
        self.assertFalse(self.flag("corge"))
        self.assertFalse(self.flag("inner"))


if __name__ == "__main__":
    unittest.main()
