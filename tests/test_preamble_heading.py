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

    @staticmethod
    def by_name(text):
        sec = api.parse_theory("Base", Path("<test>"), text.splitlines())
        return {e.name: e for e in sec.entries}

    def setUp(self):
        self.by = self.by_name(THY)

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


def _without_preamble(e):
    """The documented section-introduction reading [preamble-choice]."""
    return e.cut_span and (e.thy_line, e.cut_span[1])


class LeavingThePreambleBehind(unittest.TestCase):
    """The README's one-liner, so a change to `cut_span` cannot break it."""

    def test_starts_at_the_declaration(self):
        by = APreambleUnderAHeading.by_name(THY)
        self.assertEqual(_without_preamble(by["first"]), (5, 5))
        self.assertEqual(_without_preamble(by["inner"]), (13, 18))

    def test_none_where_cut_span_is(self):
        by = APreambleUnderAHeading.by_name(
            'theory Base imports Main begin\n'
            'text \\<open>Doc.\\<close>\n'
            'lemma a: "True" by simp lemma b: "True" by simp\n'
            'end\n')
        self.assertTrue(by["a"].shares_line)
        self.assertIsNone(_without_preamble(by["a"]))

    def test_never_wider_than_cut_span(self):
        for name, e in APreambleUnderAHeading.by_name(THY).items():
            with self.subTest(name):
                lo, hi = e.cut_span
                self.assertEqual(_without_preamble(e), (e.thy_line, hi))
                self.assertLessEqual(lo, e.thy_line)
                self.assertLessEqual(e.thy_line, hi)


if __name__ == "__main__":
    unittest.main()
