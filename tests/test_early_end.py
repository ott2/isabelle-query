r"""An entry ends where its proof does, not earlier [early-end].

An entry's span runs to the next boundary: the next entry, a heading, or a
span-bounding command.  Two of those could fall INSIDE a proof, ending the
entry while the proof ran on — 3 proofs and 1,273 lines over the AFP
(`scripts/probe_early_end.py`), outside every entry and so invisible to
`show`, `shape` and `unused`.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(__file__))
from support import section_from  # noqa: E402
from isabelle_query import parsing  # noqa: E402


def entry(text, name="t"):
    sec = section_from(text, "T")
    return next(e for e in sec.entries if e.name == name)


class AQualifiedNameIsNoCommand(unittest.TestCase):
    """The lexer takes the longest token: `context.x` is a name."""

    THY = ('theory T imports Main begin\n'      # 1
           'lemma t: "True"\n'                  # 2
           'proof -\n'                          # 3
           '  note facts =\n'                   # 4
           '    TrueI\n'                        # 5
           '    {WORD}\n'                       # 6
           '  show ?thesis by simp\n'           # 7
           'qed\n'                              # 8
           'end\n')

    def test_names_that_begin_with_a_boundary_word(self):
        for word in ("context.safe_unfolds", "context'", "end.foo",
                     "context\\<^sub>1.x", "declare\\<alpha>"):
            with self.subTest(word):
                e = entry(self.THY.replace("{WORD}", word))
                self.assertEqual((e.thy_end, e.body_end_line), (8, 8))

    def test_the_keyword_itself_still_bounds(self):
        m = parsing._LEADING_CMD_RE.match
        self.assertEqual(m("context foo begin").group(1), "context")
        self.assertEqual(m("ML\\<open>val x = 1\\<close>").group(1), "ML")
        self.assertEqual(m("end").group(1), "end")
        # `..` is a proof, not a qualifier (Interval_Arithmetic:35).
        self.assertEqual(m("instance..").group(1), "instance")
        self.assertEqual(m("instance.").group(1), "instance")
        self.assertIsNone(m("context.safe_unfolds"))


class AHeadingInsideAProof(unittest.TestCase):
    """A heading is legal in proof mode, and must not end the entry
    (Hales_Jewett:1196 lost 717 lines of `hj_imp_lhj_step` that way)."""

    THY = ('theory T imports Main begin\n'                 # 1
           'lemma t: "True \\<and> True"\n'                 # 2
           'proof\n'                                       # 3
           '  show "True" by simp\n'                       # 4
           '  paragraph \\<open>The second half\\<close>\n'  # 5
           '  text \\<open>Prose, then a diagnostic.\\<close>\n'  # 6
           '  thm conjI\n'                                 # 7
           '  show "True" by simp\n'                       # 8
           'qed\n'                                         # 9
           '\n'                                            # 10
           'section \\<open>Next\\<close>\n'                # 11
           '\n'                                            # 12
           'lemma u: "True" by simp\n'                     # 13
           '\n'                                            # 14
           'lemma v: "True"\n'                             # 15
           'proof -\n'                                     # 16
           '  paragraph \\<open>Never closed\\<close>\n'    # 17
           '  show ?thesis by simp\n'                      # 18
           '\n'                                            # 19
           'lemma w: "True" by simp\n'                     # 20
           'end\n')

    def test_the_entry_runs_on_to_its_next_boundary(self):
        # Past the heading on 5 to the one on 11, as any entry ends; its
        # body ends where the proof does.
        e = entry(self.THY, "t")
        self.assertEqual((e.thy_end, e.body_end_line), (10, 9))

    def test_a_heading_between_entries_still_ends_one(self):
        self.assertEqual(entry(self.THY, "u").thy_line, 13)
        self.assertEqual(
            [s[2] for s in section_from(self.THY, "T").outline], [5, 11, 17])

    def test_a_proof_never_seen_to_close_keeps_its_end(self):
        # No `qed` before the next entry: the walk cannot say where `v`
        # ends, so the heading still ends it, rather than a guess.
        self.assertEqual(entry(self.THY, "v").thy_end, 16)

    def test_the_gate(self):
        outer = section_from(self.THY, "T").outer_source()
        self.assertTrue(parsing._proof_follows(outer, 5, 9))
        self.assertFalse(parsing._proof_follows(outer, 11, 14))


if __name__ == "__main__":
    unittest.main()
