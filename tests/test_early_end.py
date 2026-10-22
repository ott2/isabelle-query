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


if __name__ == "__main__":
    unittest.main()
