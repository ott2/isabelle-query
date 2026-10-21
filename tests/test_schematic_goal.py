r"""`schematic_goal` declares a fact, as the other goal keywords do (#23).

`Pure.thy:55` declares `schematic_goal :: thy_goal_stmt` beside `theorem`
`lemma` `corollary` `proposition` (`Pure.thy:54`), and registers it through
the same `theorem` combinator with only the `schematic` flag set.  `DECL_RE`
did not list it, so it was not an entry, and, as with `proposition` before
v0.9.0, the entry above it ran on and took its proof: 837 AFP declarations,
279 folded into a preceding entry, 2,724 census lines billed to the wrong
proof.

The tag is `SCHEMATIC`.  The proof of a schematic goal instantiates its `?x`,
so the fact records a synthesised term; it is neither a lemma nor a result,
and `summary` footnotes it rather than counting it under L or T.
"""

import contextlib
import io
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(__file__))
from support import names, section_from, tags_by_name  # noqa: E402
from isabelle_query import commands, shape  # noqa: E402

# The fixture of #23, plus a modified declaration (the 4 AFP `private
# schematic_goal` lines in `Collections/Refine_Dflt.thy`).
#
#  1 theory Sg imports Main
#  2 begin
#  3
#  4 lemma before: "(1::nat) + 1 = 2"
#  5   apply simp
#  6   done
#  7
#  8 schematic_goal sg: "?x = (2::nat)"
#  9   by (rule refl)
# 10
# 11 lemma after: "(2::nat) + 2 = 4"
# 12   by simp
# 13
# 14 private schematic_goal psg: "?y = (3::nat)"
# 15   by (rule refl)
# 16
# 17 end
SG = '''theory Sg imports Main
begin

lemma before: "(1::nat) + 1 = 2"
  apply simp
  done

schematic_goal sg: "?x = (2::nat)"
  by (rule refl)

lemma after: "(2::nat) + 2 = 4"
  by simp

private schematic_goal psg: "?y = (3::nat)"
  by (rule refl)

end
'''


class SchematicGoalIsADeclaration(unittest.TestCase):
    def setUp(self):
        self.sec = section_from(SG, theory="Sg")
        self.by_name = {e.name: e for e in self.sec.entries}

    def test_it_is_indexed_in_source_order(self):
        self.assertEqual(names(self.sec), ["before", "sg", "after", "psg"])

    def test_it_tags_as_schematic(self):
        tags = tags_by_name(self.sec)
        self.assertEqual(tags["sg"], "SCHEMATIC")
        self.assertEqual(tags["psg"], "SCHEMATIC")

    def test_it_starts_where_it_is_written(self):
        self.assertEqual(self.by_name["sg"].thy_line, 8)
        self.assertEqual(self.by_name["psg"].thy_line, 14)

    def test_it_bounds_the_declaration_above_it(self):
        # Unseen, `before` ran to line 10 and `after` to the end.
        self.assertLess(self.by_name["before"].thy_end, 8)
        self.assertLess(self.by_name["after"].thy_end, 14)


class ItsProofIsScannedAsItsOwn(unittest.TestCase):
    """The census half: `before` is `apply simp` / `done`, two steps, as #23
    asks; before the fix it was three, with `sg`'s `by (rule refl)`."""

    def setUp(self):
        self.sec = section_from(SG, theory="Sg")
        self.by_name = {e.name: e for e in self.sec.entries}

    def methods(self, name):
        return [s.method for s in shape._scan_steps(self.sec,
                                                    self.by_name[name])]

    def test_the_lemma_above_keeps_only_its_own_steps(self):
        self.assertEqual(self.methods("before"), ["simp", ""])

    def test_the_schematic_goal_owns_its_proof(self):
        self.assertEqual(self.methods("sg"), ["rule"])
        self.assertEqual(self.methods("psg"), ["rule"])


class SummaryFootnotesIt(unittest.TestCase):

    def test_neither_l_nor_t(self):
        sec = section_from(SG, theory="Sg")
        self.assertEqual(commands._tag_counts(sec), (0, 2, 0))
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            commands._goal_note([sec])
        self.assertEqual(
            buf.getvalue(),
            "\n2 entries are schematic goals (`schematic_goal`, tag "
            "SCHEMATIC), counted in neither L nor T.\n")


if __name__ == "__main__":
    unittest.main()
