r"""`lemmas` / `theorems` bind citable facts, so they are entries [lemmas-entries].

`lemmas a = x y` gives an existing list of facts a new name.  Issue #16: no
entry was minted for it, so `show a` found nothing, `callers -r` could not
start from it, and -- the silent half -- a closure could not pass THROUGH it.
Its citations were attributed to the theory's `<toplevel>` node, which nothing
can cite, so a lemma citing `a` never reached the closure of `x`.

Isabelle's grammar (`Pure.thy`) is

    lemmas (in TARGET)? (thmdef? thms) and ... for_fixes?
    thmdef = NAME [attrs]? =

so each named group is one fact, and a group with no `NAME =` binds nothing:
`lemmas [simp] = foo` only attaches an attribute, and stays `<toplevel>`.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(__file__))
from support import brute_force_call_graph, cli, names, section_from, \
    tags_by_name  # noqa: E402

#  1 theory L imports Main begin
#  2 lemma base: "True" by simp
#  3 lemma other: "True" by simp
#  4 lemmas alias = base
#  5 lemma user: "True" using alias by simp
#  6 lemmas (in foo) two [simp] = base[of "a = b"] other
#  7   and three = other
#  8 lemmas [simp] = base
#  9 lemmas
# 10   four = base and
# 11   five = other
# 12 theorems six = other
# 13 end
THY = r'''theory L imports Main begin
lemma base: "True" by simp
lemma other: "True" by simp
lemmas alias = base
lemma user: "True" using alias by simp
lemmas (in foo) two [simp] = base[of "a = b"] other
  and three = other
lemmas [simp] = base
lemmas
  four = base and
  five = other
theorems six = other
end
'''

FACTS = ["alias", "two", "three", "four", "five", "six"]


def entry(sec, name):
    return next(e for e in sec.entries if e.name == name)


class EachNamedGroupIsAnEntry(unittest.TestCase):

    def setUp(self):
        self.sec = section_from(THY, "L")

    def test_names_in_source_order(self):
        self.assertEqual(names(self.sec),
                         ["base", "other", "alias", "user", "two", "three",
                          "four", "five", "six"])

    def test_tagged_lemmas(self):
        tags = tags_by_name(self.sec)
        self.assertEqual({n: tags[n] for n in FACTS},
                         dict.fromkeys(FACTS, "LEMMAS"))

    def test_an_anonymous_command_binds_nothing(self):
        self.assertNotIn(8, [e.thy_line for e in self.sec.entries])

    def test_group_lines(self):
        # A group runs from its first token to the line before the next one;
        # the first starts on the command line, even with the name below it.
        got = {n: (entry(self.sec, n).thy_line,
                   entry(self.sec, n).decl_end_line) for n in FACTS}
        self.assertEqual(got, {"alias": (4, 4), "two": (6, 6),
                               "three": (7, 7), "four": (9, 10),
                               "five": (11, 11), "six": (12, 12)})

    def test_the_target_covers_every_group(self):
        self.assertEqual([entry(self.sec, n).in_target
                          for n in ("two", "three")], ["foo", "foo"])

    def test_the_text_has_no_command_word(self):
        self.assertEqual(entry(self.sec, "alias").text, "LEMMAS alias = base")


class TheGraphPassesThroughAnAlias(unittest.TestCase):

    def setUp(self):
        self.sec = section_from(THY, "L")
        self.graph = cli._build_call_graph([self.sec])

    def test_each_group_cites_its_own_right_hand_side(self):
        self.assertEqual(self.graph.callers["base"],
                         {"alias", "two", "four", "L:<toplevel>"})
        self.assertEqual(self.graph.callers["other"],
                         {"two", "three", "five", "six"})

    def test_a_citation_of_the_alias_reaches_its_target(self):
        self.assertEqual(self.graph.callers["alias"], {"user"})

    def test_the_oracle_agrees(self):
        ref = brute_force_call_graph([self.sec])
        self.assertEqual(self.graph.callers, ref.callers)
        self.assertEqual(self.graph.callees, ref.callees)


if __name__ == "__main__":
    unittest.main()
