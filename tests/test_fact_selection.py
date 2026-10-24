r"""A selection does not end a fact list [fact-selection].

`assms(1)` selects from the fact `assms`; the fact walk took its `(` as
structure, which ended the list, so `using assms(1) foo` cited `assms`
alone.  About 57,800 lists in the Isabelle2025-2 AFP put a selection after
a cite keyword or `add:`.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(__file__))
from isabelle_query.graph import (  # noqa: E402
    _cited_facts_on_line, _shadowed_uses_on_line)


def _cited(line):
    return _cited_facts_on_line(line)[0]


class ASelection(unittest.TestCase):

    def test_the_todo_cases(self):
        self.assertEqual(_cited("using assms(1) foo by simp"),
                         {"assms", "foo"})
        self.assertEqual(_cited("from a(2) b have x"), {"a", "b"})
        self.assertEqual(_cited("by (simp add: f(1) g)"), {"f", "g"})

    def test_every_selection_form(self):
        self.assertEqual(_cited("using a(1,3) b(2-) c(1-2) d"),
                         {"a", "b", "c", "d"})
        # Isar tokenizes it either way; 111 AFP lists space it.
        self.assertEqual(_cited("from Suc.hyps (1) h show ?case"),
                         {"Suc.hyps", "h"})

    def test_a_method_count_keeps_the_method(self):
        # The same group after a method: premise count, occurrences.
        self.assertEqual(_cited("apply (frule (1) r)"), {"r"})
        self.assertEqual(_cited("by (subst (1 2) cong) simp"), {"cong"})

    def test_a_group_of_words_is_no_selection(self):
        self.assertEqual(_cited_facts_on_line(
            "by (metis (no_types) a b)"), ({"a", "b"}, True))


class ACitedThis(unittest.TestCase):

    def test_is_the_current_fact_not_an_entry(self):
        # Jinja declares `definition this :: vname`; once a selection no
        # longer ended the list, `using a(1) this` began citing it.
        for line in ("using a(1) this by simp", "from this show ?thesis"):
            with self.subTest(line):
                self.assertEqual(_shadowed_uses_on_line(line, {"this"}),
                                 set())
        # The constant in a term is still a use.
        self.assertEqual(
            _shadowed_uses_on_line('have "this = x" by simp', {"this"}),
            {"this"})


if __name__ == "__main__":
    unittest.main()
