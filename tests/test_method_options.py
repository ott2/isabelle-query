r"""A method's option group does not end its arguments [metis-options].

The fact walk took every `(` as the start of a fresh method, so in
`by (metis (no_types, lifting) a b)` the group's `)` left `a` to be read as
the method name: nothing was cited, and the step was uncovered.  About
15,300 `metis` / `meson` calls and 8,600 `smt` calls in the Isabelle2025-2
AFP carry a group, most of them written by Sledgehammer.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(__file__))
from isabelle_query.graph import _cited_facts_on_line  # noqa: E402


class AnOptionGroup(unittest.TestCase):

    def test_the_todo_case(self):
        self.assertEqual(
            _cited_facts_on_line("by (metis (no_types, lifting) a b)"),
            ({"a", "b"}, True))

    def test_every_prover_method(self):
        for line in ("by (meson (full_types) a b)",
                     "by (smt (verit, best) a b)",
                     "by (smt (z3) a b)"):
            with self.subTest(line):
                self.assertEqual(_cited_facts_on_line(line),
                                 ({"a", "b"}, True))

    def test_a_group_of_methods_still_starts_fresh(self):
        self.assertEqual(
            _cited_facts_on_line("by (rule a, simp add: b) (metis c)"),
            ({"a", "b", "c"}, True))
        self.assertEqual(
            _cited_facts_on_line("apply ((rule a)+, (erule b))"),
            ({"a", "b"}, True))

    def test_a_semicolon_starts_a_method(self):
        # `;` joins methods as `,` and `|` do: `drule` and `clarify` are
        # methods, not `frule`'s facts.
        self.assertEqual(
            _cited_facts_on_line(
                "apply (frule (1) r; drule s; clarify)"),
            ({"r", "s"}, True))

    def test_a_term_method_keeps_its_options_too(self):
        # `simp (no_asm)` is still `simp` after the group: no fact, covered.
        self.assertEqual(_cited_facts_on_line("by (simp (no_asm) x)"),
                         (set(), True))


if __name__ == "__main__":
    unittest.main()
