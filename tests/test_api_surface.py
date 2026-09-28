r"""Every name `isabelle_query.api` promises must still be there [span-api].

The reciprocal of `test_layout_surface.py`.  That file pins the ten
`isabelle-layout` names query reaches for, so an upstream removal fails here
rather than in a user's traceback; this one pins the four names query offers
*downstream*, for the same reason pointed the other way.  Exporting a name is
the obligation — the README paragraph is only the notice — and without a test
the obligation is a comment that a refactor can quietly overrule.

**The surface is deliberately four names, not the dozen that look public.**
Issue #10 asked for ten line-scanners plus `_attach_preambles` and
`_proof_extent`; their results are already fields on `Entry` and
`TheorySection`, so the second class below pins those FIELDS.  That is the real
contract: a consumer depends on `e.preamble` and `e.body_end_line` existing and
meaning what they say, not on which private function computed them.  Which is
also what leaves `parsing` free to keep changing, since it is the part of this
tool that changes most.

The third class is the cost note the issue's "smallest version" would have
paid: `__all__` in `__init__.py` makes `import isabelle_query` pull the parser,
which `_prog` and the version lookup do not want.  A submodule does not, and
that is checkable rather than merely intended.
"""

import importlib
import subprocess
import sys
import tempfile
import unittest
from dataclasses import fields
from pathlib import Path

from isabelle_query import api

# The four exported names, and what each has to be.
SURFACE = [("parse_theory", "callable"), ("parse_root", "callable"),
           ("Entry", "class"), ("TheorySection", "class")]

# Fields a consumer of the spans depends on.  Named here rather than left to
# `Entry`'s definition, so removing one is a deliberate act: these are the
# line ranges the five downstream tools in issue #10 are written against.
ENTRY_SPAN_FIELDS = [
    "tag", "name", "theory",
    "thy_line",        # first line of the declaration
    "decl_end_line",   # last line before the proof / next entry
    "proof_line",      # first line of the proof, 0 if none
    "body_end_line",   # last line of the proof body
    "thy_end",         # last line of the entry's span
    "preamble",        # (start, end) of the leading `text` block, or None
    "shares_line",     # another entry's lines meet this one's: no cut_span
]
# Derived, not stored — `src_start` is the preamble start when there is one and
# `thy_line` otherwise, which is the number `delete-lemmas.py` needs and the
# one a consumer would otherwise recompute.  Pinned separately because
# `dataclasses.fields` does not see a property.
# `cut_span` is the span a tool writes through — what `block.py` in NDTHT
# used to clip for itself [cut-span].
ENTRY_SPAN_PROPERTIES = ["src_start", "line_count", "cut_span"]
SECTION_SPAN_FIELDS = [
    "theory", "path", "entries", "thy_lines",
    "outline",          # [(level, title, line)]
    "text_blocks",      # [(start, end)]
    "heading_spans",    # [(start, end)]
    "comment_ranges",   # [(start, end)]
    "nonisar_ranges",   # [(start, end)] — whole lines that are not live Isar
    "nonisar_spans",    # {line: [(col, col)]} — the same, per character
    "inner_spans",      # {line: [(col, col)]} — plus terms and cartouches
]
SECTION_VIEWS = ["source", "slice", "live_source", "outer_source"]

FIXTURE = r"""theory Doc
imports Main
begin

text \<open>A preamble that documents the lemma below.\<close>

lemma documented:
  assumes "P"
  shows "P"
proof -
  show "P" by (rule assms)
qed

end
"""


class TheExportedNames(unittest.TestCase):

    def test_every_name_in_all_resolves(self):
        for name, kind in SURFACE:
            with self.subTest(name=name):
                self.assertIn(name, api.__all__)
                obj = getattr(api, name, None)
                self.assertIsNotNone(
                    obj, f"isabelle_query.api promises {name} and does not "
                         f"provide it.  This is a published surface: removing "
                         f"a name here is a MINOR version bump, not a patch.")
                if kind == "class":
                    self.assertTrue(isinstance(obj, type))
                else:
                    self.assertTrue(callable(obj))

    def test_all_lists_exactly_the_surface(self):
        # Not "at least": a name that leaks into `__all__` is a name someone
        # will import, and then it is promised whether or not that was meant.
        self.assertEqual(sorted(api.__all__), sorted(n for n, _ in SURFACE))


class TheSpanFieldsAreTheContract(unittest.TestCase):
    """What a consumer actually depends on: the spans, not the functions."""

    def test_entry_carries_every_span_field(self):
        have = {f.name for f in fields(api.Entry)}
        self.assertEqual([f for f in ENTRY_SPAN_FIELDS if f not in have], [])

    def test_entry_carries_every_derived_span(self):
        for name in ENTRY_SPAN_PROPERTIES:
            with self.subTest(prop=name):
                self.assertIsInstance(getattr(api.Entry, name, None), property)

    def test_section_carries_every_span_field(self):
        have = {f.name for f in fields(api.TheorySection)}
        self.assertEqual([f for f in SECTION_SPAN_FIELDS if f not in have], [])

    def test_section_carries_every_view(self):
        for name in SECTION_VIEWS:
            with self.subTest(view=name):
                self.assertTrue(callable(getattr(api.TheorySection, name, None)))


class TheSpansAreRight(unittest.TestCase):
    r"""The two cases issue #10 names as currently unreachable or got wrong.

    `delete-lemmas.py` locates a lemma *with* its `text \<open>...\<close>`
    preamble in order to delete both, and hand-rolls the search; `_proof_extent`
    was asked for because "where a proof ends is not derivable from the entry
    span alone".  Both are already computed, which is the finding that made the
    surface four names instead of twelve — so both are pinned here.
    """

    def setUp(self):
        self.sec = api.parse_theory("Doc", Path("<test>"),
                                    FIXTURE.splitlines())
        self.entry = self.sec.entries[0]

    def test_the_preamble_is_attached(self):
        self.assertEqual(self.entry.preamble, (5, 5))

    def test_the_entry_span_starts_at_the_preamble(self):
        self.assertEqual(self.entry.src_start, 5)
        self.assertEqual(self.entry.thy_line, 7)

    def test_the_proof_extent(self):
        # `proof -` on 10, `qed` on 12.  Where the proof ENDS is a separate
        # walk from where the entry's span ends — issue #10's "not derivable
        # from the entry span alone" — and both are already here.
        self.assertEqual((self.entry.proof_line, self.entry.body_end_line),
                         (10, 12))

    def test_the_whole_extent_including_the_preamble(self):
        # What `delete-lemmas.py` deletes: 5..12, preamble through `qed`.
        self.assertEqual((self.entry.src_start, self.entry.thy_end), (5, 12))
        self.assertEqual(self.entry.line_count, 8)

    def test_slice_round_trips_the_lines(self):
        self.assertEqual(self.sec.slice(7, 7), ["lemma documented:"])

    def test_the_cut_span_is_preamble_through_qed(self):
        self.assertEqual(self.entry.cut_span, (5, 12))


class TheCutSpanHoldsOneEntry(unittest.TestCase):
    r"""`cut_span` is written through, so it must hold its entry and no part
    of another [cut-span].  Hand-computed on the fixture below:

      * `first` is 4..5 — not 4..7: the blank on 6 and the inter-lemma
        `text` on 7 are not its body, and 8 is `second`'s preamble;
      * `second` is 8..12, its preamble through `qed`;
      * the one-line `axiomatization` on 14 is two entries — the command and
        its axiom `F1` — which lines cannot split, so both are None rather
        than a span that takes the other along (the shape of AFP
        `SimplifiedOntologicalArgument/SimpleVariantHF.thy:12`).
    """

    SRC = ("theory Cut\nimports Main\nbegin\n"          # 1-3
           'lemma first: "True"\n'                        # 4
           "  by simp\n"                                  # 5
           "\n"                                           # 6
           "text \\<open>Doc for second.\\<close>\n"      # 7
           "text \\<open>Its own preamble.\\<close>\n"    # 8
           'lemma second: "True"\n'                       # 9
           "proof -\n  show ?thesis by simp\n"            # 10-11
           "qed\n"                                        # 12
           "\n"                                           # 13
           'axiomatization where F1: "True"\n'            # 14
           "end\n")

    def setUp(self):
        sec = api.parse_theory("Cut", Path("<test>"), self.SRC.splitlines())
        self.entries = sec.entries
        self.by_name = {e.name: e for e in sec.entries}

    def test_a_trailing_text_block_is_left_behind(self):
        first = self.by_name["first"]
        self.assertEqual(first.cut_span[1], 5)
        self.assertLess(first.cut_span[1], self.by_name["second"].src_start)

    def test_the_next_entry_takes_its_own_preamble(self):
        second = self.by_name["second"]
        self.assertEqual(second.cut_span, (8, 12))

    def test_one_line_declarations_have_no_cut_span(self):
        on_14 = [e for e in self.entries if e.thy_line == 14]
        self.assertEqual(len(on_14), 2, "fixture no longer yields both entries")
        self.assertIn("F1", [e.name for e in on_14])
        for e in on_14:
            with self.subTest(name=e.name):
                self.assertTrue(e.shares_line)
                self.assertIsNone(e.cut_span)

    def test_entries_on_their_own_lines_are_not_flagged(self):
        for n in ("first", "second"):
            with self.subTest(name=n):
                self.assertFalse(self.by_name[n].shares_line)

    def test_an_unplaced_entry_has_no_cut_span(self):
        self.assertIsNone(api.Entry("LEMMA", "x", "").cut_span)


class ParseRootAgreesWithTheCli(unittest.TestCase):
    """`parse_root` exists because `parse_theory` alone would silently differ.

    Isabelle's keyword table is session-wide, and query's is built by a
    root-wide header pre-scan.  A consumer looping `parse_theory` over a
    session's files sees each header alone, so a theory using a custom command
    another theory declares loses its declarations with no warning — the exact
    trap `CONTRIBUTING.md` names ("the library caller gets the same one as the
    CLI").  Two theories, the command declared in one and used in the other.
    """

    DECLARER = ('theory A\n  imports Main\n  keywords "mydef" :: thy_defn\n'
                'begin\nend\n')
    USER = ('theory B\nimports A\nbegin\n'
            'mydef gadget :: "bool" where "gadget = True"\n'
            'end\n')

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self._tmp.name)
        (self.dir / "A.thy").write_text(self.DECLARER, encoding="utf-8")
        (self.dir / "B.thy").write_text(self.USER, encoding="utf-8")
        (self.dir / "ROOT").write_text(
            'session Demo = HOL +\n  theories\n    A\n    B\n', encoding="utf-8")

    def tearDown(self):
        self._tmp.cleanup()

    def test_parse_root_sees_the_sibling_declaration(self):
        secs = {s.theory: s for s in api.parse_root(self.dir)}
        self.assertIn("B", secs)
        self.assertIn("gadget", [e.name for e in secs["B"].entries])

    def test_parse_theory_alone_does_not(self):
        # Not a defect — a documented scope limit, pinned so the docstring
        # cannot drift from the behaviour it warns about.
        #
        # The `parse_root` call is deliberate and load-bearing: the keyword
        # table is a module global, so without it this passes for the wrong
        # reason (nothing had populated the table) and fails as soon as another
        # test in the file runs first.  Which is how the leak was found —
        # `parse_theory` was returning `gadget` here purely because the test
        # above it had left `mydef` in the table.  Ordering must not be what
        # makes a test true.
        api.parse_root(self.dir)
        sec = api.parse_theory("B", self.dir / "B.thy")
        self.assertNotIn("gadget", [e.name for e in sec.entries])

    def test_parse_theory_leaves_the_table_as_it_found_it(self):
        # The other half: a `parse_theory` in the middle of a session-scoped
        # workflow must not silently narrow the next `parse_root` result.
        first = {s.theory: s for s in api.parse_root(self.dir)}
        api.parse_theory("B", self.dir / "B.thy")
        again = {s.theory: s for s in api.parse_root(self.dir)}
        self.assertEqual([e.name for e in first["B"].entries],
                         [e.name for e in again["B"].entries])

    def test_two_roots_do_not_contaminate_each_other(self):
        other = self.dir / "other"
        other.mkdir()
        (other / "C.thy").write_text(
            'theory C\nimports Main\nbegin\n'
            'mydef stray :: "bool" where "stray = True"\n'
            'end\n', encoding="utf-8")
        (other / "ROOT").write_text(
            'session Other = HOL +\n  theories\n    C\n', encoding="utf-8")
        api.parse_root(self.dir)          # declares `mydef`
        secs = {s.theory: s for s in api.parse_root(other)}
        self.assertNotIn("stray", [e.name for e in secs["C"].entries],
                         "the previous root's keyword table survived")

    def test_an_unreadable_root_raises_rather_than_returning_empty(self):
        with self.assertRaises(ValueError):
            api.parse_root(self.dir / "nope")

    def test_a_root_with_no_theories_raises(self):
        empty = self.dir / "empty"
        empty.mkdir()
        with self.assertRaises(ValueError):
            api.parse_root(empty)


class ImportingThePackageStaysFree(unittest.TestCase):
    """`import isabelle_query` must not pull the parser.

    The cost of the issue's "smallest version" — `__all__` in `__init__.py` —
    and the reason this is a submodule instead.  `_prog` (the invoked command
    name) and the version lookup both import the package and want neither the
    parser nor `re`-compiled scanners.
    """

    def test_the_package_import_does_not_load_parsing(self):
        code = ("import sys, isabelle_query; "
                "print([m for m in ('isabelle_query.parsing', "
                "'isabelle_query.api', 'isabelle_query.cli') "
                "if m in sys.modules])")
        out = subprocess.run([sys.executable, "-c", code],
                             capture_output=True, text=True, check=True)
        self.assertEqual(out.stdout.strip(), "[]")

    def test_the_api_module_does_not_pull_the_cli(self):
        # `api` sits above `parsing` in the module DAG and must not reach up
        # into `cli`, which would drag argparse and every command handler in.
        code = ("import sys, isabelle_query.api; "
                "print('isabelle_query.cli' in sys.modules)")
        out = subprocess.run([sys.executable, "-c", code],
                             capture_output=True, text=True, check=True)
        self.assertEqual(out.stdout.strip(), "False")


class TheModuleDagStillHolds(unittest.TestCase):
    """`api` imports only from `model` and `parsing` — a leaf on the DAG."""

    def test_api_imports_stay_below_it(self):
        import ast
        src = Path(importlib.import_module("isabelle_query.api").__file__)
        allowed = {"isabelle_query.model", "isabelle_query.parsing"}
        found = {n.module for n in ast.walk(ast.parse(src.read_text()))
                 if isinstance(n, ast.ImportFrom) and n.module
                 and n.module.startswith("isabelle_query")}
        self.assertEqual(found - allowed, set())


if __name__ == "__main__":
    unittest.main()
