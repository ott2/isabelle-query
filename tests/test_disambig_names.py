r"""A printed theory name is qualified far enough to name one theory.

A theory prints as its bare stem, which is right for a session and wrong for a
corpus: **461 AFP theory names are used by more than one theory**, covering
1,219 of its 9,910.  Nineteen files are called `Examples`, fifteen
`Preliminaries`, twelve `Semantics`.  `query largest` over the AFP was a wall
of unqualified `Bla` with no way to tell one from another [disambig-names].

`render.theory_labels` gives each the shortest directory-qualified name that
identifies it uniquely — `Virtual_Substitution/QE`,
`JinjaDCI/Compiler/Correctness2` — and leaves the rest bare.  Over the whole
AFP that grows 1,219 of 9,910 labels and changes nothing else.  (Growing them
from the file's STEM instead qualified 1,316; the extra 97 are theories whose
files collide while their declared names do not — see `theory_labels`.)

**Scoped to the loaded corpus, not to the rows on screen**, and that is the
distinction the item itself got imprecise about.  Whether `Examples:11` names
one theory is a fact about the corpus, not about which theories a `-N 8`
happened to print; a label unique on screen and ambiguous on paste is worse
than no label, because it invites the paste.  `ScopedToTheCorpusNotTheScreen`
is that test.

The round-trip is the point rather than the tidiness.  `theory:line` is meant
to be valid input to `enclosing` / `lines` / `show`, so the emitter has to
qualify far enough for the resolver to get back to one theory — and no
further, since a shared root prefix distinguishes nothing.  Half the resolver
side already exists: since [name-roundtrip] a name containing a separator
resolves *as a name*, which is what makes `Virtual_Substitution/QE` paste-able
rather than a path that does not exist.
"""

import os
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, os.path.dirname(__file__))
from isabelle_query import cli  # noqa: E402
from isabelle_query.render import theory_labels  # noqa: E402

THY = 'theory {name}\nimports Main\nbegin\nlemma l{tag}: "True" by simp\nend\n'


class LabelFixture(unittest.TestCase):
    """Two entries each declaring `Examples`, plus a theory named once."""

    LAYOUT = {
        "alpha/Examples": "Examples",
        "beta/Examples": "Examples",
        "alpha/Unique": "Unique",
    }

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self._tmp.name)
        for i, (rel, name) in enumerate(self.LAYOUT.items()):
            p = self.dir / f"{rel}.thy"
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(THY.format(name=name, tag=i), encoding="utf-8")
        for entry in ("alpha", "beta"):
            theories = "\n    ".join(
                n for r, n in self.LAYOUT.items() if r.startswith(entry + "/"))
            (self.dir / entry / "ROOT").write_text(
                f"session {entry.title()} = HOL +\n  theories\n    {theories}\n",
                encoding="utf-8")
        cli._ROOT_OVERRIDE = self.dir
        self.sections = cli.load_index()

    def tearDown(self):
        cli._ROOT_OVERRIDE = None
        self._tmp.cleanup()

    def label(self, rel):
        labels = theory_labels(self.sections)
        return labels[(self.dir / f"{rel}.thy").resolve()]


class OnlyACollisionGrowsAPrefix(LabelFixture):

    def test_a_colliding_name_is_qualified(self):
        self.assertEqual(self.label("alpha/Examples"), "alpha/Examples")
        self.assertEqual(self.label("beta/Examples"), "beta/Examples")

    def test_a_unique_name_stays_bare(self):
        self.assertEqual(self.label("alpha/Unique"), "Unique")

    def test_the_shared_root_prefix_is_not_shown(self):
        # The tmpdir is a component of every path and distinguishes nothing.
        for rel in self.LAYOUT:
            with self.subTest(theory=rel):
                self.assertNotIn(self.dir.name, self.label(rel))

    def test_every_label_is_unique(self):
        labels = theory_labels(self.sections)
        self.assertEqual(len(set(labels.values())), len(labels))


class ScopedToTheCorpusNotTheScreen(LabelFixture):
    r"""The distinction that makes the label round-trip.

    Qualifying against the printed rows is the tempting reading — it is even
    what the todo item said — and it breaks the thing the item wanted:
    `Examples:11` is ambiguous because the CORPUS has two, whether or not both
    are on screen.
    """

    def test_a_collision_qualifies_even_when_shown_alone(self):
        one = [s for s in self.sections if s.theory == "Examples"][:1]
        # Against the corpus: qualified, because a second `Examples` exists.
        self.assertIn("/", theory_labels(self.sections)[one[0].path.resolve()])
        # Against that one row alone it would be bare — the wrong answer, and
        # the reason `cmd_largest` passes `sections` rather than `rows[:top]`.
        self.assertNotIn("/", theory_labels(one)[one[0].path.resolve()])


class TheLabelIsValidInput(LabelFixture):
    """A qualified label must resolve back to the theory it names."""

    def test_a_qualified_label_round_trips(self):
        from isabelle_query.commands import _resolve_theory
        for rel in ("alpha/Examples", "beta/Examples", "alpha/Unique"):
            with self.subTest(theory=rel):
                sec = _resolve_theory(self.sections, self.label(rel))
                self.assertIsNotNone(sec, f"{self.label(rel)} did not resolve")
                self.assertEqual(sec.path.resolve(),
                                 (self.dir / f"{rel}.thy").resolve())


class APathSpelledNameIsSegments(unittest.TestCase):
    r"""A ROOT may spell a theory with a directory, and then its NAME is
    several segments [label-depth].

    The AFP shape: Van_Emde_Boas_Trees keeps a copy of a theory under the
    name `Separation_Logic_Imperative_HOL/Automation`, and the genuine one is
    `Automation` in `Separation_Logic_Imperative_HOL/`.  Labels were compared
    only at equal depth, so the genuine theory's depth-2 label and the copy's
    depth-1 label were the same string, and pasting it back gave the copy.
    And a copy pushed past its name printed the name's directory twice
    (`VEB/SL/SL/Automation`), a label that resolved to nothing.  Nine AFP
    labels failed the round-trip; `scripts/probe_label_roundtrip.py`.
    """

    LAYOUT = {   # directory: (theory as the ROOT spells it, file under it)
        "SL": ("Automation", "Automation"),
        "Other": ("Automation", "Automation"),
        "VEB": ('"SL/Automation"', "SL/Automation"),
        "VEB2": ('"SL/Automation"', "SL/Automation"),
    }

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self._tmp.name)
        for i, (entry, (spelled, rel)) in enumerate(self.LAYOUT.items()):
            p = self.dir / entry / f"{rel}.thy"
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(THY.format(name="Automation", tag=i),
                         encoding="utf-8")
            (self.dir / entry / "ROOT").write_text(
                f"session {entry} = HOL +\n  theories\n    {spelled}\n",
                encoding="utf-8")
        cli._ROOT_OVERRIDE = self.dir
        self.sections = cli.load_index()
        self.labels = theory_labels(self.sections)

    def tearDown(self):
        cli._ROOT_OVERRIDE = None
        self._tmp.cleanup()

    def path(self, entry):
        return (self.dir / entry / f"{self.LAYOUT[entry][1]}.thy").resolve()

    def test_the_fixture_has_path_spelled_names(self):
        self.assertEqual(sorted(s.theory for s in self.sections),
                         ["Automation", "Automation",
                          "SL/Automation", "SL/Automation"])

    def test_no_two_theories_share_a_label(self):
        self.assertEqual(len(set(self.labels.values())), 4)

    def test_the_labels(self):
        # The genuine one cannot stop at `SL/Automation`: that is the copies'
        # NAME, and the resolver tries names first.  So it takes the one
        # component that separates it, even though it is the shared root.
        self.assertEqual(self.labels[self.path("SL")],
                         f"{self.dir.resolve().name}/SL/Automation")
        self.assertEqual(self.labels[self.path("Other")], "Other/Automation")
        # A real path suffix, not `VEB/SL/SL/Automation`.
        self.assertEqual(self.labels[self.path("VEB")], "VEB/SL/Automation")
        self.assertEqual(self.labels[self.path("VEB2")], "VEB2/SL/Automation")

    def test_every_label_round_trips(self):
        from isabelle_query.commands import _resolve_theory
        for entry in self.LAYOUT:
            with self.subTest(entry=entry):
                sec = _resolve_theory(self.sections,
                                      self.labels[self.path(entry)])
                self.assertIsNotNone(sec)
                self.assertEqual(sec.path.resolve(), self.path(entry))


class Degenerate(unittest.TestCase):
    """Inputs that must not loop or raise."""

    def test_no_sections(self):
        self.assertEqual(theory_labels([]), {})

    def test_the_same_section_twice_is_one_theory(self):
        # Not a collision: one path, one label, and no suffix can separate a
        # path from itself — the case the depth guard exists for.
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "Solo.thy"
            p.write_text(THY.format(name="Solo", tag=0), encoding="utf-8")
            sec = cli._parse_one("Solo", p)
            labels = theory_labels([sec, sec])
            self.assertEqual(list(labels.values()), ["Solo"])


if __name__ == "__main__":
    unittest.main()
