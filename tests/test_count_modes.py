r"""A count mode prints a NUMBER, including when the answer is zero.

`find zzz -c` printed `No entries matching 'zzz'.` where a count mode should
print `0`.  The sentence came from `render._emit_matches`'s empty guard, which
ran *before* the mode dispatch, so every verb funnelling through it (`find`,
`show`) was affected; `unused` had the same shape in `_render_unused`.

Small, and the difference between `$(query find X -c)` being arithmetic and
being a parse error — and the empty case is the one a script most wants to
branch on, so it was wrong exactly where it mattered most.

**The agreement between verbs is what this file really pins**, because that is
what was never checked anywhere.  `scripts/probe_count_modes.py` asks all of
them at once; this is the same question as a test.  There are two kinds of
empty and they are not the same answer:

* **zero** — the answer really is zero (`find`, `show`, `grep`, `unused`,
  `sorry`, and `callers`, which SCANS source and can truthfully report zero
  mentions of any token).  A number is the only right output.
* **unknown** — the SUBJECT does not exist, so the question could not be asked
  (`callees`, `refs`, `methods`).  Printing `0` there would be the silent zero
  `CONTRIBUTING.md` forbids: a caller cannot tell a broken run from a real one.
  These keep their diagnostic.  That they print it on *stdout* and exit *0* is
  a separate defect, filed as `[unresolved-subject]`.

`--names` gets the same treatment as `--count` and for the same reason: an
empty list is the right answer for a pipeline, and a sentence on stdout would
be read as a name.
"""

import io
import os
import sys
import unittest
from contextlib import redirect_stderr, redirect_stdout

sys.path.insert(0, os.path.dirname(__file__))
from support import section_from  # noqa: E402
from isabelle_query import commands  # noqa: E402
from isabelle_query.model import CmdFlags  # noqa: E402

THY = '''theory T
imports Main
begin
definition d :: "nat" where "d = 0"
lemma l: "d = d" by (simp add: d_def)
end
'''


def run(fn, *args, **kw):
    buf = io.StringIO()
    with redirect_stdout(buf):
        fn(*args, **kw)
    return buf.getvalue().strip()


class AnHonestZeroPrintsZero(unittest.TestCase):

    def setUp(self):
        self.sections = [section_from(THY, "T")]

    def test_find_with_no_match(self):
        out = run(commands.cmd_find, self.sections, "zzz",
                  CmdFlags(mode="count"))
        self.assertEqual(out, "0")

    def test_show_with_no_match(self):
        out = run(commands.cmd_show, self.sections, "zzz",
                  CmdFlags(mode="count"))
        self.assertEqual(out, "0")

    def test_unused_when_nothing_is_unused(self):
        out = run(commands._render_unused, [], CmdFlags(mode="count"), False)
        self.assertEqual(out, "0")

    def test_defs_of_a_theory_without_definitions(self):
        thy = section_from(THY.replace("theory T", "theory U")
                           .replace('definition d :: "nat" where "d = 0"\n',
                                    ""), "U")
        self.assertEqual(run(commands.cmd_defs, [thy], "U",
                             CmdFlags(mode="count")), "0")
        self.assertEqual(run(commands.cmd_defs, [thy], "U",
                             CmdFlags(mode="names")), "")
        self.assertEqual(run(commands.cmd_defs, [thy], "U", CmdFlags()),
                         "No definitions found in 'U'.")

    def test_the_count_is_parseable_as_a_number(self):
        # The whole point: `$(query find X -c)` must be arithmetic.
        for pattern in ("zzz", "d"):
            with self.subTest(pattern=pattern):
                out = run(commands.cmd_find, self.sections, pattern,
                          CmdFlags(mode="count"))
                self.assertEqual(str(int(out)), out)


class AnHonestZeroPrintsNothingInNamesMode(unittest.TestCase):
    """`--names` feeds a pipeline; a sentence there would read as a name."""

    def setUp(self):
        self.sections = [section_from(THY, "T")]

    def test_find_names_with_no_match(self):
        self.assertEqual(
            run(commands.cmd_find, self.sections, "zzz",
                CmdFlags(mode="names")), "")

    def test_show_names_with_no_match(self):
        self.assertEqual(
            run(commands.cmd_show, self.sections, "zzz",
                CmdFlags(mode="names")), "")


class TheHumanModesStillSaySo(unittest.TestCase):
    """Guard: passes before and after.  Only the machine modes changed."""

    def setUp(self):
        self.sections = [section_from(THY, "T")]

    def test_the_default_mode_still_explains(self):
        out = run(commands.cmd_find, self.sections, "zzz", CmdFlags())
        self.assertEqual(out, "No entries matching 'zzz'.")

    def test_the_all_mode_still_explains(self):
        out = run(commands.cmd_find, self.sections, "zzz",
                  CmdFlags(mode="all"))
        self.assertEqual(out, "No entries matching 'zzz'.")

    def test_unused_still_explains(self):
        out = run(commands._render_unused, [], CmdFlags(), False)
        self.assertEqual(out, "No unused entries found.")

    def test_a_real_count_is_unchanged(self):
        out = run(commands.cmd_find, self.sections, "d", CmdFlags(mode="count"))
        self.assertEqual(out, "1")


class AnUnknownSubjectIsNotZero(unittest.TestCase):
    r"""The other kind of empty, and it must NOT become a number.

    `callees zzz` cannot be answered without an entry called `zzz`.  Reporting
    `0` would be indistinguishable from an honestly empty answer, which is the
    silent-zero rule in `CONTRIBUTING.md` — the same reasoning that makes an
    unreadable root exit 2 rather than print nothing.

    Pinned here because "fix the count modes" is exactly the change that would
    sweep these into `0` as well, and the two kinds of empty look identical
    from the call site.
    """

    def setUp(self):
        self.sections = [section_from(THY, "T")]

    def unresolved(self, fn, *args):
        """Run `fn`, expecting it to exit 1 with a diagnostic on stderr."""
        err = io.StringIO()
        out = io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            with self.assertRaises(SystemExit) as caught:
                fn(*args)
        self.assertEqual(caught.exception.code, 1)
        # stdout must stay clean — that is what makes `$(...)` usable.
        self.assertEqual(out.getvalue(), "")
        return err.getvalue()

    def test_callees_of_a_nonexistent_entry(self):
        err = self.unresolved(commands.cmd_callees, self.sections, "zzz",
                              CmdFlags(mode="count"))
        self.assertIn("not in the entry index", err)

    def test_refs_of_a_nonexistent_theory(self):
        err = self.unresolved(commands.cmd_refs, self.sections, "zzz",
                              CmdFlags(mode="count"))
        self.assertIn("no theory 'zzz'", err)

    def test_methods_for_a_name_that_is_no_method(self):
        err = self.unresolved(commands.cmd_methods, self.sections, "zzz",
                              CmdFlags(mode="count"))
        self.assertIn("proof method", err)

    def test_callers_scans_and_so_may_truthfully_be_zero(self):
        # Not an inconsistency: `callers` searches source for a token, so zero
        # mentions is a real answer whether or not the name is an entry.
        out = run(commands.cmd_callers, self.sections, "zzz",
                  CmdFlags(mode="count"))
        self.assertEqual(out, "0")


if __name__ == "__main__":
    unittest.main()
