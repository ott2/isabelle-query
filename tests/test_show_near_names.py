r"""`show` says when it falls back to near names [show-near-names].

Once no entry is named NAME, `show` lists the entries whose names CONTAIN it.
It used to do so silently, so the first near name was rendered under its own
header as though it were the answer: issue #16's `show table_tape_len` printed
`dth_descriptor_table_tape_length`.  The fallback stays; it now says so first.

A note is not an answer, so under `--names` / `--count` it goes to stderr,
where it cannot be read as a name or break a number -- the rule `callers -r`
already follows for its bound-name note.  `show`'s own bound-name note now
follows it too: `show -c` of a conjunct printed the note above the count.
"""

import contextlib
import io
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(__file__))
from support import section_from  # noqa: E402

from isabelle_query import commands  # noqa: E402
from isabelle_query.model import CmdFlags  # noqa: E402

THY = r'''theory T imports Main begin
lemma descriptor_tape_length: "True" by simp
lemma both: shows "True" and conj: "True" by simp_all
end
'''

NOTE = "# no entry named 'tape_len'; 1 whose name contains it:"


def run(name, mode="first"):
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        commands.cmd_show([section_from(THY, "T")], name, CmdFlags(mode=mode))
    return out.getvalue().splitlines(), err.getvalue().splitlines()


class TheFallbackSaysSo(unittest.TestCase):

    def test_first_line_of_the_default_view(self):
        out, err = run("tape_len")
        self.assertEqual(out[0], NOTE)
        self.assertIn("descriptor_tape_length (LEMMA)", out[1])
        self.assertEqual(err, [])

    def test_names_mode_keeps_stdout_names_only(self):
        out, err = run("tape_len", "names")
        self.assertEqual(len(out), 1)
        self.assertTrue(out[0].startswith("descriptor_tape_length (LEMMA)"))
        self.assertEqual(err, [NOTE])

    def test_count_mode_prints_only_the_number(self):
        self.assertEqual(run("tape_len", "count"), (["1"], [NOTE]))

    def test_an_exact_match_has_no_note(self):
        out, err = run("descriptor_tape_length")
        self.assertFalse(out[0].startswith("#"))
        self.assertEqual(err, [])


class TheBoundNameNoteFollowsTheSameRule(unittest.TestCase):

    def test_count_mode(self):
        out, err = run("conj", "count")
        self.assertEqual(out, ["1"])
        self.assertEqual(len(err), 1)
        self.assertTrue(err[0].startswith("# 'conj' is "))


if __name__ == "__main__":
    unittest.main()
