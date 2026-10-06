r"""Each header says `[k of n]` when there is more than one match [show-match-count].

Issue #17: `clock_lang` is declared twice, and `show clock_lang` said so only
in its LAST line, `[+1 more match(es). ...]`.  That is the first line `head`
or a line filter drops, and a caller who lost it concluded that `show`
collapsed duplicate names.  The header is the line every filter keeps, so the
count goes there too.  A single match keeps its header as it was.
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

A = r'''theory A imports Main begin
lemma twice: "True" by simp
lemma once: "True" by simp
end
'''

B = r'''theory B imports Main begin
lemma twice: "True" by simp
end
'''


def headers(name, mode="first", cmd=commands.cmd_show):
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        cmd([section_from(A, "A"), section_from(B, "B")], name,
            CmdFlags(mode=mode))
    return [ln for ln in out.getvalue().splitlines() if ln.startswith("---")]


class TheHeaderCarriesTheCount(unittest.TestCase):

    def test_first_of_two(self):
        self.assertEqual(headers("twice"), [
            "--- twice (LEMMA) — A.thy [1 of 2] [src 2..2, 1 lines] ---"])

    def test_all_numbers_each(self):
        self.assertEqual(headers("twice", "all"), [
            "--- twice (LEMMA) — A.thy [1 of 2] [src 2..2, 1 lines] ---",
            "--- twice (LEMMA) — B.thy [2 of 2] [src 2..2, 1 lines] ---"])

    def test_a_single_match_is_unchanged(self):
        self.assertEqual(headers("once"), [
            "--- once (LEMMA) — A.thy [src 3..3, 1 lines] ---"])

    def test_find_shares_the_header(self):
        self.assertIn("[1 of 2]", headers("twice", cmd=commands.cmd_find)[0])


if __name__ == "__main__":
    unittest.main()
