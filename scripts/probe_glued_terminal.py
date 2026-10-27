#!/usr/bin/env python3
r"""How each reader takes a symbolic name glued to a terminal `.`/`..` (#37).

The fact walk on bare lines, then fan-in and `unused facts` rows for the
#37 lemmas of `tests/test_symbolic_labels.py`.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "tests"))
import test_symbolic_labels as t  # noqa: E402

from isabelle_query import proof_locals  # noqa: E402
from isabelle_query.graph import _cited_facts_on_line  # noqa: E402

for line in ("using *.", "unfolding *..", "using a.", "using * .",
             "using **..", "by (rule *.foo)"):
    print(f"{line!r:28} {_cited_facts_on_line(line)}")
names = ("named_glued", "sym_spaced", "sym_glued", "sym_glued_rule")
for n in names:
    print(f"{n:16} fanin {t._fanin(n)}")
sec = t.section_from(t.SRC, theory="Sy")
for _, b in proof_locals.unread_locals([sec]):
    if b.entry in names:
        print("unused", b.entry, b.name)
