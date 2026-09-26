#!/usr/bin/env python3
"""What every `-c`/`--count` verb prints when nothing matches [count-mode-zero].

A count mode should print a NUMBER.  Where it prints a sentence instead,
`$(query find X -c)` is a parse error rather than arithmetic — and the empty
case is the one a script most wants to branch on.  Whether the verbs agree with
each other is the part that was never pinned anywhere, which is why this asks
all of them rather than the one that prompted the item.

    python scripts/probe_count_modes.py [ROOT]

Builds its own throwaway root when none is given, so the answer does not depend
on what happens to be in a corpus.
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

_ROOT = Path(__file__).resolve().parent.parent
QUERY = str(_ROOT / ".venv" / "bin" / "query")

THY = '''theory T
imports Main
begin
definition d :: "nat" where "d = 0"
lemma l: "d = d" by (simp add: d_def)
end
'''

# (label, argv, kind).  `zzz` matches nothing anywhere.
#
#   "zero"    — the answer really is zero, so a NUMBER is the only right output.
#   "unknown" — the SUBJECT does not exist, so the question could not be asked.
#               A `0` there would be the silent zero `CONTRIBUTING.md` forbids.
#               Since [unresolved-subject] these keep stdout EMPTY, put the
#               diagnostic on stderr and exit 1, so `$(...)` captures nothing
#               and `$?` says why.
#   "control" — a non-empty answer, because a count mode that cannot count is
#               worse than one that prints a sentence.
#
# `deps`, `uses`, `lines` and `largest` carry no `-c` at all and are absent:
# asking them would report this script's mistake as the tool's.
CASES = [
    ("find", ["find", "-c", "zzz"], "zero"),
    ("show", ["show", "-c", "zzz"], "zero"),
    ("grep", ["grep", "-c", "zzz"], "zero"),
    ("unused", ["unused", "-c"], "zero"),
    ("unused --locals", ["unused", "--locals", "-c"], "zero"),
    # An entry selector names an entry that must exist, like a subject.
    ("unused T:zzz", ["unused", "--locals", "-c", "T:zzz"], "unknown"),
    ("sorry", ["sorry", "-c"], "zero"),
    # `callers` looks like the odd one out and is not: it SCANS source for a
    # token, so "zero mentions" is a truthful answer whether or not the name is
    # a declared entry.  `callees` needs the entry to exist before it can have
    # callees.  Different questions, so different empty answers is right.
    ("callers", ["callers", "-c", "zzz"], "zero"),
    ("callees", ["callees", "-c", "zzz"], "unknown"),
    ("refs", ["refs", "-c", "zzz"], "unknown"),
    ("methods", ["methods", "-c", "zzz"], "unknown"),
    # The site verbs need a declared subject before they can have sites: a
    # locale from an imported session would otherwise look exactly like one
    # nobody instantiates.
    ("instances", ["instances", "-c", "zzz"], "unknown"),
    ("codeqs", ["codeqs", "-c", "zzz"], "unknown"),
    ("find (hit)", ["find", "-c", "d"], "control"),
    ("methods (hit)", ["methods", "-c", "simp"], "control"),
    # `definition d` registers its own default code equation.
    ("codeqs (hit)", ["codeqs", "-c", "d"], "control"),
]


def main() -> int:
    if len(sys.argv) > 1:
        root = Path(sys.argv[1]).expanduser()
        tmp = None
    else:
        tmp = tempfile.TemporaryDirectory(dir=_ROOT)
        root = Path(tmp.name)
        (root / "T.thy").write_text(THY)
        (root / "ROOT").write_text("session Z = HOL +\n  theories\n    T\n")

    bad = 0
    print(f"{'verb':14} {'kind':8} {'exit':>4}  output")
    print("-" * 70)
    for label, argv, kind in CASES:
        r = subprocess.run([QUERY, "-R", str(root), *argv],
                           capture_output=True, text=True)
        out = r.stdout.strip()
        err = r.stderr.strip().splitlines()
        if kind == "unknown":
            # Nothing on stdout, something on stderr, exit 1.
            ok = out == "" and bool(err) and r.returncode == 1
            shown = err[0] if err else "<no diagnostic>"
        else:
            ok = out.lstrip("-").isdigit() and r.returncode == 0
            shown = out or "<empty>"
        if not ok:
            bad += 1
        print(f"{label:14} {kind:8} {r.returncode:>4}  "
              f"{'' if ok else '<-- WRONG '}{shown[:40]}")
    print("-" * 70)
    print(f"{bad} of {len(CASES)} count modes answer wrongly")
    if tmp is not None:
        tmp.cleanup()
    return bad


if __name__ == "__main__":
    raise SystemExit(main())
