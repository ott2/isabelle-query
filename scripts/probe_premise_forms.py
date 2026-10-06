#!/usr/bin/env python3
r"""Probe: how do facts state their premises? [show-premises]

Issue #17 asks for `show --premises`: one line per premise, with its label.
That is easy for the long form and not obviously defined for the others, so
this counts each form over the AFP, reading each LEMMA/THEOREM's statement
slice (`thy_line..decl_end_line`):

    long       `assumes a: "P" and "Q" shows "R"`     premises are Isar elements
    if         `shows "R" if a: "P" for x`             the same, written after
    arrow      `"P \<Longrightarrow> Q \<Longrightarrow> R"`   premises inside one term
    obtains    `obtains x where "P x"`                 an elimination: cases, not premises
    none       `"R"`                                   no premises at all

A statement can mix them (`assumes "P" shows "Q \<Longrightarrow> R"`), so
the forms are counted independently, and the combinations as well.  Element
keywords are read on the OUTER view (inner syntax blanked), and the arrow on
the live view.

Usage:  probe_premise_forms.py [DIR]     (default: the AFP)
"""
from __future__ import annotations

import re
import sys
from collections import Counter
from pathlib import Path

_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_ROOT / "src"))

from isabelle_query import cli  # noqa: E402

AFP = Path.home() / "repos" / "afp" / "thys"

_KW = {k: re.compile(rf"(?<![\w']){k}(?![\w'])")
       for k in ("assumes", "shows", "obtains", "if", "fixes", "defines")}
_ARROW = re.compile(r"\\<Longrightarrow>|⟹|==>|\\<And>|⋀|!!")
# A labelled `assumes` element, as `--premises` would print it.
_LABEL = re.compile(r"(?<![\w'])(?:assumes|and|if)\s+([A-Za-z][\w']*)\s*"
                    r"(?:\[[^\]]*\])?\s*:(?!:)")


def main() -> None:
    forms: Counter[str] = Counter()
    combos: Counter[str] = Counter()
    labelled = unlabelled_long = 0
    n = 0
    base = Path(sys.argv[1]).expanduser() if len(sys.argv) > 1 else AFP
    for p in sorted(base.rglob("*.thy")):
        try:
            sec = cli._parse_one(p.stem, p)
        except Exception:  # noqa: BLE001
            continue
        outer, live = sec.outer_source(), sec.live_source()
        for e in sec.entries:
            if e.tag not in ("LEMMA", "THEOREM") or not e.thy_line:
                continue
            n += 1
            lo, hi = e.thy_line - 1, max(e.decl_end_line, e.thy_line)
            o = "\n".join(outer[lo:hi])
            lv = "\n".join(live[lo:hi])
            got = set()
            if _KW["assumes"].search(o):
                got.add("long")
            if _KW["if"].search(o):
                got.add("if")
            if _KW["obtains"].search(o):
                got.add("obtains")
            if _ARROW.search(lv):
                got.add("arrow")
            if not got:
                got.add("none")
            for f in got:
                forms[f] += 1
            combos["+".join(sorted(got))] += 1
            if "long" in got or "if" in got:
                if _LABEL.search(o):
                    labelled += 1
                else:
                    unlabelled_long += 1

    print(f"=== {n:,} LEMMA/THEOREM entries under {base} ===\n")
    print("each form (a statement may have several):")
    for f, c in forms.most_common():
        print(f"  {f:<10} {c:>9,}  {100 * c / n:5.1f}%")
    print("\ncombinations:")
    for f, c in combos.most_common(12):
        print(f"  {f:<24} {c:>9,}  {100 * c / n:5.1f}%")
    tot = labelled + unlabelled_long
    print(f"\nlong/if statements with at least one labelled premise: "
          f"{labelled:,} of {tot:,} ({100 * labelled / max(tot, 1):.1f}%)")


if __name__ == "__main__":
    main()
