#!/usr/bin/env python3
r"""Probe: does `show --premises` read every statement? [show-premises]

Runs `premises.statement_of` over every LEMMA/THEOREM in a corpus and counts
the statements it declines (`None`, which the view reports as "statement not
recognised") and any that raise, with samples of each, plus the shape of what
it did read.  A declined statement is safe -- the view says so -- but each is
one the caller then has to read in full.

Usage:  probe_premises_view.py [DIR] [--samples N]     (default: the AFP)
"""
from __future__ import annotations

import random
import sys
import time
from collections import Counter
from pathlib import Path

_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_ROOT / "src"))

from isabelle_query import cli  # noqa: E402
from isabelle_query.premises import statement_of  # noqa: E402

AFP = Path.home() / "repos" / "afp" / "thys"


def main() -> None:
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    k = int(sys.argv[sys.argv.index("--samples") + 1]) \
        if "--samples" in sys.argv else 8
    if "--samples" in sys.argv:
        args = [a for a in args if a != str(k)]
    base = Path(args[0]).expanduser() if args else AFP
    n = declined = raised = 0
    premises: Counter[int] = Counter()
    kinds: Counter[str] = Counter()
    bad: list[str] = []
    errs: list[str] = []
    spent = 0.0
    for p in sorted(base.rglob("*.thy")):
        try:
            sec = cli._parse_one(p.stem, p)
        except Exception:  # noqa: BLE001
            continue
        for e in sec.entries:
            if e.tag not in ("LEMMA", "THEOREM") or not e.thy_line:
                continue
            n += 1
            t0 = time.perf_counter()
            try:
                st = statement_of(sec, e)
            except Exception as exc:  # noqa: BLE001
                raised += 1
                errs.append(f"{p}:{e.thy_line} {e.name}: {exc!r}")
                continue
            finally:
                spent += time.perf_counter() - t0
            if st is None:
                declined += 1
                bad.append(f"{p.relative_to(base)}:{e.thy_line} {e.name}")
                continue
            premises[min(len(st.premises), 10)] += 1
            for pr in st.premises:
                kinds[pr.kind] += 1

    print(f"=== {n:,} LEMMA/THEOREM entries under {base} ===")
    print(f"  declined: {declined:,} ({100 * declined / max(n, 1):.2f}%)")
    print(f"  raised:   {raised:,}")
    print(f"  time in statement_of: {spent:.1f}s")
    print("\npremises per statement (10 = 10+):")
    for c in sorted(premises):
        print(f"  {c:>3}  {premises[c]:>9,}")
    print("\npremise kinds:")
    for kd, c in kinds.most_common():
        print(f"  {kd:<8} {c:>9,}")
    rnd = random.Random(0)
    for title, xs in (("declined", bad), ("raised", errs)):
        if xs:
            print(f"\n{title} (random sample):")
            for x in rnd.sample(xs, min(k, len(xs))):
                print(f"  {x}")


if __name__ == "__main__":
    main()
