#!/usr/bin/env python3
"""Rate and crash sweep for `unused --locals` [unused-locals].

There is no prover-side oracle for "bound and never read" — Isabelle does not
warn — so a corpus answers two cheaper questions.  Does any real proof make
the scan raise?  And what is the unread RATE: issue #12 measured ~0 on
hand-written proofs and many on freshly trimmed copies, so a published corpus
of finished proofs should sit low, and a high rate is evidence about the
SCANNER.  Prints per-kind rates and a seeded sample of flagged bindings, with
their source line, for hand-checking.

Samples entries by STRIDE across the sorted list, not a prefix — `[:N]` is the
entries beginning with A.

Usage:  python3 scripts/probe_unused_locals.py <corpus-dir> [n-entries] [n-show]
"""
from __future__ import annotations

import random
import sys
import traceback
from collections import Counter
from pathlib import Path

from isabelle_query.parsing import _sections_from_dir
from isabelle_query.proof_locals import scan_proof


def main() -> int:
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    corpus = Path(sys.argv[1]).expanduser()
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    n_show = int(sys.argv[3]) if len(sys.argv) > 3 else 25
    entries = sorted(p for p in corpus.iterdir() if (p / "ROOT").exists())
    stride = max(1, len(entries) // n)
    picked = entries[::stride][:n]

    bound, unread, kept = Counter(), Counter(), Counter()
    proofs = fails = 0
    flagged: list[tuple[Path, int, str, str, str]] = []
    for root in picked:
        sections: list = []
        _sections_from_dir(root, set(), sections)
        for sec in sections:
            for e in sec.entries:
                if not e.proof_line:
                    continue
                proofs += 1
                try:
                    bs = scan_proof(sec, e)
                except Exception:
                    fails += 1
                    print(f"  !! {sec.path}:{e.proof_line} {e.name}")
                    traceback.print_exc()
                    continue
                for b in bs:
                    bound[b.kind] += 1
                    if b.kept:
                        kept[b.kind] += 1
                    elif not b.read:
                        unread[b.kind] += 1
                        flagged.append((sec.path, b.line, b.name, b.kind,
                                        sec.source()[b.line - 1].strip()))

    print(f"{len(picked)} entries, {proofs} proofs, {fails} scan failures")
    print(f"{'kind':<8} {'bound':>8} {'kept':>6} {'unread':>7}  rate")
    for kind in sorted(bound):
        rate = unread[kind] / bound[kind]
        print(f"{kind:<8} {bound[kind]:>8} {kept[kind]:>6} "
              f"{unread[kind]:>7}  {rate:.2%}")
    total = sum(bound.values())
    print(f"{'all':<8} {total:>8} {sum(kept.values()):>6} "
          f"{sum(unread.values()):>7}  {sum(unread.values()) / max(1, total):.2%}")
    random.seed(12)
    for path, line, name, kind, text in random.sample(
            flagged, min(n_show, len(flagged))):
        print(f"\n{path.relative_to(corpus)}:{line}  {name} ({kind})\n    {text}")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
