#!/usr/bin/env python3
"""What [body-end-text] moves in the `shape` step scan.

Parses the corpus twice, with `parsing._proof_close_line` live and stubbed to
0 — which is exactly the old extent, since a proof never seen to close keeps
its first `text` boundary — and compares proofs changed, steps scanned, and
goal steps.

Usage:  python3 scripts/probe_body_end_census.py <corpus-dir>
"""
from __future__ import annotations

import sys
from pathlib import Path

from isabelle_query import parsing, shape


def census(corpus: Path) -> dict[tuple[Path, str, int], tuple[int, int, int]]:
    # `_sections_from_dir` MERGES each header's custom commands into one
    # module-level table and only `load_index` clears it, so a second pass
    # over the same corpus starts with every keyword the first one met — 581
    # more AFP proofs than a cold pass.  Clearing makes the two passes alike.
    parsing._CUSTOM_COMMANDS.clear()
    out = {}
    for root in sorted(p for p in corpus.iterdir() if (p / "ROOT").exists()):
        sections: list = []
        parsing._sections_from_dir(root, set(), sections)
        for sec in sections:
            for e in sec.entries:
                if e.proof_line:
                    steps = shape._scan_steps(sec, e)
                    out[(sec.path, e.name, e.thy_line)] = (
                        e.body_end_line, len(steps),
                        sum(1 for s in steps if s.kind == "goal"))
    return out


def main() -> int:
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    corpus = Path(sys.argv[1]).expanduser()
    new = census(corpus)
    live = parsing._proof_close_line
    parsing._proof_close_line = lambda *a: 0
    try:
        old = census(corpus)
    finally:
        parsing._proof_close_line = live
    moved = [k for k in new if new[k][0] != old.get(k, new[k])[0]]
    shorter = [k for k in moved if new[k][0] < old[k][0]]
    tot = [sum(v[i] for v in d.values()) for d in (old, new) for i in (1, 2)]
    print(f"{len(new)} proofs; body_end_line moved for {len(moved)} "
          f"({len(shorter)} shorter)")
    print(f"steps  {tot[0]} -> {tot[2]}  ({(tot[2] - tot[0]) / tot[0]:+.3%})")
    print(f"goals  {tot[1]} -> {tot[3]}  ({(tot[3] - tot[1]) / tot[1]:+.3%})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
