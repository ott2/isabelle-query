#!/usr/bin/env python3
"""What `parse_theory(..., root=)` costs against `parse_root` [cut-span].

The `root=` route reads every header under ROOT but parses one body; a tool
that edits one file per call (NDTHT's `block.py`) cares about the difference.

Usage:  python3 scripts/time_parse_theory_root.py ROOT THEORY.thy
"""
from __future__ import annotations

import sys
import time
from pathlib import Path

from isabelle_query.api import parse_root, parse_theory


def main() -> int:
    if len(sys.argv) != 3:
        print(__doc__)
        return 2
    root, thy = Path(sys.argv[1]).expanduser(), Path(sys.argv[2]).expanduser()
    t0 = time.perf_counter()
    alone = parse_theory(thy.stem, thy)
    t1 = time.perf_counter()
    rooted = parse_theory(thy.stem, thy, root=root)
    t2 = time.perf_counter()
    full = next(s for s in parse_root(root)
                if s.path.resolve() == thy.resolve())
    t3 = time.perf_counter()
    key = lambda s: [(e.name, e.thy_line, e.cut_span) for e in s.entries]
    print(f"parse_theory alone:     {t1 - t0:6.2f}s  {len(alone.entries)} entries")
    print(f"parse_theory(root=):    {t2 - t1:6.2f}s  {len(rooted.entries)} entries")
    print(f"parse_root:             {t3 - t2:6.2f}s  {len(full.entries)} entries")
    print(f"root= agrees with parse_root: {key(rooted) == key(full)}")
    print(f"cut_span None: {sum(e.cut_span is None for e in rooted.entries)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
