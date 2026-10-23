#!/usr/bin/env python3
"""Share of parse time spent finding mid-line declarations [midline-decl].

Times `parsing._mid_decls` against the whole `_parse_one` on the same
theories, in one process, so a busy machine slows both alike.

    python scripts/probe_midline_cost.py [--on-off | --words] FILE.thy [...]

`--on-off` instead times whole parses with the search and without it.
`--words` instead counts the `str.find` hits each keyword costs.
"""

import sys
import time
from pathlib import Path

from isabelle_query import parsing


def main() -> int:
    total = mid = 0.0
    for arg in sys.argv[1:]:
        p = Path(arg)
        t0 = time.perf_counter()
        sec = parsing._parse_one(p.stem, p)
        t1 = time.perf_counter()
        outer = sec.outer_source()
        t2 = time.perf_counter()
        parsing._mid_decls(outer)
        t3 = time.perf_counter()
        total += t1 - t0
        mid += t3 - t2
    print(f"parse {total:.2f}s, mid-line search {mid:.3f}s "
          f"({100 * mid / total:.2f}%)")
    return 0


def on_off(paths: list[str], rounds: int = 3) -> None:
    """`--on-off`: whole-parse time with the search, and with it stubbed
    out, alternating so that drift on a busy machine hits both."""
    real = parsing._mid_decls
    totals = {"on": 0.0, "off": 0.0}
    for r in range(rounds):
        for mode in (("on", "off") if r % 2 == 0 else ("off", "on")):
            parsing._mid_decls = real if mode == "on" else (lambda o: [])
            t0 = time.perf_counter()
            for arg in paths:
                p = Path(arg)
                parsing._parse_one(p.stem, p)
            totals[mode] += time.perf_counter() - t0
    parsing._mid_decls = real
    on, off = totals["on"], totals["off"]
    print(f"on {on:.2f}s, off {off:.2f}s over {rounds} rounds: "
          f"+{100 * (on - off) / off:.1f}%")


def per_keyword(paths: list[str]) -> None:
    """`--words`: how many `str.find` hits each keyword costs."""
    from collections import Counter
    hits: Counter[str] = Counter()
    for arg in paths:
        p = Path(arg)
        text = "\n".join(parsing._parse_one(p.stem, p).outer_source())
        for kw in parsing._DECL_WORD_LIST:
            hits[kw] += text.count(kw)
    for kw, c in hits.most_common():
        print(f"{c:9,}  {kw}")


if __name__ == "__main__":
    if sys.argv[1:2] == ["--on-off"]:
        on_off(sys.argv[2:])
        sys.exit(0)
    if sys.argv[1:2] == ["--words"]:
        per_keyword(sys.argv[2:])
        sys.exit(0)
    sys.exit(main())
