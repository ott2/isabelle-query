#!/usr/bin/env python3
r"""Compare two `query shape census` JSONL outputs field by field.

For each numeric field named (default: the M5 family), prints the summed
value in each file, the change, and how many entries moved.  Entries are
matched by (theory, lemma, line), so both files must come from the same
corpus.  A field `a*b` is the product of two, so `fanin_mean*n_goals` is
the premises counted.

    python scripts/diff_census_fields.py OLD.jsonl NEW.jsonl [FIELD ...]
"""

from __future__ import annotations

import json
import sys

_DEFAULT = ["fanin_max", "fanin_cited", "live_max", "live_mean",
            "introduce", "consume", "both"]


def _load(path: str) -> dict[tuple, dict]:
    out = {}
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            d = json.loads(line)
            out[(d.get("theory"), d.get("lemma"), d.get("line"))] = d
    return out


def _get(d: dict, field: str) -> float:
    v = 1.0
    for f in field.split("*"):
        v *= d.get(f) or 0
    return v


def main() -> int:
    if len(sys.argv) < 3:
        print(__doc__, file=sys.stderr)
        return 2
    old, new = _load(sys.argv[1]), _load(sys.argv[2])
    fields = sys.argv[3:] or _DEFAULT
    keys = old.keys() & new.keys()
    print(f"entries: {len(old):,} old, {len(new):,} new, {len(keys):,} "
          "matched")
    for f in fields:
        a = sum(_get(old[k], f) for k in keys)
        b = sum(_get(new[k], f) for k in keys)
        moved = sum(1 for k in keys if _get(old[k], f) != _get(new[k], f))
        pct = f"{(b - a) / a:+.2%}" if a else "n/a"
        print(f"{f:14} {a:14,.1f} {b:14,.1f}  {pct:>8}  {moved:,} moved")
    return 0


if __name__ == "__main__":
    sys.exit(main())
