#!/usr/bin/env python3
r"""Compare two `query shape census` JSONL outputs field by field.

For each numeric field named (default: the M5 family), prints the summed
value in each file, the change, and how many entries moved, up and down.
Entries are matched by (theory, lemma, line), so both files must come from
the same corpus.  A field `a*b` is the product of two, so
`fanin_mean*n_goals` is the premises counted.  `--show=N` prints a seeded
random sample of N moved entries per field (`--seed=S`), as
`theory:line lemma old -> new`, for reading with `query shape lemma`.

    python scripts/diff_census_fields.py OLD.jsonl NEW.jsonl [FIELD ...]
        [--show=N] [--seed=S]
"""

from __future__ import annotations

import json
import random
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
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    opt = dict(a.split("=", 1) for a in sys.argv[1:]
               if a.startswith("--") and "=" in a)
    if len(argv) < 2:
        print(__doc__, file=sys.stderr)
        return 2
    show = int(opt.get("--show", 0))
    rng = random.Random(int(opt.get("--seed", 0)))
    old, new = _load(argv[0]), _load(argv[1])
    fields = argv[2:] or _DEFAULT
    keys = sorted(old.keys() & new.keys(), key=str)
    print(f"entries: {len(old):,} old, {len(new):,} new, {len(keys):,} "
          "matched")
    samples = {}
    for f in fields:
        a = sum(_get(old[k], f) for k in keys)
        b = sum(_get(new[k], f) for k in keys)
        moved = [k for k in keys if _get(old[k], f) != _get(new[k], f)]
        up = sum(1 for k in moved if _get(new[k], f) > _get(old[k], f))
        pct = f"{(b - a) / a:+.2%}" if a else "n/a"
        print(f"{f:14} {a:14,.1f} {b:14,.1f}  {pct:>8}  {len(moved):,} "
              f"moved ({up:,} up, {len(moved) - up:,} down)")
        if show:
            samples[f] = rng.sample(moved, min(show, len(moved)))
    for f, ks in samples.items():
        print(f"\n{f}:")
        for k in ks:
            theory, lemma, line = k
            print(f"  {theory}:{line} {lemma}  "
                  f"{_get(old[k], f):g} -> {_get(new[k], f):g}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
