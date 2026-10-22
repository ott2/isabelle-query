#!/usr/bin/env python3
r"""Why rows left `unused --locals` between two runs of probe_locals_rows.py
[fact-method]: a bare `fact` method in the proof, a cartouche (a literal fact)
in it, or neither — the binding-time change, a method citing the OLD label.

    python scripts/probe_locals_why.py OLD.tsv NEW.tsv [ROOT] [--show=N]

A row is put in the first class its proof's text admits, so this is a
heuristic split for hand-checking, not the scan's own reason.
"""

from __future__ import annotations

import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

from isabelle_query.parsing import _parse_one

_BARE_FACT = re.compile(r"\bfact\b\s*(?:$|[)|;,+?\]])", re.M)
_CARTOUCHE = re.compile(r"\\<open>|‹")


def rows(path: str) -> set[tuple[str, ...]]:
    with open(path, encoding="utf-8") as fh:
        return {tuple(ln.rstrip("\n").split("\t")) for ln in fh if ln.strip()}


def main() -> int:
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    opt = dict(a.split("=", 1) for a in sys.argv[1:] if a.startswith("--"))
    show = int(opt.get("--show", 3))
    old, new = rows(argv[0]), rows(argv[1])
    root = Path(argv[2]).expanduser() if len(argv) > 2 else (
        Path.home() / "repos" / "afp" / "thys")
    by_file: dict[str, list[tuple[str, ...]]] = defaultdict(list)
    for r in old - new:
        by_file[r[0]].append(r)
    why: Counter[str] = Counter()
    examples: dict[str, list[str]] = defaultdict(list)
    for rel, rs in sorted(by_file.items()):
        sec = _parse_one(Path(rel).stem, root / rel)
        live = sec.live_source()
        for r in rs:
            line = int(r[1])
            e = next((e for e in sec.entries
                      if e.src_start <= line <= e.thy_end), None)
            text = "\n".join(live[e.src_start - 1:e.thy_end]) if e else ""
            k = ("fact method" if _BARE_FACT.search(text) else
                 "literal fact" if _CARTOUCHE.search(text) else
                 "binding time")
            why[k] += 1
            if len(examples[k]) < show:
                examples[k].append(f"{rel}:{line} {r[2]}")
    print(f"{len(old - new):,} rows gone, {len(new - old):,} new")
    for k, n in why.most_common():
        print(f"  {n:6,}  {k}")
        for ex in examples[k]:
            print(f"            {ex}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
