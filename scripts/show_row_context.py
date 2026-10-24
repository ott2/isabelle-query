#!/usr/bin/env python3
r"""Show where a reported binding's name occurs after it, for checking
`unused --locals` rows by hand.

    python scripts/show_row_context.py ROWS.tsv [--root=DIR] [--sample=N]
        [--seed=S] [--after=LINES]

ROWS.tsv is `probe_locals_rows.py` output.  For each row (or a seeded
random sample), prints the binding's line and every later line, up to
`--after`, where the name occurs as a whole token, quoted or not.
"""

from __future__ import annotations

import random
import re
import sys
from pathlib import Path


def main() -> int:
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    opt = dict(a.split("=", 1) for a in sys.argv[1:]
               if a.startswith("--") and "=" in a)
    root = Path(opt.get("--root", Path.home() / "repos" / "afp" / "thys"))
    rows = [ln.rstrip("\n").split("\t") for ln in open(argv[0])]
    if "--sample" in opt:
        random.seed(int(opt.get("--seed", 0)))
        rows = random.sample(rows, min(int(opt["--sample"]), len(rows)))
    after = int(opt.get("--after", 40))
    for path, line, name, kind, entry, *_ in rows:
        src = (root / path).read_text(encoding="utf-8").splitlines()
        n = int(line)
        print(f"== {path}:{line}  {name}  {kind}  {entry}")
        print(f"   {n}: {src[n - 1].strip()[:140]}")
        tok = re.compile(rf"(?<![\w'.]){re.escape(name)}(?![\w'])")
        for k in range(n, min(n + after, len(src))):
            if tok.search(src[k]):
                print(f"   {k + 1}: {src[k].strip()[:140]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
