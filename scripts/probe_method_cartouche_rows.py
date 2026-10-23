#!/usr/bin/env python3
r"""Check rows that left `unused facts` against method cartouches (#30).

For each row in OLD.tsv but not NEW.tsv (both from
`probe_locals_rows.py`), whether the name is written inside a cartouche
after `in` or `⇒` in its own entry [method-cartouche].  Prints the rows
where it is not, which are the ones to read by hand.

    python scripts/probe_method_cartouche_rows.py OLD.tsv NEW.tsv [ROOT]
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from isabelle_query.parsing import _parse_one

_CART_RE = re.compile(
    r"(?:(?<![\w'])in|\\<Rightarrow>|⇒)\s*(?:\\<open>|‹)(.*?)(?:\\<close>|›)",
    re.S)


def main() -> int:
    old, new = (set(Path(p).read_text().splitlines()) for p in sys.argv[1:3])
    root = Path(sys.argv[3]).expanduser() if len(sys.argv) > 3 else (
        Path.home() / "repos" / "afp" / "thys")
    gone = sorted(old - new)
    found = 0
    for row in gone:
        path, line, name, _kind, entry = row.split("\t")[:5]
        p = root / path
        sec = _parse_one(p.stem, p)
        e = next((x for x in sec.entries
                  if x.thy_line <= int(line) <= x.thy_end), None)
        body = "\n".join(sec.source()[e.thy_line - 1:e.thy_end]) if e else ""
        word = re.compile(rf"(?<![\w'.]){re.escape(name)}(?![\w'])")
        if any(word.search(m.group(1)) for m in _CART_RE.finditer(body)):
            found += 1
        else:
            print(f"not in a method cartouche: {row}")
    print(f"{found} of {len(gone)} rows gone are cited in a method cartouche")
    return 0


if __name__ == "__main__":
    sys.exit(main())
