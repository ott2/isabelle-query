#!/usr/bin/env python3
r"""Which symbolic identifiers a corpus uses as fact labels (#35).

Isar's `name` includes a symbolic identifier, a run of
`!#$%&*+-/<=>?@^_|~` (`Lexicon.scan_symid`), so `have *: "P"` labels a
fact `*`.  Some such runs are also outer keywords, and a keyword wins a
tie, so `+` and `?` are method combinators and never a fact.  This counts:

  * every symbolic spelling declared as a keyword in a theory header
    (Pure, HOL and the corpus), the spellings a fact can never take;
  * every symbolic label, by spelling, in the outer view, after a command
    or element that takes one (`have`, `assume`, `assumes`, `and`, `note`,
    `obtain ... where`, ...).

    python scripts/probe_symbolic_labels.py [ROOT] [--limit=N]

`--limit=N` takes an ALPHABETICAL PREFIX of the sessions, not a sample.
"""

from __future__ import annotations

import re
import sys
from collections import Counter
from pathlib import Path

from isabelle_layout import iter_sessions
from isabelle_query.parsing import sections_for_session

_SYM = r"[!#$%&*+\-/<=>?@^_|~]"
_SYMBOLIC = re.compile(rf"{_SYM}+\Z")
_HEADER_KW = re.compile(r"\bkeywords\b(.*?)\bbegin\b", re.S)
_QUOTED = re.compile(r'"([^"]*)"')
_LABEL = re.compile(
    r"(?<![\w'])(have|show|hence|thus|obtain|where|assume|presume|assumes"
    r"|and|note|case|consider|obtains|shows|defines|define|interpret)\s+"
    rf"({_SYM}+)\s*(?:\[[^\]]*\]\s*)?(:(?!:)|=)")
_ISABELLE_SRC = Path("/Applications/Isabelle2025-2.app/src")


def _header_keywords(text: str) -> set[str]:
    m = _HEADER_KW.search(text[:20000])
    if not m:
        return set()
    return {q for q in _QUOTED.findall(m.group(1)) if _SYMBOLIC.match(q)}


def main() -> int:
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = Path(argv[0]).expanduser() if argv else (
        Path.home() / "repos" / "afp" / "thys")
    opt = dict(a.split("=", 1) for a in sys.argv[1:]
               if a.startswith("--") and "=" in a)
    limit = int(opt.get("--limit", 0)) or None

    keywords: Counter[str] = Counter()
    for base in (_ISABELLE_SRC / "Pure", _ISABELLE_SRC / "HOL", root):
        for p in base.rglob("*.thy"):
            try:
                text = p.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            for k in _header_keywords(text):
                keywords[k] += 1
    print("symbolic keywords declared in headers:")
    for k, n in sorted(keywords.items()):
        print(f"  {k!r:10} {n:6,} theories")

    sessions = iter_sessions(root)
    if limit:
        sessions = sessions[:limit]
    labels: Counter[str] = Counter()
    by_cmd: Counter[str] = Counter()
    seen: set = set()
    n_thy = 0
    for session in sessions:
        try:
            secs = sections_for_session(session, seen)
        except Exception as exc:  # noqa: BLE001
            print(f"skip {session.name}: {exc}", file=sys.stderr)
            continue
        for sec in secs:
            n_thy += 1
            for line in sec.outer_source():
                for m in _LABEL.finditer(line):
                    labels[m.group(2)] += 1
                    by_cmd[m.group(1)] += 1
    print(f"\nsymbolic labels over {n_thy:,} theories, by spelling:")
    for k, n in labels.most_common():
        flag = "  KEYWORD" if k in keywords else ""
        print(f"  {k!r:10} {n:8,}{flag}")
    print("\nby the word before the label:")
    for k, n in by_cmd.most_common():
        print(f"  {k:10} {n:8,}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
