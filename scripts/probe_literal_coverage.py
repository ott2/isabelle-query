#!/usr/bin/env python3
r"""Step lines whose method coverage changed when literals became tokens (#31).

Reads every step's command text twice in one process: with the literal
scanner, and with the tokenization it replaced (strings and cartouches
blanked, backquotes not seen), and prints the lines where `covered`
differs.

    python scripts/probe_literal_coverage.py [ROOT] [--limit=N] [--show=N]

`--limit=N` takes an ALPHABETICAL PREFIX of the sessions, not a sample.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from isabelle_layout import iter_sessions
from isabelle_query import graph, shape
from isabelle_query.parsing import sections_for_session

_DQUOTE = re.compile(r'"[^"]*"')
_CARTOUCHE = re.compile(r"\\<open>.*?\\<close>")


def _old_tokens(line: str) -> list[str]:
    return graph._FACT_TOK_RE.findall(_CARTOUCHE.sub(" ", _DQUOTE.sub(" ",
                                                                     line)))


def main() -> int:
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = Path(argv[0]).expanduser() if argv else (
        Path.home() / "repos" / "afp" / "thys")
    opt = dict(a.split("=", 1) for a in sys.argv[1:]
               if a.startswith("--") and "=" in a)
    limit = int(opt.get("--limit", 0)) or None
    show = int(opt.get("--show", 40))
    sessions = iter_sessions(root)
    if limit:
        sessions = sessions[:limit]
    new_tokens = graph._fact_tokens
    seen: set = set()
    lost = gained = 0
    for session in sessions:
        try:
            secs = sections_for_session(session, seen)
        except Exception as exc:  # noqa: BLE001
            print(f"skip {session.name}: {exc}", file=sys.stderr)
            continue
        for sec in secs:
            for e in sec.entries:
                if not e.proof_line:
                    continue
                for s in shape._scan_steps(sec, e):
                    if s.kind == "other" or not s.src:
                        continue
                    _, new = graph._cited_facts_on_line(s.src)
                    graph._fact_tokens = _old_tokens
                    try:
                        _, old = graph._cited_facts_on_line(s.src)
                    finally:
                        graph._fact_tokens = new_tokens
                    if old == new:
                        continue
                    if old:
                        lost += 1
                    else:
                        gained += 1
                    if lost + gained <= show:
                        tag = "lost" if old else "gained"
                        print(f"{tag}  {sec.theory}:{s.line}  "
                              f"{s.src.strip()[:150]}")
    print(f"coverage lost on {lost:,} step lines, gained on {gained:,}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
