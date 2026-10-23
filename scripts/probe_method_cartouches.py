#!/usr/bin/env python3
r"""Cartouches by the outer token in front of them (#30).

A cartouche in a method can be a literal fact (`rule ‹P›`) or method text:
`use x in ‹simp add: y›`, or an Eisbach `match ... ⇒ ‹rule H›`.  Names in
method text are citations, and `unused facts` read them as term names
only.  This sorts every cartouche on a line by the last outer token before
it, so the shapes and their counts are visible.

    python scripts/probe_method_cartouches.py [ROOT] [--limit=N] [--show=N]

`--limit=N` takes an ALPHABETICAL PREFIX of the sessions, not a sample.
"""

from __future__ import annotations

import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

from isabelle_layout import iter_sessions
from isabelle_query.parsing import sections_for_session

_OPEN = ("\\<open>", "‹")
_LAST_RE = re.compile(r"(\\<\^?\w+>|=>|[^\s()]+)\s*$")
_USE_RE = re.compile(r"(?<![\w'])use(?![\w'])")


def main() -> int:
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = Path(argv[0]).expanduser() if argv else (
        Path.home() / "repos" / "afp" / "thys")
    opt = dict(a.split("=", 1) for a in sys.argv[1:]
               if a.startswith("--") and "=" in a)
    limit = int(opt.get("--limit", 0)) or None
    show = int(opt.get("--show", 3))
    sessions = iter_sessions(root)
    if limit:
        sessions = sessions[:limit]
    seen: set = set()
    kinds: Counter[str] = Counter()
    examples: dict[str, list[str]] = defaultdict(list)
    for session in sessions:
        try:
            secs = sections_for_session(session, seen)
        except Exception as exc:  # noqa: BLE001
            print(f"skip {session.name}: {exc}", file=sys.stderr)
            continue
        for sec in secs:
            live, outer = sec.live_source(), sec.outer_source()
            for ln, spans in sec.inner_spans.items():
                text = live[ln - 1]
                for lo, _hi in spans:
                    if not text.startswith(_OPEN, lo):
                        continue
                    before = outer[ln - 1][:lo]
                    m = _LAST_RE.search(before)
                    if not m:
                        continue          # opens its line: not after a token
                    last = m.group(1)
                    if last == "in":
                        key = ("in, after `use`" if _USE_RE.search(before)
                               else "in, no `use` on the line")
                    elif last in ("\\<Rightarrow>", "=>", "⇒"):
                        key = "⇒ (Eisbach match)"
                    else:
                        continue
                    kinds[key] += 1
                    if len(examples[key]) < show:
                        examples[key].append(
                            f"{sec.path.relative_to(root)}:{ln}: "
                            f"{text.strip()[:100]}")
    for key, c in kinds.most_common():
        print(f"{c:7,}  {key}")
        for ex in examples[key]:
            print(f"           {ex}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
