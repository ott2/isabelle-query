#!/usr/bin/env python3
r"""What the `unfound` bare goal steps look like, by line shape [bare-wrapped].

`bare_kinds.unfound` is the residue of issue #9: goal steps whose proposition
the scanner did not find.  #26 reports most of it is `obtain x where` with the
statement on the next line.  This groups every `unfound` step by its goal
command, by whether the next live line OPENS with a delimiter (the wrapped
form `_statement_wrapped` reads), and by a normalised tail of the command
line -- identifiers become `x`, so `obtain k where`, `obtain a b where` and
`obtain k :: nat where` sort into a handful of shapes.  Examples per shape.

    python scripts/probe_unfound_residue.py [ROOT] [--limit=N] [--top=N]

Session-at-a-time, like `shape census`.  `--limit=N` is an ALPHABETICAL
PREFIX of the sessions, never a sample.
"""

from __future__ import annotations

import re
import sys
from collections import Counter
from pathlib import Path

_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_ROOT / "src"))

from isabelle_layout import iter_sessions  # noqa: E402
from isabelle_query import shape  # noqa: E402
from isabelle_query.parsing import sections_for_session  # noqa: E402

_WORD_RE = re.compile(r"[A-Za-z][\w'.]*")
_KEEP = {"obtain", "where", "have", "show", "hence", "thus", "consider",
         "interpret", "from", "with", "then", "and", "for", "if", "is",
         "using", "by", "proof", "fixes", "assumes", "shows", "note"}


def _shape(line: str) -> str:
    """The command line with identifiers outside `_KEEP` written `x`."""
    return _WORD_RE.sub(lambda m: m.group(0) if m.group(0) in _KEEP else "x",
                        line.strip())


def main() -> int:
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = Path(argv[0]).expanduser() if argv else (
        Path.home() / "repos" / "afp" / "thys")
    opt = {a.split("=")[0]: a.split("=")[1] for a in sys.argv[1:]
           if a.startswith("--") and "=" in a}
    limit = int(opt.get("--limit", 0)) or None
    top = int(opt.get("--top", 25))

    sessions = iter_sessions(root)
    if limit:
        sessions = sessions[:limit]
    by_cmd: Counter[tuple[str, bool]] = Counter()
    shapes: Counter[tuple[str, bool]] = Counter()
    examples: dict[tuple[str, bool], str] = {}
    n_unfound = 0
    seen: set = set()
    for session in sessions:
        try:
            secs = sections_for_session(session, seen)
        except Exception as exc:  # noqa: BLE001
            print(f"skip {session.name}: {exc}", file=sys.stderr)
            continue
        for sec in secs:
            src = sec.source()
            for e in sec.entries:
                for st in shape._scan_steps(sec, e):
                    if st.bare != "unfound":
                        continue
                    n_unfound += 1
                    nxt = next((ln.strip() for ln in src[st.line:]
                                if ln.strip()), "")
                    opens = bool(shape._PROP_START_RE.match(nxt))
                    cmd = st.goal_cmd or st.kw
                    by_cmd[cmd, opens] += 1
                    key = (_shape(src[st.line - 1]), opens)
                    shapes[key] += 1
                    examples.setdefault(
                        key, f"{sec.theory}:{st.line}  "
                             f"{src[st.line - 1].strip()[:70]}")
    print(f"{n_unfound:,} unfound goal steps\n")
    print("by goal command, and whether the next line opens a proposition:")
    for (cmd, opens), n in by_cmd.most_common():
        print(f"  {n:7,}  {cmd:<10} {'next-line' if opens else '-'}")
    print(f"\ntop {top} line shapes:")
    for (shp, opens), n in shapes.most_common(top):
        print(f"  {n:7,}  {'NL' if opens else '  '}  {shp[:60]}")
        print(f"           e.g. {examples[shp, opens]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
