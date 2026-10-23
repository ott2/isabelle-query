#!/usr/bin/env python3
r"""Two cut-span questions over a corpus (#28, #29).

**#29: declarations that do not start a line.**  Isabelle reads a command
wherever a token starts, so `by simp lemma b: True` declares `b`.  The entry
scan only tests a line's leading token.  This lists every declaring keyword
(`DECL_RE`: built-in, so reserved in every theory) that starts a token
later in a line of the outer view (terms and comments blanked).  It reports
the token before the keyword, and whether an entry already starts on that
line.

**#28: preambles under a heading.**  A `text` block attached as an entry's
preamble, with nothing between the nearest heading above and the block
except blank lines.  Such a block may introduce the section rather than
document the entry.

    python scripts/probe_midline_decls.py [ROOT] [--limit=N] [--show=N]
        [--boundaries]

`--boundaries` adds the span-bounding commands (`declare`, `end`, ...).

`--limit=N` takes an ALPHABETICAL PREFIX of the sessions, not a sample.
"""

from __future__ import annotations

import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

from isabelle_layout import iter_sessions
from isabelle_query import parsing
from isabelle_query.parsing import TAG_MAP, sections_for_session

_PREV_RE = re.compile(r"(\S+)\s*$")


def main() -> int:
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = Path(argv[0]).expanduser() if argv else (
        Path.home() / "repos" / "afp" / "thys")
    opt = dict(a.split("=", 1) for a in sys.argv[1:]
               if a.startswith("--") and "=" in a)
    limit = int(opt.get("--limit", 0)) or None
    show = int(opt.get("--show", 6))
    sessions = iter_sessions(root)
    if limit:
        sessions = sessions[:limit]
    seen: set = set()
    words = set(TAG_MAP)
    if "--boundaries" in sys.argv:          # span-bounding commands too
        words |= parsing._SPAN_BOUNDARY_COMMANDS
    words = sorted(words, key=len, reverse=True)
    kw_re = re.compile(
        r"(?<![\w'.\\>^?])(" + "|".join(map(re.escape, words)) + r")"
        rf"(?!{parsing._NAME_GOES_ON})")
    mid: Counter[str] = Counter()
    examples: dict[str, list[str]] = defaultdict(list)
    preambles = under_heading = 0
    pre_examples: list[str] = []
    for session in sessions:
        try:
            secs = sections_for_session(session, seen)
        except Exception as exc:  # noqa: BLE001
            print(f"skip {session.name}: {exc}", file=sys.stderr)
            continue
        for sec in secs:
            lines, outer = sec.source(), sec.outer_source()
            starts = {e.thy_line for e in sec.entries if e.thy_line}
            for n, o in enumerate(outer, 1):
                lead = len(o) - len(o.lstrip())
                for m in kw_re.finditer(o):
                    if m.start() <= lead:
                        continue
                    before = o[:m.start()]
                    if parsing._MODIFIER_RE.fullmatch(before.lstrip()):
                        continue             # `private lemma`
                    pm = _PREV_RE.search(before)
                    prev = pm.group(1) if pm else ""
                    key = (f"{m.group(1)} after `{prev[-12:]}`"
                           f"{' (entry on line)' if n in starts else ''}")
                    mid[key] += 1
                    if len(examples[key]) < show:
                        examples[key].append(
                            f"{sec.path.relative_to(root)}:{n}: "
                            f"{lines[n - 1].strip()[:110]}")
            heads = {}
            for hs, he in sec.heading_spans:
                heads[he] = hs
            for e in sec.entries:
                if not e.preamble:
                    continue
                preambles += 1
                k = e.preamble[0] - 1
                while k >= 1 and not lines[k - 1].strip():
                    k -= 1
                if k in heads:
                    under_heading += 1
                    if len(pre_examples) < show:
                        pre_examples.append(
                            f"{sec.path.relative_to(root)}:{e.preamble[0]} "
                            f"{e.name} (heading {heads[k]})")
    print("#29 mid-line declaring keywords:")
    for key, c in mid.most_common():
        print(f"  {c:6,}  {key}")
        for ex in examples[key]:
            print(f"            {ex}")
    print(f"#28 preambles: {preambles:,}; directly under a heading: "
          f"{under_heading:,}")
    for ex in pre_examples:
        print(f"    {ex}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
