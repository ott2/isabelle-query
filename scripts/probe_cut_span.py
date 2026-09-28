#!/usr/bin/env python3
"""Does `Entry.cut_span` ever reach the next entry? [cut-span]

`cut_span` is the span a downstream tool writes through (delete / move), so an
overlap is destructive: deleting one lemma takes its successor's preamble or
declaration with it.  Counts, over every session root in a corpus:

  * raw `body_end_line > thy_end` — what the cap in `cut_span` absorbs;
  * raw `body_end_line < thy_line` — a body that ends before it starts;
  * `cut_span` None — the entry shares a line with a neighbour;
  * a non-None `cut_span` meeting a neighbour's lines — must be 0.

Usage:  python3 scripts/probe_cut_span.py <corpus-dir>   (e.g. ~/repos/afp/thys)
"""
from __future__ import annotations

import sys
from pathlib import Path

from isabelle_query.api import parse_root


def main() -> int:
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    corpus = Path(sys.argv[1]).expanduser()
    total = past_end = before_start = overlap = same_line = 0
    shown = 0
    for root in sorted(p for p in corpus.iterdir() if (p / "ROOT").exists()):
        try:
            sections = parse_root(root)
        except ValueError:
            continue
        for sec in sections:
            es = sorted((e for e in sec.entries if e.thy_line),
                        key=lambda e: e.thy_line)
            for i, e in enumerate(es):
                total += 1
                if e.body_end_line > e.thy_end:
                    past_end += 1
                    if shown < 10:
                        shown += 1
                        print(f"  past thy_end: {sec.path}:{e.thy_line} "
                              f"{e.name} body_end={e.body_end_line} "
                              f"thy_end={e.thy_end}")
                if e.body_end_line and e.body_end_line < e.thy_line:
                    before_start += 1
                if e.cut_span is None:
                    # Shares a line with a neighbour (`consts F G`): no line
                    # span separates them, so there is no span to promise.
                    same_line += 1
                if i + 1 == len(es):
                    continue
                # A promised span on either side must not meet the other's
                # lines.  Neighbours suffice: spans are sorted and capped.
                nxt = es[i + 1]
                if ((e.cut_span or nxt.cut_span)
                        and e._line_cut()[1] >= nxt.src_start):
                    overlap += 1
                    print(f"  OVERLAP: {sec.path}:{e.thy_line} {e.name} "
                          f"cut={e.cut_span} next={nxt.name}"
                          f"@{nxt.src_start} cut={nxt.cut_span}")
    print(f"{total} entries")
    print(f"body_end_line > thy_end:  {past_end}")
    print(f"body_end_line < thy_line: {before_start}")
    print(f"cut_span None (shares a line): {same_line}")
    print(f"cut_span overlaps next:   {overlap}")
    return 1 if overlap else 0


if __name__ == "__main__":
    raise SystemExit(main())
