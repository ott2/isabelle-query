#!/usr/bin/env python3
"""Print each entry's span fields for one theory, or for stdin.

    python scripts/show_cut_spans.py FILE.thy
    printf '...' | python scripts/show_cut_spans.py -
"""

import sys
from pathlib import Path

from isabelle_query.api import parse_theory


def main() -> int:
    arg = sys.argv[1]
    lines = sys.stdin.read().splitlines() if arg == "-" else None
    path = Path("<stdin>") if arg == "-" else Path(arg)
    sec = parse_theory(path.stem, path, lines)
    for e in sec.entries:
        print(f"{e.thy_line:5} {e.tag:9} {e.name:28} decl_end={e.decl_end_line}"
              f" proof={e.proof_line} body_end={e.body_end_line}"
              f" thy_end={e.thy_end} pre={e.preamble}"
              f" shares={e.shares_line} cut={e.cut_span}"
              f" heading={getattr(e, 'preamble_follows_heading', '-')}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
