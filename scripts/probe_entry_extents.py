#!/usr/bin/env python3
r"""Every entry's and proof owner's extent over a corpus, as TSV, for diffing
two versions of the parser [early-end].

    python scripts/probe_entry_extents.py [ROOT] [--limit=N] [--cut] > spans.tsv

One line each: theory path, tag, name, thy_line, thy_end, body_end_line,
and with `--cut` also `cut_span` (entries only; `-` for a proof owner).  Run
a copy under `.stage/old/scripts/` with `PYTHONPATH=.stage/old/src` for the
HEAD baseline, then `diff` the two files.  Also prints, on stderr, how many
proofs end outside their entry (`scripts/probe_early_end.py` explains them).
`--limit=N` takes an ALPHABETICAL PREFIX of the sessions, not a sample.
"""

from __future__ import annotations

import sys
from pathlib import Path

from isabelle_layout import iter_sessions
from isabelle_query.parsing import sections_for_session


def main() -> int:
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = Path(argv[0]).expanduser() if argv else (
        Path.home() / "repos" / "afp" / "thys")
    opt = dict(a.split("=", 1) for a in sys.argv[1:]
               if a.startswith("--") and "=" in a)
    limit = int(opt.get("--limit", 0)) or None
    sessions = iter_sessions(root)
    if limit:
        sessions = sessions[:limit]
    seen: set = set()
    n = 0
    for session in sessions:
        try:
            secs = sections_for_session(session, seen)
        except Exception as exc:  # noqa: BLE001
            print(f"skip {session.name}: {exc}", file=sys.stderr)
            continue
        for sec in secs:
            rel = sec.path.relative_to(root) if sec.path.is_relative_to(
                root) else sec.path
            for e in list(sec.entries) + list(sec.proof_owners):
                n += 1
                cut = (f"\t{getattr(e, 'cut_span', '-')}"
                       if "--cut" in sys.argv else "")
                print(f"{rel}\t{e.tag}\t{e.name}\t{e.thy_line}\t"
                      f"{e.thy_end}\t{e.body_end_line}{cut}")
    print(f"{n:,} entries and owners", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
