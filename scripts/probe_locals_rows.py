#!/usr/bin/env python3
r"""Every `unused --locals` row over a corpus, as TSV, for diffing two versions
of the scan [fact-method].

    python scripts/probe_locals_rows.py [ROOT] [--limit=N] [--spans] > rows.tsv

One line per unread binding: theory path, line, name, kind, entry, and with
`--spans` the `unused --locals --spans` cell [local-spans].  Run a
copy under `.stage/old/scripts/` with `PYTHONPATH=.stage/old/src` for the
HEAD baseline, then `diff` the two files (`probe_locals_why.py` sorts what
changed).
`--limit=N` takes an ALPHABETICAL PREFIX of the sessions, not a sample.
"""

from __future__ import annotations

import sys
from pathlib import Path

from isabelle_layout import iter_sessions
from isabelle_query import proof_locals
from isabelle_query.parsing import sections_for_session


def main() -> int:
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = Path(argv[0]).expanduser() if argv else (
        Path.home() / "repos" / "afp" / "thys")
    opt = {a.split("=")[0]: (a.split("=") + [""])[1] for a in sys.argv[1:]
           if a.startswith("--")}
    limit = int(opt.get("--limit") or 0) or None
    spans = "--spans" in opt
    sessions = iter_sessions(root)
    if limit:
        sessions = sessions[:limit]
    seen: set = set()
    n_bound = n_unread = 0
    for session in sessions:
        try:
            secs = sections_for_session(session, seen)
        except Exception as exc:  # noqa: BLE001
            print(f"skip {session.name}: {exc}", file=sys.stderr)
            continue
        for sec in secs:
            rel = sec.path.relative_to(root) if sec.path.is_relative_to(
                root) else sec.path
            for e in sec.entries:
                for b in proof_locals.scan_proof(sec, e):
                    n_bound += 1
                    if b.read or b.kept:
                        continue
                    n_unread += 1
                    row = [str(rel), str(b.line), b.name, b.kind, b.entry]
                    if spans:
                        row.append(proof_locals.span_text(sec.theory, b))
                    print("\t".join(row))
    print(f"{n_unread:,} unread of {n_bound:,} bindings", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
