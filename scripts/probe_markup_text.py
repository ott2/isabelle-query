#!/usr/bin/env python3
r"""Probe: is the text `PIDE/markup` encodes the theory SOURCE?

`probe_step_alignment.py` compares line numbers between Isabelle's markup and
`query`'s parse, which is only meaningful if both index the same document.  The
markup body decodes to 21,365 symbols where `DitherTM.thy` is 8,171 chars, so
they are not the same string and the question is what the surplus is.

Prints the first divergence and what surrounds it.

Usage:  probe_markup_text.py SESSION THEORY
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from probe_export_oracle import (  # noqa: E402
    _ENTITY_RE, _attrs, _find_db, _read_export, _resolve_source)
from probe_pide_markup import parse_yxml  # noqa: E402


def main() -> None:
    session, theory = sys.argv[1], sys.argv[2]
    db = _find_db(session)
    if db is None:
        sys.exit(f"no database for {session}")
    if "." not in theory:
        theory = f"{session}.{theory}"
    spans, text = parse_yxml(_read_export(db, theory, "PIDE/markup"))

    src_attr = ""
    for kind in ("theory/thms", "theory/consts", "theory/types"):
        body = _read_export(db, theory, kind)
        if not body:
            continue
        for m in _ENTITY_RE.finditer(body):
            src_attr = _attrs(m.group(1)).get("file", "")
            if src_attr:
                break
        if src_attr:
            break
    path = _resolve_source(src_attr, {})
    disk = path.read_text(encoding="utf-8", errors="replace")
    print(f"markup text {len(text):>8,} chars, {text.count(chr(10)):>5,} lines")
    print(f"file        {len(disk):>8,} chars, {disk.count(chr(10)):>5,} lines")

    n = min(len(text), len(disk))
    i = 0
    while i < n and text[i] == disk[i]:
        i += 1
    line = text[:i].count("\n") + 1
    print(f"\nfirst divergence at char {i:,} (line {line})")
    print(f"  file  : {disk[max(0, i - 60):i + 90]!r}")
    print(f"  markup: {text[max(0, i - 60):i + 90]!r}")

    # Which markup element BRACKETS that offset, innermost first?  That names
    # the surplus rather than leaving it to be guessed at.
    covering = [(n_, a, s, e) for n_, a, s, e in spans if s <= i + 1 < e]
    covering.sort(key=lambda t: t[3] - t[2])
    print("\n  elements covering it, innermost first:")
    for n_, a, s, e in covering[:8]:
        print(f"    {n_:<18} {e - s:>7,} wide  {dict(list(a.items())[:3])}")


if __name__ == "__main__":
    main()
