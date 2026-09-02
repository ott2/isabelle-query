#!/usr/bin/env python3
r"""Probe: does `PIDE/markup` oracle the things `theory/thms` cannot?

The #8 oracle compares NAME SETS from `theory/thms` & friends.  Its own
preconditions said the data "must carry source POSITIONS, not just names -- a
name list alone cannot check spans, and spans are where the parser actually
errs".  The entity export only half-delivers that: `offset..end_offset`
brackets the entity's NAME, not its declaration, so declaration extents,
command segmentation and comment regions stay unchecked.

The same session database carries `PIDE/markup`: the whole theory text with
Isabelle's markup interleaved as YXML.  That contains

  * `command_span` -- every command, its keyword `name` and `kind`, and (by
    walking the text) its exact symbol extent;
  * `comment` / `cartouche` / inner-syntax markup -- the regions `query`'s
    `live_source()` / `outer_source()` redaction has to reproduce.

Those are precisely the primitives `parsing.scan_regions` computes by hand, so
this is an oracle for the parser's actual job rather than for its output names.

This decodes the markup and reports what is available and how it lines up with
`query`'s command view.

Usage:  probe_pide_markup.py [SESSION] [THEORY]
"""
from __future__ import annotations

import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from probe_export_oracle import X, Y, _find_db, _read_export, _theories  # noqa: E402


def parse_yxml(text: str):
    """Walk the YXML, yielding `(markup_name, attrs, start, end)` in SYMBOL
    coordinates, plus the plain text it encodes.

    YXML is a flat encoding of an XML tree: `X Y name Y k=v ... X` opens an
    element, `X Y X` closes one, and everything else is body text.  Symbol
    offsets are 1-based, matching every other position Isabelle exports.

    NOTE the text this returns is **not** the theory source — see
    :func:`source_line_map`.
    """
    spans: list[tuple[str, dict[str, str], int, int]] = []
    stack: list[tuple[str, dict[str, str], int]] = []
    out: list[str] = []
    off = 1
    for chunk in text.split(X):
        if not chunk:
            continue
        if chunk.startswith(Y):
            fields = chunk[1:].split(Y)
            if fields[0] == "":                       # close
                if stack:
                    name, attrs, start = stack.pop()
                    spans.append((name, attrs, start, off))
            else:                                     # open
                attrs = {}
                for f in fields[1:]:
                    k, sep, v = f.partition("=")
                    if sep:
                        attrs[k] = v
                stack.append((fields[0], attrs, off))
        else:
            out.append(chunk)
            off += len(chunk)          # markup body is already symbol-wise
    return spans, "".join(out)


def source_line_map(spans, text: str) -> tuple[list[int], str]:
    r"""`(line_of, source)` — resolve a markup offset to a **source** line.

    The text `PIDE/markup` encodes is the theory source with Isabelle's
    *elaborated* antiquotation output spliced into it: `@{term "f"}` in a `text`
    block is wrapped in an `xml_elem` whose `xml_body` child carries the
    rendered typing (`\<^bold>'a` and friends).  That text is in the markup and
    is NOT in the `.thy`, so counting newlines over the whole body gives line
    numbers for a document that does not exist on disk.

    Measured on `Universal_Turing_Machine.DitherTM`: the markup decodes to
    21,365 chars where the file is 8,171, and **deleting every `xml_body` region
    reproduces the file exactly** — byte-for-byte, not approximately.  So the
    rule is not a heuristic: source = markup minus `xml_body`.

    `line_of[i]` is therefore the source line of markup offset `i`, advanced
    only by newlines OUTSIDE an `xml_body`.  A `command_span` never begins
    inside one (a command is source, not rendering), so its start offset maps
    exactly.
    """
    inserted = bytearray(len(text) + 2)
    for name, _attrs, start, end in spans:
        if name == "xml_body":
            for k in range(start, min(end, len(text) + 1)):
                inserted[k] = 1
    line_of = [1, 1]
    src: list[str] = []
    ln = 1
    for i, ch in enumerate(text, start=1):
        if not inserted[i]:
            src.append(ch)
            ln += ch == "\n"
        line_of.append(ln)
    return line_of, "".join(src)


def main() -> None:
    session = sys.argv[1] if len(sys.argv) > 1 else "Universal_Turing_Machine"
    db = _find_db(session)
    if db is None:
        sys.exit(f"no export database for {session!r}")
    thys = _theories(db, session)
    theory = sys.argv[2] if len(sys.argv) > 2 else thys[0]
    if "." not in theory:
        theory = f"{session}.{theory}"
    body = _read_export(db, theory, "PIDE/markup")
    if not body:
        sys.exit(f"no PIDE/markup export for {theory}")
    print(f"{theory}: PIDE/markup is {len(body):,} chars")

    spans, text = parse_yxml(body)
    print(f"decoded {len(spans):,} markup spans over {len(text):,} symbols\n")

    kinds = Counter(n for n, _, _, _ in spans)
    print("markup elements present (top 20):")
    for n, c in kinds.most_common(20):
        print(f"  {n:<24} {c:>7,}")

    cmds = [(a.get("name", "?"), a.get("kind", "?"), s, e)
            for n, a, s, e in spans if n == "command_span"]
    cmds.sort(key=lambda t: t[2])
    print(f"\ncommand_span entries: {len(cmds):,}")
    ckinds = Counter(k for _, k, _, _ in cmds)
    print("  kinds: " + ", ".join(f"{k}={c}" for k, c in ckinds.most_common()))

    # Markup offset -> SOURCE line, so a span is quotable as a locus.
    line_of, _source = source_line_map(spans, text)

    print("\n  first 15 commands, as (line span) keyword [kind]:")
    for name, kind, s, e in cmds[:15]:
        a = line_of[min(s, len(line_of) - 1)]
        b = line_of[min(e - 1, len(line_of) - 1)]
        print(f"    {a:>5}..{b:<5} {name:<16} [{kind}]")

    comments = [(s, e) for n, _, s, e in spans
                if n in ("comment", "comment1", "comment2", "comment3")]
    print(f"\n  comment-ish spans: {len(comments):,}  "
          f"(the regions live_source() must blank)")


if __name__ == "__main__":
    main()
