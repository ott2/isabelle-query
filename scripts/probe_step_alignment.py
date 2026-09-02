#!/usr/bin/env python3
r"""Probe: align `query`'s step model against Isabelle's own command spans.

THE QUESTION
    Every `shape` metric counts STEPS, and a step is `query`'s reading of "one
    Isar command in a proof body".  Isabelle knows where its commands are and
    what kind each is, and records both in `PIDE/markup` as `command_span`
    elements.  So the step model has an exact reference — not for the metric
    VALUES, which are `query`'s own definitions, but for the population they
    range over.

    This is a DISCOVERY INSTRUMENT, not a fixture corpus.  It reads a session
    database read-only (never `isabelle export`, which builds), needs a built
    heap, and exists to say WHICH commands diverge.  Anything it finds gets
    fixed and pinned with a hand-written test; then this can go.  See
    `[markup-step-model]` in todo.md, and `[declared-names]` for the precedent.

THE COMPARISON
    Isabelle's model is COMMAND-based: a command has an exact extent and may
    span lines or share one.  `query`'s model is LINE-based: at most one step
    per live line, classified by the line's leading command keyword.  So a
    divergence is one of three things, and they are reported apart because they
    mean different things:

      MISSED       Isabelle starts a proof command on a line where `query` books
                   no step at all, and the line is NOT shared with the tail of
                   the preceding command.  `query` has no rule for the keyword:
                   a real defect.
      WRAPPED      same, except the preceding command ENDS on that line — a
                   multi-line command whose tail shares a line with the next
                   command's head.  `query` books one step per line and already
                   spent this line's step on the command above, so the loss is
                   the line model, not the keyword.
      CROWDED      the line has a step and Isabelle starts more than one command
                   there.  WRAPPED's same-line twin, and likewise the documented
                   line-model undercount (`shape.py`'s module docstring).
      INVENTED     `query` books a step on a line where Isabelle starts no
                   command.  A continuation line read as a command.

    Splitting MISSED from WRAPPED is the whole point.  Pooled, they read as one
    1.5% error; split, MISSED is a short list of keywords `query` does not know
    and WRAPPED is a known, deliberate approximation.  Only the first is
    actionable, and the pooled number hides which.

    Structural commands (`proof`, `{`, `}`, `next`) are excluded by design:
    `_scan_steps` tracks them for depth and never books them as steps, so
    counting them as MISSED would report a decision as a defect.

Usage:
    probe_step_alignment.py SESSION [THEORY]   # one theory, or the whole session
    probe_step_alignment.py SESSION --verbose  # list every divergence
    probe_step_alignment.py ALL                # every session with a database
"""
from __future__ import annotations

import sys
from collections import Counter, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from probe_export_oracle import (  # noqa: E402
    _find_db, _read_export, _resolve_source, _theories)
from probe_pide_markup import parse_yxml, source_line_map  # noqa: E402

# Isabelle keyword kinds that occur INSIDE a proof body.  Taken from
# `Pure/Isar/keyword.ML`, restricted to what a proof can contain; a theory-level
# kind (`thy_decl`, `thy_goal_stmt`, ...) is outside the step model by
# construction and is not compared.
PROOF_KINDS = frozenset({
    "qed", "qed_script", "qed_block", "qed_global",
    "prf_goal", "prf_asm", "prf_asm_goal", "prf_chain", "prf_decl",
    "prf_script", "prf_script_goal", "prf_script_asm_goal",
    "prf_open", "prf_close", "prf_block", "next_block",
})
# Of those, the ones `query` deliberately does not book as steps: they open or
# close a block and are tracked as depth instead.  `qed` is NOT here — it is a
# closing step in `query` and a `qed`-kind command in Isabelle, and the two
# agree.  The set is keyed by KEYWORD, not kind, because Isabelle files `qed`
# and `by` under the same `qed` kind while `query` treats only the keyword
# `qed`/`}`/`proof`/`next` structurally.
STRUCTURAL_KEYWORDS = frozenset({"proof", "{", "}", "next"})

# Divergence samples printed per keyword.
SAMPLES = 4


def isabelle_commands(db: Path, theory: str):
    """`(commands, source)` for one theory: every `command_span` as
    `(keyword, kind, start_line, end_line)`, plus the theory source the markup
    encodes.  Lines are 1-based and index that source."""
    body = _read_export(db, theory, "PIDE/markup")
    if not body:
        return None, None
    spans, text = parse_yxml(body)
    line_of, source = source_line_map(spans, text)

    def at(off: int) -> int:
        return line_of[min(max(off, 1), len(line_of) - 1)]

    cmds = [(a.get("name", "?"), a.get("kind", "?"), at(s), at(e - 1))
            for n, a, s, e in spans if n == "command_span"]
    cmds.sort(key=lambda t: (t[2], t[3]))
    return cmds, source


def query_steps(path: Path):
    """`(steps_by_line, proof_lines, theory)` from `query`'s own scan.

    `proof_lines` is every line inside some entry's proof body — the region the
    step model claims.  A command outside it is not a divergence, it is simply
    not in scope.
    """
    from isabelle_query import cli, shape

    sec = cli._parse_one(path.stem, path)
    by_line: dict[int, list] = defaultdict(list)
    in_proof: set[int] = set()
    for entry in sec.entries:
        if not entry.proof_line:
            continue
        end = entry.body_end_line or entry.thy_end or entry.proof_line
        in_proof.update(range(entry.proof_line, end + 1))
        for st in shape._scan_steps(sec, entry):
            by_line[st.line].append(st)
    return by_line, in_proof, sec.theory


def compare(db: Path, theory: str, verbose: bool = False):
    cmds, source = isabelle_commands(db, theory)
    if cmds is None:
        return None
    src_attr = ""
    # The markup carries no `file` attribute of its own; the entity exports do.
    from probe_export_oracle import _ENTITY_RE, _attrs
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
    if not src_attr:
        return None
    path = _resolve_source(src_attr, {})
    if path is None:
        return None

    # The reconstructed source must BE the file, or every line number below is
    # compared against a different document and the whole run means nothing.
    # This is the guard, not a formality: it caught the `xml_body` splice that
    # `source_line_map` now removes (21,365 markup chars vs an 8,171-char file),
    # which would otherwise have shifted loci silently in any theory whose
    # antiquotation rendering spans a line.
    on_disk = path.read_text(encoding="utf-8", errors="replace")
    if source.rstrip("\n") != on_disk.rstrip("\n"):
        print(f"  !! {theory}: reconstructed source differs from "
              f"{path.name} on disk ({len(source):,} vs {len(on_disk):,} "
              f"chars) — skipped")
        return None

    try:
        by_line, in_proof, thy = query_steps(path)
    except Exception as exc:  # noqa: BLE001
        print(f"  !! {theory}: query parse failed: {exc}")
        return None

    # How many proof commands Isabelle starts on each line, ignoring the
    # structural ones `query` books as depth rather than as steps.  `wrap_line`
    # collects the lines a PRECEDING command's extent already reaches, which is
    # what separates a line-model loss from an unknown keyword.
    isa_at: dict[int, list[tuple[str, str]]] = defaultdict(list)
    wrap_line: set[int] = set()
    prev_end = 0
    for kw, kind, start, end in cmds:
        if start <= prev_end:
            wrap_line.add(start)
        prev_end = max(prev_end, end)
        if kind in PROOF_KINDS and kw not in STRUCTURAL_KEYWORDS:
            isa_at[start].append((kw, kind))

    missed: list[str] = []
    outside: list[str] = []
    wrapped: list[str] = []
    crowded: list[str] = []
    invented: list[str] = []
    by_kw: Counter[tuple[str, str, str]] = Counter()
    src = on_disk.splitlines()

    def quote(n: int) -> str:
        return src[n - 1].strip()[:72] if 0 < n <= len(src) else ""

    for line, entries in sorted(isa_at.items()):
        n_q = len(by_line.get(line, ()))
        status = ("matched" if n_q else
                  "OUTSIDE" if line not in in_proof else
                  "WRAPPED" if line in wrap_line else "MISSED")
        for kw, kind in entries:
            by_kw[(kind, kw, status)] += 1
        row = (f"{entries[0][0]}\t{thy}:{line}  "
               f"{'/'.join(k for k, _ in entries)}"
               f"  [{entries[0][1]}]  {quote(line)}")
        if status == "MISSED":
            missed.append(row)
        elif status == "OUTSIDE":
            outside.append(row)
        elif status == "WRAPPED":
            wrapped.append(row)
        elif len(entries) > n_q:
            crowded.append(f"{thy}:{line}  Isabelle {len(entries)} cmds, "
                           f"query {n_q} step(s)  {quote(line)}")

    for line, steps in sorted(by_line.items()):
        if line not in isa_at and line in in_proof:
            invented.append(f"{thy}:{line}  query {steps[0].kw!r} "
                            f"[{steps[0].kind}]  {quote(line)}")

    if verbose:
        for label, rows in (("MISSED", missed), ("OUTSIDE", outside),
                            ("WRAPPED", wrapped), ("CROWDED", crowded),
                            ("INVENTED", invented)):
            for r in rows:
                print(f"  {label:<9} {r}")

    return dict(
        isa_proof_cmds=sum(len(v) for v in isa_at.values()),
        query_steps=sum(len(v) for v in by_line.values()),
        missed=len(missed), outside=len(outside), wrapped=len(wrapped),
        crowded=len(crowded), invented=len(invented),
        by_kw=by_kw, missed_rows=missed, outside_rows=outside,
        wrapped_rows=wrapped, invented_rows=invented, crowded_rows=crowded)


def main() -> None:
    args = [a for a in sys.argv[1:] if not a.startswith("-")]
    verbose = "--verbose" in sys.argv or "-v" in sys.argv
    if not args:
        sys.exit(__doc__)
    session = args[0]
    if session == "ALL":
        from probe_export_oracle import _available_sessions
        targets = [(n, db) for n, db in _available_sessions()]
        print(f"{len(targets)} sessions with a readable database\n")
    else:
        db = _find_db(session)
        if db is None:
            sys.exit(f"no export database for {session!r} — it has never been "
                     f"built.  Run probe_export_oracle.py with no argument to "
                     f"list the sessions that have one.")
        print(f"database: {db}  (read-only)")
        targets = [(session, db)]

    want = args[1] if len(args) > 1 else None
    tot = Counter()
    by_kw: Counter[tuple[str, str, str]] = Counter()
    rows: dict[str, list[str]] = {"missed": [], "outside": [], "wrapped": [],
                                  "invented": [], "crowded": []}
    done = 0
    # One theory may be reachable through several sessions' databases (an entry
    # imported by another).  Compare each source ONCE, or a shared theory's
    # divergences are counted as many times as it is built.
    seen: set[str] = set()
    for name, db in targets:
        thys = _theories(db, name)
        if want:
            thys = [t for t in thys if t == want or t.split(".")[-1] == want]
        for t in thys:
            if t.split(".")[-1] in seen:
                continue
            r = compare(db, t, verbose=verbose)
            if r is None:
                continue
            seen.add(t.split(".")[-1])
            done += 1
            for k in ("isa_proof_cmds", "query_steps", "missed", "outside",
                      "wrapped", "crowded", "invented"):
                tot[k] += r[k]
            by_kw.update(r["by_kw"])
            for k in rows:
                rows[k].extend(r[f"{k}_rows"])
    if want and not done:
        sys.exit(f"no theory {want!r} compared")

    print(f"\n=== {done} theories compared ===")
    print(f"Isabelle proof commands   {tot['isa_proof_cmds']:>7,}")
    print(f"query steps               {tot['query_steps']:>7,}")
    print(f"  MISSED   (no rule)      {tot['missed']:>7,}")
    print(f"  OUTSIDE  (not scanned)  {tot['outside']:>7,}")
    print(f"  WRAPPED  (line-model)   {tot['wrapped']:>7,}")
    print(f"  CROWDED  (line-model)   {tot['crowded']:>7,}")
    print(f"  INVENTED (no command)   {tot['invented']:>7,}")

    counts: dict[tuple[str, str], Counter] = defaultdict(Counter)
    for (kind, kw, status), n in by_kw.items():
        counts[(kind, kw)][status] += n
    ranked = sorted(counts.items(), key=lambda kv: -kv[1]["MISSED"])
    hot = [(k, c) for k, c in ranked if c["MISSED"]]
    if hot:
        print("\nMISSED by keyword (no rule in the step classifier):")
        print(f"  {'keyword':<14} {'kind':<12} {'missed':>7} {'wrapped':>8}"
              f" {'matched':>8}  rate")
        for (kind, kw), c in hot:
            seen = c["MISSED"] + c["WRAPPED"] + c["matched"]
            print(f"  {kw:<14} {kind:<12} {c['MISSED']:>7,} "
                  f"{c['WRAPPED']:>8,} {c['matched']:>8,}"
                  f"  {100.0 * c['MISSED'] / seen:>5.1f}%")

    # Samples PER KEYWORD, not just the first ten overall: the head of a
    # theory-ordered list is whatever the alphabetically-first entry happens to
    # do, which says nothing about the keyword that dominates the count.
    if rows["missed"]:
        per_kw: dict[str, list[str]] = defaultdict(list)
        for r in rows["missed"]:
            kw, _, rest = r.partition("\t")
            per_kw[kw].append(rest)
        print(f"\nMISSED samples, {SAMPLES} per keyword:")
        for (_kind, kw), c in hot:
            for r in per_kw.get(kw, [])[:SAMPLES]:
                print(f"  {kw:<12} {r}")
    if rows["outside"]:
        per_kw = defaultdict(list)
        for r in rows["outside"]:
            kw, _, rest = r.partition("\t")
            per_kw[kw].append(rest)
        print(f"\nOUTSIDE by keyword (line is in no proof body query scanned):")
        for kw, rs in sorted(per_kw.items(), key=lambda kv: -len(kv[1]))[:12]:
            print(f"  {kw:<12} {len(rs):>6,}   e.g. {rs[0]}")
    for label in ("invented", "wrapped", "crowded"):
        if rows[label]:
            print(f"\nfirst {label} (of {len(rows[label]):,}):")
            for r in rows[label][:8]:
                print(f"  {r.replace(chr(9), '  ')}")


if __name__ == "__main__":
    main()
