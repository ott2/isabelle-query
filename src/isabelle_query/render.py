"""Rendering — turning entries into the text the CLI prints.

The fourth layer of the DAG (above ``parsing``, below ``commands``).  Pure
formatting: the ``[src ...]`` extent annotation (``_format_extent``), preamble
and annotation previews, the single-entry renderer (``render_entry``) with its
statement / verbatim / comments modes, and the shared verbosity-mode dispatch
(``_emit_matches``) that every match-listing command funnels through.

Depends only on ``model`` and ``parsing`` (``_proof_extent`` for the proof-span
walk, ``LATEX_LINE_RE`` for the figure-noise filter) — no call-graph or CLI
dependency.  The locus grammar and proof-block drill-down live with the
commands that consume them, not here.
"""

from __future__ import annotations

import re
from collections.abc import Iterable
from pathlib import Path

from isabelle_query.model import (
    _ANNOTATION_KINDS,
    CmdFlags,
    Entry,
    TheorySection,
)
from isabelle_query.parsing import LATEX_LINE_RE, _proof_extent


def theory_labels(sections: "Iterable[TheorySection]") -> dict[Path, str]:
    r"""``{resolved path: the shortest directory-qualified name unique here}``.

    A theory prints as its bare name, which is right for a session and wrong
    for a corpus: **461 AFP theory names are used by more than one theory**,
    covering 1,219 of its 9,910 — `Examples` names nineteen different files.
    A `largest` run over the AFP was a wall of unqualified `Bla` with no way
    to tell one from another [disambig-names].

    Qualified by the *minimal distinguishing* suffix, not by the full path.
    Two reasons, and the second is the load-bearing one:

    * a shared root prefix carries no information — every row would gain the
      same `thys/` and be no easier to read;
    * the name is INPUT as well as output.  `theory:line` is meant to round-
      trip, so the emitter has to qualify far enough for the resolver to get
      back to one theory, and no further.  Since [name-roundtrip] a name
      containing a separator resolves *as a name*, so `List_Space/Bla` is not
      mistaken for a path that does not exist — which is what makes a
      qualified label paste-able.

    Scoped to the sections actually being shown, so a single-session run keeps
    bare `Bla` and only a genuine collision grows a prefix.  Two sections at
    the same resolved path are one theory and share a label.

    The label grows from the theory's declared NAME with its directory chain
    in front, not from the file's stem.  Isabelle requires the two to agree
    (`theory Foo` must live in `Foo.thy`) so on disk it is usually the same
    string, and three things follow from preferring the name anyway:

    * a section parsed from a BUFFER has no such file, and taking the stem
      made a label out of the scratch file's name.  A label whose unqualified
      case is not what every other verb prints is not a label;
    * a ROOT may spell a theory with a directory (`theories "While/Hoare"`),
      and then the NAME already carries it — 902 AFP theories, which now
      label as themselves rather than as a bare `Hoare` that no verb accepts;
    * it decides collisions on the right thing.  Growing from stems qualified
      1,316 AFP labels, growing from names qualifies **1,219**: the extra 97
      were theories whose FILES collide while their declared names do not,
      given a prefix that separated nothing a reader could ever have typed.
    """
    by_path: dict[Path, list[str]] = {}
    for sec in sections:
        p = sec.path.resolve()
        if p not in by_path:
            by_path[p] = list(p.parent.parts) + [sec.theory]
    labels: dict[Path, str] = {}
    pending = dict(by_path)
    depth = 1
    while pending:
        groups: dict[str, list[Path]] = {}
        for p, parts in pending.items():
            groups.setdefault("/".join(parts[-depth:]), []).append(p)
        nxt: dict[Path, list[str]] = {}
        for label, paths in groups.items():
            if len(paths) == 1:
                labels[paths[0]] = label
            else:
                for p in paths:
                    # Exhausted: the paths are equal, so no suffix separates
                    # them.  Settle rather than loop — a label that repeats is
                    # a poor answer, an infinite loop is not an answer.
                    if depth >= len(pending[p]):
                        labels[p] = label
                    else:
                        nxt[p] = pending[p]
        pending = nxt
        depth += 1
    return labels


def locus_labels(sections: "Iterable[TheorySection]") -> dict[Path, str]:
    r"""``theory_labels`` re-keyed by each section's path *as stored*.

    The emitter-side view.  ``theory_labels`` keys on the RESOLVED path, so
    that two spellings of one file are one theory and one label; a located hit
    carries the section's path as the section holds it, and resolving that per
    ROW is a syscall per row — `grep obtain` over the AFP prints 73,296 of
    them.  Resolving once per section and looking the stored path up is the
    same answer for free.

    Use it wherever a ``theory:line`` is printed.  A theory NAME cannot be the
    key: 461 AFP theory names are shared, which is the whole reason the label
    exists [disambig-loci].
    """
    sections = list(sections)
    labels = theory_labels(sections)
    return {sec.path: labels[sec.path.resolve()] for sec in sections}


def file_locus(labels: dict[Path, str], path: Path) -> str:
    """The ``grep`` / ``sorry`` locus for *path*: its label, suffix restored.

    Those two verbs report a FILE (``Examples.thy:12``), not a theory, because
    a non-``.thy`` positional has no theory name to print.  ``theory_labels``
    strips the suffix — a theory is cited as `Examples`, never `Examples.thy` —
    so the file view puts it back, which keeps `notes.md` intact as readily as
    it qualifies `Examples.thy` to `alpha/Examples.thy`.  Both spellings
    round-trip: `_resolve_theory` strips a trailing `.thy` before matching the
    label as a path suffix.
    """
    return labels.get(path, path.stem) + path.suffix


def theory_locus(labels: dict[Path, str], path: Path) -> str:
    """The ``instances`` / ``codeqs`` locus for *path*: the label alone, with
    no suffix restored — a site is reported at a THEORY, the way a caller is,
    not at a file the way `grep` is."""
    return labels.get(path, path.stem)


def _format_target(entry: Entry) -> str:
    """Format an entry's enclosing locale/class as a scope step: ``context hpk``.

    Rendered by the caller as ``THEORY ▸ context hpk`` — a narrowing scope path,
    the same ``▸`` idiom the proof-block drill-down uses.  Deliberately NOT
    ``(in locale hpk)``: `enclosing` already appends a role parenthetical
    (``(in proof)``, ``(in statement)``), and two adjacent parentheticals both
    starting with "in" read as one thing said twice.

    Empty when the entry sits at theory level, which is the common case — the
    annotation appears only when it has something to say.  An explicit
    ``(in foo)`` modifier prints as ``target foo`` without a kind, because the
    source does not say whether `foo` is a locale or a class and guessing would
    be worse than reporting exactly what is written.
    """
    if entry.in_target:
        return f"target {entry.in_target}"
    return " ▸ ".join(f"{k} {n}" for k, n in entry.blocks)


def _format_extent(entry: Entry) -> str:
    """Format the `[src ...]` extent annotation for an entry.

    `src` is the entry's full span ``src_start..thy_end`` — a leading `text`
    preamble through the trailing blanks before the next entry.  The `body`
    span ``thy_line..body_end_line`` is surfaced separately whenever it is
    narrower at either end: a leading doc block (``src_start < thy_line``) or
    a trailing inter-lemma block (``body_end < thy_end``).  The body end is
    the safe cut boundary for `bin/move-block.py`; `src` is the
    end-of-region the next entry-or-section starts after.
    """
    if not entry.thy_line:
        return ""
    src_start = entry.src_start
    span_size = entry.line_count
    body_end = entry.body_end_line or entry.thy_end
    if src_start < entry.thy_line or body_end < entry.thy_end:
        body_size = body_end - entry.thy_line + 1
        return (f"[src {src_start}..{entry.thy_end}, "
                f"body {entry.thy_line}..{body_end}, "
                f"{body_size}/{span_size} lines]")
    return f"[src {src_start}..{entry.thy_end}, {span_size} lines]"


def _format_name_line(sec: TheorySection, entry: Entry) -> str:
    ext = _format_extent(entry)
    span = f" {ext}" if ext else ""
    return f"{entry.name} ({entry.tag}) — {sec.theory}{span}"


def _is_latex_noise(line: str) -> bool:
    """Lines containing LaTeX figure/typesetting markup we want to skip in
    truncated previews of text blocks (e.g. UTM.thy's tikzpicture diagrams)."""
    return bool(LATEX_LINE_RE.search(line))


def _strip_text_wrapper(lines: list[str]) -> list[str]:
    """Strip leading `text \\<open>` / `text_raw \\<open>` and trailing
    `\\<close>` from a text block body, so previews don't show the wrapper.
    Returns a copy; does nothing if the markers aren't found.
    """
    if not lines:
        return lines
    out = list(lines)
    # Strip leading "text \<open>" or "text_raw \<open>"
    first = out[0]
    m = re.match(r"^(\s*)(?:text_raw|text)\s*\\<open>\s*(.*)$", first)
    if m:
        stripped_first = (m.group(1) + m.group(2)).rstrip()
        if stripped_first:
            out[0] = stripped_first
        else:
            out = out[1:]
    if not out:
        return out
    # Strip trailing "\<close>" from last line
    last = out[-1]
    if last.rstrip().endswith("\\<close>"):
        trimmed = last.rstrip()[: -len("\\<close>")].rstrip()
        if trimmed:
            out[-1] = trimmed
        else:
            out = out[:-1]
    return out


def _truncate_preview(lines: list[str], n: int,
                      skip_latex: bool = True) -> tuple[list[str], int]:
    """Return (preview_lines, omitted_count).  Picks up to N non-blank,
    non-LaTeX content lines from the start of `lines`.  `omitted_count` is
    how many *original* lines were not included in the preview.
    """
    if n <= 0:
        return [], len(lines)
    out = []
    consumed = 0
    for line in lines:
        consumed += 1
        if not line.strip():
            continue
        if skip_latex and _is_latex_noise(line):
            continue
        out.append(line)
        if len(out) >= n:
            break
    omitted = len(lines) - consumed
    return out, max(0, omitted)


def _render_preamble(sec: TheorySection, preamble: tuple[int, int],
                     mode: str, context: int) -> str:
    """Render a preamble text block.

    mode='summary': first `context` content lines + "[+N more preamble lines]"
    mode='full':    full slice, wrapper stripped
    """
    start, end = preamble
    body = _strip_text_wrapper(sec.slice(start, end))
    block_size = len(body)
    if mode == "full":
        return "\n".join(body)
    preview, _ = _truncate_preview(body, context)
    suffix = ""
    shown = len(preview)
    remaining = block_size - shown
    if remaining == 1:
        return "\n".join(body)
    if remaining > 0:
        suffix = (f"\n  [+{remaining} more preamble lines, "
                  f"use --comments-only or -V to see]")
    return "\n".join(preview) + suffix


_KIND_LABELS = {
    "decl": "declaration",
    "statement": "statement",
    "proof": "proof",
}


def _render_annotations(annotations: list[tuple[int, str, str]], context: int,
                        proof_remaining: int, mode: str) -> str:
    """Render an entry's \\<comment> annotations.

    mode='summary': first `context` notes, flat + "...(N more)" — an inline
                    preview beside the statement, where the surrounding output
                    already says which part of the entry is in view.
    mode='full':    every note, GROUPED by which part of the entry it
                    annotates.  This is the dedicated prose view
                    (`--comments-only`), and there the grouping is the content:
                    a note on the statement says what is being claimed, one in
                    the proof says how it is reached, and running the two
                    together loses the only thing that distinguishes them.
    """
    if not annotations:
        # Fallback: show the existing "+N more proof lines" count line.
        if proof_remaining > 0:
            return (f"  [+{proof_remaining} more proof line"
                    f"{'s' if proof_remaining != 1 else ''}]")
        return ""
    out = []
    if mode == "full":
        for kind in _ANNOTATION_KINDS:
            of_kind = [(ln, c) for ln, c, k in annotations if k == kind]
            if not of_kind:
                continue
            out.append(f"  {_KIND_LABELS[kind]}:")
            out.extend(f"    | line {ln}: {content}" for ln, content in of_kind)
        return "\n".join(out)
    shown = annotations[:max(1, context)]
    for ln, content, _kind in shown:
        out.append(f"  | line {ln}: {content}")
    if len(annotations) > len(shown):
        rest = len(annotations) - len(shown)
        if rest == 1:
            ln, content, _kind = annotations[len(shown)]
            out.append(f"  | line {ln}: {content}")
        else:
            out.append(f"  | ...({rest} more annotations "
                       f"in {proof_remaining}-line proof, use -U N to see more)")
    return "\n".join(out)


def _statement_text(sec: TheorySection, entry: Entry) -> str:
    """The entry's statement slice as one string: the declaration lines
    [thy_line..decl_end_line] (the lemma/def statement, not the proof).

    Falls back to `entry.text` for entries without a source location (e.g.
    an AXIOM placeholder), matching how `render_entry` degrades — so a
    statement search still sees *something* for those.
    """
    if not entry.thy_line:
        return entry.text
    return "\n".join(sec.slice(entry.thy_line, entry.decl_end_line))


def render_entry(sec: TheorySection, entry: Entry, *,
                 verbatim: bool = False,
                 statement: bool = False,
                 comments: str = "on",
                 context: int = 2) -> str:
    """Render a single entry.

    statement:       just the declaration slice [thy_line..decl_end_line]
                     (the statement, no proof) — the narrowest view
    verbatim:        full source slice [thy_line..thy_end]
    comments='on':   preamble (truncated) + header + statement + proof preview
                     + annotations (truncated)
    comments='off':  header + statement + proof preview only (current default)
    comments='only': preamble (full) + header + annotations (full, grouped by
                     which part of the entry each one annotates), no statement
    context:         lines of preamble preview / annotations shown

    `statement` and `verbatim` are opposite ends of the slice spectrum
    (declaration-only vs declaration+proof); `show` declares them mutually
    exclusive at the CLI.  If both somehow arrive, the narrower one wins.
    """
    ext = _format_extent(entry)
    header = f"--- {entry.name} ({entry.tag}) — {sec.theory}.thy {ext} ---"

    # No source location (e.g. AXIOM placeholder) → fall back to entry.text
    if not entry.thy_line:
        return f"{header}\n{entry.text}"

    if statement:
        body_lines = sec.slice(entry.thy_line, entry.decl_end_line)
        return header + "\n" + "\n".join(body_lines)

    if verbatim:
        body_lines = sec.slice(entry.thy_line, entry.thy_end)
        return header + "\n" + "\n".join(body_lines)

    out_parts: list[str] = []

    # Preamble, ABOVE the header because that is where the author wrote it —
    # `text \<open>...\<close>` precedes the declaration it introduces, and
    # reordering it would misreport the source.
    #
    # It is named, and butted straight against the header with no blank line,
    # because a match LIST separates entries by exactly one blank line: an
    # unnamed block set off the same way reads as a hit of its own, which is
    # what `find --statement PAT` looked like when its first match carried a
    # preamble.  One entry renders as one contiguous block.
    if comments != "off" and entry.preamble:
        pmode = "full" if comments == "only" else "summary"
        rendered = _render_preamble(sec, entry.preamble, pmode, context)
        if rendered:
            pstart, pend = entry.preamble
            out_parts.append(
                f"--- preamble for {entry.name} [{pstart}-{pend}] ---")
            out_parts.append(rendered)

    out_parts.append(header)

    if comments == "only":
        # Skip statement + proof; show every annotation, grouped by part.
        if entry.annotations:
            out_parts.append("--- annotations (\\<comment>) ---")
            out_parts.append(_render_annotations(entry.annotations, context,
                                                 0, "full"))
        elif not entry.preamble:
            out_parts.append("(no comment context for this entry)")
        return "\n".join(out_parts)

    # Statement + proof preview
    if entry.proof_line and entry.proof_line >= entry.decl_end_line:
        statement = sec.slice(entry.thy_line, entry.decl_end_line)
        # `lemma a: "P" by simp` puts the proof ON the last statement line, so
        # the statement slice has already printed it and a "first proof line"
        # would print it a second time.  The same holds when a multi-line
        # declaration ends with its proof (`shows "P g" by simp`), which is why
        # this compares against `decl_end_line` and not `thy_line`.
        first_proof = ([] if entry.proof_line <= entry.decl_end_line
                       else sec.slice(entry.proof_line, entry.proof_line))
        proof_end = _proof_extent(sec, entry.proof_line, entry.thy_end)
        remaining = max(0, proof_end - entry.proof_line)
        out_parts.append("\n".join(statement + first_proof))
        if comments != "off" and entry.annotations:
            out_parts.append(_render_annotations(entry.annotations, context,
                                                 remaining, "summary"))
        elif remaining == 1:
            extra = sec.slice(entry.proof_line + 1, entry.proof_line + 1)
            out_parts.append("\n".join(extra))
        elif remaining > 0:
            out_parts.append(f"  [+{remaining} more proof lines]")
    else:
        # No proof captured → just the declaration as recorded by the parser.
        # A `definition` lands here, and its marginal notes are the only prose
        # it can ever have.  Preview only the notes the slice does NOT already
        # show: this branch prints the whole declaration, so a note inside it
        # is on screen already, and repeating it underneath is noise.  (The
        # proof branch above has the opposite problem — it prints one line of
        # the proof, so its preview is the only sight of the rest.)
        body_lines = sec.slice(entry.thy_line, entry.decl_end_line)
        out_parts.append("\n".join(body_lines))
        unseen = [a for a in entry.annotations if a[0] > entry.decl_end_line]
        if comments != "off" and unseen:
            out_parts.append(_render_annotations(unseen, context, 0, "summary"))

    return "\n".join(out_parts)


# ---------------------------------------------------------------------------
# Verbosity-mode dispatch
# ---------------------------------------------------------------------------

def _emit_matches(sections_by_theory: dict[str, TheorySection],
                  matches: list[Entry], pattern: str, flags: "CmdFlags",
                  *, statement: bool = False) -> None:
    # `statement` is the *render* selector (declaration-only).  It is passed
    # explicitly rather than read off `flags` so it stays a `show` concern:
    # on `find`, `flags.statement` means "match the statement slice", which
    # must not bleed into how the matched entries are rendered.
    # Mode dispatch BEFORE the empty guard [count-mode-zero].  A count mode
    # must print a number, and the empty case is the one a script most wants to
    # branch on: with the sentence first, `$(query find X -c)` was arithmetic
    # when X matched and a parse error when it did not.  `names` is the same
    # rule — an empty list is the right answer for a pipeline, and a sentence
    # on stdout would be read as a name.
    if flags.mode == "count":
        print(len(matches))
        return

    if flags.mode == "names":
        for e in matches:
            print(_format_name_line(sections_by_theory[e.theory], e))
        return

    # Only the human-readable modes say so in words.
    if not matches:
        print(f"No entries matching '{pattern}'.")
        return

    if flags.mode == "all":
        for e in matches:
            print(render_entry(sections_by_theory[e.theory], e,
                               verbatim=flags.verbatim,
                               statement=statement,
                               comments=flags.comments,
                               context=flags.context))
            print()
        return

    # mode == "first"
    e0 = matches[0]
    print(render_entry(sections_by_theory[e0.theory], e0,
                       verbatim=flags.verbatim,
                       statement=statement,
                       comments=flags.comments,
                       context=flags.context))
    if len(matches) > 1:
        print()
        print(f"[+{len(matches) - 1} more match(es).  Use --all to show, "
              f"--names for a list, --count for just the count.]")
