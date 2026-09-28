"""The supported import surface for query's Isar span parsing.

Everything else in the package is internal and moves without notice.  These
four names do not: they follow the same policy as the CLI, so a change that
breaks them takes the **minor** version slot (0.x semver — see the release
notes in `pyproject.toml`'s bump commit), never a patch.

    from isabelle_query.api import parse_theory, parse_root, Entry, TheorySection

    sec = parse_theory("Foo", Path("Foo.thy"))
    for e in sec.entries:
        print(e.name, e.thy_line, e.thy_end, e.preamble)

**Why four names and not the dozen that look public.**  `parsing` exposes a
line-scanner per span kind — `extract_text_blocks`, `extract_comment_ranges`,
`extract_heading_spans`, `_attach_preambles`, `_proof_extent` and the rest —
and pinning those individually would freeze the part of this tool that changes
most often while promising nothing extra.  Their *results* are already fields
on `Entry` and `TheorySection`, which `parse_theory` fills in, and the
hard-won thing is not any one scanner but the ORDER they run in: the tokenizer
first, because the declaration scan must not read a commented-out `definition`
as an entry; preambles before `compute_spans`, because they fix each entry's
`src_start` and so decide which entry a leading `text` block is charged to;
`_proof_extent` last, because it needs `thy_end` as a search bound.  A consumer
composing the scanners itself would have to rediscover that, and get it subtly
wrong in the way a hand-rolled `\\<close>\\s*$` gets nested cartouches wrong.
So the composition is what is exported.  Ask for a name here if a span you
need is genuinely not reachable from these objects; do not import it from
`parsing`.

**What you get.**  `TheorySection` carries the whole parse — `entries`,
`outline`, `text_blocks`, `heading_spans`, `comment_ranges`, `nonisar_ranges`
and the character-level `nonisar_spans` / `inner_spans` — plus `source()`,
`slice(a, b)`, and the two redacted views every scanner here reads:
`live_source()` (noise blanked, terms kept) and `outer_source()` (terms blanked
too — Isar command position).  All of them are 1-indexed by line and
length-preserving by column, so a line number means the same thing in every
view.  `Entry` carries `thy_line`, `decl_end_line`, `proof_line`,
`body_end_line`, `src_start`, `thy_end` and `preamble`, and `cut_span` — the
preamble-through-proof span a tool that deletes or moves an entry writes
through, guaranteed to stop before the next entry.
"""

from __future__ import annotations

from pathlib import Path

from isabelle_query.model import Entry, TheorySection
from isabelle_query.parsing import (
    _CUSTOM_COMMANDS,
    _parse_one,
    _populate_custom_commands,
    _root_theories,
    _sections_from_dir,
)

__all__ = ["Entry", "TheorySection", "parse_root", "parse_theory"]


def parse_theory(theory: str, path: Path,
                 lines: list[str] | None = None, *,
                 root: Path | None = None) -> TheorySection:
    """Parse ONE theory's source into a fully-populated :class:`TheorySection`.

    ``lines``, when given, is parsed in place of reading ``path``, which may
    then be synthetic — the route the CLI's ``-`` stdin sentinel takes.  The
    section caches them, so a later ``source()`` never falls back to a path
    that does not exist.

    **Scope, and it is the one that bites.**  Isabelle's keyword table is
    session-wide (`Keywords.++`), so a theory that uses a custom command
    another theory in its session declares is parsed correctly by `query` and,
    without ``root``, NOT by this function, which then sees only ``path``'s own
    header.  Nothing warns you: the command is simply not recognised and its
    declarations are absent.

    Pass ``root`` — the directory you would give ``query -R`` — and the keyword
    table is built exactly as the CLI builds it, from every theory header under
    that root, before this one theory is parsed.  Only headers are read, so
    this costs a walk of the ROOT files rather than a parse of the project: the
    entries then agree with :func:`parse_root`'s for the same theory, at a
    fraction of the cost.  ``session`` is filled in when ``path`` is one of the
    root's theories.  A ``root`` that is not a directory, or that yields no
    theories, raises ``ValueError`` as :func:`parse_root` does.

    That table is a module global, so this saves and restores it rather than
    reading whatever the last call left behind.  Without that, the answer here
    would depend on whether a :func:`parse_root` had run earlier in the process
    — the same result from the same arguments, or not, according to call order,
    which is the worst kind of wrong because it is reproducible per-run and not
    across runs.
    """
    session = None
    pairs: list[tuple[str, Path]] = []
    if root is not None:
        root = Path(root)
        if not root.is_dir():
            raise ValueError(f"{root}: no such directory")
        pairs, session_of = _root_theories(root)
        if not pairs:
            raise ValueError(f"{root}: no theories found — not an Isabelle "
                             f"session root, or unreadable")
        session = session_of.get(Path(path).resolve())
    saved = dict(_CUSTOM_COMMANDS)
    _CUSTOM_COMMANDS.clear()
    try:
        _populate_custom_commands(pairs)
        sec = _parse_one(theory, path, lines)
        sec.session = session
        return sec
    finally:
        _CUSTOM_COMMANDS.clear()
        _CUSTOM_COMMANDS.update(saved)


def parse_root(root: Path) -> list[TheorySection]:
    """Parse every theory under ``root``, exactly as ``query -R root`` does.

    Walks each ROOT file, takes each declared session's theories *plus the
    transitive closure of their in-entry imports*, pre-scans all their headers
    into the shared custom-command table, then parses.  A directory with no
    ROOT falls back to a recursive ``*.thy`` glob.  Theories are deduplicated
    by resolved path, first session wins.

    Raises ``ValueError`` when the walk yields nothing.  That mirrors the CLI,
    which exits 2 rather than printing an empty report: no real Isabelle
    project has zero theories, so an empty result means the root was wrong or
    unreadable, and returning ``[]`` would be indistinguishable from an
    honestly empty answer.  It is the library form of the same rule.
    """
    root = Path(root)
    if not root.is_dir():
        raise ValueError(f"{root}: no such directory")
    _CUSTOM_COMMANDS.clear()   # rebuilt per load from this root's headers
    sections: list[TheorySection] = []
    _sections_from_dir(root, set(), sections)
    if not sections:
        raise ValueError(f"{root}: no theories found — not an Isabelle "
                         f"session root, or unreadable")
    return sections
