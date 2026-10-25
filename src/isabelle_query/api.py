"""The supported import surface for query's Isar span parsing.

Everything else in the package is internal and moves without notice.  These
five names do not: they follow the same policy as the CLI, so a change that
breaks them takes the **major** version slot (SemVer, from 1.0.0; see the
release notes in `pyproject.toml`'s bump commit).

    from isabelle_query.api import (parse_theory, parse_root, resolve_theories,
                                    Entry, TheorySection)

    sec = parse_theory("Foo", Path("Foo.thy"))
    for e in sec.entries:
        print(e.name, e.thy_line, e.thy_end, e.preamble)

**Why so few names, and not the dozen that look public.**  `parsing` exposes a
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
through, guaranteed to stop before the next entry.  `preamble_follows_heading`
says the preamble sits under a heading with no entry between, where it may
introduce the section instead: a tool should ask there rather than move it.
Leaving it behind is `e.cut_span and (e.thy_line, e.cut_span[1])`, which
keeps every guarantee of `cut_span`, `None` included.

**Reading a locus.**  query prints a place as `THEORY:LINE` or
`THEORY:A..B`, where THEORY is a label, not a path: the bare name in a
session, the shortest unique directory-qualified suffix in a corpus.
`resolve_theories` maps it back to files exactly as the CLI does, so a span a
`--spans` column printed can be edited without a second, drifting reader.
"""

from __future__ import annotations

from collections.abc import Iterable
from pathlib import Path
from typing import NamedTuple

from isabelle_layout import default_t_dir

from isabelle_query.model import Entry, TheorySection, _TheoryIndex
from isabelle_query.parsing import (
    _CUSTOM_COMMANDS,
    _parse_one,
    _populate_custom_commands,
    _root_theories,
    _sections_from_dir,
)

__all__ = ["Entry", "TheorySection", "parse_root", "parse_theory",
           "resolve_theories"]


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


class _Theory(NamedTuple):
    """A theory as a ROOT walk names it: enough to resolve, nothing parsed."""
    theory: str
    path: Path


def resolve_theories(names: Iterable[str], *, root: Path | None = None
                     ) -> dict[str, list[Path]]:
    """The ``.thy`` files each of *names* designates, as the CLI reads the
    THEORY of a ``THEORY:LINE`` or ``THEORY:A..B`` locus [theory-candidates].

    A name may be a path, a bare theory name, a label (`beta/Examples`, the
    shortest directory-qualified suffix query prints over a corpus), or a
    path-spelled name a ROOT declares (`While/Hoare`).  The tiers are the
    CLI's, in its order — path, exact name, label — through the same
    function (`model.theory_candidates`, indexed once), so what query prints
    this reads back.  The CLI's two guesses after them are left out, because
    each can land a writer in the wrong file: the stem of a name that
    matched nothing (`gamma/Unique` would give `alpha/Unique`), and a
    case-insensitive name.  A label query printed never needs either.

    **Every candidate, not the first.**  Each value lists every file of the
    first tier that matched, resolved, in load order; its first is the file
    the CLI would use.  More than one means the name is ambiguous HERE: the
    CLI prints a bare name only where it is unique among the theories it
    showed, and *root* may be wider.  An editor should refuse then and name
    the candidates.  An empty list is a name that designates no theory
    under *root*.

    ``root`` is the directory you would give ``query -R``; without it, the
    root is found as the CLI finds one (``$ISABELLE_QUERY_ROOT``, an
    ``.isabelle-query`` marker, the nearest ``ROOT``, else the current
    directory).  Relative path names resolve against the current directory,
    as they do on the command line.

    Only ROOT files and theory headers are read, once per call however many
    names it holds, so pass a batch rather than calling once per locus:
    over the whole AFP the walk takes about 2 s, over a project a few
    hundredths.  A ``root`` that is not a directory, or that yields no
    theories, raises ``ValueError`` as :func:`parse_root` does.
    """
    if isinstance(names, str):
        raise TypeError("resolve_theories takes a collection of names, "
                        "not one string")
    root = Path(root) if root is not None else default_t_dir()
    if not root.is_dir():
        raise ValueError(f"{root}: no such directory")
    pairs, _session_of = _root_theories(root)
    # The theories `query -R root` loads, in its order and with its dedup:
    # a missing file is skipped and the first path to a file wins.
    theories: list[_Theory] = []
    seen: set[Path] = set()
    for theory, path in pairs:
        if not path.exists():
            continue
        resolved = path.resolve()
        if resolved not in seen:
            seen.add(resolved)
            theories.append(_Theory(theory, resolved))
    if not theories:
        raise ValueError(f"{root}: no theories found — not an Isabelle "
                         f"session root, or unreadable")
    index = _TheoryIndex(theories)
    return {name: [t.path for t in index.candidates(name, guess=False)]
            for name in names}
