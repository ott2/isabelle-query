#!/usr/bin/env python3
r"""Query the theory index — computed live from .thy files on every invocation.

All commands re-parse the theory tree (<100ms).  Results are always in
sync with the current .thy source.  Use -h/--help on any subcommand for
its options.

This module is the CLI **entry point and facade**.  The implementation was
split out of a single file into a strict module DAG (each layer imports only
from those above it in this list):

* `model`    — the `Entry` / `TheorySection` / `CallGraph` / `CmdFlags`
               dataclasses and the shared tag frozensets.
* `parsing`  — .thy → entry database: the declaration grammar, name
               extraction, span attribution, custom-command scanning, and the
               ROOT-walking enumeration.
* `graph`    — usage analysis: line→entry attribution, the prose/def-site
               exclusion masks, the citation router and call graph, the
               proof-method census, and the one BFS behind every `-r` form.
* `render`   — `_format_extent`, `render_entry`, previews, and the shared
               verbosity-mode dispatch (`_emit_matches`).
* `commands` — one `cmd_*` per subcommand, plus the lookup / locus-grammar /
               proof-block-drill-down helpers they share.
* `cli` (this module) — session loading (`active_t_dir` / `load_index` and the
               `--root` override), the `FileSource` / `_load_sections` token
               routing, the `_run_*` handlers, the argparse tree, and `main()`.

Every name each layer defined under the old single-file layout is re-imported
here (the `from isabelle_query.<layer> import ...` blocks below), so
`cli.<name>` keeps resolving for the test suite and any external caller.  The
argparse tree wires each subcommand through one shared flag helper per feature
(`_add_count_flag`, `_add_names_flag`, `_add_with_comments_flag`,
`_add_path_files_arg`, `_add_mode_flags`, `_add_verbatim_flag`,
`_add_statement_flag`, `_add_comment_flags`, `_add_context_flag`) so
per-subparser declarations stay short and uniform.
"""

from __future__ import annotations

import os
import re
import sys
from bisect import bisect_right
from collections import Counter
from collections.abc import Callable, Iterable
from dataclasses import dataclass
from operator import itemgetter
from pathlib import Path

from isabelle_query import _isabelle_namespace as _isa_ns
from isabelle_query import _namespace_resolve as _ns
from isabelle_query import graph
from isabelle_query import shape
# The invoked command name, shared with `shape_cmds` — see `_prog` for why it
# is a leaf module.  Re-exported here (as `cli._prog_name`) for the facade.
from isabelle_query._prog import prog_name as _prog_name  # noqa: F401
from isabelle_layout import (
    default_t_dir,
    discover_roots,
    iter_sessions,
    parse_root_sessions,
    parse_thy_imports,
    resolve_base_logic,
    resolve_session_theory,
)
from isabelle_layout.distribution import is_known_nonhol_base
# Core data model, extracted to `model.py`.  Re-exported here (unqualified)
# so every existing `cli.Entry` / `cli.CallGraph` / `cli.CmdFlags` reference —
# in this module, the sibling command modules, and the test suite — keeps
# resolving through the `cli` facade after the split.
from isabelle_query.model import (  # noqa: F401  (re-exported for the facade)
    CallGraph,
    CmdFlags,
    Entry,
    TheorySection,
    _CITABLE_TAGS,
    _DEFINITION_TAGS,
    _DROP_NAMES_UPTO,
)
# Theory parsing, extracted to `parsing.py`.  Re-exported so `cli.extract_entries`
# / `cli._parse_one` / `cli._isa_word_pattern` etc. keep resolving for the test
# suite, and so this module's retained loading + routing code (load_index,
# _load_sections) can call the parse machinery by bare name.
from isabelle_query.parsing import (  # noqa: F401  (re-exported for the facade)
    LATEX_LINE_RE,
    RULE_LABEL_RE,
    _CUSTOM_COMMANDS,
    _SELECTOR_RE,
    _and_siblings,
    _isa_word_pattern,
    _LOCALE_LABEL_RE,
    _locale_facts,
    _line_mask,
    _parse_def_name,
    _parse_name,
    _parse_one,
    _parse_plain,
    _parse_typedecl_name,
    _populate_custom_commands,
    _proof_extent,
    _sections_from_dir,
    extract_entries,
    scan_keywords,
    sections_for_session,
)
# Call graph / usage analysis, extracted to `graph.py`.  Re-exported so
# `cli._build_call_graph` / `cli._scan_methods` / `cli._entry_at_line` etc.
# resolve for the test suite and this module's retained command code.
from isabelle_query.graph import (  # noqa: F401  (re-exported for the facade)
    _bfs_depths,
    _build_call_graph,
    _build_def_sites,
    _build_line_index,
    _entry_at_line,
    _entry_by_name,
    _is_citation_name,
    _noise_ranges,
    _noise_spans,
    _scan_methods,
    _sections_by_theory,
)
# Entry rendering / verbosity dispatch, extracted to `render.py`.  Re-exported
# so `cli.render_entry` / `cli._format_extent` / `cli._statement_text` resolve
# for the test suite and this module's retained command code.
from isabelle_query.render import (  # noqa: F401  (re-exported for the facade)
    _emit_matches,
    _format_extent,
    _format_name_line,
    _statement_text,
    _strip_text_wrapper,
    _truncate_preview,
    render_entry,
)
# Command implementations + shared lookup / locus / drill-down helpers,
# extracted to `commands.py`.  Re-exported so the `_run_*` handlers below can
# dispatch to `cmd_*` by bare name, the routing helpers reach `_resolve_theory`
# / `_parse_locus` / the stdin sentinels, and the test suite's `cli.cmd_*` /
# `cli._proof_blocks` / `cli._owner_field` references keep resolving.
from isabelle_query.commands import (  # noqa: F401  (re-exported for the facade)
    _STDIN_NAME,
    _STDIN_PATH,
    _STDIN_SENTINEL,
    _Block,
    _block_field,
    _block_label,
    _compute_unused,
    _enclosing_blocks,
    _enclosing_entry,
    _find_callers,
    _grep_sections,
    _locus_role,
    _owner_field,
    _parse_line_range,
    _parse_locus,
    _proof_blocks,
    _read_stdin_lines,
    _resolve_import,
    _resolve_theory,
    _suggest_theory,
    cmd_callees,
    cmd_callers,
    cmd_defs,
    cmd_deps,
    cmd_enclosing,
    cmd_find,
    cmd_find_and,
    cmd_graph,
    cmd_grep,
    _dot_quote,
    cmd_instances,
    cmd_largest,
    cmd_lines,
    cmd_methods,
    cmd_outline,
    cmd_refs,
    cmd_show,
    cmd_sorry,
    cmd_summary,
    cmd_theory,
    cmd_unused,
)
# The `shape` proof-metrics command family, extracted to `shape_cmds.py` (it
# sits above `commands` — reusing `_parse_locus` / `_resolve_theory` — and below
# this facade).  Re-exported so `cli.cmd_shape_*` resolves for the test suite and
# the `_run_shape_*` handlers below dispatch by bare name, matching every other
# command family.
from isabelle_query.shape_cmds import (  # noqa: F401  (re-exported for the facade)
    cmd_shape_census,
    cmd_shape_lemma,
    cmd_shape_steps,
    cmd_shape_summary,
    cmd_shape_widest,
)

# ---------------------------------------------------------------------------
# Session loading — resolve the active root and build the live index.  *Which*
# root to parse is config (the `--root` override the test suite rebinds), so it
# stays here; the parse machinery it drives lives in `parsing.py`.
# ---------------------------------------------------------------------------

_ROOT_OVERRIDE: Path | None = None  # set by main() from --root


def active_t_dir() -> Path:
    """The session directory the index is built from: the `--root`
    override if `main()` set one, else :func:`default_t_dir` (which
    consults `$ISABELLE_QUERY_ROOT` and walks up from the cwd)."""
    return _ROOT_OVERRIDE if _ROOT_OVERRIDE is not None else default_t_dir()


# Exit status for a root that cannot be read.  Distinct from 1 (a command that
# ran and found nothing) precisely because that is the distinction the silent
# failure destroyed.
_EXIT_BAD_ROOT = 2

# Exit status when a downstream WRITE FAILS because the reader closed the pipe
# (`census | head` over a corpus).  128 + SIGPIPE(13) is what a shell reports
# for a process killed by SIGPIPE, so pipelines and `$?` checks read the same as
# they do for `yes | head`.
#
# Note what this is NOT: a promise that every `| head` exits 141.  When the
# whole answer fits the 64K pipe buffer no write ever fails, the command
# finishes normally, and the status is 0 — which is correct, and is exactly what
# `seq 10 | head -3` does while `seq 200000 | head -3` dies of SIGPIPE.  The
# producer wrote everything; the reader chose to stop.  Forcing 141 there would
# report failure for a run that succeeded.  Measured over five AFP corpora
# straddling the buffer, 5 runs each, deterministic either side
# (`scripts/probe_closed_stdout.py`) [closed-stdout].
_EXIT_SIGPIPE = 141


def _fail_root(root: Path, why: str) -> None:
    """Report an unusable root on stderr and exit non-zero.

    An empty result printed silently is indistinguishable from a legitimate
    "nothing found", so a wrapper script cannot tell a broken run from a true
    zero — which is how a shell path-expansion bug produced a whole run of
    zero-record censuses that all looked valid.  Every path that can yield an
    empty index therefore names the directory it read and says why it came
    back empty.
    """
    print(f"{_prog_name()}: {root}: {why}", file=sys.stderr)
    sys.exit(_EXIT_BAD_ROOT)


def _diagnose_empty_root(root: Path) -> str:
    """Why did this root yield no theories?

    Only ever called once the index has already come back empty, so the ROOT
    re-scan it does costs nothing on a normal run.  Ordered narrowest-cause
    first: each check assumes the previous one passed.
    """
    if not root.exists():
        return "no such directory"
    if not root.is_dir():
        return "not a directory"
    roots = discover_roots(root)
    # A rootless directory is NOT automatically empty: `_sections_from_dir`
    # falls back to a recursive `*.thy` glob, so a bare directory of theories
    # still loads.  Reaching here without a ROOT therefore means there was
    # nothing to glob either — say that, rather than blaming the missing ROOT.
    if not roots:
        thy = next(root.rglob("*.thy"), None)
        if thy is None:
            return ("no ROOT or ROOTS file, and no .thy files — "
                    "not an Isabelle session directory")
        return (f"no ROOT or ROOTS file, and the .thy files present "
                f"(e.g. {thy.name}) yielded no theory")
    sessions = iter_sessions(root)
    if not sessions:
        return (f"{len(roots)} ROOT file(s) found, but none declares a "
                f"session")
    shown = ", ".join(s.name for s in sessions[:3])
    more = "" if len(sessions) <= 3 else f", +{len(sessions) - 3} more"
    return (f"{len(sessions)} session(s) declared ({shown}{more}) but no "
            f"theory resolved — check ROOT's `theories` / `directories` "
            f"clauses")


def load_index() -> list[TheorySection]:
    """Walk the active session directory, parsing each declared theory.
    Searches at the session root and in any sub-directory declared by
    ROOT's `directories` clause.  See :func:`active_t_dir` for how the
    directory is resolved (`--root` / `$ISABELLE_QUERY_ROOT` / cwd discovery).

    An empty index is always an error here, not a result: no real Isabelle
    project has zero theories, so reaching this point means the root was
    wrong, unreadable, or not a session — see :func:`_fail_root`.
    """
    sections: list[TheorySection] = []
    seen_paths: set[Path] = set()
    _CUSTOM_COMMANDS.clear()  # rebuilt per load from the active root's headers
    root = active_t_dir()
    _sections_from_dir(root, seen_paths, sections)
    if not sections:
        _fail_root(root, _diagnose_empty_root(root))
    return sections



# ---------------------------------------------------------------------------
# Argument parsing (argparse with subcommands)
# ---------------------------------------------------------------------------

import argparse


def _flags_from_ns(ns: argparse.Namespace) -> CmdFlags:
    """Build CmdFlags from an argparse Namespace."""
    f = CmdFlags()
    # Precedence: count > names > all > default ("first").
    if getattr(ns, "all", False):
        f.mode = "all"
    if getattr(ns, "names", False):
        f.mode = "names"
    if getattr(ns, "count", False):
        f.mode = "count"
    f.verbatim = getattr(ns, "verbatim", False)
    f.statement = getattr(ns, "statement", False)
    if getattr(ns, "no_comments", False):
        f.comments = "off"
    elif getattr(ns, "comments_only", False):
        f.comments = "only"
    f.context = getattr(ns, "context", 2)
    f.with_comments = getattr(ns, "with_comments", False)
    f.recursive = getattr(ns, "recursive", False)
    f.by_theory = getattr(ns, "by_theory", False)
    f.roots = getattr(ns, "roots", False)
    keep_args = getattr(ns, "keep", None) or []
    f.keep = frozenset(n for arg in keep_args
                       for n in arg.split(",") if n.strip())
    f.external = getattr(ns, "external", False)
    f.drop_names_upto = getattr(ns, "drop_names_upto", _DROP_NAMES_UPTO)
    f.reach = getattr(ns, "reach", "closure")
    f.sorts = getattr(ns, "sorts", False)
    return f


# -- FILES routing (shared by every `query CMD FILES`-shaped command) --------
#
# Routing answers *where the bytes are*; the command's parse policy answers
# *whether to read them as Isabelle*.  Keeping them separate is why one token
# resolver serves both `lines` (ignore-syntax, raw text) and the search family
# (`largest`/`sorry` syntax-aware, `grep` inferred) without either reinventing
# `-`/path/name resolution.

@dataclass
class FileSource:
    """A resolved `CMD FILES` token, decoupled from how a command reads it.

    `label` is the display/theory name, `path` the real or synthetic
    (`<stdin>`) path.  `preread` carries content that has no path to re-read
    (stdin); on-disk sources leave it ``None`` and are read lazily, so the
    AFP-scale memory profile is unchanged (nothing is materialised until a
    command actually parses or slices it).
    """
    label: str
    path: Path
    preread: list[str] | None = None

    @property
    def from_stdin(self) -> bool:
        return self.path == _STDIN_PATH

    def lines(self) -> list[str]:
        """The source's raw lines — the pre-read content, or the file read
        on demand."""
        if self.preread is not None:
            return self.preread
        return self.path.read_text().splitlines()


def _stdin_source() -> FileSource:
    """The one-shot `-` source: standard input read once, in full."""
    return FileSource(_STDIN_NAME, _STDIN_PATH, _read_stdin_lines())


def _resolve_file_source(token: str, p: Path,
                         get_index) -> FileSource:
    """Resolve one non-`-`, non-directory FILES token to a `FileSource`.

    `p` is the caller's already-resolved ``Path(token)``.  An existing file
    resolves to itself; otherwise the token is treated as a bare theory
    **name** (or a path whose stem names one), looked up in the lazily-built
    index via `get_index` — matching how outline/show/defs/callees take
    names.  A token that is neither exits with a 'did you mean ...?' hint.

    This is the single home of path/name routing: `_load_sections` and
    `_run_lines` both call it, so the two can never drift on what a token
    means.
    """
    if p.exists():
        return FileSource(p.stem, p)
    index = get_index()
    sec = _resolve_theory(index, token)
    if sec is not None:
        return FileSource(sec.path.stem, sec.path)
    suggestion = _suggest_theory(index, token)
    hint = f" (did you mean {suggestion}?)" if suggestion else ""
    print(f"ERROR: not a path or known theory: {token}{hint}",
          file=sys.stderr)
    sys.exit(1)


def _section_from(src: FileSource, parse: str) -> TheorySection:
    """Parse a source into a TheorySection under the command's parse policy.

    `parse="syntax"` always applies the Isabelle entry grammar — for
    `largest`/`sorry`, whose output *is* the entry view, syntax-awareness is
    intrinsic, not a property of the file.  `parse="infer"` (only `grep`, the
    command where it is genuinely unclear) decides per source from the one
    piece of evidence available: the `.thy` suffix, with stdin — which has no
    suffix — defaulting to syntax-aware (the load-bearing case is a piped
    theory).  The suffix is thus *evidence for the ambiguous case*, never the
    primary switch.
    """
    syntactic = parse == "syntax" or src.from_stdin or src.path.suffix == ".thy"
    if syntactic:
        return _parse_one(src.label, src.path, src.preread)
    return _parse_plain(src.label, src.path, src.preread)


def _split_path_window(token: str, get_index
                       ) -> tuple[tuple[int, int | None] | None, str]:
    """Peel an optional `:A..B` / `:LINE` window off a grep PATH positional.

    Returns ``(window, file_token)``.  The suffix is treated as a window
    *only* when the part before it resolves to an existing file or a known
    theory — otherwise the token is returned unchanged, so a path that
    happens to end in a colon, the `-` stdin sentinel, or a plain bad token
    all fall through to the normal resolver and its existing error.  Reuses
    `_parse_locus`, so the window grammar (`A..B`, trailing-marker tolerance)
    matches `enclosing`.
    """
    locus = _parse_locus(token)
    if locus is None:
        return None, token
    file_token, lo, hi = locus
    resolves = (Path(file_token).expanduser().exists()
                or _resolve_theory(get_index(), file_token) is not None)
    return ((lo, hi), file_token) if resolves else (None, token)


def _load_sections(ns: argparse.Namespace, parse: str = "infer", *,
                   windows: bool = False) -> list[TheorySection]:
    """Load theory sections from trailing positional PATHs, or the
    project ROOTs.

    Subcommands in the *search* family that accept ``nargs='*'`` trailing
    path positionals (``grep PATTERN ...``, ``largest ...``, ``sorry ...``)
    pre-populate ``ns.files``; the parse is then restricted to those paths
    instead of the full project index.  The *lookup* family
    (``callers``/``callees``/``show``/...) carries no PATH positionals —
    ``getattr(ns, "files", None)`` is falsy there, so they load the full
    index and scope via the global ``-R/--root``.

    Each positional may be:

    * ``-``  -> read one theory from **standard input** (the stdin
      sentinel), so the whole search family operates on piped content that
      never hit disk — ``git show REF:FILE | query grep PAT -``.
    * a ``.thy`` file path  -> that single theory.
    * a directory containing a ``ROOT`` file  -> all theories
      declared by ROOT (resolved through ROOT's ``theories`` and
      ``directories`` clauses, matching Isabelle's own semantics).
    * a directory with no ``ROOT``  -> recursive ``*.thy`` glob.

    When ``windows`` is set (grep only), a positional may carry a trailing
    ``:A..B`` (or ``:LINE``) line window — ``Foo.thy:100..200`` — scoping the
    search to those lines.  The file part resolves as usual and the window is
    attached to the section for `_grep_sections` to honour.

    Results are unioned and deduplicated by resolved absolute
    path, so passing two directories where one holds symlinks into
    the other does not double-count the shared theories.

    `parse` is the caller's parse policy, applied to single-file and stdin
    sources (a directory always yields syntax-aware `.thy` sections):
    ``"syntax"`` forces the entry grammar (`largest`/`sorry`), ``"infer"``
    decides per source from the `.thy` suffix (`grep`).  See `_section_from`.
    Token routing itself is delegated to `_resolve_file_source`, shared with
    `lines`.
    """
    files: list[str] = list(getattr(ns, "files", None) or [])
    if not files:
        return load_index()
    sections: list[TheorySection] = []
    seen_paths: set[Path] = set()
    index_cache: list[list[TheorySection]] = []  # memo box for name lookups

    def get_index() -> list[TheorySection]:
        if not index_cache:
            index_cache.append(load_index())
        return index_cache[0]

    stdin_read = False
    for token in files:
        if token == _STDIN_SENTINEL:
            # stdin is one-shot: a repeated `-` would read an exhausted
            # stream, so consume it at most once.
            if not stdin_read:
                stdin_read = True
                sections.append(_section_from(_stdin_source(), parse))
            continue
        window: tuple[int, int] | None = None
        if windows:
            window, token = _split_path_window(token, get_index)
        p = Path(token).expanduser().resolve()
        if p.is_dir():
            _sections_from_dir(p, seen_paths, sections)
            continue
        src = _resolve_file_source(token, p, get_index)
        resolved = src.path.resolve()
        if resolved in seen_paths:
            continue
        seen_paths.add(resolved)
        sec = _section_from(src, parse)
        sec.line_window = window
        sections.append(sec)
    return sections


# -- Shared flag groups (added to subparsers that need them) ----------------

def _add_mode_flags(p: argparse.ArgumentParser) -> None:
    # Composite bundle for subparsers that accept all three.  Not mutually
    # exclusive: -a --names composes (= "all matches as names").  Precedence
    # at resolution: -c > --names > -a > default.  Subparsers wanting only a
    # subset call the per-flag helpers (`_add_count_flag`,
    # `_add_names_flag`) directly.
    p.add_argument("-a", "--all", action="store_true",
                   help="show all matches")
    _add_count_flag(p, "just print the count (wins over -a / --names)")
    _add_names_flag(p, "names + tags + theory only (composable with -a)")


def _add_count_flag(p: argparse.ArgumentParser,
                    help_text: str = "just print the count") -> None:
    p.add_argument("-c", "--count", action="store_true", help=help_text)


def _add_theory_scope_flag(p: argparse.ArgumentParser) -> None:
    """``--theory THY`` — confine the search to one theory [theory-refs].

    Repeatable, so a scope is a batch like every other list argument here.
    `find` has no trailing PATH positionals (a name search is corpus-global by
    nature), which left the global `-R/--root` as its only knob — too coarse
    when the question is "where in *this* theory", and the reason the answer
    was a pipe into `grep`.
    """
    p.add_argument("--theory", dest="theory_scope", metavar="THY",
                   action="append",
                   help="confine the search to theory THY (name, Foo.thy, or "
                        "a path); repeatable")


def _add_names_flag(p: argparse.ArgumentParser,
                    help_text: str = "names + tags + theory only") -> None:
    # No `-n` short flag: it collides with the universal grep/rg convention
    # where `-n` = line numbers.  This tool always prints `theory:line`
    # locations, so there is nothing for a grep-style `-n` to toggle; rather
    # than squat on it for `--names` (a silent, surprising mode switch for
    # anyone with grep muscle memory), we leave `-n` free for its
    # conventional meaning and spell the terse view out as `--names`.
    # On the search verbs `-n` is *swallowed* rather than left unknown — see
    # `_add_line_number_noop_flag`.
    p.add_argument("--names", action="store_true", help=help_text)


def _add_sorts_flag(p: argparse.ArgumentParser) -> None:
    # The site verbs' one extra column, shared so the wording cannot drift:
    # WRITTEN text only.  No type is inferred, so a site whose source writes
    # no sort shows none — a type this tool made up would be the one thing in
    # the output nobody could check against the source.
    p.add_argument("--sorts", action="store_true",
                   help="in the name column, add the sort / arity / signature "
                        "THE SOURCE WRITES at that site (`prod :: "
                        "(topological_space, topological_space) "
                        "topological_space`).  Written text only -- no types "
                        "are inferred, so a site whose source writes none "
                        "shows none.")


class _IgnoredFlagAction(argparse.Action):
    """A flag that parses and then does nothing.

    For a flag this tool must not *reject* but has nothing to do with.  It
    writes nothing to the namespace (dest and default are both SUPPRESS), so
    no handler can accidentally branch on whether it was passed — the flag is
    invisible past the parser, which is the point.
    """
    def __init__(self, option_strings, dest=argparse.SUPPRESS,
                 default=argparse.SUPPRESS, help=None):
        super().__init__(option_strings=option_strings, dest=dest,
                         default=default, nargs=0, help=help)

    def __call__(self, parser, namespace, values, option_string=None):
        pass  # deliberately nothing


def _add_line_number_noop_flag(p: argparse.ArgumentParser) -> None:
    """Accept-and-ignore `-n`/`--line-number` on the search verbs.

    `-n` cannot *mean* line numbers here: what these verbs print is not a
    grep `-n` prefix but the `theory.thy:LINE  owner` locus, load-bearing for
    navigation and the `theory:line` round-trip, so it is always on and there
    is nothing to toggle.  Nor can it mean `--names` (see `_add_names_flag`).
    That left `-n` an unknown flag — and of the three options that is the
    worst: `query grep PAT F -n`, typed from grep reflex, dies with a usage
    dump, which reads as "`query grep` is the wrong tool" and sends the caller
    back to raw `grep`/`rg` — the exact substitution `query` exists to
    prevent.  An error here does not teach, it de-reinforces.

    So swallow it.  This is safe *because* the locus is always on: the line
    number the reflex was asking for is already in the output, so ignoring
    `-n` gives that caller precisely what they wanted, and there is no state
    in which the flag would have changed the answer.
    """
    p.add_argument("-n", "--line-number", action=_IgnoredFlagAction,
                   help="accepted and ignored — every match already prints "
                        "its `theory.thy:LINE` locus (grep-compatibility "
                        "no-op)")


def _add_with_comments_flag(
        p: argparse.ArgumentParser,
        help_text: str = "also search inside `text` blocks and "
                         "\\<comment> annotations (default: live source "
                         "only)") -> None:
    # The search family's single "widen into cartouche prose" toggle, spelled
    # the same on `find` and `grep`.  No `-a` short flag: on `find`, `-a`
    # already means "show all matches" (the lookup-family mode from
    # `_add_mode_flags`), so giving `grep` `-a` for prose would fork `-a`'s
    # meaning across the two search verbs — the same trap as the dropped `-n`.
    # One concept, one word: `--with-comments`.
    p.add_argument("--with-comments", action="store_true", help=help_text)


def _add_path_files_arg(p: argparse.ArgumentParser) -> None:
    """Add the rg/grep-style trailing PATH positionals.

    Resolved by `_load_sections`: each may be a .thy file (single
    theory), a directory containing a ROOT (theories per ROOT's
    `theories` clause), or a directory without (recursive *.thy glob).
    Results dedup'd by resolved path so `t/ archive/` doesn't double-
    count symlinked theories.
    """
    p.add_argument("files", nargs="*", metavar="PATH",
                   help="restrict search to specific .thy files or "
                        "directories (rg/grep-style trailing positionals); "
                        "a bare theory name resolves to its .thy, and `-` "
                        "reads a theory from stdin (e.g. `git show REF:FILE "
                        f"| {_prog_name()} grep PAT -`). "
                        "Directories with a ROOT are expanded via the "
                        "ROOT's `theories` clause; directories without are "
                        "walked recursively for `*.thy`.  Results are "
                        "dedup'd by resolved path, so `t/ archive/` does "
                        "not double-count symlinked theories.")


def _add_subject_list_arg(p: argparse.ArgumentParser, *, cmd: str,
                          dest: str = "name", metavar: str = "NAME",
                          noun: str = "entry name",
                          verb: str = "report each",
                          extra: str = "") -> None:
    """Shared one-or-more positional for every command that takes a list of
    subjects and processes them in turn — the lookup family
    (`show`/`callers`/`callees`, `deps`/`uses`) plus `find`.

    The list form is the load-bearing reason to prefer `query` over a shell
    loop: `query CMD A B C` does in one gate-free call what
    `for n in A B C; do query CMD $n` does in N gate-tripping ones.  Routing
    them all through this template keeps the shared part of their `--help`
    byte-identical (only `extra` carries the command-specific addendum), so
    the wording can't drift command-to-command.  The search family's *scope*
    positional is the separate `_add_path_files_arg`; subjects and paths
    never share a slot, which is what keeps the two families distinct.
    """
    help_text = (f"{noun}(s); pass multiple to {verb} in turn "
                 f"(blank-line separated), so `{cmd} A B C` replaces a "
                 f"gate-tripping `for n in A B C; do {cmd} $n` loop")
    if extra:
        help_text = f"{help_text}.  {extra}"
    p.add_argument(dest, nargs="+", metavar=metavar, help=help_text)


def _add_verbatim_flag(p: argparse.ArgumentParser) -> None:
    # `p` may be a parser or a mutually-exclusive group (both expose
    # add_argument), so `show` can pair this with `--statement` in one group.
    p.add_argument("-V", "--verbatim", action="store_true",
                   help="full source slice (statement + proof)")

def _add_statement_flag(p: argparse.ArgumentParser, *, help_text: str) -> None:
    # The statement slice (the declaration, not the proof) as a locus.  The
    # *meaning* differs by verb — `find` matches it, `show` renders it — so
    # the help text is per-verb, but the spelling (`--statement`, alias
    # `--stmt`, dest `statement`) is shared so it can't drift.
    p.add_argument("--statement", "--stmt", dest="statement",
                   action="store_true", help=help_text)

def _add_comment_flags(p: argparse.ArgumentParser) -> None:
    g = p.add_mutually_exclusive_group()
    g.add_argument("--no-comments", action="store_true",
                   help="suppress preamble and roadmap")
    g.add_argument("--comments-only", action="store_true",
                   help="show only preamble + roadmap")

def _add_context_flag(p: argparse.ArgumentParser, *, default: int = 2,
                      help_text: str = "") -> None:
    # One short flag for `--context` across every command that has it: `-U`
    # (the established spelling on the lookup family — theory/outline/find/
    # show).  `callers` routes through here too rather than declaring its own
    # `-C` inline: it is a lookup-family verb (it carries no PATH positionals),
    # so it should match its family, and rg's `-C` means context on *both*
    # sides whereas callers shows only trailing lines (rg's `-A`) — so `-C`
    # was a mis-aligned borrowing anyway.  Only the default differs per
    # command (preview wants 2, a caller listing wants 0), so it is a param.
    help_text = help_text or f"lines of preview / context (default {default})"
    p.add_argument("-U", "--context", type=int, default=default, metavar="N",
                   help=help_text)

def _add_reach_flag(p: argparse.ArgumentParser) -> None:
    # Scope citation attribution by what a theory can SEE.  A cited token is
    # resolved by NAME, and over one session that is right — everything there
    # sees everything the session declares.  Over a corpus it is not: the AFP
    # has two dozen lemmas spelled `mono`, and a site whose closure declares
    # none of them was reported as a caller of all of them.
    p.add_argument("--reach", choices=graph.REACH_MODES, default="closure",
                   help="attribute a citation only to declarations the citing "
                        "theory can see — itself or its transitive in-project "
                        "imports (default 'closure'); 'name' matches by name "
                        "alone, as before")


def _add_drop_names_flag(p: argparse.ArgumentParser) -> None:
    # Filter short citation names out of the call graph: a length-1 token
    # (`x`, `a`, `f`) is a term variable in nearly every proof, so by default
    # (L=1) single-char names are not graph nodes.  L=0 keeps them; L=2 also
    # drops 2-char names.  Method/keyword/numeral routing is independent.
    p.add_argument("--drop-names-upto", type=int, default=_DROP_NAMES_UPTO,
                   metavar="L",
                   help=f"exclude citation-graph names of length <= L "
                        f"(default {_DROP_NAMES_UPTO}: drop single-char "
                        f"variable collisions; 0 keeps all; 2 also drops "
                        f"2-char names)")


# -- Subcommand handlers (thin wrappers) -----------------------------------

def _scope_to_theories(ns: argparse.Namespace,
                       sections: list) -> list:
    """Narrow the loaded index to the theories named by ``--theory`` [theory-refs].

    Inert unless the subcommand opted in via :func:`_add_theory_scope_flag`, so
    this can sit on the shared spine.  The dest is ``theory_scope``, not
    ``theory``: ``deps`` / ``uses`` / ``refs`` already use ``theory`` for their
    positional subject, and one namespace attribute cannot be both.

    A name is resolved with the same `_resolve_theory` the theory-taking verbs
    use, so `--theory Foo`, `--theory Foo.thy` and a path all work.  An
    unresolvable one is reported and skipped rather than silently narrowing to
    nothing — "no matches" from a typo'd scope is the failure mode this whole
    tool exists to avoid.
    """
    wanted = getattr(ns, "theory_scope", None)
    if not wanted:
        return sections
    kept: list = []
    for name in wanted:
        sec = _resolve_theory(sections, name)
        if sec is None:
            print(f"{_prog_name()}: theory {name!r} not found", file=sys.stderr)
        elif sec not in kept:
            kept.append(sec)
    return kept


def _run_each(ns: argparse.Namespace, attr: str, fn) -> None:
    """Load sections once, then apply ``fn(sections, subject)`` to each subject
    in ``getattr(ns, attr)``, blank-line-separated — the shared spine of the
    list-taking subcommands (``deps``/``uses``/``find``/``show``/``callers``/
    ``callees``), so ``CMD A B C`` does in one gate-free call what a shell
    ``for`` loop does in N.
    """
    sections = _scope_to_theories(ns, _load_sections(ns))
    for i, subject in enumerate(getattr(ns, attr)):
        if i > 0:
            print()
        fn(sections, subject)


def _run_summary(ns: argparse.Namespace) -> None:
    cmd_summary(_load_sections(ns),
                by_session=getattr(ns, "by_session", False),
                verbose=getattr(ns, "verbose", False),
                totals_only=getattr(ns, "count", False))

def _run_theory(ns: argparse.Namespace) -> None:
    cmd_theory(_load_sections(ns), ns.name, _flags_from_ns(ns))

def _run_defs(ns: argparse.Namespace) -> None:
    cmd_defs(_load_sections(ns), ns.theory, _flags_from_ns(ns))

def _run_deps(ns: argparse.Namespace) -> None:
    _run_each(ns, "theory",
              lambda secs, thy: cmd_deps(secs, thy, recursive=ns.recursive))

def _run_theory_uses(ns: argparse.Namespace) -> None:
    _run_each(ns, "theory", lambda secs, thy:
              cmd_deps(secs, thy, reverse=True, recursive=ns.recursive))

def _run_graph(ns: argparse.Namespace) -> None:
    sections = _scope_to_theories(ns, _load_sections(ns))
    cmd_graph(sections, ns.kind, ns.format, _flags_from_ns(ns))

def _run_refs(ns: argparse.Namespace) -> None:
    flags = _flags_from_ns(ns)
    _run_each(ns, "theory", lambda secs, thy: cmd_refs(secs, thy, flags))

def _run_outline(ns: argparse.Namespace) -> None:
    cmd_outline(_load_sections(ns), ns.theory, _flags_from_ns(ns))

def _run_enclosing(ns: argparse.Namespace) -> None:
    # No PATH positionals: the FILE is baked into each FILE:LINE locus, so
    # load the full `-R`-scoped index and resolve each file token against it.
    mode = ("entry" if ns.entry else "blocks" if ns.blocks else "nearest")
    cmd_enclosing(_load_sections(ns), ns.locus, mode)

def _run_largest(ns: argparse.Namespace) -> None:
    # largest ranks *entries* by span — syntax-awareness is intrinsic.
    cmd_largest(_load_sections(ns, parse="syntax"), ns.top)

def _run_find(ns: argparse.Namespace) -> None:
    flags = _flags_from_ns(ns)
    if getattr(ns, "conjunction", False) and len(ns.pattern) > 1:
        # One report, not one per pattern, so `_run_each`'s blank-line
        # separation is exactly what must not happen here.
        sections = _scope_to_theories(ns, _load_sections(ns))
        cmd_find_and(sections, ns.pattern, flags)
        return
    _run_each(ns, "pattern", lambda secs, pat: cmd_find(secs, pat, flags))

def _run_show(ns: argparse.Namespace) -> None:
    flags = _flags_from_ns(ns)
    _run_each(ns, "name", lambda secs, n: cmd_show(secs, n, flags))

def _run_callers(ns: argparse.Namespace) -> None:
    flags = _flags_from_ns(ns)
    _run_each(ns, "name", lambda secs, n: cmd_callers(secs, n, flags))

def _run_callees(ns: argparse.Namespace) -> None:
    flags = _flags_from_ns(ns)
    _run_each(ns, "name", lambda secs, n: cmd_callees(secs, n, flags))

def _run_unused(ns: argparse.Namespace) -> None:
    cmd_unused(_load_sections(ns), _flags_from_ns(ns))

def _run_methods(ns: argparse.Namespace) -> None:
    cmd_methods(_load_sections(ns), ns.name, _flags_from_ns(ns))

def _run_instances(ns: argparse.Namespace) -> None:
    flags = _flags_from_ns(ns)
    _run_each(ns, "name", lambda secs, n: cmd_instances(secs, n, flags))

def _load_shape_config(ns: argparse.Namespace) -> 'shape.CorpusConfig | None':
    """Resolve the optional M3 corpus config for a shape command.

    ``--config PATH`` loads the TOML; ``--corpus NAME`` selects a table.  With a
    single-table file the corpus is inferred; with several a `--corpus` is
    required (fail-fast rather than pick one silently).  Returns ``None`` when no
    ``--config`` was given (the metric family runs config-free)."""
    path = getattr(ns, "config", None)
    if not path:
        return None
    configs = shape.load_corpus_config(path)
    corpus = getattr(ns, "corpus", None)
    if corpus is not None:
        if corpus not in configs:
            print(f"ERROR: no [{corpus}] table in {path} "
                  f"(have: {', '.join(sorted(configs)) or 'none'})",
                  file=sys.stderr)
            sys.exit(1)
        return configs[corpus]
    if len(configs) == 1:
        return next(iter(configs.values()))
    print(f"ERROR: {path} defines {len(configs)} corpora "
          f"({', '.join(sorted(configs))}); select one with --corpus",
          file=sys.stderr)
    sys.exit(1)


def _run_shape_summary(ns: argparse.Namespace) -> None:
    cmd_shape_summary(_load_sections(ns), as_json=ns.json,
                      scope=ns.scope, content=ns.content)

def _run_shape_steps(ns: argparse.Namespace) -> None:
    cmd_shape_steps(_load_sections(ns), span=ns.span, as_json=ns.json,
                    all_steps=ns.all, cfg=_load_shape_config(ns))

def _run_shape_lemma(ns: argparse.Namespace) -> None:
    cfg = _load_shape_config(ns)
    _run_each(ns, "name", lambda secs, n:
              cmd_shape_lemma(secs, n, as_json=ns.json, cfg=cfg))

def _run_shape_widest(ns: argparse.Namespace) -> None:
    # widest ranks *steps* by span/width — syntax-awareness is intrinsic, and it
    # takes trailing PATH positionals like `largest` (the search family).
    cmd_shape_widest(_load_sections(ns, parse="syntax"), top=ns.top,
                     metric=ns.metric, as_json=ns.json)

def _run_shape_census(ns: argparse.Namespace) -> None:
    """`census`: one process, one session at a time.

    There is no whole-corpus-at-once alternative, because measurement found no
    reason for one — analysis is the same work either way (within 0.03s over
    160 AFP entries) while peak memory stays flat at the largest single session
    instead of growing with the corpus (29 MB vs 315 MB at that size). Iterating
    also buys per-session error isolation, which loading everything cannot.

    The #7 contract has to be re-derived here, because "the index came back
    empty" is now a per-session event rather than a whole-run one:

    * **no session at all** — not an error by itself: a bare directory of
      `.thy` files has no ROOT and is still a corpus, so it becomes one unnamed
      group loaded by `load_index` (which raises #7's own diagnosis if the
      fallback glob finds nothing either — via `SystemExit`, a `BaseException`,
      so it passes through the per-session `except Exception` untouched rather
      than being logged as a skipped session).
    * **every session skipped** — nothing was measured and every attempt
      raised.  Silence plus exit 0 here is the corpus-scale version of the bug
      #7 fixed, so it is `_EXIT_BAD_ROOT`.
    * **some skipped** — the question WAS asked and mostly answered.  Exit 0,
      but say on stderr how many were lost, so a wrapper is never quietly given
      a short corpus.
    * **loaded but zero records** — an honest zero (a corpus of definitions has
      no proofs to measure), so exit 0 and stay silent.  The distinction from
      the case above is the whole point: `loaded` counts sessions that PARSED,
      not sessions that produced output.
    """
    root = active_t_dir()
    sessions = iter_sessions(root)
    if sessions:
        # One dedup set for the whole run, exactly as a whole-root load keeps
        # one: 47 AFP theories are referenced by two sessions (via a nested
        # ROOT), and a per-session set would emit each of them twice.
        seen: set[Path] = set()
        groups = ((s.name, (lambda s=s: sections_for_session(s, seen)))
                  for s in sessions)
    else:
        groups = [("", load_index)]
    out = cmd_shape_census(groups, resume=ns.resume)
    if out.loaded == 0:
        _fail_root(root, f"all {out.sessions} session(s) failed to load — "
                         f"no census records produced")
    if out.skipped:
        print(f"{_prog_name()}: census completed with {out.skipped} of {out.sessions} "
              f"session(s) skipped; {out.records:,} records from "
              f"{out.loaded} session(s)", file=sys.stderr)


def _run_grep(ns: argparse.Namespace) -> None:
    # grep is the one command where the parse mode is genuinely unclear
    # (live source vs. plain prose), so it infers per source.  It is also the
    # only search verb that honours a `PATH:A..B` line window (windows=True),
    # to scope a search to a hunk of a file that matches hundreds of times.
    cmd_grep(_load_sections(ns, parse="infer", windows=True), ns.pattern,
             _flags_from_ns(ns))

def _run_sorry(ns: argparse.Namespace) -> None:
    # sorry lists open goals in proofs — a theory concept; always syntax-aware.
    cmd_sorry(_load_sections(ns, parse="syntax"), getattr(ns, "count", False))

def _lines_file_and_ranges(tokens: list[str]) -> tuple[str, list[str]]:
    """Split `lines` positionals into ``(file_token, ranges)``.

    Two accepted spellings, detected by whether the first token parses as a
    ``FILE:RANGE`` locus:

      * ``FILE RANGE...``        — ``lines Foo 1..10 20..30``  (the original)
      * ``FILE:RANGE ...``       — ``lines Foo:1..10 Foo:20..30``

    The colon form is the `enclosing` / grep locus grammar reused, so a span
    printed elsewhere pastes straight in; its loci must name **one** file
    (`cmd_lines` reads a single source).  Exits with a clear error on a
    mixed or multi-file colon batch, or a bare ``FILE`` with no ranges.
    """
    if _parse_locus(tokens[0]) is not None:
        loci = []
        for t in tokens:
            parsed = _parse_locus(t)
            if parsed is None:
                print(f"ERROR: mixed `lines` forms — '{t}' is not FILE:RANGE",
                      file=sys.stderr)
                sys.exit(2)
            loci.append(parsed)
        files = {f for f, _, _ in loci}
        if len(files) > 1:
            print(f"ERROR: `lines` reads one file, got: "
                  f"{', '.join(sorted(files))}", file=sys.stderr)
            sys.exit(2)
        return loci[0][0], [
            (f"{lo}.." if hi is None else f"{lo}..{hi}") for _, lo, hi in loci]
    if len(tokens) < 2:
        print("ERROR: `lines` needs at least one RANGE "
              "(`FILE RANGE...` or `FILE:RANGE ...`)", file=sys.stderr)
        sys.exit(2)
    return tokens[0], tokens[1:]


def _run_lines(ns: argparse.Namespace) -> None:
    # lines is ignore-syntax: route the file token to its source through the
    # shared resolver (same `-`/path/name handling as the search family), then
    # hand the raw lines to cmd_lines.  `_lines_file_and_ranges` accepts both
    # the `FILE RANGE...` and colon-form `FILE:RANGE ...` spellings.
    file_token, ranges = _lines_file_and_ranges(ns.args)
    if file_token == _STDIN_SENTINEL:
        src = _stdin_source()
    else:
        src = _resolve_file_source(file_token,
                                   Path(file_token).expanduser().resolve(),
                                   load_index)
    cmd_lines(src.lines(), ranges)


# -- Parser construction ----------------------------------------------------

def _resolve_version() -> str:
    """The installed distribution version, read from package metadata.

    Single source of truth: the version lives only in `pyproject.toml` and is
    baked into the installed dist metadata at build/install time; we read it
    back here rather than duplicating a `__version__` literal that the release
    bump (and `make release`'s tomllib read) would then have to keep in sync.
    Caveat for editable installs: the metadata version reflects the last
    `pip install -e`, so it can lag the working tree even though the running
    code is live — the label is the installed version, not the checkout's.
    """
    from importlib.metadata import PackageNotFoundError, version
    try:
        return version("isabelle-query")
    except PackageNotFoundError:
        return "0+unknown (package not installed)"


class _VersionAction(argparse.Action):
    """Lazy `--version`.

    argparse's built-in `action="version"` wants a precomputed string, which
    would force the `importlib.metadata` import + dist-info scan on *every*
    `query` run.  Deferring it to `__call__` means only an actual
    `query --version` pays that cost — keeping the common path sub-100ms.
    """
    def __init__(self, option_strings, dest=argparse.SUPPRESS,
                 default=argparse.SUPPRESS,
                 help="show the version and exit"):
        super().__init__(option_strings=option_strings, dest=dest,
                         default=default, nargs=0, help=help)

    def __call__(self, parser, namespace, values, option_string=None):
        print(f"{_prog_name()} {_resolve_version()}")
        parser.exit()


def _add_root_flag(p: argparse.ArgumentParser, *, suppress_default: bool) -> None:
    """Attach the global ``-R/--root`` option to ``p``.

    Adding it to *every* (sub)parser — not only the top-level one — means it is
    documented in each subcommand's ``--help`` and accepted in either position:
    both ``query -R DIR methods`` and ``query methods -R DIR`` work.  Subparser
    copies pass ``default=SUPPRESS`` so that when ``-R`` is absent there they add
    nothing to the namespace, and so never clobber a value the top-level parser
    already resolved; the top-level copy keeps the real ``None`` default so the
    ``root`` attribute always exists.
    """
    kwargs = {"default": argparse.SUPPRESS} if suppress_default else {}
    p.add_argument(
        "-R", "--root", metavar="DIR",
        help="Isabelle session directory to query — the directory containing "
             "ROOT, or a parent of per-session ROOTs.  Overrides "
             "$ISABELLE_QUERY_ROOT, any .isabelle-query marker, and "
             "auto-discovery.  May appear before or after the subcommand.",
        **kwargs)


def _add_version_flag(p: argparse.ArgumentParser, *, short: bool) -> None:
    """Attach ``--version`` to ``p``, with the ``-V`` alias iff `short`.

    On every (sub)parser for the same reason as ``-R``: a user who has already
    typed a subcommand should not have to retype the line to ask which version
    they are running.  `_VersionAction` fires while the arguments are being
    read and exits, so it overrides whatever else is on the line — including a
    missing required positional — exactly as ``--help`` does.  It writes
    nothing to the namespace (dest/default are both SUPPRESS), so a subparser
    copy cannot clobber anything.

    ``-V`` is top-level only: on `show` / `find` it is the long-standing short
    form of ``--verbatim``, and silently repointing an existing flag at a
    different feature is worse than having the alias in one place.  The long
    ``--version`` is accepted everywhere, so nothing is unreachable.
    """
    names = ("-V", "--version") if short else ("--version",)
    p.add_argument(*names, action=_VersionAction)


def _build_parser() -> argparse.ArgumentParser:
    top = argparse.ArgumentParser(
        prog=_prog_name(),
        description="Query the theory index — computed live from .thy files.",
        formatter_class=argparse.RawDescriptionHelpFormatter)
    _add_root_flag(top, suppress_default=False)
    _add_version_flag(top, short=True)

    sub = top.add_subparsers(dest="command", title="commands")

    # summary
    p = sub.add_parser("summary",
                       help="theory overview table "
                            "(--by-session for a corpus/session aggregate)")
    p.add_argument("files", nargs="*",
                   help="theories or session directories to summarise "
                        "(default: the whole active session index)")
    p.add_argument("-S", "--by-session", action="store_true",
                   help="aggregate by session: one row per session plus a "
                        "grand total — for whole-corpus (AFP), multi-session "
                        "entry, or single-session runs, not one theory at a time")
    p.add_argument("-v", "--verbose", action="store_true",
                   help="with --by-session, expand each session to its "
                        "per-theory rows")
    _add_count_flag(p, "print only the grand totals (entries / lines / "
                       "theories / sessions), no table")
    p.set_defaults(func=_run_summary)

    # theory
    p = sub.add_parser("theory",
                       help="show all entries for a theory "
                            "(--names for a terse namespace listing)")
    p.add_argument("name", help="theory name")
    _add_names_flag(p, "list the theory's namespace entries terse "
                       "(name, tag, line; no bodies) — one per line")
    _add_count_flag(p, "just print the entry count")
    _add_verbatim_flag(p)
    _add_comment_flags(p)
    _add_context_flag(p)
    p.set_defaults(func=_run_theory)

    # defs
    p = sub.add_parser("defs",
                       help="list definitions in a theory "
                            "(--names for terse name listing)")
    p.add_argument("theory", help="theory name")
    _add_names_flag(p, "list definition names terse (name, tag, line)")
    _add_count_flag(p, "just print the definition count")
    p.set_defaults(func=_run_defs)

    # deps
    p = sub.add_parser("deps",
                       help="theories these import (direct; -r for "
                            "transitive); reverse is `uses`")
    _add_subject_list_arg(p, cmd="deps", dest="theory", metavar="THEORY",
                          noun="theory name or .thy path")
    p.add_argument("-r", "--recursive", action="store_true",
                   help="transitive closure (all indirect imports)")
    p.set_defaults(func=_run_deps)

    # uses (theory-level reverse of deps; brew's deps/uses convention)
    p = sub.add_parser("uses",
                       help="theories that import these (direct; -r for "
                            "transitive); reverse of `deps`")
    _add_subject_list_arg(p, cmd="uses", dest="theory", metavar="THEORY",
                          noun="theory name or .thy path")
    p.add_argument("-r", "--recursive", action="store_true",
                   help="transitive closure (all indirect importers)")
    p.set_defaults(func=_run_theory_uses)

    # graph (whole-graph serialisation for jq / Graphviz / external analysis)
    p = sub.add_parser("graph",
                       help="emit the whole citation or import graph as JSON "
                            "or DOT (for jq, Graphviz, external analysis)")
    p.add_argument("kind", nargs="?", default="citation",
                   choices=["citation", "imports"],
                   help="citation: entry names, from the call graph "
                        "(`callers`/`callees` one node at a time).  imports: "
                        "theories, from the `imports` clauses "
                        "(`deps`/`uses`).  Default: citation")
    p.add_argument("--format", "-f", default="json", choices=["json", "dot"],
                   help="json (default) or dot")
    _add_drop_names_flag(p)
    _add_reach_flag(p)
    _add_theory_scope_flag(p)
    p.set_defaults(func=_run_graph)

    # refs (citation-level rollup; the complement of `theory --names`, and
    # finer-grained than the imports-level `deps` / `uses`)
    p = sub.add_parser("refs",
                       help="names a theory cites, grouped by owning theory "
                            "(citation-level; `deps` is imports-level)")
    _add_subject_list_arg(p, cmd="refs", dest="theory", metavar="THEORY",
                          noun="theory name or .thy path")
    _add_count_flag(p, "just print the distinct referenced-name count")
    _add_names_flag(p, "bare referenced names, one per line, for piping "
                       "back into another query call")
    _add_drop_names_flag(p)
    p.add_argument("--external", action="store_true",
                   help="exclude names this theory declares itself, leaving "
                        "only what it takes from elsewhere (same sense as "
                        "`callees --external`)")
    _add_reach_flag(p)
    p.set_defaults(func=_run_refs)

    # outline
    p = sub.add_parser("outline", help="section structure with entries")
    p.add_argument("theory", help="theory name")
    _add_comment_flags(p)
    _add_context_flag(p)
    p.set_defaults(func=_run_outline)

    # enclosing (alias: at) — the inverse of outline: name the entry that
    # owns a FILE:LINE locus, for the build-chase loop "which lemma is at
    # line N".  Lookup-family (no PATH positionals; the FILE is in the locus).
    p = sub.add_parser("enclosing", aliases=["at"],
                       help="name the entry (and nearest proof block) that "
                            "owns each FILE:LINE locus (or every entry a "
                            "FILE:A..B range touches; inverse of outline, "
                            "for build-failure triage)")
    p.add_argument("locus", nargs="+", metavar="FILE:LINE",
                   help="one or more loci, each `FILE:LINE` (e.g. Foo.thy:42 "
                        "or, by bare theory name, Foo:42) or `FILE:A..B` for "
                        "a line range (e.g. Foo:8..12 — lists every entry the "
                        "range overlaps, the `lines`-style `A..B` grammar; the "
                        "open `Foo:8..` runs to the theory's end, `Foo:..12` "
                        "from its start). "
                        "Pass several to resolve them all in one gate-free "
                        "call, so a batch of build-failure loci needs no "
                        "per-line shell loop.  FILE resolves like "
                        "outline/show — a .thy path or a bare theory name — "
                        "and is scoped by the global -R/--root.")
    g = p.add_mutually_exclusive_group()
    g.add_argument("-e", "--entry", action="store_true",
                   help="report only the owning entry (the outermost block), "
                        "with no proof-internal drill-down")
    g.add_argument("-b", "--blocks", action="store_true",
                   help="report the full nesting path: the entry, then every "
                        "enclosing proof block from outermost to innermost "
                        "(default is the innermost block only)")
    p.set_defaults(func=_run_enclosing)

    # largest
    p = sub.add_parser("largest", help="top N largest entries by span")
    p.add_argument("-N", "--top", type=int, default=20, metavar="N",
                   help="number of entries to show (default 20)")
    _add_path_files_arg(p)  # trailing .thy/dir/name positionals -> union scope
    p.set_defaults(func=_run_largest)

    # find
    p = sub.add_parser("find", help="find entries by name (regex; "
                                    "--statement to match the statement)")
    _add_subject_list_arg(p, cmd="find", dest="pattern", metavar="PATTERN",
                          noun="regex pattern", verb="run each search",
                          extra="matching is case-insensitive; an Isabelle "
                                "name may be pasted as printed "
                                "(`split\\<^sub>i`)")
    _add_mode_flags(p)
    _add_verbatim_flag(p)
    _add_statement_flag(
        p, help_text="match the pattern within each entry's statement slice "
                     "(the declaration, not the proof) instead of its name — "
                     "a token-level `find_theorems`")
    _add_comment_flags(p)
    _add_context_flag(p)
    _add_with_comments_flag(p)
    _add_theory_scope_flag(p)
    # No `-A` short flag, for the same reason `--names` has no `-n`: `-A` is
    # grep's after-context, and squatting on it would silently change what a
    # grep-reflex caller asked for.  `--and` is spelled out.  The dest is
    # `conjunction` because `and` is a Python keyword — `ns.and` will not
    # parse, and a dest nobody can write is a trap for the next handler.
    p.add_argument("--and", dest="conjunction", action="store_true",
                   help="keep only entries matched by EVERY pattern, reported "
                        "once (default: one search per pattern, an OR).  The "
                        "find_theorems-shaped query: `find --statement --and "
                        "length encode_entry`")
    p.set_defaults(func=_run_find)

    # show
    p = sub.add_parser("show", help="show one or more specific entries")
    _add_subject_list_arg(p, cmd="show",
                          extra="each name is matched exact-then-substring")
    _add_mode_flags(p)
    # `-V` (full slice) and `--statement` (declaration only) are opposite
    # ends of the slice spectrum, so they can't be combined.
    slice_group = p.add_mutually_exclusive_group()
    _add_verbatim_flag(slice_group)
    _add_statement_flag(
        slice_group, help_text="render only the statement slice (the "
                               "declaration, without the proof)")
    _add_comment_flags(p)
    _add_context_flag(p)
    p.set_defaults(func=_run_show)

    # callers
    p = sub.add_parser("callers", help="find proof-body usages")
    _add_subject_list_arg(
        p, cmd="callers",
        extra="\"who calls X\" is corpus-global, so there are no trailing "
              "PATH positionals: scope with the global -R/--root, or cut by "
              "theory boundary with --external")
    _add_count_flag(p)
    p.add_argument("-r", "--recursive", action="store_true",
                   help="transitive closure (all indirect callers)")
    _add_names_flag(p)
    _add_drop_names_flag(p)
    _add_context_flag(p, default=0,
                      help_text="show N trailing lines after each match "
                                "(useful for multi-line `[where ..., OF ...]` "
                                "invocations whose argument list spans 2-3 "
                                "lines; default 0)")
    p.add_argument("--external", action="store_true",
                   help="exclude callers inside the theory that defines "
                        "NAME (e.g. when auditing whether anything outside "
                        "a given theory uses its primitives, that theory's "
                        "own internal cross-references are noise).  Only "
                        "affects the non-recursive form; "
                        "transitive closure via -r ignores this flag.")
    _add_reach_flag(p)
    p.set_defaults(func=_run_callers)

    # callees
    p = sub.add_parser("callees",
                       help="entries this entry references; reverse is "
                            "`callers`")
    _add_subject_list_arg(p, cmd="callees")
    _add_count_flag(p)
    _add_names_flag(p)
    _add_drop_names_flag(p)
    p.add_argument("-r", "--recursive", action="store_true",
                   help="transitive closure (all indirect callees)")
    p.add_argument("--external", action="store_true",
                   help="exclude callees defined in NAME's own theory, "
                        "leaving only cross-theory dependencies (mirror of "
                        "`callers --external`).  Only affects the "
                        "non-recursive form; transitive closure via -r "
                        "ignores this flag.")
    _add_reach_flag(p)
    p.set_defaults(func=_run_callees)

    # grep
    p = sub.add_parser("grep",
                       help="regex search across live theory source "
                            "(a PATH may carry a `:A..B` line window)")
    p.add_argument("pattern",
                   help="regex pattern (Python syntax; `\\|` rewritten to `|` "
                        "for shell-grep compatibility, and Isabelle markup "
                        "`\\<^sub>` taken literally)")
    _add_path_files_arg(p)
    # grep alone honours a `PATH:A..B` (or `PATH:LINE`) line window on a
    # trailing positional — `query grep PAT Foo.thy:100..200` searches only
    # lines 100-200, the "this token matches hundreds of times, I want one
    # region" case.  Resolved in `_load_sections(windows=True)`; the shared
    # `_add_path_files_arg` help stays window-agnostic (largest/sorry, which
    # also use it, do not accept a window).
    _add_with_comments_flag(p)
    _add_count_flag(p)
    _add_names_flag(p, "locations + owning entry only "
                       "(skip the matched line text)")
    _add_line_number_noop_flag(p)
    p.set_defaults(func=_run_grep)

    # sorry — located open-goal listing (grep specialised to the sorry token)
    p = sub.add_parser("sorry",
                       help="list open goals: every live `sorry` with its "
                            "location + owning entry")
    _add_path_files_arg(p)
    _add_count_flag(p, "just print the count (build-summary form)")
    # `sorry` is grep specialised to one token, so it draws the same reflex.
    _add_line_number_noop_flag(p)
    p.set_defaults(func=_run_sorry)

    # lines
    p = sub.add_parser("lines",
                       help="print line ranges of FILE with `NR| CONTENT` "
                            "prefix (sandbox-friendly alternative to awk loops)")
    p.add_argument("args", nargs="+", metavar="FILE-or-RANGE",
                   help="either `FILE RANGE...` (`lines Foo 1..10 20..30`) or "
                        "colon-form `FILE:RANGE ...` loci sharing one file "
                        "(`lines Foo:1..10 Foo:20..30`) — the same `FILE:A..B` "
                        "grammar `enclosing` uses, so a span printed elsewhere "
                        "pastes straight in.  FILE is any text file, a bare "
                        "theory name (resolved to its .thy, like outline/show), "
                        f"or `-` for stdin (`git show REF:FILE | {_prog_name()} "
                        "lines - A..B`).  Each RANGE is `A..B` (inclusive), `A`, or "
                        "open-ended `A..` (to EOF) / `..B` (from line 1); "
                        "multiple ranges are `--`-separated in the output.")
    p.set_defaults(func=_run_lines)

    p = sub.add_parser("unused", help="list entries with zero callers")
    _add_count_flag(p)
    p.add_argument("-r", "--recursive", action="store_true",
                   help="cascade: include entries whose callers are all unused")
    p.add_argument("--by-theory", action="store_true",
                   help="group by theory with line counts")
    p.add_argument("--roots", action="store_true",
                   help="forest summary: each root with exclusive subtree size")
    p.add_argument("--keep", action="append", metavar="NAME[,NAME...]",
                   help="treat these names as live roots (never flag as "
                        "unused, and stop the cascade at them).  Repeatable, "
                        "or pass a comma-separated list.  Use for AFP-headline "
                        "theorems and other intentional zero-caller entries.")
    _add_drop_names_flag(p)
    _add_reach_flag(p)
    p.set_defaults(func=_run_unused)

    # methods (alias: method) — proof-method usage; complement of the call
    # graph.  Scopes to a corpus via the global `-R` (e.g. `-R afp/thys`).
    p = sub.add_parser("methods", aliases=["method"],
                       help="proof-method usage tally; `methods NAME` "
                            "(e.g. `methods simp`) lists that method's uses")
    p.add_argument("name", nargs="?", default=None, metavar="NAME",
                   help="a proof method (e.g. simp, auto, induct); omit for "
                        "the ranked tally of every method used")
    _add_mode_flags(p)
    p.set_defaults(func=_run_methods)

    # instances — where a locale / class is instantiated.  A lookup-family
    # verb (subject list, no PATH positionals) that reports DECLARED SOURCE
    # sites: the complement of Isar's `print_interps`, which needs a running
    # prover and shows the processed interpretations, including those an
    # imported session installed.  No `--reach`: a site is scoped by what its
    # theory can see, always, since an `interpretation L` in a theory that
    # cannot see L's declaration interprets a different L.
    p = sub.add_parser("instances",
                       help="where a locale or class is instantiated "
                            "(instantiation / instance / interpretation / "
                            "sublocale)")
    _add_subject_list_arg(
        p, cmd="instances", noun="locale or class name",
        extra="Reports the DECLARED SOURCE sites, which is the complement of "
              "Isar's `print_interps`: that needs a running prover and shows "
              "the processed interpretations, including those an imported "
              "session installed")
    _add_count_flag(p, "just print the site count")
    _add_names_flag(p, "bare `THEORY:LINE` loci, one per line, for piping "
                       "into `enclosing`")
    p.add_argument("-r", "--recursive", action="store_true",
                   help="also the sites of every class or locale that extends "
                        "NAME, transitively (`class X = NAME + ...`, "
                        "`subclass`, `instance X \\<subseteq> NAME`, "
                        "`sublocale`).  Adds a VIA column naming, per row, "
                        "which of them the site writes -- `nat` instantiates "
                        "`comm_monoid_diff`, never `ab_semigroup_add` by "
                        "name.")
    _add_sorts_flag(p)
    p.set_defaults(func=_run_instances)

    # shape — proof-shape metrics.  Unlike every other verb this is a *nested*
    # subcommand group (`shape summary|steps|lemma|widest|census`): the five
    # views share the one step-scanner engine but differ in shape (aggregate
    # table vs per-step stream vs ranked list vs batch census), so a flat verb
    # with mode flags would blur them.  Each nested parser sets its own `func`;
    # bare `query shape` falls back to the group's help.
    wp = sub.add_parser("shape",
                        help="proof-shape metrics "
                             "(summary|steps|lemma|widest|census)")
    wsub = wp.add_subparsers(dest="shape_command", title="shape commands")

    # shape summary
    sp = wsub.add_parser("summary", help="per-theory shape aggregate table")
    _add_shape_json_flag(sp, "emit one per-proof JSONL record per line instead "
                             "of the table")
    sp.add_argument("--scope", choices=("proof", "entry"), default="proof",
                    help="size column region: the proof body (default) or the "
                         "whole entry incl. statement (as `largest` counts)")
    sp.add_argument("--content", choices=("all", "code", "prose"), default="all",
                    help="size column content: all lines (default), code only "
                         "(prose stripped — the shared text/comment set), or "
                         "prose only")
    sp.set_defaults(func=_run_shape_summary)

    # shape steps
    sp = wsub.add_parser(
        "steps",
        help="per-step shape records, optionally scoped to a THEORY or "
             "THEORY:A..B locus")
    sp.add_argument("span", nargs="?", metavar="SPAN",
                    help="optional scope: a bare THEORY name, or a "
                         "THEORY:A..B / THEORY:LINE locus (the same grammar "
                         "`enclosing` / `lines` use, so a span pastes straight "
                         "in)")
    sp.add_argument("-a", "--all", action="store_true",
                    help="include non-goal steps (context / plumbing / "
                         "closing); the default shows goal steps only, where "
                         "the shape metrics attach")
    _add_shape_json_flag(sp, "emit one per-step JSONL record per line")
    _add_shape_config_flags(sp)
    sp.set_defaults(func=_run_shape_steps)

    # shape lemma (lookup family: subject-list of lemma names)
    sp = wsub.add_parser(
        "lemma",
        help="full per-step shape view of one proof, its aggregate footer, "
             "and its M6 extension curve")
    _add_subject_list_arg(sp, cmd="shape lemma",
                          extra="each name is matched exact-then-substring")
    _add_shape_json_flag(sp, "emit one per-step JSONL record per line "
                             "(every step of the lemma)")
    _add_shape_config_flags(sp)
    sp.set_defaults(func=_run_shape_lemma)

    # shape widest (search family: trailing PATH positionals)
    sp = wsub.add_parser(
        "widest",
        help="the N widest steps by a chosen metric (the step analogue of "
             "`largest`)")
    sp.add_argument("-N", "--top", type=int, default=20, metavar="N",
                    help="number of steps to show (default 20)")
    sp.add_argument("--metric", choices=("w2", "w1", "fanin", "live"),
                    default="w2", metavar="METRIC",
                    help="ranking metric: w2 as-written token width (default), "
                         "w1 free variables, fanin cited facts, live "
                         "simultaneously-live facts")
    _add_shape_json_flag(sp, "emit the ranked steps as JSONL")
    _add_path_files_arg(sp)
    sp.set_defaults(func=_run_shape_widest)

    # shape census
    sp = wsub.add_parser(
        "census",
        help="stream one per-proof JSONL record per entry (whole-AFP "
             "distribution run; streaming + resumable)",
        description=(
            "Stream one per-proof JSONL record per entry over a corpus "
            "(whole-AFP distribution run; streaming + resumable).  Runs one "
            "SESSION at a time in a single process: memory stays bounded by "
            "the largest single session rather than the corpus, a session that "
            "fails to parse is reported on stderr and skipped instead of "
            "aborting the run, and the interpreter startup a per-entry shell "
            "loop pays ~1,000 times is paid once.  Every record carries its "
            "`session`.  Proof tokens "
            "are classified with a fixed, committed APPROXIMATE method table — "
            "the union of the distribution sessions most AFP entries build on "
            "(HOL, HOL-Library, HOL-Analysis, HOL-Eisbach, HOL-Decision_Procs) — "
            "so it needs no Isabelle and regenerates identically anywhere.  "
            "Methods an entry defines itself (e.g. an Eisbach `cs_concl`) or from "
            "a niche logic (Nominal's `nominal_induct`, HOLCF) are not in the "
            "table, so the automation axis (trivial_frac, method_kinds) "
            "under-counts on those steps — a few % of proofs, only in "
            "method-defining entries; fan-in and width are unaffected.  A more "
            "precise per-session census is in progress."))
    sp.add_argument("--resume", metavar="FILE",
                    help="skip entries already present in FILE (a prior census "
                         "JSONL), so `census -R AFP/thys --resume out.jsonl >> "
                         "out.jsonl` picks up a killed run where it stopped")
    sp.set_defaults(func=_run_shape_census)

    # bare `query shape` -> the group's help (no subcommand chosen).
    wp.set_defaults(func=lambda ns: wp.print_help())

    # Surface the global -R on every subcommand (and the nested shape verbs) so it
    # is discoverable in each `<cmd> -h` and accepted after the subcommand too, not
    # only before it.  Driving this off the subparser registry means a future verb
    # is covered automatically.  set() dedupes parsers shared by aliases
    # (methods/method, enclosing/at) — adding -R twice to one parser conflicts.
    for subp in set(sub.choices.values()):
        _add_root_flag(subp, suppress_default=True)
        _add_version_flag(subp, short=False)
    for subp in set(wsub.choices.values()):
        _add_root_flag(subp, suppress_default=True)
        _add_version_flag(subp, short=False)

    return top


def _add_shape_json_flag(p: argparse.ArgumentParser, help_text: str) -> None:
    # `--json` on the shape family switches a human view to its JSONL record
    # stream — the join contract (stable (theory, lemma, line) keys).  Its own
    # helper so the wording stays uniform across the four views that emit it.
    p.add_argument("--json", action="store_true", help=help_text)


def _add_shape_config_flags(p: argparse.ArgumentParser) -> None:
    # The optional M3 corpus config, shared by the record-emitting shape views
    # (`steps`, `lemma`).  Supplying it adds the frame_ratio columns; without
    # it the family runs config-free.  Resolved by `_load_shape_config`.
    p.add_argument("--config", metavar="TOML",
                   help="M3 corpus config (TOML, one [corpus] table per entry); "
                        "adds the frame_ratio / frame_mentioned / frame_changed "
                        "columns to the JSON where a step shows a configuration "
                        "signal")
    p.add_argument("--corpus", metavar="NAME",
                   help="select the [NAME] table from --config (required when "
                        "the file defines more than one corpus)")


# Subcommands that actually consult the method/attribute table: the call graph's
# reject-set (`callers`/`callees`/`unused`), the method census (`methods`), and
# shape's identifier classifier (`shape`).  EVERY other verb — find, grep,
# enclosing, summary, theory, outline, show, lines, largest, deps, uses, sorry —
# is a pure text/structure query that never touches the table, so it must not pay
# any namespace-resolution cost: no cache read, and above all no cache-miss
# Isabelle dump.  This is what keeps the 99% use case (`query find …`, `query grep
# …`) unconditionally pure and sub-100ms, even right after an Isabelle upgrade.
_NAMESPACE_COMMANDS = frozenset({"callers", "callees", "unused",
                                 "methods", "method", "shape"})


def _configure_namespace(ns: argparse.Namespace) -> None:
    """Bind the router's method/attribute table for this run, at **dispatch**.

    This is the one call that lets `query` track the *installed* Isabelle instead
    of the committed static scan.  It runs after argument parsing and before the
    command handler — never at import — so import stays spawn-free and every
    direct-call test keeps the committed table (nothing in the suite reaches
    `main()`).  On the warm path it is a cache read (~ms); on a cache-miss it is
    a one-off Isabelle dump (the purity-model call for this tool); with no
    Isabelle it returns the committed table.

    **Gated to the verbs that use the table** (`_NAMESPACE_COMMANDS`): the pure
    text/structure verbs (find/grep/enclosing/summary/…) return immediately, so
    they never resolve and never risk a cache-miss dump — the common case stays
    unconditionally pure.

    **Session-exact resolution.**  The table verbs resolve the project *as built*:
    the union of the dumped tables of the sessions its ROOT declares that have a
    built heap (:func:`_namespace_resolve.resolve_project`).  Each session dump is
    self-complete (its transitive deps included), so no logic base is injected — a
    Nominal session carries its own ``eqvt``, a Pure-only session keeps its own
    ``auto`` rather than being handed HOL's.

    **Committed fallback (no heap / no Isabelle — the common case here).**  When
    nothing resolves, the router binds a *committed* table chosen by the project's
    base logic (:func:`_bind_committed_fallback`): a HOL-base project takes the
    broad census union (``_census_namespace``) — the very table ``shape census``
    binds — so an interactive ``shape`` verb's method-kind / automation
    classification **matches the census** instead of the impoverished Pure floor
    (which knows ``simp``/``rule`` but not ``auto``/``blast``/``induct``).  Only a
    genuinely non-HOL project is stepped *down* to the minimal Pure floor and
    **warned**, since the HOL union would mis-assert its methods there.  Fan-in
    and width are
    position-based and identical across tables; the fallback only moves the
    name-looked-up method-kind axis (measured: on a real HOL project, fan-in Δ=0,
    method-kind histogram shifts materially).

    ``shape census`` is special: a whole-corpus run spans many logics with no
    single session to resolve against, and its output ships in ``data/`` so it
    must regenerate identically with **no Isabelle**.  So it binds the committed
    *broad* census table (the HOL-family union, ``_census_namespace``) — fixed and
    reproducible, and unlike the minimal Pure default it carries the automation
    methods (``auto``/``blast``/``induct``) the census's automation axis keys on.
    This binding is unconditional (independent of ``$ISABELLE_QUERY_NAMESPACE`` and
    of which heaps are built), so a census is reproducible everywhere; see
    ``_census_namespace`` for why a union is the correct table for the census axes.

    For the other table verbs, pin the committed table with
    ``$ISABELLE_QUERY_NAMESPACE=committed`` (a pure short-circuit — the import-time
    default already *is* it, so this resolves nothing and spawns nothing).  Note
    the table it pins is the **broad union**, not the Pure floor: the import-time
    default was moved onto the union so a library caller gets the same table a CLI
    caller does (see ``graph``'s namespace block and ``[library-table]``), and this
    short-circuit inherits it.  A non-HOL project that wants the floor should say
    so with :func:`graph.use_pure_namespace`, since the env var no longer implies
    it.  Any resolution failure degrades silently to that default: binding the
    namespace must never break a query.
    """
    if (getattr(ns, "command", None) == "shape"
            and getattr(ns, "shape_command", None) == "census"):
        _bind_census_namespace()  # fixed broad union; reproducible; see docstring
        return
    if os.environ.get("ISABELLE_QUERY_NAMESPACE", "auto").lower() == "committed":
        return
    if getattr(ns, "command", None) not in _NAMESPACE_COMMANDS:
        return  # a pure text/structure query — never resolve, never spawn
    try:
        sess_infos = list(iter_sessions(active_t_dir()))
        # The project's ROOT dirs make its sessions known to `ML_process -l`: a
        # project/AFP session is not resolvable by name alone unless its ROOT
        # directory is on the dump's search path (without this the dump fails and
        # every non-distribution session silently degrades to the Pure fallback).
        dirs = sorted({str(s.root_path.parent) for s in sess_infos})
        r = _ns.resolve_project([s.name for s in sess_infos], dirs=dirs)
        if r["source"] == "committed":
            _bind_committed_fallback(sess_infos)   # broad-for-HOL / Pure+warn
        else:
            graph.configure_namespace(r["methods"], r["attributes"],
                                      _isa_ns.KEYWORDS)
    except Exception:                                   # noqa: BLE001
        pass  # keep the import-time committed default; never fail a query here


def _bind_census_namespace() -> None:
    """Bind the committed broad census table (``_census_namespace``).  Fixed and
    reproducible: no Isabelle, no cache, no dependence on which heaps are built.

    Used both by ``shape census`` (which must regenerate identically anywhere) and,
    via :func:`_bind_committed_fallback`, as the *interactive* fallback for a
    HOL-base project with no built heap — so the two paths bind the **same** table
    and agree on the method-kind / automation axis.

    It is also the **import-time default** (:func:`graph.use_census_namespace`), so
    on the census path this is now a re-bind rather than a change.  It is kept
    explicit rather than left implicit: the census must bind its table on purpose,
    not inherit whatever a default happens to be."""
    graph.use_census_namespace()


def _use_broad_fallback(sess_infos) -> bool:
    """Whether the broad HOL census table is a sound committed fallback here.

    HOL is Isabelle's default logic and the broad table is the sensible floor, so
    the answer is yes UNLESS some declared session **positively** resolves to a
    known non-HOL logic (:func:`~isabelle_layout.distribution.is_known_nonhol_base` —
    ``ZF``/``FOL``/``Pure``/…), where the HOL union would mis-assert.  Note the
    default is the *opposite* of the census guard's `is_hol_base`: an *unknown*
    base — e.g. an out-of-scope parent *session* name reached under
    ``-R <sub-session>`` (``ae`` → ``Multitape_TM_Substrate``, whose own ``= HOL``
    is not in scope) — is treated as HOL, not vetoed.  Empty project → broad (HOL
    default; nothing identifies it as non-HOL)."""
    parents = {s.name: (s.parent or "") for s in sess_infos}
    return not any(is_known_nonhol_base(resolve_base_logic(s.name, parents))
                   for s in sess_infos)


def _bind_committed_fallback(sess_infos) -> None:
    """Pick the committed table when no session heap resolves.

    Broad-fallback project (:func:`_use_broad_fallback`) → the broad census union
    (:func:`_bind_census_namespace`), so an interactive ``shape`` verb matches
    ``shape census`` and knows ``auto``/``blast``/``induct``.  A positively non-HOL
    project → the minimal Pure floor, and warn, since the HOL union would
    mis-assert this logic's methods.

    The non-HOL branch **binds** the floor rather than assuming it: the union is
    the import-time default now, so "leave it alone" would silently hand a ZF
    project HOL's method table — which is the very thing the warning describes."""
    if _use_broad_fallback(sess_infos):
        _bind_census_namespace()              # broad HOL union — matches the census
    else:
        graph.use_pure_namespace()            # step *down* off the broad default
        _warn_committed_fallback(sess_infos)  # …and say so


def _warn_committed_fallback(sess_infos) -> None:
    """Warn that a **non-HOL** project fell back to the minimal Pure table: no heap
    resolved and its base logic is not HOL, so neither the committed HOL census
    table nor a heap dump applies.  Silent for a Pure-only project (the floor is
    exact) or when no session is declared.  Names each declared session's parent
    heap.  Deliberately does *not* claim "spurious citations": fan-in and width are
    position-based and unaffected — it is the method-kind / automation
    classification that degrades on the impoverished floor."""
    nonpure = sorted({s.parent for s in sess_infos
                      if s.parent and s.parent != "Pure"})
    if not nonpure:
        return
    print(f"{_prog_name()}: no built heap for this project and its base logic "
          f"({', '.join(nonpure)}) is not HOL, so the committed HOL namespace "
          f"table does not apply — using the minimal Pure table. Fan-in and width "
          f"are unaffected; method-kind / automation classification may be "
          f"approximate. Build the session heap or install Isabelle for exact "
          f"results.", file=sys.stderr)


def main():
    global _ROOT_OVERRIDE
    parser = _build_parser()
    ns = parser.parse_args()
    if ns.root:
        # Checked here, before any command runs, because an explicit -R is an
        # assertion by the caller: they said this is a root, so if it is not
        # one that is an error rather than an empty answer.  (A root reached by
        # cwd discovery is still checked, but only once the index comes back
        # empty — see load_index.)
        root = Path(ns.root).expanduser()
        if not root.exists():
            _fail_root(root, "no such directory (given to -R/--root)")
        if not root.is_dir():
            _fail_root(root, "not a directory (given to -R/--root)")
        _ROOT_OVERRIDE = root.resolve()
    if not hasattr(ns, "func"):
        parser.print_help()
        sys.exit(1)
    _configure_namespace(ns)
    try:
        ns.func(ns)
    except BrokenPipeError:
        # A downstream reader closed the pipe — `shape census | head`, `grep
        # ... | less` quit early.  Not an error in this program: a streaming
        # command should die quietly, like any Unix filter.
        #
        # Point fd 1 at /dev/null rather than closing stdout.  The interpreter
        # flushes stdout again during shutdown, and that second flush is what
        # prints the notorious "Exception ignored while flushing sys.stdout";
        # giving it a writable fd is what silences it.  Closing instead does
        # not work — `sys.stdout` and `sys.__stdout__` are the same object, so
        # closing one leaves nothing to redirect.
        os.dup2(os.open(os.devnull, os.O_WRONLY), sys.stdout.fileno())
        sys.exit(_EXIT_SIGPIPE)


if __name__ == "__main__":
    main()
