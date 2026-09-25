"""Core data model — the dataclasses and shared tag families every layer reads.

The bottom of the ``isabelle_query`` module DAG
(``model → parsing → graph → render → commands → cli``): pure data with no
dependency on any other package module, so every layer above can import it
without risking a cycle.

* :class:`Entry` / :class:`TheorySection` / :class:`CallGraph` — the parsed
  representation of a theory tree (populated by ``parsing``, consumed
  everywhere).
* :class:`CmdFlags` — the uniform flag bundle threaded from the CLI into each
  command function.
* The tag frozensets (:data:`_DEFINITION_TAGS`, :data:`_CITABLE_TAGS`) and the
  call-graph short-name floor (:data:`_DROP_NAMES_UPTO`) — membership lists
  named once here so they can't drift between the call sites that share them.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path


def _blank_spans(line: str, spans: list[tuple[int, int]]) -> str:
    """`line` with each half-open ``[lo, hi)`` column span replaced by spaces.

    Length-preserving by construction — every removed character is replaced by
    exactly one space — which is the whole contract of
    :meth:`TheorySection.live_source`: a column index into the result addresses
    the same character it addressed in the original.

    `spans` arrive sorted and disjoint (the tokenizer emits them as regions
    close, left to right), but the clamping here is written not to rely on it.
    """
    out: list[str] = []
    prev = 0
    for lo, hi in spans:
        lo, hi = max(lo, prev), min(hi, len(line))
        if hi <= lo:
            continue
        out.append(line[prev:lo])
        out.append(" " * (hi - lo))
        prev = hi
    out.append(line[prev:])
    return "".join(out)


def blank_all(lines: list[str],
              spans_by_line: dict[int, list[tuple[int, int]]]) -> list[str]:
    """`lines` with every span in `spans_by_line` (1-indexed) replaced by
    spaces — the shared body of `live_source` / `outer_source`.

    Returns the input list itself when there is nothing to blank, so the common
    case costs no copy.  Lives here rather than in `parsing` because `model` is
    the bottom of the DAG: `parsing` needs the same operation while building a
    section, and a second copy of it is a second thing to keep in step.
    """
    if not spans_by_line:
        return lines
    out = list(lines)
    for line_no, spans in spans_by_line.items():
        if 1 <= line_no <= len(out):
            out[line_no - 1] = _blank_spans(out[line_no - 1], spans)
    return out


@dataclass
class Entry:
    tag: str            # DEF, FUN, LEMMA, THEOREM, DATATYPE, TYPE, RECORD, AXIOM
    name: str           # identifier
    text: str           # legacy pre-formatted text (for `theory` dump)
    theory: str = ""
    thy_line: int = 0       # 1-indexed start line in the .thy source file
    decl_end_line: int = 0  # 1-indexed last line of the declaration
                            # (last header line before proof / blank / next decl)
    proof_line: int = 0     # 1-indexed first line of the proof (0 if no proof)
    thy_end: int = 0        # 1-indexed end of this entry's span: the line
                            # before the *next* entry's src_start (its leading
                            # `text` preamble, if any, else its declaration) or
                            # the next section.  Includes this entry's trailing
                            # blank lines but NOT the following entry's leading
                            # doc block — that block documents, and belongs to,
                            # the following entry (see src_start).  For a safe
                            # relocation cut use body_end_line (which also drops
                            # the trailing blanks).
    body_end_line: int = 0  # 1-indexed last line that belongs to this entry's
                            # body (the closing `qed`, the terminating `by` /
                            # `.`, or for declarations the last header line).
                            # Stops before any trailing inter-lemma `text` /
                            # `\<comment>` block.  Safe cut boundary for
                            # `bin/move-block.py`.
    # Comment context attached during _parse_one:
    preamble: tuple[int, int] | None = None
        # (start, end) of the `text \<open>...\<close>` block immediately
        # preceding this entry, if one exists within ~3 blank lines.
    annotations: list[tuple[int, str, str]] = field(default_factory=list)
        # (line_no, content, kind) for every `\<comment> \<open>...\<close>`
        # marginal note inside this entry's span [thy_line .. thy_end], tagged
        # by WHERE in the entry it sits — see `_ANNOTATION_KINDS`.
        #
        # These notes are the author's prose about this entry, and an entry is
        # decl line + statement + proof, so the note's position is what says
        # which of the three it is talking about.  Only `proof` notes used to
        # be kept; that dropped ~74% of the corpus's marginal notes, and for a
        # `definition` — which has no proof at all — it dropped every one, so
        # the feature could never say anything about a definition.  The tag is
        # carried rather than flattened away because the display decision (show
        # which kinds, under what heading) is still open, and tagging is the
        # reversible choice.
        #
        # Notes OUTSIDE any entry's span are still unowned: theory-level prose
        # above the first declaration, and the `end \<comment> \<open>Context
        # of ...\<close>` notes that close a locale (134 of 3,912 over 120 AFP
        # entries).  The blocker on the latter is gone — `blocks` below now
        # models locale structure, so the closing `end` has an owner to name —
        # but they still attach to nothing, because an annotation's owner is
        # an Entry and a block is not one.
    bindings: list[tuple[str, str]] = field(default_factory=list)
        # (name, kind) for every ADDITIONAL name this one declaration binds —
        # see `_BINDING_KINDS`.  Isabelle binds more than one name per command
        # and `query` records one, so without these each is a `find` that
        # misses, a `show` that says "No entries matching", and — worse than a
        # miss — a `callers` that reports the name's own declaration as a
        # citation of itself, since `_def_sites` can only exclude a
        # declaration site it knows about.
        #
        # Deliberately NOT separate Entries: all of these are bound by a
        # single command with a single span, so splitting them would inflate
        # entry counts, triple-count one `fun f and g and h` under `largest`,
        # and give `enclosing` several equally-valid owners for one line.
        # Resolution happens at the command boundary instead.
        #
        # The kind is carried rather than flattened away for the same reason
        # `annotations` carries one: an introduction rule is not a conjunct is
        # not a mutually-declared constant, the display decision is still
        # open, and tagging is the reversible choice.
    blocks: tuple[tuple[str, str], ...] = ()
        # (kind, name) for each NAMED target block lexically enclosing this
        # entry, outermost first — `(("locale", "hpk"),)` for a lemma inside
        # `locale hpk ... begin`.  The theory's own block is excluded (every
        # entry is in it, so it carries no information), as are anonymous
        # blocks (`notepad`, `context fixes x`), which have nothing to report
        # even though they still nest.
    in_target: str = ""
        # The `(in foo)` modifier written on this declaration itself.  It is
        # NOT the same evidence as `blocks`: lexical nesting says where the
        # text sits, `(in foo)` says where the declaration goes regardless of
        # where it sits, and Isabelle lets the two disagree.  Both are kept;
        # `target` below decides.

    @property
    def target(self) -> str:
        """The locale / class this entry actually belongs to, '' if none.

        An explicit ``(in foo)`` wins over lexical nesting because that is
        what Isabelle does — the modifier *retargets* the declaration, so a
        `lemma (in bar)` written inside `locale foo` belongs to `bar`.
        Otherwise the innermost enclosing named block."""
        if self.in_target:
            return self.in_target
        return self.blocks[-1][1] if self.blocks else ""

    @property
    def bound_names(self) -> list[str]:
        """Just the names from :attr:`bindings`, for the many callers that
        only ask "does this declaration bind NAME?" and not which kind."""
        return [n for n, _ in self.bindings]

    @property
    def roadmap(self) -> list[tuple[int, str]]:
        """The proof-tagged annotations, in the pre-`annotations` shape.

        A *roadmap* is the narration of a derivation, so it is exactly the
        subset of :attr:`annotations` that sits at or below ``proof_line``.
        Kept as a derived view rather than a second field: there is one place
        notes are attached, and no way for the two to drift.
        """
        return [(ln, content) for ln, content, kind in self.annotations
                if kind == "proof"]

    @property
    def src_start(self) -> int:
        """First line of this entry's span: the leading `text` preamble's
        start if one is attached, else the declaration line.  The preamble
        documents THIS entry, so it counts as part of this entry's extent
        (and is excluded from the preceding entry's `thy_end`)."""
        return self.preamble[0] if self.preamble else self.thy_line

    @property
    def line_count(self) -> int:
        """Inclusive source-span length [src_start..thy_end]; 0 if unplaced."""
        return self.thy_end - self.src_start + 1 if self.thy_line > 0 else 0


@dataclass
class TheorySection:
    theory: str
    path: Path
    entries: list[Entry]
    thy_lines: int = 0
    outline: list[tuple[str, str, int]] = field(default_factory=list)
    text_blocks: list[tuple[int, int]] = field(default_factory=list)
        # All top-level text blocks in the theory, used for `outline` rendering
        # (per-entry preambles are stored on Entry.preamble).
    heading_spans: list[tuple[int, int]] = field(default_factory=list)
        # `chapter`/`section`/`subsection`/`subsubsection` cartouches, including
        # the ones that wrap onto further lines.
        #
        # Kept SEPARATE from text_blocks, which it otherwise resembles, because
        # the two are wanted in different places.  Both are prose and belong in
        # `graph._noise_spans` — a heading reading "Consequences proved using
        # helper" was creating a real citation edge to `helper`, so a lemma
        # mentioned only in a heading looked used and left `unused`.  But
        # text_blocks also feeds `_attach_preambles`, and a heading is not the
        # next declaration's docstring: it belongs to the section, and folding it
        # in would silently give a docstring to every entry that happens to sit
        # under one.  One notion per consumer, rather than one list doing both.
    comment_ranges: list[tuple[int, int]] = field(default_factory=list)
        # Multi-line ranges for `\<comment> \<open>...\<close>` annotations.
        # NOT part of `_noise_spans` any more: these notes usually trail live
        # proof text, and marking the whole line dropped the step with the
        # note.  The tokenizer reports the same regions by column, so
        # `nonisar_ranges`/`nonisar_spans` cover them properly; this stays as
        # the span-boundary belt-and-braces (it also catches a `\<comment>`
        # with no cartouche, which the tokenizer does not match).
        # (Distinct from comment_lines, which records first-line content for the
        # roadmap-attachment feature.)
    nonisar_ranges: list[tuple[int, int]] = field(default_factory=list)
        # Lines holding no live Isar text: `(* ... *)` comments (which nest),
        # `\<^cancel>` regions, `\<comment>` marginal notes, legacy `{* ... *}`
        # verbatim, and ML bodies.
        # Lexical, not grammatical — see `parsing.extract_nonisar_ranges`.
        # Folded into `_noise_spans` (so no scan reads them as proof text), into
        # the span-boundary mask (so a commented-out `end` does not cut the
        # declaration above it), and into the declaration scan (so a
        # commented-out `definition` does not mint an entry).
    nonisar_spans: dict[int, list[tuple[int, int]]] = field(default_factory=dict)
        # The same regions at CHARACTER granularity: {line_no: [(lo, hi)]},
        # half-open columns, sparse (absent line = nothing to redact).  The
        # superset `nonisar_ranges` is derived from — a line appears there only
        # when its spans cover every non-blank character, whereas a line that
        # merely ENDS in a comment appears only here.  Consumed by
        # `live_source`.
    inner_spans: dict[int, list[tuple[int, int]]] = field(default_factory=dict)
        # Everything that is NOT outer syntax, at character granularity:
        # `nonisar_spans` PLUS the `"..."` terms and live cartouches that scan
        # deliberately keeps.  Consumed by `outer_source`.
        #
        # A superset of `nonisar_spans`, and the two are not redundant: a term
        # is live Isar that a citation scan must read, and simultaneously not a
        # place a COMMAND can start.  Which of the two a caller wants depends on
        # the question — "what does this proof cite" wants live_source, "where
        # does this command begin" wants outer_source.
    is_thy: bool = True
        # False for a non-`.thy` path passed as a trailing grep positional
        # (e.g. `query grep PAT notes.md`).  Such a section is parsed
        # *plainly* (no entries, outline, text/comment blocks): the Isabelle
        # entry-grammar does not apply to Markdown / prose, so cmd_grep treats
        # it as plain `grep` — every matched line, no synthesised owning-entry
        # label, no live/comment classification.
    session: str | None = None
        # The Isabelle *session* this theory was declared by (the `session
        # NAME` in the owning ROOT), attached when loaded via a ROOT walk
        # (`_sections_from_dir`); None for a single-file / stdin / bare-glob
        # load with no owning session.  A theory reached through several
        # sessions is attributed to the first that references it (matching
        # the build's own first-declaration-wins dedup).  Consumed by
        # `summary --by-session` to roll theory-level counts up to the
        # session / corpus level.
    line_window: tuple[int, int | None] | None = None
        # Optional inclusive 1-indexed [lo, hi] line window from a grep
        # `PATH:A..B` positional, set by `_load_sections(windows=True)`.
        # `_grep_sections` skips lines outside it; commands that don't read
        # it (largest/sorry) never see a window (the suffix isn't parsed for
        # them, so `largest Foo:1..9` errors rather than silently ignoring).
    _source_cache: list[str] | None = None
    _live_cache: list[str] | None = None
    _outer_cache: list[str] | None = None

    def source(self) -> list[str]:
        if self._source_cache is None:
            self._source_cache = self.path.read_text().splitlines()
        return self._source_cache

    def live_source(self) -> list[str]:
        r"""The source with every non-Isar *character* replaced by a space.

        Same number of lines, and each line the same length, so a line number
        and a column index mean exactly what they mean in :meth:`source`: a
        scanner switches to this view and changes nothing else — its regexes,
        its 1-indexed arithmetic and its line masks all still hold.

        This is what lets `by (simp add: foo) (* not bar *)` drop `bar` while
        keeping `foo`.  Whole-line skipping cannot: it has only the choice
        between keeping both and losing both, and losing a true citation is the
        worse and quieter error.

        Redacts only what `parsing`'s tokenizer reports — comments (which
        nest), ``\<^cancel>`` regions, ``\<comment>`` marginal notes, legacy
        ``{* ... *}`` verbatim and ML bodies.  A ``"..."`` term and a bare
        cartouche are deliberately NOT redacted: they hold inner syntax, so the
        `mono` in ``lemma "mono f"`` is a real citation.  ``text`` blocks and
        per-entry preambles are not redacted either — those are introduced by a
        command rather than by a lexical marker, so callers keep masking them
        at line level through `graph._noise_spans`.

        `source()` stays authoritative for display: a caller that shows a
        matched line must print the real one, or it would show blanks where
        the user's comment is.
        """
        if self._live_cache is None:
            self._live_cache = blank_all(self.source(), self.nonisar_spans)
        return self._live_cache

    def outer_source(self) -> list[str]:
        r"""The source with everything that is not OUTER SYNTAX blanked.

        Same shape contract as :meth:`live_source` — line count and every
        column preserved — but a stricter view: `live_source` keeps ``"..."``
        terms and cartouches because they hold citable names, while this blanks
        them too, because a term is not a place a command can start.

        This is what "command position" means in Isar, and it is the thing the
        declaration grammar has been approximating with a column-0 anchor.  The
        anchor is a proxy for the same idea and a poor one: Isar is
        whitespace-insensitive, so an author who indents a theory body drops out
        of the index entirely, while a `lemma` written inside a term would be
        read as a declaration if the anchor ever moved.  Asking the tokenizer
        removes both errors at once, since it already tracks the states that
        decide it.

        Empty `inner_spans` means the section was parsed without
        ``want_inner``; the result then equals `source()`, which is WRONG for
        this purpose rather than merely unhelpful, so populate them.
        """
        if self._outer_cache is None:
            self._outer_cache = blank_all(self.source(), self.inner_spans)
        return self._outer_cache

    def slice(self, start: int, end: int) -> list[str]:
        """Return 1-indexed inclusive line range from the .thy source."""
        lines = self.source()
        s = max(0, start - 1)
        e = min(len(lines), end)
        return lines[s:e]


@dataclass
class CallGraph:
    """Name-level dependency graph built by a single pass over all sources."""
    callers: dict[str, set[str]]   # callee_name → {caller entry names}
    callees: dict[str, set[str]]   # caller_name → {callee names referenced}
    all_names: set[str]            # universe of indexed entry names


# Tag families shared across commands.  Named so the membership lists can't
# drift between call sites: definition-like exports vs the citation-graph-
# eligible kinds (the two sets genuinely differ — datatypes/records/types are
# definitions but never call-graph nodes; lemmas/theorems are the reverse).
_DEFINITION_TAGS = frozenset(
    {"DEF", "ABBREV", "FUN", "DATATYPE", "RECORD", "TYPE"})

# The three parts of an entry a marginal note can be talking about, in source
# order.  An entry is: the declaration line, then its statement, then (for a
# fact) its proof — so a note's line number relative to `thy_line` and
# `proof_line` decides the tag, with no text inspection at all.
#
#   decl       on the declaration line itself — a gloss on the whole entry
#              (`type_synonym hash = ... \<comment> \<open>Type of hashes\<close>`)
#   statement  below the declaration, above the proof: what is being stated.
#              For an entry with NO proof (a `definition`'s body, a `fun`'s
#              equations) this is everything below the declaration line, which
#              is right — such an entry is all statement.
#   proof      at or below `proof_line`: how it is derived.  This is the
#              historical `Entry.roadmap`.
#
# Ordered, so a display can iterate them in the order they appear in source.
_ANNOTATION_KINDS = ("decl", "statement", "proof")
_CITABLE_TAGS = frozenset({"LEMMA", "THEOREM", "FUN", "DEF", "ABBREV"})

# The kinds of extra name an `Entry` may bind (see `Entry.bindings`), each with
# the phrasing a command uses to explain the resolution to the reader.  They
# differ in what the name IS, which is why the tag is kept:
#   conjunct  a named conjunct of a multi-`shows` lemma — `shows a: "P" and
#             b: "Q"` binds `a` and `b` as facts alongside the whole.
#   rule      a named introduction rule — `inductive p where r1: "..."` binds
#             `r1` as the fact that IS how `p` gets cited.
#   sibling   a constant declared in the same command — `fun f and g` declares
#             two constants, mutually recursive, over one termination proof.
_BINDING_KINDS = {
    "conjunct": "a named conjunct of",
    "rule": "an introduction rule of",
    "sibling": "declared together with",
    "constructor": "a constructor of",
    "discriminator": "a discriminator of",
    "selector": "a selector of",
    "field": "a field of",
    "assumption": "an assumption of",
    "definition": "a defined element of",
    "note": "a named fact of",
}


# Default short-name floor for the citation graph: a length-1 token (`x`, `a`,
# the wildcard `_`) is a bound variable in nearly every proof, so by default
# single-char names are not citation nodes.  Overridden per-invocation via
# ``--drop-names-upto`` (see ``graph._is_citation_name``).
_DROP_NAMES_UPTO = 1


@dataclass
class CmdFlags:
    """Uniform flag bundle passed to command functions."""
    mode: str = "first"          # first / all / count / names
    verbatim: bool = False       # -V / --verbatim
    statement: bool = False      # --statement / --stmt
                                 # find: match the statement slice (input);
                                 # show: render only the statement slice (output)
    comments: str = "on"         # on / off / only
    context: int = 2             # -U N / --context N
    with_comments: bool = False  # --with-comments (find + grep: search prose)
    recursive: bool = False      # -r / --recursive
    by_theory: bool = False      # --by-theory (unused)
    roots: bool = False          # --roots (unused)
    keep: frozenset[str] = frozenset()  # --keep (unused: live roots)
    external: bool = False       # --external (callers: skip defining theory)
    drop_names_upto: int = _DROP_NAMES_UPTO  # --drop-names-upto (call graph)
    # --reach: "closure" attributes a citation only to declarations the citing
    # theory can SEE; "name" is the old name-only matching, kept so a
    # corpus-scale delta can be measured against the numbers it replaces.
    reach: str = "closure"
    # --sorts (instances / codeqs): re-spell the name cell as `c :: T` with
    # the sort / arity / signature the SOURCE writes at that site.  Written
    # text only — a site whose source writes none shows none.
    sorts: bool = False
