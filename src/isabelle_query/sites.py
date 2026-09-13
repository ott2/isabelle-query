r"""Sites — where a name is used in a particular SYNTACTIC ROLE.

The layer after ``graph`` (above ``model`` / ``parsing`` / ``graph``, below
``render`` / ``commands``).  Two scans, both the shape of
``commands._find_callers`` and under the same doctrine — the LIVE view only, so
a commented-out or ``\<^cancel>``ed decoy is not a site, and a command word is
recognised where a COMMAND can start rather than wherever the word appears:

* **instantiations of a locale / class** — ``instantiation`` blocks,
  ``instance`` arities, ``interpretation`` / ``global_interpretation`` /
  ``interpret``, and ``sublocale`` (:func:`find_instantiations`);
* **code equations of a constant** — declarations carrying a ``code``
  attribute, the ``declare`` / ``lemmas`` sites that attach one to an existing
  fact, and the implicit default equations of the constant's own
  ``definition`` / ``fun`` (:func:`find_code_equations`).

What this is NOT: ``print_interps`` / ``print_codesetup`` / ``code_thms``.
Those run inside a prover and report the PROCESSED setup — after
preprocessing, after ``[code del]`` has taken effect, and including everything
an imported session declared.  This reports the DECLARED SOURCE SITES in the
project being read, which is the complement: it needs no heap and no build,
and it sees the sites a processed view has already folded away.

Both scans read a command in two views at once.  ``outer_source`` decides
STRUCTURE (a ``+`` inside a quoted term is not a locale-expression separator;
a ``::`` inside a term is not an arity's) and ``live_source`` supplies NAMES,
because a quoted name — ``instantiation "fun" :: ...``,
``:: "{order_bot, ...}"`` — lives exactly where the outer view blanks.  The two
views are line- and column-preserving, so an index found in one indexes the
other.  Both grammars are the rails from Isabelle's own ``Doc/Isar_Ref``,
quoted at each parser.

Rendering and the CLI contract (subject resolution, the exit statuses) live in
``commands`` next to the other lookup verbs; this module only finds.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

from isabelle_query.graph import site_filter
from isabelle_query.model import TheorySection
from isabelle_query.parsing import (
    ISA_MARKUP,
    QUOTED_NAME_RE,
    RESERVED_NAME_PREFIXES,
    TAG_MAP,
    _LEADING_CMD_RE,
    _NOT_A_TARGET_NAME,
    _SPAN_BOUNDARY_COMMANDS,
    _TARGET_NAME_RE,
    _balanced_end,
    _block_stacks,
)


# ---------------------------------------------------------------------------
# What a site is
# ---------------------------------------------------------------------------

# What a row says it IS, when the source does not say.  `?` is the parser's own
# placeholder for a declaration that carries no name, so a site with nothing
# written to call it by is spelled the same way rather than blank or invented.
UNNAMED = "?"


@dataclass
class Site:
    """One row: a line where ``kind`` names the subject.

    ``kind`` is the syntactic role — what makes this line a site.  ``name`` is
    what the row is called: the qualifier / type constructor / providing fact
    the SOURCE writes at that site, in the column `callers` puts its owning
    entry in.  ``sorts`` is the sort or signature text written THERE and
    nowhere else — shown only under ``--sorts``, because for most rows there
    is none and a column of blanks is worse than no column.

    ``path`` is the section's path as stored, which is the key
    ``render.locus_labels`` is keyed by and therefore the only thing from
    which the printed locus may be made: a theory NAME is not a section's
    identity, and on a corpus where two theories share one the label is
    exactly what tells them apart [disambig-loci].  ``theory`` is the bare
    declared name, a display key only.
    """
    theory: str
    path: Path
    line: int
    kind: str
    text: str
    name: str = UNNAMED
    sorts: str = ""

    def label(self, with_sorts: bool) -> str:
        """The name cell: ``c :: T`` under ``--sorts`` when a sort is written,
        the bare name otherwise — never an inferred type."""
        if with_sorts and self.sorts:
            return f"{self.name} :: {self.sorts}"
        return self.name


# Which declarations may be the subject of each verb.  The CLI refuses
# anything else (exit 1).
LOCALE_TAGS = frozenset({"LOCALE", "CLASS"})
CONSTANT_TAGS = frozenset({"DEF", "FUN", "ABBREV", "IND", "INDSET",
                           "DATATYPE", "RECORD", "AXIOM"})

# Which declaration commands register DEFAULT code equations with no attribute
# written: `definition` registers its defining equation and `fun` / `primrec`
# / `function` their `.simps` / `.code`.  `datatype` registers CONSTRUCTORS
# (`code_datatype`), not equations; `inductive` needs an explicit `code_pred`;
# an `abbreviation` is unfolded before code generation ever sees it — none of
# the three has default equations to report.
DEFAULT_CODE_TAGS = frozenset({"DEF", "FUN"})


# ---------------------------------------------------------------------------
# Reading a command header
# ---------------------------------------------------------------------------

# How many lines of a command header are read.  A locale expression or an
# arity is one or two lines in practice; the cap stops a malformed file from
# turning one site into a whole-theory scan.
HEADER_LINES = 8

# Where a header stops: the first outer-syntax token that cannot be part of
# the expression any more.  `where` / `rewrites` / `defines` / `for` end a
# locale expression by the rail; `begin` ends an `instantiation` head; the
# rest are the proof.
_HEADER_STOP_RE = re.compile(
    r"(?<![\w'])(where|rewrites|defines|for|begin|by|proof|using|unfolding"
    r"|apply|done|qed|oops|sorry)(?![\w'])|(?<=\s)\.\.?(?=\s|$)")

# The commands that BOUND a header: the parser's own boundary table plus the
# declaration keywords, rather than a second list — one grammar, one place it
# is written down.
_BOUNDARY_WORDS = (_SPAN_BOUNDARY_COMMANDS | frozenset(TAG_MAP) | frozenset({
    "global_interpretation", "interpret", "subclass", "instance",
    "text", "txt", "text_raw", "chapter", "section", "subsection",
    "subsubsection", "paragraph", "subparagraph",
}))


def _starts_command(outer_line: str) -> bool:
    m = _LEADING_CMD_RE.match(outer_line.lstrip())
    return m is not None and m.group(1) in _BOUNDARY_WORDS


def _header_at(live: list[str], outer: list[str], line: int,
               lines: int = HEADER_LINES) -> tuple[str, str]:
    """The command starting at 1-indexed ``line``, as ``(live, outer)`` text.

    Up to ``lines`` lines, joined with newlines from lines of identical length
    in both views, stopping early at a later line that opens a command of its
    own (read on the OUTER view: a command word inside a term is not a
    command) and cut at the first ``_HEADER_STOP_RE`` token.
    """
    last = min(line + lines - 1, len(live))
    live_parts: list[str] = []
    outer_parts: list[str] = []
    i = line
    while i <= last:
        if i > line and _starts_command(outer[i - 1]):
            break
        live_parts.append(live[i - 1])
        outer_parts.append(outer[i - 1])
        i += 1
    outer_text = "\n".join(outer_parts)
    m = _HEADER_STOP_RE.search(outer_text)
    cut = m.start() if m else len(outer_text)
    return "\n".join(live_parts)[:cut], outer_text[:cut]


# ---------------------------------------------------------------------------
# Reading a name
# ---------------------------------------------------------------------------

def _name_at(live: str, pos: int) -> tuple[str, int] | None:
    """An Isabelle name as written at a USE site, starting at ``pos``:
    ``(name, index past it)``, or None.

    Quoted when the word would otherwise be reserved (``"fun"``, ``"and"``),
    symbol-bearing, and — unlike a declaration name — possibly qualified
    (``Groups.monoid``).  Exactly the block scanner's target-name grammar,
    through the same two patterns, so a name it reads is a name this reads.
    """
    if pos >= len(live):
        return None
    rest = live[pos:]
    mq = QUOTED_NAME_RE.match(rest)
    if mq:
        return mq.group(1), pos + mq.end()
    m = _TARGET_NAME_RE.match(rest)
    if not m:
        return None
    nm = m.group(0)
    if nm in _NOT_A_TARGET_NAME or nm.startswith(RESERVED_NAME_PREFIXES):
        return None
    return nm, pos + m.end()


def denotes(written: str, subject: str) -> bool:
    """A written name denotes the subject when it is the subject or a
    QUALIFIED spelling of it (``Groups.monoid`` for ``monoid``).  Isabelle
    resolves a qualified name to the same locale, so refusing the spelling
    would drop real sites; requiring the last segment to match keeps
    ``foo_monoid`` out."""
    return written == subject or written.endswith("." + subject)


def _skip_space(s: str, i: int) -> int:
    n = len(s)
    while i < n and s[i] in " \n":
        i += 1
    return i


def _paren_end(outer: str, start: int) -> int:
    """Index just past the ``)`` matching the ``(`` at ``start``, or -1."""
    depth = 0
    for i in range(start, len(outer)):
        c = outer[i]
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return i + 1
    return -1


def _squash(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


# ---------------------------------------------------------------------------
# Instantiations
# ---------------------------------------------------------------------------

# The commands this verb reads, and the rails they follow
# (`Doc/Isar_Ref/Spec.thy`):
#
#   instantiation (name + and) '::' arity 'begin'
#   instance (() | (name + and) '::' arity | name ('<'|'\<subseteq>') name)
#   interpretation locale_expr
#   interpret locale_expr
#   global_interpretation locale_expr definitions?
#   sublocale (name ('<'|'\<subseteq>'))? locale_expr definitions?
#
# `locale_expr` is `(instance + '+') for_fixes`, an instance being
# `(qualifier ':')? name (pos_insts | named_insts) rewrites?`.
#
# DELIBERATELY EXCLUDED, both directions of the class/locale hierarchy:
# `class D = C + ...`, `locale K = L + ...`, `subclass`, and
# `instance C \<subseteq> D`.  Those EXTEND a locale rather than instantiate
# it — no type or term is supplied.  They are the EDGES the transitive form
# walks (`extends_edges`), which is why the two relations have to stay
# separate HERE: `instances L` answers "which types and terms were supplied
# to L, by name", and the answer is a set of lines each of which writes `L`;
# `instances L -r` answers "and to anything that IS an L", whose answer names
# L nowhere.  A listing that folded the second into the first would have no
# spelling left for the first, and its count would depend on how the
# hierarchy was factored rather than on what the project instantiates.
_INST_CMD_RE = re.compile(
    r"^(instantiation|instance|interpretation|global_interpretation|interpret"
    r"|sublocale)(?![\w'])")

# A name as WRITTEN at a use site — `_TARGET_NAME_RE`'s grammar, spelled out
# so it can be embedded in a longer pattern.
_USE_NAME = rf"(?:{ISA_MARKUP}|[A-Za-z_])(?:{ISA_MARKUP}|[\w'.])*"

# `sublocale L \<subseteq> M` (and the older `sublocale L < M`): the NAME
# before the arrow is where the interpretation is installed, not what is
# interpreted, so it is stripped before the expression is read.  The decoded
# `⊆` is accepted too, because a buffer handed over from an editor may be
# decoded text.
_SUBLOCALE_TARGET_RE = re.compile(
    rf"^\s*(?:{_USE_NAME})?\s*(?:\\<subseteq>|{re.escape('⊆')}|<)\s*")

# A qualifier (`add:`, `weak?:`, and the quoted `"and":`) prefixes an
# instance and is not the locale.  Matched on the OUTER view, where a quoted
# qualifier has been blanked to spaces — so the `:` is still there and the
# name behind it cannot be mistaken for the head.  It stops AT the colon and
# does not eat the whitespace after it: in outer a quoted locale name IS
# whitespace, so a trailing `\s*` walked straight past the name in
# `interpretation q: "open" id` and read `id` instead.
_QUALIFIER_RE = re.compile(r"^\s*(?:[A-Za-z_][\w'.]*)?\s*[?!]?\s*:(?!:)")

# A command may carry a document marker before its arguments
# (`instantiation\<^marker>\<open>tag unimportant\<close> vec :: ...`).  It is
# part of the COMMAND, and the outer view blanks only the cartouche, so the
# `\<^marker>` token is still standing where the type constructor is read.
_MARKER_RE = re.compile(r"^\s*\\<\^marker>\s*")


def _marker_end(live: str) -> int:
    m = _MARKER_RE.match(live)
    if not m:
        return 0
    if live.startswith("\\<open>", m.end()):
        e = _balanced_end(live, "\\<open>", "\\<close>", start=m.end())
        return m.end() if e < 0 else e
    return m.end()


def _split_plus(outer: str) -> list[tuple[int, int]]:
    """Half-open spans between top-level ``+`` — not inside brackets, and
    not inside a term (terms are already blanked in the outer view)."""
    out: list[tuple[int, int]] = []
    depth = 0
    start = 0
    for i, c in enumerate(outer):
        if c in "([":
            depth += 1
        elif c in ")]":
            depth -= 1
        elif c == "+" and depth <= 0:
            out.append((start, i))
            start = i + 1
    out.append((start, len(outer)))
    return out


def _qualifier_name(live: str, a: int, b: int) -> str:
    """The qualifier as WRITTEN, read off ``live`` from the span the pattern
    matched on ``outer`` — `interpretation "and": L ..` writes it quoted, and
    outer blanks exactly that.  The `?` / `!` marker is not part of it."""
    q = live[min(a, len(live)):min(b, len(live))].strip()
    if q.endswith(":"):
        q = q[:-1].rstrip()
    if q.endswith(("?", "!")):
        q = q[:-1].rstrip()
    nm = _name_at(q.lstrip(), 0)
    return nm[0] if nm else ""


def expression_instances(live: str, outer: str) -> list[tuple[str, str]]:
    """Every instance of a locale expression as ``(written qualifier, locale)``.

    The qualifier belongs to the instance, not to the command: in
    ``interpretation L1 x + q: L2 y`` only the second instance is named, and
    a row that reported ``q`` for both would be naming the wrong one.
    """
    out: list[tuple[str, str]] = []
    for a, b in _split_plus(outer):
        m = _QUALIFIER_RE.match(outer[a:b])
        skip = m.end() if m else 0
        qualifier = _qualifier_name(live, a, a + skip) if skip else ""
        pos = _skip_space(live, a + skip)
        if pos < b:
            nm = _name_at(live, pos)
            if nm:
                out.append((qualifier, nm[0]))
    return out


def expression_heads(live: str, outer: str) -> list[str]:
    """Every locale named at the head of an instance of this expression."""
    return [loc for _q, loc in expression_instances(live, outer)]


def arity_classes(live: str, outer: str) -> list[str]:
    """The classes an arity instantiates: the SORT after ``::``, past the
    argument sorts.

    ``instantiation prod :: (exhaustive, exhaustive) exhaustive`` instantiates
    ``exhaustive`` once — the sorts in parentheses are CONSTRAINTS on the
    arguments, not instantiations.  A sort is a class or a brace-list of them,
    and both are routinely written quoted, which is why it is read from live:
    whitespace is skipped on LIVE (a quoted sort is blanked in outer) while
    the parentheses are matched on OUTER (a quoted argument sort cannot hide
    one there).
    """
    sep = outer.find("::")
    if sep < 0:
        return []
    pos = _skip_space(live, sep + 2)
    if pos < len(outer) and outer[pos] == "(":
        e = _paren_end(outer, pos)
        if e < 0:
            return []
        pos = _skip_space(live, e)
    if pos >= len(live):
        return []
    c = live[pos]
    if c == '"':
        e = live.find('"', pos + 1)
        body = "" if e < 0 else live[pos + 1:e]
    elif c == "{":
        e = live.find("}", pos + 1)
        body = "" if e < 0 else live[pos + 1:e]
    elif live.startswith("\\<open>", pos):
        e = _balanced_end(live, "\\<open>", "\\<close>", start=pos)
        body = "" if e < 0 else live[pos + 7:e - 8]
    else:
        nm = _name_at(live, pos)
        body = nm[0] if nm else ""
    inner = body.strip().removeprefix("{").removesuffix("}")
    out: list[str] = []
    for part in inner.split(","):
        part = part.strip()
        if not part:
            continue
        nm = _name_at(part, 0)
        if nm:
            out.append(nm[0])
    return out


def arity_parts(live: str, outer: str) -> tuple[str, str]:
    """An arity as the source writes it, split at the ``::``: the type
    constructor being instantiated, and the arity text after it.

    Both halves VERBATIM (whitespace squashed, because a header may wrap):
    ``--sorts`` promises the constraints as they appear in source, so a quoted
    brace sort stays quoted.  The constructor is unquoted when it is a single
    quoted name (``instantiation "fun" :: ...`` instantiates ``fun``) and
    otherwise left alone — ``nat and int :: mynull`` names two, and picking
    one would be a guess.
    """
    sep = outer.find("::")
    if sep < 0:
        return "", ""
    raw = _squash(live[:min(sep, len(live))])
    nm = _name_at(raw, 0)
    ctor = nm[0] if nm and not raw[nm[1]:].strip() else raw
    return ctor, _squash(live[min(sep + 2, len(live)):])


def _sublocale_target(live: str, outer: str) -> str:
    r"""The ``L`` of ``sublocale L \<subseteq> M``: where the interpretation is
    INSTALLED, the same thing an enclosing ``context L begin`` says in the
    other spelling.  The arrow is found on outer; the name is read on live,
    because it may be quoted."""
    if not _SUBLOCALE_TARGET_RE.match(outer):
        return ""
    nm = _name_at(live, _skip_space(live, 0))
    return nm[0] if nm else ""


def _enclosing_lookup(sec: TheorySection, live: list[str],
                      outer: list[str]):
    """``line -> the name of what encloses it``: the enclosing entry (an
    ``interpret`` in a proof), else the innermost named target block (a bare
    ``interpretation`` inside ``locale holder begin``), else ``""``.

    The block stack is built at most once per section, and only for a
    section that actually asks: it is another pass over the source, and most
    theories never need it.
    """
    stacks: list | None = None

    def lookup(line: int) -> str:
        # `commands._enclosing_entry`'s rule, restated because this module
        # sits below `commands`: the entry whose [src_start, thy_end] span
        # contains the line.
        for e in sec.entries:
            if e.thy_line and e.thy_end and e.src_start <= line <= e.thy_end:
                if e.name and e.name != UNNAMED:
                    return e.name
                break
        nonlocal stacks
        if stacks is None:
            stacks = _block_stacks(outer, live)
        idx = line - 1
        if 0 <= idx < len(stacks) and stacks[idx]:
            return stacks[idx][-1][1]
        return ""

    return lookup


def _instantiation_sites(sections: list[TheorySection], names: list[str]
                         ) -> list[tuple[Site, list[str]]]:
    """Every instantiation site of ANY of ``names``, in section-load order,
    each paired with the names it instantiates IN WRITTEN ORDER.

    ``instantiation bool :: "{mynull, ord}"`` asked about both classes is ONE
    site that names two.  One pass whatever the length of ``names``, because
    each pass materialises every section's two redacted views — and a line
    matched here is one site however many of the names it writes, which is
    what makes the transitive listing free of duplicates without a second
    scan to deduplicate against.
    """
    out: list[tuple[Site, list[str]]] = []
    # An `interpretation L` in a theory that does not import L's is a
    # DIFFERENT locale of the same name.  Same necessary condition the
    # citation scan applies, and per NAME: a descendant declared elsewhere in
    # the corpus has its own visibility, not its ancestor's.
    filters = [(n, site_filter(sections, n)) for n in names]
    for sec in sections:
        here = [n for n, admits in filters if admits(sec.theory)]
        if not here:
            continue
        live = sec.live_source()
        outer = sec.outer_source()
        raw = sec.source()
        enclosing_name = _enclosing_lookup(sec, live, outer)
        for i in range(1, len(outer) + 1):
            stripped = outer[i - 1].lstrip()
            m = _INST_CMD_RE.match(stripped)
            if not m:
                continue
            command = m.group(1)
            head_live, head_outer = _header_at(live, outer, i)
            # Past the command keyword, in both views at once.
            at0 = len(outer[i - 1]) - len(stripped) + m.end()
            at = at0 + _marker_end(head_live[at0:])
            body_live = head_live[at:]
            body_outer = head_outer[at:]
            if command in ("instantiation", "instance"):
                # Bare `instance` closes an `instantiation` block (already
                # counted at its head) and `instance C \<subseteq> D` is a
                # class inclusion: neither has a `::`, so neither is an
                # arity.
                via = _first_denoted(arity_classes(body_live, body_outer),
                                     here)
                if via:
                    ctor, sorts = arity_parts(body_live, body_outer)
                    out.append((Site(sec.theory, sec.path, i, command,
                                     raw[i - 1].rstrip(),
                                     ctor or UNNAMED, sorts), via))
                continue
            target = ""
            cut = 0
            if command == "sublocale":
                target = _sublocale_target(body_live, body_outer)
                ma = _SUBLOCALE_TARGET_RE.match(body_outer)
                cut = ma.end() if ma else 0
            instances = expression_instances(body_live[cut:],
                                             body_outer[cut:])
            matched = [(q, loc) for q, loc in instances
                       if any(denotes(loc, n) for n in here)]
            if not matched:
                continue
            via = _first_denoted([loc for _q, loc in instances], here)
            # Written first, derived second: the qualifier the author put on
            # THIS instance, else the target `sublocale L \<subseteq> M`
            # names, else whatever context the site sits in.  A site with
            # none of those is left `?` rather than given the locale's own
            # name, which would make every row say the same word twice.
            written = next((q for q, _loc in matched if q), "")
            if written:
                label = written
            elif target:
                label = target
            else:
                label = enclosing_name(i) or UNNAMED
            out.append((Site(sec.theory, sec.path, i, command,
                             raw[i - 1].rstrip(), label), via))
    return out


def _first_denoted(written: list[str], here: list[str]) -> list[str]:
    """For each written name, the first of ``here`` it denotes; distinct,
    in written order."""
    out: list[str] = []
    for w in written:
        for n in here:
            if denotes(w, n):
                if n not in out:
                    out.append(n)
                break
    return out


def find_instantiations(sections: list[TheorySection], name: str
                        ) -> list[Site]:
    """Every instantiation site of ``name``."""
    return [site for site, _via in _instantiation_sites(sections, [name])]


# ---------------------------------------------------------------------------
# The class / locale hierarchy, and the transitive listing
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Extends:
    r"""THE EDGE RELATION: ``child`` extends ``parent``, written in ``theory``.

    The five ways the source writes one — live text only::

        class X = ... Y ...        Y is a head of the class expression
        locale X = ... Y ...       Y is a head of a locale-expression instance
        subclass Y                 inside the block of `class X ... begin`
        instance X ('<'|'\<subseteq>') Y
        sublocale X ('<'|'\<subseteq>') Y ...
        sublocale Y ...            inside `context X begin` / `locale X ... begin`

    The first two are read off the DECLARATION's own header, so they iterate
    entries rather than lines: an entry already knows where its command
    starts and what it is called.  The rest are commands that declare no
    entry, found the way the site scan finds its own — at a line where a
    command may start, on the outer view.

    `interpretation` and its kin are NOT edges: they supply types or terms,
    so the thing interpreted is an instance of the locale rather than a
    locale that IS one, and its own instantiations say nothing about the
    subject's.  A `sublocale X \<subseteq> S` line is both a SITE of S and an
    edge that pulls X's sites in — every instantiation of X is then an
    instantiation of S — and nothing special-cases it, because one line
    yields at most one site per scan.
    """
    child: str
    parent: str
    theory: str


_EXTEND_CMD_RE = re.compile(r"^(subclass|instance|sublocale)(?![\w'])")

# Where a class or locale expression STOPS: the first context element of the
# declaration.  `defines`, `for`, `begin` and `where` already end the header
# (`_HEADER_STOP_RE`); these four do not, because a site command has no
# context elements.
_CONTEXT_ELEM_RE = re.compile(
    r"(?<![\w'])(fixes|constrains|assumes|notes)(?![\w'])")

# An explicit `(in c)` target modifier, which RETARGETS the command it
# prefixes exactly as it retargets a declaration (`Entry.target`).
_IN_TARGET_RE = re.compile(r"^\s*\(\s*in(?![\w'])\s*")


def extends_heads(live: str, outer: str) -> list[str]:
    """The locales a ``class X = ...`` / ``locale X = ...`` header EXTENDS:
    the heads of the expression after the ``=``, up to the first context
    element.  The ``=`` and the stop are found on outer (a ``=`` inside a
    term is neither); the names are read from live, since a head may be
    quoted or qualified."""
    n = min(len(live), len(outer))
    m = _CONTEXT_ELEM_RE.search(outer)
    stop = min(m.start(), n) if m else n
    eq = outer.find("=")
    if eq < 0 or eq + 1 > stop:
        return []
    return expression_heads(live[eq + 1:stop], outer[eq + 1:stop])


def extends_edges(sections: list[TheorySection]) -> list[Extends]:
    """Every edge in the project, in one pass.

    A LIST rather than a parent-to-children map, because a parent is matched
    under :func:`denotes` — the written spelling may be qualified — and a map
    keyed by the written name would answer ``Groups.monoid`` to a question
    about ``monoid`` only by being asked twice.
    """
    out: list[Extends] = []
    for sec in sections:
        live = sec.live_source()
        outer = sec.outer_source()

        for e in sec.entries:
            if e.tag in LOCALE_TAGS and e.name and e.name != UNNAMED:
                head_live, head_outer = _header_at(live, outer, e.thy_line)
                for parent in extends_heads(head_live, head_outer):
                    out.append(Extends(e.name, parent, sec.theory))

        enclosing_name = _enclosing_lookup(sec, live, outer)
        for i in range(1, len(outer) + 1):
            stripped = outer[i - 1].lstrip()
            m = _EXTEND_CMD_RE.match(stripped)
            if not m:
                continue
            command = m.group(1)
            head_live, head_outer = _header_at(live, outer, i)
            at0 = len(outer[i - 1]) - len(stripped) + m.end()
            at = at0 + _marker_end(head_live[at0:])
            body_live = head_live[at:]
            body_outer = head_outer[at:]

            # `subclass (in c) Y` names its own child; otherwise the child of
            # a `subclass` is the class block it sits in.
            child = ""
            t = _IN_TARGET_RE.match(body_outer)
            if t:
                nm = _name_at(body_live, t.end())
                child = nm[0] if nm else ""
                e = _paren_end(body_outer, body_outer.find("("))
                if e > 0:
                    body_live = body_live[e:]
                    body_outer = body_outer[e:]

            arrow = _SUBLOCALE_TARGET_RE.match(body_outer)
            parents: list[str]
            if command == "instance":
                # `instance X \<subseteq> Y` -- and nothing else `instance`
                # writes: an arity has no arrow, and a bare `instance ..` has
                # no name.  The inclusion is a class expression of exactly
                # one head, so the same reader serves.
                if not arrow:
                    parents = []
                else:
                    if not child:
                        child = _sublocale_target(body_live, body_outer)
                    parents = expression_heads(body_live[arrow.end():],
                                               body_outer[arrow.end():])
            elif command == "sublocale":
                if not child:
                    child = (_sublocale_target(body_live, body_outer)
                             if arrow else enclosing_name(i))
                cut = arrow.end() if arrow else 0
                parents = expression_heads(body_live[cut:], body_outer[cut:])
            else:
                if not child:
                    child = enclosing_name(i)
                nm = _name_at(body_live, _skip_space(body_live, 0))
                parents = [nm[0]] if nm else []
            if child:
                for parent in parents:
                    out.append(Extends(child, parent, sec.theory))
    return out


def _extenders_of(edges: list[Extends], admits, name: str) -> list[str]:
    out: list[str] = []
    for e in edges:
        if (denotes(e.parent, name) and not denotes(e.child, name)
                and admits(e.theory) and e.child not in out):
            out.append(e.child)
    return out


def extenders(sections: list[TheorySection], name: str) -> list[str]:
    """The classes and locales that extend ``name`` DIRECTLY.

    An edge counts only where its section can see the declaration of
    ``name``, the same necessary condition a site obeys — two projects that
    each declare a ``monoid`` do not extend each other's.  A self-edge
    (``sublocale L < dual: L ...``) is not an extension and is dropped here
    rather than left for the caller.
    """
    return _extenders_of(extends_edges(sections), site_filter(sections, name),
                         name)


def descendants(sections: list[TheorySection], name: str) -> list[str]:
    """Everything that IS a ``name``, transitively.

    Breadth-first over the edge relation, ``name`` itself excluded (it is
    not its own descendant), with a visited set so that a cycle — which
    Isabelle's own checks rule out, but a text scan of a half-written theory
    does not — terminates rather than hangs.  The visibility filter is
    applied per parent at each step, memoised: a descendant declared
    elsewhere in the corpus has its own visibility, not its ancestor's.
    """
    edges = extends_edges(sections)
    filters: dict = {}

    def admits(n: str):
        if n not in filters:
            filters[n] = site_filter(sections, n)
        return filters[n]

    seen = {name}
    out: list[str] = []
    queue = [name]
    while queue:
        here = queue.pop(0)
        for child in _extenders_of(edges, admits(here), here):
            if child not in seen:
                seen.add(child)
                out.append(child)
                queue.append(child)
    return out


def find_instantiations_transitive(sections: list[TheorySection], name: str
                                   ) -> list[tuple[Site, str]]:
    """The transitive instantiation sites of ``name``: every site of
    ``name`` itself and of everything that extends it, deduplicated by
    construction (one scan, one row per line), each with the ``VIA`` cell —
    the closure members the line actually writes, comma-joined — which is
    what makes a row naming neither the subject nor anything the reader
    recognises explicable."""
    return [(site, ", ".join(via)) for site, via in
            _instantiation_sites(sections, [name] + descendants(sections, name))]
