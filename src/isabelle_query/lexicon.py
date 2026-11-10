r"""Where an Isabelle name starts and ends, and which words are keywords
[api-names] [api-keywords].

Named after Isabelle's `Pure/Syntax/lexicon.ML`, which defines the rule
this module follows.  Outer syntax does not have its own identifier rule:
`Token.scan_token` (`Pure/Isar/token.ML`) calls `Lexicon.scan_longid` and
`Lexicon.scan_id`, the same functions inner syntax uses.  So where a name
starts and ends is one fact, the same in a command, a fact list and a
term.  What differs between those places is which tokens are names at
all, which is grammar, and is not decided here.

The rule (`Symbol_Pos.scan_ident`, `Symbol.kind`):

- a *letter* is an ASCII letter, `\<A>`..`\<Z>`, `\<a>`..`\<z>`,
  `\<AA>`..`\<ZZ>`, `\<aa>`..`\<zz>`, or a Greek letter other than
  `\<lambda>`.  The `\<var...>` forms (`\<varepsilon>`) are not letters;
- an identifier is a letter, then letters, digits, `_` and `'`, with
  `\<^sub>` allowed before a run of those;
- a long identifier is identifiers joined by `.`.  A `.` with no identifier
  after it is not part of the name: in `using foo.` the `.` is the proof.

`\<Gamma>foo` and `foo\<^sub>1` are therefore one name each, and
`foo_bar` and `foo'` are not `foo`.  A schematic variable (`?x`) and a type
variable (`'a`) are not names.  Symbolic identifiers (`*`, `**`) are not
reported: they are names only as proof labels in outer syntax, and an
operator in a term, and that is grammar.

The lexical antiquotation pieces (`doc_antiquotations` and the cartouche
and brace matching under it) live here too, since `graph` and the scanner
both need them and `api` may import nothing above `parsing` and this
module.
"""

from __future__ import annotations

import functools
import re
from bisect import bisect_right
from collections.abc import Iterator
from pathlib import Path
from typing import NamedTuple

from isabelle_layout import parse_thy_imports

from isabelle_query import _isabelle_namespace as _pure
from isabelle_query.model import TheorySection

# --- the identifier rule ------------------------------------------------------

_GREEK = ("alpha beta gamma delta epsilon zeta eta theta iota kappa mu nu "
          "xi pi rho sigma tau upsilon phi chi psi omega Gamma Delta Theta "
          "Lambda Xi Pi Sigma Upsilon Phi Psi Omega").split()
_LETTER = (r"(?:[A-Za-z]|\\<(?:[A-Za-z]|AA|BB|CC|DD|EE|FF|GG|HH|II|JJ|KK|LL|"
           r"MM|NN|OO|PP|QQ|RR|SS|TT|UU|VV|WW|XX|YY|ZZ|aa|bb|cc|dd|ee|ff|gg|"
           r"hh|ii|jj|kk|ll|mm|nn|oo|pp|qq|rr|ss|tt|uu|vv|ww|xx|yy|zz|"
           + "|".join(_GREEK) + r")>)")
_LETDIG = rf"(?:{_LETTER}|[0-9_'])"
IDENT = rf"{_LETTER}(?:{_LETDIG}+|\\<\^sub>{_LETDIG}+)*"
LONG_IDENT = rf"{IDENT}(?:\.{IDENT})*"

# One token at a time, left to right, as Isabelle's scanner would: a
# variable or type variable is consumed whole so that its identifier is not
# reported, and so is any other symbol, so that the letters of `\<and>` or
# `\<open>` are not read as a name.
_TOKEN_RE = re.compile(
    rf"(?P<var>\?'?{IDENT}(?:\.[0-9]+)?|'{IDENT})"
    rf"|(?P<name>{LONG_IDENT})"
    r"|[0-9]+(?:\.[0-9]+)?"
    r"|\\<\^?[A-Za-z0-9_']*>"
    r"|.", re.S)


class NameOccurrence(NamedTuple):
    """One name in a theory's source [api-names].

    ``line`` is 1-indexed; ``start`` and ``end`` are 0-indexed character
    columns on that line, end exclusive, so ``source()[line - 1][start:end]
    == text``.  A name spans one line.  ``parts`` is ``text`` split at its
    dots: `M.foo` gives ``("M", "foo")`` and `foo.simps` gives ``("foo",
    "simps")``.  ``kind`` is the antiquotation's kind (`thm`, `const`,
    `term`, ...) when the name is inside one, else ``None``."""
    line: int
    start: int
    end: int
    text: str
    parts: tuple[str, ...]
    kind: str | None


def scan_names(text: str) -> Iterator[tuple[int, int, str]]:
    """``(start, end, name)`` for each name in ``text``, by the rule above.
    No regions are applied: a comment is scanned like code.  Use
    :func:`name_occurrences` for a theory."""
    for m in _TOKEN_RE.finditer(text):
        if m.lastgroup == "name":
            yield m.start(), m.end(), m.group()


# --- antiquotations (lexical) -------------------------------------------------

# The antiquotations that name a declaration, and so fail the build when it
# goes [doc-antiq].  FACT kinds name facts: `@{thm foo}`, `@{thm [display]
# foo bar}`, `@{thms foo}`, the style forms, `\<^thm>‹foo›`.  The others
# name constants, types, classes or locales, alone (`@{const foo}`, `@{type
# foo}`) or inside a term or type (`@{term "foo x"}`, `@{typ "'a foo"}`).
# Not `@{lemma "P" by simp}`, which states a proposition rather than naming
# one.  `graph._KIND_SPACES` says which name spaces each of the others reads.
FACT_ANTIQ_KINDS = frozenset({"thm", "thms", "thm_style", "named_thms"})
NAME_ANTIQ_KINDS = FACT_ANTIQ_KINDS | frozenset({
    "const", "const_name", "const_abbrev", "const_syntax", "Const", "Const_",
    "term", "prop", "term_type", "value", "typ", "type", "type_name", "Type",
    "Type_", "class", "locale"})
# ML's `\<^Const>‹plus T›` and `\<^Type>‹list T›` name one declaration, then
# take ML variables for its type arguments: only the first name is read.
FIRST_NAME_KINDS = frozenset({"Const", "Const_", "Type", "Type_"})
_ANTIQ_KINDS = sorted(NAME_ANTIQ_KINDS, key=lambda k: -len(k))  # `thms` > `thm`
_ANTIQ_START_RE = re.compile(
    r"@\{\s*(" + "|".join(_ANTIQ_KINDS) + r")(?![\w'])"
    r"|\\<\^(" + "|".join(_ANTIQ_KINDS) + r")>\s*(?=\\<open>|‹)")
_OPEN, _CLOSE = ("\\<open>", "‹"), ("\\<close>", "›")
# A term's options come first (`@{term [show_types] "x"}`); a later `[` is
# the term's own list syntax, whose names count.
ANTIQ_OPTIONS_RE = re.compile(r"\s*\[[^\]]*\]")


def _cartouche_end(text: str, i: int) -> int:
    """Index just past the cartouche that opens at ``text[i]``, nested
    cartouches counted; the end of the text if it never closes."""
    depth = 0
    n = len(text)
    while i < n:
        o = next((o for o in _OPEN if text.startswith(o, i)), None)
        if o:
            depth += 1
            i += len(o)
            continue
        c = next((c for c in _CLOSE if text.startswith(c, i)), None)
        if c:
            depth -= 1
            i += len(c)
            if depth == 0:
                return i
            continue
        i += 1
    return n


def _brace_end(text: str, i: int) -> int:
    """Index just past the `}` that closes an `@{` body starting at ``i``.

    A `}` inside a string or a cartouche is the body's own, as in `@{term
    "{x. P x}"}`: 239 `@{term}` and 23 `@{thm}` bodies in afp-devel hold one
    (`scripts/probe_antiquotations.py`), and a `[^}]*` body stopped there."""
    n = len(text)
    while i < n:
        ch = text[i]
        if ch == "}":
            return i + 1
        if ch == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
        elif text.startswith(_OPEN, i):
            i = _cartouche_end(text, i)
        else:
            i += 1
    return n


def unchecked_at(sec: TheorySection, line: int, col: int) -> bool:
    """Is ``line``:``col`` inside a comment, or cancelled or raw text, which
    Isabelle never reads [antiq-comment]?  The tokenizer records those
    regions (`TheorySection.unread_spans`); an ML body and a `\\<comment>`
    note are read, and are not among them."""
    return any(lo <= col < hi for lo, hi in sec.unread_spans.get(line, ()))


def doc_antiquotations(text: str):
    """Yield ``(kind, start, end, body)`` for each name-bearing antiquotation
    in ``text`` [doc-antiq], in either spelling.  Bodies may span lines: the
    caller passes a whole theory, not a line."""
    if "@{" not in text and "\\<^" not in text:
        return
    for m in _ANTIQ_START_RE.finditer(text):
        if m.group(1):
            end = _brace_end(text, m.end())
            yield m.group(1), m.start(), end, text[m.end():end - 1]
        else:
            end = _cartouche_end(text, m.end())
            yield m.group(2), m.start(), end, text[m.end():end]


# --- the scanner over a theory ------------------------------------------------

def name_occurrences(sec: TheorySection) -> list[NameOccurrence]:
    r"""Every name Isabelle reads in ``sec``, in source order [api-names].

    Read: commands, fact lists and terms (`TheorySection.live_source`, less
    the document text of `text` blocks, headings and entry preambles), and
    the bodies of the antiquotations that name a declaration, wherever
    Isabelle checks them: in document text, in an ML body, in a
    `\<comment>` note.  Not read: prose, comments, `\<^cancel>` text, and
    ML code outside an antiquotation, whose identifiers are ML's.

    In an antiquotation, a term's leading options (`[show_types]`) are
    skipped, and `\<^Const>‹plus T›` gives only `plus`.  A fact
    antiquotation's attributes are scanned like the rest, so `@{thm foo
    [OF bar]}` gives `foo`, `OF` and `bar`.

    An outer-syntax keyword (`lemma`, `by`, `where`) is not a name, and is
    left out where Isabelle reads it as one: outside a term
    (`TheorySection.inner_spans`), by :func:`active_keywords` for this
    theory.  Inside a term the syntax table decides, which is not known
    here, so a delimiter such as `if` or `case` is reported there.  It
    declares nothing, so no rename of a declaration matches it.

    What a name refers to is not decided here.  `foo_def` is one name, the
    fact `definition foo` minted; `foo.simps` is a long name whose first
    part is the `fun foo` it came from; and a bound variable spelled like a
    constant is the same text as the constant.  A tool that renames a
    declaration has to decide those cases itself."""
    lines = sec.live_source()
    prose: set[int] = set()
    for lo, hi in list(sec.text_blocks) + list(sec.heading_spans) + [
            e.preamble for e in sec.entries if e.preamble]:
        prose.update(range(lo, hi + 1))
    keywords = active_keywords([sec])
    found: dict[tuple[int, int], NameOccurrence] = {}
    for ln, text in enumerate(lines, 1):
        if ln in prose:
            continue
        inner = sec.inner_spans.get(ln, ())
        for s, e, name in scan_names(text):
            if name in keywords and not any(lo <= s < hi for lo, hi in inner):
                continue
            found[ln, s] = NameOccurrence(ln, s, e, name,
                                          tuple(name.split(".")), None)
    src = sec.source()
    text = "\n".join(src)
    starts = [0]
    for line in src:
        starts.append(starts[-1] + len(line) + 1)
    for kind, a_start, a_end, _body in doc_antiquotations(text):
        ln = bisect_right(starts, a_start)
        if unchecked_at(sec, ln, a_start - starts[ln - 1]):
            continue
        body = _ANTIQ_START_RE.match(text, a_start).end()
        stop = a_end - 1 if text[a_start] == "@" else a_end
        if kind not in FACT_ANTIQ_KINDS:
            m = ANTIQ_OPTIONS_RE.match(text, body)
            if m:
                body = m.end()
        for s, e, name in scan_names(text[body:stop]):
            at = body + s
            ln = bisect_right(starts, at)
            col = at - starts[ln - 1]
            found[ln, col] = NameOccurrence(ln, col, col + e - s, name,
                                            tuple(name.split(".")), kind)
            if kind in FIRST_NAME_KINDS:
                break
    return [found[k] for k in sorted(found)]


# --- keywords -----------------------------------------------------------------

_HEADER_RE = re.compile(r"(?s)^\s*theory\b.*?^\s*begin\b", re.M)
_CLAUSE_RE = re.compile(r"(?s)\bkeywords\b(.*?)(?:\babbrevs\b|\Z)")
_COMMENT_RE = re.compile(r"(?s)\(\*.*?\*\)")
_TAG_RE = re.compile(r'%\s*"[^"]*"')
_IDENT_RE = re.compile(IDENT)


def header_keywords(text: str) -> set[str]:
    """Every identifier-shaped keyword a theory's header declares
    [api-keywords]: its `keywords` clause, up to `abbrevs` (whose quoted
    strings are abbreviations) or `begin`.  A `%` tag (`:: thy_decl % "ML"`)
    is quoted too, and is not a keyword."""
    m = _HEADER_RE.search(text)
    if not m:
        return set()
    c = _CLAUSE_RE.search(_COMMENT_RE.sub(" ", m.group(0)))
    if not c:
        return set()
    return {w for w in re.findall(r'"([^"]+)"', _TAG_RE.sub(" ", c.group(1)))
            if _IDENT_RE.fullmatch(w)}


@functools.lru_cache(maxsize=4)
def _by_base(names: frozenset[str]) -> dict[str, list[str]]:
    out: dict[str, list[str]] = {}
    for q in names:
        out.setdefault(q.split(".", 1)[1], []).append(q)
    return out


def resolve_import(imp: str, session: str | None,
                   names: frozenset[str]) -> str | None:
    """The `Session.Theory` an import names among ``names``, or ``None``
    [api-keywords].  A qualified name is taken as written; a path
    (`"~~/src/HOL/Library/FuncSet"`) by its last component; a bare name in
    ``session`` first, then as the one theory of that name, preferring HOL's
    and then Pure's when several sessions have one."""
    imp = imp.strip('"')
    if "/" in imp:
        imp = imp.rsplit("/", 1)[1]
    if imp in names:
        return imp
    if session and f"{session}.{imp}" in names:
        return f"{session}.{imp}"
    cands = _by_base(names).get(imp.rsplit(".", 1)[-1], [])
    for pref in ("HOL.", "Pure."):
        hit = [c for c in cands if c.startswith(pref)]
        if len(hit) == 1:
            return hit[0]
    return cands[0] if len(cands) == 1 else None


@functools.cache
def _dist():
    """The distribution table, loaded on first use: it is 140KB of import
    edges that only the keyword test reads."""
    from isabelle_query import _distribution_keywords as d
    names = frozenset(d.KEYWORDS) | frozenset(d.IMPORTS) | frozenset(
        t for ts in d.IMPORTS.values() for t in ts)
    return d, names


def _closure_keywords(roots: set[str]) -> set[str]:
    d, _names = _dist()
    seen: set[str] = set()
    todo = list(roots)
    while todo:
        t = todo.pop()
        if t not in seen:
            seen.add(t)
            todo.extend(d.IMPORTS.get(t, ()))
    return {w for t in seen for w in d.KEYWORDS.get(t, ())}


def active_keywords(sections: list[TheorySection] | None = None
                    ) -> frozenset[str]:
    """The identifier-shaped keywords in force somewhere in ``sections``
    [api-keywords]: Pure's, those the distribution theories they import
    declare (with those theories' own imports, transitively), and those
    their own headers declare.  With no sections, a theory importing
    `Main`."""
    words = set(_pure.KEYWORDS)
    if sections is None:
        return frozenset(words | _closure_keywords({"HOL.Main"}))
    own = {s.theory for s in sections}
    roots: set[str] = set()
    for sec in sections:
        words |= header_keywords("\n".join(sec.source()))
        imports = (parse_thy_imports(sec.path)
                   if Path(sec.path).is_file() else [])
        for imp in imports:
            if imp.strip('"').rsplit("/", 1)[-1] in own:
                continue
            r = resolve_import(imp, None, _dist()[1])
            if r:
                roots.add(r)
    return frozenset(words | _closure_keywords(roots))


def is_keyword(word: str, sections: list[TheorySection] | None = None
               ) -> bool:
    """Would Isabelle read ``word`` as a keyword rather than a name, in some
    theory of ``sections`` [api-keywords]?  See :func:`active_keywords`.
    In outer syntax a keyword wins over an identifier of the same length,
    so a name that is a keyword cannot be written where a name goes.

    Each call reads ``sections``' headers; to test many words, take
    :func:`active_keywords` once."""
    return word in active_keywords(sections)
