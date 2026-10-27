r"""Proof-local names bound and never read (issue #12).

``unused`` asks which DECLARATIONS nothing cites, over the citation graph
between entries.  This asks the same question one level down, inside a single
proof body: which ``have NAME:``, ``obtain … where NAME:``, ``note NAME =``,
``define NAME`` or ``let ?NAME`` binds a name that nothing in its scope reads
— and, since the statement's own premises are proof-local in the same sense,
which ``assumes NAME:`` or ``if NAME:`` (issue #20, `_seed_premises`).
Isabelle never warns about these, and the edit that produces them is routine:
a long proof copied and then trimmed leaves a prefix of facts whose only
reader was in the part that went.

The walk is a token stream over the proof body in two views at once, the same
split ``sites`` uses: ``outer_source`` decides structure and fact names (a
citation is outer syntax), and the positions ``outer_source`` blanks but
``live_source`` keeps are inner terms, where a ``let ?x`` abbreviation or a
``define``d variable is read.  Comments, ``\<comment>`` notes and ``text``
blocks are in neither, so a name mentioned only there is still reported.

Three pieces of Isar semantics decide the answer, and a flat "the name occurs
once" count gets each of them wrong:

* **Scope.**  A name bound inside ``proof … qed`` or ``{ … }`` is invisible
  after the block closes, and ``next`` starts a fresh branch.  The same label
  reused in two ``case`` branches is two bindings, each needing its own reader.
* **Binding time.**  ``have a: "P" using a by simp`` cites the OLD ``a``: the
  label is bound when the statement's proof finishes, not when it is written
  — after the method of its ``by`` / ``qed`` too, so ``by (simp add: a)``
  cites the old one as well.  ``note`` / ``define`` / ``let`` bind at the end
  of their own command.
* **``this``.**  A fact consumed by chaining (``then``, ``hence``, ``thus``,
  ``with``, ``moreover``, ``ultimately``, ``also``, ``finally``, or a written
  ``this``) is used although its name is not.  That label is redundant rather
  than dead, and the question here is about dead facts, so it is not reported.
* **Statements** (issue #27).  A fact can be read with no name at all.  A
  bare ``fact`` method (``by fact``, ``(fact | rule refl)+``) closes its goal
  with ANY fact in scope whose statement matches, so it reads every one
  visible there; ``fact a`` reads ``a`` alone.  A literal fact ``‹P›`` reads
  the visible facts whose statement is written ``P``, whitespace aside.

A labelled fact given a declaring attribute (``have s [simp]:``) is read by
the rule set it joined and is never reported; a transforming attribute
(``[rule_format]``, ``[symmetric]``) adds it to nothing and does not protect it.

Each binding also records the lines that bind it [local-spans], for a caller
that means to cut them: from its statement — or the ``from`` / ``with`` /
``then`` leading into it — to the end of its proof, a method after ``qed``
included.  ``span_text`` prints them, or the reason they cannot simply go:
a clause of a statement binding several facts, a line shared with another
command, an ``obtain`` that also fixes variables, a statement premise, or a
proof the walk never saw close.

The result is a list of CANDIDATES, not a delete list, because the errors run
both ways.  A fact can be used where no scan of the proof sees its name —
through a bundle cited under another name, by position (``case`` numbering
such as ``1(2)``), by a literal fact spelled otherwise than its statement
(``‹x = 0›`` for ``"x = (0::nat)"``), or by an ``obtain`` whose hand-written
``that`` must match its supplier clause for clause — and is then reported
although it is needed.  The other way, a token that merely spells the name (a
same-named variable in outer syntax) counts as a reader, and a binding goes
unreported.  Over the AFP, 2.7% of 301,053 bindings are reported.
"""

from __future__ import annotations

import re
from bisect import bisect_right
from dataclasses import dataclass, field
from pathlib import Path
from string import ascii_letters

from isabelle_query.graph import (
    CLOSING_KEYWORDS, CONTEXT_KEYWORDS, GOAL_KEYWORDS, PLUMBING_KEYWORDS,
    _noise_spans)
from isabelle_query.model import Entry, TheorySection
from isabelle_query.parsing import (
    LETTER_SYMS, SYM_IDENT, SYMBOLIC_KEYWORDS, TRANSFORMING_ATTRS)
from isabelle_query.premises import statement_of

# An identifier by Isabelle's own lexical rule (`Doc/Isar_Ref`, "letter"): an
# ASCII letter, a Greek or `\<A>` / `\<AA>` letter symbol, and inside the name
# also digits, `_`, `'` and `\<^sub>`.  Narrower than `parsing._ISA_NAME`, which
# admits any markup: here `?R\<^sup>*` and `\<^bsub>?r\<^esub>` must read `?R`
# and `?r`, or the abbreviation they use goes unseen.
_LETTER = r"(?:[A-Za-z]|\\<(?:{})>)".format("|".join(
    list(ascii_letters) + [c + c for c in ascii_letters]
    + sorted(sym[2:-1] for sym in LETTER_SYMS)))
_NAME = rf"{_LETTER}(?:{_LETTER}|[0-9_']|\\<\^sub>)*"
# A dotted name is one token (`Suc.IH`, `assms(1)` reads as `assms`); `?x` is a
# schematic abbreviation; the punctuation is what the grammar below looks at.
# Any other symbol (`\<in>`, `\<^sup>`) is matched whole so its letters never
# surface as a word, and then dropped (the `sym` group).  A numeral is a name
# too [numeral-label]: Isar's `name` admits `nat`, so `assumes 1: "P"` binds
# and `using 1` reads, as do case facts `1.prems` (#32).  So is a symbolic
# identifier standing alone, `assumes *:` and `using * **` (#35), though a
# keyword so spelled is not (:func:`_is_name`).  `.` is no symbolic
# character, so `using *.` is `*` and the terminal proof `.` (#37), as `using
# a.` is `a` and `.`.  This is the outer view, where a numeral in a term is
# already blank.
_TOKEN_RE = re.compile(
    rf"(\?{_NAME})|({_NAME}(?:\.{_NAME})*)|([0-9]+(?![\w'])(?:\.{_NAME})*)"
    rf"|(?P<sym>\\<\^?\w+>)"
    rf"|((?<![^\s(\[,;:]){SYM_IDENT}"
    rf"(?:(?![^\s:()\[\],;])|(?=\.\.?(?!\S))))"
    rf"|(\.\.|::|[.{{}}()\[\]:=,])")
_KEYWORD_ALT = "(?:" + "|".join(map(re.escape, SYMBOLIC_KEYWORDS)) + ")"
# A symbolic name standing alone in a term may be method text's (`use x
# in ‹simp add: * "**"›`, #35).  Read as a term it names nothing, and a read
# only ever removes a candidate.
_TERM_TOKEN_RE = re.compile(
    rf"\??{_NAME}|(?P<sym>\\<\^?\w+>)"
    rf"|(?<![^\s(\[,;:\"]){SYM_IDENT}(?=[\s)\],;\"\\]|\Z)")
# A string is a name as well (`by (meson "2" foo)`, `using "14.prems"`,
# `from "**"(4)`): Sledgehammer quotes the names that are not identifiers,
# and over the AFP a symbolic label is cited quoted about as often as not.
# Under a command that cites facts, one that is nothing but a name reads that
# fact [numeral-label] — except as a term argument, `[of "i"]`, `[where x =
# "t"]`, `rule_tac x = "t"`, where the outer text before it says so.
_QUOTED_NAME_RE = re.compile(
    rf"(?:{_NAME}|[0-9]+)(?:\.{_NAME})*|(?!{_KEYWORD_ALT}\Z){SYM_IDENT}")
_TERM_ARG_BEFORE_RE = re.compile(r"(?:\[\s*(?:of|where)\b[^\[\]]*|=\s*)$")

# Every word that starts a proof command.  Recognised only outside parentheses
# and brackets, so a method's arguments (`proof (cases x)`) never read as one.
_COMMANDS = (GOAL_KEYWORDS | CONTEXT_KEYWORDS | PLUMBING_KEYWORDS
             | CLOSING_KEYWORDS
             | {"proof", "next", "sorry", "oops", "include", "including",
                "supply", "subgoal", "defer", "prefer", "back", "apply_end",
                "presume"})
# Commands that consume the fact currently bound to `this`.
_CHAIN_READERS = frozenset({
    "then", "hence", "thus", "with", "moreover", "ultimately", "also",
    "finally"})
# Commands after which `this` is something no tracked binding supplied.
_THIS_RESETS = frozenset({"from", "with", "assume", "presume", "case", "next"})
# Goals: their labels bind when their proof finishes.  `hence`/`obtain` bind
# like `have`; `show`/`thus`/`consider` are goals whose labels are not tracked.
_GOAL_CMDS = frozenset({"have", "hence", "show", "thus", "obtain", "consider"})
_LABELLED_GOALS = frozenset({"have", "hence", "obtain"})
_TERMINATORS = frozenset({"by", "done", "sorry", "oops", ".", ".."})
# Commands whose text names facts, so a cartouche there is a literal fact
# (`using ‹P›`, `by (rule ‹P›)`) and not a statement.
_FACT_CMDS = frozenset({"using", "from", "with", "unfolding", "note",
                        "by", "apply", "apply_end", "proof", "qed"})
# Commands that start a statement, and those that may lead into one from
# the line above (`from x` / `then` / `with x`, then `have …`): a statement's
# lines start at its lead [local-spans].
_STMT_CMDS = frozenset({"have", "hence", "show", "thus", "obtain", "consider",
                        "note", "let", "define"})
_LEADS = frozenset({"from", "with", "then"})
# Commands whose `and` separates two facts of one statement.
_CLAUSE_CMDS = frozenset({"have", "hence", "show", "thus", "note", "let"})
# Commands followed by a proof method.
_METHOD_CMDS = frozenset({"by", "apply", "apply_end", "proof", "qed"})


# What ends the outer text before a cartouche of method text, within a
# method [method-cartouche]: `use x in ‹simp add: y›`, and Eisbach's
# `match conclusion in "P" ⇒ ‹rule H›`.
_METHOD_TEXT_BEFORE_RE = re.compile(
    r"(?:(?<![\w'])in|\\<Rightarrow>|⇒|=>)\s*$")


def _method_cartouche(outer: list[str], t: _Tok) -> bool:
    """Whether the cartouche *t* in a method holds method text rather than a
    literal fact: whether the outer text before it, on its line or the line
    above, ends in `in` or `⇒`."""
    ln, before = t.line, outer[t.line - 1][:t.col]
    while not before.strip() and ln > 1:
        ln -= 1
        before = outer[ln - 1]
    return bool(_METHOD_TEXT_BEFORE_RE.search(before))


def _bare(live: str, end: int) -> bool:
    """Whether the method name ending at *end* is given no argument: the line
    ends there, or a combinator or bracket follows (`(fact | rule refl)+`),
    or the cartouche of method text it is written in closes (`‹fact›`)."""
    rest = live[end:].lstrip()
    return (not rest or rest[0] in ")|;,+?]›"
            or rest.startswith("\\<close>"))


@dataclass
class LocalBinding:
    """A name one proof binds.  ``line`` is 1-indexed in the theory."""
    name: str       # as written: `a`, `?p`
    kind: str       # have / hence / obtain / note / define / let
    line: int
    entry: str
    read: bool = False
    kept: bool = False   # declared into a rule set by one of its attributes
    # What it states, each proposition whitespace-collapsed: a literal fact
    # `‹P›` reads the fact whose statement is `P`, whatever its name.
    stmts: list[str] = field(default_factory=list)
    # The lines that bind it [local-spans]: its statement — from a `from` /
    # `with` / `then` leading into it — to the end of its proof, a method
    # after `qed` included.  0 for a statement premise, which has no lines
    # of its own to cut.
    start: int = 0
    end: int = 0
    clause: bool = False      # one of several facts one statement binds
    shared: bool = False      # its first or last line holds another command
    binds_vars: bool = False  # an `obtain` that also fixes variables


@dataclass
class _Tok:
    line: int
    col: int
    text: str
    inner: bool          # a name inside a term, not outer syntax
    # A whole delimited term (`"…"` or a cartouche) rides in the stream too,
    # at its opening delimiter, ahead of the names inside it: its collapsed
    # text, and whether it is a cartouche — the only spelling of a literal
    # fact.  None on every other token.
    term: str | None = None
    cartouche: bool = False


_OPENERS = (("\"", "\""), ("\\<open>", "\\<close>"), ("‹", "›"))


def _term_tokens(live: list[str], spans: dict[int, list[tuple[int, int]]],
                 ln: int) -> list[_Tok]:
    """The terms that OPEN on line *ln*, each read to its close however many
    lines it runs.  *spans* are the parser's inner spans (`hi` exclusive); a
    span at column 0 continuing a term from the line above is no opening."""
    out: list[_Tok] = []
    text = live[ln - 1]
    for lo, hi in spans.get(ln, ()):
        pair = next((p for p in _OPENERS if text.startswith(p[0], lo)), None)
        if pair is None or (lo == 0 and _runs_on(live, spans, ln - 1)):
            continue
        parts = [text[lo:hi]]
        k = ln
        while (not _closed(parts[-1], k == ln) and hi >= len(live[k - 1])
               and spans.get(k + 1) and spans[k + 1][0][0] == 0):
            k += 1
            hi = spans[k][0][1]
            parts.append(live[k - 1][:hi])
        body = " ".join(parts).strip()[len(pair[0]):]
        if body.endswith(pair[1]):
            body = body[:-len(pair[1])]
        out.append(_Tok(ln, lo, "\x00", True, " ".join(body.split()),
                        pair[0] != "\""))
    return out


def _closed(seg: str, opening: bool) -> bool:
    """Whether a term's segment ends it: it ends with a closing delimiter
    that is not its own opening one."""
    seg = seg.rstrip()
    return any(seg.endswith(c) and not (opening and seg == o)
               for o, c in _OPENERS)


def _runs_on(live: list[str], spans: dict[int, list[tuple[int, int]]],
             ln: int) -> bool:
    """Whether a term is still open at the end of line *ln*."""
    sp = spans.get(ln)
    if not sp or sp[-1][1] < len(live[ln - 1]):
        return False
    lo, hi = sp[-1]
    seg = live[ln - 1][lo:hi]
    return bool(seg.strip()) and not _closed(seg, any(
        seg.startswith(o) for o, _c in _OPENERS))


def _body_tokens(sec: TheorySection, entry: Entry) -> list[_Tok]:
    """The proof body of *entry* as one token stream, in source order."""
    outer_src, live_src = sec.outer_source(), sec.live_source()
    # Read as far as `thy_end`; `_walk` stops at the proof's own close.  The
    # `text` blocks a proof may contain are noise and skipped below.
    end = min(entry.thy_end or len(outer_src), len(outer_src))
    noise: set[int] = set()
    for lo, hi in _noise_spans(sec):
        noise.update(range(lo, hi + 1))
    # The proof line is read whole, even when the statement shares it: the
    # statement's outer words bind nothing, and cutting at the method (as
    # `shape._inline_proof_col` does) loses a leading `subgoal`.
    out: list[_Tok] = []
    for ln in range(entry.proof_line, end + 1):
        if ln in noise:
            continue
        outer, live = outer_src[ln - 1], live_src[ln - 1]
        start = 0
        toks = _term_tokens(live_src, sec.inner_spans, ln)
        for m in _TOKEN_RE.finditer(outer, start):
            if not m.group("sym"):
                toks.append(_Tok(ln, m.start(), m.group(0), False))
        for m in _TERM_TOKEN_RE.finditer(live, start):
            c = m.start()
            if (not m.group("sym") and outer[c] == " "
                    and (c == 0 or not _word_char(live[c - 1]))):
                toks.append(_Tok(ln, c, m.group(0), True))
        toks.sort(key=lambda t: t.col)
        out.extend(toks)
    return out


_SYM_START = frozenset("!#$%&*+-/<=>?@^|~")


def _after_quoted_name(toks: list[_Tok], i: int, live: list[str]) -> bool:
    """Whether the `(` at *i* is glued to a quoted name, `"**"(4)`, so that
    it opens a selection.  A string rides in the stream at its opening
    quote, ahead of the names inside it, so look back past those."""
    t = toks[i]
    if live[t.line - 1][t.col - 1:t.col] != '"':
        return False
    q = i - 1
    while q >= 0 and toks[q].inner and toks[q].term is None:
        q -= 1
    if q < 0 or toks[q].line != t.line:
        return False
    p = toks[q]
    return (p.term is not None and not p.cartouche
            and bool(_QUOTED_NAME_RE.fullmatch(p.term)))


def _word_char(ch: str) -> bool:
    return ch.isalnum() or ch in "_'?"


def _is_name(tok: str) -> bool:
    """A name token, as opposed to punctuation.  Not `isalpha()`: a name may
    begin with a letter SYMBOL, and `define \\<epsilon> where` is common, be
    a numeral (`assumes 1:`), or be a symbolic identifier (`assumes *:`)."""
    return (tok[0].isalnum() or tok[0] == "\\"
            or (tok[0] in _SYM_START and tok not in SYMBOLIC_KEYWORDS))


def _is_var(tok: str) -> bool:
    """A name a variable may have: not a numeral, which is a fact name only
    (`define c (…) [80, 80]` fixes no `80`), nor a symbolic one."""
    return _is_name(tok) and (tok[0].isalpha() or tok[0] == "\\")


@dataclass
class _Walk:
    """The scan state of one proof body."""
    entry: str
    bindings: list[LocalBinding] = field(default_factory=list)
    # Visible names, innermost block last.  A key is `("f", name)` for a fact
    # and `("t", name)` for a term; a `define` also answers to its `_def` fact.
    scopes: list[dict[tuple[str, str], list[LocalBinding]]] = field(
        default_factory=lambda: [{}])
    # What opened each scope: the entry's own goal ("goal"), `proof`, `{`,
    # `subgoal`.  A subgoal ends with its first terminator, a block does not.
    kinds: list[str] = field(default_factory=lambda: ["goal"])
    end: int = 0                     # the line the entry's own proof ends on
    goals: dict[int, list[tuple[tuple[str, str], LocalBinding]]] = field(
        default_factory=dict)        # depth -> labels bound when proved
    pending: list[tuple[tuple[str, str], list[LocalBinding]]] = field(
        default_factory=list)        # bound at the end of this command
    this: list[LocalBinding] = field(default_factory=list)
    unfinished: bool = False         # a `sorry` / `oops` somewhere in it
    # A goal's proof has ended (`by`, `qed`, `done`, …) but the method after
    # it is still being read; its labels bind at the next command.
    proved: bool = False
    # Where the statement being read began, `(line, col)`; the bindings it
    # has made so far; whether it binds several facts (`a: … and b: …`).
    stmt_start: tuple[int, int] = (0, 0)
    stmt: list[LocalBinding] = field(default_factory=list)
    multi: bool = False

    def made(self, b: LocalBinding, outer: list[str]) -> None:
        """*b* is bound by the statement being read: give it its first line."""
        ln, col = self.stmt_start
        b.start = ln or b.line
        b.shared = bool(ln and outer[ln - 1][:col].strip())
        b.clause = self.multi
        self.stmt.append(b)

    def several(self) -> None:
        """An `and` between clauses: the statement binds more than one."""
        self.multi = True
        for b in self.stmt:
            b.clause = True

    def ends(self, bindings, last: int, next_line: int) -> None:
        """*bindings* end on line *last*; the next command starts on
        *next_line*, which shares it when they are equal."""
        for b in bindings:
            if b.start:
                b.end = last
                b.shared = b.shared or next_line == last

    def read(self, key: tuple[str, str]) -> None:
        for scope in reversed(self.scopes):
            if key in scope:
                for b in scope[key]:
                    b.read = True
                return

    def _facts(self):
        for scope in self.scopes:
            for (kind, _name), group in scope.items():
                if kind == "f":
                    yield from group

    def read_every_fact(self) -> None:
        """A bare `fact` method: it closes its goal with any fact in the
        context whose statement matches, so every visible one may be read."""
        for b in self._facts():
            b.read = True

    def read_statement(self, text: str) -> None:
        """A literal fact `‹P›`: whichever visible fact states `P`."""
        for b in self._facts():
            if text in b.stmts:
                b.read = True

    def settle(self, last: int, next_line: int) -> None:
        """The method that closed a goal has been read: bind its labels now,
        so `by (simp add: a)` in `have a: … by …` cites the OLD `a`.  The
        goal's lines end with that method, on line *last*."""
        if self.proved:
            self.proved = False
            self.ends(self.prove(), last, next_line)
            self.close_subgoal()

    def read_this(self) -> None:
        for b in self.this:
            b.read = True

    def bind(self, key: tuple[str, str], group: list[LocalBinding]) -> None:
        self.scopes[-1][key] = group

    def open(self, kind: str) -> None:
        self.scopes.append({})
        self.kinds.append(kind)

    def close(self) -> None:
        if len(self.scopes) > 1:
            self.scopes.pop()
            self.kinds.pop()

    def close_subgoal(self) -> None:
        """A terminator, or the `qed` of its `proof`, finishes a `subgoal`."""
        if self.kinds[-1] == "subgoal":
            self.close()

    def finish_command(self, last: int, next_line: int) -> None:
        """Bind what `note` / `define` / `let` wrote, now that it is done:
        its lines end on *last*."""
        if not self.pending:
            return
        facts: list[LocalBinding] = []
        for key, group in self.pending:
            self.bind(key, group)
            self.ends(group, last, next_line)
            if group and group[0].kind in ("note", "define"):
                facts.extend(b for b in group if b not in facts)
        if facts:
            self.this = facts
        self.pending = []

    def prove(self) -> list[LocalBinding]:
        """The goal open at the current depth is proved: bind its labels,
        and return them."""
        done = self.goals.pop(len(self.scopes), None)
        if done is None:
            return []
        for key, b in done:
            self.bind(key, [b])
        self.this = [b for _, b in done]
        return self.this


def _attr_words(toks: list[_Tok], i: int) -> tuple[set[str], int]:
    """The attribute names of the `[…]` opening at *i*, and the index after
    its `]`.  An attribute's name is the first word after `[` or `,`."""
    words: set[str] = set()
    depth, expect = 0, True
    j = i
    while j < len(toks):
        t = toks[j]
        if not t.inner:
            if t.text == "[":
                depth += 1
                expect = depth == 1
            elif t.text == "]":
                depth -= 1
                if depth == 0:
                    return words, j + 1
            elif t.text == "," and depth == 1:
                expect = True
            elif expect and depth == 1 and _is_name(t.text):
                words.add(t.text)
                expect = False
        j += 1
    return words, j


def _label_at(toks: list[_Tok], i: int, sep: str
              ) -> tuple[str, set[str], int] | None:
    """A label `NAME [attrs] SEP` starting at *i* — its name, attributes and
    the index after SEP — or None when *i* does not start one."""
    t = toks[i]
    if t.inner or not _is_name(t.text):
        return None
    j, attrs = i + 1, set()
    while j < len(toks) and toks[j].inner:
        j += 1
    if j < len(toks) and toks[j].text == "[":
        attrs, j = _attr_words(toks, j)
    if j < len(toks) and not toks[j].inner and toks[j].text == sep:
        return t.text, attrs, j + 1
    return None


def _stmts_at(toks: list[_Tok], i: int) -> list[str]:
    """The propositions written from *i* on, up to the next outer token:
    `"P" "Q"` after a label are both its statements."""
    out: list[str] = []
    while i < len(toks) and toks[i].inner:
        if toks[i].term is not None:
            out.append(toks[i].term)
        i += 1
    return out


def scan_proof(sec: TheorySection, entry: Entry,
               ignore: frozenset[tuple[int, int]] = frozenset()
               ) -> list[LocalBinding]:
    """Every name *entry*'s proof binds, each marked read or not.

    A statement premise is left out when the proof is unfinished: a `sorry`
    reads nothing, so every label of it would be reported, and none of them
    is litter."""
    if not entry.proof_line:
        return []
    w = _walk(sec, entry, ignore)
    if w.unfinished:
        return [b for b in w.bindings if b.kind not in _PREMISE_KINDS]
    return w.bindings


# A statement premise as a binding [unread-assumes]: its kind, and the name
# that reads every premise of that kind at once.
_PREMISE_KINDS = {"assumes": ("assms", "prems"), "if": ("that",)}
PREMISE_KINDS = frozenset(_PREMISE_KINDS)


def _seed_premises(sec: TheorySection, entry: Entry, w: "_Walk") -> None:
    r"""Bind *entry*'s labelled statement premises in the walk's outermost
    scope, before its proof is read (issue #20).

    A named `assumes` is proof-local exactly as a `have NAME:` is, and the
    commonest dead name after a refactor: the theorem it fed goes, and every
    caller still has to discharge it.  It is read when the proof cites it —
    `a`, `a(2)`, `a[THEN …]` — or cites the whole block: `assms` (and the
    legacy `prems`) for `assumes`, `that` for an `if` premise.  A label
    given a declaring attribute (`a [simp]:`) is used by that tool and never
    reported.  Unlabelled premises have no name of their own to report.
    """
    st = statement_of(sec, entry)
    if st is None:
        return
    live = sec.live_source()
    stmt_end = min(max(entry.proof_line, entry.thy_line), len(live))
    groups: dict[str, list[LocalBinding]] = {}
    seen: dict[str, LocalBinding] = {}
    for p in st.premises:
        if p.kind not in _PREMISE_KINDS:
            continue
        b = None
        if p.label:
            base = p.label.split("(", 1)[0]
            b = seen.get(base)
            if b is None:
                b = LocalBinding(base, p.kind, _label_line(
                    live, entry.thy_line, stmt_end, base), entry.name,
                    kept=bool(set(p.attrs) - TRANSFORMING_ATTRS))
                seen[base] = b
                w.bindings.append(b)
                w.bind(("f", base), [b])
            b.stmts.append(p.text)
        if b is not None:
            for whole in _PREMISE_KINDS[p.kind]:
                group = groups.setdefault(whole, [])
                if b not in group:
                    group.append(b)
    for whole, group in groups.items():
        w.bind(("f", whole), group)


def _label_line(live: list[str], lo: int, hi: int, label: str) -> int:
    """The line in ``lo..hi`` where ``label`` is written as `label [..]? :`."""
    pat = re.compile(rf"(?<![\w']){re.escape(label)}\s*(?:\[[^\]]*\]\s*)?:"
                     r"(?!:)")
    for ln in range(lo, hi + 1):
        if pat.search(live[ln - 1]):
            return ln
    return lo


def proof_end(sec: TheorySection, entry: Entry) -> int:
    """The line *entry*'s own proof ends on — its outermost `qed`, or the
    terminator that closes its goal — or 0 when the walk runs out first."""
    return _walk(sec, entry).end if entry.proof_line else 0


def _walk(sec: TheorySection, entry: Entry,
          ignore: frozenset[tuple[int, int]] = frozenset()) -> _Walk:
    """Walk *entry*'s proof from `proof_line` until its own goal is closed.

    The walk reads as far as `thy_end` but STOPS where the proof does.
    `thy_end` is too long: a command that proves something without being an
    entry — an `instance`, a `termination` — sits inside the previous entry's
    span, and its bindings are not this proof's.  `parsing._proof_close_line`
    walks the same structure for `body_end_line` [body-end-text]; over the AFP
    the two agree on all 297,954 proofs, and a test holds them together."""
    toks = _body_tokens(sec, entry)
    live_src, outer_src = sec.live_source(), sec.outer_source()
    if ignore:
        # `(line, col)` of name tokens that do not count as reads: the
        # `-r` premise cascade asks whether a label is read ELSEWHERE.
        toks = [t for t in toks if (t.line, t.col) not in ignore]
    w = _Walk(entry.name)
    _seed_premises(sec, entry, w)
    cmd = ""
    nest = 0              # parentheses + brackets: no command starts inside
    selection = 0         # the `nest` of a `name(…)` selection, or 0
    label_next = False    # the next token may be a label
    premises = False      # after `if` / `when`: labels local to the goal
    after_where = False
    variables = False     # names here are being bound, not read
    after_type = False    # after `::` in a variable list: a type, not a name
    define_group: list[LocalBinding] = []
    obtain_vars = False   # this `obtain` fixes variables before `where`
    # Past the entry's own closing `by` / `qed`: its method is still read —
    # `by (auto simp: a)` is where a statement premise is most often cited —
    # up to the next command, which is the end of the proof.
    closing = False
    # `from x` / `assume` rebind `this` when they FINISH: the `this` in
    # `from this` is still the previous fact.
    this_stale = False
    begun = False         # past the statement: a command has been read
    # In a cartouche of method text (`use x in ‹simp add: y›`): its names
    # cite facts as method text does, and are read as terms too, since a
    # read only ever removes a candidate [method-cartouche].
    method_text = False
    i = 0
    while i < len(toks):
        t = toks[i]
        s = t.text
        if not t.inner:
            method_text = False
        if s in ("sorry", "oops") and not t.inner:
            w.unfinished = True
        if t.term is not None:
            if (t.cartouche and cmd in _METHOD_CMDS
                    and _method_cartouche(outer_src, t)):
                method_text = True
            elif t.cartouche and cmd in _FACT_CMDS:
                w.read_statement(t.term)
            elif (not t.cartouche and cmd in _FACT_CMDS
                  and _QUOTED_NAME_RE.fullmatch(t.term)
                  and not _TERM_ARG_BEFORE_RE.search(
                      outer_src[t.line - 1][:t.col])):
                w.read(("f", _unqualified(t.term)))
            i += 1
            continue
        if t.inner:
            if not variables:
                w.read(("t", s))
            if method_text:
                if s == "this":
                    w.read_this()
                elif s == "fact" and _bare(live_src[t.line - 1],
                                           t.col + len(s)):
                    w.read_every_fact()
                elif not s.startswith("?"):
                    w.read(("f", _unqualified(s)))
            i += 1
            continue
        if s in "([":
            nest += 1
            label_next = False
            # `1(2)`, `assms(1)`: a selection, whose numerals are indices.
            # Glued to a command (`by(simp add: 1)`) it is a method.
            p = toks[i - 1] if i else None
            if (s == "(" and p is not None and not p.inner
                    and p.line == t.line and p.col + len(p.text) == t.col
                    and _is_name(p.text) and p.text not in _COMMANDS):
                selection = nest
            elif s == "(" and _after_quoted_name(toks, i, live_src):
                selection = nest    # `"**"(4)`
            i += 1
            continue
        if s in ")]":
            if nest == selection:
                selection = 0
            nest = max(0, nest - 1)
            i += 1
            continue
        if selection and s[0].isdigit():
            i += 1
            continue
        if nest == 0 and (s in _COMMANDS or s in ("{", "}", ".", "..")):
            if closing:
                break
            begun = True
            last = toks[i - 1].line if i else t.line
            w.settle(last, t.line)
            w.finish_command(last, t.line)
            if this_stale:
                w.this, this_stale = [], False
            if s in _CHAIN_READERS:
                w.read_this()
            this_stale = s in _THIS_RESETS
            if s in ("proof", "{", "subgoal"):
                w.open(s)
            elif s in ("qed", "}"):
                w.close()
                if s == "qed":
                    # Back at the entry's own goal: its outermost block closed.
                    # Asked before `close_subgoal`, which would also reach it.
                    if len(w.scopes) == 1:
                        w.end, closing, cmd = t.line, True, s
                        i += 1
                        continue
                    w.proved = True
            elif s == "next":
                w.close()
                w.open("proof")
            elif s in _TERMINATORS:
                if len(w.scopes) == 1:
                    w.end, closing, cmd = t.line, True, s
                    i += 1
                    continue
                w.proved = True
            if s in _GOAL_CMDS:
                w.goals[len(w.scopes)] = []
            if (s in _STMT_CMDS or s in _LEADS) and cmd not in _LEADS:
                w.stmt_start = (t.line, t.col)
            if s in _STMT_CMDS:
                w.stmt, w.multi, obtain_vars = [], False, False
            cmd = s
            label_next = s in ("have", "hence", "note", "let")
            premises = after_where = after_type = False
            variables = s in ("fix", "obtain", "define", "case")
            define_group = []
            i += 1
            continue
        if nest == 0 and s in ("and", "where", "if", "when", "for", "::"):
            if s == "::":
                after_type = True
            elif s == "for":
                variables, label_next = True, False
            elif s in ("if", "when"):
                premises, label_next = True, cmd in _LABELLED_GOALS
            elif s == "where":
                after_where, variables, after_type = True, False, False
                label_next = cmd in ("obtain", "define")
            else:   # and
                after_type = False
                if not (premises or variables) and (
                        cmd in _CLAUSE_CMDS
                        or (cmd in ("obtain", "define") and after_where)):
                    w.several()
                label_next = (cmd in ("have", "hence", "note", "let")
                              or (cmd in ("obtain", "define") and after_where))
            i += 1
            continue
        if label_next and cmd == "let" and s.startswith("?"):
            j = i + 1
            if j < len(toks) and toks[j].text == "=":
                b = LocalBinding(s, "let", t.line, entry.name)
                w.made(b, outer_src)
                w.bindings.append(b)
                w.pending.append((("t", s), [b]))
                label_next = False
                i = j + 1
                continue
        if label_next:
            label_next = False
            sep = "=" if cmd == "note" else ":"
            lab = _label_at(toks, i, sep)
            if lab is not None:
                name, attrs, after = lab
                # The attributes' arguments cite facts: `[unfolded I_defs]`.
                for u in toks[i + 1:after]:
                    if u.inner:
                        w.read(("t", u.text))
                    elif _is_name(u.text):
                        w.read(("f", _unqualified(u.text)))
                i = after
                if premises:
                    continue
                b = LocalBinding(name, cmd, t.line, entry.name,
                                 kept=bool(attrs - TRANSFORMING_ATTRS),
                                 stmts=_stmts_at(toks, after))
                if cmd == "define":
                    # A `where` label is another handle on the definitions.
                    w.pending.append((("f", name), define_group))
                    continue
                w.made(b, outer_src)
                b.binds_vars = cmd == "obtain" and obtain_vars
                w.bindings.append(b)
                if cmd == "note":
                    w.pending.append((("f", name), [b]))
                else:
                    w.goals.setdefault(len(w.scopes), []).append(
                        (("f", name), b))
                continue
        if variables:
            if (cmd == "obtain" and not after_where and not after_type
                    and _is_var(s)):
                obtain_vars = True
            # Only the names before `where`: a `for` after it binds a
            # parameter of the defining equation, not a new constant.
            if (cmd == "define" and not after_where and not after_type
                    and _is_var(s)):
                b = LocalBinding(s, "define", t.line, entry.name)
                w.made(b, outer_src)
                w.bindings.append(b)
                define_group.append(b)
                if len(define_group) > 1:
                    w.several()
                w.pending.append((("t", s), [b]))
                w.pending.append((("f", s + "_def"), [b]))
            i += 1
            continue
        if not begun:
            # Still in the statement (`lemma t: assumes p: "P" shows … by
            # simp` on one line): its words declare, and cite nothing local.
            pass
        elif s == "this":
            w.read_this()
        elif (s == "fact" and cmd in _METHOD_CMDS
              and _bare(live_src[t.line - 1], t.col + len(s))):
            w.read_every_fact()
        elif s.startswith("?"):
            w.read(("t", s))
        elif _is_name(s):
            w.read(("f", _unqualified(s)))
        i += 1
    return w


def span_text(label: str, b: LocalBinding) -> str:
    """The `--spans` cell of *b*, its theory printed as *label*
    [local-spans].  A bare `THY:A..B` is a delete span: removing those
    lines removes the binding and nothing else.  Anything else says why
    not, most binding reason first."""
    if not b.start:
        return "premise"
    if not b.end:
        return f"unclosed {label}:{b.start}"
    span = f"{label}:{b.start}..{b.end}"
    for tag, on in (("clause-of", b.clause), ("binds-vars", b.binds_vars),
                    ("shares-line", b.shared)):
        if on:
            return f"{tag} {span}"
    return span


def _unqualified(name: str) -> str:
    """`local.foo` is the proof-local `foo` — Isar's spelling for reaching
    past a same-named global fact."""
    return name[len("local."):] if name.startswith("local.") else name


Window = tuple[int, "int | None"]


def unread_locals(sections: list[TheorySection],
                  windows: dict[Path, list[Window]] | None = None,
                  keep: frozenset[str] = frozenset()
                  ) -> list[tuple[TheorySection, LocalBinding]]:
    """Every binding no reader reaches, over each section's proofs — or, for
    a section with *windows*, over the proofs overlapping any of them.

    A window selects whole proofs rather than binding lines: whether a name is
    read depends on the rest of its proof, and "which of these proofs did I
    leave litter in" is the question a diff hunk or a `largest` span asks."""
    windows = windows or {}
    out: list[tuple[TheorySection, LocalBinding]] = []
    for sec in sections:
        wins = windows.get(sec.path)
        for e in sec.entries:
            if not e.proof_line:
                continue
            if wins is not None:
                last = e.thy_end
                if not any(last >= lo and (hi is None or e.src_start <= hi)
                           for lo, hi in wins):
                    continue
            for b in scan_proof(sec, e):
                if not (b.read or b.kept or b.name in keep):
                    out.append((sec, b))
    return out


# --- `unused --locals -r`: the premise cascade [unread-assumes] -----------
#
# An unread premise is not harmless: every caller still discharges it, and the
# fact a caller discharges it WITH may exist for nothing else.  In
#
#     lemma clamp: assumes sig: "…" …          (`sig` unread)
#     theorem diag: assumes sig: "…" …
#       by (rule clamp [OF lang sig tge])
#
# `diag`'s own `sig` is read only to feed `clamp`'s dead one, so once that goes
# it is dead too.  The cascade follows positional `[OF …]` discharge only: a
# fact fed through `using` / `from` reaches a premise by unification, which
# no scan of the text can map to a position.

# A cited name followed by an attribute block: `clamp [OF …]`, `clamp[OF …]`.
_CITE_ATTR_RE = re.compile(r"(?<![\w'.])((?:[\w']+\.)*[\w']+)\s*\[")


def _premise_positions(sec: TheorySection, entry: Entry
                       ) -> dict[str, list[int]] | None:
    """``{label: [positions]}`` of *entry*'s labelled premises in the order
    `[OF …]` instantiates them (1-based), or None when that order is not
    the statement's: `defines` and `obtains` reshape the exported rule."""
    st = statement_of(sec, entry)
    if st is None or st.cases or any(p.kind == "defines"
                                     for p in st.premises):
        return None
    out: dict[str, list[int]] = {}
    for k, p in enumerate(st.premises, start=1):
        if p.kind in _PREMISE_KINDS and p.label:
            out.setdefault(p.label.split("(", 1)[0], []).append(k)
    return out


def _of_args(text: str, start: int) -> list[tuple[int, str, int]] | None:
    """The `[OF …]` arguments in the attribute block opening at
    ``text[start] == '['``: ``(position, head name, offset)`` for each, the
    head name '' for `_` or a parenthesised fact.  None without an `OF`."""
    depth, quote, j = 0, "", start
    items: list[tuple[int, int]] = []          # (start, end) at depth 1
    item_start = start + 1
    while j < len(text):
        ch = text[j]
        if quote:
            quote = "" if ch == quote else quote
        elif ch == '"':
            quote = ch
        elif ch in "[(":
            depth += 1
        elif ch in "])":
            depth -= 1
            if depth == 0:
                items.append((item_start, j))
                break
        elif ch == "," and depth == 1:
            items.append((item_start, j))
            item_start = j + 1
        j += 1
    for lo, hi in items:
        m = re.match(r"\s*OF\b", text[lo:hi])
        if not m:
            continue
        args: list[tuple[int, str, int]] = []
        k, depth = lo + m.end(), 0
        while k < hi:
            ch = text[k]
            if ch.isspace():
                k += 1
                continue
            if ch in "[(":
                # An attribute block glues to the argument before it; a
                # parenthesised fact is an argument of its own.
                if ch == "(":
                    args.append((len(args) + 1, "", k))
                e = _balanced(text, k, hi)
                k = e
                continue
            mw = re.match(r"_(?![\w'])|(?:[\w']+\.)*[\w']+", text[k:hi])
            if not mw:
                k += 1
                continue
            word = mw.group(0)
            args.append((len(args) + 1, "" if word == "_" else word, k))
            k += mw.end()
        return args
    return None


def _balanced(text: str, k: int, hi: int) -> int:
    """The offset just past the bracket or parenthesis opening at *k*."""
    depth, quote = 0, ""
    while k < hi:
        ch = text[k]
        if quote:
            quote = "" if ch == quote else quote
        elif ch == '"':
            quote = ch
        elif ch in "[(":
            depth += 1
        elif ch in "])":
            depth -= 1
            if depth == 0:
                return k + 1
        k += 1
    return hi


def premise_cascade(sections: list[TheorySection],
                    dead: list[tuple[TheorySection, LocalBinding]],
                    keep: frozenset[str] = frozenset()
                    ) -> list[tuple[TheorySection, LocalBinding, str]]:
    """The premises that become unread once the *dead* ones go, each with the
    ``LEMMA.label`` it only fed, to a fixed point.

    A caller's label is reported when it discharges an unread premise by
    position (`clamp [OF … sig …]`) and nothing else in its proof reads it —
    asked by walking the proof again with those discharging tokens removed.
    """
    # lemma name -> {position: "lemma.label"} for its unread premises.
    targets: dict[str, dict[int, str]] = {}
    # lemma name -> its locale / class target.  Cited from outside that
    # target, the lemma's exported rule has the target's assumptions in
    # front, and every `[OF …]` position shifts; such a discharge is not
    # followed rather than mapped to the wrong premise.
    homes: dict[str, str] = {}

    def add_target(sec: TheorySection, b: LocalBinding) -> None:
        # The dead row's own section, not a lookup in *sections*: under
        # `unused --locals PATH -r` the rows come from a selection parsed on
        # its own, while the callers are searched for over the whole project.
        e = next((e for e in sec.entries if e.name == b.entry
                  and e.thy_line <= b.line <= e.thy_end), None)
        if e is None:
            return
        pos = _premise_positions(sec, e)
        if pos and b.name in pos:
            homes[b.entry] = e.target
            for k in pos[b.name]:
                targets.setdefault(b.entry, {})[k] = f"{b.entry}.{b.name}"

    for sec, b in dead:
        if b.kind in _PREMISE_KINDS:
            add_target(sec, b)
    reported = {(sec.path.resolve(), b.entry, b.name) for sec, b in dead}
    out: list[tuple[TheorySection, LocalBinding, str]] = []
    while targets:
        fresh: dict[str, dict[int, str]] = {}
        for sec in sections:
            live = sec.live_source()
            for e in sec.entries:
                if not e.proof_line:
                    continue
                hits = [h for h in _discharges(live, e, targets)
                        if homes.get(h[3].rsplit(".", 1)[0], "") == e.target]
                if not hits:
                    continue
                labels = {b.name: b for b in scan_proof(sec, e)
                          if b.kind in _PREMISE_KINDS}
                # label -> every dead premise it discharges here, in order.
                vias: dict[str, list[str]] = {}
                fed: set[tuple[int, int]] = set()
                for name, ln, col, via in hits:
                    if name in labels and labels[name].read:
                        fed.add((ln, col))
                        if via not in vias.setdefault(name, []):
                            vias[name].append(via)
                if not fed:
                    continue
                again = {b.name: b for b in scan_proof(sec, e,
                                                        frozenset(fed))}
                for name, via in vias.items():
                    b = again.get(name)
                    key = (sec.path.resolve(), e.name, name)
                    if (b is None or b.read or b.kept or name in keep
                            or key in reported):
                        continue
                    reported.add(key)
                    out.append((sec, b, ", ".join(via)))
                    pos = _premise_positions(sec, e)
                    if pos and name in pos:
                        homes[e.name] = e.target
                        for k in pos[name]:
                            fresh.setdefault(e.name, {})[k] = \
                                f"{e.name}.{name}"
        targets = fresh
    return out


def _discharges(live: list[str], e: Entry, targets: dict[str, dict[int, str]]
                ) -> list[tuple[str, int, int, str]]:
    """``(arg name, line, col, "lemma.label")`` for each `[OF …]` argument in
    *e*'s proof that discharges a *targets* premise."""
    out: list[tuple[str, int, int, str]] = []
    end = min(e.thy_end or len(live), len(live))
    lines = live[e.proof_line - 1:end]
    text = "\n".join(lines)
    if "[" not in text:
        return out
    starts = [0]
    for ln in lines:
        starts.append(starts[-1] + len(ln) + 1)
    for m in _CITE_ATTR_RE.finditer(text):
        cited = m.group(1).rsplit(".", 1)[-1]
        want = targets.get(cited) or targets.get(m.group(1))
        if not want:
            continue
        args = _of_args(text, m.end() - 1)
        for k, name, off in args or ():
            if name and k in want:
                row = bisect_right(starts, off) - 1
                out.append((name, e.proof_line + row, off - starts[row],
                            want[k]))
    return out
