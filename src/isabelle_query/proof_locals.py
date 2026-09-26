r"""Proof-local names bound and never read (issue #12).

``unused`` asks which DECLARATIONS nothing cites, over the citation graph
between entries.  This asks the same question one level down, inside a single
proof body: which ``have NAME:``, ``obtain … where NAME:``, ``note NAME =``,
``define NAME`` or ``let ?NAME`` binds a name that nothing in its scope reads.
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
  label is bound when the statement's proof finishes, not when it is written.
  ``note`` / ``define`` / ``let`` bind at the end of their own command.
* **``this``.**  A fact consumed by chaining (``then``, ``hence``, ``thus``,
  ``with``, ``moreover``, ``ultimately``, ``also``, ``finally``, or a written
  ``this``) is used although its name is not.  That label is redundant rather
  than dead, and the question here is about dead facts, so it is not reported.

A labelled fact given a declaring attribute (``have s [simp]:``) is read by
the rule set it joined and is never reported; a transforming attribute
(``[rule_format]``, ``[symmetric]``) adds it to nothing and does not protect it.

The result is a list of CANDIDATES, not a delete list, because the errors run
both ways.  A fact can be used where no scan of the proof sees its name —
through a bundle cited under another name, by position (``case`` numbering
such as ``1(2)``), by its statement (``using ‹P›``), or by an ``obtain`` whose
hand-written ``that`` must match its supplier clause for clause — and is then
reported although it is needed.  The other way, a token that merely spells the
name (a same-named variable in outer syntax) counts as a reader, and a binding
goes unreported.  Over the AFP, 3.1% of 241,176 bindings are reported.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from string import ascii_letters

from isabelle_query.graph import (
    CLOSING_KEYWORDS, CONTEXT_KEYWORDS, GOAL_KEYWORDS, PLUMBING_KEYWORDS,
    _noise_spans)
from isabelle_query.model import Entry, TheorySection
from isabelle_query.parsing import LETTER_SYMS

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
# surface as a word, and then dropped (the `sym` group).
_TOKEN_RE = re.compile(
    rf"(\?{_NAME})|({_NAME}(?:\.{_NAME})*)|(?P<sym>\\<\^?\w+>)"
    rf"|(\.\.|::|[.{{}}()\[\]:=,])")
_TERM_TOKEN_RE = re.compile(rf"\??{_NAME}|(?P<sym>\\<\^?\w+>)")

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
# Attributes that change the fact rather than declare it into a rule set, so a
# label carrying only these is as unread as a bare one.
_TRANSFORMING_ATTRS = frozenset({
    "rule_format", "symmetric", "THEN", "OF", "of", "where", "unfolded",
    "folded", "simplified", "abs_def", "elim_format", "rotated", "consumes",
    "case_names", "format", "standard", "untagged", "no_vars", "to_pred",
    "to_set", "atomize", "rulify", "transferred", "param"})


@dataclass
class LocalBinding:
    """A name one proof binds.  ``line`` is 1-indexed in the theory."""
    name: str       # as written: `a`, `?p`
    kind: str       # have / hence / obtain / note / define / let
    line: int
    entry: str
    read: bool = False
    kept: bool = False   # declared into a rule set by one of its attributes


@dataclass
class _Tok:
    line: int
    col: int
    text: str
    inner: bool          # a name inside a term, not outer syntax


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
        toks: list[_Tok] = []
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


def _word_char(ch: str) -> bool:
    return ch.isalnum() or ch in "_'?"


def _is_name(tok: str) -> bool:
    """A name token, as opposed to punctuation.  Not `isalpha()`: a name may
    begin with a letter SYMBOL, and `define \\<epsilon> where` is common."""
    return tok[0].isalpha() or tok[0] == "\\"


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

    def read(self, key: tuple[str, str]) -> None:
        for scope in reversed(self.scopes):
            if key in scope:
                for b in scope[key]:
                    b.read = True
                return

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

    def finish_command(self) -> None:
        """Bind what `note` / `define` / `let` wrote, now that it is done."""
        if not self.pending:
            return
        facts: list[LocalBinding] = []
        for key, group in self.pending:
            self.bind(key, group)
            if group and group[0].kind in ("note", "define"):
                facts.extend(b for b in group if b not in facts)
        if facts:
            self.this = facts
        self.pending = []

    def prove(self) -> None:
        """The goal open at the current depth is proved: bind its labels."""
        done = self.goals.pop(len(self.scopes), None)
        if done is None:
            return
        for key, b in done:
            self.bind(key, [b])
        self.this = [b for _, b in done]


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


def scan_proof(sec: TheorySection, entry: Entry) -> list[LocalBinding]:
    """Every name *entry*'s proof binds, each marked read or not."""
    return _walk(sec, entry).bindings if entry.proof_line else []


def proof_end(sec: TheorySection, entry: Entry) -> int:
    """The line *entry*'s own proof ends on — its outermost `qed`, or the
    terminator that closes its goal — or 0 when the walk runs out first."""
    return _walk(sec, entry).end if entry.proof_line else 0


def _walk(sec: TheorySection, entry: Entry) -> _Walk:
    """Walk *entry*'s proof from `proof_line` until its own goal is closed.

    The walk reads as far as `thy_end` but STOPS where the proof does.
    `thy_end` is too long: a command that proves something without being an
    entry — an `instance`, a `termination` — sits inside the previous entry's
    span, and its bindings are not this proof's.  `parsing._proof_close_line`
    walks the same structure for `body_end_line` [body-end-text]; over the AFP
    the two agree on all 297,954 proofs, and a test holds them together."""
    toks = _body_tokens(sec, entry)
    w = _Walk(entry.name)
    cmd = ""
    nest = 0              # parentheses + brackets: no command starts inside
    label_next = False    # the next token may be a label
    premises = False      # after `if` / `when`: labels local to the goal
    after_where = False
    variables = False     # names here are being bound, not read
    after_type = False    # after `::` in a variable list: a type, not a name
    define_group: list[LocalBinding] = []
    # `from x` / `assume` rebind `this` when they FINISH: the `this` in
    # `from this` is still the previous fact.
    this_stale = False
    i = 0
    while i < len(toks):
        t = toks[i]
        s = t.text
        if t.inner:
            if not variables:
                w.read(("t", s))
            i += 1
            continue
        if s in "([":
            nest += 1
            label_next = False
            i += 1
            continue
        if s in ")]":
            nest = max(0, nest - 1)
            i += 1
            continue
        if nest == 0 and (s in _COMMANDS or s in ("{", "}", ".", "..")):
            w.finish_command()
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
                        w.end = t.line
                        break
                    w.prove()
                    w.close_subgoal()
            elif s == "next":
                w.close()
                w.open("proof")
            elif s in _TERMINATORS:
                if len(w.scopes) == 1:
                    w.end = t.line
                    break
                w.prove()
                w.close_subgoal()
            if s in _GOAL_CMDS:
                w.goals[len(w.scopes)] = []
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
                label_next = (cmd in ("have", "hence", "note", "let")
                              or (cmd in ("obtain", "define") and after_where))
            i += 1
            continue
        if label_next and cmd == "let" and s.startswith("?"):
            j = i + 1
            if j < len(toks) and toks[j].text == "=":
                b = LocalBinding(s, "let", t.line, entry.name)
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
                                 kept=bool(attrs - _TRANSFORMING_ATTRS))
                if cmd == "define":
                    # A `where` label is another handle on the definitions.
                    w.pending.append((("f", name), define_group))
                    continue
                w.bindings.append(b)
                if cmd == "note":
                    w.pending.append((("f", name), [b]))
                else:
                    w.goals.setdefault(len(w.scopes), []).append(
                        (("f", name), b))
                continue
        if variables:
            # Only the names before `where`: a `for` after it binds a
            # parameter of the defining equation, not a new constant.
            if (cmd == "define" and not after_where and not after_type
                    and _is_name(s)):
                b = LocalBinding(s, "define", t.line, entry.name)
                w.bindings.append(b)
                define_group.append(b)
                w.pending.append((("t", s), [b]))
                w.pending.append((("f", s + "_def"), [b]))
            i += 1
            continue
        if s == "this":
            w.read_this()
        elif s.startswith("?"):
            w.read(("t", s))
        elif _is_name(s):
            w.read(("f", _unqualified(s)))
        i += 1
    return w


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
