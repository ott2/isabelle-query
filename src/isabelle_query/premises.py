r"""What a fact's statement assumes, one premise at a time [show-premises].

`show --premises` answers the question an abstract-versus-theorem audit asks:
what does this theorem assume, and how is each assumption cited?  It is short
by construction — one line per premise, then a count of conclusions — so it
needs no truncating however long the conclusion is (issue #17).

The layer after ``parsing`` (it reuses the balanced-delimiter scanner), below
``render``, which formats what this returns.

A statement states its premises in one of three ways, measured over the AFP's
297,456 facts by ``scripts/probe_premise_forms.py``:

    assumes a: "P" "Q" and "R" shows "C"     34%   premises cited as assms(k)
    "C" if a: "P" for x                       1%   premises cited as that(k)
    "P \<Longrightarrow> Q \<Longrightarrow> C"                 28%   premises inside the term

and 42% have none.  Each premise is reported with the name a proof can cite
it by — `assms(k)` / `that(k)`, numbered across every element as Isabelle
numbers them, plus its own label where it has one — because in the AFP only
22% of `assumes` statements label any premise at all.  A premise written
inside the term has no such name, so it is numbered by position alone.

Read on the LIVE view (noise blanked), tokenised here: the outer view blanks
a term whole, delimiters included, so `"P" "Q"` and `"P Q"` look alike there.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field

from isabelle_query.model import Entry, TheorySection
from isabelle_query.parsing import _balanced_end

# Isar statement elements (`Pure.thy`, `Parse_Spec.statement`).
_ELEMENTS = frozenset({"fixes", "constrains", "assumes", "defines", "notes",
                       "includes", "shows", "obtains"})
# Where the statement ends: the first proof command.
_PROOF_WORDS = frozenset({"by", "proof", "apply", "using", "unfolding",
                          "including", "supply", "sorry", "oops", "done",
                          "nitpick", "sledgehammer"})

# A cartouche delimiter is not part of a word: `shows\<open>P\<close>` is
# written with no space between them.
_WORD_RE = re.compile(r"(?:\\<(?!open>|close>)\^?\w+>|[\w'.?])+")


@dataclass
class Premise:
    kind: str     # "assumes" | "if" | "defines" | "term"
    cite: str     # `assms(2)` / `that(1)`; "" when there is no such name
    label: str    # the premise's own label, `wf` or `wf(2)`; "" if none
    text: str     # the proposition, delimiters stripped, whitespace collapsed


@dataclass
class Statement:
    premises: list[Premise] = field(default_factory=list)
    conclusions: int = 0
    cases: int = 0    # `obtains` alternatives; 0 when there is no `obtains`


def _tokens(s: str) -> list[tuple[str, str]]:
    """`(kind, text)` tokens: term, attr, paren, word, punct.

    A term is a `"..."` string or a cartouche, with its delimiters stripped.
    An unterminated one runs to the end, which is where a statement slice
    that stops early would leave it."""
    out: list[tuple[str, str]] = []
    i, n = 0, len(s)
    while i < n:
        c = s[i]
        if c.isspace():
            i += 1
        elif c == '"':
            j = i + 1
            while j < n and not (s[j] == '"' and s[j - 1] != "\\"):
                j += 1
            out.append(("term", s[i + 1:j]))
            i = j + 1
        elif s.startswith("\\<open>", i) or c == "‹":
            op, cl = (("\\<open>", "\\<close>") if c == "\\"
                      else ("‹", "›"))
            j = _balanced_end(s, op, cl, start=i)
            end = j if j >= 0 else n
            out.append(("term", s[i + len(op):end - (len(cl) if j >= 0
                                                     else 0)]))
            i = end
        elif c in "[(":
            j = _balanced_end(s, c, "]" if c == "[" else ")", start=i,
                              quote_aware=True)
            end = j if j >= 0 else n
            out.append(("attr" if c == "[" else "paren", s[i:end]))
            i = end
        else:
            m = _WORD_RE.match(s, i)
            if m and not (m.group() in (".", "..")):
                out.append(("word", m.group()))
                i = m.end()
            elif s.startswith("::", i):
                out.append(("punct", "::"))
                i += 2
            else:
                # `.` / `..` (proof by default/rule) and lone symbols.
                j = i + 2 if s.startswith("..", i) else i + 1
                out.append(("punct", s[i:j]))
                i = j
    return out


def _collapse(t: str) -> str:
    return " ".join(t.split())


# --- premises written inside the term --------------------------------------

_IMPS = ("\\<Longrightarrow>", "⟹", "==>")
_PAIRS = {"(": ")", "[": "]", "{": "}", "\\<lbrakk>": "\\<rbrakk>",
          "⟦": "⟧", "\\<open>": "\\<close>", "‹": "›"}
_CLOSERS = frozenset(_PAIRS.values())
_BINDERS = ("\\<And>", "⋀", "!!")


def _scan(t: str, at_depth0):
    """Walk `t` tracking bracket depth; call `at_depth0(i)` at each depth-0
    position, which returns how far to skip (0 = one char) or -1 to stop."""
    depth, i, n = 0, 0, len(t)
    while i < n:
        opener = next((o for o in _PAIRS if t.startswith(o, i)), None)
        if opener:
            depth += 1
            i += len(opener)
            continue
        closer = next((c for c in _CLOSERS if t.startswith(c, i)), None)
        if closer:
            depth -= 1
            i += len(closer)
            continue
        if depth == 0:
            step = at_depth0(i)
            if step < 0:
                return
            if step:
                i += step
                continue
        i += 1


def _strip_binders(t: str) -> str:
    r"""`\<And>x y. body` -> `body`: an outermost meta-quantifier scopes the
    whole proposition, and its premises are the body's."""
    t = t.strip()
    while t.startswith(_BINDERS):
        dot = t.find(".")
        if dot < 0:
            break
        t = t[dot + 1:].strip()
    return t


def split_imp(t: str) -> list[str]:
    r"""The premises and conclusion of `P \<Longrightarrow> Q \<Longrightarrow> C`,
    split at the outermost implications: `[P, Q, C]`.

    Only depth 0 splits, so `(A \<Longrightarrow> B) \<Longrightarrow> C` has
    the one premise `A \<Longrightarrow> B`.  A meta-quantifier met after the
    first split scopes the rest, which is then one piece.  A premise written as
    `\<lbrakk>A; B\<rbrakk>` is the two premises A and B."""
    t = _strip_binders(t)
    cuts: list[tuple[int, int]] = []

    def visit(i: int) -> int:
        if cuts and t.startswith(_BINDERS, i):
            return -1
        for imp in _IMPS:
            # `===>` (`rel_fun`) is not `==>`.
            if t.startswith(imp, i) and not (imp == "==>" and i
                                             and t[i - 1] in "=-"):
                cuts.append((i, i + len(imp)))
                return len(imp)
        return 0

    _scan(t, visit)
    pieces, lo = [], 0
    for a, b in cuts:
        pieces.append(t[lo:a].strip())
        lo = b
    pieces.append(t[lo:].strip())
    out: list[str] = []
    for p in pieces[:-1]:
        out.extend(_split_lbrakk(p))
    return out + pieces[-1:]


def _split_lbrakk(p: str) -> list[str]:
    for op, cl in (("\\<lbrakk>", "\\<rbrakk>"), ("⟦", "⟧")):
        if p.startswith(op) and _balanced_end(p, op, cl) == len(p):
            inner = p[len(op):-len(cl)]
            parts, lo = [], 0
            semis: list[int] = []

            def visit(i: int) -> int:
                if inner[i] == ";":
                    semis.append(i)
                return 0

            _scan(inner, visit)
            for k in semis:
                parts.append(inner[lo:k].strip())
                lo = k + 1
            parts.append(inner[lo:].strip())
            return [x for x in parts if x]
    return [p]


# --- the statement ---------------------------------------------------------

def _groups(toks, i, stop):
    """`(label, [terms])` groups separated by `and`, from token `i` up to the
    first token `stop(tok)` accepts.  Returns `(groups, next index)`."""
    groups: list[tuple[str, list[str]]] = []
    label, terms = "", []
    while i < len(toks) and not stop(toks[i]):
        kind, text = toks[i]
        if kind == "word" and text == "and":
            groups.append((label, terms))
            label, terms = "", []
        elif kind == "word":
            # `name [attrs]? :` labels the group; any other word is a
            # proposition written bare -- `shows False`, `assumes trans` --
            # which Isar accepts for a single-token term.
            j = i + 1
            if j < len(toks) and toks[j][0] == "attr":
                j += 1
            if not terms and j < len(toks) and toks[j] == ("punct", ":"):
                label = text
                i = j
            else:
                terms.append(text)
        elif kind == "term":
            terms.append(_collapse(text))
        i += 1
    groups.append((label, terms))
    return [g for g in groups if g[1]], i


def _is_proof(tok) -> bool:
    return (tok[0] == "word" and tok[1] in _PROOF_WORDS) \
        or tok in (("punct", "."), ("punct", ".."))


def read_statement(text: str) -> Statement | None:
    """Parse a goal statement starting at its command word.  None when it is
    not one this reader understands, so a caller can say so rather than
    print a wrong count."""
    toks = _tokens(text)
    if not toks or toks[0][0] != "word":
        return None
    i = 1
    while i < len(toks) and toks[i][0] == "paren":       # `(in loc)`
        i += 1
    # `name [attrs]? :` or `[attrs] :`
    j = i
    if j < len(toks) and toks[j][0] == "word" \
            and toks[j][1] not in _ELEMENTS and not _is_proof(toks[j]):
        j += 1
    if j < len(toks) and toks[j][0] == "attr":
        j += 1
    if j > i and j < len(toks) and toks[j] == ("punct", ":"):
        i = j + 1

    st = Statement()
    assms = that = 0

    def add(kind, groups):
        nonlocal assms, that
        for label, terms in groups:
            for k, t in enumerate(terms, start=1):
                lab = (label if len(terms) == 1 or not label
                       else f"{label}({k})")
                if kind == "assumes":
                    assms += 1
                    cite = f"assms({assms})"
                elif kind == "if":
                    that += 1
                    cite = f"that({that})"
                else:
                    cite = ""
                st.premises.append(Premise(kind, cite, lab, t))

    def at_element(tok) -> bool:
        return (tok[0] == "word" and tok[1] in _ELEMENTS) or _is_proof(tok)

    shows: list[str] = []
    if i < len(toks) and toks[i][0] == "word" and toks[i][1] in _ELEMENTS:
        while i < len(toks) and not _is_proof(toks[i]):
            kw = toks[i][1] if toks[i][0] == "word" else ""
            i += 1
            if kw in ("assumes", "defines", "shows"):
                groups, i = _groups(toks, i, at_element)
                if kw == "shows":
                    shows += [t for _l, ts in groups for t in ts]
                else:
                    add(kw, groups)
            elif kw == "obtains":
                st.cases = 1
                while i < len(toks) and not at_element(toks[i]):
                    if toks[i] == ("punct", "|"):
                        st.cases += 1
                    i += 1
            else:
                while i < len(toks) and not at_element(toks[i]):
                    i += 1
    else:
        def short_stop(tok) -> bool:
            return _is_proof(tok) or tok in (("word", "if"), ("word", "for"))
        groups, i = _groups(toks, i, short_stop)
        shows = [t for _l, ts in groups for t in ts]
        if i < len(toks) and toks[i] == ("word", "if"):
            groups, i = _groups(toks, i + 1, short_stop)
            add("if", groups)

    st.conclusions = len(shows)
    if not shows and not st.cases:
        return None
    if len(shows) == 1:
        pieces = split_imp(shows[0])
        for k, p in enumerate(pieces[:-1], start=1):
            st.premises.append(Premise("term", "", "", _collapse(p)))
    return st


def statement_of(sec: TheorySection, e: Entry) -> Statement | None:
    """The parsed statement of a LEMMA/THEOREM entry, else None."""
    if e.tag not in ("LEMMA", "THEOREM") or not e.thy_line:
        return None
    live = sec.live_source()
    # `decl_end_line` stops at a blank inside the statement, where the proof
    # search does not, so read on to the proof line.  The proof words end
    # the parse, so a one-line proof is no harm.
    end = max(e.decl_end_line, e.proof_line or 0, e.thy_line)
    return read_statement("\n".join(live[e.thy_line - 1:end]))
