r"""Proof-shape metrics — per-step measurements over Isar proof bodies.

The ``shape`` subcommand family measures the *shape* of individual proof steps
across seven incomparable axes — length, depth, width, space, redundancy,
automation, and framing.  Proof *width* (how many symbols a stated
proposition mentions) is only one of them; the family also counts how many facts
are simultaneously live, how many are cited per step, how much is re-said, and
how goals are discharged.  Width here is the proof-complexity analog of line
width (the size of an individual line), as opposed to line *count* (depth) or
proof-state size.

Everything is **source-level** — computed by re-aggregating what ``parsing`` and
``graph`` already extract, with no Isabelle process.  This module owns the one
new primitive the rest of the tool lacks: a *step* scanner.

The step model
--------------
The existing parser sees a proof body as an opaque span (``Entry.proof_line`` ..
``Entry.body_end_line``) with a nested *block* structure (``commands._proof_blocks``).
Neither resolves the individual Isar commands — the ``have`` / ``show`` /
``from`` / ``by`` lines — that width metrics attach to.  :func:`_scan_steps`
adds exactly that: it walks the live lines of one proof body and classifies each
into one of four kinds (the keyword sets are shared with ``graph``):

* **goal**  — states or derives a proposition: ``have`` ``show`` ``hence``
  ``thus`` ``obtain`` ``consider`` ``also`` ``finally`` ``interpret``.
  Metrics attach here.
* **context** — introduces variables/assumptions: ``fix`` ``assume``
  ``presume`` ``define`` ``let`` ``case``.
* **plumbing** — moves facts without stating a goal: ``from`` ``using`` ``with``
  ``note`` ``moreover`` ``ultimately`` ``then``.
* **closing** — discharges a goal: ``by`` ``apply`` ``done`` ``qed`` ``.`` ``..``.

Classification is deliberately conservative and *line-anchored*, matching the
tool's existing scanners (``graph._scan_methods``, ``commands._proof_blocks``):
one step per live proof line, keyed on the leading command sequence.  A line may
combine kinds — ``from a have b: "P" by simp`` is plumbing + goal + closing — so
a goal-stating command anywhere in the line's *command prefix* (the text before
its **proposition**) wins the classification, and the leading plumbing /
trailing closing are recorded on the goal :class:`Step` as fan-in sources.  A
multi-command physical line is attributed to its goal command; the undercount of
genuinely multi-*statement* lines matches the ethos of ``_scan_methods``
(undercount, never overcount).

Locating that proposition is the delicate part, and getting it wrong cost 3.2%
of the corpus's goal steps until issue #9.  It is *not* simply the line's first
``"`` / ``\<open>``: a delimiter reached before any goal keyword is a **fact
reference** in command position (``from \<open>P\<close> have "Q"``), and a
command's line may carry no delimiter at all because its proposition **wrapped**
onto the next.  Both are handled — see :func:`_split_command_prefix` and
:func:`_statement_wrapped` — and both mattered because their rates track
writing style rather than proof content, so they moved measurements in the same
direction as a style trend.  Neither raised nor warned; each simply produced a
record with a smaller number in it.

This module is the authoritative reference for the metric definitions.  The
exact-vs-estimator split, the reference (elaborated-term) semantics standing
behind each estimator, and the known approximations are stated at each metric
below; ``METRICS.md`` decodes the ``M1``–``M6`` identifiers and groups them into
axes.  Definitions live here rather than in prose because a separate document
drifts from the code and this one cannot.

Depends only on ``model``, ``parsing`` (source tokenisation primitives), and
``graph`` (``_noise_spans`` for the prose skip) — never on rendering or the CLI.
"""

from __future__ import annotations

import re
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from typing import NamedTuple

from isabelle_query import graph
from isabelle_query.model import Entry, TheorySection
from isabelle_query.parsing import (
    ISA_WORD_CHAR, LETTER_SYMS, PROOF_RE, _PROOF_INLINE_RE, _balanced_end)
from isabelle_query.graph import (
    CLOSING_KEYWORDS as _CLOSING_KEYWORDS,
    CONTEXT_KEYWORDS as _CONTEXT_KEYWORDS,
    GOAL_KEYWORDS as _GOAL_KEYWORDS,
    PLUMBING_KEYWORDS as _PLUMBING_KEYWORDS,
    _cited_facts_on_line,
    _leading_method,
    _noise_spans,
)
from isabelle_query._corpus_constants import CORPUS_CONSTANTS
from isabelle_query._notation import NOTATION
# The method / attribute / keyword tables live authoritatively in `graph` (the
# reconfigurable single source of truth), read late-bound in `classify_identifier`
# so a CLI-dispatch `graph.configure_namespace(...)` is seen here too — the shape
# identifier classifier and the citation router never diverge on what a token is.

# --- step classification ---------------------------------------------------
#
# The four command families are defined once in
# `graph` (the shared analysis layer, where the fact extractor also reads them)
# and imported above.  They are *bare* leading keywords of a proof-body command;
# a keyword only counts in command position (before the proposition), never
# inside a term — the classifier looks only at the line's command prefix, so a
# `have` inside a quoted statement does not register.

# Structural keywords that open / close a nested block (tracked for depth, and
# never a step of their own).  `proof` and a lone `{` open; `qed` and `}` close.
# `next` and `case` sit inside a `proof (induction ...)` but do not nest.
_BLOCK_OPEN_RE = re.compile(r"^proof\b|^\{")
_BLOCK_CLOSE_RE = re.compile(r"^qed\b|^\}")

# The proposition of a goal step is written as a double-quoted string `"P"` or a
# cartouche `\<open>P\<close>`; the command prefix is everything before it.
_PROP_START_RE = re.compile(r'"|\\<open>')
# Command-position tokens: identifiers/keywords and the bare-dot proof terminators.
_CMD_TOKEN_RE = re.compile(r"\.\.|\.|[A-Za-z][\w']*")


def _split_command_prefix(text: str) -> tuple[str, int]:
    r"""Split a proof line into its command prefix and its proposition.

    Returns ``(prefix, prop_col)``: the command keywords and fact names before
    the proposition, and the column where the proposition opens (``-1`` when the
    line states none — `by simp`, `qed`, `moreover`, `show ?thesis`).

    A `"` or `\<open>` is **not** by itself evidence of a proposition, which is
    the whole subtlety here.  Modern Isar cites a fact by writing it out, so
    `from \<open>P\<close> have "Q"` opens a cartouche in *command* position: it
    is a fact reference, and the proposition is further right.  A delimiter
    reached before any goal keyword is therefore skipped, and only a delimiter
    after one starts the proposition.

    Stopping at the first opener instead — what this did — made the `have`
    invisible, so the line booked as `plumbing` and its goal was never emitted:
    **2.68% of AFP goal steps** (issue #9).  The consequence was not only an
    undercount.  The lost goal's facts stayed pending and attached to the *next*
    goal, so a `show ?thesis` was recorded as citing a premise it does not cite;
    and `fanin_mean` *rose*, because the lost goal shrank the denominator.  The
    backtick and bare spellings (`from p have`) were never affected, so the
    error grew as a development adopted current style — a scanner artifact
    moving with the style trend is the kind that survives a release comparison.

    Skipped spans are **blanked, not deleted**, so a column into the prefix is
    still a column into the line (`_STEP_LABEL_RE` searches it) and no token
    inside a cited term can read as a command keyword.

    Cartouches nest, so the skip uses the package's balanced scanner rather
    than a non-greedy regex, which would stop at the first `\<close>` and leave
    the outer one stranded in the prefix.
    """
    out: list[str] = []
    i = 0
    seen_goal = False
    while True:
        m = _PROP_START_RE.search(text, i)
        if m is None:
            out.append(text[i:])
            return "".join(out), -1
        segment = text[i:m.start()]
        out.append(segment)
        if not seen_goal:
            seen_goal = any(t in _GOAL_KEYWORDS
                            for t in _CMD_TOKEN_RE.findall(segment))
        if seen_goal:
            return "".join(out), m.start()
        # A fact reference in command position: skip its balanced span.
        if text[m.start()] == '"':
            close = text.find('"', m.start() + 1)
            end = close + 1 if close >= 0 else -1
        else:
            end = _balanced_end(text, "\\<open>", "\\<close>", start=m.start())
        if end <= m.start():
            # Unterminated on this line.  Nothing to the right can be read
            # reliably, so treat it as the proposition — what the scanner did
            # before, which keeps the residual error one-directional.
            return "".join(out), m.start()
        out.append(" " * (end - m.start()))
        i = end


def _command_prefix(stripped: str) -> str:
    """The part of a proof line before its proposition.  See
    :func:`_split_command_prefix`, which this is the text half of."""
    return _split_command_prefix(stripped)[0]


def _classify_step_line(stripped: str) -> str:
    r"""Classify one live proof line into ``goal`` / ``context`` / ``plumbing``
    / ``closing`` / ``other`` by its leading command sequence.

    A goal-stating command anywhere in the *command prefix* wins, so a chained
    line (``from a have b: "P"``, ``ultimately show ?thesis``) is a goal step
    even though a plumbing keyword leads it.  Otherwise the *first* command
    token decides.  ``other`` covers structural lines that are not steps —
    ``proof`` / ``qed`` / ``{`` / ``}`` / ``next`` and bare term continuations.
    """
    prefix = _command_prefix(stripped)
    tokens = _CMD_TOKEN_RE.findall(prefix)
    if not tokens:
        return "other"
    # A goal command anywhere before the proposition dominates (handles the
    # `<plumbing prefix> <goal> <statement>` chain form).
    if any(t in _GOAL_KEYWORDS for t in tokens):
        return "goal"
    head = tokens[0]
    if head in _CONTEXT_KEYWORDS:
        return "context"
    if head in _PLUMBING_KEYWORDS:
        return "plumbing"
    if head in _CLOSING_KEYWORDS or head in (".", ".."):
        return "closing"
    # A terminal proof method reached later in a prefix that no step keyword
    # leads still closes the goal — a line led by a fact name or by a word this
    # classifier does not know.  It used to carry `unfolding <facts> by
    # <method>` as well, back when `unfolding` was not a step keyword; that line
    # is now claimed by the plumbing head check above, exactly as
    # `using <facts> by <method>` always was.  `by` / `done` / `..` are matched
    # anywhere; a bare single `.` is not, since `.` is also the token split
    # inside a dotted fact name (`Foo.bar`).
    if any(t in _CLOSING_KEYWORDS or t == ".." for t in tokens):
        return "closing"
    return "other"


@dataclass
class Step:
    r"""One classified Isar command inside a proof body.

    ``line`` is the 1-indexed source line of the command (the step's stable
    position key); ``depth`` is the proof-block nesting depth (0 = directly in
    the lemma's own proof, 1 = one nested ``proof``/``{`` in, ...).  For a
    ``goal`` step, ``stmt_start`` / ``stmt_end`` bound the proposition span
    (1-indexed inclusive, possibly multi-line) and ``stmt_text`` is its source
    text with the cartouche/quote wrapper stripped; for non-goal steps these
    stay ``0`` / ``""``.
    """
    theory: str
    lemma: str
    line: int
    depth: int
    kw: str          # leading command keyword (or ".."/"." for dot proofs)
    kind: str        # goal / context / plumbing / closing / other
    stmt_start: int = 0
    stmt_end: int = 0
    stmt_text: str = ""
    label: str = ""  # the step's own fact label (`have key: ...` -> "key")
    # The fact-binding command of a goal step (`have`/`hence`/`show`/`thus`/...),
    # which may differ from the leading `kw`: `from a have b:` has kw="from" but
    # goal_cmd="have".  "" for non-goal steps.  Drives M5c introduce/discharge.
    goal_cmd: str = ""
    # Proof-block identity: a fresh id per `proof`/`{` frame (the lemma's own
    # outermost proof is block 0).  Distinguishes *sibling* blocks at the same
    # `depth`, which M4/M6 must not merge — `depth` alone cannot.
    block: int = 0
    # The step's discharge method: the leading `by`/`apply` proof method of its
    # line (`have "P" by simp` -> "simp", `by (rule r)` -> "rule"), or "" for a
    # step with no method on its own line (`qed`, an unclosed `have ... proof`,
    # a bare `.`/`..`).  Drives the "trivial" half of "long, wide, and trivial".
    method: str = ""
    # Why a goal step states no proposition — one of `BARE_KINDS`, or "" for a
    # step that states one (and for every non-goal step).  See `bare_kind`.
    bare: str = ""
    # Filled by later metric passes:
    fanin: int = 0            # M5a: distinct facts cited FOR a goal step
    fanin_covered: bool = True  # False if a method shape could not be classified
    live: int = 0             # M5b: named facts simultaneously live AT this step


# A goal command optionally carries a label: `have key: "P"`, `show *: "P"`.
_STEP_LABEL_RE = re.compile(
    r"\b(?:have|show|hence|thus|obtain|consider|interpret)\s+"
    r"([A-Za-z][\w'.]*)\s*:")


def _extract_statement(lines: list[str], start_idx: int,
                       end_idx: int) -> tuple[int, int, str]:
    r"""Extract a goal step's proposition span starting at 0-indexed line
    ``start_idx`` (inclusive), searching no further than ``end_idx`` (the proof
    body's last line, 0-indexed inclusive).

    Returns ``(stmt_start, stmt_end, text)`` — 1-indexed inclusive line bounds
    and the proposition source with its ``"``/``\<open>`` wrapper removed.  The
    proposition is the first double-quoted string or ``\<open>...\<close>``
    cartouche after the command prefix, balanced across lines if it does not
    close on its own line.  A goal with no explicit proposition (``show
    ?thesis`` written bare, ``also``, ``finally``) yields ``(0, 0, "")`` — there
    is no as-written statement to measure.
    """
    first = lines[start_idx]
    _prefix, col = _split_command_prefix(first)
    if col < 0:
        # The command's own line states no proposition.  It may still have one:
        # a statement wrapped to the next line is a bare goal only in the
        # record, not in the source.
        return _statement_wrapped(lines, start_idx, end_idx)
    if first[col] == '"':
        return _balance_quote(lines, start_idx, col, end_idx)
    return _balance_cartouche(lines, start_idx, col, end_idx)


# A goal command whose line ENDS at the command (with an optional label), which
# is what makes looking ahead safe: `show ?thesis` has a remainder and stays
# bare, `have` and `from p have b:` do not.  `also` / `finally` are excluded —
# they are goal keywords that never carry a proposition of their own.
_WRAPPED_GOAL_RE = re.compile(
    r"\b(?:have|show|hence|thus|obtain|consider|interpret)"
    r"(?:\s+[A-Za-z][\w'.]*\s*:)?\s*$")


def _statement_wrapped(lines: list[str], start_idx: int,
                       end_idx: int) -> tuple[int, int, str]:
    r"""A goal whose proposition is wrapped onto a following line (issue #9).

    ``_extract_statement`` searched the command's own line only, so

        have
          "True \<and> True"
          by simp

    yielded ``(0, 0, "")`` — indistinguishable in the record from a genuinely
    bare `show ?thesis`, which is exactly what hid it: ``n_bare`` pools "bare by
    construction" with "no proposition found".  **1.43% of AFP goal steps**,
    6.2% of everything reported in ``n_bare``, and strongly style-dependent —
    5x that rate in a corpus that wraps more.

    Deliberately narrow.  The command line must end *at* the goal keyword and
    the next non-blank line must *open* with a delimiter; anything else stays
    bare.  So `obtain x where` on its own line is still missed, since its
    remainder is not a label — a residue left rather than guessed at, because
    over-reaching here would invent statements, and the metrics are built to
    undercount rather than overcount.
    """
    if not _WRAPPED_GOAL_RE.search(lines[start_idx].rstrip()):
        return 0, 0, ""
    for i in range(start_idx + 1, min(end_idx, len(lines) - 1) + 1):
        if not lines[i].strip():
            continue      # blank, or prose the scan already blanked
        m = _PROP_START_RE.match(lines[i].lstrip())
        if m is None:
            return 0, 0, ""
        col = len(lines[i]) - len(lines[i].lstrip())
        if lines[i][col] == '"':
            return _balance_quote(lines, i, col, end_idx)
        return _balance_cartouche(lines, i, col, end_idx)
    return 0, 0, ""


# --- Why a goal step states no proposition ---------------------------------
#
# `n_bare` pooled two unrelated things, and the pooling is what hid issue #9(b)
# for as long as it did: a wrapped statement was booked as bare, where nobody
# would look for a scanner fault.  These three buckets are named after the
# measured population rather than guessed at — `scripts/probe_bare_provenance.py`
# over the whole AFP, 195,733 bare goal steps out of 883,246.  That probe now
# reports THROUGH `Step.bare`, so it cannot agree with a rule the tool does not
# use; the first cut, which kept its own copy, put `undelimited` 18% low.

# Goal commands that never carry a proposition of their own.  `also`/`finally`
# continue a calculation; `interpret` instantiates a locale.
_NO_PROPOSITION_CMDS = frozenset({"also", "finally", "interpret"})
# What follows the command, once its own name and any label are gone.
_STEP_LABEL_HEAD_RE = re.compile(r"^[A-Za-z][\w'.]*\s*(?:\[[^\]]*\])?\s*:(?!:)")
# The proof tail that may follow an UNDELIMITED proposition on the same line.
# `show False by simp` states `False`; the rest is the discharge.
_PROOF_TAIL_WORDS = frozenset({
    "by", "using", "unfolding", "apply", "proof", "done", "oops", "sorry",
    ".", "..", "if", "for", "when", "is",
})
# An undelimited proposition: one term, no quotes and no cartouche.  Isar
# allows it when the term is a single token — `show False`, `show thesis`,
# `show ?case` — and the statement scanner looks only for delimiters, so these
# are booked bare although the proposition is right there on the line.
_UNDELIMITED_TERM_RE = re.compile(rf"^(?:{ISA_WORD_CHAR}|[?])+$")

BARE_KINDS = ("construction", "undelimited", "unfound")


def _after_goal_command(prefix: str, goal_cmd: str) -> str:
    """The text a goal step writes after its command and its label.

    Read from the COMMAND PREFIX, not the raw line: `_split_command_prefix`
    blanks the balanced span of a fact cited in command position, so
    `with \\<open>?nhip \\<noteq> dip\\<close> show False` leaves `show` findable
    and cannot mistake the cited term for the statement.
    """
    if not goal_cmd:
        return prefix.strip()
    last = -1
    for m in re.finditer(rf"(?<![\w']){re.escape(goal_cmd)}(?![\w'])", prefix):
        last = m.end()
    rest = (prefix[last:] if last >= 0 else prefix).strip()
    m = _STEP_LABEL_HEAD_RE.match(rest)
    return rest[m.end():].strip() if m else rest


def bare_kind(step: Step, stripped: str) -> str:
    r"""Why this goal step has no as-written proposition — one of
    :data:`BARE_KINDS`, or ``""`` for a step that states one.

    * ``construction`` — the step *cannot* carry an as-written proposition.
      `also` / `finally` continue a calculation, `interpret` instantiates a
      locale, and `show ?thesis` / `thus ?case` / `show ?rhs` name a goal
      already in scope.  **88.70% of bare goal steps**, and a fact about how
      Isar is written, not about this scanner.
    * ``undelimited`` — the proposition is on the line, written without quotes
      or a cartouche (`hence False by simp`).  **5.29%.**  Recoverable in
      principle; not read today.
    * ``unfound`` — the scanner looked and found nothing.  **6.01%**, most of
      it `obtain x where` with the statement on the next line, which
      `_statement_wrapped` deliberately declines because the remainder is not a
      label.  This is the residue, and the point of the split: it is the only
      bucket whose growth is evidence about the SCANNER rather than about
      writing style, and until now it was invisible inside `n_bare`.
    """
    if step.stmt_text:
        return ""
    cmd = step.goal_cmd or step.kw
    if cmd in _NO_PROPOSITION_CMDS:
        return "construction"
    rest = _after_goal_command(_command_prefix(stripped), cmd)
    if rest.startswith("?"):
        return "construction"          # `?thesis`, `?case`, `?rhs`
    if not rest:
        return "unfound"               # command alone on its line
    head, _, tail = rest.partition(" ")
    if (_UNDELIMITED_TERM_RE.match(head)
            and (not tail.strip()
                 or tail.split()[0] in _PROOF_TAIL_WORDS)):
        return "undelimited"
    return "unfound"


def _balance_quote(lines: list[str], start_idx: int, open_col: int,
                   end_idx: int) -> tuple[int, int, str]:
    """Collect a ``"..."`` proposition from ``open_col`` on line ``start_idx``,
    continuing to later lines until the closing quote.  ``\\"`` escapes are not
    used in Isar statements, so a plain quote count suffices."""
    parts: list[str] = []
    body_open = open_col + 1
    for i in range(start_idx, min(end_idx, len(lines) - 1) + 1):
        segment = lines[i][body_open if i == start_idx else 0:]
        close = segment.find('"')
        if close >= 0:
            parts.append(segment[:close])
            return start_idx + 1, i + 1, "".join(parts).strip()
        parts.append(segment)
    # Unbalanced (ran off the proof body): treat the first line only.
    return start_idx + 1, start_idx + 1, parts[0].strip()


def _balance_cartouche(lines: list[str], start_idx: int, open_col: int,
                       end_idx: int) -> tuple[int, int, str]:
    r"""Collect a ``\<open>...\<close>`` proposition, balanced (cartouches nest)
    across lines from ``open_col`` on line ``start_idx``."""
    depth = 0
    parts: list[str] = []
    col = open_col
    for i in range(start_idx, min(end_idx, len(lines) - 1) + 1):
        line = lines[i]
        j = col if i == start_idx else 0
        seg_start = j
        while j < len(line):
            if line.startswith("\\<open>", j):
                depth += 1
                j += len("\\<open>")
            elif line.startswith("\\<close>", j):
                depth -= 1
                if depth == 0:
                    parts.append(line[seg_start:j])
                    text = "".join(parts)
                    # strip the leading \<open> of the first segment
                    text = text[len("\\<open>"):] if text.startswith("\\<open>") else text
                    return start_idx + 1, i + 1, text.strip()
                j += len("\\<close>")
            else:
                j += 1
        parts.append(line[seg_start:])
    return start_idx + 1, start_idx + 1, ""


def _inline_proof_col(sec: TheorySection, entry: Entry) -> int:
    r"""Column at which the proof begins on a line it SHARES with the goal
    statement (``lemma foo: "P" by simp``), or 0 when nothing but whitespace
    precedes it and the line can be read from column 0 as it always was.

    Located on the OUTER view with the same :data:`_PROOF_INLINE_RE` ``parsing``
    used to set ``proof_line``, so this re-finds that exact match rather than
    inventing a second rule, and a ``by`` inside a term cannot be mistaken for
    the proof.

    Blanking the prefix is only safe if it is *statement*, never a command that
    would form a step of its own — masking the ` by` of ``from a have b: "P" by
    simp`` would delete a goal.  Two kinds of evidence establish that, and both
    are checked because the three spellings split across them:

    * **inside the declaration** (``proof_line <= decl_end_line``) — the text is
      the statement by construction.  Covers the one-liner ``lemma a: "P" by
      simp`` and, since ``parsing`` scans the whole declaration span rather than
      just its first line, the 74 AFP facts whose proof sits on a later
      ``assumes``/``shows`` line.
    * **blank in the outer view** — the prefix is entirely inner syntax, and a
      term is never command position.  This is the case the declaration span
      cannot see: in ``lemma c:`` / ``"P" by auto`` the outer view of the second
      line *starts* with ``by``, so ``PROOF_RE`` claims it through the ordinary
      branch and ``decl_end_line`` is never extended over it.  324 AFP facts.

    Those two are **defence in depth, not load-bearing**: dropping both changes
    the answer for 0 of 43,828 AFP proofs, because a ``proof_line`` whose prefix
    is command text is not currently reachable — the ordinary branch demands the
    proof keyword at the *start* of the outer line, which puts the column at 0,
    and the inline branch only fires inside the declaration.  That invariant
    lives in ``parsing``'s two branches rather than here, so it is checked here
    rather than assumed: if it ever weakens, this must undercount, not silently
    delete steps.
    """
    if not entry.proof_line:
        return 0
    src = sec.source()
    if entry.proof_line > len(src):
        return 0
    line = src[entry.proof_line - 1]
    # Fast path for the 96%: "statement text precedes the proof" is the exact
    # negation of "the line begins with the proof", which `PROOF_RE` already
    # decides — and decides with an ANCHORED match, against the unanchored
    # whole-line scan below.  Asked first, it keeps this off the hot path: the
    # scan runs on every proof in the corpus, and searching all 43,828 cost 13%
    # of the step scan to serve 1,870.
    if PROOF_RE.match(line):
        return 0
    oline = sec.outer_source()[entry.proof_line - 1]
    m = _PROOF_INLINE_RE.search(oline)
    if m is None or m.start() == 0:
        return 0
    col = m.start()
    if not line[:col].strip():
        return 0  # only whitespace — nothing to blank, and no copy to make
    if entry.proof_line <= (entry.decl_end_line or entry.thy_line):
        return col
    return col if not oline[:col].strip() else 0


def _scan_steps(sec: TheorySection, entry: Entry) -> list[Step]:
    r"""Classify the Isar commands in ``entry``'s proof body into a flat list of
    :class:`Step`, in source order.

    Walks live lines from ``proof_line`` to ``body_end_line`` (skipping
    ``text`` / ``\<comment>`` prose via ``_noise_spans``), tracking proof-block
    nesting for each step's ``depth``.  Returns ``[]`` only for an entry with no
    proof at all (a bare definition).  The entry's own outermost ``proof`` is
    depth-0 scaffolding and is not itself a step.

    A proof written on the statement's own line is scanned from the column the
    proof starts at, so ``lemma a: "P" by simp`` yields the same lone ``closing``
    step as the same proof written on the next line.  Reading such a line from
    column 0 instead gave ``_command_prefix`` the text up to the statement's
    first quote — ``lemma a: `` — which leads no step family, so the scan
    returned no steps and the entry dropped out of every ``shape`` verb: 1,525
    proofs over 120 AFP entries, 79% of all drops, and *trivial* proofs
    specifically, which biased every aggregate rather than thinning it evenly.

    The statement half is blanked rather than sliced off to keep this module's
    line view column-identical to ``source()``, the same contract
    ``live_source`` / ``outer_source`` hold.  Nothing today can tell the two
    apart — :func:`_extract_statement` reads the mutated list, so a slice would
    be self-consistent as well — but every :class:`Step` line number is resolved
    against the real source by its consumers, and a view that silently shifts
    columns is the kind of thing that is correct until one caller correlates the
    two.
    """
    if not entry.proof_line:
        return []
    lines = sec.source()
    col = _inline_proof_col(sec, entry)
    if col:
        lines = list(lines)
        lines[entry.proof_line - 1] = (
            " " * col + lines[entry.proof_line - 1][col:])
    end = min(entry.body_end_line or entry.thy_end or len(lines), len(lines))
    noise = _line_set(_noise_spans(sec))
    steps: list[Step] = []
    # `open_blocks` counts open `proof`/`{` frames.  The lemma's own outermost
    # proof is frame 1, so a step *directly* in it reports depth 0 — nesting
    # depth is `max(0, open_blocks - 1)`.  A flat `by` proof opens no frame, so
    # its lone closing step is depth 0 too.
    #
    # `block_stack` mirrors the open frames but carries a *fresh id per frame*
    # (a monotonic counter): the lemma's own proof is block 0, each nested
    # `proof`/`{` a new id.  Depth cannot distinguish sibling blocks (both at the
    # same depth); the block id can, which M4/M6 require.
    open_blocks = 0
    block_stack: list[int] = []
    next_block = 0
    for ln in range(entry.proof_line, end + 1):
        if ln in noise:
            continue
        stripped = lines[ln - 1].strip()
        if not stripped:
            continue
        step_depth = max(0, open_blocks - 1)
        cur_block = block_stack[-1] if block_stack else 0
        method = _leading_method(stripped)
        # Block close: `qed` is a closing step in the block it closes (recorded
        # before the frame pops); a raw `}` is structural only.
        if _BLOCK_CLOSE_RE.match(stripped):
            if stripped.startswith("qed"):
                steps.append(Step(sec.theory, entry.name, ln, step_depth,
                                  "qed", "closing", block=cur_block,
                                  method=method))
            open_blocks = max(0, open_blocks - 1)
            if block_stack:
                block_stack.pop()
            continue
        kind = _classify_step_line(stripped)
        kw = _leading_kw(stripped)
        if kind == "goal":
            s_start, s_end, text = _extract_statement(lines, ln - 1, end - 1)
            label_m = _STEP_LABEL_RE.search(_command_prefix(stripped))
            st = Step(sec.theory, entry.name, ln, step_depth, kw, kind,
                      s_start, s_end, text,
                      label=label_m.group(1) if label_m else "",
                      goal_cmd=_goal_command(stripped), block=cur_block,
                      method=method)
            # Classified here, where the step's own source line is still in
            # hand: `bare_kind` reads the command prefix, and reconstructing it
            # later from `Step.line` would be a second parse to keep in step.
            st.bare = bare_kind(st, stripped)
            steps.append(st)
        elif kind != "other":
            steps.append(Step(sec.theory, entry.name, ln, step_depth, kw, kind,
                              block=cur_block, method=method))
        # A `proof`/`{` opener deepens *subsequent* lines and opens a new block.
        if _BLOCK_OPEN_RE.match(stripped):
            open_blocks += 1
            block_stack.append(next_block)
            next_block += 1
    return steps


def _leading_kw(stripped: str) -> str:
    """The leading command keyword of a proof line (`have`, `from`, `by`, or a
    bare `.`/`..`), for the step's ``kw`` field."""
    m = _CMD_TOKEN_RE.match(stripped)
    return m.group(0) if m else ""


def _goal_command(stripped: str) -> str:
    """The fact-binding goal command of a goal line — the *last* goal keyword in
    its command prefix.  A chained line reads ``<chain-word> <core-command>``
    (`from a have`, `ultimately show`, `also have`), so the core command is the
    trailing goal keyword; taking the last one keeps `finally show` a `show`
    (discharge) and `also have` a `have` (introduce)."""
    prefix = _command_prefix(stripped)
    cmds = [t for t in _CMD_TOKEN_RE.findall(prefix) if t in _GOAL_KEYWORDS]
    return cmds[-1] if cmds else ""


def _line_set(spans: list[tuple[int, int]]) -> set[int]:
    """Flatten inclusive ``[lo, hi]`` spans into a set of line numbers, for
    O(1) prose-line membership during the step walk."""
    out: set[int] = set()
    for lo, hi in spans:
        out.update(range(lo, hi + 1))
    return out


# --- metrics ---------------------------------------------------------------
#
# Each metric is a deterministic function of a Step (and, for later metrics,
# corpus context).  Source-level *estimator* values carry an
# `_est` suffix in the JSONL schema; exact source-level values (like w2_src) do
# not.  This section grows one metric at a time.

# A proposition token is an identifier/symbol *run* or a single punctuation
# char.  The run alternative is tried first, so an Isabelle symbol `\<and>` or a
# control `\<^sub>` — and a name with glued sub/superscripts, `x\<^sub>1` — is
# one token, not split at the backslash.  `\S` then picks up standalone operators
# and delimiters (`=`, `(`, `+`, `,`), one token each; whitespace is skipped.
_STMT_TOKEN_RE = re.compile(rf"{ISA_WORD_CHAR}+|\S")


def _stmt_tokens(text: str) -> list[str]:
    r"""Tokenise a proposition's source text into the units :func:`w2_src`
    counts: one per identifier/symbol run (``\<sym>`` / ``\<^ctrl>`` count as
    one, glued sub/superscripts stay attached) and one per non-space punctuation
    character.  Deterministic and elaboration-free — this is the *as-written*
    view, exact at source level."""
    return _STMT_TOKEN_RE.findall(text)


def w2_src(step: Step) -> int:
    r"""**M2 headline (source width)** — the token count of a goal step's
    as-written proposition span.

    This is the number of tokens a human or LLM reader actually experiences,
    with abbreviations still contracted; it needs no elaboration and is exact at
    source level, so it is the phase-1 headline for M2 (the elaborated ``w2`` /
    ``w2_ty`` are phase-2 calibration only).  Non-goal steps, and goal steps
    with no explicit proposition (``show ?thesis``, ``also``, ``finally``),
    measure 0 — there is no as-written statement to count."""
    return len(_stmt_tokens(step.stmt_text)) if step.stmt_text else 0


def _line_facts(step: Step, lines: list[str]) -> tuple[set[str], bool]:
    """The facts cited on a step's own source line, via the shared positional
    extractor.  ``other`` steps (structural lines) cite nothing."""
    if step.kind == "other":
        return set(), True
    return _cited_facts_on_line(lines[step.line - 1])


# Plumbing commands that cite BACKWARD — for the goal already stated, not the
# next one.  Isar admits `using` / `unfolding` only in `proof(prove)` mode, i.e.
# after a goal statement and before its method, so their facts serve that goal:
#
#     have a: "P"
#       using q by simp        <- q is a premise OF a, not of the next goal
#
# `from` / `with` / `then` / `moreover` / `ultimately` are the forward half
# (`proof(state)` mode, before a goal statement) and keep the pending-chain
# behaviour.  Isabelle's own keyword kinds put the forward four under
# `prf_chain` and these two under `prf_decl`, which is the same distinction
# read off the grammar rather than inferred from usage.
_BACKWARD_CITE_CMDS = frozenset({"using", "unfolding"})


def annotate_fanin(steps: list[Step], sec: TheorySection) -> None:
    r"""**M5a fan-in** — set ``step.fanin`` on each goal step to the number of
    distinct facts cited *for* it.

    A goal step's fan-in is the union of the facts on its own line
    (``from a have p: "P" using b``) and those of the standalone plumbing lines
    that serve it.  **Which goal a plumbing line serves depends on its keyword,
    and the two directions are not interchangeable** (:data:`_BACKWARD_CITE_CMDS`):

    * ``from`` / ``with`` / ``then`` / ``moreover`` / ``ultimately`` chain
      FORWARD — they run in ``proof(state)`` mode, before a goal statement, so
      their facts accumulate and attach to the next goal.
    * ``using`` / ``unfolding`` cite BACKWARD — Isar admits them only in
      ``proof(prove)`` mode, after a goal has been stated, so their facts belong
      to the goal already open.

    Treating both as forward was an off-by-one-goal misattribution: in

        have a: "P"
          using q by simp
        have b: "Q"

    ``q`` was credited to ``b`` and ``a`` was left at zero.  It survived because
    the *totals* stayed plausible — each goal received some other goal's
    premises — so only a per-step check could see it.  Corrected, M5a rose 15.9%
    over a 40-entry AFP sample: the shift also *lost* every citation whose
    ``using`` line had no following goal, which is why the fix is not
    redistribution-neutral.

    A closing step (``qed``, a standalone ``by``) is a boundary: it discards any
    not-yet-consumed forward chain and ends the backward-citable goal.
    ``step.fanin_covered`` is ``False`` when a method shape on the contributing
    lines could not be classified (folded into the census's method-syntax
    coverage statistic).

    Implicit ``this`` chaining (``then`` / ``moreover`` / ``ultimately``) brings
    an *unnamed* fact, so it adds nothing to this explicit-citation count — that
    working-set pressure is M5b's (live-fact space), not M5a's.  Non-goal steps
    keep ``fanin`` 0.

    **Scope.** This counts *explicit source-cited* premises only — the facts a
    reader sees named in the text.  It does **not** count what a ``simp``/``auto``
    invocation pulls from the default simpset/claset (invisible without the
    prover), and it averages over the many zero-premise ``by simp`` / ``by auto``
    goals.  So the mean is "explicit source-cited premises **per goal step**".  A
    related figure is the **conditional** fan-in — the mean over goal steps that
    cite ≥1 — which the census exposes via
    the ``fanin_cited`` count (see :func:`summarize`); do not equate the flat
    ``fanin_mean`` with the field anchor.
    """
    lines = sec.source()
    pending: set[str] = set()      # facts from plumbing lines not yet consumed
    pending_covered = True
    open_goal: Step | None = None  # the goal a BACKWARD cite would serve
    seen: set[str] = set()         # what that goal has already been credited
    for s in steps:
        facts, covered = _line_facts(s, lines)
        if s.kind == "plumbing" and s.kw in _BACKWARD_CITE_CMDS:
            if open_goal is not None:
                fresh = facts - seen
                open_goal.fanin += len(fresh)
                open_goal.fanin_covered = open_goal.fanin_covered and covered
                seen |= fresh
        elif s.kind == "plumbing":
            pending |= facts
            pending_covered = pending_covered and covered
        elif s.kind == "goal":
            s.fanin = len(facts | pending)
            s.fanin_covered = covered and pending_covered
            pending, pending_covered = set(), True
            open_goal, seen = s, facts | pending
        elif s.kind == "closing":
            pending, pending_covered = set(), True
            open_goal, seen = None, set()


# --- M5b: live-fact space (abstract metric A1, reading (i)) -----------------
#
# Within a proof, a *named* fact is "live" from the step that introduces it
# (`have l:`, `note l = ...`, `obtain ... where l:`) until the last step that
# cites it — by name (`using l`, `rule l`) or by implicit `this`-chaining
# (`then`, `moreover`, ...).  The live-fact space is the peak count of
# simultaneously live named facts (the proof-complexity "clause space" analog);
# we also report the per-step mean, which is the abstract's "average ... live
# hypotheses per step".
#
# Only *named* facts are tracked: an anonymous `have "P"` / `assume "P"` binds
# `this` but no citable label, so it adds nothing a later step could name.  Two
# deliberate phase-1 simplifications, both documented as conservative:
#   * Birth is line-anchored at the introducing command (matching the scanner).
#     For the inline `have l: "P" proof ... qed` form this counts `l` as live
#     during its own sub-proof — a slight over-approximation of the *mean* (never
#     of the max in practice).
#   * Scope is the whole proof body, not per-block: a fact established before a
#     nested block is genuinely live inside it, so a flat sweep captures the true
#     simultaneity.  Sibling-block facts never overlap because each dies at its
#     last use.  Explicit per-block partitioning is a phase-2 refinement.

# Goal commands that BIND a reusable fact (M5c numerator / M5b introduction).
# `show`/`thus`/`finally`/`also` discharge or chain rather than introduce.
_GOAL_INTRO_CMDS = frozenset({"have", "hence", "obtain", "consider", "interpret"})
# Context / plumbing commands that also introduce a fact.  `fix` (a variable) and
# `let` (a term abbreviation) bind no fact and are excluded.
_CONTEXT_INTRO_CMDS = frozenset({"assume", "presume", "define", "case"})
_PLUMBING_INTRO_CMDS = frozenset({"note", "moreover"})
# Commands that implicitly cite `this` / the calculation, consuming the most
# recently established named fact without spelling its name.  These always lead
# the line, so the step's leading `kw` suffices to detect them.
_THIS_CHAIN_WORDS = frozenset({
    "then", "hence", "thus", "with", "moreover", "ultimately", "also", "finally",
})

# Label on a context / plumbing introduction: `note l = ...`, `assume l: ...`,
# `case l`.  (Goal-step labels are already parsed into `Step.label`.)
_INTRO_LABEL_RE = re.compile(
    r"^(?:note|assume|presume|case)\s+\(?\s*([A-Za-z][\w'.]*)\s*[:=]")


def introduces(step: Step) -> bool:
    r"""**M5c numerator** — whether ``step`` binds a fact into the context.

    Keys on the *goal command*, not the leading keyword: ``from a have b:`` has
    ``kw="from"`` yet introduces ``b`` because its goal command is ``have``.
    ``show`` / ``thus`` / ``finally`` discharge a goal rather than introduce one.
    Context ``assume`` / ``presume`` / ``define`` / ``case`` and plumbing
    ``note`` / ``moreover`` (calculation accumulation) also introduce; ``fix``
    and ``let`` do not.
    """
    if step.kind == "goal":
        return step.goal_cmd in _GOAL_INTRO_CMDS
    if step.kind == "context":
        return step.kw in _CONTEXT_INTRO_CMDS
    if step.kind == "plumbing":
        return step.kw in _PLUMBING_INTRO_CMDS
    return False


def consumes(step: Step, sec: TheorySection) -> bool:
    """**M5c denominator** — whether ``step`` cites at least one fact, via the
    M5a positional extractor on the step's own line.  Implicit ``this``-chaining
    is *not* counted here — M5c ties consumption to *explicit* citation."""
    return bool(_line_facts(step, sec.source())[0])


def _intro_fact_name(step: Step, line: str) -> str:
    """The *named* fact ``step`` introduces, or ``""`` for an anonymous one.

    Goal introductions carry their name in ``Step.label``; context / plumbing
    introductions (`note l =`, `assume l:`, `case l`) are parsed from the line.
    An unlabelled `have "P"` / `assume "P"` introduces an anonymous fact — it
    binds ``this`` but nothing a later step can cite by name, so it is untracked.
    """
    if step.kind == "goal":
        return step.label if step.goal_cmd in _GOAL_INTRO_CMDS else ""
    if introduces(step):
        m = _INTRO_LABEL_RE.match(line.strip())
        return m.group(1) if m else ""
    return ""


def _fact_intervals(steps: list[Step],
                    lines: list[str]) -> tuple[dict[str, int], dict[str, int]]:
    r"""Compute, per named fact, its ``(birth, death)`` step indices.

    Birth is the index of the introducing step; death is the index of the last
    step that cites it — explicitly (its name in :func:`_line_facts`) or via
    ``this``-chaining, where a chaining step (``then``, ``moreover``, ...)
    consumes the fact currently bound to ``this``.  A never-cited fact dies at
    its birth.  Returns ``(births, deaths)`` keyed by fact name.
    """
    births: dict[str, int] = {}
    deaths: dict[str, int] = {}
    current_this: str | None = None   # named fact bound to `this`, or None
    for i, s in enumerate(steps):
        cited, _ = _line_facts(s, lines)
        for name in cited:
            if name in births:
                deaths[name] = i
        if (s.kw in _THIS_CHAIN_WORDS or "this" in cited) \
                and current_this in births:
            deaths[current_this] = i
        name = _intro_fact_name(s, lines[s.line - 1])
        if name:
            births.setdefault(name, i)
            deaths.setdefault(name, i)
            current_this = name
        elif s.kind == "goal":
            current_this = None       # an anonymous goal rebinds `this` unnamed
    return births, deaths


def live_fact_space(steps: list[Step],
                    sec: TheorySection) -> tuple[int, float]:
    r"""**M5b** — the ``(max, mean)`` number of simultaneously live named facts
    across a proof's steps, annotating each ``step.live``.

    A named fact is live on the inclusive step interval ``[birth, death]`` from
    :func:`_fact_intervals`; ``step.live`` counts the facts live at that step.
    ``max`` is the peak (the clause-space analog); ``mean`` is the average over
    all steps (the abstract's per-step average).  An empty / bare proof is
    ``(0, 0.0)``.
    """
    if not steps:
        return 0, 0.0
    births, deaths = _fact_intervals(steps, sec.source())
    counts: list[int] = []
    for i, s in enumerate(steps):
        s.live = sum(1 for nm, b in births.items() if b <= i <= deaths[nm])
        counts.append(s.live)
    return max(counts), sum(counts) / len(counts)


# --- M5c: introduce / consume ratio (abstract metric A2) --------------------
#
# The ratio of fact-introducing to fact-consuming lines, plus the disjoint
# three-way split (introduce-only / consume-only / both) that the bare ratio
# hides.  The ratio is fairly constrained in well-formed Isar (an
# introduced fact is eventually consumed), so the split and the M5a fan-in
# distribution carry most of the signal.


@dataclass
class IntroConsume:
    """M5c tallies over a proof's steps: introducing / consuming line counts,
    their disjoint three-way split, and the derived ratio."""
    introduce: int = 0
    consume: int = 0
    both: int = 0
    introduce_only: int = 0
    consume_only: int = 0
    neither: int = 0
    total: int = 0

    @property
    def ratio(self) -> float | None:
        """Introducing lines per consuming line, or ``None`` when nothing is
        consumed (a flat ``by`` proof) — an undefined ratio, not zero."""
        return self.introduce / self.consume if self.consume else None


def introduce_consume(steps: list[Step], sec: TheorySection) -> IntroConsume:
    """**M5c** — tally introducing / consuming lines and their three-way split
    across a proof's steps.  A line can be both (`from a have b:` introduces
    ``b`` and consumes ``a``); it counts in ``introduce``, ``consume`` and
    ``both``, but in neither ``introduce_only`` nor ``consume_only``."""
    lines = sec.source()
    out = IntroConsume()
    for s in steps:
        intro = introduces(s)
        cons = bool(_line_facts(s, lines)[0])
        out.total += 1
        out.introduce += intro
        out.consume += cons
        if intro and cons:
            out.both += 1
        elif intro:
            out.introduce_only += 1
        elif cons:
            out.consume_only += 1
        else:
            out.neither += 1
    return out


# --- "trivial": the automation fraction ------------------------------------
#
# "Long, wide, and trivial" — the third axis.  "Trivial" means each step is
# discharged by bounded-search automation (`simp`/`auto`/`blast`) rather than a
# deep proof, so it is directly measurable in phase 1 from the step's discharge
# method (`Step.method`, extracted by the shared method-census primitive).  This
# is the phase-1 half of the "trivial" claim; a small-fact-list refinement
# (joining fan-in) is a later cross of M5a with this column.

# Bounded-search automation methods — the "trivial" discharges.  A named-rule
# (`rule`, `metis`), structural (`induction`, `cases`), or bespoke method is NOT
# trivial.  Kept to this documented set so `trivial_frac` is hand-computable and
# comparable across corpora; treat it as the tunable knob if the definition
# needs to widen (e.g. `simp_all`, `arith`).
TRIVIAL_METHODS = frozenset({"simp", "auto", "blast", "force", "fastforce"})


def trivial_frac(steps: list[Step]) -> float | None:
    r"""Fraction of a proof's *discharged* steps closed by a trivial automation
    method (:data:`TRIVIAL_METHODS`).

    The denominator is the steps that carry an extracted discharge method
    (``step.method != ""`` — a ``by`` / ``apply`` line); ``qed``, structured
    openers, and rule-shorthand ``.`` / ``..`` carry none and do not count.
    Returns ``None`` when the proof discharges nothing at all (a purely
    structural body) — an undefined fraction, not ``0``.

    That is now ``None``'s only meaning.  While :func:`graph._leading_method`
    checked the bound method table, ``None`` was ambiguous between "discharges
    nothing" and "discharges with a tactic the table lacks", and the second case
    was not noise: it was 1.29% of AFP proofs, concentrated by proof style
    (`Auto2_Imperative_HOL` reported ``None`` for 305 of its 349 proofs).  The
    denominator is positional now, so the whole automation axis is independent of
    which table is bound — like fan-in, width and depth, and unlike the
    position-blind :func:`classify_identifier`, where a table is still the right
    instrument.

    A caveat that follows, and is wanted: a proof discharged entirely by a
    bespoke tactic reads ``0.0`` rather than ``None``, which understates a
    genuinely automatic `auto2` proof — but it does so *visibly*, as a number a
    reader can question, rather than by leaving the measure.
    :data:`TRIVIAL_METHODS` is the documented knob if a corpus wants its own
    tactics counted as trivial.
    """
    methoded = [s for s in steps if s.method]
    if not methoded:
        return None
    trivial = sum(1 for s in methoded if s.method in TRIVIAL_METHODS)
    return trivial / len(methoded)


# The proof-method *kind* taxonomy — the "automation" axis's finer grain than the
# binary `trivial_frac`.  Each discharged step's leading method (`Step.method`,
# whatever stands in introducer position) maps to exactly one kind; anything
# outside the four core families is `other` (domain-specific or manual tactics —
# `unfold`, `subst`, `transfer`, and an entry's own Eisbach/ML tactics, which
# reach `other` now rather than leaving the measure entirely).  Like
# TRIVIAL_METHODS these sets are a tunable knob, not a claim about tactic
# semantics: they name the cross-corpus core so the distribution is comparable
# across entries, and `trivial_frac`'s set is a union of `automation` + parts of
# `search` (it predates this finer split and is kept for continuity).
METHOD_KIND_NAMES = ("automation", "search", "arith", "structural", "other")

_METHOD_KIND_SETS = {
    "automation": frozenset({"simp", "simp_all", "auto", "clarsimp", "clarify"}),
    "search": frozenset({"blast", "fast", "fastforce", "force", "best",
                         "metis", "meson", "smt", "satx", "argo"}),
    "arith": frozenset({"arith", "linarith", "presburger", "algebra", "sos",
                        "approximation", "order", "cooper", "real_asymp"}),
    "structural": frozenset({"rule", "rule_tac", "drule", "drule_tac", "erule",
                             "erule_tac", "frule", "frule_tac", "intro", "elim",
                             "cases", "case_tac", "induct", "induction",
                             "induct_tac", "coinduct", "coinduction",
                             "nominal_induct", "standard", "unfold_locales",
                             "intro_classes", "intro_locales", "pat_completeness",
                             "split"}),
}


def method_kind(method: str) -> str:
    """Classify one leading proof method into its kind (one of
    :data:`METHOD_KIND_NAMES`).  ``""`` for a step that discharges nothing; any
    method outside the four core families is ``"other"`` (custom or manual
    tactics).  ``"other"`` therefore means "outside the core families", not
    "recognised but outside them" — an entry-local tactic lands here."""
    if not method:
        return ""
    for kind, names in _METHOD_KIND_SETS.items():
        if method in names:
            return kind
    return "other"


def bare_kind_counts(steps: list[Step]) -> dict[str, int]:
    """Histogram of a proof's bare goal steps by provenance — the split
    `n_bare` never had.  Every :data:`BARE_KINDS` key is present (``0`` when a
    kind is absent), so the schema is uniform, and the sum is exactly
    ``n_bare``: this refines the field rather than redefining it, so a stored
    census row stays comparable with a new one."""
    counts = {k: 0 for k in BARE_KINDS}
    for s in steps:
        if s.bare:
            counts[s.bare] += 1
    return counts


def method_kind_counts(steps: list[Step]) -> dict[str, int]:
    """Histogram of a proof's *discharged* steps by method kind — the automation
    axis's profile.  Every :data:`METHOD_KIND_NAMES` key is present (``0`` when a
    kind is absent), so the schema is uniform; the denominator is the sum
    (discharged steps), matching :func:`trivial_frac`."""
    counts = {k: 0 for k in METHOD_KIND_NAMES}
    for s in steps:
        if s.method:
            counts[method_kind(s.method)] += 1
    return counts


# --- ADD #3: induction discipline (LiFtEr's source-visible inputs) ----------
#
# LiFtEr (Nagashima, APLAS 2019) encodes induction heuristics; its *input* is the
# source-visible part of an `induct` / `induction` call — how many terms it
# inducts on, how many variables it generalizes (`arbitrary:`), and whether it
# supplies a custom induction `rule:`.  None of M1-M6 / A1-A3 captures this, and
# for a machine-generated corpus the
# induction *discipline* is plausibly a strong discriminator.  We measure the
# source inputs only, NOT LiFtEr's full semantic assertions (those need the
# elaborated proof state — out of phase-1 scope).

class Induction(NamedTuple):
    """One induction-method invocation, reduced to its source-visible inputs.
    Compares equal to the plain ``(terms, arbitrary, rule, recursion)`` tuple,
    so it is a drop-in for the census reduction and its fixtures."""
    terms: int           # # induction terms (`induct x y` -> 2)
    arbitrary: int       # # `arbitrary:` generalized variables
    rule: bool           # an explicit `rule:` is supplied
    recursion: bool      # ... and it is a `*.induct` recursion rule


# The induction methods sharing the `terms [arbitrary:] [rule:]` argument
# grammar.  `coinduct` / `coinduction` are the dual and take different modifiers,
# so they stay out of this axis (kept to a hand-computable, defensible set).
INDUCTION_METHODS = frozenset({
    "induct", "induction", "induct_tac", "nominal_induct"})

# Modifier keywords inside an induction method's argument list; each ends the
# leading run of induction *terms* and opens a named sub-list.  `arbitrary:` and
# `rule:` are the two scored; `taking:` / `avoiding:` / `pred:` / `set:` are
# recognised only so they correctly terminate the terms run (real but rare —
# ~600 uses archive-wide).
_INDUCT_MODIFIERS = frozenset({
    "arbitrary", "taking", "rule", "avoiding", "pred", "set"})

# An induction method in introducer position: `by` / `apply` / `proof`, an
# optional `(`, then the method name.  The `(` (when present) is captured so the
# argument list can be balanced from it; a bare `by induct` (no `(`) has no args.
# Longest alternatives first so `induction` is not shadowed by the `induct`
# prefix.  Anchored on the introducer like `_leading_method`: an induction that
# is not the step's leading method (`apply (rule r, induct x)`) is not seen —
# undercount, never overcount.
_INDUCT_INTRO_RE = re.compile(
    r"\b(?:by|apply|proof)\b\s*(\(?)\s*"
    r"(induction|induct_tac|nominal_induct|induct)\b")


def _split_induct_args(args: str) -> list[str]:
    r"""Whitespace-split an induction argument list, keeping a ``"..."`` compound
    term as a single token — its inner spaces / commas / parens are part of the
    term, not separators (``induct "(p, t)"`` inducts on *one* term)."""
    out: list[str] = []
    i, n = 0, len(args)
    while i < n:
        if args[i].isspace():
            i += 1
            continue
        if args[i] == '"':
            j = args.find('"', i + 1)
            j = n if j < 0 else j + 1
            out.append(args[i:j])
            i = j
            continue
        j = i
        while j < n and not args[j].isspace() and args[j] != '"':
            j += 1
        out.append(args[i:j])
        i = j
    return out


def _induct_modifier(word: str) -> "tuple[str | None, str]":
    r"""``(modifier_name, inline_value)`` when ``word`` opens a modifier sub-list
    (``arbitrary:``, ``rule:``, ...), else ``(None, "")``.  Handles both the
    spaced form (``rule:`` then ``foo.induct``) and a glued ``rule:foo.induct``;
    a term like ``n::nat`` or a quoted ``"x:y"`` is not a modifier."""
    idx = word.find(":")
    if idx > 0 and word[:idx] in _INDUCT_MODIFIERS:
        return word[:idx], word[idx + 1:]
    return None, ""


def _parse_induction(args: str) -> Induction:
    r"""Reduce an induction method's argument text to an :class:`Induction`.

    ``terms`` counts the leading induction terms (a ``"..."`` compound term
    counts once); ``arbitrary`` the ``arbitrary:`` generalized variables;
    ``rule`` whether a ``rule:`` is supplied; ``recursion`` whether any supplied
    rule is a ``*.induct`` recursion rule — the qualified ``f.induct`` schema
    auto-generated per recursive function / datatype, distinct from a library
    rule like ``list_induct2`` (no qualifying dot).  The ``.induct`` dot is the
    source-level discriminator between the two."""
    section = "terms"
    n_terms = n_arb = 0
    has_rule = recursion = False
    for w in _split_induct_args(args):
        name, inline = _induct_modifier(w)
        if name is not None:
            section = name
            if name == "rule":
                has_rule = True
                if ".induct" in inline:
                    recursion = True
            elif name == "arbitrary" and inline:
                n_arb += 1
            continue
        if section == "terms":
            n_terms += 1
        elif section == "arbitrary":
            n_arb += 1
        elif section == "rule" and ".induct" in w:
            recursion = True
    return Induction(n_terms, n_arb, has_rule, recursion)


def _join_arg_parts(parts: list[str]) -> str:
    """Join per-line argument segments into one logical argument list, dropping
    the continuation lines' indentation (interior whitespace is only a token
    separator here, never significant)."""
    return " ".join(p.strip() for p in parts if p.strip())


def _induction_arg_text(lines: list[str], start_0: int) -> "str | None":
    r"""The argument text of the induction-method call whose introducer is on
    0-indexed line ``start_0`` — the source between the method name and the
    matching ``)``, paren-balanced *quote-aware* (compound terms carry commas /
    parens) across continuation lines.  ``None`` when the call is bare (no
    parenthesised argument list, ``by induct``) or the line has no induction
    introducer.  Line-anchored on the introducer, matching ``_leading_method``.

    The balancing itself is the shared :func:`parsing._balanced_end` scanner
    (``quote_aware`` — the ``)`` inside ``"(p, t)"`` must not close the call).
    This function only *locates* the opening ``(`` and the collection start, then
    joins the newline-delimited continuation region back into one argument list
    with :func:`_join_arg_parts`; the interior of the balanced parens, minus the
    closing ``)``, is that region between the method name and the match."""
    m = _INDUCT_INTRO_RE.search(lines[start_0])
    if m is None or not m.group(1):     # no introducer, or bare (no `(`)
        return None
    open_col = m.start(1)               # the `(` before the method name
    arg_start = m.end(2)                # just past the method name
    region = "\n".join(lines[start_0:])
    close = _balanced_end(region, "(", ")", start=open_col, quote_aware=True)
    body = region[arg_start:] if close < 0 else region[arg_start:close - 1]
    return _join_arg_parts(body.split("\n"))


def scan_inductions(sec: TheorySection, entry: Entry) -> list[Induction]:
    r"""Every induction-method invocation in ``entry``'s proof region, each
    reduced by :func:`_parse_induction` to an :class:`Induction`.

    Scans the proof-region *source* directly rather than :func:`_scan_steps`
    steps, because a common induction form is not a step at all: the
    ``proof (induction ...)`` block-opener is depth scaffolding, not a step.
    (The one-line ``lemma foo: "..." by (induction ...)`` is now a closing step,
    but reading the source keeps this independent of that.)
    Anchored on the ``by`` / ``apply`` / ``proof`` introducer
    (:data:`_INDUCT_INTRO_RE`), so an induction-method *name* appearing in a
    statement never registers; ``text`` / ``\<comment>`` noise lines are skipped.
    A continuation line of a wrapped argument list carries no introducer, so it
    is not re-counted.  Line-anchored (undercount, never overcount): an induction
    that is not its step's leading method (``apply (rule r, induct x)``) is
    missed, matching :func:`_leading_method`."""
    end = entry.body_end_line or entry.thy_end or len(sec.source())
    if not end:
        return []
    lines = sec.source()
    end = min(end, len(lines))
    start = entry.proof_line or entry.thy_line or 1
    noise = _line_set(_noise_spans(sec))
    out: list[Induction] = []
    for ln in range(start, end + 1):
        if ln in noise:
            continue
        if _INDUCT_INTRO_RE.search(lines[ln - 1]) is None:
            continue
        args = _induction_arg_text(lines, ln - 1)
        out.append(_parse_induction(args) if args
                   else Induction(0, 0, False, False))
    return out


class InductionSummary(NamedTuple):
    """Per-proof reduction of a proof's induction invocations — the census-record
    columns.  A sufficient statistic for the entry-level axes: ``n`` gives the
    induction-using fraction, ``arbitrary_max`` the generalization depth (LiFtEr's
    core discipline), ``n_recursion`` / ``n_rule`` the recursion-rule fractions."""
    n: int               # induction invocations in the proof
    terms_max: int       # widest induction (# terms)
    arbitrary_max: int   # deepest generalization (# `arbitrary:` vars)
    n_rule: int          # invocations giving an explicit `rule:`
    n_recursion: int     # ... whose rule is a `*.induct` recursion schema


def summarize_inductions(inductions: list[Induction]) -> InductionSummary:
    """Reduce a proof's :class:`Induction` list to its :class:`InductionSummary`
    census columns (all ``0`` for a proof with no induction)."""
    return InductionSummary(
        n=len(inductions),
        terms_max=max((i.terms for i in inductions), default=0),
        arbitrary_max=max((i.arbitrary for i in inductions), default=0),
        n_rule=sum(i.rule for i in inductions),
        n_recursion=sum(i.recursion for i in inductions))


# --- M1: eigenvariable width (w1_est) + layered variable/constant classifier -
#
# w1(s) counts the distinct FREE variables (`Free`) in a step's elaborated
# proposition — the resolution-width analog over variables.  The source-level
# estimator `w1_est` cannot type-check, so it (1) tokenises the as-written
# statement, (2) separates statement-local binder-bound names and schematic
# `?vars` into their own columns, and (3) classifies each remaining identifier as
# variable-or-constant with a layered heuristic, recording the *provenance* of
# each decision so estimator error is auditable.
#
# The layered classifier (in precedence order):
#   context  -> var    a `fix`/`for`/binder-bound name is authoritatively a
#                      variable, even when it shadows a global.
#   syntax   -> const  a proof method / keyword / attribute (`if`, `then`) is
#                      term syntax, never an eigenvariable.
#   entry    -> const  a name defined in this theory's entry DB.
#   corpus   -> const  a name harvested as a shared constant from AFP usage
#                      (`Suc`, `map`; see `_corpus_constants`).
#   default  -> var    an unknown lowercase name confined to one lemma is most
#                      likely a variable.  This is where the estimator is weakest
#                      (a single-letter algebra constant `e` misclassifies here);
#                      the provenance tag makes that visible to calibration.

# Statement-local binders whose trailing names bind bound variables.  Two forms:
# symbolic (`\<forall>`, `\<lambda>`) — which `_stmt_tokens` GLUES to the first
# bound var (`\<forall>k` is one token, by the same rule that keeps `g\<^sub>1`
# together), so we split them off by prefix — and ASCII word spellings, which are
# standalone name tokens.
_BINDER_SYMS = (
    "\\<forall>", "\\<exists>", "\\<nexists>", "\\<lambda>", "\\<And>",
    "\\<Sum>", "\\<Prod>", "\\<Union>", "\\<Inter>",
)
_BINDER_WORDS = frozenset({"ALL", "EX", "SOME", "THE", "LEAST", "GREATEST"})
_NAME_RE = re.compile(r"[A-Za-z][\w']*\Z")


def _is_name(tok: str) -> bool:
    """Whether a statement token is a bare identifier (a var/const candidate),
    as opposed to a symbol, delimiter, numeral or `\\<sym>` operator."""
    return bool(_NAME_RE.match(tok))


def _binder_prefix(tok: str) -> tuple[str | None, str]:
    """If ``tok`` begins with a symbolic binder, return ``(sym, rest)`` where
    ``rest`` is the glued first bound variable (``\\<forall>k`` -> ``("\\<forall>",
    "k")``), else ``(None, "")``."""
    for sym in _BINDER_SYMS:
        if tok.startswith(sym):
            return sym, tok[len(sym):]
    return None, ""


@dataclass
class StmtVars:
    """The identifier structure of a proposition, at token level: distinct
    free-candidate names (in first-seen order), schematic `?vars`, and
    statement-local binder-bound names."""
    free: tuple[str, ...]
    schematic: tuple[str, ...]
    bound: tuple[str, ...]


def _analyze_statement(text: str) -> StmtVars:
    r"""Split a proposition's tokens into free candidates, schematic ``?vars``
    and binder-bound names.

    A binder token (``\<forall>``, ``\<lambda>``, ``ALL``, ...) binds the run of
    name tokens that follows it (``\<forall>x y.`` binds ``x`` ``y``); a ``?``
    followed by a name is a schematic ``Var``.  A name that is bound or schematic
    anywhere is removed from the free candidates — a token-level approximation of
    scoping (a name both bound in one subterm and free in another is treated as
    bound throughout; documented, phase-1).
    """
    return _analyze_tokens(_stmt_tokens(text))


def _analyze_tokens(toks: list[str]) -> StmtVars:
    """The token-level core of :func:`_analyze_statement`, split out so M6 can
    re-analyse a *rewritten* token list (chunks replaced by non-name reference
    tokens) without a text round-trip."""
    bound: list[str] = []
    schematic: list[str] = []
    free: list[str] = []

    def _bind(nm: str) -> None:
        if nm not in bound:
            bound.append(nm)

    i, n = 0, len(toks)
    while i < n:
        t = toks[i]
        sym, rest = _binder_prefix(t)
        if sym is not None or t in _BINDER_WORDS:
            j = i + 1
            if sym is not None and rest:
                if _is_name(rest):          # the glued first bound var
                    _bind(rest)
            elif j < n and toks[j] == "!":  # `\<exists> ! x` unique-existence
                j += 1
            while j < n and _is_name(toks[j]):
                _bind(toks[j])
                j += 1
            i = j
            continue
        if t == "?" and i + 1 < n and _is_name(toks[i + 1]):
            if toks[i + 1] not in schematic:
                schematic.append(toks[i + 1])
            i += 2
            continue
        if _is_name(t) and t not in free:
            free.append(t)
        i += 1
    boundset, schset = set(bound), set(schematic)
    free = [f for f in free if f not in boundset and f not in schset]
    return StmtVars(tuple(free), tuple(schematic), tuple(bound))


@dataclass
class ClassifyCtx:
    """Per-lemma inputs to :func:`classify_identifier`: theory-defined constant
    names (bucket a), context-bound variable names (bucket b), and the harvested
    corpus constant list (bucket c)."""
    entry_names: frozenset[str] = frozenset()
    context_vars: frozenset[str] = frozenset()
    corpus_consts: frozenset[str] = CORPUS_CONSTANTS


def classify_identifier(name: str, ctx: ClassifyCtx) -> tuple[str, str]:
    """Classify an identifier as ``("var"|"const", source)`` under the layered
    heuristic.  ``source`` records which bucket decided, for audit."""
    if name in ctx.context_vars:
        return "var", "context"
    if (name in graph._KEYWORDS or name in graph._PROOF_METHODS
            or name in graph._ATTRIBUTES):
        return "const", "syntax"
    if name in ctx.entry_names:
        return "const", "entry"
    if name in ctx.corpus_consts:
        return "const", "corpus"
    return "var", "default"


# --- const_est: distinct constants in the as-written proposition ------------
#
# The Width sibling of `w1_est` (free vars) and `w2_src` (total tokens): a
# *vocabulary* count — the distinct constant symbols the stated proposition
# mentions.  Two token classes carry constants.  Letter-initial *names* the
# layered classifier already tags `const` (`Suc`, `insert`) — the discarded
# complement of `w1_est`'s free vars.  And *operator symbols* written as notation
# (`+`, `\<in>`, `\<le>`), which the classifier never sees because `_is_name`
# gates on a leading ASCII letter — yet these are genuine HOL/Pure constants
# (`plus`, `Set.member`, `less_eq`); they are spelled as glyphs, not thereby less
# a constant (the tiny Pure core aside, essentially every operator is defined in
# HOL/HOL-Library).
#
# This is an *estimator* (`_est`): it counts the as-written glyph, not the
# elaborated `Const`.  So overloaded `+` (nat vs int) collapses to one; a constant
# written two ways is not deduped; an abbreviation (`\<noteq>` = `Not`/`eq`) is
# one glyph; and an ASCII multi-char operator the tokeniser splits is over-split.
# Canonicalising glyph -> constant name would need Isabelle's notation table (a
# cached-heap job, like the method table) — deferred.  Structural syntax
# (brackets, `,` `.` `::`), binders (quantifiers and big operators — carried on
# the bound-variable axis), and numerals are not counted as constants.
_ASCII_OP_CONSTS = frozenset("+-*/=<>@")
_BINDER_SET = frozenset(_BINDER_SYMS)
# Exactly one `\<sym>` and nothing else (no `\<^ctrl>`, no glued word/subscript):
# a spaced, standalone operator token.  `\<And>c_b` (binder+var), `\<Gamma>\<^sub>M`
# (subscripted letter) and `x\<in>y` (unspaced) all fail this and so are not
# mistaken for operators — the tokeniser only leaves a lone `\<in>` when it was
# written spaced, as operators almost always are.
_SINGLE_SYM_RE = re.compile(r"\\<\w+>\Z")


def _is_operator_const(tok: str) -> bool:
    r"""Whether ``tok`` is an operator-symbol constant (`+`, `\<in>`, `\<le>`) —
    a non-identifier, non-numeral symbol that denotes a constant, i.e. not a
    bracket, binder, letter symbol, ``\<^ctrl>`` symbol, or structural delimiter."""
    if not tok or tok[0].isalpha() or tok[0].isdigit():
        return False                      # identifier (name/subscripted) or numeral
    if tok in _ASCII_OP_CONSTS:
        return True                       # ASCII arithmetic/relational operator
    if _SINGLE_SYM_RE.match(tok):         # a lone, spaced \<sym>
        return (tok not in _BRACKET_PAIRS and tok not in _CLOSERS
                and tok not in _BINDER_SET and tok not in LETTER_SYMS)
    return False                          # punctuation, glued binders, letter subscripts


def _operator_consts(toks: list[str]) -> tuple[str, ...]:
    """Distinct operator-symbol constants in ``toks``, in first-seen order."""
    seen: list[str] = []
    for t in toks:
        if _is_operator_const(t) and t not in seen:
            seen.append(t)
    return tuple(seen)


def _canonicalize_consts(names: tuple[str, ...]) -> tuple[str, ...]:
    r"""Distinct constants after mapping each operator glyph to its canonical
    Isabelle constant via the committed :data:`NOTATION` table — the semantic
    vocabulary behind ``const_canon_est``.  Word constants (not glyph-keyed) pass
    through unchanged; a glyph the table doesn't carry falls back to itself, so
    this only ever *dedups*, never loses, a constant.  Collapses overloaded
    notations of one constant: `\<le>`, `\<ge>`, `\<subseteq>` all become
    `Orderings.ord_class.less_eq`, so `x \<le> y \<and> A \<subseteq> B` counts 2
    constants (`less_eq`, `conj`), not the 3 distinct glyphs of ``const_est``."""
    seen: list[str] = []
    for nm in names:
        c = NOTATION.get(nm, nm)
        if c not in seen:
            seen.append(c)
    return tuple(seen)


@dataclass
class W1:
    """M1 estimator columns for one goal step.  ``free`` is the headline
    ``w1_est`` (distinct free variables); ``schematic`` and ``bound`` are the
    separate ``Var`` and bound-variable columns.  ``provenance`` maps each free
    candidate to its ``(kind, source)`` for calibration auditing.  ``const`` /
    ``const_names`` are the Width vocabulary sibling — the distinct constants
    (`const_est`), free-candidate names tagged const plus operator symbols."""
    free: int = 0
    schematic: int = 0
    bound: int = 0
    free_names: tuple[str, ...] = ()
    provenance: dict[str, tuple[str, str]] = field(default_factory=dict)
    const: int = 0
    const_names: tuple[str, ...] = ()
    # `const_canon` is `const` after canonicalising operator glyphs to their
    # Isabelle constant via the committed notation table — the *semantic*
    # vocabulary (`\<le>`/`\<subseteq>` -> one `less_eq`), <= `const`.
    const_canon: int = 0
    const_canon_names: tuple[str, ...] = ()


def w1_est(step: Step, ctx: ClassifyCtx) -> W1:
    r"""**M1 estimator** — distinct free variables in a goal step's as-written
    proposition, by the layered classifier, with the schematic and bound-variable
    columns reported separately.  Non-goal / bare-statement steps are ``W1()``."""
    if step.kind != "goal" or not step.stmt_text:
        return W1()
    toks = _stmt_tokens(step.stmt_text)
    sv = _analyze_tokens(toks)
    prov = {nm: classify_identifier(nm, ctx) for nm in sv.free}
    free_vars = tuple(nm for nm in sv.free if prov[nm][0] == "var")
    # const_est: free-candidate names tagged const (disjoint from the operator
    # symbols, which are never `_is_name` and so never in `sv.free`) + notation.
    const_names = tuple(nm for nm in sv.free if prov[nm][0] == "const")
    const_names += _operator_consts(toks)
    canon = _canonicalize_consts(const_names)
    return W1(len(free_vars), len(sv.schematic), len(sv.bound), free_vars, prov,
              len(const_names), const_names, len(canon), canon)


# `fix x y`, `obtain a b where ...` — only the LEADING run of identifier tokens
# is the bound-variable list.  Capturing that run (rather than everything up to
# `where`/`::`/end) stops at the first quote or symbol, so a same-line trailing
# proposition — `fix VS assume "VS \<subseteq> insert a A"` — cannot leak its
# constants (`insert`) into the context as spurious variables.
_FIX_NAMES_RE = re.compile(
    r"^(?:fix|obtain)\s+((?:[A-Za-z][\w']*\s+)*[A-Za-z][\w']*)")
# A `fixes`/`for` header clause: an identifier must follow the keyword (a real
# clause is `fixes n :: t`, never `fixes = ...`), which rejects stray `fixes`/`for`
# words in ML antiquotations (`val fixes = map ...`).  Names run up to the next
# header keyword.
_HEADER_FIX_RE = re.compile(
    r"\b(?:fixes|for)\s+([A-Za-z].*?)(?=\b(?:fixes|assumes|shows|where|for|is)\b|$)",
    re.S)
_IDENT_RE = re.compile(r"[A-Za-z][\w']*")


def _fix_line_names(stripped: str) -> set[str]:
    """Variable names bound by a ``fix``/``obtain`` step line."""
    m = _FIX_NAMES_RE.match(stripped)
    if not m:
        return set()
    return set(_IDENT_RE.findall(m.group(1)))


def _header_fix_names(sec: TheorySection, entry: Entry) -> set[str]:
    """Variable names bound by the lemma header's ``fixes``/``for`` clauses.
    Each clause's names run up to a ``::`` type ascription or the next keyword;
    for ``fixes n :: nat and f :: "..."`` this yields ``{n, f}``."""
    lines = sec.source()
    end = entry.decl_end_line or entry.thy_line
    header = " ".join(lines[entry.thy_line - 1:end])
    names: set[str] = set()
    for clause in _HEADER_FIX_RE.findall(header):
        # Split on `and`; take the leading identifier of each (before any `::`).
        for part in re.split(r"\band\b", clause):
            head = part.split("::", 1)[0]
            ids = _IDENT_RE.findall(head)
            if ids:
                names.add(ids[0])
    return names


def build_ctx(sec: TheorySection, entry: Entry, steps: list[Step],
              corpus_consts: frozenset[str] = CORPUS_CONSTANTS) -> ClassifyCtx:
    """Assemble the classifier context for one lemma: entry-DB constant names,
    the context-bound variables (header ``fixes``/``for`` + in-proof ``fix`` /
    ``obtain`` steps), and the corpus constant list."""
    entry_names = frozenset(e.name for e in sec.entries)
    context_vars = _header_fix_names(sec, entry)
    lines = sec.source()
    for s in steps:
        if s.kind == "context" and s.kw in ("fix", "obtain"):
            context_vars |= _fix_line_names(lines[s.line - 1].strip())
    return ClassifyCtx(entry_names, frozenset(context_vars), corpus_consts)


# --- M4 / M6: cross-step redundancy + extension-sensitivity -----------------
#
# M4 asks: within a proof block, how much of the stated width is the *same*
# subterms restated across steps ("wide and trivial" delta-tracing)?  M6 asks:
# how much of that width is removable by naming repeated subterms as fresh
# definitions (the extension-rule analogy)?  Both approximate elaborated
# subterms by **well-bracketed token chunks** and share one greedy extractor.
#
# A *chunk* is a bracket-balanced contiguous token span — the inclusive span of a
# matched bracket pair (parens / square / brace / cartouche / record / semantic
# brackets), at every nesting level.  This is the bracket forest of the token
# stream: O(n), deterministic, and each chunk literally "well-bracketed" (opens
# with a bracket, closes with its match).  It is deliberately *cruder* than the
# reference term DAG: it misses repeated *unbracketed* subterms (`Suc n` restated
# without parens) and over-segments nothing.  Configuration-style width — the
# phenomenon M4 targets — is parenthesised (`(q, tps, ...)`, `\<lparr>...\<rparr>`),
# so the estimator is monotone in the same signal; phase 2 calibrates the gap.
# Alternative considered and rejected for v1: *all* balanced contiguous
# subsequences (O(n^2), and its heavy overlap swamps the chunk multiset with
# fragments), which is closer to "all subterms" but neither cheap nor testable.

# Matched bracket pairs, opener -> closer.  Symbol brackets (`\<open>`, records,
# semantic `\<lbrakk>`) tokenise as single tokens, so they key like ASCII ones.
_BRACKET_PAIRS = {
    "(": ")", "[": "]", "{": "}",
    "\\<open>": "\\<close>", "\\<lparr>": "\\<rparr>", "\\<lbrakk>": "\\<rbrakk>",
}
_CLOSERS = frozenset(_BRACKET_PAIRS.values())
# A chunk must be at least this many tokens to count as a shared subterm — below
# it the "subterm" is a lone atom in brackets (`( x )`) and carries no redundancy
# signal.  Five tokens admits a 2-tuple `( a , b )` / a 2-list `[ a , b ]`.
_MIN_CHUNK_TOKENS = 4
# The reference token a chunk is rewritten to under M6 extraction: a single,
# non-name symbol (so it counts 1 toward w2_src and is ignored by w1_est, exactly
# as a fresh nullary definition would be).
_CHUNK_REF = "\\<hole>"


def _bracket_spans(tokens: list[str],
                   min_len: int = _MIN_CHUNK_TOKENS) -> list[tuple[str, int, int]]:
    r"""Every matched bracket pair in ``tokens`` as ``(text, start, end)`` — the
    inclusive-opener/exclusive-closer token span, normalised to a single-spaced
    string, for spans of at least ``min_len`` tokens.  Nesting yields the full
    bracket forest (inner pairs as well as outer).  Unmatched brackets are
    tolerated and skipped (Isar statements are balanced by construction)."""
    spans: list[tuple[str, int, int]] = []
    stack: list[int] = []
    for i, t in enumerate(tokens):
        if t in _BRACKET_PAIRS:
            stack.append(i)
        elif t in _CLOSERS and stack:
            opener = stack[-1]
            if _BRACKET_PAIRS[tokens[opener]] == t:
                stack.pop()
                if i - opener + 1 >= min_len:
                    spans.append((" ".join(tokens[opener:i + 1]), opener, i + 1))
    return spans


def _bracket_chunks(tokens: list[str],
                    min_len: int = _MIN_CHUNK_TOKENS) -> list[str]:
    """The chunk multiset of one statement: the normalised text of every bracket
    span (:func:`_bracket_spans`), with multiplicity."""
    return [text for text, _, _ in _bracket_spans(tokens, min_len)]


def _multiset_jaccard(a: list[str], b: list[str]) -> float | None:
    """Multiset Jaccard index of two chunk lists — ``sum(min counts) /
    sum(max counts)``.  ``None`` when *neither* statement has any chunk (an
    undefined overlap, distinct from a genuine 0 = both have chunks, share none)."""
    ca, cb = Counter(a), Counter(b)
    keys = set(ca) | set(cb)
    if not keys:
        return None
    inter = sum(min(ca[k], cb[k]) for k in keys)
    union = sum(max(ca[k], cb[k]) for k in keys)
    return inter / union


def _non_overlapping(occs: list[tuple[int, int, int]]) -> list[tuple[int, int, int]]:
    """Greedily keep a non-overlapping subset of ``(stmt, start, end)`` chunk
    occurrences (earliest-start first, per statement).  Equal-valued spans in one
    statement are normally disjoint already; this guards the nested-equal case."""
    chosen: list[tuple[int, int, int]] = []
    last_end: dict[int, int] = {}
    for occ in sorted(occs):
        si, a, b = occ
        if a >= last_end.get(si, -1):
            chosen.append(occ)
            last_end[si] = b
    return chosen


def _greedy_extract(tok_lists: list[list[str]], min_len: int,
                    max_k: int | None):
    r"""Greedily factor repeated bracket chunks out of a block's goal statements.

    At each step, pick the highest-*value* chunk (``value = (occurrences - 1) *
    token length``, ties broken by chunk text for determinism) that still has at
    least two intact, non-overlapping occurrences, and "extract" it: mark those
    token positions consumed (so nested/overlapping chunks can no longer claim
    them) and record one reference per occurrence.  Extracting a chunk that
    occurs ``occ`` times collapses ``occ - 1`` redundant copies (node-sharing: the
    subterm is stored once, references are free), so ``compressed`` drops by
    ``(occ - 1) * length`` — exactly M6's value formula.

    Stops after ``max_k`` extractions (M6) or, when ``max_k`` is ``None``, once no
    positive-value repeat remains (M4's full DAG).  Returns ``(k_done,
    compressed_tokens, extracted_values, ref_spans_per_stmt)`` where the last maps
    each statement to its extracted ``(start, end)`` spans, for rewriting.
    """
    spans_per = [_bracket_spans(t, min_len) for t in tok_lists]
    consumed = [[False] * len(t) for t in tok_lists]
    compressed = sum(len(t) for t in tok_lists)
    extracted: list[str] = []
    ref_spans: list[list[tuple[int, int]]] = [[] for _ in tok_lists]
    k = 0
    while max_k is None or k < max_k:
        occ: dict[str, list[tuple[int, int, int]]] = defaultdict(list)
        for si, spans in enumerate(spans_per):
            for text, a, b in spans:
                if not any(consumed[si][p] for p in range(a, b)):
                    occ[text].append((si, a, b))
        best = None            # (value, text, usable, length)
        for text, occs in occ.items():
            usable = _non_overlapping(occs)
            if len(usable) < 2:
                continue
            length = len(text.split(" "))
            value = (len(usable) - 1) * length
            cand = (value, text)
            if best is None or cand > (best[0], best[1]):
                best = (value, text, usable, length)
        if best is None or best[0] <= 0:
            break
        value, text, usable, length = best
        for si, a, b in usable:
            for p in range(a, b):
                consumed[si][p] = True
            ref_spans[si].append((a, b))
        compressed -= (len(usable) - 1) * length
        extracted.append(text)
        k += 1
    return k, compressed, extracted, ref_spans


def _rewrite(tokens: list[str], spans: list[tuple[int, int]]) -> list[str]:
    """Rewrite ``tokens`` replacing each extracted ``(start, end)`` span with a
    single :data:`_CHUNK_REF` reference token (as if named a fresh definition)."""
    out: list[str] = []
    i = 0
    for a, b in sorted(spans):
        out.extend(tokens[i:a])
        out.append(_CHUNK_REF)
        i = b
    out.extend(tokens[i:])
    return out


@dataclass
class BlockRedundancy:
    """M4 estimator for one proof block: the DAG compression ratio and the
    per-adjacent-goal-pair overlaps.  ``dag_ratio`` is ``>= 1``; higher means the
    same large subterms are restated across the block's goal steps."""
    block: int
    n_goals: int
    total_tokens: int
    compressed_tokens: int
    dag_ratio: float
    overlaps: tuple[float | None, ...]


def cross_step_redundancy(
        steps: list[Step],
        min_len: int = _MIN_CHUNK_TOKENS) -> list[BlockRedundancy]:
    r"""**M4 estimator** — per proof block, over its goal-stating propositions:

    * ``dag_ratio_est`` = total tokens / tokens after factoring out every repeated
      well-bracketed chunk (:func:`_greedy_extract` run to exhaustion).
    * ``adjacent_overlap_est`` = multiset Jaccard of the chunk multisets of each
      consecutive goal pair.

    Restricted to a single block (no global DAG over the whole development).
    Blocks with no goal statement are skipped; a lone-goal block has empty
    ``overlaps`` and ``dag_ratio`` reflecting only intra-statement repeats.
    """
    out: list[BlockRedundancy] = []
    for block_steps in _blocks(steps):
        goals = [s for s in block_steps if s.kind == "goal" and s.stmt_text]
        if not goals:
            continue
        tok_lists = [_stmt_tokens(g.stmt_text) for g in goals]
        total = sum(len(t) for t in tok_lists)
        _, compressed, _, _ = _greedy_extract(tok_lists, min_len, None)
        dag = total / compressed if compressed else 1.0
        chunks = [_bracket_chunks(t, min_len) for t in tok_lists]
        overlaps = tuple(_multiset_jaccard(chunks[i], chunks[i + 1])
                         for i in range(len(chunks) - 1))
        out.append(BlockRedundancy(goals[0].block, len(goals), total,
                                   compressed, dag, overlaps))
    return out


@dataclass
class ExtensionCurve:
    """M6 estimator for one proof block: the width-vs-``k`` curve.  ``w1`` and
    ``w2`` are the *summed* ``w1_est`` / ``w2_src`` over the block's goal steps
    after greedily extracting the top-``k`` repeated chunks as fresh definitions;
    the drop from ``k=0`` bounds how much width naming can remove."""
    block: int
    n_goals: int
    ks: tuple[int, ...]
    w1: tuple[int, ...]
    w2: tuple[int, ...]


_M6_KS = (0, 1, 2, 4, 8, 16)


def extension_curve(steps: list[Step], ctx: ClassifyCtx,
                    ks: tuple[int, ...] = _M6_KS,
                    min_len: int = _MIN_CHUNK_TOKENS) -> list[ExtensionCurve]:
    r"""**M6 estimator** — per proof block, the width-vs-``k`` curve: recompute
    summed ``w1_est`` / ``w2_src`` over the block's goal statements after
    extracting the ``k`` most valuable repeated chunks as fresh definitions, for
    each ``k`` in ``ks``.

    A heuristic *upper* bound on removable width: the extracted definitions' own
    width is not charged back, so the curve shows the best case for
    naming.  ``k=0`` reproduces the raw summed widths.  Blocks with no goal
    statement are skipped.
    """
    out: list[ExtensionCurve] = []
    for block_steps in _blocks(steps):
        goals = [s for s in block_steps if s.kind == "goal" and s.stmt_text]
        if not goals:
            continue
        tok_lists = [_stmt_tokens(g.stmt_text) for g in goals]
        w1s: list[int] = []
        w2s: list[int] = []
        for k in ks:
            _, _, _, ref_spans = _greedy_extract(tok_lists, min_len, k)
            rewritten = [_rewrite(t, ref_spans[i])
                         for i, t in enumerate(tok_lists)]
            w1s.append(sum(_w1_count(toks, ctx) for toks in rewritten))
            w2s.append(sum(len(toks) for toks in rewritten))
        out.append(ExtensionCurve(goals[0].block, len(goals), tuple(ks),
                                   tuple(w1s), tuple(w2s)))
    return out


def _w1_count(toks: list[str], ctx: ClassifyCtx) -> int:
    """Headline ``w1_est`` (distinct free variables) for a token list, via the
    layered classifier — the recompute primitive M6 runs on rewritten statements
    (where :data:`_CHUNK_REF` refs are non-names and so drop out)."""
    sv = _analyze_tokens(toks)
    return sum(1 for nm in sv.free if classify_identifier(nm, ctx)[0] == "var")


def _blocks(steps: list[Step]) -> list[list[Step]]:
    """Partition a proof's steps by ``block`` id, preserving first-appearance
    order — each group is one proof block's steps in source order."""
    groups: dict[int, list[Step]] = {}
    order: list[int] = []
    for s in steps:
        if s.block not in groups:
            groups[s.block] = []
            order.append(s.block)
        groups[s.block].append(s)
    return [groups[b] for b in order]


def removable_w2_at_8(steps: list[Step], ctx: ClassifyCtx) -> float:
    r"""**M6 scalar** — the fraction of a proof's total stated width removable by
    naming up to 8 repeated chunks per block: ``1 - sum(w2[k=8]) / sum(w2[k=0])``
    summed over every block's :func:`extension_curve`.

    The cross-corpus reduction of the M6 curve to one per-proof scalar (the full
    per-block curve stays in the ``lemma`` view).  Summed over blocks — all
    stated width in the denominator, each block's own extraction in the numerator
    (M6 never crosses a block) — so a proof whose width is mostly
    non-redundant single goals scores near ``0``.  ``0.0`` when the proof states
    no width.  Uses only ``k \in {0, 8}`` (two extraction passes, not the full
    six-point curve).  A heuristic *upper* bound: the extracted definitions' own
    width is not charged back (an explicit non-goal)."""
    curves = extension_curve(steps, ctx, ks=(0, 8))
    w2_0 = sum(c.w2[0] for c in curves)
    w2_8 = sum(c.w2[1] for c in curves)
    return 1 - w2_8 / w2_0 if w2_0 else 0.0


# --- M3: frame ratio (delta-tracing overhead) ------------------------------
#
# For a goal step whose proposition relates two values of a designated
# *configuration type*, the frame ratio measures how much of the configuration
# is restated versus actually changed: `frame_ratio = mentioned / max(changed, 1)`.
# Delta-tracing style (write out the whole config, change one component) gives a
# large ratio; framing style (state only the delta) gives a ratio near 1.
#
# Purely syntactic and heuristic (source parsing cannot resolve types), so the
# "configuration type" degrades to a per-corpus TABLE of names,
# and a step whose proposition shows no configuration signal yields `None` (a
# coverage statistic, never a guess).  There is no estimator/reference split: the
# source computation *is* the definition.
#
# Detection rules (conservative v1):
#   mentioned = configured-selector occurrences  (record/field/`fst`/`snd` accesses)
#             + `!` occurrences                   (list indexing)
#             + `:=` occurrences                  (each update site both accesses
#                                                   AND changes a component)
#   changed   = `:=` occurrences                  (record / function / list update)
#   applicable iff the proposition has a relation (`=` or a configured relation
#              name) AND a configuration signal (a selector / `!` / `:=` /
#              constructor); else `None`.
# Deferred (documented): the *constructor-diff* source of `changed` — aligning two
# written-out constructor/tuple terms and diffing them component-wise — is not
# detected in v1, so a delta-tracing step that states both configs in full with no
# explicit `:=` reports changed=0 (ratio = mentioned), which is still directionally
# correct (large).  `:=` counting reads the raw text (the tokeniser splits `:=`
# into `:` and `=`).


@dataclass(frozen=True)
class CorpusConfig:
    """Per-corpus M3 descriptor: names that mark the configuration type.
    ``selectors`` drive ``mentioned``; ``constructors`` / ``relations`` extend the
    applicability signal (a constructor application or a named simulation relation
    still makes a proposition "about the configuration").  Loaded from TOML."""
    constructors: frozenset[str] = frozenset()
    selectors: frozenset[str] = frozenset()
    relations: frozenset[str] = frozenset()


def load_corpus_config(path) -> dict[str, CorpusConfig]:
    """Load a TOML M3 config (one ``[corpus]`` table per corpus) into a mapping
    from corpus name to :class:`CorpusConfig`.  Reads with the stdlib
    ``tomllib`` — data, not code, so a corpus config is safe to hand-write and
    contribute.  Unknown keys are ignored; missing lists default to empty."""
    import tomllib
    with open(path, "rb") as fh:
        data = tomllib.load(fh)
    return {
        name: CorpusConfig(
            frozenset(tbl.get("constructors", ())),
            frozenset(tbl.get("selectors", ())),
            frozenset(tbl.get("relations", ())),
        )
        for name, tbl in data.items()
    }


@dataclass
class FrameRatio:
    """M3 for one goal step: component-access count, changed-component count, and
    their ratio."""
    mentioned: int
    changed: int
    ratio: float


def frame_ratio(step: Step, cfg: CorpusConfig) -> FrameRatio | None:
    """**M3** — the frame ratio of a goal step under corpus config ``cfg``, or
    ``None`` when the proposition shows no configuration signal (not a relation,
    or mentions nothing configured).  See the section header for the exact rules."""
    if step.kind != "goal" or not step.stmt_text:
        return None
    text = step.stmt_text
    toks = _stmt_tokens(text)
    tokset = set(toks)
    has_relation = "=" in tokset or any(r in tokset for r in cfg.relations)
    updates = text.count(":=")
    indexing = toks.count("!")
    selectors = sum(toks.count(s) for s in cfg.selectors)
    has_config = (selectors or indexing or updates
                  or any(c in tokset for c in cfg.constructors))
    if not (has_relation and has_config):
        return None
    mentioned = selectors + indexing + updates
    return FrameRatio(mentioned, updates, mentioned / max(updates, 1))


@dataclass
class M3Summary:
    """M3 aggregated over a proof's goal steps: how many were computable (a
    configuration relation), the computed ratios, and the coverage."""
    n_goals: int
    ratios: tuple[float, ...]

    @property
    def n_computed(self) -> int:
        return len(self.ratios)

    @property
    def coverage(self) -> float:
        """Fraction of goal steps for which M3 was computable (``0.0`` for a
        proof with no goal steps)."""
        return self.n_computed / self.n_goals if self.n_goals else 0.0

    @property
    def max_ratio(self) -> float | None:
        return max(self.ratios) if self.ratios else None

    @property
    def mean_ratio(self) -> float | None:
        return sum(self.ratios) / len(self.ratios) if self.ratios else None


def frame_ratios(steps: list[Step], cfg: CorpusConfig) -> M3Summary:
    """**M3 aggregate** — frame ratios over a proof's goal steps plus coverage.
    Every ``goal`` step counts in the denominator; only those with a
    configuration relation contribute a ratio (the rest are the uncovered
    fraction)."""
    goals = [s for s in steps if s.kind == "goal"]
    ratios = tuple(fr.ratio for fr in (frame_ratio(s, cfg) for s in goals)
                   if fr is not None)
    return M3Summary(len(goals), ratios)


# --- CLI roll-up: per-proof analysis + JSONL records -----------------------
#
# The `query shape` subcommand family (summary | steps | lemma | widest |
# census) needs the metrics *composed* per proof, in a fixed order: `fanin` and
# `live` are annotated onto the Step list in place, so they must run before any
# per-step record is emitted (or the record carries zeros).  `analyze_proof`
# runs that pipeline once; `summarize` rolls a proof up to the aggregate numbers
# the tables and the census stream report; the two `*_record` helpers are the
# JSONL join contract (stable (theory, lemma, line) keys, an `_est` suffix on
# every estimator column).  All *formatting* stays in the command layer
# (`shape_cmds`) — this section is pure computation, so it stays testable against
# hand-computed fixture values with no CLI in the loop.


@dataclass
class ProofMetrics:
    r"""The full shape analysis of one proof (entry), computed in a single pass.

    ``steps`` are annotated in place (``fanin`` / ``live`` set by the pipeline);
    ``ctx`` is the classifier context for their ``w1_est``; ``live_max`` /
    ``live_mean`` are M5b; ``intro_consume`` is M5c; ``redundancy`` is M4 per
    block; ``inductions`` is the ADD #3 per-invocation induction-discipline list
    (one :class:`Induction` per ``induct`` / ``induction`` call in the proof).
    M6 (:func:`extension_curve`) is *not* precomputed — it is the one heavy pass
    and only the ``lemma`` deep-dive needs it, so callers run it on demand.
    """
    sec: TheorySection
    entry: Entry
    steps: list[Step]
    ctx: ClassifyCtx
    live_max: int
    live_mean: float
    intro_consume: IntroConsume
    redundancy: list[BlockRedundancy]
    inductions: list[Induction]

    @property
    def theory(self) -> str:
        return self.sec.theory

    @property
    def lemma(self) -> str:
        return self.entry.name

    @property
    def goals(self) -> list[Step]:
        """The proof's goal-stating steps — where the width metrics attach."""
        return [s for s in self.steps if s.kind == "goal"]


def analyze_proof(sec: TheorySection, entry: Entry,
                  corpus_consts: frozenset[str] = CORPUS_CONSTANTS
                  ) -> ProofMetrics | None:
    """Run the full per-proof shape pipeline once, in dependency order
    (fan-in and live-fact annotation mutate ``steps``, so they precede any
    per-step record).  Returns ``None`` for an entry with no proof body at all —
    a bare definition.  A one-liner ``by`` proof DOES yield a record (its lone
    closing step); it did not before, which is what dropped 3.5% of AFP proofs
    from the census, trivial ones first.

    **No axis here reads the method table.**  ``Step.method`` is whatever stands
    in introducer position (:func:`graph._leading_method`), so :func:`trivial_frac`
    and :func:`method_kind_counts` are positional like every other axis, and
    binding a different namespace cannot move a shape record.  It could once, and
    that was the defect: a table narrower than the corpus silently emptied
    ``trivial_frac``'s denominator rather than misclassifying anything, so the
    loss was invisible in the output.

    The bound table still matters *elsewhere* in this module —
    :func:`classify_identifier` is position-blind and genuinely needs one — so
    :func:`graph.configure_namespace` and friends have not stopped being useful;
    they simply no longer decide what a proof's automation looks like."""
    steps = _scan_steps(sec, entry)
    if not steps:
        return None
    annotate_fanin(steps, sec)
    live_max, live_mean = live_fact_space(steps, sec)
    ctx = build_ctx(sec, entry, steps, corpus_consts)
    ic = introduce_consume(steps, sec)
    red = cross_step_redundancy(steps)
    inductions = scan_inductions(sec, entry)
    return ProofMetrics(sec, entry, steps, ctx, live_max, live_mean, ic, red,
                        inductions)


def analyze_sections(sections: list[TheorySection],
                     corpus_consts: frozenset[str] = CORPUS_CONSTANTS):
    """Yield a :class:`ProofMetrics` for every entry across ``sections`` that
    has a proof body, in source order — the shared spine of every ``shape``
    subcommand.  Entries with no proof (definitions) are silently skipped, so a
    consumer sees only the measurable proofs."""
    for sec in sections:
        for entry in sec.entries:
            pm = analyze_proof(sec, entry, corpus_consts)
            if pm is not None:
                yield pm


def _dist(vals: list[float]) -> tuple[float, float, float]:
    """``(max, mean, p90)`` of a value list, or ``(0, 0, 0)`` when empty.  p90 is
    the nearest-rank order statistic (deterministic, no interpolation) — the
    same convention the cross-corpus analysis script uses."""
    if not vals:
        return 0.0, 0.0, 0.0
    s = sorted(vals)
    p90 = s[min(len(s) - 1, int(0.9 * len(s)))]
    return s[-1], sum(s) / len(s), p90


def _region_counts(sec: TheorySection, lo: int, hi: int
                   ) -> tuple[int, int, int, int]:
    r"""Line and token counts over the inclusive 1-based span ``[lo, hi]``, split
    **raw** vs **code** (raw minus prose).

    Prose is the one shared "not proof" line-set (:func:`graph._noise_spans`:
    ``text``/``text_raw`` blocks, ``\<comment>`` annotations, entry preambles), so
    the *code* lines here are exactly the lines ``grep`` / ``methods`` / the call
    graph treat as live — no second notion of "code".  Returns
    ``(lines, lines_code, tokens, tokens_code)``; all zero for an empty or absent
    span (e.g. the proof span of a bare definition, whose ``proof_line`` is 0).
    ``prose = raw - code`` for both, so no prose column is stored.  The prose
    line-set is memoised on the section — every proof in a theory shares it."""
    lines = sec.source()
    hi = min(hi, len(lines))
    if lo < 1 or hi < lo:
        return (0, 0, 0, 0)
    prose = getattr(sec, "_prose_line_set", None)
    if prose is None:
        prose = _line_set(_noise_spans(sec))
        sec._prose_line_set = prose
    n = nc = t = tc = 0
    for ln in range(lo, hi + 1):
        ntok = len(_stmt_tokens(lines[ln - 1]))
        n += 1
        t += ntok
        if ln not in prose:
            nc += 1
            tc += ntok
    return (n, nc, t, tc)


@dataclass
class ProofSummary:
    """Per-proof aggregate row — the unit of ``shape summary``'s table and the
    ``shape census`` JSONL stream.  Distributions are over the proof's *goal*
    steps with an as-written proposition (the metric-bearing ones); ``n_bare``
    counts goal steps with none (``show ?thesis`` / ``case`` — width hidden from
    source, so excluded from the w1/w2 distributions but reported alongside).

    ``n_bare`` used to **pool two different things** — "bare by construction"
    and "the scanner found no proposition" — which is what hid issue #9(b) for
    as long as it did: a wrapped statement was silently booked here, where
    nobody would look for it.  ``bare_kinds`` is the split [bare-provenance];
    ``n_bare`` is unchanged and is its sum, so a rise in it is now readable
    (``construction`` moves with writing style, ``unfound`` with the scanner)
    without invalidating a stored row."""
    theory: str
    lemma: str
    n_steps: int
    n_goals: int
    n_bare: int
    # Length axis: proof-block nesting, 1-based to match the 2015 mining paper's
    # convention (§2.2, Fig 5) — 1 = a flat proof (all steps in the lemma's own
    # `proof … qed`), 2 = one nested `proof`/`{` block, etc.  = max step `depth`
    # (0-based) + 1.  A proof reaching here always has >=1 step, so >=1.
    depth_max: int
    w2_max: int
    w2_mean: float
    w2_p90: float
    w1_max: int
    w1_mean: float
    # Width (vocabulary): const_est distribution over the proof's stated goal
    # steps — distinct constants (names tagged const + operator notation) per
    # step, max and mean.  Estimator (`_est`): as-written constant *symbols*, not
    # elaborated `Const`s (overloading collapses, notation not canonicalised).
    const_max: int
    const_mean: float
    # Width (semantic vocabulary): const_canon_est — `const_est` after mapping
    # operator glyphs to canonical constants (committed notation table), so
    # overloaded notations of one constant collapse.  Estimator; <= `const_*`.
    const_canon_max: int
    const_canon_mean: float
    fanin_max: int
    fanin_mean: float
    # M5a reconciliation: the count of goal steps that cite >=1 explicit premise.
    # `fanin_mean` averages over ALL goal steps — and most `by simp`/`by auto`
    # steps cite nothing explicit — so it is "explicit source-cited premises per
    # goal step".  With `fanin_mean` and `n_goals`
    # this recovers the *conditional* fan-in (mean over citing steps only,
    # `fanin_mean*n_goals/fanin_cited` — the apples-to-apples comparator) and the
    # citation-density fraction `fanin_cited/n_goals`.  0 for a goal-free proof.
    fanin_cited: int
    live_max: int
    live_mean: float
    dag_max: float
    intro: int
    consume: int
    # M5c three-way split: `both` = lines that introduce AND cite (`from a have
    # b:`).  With `intro`/`consume` already present, `intro - both` and
    # `consume - both` recover the disjoint introduce-only / consume-only counts,
    # so one scalar carries the whole split (abstract metric A2's refinement).
    both: int
    ratio: float | None
    # The "trivial" axis and the M6 cross-corpus scalar — the two additions that
    # make this record a *sufficient statistic* per proof (every fingerprint
    # number a scalar reduction, nothing fetched live by the analysis layer).
    trivial_frac: float | None
    removable_w2: float
    # The "automation" axis's profile: discharged steps per method kind
    # (:data:`METHOD_KIND_NAMES`).  A finer grain than `trivial_frac` — its keys
    # sum to the same discharged-step denominator.
    method_kinds: dict[str, int]
    # Why each bare goal step is bare (:data:`BARE_KINDS`).  Sums to `n_bare`,
    # which is left exactly as it was — this REFINES the field rather than
    # redefining it, so a stored census row stays comparable with a new one.
    # `unfound` is the one that carries information about the scanner; the other
    # two are facts about how the proof is written.
    bare_kinds: dict[str, int]
    # ADD #3 induction discipline (LiFtEr source inputs), reduced per proof from
    # `scan_inductions`.  `n_induct` counts induction invocations; the rest
    # describe them (widest, deepest generalization, rule-bearing, recursion-rule
    # counts).  All 0 for a proof that inducts on nothing.
    n_induct: int
    induct_terms_max: int
    induct_arbitrary_max: int
    induct_rule: int
    induct_recursion: int
    # Length axis (size): line and token counts of the proof *body*
    # (`proof_line..body_end_line`), raw and *code* (raw minus prose — the shared
    # `_noise_spans` `text`/`\<comment>`/preamble set).  Prose is derivable
    # (`proof_lines - proof_lines_code`), so it is not stored.  `entry_lines` is
    # the raw whole-entry span (`Entry.line_count`: statement + proof + attached
    # doc) — the coarser size the `largest` command reports, carried here so a
    # proof's size and the other shape axes join in one record.
    proof_lines: int
    proof_lines_code: int
    proof_tokens: int
    proof_tokens_code: int
    entry_lines: int
    # Provenance.  The Isabelle *session* the theory was declared by, or None
    # when the load had no session context (a bare `.thy` path, stdin).  Last
    # and defaulted so the positional construction above is unchanged; emitted
    # FIRST in the record, where a reader looks for the coarsest key.  A corpus
    # run's records are otherwise attributable only by theory name, which is not
    # unique across the AFP: 505 of 8,849 theory names are used by more than one
    # theory (`Examples` 19 times, `Preliminaries` 15, `Misc` 8), so
    # `(theory, lemma)` alone cannot say which entry a record came from.
    session: str | None = None


def summarize(pm: ProofMetrics) -> ProofSummary:
    """Roll a :class:`ProofMetrics` up to its aggregate row.  w1/w2
    distributions are over goal steps with an as-written proposition; fan-in is
    over all goal steps; ``dag_max`` is the widest block's M4 ratio (``1.0`` when
    no block has repeated chunks); ``trivial_frac`` and ``removable_w2`` are the
    "trivial" and M6-removable scalars over the whole proof."""
    goals = pm.goals
    stated = [s for s in goals if s.stmt_text]
    depth_max = max((s.depth for s in pm.steps), default=0) + 1
    w2_max, w2_mean, w2_p90 = _dist([float(w2_src(s)) for s in stated])
    # One w1_est pass per stated step yields both the free-var (w1) and the
    # constant (const_est) Width distributions.
    w1s = [w1_est(s, pm.ctx) for s in stated]
    w1_max, w1_mean, _ = _dist([float(w.free) for w in w1s])
    const_max, const_mean, _ = _dist([float(w.const) for w in w1s])
    const_canon_max, const_canon_mean, _ = _dist(
        [float(w.const_canon) for w in w1s])
    fanin_max, fanin_mean, _ = _dist([float(s.fanin) for s in goals])
    fanin_cited = sum(1 for s in goals if s.fanin)
    dag_max = max((b.dag_ratio for b in pm.redundancy), default=1.0)
    ic = pm.intro_consume
    ind = summarize_inductions(pm.inductions)
    e = pm.entry
    p_lines, p_lines_code, p_tokens, p_tokens_code = (
        _region_counts(pm.sec, e.proof_line, e.body_end_line)
        if e.proof_line else (0, 0, 0, 0))
    return ProofSummary(
        pm.theory, pm.lemma, len(pm.steps), len(goals), len(goals) - len(stated),
        depth_max,
        int(w2_max), w2_mean, w2_p90, int(w1_max), w1_mean,
        int(const_max), const_mean, int(const_canon_max), const_canon_mean,
        int(fanin_max), fanin_mean, fanin_cited, pm.live_max, pm.live_mean,
        dag_max, ic.introduce, ic.consume, ic.both, ic.ratio,
        trivial_frac(pm.steps), removable_w2_at_8(pm.steps, pm.ctx),
        method_kind_counts(pm.steps), bare_kind_counts(pm.steps),
        ind.n, ind.terms_max, ind.arbitrary_max, ind.n_rule, ind.n_recursion,
        p_lines, p_lines_code, p_tokens, p_tokens_code, e.line_count,
        session=pm.sec.session)


def step_record(step: Step, ctx: ClassifyCtx, lines: list[str],
                cfg: CorpusConfig | None = None) -> dict:
    r"""One **per-step JSONL record** — the join contract (deliverable #2).

    Carries stable position keys (``theory`` / ``lemma`` / ``line``, plus
    ``block`` / ``depth`` for structure) so a value can later be joined against a
    per-step LLM-tractability experiment with no re-instrumentation.  Estimator
    columns are suffixed ``_est`` (``w1_est`` and its schematic/bound companions);
    the exact source metrics (``w2_src``, ``fanin``, ``live``) are not.  Metric
    fields are ``0`` / ``false`` on non-goal or bare-statement steps — a *uniform*
    schema (every step, every column present) is friendlier to a columnar join
    than a sparse one; filter on ``kind == "goal"`` downstream.

    When a corpus ``cfg`` is supplied, the M3 ``frame_ratio`` columns are added
    (``null`` where the step shows no configuration signal); without one they are
    absent, so the schema is config-gated and self-describing.
    """
    w1 = w1_est(step, ctx)
    cited, _covered = _line_facts(step, lines)
    rec = {
        "theory": step.theory,
        "lemma": step.lemma,
        "line": step.line,
        "block": step.block,
        "depth": step.depth,
        "kind": step.kind,
        "kw": step.kw,
        "goal_cmd": step.goal_cmd,
        "method": step.method,
        "label": step.label,
        "stmt_start": step.stmt_start,
        "stmt_end": step.stmt_end,
        "w2_src": w2_src(step),
        "w1_est": w1.free,
        "w1_schematic_est": w1.schematic,
        "w1_bound_est": w1.bound,
        "const_est": w1.const,
        "const_canon_est": w1.const_canon,
        "fanin": step.fanin,
        "fanin_covered": step.fanin_covered,
        "live": step.live,
        "introduces": introduces(step),
        "consumes": bool(cited),
    }
    if cfg is not None:
        fr = frame_ratio(step, cfg)
        rec["frame_ratio"] = fr.ratio if fr is not None else None
        rec["frame_mentioned"] = fr.mentioned if fr is not None else None
        rec["frame_changed"] = fr.changed if fr is not None else None
    return rec


def summary_record(ps: ProofSummary) -> dict:
    """One **per-proof JSONL record** (``shape census`` / ``shape summary
    --json``): the :class:`ProofSummary` aggregates as a flat dict, same stable
    ``(theory, lemma)`` keys, ``_est`` suffix on the estimator aggregates."""
    return {
        # Provenance first — the coarsest key, and the one that disambiguates a
        # theory name repeated across AFP entries.  `null` when the load had no
        # session context.
        "session": ps.session,
        "theory": ps.theory,
        "lemma": ps.lemma,
        "n_steps": ps.n_steps,
        "n_goals": ps.n_goals,
        "n_bare": ps.n_bare,
        # Length axis: max proof-block nesting (1 = flat), the 2015 paper's depth.
        "depth_max": ps.depth_max,
        "w2_src_max": ps.w2_max,
        "w2_src_mean": ps.w2_mean,
        "w2_src_p90": ps.w2_p90,
        "w1_est_max": ps.w1_max,
        "w1_est_mean": ps.w1_mean,
        # Width (vocabulary): distinct constants per stated step, max/mean.
        "const_est_max": ps.const_max,
        "const_est_mean": ps.const_mean,
        # Width (semantic vocabulary): canonicalised distinct constants per step.
        "const_canon_est_max": ps.const_canon_max,
        "const_canon_est_mean": ps.const_canon_mean,
        "fanin_max": ps.fanin_max,
        "fanin_mean": ps.fanin_mean,
        # M5a is "explicit source-cited premises per goal step" — `fanin_cited`
        # (goal steps citing >=1) is the denominator that turns `fanin_mean` into
        # the *conditional* fan-in (the mean over citing steps only).
        "fanin_cited": ps.fanin_cited,
        "live_max": ps.live_max,
        "live_mean": ps.live_mean,
        "dag_ratio_est_max": ps.dag_max,
        "introduce": ps.intro,
        "consume": ps.consume,
        "both": ps.both,
        "ratio": ps.ratio,
        "trivial_frac": ps.trivial_frac,
        # `_est`: removability is measured over estimator bracket-chunks, so it
        # is an estimate of the true removable width (the never-conflate rule: an
        # estimator never shares a column with an exact value) — unlike
        # `trivial_frac`, which reads exact method names.
        "removable_w2_est_at_8": ps.removable_w2,
        # The automation axis's method-kind histogram (fixed keys, a per-proof
        # reduction — the one structured field, kept grouped rather than spread
        # across five columns).
        "method_kinds": ps.method_kinds,
        # Why the `n_bare` steps are bare; the three keys sum to `n_bare`.
        "bare_kinds": ps.bare_kinds,
        # ADD #3 induction discipline (LiFtEr source inputs): induction
        # invocations in the proof and their shape.  `n_induct` 0 => this proof
        # inducts on nothing (the others are then 0 too).  Entry-level: the
        # induction-using fraction, generalization depth (`induct_arbitrary_max`),
        # and recursion-rule fraction (`induct_recursion`/`n_induct`) reduce from
        # these — a sufficient statistic, no re-scan.
        "n_induct": ps.n_induct,
        "induct_terms_max": ps.induct_terms_max,
        "induct_arbitrary_max": ps.induct_arbitrary_max,
        "induct_rule": ps.induct_rule,
        "induct_recursion": ps.induct_recursion,
        # Length axis (size): proof-body line/token counts, raw + code (prose =
        # raw - code, not stored); `entry_lines` is the whole-entry span
        # (`largest`'s measure).  Exact, no `_est`.
        "proof_lines": ps.proof_lines,
        "proof_lines_code": ps.proof_lines_code,
        "proof_tokens": ps.proof_tokens,
        "proof_tokens_code": ps.proof_tokens_code,
        "entry_lines": ps.entry_lines,
    }
