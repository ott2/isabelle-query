#!/usr/bin/env python3
r"""Generate the committed *minimal* method / attribute / keyword namespace —
the shipped fallback table for isabelle_query's token router.

WHY THIS EXISTS
    query approximates Isabelle's parser by tokenising `.thy` source.  To tell
    a *fact citation* (a call-graph edge) apart from a *proof method* (`by simp`),
    an *attribute* (`[OF g]`) and a structural *keyword* (`proof`, `qed`, `and`),
    it needs Isabelle's namespaces.  At runtime the router resolves the *session-
    exact* table from a loaded heap (see `_namespace_resolve`); this generator
    produces only the **committed fallback** used when Isabelle is unavailable —
    deliberately the *minimal* table: the **Pure** dump, the universal core every
    session transitively imports (`rule`, `assumption`, `simp`, `OF`, ...).  It is
    minimal on purpose: HOL's `auto`/`blast`/`induct` are NOT Pure, so they come
    from session resolution, never imposed on a session that does not import HOL.

SOURCES
    methods     the running **Pure** image's method name space
    attributes  the running **Pure** image's attribute name space
                (both via `_namespace_resolve.dump("Pure")` — the same ML dump
                the runtime uses; RETIRES the old `.thy`/`.ML` registration-site
                *source scan*, which was only as complete as its list of idioms,
                the reason `induction` was once dropped)
    keywords    the declarative `Pure/Pure.thy` `keywords ... begin` block plus
                the `bootstrap_keywords` of `Pure/Thy/thy_header.ML` (a fixed
                table — scanning it is not reinventing anything, so it stays)

    A few argument-modifier tokens (`add`, `del`, `OF`, `THEN`) have no
    declaration site — parsed inline by individual methods — so the router keeps
    that short, auditable tier-2 list itself.

USAGE
    python3 scripts/extract_isabelle_namespace.py \
        [--session Pure] [--src /path/to/Isabelle/src] [--version LABEL] \
        [--out PATH] [--date YYYY-MM-DD]

    Needs a built `--session` heap (Pure is always built) for the dump, and
    `--src` (the Isabelle source tree) for the keyword scan.
    Defaults: --session Pure; --src from $ISABELLE_SRC, else
              /Applications/Isabelle2025-2.app/src; --out the committed data module.
"""
from __future__ import annotations

import argparse
import os
import re
import sys
from pathlib import Path

# The runtime dump lives in the package; the generator consumes it for the
# method/attribute tables (see the module docstring for why the source scan is
# retired).  Keywords still come from the declarative source scan below.
from isabelle_query._namespace_resolve import _base, dump, resolve_project

# The distribution sessions unioned into the committed *census* table, chosen by
# measuring what AFP entries actually build on (scripts/afp_base_logics.py over
# 988 sessions).  The HOL family carries the automation methods the census keys
# on (`auto`/`blast`/`induct`/`metis`/…); HOL-Eisbach adds the reusable method
# combinators (`match`/`solves`/`determ`/…); HOL-Decision_Procs adds the decision
# procedures (`cooper`/`mir`/`ferrack`/`dlo`/`ring`/`approximation`/…, used by 16
# AFP sessions).  Excluded on evidence: the non-HOL object logics (FOL/ZF/CCL/…
# underlie 1 of 988 AFP entries, and share the core method *names* with HOL) and
# the frequent lemma/codegen libraries (HOL-Computational_Algebra & co. register
# no proof methods).  All are distribution sessions, so the union is reproducible
# on any machine with the Isabelle distribution.
_CENSUS_UNION = ("HOL", "HOL-Library", "HOL-Analysis", "HOL-Eisbach",
                 "HOL-Decision_Procs")


def _pure_block_keywords(src: Path) -> dict[str, str]:
    """{keyword: kind} from Pure/Pure.thy's `keywords ... begin` block.

    Only alphabetic names are kept (symbolic keywords such as `!!`, `==`, `+`
    are never tokenised as identifiers, so they cannot collide with a fact
    name).  Kind is the group's `:: <kind>`, or ``"minor"`` for the leading
    un-kinded group."""
    pure = src / "Pure" / "Pure.thy"
    m = re.search(r"(?ms)^keywords\b(.*?)^begin\b",
                  pure.read_text(encoding="utf-8", errors="replace"))
    if not m:
        raise SystemExit(f"could not find the keywords block in {pure}")
    out: dict[str, str] = {}
    # Groups are separated by a line-leading `and ` (the leading group has
    # none); splitting on that avoids tripping over a quoted name like "and".
    for piece in re.split(r"\n\s+and\s", m.group(1)):
        if "::" in piece:
            names_part, kind_part = piece.split("::", 1)
            km = re.match(r"\s*([A-Za-z_]+)", kind_part)
            kind = km.group(1) if km else ""
        else:
            names_part, kind = piece, "minor"
        for nm in re.findall(r'"([^"]+)"', names_part):
            if nm[:1].isalpha():
                out[nm] = kind
    return out


def _bootstrap_keywords(src: Path) -> dict[str, str]:
    """The alphabetic `bootstrap_keywords` of Pure/Thy/thy_header.ML — `and`,
    `begin`, `imports`, the document headings, etc.  Entries name either a
    quoted literal (`"and"`) or a `val xN = "..."` constant, which we resolve."""
    th = (src / "Pure" / "Thy" / "thy_header.ML").read_text(
        encoding="utf-8", errors="replace")
    consts = dict(re.findall(r'val\s+(\w+)\s*=\s*"([^"]+)"', th))
    # The list ends at `];`.  It holds `]`s of its own (`command_spec
    # (Keyword.thy_begin, ["theory"])`), and ending at the first one lost
    # the entries after it, `theory` and `ML` among them [api-keywords].
    m = re.search(r"bootstrap_keywords\b.*?add_keywords\s*\[(.*?)\];", th, re.S)
    out: dict[str, str] = {}
    if m:
        for tok in re.findall(r'\(\(\s*("?[\w]+"?)\s*,', m.group(1)):
            nm = tok.strip('"') if tok.startswith('"') else consts.get(tok, "")
            if nm[:1].isalpha():
                out[nm] = "bootstrap"
    return out


def extract_keywords(src: Path) -> dict[str, str]:
    kws = _pure_block_keywords(src)
    for nm, kind in _bootstrap_keywords(src).items():
        kws.setdefault(nm, kind)
    return kws


def infer_version(src: Path) -> str:
    m = re.search(r"Isabelle[0-9]{4}(?:-[0-9]+)?", str(src.resolve()))
    return m.group(0) if m else "unknown"


_HEADER = '''\
"""Minimal (Pure) method / attribute / keyword namespace — GENERATED, do not edit.

The committed *fallback* table; the runtime resolves the session-exact table.

Regenerate with::

    python3 scripts/extract_isabelle_namespace.py

This is the *minimal* fallback table (the Pure core).  At runtime the router
resolves the session-exact table from a loaded heap; this ships for when
Isabelle is unavailable — so it deliberately omits HOL's auto/blast/induct,
which come from session resolution, not from assuming HOL.

Provenance:
    Isabelle:    {version}
    Extracted:   {date}
    Methods:     {nmeth} (Pure image method name space — ML_process -l Pure)
    Attributes:  {nattr} (Pure image attribute name space)
    Keywords:    {nkw} (Pure.thy keyword table + thy_header bootstrap; {src})

These power isabelle_query's token *router*: a proof-body token is a fact
citation (a call-graph edge) only if it is none of a proof method, an
attribute, a keyword, or a numeral.  Method occurrences are not discarded —
they feed the `methods` query.
"""

# proof methods (`by simp`, `apply (rule r)`) — never a fact citation, but a
# method-usage datum.
PROOF_METHODS = frozenset({{
{methods}
}})

# attributes (`[OF g]`, `simp del:`, `[simp]`) — modifiers, never citations.
ATTRIBUTES = frozenset({{
{attributes}
}})

# outer-syntax keywords (commands, proof language, quasi-commands, bootstrap):
# structural, never a fact citation.
KEYWORDS = frozenset({{
{keywords}
}})
'''


_CENSUS_HEADER = '''\
"""Broad (HOL-family union) method / attribute namespace — the router's
**import-time default** and the table `shape census` binds.  GENERATED, do not
edit.

Unlike the minimal Pure fallback in ``_isabelle_namespace.py`` (which the *per-
project* verbs narrow to a session-exact table at runtime), the whole-corpus
census needs one **fixed, broad, reproducible** table: a census spans many
logics with no single session to resolve against, and its output ships in
``data/`` so it must regenerate identically with **no Isabelle**.  This is that
table — the union of the base-logic heaps below, over the Pure floor.

It is also what ``graph`` binds at import, so a caller using the package as a
library gets the same numbers a ``query`` run prints without configuring
anything; the Pure floor is reached deliberately, via
``graph.use_pure_namespace()``, and only a positively non-HOL project wants it.

Why a union is correct here (not just convenient): of the three census axes that
read the table, M5a fan-in never consults it (a separate fixed extractor), and
the automation axis reads it only in ``by``/``apply``/``proof`` *introducer*
position — where a match is a real method by construction, so a broader table
only adds correct recognitions.  Only the M1/M5b free-identifier estimator is
position-blind, and there a union can over-exclude a variable whose name
collides with a foreign-logic method; that sliver is measured, not assumed
(see ``scripts/census_table_sensitivity.py``).

Regenerate with::

    python3 scripts/extract_isabelle_namespace.py --census

Provenance:
    Isabelle:    {version}
    Extracted:   {date}
    Union of:    {sessions}
    Methods:     {nmeth} (union of the above heaps' method name spaces)
    Attributes:  {nattr} (union of the above heaps' attribute name spaces)

Keywords are logic-invariant (Pure outer syntax), so the census reuses
``_isabelle_namespace.KEYWORDS`` and this module carries none.
"""

# proof methods across the HOL family — `by auto`, `by (induct n)`, `by metis`.
PROOF_METHODS = frozenset({{
{methods}
}})

# attributes across the HOL family — `[simp]`, `[intro]`, `[measurable]`.
ATTRIBUTES = frozenset({{
{attributes}
}})
'''


def _fmt_set(names) -> str:
    out, line = [], "    "
    for nm in sorted(names):
        tok = repr(nm) + ", "
        if len(line) + len(tok) > 78:
            out.append(line.rstrip())
            line = "    "
        line += tok
    if line.strip():
        out.append(line.rstrip())
    return "\n".join(out)


def _write_census(ns) -> int:
    """Generate the broad census union table from the built base-logic heaps.

    Reuses ``resolve_project`` — the same union-over-Pure-floor the per-project
    router uses — so there is no second dump path; here we just serialise its
    result for the census's fixed, reproducible table."""
    from isabelle_query import _namespace_resolve as nsr
    sessions = [s.strip() for s in ns.union.split(",") if s.strip()]
    out = ns.out or str(Path(__file__).resolve().parent.parent
                        / "src" / "isabelle_query" / "_census_namespace.py")
    r = resolve_project(sessions)
    if r["source"] == "committed" or not r.get("sessions"):
        sys.stderr.write(
            "no base-logic heap resolved — build the union sessions first "
            f"({', '.join(sessions)}); census table needs a running Isabelle.\n")
        return 1
    methods = sorted(r["methods"])
    attributes = sorted(r["attributes"])
    version = ns.version or nsr._version_id(nsr._isabelle_bin())
    if ns.date:
        date = ns.date
    else:
        import datetime
        date = datetime.date.today().isoformat()

    Path(out).write_text(_CENSUS_HEADER.format(
        version=version, date=date, sessions=", ".join(r["sessions"]),
        nmeth=len(methods), nattr=len(attributes),
        methods=_fmt_set(methods), attributes=_fmt_set(attributes)),
        encoding="utf-8")
    print(f"wrote {out}")
    print(f"  union {r['sessions']}: {len(methods)} methods, "
          f"{len(attributes)} attributes")
    # The census automation axis needs these HOL methods the Pure fallback lacks.
    for staple in ("auto", "blast", "induct", "induction", "metis", "simp"):
        got = staple in r["methods"]
        print(f"  {staple!r}: {'present' if got else 'ABSENT'} "
              f"({'ok' if got else 'UNEXPECTED'})")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Generate the committed minimal (Pure) namespace.")
    ap.add_argument("--session", default="Pure",
                    help="logic image to dump methods/attributes from "
                         "(default Pure — the minimal universal core)")
    ap.add_argument("--src", default=os.environ.get(
        "ISABELLE_SRC",
        "/Applications/Isabelle2025-2.app/src"))
    ap.add_argument("--version", default=None)
    ap.add_argument("--date", default=None, help="YYYY-MM-DD; default today")
    ap.add_argument("--census", action="store_true",
                    help="generate the broad census union table "
                         "(_census_namespace.py) instead of the Pure fallback")
    ap.add_argument("--union", default=",".join(_CENSUS_UNION),
                    help="comma-separated base logics to union for --census "
                         f"(default: {','.join(_CENSUS_UNION)})")
    ap.add_argument("--out", default=None)
    ns = ap.parse_args()

    if ns.census:
        return _write_census(ns)

    ns.out = ns.out or str(
        Path(__file__).resolve().parent.parent
        / "src" / "isabelle_query" / "_isabelle_namespace.py")
    src = Path(ns.src)
    if not (src / "Pure" / "Pure.thy").exists():
        raise SystemExit(f"--src {src} is not an Isabelle src dir "
                         f"(no Pure/Pure.thy)")
    version = ns.version or infer_version(src)
    if ns.date:
        date = ns.date
    else:
        import datetime
        date = datetime.date.today().isoformat()

    # Methods/attributes: the running image's own name spaces (base-folded to the
    # bare token the router matches).  Keywords: the declarative source scan.
    raw_m, raw_a, theory, proc = dump(ns.session)
    if not raw_m and not raw_a:
        sys.stderr.write("no tables dumped — is the session heap built?\n")
        if proc:
            sys.stderr.write(proc.stdout + proc.stderr)
        return 1
    methods, attributes = sorted(_base(raw_m)), sorted(_base(raw_a))
    keywords = extract_keywords(src)

    Path(ns.out).write_text(_HEADER.format(
        version=version, src=src, date=date,
        nmeth=len(methods), nattr=len(attributes), nkw=len(keywords),
        methods=_fmt_set(methods), attributes=_fmt_set(attributes),
        keywords=_fmt_set(keywords)), encoding="utf-8")
    print(f"wrote {ns.out}")
    print(f"  {ns.session} image ({theory}): {len(methods)} methods, "
          f"{len(attributes)} attributes, {len(keywords)} keywords")
    # Pure has simp/rule/OF but NOT auto/blast/induct (those are HOL) — the check
    # asserts the universal core is present and confirms HOL is absent.
    for staple, group, want in [("simp", methods, True), ("rule", methods, True),
                                ("auto", methods, False), ("OF", attributes, True),
                                ("and", keywords, True), ("proof", keywords, True)]:
        got = staple in group
        ok = "ok" if got == want else "UNEXPECTED"
        print(f"  {staple!r}: {'present' if got else 'absent'} ({ok})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
