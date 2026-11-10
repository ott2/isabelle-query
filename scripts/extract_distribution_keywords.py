#!/usr/bin/env python3
r"""Generate `_distribution_keywords`: which outer-syntax keywords each
Isabelle distribution theory declares, and what each imports [api-keywords].

The committed `_isabelle_namespace.KEYWORDS` is Pure's table.  HOL and the
other distribution sessions declare more in their theory headers' `keywords`
clauses (`fun`, `datatype`, `record`, `typedef`, `morphisms`, ...).  A
keyword is active only in a theory that imports, perhaps indirectly, the
one declaring it: `domain` is a keyword under HOLCF and a free name under
Main.  So the table is per theory, with the import edges, and
`lexicon.is_keyword` takes the closure of what a project imports.

Every keyword in a clause is read, not only the declaring commands that
`parsing.scan_keywords` keeps for the parser.  The table is declarative, as
Pure's is (`extract_isabelle_namespace.py`), so no Isabelle process is run.

    python scripts/extract_distribution_keywords.py [--src DIR] [--check]

`--src` defaults to $ISABELLE_SRC, else /Applications/Isabelle2025-2.app/src.
Point it at the released version, not a development checkout.  `--check`
prints the counts and writes nothing.

Theories are named `Session.Theory`, by the first session (in
`iter_sessions` order) whose closure contains the file.  An import resolves
as `lexicon.resolve_import` resolves it at run time: a qualified name as
written, a bare one in the importing theory's own session first, then in
the distribution's unique theory of that name.
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

from isabelle_layout import iter_sessions, parse_thy_imports, session_theories

from isabelle_query import _isabelle_namespace as pure
from isabelle_query.lexicon import header_keywords, resolve_import

OUT = Path(__file__).resolve().parents[1] / "src" / "isabelle_query" \
    / "_distribution_keywords.py"


def main() -> int:
    argv = sys.argv[1:]
    src = Path(os.environ.get("ISABELLE_SRC",
                              "/Applications/Isabelle2025-2.app/src"))
    if "--src" in argv:
        src = Path(argv[argv.index("--src") + 1])
    owner: dict[Path, str] = {}
    for s in iter_sessions(src):
        for name, p in session_theories(s):
            owner.setdefault(p.resolve(), f"{s.name}.{name}")
    names = frozenset(owner.values())
    keywords: dict[str, list[str]] = {}
    imports: dict[str, list[str]] = {}
    unresolved = 0
    for p, q in sorted(owner.items(), key=lambda kv: kv[1]):
        kws = header_keywords(p.read_text(encoding="utf-8", errors="replace"))
        kws -= pure.KEYWORDS
        if kws:
            keywords[q] = sorted(kws)
        deps = []
        for imp in parse_thy_imports(p):
            r = resolve_import(imp, q.split(".", 1)[0], names)
            if r is None:
                unresolved += 1
                if "--verbose" in argv:
                    print(f"  unresolved: {q} imports {imp}", file=sys.stderr)
            elif r != q:
                deps.append(r)
        if deps:
            imports[q] = deps
    # Keep only what can reach a keyword: a theory whose closure declares
    # none adds nothing to `lexicon.active_keywords`, nor does an edge to it.
    reaches = set(keywords)
    grew = True
    while grew:
        grew = False
        for q, deps in imports.items():
            if q not in reaches and any(d in reaches for d in deps):
                reaches.add(q)
                grew = True
    imports = {q: [d for d in deps if d in reaches]
               for q, deps in imports.items() if q in reaches}
    imports = {q: deps for q, deps in imports.items() if deps}
    every = set().union(*map(set, keywords.values()))
    version = next((part.removesuffix(".app") for part in src.resolve().parts
                    if part.startswith("Isabelle")), "unknown")
    print(f"{version}: {len(owner)} theories, {len(keywords)} declare "
          f"keywords, {len(every)} beyond Pure's {len(pure.KEYWORDS)}; "
          f"{unresolved} imports unresolved", file=sys.stderr)
    if "--check" in argv:
        return 0

    def table(d: dict[str, list[str]]) -> str:
        return "\n".join(f"    {k!r}: ({', '.join(map(repr, v))},),"
                         for k, v in sorted(d.items()))

    OUT.write_text(f'''"""Outer-syntax keywords per Isabelle distribution theory, and the
import edges between those theories -- GENERATED, do not edit
[api-keywords].

Regenerate with::

    python scripts/extract_distribution_keywords.py

Provenance: {version}, {len(owner)} theories, {len(keywords)} of which
declare keywords beyond Pure's ({len(every)} words).  Identifier-shaped
keywords only: a symbolic one can never be a name.
"""

# Theory -> the keywords its own header declares, beyond Pure's.
KEYWORDS = {{
{table(keywords)}
}}

# Theory -> the distribution theories it imports directly.
IMPORTS = {{
{table(imports)}
}}
''', encoding="utf-8")
    print(f"wrote {OUT}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
