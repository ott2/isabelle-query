r"""Resolve the router's method / attribute namespace from a *running* Isabelle,
with a version-keyed cache so currency costs no per-invocation Isabelle tax.

Isabelle's method / attribute tables are a function of the **installed Isabelle**
(its heaps), not of the queried project, so they change only when Isabelle is
upgraded or a heap rebuilt.  That lets us stay "always up to date" while spawning
Isabelle at most once per change, by keying a cache on a cheap fingerprint of the
heap:

    cache hit  (fingerprint unchanged)  -> read the cache file        (~ms)
    cache miss (Isabelle changed/first) -> dump from Isabelle once     (~2.7s)
    no Isabelle at all                  -> the committed static table  (fallback)

**Purity contract.**  Importing this module spawns nothing and stats nothing:
the fingerprint is a pure ``stat`` of the heap file plus the version id parsed
from the binary path, so the *warm* path (cache hit) is a file read and the
runtime stays pure-Python.  Isabelle is invoked (``dump``) only on a cache-miss,
never at import, never on the warm path, and — the no-build guard — **only when
the session's heap already exists** (``ML_process -l S`` would otherwise *build*
an absent ``S``).  A dump that hangs (a heap being rebuilt underneath us) is
bounded by a subprocess timeout and degrades to the committed table rather than
blocking the query indefinitely.

This is the runtime counterpart of ``scripts/extract_isabelle_namespace.py``:
that reconstructs the tables by regex-scanning registration *sites* in the
distribution source (only as complete as its list of idioms — the reason the
``Induct.gen_induct_setup`` factory once dropped ``induction``); here we consume
the table a loaded heap already assembled, complete by construction.
"""
from __future__ import annotations

import glob
import hashlib
import json
import os
import re
import shutil
import subprocess
from pathlib import Path

# The ML dump script is package data (a *runtime* asset now, not a scripts/
# tool): it enumerates the live method/attribute name spaces of a loaded heap.
_ML = Path(__file__).resolve().parent / "_dump_namespace.ML"
_DEFAULT_ISABELLE = "/Applications/Isabelle2025-2.app/bin/isabelle"
_VERSION_RE = re.compile(r"Isabelle[0-9]{4}(?:-[0-9]+)?")

# Bound on a single dump.  The cold dump is ~2.7s; a generous ceiling keeps a
# heap that is being rebuilt underneath us from hanging the query — on timeout
# `dump` returns empty and the caller degrades to the committed table.  Override
# with $QUERY_DUMP_TIMEOUT (seconds).
_DUMP_TIMEOUT = 120.0


def _isabelle_bin() -> str:
    """The `isabelle` CLI: $ISABELLE_TOOL, else PATH, else the 2025-2 bundle."""
    return (os.environ.get("ISABELLE_TOOL") or shutil.which("isabelle")
            or _DEFAULT_ISABELLE)


def _dump_timeout() -> float:
    try:
        return float(os.environ.get("QUERY_DUMP_TIMEOUT") or _DUMP_TIMEOUT)
    except ValueError:
        return _DUMP_TIMEOUT


def dump(session: str = "HOL", theory: str | None = None,
         dirs: list[str] | None = None
         ) -> tuple[set[str], set[str], str | None,
                    subprocess.CompletedProcess | None]:
    """Run the ML dump against a loaded `session` heap; return
    ``(methods, attributes, theory_scope, process)``.  ``theory`` overrides the
    namespace scope (default: the heap's top loaded theory).  ``dirs`` are extra
    session-root directories (``-d``): a distribution session (``HOL``) resolves
    by name alone, but a project/AFP session is only *known* to ``ML_process -l``
    when its ROOT directory is on the search path — pass the session's own root
    dir here or the dump fails with "Undefined session".  On a timeout the tables
    come back empty and ``process`` is ``None`` — the caller then falls back to
    the committed table rather than blocking."""
    env = dict(os.environ)
    if theory:
        env["QUERY_DUMP_THEORY"] = theory
    cmd = [_isabelle_bin(), "ML_process", "-l", session]
    for d in (dirs or []):
        cmd += ["-d", d]
    cmd += ["-r", "-f", str(_ML)]
    try:
        proc = subprocess.run(
            cmd, capture_output=True, text=True, env=env,
            timeout=_dump_timeout())
    except (subprocess.TimeoutExpired, OSError):
        return set(), set(), None, None
    methods: set[str] = set()
    attribs: set[str] = set()
    scope: str | None = None
    for line in proc.stdout.splitlines():
        parts = line.split("\t")
        if len(parts) != 3 or parts[0] != "DUMP":
            continue
        _, kind, name = parts
        if kind == "METHOD":
            methods.add(name)
        elif kind == "ATTRIB":
            attribs.add(name)
        elif kind == "THEORY":
            scope = name
    return methods, attribs, scope, proc


def _base(names: set[str]) -> set[str]:
    """Fold qualified names to the bare token the router matches: ``extern``
    qualifies a name (``HOL.simp``, ``Pure.rule``) only when the base collides
    across namespaces, but a proof writes the unqualified ``simp``."""
    return {n.rsplit(".", 1)[-1] for n in names}


def _version_id(isabelle: str) -> str:
    """The `IsabelleYYYY[-N]` identifier from the binary path (`unknown` if the
    path carries no version — e.g. a bare `isabelle` on PATH)."""
    m = _VERSION_RE.search(str(Path(isabelle).resolve()))
    return m.group(0) if m else "unknown"


def _isabelle_home(isabelle: str | None = None) -> Path:
    """``$ISABELLE_HOME`` — the distribution root, which is the parent of the
    ``bin/`` holding the resolved ``isabelle`` script.  ``.resolve()`` first, so
    the usual ``~/.local/bin/isabelle`` symlink into the installed tree lands on
    the tree and not on ``~/.local``."""
    return Path(isabelle or _isabelle_bin()).resolve().parent.parent


def _heaps_dirs(version_id: str, isabelle: str | None = None) -> list[str]:
    """The heap search path, in Isabelle's own order — USER heaps first, then
    the DISTRIBUTION heaps.  Both names come from ``etc/settings``::

        ISABELLE_HEAPS="$ISABELLE_HOME_USER/heaps"
        ISABELLE_HEAPS_SYSTEM="$ISABELLE_HOME/heaps"

    and the order mirrors ``Store.input_dirs``, which reads the user directory
    ahead of the system one — so a locally rebuilt session shadows the shipped
    heap, as it does for Isabelle itself.

    Only the first was consulted before, which made every session shipped
    *prebuilt* with the distribution invisible: on a stock install nothing has
    ever been built into the user directory, so `HOL` is not found, no heap can
    be dumped, and the router silently falls back to the committed table.  The
    machine this was written on cannot show the bug — it has `HOL` **and**
    `Pure` in both directories — which is why the tests build synthetic trees
    and never reach for a real heap.

    Reading both never weakens the no-build guarantee: this only ever *detects*
    heaps that already exist, and finding more of them can only turn a spawn
    that was refused into one that is safe.  Isabelle's ``system_heaps`` option
    (search the system directory alone) is not modelled — it is not visible
    without a spawn, and the difference only matters for a session built in both
    places, where the two heaps are the same session either way.
    """
    user = os.environ.get("ISABELLE_HEAPS") or str(
        Path.home() / ".isabelle" / version_id / "heaps")
    system = os.environ.get("ISABELLE_HEAPS_SYSTEM") or str(
        _isabelle_home(isabelle) / "heaps")
    return [user] if system == user else [user, system]


def _heap_file(version_id: str, session: str,
               isabelle: str | None = None) -> Path | None:
    """The session heap file, located by pure globbing (no spawn).  Searches
    every directory in :func:`_heaps_dirs`, in order, and returns the first
    match under any ML-platform subdir — or None if unbuilt/absent."""
    for d in _heaps_dirs(version_id, isabelle):
        hits = sorted(glob.glob(os.path.join(d, "*", session)))
        if hits:
            return Path(hits[0])
    return None


def _built_sessions(version_id: str, isabelle: str | None = None) -> set[str]:
    """The set of session names with a built heap — **one** glob of
    ``<heaps>/*/*`` per heap directory (no spawn), so augmenting a project with
    N declared sessions costs a directory scan and a set intersection, not N
    per-session globs.  The union across directories: a session counts as built
    wherever its heap lives."""
    return {os.path.basename(p)
            for d in _heaps_dirs(version_id, isabelle)
            for p in glob.glob(os.path.join(d, "*", "*"))
            if os.path.isfile(p)}


def isabelle_fingerprint(session: str = "HOL",
                         isabelle: str | None = None) -> str:
    """A cheap, spawn-free fingerprint of the table we *would* extract: the
    version id, the session, and the heap file's size + mtime.  Empty string when
    no Isabelle binary is resolvable at all (→ committed fallback).  If the binary
    is present but the heap is not yet built, the fingerprint degrades to the
    version id alone — still valid, just coarser."""
    isabelle = isabelle or _isabelle_bin()
    if not (isabelle and Path(isabelle).exists()):
        return ""
    vid = _version_id(isabelle)
    parts = [vid, session]
    # Pass the binary on rather than letting `_heap_file` re-resolve one: a
    # caller that named an Isabelle must be fingerprinted against THAT
    # distribution's heaps, not against whatever is on PATH.
    heap = _heap_file(vid, session, isabelle)
    if heap is not None:
        st = heap.stat()
        parts += [str(heap), str(st.st_size), str(st.st_mtime_ns)]
    # Fold in the dump script's own stat: the cached table is a function of the
    # ML that produced it, so a change to the enumeration logic (e.g. per-theory
    # union vs one terminal theory) must invalidate every cache, even though the
    # heap is byte-identical.
    try:
        ml = _ML.stat()
        parts += [str(ml.st_size), str(ml.st_mtime_ns)]
    except OSError:
        pass
    return hashlib.sha256("\0".join(parts).encode()).hexdigest()[:16]


def _cache_dir() -> Path:
    return Path(os.environ.get("QUERY_CACHE_DIR")
                or os.environ.get("XDG_CACHE_HOME") or Path.home() / ".cache",
                ).joinpath("query")


def _cache_path(session: str) -> Path:
    return _cache_dir() / f"namespace-{session}.json"


def load_cache(session: str) -> dict | None:
    try:
        return json.loads(_cache_path(session).read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None


def save_cache(session: str, payload: dict) -> None:
    d = _cache_dir()
    d.mkdir(parents=True, exist_ok=True)
    _cache_path(session).write_text(
        json.dumps(payload, indent=1, sort_keys=True), encoding="utf-8")


def _heaps_state(version_id: str) -> str:
    """A spawn-free digest of every heap under the heap search path: path,
    size and mtime.  One glob, as `_built_sessions` does.

    Whether a session's dump CAN succeed depends on more than its own heap: a
    child heap whose parent was rebuilt after it fails with "The parent for this
    saved state does not match", and one whose parent heap is missing fails
    with "Missing heap image".  Either clears when *some* heap changes, so a
    recorded failure is keyed on all of them."""
    stats = []
    for d in _heaps_dirs(version_id):
        for p in sorted(glob.glob(os.path.join(d, "*", "*"))):
            try:
                st = os.stat(p)
            except OSError:
                continue
            stats.append(f"{p}\0{st.st_size}\0{st.st_mtime_ns}")
    return hashlib.sha256("\n".join(stats).encode()).hexdigest()[:16]


def _failure_path(session: str) -> Path:
    return _cache_dir() / f"namespace-{session}.failed.json"


def _failed_before(session: str, key: str) -> bool:
    try:
        rec = json.loads(_failure_path(session).read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return False
    return rec.get("key") == key


def _record_failure(session: str, key: str, reason: str) -> None:
    try:
        d = _cache_dir()
        d.mkdir(parents=True, exist_ok=True)
        _failure_path(session).write_text(
            json.dumps({"key": key, "session": session, "reason": reason},
                       indent=1), encoding="utf-8")
    except OSError:
        pass   # recording is an optimisation; never fail a query over it


def _committed() -> tuple[frozenset, frozenset]:
    from isabelle_query._isabelle_namespace import ATTRIBUTES, PROOF_METHODS
    return PROOF_METHODS, ATTRIBUTES


def resolve_namespace(session: str = "HOL", *, allow_isabelle: bool = True,
                      dirs: list[str] | None = None) -> dict:
    """Resolve the router's method/attribute sets, preferring a fingerprint-valid
    cache, then a one-off Isabelle dump, then the committed static table.  Returns
    ``{methods, attributes (frozensets), source, fingerprint, theory}`` where
    ``source`` is ``cache`` | ``isabelle`` | ``committed``.

    ``dirs`` are the session's ROOT directories, forwarded to the dump: a
    distribution session (``HOL``) resolves by name, but a project/AFP session is
    unknown to ``ML_process -l`` unless its ROOT dir is on the search path — so
    without ``dirs`` the dump of such a session fails and this degrades to the
    committed table.  ``dirs`` does not enter the cache key: it only affects
    whether the *same* heap's table can be dumped, not the table itself."""
    fp = isabelle_fingerprint(session) if allow_isabelle else ""
    cached = load_cache(session)
    if fp and cached and cached.get("fingerprint") == fp:
        return {"methods": frozenset(cached["methods"]),
                "attributes": frozenset(cached["attributes"]),
                "source": "cache", "fingerprint": fp,
                "theory": cached.get("theory")}
    # Dump only when the heap already exists: `ML_process -l S` would *build* an
    # absent session, and the no-build guarantee is non-negotiable.  A missing
    # heap is skipped, never built.
    vid = _version_id(_isabelle_bin())
    have_heap = _heap_file(vid, session) is not None
    # A dump that failed against these exact heaps fails again [stale-heap-dump]:
    # recorded, so a stale heap costs one Isabelle spawn rather than one per
    # invocation (1.6 s each, measured on a development mid-rebuild).
    fail_key = f"{fp}:{_heaps_state(vid)}" if fp and have_heap else ""
    if fail_key and _failed_before(session, fail_key):
        have_heap = False
    if fp and allow_isabelle and have_heap:
        methods, attribs, theory, proc = dump(session, dirs=dirs)
        if not (methods or attribs) and proc is not None:
            # Not a timeout (proc is None there, and may be machine load): the
            # process ran and produced no table.
            out = (proc.stderr or proc.stdout or "").strip().splitlines()
            _record_failure(session, fail_key, out[-1] if out else "")
        if methods or attribs:
            payload = {"fingerprint": fp, "session": session, "theory": theory,
                       "methods": sorted(_base(methods)),
                       "attributes": sorted(_base(attribs))}
            save_cache(session, payload)
            return {"methods": frozenset(payload["methods"]),
                    "attributes": frozenset(payload["attributes"]),
                    "source": "isabelle", "fingerprint": fp, "theory": theory}
    methods, attribs = _committed()
    return {"methods": methods, "attributes": attribs,
            "source": "committed", "fingerprint": fp, "theory": None}


def resolve_augmented(session: str, *, base: str = "HOL",
                      allow_isabelle: bool = True) -> dict:
    """Two-tier namespace: the `base` table (universal core, cached) unioned with
    `session`'s *active* table — the namespace actually live under that session's
    imports, dumped from its prebuilt heap and cached per session.

    Intended for the deep, per-session measurements (``shape``) where recognising
    a session-local method/attribute is what keeps the method tally and the
    citation routing exact; structural queries are fine on `base` alone.  Because
    the table is the session's *real* namespace, unioning is monotone-safe: a name
    it adds genuinely is a method/attribute in that context (no false citation
    suppression).

    Falls back to `base` alone when Isabelle is absent, when `session` *is* the
    base, or when `session` has **no prebuilt heap** — the last upholds the
    no-build guarantee (skip, never build)."""
    base_r = resolve_namespace(base, allow_isabelle=allow_isabelle)
    skip = (not allow_isabelle or session == base
            or _heap_file(_version_id(_isabelle_bin()), session) is None)
    if skip:
        return {**base_r, "base": base, "augmented_with": None}
    sess_r = resolve_namespace(session, allow_isabelle=True)
    return {"methods": base_r["methods"] | sess_r["methods"],
            "attributes": base_r["attributes"] | sess_r["attributes"],
            "source": f"{base_r['source']}+{sess_r['source']}",
            "base": base, "augmented_with": session,
            "theory": sess_r.get("theory"),
            "fingerprint": sess_r.get("fingerprint")}


def resolve_project(sessions, *, allow_isabelle: bool = True,
                    dirs: list[str] | None = None) -> dict:
    """The exact namespace of a project *as built*: the union of the dumped tables
    of every session in `sessions` that has a **built heap**, over the committed
    (minimal, Pure) floor.

    Each session dump is *self-complete* — it includes the session's transitive
    dependencies — so **no logic base is injected**: a session that builds only on
    Pure keeps its own `auto`, a Nominal session carries `eqvt`, without either
    being forced to look like HOL.  The committed floor is the universal Pure core
    (every session imports Pure), so unioning it is always safe and never HOL-
    specific.

    A single ``<heaps>/*/*`` glob yields the built-session set; only sessions in
    both `sessions` and that set are dumped (each cached after first).  When **no**
    session heap is built — or Isabelle is absent — returns the committed (Pure)
    table as the honest fallback: ``source`` is ``committed`` and ``sessions`` is
    ``None`` (the caller warns if the project builds on non-Pure logic).  The
    no-build guarantee holds throughout: an unbuilt session is skipped, never
    built.  Otherwise ``source`` is ``isabelle:<s1>+<s2>`` and ``sessions`` lists
    the sessions folded in.

    ``dirs`` are the project's ROOT directories, forwarded to each session dump;
    without them a project/AFP session is unknown to ``ML_process -l`` and its
    dump fails, so the project degrades to the Pure fallback (the caller then
    warns).  Pass ``{SessionInfo.root_path.parent}`` from discovery."""
    committed_m, committed_a = _committed()
    fallback = {"methods": committed_m, "attributes": committed_a,
                "source": "committed", "sessions": None}
    if not allow_isabelle:
        return fallback
    built = _built_sessions(_version_id(_isabelle_bin()))
    methods = set(committed_m)
    attributes = set(committed_a)
    used: list[str] = []
    for s in sessions:
        if s in used or s not in built:
            continue
        sr = resolve_namespace(s, allow_isabelle=True, dirs=dirs)
        # Count a session as folded-in only when it was *actually dumped* (or
        # cache-hit), not when its resolve degraded to the committed floor: the
        # Pure floor is always non-empty, so gating on non-empty methods would
        # mis-report a failed dump as `isabelle:<session>` and suppress the
        # Pure-fallback warning.
        if sr["source"] in ("cache", "isabelle"):
            methods |= sr["methods"]
            attributes |= sr["attributes"]
            used.append(s)
    if not used:
        return fallback
    return {"methods": frozenset(methods), "attributes": frozenset(attributes),
            "source": "isabelle:" + "+".join(used), "sessions": used}
