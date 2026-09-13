# Contributing to isabelle-query

Normative rules for changing the tool. Orientation (what `query` is, how the
package is laid out) is in `CLAUDE.md`. User-facing docs are `README.md` (the
CLI surface), `SCANNING.md` (what counts as a declaration, a citation and a
session) and `METRICS.md` (the `query shape` reference).

## Where design decisions are recorded

**In commit messages.** They carry the reasoning, the rejected alternatives and
the before/after, and they are the only record that cannot drift from the code.
Cross-reference a body of work with a stable `[tag]` handle, and recover it with

    git log --grep='\[grep-owner-span\]'

`todo.md` holds only *open* work — things not yet done. It is not a changelog.
If you want to know why something is the way it is, read the commits.

**Cite only what a reader of this repo can open.** Comments, docstrings and
config headers must not reference paths outside it — a pointer the reader cannot
resolve is worse than no pointer, and the design material it names may be
unpublished. For the proof-shape metrics the public authority is
`src/isabelle_query/shape.py` itself (definitions at each metric) plus the
`M1`–`M6` table in `METRICS.md`. Check with:

    grep -rn 'docs/' --include='*.py' --include='*.toml' src tests scripts configs

## CLI contract (follow when adding or changing commands)

Two families, each matching an external convention; a command's primary
positional decides which one it is.

- **lookup** (git/brew: `git show REF...`, `brew deps FORMULA`) — the
  primary positional is a **subject** (entry/theory name), one-or-more,
  reported in turn. Add it with `_add_subject_list_arg`. **No trailing
  PATH positionals**: "who calls X" is corpus-global, so scope with the
  global `-R/--root` and narrow with *semantic* flags (`--external`,
  `-r/--recursive`), never a file subset. Members: `show`, `callers`,
  `callees`, `deps`, `uses`, `theory`, `defs`, `outline`, `methods`,
  `instances`, `codeqs`.
- **search** (grep/rg: `grep PAT PATH...`) — the primary positional is a
  pattern (or nothing), and **paths are the trailing positionals**, added
  with `_add_path_files_arg` (resolved by `_load_sections`). Members:
  `grep`, `largest`, `sorry` (and `find` once it gains PATH/`--theory`
  scope under `[theory-refs]`).

**Never return an empty success for a question you could not ask.** A silent
zero is indistinguishable from an honest zero, so a caller cannot tell a broken
run from a real one — `query -R /typo shape census` once printed nothing and
exited 0, and a shell path-expansion bug turned that into a run of plausible
zero-record censuses. A root that cannot be read reports on stderr and exits
`2`, a code deliberately distinct from `1`.

The same rule one level down: **an unresolvable SUBJECT goes through
`commands._fail_subject`** — stderr, stdout untouched, exit `1`. Distinguish
the two empties before choosing, because they look identical at the call site:

| | example | answer |
|---|---|---|
| the search found nothing | `find zzz -c`, `callers zzz -c` | `0` on stdout, exit `0` |
| the subject does not exist | `callees zzz`, `refs zzz`, `theory zzz` | stderr, exit `1` |

`callers` is in the first row and that is not an inconsistency: it SCANS source
for a token, so zero mentions is truthful whether or not the name is declared,
while `callees` needs the entry to exist before it can have callees. Different
questions, different empties. `scripts/probe_count_modes.py` checks the whole
family at once — add a verb there when you add one here.

**The two site verbs sit in the lookup family, and their exit contract is the
reason they were allowed to exist.** `instances` and `codeqs` take a subject
list and no PATH positionals. Neither has a prover-side oracle to compare
against, so they carry the discipline an oracle would otherwise have supplied:

- A subject that is **not a locale/class** (resp. **not a constant**) declared
  in the project exits `1` with a diagnostic on stderr — never `0` with zero
  sites. "No instantiations of `foo`" and "`foo` is not a locale" are different
  answers and a script must be able to tell them apart. This is the same
  never-empty-success rule one level in.
- A subject that IS declared and has no sites exits `0`. That is an honest
  zero.
- Their scope is stated in `README.md`, not buried: declared source sites only,
  the complement of `print_interps` / `print_codesetup`; and `codeqs`
  under-reports where mixfix notation hides the head symbol. A verb that leans
  the unsafe way says so where the user reads about it.

A third verb of this kind would need the same three things before it ships.

**A user-typed pattern goes through `commands._user_pattern`, never straight to
`re.compile`.** This is the same rule one level down: a pattern that cannot
match is a silent zero the caller has no reason to doubt. Two rewrites live
there — shell-grep `\|` to `|`, and Isabelle markup (`\<^sub>`) escaped so the
`^` is not read as a start-of-string anchor. The second is what makes `query
find 'split\<^sub>i'` work, and it is a case of the tool accepting its own
output as input: `show` and `callers` already took that name, `find` did not.
Add a third rewrite here rather than at a call site, and route new
pattern-taking verbs through `_compile_user_pattern`, which also reports a bad
regex on stderr and exits `2` instead of raising.

**A configurable global that moves a measurement gets ONE default, and the
library caller gets the same one as the CLI.** Third instance of the silent-zero
family, and the worst-behaved: `graph`'s method table is late-bound, the CLI
bound it at dispatch, and `import isabelle_query` left the minimal Pure floor —
so `shape.analyze_proof` called directly returned numbers no `query` run would
ever print. It failed *selectively* (`simp` and `rule` are in the floor; `auto`,
`blast`, `metis` are not), which is why it read as data: a spot-checked `by simp`
proof agreed with the census exactly while 62.3% of proofs' `trivial_frac`
silently became `None` — "discharges nothing" for proofs that discharge
everything. The default is now the broad committed union both paths use
(`graph.use_census_namespace`), and stepping *down* is an explicit call
(`graph.use_pure_namespace`), never an inherited default. When a global like this
has to differ by context, make each context bind what it wants — a branch that
relies on "the default is already right" stops being right the moment the default
moves, and nothing fails when it does.

Shared-feature help text comes from one helper each, so wording can't
drift command-to-command — always add a feature through its helper, never
inline:

| helper | feature |
|---|---|
| `_add_subject_list_arg` | subject list |
| `_add_path_files_arg` | trailing `PATH` |
| `_add_names_flag` | `--names` (**no `-n`** — reserved for grep's line-number meaning) |
| `_add_count_flag` | `-c/--count` |
| `_add_with_comments_flag` | `--with-comments` — the *only* prose-search toggle on `find`/`grep` (**no `-a`**, which is `_add_mode_flags`' show-all) |
| `_add_mode_flags` | the `-a` / `--names` / `-c` bundle |
| `_add_verbatim_flag` | `-V/--verbatim` |
| `_add_comment_flags` | `--comments-off` / `--comments-only` |
| `_add_context_flag` | `-U/--context` — one short flag everywhere, default per-command |
| `_add_drop_names_flag` | `--drop-names-upto` |
| `_add_line_number_noop_flag` | `-n/--line-number` — accepted and ignored on the search verbs |
| `_add_sorts_flag` | `--sorts` — the site verbs' written sort / arity / signature column |

The **program name is not a literal**. The tool installs under two console
script names (`query`, `isabelle-query`) and reports whichever was invoked, via
`_prog.prog_name()` (re-exported as `cli._prog_name`). Anything a user reads —
the `prog=`, `--version`, a stderr diagnostic prefix, an example embedded in
help prose — goes through that accessor. A hardcoded `"query"` is guaranteed
wrong for one of the two callers, and wrong in the direction that names a
command the reader may not have on PATH. Internal comments and docstrings are
exempt: nobody retypes those. `tests/test_cli_prog_name.py` greps `src/` for the
literal, because the failure mode is a *new* message, not an old one.

`_prog` is a leaf module — it imports nothing from the package — precisely so
that `shape_cmds`, which sits below `cli`, can use it without closing a cycle.

**A printed `theory:line` goes through `render.locus_labels`, and a printed
`file:line` through `render.file_locus`.** Emitting `sec.theory` is the obvious
thing and it is ambiguous over a corpus: 461 AFP theory names name more than
one theory, so the locus a verb hands you may not paste back to the theory it
came from. Scope the label to the whole loaded corpus, never to the rows being
shown — `cmd_largest` passes `sections`, not `rows[:top]`, for that reason.

The corollary is the sharper half, and it is not about labels: **a theory NAME
is never a section's identity — key by `sec.path` and pass the section
itself.** A name is unique in a session and not in a corpus, so any
`{sec.theory: ...}` map written by one loop over the sections and read back by
another silently hands 758 of the AFP's 9,910 sections another file's data.
Four instances, all now keyed by path: `_build_line_index` (line → owning
entry), `_noise_ranges` (prose vs live), `_build_def_sites` (declaration
sites), and `cmd_callers` re-deriving its hit's section through
`graph._sections_by_theory`.

The two suppressing indexes are the worst, because a dropped citation leaves
nothing to notice: over the AFP the collapse gave 381,710 lines a different
owner, classified 38,068 the wrong side of prose-vs-live, and moved 48,177
citation edges onto the wrong entry while hiding 43,912 real ones (`unused`
95,696 → 104,028). Measured by `scripts/probe_name_keyed_index.py`, which
reconstructs the name-keyed map itself and so reads the same on either side of
the fix.

The fifth instance, `graph._Visibility`'s import closure, is a genuine graph
node rather than a per-section lookup, so it took a different answer: not a
better tiebreak among same-named candidates but the **union** of their edges.
That follows from what the filter is. A visibility closure is a *necessary*
condition and may only DROP, so a closure that is too large is merely weak
while one that is too small deletes real citations — and between two
approximations, the permissive one is the only safe one. The same reasoning
decides how an `imports` token is matched: **by its last path segment**, which
is Isabelle's own rule (`Thy_Header.import_name`), because a token the resolver
cannot map is not a missing feature but a hole, and a hole prunes
[import-leaf].

## Library contract (`isabelle_query.api`)

**Four names are supported: `parse_theory`, `parse_root`, `Entry`,
`TheorySection`.** They carry the same promise as the CLI — a change that
breaks them takes the **minor** version slot, never a patch. Everything else in
the package is internal and may move in any release.

Adding a fifth is a decision, not a convenience. `tests/test_api_surface.py`
pins `__all__` **exactly**, not "at least", because a name that leaks into it
is a name someone will import, and then it is promised whether or not that was
meant. The same file pins the *span fields* of `Entry` and `TheorySection`,
which is where the real contract lives: a consumer depends on `e.preamble` and
`e.body_end_line` meaning what they say, not on which private function computed
them — and that is precisely what leaves `parsing` free to keep changing.

Prefer exporting a **composition** over its ingredients. Issue #10 asked for
ten line-scanners plus `_attach_preambles` and `_proof_extent`; their results
were already fields on the two objects, and the hard-won part is the order the
scanners run in (tokenizer first, preambles before `compute_spans`,
`_proof_extent` last). Pinning the pieces would have frozen the most volatile
module in the package while promising nothing extra.

`api` imports only from `model` and `parsing`, and `__init__.py` re-exports
nothing — `import isabelle_query` must stay free of the parser, which `_prog`
and the version lookup do not want. Both are enforced by that test file.

A library entry point that reads a module global gets it **saved and restored**,
or the answer depends on call order — `parse_theory` after a `parse_root` was
returning the previous root's custom commands. Same family as the namespace
default above: a caller must get the same result from the same arguments.

## Verification

The suite is not sufficient on its own for parser changes; unit tests cannot
see a scanner failing at scale. Two habits catch what they miss:

- **Diff the entry set** after any parser change — `scripts/dump_entries.py`
  (add `--spans` when extents may move; a change can leave entries identical
  while moving a thousand declaration ends).
- **Diff the discovered theory set** after any change to session or `imports`
  parsing — and diff it **as a set, not a count**. `dump_entries.py` walks
  `ent.rglob("*.thy")`, so it never calls `parse_thy_imports` and cannot see a
  discovery regression: when `[thy-header]` silently dropped 72 theories it
  reported an identical 55,838 entries. Compare
  `{p for s in iter_sessions(root) for _, p in session_theories(s)}` against
  the same set from `git archive <ref> | tar -x -C .scratch-head`. A count
  alone hides a simultaneous gain and loss, which is exactly what happened.
- **Check a new test can fail.** Patch the behaviour it pins, run it, restore.
  Several tests have been written that could not fail. Two traps in the loop
  itself, both of which have produced a wrong verdict here:
  - **Run the mutation with `PYTHONDONTWRITEBYTECODE=1`.** A mutation harness
    rewrites the source several times a second, and CPython invalidates a
    `.pyc` on `(mtime, size)` — so a same-second rewrite can leave the previous
    bytecode in place and the subprocess runs code that is not on disk. That
    reports a *live* mutation as SURVIVED. `CAUGHT` is always trustworthy;
    `SURVIVED` is not, until the cache is off.
  - **A survivor may be masked, not dead.** A unit test can be shadowed by a
    downstream guard that ends the scan anyway. Before concluding a branch is
    unreachable, diff the entry set with the mutation applied: two branches
    that survived every unit test moved 706 and 330 entries.
  When a branch really is unreachable from valid input, say so in the comment
  and pin it at the helper/regex level, rather than leaving it looking tested.

`pytest -q` stays green after every change.
