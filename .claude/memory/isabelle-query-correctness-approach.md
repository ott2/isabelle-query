---
name: isabelle-query-correctness-approach
description: How to validate parser/analysis changes on the isabelle-query tool
metadata: 
  node_type: memory
  type: feedback
  originSessionId: ef4b3238-179f-4694-a1b1-cea8fbcab1b1
---

When changing isabelle-query's parser or analysis code, **do not treat bit-parity with the old behaviour as the correctness bar** — the old code has its own bugs. Examples found in practice: `_parse_name` silently truncated symbolic names (`finally\<^sub>n` → `finally`); the naive call-graph oracle over-matches short symbolic names nested in longer identifiers; a quoted spelling was captured as a name even when it was an anonymous lemma's statement. Verify against the actual Isabelle semantics, not against what the previous version did.

**Why:** the user explicitly said "the old code isn't necessarily correct of course," and several of this session's real bugs were cases where the new code was *more* correct than the code it replaced.

**How to apply:**
- Pin fast/optimised builders to a brute-force reference *oracle* in tests (see `tests/support.brute_force_call_graph`), but treat oracle disagreements as candidates for *either* side being wrong.
- **The oracle shares the exclusion helpers** (`brute_force_call_graph` calls `cli._noise_ranges` / `_build_def_sites` / `_is_citation_name`). So for the *exclusion set itself* it is a **consistency check between two implementations, not ground truth** — both inherit the same membership. Changing what counts as live source (text / `\<comment>` / preamble / def-site) will keep passing oracle-parity while silently changing real output; it needs a dedicated fixture, not just green oracle tests. (This is how the call graph's missing `\<comment>` skip hid for so long; fixed 2026-06 so comments are no longer call edges — re-measure `unused`/`callers` on the corpus after such a change.)
- Record corner cases where parsing fails as `@unittest.expectedFailure` tests in `tests/test_known_failures.py` — they stay green now but flip to "unexpected success" when fixed, forming a turn-on-able roadmap toward full AFP coverage. The intricate analysis to find them is valuable; don't discard it.
- Measure on the real AFP tree (`env ISABELLE_QUERY_CORPUS=$HOME/repos/afp/thys pytest -q tests/test_corpus.py`) — corner cases only show at scale.  Spell it `$HOME`: the shell is tcsh, which does not expand `~` after `=`, and the corpus tests then all SKIP with exit 0.

See [[user-andras-salamon]].
