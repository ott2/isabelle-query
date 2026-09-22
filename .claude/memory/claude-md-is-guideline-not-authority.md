---
name: claude-md-is-guideline-not-authority
description: CLAUDE.md and project docs are guidelines; actual facts outrank them when the two disagree
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 3cfc621c-eaf3-4997-8abd-1b1c0a34743d
  modified: 2026-09-22T14:25:47.711Z
---

`CLAUDE.md` (and the other in-repo docs) are guidelines, **not** a higher
authority than the facts of a situation. When a documented rule and the
evidence disagree, the evidence wins and the doc is what gets updated.

Raised on 2026-09-22 reviewing PR #11 on isabelle-query: I described
`CLAUDE.md`'s credit rule ("By András Salamon, with Claude Opus 4.6, 4.7, 4.8,
and 5") as *pinning* the artifact credit line, when the real question was who
had actually done the work — an outside contributor (David Wang) with Claude
Fable 5.1. András: "We should credit the correct author(s), CLAUDE.md is a
guideline not more authoritative than the actual facts."

**Why:** these docs are written ahead of the cases they end up governing, so
treating one as binding converts a stale line into a wrong answer — and for
credit specifically, into misattributing a real person's work.

**How to apply:** quote a project doc as the *default*, not as the decision.
When something in it is contradicted by what is actually true — authorship,
a measured number, a file that no longer exists — say so plainly, follow the
facts, and offer to amend the doc. Do not resolve a conflict by deferring to
the written rule. Related: [[isabelle-query-correctness-approach]] (verify
against Isabelle semantics, not prior behaviour) — the same instinct one layer
up.
