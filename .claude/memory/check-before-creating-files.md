---
name: check-before-creating-files
description: "Before Write-ing a \"new\" file in scripts/ or tests/, check the name is free; tracked files have been overwritten twice"
metadata:
  node_type: memory
  type: feedback
  originSessionId: 1f30afe9-8431-4640-9b0d-5ba3b79cc9f2
  modified: 2026-10-23T00:00:43.367Z
---

Before creating a file with Write in `scripts/` or `tests/` (including
`tests/fixtures/`), check that the path does not already exist (`ls` it). A
Write result saying "updated" rather than "created" means something was
overwritten: stop and `git checkout --` it.

**Why:** in the 1.1.0 cycle this clobbered `tests/fixtures/Owners.thy` (about
20 failures) and later the tracked `scripts/probe_entry_spans.py`. Probe names
are natural to reuse, and earlier sessions already wrote many.

**How to apply:** pick the name, `ls` it, then write. See also
[[prefer-scripts-over-inline-python]] and
[[old-code-diagnostics-without-worktrees]].
