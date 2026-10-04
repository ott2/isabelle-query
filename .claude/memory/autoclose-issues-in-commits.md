---
name: autoclose-issues-in-commits
description: a commit that addresses a GitHub issue carries "Fixes #N" so the issue closes itself when it reaches main
metadata:
  type: feedback
---

When a commit addresses a GitHub issue, put `Fixes #N` (or `Closes #N`) in its
message so GitHub closes the issue automatically when the commit is pushed to
`main`. For an issue addressed across several commits, put it on the last one
(or the version-bump commit), not on each.

**Why:** the user wants issues closed by the change itself, not left open for a
manual close and comment afterwards. Issue #14 (multi-name `callers`) was fixed
across four commits in 0.9.4 with no `Fixes` line and stayed open.

**How to apply:** check whether the work came from an issue before writing the
commit message. Commit messages already record design decisions
([[small-frequent-commits]]), so where the fix departs from the request, say
why in the commit body; that is the record, and no separate issue comment is
needed. The release-notes bump commit can also carry it ([[release-versioning-policy]]).
