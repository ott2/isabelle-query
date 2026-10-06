---
name: old-code-diagnostics-without-worktrees
description: to run a probe or test against HEAD's code, extract it with git archive into a scratch dir; never git worktree add/remove
metadata:
  type: feedback
---

To check that a new test or probe fails on the old code, extract HEAD's
sources into a scratch directory inside the repo and point `PYTHONPATH` at it:

    git archive HEAD src | tar -x -C .stage    # (mkdir .stage first)
    PYTHONPATH=.stage/src pytest -q tests/test_x.py
    rm -rf .stage

(`git checkout-index -a --prefix=.stage/` also works.)  Do **not** use
`git worktree add` / `git worktree remove`.

**Why:** the user reports that worktree add/remove trips the permission
classifier. Rewriting local history (`git reset --soft` to redo commits) was
refused in the same session, so treat a committed message as final rather
than re-cutting commits to polish it.

**How to apply:** use this whenever you verify a regression test against
the pre-fix code. Scratch dirs go in the repo, not /tmp
([[scratch-files-in-repo-not-tmp]]). If a commit message needs correcting
after the fact, say so to the user instead of rewriting.
