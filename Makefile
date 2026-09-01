# Makefile for isabelle-query.
#
# Development: create and activate a venv, then `make dev` installs the
# package (editable) plus the PEP 735 `test` dependency group, and
# `make test` runs the suite.
#
# Release: pyproject.toml's [project].version is the single source of truth for the
# release version. `make release` reads it, builds the sdist + wheel into
# dist/, creates an annotated git tag v<version> on the current commit, then
# pushes the current branch and that tag to the remote. GitHub renders a pushed
# tag as a Release whose body is the tagged commit's message (see
# .github/workflows/release.yml), so write the changelog in the version-bump
# commit:
#   https://github.com/ott2/isabelle-query/releases/tag/v<version>
#
# The PyPI upload is deliberately NOT automated — it is the one step that
# cannot be undone, and it is the maintainer's. `release` prints the exact
# command as its last line.

REMOTE ?= origin

# Read [project].version from pyproject.toml. The release step assumes Python
# 3.11+ for tomllib; the packaged library still supports 3.9+ independently.
VERSION := $(shell python3 -c "import tomllib; print(tomllib.load(open('pyproject.toml','rb'))['project']['version'])")
TAG     := v$(VERSION)
# Distribution filenames for THIS version.  `python -m build` does not clean
# dist/, so old releases accumulate there — naming the version explicitly is
# what stops `twine upload` re-offering an already-published one.
DIST    := dist/isabelle_query-$(VERSION)
# The `~/.pypirc` repository entry to upload to.
PYPI_REPO ?= pypi-isabelle-query

.DEFAULT_GOAL := version
.PHONY: version release dev test dist

# Install the package (editable) plus the PEP 735 `test` dependency group
# into the active environment.  Create and activate a venv first; then a
# single `make dev` gives a working, test-ready checkout.
dev:
	python3 -m pip install -e .
	python3 -m pip install --group test

# Run the test suite.  Assumes `make dev` (or an equivalent install) has put
# pytest in the environment.
test:
	python3 -m pytest

# Print the tag that `make release` would create.
version:
	@echo $(TAG)

# Build the sdist + wheel into dist/.  Plain `python -m build`, no --outdir:
# dist/ is the default, it is what twine expects, and it is gitignored.
dist:
	python3 -m build
	@ls -1 $(DIST)* 2>/dev/null || { \
		echo "error: no artifacts matching $(DIST)*"; exit 1; }

# Tag the current commit as v<version> (annotated), then push the current
# branch and the tag to $(REMOTE).
release:
	@test -n "$(VERSION)" || { echo "error: could not read version from pyproject.toml"; exit 1; }
	@git update-index -q --refresh
	@git diff-index --quiet HEAD -- || { echo "error: uncommitted changes in working tree; commit or stash before releasing"; exit 1; }
	@if git rev-parse -q --verify "refs/tags/$(TAG)" >/dev/null; then \
		echo "error: tag $(TAG) already exists locally"; exit 1; \
	fi
	@if git ls-remote --exit-code --tags $(REMOTE) "refs/tags/$(TAG)" >/dev/null 2>&1; then \
		echo "error: tag $(TAG) already exists on $(REMOTE)"; exit 1; \
	fi
	@echo "Tagging $$(git rev-parse --short HEAD) as $(TAG); pushing branch + tag to $(REMOTE)..."
	@# Release notes come from the *tagged (HEAD) commit's message*: CI
	@# (.github/workflows/release.yml) reads it and publishes it as the GitHub
	@# Release body.  Write the changelog in the version-bump commit, e.g.
	@#   git commit -m "$(VERSION) - changes from <prev>" -m "## Added" -m "- ..."
	@# The tag message itself is just a label.
	@if [ "$$(git log -1 --format=%B HEAD | sed '/^$$/d' | wc -l | tr -d ' ')" -le 1 ]; then \
		echo "warning: HEAD's commit message is a single line, so the Release"; \
		echo "         notes will be just that line.  Amend it with the changelog"; \
		echo "         for fuller notes.  Continuing in 3s (Ctrl-C to abort)..."; \
		sleep 3; \
	fi
	@# Build BEFORE tagging: a broken build then costs nothing, where a tag
	@# that is already pushed cannot be taken back.
	@$(MAKE) --no-print-directory dist
	git tag -a "$(TAG)" -m "isabelle-query $(VERSION)"
	git push $(REMOTE) HEAD "$(TAG)"
	@echo
	@echo "Released $(TAG); CI will publish HEAD's commit message at https://github.com/ott2/isabelle-query/releases/tag/$(TAG)"
	@echo
	@echo "Remaining step, yours — upload to PyPI:"
	@echo
	@echo "    twine upload -r $(PYPI_REPO) $(DIST)*"
	@echo
	@echo "(version-scoped on purpose: dist/ keeps every past build, and a bare"
	@echo " 'dist/*' would re-offer an already-published release.)"
