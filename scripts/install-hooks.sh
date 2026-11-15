#!/usr/bin/env bash
#
# install-hooks.sh — activate the tracked git hooks (the permanence layer).
#
# Points git at the in-repo `hooks/` directory so the pre-push soundness gate
# is enforced. Run once per clone. Idempotent. Purely LOCAL — NO GitHub CI.
#
#   scripts/install-hooks.sh
#
# After this, a push that updates `main` must carry a verified per-commit
# soundness attestation (refs/attest/soundness/<C>/*); the hook runs
# scripts/soundness_check.sh --attest when none verifies and BLOCKS on any red
# leg. See hooks/pre-push for the transitional owner exception.
#
set -eu

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

if [ ! -d hooks ]; then
  echo "install-hooks: no tracked hooks/ dir in $repo_root — nothing to install." >&2
  exit 1
fi

chmod +x hooks/* 2>/dev/null || true
git config core.hooksPath hooks

echo "install-hooks: core.hooksPath = $(git config core.hooksPath)"
echo "install-hooks: pre-push soundness attestation gate is now ACTIVE for 'main' pushes."
