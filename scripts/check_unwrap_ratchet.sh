#!/usr/bin/env bash
# scripts/check_unwrap_ratchet.sh
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Issue:  #385 / Part of #372, shim per #446.
#
# Monotonic-decrease ratchet for production-code panic-family sites.
#
# Compares the current per-file count of .unwrap(), .expect(, panic!,
# unreachable!, and todo! (outside `#[cfg(test)]` modules, outside
# `trust-cg-verify`, outside rustdoc code examples) against the baseline
# stored in `ratchet/unwrap_baseline.json`.
#
# Exit codes:
#   0 — every file is at or below its baseline (OK).
#   1 — at least one file exceeds its baseline (CI failure).
#   2 — tooling error (missing python3, baseline file, etc.).
#
# Note (#446): the canonical implementation has been ported to
# `trust-cg-test ratchet unwrap` (see crates/trust-cg-test/src/cmd/ratchet.rs).
# This shell wrapper is kept for CI compatibility during the transition
# and produces the same exit-code contract. New workflows should prefer
#   cargo run -p trust-cg-test --quiet -- ratchet unwrap
#
# Regenerate baseline after an approved reduction:
#   python3 scripts/generate_unwrap_audit.py --write

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${REPO_ROOT}"
exec cargo run -p trust-cg-test --quiet -- ratchet unwrap "$@"
