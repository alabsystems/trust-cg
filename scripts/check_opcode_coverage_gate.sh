#!/usr/bin/env bash
# scripts/check_opcode_coverage_gate.sh
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Part of: proof-gap-program P1.1 — emittable-opcode evidence inventory.
#
# Fail-closed inventory: every inventoried opcode is pinned as accepted,
# explicitly deferred RED debt, pseudo/trap, or a justified structural/
# never-selected exclusion. The test passes with the exact named deferred debt
# and fails on unknown classification or evidence drift. With default features,
# accepted records may be evaluator-backed statistical evidence; they are not
# correctness proofs. This wraps the coverage-gate test suite in trust-cg-verify so it runs
# in the same lane as the other ratchet-style gates (check_test_ratchet.sh,
# check_warnings_ratchet.sh, ...).
#
# The actual coverage logic lives in
#   crates/trust-cg-verify/src/coverage_gate.rs
#   crates/trust-cg-verify/tests/coverage_gate_tests.rs
# and is exhaustiveness-forced at COMPILE time (a new opcode variant will not
# compile until classified). This script makes the gate explicit in CI and
# prints the full audit log (allowlist included) so exceptions stay visible.
#
# Exit codes:
#   0 — accepted/deferred/excluded classifications match the pinned inventory.
#   1 — unknown classification/evidence drift or a test failure was found.
#   2 — tooling error.
#
# Usage:
#   scripts/check_opcode_coverage_gate.sh
#
# This inventory gate uses evaluator-backed coverage records by default. A
# green result is accepted evidence coverage, not proof. Run
# `scripts/check_proof_gate.sh` separately for strict external-SMT discharge.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

if ! command -v cargo >/dev/null 2>&1; then
    echo "check_opcode_coverage_gate: cargo not found on PATH" >&2
    exit 2
fi

FEATURES="${COVERAGE_GATE_FEATURES:-}"
FEATURE_ARGS=()
if [ -n "${FEATURES}" ]; then
    FEATURE_ARGS=(--features "${FEATURES}")
fi

echo "== opcode obligation/evidence inventory =="
echo "   crate:    trust-cg-verify"
echo "   test:     coverage_gate_tests (integration test)"
echo "   features: ${FEATURES:-<default: evaluator-backed statistical evidence; not proof>}"
echo

# --nocapture so the per-backend audit_log() (every opcode + allowlist reasons)
# is visible in CI output, keeping the gate honest.
cd "${REPO_ROOT}"
if cargo test -p trust-cg-verify ${FEATURE_ARGS[@]+"${FEATURE_ARGS[@]}"} --test coverage_gate_tests -- --nocapture; then
    echo
    echo "check_opcode_coverage_gate: PASS — accepted/deferred/excluded opcode classifications match the pinned inventory."
    exit 0
else
    echo
    echo "check_opcode_coverage_gate: FAIL — opcode classification or evidence drifted from the pinned inventory." >&2
    echo "  See the audit above. Known deferred RED rows are allowed only when exactly" >&2
    echo "  named and pinned; unknown RED, accepted-credit, denominator, or exclusion" >&2
    echo "  drift must be reviewed and updated deliberately." >&2
    exit 1
fi
