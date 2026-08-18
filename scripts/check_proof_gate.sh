#!/usr/bin/env bash
# scripts/check_proof_gate.sh
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Issue:  P0 of the proof-gap program — make formal SMT discharge the gate.
#
# Runs the strict, fail-closed formal-proof gate. Unlike the default
# verification lane (which silently downgrades to statistical mock when no solver
# is present), this gate FAILS if:
#   (i)   no external AY solver is available,
#   (ii)  any obligation is disproved or errors, or
#   (iii) any obligation falls back to statistical evaluation.
#
# It sets the test-only `TRUST_CG_RUN_FORMAL_PROOF_TESTS=1` qualification so
# the solver-gated body actually executes, and discharges every obligation
# through the AY CLI subprocess (`verify_with_ay` -> `verify_with_cli`).
#
# ===========================================================================
# THE DEFAULT LANE IS THE FULL-DATABASE ZERO-COUNTEREXAMPLE FLOOR.
# ===========================================================================
# The DEFAULT lane runs `full_database_is_formally_verified`: every obligation in
# the ProofDatabase is discharged FORMALLY through AY. THE ENFORCED GUARANTEE
# is ZERO soundness failures — a counterexample (the solver DISPROVED an
# obligation) or an error hard-fails the gate; that is the only thing that can
# indicate a miscompile. Solver-capacity PENDING (timeouts/unknown) are REPORTED,
# never a pass. Only five audited wide x86 bit-vector obligations may remain
# pending (Sdiv I32/I64, Srem I32/I64, and V2I64 widening Umul); an entry may
# graduate to Verified, but any new pending name hard-fails the floor. The
# registry contains exactly 1,869 unique obligations, so the five-row capacity
# ceiling requires at least 1,864 formally Verified rows and 0 soundness
# failures. Several minutes; quick smoke via
# `--test representative_arithmetic_is_formally_verified`.
#
# v0.1.0 intentionally exposes only the external solver lane. It uses an `ay`
# binary on PATH (`z3_available()` retains its legacy compatibility name);
# there is no native-AY Cargo feature in this release.
#
# This script is meant to be added to scripts/run_full_test_matrix.sh as a
# dedicated external probe (see the integration_edits in the P0 manifest), in
# the same spirit as `--check-rustc-backend-env`.
#
# Exit codes:
#   0 — the selected gate completed with zero soundness failures and no
#       statistical fallback. Solver-capacity PENDING is reported, not proved.
#   1 — gate failure (no solver, a soundness failure, or an un-allowlisted PENDING).
#   2 — tooling error (cargo missing, build failure).
#
# Usage:
#   scripts/check_proof_gate.sh                 # DEFAULT = full ProofDatabase floor (CLI solver)
#   scripts/check_proof_gate.sh --test full_database_is_formally_verified  # explicit spelling of the default floor
#   scripts/check_proof_gate.sh --timeout-ms N  # per-obligation solver timeout
#   scripts/check_proof_gate.sh --test NAME     # run one gate test by name

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

PACKAGE="trust-cg-verify"
TEST_TARGET="proof_gate_strict"
# Default to the full-database floor: every ProofDatabase obligation is sent to
# AY, with zero soundness failures and no statistical fallback. Explicit
# solver-capacity pending results are reported. This takes several
# minutes; for a quick local check use the 6-obligation smoke:
#   scripts/check_proof_gate.sh --test representative_arithmetic_is_formally_verified
TEST_FILTER="${PROOF_GATE_FILTER:-full_database_is_formally_verified}"

usage() {
    sed -n '2,65p' "$0" | sed 's/^# \{0,1\}//'
}

while [ $# -gt 0 ]; do
    case "$1" in
        --timeout-ms)
            [ $# -ge 2 ] || { echo "check_proof_gate: --timeout-ms requires a value" >&2; exit 2; }
            export TRUST_CG_AY_TIMEOUT_MS="$2"; shift 2 ;;
        --timeout-ms=*)
            export TRUST_CG_AY_TIMEOUT_MS="${1#--timeout-ms=}"; shift ;;
        --test)
            [ $# -ge 2 ] || { echo "check_proof_gate: --test requires a value" >&2; exit 2; }
            TEST_FILTER="$2"; shift 2 ;;
        --test=*)
            TEST_FILTER="${1#--test=}"; shift ;;
        -h|--help)
            usage; exit 0 ;;
        *)
            echo "check_proof_gate: unknown argument: $1" >&2
            usage >&2
            exit 2 ;;
    esac
done

if ! command -v cargo >/dev/null 2>&1; then
    echo "check_proof_gate: cargo not found on PATH" >&2
    exit 2
fi

cd "${REPO_ROOT}"

# Some verifier proof tests recurse deeply in debug; match the matrix runner's
# stack override so the gate test does not overflow the libtest thread stack.
: "${RUST_MIN_STACK:=67108864}"
export RUST_MIN_STACK
export TRUST_CG_RUN_FORMAL_PROOF_TESTS=1

echo "[proof-gate] package=${PACKAGE} test=${TEST_TARGET}::${TEST_FILTER} features='${FEATURES:-<none, CLI lane>}'"
echo "[proof-gate] TRUST_CG_AY_TIMEOUT_MS=${TRUST_CG_AY_TIMEOUT_MS:-<default 30000>}"

# Single-threaded so per-obligation solver durations are not contended, and so
# the failure output (which obligation, which counterexample) is ordered.
#
# Capture the libtest output (while still streaming it) so we can assert below
# that the filter actually matched and RAN at least one test — see the
# zero-tests-ran guard. `tee` would mask cargo's exit, so use PIPESTATUS.
gate_out_log="$(mktemp -t trust_cg_proof_gate.XXXXXX)"
set +e
cargo test \
    -p "${PACKAGE}" \
    --test "${TEST_TARGET}" \
    "${TEST_FILTER}" \
    -- --test-threads=1 --nocapture 2>&1 | tee "${gate_out_log}"
status="${PIPESTATUS[0]}"
set -e

if [ "${status}" -ne 0 ]; then
    echo "proof gate FAILED: solver unavailable, soundness failure, or gate error." >&2
    echo "The gate refuses to downgrade to statistical mock verification." >&2
    echo "Inspect the test output above for the specific non-verified obligations." >&2
    rm -f "${gate_out_log}"
    exit 1
fi

# ZERO-TESTS-RAN GUARD (an empty gate is worse than none). `cargo test <filter>`
# exits 0 even when the filter matches NOTHING ("0 passed; N filtered out") — if
# the gate test is renamed, typo'd, or cfg-gated out, the gate would otherwise
# print "proof gate OK" while discharging ZERO obligations. Require that libtest
# reported >= 1 passed across all summaries.
gate_passed_total="$(
    grep -oE '[0-9]+ passed' "${gate_out_log}" | grep -oE '[0-9]+' | awk '{s+=$1} END{print s+0}'
)"
if ! grep -q 'test result:' "${gate_out_log}" || [ "${gate_passed_total:-0}" -eq 0 ]; then
    echo "proof gate FAILED: filter '${TEST_FILTER}' (target '${TEST_TARGET}') matched 0 tests that RAN" >&2
    echo "  (libtest reported ${gate_passed_total:-0} passed). The gate verified NOTHING — a renamed/" >&2
    echo "  typo'd/cfg-gated test name passes 'cargo test' with exit 0. Refusing to report OK." >&2
    rm -f "${gate_out_log}"
    exit 2
fi

# HONESTY: the success message must describe ONLY what was actually run. The
# default lane is the full-database floor; selecting the representative test
# explicitly runs only the six-obligation arithmetic smoke.
case "${TEST_FILTER}" in
    full_database_is_formally_verified)
        # libtest may leave its `test <name> ... ` progress prefix on the same
        # line as the test's first nocapture write.  Requiring column zero made
        # a genuinely successful full-database run fail in the wrapper after
        # the test had already reported `ok`.
        gate_summary="$(grep -F 'STRICT GATE OK:' "${gate_out_log}" | tail -1 || true)"
        if [ -z "${gate_summary}" ]; then
            echo "proof gate FAILED: full-database test emitted no verified/pending summary" >&2
            rm -f "${gate_out_log}"
            exit 2
        fi
        echo "proof gate OK: full-database zero-soundness/no-statistical-fallback floor passed."
        echo "${gate_summary}" ;;
    representative_arithmetic_is_formally_verified)
        echo "proof gate OK (SMOKE): 6 representative arithmetic obligations formally Verified" \
             "via AY with strict no-statistical-fallback assertions. This is NOT the full-database" \
             "formal floor — run '--test full_database_is_formally_verified' for that." ;;
    *)
        echo "proof gate OK: selected test '${TEST_FILTER}' passed via AY." \
             "(Scope = the selected test only; the full-database formal floor is" \
             "'--test full_database_is_formally_verified'.)" ;;
esac
rm -f "${gate_out_log}"
exit 0
