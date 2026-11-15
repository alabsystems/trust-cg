#!/usr/bin/env bash
# scripts/check_proof_gate.sh
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Issue:  P0 of the proof-gap program — make formal SMT discharge the gate.
#
# Runs the strict, fail-closed formal-proof gate. Unlike the default
# verification lane (which silently downgrades to statistical mock when no solver
# is present), this gate FAILS if:
#   (i)   AY or its independent Clean proof checker is unavailable,
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
# obligation) or an error hard-fails the gate. Passing covers only the represented
# obligations, not every possible compiler defect. Timeouts/unknown are REPORTED,
# never a pass. Only five audited wide x86 bit-vector obligations may remain
# pending (Sdiv I32/I64, Srem I32/I64, and V2I64 widening Umul); an entry may
# graduate to Verified, but any new pending name hard-fails the floor. The
# registry cardinality and derived verified floor are asserted by
# EXPECTED_STATIC_PROOF_OBLIGATION_COUNT in
# crates/trust-cg-verify/tests/proof_gate_strict.rs; do not duplicate that moving
# count here. Several minutes; quick smoke via
# `--test representative_arithmetic_is_formally_verified`.
#
# trust-cg uses the identity-checked AY shipped in the sysroot of the Trust
# compiler that built it (crates/trust-cg-verify/src/ay_identity.rs) and
# independent Clean checking from aterm's managed package store. No sibling
# source checkout or Z3 fallback is required.
# There is no native-AY Cargo feature in this release.
#
# This script is meant to be added to scripts/run_full_test_matrix.sh as a
# dedicated external probe (see the integration_edits in the P0 manifest), in
# the same spirit as `--check-rustc-backend-env`.
#
# Exit codes:
#   0 — the selected gate completed with zero soundness failures and no
#       statistical fallback. Solver-capacity PENDING is reported, not proved.
#   1 — gate failure (no solver, a soundness failure, or an un-allowlisted PENDING).
#   2 — tooling error (targo missing, build failure).
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

# The installed Trust package's targo, through the wrapper that keeps the
# TRUST_CG_* controls below out of trustc's environment (it refuses to run
# under one) and hands them to the test. A Trust build of trust-cg-verify is
# also what records the toolchain AY its solver lanes admit.
TRUST_CARGO="${SCRIPT_DIR}/trust_cargo.sh"
if [ ! -x "${TRUST_CARGO}" ]; then
    echo "check_proof_gate: missing executable ${TRUST_CARGO}" >&2
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
# zero-tests-ran guard. `tee` would mask targo's exit, so use PIPESTATUS.
gate_out_log="$(mktemp -t trust_cg_proof_gate.XXXXXX)"
set +e
"${TRUST_CARGO}" test --locked \
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

# ZERO-TESTS-RAN GUARD (an empty gate is worse than none). `targo test <filter>`
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
    echo "  typo'd/cfg-gated test name passes 'targo test' with exit 0. Refusing to report OK." >&2
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
