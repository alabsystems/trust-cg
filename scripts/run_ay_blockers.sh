#!/usr/bin/env bash
# scripts/run_ay_blockers.sh
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Narrow local rerun lane for the ay blocker route fixed by Trust Codegen #502.
# This is intentionally separate from the full test matrix: by default it pins
# the supported local ay release build for the two BV blocker cases and expects
# them to pass, then runs one FP-safe default-route control.
#
# Usage:
#   scripts/run_ay_blockers.sh
#   LOCAL_AY_BIN=/path/to/ay scripts/run_ay_blockers.sh
#   CARGO_BIN=/path/to/cargo scripts/run_ay_blockers.sh
#   ALLOW_LEGACY_AY_TARGET=1 \
#     LOCAL_AY_BIN=~/ay/target/user/release/ay \
#     LOCAL_AY_EXPECTATION=known-failure \
#     scripts/run_ay_blockers.sh
# Each case prints a one-line route summary before running its exact test.
# Legacy ~/ay/target/user/... builds are unsupported by default; the opt-in
# form above is only for deliberate stale-route reproduction.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

CARGO_BIN="${CARGO_BIN:-cargo}"
LOCAL_AY_BIN="${LOCAL_AY_BIN:-${HOME}/ay/target/release/ay}"
LOCAL_AY_EXPECTATION="${LOCAL_AY_EXPECTATION:-pass}"

ATOMIC_TEST="ay_bridge::tests::test_ay_batch_verify_atomic_proofs"
LOOP_TEST="ay_bridge::tests::test_ay_batch_verify_loop_optimization_proofs"
CONTROL_TEST="ay_bridge::tests::test_cli_verify_fp_roundtrip_prefers_fp_safe_solver"

overall_status=0

if [ $# -gt 0 ]; then
    case "$1" in
        -h|--help)
            sed -n '2,22p' "$0" | sed 's/^# \{0,1\}//'
            exit 0
            ;;
        *)
            echo "run_ay_blockers: unknown arg: $1" >&2
            exit 2
            ;;
    esac
fi

need_cmd() {
    if ! command -v "$1" >/dev/null 2>&1; then
        echo "run_ay_blockers: required command not found: $1" >&2
        exit 2
    fi
}

case "${LOCAL_AY_EXPECTATION}" in
    pass|known-failure)
        ;;
    *)
        echo "run_ay_blockers: LOCAL_AY_EXPECTATION must be 'pass' or 'known-failure'" >&2
        exit 2
        ;;
esac

case "${LOCAL_AY_BIN}" in
    */target/user/*)
        if [ "${ALLOW_LEGACY_AY_TARGET:-0}" != "1" ] || [ "${LOCAL_AY_EXPECTATION}" != "known-failure" ]; then
            echo "run_ay_blockers: legacy ay target route is unsupported by default: ${LOCAL_AY_BIN}" >&2
            echo "run_ay_blockers: use ~/ay/target/release/ay, or set ALLOW_LEGACY_AY_TARGET=1 and LOCAL_AY_EXPECTATION=known-failure to reproduce #502 stale-route failures" >&2
            exit 2
        fi
        ;;
esac

matches_expected_pattern() {
    local log_file="$1"
    local patterns="$2"
    local pattern

    while IFS= read -r pattern; do
        [ -z "${pattern}" ] && continue
        if rg -F -q "${pattern}" "${log_file}"; then
            return 0
        fi
    done <<EOF
${patterns}
EOF

    return 1
}

run_test() {
    local label="$1"
    local mode="$2"
    local test_name="$3"
    local expect_kind="$4"
    local expect_pattern="$5"

    local log_file
    local case_status=0
    local rc
    local route_summary
    log_file="$(mktemp -t trust_cg_ay_blockers.XXXXXX.log)"

    echo "==> ${label}"
    if [ "${mode}" = "forced-ay" ]; then
        route_summary="route=local-ay-explicit expectation=${expect_kind} solver=${LOCAL_AY_BIN}"
        echo "    ${route_summary}"
        echo "    AY_SOLVER_PATH=${LOCAL_AY_BIN} ${CARGO_BIN} test -p trust-cg-verify --lib ${test_name} -- --exact --nocapture"
        (
            cd "${REPO_ROOT}" &&
            CARGO_SKIP_CACHE=1 \
            CARGO_TERM_COLOR=never \
            AY_SOLVER_PATH="${LOCAL_AY_BIN}" \
            "${CARGO_BIN}" test -p trust-cg-verify --lib "${test_name}" -- --exact --nocapture
        ) >"${log_file}" 2>&1
        rc=$?
    else
        route_summary="route=auto-fp-prefer-z3 solver=$(command -v z3)"
        echo "    ${route_summary}"
        echo "    ${CARGO_BIN} test -p trust-cg-verify --lib ${test_name} -- --exact --nocapture"
        (
            cd "${REPO_ROOT}" &&
            CARGO_SKIP_CACHE=1 \
            CARGO_TERM_COLOR=never \
            env -u AY_SOLVER_PATH \
            "${CARGO_BIN}" test -p trust-cg-verify --lib "${test_name}" -- --exact --nocapture
        ) >"${log_file}" 2>&1
        rc=$?
    fi

    if [ "${expect_kind}" = "known-failure" ]; then
        if [ "${rc}" -ne 0 ] && matches_expected_pattern "${log_file}" "${expect_pattern}"; then
            echo "    EXPECTED blocker reproduced"
        elif [ "${rc}" -eq 0 ]; then
            echo "    UNEXPECTED pass: blocker no longer reproduces" >&2
            overall_status=1
            case_status=1
        else
            echo "    UNEXPECTED failure shape; expected pattern(s) not found" >&2
            overall_status=1
            case_status=1
        fi
    else
        if [ "${rc}" -eq 0 ]; then
            echo "    PASS"
        else
            echo "    UNEXPECTED control failure" >&2
            overall_status=1
            case_status=1
        fi
    fi

    if [ "${case_status}" -ne 0 ]; then
        echo "    ---- begin captured output ----" >&2
        sed -n '1,220p' "${log_file}" >&2
        echo "    ---- end captured output ----" >&2
    fi

    rm -f "${log_file}"
}

need_cmd "${CARGO_BIN}"
need_cmd rg
need_cmd z3

if [ ! -x "${LOCAL_AY_BIN}" ]; then
    echo "run_ay_blockers: local ay binary not found or not executable: ${LOCAL_AY_BIN}" >&2
    exit 2
fi

run_test \
    "atomic-bv blocker" \
    "forced-ay" \
    "${ATOMIC_TEST}" \
    "${LOCAL_AY_EXPECTATION}" \
    $'trail exhausted in conflict analysis\nstack overflow'

run_test \
    "simple-bv blocker" \
    "forced-ay" \
    "${LOOP_TEST}" \
    "${LOCAL_AY_EXPECTATION}" \
    $':reason-unknown incomplete\nstack overflow'

run_test \
    "fp roundtrip control" \
    "default-route" \
    "${CONTROL_TEST}" \
    "pass" \
    ""

if [ "${overall_status}" -eq 0 ]; then
    echo "run_ay_blockers: supported ay blocker lane matched expected results"
else
    echo "run_ay_blockers: blocker lane drift detected" >&2
fi

exit "${overall_status}"
