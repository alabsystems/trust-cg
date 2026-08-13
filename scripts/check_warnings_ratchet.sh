#!/usr/bin/env bash
# scripts/check_warnings_ratchet.sh
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Zero-warnings ratchet for the workspace.
#
# Runs `cargo build --workspace` and `cargo build --workspace --tests`,
# counts compiler warnings in the output, and compares the total against
# the baseline stored in `ratchet/warnings_baseline.json` (default: 0).
#
# This complements the `[workspace.lints.rust] warnings = "deny"` policy in
# the root `Cargo.toml` — that policy stops warnings at compile time during
# local dev, and this script provides an auditable CI-style check that
# reports the explicit delta against the baseline.
#
# Exit codes:
#   0 — warning count is at or below the baseline (OK).
#   1 — warning count exceeds the baseline (CI failure).
#   2 — tooling error (missing python3, baseline file, cargo, etc.).
#
# Usage:
#   scripts/check_warnings_ratchet.sh
#
# To raise the baseline after an intentional, approved regression, edit
# `ratchet/warnings_baseline.json` in the same commit that introduces the
# new warnings, and justify the change in the commit body.
#
# Note (#446): the canonical implementation has been ported to
# `trust-cg-test ratchet warnings` (see crates/trust-cg-test/src/cmd/ratchet.rs).
# This shell wrapper is kept for CI compatibility during the transition
# and produces the same exit-code contract. New workflows should prefer
#   cargo run -p trust-cg-test --quiet -- ratchet warnings

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
BASELINE="${REPO_ROOT}/ratchet/warnings_baseline.json"

if ! command -v python3 >/dev/null 2>&1; then
    echo "check_warnings_ratchet: python3 not found on PATH" >&2
    exit 2
fi

if ! command -v cargo >/dev/null 2>&1; then
    echo "check_warnings_ratchet: cargo not found on PATH" >&2
    exit 2
fi

if [ ! -f "${BASELINE}" ]; then
    echo "check_warnings_ratchet: baseline file missing: ${BASELINE}" >&2
    exit 2
fi

BASELINE_COUNT="$(python3 -c "import json,sys; print(json.load(open('${BASELINE}'))['warnings'])")"

# Temp files for build output.
TMP_PROD="$(mktemp -t warnings_prod.XXXXXX.txt)"
TMP_TESTS="$(mktemp -t warnings_tests.XXXXXX.txt)"
trap 'rm -f "${TMP_PROD}" "${TMP_TESTS}"' EXIT

cd "${REPO_ROOT}"

# Build production and tests, capturing stderr+stdout. Record the statuses
# instead of discarding them: deny(warnings) can make a warning build fail, but
# a zero-warning compile error must never be reported as a successful ratchet.
set +e
cargo build --workspace --message-format=human --color=never \
    >"${TMP_PROD}" 2>&1
PROD_STATUS=$?
cargo build --workspace --tests --message-format=human --color=never \
    >"${TMP_TESTS}" 2>&1
TESTS_STATUS=$?
set -e

# Count distinct warning diagnostics. rustc emits one "warning: <msg>" line
# per diagnostic and a summary line "warning: `<crate>` generated N warnings"
# — we want the former (source diagnostics), not the latter.
count_warnings() {
    local file="$1"
    # Exclude summary lines and spurious cargo network warnings.
    # `set -o pipefail` + `grep` returning 1 on no-match would fail this
    # function, so use `|| true` at each stage to keep it robust when the
    # build is clean.
    local count
    count="$({ grep -E '^warning: ' "${file}" || true; } \
        | { grep -vE '^warning: `[^`]+` \(.*\) generated [0-9]+ warnings?' || true; } \
        | { grep -vE '^warning: (spurious network error|unused manifest key|build failed, waiting for other jobs to finish\.\.\.)' || true; } \
        | wc -l \
        | tr -d ' ')"
    echo "${count}"
}

PROD_COUNT="$(count_warnings "${TMP_PROD}")"
TESTS_COUNT="$(count_warnings "${TMP_TESTS}")"
TOTAL=$(( PROD_COUNT + TESTS_COUNT ))

echo "warnings ratchet: baseline=${BASELINE_COUNT}"
echo "  cargo build --workspace:          ${PROD_COUNT} warnings"
echo "  cargo build --workspace --tests:  ${TESTS_COUNT} warnings"
echo "  total:                             ${TOTAL}"

if [ "${TOTAL}" -gt "${BASELINE_COUNT}" ]; then
    echo ""
    echo "warnings ratchet FAILED: total ${TOTAL} > baseline ${BASELINE_COUNT}."
    echo ""
    echo "Production warnings:"
    grep -E '^warning: ' "${TMP_PROD}" \
        | grep -vE '^warning: `[^`]+` \(.*\) generated [0-9]+ warnings?' \
        | grep -vE '^warning: (spurious network error|unused manifest key|build failed, waiting for other jobs to finish\.\.\.)' \
        || true
    echo ""
    echo "Test warnings:"
    grep -E '^warning: ' "${TMP_TESTS}" \
        | grep -vE '^warning: `[^`]+` \(.*\) generated [0-9]+ warnings?' \
        | grep -vE '^warning: (spurious network error|unused manifest key|build failed, waiting for other jobs to finish\.\.\.)' \
        || true
    echo ""
    echo "Fix the warnings, or update ${BASELINE} and justify in commit body."
    exit 1
fi

if [ "${PROD_STATUS}" -ne 0 ] || [ "${TESTS_STATUS}" -ne 0 ]; then
    echo "" >&2
    echo "warnings ratchet ERROR: a workspace build failed without exceeding the warning baseline." >&2
    if [ "${PROD_STATUS}" -ne 0 ]; then
        echo "" >&2
        echo "Production build output:" >&2
        cat "${TMP_PROD}" >&2
    fi
    if [ "${TESTS_STATUS}" -ne 0 ]; then
        echo "" >&2
        echo "Test build output:" >&2
        cat "${TMP_TESTS}" >&2
    fi
    exit 2
fi

echo "warnings ratchet OK: total ${TOTAL} <= baseline ${BASELINE_COUNT}."
exit 0
