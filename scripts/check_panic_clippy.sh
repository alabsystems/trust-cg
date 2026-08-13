#!/usr/bin/env bash
# scripts/check_panic_clippy.sh
#
# Baseline-aware clippy gate for production panic-family sites (#699).
#
# Runs clippy with deny-level panic-family lints, but compares those
# diagnostics against the generated audit baseline instead of requiring the
# already accepted ledger entries to be annotated inline. Unrelated clippy
# diagnostics are reported as notes; the warnings ratchet owns that surface.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
BASELINE="${REPO_ROOT}/ratchet/unwrap_baseline.json"

PACKAGES=()
SKIP_RATCHET=0

usage() {
    cat <<'USAGE'
Usage: scripts/check_panic_clippy.sh [--package NAME]... [--skip-ratchet]

Runs cargo clippy with deny-level panic-family lints:
  clippy::unwrap_used
  clippy::expect_used
  clippy::panic
  clippy::unreachable
  clippy::todo

Existing production sites are accepted only up to ratchet/unwrap_baseline.json.
Full runs also execute scripts/check_unwrap_ratchet.sh and regenerate the local
ratchet/panic_audit.md operator report; that generated report is not part of the
public source snapshot.

Options:
  --package NAME   Check only one workspace package. May be repeated.
  --skip-ratchet   Skip the full unwrap ratchet; intended for focused local
                   clippy probes while other worktrees have dirty files.
  -h, --help       Show this help.
USAGE
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --package|-p)
            if [[ $# -lt 2 ]]; then
                echo "check_panic_clippy: --package requires a value" >&2
                exit 2
            fi
            PACKAGES+=("$2")
            shift 2
            ;;
        --skip-ratchet)
            SKIP_RATCHET=1
            shift
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            echo "check_panic_clippy: unknown argument: $1" >&2
            usage >&2
            exit 2
            ;;
    esac
done

if ! command -v cargo >/dev/null 2>&1; then
    echo "check_panic_clippy: cargo not found on PATH" >&2
    exit 2
fi

if ! command -v python3 >/dev/null 2>&1; then
    echo "check_panic_clippy: python3 not found on PATH" >&2
    exit 2
fi

if [[ ! -f "${BASELINE}" ]]; then
    echo "check_panic_clippy: baseline file missing: ${BASELINE}" >&2
    exit 2
fi

cd "${REPO_ROOT}"

if [[ ${#PACKAGES[@]} -eq 0 ]]; then
    while IFS= read -r package; do
        PACKAGES+=("${package}")
    done < <(cargo metadata --format-version=1 --no-deps |
        python3 scripts/check_panic_clippy.py list-packages)
fi

TMP_DIR="$(mktemp -d -t trust-cg-panic-clippy.XXXXXX)"
trap 'rm -rf "${TMP_DIR}"' EXIT

for package in "${PACKAGES[@]}"; do
    log="${TMP_DIR}/${package}.jsonl"
    echo "[panic-clippy] package=${package}"
    set +e
    cargo clippy -p "${package}" --no-deps --message-format=json -- \
        -A warnings \
        -D clippy::unwrap_used \
        -D clippy::expect_used \
        -D clippy::panic \
        -D clippy::unreachable \
        -D clippy::todo \
        >"${log}" 2>&1
    status=$?
    set -e
    echo "${status}" >"${log}.status"
done

python3 scripts/check_panic_clippy.py summarize "${BASELINE}" "${TMP_DIR}" "${REPO_ROOT}"

if [[ "${SKIP_RATCHET}" -eq 0 ]]; then
    scripts/check_unwrap_ratchet.sh
fi
