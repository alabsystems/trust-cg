#!/usr/bin/env bash
# fuzz_campaign.sh - Run a differential-fuzzing campaign
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
# Usage:
#   scripts/fuzz_campaign.sh --driver <name> --duration <secs> --out <dir>
#
# <name> is one of: trust-ir-gen | trust-ir-jit-diff | csmith-driver | yarpgen-driver
#
# The driver writes a JSON result to <dir>/<driver>.json. On miscompile,
# reprod files land in <dir>/repro-<driver>-seed-<seed>.json (for
# trust-ir-gen) and the driver invokes scripts/file_miscompile_issue.sh if
# TRUST_AUTOFILE=1 is set in the environment.
#
# Cap: 5 minutes per driver is the default. Raise with --duration.

set -euo pipefail

DRIVER=""
DURATION="300"
OUT=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --driver)
            DRIVER="$2"
            shift 2
            ;;
        --duration)
            DURATION="$2"
            shift 2
            ;;
        --out)
            OUT="$2"
            shift 2
            ;;
        -h|--help)
            echo "Usage: $0 --driver <name> --duration <secs> --out <dir>"
            exit 0
            ;;
        *)
            echo "unknown arg: $1" >&2
            exit 2
            ;;
    esac
done

if [[ -z "$DRIVER" || -z "$OUT" ]]; then
    echo "ERROR: --driver and --out are required" >&2
    exit 2
fi

case "$DRIVER" in
    trust-ir-gen|trust-ir-jit-diff|csmith-driver|yarpgen-driver)
        ;;
    *)
        echo "ERROR: unknown driver '$DRIVER'" >&2
        exit 2
        ;;
esac

REPO_ROOT="$(git rev-parse --show-toplevel)"
BIN="$REPO_ROOT/target/release/$DRIVER"

# Build the driver if missing. We trust cargo's own up-to-date check on
# subsequent runs — this is idempotent but not forced.
if [[ ! -x "$BIN" ]]; then
    echo "[fuzz_campaign] building $DRIVER (release) ..."
    (cd "$REPO_ROOT" && cargo build --release -p trust-cg-fuzz --bin "$DRIVER")
fi

mkdir -p "$OUT"

echo "[fuzz_campaign] driver=$DRIVER duration=${DURATION}s out=$OUT"
"$BIN" --duration "$DURATION" --out "$OUT"

JSON="$OUT/$DRIVER.json"
if [[ -f "$JSON" ]]; then
    echo "[fuzz_campaign] results:"
    # Use jq if available, else fall back to grep (the driver writes
    # JSON with one key per line, so simple grep works).
    if command -v jq >/dev/null 2>&1; then
        jq '{status, runs, miscompiles, crashes}' "$JSON"
    else
        grep -E '"(status|runs|miscompiles|crashes)"' "$JSON"
    fi
fi
