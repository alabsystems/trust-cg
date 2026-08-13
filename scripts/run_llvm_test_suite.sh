#!/usr/bin/env bash
#
# scripts/run_llvm_test_suite.sh — WS2 driver.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
# Runs Trust Codegen against the llvm-test-suite SingleSource
# correctness corpus and emits a single evals JSON summary. See WS2
# (issue #439) through the maintained standalone corpus runner.
#
# Algorithm per program:
#   1. clang -O0 -S -emit-llvm -> <prog>.ll        (reference IR)
#   2. trust-cg-ws2-import <prog>.ll <prog>.o         (Trust Codegen pipeline)
#      - unsupported construct: first stderr line starts `unsupported:`
#        => status: unsupported, recorded reason, skip to next program.
#      - other failure => status: crash, stderr captured.
#   3. cc <prog>.o -o <prog>.bin                   (host linker)
#   4. <prog>.bin > actual_out                     (run)
#   5. diff actual_out expected.ref                (compare)
#      - match => status: pass
#      - mismatch => status: fail, diff captured.
#
# Usage:
#   scripts/run_llvm_test_suite.sh --out evals/results/llvm-test-suite/<date>.json
#   scripts/run_llvm_test_suite.sh --filter "*CastTest*"
#
# The corpus is hardcoded below (5 programs). It is *not* vendored into
# this repo. Each run requires `~/llvm-test-suite-ref/` to be present.

set -u
set -o pipefail

usage() {
    cat <<'USAGE'
Usage: run_llvm_test_suite.sh [--out <path>] [--filter <glob>]

  --out PATH    Write evals JSON to PATH. Default: evals/results/llvm-test-suite/<UTC-date>.json
  --filter G    Run only programs whose name matches shell glob G.
  -h, --help    Show this help.
USAGE
}

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
REF_ROOT="${LLVM_TEST_SUITE_REF:-$HOME/llvm-test-suite-ref}"
FILTER="*"
OUT=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --out)    OUT="$2"; shift 2;;
        --filter) FILTER="$2"; shift 2;;
        -h|--help) usage; exit 0;;
        *) echo "unknown argument: $1" >&2; usage; exit 2;;
    esac
done

if [[ -z "$OUT" ]]; then
    date="$(date -u +%Y-%m-%d)"
    OUT="$REPO_ROOT/evals/results/llvm-test-suite/$date.json"
fi
mkdir -p "$(dirname "$OUT")"

# --- Corpus ---------------------------------------------------------------
#
# Five small integer programs from
# ~/llvm-test-suite-ref/SingleSource/UnitTests/. The selection targets
# different subset features (signed/unsigned casts, bitwise ops, division)
# so we exercise a spread of importer opcodes. Every program calls
# printf("literal"), which currently trips the importer's
# "address-of global" guard and therefore classifies as `unsupported`
# in this baseline. That is the designed signal: the driver logs a
# truthful per-reason count rather than a fake pass, and the expansion
# remaining importer coverage gap is global-address materialization.
CORPUS=(
    "SingleSource/UnitTests/2002-05-02-CastTest1"
    "SingleSource/UnitTests/2002-05-02-CastTest3"
    "SingleSource/UnitTests/2002-05-03-NotTest"
    "SingleSource/UnitTests/2002-05-19-DivTest"
    "SingleSource/UnitTests/2002-08-02-CastTest"
)

# --- Tool discovery -------------------------------------------------------
CLANG="${CLANG:-clang}"
CC="${CC:-cc}"
IMPORTER="$REPO_ROOT/target/release/trust-cg-ws2-import"

echo "building trust-cg-ws2-import (release)..." >&2
# Existing release binaries may come from an older checkout; rebuild so the
# evidence JSON always reflects the source commit recorded below.
(cd "$REPO_ROOT" && cargo build -p trust-cg-llvm-import --release --bin trust-cg-ws2-import --features driver 2>&1) \
    | tail -5 >&2 || { echo "FATAL: cargo build failed" >&2; exit 1; }
if [[ ! -x "$IMPORTER" ]]; then
    echo "FATAL: $IMPORTER missing after build" >&2
    exit 1
fi

if ! command -v "$CLANG" >/dev/null 2>&1; then
    echo "FATAL: clang not found (set CLANG=...)" >&2
    exit 1
fi
if ! command -v "$CC" >/dev/null 2>&1; then
    echo "FATAL: cc not found (set CC=...)" >&2
    exit 1
fi
if [[ ! -d "$REF_ROOT" ]]; then
    echo "FATAL: llvm-test-suite not found at $REF_ROOT" >&2
    echo "       clone https://github.com/llvm/llvm-test-suite and set LLVM_TEST_SUITE_REF" >&2
    exit 1
fi

# --- Run ------------------------------------------------------------------
work="$(mktemp -d -t ws2.XXXXXX)"
trap 'rm -rf "$work"' EXIT

passed=0
total=0
items_json=""

commit_hash="$(git -C "$REPO_ROOT" rev-parse HEAD 2>/dev/null || echo "unknown")"
clang_version="$("$CLANG" --version 2>/dev/null | head -1)"
timestamp="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

if ! command -v jq >/dev/null 2>&1; then
    echo "FATAL: jq not found (brew install jq)" >&2
    exit 1
fi

append_item() {
    local name="$1" status="$2" reason="$3" stdout_snippet="$4"
    # Use jq to safely JSON-encode every field. `-Rs` reads stdin as a
    # single string; piping individual fields avoids shell quoting
    # traps. `-c` keeps each entry on one line so the final `items`
    # array stays greppable.
    local entry
    entry="$(jq -cn \
        --arg name "$name" \
        --arg status "$status" \
        --arg reason "$reason" \
        --arg stdout_head "$stdout_snippet" \
        '{name: $name, status: $status, reason: $reason, stdout_head: $stdout_head}')"
    if [[ -z "$items_json" ]]; then
        items_json="$entry"
    else
        items_json="$items_json, $entry"
    fi
}

for rel in "${CORPUS[@]}"; do
    base="$(basename "$rel")"
    # shellcheck disable=SC2053
    if [[ "$base" != $FILTER ]]; then
        continue
    fi
    total=$((total + 1))
    src="$REF_ROOT/$rel.c"
    ref="$REF_ROOT/$rel.reference_output"

    if [[ ! -f "$src" ]]; then
        append_item "$base" "unsupported" "source missing at $src" ""
        continue
    fi

    ll="$work/$base.ll"
    obj="$work/$base.o"
    bin="$work/$base.bin"
    actual="$work/$base.actual"
    importer_err="$work/$base.import.err"

    if ! "$CLANG" -O0 -S -emit-llvm -o "$ll" "$src" 2>"$work/$base.clang.err"; then
        append_item "$base" "crash" "clang failed: $(tr '\n' ' ' <"$work/$base.clang.err" | head -c 200)" ""
        continue
    fi

    if ! "$IMPORTER" "$ll" "$obj" 2>"$importer_err"; then
        first_err="$(head -1 "$importer_err")"
        if [[ "$first_err" == unsupported:* ]]; then
            reason="${first_err#unsupported: }"
            append_item "$base" "unsupported" "$reason" ""
        else
            append_item "$base" "crash" "$first_err" ""
        fi
        continue
    fi

    if ! "$CC" "$obj" -o "$bin" 2>"$work/$base.ld.err"; then
        append_item "$base" "crash" "link failed: $(tr '\n' ' ' <"$work/$base.ld.err" | head -c 200)" ""
        continue
    fi

    if ! "$bin" >"$actual" 2>"$work/$base.run.err"; then
        append_item "$base" "crash" "runtime failure" ""
        continue
    fi

    # llvm-test-suite reference outputs typically end with `exit N`;
    # we compare only the pre-"exit" prefix.
    ref_body="$(sed -n '/^exit /!p' "$ref")"
    actual_body="$(cat "$actual")"
    if [[ "$ref_body" == "$actual_body" ]]; then
        passed=$((passed + 1))
        append_item "$base" "pass" "" "$(echo "$actual_body" | head -c 120)"
    else
        append_item "$base" "fail" "output mismatch" "$(echo "$actual_body" | head -c 120)"
    fi
done

# --- JSON emission --------------------------------------------------------
# Matches the evals schema used elsewhere in Trust Codegen: top-level `metrics`,
# per-program `items` list, metadata block.
{
    printf '{\n'
    printf '  "schema": "evals/v1",\n'
    printf '  "suite": "llvm-test-suite-singlesource",\n'
    printf '  "timestamp": "%s",\n' "$timestamp"
    printf '  "commit": "%s",\n' "$commit_hash"
    printf '  "clang_version": "%s",\n' "$clang_version"
    printf '  "filter": "%s",\n' "$FILTER"
    printf '  "metrics": { "passed": %d, "total": %d },\n' "$passed" "$total"
    printf '  "items": [ %s ]\n' "$items_json"
    printf '}\n'
} >"$OUT"

echo "wrote $OUT: $passed / $total passed" >&2

# Refresh the latest-report marker so weekly reporting keeps pointing at
# the newest run without a manual edit.
summarize="$REPO_ROOT/scripts/summarize_llvm_test_suite.sh"
if [[ -x "$summarize" ]]; then
    "$summarize" "$OUT" >"$REPO_ROOT/reports/llvm-test-suite-latest.md"
fi
