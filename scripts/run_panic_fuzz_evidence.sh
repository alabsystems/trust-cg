#!/usr/bin/env bash
# scripts/run_panic_fuzz_evidence.sh
#
# Focused panic-fuzz evidence lane for #372 / #689 / #700.
#
# Runs the panic-fuzz families named by the crash-free codegen plan
# with PROPTEST_CASES=256 by default, and checks that the matching
# cargo-fuzz targets are discoverable when cargo-fuzz is installed. The
# opt-in nightly lane raises that to 1,000,000 proptest cases and runs each
# matching cargo-fuzz target for a bounded duration with retained logs.

set -euo pipefail

usage() {
    cat <<'EOF'
Usage: scripts/run_panic_fuzz_evidence.sh [OPTIONS]

Run the #372 panic-fuzz proptest families with PROPTEST_CASES=256.

Options:
  --lane pr|nightly    Select the evidence lane (default: pr).
  --nightly            Alias for --lane nightly.
  --cases N             Set PROPTEST_CASES to N (default: env value or 256).
                       Nightly defaults to 1000000.
  --fuzz-seconds N     Nightly cargo-fuzz seconds per target (default: env
                       TRUST_CG_PANIC_FUZZ_FUZZ_SECONDS or 3600).
  --test-timeout-seconds N
                       Per-family proptest timeout for the nightly lane
                       (default: env TRUST_CG_PANIC_FUZZ_TEST_TIMEOUT_SECONDS
                       or 7200; 0 disables).
  --artifact-dir DIR   Retain nightly logs and artifacts under DIR (default:
                       evals/results/panic-fuzz/nightly/<utc-stamp>).
  --retention-days N   Document the expected artifact retention window
                       (default: env TRUST_CG_PANIC_FUZZ_RETENTION_DAYS or 14).
  --dry-run            Print/write the configured commands without running.
  --skip-cargo-fuzz    Explicitly skip cargo-fuzz target discovery when the
                       cargo-fuzz subcommand is not installed.
  --negative-control   Run the deliberate-panic control and require it to fail.
  -h, --help           Show this help.

Behavior:
  By default, missing cargo-fuzz is an error with install instructions.
  Use --skip-cargo-fuzz only when recording an environment where cargo-fuzz
  cannot be installed for a PR-lane run. Nightly runs require cargo-fuzz and
  reject --skip-cargo-fuzz.
EOF
}

LANE="pr"
CASES="${PROPTEST_CASES:-}"
FUZZ_SECONDS="${TRUST_CG_PANIC_FUZZ_FUZZ_SECONDS:-}"
TEST_TIMEOUT_SECONDS="${TRUST_CG_PANIC_FUZZ_TEST_TIMEOUT_SECONDS:-}"
ARTIFACT_DIR="${TRUST_CG_PANIC_FUZZ_ARTIFACT_DIR:-}"
RETENTION_DAYS="${TRUST_CG_PANIC_FUZZ_RETENTION_DAYS:-14}"
SKIP_CARGO_FUZZ=0
NEGATIVE_CONTROL=0
DRY_RUN=0

while [[ $# -gt 0 ]]; do
    case "$1" in
        --lane)
            LANE="$2"
            shift 2
            ;;
        --lane=*)
            LANE="${1#--lane=}"
            shift
            ;;
        --nightly)
            LANE="nightly"
            shift
            ;;
        --cases)
            CASES="$2"
            shift 2
            ;;
        --cases=*)
            CASES="${1#--cases=}"
            shift
            ;;
        --fuzz-seconds)
            FUZZ_SECONDS="$2"
            shift 2
            ;;
        --fuzz-seconds=*)
            FUZZ_SECONDS="${1#--fuzz-seconds=}"
            shift
            ;;
        --test-timeout-seconds)
            TEST_TIMEOUT_SECONDS="$2"
            shift 2
            ;;
        --test-timeout-seconds=*)
            TEST_TIMEOUT_SECONDS="${1#--test-timeout-seconds=}"
            shift
            ;;
        --artifact-dir)
            ARTIFACT_DIR="$2"
            shift 2
            ;;
        --artifact-dir=*)
            ARTIFACT_DIR="${1#--artifact-dir=}"
            shift
            ;;
        --retention-days)
            RETENTION_DAYS="$2"
            shift 2
            ;;
        --retention-days=*)
            RETENTION_DAYS="${1#--retention-days=}"
            shift
            ;;
        --dry-run)
            DRY_RUN=1
            shift
            ;;
        --skip-cargo-fuzz)
            SKIP_CARGO_FUZZ=1
            shift
            ;;
        --negative-control)
            NEGATIVE_CONTROL=1
            shift
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            echo "run_panic_fuzz_evidence: unknown arg: $1" >&2
            usage >&2
            exit 2
            ;;
    esac
done

if [[ "$LANE" != "pr" && "$LANE" != "nightly" ]]; then
    echo "run_panic_fuzz_evidence: --lane must be 'pr' or 'nightly'" >&2
    exit 2
fi

if [[ -z "$CASES" ]]; then
    if [[ "$LANE" == "nightly" ]]; then
        CASES=1000000
    else
        CASES=256
    fi
fi

if [[ -z "$FUZZ_SECONDS" ]]; then
    if [[ "$LANE" == "nightly" ]]; then
        FUZZ_SECONDS=3600
    else
        FUZZ_SECONDS=0
    fi
fi

if [[ -z "$TEST_TIMEOUT_SECONDS" ]]; then
    if [[ "$LANE" == "nightly" ]]; then
        TEST_TIMEOUT_SECONDS=7200
    else
        TEST_TIMEOUT_SECONDS=0
    fi
fi

require_positive_integer() {
    local name="$1"
    local value="$2"
    if ! [[ "$value" =~ ^[0-9]+$ ]] || [[ "$value" -eq 0 ]]; then
        echo "run_panic_fuzz_evidence: $name must be a positive integer" >&2
        exit 2
    fi
}

require_non_negative_integer() {
    local name="$1"
    local value="$2"
    if ! [[ "$value" =~ ^[0-9]+$ ]]; then
        echo "run_panic_fuzz_evidence: $name must be a non-negative integer" >&2
        exit 2
    fi
}

require_positive_integer "--cases" "$CASES"
if [[ "$LANE" == "nightly" ]]; then
    require_positive_integer "--fuzz-seconds" "$FUZZ_SECONDS"
else
    require_non_negative_integer "--fuzz-seconds" "$FUZZ_SECONDS"
fi
require_non_negative_integer "--test-timeout-seconds" "$TEST_TIMEOUT_SECONDS"
require_positive_integer "--retention-days" "$RETENTION_DAYS"

if [[ "$LANE" == "nightly" && "$SKIP_CARGO_FUZZ" -eq 1 ]]; then
    echo "run_panic_fuzz_evidence: nightly lane requires cargo-fuzz; remove --skip-cargo-fuzz" >&2
    exit 2
fi

REPO_ROOT="$(git rev-parse --show-toplevel)"
CARGO_BIN="${CARGO_BIN:-cargo}"
export PROPTEST_CASES="$CASES"
: "${CARGO_SKIP_CACHE:=1}"
export CARGO_SKIP_CACHE

FAMILIES=(
    "lower translate_function|trust-cg-lower|panic_fuzz_lower|fuzz_translate_function"
    "compile Pipeline::compile_function|trust-cg-codegen|panic_fuzz_compile|fuzz_compile_function"
    "compile x86-64 X86Pipeline|trust-cg-codegen|panic_fuzz_compile_x86_64|fuzz_compile_x86_64"
    "encode AArch64 instruction|trust-cg-codegen|panic_fuzz_encode|fuzz_encode_instruction"
    "Mach-O fixup/relocation|trust-cg-codegen|panic_fuzz_macho_fixup|fuzz_macho_fixup"
    "verify MachFunction|trust-cg-verify|panic_fuzz_verify|fuzz_verify_module"
)

FUZZ_TARGETS=(
    "fuzz_translate_function"
    "fuzz_compile_function"
    "fuzz_compile_x86_64"
    "fuzz_encode_instruction"
    "fuzz_macho_fixup"
    "fuzz_verify_module"
)

if [[ "$LANE" == "nightly" && -z "$ARTIFACT_DIR" ]]; then
    RUN_STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
    ARTIFACT_DIR="evals/results/panic-fuzz/nightly/$RUN_STAMP"
fi

cd "$REPO_ROOT"

if [[ -n "$ARTIFACT_DIR" ]]; then
    mkdir -p "$ARTIFACT_DIR/logs" "$ARTIFACT_DIR/fuzz-artifacts"
    MANIFEST_PATH="$ARTIFACT_DIR/manifest.txt"
    {
        echo "lane=$LANE"
        echo "utc_start=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
        echo "proptest_cases=$CASES"
        echo "cargo_fuzz_seconds_per_target=$FUZZ_SECONDS"
        echo "proptest_timeout_seconds_per_family=$TEST_TIMEOUT_SECONDS"
        echo "retention_days=$RETENTION_DAYS"
        echo "dry_run=$DRY_RUN"
        echo "cargo=$CARGO_BIN"
        echo "families=${#FAMILIES[@]}"
        for family in "${FAMILIES[@]}"; do
            IFS='|' read -r label package test_target fuzz_target <<<"$family"
            echo "family=$label package=$package test=$test_target fuzz_target=$fuzz_target"
        done
    } > "$MANIFEST_PATH"
else
    MANIFEST_PATH=""
fi

finish_manifest() {
    local status="$?"
    if [[ -n "$MANIFEST_PATH" ]]; then
        echo "utc_end=$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$MANIFEST_PATH"
        if [[ "$status" -eq 0 && "$DRY_RUN" -eq 1 ]]; then
            echo "status=dry-run" >> "$MANIFEST_PATH"
        elif [[ "$status" -eq 0 ]]; then
            echo "status=passed" >> "$MANIFEST_PATH"
        else
            echo "status=failed" >> "$MANIFEST_PATH"
            echo "exit_status=$status" >> "$MANIFEST_PATH"
        fi
    fi
}
trap finish_manifest EXIT

command_line() {
    printf '%q ' "$@"
}

run_logged() {
    local log_path="$1"
    shift
    local -a cmd=("$@")

    echo "[panic-fuzz] command: $(command_line "${cmd[@]}")"
    if [[ "$DRY_RUN" -eq 1 ]]; then
        echo "[panic-fuzz] DRY-RUN: command not executed"
        if [[ -n "$log_path" ]]; then
            printf '$ %s\n' "$(command_line "${cmd[@]}")" > "$log_path"
            echo "[panic-fuzz] DRY-RUN: wrote command log $log_path"
        fi
        return 0
    fi

    if [[ -n "$log_path" ]]; then
        set +e
        "${cmd[@]}" 2>&1 | tee "$log_path"
        local status=${PIPESTATUS[0]}
        set -e
        return "$status"
    fi

    "${cmd[@]}"
}

run_timed_logged() {
    local seconds="$1"
    local log_path="$2"
    shift 2
    local -a cmd=("$@")
    local timeout_bin=""

    if [[ "$seconds" -gt 0 ]]; then
        if command -v timeout >/dev/null 2>&1; then
            timeout_bin="timeout"
        elif command -v gtimeout >/dev/null 2>&1; then
            timeout_bin="gtimeout"
        fi

        if [[ -n "$timeout_bin" ]]; then
            cmd=("$timeout_bin" "$seconds" "${cmd[@]}")
        else
            echo "[panic-fuzz] WARNING: timeout/gtimeout not found; configured timeout ${seconds}s is documented but not enforced by this shell"
        fi
    fi

    run_logged "$log_path" "${cmd[@]}"
}

echo "[panic-fuzz] repo=$REPO_ROOT"
echo "[panic-fuzz] cargo=$CARGO_BIN"
echo "[panic-fuzz] lane=$LANE"
echo "[panic-fuzz] PROPTEST_CASES=$PROPTEST_CASES"
echo "[panic-fuzz] fuzz_seconds_per_target=$FUZZ_SECONDS"
echo "[panic-fuzz] proptest_timeout_seconds_per_family=$TEST_TIMEOUT_SECONDS"
echo "[panic-fuzz] CARGO_SKIP_CACHE=$CARGO_SKIP_CACHE"
echo "[panic-fuzz] retention_days=$RETENTION_DAYS"
if [[ -n "$ARTIFACT_DIR" ]]; then
    echo "[panic-fuzz] artifact_dir=$ARTIFACT_DIR"
    echo "[panic-fuzz] manifest=$MANIFEST_PATH"
fi
if [[ "$DRY_RUN" -eq 1 ]]; then
    echo "[panic-fuzz] dry_run=1"
fi

if [[ "$NEGATIVE_CONTROL" -eq 1 ]]; then
    echo "[panic-fuzz] running deliberate-panic negative control"
    NEGATIVE_LOG="$(mktemp -t trust-cg-panic-fuzz-negative.XXXXXX)"
    set +e
    TRUST_CG_PANIC_FUZZ_NEGATIVE_CONTROL=1 "$CARGO_BIN" test \
        -p trust-cg-lower \
        --test panic_fuzz_lower \
        panic_fuzz_negative_control_fails_when_enabled \
        -- --nocapture 2>&1 | tee "$NEGATIVE_LOG"
    STATUS=${PIPESTATUS[0]}
    set -e
    if [[ "$STATUS" -eq 0 ]]; then
        echo "[panic-fuzz] ERROR: deliberate-panic negative control unexpectedly passed" >&2
        rm -f "$NEGATIVE_LOG"
        exit 1
    fi
    if ! grep -Fq "panic-fuzz negative control observed deliberate panic" "$NEGATIVE_LOG"; then
        echo "[panic-fuzz] ERROR: negative control failed for the wrong reason" >&2
        echo "[panic-fuzz] expected panic signature was absent from: $NEGATIVE_LOG" >&2
        exit 1
    fi
    rm -f "$NEGATIVE_LOG"
    echo "[panic-fuzz] deliberate-panic negative control failed as expected (status=$STATUS)"
    exit 0
fi

if [[ "$DRY_RUN" -eq 1 ]]; then
    echo "[panic-fuzz] DRY-RUN: cargo-fuzz discovery command: $CARGO_BIN fuzz list --fuzz-dir fuzz"
elif "$CARGO_BIN" fuzz --version >/dev/null 2>&1; then
    echo "[panic-fuzz] cargo-fuzz installed: $("$CARGO_BIN" fuzz --version)"
    TARGET_LIST="$("$CARGO_BIN" fuzz list --fuzz-dir fuzz)"
    echo "[panic-fuzz] cargo-fuzz targets:"
    while IFS= read -r target_line; do
        echo "[panic-fuzz]   $target_line"
    done <<< "$TARGET_LIST"
    for target in "${FUZZ_TARGETS[@]}"; do
        if ! echo "$TARGET_LIST" | grep -Fxq "$target"; then
            echo "[panic-fuzz] ERROR: missing cargo-fuzz target: $target" >&2
            exit 1
        fi
    done
else
    if [[ "$SKIP_CARGO_FUZZ" -eq 1 ]]; then
        echo "[panic-fuzz] SKIP cargo-fuzz target discovery: cargo-fuzz is not installed."
        echo "[panic-fuzz] Install with: cargo install cargo-fuzz"
    else
        echo "[panic-fuzz] ERROR: cargo-fuzz is not installed." >&2
        echo "[panic-fuzz] Install with: cargo install cargo-fuzz" >&2
        echo "[panic-fuzz] Or rerun with --skip-cargo-fuzz to record an explicit skip." >&2
        exit 2
    fi
fi

for family in "${FAMILIES[@]}"; do
    IFS='|' read -r label package test_target fuzz_target <<<"$family"
    echo "[panic-fuzz] running family='$label' package=$package test=$test_target fuzz_target=$fuzz_target"
    log_path=""
    if [[ -n "$ARTIFACT_DIR" ]]; then
        log_path="$ARTIFACT_DIR/logs/proptest-$test_target.log"
    fi
    run_timed_logged "$TEST_TIMEOUT_SECONDS" "$log_path" \
        "$CARGO_BIN" test -p "$package" --test "$test_target"
done

if [[ "$LANE" == "nightly" ]]; then
    echo "[panic-fuzz] running cargo-fuzz target family for ${FUZZ_SECONDS}s per target"
    for target in "${FUZZ_TARGETS[@]}"; do
        target_artifacts=""
        log_path=""
        if [[ -n "$ARTIFACT_DIR" ]]; then
            target_artifacts="$ARTIFACT_DIR/fuzz-artifacts/$target"
            mkdir -p "$target_artifacts"
            log_path="$ARTIFACT_DIR/logs/cargo-fuzz-$target.log"
        fi
        libfuzzer_args=("-max_total_time=$FUZZ_SECONDS")
        if [[ -n "$target_artifacts" ]]; then
            artifact_prefix="$target_artifacts"
            if [[ "$artifact_prefix" != /* ]]; then
                artifact_prefix="$REPO_ROOT/$artifact_prefix"
            fi
            libfuzzer_args+=("-artifact_prefix=$artifact_prefix/")
        fi
        run_timed_logged "$((FUZZ_SECONDS + 300))" "$log_path" \
            "$CARGO_BIN" fuzz run "$target" --fuzz-dir fuzz -- "${libfuzzer_args[@]}"
    done
fi

if [[ "$DRY_RUN" -eq 1 ]]; then
    echo "[panic-fuzz] complete dry-run: ${#FAMILIES[@]} families configured with PROPTEST_CASES=$PROPTEST_CASES"
    if [[ "$LANE" == "nightly" ]]; then
        echo "[panic-fuzz] complete dry-run: ${#FUZZ_TARGETS[@]} cargo-fuzz targets configured for ${FUZZ_SECONDS}s each"
    fi
else
    echo "[panic-fuzz] complete: ${#FAMILIES[@]} families passed with PROPTEST_CASES=$PROPTEST_CASES"
    if [[ "$LANE" == "nightly" ]]; then
        echo "[panic-fuzz] complete: ${#FUZZ_TARGETS[@]} cargo-fuzz targets ran for ${FUZZ_SECONDS}s each"
    fi
fi
