#!/usr/bin/env bash
# scripts/run_full_test_matrix.sh
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Issue:  Part of #437 (WS1 — Measured workspace pass-count)
#
# Runs `cargo test` per workspace crate with `--no-fail-fast` and captures
# libtest output. Nightly toolchains use JSON; stable toolchains use the
# standard text summary. Every shard runs in an isolated process group with a
# finite wall-clock bound.
#
# Cargo invocations are serialized by this runner; shards run sequentially.
#
# Output:
#   evals/results/tests/<ISO-date>.json
#     {
#       "date": "YYYY-MM-DD",
#       "commit": "<sha>",
#       "rustc": "<version>",
#       "shards": [
#         { "crate": "...", "shard": "...",
#           "passed": N, "failed": N, "ignored": N, "filtered": N,
#           "status": "pass|fail|skipped|timeout|incomplete",
#           "time_s": F, "suites": N, "notes": "..." }
#       ],
#       "totals": { "passed": ..., "failed": ..., "ignored": ..., "filtered": ...,
#                   "outcome_counts": {"pass": N, "fail": N, "skipped": N,
#                                      "timeout": N, "incomplete": N},
#                   "time_s": ... }
#     }
#
# Usage:
#   scripts/run_full_test_matrix.sh                # write evals/results/tests/<today>.json
#   scripts/run_full_test_matrix.sh --out FILE     # write to a specific path
#   scripts/run_full_test_matrix.sh --dry-run      # print the selected shard plan only
#   scripts/run_full_test_matrix.sh --only SELECTOR # run one crate, shard, or CRATE|SHARD
#   scripts/run_full_test_matrix.sh --report-only  # always exit 0 after writing a complete report
#   scripts/run_full_test_matrix.sh --check-rustc-backend-env
#       # require the pinned rustc_codegen_trust_cg nightly + rustc-dev components,
#       # then cargo-check the rustc private backend crate
#
# Exit codes:
#   0 — every selected shard completed successfully
#   1 — a test/shard failed, timed out, was skipped/incomplete, or tooling failed
#   64 — invalid CLI args or --only selector
#
# `--report-only` preserves the historical measurement behavior by returning 0
# after a complete report even when a shard is non-green. Without that explicit
# option the matrix is fail-closed. The plan is validated against the current
# Cargo metadata, so newly added packages or integration targets cannot remain
# outside the measured denominator. README.md and LIMITATIONS.md define how to
# interpret the resulting coverage numbers.

set -uo pipefail

prepend_path_dir() {
    [ -d "$1" ] || return 0
    case ":${PATH:-}:" in
        *:"$1":*) ;;
        *) PATH="$1:${PATH:-}" ;;
    esac
}

case ":${PATH:-}:" in
    *:/usr/bin:*) ;;
    *) PATH="/usr/bin:${PATH:-}" ;;
esac

if ! command -v cargo >/dev/null 2>&1; then
    [ -z "${CARGO_HOME:-}" ] || prepend_path_dir "${CARGO_HOME}/bin"
    [ -z "${HOME:-}" ] || prepend_path_dir "${HOME}/.cargo/bin"
    [ -z "${USER:-}" ] || prepend_path_dir "/c/Users/${USER}/.cargo/bin"
    if [ -n "${USERPROFILE:-}" ] && command -v cygpath >/dev/null 2>&1; then
        prepend_path_dir "$(cygpath -u "${USERPROFILE}")/.cargo/bin"
    fi
fi
export PATH

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
RUN_WITH_TIMEOUT="${SCRIPT_DIR}/run_with_timeout.py"
EVALS_DIR="${REPO_ROOT}/evals/results/tests"
TODAY="$(date -u +%Y-%m-%d)"
DEFAULT_OUT="${EVALS_DIR}/${TODAY}.json"

OUT="${DEFAULT_OUT}"
DRY_RUN=0
ONLY=""
ONLY_SET=0
CHECK_RUSTC_BACKEND_ENV=0
REPORT_ONLY=0

usage_error() {
    echo "run_full_test_matrix: $*" >&2
    exit 64
}

while [ $# -gt 0 ]; do
    case "$1" in
        --out)
            [ $# -ge 2 ] || usage_error "--out requires a path"
            OUT="$2"; shift 2 ;;
        --out=*)
            OUT="${1#--out=}"; shift ;;
        --dry-run)
            DRY_RUN=1; shift ;;
        --only)
            [ $# -ge 2 ] || usage_error "--only requires a selector"
            ONLY_SET=1
            ONLY="$2"; shift 2 ;;
        --only=*)
            ONLY_SET=1
            ONLY="${1#--only=}"; shift ;;
        --check-rustc-backend-env)
            CHECK_RUSTC_BACKEND_ENV=1; shift ;;
        --report-only)
            REPORT_ONLY=1; shift ;;
        -h|--help)
            sed -n '2,41p' "$0" | sed 's/^# \{0,1\}//'
            exit 0 ;;
        *)
            usage_error "unknown arg: $1" ;;
    esac
done

if [ "${ONLY_SET}" -eq 1 ] && [ -z "${ONLY}" ]; then
    usage_error "--only requires a non-empty selector"
fi

# Some verifier proof tests recurse deeply enough to overflow the default
# libtest thread stack in debug builds. Keep this override local to the matrix
# runner; callers can still raise/lower it explicitly.
: "${RUST_MIN_STACK:=67108864}"
export RUST_MIN_STACK

# --- BENCH-10 measurement (bench) stage --------------------------------------
# Wire the BENCH measurement gates into the existing local-gate cadence (the
# project's no-GitHub-CI stance, SOUNDNESS_CHECK.md): every plain full-matrix
# run also evaluates the compile-time canary + perf ratchet + determinism sentinel
# + soundness-lock drift via the single entry point scripts/landing_checks.sh.
#
# Additive and SAFE by construction:
#   - runs ONLY on a plain full invocation (skipped for --dry-run / --only /
#     --check-rustc-backend-env, which are targeted/introspection modes);
#   - skippable via TCG_SKIP_BENCH_STAGE=1 (the skip is LOGGED, mirroring the
#     repo's explicit-opt-out convention);
#   - NON-FATAL to the matrix: the stage prints its verdict and the matrix
#     continues to the test shards regardless, so it can never convert a
#     load-noisy bench result into a false matrix tooling failure. (landing_checks.sh
#     itself keeps the 0/1/2 convention; here we only surface it.)
if [ "${DRY_RUN}" -eq 0 ] && [ "${ONLY_SET}" -eq 0 ] && [ "${CHECK_RUSTC_BACKEND_ENV}" -eq 0 ]; then
    if [ "${TCG_SKIP_BENCH_STAGE:-0}" = 1 ]; then
        echo "run_full_test_matrix: bench stage SKIPPED (TCG_SKIP_BENCH_STAGE=1)"
    else
        echo "=== bench stage (BENCH-10): scripts/landing_checks.sh ==="
        if "${SCRIPT_DIR}/landing_checks.sh"; then
            echo "run_full_test_matrix: bench stage GREEN"
        else
            bench_rc=$?
            echo "run_full_test_matrix: bench stage NON-GREEN (rc=${bench_rc}: 1=regression/MISMATCH, 2=tooling/loaded) — surfaced, not fatal to the test matrix; investigate before landing" >&2
        fi
        echo "=== end bench stage ==="
    fi
fi

# --- Shard plan ---------------------------------------------------------------
#
# Each line:  <crate>|<shard-name>|<cargo-args>|<notes>
#
# cargo-args is everything that goes after `cargo test`. The script appends
# `--no-fail-fast`; on nightly it also asks libtest for JSON/report-time output.
#
# For trust-cg-codegen, we shard by test binary (`--lib` + per-integration-group
# via `--test <file>`). Integration tests are independent binaries so a
# single `cargo test --test X` builds and runs just that binary.
#
# Policy: every Cargo workspace package must be present in this plan unless it
# is listed as an approved exclusion in validate_shard_policy(). For crates
# sharded with explicit `--test` selectors, every integration-test target must
# be assigned to a shard unless it is explicitly excluded there.

# Format: <crate>|<shard-name>|<cargo-args>|<libtest-post-args>|<notes>
# * cargo-args: goes after `cargo test`, before `--`.
# * libtest-post-args: goes after `--`, after any nightly JSON/report-time flags.
#   Use this for `--skip <prefix>` or other libtest flags.
read -r -d '' SHARD_PLAN <<'EOF' || true
trust-cg-ir|all|-p trust-cg-ir||
trust-cg-dialect|all|-p trust-cg-dialect||
trust-cg-lower|all|-p trust-cg-lower||
trust-cg-opt|all|-p trust-cg-opt||
trust-cg-lift|all|-p trust-cg-lift||
trust-cg-regalloc|all|-p trust-cg-regalloc||
trust-cg-gpu|all|-p trust-cg-gpu||
trust-cg-fuzz|all|-p trust-cg-fuzz||
trust-cg-llvm-import|lib|-p trust-cg-llvm-import --lib||
trust-cg-llvm-import|integration|-p trust-cg-llvm-import --tests --features driver||
trust-cg-llvm-import|driver-bin|-p trust-cg-llvm-import --bin trust-cg-ws2-import --features driver||
trust-cg-onnx-import|all|-p trust-cg-onnx-import||
trust-cg-jit-matrix|all|-p trust-cg-jit-matrix||
trust-cg-sat-host|all|-p trust-cg-sat-host||
trust-cg-process-env|all|-p trust-cg-process-env||
trust-cg-drat-trim|all|-p trust-cg-drat-trim||
trust-cg-test|all|-p trust-cg-test||
trust-types|all|-p trust-types||
trust-cg-verify|lib-runner|-p trust-cg-verify --lib|verification_runner::|verification_runner unit tests use representative/subset ProofDatabases with a small runner sample cap; full-database runner verification is opt-in via slow-full-database.
trust-cg-verify|lib-memory-atomic|-p trust-cg-verify --lib|memory_proofs:: atomic_proofs:: addr_mode_proofs::|Memory + atomic are the other slow suites (>100s each).
trust-cg-verify|lib-synthesis|-p trust-cg-verify --lib|unified_synthesis:: cegis:: cegis_pass:: rule_discovery:: proof_database:: proof_certificate:: function_verifier::|Synthesis / CEGIS / proof-database — medium-weight.
trust-cg-verify|lib-neon-vec|-p trust-cg-verify --lib|neon_encoding_proofs:: neon_lowering_proofs:: vectorization_proofs::|NEON encoding / lowering / vectorization proofs (each ~60-75s).
trust-cg-verify|lib-other|-p trust-cg-verify --lib|--skip verification_runner:: --skip memory_proofs:: --skip atomic_proofs:: --skip addr_mode_proofs:: --skip unified_synthesis:: --skip cegis:: --skip cegis_pass:: --skip rule_discovery:: --skip proof_database:: --skip proof_certificate:: --skip function_verifier:: --skip neon_encoding_proofs:: --skip neon_lowering_proofs:: --skip vectorization_proofs::|Everything else in the trust-cg-verify library (arithmetic, peephole, CFG, DCE, GVN, LICM, and related modules).
trust-cg-verify|integration|-p trust-cg-verify --tests||All integration targets under crates/trust-cg-verify/tests/; Cargo metadata and validate_shard_policy keep the denominator complete.
trust-cg-cli|all|-p trust-cg-cli||
trust-cg-codegen|lib|-p trust-cg-codegen --lib||
trust-cg-codegen|integration-aarch64|-p trust-cg-codegen --test aarch64_encoding --test aarch64_incoming_arg_zero_offset_load --test aarch64_msub_mneg_encode --test aarch64_petri_o2_o3_incoming_arg_canary --test compact_unwind_integration --test e2e_aarch64_link||
trust-cg-codegen|integration-abi|-p trust-cg-codegen --test abi_many_args_e2e --test e2e_abi_dual_target --test e2e_abi_dual_target_linkrun||
trust-cg-codegen|integration-x86_64|-p trust-cg-codegen --test e2e_x86_64_correctness --test e2e_x86_64_dispatcher --test e2e_x86_64_link --test e2e_x86_64_macho --test e2e_x86_64_windows_host_objects --test x86_64_constant_pool --test x86_64_external_call_relocations --test x86_64_imm8_encoding --test x86_64_sse2_dword_shifts --test x86_64_sse2_lane_encoding --test x86_64_target_features||
trust-cg-codegen|integration-macho|-p trust-cg-codegen --test e2e_macho_link --test e2e_macho_validation --test macho_integration --test e2e_native_link --test macho_fixup_error_integration --test o3_debug_lldb_line_200loc||
trust-cg-codegen|integration-elf-riscv|-p trust-cg-codegen --test e2e_elf_link --test e2e_riscv_elf||
trust-cg-codegen|integration-jit-runtime|-p trust-cg-codegen --test jit_calling_convention_contract --test jit_checked_overflow_intrinsics --test jit_cross_thread_execute_mode --test jit_forced_spill_post_ra_frame --test jit_integration --test jit_integration_x86_64 --test jit_sysv_x86_64_spill_replay --test jit_windows_raw_x86_64 --test jit_windows_x86_64 --test jit_windows_x86_64_fp_unary --test jit_x86_64_aggregate_abi_fail_closed --test jit_x86_64_profile_modes --test jit_mrs_tpidr --test jit_sparse_substitute_regression --test jit_tls --test jit_ay_pb_pbo_checked_arithmetic --test jit_ay_simplex_pivot --test jit_ay_widened_overflow_regression --test pgo_host_jit_runner --test v4i32_unsigned_compare_jit||
trust-cg-codegen|integration-jit-artifacts|-p trust-cg-codegen --test jit_contract_artifact --test jit_crash_replay --test jit_diagnostics --test jit_everywhere_control_plane --test jit_everywhere_nomination --test jit_everywhere_profile_cache --test jit_everywhere_shadow_replay --test jit_fail_closed_proof_policy --test jit_install_gate --test jit_no_handle_negative_fixtures --test jit_release_artifact --test jit_replay_bundle_consumer_fixture --test jit_ay_lra_status_abi||
trust-cg-codegen|integration-jit-observability|-p trust-cg-codegen --test jit_block_counter_lifetime --test jit_block_counters --test jit_block_counters_and_timing --test jit_entry_counters --test jit_explicit_extern_collision --test jit_profiling --test jit_proof_certs||
trust-cg-codegen|integration-pipeline|-p trust-cg-codegen --test e2e_pipeline --test e2e_pipeline_integration --test pipeline_integration --test e2e_full_pipeline --test e2e_opt_levels --test e2e_multiblock_builder||
trust-cg-codegen|integration-trust-ir|-p trust-cg-codegen --test trust_ir_aligned_pair_combine --test trust_ir_aligned_pair_production --test trust_ir_text_roundtrip --test xxh3_main_loop_trust_ir --test xxh3_medium_long_trust_ir --test xxh3_trust_ir||
trust-cg-codegen|integration-service-debug|-p trust-cg-codegen --test command_timeout --test compile_service_async_api --test dwarf_dwarfdump --test trust_cg_error_facade --test rewrite_admission||
trust-cg-codegen|integration-e2e-misc|-p trust-cg-codegen --test certified_pass_chain --test dialect_lower_module --test e2e_bridge --test e2e_cegis_superopt --test e2e_cli_json --test e2e_cli_tmbc --test e2e_correctness --test e2e_cse_movz_movn --test e2e_differential --test e2e_heterogeneous --test e2e_run --test e2e_stack_alloc --test e2e_triple_oracle --test metal_attention --test metal_bn_relu --test metal_conv_bn --test o3_ty_materialized_return --test ty_bfs_minimal||
trust-cg-codegen|integration-ty|-p trust-cg-codegen --test jit_ty_canary_allowlist --test ty_bfs_minimal_o1_o3_summary --test ty_callback_abi_call_clobber --test ty_edge_copy_loop_call --test ty_mcl_fused_parent_loop --test ty_native_bfs_no_action_parent_loop --test ty_reducer_evidence_packet --test ty_request_1_1_replay_bundle_reducer --test ty_runtime_value_replay_contract||
trust-cg-codegen|integration-fuzz|-p trust-cg-codegen --test panic_fuzz_compile --test panic_fuzz_compile_x86_64 --test panic_fuzz_encode --test panic_fuzz_encode_x86_64 --test panic_fuzz_macho_fixup||
trust-cg-codegen|integration-tmbc-misc|-p trust-cg-codegen --test o2_hang_diagnostic --test tmbc_canonical --test tmbc_roundtrip_prop||
trust-cg-codegen|integration-windows-coff|-p trust-cg-codegen --test x86_64_coff_constant_pool --test x86_64_coff_link_smoke||
trust-cg-codegen|integration-ay-contracts|-p trust-cg-codegen --test jit_ay_canary_allowlist --test x86_64_sysv_ay_abi --test ay_lra_manifest_contract --test ay_lra_runtime_value_replay --test ay_pb_pbo_checked_arithmetic_manifest_contract --test ay_sat_bcp_differential --test ay_sat_bcp_install_gate --test ay_sat_bcp_manifest_contract --test ay_sat_helper_replacement_differential --test ay_sat_helper_replacement_install_gate --test ay_sat_helper_replacement_manifest_contract||
EOF

# Keep the maintained matrix exhaustive as integration targets are added. The
# curated rows above preserve useful multi-target shards; every otherwise
# unassigned integration target receives its own bounded auto shard. The policy
# validator below still rejects unknown/stale explicit targets and verifies the
# resulting complete inventory.
if [ "${CHECK_RUSTC_BACKEND_ENV}" -eq 0 ]; then
    if ! command -v python3 >/dev/null 2>&1; then
        echo "run_full_test_matrix: python3 not found on PATH" >&2
        exit 1
    fi
    if ! AUTO_INTEGRATION_SHARDS="$(
        SHARD_PLAN_FOR_AUTO="${SHARD_PLAN}" python3 - "${REPO_ROOT}" <<'PYEOF'
import json
import os
import re
import shlex
import subprocess
import sys

repo_root = sys.argv[1]
plan = os.environ["SHARD_PLAN_FOR_AUTO"]
crate = "trust-cg-codegen"
target_selector_flags = {
    "--bench", "--benches", "--bin", "--bins", "--doc", "--example",
    "--examples", "--lib", "--test", "--tests",
}

assigned = set()
covered_by_default = False
for raw in plan.splitlines():
    if not raw.strip():
        continue
    parts = raw.split("|")
    if len(parts) < 3 or parts[0] != crate:
        continue
    args = shlex.split(parts[2])
    if "--all-targets" in args or "--tests" in args or not any(
        arg in target_selector_flags for arg in args
    ):
        covered_by_default = True
        break
    for index, arg in enumerate(args[:-1]):
        if arg == "--test":
            assigned.add(args[index + 1])

if covered_by_default:
    raise SystemExit(0)

metadata = subprocess.run(
    ["cargo", "metadata", "--locked", "--no-deps", "--format-version", "1"],
    cwd=repo_root,
    check=False,
    text=True,
    capture_output=True,
)
if metadata.returncode != 0:
    print(
        "run_full_test_matrix: cargo metadata failed while deriving auto shards",
        file=sys.stderr,
    )
    if metadata.stderr:
        print(metadata.stderr, file=sys.stderr, end="")
    raise SystemExit(1)

data = json.loads(metadata.stdout)
package = next(
    (item for item in data.get("packages", []) if item.get("name") == crate),
    None,
)
if package is None:
    print(f"run_full_test_matrix: metadata has no package {crate}", file=sys.stderr)
    raise SystemExit(1)

integration_targets = {
    target["name"]
    for target in package.get("targets", [])
    if "test" in target.get("kind", []) and target.get("test", True)
}
for name in sorted(integration_targets - assigned):
    if re.fullmatch(r"[A-Za-z0-9_-]+", name) is None:
        print(
            f"run_full_test_matrix: unsafe integration target name: {name!r}",
            file=sys.stderr,
        )
        raise SystemExit(1)
    print(
        f"{crate}|auto-{name}|-p {crate} --test {name}||"
        "Automatically assigned exhaustive integration target."
    )
PYEOF
    )"; then
        exit 1
    fi
    if [ -n "${AUTO_INTEGRATION_SHARDS}" ]; then
        SHARD_PLAN="${SHARD_PLAN}"$'\n'"${AUTO_INTEGRATION_SHARDS}"
    fi
fi

shard_matches_only() {
    local shard_crate="$1"
    local shard_name="$2"
    local shard_key="${shard_crate}|${shard_name}"

    if [ -z "${ONLY}" ]; then
        return 0
    fi

    if [ "${shard_key}" = "${ONLY}" ] ||
        [ "${shard_key}" = "${ONLY}|all" ] ||
        [ "${shard_key}" = "${shard_crate}|${ONLY}" ] ||
        [ "${shard_key}" = "${ONLY}|${shard_name}" ] ||
        [ "${shard_crate}" = "${ONLY}" ] ||
        [ "${shard_name}" = "${ONLY}" ]; then
        return 0
    fi

    return 1
}

selected_shard_count() {
    local selected=0
    local shard_crate=""
    local shard_name=""
    local shard_args=""
    local shard_post_args=""
    local shard_notes=""

    while IFS='|' read -r shard_crate shard_name shard_args shard_post_args shard_notes; do
        [ -z "${shard_crate}" ] && continue
        if shard_matches_only "${shard_crate}" "${shard_name}"; then
            selected=$((selected + 1))
        fi
    done <<< "${SHARD_PLAN}"

    echo "${selected}"
}

fail_no_shards_selected() {
    if [ -n "${ONLY}" ]; then
        echo "run_full_test_matrix: --only matched no shards: ${ONLY}" >&2
        echo "run_full_test_matrix: valid selectors are CRATE, SHARD, or CRATE|SHARD; use --dry-run to list them" >&2
    else
        echo "run_full_test_matrix: no shards selected" >&2
    fi
    exit 64
}

SELECTED_SHARDS="$(selected_shard_count)"
if [ "${SELECTED_SHARDS}" -eq 0 ]; then
    fail_no_shards_selected
fi

mkdir -p "${EVALS_DIR}"
mkdir -p "$(dirname "${OUT}")"

RUSTC_VERSION="$(rustc --version 2>/dev/null || echo 'unknown')"
COMMIT_SHA="$(git -C "${REPO_ROOT}" rev-parse HEAD 2>/dev/null || echo 'unknown')"
COMMIT_SHORT="$(git -C "${REPO_ROOT}" rev-parse --short HEAD 2>/dev/null || echo 'unknown')"
TIMEOUT_POLICY="isolated-process-group-term-kill"
LIBTEST_UNSTABLE_ARGS="-Z unstable-options --format json --report-time"
LIBTEST_OUTPUT_KIND="json"
if [ "${TRUST_CG_TEST_MATRIX_FORCE_JSON:-0}" != "1" ]; then
    case "${RUSTC_VERSION}" in
        *nightly*) ;;
        *)
            LIBTEST_UNSTABLE_ARGS=""
            LIBTEST_OUTPUT_KIND="plain"
            ;;
    esac
fi

if ! command -v python3 >/dev/null 2>&1; then
    echo "run_full_test_matrix: python3 not found on PATH" >&2
    exit 1
fi
if [ ! -x "${RUN_WITH_TIMEOUT}" ]; then
    echo "run_full_test_matrix: missing executable timeout runner ${RUN_WITH_TIMEOUT}" >&2
    exit 1
fi

rustc_backend_toolchain_field() {
    python3 - "$REPO_ROOT/crates/rustc-codegen-trust-cg/rust-toolchain.toml" "$1" <<'PYEOF'
from __future__ import annotations

import sys

path, field = sys.argv[1], sys.argv[2]

def parse_toolchain(path):
    try:
        import tomllib
    except ModuleNotFoundError:
        return parse_toolchain_fallback(path)

    try:
        with open(path, "rb") as fh:
            data = tomllib.load(fh)
    except (OSError, tomllib.TOMLDecodeError) as exc:
        print(f"run_full_test_matrix: failed to read {path}: {exc}", file=sys.stderr)
        raise SystemExit(1)

    toolchain = data.get("toolchain")
    if not isinstance(toolchain, dict):
        print(f"run_full_test_matrix: {path} has no [toolchain] table", file=sys.stderr)
        raise SystemExit(1)
    return toolchain


def parse_toolchain_fallback(path):
    in_toolchain = False
    toolchain = {}
    try:
        lines = open(path, encoding="utf-8").read().splitlines()
    except OSError as exc:
        print(f"run_full_test_matrix: failed to read {path}: {exc}", file=sys.stderr)
        raise SystemExit(1)
    for raw in lines:
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        if line.startswith("[") and line.endswith("]"):
            in_toolchain = line == "[toolchain]"
            continue
        if not in_toolchain or "=" not in line:
            continue
        key, value = [part.strip() for part in line.split("=", 1)]
        if key == "channel" and value.startswith('"') and value.endswith('"'):
            toolchain[key] = value[1:-1]
        elif key == "components" and value.startswith("[") and value.endswith("]"):
            items = []
            body = value[1:-1].strip()
            if body:
                for item in body.split(","):
                    item = item.strip()
                    if item.startswith('"') and item.endswith('"'):
                        items.append(item[1:-1])
                    else:
                        print(f"run_full_test_matrix: unsupported components entry in {path}: {item}", file=sys.stderr)
                        raise SystemExit(1)
            toolchain[key] = items
    if not toolchain:
        print(f"run_full_test_matrix: {path} has no parseable [toolchain] table", file=sys.stderr)
        raise SystemExit(1)
    return toolchain

try:
    toolchain = parse_toolchain(path)
except UnicodeDecodeError as exc:
    print(f"run_full_test_matrix: failed to decode {path}: {exc}", file=sys.stderr)
    raise SystemExit(1)

value = toolchain.get(field)
if field == "components":
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        print(f"run_full_test_matrix: {path} has no string-list toolchain.components", file=sys.stderr)
        raise SystemExit(1)
    print(" ".join(value))
elif field == "channel":
    if not isinstance(value, str) or not value:
        print(f"run_full_test_matrix: {path} has no string toolchain.channel", file=sys.stderr)
        raise SystemExit(1)
    print(value)
else:
    print(f"run_full_test_matrix: unsupported rustc backend toolchain field: {field}", file=sys.stderr)
    raise SystemExit(1)
PYEOF
}

check_rustc_backend_env() {
    local backend_manifest="${REPO_ROOT}/crates/rustc-codegen-trust-cg/Cargo.toml"
    local channel=""
    local components=""
    local sysroot=""
    local host=""
    local deps_dir=""
    local component=""
    local missing=0
    local probe_dir=""
    local probe_src=""
    local probe_bin=""

    channel="$(rustc_backend_toolchain_field channel)" || return 1
    components="$(rustc_backend_toolchain_field components)" || return 1

    echo "Rustc backend availability probe:"
    echo "  manifest: ${backend_manifest}"
    echo "  toolchain: ${channel}"
    echo "  required components: ${components}"

    if ! command -v rustup >/dev/null 2>&1; then
        echo "run_full_test_matrix: rustup not found; cannot verify pinned rustc-dev availability" >&2
        return 1
    fi

    if ! rustup run "${channel}" rustc --version >/dev/null 2>&1; then
        echo "run_full_test_matrix: missing rustup toolchain ${channel}" >&2
        echo "run_full_test_matrix: install with: rustup toolchain install ${channel} --profile minimal --component ${components// / --component }" >&2
        return 1
    fi

    for component in ${components}; do
        if ! rustup component list --toolchain "${channel}" --installed 2>/dev/null | grep -Eq "^${component}($|-| )"; then
            echo "run_full_test_matrix: missing ${component} for ${channel}" >&2
            missing=1
        fi
    done
    if [ "${missing}" -ne 0 ]; then
        echo "run_full_test_matrix: install missing components with: rustup component add --toolchain ${channel} ${components}" >&2
        return 1
    fi

    sysroot="$(rustup run "${channel}" rustc --print sysroot)" || return 1
    host="$(rustup run "${channel}" rustc -vV | awk '/^host: / { print $2 }')" || return 1
    deps_dir="${sysroot}/lib/rustlib/${host}/lib"
    if [ -z "${host}" ] || [ ! -d "${deps_dir}" ]; then
        echo "run_full_test_matrix: rustc-dev deps dir missing for ${channel}: ${deps_dir}" >&2
        return 1
    fi
    for component in rustc_middle rustc_codegen_ssa; do
        if ! find "${deps_dir}" -maxdepth 1 -name "lib${component}-*" -print -quit | grep -q .; then
            echo "run_full_test_matrix: rustc-dev private crate missing from ${deps_dir}: lib${component}-*" >&2
            missing=1
        fi
    done
    if [ "${missing}" -ne 0 ]; then
        return 1
    fi

    probe_dir="$(mktemp -d -t trust_cg_rustc_private_probe.XXXXXX)"
    probe_src="${probe_dir}/probe.rs"
    probe_bin="${probe_dir}/probe"
    trap 'rm -rf "${probe_dir}"' RETURN
    cat > "${probe_src}" <<'EOF'
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_middle;
extern crate rustc_session;

fn main() {
    let _ = core::mem::size_of::<Option<rustc_session::config::OptLevel>>();
}
EOF
    if ! rustup run "${channel}" rustc --crate-name trust_cg_rustc_private_probe "${probe_src}" -o "${probe_bin}" >/dev/null 2>&1; then
        echo "run_full_test_matrix: pinned toolchain exists but cannot compile a rustc_private probe" >&2
        echo "run_full_test_matrix: this blocks rustc_codegen_trust_cg CI even before backend correctness tests" >&2
        return 1
    fi
    rm -rf "${probe_dir}"
    trap - RETURN

    if ! CARGO_TARGET_DIR="${REPO_ROOT}/target/rustc-codegen-trust-cg-${channel}" \
        rustup run "${channel}" cargo build --manifest-path "${backend_manifest}" --release --locked; then
        echo "run_full_test_matrix: rustc_codegen_trust_cg release build failed under ${channel}" >&2
        echo "run_full_test_matrix: this blocks replacement because the rustc backend no longer builds against its pinned rustc_private API" >&2
        return 1
    fi

    echo "  rustc: $(rustup run "${channel}" rustc --version)"
    echo "  host: ${host}"
    echo "  sysroot: ${sysroot}"
    echo "  rustc_private deps: ${deps_dir}"
    echo "  backend release build: ${backend_manifest}"
    echo "Rustc backend availability probe: OK"
}

TEST_TIMEOUT_SECONDS="${TRUST_CG_TEST_MATRIX_TIMEOUT_SECONDS:-1500}"
if ! [[ "${TEST_TIMEOUT_SECONDS}" =~ ^[1-9][0-9]*$ ]]; then
    echo "run_full_test_matrix: TRUST_CG_TEST_MATRIX_TIMEOUT_SECONDS must be a positive integer" >&2
    exit 64
fi

validate_shard_policy() {
    SHARD_PLAN_FOR_POLICY="${SHARD_PLAN}" python3 - "${REPO_ROOT}" <<'PYEOF'
import json
import os
import subprocess
import sys

repo_root = sys.argv[1]
plan = os.environ["SHARD_PLAN_FOR_POLICY"]

# Approved exclusions are intentionally empty for #437: the default matrix is
# the workspace pass-count. If a future crate or integration test is excluded,
# document the issue number here and the policy check will enforce that entry.
APPROVED_WORKSPACE_EXCLUSIONS = set()
APPROVED_INTEGRATION_TEST_EXCLUSIONS = {}

shards = []
for lineno, raw in enumerate(plan.splitlines(), 1):
    line = raw.strip()
    if not line:
        continue
    parts = line.split("|")
    if len(parts) < 3:
        print(f"run_full_test_matrix: malformed shard-plan line {lineno}: {raw!r}", file=sys.stderr)
        sys.exit(1)
    crate, shard, cargo_args = parts[0], parts[1], parts[2]
    shards.append((crate, shard, cargo_args.split()))

metadata = subprocess.run(
    ["cargo", "metadata", "--locked", "--no-deps", "--format-version", "1"],
    cwd=repo_root,
    check=False,
    text=True,
    capture_output=True,
)
if metadata.returncode != 0:
    print("run_full_test_matrix: cargo metadata failed while checking shard policy", file=sys.stderr)
    if metadata.stderr:
        print(metadata.stderr, file=sys.stderr, end="")
    sys.exit(1)

data = json.loads(metadata.stdout)
workspace_ids = set(data.get("workspace_members", []))
packages = [p for p in data.get("packages", []) if p.get("id") in workspace_ids]
workspace_packages = {p["name"] for p in packages}
covered_packages = {crate for crate, _, _ in shards}

stale_package_exclusions = sorted(APPROVED_WORKSPACE_EXCLUSIONS - workspace_packages)
if stale_package_exclusions:
    print(
        "run_full_test_matrix: stale approved workspace exclusions: "
        + ", ".join(stale_package_exclusions),
        file=sys.stderr,
    )
    sys.exit(1)

missing_packages = sorted(workspace_packages - covered_packages - APPROVED_WORKSPACE_EXCLUSIONS)
if missing_packages:
    print(
        "run_full_test_matrix: shard policy missing workspace package(s): "
        + ", ".join(missing_packages),
        file=sys.stderr,
    )
    print(
        "Add each package to SHARD_PLAN or document it in APPROVED_WORKSPACE_EXCLUSIONS.",
        file=sys.stderr,
    )
    sys.exit(1)

known_packages = workspace_packages | APPROVED_WORKSPACE_EXCLUSIONS
unknown_packages = sorted(covered_packages - known_packages)
if unknown_packages:
    print(
        "run_full_test_matrix: shard plan names non-workspace package(s): "
        + ", ".join(unknown_packages),
        file=sys.stderr,
    )
    sys.exit(1)

target_selector_flags = {
    "--bench",
    "--benches",
    "--bin",
    "--bins",
    "--doc",
    "--example",
    "--examples",
    "--lib",
    "--test",
    "--tests",
}

def covers_default_test_targets(args):
    return "--all-targets" in args or not any(arg in target_selector_flags for arg in args)

def explicit_test_targets(args):
    names = []
    for idx, arg in enumerate(args[:-1]):
        if arg == "--test":
            names.append(args[idx + 1])
    return names

missing_tests = []
unknown_tests = []
stale_test_exclusions = []

for package in packages:
    crate = package["name"]
    crate_shards = [(shard, args) for shard_crate, shard, args in shards if shard_crate == crate]
    if not crate_shards:
        continue
    integration_targets = {
        target["name"]
        for target in package.get("targets", [])
        if "test" in target.get("kind", []) and target.get("test", True)
    }
    if not integration_targets:
        continue

    approved = set(APPROVED_INTEGRATION_TEST_EXCLUSIONS.get(crate, ()))
    stale = approved - integration_targets
    if stale:
        stale_test_exclusions.extend(f"{crate}/{name}" for name in sorted(stale))
    if any(covers_default_test_targets(args) or "--tests" in args for _, args in crate_shards):
        continue

    assigned = set()
    for _, args in crate_shards:
        assigned.update(explicit_test_targets(args))

    for name in sorted(integration_targets - assigned - approved):
        missing_tests.append(f"{crate}/{name}")
    for name in sorted(assigned - integration_targets):
        unknown_tests.append(f"{crate}/{name}")

if stale_test_exclusions:
    print(
        "run_full_test_matrix: stale approved integration-test exclusions: "
        + ", ".join(stale_test_exclusions),
        file=sys.stderr,
    )
    sys.exit(1)

if missing_tests:
    print(
        "run_full_test_matrix: shard policy missing integration test target(s): "
        + ", ".join(missing_tests),
        file=sys.stderr,
    )
    print(
        "Assign each target to SHARD_PLAN or document it in APPROVED_INTEGRATION_TEST_EXCLUSIONS.",
        file=sys.stderr,
    )
    sys.exit(1)

if unknown_tests:
    print(
        "run_full_test_matrix: shard plan names unknown integration test target(s): "
        + ", ".join(unknown_tests),
        file=sys.stderr,
    )
    sys.exit(1)

assigned_integration_tests = sum(
    1
    for crate, _, args in shards
    for _ in explicit_test_targets(args)
)
print(
    f"Shard policy OK: {len(workspace_packages)} workspace packages covered; "
    f"{assigned_integration_tests} explicit integration-test target assignments checked."
)
PYEOF
}

if [ "${CHECK_RUSTC_BACKEND_ENV}" -eq 1 ]; then
    check_rustc_backend_env
    exit $?
fi

validate_shard_policy || exit 1

# P1.1 opcode obligation/evidence inventory: accepted, explicitly deferred RED,
# pseudo/trap, and justified exclusion classifications are pinned exactly.
# Known named RED debt is allowed; unknown drift fails. Default evaluator-backed
# accepted records may be statistical and are NOT proofs. Cheap, no external solver needed; runs
# unconditionally (skip with TRUST_CG_COVERAGE_GATE=skip).
if [ "${DRY_RUN}" -eq 0 ] && [ "${TRUST_CG_COVERAGE_GATE:-auto}" != "skip" ]; then
    echo '>>> opcode-evidence-inventory (accepted obligation/evidence coverage; statistical default is not proof)'
    "${SCRIPT_DIR}/check_opcode_coverage_gate.sh" || exit 1
fi

# P0 proof gate: STRICT formal SMT discharge (no silent statistical downgrade).
# Runs only when a solver (ay/z3) is on PATH so the default local matrix is not
# blocked on a solver install; set TRUST_CG_PROOF_GATE=require to make absence a
# hard failure (the posture the CI solver lane should use).
if [ "${DRY_RUN}" -eq 0 ] && [ "${TRUST_CG_PROOF_GATE:-auto}" != "skip" ]; then
    if command -v z3 >/dev/null 2>&1 || command -v ay >/dev/null 2>&1 || [ -n "${AY_SOLVER_PATH:-}" ]; then
        echo '>>> proof-gate (strict formal SMT discharge)'
        "${SCRIPT_DIR}/check_proof_gate.sh" || exit 1
    elif [ "${TRUST_CG_PROOF_GATE:-auto}" = "require" ] || [ -n "${CI:-}" ] || [ -n "${GITHUB_ACTIONS:-}" ]; then
        # Fail closed in CI (or when explicitly required): a green matrix must not
        # silently omit the formal floor just because a solver wasn't installed.
        echo 'run_full_test_matrix: no ay/z3 solver on PATH and proof gate is required' >&2
        echo '  (CI detected or TRUST_CG_PROOF_GATE=require) — refusing to report success with' >&2
        echo '  the formal floor UN-RUN. Install z3/ay or unset CI to run the non-formal matrix.' >&2
        exit 1
    else
        # Local convenience only: loud, unmistakable warning so a solver-less run
        # is never mistaken for a green that includes the formal floor.
        echo '!!! run_full_test_matrix: no ay/z3 solver on PATH — STRICT PROOF GATE SKIPPED !!!' >&2
        echo '!!! This matrix run did NOT discharge the formal floor. Install z3/ay, or set      !!!' >&2
        echo '!!! TRUST_CG_PROOF_GATE=require, to enforce it. (Auto-enforced in CI.)             !!!' >&2
    fi
fi

if [ "${DRY_RUN}" -eq 1 ]; then
    echo "Shard plan (${TODAY}):"
    while IFS='|' read -r shard_crate shard_name shard_args shard_post_args shard_notes; do
        [ -z "${shard_crate}" ] && continue
        if ! shard_matches_only "${shard_crate}" "${shard_name}"; then
            continue
        fi
        printf "  %-14s %-20s scripts/run_with_timeout.py %s cargo test --locked %s --no-fail-fast" \
            "${shard_crate}" "${shard_name}" "${TEST_TIMEOUT_SECONDS}" "${shard_args}"
        if [ -n "${shard_post_args}" ]; then
            printf " -- %s" "${shard_post_args}"
        fi
        printf "\n"
    done <<< "${SHARD_PLAN}"
    echo
    echo "External validation probes:"
    echo "  rustc-codegen-trust-cg rustc-backend-env scripts/run_full_test_matrix.sh --check-rustc-backend-env"
    echo "    requires pinned nightly from crates/rustc-codegen-trust-cg/rust-toolchain.toml plus rustc-dev/rust-src/llvm-tools/rustfmt"
    echo "    release-builds crates/rustc-codegen-trust-cg against that pinned rustc_private API"
    echo "    not part of the default local stable workspace matrix; CI runs it in a dedicated rustc-dev lane"
    exit 0
fi

# Run each shard, capture libtest JSON output into a tempfile, parse it,
# collect per-shard totals. Sequential execution avoids competing Cargo jobs.

TMP_SHARDS_JSON="$(mktemp -t run_matrix.XXXXXX.json)"
trap 'rm -f "${TMP_SHARDS_JSON}"' EXIT

: > "${TMP_SHARDS_JSON}"

total_shards=0
failed_shards=0

while IFS='|' read -r shard_crate shard_name shard_args shard_post_args shard_notes; do
    [ -z "${shard_crate}" ] && continue

    if ! shard_matches_only "${shard_crate}" "${shard_name}"; then
        continue
    fi

    total_shards=$((total_shards + 1))
    echo ">>> ${shard_crate} / ${shard_name}"
    libtest_args="${LIBTEST_UNSTABLE_ARGS}"
    if [ -n "${shard_post_args}" ]; then
        libtest_args="${libtest_args} ${shard_post_args}"
    fi
    if [ -n "${libtest_args// /}" ]; then
        shard_command="scripts/run_with_timeout.py ${TEST_TIMEOUT_SECONDS} cargo test --locked ${shard_args} --no-fail-fast -- ${libtest_args}"
    else
        shard_command="scripts/run_with_timeout.py ${TEST_TIMEOUT_SECONDS} cargo test --locked ${shard_args} --no-fail-fast"
    fi
    echo "    ${shard_command}"

    start_ns="$(python3 -c 'import time;print(int(time.time()*1e9))')"
    shard_log="$(mktemp -t run_matrix_shard.XXXXXX.log)"

    # CARGO_SKIP_CACHE=1 remains set for compatibility with environments that
    # put a caching Cargo shim on PATH. A cache hit that omits stdout would make
    # the fail-closed parser report an incomplete shard.
    # shellcheck disable=SC2086
    if [ -n "${libtest_args// /}" ]; then
        CARGO_SKIP_CACHE=1 "${RUN_WITH_TIMEOUT}" "${TEST_TIMEOUT_SECONDS}" \
            cargo test --locked ${shard_args} --no-fail-fast -- ${libtest_args} \
            > "${shard_log}" 2>&1
    else
        CARGO_SKIP_CACHE=1 "${RUN_WITH_TIMEOUT}" "${TEST_TIMEOUT_SECONDS}" \
            cargo test --locked ${shard_args} --no-fail-fast \
            > "${shard_log}" 2>&1
    fi
    shard_rc=$?
    end_ns="$(python3 -c 'import time;print(int(time.time()*1e9))')"
    dt="$(python3 -c "print((${end_ns}-${start_ns})/1e9)")"
    keeper=""
    if [ "${shard_rc}" -ne 0 ]; then
        keeper="${EVALS_DIR}/${TODAY}.${shard_crate}.${shard_name}.log"
    fi

    # Parse the log. libtest emits one JSON object per line mixed with build
    # output; non-JSON lines are ignored. A "suite" event with event=ok/failed
    # carries the roll-up counts we want.
    #
    # We also track which suite is a doc-test suite vs. a regular one.
    # `cargo test` emits a non-JSON header line `   Doc-tests <crate>` before
    # the doc-test suite, and `     Running tests/X.rs ...` before integration
    # suites. Tests marked rustdoc ```ignore show up as `ignored` in the
    # doc-test suite rather than as #[ignore] attributes. We record both
    # categories separately so the summary can reject either category while
    # retaining precise diagnostics.
    if ! python3 - "${shard_crate}" "${shard_name}" "${shard_log}" "${dt}" "${shard_rc}" \
        "${shard_notes}" "${shard_args}" "${shard_post_args}" "${shard_command}" \
        "${TEST_TIMEOUT_SECONDS}" "${TIMEOUT_POLICY}" "${keeper}" "${LIBTEST_OUTPUT_KIND}" <<'PYEOF' >> "${TMP_SHARDS_JSON}"
import json, re, shlex, sys

(
    crate,
    shard,
    log_path,
    dt,
    rc,
    notes,
    cargo_args,
    shard_post_args,
    shard_command,
    timeout_budget_sec,
    timeout_policy,
    combined_log,
    libtest_output_kind,
) = sys.argv[1:]
dt = float(dt); rc = int(rc)
timeout_budget_sec = int(timeout_budget_sec)


def split_args(text):
    return shlex.split(text) if text else []


def feature_set(cargo_args):
    args = split_args(cargo_args)
    features = []
    for idx, arg in enumerate(args):
        value = None
        if arg == "--features" and idx + 1 < len(args):
            value = args[idx + 1]
        elif arg.startswith("--features="):
            value = arg.split("=", 1)[1]
        if value:
            features.extend(part for part in value.replace(",", " ").split() if part)
    return sorted(set(features))


def input_identifiers(crate, shard, cargo_args):
    args = split_args(cargo_args)
    test_targets = []
    selectors = []
    selector_flags = {"--lib", "--tests", "--doc", "--all-targets"}
    for idx, arg in enumerate(args):
        if arg in selector_flags:
            selectors.append(arg)
        elif arg == "--test" and idx + 1 < len(args):
            test_targets.append(args[idx + 1])
        elif arg.startswith("--test="):
            test_targets.append(arg.split("=", 1)[1])
    return {
        "crate": crate,
        "shard": shard,
        "selectors": selectors,
        "test_targets": test_targets,
    }


def classify_status(rc, suites, failed, timed_out, parse_errors):
    if timed_out:
        return "timeout"
    if parse_errors:
        return "incomplete"
    if suites == 0:
        return "skipped" if rc == 0 else "incomplete"
    if rc != 0 and failed == 0:
        return "incomplete"
    if failed > 0 or rc != 0:
        return "fail"
    return "pass"

passed = failed = ignored = filtered = suites = 0
doc_ignored = 0
test_ignored = 0
parse_errors = 0
in_doc_tests = False
timeout_marker = False
# Partial-suite counters track individual test events when a suite's rollup
# event never emitted (e.g. cargo wrapper killed the process before the
# suite finished). They are only used as a fallback.
partial_passed = partial_failed = partial_ignored = 0
partial_doc_ignored = partial_test_ignored = 0
pending_suite_started = False   # a `suite started` line without a matching `suite ok/failed`
with open(log_path, encoding="utf-8", errors="replace") as fh:
    for raw in fh:
        line = raw.strip()
        if "[cargo] ERROR: Command timed out" in line or (
            "[trust-cg-timeout] ERROR: Command timed out" in line
        ) or (
            "timed out after" in line and "(timeout=" in line and "killing process group" in line
        ) or (
            "run_with_timeout: command exceeded " in line
        ):
            timeout_marker = True
        # Section markers from cargo's cargo_test output (before each suite).
        if line.startswith("Doc-tests "):
            in_doc_tests = True
            continue
        if line.startswith("Running "):
            in_doc_tests = False
            continue
        plain_result = re.match(
            r"test result: \S+\. (\d+) passed; (\d+) failed; "
            r"(\d+) ignored; \d+ measured; (\d+) filtered out;",
            line,
        )
        if plain_result:
            suite_passed, suite_failed, suite_ignored, suite_filtered = (
                int(part) for part in plain_result.groups()
            )
            passed += suite_passed
            failed += suite_failed
            ignored += suite_ignored
            filtered += suite_filtered
            if in_doc_tests:
                doc_ignored += suite_ignored
            else:
                test_ignored += suite_ignored
            suites += 1
            pending_suite_started = False
            partial_passed = partial_failed = partial_ignored = 0
            partial_doc_ignored = partial_test_ignored = 0
            continue
        if not line.startswith("{"):
            continue
        try:
            obj = json.loads(line)
        except Exception:
            parse_errors += 1
            continue
        obj_type = obj.get("type")
        event = obj.get("event")
        if obj_type == "suite":
            if event == "started":
                pending_suite_started = True
                continue
            if event in ("ok", "failed"):
                suite_passed = int(obj.get("passed", 0))
                suite_failed = int(obj.get("failed", 0))
                suite_ignored = int(obj.get("ignored", 0))
                suite_filtered = int(obj.get("filtered_out", 0))
                passed += suite_passed
                failed += suite_failed
                ignored += suite_ignored
                filtered += suite_filtered
                if in_doc_tests:
                    doc_ignored += suite_ignored
                else:
                    test_ignored += suite_ignored
                suites += 1
                pending_suite_started = False
                # Drop partials accumulated for this completed suite.
                partial_passed = partial_failed = partial_ignored = 0
                partial_doc_ignored = partial_test_ignored = 0
            continue
        if obj_type == "test" and pending_suite_started:
            if event == "ok":
                partial_passed += 1
            elif event == "failed":
                partial_failed += 1
            elif event == "ignored":
                partial_ignored += 1
                if in_doc_tests:
                    partial_doc_ignored += 1
                else:
                    partial_test_ignored += 1

# If a suite got killed mid-run (no `suite ok/failed` for the last
# `suite started`), fold its per-test counts in so we don't lose data.
partial_note = None
if pending_suite_started and (partial_passed or partial_failed or partial_ignored):
    passed += partial_passed
    failed += partial_failed
    ignored += partial_ignored
    test_ignored += partial_test_ignored
    doc_ignored += partial_doc_ignored
    suites += 1
    partial_note = (
        f"partial suite: {partial_passed} pass / {partial_failed} fail from individual test events "
        "(suite roll-up missing, likely process-group timeout)"
    )

# If we got zero suites but rc != 0, the run failed to produce JSON at all
# (compile error, linker error, timeout, etc.). Record as a single logical
# failure so the ratchet can catch it, with a note pointing at the log.
note_out = notes
if partial_note:
    note_out = (note_out + "; " if note_out else "") + partial_note
if parse_errors:
    note_out = (note_out + "; " if note_out else "") + (
        f"{parse_errors} malformed libtest JSON line(s)"
    )
if suites == 0:
    if rc != 0:
        failed += 1
        note_out = (note_out + "; " if note_out else "") + f"no suites parsed; cargo rc={rc}; see log"
    else:
        note_out = (note_out + "; " if note_out else "") + "no tests produced suite events"
timed_out = rc == 124 or timeout_marker
if timed_out and "timeout" not in note_out.lower():
    note_out = (note_out + "; " if note_out else "") + (
        f"timeout after {timeout_budget_sec}s; see log"
    )
status = classify_status(rc, suites, failed, timed_out, parse_errors)

print(json.dumps({
    "crate": crate, "shard": shard,
    "passed": passed, "failed": failed, "ignored": ignored, "filtered": filtered,
    "doc_ignored": doc_ignored, "test_ignored": test_ignored,
    "suites": suites, "time_s": round(dt, 3),
    "status": status,
    "timeout_policy": timeout_policy,
    "timeout_budget_sec": timeout_budget_sec,
    "timeout_detected": timed_out,
    "libtest_output": libtest_output_kind,
    "command": shard_command,
    "feature_set": feature_set(cargo_args),
    "input_identifiers": input_identifiers(crate, shard, cargo_args),
    "combined_log": combined_log or None,
    "rc": rc, "notes": note_out,
}))
PYEOF
    then
        keeper="${EVALS_DIR}/${TODAY}.${shard_crate}.${shard_name}.log"
        mv "${shard_log}" "${keeper}"
        echo "run_full_test_matrix: failed to parse ${shard_crate}/${shard_name}; kept log: ${keeper}" >&2
        exit 1
    fi

    if [ "${shard_rc}" -ne 0 ]; then
        failed_shards=$((failed_shards + 1))
        echo "    shard returned rc=${shard_rc} (test failures are recorded in JSON)"
    fi
    # Log is kept around only if the run failed, for post-mortem.
    if [ "${shard_rc}" -eq 0 ]; then
        rm -f "${shard_log}"
    else
        mv "${shard_log}" "${keeper}"
        echo "    kept shard log: ${keeper}"
    fi
done <<< "${SHARD_PLAN}"

if [ "${total_shards}" -eq 0 ]; then
    fail_no_shards_selected
fi

# Aggregate shard JSON lines into the final output.
if ! python3 - "${TMP_SHARDS_JSON}" "${OUT}" "${TODAY}" "${COMMIT_SHA}" "${COMMIT_SHORT}" "${RUSTC_VERSION}" "${total_shards}" <<'PYEOF'
import json, sys
shards_path, out_path, date, commit, commit_short, rustc, expected_shards = sys.argv[1:]
expected_shards = int(expected_shards)

shards = []
with open(shards_path) as fh:
    for line in fh:
        line = line.strip()
        if not line:
            continue
        shards.append(json.loads(line))

if len(shards) != expected_shards:
    raise SystemExit(
        f"run_full_test_matrix: parsed {len(shards)} shard row(s), "
        f"expected {expected_shards}"
    )
identities = [(shard.get("crate"), shard.get("shard")) for shard in shards]
if any(not crate or not name for crate, name in identities):
    raise SystemExit("run_full_test_matrix: aggregate contains an unidentified shard")
if len(set(identities)) != len(identities):
    raise SystemExit("run_full_test_matrix: aggregate contains duplicate shard identities")

OUTCOME_ORDER = ("pass", "fail", "skipped", "timeout", "incomplete")
outcome_counts = {name: 0 for name in OUTCOME_ORDER}
for shard in shards:
    status = shard.get("status") or ("fail" if shard.get("failed", 0) else "pass")
    if status not in outcome_counts:
        status = "incomplete"
    outcome_counts[status] += 1

totals = {
    "passed": sum(s["passed"] for s in shards),
    "failed": sum(s["failed"] for s in shards),
    "ignored": sum(s["ignored"] for s in shards),
    "doc_ignored": sum(s.get("doc_ignored", 0) for s in shards),
    "test_ignored": sum(s.get("test_ignored", 0) for s in shards),
    "filtered": sum(s["filtered"] for s in shards),
    "suites": sum(s.get("suites", 0) for s in shards),
    "outcome_counts": outcome_counts,
    "time_s": round(sum(s["time_s"] for s in shards), 3),
}

out = {
    "schema": "trust-cg.test-matrix.v1",
    "date": date,
    "commit": commit,
    "commit_short": commit_short,
    "rustc": rustc,
    "shards": shards,
    "totals": totals,
}
with open(out_path, "w") as fh:
    json.dump(out, fh, indent=2, sort_keys=False)
    fh.write("\n")

print()
print(f"Wrote {out_path}")
print(f"  shards: {len(shards)}")
print(f"  passed: {totals['passed']}")
print(f"  failed: {totals['failed']}")
print(f"  ignored: {totals['ignored']}")
print(f"  filtered: {totals['filtered']}")
print("  outcomes: " + ", ".join(f"{name}={outcome_counts[name]}" for name in OUTCOME_ORDER))
print(f"  time_s: {totals['time_s']}")
PYEOF
then
    echo "run_full_test_matrix: failed to aggregate shard results" >&2
    exit 1
fi

if ! NONPASS_OUTCOMES="$(python3 - "${OUT}" <<'PYEOF'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as handle:
    report = json.load(handle)
outcomes = report["totals"]["outcome_counts"]
print(sum(count for name, count in outcomes.items() if name != "pass"))
PYEOF
)"; then
    echo "run_full_test_matrix: failed to read aggregate outcome counts" >&2
    exit 1
fi

echo
echo "Done. ${total_shards} shards run, ${failed_shards} with non-zero exit."
if [ "${failed_shards}" -ne 0 ] || [ "${NONPASS_OUTCOMES}" -ne 0 ]; then
    if [ "${REPORT_ONLY}" -eq 1 ]; then
        echo "run_full_test_matrix: non-green outcomes retained in report-only mode"
        exit 0
    fi
    echo "run_full_test_matrix: matrix is non-green; see ${OUT}" >&2
    exit 1
fi
exit 0
