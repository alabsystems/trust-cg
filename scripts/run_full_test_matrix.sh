#!/usr/bin/env bash
# scripts/run_full_test_matrix.sh
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Issue:  Part of #437 (WS1 — Measured workspace pass-count)
#
# Runs `scripts/trust_cargo.sh test` (targo --unverified) per workspace crate
# with `--no-fail-fast` and captures libtest output. Nightly toolchains use
# JSON; stable toolchains use the named text results. Both use --show-output so
# observed runtime SKIPs are not counted as passes. Every shard runs in an
# isolated process group with a finite wall-clock bound.
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
#           "libtest_passed": N, "runtime_skipped": N, "unclassified_passes": N,
#           "status": "pass|fail|skipped|timeout|incomplete",
#           "time_s": F, "suites": N, "notes": "..." }
#       ],
#       "totals": { "passed": ..., "failed": ..., "ignored": ..., "filtered": ...,
#                   "outcome_counts": {"pass": N, "fail": N, "skipped": N,
#                                      "timeout": N, "incomplete": N},
#                   "time_s": ... },
#       "proof_gate": { "mode": "...", "result": "..." },
#       "bench_stage": { "mode": "auto|required|skipped|targeted", "result": "...",
#                        "landing_checks_rc": N|null, "qualifying": true|false }
#     }
#
# Usage:
#   scripts/run_full_test_matrix.sh                # write evals/results/tests/<today>.json
#   scripts/run_full_test_matrix.sh --out FILE     # write to a specific path
#   scripts/run_full_test_matrix.sh --dry-run      # print the selected shard plan only
#   scripts/run_full_test_matrix.sh --only SELECTOR # run one crate, shard, or CRATE|SHARD
#   scripts/run_full_test_matrix.sh --report-only  # always exit 0 after writing a complete report
#   scripts/run_full_test_matrix.sh --check-rustc-backend-env
#       # require the selected rustc_codegen_trust_cg compiler + development components,
#       # then release-build the rustc private backend crate with `targo --unverified`
#
# Exit codes:
#   0 — every selected shard passed (or explicit --report-only)
#   1 — a test/shard failed, timed out, was skipped/incomplete, or tooling failed;
#       or a REQUIRED bench stage (TRUST_CG_REQUIRE_BENCH=1) was skipped, not
#       runnable, or non-green
#   64 — invalid CLI args, --only selector, or TRUST_CG_REQUIRE_BENCH value
#
# `--report-only` preserves the historical measurement behavior by returning 0
# after a complete report even when a shard is non-green. Without that explicit
# option the matrix is fail-closed. The plan is validated against the current
# Cargo metadata, so newly added packages or integration targets cannot remain
# outside the measured denominator. README.md and LIMITATIONS.md define how to
# interpret the resulting coverage numbers.
#
# This census runs every suite on one host, so it is non-green on any single
# host by construction (Linux-only suites compile empty on Darwin; macOS-guarded
# suites print skips on Linux). The per-host required sets of the same
# denominator are scripts/full_test_matrix_hosts.py; the Darwin set's runner is
# scripts/run_darwin_full_test_matrix.py (docs/testing/full-test-matrix.md).

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

# Every shard runs on the installed Trust package (rust-toolchain.toml
# `channel = "trust"`; owner directive 2026-09-28) through
# scripts/trust_cargo.sh; no stock rustup/~/.cargo/bin directory is prepended.
export PATH

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
RUN_WITH_TIMEOUT="${SCRIPT_DIR}/run_with_timeout.py"
MATRIX_RESULTS="${SCRIPT_DIR}/matrix_results.py"
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
            sed -n '2,45p' "$0" | sed 's/^# \{0,1\}//'
            exit 0 ;;
        *)
            usage_error "unknown arg: $1" ;;
    esac
done

if [ "${ONLY_SET}" -eq 1 ] && [ -z "${ONLY}" ]; then
    usage_error "--only requires a non-empty selector"
fi

# Captured, named stdout is required to distinguish runtime SKIPs from passes.
# Do not silently sanitize a caller's incompatible libtest setting.
if [ "${CHECK_RUSTC_BACKEND_ENV}" -eq 0 ] && [ "${RUST_TEST_NOCAPTURE-0}" != 0 ]; then
    usage_error "RUST_TEST_NOCAPTURE must be unset or 0; the matrix requires captured --show-output"
fi

# Some verifier proof tests recurse deeply enough to overflow the default
# libtest thread stack in debug builds. Keep this override local to the matrix
# runner; callers can still raise/lower it explicitly.
: "${RUST_MIN_STACK:=67108864}"
export RUST_MIN_STACK

# Keep the large-stack proof and generated-code tests from running concurrently
# by default. An explicit caller setting still wins.
: "${RUST_TEST_THREADS:=1}"
export RUST_TEST_THREADS

# --- BENCH-10 measurement (bench) stage --------------------------------------
# Wire the BENCH measurement gates into the existing local-gate cadence (the
# project's no-GitHub-CI stance, SOUNDNESS_CHECK.md): every plain full-matrix
# run also evaluates the compile-time canary + perf ratchet + determinism sentinel
# + predecessor soundness attestation via the single entry point
# scripts/landing_checks.sh.
#
#   - runs ONLY on a plain full invocation; --dry-run / --only /
#     --check-rustc-backend-env are targeted or introspection modes and record
#     the stage as "targeted"/"not-run";
#   - REQUIRED only when TRUST_CG_REQUIRE_BENCH=1: TCG_SKIP_BENCH_STAGE=1 is
#     refused, --only is refused because it cannot run the stage,
#     landing_checks.sh runs with --require-current-perf, and any non-green
#     result (including missing evidence) stops the matrix before its shards run;
#   - otherwise NON-FATAL: the verdict is surfaced and the matrix continues to
#     the test shards, so a load-noisy bench result never becomes a false shard
#     failure. TCG_SKIP_BENCH_STAGE=1 skips it loudly.
# TRUST_CG_PROOF_GATE=require does not make this stage required: performance
# measurements are not proof evidence, and the stage needs a built bridge backend
# and a quiet host, which the formal gate does not.
# Every report records the stage in its bench_stage marker, and only a green
# stage is qualifying. Runner controls are removed from the stage environment
# because they are not compiler controls.
case "${TRUST_CG_REQUIRE_BENCH:-0}" in
    0|1) ;;
    *) usage_error "TRUST_CG_REQUIRE_BENCH must be 0 or 1, not '${TRUST_CG_REQUIRE_BENCH}'" ;;
esac
BENCH_STAGE_REQUIRED=0
if [ "${TRUST_CG_REQUIRE_BENCH:-0}" = 1 ]; then
    BENCH_STAGE_REQUIRED=1
fi
BENCH_STAGE_MODE="targeted"
BENCH_STAGE_RESULT="not-run"
BENCH_STAGE_RC=""
if [ "${DRY_RUN}" -eq 0 ] && [ "${ONLY_SET}" -eq 1 ] && [ "${BENCH_STAGE_REQUIRED}" -eq 1 ]; then
    echo "run_full_test_matrix: TRUST_CG_REQUIRE_BENCH=1 needs a plain full run; --only cannot run the bench stage" >&2
    exit 1
fi
if [ "${DRY_RUN}" -eq 0 ] && [ "${ONLY_SET}" -eq 0 ] && [ "${CHECK_RUSTC_BACKEND_ENV}" -eq 0 ]; then
    if [ "${TCG_SKIP_BENCH_STAGE:-0}" = 1 ]; then
        if [ "${BENCH_STAGE_REQUIRED}" -eq 1 ]; then
            echo "run_full_test_matrix: bench stage is REQUIRED (TRUST_CG_REQUIRE_BENCH=1); refusing TCG_SKIP_BENCH_STAGE=1" >&2
            exit 1
        fi
        BENCH_STAGE_MODE="skipped"
        BENCH_STAGE_RESULT="skipped-non-qualifying"
        echo "!!! run_full_test_matrix: bench stage SKIPPED (TCG_SKIP_BENCH_STAGE=1) — this report is NON-QUALIFYING for the measurement gates !!!" >&2
    else
        BENCH_STAGE_MODE="auto"
        bench_flag=""
        if [ "${BENCH_STAGE_REQUIRED}" -eq 1 ]; then
            BENCH_STAGE_MODE="required"
            bench_flag="--require-current-perf"
        fi
        echo "=== bench stage (BENCH-10, ${BENCH_STAGE_MODE}): scripts/landing_checks.sh ${bench_flag} ==="
        env -u TRUST_CG_PROOF_GATE -u TRUST_CG_COVERAGE_GATE -u TRUST_CG_TEST_MATRIX_FORCE_JSON \
            -u TRUST_CG_TEST_MATRIX_TIMEOUT_SECONDS -u TCG_SKIP_BENCH_STAGE -u TRUST_CG_REQUIRE_BENCH \
            "${SCRIPT_DIR}/landing_checks.sh" ${bench_flag:+"${bench_flag}"}
        BENCH_STAGE_RC=$?
        case "${BENCH_STAGE_RC}" in
            0) BENCH_STAGE_RESULT="green" ;;
            1) BENCH_STAGE_RESULT="red" ;;
            2) BENCH_STAGE_RESULT="inconclusive" ;;
            3) BENCH_STAGE_RESULT="missing-evidence" ;;
            *) BENCH_STAGE_RESULT="error" ;;
        esac
        if [ "${BENCH_STAGE_RC}" -eq 0 ]; then
            echo "run_full_test_matrix: bench stage GREEN"
        elif [ "${BENCH_STAGE_REQUIRED}" -eq 1 ]; then
            echo "run_full_test_matrix: REQUIRED bench stage is ${BENCH_STAGE_RESULT} (rc=${BENCH_STAGE_RC}); refusing to report this matrix run" >&2
            exit 1
        else
            echo "run_full_test_matrix: bench stage NON-GREEN: ${BENCH_STAGE_RESULT} (rc=${BENCH_STAGE_RC}: 1=regression/MISMATCH, 2=tooling/loaded, 3=missing evidence) — recorded as non-qualifying, not fatal to the test matrix; investigate before landing" >&2
        fi
        echo "=== end bench stage ==="
    fi
fi

# --- Shard plan ---------------------------------------------------------------
#
# Each line:  <crate>|<shard-name>|<cargo-args>|<notes>
#
# cargo-args is everything that goes after `scripts/trust_cargo.sh test`. The script appends
# `--no-fail-fast` and captured `--show-output`; nightly also uses JSON/report-time.
#
# For trust-cg-codegen, we shard by test binary (`--lib` + per-integration-group
# via `--test <file>`). Integration tests are independent binaries so a
# single `scripts/trust_cargo.sh test --test X` builds and runs just that binary.
#
# Policy: every Cargo workspace package must be present in this plan unless it
# is listed as an approved exclusion in validate_shard_policy(). For crates
# sharded with explicit `--test` selectors, every integration-test target must
# be assigned to a shard unless it is explicitly excluded there.

# Format: <crate>|<shard-name>|<cargo-args>|<libtest-post-args>|<notes>
# * cargo-args: goes after `scripts/trust_cargo.sh test`, before `--`.
# * libtest-post-args: goes after `--`, after any nightly JSON/report-time flags.
#   Use this for `--skip <prefix>` or other libtest flags.
read -r -d '' SHARD_PLAN <<'EOF' || true
trust-cg-ir|all|-p trust-cg-ir||
trust-cg-dialect|all|-p trust-cg-dialect||
trust-cg-lower|all|-p trust-cg-lower||
trust-cg-opt|all|-p trust-cg-opt||
trust-cg-irmid|all|-p trust-cg-irmid||
trust-cg-eqsat|all|-p trust-cg-eqsat||
trust-cg-eqsat-check|all|-p trust-cg-eqsat-check||
trust-cg-lift|all|-p trust-cg-lift||
trust-cg-regalloc|all|-p trust-cg-regalloc||
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
trust-cg-verify|lib-synthesis|-p trust-cg-verify --lib|cegis:: cegis_pass:: rule_discovery:: proof_database:: proof_certificate:: function_verifier::|Synthesis / CEGIS / proof-database — medium-weight.
trust-cg-verify|lib-neon-vec|-p trust-cg-verify --lib|neon_encoding_proofs:: neon_lowering_proofs:: vectorization_proofs::|NEON encoding / lowering / vectorization proofs (each ~60-75s).
trust-cg-verify|lib-live-ay|-p trust-cg-verify --lib --features live-ay|ay_bridge::tests::test_ay_batch_verify_|The live-AY batch group (TRUSTCG-21): whole proof categories through the external AY solver, one obligation at a time; ignored without the live-ay feature.
trust-cg-verify|lib-other|-p trust-cg-verify --lib|--skip ay_bridge::tests::test_ay_batch_verify_ --skip verification_runner:: --skip memory_proofs:: --skip atomic_proofs:: --skip addr_mode_proofs:: --skip cegis:: --skip cegis_pass:: --skip rule_discovery:: --skip proof_database:: --skip proof_certificate:: --skip function_verifier:: --skip neon_encoding_proofs:: --skip neon_lowering_proofs:: --skip vectorization_proofs::|Everything else in the trust-cg-verify library (arithmetic, peephole, CFG, DCE, GVN, LICM, and related modules).
trust-cg-verify|integration|-p trust-cg-verify --tests|--skip ay_bridge::tests::test_ay_batch_verify_|All integration targets under crates/trust-cg-verify/tests/ that need no feature (--tests also runs the library's unit tests, so it filters out the lib-live-ay group rather than count it ignored); Cargo metadata and validate_shard_policy keep the denominator complete.
trust-cg-verify|integration-core-byte-store|-p trust-cg-verify --features core-byte-replay --test core_byte_store||Requires core-byte-replay (TRUSTCG-20); its own shard because the ByteV1 replay is minutes long.
trust-cg-verify|integration-core-byte-writer|-p trust-cg-verify --features core-byte-replay --test core_byte_writer||Requires core-byte-replay (TRUSTCG-20); its own shard because the ByteV1 replay is minutes long.
trust-cg-cli|all|-p trust-cg-cli||
trust-cg-codegen|lib|-p trust-cg-codegen --lib||
trust-cg-codegen|integration-aarch64|-p trust-cg-codegen --test aarch64_encoding --test aarch64_incoming_arg_zero_offset_load --test aarch64_msub_mneg_encode --test aarch64_petri_o2_o3_incoming_arg_canary --test aarch64_framed_identity_control --test aarch64_nonleaf_frame_control --test compact_unwind_integration --test e2e_aarch64_link||
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

# trustc refuses to run under any TRUST_CG_*/TCG_* control; probe without them.
trust_env() {
    local unset_args=() name
    while IFS= read -r name; do
        case "${name}" in TRUST_CG_* | TCG_*) unset_args+=(-u "${name}") ;; esac
    done < <(compgen -e)
    env ${unset_args[@]+"${unset_args[@]}"} "$@"
}

# The Trust package this runner's own probes run: the one the shards build
# with. scripts/trust_cargo.sh builds with $TRUST_TARGO when set (an absolute
# path) and otherwise with the package scripts/trust_toolchain.py resolves from
# PATH for the `workspace` purpose. The auto-shard census and the shard-policy
# check (the denominator), the recorded compiler version (which also picks the
# libtest format) and the proof-gate hint run that package's own files, never a
# PATH `targo` or `trustc`: either may be an atpkg launcher shim whose shell
# prelude the resolver reads but never runs (DR-ATPKG-PRELUDE-SHIM-20261015),
# and no verdict here may rest on what such a prelude prints.
# --check-rustc-backend-env resolves its own (bridge) package below.
MATRIX_TARGO=""
MATRIX_TRUSTC=""
MATRIX_TRUST_SYSROOT=""
if [ "${CHECK_RUSTC_BACKEND_ENV}" -eq 0 ]; then
    if ! command -v python3 >/dev/null 2>&1; then
        echo "run_full_test_matrix: python3 not found on PATH" >&2
        exit 1
    fi
    if [ -n "${TRUST_TARGO:-}" ]; then
        case "${TRUST_TARGO}" in
            /*) ;;
            *)
                echo "run_full_test_matrix: TRUST_TARGO must be an absolute path, got '${TRUST_TARGO}'" >&2
                exit 1
                ;;
        esac
        if [ ! -x "${TRUST_TARGO}" ]; then
            echo "run_full_test_matrix: TRUST_TARGO is not executable: ${TRUST_TARGO}" >&2
            exit 1
        fi
        MATRIX_TARGO="${TRUST_TARGO}"
        MATRIX_TRUSTC="$(dirname "${TRUST_TARGO}")/trustc"
        if [ -x "${MATRIX_TRUSTC}" ]; then
            MATRIX_TRUST_SYSROOT="$(trust_env "${MATRIX_TRUSTC}" --print sysroot 2>/dev/null)" || MATRIX_TRUST_SYSROOT=""
        else
            MATRIX_TRUSTC=""
        fi
    else
        if ! matrix_trust_record="$(trust_env python3 -B "${SCRIPT_DIR}/trust_toolchain.py" --purpose workspace --print json)"; then
            echo "run_full_test_matrix: no installed Trust toolchain resolves (scripts/trust_toolchain.py); there is no stock fallback" >&2
            exit 1
        fi
        if ! matrix_trust_tools="$(printf '%s' "${matrix_trust_record}" | python3 -c '
import json, sys
record = json.load(sys.stdin)
for key in ("targo", "compiler", "sysroot"):
    value = record.get(key)
    if not isinstance(value, str) or not value.startswith("/") or "\n" in value:
        sys.exit(f"run_full_test_matrix: scripts/trust_toolchain.py names no absolute {key}")
    print(value)
')"; then
            exit 1
        fi
        {
            IFS= read -r MATRIX_TARGO
            IFS= read -r MATRIX_TRUSTC
            IFS= read -r MATRIX_TRUST_SYSROOT
        } <<< "${matrix_trust_tools}"
    fi
fi

# Keep the maintained matrix exhaustive as integration targets are added. The
# curated rows above preserve useful multi-target shards; every otherwise
# unassigned integration target receives its own bounded auto shard. The policy
# validator below still rejects unknown/stale explicit targets and verifies the
# resulting complete inventory.
if [ "${CHECK_RUSTC_BACKEND_ENV}" -eq 0 ]; then
    if ! AUTO_INTEGRATION_SHARDS="$(
        SHARD_PLAN_FOR_AUTO="${SHARD_PLAN}" python3 - "${REPO_ROOT}" "${MATRIX_TARGO}" <<'PYEOF'
import json
import os
import re
import shlex
import subprocess
import sys

repo_root = sys.argv[1]
targo = sys.argv[2]
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
    [targo, "metadata", "--locked", "--no-deps", "--format-version", "1"],
    cwd=repo_root,
    check=False,
    text=True,
    capture_output=True,
)
if metadata.returncode != 0:
    print(
        f"run_full_test_matrix: {targo} metadata failed while deriving auto shards",
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

sys.path.insert(0, os.path.join(repo_root, "scripts"))
from matrix_shard_features import feature_args  # noqa: E402

integration_targets = {
    target["name"]: target
    for target in package.get("targets", [])
    if "test" in target.get("kind", []) and target.get("test", True)
}
for name in sorted(set(integration_targets) - assigned):
    if re.fullmatch(r"[A-Za-z0-9_-]+", name) is None:
        print(
            f"run_full_test_matrix: unsafe integration target name: {name!r}",
            file=sys.stderr,
        )
        raise SystemExit(1)
    # A feature-gated target runs only with its features; without them Cargo
    # skips it and the shard would pass having run nothing.
    features = " ".join(feature_args(integration_targets[name]))
    print(
        f"{crate}|auto-{name}|-p {crate} --test {name}{' ' + features if features else ''}||"
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

RUSTC_VERSION="unknown"
if [ -n "${MATRIX_TRUSTC}" ]; then
    RUSTC_VERSION="$(trust_env "${MATRIX_TRUSTC}" --version 2>/dev/null || echo 'unknown')"
fi
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
if [ ! -f "${MATRIX_RESULTS}" ]; then
    echo "run_full_test_matrix: missing result parser ${MATRIX_RESULTS}" >&2
    exit 1
fi

matrix_libtest_args() {
    printf '%s' '--show-output'
    [ -z "${LIBTEST_UNSTABLE_ARGS}" ] || printf ' %s' "${LIBTEST_UNSTABLE_ARGS}"
    [ -z "$1" ] || printf ' %s' "$1"
    return 0
}
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
    if value is None and toolchain.get("channel") == "trust":
        value = []  # Installed Trust packs provide components through their sysroot.
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
    local compiler_flags=()
    local build_driver=()
    local compiler_command=()
    local compiler_identity=""
    local trust_tools=""
    local compiler_path=""
    local targo_path=""
    local override=""

    channel="$(rustc_backend_toolchain_field channel)" || return 1
    components="$(rustc_backend_toolchain_field components)" || return 1
    # The bridge is built by and loaded into the installed Trust package; a
    # stock or retired nightly channel is refused, never driven through rustup.
    if [ "${channel}" != trust ]; then
        echo "run_full_test_matrix: crates/rustc-codegen-trust-cg/rust-toolchain.toml must pin channel = \"trust\", found '${channel}'" >&2
        return 1
    fi
    {
        for override in RUSTC RUSTC_WRAPPER RUSTC_WORKSPACE_WRAPPER CARGO_BUILD_RUSTC CARGO_BUILD_RUSTC_WRAPPER CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER; do
            if [ "${!override+x}" = x ]; then
                echo "run_full_test_matrix: rejects ambient compiler override: ${override}" >&2
                return 1
            fi
        done
        trust_tools="$(python3 - "${SCRIPT_DIR}" <<'PYTOOLS'
import os
from pathlib import Path
import shutil
import sys
sys.path.insert(0, sys.argv[1])
from trust_toolchain import launcher_target  # noqa: E402
try:
    paths = []
    for name in ("trustc", "targo"):
        found = shutil.which(name)
        if found is None:
            raise RuntimeError(f"required installed Trust tool is missing from PATH: {name}")
        path = Path(found).resolve(strict=True)
        # An atpkg launcher shim is followed to the package file it execs.
        target = launcher_target(path)
        if target is not None:
            path = target.resolve(strict=True)
        if not path.is_file() or not os.access(path, os.X_OK):
            raise RuntimeError(f"Trust tool is not an executable file: {path}")
        paths.append(path)
    if paths[0].parent != paths[1].parent:
        raise RuntimeError("PATH trustc and targo must resolve to the same installed package")
    print(*paths, sep="\n")
except (OSError, RuntimeError) as error:
    print(f"run_full_test_matrix: {error}", file=sys.stderr)
    sys.exit(1)
PYTOOLS
)" || return 1
        compiler_path="${trust_tools%%$'\n'*}"
        targo_path="${trust_tools#*$'\n'}"
        compiler_command=("${compiler_path}")
        compiler_flags=(-Ztrust-verify=off)
        build_driver=(env "RUSTC=${compiler_path}" "${targo_path}" --unverified)
    }

    echo "Rustc backend availability probe:"
    echo "  manifest: ${backend_manifest}"
    echo "  toolchain: ${channel}"
    echo "  compiler command: ${compiler_command[*]}"
    echo "  build command: ${build_driver[*]}"
    if ! "${compiler_command[@]}" --version >/dev/null 2>&1; then
        echo "run_full_test_matrix: selected compiler is unavailable for ${channel}" >&2
        return 1
    fi
    compiler_identity="$("${compiler_command[@]}" -vV)" || return 1
    if [ "${channel}" = trust ] && ! { printf '%s\n' "${compiler_identity}" | grep -qx 'binary: trustc' && printf '%s\n' "${compiler_identity}" | grep -Eq '^commit-hash: [0-9a-f]{40}$'; }; then
        echo "run_full_test_matrix: installed Trust compiler lacks branded trustc/commit identity" >&2
        return 1
    fi
    sysroot="$("${compiler_command[@]}" --print sysroot)" || return 1
    if [ "${channel}" = trust ]; then
        sysroot="$(python3 - "${sysroot}" "${compiler_path}" <<'PYSYSROOT'
from pathlib import Path
import sys
path = Path(sys.argv[1]).resolve(strict=True)
if path != Path(sys.argv[2]).parent.parent:
    print("run_full_test_matrix: Trust compiler/sysroot package mismatch", file=sys.stderr)
    sys.exit(1)
print(path)
PYSYSROOT
)" || return 1
    fi
    host="$(printf '%s\n' "${compiler_identity}" | awk '/^host: / { print $2 }')"
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
    if ! "${compiler_command[@]}" "${compiler_flags[@]}" --crate-name trust_cg_rustc_private_probe "${probe_src}" -o "${probe_bin}" >/dev/null 2>&1; then
        echo "run_full_test_matrix: pinned toolchain exists but cannot compile a rustc_private probe" >&2
        echo "run_full_test_matrix: this blocks rustc_codegen_trust_cg CI even before backend correctness tests" >&2
        return 1
    fi
    rm -rf "${probe_dir}"
    trap - RETURN

    if ! CARGO_TARGET_DIR="${REPO_ROOT}/target/rustc-codegen-trust-cg-${channel}" \
        "${build_driver[@]}" build --manifest-path "${backend_manifest}" --release --locked; then
        echo "run_full_test_matrix: rustc_codegen_trust_cg release build failed under ${channel}" >&2
        echo "run_full_test_matrix: this blocks replacement because the rustc backend no longer builds against its pinned rustc_private API" >&2
        return 1
    fi

    printf '%s\n' "${compiler_identity}"
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
    SHARD_PLAN_FOR_POLICY="${SHARD_PLAN}" python3 - "${REPO_ROOT}" "${MATRIX_TARGO}" <<'PYEOF'
import json
import os
import subprocess
import sys

repo_root = sys.argv[1]
targo = sys.argv[2]
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
    [targo, "metadata", "--locked", "--no-deps", "--format-version", "1"],
    cwd=repo_root,
    check=False,
    text=True,
    capture_output=True,
)
if metadata.returncode != 0:
    print(f"run_full_test_matrix: {targo} metadata failed while checking shard policy", file=sys.stderr)
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

# A shard that selects a target without enabling its required features runs
# nothing for it, and Cargo reports success (TRUSTCG-20).
sys.path.insert(0, os.path.join(repo_root, "scripts"))
from matrix_shard_features import feature_gate_problems  # noqa: E402

feature_problems = feature_gate_problems(shards, packages)
if feature_problems:
    for problem in feature_problems:
        print(f"run_full_test_matrix: shard policy: {problem}", file=sys.stderr)
    print(
        "Enable the target's features in a shard that selects it (--features ...).",
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
# Auto mode probes when aterm or AY is advertised; the Rust gate admits only the
# build toolchain's identity-checked AY (crates/trust-cg-verify/src/ay_identity.rs)
# and that toolchain's Clean (else the managed one), and checks capability.
# PATH presence is only a scheduling hint, never proof authority. A broken installed package is
# a failure, not a reason to skip. Explicit overrides (including empty invalid
# ones) also require the probe. Z3 is neither discovered nor invoked.
MATRIX_PROOF_GATE_RESULT="not-run"
if [ "${DRY_RUN}" -eq 0 ] && [ "${TRUST_CG_PROOF_GATE:-auto}" != "skip" ]; then
    if command -v aterm >/dev/null 2>&1 ||
        command -v alab-ay >/dev/null 2>&1 ||
        command -v ay >/dev/null 2>&1 ||
        { [ -n "${MATRIX_TRUST_SYSROOT:-}" ] && [ -x "${MATRIX_TRUST_SYSROOT}/bin/ay" ]; } ||
        [ "${AY_SOLVER_PATH+x}" = x ] ||
        [ "${TCG_EXTERNAL_CLEAN_CHECKER+x}" = x ] ||
        [ "${TCG_CLEAN_CHECKER+x}" = x ]; then
        echo '>>> proof-gate (strict formal SMT discharge)'
        "${SCRIPT_DIR}/check_proof_gate.sh" || exit 1
        MATRIX_PROOF_GATE_RESULT="passed"
    elif [ "${TRUST_CG_PROOF_GATE:-auto}" = "require" ] || [ -n "${CI:-}" ] || [ -n "${GITHUB_ACTIONS:-}" ]; then
        # Fail closed in CI (or when explicitly required): a green matrix must not
        # silently omit the formal floor just because a solver wasn't installed.
        echo 'run_full_test_matrix: no AY/aterm toolchain advertised and proof gate is required' >&2
        echo '  (CI detected or TRUST_CG_PROOF_GATE=require) — refusing to report success with' >&2
        echo '  the formal floor UN-RUN. Inspect aterm’s managed AY and Clean packages.' >&2
        exit 1
    else
        # Local convenience only: loud, unmistakable warning so a solver-less run
        # is never mistaken for a green that includes the formal floor.
        echo '!!! run_full_test_matrix: no AY/aterm toolchain advertised — STRICT PROOF GATE SKIPPED !!!' >&2
        echo '!!! This run did NOT discharge the formal floor. AY and Clean ship through aterm.    !!!' >&2
        echo '!!! Set TRUST_CG_PROOF_GATE=require to enforce it. (Auto-enforced in CI.)             !!!' >&2
    fi
fi

if [ "${DRY_RUN}" -eq 1 ]; then
    echo "Shard plan (${TODAY}):"
    while IFS='|' read -r shard_crate shard_name shard_args shard_post_args shard_notes; do
        [ -z "${shard_crate}" ] && continue
        if ! shard_matches_only "${shard_crate}" "${shard_name}"; then
            continue
        fi
        printf "  %-14s %-20s scripts/run_with_timeout.py %s scripts/trust_cargo.sh test --locked %s --no-fail-fast" \
            "${shard_crate}" "${shard_name}" "${TEST_TIMEOUT_SECONDS}" "${shard_args}"
        printf " -- %s" "$(matrix_libtest_args "${shard_post_args}")"
        printf "\n"
    done <<< "${SHARD_PLAN}"
    echo
    echo "External validation probes:"
    echo "  rustc-codegen-trust-cg rustc-backend-env scripts/run_full_test_matrix.sh --check-rustc-backend-env"
    echo "    requires the compiler and development libraries selected by crates/rustc-codegen-trust-cg/rust-toolchain.toml"
    echo "    release-builds crates/rustc-codegen-trust-cg against that pinned rustc_private API"
    echo "    not part of the default local stable workspace matrix; CI runs it in a dedicated rustc-dev lane"
    exit 0
fi

# The runner's mode selects whether it runs the external formal gate; it is
# not a compiler control. Do not leak it into child tests, where Core admission
# correctly refuses unknown TRUST_CG_* controls. Retain the mode in the report.
MATRIX_PROOF_GATE_MODE="${TRUST_CG_PROOF_GATE:-auto}"
if [ "$MATRIX_PROOF_GATE_MODE" = skip ]; then
    echo 'run_full_test_matrix: STRICT PROOF GATE SKIPPED explicitly; runtime results do not include the formal floor' >&2
fi
unset TRUST_CG_PROOF_GATE TRUST_CG_COVERAGE_GATE TRUST_CG_TEST_MATRIX_FORCE_JSON
unset TRUST_CG_TEST_MATRIX_TIMEOUT_SECONDS TCG_SKIP_BENCH_STAGE TRUST_CG_REQUIRE_BENCH

# Run each shard, capture named libtest output, and retain every transcript.
# Sequential execution avoids competing Cargo jobs.

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
    libtest_args="$(matrix_libtest_args "${shard_post_args}")"
    shard_command="scripts/run_with_timeout.py ${TEST_TIMEOUT_SECONDS} scripts/trust_cargo.sh test --locked ${shard_args} --no-fail-fast -- ${libtest_args}"
    echo "    ${shard_command}"

    # Keep successful captures too: a raw libtest pass may contain a runtime
    # SKIP, and every classified outcome must retain its underlying transcript.
    shard_log="$(mktemp "${EVALS_DIR}/${TODAY}.${shard_crate}.${shard_name}.XXXXXX")" || exit 1
    # Python <3.10 on macOS gives monotonic_ns() a process-local origin.
    # This POSIX runner samples in separate processes, so use the OS clock
    # directly; never subtract unrelated interpreter-relative timestamps.
    start_ns="$(python3 -c 'import time; print(time.clock_gettime_ns(time.CLOCK_MONOTONIC))')" || exit 1

    # A caching Cargo shim that omits stdout must not manufacture test evidence.
    # shellcheck disable=SC2086
    CARGO_SKIP_CACHE=1 "${RUN_WITH_TIMEOUT}" "${TEST_TIMEOUT_SECONDS}" \
        "${SCRIPT_DIR}/trust_cargo.sh" test --locked ${shard_args} --no-fail-fast -- ${libtest_args} \
        > "${shard_log}" 2>&1
    shard_rc=$?
    end_ns="$(python3 -c 'import time; print(time.clock_gettime_ns(time.CLOCK_MONOTONIC))')" || exit 1
    dt="$(python3 -c "print((${end_ns}-${start_ns})/1e9)")" || exit 1

    if ! python3 "${MATRIX_RESULTS}" parse-shard \
        "${shard_crate}" "${shard_name}" "${shard_log}" "${dt}" "${shard_rc}" \
        "${shard_notes}" "${shard_args}" "${shard_post_args}" "${shard_command}" \
        "${TEST_TIMEOUT_SECONDS}" "${TIMEOUT_POLICY}" "${shard_log}" "${LIBTEST_OUTPUT_KIND}" \
        >> "${TMP_SHARDS_JSON}"; then
        echo "run_full_test_matrix: failed to parse ${shard_crate}/${shard_name}; kept log: ${shard_log}" >&2
        exit 1
    fi

    if [ "${shard_rc}" -ne 0 ]; then
        failed_shards=$((failed_shards + 1))
        echo "    shard returned rc=${shard_rc} (outcomes are recorded in JSON)"
    fi
    echo "    kept shard log: ${shard_log}"
done <<< "${SHARD_PLAN}"

if [ "${total_shards}" -eq 0 ]; then
    fail_no_shards_selected
fi

# Aggregate shard JSON lines into the final output.
if ! python3 "${MATRIX_RESULTS}" aggregate "${TMP_SHARDS_JSON}" "${OUT}" "${TODAY}" \
    "${COMMIT_SHA}" "${COMMIT_SHORT}" "${RUSTC_VERSION}" "${total_shards}" \
    "${MATRIX_PROOF_GATE_MODE}" "${MATRIX_PROOF_GATE_RESULT}" \
    "${BENCH_STAGE_MODE}" "${BENCH_STAGE_RESULT}" "${BENCH_STAGE_RC}"
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
