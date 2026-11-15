#!/bin/sh
#
# Fail-closed public-release gate for trust-cg-codegen: the complement of every
# non-capstone test plus doctests, and the generated Clean-kernel codegen
# capstones merged into the publication candidate.
#
# These JIT-heavy capstones must not share a libtest process: accumulated JIT
# state has previously made an otherwise-correct aggregate run unreliable. Pin
# the exact libtest inventory, then execute every release-selected test in its
# own bounded targo process with one test thread.
#
# Usage: run_public_release_codegen_tests.sh
#            [--release|--complement|--plan|--self-test|--validate-policy|
#             --qualify-kernel-layout-fixtures]
#            [--proof-gate=auto|require] [--summary=PATH]
#
# --proof-gate defaults to TRUST_CG_PROOF_GATE (the run_full_test_matrix.sh
# spelling), which is consumed here and never exported to targo. In auto mode a
# host without a resolvable AY solver skips the solver-backed tests listed in
# SOLVER_SKIP_TESTS; every such --skip is recorded as an exclusion and
# announced as NON-QUALIFYING. require mode refuses to run unless AY and Clean
# resolve through a pinned route (AY: an absolute AY_SOLVER_PATH or the build
# toolchain's bin/ay; Clean: explicit override or aterm's managed store) and
# refuses any exclusion. The capstones are in-process JIT differentials
# qualified only on aarch64-apple-darwin; aarch64-unknown-linux-gnu runs the
# complement and records the capstones as a host exclusion. Test-running modes
# record lanes and exclusions in a scripts/release_gate_summary.py document:
# the --summary document owned by the caller, or a new one in a fresh
# temporary directory. --plan records the plan without invoking targo.
# --qualify-kernel-layout-fixtures runs EVERY compiled test of the eleven
# layout-policy targets separately, including their complement cases. It
# records layout-differential evidence only, never full release/proof credit.

set -eu

# Private fake-cargo endpoint used only by `--self-test`. Normal publication
# invocations never enter this branch.
if [ "${1-}" = "--fake-cargo" ]; then
    shift
    mode=${TCG_RELEASE_FAKE_CARGO_MODE-}
    if [ -z "${mode}" ]; then
        echo "run_public_release_codegen_tests: fake cargo mode is unset" >&2
        exit 2
    fi
    is_list=0
    has_all_features=0
    exact_name=
    previous_arg=
    for arg in "$@"; do
        if [ "${previous_arg}" = "--exact" ]; then
            exact_name=${arg}
        fi
        if [ "${arg}" = "--list" ]; then
            is_list=1
        fi
        if [ "${arg}" = "--all-features" ]; then
            has_all_features=1
        fi
        previous_arg=${arg}
    done
    if [ "${has_all_features}" -ne 1 ]; then
        echo "run_public_release_codegen_tests: fake cargo requires --all-features" >&2
        exit 10
    fi
    if [ "${is_list}" -eq 1 ]; then
        case "${mode}" in
            valid|exact_fail)
                printf '%s\n' 'alpha: test'
                ;;
            missing)
                printf '%s\n' 'beta: test'
                ;;
            duplicate)
                printf '%s\n' 'alpha: test' 'alpha: test'
                ;;
            full_valid|full_empty_exact)
                printf '%s\n' 'alpha: test' 'beta: test'
                ;;
            full_duplicate)
                printf '%s\n' 'alpha: test' 'alpha: test'
                ;;
            list_fail)
                exit 9
                ;;
            *)
                echo "run_public_release_codegen_tests: unknown fake cargo mode ${mode}" >&2
                exit 2
                ;;
        esac
        exit 0
    fi
    if [ "${mode}" = "exact_fail" ]; then
        exit 7
    fi
    if [ "${mode}" = "full_valid" ]; then
        printf 'running 1 test\ntest %s ... ok\n' "${exact_name}"
        printf 'test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 1 filtered out; finished in 0.01s\n'
    fi
    exit 0
fi

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
REPO_ROOT=$(CDPATH= cd -- "${SCRIPT_DIR}/.." && pwd)
RUN_WITH_TIMEOUT="${SCRIPT_DIR}/run_with_timeout.py"
SUMMARY_TOOL="${SCRIPT_DIR}/release_gate_summary.py"
TRANSCRIPT_TOOL="${SCRIPT_DIR}/rust_guard_transcript.py"
cd "${REPO_ROOT}"

usage() {
    echo "usage: $0 [--release|--complement|--plan|--self-test|--validate-policy|--qualify-kernel-layout-fixtures] [--proof-gate=auto|require] [--summary=PATH]" >&2
}

ORIGINAL_ARGS="$*"
ACTION=
ACTION_SEEN=0
PROOF_GATE=${TRUST_CG_PROOF_GATE:-auto}
SUMMARY_PATH=
for arg in "$@"; do
    case "${arg}" in
        --release|--complement|--plan|--self-test|--validate-policy|--qualify-kernel-layout-fixtures)
            if [ "${ACTION_SEEN}" -eq 1 ]; then
                usage
                exit 2
            fi
            ACTION=${arg}
            ACTION_SEEN=1
            ;;
        --proof-gate=*)
            PROOF_GATE=${arg#--proof-gate=}
            ;;
        --summary=*)
            SUMMARY_PATH=${arg#--summary=}
            # The runner has already changed to the source root, so a relative
            # path would silently name a document inside the checkout.
            case "${SUMMARY_PATH}" in
                /*) ;;
                *)
                    echo "run_public_release_codegen_tests: --summary requires an absolute path" >&2
                    usage
                    exit 2
                    ;;
            esac
            ;;
        *)
            usage
            exit 2
            ;;
    esac
done
case "${PROOF_GATE}" in
    auto|require) ;;
    *)
        echo "run_public_release_codegen_tests: proof gate must be auto or require, got '${PROOF_GATE}'" >&2
        exit 2
        ;;
esac
# Child tests run through targo refuse unknown TRUST_CG_* controls; the mode is ours alone.
unset TRUST_CG_PROOF_GATE
case "${ACTION}" in
    --self-test|--validate-policy)
        if [ -n "${SUMMARY_PATH}" ]; then
            echo "run_public_release_codegen_tests: --summary applies only to test-running modes" >&2
            exit 2
        fi
        ;;
esac

# Each selected JIT-heavy test already runs in its own Cargo process. Keep the
# complement and inventory lanes serial in libtest too unless a caller opts in
# to a different thread count.
: "${RUST_TEST_THREADS:=1}"
export RUST_TEST_THREADS

if ! command -v python3 >/dev/null 2>&1; then
    echo "run_public_release_codegen_tests: python3 is required for bounded test processes" >&2
    exit 1
fi
if [ ! -x "${RUN_WITH_TIMEOUT}" ]; then
    echo "run_public_release_codegen_tests: missing executable timeout runner ${RUN_WITH_TIMEOUT}" >&2
    exit 1
fi

# Every Cargo process runs on the installed Trust package (rust-toolchain.toml
# `channel = "trust"`; owner directive 2026-09-28) through scripts/trust_cargo.sh:
# TRUST_TARGO names its targo explicitly (the release gate passes the one it
# resolved), else scripts/trust_toolchain.py resolves it. No stock fallback.
TRUST_CARGO="${SCRIPT_DIR}/trust_cargo.sh"
if [ -n "${TRUST_TARGO:-}" ]; then
    TRUST_COMPILER="$(dirname -- "${TRUST_TARGO}")/trustc"
else
    TRUST_TARGO=$(python3 -B "${SCRIPT_DIR}/trust_toolchain.py" --print targo) || {
        echo "run_public_release_codegen_tests: no installed Trust package resolves (scripts/trust_toolchain.py)" >&2
        exit 1
    }
    TRUST_COMPILER=$(python3 -B "${SCRIPT_DIR}/trust_toolchain.py" --print compiler) || exit 1
fi
export TRUST_TARGO
# trustc refuses to run at all under any TRUST_CG_*/TCG_* variable.
trust_probe() {
    set -- env $(env | awk -F= '/^(TRUST_CG_|TCG_)/ { printf "-u %s ", $1 }') "$@"
    "$@"
}

# The selected kernel fixtures contain compiler-specific repr(Rust) layouts
# and ABI decisions. crates/trust-cg-codegen/fixture_toolchain.rs certifies the
# exact Trust compilers scripts/release_trust_compilers.txt lists for each
# host; assert it here too so an override cannot route an unknown compiler
# through the current-fixture branch and turn a stale-layout mismatch into
# memory unsafety.
RELEASE_TRUST_COMPILERS="${SCRIPT_DIR}/release_trust_compilers.txt"
host_target=$(trust_probe "${TRUST_COMPILER}" -vV 2>/dev/null | sed -n 's/^host: //p')
case "${host_target}" in
    aarch64-apple-darwin|aarch64-unknown-linux-gnu)
        expected_trustc=$(awk -F '\t' -v host="${host_target}" \
            '$0 !~ /^#/ && NF == 2 && $1 == host { print $2 }' "${RELEASE_TRUST_COMPILERS}") \
            || expected_trustc=
        ;;
    *) expected_trustc= ;;
esac
actual_trustc=$(trust_probe "${TRUST_COMPILER}" --version 2>/dev/null || true)
actual_targo=$(trust_probe "${TRUST_TARGO}" --unverified --version 2>/dev/null || true)
certified=0
while IFS= read -r line; do
    if [ -n "${line}" ] && [ "${line}" = "${actual_trustc}" ]; then
        certified=1
    fi
done <<EOF
${expected_trustc}
EOF
if [ "${certified}" -ne 1 ]; then
    if [ -n "${expected_trustc}" ]; then
        expected_desc="one of the ${host_target} compilers in ${RELEASE_TRUST_COMPILERS} ($(printf '%s\n' "${expected_trustc}" | paste -s -d ';' -))"
    else
        expected_desc="an aarch64-apple-darwin or aarch64-unknown-linux-gnu Trust compiler listed in ${RELEASE_TRUST_COMPILERS}"
    fi
    echo "run_public_release_codegen_tests: expected ${expected_desc}, got ${actual_trustc:-no identity from ${TRUST_COMPILER}}" >&2
    exit 1
fi
trustc_build=$(printf '%s\n' "${actual_trustc}" | sed -n 's/^rustc \([^ ]* ([^)]*)\) (trustc .*/\1/p')
case "${actual_targo}" in
    "targo ${trustc_build} (targo "*) ;;
    *)
        echo "run_public_release_codegen_tests: ${TRUST_TARGO} (${actual_targo:-rejects --unverified}) is not the targo of ${actual_trustc}" >&2
        exit 1
        ;;
esac
# The capstones compare in-process JIT code with host Rust values; they are
# qualified only on aarch64-apple-darwin and are not treated as exercised on
# another host. Linux AArch64 runs the complement and records that exclusion.
case "${host_target}" in
    aarch64-apple-darwin)
        CAPSTONE_HOST=1
        ;;
    aarch64-unknown-linux-gnu)
        CAPSTONE_HOST=0
        ;;
    *)
        echo "run_public_release_codegen_tests: expected an aarch64-apple-darwin or aarch64-unknown-linux-gnu host, got ${host_target:-unknown}" >&2
        exit 1
        ;;
esac
if [ "${CAPSTONE_HOST}" -eq 0 ]; then
    case "${ACTION}" in
        "")
            echo "run_public_release_codegen_tests: capstone-only mode requires an aarch64-apple-darwin host, got ${host_target}" >&2
            exit 1
            ;;
        --qualify-kernel-layout-fixtures)
            echo "run_public_release_codegen_tests: kernel-layout qualification requires an aarch64-apple-darwin host, got ${host_target}" >&2
            exit 1
            ;;
    esac
fi

run_with_timeout() {
    timeout_seconds=$1
    shift
    "${RUN_WITH_TIMEOUT}" "${timeout_seconds}" "$@"
}

SELF_TEST_FAKE_CARGO=0
run_cargo_with_timeout() {
    cargo_timeout=$1
    shift
    if [ "${SELF_TEST_FAKE_CARGO}" -eq 1 ]; then
        run_with_timeout "${cargo_timeout}" sh "$0" --fake-cargo "$@"
    else
        run_with_timeout "${cargo_timeout}" "${TRUST_CARGO}" "$@"
    fi
}

RUN_EXACT_TESTS=1
RUN_ALL_TARGET_TESTS=0
LAYOUT_CASES_EXECUTED=0
LAYOUT_EVIDENCE_DIR=

run_target() {
    target=$1
    expected_total=$2
    expected_selected=$3
    coverage=$4
    shift 4

    test_file="crates/trust-cg-codegen/tests/${target}.rs"
    if [ ! -f "${test_file}" ]; then
        echo "run_public_release_codegen_tests: missing test target ${test_file}" >&2
        exit 1
    fi
    if [ "$#" -ne "${expected_selected}" ]; then
        echo "run_public_release_codegen_tests: ${target} policy names $# test(s), expected ${expected_selected}" >&2
        exit 1
    fi
    for policy_count in "${expected_total}" "${expected_selected}"; do
        case "${policy_count}" in
            ""|*[!0-9]*)
                echo "run_public_release_codegen_tests: ${target} policy counts must be integers" >&2
                exit 1
                ;;
        esac
    done
    if [ -z "${expected_selected}" ] || [ "${expected_total}" -le 0 ] || [ "${expected_selected}" -le 0 ]; then
        echo "run_public_release_codegen_tests: ${target} policy must select a nonzero inventory" >&2
        exit 1
    fi
    if [ "${coverage}" = "full" ] && [ "${expected_selected}" -ne "${expected_total}" ]; then
        echo "run_public_release_codegen_tests: full target ${target} does not select its complete expected inventory" >&2
        exit 1
    fi
    if [ "${coverage}" != "full" ] && [ "${coverage}" != "subset" ]; then
        echo "run_public_release_codegen_tests: invalid coverage mode ${coverage} for ${target}" >&2
        exit 1
    fi

    echo ">>> public-release codegen inventory: ${target}"
    if ! listing=$(
        run_cargo_with_timeout 1200 \
            test --locked --quiet -p trust-cg-codegen --all-features \
            --test "${target}" -- \
            --list --format terse
    ); then
        echo "run_public_release_codegen_tests: could not list ${target}" >&2
        exit 1
    fi

    actual_total=$(
        printf '%s\n' "${listing}" |
            awk -F ': ' '$2 == "test" { count += 1 } END { print count + 0 }'
    )
    if [ "${actual_total}" -ne "${expected_total}" ]; then
        echo "run_public_release_codegen_tests: ${target} exposes ${actual_total} test(s), expected ${expected_total}" >&2
        exit 1
    fi

    if [ "${RUN_ALL_TARGET_TESTS}" -eq 1 ]; then
        printf '%s\n' "${listing}" >"${LAYOUT_EVIDENCE_DIR}/${target}.inventory.log"
        compiled_names=$(printf '%s\n' "${listing}" | awk -F ': ' '$2 == "test" { print $1 }')
        malformed_names=$(printf '%s\n' "${compiled_names}" | grep -Ev '^[A-Za-z_][A-Za-z_0-9:]*$' || true)
        duplicate_names=$(printf '%s\n' "${compiled_names}" | LC_ALL=C sort | uniq -d)
        if [ -n "${malformed_names}" ] || [ -n "${duplicate_names}" ]; then
            echo "run_public_release_codegen_tests: ${target} has malformed or duplicate compiled case names" >&2
            exit 1
        fi
    fi

    seen=" "
    for test_name in "$@"; do
        case "${seen}" in
            *" ${test_name} "*)
                echo "run_public_release_codegen_tests: duplicate policy test ${target}::${test_name}" >&2
                exit 1
                ;;
        esac
        seen="${seen}${test_name} "

        matches=$(
            printf '%s\n' "${listing}" |
                awk -F ': ' -v wanted="${test_name}" \
                    '$1 == wanted && $2 == "test" { count += 1 } END { print count + 0 }'
        )
        if [ "${matches}" -ne 1 ]; then
            echo "run_public_release_codegen_tests: expected exactly one ${target}::${test_name}, found ${matches}" >&2
            exit 1
        fi
    done

    if [ "${RUN_ALL_TARGET_TESTS}" -eq 1 ]; then
        # Names were validated above, so splitting on newlines cannot introduce
        # shell patterns or arguments. Keep the selected-name checks above even
        # when this mode runs the entire compiled inventory.
        set -- ${compiled_names}
        if [ "$#" -ne "${expected_total}" ]; then
            echo "run_public_release_codegen_tests: ${target} full execution roster is incomplete" >&2
            exit 1
        fi
    fi

    if [ "${RUN_EXACT_TESTS}" -eq 1 ]; then
        for test_name in "$@"; do
            echo ">>> public-release codegen test: ${target}::${test_name}"
            if [ "${RUN_ALL_TARGET_TESTS}" -eq 1 ]; then
                LAYOUT_CASES_EXECUTED=$((LAYOUT_CASES_EXECUTED + 1))
                exact_log="${LAYOUT_EVIDENCE_DIR}/case-${LAYOUT_CASES_EXECUTED}.log"
                if run_cargo_with_timeout 600 \
                    test --locked -p trust-cg-codegen --all-features \
                    --test "${target}" -- \
                    --exact "${test_name}" --include-ignored --test-threads=1 \
                    >"${exact_log}" 2>&1; then
                    cat "${exact_log}"
                else
                    exact_status=$?
                    cat "${exact_log}"
                    return "${exact_status}"
                fi
                if ! python3 -I -B "${TRANSCRIPT_TOOL}" --exact-name "${test_name}" \
                    --inventory-total "${expected_total}" "${exact_log}"; then
                    return 1
                fi
            else
                run_cargo_with_timeout 600 \
                    test --locked -p trust-cg-codegen --all-features \
                    --test "${target}" -- \
                        --exact "${test_name}" --include-ignored \
                        --test-threads="${RUST_TEST_THREADS}"
            fi
        done
    fi
}

runner_self_test() {
    echo ">>> public-release codegen runner self-test"

    run_with_timeout 5 sh -c 'exit 0'

    if run_with_timeout 5 sh -c 'exit 7'; then
        echo "run_public_release_codegen_tests: nonzero self-test unexpectedly passed" >&2
        return 1
    else
        status=$?
    fi
    if [ "${status}" -ne 7 ]; then
        echo "run_public_release_codegen_tests: expected status 7, got ${status}" >&2
        return 1
    fi

    # SIGKILL, not a core-dump signal: the runner maps any signal death to
    # 128+N, and a SEGV'd /bin/sh made macOS write a crash report every run.
    if run_with_timeout 5 sh -c 'kill -KILL $$'; then
        echo "run_public_release_codegen_tests: signal self-test unexpectedly passed" >&2
        return 1
    else
        status=$?
    fi
    if [ "${status}" -ne 137 ]; then
        echo "run_public_release_codegen_tests: expected SIGKILL status 137, got ${status}" >&2
        return 1
    fi

    pid_file=$(mktemp "${TMPDIR:-/tmp}/trust-cg-release-runner.XXXXXX")
    if run_with_timeout 1 sh -c \
        'trap "" TERM; (trap "" TERM; while :; do sleep 60; done) & echo $! > "$1"; wait' \
        sh "${pid_file}"; then
        echo "run_public_release_codegen_tests: timeout self-test unexpectedly passed" >&2
        rm -f "${pid_file}"
        return 1
    else
        status=$?
    fi
    if [ "${status}" -ne 124 ]; then
        echo "run_public_release_codegen_tests: expected timeout status 124, got ${status}" >&2
        rm -f "${pid_file}"
        return 1
    fi
    descendant_pid=$(sed -n '1p' "${pid_file}")
    rm -f "${pid_file}"
    attempts=0
    while kill -0 "${descendant_pid}" 2>/dev/null && [ "${attempts}" -lt 20 ]; do
        attempts=$((attempts + 1))
        sleep 0.1
    done
    if kill -0 "${descendant_pid}" 2>/dev/null; then
        echo "run_public_release_codegen_tests: timed-out descendant ${descendant_pid} survived" >&2
        return 1
    fi

    SELF_TEST_FAKE_CARGO=1
    export TCG_RELEASE_FAKE_CARGO_MODE=valid
    run_target e2e_binding_defeq 1 1 full alpha >/dev/null

    export TCG_RELEASE_FAKE_CARGO_MODE=list_fail
    if (run_target e2e_binding_defeq 1 1 full alpha) >/dev/null 2>&1; then
        echo "run_public_release_codegen_tests: failing inventory command was accepted" >&2
        return 1
    fi

    export TCG_RELEASE_FAKE_CARGO_MODE=missing
    if (run_target e2e_binding_defeq 1 1 full alpha) >/dev/null 2>&1; then
        echo "run_public_release_codegen_tests: missing exact test was accepted" >&2
        return 1
    fi

    export TCG_RELEASE_FAKE_CARGO_MODE=duplicate
    if (run_target e2e_binding_defeq 2 1 subset alpha) >/dev/null 2>&1; then
        echo "run_public_release_codegen_tests: duplicate inventory test was accepted" >&2
        return 1
    fi

    export TCG_RELEASE_FAKE_CARGO_MODE=valid
    if (run_target e2e_binding_defeq 1 2 subset alpha alpha) >/dev/null 2>&1; then
        echo "run_public_release_codegen_tests: duplicate policy test was accepted" >&2
        return 1
    fi
    if (run_target e2e_binding_defeq 0 0 full) >/dev/null 2>&1; then
        echo "run_public_release_codegen_tests: zero-test policy was accepted" >&2
        return 1
    fi

    export TCG_RELEASE_FAKE_CARGO_MODE=exact_fail
    if (run_target e2e_binding_defeq 1 1 full alpha) >/dev/null 2>&1; then
        echo "run_public_release_codegen_tests: failing exact test was accepted" >&2
        return 1
    fi

    layout_selftest=$(mktemp -d "${TMPDIR:-/tmp}/trust-cg-layout-selftest.XXXXXX")
    LAYOUT_EVIDENCE_DIR=${layout_selftest}
    RUN_ALL_TARGET_TESTS=1
    export TCG_RELEASE_FAKE_CARGO_MODE=full_valid
    run_target e2e_binding_defeq 2 1 subset alpha >/dev/null
    for mode in full_duplicate full_empty_exact; do
        export TCG_RELEASE_FAKE_CARGO_MODE=${mode}
        if (run_target e2e_binding_defeq 2 1 subset alpha) >/dev/null 2>&1; then
            rm -rf "${layout_selftest:?}"
            echo "run_public_release_codegen_tests: invalid complete layout execution ${mode} was accepted" >&2
            return 1
        fi
    done
    RUN_ALL_TARGET_TESTS=0
    LAYOUT_CASES_EXECUTED=0
    LAYOUT_EVIDENCE_DIR=
    rm -rf "${layout_selftest:?}"

    unset TCG_RELEASE_FAKE_CARGO_MODE
    SELF_TEST_FAKE_CARGO=0

    # An uncertified Trust compiler must be refused before any Cargo process.
    fake_package=$(mktemp -d "${TMPDIR:-/tmp}/trust-cg-release-package.XXXXXX")
    mkdir -p "${fake_package}/bin"
    printf '%s\n' '#!/bin/sh' \
        'case "$1" in -vV) echo "host: aarch64-apple-darwin" ;; --version) echo "rustc 1.99.0-dev (012345678 2026-01-01) (trustc 0.1.0)" ;; esac' \
        >"${fake_package}/bin/trustc"
    printf '%s\n' '#!/bin/sh' 'echo "targo 1.99.0-dev (012345678 2026-01-01) (targo 0.1.0)"' \
        >"${fake_package}/bin/targo"
    chmod +x "${fake_package}/bin/trustc" "${fake_package}/bin/targo"
    if TRUST_TARGO="${fake_package}/bin/targo" sh "$0" >/dev/null 2>&1; then
        rm -rf "${fake_package}"
        echo "run_public_release_codegen_tests: an uncertified Trust compiler was accepted" >&2
        return 1
    fi
    rm -rf "${fake_package}"

    echo "Public-release codegen runner self-test: PASS"
}

# e2e_lazy_delta carries a sixth, native-only test since 2b6fdebb5
# (ld_murmur_ragged_tail_is_mixed_not_dropped, a hash tail pin with no JIT):
# it runs in the complement, so the target is a subset of five capstones.
policy_rows() {
    cat <<'EOF'
e2e_binding_defeq|5|5|full|bd_module_sanity_and_inmodule_surface bd_probe_binding_differential bd_decl_gate_full_differential bd_blind_divergence_differential bd_armed_module_corruption_diverges
e2e_defeq_cache|8|8|full|cache_module_sanity_and_wiring cache_transparency_hit_equals_miss cache_guard_1773_soundness_centerpiece cache_equiv_manager_union_find cache_branch_sharing_3402 cache_poisoned_value_control cache_armed_fnv_corruption_control cache_full_native_jit_sweep_and_poison_push
e2e_eta_struct_ext|3|3|full|mir_eta_struct_params_roundtrip mir_eta_struct_proj_nested_roundtrip mir_expand_eta_struct_recursor_major_roundtrip
e2e_ctx_whnf_defeq|5|5|full|cw_module_sanity_and_inmodule_surface cw_probe_ctx_consults_differential cw_decl_gate_full_differential cw_blind_divergence_differential cw_armed_module_corruption_diverges
e2e_fvar_opening|4|4|full|fv_module_sanity_and_inmodule_surface fv_probe_fvar_discipline_differential fv_decl_gate_full_differential fv_armed_module_corruption_diverges
e2e_lazy_delta|6|5|subset|ld_module_sanity_and_inmodule_surface ld_probe_lazy_delta_differential ld_decl_gate_full_differential ld_blind_divergence_differential ld_armed_module_corruption_diverges
e2e_phase_completion|4|4|full|pc_module_sanity_and_inmodule_surface pc_phase_completion_differential pc_decl_gate_rerun_differential pc_armed_corruption_control
e2e_universe_realnames|5|5|full|aarch64_external_call_reads_exact_stack_slot_address aarch64_sext_i32_to_i64_store_overwrites_full_word dn_module_sanity_and_inmodule_surface dn_probe_names_bitidentical_to_kernel_goldens dn_decl_gate_full_differential_realnames
e2e_tc_stitching|5|5|full|mir_tc_infer_proj_gate_err_propagation_roundtrip mir_tc_infer_proj_ok_paths_roundtrip mir_tc_whnf_cache_routing_roundtrip mir_tc_whnf_core_unfold_discipline_roundtrip mir_tc_whnf_reduce_proj_iota_zext_load_callarg_roundtrip
e2e_universe_integration|1|1|full|mir_decl_gate_full_universe_roundtrip
e2e_frontend_roundtrip|72|7|subset|mir_verify_impl_capstone_roundtrip mir_reduce_recursor_iota_roundtrip mir_native_arith_iota_roundtrip mir_real_expr_infer_type_roundtrip mir_real_expr_infer_type_extra_roundtrip mir_real_expr_proof_irrel_roundtrip mir_real_expr_full_decl_check_roundtrip
EOF
}

policy_test_names() {
    policy_rows | awk -F '|' '{ count = split($5, names, " "); for (i = 1; i <= count; i++) print names[i] }'
}

# Source-bound object/JIT qualification rows (L11-P8, L08-P9): every test of each
# target on aarch64-apple-darwin. The complement skips them by exact name and
# then runs each in its own bounded cargo process, so each inventory is pinned
# and a vanished test fails. They pass only when the Trust toolchain's AY
# discharges the source-bound frame and ALU queries and its Clean replays the
# proofs (measured with an overlay of AY 2657db47c and Clean ed21fee39,
# reports/2026-09-29-darwin-source-bound-jit-qualification/); with pack
# 9192's AY they fail, naming the proof tools they resolved, and never skip.
# Linux AArch64 keeps running them in the complement's single process.
source_bound_rows() {
    cat <<'EOF'
aarch64_framed_identity_control|1|1|full|captured_black_box_framed_control_requires_real_proof_promotion
aarch64_nonleaf_frame_control|2|2|full|captured_nonleaf_wrapper_cannot_borrow_leaf_frame_authority captured_lang_start_cannot_borrow_leaf_frame_authority
jit_source_bound_arithmetic|4|4|full|proof_required_arithmetic_executes_all_types_shapes_and_levels source_bound_arithmetic_preserves_request_authority_and_original_inputs source_bound_constants_refute_dead_writes_and_preserve_request_authority raw_body_copy_exports_bind_exact_inputs_and_withdrawn_authority_refuses
jit_fail_closed_proof_policy|9|9|full|compiler_config_emit_proofs_maps_to_verifying_jit_config compiler_config_emit_proofs_rejects_riscv64_jit_policy compiler_jit_emit_proofs_checks_bound_add_in_object_compatibility_mode compiler_jit_emit_proofs_executes_source_bound_identity_o0_through_o3 compiler_jit_emit_proofs_rejects_unproved_calling_frame darwin_verifying_jit_leaves_keep_their_frame_and_publish_only_formal_evidence independent_jit_certificate_gate::compiler_jit_verify_override_proves_bound_add_and_rejects_raw_sampling independent_jit_certificate_gate::compiler_jit_verify_override_rejects_calling_frame_and_raw_trap_only_certificate proof_refusal_names_an_ay_refused_beneath_a_group_writable_cache
jit_cert_cache_identity_aarch64|9|9|full|always_verify_never_serves_from_a_warm_shared_cache cached_verified_caches_nothing_for_bytes_it_cannot_certify cached_verified_warm_hit_reuses_the_verdict_and_both_buffers_execute deep_verifier_override_bypasses_outer_cache_for_reads_and_writes distinct_content_misses_and_reverifies function_name_is_bound_even_when_published_machine_bytes_match raw_and_source_bound_requests_never_share_a_verdict relocation_target_name_is_bound_even_at_the_same_host_address swapped_source_and_missing_source_cannot_reuse_or_promote_the_report
EOF
}

source_bound_test_names() {
    source_bound_rows | awk -F '|' '{ count = split($5, names, " "); for (i = 1; i <= count; i++) print names[i] }'
}

validate_policy_shape() {
    names=$(policy_test_names)
    count=$(printf '%s\n' "${names}" | awk 'NF { count += 1 } END { print count + 0 }')
    if [ "${count}" -ne 52 ]; then
        echo "run_public_release_codegen_tests: policy names ${count} test(s), expected 52" >&2
        exit 1
    fi
    duplicates=$(printf '%s\n' "${names}" | sort | uniq -d)
    if [ -n "${duplicates}" ]; then
        echo "run_public_release_codegen_tests: globally duplicated policy name(s): ${duplicates}" >&2
        exit 1
    fi
    bound=$(source_bound_test_names)
    count=$(printf '%s\n' "${bound}" | awk 'NF { count += 1 } END { print count + 0 }')
    if [ "${count}" -ne 25 ]; then
        echo "run_public_release_codegen_tests: source-bound rows name ${count} test(s), expected 25" >&2
        exit 1
    fi
    duplicates=$(printf '%s\n%s\n' "${names}" "${bound}" | sort | uniq -d)
    if [ -n "${duplicates}" ]; then
        echo "run_public_release_codegen_tests: duplicated capstone/source-bound name(s): ${duplicates}" >&2
        exit 1
    fi
}

validate_global_policy_inventory() {
    echo ">>> public-release codegen global inventory"
    if ! listing=$(
        run_cargo_with_timeout 1800 \
            test --locked --quiet -p trust-cg-codegen --all-features \
                --lib --bins --examples --tests -- --list --format terse
    ); then
        echo "run_public_release_codegen_tests: could not list global codegen inventory" >&2
        exit 1
    fi
    for test_name in $(policy_test_names) $(host_source_bound_test_names); do
        matches=$(
            printf '%s\n' "${listing}" |
                awk -F ': ' -v wanted="${test_name}" \
                    '$1 == wanted && $2 == "test" { count += 1 } END { print count + 0 }'
        )
        if [ "${matches}" -ne 1 ]; then
            echo "run_public_release_codegen_tests: expected one global ${test_name}, found ${matches}" >&2
            exit 1
        fi
    done
}

# The source-bound rows this host runs exactly (Darwin only; see
# source_bound_rows).
host_source_bound_test_names() {
    if [ "${CAPSTONE_HOST}" -eq 1 ]; then
        source_bound_test_names
    fi
}

run_rows() {
    while IFS='|' read -r target expected_total expected_selected coverage names; do
        [ -n "${target}" ] || continue
        set -f
        # Policy names are controlled Rust identifiers separated by spaces.
        set -- ${names}
        run_target "${target}" "${expected_total}" "${expected_selected}" "${coverage}" "$@"
    done
}

run_policy() {
    policy_rows | run_rows
}

run_source_bound_policy() {
    if [ "${CAPSTONE_HOST}" -eq 1 ]; then
        source_bound_rows | run_rows
    fi
}

validate_policy() {
    validate_policy_shape
    validate_global_policy_inventory
    RUN_EXACT_TESTS=0
    run_policy
    run_source_bound_policy
    RUN_EXACT_TESTS=1
}

# `AY_SOLVER_PATH` is the canonical override and the ONLY name the backend
# reads (crates/trust-cg-verify/src/ay_identity.rs: it must be absolute and is
# identity-checked exactly like the toolchain's own `bin/ay`; there is no PATH
# lookup and no other automatic route). `TCG_SOLVER_PATH` is accepted as a
# legacy alias and exported to the canonical name, so the tests see exactly the
# solver this gate saw. scripts/release_gate_summary.py mirrors that rule.
if [ -z "${AY_SOLVER_PATH:-}" ] && [ -n "${TCG_SOLVER_PATH:-}" ]; then
    export AY_SOLVER_PATH="${TCG_SOLVER_PATH}"
fi
# The alias is consumed; trustc refuses to run while any TCG_* is set.
unset TCG_SOLVER_PATH

# The CEGIS superoptimiser and the AY regalloc differential shell out to an
# `ay` BINARY. Without one they fail on the environment rather than the code,
# so auto mode skips exactly these names and records every skip.
SOLVER_SKIP_TESTS="test_cegis_cache_hit_on_repeat
test_cegis_codegen_layer_a_mul_zero_i32_matches_hand_movz
test_cegis_codegen_layer_b_movz_add_max_imm12_matches_hand_addri
test_cegis_codegen_layer_b_movz_add_small_imm_matches_hand_addri
test_cegis_flag_is_noop_when_disabled
test_cegis_flag_runs_pass
test_full_pipeline_with_cegis_flag
ay_pbo_aarch64_execution_differential
natural_keep_better_does_not_keep_worse_whole_vreg_ay
teeth_ay_path_detects_a_corrupted_instruction"

# Sets RESOLVED_PATH/RESOLVED_ROUTE/RESOLVED_PINNING and RESOLVE_STATUS
# (0 found, 3 absent, 4 invalid explicit override) for `ay` or `clean`.
resolve_proof_tool() {
    RESOLVED_PATH=
    RESOLVED_ROUTE=
    RESOLVED_PINNING=
    set +e
    resolved=$(python3 -B "${SUMMARY_TOOL}" resolve --tool "$1" --host "${host_target}")
    RESOLVE_STATUS=$?
    set -e
    case "${RESOLVE_STATUS}" in
        0)
            RESOLVED_PATH=$(printf '%s\n' "${resolved}" | cut -f1)
            RESOLVED_ROUTE=$(printf '%s\n' "${resolved}" | cut -f2)
            RESOLVED_PINNING=$(printf '%s\n' "${resolved}" | cut -f3)
            ;;
        3|4) ;;
        *)
            echo "run_public_release_codegen_tests: proof-tool resolution failed (exit ${RESOLVE_STATUS})" >&2
            exit 1
            ;;
    esac
}

OWN_SUMMARY=0
CURRENT_LANE=
summary() {
    python3 -B "${SUMMARY_TOOL}" "$@" --path "${SUMMARY_PATH}"
}
begin_lane() {
    CURRENT_LANE=$1
    summary lane --name "$1" --status running
}
end_lane() {
    summary lane --name "${CURRENT_LANE}" --status pass
    CURRENT_LANE=
}
on_exit() {
    status=$?
    trap - EXIT
    if [ -n "${CURRENT_LANE}" ]; then
        summary lane --name "${CURRENT_LANE}" --status fail --detail "exit status ${status}" >/dev/null 2>&1 || true
    fi
    if [ "${OWN_SUMMARY}" -eq 1 ] && [ "${status}" -ne 0 ]; then
        summary finish --status fail >/dev/null || true
        echo "run_public_release_codegen_tests: FAIL (summary ${SUMMARY_PATH})" >&2
    fi
    exit "${status}"
}

# Attach to the caller's summary, or create a retained one for a standalone run.
open_summary() {
    if [ -n "${SUMMARY_PATH}" ]; then
        if [ ! -f "${SUMMARY_PATH}" ]; then
            echo "run_public_release_codegen_tests: --summary document does not exist: ${SUMMARY_PATH}" >&2
            exit 2
        fi
    else
        summary_dir=$(mktemp -d "${TMPDIR:-/tmp}/trust-cg-public-release-codegen.XXXXXX")
        SUMMARY_PATH="${summary_dir}/summary.json"
        summary_gate=run_public_release_codegen_tests
        if [ "${ACTION}" = --qualify-kernel-layout-fixtures ]; then
            summary_gate=kernel_layout_fixture_qualification
        fi
        summary init --gate "${summary_gate}" --mode "${PROOF_GATE}" \
            --host "${host_target}" --evidence-dir "${summary_dir}" \
            --command "$0 ${ORIGINAL_ARGS}" >&2
        OWN_SUMMARY=1
    fi
    trap on_exit EXIT
    trap 'exit 129' HUP
    trap 'exit 130' INT
    trap 'exit 143' TERM
}

# Resolve the proof tools, record the lanes this action will run and every
# exclusion it applies, then refuse in require mode or announce in auto mode.
AY_AVAILABLE=0
plan_proof_tools() {
    resolve_proof_tool ay
    AY_PATH=${RESOLVED_PATH}
    AY_ROUTE=${RESOLVED_ROUTE}
    AY_PINNING=${RESOLVED_PINNING}
    AY_STATUS=${RESOLVE_STATUS}
    resolve_proof_tool clean
    CLEAN_PATH=${RESOLVED_PATH}
    CLEAN_ROUTE=${RESOLVED_ROUTE}
    CLEAN_PINNING=${RESOLVED_PINNING}
    CLEAN_STATUS=${RESOLVE_STATUS}
    if [ "${PROOF_GATE}" = require ]; then
        if [ "${AY_PINNING}" != pinned ] || [ "${CLEAN_PINNING}" != pinned ]; then
            echo "run_public_release_codegen_tests: proof gate 'require' needs AY and Clean through a pinned route" >&2
            echo "  (AY: ${AY_PATH:-unresolved} ${AY_ROUTE:-status ${AY_STATUS}}; Clean: ${CLEAN_PATH:-unresolved} ${CLEAN_ROUTE:-status ${CLEAN_STATUS}})." >&2
            echo "  Set AY_SOLVER_PATH and TCG_EXTERNAL_CLEAN_CHECKER to absolute executables or build with a Trust toolchain that ships its AY and install aterm's managed clean." >&2
            exit 1
        fi
    fi
    if [ -n "${AY_PATH}" ]; then
        AY_AVAILABLE=1
    fi
    if [ "${OWN_SUMMARY}" -eq 1 ] && { [ -n "${AY_PATH}" ] || [ -n "${CLEAN_PATH}" ]; }; then
        set --
        if [ -n "${AY_PATH}" ]; then
            set -- "$@" --ay "${AY_PATH}" --ay-route "${AY_ROUTE}"
        fi
        if [ -n "${CLEAN_PATH}" ]; then
            set -- "$@" --clean "${CLEAN_PATH}" --clean-route "${CLEAN_ROUTE}"
        fi
        summary solver "$@"
    fi
}

plan_codegen_lanes() {
    plan_action=$1
    plan_proof_tools

    runs_complement=0
    runs_capstones=0
    case "${plan_action}" in
        --release|--plan)
            runs_complement=1
            runs_capstones=1
            ;;
        --complement)
            runs_complement=1
            ;;
        "")
            runs_capstones=1
            ;;
    esac
    if [ "${runs_complement}" -eq 1 ]; then
        solver_tests=$(printf '%s\n' "${SOLVER_SKIP_TESTS}" | tr '\n' ' ' | sed 's/ $//')
        if [ "${AY_AVAILABLE}" -eq 1 ]; then
            solver_detail="; AY-backed tests included, not skipped: ${solver_tests}"
        else
            solver_detail="; AY-backed tests skipped: ${solver_tests}"
        fi
        if [ "${CAPSTONE_HOST}" -eq 1 ]; then
            source_bound_detail="; the 25 source-bound object/JIT tests then run exactly, one bounded cargo process each"
        else
            source_bound_detail=
        fi
        summary lane --name codegen-complement --status planned \
            --detail "every non-capstone trust-cg-codegen lib/bin/example/integration test; --exact skips for the 52 capstones${source_bound_detail}${solver_detail}"
        summary lane --name codegen-doctests --status planned \
            --detail "trust-cg-codegen doctests"
        if [ "${AY_AVAILABLE}" -eq 0 ]; then
            if [ "${AY_STATUS}" -eq 4 ]; then
                ay_reason="the explicit AY_SOLVER_PATH override is not an absolute path to an executable"
            else
                ay_reason="no AY solver resolvable: the build toolchain's sysroot ships no bin/ay; build with a Trust toolchain that ships its AY, or set an absolute AY_SOLVER_PATH (TCG_SOLVER_PATH alias) to a copy of that exact AY"
            fi
            summary exclusion --lane codegen-complement --kind cargo-skip \
                --value "${solver_tests}" \
                --reason "${ay_reason}"
        fi
    else
        summary exclusion --lane codegen-complement --kind not-run \
            --value "all non-capstone trust-cg-codegen tests and doctests" \
            --reason "capstone-only mode does not run the complement"
    fi
    if [ "${runs_capstones}" -eq 1 ] && [ "${CAPSTONE_HOST}" -eq 1 ]; then
        summary lane --name codegen-capstones --status planned \
            --detail "52 exact policy tests, one bounded cargo process each"
    elif [ "${runs_capstones}" -eq 1 ]; then
        summary lane --name codegen-capstones --status excluded \
            --detail "in-process JIT capstones are qualified only on aarch64-apple-darwin"
        summary exclusion --lane codegen-capstones --kind host --value "52 exact policy tests" \
            --reason "the capstones are in-process JIT differentials not qualified on ${host_target}"
    else
        summary exclusion --lane codegen-capstones --kind not-run --value "52 exact policy tests" \
            --reason "--complement skips the capstones without running them"
    fi

    codegen_blockers=$(summary blockers --lane-prefix codegen-)
    if [ -n "${codegen_blockers}" ]; then
        printf '%s\n' "${codegen_blockers}" | while IFS= read -r blocker; do
            echo "!!! run_public_release_codegen_tests: NON-QUALIFYING: ${blocker} !!!" >&2
        done
        if [ "${PROOF_GATE}" = require ]; then
            echo "run_public_release_codegen_tests: proof gate 'require' refuses every exclusion; nothing was run" >&2
            exit 1
        fi
    fi
}

run_complement() {
    validate_policy

    set -- test --locked -p trust-cg-codegen --all-features \
        --lib --bins --examples --tests \
        --no-fail-fast -- --exact --test-threads="${RUST_TEST_THREADS}"
    for test_name in $(policy_test_names) $(host_source_bound_test_names); do
        set -- "$@" --skip "${test_name}"
    done
    if [ "${AY_AVAILABLE}" -eq 0 ]; then
        echo "!!! run_public_release_codegen_tests: NO AY SOLVER -- skipping the CEGIS superopt and" >&2
        echo "!!! AY regalloc differential tests. This run is NON-QUALIFYING; every skip is recorded" >&2
        echo "!!! in ${SUMMARY_PATH}" >&2
        for test_name in ${SOLVER_SKIP_TESTS}; do
            set -- "$@" --skip "${test_name}"
        done
    fi
    echo ">>> public-release codegen complement (all non-capstone tests)"
    begin_lane codegen-complement
    run_cargo_with_timeout 36000 "$@"
    run_source_bound_policy
    end_lane

    echo ">>> public-release codegen doctests"
    begin_lane codegen-doctests
    run_cargo_with_timeout 3600 \
        test --locked -p trust-cg-codegen --all-features --doc -- \
            --test-threads="${RUST_TEST_THREADS}"
    end_lane
    echo "Public-release codegen complement: PASS"
}

run_capstones() {
    begin_lane codegen-capstones
    run_policy
    end_lane
}

# Close a standalone summary; a caller-owned summary is finished by its caller.
finish_codegen() {
    if [ "${OWN_SUMMARY}" -eq 1 ]; then
        trap - EXIT
        if [ "${PROOF_GATE}" = require ] && [ "$1" = pass ] \
            && [ "${ACTION}" != --qualify-kernel-layout-fixtures ]; then
            summary finish --status "$1" --require-qualifying >/dev/null
        else
            summary finish --status "$1" >/dev/null
        fi
    fi
}

case "${ACTION}" in
    --qualify-kernel-layout-fixtures)
        open_summary
        validate_policy_shape
        plan_proof_tools
        LAYOUT_EVIDENCE_DIR="$(dirname -- "${SUMMARY_PATH}")/kernel-layout-fixtures"
        if [ -e "${LAYOUT_EVIDENCE_DIR}" ]; then
            echo "run_public_release_codegen_tests: refusing to overwrite retained layout evidence ${LAYOUT_EVIDENCE_DIR}" >&2
            exit 1
        fi
        mkdir "${LAYOUT_EVIDENCE_DIR}"
        policy_rows >"${LAYOUT_EVIDENCE_DIR}/policy.txt"
        layout_targets=$(awk -F '|' 'NF { count += 1 } END { print count + 0 }' \
            "${LAYOUT_EVIDENCE_DIR}/policy.txt")
        layout_total=$(awk -F '|' '{ count += $2 } END { print count + 0 }' \
            "${LAYOUT_EVIDENCE_DIR}/policy.txt")
        if [ "${layout_targets}" -ne 11 ]; then
            echo "run_public_release_codegen_tests: kernel-layout policy must name eleven targets" >&2
            exit 1
        fi
        summary lane --name kernel-layout-fixtures --status planned \
            --output "${LAYOUT_EVIDENCE_DIR}" \
            --detail "${layout_total} cases across ${layout_targets} pinned targets; each compiled case executes alone; existing fixtures unchanged; compiler ${actual_trustc}; host ${host_target}; targo ${actual_targo}; layout differential only, not full release or proof qualification"
        begin_lane kernel-layout-fixtures
        RUN_ALL_TARGET_TESTS=1
        # Redirection keeps the per-case counter in this process. A pipeline
        # would hide an incomplete execution count in its subshell.
        run_rows <"${LAYOUT_EVIDENCE_DIR}/policy.txt"
        RUN_ALL_TARGET_TESTS=0
        if [ "${LAYOUT_CASES_EXECUTED}" -ne "${layout_total}" ]; then
            echo "run_public_release_codegen_tests: kernel-layout execution count is incomplete" >&2
            exit 1
        fi
        end_lane
        finish_codegen pass
        echo "Kernel-layout fixture qualification: PASS (${LAYOUT_CASES_EXECUTED}/${layout_total} cases, ${layout_targets} targets, isolated execution; not full release or proof qualification)"
        ;;
    --release)
        open_summary
        plan_codegen_lanes --release
        validate_policy_shape
        runner_self_test
        run_complement
        if [ "${CAPSTONE_HOST}" -eq 1 ]; then
            run_capstones
            finish_codegen pass
            echo "Public-release codegen: PASS (complement, doctests and 52/52 exact capstones)"
        else
            finish_codegen pass
            echo "Public-release codegen: PASS (complement and doctests; the 52 capstones are EXCLUDED on ${host_target} -- NON-QUALIFYING)"
        fi
        ;;
    --plan)
        open_summary
        plan_codegen_lanes --plan
        validate_policy_shape
        finish_codegen dry-run
        echo "Public-release codegen plan recorded in ${SUMMARY_PATH}"
        ;;
    --self-test)
        validate_policy_shape
        runner_self_test
        ;;
    --validate-policy)
        validate_policy
        if [ "${CAPSTONE_HOST}" -eq 1 ]; then
            echo "Public-release generated codegen policy: PASS (52 exact tests; 25 source-bound object/JIT tests)"
        else
            echo "Public-release generated codegen policy: PASS (52 exact tests)"
        fi
        ;;
    --complement)
        open_summary
        plan_codegen_lanes --complement
        run_complement
        finish_codegen pass
        ;;
    "")
        open_summary
        plan_codegen_lanes ""
        validate_policy_shape
        validate_global_policy_inventory
        run_capstones
        finish_codegen pass
        echo "Public-release generated codegen capstones: PASS (52/52 exact tests)"
        ;;
esac
