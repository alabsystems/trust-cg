#!/bin/sh
#
# Fail-closed public-release gate for the generated Clean-kernel codegen
# capstones merged into the v0.1.0 candidate.
#
# These JIT-heavy tests must not share a libtest process: accumulated JIT state
# has previously made an otherwise-correct aggregate run unreliable.  Pin the
# exact libtest inventory, then execute every release-selected test in its own
# bounded cargo process with one test thread.

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
    for arg in "$@"; do
        if [ "${arg}" = "--list" ]; then
            is_list=1
        fi
        if [ "${arg}" = "--all-features" ]; then
            has_all_features=1
        fi
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
    exit 0
fi

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
REPO_ROOT=$(CDPATH= cd -- "${SCRIPT_DIR}/.." && pwd)
RUN_WITH_TIMEOUT="${SCRIPT_DIR}/run_with_timeout.py"
cd "${REPO_ROOT}"

if ! command -v cargo >/dev/null 2>&1; then
    echo "run_public_release_codegen_tests: cargo not found on PATH" >&2
    exit 1
fi
if ! command -v rustc >/dev/null 2>&1; then
    echo "run_public_release_codegen_tests: rustc not found on PATH" >&2
    exit 1
fi
if ! command -v python3 >/dev/null 2>&1; then
    echo "run_public_release_codegen_tests: python3 is required for bounded test processes" >&2
    exit 1
fi
if [ ! -x "${RUN_WITH_TIMEOUT}" ]; then
    echo "run_public_release_codegen_tests: missing executable timeout runner ${RUN_WITH_TIMEOUT}" >&2
    exit 1
fi

# The selected kernel fixtures contain compiler-specific repr(Rust) layouts
# and ABI decisions.  The root rust-toolchain file pins this identity; assert
# it again here so an override cannot route an unknown compiler through the
# current-fixture branch and turn a stale-layout mismatch into memory unsafety.
expected_rustc='rustc 1.97.1 (8bab26f4f 2026-07-14)'
expected_cargo='cargo 1.97.1 (c980f4866 2026-06-30)'
actual_rustc=$(rustc --version)
actual_cargo=$(cargo --version)
if [ "${actual_rustc}" != "${expected_rustc}" ]; then
    echo "run_public_release_codegen_tests: expected ${expected_rustc}, got ${actual_rustc}" >&2
    exit 1
fi
if [ "${actual_cargo}" != "${expected_cargo}" ]; then
    echo "run_public_release_codegen_tests: expected ${expected_cargo}, got ${actual_cargo}" >&2
    exit 1
fi
host_target=$(rustc -vV | sed -n 's/^host: //p')
if [ "${host_target}" != "aarch64-apple-darwin" ]; then
    echo "run_public_release_codegen_tests: expected aarch64-apple-darwin host, got ${host_target:-unknown}" >&2
    exit 1
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
        run_with_timeout "${cargo_timeout}" cargo "$@"
    fi
}

RUN_EXACT_TESTS=1

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
    if [ "${expected_total}" -le 0 ] || [ "${expected_selected}" -le 0 ]; then
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

    if [ "${RUN_EXACT_TESTS}" -eq 1 ]; then
        for test_name in "$@"; do
            echo ">>> public-release codegen test: ${target}::${test_name}"
            run_cargo_with_timeout 600 \
                test --locked -p trust-cg-codegen --all-features \
                --test "${target}" -- \
                    --exact "${test_name}" --include-ignored --test-threads=1
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

    if run_with_timeout 5 sh -c 'kill -SEGV $$'; then
        echo "run_public_release_codegen_tests: signal self-test unexpectedly passed" >&2
        return 1
    else
        status=$?
    fi
    if [ "${status}" -ne 139 ]; then
        echo "run_public_release_codegen_tests: expected SIGSEGV status 139, got ${status}" >&2
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

    unset TCG_RELEASE_FAKE_CARGO_MODE
    SELF_TEST_FAKE_CARGO=0

    if RUSTUP_TOOLCHAIN=1.95.0 sh "$0" >/dev/null 2>&1; then
        echo "run_public_release_codegen_tests: incompatible toolchain override was accepted" >&2
        return 1
    fi

    echo "Public-release codegen runner self-test: PASS"
}

policy_rows() {
    cat <<'EOF'
e2e_binding_defeq|5|5|full|bd_module_sanity_and_inmodule_surface bd_probe_binding_differential bd_decl_gate_full_differential bd_blind_divergence_differential bd_armed_module_corruption_diverges
e2e_defeq_cache|8|8|full|cache_module_sanity_and_wiring cache_transparency_hit_equals_miss cache_guard_1773_soundness_centerpiece cache_equiv_manager_union_find cache_branch_sharing_3402 cache_poisoned_value_control cache_armed_fnv_corruption_control cache_full_native_jit_sweep_and_poison_push
e2e_eta_struct_ext|3|3|full|mir_eta_struct_params_roundtrip mir_eta_struct_proj_nested_roundtrip mir_expand_eta_struct_recursor_major_roundtrip
e2e_ctx_whnf_defeq|5|5|full|cw_module_sanity_and_inmodule_surface cw_probe_ctx_consults_differential cw_decl_gate_full_differential cw_blind_divergence_differential cw_armed_module_corruption_diverges
e2e_fvar_opening|4|4|full|fv_module_sanity_and_inmodule_surface fv_probe_fvar_discipline_differential fv_decl_gate_full_differential fv_armed_module_corruption_diverges
e2e_lazy_delta|5|5|full|ld_module_sanity_and_inmodule_surface ld_probe_lazy_delta_differential ld_decl_gate_full_differential ld_blind_divergence_differential ld_armed_module_corruption_diverges
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
    for test_name in $(policy_test_names); do
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

run_policy() {
    policy_rows | while IFS='|' read -r target expected_total expected_selected coverage names; do
        [ -n "${target}" ] || continue
        set -f
        # Policy names are controlled Rust identifiers separated by spaces.
        set -- ${names}
        run_target "${target}" "${expected_total}" "${expected_selected}" "${coverage}" "$@"
    done
}

validate_policy() {
    validate_policy_shape
    validate_global_policy_inventory
    RUN_EXACT_TESTS=0
    run_policy
    RUN_EXACT_TESTS=1
}

tcg_solver_present() {
    [ -n "${TCG_SOLVER_PATH:-}" ] && [ -x "${TCG_SOLVER_PATH}" ] && return 0
    command -v ay >/dev/null 2>&1 && return 0
    for root in "$HOME/trust" "$HOME"; do
        [ -x "$root/build/aarch64-apple-darwin/stage2/bin/ay" ] && return 0
        [ -x "$root/first-party/ay/target/release/ay" ] && return 0
        [ -x "$root/ay/target/release/ay" ] && return 0
    done
    return 1
}

run_complement() {
    validate_policy

    set -- test --locked -p trust-cg-codegen --all-features \
        --lib --bins --examples --tests \
        --no-fail-fast -- --exact --test-threads=1
    for test_name in $(policy_test_names); do
        set -- "$@" --skip "${test_name}"
    done
    # The CEGIS superoptimiser and the AY regalloc differential shell out to an
    # `ay` BINARY, discovered through the Trust toolchain layout. The public-clone
    # release gate runs with a fresh HOME and an isolated tree by design, so no
    # solver is discoverable there and these fail on the ENVIRONMENT, not the
    # code — they pass wherever a solver exists. Skip them only in that case, and
    # say so, exactly as run_public_release_checks.sh does for the workspace lane.
    if ! tcg_solver_present; then
        echo "run_public_release_codegen_tests: NO AY SOLVER FOUND -- skipping the" >&2
        echo "  CEGIS superopt and AY regalloc differential tests. This release is" >&2
        echo "  verified MODULO those lanes. Set TCG_SOLVER_PATH or put \`ay\` on PATH." >&2
        for test_name in \
            test_cegis_cache_hit_on_repeat \
            test_cegis_codegen_layer_a_mul_zero_i32_matches_hand_movz \
            test_cegis_codegen_layer_b_movz_add_max_imm12_matches_hand_addri \
            test_cegis_codegen_layer_b_movz_add_small_imm_matches_hand_addri \
            test_cegis_flag_is_noop_when_disabled \
            test_cegis_flag_runs_pass \
            test_full_pipeline_with_cegis_flag \
            ay_pbo_aarch64_execution_differential \
            natural_keep_better_does_not_keep_worse_whole_vreg_ay \
            teeth_ay_path_detects_a_corrupted_instruction; do
            set -- "$@" --skip "${test_name}"
        done
    fi
    echo ">>> public-release codegen complement (all non-capstone tests)"
    run_cargo_with_timeout 36000 "$@"

    echo ">>> public-release codegen doctests"
    run_cargo_with_timeout 3600 \
        test --locked -p trust-cg-codegen --all-features --doc -- \
            --test-threads=1
    echo "Public-release codegen complement: PASS"
}

case "${1-}" in
    --release)
        if [ "$#" -ne 1 ]; then
            echo "usage: $0 [--release|--self-test|--validate-policy|--complement]" >&2
            exit 2
        fi
        validate_policy_shape
        runner_self_test
        run_complement
        run_policy
        ;;
    --self-test)
        if [ "$#" -ne 1 ]; then
            echo "usage: $0 [--release|--self-test|--validate-policy|--complement]" >&2
            exit 2
        fi
        validate_policy_shape
        runner_self_test
        exit 0
        ;;
    --validate-policy)
        if [ "$#" -ne 1 ]; then
            echo "usage: $0 [--release|--self-test|--validate-policy|--complement]" >&2
            exit 2
        fi
        validate_policy
        echo "Public-release generated codegen policy: PASS (52 exact tests)"
        exit 0
        ;;
    --complement)
        if [ "$#" -ne 1 ]; then
            echo "usage: $0 [--release|--self-test|--validate-policy|--complement]" >&2
            exit 2
        fi
        run_complement
        exit 0
        ;;
    "")
        validate_policy_shape
        validate_global_policy_inventory
        run_policy
        ;;
    *)
        echo "usage: $0 [--release|--self-test|--validate-policy|--complement]" >&2
        exit 2
        ;;
esac

echo "Public-release generated codegen capstones: PASS (52/52 exact tests)"
