//! Stock-Rust compilation of the actual compiler-independent backend parser.
//! This exercises policy installation, not rustc-private backend wiring.

// The backend consumes all accessors; this test target consumes only its pure
// parser/installation contracts and deliberately does not fake a Session.
#[allow(dead_code)]
#[path = "../../rustc-codegen-trust-cg/src/knobs.rs"]
mod knobs;

#[test]
fn actual_global_install_and_library_error_propagation() {
    knobs::install(&["no-proof-certs=1".to_owned()]).unwrap();
    assert!(knobs::is_enabled(knobs::NO_PROOF_CERTS));
    knobs::install(&["no-proof-certs".to_owned()]).unwrap();
    assert!(knobs::install(&["no-proof-certs=0".to_owned()]).is_err());
    assert!(knobs::is_enabled(knobs::NO_PROOF_CERTS));

    // Exercise exactly the same first/equal boolean-to-error boundary used by
    // lib::init with real library conflicts, without pretending to run rustc.
    knobs::require_compatible_policy(
        knobs::DIAG_JSON,
        trust_cg_verify::diag::set_json_enabled(false),
    )
    .unwrap();
    assert!(
        knobs::require_compatible_policy(
            knobs::DIAG_JSON,
            trust_cg_verify::diag::set_json_enabled(true)
        )
        .is_err()
    );
    knobs::require_compatible_policy(
        knobs::BRIDGE_COVERAGE_STRICT,
        trust_cg_verify::bridge_coverage::set_recorder_defaults(false, false),
    )
    .unwrap();
    assert!(
        knobs::require_compatible_policy(
            knobs::BRIDGE_COVERAGE_STRICT,
            trust_cg_verify::bridge_coverage::set_recorder_defaults(true, true)
        )
        .is_err()
    );
    let key = trust_cg_process_env::resource_budget::TRUST_CG_MAX_PARALLELISM_ENV;
    knobs::require_compatible_policy(
        knobs::MAX_PARALLELISM,
        trust_cg_process_env::resource_budget::install_positive_usize_control(
            key,
            std::num::NonZeroUsize::new(2).unwrap(),
        ),
    )
    .unwrap();
    assert!(
        knobs::require_compatible_policy(
            knobs::MAX_PARALLELISM,
            trust_cg_process_env::resource_budget::install_optional_positive_usize_control(
                key, None
            )
        )
        .is_err()
    );
}

#[test]
fn solver_trace_setting_preserves_first_or_equal_installation() {
    assert!(trust_cg_verify::diag::set_solve_trace_enabled(false));
    assert!(trust_cg_verify::diag::set_solve_trace_enabled(false));
    assert!(!trust_cg_verify::diag::set_solve_trace_enabled(true));
    assert!(!trust_cg_verify::diag::solve_trace_enabled());
    assert!(
        knobs::require_compatible_policy(
            knobs::SOLVE_TRACE,
            trust_cg_verify::diag::set_solve_trace_enabled(true),
        )
        .is_err()
    );
}
