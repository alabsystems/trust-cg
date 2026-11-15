//! Process-isolated contracts for embedder-installed library policy.
//! These are stock-Rust library tests, not rustc backend session tests.

use std::num::NonZeroUsize;
use std::process::Command;
use trust_cg_process_env::resource_budget::{
    TRUST_CG_MAX_PARALLELISM_ENV, capture_positive_usize_control,
    install_optional_positive_usize_control, install_positive_usize_control,
};
use trust_cg_verify::{bridge_coverage, diag};

fn in_child(test: &str) -> bool {
    const CHILD: &str = "POLICY_INSTALL_TEST_CHILD";
    if std::env::var(CHILD).as_deref() == Ok(test) {
        return true;
    }
    let output = Command::new(std::env::current_exe().expect("test binary"))
        .args(["--exact", test, "--nocapture", "--test-threads=1"])
        .env(CHILD, test)
        .env_remove("TCG_DIAG_JSON")
        .env_remove("TCG_BRIDGE_COVERAGE")
        .env_remove("TCG_BRIDGE_COVERAGE_STRICT")
        .env_remove(TRUST_CG_MAX_PARALLELISM_ENV)
        .output()
        .expect("isolated policy test child");
    println!("{}", String::from_utf8_lossy(&output.stdout));
    eprintln!("{}", String::from_utf8_lossy(&output.stderr));
    assert!(
        output.status.success(),
        "isolated {test}: {}",
        output.status
    );
    false
}

#[test]
fn diagnostic_equal_install_is_idempotent() {
    if !in_child("diagnostic_equal_install_is_idempotent") {
        return;
    }
    assert!(diag::set_json_enabled(false));
    assert!(
        diag::set_json_enabled(false),
        "equal policy must be compatible"
    );
    assert!(!diag::json_enabled());
}

#[test]
fn coverage_equal_install_is_idempotent() {
    if !in_child("coverage_equal_install_is_idempotent") {
        return;
    }
    assert!(bridge_coverage::set_recorder_defaults(false, true));
    assert!(bridge_coverage::set_recorder_defaults(false, true));
    let mut recorder = bridge_coverage::CoverageRecorder::from_env();
    assert!(recorder.is_strict());
    assert!(
        recorder
            .record_terminator(bridge_coverage::TerminatorShape::InlineAsm)
            .is_err()
    );
}

#[test]
fn resource_equal_install_is_idempotent() {
    if !in_child("resource_equal_install_is_idempotent") {
        return;
    }
    let cap = NonZeroUsize::new(2).unwrap();
    assert!(install_positive_usize_control(
        TRUST_CG_MAX_PARALLELISM_ENV,
        cap
    ));
    assert!(install_positive_usize_control(
        TRUST_CG_MAX_PARALLELISM_ENV,
        cap
    ));
    assert_eq!(
        capture_positive_usize_control(TRUST_CG_MAX_PARALLELISM_ENV),
        Ok(Some(cap))
    );
}

#[test]
fn conflicting_library_settings_are_refused_without_replacement() {
    if !in_child("conflicting_library_settings_are_refused_without_replacement") {
        return;
    }
    assert!(diag::set_json_enabled(false));
    assert!(!diag::set_json_enabled(true));
    assert!(!diag::json_enabled());
    assert!(bridge_coverage::set_recorder_defaults(false, false));
    assert!(!bridge_coverage::set_recorder_defaults(true, true));
    assert!(!bridge_coverage::CoverageRecorder::from_env().is_strict());
    let cap = NonZeroUsize::new(2).unwrap();
    assert!(install_positive_usize_control(
        TRUST_CG_MAX_PARALLELISM_ENV,
        cap
    ));
    assert!(!install_positive_usize_control(
        TRUST_CG_MAX_PARALLELISM_ENV,
        NonZeroUsize::new(8).unwrap()
    ));
    assert_eq!(
        capture_positive_usize_control(TRUST_CG_MAX_PARALLELISM_ENV),
        Ok(Some(cap))
    );
}

#[test]
fn installed_absent_cap_is_not_uninstalled_environment_fallback() {
    if !in_child("installed_absent_cap_is_not_uninstalled_environment_fallback") {
        return;
    }
    trust_cg_process_env::with_env_overrides(&[(TRUST_CG_MAX_PARALLELISM_ENV, "64")], || {
        assert_eq!(
            capture_positive_usize_control(TRUST_CG_MAX_PARALLELISM_ENV),
            Ok(NonZeroUsize::new(64))
        );
        assert!(install_optional_positive_usize_control(
            TRUST_CG_MAX_PARALLELISM_ENV,
            None
        ));
        assert!(install_optional_positive_usize_control(
            TRUST_CG_MAX_PARALLELISM_ENV,
            None
        ));
        assert_eq!(
            capture_positive_usize_control(TRUST_CG_MAX_PARALLELISM_ENV),
            Ok(None)
        );
        assert!(!install_positive_usize_control(
            TRUST_CG_MAX_PARALLELISM_ENV,
            NonZeroUsize::new(2).unwrap()
        ));
        assert_eq!(
            capture_positive_usize_control(TRUST_CG_MAX_PARALLELISM_ENV),
            Ok(None)
        );
    });
}

#[test]
fn installed_explicit_cap_refuses_default_reinstallation() {
    if !in_child("installed_explicit_cap_refuses_default_reinstallation") {
        return;
    }
    let cap = NonZeroUsize::new(2).unwrap();
    assert!(install_positive_usize_control(
        TRUST_CG_MAX_PARALLELISM_ENV,
        cap
    ));
    assert!(!install_optional_positive_usize_control(
        TRUST_CG_MAX_PARALLELISM_ENV,
        None
    ));
    trust_cg_process_env::with_env_overrides(&[(TRUST_CG_MAX_PARALLELISM_ENV, "64")], || {
        assert_eq!(
            capture_positive_usize_control(TRUST_CG_MAX_PARALLELISM_ENV),
            Ok(Some(cap))
        );
    });
}

#[test]
fn enabled_and_strict_policies_cannot_be_replaced_with_weaker_settings() {
    if !in_child("enabled_and_strict_policies_cannot_be_replaced_with_weaker_settings") {
        return;
    }
    assert!(diag::set_json_enabled(true));
    assert!(!diag::set_json_enabled(false));
    assert!(diag::json_enabled());
    assert!(bridge_coverage::set_recorder_defaults(true, true));
    assert!(!bridge_coverage::set_recorder_defaults(false, false));
    assert!(bridge_coverage::CoverageRecorder::from_env().is_strict());
}

#[test]
fn equal_worker_default_is_compatible_after_budget_capture() {
    if !in_child("equal_worker_default_is_compatible_after_budget_capture") {
        return;
    }
    use trust_cg_verify::resource_limits::*;
    assert!(install_optional_positive_usize_control(
        TRUST_CG_MAX_PARALLELISM_ENV,
        None
    ));
    assert!(configure_proof_verifier_default_worker_limit(1));
    assert_eq!(try_proof_verifier_worker_limit(), Ok(1));
    assert!(configure_proof_verifier_default_worker_limit(1));
    assert!(!configure_proof_verifier_default_worker_limit(8));
    assert_eq!(try_proof_verifier_worker_limit(), Ok(1));
}
