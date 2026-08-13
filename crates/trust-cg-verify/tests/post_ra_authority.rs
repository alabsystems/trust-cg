use trust_cg_verify::env_lock;
use trust_cg_verify::post_ra_dataflow::{X86_POST_RA_DATAFLOW_DEFAULT, post_ra_dataflow_mode};
use trust_cg_verify::post_regalloc_recheck::{
    AARCH64_POST_RA_RECHECK_DEFAULT, PostRegallocRecheckMode, X86_POST_RA_RECHECK_DEFAULT,
    post_regalloc_recheck_mode,
};

#[test]
fn environment_cannot_downgrade_production_post_ra_correctness_gates() {
    // Even with both downgrade knobs set, the production correctness gates stay
    // Enforce. The thread-local overrides are restored on scope exit, even on
    // panic, and cannot affect sibling tests.
    env_lock::with_env_overrides(
        &[
            ("TCG_POST_RA_DATAFLOW", "off"),
            ("TCG_POST_RA_RECHECK", "warn"),
        ],
        || {
            assert_eq!(
                X86_POST_RA_DATAFLOW_DEFAULT,
                PostRegallocRecheckMode::Enforce
            );
            assert_eq!(post_ra_dataflow_mode(), PostRegallocRecheckMode::Enforce);
            assert_eq!(
                X86_POST_RA_RECHECK_DEFAULT,
                PostRegallocRecheckMode::Enforce
            );
            assert_eq!(
                AARCH64_POST_RA_RECHECK_DEFAULT,
                PostRegallocRecheckMode::Enforce
            );
            assert_eq!(
                post_regalloc_recheck_mode(X86_POST_RA_RECHECK_DEFAULT),
                PostRegallocRecheckMode::Enforce
            );
            assert_eq!(
                post_regalloc_recheck_mode(AARCH64_POST_RA_RECHECK_DEFAULT),
                PostRegallocRecheckMode::Enforce
            );
        },
    );
}
