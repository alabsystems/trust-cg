// trust-cg-codegen/tests/jit_everywhere_shadow_replay.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_codegen::jit_shadow_replay::{
    ShadowReplayTyNativeFusedSmokeFixture, ShadowReplayTyNativeFusedSmokeRejection,
    ShadowReplayTyNativeFusedSmokeSpec, TY_NATIVE_FUSED_THREE_SPEC_SMOKE_CANONICAL_FIXTURE_SHA256,
    TY_NATIVE_FUSED_THREE_SPEC_SMOKE_ISSUE, TY_NATIVE_FUSED_THREE_SPEC_SMOKE_SCHEMA,
    TY_NATIVE_FUSED_THREE_SPEC_SMOKE_SCHEMA_VERSION, TY_NATIVE_FUSED_THREE_SPEC_SMOKE_SPEC_IDS,
    ty_native_fused_three_spec_smoke_fixture,
};
use trust_cg_codegen::{
    JIT_EVERYWHERE_SHADOW_REPLAY_SCHEMA, JIT_EVERYWHERE_SHADOW_REPLAY_SCHEMA_VERSION,
    ShadowReplayAYChecks, ShadowReplayBundle, ShadowReplayCompilerConfig, ShadowReplayConsumer,
    ShadowReplayDecision, ShadowReplayEvidenceReference, ShadowReplayGenerationFacts,
    ShadowReplayHook, ShadowReplayInputSlice, ShadowReplayObservation, ShadowReplayOutcome,
    ShadowReplayStatus, ShadowReplayTyChecks, Target, compare_shadow_replay,
};

fn compiler_config() -> ShadowReplayCompilerConfig {
    ShadowReplayCompilerConfig::new(
        "pipeline:o3-shadow-only:v1",
        "sha256:codegen-config-shadow-only",
        "proof-policy:v1:require-certificates",
        "profile-schema:block-counters:v1",
    )
}

fn ay_bundle() -> ShadowReplayBundle {
    ShadowReplayBundle::new(
        ShadowReplayConsumer::AY,
        "ay_sparse_substitute",
        "sha256:manifest-ay-sparse-substitute",
        "sha256:source-ay-sparse-substitute",
        "sha256:trust_ir-ay-sparse-substitute",
        "sha256:native-ay-sparse-substitute",
        compiler_config(),
        Target::Aarch64,
        "sha256:target-facts-aarch64-darwin",
        "sha256:proof-report-ay-sparse-substitute",
        ShadowReplayGenerationFacts::new("ay_sparse_substitute", 7, 7, "layout:generation:7"),
        vec![
            ShadowReplayInputSlice::new("solver-program", "sha256:input-solver-program", 4096),
            ShadowReplayInputSlice::new("basis-region", "sha256:input-basis-region", 2048),
        ],
        vec![
            ShadowReplayHook::ImmutableInputs,
            ShadowReplayHook::CopyOnWriteState,
            ShadowReplayHook::ReplayedTrace,
        ],
        "sha256:replay-root-ay-sparse-substitute",
    )
}

fn ty_bundle() -> ShadowReplayBundle {
    ShadowReplayBundle::new(
        ShadowReplayConsumer::Ty,
        "ty_action_cluster",
        "sha256:manifest-ty-action",
        "sha256:source-ty-action",
        "sha256:trust_ir-ty-action",
        "sha256:native-ty-action",
        compiler_config(),
        Target::Aarch64,
        "sha256:target-facts-aarch64-darwin",
        "sha256:proof-report-ty-action",
        ShadowReplayGenerationFacts::new("ty_action", 11, 11, "layout:generation:11"),
        vec![
            ShadowReplayInputSlice::new("state-frontier", "sha256:input-state-frontier", 8192),
            ShadowReplayInputSlice::new("action-trace", "sha256:input-action-trace", 4096),
        ],
        vec![
            ShadowReplayHook::ImmutableInputs,
            ShadowReplayHook::CopyOnWriteState,
            ShadowReplayHook::ReplayedTrace,
            ShadowReplayHook::ShadowTyArena,
        ],
        "sha256:replay-root-ty-action",
    )
}

fn ay_observation(
    status: ShadowReplayStatus,
    result: &str,
    memory: &str,
    witness: &str,
    proof: &str,
) -> ShadowReplayObservation {
    ShadowReplayObservation::new(
        status,
        None,
        result,
        memory,
        Some(ShadowReplayAYChecks::new(true, witness, proof)),
        None,
    )
}

fn ty_observation(
    state_count: u64,
    generated_count: u64,
    fingerprint: &str,
    parent_sequence: &str,
    status: &str,
    callback_visible: &str,
) -> ShadowReplayObservation {
    ShadowReplayObservation::new(
        ShadowReplayStatus::Ok,
        None,
        "sha256:ty-visible-result",
        "sha256:ty-memory-effects",
        None,
        Some(ShadowReplayTyChecks::new(
            state_count,
            generated_count,
            fingerprint,
            parent_sequence,
            status,
            callback_visible,
        )),
    )
}

fn matching_ty_observation() -> ShadowReplayObservation {
    ty_observation(
        19,
        37,
        "sha256:ty-fingerprint",
        "sha256:ty-parent-sequence",
        "sha256:ty-status",
        "sha256:ty-callback-visible",
    )
}

fn ty_three_spec_bundle(spec: &ShadowReplayTyNativeFusedSmokeSpec) -> ShadowReplayBundle {
    ShadowReplayBundle::new(
        ShadowReplayConsumer::Ty,
        format!("ty_native_fused_three_spec_smoke:{}", spec.spec_id),
        format!("sha256:manifest-ty-three-spec-{}", spec.spec_id),
        format!("sha256:source-ty-three-spec-{}", spec.spec_id),
        format!("sha256:trust_ir-ty-three-spec-{}", spec.spec_id),
        format!("sha256:native-ty-three-spec-{}", spec.spec_id),
        ShadowReplayCompilerConfig::new(
            format!(
                "pipeline:native-fused-parent-loop:{}",
                spec.controls.native_fused_parent_loop_opt_level
            ),
            format!(
                "sha256:ty-controls:{}:{}:{}",
                spec.controls.target_triple,
                spec.controls.native_callout_opt_level,
                spec.controls.native_fused_strict
            ),
            "proof-policy:ty-native-fused-three-spec-shadow-only:v1",
            "profile-schema:ty-native-fused-three-spec-smoke:v1",
        ),
        Target::Aarch64,
        format!("sha256:target-facts-{}", spec.controls.target_triple),
        format!("sha256:proof-report-ty-three-spec-{}", spec.spec_id),
        ShadowReplayGenerationFacts::new(
            format!("ty_three_spec_smoke:{}", spec.spec_id),
            spec.state_count,
            spec.state_count,
            format!("layout:native-fused:{}:{}", spec.spec_id, spec.state_count),
        ),
        vec![
            ShadowReplayInputSlice::new(
                "replay-artifact-dir",
                spec.replay_artifact_dir_sha256.clone(),
                spec.generated_count,
            ),
            ShadowReplayInputSlice::new(
                "parent-sequence",
                spec.parent_sequence_sha256.clone(),
                spec.state_count,
            ),
        ],
        vec![
            ShadowReplayHook::ImmutableInputs,
            ShadowReplayHook::CopyOnWriteState,
            ShadowReplayHook::ReplayedTrace,
            ShadowReplayHook::ShadowTyArena,
        ],
        spec.replay_artifact_dir_sha256.clone(),
    )
}

fn ty_three_spec_observation(spec: &ShadowReplayTyNativeFusedSmokeSpec) -> ShadowReplayObservation {
    ShadowReplayObservation::new(
        ShadowReplayStatus::Ok,
        None,
        spec.fingerprint_sha256.clone(),
        spec.replay_artifact_dir_sha256.clone(),
        None,
        Some(spec.to_ty_checks()),
    )
}

fn ty_three_spec_evidence_ref(
    fixture: &ShadowReplayTyNativeFusedSmokeFixture,
    spec: &ShadowReplayTyNativeFusedSmokeSpec,
) -> ShadowReplayEvidenceReference {
    ShadowReplayEvidenceReference::new(
        spec.replay_artifact_dir_sha256.clone(),
        Some(spec.status_sha256.clone()),
    )
    .with_canonical_fixture_sha256(fixture.canonical_fixture_sha256())
}

fn evidence_ref() -> ShadowReplayEvidenceReference {
    ShadowReplayEvidenceReference::new(
        "sha256:shadow-replay-record",
        Some("sha256:shadow-reducer".to_owned()),
    )
}

fn assert_shadow_only(decision: &ShadowReplayDecision) {
    assert!(decision.is_shadow_only());
    assert!(decision.baseline_authoritative);
    assert!(!decision.native_authoritative);
    assert!(decision.side_effects.all_install_authority_blocked());
    assert!(!decision.side_effects.callable_handle_published);
    assert!(!decision.side_effects.installable_cache_hit_accepted);
    assert!(!decision.side_effects.ay_registry_inserted);
    assert!(!decision.side_effects.ty_native_activated);
    assert!(!decision.side_effects.baseline_replaced);
    assert_eq!(decision.side_effects.useful_native_delta, 0);
}

#[test]
fn ty_three_spec_native_fused_smoke_fixture_replays_shadow_only() {
    let fixture = ty_native_fused_three_spec_smoke_fixture();

    assert_eq!(fixture.schema, TY_NATIVE_FUSED_THREE_SPEC_SMOKE_SCHEMA);
    assert_eq!(
        fixture.schema_version,
        TY_NATIVE_FUSED_THREE_SPEC_SMOKE_SCHEMA_VERSION
    );
    assert_eq!(fixture.issue, TY_NATIVE_FUSED_THREE_SPEC_SMOKE_ISSUE);
    assert!(fixture.is_shadow_only_non_promoting());
    assert!(!fixture.product_promotion_allowed);
    assert!(!fixture.useful_native_credit_allowed);
    assert_eq!(
        fixture
            .specs
            .iter()
            .map(|spec| spec.spec_id.as_str())
            .collect::<Vec<_>>(),
        TY_NATIVE_FUSED_THREE_SPEC_SMOKE_SPEC_IDS
    );
    assert_eq!(
        fixture.canonical_fixture_sha256(),
        TY_NATIVE_FUSED_THREE_SPEC_SMOKE_CANONICAL_FIXTURE_SHA256
    );

    for spec in &fixture.specs {
        assert_eq!(
            fixture
                .validate_spec_observation(spec)
                .expect("fixture row should validate"),
            spec
        );
        assert_eq!(spec.controls.target_triple, "aarch64-apple-darwin");
        assert_eq!(spec.controls.native_callout_opt_level, "O3");
        assert_eq!(spec.controls.native_fused_parent_loop_opt_level, "O3");
        assert!(spec.controls.native_fused_strict);

        let bundle = ty_three_spec_bundle(spec);
        let baseline = ty_three_spec_observation(spec);
        let native = baseline.clone();

        assert!(bundle.is_replayable());
        assert_eq!(bundle.replay_root_sha256, spec.replay_artifact_dir_sha256);

        let evidence_reference = ty_three_spec_evidence_ref(&fixture, spec);
        assert_eq!(
            evidence_reference.canonical_fixture_sha256.as_deref(),
            Some(TY_NATIVE_FUSED_THREE_SPEC_SMOKE_CANONICAL_FIXTURE_SHA256)
        );
        let decision = compare_shadow_replay(&bundle, &baseline, &native, Some(evidence_reference));

        assert_eq!(decision.outcome, ShadowReplayOutcome::Match);
        assert_eq!(decision.evidence_code, None);
        assert_eq!(
            decision
                .evidence_reference
                .as_ref()
                .and_then(|reference| reference.canonical_fixture_sha256.as_deref()),
            Some(TY_NATIVE_FUSED_THREE_SPEC_SMOKE_CANONICAL_FIXTURE_SHA256)
        );
        assert_eq!(
            decision.decision_sha256,
            decision.canonical_decision_sha256()
        );
        assert_shadow_only(&decision);

        let missing_fixture_hash = compare_shadow_replay(
            &bundle,
            &baseline,
            &native,
            Some(ShadowReplayEvidenceReference::new(
                spec.replay_artifact_dir_sha256.clone(),
                Some(spec.status_sha256.clone()),
            )),
        );
        assert_eq!(
            missing_fixture_hash.outcome,
            ShadowReplayOutcome::ReplayRejected
        );
        assert_eq!(
            missing_fixture_hash.evidence_code.as_deref(),
            Some("ty_three_spec_fixture_hash_mismatch")
        );
        assert_shadow_only(&missing_fixture_hash);
    }
}

#[test]
fn ty_three_spec_native_fused_smoke_fixture_rejects_stale_or_mutated_evidence() {
    let fixture = ty_native_fused_three_spec_smoke_fixture();
    let base = fixture
        .expected_spec("MCLamportMutex")
        .expect("fixture covers MCLamportMutex")
        .clone();

    let assert_reject =
        |mutated: ShadowReplayTyNativeFusedSmokeSpec,
         expected: ShadowReplayTyNativeFusedSmokeRejection| {
            let rejection = fixture
                .validate_spec_observation(&mutated)
                .expect_err("mutated replay row must reject");
            assert_eq!(rejection, expected);
            assert_eq!(rejection.as_str(), expected.as_str());
        };

    let assert_fixture_reject =
        |mutated: ShadowReplayTyNativeFusedSmokeFixture,
         expected: ShadowReplayTyNativeFusedSmokeRejection| {
            let rejection = mutated
                .validate_spec_observation(&base)
                .expect_err("malformed fixture must reject before accepting row observations");
            assert_eq!(rejection, expected);
            assert_eq!(rejection.as_str(), expected.as_str());
        };

    let mut bad_schema = fixture.clone();
    bad_schema.schema = "trust-cg.ty.native_fused_three_spec_smoke.shadow_replay.bad";
    assert_fixture_reject(
        bad_schema,
        ShadowReplayTyNativeFusedSmokeRejection::MalformedFixtureSchema,
    );

    let mut bad_shadow_flags = fixture.clone();
    bad_shadow_flags.shadow_only = false;
    bad_shadow_flags.product_promotion_allowed = true;
    bad_shadow_flags.useful_native_credit_allowed = true;
    assert_fixture_reject(
        bad_shadow_flags,
        ShadowReplayTyNativeFusedSmokeRejection::ShadowFlagsMismatch,
    );

    let mut missing_required_spec = fixture.clone();
    missing_required_spec.specs.pop();
    assert_fixture_reject(
        missing_required_spec,
        ShadowReplayTyNativeFusedSmokeRejection::SpecSetMismatch,
    );

    let mut unrelated_row_mutation = fixture.clone();
    let unrelated = unrelated_row_mutation
        .specs
        .iter_mut()
        .find(|spec| spec.spec_id != base.spec_id)
        .expect("fixture has an unrelated row");
    unrelated.status_sha256 = "sha256:changed-unrelated-three-spec-status".to_owned();
    assert_ne!(
        unrelated_row_mutation.canonical_fixture_sha256(),
        TY_NATIVE_FUSED_THREE_SPEC_SMOKE_CANONICAL_FIXTURE_SHA256
    );
    assert_fixture_reject(
        unrelated_row_mutation,
        ShadowReplayTyNativeFusedSmokeRejection::CanonicalFixtureHashMismatch,
    );

    let mut missing_spec = base.clone();
    missing_spec.spec_id = "MissingSpec".to_owned();
    assert_reject(
        missing_spec,
        ShadowReplayTyNativeFusedSmokeRejection::MissingSpec,
    );

    let mut stale_commit = base.clone();
    stale_commit.ty_git_commit = "b2467ae55068cecf0558265b19209e9c73d1c874".to_owned();
    assert_reject(
        stale_commit,
        ShadowReplayTyNativeFusedSmokeRejection::StaleTyCommitIdentity,
    );

    let mut wrong_controls = base.clone();
    wrong_controls.controls.native_callout_opt_level = "O1".to_owned();
    assert_reject(
        wrong_controls,
        ShadowReplayTyNativeFusedSmokeRejection::TargetOrO3ControlMismatch,
    );

    let mut missing_replay_root = base.clone();
    missing_replay_root.replay_artifact_dir_sha256.clear();
    assert_reject(
        missing_replay_root,
        ShadowReplayTyNativeFusedSmokeRejection::MissingReplayRoot,
    );

    let mut changed_counts = base.clone();
    changed_counts.generated_count += 1;
    assert_reject(
        changed_counts,
        ShadowReplayTyNativeFusedSmokeRejection::StateGeneratedOrFingerprintMismatch,
    );

    let mut changed_fingerprint = base.clone();
    changed_fingerprint.fingerprint_sha256 = "sha256:changed-fingerprint".to_owned();
    assert_reject(
        changed_fingerprint,
        ShadowReplayTyNativeFusedSmokeRejection::StateGeneratedOrFingerprintMismatch,
    );

    let mut parent_mismatch = base.clone();
    parent_mismatch.parent_sequence_sha256 = "sha256:changed-parent-sequence".to_owned();
    assert_reject(
        parent_mismatch,
        ShadowReplayTyNativeFusedSmokeRejection::ParentSequenceMismatch,
    );

    let mut status_mismatch = base.clone();
    status_mismatch.status_sha256 = "sha256:changed-status".to_owned();
    assert_reject(
        status_mismatch,
        ShadowReplayTyNativeFusedSmokeRejection::StatusDigestMismatch,
    );

    let mut callback_mismatch = base;
    callback_mismatch.callback_visible_sha256 = "sha256:changed-callback-visible".to_owned();
    assert_reject(
        callback_mismatch,
        ShadowReplayTyNativeFusedSmokeRejection::CallbackVisibleMismatch,
    );
}

#[test]
fn jit_everywhere_shadow_replay_matches_ay_without_install_authority() {
    let bundle = ay_bundle();
    let baseline = ay_observation(
        ShadowReplayStatus::Ok,
        "sha256:ay-visible-result",
        "sha256:ay-memory-effects",
        "sha256:ay-witness",
        "sha256:ay-proof",
    );
    let native = baseline.clone();

    assert_eq!(bundle.schema, JIT_EVERYWHERE_SHADOW_REPLAY_SCHEMA);
    assert_eq!(
        bundle.schema_version,
        JIT_EVERYWHERE_SHADOW_REPLAY_SCHEMA_VERSION
    );
    assert_eq!(bundle.issue, 738);
    assert!(bundle.is_replayable());
    // Golden refreshed to the committed `canonical_bundle_sha256` serialization
    // (host/arch-independent: the bundle pins `Target::Aarch64` plus fixed
    // digests). Equal to `bundle.canonical_bundle_sha256()` asserted on the next
    // line; the previous literal was baked from an older framing and was stale,
    // not platform drift.
    assert_eq!(
        bundle.bundle_sha256,
        "sha256:6e7b911b6b2c85ba62d6af8c1fceb4b89142fe85630103ce4f5ed28d4088408a"
    );
    assert_eq!(bundle.bundle_sha256, bundle.canonical_bundle_sha256());

    let decision = compare_shadow_replay(&bundle, &baseline, &native, Some(evidence_ref()));

    assert_eq!(decision.outcome, ShadowReplayOutcome::Match);
    assert_eq!(decision.evidence_code, None);
    assert_eq!(decision.bundle_sha256, bundle.bundle_sha256);
    // Golden refreshed to the committed `canonical_decision_sha256`
    // serialization (host/arch-independent); equal to
    // `decision.canonical_decision_sha256()` asserted just below. Stale literal
    // from an older framing, not platform drift.
    assert_eq!(
        decision.decision_sha256,
        "sha256:a950d5d9d7d02a33a27d201b7f8b8699ab2847ac974d4a4886587946f5c1060a"
    );
    assert_eq!(
        decision.decision_sha256,
        decision.canonical_decision_sha256()
    );
    assert_shadow_only(&decision);
}

#[test]
fn jit_everywhere_shadow_replay_records_ay_witness_mismatch() {
    let bundle = ay_bundle();
    let baseline = ay_observation(
        ShadowReplayStatus::Ok,
        "sha256:ay-visible-result",
        "sha256:ay-memory-effects",
        "sha256:ay-witness-baseline",
        "sha256:ay-proof",
    );
    let native = ay_observation(
        ShadowReplayStatus::Ok,
        "sha256:ay-visible-result",
        "sha256:ay-memory-effects",
        "sha256:ay-witness-native",
        "sha256:ay-proof",
    );

    let decision = compare_shadow_replay(&bundle, &baseline, &native, Some(evidence_ref()));

    assert_eq!(decision.outcome, ShadowReplayOutcome::Mismatch);
    assert_eq!(
        decision.evidence_code.as_deref(),
        Some("ay_witness_or_proof_mismatch")
    );
    assert_shadow_only(&decision);
}

#[test]
fn jit_everywhere_shadow_replay_checks_ty_state_generated_fingerprint_parity() {
    let bundle = ty_bundle();
    let baseline = matching_ty_observation();
    let native_match = matching_ty_observation();
    let native_mismatch = ty_observation(
        19,
        38,
        "sha256:ty-fingerprint",
        "sha256:ty-parent-sequence",
        "sha256:ty-status",
        "sha256:ty-callback-visible",
    );

    let matched = compare_shadow_replay(&bundle, &baseline, &native_match, Some(evidence_ref()));
    // Golden refreshed to the committed `canonical_bundle_sha256` serialization
    // (host/arch-independent); stale literal from an older framing, not drift.
    assert_eq!(
        bundle.bundle_sha256,
        "sha256:28a2f30661cd3fc7dd4392d9666630881fc1db3316947a116176c28fbf014127"
    );
    assert_eq!(matched.outcome, ShadowReplayOutcome::Match);
    // Golden refreshed to the committed `canonical_decision_sha256`
    // serialization (host/arch-independent); stale literal from an older
    // framing, not platform drift.
    assert_eq!(
        matched.decision_sha256,
        "sha256:5ab8e29268455146615d0d1f1fb80da5e775d92971c325372c106f731d0452cd"
    );
    assert_shadow_only(&matched);

    let mismatched =
        compare_shadow_replay(&bundle, &baseline, &native_mismatch, Some(evidence_ref()));
    assert_eq!(mismatched.outcome, ShadowReplayOutcome::Mismatch);
    assert_eq!(
        mismatched.evidence_code.as_deref(),
        Some("ty_state_generated_or_fingerprint_mismatch")
    );
    // Golden refreshed to the committed `canonical_decision_sha256`
    // serialization (host/arch-independent); stale literal from an older
    // framing, not platform drift.
    assert_eq!(
        mismatched.decision_sha256,
        "sha256:1120a00717079fb37a05b0f04739d2b38d88baaa8f43b7305177ed2b2ddb17e8"
    );
    assert_shadow_only(&mismatched);
}

#[test]
fn jit_everywhere_shadow_replay_records_ty_parent_sequence_mismatch() {
    let bundle = ty_bundle();
    let baseline = matching_ty_observation();
    let native = ty_observation(
        19,
        37,
        "sha256:ty-fingerprint",
        "sha256:ty-parent-sequence-native",
        "sha256:ty-status",
        "sha256:ty-callback-visible",
    );

    let decision = compare_shadow_replay(&bundle, &baseline, &native, Some(evidence_ref()));

    assert_eq!(decision.outcome, ShadowReplayOutcome::Mismatch);
    assert_eq!(
        decision.evidence_code.as_deref(),
        Some("ty_parent_sequence_mismatch")
    );
    assert_shadow_only(&decision);
}

#[test]
fn jit_everywhere_shadow_replay_records_ty_status_digest_mismatch() {
    let bundle = ty_bundle();
    let baseline = matching_ty_observation();
    let native = ty_observation(
        19,
        37,
        "sha256:ty-fingerprint",
        "sha256:ty-parent-sequence",
        "sha256:ty-status-native",
        "sha256:ty-callback-visible",
    );

    let decision = compare_shadow_replay(&bundle, &baseline, &native, Some(evidence_ref()));

    assert_eq!(decision.outcome, ShadowReplayOutcome::Mismatch);
    assert_eq!(
        decision.evidence_code.as_deref(),
        Some("ty_status_digest_mismatch")
    );
    assert_shadow_only(&decision);
}

#[test]
fn jit_everywhere_shadow_replay_records_ty_callback_visible_mismatch() {
    let bundle = ty_bundle();
    let baseline = matching_ty_observation();
    let native = ty_observation(
        19,
        37,
        "sha256:ty-fingerprint",
        "sha256:ty-parent-sequence",
        "sha256:ty-status",
        "sha256:ty-callback-visible-native",
    );

    let decision = compare_shadow_replay(&bundle, &baseline, &native, Some(evidence_ref()));

    assert_eq!(decision.outcome, ShadowReplayOutcome::Mismatch);
    assert_eq!(
        decision.evidence_code.as_deref(),
        Some("ty_callback_visible_mismatch")
    );
    assert_shadow_only(&decision);
}

#[test]
fn jit_everywhere_shadow_replay_records_native_failure_classes() {
    let bundle = ay_bundle();
    let baseline = ay_observation(
        ShadowReplayStatus::Ok,
        "sha256:ay-visible-result",
        "sha256:ay-memory-effects",
        "sha256:ay-witness",
        "sha256:ay-proof",
    );
    let cases = [
        (
            ShadowReplayStatus::Crash,
            ShadowReplayOutcome::NativeCrash,
            "native_crash",
        ),
        (
            ShadowReplayStatus::Timeout,
            ShadowReplayOutcome::NativeTimeout,
            "native_timeout",
        ),
        (
            ShadowReplayStatus::VerifierFailure,
            ShadowReplayOutcome::VerifierFailure,
            "verifier_failure",
        ),
        (
            ShadowReplayStatus::Deopt,
            ShadowReplayOutcome::NativeDeopt,
            "native_deopt",
        ),
    ];

    for (status, expected_outcome, expected_code) in cases {
        let native = ay_observation(
            status,
            "sha256:ay-visible-result",
            "sha256:ay-memory-effects",
            "sha256:ay-witness",
            "sha256:ay-proof",
        );

        let decision = compare_shadow_replay(&bundle, &baseline, &native, Some(evidence_ref()));

        assert_eq!(decision.outcome, expected_outcome);
        assert_eq!(decision.evidence_code.as_deref(), Some(expected_code));
        assert_shadow_only(&decision);
    }
}

#[test]
fn jit_everywhere_shadow_replay_fails_closed_for_missing_replay_evidence() {
    let mut bundle = ay_bundle();
    bundle.replay_root_sha256.clear();
    bundle.bundle_sha256 = bundle.canonical_bundle_sha256();
    let baseline = ay_observation(
        ShadowReplayStatus::Ok,
        "sha256:ay-visible-result",
        "sha256:ay-memory-effects",
        "sha256:ay-witness",
        "sha256:ay-proof",
    );
    let native = baseline.clone();

    let decision = compare_shadow_replay(&bundle, &baseline, &native, None);

    assert_eq!(decision.outcome, ShadowReplayOutcome::ReplayRejected);
    assert_eq!(
        decision.evidence_code.as_deref(),
        Some("missing_replay_evidence")
    );
    assert_shadow_only(&decision);
}
