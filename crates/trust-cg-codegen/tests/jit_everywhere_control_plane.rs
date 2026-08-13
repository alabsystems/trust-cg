// trust-cg-codegen/tests/jit_everywhere_control_plane.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_codegen::{
    ControlPlaneCandidate, ControlPlaneDecision, ControlPlaneGateEvidence, ControlPlaneKillSwitch,
    ControlPlaneMode, ControlPlaneReason, ControlPlaneRevocation, ControlPlaneRoute,
    JIT_EVERYWHERE_CONTROL_PLANE_SCHEMA, JIT_EVERYWHERE_CONTROL_PLANE_SCHEMA_VERSION,
    JIT_EVERYWHERE_PRODUCT_ADAPTER_EVENT_SCHEMA,
    JIT_EVERYWHERE_PRODUCT_ADAPTER_EVENT_SCHEMA_VERSION, JitEverywhereControlPlane, Target,
};

fn gate_accepted() -> ControlPlaneGateEvidence {
    ControlPlaneGateEvidence {
        phase6_accepted: true,
        phase9_accepted: true,
    }
}

fn candidate(mode: ControlPlaneMode) -> ControlPlaneCandidate {
    ControlPlaneCandidate::new(
        "ay",
        "ay_sparse_substitute",
        "sha256:artifact-ay-sparse-substitute",
        Target::Aarch64,
        "sha256:target-facts-aarch64-darwin",
        "proof-policy:v1:require-certificates",
        mode,
        "ay_sparse_substitute:generation:7",
        "sha256:replay-root-ay-sparse-substitute",
        "telemetry:ay-sparse-substitute",
    )
}

fn ty_candidate(mode: ControlPlaneMode) -> ControlPlaneCandidate {
    ControlPlaneCandidate::new(
        "ty",
        "ty_action_cluster",
        "sha256:artifact-ty-action",
        Target::Aarch64,
        "sha256:target-facts-aarch64-darwin",
        "proof-policy:v1:require-certificates",
        mode,
        "ty_action:generation:11",
        "sha256:replay-root-ty-action",
        "telemetry:ty-action",
    )
}

fn assert_baseline_denied(decision: &ControlPlaneDecision, reason: ControlPlaneReason) {
    assert_eq!(decision.route, ControlPlaneRoute::Baseline);
    assert_eq!(decision.reason, reason);
    assert!(decision.baseline_authoritative);
    assert!(!decision.native_authoritative);
    assert!(decision.is_deny_or_baseline_only());
    assert!(decision.side_effects.all_install_authority_blocked());
    assert!(!decision.side_effects.callable_handle_published);
    assert!(!decision.side_effects.installable_cache_hit_accepted);
    assert!(!decision.side_effects.ay_registry_inserted);
    assert!(!decision.side_effects.ty_native_activated);
    assert!(!decision.side_effects.baseline_replaced);
    assert!(!decision.side_effects.native_invocation_allowed);
    assert_eq!(decision.side_effects.useful_native_delta, 0);
    assert_eq!(
        decision.telemetry.schema,
        JIT_EVERYWHERE_CONTROL_PLANE_SCHEMA
    );
    assert_eq!(
        decision.telemetry.schema_version,
        JIT_EVERYWHERE_CONTROL_PLANE_SCHEMA_VERSION
    );
    assert_eq!(decision.telemetry.issue, 739);
    assert_eq!(
        decision.telemetry.record_sha256,
        decision.telemetry.canonical_record_sha256()
    );
}

fn assert_product_adapter_denied(
    adapter: &trust_cg_codegen::ControlPlaneProductAdapterDecision,
    reason: ControlPlaneReason,
) {
    assert_eq!(adapter.reason, reason);
    assert!(adapter.baseline_route_recorded);
    assert!(adapter.denied_without_product_authority());
    assert_eq!(adapter.callable_handle_id, None);
    assert_eq!(adapter.native_handle_id, None);
    assert!(!adapter.installable_cache_hit_accepted);
    assert_eq!(adapter.useful_native_delta, 0);
    assert_eq!(
        adapter.telemetry.schema,
        JIT_EVERYWHERE_PRODUCT_ADAPTER_EVENT_SCHEMA
    );
    assert_eq!(
        adapter.telemetry.schema_version,
        JIT_EVERYWHERE_PRODUCT_ADAPTER_EVENT_SCHEMA_VERSION
    );
    assert_eq!(adapter.telemetry.issue, 749);
    assert_eq!(
        adapter.telemetry.candidate_key_sha256,
        adapter.candidate_key_sha256
    );
    assert_eq!(adapter.telemetry.artifact_sha256, adapter.artifact_sha256);
    assert_eq!(adapter.telemetry.route, adapter.route);
    assert_eq!(adapter.telemetry.reason, adapter.reason);
    assert!(adapter.telemetry.baseline_route_recorded);
    assert_eq!(
        adapter.telemetry.callable_registry_removed,
        adapter.callable_registry_removed
    );
    assert_eq!(
        adapter.telemetry.installable_cache_removed,
        adapter.installable_cache_removed
    );
    assert_eq!(
        adapter.telemetry.ay_registry_removed,
        adapter.ay_registry_removed
    );
    assert_eq!(
        adapter.telemetry.ty_native_removed,
        adapter.ty_native_removed
    );
    assert!(
        adapter
            .telemetry
            .control_plane_record_sha256
            .starts_with("sha256:")
    );
    assert_eq!(adapter.telemetry.callable_handle_id, None);
    assert_eq!(adapter.telemetry.native_handle_id, None);
    assert!(!adapter.telemetry.installable_cache_hit_accepted);
    assert_eq!(adapter.telemetry.useful_native_delta, 0);
    assert_eq!(adapter.telemetry.product_call_status, None);
    assert_eq!(adapter.telemetry.product_call_status_record_sha256, None);
    assert!(adapter.telemetry.denied_without_product_authority());
    assert_eq!(
        adapter.telemetry.record_sha256,
        adapter.telemetry.canonical_record_sha256()
    );
    assert!(
        adapter
            .retained_replay_root_sha256
            .as_deref()
            .is_some_and(|root| root.starts_with("sha256:"))
    );
    assert!(
        adapter
            .retained_telemetry_key
            .as_deref()
            .is_some_and(|key| key.starts_with("telemetry:"))
    );
    assert_eq!(
        adapter.telemetry.retained_replay_root_sha256,
        adapter.retained_replay_root_sha256
    );
    assert_eq!(
        adapter.telemetry.retained_telemetry_key,
        adapter.retained_telemetry_key
    );
}

#[test]
fn jit_everywhere_control_plane_kill_switch_scopes_route_new_calls_to_baseline() {
    let base = candidate(ControlPlaneMode::CanaryInstallable);
    let switches = [
        ControlPlaneKillSwitch::global("global native off"),
        ControlPlaneKillSwitch::consumer("ay", "ay native off"),
        ControlPlaneKillSwitch::family("ay", "ay_sparse_substitute", "family off"),
        ControlPlaneKillSwitch::artifact("sha256:artifact-ay-sparse-substitute", "artifact off"),
        ControlPlaneKillSwitch::target_proof_policy(
            "sha256:target-facts-aarch64-darwin",
            "proof-policy:v1:require-certificates",
            "target proof policy off",
        ),
        ControlPlaneKillSwitch::mode(ControlPlaneMode::CanaryInstallable, "canary off"),
    ];

    for switch in switches {
        let expected_rule_hash = switch.rule_sha256.clone();
        let mut control = JitEverywhereControlPlane::new();
        control.add_kill_switch(switch);

        let decision = control.route_new_call(&base, gate_accepted());

        assert_baseline_denied(&decision, ControlPlaneReason::KillSwitchActive);
        assert_eq!(decision.kill_switch_sha256, Some(expected_rule_hash));
        assert_eq!(
            decision.telemetry.kill_switch_sha256,
            decision.kill_switch_sha256
        );
    }
}

#[test]
fn jit_everywhere_control_plane_switches_profile_shadow_and_canary_modes() {
    let cases = [
        (
            candidate(ControlPlaneMode::ProfileOnly),
            ControlPlaneMode::ProfileOnly,
        ),
        (
            candidate(ControlPlaneMode::ShadowOnly),
            ControlPlaneMode::ShadowOnly,
        ),
        (
            candidate(ControlPlaneMode::CanaryInstallable),
            ControlPlaneMode::CanaryInstallable,
        ),
    ];

    for (candidate, mode) in cases {
        let mut control = JitEverywhereControlPlane::new();
        control.add_kill_switch(ControlPlaneKillSwitch::mode(mode, "mode disabled"));

        let decision = control.route_new_call(&candidate, gate_accepted());

        assert_baseline_denied(&decision, ControlPlaneReason::KillSwitchActive);
        assert_eq!(decision.telemetry.mode, mode);
        assert!(decision.telemetry.kill_switch_sha256.is_some());
    }
}

#[test]
fn jit_everywhere_control_plane_revokes_artifact_and_retains_replay_evidence() {
    let candidate = candidate(ControlPlaneMode::CanaryInstallable);
    let revocation = ControlPlaneRevocation::active(
        candidate.artifact_sha256.clone(),
        candidate.replay_root_sha256.clone(),
        candidate.telemetry_key.clone(),
        "wrong-answer quarantine",
    );
    let expected_revocation_hash = revocation.revocation_sha256.clone();
    let mut control = JitEverywhereControlPlane::new();
    control.publish_local_fixture(&candidate);
    assert!(
        control
            .publication_state()
            .has_callable(&candidate.artifact_sha256)
    );
    assert!(
        control
            .publication_state()
            .has_installable_cache_entry(&candidate.artifact_sha256)
    );

    control.revoke_artifact(revocation);

    assert!(
        !control
            .publication_state()
            .has_callable(&candidate.artifact_sha256)
    );
    assert!(
        !control
            .publication_state()
            .has_installable_cache_entry(&candidate.artifact_sha256)
    );
    assert_eq!(
        control
            .publication_state()
            .retained_replay_root(&candidate.artifact_sha256)
            .map(String::as_str),
        Some(candidate.replay_root_sha256.as_str())
    );
    assert_eq!(
        control
            .publication_state()
            .retained_telemetry_key(&candidate.artifact_sha256)
            .map(String::as_str),
        Some(candidate.telemetry_key.as_str())
    );

    let decision = control.route_new_call(&candidate, gate_accepted());

    assert_baseline_denied(&decision, ControlPlaneReason::ArtifactRevoked);
    assert_eq!(decision.revocation_sha256, Some(expected_revocation_hash));
    assert_eq!(
        decision.telemetry.revocation_sha256,
        decision.revocation_sha256
    );
    assert_eq!(
        decision.telemetry.replay_root_sha256,
        candidate.replay_root_sha256
    );
    assert_eq!(decision.telemetry.telemetry_key, candidate.telemetry_key);
}

#[test]
fn jit_everywhere_control_plane_in_flight_guard_blocks_native_invocation() {
    let candidate = ty_candidate(ControlPlaneMode::ActiveInstallable);
    let switch = ControlPlaneKillSwitch::family("ty", "ty_action_cluster", "stop action");
    let mut control = JitEverywhereControlPlane::new();
    control.add_kill_switch(switch);

    let decision = control.guard_in_flight_call(&candidate, gate_accepted());

    assert_baseline_denied(&decision, ControlPlaneReason::KillSwitchActive);
    assert!(!decision.side_effects.native_invocation_allowed);
    assert_eq!(decision.telemetry.consumer, "ty");
    assert_eq!(decision.telemetry.family, "ty_action_cluster");
}

#[test]
fn jit_everywhere_control_plane_reenable_requires_parent_gate_evidence() {
    let candidate = candidate(ControlPlaneMode::CanaryInstallable);
    let control = JitEverywhereControlPlane::new();

    let missing = control.attempt_reenable(&candidate, ControlPlaneGateEvidence::default());
    assert_baseline_denied(&missing, ControlPlaneReason::MissingProductGateEvidence);

    let accepted = control.attempt_reenable(&candidate, gate_accepted());
    assert_eq!(accepted.route, ControlPlaneRoute::ProductGateRequired);
    assert_eq!(
        accepted.reason,
        ControlPlaneReason::ProductActivationRequired
    );
    assert!(accepted.baseline_authoritative);
    assert!(!accepted.native_authoritative);
    assert!(accepted.is_deny_or_baseline_only());
    assert!(accepted.side_effects.all_install_authority_blocked());
    assert_eq!(accepted.telemetry.reason, accepted.reason);
}

#[test]
fn jit_everywhere_control_plane_non_callable_modes_never_publish_handles() {
    let control = JitEverywhereControlPlane::new();
    let profile = control.route_new_call(
        &candidate(ControlPlaneMode::ProfileOnly),
        ControlPlaneGateEvidence::default(),
    );
    let shadow = control.route_new_call(
        &candidate(ControlPlaneMode::ShadowOnly),
        ControlPlaneGateEvidence::default(),
    );

    assert_eq!(profile.route, ControlPlaneRoute::ProfileOnlyRetained);
    assert_eq!(profile.reason, ControlPlaneReason::ProfileOnlyNonCallable);
    assert!(profile.is_deny_or_baseline_only());
    assert_eq!(shadow.route, ControlPlaneRoute::ShadowOnlyRetained);
    assert_eq!(shadow.reason, ControlPlaneReason::ShadowOnlyNonCallable);
    assert!(shadow.is_deny_or_baseline_only());
}

#[test]
fn jit_everywhere_product_adapter_removes_ay_registry_cache_and_routes_baseline() {
    let candidate = candidate(ControlPlaneMode::CanaryInstallable);
    let mut control = JitEverywhereControlPlane::new();
    control.record_existing_product_publication(&candidate);
    control.add_kill_switch(ControlPlaneKillSwitch::consumer("ay", "ay native off"));

    assert!(
        control
            .publication_state()
            .has_callable(&candidate.artifact_sha256)
    );
    assert!(
        control
            .publication_state()
            .has_installable_cache_entry(&candidate.artifact_sha256)
    );
    assert!(
        control
            .publication_state()
            .has_ay_registry_entry(&candidate.artifact_sha256)
    );

    let adapter = control.route_product_adapter_call(&candidate, gate_accepted());

    assert_product_adapter_denied(&adapter, ControlPlaneReason::KillSwitchActive);
    assert_eq!(adapter.route, ControlPlaneRoute::Baseline);
    assert!(adapter.callable_registry_removed);
    assert!(adapter.installable_cache_removed);
    assert!(adapter.ay_registry_removed);
    assert!(!adapter.ty_native_removed);
    assert!(
        !control
            .publication_state()
            .has_callable(&candidate.artifact_sha256)
    );
    assert!(
        !control
            .publication_state()
            .has_installable_cache_entry(&candidate.artifact_sha256)
    );
    assert!(
        !control
            .publication_state()
            .has_ay_registry_entry(&candidate.artifact_sha256)
    );
}

#[test]
fn jit_everywhere_product_adapter_revocation_removes_ty_native_cache() {
    let candidate = ty_candidate(ControlPlaneMode::ActiveInstallable);
    let revocation = ControlPlaneRevocation::active(
        candidate.artifact_sha256.clone(),
        candidate.replay_root_sha256.clone(),
        candidate.telemetry_key.clone(),
        "ty action quarantine",
    );
    let mut control = JitEverywhereControlPlane::new();
    control.revoke_artifact(revocation);
    control.record_existing_product_publication(&candidate);
    assert!(
        control
            .publication_state()
            .has_ty_native_entry(&candidate.artifact_sha256)
    );

    let adapter = control.route_product_adapter_call(&candidate, gate_accepted());

    assert_product_adapter_denied(&adapter, ControlPlaneReason::ArtifactRevoked);
    assert_eq!(adapter.route, ControlPlaneRoute::Baseline);
    assert!(adapter.callable_registry_removed);
    assert!(adapter.installable_cache_removed);
    assert!(!adapter.ay_registry_removed);
    assert!(adapter.ty_native_removed);
    assert!(
        !control
            .publication_state()
            .has_ty_native_entry(&candidate.artifact_sha256)
    );
    assert_eq!(
        adapter.retained_replay_root_sha256.as_deref(),
        Some(candidate.replay_root_sha256.as_str())
    );
    assert_eq!(
        adapter.retained_telemetry_key.as_deref(),
        Some(candidate.telemetry_key.as_str())
    );
}

#[test]
fn jit_everywhere_product_adapter_removes_state_when_activation_still_requires_parent_gate() {
    let candidate = candidate(ControlPlaneMode::ActiveInstallable);
    let mut control = JitEverywhereControlPlane::new();
    control.record_existing_product_publication(&candidate);

    let adapter = control.route_product_adapter_call(&candidate, gate_accepted());

    assert_product_adapter_denied(&adapter, ControlPlaneReason::ProductActivationRequired);
    assert_eq!(adapter.route, ControlPlaneRoute::ProductGateRequired);
    assert!(adapter.callable_registry_removed);
    assert!(adapter.installable_cache_removed);
    assert!(adapter.ay_registry_removed);
    assert!(!adapter.ty_native_removed);
    assert!(
        !control
            .publication_state()
            .has_callable(&candidate.artifact_sha256)
    );
    assert!(
        !control
            .publication_state()
            .has_installable_cache_entry(&candidate.artifact_sha256)
    );
    assert!(
        !control
            .publication_state()
            .has_ay_registry_entry(&candidate.artifact_sha256)
    );
}

#[test]
fn jit_everywhere_product_adapter_telemetry_hash_binds_replay_and_zero_delta() {
    let candidate = candidate(ControlPlaneMode::CanaryInstallable);
    let mut control = JitEverywhereControlPlane::new();
    control.record_existing_product_publication(&candidate);
    control.add_kill_switch(ControlPlaneKillSwitch::artifact(
        candidate.artifact_sha256.clone(),
        "artifact denied",
    ));

    let adapter = control.route_product_adapter_call(&candidate, gate_accepted());
    assert_product_adapter_denied(&adapter, ControlPlaneReason::KillSwitchActive);

    let mut useful_native_tampered = adapter.telemetry.clone();
    useful_native_tampered.useful_native_delta = 1;
    assert_ne!(
        useful_native_tampered.record_sha256,
        useful_native_tampered.canonical_record_sha256()
    );
    assert!(!useful_native_tampered.denied_without_product_authority());

    let mut replay_tampered = adapter.telemetry.clone();
    replay_tampered.retained_replay_root_sha256 =
        Some("sha256:wrong-product-adapter-replay-root".to_owned());
    assert_ne!(
        replay_tampered.record_sha256,
        replay_tampered.canonical_record_sha256()
    );

    let mut handle_tampered = adapter.telemetry.clone();
    handle_tampered.callable_handle_id = Some("callable:unexpected".to_owned());
    assert_ne!(
        handle_tampered.record_sha256,
        handle_tampered.canonical_record_sha256()
    );
    assert!(!handle_tampered.denied_without_product_authority());
}
