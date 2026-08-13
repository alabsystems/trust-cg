// trust-cg-codegen/jit_control_plane.rs - JIT-everywhere deny/remove control plane
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Data-only deny/remove control-plane model for JIT-everywhere prework.
//!
//! This module models scoped kill switches, revocation, baseline routing,
//! in-flight call guards, and retained replay/telemetry evidence. It does not
//! publish callable handles, admit installable cache hits, activate ay/TY
//! native dispatch, or increment useful-native counters.

use std::collections::{BTreeMap, BTreeSet};

use crate::jit_contract::ArtifactChecksum;
use crate::jit_diagnostics::sha256_hex;
use crate::jit_install_gate::{
    NativeInstallGateConsumerAdmissionDecision, NativeInstallGateConsumerAdmissionEvidence,
    NativeInstallGateDenyControlPlane, NativeInstallGateDenyReason, NativeInstallGateDenyScope,
    NativeInstallGateDisposition, NativeInstallGatePacket, NativeInstallGateRejectionCode,
    NativeInstallGateRevalidationInput, NativeInstallGateRuntimeOutcome,
    NativeInstallGateRuntimeTelemetryPacket, native_install_gate_consumer_admission,
    native_install_gate_runtime_telemetry,
};
use crate::target::Target;

/// Stable schema tag for control-plane telemetry packets.
pub const JIT_EVERYWHERE_CONTROL_PLANE_SCHEMA: &str = "trust-cg.jit_everywhere.control_plane.v1";

/// Stable numeric schema version for control-plane telemetry packets.
pub const JIT_EVERYWHERE_CONTROL_PLANE_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for product-adapter deny/remove telemetry packets.
pub const JIT_EVERYWHERE_PRODUCT_ADAPTER_EVENT_SCHEMA: &str =
    "trust-cg.jit_everywhere.product_adapter_event.v2";

/// Stable numeric schema version for product-adapter telemetry packets.
pub const JIT_EVERYWHERE_PRODUCT_ADAPTER_EVENT_SCHEMA_VERSION: u32 = 2;

/// Stable schema tag for product-adapter call-status rows.
pub const JIT_EVERYWHERE_PRODUCT_CALL_STATUS_SCHEMA: &str =
    "trust-cg.jit_everywhere.product_call_status.v1";

/// Stable numeric schema version for product-adapter call-status rows.
pub const JIT_EVERYWHERE_PRODUCT_CALL_STATUS_SCHEMA_VERSION: u32 = 1;

/// Native-dispatch rollout mode observed by the control plane.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ControlPlaneMode {
    /// Profile-only learning mode.
    ProfileOnly,
    /// Shadow-only comparison mode.
    ShadowOnly,
    /// Canary callable candidate mode.
    CanaryInstallable,
    /// Active callable candidate mode.
    ActiveInstallable,
}

impl ControlPlaneMode {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ProfileOnly => "profile_only",
            Self::ShadowOnly => "shadow_only",
            Self::CanaryInstallable => "canary_installable",
            Self::ActiveInstallable => "active_installable",
        }
    }
}

/// Scope covered by one deny/remove kill switch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ControlPlaneKillSwitchScope {
    /// Applies to every candidate.
    Global,
    /// Applies to one consumer.
    Consumer,
    /// Applies to one consumer family.
    Family,
    /// Applies to one artifact digest.
    Artifact,
    /// Applies to one target/proof-policy tuple.
    TargetProofPolicy,
    /// Applies to one rollout mode.
    Mode,
}

impl ControlPlaneKillSwitchScope {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Global => "global",
            Self::Consumer => "consumer",
            Self::Family => "family",
            Self::Artifact => "artifact",
            Self::TargetProofPolicy => "target_proof_policy",
            Self::Mode => "mode",
        }
    }
}

/// Stable route after control-plane evaluation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ControlPlaneRoute {
    /// Route to baseline execution.
    Baseline,
    /// Keep only profile-only learning data.
    ProfileOnlyRetained,
    /// Keep only shadow replay data.
    ShadowOnlyRetained,
    /// Gate evidence exists but product activation remains outside this issue.
    ProductGateRequired,
}

impl ControlPlaneRoute {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Baseline => "baseline",
            Self::ProfileOnlyRetained => "profile_only_retained",
            Self::ShadowOnlyRetained => "shadow_only_retained",
            Self::ProductGateRequired => "product_gate_required",
        }
    }
}

/// Stable deny/remove reason emitted by the control plane.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ControlPlaneReason {
    /// Active kill switch matched this candidate.
    KillSwitchActive,
    /// Artifact is revoked.
    ArtifactRevoked,
    /// Profile-only mode is non-callable.
    ProfileOnlyNonCallable,
    /// Shadow-only mode is non-callable.
    ShadowOnlyNonCallable,
    /// Accepted product gate evidence is missing.
    MissingProductGateEvidence,
    /// Full product activation is outside this issue.
    ProductActivationRequired,
}

impl ControlPlaneReason {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::KillSwitchActive => "kill_switch_active",
            Self::ArtifactRevoked => "artifact_revoked",
            Self::ProfileOnlyNonCallable => "profile_only_non_callable",
            Self::ShadowOnlyNonCallable => "shadow_only_non_callable",
            Self::MissingProductGateEvidence => "missing_product_gate_evidence",
            Self::ProductActivationRequired => "product_activation_required",
        }
    }
}

/// Product-adapter lifecycle status after call-time revalidation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ControlPlaneProductCallStatus {
    /// Consumer admission accepted the packet, but product activation is still gated.
    AcceptedPendingProductGate,
    /// Consumer admission rejected the packet before product publication.
    ConsumerRejected,
    /// Call-time revalidation observed stale freshness or proof evidence.
    StaleDeopt,
    /// Call-time revalidation observed revocation.
    RevokedDeopt,
    /// Call-time revalidation observed an active kill switch.
    KillSwitchDeopt,
    /// Call-time revalidation observed tampered or mismatched packet identity.
    InvalidatedDeopt,
    /// Call-time revalidation rejected for any other fail-closed reason.
    RejectedDeopt,
}

impl ControlPlaneProductCallStatus {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::AcceptedPendingProductGate => "accepted_pending_product_gate",
            Self::ConsumerRejected => "consumer_rejected",
            Self::StaleDeopt => "stale_deopt",
            Self::RevokedDeopt => "revoked_deopt",
            Self::KillSwitchDeopt => "kill_switch_deopt",
            Self::InvalidatedDeopt => "invalidated_deopt",
            Self::RejectedDeopt => "rejected_deopt",
        }
    }
}

/// Candidate identity consumed by kill switches, revocation, and routing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ControlPlaneCandidate {
    /// Consumer name: `trust-cg`, `ay`, or `ty`.
    pub consumer: String,
    /// Consumer family or mode.
    pub family: String,
    /// Native artifact digest.
    pub artifact_sha256: String,
    /// Target architecture.
    pub target: Target,
    /// Target facts SHA-256.
    pub target_facts_sha256: String,
    /// Proof-policy id or checksum.
    pub proof_policy: String,
    /// Rollout mode.
    pub mode: ControlPlaneMode,
    /// Generation domain.
    pub generation_domain: String,
    /// Replay root retained for diagnostics.
    pub replay_root_sha256: String,
    /// Telemetry key retained for diagnostics.
    pub telemetry_key: String,
    /// Canonical candidate key SHA-256.
    pub candidate_key_sha256: String,
}

impl ControlPlaneCandidate {
    /// Build a control-plane candidate identity.
    pub fn new(
        consumer: impl Into<String>,
        family: impl Into<String>,
        artifact_sha256: impl Into<String>,
        target: Target,
        target_facts_sha256: impl Into<String>,
        proof_policy: impl Into<String>,
        mode: ControlPlaneMode,
        generation_domain: impl Into<String>,
        replay_root_sha256: impl Into<String>,
        telemetry_key: impl Into<String>,
    ) -> Self {
        let mut candidate = Self {
            consumer: consumer.into(),
            family: family.into(),
            artifact_sha256: artifact_sha256.into(),
            target,
            target_facts_sha256: target_facts_sha256.into(),
            proof_policy: proof_policy.into(),
            mode,
            generation_domain: generation_domain.into(),
            replay_root_sha256: replay_root_sha256.into(),
            telemetry_key: telemetry_key.into(),
            candidate_key_sha256: String::new(),
        };
        candidate.candidate_key_sha256 = candidate.canonical_candidate_key_sha256();
        candidate
    }

    /// Return the stable hash of this candidate identity.
    pub fn canonical_candidate_key_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(
            &mut out,
            "trust-cg.jit_everywhere.control_plane.candidate.v1",
        );
        put_str(&mut out, &self.consumer);
        put_str(&mut out, &self.family);
        put_str(&mut out, &self.artifact_sha256);
        put_str(&mut out, self.target.name());
        put_str(&mut out, &self.target_facts_sha256);
        put_str(&mut out, &self.proof_policy);
        put_str(&mut out, self.mode.as_str());
        put_str(&mut out, &self.generation_domain);
        put_str(&mut out, &self.replay_root_sha256);
        put_str(&mut out, &self.telemetry_key);
        format!("sha256:{}", sha256_hex(&out))
    }

    fn has_required_identity(&self) -> bool {
        !missing_required_text(&self.consumer)
            && !missing_required_text(&self.family)
            && !missing_required_text(&self.artifact_sha256)
            && !missing_required_text(&self.target_facts_sha256)
            && !missing_required_text(&self.proof_policy)
            && !missing_required_text(&self.generation_domain)
            && !missing_required_text(&self.replay_root_sha256)
            && !missing_required_text(&self.telemetry_key)
            && self.candidate_key_sha256 == self.canonical_candidate_key_sha256()
    }
}

/// One scoped kill-switch rule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ControlPlaneKillSwitch {
    /// Whether this switch is active.
    pub active: bool,
    /// Switch scope.
    pub scope: ControlPlaneKillSwitchScope,
    /// Optional matching consumer.
    pub consumer: Option<String>,
    /// Optional matching family.
    pub family: Option<String>,
    /// Optional matching artifact digest.
    pub artifact_sha256: Option<String>,
    /// Optional matching target facts digest.
    pub target_facts_sha256: Option<String>,
    /// Optional matching proof policy.
    pub proof_policy: Option<String>,
    /// Optional matching mode.
    pub mode: Option<ControlPlaneMode>,
    /// Human-readable operator reason.
    pub operator_reason: String,
    /// Canonical rule SHA-256.
    pub rule_sha256: String,
}

impl ControlPlaneKillSwitch {
    /// Build an inactive shell for a scope.
    pub fn new(scope: ControlPlaneKillSwitchScope, operator_reason: impl Into<String>) -> Self {
        let mut switch = Self {
            active: true,
            scope,
            consumer: None,
            family: None,
            artifact_sha256: None,
            target_facts_sha256: None,
            proof_policy: None,
            mode: None,
            operator_reason: operator_reason.into(),
            rule_sha256: String::new(),
        };
        switch.rule_sha256 = switch.canonical_rule_sha256();
        switch
    }

    /// Global active switch.
    pub fn global(operator_reason: impl Into<String>) -> Self {
        Self::new(ControlPlaneKillSwitchScope::Global, operator_reason)
    }

    /// Consumer active switch.
    pub fn consumer(consumer: impl Into<String>, operator_reason: impl Into<String>) -> Self {
        let mut switch = Self::new(ControlPlaneKillSwitchScope::Consumer, operator_reason);
        switch.consumer = Some(consumer.into());
        switch.rule_sha256 = switch.canonical_rule_sha256();
        switch
    }

    /// Family active switch.
    pub fn family(
        consumer: impl Into<String>,
        family: impl Into<String>,
        operator_reason: impl Into<String>,
    ) -> Self {
        let mut switch = Self::new(ControlPlaneKillSwitchScope::Family, operator_reason);
        switch.consumer = Some(consumer.into());
        switch.family = Some(family.into());
        switch.rule_sha256 = switch.canonical_rule_sha256();
        switch
    }

    /// Artifact active switch.
    pub fn artifact(
        artifact_sha256: impl Into<String>,
        operator_reason: impl Into<String>,
    ) -> Self {
        let mut switch = Self::new(ControlPlaneKillSwitchScope::Artifact, operator_reason);
        switch.artifact_sha256 = Some(artifact_sha256.into());
        switch.rule_sha256 = switch.canonical_rule_sha256();
        switch
    }

    /// Target/proof-policy active switch.
    pub fn target_proof_policy(
        target_facts_sha256: impl Into<String>,
        proof_policy: impl Into<String>,
        operator_reason: impl Into<String>,
    ) -> Self {
        let mut switch = Self::new(
            ControlPlaneKillSwitchScope::TargetProofPolicy,
            operator_reason,
        );
        switch.target_facts_sha256 = Some(target_facts_sha256.into());
        switch.proof_policy = Some(proof_policy.into());
        switch.rule_sha256 = switch.canonical_rule_sha256();
        switch
    }

    /// Mode active switch.
    pub fn mode(mode: ControlPlaneMode, operator_reason: impl Into<String>) -> Self {
        let mut switch = Self::new(ControlPlaneKillSwitchScope::Mode, operator_reason);
        switch.mode = Some(mode);
        switch.rule_sha256 = switch.canonical_rule_sha256();
        switch
    }

    /// Return the stable hash of this kill-switch rule.
    pub fn canonical_rule_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(
            &mut out,
            "trust-cg.jit_everywhere.control_plane.kill_switch.v1",
        );
        put_bool(&mut out, self.active);
        put_str(&mut out, self.scope.as_str());
        put_option_str(&mut out, self.consumer.as_deref());
        put_option_str(&mut out, self.family.as_deref());
        put_option_str(&mut out, self.artifact_sha256.as_deref());
        put_option_str(&mut out, self.target_facts_sha256.as_deref());
        put_option_str(&mut out, self.proof_policy.as_deref());
        put_option_str(&mut out, self.mode.map(ControlPlaneMode::as_str));
        put_str(&mut out, &self.operator_reason);
        format!("sha256:{}", sha256_hex(&out))
    }

    /// Return true when this switch currently denies the candidate.
    pub fn applies_to(&self, candidate: &ControlPlaneCandidate) -> bool {
        if !self.active || self.rule_sha256 != self.canonical_rule_sha256() {
            return false;
        }
        match self.scope {
            ControlPlaneKillSwitchScope::Global => true,
            ControlPlaneKillSwitchScope::Consumer => self
                .consumer
                .as_deref()
                .is_some_and(|consumer| consumer == candidate.consumer),
            ControlPlaneKillSwitchScope::Family => {
                self.consumer
                    .as_deref()
                    .is_some_and(|consumer| consumer == candidate.consumer)
                    && self
                        .family
                        .as_deref()
                        .is_some_and(|family| family == candidate.family)
            }
            ControlPlaneKillSwitchScope::Artifact => self
                .artifact_sha256
                .as_deref()
                .is_some_and(|artifact| artifact == candidate.artifact_sha256),
            ControlPlaneKillSwitchScope::TargetProofPolicy => {
                self.target_facts_sha256
                    .as_deref()
                    .is_some_and(|target| target == candidate.target_facts_sha256)
                    && self
                        .proof_policy
                        .as_deref()
                        .is_some_and(|policy| policy == candidate.proof_policy)
            }
            ControlPlaneKillSwitchScope::Mode => self.mode == Some(candidate.mode),
        }
    }
}

/// Revocation record for one artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ControlPlaneRevocation {
    /// Whether this revocation is active.
    pub active: bool,
    /// Revoked artifact digest.
    pub artifact_sha256: String,
    /// Replay root retained after removal.
    pub replay_root_sha256: String,
    /// Telemetry key retained after removal.
    pub telemetry_key: String,
    /// Operator reason.
    pub operator_reason: String,
    /// Canonical revocation SHA-256.
    pub revocation_sha256: String,
}

impl ControlPlaneRevocation {
    /// Build an active artifact revocation.
    pub fn active(
        artifact_sha256: impl Into<String>,
        replay_root_sha256: impl Into<String>,
        telemetry_key: impl Into<String>,
        operator_reason: impl Into<String>,
    ) -> Self {
        let mut revocation = Self {
            active: true,
            artifact_sha256: artifact_sha256.into(),
            replay_root_sha256: replay_root_sha256.into(),
            telemetry_key: telemetry_key.into(),
            operator_reason: operator_reason.into(),
            revocation_sha256: String::new(),
        };
        revocation.revocation_sha256 = revocation.canonical_revocation_sha256();
        revocation
    }

    /// Return the stable hash of this revocation.
    pub fn canonical_revocation_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(
            &mut out,
            "trust-cg.jit_everywhere.control_plane.revocation.v1",
        );
        put_bool(&mut out, self.active);
        put_str(&mut out, &self.artifact_sha256);
        put_str(&mut out, &self.replay_root_sha256);
        put_str(&mut out, &self.telemetry_key);
        put_str(&mut out, &self.operator_reason);
        format!("sha256:{}", sha256_hex(&out))
    }

    fn applies_to(&self, candidate: &ControlPlaneCandidate) -> bool {
        self.active
            && self.artifact_sha256 == candidate.artifact_sha256
            && self.revocation_sha256 == self.canonical_revocation_sha256()
    }
}

/// Product gate evidence summary observed by the control plane.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct ControlPlaneGateEvidence {
    /// Phase 6 install/cache/replay evidence accepted.
    pub phase6_accepted: bool,
    /// Phase 9 promotion/closure evidence accepted.
    pub phase9_accepted: bool,
}

impl ControlPlaneGateEvidence {
    /// Return true only when all required parent product gates are accepted.
    pub const fn accepted(self) -> bool {
        self.phase6_accepted && self.phase9_accepted
    }
}

/// Explicit side-effect summary for control-plane decisions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct ControlPlaneSideEffects {
    /// Whether a callable handle was published.
    pub callable_handle_published: bool,
    /// Whether an installable cache hit was accepted.
    pub installable_cache_hit_accepted: bool,
    /// Whether ay registry insertion occurred.
    pub ay_registry_inserted: bool,
    /// Whether TY native activation occurred.
    pub ty_native_activated: bool,
    /// Whether baseline execution was replaced.
    pub baseline_replaced: bool,
    /// Whether native invocation is allowed by an in-flight guard.
    pub native_invocation_allowed: bool,
    /// Useful-native counter delta.
    pub useful_native_delta: u64,
}

impl ControlPlaneSideEffects {
    /// Return true when every install-authorizing side effect is blocked.
    pub const fn all_install_authority_blocked(self) -> bool {
        !self.callable_handle_published
            && !self.installable_cache_hit_accepted
            && !self.ay_registry_inserted
            && !self.ty_native_activated
            && !self.baseline_replaced
            && !self.native_invocation_allowed
            && self.useful_native_delta == 0
    }
}

/// Deny/remove result for a product registry or cache adapter.
///
/// This records the effect of consuming a control-plane decision at a product
/// boundary. It is intentionally non-authorizing: no callable handle, native
/// handle, installable-cache hit, or useful-native credit can be returned.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ControlPlaneProductAdapterDecision {
    /// Candidate key.
    pub candidate_key_sha256: String,
    /// Artifact digest.
    pub artifact_sha256: String,
    /// Final route.
    pub route: ControlPlaneRoute,
    /// Decision reason.
    pub reason: ControlPlaneReason,
    /// Whether baseline routing was recorded as authoritative.
    pub baseline_route_recorded: bool,
    /// Whether a callable registry entry was removed.
    pub callable_registry_removed: bool,
    /// Whether an installable-cache entry was removed.
    pub installable_cache_removed: bool,
    /// Whether a ay registry entry was removed.
    pub ay_registry_removed: bool,
    /// Whether a TY native activation entry was removed.
    pub ty_native_removed: bool,
    /// Replay root retained after removal.
    pub retained_replay_root_sha256: Option<String>,
    /// Telemetry key retained after removal.
    pub retained_telemetry_key: Option<String>,
    /// No callable handle is returned by this adapter.
    pub callable_handle_id: Option<String>,
    /// No native handle is returned by this adapter.
    pub native_handle_id: Option<String>,
    /// No installable-cache hit is accepted by this adapter.
    pub installable_cache_hit_accepted: bool,
    /// Useful-native counter delta.
    pub useful_native_delta: u64,
    /// Structured telemetry/replay packet for this adapter decision.
    pub telemetry: ControlPlaneProductAdapterTelemetryPacket,
}

impl ControlPlaneProductAdapterDecision {
    /// Return true when this adapter result cannot authorize native product use.
    pub fn denied_without_product_authority(&self) -> bool {
        self.baseline_route_recorded
            && self.callable_handle_id.is_none()
            && self.native_handle_id.is_none()
            && !self.installable_cache_hit_accepted
            && self.useful_native_delta == 0
            && self.telemetry.denied_without_product_authority()
            && self.telemetry.record_sha256 == self.telemetry.canonical_record_sha256()
    }

    fn bind_product_call_status_row(&mut self, row: &ControlPlaneProductCallStatusRow) {
        self.telemetry.bind_product_call_status_row(row);
    }
}

/// Product-adapter call-status row exported after call-time revalidation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ControlPlaneProductCallStatusRow {
    /// Call-status row schema.
    pub schema: &'static str,
    /// Call-status row schema version.
    pub schema_version: u32,
    /// Implementing issue.
    pub issue: u64,
    /// Candidate key.
    pub candidate_key_sha256: String,
    /// Artifact digest.
    pub artifact_sha256: String,
    /// Runtime packet hash used for call-time revalidation.
    pub packet_hash: ArtifactChecksum,
    /// Caller-current invalidation checksum used for call-time revalidation.
    pub current_invalidation_checksum: ArtifactChecksum,
    /// Caller-current generation used for call-time revalidation.
    pub current_generation: u64,
    /// Consumer.
    pub consumer: String,
    /// Family.
    pub family: String,
    /// Final control-plane route.
    pub route: ControlPlaneRoute,
    /// Final control-plane reason.
    pub reason: ControlPlaneReason,
    /// Product lifecycle status for this adapter attempt.
    pub status: ControlPlaneProductCallStatus,
    /// Consumer-admission disposition.
    pub consumer_disposition: NativeInstallGateDisposition,
    /// Consumer-admission rejection code.
    pub consumer_rejection_code: Option<NativeInstallGateRejectionCode>,
    /// Call-time runtime outcome.
    pub runtime_outcome: NativeInstallGateRuntimeOutcome,
    /// Call-time runtime rejection code.
    pub runtime_rejection_code: Option<NativeInstallGateRejectionCode>,
    /// Product publication remains denied.
    pub product_publication_denied: bool,
    /// No ay registry entry was published.
    pub publish_ay_registry_entry: bool,
    /// No TY native handle was activated.
    pub activate_ty_native_handle: bool,
    /// No callable handle was exposed.
    pub expose_callable_handle: bool,
    /// Useful-native counter delta for this product-adapter attempt.
    pub useful_native_delta: u64,
    /// Whether this row proves deopt/baseline fallback readiness.
    pub deopt_ready: bool,
    /// Canonical call-status row SHA-256.
    pub record_sha256: String,
}

impl ControlPlaneProductCallStatusRow {
    fn new(
        candidate: &ControlPlaneCandidate,
        control_plane: &ControlPlaneDecision,
        consumer_admission: &NativeInstallGateConsumerAdmissionDecision,
        product_adapter: &ControlPlaneProductAdapterDecision,
        call_time_revalidation: &NativeInstallGateRuntimeTelemetryPacket,
    ) -> Self {
        let status = product_call_status(consumer_admission, call_time_revalidation);
        let product_publication_denied = product_adapter.denied_without_product_authority();
        let useful_native_delta = consumer_admission
            .telemetry
            .useful_native_delta
            .saturating_add(product_adapter.useful_native_delta)
            .saturating_add(product_adapter.telemetry.useful_native_delta)
            .saturating_add(call_time_revalidation.useful_native_delta);
        let deopt_ready = product_publication_denied
            && useful_native_delta == 0
            && product_adapter.callable_handle_id.is_none()
            && product_adapter.native_handle_id.is_none()
            && !product_adapter.installable_cache_hit_accepted;
        let mut row = Self {
            schema: JIT_EVERYWHERE_PRODUCT_CALL_STATUS_SCHEMA,
            schema_version: JIT_EVERYWHERE_PRODUCT_CALL_STATUS_SCHEMA_VERSION,
            issue: 748,
            candidate_key_sha256: candidate.candidate_key_sha256.clone(),
            artifact_sha256: candidate.artifact_sha256.clone(),
            packet_hash: call_time_revalidation.packet_hash,
            current_invalidation_checksum: call_time_revalidation.current_invalidation_checksum,
            current_generation: call_time_revalidation.current_generation,
            consumer: candidate.consumer.clone(),
            family: candidate.family.clone(),
            route: control_plane.route,
            reason: control_plane.reason,
            status,
            consumer_disposition: consumer_admission.disposition,
            consumer_rejection_code: consumer_admission.rejection_code,
            runtime_outcome: call_time_revalidation.runtime_outcome,
            runtime_rejection_code: call_time_revalidation.rejection_code,
            product_publication_denied,
            publish_ay_registry_entry: false,
            activate_ty_native_handle: false,
            expose_callable_handle: false,
            useful_native_delta,
            deopt_ready,
            record_sha256: String::new(),
        };
        row.record_sha256 = row.canonical_record_sha256();
        row
    }

    /// Return the stable hash of this call-status row.
    pub fn canonical_record_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_u64(&mut out, self.issue);
        put_str(&mut out, &self.candidate_key_sha256);
        put_str(&mut out, &self.artifact_sha256);
        put_checksum(&mut out, self.packet_hash);
        put_checksum(&mut out, self.current_invalidation_checksum);
        put_u64(&mut out, self.current_generation);
        put_str(&mut out, &self.consumer);
        put_str(&mut out, &self.family);
        put_str(&mut out, self.route.as_str());
        put_str(&mut out, self.reason.as_str());
        put_str(&mut out, self.status.as_str());
        put_str(&mut out, self.consumer_disposition.as_str());
        put_option_str(
            &mut out,
            self.consumer_rejection_code
                .map(NativeInstallGateRejectionCode::as_str),
        );
        put_str(&mut out, self.runtime_outcome.as_str());
        put_option_str(
            &mut out,
            self.runtime_rejection_code
                .map(NativeInstallGateRejectionCode::as_str),
        );
        put_bool(&mut out, self.product_publication_denied);
        put_bool(&mut out, self.publish_ay_registry_entry);
        put_bool(&mut out, self.activate_ty_native_handle);
        put_bool(&mut out, self.expose_callable_handle);
        put_u64(&mut out, self.useful_native_delta);
        put_bool(&mut out, self.deopt_ready);
        format!("sha256:{}", sha256_hex(&out))
    }

    /// Return true when the row proves product-native use stayed fail closed.
    pub fn fail_closed_deopt_ready(&self) -> bool {
        self.schema == JIT_EVERYWHERE_PRODUCT_CALL_STATUS_SCHEMA
            && self.schema_version == JIT_EVERYWHERE_PRODUCT_CALL_STATUS_SCHEMA_VERSION
            && self.issue == 748
            && self.product_publication_denied
            && !self.publish_ay_registry_entry
            && !self.activate_ty_native_handle
            && !self.expose_callable_handle
            && self.useful_native_delta == 0
            && self.deopt_ready
            && self.record_sha256 == self.canonical_record_sha256()
    }
}

/// Combined consumer-admission and product-adapter result for ay/TY product
/// boundaries.
///
/// Consumer admission can prove that a packet is admissible for a consumer
/// surface, but current Phase 9 product wiring must still keep publication
/// denied until parent product gates authorize activation. This type records
/// both facts in one production-facing result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ControlPlaneConsumerAdmissionProductDecision {
    /// Control-plane decision consumed by install-gate revalidation.
    pub control_plane: ControlPlaneDecision,
    /// ay/TY consumer-admission decision.
    pub consumer_admission: NativeInstallGateConsumerAdmissionDecision,
    /// Product registry/cache deny-remove adapter decision.
    pub product_adapter: ControlPlaneProductAdapterDecision,
    /// Call-time revalidation telemetry for this product-adapter attempt.
    pub call_time_revalidation: NativeInstallGateRuntimeTelemetryPacket,
    /// Product lifecycle/call-status row for this adapter attempt.
    pub call_status: ControlPlaneProductCallStatusRow,
    /// Consumer admission authorized ay registry insertion.
    pub consumer_allows_ay_registry: bool,
    /// Consumer admission authorized TY native activation.
    pub consumer_allows_ty_activation: bool,
    /// Product publication remains denied by the product adapter.
    pub product_publication_denied: bool,
    /// No ay registry entry may be published by this bridge.
    pub publish_ay_registry_entry: bool,
    /// No TY native handle may be activated by this bridge.
    pub activate_ty_native_handle: bool,
    /// No callable handle may be exposed by this bridge.
    pub expose_callable_handle: bool,
    /// Useful-native counter delta for this bridge.
    pub useful_native_delta: u64,
}

impl ControlPlaneConsumerAdmissionProductDecision {
    fn new(
        candidate: &ControlPlaneCandidate,
        control_plane: ControlPlaneDecision,
        consumer_admission: NativeInstallGateConsumerAdmissionDecision,
        product_adapter: ControlPlaneProductAdapterDecision,
        call_time_revalidation: NativeInstallGateRuntimeTelemetryPacket,
    ) -> Self {
        let consumer_allows_ay_registry = consumer_admission.disposition.is_installable()
            && consumer_admission.rejection_code.is_none()
            && consumer_admission.actions.ay_registry_insert;
        let consumer_allows_ty_activation = consumer_admission.disposition.is_installable()
            && consumer_admission.rejection_code.is_none()
            && consumer_admission.actions.ty_native_activate;
        let call_status = ControlPlaneProductCallStatusRow::new(
            candidate,
            &control_plane,
            &consumer_admission,
            &product_adapter,
            &call_time_revalidation,
        );
        let mut product_adapter = product_adapter;
        product_adapter.bind_product_call_status_row(&call_status);
        let product_publication_denied = product_adapter.denied_without_product_authority();
        Self {
            control_plane,
            consumer_admission,
            product_adapter,
            call_time_revalidation,
            call_status,
            consumer_allows_ay_registry,
            consumer_allows_ty_activation,
            product_publication_denied,
            publish_ay_registry_entry: false,
            activate_ty_native_handle: false,
            expose_callable_handle: false,
            useful_native_delta: 0,
        }
    }

    /// Return true when consumer admission and product adapter telemetry remain
    /// bound while product publication is still denied with zero useful-native
    /// credit.
    pub fn publication_blocked_without_product_authority(&self) -> bool {
        self.product_publication_denied
            && self.product_adapter.denied_without_product_authority()
            && !self.publish_ay_registry_entry
            && !self.activate_ty_native_handle
            && !self.expose_callable_handle
            && self.useful_native_delta == 0
            && self.consumer_admission.telemetry.useful_native_delta == 0
            && self.product_adapter.telemetry.useful_native_delta == 0
            && self.call_time_revalidation.useful_native_delta == 0
            && self.call_status.fail_closed_deopt_ready()
            && self
                .product_adapter
                .telemetry
                .valid_for_product_call_status_row(&self.call_status)
    }
}

/// Structured telemetry/replay binding for product-adapter deny/remove results.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ControlPlaneProductAdapterTelemetryPacket {
    /// Telemetry schema.
    pub schema: &'static str,
    /// Telemetry schema version.
    pub schema_version: u32,
    /// Implementing issue.
    pub issue: u64,
    /// Candidate key.
    pub candidate_key_sha256: String,
    /// Artifact digest.
    pub artifact_sha256: String,
    /// Consumer.
    pub consumer: String,
    /// Family.
    pub family: String,
    /// Final route.
    pub route: ControlPlaneRoute,
    /// Decision reason.
    pub reason: ControlPlaneReason,
    /// Control-plane decision telemetry record hash.
    pub control_plane_record_sha256: String,
    /// Product call-status row status bound after product-admission revalidation.
    pub product_call_status: Option<ControlPlaneProductCallStatus>,
    /// Product call-status row SHA-256 bound after product-admission revalidation.
    pub product_call_status_record_sha256: Option<String>,
    /// Whether baseline routing was recorded as authoritative.
    pub baseline_route_recorded: bool,
    /// Whether a callable registry entry was removed.
    pub callable_registry_removed: bool,
    /// Whether an installable-cache entry was removed.
    pub installable_cache_removed: bool,
    /// Whether a ay registry entry was removed.
    pub ay_registry_removed: bool,
    /// Whether a TY native activation entry was removed.
    pub ty_native_removed: bool,
    /// Replay root retained after removal.
    pub retained_replay_root_sha256: Option<String>,
    /// Telemetry key retained after removal.
    pub retained_telemetry_key: Option<String>,
    /// No callable handle is returned by this adapter.
    pub callable_handle_id: Option<String>,
    /// No native handle is returned by this adapter.
    pub native_handle_id: Option<String>,
    /// No installable-cache hit is accepted by this adapter.
    pub installable_cache_hit_accepted: bool,
    /// Useful-native counter delta.
    pub useful_native_delta: u64,
    /// Canonical telemetry record SHA-256.
    pub record_sha256: String,
}

impl ControlPlaneProductAdapterTelemetryPacket {
    /// Return the stable hash of this telemetry packet.
    pub fn canonical_record_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_u64(&mut out, self.issue);
        put_str(&mut out, &self.candidate_key_sha256);
        put_str(&mut out, &self.artifact_sha256);
        put_str(&mut out, &self.consumer);
        put_str(&mut out, &self.family);
        put_str(&mut out, self.route.as_str());
        put_str(&mut out, self.reason.as_str());
        put_str(&mut out, &self.control_plane_record_sha256);
        put_option_str(
            &mut out,
            self.product_call_status
                .map(ControlPlaneProductCallStatus::as_str),
        );
        put_option_str(&mut out, self.product_call_status_record_sha256.as_deref());
        put_bool(&mut out, self.baseline_route_recorded);
        put_bool(&mut out, self.callable_registry_removed);
        put_bool(&mut out, self.installable_cache_removed);
        put_bool(&mut out, self.ay_registry_removed);
        put_bool(&mut out, self.ty_native_removed);
        put_option_str(&mut out, self.retained_replay_root_sha256.as_deref());
        put_option_str(&mut out, self.retained_telemetry_key.as_deref());
        put_option_str(&mut out, self.callable_handle_id.as_deref());
        put_option_str(&mut out, self.native_handle_id.as_deref());
        put_bool(&mut out, self.installable_cache_hit_accepted);
        put_u64(&mut out, self.useful_native_delta);
        format!("sha256:{}", sha256_hex(&out))
    }

    /// Return true when this telemetry packet records no product-native authority.
    pub fn denied_without_product_authority(&self) -> bool {
        self.schema == JIT_EVERYWHERE_PRODUCT_ADAPTER_EVENT_SCHEMA
            && self.schema_version == JIT_EVERYWHERE_PRODUCT_ADAPTER_EVENT_SCHEMA_VERSION
            && self.issue == 749
            && self.baseline_route_recorded
            && !missing_required_text(&self.control_plane_record_sha256)
            && (self.product_call_status.is_some()
                == self.product_call_status_record_sha256.is_some())
            && self.callable_handle_id.is_none()
            && self.native_handle_id.is_none()
            && !self.installable_cache_hit_accepted
            && self.useful_native_delta == 0
    }

    /// Bind this telemetry packet to the call-status row created for the same
    /// product-admission attempt.
    pub fn bind_product_call_status_row(&mut self, row: &ControlPlaneProductCallStatusRow) {
        self.product_call_status = Some(row.status);
        self.product_call_status_record_sha256 = Some(row.record_sha256.clone());
        self.record_sha256 = self.canonical_record_sha256();
    }

    /// Return true when this telemetry packet matches the supplied call-status row.
    pub fn valid_for_product_call_status_row(
        &self,
        row: &ControlPlaneProductCallStatusRow,
    ) -> bool {
        self.denied_without_product_authority()
            && row.fail_closed_deopt_ready()
            && self.product_call_status == Some(row.status)
            && self.product_call_status_record_sha256.as_deref() == Some(row.record_sha256.as_str())
            && self.record_sha256 == self.canonical_record_sha256()
    }
}

/// Telemetry emitted for a control-plane decision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ControlPlaneTelemetryPacket {
    /// Telemetry schema.
    pub schema: &'static str,
    /// Telemetry schema version.
    pub schema_version: u32,
    /// Implementing issue.
    pub issue: u64,
    /// Candidate key.
    pub candidate_key_sha256: String,
    /// Consumer.
    pub consumer: String,
    /// Family.
    pub family: String,
    /// Artifact digest.
    pub artifact_sha256: String,
    /// Rollout mode.
    pub mode: ControlPlaneMode,
    /// Final route.
    pub route: ControlPlaneRoute,
    /// Decision reason.
    pub reason: ControlPlaneReason,
    /// Matched kill-switch scope.
    pub kill_switch_scope: Option<ControlPlaneKillSwitchScope>,
    /// Matched kill-switch hash.
    pub kill_switch_sha256: Option<String>,
    /// Matched revocation hash.
    pub revocation_sha256: Option<String>,
    /// Whether baseline routing is authoritative.
    pub baseline_authoritative: bool,
    /// Replay root retained for diagnostics.
    pub replay_root_sha256: String,
    /// Telemetry key retained for diagnostics.
    pub telemetry_key: String,
    /// Side effects.
    pub side_effects: ControlPlaneSideEffects,
    /// Canonical telemetry record SHA-256.
    pub record_sha256: String,
}

impl ControlPlaneTelemetryPacket {
    /// Return the stable hash of this telemetry packet.
    pub fn canonical_record_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_u64(&mut out, self.issue);
        put_str(&mut out, &self.candidate_key_sha256);
        put_str(&mut out, &self.consumer);
        put_str(&mut out, &self.family);
        put_str(&mut out, &self.artifact_sha256);
        put_str(&mut out, self.mode.as_str());
        put_str(&mut out, self.route.as_str());
        put_str(&mut out, self.reason.as_str());
        put_option_str(
            &mut out,
            self.kill_switch_scope
                .map(ControlPlaneKillSwitchScope::as_str),
        );
        put_option_str(&mut out, self.kill_switch_sha256.as_deref());
        put_option_str(&mut out, self.revocation_sha256.as_deref());
        put_bool(&mut out, self.baseline_authoritative);
        put_str(&mut out, &self.replay_root_sha256);
        put_str(&mut out, &self.telemetry_key);
        put_side_effects(&mut out, self.side_effects);
        format!("sha256:{}", sha256_hex(&out))
    }
}

/// Control-plane routing decision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ControlPlaneDecision {
    /// Final route.
    pub route: ControlPlaneRoute,
    /// Stable reason.
    pub reason: ControlPlaneReason,
    /// Matched kill-switch scope.
    pub kill_switch_scope: Option<ControlPlaneKillSwitchScope>,
    /// Matched kill-switch hash.
    pub kill_switch_sha256: Option<String>,
    /// Matched revocation hash.
    pub revocation_sha256: Option<String>,
    /// Whether baseline execution remains authoritative.
    pub baseline_authoritative: bool,
    /// Whether native execution is product-authoritative.
    pub native_authoritative: bool,
    /// Side effects.
    pub side_effects: ControlPlaneSideEffects,
    /// Telemetry packet.
    pub telemetry: ControlPlaneTelemetryPacket,
}

impl ControlPlaneDecision {
    /// Return true when the decision cannot authorize native product use.
    pub fn is_deny_or_baseline_only(&self) -> bool {
        self.baseline_authoritative
            && !self.native_authoritative
            && self.side_effects.all_install_authority_blocked()
            && self.telemetry.side_effects.all_install_authority_blocked()
            && self.telemetry.record_sha256 == self.telemetry.canonical_record_sha256()
    }
}

/// Local publication state used by focused tests and future adapters.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ControlPlanePublicationState {
    callable_registry: BTreeSet<String>,
    installable_cache: BTreeSet<String>,
    ay_registry: BTreeSet<String>,
    ty_native_handles: BTreeSet<String>,
    replay_roots: BTreeMap<String, String>,
    telemetry_keys: BTreeMap<String, String>,
}

impl ControlPlanePublicationState {
    /// Publish a local harness entry. This is used only to prove removal.
    pub fn publish_local_fixture(&mut self, candidate: &ControlPlaneCandidate) {
        self.callable_registry
            .insert(candidate.artifact_sha256.clone());
        self.installable_cache
            .insert(candidate.artifact_sha256.clone());
        self.replay_roots.insert(
            candidate.artifact_sha256.clone(),
            candidate.replay_root_sha256.clone(),
        );
        self.telemetry_keys.insert(
            candidate.artifact_sha256.clone(),
            candidate.telemetry_key.clone(),
        );
    }

    /// Record existing product publication state for deny/remove adapters.
    ///
    /// This models pre-existing downstream state that must be removed when a
    /// control-plane decision routes back to baseline. It does not create new
    /// install authority; callers use it to prove removal behavior.
    pub fn record_existing_product_publication(&mut self, candidate: &ControlPlaneCandidate) {
        self.publish_local_fixture(candidate);
        match candidate.consumer.as_str() {
            "ay" => {
                self.ay_registry.insert(candidate.artifact_sha256.clone());
            }
            "ty" => {
                self.ty_native_handles
                    .insert(candidate.artifact_sha256.clone());
            }
            _ => {}
        }
    }

    /// Remove callable/installable state but retain replay/telemetry evidence.
    pub fn remove_callable_install_state(&mut self, artifact_sha256: &str) {
        self.callable_registry.remove(artifact_sha256);
        self.installable_cache.remove(artifact_sha256);
        self.ay_registry.remove(artifact_sha256);
        self.ty_native_handles.remove(artifact_sha256);
    }

    /// Apply a control-plane decision to product registry/cache state.
    pub fn apply_product_adapter_decision(
        &mut self,
        candidate: &ControlPlaneCandidate,
        decision: &ControlPlaneDecision,
    ) -> ControlPlaneProductAdapterDecision {
        self.replay_roots.insert(
            candidate.artifact_sha256.clone(),
            candidate.replay_root_sha256.clone(),
        );
        self.telemetry_keys.insert(
            candidate.artifact_sha256.clone(),
            candidate.telemetry_key.clone(),
        );

        let callable_registry_removed = self.callable_registry.remove(&candidate.artifact_sha256);
        let installable_cache_removed = self.installable_cache.remove(&candidate.artifact_sha256);
        let ay_registry_removed = self.ay_registry.remove(&candidate.artifact_sha256);
        let ty_native_removed = self.ty_native_handles.remove(&candidate.artifact_sha256);

        let retained_replay_root_sha256 = self
            .retained_replay_root(&candidate.artifact_sha256)
            .cloned();
        let retained_telemetry_key = self
            .retained_telemetry_key(&candidate.artifact_sha256)
            .cloned();

        let mut telemetry = ControlPlaneProductAdapterTelemetryPacket {
            schema: JIT_EVERYWHERE_PRODUCT_ADAPTER_EVENT_SCHEMA,
            schema_version: JIT_EVERYWHERE_PRODUCT_ADAPTER_EVENT_SCHEMA_VERSION,
            issue: 749,
            candidate_key_sha256: candidate.candidate_key_sha256.clone(),
            artifact_sha256: candidate.artifact_sha256.clone(),
            consumer: candidate.consumer.clone(),
            family: candidate.family.clone(),
            route: decision.route,
            reason: decision.reason,
            control_plane_record_sha256: decision.telemetry.record_sha256.clone(),
            product_call_status: None,
            product_call_status_record_sha256: None,
            baseline_route_recorded: decision.baseline_authoritative,
            callable_registry_removed,
            installable_cache_removed,
            ay_registry_removed,
            ty_native_removed,
            retained_replay_root_sha256: retained_replay_root_sha256.clone(),
            retained_telemetry_key: retained_telemetry_key.clone(),
            callable_handle_id: None,
            native_handle_id: None,
            installable_cache_hit_accepted: false,
            useful_native_delta: 0,
            record_sha256: String::new(),
        };
        telemetry.record_sha256 = telemetry.canonical_record_sha256();

        ControlPlaneProductAdapterDecision {
            candidate_key_sha256: candidate.candidate_key_sha256.clone(),
            artifact_sha256: candidate.artifact_sha256.clone(),
            route: decision.route,
            reason: decision.reason,
            baseline_route_recorded: decision.baseline_authoritative,
            callable_registry_removed,
            installable_cache_removed,
            ay_registry_removed,
            ty_native_removed,
            retained_replay_root_sha256,
            retained_telemetry_key,
            callable_handle_id: None,
            native_handle_id: None,
            installable_cache_hit_accepted: false,
            useful_native_delta: 0,
            telemetry,
        }
    }

    /// Return true when a callable registry entry exists.
    pub fn has_callable(&self, artifact_sha256: &str) -> bool {
        self.callable_registry.contains(artifact_sha256)
    }

    /// Return true when an installable cache entry exists.
    pub fn has_installable_cache_entry(&self, artifact_sha256: &str) -> bool {
        self.installable_cache.contains(artifact_sha256)
    }

    /// Return true when a ay registry entry exists.
    pub fn has_ay_registry_entry(&self, artifact_sha256: &str) -> bool {
        self.ay_registry.contains(artifact_sha256)
    }

    /// Return true when a TY native activation entry exists.
    pub fn has_ty_native_entry(&self, artifact_sha256: &str) -> bool {
        self.ty_native_handles.contains(artifact_sha256)
    }

    /// Return retained replay root for an artifact.
    pub fn retained_replay_root(&self, artifact_sha256: &str) -> Option<&String> {
        self.replay_roots.get(artifact_sha256)
    }

    /// Return retained telemetry key for an artifact.
    pub fn retained_telemetry_key(&self, artifact_sha256: &str) -> Option<&String> {
        self.telemetry_keys.get(artifact_sha256)
    }
}

/// Deny/remove control plane.
#[derive(Debug, Clone, Default)]
pub struct JitEverywhereControlPlane {
    kill_switches: Vec<ControlPlaneKillSwitch>,
    revocations: BTreeMap<String, ControlPlaneRevocation>,
    publication_state: ControlPlanePublicationState,
}

impl JitEverywhereControlPlane {
    /// Build an empty control plane.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add one kill-switch rule.
    pub fn add_kill_switch(&mut self, switch: ControlPlaneKillSwitch) {
        self.kill_switches.push(switch);
    }

    /// Publish one local fixture entry to prove removal semantics.
    pub fn publish_local_fixture(&mut self, candidate: &ControlPlaneCandidate) {
        self.publication_state.publish_local_fixture(candidate);
    }

    /// Record existing product registry/cache state for deny/remove adapters.
    pub fn record_existing_product_publication(&mut self, candidate: &ControlPlaneCandidate) {
        self.publication_state
            .record_existing_product_publication(candidate);
    }

    /// Add one active revocation and remove callable/installable state.
    pub fn revoke_artifact(&mut self, revocation: ControlPlaneRevocation) {
        self.publication_state
            .remove_callable_install_state(&revocation.artifact_sha256);
        self.revocations
            .insert(revocation.artifact_sha256.clone(), revocation);
    }

    /// Route a product call and apply deny/remove registry/cache effects.
    ///
    /// This is the product-adapter surface for #739 prework. It cannot publish
    /// or return native handles; it only removes any existing product state and
    /// records that baseline remains authoritative.
    pub fn route_product_adapter_call(
        &mut self,
        candidate: &ControlPlaneCandidate,
        gate_evidence: ControlPlaneGateEvidence,
    ) -> ControlPlaneProductAdapterDecision {
        let decision = self.evaluate(candidate, gate_evidence, false);
        self.publication_state
            .apply_product_adapter_decision(candidate, &decision)
    }

    /// Route ay/TY consumer admission through the product adapter.
    ///
    /// This is the product-boundary surface for #750. It revalidates the shared
    /// install-gate packet with the current control-plane decision, records the
    /// ay/TY consumer-admission verdict, and applies deny/remove product
    /// adapter effects. It deliberately cannot publish registry entries,
    /// activate native handles, expose callable handles, or credit useful-native
    /// counters.
    pub fn route_consumer_admission_product_adapter(
        &mut self,
        candidate: &ControlPlaneCandidate,
        gate_evidence: ControlPlaneGateEvidence,
        packet: &NativeInstallGatePacket,
        expected_packet_hash: Option<ArtifactChecksum>,
        evidence: &NativeInstallGateConsumerAdmissionEvidence,
    ) -> ControlPlaneConsumerAdmissionProductDecision {
        let current = NativeInstallGateRevalidationInput::from_packet(packet);
        self.route_consumer_admission_product_adapter_with_current(
            candidate,
            gate_evidence,
            packet,
            expected_packet_hash,
            &current,
            evidence,
        )
    }

    /// Route ay/TY consumer admission through the product adapter with
    /// caller-current call-time freshness state.
    ///
    /// This is the #748 revalidation surface for product adapters. A stale
    /// current generation, domain, revocation, or live deny-control packet is
    /// consumed before product publication can be retained. The result remains
    /// deny/remove-only and cannot expose native product handles.
    pub fn route_consumer_admission_product_adapter_with_current(
        &mut self,
        candidate: &ControlPlaneCandidate,
        gate_evidence: ControlPlaneGateEvidence,
        packet: &NativeInstallGatePacket,
        expected_packet_hash: Option<ArtifactChecksum>,
        current: &NativeInstallGateRevalidationInput,
        evidence: &NativeInstallGateConsumerAdmissionEvidence,
    ) -> ControlPlaneConsumerAdmissionProductDecision {
        let control_plane = self.evaluate(candidate, gate_evidence, false);
        let current =
            install_gate_revalidation_with_control_plane_current(packet, &control_plane, current);
        let consumer_admission = native_install_gate_consumer_admission(
            packet,
            expected_packet_hash,
            &current,
            evidence,
        );
        let call_time_revalidation =
            native_install_gate_runtime_telemetry(packet, expected_packet_hash, &current, false);
        let product_adapter = self
            .publication_state
            .apply_product_adapter_decision(candidate, &control_plane);
        ControlPlaneConsumerAdmissionProductDecision::new(
            candidate,
            control_plane,
            consumer_admission,
            product_adapter,
            call_time_revalidation,
        )
    }

    /// Evaluate a new call dispatch. Denied candidates route to baseline.
    pub fn route_new_call(
        &self,
        candidate: &ControlPlaneCandidate,
        gate_evidence: ControlPlaneGateEvidence,
    ) -> ControlPlaneDecision {
        self.evaluate(candidate, gate_evidence, false)
    }

    /// Guard an in-flight native call before invocation.
    pub fn guard_in_flight_call(
        &self,
        candidate: &ControlPlaneCandidate,
        gate_evidence: ControlPlaneGateEvidence,
    ) -> ControlPlaneDecision {
        self.evaluate(candidate, gate_evidence, true)
    }

    /// Attempt re-enable. Without accepted gates this is always rejected.
    ///
    /// Even with accepted gates, this issue returns `ProductGateRequired`
    /// without publishing callable/install authority; product activation is
    /// owned by later parent-gated paths.
    pub fn attempt_reenable(
        &self,
        candidate: &ControlPlaneCandidate,
        gate_evidence: ControlPlaneGateEvidence,
    ) -> ControlPlaneDecision {
        self.evaluate(candidate, gate_evidence, false)
    }

    /// Return local publication state for tests/adapters.
    pub fn publication_state(&self) -> &ControlPlanePublicationState {
        &self.publication_state
    }

    fn evaluate(
        &self,
        candidate: &ControlPlaneCandidate,
        gate_evidence: ControlPlaneGateEvidence,
        in_flight: bool,
    ) -> ControlPlaneDecision {
        if !candidate.has_required_identity() {
            return self.decision(
                candidate,
                ControlPlaneRoute::Baseline,
                ControlPlaneReason::MissingProductGateEvidence,
                None,
                None,
                None,
                in_flight,
            );
        }

        if let Some(switch) = self
            .kill_switches
            .iter()
            .find(|switch| switch.applies_to(candidate))
        {
            return self.decision(
                candidate,
                ControlPlaneRoute::Baseline,
                ControlPlaneReason::KillSwitchActive,
                Some(switch.scope),
                Some(switch.rule_sha256.clone()),
                None,
                in_flight,
            );
        }

        if let Some(revocation) = self
            .revocations
            .get(&candidate.artifact_sha256)
            .filter(|revocation| revocation.applies_to(candidate))
        {
            return self.decision(
                candidate,
                ControlPlaneRoute::Baseline,
                ControlPlaneReason::ArtifactRevoked,
                None,
                None,
                Some(revocation.revocation_sha256.clone()),
                in_flight,
            );
        }

        match candidate.mode {
            ControlPlaneMode::ProfileOnly => self.decision(
                candidate,
                ControlPlaneRoute::ProfileOnlyRetained,
                ControlPlaneReason::ProfileOnlyNonCallable,
                None,
                None,
                None,
                in_flight,
            ),
            ControlPlaneMode::ShadowOnly => self.decision(
                candidate,
                ControlPlaneRoute::ShadowOnlyRetained,
                ControlPlaneReason::ShadowOnlyNonCallable,
                None,
                None,
                None,
                in_flight,
            ),
            ControlPlaneMode::CanaryInstallable | ControlPlaneMode::ActiveInstallable
                if !gate_evidence.accepted() =>
            {
                self.decision(
                    candidate,
                    ControlPlaneRoute::Baseline,
                    ControlPlaneReason::MissingProductGateEvidence,
                    None,
                    None,
                    None,
                    in_flight,
                )
            }
            ControlPlaneMode::CanaryInstallable | ControlPlaneMode::ActiveInstallable => self
                .decision(
                    candidate,
                    ControlPlaneRoute::ProductGateRequired,
                    ControlPlaneReason::ProductActivationRequired,
                    None,
                    None,
                    None,
                    in_flight,
                ),
        }
    }

    fn decision(
        &self,
        candidate: &ControlPlaneCandidate,
        route: ControlPlaneRoute,
        reason: ControlPlaneReason,
        kill_switch_scope: Option<ControlPlaneKillSwitchScope>,
        kill_switch_sha256: Option<String>,
        revocation_sha256: Option<String>,
        _in_flight: bool,
    ) -> ControlPlaneDecision {
        let side_effects = ControlPlaneSideEffects::default();
        let mut telemetry = ControlPlaneTelemetryPacket {
            schema: JIT_EVERYWHERE_CONTROL_PLANE_SCHEMA,
            schema_version: JIT_EVERYWHERE_CONTROL_PLANE_SCHEMA_VERSION,
            issue: 739,
            candidate_key_sha256: candidate.candidate_key_sha256.clone(),
            consumer: candidate.consumer.clone(),
            family: candidate.family.clone(),
            artifact_sha256: candidate.artifact_sha256.clone(),
            mode: candidate.mode,
            route,
            reason,
            kill_switch_scope,
            kill_switch_sha256,
            revocation_sha256,
            baseline_authoritative: true,
            replay_root_sha256: candidate.replay_root_sha256.clone(),
            telemetry_key: candidate.telemetry_key.clone(),
            side_effects,
            record_sha256: String::new(),
        };
        telemetry.record_sha256 = telemetry.canonical_record_sha256();
        ControlPlaneDecision {
            route,
            reason,
            kill_switch_scope: telemetry.kill_switch_scope,
            kill_switch_sha256: telemetry.kill_switch_sha256.clone(),
            revocation_sha256: telemetry.revocation_sha256.clone(),
            baseline_authoritative: true,
            native_authoritative: false,
            side_effects,
            telemetry,
        }
    }
}

/// Convert a deny/remove control-plane decision into install-gate deny-control metadata.
///
/// This is intentionally one-way and fail-closed: only active kill-switch and
/// revocation decisions produce a deny-control packet. Non-callable/profile/
/// shadow/product-gate decisions stay modeled by the install-gate disposition
/// and do not synthesize install authority.
pub fn install_gate_deny_control_for_decision(
    packet: &NativeInstallGatePacket,
    decision: &ControlPlaneDecision,
) -> Option<NativeInstallGateDenyControlPlane> {
    let mut deny = match decision.reason {
        ControlPlaneReason::KillSwitchActive => {
            let scope = decision.kill_switch_scope?;
            let mut deny = NativeInstallGateDenyControlPlane::active(
                install_gate_deny_scope(scope),
                NativeInstallGateDenyReason::KillSwitch,
            );
            bind_install_gate_deny_scope(&mut deny, packet, scope);
            deny
        }
        ControlPlaneReason::ArtifactRevoked => {
            let mut deny = NativeInstallGateDenyControlPlane::active(
                NativeInstallGateDenyScope::Artifact,
                NativeInstallGateDenyReason::Revoked,
            );
            deny.artifact_id = Some(packet.artifact.artifact_id.clone());
            deny
        }
        _ => return None,
    };
    deny = deny.with_canonical_deny_sha256();
    Some(deny)
}

/// Build install-gate revalidation input that consumes a control-plane decision.
///
/// Callers can use the returned context with
/// `validate_native_install_gate_packet_with_current` or runtime telemetry.
/// Revocations also set the current `revoked` bit so stale cached packets
/// fail closed even if a future caller ignores the scoped deny-control packet.
pub fn install_gate_revalidation_with_control_plane(
    packet: &NativeInstallGatePacket,
    decision: &ControlPlaneDecision,
) -> NativeInstallGateRevalidationInput {
    let current = NativeInstallGateRevalidationInput::from_packet(packet);
    install_gate_revalidation_with_control_plane_current(packet, decision, &current)
}

/// Overlay a control-plane decision onto caller-current install-gate state.
pub fn install_gate_revalidation_with_control_plane_current(
    packet: &NativeInstallGatePacket,
    decision: &ControlPlaneDecision,
    current: &NativeInstallGateRevalidationInput,
) -> NativeInstallGateRevalidationInput {
    let mut current = current.clone();
    if decision.reason == ControlPlaneReason::ArtifactRevoked {
        current.revoked = true;
    }
    if let Some(deny_control) = install_gate_deny_control_for_decision(packet, decision) {
        current.deny_control = Some(deny_control);
    }
    current
}

/// Evaluate ay/TY consumer admission through the live control-plane decision.
///
/// This composes the deny/remove bridge with consumer admission so registry or
/// activation adapters cannot accidentally skip call-time revocation and
/// kill-switch revalidation. It remains data-only and only returns the
/// admission decision; product adapters still own any handle publication.
pub fn consumer_admission_with_control_plane(
    packet: &NativeInstallGatePacket,
    expected_packet_hash: Option<ArtifactChecksum>,
    decision: &ControlPlaneDecision,
    evidence: &NativeInstallGateConsumerAdmissionEvidence,
) -> NativeInstallGateConsumerAdmissionDecision {
    let current = install_gate_revalidation_with_control_plane(packet, decision);
    native_install_gate_consumer_admission(packet, expected_packet_hash, &current, evidence)
}

fn install_gate_deny_scope(scope: ControlPlaneKillSwitchScope) -> NativeInstallGateDenyScope {
    match scope {
        ControlPlaneKillSwitchScope::Global => NativeInstallGateDenyScope::Global,
        ControlPlaneKillSwitchScope::Consumer => NativeInstallGateDenyScope::Consumer,
        ControlPlaneKillSwitchScope::Family => NativeInstallGateDenyScope::Family,
        ControlPlaneKillSwitchScope::Artifact => NativeInstallGateDenyScope::Artifact,
        ControlPlaneKillSwitchScope::TargetProofPolicy => {
            NativeInstallGateDenyScope::TargetProofPolicy
        }
        ControlPlaneKillSwitchScope::Mode => NativeInstallGateDenyScope::Mode,
    }
}

fn bind_install_gate_deny_scope(
    deny: &mut NativeInstallGateDenyControlPlane,
    packet: &NativeInstallGatePacket,
    scope: ControlPlaneKillSwitchScope,
) {
    match scope {
        ControlPlaneKillSwitchScope::Global => {}
        ControlPlaneKillSwitchScope::Consumer => {
            deny.consumer = Some(packet.consumer.clone());
        }
        ControlPlaneKillSwitchScope::Family => {
            deny.consumer = Some(packet.consumer.clone());
            deny.family = Some(packet.consumer_mode.clone());
        }
        ControlPlaneKillSwitchScope::Artifact => {
            deny.artifact_id = Some(packet.artifact.artifact_id.clone());
        }
        ControlPlaneKillSwitchScope::TargetProofPolicy => {
            deny.target_checksum = Some(packet.artifact.target_checksum);
            deny.proof_policy_checksum = Some(packet.artifact.proof_policy_checksum);
        }
        ControlPlaneKillSwitchScope::Mode => {
            deny.mode = Some(packet.requested_authority);
        }
    }
}

fn product_call_status(
    consumer_admission: &NativeInstallGateConsumerAdmissionDecision,
    call_time_revalidation: &NativeInstallGateRuntimeTelemetryPacket,
) -> ControlPlaneProductCallStatus {
    match call_time_revalidation.runtime_outcome {
        NativeInstallGateRuntimeOutcome::StaleDeopt => ControlPlaneProductCallStatus::StaleDeopt,
        NativeInstallGateRuntimeOutcome::RevokedDeopt => {
            ControlPlaneProductCallStatus::RevokedDeopt
        }
        NativeInstallGateRuntimeOutcome::KillSwitchDeopt => {
            ControlPlaneProductCallStatus::KillSwitchDeopt
        }
        NativeInstallGateRuntimeOutcome::InvalidatedDeopt => {
            ControlPlaneProductCallStatus::InvalidatedDeopt
        }
        NativeInstallGateRuntimeOutcome::RejectedDeopt => {
            if consumer_admission.disposition.is_installable() {
                ControlPlaneProductCallStatus::RejectedDeopt
            } else {
                ControlPlaneProductCallStatus::ConsumerRejected
            }
        }
        NativeInstallGateRuntimeOutcome::NativeUseful
        | NativeInstallGateRuntimeOutcome::BaselineFallback
        | NativeInstallGateRuntimeOutcome::MetadataOnly => {
            if consumer_admission.disposition.is_installable()
                && consumer_admission.rejection_code.is_none()
            {
                ControlPlaneProductCallStatus::AcceptedPendingProductGate
            } else {
                ControlPlaneProductCallStatus::ConsumerRejected
            }
        }
    }
}

fn put_side_effects(out: &mut Vec<u8>, side_effects: ControlPlaneSideEffects) {
    put_bool(out, side_effects.callable_handle_published);
    put_bool(out, side_effects.installable_cache_hit_accepted);
    put_bool(out, side_effects.ay_registry_inserted);
    put_bool(out, side_effects.ty_native_activated);
    put_bool(out, side_effects.baseline_replaced);
    put_bool(out, side_effects.native_invocation_allowed);
    put_u64(out, side_effects.useful_native_delta);
}

fn put_str(out: &mut Vec<u8>, value: &str) {
    put_u64(out, value.len() as u64);
    out.extend_from_slice(value.as_bytes());
}

fn put_option_str(out: &mut Vec<u8>, value: Option<&str>) {
    if let Some(value) = value {
        put_bool(out, true);
        put_str(out, value);
    } else {
        put_bool(out, false);
    }
}

fn put_u32(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_checksum(out: &mut Vec<u8>, value: ArtifactChecksum) {
    out.extend_from_slice(&value.get().to_le_bytes());
}

fn put_bool(out: &mut Vec<u8>, value: bool) {
    out.push(u8::from(value));
}

fn missing_required_text(value: &str) -> bool {
    value.trim().is_empty()
}
