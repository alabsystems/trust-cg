// trust-cg-codegen/jit_ty_canary_allowlist.rs - TY canary allowlist prework
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Data-only TY canary allowlist readiness model.
//!
//! This module validates exact TY canary tuples and required evidence, but it
//! deliberately does not publish callable handles, activate TY native
//! dispatch, replace baseline execution, or increment useful-native counters.

use std::collections::BTreeSet;

use crate::jit_contract::ArtifactChecksum;
use crate::jit_control_plane::{
    ControlPlaneCandidate, ControlPlaneConsumerAdmissionProductDecision, ControlPlaneDecision,
    ControlPlaneGateEvidence, JitEverywhereControlPlane, consumer_admission_with_control_plane,
};
use crate::jit_diagnostics::sha256_hex;
use crate::jit_install_gate::{
    NativeInstallGateConsumerAdmissionDecision, NativeInstallGateConsumerAdmissionEvidence,
    NativeInstallGatePacket, NativeInstallGateRevalidationInput,
    TY_NATIVE_FUSED_PROOF_FACT_VERIFIED, TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA,
};
use crate::target::Target;

/// Stable schema tag for TY canary allowlist decisions.
pub const JIT_TY_CANARY_ALLOWLIST_SCHEMA: &str = "trust-cg.jit_everywhere.ty_canary_allowlist.v1";

/// Stable numeric schema version for TY canary allowlist decisions.
pub const JIT_TY_CANARY_ALLOWLIST_SCHEMA_VERSION: u32 = 1;

/// Stable validator-id separator for explicit TY trust_ir proof-fact bindings.
pub const TY_CANARY_TRUST_IR_PROOF_FACT_BINDINGS_PREFIX: &str = "|ty_trust_ir_proof_facts:v1|";

/// TY canary family.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum TyCanaryFamily {
    /// One deterministic action cluster.
    ActionCluster,
    /// One deterministic fingerprint helper family.
    FingerprintHelper,
}

impl TyCanaryFamily {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ActionCluster => "action_cluster",
            Self::FingerprintHelper => "fingerprint_helper",
        }
    }
}

/// Candidate mode at the canary boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TyCanaryCandidateMode {
    /// Profile-only candidates are not callable.
    ProfileOnly,
    /// Replay-only candidates are not callable.
    ReplayOnly,
    /// Shadow-only candidates are not callable.
    ShadowOnly,
    /// Candidate requests canary callable authority for this exact tuple.
    CanaryInstallable,
}

impl TyCanaryCandidateMode {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ProfileOnly => "profile_only",
            Self::ReplayOnly => "replay_only",
            Self::ShadowOnly => "shadow_only",
            Self::CanaryInstallable => "canary_installable",
        }
    }
}

/// Runtime generation tuple for a TY canary candidate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TyCanaryGenerationTuple {
    /// Arena generation.
    pub arena_generation: u64,
    /// Action generation.
    pub action_generation: u64,
    /// Fingerprint generation.
    pub fingerprint_generation: u64,
    /// Runtime generation.
    pub runtime_generation: u64,
}

impl TyCanaryGenerationTuple {
    /// Build a generation tuple.
    pub const fn new(
        arena_generation: u64,
        action_generation: u64,
        fingerprint_generation: u64,
        runtime_generation: u64,
    ) -> Self {
        Self {
            arena_generation,
            action_generation,
            fingerprint_generation,
            runtime_generation,
        }
    }
}

/// Exact TY allowlist key.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TyCanaryAllowlistKey {
    /// Spec digest.
    pub spec_sha256: String,
    /// Action or fingerprint-family digest.
    pub action_sha256: String,
    /// TY family.
    pub family: TyCanaryFamily,
    /// Arena/action/fingerprint/runtime generation tuple.
    pub generations: TyCanaryGenerationTuple,
    /// Target architecture.
    pub target: Target,
    /// Target facts digest.
    pub target_facts_sha256: String,
    /// Proof-policy version or checksum.
    pub proof_policy: String,
    /// Layout checksum.
    pub layout_checksum: String,
    /// Manifest hash.
    pub manifest_sha256: String,
    /// Canonical allowlist key hash.
    pub key_sha256: String,
}

impl TyCanaryAllowlistKey {
    /// Build an exact TY canary key.
    pub fn new(
        spec_sha256: impl Into<String>,
        action_sha256: impl Into<String>,
        family: TyCanaryFamily,
        generations: TyCanaryGenerationTuple,
        target: Target,
        target_facts_sha256: impl Into<String>,
        proof_policy: impl Into<String>,
        layout_checksum: impl Into<String>,
        manifest_sha256: impl Into<String>,
    ) -> Self {
        let mut key = Self {
            spec_sha256: spec_sha256.into(),
            action_sha256: action_sha256.into(),
            family,
            generations,
            target,
            target_facts_sha256: target_facts_sha256.into(),
            proof_policy: proof_policy.into(),
            layout_checksum: layout_checksum.into(),
            manifest_sha256: manifest_sha256.into(),
            key_sha256: String::new(),
        };
        key.key_sha256 = key.canonical_key_sha256();
        key
    }

    /// Return the stable hash of this key.
    pub fn canonical_key_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(&mut out, "trust-cg.jit_everywhere.ty_canary.key.v1");
        put_str(&mut out, &self.spec_sha256);
        put_str(&mut out, &self.action_sha256);
        put_str(&mut out, self.family.as_str());
        put_generations(&mut out, self.generations);
        put_str(&mut out, self.target.name());
        put_str(&mut out, &self.target_facts_sha256);
        put_str(&mut out, &self.proof_policy);
        put_str(&mut out, &self.layout_checksum);
        put_str(&mut out, &self.manifest_sha256);
        format!("sha256:{}", sha256_hex(&out))
    }

    fn has_required_identity(&self) -> bool {
        !missing_required_text(&self.spec_sha256)
            && !missing_required_text(&self.action_sha256)
            && !missing_required_text(&self.target_facts_sha256)
            && !missing_required_text(&self.proof_policy)
            && !missing_required_text(&self.layout_checksum)
            && !missing_required_text(&self.manifest_sha256)
            && self.generations.arena_generation > 0
            && self.generations.action_generation > 0
            && self.generations.fingerprint_generation > 0
            && self.generations.runtime_generation > 0
            && self.key_sha256 == self.canonical_key_sha256()
    }
}

/// Manifest fields that must bind an allowlisted TY tuple.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TyCanaryManifestBinding {
    /// Source digest.
    pub source_sha256: String,
    /// Canonical trust_ir digest.
    pub trust_ir_sha256: String,
    /// Native payload digest.
    pub native_payload_sha256: String,
    /// ABI checksum.
    pub abi_checksum: String,
    /// Layout checksum.
    pub layout_checksum: String,
    /// Compiler configuration checksum.
    pub compiler_config_sha256: String,
    /// Target facts digest.
    pub target_facts_sha256: String,
    /// Proof-policy version or checksum.
    pub proof_policy: String,
    /// Consumer kind.
    pub consumer_kind: String,
    /// Wrapper identity.
    pub wrapper_id: String,
    /// Exported symbols.
    pub symbols: Vec<String>,
    /// Replay root digest.
    pub replay_root_sha256: String,
    /// Telemetry key.
    pub telemetry_key: String,
    /// Manifest hash.
    pub manifest_sha256: String,
}

impl TyCanaryManifestBinding {
    /// Return true when this manifest binds the exact allowlist key.
    pub fn matches_key(&self, key: &TyCanaryAllowlistKey) -> bool {
        !missing_required_text(&self.source_sha256)
            && !missing_required_text(&self.trust_ir_sha256)
            && !missing_required_text(&self.native_payload_sha256)
            && !missing_required_text(&self.abi_checksum)
            && !missing_required_text(&self.compiler_config_sha256)
            && self.layout_checksum == key.layout_checksum
            && self.target_facts_sha256 == key.target_facts_sha256
            && self.proof_policy == key.proof_policy
            && self.consumer_kind == "ty"
            && !missing_required_text(&self.wrapper_id)
            && !self.symbols.is_empty()
            && self
                .symbols
                .iter()
                .all(|symbol| !missing_required_text(symbol))
            && !missing_required_text(&self.replay_root_sha256)
            && !missing_required_text(&self.telemetry_key)
            && self.manifest_sha256 == key.manifest_sha256
    }
}

/// Layout proof coverage for TY canary activation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TyCanaryLayoutProof {
    /// Flat-state buffers are covered.
    pub flat_state_buffers: bool,
    /// Parent buffers are covered.
    pub parent_buffers: bool,
    /// Fingerprint buffers are covered.
    pub fingerprint_buffers: bool,
    /// Callback/runtime symbols are covered.
    pub callback_runtime_symbols: bool,
    /// Return/status buffers are covered.
    pub return_status_buffers: bool,
    /// Generation fences are covered.
    pub generation_fences: bool,
    /// Mutability and aliasing are covered.
    pub mutability_aliasing: bool,
    /// Wrapper identity covered by the proof.
    pub wrapper_id: String,
}

impl TyCanaryLayoutProof {
    /// Return true when layout proof covers all required domains.
    pub fn covers_manifest(&self, manifest: &TyCanaryManifestBinding) -> bool {
        self.flat_state_buffers
            && self.parent_buffers
            && self.fingerprint_buffers
            && self.callback_runtime_symbols
            && self.return_status_buffers
            && self.generation_fences
            && self.mutability_aliasing
            && self.wrapper_id == manifest.wrapper_id
    }
}

/// Proof-policy decision recorded in validation provenance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TyCanaryProofDecision {
    /// Proof/TV accepted this tuple.
    Accepted,
    /// Proof/TV rejected this tuple.
    Rejected,
    /// Required proof/TV evidence is missing.
    Missing,
    /// Proof/TV timed out.
    Timeout,
}

impl TyCanaryProofDecision {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::Rejected => "rejected",
            Self::Missing => "missing",
            Self::Timeout => "timeout",
        }
    }
}

/// Validation provenance for the exact TY tuple.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TyCanaryValidationProvenance {
    /// Proof report digest.
    pub proof_report_sha256: String,
    /// Translation-validation report digest.
    pub tv_report_sha256: String,
    /// Replay root digest.
    pub replay_root_sha256: String,
    /// Consumer-equivalence report digest.
    pub consumer_equivalence_sha256: String,
    /// Validator identity.
    pub validator_id: String,
    /// Proof-policy decision.
    pub proof_policy_decision: TyCanaryProofDecision,
}

impl TyCanaryValidationProvenance {
    /// Return provenance with a canonical binding for every required TY proof fact.
    pub fn with_required_trust_ir_proof_fact_bindings(
        mut self,
        manifest: &TyCanaryManifestBinding,
    ) -> Self {
        let core_validator_id = validator_core_id(&self.validator_id)
            .unwrap_or(self.validator_id.as_str())
            .trim()
            .to_owned();
        let records = TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA
            .iter()
            .map(|(metadata_key, fact)| {
                self.canonical_trust_ir_proof_fact_binding_record(
                    manifest,
                    &core_validator_id,
                    metadata_key,
                    fact,
                )
            })
            .collect::<Vec<_>>();
        self.validator_id = format!(
            "{}{}{}",
            core_validator_id,
            TY_CANARY_TRUST_IR_PROOF_FACT_BINDINGS_PREFIX,
            records.join(",")
        );
        self
    }

    fn is_accepted_for(&self, manifest: &TyCanaryManifestBinding) -> bool {
        self.proof_policy_decision == TyCanaryProofDecision::Accepted
            && !missing_required_text(&self.proof_report_sha256)
            && !missing_required_text(&self.tv_report_sha256)
            && self.replay_root_sha256 == manifest.replay_root_sha256
            && !missing_required_text(&self.consumer_equivalence_sha256)
            && !missing_required_text(&self.validator_id)
            && self.required_trust_ir_proof_facts_bound(manifest)
    }

    fn required_trust_ir_proof_facts_bound(&self, manifest: &TyCanaryManifestBinding) -> bool {
        let Some((core_validator_id, binding_records)) =
            validator_id_and_binding_records(&self.validator_id)
        else {
            return false;
        };
        if missing_required_text(core_validator_id) || binding_records.is_empty() {
            return false;
        }

        let mut seen = BTreeSet::new();
        let records = binding_records.split(',').collect::<Vec<_>>();
        if records.len() != TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA.len() {
            return false;
        }

        for record in records {
            let Some((metadata_key, fact, status, binding_sha256)) =
                parse_trust_ir_proof_fact_binding_record(record)
            else {
                return false;
            };
            if status != TY_NATIVE_FUSED_PROOF_FACT_VERIFIED {
                return false;
            }
            let Some((required_metadata_key, required_fact)) =
                required_trust_ir_proof_fact(metadata_key, fact)
            else {
                return false;
            };
            if !seen.insert(required_fact) {
                return false;
            }
            if binding_sha256
                != self.canonical_trust_ir_proof_fact_binding_sha256(
                    manifest,
                    core_validator_id,
                    required_metadata_key,
                    required_fact,
                )
            {
                return false;
            }
        }

        seen.len() == TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA.len()
    }

    fn canonical_trust_ir_proof_fact_binding_record(
        &self,
        manifest: &TyCanaryManifestBinding,
        core_validator_id: &str,
        metadata_key: &str,
        fact: &str,
    ) -> String {
        format!(
            "{}={}={}={}",
            metadata_key,
            fact,
            TY_NATIVE_FUSED_PROOF_FACT_VERIFIED,
            self.canonical_trust_ir_proof_fact_binding_sha256(
                manifest,
                core_validator_id,
                metadata_key,
                fact
            )
        )
    }

    fn canonical_trust_ir_proof_fact_binding_sha256(
        &self,
        manifest: &TyCanaryManifestBinding,
        core_validator_id: &str,
        metadata_key: &str,
        fact: &str,
    ) -> String {
        let mut out = Vec::new();
        put_str(
            &mut out,
            "trust-cg.jit_everywhere.ty_canary.trust_ir_proof_fact_binding.v1",
        );
        put_str(&mut out, core_validator_id);
        put_str(&mut out, metadata_key);
        put_str(&mut out, fact);
        put_str(&mut out, TY_NATIVE_FUSED_PROOF_FACT_VERIFIED);
        put_str(&mut out, &manifest.source_sha256);
        put_str(&mut out, &manifest.trust_ir_sha256);
        put_str(&mut out, &manifest.native_payload_sha256);
        put_str(&mut out, &manifest.abi_checksum);
        put_str(&mut out, &manifest.layout_checksum);
        put_str(&mut out, &manifest.compiler_config_sha256);
        put_str(&mut out, &manifest.target_facts_sha256);
        put_str(&mut out, &manifest.proof_policy);
        put_str(&mut out, &manifest.consumer_kind);
        put_str(&mut out, &manifest.wrapper_id);
        put_str(&mut out, &manifest.replay_root_sha256);
        put_str(&mut out, &manifest.manifest_sha256);
        put_str(&mut out, &self.proof_report_sha256);
        put_str(&mut out, &self.tv_report_sha256);
        put_str(&mut out, &self.replay_root_sha256);
        put_str(&mut out, &self.consumer_equivalence_sha256);
        format!("sha256:{}", sha256_hex(&out))
    }
}

/// One TY native or baseline observation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TyCanaryExecutionObservation {
    /// Generated-state count.
    pub generated_state_count: u64,
    /// Distinct-state count.
    pub distinct_state_count: u64,
    /// Parent index digest.
    pub parent_indexes_sha256: String,
    /// Fingerprint digest.
    pub fingerprints_sha256: String,
    /// Final verdict string.
    pub final_verdict: String,
    /// Status-code digest.
    pub status_codes_sha256: String,
    /// Callback-visible behavior digest.
    pub callback_visible_sha256: String,
    /// Replay verdict digest.
    pub replay_verdict_sha256: String,
}

impl TyCanaryExecutionObservation {
    fn has_required_identity(&self) -> bool {
        self.generated_state_count > 0
            && self.distinct_state_count > 0
            && !missing_required_text(&self.parent_indexes_sha256)
            && !missing_required_text(&self.fingerprints_sha256)
            && !missing_required_text(&self.final_verdict)
            && !missing_required_text(&self.status_codes_sha256)
            && !missing_required_text(&self.callback_visible_sha256)
            && !missing_required_text(&self.replay_verdict_sha256)
    }
}

/// Baseline/native equivalence evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TyCanaryEquivalenceEvidence {
    /// Baseline observation.
    pub baseline: TyCanaryExecutionObservation,
    /// Native observation.
    pub native: TyCanaryExecutionObservation,
}

impl TyCanaryEquivalenceEvidence {
    fn matches(&self) -> bool {
        self.baseline.has_required_identity()
            && self.native.has_required_identity()
            && self.baseline == self.native
    }
}

/// Live invalidation state checked before install and call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TyCanaryInvalidationState {
    /// Current generation tuple.
    pub current_generations: TyCanaryGenerationTuple,
    /// Current target facts digest.
    pub target_facts_sha256: String,
    /// Current proof-policy id.
    pub proof_policy: String,
    /// Current compiler config digest.
    pub compiler_config_sha256: String,
    /// Current manifest digest.
    pub manifest_sha256: String,
    /// Current source digest.
    pub source_sha256: String,
    /// Current trust_ir digest.
    pub trust_ir_sha256: String,
    /// Current native payload digest.
    pub native_payload_sha256: String,
    /// Whether a kill switch is active.
    pub kill_switch_active: bool,
    /// Whether this artifact is revoked.
    pub revoked: bool,
}

impl TyCanaryInvalidationState {
    fn matches(
        &self,
        key: &TyCanaryAllowlistKey,
        manifest: &TyCanaryManifestBinding,
    ) -> Result<(), TyCanaryRejectionReason> {
        if self.kill_switch_active {
            return Err(TyCanaryRejectionReason::KillSwitchActive);
        }
        if self.revoked {
            return Err(TyCanaryRejectionReason::Revoked);
        }
        if self.current_generations != key.generations {
            return Err(TyCanaryRejectionReason::StaleGeneration);
        }
        if self.target_facts_sha256 != key.target_facts_sha256
            || self.proof_policy != key.proof_policy
            || self.manifest_sha256 != key.manifest_sha256
            || self.source_sha256 != manifest.source_sha256
            || self.trust_ir_sha256 != manifest.trust_ir_sha256
            || self.native_payload_sha256 != manifest.native_payload_sha256
            || self.compiler_config_sha256 != manifest.compiler_config_sha256
        {
            return Err(TyCanaryRejectionReason::StaleGeneration);
        }
        Ok(())
    }
}

/// Parent product gate evidence required before real canary activation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct TyCanaryParentGateEvidence {
    /// Shared install gate accepted this tuple.
    pub install_gate_accepted: bool,
    /// TY consumer gate accepted this tuple.
    pub consumer_gate_accepted: bool,
    /// Three-spec Rust CLI evidence accepted this tuple.
    pub three_spec_cli_accepted: bool,
}

impl TyCanaryParentGateEvidence {
    /// Return true only when all parent-gated product evidence exists.
    pub const fn accepted(self) -> bool {
        self.install_gate_accepted && self.consumer_gate_accepted && self.three_spec_cli_accepted
    }
}

/// Candidate evidence for one TY canary allowlist decision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TyCanaryCandidate {
    /// Candidate mode.
    pub mode: TyCanaryCandidateMode,
    /// Exact allowlist key.
    pub key: TyCanaryAllowlistKey,
    /// Manifest binding.
    pub manifest: Option<TyCanaryManifestBinding>,
    /// Layout proof.
    pub layout: Option<TyCanaryLayoutProof>,
    /// Validation provenance.
    pub provenance: Option<TyCanaryValidationProvenance>,
    /// Baseline/native equivalence.
    pub equivalence: Option<TyCanaryEquivalenceEvidence>,
    /// Invalidation state.
    pub invalidation: Option<TyCanaryInvalidationState>,
}

/// Allowlist decision status.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TyCanaryDecisionStatus {
    /// Candidate is rejected.
    Rejected,
    /// Candidate matches the exact allowlist and evidence, but product activation is separate.
    AllowlistedRequiresProductGate,
}

impl TyCanaryDecisionStatus {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Rejected => "rejected",
            Self::AllowlistedRequiresProductGate => "allowlisted_requires_product_gate",
        }
    }
}

/// Stable rejection or pending-product-gate reason.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TyCanaryRejectionReason {
    /// Tuple is not exactly allowlisted.
    NonAllowlisted,
    /// Profile-only is non-callable.
    ProfileOnlyNonCallable,
    /// Replay-only is non-callable.
    ReplayOnlyNonCallable,
    /// Shadow-only is non-callable.
    ShadowOnlyNonCallable,
    /// Manifest evidence is missing or mismatched.
    MissingManifest,
    /// Layout proof is missing or mismatched.
    LayoutMismatch,
    /// Proof/TV/validation did not accept the tuple.
    FailedProof,
    /// Invalidation state is stale.
    StaleGeneration,
    /// Telemetry key is missing.
    MissingTelemetry,
    /// Artifact is revoked.
    Revoked,
    /// Kill switch is active.
    KillSwitchActive,
    /// Native/baseline equivalence is missing or mismatched.
    MissingEquivalence,
    /// Parent product gate evidence is still required.
    MissingProductGateEvidence,
    /// Product activation remains outside this local prework issue.
    ProductActivationRequired,
}

impl TyCanaryRejectionReason {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::NonAllowlisted => "non_allowlisted",
            Self::ProfileOnlyNonCallable => "profile_only_non_callable",
            Self::ReplayOnlyNonCallable => "replay_only_non_callable",
            Self::ShadowOnlyNonCallable => "shadow_only_non_callable",
            Self::MissingManifest => "missing_manifest",
            Self::LayoutMismatch => "layout_mismatch",
            Self::FailedProof => "failed_proof",
            Self::StaleGeneration => "stale_generation",
            Self::MissingTelemetry => "missing_telemetry",
            Self::Revoked => "revoked",
            Self::KillSwitchActive => "kill_switch_active",
            Self::MissingEquivalence => "missing_equivalence",
            Self::MissingProductGateEvidence => "missing_product_gate_evidence",
            Self::ProductActivationRequired => "product_activation_required",
        }
    }
}

/// Side effects blocked by this pre-activation allowlist.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct TyCanarySideEffects {
    /// Whether a callable handle was published.
    pub callable_handle_published: bool,
    /// Whether an installable-cache hit was accepted.
    pub installable_cache_hit_accepted: bool,
    /// Whether TY native activation occurred.
    pub ty_native_activated: bool,
    /// Whether baseline execution was replaced.
    pub baseline_replaced: bool,
    /// Useful-native counter delta.
    pub useful_native_delta: u64,
}

impl TyCanarySideEffects {
    /// Return true when every install-authorizing side effect is blocked.
    pub const fn all_blocked(self) -> bool {
        !self.callable_handle_published
            && !self.installable_cache_hit_accepted
            && !self.ty_native_activated
            && !self.baseline_replaced
            && self.useful_native_delta == 0
    }
}

/// Telemetry emitted by a TY canary allowlist decision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TyCanaryTelemetryPacket {
    /// Schema.
    pub schema: &'static str,
    /// Schema version.
    pub schema_version: u32,
    /// Implementing issue.
    pub issue: u64,
    /// Allowlist key hash.
    pub key_sha256: String,
    /// Decision status.
    pub status: TyCanaryDecisionStatus,
    /// Decision reason.
    pub reason: TyCanaryRejectionReason,
    /// Replay root when present.
    pub replay_root_sha256: Option<String>,
    /// Telemetry key when present.
    pub telemetry_key: Option<String>,
    /// Side-effect summary.
    pub side_effects: TyCanarySideEffects,
    /// Canonical telemetry hash.
    pub record_sha256: String,
}

impl TyCanaryTelemetryPacket {
    /// Return the stable hash of this telemetry packet.
    pub fn canonical_record_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_u64(&mut out, self.issue);
        put_str(&mut out, &self.key_sha256);
        put_str(&mut out, self.status.as_str());
        put_str(&mut out, self.reason.as_str());
        put_option_str(&mut out, self.replay_root_sha256.as_deref());
        put_option_str(&mut out, self.telemetry_key.as_deref());
        put_side_effects(&mut out, self.side_effects);
        format!("sha256:{}", sha256_hex(&out))
    }
}

/// TY canary allowlist decision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TyCanaryAllowlistDecision {
    /// Decision status.
    pub status: TyCanaryDecisionStatus,
    /// Decision reason.
    pub reason: TyCanaryRejectionReason,
    /// Baseline remains authoritative.
    pub baseline_authoritative: bool,
    /// Native is not product-authoritative in this local slice.
    pub native_authoritative: bool,
    /// Side effects.
    pub side_effects: TyCanarySideEffects,
    /// Telemetry packet.
    pub telemetry: TyCanaryTelemetryPacket,
}

impl TyCanaryAllowlistDecision {
    /// Return true when no callable/native authority was granted.
    pub fn is_pre_activation_only(&self) -> bool {
        self.baseline_authoritative
            && !self.native_authoritative
            && self.side_effects.all_blocked()
            && self.telemetry.side_effects.all_blocked()
            && self.telemetry.record_sha256 == self.telemetry.canonical_record_sha256()
    }
}

/// Combined TY canary precheck over allowlist, control-plane, and consumer admission.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TyCanaryActivationPrecheckDecision {
    /// Exact-family allowlist decision.
    pub allowlist: TyCanaryAllowlistDecision,
    /// Existing install-gate/control-plane consumer-admission decision.
    pub consumer_admission: NativeInstallGateConsumerAdmissionDecision,
    /// Side effects authorized by this local canary precheck.
    pub side_effects: TyCanarySideEffects,
    /// Whether this local precheck published a TY native handle.
    pub publish_ty_native_handle: bool,
    /// Useful-native counter delta from this local precheck.
    pub useful_native_delta: u64,
}

impl TyCanaryActivationPrecheckDecision {
    /// Return true when this precheck remains fixture-only and pre-activation.
    pub fn is_pre_activation_only(&self) -> bool {
        self.allowlist.is_pre_activation_only()
            && self.side_effects.all_blocked()
            && !(self.allowlist.native_authoritative
                && self.consumer_admission.actions.ty_native_activate)
            && !self.publish_ty_native_handle
            && self.useful_native_delta == 0
            && self.consumer_admission.telemetry.useful_native_delta == 0
    }
}

/// Combined TY canary precheck over allowlist and product-adapter admission.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TyCanaryProductAdapterPrecheckDecision {
    /// Exact-family allowlist decision.
    pub allowlist: TyCanaryAllowlistDecision,
    /// Existing control-plane/product-adapter consumer admission decision.
    pub product_admission: ControlPlaneConsumerAdmissionProductDecision,
    /// Side effects authorized by this local canary precheck.
    pub side_effects: TyCanarySideEffects,
    /// Whether this local precheck published a TY native handle.
    pub publish_ty_native_handle: bool,
    /// Useful-native counter delta from this local precheck.
    pub useful_native_delta: u64,
}

impl TyCanaryProductAdapterPrecheckDecision {
    /// Return true when this precheck remains fixture-only and pre-activation.
    pub fn is_pre_activation_only(&self) -> bool {
        self.allowlist.is_pre_activation_only()
            && self
                .product_admission
                .publication_blocked_without_product_authority()
            && self.side_effects.all_blocked()
            && !self.product_admission.publish_ay_registry_entry
            && !self.product_admission.activate_ty_native_handle
            && !self.product_admission.expose_callable_handle
            && !self.publish_ty_native_handle
            && self.useful_native_delta == 0
            && self.product_admission.product_adapter.useful_native_delta == 0
    }
}

/// Exact TY canary allowlist.
#[derive(Debug, Clone, Default)]
pub struct TyCanaryAllowlist {
    exact_keys: BTreeSet<String>,
}

impl TyCanaryAllowlist {
    /// Build an empty allowlist.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add one exact key. Wildcards/default-on entries are not representable.
    pub fn add_exact(&mut self, key: &TyCanaryAllowlistKey) {
        self.exact_keys.insert(key.key_sha256.clone());
    }

    /// Return true when this exact key is allowlisted.
    pub fn contains_exact(&self, key: &TyCanaryAllowlistKey) -> bool {
        self.exact_keys.contains(&key.key_sha256)
    }

    /// Evaluate one TY canary candidate.
    pub fn evaluate(
        &self,
        candidate: &TyCanaryCandidate,
        parent_gates: TyCanaryParentGateEvidence,
    ) -> TyCanaryAllowlistDecision {
        let reason = self.rejection_reason(candidate, parent_gates);
        let status = if reason == TyCanaryRejectionReason::ProductActivationRequired {
            TyCanaryDecisionStatus::AllowlistedRequiresProductGate
        } else {
            TyCanaryDecisionStatus::Rejected
        };
        self.decision(candidate, status, reason)
    }

    fn rejection_reason(
        &self,
        candidate: &TyCanaryCandidate,
        parent_gates: TyCanaryParentGateEvidence,
    ) -> TyCanaryRejectionReason {
        if !candidate.key.has_required_identity() || !self.contains_exact(&candidate.key) {
            return TyCanaryRejectionReason::NonAllowlisted;
        }
        match candidate.mode {
            TyCanaryCandidateMode::ProfileOnly => {
                return TyCanaryRejectionReason::ProfileOnlyNonCallable;
            }
            TyCanaryCandidateMode::ReplayOnly => {
                return TyCanaryRejectionReason::ReplayOnlyNonCallable;
            }
            TyCanaryCandidateMode::ShadowOnly => {
                return TyCanaryRejectionReason::ShadowOnlyNonCallable;
            }
            TyCanaryCandidateMode::CanaryInstallable => {}
        }

        let Some(manifest) = &candidate.manifest else {
            return TyCanaryRejectionReason::MissingManifest;
        };
        if !manifest.matches_key(&candidate.key) {
            if missing_required_text(&manifest.telemetry_key) {
                return TyCanaryRejectionReason::MissingTelemetry;
            }
            return TyCanaryRejectionReason::MissingManifest;
        }
        if missing_required_text(&manifest.telemetry_key) {
            return TyCanaryRejectionReason::MissingTelemetry;
        }

        let Some(layout) = &candidate.layout else {
            return TyCanaryRejectionReason::LayoutMismatch;
        };
        if !layout.covers_manifest(manifest) {
            return TyCanaryRejectionReason::LayoutMismatch;
        }

        let Some(provenance) = &candidate.provenance else {
            return TyCanaryRejectionReason::FailedProof;
        };
        if !provenance.is_accepted_for(manifest) {
            return TyCanaryRejectionReason::FailedProof;
        }

        let Some(invalidation) = &candidate.invalidation else {
            return TyCanaryRejectionReason::StaleGeneration;
        };
        if let Err(reason) = invalidation.matches(&candidate.key, manifest) {
            return reason;
        }

        let Some(equivalence) = &candidate.equivalence else {
            return TyCanaryRejectionReason::MissingEquivalence;
        };
        if !equivalence.matches() {
            return TyCanaryRejectionReason::MissingEquivalence;
        }

        if !parent_gates.accepted() {
            return TyCanaryRejectionReason::MissingProductGateEvidence;
        }

        TyCanaryRejectionReason::ProductActivationRequired
    }

    fn decision(
        &self,
        candidate: &TyCanaryCandidate,
        status: TyCanaryDecisionStatus,
        reason: TyCanaryRejectionReason,
    ) -> TyCanaryAllowlistDecision {
        let side_effects = TyCanarySideEffects::default();
        let manifest = candidate.manifest.as_ref();
        let mut telemetry = TyCanaryTelemetryPacket {
            schema: JIT_TY_CANARY_ALLOWLIST_SCHEMA,
            schema_version: JIT_TY_CANARY_ALLOWLIST_SCHEMA_VERSION,
            issue: 741,
            key_sha256: candidate.key.key_sha256.clone(),
            status,
            reason,
            replay_root_sha256: manifest.map(|manifest| manifest.replay_root_sha256.clone()),
            telemetry_key: manifest.map(|manifest| manifest.telemetry_key.clone()),
            side_effects,
            record_sha256: String::new(),
        };
        telemetry.record_sha256 = telemetry.canonical_record_sha256();
        TyCanaryAllowlistDecision {
            status,
            reason,
            baseline_authoritative: true,
            native_authoritative: false,
            side_effects,
            telemetry,
        }
    }
}

/// Evaluate one TY canary tuple through the shared install-gate admission path.
///
/// This is deliberately a pre-activation composition: it consumes the exact
/// TY allowlist, parent-gate evidence, the live control-plane decision, and
/// the existing ay/TY consumer-admission gate, but it never publishes a
/// callable handle or increments useful-native counters.
pub fn evaluate_ty_canary_activation_precheck(
    allowlist: &TyCanaryAllowlist,
    candidate: &TyCanaryCandidate,
    parent_gates: TyCanaryParentGateEvidence,
    packet: &NativeInstallGatePacket,
    expected_packet_hash: Option<ArtifactChecksum>,
    control_decision: &ControlPlaneDecision,
    consumer_evidence: &NativeInstallGateConsumerAdmissionEvidence,
) -> TyCanaryActivationPrecheckDecision {
    let allowlist = allowlist.evaluate(candidate, parent_gates);
    let consumer_admission = consumer_admission_with_control_plane(
        packet,
        expected_packet_hash,
        control_decision,
        consumer_evidence,
    );
    let side_effects = TyCanarySideEffects::default();
    TyCanaryActivationPrecheckDecision {
        allowlist,
        consumer_admission,
        side_effects,
        publish_ty_native_handle: false,
        useful_native_delta: 0,
    }
}

/// Evaluate one TY canary tuple through the product-adapter admission bridge.
///
/// This composes the exact TY allowlist, parent-gate evidence, caller-current
/// install-gate revalidation state, and the #749/#750 product adapter bridge.
/// It remains pre-activation-only: no callable handles are published, no TY
/// native handles are activated, and useful-native counters stay at zero.
pub fn evaluate_ty_canary_product_adapter_precheck(
    allowlist: &TyCanaryAllowlist,
    candidate: &TyCanaryCandidate,
    parent_gates: TyCanaryParentGateEvidence,
    control_plane: &mut JitEverywhereControlPlane,
    control_candidate: &ControlPlaneCandidate,
    gate_evidence: ControlPlaneGateEvidence,
    packet: &NativeInstallGatePacket,
    expected_packet_hash: Option<ArtifactChecksum>,
    current: &NativeInstallGateRevalidationInput,
    consumer_evidence: &NativeInstallGateConsumerAdmissionEvidence,
) -> TyCanaryProductAdapterPrecheckDecision {
    let allowlist = allowlist.evaluate(candidate, parent_gates);
    let product_admission = control_plane.route_consumer_admission_product_adapter_with_current(
        control_candidate,
        gate_evidence,
        packet,
        expected_packet_hash,
        current,
        consumer_evidence,
    );
    let side_effects = TyCanarySideEffects::default();
    TyCanaryProductAdapterPrecheckDecision {
        allowlist,
        product_admission,
        side_effects,
        publish_ty_native_handle: false,
        useful_native_delta: 0,
    }
}

fn put_generations(out: &mut Vec<u8>, generations: TyCanaryGenerationTuple) {
    put_u64(out, generations.arena_generation);
    put_u64(out, generations.action_generation);
    put_u64(out, generations.fingerprint_generation);
    put_u64(out, generations.runtime_generation);
}

fn put_side_effects(out: &mut Vec<u8>, side_effects: TyCanarySideEffects) {
    put_bool(out, side_effects.callable_handle_published);
    put_bool(out, side_effects.installable_cache_hit_accepted);
    put_bool(out, side_effects.ty_native_activated);
    put_bool(out, side_effects.baseline_replaced);
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

fn put_bool(out: &mut Vec<u8>, value: bool) {
    out.push(u8::from(value));
}

fn validator_core_id(validator_id: &str) -> Option<&str> {
    validator_id
        .split_once(TY_CANARY_TRUST_IR_PROOF_FACT_BINDINGS_PREFIX)
        .map(|(core, _)| core)
        .or(Some(validator_id))
}

fn validator_id_and_binding_records(validator_id: &str) -> Option<(&str, &str)> {
    let (core, records) = validator_id.split_once(TY_CANARY_TRUST_IR_PROOF_FACT_BINDINGS_PREFIX)?;
    if records.contains(TY_CANARY_TRUST_IR_PROOF_FACT_BINDINGS_PREFIX) {
        return None;
    }
    Some((core, records))
}

fn parse_trust_ir_proof_fact_binding_record(record: &str) -> Option<(&str, &str, &str, &str)> {
    let mut parts = record.split('=');
    let metadata_key = parts.next()?;
    let fact = parts.next()?;
    let status = parts.next()?;
    let binding_sha256 = parts.next()?;
    if parts.next().is_some()
        || missing_required_text(metadata_key)
        || missing_required_text(fact)
        || missing_required_text(status)
        || missing_required_text(binding_sha256)
    {
        return None;
    }
    Some((metadata_key, fact, status, binding_sha256))
}

fn required_trust_ir_proof_fact(
    metadata_key: &str,
    fact: &str,
) -> Option<(&'static str, &'static str)> {
    TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA
        .iter()
        .copied()
        .find(|(required_metadata_key, required_fact)| {
            metadata_key == *required_metadata_key && fact == *required_fact
        })
}

fn missing_required_text(value: &str) -> bool {
    value.trim().is_empty()
}
