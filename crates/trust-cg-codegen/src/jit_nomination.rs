// trust-cg-codegen/jit_nomination.rs - JIT-everywhere candidate nomination telemetry
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Data-only candidate nomination telemetry for JIT-everywhere prework.
//!
//! Nomination records are advisory observations. They are deliberately unable
//! to enqueue compilation, create executable artifacts, publish callable
//! handles, mutate product registries, or count useful-native execution.

use crate::jit_diagnostics::sha256_hex;
use crate::target::Target;

/// Stable schema tag for JIT-everywhere nomination records.
pub const JIT_EVERYWHERE_NOMINATION_SCHEMA: &str = "trust-cg.jit_everywhere.nomination.v1";

/// Stable numeric schema version for nomination records.
pub const JIT_EVERYWHERE_NOMINATION_SCHEMA_VERSION: u32 = 1;

/// Stable identity for one advisory candidate nomination.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CandidateId {
    /// Stable id string derived only from deterministic candidate fields.
    pub value: String,
}

impl CandidateId {
    /// Build a candidate id from a canonical SHA-256 body.
    pub fn from_hash(hash: impl Into<String>) -> Self {
        Self {
            value: format!("candidate:{}", hash.into()),
        }
    }
}

/// Region shape observed by nomination telemetry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CandidateRegionKind {
    /// Generic trust_ir function region.
    TrustIrFunction,
    /// Generic trust_ir basic-block or block cluster region.
    TrustIrBlockCluster,
    /// ay solver-program kernel family.
    AYSolverProgram,
    /// ay sparse-substitute kernel family.
    AYSparseSubstitute,
    /// ay basis-region kernel family.
    AYBasisRegion,
    /// ay watch-list/BCP kernel family.
    AYWatchListBcp,
    /// TY action cluster.
    TyActionCluster,
    /// TY invariant cluster.
    TyInvariantCluster,
    /// TY fingerprint cluster.
    TyFingerprintCluster,
    /// TY fused parent-loop cluster.
    TyFusedParentLoop,
    /// Shape observed but not supported by this nomination schema.
    UnsupportedShape,
}

impl CandidateRegionKind {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::TrustIrFunction => "trust_ir_function",
            Self::TrustIrBlockCluster => "trust_ir_block_cluster",
            Self::AYSolverProgram => "ay_solver_program",
            Self::AYSparseSubstitute => "ay_sparse_substitute",
            Self::AYBasisRegion => "ay_basis_region",
            Self::AYWatchListBcp => "ay_watch_list_bcp",
            Self::TyActionCluster => "ty_action_cluster",
            Self::TyInvariantCluster => "ty_invariant_cluster",
            Self::TyFingerprintCluster => "ty_fingerprint_cluster",
            Self::TyFusedParentLoop => "ty_fused_parent_loop",
            Self::UnsupportedShape => "unsupported_shape",
        }
    }

    fn is_supported_for_consumer(self, consumer: &str) -> bool {
        match (consumer, self) {
            ("trust-cg", Self::TrustIrFunction | Self::TrustIrBlockCluster) => true,
            (
                "ay",
                Self::TrustIrFunction
                | Self::TrustIrBlockCluster
                | Self::AYSolverProgram
                | Self::AYSparseSubstitute
                | Self::AYBasisRegion
                | Self::AYWatchListBcp,
            ) => true,
            (
                "ty",
                Self::TrustIrFunction
                | Self::TrustIrBlockCluster
                | Self::TyActionCluster
                | Self::TyInvariantCluster
                | Self::TyFingerprintCluster
                | Self::TyFusedParentLoop,
            ) => true,
            _ => false,
        }
    }
}

/// Nomination record disposition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NominationDisposition {
    /// Candidate is advisory-only nominated.
    Nominated,
    /// Candidate is advisory-only rejected with a typed reason.
    Rejected,
}

impl NominationDisposition {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Nominated => "nominated",
            Self::Rejected => "rejected",
        }
    }
}

/// Typed advisory rejection reason.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NominationRejectionReason {
    /// Consumer is not part of the local nomination prework surface.
    UnsupportedConsumer,
    /// Region kind is not supported for the requested consumer.
    UnsupportedRegionKind,
    /// Source digest is absent.
    MissingSourceDigest,
    /// trust_ir digest is absent.
    MissingTrustIrDigest,
    /// Profile key digest is absent.
    MissingProfileKeyDigest,
    /// Proof-policy version is absent.
    MissingProofPolicyVersion,
    /// Generation domain is absent.
    MissingGenerationDomain,
    /// No counters or structural scan observations were present.
    MissingObservation,
}

impl NominationRejectionReason {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::UnsupportedConsumer => "unsupported_consumer",
            Self::UnsupportedRegionKind => "unsupported_region_kind",
            Self::MissingSourceDigest => "missing_source_digest",
            Self::MissingTrustIrDigest => "missing_trust_ir_digest",
            Self::MissingProfileKeyDigest => "missing_profile_key_digest",
            Self::MissingProofPolicyVersion => "missing_proof_policy_version",
            Self::MissingGenerationDomain => "missing_generation_domain",
            Self::MissingObservation => "missing_observation",
        }
    }
}

/// Deterministic structural signal used for advisory scoring.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NominationStructuralSignal {
    /// Existing profile counter observations for this candidate.
    pub observation_count: u64,
    /// Existing call counter observations.
    pub call_count: u64,
    /// Loop count from a structural scan.
    pub loop_count: u64,
    /// Basic block count from a structural scan.
    pub block_count: u64,
    /// Instruction count from a structural scan.
    pub instruction_count: u64,
    /// Consumer-owned memory or state regions seen by a structural scan.
    pub memory_region_count: u64,
}

impl NominationStructuralSignal {
    /// Build structural signal from existing counters and structural scans.
    pub const fn new(
        observation_count: u64,
        call_count: u64,
        loop_count: u64,
        block_count: u64,
        instruction_count: u64,
        memory_region_count: u64,
    ) -> Self {
        Self {
            observation_count,
            call_count,
            loop_count,
            block_count,
            instruction_count,
            memory_region_count,
        }
    }

    /// Return true when no profile or structural observation exists.
    pub const fn is_empty(&self) -> bool {
        self.observation_count == 0
            && self.call_count == 0
            && self.loop_count == 0
            && self.block_count == 0
            && self.instruction_count == 0
            && self.memory_region_count == 0
    }

    fn advisory_score(&self) -> u32 {
        let score = self
            .observation_count
            .saturating_add(self.call_count.saturating_mul(4))
            .saturating_add(self.loop_count.saturating_mul(8))
            .saturating_add(self.block_count.saturating_mul(2))
            .saturating_add(self.instruction_count / 16)
            .saturating_add(self.memory_region_count.saturating_mul(4));
        score.min(100) as u32
    }
}

/// Pure data-only nomination input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NominationInput {
    /// Downstream consumer or shared service name: `trust-cg`, `ay`, or `ty`.
    pub consumer: String,
    /// Candidate region kind.
    pub region_kind: CandidateRegionKind,
    /// Target observed by the current run.
    pub target: Target,
    /// Source or solver-program digest.
    pub source_sha256: String,
    /// Canonical trust_ir digest.
    pub trust_ir_sha256: String,
    /// Profile key digest.
    pub profile_key_sha256: String,
    /// Proof-policy version or checksum string visible to this advisory path.
    pub proof_policy_version: String,
    /// Runtime or consumer generation domain.
    pub generation_domain: String,
    /// Existing counters and structural scan signal.
    pub structural_signal: NominationStructuralSignal,
}

impl NominationInput {
    /// Build a nomination input from deterministic profile and structural fields.
    pub fn new(
        consumer: impl Into<String>,
        region_kind: CandidateRegionKind,
        target: Target,
        source_sha256: impl Into<String>,
        trust_ir_sha256: impl Into<String>,
        profile_key_sha256: impl Into<String>,
        proof_policy_version: impl Into<String>,
        generation_domain: impl Into<String>,
        structural_signal: NominationStructuralSignal,
    ) -> Self {
        Self {
            consumer: consumer.into(),
            region_kind,
            target,
            source_sha256: source_sha256.into(),
            trust_ir_sha256: trust_ir_sha256.into(),
            profile_key_sha256: profile_key_sha256.into(),
            proof_policy_version: proof_policy_version.into(),
            generation_domain: generation_domain.into(),
            structural_signal,
        }
    }
}

/// Effects that nomination telemetry is forbidden to perform.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct NominationSideEffects {
    /// Whether a compile request was enqueued.
    pub compile_enqueued: bool,
    /// Whether an executable artifact was created.
    pub executable_artifact_created: bool,
    /// Whether a callable handle was published.
    pub callable_handle_published: bool,
    /// Whether an installable cache entry was written.
    pub install_cache_written: bool,
    /// Whether a ay registry entry was inserted.
    pub ay_registry_inserted: bool,
    /// Whether TY native activation occurred.
    pub ty_native_activated: bool,
    /// Useful-native counter delta from nomination.
    pub useful_native_delta: u64,
}

impl NominationSideEffects {
    /// Return true when every install-authorizing side effect is blocked.
    pub const fn all_blocked(self) -> bool {
        !self.compile_enqueued
            && !self.executable_artifact_created
            && !self.callable_handle_published
            && !self.install_cache_written
            && !self.ay_registry_inserted
            && !self.ty_native_activated
            && self.useful_native_delta == 0
    }
}

/// Deterministic advisory nomination telemetry record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NominationRecord {
    /// Record schema.
    pub schema: &'static str,
    /// Record schema version.
    pub schema_version: u32,
    /// Implementing issue.
    pub issue: u64,
    /// Stable candidate id.
    pub candidate_id: CandidateId,
    /// Final advisory disposition.
    pub disposition: NominationDisposition,
    /// Typed rejection reason when rejected.
    pub rejection_reason: Option<NominationRejectionReason>,
    /// Consumer.
    pub consumer: String,
    /// Candidate region kind.
    pub region_kind: CandidateRegionKind,
    /// Target.
    pub target: Target,
    /// Source digest.
    pub source_sha256: String,
    /// trust_ir digest.
    pub trust_ir_sha256: String,
    /// Profile key digest.
    pub profile_key_sha256: String,
    /// Proof-policy version.
    pub proof_policy_version: String,
    /// Generation domain.
    pub generation_domain: String,
    /// Deterministic advisory score, 0-100.
    pub advisory_score: u32,
    /// Structural signal behind the advisory score.
    pub structural_signal: NominationStructuralSignal,
    /// Explicit no-side-effect summary.
    pub side_effects: NominationSideEffects,
    /// Canonical telemetry record SHA-256.
    pub record_sha256: String,
}

impl NominationRecord {
    /// Return the stable hash of this nomination record.
    pub fn canonical_record_sha256(&self) -> String {
        let mut out = Vec::new();
        put_record_body(self, &mut out, false);
        format!("sha256:{}", sha256_hex(&out))
    }

    /// Return true when this record cannot authorize native execution.
    pub const fn is_non_installing(&self) -> bool {
        self.side_effects.all_blocked()
    }
}

/// Build one deterministic advisory nomination record.
pub fn nominate_jit_everywhere_candidate(input: &NominationInput) -> NominationRecord {
    let rejection_reason = nomination_rejection_reason(input);
    let disposition = if rejection_reason.is_some() {
        NominationDisposition::Rejected
    } else {
        NominationDisposition::Nominated
    };
    let advisory_score = if disposition == NominationDisposition::Nominated {
        input.structural_signal.advisory_score()
    } else {
        0
    };
    let candidate_id = candidate_id_for_input(input);
    let mut record = NominationRecord {
        schema: JIT_EVERYWHERE_NOMINATION_SCHEMA,
        schema_version: JIT_EVERYWHERE_NOMINATION_SCHEMA_VERSION,
        issue: 736,
        candidate_id,
        disposition,
        rejection_reason,
        consumer: input.consumer.clone(),
        region_kind: input.region_kind,
        target: input.target,
        source_sha256: input.source_sha256.clone(),
        trust_ir_sha256: input.trust_ir_sha256.clone(),
        profile_key_sha256: input.profile_key_sha256.clone(),
        proof_policy_version: input.proof_policy_version.clone(),
        generation_domain: input.generation_domain.clone(),
        advisory_score,
        structural_signal: input.structural_signal.clone(),
        side_effects: NominationSideEffects::default(),
        record_sha256: String::new(),
    };
    record.record_sha256 = record.canonical_record_sha256();
    record
}

fn nomination_rejection_reason(input: &NominationInput) -> Option<NominationRejectionReason> {
    if missing_required_text(&input.source_sha256) {
        return Some(NominationRejectionReason::MissingSourceDigest);
    }
    if missing_required_text(&input.trust_ir_sha256) {
        return Some(NominationRejectionReason::MissingTrustIrDigest);
    }
    if missing_required_text(&input.profile_key_sha256) {
        return Some(NominationRejectionReason::MissingProfileKeyDigest);
    }
    if missing_required_text(&input.proof_policy_version) {
        return Some(NominationRejectionReason::MissingProofPolicyVersion);
    }
    if missing_required_text(&input.generation_domain) {
        return Some(NominationRejectionReason::MissingGenerationDomain);
    }
    if !matches!(input.consumer.as_str(), "trust-cg" | "ay" | "ty") {
        return Some(NominationRejectionReason::UnsupportedConsumer);
    }
    if !input.region_kind.is_supported_for_consumer(&input.consumer) {
        return Some(NominationRejectionReason::UnsupportedRegionKind);
    }
    if input.structural_signal.is_empty() {
        return Some(NominationRejectionReason::MissingObservation);
    }
    None
}

fn candidate_id_for_input(input: &NominationInput) -> CandidateId {
    let mut out = Vec::new();
    put_str(&mut out, "trust-cg.jit_everywhere.candidate_id.v1");
    put_str(&mut out, &input.consumer);
    put_str(&mut out, input.region_kind.as_str());
    put_str(&mut out, input.target.name());
    put_str(&mut out, &input.source_sha256);
    put_str(&mut out, &input.trust_ir_sha256);
    put_str(&mut out, &input.profile_key_sha256);
    put_str(&mut out, &input.proof_policy_version);
    put_str(&mut out, &input.generation_domain);
    CandidateId::from_hash(format!("sha256:{}", sha256_hex(&out)))
}

fn put_record_body(record: &NominationRecord, out: &mut Vec<u8>, include_record_hash: bool) {
    put_str(out, record.schema);
    put_u32(out, record.schema_version);
    put_u64(out, record.issue);
    put_str(out, &record.candidate_id.value);
    put_str(out, record.disposition.as_str());
    put_option_str(
        out,
        record
            .rejection_reason
            .map(NominationRejectionReason::as_str),
    );
    put_str(out, &record.consumer);
    put_str(out, record.region_kind.as_str());
    put_str(out, record.target.name());
    put_str(out, &record.source_sha256);
    put_str(out, &record.trust_ir_sha256);
    put_str(out, &record.profile_key_sha256);
    put_str(out, &record.proof_policy_version);
    put_str(out, &record.generation_domain);
    put_u32(out, record.advisory_score);
    put_signal(out, &record.structural_signal);
    put_bool(out, record.side_effects.compile_enqueued);
    put_bool(out, record.side_effects.executable_artifact_created);
    put_bool(out, record.side_effects.callable_handle_published);
    put_bool(out, record.side_effects.install_cache_written);
    put_bool(out, record.side_effects.ay_registry_inserted);
    put_bool(out, record.side_effects.ty_native_activated);
    put_u64(out, record.side_effects.useful_native_delta);
    if include_record_hash {
        put_str(out, &record.record_sha256);
    }
}

fn put_signal(out: &mut Vec<u8>, signal: &NominationStructuralSignal) {
    put_u64(out, signal.observation_count);
    put_u64(out, signal.call_count);
    put_u64(out, signal.loop_count);
    put_u64(out, signal.block_count);
    put_u64(out, signal.instruction_count);
    put_u64(out, signal.memory_region_count);
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

fn missing_required_text(value: &str) -> bool {
    value.trim().is_empty()
}
