// trust-cg-codegen/jit_ay_canary_allowlist.rs - ay canary allowlist prework
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Data-only ay canary allowlist readiness model.
//!
//! This module validates exact ay canary tuples and required evidence, but it
//! deliberately does not publish callable handles, insert ay registry entries,
//! accept install-cache hits, release installable bundles, replace baseline
//! execution, or increment useful-native counters.

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
};
use crate::target::Target;

/// Stable schema tag for ay canary allowlist decisions.
pub const JIT_AY_CANARY_ALLOWLIST_SCHEMA: &str = "trust-cg.jit_everywhere.ay_canary_allowlist.v1";

/// Stable numeric schema version for ay canary allowlist decisions.
pub const JIT_AY_CANARY_ALLOWLIST_SCHEMA_VERSION: u32 = 1;

const AY_CANARY_LRA_PROOF_FACT_SCHEMA: &str =
    "trust-cg.jit_everywhere.ay_canary.lra_proof_facts.v1";
const AY_LRA_PROOF_FACT_METADATA_PREFIX: &str = "ay_lra.proof_fact.";
const AY_CANARY_BCP_PROOF_FACT_SCHEMA: &str =
    "trust-cg.jit_everywhere.ay_canary.bcp_proof_facts.v1";
const AY_BCP_PROOF_FACT_METADATA_PREFIX: &str = "ay_bcp.proof_fact.";

/// ay canary family.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum AYCanaryFamily {
    /// One sparse-substitute/LRA solver family.
    SparseSubstitute,
    /// One basis-region scanner family.
    BasisRegionScanner,
    /// One watched-list BCP family.
    WatchListBcp,
}

impl AYCanaryFamily {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::SparseSubstitute => "sparse_substitute",
            Self::BasisRegionScanner => "basis_region_scanner",
            Self::WatchListBcp => "watch_list_bcp",
        }
    }
}

/// Typed ay LRA proof fact required by canary admission.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum AYCanaryLraProofFact {
    /// Sparse rows are sorted by column/index before substitute/update.
    SortedSparseRows,
    /// Entering-variable identity and column membership are bound.
    EnteringVariable,
    /// Target and pivot rows have a checked alias policy.
    TargetPivotAliasPolicy,
    /// Output buffers have sufficient capacity.
    OutputCapacityBounds,
    /// Coefficient arithmetic cannot overflow the admitted representation.
    CoefficientOverflow,
    /// Basis epoch is fresh for the native artifact.
    BasisEpochFreshness,
    /// Batch prefix commit/rollback facts are present.
    BatchPrefixCommitRollback,
    /// trust_ir identity and source policy are bound.
    SourceIdentityLocks,
    /// AArch64 ABI and LP64 layout are bound.
    Aarch64AbiLayout,
    /// Typed status signature is bound.
    StatusSignature,
    /// Proof-policy checksum is bound.
    ProofPolicyChecksum,
    /// Generic, specialized, and reference replay artifacts compare equal.
    ReplayComparison,
    /// SAT candidate-loop proof family placeholder.
    SatCandidateLoopProof,
    /// CHC candidate-loop proof family placeholder.
    ChcCandidateLoopProof,
    /// PB candidate-loop proof family placeholder.
    PbCandidateLoopProof,
}

impl AYCanaryLraProofFact {
    /// Return the stable lower-snake-case fact id.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::SortedSparseRows => "sorted_sparse_rows",
            Self::EnteringVariable => "entering_variable",
            Self::TargetPivotAliasPolicy => "target_pivot_alias_policy",
            Self::OutputCapacityBounds => "output_capacity_bounds",
            Self::CoefficientOverflow => "coefficient_overflow",
            Self::BasisEpochFreshness => "basis_epoch_freshness",
            Self::BatchPrefixCommitRollback => "batch_prefix_commit_rollback",
            Self::SourceIdentityLocks => "source_identity_locks",
            Self::Aarch64AbiLayout => "aarch64_abi_layout",
            Self::StatusSignature => "status_signature",
            Self::ProofPolicyChecksum => "proof_policy_checksum",
            Self::ReplayComparison => "replay_comparison",
            Self::SatCandidateLoopProof => "sat_candidate_loop_proof",
            Self::ChcCandidateLoopProof => "chc_candidate_loop_proof",
            Self::PbCandidateLoopProof => "pb_candidate_loop_proof",
        }
    }

    /// Return the stable proof-evidence metadata key for this fact.
    pub fn metadata_key(self) -> String {
        format!("{AY_LRA_PROOF_FACT_METADATA_PREFIX}{}", self.as_str())
    }
}

/// Typed ay watched-list BCP proof fact required by canary admission.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum AYCanaryBcpProofFact {
    /// Watch heads and entries implement the two-watched-literals layout.
    WatchLayout,
    /// Clause arena reads are bounded by the runtime arena length.
    ClauseArenaBounds,
    /// Assignment and trail generations are fresh for propagation.
    AssignmentTrailFreshness,
    /// Pending queue head/tail remain within capacity.
    PendingQueueBounds,
    /// Runtime, watch, assignment, and expected generations match.
    GenerationMatch,
    /// Result record ABI and status encoding are bound.
    ResultAbi,
    /// Generic, specialized, and reference replay artifacts compare equal.
    ReplayComparison,
}

impl AYCanaryBcpProofFact {
    /// Return the stable lower-snake-case fact id.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::WatchLayout => "watch_layout",
            Self::ClauseArenaBounds => "clause_arena_bounds",
            Self::AssignmentTrailFreshness => "assignment_trail_freshness",
            Self::PendingQueueBounds => "pending_queue_bounds",
            Self::GenerationMatch => "generation_match",
            Self::ResultAbi => "result_abi",
            Self::ReplayComparison => "replay_comparison",
        }
    }

    /// Return the stable proof-evidence metadata key for this fact.
    pub fn metadata_key(self) -> String {
        format!("{AY_BCP_PROOF_FACT_METADATA_PREFIX}{}", self.as_str())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct AYCanaryLraProofFactRequirement {
    fact: AYCanaryLraProofFact,
    lemma_id: &'static str,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct AYCanaryBcpProofFactRequirement {
    fact: AYCanaryBcpProofFact,
    lemma_id: &'static str,
}

const SPARSE_LRA_PROOF_FACT_REQUIREMENTS: [AYCanaryLraProofFactRequirement; 11] = [
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::SortedSparseRows,
        lemma_id: "ay_lra_sparse.sorted_rows_strict_order",
    },
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::EnteringVariable,
        lemma_id: "ay_lra_sparse.entering_variable_in_basis_frontier",
    },
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::TargetPivotAliasPolicy,
        lemma_id: "ay_lra_sparse.target_pivot_alias_exclusive_or_readonly",
    },
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::OutputCapacityBounds,
        lemma_id: "ay_lra_sparse.output_capacity_bounds",
    },
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::CoefficientOverflow,
        lemma_id: "ay_lra_sparse.coefficient_update_no_overflow",
    },
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::BasisEpochFreshness,
        lemma_id: "ay_lra_sparse.basis_epoch_fresh",
    },
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::SourceIdentityLocks,
        lemma_id: "trust_cg_ay_lra.source_identity_policy_bound",
    },
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::Aarch64AbiLayout,
        lemma_id: "trust_cg_ay_lra.aarch64_abi_layout_bound",
    },
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::StatusSignature,
        lemma_id: "trust_cg_ay_lra.status_signature_bound",
    },
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::ProofPolicyChecksum,
        lemma_id: "trust_cg_ay_lra.proof_policy_checksum_bound",
    },
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::ReplayComparison,
        lemma_id: "trust_cg_ay_lra.replay_generic_specialized_reference_equal",
    },
];

const BASIS_LRA_PROOF_FACT_REQUIREMENTS: [AYCanaryLraProofFactRequirement; 12] = [
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::SortedSparseRows,
        lemma_id: "ay_lra_basis.sorted_tableau_rows",
    },
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::EnteringVariable,
        lemma_id: "ay_lra_basis.entering_variable_matches_basis_update",
    },
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::TargetPivotAliasPolicy,
        lemma_id: "ay_lra_basis.target_pivot_alias_exclusive_or_readonly",
    },
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::OutputCapacityBounds,
        lemma_id: "ay_lra_basis.output_capacity_bounds",
    },
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::CoefficientOverflow,
        lemma_id: "ay_lra_basis.coefficient_update_no_overflow",
    },
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::BasisEpochFreshness,
        lemma_id: "ay_lra_basis.basis_epoch_fresh",
    },
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::BatchPrefixCommitRollback,
        lemma_id: "ay_lra_basis.batch_prefix_commit_rollback",
    },
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::SourceIdentityLocks,
        lemma_id: "trust_cg_ay_lra.source_identity_policy_bound",
    },
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::Aarch64AbiLayout,
        lemma_id: "trust_cg_ay_lra.aarch64_abi_layout_bound",
    },
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::StatusSignature,
        lemma_id: "trust_cg_ay_lra.status_signature_bound",
    },
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::ProofPolicyChecksum,
        lemma_id: "trust_cg_ay_lra.proof_policy_checksum_bound",
    },
    AYCanaryLraProofFactRequirement {
        fact: AYCanaryLraProofFact::ReplayComparison,
        lemma_id: "trust_cg_ay_lra.replay_generic_specialized_reference_equal",
    },
];

const WATCH_LIST_BCP_PROOF_FACT_REQUIREMENTS: [AYCanaryBcpProofFactRequirement; 7] = [
    AYCanaryBcpProofFactRequirement {
        fact: AYCanaryBcpProofFact::WatchLayout,
        lemma_id: "ay_sat_bcp.watch_layout_two_watched_literals",
    },
    AYCanaryBcpProofFactRequirement {
        fact: AYCanaryBcpProofFact::ClauseArenaBounds,
        lemma_id: "ay_sat_bcp.clause_arena_bounds",
    },
    AYCanaryBcpProofFactRequirement {
        fact: AYCanaryBcpProofFact::AssignmentTrailFreshness,
        lemma_id: "ay_sat_bcp.assignment_trail_freshness",
    },
    AYCanaryBcpProofFactRequirement {
        fact: AYCanaryBcpProofFact::PendingQueueBounds,
        lemma_id: "ay_sat_bcp.pending_queue_bounds",
    },
    AYCanaryBcpProofFactRequirement {
        fact: AYCanaryBcpProofFact::GenerationMatch,
        lemma_id: "ay_sat_bcp.generation_match",
    },
    AYCanaryBcpProofFactRequirement {
        fact: AYCanaryBcpProofFact::ResultAbi,
        lemma_id: "trust_cg_ay_bcp.result_abi_bound",
    },
    AYCanaryBcpProofFactRequirement {
        fact: AYCanaryBcpProofFact::ReplayComparison,
        lemma_id: "trust_cg_ay_bcp.replay_generic_specialized_reference_equal",
    },
];

/// One typed ay LRA proof-fact metadata binding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYCanaryLraProofFactBinding {
    /// Required proof fact.
    pub fact: AYCanaryLraProofFact,
    /// Metadata key that must bind the fact.
    pub metadata_key: String,
    /// Stable lemma or checker id expected from proof evidence.
    pub lemma_id: String,
}

impl AYCanaryLraProofFactBinding {
    /// Build a proof-fact metadata binding with the canonical metadata key.
    pub fn new(fact: AYCanaryLraProofFact, lemma_id: impl Into<String>) -> Self {
        Self {
            fact,
            metadata_key: fact.metadata_key(),
            lemma_id: lemma_id.into(),
        }
    }
}

/// One typed ay watched-list BCP proof-fact metadata binding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYCanaryBcpProofFactBinding {
    /// Required proof fact.
    pub fact: AYCanaryBcpProofFact,
    /// Metadata key that must bind the fact.
    pub metadata_key: String,
    /// Stable lemma or checker id expected from proof evidence.
    pub lemma_id: String,
}

impl AYCanaryBcpProofFactBinding {
    /// Build a proof-fact metadata binding with the canonical metadata key.
    pub fn new(fact: AYCanaryBcpProofFact, lemma_id: impl Into<String>) -> Self {
        Self {
            fact,
            metadata_key: fact.metadata_key(),
            lemma_id: lemma_id.into(),
        }
    }
}

/// Candidate mode at the canary boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AYCanaryCandidateMode {
    /// Profile-only candidates are not callable.
    ProfileOnly,
    /// Replay-only candidates are not callable.
    ReplayOnly,
    /// Shadow-only candidates are not callable.
    ShadowOnly,
    /// Candidate requests canary callable authority for this exact tuple.
    CanaryInstallable,
}

impl AYCanaryCandidateMode {
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

/// Runtime generation fence for a ay canary candidate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AYCanaryGenerationFence {
    /// Solver-program generation.
    pub solver_generation: u64,
    /// Basis-region generation.
    pub basis_generation: u64,
    /// Watch-list generation.
    pub watch_list_generation: u64,
    /// Runtime generation.
    pub runtime_generation: u64,
}

impl AYCanaryGenerationFence {
    /// Build a generation fence.
    pub const fn new(
        solver_generation: u64,
        basis_generation: u64,
        watch_list_generation: u64,
        runtime_generation: u64,
    ) -> Self {
        Self {
            solver_generation,
            basis_generation,
            watch_list_generation,
            runtime_generation,
        }
    }
}

/// Exact ay allowlist key.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYCanaryAllowlistKey {
    /// Solver-program semantic digest.
    pub solver_program_sha256: String,
    /// ay kernel family.
    pub family: AYCanaryFamily,
    /// Solver/basis/watch-list/runtime generation fence.
    pub generations: AYCanaryGenerationFence,
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

impl AYCanaryAllowlistKey {
    /// Build an exact ay canary key.
    pub fn new(
        solver_program_sha256: impl Into<String>,
        family: AYCanaryFamily,
        generations: AYCanaryGenerationFence,
        target: Target,
        target_facts_sha256: impl Into<String>,
        proof_policy: impl Into<String>,
        layout_checksum: impl Into<String>,
        manifest_sha256: impl Into<String>,
    ) -> Self {
        let mut key = Self {
            solver_program_sha256: solver_program_sha256.into(),
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
        put_str(&mut out, "trust-cg.jit_everywhere.ay_canary.key.v1");
        put_str(&mut out, &self.solver_program_sha256);
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
        !missing_required_text(&self.solver_program_sha256)
            && !missing_required_text(&self.target_facts_sha256)
            && !missing_required_text(&self.proof_policy)
            && !missing_required_text(&self.layout_checksum)
            && !missing_required_text(&self.manifest_sha256)
            && self.generations.solver_generation > 0
            && self.generations.basis_generation > 0
            && self.generations.watch_list_generation > 0
            && self.generations.runtime_generation > 0
            && self.key_sha256 == self.canonical_key_sha256()
    }
}

/// Manifest fields that must bind an allowlisted ay tuple.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYCanaryManifestBinding {
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

impl AYCanaryManifestBinding {
    /// Return true when this manifest binds the exact allowlist key.
    pub fn matches_key(&self, key: &AYCanaryAllowlistKey) -> bool {
        !missing_required_text(&self.source_sha256)
            && !missing_required_text(&self.trust_ir_sha256)
            && !missing_required_text(&self.native_payload_sha256)
            && !missing_required_text(&self.abi_checksum)
            && !missing_required_text(&self.compiler_config_sha256)
            && self.layout_checksum == key.layout_checksum
            && self.target_facts_sha256 == key.target_facts_sha256
            && self.proof_policy == key.proof_policy
            && self.consumer_kind == "ay"
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

/// Typed ay LRA proof-fact evidence bound into a canary proof report.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYCanaryLraProofFactEvidence {
    /// ay canary family.
    pub family: AYCanaryFamily,
    /// Target architecture.
    pub target: Target,
    /// Source digest bound by the proof facts.
    pub source_sha256: String,
    /// Canonical trust_ir digest bound by the proof facts.
    pub trust_ir_sha256: String,
    /// Target facts digest bound by the proof facts.
    pub target_facts_sha256: String,
    /// Proof-policy checksum bound by the proof facts.
    pub proof_policy: String,
    /// Layout checksum bound by the proof facts.
    pub layout_checksum: String,
    /// Manifest digest bound by the proof facts.
    pub manifest_sha256: String,
    /// Required typed metadata bindings.
    pub bindings: Vec<AYCanaryLraProofFactBinding>,
}

impl AYCanaryLraProofFactEvidence {
    /// Build the required AArch64 LRA proof-fact evidence for an exact canary tuple.
    pub fn aarch64_required_for(
        key: &AYCanaryAllowlistKey,
        manifest: &AYCanaryManifestBinding,
    ) -> Option<Self> {
        if key.target != Target::Aarch64 {
            return None;
        }
        let requirements = required_lra_proof_fact_requirements(key.family)?;
        Some(Self {
            family: key.family,
            target: key.target,
            source_sha256: manifest.source_sha256.clone(),
            trust_ir_sha256: manifest.trust_ir_sha256.clone(),
            target_facts_sha256: key.target_facts_sha256.clone(),
            proof_policy: key.proof_policy.clone(),
            layout_checksum: key.layout_checksum.clone(),
            manifest_sha256: key.manifest_sha256.clone(),
            bindings: requirements
                .iter()
                .map(|requirement| {
                    AYCanaryLraProofFactBinding::new(requirement.fact, requirement.lemma_id)
                })
                .collect(),
        })
    }

    /// Return the stable digest for this typed proof-fact report.
    pub fn canonical_report_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(&mut out, AY_CANARY_LRA_PROOF_FACT_SCHEMA);
        put_str(&mut out, self.family.as_str());
        put_str(&mut out, self.target.name());
        put_str(&mut out, &self.source_sha256);
        put_str(&mut out, &self.trust_ir_sha256);
        put_str(&mut out, &self.target_facts_sha256);
        put_str(&mut out, &self.proof_policy);
        put_str(&mut out, &self.layout_checksum);
        put_str(&mut out, &self.manifest_sha256);
        put_u64(&mut out, self.bindings.len() as u64);
        for binding in &self.bindings {
            put_str(&mut out, binding.fact.as_str());
            put_str(&mut out, &binding.metadata_key);
            put_str(&mut out, &binding.lemma_id);
        }
        format!("sha256:{}", sha256_hex(&out))
    }
}

/// Typed ay watched-list BCP proof-fact evidence bound into a canary proof report.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYCanaryBcpProofFactEvidence {
    /// ay canary family.
    pub family: AYCanaryFamily,
    /// Target architecture.
    pub target: Target,
    /// Solver/basis/watch/runtime generations bound by the proof facts.
    pub generations: AYCanaryGenerationFence,
    /// Source digest bound by the proof facts.
    pub source_sha256: String,
    /// Canonical trust_ir digest bound by the proof facts.
    pub trust_ir_sha256: String,
    /// ABI checksum bound by the result-ABI proof fact.
    pub abi_checksum: String,
    /// Target facts digest bound by the proof facts.
    pub target_facts_sha256: String,
    /// Proof-policy checksum bound by the proof facts.
    pub proof_policy: String,
    /// Layout checksum bound by the watch-layout proof fact.
    pub layout_checksum: String,
    /// Manifest digest bound by the proof facts.
    pub manifest_sha256: String,
    /// Replay root bound by the replay-comparison proof fact.
    pub replay_root_sha256: String,
    /// Telemetry key bound to the exact pre-activation tuple.
    pub telemetry_key: String,
    /// Required typed metadata bindings.
    pub bindings: Vec<AYCanaryBcpProofFactBinding>,
}

impl AYCanaryBcpProofFactEvidence {
    /// Build the required AArch64 BCP proof-fact evidence for an exact canary tuple.
    pub fn aarch64_required_for(
        key: &AYCanaryAllowlistKey,
        manifest: &AYCanaryManifestBinding,
    ) -> Option<Self> {
        if key.target != Target::Aarch64 || key.family != AYCanaryFamily::WatchListBcp {
            return None;
        }
        Some(Self {
            family: key.family,
            target: key.target,
            generations: key.generations,
            source_sha256: manifest.source_sha256.clone(),
            trust_ir_sha256: manifest.trust_ir_sha256.clone(),
            abi_checksum: manifest.abi_checksum.clone(),
            target_facts_sha256: key.target_facts_sha256.clone(),
            proof_policy: key.proof_policy.clone(),
            layout_checksum: key.layout_checksum.clone(),
            manifest_sha256: key.manifest_sha256.clone(),
            replay_root_sha256: manifest.replay_root_sha256.clone(),
            telemetry_key: manifest.telemetry_key.clone(),
            bindings: WATCH_LIST_BCP_PROOF_FACT_REQUIREMENTS
                .iter()
                .map(|requirement| {
                    AYCanaryBcpProofFactBinding::new(requirement.fact, requirement.lemma_id)
                })
                .collect(),
        })
    }

    /// Return the stable digest for this typed proof-fact report.
    pub fn canonical_report_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(&mut out, AY_CANARY_BCP_PROOF_FACT_SCHEMA);
        put_str(&mut out, self.family.as_str());
        put_str(&mut out, self.target.name());
        put_generations(&mut out, self.generations);
        put_str(&mut out, &self.source_sha256);
        put_str(&mut out, &self.trust_ir_sha256);
        put_str(&mut out, &self.abi_checksum);
        put_str(&mut out, &self.target_facts_sha256);
        put_str(&mut out, &self.proof_policy);
        put_str(&mut out, &self.layout_checksum);
        put_str(&mut out, &self.manifest_sha256);
        put_str(&mut out, &self.replay_root_sha256);
        put_str(&mut out, &self.telemetry_key);
        put_u64(&mut out, self.bindings.len() as u64);
        for binding in &self.bindings {
            put_str(&mut out, binding.fact.as_str());
            put_str(&mut out, &binding.metadata_key);
            put_str(&mut out, &binding.lemma_id);
        }
        format!("sha256:{}", sha256_hex(&out))
    }
}

/// Layout proof coverage for ay canary activation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYCanaryLayoutProof {
    /// Pointer inputs are covered.
    pub pointer_inputs: bool,
    /// Bounds are covered.
    pub bounds: bool,
    /// Mutability is covered.
    pub mutability: bool,
    /// Aliasing is covered.
    pub aliasing: bool,
    /// Rollback state is covered.
    pub rollback_state: bool,
    /// Generation fences are covered.
    pub generation_fences: bool,
    /// Consumer-owned memory is covered.
    pub consumer_owned_memory: bool,
    /// Wrapper identity covered by the proof.
    pub wrapper_id: String,
}

impl AYCanaryLayoutProof {
    /// Return true when layout proof covers all required domains.
    pub fn covers_manifest(&self, manifest: &AYCanaryManifestBinding) -> bool {
        self.pointer_inputs
            && self.bounds
            && self.mutability
            && self.aliasing
            && self.rollback_state
            && self.generation_fences
            && self.consumer_owned_memory
            && self.wrapper_id == manifest.wrapper_id
    }
}

/// Proof-policy decision recorded in validation provenance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AYCanaryProofDecision {
    /// Proof/TV accepted this tuple.
    Accepted,
    /// Proof/TV rejected this tuple.
    Rejected,
    /// Required proof/TV evidence is missing.
    Missing,
    /// Proof/TV timed out.
    Timeout,
    /// Proof/TV result was unknown.
    Unknown,
}

impl AYCanaryProofDecision {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::Rejected => "rejected",
            Self::Missing => "missing",
            Self::Timeout => "timeout",
            Self::Unknown => "unknown",
        }
    }
}

/// Validation provenance for the exact ay tuple.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYCanaryValidationProvenance {
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
    pub proof_policy_decision: AYCanaryProofDecision,
}

impl AYCanaryValidationProvenance {
    fn is_accepted_for(
        &self,
        key: &AYCanaryAllowlistKey,
        manifest: &AYCanaryManifestBinding,
    ) -> bool {
        self.proof_policy_decision == AYCanaryProofDecision::Accepted
            && !missing_required_text(&self.proof_report_sha256)
            && required_proof_fact_report_sha256(key, manifest)
                .map(|expected| self.proof_report_sha256 == expected)
                .unwrap_or(false)
            && !missing_required_text(&self.tv_report_sha256)
            && self.replay_root_sha256 == manifest.replay_root_sha256
            && !missing_required_text(&self.consumer_equivalence_sha256)
            && !missing_required_text(&self.validator_id)
    }
}

/// One ay native or baseline observation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYCanaryExecutionObservation {
    /// Visible result digest.
    pub result_sha256: String,
    /// Proof digest.
    pub proof_sha256: String,
    /// Witness digest.
    pub witness_sha256: String,
    /// Score digest.
    pub score_sha256: String,
    /// Status digest.
    pub status_sha256: String,
    /// Replay verdict digest.
    pub replay_verdict_sha256: String,
    /// Wrong-answer regression count.
    pub wrong_answer_regressions: u64,
    /// Proof regression count.
    pub proof_regressions: u64,
    /// Witness regression count.
    pub witness_regressions: u64,
    /// Score regression count.
    pub score_regressions: u64,
    /// Timeout or unknown regression count.
    pub timeout_unknown_regressions: u64,
    /// Crash regression count.
    pub crash_regressions: u64,
}

impl AYCanaryExecutionObservation {
    fn has_required_identity(&self) -> bool {
        !missing_required_text(&self.result_sha256)
            && !missing_required_text(&self.proof_sha256)
            && !missing_required_text(&self.witness_sha256)
            && !missing_required_text(&self.score_sha256)
            && !missing_required_text(&self.status_sha256)
            && !missing_required_text(&self.replay_verdict_sha256)
    }

    fn has_no_regressions(&self) -> bool {
        self.wrong_answer_regressions == 0
            && self.proof_regressions == 0
            && self.witness_regressions == 0
            && self.score_regressions == 0
            && self.timeout_unknown_regressions == 0
            && self.crash_regressions == 0
    }
}

/// Baseline/native equivalence and no-regression evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYCanaryEquivalenceEvidence {
    /// Baseline observation.
    pub baseline: AYCanaryExecutionObservation,
    /// Native observation.
    pub native: AYCanaryExecutionObservation,
}

impl AYCanaryEquivalenceEvidence {
    fn matches(&self) -> bool {
        self.baseline.has_required_identity()
            && self.native.has_required_identity()
            && self.baseline == self.native
            && self.baseline.has_no_regressions()
            && self.native.has_no_regressions()
    }
}

/// Live invalidation state checked before install and call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYCanaryInvalidationState {
    /// Current generation fence.
    pub current_generations: AYCanaryGenerationFence,
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

impl AYCanaryInvalidationState {
    fn matches(
        &self,
        key: &AYCanaryAllowlistKey,
        manifest: &AYCanaryManifestBinding,
    ) -> Result<(), AYCanaryRejectionReason> {
        if self.kill_switch_active {
            return Err(AYCanaryRejectionReason::KillSwitchActive);
        }
        if self.revoked {
            return Err(AYCanaryRejectionReason::Revoked);
        }
        if self.current_generations != key.generations {
            return Err(AYCanaryRejectionReason::StaleGeneration);
        }
        if self.target_facts_sha256 != key.target_facts_sha256
            || self.proof_policy != key.proof_policy
            || self.manifest_sha256 != key.manifest_sha256
            || self.source_sha256 != manifest.source_sha256
            || self.trust_ir_sha256 != manifest.trust_ir_sha256
            || self.native_payload_sha256 != manifest.native_payload_sha256
            || self.compiler_config_sha256 != manifest.compiler_config_sha256
        {
            return Err(AYCanaryRejectionReason::StaleGeneration);
        }
        Ok(())
    }
}

/// Parent product gate evidence required before real ay canary activation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct AYCanaryParentGateEvidence {
    /// Shared install gate accepted this tuple.
    pub install_gate_accepted: bool,
    /// ay consumer gate accepted this tuple.
    pub consumer_gate_accepted: bool,
    /// Downstream ay no-regression evidence accepted this tuple.
    pub downstream_ay_no_regression_accepted: bool,
}

impl AYCanaryParentGateEvidence {
    /// Return true only when all parent-gated product evidence exists.
    pub const fn accepted(self) -> bool {
        self.install_gate_accepted
            && self.consumer_gate_accepted
            && self.downstream_ay_no_regression_accepted
    }
}

/// Candidate evidence for one ay canary allowlist decision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYCanaryCandidate {
    /// Candidate mode.
    pub mode: AYCanaryCandidateMode,
    /// Exact allowlist key.
    pub key: AYCanaryAllowlistKey,
    /// Manifest binding.
    pub manifest: Option<AYCanaryManifestBinding>,
    /// Layout proof.
    pub layout: Option<AYCanaryLayoutProof>,
    /// Validation provenance.
    pub provenance: Option<AYCanaryValidationProvenance>,
    /// Baseline/native equivalence and no-regression evidence.
    pub equivalence: Option<AYCanaryEquivalenceEvidence>,
    /// Invalidation state.
    pub invalidation: Option<AYCanaryInvalidationState>,
}

/// Allowlist decision status.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AYCanaryDecisionStatus {
    /// Candidate is rejected.
    Rejected,
    /// Candidate matches the exact allowlist and evidence, but product activation is separate.
    AllowlistedRequiresProductGate,
}

impl AYCanaryDecisionStatus {
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
pub enum AYCanaryRejectionReason {
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
    /// ay no-regression evidence is mismatched.
    AYRegressionEvidenceMismatch,
    /// Parent product gate evidence is still required.
    MissingProductGateEvidence,
    /// Product activation remains outside this local prework issue.
    ProductActivationRequired,
}

impl AYCanaryRejectionReason {
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
            Self::AYRegressionEvidenceMismatch => "ay_regression_evidence_mismatch",
            Self::MissingProductGateEvidence => "missing_product_gate_evidence",
            Self::ProductActivationRequired => "product_activation_required",
        }
    }
}

/// Side effects blocked by this pre-activation allowlist.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct AYCanarySideEffects {
    /// Whether a callable handle was published.
    pub callable_handle_published: bool,
    /// Whether an installable-cache hit was accepted.
    pub installable_cache_hit_accepted: bool,
    /// Whether a ay registry entry was inserted.
    pub ay_registry_inserted: bool,
    /// Whether a release-install bundle was published.
    pub release_install_published: bool,
    /// Whether baseline execution was replaced.
    pub baseline_replaced: bool,
    /// Useful-native counter delta.
    pub useful_native_delta: u64,
}

impl AYCanarySideEffects {
    /// Return true when every install-authorizing side effect is blocked.
    pub const fn all_blocked(self) -> bool {
        !self.callable_handle_published
            && !self.installable_cache_hit_accepted
            && !self.ay_registry_inserted
            && !self.release_install_published
            && !self.baseline_replaced
            && self.useful_native_delta == 0
    }
}

/// Telemetry emitted by a ay canary allowlist decision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYCanaryTelemetryPacket {
    /// Schema.
    pub schema: &'static str,
    /// Schema version.
    pub schema_version: u32,
    /// Implementing issue.
    pub issue: u64,
    /// Allowlist key hash.
    pub key_sha256: String,
    /// Decision status.
    pub status: AYCanaryDecisionStatus,
    /// Decision reason.
    pub reason: AYCanaryRejectionReason,
    /// Replay root when present.
    pub replay_root_sha256: Option<String>,
    /// Telemetry key when present.
    pub telemetry_key: Option<String>,
    /// Side-effect summary.
    pub side_effects: AYCanarySideEffects,
    /// Canonical telemetry hash.
    pub record_sha256: String,
}

impl AYCanaryTelemetryPacket {
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

/// ay canary allowlist decision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYCanaryAllowlistDecision {
    /// Decision status.
    pub status: AYCanaryDecisionStatus,
    /// Decision reason.
    pub reason: AYCanaryRejectionReason,
    /// Baseline remains authoritative.
    pub baseline_authoritative: bool,
    /// Native is not product-authoritative in this local slice.
    pub native_authoritative: bool,
    /// Side effects.
    pub side_effects: AYCanarySideEffects,
    /// Telemetry packet.
    pub telemetry: AYCanaryTelemetryPacket,
}

impl AYCanaryAllowlistDecision {
    /// Return true when no callable/native authority was granted.
    pub fn is_pre_activation_only(&self) -> bool {
        self.baseline_authoritative
            && !self.native_authoritative
            && self.side_effects.all_blocked()
            && self.telemetry.side_effects.all_blocked()
            && self.telemetry.record_sha256 == self.telemetry.canonical_record_sha256()
    }
}

/// Combined ay canary precheck over allowlist, control-plane, and consumer admission.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYCanaryActivationPrecheckDecision {
    /// Exact-family allowlist decision.
    pub allowlist: AYCanaryAllowlistDecision,
    /// Existing install-gate/control-plane consumer-admission decision.
    pub consumer_admission: NativeInstallGateConsumerAdmissionDecision,
    /// Side effects authorized by this local canary precheck.
    pub side_effects: AYCanarySideEffects,
    /// Whether this local precheck published a ay registry entry.
    pub publish_ay_registry_entry: bool,
    /// Whether this local precheck published a callable ay handle.
    pub publish_callable_handle: bool,
    /// Useful-native counter delta from this local precheck.
    pub useful_native_delta: u64,
}

impl AYCanaryActivationPrecheckDecision {
    /// Return true when this precheck remains fixture-only and pre-activation.
    pub fn is_pre_activation_only(&self) -> bool {
        self.allowlist.is_pre_activation_only()
            && self.side_effects.all_blocked()
            && !(self.allowlist.native_authoritative
                && self.consumer_admission.actions.ay_registry_insert)
            && !self.publish_ay_registry_entry
            && !self.publish_callable_handle
            && self.useful_native_delta == 0
            && self.consumer_admission.telemetry.useful_native_delta == 0
    }
}

/// Combined ay canary precheck over allowlist and product-adapter admission.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYCanaryProductAdapterPrecheckDecision {
    /// Exact-family allowlist decision.
    pub allowlist: AYCanaryAllowlistDecision,
    /// Existing control-plane/product-adapter consumer admission decision.
    pub product_admission: ControlPlaneConsumerAdmissionProductDecision,
    /// Side effects authorized by this local canary precheck.
    pub side_effects: AYCanarySideEffects,
    /// Whether this local precheck published a ay registry entry.
    pub publish_ay_registry_entry: bool,
    /// Whether this local precheck published a callable ay handle.
    pub publish_callable_handle: bool,
    /// Useful-native counter delta from this local precheck.
    pub useful_native_delta: u64,
}

impl AYCanaryProductAdapterPrecheckDecision {
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
            && !self.publish_ay_registry_entry
            && !self.publish_callable_handle
            && self.useful_native_delta == 0
            && self.product_admission.product_adapter.useful_native_delta == 0
    }
}

/// Exact ay canary allowlist.
#[derive(Debug, Clone, Default)]
pub struct AYCanaryAllowlist {
    exact_keys: BTreeSet<String>,
}

impl AYCanaryAllowlist {
    /// Build an empty allowlist.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add one exact key. Wildcards/default-on entries are not representable.
    pub fn add_exact(&mut self, key: &AYCanaryAllowlistKey) {
        self.exact_keys.insert(key.key_sha256.clone());
    }

    /// Return true when this exact key is allowlisted.
    pub fn contains_exact(&self, key: &AYCanaryAllowlistKey) -> bool {
        self.exact_keys.contains(&key.key_sha256)
    }

    /// Evaluate one ay canary candidate.
    pub fn evaluate(
        &self,
        candidate: &AYCanaryCandidate,
        parent_gates: AYCanaryParentGateEvidence,
    ) -> AYCanaryAllowlistDecision {
        let reason = self.rejection_reason(candidate, parent_gates);
        let status = if reason == AYCanaryRejectionReason::ProductActivationRequired {
            AYCanaryDecisionStatus::AllowlistedRequiresProductGate
        } else {
            AYCanaryDecisionStatus::Rejected
        };
        self.decision(candidate, status, reason)
    }

    fn rejection_reason(
        &self,
        candidate: &AYCanaryCandidate,
        parent_gates: AYCanaryParentGateEvidence,
    ) -> AYCanaryRejectionReason {
        if !candidate.key.has_required_identity() || !self.contains_exact(&candidate.key) {
            return AYCanaryRejectionReason::NonAllowlisted;
        }
        match candidate.mode {
            AYCanaryCandidateMode::ProfileOnly => {
                return AYCanaryRejectionReason::ProfileOnlyNonCallable;
            }
            AYCanaryCandidateMode::ReplayOnly => {
                return AYCanaryRejectionReason::ReplayOnlyNonCallable;
            }
            AYCanaryCandidateMode::ShadowOnly => {
                return AYCanaryRejectionReason::ShadowOnlyNonCallable;
            }
            AYCanaryCandidateMode::CanaryInstallable => {}
        }

        let Some(manifest) = &candidate.manifest else {
            return AYCanaryRejectionReason::MissingManifest;
        };
        if !manifest.matches_key(&candidate.key) {
            if missing_required_text(&manifest.telemetry_key) {
                return AYCanaryRejectionReason::MissingTelemetry;
            }
            return AYCanaryRejectionReason::MissingManifest;
        }
        if missing_required_text(&manifest.telemetry_key) {
            return AYCanaryRejectionReason::MissingTelemetry;
        }

        let Some(layout) = &candidate.layout else {
            return AYCanaryRejectionReason::LayoutMismatch;
        };
        if !layout.covers_manifest(manifest) {
            return AYCanaryRejectionReason::LayoutMismatch;
        }

        let Some(provenance) = &candidate.provenance else {
            return AYCanaryRejectionReason::FailedProof;
        };
        if !provenance.is_accepted_for(&candidate.key, manifest) {
            return AYCanaryRejectionReason::FailedProof;
        }

        let Some(invalidation) = &candidate.invalidation else {
            return AYCanaryRejectionReason::StaleGeneration;
        };
        if let Err(reason) = invalidation.matches(&candidate.key, manifest) {
            return reason;
        }

        let Some(equivalence) = &candidate.equivalence else {
            return AYCanaryRejectionReason::MissingEquivalence;
        };
        if !equivalence.baseline.has_required_identity()
            || !equivalence.native.has_required_identity()
        {
            return AYCanaryRejectionReason::MissingEquivalence;
        }
        if !equivalence.matches() {
            return AYCanaryRejectionReason::AYRegressionEvidenceMismatch;
        }

        if !parent_gates.accepted() {
            return AYCanaryRejectionReason::MissingProductGateEvidence;
        }

        AYCanaryRejectionReason::ProductActivationRequired
    }

    fn decision(
        &self,
        candidate: &AYCanaryCandidate,
        status: AYCanaryDecisionStatus,
        reason: AYCanaryRejectionReason,
    ) -> AYCanaryAllowlistDecision {
        let side_effects = AYCanarySideEffects::default();
        let manifest = candidate.manifest.as_ref();
        let mut telemetry = AYCanaryTelemetryPacket {
            schema: JIT_AY_CANARY_ALLOWLIST_SCHEMA,
            schema_version: JIT_AY_CANARY_ALLOWLIST_SCHEMA_VERSION,
            issue: 742,
            key_sha256: candidate.key.key_sha256.clone(),
            status,
            reason,
            replay_root_sha256: manifest.map(|manifest| manifest.replay_root_sha256.clone()),
            telemetry_key: manifest.map(|manifest| manifest.telemetry_key.clone()),
            side_effects,
            record_sha256: String::new(),
        };
        telemetry.record_sha256 = telemetry.canonical_record_sha256();
        AYCanaryAllowlistDecision {
            status,
            reason,
            baseline_authoritative: true,
            native_authoritative: false,
            side_effects,
            telemetry,
        }
    }
}

/// Evaluate one ay canary tuple through the shared install-gate admission path.
///
/// This is deliberately a pre-activation composition: it consumes the exact ay
/// allowlist, parent-gate evidence, the live control-plane decision, and the
/// existing ay/TY consumer-admission gate, but it never publishes a registry
/// entry, callable handle, release install, or useful-native counter.
pub fn evaluate_ay_canary_activation_precheck(
    allowlist: &AYCanaryAllowlist,
    candidate: &AYCanaryCandidate,
    parent_gates: AYCanaryParentGateEvidence,
    packet: &NativeInstallGatePacket,
    expected_packet_hash: Option<ArtifactChecksum>,
    control_decision: &ControlPlaneDecision,
    consumer_evidence: &NativeInstallGateConsumerAdmissionEvidence,
) -> AYCanaryActivationPrecheckDecision {
    let allowlist = allowlist.evaluate(candidate, parent_gates);
    let consumer_admission = consumer_admission_with_control_plane(
        packet,
        expected_packet_hash,
        control_decision,
        consumer_evidence,
    );
    let side_effects = AYCanarySideEffects::default();
    AYCanaryActivationPrecheckDecision {
        allowlist,
        consumer_admission,
        side_effects,
        publish_ay_registry_entry: false,
        publish_callable_handle: false,
        useful_native_delta: 0,
    }
}

/// Evaluate one ay canary tuple through the product-adapter admission bridge.
///
/// This composes the exact ay allowlist, parent-gate evidence, caller-current
/// install-gate revalidation state, and the #749/#750 product adapter bridge.
/// It remains pre-activation-only: no ay registry entries or callable handles
/// are published, and useful-native counters stay at zero.
pub fn evaluate_ay_canary_product_adapter_precheck(
    allowlist: &AYCanaryAllowlist,
    candidate: &AYCanaryCandidate,
    parent_gates: AYCanaryParentGateEvidence,
    control_plane: &mut JitEverywhereControlPlane,
    control_candidate: &ControlPlaneCandidate,
    gate_evidence: ControlPlaneGateEvidence,
    packet: &NativeInstallGatePacket,
    expected_packet_hash: Option<ArtifactChecksum>,
    current: &NativeInstallGateRevalidationInput,
    consumer_evidence: &NativeInstallGateConsumerAdmissionEvidence,
) -> AYCanaryProductAdapterPrecheckDecision {
    let allowlist = allowlist.evaluate(candidate, parent_gates);
    let product_admission = control_plane.route_consumer_admission_product_adapter_with_current(
        control_candidate,
        gate_evidence,
        packet,
        expected_packet_hash,
        current,
        consumer_evidence,
    );
    let side_effects = AYCanarySideEffects::default();
    AYCanaryProductAdapterPrecheckDecision {
        allowlist,
        product_admission,
        side_effects,
        publish_ay_registry_entry: false,
        publish_callable_handle: false,
        useful_native_delta: 0,
    }
}

fn put_generations(out: &mut Vec<u8>, generations: AYCanaryGenerationFence) {
    put_u64(out, generations.solver_generation);
    put_u64(out, generations.basis_generation);
    put_u64(out, generations.watch_list_generation);
    put_u64(out, generations.runtime_generation);
}

fn required_lra_proof_fact_report_sha256(
    key: &AYCanaryAllowlistKey,
    manifest: &AYCanaryManifestBinding,
) -> Option<String> {
    AYCanaryLraProofFactEvidence::aarch64_required_for(key, manifest)
        .map(|evidence| evidence.canonical_report_sha256())
}

fn required_bcp_proof_fact_report_sha256(
    key: &AYCanaryAllowlistKey,
    manifest: &AYCanaryManifestBinding,
) -> Option<String> {
    AYCanaryBcpProofFactEvidence::aarch64_required_for(key, manifest)
        .map(|evidence| evidence.canonical_report_sha256())
}

fn required_proof_fact_report_sha256(
    key: &AYCanaryAllowlistKey,
    manifest: &AYCanaryManifestBinding,
) -> Option<String> {
    match key.family {
        AYCanaryFamily::SparseSubstitute | AYCanaryFamily::BasisRegionScanner => {
            required_lra_proof_fact_report_sha256(key, manifest)
        }
        AYCanaryFamily::WatchListBcp => required_bcp_proof_fact_report_sha256(key, manifest),
    }
}

fn required_lra_proof_fact_requirements(
    family: AYCanaryFamily,
) -> Option<&'static [AYCanaryLraProofFactRequirement]> {
    match family {
        AYCanaryFamily::SparseSubstitute => Some(&SPARSE_LRA_PROOF_FACT_REQUIREMENTS),
        AYCanaryFamily::BasisRegionScanner => Some(&BASIS_LRA_PROOF_FACT_REQUIREMENTS),
        AYCanaryFamily::WatchListBcp => None,
    }
}

fn put_side_effects(out: &mut Vec<u8>, side_effects: AYCanarySideEffects) {
    put_bool(out, side_effects.callable_handle_published);
    put_bool(out, side_effects.installable_cache_hit_accepted);
    put_bool(out, side_effects.ay_registry_inserted);
    put_bool(out, side_effects.release_install_published);
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

fn missing_required_text(value: &str) -> bool {
    value.trim().is_empty()
}
