// trust-cg-codegen/ay_lra_proof_manifest.rs - ay LRA proof-consumption manifest
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Typed proof-consumption contract for ay LRA native kernels.
//!
//! This module is deliberately data-only. It validates the product-facing
//! [`DeterministicArtifactManifest`](crate::jit_contract::DeterministicArtifactManifest)
//! plus sidecar proof/replay evidence for the current sparse-substitute and
//! basis-update roadmap slice. SAT/CHC/PB candidate-loop families are named as
//! future missing proof families so they cannot accidentally authorize product
//! promotion through this LRA path.

use std::collections::BTreeMap;

use crate::jit_contract::{
    AbiDescriptor, AbiValue, AbiValueKind, AbiVarargsPolicy, AliasPolicy, ArtifactChecksum,
    DeterministicArtifactManifest, ExecutableMemoryOwner, FieldLayout, JitArtifactKind, Mutability,
    PointerBounds, ProofEvidenceSummary, ProofMode, RecordLayout, SymbolSignature,
    TargetArchitecture, TargetOperatingSystem, TeardownPolicy,
};
use crate::jit_diagnostics::sha256_hex;

/// Stable schema tag for ay LRA proof-consumption manifests.
pub const AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA: &str =
    "trust-cg.ay_lra.proof_consumption_manifest.v1";

/// Stable numeric schema version for ay LRA proof-consumption manifests.
pub const AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA_VERSION: u32 = 1;

/// Issue that introduced this manifest contract.
pub const AY_LRA_PROOF_CONSUMPTION_MANIFEST_ISSUE: u64 = 796;

/// Stable schema tag for private/local ay LRA solver-program evidence.
pub const AY_LRA_LOCAL_SOLVER_PROGRAM_EVIDENCE_SCHEMA: &str =
    "trust-cg.ay_lra.local_solver_program_evidence.v1";

/// Stable numeric schema version for private/local solver-program evidence.
pub const AY_LRA_LOCAL_SOLVER_PROGRAM_EVIDENCE_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for private/local ay LRA perf JSON evidence.
pub const AY_LRA_LOCAL_PERF_JSON_EVIDENCE_SCHEMA: &str =
    "trust-cg.ay_lra.local_perf_json_evidence.v1";

/// Stable numeric schema version for private/local perf JSON evidence.
pub const AY_LRA_LOCAL_PERF_JSON_EVIDENCE_SCHEMA_VERSION: u32 = 1;

/// Observed native apply count in the private W2 sparse-substitute solver-program slice.
pub const AY_LRA_SPARSE_SOLVER_PROGRAM_NATIVE_APPLIES: u64 = 10;

/// Observed install count in the private W2 sparse-substitute solver-program slice.
pub const AY_LRA_SPARSE_SOLVER_PROGRAM_INSTALLS: u64 = 2;

/// Observed evidence-wait hit count in the private W2 sparse-substitute solver-program slice.
pub const AY_LRA_SPARSE_SOLVER_PROGRAM_EVIDENCE_WAIT_HITS: u64 = 1;

/// Observed baseline PAR-2 for the private W2 sparse-substitute solver-program slice, in milliseconds.
pub const AY_LRA_SPARSE_SOLVER_PROGRAM_BASELINE_PAR2_MILLIS: u64 = 271;

/// Observed candidate PAR-2 for the private W2 sparse-substitute solver-program slice, in milliseconds.
pub const AY_LRA_SPARSE_SOLVER_PROGRAM_CANDIDATE_PAR2_MILLIS: u64 = 264;

/// Observed candidate PAR-2 regression for the private W2 sparse-substitute solver-program slice.
pub const AY_LRA_SPARSE_SOLVER_PROGRAM_PAR2_REGRESSION_MILLIS: u64 = 0;

/// ay comparison JSON schema observed in the private sparse-substitute perf report.
pub const AY_LRA_SPARSE_PERF_JSON_REPORT_SCHEMA: &str = "ay.jit-roi-probe-comparison/v1";

/// SHA-256 of the private sparse-substitute solver-program perf report.
pub const AY_LRA_SPARSE_PERF_JSON_REPORT_SHA256: &str =
    "sha256:c0a544a587edbf6d290be083621165f8842a985feb4b85786d529ad6c75821bf";

/// Benchmarks represented by the private sparse-substitute perf report.
pub const AY_LRA_SPARSE_PERF_JSON_BENCHMARK_COUNT: u64 = 2;

/// Queue submissions represented by the private sparse-substitute perf report.
pub const AY_LRA_SPARSE_PERF_JSON_QUEUE_SUBMISSIONS: u64 = 4;

/// Total compile queue time in the private sparse-substitute perf report.
pub const AY_LRA_SPARSE_PERF_JSON_QUEUE_COMPILE_US_TOTAL: u64 = 5483;

/// Total submit-to-install queue time in the private sparse-substitute perf report.
pub const AY_LRA_SPARSE_PERF_JSON_SUBMIT_TO_INSTALL_US_TOTAL: u64 = 5595;

/// Rows attempted in the private/local basis-row batch telemetry slice.
pub const AY_LRA_BASIS_ROW_BATCH_TELEMETRY_ROWS_ATTEMPTED: u64 = 9;

/// Rows committed in the private/local basis-row batch telemetry slice.
pub const AY_LRA_BASIS_ROW_BATCH_TELEMETRY_ROWS_COMMITTED: u64 = 6;

/// First zero-based failed row in the private/local basis-row batch telemetry slice.
pub const AY_LRA_BASIS_ROW_BATCH_TELEMETRY_FIRST_FAILED_ROW: u64 = 6;

/// Stale-basis deopt count in the private/local basis-row batch telemetry slice.
pub const AY_LRA_BASIS_ROW_BATCH_TELEMETRY_STALE_DEOPTS: u64 = 1;

/// Coefficient-overflow deopt count in the private/local basis-row batch telemetry slice.
pub const AY_LRA_BASIS_ROW_BATCH_TELEMETRY_OVERFLOW_DEOPTS: u64 = 2;

/// Partial-row deopt count in the private/local basis-row batch telemetry slice.
pub const AY_LRA_BASIS_ROW_BATCH_TELEMETRY_PARTIAL_ROW_DEOPTS: u64 = 2;

/// Useful-native delta authorized by private/local basis-row batch telemetry.
pub const AY_LRA_BASIS_ROW_BATCH_TELEMETRY_USEFUL_NATIVE_DELTA: u64 = 0;

/// Observations in the private/local sparse affected-row batch status slice.
pub const AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OBSERVATIONS: u64 = 4;

/// Affected rows per observation in the private/local sparse affected-row batch slice.
pub const AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_PER_OBSERVATION: u64 = 3;

/// Rows attempted in the private/local sparse affected-row batch status slice.
pub const AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_ATTEMPTED: u64 = 12;

/// Total rows committed in the private/local sparse affected-row batch status slice.
pub const AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_COMMITTED_TOTAL: u64 = 5;

/// Exact row-output lengths observed for success, overflow, bounds, and stale rows.
pub const AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROW_OUTPUT_LENGTHS: [i64; 12] = [
    3,
    3,
    3,
    3,
    3,
    i64::MIN,
    3,
    i64::MIN,
    i64::MIN,
    i64::MIN,
    i64::MIN,
    i64::MIN,
];

/// Rows committed by each sparse affected-row batch observation.
pub const AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_COMMITTED: [u64; 4] = [3, 1, 1, 0];

/// First failed row by observation; -1 means the observation has no failed row.
pub const AY_LRA_SPARSE_AFFECTED_ROW_BATCH_FIRST_FAILED_ROWS: [i64; 4] = [-1, 1, 1, -1];

/// OK status count in the private/local sparse affected-row batch status slice.
pub const AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OK_STATUS_COUNT: u64 = 1;

/// Overflow status count in the private/local sparse affected-row batch status slice.
pub const AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OVERFLOW_STATUS_COUNT: u64 = 1;

/// Bounds status count in the private/local sparse affected-row batch status slice.
pub const AY_LRA_SPARSE_AFFECTED_ROW_BATCH_BOUNDS_STATUS_COUNT: u64 = 1;

/// Stale status count in the private/local sparse affected-row batch status slice.
pub const AY_LRA_SPARSE_AFFECTED_ROW_BATCH_STALE_STATUS_COUNT: u64 = 1;

/// Useful-native delta authorized by private/local sparse affected-row batch evidence.
pub const AY_LRA_SPARSE_AFFECTED_ROW_BATCH_USEFUL_NATIVE_DELTA: u64 = 0;

const SPARSE_STATUS_SYMBOL: &str = "ay_lra_sparse_substitute_status_probe";
const SPARSE_STATUS_RECORD: &str = "AYLraSparseSubstituteStatusAbi";
const SPARSE_STATUS_ABI: &str = "ay_lra_status_abi_v1";
const SPARSE_SUBSTITUTE_TRUST_IR_SOURCE_IDENTITY: &str = "trust_ir:ay:lra:sparse-substitute:v1";
const SPARSE_SUBSTITUTE_TRUST_CG_SOURCE_LOCK: &str =
    "source-lock-sha256:trust-cg:ay-lra-sparse-substitute:v1";
const SPARSE_SUBSTITUTE_TRUST_IR_SOURCE_LOCK: &str =
    "source-lock-sha256:trust-ir:ay-lra-sparse-substitute:v1";
const SPARSE_SUBSTITUTE_WRAPPER_IDENTITY: &str = "ay::lra::SparseSubstituteKernel::lp64:v1";
const SPARSE_AFFECTED_ROW_BATCH_STATUS_SYMBOL: &str =
    "ay_lra_sparse_affected_row_batch_status_probe";
const SPARSE_AFFECTED_ROW_BATCH_KERNEL: &str = "ay_lra_sparse_affected_row_batch";
const SPARSE_AFFECTED_ROW_BATCH_STATUS_RECORD: &str = "AYLraSparseAffectedRowBatchStatusAbi";
const SPARSE_AFFECTED_ROW_BATCH_STATUS_ABI: &str = "ay_lra_sparse_affected_row_batch_status_abi_v1";
const SPARSE_AFFECTED_ROW_BATCH_TRUST_IR_SOURCE_IDENTITY: &str =
    "trust_ir:ay:lra:sparse-affected-row-batch:v1";
const SPARSE_AFFECTED_ROW_BATCH_TRUST_CG_SOURCE_LOCK: &str =
    "source-lock-sha256:trust-cg:ay-lra-sparse-affected-row-batch:v1";
const SPARSE_AFFECTED_ROW_BATCH_TRUST_IR_SOURCE_LOCK: &str =
    "source-lock-sha256:trust-ir:ay-lra-sparse-affected-row-batch:v1";
const SPARSE_AFFECTED_ROW_BATCH_WRAPPER_IDENTITY: &str =
    "ay::lra::SparseAffectedRowBatchKernel::lp64:v1";
const SPARSE_AFFECTED_ROW_BATCH_ROW_OUTPUT_LENGTHS: &str = "exact_per_row_i64_lengths";
const SPARSE_AFFECTED_ROW_BATCH_OUTPUT_CAPACITY: &str = "runtime_i64";
const SPARSE_AFFECTED_ROW_BATCH_STATUS_VALUE: &str = "rows_committed";
const SPARSE_AFFECTED_ROW_BATCH_STATUS_DETAIL: &str = "first_failed_row";
const BASIS_STATUS_SYMBOL: &str = "ay_lra_basis_row_batch";
const BASIS_STATUS_RECORD: &str = "AYLraBasisRowBatchStatusAbi";
const BASIS_STATUS_ABI: &str = "ay_lra_basis_row_batch_status_abi_v1";
const BASIS_ROW_BATCH_TRUST_IR_SOURCE_IDENTITY: &str = "trust_ir:ay:lra:basis-row-batch:v1";
const BASIS_ROW_BATCH_TRUST_CG_SOURCE_LOCK: &str =
    "source-lock-sha256:trust-cg:ay-lra-basis-row-batch:v1";
const BASIS_ROW_BATCH_TRUST_IR_SOURCE_LOCK: &str =
    "source-lock-sha256:trust-ir:ay-lra-basis-row-batch:v1";
const BASIS_ROW_BATCH_WRAPPER_IDENTITY: &str = "ay::lra::BasisRowBatchKernel::lp64:v1";
const BASIS_ROW_BATCH_TABLEAU_ROW_LAYOUT: &str = "ptrs_to_i64_rows_len5_stride40";
const BASIS_ROW_BATCH_BASIS_ROW_LAYOUT: &str = "basis_epoch_pair_current_expected";
const BASIS_ROW_BATCH_ROW_REGION_HASH: &str = "pre_post_tableau_digest";
const BASIS_ROW_BATCH_INVALIDATION_ROW_REGION_HASH: &str = "runtime_tableau_digest";
const BASIS_ROW_BATCH_SCRATCH_ROLLBACK: &str = "row_lengths_as_commit_log_no_failed_row_rollback";
const BASIS_ROW_BATCH_ROLLBACK_FAILURE_DISPOSITION: &str =
    "non_promoting_deopt_failed_row_left_uncommitted";
const BASIS_ROW_BATCH_ALIAS_POLICY: &str = "exclusive_tableau_rows_shared_inputs";
const BASIS_ROW_BATCH_OUTPUT_CAPACITY: &str = "runtime_i64";
const BASIS_ROW_BATCH_COMMIT_POLICY: &str = "partial_row_deopt";
const BASIS_ROW_BATCH_STATUS_VALUE: &str = "rows_completed";
const BASIS_ROW_BATCH_STATUS_DETAIL: &str = "first_failed_row";
const BASIS_ROW_BATCH_PREFIX_ROLLBACK_CERTIFICATE: &str = "ay-lra-basis-prefix-rollback";
const BASIS_ROW_BATCH_PREFIX_ROLLBACK_LEMMA: &str = "ay_lra_basis.batch_prefix_commit_rollback";
const AARCH64_AAPCS64_CALLING_CONVENTION: &str = "aapcs64";
const AARCH64_MACOS_AAPCS64_LP64_TARGET_ABI_LAYOUT: &str = "aarch64-macos-aapcs64-lp64";
const PROOF_FACT_METADATA_PREFIX: &str = "ay_lra.proof_fact.";

/// ay LRA kernel family covered by the current manifest.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AYLraKernelFamily {
    /// Sparse substitute row update kernel.
    SparseSubstitute,
    /// Sparse substitute affected-row batch status kernel.
    SparseAffectedRowBatch,
    /// Basis-region or basis-row update kernel.
    BasisUpdate,
}

impl AYLraKernelFamily {
    /// Return the stable lower-snake-case family id.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::SparseSubstitute => "ay_lra_sparse_substitute",
            Self::SparseAffectedRowBatch => "ay_lra_sparse_affected_row_batch",
            Self::BasisUpdate => "ay_lra_basis_update",
        }
    }

    fn accepted_kernel_metadata(self) -> &'static [&'static str] {
        match self {
            Self::SparseSubstitute => &["ay_lra_sparse_substitute", "lra_sparse_substitute"],
            Self::SparseAffectedRowBatch => &[
                "ay_lra_sparse_affected_row_batch",
                "lra_sparse_affected_row_batch",
            ],
            Self::BasisUpdate => &["ay_lra_basis_row_batch", "ay_lra_basis_update"],
        }
    }
}

/// Proof family named by the ay LRA manifest.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AYLraProofFamily {
    /// LRA sparse substitute proof family.
    LraSparseSubstitute,
    /// LRA sparse affected-row batch proof family.
    LraSparseAffectedRowBatch,
    /// LRA basis update proof family.
    LraBasisUpdate,
    /// SAT candidate-loop proof family, not yet admitted by this LRA manifest.
    SatCandidateLoop,
    /// CHC candidate-loop proof family, not yet admitted by this LRA manifest.
    ChcCandidateLoop,
    /// PB candidate-loop proof family, not yet admitted by this LRA manifest.
    PbCandidateLoop,
}

impl AYLraProofFamily {
    /// Return the stable lower-snake-case family id.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::LraSparseSubstitute => "ay_lra_sparse_substitute",
            Self::LraSparseAffectedRowBatch => "ay_lra_sparse_affected_row_batch",
            Self::LraBasisUpdate => "ay_lra_basis_update",
            Self::SatCandidateLoop => "ay_sat_candidate_loop",
            Self::ChcCandidateLoop => "ay_chc_candidate_loop",
            Self::PbCandidateLoop => "ay_pb_candidate_loop",
        }
    }
}

/// Proof fact or admission binding required by a ay LRA manifest.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AYLraProofFact {
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

impl AYLraProofFact {
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
}

/// Whether a manifest entry is admission-critical now or only named for future work.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AYLraRequirementAvailability {
    /// Required before this manifest can be emitted for product-facing use.
    RequiredForAdmission,
    /// Named but not implemented/admitted by this issue.
    MissingFuture,
}

impl AYLraRequirementAvailability {
    /// Return the stable lower-snake-case status.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::RequiredForAdmission => "required_for_admission",
            Self::MissingFuture => "missing_future",
        }
    }
}

/// One proof requirement in the manifest.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYLraProofRequirement {
    /// Proof family that owns this requirement.
    pub family: AYLraProofFamily,
    /// Required proof fact.
    pub fact: AYLraProofFact,
    /// Stable lemma or checker id expected from proof evidence.
    pub lemma_id: &'static str,
    /// Current availability of this requirement.
    pub availability: AYLraRequirementAvailability,
}

/// Return the stable proof-evidence metadata key for one proof fact.
pub fn ay_lra_proof_fact_metadata_key(fact: AYLraProofFact) -> String {
    format!("{PROOF_FACT_METADATA_PREFIX}{}", fact.as_str())
}

/// Certificate dependency named by the manifest.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYLraCertificateDependency {
    /// Stable certificate or checker id.
    pub id: &'static str,
    /// Proof family that owns this certificate.
    pub family: AYLraProofFamily,
    /// Current availability of this dependency.
    pub availability: AYLraRequirementAvailability,
    /// Optional blocker issue or milestone for missing future work.
    pub blocker: Option<&'static str>,
}

/// Product gate fields that must remain bound before product promotion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYLraProductGateFields {
    /// Downstream consumer.
    pub consumer: &'static str,
    /// Product surface.
    pub surface: &'static str,
    /// Allowlist family key.
    pub allowlist_family: &'static str,
    /// Parent gates required before promotion.
    pub required_parent_gates: Vec<&'static str>,
    /// Telemetry counter policy.
    pub telemetry_counter_policy: &'static str,
    /// Whether the native artifact can increment useful-native counters.
    pub useful_native_eligible: bool,
    /// Whether baseline remains authoritative until product gate completion.
    pub baseline_authoritative_until_product_gate: bool,
}

/// Typed proof-consumption manifest for one ay LRA kernel family.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYLraKernelProofConsumptionManifest {
    /// Manifest schema.
    pub schema: &'static str,
    /// Manifest schema version.
    pub schema_version: u32,
    /// Implementing issue.
    pub issue: u64,
    /// Kernel family.
    pub kernel_family: AYLraKernelFamily,
    /// Required proof facts/lemmas.
    pub required_facts: Vec<AYLraProofRequirement>,
    /// Future proof families named by the roadmap but not admitted here.
    pub future_facts: Vec<AYLraProofRequirement>,
    /// Admission precondition facts.
    pub admission_preconditions: Vec<AYLraProofFact>,
    /// Certificate dependencies.
    pub certificate_dependencies: Vec<AYLraCertificateDependency>,
    /// Product gate fields.
    pub product_gate: AYLraProductGateFields,
}

impl AYLraKernelProofConsumptionManifest {
    /// Return the stable required fact ids as comma-separated text.
    pub fn required_fact_csv(&self) -> String {
        join_ids(
            self.required_facts
                .iter()
                .map(|requirement| requirement.fact.as_str()),
        )
    }

    /// Return the stable required lemma ids as comma-separated text.
    pub fn required_lemma_csv(&self) -> String {
        join_ids(
            self.required_facts
                .iter()
                .map(|requirement| requirement.lemma_id),
        )
    }

    /// Return the required certificate dependency ids as comma-separated text.
    pub fn required_certificate_csv(&self) -> String {
        join_ids(
            self.certificate_dependencies
                .iter()
                .filter(|dependency| {
                    dependency.availability == AYLraRequirementAvailability::RequiredForAdmission
                })
                .map(|dependency| dependency.id),
        )
    }

    /// Return the future proof-family ids as comma-separated text.
    pub fn future_family_csv(&self) -> String {
        join_ids(
            self.future_facts
                .iter()
                .map(|requirement| requirement.family.as_str()),
        )
    }
}

/// Evidence availability supplied by a producer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AYLraEvidenceAvailability {
    /// Evidence is present and available.
    Available,
    /// Evidence is missing.
    Missing,
    /// Evidence belongs to a future family and is not admissible now.
    Future,
}

impl AYLraEvidenceAvailability {
    /// Return the stable lower-snake-case evidence availability id.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Available => "available",
            Self::Missing => "missing",
            Self::Future => "future",
        }
    }

    fn is_available(self) -> bool {
        self == Self::Available
    }
}

/// Basis epoch evidence observed at admission time.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AYLraBasisEpochEvidence {
    /// Current runtime basis epoch.
    pub current_epoch: u64,
    /// Epoch expected by the artifact.
    pub expected_epoch: u64,
}

impl AYLraBasisEpochEvidence {
    /// Return true when the artifact basis epoch is fresh.
    pub const fn is_fresh(self) -> bool {
        self.current_epoch == self.expected_epoch
    }
}

/// Replay artifacts comparing generic, specialized, and reference behavior.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYLraReplayComparison {
    /// Manifest checksum bound by replay.
    pub manifest_checksum: ArtifactChecksum,
    /// Replay root digest.
    pub replay_root_sha256: String,
    /// Generic path behavior digest.
    pub generic_behavior_sha256: String,
    /// Specialized path behavior digest.
    pub specialized_behavior_sha256: String,
    /// Reference behavior digest.
    pub reference_behavior_sha256: String,
}

impl AYLraReplayComparison {
    fn compares(
        &self,
        manifest_checksum: ArtifactChecksum,
        kernel_family: AYLraKernelFamily,
    ) -> bool {
        self.manifest_checksum == manifest_checksum
            && replay_hashes_bound(self, kernel_family)
            && self.generic_behavior_sha256 == self.specialized_behavior_sha256
            && self.generic_behavior_sha256 == self.reference_behavior_sha256
    }
}

/// Parent product gate evidence present at the manifest boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYLraProductGateEvidence {
    /// Native install-gate packet digest.
    pub install_gate_packet_sha256: String,
    /// ay consumer admission digest.
    pub consumer_admission_sha256: String,
    /// Replay identity digest.
    pub replay_identity_sha256: String,
    /// Telemetry record digest.
    pub telemetry_record_sha256: String,
}

impl AYLraProductGateEvidence {
    fn is_complete(&self, kernel_family: AYLraKernelFamily) -> bool {
        product_gate_hashes_bound(self, kernel_family)
    }
}

/// Native-dispatch evidence kind observed for a local ay LRA solver-program run.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AYLraSolverProgramEvidenceKind {
    /// Native counters are only profile evidence and do not prove solver-program dispatch.
    ProfileOnly,
    /// Solver-program-native dispatch evidence is present.
    SolverProgramNative,
}

impl AYLraSolverProgramEvidenceKind {
    /// Return the stable evidence-kind id.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ProfileOnly => "profile-only",
            Self::SolverProgramNative => "solver-program-native",
        }
    }
}

/// Publication scope for ay LRA solver-program evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AYLraSolverProgramEvidenceScope {
    /// Evidence is private/local and cannot be used as a publication claim.
    PrivateLocal,
    /// Evidence claims published authority and must not be admitted here.
    Published,
}

impl AYLraSolverProgramEvidenceScope {
    /// Return the stable evidence-scope id.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::PrivateLocal => "private-local",
            Self::Published => "published",
        }
    }
}

/// Counter facts observed for a local sparse-substitute solver-program run.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AYLraSparseSubstituteSolverProgramCounters {
    /// solver_program.lra_basis_region.native_applies
    pub native_applies: u64,
    /// solver_program.lra_basis_region.installs
    pub installs: u64,
    /// solver_program.lra_basis_region.evidence_wait_hits
    pub evidence_wait_hits: u64,
}

impl AYLraSparseSubstituteSolverProgramCounters {
    /// Return the private/local sparse solver-program counter facts.
    pub const fn packet1_observed() -> Self {
        Self {
            native_applies: AY_LRA_SPARSE_SOLVER_PROGRAM_NATIVE_APPLIES,
            installs: AY_LRA_SPARSE_SOLVER_PROGRAM_INSTALLS,
            evidence_wait_hits: AY_LRA_SPARSE_SOLVER_PROGRAM_EVIDENCE_WAIT_HITS,
        }
    }
}

/// Canonical hash bindings for local sparse-substitute solver-program evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYLraSparseSubstituteSolverProgramEvidenceHashes {
    /// Hash over manifest proof facts and attached proof evidence.
    pub proof_facts_sha256: String,
    /// Hash over replay comparison evidence.
    pub replay_sha256: String,
    /// Hash over product-gate evidence.
    pub product_gate_sha256: String,
    /// Hash over the complete local evidence tuple.
    pub evidence_tuple_sha256: String,
}

impl AYLraSparseSubstituteSolverProgramEvidenceHashes {
    fn empty() -> Self {
        Self {
            proof_facts_sha256: String::new(),
            replay_sha256: String::new(),
            product_gate_sha256: String::new(),
            evidence_tuple_sha256: String::new(),
        }
    }

    fn all_canonical_sha256(&self) -> bool {
        canonical_sha256_bound(&self.proof_facts_sha256)
            && canonical_sha256_bound(&self.replay_sha256)
            && canonical_sha256_bound(&self.product_gate_sha256)
            && canonical_sha256_bound(&self.evidence_tuple_sha256)
    }
}

/// Private/local sparse-substitute solver-program evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYLraSparseSubstituteSolverProgramEvidence {
    /// Evidence schema.
    pub schema: &'static str,
    /// Evidence schema version.
    pub schema_version: u32,
    /// Observed native-dispatch evidence kind.
    pub evidence_kind: AYLraSolverProgramEvidenceKind,
    /// Publication scope.
    pub scope: AYLraSolverProgramEvidenceScope,
    /// Observed counter facts.
    pub counters: AYLraSparseSubstituteSolverProgramCounters,
    /// Baseline PAR-2 in milliseconds.
    pub baseline_par2_millis: u64,
    /// Candidate PAR-2 in milliseconds.
    pub candidate_par2_millis: u64,
    /// Whether the evidence claims production activation.
    pub production_activation: bool,
    /// Whether the evidence claims publication authority.
    pub publication_claim: bool,
    /// Canonical hash bindings.
    pub hashes: AYLraSparseSubstituteSolverProgramEvidenceHashes,
}

impl AYLraSparseSubstituteSolverProgramEvidence {
    /// Return the private/local profile-only observation.
    pub fn packet1_private_local_profile_only() -> Self {
        Self::packet1_private_local(AYLraSolverProgramEvidenceKind::ProfileOnly)
    }

    /// Return the private/local observation with an explicit evidence kind.
    pub fn packet1_private_local(evidence_kind: AYLraSolverProgramEvidenceKind) -> Self {
        Self {
            schema: AY_LRA_LOCAL_SOLVER_PROGRAM_EVIDENCE_SCHEMA,
            schema_version: AY_LRA_LOCAL_SOLVER_PROGRAM_EVIDENCE_SCHEMA_VERSION,
            evidence_kind,
            scope: AYLraSolverProgramEvidenceScope::PrivateLocal,
            counters: AYLraSparseSubstituteSolverProgramCounters::packet1_observed(),
            baseline_par2_millis: AY_LRA_SPARSE_SOLVER_PROGRAM_BASELINE_PAR2_MILLIS,
            candidate_par2_millis: AY_LRA_SPARSE_SOLVER_PROGRAM_CANDIDATE_PAR2_MILLIS,
            production_activation: false,
            publication_claim: false,
            hashes: AYLraSparseSubstituteSolverProgramEvidenceHashes::empty(),
        }
    }

    /// Return this evidence with all canonical hash bindings filled in.
    pub fn with_canonical_hashes(
        mut self,
        manifest: &AYLraKernelProofConsumptionManifest,
        evidence: &AYLraProofConsumptionEvidence,
    ) -> Self {
        self.hashes = self.canonical_hashes(manifest, evidence);
        self
    }

    /// Compute canonical hash bindings for the current manifest/evidence tuple.
    pub fn canonical_hashes(
        &self,
        manifest: &AYLraKernelProofConsumptionManifest,
        evidence: &AYLraProofConsumptionEvidence,
    ) -> AYLraSparseSubstituteSolverProgramEvidenceHashes {
        let proof_facts_sha256 = ay_lra_solver_program_proof_facts_sha256(manifest, evidence);
        let replay_sha256 =
            ay_lra_solver_program_replay_sha256(manifest.kernel_family, &evidence.replay);
        let product_gate_sha256 = ay_lra_solver_program_product_gate_sha256(
            manifest.kernel_family,
            &evidence.product_gate,
        );
        let evidence_tuple_sha256 = self.canonical_evidence_tuple_sha256(
            manifest,
            evidence,
            &proof_facts_sha256,
            &replay_sha256,
            &product_gate_sha256,
        );

        AYLraSparseSubstituteSolverProgramEvidenceHashes {
            proof_facts_sha256,
            replay_sha256,
            product_gate_sha256,
            evidence_tuple_sha256,
        }
    }

    /// Return the candidate minus baseline PAR-2 delta in milliseconds.
    pub const fn par2_regression_millis(&self) -> u64 {
        self.candidate_par2_millis
            .saturating_sub(self.baseline_par2_millis)
    }

    /// Return true when the candidate regressed against baseline PAR-2.
    pub const fn has_par2_regression(&self) -> bool {
        self.candidate_par2_millis > self.baseline_par2_millis
    }

    fn binds_packet1_observed_facts(&self) -> bool {
        self.counters == AYLraSparseSubstituteSolverProgramCounters::packet1_observed()
            && self.baseline_par2_millis == AY_LRA_SPARSE_SOLVER_PROGRAM_BASELINE_PAR2_MILLIS
            && self.candidate_par2_millis == AY_LRA_SPARSE_SOLVER_PROGRAM_CANDIDATE_PAR2_MILLIS
            && self.par2_regression_millis() == AY_LRA_SPARSE_SOLVER_PROGRAM_PAR2_REGRESSION_MILLIS
    }

    fn canonical_evidence_tuple_sha256(
        &self,
        manifest: &AYLraKernelProofConsumptionManifest,
        evidence: &AYLraProofConsumptionEvidence,
        proof_facts_sha256: &str,
        replay_sha256: &str,
        product_gate_sha256: &str,
    ) -> String {
        let mut out = Vec::new();
        put_str(
            &mut out,
            "trust-cg.ay_lra.sparse_solver_program.evidence_tuple.v1",
        );
        put_str(&mut out, self.schema);
        put_u64(&mut out, u64::from(self.schema_version));
        put_str(&mut out, manifest.kernel_family.as_str());
        put_str(&mut out, &evidence.replay.manifest_checksum.to_string());
        put_str(&mut out, self.evidence_kind.as_str());
        put_str(&mut out, self.scope.as_str());
        put_u64(&mut out, self.counters.native_applies);
        put_u64(&mut out, self.counters.installs);
        put_u64(&mut out, self.counters.evidence_wait_hits);
        put_u64(&mut out, self.baseline_par2_millis);
        put_u64(&mut out, self.candidate_par2_millis);
        put_u64(&mut out, self.par2_regression_millis());
        put_bool(&mut out, self.production_activation);
        put_bool(&mut out, self.publication_claim);
        put_str(&mut out, proof_facts_sha256);
        put_str(&mut out, replay_sha256);
        put_str(&mut out, product_gate_sha256);
        sha256_digest(&out)
    }
}

/// Compile amortization facts from a ay LRA sparse-substitute perf JSON report.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AYLraSparseSubstitutePerfJsonCompileAmortization {
    /// Benchmarks represented by the report.
    pub benchmark_count: u64,
    /// Native sparse-substitute applications in the candidate run.
    pub native_applies: u64,
    /// Native sparse-substitute installs in the candidate run.
    pub native_installs: u64,
    /// Queue submissions in the candidate run.
    pub queue_submissions: u64,
    /// Total compile queue time in microseconds.
    pub queue_compile_us_total: u64,
    /// Total submit-to-install queue time in microseconds.
    pub submit_to_install_us_total: u64,
}

impl AYLraSparseSubstitutePerfJsonCompileAmortization {
    /// Return the compile amortization facts from the current private report.
    pub const fn current_private_report() -> Self {
        Self {
            benchmark_count: AY_LRA_SPARSE_PERF_JSON_BENCHMARK_COUNT,
            native_applies: AY_LRA_SPARSE_SOLVER_PROGRAM_NATIVE_APPLIES,
            native_installs: AY_LRA_SPARSE_SOLVER_PROGRAM_INSTALLS,
            queue_submissions: AY_LRA_SPARSE_PERF_JSON_QUEUE_SUBMISSIONS,
            queue_compile_us_total: AY_LRA_SPARSE_PERF_JSON_QUEUE_COMPILE_US_TOTAL,
            submit_to_install_us_total: AY_LRA_SPARSE_PERF_JSON_SUBMIT_TO_INSTALL_US_TOTAL,
        }
    }

    /// Return true when compile cost is amortized across installed native applications.
    pub const fn has_compile_amortization(self) -> bool {
        self.benchmark_count > 0
            && self.native_installs > 0
            && self.native_applies >= self.native_installs
            && self.queue_submissions >= self.native_installs
            && self.queue_compile_us_total > 0
            && self.submit_to_install_us_total >= self.queue_compile_us_total
    }

    fn binds_current_private_report(self) -> bool {
        self == Self::current_private_report() && self.has_compile_amortization()
    }
}

/// Apply-latency facts expected from a ay LRA sparse-substitute perf JSON report.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AYLraSparseSubstitutePerfJsonApplyLatency {
    /// Baseline p50 apply latency in microseconds.
    pub baseline_p50_us: Option<u64>,
    /// Baseline p95 apply latency in microseconds.
    pub baseline_p95_us: Option<u64>,
    /// Native p50 apply latency in microseconds.
    pub native_p50_us: Option<u64>,
    /// Native p95 apply latency in microseconds.
    pub native_p95_us: Option<u64>,
}

impl AYLraSparseSubstitutePerfJsonApplyLatency {
    /// Return the current private report latency state: p50/p95 apply latency is absent.
    pub const fn missing_from_current_private_report() -> Self {
        Self {
            baseline_p50_us: None,
            baseline_p95_us: None,
            native_p50_us: None,
            native_p95_us: None,
        }
    }

    /// Return true when both baseline and native p50/p95 apply latency are present.
    pub fn has_p50_p95_apply_latency(self) -> bool {
        match (
            self.baseline_p50_us,
            self.baseline_p95_us,
            self.native_p50_us,
            self.native_p95_us,
        ) {
            (Some(b50), Some(b95), Some(n50), Some(n95)) => {
                b50 > 0 && n50 > 0 && b50 <= b95 && n50 <= n95
            }
            _ => false,
        }
    }

    /// Return true when complete native latency evidence is worse than baseline.
    pub fn has_native_apply_latency_regression(self) -> bool {
        match (
            self.baseline_p50_us,
            self.baseline_p95_us,
            self.native_p50_us,
            self.native_p95_us,
        ) {
            (Some(b50), Some(b95), Some(n50), Some(n95)) if b50 <= b95 && n50 <= n95 => {
                n50 > b50 || n95 > b95
            }
            _ => false,
        }
    }
}

/// Canonical hash bindings for local sparse-substitute perf JSON evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYLraSparseSubstitutePerfJsonEvidenceHashes {
    /// Hash over the bound artifact and proof-consumption manifest identities.
    pub manifest_sha256: String,
    /// Hash over manifest proof facts and attached proof evidence.
    pub proof_facts_sha256: String,
    /// Hash over replay comparison evidence.
    pub replay_sha256: String,
    /// Hash over product-gate evidence.
    pub product_gate_sha256: String,
    /// Hash over the complete local perf JSON tuple.
    pub evidence_tuple_sha256: String,
}

impl AYLraSparseSubstitutePerfJsonEvidenceHashes {
    fn empty() -> Self {
        Self {
            manifest_sha256: String::new(),
            proof_facts_sha256: String::new(),
            replay_sha256: String::new(),
            product_gate_sha256: String::new(),
            evidence_tuple_sha256: String::new(),
        }
    }

    fn all_canonical_sha256(&self) -> bool {
        canonical_sha256_bound(&self.manifest_sha256)
            && canonical_sha256_bound(&self.proof_facts_sha256)
            && canonical_sha256_bound(&self.replay_sha256)
            && canonical_sha256_bound(&self.product_gate_sha256)
            && canonical_sha256_bound(&self.evidence_tuple_sha256)
    }
}

/// Private/local sparse-substitute perf JSON evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYLraSparseSubstitutePerfJsonEvidence {
    /// Evidence schema.
    pub schema: &'static str,
    /// Evidence schema version.
    pub schema_version: u32,
    /// ay perf report schema.
    pub report_schema: &'static str,
    /// ay perf report SHA-256, prefixed with `sha256:`.
    pub report_sha256: String,
    /// Publication scope.
    pub scope: AYLraSolverProgramEvidenceScope,
    /// Compile amortization facts.
    pub compile_amortization: AYLraSparseSubstitutePerfJsonCompileAmortization,
    /// Required p50/p95 apply-latency facts.
    pub apply_latency: AYLraSparseSubstitutePerfJsonApplyLatency,
    /// Whether the evidence claims production activation.
    pub production_activation: bool,
    /// Whether the evidence claims publication authority.
    pub publication_claim: bool,
    /// Useful-native counter delta authorized by this local perf slice.
    pub useful_native_delta: u64,
    /// Canonical hash bindings.
    pub hashes: AYLraSparseSubstitutePerfJsonEvidenceHashes,
}

impl AYLraSparseSubstitutePerfJsonEvidence {
    /// Return the current private perf report facts. The report has compile
    /// amortization counters, but does not yet carry p50/p95 apply latency.
    pub fn current_private_report_missing_apply_latency() -> Self {
        Self {
            schema: AY_LRA_LOCAL_PERF_JSON_EVIDENCE_SCHEMA,
            schema_version: AY_LRA_LOCAL_PERF_JSON_EVIDENCE_SCHEMA_VERSION,
            report_schema: AY_LRA_SPARSE_PERF_JSON_REPORT_SCHEMA,
            report_sha256: AY_LRA_SPARSE_PERF_JSON_REPORT_SHA256.to_owned(),
            scope: AYLraSolverProgramEvidenceScope::PrivateLocal,
            compile_amortization:
                AYLraSparseSubstitutePerfJsonCompileAmortization::current_private_report(),
            apply_latency:
                AYLraSparseSubstitutePerfJsonApplyLatency::missing_from_current_private_report(),
            production_activation: false,
            publication_claim: false,
            useful_native_delta: 0,
            hashes: AYLraSparseSubstitutePerfJsonEvidenceHashes::empty(),
        }
    }

    /// Return this evidence with apply-latency fields supplied by a caller.
    pub fn with_apply_latency(
        mut self,
        baseline_p50_us: u64,
        baseline_p95_us: u64,
        native_p50_us: u64,
        native_p95_us: u64,
    ) -> Self {
        self.apply_latency = AYLraSparseSubstitutePerfJsonApplyLatency {
            baseline_p50_us: Some(baseline_p50_us),
            baseline_p95_us: Some(baseline_p95_us),
            native_p50_us: Some(native_p50_us),
            native_p95_us: Some(native_p95_us),
        };
        self
    }

    /// Return this evidence with all canonical hash bindings filled in.
    pub fn with_canonical_hashes(
        mut self,
        artifact: &DeterministicArtifactManifest,
        manifest: &AYLraKernelProofConsumptionManifest,
        evidence: &AYLraProofConsumptionEvidence,
    ) -> Self {
        self.hashes = self.canonical_hashes(artifact, manifest, evidence);
        self
    }

    /// Compute canonical hash bindings for the current artifact/manifest/evidence tuple.
    pub fn canonical_hashes(
        &self,
        artifact: &DeterministicArtifactManifest,
        manifest: &AYLraKernelProofConsumptionManifest,
        evidence: &AYLraProofConsumptionEvidence,
    ) -> AYLraSparseSubstitutePerfJsonEvidenceHashes {
        let manifest_sha256 = ay_lra_sparse_perf_json_manifest_sha256(artifact, manifest);
        let proof_facts_sha256 = ay_lra_sparse_perf_json_proof_facts_sha256(manifest, evidence);
        let replay_sha256 =
            ay_lra_sparse_perf_json_replay_sha256(manifest.kernel_family, &evidence.replay);
        let product_gate_sha256 = ay_lra_sparse_perf_json_product_gate_sha256(
            manifest.kernel_family,
            &evidence.product_gate,
        );
        let evidence_tuple_sha256 = self.canonical_evidence_tuple_sha256(
            artifact,
            manifest,
            evidence,
            &manifest_sha256,
            &proof_facts_sha256,
            &replay_sha256,
            &product_gate_sha256,
        );

        AYLraSparseSubstitutePerfJsonEvidenceHashes {
            manifest_sha256,
            proof_facts_sha256,
            replay_sha256,
            product_gate_sha256,
            evidence_tuple_sha256,
        }
    }

    fn report_identity_bound(&self) -> bool {
        self.report_schema == AY_LRA_SPARSE_PERF_JSON_REPORT_SCHEMA
            && self.report_sha256 == AY_LRA_SPARSE_PERF_JSON_REPORT_SHA256
            && canonical_sha256_bound(&self.report_sha256)
    }

    fn canonical_evidence_tuple_sha256(
        &self,
        artifact: &DeterministicArtifactManifest,
        manifest: &AYLraKernelProofConsumptionManifest,
        evidence: &AYLraProofConsumptionEvidence,
        manifest_sha256: &str,
        proof_facts_sha256: &str,
        replay_sha256: &str,
        product_gate_sha256: &str,
    ) -> String {
        let mut out = Vec::new();
        put_str(
            &mut out,
            "trust-cg.ay_lra.sparse_substitute.perf_json.evidence_tuple.v1",
        );
        put_str(&mut out, self.schema);
        put_u64(&mut out, u64::from(self.schema_version));
        put_str(&mut out, manifest.kernel_family.as_str());
        put_str(&mut out, &artifact.checksum().to_string());
        put_str(&mut out, &evidence.replay.manifest_checksum.to_string());
        put_str(&mut out, self.report_schema);
        put_str(&mut out, &self.report_sha256);
        put_str(&mut out, self.scope.as_str());
        put_u64(&mut out, self.compile_amortization.benchmark_count);
        put_u64(&mut out, self.compile_amortization.native_applies);
        put_u64(&mut out, self.compile_amortization.native_installs);
        put_u64(&mut out, self.compile_amortization.queue_submissions);
        put_u64(&mut out, self.compile_amortization.queue_compile_us_total);
        put_u64(
            &mut out,
            self.compile_amortization.submit_to_install_us_total,
        );
        put_option_u64(&mut out, self.apply_latency.baseline_p50_us);
        put_option_u64(&mut out, self.apply_latency.baseline_p95_us);
        put_option_u64(&mut out, self.apply_latency.native_p50_us);
        put_option_u64(&mut out, self.apply_latency.native_p95_us);
        put_u64(&mut out, self.useful_native_delta);
        put_bool(&mut out, self.production_activation);
        put_bool(&mut out, self.publication_claim);
        put_str(&mut out, manifest_sha256);
        put_str(&mut out, proof_facts_sha256);
        put_str(&mut out, replay_sha256);
        put_str(&mut out, product_gate_sha256);
        sha256_digest(&out)
    }
}

/// Counter facts observed for a local sparse affected-row batch status slice.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AYLraSparseAffectedRowBatchCounters {
    /// Affected rows covered by each observed batch invocation.
    pub affected_rows_per_observation: u64,
    /// Exact row-output lengths written by each observed row.
    pub row_output_lengths: Vec<i64>,
    /// Rows committed by each observed batch invocation.
    pub rows_committed: Vec<u64>,
    /// First failed row by observation; -1 means the observation has no failed row.
    pub first_failed_rows: Vec<i64>,
    /// OK status observations.
    pub ok_statuses: u64,
    /// Overflow status observations.
    pub overflow_statuses: u64,
    /// Bounds status observations.
    pub bounds_statuses: u64,
    /// Stale-basis status observations.
    pub stale_statuses: u64,
}

impl AYLraSparseAffectedRowBatchCounters {
    /// Return the private/local sparse affected-row batch status facts.
    pub fn private_local_observed() -> Self {
        Self {
            affected_rows_per_observation: AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_PER_OBSERVATION,
            row_output_lengths: AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROW_OUTPUT_LENGTHS.to_vec(),
            rows_committed: AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_COMMITTED.to_vec(),
            first_failed_rows: AY_LRA_SPARSE_AFFECTED_ROW_BATCH_FIRST_FAILED_ROWS.to_vec(),
            ok_statuses: AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OK_STATUS_COUNT,
            overflow_statuses: AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OVERFLOW_STATUS_COUNT,
            bounds_statuses: AY_LRA_SPARSE_AFFECTED_ROW_BATCH_BOUNDS_STATUS_COUNT,
            stale_statuses: AY_LRA_SPARSE_AFFECTED_ROW_BATCH_STALE_STATUS_COUNT,
        }
    }

    /// Return the number of rows represented by the exact row-length vector.
    pub fn rows_attempted(&self) -> u64 {
        self.row_output_lengths.len() as u64
    }

    /// Return total committed rows across the observed batch invocations.
    pub fn total_rows_committed(&self) -> u64 {
        self.rows_committed.iter().sum()
    }

    fn observation_count(&self) -> u64 {
        self.rows_committed.len() as u64
    }

    fn status_count(&self) -> u64 {
        self.ok_statuses + self.overflow_statuses + self.bounds_statuses + self.stale_statuses
    }
}

/// Canonical hash bindings for local sparse affected-row batch evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYLraSparseAffectedRowBatchEvidenceHashes {
    /// Hash over the bound artifact and proof-consumption manifest identities.
    pub manifest_sha256: String,
    /// Hash over manifest proof facts and attached proof evidence.
    pub proof_facts_sha256: String,
    /// Hash over replay comparison evidence.
    pub replay_sha256: String,
    /// Hash over product-gate evidence.
    pub product_gate_sha256: String,
    /// Hash over the complete local sparse affected-row batch tuple.
    pub evidence_tuple_sha256: String,
}

impl AYLraSparseAffectedRowBatchEvidenceHashes {
    fn empty() -> Self {
        Self {
            manifest_sha256: String::new(),
            proof_facts_sha256: String::new(),
            replay_sha256: String::new(),
            product_gate_sha256: String::new(),
            evidence_tuple_sha256: String::new(),
        }
    }

    fn all_canonical_sha256(&self) -> bool {
        canonical_sha256_bound(&self.manifest_sha256)
            && canonical_sha256_bound(&self.proof_facts_sha256)
            && canonical_sha256_bound(&self.replay_sha256)
            && canonical_sha256_bound(&self.product_gate_sha256)
            && canonical_sha256_bound(&self.evidence_tuple_sha256)
    }
}

/// Private/local sparse affected-row batch status evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYLraSparseAffectedRowBatchEvidence {
    /// Evidence schema.
    pub schema: &'static str,
    /// Evidence schema version.
    pub schema_version: u32,
    /// Observed native-dispatch evidence kind.
    pub evidence_kind: AYLraSolverProgramEvidenceKind,
    /// Publication scope.
    pub scope: AYLraSolverProgramEvidenceScope,
    /// Observed sparse affected-row status facts.
    pub counters: AYLraSparseAffectedRowBatchCounters,
    /// Whether the evidence claims production activation.
    pub production_activation: bool,
    /// Whether the evidence claims publication authority.
    pub publication_claim: bool,
    /// Useful-native counter delta authorized by this local slice.
    pub useful_native_delta: u64,
    /// Canonical hash bindings.
    pub hashes: AYLraSparseAffectedRowBatchEvidenceHashes,
}

impl AYLraSparseAffectedRowBatchEvidence {
    /// Return the private/local sparse affected-row batch observation.
    pub fn private_local() -> Self {
        Self {
            schema: AY_LRA_LOCAL_SOLVER_PROGRAM_EVIDENCE_SCHEMA,
            schema_version: AY_LRA_LOCAL_SOLVER_PROGRAM_EVIDENCE_SCHEMA_VERSION,
            evidence_kind: AYLraSolverProgramEvidenceKind::SolverProgramNative,
            scope: AYLraSolverProgramEvidenceScope::PrivateLocal,
            counters: AYLraSparseAffectedRowBatchCounters::private_local_observed(),
            production_activation: false,
            publication_claim: false,
            useful_native_delta: AY_LRA_SPARSE_AFFECTED_ROW_BATCH_USEFUL_NATIVE_DELTA,
            hashes: AYLraSparseAffectedRowBatchEvidenceHashes::empty(),
        }
    }

    /// Return this evidence with all canonical hash bindings filled in.
    pub fn with_canonical_hashes(
        mut self,
        artifact: &DeterministicArtifactManifest,
        manifest: &AYLraKernelProofConsumptionManifest,
        evidence: &AYLraProofConsumptionEvidence,
    ) -> Self {
        self.hashes = self.canonical_hashes(artifact, manifest, evidence);
        self
    }

    /// Compute canonical hash bindings for the current artifact/manifest/evidence tuple.
    pub fn canonical_hashes(
        &self,
        artifact: &DeterministicArtifactManifest,
        manifest: &AYLraKernelProofConsumptionManifest,
        evidence: &AYLraProofConsumptionEvidence,
    ) -> AYLraSparseAffectedRowBatchEvidenceHashes {
        let manifest_sha256 = ay_lra_sparse_affected_row_batch_manifest_sha256(artifact, manifest);
        let proof_facts_sha256 =
            ay_lra_sparse_affected_row_batch_proof_facts_sha256(manifest, evidence);
        let replay_sha256 = ay_lra_sparse_affected_row_batch_replay_sha256(
            manifest.kernel_family,
            &evidence.replay,
        );
        let product_gate_sha256 = ay_lra_sparse_affected_row_batch_product_gate_sha256(
            manifest.kernel_family,
            &evidence.product_gate,
        );
        let evidence_tuple_sha256 = self.canonical_evidence_tuple_sha256(
            artifact,
            manifest,
            evidence,
            &manifest_sha256,
            &proof_facts_sha256,
            &replay_sha256,
            &product_gate_sha256,
        );

        AYLraSparseAffectedRowBatchEvidenceHashes {
            manifest_sha256,
            proof_facts_sha256,
            replay_sha256,
            product_gate_sha256,
            evidence_tuple_sha256,
        }
    }

    fn binds_private_local_observed_facts(&self) -> bool {
        self.counters == AYLraSparseAffectedRowBatchCounters::private_local_observed()
            && self.counters.rows_attempted() == AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_ATTEMPTED
            && self.counters.total_rows_committed()
                == AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_COMMITTED_TOTAL
            && self.counters.observation_count() == AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OBSERVATIONS
            && self.counters.status_count() == AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OBSERVATIONS
            && self.useful_native_delta == AY_LRA_SPARSE_AFFECTED_ROW_BATCH_USEFUL_NATIVE_DELTA
    }

    fn canonical_evidence_tuple_sha256(
        &self,
        artifact: &DeterministicArtifactManifest,
        manifest: &AYLraKernelProofConsumptionManifest,
        evidence: &AYLraProofConsumptionEvidence,
        manifest_sha256: &str,
        proof_facts_sha256: &str,
        replay_sha256: &str,
        product_gate_sha256: &str,
    ) -> String {
        let mut out = Vec::new();
        put_str(
            &mut out,
            "trust-cg.ay_lra.sparse_affected_row_batch.evidence_tuple.v1",
        );
        put_str(&mut out, self.schema);
        put_u64(&mut out, u64::from(self.schema_version));
        put_str(&mut out, manifest.kernel_family.as_str());
        put_str(&mut out, &artifact.checksum().to_string());
        put_str(&mut out, &evidence.replay.manifest_checksum.to_string());
        put_str(&mut out, self.evidence_kind.as_str());
        put_str(&mut out, self.scope.as_str());
        put_u64(&mut out, self.counters.affected_rows_per_observation);
        put_u64(&mut out, self.counters.row_output_lengths.len() as u64);
        for length in &self.counters.row_output_lengths {
            put_i64(&mut out, *length);
        }
        put_u64(&mut out, self.counters.rows_committed.len() as u64);
        for rows_committed in &self.counters.rows_committed {
            put_u64(&mut out, *rows_committed);
        }
        put_u64(&mut out, self.counters.first_failed_rows.len() as u64);
        for first_failed_row in &self.counters.first_failed_rows {
            put_i64(&mut out, *first_failed_row);
        }
        put_u64(&mut out, self.counters.ok_statuses);
        put_u64(&mut out, self.counters.overflow_statuses);
        put_u64(&mut out, self.counters.bounds_statuses);
        put_u64(&mut out, self.counters.stale_statuses);
        put_u64(&mut out, self.useful_native_delta);
        put_bool(&mut out, self.production_activation);
        put_bool(&mut out, self.publication_claim);
        put_str(&mut out, manifest_sha256);
        put_str(&mut out, proof_facts_sha256);
        put_str(&mut out, replay_sha256);
        put_str(&mut out, product_gate_sha256);
        sha256_digest(&out)
    }
}

/// Counter facts observed for a local basis-row batch telemetry/replay slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AYLraBasisRowBatchTelemetryCounters {
    /// Rows attempted by the batch update.
    pub rows_attempted: u64,
    /// Rows committed before deopt.
    pub rows_committed: u64,
    /// First zero-based row that failed.
    pub first_failed_row: u64,
    /// Basis-epoch stale deopts.
    pub stale_deopts: u64,
    /// Coefficient-overflow deopts.
    pub overflow_deopts: u64,
    /// Partial-row deopts that preserve the committed prefix.
    pub partial_row_deopts: u64,
}

impl AYLraBasisRowBatchTelemetryCounters {
    /// Return the private/local basis-row batch telemetry facts.
    pub const fn private_local_observed() -> Self {
        Self {
            rows_attempted: AY_LRA_BASIS_ROW_BATCH_TELEMETRY_ROWS_ATTEMPTED,
            rows_committed: AY_LRA_BASIS_ROW_BATCH_TELEMETRY_ROWS_COMMITTED,
            first_failed_row: AY_LRA_BASIS_ROW_BATCH_TELEMETRY_FIRST_FAILED_ROW,
            stale_deopts: AY_LRA_BASIS_ROW_BATCH_TELEMETRY_STALE_DEOPTS,
            overflow_deopts: AY_LRA_BASIS_ROW_BATCH_TELEMETRY_OVERFLOW_DEOPTS,
            partial_row_deopts: AY_LRA_BASIS_ROW_BATCH_TELEMETRY_PARTIAL_ROW_DEOPTS,
        }
    }
}

/// Canonical hash bindings for local basis-row batch telemetry/replay evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYLraBasisRowBatchTelemetryEvidenceHashes {
    /// Hash over the bound artifact and proof-consumption manifest identities.
    pub manifest_sha256: String,
    /// Hash over manifest proof facts and attached proof evidence.
    pub proof_facts_sha256: String,
    /// Hash over replay comparison evidence.
    pub replay_sha256: String,
    /// Hash over product-gate evidence.
    pub product_gate_sha256: String,
    /// Hash over the complete local telemetry tuple.
    pub evidence_tuple_sha256: String,
}

impl AYLraBasisRowBatchTelemetryEvidenceHashes {
    fn empty() -> Self {
        Self {
            manifest_sha256: String::new(),
            proof_facts_sha256: String::new(),
            replay_sha256: String::new(),
            product_gate_sha256: String::new(),
            evidence_tuple_sha256: String::new(),
        }
    }

    fn all_canonical_sha256(&self) -> bool {
        canonical_sha256_bound(&self.manifest_sha256)
            && canonical_sha256_bound(&self.proof_facts_sha256)
            && canonical_sha256_bound(&self.replay_sha256)
            && canonical_sha256_bound(&self.product_gate_sha256)
            && canonical_sha256_bound(&self.evidence_tuple_sha256)
    }
}

/// Private/local basis-row batch telemetry and replay evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYLraBasisRowBatchTelemetryEvidence {
    /// Evidence schema.
    pub schema: &'static str,
    /// Evidence schema version.
    pub schema_version: u32,
    /// Observed native-dispatch evidence kind.
    pub evidence_kind: AYLraSolverProgramEvidenceKind,
    /// Publication scope.
    pub scope: AYLraSolverProgramEvidenceScope,
    /// Observed basis-row telemetry facts.
    pub counters: AYLraBasisRowBatchTelemetryCounters,
    /// Whether the evidence claims production activation.
    pub production_activation: bool,
    /// Whether the evidence claims publication authority.
    pub publication_claim: bool,
    /// Useful-native counter delta authorized by this local slice.
    pub useful_native_delta: u64,
    /// Canonical hash bindings.
    pub hashes: AYLraBasisRowBatchTelemetryEvidenceHashes,
}

impl AYLraBasisRowBatchTelemetryEvidence {
    /// Return the private/local basis-row batch telemetry observation.
    pub fn private_local() -> Self {
        Self {
            schema: AY_LRA_LOCAL_SOLVER_PROGRAM_EVIDENCE_SCHEMA,
            schema_version: AY_LRA_LOCAL_SOLVER_PROGRAM_EVIDENCE_SCHEMA_VERSION,
            evidence_kind: AYLraSolverProgramEvidenceKind::SolverProgramNative,
            scope: AYLraSolverProgramEvidenceScope::PrivateLocal,
            counters: AYLraBasisRowBatchTelemetryCounters::private_local_observed(),
            production_activation: false,
            publication_claim: false,
            useful_native_delta: AY_LRA_BASIS_ROW_BATCH_TELEMETRY_USEFUL_NATIVE_DELTA,
            hashes: AYLraBasisRowBatchTelemetryEvidenceHashes::empty(),
        }
    }

    /// Return this evidence with all canonical hash bindings filled in.
    pub fn with_canonical_hashes(
        mut self,
        artifact: &DeterministicArtifactManifest,
        manifest: &AYLraKernelProofConsumptionManifest,
        evidence: &AYLraProofConsumptionEvidence,
    ) -> Self {
        self.hashes = self.canonical_hashes(artifact, manifest, evidence);
        self
    }

    /// Compute canonical hash bindings for the current artifact/manifest/evidence tuple.
    pub fn canonical_hashes(
        &self,
        artifact: &DeterministicArtifactManifest,
        manifest: &AYLraKernelProofConsumptionManifest,
        evidence: &AYLraProofConsumptionEvidence,
    ) -> AYLraBasisRowBatchTelemetryEvidenceHashes {
        let manifest_sha256 = ay_lra_basis_row_batch_telemetry_manifest_sha256(artifact, manifest);
        let proof_facts_sha256 =
            ay_lra_basis_row_batch_telemetry_proof_facts_sha256(manifest, evidence);
        let replay_sha256 = ay_lra_basis_row_batch_telemetry_replay_sha256(
            manifest.kernel_family,
            &evidence.replay,
        );
        let product_gate_sha256 = ay_lra_basis_row_batch_telemetry_product_gate_sha256(
            manifest.kernel_family,
            &evidence.product_gate,
        );
        let evidence_tuple_sha256 = self.canonical_evidence_tuple_sha256(
            artifact,
            manifest,
            evidence,
            &manifest_sha256,
            &proof_facts_sha256,
            &replay_sha256,
            &product_gate_sha256,
        );

        AYLraBasisRowBatchTelemetryEvidenceHashes {
            manifest_sha256,
            proof_facts_sha256,
            replay_sha256,
            product_gate_sha256,
            evidence_tuple_sha256,
        }
    }

    fn binds_private_local_observed_facts(&self) -> bool {
        self.counters == AYLraBasisRowBatchTelemetryCounters::private_local_observed()
            && self.useful_native_delta == AY_LRA_BASIS_ROW_BATCH_TELEMETRY_USEFUL_NATIVE_DELTA
            && self.counters.rows_committed <= self.counters.rows_attempted
            && self.counters.first_failed_row == self.counters.rows_committed
    }

    fn canonical_evidence_tuple_sha256(
        &self,
        artifact: &DeterministicArtifactManifest,
        manifest: &AYLraKernelProofConsumptionManifest,
        evidence: &AYLraProofConsumptionEvidence,
        manifest_sha256: &str,
        proof_facts_sha256: &str,
        replay_sha256: &str,
        product_gate_sha256: &str,
    ) -> String {
        let mut out = Vec::new();
        put_str(
            &mut out,
            "trust-cg.ay_lra.basis_row_batch.telemetry.evidence_tuple.v1",
        );
        put_str(&mut out, self.schema);
        put_u64(&mut out, u64::from(self.schema_version));
        put_str(&mut out, manifest.kernel_family.as_str());
        put_str(&mut out, &artifact.checksum().to_string());
        put_str(&mut out, &evidence.replay.manifest_checksum.to_string());
        put_str(&mut out, self.evidence_kind.as_str());
        put_str(&mut out, self.scope.as_str());
        put_u64(&mut out, self.counters.rows_attempted);
        put_u64(&mut out, self.counters.rows_committed);
        put_u64(&mut out, self.counters.first_failed_row);
        put_u64(&mut out, self.counters.stale_deopts);
        put_u64(&mut out, self.counters.overflow_deopts);
        put_u64(&mut out, self.counters.partial_row_deopts);
        put_u64(&mut out, self.useful_native_delta);
        put_bool(&mut out, self.production_activation);
        put_bool(&mut out, self.publication_claim);
        put_str(&mut out, manifest_sha256);
        put_str(&mut out, proof_facts_sha256);
        put_str(&mut out, replay_sha256);
        put_str(&mut out, product_gate_sha256);
        sha256_digest(&out)
    }
}

/// Sidecar evidence used to emit or reject a ay LRA proof-consumption manifest.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYLraProofConsumptionEvidence {
    /// Existing proof evidence summary bound to the artifact.
    pub proof_evidence: Option<ProofEvidenceSummary>,
    /// Fact evidence keyed by proof fact.
    pub facts: BTreeMap<AYLraProofFact, AYLraEvidenceAvailability>,
    /// Certificate evidence keyed by certificate id.
    pub certificates: BTreeMap<String, AYLraEvidenceAvailability>,
    /// Basis epoch evidence.
    pub basis_epoch: AYLraBasisEpochEvidence,
    /// Replay comparison evidence.
    pub replay: AYLraReplayComparison,
    /// Product gate evidence.
    pub product_gate: AYLraProductGateEvidence,
}

/// Manifest admission disposition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AYLraManifestDisposition {
    /// Manifest can be emitted, subject to product gates.
    EmitManifest,
    /// Manifest must be rejected and remain non-promoting.
    RejectNonPromoting,
}

/// Typed reason for rejecting a ay LRA proof-consumption manifest.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AYLraManifestRejectionReason {
    /// Artifact kernel metadata does not match the proof-consumption manifest.
    UnsupportedKernelFamily,
    /// Manifest identity metadata is missing or does not match the typed manifest.
    ManifestIdentityMetadataMismatch,
    /// Required proof fact metadata is missing or stale.
    RequiredProofMetadataMismatch,
    /// Required certificate metadata is missing or stale.
    RequiredCertificateMetadataMismatch,
    /// Future proof-family status metadata is missing or stale.
    FutureProofStatusMismatch,
    /// Product-gate metadata is missing or stale.
    ProductGateMetadataMismatch,
    /// trust_ir source identity or approved source policy is missing.
    MissingSourceIdentity,
    /// Target, ABI, or LP64 layout does not match the ay LRA AArch64 contract.
    TargetAbiLayoutMismatch,
    /// Invalidation key does not bind target/ABI/layout/proof policy.
    InvalidationMismatch,
    /// Typed status signature binding is missing.
    StatusSignatureMismatch,
    /// Proof policy or proof evidence is missing.
    MissingProofEvidence,
    /// Proof evidence was rejected by the existing artifact contract.
    ProofEvidenceRejected,
    /// Sorted sparse-row proof fact is missing.
    MissingSortedSparseRows,
    /// Entering-variable proof fact is missing.
    MissingEnteringVariable,
    /// Target/pivot alias proof fact is missing.
    MissingTargetPivotAliasPolicy,
    /// Output capacity proof fact is missing.
    MissingOutputCapacityBounds,
    /// Coefficient-overflow proof fact is missing.
    MissingCoefficientOverflow,
    /// Basis epoch is stale or its proof fact is missing.
    StaleBasisEpoch,
    /// Batch prefix commit/rollback proof fact is missing.
    MissingBatchPrefixCommitRollback,
    /// Replay artifacts are missing.
    MissingReplayComparison,
    /// Replay artifacts do not agree with the manifest identity.
    ReplayMismatch,
    /// A required certificate dependency is missing.
    MissingCertificateDependency,
    /// Parent product-gate evidence is missing.
    MissingProductGate,
    /// Local solver-program evidence schema is unsupported.
    SolverProgramEvidenceSchemaMismatch,
    /// Local solver-program evidence kind is not solver-program-native.
    SolverProgramEvidenceKindMismatch,
    /// Local solver-program evidence is not private/local.
    SolverProgramEvidenceScopeMismatch,
    /// Local solver-program observed counter or PAR-2 fact is stale.
    SolverProgramObservedFactMismatch,
    /// Local solver-program PAR-2 regressed against baseline.
    SolverProgramPar2Regression,
    /// Local solver-program evidence claims production or publication authority.
    SolverProgramAuthorityMismatch,
    /// Local solver-program evidence hash binding is stale or malformed.
    SolverProgramEvidenceHashMismatch,
    /// Local perf JSON evidence schema is unsupported.
    PerfJsonEvidenceSchemaMismatch,
    /// Local perf JSON evidence is not private/local.
    PerfJsonEvidenceScopeMismatch,
    /// Local perf JSON report identity or checksum is stale.
    PerfJsonReportIdentityMismatch,
    /// Local perf JSON compile amortization counters are missing or stale.
    PerfJsonCompileAmortizationMissing,
    /// Local perf JSON p50/p95 apply-latency counters are missing or malformed.
    PerfJsonApplyLatencyMissing,
    /// Local perf JSON native apply latency regressed against baseline.
    PerfJsonApplyLatencyRegression,
    /// Local perf JSON evidence claims production or publication authority.
    PerfJsonAuthorityMismatch,
    /// Local perf JSON evidence hash binding is stale or malformed.
    PerfJsonEvidenceHashMismatch,
}

impl AYLraManifestRejectionReason {
    /// Return the stable lower-snake-case reason id.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::UnsupportedKernelFamily => "unsupported_kernel_family",
            Self::ManifestIdentityMetadataMismatch => "manifest_identity_metadata_mismatch",
            Self::RequiredProofMetadataMismatch => "required_proof_metadata_mismatch",
            Self::RequiredCertificateMetadataMismatch => "required_certificate_metadata_mismatch",
            Self::FutureProofStatusMismatch => "future_proof_status_mismatch",
            Self::ProductGateMetadataMismatch => "product_gate_metadata_mismatch",
            Self::MissingSourceIdentity => "missing_source_identity",
            Self::TargetAbiLayoutMismatch => "target_abi_layout_mismatch",
            Self::InvalidationMismatch => "invalidation_mismatch",
            Self::StatusSignatureMismatch => "status_signature_mismatch",
            Self::MissingProofEvidence => "missing_proof_evidence",
            Self::ProofEvidenceRejected => "proof_evidence_rejected",
            Self::MissingSortedSparseRows => "missing_sorted_sparse_rows",
            Self::MissingEnteringVariable => "missing_entering_variable",
            Self::MissingTargetPivotAliasPolicy => "missing_target_pivot_alias_policy",
            Self::MissingOutputCapacityBounds => "missing_output_capacity_bounds",
            Self::MissingCoefficientOverflow => "missing_coefficient_overflow",
            Self::StaleBasisEpoch => "stale_basis_epoch",
            Self::MissingBatchPrefixCommitRollback => "missing_batch_prefix_commit_rollback",
            Self::MissingReplayComparison => "missing_replay_comparison",
            Self::ReplayMismatch => "replay_mismatch",
            Self::MissingCertificateDependency => "missing_certificate_dependency",
            Self::MissingProductGate => "missing_product_gate",
            Self::SolverProgramEvidenceSchemaMismatch => "solver_program_evidence_schema_mismatch",
            Self::SolverProgramEvidenceKindMismatch => "solver_program_evidence_kind_mismatch",
            Self::SolverProgramEvidenceScopeMismatch => "solver_program_evidence_scope_mismatch",
            Self::SolverProgramObservedFactMismatch => "solver_program_observed_fact_mismatch",
            Self::SolverProgramPar2Regression => "solver_program_par2_regression",
            Self::SolverProgramAuthorityMismatch => "solver_program_authority_mismatch",
            Self::SolverProgramEvidenceHashMismatch => "solver_program_evidence_hash_mismatch",
            Self::PerfJsonEvidenceSchemaMismatch => "perf_json_evidence_schema_mismatch",
            Self::PerfJsonEvidenceScopeMismatch => "perf_json_evidence_scope_mismatch",
            Self::PerfJsonReportIdentityMismatch => "perf_json_report_identity_mismatch",
            Self::PerfJsonCompileAmortizationMissing => "perf_json_compile_amortization_missing",
            Self::PerfJsonApplyLatencyMissing => "perf_json_apply_latency_missing",
            Self::PerfJsonApplyLatencyRegression => "perf_json_apply_latency_regression",
            Self::PerfJsonAuthorityMismatch => "perf_json_authority_mismatch",
            Self::PerfJsonEvidenceHashMismatch => "perf_json_evidence_hash_mismatch",
        }
    }
}

/// Structured diagnostic for one required proof metadata mismatch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYLraProofMetadataMismatchDetail {
    /// Proof evidence metadata key that was checked.
    pub key: String,
    /// Lemma/checker id required by the manifest.
    pub expected: &'static str,
    /// Lemma/checker id found in proof evidence, if present.
    pub actual: Option<String>,
}

/// Admission decision for one ay LRA proof-consumption manifest.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYLraManifestAdmission {
    /// Disposition.
    pub disposition: AYLraManifestDisposition,
    /// Typed rejection reasons.
    pub reasons: Vec<AYLraManifestRejectionReason>,
    /// Structured per-fact metadata mismatch diagnostics.
    pub proof_metadata_mismatch_details: Vec<AYLraProofMetadataMismatchDetail>,
    /// Whether the decision remains non-promoting.
    pub non_promoting: bool,
    /// Bound artifact manifest checksum.
    pub manifest_checksum: ArtifactChecksum,
    /// Useful-native counter delta authorized by this admission decision.
    pub useful_native_delta: u64,
}

/// Narrow native AArch64 lowering kind admitted by the ay LRA selector.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AYLraAarch64LoweringKind {
    /// ay LRA sparse-substitute lowering.
    SparseSubstitute,
    /// ay LRA sparse affected-row batch status lowering.
    SparseAffectedRowBatch,
    /// ay LRA basis-row batch lowering.
    BasisRowBatch,
}

impl AYLraAarch64LoweringKind {
    /// Return the stable lower-snake-case lowering id.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::SparseSubstitute => "sparse_substitute",
            Self::SparseAffectedRowBatch => "sparse_affected_row_batch",
            Self::BasisRowBatch => "basis_row_batch",
        }
    }
}

/// Non-promoting AArch64 lowering selector decision for ay LRA.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AYLraAarch64LoweringDecision {
    /// The native lowering slice may be used, but remains non-promoting.
    UseNative {
        /// Selected lowering kind.
        kind: AYLraAarch64LoweringKind,
        /// Manifest admission evidence supporting the decision.
        admission: AYLraManifestAdmission,
    },
    /// Native lowering is rejected and product behavior must remain baseline-only.
    RejectNonPromoting {
        /// Manifest admission evidence and rejection reasons.
        admission: AYLraManifestAdmission,
    },
}

impl AYLraAarch64LoweringDecision {
    /// Return the admission record attached to this selector decision.
    pub const fn admission(&self) -> &AYLraManifestAdmission {
        match self {
            Self::UseNative { admission, .. } | Self::RejectNonPromoting { admission } => admission,
        }
    }

    /// Return true when this selector chose a native lowering slice.
    pub const fn is_use_native(&self) -> bool {
        matches!(self, Self::UseNative { .. })
    }

    /// Useful-native counter delta authorized by this selector decision.
    pub const fn useful_native_delta(&self) -> u64 {
        self.admission().useful_native_delta
    }
}

/// Build the sparse-substitute proof-consumption manifest.
pub fn ay_lra_sparse_substitute_proof_manifest() -> AYLraKernelProofConsumptionManifest {
    lra_manifest(
        AYLraKernelFamily::SparseSubstitute,
        AYLraProofFamily::LraSparseSubstitute,
        &[
            (
                AYLraProofFact::SortedSparseRows,
                "ay_lra_sparse.sorted_rows_strict_order",
            ),
            (
                AYLraProofFact::EnteringVariable,
                "ay_lra_sparse.entering_variable_in_basis_frontier",
            ),
            (
                AYLraProofFact::TargetPivotAliasPolicy,
                "ay_lra_sparse.target_pivot_alias_exclusive_or_readonly",
            ),
            (
                AYLraProofFact::OutputCapacityBounds,
                "ay_lra_sparse.output_capacity_bounds",
            ),
            (
                AYLraProofFact::CoefficientOverflow,
                "ay_lra_sparse.coefficient_update_no_overflow",
            ),
            (
                AYLraProofFact::BasisEpochFreshness,
                "ay_lra_sparse.basis_epoch_fresh",
            ),
        ],
        &[
            "ay-lra-sparse-substitute-row-order",
            "ay-lra-sparse-output-bounds",
            "ay-lra-sparse-overflow",
            "ay-lra-sparse-alias-policy",
            "ay-lra-basis-epoch",
        ],
    )
}

/// Build the sparse affected-row batch proof-consumption manifest.
pub fn ay_lra_sparse_affected_row_batch_proof_manifest() -> AYLraKernelProofConsumptionManifest {
    lra_manifest(
        AYLraKernelFamily::SparseAffectedRowBatch,
        AYLraProofFamily::LraSparseAffectedRowBatch,
        &[
            (
                AYLraProofFact::SortedSparseRows,
                "ay_lra_sparse_affected_batch.sorted_rows_strict_order",
            ),
            (
                AYLraProofFact::EnteringVariable,
                "ay_lra_sparse_affected_batch.entering_variable_in_basis_frontier",
            ),
            (
                AYLraProofFact::TargetPivotAliasPolicy,
                "ay_lra_sparse_affected_batch.target_pivot_alias_exclusive_or_readonly",
            ),
            (
                AYLraProofFact::OutputCapacityBounds,
                "ay_lra_sparse_affected_batch.output_capacity_bounds",
            ),
            (
                AYLraProofFact::CoefficientOverflow,
                "ay_lra_sparse_affected_batch.coefficient_update_no_overflow",
            ),
            (
                AYLraProofFact::BasisEpochFreshness,
                "ay_lra_sparse_affected_batch.basis_epoch_fresh",
            ),
        ],
        &[
            "ay-lra-sparse-affected-row-batch-row-order",
            "ay-lra-sparse-affected-row-batch-output-bounds",
            "ay-lra-sparse-affected-row-batch-overflow",
            "ay-lra-sparse-affected-row-batch-alias-policy",
            "ay-lra-sparse-affected-row-batch-basis-epoch",
        ],
    )
}

/// Build the basis-update proof-consumption manifest.
pub fn ay_lra_basis_update_proof_manifest() -> AYLraKernelProofConsumptionManifest {
    lra_manifest(
        AYLraKernelFamily::BasisUpdate,
        AYLraProofFamily::LraBasisUpdate,
        &[
            (
                AYLraProofFact::SortedSparseRows,
                "ay_lra_basis.sorted_tableau_rows",
            ),
            (
                AYLraProofFact::EnteringVariable,
                "ay_lra_basis.entering_variable_matches_basis_update",
            ),
            (
                AYLraProofFact::TargetPivotAliasPolicy,
                "ay_lra_basis.target_pivot_alias_exclusive_or_readonly",
            ),
            (
                AYLraProofFact::OutputCapacityBounds,
                "ay_lra_basis.output_capacity_bounds",
            ),
            (
                AYLraProofFact::CoefficientOverflow,
                "ay_lra_basis.coefficient_update_no_overflow",
            ),
            (
                AYLraProofFact::BasisEpochFreshness,
                "ay_lra_basis.basis_epoch_fresh",
            ),
            (
                AYLraProofFact::BatchPrefixCommitRollback,
                "ay_lra_basis.batch_prefix_commit_rollback",
            ),
        ],
        &[
            "ay-lra-basis-sorted-rows",
            "ay-lra-basis-output-bounds",
            "ay-lra-basis-overflow",
            "ay-lra-basis-alias-policy",
            "ay-lra-basis-epoch",
            "ay-lra-basis-prefix-rollback",
        ],
    )
}

/// Evaluate one artifact plus evidence against a ay LRA proof-consumption manifest.
pub fn evaluate_ay_lra_manifest_admission(
    artifact: &DeterministicArtifactManifest,
    manifest: &AYLraKernelProofConsumptionManifest,
    evidence: &AYLraProofConsumptionEvidence,
) -> AYLraManifestAdmission {
    let mut reasons = Vec::new();
    let mut proof_metadata_mismatch_details = Vec::new();
    let proof_evidence = evidence.proof_evidence.as_ref();

    push_if(
        &mut reasons,
        !kernel_metadata_matches(artifact, manifest.kernel_family),
        AYLraManifestRejectionReason::UnsupportedKernelFamily,
    );
    push_manifest_metadata_rejections(&mut reasons, artifact, manifest, proof_evidence);
    push_if(
        &mut reasons,
        !source_policy_bound(artifact, proof_evidence),
        AYLraManifestRejectionReason::MissingSourceIdentity,
    );
    push_if(
        &mut reasons,
        !aarch64_lp64_layout_bound(artifact),
        AYLraManifestRejectionReason::TargetAbiLayoutMismatch,
    );
    push_if(
        &mut reasons,
        !invalidation_binds_current_artifact(artifact),
        AYLraManifestRejectionReason::InvalidationMismatch,
    );
    push_if(
        &mut reasons,
        !status_signature_bound(artifact, manifest.kernel_family),
        AYLraManifestRejectionReason::StatusSignatureMismatch,
    );
    push_if(
        &mut reasons,
        !matches!(
            &artifact.proof_policy.mode,
            ProofMode::RequireCertificates | ProofMode::RequireReplay
        ),
        AYLraManifestRejectionReason::MissingProofEvidence,
    );

    match proof_evidence {
        Some(proof_evidence) if artifact.verify_proof_evidence(proof_evidence).is_ok() => {}
        Some(_) => push_unique(
            &mut reasons,
            AYLraManifestRejectionReason::ProofEvidenceRejected,
        ),
        None => push_unique(
            &mut reasons,
            AYLraManifestRejectionReason::MissingProofEvidence,
        ),
    }

    for requirement in &manifest.required_facts {
        let fact_available = evidence
            .facts
            .get(&requirement.fact)
            .copied()
            .unwrap_or(AYLraEvidenceAvailability::Missing)
            .is_available();
        if !fact_available {
            push_unique(&mut reasons, rejection_for_fact(requirement.fact));
        } else if let Some(detail) =
            proof_fact_metadata_mismatch_detail(proof_evidence, requirement)
        {
            push_unique(
                &mut reasons,
                AYLraManifestRejectionReason::RequiredProofMetadataMismatch,
            );
            proof_metadata_mismatch_details.push(detail);
            push_unique(&mut reasons, rejection_for_fact(requirement.fact));
        }
    }

    if !basis_epoch_fresh_for_artifact(artifact, evidence.basis_epoch) {
        push_unique(&mut reasons, AYLraManifestRejectionReason::StaleBasisEpoch);
    }

    let replay_has_all_digests = !missing_required_text(&evidence.replay.replay_root_sha256)
        && !missing_required_text(&evidence.replay.generic_behavior_sha256)
        && !missing_required_text(&evidence.replay.specialized_behavior_sha256)
        && !missing_required_text(&evidence.replay.reference_behavior_sha256);
    push_if(
        &mut reasons,
        !replay_has_all_digests,
        AYLraManifestRejectionReason::MissingReplayComparison,
    );
    push_if(
        &mut reasons,
        replay_has_all_digests
            && !evidence
                .replay
                .compares(artifact.checksum(), manifest.kernel_family),
        AYLraManifestRejectionReason::ReplayMismatch,
    );

    for dependency in &manifest.certificate_dependencies {
        if dependency.availability == AYLraRequirementAvailability::RequiredForAdmission
            && !evidence
                .certificates
                .get(dependency.id)
                .copied()
                .unwrap_or(AYLraEvidenceAvailability::Missing)
                .is_available()
        {
            push_unique(
                &mut reasons,
                AYLraManifestRejectionReason::MissingCertificateDependency,
            );
        }
    }

    push_if(
        &mut reasons,
        !evidence.product_gate.is_complete(manifest.kernel_family),
        AYLraManifestRejectionReason::MissingProductGate,
    );

    let disposition = if reasons.is_empty() {
        AYLraManifestDisposition::EmitManifest
    } else {
        AYLraManifestDisposition::RejectNonPromoting
    };
    AYLraManifestAdmission {
        disposition,
        reasons,
        proof_metadata_mismatch_details,
        non_promoting: disposition == AYLraManifestDisposition::RejectNonPromoting
            || manifest
                .product_gate
                .baseline_authoritative_until_product_gate,
        manifest_checksum: artifact.checksum(),
        useful_native_delta: 0,
    }
}

/// Evaluate private/local sparse-substitute solver-program evidence as a
/// non-promoting manifest-evidence slice.
pub fn evaluate_ay_lra_sparse_substitute_solver_program_evidence(
    artifact: &DeterministicArtifactManifest,
    manifest: &AYLraKernelProofConsumptionManifest,
    evidence: &AYLraProofConsumptionEvidence,
    solver_program_evidence: &AYLraSparseSubstituteSolverProgramEvidence,
) -> AYLraManifestAdmission {
    let mut admission = evaluate_ay_lra_manifest_admission(artifact, manifest, evidence);

    push_if(
        &mut admission.reasons,
        manifest.kernel_family != AYLraKernelFamily::SparseSubstitute,
        AYLraManifestRejectionReason::UnsupportedKernelFamily,
    );
    push_if(
        &mut admission.reasons,
        solver_program_evidence.schema != AY_LRA_LOCAL_SOLVER_PROGRAM_EVIDENCE_SCHEMA
            || solver_program_evidence.schema_version
                != AY_LRA_LOCAL_SOLVER_PROGRAM_EVIDENCE_SCHEMA_VERSION,
        AYLraManifestRejectionReason::SolverProgramEvidenceSchemaMismatch,
    );
    push_if(
        &mut admission.reasons,
        solver_program_evidence.evidence_kind
            != AYLraSolverProgramEvidenceKind::SolverProgramNative,
        AYLraManifestRejectionReason::SolverProgramEvidenceKindMismatch,
    );
    push_if(
        &mut admission.reasons,
        solver_program_evidence.scope != AYLraSolverProgramEvidenceScope::PrivateLocal,
        AYLraManifestRejectionReason::SolverProgramEvidenceScopeMismatch,
    );
    push_if(
        &mut admission.reasons,
        !solver_program_evidence.binds_packet1_observed_facts(),
        AYLraManifestRejectionReason::SolverProgramObservedFactMismatch,
    );
    push_if(
        &mut admission.reasons,
        solver_program_evidence.has_par2_regression(),
        AYLraManifestRejectionReason::SolverProgramPar2Regression,
    );
    push_if(
        &mut admission.reasons,
        solver_program_evidence.production_activation || solver_program_evidence.publication_claim,
        AYLraManifestRejectionReason::SolverProgramAuthorityMismatch,
    );

    let canonical_hashes = solver_program_evidence.canonical_hashes(manifest, evidence);
    push_if(
        &mut admission.reasons,
        !solver_program_evidence.hashes.all_canonical_sha256()
            || solver_program_evidence.hashes != canonical_hashes,
        AYLraManifestRejectionReason::SolverProgramEvidenceHashMismatch,
    );

    if !admission.reasons.is_empty() {
        admission.disposition = AYLraManifestDisposition::RejectNonPromoting;
    }
    admission.non_promoting = true;
    admission.useful_native_delta = 0;
    admission
}

/// Evaluate private/local sparse-substitute perf JSON evidence as a
/// non-promoting manifest-evidence slice.
pub fn evaluate_ay_lra_sparse_substitute_perf_json_evidence(
    artifact: &DeterministicArtifactManifest,
    manifest: &AYLraKernelProofConsumptionManifest,
    evidence: &AYLraProofConsumptionEvidence,
    perf_json_evidence: &AYLraSparseSubstitutePerfJsonEvidence,
) -> AYLraManifestAdmission {
    let mut admission = evaluate_ay_lra_manifest_admission(artifact, manifest, evidence);

    push_if(
        &mut admission.reasons,
        manifest.kernel_family != AYLraKernelFamily::SparseSubstitute,
        AYLraManifestRejectionReason::UnsupportedKernelFamily,
    );
    push_if(
        &mut admission.reasons,
        perf_json_evidence.schema != AY_LRA_LOCAL_PERF_JSON_EVIDENCE_SCHEMA
            || perf_json_evidence.schema_version != AY_LRA_LOCAL_PERF_JSON_EVIDENCE_SCHEMA_VERSION,
        AYLraManifestRejectionReason::PerfJsonEvidenceSchemaMismatch,
    );
    push_if(
        &mut admission.reasons,
        perf_json_evidence.scope != AYLraSolverProgramEvidenceScope::PrivateLocal,
        AYLraManifestRejectionReason::PerfJsonEvidenceScopeMismatch,
    );
    push_if(
        &mut admission.reasons,
        !perf_json_evidence.report_identity_bound(),
        AYLraManifestRejectionReason::PerfJsonReportIdentityMismatch,
    );
    push_if(
        &mut admission.reasons,
        !perf_json_evidence
            .compile_amortization
            .binds_current_private_report(),
        AYLraManifestRejectionReason::PerfJsonCompileAmortizationMissing,
    );
    push_if(
        &mut admission.reasons,
        !perf_json_evidence.apply_latency.has_p50_p95_apply_latency(),
        AYLraManifestRejectionReason::PerfJsonApplyLatencyMissing,
    );
    push_if(
        &mut admission.reasons,
        perf_json_evidence
            .apply_latency
            .has_native_apply_latency_regression(),
        AYLraManifestRejectionReason::PerfJsonApplyLatencyRegression,
    );
    push_if(
        &mut admission.reasons,
        perf_json_evidence.production_activation
            || perf_json_evidence.publication_claim
            || perf_json_evidence.useful_native_delta != 0,
        AYLraManifestRejectionReason::PerfJsonAuthorityMismatch,
    );

    let canonical_hashes = perf_json_evidence.canonical_hashes(artifact, manifest, evidence);
    push_if(
        &mut admission.reasons,
        !perf_json_evidence.hashes.all_canonical_sha256()
            || perf_json_evidence.hashes != canonical_hashes,
        AYLraManifestRejectionReason::PerfJsonEvidenceHashMismatch,
    );

    if !admission.reasons.is_empty() {
        admission.disposition = AYLraManifestDisposition::RejectNonPromoting;
    }
    admission.non_promoting = true;
    admission.useful_native_delta = 0;
    admission
}

/// Evaluate private/local sparse affected-row batch status evidence as a
/// non-promoting manifest-evidence slice.
pub fn evaluate_ay_lra_sparse_affected_row_batch_evidence(
    artifact: &DeterministicArtifactManifest,
    manifest: &AYLraKernelProofConsumptionManifest,
    evidence: &AYLraProofConsumptionEvidence,
    affected_row_evidence: &AYLraSparseAffectedRowBatchEvidence,
) -> AYLraManifestAdmission {
    let mut admission = evaluate_ay_lra_manifest_admission(artifact, manifest, evidence);

    push_if(
        &mut admission.reasons,
        manifest.kernel_family != AYLraKernelFamily::SparseAffectedRowBatch,
        AYLraManifestRejectionReason::UnsupportedKernelFamily,
    );
    push_if(
        &mut admission.reasons,
        !sparse_affected_row_batch_manifest_identity_bound(manifest),
        AYLraManifestRejectionReason::ManifestIdentityMetadataMismatch,
    );
    push_if(
        &mut admission.reasons,
        !sparse_affected_row_batch_source_identity_bound(
            artifact,
            evidence.proof_evidence.as_ref(),
        ),
        AYLraManifestRejectionReason::MissingSourceIdentity,
    );
    push_if(
        &mut admission.reasons,
        !sparse_affected_row_batch_layout_bound(artifact),
        AYLraManifestRejectionReason::TargetAbiLayoutMismatch,
    );
    push_if(
        &mut admission.reasons,
        !sparse_affected_row_batch_invalidation_bound(artifact),
        AYLraManifestRejectionReason::InvalidationMismatch,
    );
    push_if(
        &mut admission.reasons,
        affected_row_evidence.schema != AY_LRA_LOCAL_SOLVER_PROGRAM_EVIDENCE_SCHEMA
            || affected_row_evidence.schema_version
                != AY_LRA_LOCAL_SOLVER_PROGRAM_EVIDENCE_SCHEMA_VERSION,
        AYLraManifestRejectionReason::SolverProgramEvidenceSchemaMismatch,
    );
    push_if(
        &mut admission.reasons,
        affected_row_evidence.evidence_kind != AYLraSolverProgramEvidenceKind::SolverProgramNative,
        AYLraManifestRejectionReason::SolverProgramEvidenceKindMismatch,
    );
    push_if(
        &mut admission.reasons,
        affected_row_evidence.scope != AYLraSolverProgramEvidenceScope::PrivateLocal,
        AYLraManifestRejectionReason::SolverProgramEvidenceScopeMismatch,
    );
    push_if(
        &mut admission.reasons,
        !affected_row_evidence.binds_private_local_observed_facts(),
        AYLraManifestRejectionReason::SolverProgramObservedFactMismatch,
    );
    push_if(
        &mut admission.reasons,
        affected_row_evidence.production_activation || affected_row_evidence.publication_claim,
        AYLraManifestRejectionReason::SolverProgramAuthorityMismatch,
    );

    let canonical_hashes = affected_row_evidence.canonical_hashes(artifact, manifest, evidence);
    push_if(
        &mut admission.reasons,
        !affected_row_evidence.hashes.all_canonical_sha256()
            || affected_row_evidence.hashes != canonical_hashes,
        AYLraManifestRejectionReason::SolverProgramEvidenceHashMismatch,
    );

    if !admission.reasons.is_empty() {
        admission.disposition = AYLraManifestDisposition::RejectNonPromoting;
    }
    admission.non_promoting = true;
    admission.useful_native_delta = 0;
    admission
}

/// Evaluate private/local basis-row batch telemetry/replay evidence as a
/// non-promoting manifest-evidence slice.
pub fn evaluate_ay_lra_basis_row_batch_telemetry_evidence(
    artifact: &DeterministicArtifactManifest,
    manifest: &AYLraKernelProofConsumptionManifest,
    evidence: &AYLraProofConsumptionEvidence,
    telemetry_evidence: &AYLraBasisRowBatchTelemetryEvidence,
) -> AYLraManifestAdmission {
    let mut admission = evaluate_ay_lra_manifest_admission(artifact, manifest, evidence);

    push_if(
        &mut admission.reasons,
        manifest.kernel_family != AYLraKernelFamily::BasisUpdate,
        AYLraManifestRejectionReason::UnsupportedKernelFamily,
    );
    push_if(
        &mut admission.reasons,
        telemetry_evidence.schema != AY_LRA_LOCAL_SOLVER_PROGRAM_EVIDENCE_SCHEMA
            || telemetry_evidence.schema_version
                != AY_LRA_LOCAL_SOLVER_PROGRAM_EVIDENCE_SCHEMA_VERSION,
        AYLraManifestRejectionReason::SolverProgramEvidenceSchemaMismatch,
    );
    push_if(
        &mut admission.reasons,
        telemetry_evidence.evidence_kind != AYLraSolverProgramEvidenceKind::SolverProgramNative,
        AYLraManifestRejectionReason::SolverProgramEvidenceKindMismatch,
    );
    push_if(
        &mut admission.reasons,
        telemetry_evidence.scope != AYLraSolverProgramEvidenceScope::PrivateLocal,
        AYLraManifestRejectionReason::SolverProgramEvidenceScopeMismatch,
    );
    push_if(
        &mut admission.reasons,
        !telemetry_evidence.binds_private_local_observed_facts(),
        AYLraManifestRejectionReason::SolverProgramObservedFactMismatch,
    );
    push_if(
        &mut admission.reasons,
        telemetry_evidence.production_activation || telemetry_evidence.publication_claim,
        AYLraManifestRejectionReason::SolverProgramAuthorityMismatch,
    );

    let canonical_hashes = telemetry_evidence.canonical_hashes(artifact, manifest, evidence);
    push_if(
        &mut admission.reasons,
        !telemetry_evidence.hashes.all_canonical_sha256()
            || telemetry_evidence.hashes != canonical_hashes,
        AYLraManifestRejectionReason::SolverProgramEvidenceHashMismatch,
    );

    if !admission.reasons.is_empty() {
        admission.disposition = AYLraManifestDisposition::RejectNonPromoting;
    }
    admission.non_promoting = true;
    admission.useful_native_delta = 0;
    admission
}

/// Select the first certificate-driven ay LRA AArch64 lowering slice.
///
/// This selector is intentionally fail-closed and non-promoting. It can only
/// choose a native lowering slice after the generic manifest admission succeeds
/// and the family-specific source, layout, invalidation, replay, product-gate,
/// and status bindings are all current.
pub fn select_ay_lra_aarch64_lowering(
    artifact: &DeterministicArtifactManifest,
    manifest: &AYLraKernelProofConsumptionManifest,
    evidence: &AYLraProofConsumptionEvidence,
) -> AYLraAarch64LoweringDecision {
    let mut admission = evaluate_ay_lra_manifest_admission(artifact, manifest, evidence);
    let selected_kind = match manifest.kernel_family {
        AYLraKernelFamily::SparseSubstitute => {
            push_sparse_substitute_selector_rejections(
                &mut admission.reasons,
                artifact,
                manifest,
                evidence,
            );
            AYLraAarch64LoweringKind::SparseSubstitute
        }
        AYLraKernelFamily::SparseAffectedRowBatch => {
            push_sparse_affected_row_batch_selector_rejections(
                &mut admission.reasons,
                artifact,
                manifest,
                evidence,
            );
            AYLraAarch64LoweringKind::SparseAffectedRowBatch
        }
        AYLraKernelFamily::BasisUpdate => {
            push_basis_row_batch_selector_rejections(
                &mut admission.reasons,
                artifact,
                manifest,
                evidence,
            );
            AYLraAarch64LoweringKind::BasisRowBatch
        }
    };
    push_if(
        &mut admission.reasons,
        !admission.non_promoting || admission.useful_native_delta != 0,
        AYLraManifestRejectionReason::ProductGateMetadataMismatch,
    );

    if admission.disposition == AYLraManifestDisposition::EmitManifest
        && admission.reasons.is_empty()
        && admission.non_promoting
        && admission.useful_native_delta == 0
    {
        AYLraAarch64LoweringDecision::UseNative {
            kind: selected_kind,
            admission,
        }
    } else {
        admission.disposition = AYLraManifestDisposition::RejectNonPromoting;
        admission.non_promoting = true;
        admission.useful_native_delta = 0;
        AYLraAarch64LoweringDecision::RejectNonPromoting { admission }
    }
}

fn lra_manifest(
    kernel_family: AYLraKernelFamily,
    proof_family: AYLraProofFamily,
    required: &[(AYLraProofFact, &'static str)],
    certificates: &[&'static str],
) -> AYLraKernelProofConsumptionManifest {
    let mut required_facts: Vec<_> = required
        .iter()
        .map(|(fact, lemma_id)| required_requirement(proof_family, *fact, lemma_id))
        .collect();
    required_facts.extend([
        required_requirement(
            proof_family,
            AYLraProofFact::SourceIdentityLocks,
            "trust_cg_ay_lra.source_identity_policy_bound",
        ),
        required_requirement(
            proof_family,
            AYLraProofFact::Aarch64AbiLayout,
            "trust_cg_ay_lra.aarch64_abi_layout_bound",
        ),
        required_requirement(
            proof_family,
            AYLraProofFact::StatusSignature,
            "trust_cg_ay_lra.status_signature_bound",
        ),
        required_requirement(
            proof_family,
            AYLraProofFact::ProofPolicyChecksum,
            "trust_cg_ay_lra.proof_policy_checksum_bound",
        ),
        required_requirement(
            proof_family,
            AYLraProofFact::ReplayComparison,
            "trust_cg_ay_lra.replay_generic_specialized_reference_equal",
        ),
    ]);

    let future_facts = vec![
        future_requirement(
            AYLraProofFamily::SatCandidateLoop,
            AYLraProofFact::SatCandidateLoopProof,
            "ay_sat.candidate_loop_replay_future",
        ),
        future_requirement(
            AYLraProofFamily::ChcCandidateLoop,
            AYLraProofFact::ChcCandidateLoopProof,
            "ay_chc.candidate_loop_replay_future",
        ),
        future_requirement(
            AYLraProofFamily::PbCandidateLoop,
            AYLraProofFact::PbCandidateLoopProof,
            "ay_pb.candidate_loop_replay_future",
        ),
    ];

    let mut certificate_dependencies: Vec<_> = certificates
        .iter()
        .map(|id| AYLraCertificateDependency {
            id,
            family: proof_family,
            availability: AYLraRequirementAvailability::RequiredForAdmission,
            blocker: None,
        })
        .collect();
    certificate_dependencies.extend([
        AYLraCertificateDependency {
            id: "ay-sat-candidate-loop-proof",
            family: AYLraProofFamily::SatCandidateLoop,
            availability: AYLraRequirementAvailability::MissingFuture,
            blocker: Some("future-sat-candidate-loop-lane"),
        },
        AYLraCertificateDependency {
            id: "ay-chc-candidate-loop-proof",
            family: AYLraProofFamily::ChcCandidateLoop,
            availability: AYLraRequirementAvailability::MissingFuture,
            blocker: Some("future-chc-candidate-loop-lane"),
        },
        AYLraCertificateDependency {
            id: "ay-pb-candidate-loop-proof",
            family: AYLraProofFamily::PbCandidateLoop,
            availability: AYLraRequirementAvailability::MissingFuture,
            blocker: Some("future-pb-candidate-loop-lane"),
        },
    ]);

    AYLraKernelProofConsumptionManifest {
        schema: AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA,
        schema_version: AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA_VERSION,
        issue: AY_LRA_PROOF_CONSUMPTION_MANIFEST_ISSUE,
        kernel_family,
        admission_preconditions: required_facts
            .iter()
            .map(|requirement| requirement.fact)
            .collect(),
        required_facts,
        future_facts,
        certificate_dependencies,
        product_gate: AYLraProductGateFields {
            consumer: "ay",
            surface: "ay_registry",
            allowlist_family: kernel_family.as_str(),
            required_parent_gates: vec![
                "native_install_gate_packet",
                "ay_consumer_admission",
                "manifest_replay_identity",
                "useful_native_telemetry_record",
            ],
            telemetry_counter_policy: "metadata_only_useful_native_false",
            useful_native_eligible: false,
            baseline_authoritative_until_product_gate: true,
        },
    }
}

fn push_sparse_affected_row_batch_selector_rejections(
    reasons: &mut Vec<AYLraManifestRejectionReason>,
    artifact: &DeterministicArtifactManifest,
    manifest: &AYLraKernelProofConsumptionManifest,
    evidence: &AYLraProofConsumptionEvidence,
) {
    let proof_evidence = evidence.proof_evidence.as_ref();
    push_if(
        reasons,
        manifest.kernel_family != AYLraKernelFamily::SparseAffectedRowBatch,
        AYLraManifestRejectionReason::UnsupportedKernelFamily,
    );
    push_if(
        reasons,
        !sparse_affected_row_batch_manifest_identity_bound(manifest),
        AYLraManifestRejectionReason::ManifestIdentityMetadataMismatch,
    );
    push_if(
        reasons,
        !sparse_affected_row_batch_source_identity_bound(artifact, proof_evidence),
        AYLraManifestRejectionReason::MissingSourceIdentity,
    );
    push_if(
        reasons,
        !sparse_affected_row_batch_layout_bound(artifact),
        AYLraManifestRejectionReason::TargetAbiLayoutMismatch,
    );
    push_if(
        reasons,
        !sparse_affected_row_batch_invalidation_bound(artifact),
        AYLraManifestRejectionReason::InvalidationMismatch,
    );
    push_if(
        reasons,
        !replay_hashes_bound(&evidence.replay, manifest.kernel_family),
        AYLraManifestRejectionReason::ReplayMismatch,
    );
    push_if(
        reasons,
        !product_gate_hashes_bound(&evidence.product_gate, manifest.kernel_family),
        AYLraManifestRejectionReason::MissingProductGate,
    );
}

fn push_basis_row_batch_selector_rejections(
    reasons: &mut Vec<AYLraManifestRejectionReason>,
    artifact: &DeterministicArtifactManifest,
    manifest: &AYLraKernelProofConsumptionManifest,
    evidence: &AYLraProofConsumptionEvidence,
) {
    let proof_evidence = evidence.proof_evidence.as_ref();
    push_if(
        reasons,
        manifest.kernel_family != AYLraKernelFamily::BasisUpdate,
        AYLraManifestRejectionReason::UnsupportedKernelFamily,
    );
    push_if(
        reasons,
        !basis_row_batch_manifest_identity_bound(manifest),
        AYLraManifestRejectionReason::ManifestIdentityMetadataMismatch,
    );
    push_if(
        reasons,
        !basis_row_batch_source_identity_bound(artifact, proof_evidence),
        AYLraManifestRejectionReason::MissingSourceIdentity,
    );
    push_if(
        reasons,
        !basis_row_batch_manifest_declares_prefix_rollback(manifest),
        AYLraManifestRejectionReason::MissingBatchPrefixCommitRollback,
    );
    push_if(
        reasons,
        !basis_row_batch_manifest_declares_prefix_rollback_certificate(manifest),
        AYLraManifestRejectionReason::MissingCertificateDependency,
    );
    push_if(
        reasons,
        !basis_row_batch_layout_bound(artifact),
        AYLraManifestRejectionReason::TargetAbiLayoutMismatch,
    );
    push_if(
        reasons,
        !basis_row_batch_invalidation_bound(artifact),
        AYLraManifestRejectionReason::InvalidationMismatch,
    );
    push_if(
        reasons,
        !replay_hashes_bound(&evidence.replay, manifest.kernel_family),
        AYLraManifestRejectionReason::ReplayMismatch,
    );
    push_if(
        reasons,
        !product_gate_hashes_bound(&evidence.product_gate, manifest.kernel_family),
        AYLraManifestRejectionReason::MissingProductGate,
    );
}

fn push_sparse_substitute_selector_rejections(
    reasons: &mut Vec<AYLraManifestRejectionReason>,
    artifact: &DeterministicArtifactManifest,
    manifest: &AYLraKernelProofConsumptionManifest,
    evidence: &AYLraProofConsumptionEvidence,
) {
    let proof_evidence = evidence.proof_evidence.as_ref();
    push_if(
        reasons,
        manifest.kernel_family != AYLraKernelFamily::SparseSubstitute,
        AYLraManifestRejectionReason::UnsupportedKernelFamily,
    );
    push_if(
        reasons,
        !sparse_substitute_manifest_identity_bound(manifest),
        AYLraManifestRejectionReason::ManifestIdentityMetadataMismatch,
    );
    push_if(
        reasons,
        !sparse_substitute_source_identity_bound(artifact, proof_evidence),
        AYLraManifestRejectionReason::MissingSourceIdentity,
    );
    push_if(
        reasons,
        !sparse_substitute_layout_bound(artifact),
        AYLraManifestRejectionReason::TargetAbiLayoutMismatch,
    );
    push_if(
        reasons,
        !sparse_substitute_invalidation_bound(artifact),
        AYLraManifestRejectionReason::InvalidationMismatch,
    );
    push_if(
        reasons,
        !replay_hashes_bound(&evidence.replay, manifest.kernel_family),
        AYLraManifestRejectionReason::ReplayMismatch,
    );
    push_if(
        reasons,
        !product_gate_hashes_bound(&evidence.product_gate, manifest.kernel_family),
        AYLraManifestRejectionReason::MissingProductGate,
    );
}

fn required_requirement(
    family: AYLraProofFamily,
    fact: AYLraProofFact,
    lemma_id: &'static str,
) -> AYLraProofRequirement {
    AYLraProofRequirement {
        family,
        fact,
        lemma_id,
        availability: AYLraRequirementAvailability::RequiredForAdmission,
    }
}

fn future_requirement(
    family: AYLraProofFamily,
    fact: AYLraProofFact,
    lemma_id: &'static str,
) -> AYLraProofRequirement {
    AYLraProofRequirement {
        family,
        fact,
        lemma_id,
        availability: AYLraRequirementAvailability::MissingFuture,
    }
}

fn rejection_for_fact(fact: AYLraProofFact) -> AYLraManifestRejectionReason {
    match fact {
        AYLraProofFact::SortedSparseRows => AYLraManifestRejectionReason::MissingSortedSparseRows,
        AYLraProofFact::EnteringVariable => AYLraManifestRejectionReason::MissingEnteringVariable,
        AYLraProofFact::TargetPivotAliasPolicy => {
            AYLraManifestRejectionReason::MissingTargetPivotAliasPolicy
        }
        AYLraProofFact::OutputCapacityBounds => {
            AYLraManifestRejectionReason::MissingOutputCapacityBounds
        }
        AYLraProofFact::CoefficientOverflow => {
            AYLraManifestRejectionReason::MissingCoefficientOverflow
        }
        AYLraProofFact::BasisEpochFreshness => AYLraManifestRejectionReason::StaleBasisEpoch,
        AYLraProofFact::BatchPrefixCommitRollback => {
            AYLraManifestRejectionReason::MissingBatchPrefixCommitRollback
        }
        AYLraProofFact::SourceIdentityLocks => AYLraManifestRejectionReason::MissingSourceIdentity,
        AYLraProofFact::Aarch64AbiLayout => AYLraManifestRejectionReason::TargetAbiLayoutMismatch,
        AYLraProofFact::StatusSignature => AYLraManifestRejectionReason::StatusSignatureMismatch,
        AYLraProofFact::ProofPolicyChecksum => AYLraManifestRejectionReason::MissingProofEvidence,
        AYLraProofFact::ReplayComparison => AYLraManifestRejectionReason::MissingReplayComparison,
        AYLraProofFact::SatCandidateLoopProof
        | AYLraProofFact::ChcCandidateLoopProof
        | AYLraProofFact::PbCandidateLoopProof => {
            AYLraManifestRejectionReason::MissingCertificateDependency
        }
    }
}

fn kernel_metadata_matches(
    artifact: &DeterministicArtifactManifest,
    family: AYLraKernelFamily,
) -> bool {
    let accepted = family.accepted_kernel_metadata();
    artifact
        .metadata
        .get("kernel")
        .or_else(|| artifact.layout.metadata.get("kernel"))
        .map(|kernel| accepted.iter().any(|accepted| accepted == kernel))
        .unwrap_or(false)
}

fn sparse_substitute_manifest_identity_bound(
    manifest: &AYLraKernelProofConsumptionManifest,
) -> bool {
    let canonical = ay_lra_sparse_substitute_proof_manifest();
    manifest == &canonical
}

fn sparse_substitute_source_identity_bound(
    artifact: &DeterministicArtifactManifest,
    proof_evidence: Option<&ProofEvidenceSummary>,
) -> bool {
    private_source_metadata_bound(
        artifact,
        proof_evidence,
        SPARSE_SUBSTITUTE_TRUST_IR_SOURCE_IDENTITY,
        SPARSE_SUBSTITUTE_TRUST_CG_SOURCE_LOCK,
        SPARSE_SUBSTITUTE_TRUST_IR_SOURCE_LOCK,
    )
}

fn private_source_metadata_bound(
    artifact: &DeterministicArtifactManifest,
    proof_evidence: Option<&ProofEvidenceSummary>,
    expected_trust_ir_source_identity: &str,
    expected_trust_cg_source_lock: &str,
    expected_trust_ir_source_lock: &str,
) -> bool {
    artifact_metadata_matches(
        artifact,
        "trust_ir_source_identity",
        expected_trust_ir_source_identity,
    ) && artifact_metadata_matches(artifact, "source_policy", "approved_private_source")
        && has_metadata(artifact, "approved_private_source_policy")
        && artifact_metadata_matches(
            artifact,
            "trust_cg_source_lock",
            expected_trust_cg_source_lock,
        )
        && artifact_metadata_matches(
            artifact,
            "trust_ir_source_lock",
            expected_trust_ir_source_lock,
        )
        && proof_evidence
            .map(|proof| {
                proof_metadata_matches(
                    proof,
                    "trust_ir_source_identity",
                    expected_trust_ir_source_identity,
                ) && proof_metadata_matches(proof, "source_policy", "approved_private_source")
                    && proof_metadata_matches(
                        proof,
                        "trust_cg_source_lock",
                        expected_trust_cg_source_lock,
                    )
                    && proof_metadata_matches(
                        proof,
                        "trust_ir_source_lock",
                        expected_trust_ir_source_lock,
                    )
            })
            .unwrap_or(false)
}

fn sparse_substitute_layout_bound(artifact: &DeterministicArtifactManifest) -> bool {
    artifact.layout.wrapper_identity.as_deref() == Some(SPARSE_SUBSTITUTE_WRAPPER_IDENTITY)
        && layout_metadata_matches(artifact, "kernel", "ay_lra_sparse_substitute")
        && status_abi_metadata_matches(artifact, SPARSE_STATUS_ABI)
        && artifact
            .layout
            .symbols
            .iter()
            .any(|symbol| symbol.name == SPARSE_STATUS_SYMBOL && symbol.alignment_bytes == 16)
        && sparse_substitute_slice_bound(
            artifact,
            "pivot_coeffs",
            Mutability::Immutable,
            AliasPolicy::SharedReadOnly,
        )
        && sparse_substitute_slice_bound(
            artifact,
            "target_coeffs",
            Mutability::Mutable,
            AliasPolicy::Exclusive,
        )
        && artifact.layout.pointers.iter().any(|pointer| {
            pointer.name == "status_out"
                && pointer.bounds
                    == (PointerBounds::ByteRange {
                        start_bytes: 0,
                        length_bytes: 24,
                    })
                && pointer.mutability == Mutability::Mutable
                && pointer.alias_policy == AliasPolicy::Exclusive
        })
}

fn sparse_substitute_invalidation_bound(artifact: &DeterministicArtifactManifest) -> bool {
    invalidation_extra_matches(artifact, "basis_epoch", "runtime")
        && invalidation_extra_matches(artifact, "status_abi", SPARSE_STATUS_ABI)
}

fn sparse_substitute_slice_bound(
    artifact: &DeterministicArtifactManifest,
    name: &str,
    mutability: Mutability,
    alias_policy: AliasPolicy,
) -> bool {
    artifact.layout.slices.iter().any(|slice| {
        slice.name == name
            && slice.element_size_bytes == 8
            && slice.element_alignment_bytes == 8
            && slice.stride_bytes == 8
            && slice.length.is_none()
            && slice.bounds == PointerBounds::Symbol("row_len".to_owned())
            && slice.mutability == mutability
            && slice.alias_policy == alias_policy
    })
}

fn sparse_affected_row_batch_manifest_identity_bound(
    manifest: &AYLraKernelProofConsumptionManifest,
) -> bool {
    let canonical = ay_lra_sparse_affected_row_batch_proof_manifest();
    manifest == &canonical
}

fn sparse_affected_row_batch_source_identity_bound(
    artifact: &DeterministicArtifactManifest,
    proof_evidence: Option<&ProofEvidenceSummary>,
) -> bool {
    private_source_metadata_bound(
        artifact,
        proof_evidence,
        SPARSE_AFFECTED_ROW_BATCH_TRUST_IR_SOURCE_IDENTITY,
        SPARSE_AFFECTED_ROW_BATCH_TRUST_CG_SOURCE_LOCK,
        SPARSE_AFFECTED_ROW_BATCH_TRUST_IR_SOURCE_LOCK,
    )
}

fn sparse_affected_row_batch_layout_bound(artifact: &DeterministicArtifactManifest) -> bool {
    artifact.layout.wrapper_identity.as_deref() == Some(SPARSE_AFFECTED_ROW_BATCH_WRAPPER_IDENTITY)
        && layout_pair_metadata_matches(artifact, "kernel", SPARSE_AFFECTED_ROW_BATCH_KERNEL)
        && layout_pair_metadata_matches(
            artifact,
            "row_output_lengths",
            SPARSE_AFFECTED_ROW_BATCH_ROW_OUTPUT_LENGTHS,
        )
        && layout_pair_metadata_matches(
            artifact,
            "output_capacity",
            SPARSE_AFFECTED_ROW_BATCH_OUTPUT_CAPACITY,
        )
        && layout_pair_metadata_matches(
            artifact,
            "status_value",
            SPARSE_AFFECTED_ROW_BATCH_STATUS_VALUE,
        )
        && layout_pair_metadata_matches(
            artifact,
            "status_detail",
            SPARSE_AFFECTED_ROW_BATCH_STATUS_DETAIL,
        )
        && status_abi_metadata_matches(artifact, SPARSE_AFFECTED_ROW_BATCH_STATUS_ABI)
        && artifact.layout.symbols.iter().any(|symbol| {
            symbol.name == SPARSE_AFFECTED_ROW_BATCH_STATUS_SYMBOL && symbol.alignment_bytes == 16
        })
        && basis_row_batch_slice_bound(
            artifact,
            "row_output_lengths",
            Mutability::Mutable,
            AliasPolicy::Exclusive,
            PointerBounds::Symbol("affected_row_count".to_owned()),
            None,
        )
        && artifact.layout.pointers.iter().any(|pointer| {
            pointer.name == "batch_status_out"
                && pointer.bounds
                    == (PointerBounds::ByteRange {
                        start_bytes: 0,
                        length_bytes: 24,
                    })
                && pointer.mutability == Mutability::Mutable
                && pointer.alias_policy == AliasPolicy::Exclusive
        })
}

fn sparse_affected_row_batch_invalidation_bound(artifact: &DeterministicArtifactManifest) -> bool {
    invalidation_extra_matches(artifact, "basis_epoch", "runtime")
        && invalidation_extra_matches(artifact, "row_output_lengths", "mutable_runtime")
        && invalidation_extra_matches(
            artifact,
            "row_output_lengths_contract",
            SPARSE_AFFECTED_ROW_BATCH_ROW_OUTPUT_LENGTHS,
        )
        && invalidation_extra_matches(
            artifact,
            "output_capacity",
            SPARSE_AFFECTED_ROW_BATCH_OUTPUT_CAPACITY,
        )
        && invalidation_extra_matches(artifact, "status_abi", SPARSE_AFFECTED_ROW_BATCH_STATUS_ABI)
        && invalidation_extra_matches(
            artifact,
            "status_detail",
            SPARSE_AFFECTED_ROW_BATCH_STATUS_DETAIL,
        )
        && invalidation_extra_matches(
            artifact,
            "status_value",
            SPARSE_AFFECTED_ROW_BATCH_STATUS_VALUE,
        )
}

fn basis_row_batch_source_identity_bound(
    artifact: &DeterministicArtifactManifest,
    proof_evidence: Option<&ProofEvidenceSummary>,
) -> bool {
    private_source_metadata_bound(
        artifact,
        proof_evidence,
        BASIS_ROW_BATCH_TRUST_IR_SOURCE_IDENTITY,
        BASIS_ROW_BATCH_TRUST_CG_SOURCE_LOCK,
        BASIS_ROW_BATCH_TRUST_IR_SOURCE_LOCK,
    )
}

fn basis_row_batch_manifest_identity_bound(manifest: &AYLraKernelProofConsumptionManifest) -> bool {
    let canonical = ay_lra_basis_update_proof_manifest();
    manifest == &canonical
}

fn basis_row_batch_manifest_declares_prefix_rollback(
    manifest: &AYLraKernelProofConsumptionManifest,
) -> bool {
    manifest
        .admission_preconditions
        .contains(&AYLraProofFact::BatchPrefixCommitRollback)
        && manifest.required_facts.iter().any(|requirement| {
            requirement.family == AYLraProofFamily::LraBasisUpdate
                && requirement.fact == AYLraProofFact::BatchPrefixCommitRollback
                && requirement.lemma_id == BASIS_ROW_BATCH_PREFIX_ROLLBACK_LEMMA
                && requirement.availability == AYLraRequirementAvailability::RequiredForAdmission
        })
}

fn basis_row_batch_manifest_declares_prefix_rollback_certificate(
    manifest: &AYLraKernelProofConsumptionManifest,
) -> bool {
    manifest.certificate_dependencies.iter().any(|dependency| {
        dependency.id == BASIS_ROW_BATCH_PREFIX_ROLLBACK_CERTIFICATE
            && dependency.family == AYLraProofFamily::LraBasisUpdate
            && dependency.availability == AYLraRequirementAvailability::RequiredForAdmission
    })
}

fn basis_row_batch_layout_bound(artifact: &DeterministicArtifactManifest) -> bool {
    artifact.layout.wrapper_identity.as_deref() == Some(BASIS_ROW_BATCH_WRAPPER_IDENTITY)
        && layout_pair_metadata_matches(artifact, "kernel", BASIS_STATUS_SYMBOL)
        && layout_pair_metadata_matches(
            artifact,
            "tableau_row_layout",
            BASIS_ROW_BATCH_TABLEAU_ROW_LAYOUT,
        )
        && layout_pair_metadata_matches(
            artifact,
            "basis_row_layout",
            BASIS_ROW_BATCH_BASIS_ROW_LAYOUT,
        )
        && layout_pair_metadata_matches(
            artifact,
            "row_region_hash",
            BASIS_ROW_BATCH_ROW_REGION_HASH,
        )
        && layout_pair_metadata_matches(
            artifact,
            "scratch_rollback",
            BASIS_ROW_BATCH_SCRATCH_ROLLBACK,
        )
        && layout_pair_metadata_matches(
            artifact,
            "rollback_failure_disposition",
            BASIS_ROW_BATCH_ROLLBACK_FAILURE_DISPOSITION,
        )
        && layout_pair_metadata_matches(artifact, "alias_policy", BASIS_ROW_BATCH_ALIAS_POLICY)
        && layout_pair_metadata_matches(
            artifact,
            "output_capacity",
            BASIS_ROW_BATCH_OUTPUT_CAPACITY,
        )
        && layout_pair_metadata_matches(artifact, "commit_policy", BASIS_ROW_BATCH_COMMIT_POLICY)
        && layout_pair_metadata_matches(artifact, "status_value", BASIS_ROW_BATCH_STATUS_VALUE)
        && layout_pair_metadata_matches(artifact, "status_detail", BASIS_ROW_BATCH_STATUS_DETAIL)
        && status_abi_metadata_matches(artifact, BASIS_STATUS_ABI)
        && artifact
            .layout
            .symbols
            .iter()
            .any(|symbol| symbol.name == BASIS_STATUS_SYMBOL && symbol.alignment_bytes == 16)
        && basis_row_batch_slice_bound(
            artifact,
            "tableau_row_ptrs",
            Mutability::Mutable,
            AliasPolicy::Exclusive,
            PointerBounds::Symbol("affected_row_count".to_owned()),
            None,
        )
        && basis_row_batch_slice_bound(
            artifact,
            "row_scales",
            Mutability::Immutable,
            AliasPolicy::SharedReadOnly,
            PointerBounds::Symbol("affected_row_count".to_owned()),
            None,
        )
        && basis_row_batch_slice_bound(
            artifact,
            "basis_epochs",
            Mutability::Immutable,
            AliasPolicy::SharedReadOnly,
            PointerBounds::ByteRange {
                start_bytes: 0,
                length_bytes: 16,
            },
            Some(2),
        )
        && basis_row_batch_slice_bound(
            artifact,
            "row_output_offsets",
            Mutability::Immutable,
            AliasPolicy::SharedReadOnly,
            PointerBounds::Symbol("affected_row_count".to_owned()),
            None,
        )
        && basis_row_batch_slice_bound(
            artifact,
            "row_output_lengths",
            Mutability::Mutable,
            AliasPolicy::Exclusive,
            PointerBounds::Symbol("affected_row_count".to_owned()),
            None,
        )
        && artifact.layout.pointers.iter().any(|pointer| {
            pointer.name == "batch_status_out"
                && pointer.bounds
                    == (PointerBounds::ByteRange {
                        start_bytes: 0,
                        length_bytes: 24,
                    })
                && pointer.mutability == Mutability::Mutable
                && pointer.alias_policy == AliasPolicy::Exclusive
        })
}

fn basis_row_batch_invalidation_bound(artifact: &DeterministicArtifactManifest) -> bool {
    invalidation_extra_matches(artifact, "tableau_row_ptrs", "runtime")
        && invalidation_extra_matches(artifact, "row_scales", "runtime")
        && invalidation_extra_matches(artifact, "basis_epoch", "runtime")
        && invalidation_extra_matches(
            artifact,
            "basis_row_layout",
            BASIS_ROW_BATCH_BASIS_ROW_LAYOUT,
        )
        && invalidation_extra_matches(
            artifact,
            "tableau_row_layout",
            BASIS_ROW_BATCH_TABLEAU_ROW_LAYOUT,
        )
        && invalidation_extra_matches(
            artifact,
            "row_region_hash",
            BASIS_ROW_BATCH_INVALIDATION_ROW_REGION_HASH,
        )
        && invalidation_extra_matches(artifact, "commit_policy", BASIS_ROW_BATCH_COMMIT_POLICY)
        && invalidation_extra_matches(
            artifact,
            "scratch_rollback",
            BASIS_ROW_BATCH_SCRATCH_ROLLBACK,
        )
        && invalidation_extra_matches(
            artifact,
            "rollback_failure_disposition",
            BASIS_ROW_BATCH_ROLLBACK_FAILURE_DISPOSITION,
        )
        && invalidation_extra_matches(artifact, "row_output_lengths", "mutable_runtime")
        && invalidation_extra_matches(artifact, "row_output_offsets", "runtime")
        && invalidation_extra_matches(artifact, "output_capacity", BASIS_ROW_BATCH_OUTPUT_CAPACITY)
        && invalidation_extra_matches(artifact, "status_abi", BASIS_STATUS_ABI)
        && invalidation_extra_matches(artifact, "status_detail", BASIS_ROW_BATCH_STATUS_DETAIL)
        && invalidation_extra_matches(artifact, "status_value", BASIS_ROW_BATCH_STATUS_VALUE)
}

fn basis_row_batch_slice_bound(
    artifact: &DeterministicArtifactManifest,
    name: &str,
    mutability: Mutability,
    alias_policy: AliasPolicy,
    bounds: PointerBounds,
    length: Option<u64>,
) -> bool {
    artifact.layout.slices.iter().any(|slice| {
        slice.name == name
            && slice.element_size_bytes == 8
            && slice.element_alignment_bytes == 8
            && slice.stride_bytes == 8
            && slice.length == length
            && slice.bounds == bounds
            && slice.mutability == mutability
            && slice.alias_policy == alias_policy
    })
}

fn ay_lra_solver_program_proof_facts_sha256(
    manifest: &AYLraKernelProofConsumptionManifest,
    evidence: &AYLraProofConsumptionEvidence,
) -> String {
    ay_lra_proof_facts_sha256_with_domain(
        "trust-cg.ay_lra.sparse_solver_program.proof_facts.v1",
        manifest,
        evidence,
    )
}

fn ay_lra_sparse_perf_json_manifest_sha256(
    artifact: &DeterministicArtifactManifest,
    manifest: &AYLraKernelProofConsumptionManifest,
) -> String {
    let mut out = Vec::new();
    put_str(&mut out, "trust-cg.ay_lra.sparse_perf_json.manifest.v1");
    put_str(&mut out, &artifact.checksum().to_string());
    put_str(&mut out, &artifact.schema);
    put_u64(&mut out, u64::from(artifact.schema_version));
    put_str(&mut out, &artifact.target.checksum().to_string());
    put_str(&mut out, &artifact.abi.checksum().to_string());
    put_str(&mut out, &artifact.layout.checksum().to_string());
    put_str(&mut out, &artifact.invalidation.checksum().to_string());
    put_str(&mut out, &artifact.proof_policy.checksum().to_string());
    put_str(&mut out, manifest.schema);
    put_u64(&mut out, u64::from(manifest.schema_version));
    put_u64(&mut out, manifest.issue);
    put_str(&mut out, manifest.kernel_family.as_str());
    put_str(&mut out, manifest.product_gate.allowlist_family);
    sha256_digest(&out)
}

fn ay_lra_sparse_perf_json_proof_facts_sha256(
    manifest: &AYLraKernelProofConsumptionManifest,
    evidence: &AYLraProofConsumptionEvidence,
) -> String {
    ay_lra_proof_facts_sha256_with_domain(
        "trust-cg.ay_lra.sparse_perf_json.proof_facts.v1",
        manifest,
        evidence,
    )
}

fn ay_lra_sparse_affected_row_batch_manifest_sha256(
    artifact: &DeterministicArtifactManifest,
    manifest: &AYLraKernelProofConsumptionManifest,
) -> String {
    let mut out = Vec::new();
    put_str(
        &mut out,
        "trust-cg.ay_lra.sparse_affected_row_batch.manifest.v1",
    );
    put_str(&mut out, &artifact.checksum().to_string());
    put_str(&mut out, &artifact.schema);
    put_u64(&mut out, u64::from(artifact.schema_version));
    put_str(&mut out, &artifact.target.checksum().to_string());
    put_str(&mut out, &artifact.abi.checksum().to_string());
    put_str(&mut out, &artifact.layout.checksum().to_string());
    put_str(&mut out, &artifact.invalidation.checksum().to_string());
    put_str(&mut out, &artifact.proof_policy.checksum().to_string());
    put_str(&mut out, manifest.schema);
    put_u64(&mut out, u64::from(manifest.schema_version));
    put_u64(&mut out, manifest.issue);
    put_str(&mut out, manifest.kernel_family.as_str());
    put_str(&mut out, manifest.product_gate.allowlist_family);
    sha256_digest(&out)
}

fn ay_lra_sparse_affected_row_batch_proof_facts_sha256(
    manifest: &AYLraKernelProofConsumptionManifest,
    evidence: &AYLraProofConsumptionEvidence,
) -> String {
    ay_lra_proof_facts_sha256_with_domain(
        "trust-cg.ay_lra.sparse_affected_row_batch.proof_facts.v1",
        manifest,
        evidence,
    )
}

fn ay_lra_basis_row_batch_telemetry_manifest_sha256(
    artifact: &DeterministicArtifactManifest,
    manifest: &AYLraKernelProofConsumptionManifest,
) -> String {
    let mut out = Vec::new();
    put_str(
        &mut out,
        "trust-cg.ay_lra.basis_row_batch.telemetry.manifest.v1",
    );
    put_str(&mut out, &artifact.checksum().to_string());
    put_str(&mut out, &artifact.schema);
    put_u64(&mut out, u64::from(artifact.schema_version));
    put_str(&mut out, &artifact.target.checksum().to_string());
    put_str(&mut out, &artifact.abi.checksum().to_string());
    put_str(&mut out, &artifact.layout.checksum().to_string());
    put_str(&mut out, &artifact.invalidation.checksum().to_string());
    put_str(&mut out, &artifact.proof_policy.checksum().to_string());
    put_str(&mut out, manifest.schema);
    put_u64(&mut out, u64::from(manifest.schema_version));
    put_u64(&mut out, manifest.issue);
    put_str(&mut out, manifest.kernel_family.as_str());
    put_str(&mut out, manifest.product_gate.allowlist_family);
    sha256_digest(&out)
}

fn ay_lra_basis_row_batch_telemetry_proof_facts_sha256(
    manifest: &AYLraKernelProofConsumptionManifest,
    evidence: &AYLraProofConsumptionEvidence,
) -> String {
    ay_lra_proof_facts_sha256_with_domain(
        "trust-cg.ay_lra.basis_row_batch.telemetry.proof_facts.v1",
        manifest,
        evidence,
    )
}

fn ay_lra_proof_facts_sha256_with_domain(
    domain: &str,
    manifest: &AYLraKernelProofConsumptionManifest,
    evidence: &AYLraProofConsumptionEvidence,
) -> String {
    let mut out = Vec::new();
    put_str(&mut out, domain);
    put_str(&mut out, manifest.schema);
    put_u64(&mut out, u64::from(manifest.schema_version));
    put_u64(&mut out, manifest.issue);
    put_str(&mut out, manifest.kernel_family.as_str());

    let mut required_facts: Vec<_> = manifest.required_facts.iter().collect();
    required_facts.sort_by_key(|requirement| requirement.fact.as_str());
    put_u64(&mut out, required_facts.len() as u64);
    for requirement in required_facts {
        put_str(&mut out, requirement.family.as_str());
        put_str(&mut out, requirement.fact.as_str());
        put_str(&mut out, requirement.lemma_id);
        put_str(&mut out, requirement.availability.as_str());
        let availability = evidence
            .facts
            .get(&requirement.fact)
            .copied()
            .unwrap_or(AYLraEvidenceAvailability::Missing);
        put_str(&mut out, availability.as_str());
    }

    let mut future_facts: Vec<_> = manifest.future_facts.iter().collect();
    future_facts.sort_by_key(|requirement| requirement.fact.as_str());
    put_u64(&mut out, future_facts.len() as u64);
    for requirement in future_facts {
        put_str(&mut out, requirement.family.as_str());
        put_str(&mut out, requirement.fact.as_str());
        put_str(&mut out, requirement.lemma_id);
        put_str(&mut out, requirement.availability.as_str());
        let availability = evidence
            .facts
            .get(&requirement.fact)
            .copied()
            .unwrap_or(AYLraEvidenceAvailability::Missing);
        put_str(&mut out, availability.as_str());
    }

    put_u64(&mut out, evidence.facts.len() as u64);
    for (fact, availability) in &evidence.facts {
        put_str(&mut out, fact.as_str());
        put_str(&mut out, availability.as_str());
    }

    let mut dependencies: Vec<_> = manifest.certificate_dependencies.iter().collect();
    dependencies.sort_by_key(|dependency| dependency.id);
    put_u64(&mut out, dependencies.len() as u64);
    for dependency in dependencies {
        put_str(&mut out, dependency.id);
        put_str(&mut out, dependency.family.as_str());
        put_str(&mut out, dependency.availability.as_str());
        put_option_str(&mut out, dependency.blocker);
        let availability = evidence
            .certificates
            .get(dependency.id)
            .copied()
            .unwrap_or(AYLraEvidenceAvailability::Missing);
        put_str(&mut out, availability.as_str());
    }

    put_u64(&mut out, evidence.certificates.len() as u64);
    for (id, availability) in &evidence.certificates {
        put_str(&mut out, id);
        put_str(&mut out, availability.as_str());
    }

    put_proof_evidence_summary(&mut out, evidence.proof_evidence.as_ref());
    sha256_digest(&out)
}

fn ay_lra_solver_program_replay_sha256(
    kernel_family: AYLraKernelFamily,
    replay: &AYLraReplayComparison,
) -> String {
    ay_lra_replay_sha256_with_domain(
        "trust-cg.ay_lra.sparse_solver_program.replay.v1",
        kernel_family,
        replay,
    )
}

fn ay_lra_sparse_perf_json_replay_sha256(
    kernel_family: AYLraKernelFamily,
    replay: &AYLraReplayComparison,
) -> String {
    ay_lra_replay_sha256_with_domain(
        "trust-cg.ay_lra.sparse_perf_json.replay.v1",
        kernel_family,
        replay,
    )
}

fn ay_lra_sparse_affected_row_batch_replay_sha256(
    kernel_family: AYLraKernelFamily,
    replay: &AYLraReplayComparison,
) -> String {
    ay_lra_replay_sha256_with_domain(
        "trust-cg.ay_lra.sparse_affected_row_batch.replay.v1",
        kernel_family,
        replay,
    )
}

fn ay_lra_basis_row_batch_telemetry_replay_sha256(
    kernel_family: AYLraKernelFamily,
    replay: &AYLraReplayComparison,
) -> String {
    ay_lra_replay_sha256_with_domain(
        "trust-cg.ay_lra.basis_row_batch.telemetry.replay.v1",
        kernel_family,
        replay,
    )
}

fn ay_lra_replay_sha256_with_domain(
    domain: &str,
    kernel_family: AYLraKernelFamily,
    replay: &AYLraReplayComparison,
) -> String {
    let mut out = Vec::new();
    put_str(&mut out, domain);
    put_str(&mut out, kernel_family.as_str());
    put_str(&mut out, &replay.manifest_checksum.to_string());
    put_str(&mut out, &replay.replay_root_sha256);
    put_str(&mut out, &replay.generic_behavior_sha256);
    put_str(&mut out, &replay.specialized_behavior_sha256);
    put_str(&mut out, &replay.reference_behavior_sha256);
    sha256_digest(&out)
}

fn ay_lra_solver_program_product_gate_sha256(
    kernel_family: AYLraKernelFamily,
    product_gate: &AYLraProductGateEvidence,
) -> String {
    ay_lra_product_gate_sha256_with_domain(
        "trust-cg.ay_lra.sparse_solver_program.product_gate.v1",
        kernel_family,
        product_gate,
    )
}

fn ay_lra_sparse_perf_json_product_gate_sha256(
    kernel_family: AYLraKernelFamily,
    product_gate: &AYLraProductGateEvidence,
) -> String {
    ay_lra_product_gate_sha256_with_domain(
        "trust-cg.ay_lra.sparse_perf_json.product_gate.v1",
        kernel_family,
        product_gate,
    )
}

fn ay_lra_sparse_affected_row_batch_product_gate_sha256(
    kernel_family: AYLraKernelFamily,
    product_gate: &AYLraProductGateEvidence,
) -> String {
    ay_lra_product_gate_sha256_with_domain(
        "trust-cg.ay_lra.sparse_affected_row_batch.product_gate.v1",
        kernel_family,
        product_gate,
    )
}

fn ay_lra_basis_row_batch_telemetry_product_gate_sha256(
    kernel_family: AYLraKernelFamily,
    product_gate: &AYLraProductGateEvidence,
) -> String {
    ay_lra_product_gate_sha256_with_domain(
        "trust-cg.ay_lra.basis_row_batch.telemetry.product_gate.v1",
        kernel_family,
        product_gate,
    )
}

fn ay_lra_product_gate_sha256_with_domain(
    domain: &str,
    kernel_family: AYLraKernelFamily,
    product_gate: &AYLraProductGateEvidence,
) -> String {
    let mut out = Vec::new();
    put_str(&mut out, domain);
    put_str(&mut out, kernel_family.as_str());
    put_str(&mut out, &product_gate.install_gate_packet_sha256);
    put_str(&mut out, &product_gate.consumer_admission_sha256);
    put_str(&mut out, &product_gate.replay_identity_sha256);
    put_str(&mut out, &product_gate.telemetry_record_sha256);
    sha256_digest(&out)
}

fn replay_hashes_bound(replay: &AYLraReplayComparison, kernel_family: AYLraKernelFamily) -> bool {
    evidence_hash_bound(&replay.replay_root_sha256, kernel_family, "replay-root")
        && evidence_hash_bound(
            &replay.generic_behavior_sha256,
            kernel_family,
            "reference-behavior",
        )
        && evidence_hash_bound(
            &replay.specialized_behavior_sha256,
            kernel_family,
            "reference-behavior",
        )
        && evidence_hash_bound(
            &replay.reference_behavior_sha256,
            kernel_family,
            "reference-behavior",
        )
}

fn product_gate_hashes_bound(
    product_gate: &AYLraProductGateEvidence,
    kernel_family: AYLraKernelFamily,
) -> bool {
    evidence_hash_bound(
        &product_gate.install_gate_packet_sha256,
        kernel_family,
        "install-gate",
    ) && evidence_hash_bound(
        &product_gate.consumer_admission_sha256,
        kernel_family,
        "consumer-admission",
    ) && evidence_hash_bound(
        &product_gate.replay_identity_sha256,
        kernel_family,
        "replay-identity",
    ) && evidence_hash_bound(
        &product_gate.telemetry_record_sha256,
        kernel_family,
        "telemetry",
    )
}

fn evidence_hash_bound(
    value: &str,
    _kernel_family: AYLraKernelFamily,
    _contract_suffix: &str,
) -> bool {
    canonical_sha256_bound(value)
}

fn canonical_sha256_bound(value: &str) -> bool {
    let Some(digest) = value.strip_prefix("sha256:") else {
        return false;
    };
    digest.len() == 64
        && digest
            .bytes()
            .all(|byte| matches!(byte, b'0'..=b'9' | b'a'..=b'f'))
}

fn source_policy_bound(
    artifact: &DeterministicArtifactManifest,
    proof_evidence: Option<&ProofEvidenceSummary>,
) -> bool {
    let Some(proof) = proof_evidence else {
        return false;
    };
    let Some(source_policy) = artifact.metadata.get("source_policy").map(String::as_str) else {
        return false;
    };

    artifact_proof_metadata_matches(artifact, proof, "source_policy")
        && artifact_proof_metadata_matches(artifact, proof, "trust_ir_source_identity")
        && artifact_proof_metadata_matches(artifact, proof, "trust_cg_source_lock")
        && artifact_proof_metadata_matches(artifact, proof, "trust_ir_source_lock")
        && match source_policy {
            "public_source_locks" => true,
            "approved_private_source" => has_metadata(artifact, "approved_private_source_policy"),
            _ => false,
        }
}

fn artifact_proof_metadata_matches(
    artifact: &DeterministicArtifactManifest,
    proof: &ProofEvidenceSummary,
    key: &str,
) -> bool {
    artifact
        .metadata
        .get(key)
        .filter(|value| !missing_required_text(value))
        .map(|value| proof_metadata_matches(proof, key, value))
        .unwrap_or(false)
}

fn aarch64_lp64_layout_bound(artifact: &DeterministicArtifactManifest) -> bool {
    matches!(&artifact.kind, JitArtifactKind::ExecutableMemory)
        && matches!(&artifact.target.architecture, TargetArchitecture::Aarch64)
        && matches!(
            &artifact.target.operating_system,
            TargetOperatingSystem::Macos
        )
        && artifact.target.pointer_width_bits == 64
        && aarch64_aapcs64_abi_bound(&artifact.abi)
        && artifact_metadata_matches(
            artifact,
            "target_abi_layout",
            AARCH64_MACOS_AAPCS64_LP64_TARGET_ABI_LAYOUT,
        )
        && artifact.layout.pointer_size_bytes == 8
        && artifact.layout.pointer_alignment_bytes == 8
        && artifact.layout.stack_alignment_bytes == 16
}

fn aarch64_aapcs64_abi_bound(abi: &AbiDescriptor) -> bool {
    abi.calling_convention == AARCH64_AAPCS64_CALLING_CONVENTION
        && abi.pointer_width_bits == 64
        && abi.stack_alignment_bytes == 16
        && abi.red_zone_bytes == 128
        && abi.shadow_space_bytes == 0
        && string_list_matches(
            &abi.integer_argument_registers,
            &["x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7"],
        )
        && string_list_matches(
            &abi.float_argument_registers,
            &["v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7"],
        )
        && string_list_matches(
            &abi.integer_return_registers,
            &["x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7"],
        )
        && string_list_matches(
            &abi.float_return_registers,
            &["v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7"],
        )
        && string_list_matches(
            &abi.callee_saved_registers,
            &[
                "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28",
            ],
        )
        && abi.executable_memory_owner == ExecutableMemoryOwner::TrustCg
        && abi.teardown_policy == TeardownPolicy::RefCounted
        && abi.varargs == AbiVarargsPolicy::Unsupported
}

fn string_list_matches(values: &[String], expected: &[&str]) -> bool {
    values.len() == expected.len()
        && values
            .iter()
            .zip(expected.iter())
            .all(|(value, expected)| value.as_str() == *expected)
}

fn invalidation_binds_current_artifact(artifact: &DeterministicArtifactManifest) -> bool {
    artifact.invalidation.target_checksum == artifact.target.checksum()
        && artifact.invalidation.abi_checksum == artifact.abi.checksum()
        && artifact.invalidation.layout_checksum == artifact.layout.checksum()
        && artifact.invalidation.proof_policy_checksum == artifact.proof_policy.checksum()
        && artifact.invalidation.generation > 0
}

fn basis_epoch_fresh_for_artifact(
    artifact: &DeterministicArtifactManifest,
    basis_epoch: AYLraBasisEpochEvidence,
) -> bool {
    basis_epoch.is_fresh()
        && basis_epoch.current_epoch == artifact.invalidation.generation
        && basis_epoch.expected_epoch == artifact.invalidation.generation
}

fn push_manifest_metadata_rejections(
    reasons: &mut Vec<AYLraManifestRejectionReason>,
    artifact: &DeterministicArtifactManifest,
    manifest: &AYLraKernelProofConsumptionManifest,
    proof_evidence: Option<&ProofEvidenceSummary>,
) {
    let manifest_issue = format!("#{}", manifest.issue);
    let identity_matches = artifact_metadata_matches(
        artifact,
        "proof_consumption_manifest_schema",
        manifest.schema,
    ) && artifact_metadata_matches(
        artifact,
        "proof_consumption_manifest_issue",
        &manifest_issue,
    ) && proof_evidence
        .map(|proof| {
            proof_metadata_matches(proof, "proof_consumption_manifest_schema", manifest.schema)
                && proof_metadata_matches(
                    proof,
                    "proof_consumption_manifest_issue",
                    &manifest_issue,
                )
                && proof_metadata_matches(proof, "kernel_family", manifest.kernel_family.as_str())
        })
        .unwrap_or(true);
    push_if(
        reasons,
        !identity_matches,
        AYLraManifestRejectionReason::ManifestIdentityMetadataMismatch,
    );

    let required_facts = manifest.required_fact_csv();
    let required_proof_matches =
        artifact_metadata_matches(artifact, "required_proof_facts", &required_facts)
            && proof_evidence
                .map(|proof| proof_metadata_matches(proof, "required_proof_facts", &required_facts))
                .unwrap_or(true);
    push_if(
        reasons,
        !required_proof_matches,
        AYLraManifestRejectionReason::RequiredProofMetadataMismatch,
    );

    let required_certificates = manifest.required_certificate_csv();
    let required_certificate_matches = artifact_metadata_matches(
        artifact,
        "required_certificate_dependencies",
        &required_certificates,
    ) && proof_evidence
        .map(|proof| {
            proof_metadata_matches(
                proof,
                "required_certificate_dependencies",
                &required_certificates,
            )
        })
        .unwrap_or(true);
    push_if(
        reasons,
        !required_certificate_matches,
        AYLraManifestRejectionReason::RequiredCertificateMetadataMismatch,
    );

    let future_status = manifest_future_proof_status(manifest);
    let future_status_matches =
        artifact_metadata_matches(artifact, "future_proof_status", &future_status)
            && proof_evidence
                .map(|proof| proof_metadata_matches(proof, "future_proof_status", &future_status))
                .unwrap_or(true);
    push_if(
        reasons,
        !future_status_matches,
        AYLraManifestRejectionReason::FutureProofStatusMismatch,
    );

    let product_gate_fields = manifest.product_gate.required_parent_gates.join(",");
    let useful_native = manifest.product_gate.useful_native_eligible.to_string();
    let baseline_authoritative = manifest
        .product_gate
        .baseline_authoritative_until_product_gate
        .to_string();
    let product_gate_matches =
        artifact_metadata_matches(artifact, "consumer", manifest.product_gate.consumer)
            && artifact_metadata_matches(
                artifact,
                "product_gate_surface",
                manifest.product_gate.surface,
            )
            && artifact_metadata_matches(
                artifact,
                "product_gate_allowlist_family",
                manifest.product_gate.allowlist_family,
            )
            && artifact_metadata_matches(artifact, "product_gate_fields", &product_gate_fields)
            && artifact_metadata_matches(
                artifact,
                "telemetry_counter_policy",
                manifest.product_gate.telemetry_counter_policy,
            )
            && artifact_metadata_matches(artifact, "useful_native", &useful_native)
            && artifact_metadata_matches(
                artifact,
                "baseline_authoritative_until_product_gate",
                &baseline_authoritative,
            )
            && proof_evidence
                .map(|proof| {
                    proof_metadata_matches(proof, "product_gate_fields", &product_gate_fields)
                })
                .unwrap_or(true);
    push_if(
        reasons,
        !product_gate_matches,
        AYLraManifestRejectionReason::ProductGateMetadataMismatch,
    );
}

fn status_signature_bound(
    artifact: &DeterministicArtifactManifest,
    family: AYLraKernelFamily,
) -> bool {
    let contract = status_contract(family);
    let Some(symbol) = artifact
        .symbols
        .iter()
        .find(|symbol| symbol.name == contract.symbol)
    else {
        return false;
    };
    let expected_signature_checksum = contract.signature.checksum().to_string();

    symbol.signature == contract.signature
        && artifact_metadata_matches(
            artifact,
            "status_signature_checksum",
            &expected_signature_checksum,
        )
        && artifact
            .layout
            .symbols
            .iter()
            .any(|layout_symbol| layout_symbol.name == contract.symbol)
        && artifact
            .layout
            .records
            .iter()
            .any(|record| record == &contract.status_record)
        && status_abi_metadata_matches(artifact, contract.status_abi)
}

fn has_metadata(artifact: &DeterministicArtifactManifest, key: &str) -> bool {
    artifact
        .metadata
        .get(key)
        .map(|value| !missing_required_text(value))
        .unwrap_or(false)
}

fn artifact_metadata_matches(
    artifact: &DeterministicArtifactManifest,
    key: &str,
    expected: &str,
) -> bool {
    artifact
        .metadata
        .get(key)
        .map(|value| value == expected)
        .unwrap_or(false)
}

fn layout_metadata_matches(
    artifact: &DeterministicArtifactManifest,
    key: &str,
    expected: &str,
) -> bool {
    artifact
        .layout
        .metadata
        .get(key)
        .map(|value| value == expected)
        .unwrap_or(false)
}

fn layout_pair_metadata_matches(
    artifact: &DeterministicArtifactManifest,
    key: &str,
    expected: &str,
) -> bool {
    artifact_metadata_matches(artifact, key, expected)
        && layout_metadata_matches(artifact, key, expected)
}

fn invalidation_extra_matches(
    artifact: &DeterministicArtifactManifest,
    key: &str,
    expected: &str,
) -> bool {
    artifact
        .invalidation
        .extra
        .get(key)
        .map(|value| value == expected)
        .unwrap_or(false)
}

fn proof_metadata_matches(proof: &ProofEvidenceSummary, key: &str, expected: &str) -> bool {
    proof
        .metadata
        .get(key)
        .map(|value| value == expected)
        .unwrap_or(false)
}

fn proof_fact_metadata_mismatch_detail(
    proof_evidence: Option<&ProofEvidenceSummary>,
    requirement: &AYLraProofRequirement,
) -> Option<AYLraProofMetadataMismatchDetail> {
    let key = ay_lra_proof_fact_metadata_key(requirement.fact);
    let actual = proof_evidence.and_then(|proof| proof.metadata.get(&key).cloned());
    if actual.as_deref() == Some(requirement.lemma_id) {
        None
    } else {
        Some(AYLraProofMetadataMismatchDetail {
            key,
            expected: requirement.lemma_id,
            actual,
        })
    }
}

fn status_abi_metadata_matches(artifact: &DeterministicArtifactManifest, expected: &str) -> bool {
    let artifact_status_abi = artifact.metadata.get("status_abi");
    let layout_status_abi = artifact.layout.metadata.get("status_abi");
    artifact_status_abi
        .map(|value| value == expected)
        .unwrap_or(true)
        && layout_status_abi
            .map(|value| value == expected)
            .unwrap_or(true)
        && (artifact_status_abi.is_some() || layout_status_abi.is_some())
}

fn manifest_future_proof_status(manifest: &AYLraKernelProofConsumptionManifest) -> String {
    let mut statuses: Vec<_> = manifest
        .future_facts
        .iter()
        .map(|requirement| requirement.availability.as_str())
        .collect();
    statuses.sort_unstable();
    statuses.dedup();
    statuses.join(",")
}

struct AYLraStatusContract {
    symbol: &'static str,
    status_abi: &'static str,
    signature: SymbolSignature,
    status_record: RecordLayout,
}

fn status_contract(family: AYLraKernelFamily) -> AYLraStatusContract {
    match family {
        AYLraKernelFamily::SparseSubstitute => AYLraStatusContract {
            symbol: SPARSE_STATUS_SYMBOL,
            status_abi: SPARSE_STATUS_ABI,
            signature: ay_lra_sparse_status_signature(),
            status_record: ay_lra_sparse_status_record(),
        },
        AYLraKernelFamily::SparseAffectedRowBatch => AYLraStatusContract {
            symbol: SPARSE_AFFECTED_ROW_BATCH_STATUS_SYMBOL,
            status_abi: SPARSE_AFFECTED_ROW_BATCH_STATUS_ABI,
            signature: ay_lra_sparse_affected_row_batch_status_signature(),
            status_record: ay_lra_sparse_affected_row_batch_status_record(),
        },
        AYLraKernelFamily::BasisUpdate => AYLraStatusContract {
            symbol: BASIS_STATUS_SYMBOL,
            status_abi: BASIS_STATUS_ABI,
            signature: ay_lra_basis_status_signature(),
            status_record: ay_lra_basis_status_record(),
        },
    }
}

fn i64_value() -> AbiValue {
    AbiValue::new(AbiValueKind::I64)
}

fn ptr_value() -> AbiValue {
    AbiValue::new(AbiValueKind::Ptr)
}

fn ay_lra_sparse_status_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![
            i64_value(),
            i64_value(),
            i64_value(),
            i64_value(),
            i64_value(),
            i64_value(),
            ptr_value(),
        ],
        vec![],
    )
}

fn ay_lra_sparse_affected_row_batch_status_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![
            i64_value(),
            i64_value(),
            i64_value(),
            i64_value(),
            i64_value(),
            ptr_value(),
            ptr_value(),
        ],
        vec![],
    )
}

fn ay_lra_basis_status_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![
            ptr_value(),
            ptr_value(),
            i64_value(),
            ptr_value(),
            ptr_value(),
            i64_value(),
            ptr_value(),
            ptr_value(),
        ],
        vec![],
    )
}

fn ay_lra_sparse_status_record() -> RecordLayout {
    RecordLayout {
        name: SPARSE_STATUS_RECORD.to_owned(),
        representation: "repr(C)".to_owned(),
        size_bytes: 24,
        alignment_bytes: 8,
        fields: vec![
            field_layout("status", 0, 1, 1),
            field_layout("deopt", 1, 1, 1),
            field_layout("reserved", 2, 6, 1),
            field_layout("value", 8, 8, 8),
            field_layout("detail", 16, 8, 8),
        ],
    }
}

fn ay_lra_sparse_affected_row_batch_status_record() -> RecordLayout {
    RecordLayout {
        name: SPARSE_AFFECTED_ROW_BATCH_STATUS_RECORD.to_owned(),
        representation: "repr(C)".to_owned(),
        size_bytes: 24,
        alignment_bytes: 8,
        fields: vec![
            field_layout("status", 0, 1, 1),
            field_layout("deopt", 1, 1, 1),
            field_layout("reserved", 2, 6, 1),
            field_layout("rows_committed", 8, 8, 8),
            field_layout("first_failed_row", 16, 8, 8),
        ],
    }
}

fn ay_lra_basis_status_record() -> RecordLayout {
    RecordLayout {
        name: BASIS_STATUS_RECORD.to_owned(),
        representation: "repr(C)".to_owned(),
        size_bytes: 24,
        alignment_bytes: 8,
        fields: vec![
            field_layout("status", 0, 1, 1),
            field_layout("deopt", 1, 1, 1),
            field_layout("reserved", 2, 6, 1),
            field_layout("rows_completed", 8, 8, 8),
            field_layout("first_failed_row", 16, 8, 8),
        ],
    }
}

fn field_layout(
    name: &str,
    offset_bytes: u64,
    size_bytes: u64,
    alignment_bytes: u32,
) -> FieldLayout {
    FieldLayout {
        name: name.to_owned(),
        offset_bytes,
        size_bytes,
        alignment_bytes,
    }
}

fn push_if(
    reasons: &mut Vec<AYLraManifestRejectionReason>,
    condition: bool,
    reason: AYLraManifestRejectionReason,
) {
    if condition {
        push_unique(reasons, reason);
    }
}

fn push_unique(
    reasons: &mut Vec<AYLraManifestRejectionReason>,
    reason: AYLraManifestRejectionReason,
) {
    if !reasons.contains(&reason) {
        reasons.push(reason);
    }
}

fn put_proof_evidence_summary(out: &mut Vec<u8>, proof: Option<&ProofEvidenceSummary>) {
    match proof {
        Some(proof) => {
            put_bool(out, true);
            put_str(out, &proof.schema);
            put_u64(out, u64::from(proof.schema_version));
            put_str(out, &proof.verifier);
            put_str(out, proof.verdict.as_str());
            put_option_str(out, proof.rejection_code.as_ref().map(|code| code.as_str()));
            put_str(out, &proof.target_checksum.to_string());
            put_str(out, &proof.abi_checksum.to_string());
            put_str(out, &proof.layout_checksum.to_string());
            put_str(out, &proof.invalidation_checksum.to_string());
            put_str(out, &proof.proof_policy_checksum.to_string());
            put_str(out, &proof.checksum().to_string());
            put_u64(out, proof.metadata.len() as u64);
            for (key, value) in &proof.metadata {
                put_str(out, key);
                put_str(out, value);
            }
        }
        None => put_bool(out, false),
    }
}

fn sha256_digest(bytes: &[u8]) -> String {
    format!("sha256:{}", sha256_hex(bytes))
}

fn put_bool(out: &mut Vec<u8>, value: bool) {
    out.push(u8::from(value));
}

fn put_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_i64(out: &mut Vec<u8>, value: i64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_str(out: &mut Vec<u8>, value: &str) {
    put_u64(out, value.len() as u64);
    out.extend_from_slice(value.as_bytes());
}

fn put_option_str(out: &mut Vec<u8>, value: Option<&str>) {
    match value {
        Some(value) => {
            put_bool(out, true);
            put_str(out, value);
        }
        None => put_bool(out, false),
    }
}

fn put_option_u64(out: &mut Vec<u8>, value: Option<u64>) {
    match value {
        Some(value) => {
            put_bool(out, true);
            put_u64(out, value);
        }
        None => put_bool(out, false),
    }
}

fn join_ids<'a>(ids: impl Iterator<Item = &'a str>) -> String {
    let mut ids: Vec<_> = ids.collect();
    ids.sort_unstable();
    ids.join(",")
}

fn missing_required_text(value: &str) -> bool {
    value.trim().is_empty()
}
