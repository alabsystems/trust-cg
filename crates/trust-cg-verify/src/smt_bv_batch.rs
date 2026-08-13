// trust-cg-verify/smt_bv_batch.rs - SMT BV batch-template manifests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Non-promoting SMT bitvector batch-template manifest contracts.
//!
//! This module describes the artifact shape used to replay and compare scalar
//! ay proof results against batch-template lanes. It intentionally does not
//! promote or install any generated template; product promotion remains blocked
//! on #660 and #664.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use thiserror::Error;
use trust_cg_opt::cache::StableHasher;

use crate::aarch64_backend_proof_report::{
    AARCH64_BACKEND_PROOF_FAMILY_REPORT_SCHEMA, AARCH64_BACKEND_PROOF_TARGET,
    Aarch64BackendProofEvidenceKind, Aarch64BackendProofFamily, Aarch64BackendProofFamilyReport,
    Aarch64BackendProofRow,
};
use crate::ay_bridge::{AYConfig, AYResult, generate_smt2_query, solver_info};
use crate::lowering_proof::ProofObligation;
use crate::proof_database::{CategorizedProof, ProofCategory, ProofDatabase};
use crate::smt::SmtSort;

/// Stable schema tag for SMT BV batch-template manifests.
pub const SMT_BV_BATCH_TEMPLATE_SCHEMA: &str = "trust-cg.smt_bv_batch_template.v1";

/// Current manifest template version.
pub const SMT_BV_BATCH_TEMPLATE_VERSION: u32 = 1;

/// Proof-policy version for this non-promoting Phase 7 contract slice.
pub const SMT_BV_BATCH_PROOF_POLICY_VERSION: &str = "trust-cg.phase7.smt_bv_batch.non_promoting.v1";

/// Product promotion and install are intentionally blocked for this slice.
pub const SMT_BV_BATCH_PROMOTION_BLOCKERS: [&str; 2] = ["#660", "#664"];

/// Stable schema tag for the AArch64 SMT BV batch proof-consumption report.
pub const AARCH64_SMT_BV_BATCH_PROOF_CONSUMPTION_SCHEMA: &str =
    "trust-cg.aarch64.smt_bv_batch.proof_consumption.v1";

/// Current AArch64 proof-consumption report schema version.
pub const AARCH64_SMT_BV_BATCH_PROOF_CONSUMPTION_VERSION: u32 = 1;

/// Stable, non-authoritative fingerprint for manifest correlation.
///
/// This deliberately has no cache lookup counterpart: a content digest is
/// useful for matching batch lanes to their scalar source, but it is not a
/// proof certificate and can never establish a solver verdict.
fn proof_query_fingerprint(smt2: &str, config_signature: &str, solver: &str) -> u128 {
    let mut hasher = StableHasher::new();
    hasher.write_str(smt2);
    hasher.write_u8(0);
    hasher.write_str(config_signature);
    hasher.write_u8(0);
    hasher.write_str(solver);
    hasher.finish128()
}

fn config_signature(timeout_ms: u64, produce_models: bool) -> String {
    format!("aycfg/v1/timeout_ms={timeout_ms}/produce_models={produce_models}")
}

/// Manifest construction failures.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum SmtBvBatchTemplateError {
    /// A batch template must contain at least one lane.
    #[error("lane_count must be greater than zero")]
    EmptyLaneCount,

    /// The requested ay proof inventory did not contain enough SMT BV proofs.
    #[error(
        "not enough SMT BV proof obligations in {category}: requested {requested}, available {available}"
    )]
    NotEnoughInventory {
        /// Human-readable proof category name.
        category: String,
        /// Requested lane count.
        requested: usize,
        /// Available SMT BV proof obligations in the category.
        available: usize,
    },
}

/// Canonical scalar and batch result statuses for SMT BV batch templates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SmtBvBatchStatus {
    /// Scalar and batch obligations were proven equivalent.
    Verified,
    /// A counterexample refuted the equivalence claim.
    Refuted,
    /// The obligation shape is not supported by the batch template.
    Unsupported,
    /// The solver returned unknown without a supported proof or refutation.
    Unknown,
    /// The solver exceeded the configured timeout budget.
    Timeout,
    /// A cache hit was rejected because its source/proof hash was stale.
    StaleCache,
    /// The verifier or solver path failed internally.
    InternalError,
}

impl SmtBvBatchStatus {
    /// Return the stable status spelling used in manifests.
    pub fn as_str(self) -> &'static str {
        match self {
            SmtBvBatchStatus::Verified => "verified",
            SmtBvBatchStatus::Refuted => "refuted",
            SmtBvBatchStatus::Unsupported => "unsupported",
            SmtBvBatchStatus::Unknown => "unknown",
            SmtBvBatchStatus::Timeout => "timeout",
            SmtBvBatchStatus::StaleCache => "stale_cache",
            SmtBvBatchStatus::InternalError => "internal_error",
        }
    }

    /// Full status vocabulary, in stable manifest order.
    pub fn vocabulary() -> Vec<Self> {
        vec![
            SmtBvBatchStatus::Verified,
            SmtBvBatchStatus::Refuted,
            SmtBvBatchStatus::Unsupported,
            SmtBvBatchStatus::Unknown,
            SmtBvBatchStatus::Timeout,
            SmtBvBatchStatus::StaleCache,
            SmtBvBatchStatus::InternalError,
        ]
    }
}

/// Top-level SMT BV batch-template manifest.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtBvBatchTemplateManifest {
    /// Stable schema tag.
    pub schema: String,
    /// Stable template identity.
    pub template_id: String,
    /// Version of this template schema.
    pub template_version: u32,
    /// Sorted union of bit widths used by all lanes.
    pub bit_widths: Vec<u32>,
    /// Number of batch lanes.
    pub lane_count: usize,
    /// Mapping from ay proof inventory entries to batch lanes.
    pub obligation_batch_layout: SmtBvObligationBatchLayout,
    /// Mapping used to compare scalar results with batch lane results.
    pub scalar_equivalence_layout: SmtBvScalarEquivalenceLayout,
    /// Source hashes for source inventory and formula identity.
    pub source_hashes: Vec<SmtBvTemplateHash>,
    /// Proof hashes for SMT2 query, solver route, and config identity.
    pub proof_hashes: Vec<SmtBvTemplateHash>,
    /// Solver route used for replay and cache keys.
    pub solver_route: SmtBvSolverRoute,
    /// Timeout budget for scalar and batch replay.
    pub timeout_budget: SmtBvTimeoutBudget,
    /// Proof policy governing interpretation of this manifest.
    pub proof_policy_version: String,
    /// Replay inputs needed to reproduce scalar queries and batch lane queries.
    pub replay_inputs: SmtBvReplayInputs,
    /// Stable vocabulary accepted by scalar and batch result slots.
    pub status_vocabulary: Vec<SmtBvBatchStatus>,
    /// Explicit non-promotion/install policy for this slice.
    pub promotion_policy: SmtBvPromotionPolicy,
}

/// Mapping from proof inventory entries to batch lanes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtBvObligationBatchLayout {
    /// Existing inventory path used to source obligations.
    pub inventory_path: String,
    /// Number of lanes in the batch layout.
    pub lane_count: usize,
    /// Per-lane obligation metadata.
    pub lanes: Vec<SmtBvBatchLane>,
}

/// One SMT BV proof obligation assigned to a batch lane.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtBvBatchLane {
    /// Batch lane index.
    pub lane: usize,
    /// Existing inventory path for this exact lane.
    pub inventory_path: String,
    /// Proof obligation name.
    pub obligation_id: String,
    /// Proof database category name.
    pub proof_category: String,
    /// Input bit widths in declaration order.
    pub input_widths: Vec<u32>,
    /// Result bit width for the equivalence expression.
    pub result_width: u32,
    /// Number of preconditions applied before the equivalence check.
    pub precondition_count: usize,
}

/// Scalar-to-batch comparison layout.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtBvScalarEquivalenceLayout {
    /// Comparison rule used for all lanes.
    pub comparison: String,
    /// Scalar result field name.
    pub scalar_result_slot: String,
    /// Batch result field name.
    pub batch_result_slot: String,
    /// Per-lane scalar result mapping.
    pub lanes: Vec<SmtBvScalarEquivalenceLane>,
}

/// One scalar proof result mapped to a batch lane result.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtBvScalarEquivalenceLane {
    /// Batch lane index.
    pub lane: usize,
    /// Scalar proof obligation name.
    pub scalar_obligation_id: String,
    /// Batch proof obligation name.
    pub batch_obligation_id: String,
    /// Counterexample field used when status is `refuted`.
    pub counterexample_slot: String,
}

/// Stable hash metadata for a manifest lane.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtBvTemplateHash {
    /// Batch lane index.
    pub lane: usize,
    /// Proof obligation name.
    pub obligation_id: String,
    /// Hash algorithm tag.
    pub algorithm: String,
    /// Hex digest.
    pub digest: String,
}

/// Solver route recorded in the manifest.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtBvSolverRoute {
    /// Solver backend for this non-promoting slice.
    pub backend: String,
    /// Route kind.
    pub route_kind: String,
    /// Solver descriptor or configured solver path.
    pub solver: String,
    /// Sorted SMT logics used by the lanes.
    pub logics: Vec<String>,
    /// Canonical ay cache config signature.
    pub config_signature: String,
}

/// Timeout budget recorded in the manifest.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtBvTimeoutBudget {
    /// Per-obligation timeout.
    pub per_obligation_ms: u64,
    /// Saturating sum of all lane timeout budgets.
    pub total_budget_ms: u64,
    /// Per-lane timeout budgets.
    pub lane_budgets: Vec<SmtBvLaneTimeoutBudget>,
}

/// Timeout budget for one batch lane.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtBvLaneTimeoutBudget {
    /// Batch lane index.
    pub lane: usize,
    /// Proof obligation name.
    pub obligation_id: String,
    /// Timeout budget in milliseconds.
    pub timeout_ms: u64,
}

/// Replay inputs for scalar and batch verification.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtBvReplayInputs {
    /// Canonical ay cache config signature.
    pub config_signature: String,
    /// Solver descriptor or configured solver path.
    pub solver: String,
    /// Replay lanes.
    pub lanes: Vec<SmtBvReplayLane>,
}

/// Replay metadata for one lane.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtBvReplayLane {
    /// Batch lane index.
    pub lane: usize,
    /// Proof obligation name.
    pub obligation_id: String,
    /// Stable hash of the SMT2 query text.
    pub smt2_query_hash: String,
    /// Stable ay cache key for this query/config/solver tuple.
    pub proof_cache_key: String,
    /// Input symbols in declaration order.
    pub input_symbols: Vec<SmtBvInputSymbol>,
    /// Preconditions in declaration order, represented by stable hashes.
    pub precondition_hashes: Vec<String>,
}

/// Replay input symbol metadata.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtBvInputSymbol {
    /// Symbol name.
    pub name: String,
    /// Bitvector width.
    pub width: u32,
}

/// Promotion policy for this non-promoting slice.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtBvPromotionPolicy {
    /// Product promotion state.
    pub promotion_status: String,
    /// Install state.
    pub install_status: String,
    /// Blocking issues that must be cleared before promotion/install.
    pub blocked_by: Vec<String>,
}

/// One cached or replayed proof outcome supplied to the AArch64 consumer.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtBvAarch64ProofRecord {
    /// AArch64 backend proof report row id.
    pub row_id: String,
    /// Evidence hash observed when this proof/cache record was produced.
    pub evidence_hash: String,
    /// Source report hash observed when this proof/cache record was produced.
    pub source_report_hash: String,
    /// Optional ay cache key or replay artifact id for diagnostics.
    pub proof_cache_key: Option<String>,
    /// Consumed proof outcome.
    pub outcome: SmtBvOutcome,
}

impl SmtBvAarch64ProofRecord {
    /// Build a proof record tied to one row of an AArch64 backend report.
    pub fn from_report_row(
        report: &Aarch64BackendProofFamilyReport,
        row: &Aarch64BackendProofRow,
        outcome: SmtBvOutcome,
    ) -> Self {
        Self {
            row_id: row.row_id.clone(),
            evidence_hash: row.evidence_hash.clone(),
            source_report_hash: report.report_hash.clone(),
            proof_cache_key: None,
            outcome,
        }
    }

    /// Attach a diagnostic proof-cache key to this record.
    pub fn with_proof_cache_key(mut self, proof_cache_key: impl Into<String>) -> Self {
        self.proof_cache_key = Some(proof_cache_key.into());
        self
    }
}

/// AArch64-only proof-consumption report for SMT BV batch evidence.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtBvAarch64ProofConsumptionReport {
    /// Stable schema tag.
    pub schema: String,
    /// Stable schema version.
    pub schema_version: u32,
    /// Source report schema consumed by this report.
    pub source_report_schema: String,
    /// Source report hash consumed by this report.
    pub source_report_hash: String,
    /// AArch64 target triple from the consumed report.
    pub target: String,
    /// Obligation set from the consumed report.
    pub obligation_set: String,
    /// Source report policy disposition.
    pub source_policy_disposition: String,
    /// This report is metadata-only and cannot install code.
    pub metadata_only: bool,
    /// This report does not authorize installable artifacts.
    pub installable: bool,
    /// This report does not authorize product/native promotion.
    pub product_promotion_allowed: bool,
    /// Stable status vocabulary accepted by per-region outcomes.
    pub status_vocabulary: Vec<SmtBvBatchStatus>,
    /// Per-status summary over all emitted regions.
    pub status_counts: SmtBvBatchStatusCounts,
    /// Per-region proof-consumption statuses.
    pub regions: Vec<SmtBvAarch64RegionStatus>,
    /// Explicit non-promotion/install policy for this slice.
    pub promotion_policy: SmtBvPromotionPolicy,
}

/// Per-region AArch64 SMT BV batch proof-consumption status.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtBvAarch64RegionStatus {
    /// AArch64 backend proof report row id.
    pub region_id: String,
    /// AArch64 backend proof family.
    pub family: Aarch64BackendProofFamily,
    /// Source inventory named by the backend proof report row.
    pub source: String,
    /// Report row evidence kind.
    pub evidence_kind: Aarch64BackendProofEvidenceKind,
    /// Proof obligation, contract, or test id.
    pub evidence_id: String,
    /// Evidence hash copied from the source report row.
    pub evidence_hash: String,
    /// Coarse translation-validation category when present.
    pub transval_check_kind: Option<String>,
    /// Input bit widths in declaration order.
    pub input_widths: Vec<u32>,
    /// Number of preconditions in the source proof obligation.
    pub precondition_count: usize,
    /// Result sort copied from the source report row.
    pub result_sort: String,
    /// Optional consumed proof-cache key.
    pub proof_cache_key: Option<String>,
    /// Stable region status.
    pub status: SmtBvBatchStatus,
    /// Full structured outcome for this region.
    pub outcome: SmtBvOutcome,
}

/// Per-status counts for SMT BV batch proof-consumption reports.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtBvBatchStatusCounts {
    /// Number of verified regions.
    pub verified: usize,
    /// Number of refuted regions.
    pub refuted: usize,
    /// Number of unsupported regions.
    pub unsupported: usize,
    /// Number of unknown regions.
    pub unknown: usize,
    /// Number of timed-out regions.
    pub timeout: usize,
    /// Number of stale proof/cache regions.
    pub stale_cache: usize,
    /// Number of internal-error regions.
    pub internal_error: usize,
}

impl SmtBvBatchStatusCounts {
    /// Increment the counter for `status`.
    pub fn record(&mut self, status: SmtBvBatchStatus) {
        match status {
            SmtBvBatchStatus::Verified => self.verified += 1,
            SmtBvBatchStatus::Refuted => self.refuted += 1,
            SmtBvBatchStatus::Unsupported => self.unsupported += 1,
            SmtBvBatchStatus::Unknown => self.unknown += 1,
            SmtBvBatchStatus::Timeout => self.timeout += 1,
            SmtBvBatchStatus::StaleCache => self.stale_cache += 1,
            SmtBvBatchStatus::InternalError => self.internal_error += 1,
        }
    }

    /// Return the counter for `status`.
    pub fn get(&self, status: SmtBvBatchStatus) -> usize {
        match status {
            SmtBvBatchStatus::Verified => self.verified,
            SmtBvBatchStatus::Refuted => self.refuted,
            SmtBvBatchStatus::Unsupported => self.unsupported,
            SmtBvBatchStatus::Unknown => self.unknown,
            SmtBvBatchStatus::Timeout => self.timeout,
            SmtBvBatchStatus::StaleCache => self.stale_cache,
            SmtBvBatchStatus::InternalError => self.internal_error,
        }
    }

    /// Total number of counted regions.
    pub fn total(&self) -> usize {
        self.verified
            + self.refuted
            + self.unsupported
            + self.unknown
            + self.timeout
            + self.stale_cache
            + self.internal_error
    }
}

/// Scalar verifier result for one obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtBvScalarResult {
    /// Proof obligation name.
    pub obligation_id: String,
    /// Scalar result outcome.
    pub outcome: SmtBvOutcome,
}

/// Batch verifier result for one lane.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtBvBatchLaneResult {
    /// Batch lane index.
    pub lane: usize,
    /// Proof obligation name.
    pub obligation_id: String,
    /// Batch result outcome.
    pub outcome: SmtBvOutcome,
}

/// Canonical outcome payload for scalar and batch result slots.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtBvOutcome {
    /// Stable outcome status.
    pub status: SmtBvBatchStatus,
    /// Counterexample values when status is `refuted`.
    pub counterexample: Vec<(String, u64)>,
    /// Optional diagnostic detail.
    pub detail: Option<String>,
}

impl SmtBvOutcome {
    /// Construct an outcome with no counterexample payload.
    pub fn status(status: SmtBvBatchStatus) -> Self {
        Self {
            status,
            counterexample: Vec::new(),
            detail: None,
        }
    }

    /// Construct a refuted outcome with a counterexample payload.
    pub fn refuted(counterexample: Vec<(String, u64)>) -> Self {
        Self {
            status: SmtBvBatchStatus::Refuted,
            counterexample,
            detail: None,
        }
    }

    /// Construct an unsupported outcome.
    pub fn unsupported(reason: impl Into<String>) -> Self {
        Self {
            status: SmtBvBatchStatus::Unsupported,
            counterexample: Vec::new(),
            detail: Some(reason.into()),
        }
    }

    /// Construct a stale-cache outcome.
    pub fn stale_cache(reason: impl Into<String>) -> Self {
        Self {
            status: SmtBvBatchStatus::StaleCache,
            counterexample: Vec::new(),
            detail: Some(reason.into()),
        }
    }

    /// Construct an unknown outcome.
    pub fn unknown(reason: impl Into<String>) -> Self {
        Self {
            status: SmtBvBatchStatus::Unknown,
            counterexample: Vec::new(),
            detail: Some(reason.into()),
        }
    }

    /// Construct an internal-error outcome.
    pub fn internal_error(reason: impl Into<String>) -> Self {
        Self {
            status: SmtBvBatchStatus::InternalError,
            counterexample: Vec::new(),
            detail: Some(reason.into()),
        }
    }
}

impl From<&AYResult> for SmtBvOutcome {
    fn from(result: &AYResult) -> Self {
        match result {
            AYResult::Verified => SmtBvOutcome::status(SmtBvBatchStatus::Verified),
            AYResult::SolverUnsat => {
                SmtBvOutcome::unknown("solver UNSAT lacked an independently accepted exact proof")
            }
            AYResult::CounterExample(cex) => SmtBvOutcome::refuted(cex.clone()),
            AYResult::Timeout => SmtBvOutcome::status(SmtBvBatchStatus::Timeout),
            AYResult::Unknown(msg) => SmtBvOutcome {
                status: SmtBvBatchStatus::Unknown,
                counterexample: Vec::new(),
                detail: Some(msg.clone()),
            },
            AYResult::Error(msg) => SmtBvOutcome {
                status: SmtBvBatchStatus::InternalError,
                counterexample: Vec::new(),
                detail: Some(msg.clone()),
            },
        }
    }
}

/// Result of comparing scalar and batch outcomes for one lane.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SmtBvScalarBatchEquivalence {
    /// Proof obligation name.
    pub obligation_id: String,
    /// Batch lane index.
    pub lane: usize,
    /// Scalar status.
    pub scalar_status: SmtBvBatchStatus,
    /// Batch status.
    pub batch_status: SmtBvBatchStatus,
    /// Whether scalar and batch results are equivalent.
    pub equivalent: bool,
    /// Mismatch reason when not equivalent.
    pub reason: Option<String>,
}

/// Build a non-promoting manifest from the existing ay proof inventory.
pub fn build_smt_bv_batch_template_from_ay_inventory(
    category: ProofCategory,
    lane_count: usize,
    config: &AYConfig,
) -> Result<SmtBvBatchTemplateManifest, SmtBvBatchTemplateError> {
    if lane_count == 0 {
        return Err(SmtBvBatchTemplateError::EmptyLaneCount);
    }

    let db = ProofDatabase::new();
    let candidates: Vec<CategorizedProof> = db
        .by_category(category)
        .into_iter()
        .filter(|proof| is_smt_bv_obligation(&proof.obligation))
        .cloned()
        .collect();

    if candidates.len() < lane_count {
        return Err(SmtBvBatchTemplateError::NotEnoughInventory {
            category: category.name().to_string(),
            requested: lane_count,
            available: candidates.len(),
        });
    }

    let proofs: Vec<CategorizedProof> = candidates.into_iter().take(lane_count).collect();
    let template_id = format!("smt_bv_batch_{}", sanitize_id(category.name()));
    Ok(build_smt_bv_batch_template_manifest(
        template_id,
        format!("ProofDatabase::new().by_category({})", category.name()),
        &proofs,
        config,
    ))
}

/// Build a manifest from already selected categorized proofs.
pub fn build_smt_bv_batch_template_manifest(
    template_id: impl Into<String>,
    inventory_path: impl Into<String>,
    proofs: &[CategorizedProof],
    config: &AYConfig,
) -> SmtBvBatchTemplateManifest {
    let template_id = template_id.into();
    let inventory_path = inventory_path.into();
    let lane_count = proofs.len();
    let cfg_sig = config_signature(config.timeout_ms, config.produce_models);
    let solver = solver_descriptor(config);

    let mut bit_widths = BTreeSet::new();
    let mut logics = BTreeSet::new();
    let mut lanes = Vec::with_capacity(lane_count);
    let mut equivalence_lanes = Vec::with_capacity(lane_count);
    let mut source_hashes = Vec::with_capacity(lane_count);
    let mut proof_hashes = Vec::with_capacity(lane_count);
    let mut replay_lanes = Vec::with_capacity(lane_count);
    let mut lane_budgets = Vec::with_capacity(lane_count);

    for (lane, categorized) in proofs.iter().enumerate() {
        let obligation = &categorized.obligation;
        let result_width = obligation_result_width(obligation).unwrap_or(0);
        for width in obligation_widths(obligation) {
            bit_widths.insert(width);
        }
        if result_width != 0 {
            bit_widths.insert(result_width);
        }

        let smt2 = generate_smt2_query(obligation, config);
        logics.insert(extract_logic(&smt2));
        let proof_cache_key = format!("{:032x}", proof_query_fingerprint(&smt2, &cfg_sig, &solver));
        let source_digest = source_hash_for_obligation(obligation, categorized.category);
        let smt2_query_hash = stable_hash_hex("smt2_query", smt2.as_bytes());

        lanes.push(SmtBvBatchLane {
            lane,
            inventory_path: format!("{}[{}]", inventory_path, lane),
            obligation_id: obligation.name.clone(),
            proof_category: categorized.category.name().to_string(),
            input_widths: obligation.inputs.iter().map(|(_, width)| *width).collect(),
            result_width,
            precondition_count: obligation.preconditions.len(),
        });

        equivalence_lanes.push(SmtBvScalarEquivalenceLane {
            lane,
            scalar_obligation_id: obligation.name.clone(),
            batch_obligation_id: obligation.name.clone(),
            counterexample_slot: format!("lanes[{lane}].counterexample"),
        });

        source_hashes.push(SmtBvTemplateHash {
            lane,
            obligation_id: obligation.name.clone(),
            algorithm: "trust-cg-stable-hash-128".to_string(),
            digest: source_digest,
        });

        proof_hashes.push(SmtBvTemplateHash {
            lane,
            obligation_id: obligation.name.clone(),
            algorithm: "trust-cg-ay-cache-key-128".to_string(),
            digest: proof_cache_key.clone(),
        });

        replay_lanes.push(SmtBvReplayLane {
            lane,
            obligation_id: obligation.name.clone(),
            smt2_query_hash,
            proof_cache_key,
            input_symbols: obligation
                .inputs
                .iter()
                .map(|(name, width)| SmtBvInputSymbol {
                    name: name.clone(),
                    width: *width,
                })
                .collect(),
            precondition_hashes: obligation
                .preconditions
                .iter()
                .map(|precondition| {
                    stable_hash_hex(
                        "smt_bv_precondition",
                        format!("{precondition:?}").as_bytes(),
                    )
                })
                .collect(),
        });

        lane_budgets.push(SmtBvLaneTimeoutBudget {
            lane,
            obligation_id: obligation.name.clone(),
            timeout_ms: config.timeout_ms,
        });
    }

    SmtBvBatchTemplateManifest {
        schema: SMT_BV_BATCH_TEMPLATE_SCHEMA.to_string(),
        template_id,
        template_version: SMT_BV_BATCH_TEMPLATE_VERSION,
        bit_widths: bit_widths.into_iter().collect(),
        lane_count,
        obligation_batch_layout: SmtBvObligationBatchLayout {
            inventory_path,
            lane_count,
            lanes,
        },
        scalar_equivalence_layout: SmtBvScalarEquivalenceLayout {
            comparison: "scalar_status == batch_status; refuted requires identical counterexample"
                .to_string(),
            scalar_result_slot: "scalar.outcome".to_string(),
            batch_result_slot: "batch.lanes[].outcome".to_string(),
            lanes: equivalence_lanes,
        },
        source_hashes,
        proof_hashes,
        solver_route: SmtBvSolverRoute {
            backend: "ay-cli".to_string(),
            route_kind: if config.solver_path.is_some() {
                "config-override".to_string()
            } else {
                "ay-bridge-auto".to_string()
            },
            solver: solver.clone(),
            logics: logics.into_iter().collect(),
            config_signature: cfg_sig.clone(),
        },
        timeout_budget: SmtBvTimeoutBudget {
            per_obligation_ms: config.timeout_ms,
            total_budget_ms: config.timeout_ms.saturating_mul(lane_count as u64),
            lane_budgets,
        },
        proof_policy_version: SMT_BV_BATCH_PROOF_POLICY_VERSION.to_string(),
        replay_inputs: SmtBvReplayInputs {
            config_signature: cfg_sig,
            solver,
            lanes: replay_lanes,
        },
        status_vocabulary: SmtBvBatchStatus::vocabulary(),
        promotion_policy: SmtBvPromotionPolicy {
            promotion_status: "blocked".to_string(),
            install_status: "blocked".to_string(),
            blocked_by: SMT_BV_BATCH_PROMOTION_BLOCKERS
                .iter()
                .map(|issue| (*issue).to_string())
                .collect(),
        },
    }
}

/// Consume an AArch64 backend proof-family report as SMT BV batch evidence.
///
/// This is deliberately report-only: it records proof/cache outcomes by
/// backend proof row, rejects stale hashes, marks non-SMT-BV rows unsupported,
/// and does not install or promote any native dispatch path.
pub fn build_aarch64_smt_bv_batch_proof_consumption_report(
    report: &Aarch64BackendProofFamilyReport,
    proof_records: &[SmtBvAarch64ProofRecord],
) -> SmtBvAarch64ProofConsumptionReport {
    let mut records_by_row: BTreeMap<&str, Vec<&SmtBvAarch64ProofRecord>> = BTreeMap::new();
    for record in proof_records {
        records_by_row
            .entry(record.row_id.as_str())
            .or_default()
            .push(record);
    }

    let report_hash_is_current = report.report_hash == report.compute_report_hash();
    let source_report_is_aarch64 = report.schema == AARCH64_BACKEND_PROOF_FAMILY_REPORT_SCHEMA
        && report.target == AARCH64_BACKEND_PROOF_TARGET;
    let mut regions = Vec::with_capacity(report.rows.len());
    let mut status_counts = SmtBvBatchStatusCounts::default();

    for row in &report.rows {
        let (outcome, proof_cache_key) = consume_aarch64_row(
            report,
            row,
            records_by_row.get(row.row_id.as_str()).map(Vec::as_slice),
            report_hash_is_current,
            source_report_is_aarch64,
        );
        let status = outcome.status;
        status_counts.record(status);
        regions.push(SmtBvAarch64RegionStatus {
            region_id: row.row_id.clone(),
            family: row.family,
            source: row.source.clone(),
            evidence_kind: row.evidence_kind,
            evidence_id: row.evidence_id.clone(),
            evidence_hash: row.evidence_hash.clone(),
            transval_check_kind: row.transval_check_kind.clone(),
            input_widths: row.input_widths.clone(),
            precondition_count: row.precondition_count,
            result_sort: row.result_sort.clone(),
            proof_cache_key,
            status,
            outcome,
        });
    }

    SmtBvAarch64ProofConsumptionReport {
        schema: AARCH64_SMT_BV_BATCH_PROOF_CONSUMPTION_SCHEMA.to_string(),
        schema_version: AARCH64_SMT_BV_BATCH_PROOF_CONSUMPTION_VERSION,
        source_report_schema: report.schema.clone(),
        source_report_hash: report.report_hash.clone(),
        target: report.target.clone(),
        obligation_set: report.obligation_set.clone(),
        source_policy_disposition: report.policy.disposition.clone(),
        metadata_only: true,
        installable: false,
        product_promotion_allowed: false,
        status_vocabulary: SmtBvBatchStatus::vocabulary(),
        status_counts,
        regions,
        promotion_policy: SmtBvPromotionPolicy {
            promotion_status: "blocked".to_string(),
            install_status: "blocked".to_string(),
            blocked_by: SMT_BV_BATCH_PROMOTION_BLOCKERS
                .iter()
                .map(|issue| (*issue).to_string())
                .collect(),
        },
    }
}

/// Return true when the obligation is a pure bitvector equivalence check.
pub fn is_smt_bv_obligation(obligation: &ProofObligation) -> bool {
    if !obligation.fp_inputs.is_empty() {
        return false;
    }

    matches!(
        (obligation.trust_ir_expr.sort(), obligation.aarch64_expr.sort()),
        (SmtSort::BitVec(lhs), SmtSort::BitVec(rhs)) if lhs == rhs
    )
}

fn consume_aarch64_row(
    report: &Aarch64BackendProofFamilyReport,
    row: &Aarch64BackendProofRow,
    records: Option<&[&SmtBvAarch64ProofRecord]>,
    report_hash_is_current: bool,
    source_report_is_aarch64: bool,
) -> (SmtBvOutcome, Option<String>) {
    if !source_report_is_aarch64 {
        return (
            SmtBvOutcome::internal_error("source report is not the canonical AArch64 report"),
            None,
        );
    }

    if !report_hash_is_current {
        return (
            SmtBvOutcome::stale_cache("source report hash does not match report payload"),
            None,
        );
    }

    if let Some(reason) = unsupported_aarch64_row_reason(row) {
        return (SmtBvOutcome::unsupported(reason), None);
    }

    let Some(records) = records else {
        return (
            SmtBvOutcome::unknown("no consumed proof/cache record for region"),
            None,
        );
    };

    if records.len() != 1 {
        return (
            SmtBvOutcome::internal_error(format!(
                "expected one proof/cache record for region {}, found {}",
                row.row_id,
                records.len()
            )),
            None,
        );
    }

    let record = records[0];
    if record.evidence_hash != row.evidence_hash {
        return (
            SmtBvOutcome::stale_cache("proof/cache evidence hash does not match report row"),
            record.proof_cache_key.clone(),
        );
    }
    if record.source_report_hash != report.report_hash {
        return (
            SmtBvOutcome::stale_cache("proof/cache source report hash does not match report"),
            record.proof_cache_key.clone(),
        );
    }

    (record.outcome.clone(), record.proof_cache_key.clone())
}

fn unsupported_aarch64_row_reason(row: &Aarch64BackendProofRow) -> Option<String> {
    if row.evidence_kind != Aarch64BackendProofEvidenceKind::ProofObligation {
        return Some(format!(
            "{} evidence is metadata-only and unsupported by SMT BV batch consumption",
            row.evidence_kind.as_str()
        ));
    }

    if !row.fp_input_widths.is_empty() {
        return Some("floating-point inputs are outside the SMT BV batch slice".to_string());
    }

    if !is_bv_result_sort(&row.result_sort) {
        return Some(format!(
            "result sort {} is outside the SMT BV batch slice",
            row.result_sort
        ));
    }

    if row.input_widths.contains(&0) {
        return Some("zero-width bitvector input is unsupported".to_string());
    }

    None
}

fn is_bv_result_sort(result_sort: &str) -> bool {
    result_sort
        .strip_prefix("bv")
        .and_then(|width| width.parse::<u32>().ok())
        .is_some_and(|width| width > 0)
}

/// Compare one scalar result with its corresponding batch lane result.
pub fn compare_scalar_and_batch_outcome(
    scalar: &SmtBvScalarResult,
    batch: &SmtBvBatchLaneResult,
) -> SmtBvScalarBatchEquivalence {
    let mut equivalent = true;
    let mut reason = None;

    if scalar.obligation_id != batch.obligation_id {
        equivalent = false;
        reason = Some(format!(
            "obligation mismatch: scalar={} batch={}",
            scalar.obligation_id, batch.obligation_id
        ));
    } else if scalar.outcome.status != batch.outcome.status {
        equivalent = false;
        reason = Some(format!(
            "status mismatch: scalar={} batch={}",
            scalar.outcome.status.as_str(),
            batch.outcome.status.as_str()
        ));
    } else if scalar.outcome.status == SmtBvBatchStatus::Refuted
        && scalar.outcome.counterexample != batch.outcome.counterexample
    {
        equivalent = false;
        reason = Some("counterexample mismatch".to_string());
    }

    SmtBvScalarBatchEquivalence {
        obligation_id: scalar.obligation_id.clone(),
        lane: batch.lane,
        scalar_status: scalar.outcome.status,
        batch_status: batch.outcome.status,
        equivalent,
        reason,
    }
}

fn obligation_widths(obligation: &ProofObligation) -> Vec<u32> {
    obligation.inputs.iter().map(|(_, width)| *width).collect()
}

fn obligation_result_width(obligation: &ProofObligation) -> Option<u32> {
    match obligation.trust_ir_expr.sort() {
        SmtSort::BitVec(width) => Some(width),
        _ => None,
    }
}

fn source_hash_for_obligation(obligation: &ProofObligation, category: ProofCategory) -> String {
    let source = format!(
        "category={};name={};inputs={:?};preconditions={:?};formula={:?}",
        category.name(),
        obligation.name,
        obligation.inputs,
        obligation.preconditions,
        obligation.negated_equivalence()
    );
    stable_hash_hex("smt_bv_source", source.as_bytes())
}

fn stable_hash_hex(domain: &str, bytes: &[u8]) -> String {
    let mut hasher = StableHasher::new();
    hasher.write_str(domain);
    hasher.write_framed(bytes);
    format!("{:032x}", hasher.finish128())
}

fn extract_logic(smt2: &str) -> String {
    smt2.lines()
        .map(str::trim)
        .find_map(|line| {
            line.strip_prefix("(set-logic ")
                .and_then(|rest| rest.strip_suffix(')'))
                .map(str::to_string)
        })
        .unwrap_or_else(|| "unknown".to_string())
}

fn solver_descriptor(config: &AYConfig) -> String {
    config.solver_path.clone().unwrap_or_else(solver_info)
}

fn sanitize_id(raw: &str) -> String {
    let mut out = String::with_capacity(raw.len());
    let mut last_was_sep = false;

    for ch in raw.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch.to_ascii_lowercase());
            last_was_sep = false;
        } else if !last_was_sep {
            out.push('_');
            last_was_sep = true;
        }
    }

    out.trim_matches('_').to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scalar_result(status: SmtBvBatchStatus) -> SmtBvScalarResult {
        SmtBvScalarResult {
            obligation_id: "proof_0".to_string(),
            outcome: SmtBvOutcome::status(status),
        }
    }

    fn batch_result(status: SmtBvBatchStatus) -> SmtBvBatchLaneResult {
        SmtBvBatchLaneResult {
            lane: 0,
            obligation_id: "proof_0".to_string(),
            outcome: SmtBvOutcome::status(status),
        }
    }

    #[test]
    fn smt_bv_batch_status_vocabulary_is_stable() {
        let vocabulary: Vec<&str> = SmtBvBatchStatus::vocabulary()
            .into_iter()
            .map(SmtBvBatchStatus::as_str)
            .collect();
        assert_eq!(
            vocabulary,
            vec![
                "verified",
                "refuted",
                "unsupported",
                "unknown",
                "timeout",
                "stale_cache",
                "internal_error",
            ]
        );
    }

    #[test]
    fn smt_bv_batch_manifest_from_ay_inventory_has_contract_fields() {
        let config = AYConfig::default().with_timeout(1_234);
        let manifest =
            build_smt_bv_batch_template_from_ay_inventory(ProofCategory::Arithmetic, 4, &config)
                .expect("arithmetic ay inventory should contain SMT BV obligations");

        assert_eq!(manifest.schema, SMT_BV_BATCH_TEMPLATE_SCHEMA);
        assert_eq!(manifest.template_id, "smt_bv_batch_arithmetic");
        assert_eq!(manifest.template_version, SMT_BV_BATCH_TEMPLATE_VERSION);
        assert_eq!(
            manifest.proof_policy_version,
            SMT_BV_BATCH_PROOF_POLICY_VERSION
        );
        assert_eq!(manifest.lane_count, 4);
        assert!(!manifest.bit_widths.is_empty());
        assert!(
            manifest
                .obligation_batch_layout
                .lanes
                .iter()
                .flat_map(|lane| lane.input_widths.iter().copied())
                .all(|width| manifest.bit_widths.contains(&width))
        );
        assert_eq!(
            manifest.obligation_batch_layout.inventory_path,
            "ProofDatabase::new().by_category(Arithmetic)"
        );
        assert_eq!(manifest.obligation_batch_layout.lanes.len(), 4);
        assert_eq!(manifest.scalar_equivalence_layout.lanes.len(), 4);
        assert_eq!(manifest.source_hashes.len(), 4);
        assert_eq!(manifest.proof_hashes.len(), 4);
        assert!(
            manifest
                .source_hashes
                .iter()
                .all(|hash| hash.digest.len() == 32)
        );
        assert!(
            manifest
                .proof_hashes
                .iter()
                .all(|hash| hash.digest.len() == 32)
        );
        assert_eq!(manifest.timeout_budget.per_obligation_ms, 1_234);
        assert_eq!(manifest.timeout_budget.total_budget_ms, 4_936);
        assert_eq!(manifest.replay_inputs.lanes.len(), 4);
        assert_eq!(
            manifest
                .status_vocabulary
                .iter()
                .map(|status| status.as_str())
                .collect::<Vec<_>>(),
            vec![
                "verified",
                "refuted",
                "unsupported",
                "unknown",
                "timeout",
                "stale_cache",
                "internal_error",
            ]
        );
        assert_eq!(
            manifest.promotion_policy.blocked_by,
            vec!["#660".to_string(), "#664".to_string()]
        );
        assert_eq!(manifest.promotion_policy.promotion_status, "blocked");
        assert_eq!(manifest.promotion_policy.install_status, "blocked");

        let json = serde_json::to_value(&manifest).expect("manifest should serialize");
        assert_eq!(json["template_id"], "smt_bv_batch_arithmetic");
        assert_eq!(json["status_vocabulary"][5], "stale_cache");
    }

    #[test]
    fn smt_bv_batch_scalar_batch_equivalence_covers_terminal_statuses() {
        for status in [
            SmtBvBatchStatus::Verified,
            SmtBvBatchStatus::Unsupported,
            SmtBvBatchStatus::Unknown,
            SmtBvBatchStatus::Timeout,
            SmtBvBatchStatus::StaleCache,
            SmtBvBatchStatus::InternalError,
        ] {
            let scalar = scalar_result(status);
            let batch = batch_result(status);
            let equivalence = compare_scalar_and_batch_outcome(&scalar, &batch);
            assert!(
                equivalence.equivalent,
                "status {} should compare equivalent",
                status.as_str()
            );
            assert_eq!(equivalence.reason, None);
        }
    }

    #[test]
    fn smt_bv_batch_scalar_batch_equivalence_covers_refuted_counterexamples() {
        let scalar = SmtBvScalarResult {
            obligation_id: "proof_0".to_string(),
            outcome: SmtBvOutcome::refuted(vec![("x".to_string(), 0x2a)]),
        };
        let batch = SmtBvBatchLaneResult {
            lane: 0,
            obligation_id: "proof_0".to_string(),
            outcome: SmtBvOutcome::refuted(vec![("x".to_string(), 0x2a)]),
        };
        let equivalence = compare_scalar_and_batch_outcome(&scalar, &batch);
        assert!(equivalence.equivalent);

        let stale_batch = SmtBvBatchLaneResult {
            lane: 0,
            obligation_id: "proof_0".to_string(),
            outcome: SmtBvOutcome::refuted(vec![("x".to_string(), 0x2b)]),
        };
        let mismatch = compare_scalar_and_batch_outcome(&scalar, &stale_batch);
        assert!(!mismatch.equivalent);
        assert_eq!(mismatch.reason, Some("counterexample mismatch".to_string()));
    }

    #[test]
    fn smt_bv_batch_scalar_batch_equivalence_rejects_mismatched_status() {
        let scalar = scalar_result(SmtBvBatchStatus::Verified);
        let batch = batch_result(SmtBvBatchStatus::Timeout);
        let equivalence = compare_scalar_and_batch_outcome(&scalar, &batch);
        assert!(!equivalence.equivalent);
        assert_eq!(
            equivalence.reason,
            Some("status mismatch: scalar=verified batch=timeout".to_string())
        );
    }

    #[test]
    fn smt_bv_batch_ay_result_mapping_matches_status_vocabulary() {
        assert_eq!(
            SmtBvOutcome::from(&AYResult::Verified).status,
            SmtBvBatchStatus::Verified
        );
        let solver_unsat = SmtBvOutcome::from(&AYResult::SolverUnsat);
        assert_eq!(solver_unsat.status, SmtBvBatchStatus::Unknown);
        assert!(
            solver_unsat
                .detail
                .as_deref()
                .is_some_and(|detail| detail.contains("independently accepted"))
        );
        assert_eq!(
            SmtBvOutcome::from(&AYResult::CounterExample(vec![("x".to_string(), 7)])).status,
            SmtBvBatchStatus::Refuted
        );
        assert_eq!(
            SmtBvOutcome::from(&AYResult::Timeout).status,
            SmtBvBatchStatus::Timeout
        );
        assert_eq!(
            SmtBvOutcome::from(&AYResult::Unknown("incomplete".to_string())).status,
            SmtBvBatchStatus::Unknown
        );
        assert_eq!(
            SmtBvOutcome::from(&AYResult::Error("solver panic".to_string())).status,
            SmtBvBatchStatus::InternalError
        );
        assert_eq!(
            SmtBvOutcome::unsupported("quantifier outside template").status,
            SmtBvBatchStatus::Unsupported
        );
        assert_eq!(
            SmtBvOutcome::stale_cache("source hash changed").status,
            SmtBvBatchStatus::StaleCache
        );
    }
}
