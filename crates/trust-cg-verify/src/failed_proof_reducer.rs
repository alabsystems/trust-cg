// trust-cg-verify/failed_proof_reducer.rs - failed rewrite proof reducer artifacts
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Stable reducer artifacts and follow-up templates for failed rewrite proofs.
//!
//! This module consumes verify-side [`RewriteAdmissionRecord`] metadata and
//! produces serializable records for human triage. It deliberately does not
//! register dynamic rewrites or perform product promotion.

use crate::cegis::ConcreteInput;
use crate::rewrite_admission::{
    AdmissionState, CostContext, CounterexampleValue, KernelAllowlist, ProductGateEvidence,
    ProofAssumption, ProofFailureKind, ReducerMetadata, RewriteAdmissionRecord, SolverEvidence,
    SourceRegionIdentity, TargetAbiLayoutIdentity, TransformIdentity,
};
use serde::{Deserialize, Serialize};
use trust_cg_opt::cache::StableHasher;

/// Schema name for serialized failed proof reducer artifacts.
pub const FAILED_PROOF_REDUCER_ARTIFACT_SCHEMA: &str = "trust-cg.failed_proof_reducer_artifact.v1";

/// Numeric schema version for failed proof reducer artifacts.
pub const FAILED_PROOF_REDUCER_ARTIFACT_SCHEMA_VERSION: u32 = 1;

/// Parent issue that owns the failed-proof reducer/follow-up slice.
pub const FAILED_PROOF_REDUCER_PARENT_ISSUE: u64 = 798;

/// Schema name for fuel-only failed-proof counterexample corpora.
pub const FAILED_PROOF_COUNTEREXAMPLE_CORPUS_SCHEMA: &str =
    "trust-cg.failed_proof_counterexample_corpus.v1";

/// Numeric schema version for failed-proof counterexample corpora.
pub const FAILED_PROOF_COUNTEREXAMPLE_CORPUS_SCHEMA_VERSION: u32 = 1;

const FAILED_PROOF_REDUCER_DEFAULT_REDUCER_ID: &str = "trust-cg-verify.failed-proof-reducer";

/// Stable artifact record for one failed solver proof or product-gate mismatch.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FailedProofReducerArtifact {
    /// Stable schema name.
    pub schema: String,
    /// Stable schema version.
    pub schema_version: u32,
    /// Parent issue for this artifact family.
    pub parent_issue: u64,
    /// Stable artifact identity derived from admission and failure metadata.
    pub artifact_id: String,
    /// Failure classification used for triage.
    pub failure_kind: ProofFailureKind,
    /// Source kernel region covered by the failed candidate.
    pub source_region: SourceRegionIdentity,
    /// Explicit proof assumptions recorded on the admission candidate.
    pub proof_assumptions: Vec<ProofAssumption>,
    /// Target ABI and layout identity used for proof/cost replay.
    pub target: TargetAbiLayoutIdentity,
    /// Cost-model context from the admission candidate.
    pub cost_context: CostContext,
    /// Candidate transform identity.
    pub transform: TransformIdentity,
    /// Admission state observed when the artifact was built.
    pub admission_state: AdmissionState,
    /// AArch64 cost delta from the admission candidate.
    pub aarch64_cost_delta: i64,
    /// Named-kernel allowlist metadata.
    pub allowlist: KernelAllowlist,
    /// Product gate state observed when the artifact was built.
    pub product_gates: ProductGateEvidence,
    /// Existing reducer metadata, when the admission failure carried it.
    pub reducer: Option<ReducerMetadata>,
    /// Reduced solver/admission evidence for the failure.
    pub evidence: FailedProofEvidenceSummary,
    /// Follow-up issue template for the classified failure.
    pub follow_up: FailedProofFollowUpTemplate,
}

impl FailedProofReducerArtifact {
    /// Build an artifact from a failed admission record.
    ///
    /// Existing [`ReducerMetadata`] on counterexample or inconclusive evidence
    /// is treated as authoritative. Without reducer metadata, only concrete
    /// counterexamples and allowlisted proved candidates with missing product
    /// gates are classified.
    pub fn from_admission_record(record: &RewriteAdmissionRecord) -> Option<Self> {
        let failure_kind = classify_failed_admission_record(record)?;
        let evidence = failed_evidence_summary(record, failure_kind)?;
        let reducer = evidence_reducer_metadata(&record.evidence).cloned();
        let artifact_id = stable_artifact_id(record, failure_kind, reducer.as_ref(), &evidence);
        let follow_up = FailedProofFollowUpTemplate::from_failure(
            failure_kind,
            record,
            reducer.as_ref(),
            &artifact_id,
            &evidence,
        );

        Some(Self {
            schema: FAILED_PROOF_REDUCER_ARTIFACT_SCHEMA.to_string(),
            schema_version: FAILED_PROOF_REDUCER_ARTIFACT_SCHEMA_VERSION,
            parent_issue: FAILED_PROOF_REDUCER_PARENT_ISSUE,
            artifact_id,
            failure_kind,
            source_region: record.source_region.clone(),
            proof_assumptions: record.proof_assumptions.clone(),
            target: record.target.clone(),
            cost_context: record.cost_context.clone(),
            transform: record.transform.clone(),
            admission_state: record.admission_state,
            aarch64_cost_delta: record.aarch64_cost_delta,
            allowlist: record.allowlist.clone(),
            product_gates: record.product_gates.clone(),
            reducer,
            evidence,
            follow_up,
        })
    }

    /// Serialize the artifact as stable JSON.
    pub fn to_json_pretty(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Deserialize an artifact from stable JSON.
    pub fn from_json_str(json: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(json)
    }
}

/// Explicit opt-in filter for turning failed-proof artifacts into CEGIS fuel.
///
/// The default is disabled. Even when enabled, construction fails closed unless
/// the caller provides a source region, target identity, and the exact variable
/// names expected by the CEGIS obligation that will consume the seeds.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FailedProofCounterexampleSeedFilter {
    /// Whether failed-proof counterexample reuse is enabled.
    pub enabled: bool,
    /// Source region that must exactly match the artifact source identity.
    pub source_region: Option<SourceRegionIdentity>,
    /// Target identity that must exactly match the artifact target identity.
    pub target: Option<TargetAbiLayoutIdentity>,
    /// Variable names expected by the consuming CEGIS obligation.
    pub variable_names: Vec<String>,
}

impl FailedProofCounterexampleSeedFilter {
    /// Build a disabled filter.
    pub fn disabled() -> Self {
        Self::default()
    }

    /// Build an enabled filter for one exact source/target/variable scope.
    pub fn enabled(
        source_region: SourceRegionIdentity,
        target: TargetAbiLayoutIdentity,
        variable_names: Vec<String>,
    ) -> Self {
        Self {
            enabled: true,
            source_region: Some(source_region),
            target: Some(target),
            variable_names,
        }
    }

    fn ready(&self) -> Option<(&SourceRegionIdentity, &TargetAbiLayoutIdentity)> {
        if !self.enabled || self.variable_names.is_empty() {
            return None;
        }
        Some((self.source_region.as_ref()?, self.target.as_ref()?))
    }
}

/// Fuel-only counterexample corpus built from rejected failed-proof artifacts.
///
/// This type is deliberately separate from admission records, reducer
/// artifacts, [`crate::synthesis::ProvenRuleDb`], and
/// [`crate::cegis_pass::CegisCacheEntry`]. It stores only concrete inputs and
/// the source/target metadata needed to make reuse fail closed.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FailedProofCounterexampleCorpus {
    /// Stable corpus schema name.
    pub schema: String,
    /// Stable corpus schema version.
    pub schema_version: u32,
    /// Parent issue for this fuel-only corpus family.
    pub parent_issue: u64,
    /// Fuel-only counterexample seeds.
    pub seeds: Vec<FailedProofCounterexampleSeed>,
}

impl FailedProofCounterexampleCorpus {
    /// Fresh empty corpus with the current schema.
    pub fn empty() -> Self {
        Self {
            schema: FAILED_PROOF_COUNTEREXAMPLE_CORPUS_SCHEMA.to_string(),
            schema_version: FAILED_PROOF_COUNTEREXAMPLE_CORPUS_SCHEMA_VERSION,
            parent_issue: FAILED_PROOF_REDUCER_PARENT_ISSUE,
            seeds: Vec::new(),
        }
    }

    /// Build a corpus from reducer artifacts under an explicit opt-in filter.
    pub fn from_artifacts<'a>(
        artifacts: impl IntoIterator<Item = &'a FailedProofReducerArtifact>,
        filter: &FailedProofCounterexampleSeedFilter,
    ) -> Self {
        let mut corpus = Self::empty();
        for artifact in artifacts {
            if let Some(seed) = FailedProofCounterexampleSeed::from_artifact(artifact, filter) {
                corpus.seeds.push(seed);
            }
        }
        corpus
    }

    /// Number of fuel seeds in the corpus.
    pub fn len(&self) -> usize {
        self.seeds.len()
    }

    /// True when the corpus contains no fuel seeds.
    pub fn is_empty(&self) -> bool {
        self.seeds.is_empty()
    }

    /// Return concrete CEGIS inputs whose source, target, and variable set
    /// exactly match the consuming obligation.
    pub fn concrete_inputs_for_scope(
        &self,
        source_region: &SourceRegionIdentity,
        target: &TargetAbiLayoutIdentity,
        variable_names: &[String],
    ) -> Vec<ConcreteInput> {
        if self.schema != FAILED_PROOF_COUNTEREXAMPLE_CORPUS_SCHEMA
            || self.schema_version != FAILED_PROOF_COUNTEREXAMPLE_CORPUS_SCHEMA_VERSION
            || self.parent_issue != FAILED_PROOF_REDUCER_PARENT_ISSUE
        {
            return Vec::new();
        }

        self.seeds
            .iter()
            .filter(|seed| seed.matches_scope(source_region, target, variable_names))
            .map(FailedProofCounterexampleSeed::to_concrete_input)
            .collect()
    }
}

impl Default for FailedProofCounterexampleCorpus {
    fn default() -> Self {
        Self::empty()
    }
}

/// One concrete failed-proof counterexample usable only as optimizer fuel.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FailedProofCounterexampleSeed {
    /// Stable seed schema name.
    pub schema: String,
    /// Stable seed schema version.
    pub schema_version: u32,
    /// Parent issue for this fuel-only seed family.
    pub parent_issue: u64,
    /// Stable seed identity derived only from fuel-safe fields.
    pub seed_id: String,
    /// Source identity used to constrain reuse.
    pub source_region: SourceRegionIdentity,
    /// Target identity used to constrain reuse.
    pub target: TargetAbiLayoutIdentity,
    /// Sorted concrete variable assignments.
    pub values: Vec<CounterexampleValue>,
    /// Whether fast concrete evaluation originally found the counterexample.
    pub found_by_concrete: bool,
}

impl FailedProofCounterexampleSeed {
    /// Build a fuel seed from a reducer artifact when every guard matches.
    pub fn from_artifact(
        artifact: &FailedProofReducerArtifact,
        filter: &FailedProofCounterexampleSeedFilter,
    ) -> Option<Self> {
        let (expected_source, expected_target) = filter.ready()?;
        if artifact.schema != FAILED_PROOF_REDUCER_ARTIFACT_SCHEMA
            || artifact.schema_version != FAILED_PROOF_REDUCER_ARTIFACT_SCHEMA_VERSION
            || artifact.parent_issue != FAILED_PROOF_REDUCER_PARENT_ISSUE
            || artifact.admission_state != AdmissionState::Rejected
            || artifact.failure_kind != ProofFailureKind::BadCandidate
            || !source_region_matches(&artifact.source_region, expected_source)
            || !target_matches(&artifact.target, expected_target)
        {
            return None;
        }

        let FailedProofEvidenceSummary::Counterexample {
            values,
            found_by_concrete,
        } = &artifact.evidence
        else {
            return None;
        };
        if !variable_names_match(values, &filter.variable_names) {
            return None;
        }

        let mut values = values.clone();
        values.sort_by(|lhs, rhs| lhs.name.cmp(&rhs.name).then(lhs.value.cmp(&rhs.value)));
        let seed_id = stable_seed_id(
            &artifact.source_region,
            &artifact.target,
            &values,
            *found_by_concrete,
        );

        Some(Self {
            schema: FAILED_PROOF_COUNTEREXAMPLE_CORPUS_SCHEMA.to_string(),
            schema_version: FAILED_PROOF_COUNTEREXAMPLE_CORPUS_SCHEMA_VERSION,
            parent_issue: FAILED_PROOF_REDUCER_PARENT_ISSUE,
            seed_id,
            source_region: artifact.source_region.clone(),
            target: artifact.target.clone(),
            values,
            found_by_concrete: *found_by_concrete,
        })
    }

    /// Convert this fuel seed to a concrete CEGIS input.
    pub fn to_concrete_input(&self) -> ConcreteInput {
        let mut input = ConcreteInput::new();
        for value in &self.values {
            input.insert(value.name.clone(), value.value);
        }
        input
    }

    fn matches_scope(
        &self,
        source_region: &SourceRegionIdentity,
        target: &TargetAbiLayoutIdentity,
        variable_names: &[String],
    ) -> bool {
        self.schema == FAILED_PROOF_COUNTEREXAMPLE_CORPUS_SCHEMA
            && self.schema_version == FAILED_PROOF_COUNTEREXAMPLE_CORPUS_SCHEMA_VERSION
            && self.parent_issue == FAILED_PROOF_REDUCER_PARENT_ISSUE
            && source_region_matches(&self.source_region, source_region)
            && target_matches(&self.target, target)
            && variable_names_match(&self.values, variable_names)
    }
}

/// Reduced evidence attached to a failed proof artifact.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum FailedProofEvidenceSummary {
    /// Solver or concrete evaluation found a counterexample.
    Counterexample {
        /// Sorted variable values.
        values: Vec<CounterexampleValue>,
        /// Whether fast concrete evaluation found the counterexample.
        found_by_concrete: bool,
    },
    /// The solver did not produce a proof or concrete counterexample.
    Inconclusive {
        /// Inconclusive reason from admission metadata.
        reason: String,
    },
    /// Proof succeeded, but product gates rejected promotion.
    ProductGateMismatch {
        /// ay/CEGIS proof hash when available.
        proof_hash: Option<u64>,
        /// Missing product gates.
        missing_gates: Vec<ProductGateName>,
    },
}

/// Product gates tracked in reducer follow-up artifacts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ProductGateName {
    /// Replay gate.
    Replay,
    /// Telemetry guard.
    TelemetryGuard,
    /// Rollback or deopt gate.
    RollbackOrDeopt,
    /// Product promotion approval gate.
    ProductPromotion,
}

impl ProductGateName {
    /// Stable snake-case gate name.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Replay => "replay",
            Self::TelemetryGuard => "telemetry_guard",
            Self::RollbackOrDeopt => "rollback_or_deopt",
            Self::ProductPromotion => "product_promotion",
        }
    }
}

/// Serializable follow-up issue template for one failed proof artifact.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FailedProofFollowUpTemplate {
    /// Suggested issue title.
    pub title: String,
    /// Suggested existing labels.
    pub labels: Vec<String>,
    /// Suggested issue body.
    pub body: String,
}

impl FailedProofFollowUpTemplate {
    fn from_failure(
        failure_kind: ProofFailureKind,
        record: &RewriteAdmissionRecord,
        reducer: Option<&ReducerMetadata>,
        artifact_id: &str,
        evidence: &FailedProofEvidenceSummary,
    ) -> Self {
        let title = reducer
            .and_then(|metadata| metadata.follow_up_issue_title.clone())
            .unwrap_or_else(|| default_follow_up_title(failure_kind, record));
        let labels = default_follow_up_labels(failure_kind);
        let body = follow_up_body(failure_kind, record, reducer, artifact_id, evidence);

        Self {
            title,
            labels,
            body,
        }
    }
}

/// Classify a failed admission record using existing reducer metadata first.
pub fn classify_failed_admission_record(
    record: &RewriteAdmissionRecord,
) -> Option<ProofFailureKind> {
    if let Some(reducer) = evidence_reducer_metadata(&record.evidence) {
        return Some(reducer.failure_kind);
    }

    match &record.evidence {
        SolverEvidence::Counterexample { .. } => Some(ProofFailureKind::BadCandidate),
        SolverEvidence::Inconclusive { reason, .. } => classify_inconclusive_reason(reason),
        SolverEvidence::AYEquivalenceProof { .. } if product_gates_mismatch(record) => {
            Some(ProofFailureKind::ProductGateMismatch)
        }
        _ => None,
    }
}

/// Return the product gates that are not satisfied.
pub fn missing_product_gates(gates: &ProductGateEvidence) -> Vec<ProductGateName> {
    let mut missing = Vec::new();
    if !gates.replay_passed {
        missing.push(ProductGateName::Replay);
    }
    if !gates.telemetry_guarded {
        missing.push(ProductGateName::TelemetryGuard);
    }
    if !gates.rollback_or_deopt_available {
        missing.push(ProductGateName::RollbackOrDeopt);
    }
    if !gates.product_promotion_approved {
        missing.push(ProductGateName::ProductPromotion);
    }
    missing
}

fn evidence_reducer_metadata(evidence: &SolverEvidence) -> Option<&ReducerMetadata> {
    match evidence {
        SolverEvidence::Counterexample {
            reducer: Some(reducer),
            ..
        }
        | SolverEvidence::Inconclusive {
            reducer: Some(reducer),
            ..
        } => Some(reducer),
        _ => None,
    }
}

fn classify_inconclusive_reason(reason: &str) -> Option<ProofFailureKind> {
    let reason = reason.to_ascii_lowercase();
    if reason.contains("precondition")
        || reason.contains("assumption")
        || reason.contains("invariant")
    {
        return Some(ProofFailureKind::MissingProofPrecondition);
    }
    if reason.contains("lowering") || reason.contains("semantics") {
        return Some(ProofFailureKind::LoweringOrSemanticsBug);
    }
    None
}

fn product_gates_mismatch(record: &RewriteAdmissionRecord) -> bool {
    record.allowlist.allowlisted
        && record
            .allowlist
            .matches_source_region(&record.source_region)
        && !record.product_gates.all_passed()
}

fn failed_evidence_summary(
    record: &RewriteAdmissionRecord,
    failure_kind: ProofFailureKind,
) -> Option<FailedProofEvidenceSummary> {
    match &record.evidence {
        SolverEvidence::Counterexample { counterexample, .. } => {
            let mut values = counterexample.values.clone();
            values.sort_by(|lhs, rhs| lhs.name.cmp(&rhs.name).then(lhs.value.cmp(&rhs.value)));
            Some(FailedProofEvidenceSummary::Counterexample {
                values,
                found_by_concrete: counterexample.found_by_concrete,
            })
        }
        SolverEvidence::Inconclusive { reason, .. } => {
            Some(FailedProofEvidenceSummary::Inconclusive {
                reason: reason.clone(),
            })
        }
        SolverEvidence::AYEquivalenceProof { proof_hash, .. }
            if failure_kind == ProofFailureKind::ProductGateMismatch =>
        {
            Some(FailedProofEvidenceSummary::ProductGateMismatch {
                proof_hash: Some(*proof_hash),
                missing_gates: missing_product_gates(&record.product_gates),
            })
        }
        _ => None,
    }
}

fn stable_artifact_id(
    record: &RewriteAdmissionRecord,
    failure_kind: ProofFailureKind,
    reducer: Option<&ReducerMetadata>,
    evidence: &FailedProofEvidenceSummary,
) -> String {
    let mut hasher = StableHasher::new();
    hasher.write_str(FAILED_PROOF_REDUCER_ARTIFACT_SCHEMA);
    hasher.write_u32(FAILED_PROOF_REDUCER_ARTIFACT_SCHEMA_VERSION);
    hasher.write_str(failure_kind_tag(failure_kind));
    hash_source_region(&mut hasher, &record.source_region);
    hash_proof_assumptions(&mut hasher, &record.proof_assumptions);
    hash_target(&mut hasher, &record.target);
    hash_cost_context(&mut hasher, &record.cost_context);
    hash_transform(&mut hasher, &record.transform);
    hasher.write_str(admission_state_tag(record.admission_state));
    hasher.write(&record.aarch64_cost_delta.to_le_bytes());
    hash_allowlist(&mut hasher, &record.allowlist);
    hash_product_gates(&mut hasher, &record.product_gates);
    hash_evidence(&mut hasher, evidence);
    hash_reducer(&mut hasher, reducer);
    format!("trust-cg-failed-proof-reducer:{:032x}", hasher.finish128())
}

fn stable_seed_id(
    source_region: &SourceRegionIdentity,
    target: &TargetAbiLayoutIdentity,
    values: &[CounterexampleValue],
    found_by_concrete: bool,
) -> String {
    let mut hasher = StableHasher::new();
    hasher.write_str(FAILED_PROOF_COUNTEREXAMPLE_CORPUS_SCHEMA);
    hasher.write_u32(FAILED_PROOF_COUNTEREXAMPLE_CORPUS_SCHEMA_VERSION);
    hasher.write_u64(FAILED_PROOF_REDUCER_PARENT_ISSUE);
    hash_source_region(&mut hasher, source_region);
    hash_target(&mut hasher, target);
    hasher.write_u8(u8::from(found_by_concrete));
    hasher.write_u64(values.len() as u64);
    for value in values {
        hasher.write_str(&value.name);
        hasher.write_u64(value.value);
    }
    format!("trust-cg-failed-proof-cx-seed:{:032x}", hasher.finish128())
}

fn source_region_matches(lhs: &SourceRegionIdentity, rhs: &SourceRegionIdentity) -> bool {
    lhs.source_region_hash == rhs.source_region_hash
        && lhs.hash_algorithm == rhs.hash_algorithm
        && lhs.kernel_family == rhs.kernel_family
        && lhs.kernel_name == rhs.kernel_name
        && lhs.function_symbol == rhs.function_symbol
        && lhs.region_label == rhs.region_label
}

fn target_matches(lhs: &TargetAbiLayoutIdentity, rhs: &TargetAbiLayoutIdentity) -> bool {
    lhs.arch == rhs.arch
        && lhs.target_triple == rhs.target_triple
        && lhs.abi == rhs.abi
        && lhs.data_layout == rhs.data_layout
        && lhs.cpu == rhs.cpu
        && sorted_features(&lhs.features) == sorted_features(&rhs.features)
}

fn sorted_features(features: &[String]) -> Vec<&str> {
    let mut sorted = features.iter().map(String::as_str).collect::<Vec<_>>();
    sorted.sort_unstable();
    sorted
}

fn variable_names_match(values: &[CounterexampleValue], variable_names: &[String]) -> bool {
    if values.len() != variable_names.len() {
        return false;
    }
    let mut expected = variable_names
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>();
    expected.sort_unstable();
    expected.dedup();
    if expected.len() != variable_names.len() {
        return false;
    }
    let mut actual = values
        .iter()
        .map(|value| value.name.as_str())
        .collect::<Vec<_>>();
    actual.sort_unstable();
    actual == expected
}

fn hash_source_region(hasher: &mut StableHasher, source_region: &SourceRegionIdentity) {
    hasher.write_str(&source_region.source_region_hash);
    hasher.write_str(&source_region.hash_algorithm);
    hasher.write_str(&source_region.kernel_family);
    hash_option_str(hasher, source_region.kernel_name.as_deref());
    hash_option_str(hasher, source_region.function_symbol.as_deref());
    hash_option_str(hasher, source_region.region_label.as_deref());
}

fn hash_proof_assumptions(hasher: &mut StableHasher, assumptions: &[ProofAssumption]) {
    hasher.write_u64(assumptions.len() as u64);
    for assumption in assumptions {
        hasher.write_str(&assumption.id);
        hasher.write_str(proof_assumption_kind_tag(assumption.kind));
        hasher.write_str(&assumption.formula);
        hasher.write_str(&assumption.source);
    }
}

fn hash_target(hasher: &mut StableHasher, target: &TargetAbiLayoutIdentity) {
    hasher.write_str(&target.arch);
    hasher.write_str(&target.target_triple);
    hasher.write_str(&target.abi);
    hasher.write_str(&target.data_layout);
    hasher.write_str(&target.cpu);
    hasher.write_u64(target.features.len() as u64);
    for feature in &target.features {
        hasher.write_str(feature);
    }
}

fn hash_cost_context(hasher: &mut StableHasher, cost_context: &CostContext) {
    hasher.write_str(&cost_context.cost_model);
    hasher.write_str(&cost_context.cost_model_version);
    hash_option_str(hasher, cost_context.profile.as_deref());
    hasher.write(&cost_context.source_cost.to_le_bytes());
    hasher.write(&cost_context.replacement_cost.to_le_bytes());
    hasher.write_u64(cost_context.notes.len() as u64);
    for note in &cost_context.notes {
        hasher.write_str(note);
    }
}

fn hash_transform(hasher: &mut StableHasher, transform: &TransformIdentity) {
    hasher.write_str(&transform.name);
    hasher.write_str(&transform.version);
    hash_option_u64(hasher, transform.rule_proposal_hash);
    hash_option_str(hasher, transform.discovered_rule_name.as_deref());
    hash_option_u64(hasher, transform.discovered_rule_proof_hash);
}

fn hash_allowlist(hasher: &mut StableHasher, allowlist: &KernelAllowlist) {
    hasher.write_str(&allowlist.kernel_family);
    hash_option_str(hasher, allowlist.kernel_name.as_deref());
    hash_option_str(hasher, allowlist.allowlist_entry.as_deref());
    hasher.write_u8(u8::from(allowlist.allowlisted));
}

fn hash_product_gates(hasher: &mut StableHasher, gates: &ProductGateEvidence) {
    hasher.write_u8(u8::from(gates.replay_passed));
    hasher.write_u8(u8::from(gates.telemetry_guarded));
    hasher.write_u8(u8::from(gates.rollback_or_deopt_available));
    hasher.write_u8(u8::from(gates.product_promotion_approved));
}

fn hash_evidence(hasher: &mut StableHasher, evidence: &FailedProofEvidenceSummary) {
    match evidence {
        FailedProofEvidenceSummary::Counterexample {
            values,
            found_by_concrete,
        } => {
            hasher.write_str("counterexample");
            hasher.write_u8(u8::from(*found_by_concrete));
            hasher.write_u64(values.len() as u64);
            for value in values {
                hasher.write_str(&value.name);
                hasher.write_u64(value.value);
            }
        }
        FailedProofEvidenceSummary::Inconclusive { reason } => {
            hasher.write_str("inconclusive");
            hasher.write_str(reason);
        }
        FailedProofEvidenceSummary::ProductGateMismatch {
            proof_hash,
            missing_gates,
        } => {
            hasher.write_str("product_gate_mismatch");
            hash_option_u64(hasher, *proof_hash);
            hasher.write_u64(missing_gates.len() as u64);
            for gate in missing_gates {
                hasher.write_str(gate.as_str());
            }
        }
    }
}

fn hash_reducer(hasher: &mut StableHasher, reducer: Option<&ReducerMetadata>) {
    let Some(reducer) = reducer else {
        hasher.write_u8(0);
        return;
    };
    hasher.write_u8(1);
    hasher.write_str(failure_kind_tag(reducer.failure_kind));
    hasher.write_str(&reducer.reducer_id);
    hash_option_str(hasher, reducer.artifact_path.as_deref());
    hash_option_str(hasher, reducer.artifact_hash.as_deref());
    hash_option_str(hasher, reducer.follow_up_issue_title.as_deref());
}

fn hash_option_str(hasher: &mut StableHasher, value: Option<&str>) {
    match value {
        Some(value) => {
            hasher.write_u8(1);
            hasher.write_str(value);
        }
        None => hasher.write_u8(0),
    }
}

fn hash_option_u64(hasher: &mut StableHasher, value: Option<u64>) {
    match value {
        Some(value) => {
            hasher.write_u8(1);
            hasher.write_u64(value);
        }
        None => hasher.write_u8(0),
    }
}

fn default_follow_up_title(
    failure_kind: ProofFailureKind,
    record: &RewriteAdmissionRecord,
) -> String {
    let kernel = display_kernel(record);
    match failure_kind {
        ProofFailureKind::MissingProofPrecondition => {
            format!(
                "Proof precondition needed: {} for {}",
                record.transform.name, kernel
            )
        }
        ProofFailureKind::BadCandidate => {
            format!(
                "Bad solver candidate: {} for {}",
                record.transform.name, kernel
            )
        }
        ProofFailureKind::LoweringOrSemanticsBug => {
            format!(
                "Lowering/semantics bug: {} for {}",
                record.transform.name, kernel
            )
        }
        ProofFailureKind::ProductGateMismatch => {
            format!(
                "Product gate mismatch: {} for {}",
                record.transform.name, kernel
            )
        }
    }
}

fn default_follow_up_labels(failure_kind: ProofFailureKind) -> Vec<String> {
    let labels = match failure_kind {
        ProofFailureKind::ProductGateMismatch => ["P2", "feature", "codegen-quality"],
        _ => ["P2", "bug", "correctness"],
    };
    labels.iter().map(|label| (*label).to_string()).collect()
}

fn follow_up_body(
    failure_kind: ProofFailureKind,
    record: &RewriteAdmissionRecord,
    reducer: Option<&ReducerMetadata>,
    artifact_id: &str,
    evidence: &FailedProofEvidenceSummary,
) -> String {
    let reducer_id = reducer
        .map(|metadata| metadata.reducer_id.as_str())
        .unwrap_or(FAILED_PROOF_REDUCER_DEFAULT_REDUCER_ID);
    let artifact_path = reducer
        .and_then(|metadata| metadata.artifact_path.as_deref())
        .unwrap_or("not-recorded");
    let artifact_hash = reducer
        .and_then(|metadata| metadata.artifact_hash.as_deref())
        .unwrap_or("not-recorded");

    format!(
        "Parent: #{}\n\n## Failure Class\n{}\n\n## Candidate\n- Kernel family: {}\n- Kernel name: {}\n- Transform: {}@{}\n- Source region hash: {}\n- Artifact id: {}\n\n## Evidence\n{}\n\n## Reducer\n- Reducer id: {}\n- Artifact path: {}\n- Artifact hash: {}\n\n## Required Follow-up\n{}\n",
        FAILED_PROOF_REDUCER_PARENT_ISSUE,
        failure_kind_tag(failure_kind),
        record.source_region.kernel_family,
        record
            .source_region
            .kernel_name
            .as_deref()
            .unwrap_or("not-recorded"),
        record.transform.name,
        record.transform.version,
        record.source_region.source_region_hash,
        artifact_id,
        evidence_line(evidence),
        reducer_id,
        artifact_path,
        artifact_hash,
        required_follow_up_line(failure_kind, evidence)
    )
}

fn evidence_line(evidence: &FailedProofEvidenceSummary) -> String {
    match evidence {
        FailedProofEvidenceSummary::Counterexample {
            values,
            found_by_concrete,
        } => {
            let assignments = values
                .iter()
                .map(|value| format!("{}={}", value.name, value.value))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "counterexample found_by_concrete={} values=[{}]",
                found_by_concrete, assignments
            )
        }
        FailedProofEvidenceSummary::Inconclusive { reason } => {
            format!("inconclusive reason={}", reason)
        }
        FailedProofEvidenceSummary::ProductGateMismatch {
            proof_hash,
            missing_gates,
        } => {
            let gates = missing_gates
                .iter()
                .map(|gate| gate.as_str())
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "proved proof_hash={} missing_gates=[{}]",
                proof_hash
                    .map(|hash| format!("{hash:016x}"))
                    .unwrap_or_else(|| "not-recorded".to_string()),
                gates
            )
        }
    }
}

fn required_follow_up_line(
    failure_kind: ProofFailureKind,
    evidence: &FailedProofEvidenceSummary,
) -> String {
    match failure_kind {
        ProofFailureKind::MissingProofPrecondition => {
            "add or prove the missing precondition, then replay the candidate proof".to_string()
        }
        ProofFailureKind::BadCandidate => {
            "reject or repair the solver candidate before reconsidering admission".to_string()
        }
        ProofFailureKind::LoweringOrSemanticsBug => {
            "audit the lowering and semantics model before trusting this candidate".to_string()
        }
        ProofFailureKind::ProductGateMismatch => {
            let gates = match evidence {
                FailedProofEvidenceSummary::ProductGateMismatch { missing_gates, .. } => {
                    missing_gates
                        .iter()
                        .map(|gate| gate.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                }
                _ => "not-recorded".to_string(),
            };
            format!("resolve product gates before promotion: {}", gates)
        }
    }
}

fn display_kernel(record: &RewriteAdmissionRecord) -> &str {
    record
        .source_region
        .kernel_name
        .as_deref()
        .unwrap_or(record.source_region.kernel_family.as_str())
}

fn failure_kind_tag(kind: ProofFailureKind) -> &'static str {
    match kind {
        ProofFailureKind::MissingProofPrecondition => "missing_proof_precondition",
        ProofFailureKind::BadCandidate => "bad_candidate",
        ProofFailureKind::LoweringOrSemanticsBug => "lowering_or_semantics_bug",
        ProofFailureKind::ProductGateMismatch => "product_gate_mismatch",
    }
}

fn admission_state_tag(state: AdmissionState) -> &'static str {
    match state {
        AdmissionState::Disabled => "disabled",
        AdmissionState::PendingProof => "pending_proof",
        AdmissionState::ProvedProfileOnly => "proved_profile_only",
        AdmissionState::Admitted => "admitted",
        AdmissionState::Rejected => "rejected",
    }
}

fn proof_assumption_kind_tag(kind: crate::rewrite_admission::ProofAssumptionKind) -> &'static str {
    match kind {
        crate::rewrite_admission::ProofAssumptionKind::SmtPrecondition => "smt_precondition",
        crate::rewrite_admission::ProofAssumptionKind::AbiLayout => "abi_layout",
        crate::rewrite_admission::ProofAssumptionKind::KernelInvariant => "kernel_invariant",
        crate::rewrite_admission::ProofAssumptionKind::ProductGuard => "product_guard",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cegis::{CegisResult, ConcreteInput};
    use crate::rewrite_admission::{
        CostContext, KernelAllowlist, ProofAssumptionKind, SourceRegionIdentity,
        TargetAbiLayoutIdentity,
    };

    fn base_record() -> RewriteAdmissionRecord {
        RewriteAdmissionRecord::new(
            SourceRegionIdentity::new(
                "trust-cg-stable128:0123456789abcdef0123456789abcdef",
                "trust-cg-stable128-v1",
                "ay_lra_sparse_substitute",
            )
            .with_kernel_name("ay_lra_sparse_substitute")
            .with_function_symbol("_trust_cg_sparse_lra_i64")
            .with_region_label("bb0:0..2"),
            vec![ProofAssumption {
                id: "sparse.bounds".to_string(),
                kind: ProofAssumptionKind::KernelInvariant,
                formula: "0 <= row && row < rows".to_string(),
                source: "test".to_string(),
            }],
            TargetAbiLayoutIdentity::aarch64(
                "aarch64-apple-darwin",
                "aapcs64",
                "e-m:o-i64:64-i128:128-n32:64-S128",
                "apple-m2",
                vec!["+neon".to_string()],
            ),
            CostContext::aarch64("trust-cg-aarch64", "2026.04", 12, 8),
            TransformIdentity::new("proof-opts.sparse-rewrite", "v1"),
        )
    }

    fn assert_roundtrip(artifact: &FailedProofReducerArtifact) {
        let json = artifact
            .to_json_pretty()
            .expect("failed proof artifact should serialize");
        assert!(json.contains(FAILED_PROOF_REDUCER_ARTIFACT_SCHEMA));
        assert_eq!(
            FailedProofReducerArtifact::from_json_str(&json)
                .expect("failed proof artifact should deserialize"),
            *artifact
        );
    }

    fn golden_bad_candidate_record() -> RewriteAdmissionRecord {
        // The artifact id hashes the schema/version plus the admission,
        // evidence, and reducer metadata fields. Keep this fixture literal so
        // any golden movement means the reducer identity contract changed.
        let reducer =
            ReducerMetadata::new(ProofFailureKind::BadCandidate, "ay-named-kernel-reducer")
                .with_artifact(
                    "artifacts/reducers/golden/sparse-bad-candidate.json",
                    "sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
                )
                .with_follow_up_issue_title(
                    "Bad solver candidate: pinned sparse LRA reducer golden",
                );

        base_record().with_cegis_result(
            &CegisResult::NotEquivalent {
                counterexample: ConcreteInput::from_pairs(&[("row", 9), ("col", 4)]),
                found_by_concrete: true,
            },
            Some(reducer),
        )
    }

    fn enabled_seed_filter(
        record: &RewriteAdmissionRecord,
        variable_names: &[&str],
    ) -> FailedProofCounterexampleSeedFilter {
        FailedProofCounterexampleSeedFilter::enabled(
            record.source_region.clone(),
            record.target.clone(),
            variable_names
                .iter()
                .map(|name| (*name).to_string())
                .collect(),
        )
    }

    #[test]
    fn bad_candidate_artifact_id_and_follow_up_are_golden_stable() {
        let record = golden_bad_candidate_record();
        let artifact = FailedProofReducerArtifact::from_admission_record(&record)
            .expect("golden bad candidate should classify");
        let expected_artifact_id = "trust-cg-failed-proof-reducer:afdf1dcbe19647615a14aee45c723956";

        assert_eq!(artifact.schema, FAILED_PROOF_REDUCER_ARTIFACT_SCHEMA);
        assert_eq!(
            artifact.schema_version,
            FAILED_PROOF_REDUCER_ARTIFACT_SCHEMA_VERSION
        );
        assert_eq!(artifact.parent_issue, FAILED_PROOF_REDUCER_PARENT_ISSUE);
        assert_eq!(artifact.artifact_id, expected_artifact_id);
        assert_eq!(artifact.failure_kind, ProofFailureKind::BadCandidate);
        assert_eq!(
            artifact.evidence,
            FailedProofEvidenceSummary::Counterexample {
                values: vec![
                    CounterexampleValue {
                        name: "col".to_string(),
                        value: 4,
                    },
                    CounterexampleValue {
                        name: "row".to_string(),
                        value: 9,
                    },
                ],
                found_by_concrete: true,
            }
        );

        let reducer = artifact
            .reducer
            .as_ref()
            .expect("golden artifact should keep reducer metadata");
        assert_eq!(
            reducer.artifact_hash.as_deref(),
            Some("sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef")
        );
        assert_eq!(
            artifact.follow_up.title,
            "Bad solver candidate: pinned sparse LRA reducer golden"
        );
        assert_eq!(
            artifact.follow_up.labels,
            vec![
                "P2".to_string(),
                "bug".to_string(),
                "correctness".to_string()
            ]
        );
        assert_eq!(
            artifact.follow_up.body,
            format!(
                "Parent: #798\n\n\
                 ## Failure Class\n\
                 bad_candidate\n\n\
                 ## Candidate\n\
                 - Kernel family: ay_lra_sparse_substitute\n\
                 - Kernel name: ay_lra_sparse_substitute\n\
                 - Transform: proof-opts.sparse-rewrite@v1\n\
                 - Source region hash: trust-cg-stable128:0123456789abcdef0123456789abcdef\n\
                 - Artifact id: {expected_artifact_id}\n\n\
                 ## Evidence\n\
                 counterexample found_by_concrete=true values=[col=4, row=9]\n\n\
                 ## Reducer\n\
                 - Reducer id: ay-named-kernel-reducer\n\
                 - Artifact path: artifacts/reducers/golden/sparse-bad-candidate.json\n\
                 - Artifact hash: sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef\n\n\
                 ## Required Follow-up\n\
                 reject or repair the solver candidate before reconsidering admission\n"
            )
        );
        assert_roundtrip(&artifact);
    }

    #[test]
    fn failed_counterexample_corpus_default_off_is_empty() {
        let record = golden_bad_candidate_record();
        let artifact = FailedProofReducerArtifact::from_admission_record(&record)
            .expect("golden bad candidate should classify");
        let corpus = FailedProofCounterexampleCorpus::from_artifacts(
            [&artifact],
            &FailedProofCounterexampleSeedFilter::disabled(),
        );

        assert!(corpus.is_empty());
        assert!(
            corpus
                .concrete_inputs_for_scope(
                    &record.source_region,
                    &record.target,
                    &["row".to_string()],
                )
                .is_empty()
        );
    }

    #[test]
    fn failed_counterexample_corpus_accepts_only_matching_bad_candidate_rejections() {
        let record = golden_bad_candidate_record();
        let artifact = FailedProofReducerArtifact::from_admission_record(&record)
            .expect("golden bad candidate should classify");
        let filter = enabled_seed_filter(&record, &["col", "row"]);

        let corpus = FailedProofCounterexampleCorpus::from_artifacts([&artifact], &filter);

        assert_eq!(corpus.len(), 1);
        let seed = &corpus.seeds[0];
        assert_eq!(seed.schema, FAILED_PROOF_COUNTEREXAMPLE_CORPUS_SCHEMA);
        assert_eq!(
            seed.schema_version,
            FAILED_PROOF_COUNTEREXAMPLE_CORPUS_SCHEMA_VERSION
        );
        assert_eq!(seed.parent_issue, FAILED_PROOF_REDUCER_PARENT_ISSUE);
        assert_eq!(seed.source_region, record.source_region);
        assert_eq!(seed.target, record.target);
        assert_eq!(
            seed.values,
            vec![
                CounterexampleValue {
                    name: "col".to_string(),
                    value: 4,
                },
                CounterexampleValue {
                    name: "row".to_string(),
                    value: 9,
                },
            ]
        );

        let json = serde_json::to_string(seed).expect("seed should serialize");
        assert!(!json.contains("proof_hash"));
        assert!(!json.contains("product_gates"));
        assert!(!json.contains("admission_state"));
        assert!(!json.contains("allowlist"));
        assert!(!json.contains("replacement"));
    }

    #[test]
    fn failed_counterexample_corpus_rejects_non_counterexample_or_mismatch_scope() {
        let record = golden_bad_candidate_record();
        let mut artifact = FailedProofReducerArtifact::from_admission_record(&record)
            .expect("golden bad candidate should classify");
        let filter = enabled_seed_filter(&record, &["col", "row"]);

        artifact.admission_state = AdmissionState::Admitted;
        assert!(FailedProofCounterexampleCorpus::from_artifacts([&artifact], &filter).is_empty());

        artifact = FailedProofReducerArtifact::from_admission_record(&record)
            .expect("golden bad candidate should classify");
        artifact.failure_kind = ProofFailureKind::MissingProofPrecondition;
        assert!(FailedProofCounterexampleCorpus::from_artifacts([&artifact], &filter).is_empty());

        artifact = FailedProofReducerArtifact::from_admission_record(&record)
            .expect("golden bad candidate should classify");
        artifact.evidence = FailedProofEvidenceSummary::Inconclusive {
            reason: "not fuel".to_string(),
        };
        assert!(FailedProofCounterexampleCorpus::from_artifacts([&artifact], &filter).is_empty());

        let mismatched_vars = enabled_seed_filter(&record, &["row"]);
        artifact = FailedProofReducerArtifact::from_admission_record(&record)
            .expect("golden bad candidate should classify");
        assert!(
            FailedProofCounterexampleCorpus::from_artifacts([&artifact], &mismatched_vars)
                .is_empty()
        );

        let mut mismatched_target = record.clone();
        mismatched_target.target.cpu = "apple-m3".to_string();
        let target_filter = enabled_seed_filter(&mismatched_target, &["col", "row"]);
        assert!(
            FailedProofCounterexampleCorpus::from_artifacts([&artifact], &target_filter).is_empty()
        );
    }

    #[test]
    fn failed_counterexample_corpus_consumes_only_matching_scope() {
        let record = golden_bad_candidate_record();
        let artifact = FailedProofReducerArtifact::from_admission_record(&record)
            .expect("golden bad candidate should classify");
        let filter = enabled_seed_filter(&record, &["col", "row"]);
        let corpus = FailedProofCounterexampleCorpus::from_artifacts([&artifact], &filter);
        let variable_names = vec!["col".to_string(), "row".to_string()];

        assert_eq!(
            corpus
                .concrete_inputs_for_scope(&record.source_region, &record.target, &variable_names)
                .len(),
            1
        );

        let mut wrong_source = record.source_region.clone();
        wrong_source.function_symbol = Some("other_function".to_string());
        assert!(
            corpus
                .concrete_inputs_for_scope(&wrong_source, &record.target, &variable_names)
                .is_empty()
        );

        let mut wrong_target = record.target.clone();
        wrong_target.cpu = "apple-m3".to_string();
        assert!(
            corpus
                .concrete_inputs_for_scope(&record.source_region, &wrong_target, &variable_names)
                .is_empty()
        );
    }

    #[test]
    fn missing_precondition_artifact_uses_existing_reducer_metadata() {
        let reducer = ReducerMetadata::new(
            ProofFailureKind::MissingProofPrecondition,
            "ay-named-kernel-reducer",
        )
        .with_artifact(
            "artifacts/reducers/sparse-precondition.json",
            "sha256:precondition",
        )
        .with_follow_up_issue_title("Rewrite admission needs sparse bounds precondition");
        let record = base_record().with_cegis_result(
            &CegisResult::NotEquivalent {
                counterexample: ConcreteInput::from_pairs(&[("row", 9), ("rows", 8)]),
                found_by_concrete: false,
            },
            Some(reducer.clone()),
        );

        let artifact = FailedProofReducerArtifact::from_admission_record(&record)
            .expect("record should classify as missing precondition");

        assert_eq!(
            artifact.failure_kind,
            ProofFailureKind::MissingProofPrecondition
        );
        assert_eq!(artifact.reducer, Some(reducer));
        assert_eq!(
            artifact.follow_up.title,
            "Rewrite admission needs sparse bounds precondition"
        );
        assert!(
            artifact
                .follow_up
                .body
                .contains("missing_proof_precondition")
        );
        assert_roundtrip(&artifact);
    }

    #[test]
    fn bad_candidate_artifact_records_sorted_counterexample() {
        let reducer =
            ReducerMetadata::new(ProofFailureKind::BadCandidate, "ay-named-kernel-reducer");
        let record = base_record().with_cegis_result(
            &CegisResult::NotEquivalent {
                counterexample: ConcreteInput::from_pairs(&[("rhs", 2), ("lhs", 1)]),
                found_by_concrete: true,
            },
            Some(reducer),
        );

        let artifact = FailedProofReducerArtifact::from_admission_record(&record)
            .expect("record should classify as bad candidate");

        assert_eq!(artifact.failure_kind, ProofFailureKind::BadCandidate);
        assert!(
            artifact
                .follow_up
                .title
                .starts_with("Bad solver candidate:")
        );
        assert_eq!(
            artifact.evidence,
            FailedProofEvidenceSummary::Counterexample {
                values: vec![
                    CounterexampleValue {
                        name: "lhs".to_string(),
                        value: 1,
                    },
                    CounterexampleValue {
                        name: "rhs".to_string(),
                        value: 2,
                    },
                ],
                found_by_concrete: true,
            }
        );
        assert_roundtrip(&artifact);
    }

    #[test]
    fn lowering_semantics_artifact_records_inconclusive_reason() {
        let reducer = ReducerMetadata::new(
            ProofFailureKind::LoweringOrSemanticsBug,
            "aarch64-semantics-reducer",
        )
        .with_artifact("artifacts/reducers/semantics.json", "sha256:semantics");
        let record = base_record().with_cegis_result(
            &CegisResult::Error("aarch64 semantics disagreed with trust_ir lowering".to_string()),
            Some(reducer),
        );

        let artifact = FailedProofReducerArtifact::from_admission_record(&record)
            .expect("record should classify as lowering or semantics bug");

        assert_eq!(
            artifact.failure_kind,
            ProofFailureKind::LoweringOrSemanticsBug
        );
        assert!(
            artifact
                .follow_up
                .body
                .contains("lowering_or_semantics_bug")
        );
        assert_eq!(
            artifact.evidence,
            FailedProofEvidenceSummary::Inconclusive {
                reason: "solver_error: aarch64 semantics disagreed with trust_ir lowering"
                    .to_string(),
            }
        );
        assert_roundtrip(&artifact);
    }

    #[test]
    fn product_gate_mismatch_artifact_lists_missing_gates() {
        let record = base_record()
            .with_cegis_result(
                &CegisResult::Equivalent {
                    proof_hash: 0xced1_f1ed,
                    iterations: 1,
                },
                None,
            )
            .with_allowlist(KernelAllowlist::allowlisted(
                "ay_lra_sparse_substitute",
                "ay_lra_sparse_substitute",
                "rewrite-admission/ay-lra-sparse-substitute-v1",
            ))
            .with_product_gates(ProductGateEvidence {
                replay_passed: true,
                telemetry_guarded: false,
                rollback_or_deopt_available: true,
                product_promotion_approved: false,
            });

        let artifact = FailedProofReducerArtifact::from_admission_record(&record)
            .expect("record should classify as product gate mismatch");

        assert_eq!(artifact.failure_kind, ProofFailureKind::ProductGateMismatch);
        assert_eq!(artifact.reducer, None);
        assert_eq!(
            artifact.evidence,
            FailedProofEvidenceSummary::ProductGateMismatch {
                proof_hash: Some(0xced1_f1ed),
                missing_gates: vec![
                    ProductGateName::TelemetryGuard,
                    ProductGateName::ProductPromotion,
                ],
            }
        );
        assert!(
            artifact
                .follow_up
                .body
                .contains("telemetry_guard, product_promotion")
        );

        let rebuilt = FailedProofReducerArtifact::from_admission_record(&record)
            .expect("rebuilt record should classify");
        assert_eq!(artifact.artifact_id, rebuilt.artifact_id);
        assert_roundtrip(&artifact);
    }
}
