// trust-cg-verify/rewrite_admission.rs - solver-discovered rewrite admission records
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Persisted admission records for solver-discovered AArch64 rewrites.
//!
//! This module deliberately stops at record construction and validation. It
//! does not register the rewrite with `trust-cg-opt`; downstream promotion must
//! still check the allowlist, replay, telemetry, rollback/deopt, and product
//! promotion gates before a declarative rewrite can become reachable.

use crate::cegis::{CegisResult, ConcreteInput};
use crate::rule_discovery::{DiscoveredRule, RuleProposal, RuleResult};
use serde::{Deserialize, Serialize};
use trust_cg_opt::proof_opts::OptCertificate;

/// Schema name for serialized rewrite admission records.
pub const REWRITE_ADMISSION_SCHEMA: &str = "trust-cg.rewrite_admission.v1";

/// Numeric schema version for serialized rewrite admission records.
pub const REWRITE_ADMISSION_SCHEMA_VERSION: u32 = 1;

/// Issue that introduced the ay LRA proof-consumption manifest family.
pub const AY_LRA_PROOF_CONSUMPTION_MANIFEST_ISSUE: u64 = 796;

/// Stable schema tag for #796 ay LRA proof-consumption manifests.
pub const AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA: &str =
    "trust-cg.ay_lra.proof_consumption_manifest.v1";

/// Stable schema version for #796 ay LRA proof-consumption manifests.
pub const AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA_VERSION: u32 = 1;

/// Stable #796 ay LRA sparse-substitute kernel family id.
pub const AY_LRA_SPARSE_SUBSTITUTE_KERNEL_FAMILY: &str = "ay_lra_sparse_substitute";

/// Stable #796 ay LRA basis-update kernel family id.
pub const AY_LRA_BASIS_UPDATE_KERNEL_FAMILY: &str = "ay_lra_basis_update";

/// Stable #795 proof-optimization certificate producer id.
pub const PROOF_OPTS_CERTIFICATE_PRODUCER: &str = "trust-cg-opt.proof-opts";

/// Stable schema tag for the #800 proof-guided admission verdict.
pub const PROOF_GUIDED_ADMISSION_VERDICT_SCHEMA: &str =
    "trust-cg.proof_guided_admission.verdict.v1";

/// Stable schema version for the #800 proof-guided admission verdict.
pub const PROOF_GUIDED_ADMISSION_VERDICT_SCHEMA_VERSION: u32 = 1;

/// Issue that owns the complete proof-guided admission gate.
pub const PROOF_GUIDED_ADMISSION_VERDICT_ISSUE: u64 = 800;

const AY_LRA_SPARSE_ADD_ZERO_TRANSFORM: &str = "ay_lra_sparse_add_zero";
const AY_LRA_SPARSE_ADD_ZERO_VERSION: &str = "v1";
const AY_LRA_SPARSE_ADD_ZERO_PROOF_HASH: u64 = 0xbeef;
const AY_LRA_SPARSE_ADD_ZERO_CERTIFICATE_HASH: &str = "0000000000000000feedfacecafebeef";
const AY_LRA_SPARSE_ADD_ZERO_VALIDATION_HASH: &str = "00000000000000000000000000005678";

/// A persisted candidate rewrite admission record.
///
/// Positive `aarch64_cost_delta` means the target rewrite is cheaper than the
/// source region under the recorded cost context.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RewriteAdmissionRecord {
    /// Stable schema name.
    pub schema: String,
    /// Stable schema version.
    pub schema_version: u32,
    /// Source kernel region covered by the candidate.
    pub source_region: SourceRegionIdentity,
    /// Explicit proof assumptions/preconditions used for equivalence.
    pub proof_assumptions: Vec<ProofAssumption>,
    /// Target ABI and layout identity used during proof and cost modeling.
    pub target: TargetAbiLayoutIdentity,
    /// Cost model context used to evaluate the candidate.
    pub cost_context: CostContext,
    /// Candidate transform identity and solver-discovery lineage.
    pub transform: TransformIdentity,
    /// Solver proof, counterexample, or reducer evidence.
    pub evidence: SolverEvidence,
    /// AArch64-specific cost delta; positive means the rewrite is cheaper.
    pub aarch64_cost_delta: i64,
    /// Current admission state. Defaults to [`AdmissionState::Disabled`].
    pub admission_state: AdmissionState,
    /// Named-kernel allowlist scope.
    pub allowlist: KernelAllowlist,
    /// Product gates that must remain true before any promotion.
    pub product_gates: ProductGateEvidence,
    /// #800 complete proof-guided admission verdict.
    #[serde(
        default,
        skip_serializing_if = "ProofGuidedAdmissionVerdict::is_default_rejected"
    )]
    pub proof_guided_admission: ProofGuidedAdmissionVerdict,
    /// #795 proof-optimization certificate identity.
    pub certificate_identity: Option<CertificateIdentity>,
    /// #796 ay LRA proof-consumption manifest family binding.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ay_lra_manifest_binding: Option<AYLraManifestBinding>,
}

impl RewriteAdmissionRecord {
    /// Build a disabled-by-default record from an existing rule proposal.
    pub fn from_rule_proposal(
        source_region: SourceRegionIdentity,
        target: TargetAbiLayoutIdentity,
        cost_context: CostContext,
        proposal: &RuleProposal,
        transform_version: impl Into<String>,
    ) -> Self {
        let transform = TransformIdentity::from_rule_proposal(proposal, transform_version);
        let proof_assumptions = proposal
            .preconditions
            .iter()
            .enumerate()
            .map(|(idx, expr)| ProofAssumption {
                id: format!("proposal_precondition_{}", idx),
                kind: ProofAssumptionKind::SmtPrecondition,
                formula: format!("{}", expr),
                source: "RuleProposal::preconditions".to_string(),
            })
            .collect();

        Self::new(
            source_region,
            proof_assumptions,
            target,
            cost_context,
            transform,
        )
    }

    /// Build a disabled-by-default record from explicit admission metadata.
    pub fn new(
        source_region: SourceRegionIdentity,
        proof_assumptions: Vec<ProofAssumption>,
        target: TargetAbiLayoutIdentity,
        cost_context: CostContext,
        transform: TransformIdentity,
    ) -> Self {
        let aarch64_cost_delta = cost_context.delta();
        Self {
            schema: REWRITE_ADMISSION_SCHEMA.to_string(),
            schema_version: REWRITE_ADMISSION_SCHEMA_VERSION,
            source_region,
            proof_assumptions,
            target,
            cost_context,
            transform,
            evidence: SolverEvidence::Pending,
            aarch64_cost_delta,
            admission_state: AdmissionState::Disabled,
            allowlist: KernelAllowlist::not_allowlisted("unknown"),
            product_gates: ProductGateEvidence::default(),
            proof_guided_admission: ProofGuidedAdmissionVerdict::default(),
            certificate_identity: None,
            ay_lra_manifest_binding: None,
        }
    }

    /// Attach solver evidence from an existing CEGIS result.
    ///
    /// Equivalent results move only to profile-only proof state. They are not
    /// admitted until the caller explicitly sets the allowlist, product gates,
    /// and [`AdmissionState::Admitted`].
    pub fn with_cegis_result(
        mut self,
        result: &CegisResult,
        reducer: Option<ReducerMetadata>,
    ) -> Self {
        let mut reducer = reducer;
        match result {
            CegisResult::Equivalent {
                proof_hash,
                iterations,
            } => {
                self.evidence = SolverEvidence::AYEquivalenceProof {
                    proof_hash: *proof_hash,
                    cegis_iterations: Some(*iterations as u32),
                };
                self.admission_state = AdmissionState::ProvedProfileOnly;
            }
            CegisResult::NotEquivalent {
                counterexample,
                found_by_concrete,
            } => {
                self.evidence = SolverEvidence::Counterexample {
                    counterexample: CounterexampleRecord::from_concrete_input(
                        counterexample,
                        *found_by_concrete,
                    ),
                    reducer: reducer.take(),
                };
                self.admission_state = AdmissionState::Rejected;
            }
            CegisResult::Timeout => {
                self.evidence = SolverEvidence::Inconclusive {
                    reason: "timeout".to_string(),
                    reducer: reducer.take(),
                };
                self.admission_state = AdmissionState::PendingProof;
            }
            CegisResult::MaxIterationsReached { counterexamples } => {
                self.evidence = SolverEvidence::Inconclusive {
                    reason: format!(
                        "max_iterations_reached: {} counterexamples",
                        counterexamples
                    ),
                    reducer: reducer.take(),
                };
                self.admission_state = AdmissionState::PendingProof;
            }
            CegisResult::Error(message) => {
                self.evidence = SolverEvidence::Inconclusive {
                    reason: format!("solver_error: {}", message),
                    reducer: reducer.take(),
                };
                self.admission_state = AdmissionState::PendingProof;
            }
        }
        self
    }

    /// Mark this record with a discovered rule's proven equivalence metadata.
    pub fn with_discovered_rule(mut self, rule: &DiscoveredRule) -> Self {
        self.transform.discovered_rule_name = Some(rule.name.clone());
        self.transform.discovered_rule_proof_hash = Some(rule.proof_hash);
        self.evidence = SolverEvidence::AYEquivalenceProof {
            proof_hash: rule.proof_hash,
            cegis_iterations: Some(rule.cegis_iterations as u32),
        };
        self.admission_state = AdmissionState::ProvedProfileOnly;
        self
    }

    /// Attach the outcome from the rule-discovery pipeline.
    ///
    /// Accepted rules become profile-only proof records. Rejected rules carry
    /// the counterexample/reducer path. Inconclusive and duplicate proposals
    /// remain non-promoting metadata.
    pub fn with_rule_result(self, result: &RuleResult, reducer: Option<ReducerMetadata>) -> Self {
        let mut reducer = reducer;
        match result {
            RuleResult::Accepted(rule) => self.with_discovered_rule(rule),
            RuleResult::Rejected {
                counterexample,
                found_by_concrete,
            } => {
                let mut record = self;
                record.evidence = SolverEvidence::Counterexample {
                    counterexample: CounterexampleRecord::from_concrete_input(
                        counterexample,
                        *found_by_concrete,
                    ),
                    reducer: reducer.take(),
                };
                record.admission_state = AdmissionState::Rejected;
                record
            }
            RuleResult::Inconclusive => {
                let mut record = self;
                record.evidence = SolverEvidence::Inconclusive {
                    reason: "rule_discovery_inconclusive".to_string(),
                    reducer: reducer.take(),
                };
                record.admission_state = AdmissionState::PendingProof;
                record
            }
            RuleResult::Duplicate => {
                let mut record = self;
                record.evidence = SolverEvidence::Inconclusive {
                    reason: "duplicate_rule_proposal".to_string(),
                    reducer: None,
                };
                record.admission_state = AdmissionState::Disabled;
                record
            }
        }
    }

    /// Attach #795 proof-optimization certificate identity and transform id.
    pub fn with_opt_certificate(mut self, certificate: &OptCertificate) -> Self {
        self.transform = TransformIdentity::from_opt_certificate(certificate);
        self.certificate_identity = Some(CertificateIdentity::from_opt_certificate(certificate));
        self
    }

    /// Replace the named-kernel allowlist scope.
    pub fn with_allowlist(mut self, allowlist: KernelAllowlist) -> Self {
        self.allowlist = allowlist;
        self
    }

    /// Replace product gate evidence.
    pub fn with_product_gates(mut self, product_gates: ProductGateEvidence) -> Self {
        self.product_gates = product_gates;
        self
    }

    /// Replace the complete #800 proof-guided admission verdict.
    pub fn with_proof_guided_admission_verdict(
        mut self,
        verdict: ProofGuidedAdmissionVerdict,
    ) -> Self {
        self.proof_guided_admission = verdict;
        self
    }

    /// Replace the admission state.
    pub fn with_admission_state(mut self, admission_state: AdmissionState) -> Self {
        self.admission_state = admission_state;
        self
    }

    /// Apply profile-review gates and promote only when every gate is closed.
    ///
    /// A proved record that is missing allowlist or product gates remains
    /// profile-only. Unproved records keep their existing state.
    pub fn with_profile_review(
        mut self,
        allowlist: KernelAllowlist,
        product_gates: ProductGateEvidence,
    ) -> Self {
        self.allowlist = allowlist;
        self.product_gates = product_gates;
        if matches!(self.evidence, SolverEvidence::AYEquivalenceProof { .. }) {
            self.admission_state = if self.has_strict_admission_inputs() {
                AdmissionState::Admitted
            } else {
                AdmissionState::ProvedProfileOnly
            };
        }
        self
    }

    /// Attach a #795 proof-optimization certificate identity.
    pub fn with_certificate_identity(mut self, certificate_identity: CertificateIdentity) -> Self {
        self.certificate_identity = Some(certificate_identity);
        self
    }

    /// Attach a #796 ay LRA proof-consumption manifest family binding.
    pub fn with_ay_lra_manifest_binding(mut self, binding: AYLraManifestBinding) -> Self {
        self.ay_lra_manifest_binding = Some(binding);
        self
    }

    /// Attach the canonical #796 binding for a ay LRA named-kernel family.
    pub fn with_ay_lra_kernel_family_binding(self, family: AYLraRewriteKernelFamily) -> Self {
        self.with_ay_lra_manifest_binding(AYLraManifestBinding::ay_lra(family))
    }

    /// True only when the record is fully eligible for downstream promotion.
    pub fn can_admit_to_declarative_rewrite(&self) -> bool {
        matches!(self.admission_state, AdmissionState::Admitted)
            && self.has_strict_admission_inputs()
    }

    fn has_strict_admission_inputs(&self) -> bool {
        self.allowlist.allowlisted
            && self.allowlist.matches_source_region(&self.source_region)
            && matches!(self.evidence, SolverEvidence::AYEquivalenceProof { .. })
            && self.product_gates.all_passed()
            && self.proof_guided_admission.accepts_record(self)
            && self.has_strict_certificate_identity()
            && self.has_strict_ay_lra_manifest_binding()
    }

    fn has_strict_certificate_identity(&self) -> bool {
        let Some(proof_hash) = self.evidence.proof_hash() else {
            return false;
        };
        self.certificate_identity.as_ref().is_some_and(|identity| {
            identity.matches_transform_identity(&self.transform, proof_hash)
        })
    }

    fn has_strict_ay_lra_manifest_binding(&self) -> bool {
        self.ay_lra_manifest_binding
            .as_ref()
            .is_some_and(|binding| {
                binding.matches_source_and_allowlist(&self.source_region, &self.allowlist)
            })
    }

    /// Serialize the record as stable JSON.
    pub fn to_json_pretty(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Deserialize a record from stable JSON.
    pub fn from_json_str(json: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(json)
    }
}

/// Source region identity for a named AArch64 kernel candidate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceRegionIdentity {
    /// Hash of the source region payload.
    pub source_region_hash: String,
    /// Hash algorithm used for `source_region_hash`.
    pub hash_algorithm: String,
    /// Logical kernel family, such as `sparse` or `basis`.
    pub kernel_family: String,
    /// Optional concrete kernel name.
    pub kernel_name: Option<String>,
    /// Optional function symbol containing the source region.
    pub function_symbol: Option<String>,
    /// Optional source instruction/window description.
    pub region_label: Option<String>,
}

impl SourceRegionIdentity {
    /// Create a source region identity with the required hash and family.
    pub fn new(
        source_region_hash: impl Into<String>,
        hash_algorithm: impl Into<String>,
        kernel_family: impl Into<String>,
    ) -> Self {
        Self {
            source_region_hash: source_region_hash.into(),
            hash_algorithm: hash_algorithm.into(),
            kernel_family: kernel_family.into(),
            kernel_name: None,
            function_symbol: None,
            region_label: None,
        }
    }

    /// Create a source identity for a #796 ay LRA named AArch64 kernel family.
    pub fn ay_lra(
        source_region_hash: impl Into<String>,
        hash_algorithm: impl Into<String>,
        family: AYLraRewriteKernelFamily,
    ) -> Self {
        Self::new(source_region_hash, hash_algorithm, family.as_str())
            .with_kernel_name(family.default_kernel_name())
    }

    /// Attach a concrete kernel name.
    pub fn with_kernel_name(mut self, kernel_name: impl Into<String>) -> Self {
        self.kernel_name = Some(kernel_name.into());
        self
    }

    /// Attach a function symbol.
    pub fn with_function_symbol(mut self, function_symbol: impl Into<String>) -> Self {
        self.function_symbol = Some(function_symbol.into());
        self
    }

    /// Attach a source-region label.
    pub fn with_region_label(mut self, region_label: impl Into<String>) -> Self {
        self.region_label = Some(region_label.into());
        self
    }
}

/// Explicit assumption used during proof.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofAssumption {
    /// Stable assumption identifier.
    pub id: String,
    /// Assumption category.
    pub kind: ProofAssumptionKind,
    /// Assumption formula or structured text.
    pub formula: String,
    /// Where the assumption came from.
    pub source: String,
}

/// Categories for explicit proof assumptions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ProofAssumptionKind {
    /// SMT precondition from a rule proposal.
    SmtPrecondition,
    /// ABI/layout fact used by the proof.
    AbiLayout,
    /// Kernel-specific invariant.
    KernelInvariant,
    /// Product or profile guard.
    ProductGuard,
}

/// Target identity used for proof and cost-model replay.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TargetAbiLayoutIdentity {
    /// Target architecture.
    pub arch: String,
    /// Target triple.
    pub target_triple: String,
    /// Target ABI.
    pub abi: String,
    /// Target data layout identity.
    pub data_layout: String,
    /// CPU model.
    pub cpu: String,
    /// Target feature string.
    pub features: Vec<String>,
}

impl TargetAbiLayoutIdentity {
    /// Create a target identity for AArch64.
    pub fn aarch64(
        target_triple: impl Into<String>,
        abi: impl Into<String>,
        data_layout: impl Into<String>,
        cpu: impl Into<String>,
        features: Vec<String>,
    ) -> Self {
        Self {
            arch: "aarch64".to_string(),
            target_triple: target_triple.into(),
            abi: abi.into(),
            data_layout: data_layout.into(),
            cpu: cpu.into(),
            features,
        }
    }
}

/// Cost-model context recorded with a candidate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CostContext {
    /// Cost model name.
    pub cost_model: String,
    /// Cost model version.
    pub cost_model_version: String,
    /// Optional profile context that discovered this candidate.
    pub profile: Option<String>,
    /// Source region cost.
    pub source_cost: i64,
    /// Replacement region cost.
    pub replacement_cost: i64,
    /// Extra cost-model notes.
    pub notes: Vec<String>,
}

impl CostContext {
    /// Build an AArch64 cost context.
    pub fn aarch64(
        cost_model: impl Into<String>,
        cost_model_version: impl Into<String>,
        source_cost: i64,
        replacement_cost: i64,
    ) -> Self {
        Self {
            cost_model: cost_model.into(),
            cost_model_version: cost_model_version.into(),
            profile: None,
            source_cost,
            replacement_cost,
            notes: Vec::new(),
        }
    }

    /// Attach a profile context.
    pub fn with_profile(mut self, profile: impl Into<String>) -> Self {
        self.profile = Some(profile.into());
        self
    }

    /// Attach a cost-model note.
    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    /// Positive means the replacement is cheaper than the source region.
    pub fn delta(&self) -> i64 {
        self.source_cost - self.replacement_cost
    }
}

/// Candidate transform identity and solver-discovery lineage.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransformIdentity {
    /// Transform name.
    pub name: String,
    /// Transform version.
    pub version: String,
    /// Hash from [`RuleProposal::proposal_hash`] when available.
    pub rule_proposal_hash: Option<u64>,
    /// Name from a proven [`DiscoveredRule`] when available.
    pub discovered_rule_name: Option<String>,
    /// Proof hash from a proven [`DiscoveredRule`] when available.
    pub discovered_rule_proof_hash: Option<u64>,
    /// Certificate hash that the admitted proof/certificate record is bound to.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub certificate_hash: Option<String>,
    /// Validation hash expected as the suffix of `certificate_chain_id`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub certificate_validation_hash: Option<String>,
}

impl TransformIdentity {
    /// Create an explicit transform identity.
    pub fn new(name: impl Into<String>, version: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            version: version.into(),
            rule_proposal_hash: None,
            discovered_rule_name: None,
            discovered_rule_proof_hash: None,
            certificate_hash: None,
            certificate_validation_hash: None,
        }
    }

    /// Create a transform identity from a rule proposal.
    pub fn from_rule_proposal(
        proposal: &RuleProposal,
        transform_version: impl Into<String>,
    ) -> Self {
        Self {
            name: proposal
                .name
                .clone()
                .unwrap_or_else(|| "unnamed_rule_proposal".to_string()),
            version: transform_version.into(),
            rule_proposal_hash: Some(proposal.proposal_hash()),
            discovered_rule_name: None,
            discovered_rule_proof_hash: None,
            certificate_hash: None,
            certificate_validation_hash: None,
        }
    }

    /// Create a transform identity from a #795 proof-optimization certificate.
    pub fn from_opt_certificate(certificate: &OptCertificate) -> Self {
        Self {
            name: certificate.transform.name.clone(),
            version: format!("v{}", certificate.transform.version),
            rule_proposal_hash: None,
            discovered_rule_name: Some(certificate.transform.name.clone()),
            discovered_rule_proof_hash: u64::try_from(certificate.proof_hash).ok(),
            certificate_hash: Some(format_u128_hex(certificate.certificate_id)),
            certificate_validation_hash: Some(format_u128_hex(certificate.validation_hash)),
        }
    }

    fn certificate_binding_expectation(
        &self,
        proof_hash: u64,
    ) -> CertificateBindingExpectation<'_> {
        match (
            self.certificate_hash.as_deref(),
            self.certificate_validation_hash.as_deref(),
        ) {
            (Some(certificate_hash), Some(validation_hash))
                if is_u128_hex_identity(certificate_hash)
                    && is_u128_hex_identity(validation_hash) =>
            {
                if self.discovered_rule_proof_hash == Some(proof_hash) {
                    CertificateBindingExpectation::Bound {
                        certificate_hash,
                        validation_hash,
                    }
                } else {
                    CertificateBindingExpectation::Invalid
                }
            }
            (Some(_), _) | (_, Some(_)) => CertificateBindingExpectation::Invalid,
            (None, None) => {
                match reviewed_certificate_binding(&self.name, &self.version, proof_hash) {
                    Some(binding) => CertificateBindingExpectation::Bound {
                        certificate_hash: binding.certificate_hash,
                        validation_hash: binding.validation_hash,
                    },
                    None if is_reviewed_certificate_transform(&self.name, &self.version) => {
                        CertificateBindingExpectation::Invalid
                    }
                    None => CertificateBindingExpectation::Unbound,
                }
            }
        }
    }
}

fn is_reviewed_certificate_transform(transform_name: &str, transform_version: &str) -> bool {
    transform_name == AY_LRA_SPARSE_ADD_ZERO_TRANSFORM
        && transform_version == AY_LRA_SPARSE_ADD_ZERO_VERSION
}

/// ay LRA named AArch64 kernel families admitted by the #796 manifest slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AYLraRewriteKernelFamily {
    /// Sparse substitute row update kernel.
    SparseSubstitute,
    /// Basis-region or basis-row update kernel.
    BasisUpdate,
}

impl AYLraRewriteKernelFamily {
    /// Return the stable lower-snake-case family id from #796.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::SparseSubstitute => AY_LRA_SPARSE_SUBSTITUTE_KERNEL_FAMILY,
            Self::BasisUpdate => AY_LRA_BASIS_UPDATE_KERNEL_FAMILY,
        }
    }

    /// Return the default named kernel used for extractor/admission tests.
    pub const fn default_kernel_name(self) -> &'static str {
        match self {
            Self::SparseSubstitute => "ay_lra_sparse_substitute",
            Self::BasisUpdate => "ay_lra_basis_row_batch",
        }
    }

    /// Return the default admission allowlist entry id for this family.
    pub const fn allowlist_entry(self) -> &'static str {
        match self {
            Self::SparseSubstitute => "rewrite-admission/ay-lra-sparse-substitute-v1",
            Self::BasisUpdate => "rewrite-admission/ay-lra-basis-update-v1",
        }
    }

    /// Return the #796 proof family id expected for this kernel family.
    pub const fn proof_family(self) -> &'static str {
        self.as_str()
    }

    /// Return the required #796 certificate dependencies for this family.
    pub const fn required_certificate_dependencies(self) -> &'static [&'static str] {
        match self {
            Self::SparseSubstitute => &[
                "ay-lra-sparse-substitute-row-order",
                "ay-lra-sparse-output-bounds",
                "ay-lra-sparse-overflow",
                "ay-lra-sparse-alias-policy",
                "ay-lra-basis-epoch",
            ],
            Self::BasisUpdate => &[
                "ay-lra-basis-sorted-rows",
                "ay-lra-basis-output-bounds",
                "ay-lra-basis-overflow",
                "ay-lra-basis-alias-policy",
                "ay-lra-basis-epoch",
                "ay-lra-basis-prefix-rollback",
            ],
        }
    }
}

fn ay_lra_family_from_str(kernel_family: &str) -> Option<AYLraRewriteKernelFamily> {
    match kernel_family {
        AY_LRA_SPARSE_SUBSTITUTE_KERNEL_FAMILY => Some(AYLraRewriteKernelFamily::SparseSubstitute),
        AY_LRA_BASIS_UPDATE_KERNEL_FAMILY => Some(AYLraRewriteKernelFamily::BasisUpdate),
        _ => None,
    }
}

/// #796 ay LRA proof-consumption manifest identity bound to an admission record.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AYLraManifestBinding {
    /// Manifest schema.
    pub schema: String,
    /// Manifest schema version.
    pub schema_version: u32,
    /// Issue that owns the manifest contract.
    pub issue: u64,
    /// ay LRA kernel family id.
    pub kernel_family: String,
    /// ay LRA proof family id.
    pub proof_family: String,
    /// Product allowlist family from the #796 manifest.
    pub allowlist_family: String,
    /// Required certificate dependencies from the #796 manifest.
    pub required_certificate_dependencies: Vec<String>,
}

impl AYLraManifestBinding {
    /// Build the canonical #796 manifest binding for a ay LRA kernel family.
    pub fn ay_lra(family: AYLraRewriteKernelFamily) -> Self {
        Self {
            schema: AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA.to_string(),
            schema_version: AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA_VERSION,
            issue: AY_LRA_PROOF_CONSUMPTION_MANIFEST_ISSUE,
            kernel_family: family.as_str().to_string(),
            proof_family: family.proof_family().to_string(),
            allowlist_family: family.as_str().to_string(),
            required_certificate_dependencies: family
                .required_certificate_dependencies()
                .iter()
                .map(|dependency| (*dependency).to_string())
                .collect(),
        }
    }

    /// True only for the exact #796 manifest identity and matching kernel family.
    pub fn matches_source_and_allowlist(
        &self,
        source_region: &SourceRegionIdentity,
        allowlist: &KernelAllowlist,
    ) -> bool {
        let Some(family) = ay_lra_family_from_str(&self.kernel_family) else {
            return false;
        };
        self.schema == AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA
            && self.schema_version == AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA_VERSION
            && self.issue == AY_LRA_PROOF_CONSUMPTION_MANIFEST_ISSUE
            && self.proof_family == family.proof_family()
            && self.allowlist_family == family.as_str()
            && self.required_certificate_dependencies
                == family
                    .required_certificate_dependencies()
                    .iter()
                    .map(|dependency| (*dependency).to_string())
                    .collect::<Vec<_>>()
            && source_region.kernel_family == family.as_str()
            && allowlist.kernel_family == family.as_str()
            && allowlist.allowlist_entry.as_deref() == Some(family.allowlist_entry())
            && allowlist.matches_source_region(source_region)
    }
}

/// Solver evidence for a candidate rewrite.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum SolverEvidence {
    /// No solver result has been attached.
    Pending,
    /// ay proved semantic equivalence.
    // `rename_all = "snake_case"` would split the `AY` acronym into
    // `a_y_equivalence_proof`; the canonical wire name consumed by ay and by
    // `trust-cg-opt`'s admission loader is `ay_equivalence_proof`.
    #[serde(rename = "ay_equivalence_proof")]
    AYEquivalenceProof {
        /// ay/CEGIS proof hash.
        proof_hash: u64,
        /// Number of CEGIS iterations when available.
        cegis_iterations: Option<u32>,
    },
    /// Solver or concrete evaluation found a counterexample.
    Counterexample {
        /// Counterexample values.
        counterexample: CounterexampleRecord,
        /// Reducer or follow-up issue metadata.
        reducer: Option<ReducerMetadata>,
    },
    /// The solver did not prove or disprove the candidate.
    Inconclusive {
        /// Inconclusive reason.
        reason: String,
        /// Reducer or follow-up issue metadata.
        reducer: Option<ReducerMetadata>,
    },
}

impl SolverEvidence {
    fn proof_hash(&self) -> Option<u64> {
        match self {
            Self::AYEquivalenceProof { proof_hash, .. } => Some(*proof_hash),
            Self::Pending | Self::Counterexample { .. } | Self::Inconclusive { .. } => None,
        }
    }
}

/// Serialized counterexample metadata.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CounterexampleRecord {
    /// Sorted variable values.
    pub values: Vec<CounterexampleValue>,
    /// Whether fast concrete evaluation found the counterexample.
    pub found_by_concrete: bool,
}

impl CounterexampleRecord {
    /// Build a deterministic counterexample record from a CEGIS input.
    pub fn from_concrete_input(input: &ConcreteInput, found_by_concrete: bool) -> Self {
        let mut values: Vec<_> = input
            .values
            .iter()
            .map(|(name, value)| CounterexampleValue {
                name: name.clone(),
                value: *value,
            })
            .collect();
        values.sort_by(|lhs, rhs| lhs.name.cmp(&rhs.name));
        Self {
            values,
            found_by_concrete,
        }
    }
}

/// Single counterexample assignment.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CounterexampleValue {
    /// Variable name.
    pub name: String,
    /// Concrete bitvector value.
    pub value: u64,
}

/// Reducer artifact or follow-up issue metadata for failed proofs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReducerMetadata {
    /// Failure classification.
    pub failure_kind: ProofFailureKind,
    /// Reducer identifier or command family.
    pub reducer_id: String,
    /// Optional artifact path.
    pub artifact_path: Option<String>,
    /// Optional artifact hash.
    pub artifact_hash: Option<String>,
    /// Optional follow-up issue title.
    pub follow_up_issue_title: Option<String>,
}

impl ReducerMetadata {
    /// Create reducer metadata for a failed candidate.
    pub fn new(failure_kind: ProofFailureKind, reducer_id: impl Into<String>) -> Self {
        Self {
            failure_kind,
            reducer_id: reducer_id.into(),
            artifact_path: None,
            artifact_hash: None,
            follow_up_issue_title: None,
        }
    }

    /// Attach an artifact path and hash.
    pub fn with_artifact(
        mut self,
        artifact_path: impl Into<String>,
        artifact_hash: impl Into<String>,
    ) -> Self {
        self.artifact_path = Some(artifact_path.into());
        self.artifact_hash = Some(artifact_hash.into());
        self
    }

    /// Attach a follow-up issue title.
    pub fn with_follow_up_issue_title(mut self, title: impl Into<String>) -> Self {
        self.follow_up_issue_title = Some(title.into());
        self
    }
}

/// Failure classes used by reducers and follow-up issues.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ProofFailureKind {
    /// Proof likely needs an extra precondition.
    MissingProofPrecondition,
    /// Candidate transform is incorrect.
    BadCandidate,
    /// Lowering or semantics model may be wrong.
    LoweringOrSemanticsBug,
    /// Product gate rejected an otherwise proved candidate.
    ProductGateMismatch,
}

/// Admission state for a candidate rewrite.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[derive(Default)]
pub enum AdmissionState {
    /// The candidate exists only as disabled metadata.
    #[default]
    Disabled,
    /// Proof has not completed yet.
    PendingProof,
    /// Proof succeeded, but the record is profile-only telemetry.
    ProvedProfileOnly,
    /// Candidate is eligible for downstream declarative rewrite promotion.
    Admitted,
    /// Candidate was rejected by proof or product gates.
    Rejected,
}

/// Named-kernel allowlist scope.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct KernelAllowlist {
    /// Logical kernel family.
    pub kernel_family: String,
    /// Optional concrete kernel name.
    pub kernel_name: Option<String>,
    /// Optional allowlist entry identifier.
    pub allowlist_entry: Option<String>,
    /// Whether this record is allowlisted for promotion.
    pub allowlisted: bool,
}

impl KernelAllowlist {
    /// Create a non-allowlisted scope.
    pub fn not_allowlisted(kernel_family: impl Into<String>) -> Self {
        Self {
            kernel_family: kernel_family.into(),
            kernel_name: None,
            allowlist_entry: None,
            allowlisted: false,
        }
    }

    /// Create an allowlisted named-kernel scope.
    pub fn allowlisted(
        kernel_family: impl Into<String>,
        kernel_name: impl Into<String>,
        allowlist_entry: impl Into<String>,
    ) -> Self {
        Self {
            kernel_family: kernel_family.into(),
            kernel_name: Some(kernel_name.into()),
            allowlist_entry: Some(allowlist_entry.into()),
            allowlisted: true,
        }
    }

    /// Create an allowlist scope for a #796 ay LRA family and named kernel.
    pub fn ay_lra_allowlisted(family: AYLraRewriteKernelFamily) -> Self {
        Self::allowlisted(
            family.as_str(),
            family.default_kernel_name(),
            family.allowlist_entry(),
        )
    }

    /// True when this allowlist is bound to the same family/kernel as a source region.
    pub fn matches_source_region(&self, source_region: &SourceRegionIdentity) -> bool {
        self.kernel_family == source_region.kernel_family
            && match (&self.kernel_name, &source_region.kernel_name) {
                (Some(allowlisted), Some(source)) => allowlisted == source,
                (Some(_), None) => false,
                (None, _) => true,
            }
    }
}

/// Product gate evidence needed before downstream promotion.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProductGateEvidence {
    /// Replay gate passed.
    pub replay_passed: bool,
    /// Telemetry guard is present.
    pub telemetry_guarded: bool,
    /// Rollback or deopt guard is available.
    pub rollback_or_deopt_available: bool,
    /// Product promotion has approved the candidate.
    pub product_promotion_approved: bool,
}

impl ProductGateEvidence {
    /// Product gates that have all passed.
    pub fn all_passed_record() -> Self {
        Self {
            replay_passed: true,
            telemetry_guarded: true,
            rollback_or_deopt_available: true,
            product_promotion_approved: true,
        }
    }

    /// True when every product promotion gate has passed.
    pub fn all_passed(&self) -> bool {
        self.replay_passed
            && self.telemetry_guarded
            && self.rollback_or_deopt_available
            && self.product_promotion_approved
    }
}

/// Stable #800 verdict disposition for proof-guided admission.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[derive(Default)]
pub enum ProofGuidedAdmissionDisposition {
    /// The candidate has complete admission evidence.
    Accepted,
    /// The candidate is non-promoting and must not be registered.
    #[default]
    Rejected,
}

/// Stable #800 typed rejection reasons for proof-guided admission.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ProofGuidedAdmissionRejection {
    /// No complete #800 verdict was attached.
    MissingCompleteAdmissionVerdict,
    /// The verdict schema tag/version is not the #800 verdict schema.
    UnsupportedVerdictSchema,
    /// The verdict is not accepted, or carries rejection reasons.
    VerdictRejected,
    /// Consumed proof facts are absent or incomplete.
    MissingProofFact,
    /// #795 certificate identity is absent.
    MissingCertificateIdentity,
    /// The verdict transform name/version does not match the record.
    TransformIdentityMismatch,
    /// The verdict source trust_ir region hash does not match the record.
    SourceRegionHashMismatch,
    /// Target AArch64/MachIR region identity is absent.
    MissingTargetRegionHash,
    /// ay proof or translation-validation hash is absent or stale.
    FailedValidationHash,
    /// Manifest identity/hash is absent.
    MissingManifestHash,
    /// Runtime status/deopt contract is absent.
    MissingRuntimeStatusContract,
    /// Replay artifact root is absent.
    MissingReplayRoot,
    /// Telemetry event identity is absent.
    MissingTelemetryEvent,
    /// Useful-native telemetry counter is absent.
    MissingTelemetryUsefulNativeCounter,
    /// Rollback/deopt or disable knob is absent.
    MissingRollbackKnob,
}

/// Complete #800 verdict for promoting a proof-guided rewrite candidate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofGuidedAdmissionVerdict {
    /// Verdict schema.
    pub schema: String,
    /// Verdict schema version.
    pub schema_version: u32,
    /// Owning issue.
    pub issue: u64,
    /// Final verdict disposition.
    pub disposition: ProofGuidedAdmissionDisposition,
    /// Stable typed rejection reasons. Accepted verdicts must have none.
    pub rejection_reasons: Vec<ProofGuidedAdmissionRejection>,
    /// Proof facts consumed by the candidate certificate/proof route.
    pub consumed_proof_facts: Vec<String>,
    /// Candidate transform name.
    pub transform_name: String,
    /// Candidate transform version.
    pub transform_version: String,
    /// Source trust_ir region hash.
    pub source_trust_ir_region_hash: String,
    /// Target AArch64/MachIR region hash.
    pub target_aarch64_region_hash: String,
    /// ay equivalence proof or translation-validation result hash.
    pub validation_result_hash: String,
    /// Manifest identity/hash bound to the candidate.
    pub manifest_hash: String,
    /// Runtime guard/deopt status contract.
    pub runtime_status_contract: String,
    /// Replay artifact root.
    pub replay_artifact_root: String,
    /// Telemetry event identity.
    pub telemetry_event_id: String,
    /// Useful-native application counter. `None` means the counter was absent.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub telemetry_useful_native_applications: Option<u64>,
    /// Rollback/deopt or disable knob that can withdraw the rewrite.
    pub rollback_or_disable_knob: String,
}

impl Default for ProofGuidedAdmissionVerdict {
    fn default() -> Self {
        Self::rejected(vec![
            ProofGuidedAdmissionRejection::MissingCompleteAdmissionVerdict,
        ])
    }
}

impl ProofGuidedAdmissionVerdict {
    /// Build a typed rejected verdict.
    pub fn rejected(rejection_reasons: Vec<ProofGuidedAdmissionRejection>) -> Self {
        Self {
            schema: PROOF_GUIDED_ADMISSION_VERDICT_SCHEMA.to_string(),
            schema_version: PROOF_GUIDED_ADMISSION_VERDICT_SCHEMA_VERSION,
            issue: PROOF_GUIDED_ADMISSION_VERDICT_ISSUE,
            disposition: ProofGuidedAdmissionDisposition::Rejected,
            rejection_reasons,
            consumed_proof_facts: Vec::new(),
            transform_name: String::new(),
            transform_version: String::new(),
            source_trust_ir_region_hash: String::new(),
            target_aarch64_region_hash: String::new(),
            validation_result_hash: String::new(),
            manifest_hash: String::new(),
            runtime_status_contract: String::new(),
            replay_artifact_root: String::new(),
            telemetry_event_id: String::new(),
            telemetry_useful_native_applications: None,
            rollback_or_disable_knob: String::new(),
        }
    }

    /// Build a complete accepted verdict for a record.
    #[allow(clippy::too_many_arguments)] // Each argument binds one independently audited schema field.
    pub fn accepted_for_record(
        record: &RewriteAdmissionRecord,
        consumed_proof_facts: Vec<String>,
        target_aarch64_region_hash: impl Into<String>,
        manifest_hash: impl Into<String>,
        runtime_status_contract: impl Into<String>,
        replay_artifact_root: impl Into<String>,
        telemetry_event_id: impl Into<String>,
        telemetry_useful_native_applications: u64,
        rollback_or_disable_knob: impl Into<String>,
    ) -> Self {
        let validation_result_hash = record
            .evidence
            .proof_hash()
            .map(|proof_hash| expected_validation_result_hash(&record.transform, proof_hash))
            .unwrap_or_default();
        Self {
            schema: PROOF_GUIDED_ADMISSION_VERDICT_SCHEMA.to_string(),
            schema_version: PROOF_GUIDED_ADMISSION_VERDICT_SCHEMA_VERSION,
            issue: PROOF_GUIDED_ADMISSION_VERDICT_ISSUE,
            disposition: ProofGuidedAdmissionDisposition::Accepted,
            rejection_reasons: Vec::new(),
            consumed_proof_facts,
            transform_name: record.transform.name.clone(),
            transform_version: record.transform.version.clone(),
            source_trust_ir_region_hash: record.source_region.source_region_hash.clone(),
            target_aarch64_region_hash: target_aarch64_region_hash.into(),
            validation_result_hash,
            manifest_hash: manifest_hash.into(),
            runtime_status_contract: runtime_status_contract.into(),
            replay_artifact_root: replay_artifact_root.into(),
            telemetry_event_id: telemetry_event_id.into(),
            telemetry_useful_native_applications: Some(telemetry_useful_native_applications),
            rollback_or_disable_knob: rollback_or_disable_knob.into(),
        }
    }

    /// Return true when this is the default missing-verdict rejection.
    pub fn is_default_rejected(&self) -> bool {
        self == &Self::default()
    }

    /// Return typed rejection reasons for this record.
    pub fn rejection_reasons_for_record(
        &self,
        record: &RewriteAdmissionRecord,
    ) -> Vec<ProofGuidedAdmissionRejection> {
        let mut reasons = Vec::new();
        if self.schema != PROOF_GUIDED_ADMISSION_VERDICT_SCHEMA
            || self.schema_version != PROOF_GUIDED_ADMISSION_VERDICT_SCHEMA_VERSION
            || self.issue != PROOF_GUIDED_ADMISSION_VERDICT_ISSUE
        {
            reasons.push(ProofGuidedAdmissionRejection::UnsupportedVerdictSchema);
        }
        if self.disposition != ProofGuidedAdmissionDisposition::Accepted
            || !self.rejection_reasons.is_empty()
        {
            reasons.push(ProofGuidedAdmissionRejection::VerdictRejected);
        }
        if record.certificate_identity.is_none() {
            reasons.push(ProofGuidedAdmissionRejection::MissingCertificateIdentity);
        }
        if self.transform_name != record.transform.name
            || self.transform_version != record.transform.version
        {
            reasons.push(ProofGuidedAdmissionRejection::TransformIdentityMismatch);
        }
        if self.source_trust_ir_region_hash != record.source_region.source_region_hash {
            reasons.push(ProofGuidedAdmissionRejection::SourceRegionHashMismatch);
        }
        if missing_required_text(&self.target_aarch64_region_hash) {
            reasons.push(ProofGuidedAdmissionRejection::MissingTargetRegionHash);
        }
        let Some(proof_hash) = record.evidence.proof_hash() else {
            reasons.push(ProofGuidedAdmissionRejection::FailedValidationHash);
            return reasons;
        };
        if self.validation_result_hash
            != expected_validation_result_hash(&record.transform, proof_hash)
        {
            reasons.push(ProofGuidedAdmissionRejection::FailedValidationHash);
        }
        if missing_required_text(&self.manifest_hash) {
            reasons.push(ProofGuidedAdmissionRejection::MissingManifestHash);
        }
        if missing_required_text(&self.runtime_status_contract) {
            reasons.push(ProofGuidedAdmissionRejection::MissingRuntimeStatusContract);
        }
        if missing_required_text(&self.replay_artifact_root) {
            reasons.push(ProofGuidedAdmissionRejection::MissingReplayRoot);
        }
        if missing_required_text(&self.telemetry_event_id) {
            reasons.push(ProofGuidedAdmissionRejection::MissingTelemetryEvent);
        }
        if self.telemetry_useful_native_applications.is_none() {
            reasons.push(ProofGuidedAdmissionRejection::MissingTelemetryUsefulNativeCounter);
        }
        if missing_required_text(&self.rollback_or_disable_knob) {
            reasons.push(ProofGuidedAdmissionRejection::MissingRollbackKnob);
        }
        let missing_proof_fact = if let Some(binding) = &record.ay_lra_manifest_binding {
            binding
                .required_certificate_dependencies
                .iter()
                .any(|required| {
                    !self
                        .consumed_proof_facts
                        .iter()
                        .any(|actual| actual == required)
                })
        } else {
            self.consumed_proof_facts
                .iter()
                .any(|fact| missing_required_text(fact))
        };
        if missing_proof_fact || self.consumed_proof_facts.is_empty() {
            reasons.push(ProofGuidedAdmissionRejection::MissingProofFact);
        }
        reasons
    }

    /// True only for a complete, accepted #800 verdict bound to this record.
    pub fn accepts_record(&self, record: &RewriteAdmissionRecord) -> bool {
        self.rejection_reasons_for_record(record).is_empty()
    }
}

/// #795 proof certificate identity.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CertificateIdentity {
    /// Certificate schema or producer.
    pub producer: String,
    /// Optional certificate hash.
    pub certificate_hash: Option<String>,
    /// Optional certificate chain identifier.
    pub certificate_chain_id: Option<String>,
}

impl CertificateIdentity {
    /// Create a certificate identity placeholder that is never promotion-eligible.
    pub fn placeholder(producer: impl Into<String>) -> Self {
        Self {
            producer: producer.into(),
            certificate_hash: None,
            certificate_chain_id: None,
        }
    }

    /// Build identity metadata from a #795 proof-optimization certificate.
    pub fn from_opt_certificate(certificate: &OptCertificate) -> Self {
        Self {
            producer: PROOF_OPTS_CERTIFICATE_PRODUCER.to_string(),
            certificate_hash: Some(format_u128_hex(certificate.certificate_id)),
            certificate_chain_id: Some(format!(
                "{}@v{}:{}",
                certificate.transform.name,
                certificate.transform.version,
                format_u128_hex(certificate.validation_hash)
            )),
        }
    }

    /// True when this identity has the concrete shape emitted by #795 proof-opts certificates.
    pub fn is_proof_opts_certificate_identity(&self) -> bool {
        self.producer == PROOF_OPTS_CERTIFICATE_PRODUCER
            && self
                .certificate_hash
                .as_deref()
                .is_some_and(is_u128_hex_identity)
            && self
                .certificate_chain_id
                .as_deref()
                .is_some_and(is_proof_opts_certificate_chain_id)
    }

    /// True when this certificate identity is valid and bound to the transform.
    pub fn matches_transform_identity(
        &self,
        transform: &TransformIdentity,
        proof_hash: u64,
    ) -> bool {
        if !self.is_proof_opts_certificate_identity() {
            return false;
        }
        let Some((chain_transform, chain_version, chain_validation_hash)) = self
            .certificate_chain_id
            .as_deref()
            .and_then(parse_proof_opts_certificate_chain_id)
        else {
            return false;
        };
        if chain_transform != transform.name
            || !certificate_chain_version_matches(chain_version, &transform.version)
        {
            return false;
        }

        match transform.certificate_binding_expectation(proof_hash) {
            CertificateBindingExpectation::Unbound => true,
            CertificateBindingExpectation::Invalid => false,
            CertificateBindingExpectation::Bound {
                certificate_hash,
                validation_hash,
            } => {
                self.certificate_hash.as_deref() == Some(certificate_hash)
                    && chain_validation_hash == validation_hash
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct ReviewedCertificateBinding {
    certificate_hash: &'static str,
    validation_hash: &'static str,
}

enum CertificateBindingExpectation<'a> {
    Unbound,
    Invalid,
    Bound {
        certificate_hash: &'a str,
        validation_hash: &'a str,
    },
}

fn format_u128_hex(value: u128) -> String {
    format!("{:032x}", value)
}

fn is_u128_hex_identity(value: &str) -> bool {
    value.len() == 32 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn missing_required_text(value: &str) -> bool {
    value.trim().is_empty()
}

fn is_proof_opts_certificate_chain_id(value: &str) -> bool {
    parse_proof_opts_certificate_chain_id(value).is_some()
}

fn parse_proof_opts_certificate_chain_id(value: &str) -> Option<(&str, &str, &str)> {
    let (transform_and_version, validation_hash) = value.rsplit_once(':')?;
    if !is_u128_hex_identity(validation_hash) {
        return None;
    }
    let (transform_name, version) = transform_and_version.rsplit_once("@v")?;
    if !transform_name.is_empty()
        && !version.is_empty()
        && version.bytes().all(|byte| byte.is_ascii_digit())
    {
        Some((transform_name, version, validation_hash))
    } else {
        None
    }
}

fn certificate_chain_version_matches(chain_version: &str, transform_version: &str) -> bool {
    chain_version == transform_version || format!("v{}", chain_version) == transform_version
}

fn reviewed_certificate_binding(
    transform_name: &str,
    transform_version: &str,
    proof_hash: u64,
) -> Option<ReviewedCertificateBinding> {
    if is_reviewed_certificate_transform(transform_name, transform_version)
        && proof_hash == AY_LRA_SPARSE_ADD_ZERO_PROOF_HASH
    {
        Some(ReviewedCertificateBinding {
            certificate_hash: AY_LRA_SPARSE_ADD_ZERO_CERTIFICATE_HASH,
            validation_hash: AY_LRA_SPARSE_ADD_ZERO_VALIDATION_HASH,
        })
    } else {
        None
    }
}

fn expected_validation_result_hash(transform: &TransformIdentity, proof_hash: u64) -> String {
    transform
        .certificate_validation_hash
        .clone()
        .unwrap_or_else(|| format!("ay-proof:{proof_hash:016x}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::SmtExpr;
    use trust_cg_ir::{InstId, ProofAnnotation};
    use trust_cg_opt::proof_opts::{
        OptAdmissionRoute, OptCertificate, OptCertificateKind, OptConsumedProofFact,
        OptTransformIdentity,
    };

    fn proposal() -> RuleProposal {
        RuleProposal::new(
            SmtExpr::var("x", 64).bvadd(SmtExpr::bv_const(0, 64)),
            SmtExpr::var("x", 64),
        )
        .with_name("add_zero_named_kernel")
        .with_precondition(SmtExpr::bool_const(true))
        .with_cost_estimate(4)
    }

    fn source_region() -> SourceRegionIdentity {
        SourceRegionIdentity::ay_lra(
            "sha256:region",
            "sha256",
            AYLraRewriteKernelFamily::SparseSubstitute,
        )
        .with_function_symbol("_trust_cg_sparse_lra_i64")
        .with_region_label("bb0:0..2")
    }

    fn target() -> TargetAbiLayoutIdentity {
        TargetAbiLayoutIdentity::aarch64(
            "aarch64-apple-darwin",
            "aapcs64",
            "e-m:o-i64:64-i128:128-n32:64-S128",
            "apple-m2",
            vec!["+neon".to_string()],
        )
    }

    fn cost_context() -> CostContext {
        CostContext::aarch64("trust-cg-aarch64", "2026.04", 12, 8)
            .with_profile("named-kernel-hot")
            .with_note("candidate extracted from named sparse kernel")
    }

    fn disabled_record() -> RewriteAdmissionRecord {
        RewriteAdmissionRecord::from_rule_proposal(
            source_region(),
            target(),
            cost_context(),
            &proposal(),
            "v1",
        )
    }

    fn proof_opts_certificate_identity() -> CertificateIdentity {
        CertificateIdentity {
            producer: PROOF_OPTS_CERTIFICATE_PRODUCER.to_string(),
            certificate_hash: Some("0000000000000000feedfacecafebeef".to_string()),
            certificate_chain_id: Some(
                "add_zero_named_kernel@v1:00000000000000000000000000005678".to_string(),
            ),
        }
    }

    fn ay_lra_proof_facts(family: AYLraRewriteKernelFamily) -> Vec<String> {
        family
            .required_certificate_dependencies()
            .iter()
            .map(|fact| (*fact).to_string())
            .collect()
    }

    fn complete_proof_guided_verdict(
        record: &RewriteAdmissionRecord,
        family: AYLraRewriteKernelFamily,
    ) -> ProofGuidedAdmissionVerdict {
        ProofGuidedAdmissionVerdict::accepted_for_record(
            record,
            ay_lra_proof_facts(family),
            format!("machir-target-region:{}", family.as_str()),
            format!("sha256:{}-proof-consumption-manifest", family.as_str()),
            "ay_lra_status_abi_v1",
            format!("replay/{}", family.as_str()),
            format!("telemetry/{}", family.as_str()),
            0,
            format!("trust_cg_disable_admitted_rewrite_{}", family.as_str()),
        )
    }

    fn ay_lra_sparse_add_zero_certificate() -> OptCertificate {
        OptCertificate {
            certificate_id: 0xfeed_face_cafe_beef,
            transform: OptTransformIdentity {
                name: "ay_lra_sparse_add_zero".to_string(),
                version: 1,
            },
            route: OptAdmissionRoute {
                pass: "proof-opts".to_string(),
                admission: "proof-annotation+proof-facts".to_string(),
            },
            annotation: Some(ProofAnnotation::NoOverflow),
            consumed_facts: vec![OptConsumedProofFact::LegacyAnnotation(
                ProofAnnotation::NoOverflow,
            )],
            description: "ay LRA sparse add-zero rewrite certificate".to_string(),
            primary_inst: InstId(7),
            affected_insts: vec![InstId(8)],
            kind: OptCertificateKind::CheckedToUnchecked,
            source_region_hash: 0xa11ce,
            target_region_hash: 0xb0b,
            proof_hash: 0xbeef,
            validation_hash: 0x5678,
            rejection: None,
        }
    }

    fn admitted_ay_lra_sparse_add_zero_record() -> RewriteAdmissionRecord {
        let certificate = ay_lra_sparse_add_zero_certificate();
        let proof_hash =
            u64::try_from(certificate.proof_hash).expect("fixture proof hash fits u64");
        let record = disabled_record()
            .with_cegis_result(
                &CegisResult::Equivalent {
                    proof_hash,
                    iterations: 2,
                },
                None,
            )
            .with_opt_certificate(&certificate)
            .with_ay_lra_kernel_family_binding(AYLraRewriteKernelFamily::SparseSubstitute);
        let verdict =
            complete_proof_guided_verdict(&record, AYLraRewriteKernelFamily::SparseSubstitute);
        record
            .with_proof_guided_admission_verdict(verdict)
            .with_profile_review(
                KernelAllowlist::ay_lra_allowlisted(AYLraRewriteKernelFamily::SparseSubstitute),
                ProductGateEvidence::all_passed_record(),
            )
    }

    fn proved_gated_record_with_admitted_state() -> RewriteAdmissionRecord {
        disabled_record()
            .with_cegis_result(
                &CegisResult::Equivalent {
                    proof_hash: 0xced1_f1ed,
                    iterations: 1,
                },
                None,
            )
            .with_profile_review(
                KernelAllowlist::ay_lra_allowlisted(AYLraRewriteKernelFamily::SparseSubstitute),
                ProductGateEvidence::all_passed_record(),
            )
            .with_admission_state(AdmissionState::Admitted)
    }

    #[test]
    fn disabled_by_default_candidate_is_not_admitted() {
        let record = disabled_record();

        assert_eq!(record.schema, REWRITE_ADMISSION_SCHEMA);
        assert_eq!(
            record.source_region.kernel_family,
            AY_LRA_SPARSE_SUBSTITUTE_KERNEL_FAMILY
        );
        assert_eq!(AY_LRA_PROOF_CONSUMPTION_MANIFEST_ISSUE, 796);
        assert_eq!(record.admission_state, AdmissionState::Disabled);
        assert_eq!(record.evidence, SolverEvidence::Pending);
        assert_eq!(record.aarch64_cost_delta, 4);
        assert!(!record.allowlist.allowlisted);
        assert_eq!(record.proof_assumptions.len(), 1);
        assert!(!record.can_admit_to_declarative_rewrite());

        let json = record.to_json_pretty().expect("record should serialize");
        let roundtrip =
            RewriteAdmissionRecord::from_json_str(&json).expect("record should deserialize");
        assert_eq!(roundtrip, record);
    }

    #[test]
    fn proved_profile_only_candidate_is_not_admitted() {
        let record = disabled_record().with_cegis_result(
            &CegisResult::Equivalent {
                proof_hash: 0x5eed,
                iterations: 2,
            },
            None,
        );

        assert_eq!(record.admission_state, AdmissionState::ProvedProfileOnly);
        assert_eq!(
            record.evidence,
            SolverEvidence::AYEquivalenceProof {
                proof_hash: 0x5eed,
                cegis_iterations: Some(2),
            }
        );
        assert!(!record.can_admit_to_declarative_rewrite());
    }

    #[test]
    fn admitted_allowlisted_record_requires_all_promotion_gates() {
        let record = disabled_record()
            .with_cegis_result(
                &CegisResult::Equivalent {
                    proof_hash: 0xced1_f1ed,
                    iterations: 1,
                },
                None,
            )
            .with_certificate_identity(proof_opts_certificate_identity())
            .with_ay_lra_kernel_family_binding(AYLraRewriteKernelFamily::SparseSubstitute);
        let verdict =
            complete_proof_guided_verdict(&record, AYLraRewriteKernelFamily::SparseSubstitute);
        let record = record
            .with_proof_guided_admission_verdict(verdict)
            .with_profile_review(
                KernelAllowlist::ay_lra_allowlisted(AYLraRewriteKernelFamily::SparseSubstitute),
                ProductGateEvidence::all_passed_record(),
            );

        assert_eq!(record.admission_state, AdmissionState::Admitted);
        assert!(record.can_admit_to_declarative_rewrite());
        assert!(record.certificate_identity.is_some());
        assert!(record.ay_lra_manifest_binding.is_some());
        assert!(record.proof_guided_admission.accepts_record(&record));
    }

    #[test]
    fn admitted_state_with_boolean_product_gates_but_without_800_verdict_is_not_eligible() {
        let record = disabled_record()
            .with_cegis_result(
                &CegisResult::Equivalent {
                    proof_hash: 0xced1_f1ed,
                    iterations: 1,
                },
                None,
            )
            .with_certificate_identity(proof_opts_certificate_identity())
            .with_ay_lra_kernel_family_binding(AYLraRewriteKernelFamily::SparseSubstitute)
            .with_product_gates(ProductGateEvidence::all_passed_record())
            .with_allowlist(KernelAllowlist::ay_lra_allowlisted(
                AYLraRewriteKernelFamily::SparseSubstitute,
            ))
            .with_admission_state(AdmissionState::Admitted);

        assert_eq!(record.admission_state, AdmissionState::Admitted);
        assert!(record.product_gates.all_passed());
        assert_eq!(
            record
                .proof_guided_admission
                .rejection_reasons_for_record(&record),
            vec![
                ProofGuidedAdmissionRejection::VerdictRejected,
                ProofGuidedAdmissionRejection::TransformIdentityMismatch,
                ProofGuidedAdmissionRejection::SourceRegionHashMismatch,
                ProofGuidedAdmissionRejection::MissingTargetRegionHash,
                ProofGuidedAdmissionRejection::FailedValidationHash,
                ProofGuidedAdmissionRejection::MissingManifestHash,
                ProofGuidedAdmissionRejection::MissingRuntimeStatusContract,
                ProofGuidedAdmissionRejection::MissingReplayRoot,
                ProofGuidedAdmissionRejection::MissingTelemetryEvent,
                ProofGuidedAdmissionRejection::MissingTelemetryUsefulNativeCounter,
                ProofGuidedAdmissionRejection::MissingRollbackKnob,
                ProofGuidedAdmissionRejection::MissingProofFact,
            ]
        );
        assert!(!record.can_admit_to_declarative_rewrite());
    }

    #[test]
    fn proof_guided_admission_verdict_reports_typed_missing_evidence() {
        let base = disabled_record()
            .with_cegis_result(
                &CegisResult::Equivalent {
                    proof_hash: 0xced1_f1ed,
                    iterations: 1,
                },
                None,
            )
            .with_certificate_identity(proof_opts_certificate_identity())
            .with_ay_lra_kernel_family_binding(AYLraRewriteKernelFamily::SparseSubstitute);
        let mut verdict =
            complete_proof_guided_verdict(&base, AYLraRewriteKernelFamily::SparseSubstitute);
        verdict.consumed_proof_facts.pop();
        verdict.manifest_hash.clear();
        verdict.replay_artifact_root.clear();
        verdict.telemetry_useful_native_applications = None;
        verdict.validation_result_hash = "sha256:stale-validation".to_string();
        verdict.rollback_or_disable_knob.clear();

        let reasons = verdict.rejection_reasons_for_record(&base);

        assert!(reasons.contains(&ProofGuidedAdmissionRejection::MissingProofFact));
        assert!(reasons.contains(&ProofGuidedAdmissionRejection::MissingManifestHash));
        assert!(reasons.contains(&ProofGuidedAdmissionRejection::MissingReplayRoot));
        assert!(
            reasons.contains(&ProofGuidedAdmissionRejection::MissingTelemetryUsefulNativeCounter)
        );
        assert!(reasons.contains(&ProofGuidedAdmissionRejection::FailedValidationHash));
        assert!(reasons.contains(&ProofGuidedAdmissionRejection::MissingRollbackKnob));
    }

    #[test]
    fn admitted_state_without_certificate_identity_is_not_eligible() {
        let record = proved_gated_record_with_admitted_state()
            .with_ay_lra_kernel_family_binding(AYLraRewriteKernelFamily::SparseSubstitute);

        assert_eq!(record.admission_state, AdmissionState::Admitted);
        assert!(record.certificate_identity.is_none());
        assert!(!record.can_admit_to_declarative_rewrite());
    }

    #[test]
    fn admitted_state_with_placeholder_certificate_identity_is_not_eligible() {
        let record = proved_gated_record_with_admitted_state()
            .with_certificate_identity(CertificateIdentity::placeholder("proof-opts-#795"))
            .with_ay_lra_kernel_family_binding(AYLraRewriteKernelFamily::SparseSubstitute);

        assert_eq!(record.admission_state, AdmissionState::Admitted);
        assert!(!record.can_admit_to_declarative_rewrite());
    }

    #[test]
    fn admitted_state_requires_certificate_chain_to_match_transform_identity() {
        let mut certificate_identity = proof_opts_certificate_identity();
        certificate_identity.certificate_chain_id =
            Some("other_transform@v1:00000000000000000000000000005678".to_string());
        let record = proved_gated_record_with_admitted_state()
            .with_certificate_identity(certificate_identity)
            .with_ay_lra_kernel_family_binding(AYLraRewriteKernelFamily::SparseSubstitute);

        assert_eq!(record.admission_state, AdmissionState::Admitted);
        assert!(!record.can_admit_to_declarative_rewrite());
    }

    #[test]
    fn admitted_state_without_ay_lra_manifest_binding_is_not_eligible() {
        let record = proved_gated_record_with_admitted_state()
            .with_certificate_identity(proof_opts_certificate_identity());

        assert_eq!(record.admission_state, AdmissionState::Admitted);
        assert!(record.ay_lra_manifest_binding.is_none());
        assert!(!record.can_admit_to_declarative_rewrite());
    }

    #[test]
    fn admitted_state_with_mismatched_ay_lra_kernel_family_is_not_eligible() {
        let record = proved_gated_record_with_admitted_state()
            .with_certificate_identity(proof_opts_certificate_identity())
            .with_ay_lra_kernel_family_binding(AYLraRewriteKernelFamily::BasisUpdate);

        assert_eq!(record.admission_state, AdmissionState::Admitted);
        assert!(!record.can_admit_to_declarative_rewrite());
    }

    #[test]
    fn admitted_state_requires_exact_ay_lra_allowlist_entry() {
        let record = proved_gated_record_with_admitted_state()
            .with_certificate_identity(proof_opts_certificate_identity())
            .with_ay_lra_kernel_family_binding(AYLraRewriteKernelFamily::SparseSubstitute)
            .with_allowlist(KernelAllowlist::allowlisted(
                AY_LRA_SPARSE_SUBSTITUTE_KERNEL_FAMILY,
                AYLraRewriteKernelFamily::SparseSubstitute.default_kernel_name(),
                "rewrite-admission/spoofed-entry",
            ));

        assert_eq!(record.admission_state, AdmissionState::Admitted);
        assert!(!record.can_admit_to_declarative_rewrite());
    }

    #[test]
    fn profile_review_keeps_proved_candidate_profile_only_until_gates_pass() {
        let record = disabled_record()
            .with_cegis_result(
                &CegisResult::Equivalent {
                    proof_hash: 0xced1_f1ed,
                    iterations: 1,
                },
                None,
            )
            .with_profile_review(
                KernelAllowlist::ay_lra_allowlisted(AYLraRewriteKernelFamily::SparseSubstitute),
                ProductGateEvidence {
                    replay_passed: true,
                    telemetry_guarded: true,
                    rollback_or_deopt_available: true,
                    product_promotion_approved: false,
                },
            );

        assert_eq!(record.admission_state, AdmissionState::ProvedProfileOnly);
        assert!(!record.can_admit_to_declarative_rewrite());
    }

    #[test]
    fn rule_discovery_result_bridge_preserves_transform_and_proof_identity() {
        let rule = DiscoveredRule {
            name: "ay_lra_sparse_add_zero".to_string(),
            pattern: SmtExpr::var("x", 64).bvadd(SmtExpr::bv_const(0, 64)),
            replacement: SmtExpr::var("x", 64),
            preconditions: vec![SmtExpr::bool_const(true)],
            proof_hash: 0x51a5_5eed,
            cost_delta: 4,
            verified_width: 64,
            cegis_iterations: 3,
        };

        let record = disabled_record().with_rule_result(&RuleResult::Accepted(rule.clone()), None);

        assert_eq!(record.admission_state, AdmissionState::ProvedProfileOnly);
        assert_eq!(record.transform.name, "add_zero_named_kernel");
        assert_eq!(
            record.transform.discovered_rule_name,
            Some(rule.name.clone())
        );
        assert_eq!(
            record.transform.discovered_rule_proof_hash,
            Some(0x51a5_5eed)
        );
        assert_eq!(
            record.evidence,
            SolverEvidence::AYEquivalenceProof {
                proof_hash: 0x51a5_5eed,
                cegis_iterations: Some(3),
            }
        );
        assert!(!record.can_admit_to_declarative_rewrite());
    }

    #[test]
    fn rejected_rule_result_records_counterexample_and_reducer_path() {
        let reducer =
            ReducerMetadata::new(ProofFailureKind::BadCandidate, "ay-named-kernel-reducer")
                .with_follow_up_issue_title("Rewrite admission rejected bad sparse candidate");
        let result = RuleResult::Rejected {
            counterexample: ConcreteInput::from_pairs(&[("rhs", 9), ("lhs", 7)]),
            found_by_concrete: true,
        };

        let record = disabled_record().with_rule_result(&result, Some(reducer.clone()));

        assert_eq!(record.admission_state, AdmissionState::Rejected);
        match record.evidence {
            SolverEvidence::Counterexample {
                counterexample,
                reducer: Some(actual_reducer),
            } => {
                assert_eq!(actual_reducer, reducer);
                assert!(counterexample.found_by_concrete);
                assert_eq!(
                    counterexample.values,
                    vec![
                        CounterexampleValue {
                            name: "lhs".to_string(),
                            value: 7,
                        },
                        CounterexampleValue {
                            name: "rhs".to_string(),
                            value: 9,
                        },
                    ]
                );
            }
            other => panic!("expected counterexample evidence, got {:?}", other),
        }
    }

    #[test]
    fn proof_opt_certificate_bridge_carries_795_identity() {
        let certificate = OptCertificate {
            certificate_id: 0xfeed_face_cafe_beef,
            transform: OptTransformIdentity {
                name: "proof-opts.no-overflow.checked-to-unchecked".to_string(),
                version: 1,
            },
            route: OptAdmissionRoute {
                pass: "proof-opts".to_string(),
                admission: "proof-annotation".to_string(),
            },
            annotation: Some(ProofAnnotation::NoOverflow),
            consumed_facts: vec![OptConsumedProofFact::LegacyAnnotation(
                ProofAnnotation::NoOverflow,
            )],
            description: "ADDS proof removes overflow trap".to_string(),
            primary_inst: InstId(7),
            affected_insts: vec![InstId(8)],
            kind: OptCertificateKind::CheckedToUnchecked,
            source_region_hash: 0xa11ce,
            target_region_hash: 0xb0b,
            proof_hash: 0x1234,
            validation_hash: 0x5678,
            rejection: None,
        };

        let record = disabled_record().with_opt_certificate(&certificate);
        let identity = record
            .certificate_identity
            .as_ref()
            .expect("certificate identity should be attached");

        assert_eq!(
            record.transform.name,
            "proof-opts.no-overflow.checked-to-unchecked"
        );
        assert_eq!(record.transform.version, "v1");
        assert_eq!(
            record.transform.discovered_rule_name.as_deref(),
            Some("proof-opts.no-overflow.checked-to-unchecked")
        );
        assert_eq!(record.transform.discovered_rule_proof_hash, Some(0x1234));
        assert_eq!(
            record.transform.certificate_hash.as_deref(),
            Some("0000000000000000feedfacecafebeef")
        );
        assert_eq!(
            record.transform.certificate_validation_hash.as_deref(),
            Some("00000000000000000000000000005678")
        );
        assert_eq!(identity.producer, "trust-cg-opt.proof-opts");
        assert_eq!(
            identity.certificate_hash.as_deref(),
            Some("0000000000000000feedfacecafebeef")
        );
        assert_eq!(
            identity.certificate_chain_id.as_deref(),
            Some("proof-opts.no-overflow.checked-to-unchecked@v1:00000000000000000000000000005678")
        );
    }

    #[test]
    fn opt_certificate_admitted_record_roundtrips_to_opt_preview_loader() {
        let certificate = ay_lra_sparse_add_zero_certificate();
        let proof_hash =
            u64::try_from(certificate.proof_hash).expect("fixture proof hash fits u64");
        let record = admitted_ay_lra_sparse_add_zero_record();

        assert_eq!(record.admission_state, AdmissionState::Admitted);
        assert!(record.can_admit_to_declarative_rewrite());
        assert_eq!(record.transform.name, "ay_lra_sparse_add_zero");
        assert_eq!(record.transform.version, "v1");
        assert_eq!(
            record.transform.discovered_rule_name.as_deref(),
            Some("ay_lra_sparse_add_zero")
        );
        assert_eq!(
            record.transform.discovered_rule_proof_hash,
            Some(proof_hash)
        );

        let json = record.to_json_pretty().expect("record should serialize");
        let preview = trust_cg_opt::rewrite::load_admitted_rewrites_from_json(
            [json.as_str()],
            trust_cg_opt::rewrite::RewriteAdmissionLoaderConfig::enabled_for_preview(),
        )
        .expect("verify-produced record should load in opt preview");
        assert_eq!(preview.parsed_records, 1);
        assert_eq!(preview.eligible_records, 1);
        assert_eq!(preview.registered_rules, 0);
        assert_eq!(
            preview.loaded_records[0].transform_name,
            "ay_lra_sparse_add_zero"
        );
        assert_eq!(preview.loaded_records[0].transform_version, "v1");
        assert_eq!(
            preview.loaded_records[0].discovered_rule_proof_hash,
            Some(proof_hash)
        );

        let mut engine = trust_cg_opt::rewrite::RewriteEngine::new();
        let registered = trust_cg_opt::rewrite::register_admitted_rewrites_from_json(
            [json.as_str()],
            trust_cg_opt::rewrite::RewriteAdmissionLoaderConfig::enabled_for_preview(),
            &mut engine,
        )
        .expect("verify-produced record should select reviewed opt registry entry");
        assert_eq!(registered.eligible_records, 1);
        assert_eq!(registered.registered_rules, 1);
        assert_eq!(engine.num_rules(), 1);
    }

    #[test]
    fn opt_certificate_admitted_record_rejects_stale_same_transform_certificate_hash() {
        let mut record = admitted_ay_lra_sparse_add_zero_record();
        record
            .certificate_identity
            .as_mut()
            .expect("certificate identity should be attached")
            .certificate_hash = Some("0000000000000000feedfacecafebe00".to_string());

        assert_eq!(record.admission_state, AdmissionState::Admitted);
        assert!(!record.can_admit_to_declarative_rewrite());
    }

    #[test]
    fn opt_certificate_admitted_record_rejects_stale_same_transform_validation_hash() {
        let mut record = admitted_ay_lra_sparse_add_zero_record();
        let identity = record
            .certificate_identity
            .as_mut()
            .expect("certificate identity should be attached");
        identity.certificate_chain_id =
            Some("ay_lra_sparse_add_zero@v1:00000000000000000000000000005679".to_string());

        assert_eq!(record.admission_state, AdmissionState::Admitted);
        assert!(!record.can_admit_to_declarative_rewrite());
    }

    #[test]
    fn opt_certificate_admitted_record_rejects_legacy_unbound_stale_same_transform_identity() {
        let mut record = admitted_ay_lra_sparse_add_zero_record();
        let stale_proof_hash = AY_LRA_SPARSE_ADD_ZERO_PROOF_HASH + 1;
        record.transform.discovered_rule_proof_hash = Some(stale_proof_hash);
        record.transform.certificate_hash = None;
        record.transform.certificate_validation_hash = None;
        record.evidence = SolverEvidence::AYEquivalenceProof {
            proof_hash: stale_proof_hash,
            cegis_iterations: Some(2),
        };
        let identity = record
            .certificate_identity
            .as_mut()
            .expect("certificate identity should be attached");
        identity.certificate_hash = Some("0000000000000000feedfacecafebe00".to_string());
        identity.certificate_chain_id =
            Some("ay_lra_sparse_add_zero@v1:00000000000000000000000000005679".to_string());

        assert_eq!(record.admission_state, AdmissionState::Admitted);
        assert!(!record.can_admit_to_declarative_rewrite());
    }

    #[test]
    fn opt_certificate_admitted_record_rejects_stale_solver_proof_hash() {
        let mut record = admitted_ay_lra_sparse_add_zero_record();
        let stale_proof_hash = AY_LRA_SPARSE_ADD_ZERO_PROOF_HASH + 1;
        record.evidence = SolverEvidence::AYEquivalenceProof {
            proof_hash: stale_proof_hash,
            cegis_iterations: Some(2),
        };

        assert_eq!(record.admission_state, AdmissionState::Admitted);
        assert_eq!(
            record.transform.discovered_rule_proof_hash,
            Some(AY_LRA_SPARSE_ADD_ZERO_PROOF_HASH)
        );
        assert!(!record.can_admit_to_declarative_rewrite());

        let json = record.to_json_pretty().expect("record should serialize");
        let preview = trust_cg_opt::rewrite::load_admitted_rewrites_from_json(
            [json.as_str()],
            trust_cg_opt::rewrite::RewriteAdmissionLoaderConfig::enabled_for_preview(),
        )
        .expect("stale solver proof record should parse");
        assert_eq!(preview.parsed_records, 1);
        assert_eq!(preview.eligible_records, 0);
    }

    #[test]
    fn counterexample_records_reducer_path_and_rejects_candidate() {
        let reducer = ReducerMetadata::new(
            ProofFailureKind::MissingProofPrecondition,
            "ay-named-kernel-reducer",
        )
        .with_artifact("artifacts/reducers/sparse_lra_i64.json", "sha256:reducer")
        .with_follow_up_issue_title("Rewrite admission needs precondition for sparse_lra_i64");
        let result = CegisResult::NotEquivalent {
            counterexample: ConcreteInput::from_pairs(&[("b", 2), ("a", 1)]),
            found_by_concrete: false,
        };

        let record = disabled_record().with_cegis_result(&result, Some(reducer.clone()));

        assert_eq!(record.admission_state, AdmissionState::Rejected);
        assert!(!record.can_admit_to_declarative_rewrite());
        match record.evidence {
            SolverEvidence::Counterexample {
                counterexample,
                reducer: Some(actual_reducer),
            } => {
                assert_eq!(actual_reducer, reducer);
                assert_eq!(
                    counterexample.values,
                    vec![
                        CounterexampleValue {
                            name: "a".to_string(),
                            value: 1,
                        },
                        CounterexampleValue {
                            name: "b".to_string(),
                            value: 2,
                        },
                    ]
                );
                assert!(!counterexample.found_by_concrete);
            }
            other => panic!("expected counterexample evidence, got {:?}", other),
        }
    }
}
