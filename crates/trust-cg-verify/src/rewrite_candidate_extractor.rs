// trust-cg-verify/rewrite_candidate_extractor.rs - named kernel rewrite extraction
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Candidate-region extraction data for solver-discovered rewrite admission.
//!
//! This module is intentionally verify-side only. It recognizes a small set of
//! named AArch64 ay/TY kernel families and serializes the source-region,
//! proof-assumption, target ABI/layout, and cost-model inputs needed to build a
//! disabled [`RewriteAdmissionRecord`]. It does not register dynamic rewrites.

use crate::rewrite_admission::{
    AY_LRA_BASIS_UPDATE_KERNEL_FAMILY, AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA,
    AY_LRA_SPARSE_SUBSTITUTE_KERNEL_FAMILY, AYLraRewriteKernelFamily, AdmissionState, CostContext,
    KernelAllowlist, ProofAssumption, ProofAssumptionKind, RewriteAdmissionRecord,
    SourceRegionIdentity, TargetAbiLayoutIdentity, TransformIdentity,
};
use serde::{Deserialize, Serialize};
use trust_cg_opt::cache::StableHasher;

/// Schema tag for serialized candidate-region extraction records.
pub const REWRITE_CANDIDATE_EXTRACTOR_SCHEMA: &str = "trust-cg.rewrite_candidate_extractor.v1";

/// Numeric schema version for candidate-region extraction records.
pub const REWRITE_CANDIDATE_EXTRACTOR_SCHEMA_VERSION: u32 = 1;

/// Stable hash algorithm name used by the extractor for source regions.
pub const REWRITE_CANDIDATE_SOURCE_HASH_ALGORITHM: &str = "trust-cg-stable128-v1";

/// Stable TY native-fused parent-loop rewrite kernel family id.
pub const TY_NATIVE_FUSED_PARENT_LOOP_KERNEL_FAMILY: &str = "ty_native_fused_parent_loop";

/// Stable TY native-fused parent-loop default kernel name.
pub const TY_NATIVE_FUSED_PARENT_LOOP_DEFAULT_KERNEL_NAME: &str =
    "mcl_shaped_native_fused_parent_loop";

/// Stable TY native-fused parent-loop consumer mode.
pub const TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE: &str = "native-fused-parent-loop";

/// Stable TY native-fused parent-loop manifest schema.
pub const TY_NATIVE_FUSED_PARENT_LOOP_MANIFEST_SCHEMA: &str =
    "trust-cg.ty.native_fused_parent_loop_manifest/v1";

/// Stable TY native-fused parent-loop status/deopt contract.
pub const TY_NATIVE_FUSED_PARENT_LOOP_STATUS_DEOPT_CONTRACT: &str =
    "ty.native_fused_parent_loop.status_deopt_abi.v1";

const EXTRACTOR_NAME: &str = "trust-cg-verify.rewrite-candidate-extractor";

const TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA: &[(&str, &str)] = &[
    (
        "ty.native_fused.fact.state_layout_stability",
        "state_layout_stability",
    ),
    (
        "ty.native_fused.fact.helper_purity_readonly",
        "helper_purity_readonly",
    ),
    (
        "ty.native_fused.fact.action_independence_or_fused_step_equivalence",
        "action_independence_or_fused_step_equivalence",
    ),
    (
        "ty.native_fused.fact.state_vector_bounds",
        "state_vector_bounds",
    ),
    (
        "ty.native_fused.fact.dispatch_panic_deopt_safety",
        "dispatch_panic_deopt_safety",
    ),
];

/// Input metadata for extracting one named AArch64 candidate region.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CandidateRegionExtractionInput {
    /// Logical kernel family from the producer.
    pub kernel_family: String,
    /// Concrete kernel name. Missing or empty names are not extracted.
    pub kernel_name: Option<String>,
    /// Optional function symbol containing the source region.
    pub function_symbol: Option<String>,
    /// Optional producer-local source region label.
    pub region_label: Option<String>,
    /// Canonical source-region bytes used to compute the region hash.
    pub source_region_payload: Vec<u8>,
    /// Additional proof assumptions supplied by the producer.
    pub proof_assumptions: Vec<ProofAssumption>,
    /// Target ABI and layout identity for proof/cost replay.
    pub target: TargetAbiLayoutIdentity,
    /// Cost model context for the source and replacement regions.
    pub cost_context: CostContext,
    /// Candidate transform identity.
    pub transform: TransformIdentity,
}

impl CandidateRegionExtractionInput {
    /// Build input metadata for one candidate region.
    pub fn new(
        kernel_family: impl Into<String>,
        kernel_name: impl Into<String>,
        source_region_payload: impl Into<Vec<u8>>,
        target: TargetAbiLayoutIdentity,
        cost_context: CostContext,
        transform: TransformIdentity,
    ) -> Self {
        Self {
            kernel_family: kernel_family.into(),
            kernel_name: Some(kernel_name.into()),
            function_symbol: None,
            region_label: None,
            source_region_payload: source_region_payload.into(),
            proof_assumptions: Vec::new(),
            target,
            cost_context,
            transform,
        }
    }

    /// Build input metadata without a concrete kernel name.
    pub fn unnamed(
        kernel_family: impl Into<String>,
        source_region_payload: impl Into<Vec<u8>>,
        target: TargetAbiLayoutIdentity,
        cost_context: CostContext,
        transform: TransformIdentity,
    ) -> Self {
        Self {
            kernel_family: kernel_family.into(),
            kernel_name: None,
            function_symbol: None,
            region_label: None,
            source_region_payload: source_region_payload.into(),
            proof_assumptions: Vec::new(),
            target,
            cost_context,
            transform,
        }
    }

    /// Attach a function symbol.
    pub fn with_function_symbol(mut self, function_symbol: impl Into<String>) -> Self {
        self.function_symbol = Some(function_symbol.into());
        self
    }

    /// Attach a producer-local source-region label.
    pub fn with_region_label(mut self, region_label: impl Into<String>) -> Self {
        self.region_label = Some(region_label.into());
        self
    }

    /// Attach one explicit proof assumption.
    pub fn with_proof_assumption(mut self, proof_assumption: ProofAssumption) -> Self {
        self.proof_assumptions.push(proof_assumption);
        self
    }
}

/// Recognized named AArch64 kernel family for rewrite candidate extraction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CandidateKernelFamily {
    /// ay LRA sparse substitute kernel.
    AYLraSparseSubstitute,
    /// ay LRA basis update kernel.
    AYLraBasisUpdate,
    /// TY native-fused parent-loop kernel.
    TyNativeFusedParentLoop,
}

impl CandidateKernelFamily {
    /// Classify a named kernel family/name pair.
    pub fn classify(kernel_family: &str, kernel_name: Option<&str>) -> Option<Self> {
        let kernel_name = kernel_name.filter(|name| !name.trim().is_empty())?;
        match kernel_family {
            AY_LRA_SPARSE_SUBSTITUTE_KERNEL_FAMILY
                if kernel_name
                    == AYLraRewriteKernelFamily::SparseSubstitute.default_kernel_name() =>
            {
                Some(Self::AYLraSparseSubstitute)
            }
            AY_LRA_BASIS_UPDATE_KERNEL_FAMILY
                if kernel_name == AYLraRewriteKernelFamily::BasisUpdate.default_kernel_name() =>
            {
                Some(Self::AYLraBasisUpdate)
            }
            TY_NATIVE_FUSED_PARENT_LOOP_KERNEL_FAMILY
                if kernel_name == TY_NATIVE_FUSED_PARENT_LOOP_DEFAULT_KERNEL_NAME =>
            {
                Some(Self::TyNativeFusedParentLoop)
            }
            _ => None,
        }
    }

    /// Stable logical kernel family id.
    pub const fn kernel_family(self) -> &'static str {
        match self {
            Self::AYLraSparseSubstitute => AY_LRA_SPARSE_SUBSTITUTE_KERNEL_FAMILY,
            Self::AYLraBasisUpdate => AY_LRA_BASIS_UPDATE_KERNEL_FAMILY,
            Self::TyNativeFusedParentLoop => TY_NATIVE_FUSED_PARENT_LOOP_KERNEL_FAMILY,
        }
    }

    /// Consumer that owns this family.
    pub const fn consumer(self) -> &'static str {
        match self {
            Self::AYLraSparseSubstitute | Self::AYLraBasisUpdate => "ay",
            Self::TyNativeFusedParentLoop => "ty",
        }
    }

    fn ay_lra_family(self) -> Option<AYLraRewriteKernelFamily> {
        match self {
            Self::AYLraSparseSubstitute => Some(AYLraRewriteKernelFamily::SparseSubstitute),
            Self::AYLraBasisUpdate => Some(AYLraRewriteKernelFamily::BasisUpdate),
            Self::TyNativeFusedParentLoop => None,
        }
    }
}

/// Serializable input bundle accepted by [`RewriteAdmissionRecord::new`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RewriteAdmissionRecordInputs {
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
}

impl RewriteAdmissionRecordInputs {
    /// Build a disabled-by-default admission record from these inputs.
    pub fn into_disabled_record(self) -> RewriteAdmissionRecord {
        let family = self.source_region.kernel_family.clone();
        RewriteAdmissionRecord::new(
            self.source_region,
            self.proof_assumptions,
            self.target,
            self.cost_context,
            self.transform,
        )
        .with_allowlist(KernelAllowlist::not_allowlisted(family))
        .with_admission_state(AdmissionState::Disabled)
    }
}

/// Metadata about a recognized extraction surface.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CandidateRegionExtractionMetadata {
    /// Extractor implementation identity.
    pub extractor: String,
    /// Extractor schema version.
    pub extractor_version: u32,
    /// Recognized family.
    pub kernel_family: CandidateKernelFamily,
    /// Owning consumer.
    pub consumer: String,
    /// Optional proof/manifest schema tied to this family.
    pub manifest_schema: Option<String>,
    /// Optional status/deopt ABI contract tied to this family.
    pub status_deopt_contract: Option<String>,
    /// Required proof facts/dependencies serialized by the extractor.
    pub required_proof_facts: Vec<String>,
    /// Extra deterministic extraction notes.
    pub notes: Vec<String>,
}

/// Extracted candidate-region data for rewrite admission.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExtractedRewriteAdmissionCandidate {
    /// Stable extractor schema.
    pub schema: String,
    /// Stable extractor schema version.
    pub schema_version: u32,
    /// Rewrite admission record inputs.
    pub inputs: RewriteAdmissionRecordInputs,
    /// Extraction metadata for audit/replay.
    pub metadata: CandidateRegionExtractionMetadata,
}

impl ExtractedRewriteAdmissionCandidate {
    /// Build a disabled admission record. For ay LRA families, this also
    /// attaches the canonical #796 manifest binding. No product gates or
    /// dynamic rewrite registration are enabled.
    pub fn to_disabled_record(&self) -> RewriteAdmissionRecord {
        let record = self.inputs.clone().into_disabled_record();
        match self.metadata.kernel_family.ay_lra_family() {
            Some(family) => record.with_ay_lra_kernel_family_binding(family),
            None => record,
        }
    }
}

/// Extract candidate-region inputs for recognized named AArch64 kernels.
///
/// Returns `None` for non-AArch64 targets, unknown families, or missing/empty
/// kernel names.
pub fn extract_rewrite_admission_candidate(
    input: CandidateRegionExtractionInput,
) -> Option<ExtractedRewriteAdmissionCandidate> {
    if input.target.arch != "aarch64" {
        return None;
    }

    let kernel_name = input.kernel_name.as_deref();
    let family = CandidateKernelFamily::classify(input.kernel_family.as_str(), kernel_name)?;
    let source_region_hash = stable_source_region_hash(&input, family);
    let source_region = SourceRegionIdentity::new(
        source_region_hash,
        REWRITE_CANDIDATE_SOURCE_HASH_ALGORITHM,
        family.kernel_family(),
    );
    let source_region = {
        let kernel_name = input.kernel_name?;
        source_region.with_kernel_name(kernel_name)
    };
    let source_region = if let Some(function_symbol) = input.function_symbol {
        source_region.with_function_symbol(function_symbol)
    } else {
        source_region
    };
    let source_region = if let Some(region_label) = input.region_label {
        source_region.with_region_label(region_label)
    } else {
        source_region
    };

    let mut proof_assumptions = canonical_proof_assumptions(family, &input.target);
    proof_assumptions.extend(input.proof_assumptions);

    let metadata = extraction_metadata(family);

    Some(ExtractedRewriteAdmissionCandidate {
        schema: REWRITE_CANDIDATE_EXTRACTOR_SCHEMA.to_string(),
        schema_version: REWRITE_CANDIDATE_EXTRACTOR_SCHEMA_VERSION,
        inputs: RewriteAdmissionRecordInputs {
            source_region,
            proof_assumptions,
            target: input.target,
            cost_context: input.cost_context,
            transform: input.transform,
        },
        metadata,
    })
}

fn stable_source_region_hash(
    input: &CandidateRegionExtractionInput,
    family: CandidateKernelFamily,
) -> String {
    let mut hasher = StableHasher::new();
    hasher.write_str(REWRITE_CANDIDATE_EXTRACTOR_SCHEMA);
    hasher.write_str(family.kernel_family());
    hasher.write_str(input.kernel_name.as_deref().unwrap_or(""));
    hasher.write_str(input.function_symbol.as_deref().unwrap_or(""));
    hasher.write_str(input.region_label.as_deref().unwrap_or(""));
    hasher.write_framed(&input.source_region_payload);
    format!("trust-cg-stable128:{:032x}", hasher.finish128())
}

fn canonical_proof_assumptions(
    family: CandidateKernelFamily,
    target: &TargetAbiLayoutIdentity,
) -> Vec<ProofAssumption> {
    let mut assumptions = vec![ProofAssumption {
        id: format!("{}.target_abi_layout", family.kernel_family()),
        kind: ProofAssumptionKind::AbiLayout,
        formula: format!(
            "arch={} target_triple={} abi={} data_layout={} cpu={} features={}",
            target.arch,
            target.target_triple,
            target.abi,
            target.data_layout,
            target.cpu,
            target.features.join(",")
        ),
        source: "CandidateRegionExtractionInput::target".to_string(),
    }];

    match family {
        CandidateKernelFamily::AYLraSparseSubstitute => {
            assumptions.extend(ay_lra_assumptions(
                AYLraRewriteKernelFamily::SparseSubstitute,
            ));
        }
        CandidateKernelFamily::AYLraBasisUpdate => {
            assumptions.extend(ay_lra_assumptions(AYLraRewriteKernelFamily::BasisUpdate));
        }
        CandidateKernelFamily::TyNativeFusedParentLoop => {
            assumptions.extend(ty_native_fused_assumptions());
        }
    }

    assumptions
}

fn ay_lra_assumptions(family: AYLraRewriteKernelFamily) -> Vec<ProofAssumption> {
    family
        .required_certificate_dependencies()
        .iter()
        .map(|dependency| ProofAssumption {
            id: (*dependency).to_string(),
            kind: ProofAssumptionKind::KernelInvariant,
            formula: format!("required_ay_lra_certificate_dependency={dependency}"),
            source: AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA.to_string(),
        })
        .collect()
}

fn ty_native_fused_assumptions() -> Vec<ProofAssumption> {
    let mut assumptions: Vec<_> = TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA
        .iter()
        .map(|(metadata_key, fact)| ProofAssumption {
            id: (*metadata_key).to_string(),
            kind: ProofAssumptionKind::KernelInvariant,
            formula: format!("required_ty_native_fused_fact={fact}"),
            source: TY_NATIVE_FUSED_PARENT_LOOP_MANIFEST_SCHEMA.to_string(),
        })
        .collect();
    assumptions.push(ProofAssumption {
        id: "ty.native_fused.status_deopt_contract".to_string(),
        kind: ProofAssumptionKind::AbiLayout,
        formula: format!(
            "status_deopt_contract={}",
            TY_NATIVE_FUSED_PARENT_LOOP_STATUS_DEOPT_CONTRACT
        ),
        source: TY_NATIVE_FUSED_PARENT_LOOP_MANIFEST_SCHEMA.to_string(),
    });
    assumptions
}

fn extraction_metadata(family: CandidateKernelFamily) -> CandidateRegionExtractionMetadata {
    match family {
        CandidateKernelFamily::AYLraSparseSubstitute => ay_lra_metadata(
            family,
            AYLraRewriteKernelFamily::SparseSubstitute,
            "disabled extraction for #796 ay LRA sparse substitute",
        ),
        CandidateKernelFamily::AYLraBasisUpdate => ay_lra_metadata(
            family,
            AYLraRewriteKernelFamily::BasisUpdate,
            "disabled extraction for #796 ay LRA basis update",
        ),
        CandidateKernelFamily::TyNativeFusedParentLoop => CandidateRegionExtractionMetadata {
            extractor: EXTRACTOR_NAME.to_string(),
            extractor_version: REWRITE_CANDIDATE_EXTRACTOR_SCHEMA_VERSION,
            kernel_family: family,
            consumer: family.consumer().to_string(),
            manifest_schema: Some(TY_NATIVE_FUSED_PARENT_LOOP_MANIFEST_SCHEMA.to_string()),
            status_deopt_contract: Some(
                TY_NATIVE_FUSED_PARENT_LOOP_STATUS_DEOPT_CONTRACT.to_string(),
            ),
            required_proof_facts: TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA
                .iter()
                .map(|(metadata_key, _fact)| (*metadata_key).to_string())
                .collect(),
            notes: vec![format!(
                "consumer_mode={}",
                TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE
            )],
        },
    }
}

fn ay_lra_metadata(
    family: CandidateKernelFamily,
    ay_family: AYLraRewriteKernelFamily,
    note: &str,
) -> CandidateRegionExtractionMetadata {
    CandidateRegionExtractionMetadata {
        extractor: EXTRACTOR_NAME.to_string(),
        extractor_version: REWRITE_CANDIDATE_EXTRACTOR_SCHEMA_VERSION,
        kernel_family: family,
        consumer: family.consumer().to_string(),
        manifest_schema: Some(AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA.to_string()),
        status_deopt_contract: None,
        required_proof_facts: ay_family
            .required_certificate_dependencies()
            .iter()
            .map(|dependency| (*dependency).to_string())
            .collect(),
        notes: vec![note.to_string()],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cegis::CegisResult;
    use crate::rewrite_admission::{
        CertificateIdentity, PROOF_OPTS_CERTIFICATE_PRODUCER, ProductGateEvidence,
        ProofGuidedAdmissionVerdict, SolverEvidence,
    };
    use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, Signature};

    const AY_LRA_BASIS_SUB_ZERO_TRANSFORM: &str = "ay_lra_basis_sub_zero";
    const AY_LRA_BASIS_SUB_ZERO_PROOF_HASH: u64 = 0xba5e;
    const AY_LRA_BASIS_SUB_ZERO_CERTIFICATE_HASH: &str = "0000000000000000ba5eba5ecafed00d";
    const AY_LRA_BASIS_SUB_ZERO_VALIDATION_HASH: &str = "0000000000000000000000000000ba5e";

    fn target() -> TargetAbiLayoutIdentity {
        TargetAbiLayoutIdentity::aarch64(
            "aarch64-apple-darwin",
            "aapcs64",
            "e-m:o-i64:64-i128:128-n32:64-S128",
            "apple-m2",
            vec!["+neon".to_string(), "+fp-armv8".to_string()],
        )
    }

    fn cost_context() -> CostContext {
        CostContext::aarch64("trust-cg-aarch64", "2026.04", 31, 19)
            .with_profile("named-kernel-hot")
            .with_note("extractor fixture")
    }

    fn transform() -> TransformIdentity {
        TransformIdentity::new("candidate.region.rewrite", "v1")
    }

    fn basis_sub_zero_transform() -> TransformIdentity {
        let mut transform = TransformIdentity::new(AY_LRA_BASIS_SUB_ZERO_TRANSFORM, "v1");
        transform.discovered_rule_name = Some(AY_LRA_BASIS_SUB_ZERO_TRANSFORM.to_string());
        transform.discovered_rule_proof_hash = Some(AY_LRA_BASIS_SUB_ZERO_PROOF_HASH);
        transform.certificate_hash = Some(AY_LRA_BASIS_SUB_ZERO_CERTIFICATE_HASH.to_string());
        transform.certificate_validation_hash =
            Some(AY_LRA_BASIS_SUB_ZERO_VALIDATION_HASH.to_string());
        transform
    }

    fn basis_sub_zero_certificate_identity() -> CertificateIdentity {
        CertificateIdentity {
            producer: PROOF_OPTS_CERTIFICATE_PRODUCER.to_string(),
            certificate_hash: Some(AY_LRA_BASIS_SUB_ZERO_CERTIFICATE_HASH.to_string()),
            certificate_chain_id: Some(format!(
                "{AY_LRA_BASIS_SUB_ZERO_TRANSFORM}@v1:{AY_LRA_BASIS_SUB_ZERO_VALIDATION_HASH}"
            )),
        }
    }

    fn basis_update_proof_guided_verdict(
        record: &RewriteAdmissionRecord,
    ) -> ProofGuidedAdmissionVerdict {
        ProofGuidedAdmissionVerdict::accepted_for_record(
            record,
            AYLraRewriteKernelFamily::BasisUpdate
                .required_certificate_dependencies()
                .iter()
                .map(|fact| (*fact).to_string())
                .collect(),
            "machir-target-region:ay_lra_basis_update",
            "sha256:ay-lra-basis-proof-consumption-manifest",
            "ay_lra_status_abi_v1",
            "replay/ay_lra_basis_update",
            "telemetry/ay_lra_basis_update",
            0,
            "trust_cg_disable_admitted_rewrite_ay_lra_basis_update",
        )
    }

    fn single_ret_function() -> MachFunction {
        let mut func = MachFunction::new(
            "basis_update_admission_report".to_string(),
            Signature::new(vec![], vec![]),
        );
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(func.entry, ret);
        func
    }

    fn caller_assumption() -> ProofAssumption {
        ProofAssumption {
            id: "fixture.explicit_assumption".to_string(),
            kind: ProofAssumptionKind::ProductGuard,
            formula: "profile_count >= 64".to_string(),
            source: "unit-test".to_string(),
        }
    }

    #[test]
    fn ay_lra_sparse_substitute_extraction_builds_record_inputs() {
        let input = CandidateRegionExtractionInput::new(
            AY_LRA_SPARSE_SUBSTITUTE_KERNEL_FAMILY,
            AYLraRewriteKernelFamily::SparseSubstitute.default_kernel_name(),
            b"ldr x8, [x0]; add x8, x8, x1; str x8, [x0]",
            target(),
            cost_context(),
            transform(),
        )
        .with_function_symbol("_trust_cg_ay_lra_sparse_substitute")
        .with_region_label("machir:bb0:4..7")
        .with_proof_assumption(caller_assumption());

        let extracted = extract_rewrite_admission_candidate(input)
            .expect("named ay LRA sparse substitute should extract");

        assert_eq!(extracted.schema, REWRITE_CANDIDATE_EXTRACTOR_SCHEMA);
        assert_eq!(
            extracted.metadata.kernel_family,
            CandidateKernelFamily::AYLraSparseSubstitute
        );
        assert_eq!(extracted.metadata.consumer, "ay");
        assert_eq!(
            extracted.inputs.source_region.kernel_family,
            AY_LRA_SPARSE_SUBSTITUTE_KERNEL_FAMILY
        );
        assert_eq!(
            extracted.inputs.source_region.kernel_name.as_deref(),
            Some("ay_lra_sparse_substitute")
        );
        assert_eq!(
            extracted.inputs.source_region.hash_algorithm,
            REWRITE_CANDIDATE_SOURCE_HASH_ALGORITHM
        );
        assert!(
            extracted
                .inputs
                .source_region
                .source_region_hash
                .starts_with("trust-cg-stable128:")
        );
        assert_eq!(extracted.inputs.cost_context.delta(), 12);
        assert!(
            extracted
                .inputs
                .proof_assumptions
                .iter()
                .any(|assumption| { assumption.id == "ay-lra-sparse-substitute-row-order" })
        );
        assert!(
            extracted
                .inputs
                .proof_assumptions
                .iter()
                .any(|assumption| { assumption.id == "fixture.explicit_assumption" })
        );

        let serialized_inputs =
            serde_json::to_string(&extracted.inputs).expect("inputs should serialize");
        assert!(serialized_inputs.contains("source_region_hash"));
        assert!(serialized_inputs.contains("proof_assumptions"));
        assert!(serialized_inputs.contains("target"));
        assert!(serialized_inputs.contains("cost_context"));

        let record = extracted.to_disabled_record();
        assert_eq!(record.admission_state, AdmissionState::Disabled);
        assert_eq!(
            record.allowlist.kernel_family,
            AY_LRA_SPARSE_SUBSTITUTE_KERNEL_FAMILY
        );
        assert!(record.ay_lra_manifest_binding.is_some());
        assert!(!record.can_admit_to_declarative_rewrite());
    }

    #[test]
    fn ay_lra_basis_update_extraction_builds_record_inputs() {
        let input = CandidateRegionExtractionInput::new(
            AY_LRA_BASIS_UPDATE_KERNEL_FAMILY,
            AYLraRewriteKernelFamily::BasisUpdate.default_kernel_name(),
            b"sub x9, x9, #0; str x9, [x2]; add x3, x3, #1",
            target(),
            CostContext::aarch64("trust-cg-aarch64", "2026.04", 44, 28)
                .with_profile("basis-row-batch-hot")
                .with_note("basis update extractor fixture"),
            TransformIdentity::new("candidate.basis_update.rewrite", "v1"),
        )
        .with_function_symbol("_trust_cg_ay_lra_basis_row_batch")
        .with_region_label("basis-row-batch:bb1:2..5");

        let extracted =
            extract_rewrite_admission_candidate(input).expect("named ay LRA basis should extract");

        assert_eq!(
            extracted.metadata.kernel_family,
            CandidateKernelFamily::AYLraBasisUpdate
        );
        assert_eq!(extracted.metadata.consumer, "ay");
        assert_eq!(
            extracted.metadata.manifest_schema.as_deref(),
            Some(AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA)
        );
        assert_eq!(
            extracted.inputs.source_region.kernel_family,
            AY_LRA_BASIS_UPDATE_KERNEL_FAMILY
        );
        assert_eq!(
            extracted.inputs.source_region.kernel_name.as_deref(),
            Some("ay_lra_basis_row_batch")
        );
        assert_eq!(
            extracted.inputs.source_region.function_symbol.as_deref(),
            Some("_trust_cg_ay_lra_basis_row_batch")
        );
        assert_eq!(
            extracted.inputs.source_region.region_label.as_deref(),
            Some("basis-row-batch:bb1:2..5")
        );
        assert_eq!(extracted.inputs.cost_context.delta(), 16);
        assert!(
            extracted
                .metadata
                .required_proof_facts
                .iter()
                .any(|fact| { fact == "ay-lra-basis-prefix-rollback" })
        );
        assert!(
            extracted
                .inputs
                .proof_assumptions
                .iter()
                .any(|assumption| { assumption.id == "ay-lra-basis-sorted-rows" })
        );
        assert!(
            extracted
                .inputs
                .proof_assumptions
                .iter()
                .any(|assumption| { assumption.id == "ay-lra-basis-prefix-rollback" })
        );

        let record = extracted.to_disabled_record();
        assert_eq!(record.admission_state, AdmissionState::Disabled);
        assert_eq!(
            record.allowlist.kernel_family,
            AY_LRA_BASIS_UPDATE_KERNEL_FAMILY
        );
        assert!(
            record
                .ay_lra_manifest_binding
                .as_ref()
                .is_some_and(|binding| {
                    binding.kernel_family == AY_LRA_BASIS_UPDATE_KERNEL_FAMILY
                        && binding
                            .required_certificate_dependencies
                            .iter()
                            .any(|fact| fact == "ay-lra-basis-prefix-rollback")
                })
        );
        assert!(!record.can_admit_to_declarative_rewrite());
    }

    #[test]
    fn ay_lra_basis_update_extracted_record_strictly_admits_into_pipeline_report() {
        let input = CandidateRegionExtractionInput::new(
            AY_LRA_BASIS_UPDATE_KERNEL_FAMILY,
            AYLraRewriteKernelFamily::BasisUpdate.default_kernel_name(),
            b"sub x9, x9, #0; str x9, [x2]; add x3, x3, #1",
            target(),
            CostContext::aarch64("trust-cg-aarch64", "2026.04", 44, 28)
                .with_profile("basis-row-batch-hot")
                .with_note("basis update extractor fixture"),
            basis_sub_zero_transform(),
        )
        .with_function_symbol("_trust_cg_ay_lra_basis_row_batch")
        .with_region_label("basis-row-batch:bb1:2..5");

        let extracted =
            extract_rewrite_admission_candidate(input).expect("named ay LRA basis should extract");
        assert_eq!(
            extracted.metadata.kernel_family,
            CandidateKernelFamily::AYLraBasisUpdate
        );
        assert_eq!(
            extracted.inputs.source_region.kernel_family,
            AY_LRA_BASIS_UPDATE_KERNEL_FAMILY
        );
        assert_eq!(
            extracted.inputs.source_region.kernel_name.as_deref(),
            Some(AYLraRewriteKernelFamily::BasisUpdate.default_kernel_name())
        );
        assert!(
            extracted
                .inputs
                .proof_assumptions
                .iter()
                .any(|assumption| assumption.id == "ay-lra-basis-prefix-rollback")
        );

        let record = extracted
            .to_disabled_record()
            .with_cegis_result(
                &CegisResult::Equivalent {
                    proof_hash: AY_LRA_BASIS_SUB_ZERO_PROOF_HASH,
                    iterations: 3,
                },
                None,
            )
            .with_certificate_identity(basis_sub_zero_certificate_identity());
        let verdict = basis_update_proof_guided_verdict(&record);
        let record = record
            .with_proof_guided_admission_verdict(verdict)
            .with_profile_review(
                KernelAllowlist::ay_lra_allowlisted(AYLraRewriteKernelFamily::BasisUpdate),
                ProductGateEvidence::all_passed_record(),
            );

        assert_eq!(record.admission_state, AdmissionState::Admitted);
        assert!(record.can_admit_to_declarative_rewrite());
        assert_eq!(record.transform.name, AY_LRA_BASIS_SUB_ZERO_TRANSFORM);
        assert_eq!(
            record.transform.discovered_rule_proof_hash,
            Some(AY_LRA_BASIS_SUB_ZERO_PROOF_HASH)
        );
        assert_eq!(
            record.transform.certificate_hash.as_deref(),
            Some(AY_LRA_BASIS_SUB_ZERO_CERTIFICATE_HASH)
        );
        assert_eq!(
            record.transform.certificate_validation_hash.as_deref(),
            Some(AY_LRA_BASIS_SUB_ZERO_VALIDATION_HASH)
        );

        let mut stale_certificate = record.clone();
        stale_certificate.transform.certificate_hash =
            Some("0000000000000000ba5eba5ecafed00e".to_string());
        assert!(!stale_certificate.can_admit_to_declarative_rewrite());

        let mut stale_proof = record.clone();
        stale_proof.evidence = SolverEvidence::AYEquivalenceProof {
            proof_hash: AY_LRA_BASIS_SUB_ZERO_PROOF_HASH + 1,
            cegis_iterations: Some(3),
        };
        assert!(!stale_proof.can_admit_to_declarative_rewrite());

        let json = record.to_json_pretty().expect("record should serialize");
        let mut func = single_ret_function();
        let result = trust_cg_opt::OptimizationPipeline::new(trust_cg_opt::OptLevel::O1)
            .with_admitted_rewrite_records([json])
            .with_rewrite_admission_config(
                trust_cg_opt::rewrite::RewriteAdmissionLoaderConfig::enabled_for_preview(),
            )
            .run_with_report(&mut func);

        assert!(
            result
                .pipeline_report
                .rewrite_admission_load_error
                .is_none()
        );
        let report = result
            .pipeline_report
            .rewrite_admission_load_report
            .expect("basis update admission should be visible in the pipeline report");
        assert!(report.loader_enabled);
        assert_eq!(report.input_records, 1);
        assert_eq!(report.parsed_records, 1);
        assert_eq!(report.eligible_records, 1);
        assert_eq!(report.registered_rules, 1);
        assert_eq!(report.loaded_records.len(), 1);
        assert_eq!(
            report.loaded_records[0].transform_name,
            AY_LRA_BASIS_SUB_ZERO_TRANSFORM
        );
        assert_eq!(
            report.loaded_records[0].kernel_family,
            AY_LRA_BASIS_UPDATE_KERNEL_FAMILY
        );
        assert_eq!(
            report.loaded_records[0].kernel_name.as_deref(),
            Some(AYLraRewriteKernelFamily::BasisUpdate.default_kernel_name())
        );
        assert_eq!(
            report.loaded_records[0].proof_hash,
            AY_LRA_BASIS_SUB_ZERO_PROOF_HASH
        );
        assert!(
            result
                .pass_stats
                .runs
                .iter()
                .any(|(name, count)| name == "declarative-rewrite" && *count == 1)
        );
    }

    #[test]
    fn ty_native_fused_parent_loop_extraction_preserves_metadata() {
        let input = CandidateRegionExtractionInput::new(
            TY_NATIVE_FUSED_PARENT_LOOP_KERNEL_FAMILY,
            TY_NATIVE_FUSED_PARENT_LOOP_DEFAULT_KERNEL_NAME,
            b"ty fused parent loop machir region",
            target(),
            CostContext::aarch64("trust-cg-aarch64", "2026.04", 87, 52)
                .with_profile("ty-native-fused-shadow"),
            TransformIdentity::new("ty.native_fused.parent_loop", "v1"),
        )
        .with_function_symbol("_trust_cg_ty_mcl_native_fused_parent_loop")
        .with_region_label("parent-loop:dispatch+commit");

        let extracted = extract_rewrite_admission_candidate(input)
            .expect("named TY native-fused parent loop should extract");

        assert_eq!(
            extracted.metadata.kernel_family,
            CandidateKernelFamily::TyNativeFusedParentLoop
        );
        assert_eq!(extracted.metadata.consumer, "ty");
        assert_eq!(
            extracted.metadata.manifest_schema.as_deref(),
            Some(TY_NATIVE_FUSED_PARENT_LOOP_MANIFEST_SCHEMA)
        );
        assert_eq!(
            extracted.metadata.status_deopt_contract.as_deref(),
            Some(TY_NATIVE_FUSED_PARENT_LOOP_STATUS_DEOPT_CONTRACT)
        );
        assert_eq!(extracted.metadata.required_proof_facts.len(), 5);
        assert!(extracted.metadata.required_proof_facts.iter().any(|fact| {
            fact == "ty.native_fused.fact.action_independence_or_fused_step_equivalence"
        }));
        assert!(
            extracted
                .metadata
                .notes
                .iter()
                .any(|note| { note == "consumer_mode=native-fused-parent-loop" })
        );
        assert_eq!(
            extracted.inputs.source_region.kernel_family,
            TY_NATIVE_FUSED_PARENT_LOOP_KERNEL_FAMILY
        );
        assert_eq!(
            extracted.inputs.source_region.kernel_name.as_deref(),
            Some(TY_NATIVE_FUSED_PARENT_LOOP_DEFAULT_KERNEL_NAME)
        );
        assert_eq!(
            extracted.inputs.source_region.region_label.as_deref(),
            Some("parent-loop:dispatch+commit")
        );
        assert!(extracted.inputs.proof_assumptions.iter().any(|assumption| {
            assumption.id == "ty.native_fused.status_deopt_contract"
                && assumption.formula.contains("status_deopt_abi.v1")
        }));

        let record = extracted.to_disabled_record();
        assert_eq!(record.admission_state, AdmissionState::Disabled);
        assert_eq!(
            record.allowlist.kernel_family,
            TY_NATIVE_FUSED_PARENT_LOOP_KERNEL_FAMILY
        );
        assert!(record.ay_lra_manifest_binding.is_none());
        assert!(!record.can_admit_to_declarative_rewrite());
    }

    #[test]
    fn ty_native_fused_parent_loop_rejects_wrong_kernel_name() {
        assert_eq!(
            CandidateKernelFamily::classify(
                TY_NATIVE_FUSED_PARENT_LOOP_KERNEL_FAMILY,
                Some("wrong_ty_native_fused_parent_loop")
            ),
            None
        );

        let wrong_name = CandidateRegionExtractionInput::new(
            TY_NATIVE_FUSED_PARENT_LOOP_KERNEL_FAMILY,
            "wrong_ty_native_fused_parent_loop",
            b"ty fused parent loop machir region",
            target(),
            cost_context(),
            transform(),
        );

        assert!(extract_rewrite_admission_candidate(wrong_name).is_none());
    }

    #[test]
    fn unnamed_or_unknown_kernel_families_do_not_extract() {
        let unnamed_ay = CandidateRegionExtractionInput::unnamed(
            AY_LRA_SPARSE_SUBSTITUTE_KERNEL_FAMILY,
            b"unnamed region",
            target(),
            cost_context(),
            transform(),
        );
        assert!(extract_rewrite_admission_candidate(unnamed_ay).is_none());

        let unknown = CandidateRegionExtractionInput::new(
            "generic_sparse_loop",
            "generic_sparse_loop",
            b"unknown region",
            target(),
            cost_context(),
            transform(),
        );
        assert!(extract_rewrite_admission_candidate(unknown).is_none());

        let mut non_aarch64_target = target();
        non_aarch64_target.arch = "x86_64".to_string();
        let non_aarch64 = CandidateRegionExtractionInput::new(
            TY_NATIVE_FUSED_PARENT_LOOP_KERNEL_FAMILY,
            TY_NATIVE_FUSED_PARENT_LOOP_DEFAULT_KERNEL_NAME,
            b"wrong target",
            non_aarch64_target,
            cost_context(),
            transform(),
        );
        assert!(extract_rewrite_admission_candidate(non_aarch64).is_none());
    }
}
