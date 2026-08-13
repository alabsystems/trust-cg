// trust-cg-opt - Admitted rewrite record loader stub
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Disabled-by-default loader for solver-discovered rewrite admission records.
//!
//! `trust-cg-verify` owns the canonical admission record schema. This module is
//! intentionally a narrow opt-side boundary: it can parse the stable JSON shape
//! and identify records that would be eligible for declarative rewrite
//! promotion, but it does not synthesize [`Rule`] instances from
//! JSON. Only reviewed static registry entries can become reachable.

use serde::Deserialize;
use thiserror::Error;

use crate::rewrite::engine::RewriteEngine;
use crate::rewrite::patterns::{rule_add_ri_zero, rule_sub_ri_zero};
use crate::rewrite::rule::Rule;

/// Stable schema tag produced by `trust-cg-verify`.
pub const REWRITE_ADMISSION_SCHEMA: &str = "trust-cg.rewrite_admission.v1";

/// Stable schema version produced by `trust-cg-verify`.
pub const REWRITE_ADMISSION_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for #796 ay LRA proof-consumption manifests.
const AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA: &str =
    "trust-cg.ay_lra.proof_consumption_manifest.v1";

/// Stable schema version for #796 ay LRA proof-consumption manifests.
const AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA_VERSION: u32 = 1;

/// Issue that introduced the #796 ay LRA proof-consumption manifest contract.
const AY_LRA_PROOF_CONSUMPTION_MANIFEST_ISSUE: u64 = 796;

/// Stable #796 ay LRA sparse-substitute kernel family id.
const AY_LRA_SPARSE_SUBSTITUTE_KERNEL_FAMILY: &str = "ay_lra_sparse_substitute";

/// Stable #796 ay LRA basis-update kernel family id.
const AY_LRA_BASIS_UPDATE_KERNEL_FAMILY: &str = "ay_lra_basis_update";

/// Stable #795 proof-optimization certificate producer id.
const PROOF_OPTS_CERTIFICATE_PRODUCER: &str = "trust-cg-opt.proof-opts";

/// Stable schema tag for the #800 proof-guided admission verdict.
const PROOF_GUIDED_ADMISSION_VERDICT_SCHEMA: &str = "trust-cg.proof_guided_admission.verdict.v1";

/// Stable schema version for the #800 proof-guided admission verdict.
const PROOF_GUIDED_ADMISSION_VERDICT_SCHEMA_VERSION: u32 = 1;

/// Issue that owns the complete proof-guided admission gate.
const PROOF_GUIDED_ADMISSION_VERDICT_ISSUE: u64 = 800;

/// Only AArch64 admission records can register opt-side AArch64 rewrites.
const AARCH64_TARGET_ARCH: &str = "aarch64";

/// Stable transform id for the reviewed sparse add-zero admitted rewrite.
const AY_LRA_SPARSE_ADD_ZERO_TRANSFORM: &str = "ay_lra_sparse_add_zero";

/// Stable transform version for the reviewed sparse add-zero admitted rewrite.
const AY_LRA_SPARSE_ADD_ZERO_VERSION: &str = "v1";

/// Stable transform id for the reviewed basis sub-zero admitted rewrite.
const AY_LRA_BASIS_SUB_ZERO_TRANSFORM: &str = "ay_lra_basis_sub_zero";

/// Stable transform version for the reviewed basis sub-zero admitted rewrite.
const AY_LRA_BASIS_SUB_ZERO_VERSION: &str = "v1";

/// Proof hash for the reviewed sparse add-zero admitted rewrite fixture.
const AY_LRA_SPARSE_ADD_ZERO_PROOF_HASH: u64 = 0xbeef;

/// Proof hash for the reviewed basis sub-zero admitted rewrite fixture.
const AY_LRA_BASIS_SUB_ZERO_PROOF_HASH: u64 = 0xba5e;

/// Proof-optimization certificate hash bound to the reviewed sparse add-zero rewrite.
const AY_LRA_SPARSE_ADD_ZERO_CERTIFICATE_HASH: &str = "0000000000000000feedfacecafebeef";

/// Proof-optimization validation hash bound to the reviewed sparse add-zero rewrite.
const AY_LRA_SPARSE_ADD_ZERO_VALIDATION_HASH: &str = "00000000000000000000000000005678";

/// Proof-optimization certificate hash bound to the reviewed basis sub-zero rewrite.
const AY_LRA_BASIS_SUB_ZERO_CERTIFICATE_HASH: &str = "0000000000000000ba5eba5ecafed00d";

/// Proof-optimization validation hash bound to the reviewed basis sub-zero rewrite.
const AY_LRA_BASIS_SUB_ZERO_VALIDATION_HASH: &str = "0000000000000000000000000000ba5e";

/// Named ay LRA sparse substitute kernel admitted by the reviewed mapping.
const AY_LRA_SPARSE_SUBSTITUTE_KERNEL_NAME: &str = "ay_lra_sparse_substitute";

/// Named ay LRA basis update kernel admitted by the reviewed mapping.
const AY_LRA_BASIS_UPDATE_KERNEL_NAME: &str = "ay_lra_basis_row_batch";

/// Exact allowlist entry admitted by the reviewed sparse add-zero mapping.
const AY_LRA_SPARSE_SUBSTITUTE_ALLOWLIST_ENTRY: &str =
    "rewrite-admission/ay-lra-sparse-substitute-v1";

/// Configuration for the admitted-record loader.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RewriteAdmissionLoaderConfig {
    /// Enables parsing of admitted records. Defaults to `false`.
    pub enabled: bool,
}

impl RewriteAdmissionLoaderConfig {
    /// Build the default fail-closed loader configuration.
    pub const fn disabled() -> Self {
        Self { enabled: false }
    }

    /// Build an enabled loader configuration for tests and offline preview.
    pub const fn enabled_for_preview() -> Self {
        Self { enabled: true }
    }
}

impl Default for RewriteAdmissionLoaderConfig {
    fn default() -> Self {
        Self::disabled()
    }
}

/// Report returned by the opt-side admitted-record loader.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RewriteAdmissionLoadReport {
    /// Whether the loader configuration was enabled.
    pub loader_enabled: bool,
    /// Number of input JSON records supplied.
    pub input_records: usize,
    /// Number of records parsed and schema-validated.
    pub parsed_records: usize,
    /// Number of parsed records that met admitted/gated/proved checks.
    pub eligible_records: usize,
    /// Number of reviewed static rewrite rules registered.
    pub registered_rules: usize,
    /// Metadata for eligible records found during enabled preview loading.
    pub loaded_records: Vec<LoadedAdmittedRewrite>,
}

/// Metadata extracted from an eligible admitted rewrite record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoadedAdmittedRewrite {
    /// Transform name bound by the admission record.
    pub transform_name: String,
    /// Transform version bound by the admission record.
    pub transform_version: String,
    /// Named kernel family allowlisted for the record.
    pub kernel_family: String,
    /// Optional concrete kernel name allowlisted for the record.
    pub kernel_name: Option<String>,
    /// Optional allowlist entry id.
    pub allowlist_entry: Option<String>,
    /// Target architecture from the admission record.
    pub target_arch: String,
    /// Positive AArch64 cost-model delta from the admission record.
    pub aarch64_cost_delta: i64,
    /// Optional discovered-rule name from solver discovery lineage.
    pub discovered_rule_name: Option<String>,
    /// Optional discovered-rule proof hash from solver discovery lineage.
    pub discovered_rule_proof_hash: Option<u64>,
    /// ay equivalence proof hash from the record.
    pub proof_hash: u64,
}

/// Errors returned while parsing admitted rewrite records.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum RewriteAdmissionLoadError {
    /// JSON parsing failed.
    #[error("failed to parse rewrite admission record JSON: {0}")]
    Json(String),
    /// The record uses an unsupported schema tag or version.
    #[error("unsupported rewrite admission schema {schema} version {schema_version}")]
    UnsupportedSchema {
        /// Record schema tag.
        schema: String,
        /// Record schema version.
        schema_version: u32,
    },
}

/// Parse admitted rewrite records and return preview metadata.
///
/// The default disabled configuration consumes only the input iterator count
/// and does not parse or register anything. When enabled, this function parses
/// records, filters to records that are admitted, allowlisted, product-gated,
/// target-compatible, backed by ay proof evidence, and bound to #795/#796
/// identities, without registering rules.
pub fn load_admitted_rewrites_from_json<'a>(
    records: impl IntoIterator<Item = &'a str>,
    config: RewriteAdmissionLoaderConfig,
) -> Result<RewriteAdmissionLoadReport, RewriteAdmissionLoadError> {
    let mut report = RewriteAdmissionLoadReport {
        loader_enabled: config.enabled,
        ..RewriteAdmissionLoadReport::default()
    };

    if !config.enabled {
        report.input_records = records.into_iter().count();
        return Ok(report);
    }

    for json in records {
        report.input_records += 1;
        let record: RawRewriteAdmissionRecord = serde_json::from_str(json)
            .map_err(|e| RewriteAdmissionLoadError::Json(e.to_string()))?;
        record.validate_schema()?;
        report.parsed_records += 1;

        if let Some(loaded) = record.as_loaded_admitted_rewrite() {
            report.loaded_records.push(loaded);
        }
    }

    report.eligible_records = report.loaded_records.len();
    Ok(report)
}

/// Parse admitted rewrite records and register reviewed static rewrites.
///
/// This is disabled by default through [`RewriteAdmissionLoaderConfig`]. When
/// enabled, JSON records can only select entries already present in the tiny
/// opt-side registry; unsupported transforms, TY records, and malformed
/// admission identities simply register zero rules instead of manufacturing
/// rules from data.
pub fn register_admitted_rewrites_from_json<'a>(
    records: impl IntoIterator<Item = &'a str>,
    config: RewriteAdmissionLoaderConfig,
    engine: &mut RewriteEngine,
) -> Result<RewriteAdmissionLoadReport, RewriteAdmissionLoadError> {
    let mut report = load_admitted_rewrites_from_json(records, config)?;
    if !config.enabled {
        return Ok(report);
    }

    let mut registered_entries = Vec::new();
    for loaded in &report.loaded_records {
        let Some((entry_idx, entry)) = registry_entry_for(loaded) else {
            continue;
        };
        if registered_entries.contains(&entry_idx) {
            continue;
        }
        engine.register((entry.rule)());
        registered_entries.push(entry_idx);
        report.registered_rules += 1;
    }

    Ok(report)
}

#[derive(Debug, Deserialize)]
struct RawRewriteAdmissionRecord {
    schema: String,
    schema_version: u32,
    source_region: RawSourceRegionIdentity,
    target: RawTargetIdentity,
    transform: RawTransformIdentity,
    evidence: RawSolverEvidence,
    aarch64_cost_delta: i64,
    admission_state: RawAdmissionState,
    allowlist: RawKernelAllowlist,
    product_gates: RawProductGateEvidence,
    #[serde(default)]
    proof_guided_admission: RawProofGuidedAdmissionVerdict,
    certificate_identity: Option<RawCertificateIdentity>,
    ay_lra_manifest_binding: Option<RawAYLraManifestBinding>,
}

impl RawRewriteAdmissionRecord {
    fn validate_schema(&self) -> Result<(), RewriteAdmissionLoadError> {
        if self.schema == REWRITE_ADMISSION_SCHEMA
            && self.schema_version == REWRITE_ADMISSION_SCHEMA_VERSION
        {
            Ok(())
        } else {
            Err(RewriteAdmissionLoadError::UnsupportedSchema {
                schema: self.schema.clone(),
                schema_version: self.schema_version,
            })
        }
    }

    fn as_loaded_admitted_rewrite(&self) -> Option<LoadedAdmittedRewrite> {
        let proof_hash = self.evidence.proof_hash()?;
        let discovered_rule_proof_hash = self.transform.discovered_rule_proof_hash?;
        if discovered_rule_proof_hash != proof_hash {
            return None;
        }

        if self.admission_state != RawAdmissionState::Admitted
            || !self.allowlist.allowlisted
            || !self.product_gates.all_passed()
            || !self.proof_guided_admission.accepts_record(self, proof_hash)
            || !self.allowlist.matches_source_region(&self.source_region)
            || self.target.arch != AARCH64_TARGET_ARCH
            || self.aarch64_cost_delta <= 0
            || !self.certificate_identity.as_ref().is_some_and(|identity| {
                identity.matches_transform_identity(&self.transform, proof_hash)
            })
            || !self
                .ay_lra_manifest_binding
                .as_ref()
                .is_some_and(|binding| {
                    binding.matches_source_and_allowlist(&self.source_region, &self.allowlist)
                })
        {
            return None;
        }
        Some(LoadedAdmittedRewrite {
            transform_name: self.transform.name.clone(),
            transform_version: self.transform.version.clone(),
            kernel_family: self.allowlist.kernel_family.clone(),
            kernel_name: self.allowlist.kernel_name.clone(),
            allowlist_entry: self.allowlist.allowlist_entry.clone(),
            target_arch: self.target.arch.clone(),
            aarch64_cost_delta: self.aarch64_cost_delta,
            discovered_rule_name: self.transform.discovered_rule_name.clone(),
            discovered_rule_proof_hash: Some(discovered_rule_proof_hash),
            proof_hash,
        })
    }
}

#[derive(Debug, Deserialize)]
struct RawSourceRegionIdentity {
    #[allow(dead_code)]
    source_region_hash: String,
    #[allow(dead_code)]
    hash_algorithm: String,
    kernel_family: String,
    kernel_name: Option<String>,
    #[allow(dead_code)]
    function_symbol: Option<String>,
    #[allow(dead_code)]
    region_label: Option<String>,
}

#[derive(Debug, Deserialize)]
struct RawTargetIdentity {
    arch: String,
}

#[derive(Debug, Deserialize)]
struct RawTransformIdentity {
    name: String,
    version: String,
    #[allow(dead_code)]
    rule_proposal_hash: Option<u64>,
    discovered_rule_name: Option<String>,
    discovered_rule_proof_hash: Option<u64>,
    certificate_hash: Option<String>,
    certificate_validation_hash: Option<String>,
}

impl RawTransformIdentity {
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
                CertificateBindingExpectation::Bound {
                    certificate_hash,
                    validation_hash,
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
    (transform_name == AY_LRA_SPARSE_ADD_ZERO_TRANSFORM
        && transform_version == AY_LRA_SPARSE_ADD_ZERO_VERSION)
        || (transform_name == AY_LRA_BASIS_SUB_ZERO_TRANSFORM
            && transform_version == AY_LRA_BASIS_SUB_ZERO_VERSION)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
enum RawAdmissionState {
    Disabled,
    PendingProof,
    ProvedProfileOnly,
    Admitted,
    Rejected,
}

#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum RawSolverEvidence {
    Pending,
    // `rename_all = "snake_case"` would split the `AY` acronym into
    // `a_y_equivalence_proof`; the canonical wire name produced by ay and by
    // `trust-cg-verify`'s `SolverEvidence` is `ay_equivalence_proof`.
    #[serde(rename = "ay_equivalence_proof")]
    AYEquivalenceProof {
        proof_hash: u64,
        #[allow(dead_code)]
        cegis_iterations: Option<u32>,
    },
    Counterexample {
        #[allow(dead_code)]
        counterexample: serde_json::Value,
        #[allow(dead_code)]
        reducer: Option<serde_json::Value>,
    },
    Inconclusive {
        #[allow(dead_code)]
        reason: String,
        #[allow(dead_code)]
        reducer: Option<serde_json::Value>,
    },
}

impl RawSolverEvidence {
    fn proof_hash(&self) -> Option<u64> {
        match self {
            RawSolverEvidence::AYEquivalenceProof { proof_hash, .. } => Some(*proof_hash),
            RawSolverEvidence::Pending
            | RawSolverEvidence::Counterexample { .. }
            | RawSolverEvidence::Inconclusive { .. } => None,
        }
    }
}

#[derive(Debug, Deserialize)]
struct RawKernelAllowlist {
    kernel_family: String,
    kernel_name: Option<String>,
    allowlist_entry: Option<String>,
    allowlisted: bool,
}

impl RawKernelAllowlist {
    fn matches_source_region(&self, source_region: &RawSourceRegionIdentity) -> bool {
        self.kernel_family == source_region.kernel_family
            && match (&self.kernel_name, &source_region.kernel_name) {
                (Some(allowlisted), Some(source)) => allowlisted == source,
                (Some(_), None) => false,
                (None, _) => true,
            }
    }
}

#[derive(Debug, Deserialize)]
struct RawProductGateEvidence {
    replay_passed: bool,
    telemetry_guarded: bool,
    rollback_or_deopt_available: bool,
    product_promotion_approved: bool,
}

impl RawProductGateEvidence {
    fn all_passed(&self) -> bool {
        self.replay_passed
            && self.telemetry_guarded
            && self.rollback_or_deopt_available
            && self.product_promotion_approved
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
#[derive(Default)]
enum RawProofGuidedAdmissionDisposition {
    Accepted,
    #[default]
    Rejected,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
enum RawProofGuidedAdmissionRejection {
    MissingCompleteAdmissionVerdict,
    UnsupportedVerdictSchema,
    VerdictRejected,
    MissingProofFact,
    MissingCertificateIdentity,
    TransformIdentityMismatch,
    SourceRegionHashMismatch,
    MissingTargetRegionHash,
    FailedValidationHash,
    MissingManifestHash,
    MissingRuntimeStatusContract,
    MissingReplayRoot,
    MissingTelemetryEvent,
    MissingTelemetryUsefulNativeCounter,
    MissingRollbackKnob,
}

#[derive(Debug, Deserialize)]
struct RawProofGuidedAdmissionVerdict {
    schema: String,
    schema_version: u32,
    issue: u64,
    disposition: RawProofGuidedAdmissionDisposition,
    rejection_reasons: Vec<RawProofGuidedAdmissionRejection>,
    consumed_proof_facts: Vec<String>,
    transform_name: String,
    transform_version: String,
    source_trust_ir_region_hash: String,
    target_aarch64_region_hash: String,
    validation_result_hash: String,
    manifest_hash: String,
    runtime_status_contract: String,
    replay_artifact_root: String,
    telemetry_event_id: String,
    #[serde(default)]
    telemetry_useful_native_applications: Option<u64>,
    rollback_or_disable_knob: String,
}

impl Default for RawProofGuidedAdmissionVerdict {
    fn default() -> Self {
        Self {
            schema: PROOF_GUIDED_ADMISSION_VERDICT_SCHEMA.to_string(),
            schema_version: PROOF_GUIDED_ADMISSION_VERDICT_SCHEMA_VERSION,
            issue: PROOF_GUIDED_ADMISSION_VERDICT_ISSUE,
            disposition: RawProofGuidedAdmissionDisposition::Rejected,
            rejection_reasons: vec![
                RawProofGuidedAdmissionRejection::MissingCompleteAdmissionVerdict,
            ],
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
}

impl RawProofGuidedAdmissionVerdict {
    fn accepts_record(&self, record: &RawRewriteAdmissionRecord, proof_hash: u64) -> bool {
        self.schema == PROOF_GUIDED_ADMISSION_VERDICT_SCHEMA
            && self.schema_version == PROOF_GUIDED_ADMISSION_VERDICT_SCHEMA_VERSION
            && self.issue == PROOF_GUIDED_ADMISSION_VERDICT_ISSUE
            && self.disposition == RawProofGuidedAdmissionDisposition::Accepted
            && self.rejection_reasons.is_empty()
            && self.transform_name == record.transform.name
            && self.transform_version == record.transform.version
            && self.source_trust_ir_region_hash == record.source_region.source_region_hash
            && !missing_required_text(&self.target_aarch64_region_hash)
            && self.validation_result_hash
                == expected_validation_result_hash(&record.transform, proof_hash)
            && !missing_required_text(&self.manifest_hash)
            && !missing_required_text(&self.runtime_status_contract)
            && !missing_required_text(&self.replay_artifact_root)
            && !missing_required_text(&self.telemetry_event_id)
            && self.telemetry_useful_native_applications.is_some()
            && !missing_required_text(&self.rollback_or_disable_knob)
            && self.has_required_proof_facts(record)
    }

    fn has_required_proof_facts(&self, record: &RawRewriteAdmissionRecord) -> bool {
        if self.consumed_proof_facts.is_empty()
            || self
                .consumed_proof_facts
                .iter()
                .any(|fact| missing_required_text(fact))
        {
            return false;
        }
        let Some(binding) = record.ay_lra_manifest_binding.as_ref() else {
            return false;
        };
        binding
            .required_certificate_dependencies
            .iter()
            .all(|required| {
                self.consumed_proof_facts
                    .iter()
                    .any(|fact| fact == required)
            })
    }
}

#[derive(Debug, Deserialize)]
struct RawCertificateIdentity {
    producer: String,
    certificate_hash: Option<String>,
    certificate_chain_id: Option<String>,
}

impl RawCertificateIdentity {
    fn is_proof_opts_certificate_identity(&self) -> bool {
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

    fn matches_transform_identity(
        &self,
        transform: &RawTransformIdentity,
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

#[derive(Debug, Deserialize)]
struct RawAYLraManifestBinding {
    schema: String,
    schema_version: u32,
    issue: u64,
    kernel_family: String,
    proof_family: String,
    allowlist_family: String,
    required_certificate_dependencies: Vec<String>,
}

impl RawAYLraManifestBinding {
    fn matches_source_and_allowlist(
        &self,
        source_region: &RawSourceRegionIdentity,
        allowlist: &RawKernelAllowlist,
    ) -> bool {
        let Some(expected_dependencies) =
            ay_lra_required_certificate_dependencies(self.kernel_family.as_str())
        else {
            return false;
        };
        self.schema == AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA
            && self.schema_version == AY_LRA_PROOF_CONSUMPTION_MANIFEST_SCHEMA_VERSION
            && self.issue == AY_LRA_PROOF_CONSUMPTION_MANIFEST_ISSUE
            && self.proof_family == self.kernel_family
            && self.allowlist_family == self.kernel_family
            && self.required_certificate_dependencies.len() == expected_dependencies.len()
            && self
                .required_certificate_dependencies
                .iter()
                .map(String::as_str)
                .eq(expected_dependencies.iter().copied())
            && source_region.kernel_family == self.kernel_family
            && allowlist.kernel_family == self.kernel_family
            && allowlist.allowlist_entry.as_deref()
                == ay_lra_allowlist_entry(self.kernel_family.as_str())
            && allowlist.matches_source_region(source_region)
    }
}

fn ay_lra_required_certificate_dependencies(
    kernel_family: &str,
) -> Option<&'static [&'static str]> {
    match kernel_family {
        AY_LRA_SPARSE_SUBSTITUTE_KERNEL_FAMILY => Some(&[
            "ay-lra-sparse-substitute-row-order",
            "ay-lra-sparse-output-bounds",
            "ay-lra-sparse-overflow",
            "ay-lra-sparse-alias-policy",
            "ay-lra-basis-epoch",
        ]),
        AY_LRA_BASIS_UPDATE_KERNEL_FAMILY => Some(&[
            "ay-lra-basis-sorted-rows",
            "ay-lra-basis-output-bounds",
            "ay-lra-basis-overflow",
            "ay-lra-basis-alias-policy",
            "ay-lra-basis-epoch",
            "ay-lra-basis-prefix-rollback",
        ]),
        _ => None,
    }
}

fn ay_lra_allowlist_entry(kernel_family: &str) -> Option<&'static str> {
    match kernel_family {
        AY_LRA_SPARSE_SUBSTITUTE_KERNEL_FAMILY => Some(AY_LRA_SPARSE_SUBSTITUTE_ALLOWLIST_ENTRY),
        AY_LRA_BASIS_UPDATE_KERNEL_FAMILY => Some("rewrite-admission/ay-lra-basis-update-v1"),
        _ => None,
    }
}

fn missing_required_text(value: &str) -> bool {
    value.trim().is_empty()
}

fn is_u128_hex_identity(value: &str) -> bool {
    value.len() == 32 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
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
    if transform_name == AY_LRA_SPARSE_ADD_ZERO_TRANSFORM
        && transform_version == AY_LRA_SPARSE_ADD_ZERO_VERSION
        && proof_hash == AY_LRA_SPARSE_ADD_ZERO_PROOF_HASH
    {
        Some(ReviewedCertificateBinding {
            certificate_hash: AY_LRA_SPARSE_ADD_ZERO_CERTIFICATE_HASH,
            validation_hash: AY_LRA_SPARSE_ADD_ZERO_VALIDATION_HASH,
        })
    } else if transform_name == AY_LRA_BASIS_SUB_ZERO_TRANSFORM
        && transform_version == AY_LRA_BASIS_SUB_ZERO_VERSION
        && proof_hash == AY_LRA_BASIS_SUB_ZERO_PROOF_HASH
    {
        Some(ReviewedCertificateBinding {
            certificate_hash: AY_LRA_BASIS_SUB_ZERO_CERTIFICATE_HASH,
            validation_hash: AY_LRA_BASIS_SUB_ZERO_VALIDATION_HASH,
        })
    } else {
        None
    }
}

fn expected_validation_result_hash(transform: &RawTransformIdentity, proof_hash: u64) -> String {
    transform
        .certificate_validation_hash
        .clone()
        .unwrap_or_else(|| format!("ay-proof:{proof_hash:016x}"))
}

type RuleFactory = fn() -> Rule;

struct AdmittedRewriteRegistryEntry {
    transform_name: &'static str,
    transform_version: &'static str,
    discovered_rule_name: &'static str,
    kernel_family: &'static str,
    kernel_name: &'static str,
    allowlist_entry: &'static str,
    rule: RuleFactory,
}

impl AdmittedRewriteRegistryEntry {
    fn matches(&self, loaded: &LoadedAdmittedRewrite) -> bool {
        loaded.transform_name == self.transform_name
            && loaded.transform_version == self.transform_version
            && loaded.target_arch == AARCH64_TARGET_ARCH
            && loaded.kernel_family == self.kernel_family
            && loaded.kernel_name.as_deref() == Some(self.kernel_name)
            && loaded.allowlist_entry.as_deref() == Some(self.allowlist_entry)
            && match loaded.discovered_rule_name.as_deref() {
                Some(discovered_rule_name) => discovered_rule_name == self.discovered_rule_name,
                None => true,
            }
    }
}

const ADMITTED_REWRITE_REGISTRY: &[AdmittedRewriteRegistryEntry] = &[
    AdmittedRewriteRegistryEntry {
        transform_name: AY_LRA_SPARSE_ADD_ZERO_TRANSFORM,
        transform_version: AY_LRA_SPARSE_ADD_ZERO_VERSION,
        discovered_rule_name: AY_LRA_SPARSE_ADD_ZERO_TRANSFORM,
        kernel_family: AY_LRA_SPARSE_SUBSTITUTE_KERNEL_FAMILY,
        kernel_name: AY_LRA_SPARSE_SUBSTITUTE_KERNEL_NAME,
        allowlist_entry: AY_LRA_SPARSE_SUBSTITUTE_ALLOWLIST_ENTRY,
        rule: rule_add_ri_zero,
    },
    AdmittedRewriteRegistryEntry {
        transform_name: AY_LRA_BASIS_SUB_ZERO_TRANSFORM,
        transform_version: AY_LRA_BASIS_SUB_ZERO_VERSION,
        discovered_rule_name: AY_LRA_BASIS_SUB_ZERO_TRANSFORM,
        kernel_family: AY_LRA_BASIS_UPDATE_KERNEL_FAMILY,
        kernel_name: AY_LRA_BASIS_UPDATE_KERNEL_NAME,
        allowlist_entry: "rewrite-admission/ay-lra-basis-update-v1",
        rule: rule_sub_ri_zero,
    },
];

fn registry_entry_for(
    loaded: &LoadedAdmittedRewrite,
) -> Option<(usize, &'static AdmittedRewriteRegistryEntry)> {
    ADMITTED_REWRITE_REGISTRY
        .iter()
        .enumerate()
        .find(|(_, entry)| entry.matches(loaded))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn admitted_json() -> String {
        serde_json::json!({
            "schema": REWRITE_ADMISSION_SCHEMA,
            "schema_version": REWRITE_ADMISSION_SCHEMA_VERSION,
            "source_region": {
                "source_region_hash": "sha256:region",
                "hash_algorithm": "sha256",
                "kernel_family": "ay_lra_sparse_substitute",
                "kernel_name": "ay_lra_sparse_substitute",
                "function_symbol": "_trust_cg_ay_lra_sparse_substitute",
                "region_label": "bb0:0..2"
            },
            "proof_assumptions": [],
            "target": {
                "arch": "aarch64",
                "target_triple": "aarch64-apple-darwin",
                "abi": "aapcs64",
                "data_layout": "e-m:o-i64:64-i128:128-n32:64-S128",
                "cpu": "apple-m2",
                "features": ["+neon"]
            },
            "cost_context": {
                "cost_model": "trust-cg-aarch64",
                "cost_model_version": "2026.04",
                "profile": "named-kernel-hot",
                "source_cost": 12,
                "replacement_cost": 8,
                "notes": []
            },
            "transform": {
                "name": "ay_lra_sparse_add_zero",
                "version": "v1",
                "rule_proposal_hash": 17,
                "discovered_rule_name": "ay_lra_sparse_add_zero",
                "discovered_rule_proof_hash": 48879,
                "certificate_hash": "0000000000000000feedfacecafebeef",
                "certificate_validation_hash": "00000000000000000000000000005678"
            },
            "evidence": {
                "kind": "ay_equivalence_proof",
                "proof_hash": 48879,
                "cegis_iterations": 2
            },
            "aarch64_cost_delta": 4,
            "admission_state": "admitted",
            "allowlist": {
                "kernel_family": "ay_lra_sparse_substitute",
                "kernel_name": "ay_lra_sparse_substitute",
                "allowlist_entry": "rewrite-admission/ay-lra-sparse-substitute-v1",
                "allowlisted": true
            },
            "product_gates": {
                "replay_passed": true,
                "telemetry_guarded": true,
                "rollback_or_deopt_available": true,
                "product_promotion_approved": true
            },
            "proof_guided_admission": {
                "schema": "trust-cg.proof_guided_admission.verdict.v1",
                "schema_version": 1,
                "issue": 800,
                "disposition": "accepted",
                "rejection_reasons": [],
                "consumed_proof_facts": [
                    "ay-lra-sparse-substitute-row-order",
                    "ay-lra-sparse-output-bounds",
                    "ay-lra-sparse-overflow",
                    "ay-lra-sparse-alias-policy",
                    "ay-lra-basis-epoch"
                ],
                "transform_name": "ay_lra_sparse_add_zero",
                "transform_version": "v1",
                "source_trust_ir_region_hash": "sha256:region",
                "target_aarch64_region_hash": "machir:ay-lra-sparse-add-zero",
                "validation_result_hash": "00000000000000000000000000005678",
                "manifest_hash": "sha256:ay-lra-sparse-substitute-manifest",
                "runtime_status_contract": "ay_lra_status_abi_v1",
                "replay_artifact_root": "replay/ay_lra_sparse_substitute",
                "telemetry_event_id": "telemetry/ay_lra_sparse_substitute/admitted",
                "telemetry_useful_native_applications": 0,
                "rollback_or_disable_knob": "trust_cg_disable_admitted_rewrite_ay_lra_sparse_substitute"
            },
            "certificate_identity": {
                "producer": "trust-cg-opt.proof-opts",
                "certificate_hash": "0000000000000000feedfacecafebeef",
                "certificate_chain_id": "ay_lra_sparse_add_zero@v1:00000000000000000000000000005678"
            },
            "ay_lra_manifest_binding": {
                "schema": "trust-cg.ay_lra.proof_consumption_manifest.v1",
                "schema_version": 1,
                "issue": 796,
                "kernel_family": "ay_lra_sparse_substitute",
                "proof_family": "ay_lra_sparse_substitute",
                "allowlist_family": "ay_lra_sparse_substitute",
                "required_certificate_dependencies": [
                    "ay-lra-sparse-substitute-row-order",
                    "ay-lra-sparse-output-bounds",
                    "ay-lra-sparse-overflow",
                    "ay-lra-sparse-alias-policy",
                    "ay-lra-basis-epoch"
                ]
            }
        })
        .to_string()
    }

    fn basis_update_json() -> String {
        let mut value: serde_json::Value =
            serde_json::from_str(&admitted_json()).expect("test JSON");
        value["source_region"]["source_region_hash"] =
            serde_json::Value::String("sha256:basis-region".to_string());
        value["source_region"]["kernel_family"] =
            serde_json::Value::String(AY_LRA_BASIS_UPDATE_KERNEL_FAMILY.to_string());
        value["source_region"]["kernel_name"] =
            serde_json::Value::String(AY_LRA_BASIS_UPDATE_KERNEL_NAME.to_string());
        value["source_region"]["function_symbol"] =
            serde_json::Value::String("_trust_cg_ay_lra_basis_row_batch".to_string());
        value["source_region"]["region_label"] =
            serde_json::Value::String("basis-row-batch:bb0:2..5".to_string());
        value["cost_context"]["source_cost"] = serde_json::Value::from(14);
        value["cost_context"]["replacement_cost"] = serde_json::Value::from(9);
        value["transform"]["name"] =
            serde_json::Value::String(AY_LRA_BASIS_SUB_ZERO_TRANSFORM.to_string());
        value["transform"]["discovered_rule_name"] =
            serde_json::Value::String(AY_LRA_BASIS_SUB_ZERO_TRANSFORM.to_string());
        value["transform"]["discovered_rule_proof_hash"] =
            serde_json::Value::from(AY_LRA_BASIS_SUB_ZERO_PROOF_HASH);
        value["transform"]["certificate_hash"] =
            serde_json::Value::String(AY_LRA_BASIS_SUB_ZERO_CERTIFICATE_HASH.to_string());
        value["transform"]["certificate_validation_hash"] =
            serde_json::Value::String(AY_LRA_BASIS_SUB_ZERO_VALIDATION_HASH.to_string());
        value["evidence"]["proof_hash"] = serde_json::Value::from(AY_LRA_BASIS_SUB_ZERO_PROOF_HASH);
        value["aarch64_cost_delta"] = serde_json::Value::from(5);
        value["proof_guided_admission"]["consumed_proof_facts"] = serde_json::json!([
            "ay-lra-basis-sorted-rows",
            "ay-lra-basis-output-bounds",
            "ay-lra-basis-overflow",
            "ay-lra-basis-alias-policy",
            "ay-lra-basis-epoch",
            "ay-lra-basis-prefix-rollback"
        ]);
        value["proof_guided_admission"]["transform_name"] =
            serde_json::Value::String(AY_LRA_BASIS_SUB_ZERO_TRANSFORM.to_string());
        value["proof_guided_admission"]["source_trust_ir_region_hash"] =
            serde_json::Value::String("sha256:basis-region".to_string());
        value["proof_guided_admission"]["target_aarch64_region_hash"] =
            serde_json::Value::String("machir:ay-lra-basis-sub-zero".to_string());
        value["proof_guided_admission"]["validation_result_hash"] =
            serde_json::Value::String(AY_LRA_BASIS_SUB_ZERO_VALIDATION_HASH.to_string());
        value["proof_guided_admission"]["manifest_hash"] =
            serde_json::Value::String("sha256:ay-lra-basis-update-manifest".to_string());
        value["proof_guided_admission"]["runtime_status_contract"] =
            serde_json::Value::String("ay_lra_status_abi_v1".to_string());
        value["proof_guided_admission"]["replay_artifact_root"] =
            serde_json::Value::String("replay/ay_lra_basis_update".to_string());
        value["proof_guided_admission"]["telemetry_event_id"] =
            serde_json::Value::String("telemetry/ay_lra_basis_update/admitted".to_string());
        value["proof_guided_admission"]["rollback_or_disable_knob"] = serde_json::Value::String(
            "trust_cg_disable_admitted_rewrite_ay_lra_basis_update".to_string(),
        );
        value["allowlist"]["kernel_family"] =
            serde_json::Value::String(AY_LRA_BASIS_UPDATE_KERNEL_FAMILY.to_string());
        value["allowlist"]["kernel_name"] =
            serde_json::Value::String(AY_LRA_BASIS_UPDATE_KERNEL_NAME.to_string());
        value["allowlist"]["allowlist_entry"] =
            serde_json::Value::String("rewrite-admission/ay-lra-basis-update-v1".to_string());
        value["certificate_identity"]["certificate_hash"] =
            serde_json::Value::String(AY_LRA_BASIS_SUB_ZERO_CERTIFICATE_HASH.to_string());
        value["certificate_identity"]["certificate_chain_id"] = serde_json::Value::String(format!(
            "{}@v1:{}",
            AY_LRA_BASIS_SUB_ZERO_TRANSFORM, AY_LRA_BASIS_SUB_ZERO_VALIDATION_HASH
        ));
        value["ay_lra_manifest_binding"]["kernel_family"] =
            serde_json::Value::String(AY_LRA_BASIS_UPDATE_KERNEL_FAMILY.to_string());
        value["ay_lra_manifest_binding"]["proof_family"] =
            serde_json::Value::String(AY_LRA_BASIS_UPDATE_KERNEL_FAMILY.to_string());
        value["ay_lra_manifest_binding"]["allowlist_family"] =
            serde_json::Value::String(AY_LRA_BASIS_UPDATE_KERNEL_FAMILY.to_string());
        value["ay_lra_manifest_binding"]["required_certificate_dependencies"] =
            serde_json::json!([
                "ay-lra-basis-sorted-rows",
                "ay-lra-basis-output-bounds",
                "ay-lra-basis-overflow",
                "ay-lra-basis-alias-policy",
                "ay-lra-basis-epoch",
                "ay-lra-basis-prefix-rollback"
            ]);
        value.to_string()
    }

    #[test]
    fn admitted_rewrite_loader_is_disabled_by_default() {
        let json = admitted_json();
        let report = load_admitted_rewrites_from_json(
            [json.as_str()],
            RewriteAdmissionLoaderConfig::default(),
        )
        .expect("disabled loader should not parse");

        assert!(!report.loader_enabled);
        assert_eq!(report.input_records, 1);
        assert_eq!(report.parsed_records, 0);
        assert_eq!(report.eligible_records, 0);
        assert_eq!(report.registered_rules, 0);
        assert!(report.loaded_records.is_empty());
    }

    #[test]
    fn enabled_preview_loads_eligible_admitted_record_without_registering_rules() {
        let json = admitted_json();
        let report = load_admitted_rewrites_from_json(
            [json.as_str()],
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
        )
        .expect("admitted record should parse");

        assert!(report.loader_enabled);
        assert_eq!(report.input_records, 1);
        assert_eq!(report.parsed_records, 1);
        assert_eq!(report.eligible_records, 1);
        assert_eq!(report.registered_rules, 0);
        assert_eq!(
            report.loaded_records,
            vec![LoadedAdmittedRewrite {
                transform_name: "ay_lra_sparse_add_zero".to_string(),
                transform_version: "v1".to_string(),
                kernel_family: "ay_lra_sparse_substitute".to_string(),
                kernel_name: Some("ay_lra_sparse_substitute".to_string()),
                allowlist_entry: Some("rewrite-admission/ay-lra-sparse-substitute-v1".to_string()),
                target_arch: "aarch64".to_string(),
                aarch64_cost_delta: 4,
                discovered_rule_name: Some("ay_lra_sparse_add_zero".to_string()),
                discovered_rule_proof_hash: Some(48879),
                proof_hash: 48879,
            }]
        );
    }

    #[test]
    fn enabled_preview_loads_eligible_basis_update_record_without_registering_rules() {
        let json = basis_update_json();
        let report = load_admitted_rewrites_from_json(
            [json.as_str()],
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
        )
        .expect("basis update admitted record should parse");

        assert!(report.loader_enabled);
        assert_eq!(report.input_records, 1);
        assert_eq!(report.parsed_records, 1);
        assert_eq!(report.eligible_records, 1);
        assert_eq!(report.registered_rules, 0);
        assert_eq!(
            report.loaded_records,
            vec![LoadedAdmittedRewrite {
                transform_name: "ay_lra_basis_sub_zero".to_string(),
                transform_version: "v1".to_string(),
                kernel_family: "ay_lra_basis_update".to_string(),
                kernel_name: Some("ay_lra_basis_row_batch".to_string()),
                allowlist_entry: Some("rewrite-admission/ay-lra-basis-update-v1".to_string()),
                target_arch: "aarch64".to_string(),
                aarch64_cost_delta: 5,
                discovered_rule_name: Some("ay_lra_basis_sub_zero".to_string()),
                discovered_rule_proof_hash: Some(AY_LRA_BASIS_SUB_ZERO_PROOF_HASH),
                proof_hash: AY_LRA_BASIS_SUB_ZERO_PROOF_HASH,
            }]
        );
    }

    #[test]
    fn enabled_registration_registers_reviewed_sparse_add_zero_rule_once() {
        let json = admitted_json();
        let mut engine = RewriteEngine::new();

        let report = register_admitted_rewrites_from_json(
            [json.as_str(), json.as_str()],
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
            &mut engine,
        )
        .expect("admitted record should parse and register");

        assert_eq!(report.input_records, 2);
        assert_eq!(report.parsed_records, 2);
        assert_eq!(report.eligible_records, 2);
        assert_eq!(report.registered_rules, 1);
        assert_eq!(engine.num_rules(), 1);
    }

    #[test]
    fn enabled_registration_registers_reviewed_basis_sub_zero_rule_once() {
        let json = basis_update_json();
        let mut engine = RewriteEngine::new();

        let report = register_admitted_rewrites_from_json(
            [json.as_str(), json.as_str()],
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
            &mut engine,
        )
        .expect("basis update admitted record should parse and register");

        assert_eq!(report.input_records, 2);
        assert_eq!(report.parsed_records, 2);
        assert_eq!(report.eligible_records, 2);
        assert_eq!(report.registered_rules, 1);
        assert_eq!(engine.num_rules(), 1);
    }

    #[test]
    fn registration_is_disabled_by_default() {
        let json = admitted_json();
        let mut engine = RewriteEngine::new();

        let report = register_admitted_rewrites_from_json(
            [json.as_str()],
            RewriteAdmissionLoaderConfig::default(),
            &mut engine,
        )
        .expect("disabled loader should not parse");

        assert!(!report.loader_enabled);
        assert_eq!(report.input_records, 1);
        assert_eq!(report.parsed_records, 0);
        assert_eq!(report.eligible_records, 0);
        assert_eq!(report.registered_rules, 0);
        assert_eq!(engine.num_rules(), 0);
    }

    #[test]
    fn enabled_registration_ignores_unsupported_transform_without_panic() {
        let mut value: serde_json::Value =
            serde_json::from_str(&admitted_json()).expect("test JSON");
        value["transform"]["name"] =
            serde_json::Value::String("ty_parent_loop_strength_reduce".to_string());
        value["transform"]["discovered_rule_name"] =
            serde_json::Value::String("ty_parent_loop_strength_reduce".to_string());
        value["proof_guided_admission"]["transform_name"] =
            serde_json::Value::String("ty_parent_loop_strength_reduce".to_string());
        value["certificate_identity"]["certificate_chain_id"] = serde_json::Value::String(
            "ty_parent_loop_strength_reduce@v1:00000000000000000000000000005678".to_string(),
        );
        let json = value.to_string();
        let mut engine = RewriteEngine::new();

        let report = register_admitted_rewrites_from_json(
            [json.as_str()],
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
            &mut engine,
        )
        .expect("unsupported transform should parse");

        assert_eq!(report.parsed_records, 1);
        assert_eq!(report.eligible_records, 1);
        assert_eq!(report.registered_rules, 0);
        assert_eq!(engine.num_rules(), 0);
    }

    #[test]
    fn enabled_registration_requires_aarch64_target() {
        let mut value: serde_json::Value =
            serde_json::from_str(&admitted_json()).expect("test JSON");
        value["target"]["arch"] = serde_json::Value::String("x86_64".to_string());
        let json = value.to_string();
        let mut engine = RewriteEngine::new();

        let report = register_admitted_rewrites_from_json(
            [json.as_str()],
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
            &mut engine,
        )
        .expect("record should parse");

        assert_eq!(report.parsed_records, 1);
        assert_eq!(report.eligible_records, 0);
        assert_eq!(report.registered_rules, 0);
        assert_eq!(engine.num_rules(), 0);
    }

    #[test]
    fn enabled_registration_requires_positive_aarch64_cost_delta() {
        let mut value: serde_json::Value =
            serde_json::from_str(&admitted_json()).expect("test JSON");
        value["aarch64_cost_delta"] = serde_json::Value::from(0);
        let json = value.to_string();
        let mut engine = RewriteEngine::new();

        let report = register_admitted_rewrites_from_json(
            [json.as_str()],
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
            &mut engine,
        )
        .expect("record should parse");

        assert_eq!(report.parsed_records, 1);
        assert_eq!(report.eligible_records, 0);
        assert_eq!(report.registered_rules, 0);
        assert_eq!(engine.num_rules(), 0);
    }

    #[test]
    fn enabled_registration_requires_discovered_proof_hash_match_when_present() {
        let mut value: serde_json::Value =
            serde_json::from_str(&admitted_json()).expect("test JSON");
        value["transform"]["discovered_rule_proof_hash"] = serde_json::Value::from(48880);
        let json = value.to_string();
        let mut engine = RewriteEngine::new();

        let report = register_admitted_rewrites_from_json(
            [json.as_str()],
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
            &mut engine,
        )
        .expect("record should parse");

        assert_eq!(report.parsed_records, 1);
        assert_eq!(report.eligible_records, 0);
        assert_eq!(report.registered_rules, 0);
        assert_eq!(engine.num_rules(), 0);
    }

    #[test]
    fn enabled_registration_requires_discovered_proof_hash() {
        let mut value: serde_json::Value =
            serde_json::from_str(&admitted_json()).expect("test JSON");
        value["transform"]
            .as_object_mut()
            .expect("transform object")
            .remove("discovered_rule_proof_hash");
        let json = value.to_string();
        let mut engine = RewriteEngine::new();

        let report = register_admitted_rewrites_from_json(
            [json.as_str()],
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
            &mut engine,
        )
        .expect("record should parse");

        assert_eq!(report.parsed_records, 1);
        assert_eq!(report.eligible_records, 0);
        assert_eq!(report.registered_rules, 0);
        assert_eq!(engine.num_rules(), 0);
    }

    #[test]
    fn enabled_preview_ignores_profile_only_record() {
        let mut value: serde_json::Value =
            serde_json::from_str(&admitted_json()).expect("test JSON");
        value["admission_state"] = serde_json::Value::String("proved_profile_only".to_string());
        let json = value.to_string();

        let report = load_admitted_rewrites_from_json(
            [json.as_str()],
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
        )
        .expect("profile-only record should parse");

        assert_eq!(report.parsed_records, 1);
        assert_eq!(report.eligible_records, 0);
        assert_eq!(report.registered_rules, 0);
        assert!(report.loaded_records.is_empty());
    }

    #[test]
    fn enabled_preview_rejects_legacy_boolean_product_gates_without_800_verdict() {
        let mut value: serde_json::Value =
            serde_json::from_str(&admitted_json()).expect("test JSON");
        value
            .as_object_mut()
            .expect("record object")
            .remove("proof_guided_admission");
        let json = value.to_string();

        let report = load_admitted_rewrites_from_json(
            [json.as_str()],
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
        )
        .expect("record should parse");

        assert_eq!(report.parsed_records, 1);
        assert_eq!(report.eligible_records, 0);
        assert_eq!(report.registered_rules, 0);
        assert!(report.loaded_records.is_empty());
    }

    #[test]
    fn enabled_preview_requires_complete_800_verdict_evidence() {
        type EvidenceMutation = (&'static str, fn(&mut serde_json::Value));

        let cases: [EvidenceMutation; 6] = [
            ("missing_proof_fact", |value| {
                value["proof_guided_admission"]["consumed_proof_facts"] =
                    serde_json::json!(["ay-lra-sparse-substitute-row-order"]);
            }),
            ("missing_manifest_hash", |value| {
                value["proof_guided_admission"]["manifest_hash"] =
                    serde_json::Value::String(String::new());
            }),
            ("missing_replay_root", |value| {
                value["proof_guided_admission"]["replay_artifact_root"] =
                    serde_json::Value::String(String::new());
            }),
            ("missing_telemetry_counter", |value| {
                value["proof_guided_admission"]
                    .as_object_mut()
                    .expect("verdict object")
                    .remove("telemetry_useful_native_applications");
            }),
            ("failed_validation_hash", |value| {
                value["proof_guided_admission"]["validation_result_hash"] =
                    serde_json::Value::String("sha256:stale-validation".to_string());
            }),
            ("missing_rollback_knob", |value| {
                value["proof_guided_admission"]["rollback_or_disable_knob"] =
                    serde_json::Value::String(String::new());
            }),
        ];

        for (name, mutate) in cases {
            let mut value: serde_json::Value =
                serde_json::from_str(&admitted_json()).expect("test JSON");
            mutate(&mut value);
            let json = value.to_string();
            let report = load_admitted_rewrites_from_json(
                [json.as_str()],
                RewriteAdmissionLoaderConfig::enabled_for_preview(),
            )
            .unwrap_or_else(|err| panic!("{name} should parse: {err}"));

            assert_eq!(report.parsed_records, 1, "{name}");
            assert_eq!(report.eligible_records, 0, "{name}");
            assert_eq!(report.registered_rules, 0, "{name}");
            assert!(report.loaded_records.is_empty(), "{name}");
        }
    }

    #[test]
    fn enabled_preview_ignores_admitted_record_without_certificate_identity() {
        let mut value: serde_json::Value =
            serde_json::from_str(&admitted_json()).expect("test JSON");
        value
            .as_object_mut()
            .expect("record object")
            .remove("certificate_identity");
        let json = value.to_string();

        let report = load_admitted_rewrites_from_json(
            [json.as_str()],
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
        )
        .expect("record should parse");

        assert_eq!(report.parsed_records, 1);
        assert_eq!(report.eligible_records, 0);
        assert_eq!(report.registered_rules, 0);
        assert!(report.loaded_records.is_empty());
    }

    #[test]
    fn enabled_preview_requires_certificate_chain_to_match_transform_identity() {
        let mut value: serde_json::Value =
            serde_json::from_str(&admitted_json()).expect("test JSON");
        value["certificate_identity"]["certificate_chain_id"] = serde_json::Value::String(
            "other_transform@v1:00000000000000000000000000005678".to_string(),
        );
        let json = value.to_string();

        let report = load_admitted_rewrites_from_json(
            [json.as_str()],
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
        )
        .expect("record should parse");

        assert_eq!(report.parsed_records, 1);
        assert_eq!(report.eligible_records, 0);
        assert_eq!(report.registered_rules, 0);
        assert!(report.loaded_records.is_empty());
    }

    #[test]
    fn enabled_preview_rejects_stale_same_transform_certificate_hash() {
        let mut value: serde_json::Value =
            serde_json::from_str(&admitted_json()).expect("test JSON");
        value["certificate_identity"]["certificate_hash"] =
            serde_json::Value::String("0000000000000000feedfacecafebe00".to_string());
        let json = value.to_string();

        let report = load_admitted_rewrites_from_json(
            [json.as_str()],
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
        )
        .expect("record should parse");

        assert_eq!(report.parsed_records, 1);
        assert_eq!(report.eligible_records, 0);
        assert_eq!(report.registered_rules, 0);
        assert!(report.loaded_records.is_empty());
    }

    #[test]
    fn enabled_preview_rejects_stale_same_transform_validation_hash() {
        let mut value: serde_json::Value =
            serde_json::from_str(&admitted_json()).expect("test JSON");
        value["certificate_identity"]["certificate_chain_id"] = serde_json::Value::String(
            "ay_lra_sparse_add_zero@v1:00000000000000000000000000005679".to_string(),
        );
        let json = value.to_string();

        let report = load_admitted_rewrites_from_json(
            [json.as_str()],
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
        )
        .expect("record should parse");

        assert_eq!(report.parsed_records, 1);
        assert_eq!(report.eligible_records, 0);
        assert_eq!(report.registered_rules, 0);
        assert!(report.loaded_records.is_empty());
    }

    #[test]
    fn enabled_registration_rejects_legacy_unbound_stale_same_transform_record() {
        let mut value: serde_json::Value =
            serde_json::from_str(&admitted_json()).expect("test JSON");
        let stale_proof_hash = AY_LRA_SPARSE_ADD_ZERO_PROOF_HASH + 1;
        value["transform"]["discovered_rule_proof_hash"] =
            serde_json::Value::from(stale_proof_hash);
        value["evidence"]["proof_hash"] = serde_json::Value::from(stale_proof_hash);
        let transform = value["transform"]
            .as_object_mut()
            .expect("transform object");
        transform.remove("certificate_hash");
        transform.remove("certificate_validation_hash");
        value["certificate_identity"]["certificate_hash"] =
            serde_json::Value::String("0000000000000000feedfacecafebe00".to_string());
        value["certificate_identity"]["certificate_chain_id"] = serde_json::Value::String(
            "ay_lra_sparse_add_zero@v1:00000000000000000000000000005679".to_string(),
        );
        let json = value.to_string();
        let mut engine = RewriteEngine::new();

        let report = register_admitted_rewrites_from_json(
            [json.as_str()],
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
            &mut engine,
        )
        .expect("record should parse");

        assert_eq!(report.parsed_records, 1);
        assert_eq!(report.eligible_records, 0);
        assert_eq!(report.registered_rules, 0);
        assert_eq!(engine.num_rules(), 0);
    }

    #[test]
    fn enabled_preview_rejects_legacy_unbound_stale_basis_transform_record() {
        let mut value: serde_json::Value =
            serde_json::from_str(&basis_update_json()).expect("test JSON");
        let stale_proof_hash = AY_LRA_BASIS_SUB_ZERO_PROOF_HASH + 1;
        value["transform"]["discovered_rule_proof_hash"] =
            serde_json::Value::from(stale_proof_hash);
        value["evidence"]["proof_hash"] = serde_json::Value::from(stale_proof_hash);
        let transform = value["transform"]
            .as_object_mut()
            .expect("transform object");
        transform.remove("certificate_hash");
        transform.remove("certificate_validation_hash");
        value["certificate_identity"]["certificate_hash"] =
            serde_json::Value::String("0000000000000000ba5eba5ecafed00e".to_string());
        value["certificate_identity"]["certificate_chain_id"] = serde_json::Value::String(
            "ay_lra_basis_sub_zero@v1:0000000000000000000000000000ba5f".to_string(),
        );
        let json = value.to_string();

        let report = load_admitted_rewrites_from_json(
            [json.as_str()],
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
        )
        .expect("record should parse");

        assert_eq!(report.parsed_records, 1);
        assert_eq!(report.eligible_records, 0);
        assert_eq!(report.registered_rules, 0);
        assert!(report.loaded_records.is_empty());
    }

    #[test]
    fn enabled_preview_ignores_admitted_record_without_ay_lra_manifest_binding() {
        let mut value: serde_json::Value =
            serde_json::from_str(&admitted_json()).expect("test JSON");
        value
            .as_object_mut()
            .expect("record object")
            .remove("ay_lra_manifest_binding");
        let json = value.to_string();

        let report = load_admitted_rewrites_from_json(
            [json.as_str()],
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
        )
        .expect("record should parse");

        assert_eq!(report.parsed_records, 1);
        assert_eq!(report.eligible_records, 0);
        assert_eq!(report.registered_rules, 0);
        assert!(report.loaded_records.is_empty());
    }

    #[test]
    fn enabled_preview_ignores_admitted_record_with_mismatched_ay_lra_kernel_family() {
        let mut value: serde_json::Value =
            serde_json::from_str(&admitted_json()).expect("test JSON");
        value["ay_lra_manifest_binding"]["kernel_family"] =
            serde_json::Value::String("ay_lra_basis_update".to_string());
        value["ay_lra_manifest_binding"]["proof_family"] =
            serde_json::Value::String("ay_lra_basis_update".to_string());
        value["ay_lra_manifest_binding"]["allowlist_family"] =
            serde_json::Value::String("ay_lra_basis_update".to_string());
        value["ay_lra_manifest_binding"]["required_certificate_dependencies"] =
            serde_json::json!([
                "ay-lra-basis-sorted-rows",
                "ay-lra-basis-output-bounds",
                "ay-lra-basis-overflow",
                "ay-lra-basis-alias-policy",
                "ay-lra-basis-epoch",
                "ay-lra-basis-prefix-rollback"
            ]);
        let json = value.to_string();

        let report = load_admitted_rewrites_from_json(
            [json.as_str()],
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
        )
        .expect("record should parse");

        assert_eq!(report.parsed_records, 1);
        assert_eq!(report.eligible_records, 0);
        assert_eq!(report.registered_rules, 0);
        assert!(report.loaded_records.is_empty());
    }

    #[test]
    fn enabled_preview_requires_exact_ay_lra_allowlist_entry() {
        let mut value: serde_json::Value =
            serde_json::from_str(&admitted_json()).expect("test JSON");
        value["allowlist"]["allowlist_entry"] =
            serde_json::Value::String("rewrite-admission/spoofed-entry".to_string());
        let json = value.to_string();

        let report = load_admitted_rewrites_from_json(
            [json.as_str()],
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
        )
        .expect("record should parse");

        assert_eq!(report.parsed_records, 1);
        assert_eq!(report.eligible_records, 0);
        assert_eq!(report.registered_rules, 0);
        assert!(report.loaded_records.is_empty());
    }

    #[test]
    fn enabled_preview_rejects_unsupported_schema() {
        let mut value: serde_json::Value =
            serde_json::from_str(&admitted_json()).expect("test JSON");
        value["schema_version"] = serde_json::Value::from(999);
        let json = value.to_string();

        let err = load_admitted_rewrites_from_json(
            [json.as_str()],
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
        )
        .expect_err("schema mismatch should fail");

        assert_eq!(
            err,
            RewriteAdmissionLoadError::UnsupportedSchema {
                schema: REWRITE_ADMISSION_SCHEMA.to_string(),
                schema_version: 999,
            }
        );
    }
}
