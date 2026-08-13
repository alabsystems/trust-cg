// trust-cg-codegen/rewrite_admission.rs - Data-only rewrite admission records
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Data-only rewrite admission records for proof-backed native rewrites.
//!
//! This module intentionally does not grant product install authority. It
//! records the proof-optimization certificate citation, AArch64 cost facts, and
//! a fail-closed admission disposition for downstream auditing.

use crate::jit_diagnostics::sha256_hex;
use crate::pipeline::ProofOptimizationCertificateCitation;
use serde::{Deserialize, Serialize};

/// Stable schema tag for data-only rewrite admission records.
pub const REWRITE_ADMISSION_RECORD_SCHEMA: &str = "trust-cg.codegen.rewrite_admission_record";

/// Stable numeric schema version for data-only rewrite admission records.
pub const REWRITE_ADMISSION_RECORD_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for tiny-block superopt rewrite admission records.
pub const TINY_BLOCK_SUPEROPT_REWRITE_ADMISSION_RECORD_SCHEMA: &str =
    "trust-cg.codegen.tiny_block_superopt_rewrite_admission_record";

/// Stable numeric schema version for tiny-block superopt rewrite admission records.
pub const TINY_BLOCK_SUPEROPT_REWRITE_ADMISSION_RECORD_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for local reducer inputs derived from rejected
/// tiny-block superopt counterexamples.
pub const TINY_BLOCK_SUPEROPT_COUNTEREXAMPLE_REDUCER_RECORD_SCHEMA: &str =
    "trust-cg.codegen.tiny_block_superopt_counterexample_reducer_record";

/// Stable numeric schema version for local counterexample reducer records.
pub const TINY_BLOCK_SUPEROPT_COUNTEREXAMPLE_REDUCER_RECORD_SCHEMA_VERSION: u32 = 1;

/// Stable local reducer family for rejected tiny-block superopt counterexamples.
pub const TINY_BLOCK_SUPEROPT_COUNTEREXAMPLE_REDUCER_FAMILY: &str =
    "tiny_block_superopt_counterexample";

/// Admission disposition for the first S3 rewrite-admission slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RewriteAdmissionDisposition {
    /// The rewrite is admitted only as non-promoting metadata.
    AdmitNonPromoting,
    /// The rewrite is rejected and must not be used for native rewrite routing.
    Reject,
}

impl RewriteAdmissionDisposition {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::AdmitNonPromoting => "admit_non_promoting",
            Self::Reject => "reject",
        }
    }
}

/// Fail-closed rejection reasons for tiny-block superopt rewrite admission.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TinyBlockSuperoptRewriteRejection {
    AdmissionDisabled,
    MissingOriginalIdentity,
    MissingOriginalHash,
    MissingReplacementIdentity,
    MissingReplacementHash,
    MissingCertificateIdentity,
    MissingCertificateHash,
    MalformedOriginalIdentity,
    MalformedOriginalHash,
    MalformedReplacementIdentity,
    MalformedReplacementHash,
    MalformedCertificateIdentity,
    MalformedCertificateHash,
    MalformedCounterexampleIdentity,
    MalformedCounterexampleHash,
    CounterexampleModel,
    CostRegression,
    CostDeltaMismatch,
    DiagnosticReasonMismatch,
    ChecksumMismatch,
    ProductInstallAuthority,
}

impl TinyBlockSuperoptRewriteRejection {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::AdmissionDisabled => "admission_disabled",
            Self::MissingOriginalIdentity => "missing_original_identity",
            Self::MissingOriginalHash => "missing_original_hash",
            Self::MissingReplacementIdentity => "missing_replacement_identity",
            Self::MissingReplacementHash => "missing_replacement_hash",
            Self::MissingCertificateIdentity => "missing_certificate_identity",
            Self::MissingCertificateHash => "missing_certificate_hash",
            Self::MalformedOriginalIdentity => "malformed_original_identity",
            Self::MalformedOriginalHash => "malformed_original_hash",
            Self::MalformedReplacementIdentity => "malformed_replacement_identity",
            Self::MalformedReplacementHash => "malformed_replacement_hash",
            Self::MalformedCertificateIdentity => "malformed_certificate_identity",
            Self::MalformedCertificateHash => "malformed_certificate_hash",
            Self::MalformedCounterexampleIdentity => "malformed_counterexample_identity",
            Self::MalformedCounterexampleHash => "malformed_counterexample_hash",
            Self::CounterexampleModel => "counterexample_model",
            Self::CostRegression => "cost_regression",
            Self::CostDeltaMismatch => "cost_delta_mismatch",
            Self::DiagnosticReasonMismatch => "diagnostic_reason_mismatch",
            Self::ChecksumMismatch => "checksum_mismatch",
            Self::ProductInstallAuthority => "product_install_authority",
        }
    }
}

/// Fail-closed reasons for counterexample reducer record materialization.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TinyBlockSuperoptCounterexampleReducerRejection {
    SourceAdmissionChecksumMismatch,
    SourceRejectionMismatch,
    SourceDiagnosticReasonMismatch,
    MissingCounterexampleModel,
    MalformedReducerInputIdentity,
    MalformedCounterexampleModel,
    MalformedRequiredPreconditionGap,
    ProductInstallAuthority,
    ChecksumMismatch,
}

impl TinyBlockSuperoptCounterexampleReducerRejection {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::SourceAdmissionChecksumMismatch => "source_admission_checksum_mismatch",
            Self::SourceRejectionMismatch => "source_rejection_mismatch",
            Self::SourceDiagnosticReasonMismatch => "source_diagnostic_reason_mismatch",
            Self::MissingCounterexampleModel => "missing_counterexample_model",
            Self::MalformedReducerInputIdentity => "malformed_reducer_input_identity",
            Self::MalformedCounterexampleModel => "malformed_counterexample_model",
            Self::MalformedRequiredPreconditionGap => "malformed_required_precondition_gap",
            Self::ProductInstallAuthority => "product_install_authority",
            Self::ChecksumMismatch => "checksum_mismatch",
        }
    }
}

/// Fail-closed rejection reasons for rewrite admission validation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RewriteAdmissionRejection {
    MissingCertificateIdentity,
    MissingTransformIdentity,
    MissingSourceRegionHash,
    MissingTargetRegionHash,
    RejectedCertificateEvidence,
    MissingConsumedProofFact,
    ValidationHashMismatch,
    MissingManifestHash,
    MissingRuntimeStatusContract,
    MissingReplayArtifactRoot,
    MissingTelemetryUsefulNativeCounter,
    MissingRollbackDisableKnob,
    UnsupportedTargetArch,
    UnprofitableCost,
    ChecksumMismatch,
}

impl RewriteAdmissionRejection {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::MissingCertificateIdentity => "missing_certificate_identity",
            Self::MissingTransformIdentity => "missing_transform_identity",
            Self::MissingSourceRegionHash => "missing_source_region_hash",
            Self::MissingTargetRegionHash => "missing_target_region_hash",
            Self::RejectedCertificateEvidence => "rejected_certificate_evidence",
            Self::MissingConsumedProofFact => "missing_consumed_proof_fact",
            Self::ValidationHashMismatch => "validation_hash_mismatch",
            Self::MissingManifestHash => "missing_manifest_hash",
            Self::MissingRuntimeStatusContract => "missing_runtime_status_contract",
            Self::MissingReplayArtifactRoot => "missing_replay_artifact_root",
            Self::MissingTelemetryUsefulNativeCounter => "missing_telemetry_useful_native_counter",
            Self::MissingRollbackDisableKnob => "missing_rollback_disable_knob",
            Self::UnsupportedTargetArch => "unsupported_target_arch",
            Self::UnprofitableCost => "unprofitable_cost",
            Self::ChecksumMismatch => "checksum_mismatch",
        }
    }
}

/// Stable original or replacement identity for a tiny-block superopt candidate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TinyBlockSuperoptRewriteIdentity {
    pub identity: String,
    pub sha256: String,
}

impl TinyBlockSuperoptRewriteIdentity {
    pub fn new(identity: impl Into<String>, sha256: impl Into<String>) -> Self {
        Self {
            identity: identity.into(),
            sha256: sha256.into(),
        }
    }
}

/// Certificate identity bound to a tiny-block superopt candidate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TinyBlockSuperoptCertificateIdentity {
    pub identity: String,
    pub sha256: String,
}

impl TinyBlockSuperoptCertificateIdentity {
    pub fn new(identity: impl Into<String>, sha256: impl Into<String>) -> Self {
        Self {
            identity: identity.into(),
            sha256: sha256.into(),
        }
    }
}

/// Optional solver counterexample model attached to a rejected candidate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TinyBlockSuperoptCounterexampleModel {
    pub identity: String,
    pub sha256: String,
}

impl TinyBlockSuperoptCounterexampleModel {
    pub fn new(identity: impl Into<String>, sha256: impl Into<String>) -> Self {
        Self {
            identity: identity.into(),
            sha256: sha256.into(),
        }
    }
}

/// Cost-model facts for a tiny-block superopt rewrite candidate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TinyBlockSuperoptCostModel {
    pub original_cost_cycles: u64,
    pub replacement_cost_cycles: u64,
    pub delta_cycles: i64,
}

impl TinyBlockSuperoptCostModel {
    pub fn new(original_cost_cycles: u64, replacement_cost_cycles: u64) -> Self {
        Self {
            original_cost_cycles,
            replacement_cost_cycles,
            delta_cycles: signed_cost_delta(original_cost_cycles, replacement_cost_cycles),
        }
    }
}

/// Local reducer input derived from a rejected tiny-block superopt candidate
/// with a ay counterexample model.
///
/// This record is intentionally compiler-local evidence. It can seed reducers,
/// but it carries no product publication, activation, or install authority.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TinyBlockSuperoptCounterexampleReducerRecord {
    pub schema: String,
    pub schema_version: u32,
    pub reducer_family: String,
    pub original: TinyBlockSuperoptRewriteIdentity,
    pub replacement: TinyBlockSuperoptRewriteIdentity,
    pub rejection_reason: TinyBlockSuperoptRewriteRejection,
    pub counterexample_model: TinyBlockSuperoptCounterexampleModel,
    pub required_precondition_gap: Option<String>,
    pub source_admission_record_checksum: String,
    pub local_compiler_evidence_only: bool,
    pub publish_product_artifact: bool,
    pub activate_product: bool,
    pub product_install_authority: bool,
    pub record_checksum: String,
}

impl TinyBlockSuperoptCounterexampleReducerRecord {
    fn from_rejected_candidate_parts(
        original: TinyBlockSuperoptRewriteIdentity,
        replacement: TinyBlockSuperoptRewriteIdentity,
        rejection_reason: TinyBlockSuperoptRewriteRejection,
        counterexample_model: TinyBlockSuperoptCounterexampleModel,
        required_precondition_gap: Option<String>,
        source_admission_record_checksum: String,
    ) -> Self {
        let mut record = Self {
            schema: TINY_BLOCK_SUPEROPT_COUNTEREXAMPLE_REDUCER_RECORD_SCHEMA.to_owned(),
            schema_version: TINY_BLOCK_SUPEROPT_COUNTEREXAMPLE_REDUCER_RECORD_SCHEMA_VERSION,
            reducer_family: TINY_BLOCK_SUPEROPT_COUNTEREXAMPLE_REDUCER_FAMILY.to_owned(),
            original,
            replacement,
            rejection_reason,
            counterexample_model,
            required_precondition_gap,
            source_admission_record_checksum,
            local_compiler_evidence_only: true,
            publish_product_artifact: false,
            activate_product: false,
            product_install_authority: false,
            record_checksum: String::new(),
        };

        record.record_checksum = record.canonical_record_checksum();
        record
    }

    /// True when the reducer record grants product install authority. This
    /// local reducer input never does.
    pub fn grants_product_install_authority(&self) -> bool {
        false
    }

    /// Validate reducer-input integrity and that publication/product activation
    /// remain disabled.
    pub fn validate(&self) -> Result<(), TinyBlockSuperoptCounterexampleReducerRejection> {
        if self.record_checksum != self.canonical_record_checksum() {
            return Err(TinyBlockSuperoptCounterexampleReducerRejection::ChecksumMismatch);
        }
        if !self.local_compiler_evidence_only
            || self.publish_product_artifact
            || self.activate_product
            || self.product_install_authority
            || self.grants_product_install_authority()
        {
            return Err(TinyBlockSuperoptCounterexampleReducerRejection::ProductInstallAuthority);
        }
        if malformed_rewrite_identity(&self.original)
            || malformed_rewrite_identity(&self.replacement)
        {
            return Err(
                TinyBlockSuperoptCounterexampleReducerRejection::MalformedReducerInputIdentity,
            );
        }
        if malformed_counterexample_model(&self.counterexample_model) {
            return Err(
                TinyBlockSuperoptCounterexampleReducerRejection::MalformedCounterexampleModel,
            );
        }
        if malformed_sha256(&self.source_admission_record_checksum) {
            return Err(
                TinyBlockSuperoptCounterexampleReducerRejection::SourceAdmissionChecksumMismatch,
            );
        }
        if self
            .required_precondition_gap
            .as_deref()
            .is_some_and(malformed_precondition_gap)
        {
            return Err(
                TinyBlockSuperoptCounterexampleReducerRejection::MalformedRequiredPreconditionGap,
            );
        }
        Ok(())
    }

    /// Deterministic JSON for the full reducer record, including
    /// `record_checksum`.
    pub fn stable_json(&self) -> String {
        self.to_json_value().to_string()
    }

    /// Deterministic JSON object for the full reducer record.
    pub fn to_json_value(&self) -> serde_json::Value {
        let mut object = self.payload_json_map();
        object.insert(
            "record_checksum".to_owned(),
            serde_json::Value::String(self.record_checksum.clone()),
        );
        serde_json::Value::Object(object)
    }

    /// Deterministic checksum over the reducer record payload excluding
    /// `record_checksum`.
    pub fn canonical_record_checksum(&self) -> String {
        format!(
            "sha256:{}",
            sha256_hex(self.canonical_payload_json().as_bytes())
        )
    }

    /// Deterministic JSON payload used as the reducer checksum input.
    pub fn canonical_payload_json(&self) -> String {
        serde_json::Value::Object(self.payload_json_map()).to_string()
    }

    fn payload_json_map(&self) -> serde_json::Map<String, serde_json::Value> {
        let mut object = serde_json::Map::with_capacity(13);
        object.insert(
            "schema".to_owned(),
            serde_json::Value::String(self.schema.clone()),
        );
        object.insert(
            "schema_version".to_owned(),
            serde_json::Value::Number(serde_json::Number::from(u64::from(self.schema_version))),
        );
        object.insert(
            "reducer_family".to_owned(),
            serde_json::Value::String(self.reducer_family.clone()),
        );
        object.insert("original".to_owned(), rewrite_identity_json(&self.original));
        object.insert(
            "replacement".to_owned(),
            rewrite_identity_json(&self.replacement),
        );
        object.insert(
            "rejection_reason".to_owned(),
            serde_json::Value::String(self.rejection_reason.as_str().to_owned()),
        );
        object.insert(
            "counterexample_model".to_owned(),
            counterexample_model_json(&self.counterexample_model),
        );
        object.insert(
            "required_precondition_gap".to_owned(),
            self.required_precondition_gap
                .as_ref()
                .map_or(serde_json::Value::Null, |gap| {
                    serde_json::Value::String(gap.clone())
                }),
        );
        object.insert(
            "source_admission_record_checksum".to_owned(),
            serde_json::Value::String(self.source_admission_record_checksum.clone()),
        );
        object.insert(
            "local_compiler_evidence_only".to_owned(),
            serde_json::Value::Bool(self.local_compiler_evidence_only),
        );
        object.insert(
            "publish_product_artifact".to_owned(),
            serde_json::Value::Bool(self.publish_product_artifact),
        );
        object.insert(
            "activate_product".to_owned(),
            serde_json::Value::Bool(self.activate_product),
        );
        object.insert(
            "product_install_authority".to_owned(),
            serde_json::Value::Bool(self.product_install_authority),
        );
        object
    }
}

/// Complete proof-guided evidence required before a rewrite can even become
/// non-promoting admission metadata.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofGuidedAdmissionEvidence {
    /// Hash of the ay/TY proof-consumption manifest that admitted the family.
    pub manifest_hash: String,
    /// Runtime guard, deopt, or typed status ABI contract bound to the rewrite.
    pub runtime_status_contract: String,
    /// Replay artifact root that can reproduce the admitted or rejected verdict.
    pub replay_artifact_root: String,
    /// Telemetry counter family containing useful-native application counts.
    pub telemetry_counter_family: String,
    /// Observed useful-native application count for this exact candidate tuple.
    pub telemetry_useful_native_applications: Option<u64>,
    /// Rollback or disable knob that can stop the admitted tuple.
    pub rollback_disable_knob: String,
}

impl ProofGuidedAdmissionEvidence {
    pub fn new(
        manifest_hash: impl Into<String>,
        runtime_status_contract: impl Into<String>,
        replay_artifact_root: impl Into<String>,
        telemetry_counter_family: impl Into<String>,
        telemetry_useful_native_applications: u64,
        rollback_disable_knob: impl Into<String>,
    ) -> Self {
        Self {
            manifest_hash: manifest_hash.into(),
            runtime_status_contract: runtime_status_contract.into(),
            replay_artifact_root: replay_artifact_root.into(),
            telemetry_counter_family: telemetry_counter_family.into(),
            telemetry_useful_native_applications: Some(telemetry_useful_native_applications),
            rollback_disable_knob: rollback_disable_knob.into(),
        }
    }
}

/// Tiny-block superopt rewrite admission record.
///
/// This is certificate-bound, data-only metadata. A valid candidate can only be
/// admitted as non-promoting audit evidence; product install authority remains
/// false and must be granted by a separate downstream gate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TinyBlockSuperoptRewriteAdmissionRecord {
    pub schema: String,
    pub schema_version: u32,
    pub original: TinyBlockSuperoptRewriteIdentity,
    pub replacement: TinyBlockSuperoptRewriteIdentity,
    pub cost_model: TinyBlockSuperoptCostModel,
    pub certificate: Option<TinyBlockSuperoptCertificateIdentity>,
    pub counterexample_model: Option<TinyBlockSuperoptCounterexampleModel>,
    pub admission_enabled: bool,
    pub disposition: RewriteAdmissionDisposition,
    pub rejection: Option<TinyBlockSuperoptRewriteRejection>,
    pub diagnostic_reason: Option<String>,
    pub product_install_authority: bool,
    pub record_checksum: String,
}

impl TinyBlockSuperoptRewriteAdmissionRecord {
    /// Build and validate a tiny-block superopt rewrite admission candidate.
    pub fn from_candidate(
        original: TinyBlockSuperoptRewriteIdentity,
        replacement: TinyBlockSuperoptRewriteIdentity,
        cost_model: TinyBlockSuperoptCostModel,
        certificate: Option<TinyBlockSuperoptCertificateIdentity>,
        counterexample_model: Option<TinyBlockSuperoptCounterexampleModel>,
    ) -> Self {
        Self::from_candidate_with_admission_enabled(
            original,
            replacement,
            cost_model,
            certificate,
            counterexample_model,
            true,
        )
    }

    /// Build and validate a tiny-block superopt rewrite admission candidate
    /// with an explicit kill-switch state.
    pub fn from_candidate_with_admission_enabled(
        original: TinyBlockSuperoptRewriteIdentity,
        replacement: TinyBlockSuperoptRewriteIdentity,
        cost_model: TinyBlockSuperoptCostModel,
        certificate: Option<TinyBlockSuperoptCertificateIdentity>,
        counterexample_model: Option<TinyBlockSuperoptCounterexampleModel>,
        admission_enabled: bool,
    ) -> Self {
        let mut record = Self {
            schema: TINY_BLOCK_SUPEROPT_REWRITE_ADMISSION_RECORD_SCHEMA.to_owned(),
            schema_version: TINY_BLOCK_SUPEROPT_REWRITE_ADMISSION_RECORD_SCHEMA_VERSION,
            original,
            replacement,
            cost_model,
            certificate,
            counterexample_model,
            admission_enabled,
            disposition: RewriteAdmissionDisposition::Reject,
            rejection: None,
            diagnostic_reason: None,
            product_install_authority: false,
            record_checksum: String::new(),
        };

        record.recompute_disposition();
        record.record_checksum = record.canonical_record_checksum();
        record
    }

    /// True when the record grants product install authority. This data-only
    /// admission record never does.
    pub fn grants_product_install_authority(&self) -> bool {
        false
    }

    /// Materialize a local reducer input for rejected candidates that carry a
    /// stable ay counterexample model. Verified candidates produce no reducer
    /// record.
    pub fn counterexample_reducer_record(
        &self,
        required_precondition_gap: Option<String>,
    ) -> Result<
        Option<TinyBlockSuperoptCounterexampleReducerRecord>,
        TinyBlockSuperoptCounterexampleReducerRejection,
    > {
        if self.record_checksum != self.canonical_record_checksum() {
            return Err(
                TinyBlockSuperoptCounterexampleReducerRejection::SourceAdmissionChecksumMismatch,
            );
        }
        if self.product_install_authority || self.grants_product_install_authority() {
            return Err(TinyBlockSuperoptCounterexampleReducerRejection::ProductInstallAuthority);
        }

        let rejection = self.first_rejection();
        if self.rejection != rejection {
            return Err(TinyBlockSuperoptCounterexampleReducerRejection::SourceRejectionMismatch);
        }
        let expected_reason = rejection.map(|reason| reason.as_str().to_owned());
        if self.diagnostic_reason != expected_reason {
            return Err(
                TinyBlockSuperoptCounterexampleReducerRejection::SourceDiagnosticReasonMismatch,
            );
        }

        let Some(rejection_reason) = rejection else {
            return Ok(None);
        };

        if malformed_rewrite_identity(&self.original)
            || malformed_rewrite_identity(&self.replacement)
        {
            return Err(
                TinyBlockSuperoptCounterexampleReducerRejection::MalformedReducerInputIdentity,
            );
        }
        if required_precondition_gap
            .as_deref()
            .is_some_and(malformed_precondition_gap)
        {
            return Err(
                TinyBlockSuperoptCounterexampleReducerRejection::MalformedRequiredPreconditionGap,
            );
        }

        let Some(counterexample_model) = self.counterexample_model.clone() else {
            return Err(
                TinyBlockSuperoptCounterexampleReducerRejection::MissingCounterexampleModel,
            );
        };
        if malformed_counterexample_model(&counterexample_model) {
            return Err(
                TinyBlockSuperoptCounterexampleReducerRejection::MalformedCounterexampleModel,
            );
        }

        Ok(Some(
            TinyBlockSuperoptCounterexampleReducerRecord::from_rejected_candidate_parts(
                self.original.clone(),
                self.replacement.clone(),
                rejection_reason,
                counterexample_model,
                required_precondition_gap,
                self.record_checksum.clone(),
            ),
        ))
    }

    /// Recompute the fail-closed disposition from the current record contents.
    pub fn recompute_disposition(&mut self) {
        self.product_install_authority = false;
        self.rejection = self.first_rejection();
        self.diagnostic_reason = self
            .rejection
            .map(|rejection| rejection.as_str().to_owned());
        self.disposition = if self.rejection.is_none() {
            RewriteAdmissionDisposition::AdmitNonPromoting
        } else {
            RewriteAdmissionDisposition::Reject
        };
    }

    /// Validate the record including its deterministic checksum and diagnostic
    /// reason.
    pub fn validate(&self) -> Result<(), TinyBlockSuperoptRewriteRejection> {
        if self.record_checksum != self.canonical_record_checksum() {
            return Err(TinyBlockSuperoptRewriteRejection::ChecksumMismatch);
        }
        if self.product_install_authority || self.grants_product_install_authority() {
            return Err(TinyBlockSuperoptRewriteRejection::ProductInstallAuthority);
        }
        let rejection = self.first_rejection();
        let expected_reason = rejection.map(|reason| reason.as_str().to_owned());
        if self.diagnostic_reason != expected_reason {
            return Err(TinyBlockSuperoptRewriteRejection::DiagnosticReasonMismatch);
        }
        if let Some(rejection) = rejection {
            return Err(rejection);
        }
        Ok(())
    }

    /// Deterministic JSON for the full record, including `record_checksum`.
    pub fn stable_json(&self) -> String {
        self.to_json_value().to_string()
    }

    /// Deterministic JSON object for the full record.
    pub fn to_json_value(&self) -> serde_json::Value {
        let mut object = self.payload_json_map();
        object.insert(
            "record_checksum".to_owned(),
            serde_json::Value::String(self.record_checksum.clone()),
        );
        serde_json::Value::Object(object)
    }

    /// Deterministic checksum over the record payload excluding
    /// `record_checksum`.
    pub fn canonical_record_checksum(&self) -> String {
        format!(
            "sha256:{}",
            sha256_hex(self.canonical_payload_json().as_bytes())
        )
    }

    /// Deterministic JSON payload used as the checksum input.
    pub fn canonical_payload_json(&self) -> String {
        serde_json::Value::Object(self.payload_json_map()).to_string()
    }

    fn first_rejection(&self) -> Option<TinyBlockSuperoptRewriteRejection> {
        if !self.admission_enabled {
            return Some(TinyBlockSuperoptRewriteRejection::AdmissionDisabled);
        }
        if missing_required_text(&self.original.identity) {
            return Some(TinyBlockSuperoptRewriteRejection::MissingOriginalIdentity);
        }
        if missing_required_text(&self.original.sha256) {
            return Some(TinyBlockSuperoptRewriteRejection::MissingOriginalHash);
        }
        if malformed_stable_identity(&self.original.identity) {
            return Some(TinyBlockSuperoptRewriteRejection::MalformedOriginalIdentity);
        }
        if malformed_sha256(&self.original.sha256) {
            return Some(TinyBlockSuperoptRewriteRejection::MalformedOriginalHash);
        }
        if missing_required_text(&self.replacement.identity) {
            return Some(TinyBlockSuperoptRewriteRejection::MissingReplacementIdentity);
        }
        if missing_required_text(&self.replacement.sha256) {
            return Some(TinyBlockSuperoptRewriteRejection::MissingReplacementHash);
        }
        if malformed_stable_identity(&self.replacement.identity) {
            return Some(TinyBlockSuperoptRewriteRejection::MalformedReplacementIdentity);
        }
        if malformed_sha256(&self.replacement.sha256) {
            return Some(TinyBlockSuperoptRewriteRejection::MalformedReplacementHash);
        }

        let Some(certificate) = &self.certificate else {
            return Some(TinyBlockSuperoptRewriteRejection::MissingCertificateIdentity);
        };
        if missing_required_text(&certificate.identity) {
            return Some(TinyBlockSuperoptRewriteRejection::MissingCertificateIdentity);
        }
        if missing_required_text(&certificate.sha256) {
            return Some(TinyBlockSuperoptRewriteRejection::MissingCertificateHash);
        }
        if malformed_stable_identity(&certificate.identity) {
            return Some(TinyBlockSuperoptRewriteRejection::MalformedCertificateIdentity);
        }
        if malformed_sha256(&certificate.sha256) {
            return Some(TinyBlockSuperoptRewriteRejection::MalformedCertificateHash);
        }

        if let Some(counterexample) = &self.counterexample_model {
            if missing_required_text(&counterexample.identity)
                || malformed_stable_identity(&counterexample.identity)
            {
                return Some(TinyBlockSuperoptRewriteRejection::MalformedCounterexampleIdentity);
            }
            if missing_required_text(&counterexample.sha256)
                || malformed_sha256(&counterexample.sha256)
            {
                return Some(TinyBlockSuperoptRewriteRejection::MalformedCounterexampleHash);
            }
            return Some(TinyBlockSuperoptRewriteRejection::CounterexampleModel);
        }

        if self.cost_model.delta_cycles
            != signed_cost_delta(
                self.cost_model.original_cost_cycles,
                self.cost_model.replacement_cost_cycles,
            )
        {
            return Some(TinyBlockSuperoptRewriteRejection::CostDeltaMismatch);
        }
        if self.cost_model.replacement_cost_cycles > self.cost_model.original_cost_cycles {
            return Some(TinyBlockSuperoptRewriteRejection::CostRegression);
        }

        None
    }

    fn payload_json_map(&self) -> serde_json::Map<String, serde_json::Value> {
        let mut object = serde_json::Map::with_capacity(13);
        object.insert(
            "schema".to_owned(),
            serde_json::Value::String(self.schema.clone()),
        );
        object.insert(
            "schema_version".to_owned(),
            serde_json::Value::Number(serde_json::Number::from(u64::from(self.schema_version))),
        );
        object.insert("original".to_owned(), rewrite_identity_json(&self.original));
        object.insert(
            "replacement".to_owned(),
            rewrite_identity_json(&self.replacement),
        );
        object.insert("cost_model".to_owned(), cost_model_json(&self.cost_model));
        object.insert(
            "certificate".to_owned(),
            self.certificate
                .as_ref()
                .map_or(serde_json::Value::Null, certificate_identity_json),
        );
        object.insert(
            "counterexample_model".to_owned(),
            self.counterexample_model
                .as_ref()
                .map_or(serde_json::Value::Null, counterexample_model_json),
        );
        object.insert(
            "admission_enabled".to_owned(),
            serde_json::Value::Bool(self.admission_enabled),
        );
        object.insert(
            "disposition".to_owned(),
            serde_json::Value::String(self.disposition.as_str().to_owned()),
        );
        object.insert(
            "rejection".to_owned(),
            self.rejection.map_or(serde_json::Value::Null, |rejection| {
                serde_json::Value::String(rejection.as_str().to_owned())
            }),
        );
        object.insert(
            "diagnostic_reason".to_owned(),
            self.diagnostic_reason
                .as_ref()
                .map_or(serde_json::Value::Null, |reason| {
                    serde_json::Value::String(reason.clone())
                }),
        );
        object.insert(
            "product_install_authority".to_owned(),
            serde_json::Value::Bool(false),
        );
        object
    }
}

/// Stable data-only admission record tied to a proof-optimization certificate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RewriteAdmissionRecord {
    pub schema: String,
    pub schema_version: u32,
    /// Existing certificate citation emitted by the proof-optimization
    /// pipeline. Source/target region identity is not recomputed here.
    pub certificate: ProofOptimizationCertificateCitation,
    pub target_arch: String,
    pub source_cost_cycles: u64,
    pub target_cost_cycles: u64,
    pub expected_validation_hash: Option<String>,
    pub complete_evidence: ProofGuidedAdmissionEvidence,
    pub disposition: RewriteAdmissionDisposition,
    pub rejection: Option<RewriteAdmissionRejection>,
    /// Always false for this data-only slice.
    pub product_install_authority: bool,
    pub record_checksum: String,
}

impl RewriteAdmissionRecord {
    /// Build and validate a data-only admission record from an existing
    /// proof-optimization certificate citation.
    pub fn from_certificate_citation(
        certificate: ProofOptimizationCertificateCitation,
        target_arch: impl Into<String>,
        source_cost_cycles: u64,
        target_cost_cycles: u64,
        expected_validation_hash: Option<String>,
    ) -> Self {
        Self::from_complete_evidence(
            certificate,
            target_arch,
            source_cost_cycles,
            target_cost_cycles,
            expected_validation_hash,
            ProofGuidedAdmissionEvidence::default(),
        )
    }

    /// Build and validate a data-only admission record with the complete
    /// #800 admission evidence packet.
    pub fn from_complete_evidence(
        certificate: ProofOptimizationCertificateCitation,
        target_arch: impl Into<String>,
        source_cost_cycles: u64,
        target_cost_cycles: u64,
        expected_validation_hash: Option<String>,
        complete_evidence: ProofGuidedAdmissionEvidence,
    ) -> Self {
        let mut record = Self {
            schema: REWRITE_ADMISSION_RECORD_SCHEMA.to_owned(),
            schema_version: REWRITE_ADMISSION_RECORD_SCHEMA_VERSION,
            certificate,
            target_arch: target_arch.into(),
            source_cost_cycles,
            target_cost_cycles,
            expected_validation_hash,
            complete_evidence,
            disposition: RewriteAdmissionDisposition::Reject,
            rejection: None,
            product_install_authority: false,
            record_checksum: String::new(),
        };

        record.recompute_disposition();
        record.record_checksum = record.canonical_record_checksum();
        record
    }

    /// True when the record grants product install authority. This S3 slice
    /// never does.
    pub fn grants_product_install_authority(&self) -> bool {
        false
    }

    /// Recompute the fail-closed disposition from the current record contents.
    pub fn recompute_disposition(&mut self) {
        self.product_install_authority = false;
        self.rejection = self.first_rejection();
        self.disposition = if self.rejection.is_none() {
            RewriteAdmissionDisposition::AdmitNonPromoting
        } else {
            RewriteAdmissionDisposition::Reject
        };
    }

    /// Validate the record including its deterministic checksum.
    pub fn validate(&self) -> Result<(), RewriteAdmissionRejection> {
        if self.record_checksum != self.canonical_record_checksum() {
            return Err(RewriteAdmissionRejection::ChecksumMismatch);
        }
        if self.product_install_authority || self.grants_product_install_authority() {
            return Err(RewriteAdmissionRejection::UnsupportedTargetArch);
        }
        if let Some(rejection) = self.first_rejection() {
            return Err(rejection);
        }
        Ok(())
    }

    /// Deterministic JSON for the full record, including `record_checksum`.
    pub fn stable_json(&self) -> String {
        self.to_json_value().to_string()
    }

    /// Deterministic JSON object for the full record.
    pub fn to_json_value(&self) -> serde_json::Value {
        let mut object = self.payload_json_map();
        object.insert(
            "record_checksum".to_owned(),
            serde_json::Value::String(self.record_checksum.clone()),
        );
        serde_json::Value::Object(object)
    }

    /// Deterministic checksum over the record payload excluding
    /// `record_checksum`.
    pub fn canonical_record_checksum(&self) -> String {
        format!(
            "sha256:{}",
            sha256_hex(self.canonical_payload_json().as_bytes())
        )
    }

    /// Deterministic JSON payload used as the checksum input.
    pub fn canonical_payload_json(&self) -> String {
        serde_json::Value::Object(self.payload_json_map()).to_string()
    }

    fn first_rejection(&self) -> Option<RewriteAdmissionRejection> {
        if self.target_arch != "aarch64" {
            return Some(RewriteAdmissionRejection::UnsupportedTargetArch);
        }
        if citation_certificate_identity_missing(&self.certificate) {
            return Some(RewriteAdmissionRejection::MissingCertificateIdentity);
        }
        if citation_transform_identity_missing(&self.certificate) {
            return Some(RewriteAdmissionRejection::MissingTransformIdentity);
        }
        if missing_required_text(&self.certificate.source_region_hash) {
            return Some(RewriteAdmissionRejection::MissingSourceRegionHash);
        }
        if missing_required_text(&self.certificate.target_region_hash) {
            return Some(RewriteAdmissionRejection::MissingTargetRegionHash);
        }
        if citation_has_rejected_evidence(&self.certificate) {
            return Some(RewriteAdmissionRejection::RejectedCertificateEvidence);
        }
        if self.certificate.consumed_facts.is_empty() {
            return Some(RewriteAdmissionRejection::MissingConsumedProofFact);
        }
        if self
            .expected_validation_hash
            .as_deref()
            .is_some_and(|expected| expected != self.certificate.validation_hash)
        {
            return Some(RewriteAdmissionRejection::ValidationHashMismatch);
        }
        if missing_required_text(&self.complete_evidence.manifest_hash) {
            return Some(RewriteAdmissionRejection::MissingManifestHash);
        }
        if missing_required_text(&self.complete_evidence.runtime_status_contract) {
            return Some(RewriteAdmissionRejection::MissingRuntimeStatusContract);
        }
        if missing_required_text(&self.complete_evidence.replay_artifact_root) {
            return Some(RewriteAdmissionRejection::MissingReplayArtifactRoot);
        }
        if missing_required_text(&self.complete_evidence.telemetry_counter_family)
            || self
                .complete_evidence
                .telemetry_useful_native_applications
                .is_none()
        {
            return Some(RewriteAdmissionRejection::MissingTelemetryUsefulNativeCounter);
        }
        if missing_required_text(&self.complete_evidence.rollback_disable_knob) {
            return Some(RewriteAdmissionRejection::MissingRollbackDisableKnob);
        }
        if self.target_cost_cycles >= self.source_cost_cycles {
            return Some(RewriteAdmissionRejection::UnprofitableCost);
        }
        None
    }

    fn payload_json_map(&self) -> serde_json::Map<String, serde_json::Value> {
        let mut object = serde_json::Map::with_capacity(10);
        object.insert(
            "schema".to_owned(),
            serde_json::Value::String(self.schema.clone()),
        );
        object.insert(
            "schema_version".to_owned(),
            serde_json::Value::Number(serde_json::Number::from(u64::from(self.schema_version))),
        );
        object.insert("certificate".to_owned(), self.certificate.to_json_value());
        object.insert(
            "target_arch".to_owned(),
            serde_json::Value::String(self.target_arch.clone()),
        );
        object.insert(
            "source_cost_cycles".to_owned(),
            serde_json::Value::Number(serde_json::Number::from(self.source_cost_cycles)),
        );
        object.insert(
            "target_cost_cycles".to_owned(),
            serde_json::Value::Number(serde_json::Number::from(self.target_cost_cycles)),
        );
        object.insert(
            "expected_validation_hash".to_owned(),
            self.expected_validation_hash
                .as_ref()
                .map_or(serde_json::Value::Null, |hash| {
                    serde_json::Value::String(hash.clone())
                }),
        );
        object.insert(
            "complete_evidence".to_owned(),
            self.complete_evidence_json_value(),
        );
        object.insert(
            "disposition".to_owned(),
            serde_json::Value::String(self.disposition.as_str().to_owned()),
        );
        object.insert(
            "rejection".to_owned(),
            self.rejection.map_or(serde_json::Value::Null, |rejection| {
                serde_json::Value::String(rejection.as_str().to_owned())
            }),
        );
        object.insert(
            "product_install_authority".to_owned(),
            serde_json::Value::Bool(false),
        );
        object
    }

    fn complete_evidence_json_value(&self) -> serde_json::Value {
        let mut object = serde_json::Map::with_capacity(6);
        object.insert(
            "manifest_hash".to_owned(),
            serde_json::Value::String(self.complete_evidence.manifest_hash.clone()),
        );
        object.insert(
            "runtime_status_contract".to_owned(),
            serde_json::Value::String(self.complete_evidence.runtime_status_contract.clone()),
        );
        object.insert(
            "replay_artifact_root".to_owned(),
            serde_json::Value::String(self.complete_evidence.replay_artifact_root.clone()),
        );
        object.insert(
            "telemetry_counter_family".to_owned(),
            serde_json::Value::String(self.complete_evidence.telemetry_counter_family.clone()),
        );
        object.insert(
            "telemetry_useful_native_applications".to_owned(),
            self.complete_evidence
                .telemetry_useful_native_applications
                .map_or(serde_json::Value::Null, |count| {
                    serde_json::Value::Number(serde_json::Number::from(count))
                }),
        );
        object.insert(
            "rollback_disable_knob".to_owned(),
            serde_json::Value::String(self.complete_evidence.rollback_disable_knob.clone()),
        );
        serde_json::Value::Object(object)
    }
}

fn rewrite_identity_json(identity: &TinyBlockSuperoptRewriteIdentity) -> serde_json::Value {
    let mut object = serde_json::Map::with_capacity(2);
    object.insert(
        "identity".to_owned(),
        serde_json::Value::String(identity.identity.clone()),
    );
    object.insert(
        "sha256".to_owned(),
        serde_json::Value::String(identity.sha256.clone()),
    );
    serde_json::Value::Object(object)
}

fn certificate_identity_json(
    certificate: &TinyBlockSuperoptCertificateIdentity,
) -> serde_json::Value {
    let mut object = serde_json::Map::with_capacity(2);
    object.insert(
        "identity".to_owned(),
        serde_json::Value::String(certificate.identity.clone()),
    );
    object.insert(
        "sha256".to_owned(),
        serde_json::Value::String(certificate.sha256.clone()),
    );
    serde_json::Value::Object(object)
}

fn counterexample_model_json(
    counterexample: &TinyBlockSuperoptCounterexampleModel,
) -> serde_json::Value {
    let mut object = serde_json::Map::with_capacity(2);
    object.insert(
        "identity".to_owned(),
        serde_json::Value::String(counterexample.identity.clone()),
    );
    object.insert(
        "sha256".to_owned(),
        serde_json::Value::String(counterexample.sha256.clone()),
    );
    serde_json::Value::Object(object)
}

fn cost_model_json(cost_model: &TinyBlockSuperoptCostModel) -> serde_json::Value {
    let mut object = serde_json::Map::with_capacity(3);
    object.insert(
        "original_cost_cycles".to_owned(),
        serde_json::Value::Number(serde_json::Number::from(cost_model.original_cost_cycles)),
    );
    object.insert(
        "replacement_cost_cycles".to_owned(),
        serde_json::Value::Number(serde_json::Number::from(cost_model.replacement_cost_cycles)),
    );
    object.insert(
        "delta_cycles".to_owned(),
        serde_json::Value::Number(serde_json::Number::from(cost_model.delta_cycles)),
    );
    serde_json::Value::Object(object)
}

fn malformed_rewrite_identity(identity: &TinyBlockSuperoptRewriteIdentity) -> bool {
    missing_required_text(&identity.identity)
        || missing_required_text(&identity.sha256)
        || malformed_stable_identity(&identity.identity)
        || malformed_sha256(&identity.sha256)
}

fn malformed_counterexample_model(counterexample: &TinyBlockSuperoptCounterexampleModel) -> bool {
    missing_required_text(&counterexample.identity)
        || missing_required_text(&counterexample.sha256)
        || malformed_stable_identity(&counterexample.identity)
        || malformed_sha256(&counterexample.sha256)
}

fn citation_certificate_identity_missing(citation: &ProofOptimizationCertificateCitation) -> bool {
    missing_required_text(&citation.function_name)
        || missing_required_text(&citation.certificate_id)
        || missing_required_text(&citation.proof_hash)
        || missing_required_text(&citation.validation_hash)
}

fn citation_transform_identity_missing(citation: &ProofOptimizationCertificateCitation) -> bool {
    missing_required_text(&citation.transform_name) || citation.transform_version == 0
}

fn citation_has_rejected_evidence(citation: &ProofOptimizationCertificateCitation) -> bool {
    citation.status != "applied"
        || citation.rejection_code.is_some()
        || citation.rejection_fact.is_some()
        || citation.rejection_detail.is_some()
}

fn missing_required_text(value: &str) -> bool {
    value.trim().is_empty()
}

fn malformed_stable_identity(value: &str) -> bool {
    value.trim() != value
        || value
            .chars()
            .any(|ch| ch.is_control() || ch.is_whitespace())
}

fn malformed_precondition_gap(value: &str) -> bool {
    missing_required_text(value) || value.chars().any(char::is_control)
}

fn malformed_sha256(value: &str) -> bool {
    let Some(hex) = value.strip_prefix("sha256:") else {
        return true;
    };
    hex.len() != 64
        || !hex
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn signed_cost_delta(original_cost_cycles: u64, replacement_cost_cycles: u64) -> i64 {
    if replacement_cost_cycles >= original_cost_cycles {
        let delta = replacement_cost_cycles - original_cost_cycles;
        i64::try_from(delta).unwrap_or(i64::MAX)
    } else {
        let delta = original_cost_cycles - replacement_cost_cycles;
        -i64::try_from(delta).unwrap_or(i64::MAX)
    }
}
