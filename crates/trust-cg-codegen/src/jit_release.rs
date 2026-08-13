// trust-cg-codegen/jit_release.rs - Release/replay bundle metadata
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Data model for Phase 6 release/replay bundle manifests.
//!
//! The bundle manifest is deliberately metadata-only: it binds paths and hashes
//! for files produced by consumer-visible compile, proof, telemetry, release,
//! replay, and gate-result flows without owning those file formats.

use std::collections::{BTreeMap, BTreeSet};

use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use crate::jit_contract::{
    ArtifactChecksum, HOST_JIT_TARGET_FEATURE_PROFILE_METADATA_PREFIX,
    TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_ROW_COUNT_KEY,
    TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA_KEY,
    TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA_VERSION_KEY,
    TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SHA256_KEY,
    TRUST_IR_HARDWARE_VECTOR_CONTRACT_SET_NAME_KEY,
    TRUST_IR_HARDWARE_VECTOR_CONTRACT_TARGET_FAMILY_KEY,
};
use crate::jit_install_gate::{
    NATIVE_INSTALL_GATE_PACKET_SCHEMA, NATIVE_INSTALL_GATE_PACKET_SCHEMA_VERSION,
    NativeInstallGatePacket, NativeInstallGateRejectionCode, NativeInstallGateRevalidationInput,
    NativeInstallGateSurface, TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE,
    TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA, validate_native_install_gate_packet,
    validate_native_install_gate_packet_with_current,
};
use crate::pipeline::ProofOptimizationCertificateCitation;

/// Stable schema tag for Phase 6 release/replay bundle manifests.
pub const JIT_RELEASE_BUNDLE_SCHEMA: &str = "trust-cg.phase6.release_replay_bundle.v1";

/// Stable numeric schema version for [`ReleaseReplayBundleMetadata`].
pub const JIT_RELEASE_BUNDLE_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for source-lock metadata bound into release bundles.
pub const RELEASE_SOURCE_LOCK_METADATA_SCHEMA: &str = "trust-cg.release.source_lock_metadata.v1";

/// Stable numeric schema version for source-lock metadata bindings.
pub const RELEASE_SOURCE_LOCK_METADATA_SCHEMA_VERSION: u32 = 1;

/// Metadata key for the release source-lock metadata schema tag.
pub const RELEASE_SOURCE_LOCK_SCHEMA_KEY: &str = "source_lock_schema";

/// Metadata key for the release source-lock metadata schema version.
pub const RELEASE_SOURCE_LOCK_SCHEMA_VERSION_KEY: &str = "source_lock_schema_version";

/// Metadata key for the release source-lock file SHA-256.
pub const RELEASE_SOURCE_LOCK_SHA256_KEY: &str = "source_lock_sha256";

/// Metadata key for the Trust Codegen source revision.
pub const RELEASE_SOURCE_LOCK_TRUST_CG_REVISION_KEY: &str = "trust_cg_revision";

/// Metadata key for the trust_ir source revision.
pub const RELEASE_SOURCE_LOCK_TRUST_IR_REVISION_KEY: &str = "trust_ir_revision";

/// Metadata key for the ay downstream source revision.
pub const RELEASE_SOURCE_LOCK_AY_REVISION_KEY: &str = "ay_revision";

/// Metadata key for the TY downstream source revision.
pub const RELEASE_SOURCE_LOCK_TY_REVISION_KEY: &str = "ty_revision";

/// Metadata key for the consumer source SHA-256.
pub const RELEASE_SOURCE_SHA256_KEY: &str = "source_sha256";

/// Metadata key for the canonical trust_ir SHA-256.
pub const RELEASE_TRUST_IR_SHA256_KEY: &str = "trust_ir_sha256";

/// Metadata key for the native payload SHA-256.
pub const RELEASE_NATIVE_PAYLOAD_SHA256_KEY: &str = "native_payload_sha256";

/// Stable release metadata schema for TY native-fused replay bindings.
pub const RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA: &str =
    "trust-cg.release.ty_native_fused_replay_metadata.v1";

/// Stable release metadata schema version for TY native-fused replay bindings.
pub const RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA_VERSION: u32 = 1;

/// Metadata key for the TY native-fused release/replay schema tag.
pub const RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA_KEY: &str = "ty.native_fused.release.schema";

/// Metadata key for the TY native-fused release/replay schema version.
pub const RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA_VERSION_KEY: &str =
    "ty.native_fused.release.schema_version";

/// Metadata key for the TY native-fused release/replay manifest checksum.
pub const RELEASE_TY_NATIVE_FUSED_REPLAY_MANIFEST_CHECKSUM_KEY: &str =
    "ty.native_fused.release.manifest_checksum";

/// Metadata key for the TY native-fused release/replay replay root.
pub const RELEASE_TY_NATIVE_FUSED_REPLAY_ROOT_SHA256_KEY: &str =
    "ty.native_fused.release.replay_root_sha256";

/// Metadata key for the TY native-fused release/replay replay identity record.
pub const RELEASE_TY_NATIVE_FUSED_REPLAY_RECORD_SHA256_KEY: &str =
    "ty.native_fused.release.replay_record_sha256";

/// Metadata key for the TY native-fused release/replay telemetry event.
pub const RELEASE_TY_NATIVE_FUSED_REPLAY_TELEMETRY_EVENT_ID_KEY: &str =
    "ty.native_fused.release.telemetry_event_id";

/// Metadata key for the TY native-fused release/replay telemetry record.
pub const RELEASE_TY_NATIVE_FUSED_REPLAY_TELEMETRY_RECORD_SHA256_KEY: &str =
    "ty.native_fused.release.telemetry_record_sha256";

/// Metadata key for the TY native-fused release/replay install-gate packet.
pub const RELEASE_TY_NATIVE_FUSED_REPLAY_GATE_PACKET_HASH_KEY: &str =
    "ty.native_fused.release.gate_packet_hash";

/// Metadata key for the TY native-fused release/replay proof validation hash.
pub const RELEASE_TY_NATIVE_FUSED_REPLAY_PROOF_VALIDATION_SHA256_KEY: &str =
    "ty.native_fused.release.proof_validation_sha256";

/// Metadata key for the TY native-fused proof-optimization function identity.
pub const RELEASE_TY_NATIVE_FUSED_PROOF_OPT_FUNCTION_NAME_KEY: &str =
    "ty.native_fused.release.proof_optimization.function_name";

/// Metadata key for the TY native-fused proof-optimization certificate identity.
pub const RELEASE_TY_NATIVE_FUSED_PROOF_OPT_CERTIFICATE_ID_KEY: &str =
    "ty.native_fused.release.proof_optimization.certificate_id";

/// Metadata key for the TY native-fused proof-optimization source-region identity.
pub const RELEASE_TY_NATIVE_FUSED_PROOF_OPT_SOURCE_REGION_HASH_KEY: &str =
    "ty.native_fused.release.proof_optimization.source_region_hash";

/// Metadata key for the TY native-fused proof-optimization target-region identity.
pub const RELEASE_TY_NATIVE_FUSED_PROOF_OPT_TARGET_REGION_HASH_KEY: &str =
    "ty.native_fused.release.proof_optimization.target_region_hash";

/// Stable schema tag for release proof-optimization citation summaries.
pub const RELEASE_PROOF_OPTIMIZATION_CITATION_SUMMARY_SCHEMA: &str =
    "trust-cg.release.proof_optimization_citation_summary.v1";

/// Stable numeric schema version for release proof-optimization citation summaries.
pub const RELEASE_PROOF_OPTIMIZATION_CITATION_SUMMARY_SCHEMA_VERSION: u32 = 1;

const RELEASE_TY_NATIVE_FUSED_PROOF_OPT_TRANSFORM_NAME: &str = "ty-native-fused-parent-loop";
const RELEASE_TY_NATIVE_FUSED_PROOF_OPT_TRANSFORM_VERSION: u32 = 1;
const RELEASE_TY_NATIVE_FUSED_PROOF_OPT_ADMISSION: &str = "proof-annotation+proof-facts";
const RELEASE_TY_NATIVE_FUSED_PROOF_OPT_KIND: &str = "TyNativeFusedParentLoop";

/// Stable install decision status for a release/replay bundle.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReleaseBundleInstallStatus {
    /// Bundle has complete replay metadata and all proof reports are accepted.
    Installable,
    /// Bundle has enough metadata for replay, but must not be installed.
    ReplayOnly,
    /// Bundle is missing metadata required for install or replay decisions.
    NonInstallable,
}

impl ReleaseBundleInstallStatus {
    /// Return the stable manifest/log string for this install status.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Installable => "installable",
            Self::ReplayOnly => "replay_only",
            Self::NonInstallable => "non_installable",
        }
    }
}

/// Stable release-bundle install decision code.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReleaseBundleInstallCode {
    /// Bundle is installable.
    Installable,
    /// Bundle schema tag or schema version is not supported.
    UnsupportedSchema,
    /// Bundle consumer is not supported by the install validator.
    UnsupportedConsumer,
    /// Required replay metadata was absent or incomplete.
    MissingReplayMetadata,
    /// No proof reports were bound into the bundle.
    MissingProofReports,
    /// A proof report binding was absent or incomplete.
    MissingProofReportMetadata,
    /// A proof report did not record a verdict.
    MissingProofVerdict,
    /// A proof report recorded a rejected verdict.
    ProofRejected,
    /// A proof report recorded a timeout verdict.
    ProofTimeout,
    /// A proof report verdict was not accepted by the install validator.
    ProofVerdictNotAccepted,
    /// Native install gate packet metadata is absent.
    MissingGateMetadata,
    /// Native install gate packet metadata does not match this bundle.
    GateMetadataMismatch,
    /// Source-lock metadata required for release install is absent.
    MissingSourceLockMetadata,
    /// Source-lock metadata does not match this bundle or the install gate packet.
    SourceLockMetadataMismatch,
    /// Native install gate packet is present but did not authorize release install.
    GateRejected,
    /// Native install gate packet was stale at release-restore time.
    GateStaleInvalidation,
    /// Native install gate packet was revoked at release-restore time.
    GateRevoked,
    /// Native install gate packet was blocked by a kill switch at release-restore time.
    GateKillSwitch,
    /// TY native-fused replay lacks a proof-optimization certificate citation.
    MissingProofOptimizationCitation,
    /// TY native-fused replay citation does not consume every required proof fact.
    ProofOptimizationCitationMissingFact,
    /// TY native-fused replay citation is bound to a stale proof validation hash.
    ProofOptimizationValidationHashMismatch,
}

impl ReleaseBundleInstallCode {
    /// Return the stable manifest/log string for this decision code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Installable => "installable",
            Self::UnsupportedSchema => "unsupported_schema",
            Self::UnsupportedConsumer => "unsupported_consumer",
            Self::MissingReplayMetadata => "missing_replay_metadata",
            Self::MissingProofReports => "missing_proof_reports",
            Self::MissingProofReportMetadata => "missing_proof_report_metadata",
            Self::MissingProofVerdict => "missing_proof_verdict",
            Self::ProofRejected => "proof_rejected",
            Self::ProofTimeout => "proof_timeout",
            Self::ProofVerdictNotAccepted => "proof_verdict_not_accepted",
            Self::MissingGateMetadata => "missing_gate_metadata",
            Self::GateMetadataMismatch => "gate_metadata_mismatch",
            Self::MissingSourceLockMetadata => "missing_source_lock_metadata",
            Self::SourceLockMetadataMismatch => "source_lock_metadata_mismatch",
            Self::GateRejected => "gate_rejected",
            Self::GateStaleInvalidation => "gate_stale_invalidation",
            Self::GateRevoked => "gate_revoked",
            Self::GateKillSwitch => "gate_kill_switch",
            Self::MissingProofOptimizationCitation => "missing_proof_optimization_citation",
            Self::ProofOptimizationCitationMissingFact => {
                "proof_optimization_citation_missing_fact"
            }
            Self::ProofOptimizationValidationHashMismatch => {
                "proof_optimization_validation_hash_mismatch"
            }
        }
    }
}

/// Metadata-only install decision for a release/replay bundle.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ReleaseBundleInstallDecision {
    /// Stable install status.
    pub status: ReleaseBundleInstallStatus,
    /// Stable decision code.
    pub code: ReleaseBundleInstallCode,
}

impl ReleaseBundleInstallDecision {
    /// Create a stable install decision.
    pub const fn new(status: ReleaseBundleInstallStatus, code: ReleaseBundleInstallCode) -> Self {
        Self { status, code }
    }

    /// Create an installable decision.
    pub const fn installable() -> Self {
        Self::new(
            ReleaseBundleInstallStatus::Installable,
            ReleaseBundleInstallCode::Installable,
        )
    }

    /// Create a replay-only decision.
    pub const fn replay_only(code: ReleaseBundleInstallCode) -> Self {
        Self::new(ReleaseBundleInstallStatus::ReplayOnly, code)
    }

    /// Create a non-installable decision.
    pub const fn non_installable(code: ReleaseBundleInstallCode) -> Self {
        Self::new(ReleaseBundleInstallStatus::NonInstallable, code)
    }

    /// Return true when the bundle may be installed.
    pub const fn is_installable(self) -> bool {
        matches!(self.status, ReleaseBundleInstallStatus::Installable)
    }

    /// Convert to the stable bundle JSON representation.
    ///
    /// Keep decision serialization private to release bundles so an
    /// `installable` decision cannot be emitted without validating the bound
    /// manifest and proof metadata first.
    fn to_json_value(self) -> Value {
        json!({
            "status": self.status.as_str(),
            "code": self.code.as_str(),
            "installable": self.is_installable(),
        })
    }
}

/// Native install gate packet metadata carried by a release/replay bundle.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReleaseNativeInstallGateMetadata {
    /// Shared native install gate packet.
    pub packet: NativeInstallGatePacket,
    /// SHA-256 of the telemetry file whose row produced the gate decision.
    pub telemetry_sha256: String,
}

impl ReleaseNativeInstallGateMetadata {
    /// Create release metadata from a shared native install gate packet.
    pub fn new(packet: NativeInstallGatePacket, telemetry_sha256: impl Into<String>) -> Self {
        Self {
            packet,
            telemetry_sha256: telemetry_sha256.into(),
        }
    }

    /// Convert to the stable bundle JSON representation.
    pub fn to_json_value(&self) -> Value {
        json!({
            "schema": self.packet.schema,
            "schema_version": self.packet.schema_version,
            "gate_issue": self.packet.gate_issue,
            "design_issue": self.packet.design_issue,
            "consumer": self.packet.consumer,
            "consumer_mode": self.packet.consumer_mode,
            "surface": self.packet.surface.as_str(),
            "disposition": self.packet.disposition.as_str(),
            "rejection_code": self.packet.rejection_code.map(NativeInstallGateRejectionCode::as_str),
            "install_authority": self.packet.install_authority.as_str(),
            "requested_authority": self.packet.requested_authority.as_str(),
            "packet_hash": self.packet.packet_hash.to_string(),
            "manifest_checksum": self.packet.artifact.manifest_checksum.to_string(),
            "proof_tv_checksum": self.packet.validation.proof_report_sha256,
            "invalidation_checksum": self.packet.artifact.invalidation_checksum.to_string(),
            "artifact_metadata": self.packet.artifact.manifest_metadata.clone(),
            "telemetry_checksum": self.telemetry_sha256,
            "telemetry_event_id": self.packet.telemetry.as_ref().map(|telemetry| telemetry.event_id.as_str()),
            "telemetry_record_sha256": self.packet.telemetry.as_ref().map(|telemetry| telemetry.record_sha256.as_str()),
            "counter_scope": self.packet.telemetry.as_ref().map(|telemetry| telemetry.counter_scope.as_str()),
            "useful_native_delta": self.packet.telemetry.as_ref().map(|telemetry| telemetry.useful_native_delta).unwrap_or(0),
            "replay_root_sha256": self.packet.replay_binding.replay_root_sha256,
            "replay_record_sha256": self.packet.replay_identity.as_ref().map(|replay| replay.replay_record_sha256.as_str()),
            "release_installable": self.packet.actions.release_installable,
            "useful_native_eligible": self.packet.actions.useful_native_eligible,
            "actions": {
                "expose_callable": self.packet.actions.expose_callable,
                "typed_symbol_lookup": self.packet.actions.typed_symbol_lookup,
                "insert_installable_cache": self.packet.actions.insert_installable_cache,
                "accept_installable_cache_hit": self.packet.actions.accept_installable_cache_hit,
                "release_installable": self.packet.actions.release_installable,
                "ay_registry_insert": self.packet.actions.ay_registry_insert,
                "ty_native_activate": self.packet.actions.ty_native_activate,
                "useful_native_eligible": self.packet.actions.useful_native_eligible,
            },
        })
    }
}

/// TY native-fused replay/release identity projected into bundle metadata.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReleaseTyNativeFusedReplayMetadata {
    /// Deterministic artifact manifest checksum.
    pub manifest_checksum: ArtifactChecksum,
    /// Stable replay root SHA-256 from the install gate replay identity.
    pub replay_root_sha256: String,
    /// Canonical replay identity record SHA-256.
    pub replay_record_sha256: String,
    /// Install-gate telemetry event id.
    pub telemetry_event_id: String,
    /// Canonical install-gate telemetry record SHA-256.
    pub telemetry_record_sha256: String,
    /// Canonical install-gate packet hash.
    pub gate_packet_hash: ArtifactChecksum,
    /// Proof/validation report SHA-256 consumed by the install gate.
    pub proof_validation_sha256: String,
}

impl ReleaseTyNativeFusedReplayMetadata {
    /// Build release metadata from install-gate packet bindings when the packet
    /// is for TY native-fused parent-loop release.
    pub fn from_install_gate(install_gate: &ReleaseNativeInstallGateMetadata) -> Option<Self> {
        let packet = &install_gate.packet;
        if packet.consumer != "ty"
            || packet.consumer_mode != TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE
            || packet.surface != NativeInstallGateSurface::ReleaseBundle
        {
            return None;
        }
        let replay_identity = packet.replay_identity.as_ref()?;
        let telemetry = packet.telemetry.as_ref()?;
        let proof_validation_sha256 = packet.validation.proof_report_sha256.clone()?;
        Some(Self {
            manifest_checksum: packet.artifact.manifest_checksum,
            replay_root_sha256: replay_identity.replay_root_sha256.clone(),
            replay_record_sha256: replay_identity.replay_record_sha256.clone(),
            telemetry_event_id: telemetry.event_id.clone(),
            telemetry_record_sha256: telemetry.record_sha256.clone(),
            gate_packet_hash: packet.packet_hash,
            proof_validation_sha256,
        })
    }

    /// Return deterministic key/value metadata for the release bundle map.
    pub fn to_metadata_entries(&self) -> BTreeMap<String, String> {
        BTreeMap::from([
            (
                RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA_KEY.to_owned(),
                RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA.to_owned(),
            ),
            (
                RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA_VERSION_KEY.to_owned(),
                RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA_VERSION.to_string(),
            ),
            (
                RELEASE_TY_NATIVE_FUSED_REPLAY_MANIFEST_CHECKSUM_KEY.to_owned(),
                self.manifest_checksum.to_string(),
            ),
            (
                RELEASE_TY_NATIVE_FUSED_REPLAY_ROOT_SHA256_KEY.to_owned(),
                self.replay_root_sha256.clone(),
            ),
            (
                RELEASE_TY_NATIVE_FUSED_REPLAY_RECORD_SHA256_KEY.to_owned(),
                self.replay_record_sha256.clone(),
            ),
            (
                RELEASE_TY_NATIVE_FUSED_REPLAY_TELEMETRY_EVENT_ID_KEY.to_owned(),
                self.telemetry_event_id.clone(),
            ),
            (
                RELEASE_TY_NATIVE_FUSED_REPLAY_TELEMETRY_RECORD_SHA256_KEY.to_owned(),
                self.telemetry_record_sha256.clone(),
            ),
            (
                RELEASE_TY_NATIVE_FUSED_REPLAY_GATE_PACKET_HASH_KEY.to_owned(),
                self.gate_packet_hash.to_string(),
            ),
            (
                RELEASE_TY_NATIVE_FUSED_REPLAY_PROOF_VALIDATION_SHA256_KEY.to_owned(),
                self.proof_validation_sha256.clone(),
            ),
        ])
    }

    /// Insert deterministic key/value bindings into a bundle metadata map.
    pub fn bind_into_metadata(&self, metadata: &mut BTreeMap<String, String>) {
        metadata.extend(self.to_metadata_entries());
    }
}

/// Deterministic summary derived from proof-optimization certificate citations.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReleaseProofOptimizationCitationSummary {
    /// Total proof-optimization certificates cited by the bundle.
    pub certificate_count: usize,
    /// Distinct functions that cite at least one proof-optimization certificate.
    pub function_count: usize,
    /// Certificates with `status == "applied"`.
    pub applied_count: usize,
    /// Certificates with `status == "rejected"`.
    pub rejected_count: usize,
    /// Distinct function names in deterministic order.
    pub functions: Vec<String>,
    /// Citation counts by certificate status.
    pub status_counts: BTreeMap<String, usize>,
    /// Citation counts by optimization kind.
    pub kind_counts: BTreeMap<String, usize>,
    /// Citation counts by `transform_name@transform_version`.
    pub transform_counts: BTreeMap<String, usize>,
    /// Citation counts by consumed proof fact name.
    pub consumed_fact_counts: BTreeMap<String, usize>,
    /// Citation counts by rejection code.
    pub rejection_code_counts: BTreeMap<String, usize>,
}

impl ReleaseProofOptimizationCitationSummary {
    /// Build a deterministic summary from canonical certificate citations.
    pub fn from_certificates(certificates: &[ProofOptimizationCertificateCitation]) -> Self {
        let mut functions = BTreeSet::new();
        let mut status_counts = BTreeMap::new();
        let mut kind_counts = BTreeMap::new();
        let mut transform_counts = BTreeMap::new();
        let mut consumed_fact_counts = BTreeMap::new();
        let mut rejection_code_counts = BTreeMap::new();
        let mut applied_count = 0;
        let mut rejected_count = 0;

        for certificate in certificates {
            functions.insert(certificate.function_name.clone());
            increment_count(&mut status_counts, &certificate.status);
            increment_count(&mut kind_counts, &certificate.kind);
            increment_count(
                &mut transform_counts,
                &format!(
                    "{}@{}",
                    certificate.transform_name, certificate.transform_version
                ),
            );

            if certificate.status == "applied" {
                applied_count += 1;
            }
            if certificate.status == "rejected" {
                rejected_count += 1;
            }

            for fact in &certificate.consumed_facts {
                increment_count(&mut consumed_fact_counts, &fact.name);
            }
            if let Some(code) = certificate.rejection_code.as_deref() {
                increment_count(&mut rejection_code_counts, code);
            }
        }

        let functions: Vec<_> = functions.into_iter().collect();
        Self {
            certificate_count: certificates.len(),
            function_count: functions.len(),
            applied_count,
            rejected_count,
            functions,
            status_counts,
            kind_counts,
            transform_counts,
            consumed_fact_counts,
            rejection_code_counts,
        }
    }

    /// Convert to the stable bundle JSON representation.
    pub fn to_json_value(&self) -> Value {
        json!({
            "schema": RELEASE_PROOF_OPTIMIZATION_CITATION_SUMMARY_SCHEMA,
            "schema_version": RELEASE_PROOF_OPTIMIZATION_CITATION_SUMMARY_SCHEMA_VERSION,
            "certificate_count": self.certificate_count,
            "function_count": self.function_count,
            "applied_count": self.applied_count,
            "rejected_count": self.rejected_count,
            "functions": self.functions,
            "status_counts": self.status_counts,
            "kind_counts": self.kind_counts,
            "transform_counts": self.transform_counts,
            "consumed_fact_counts": self.consumed_fact_counts,
            "rejection_code_counts": self.rejection_code_counts,
        })
    }
}

fn increment_count(counts: &mut BTreeMap<String, usize>, key: &str) {
    *counts.entry(key.to_owned()).or_insert(0) += 1;
}

/// Path plus SHA-256 binding for one file inside a release/replay bundle.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReleaseBundleFileReference {
    /// Bundle-relative path.
    pub path: String,
    /// SHA-256 digest for the referenced file bytes.
    pub sha256: String,
}

impl ReleaseBundleFileReference {
    /// Create a file reference from a bundle-relative path and SHA-256 digest.
    pub fn new(path: impl Into<String>, sha256: impl Into<String>) -> Self {
        Self {
            path: path.into(),
            sha256: sha256.into(),
        }
    }

    /// Convert to the stable bundle JSON representation.
    pub fn to_json_value(&self) -> Value {
        json!({
            "path": self.path,
            "sha256": self.sha256,
        })
    }
}

/// Artifact manifest reference with both file and deterministic manifest hashes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReleaseArtifactManifestReference {
    /// Bundle-relative manifest path.
    pub path: String,
    /// SHA-256 digest for the serialized manifest file bytes.
    pub sha256: String,
    /// Schema version recorded inside the artifact manifest.
    pub schema_version: u32,
    /// Deterministic Trust Codegen artifact manifest checksum.
    pub manifest_checksum: ArtifactChecksum,
}

impl ReleaseArtifactManifestReference {
    /// Create an artifact manifest reference.
    pub fn new(
        path: impl Into<String>,
        sha256: impl Into<String>,
        schema_version: u32,
        manifest_checksum: ArtifactChecksum,
    ) -> Self {
        Self {
            path: path.into(),
            sha256: sha256.into(),
            schema_version,
            manifest_checksum,
        }
    }

    /// Convert to the stable bundle JSON representation.
    pub fn to_json_value(&self) -> Value {
        json!({
            "manifest_checksum": self.manifest_checksum.to_string(),
            "path": self.path,
            "schema_version": self.schema_version,
            "sha256": self.sha256,
        })
    }
}

/// Proof report reference with optional policy metadata.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReleaseProofReportReference {
    /// Bundle file reference for the proof report.
    pub file: ReleaseBundleFileReference,
    /// Proof policy name applied to this report.
    pub policy: Option<String>,
    /// Proof or rejection verdict.
    pub verdict: Option<String>,
    /// Solver or verifier route.
    pub solver: Option<String>,
    /// Obligation-set identifier or hash.
    pub obligation_set: Option<String>,
    /// Proof timeout budget, when the report records one.
    pub timeout_ms: Option<u64>,
}

impl ReleaseProofReportReference {
    /// Create a proof report reference from a path and SHA-256 digest.
    pub fn new(path: impl Into<String>, sha256: impl Into<String>) -> Self {
        Self {
            file: ReleaseBundleFileReference::new(path, sha256),
            policy: None,
            verdict: None,
            solver: None,
            obligation_set: None,
            timeout_ms: None,
        }
    }

    /// Attach the proof policy name.
    pub fn with_policy(mut self, policy: impl Into<String>) -> Self {
        self.policy = Some(policy.into());
        self
    }

    /// Attach the proof or rejection verdict.
    pub fn with_verdict(mut self, verdict: impl Into<String>) -> Self {
        self.verdict = Some(verdict.into());
        self
    }

    /// Attach the solver or verifier route.
    pub fn with_solver(mut self, solver: impl Into<String>) -> Self {
        self.solver = Some(solver.into());
        self
    }

    /// Attach the obligation-set identifier or hash.
    pub fn with_obligation_set(mut self, obligation_set: impl Into<String>) -> Self {
        self.obligation_set = Some(obligation_set.into());
        self
    }

    /// Attach the proof timeout budget.
    pub const fn with_timeout_ms(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = Some(timeout_ms);
        self
    }

    fn stable_key(
        &self,
    ) -> (
        &str,
        &str,
        Option<&str>,
        Option<&str>,
        Option<&str>,
        Option<&str>,
        Option<u64>,
    ) {
        (
            self.file.path.as_str(),
            self.file.sha256.as_str(),
            self.policy.as_deref(),
            self.verdict.as_deref(),
            self.solver.as_deref(),
            self.obligation_set.as_deref(),
            self.timeout_ms,
        )
    }

    /// Convert to the stable bundle JSON representation.
    pub fn to_json_value(&self) -> Value {
        json!({
            "obligation_set": self.obligation_set,
            "path": self.file.path,
            "policy": self.policy,
            "sha256": self.file.sha256,
            "solver": self.solver,
            "timeout_ms": self.timeout_ms,
            "verdict": self.verdict,
        })
    }
}

/// Top-level release/replay bundle manifest metadata.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReleaseReplayBundleMetadata {
    /// Stable schema tag.
    pub schema: String,
    /// Stable numeric schema version.
    pub schema_version: u32,
    /// Downstream consumer name, such as `ay` or `ty`.
    pub consumer: String,
    /// Exact downstream mode that produced this bundle.
    pub consumer_mode: String,
    /// Caller-visible artifact id.
    pub artifact_id: String,
    /// Deterministic artifact manifest binding.
    pub artifact_manifest: ReleaseArtifactManifestReference,
    /// Source-lock file binding.
    pub source_lock: ReleaseBundleFileReference,
    /// Proof report bindings. Reports are sorted by path/hash in JSON output.
    pub proof_reports: Vec<ReleaseProofReportReference>,
    /// Compile telemetry file binding.
    pub telemetry: ReleaseBundleFileReference,
    /// Release package/build metadata file binding.
    pub release_package: ReleaseBundleFileReference,
    /// Replay entrypoint file binding.
    pub replay: ReleaseBundleFileReference,
    /// Gate-result file binding.
    pub gate_results: ReleaseBundleFileReference,
    /// Shared native install gate packet metadata.
    pub install_gate: Option<ReleaseNativeInstallGateMetadata>,
    /// Proof-optimization certificates cited by this release/replay bundle.
    pub proof_optimization_certificates: Vec<ProofOptimizationCertificateCitation>,
    /// Downstream extension metadata. Keys are deterministic.
    pub metadata: BTreeMap<String, String>,
}

/// Stable allow/deny decision for release/replay preflight surfaces.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReleaseReplayPreflightDecision {
    /// The preflight surface may continue.
    Allow,
    /// The preflight surface must fail closed.
    Deny,
}

impl ReleaseReplayPreflightDecision {
    /// Return the stable manifest/log string for this decision.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Allow => "allow",
            Self::Deny => "deny",
        }
    }
}

/// Stable taxonomy code for release/replay bundle preflight validation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReleaseReplayPreflightCode {
    /// Preflight passed.
    Ok,
    /// Bundle schema tag or schema version is not supported.
    UnsupportedSchema,
    /// The bundle requires an unknown consumer feature.
    UnknownRequiredFeature,
    /// A bound file reference is absent, incomplete, or missing from inputs.
    MissingBoundFile,
    /// A bound file checksum does not match the manifest.
    ChecksumMismatch,
    /// Replay report binding or file contents are absent or malformed.
    MissingReplayReport,
    /// Replay report lacks a non-empty pc map.
    MissingPcMap,
    /// Replay report lacks non-empty status entries.
    MissingStatuses,
    /// Replay report lacks non-empty symbols.
    MissingSymbols,
    /// Replay report generation is older than the bundle generation.
    StaleGeneration,
}

impl ReleaseReplayPreflightCode {
    /// Return the stable manifest/log string for this taxonomy code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Ok => "ok",
            Self::UnsupportedSchema => "unsupported_schema",
            Self::UnknownRequiredFeature => "unknown_required_feature",
            Self::MissingBoundFile => "missing_bound_file",
            Self::ChecksumMismatch => "checksum_mismatch",
            Self::MissingReplayReport => "missing_replay_report",
            Self::MissingPcMap => "missing_pc_map",
            Self::MissingStatuses => "missing_statuses",
            Self::MissingSymbols => "missing_symbols",
            Self::StaleGeneration => "stale_generation",
        }
    }
}

/// Consumer-facing preflight result for a release/replay bundle.
///
/// This is an integrity preflight API. It checks schema support, required
/// features, bound file presence/checksums, and replay report shape, but it is
/// not install authority.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReleaseReplayBundlePreflightVerdict {
    /// Whether install preflight may continue.
    pub install: ReleaseReplayPreflightDecision,
    /// Whether replay preflight may continue.
    pub replay: ReleaseReplayPreflightDecision,
    /// Whether dispatch preflight may continue.
    pub dispatch: ReleaseReplayPreflightDecision,
    /// Whether gate-result preflight may continue.
    pub gate: ReleaseReplayPreflightDecision,
    /// Stable taxonomy code for the preflight result.
    pub taxonomy_code: ReleaseReplayPreflightCode,
    /// Stable telemetry join result for downstream reducers.
    pub telemetry_join_result: String,
    /// Stable reducer route for downstream consumers.
    pub reducer_routing: String,
    /// Stable useful-native-counter decision.
    pub useful_native_counter_decision: String,
}

impl ReleaseReplayBundlePreflightVerdict {
    fn accepted(consumer: &str) -> Self {
        Self {
            install: ReleaseReplayPreflightDecision::Allow,
            replay: ReleaseReplayPreflightDecision::Allow,
            dispatch: ReleaseReplayPreflightDecision::Allow,
            gate: ReleaseReplayPreflightDecision::Allow,
            taxonomy_code: ReleaseReplayPreflightCode::Ok,
            telemetry_join_result: "joined".to_owned(),
            reducer_routing: format!("{consumer}_reducer"),
            useful_native_counter_decision: "use_native_counters".to_owned(),
        }
    }

    fn rejected(taxonomy_code: ReleaseReplayPreflightCode) -> Self {
        Self {
            install: ReleaseReplayPreflightDecision::Deny,
            replay: ReleaseReplayPreflightDecision::Deny,
            dispatch: ReleaseReplayPreflightDecision::Deny,
            gate: ReleaseReplayPreflightDecision::Deny,
            taxonomy_code,
            telemetry_join_result: "not_joined".to_owned(),
            reducer_routing: "quarantine".to_owned(),
            useful_native_counter_decision: "disable_native_counters".to_owned(),
        }
    }
}

fn non_empty(value: &str) -> bool {
    !value.trim().is_empty()
}

fn sha256_ref(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut output = String::with_capacity("sha256:".len() + digest.len() * 2);
    output.push_str("sha256:");
    for byte in digest {
        use std::fmt::Write as _;
        let _ = write!(&mut output, "{byte:02x}");
    }
    output
}

fn json_array_is_non_empty(value: Option<&Value>) -> bool {
    value
        .and_then(Value::as_array)
        .is_some_and(|items| !items.is_empty())
}

fn json_string_array_is_non_empty(value: Option<&Value>) -> bool {
    value.and_then(Value::as_array).is_some_and(|items| {
        items
            .iter()
            .any(|item| item.as_str().is_some_and(non_empty))
    })
}

fn file_ref<'a>(manifest: &'a Value, key: &str) -> Option<(&'a str, &'a str)> {
    let file = manifest.get(key)?;
    let path = file.get("path").and_then(Value::as_str)?;
    let sha256 = file.get("sha256").and_then(Value::as_str)?;
    Some((path, sha256))
}

fn proof_refs(manifest: &Value) -> Option<Vec<(&str, &str)>> {
    let reports = manifest.get("proof_reports")?.as_array()?;
    let mut refs = Vec::with_capacity(reports.len());
    for report in reports {
        let path = report.get("path").and_then(Value::as_str)?;
        let sha256 = report.get("sha256").and_then(Value::as_str)?;
        refs.push((path, sha256));
    }
    Some(refs)
}

fn checksum_matches(bytes: &[u8], expected: &str) -> bool {
    let Some(hex) = expected.strip_prefix("sha256:") else {
        return false;
    };
    hex.eq_ignore_ascii_case(sha256_ref(bytes).trim_start_matches("sha256:"))
}

fn validate_preflight_bound_file(
    files: &BTreeMap<String, Vec<u8>>,
    path: &str,
    sha256: &str,
) -> Result<(), ReleaseReplayPreflightCode> {
    if !non_empty(path) || !non_empty(sha256) {
        return Err(ReleaseReplayPreflightCode::MissingBoundFile);
    }
    let Some(bytes) = files.get(path) else {
        return Err(ReleaseReplayPreflightCode::MissingBoundFile);
    };
    if checksum_matches(bytes, sha256) {
        Ok(())
    } else {
        Err(ReleaseReplayPreflightCode::ChecksumMismatch)
    }
}

fn validate_preflight_required_features(
    manifest: &Value,
    supported_required_features: &[&str],
) -> Result<(), ReleaseReplayPreflightCode> {
    for key in ["required_features", "compat_required_features"] {
        let Some(features) = manifest.get(key) else {
            continue;
        };
        let Some(features) = features.as_array() else {
            return Err(ReleaseReplayPreflightCode::UnknownRequiredFeature);
        };
        for feature in features {
            let Some(feature) = feature.as_str() else {
                return Err(ReleaseReplayPreflightCode::UnknownRequiredFeature);
            };
            if !supported_required_features.contains(&feature) {
                return Err(ReleaseReplayPreflightCode::UnknownRequiredFeature);
            }
        }
    }
    Ok(())
}

fn validate_preflight_bound_files(
    manifest: &Value,
    files: &BTreeMap<String, Vec<u8>>,
) -> Result<(), ReleaseReplayPreflightCode> {
    let Some((path, sha256)) = file_ref(manifest, "artifact_manifest") else {
        return Err(ReleaseReplayPreflightCode::MissingBoundFile);
    };
    validate_preflight_bound_file(files, path, sha256)?;

    for key in [
        "source_lock",
        "telemetry",
        "release_package",
        "replay",
        "gate_results",
    ] {
        let Some((path, sha256)) = file_ref(manifest, key) else {
            return Err(if key == "replay" {
                ReleaseReplayPreflightCode::MissingReplayReport
            } else {
                ReleaseReplayPreflightCode::MissingBoundFile
            });
        };
        if key == "replay" && !files.contains_key(path) {
            return Err(ReleaseReplayPreflightCode::MissingReplayReport);
        }
        validate_preflight_bound_file(files, path, sha256)?;
    }

    let Some(proofs) = proof_refs(manifest) else {
        return Err(ReleaseReplayPreflightCode::MissingBoundFile);
    };
    for (path, sha256) in proofs {
        validate_preflight_bound_file(files, path, sha256)?;
    }
    Ok(())
}

fn validate_preflight_replay_report(
    manifest: &Value,
    files: &BTreeMap<String, Vec<u8>>,
) -> Result<(), ReleaseReplayPreflightCode> {
    let Some((path, _sha256)) = file_ref(manifest, "replay") else {
        return Err(ReleaseReplayPreflightCode::MissingReplayReport);
    };
    let Some(bytes) = files.get(path) else {
        return Err(ReleaseReplayPreflightCode::MissingReplayReport);
    };
    let Ok(report) = serde_json::from_slice::<Value>(bytes) else {
        return Err(ReleaseReplayPreflightCode::MissingReplayReport);
    };

    if !json_array_is_non_empty(report.get("pc_map")) {
        return Err(ReleaseReplayPreflightCode::MissingPcMap);
    }
    if !json_array_is_non_empty(report.get("statuses")) {
        return Err(ReleaseReplayPreflightCode::MissingStatuses);
    }
    if !json_string_array_is_non_empty(report.get("symbols")) {
        return Err(ReleaseReplayPreflightCode::MissingSymbols);
    }

    let bundle_generation = manifest
        .get("generation")
        .and_then(Value::as_u64)
        .unwrap_or(0);
    let replay_generation = report
        .get("generation")
        .and_then(Value::as_u64)
        .unwrap_or(bundle_generation);
    if replay_generation < bundle_generation {
        return Err(ReleaseReplayPreflightCode::StaleGeneration);
    }
    Ok(())
}

/// Preflight a release/replay bundle before consumer replay or dispatch.
///
/// The caller supplies the manifest JSON, the already-loaded bundle files keyed
/// by bundle-relative path, and the required features it understands. Unknown
/// required features fail closed.
pub fn preflight_release_replay_bundle_consumer(
    manifest: &str,
    files: &BTreeMap<String, Vec<u8>>,
    supported_required_features: &[&str],
) -> ReleaseReplayBundlePreflightVerdict {
    let Ok(manifest) = serde_json::from_str::<Value>(manifest) else {
        return ReleaseReplayBundlePreflightVerdict::rejected(
            ReleaseReplayPreflightCode::UnsupportedSchema,
        );
    };

    let schema = manifest.get("schema").and_then(Value::as_str).unwrap_or("");
    let schema_version = manifest
        .get("schema_version")
        .and_then(Value::as_u64)
        .and_then(|version| u32::try_from(version).ok())
        .unwrap_or(0);
    if !bundle_schema_is_supported(schema, schema_version) {
        return ReleaseReplayBundlePreflightVerdict::rejected(
            ReleaseReplayPreflightCode::UnsupportedSchema,
        );
    }
    if let Err(code) = validate_preflight_required_features(&manifest, supported_required_features)
    {
        return ReleaseReplayBundlePreflightVerdict::rejected(code);
    }
    if let Err(code) = validate_preflight_bound_files(&manifest, files) {
        return ReleaseReplayBundlePreflightVerdict::rejected(code);
    }
    if let Err(code) = validate_preflight_replay_report(&manifest, files) {
        return ReleaseReplayBundlePreflightVerdict::rejected(code);
    }

    let consumer = manifest
        .get("consumer")
        .and_then(Value::as_str)
        .filter(|consumer| bundle_consumer_is_supported(consumer))
        .unwrap_or("generic");
    ReleaseReplayBundlePreflightVerdict::accepted(consumer)
}

fn file_reference_is_complete(file: &ReleaseBundleFileReference) -> bool {
    non_empty(&file.path) && non_empty(&file.sha256)
}

fn artifact_manifest_reference_is_complete(file: &ReleaseArtifactManifestReference) -> bool {
    non_empty(&file.path) && non_empty(&file.sha256) && file.schema_version != 0
}

fn proof_report_reference_has_required_metadata(
    proof_report: &ReleaseProofReportReference,
) -> bool {
    file_reference_is_complete(&proof_report.file)
        && proof_report.policy.as_deref().is_some_and(non_empty)
        && proof_report.solver.as_deref().is_some_and(non_empty)
        && proof_report
            .obligation_set
            .as_deref()
            .is_some_and(non_empty)
        && proof_report.timeout_ms.is_some()
}

fn proof_verdict_install_code(verdict: Option<&str>) -> Result<(), ReleaseBundleInstallCode> {
    let Some(verdict) = verdict.map(str::trim).filter(|verdict| !verdict.is_empty()) else {
        return Err(ReleaseBundleInstallCode::MissingProofVerdict);
    };

    if verdict.eq_ignore_ascii_case("accepted") {
        return Ok(());
    }

    if verdict.eq_ignore_ascii_case("proof_timeout") || verdict.eq_ignore_ascii_case("timeout") {
        return Err(ReleaseBundleInstallCode::ProofTimeout);
    }

    if verdict.eq_ignore_ascii_case("rejected") || verdict.eq_ignore_ascii_case("proof_rejected") {
        return Err(ReleaseBundleInstallCode::ProofRejected);
    }

    Err(ReleaseBundleInstallCode::ProofVerdictNotAccepted)
}

fn proof_optimization_citation_identity_is_complete(
    citation: &ProofOptimizationCertificateCitation,
) -> bool {
    non_empty(&citation.function_name)
        && non_empty(&citation.certificate_id)
        && non_empty(&citation.proof_hash)
        && non_empty(&citation.validation_hash)
        && non_empty(&citation.source_region_hash)
        && non_empty(&citation.target_region_hash)
        && non_empty(&citation.transform_name)
        && non_empty(&citation.admission)
        && non_empty(&citation.kind)
        && non_empty(&citation.status)
}

fn ty_native_fused_proof_optimization_citation_is_applied(
    citation: &ProofOptimizationCertificateCitation,
) -> bool {
    proof_optimization_citation_identity_is_complete(citation)
        && citation.status == "applied"
        && citation.rejection_code.is_none()
        && citation.rejection_fact.is_none()
        && citation.rejection_detail.is_none()
        && citation.transform_name == RELEASE_TY_NATIVE_FUSED_PROOF_OPT_TRANSFORM_NAME
        && citation.transform_version == RELEASE_TY_NATIVE_FUSED_PROOF_OPT_TRANSFORM_VERSION
        && citation.admission == RELEASE_TY_NATIVE_FUSED_PROOF_OPT_ADMISSION
        && citation.kind == RELEASE_TY_NATIVE_FUSED_PROOF_OPT_KIND
}

fn ty_native_fused_expected_proof_optimization_certificate_id(function_name: &str) -> String {
    format!("{RELEASE_TY_NATIVE_FUSED_PROOF_OPT_TRANSFORM_NAME}:{function_name}:cert-v1")
}

fn ty_native_fused_proof_optimization_citation_matches_release_identity(
    citation: &ProofOptimizationCertificateCitation,
    metadata: &BTreeMap<String, String>,
) -> bool {
    if citation.certificate_id
        != ty_native_fused_expected_proof_optimization_certificate_id(&citation.function_name)
    {
        return false;
    }

    [
        (
            RELEASE_TY_NATIVE_FUSED_PROOF_OPT_FUNCTION_NAME_KEY,
            citation.function_name.as_str(),
        ),
        (
            RELEASE_TY_NATIVE_FUSED_PROOF_OPT_CERTIFICATE_ID_KEY,
            citation.certificate_id.as_str(),
        ),
        (
            RELEASE_TY_NATIVE_FUSED_PROOF_OPT_SOURCE_REGION_HASH_KEY,
            citation.source_region_hash.as_str(),
        ),
        (
            RELEASE_TY_NATIVE_FUSED_PROOF_OPT_TARGET_REGION_HASH_KEY,
            citation.target_region_hash.as_str(),
        ),
    ]
    .into_iter()
    .all(|(key, expected)| {
        metadata
            .get(key)
            .is_some_and(|actual| non_empty(actual) && actual == expected)
    })
}

fn ty_native_fused_proof_optimization_citation_consumes_required_facts(
    citation: &ProofOptimizationCertificateCitation,
) -> bool {
    TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA
        .iter()
        .all(|(metadata_key, fact)| {
            citation.consumed_facts.iter().any(|consumed| {
                consumed.name == *fact && consumed.payload.as_deref() == Some(*metadata_key)
            })
        })
}

fn release_install_code_for_gate_rejection(
    code: Option<NativeInstallGateRejectionCode>,
) -> ReleaseBundleInstallCode {
    match code {
        Some(
            NativeInstallGateRejectionCode::StaleInvalidation
            | NativeInstallGateRejectionCode::ProofStaleEvidence,
        ) => ReleaseBundleInstallCode::GateStaleInvalidation,
        Some(NativeInstallGateRejectionCode::RevokedArtifact) => {
            ReleaseBundleInstallCode::GateRevoked
        }
        Some(NativeInstallGateRejectionCode::KillSwitchActive) => {
            ReleaseBundleInstallCode::GateKillSwitch
        }
        _ => ReleaseBundleInstallCode::GateRejected,
    }
}

fn bundle_schema_is_supported(schema: &str, schema_version: u32) -> bool {
    schema == JIT_RELEASE_BUNDLE_SCHEMA && schema_version == JIT_RELEASE_BUNDLE_SCHEMA_VERSION
}

fn bundle_consumer_is_supported(consumer: &str) -> bool {
    matches!(consumer, "ay" | "ty")
}

fn source_lock_downstream_revision_key(consumer: &str) -> Option<&'static str> {
    match consumer {
        "ay" => Some(RELEASE_SOURCE_LOCK_AY_REVISION_KEY),
        "ty" => Some(RELEASE_SOURCE_LOCK_TY_REVISION_KEY),
        _ => None,
    }
}

fn required_source_lock_metadata_value<'a>(
    metadata: &'a BTreeMap<String, String>,
    key: &str,
) -> Result<&'a str, ReleaseBundleInstallCode> {
    let Some(value) = metadata.get(key) else {
        return Err(ReleaseBundleInstallCode::MissingSourceLockMetadata);
    };
    if value.trim().is_empty() {
        return Err(ReleaseBundleInstallCode::MissingSourceLockMetadata);
    }
    Ok(value.as_str())
}

fn bind_trust_ir_hardware_vector_contract_metadata_from_gate(
    artifact_metadata: &BTreeMap<String, String>,
    release_metadata: &mut BTreeMap<String, String>,
) {
    for key in [
        TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA_KEY,
        TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA_VERSION_KEY,
        TRUST_IR_HARDWARE_VECTOR_CONTRACT_SET_NAME_KEY,
        TRUST_IR_HARDWARE_VECTOR_CONTRACT_TARGET_FAMILY_KEY,
        TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_ROW_COUNT_KEY,
        TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SHA256_KEY,
    ] {
        if let Some(value) = artifact_metadata.get(key) {
            release_metadata.insert(key.to_owned(), value.clone());
        }
    }
}

fn bind_host_jit_target_feature_profile_metadata_from_gate(
    artifact_metadata: &BTreeMap<String, String>,
    release_metadata: &mut BTreeMap<String, String>,
) {
    for (key, value) in artifact_metadata {
        if key.starts_with(HOST_JIT_TARGET_FEATURE_PROFILE_METADATA_PREFIX) {
            release_metadata.insert(key.clone(), value.clone());
        }
    }
}

fn revision_value_is_installable(value: &str) -> bool {
    let trimmed = value.trim();
    if trimmed.is_empty() {
        return false;
    }
    let lower = trimmed.to_ascii_lowercase();
    if lower.starts_with("todo") {
        return false;
    }
    if matches!(
        lower.as_str(),
        "unknown"
            | "tbd"
            | "n/a"
            | "na"
            | "none"
            | "latest"
            | "head"
            | "main"
            | "master"
            | "trunk"
            | "develop"
            | "dev"
    ) {
        return false;
    }
    !lower.starts_with("refs/heads/")
        && !lower.starts_with("heads/")
        && !lower.starts_with("refs/remotes/")
        && !lower.starts_with("remotes/")
        && !lower.starts_with("origin/")
}

impl ReleaseReplayBundleMetadata {
    /// Create a bundle manifest with the current schema tag and one proof report.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        consumer: impl Into<String>,
        consumer_mode: impl Into<String>,
        artifact_id: impl Into<String>,
        artifact_manifest: ReleaseArtifactManifestReference,
        source_lock: ReleaseBundleFileReference,
        proof_report: ReleaseProofReportReference,
        telemetry: ReleaseBundleFileReference,
        release_package: ReleaseBundleFileReference,
        replay: ReleaseBundleFileReference,
        gate_results: ReleaseBundleFileReference,
    ) -> Self {
        Self {
            schema: JIT_RELEASE_BUNDLE_SCHEMA.to_owned(),
            schema_version: JIT_RELEASE_BUNDLE_SCHEMA_VERSION,
            consumer: consumer.into(),
            consumer_mode: consumer_mode.into(),
            artifact_id: artifact_id.into(),
            artifact_manifest,
            source_lock,
            proof_reports: vec![proof_report],
            telemetry,
            release_package,
            replay,
            gate_results,
            install_gate: None,
            proof_optimization_certificates: Vec::new(),
            metadata: BTreeMap::new(),
        }
    }

    /// Replace proof report references.
    pub fn with_proof_reports(
        mut self,
        proof_reports: impl IntoIterator<Item = ReleaseProofReportReference>,
    ) -> Self {
        self.proof_reports = proof_reports.into_iter().collect();
        self
    }

    /// Attach proof-optimization certificate citations produced by codegen.
    pub fn with_proof_optimization_certificates(
        mut self,
        certificates: impl IntoIterator<Item = ProofOptimizationCertificateCitation>,
    ) -> Self {
        self.proof_optimization_certificates = certificates.into_iter().collect();
        self
    }

    /// Bind the TY native-fused proof-optimization citation identity used by
    /// install validation.
    pub fn with_ty_native_fused_proof_optimization_citation_identity(
        mut self,
        citation: &ProofOptimizationCertificateCitation,
    ) -> Self {
        self.metadata.insert(
            RELEASE_TY_NATIVE_FUSED_PROOF_OPT_FUNCTION_NAME_KEY.to_owned(),
            citation.function_name.clone(),
        );
        self.metadata.insert(
            RELEASE_TY_NATIVE_FUSED_PROOF_OPT_CERTIFICATE_ID_KEY.to_owned(),
            citation.certificate_id.clone(),
        );
        self.metadata.insert(
            RELEASE_TY_NATIVE_FUSED_PROOF_OPT_SOURCE_REGION_HASH_KEY.to_owned(),
            citation.source_region_hash.clone(),
        );
        self.metadata.insert(
            RELEASE_TY_NATIVE_FUSED_PROOF_OPT_TARGET_REGION_HASH_KEY.to_owned(),
            citation.target_region_hash.clone(),
        );
        self
    }

    /// Attach native install gate metadata.
    pub fn with_install_gate(mut self, install_gate: ReleaseNativeInstallGateMetadata) -> Self {
        self.install_gate = Some(install_gate);
        self
    }

    /// Attach native install gate metadata and, for TY native-fused release
    /// bundles, bind replay/release identity into the extension metadata map.
    pub fn with_install_gate_metadata_bindings(
        mut self,
        install_gate: ReleaseNativeInstallGateMetadata,
    ) -> Self {
        if self.install_gate_identity_matches_bundle(&install_gate) {
            if let Some(metadata) =
                ReleaseTyNativeFusedReplayMetadata::from_install_gate(&install_gate)
            {
                metadata.bind_into_metadata(&mut self.metadata);
            }
            bind_trust_ir_hardware_vector_contract_metadata_from_gate(
                &install_gate.packet.artifact.manifest_metadata,
                &mut self.metadata,
            );
            bind_host_jit_target_feature_profile_metadata_from_gate(
                &install_gate.packet.artifact.manifest_metadata,
                &mut self.metadata,
            );
        }
        self.install_gate = Some(install_gate);
        self
    }

    /// Return the metadata-only install decision for this release/replay bundle.
    ///
    /// The validator intentionally does not open bound files. It only checks
    /// that required replay bindings are present and that every proof report
    /// carries an install-accepted verdict.
    pub fn install_decision(&self) -> ReleaseBundleInstallDecision {
        self.install_decision_with_current_gate(None)
    }

    /// Return the install decision while revalidating the gate packet against
    /// a live current freshness context observed during release restore.
    pub fn install_decision_with_gate_current(
        &self,
        current: &NativeInstallGateRevalidationInput,
    ) -> ReleaseBundleInstallDecision {
        self.install_decision_with_current_gate(Some(current))
    }

    fn install_decision_with_current_gate(
        &self,
        current: Option<&NativeInstallGateRevalidationInput>,
    ) -> ReleaseBundleInstallDecision {
        if !bundle_schema_is_supported(&self.schema, self.schema_version) {
            return ReleaseBundleInstallDecision::non_installable(
                ReleaseBundleInstallCode::UnsupportedSchema,
            );
        }

        if !self.has_required_replay_metadata() {
            return ReleaseBundleInstallDecision::non_installable(
                ReleaseBundleInstallCode::MissingReplayMetadata,
            );
        }

        if !bundle_consumer_is_supported(&self.consumer) {
            return ReleaseBundleInstallDecision::non_installable(
                ReleaseBundleInstallCode::UnsupportedConsumer,
            );
        }

        if self.proof_reports.is_empty() {
            return ReleaseBundleInstallDecision::non_installable(
                ReleaseBundleInstallCode::MissingProofReports,
            );
        }

        for proof_report in &self.proof_reports {
            if !proof_report_reference_has_required_metadata(proof_report) {
                return ReleaseBundleInstallDecision::non_installable(
                    ReleaseBundleInstallCode::MissingProofReportMetadata,
                );
            }

            if let Err(code) = proof_verdict_install_code(proof_report.verdict.as_deref()) {
                return ReleaseBundleInstallDecision::replay_only(code);
            }
        }

        if let Err(code) = self.validate_install_gate_metadata(current) {
            return ReleaseBundleInstallDecision::non_installable(code);
        }

        if let Err(code) = self.validate_ty_native_fused_replay_metadata() {
            return ReleaseBundleInstallDecision::non_installable(code);
        }

        if let Err(code) = self.validate_ty_native_fused_proof_optimization_citation() {
            return ReleaseBundleInstallDecision::non_installable(code);
        }

        ReleaseBundleInstallDecision::installable()
    }

    fn validate_install_gate_metadata(
        &self,
        current: Option<&NativeInstallGateRevalidationInput>,
    ) -> Result<(), ReleaseBundleInstallCode> {
        let Some(gate) = self.install_gate.as_ref() else {
            return Err(ReleaseBundleInstallCode::MissingGateMetadata);
        };
        let packet = &gate.packet;
        if packet.schema != NATIVE_INSTALL_GATE_PACKET_SCHEMA
            || packet.schema_version != NATIVE_INSTALL_GATE_PACKET_SCHEMA_VERSION
            || packet.surface != NativeInstallGateSurface::ReleaseBundle
            || packet.consumer != self.consumer
            || packet.consumer_mode != self.consumer_mode
            || packet.artifact.artifact_id != self.artifact_id
            || packet.artifact.manifest_checksum != self.artifact_manifest.manifest_checksum
            || gate.telemetry_sha256 != self.telemetry.sha256
        {
            return Err(ReleaseBundleInstallCode::GateMetadataMismatch);
        }
        self.validate_source_lock_metadata(gate)?;
        let proof_tv_checksum = packet.validation.proof_report_sha256.as_deref();
        if proof_tv_checksum.is_none()
            || !self
                .proof_reports
                .iter()
                .any(|proof| Some(proof.file.sha256.as_str()) == proof_tv_checksum)
        {
            return Err(ReleaseBundleInstallCode::GateMetadataMismatch);
        }
        let verdict = if let Some(current) = current {
            validate_native_install_gate_packet_with_current(
                packet,
                Some(packet.packet_hash),
                current,
            )
        } else {
            validate_native_install_gate_packet(packet, Some(packet.packet_hash))
        };
        if !verdict.disposition.is_installable()
            || verdict.rejection_code.is_some()
            || !verdict.actions.release_installable
        {
            return Err(release_install_code_for_gate_rejection(
                verdict.rejection_code,
            ));
        }
        Ok(())
    }

    fn validate_source_lock_metadata(
        &self,
        gate: &ReleaseNativeInstallGateMetadata,
    ) -> Result<(), ReleaseBundleInstallCode> {
        let schema =
            required_source_lock_metadata_value(&self.metadata, RELEASE_SOURCE_LOCK_SCHEMA_KEY)?;
        let schema_version = required_source_lock_metadata_value(
            &self.metadata,
            RELEASE_SOURCE_LOCK_SCHEMA_VERSION_KEY,
        )?;
        let expected_schema_version = RELEASE_SOURCE_LOCK_METADATA_SCHEMA_VERSION.to_string();
        if schema != RELEASE_SOURCE_LOCK_METADATA_SCHEMA
            || schema_version != expected_schema_version
        {
            return Err(ReleaseBundleInstallCode::SourceLockMetadataMismatch);
        }

        for key in [
            RELEASE_SOURCE_LOCK_TRUST_CG_REVISION_KEY,
            RELEASE_SOURCE_LOCK_TRUST_IR_REVISION_KEY,
            source_lock_downstream_revision_key(&self.consumer)
                .ok_or(ReleaseBundleInstallCode::UnsupportedConsumer)?,
        ] {
            let value = required_source_lock_metadata_value(&self.metadata, key)?;
            if !revision_value_is_installable(value) {
                return Err(ReleaseBundleInstallCode::MissingSourceLockMetadata);
            }
        }

        let source_lock_sha256 =
            required_source_lock_metadata_value(&self.metadata, RELEASE_SOURCE_LOCK_SHA256_KEY)?;
        if source_lock_sha256 != self.source_lock.sha256 {
            return Err(ReleaseBundleInstallCode::SourceLockMetadataMismatch);
        }

        let artifact = &gate.packet.artifact;
        for (key, expected) in [
            (RELEASE_SOURCE_SHA256_KEY, artifact.source_sha256.as_str()),
            (
                RELEASE_TRUST_IR_SHA256_KEY,
                artifact.trust_ir_sha256.as_str(),
            ),
            (
                RELEASE_NATIVE_PAYLOAD_SHA256_KEY,
                artifact.native_payload_sha256.as_str(),
            ),
        ] {
            let actual = required_source_lock_metadata_value(&self.metadata, key)?;
            if actual != expected {
                return Err(ReleaseBundleInstallCode::SourceLockMetadataMismatch);
            }
        }

        Ok(())
    }

    fn validate_ty_native_fused_replay_metadata(&self) -> Result<(), ReleaseBundleInstallCode> {
        if self.consumer != "ty" || self.consumer_mode != TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE
        {
            return Ok(());
        }

        let Some(gate) = self.install_gate.as_ref() else {
            return Err(ReleaseBundleInstallCode::MissingGateMetadata);
        };
        let Some(expected) = ReleaseTyNativeFusedReplayMetadata::from_install_gate(gate) else {
            return Err(ReleaseBundleInstallCode::GateMetadataMismatch);
        };
        let expected_entries = expected.to_metadata_entries();

        if expected_entries.keys().any(|key| {
            self.metadata
                .get(key)
                .is_none_or(|value| value.trim().is_empty())
        }) {
            return Err(ReleaseBundleInstallCode::MissingReplayMetadata);
        }

        for (key, expected_value) in expected_entries {
            if self.metadata.get(&key) != Some(&expected_value) {
                return Err(ReleaseBundleInstallCode::GateMetadataMismatch);
            }
        }

        Ok(())
    }

    fn validate_ty_native_fused_proof_optimization_citation(
        &self,
    ) -> Result<(), ReleaseBundleInstallCode> {
        if self.consumer != "ty" || self.consumer_mode != TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE
        {
            return Ok(());
        }

        let Some(gate) = self.install_gate.as_ref() else {
            return Err(ReleaseBundleInstallCode::MissingGateMetadata);
        };
        let Some(expected) = ReleaseTyNativeFusedReplayMetadata::from_install_gate(gate) else {
            return Err(ReleaseBundleInstallCode::GateMetadataMismatch);
        };

        let mut saw_ty_native_fused_applied = false;
        let mut saw_matching_release_identity = false;
        let mut saw_matching_validation_hash = false;
        for citation in &self.proof_optimization_certificates {
            if !ty_native_fused_proof_optimization_citation_is_applied(citation) {
                continue;
            }
            saw_ty_native_fused_applied = true;

            if !ty_native_fused_proof_optimization_citation_matches_release_identity(
                citation,
                &self.metadata,
            ) {
                continue;
            }
            saw_matching_release_identity = true;

            if citation.validation_hash != expected.proof_validation_sha256 {
                continue;
            }
            saw_matching_validation_hash = true;

            if ty_native_fused_proof_optimization_citation_consumes_required_facts(citation) {
                return Ok(());
            }
        }

        if !saw_ty_native_fused_applied {
            return Err(ReleaseBundleInstallCode::MissingProofOptimizationCitation);
        }
        if !saw_matching_release_identity {
            return Err(ReleaseBundleInstallCode::MissingProofOptimizationCitation);
        }
        if !saw_matching_validation_hash {
            return Err(ReleaseBundleInstallCode::ProofOptimizationValidationHashMismatch);
        }
        Err(ReleaseBundleInstallCode::ProofOptimizationCitationMissingFact)
    }

    fn install_gate_identity_matches_bundle(
        &self,
        install_gate: &ReleaseNativeInstallGateMetadata,
    ) -> bool {
        let packet = &install_gate.packet;
        packet.schema == NATIVE_INSTALL_GATE_PACKET_SCHEMA
            && packet.schema_version == NATIVE_INSTALL_GATE_PACKET_SCHEMA_VERSION
            && packet.surface == NativeInstallGateSurface::ReleaseBundle
            && packet.consumer == self.consumer
            && packet.consumer_mode == self.consumer_mode
            && packet.artifact.artifact_id == self.artifact_id
            && packet.artifact.manifest_checksum == self.artifact_manifest.manifest_checksum
    }

    fn has_required_replay_metadata(&self) -> bool {
        non_empty(&self.consumer)
            && non_empty(&self.consumer_mode)
            && non_empty(&self.artifact_id)
            && artifact_manifest_reference_is_complete(&self.artifact_manifest)
            && file_reference_is_complete(&self.source_lock)
            && file_reference_is_complete(&self.telemetry)
            && file_reference_is_complete(&self.release_package)
            && file_reference_is_complete(&self.replay)
            && file_reference_is_complete(&self.gate_results)
    }

    /// Return a clone with unordered collections in canonical order.
    pub fn canonicalized(&self) -> Self {
        let mut bundle = self.clone();
        bundle
            .proof_reports
            .sort_by(|left, right| left.stable_key().cmp(&right.stable_key()));
        bundle
            .proof_optimization_certificates
            .sort_by(|left, right| {
                (
                    left.function_name.as_str(),
                    left.certificate_id.as_str(),
                    left.proof_hash.as_str(),
                    left.validation_hash.as_str(),
                )
                    .cmp(&(
                        right.function_name.as_str(),
                        right.certificate_id.as_str(),
                        right.proof_hash.as_str(),
                        right.validation_hash.as_str(),
                    ))
            });
        bundle
    }

    /// Convert to the stable bundle JSON representation.
    pub fn to_json_value(&self) -> Value {
        let bundle = self.canonicalized();
        let proof_reports: Vec<_> = bundle
            .proof_reports
            .iter()
            .map(ReleaseProofReportReference::to_json_value)
            .collect();
        let proof_optimization_certificates: Vec<_> = bundle
            .proof_optimization_certificates
            .iter()
            .map(ProofOptimizationCertificateCitation::to_json_value)
            .collect();
        let proof_optimization_citation_summary =
            ReleaseProofOptimizationCitationSummary::from_certificates(
                &bundle.proof_optimization_certificates,
            );

        json!({
            "artifact_id": bundle.artifact_id,
            "artifact_manifest": bundle.artifact_manifest.to_json_value(),
            "consumer": bundle.consumer,
            "consumer_mode": bundle.consumer_mode,
            "gate_results": bundle.gate_results.to_json_value(),
            "install_gate": bundle.install_gate.as_ref().map(ReleaseNativeInstallGateMetadata::to_json_value),
            "install_decision": bundle.install_decision().to_json_value(),
            "metadata": bundle.metadata,
            "proof_optimization_citation_summary": proof_optimization_citation_summary.to_json_value(),
            "proof_optimization_certificates": proof_optimization_certificates,
            "proof_reports": proof_reports,
            "release_package": bundle.release_package.to_json_value(),
            "replay": bundle.replay.to_json_value(),
            "schema": bundle.schema,
            "schema_version": bundle.schema_version,
            "source_lock": bundle.source_lock.to_json_value(),
            "telemetry": bundle.telemetry.to_json_value(),
        })
    }

    /// Convert to deterministic pretty JSON with a trailing newline.
    pub fn to_pretty_json(&self) -> String {
        let mut output = serde_json::to_string_pretty(&self.to_json_value())
            .expect("serializing serde_json::Value should not fail");
        output.push('\n');
        output
    }

    /// Return deterministic bytes used for the bundle checksum.
    pub fn canonical_bytes(&self) -> Vec<u8> {
        self.to_pretty_json().into_bytes()
    }

    /// Deterministic checksum for this bundle manifest.
    pub fn checksum(&self) -> ArtifactChecksum {
        ArtifactChecksum::for_bytes(&self.canonical_bytes())
    }
}
