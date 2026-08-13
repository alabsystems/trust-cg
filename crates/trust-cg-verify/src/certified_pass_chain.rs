// trust-cg-verify/certified_pass_chain.rs - Ordered certified pass chain boundary
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Fail-closed boundary for ordered certified compiler-pass chains.
//!
//! This module binds the existing Lean5 pass-certificate request/report hook to
//! a production chain shape. A chain entry is accepted only when the certificate
//! says it must be verified, the checker report is verified, the request,
//! certificate, and report agree on the obligation hash, and the certificate
//! indices form a zero-based ordered sequence.

use serde::{Deserialize, Serialize};
use serde_json::Value;
use thiserror::Error;

use crate::certified_pass_checker::{
    CheckerArtifactRef, Lean5CheckerResult, Lean5PassCertificateCheckReport,
    Lean5PassCertificateCheckRequest, ProofArtifactIdentity, check_lean5_pass_certificate,
};

const CHECK_REPORT_FORMAT_VERSION: &str = "trust-cg.lean5_pass_check.report.v1";

/// Ordered fail-closed chain of certified pass checker reports.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertifiedPassChain {
    compilation_unit: String,
    entries: Vec<CertifiedPassChainEntry>,
}

impl CertifiedPassChain {
    /// Run the Lean5 checker hook for every request, then validate the chain.
    pub fn check_requests<I>(requests: I) -> Result<Self, CertifiedPassChainError>
    where
        I: IntoIterator<Item = Lean5PassCertificateCheckRequest>,
    {
        Self::from_entries(requests.into_iter().map(CertifiedPassChainEntry::check))
    }

    /// Build a chain from caller-supplied request/report pairs.
    pub fn from_entries<I>(entries: I) -> Result<Self, CertifiedPassChainError>
    where
        I: IntoIterator<Item = CertifiedPassChainEntry>,
    {
        let entries: Vec<_> = entries.into_iter().collect();
        if entries.is_empty() {
            return Err(CertifiedPassChainError::Empty);
        }

        let compilation_unit = required_certificate_string(
            &entries[0].request.certificate,
            &["chain", "compilation_unit"],
            0,
        )?
        .to_string();
        if compilation_unit.is_empty() {
            return Err(CertifiedPassChainError::MissingCertificateField {
                entry_index: 0,
                field: "chain.compilation_unit",
            });
        }

        let chain = Self {
            compilation_unit,
            entries,
        };
        chain.validate()?;
        Ok(chain)
    }

    /// Validate the chain without rebuilding it.
    pub fn validate(&self) -> Result<(), CertifiedPassChainError> {
        if self.entries.is_empty() {
            return Err(CertifiedPassChainError::Empty);
        }

        for (entry_index, entry) in self.entries.iter().enumerate() {
            validate_entry(entry_index, &self.compilation_unit, entry)?;
        }

        Ok(())
    }

    /// Compilation unit shared by all certificates in this chain.
    pub fn compilation_unit(&self) -> &str {
        &self.compilation_unit
    }

    /// Validated chain entries in certificate order.
    pub fn entries(&self) -> &[CertifiedPassChainEntry] {
        &self.entries
    }
}

/// One certified pass request and the checker report attached to it.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertifiedPassChainEntry {
    /// Request supplied to the Lean5 pass-certificate checker hook.
    pub request: Lean5PassCertificateCheckRequest,
    /// Checker report attached to this chain entry.
    pub report: Lean5PassCertificateCheckReport,
}

impl CertifiedPassChainEntry {
    /// Run the existing checker hook and attach its report.
    pub fn check(request: Lean5PassCertificateCheckRequest) -> Self {
        let report = check_lean5_pass_certificate(&request);
        Self { request, report }
    }

    /// Attach an existing checker report to a request for chain validation.
    pub fn from_report(
        request: Lean5PassCertificateCheckRequest,
        report: Lean5PassCertificateCheckReport,
    ) -> Self {
        Self { request, report }
    }

    /// Certificate index declared by `certificate.chain.certificate_index`.
    pub fn certificate_index(&self) -> Option<u64> {
        certificate_u64(&self.request.certificate, &["chain", "certificate_index"])
    }

    /// Pass name declared by `certificate.pass.name`.
    pub fn pass_name(&self) -> Option<&str> {
        certificate_string(&self.request.certificate, &["pass", "name"])
    }
}

/// Reason an ordered certified pass chain was rejected.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum CertifiedPassChainError {
    /// No entries were supplied.
    #[error("certified pass chain has no entries")]
    Empty,
    /// A required certificate field is missing or has the wrong JSON type.
    #[error("entry {entry_index}: missing or invalid certificate.{field}")]
    MissingCertificateField {
        /// Zero-based entry position in the attempted chain.
        entry_index: usize,
        /// Dot-separated certificate field path.
        field: &'static str,
    },
    /// `certificate.chain.must_be_verified` is missing or false.
    #[error("entry {entry_index}: certificate.chain.must_be_verified must be true")]
    CertificateMustBeVerified {
        /// Zero-based entry position in the attempted chain.
        entry_index: usize,
    },
    /// `certificate.result.status` is not `verified`.
    #[error("entry {entry_index}: certificate result status is not verified: {status}")]
    CertificateResultNotVerified {
        /// Zero-based entry position in the attempted chain.
        entry_index: usize,
        /// Certificate result status, or `<missing>`.
        status: String,
    },
    /// The certificate index does not match the chain position.
    #[error(
        "entry {entry_index}: certificate.chain.certificate_index is {certificate_index}, expected {expected_index}"
    )]
    CertificateIndexOutOfOrder {
        /// Zero-based entry position in the attempted chain.
        entry_index: usize,
        /// Expected zero-based certificate index.
        expected_index: u64,
        /// Certificate-provided index.
        certificate_index: u64,
    },
    /// A certificate belongs to a different compilation unit than the chain.
    #[error(
        "entry {entry_index}: certificate.chain.compilation_unit is '{actual}', expected '{expected}'"
    )]
    CompilationUnitMismatch {
        /// Zero-based entry position in the attempted chain.
        entry_index: usize,
        /// Chain compilation unit.
        expected: String,
        /// Certificate compilation unit.
        actual: String,
    },
    /// Request, certificate, and report obligation hashes do not agree.
    #[error(
        "entry {entry_index}: obligation hash mismatch: request='{request}', certificate='{certificate}', report='{report}'"
    )]
    ObligationHashMismatch {
        /// Zero-based entry position in the attempted chain.
        entry_index: usize,
        /// Request obligation hash.
        request: String,
        /// Certificate obligation hash.
        certificate: String,
        /// Report obligation hash.
        report: String,
    },
    /// The attached checker report is not verified.
    #[error("entry {entry_index}: checker report is not verified: {result:?}")]
    ReportNotVerified {
        /// Zero-based entry position in the attempted chain.
        entry_index: usize,
        /// Attached report result.
        result: Lean5CheckerResult,
    },
    /// Replaying the request through the checker hook does not verify.
    #[error("entry {entry_index}: checker replay did not verify: {result:?}")]
    CheckerReplayNotVerified {
        /// Zero-based entry position in the attempted chain.
        entry_index: usize,
        /// Replayed checker result.
        result: Lean5CheckerResult,
    },
    /// Required proof artifact identity is missing.
    #[error("entry {entry_index}: missing proof artifact identity in {artifact_source}")]
    ProofArtifactMissing {
        /// Zero-based entry position in the attempted chain.
        entry_index: usize,
        /// Artifact source that was missing the proof artifact.
        artifact_source: &'static str,
    },
    /// Proof artifact identity differs across request, certificate, and report.
    #[error("entry {entry_index}: proof artifact mismatch: {reason}")]
    ProofArtifactMismatch {
        /// Zero-based entry position in the attempted chain.
        entry_index: usize,
        /// Human-readable mismatch reason.
        reason: String,
    },
    /// A verified-looking report has summary fields that do not match replay.
    #[error("entry {entry_index}: checker report summary mismatch: {reason}")]
    TamperedReportSummary {
        /// Zero-based entry position in the attempted chain.
        entry_index: usize,
        /// Human-readable mismatch reason.
        reason: String,
    },
}

fn validate_entry(
    entry_index: usize,
    chain_compilation_unit: &str,
    entry: &CertifiedPassChainEntry,
) -> Result<(), CertifiedPassChainError> {
    let certificate = &entry.request.certificate;

    if certificate_bool(certificate, &["chain", "must_be_verified"]) != Some(true) {
        return Err(CertifiedPassChainError::CertificateMustBeVerified { entry_index });
    }

    let cert_status = certificate_string(certificate, &["result", "status"])
        .unwrap_or("<missing>")
        .to_string();
    if cert_status != "verified" {
        return Err(CertifiedPassChainError::CertificateResultNotVerified {
            entry_index,
            status: cert_status,
        });
    }

    let certificate_index =
        required_certificate_u64(certificate, &["chain", "certificate_index"], entry_index)?;
    let expected_index = entry_index as u64;
    if certificate_index != expected_index {
        return Err(CertifiedPassChainError::CertificateIndexOutOfOrder {
            entry_index,
            expected_index,
            certificate_index,
        });
    }

    let certificate_compilation_unit =
        required_certificate_string(certificate, &["chain", "compilation_unit"], entry_index)?;
    if certificate_compilation_unit != chain_compilation_unit {
        return Err(CertifiedPassChainError::CompilationUnitMismatch {
            entry_index,
            expected: chain_compilation_unit.to_string(),
            actual: certificate_compilation_unit.to_string(),
        });
    }

    let certificate_obligation_hash =
        required_certificate_string(certificate, &["obligation_hash"], entry_index)?;
    if entry.request.obligation_hash != certificate_obligation_hash
        || entry.request.obligation_hash != entry.report.obligation_hash
    {
        return Err(CertifiedPassChainError::ObligationHashMismatch {
            entry_index,
            request: entry.request.obligation_hash.clone(),
            certificate: certificate_obligation_hash.to_string(),
            report: entry.report.obligation_hash.clone(),
        });
    }

    if !entry.report.result.is_verified() {
        return Err(CertifiedPassChainError::ReportNotVerified {
            entry_index,
            result: entry.report.result.clone(),
        });
    }

    validate_proof_artifact(entry_index, entry)?;

    let replayed_report = check_lean5_pass_certificate(&entry.request);
    if !replayed_report.result.is_verified() {
        return Err(CertifiedPassChainError::CheckerReplayNotVerified {
            entry_index,
            result: replayed_report.result,
        });
    }

    validate_report_summary(entry_index, entry, &replayed_report)
}

fn validate_report_summary(
    entry_index: usize,
    entry: &CertifiedPassChainEntry,
    replayed_report: &Lean5PassCertificateCheckReport,
) -> Result<(), CertifiedPassChainError> {
    if entry.report.format_version != CHECK_REPORT_FORMAT_VERSION {
        return tampered_report(
            entry_index,
            format!(
                "report.format_version is '{}', expected '{}'",
                entry.report.format_version, CHECK_REPORT_FORMAT_VERSION
            ),
        );
    }

    if entry.report.result != replayed_report.result {
        return tampered_report(
            entry_index,
            format!(
                "report.result is {:?}, replayed checker returned {:?}",
                entry.report.result, replayed_report.result
            ),
        );
    }

    if entry.report.lean5.version != replayed_report.lean5.version
        || entry.report.lean5.observed != replayed_report.lean5.observed
    {
        return tampered_report(
            entry_index,
            "report.lean5 metadata does not match checker replay".to_string(),
        );
    }

    if entry.report.replay.checker != replayed_report.replay.checker {
        return tampered_report(
            entry_index,
            "report.replay.checker does not match checker replay".to_string(),
        );
    }

    if entry.report.replay.mode != replayed_report.replay.mode {
        return tampered_report(
            entry_index,
            "report.replay.mode does not match checker replay".to_string(),
        );
    }

    if !entry.report.replay.fail_closed
        || entry.report.replay.fail_closed != replayed_report.replay.fail_closed
    {
        return tampered_report(
            entry_index,
            "report.replay.fail_closed does not match checker replay".to_string(),
        );
    }

    if !artifact_ref_slices_equal(
        &entry.report.replay.replay_inputs,
        &replayed_report.replay.replay_inputs,
    ) {
        return tampered_report(
            entry_index,
            "report.replay.replay_inputs do not match checker replay".to_string(),
        );
    }

    Ok(())
}

fn validate_proof_artifact(
    entry_index: usize,
    entry: &CertifiedPassChainEntry,
) -> Result<(), CertifiedPassChainError> {
    let request_artifact = request_proof_artifact(&entry.request).ok_or(
        CertifiedPassChainError::ProofArtifactMissing {
            entry_index,
            artifact_source: "request.artifacts",
        },
    )?;
    let certificate_artifact = certificate_proof_artifact(&entry.request.certificate).ok_or(
        CertifiedPassChainError::ProofArtifactMissing {
            entry_index,
            artifact_source: "certificate.artifacts.refs",
        },
    )?;
    let report_artifact = entry.report.proof_artifact.as_ref().ok_or(
        CertifiedPassChainError::ProofArtifactMissing {
            entry_index,
            artifact_source: "report.proof_artifact",
        },
    )?;

    if !request_artifact.matches_certificate(certificate_artifact) {
        return Err(CertifiedPassChainError::ProofArtifactMismatch {
            entry_index,
            reason: "request proof artifact does not match certificate.artifacts.refs".to_string(),
        });
    }

    if !request_artifact.matches_report(report_artifact) {
        return Err(CertifiedPassChainError::ProofArtifactMismatch {
            entry_index,
            reason: "request proof artifact does not match report.proof_artifact".to_string(),
        });
    }

    Ok(())
}

fn tampered_report<T>(entry_index: usize, reason: String) -> Result<T, CertifiedPassChainError> {
    Err(CertifiedPassChainError::TamperedReportSummary {
        entry_index,
        reason,
    })
}

fn required_certificate_string<'a>(
    certificate: &'a Value,
    path: &[&str],
    entry_index: usize,
) -> Result<&'a str, CertifiedPassChainError> {
    certificate_string(certificate, path).ok_or(CertifiedPassChainError::MissingCertificateField {
        entry_index,
        field: certificate_field(path),
    })
}

fn required_certificate_u64(
    certificate: &Value,
    path: &[&str],
    entry_index: usize,
) -> Result<u64, CertifiedPassChainError> {
    certificate_u64(certificate, path).ok_or(CertifiedPassChainError::MissingCertificateField {
        entry_index,
        field: certificate_field(path),
    })
}

fn certificate_string<'a>(value: &'a Value, path: &[&str]) -> Option<&'a str> {
    certificate_value(value, path)?.as_str()
}

fn certificate_bool(value: &Value, path: &[&str]) -> Option<bool> {
    certificate_value(value, path)?.as_bool()
}

fn certificate_u64(value: &Value, path: &[&str]) -> Option<u64> {
    certificate_value(value, path)?.as_u64()
}

fn certificate_value<'a>(value: &'a Value, path: &[&str]) -> Option<&'a Value> {
    let mut cursor = value;
    for segment in path {
        cursor = cursor.get(*segment)?;
    }
    Some(cursor)
}

fn certificate_field(path: &[&str]) -> &'static str {
    match path {
        ["chain", "compilation_unit"] => "chain.compilation_unit",
        ["chain", "certificate_index"] => "chain.certificate_index",
        ["obligation_hash"] => "obligation_hash",
        _ => "<unknown>",
    }
}

#[derive(Debug, Clone, Copy)]
struct CertificateArtifactIdentity<'a> {
    kind: &'a str,
    uri: &'a str,
    digest: &'a str,
}

impl CertificateArtifactIdentity<'_> {
    fn matches_certificate(&self, other: CertificateArtifactIdentity<'_>) -> bool {
        self.kind == other.kind && self.uri == other.uri && self.digest == other.digest
    }

    fn matches_report(&self, other: &ProofArtifactIdentity) -> bool {
        self.kind == other.kind && self.uri == other.uri && self.digest == other.digest
    }
}

fn request_proof_artifact(
    request: &Lean5PassCertificateCheckRequest,
) -> Option<CertificateArtifactIdentity<'_>> {
    request.artifacts.iter().find_map(|artifact| {
        if is_proof_artifact_kind(&artifact.kind) {
            Some(CertificateArtifactIdentity {
                kind: artifact.kind.as_str(),
                uri: artifact.uri.as_str(),
                digest: artifact.digest.as_str(),
            })
        } else {
            None
        }
    })
}

fn certificate_proof_artifact(certificate: &Value) -> Option<CertificateArtifactIdentity<'_>> {
    certificate_value(certificate, &["artifacts", "refs"])?
        .as_array()?
        .iter()
        .find_map(|artifact| {
            let kind = artifact.get("kind")?.as_str()?;
            if is_proof_artifact_kind(kind) {
                Some(CertificateArtifactIdentity {
                    kind,
                    uri: artifact.get("uri")?.as_str()?,
                    digest: artifact.get("digest")?.as_str()?,
                })
            } else {
                None
            }
        })
}

fn is_proof_artifact_kind(kind: &str) -> bool {
    matches!(kind, "lean_module" | "lean_proof" | "lean_proof_term")
}

fn artifact_ref_slices_equal(left: &[CheckerArtifactRef], right: &[CheckerArtifactRef]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| artifact_refs_equal(left, right))
}

fn artifact_refs_equal(left: &CheckerArtifactRef, right: &CheckerArtifactRef) -> bool {
    left.kind == right.kind
        && left.uri == right.uri
        && left.digest == right.digest
        && left.media_type == right.media_type
        && placeholder_transport_equal(left, right)
}

fn placeholder_transport_equal(left: &CheckerArtifactRef, right: &CheckerArtifactRef) -> bool {
    match (&left.placeholder_transport, &right.placeholder_transport) {
        (Some(left), Some(right)) => left.accepted == right.accepted && left.note == right.note,
        (None, None) => true,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use crate::certified_pass_checker::{
        CheckerArtifactRef, Lean5CheckerMode, Lean5CheckerPolicy, PlaceholderTransportEvidence,
    };

    use super::*;

    /// Build a verified `Lean5PassCertificateCheckRequest` for the
    /// gamma-vnncomp-demo chain entry at `certificate_index`.
    ///
    /// The previous unit-test scaffold loaded JSON fixtures from
    /// `reports/fixtures/gamma_vnncomp_demo_*_request.json`. Those fixtures
    /// are not part of the open-source baseline. The unit tests synthesize
    /// equivalent requests in-process, mirroring the shape the production
    /// certified pass chain writes for an trust-cg-opt local certified pass
    /// run (`Compiler::certified_pass_check_request` in trust-cg-codegen).
    fn gamma_demo_request(certificate_index: u64) -> Lean5PassCertificateCheckRequest {
        let (pass_name, pass_instance_id, local_checker_name) = match certificate_index {
            0 => (
                "const-fold-bv64",
                "const-fold:bv64:v1",
                "analytical-bv64 const-fold checker",
            ),
            1 => (
                "dce-pure-unused",
                "dce:pure-unused:v1",
                "trust-cg-opt dce checker",
            ),
            other => panic!("unsupported gamma demo certificate_index: {other}"),
        };
        let function_name = "gamma_vnncomp_demo";
        let compilation_unit = "gamma-vnncomp-demo";
        let obligation_hash =
            format!("trust-cg-opt-certified-pass-run-v1:{compilation_unit}:{pass_instance_id}");

        let run_record = serde_json::json!({
            "format_version": "trust-cg.opt.certified_pass_run.v1",
            "pass_name": pass_name,
            "pass_version": 1,
            "pass_instance_id": pass_instance_id,
            "function_name": function_name,
            "changed": false,
            "status": "verified",
            "certificate_count": 0,
            "failure_count": 0,
            "obligation_hash": obligation_hash.as_str(),
            "local_checker": {
                "kind": "trust-cg-opt-local",
                "name": local_checker_name,
                "version": "1",
                "status": "verified",
            },
            "summary": {
                "changed": false,
                "certificates": [],
                "failures": [],
            },
        });

        let run_record_bytes = serde_json::to_vec(&run_record).expect("run record JSON serializes");
        let run_record_digest = sha256_hex(&run_record_bytes);
        let run_record_uri = format!("trust-cg-opt://certified-pass-run/{run_record_digest}.json");
        let proof_digest = sha256_hex(
            format!("{pass_instance_id}:{obligation_hash}:{run_record_digest}").as_bytes(),
        );
        let proof_uri = format!(
            "builtin://trust-cg-opt/certified-pass-run/{pass_instance_id}/placeholder-lean5"
        );

        let canonical_obligation = CheckerArtifactRef {
            kind: "canonical_obligation".to_string(),
            uri: run_record_uri,
            digest: format!("sha256:{run_record_digest}"),
            media_type: Some("application/json".to_string()),
            placeholder_transport: None,
        };
        let proof_artifact = CheckerArtifactRef {
            kind: "lean_module".to_string(),
            uri: proof_uri,
            digest: format!("sha256:{proof_digest}"),
            media_type: Some("text/plain".to_string()),
            placeholder_transport: Some(PlaceholderTransportEvidence {
                accepted: true,
                note: "Transport check for an trust-cg-opt local certified pass run; semantic Lean replay is not part of this bounded slice.".to_string(),
            }),
        };
        let artifacts = vec![canonical_obligation, proof_artifact];
        let certificate_artifacts =
            serde_json::to_value(&artifacts).expect("artifacts JSON serializes");

        let certificate = serde_json::json!({
            "format_version": "trust-cg.certified_pass.v1",
            "pass": {
                "name": pass_name,
                "version": "1",
                "implementation_commit": "workspace-local",
                "instance_id": pass_instance_id,
                "pipeline_ordinal": certificate_index + 1,
                "target_profile": {
                    "triple": "synthetic-gamma-demo",
                    "cpu": "unspecified",
                    "features": [],
                },
                "options_hash": format!("sha256:{}", sha256_hex(b"O2")),
            },
            "provenance": {
                "source": {
                    "program_id": format!(
                        "trust-cg://{compilation_unit}/{function_name}/before/{pass_instance_id}"
                    ),
                    "node_ids": [],
                    "expression_digest": obligation_hash.as_str(),
                },
                "rewrite": {
                    "program_id": format!(
                        "trust-cg://{compilation_unit}/{function_name}/after/{pass_instance_id}"
                    ),
                    "node_ids": [],
                    "expression_digest": obligation_hash.as_str(),
                },
            },
            "contract": {
                "mode": "local_pass_certificate_summary",
                "semantic_policy": {
                    "source": "trust-cg-opt certified wrapper",
                    "fail_closed": true,
                },
            },
            "domain": {
                "kind": "machine-ir",
                "certified_pass_run": &run_record,
            },
            "obligation_hash": obligation_hash.as_str(),
            "checker": {
                "kind": "lean5",
                "name": "trust-cg-cert-check",
                "version": "0.1.0",
                "proof_family": "trust-cg-opt-local-certified-pass-run-v1",
                "invocation": {
                    "mode": "in_process",
                    "command": ["trust-cg-codegen", "production-certified-pass-chain"],
                    "working_directory_policy": "process",
                },
                "limits": {"timeout_ms": 1000},
                "replay_inputs": certificate_artifacts.clone(),
                "trust_base": [
                    "lean5-kernel",
                    "trust-cg-opt-local-certified-pass-run",
                    "placeholder-transport-fixture",
                ],
            },
            "result": {
                "status": "verified",
                "checked_at_unix": 0,
                "duration_ms": 0,
                "local_checker": &run_record["local_checker"],
                "certificate_count": 0,
                "failure_count": 0,
            },
            "artifacts": {"refs": certificate_artifacts},
            "chain": {
                "compilation_unit": compilation_unit,
                "certificate_index": certificate_index,
                "must_be_verified": true,
            },
        });

        Lean5PassCertificateCheckRequest {
            format_version: "trust-cg.lean5_pass_check.request.v1".to_string(),
            certificate,
            obligation_hash,
            policy: Lean5CheckerPolicy {
                checker: "lean5".to_string(),
                mode: Lean5CheckerMode::PlaceholderTransport,
                timeout_ms: 1000,
                fail_closed: true,
                expected_lean_version: Some("Lean 5.0.0-placeholder".to_string()),
                lean5_binary: None,
            },
            artifacts,
        }
    }

    fn sha256_hex(bytes: &[u8]) -> String {
        use sha2::{Digest, Sha256};
        let mut hasher = Sha256::new();
        hasher.update(bytes);
        hasher
            .finalize()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect()
    }

    #[test]
    fn accepts_gamma_fixture_chain() {
        let chain =
            CertifiedPassChain::check_requests(vec![gamma_demo_request(0), gamma_demo_request(1)])
                .expect("verified gamma synthetic chain should validate");

        assert_eq!(chain.compilation_unit(), "gamma-vnncomp-demo");
        assert_eq!(chain.entries().len(), 2);
        assert_eq!(chain.entries()[0].certificate_index(), Some(0));
        assert_eq!(chain.entries()[1].certificate_index(), Some(1));
    }

    #[test]
    fn rejects_tampered_report_summary() {
        let request = gamma_demo_request(0);
        let mut report = check_lean5_pass_certificate(&request);
        report.replay.fail_closed = false;

        let err = CertifiedPassChain::from_entries(vec![CertifiedPassChainEntry::from_report(
            request, report,
        )])
        .expect_err("tampered report summary must be rejected");

        assert!(matches!(
            err,
            CertifiedPassChainError::TamperedReportSummary { entry_index: 0, .. }
        ));
    }
}
