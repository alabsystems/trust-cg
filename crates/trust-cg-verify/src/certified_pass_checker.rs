// trust-cg-verify/certified_pass_checker.rs - Certified pass checker hook
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! File/library hook for checking certified compiler-pass certificates.
//!
//! This module is the first Lean5-facing boundary for gamma-crown pass
//! certificates. It validates the transport shape and fail-closed policy around
//! `trust-cg.certified_pass.v1` certificates. Semantic replay validates a pinned
//! Lean artifact and invokes Lean5 fail-closed; `placeholder_transport` remains
//! available only for fixture transport checks.

use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::process::{Command, ExitStatus, Stdio};
use std::time::Duration;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};
use thiserror::Error;

const REQUEST_FORMAT_VERSION: &str = "trust-cg.lean5_pass_check.request.v1";
const CERTIFICATE_FORMAT_VERSION: &str = "trust-cg.certified_pass.v1";

/// Request object accepted by the Lean5 pass-certificate checker hook.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Lean5PassCertificateCheckRequest {
    /// Request schema version.
    pub format_version: String,
    /// Full `trust-cg.certified_pass.v1` certificate object.
    pub certificate: Value,
    /// Stable obligation hash expected by the caller.
    pub obligation_hash: String,
    /// Checker policy controlling fail-closed behavior and replay mode.
    pub policy: Lean5CheckerPolicy,
    /// Artifact references supplied by the caller for replay.
    #[serde(default)]
    pub artifacts: Vec<CheckerArtifactRef>,
}

/// Checker policy for one Lean5 pass-certificate check.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Lean5CheckerPolicy {
    /// Checker kind. Must be `lean5`.
    pub checker: String,
    /// Replay mode. `semantic` invokes Lean5 fail-closed.
    pub mode: Lean5CheckerMode,
    /// Maximum checker time.
    pub timeout_ms: u64,
    /// Fail-closed switch. Must be true for certified compiles.
    pub fail_closed: bool,
    /// Optional caller-pinned Lean version.
    #[serde(default)]
    pub expected_lean_version: Option<String>,
    /// Optional Lean5 executable path. If omitted, the checker tries
    /// `TRUST_CG_LEAN5`, `LEAN5`, the local development release binary, then
    /// `lean5` on PATH.
    #[serde(default)]
    pub lean5_binary: Option<String>,
}

/// Lean5 checker execution mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Lean5CheckerMode {
    /// Real Lean semantic replay through a pinned Lean module artifact.
    Semantic,
    /// Fixture-only transport check; does not prove certificate semantics.
    PlaceholderTransport,
}

/// Artifact reference used by the checker hook request.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckerArtifactRef {
    /// Artifact role, for example `lean_module` or `canonical_obligation`.
    pub kind: String,
    /// Artifact URI or repo-relative path.
    pub uri: String,
    /// Content digest such as `sha256:<hex>`.
    pub digest: String,
    /// Media type, when known.
    #[serde(default)]
    pub media_type: Option<String>,
    /// Fixture-only signal used in `placeholder_transport` mode.
    #[serde(default)]
    pub placeholder_transport: Option<PlaceholderTransportEvidence>,
}

/// Fixture-only evidence marker. This is intentionally not semantic proof.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PlaceholderTransportEvidence {
    /// Whether the fixture proof artifact should be accepted by transport.
    pub accepted: bool,
    /// Human-readable note stating what was checked.
    pub note: String,
}

/// Checker report emitted by the library hook or file wrapper.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Lean5PassCertificateCheckReport {
    /// Report schema version.
    pub format_version: String,
    /// Checked obligation hash.
    pub obligation_hash: String,
    /// Final fail-closed checker result.
    pub result: Lean5CheckerResult,
    /// Lean version metadata recorded for replay.
    pub lean5: Lean5VersionMetadata,
    /// Proof artifact used by replay, if present.
    pub proof_artifact: Option<ProofArtifactIdentity>,
    /// Replay metadata needed by external certificate-chain tooling.
    pub replay: ReplayMetadata,
}

/// Result status and details for one Lean5 pass-certificate check.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum Lean5CheckerResult {
    /// The checker accepted the obligation under the selected policy.
    Verified,
    /// Validation or checker replay failed.
    Failed { reason: String },
    /// Checker exceeded its limit.
    Timeout { timeout_ms: u64 },
    /// Checker was not attempted.
    Skipped { reason: String },
}

impl Lean5CheckerResult {
    /// Returns true only for verified results.
    pub fn is_verified(&self) -> bool {
        matches!(self, Lean5CheckerResult::Verified)
    }
}

/// Lean version metadata in the checker report.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Lean5VersionMetadata {
    /// Version string observed or requested.
    pub version: String,
    /// Whether this was observed from an actual Lean binary.
    pub observed: bool,
}

/// Identity of the Lean proof artifact selected for replay.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofArtifactIdentity {
    /// Artifact kind.
    pub kind: String,
    /// Artifact URI.
    pub uri: String,
    /// Artifact digest.
    pub digest: String,
}

/// Replay metadata attached to every report status.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReplayMetadata {
    /// Checker kind.
    pub checker: String,
    /// Checker mode.
    pub mode: Lean5CheckerMode,
    /// Whether the report preserves fail-closed policy.
    pub fail_closed: bool,
    /// Unix epoch seconds when the check was performed.
    pub checked_at_unix: u64,
    /// Checker duration.
    pub duration_ms: u64,
    /// Caller-provided artifact refs considered during replay.
    pub replay_inputs: Vec<CheckerArtifactRef>,
}

/// Errors from reading or parsing checker hook requests/reports.
#[derive(Debug, Error)]
pub enum Lean5CheckerError {
    /// Filesystem read/write failed.
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    /// JSON parse/serialize failed.
    #[error("JSON error: {0}")]
    Json(#[from] serde_json::Error),
}

/// Check a pass certificate request from a JSON file.
pub fn check_lean5_pass_certificate_file(
    path: impl AsRef<Path>,
) -> Result<Lean5PassCertificateCheckReport, Lean5CheckerError> {
    let input = fs::read_to_string(path)?;
    let request: Lean5PassCertificateCheckRequest = serde_json::from_str(&input)?;
    Ok(check_lean5_pass_certificate(&request))
}

/// Write a checker report as pretty JSON.
pub fn write_lean5_pass_certificate_report(
    report: &Lean5PassCertificateCheckReport,
    path: impl AsRef<Path>,
) -> Result<(), Lean5CheckerError> {
    let output = serde_json::to_string_pretty(report)?;
    fs::write(path, output)?;
    Ok(())
}

/// Check one pass certificate with the Lean5 hook policy.
pub fn check_lean5_pass_certificate(
    request: &Lean5PassCertificateCheckRequest,
) -> Lean5PassCertificateCheckReport {
    let start = Instant::now();
    let classified = classify_request(request);
    build_report(request, classified, start.elapsed().as_millis() as u64)
}

struct ClassifiedRequest {
    result: Lean5CheckerResult,
    lean5: Lean5VersionMetadata,
}

fn classify_request(request: &Lean5PassCertificateCheckRequest) -> ClassifiedRequest {
    let default_lean5 = Lean5VersionMetadata {
        version: request
            .policy
            .expected_lean_version
            .clone()
            .unwrap_or_else(|| "lean5-unavailable".to_string()),
        observed: false,
    };

    if request.policy.timeout_ms == 0 {
        return failed("policy.timeout_ms must be greater than zero", default_lean5);
    }

    if request.format_version != REQUEST_FORMAT_VERSION {
        return failed(
            format!(
                "unsupported request format_version '{}'",
                request.format_version
            ),
            default_lean5,
        );
    }

    if request.policy.checker != "lean5" {
        return failed(
            format!("unsupported checker '{}'", request.policy.checker),
            default_lean5,
        );
    }

    if !request.policy.fail_closed {
        return failed("policy.fail_closed must be true", default_lean5);
    }

    if certificate_string(&request.certificate, &["format_version"])
        != Some(CERTIFICATE_FORMAT_VERSION)
    {
        return failed(
            "certificate.format_version must be trust-cg.certified_pass.v1",
            default_lean5,
        );
    }

    let cert_hash = certificate_string(&request.certificate, &["obligation_hash"]);
    if cert_hash != Some(request.obligation_hash.as_str()) {
        return failed(
            "request obligation_hash does not match certificate.obligation_hash",
            default_lean5,
        );
    }

    if certificate_string(&request.certificate, &["checker", "kind"]) != Some("lean5") {
        return failed("certificate.checker.kind must be lean5", default_lean5);
    }

    if certificate_bool(&request.certificate, &["chain", "must_be_verified"]) != Some(true) {
        return failed(
            "certificate.chain.must_be_verified must be true",
            default_lean5,
        );
    }

    let cert_status = certificate_string(&request.certificate, &["result", "status"]);
    if cert_status != Some("verified") {
        return failed(
            format!(
                "certificate result status is not verified: {}",
                cert_status.unwrap_or("<missing>")
            ),
            default_lean5,
        );
    }

    let Some(proof_artifact) = proof_artifact(request) else {
        return failed("missing Lean proof artifact reference", default_lean5);
    };

    match request.policy.mode {
        Lean5CheckerMode::Semantic => run_semantic_lean5_replay(request, proof_artifact),
        Lean5CheckerMode::PlaceholderTransport => match &proof_artifact.placeholder_transport {
            Some(evidence) if evidence.accepted => ClassifiedRequest {
                result: Lean5CheckerResult::Verified,
                lean5: default_lean5,
            },
            Some(evidence) => failed(
                format!(
                    "placeholder transport rejected proof artifact: {}",
                    evidence.note
                ),
                default_lean5,
            ),
            None => failed(
                "placeholder_transport mode requires explicit fixture evidence",
                default_lean5,
            ),
        },
    }
}

fn failed(reason: impl Into<String>, lean5: Lean5VersionMetadata) -> ClassifiedRequest {
    ClassifiedRequest {
        result: Lean5CheckerResult::Failed {
            reason: reason.into(),
        },
        lean5,
    }
}

fn build_report(
    request: &Lean5PassCertificateCheckRequest,
    classified: ClassifiedRequest,
    duration_ms: u64,
) -> Lean5PassCertificateCheckReport {
    Lean5PassCertificateCheckReport {
        format_version: "trust-cg.lean5_pass_check.report.v1".to_string(),
        obligation_hash: request.obligation_hash.clone(),
        result: classified.result,
        lean5: classified.lean5,
        proof_artifact: proof_artifact(request).map(|artifact| ProofArtifactIdentity {
            kind: artifact.kind.clone(),
            uri: artifact.uri.clone(),
            digest: artifact.digest.clone(),
        }),
        replay: ReplayMetadata {
            checker: request.policy.checker.clone(),
            mode: request.policy.mode,
            fail_closed: request.policy.fail_closed,
            checked_at_unix: unix_now(),
            duration_ms,
            replay_inputs: request.artifacts.clone(),
        },
    }
}

fn run_semantic_lean5_replay(
    request: &Lean5PassCertificateCheckRequest,
    proof_artifact: &CheckerArtifactRef,
) -> ClassifiedRequest {
    let default_lean5 = Lean5VersionMetadata {
        version: request
            .policy
            .expected_lean_version
            .clone()
            .unwrap_or_else(|| "lean5-unavailable".to_string()),
        observed: false,
    };

    let lean_module = match resolve_repo_artifact_path(&proof_artifact.uri) {
        Ok(path) => path,
        Err(reason) => return failed(reason, default_lean5),
    };

    match sha256_file_prefixed(&lean_module) {
        Ok(actual) if actual == proof_artifact.digest => {}
        Ok(actual) => {
            return failed(
                format!(
                    "Lean proof artifact digest mismatch: expected {}, got {}",
                    proof_artifact.digest, actual
                ),
                default_lean5,
            );
        }
        Err(reason) => return failed(reason, default_lean5),
    }

    let lean5_binary = resolve_lean5_binary(&request.policy);
    let version_result = run_lean5_version_check(
        &lean5_binary,
        lean5_version_timeout_ms(&request.policy),
        &request.policy.expected_lean_version,
    );

    let lean5_metadata = match version_result {
        Lean5VersionCheck::Observed(version) => Lean5VersionMetadata {
            version,
            observed: true,
        },
        Lean5VersionCheck::Failed(reason) => return failed(reason, default_lean5),
        Lean5VersionCheck::Unavailable => default_lean5,
    };

    match run_command_with_timeout(
        &lean5_binary,
        &["check", lean_module.to_string_lossy().as_ref()],
        request.policy.timeout_ms,
    ) {
        LeanCommandOutcome::Completed {
            status,
            stdout,
            stderr,
        } if status.success() => {
            if output_contains_explicit_sorry(&stdout, &stderr) {
                return failed(
                    "Lean5 semantic replay reported explicit sorry trust debt",
                    lean5_metadata,
                );
            }
            ClassifiedRequest {
                result: Lean5CheckerResult::Verified,
                lean5: lean5_metadata,
            }
        }
        LeanCommandOutcome::Completed {
            status,
            stdout,
            stderr,
        } => {
            if output_contains_explicit_sorry(&stdout, &stderr) {
                return failed(
                    "Lean5 semantic replay reported explicit sorry trust debt",
                    lean5_metadata,
                );
            }
            failed(
                format!(
                    "Lean5 semantic replay failed with status {}{}",
                    status_text(status),
                    command_output_snippet(&stdout, &stderr)
                ),
                lean5_metadata,
            )
        }
        LeanCommandOutcome::Timeout => ClassifiedRequest {
            result: Lean5CheckerResult::Timeout {
                timeout_ms: request.policy.timeout_ms,
            },
            lean5: lean5_metadata,
        },
        LeanCommandOutcome::SpawnError(reason) => failed(reason, lean5_metadata),
    }
}

enum Lean5VersionCheck {
    Observed(String),
    Failed(String),
    Unavailable,
}

fn run_lean5_version_check(
    lean5_binary: &str,
    timeout_ms: u64,
    expected: &Option<String>,
) -> Lean5VersionCheck {
    match run_command_with_timeout(lean5_binary, &["--version"], timeout_ms) {
        LeanCommandOutcome::Completed {
            status,
            stdout,
            stderr: _,
        } if status.success() => {
            let observed = stdout.trim().to_string();
            if observed.is_empty() {
                return Lean5VersionCheck::Unavailable;
            }
            if let Some(expected) = expected
                && observed != *expected
            {
                return Lean5VersionCheck::Failed(format!(
                    "Lean5 version mismatch: expected '{}', got '{}'",
                    expected, observed
                ));
            }
            Lean5VersionCheck::Observed(observed)
        }
        LeanCommandOutcome::Completed { stderr, .. } if expected.is_some() => {
            Lean5VersionCheck::Failed(format!(
                "Lean5 version check failed{}",
                command_output_snippet("", &stderr)
            ))
        }
        LeanCommandOutcome::Timeout if expected.is_some() => Lean5VersionCheck::Failed(format!(
            "Lean5 version check timed out after {timeout_ms}ms"
        )),
        LeanCommandOutcome::SpawnError(reason) if expected.is_some() => {
            Lean5VersionCheck::Failed(reason)
        }
        _ => Lean5VersionCheck::Unavailable,
    }
}

fn lean5_version_timeout_ms(policy: &Lean5CheckerPolicy) -> u64 {
    if policy
        .lean5_binary
        .as_deref()
        .is_some_and(|binary| !binary.is_empty())
    {
        policy.timeout_ms
    } else {
        policy.timeout_ms.min(1_000)
    }
}

enum LeanCommandOutcome {
    Completed {
        status: ExitStatus,
        stdout: String,
        stderr: String,
    },
    Timeout,
    SpawnError(String),
}

fn run_command_with_timeout(program: &str, args: &[&str], timeout_ms: u64) -> LeanCommandOutcome {
    let mut child = match Command::new(program)
        .args(args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(child) => child,
        Err(err) => {
            return LeanCommandOutcome::SpawnError(format!(
                "failed to spawn Lean5 binary '{}': {}",
                program, err
            ));
        }
    };

    let deadline = Instant::now() + Duration::from_millis(timeout_ms);
    loop {
        match child.try_wait() {
            Ok(Some(_)) => match child.wait_with_output() {
                Ok(output) => {
                    return LeanCommandOutcome::Completed {
                        status: output.status,
                        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
                        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
                    };
                }
                Err(err) => {
                    return LeanCommandOutcome::SpawnError(format!(
                        "failed to collect Lean5 output: {err}"
                    ));
                }
            },
            Ok(None) if Instant::now() >= deadline => {
                let _ = child.kill();
                let _ = child.wait();
                return LeanCommandOutcome::Timeout;
            }
            Ok(None) => std::thread::sleep(Duration::from_millis(5)),
            Err(err) => {
                let _ = child.kill();
                let _ = child.wait();
                return LeanCommandOutcome::SpawnError(format!(
                    "failed while waiting for Lean5 process: {err}"
                ));
            }
        }
    }
}

fn resolve_lean5_binary(policy: &Lean5CheckerPolicy) -> String {
    if let Some(binary) = &policy.lean5_binary
        && !binary.is_empty()
    {
        return binary.clone();
    }
    for env_key in ["TRUST_CG_LEAN5", "LEAN5"] {
        if let Ok(binary) = std::env::var(env_key)
            && !binary.is_empty()
        {
            return binary;
        }
    }
    if let Some(home) = std::env::var_os("HOME") {
        let local_release = PathBuf::from(home).join("lean5/target/user/release/lean5");
        if local_release.exists() {
            return local_release.to_string_lossy().into_owned();
        }
    }
    "lean5".to_string()
}

fn resolve_repo_artifact_path(uri: &str) -> Result<PathBuf, String> {
    if uri.contains("://") {
        return Err(format!(
            "semantic Lean5 replay requires a file artifact, got URI '{uri}'"
        ));
    }

    let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|err| format!("failed to resolve Trust Codegen repo root: {err}"))?;
    let candidate = if Path::new(uri).is_absolute() {
        PathBuf::from(uri)
    } else {
        repo_root.join(uri)
    };
    let canonical = candidate
        .canonicalize()
        .map_err(|err| format!("failed to resolve Lean proof artifact '{uri}': {err}"))?;
    if !canonical.starts_with(&repo_root) {
        return Err(format!(
            "Lean proof artifact '{}' resolves outside Trust Codegen repo root",
            uri
        ));
    }
    Ok(canonical)
}

fn sha256_file_prefixed(path: &Path) -> Result<String, String> {
    let bytes = fs::read(path).map_err(|err| {
        format!(
            "failed to read Lean proof artifact '{}': {err}",
            path.display()
        )
    })?;
    Ok(sha256_prefixed(&bytes))
}

fn sha256_prefixed(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity("sha256:".len() + digest.len() * 2);
    out.push_str("sha256:");
    for byte in digest {
        out.push_str(&format!("{byte:02x}"));
    }
    out
}

fn command_output_snippet(stdout: &str, stderr: &str) -> String {
    let combined = format!("{}{}", stdout, stderr);
    let trimmed = combined.trim();
    if trimmed.is_empty() {
        String::new()
    } else {
        let snippet: String = trimmed.chars().take(240).collect();
        format!(": {snippet}")
    }
}

fn output_contains_explicit_sorry(stdout: &str, stderr: &str) -> bool {
    stdout.contains("explicit sorry") || stderr.contains("explicit sorry")
}

fn status_text(status: ExitStatus) -> String {
    status
        .code()
        .map(|code| code.to_string())
        .unwrap_or_else(|| "signal".to_string())
}

fn unix_now() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs()
}

fn proof_artifact(request: &Lean5PassCertificateCheckRequest) -> Option<&CheckerArtifactRef> {
    request
        .artifacts
        .iter()
        .find(|artifact| matches!(artifact.kind.as_str(), "lean_module" | "lean_proof"))
}

fn certificate_string<'a>(value: &'a Value, path: &[&str]) -> Option<&'a str> {
    let mut cursor = value;
    for segment in path {
        cursor = cursor.get(*segment)?;
    }
    cursor.as_str()
}

fn certificate_bool(value: &Value, path: &[&str]) -> Option<bool> {
    let mut cursor = value;
    for segment in path {
        cursor = cursor.get(*segment)?;
    }
    cursor.as_bool()
}
