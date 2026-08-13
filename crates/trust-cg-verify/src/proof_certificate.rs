// trust-cg-verify/proof_certificate.rs - Proof certificate chain
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Proof certificates record the outcome of verification proofs so they can be
// persisted, inspected, and chained together. They connect tRust's
// TrustDisposition to Trust Codegen's verification proofs by providing a serializable
// evidence trail.
//
// A CertificateChain collects all proof certificates for a compilation unit
// (e.g., a function) and can be serialized to/from JSON for persistence.
//
// Reference: designs/2026-04-13-verification-architecture.md

//! Proof certificate chain for verification persistence.
//!
//! [`ProofCertificate`] records the outcome of a single proof obligation,
//! including the solver used, verification strength, duration, and a formula
//! hash for cache invalidation.
//!
//! [`CertificateChain`] collects certificates for a compilation unit and
//! provides JSON serialization for persistence and inspection.
//!
//! # Example
//!
//! ```rust
//! use trust_cg_verify::proof_certificate::{
//!     generate_certificate, generate_certificate_chain, CertificateResult,
//! };
//! use trust_cg_verify::lowering_proof::proof_iadd_i8;
//!
//! let obligation = proof_iadd_i8();
//! let cert = generate_certificate(&obligation);
//! assert_eq!(cert.result, CertificateResult::Verified);
//!
//! let chain = generate_certificate_chain("test_fn", &[obligation]);
//! assert!(chain.all_verified());
//! ```

use std::collections::HashMap;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};
use thiserror::Error;

use trust_cg_opt::cache::StableHasher;

use crate::lowering_proof::{ProofObligation, TransvalCheckKind, verify_by_evaluation};
use crate::verify::{VerificationResult, VerificationStrength};

// ---------------------------------------------------------------------------
// CertificateResult
// ---------------------------------------------------------------------------

/// Outcome of a single proof certificate.
#[derive(Debug, Clone, PartialEq)]
pub enum CertificateResult {
    /// Proof succeeded -- property holds for all inputs.
    Verified,
    /// Proof failed -- counterexample found.
    Failed { counterexample: String },
    /// Solver timed out before reaching a conclusion.
    Timeout { seconds: f64 },
    /// Proof was not attempted.
    Skipped { reason: String },
}

impl CertificateResult {
    /// Returns true if the result is Verified.
    pub fn is_verified(&self) -> bool {
        matches!(self, CertificateResult::Verified)
    }

    /// Returns a short string tag for serialization.
    fn tag(&self) -> &'static str {
        match self {
            CertificateResult::Verified => "verified",
            CertificateResult::Failed { .. } => "failed",
            CertificateResult::Timeout { .. } => "timeout",
            CertificateResult::Skipped { .. } => "skipped",
        }
    }
}

impl std::fmt::Display for CertificateResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CertificateResult::Verified => write!(f, "Verified"),
            CertificateResult::Failed { counterexample } => {
                write!(f, "Failed({})", counterexample)
            }
            CertificateResult::Timeout { seconds } => write!(f, "Timeout({:.2}s)", seconds),
            CertificateResult::Skipped { reason } => write!(f, "Skipped({})", reason),
        }
    }
}

// ---------------------------------------------------------------------------
// SolverUsed
// ---------------------------------------------------------------------------

/// Which solver backend was used for verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SolverUsed {
    /// Exhaustive concrete evaluation (all input combinations).
    MockExhaustive,
    /// Random sampling with the given number of samples.
    MockStatistical { samples: u64 },
    /// ay CLI subprocess.
    AYCli,
    /// ay in-process native API.
    AYNative,
    /// z3 CLI subprocess.
    Z3Cli,
}

impl SolverUsed {
    /// Returns a short string tag for serialization.
    fn tag(&self) -> &'static str {
        match self {
            SolverUsed::MockExhaustive => "mock_exhaustive",
            SolverUsed::MockStatistical { .. } => "mock_statistical",
            SolverUsed::AYCli => "ay_cli",
            SolverUsed::AYNative => "ay_native",
            SolverUsed::Z3Cli => "z3_cli",
        }
    }
}

impl std::fmt::Display for SolverUsed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SolverUsed::MockExhaustive => write!(f, "MockExhaustive"),
            SolverUsed::MockStatistical { samples } => {
                write!(f, "MockStatistical({})", samples)
            }
            SolverUsed::AYCli => write!(f, "AYCli"),
            SolverUsed::AYNative => write!(f, "AYNative"),
            SolverUsed::Z3Cli => write!(f, "Z3Cli"),
        }
    }
}

// ---------------------------------------------------------------------------
// ProofCertificate
// ---------------------------------------------------------------------------

/// A certificate recording the outcome of verifying a single proof obligation.
#[derive(Debug, Clone)]
pub struct ProofCertificate {
    /// Name of the proof obligation (e.g., "Iadd_I32 -> ADDWrr").
    pub obligation_name: String,
    /// Verification outcome.
    pub result: CertificateResult,
    /// Which solver backend was used.
    pub solver: SolverUsed,
    /// Strength of the verification applied.
    pub strength: VerificationStrength,
    /// Proof category from the obligation (if set).
    pub check_kind: Option<TransvalCheckKind>,
    /// Hash of the negated equivalence formula, for cache invalidation.
    pub formula_hash: u64,
    /// Unix epoch seconds when this certificate was generated.
    pub timestamp_epoch_secs: u64,
    /// Duration of the verification in milliseconds.
    pub duration_ms: u64,
}

// ---------------------------------------------------------------------------
// CertificateChain
// ---------------------------------------------------------------------------

/// An ordered collection of proof certificates for a compilation unit.
#[derive(Debug, Clone)]
pub struct CertificateChain {
    /// Name of the compilation unit (e.g., function name).
    pub compilation_unit: String,
    /// Ordered list of proof certificates.
    pub certificates: Vec<ProofCertificate>,
    /// Unix epoch seconds when this chain was created.
    pub created_epoch_secs: u64,
}

impl CertificateChain {
    /// Create a new empty certificate chain for the given compilation unit.
    pub fn new(compilation_unit: String) -> Self {
        let created = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();
        Self {
            compilation_unit,
            certificates: Vec::new(),
            created_epoch_secs: created,
        }
    }

    /// Add a certificate to the chain.
    pub fn add(&mut self, cert: ProofCertificate) {
        self.certificates.push(cert);
    }

    /// Verify the chain: check that all certificates are Verified.
    pub fn verify_chain(&self) -> ChainVerificationResult {
        if self.certificates.is_empty() {
            return ChainVerificationResult::Empty;
        }

        let summary = self.summary();

        if summary.failed == 0 && summary.timeout == 0 && summary.skipped == 0 {
            ChainVerificationResult::AllVerified {
                count: summary.verified,
            }
        } else {
            ChainVerificationResult::HasFailures {
                verified: summary.verified,
                failed: summary.failed,
                skipped: summary.skipped,
                timeout: summary.timeout,
            }
        }
    }

    /// Returns true if all certificates in the chain are Verified.
    pub fn all_verified(&self) -> bool {
        !self.certificates.is_empty() && self.certificates.iter().all(|c| c.result.is_verified())
    }

    /// Returns references to all failed certificates.
    pub fn failed_certificates(&self) -> Vec<&ProofCertificate> {
        self.certificates
            .iter()
            .filter(|c| matches!(c.result, CertificateResult::Failed { .. }))
            .collect()
    }

    /// Compute a summary of the chain.
    pub fn summary(&self) -> ChainSummary {
        let mut verified = 0;
        let mut failed = 0;
        let mut timeout = 0;
        let mut skipped = 0;
        let mut total_duration_ms = 0u64;

        for cert in &self.certificates {
            match &cert.result {
                CertificateResult::Verified => verified += 1,
                CertificateResult::Failed { .. } => failed += 1,
                CertificateResult::Timeout { .. } => timeout += 1,
                CertificateResult::Skipped { .. } => skipped += 1,
            }
            total_duration_ms = total_duration_ms.saturating_add(cert.duration_ms);
        }

        ChainSummary {
            total: self.certificates.len(),
            verified,
            failed,
            timeout,
            skipped,
            total_duration_ms,
        }
    }

    /// Serialize the chain to JSON (manual, no serde dependency).
    pub fn to_json(&self) -> String {
        let mut out = String::from("{\n");
        out.push_str(&format!(
            "  \"compilation_unit\": \"{}\",\n",
            escape_json(&self.compilation_unit)
        ));
        out.push_str(&format!(
            "  \"created_epoch_secs\": {},\n",
            self.created_epoch_secs
        ));
        out.push_str("  \"certificates\": [\n");

        for (i, cert) in self.certificates.iter().enumerate() {
            out.push_str("    {\n");
            out.push_str(&format!(
                "      \"obligation_name\": \"{}\",\n",
                escape_json(&cert.obligation_name)
            ));
            out.push_str(&format!("      \"result\": \"{}\",\n", cert.result.tag()));

            // Result detail (counterexample, timeout seconds, skip reason)
            match &cert.result {
                CertificateResult::Failed { counterexample } => {
                    out.push_str(&format!(
                        "      \"counterexample\": \"{}\",\n",
                        escape_json(counterexample)
                    ));
                }
                CertificateResult::Timeout { seconds } => {
                    out.push_str(&format!("      \"timeout_seconds\": {},\n", seconds));
                }
                CertificateResult::Skipped { reason } => {
                    out.push_str(&format!(
                        "      \"skip_reason\": \"{}\",\n",
                        escape_json(reason)
                    ));
                }
                CertificateResult::Verified => {}
            }

            out.push_str(&format!("      \"solver\": \"{}\",\n", cert.solver.tag()));

            // Solver detail (samples for statistical)
            if let SolverUsed::MockStatistical { samples } = &cert.solver {
                out.push_str(&format!("      \"solver_samples\": {},\n", samples));
            }

            out.push_str(&format!(
                "      \"strength\": \"{}\",\n",
                strength_to_tag(&cert.strength)
            ));
            if let VerificationStrength::Statistical { sample_count } = &cert.strength {
                out.push_str(&format!("      \"strength_samples\": {},\n", sample_count));
            }

            if let Some(kind) = &cert.check_kind {
                out.push_str(&format!("      \"check_kind\": \"{}\",\n", kind));
            }

            out.push_str(&format!("      \"formula_hash\": {},\n", cert.formula_hash));
            out.push_str(&format!(
                "      \"timestamp_epoch_secs\": {},\n",
                cert.timestamp_epoch_secs
            ));
            out.push_str(&format!("      \"duration_ms\": {}\n", cert.duration_ms));

            if i + 1 < self.certificates.len() {
                out.push_str("    },\n");
            } else {
                out.push_str("    }\n");
            }
        }

        out.push_str("  ]\n");
        out.push('}');
        out
    }

    /// Deserialize a chain from JSON (manual parsing, no serde dependency).
    pub fn from_json(json: &str) -> Result<Self, CertificateError> {
        let compilation_unit = extract_string_field(json, "compilation_unit")?;
        let created_epoch_secs = extract_u64_field(json, "created_epoch_secs")?;

        let certs_start = json
            .find("\"certificates\"")
            .ok_or_else(|| CertificateError::MissingField("certificates".to_string()))?;
        let array_start = json[certs_start..].find('[').ok_or_else(|| {
            CertificateError::JsonParseError("missing [ for certificates".to_string())
        })? + certs_start;
        let array_end = find_matching_bracket(json, array_start).ok_or_else(|| {
            CertificateError::JsonParseError("unmatched [ in certificates".to_string())
        })?;

        let array_content = &json[array_start + 1..array_end];
        let mut certificates = Vec::new();

        // Split on objects by finding matched { }
        let mut pos = 0;
        let bytes = array_content.as_bytes();
        while pos < bytes.len() {
            if bytes[pos] == b'{' {
                let obj_end = find_matching_brace(array_content, pos).ok_or_else(|| {
                    CertificateError::JsonParseError("unmatched { in certificate".to_string())
                })?;
                let obj_str = &array_content[pos..=obj_end];
                let cert = parse_certificate(obj_str)?;
                certificates.push(cert);
                pos = obj_end + 1;
            } else {
                pos += 1;
            }
        }

        Ok(CertificateChain {
            compilation_unit,
            certificates,
            created_epoch_secs,
        })
    }
}

impl std::fmt::Display for CertificateChain {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let summary = self.summary();
        write!(
            f,
            "CertificateChain({}: {}/{} verified, {} failed, {} timeout, {} skipped, {}ms)",
            self.compilation_unit,
            summary.verified,
            summary.total,
            summary.failed,
            summary.timeout,
            summary.skipped,
            summary.total_duration_ms
        )
    }
}

// ---------------------------------------------------------------------------
// ChainVerificationResult
// ---------------------------------------------------------------------------

/// Result of verifying an entire certificate chain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChainVerificationResult {
    /// All certificates are Verified.
    AllVerified { count: usize },
    /// Some certificates are not Verified.
    HasFailures {
        verified: usize,
        failed: usize,
        skipped: usize,
        timeout: usize,
    },
    /// The chain is empty (no certificates).
    Empty,
}

// ---------------------------------------------------------------------------
// ChainSummary
// ---------------------------------------------------------------------------

/// Summary statistics for a certificate chain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChainSummary {
    /// Total number of certificates.
    pub total: usize,
    /// Number of Verified certificates.
    pub verified: usize,
    /// Number of Failed certificates.
    pub failed: usize,
    /// Number of Timeout certificates.
    pub timeout: usize,
    /// Number of Skipped certificates.
    pub skipped: usize,
    /// Total verification duration in milliseconds.
    pub total_duration_ms: u64,
}

// ---------------------------------------------------------------------------
// Lowering certificates
// ---------------------------------------------------------------------------

/// Function-level certificate for a trust_ir-to-machine-code lowering.
///
/// This composes the existing per-obligation [`ProofCertificate`] entries into
/// the function-level shape tRust can consume via `trust-proof-cert` JSON. It is
/// emitted only from verified obligations; any failed, skipped, timed-out, or
/// uncategorized obligation rejects certificate construction.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LoweringCertificate {
    /// Stable schema tag for Trust Codegen lowering certificates.
    pub schema: String,
    /// Function name or other compilation-unit identity.
    pub function: String,
    /// Target triple/backend name for the emitted machine code.
    pub target: String,
    /// SHA-256 hash of the canonical trust_ir/function input bytes.
    pub trust_ir_hash: String,
    /// SHA-256 hash of emitted machine-code bytes.
    pub machine_code_hash: String,
    /// SHA-256 hash of compiler configuration bytes relevant to lowering.
    pub compiler_config_hash: String,
    /// Ordered proof records, one per lowering rule/obligation.
    pub rule_proofs: Vec<LoweringRuleProof>,
    /// Weakest proof strength among all included rules.
    pub overall_strength: LoweringProofStrength,
    /// Certificate-level result. Current lowering certificates are fail-closed.
    pub result: LoweringCertificateStatus,
    /// Aggregate solver information across all included obligations.
    pub solver: LoweringSolverSummary,
    /// Sum of per-obligation verification time.
    pub total_time_ms: u64,
    /// Unix epoch seconds when this certificate was created.
    pub created_epoch_secs: u64,
}

impl LoweringCertificate {
    /// Build a lowering certificate from an existing verified certificate chain.
    ///
    /// Prefer [`LoweringCertificateGenerator::generate`] when the original
    /// obligations are available; it records exhaustive finite-state counts for
    /// trust-proof-cert export. This chain-based path is useful for callers that
    /// have already run verification and only need fail-closed composition.
    pub fn from_verified_chain(
        function: &str,
        target: &str,
        trust_ir_bytes: &[u8],
        machine_code_bytes: &[u8],
        compiler_config_bytes: &[u8],
        chain: &CertificateChain,
    ) -> Result<Self, CertificateError> {
        Self::from_verified_chain_with_state_counts(
            function,
            target,
            trust_ir_bytes,
            machine_code_bytes,
            compiler_config_bytes,
            chain,
            &HashMap::new(),
        )
    }

    fn from_verified_chain_with_state_counts(
        function: &str,
        target: &str,
        trust_ir_bytes: &[u8],
        machine_code_bytes: &[u8],
        compiler_config_bytes: &[u8],
        chain: &CertificateChain,
        exhaustive_state_counts: &HashMap<String, u64>,
    ) -> Result<Self, CertificateError> {
        if chain.certificates.is_empty() {
            return Err(CertificateError::EmptyChain);
        }

        let mut rule_proofs = Vec::with_capacity(chain.certificates.len());
        let mut solver_names: Vec<&'static str> = Vec::with_capacity(chain.certificates.len());
        let mut total_time_ms = 0u64;

        for cert in &chain.certificates {
            let check_kind = cert
                .check_kind
                .ok_or_else(|| CertificateError::MissingCheckKind {
                    obligation_name: cert.obligation_name.clone(),
                })?;

            if !cert.result.is_verified() {
                return Err(CertificateError::UnverifiedObligation {
                    obligation_name: cert.obligation_name.clone(),
                    result: cert.result.to_string(),
                });
            }

            let state_count = exhaustive_state_counts.get(&cert.obligation_name).copied();
            let strength =
                LoweringProofStrength::from_verification_strength(&cert.strength, state_count);
            let solver = cert.solver.tag().to_string();
            let proof_hash = compute_rule_proof_hash(cert, check_kind, &strength);
            total_time_ms = total_time_ms.saturating_add(cert.duration_ms);
            solver_names.push(cert.solver.tag());

            rule_proofs.push(LoweringRuleProof {
                rule_name: cert.obligation_name.clone(),
                check_kind: check_kind.to_string(),
                result: LoweringVerification::Proved {
                    strength,
                    solver,
                    time_ms: cert.duration_ms,
                },
                obligation_hash: format!("{:016x}", cert.formula_hash),
                proof_hash,
            });
        }

        let overall_strength =
            weakest_lowering_strength(&rule_proofs).ok_or(CertificateError::EmptyChain)?;
        let solver_name = summarize_solver_names(&solver_names);

        Ok(Self {
            schema: "trust-cg.lowering_certificate.v1".to_string(),
            function: function.to_string(),
            target: target.to_string(),
            trust_ir_hash: sha256_hex(trust_ir_bytes),
            machine_code_hash: sha256_hex(machine_code_bytes),
            compiler_config_hash: sha256_hex(compiler_config_bytes),
            rule_proofs,
            overall_strength,
            result: LoweringCertificateStatus::Verified,
            solver: LoweringSolverSummary {
                name: solver_name,
                version: format!("trust-cg-verify {}", env!("CARGO_PKG_VERSION")),
                total_time_ms,
            },
            total_time_ms,
            created_epoch_secs: chain.created_epoch_secs,
        })
    }

    /// Serialize this lowering certificate to stable Trust Codegen JSON.
    pub fn to_json(&self) -> Result<String, CertificateError> {
        serde_json::to_string_pretty(self)
            .map_err(|e| CertificateError::SerializationError(e.to_string()))
    }

    /// Deserialize a lowering certificate from stable Trust Codegen JSON.
    pub fn from_json(json: &str) -> Result<Self, CertificateError> {
        serde_json::from_str(json).map_err(|e| CertificateError::JsonParseError(e.to_string()))
    }

    /// Export this certificate as JSON matching tRust `trust-proof-cert`
    /// `ProofCertificate` format version 2.
    ///
    /// Upstream assumptions captured by this stable transport:
    /// - `trust-proof-cert::ChainStepType::CodegenLowering` exists.
    /// - A missing signature is encoded as `null`; signing/certification is an
    ///   upstream tRust step, not an Trust Codegen lowering-verification claim.
    /// - Statistical Trust Codegen checks map to bounded proof strength, preserving
    ///   that they are not complete proofs.
    pub fn to_trust_proof_cert_json(&self) -> Result<String, CertificateError> {
        let value = self.to_trust_proof_cert_value()?;
        serde_json::to_string_pretty(&value)
            .map_err(|e| CertificateError::SerializationError(e.to_string()))
    }

    /// Build the serde JSON value for tRust `trust-proof-cert` consumption.
    pub fn to_trust_proof_cert_value(&self) -> Result<serde_json::Value, CertificateError> {
        let timestamp = epoch_secs_to_rfc3339(self.created_epoch_secs);
        let formula_json = self.trust_formula_json()?;
        let vc_hash = sha256_digest(format!("lowering_equivalence:{formula_json}").as_bytes());
        let vc_hash_hex = hex_bytes(&vc_hash);
        let certificate_id = sha256_hex(format!("{}:{timestamp}", self.function).as_bytes());
        let proof_bundle_hash = self.stable_hash()?;
        let trust_strength = self.overall_strength.to_trust_strength_json();
        let trust_evidence = self.overall_strength.to_trust_evidence_json();

        Ok(serde_json::json!({
            "id": certificate_id,
            "function": &self.function,
            "function_hash": &self.trust_ir_hash,
            "vc_hash": vc_hash.to_vec(),
            "vc_snapshot": {
                "kind": "lowering_equivalence",
                "formula_json": formula_json,
                "location": null,
            },
            "solver": {
                "name": &self.solver.name,
                "version": &self.solver.version,
                "time_ms": self.total_time_ms,
                "strength": trust_strength,
                "evidence": trust_evidence,
            },
            "proof_steps": [],
            "witness": null,
            "chain": {
                "steps": [
                    {
                        "step_type": "VcGeneration",
                        "tool": "trust-cg",
                        "tool_version": env!("CARGO_PKG_VERSION"),
                        "input_hash": &self.compiler_config_hash,
                        "output_hash": &vc_hash_hex,
                        "time_ms": 0,
                        "timestamp": &timestamp,
                    },
                    {
                        "step_type": "SolverProof",
                        "tool": &self.solver.name,
                        "tool_version": &self.solver.version,
                        "input_hash": &vc_hash_hex,
                        "output_hash": &self.trust_ir_hash,
                        "time_ms": self.total_time_ms,
                        "timestamp": &timestamp,
                    },
                    {
                        "step_type": "CodegenLowering",
                        "tool": "trust-cg",
                        "tool_version": env!("CARGO_PKG_VERSION"),
                        "input_hash": &self.trust_ir_hash,
                        "output_hash": &self.machine_code_hash,
                        "time_ms": self.total_time_ms,
                        "timestamp": &timestamp,
                    }
                ]
            },
            "proof_trace": [],
            "timestamp": &timestamp,
            "status": "Trusted",
            "version": 2,
            "signature": null,
            "trust_cg_lowering_certificate_hash": proof_bundle_hash,
        }))
    }

    /// Stable SHA-256 hash of the lowering certificate content that affects the
    /// proof claim. Timing and timestamp metadata are intentionally excluded.
    pub fn stable_hash(&self) -> Result<String, CertificateError> {
        let stable = LoweringStableHashView {
            schema: &self.schema,
            function: &self.function,
            target: &self.target,
            trust_ir_hash: &self.trust_ir_hash,
            machine_code_hash: &self.machine_code_hash,
            compiler_config_hash: &self.compiler_config_hash,
            rule_proofs: &self.rule_proofs,
            overall_strength: &self.overall_strength,
            result: &self.result,
        };
        let json = serde_json::to_string(&stable)
            .map_err(|e| CertificateError::SerializationError(e.to_string()))?;
        Ok(sha256_hex(json.as_bytes()))
    }

    fn trust_formula_json(&self) -> Result<String, CertificateError> {
        let summary = LoweringFormulaSummary {
            schema: "trust-cg.lowering_formula_summary.v1",
            function: &self.function,
            target: &self.target,
            trust_ir_hash: &self.trust_ir_hash,
            machine_code_hash: &self.machine_code_hash,
            compiler_config_hash: &self.compiler_config_hash,
            rule_proofs: &self.rule_proofs,
        };
        serde_json::to_string(&summary)
            .map_err(|e| CertificateError::SerializationError(e.to_string()))
    }
}

/// Generates fail-closed function-level lowering certificates from existing
/// Trust Codegen proof obligations.
#[derive(Debug, Clone)]
pub struct LoweringCertificateGenerator {
    target: String,
    compiler_config_bytes: Vec<u8>,
}

impl LoweringCertificateGenerator {
    /// Create a generator for a target/backend and canonical compiler config.
    pub fn new(target: impl Into<String>, compiler_config_bytes: impl AsRef<[u8]>) -> Self {
        Self {
            target: target.into(),
            compiler_config_bytes: compiler_config_bytes.as_ref().to_vec(),
        }
    }

    /// Verify obligations and emit a lowering certificate only if every
    /// obligation verifies and carries a `TransvalCheckKind`.
    pub fn generate(
        &self,
        function: &str,
        trust_ir_bytes: &[u8],
        machine_code_bytes: &[u8],
        obligations: &[ProofObligation],
    ) -> Result<LoweringCertificate, CertificateError> {
        let mut exhaustive_state_counts = HashMap::with_capacity(obligations.len());
        for obligation in obligations {
            exhaustive_state_counts.insert(
                obligation.name.clone(),
                exhaustive_input_state_count(obligation),
            );
        }

        let chain = generate_certificate_chain(function, obligations);
        LoweringCertificate::from_verified_chain_with_state_counts(
            function,
            &self.target,
            trust_ir_bytes,
            machine_code_bytes,
            &self.compiler_config_bytes,
            &chain,
            &exhaustive_state_counts,
        )
    }
}

/// Convenience wrapper around [`LoweringCertificateGenerator::generate`].
pub fn generate_lowering_certificate(
    function: &str,
    target: &str,
    trust_ir_bytes: &[u8],
    machine_code_bytes: &[u8],
    compiler_config_bytes: &[u8],
    obligations: &[ProofObligation],
) -> Result<LoweringCertificate, CertificateError> {
    LoweringCertificateGenerator::new(target, compiler_config_bytes).generate(
        function,
        trust_ir_bytes,
        machine_code_bytes,
        obligations,
    )
}

/// One verified lowering rule inside a [`LoweringCertificate`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LoweringRuleProof {
    /// Rule/proof obligation name.
    pub rule_name: String,
    /// Stable `TransvalCheckKind` tag.
    pub check_kind: String,
    /// Verification result. Lowering certificates only include proved rules.
    pub result: LoweringVerification,
    /// Stable hash of the proof obligation formula.
    pub obligation_hash: String,
    /// Stable hash of the rule proof claim.
    pub proof_hash: String,
}

/// Verification result included in a lowering certificate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum LoweringVerification {
    /// The lowering rule was proved/verified by Trust Codegen.
    Proved {
        /// Proof strength for this rule.
        strength: LoweringProofStrength,
        /// Solver/evaluator used for this rule.
        solver: String,
        /// Time spent on this rule in milliseconds.
        time_ms: u64,
    },
}

impl LoweringVerification {
    fn strength(&self) -> &LoweringProofStrength {
        match self {
            LoweringVerification::Proved { strength, .. } => strength,
        }
    }
}

/// Proof strength levels exposed by Trust Codegen lowering certificates.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum LoweringProofStrength {
    /// Random/edge-case sampling; not a complete proof.
    Sampled { sample_count: u64 },
    /// Exhaustive finite-state checking for the obligation input space.
    ///
    /// `state_count == None` means the certificate was composed from an older
    /// chain that no longer carried the original obligation input widths.
    ExhaustiveFinite { state_count: Option<u64> },
    /// SMT solver returned UNSAT.
    SmtUnsat,
}

impl LoweringProofStrength {
    fn from_verification_strength(
        strength: &VerificationStrength,
        state_count: Option<u64>,
    ) -> Self {
        match strength {
            VerificationStrength::Exhaustive => {
                LoweringProofStrength::ExhaustiveFinite { state_count }
            }
            VerificationStrength::Statistical { sample_count } => LoweringProofStrength::Sampled {
                sample_count: *sample_count,
            },
            VerificationStrength::Formal => LoweringProofStrength::SmtUnsat,
        }
    }

    fn rank(&self) -> u8 {
        match self {
            LoweringProofStrength::Sampled { .. } => 0,
            LoweringProofStrength::ExhaustiveFinite { .. } => 1,
            LoweringProofStrength::SmtUnsat => 2,
        }
    }

    fn detail_rank(&self) -> u64 {
        match self {
            LoweringProofStrength::Sampled { sample_count } => *sample_count,
            LoweringProofStrength::ExhaustiveFinite { state_count } => state_count.unwrap_or(0),
            LoweringProofStrength::SmtUnsat => u64::MAX,
        }
    }

    fn to_trust_strength_json(&self) -> serde_json::Value {
        match self {
            LoweringProofStrength::Sampled { sample_count } => serde_json::json!({
                "reasoning": { "BoundedModelCheck": { "depth": sample_count } },
                "assurance": { "BoundedSound": { "depth": sample_count } }
            }),
            LoweringProofStrength::ExhaustiveFinite { state_count } => {
                let states = state_count.unwrap_or(0);
                serde_json::json!({
                    "reasoning": { "ExhaustiveFinite": states },
                    "assurance": "Sound"
                })
            }
            LoweringProofStrength::SmtUnsat => serde_json::json!({
                "reasoning": "Smt",
                "assurance": "Sound"
            }),
        }
    }

    fn to_trust_evidence_json(&self) -> serde_json::Value {
        match self {
            LoweringProofStrength::Sampled { sample_count } => serde_json::json!({
                "reasoning": { "BoundedModelCheck": { "depth": sample_count } },
                "assurance": { "BoundedSound": { "depth": sample_count } }
            }),
            LoweringProofStrength::ExhaustiveFinite { state_count } => {
                let states = state_count.unwrap_or(0);
                serde_json::json!({
                    "reasoning": { "ExhaustiveFinite": states },
                    "assurance": "SmtBacked"
                })
            }
            LoweringProofStrength::SmtUnsat => serde_json::json!({
                "reasoning": "Smt",
                "assurance": "SmtBacked"
            }),
        }
    }
}

/// Certificate-level result.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LoweringCertificateStatus {
    /// All included obligations were verified.
    Verified,
}

/// Aggregate solver metadata for a lowering certificate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LoweringSolverSummary {
    /// Solver/evaluator name, or `mixed` when rules used multiple solvers.
    pub name: String,
    /// Trust Codegen verifier version string.
    pub version: String,
    /// Total time spent verifying included rules.
    pub total_time_ms: u64,
}

#[derive(Serialize)]
struct LoweringFormulaSummary<'a> {
    schema: &'static str,
    function: &'a str,
    target: &'a str,
    trust_ir_hash: &'a str,
    machine_code_hash: &'a str,
    compiler_config_hash: &'a str,
    rule_proofs: &'a [LoweringRuleProof],
}

#[derive(Serialize)]
struct LoweringStableHashView<'a> {
    schema: &'a str,
    function: &'a str,
    target: &'a str,
    trust_ir_hash: &'a str,
    machine_code_hash: &'a str,
    compiler_config_hash: &'a str,
    rule_proofs: &'a [LoweringRuleProof],
    overall_strength: &'a LoweringProofStrength,
    result: &'a LoweringCertificateStatus,
}

// ---------------------------------------------------------------------------
// CertificateError
// ---------------------------------------------------------------------------

/// Errors during certificate chain serialization/deserialization.
#[derive(Debug, Error)]
pub enum CertificateError {
    /// JSON parsing error.
    #[error("JSON parse error: {0}")]
    JsonParseError(String),
    /// JSON serialization error.
    #[error("serialization error: {0}")]
    SerializationError(String),
    /// Required field missing.
    #[error("missing field: {0}")]
    MissingField(String),
    /// Invalid result value.
    #[error("invalid result: {0}")]
    InvalidResult(String),
    /// Cannot build a function-level certificate from an empty chain.
    #[error("cannot emit lowering certificate from an empty certificate chain")]
    EmptyChain,
    /// An obligation did not verify, so certified output must fail closed.
    #[error("cannot certify obligation `{obligation_name}` with result {result}")]
    UnverifiedObligation {
        /// Obligation name.
        obligation_name: String,
        /// Non-verified result.
        result: String,
    },
    /// Lowering certificates require typed transval check-kind coverage.
    #[error("cannot certify obligation `{obligation_name}` without check_kind")]
    MissingCheckKind {
        /// Obligation name.
        obligation_name: String,
    },
}

// ---------------------------------------------------------------------------
// Certificate generation
// ---------------------------------------------------------------------------

/// Generate a proof certificate by running verification on the given obligation.
///
/// This function:
/// 1. Computes a formula hash from the negated equivalence expression
/// 2. Runs `verify_by_evaluation` on the obligation
/// 3. Records the outcome, duration, solver, and strength
pub fn generate_certificate(obligation: &ProofObligation) -> ProofCertificate {
    let formula_hash = compute_formula_hash(obligation);
    let strength = VerificationStrength::for_obligation(obligation);
    let solver = strength_to_solver(&strength);

    let timestamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs();

    let start = Instant::now();
    let result = verify_by_evaluation(obligation);
    let duration_ms = start.elapsed().as_millis() as u64;

    let cert_result = match result {
        VerificationResult::Valid => CertificateResult::Verified,
        VerificationResult::Invalid { counterexample } => {
            CertificateResult::Failed { counterexample }
        }
        VerificationResult::Unknown { reason } => {
            if reason.to_lowercase().contains("timeout") {
                CertificateResult::Timeout {
                    seconds: duration_ms as f64 / 1000.0,
                }
            } else {
                CertificateResult::Skipped { reason }
            }
        }
    };

    ProofCertificate {
        obligation_name: obligation.name.clone(),
        result: cert_result,
        solver,
        strength,
        check_kind: obligation.category,
        formula_hash,
        timestamp_epoch_secs: timestamp,
        duration_ms,
    }
}

/// Generate a certificate chain by verifying all obligations for a compilation unit.
pub fn generate_certificate_chain(
    compilation_unit: &str,
    obligations: &[ProofObligation],
) -> CertificateChain {
    let mut chain = CertificateChain::new(compilation_unit.to_string());
    for obligation in obligations {
        let cert = generate_certificate(obligation);
        chain.add(cert);
    }
    chain
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

fn weakest_lowering_strength(rule_proofs: &[LoweringRuleProof]) -> Option<LoweringProofStrength> {
    rule_proofs
        .iter()
        .map(|proof| proof.result.strength())
        .min_by_key(|strength| (strength.rank(), strength.detail_rank()))
        .cloned()
}

fn summarize_solver_names(names: &[&'static str]) -> String {
    let Some(first) = names.first() else {
        return "unknown".to_string();
    };
    if names.iter().all(|name| name == first) {
        (*first).to_string()
    } else {
        "mixed".to_string()
    }
}

fn compute_rule_proof_hash(
    cert: &ProofCertificate,
    check_kind: TransvalCheckKind,
    strength: &LoweringProofStrength,
) -> String {
    let stable = format!(
        "{}|{}|{}|{}|{}|{:016x}",
        cert.obligation_name,
        check_kind,
        cert.result.tag(),
        cert.solver.tag(),
        lowering_strength_stable_tag(strength),
        cert.formula_hash
    );
    sha256_hex(stable.as_bytes())
}

fn lowering_strength_stable_tag(strength: &LoweringProofStrength) -> String {
    match strength {
        LoweringProofStrength::Sampled { sample_count } => {
            format!("sampled:{sample_count}")
        }
        LoweringProofStrength::ExhaustiveFinite { state_count } => {
            format!("exhaustive_finite:{}", state_count.unwrap_or(0))
        }
        LoweringProofStrength::SmtUnsat => "smt_unsat".to_string(),
    }
}

fn exhaustive_input_state_count(obligation: &ProofObligation) -> u64 {
    let mut bits = 0u64;
    for (_, width) in &obligation.inputs {
        bits = bits.saturating_add(*width as u64);
    }
    for (_, exponent_bits, significand_bits) in &obligation.fp_inputs {
        bits = bits
            .saturating_add(*exponent_bits as u64)
            .saturating_add(*significand_bits as u64);
    }

    if bits >= 63 { u64::MAX } else { 1u64 << bits }
}

/// Compute a hash of the negated equivalence formula for cache invalidation.
fn compute_formula_hash(obligation: &ProofObligation) -> u64 {
    let formula = obligation.negated_equivalence();
    let debug_str = format!("{:?}", formula);
    let mut hasher = StableHasher::new();
    hasher.write(debug_str.as_bytes());
    hasher.finish64()
}

fn sha256_hex(data: &[u8]) -> String {
    hex_bytes(&sha256_digest(data))
}

fn hex_bytes(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

fn sha256_digest(data: &[u8]) -> [u8; 32] {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];

    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];

    let bit_len = (data.len() as u64).wrapping_mul(8);
    let mut padded = Vec::with_capacity(data.len() + 72);
    padded.extend_from_slice(data);
    padded.push(0x80);
    while padded.len() % 64 != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());

    for chunk in padded.chunks_exact(64) {
        let mut w = [0u32; 64];
        for (i, word) in w.iter_mut().take(16).enumerate() {
            let base = i * 4;
            *word = u32::from_be_bytes([
                chunk[base],
                chunk[base + 1],
                chunk[base + 2],
                chunk[base + 3],
            ]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }

        let mut a = h[0];
        let mut b = h[1];
        let mut c = h[2];
        let mut d = h[3];
        let mut e = h[4];
        let mut f = h[5];
        let mut g = h[6];
        let mut hh = h[7];

        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);

            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }

        h[0] = h[0].wrapping_add(a);
        h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
        h[4] = h[4].wrapping_add(e);
        h[5] = h[5].wrapping_add(f);
        h[6] = h[6].wrapping_add(g);
        h[7] = h[7].wrapping_add(hh);
    }

    let mut out = [0u8; 32];
    for (i, word) in h.iter().enumerate() {
        out[i * 4..i * 4 + 4].copy_from_slice(&word.to_be_bytes());
    }
    out
}

fn epoch_secs_to_rfc3339(epoch_secs: u64) -> String {
    let days = (epoch_secs / 86_400) as i64;
    let seconds_of_day = epoch_secs % 86_400;
    let (year, month, day) = civil_from_days(days);
    let hour = seconds_of_day / 3_600;
    let minute = (seconds_of_day % 3_600) / 60;
    let second = seconds_of_day % 60;
    format!("{year:04}-{month:02}-{day:02}T{hour:02}:{minute:02}:{second:02}Z")
}

fn civil_from_days(days_since_unix_epoch: i64) -> (i64, u32, u32) {
    let z = days_since_unix_epoch + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1_460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = mp + if mp < 10 { 3 } else { -9 };
    let year = y + if month <= 2 { 1 } else { 0 };
    (year, month as u32, day as u32)
}

/// Map verification strength to the solver that was used.
fn strength_to_solver(strength: &VerificationStrength) -> SolverUsed {
    match strength {
        VerificationStrength::Exhaustive => SolverUsed::MockExhaustive,
        VerificationStrength::Statistical { sample_count } => SolverUsed::MockStatistical {
            samples: *sample_count,
        },
        VerificationStrength::Formal => SolverUsed::AYNative,
    }
}

/// Convert VerificationStrength to a short tag for JSON.
fn strength_to_tag(strength: &VerificationStrength) -> &'static str {
    match strength {
        VerificationStrength::Exhaustive => "exhaustive",
        VerificationStrength::Statistical { .. } => "statistical",
        VerificationStrength::Formal => "formal",
    }
}

/// Escape a string for JSON output.
fn escape_json(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out
}

/// Extract a string field from a flat JSON object.
fn extract_string_field(json: &str, field: &str) -> Result<String, CertificateError> {
    let pattern = format!("\"{}\"", field);
    let field_pos = json
        .find(&pattern)
        .ok_or_else(|| CertificateError::MissingField(field.to_string()))?;
    let after_key = &json[field_pos + pattern.len()..];
    // Skip ': "'
    let val_start = after_key
        .find('"')
        .ok_or_else(|| CertificateError::JsonParseError(format!("no value for {}", field)))?;
    let val_content = &after_key[val_start + 1..];
    let val_end = find_unescaped_quote(val_content).ok_or_else(|| {
        CertificateError::JsonParseError(format!("unterminated string for {}", field))
    })?;
    Ok(unescape_json(&val_content[..val_end]))
}

/// Extract a u64 field from a flat JSON object.
fn extract_u64_field(json: &str, field: &str) -> Result<u64, CertificateError> {
    let pattern = format!("\"{}\"", field);
    let field_pos = json
        .find(&pattern)
        .ok_or_else(|| CertificateError::MissingField(field.to_string()))?;
    let after_key = &json[field_pos + pattern.len()..];
    // Skip ': '
    let colon_pos = after_key
        .find(':')
        .ok_or_else(|| CertificateError::JsonParseError(format!("no colon after {}", field)))?;
    let after_colon = after_key[colon_pos + 1..].trim_start();
    // Read digits
    let num_end = after_colon
        .find(|c: char| !c.is_ascii_digit())
        .unwrap_or(after_colon.len());
    let num_str = &after_colon[..num_end];
    num_str
        .parse::<u64>()
        .map_err(|e| CertificateError::JsonParseError(format!("bad u64 for {}: {}", field, e)))
}

/// Extract an optional f64 field from a flat JSON object.
fn extract_f64_field(json: &str, field: &str) -> Option<f64> {
    let pattern = format!("\"{}\"", field);
    let field_pos = json.find(&pattern)?;
    let after_key = &json[field_pos + pattern.len()..];
    let colon_pos = after_key.find(':')?;
    let after_colon = after_key[colon_pos + 1..].trim_start();
    let num_end = after_colon
        .find(|c: char| !c.is_ascii_digit() && c != '.' && c != '-')
        .unwrap_or(after_colon.len());
    after_colon[..num_end].parse::<f64>().ok()
}

/// Find the index of the first unescaped double-quote.
fn find_unescaped_quote(s: &str) -> Option<usize> {
    let mut escaped = false;
    for (i, c) in s.char_indices() {
        if escaped {
            escaped = false;
            continue;
        }
        if c == '\\' {
            escaped = true;
            continue;
        }
        if c == '"' {
            return Some(i);
        }
    }
    None
}

/// Unescape a JSON string value.
fn unescape_json(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('"') => out.push('"'),
                Some('\\') => out.push('\\'),
                Some('n') => out.push('\n'),
                Some('r') => out.push('\r'),
                Some('t') => out.push('\t'),
                Some(other) => {
                    out.push('\\');
                    out.push(other);
                }
                None => out.push('\\'),
            }
        } else {
            out.push(c);
        }
    }
    out
}

/// Find the matching ] for a [ at position `start`.
fn find_matching_bracket(s: &str, start: usize) -> Option<usize> {
    let mut depth = 0;
    let mut in_string = false;
    let mut escape_next = false;
    for (i, c) in s[start..].char_indices() {
        if escape_next {
            escape_next = false;
            continue;
        }
        if c == '\\' && in_string {
            escape_next = true;
            continue;
        }
        if c == '"' {
            in_string = !in_string;
            continue;
        }
        if in_string {
            continue;
        }
        if c == '[' {
            depth += 1;
        } else if c == ']' {
            depth -= 1;
            if depth == 0 {
                return Some(start + i);
            }
        }
    }
    None
}

/// Find the matching } for a { at position `start`.
fn find_matching_brace(s: &str, start: usize) -> Option<usize> {
    let mut depth = 0;
    let mut in_string = false;
    let mut escape_next = false;
    for (i, c) in s[start..].char_indices() {
        if escape_next {
            escape_next = false;
            continue;
        }
        if c == '\\' && in_string {
            escape_next = true;
            continue;
        }
        if c == '"' {
            in_string = !in_string;
            continue;
        }
        if in_string {
            continue;
        }
        if c == '{' {
            depth += 1;
        } else if c == '}' {
            depth -= 1;
            if depth == 0 {
                return Some(start + i);
            }
        }
    }
    None
}

/// Parse a single certificate from a JSON object string.
fn parse_certificate(json: &str) -> Result<ProofCertificate, CertificateError> {
    let obligation_name = extract_string_field(json, "obligation_name")?;
    let result_tag = extract_string_field(json, "result")?;

    let result = match result_tag.as_str() {
        "verified" => CertificateResult::Verified,
        "failed" => {
            let cex =
                extract_string_field(json, "counterexample").unwrap_or_else(|_| String::new());
            CertificateResult::Failed {
                counterexample: cex,
            }
        }
        "timeout" => {
            let secs = extract_f64_field(json, "timeout_seconds").unwrap_or(0.0);
            CertificateResult::Timeout { seconds: secs }
        }
        "skipped" => {
            let reason =
                extract_string_field(json, "skip_reason").unwrap_or_else(|_| String::new());
            CertificateResult::Skipped { reason }
        }
        other => {
            return Err(CertificateError::InvalidResult(other.to_string()));
        }
    };

    let solver_tag = extract_string_field(json, "solver")?;
    let solver = match solver_tag.as_str() {
        "mock_exhaustive" => SolverUsed::MockExhaustive,
        "mock_statistical" => {
            let samples = extract_u64_field(json, "solver_samples").unwrap_or(100_000);
            SolverUsed::MockStatistical { samples }
        }
        "ay_cli" => SolverUsed::AYCli,
        "ay_native" => SolverUsed::AYNative,
        "z3_cli" => SolverUsed::Z3Cli,
        other => {
            return Err(CertificateError::InvalidResult(format!(
                "unknown solver: {}",
                other
            )));
        }
    };

    let strength_tag = extract_string_field(json, "strength")?;
    let strength = match strength_tag.as_str() {
        "exhaustive" => VerificationStrength::Exhaustive,
        "statistical" => {
            let samples = extract_u64_field(json, "strength_samples").unwrap_or(100_000);
            VerificationStrength::Statistical {
                sample_count: samples,
            }
        }
        "formal" => VerificationStrength::Formal,
        other => {
            return Err(CertificateError::InvalidResult(format!(
                "unknown strength: {}",
                other
            )));
        }
    };

    let check_kind = extract_string_field(json, "check_kind")
        .ok()
        .and_then(|s| parse_check_kind(&s));

    let formula_hash = extract_u64_field(json, "formula_hash")?;
    let timestamp_epoch_secs = extract_u64_field(json, "timestamp_epoch_secs")?;
    let duration_ms = extract_u64_field(json, "duration_ms")?;

    Ok(ProofCertificate {
        obligation_name,
        result,
        solver,
        strength,
        check_kind,
        formula_hash,
        timestamp_epoch_secs,
        duration_ms,
    })
}

/// Parse a TransvalCheckKind from its Display string.
fn parse_check_kind(s: &str) -> Option<TransvalCheckKind> {
    match s {
        "data_flow" => Some(TransvalCheckKind::DataFlow),
        "control_flow" => Some(TransvalCheckKind::ControlFlow),
        "return_value" => Some(TransvalCheckKind::ReturnValue),
        "termination" => Some(TransvalCheckKind::Termination),
        "instruction_lowering" => Some(TransvalCheckKind::InstructionLowering),
        "peephole" => Some(TransvalCheckKind::PeepholeOptimization),
        "memory" => Some(TransvalCheckKind::MemoryModel),
        "regalloc" => Some(TransvalCheckKind::RegisterAllocation),
        "vectorization" => Some(TransvalCheckKind::Vectorization),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::SmtExpr;

    /// Helper: create a trivially valid proof obligation (bvadd(a,b) == bvadd(a,b)).
    fn make_simple_obligation(name: &str) -> ProofObligation {
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);
        ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: name.to_string(),
            trust_ir_expr: SmtExpr::bvadd(a.clone(), b.clone()),
            aarch64_expr: SmtExpr::bvadd(a, b),
            inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(TransvalCheckKind::InstructionLowering),
        }
    }

    fn make_certificate_with_result(name: &str, result: CertificateResult) -> ProofCertificate {
        ProofCertificate {
            obligation_name: name.to_string(),
            result,
            solver: SolverUsed::MockExhaustive,
            strength: VerificationStrength::Exhaustive,
            check_kind: Some(TransvalCheckKind::InstructionLowering),
            formula_hash: 0xabc,
            timestamp_epoch_secs: 1,
            duration_ms: 7,
        }
    }

    #[test]
    fn test_certificate_result_display() {
        let v = CertificateResult::Verified;
        assert_eq!(format!("{:?}", v), "Verified");
        assert_eq!(format!("{}", v), "Verified");

        let f = CertificateResult::Failed {
            counterexample: "a=1, b=2".to_string(),
        };
        assert!(format!("{}", f).contains("Failed"));

        let t = CertificateResult::Timeout { seconds: 5.5 };
        assert!(format!("{}", t).contains("Timeout"));

        let s = CertificateResult::Skipped {
            reason: "no solver".to_string(),
        };
        assert!(format!("{}", s).contains("Skipped"));
    }

    #[test]
    fn test_sha256_known_vectors() {
        assert_eq!(
            sha256_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn test_generate_certificate_for_simple_proof() {
        let obligation = make_simple_obligation("test_iadd_i8");
        let cert = generate_certificate(&obligation);

        assert_eq!(cert.obligation_name, "test_iadd_i8");
        assert_eq!(cert.result, CertificateResult::Verified);
        assert_eq!(cert.solver, SolverUsed::MockExhaustive);
        assert_eq!(cert.strength, VerificationStrength::Exhaustive);
        assert_eq!(
            cert.check_kind,
            Some(TransvalCheckKind::InstructionLowering)
        );
        assert!(cert.formula_hash != 0);
        assert!(cert.timestamp_epoch_secs > 0);
    }

    #[test]
    fn test_generate_lowering_certificate_verified_chain() {
        let mut ret_obligation = make_simple_obligation("return_value_i8");
        ret_obligation.category = Some(TransvalCheckKind::ReturnValue);
        let obligations = vec![make_simple_obligation("iadd_i8"), ret_obligation];

        let cert = generate_lowering_certificate(
            "test_fn",
            "aarch64-apple-darwin",
            br#"{"function":"test_fn"}"#,
            &[0x20, 0x00, 0x00, 0x0b],
            br#"{"opt_level":0}"#,
            &obligations,
        )
        .expect("verified obligations should emit lowering certificate");

        assert_eq!(cert.schema, "trust-cg.lowering_certificate.v1");
        assert_eq!(cert.function, "test_fn");
        assert_eq!(cert.target, "aarch64-apple-darwin");
        assert_eq!(cert.result, LoweringCertificateStatus::Verified);
        assert_eq!(cert.rule_proofs.len(), 2);
        assert_eq!(cert.rule_proofs[0].rule_name, "iadd_i8");
        assert_eq!(cert.rule_proofs[0].check_kind, "instruction_lowering");
        assert_eq!(cert.rule_proofs[1].rule_name, "return_value_i8");
        assert_eq!(cert.rule_proofs[1].check_kind, "return_value");
        assert_eq!(cert.trust_ir_hash.len(), 64);
        assert_eq!(cert.machine_code_hash.len(), 64);
        assert_eq!(
            cert.overall_strength,
            LoweringProofStrength::ExhaustiveFinite {
                state_count: Some(65_536)
            }
        );
    }

    #[test]
    fn test_lowering_certificate_rejects_unverified_obligations() {
        let cases = vec![
            CertificateResult::Failed {
                counterexample: "a=1".to_string(),
            },
            CertificateResult::Timeout { seconds: 30.0 },
            CertificateResult::Skipped {
                reason: "solver unavailable".to_string(),
            },
        ];

        for (idx, result) in cases.into_iter().enumerate() {
            let mut chain = CertificateChain::new(format!("bad_fn_{idx}"));
            chain.add(make_certificate_with_result("bad_rule", result));
            let err = LoweringCertificate::from_verified_chain(
                "bad_fn",
                "aarch64",
                b"trust_ir",
                b"machine",
                b"config",
                &chain,
            )
            .expect_err("non-verified obligations must fail closed");

            assert!(
                matches!(err, CertificateError::UnverifiedObligation { .. }),
                "unexpected error: {err:?}"
            );
        }
    }

    #[test]
    fn test_lowering_certificate_rejects_missing_check_kind() {
        let mut chain = CertificateChain::new("uncategorized_fn".to_string());
        let mut cert =
            make_certificate_with_result("uncategorized_rule", CertificateResult::Verified);
        cert.check_kind = None;
        chain.add(cert);

        let err = LoweringCertificate::from_verified_chain(
            "uncategorized_fn",
            "aarch64",
            b"trust_ir",
            b"machine",
            b"config",
            &chain,
        )
        .expect_err("missing check_kind must fail closed");

        assert!(matches!(err, CertificateError::MissingCheckKind { .. }));
    }

    #[test]
    fn test_lowering_certificate_json_roundtrip() {
        let obligations = vec![make_simple_obligation("iadd_i8")];
        let cert = generate_lowering_certificate(
            "roundtrip_lowering",
            "aarch64",
            b"trust_ir",
            b"machine",
            b"config",
            &obligations,
        )
        .expect("lowering certificate should generate");

        let json = cert
            .to_json()
            .expect("lowering certificate should serialize");
        let parsed =
            LoweringCertificate::from_json(&json).expect("lowering certificate should parse");
        assert_eq!(parsed, cert);
    }

    #[test]
    fn test_trust_proof_cert_export_schema() {
        let obligations = vec![make_simple_obligation("iadd_i8")];
        let cert = generate_lowering_certificate(
            "trust_export",
            "aarch64",
            b"trust_ir",
            b"machine",
            b"config",
            &obligations,
        )
        .expect("lowering certificate should generate");

        let json = cert
            .to_trust_proof_cert_json()
            .expect("trust export should serialize");
        let value: serde_json::Value =
            serde_json::from_str(&json).expect("trust export should be JSON");

        assert_eq!(value["version"], 2);
        assert_eq!(value["function"], "trust_export");
        assert_eq!(value["status"], "Trusted");
        assert_eq!(
            value["function_hash"].as_str().expect("function hash"),
            cert.trust_ir_hash
        );
        assert_eq!(
            value["vc_hash"].as_array().expect("vc_hash array").len(),
            32
        );
        assert_eq!(value["vc_snapshot"]["kind"], "lowering_equivalence");
        assert!(value["signature"].is_null());

        let formula_json = value["vc_snapshot"]["formula_json"]
            .as_str()
            .expect("formula_json string");
        let formula: serde_json::Value =
            serde_json::from_str(formula_json).expect("formula summary should be JSON");
        assert_eq!(formula["schema"], "trust-cg.lowering_formula_summary.v1");
        assert_eq!(
            formula["rule_proofs"][0]["check_kind"],
            "instruction_lowering"
        );

        let strength = &value["solver"]["strength"];
        assert_eq!(
            strength["reasoning"],
            serde_json::json!({ "ExhaustiveFinite": 65_536_u64 })
        );
        assert_eq!(strength["assurance"], "Sound");
        assert_eq!(value["solver"]["evidence"]["assurance"], "SmtBacked");

        let steps = value["chain"]["steps"].as_array().expect("chain steps");
        assert_eq!(steps.len(), 3);
        assert_eq!(steps[0]["step_type"], "VcGeneration");
        assert_eq!(steps[1]["step_type"], "SolverProof");
        assert_eq!(steps[2]["step_type"], "CodegenLowering");
        assert_eq!(steps[0]["output_hash"], steps[1]["input_hash"]);
        assert_eq!(steps[1]["output_hash"], steps[2]["input_hash"]);
        assert_eq!(
            steps[2]["output_hash"].as_str().expect("output hash"),
            cert.machine_code_hash
        );
    }

    #[test]
    fn test_certificate_chain_empty() {
        let chain = CertificateChain::new("empty_fn".to_string());
        assert_eq!(chain.verify_chain(), ChainVerificationResult::Empty);
        assert!(!chain.all_verified());
        assert!(chain.failed_certificates().is_empty());
    }

    #[test]
    fn test_certificate_chain_all_verified() {
        let mut chain = CertificateChain::new("verified_fn".to_string());
        for i in 0..3 {
            let obligation = make_simple_obligation(&format!("proof_{}", i));
            let cert = generate_certificate(&obligation);
            chain.add(cert);
        }

        assert!(chain.all_verified());
        assert_eq!(
            chain.verify_chain(),
            ChainVerificationResult::AllVerified { count: 3 }
        );
        assert!(chain.failed_certificates().is_empty());
    }

    #[test]
    fn test_certificate_chain_with_failure() {
        let mut chain = CertificateChain::new("mixed_fn".to_string());

        // Add a verified certificate
        let obligation = make_simple_obligation("good_proof");
        let cert = generate_certificate(&obligation);
        chain.add(cert);

        // Add a manually-created failed certificate
        chain.add(ProofCertificate {
            obligation_name: "bad_proof".to_string(),
            result: CertificateResult::Failed {
                counterexample: "a=0xff, b=0x01".to_string(),
            },
            solver: SolverUsed::MockExhaustive,
            strength: VerificationStrength::Exhaustive,
            check_kind: None,
            formula_hash: 12345,
            timestamp_epoch_secs: 1000,
            duration_ms: 50,
        });

        assert!(!chain.all_verified());
        assert_eq!(chain.failed_certificates().len(), 1);

        match chain.verify_chain() {
            ChainVerificationResult::HasFailures {
                verified,
                failed,
                skipped,
                timeout,
            } => {
                assert_eq!(verified, 1);
                assert_eq!(failed, 1);
                assert_eq!(skipped, 0);
                assert_eq!(timeout, 0);
            }
            other => panic!("expected HasFailures, got {:?}", other),
        }
    }

    #[test]
    fn test_chain_summary() {
        let mut chain = CertificateChain::new("summary_fn".to_string());

        // Two verified
        for i in 0..2 {
            let obligation = make_simple_obligation(&format!("proof_{}", i));
            chain.add(generate_certificate(&obligation));
        }

        // One timeout
        chain.add(ProofCertificate {
            obligation_name: "timeout_proof".to_string(),
            result: CertificateResult::Timeout { seconds: 30.0 },
            solver: SolverUsed::Z3Cli,
            strength: VerificationStrength::Formal,
            check_kind: None,
            formula_hash: 99999,
            timestamp_epoch_secs: 1000,
            duration_ms: 30000,
        });

        // One skipped
        chain.add(ProofCertificate {
            obligation_name: "skipped_proof".to_string(),
            result: CertificateResult::Skipped {
                reason: "solver not available".to_string(),
            },
            solver: SolverUsed::AYNative,
            strength: VerificationStrength::Formal,
            check_kind: None,
            formula_hash: 88888,
            timestamp_epoch_secs: 1000,
            duration_ms: 0,
        });

        let summary = chain.summary();
        assert_eq!(summary.total, 4);
        assert_eq!(summary.verified, 2);
        assert_eq!(summary.failed, 0);
        assert_eq!(summary.timeout, 1);
        assert_eq!(summary.skipped, 1);
        assert!(summary.total_duration_ms >= 30000);
    }

    #[test]
    fn test_json_roundtrip() {
        let mut chain = CertificateChain::new("roundtrip_fn".to_string());

        // Add a verified certificate
        let obligation = make_simple_obligation("iadd_i8");
        let cert = generate_certificate(&obligation);
        let original_hash = cert.formula_hash;
        let original_name = cert.obligation_name.clone();
        chain.add(cert);

        // Add a failed certificate
        chain.add(ProofCertificate {
            obligation_name: "bad_rule".to_string(),
            result: CertificateResult::Failed {
                counterexample: "a=255, b=1".to_string(),
            },
            solver: SolverUsed::MockStatistical { samples: 50000 },
            strength: VerificationStrength::Statistical {
                sample_count: 50000,
            },
            check_kind: Some(TransvalCheckKind::DataFlow),
            formula_hash: 42,
            timestamp_epoch_secs: 1713200000,
            duration_ms: 123,
        });

        let json = chain.to_json();

        // Parse it back
        let parsed = CertificateChain::from_json(&json).expect("JSON roundtrip failed");

        assert_eq!(parsed.compilation_unit, "roundtrip_fn");
        assert_eq!(parsed.certificates.len(), 2);

        // Check first certificate
        let c0 = &parsed.certificates[0];
        assert_eq!(c0.obligation_name, original_name);
        assert_eq!(c0.result, CertificateResult::Verified);
        assert_eq!(c0.solver, SolverUsed::MockExhaustive);
        assert_eq!(c0.strength, VerificationStrength::Exhaustive);
        assert_eq!(c0.check_kind, Some(TransvalCheckKind::InstructionLowering));
        assert_eq!(c0.formula_hash, original_hash);

        // Check second certificate
        let c1 = &parsed.certificates[1];
        assert_eq!(c1.obligation_name, "bad_rule");
        assert!(matches!(c1.result, CertificateResult::Failed { .. }));
        assert_eq!(c1.solver, SolverUsed::MockStatistical { samples: 50000 });
        assert_eq!(
            c1.strength,
            VerificationStrength::Statistical {
                sample_count: 50000
            }
        );
        assert_eq!(c1.formula_hash, 42);
        assert_eq!(c1.timestamp_epoch_secs, 1713200000);
        assert_eq!(c1.duration_ms, 123);
        assert_eq!(c1.check_kind, Some(TransvalCheckKind::DataFlow));
    }

    #[test]
    fn test_generate_certificate_chain_fn() {
        let obligations: Vec<ProofObligation> = (0..3)
            .map(|i| make_simple_obligation(&format!("chain_proof_{}", i)))
            .collect();

        let chain = generate_certificate_chain("test_function", &obligations);

        assert_eq!(chain.compilation_unit, "test_function");
        assert_eq!(chain.certificates.len(), 3);
        assert!(chain.all_verified());

        for (i, cert) in chain.certificates.iter().enumerate() {
            assert_eq!(cert.obligation_name, format!("chain_proof_{}", i));
            assert_eq!(cert.result, CertificateResult::Verified);
        }
    }

    #[test]
    fn test_formula_hash_stability() {
        // Same obligation should produce the same hash
        let o1 = make_simple_obligation("same_proof");
        let o2 = make_simple_obligation("same_proof");
        let h1 = compute_formula_hash(&o1);
        let h2 = compute_formula_hash(&o2);
        assert_eq!(h1, h2);

        // Different obligation should produce a different hash
        let o3 = make_simple_obligation("different_proof");
        // Same formula structure -- hash should still be equal since the
        // negated equivalence is the same (just different name, which
        // is not part of the formula).
        let h3 = compute_formula_hash(&o3);
        assert_eq!(h1, h3); // name not hashed, formula is identical

        // Truly different formula
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);
        let o4 = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "sub_proof".to_string(),
            trust_ir_expr: SmtExpr::bvsub(a.clone(), b.clone()),
            aarch64_expr: SmtExpr::bvsub(a, b),
            inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };
        let h4 = compute_formula_hash(&o4);
        assert_ne!(h1, h4);
    }

    #[test]
    fn test_chain_display() {
        let mut chain = CertificateChain::new("display_fn".to_string());
        let obligation = make_simple_obligation("proof_0");
        chain.add(generate_certificate(&obligation));

        let display = format!("{}", chain);
        assert!(display.contains("display_fn"));
        assert!(display.contains("1/1 verified"));
    }

    // =======================================================================
    // ENC-11 verdict-tier TAXONOMY LOCK (proven-ness integrity)
    //
    // A Statistical (sampled, > 8-bit) verdict is a strictly-weaker, NON-PROOF
    // tier. These tests LOCK the tier taxonomy so a sampled verdict can never be
    // constructed, aggregated, or serialized as a proof tier (`SmtUnsat` /
    // `Formal`). Crediting a sampled verdict as a proof is a soundness-reporting
    // lie — exactly the class PROOF-4/5 and P3c (df8f6bd) closed. If any mapping
    // here up-labels Statistical, the gate fails.
    // =======================================================================

    /// Criterion (d): constructing a proof tier from a sampled result is
    /// impossible — `from_verification_strength` maps a `Statistical` verdict to
    /// the `Sampled` tier, NEVER to `SmtUnsat`. Exhaustive/Formal keep their
    /// (stronger) tiers, and `Sampled` ranks strictly below the proof tier.
    #[test]
    fn enc11_statistical_strength_never_maps_to_smt_unsat() {
        let sampled = LoweringProofStrength::from_verification_strength(
            &VerificationStrength::Statistical {
                sample_count: 100_000,
            },
            None,
        );
        assert_eq!(
            sampled,
            LoweringProofStrength::Sampled {
                sample_count: 100_000
            },
            "a Statistical verdict must map to the Sampled tier, never a proof tier"
        );
        assert!(
            !matches!(sampled, LoweringProofStrength::SmtUnsat),
            "a Statistical verdict must NEVER become SmtUnsat"
        );
        assert_eq!(
            LoweringProofStrength::from_verification_strength(&VerificationStrength::Formal, None),
            LoweringProofStrength::SmtUnsat
        );
        assert!(matches!(
            LoweringProofStrength::from_verification_strength(
                &VerificationStrength::Exhaustive,
                Some(256)
            ),
            LoweringProofStrength::ExhaustiveFinite { .. }
        ));
        assert!(
            LoweringProofStrength::Sampled {
                sample_count: 100_000
            }
            .rank()
                < LoweringProofStrength::SmtUnsat.rank(),
            "Sampled must rank strictly below the SMT-UNSAT proof tier"
        );
    }

    /// Criterion (a): a certificate chain that mixes a Statistical (sampled)
    /// obligation with a Formal (SMT-UNSAT) one must aggregate to the WEAKEST
    /// tier — `Sampled` — so a whole-function certificate can never be presented
    /// as SMT-proven overall while any rule was only sampled. The sampled rule's
    /// own record must also stay `Sampled`.
    #[test]
    fn enc11_mixed_chain_never_labels_a_proof_tier_while_any_rule_is_sampled() {
        let mut sampled_cert =
            make_certificate_with_result("sampled_rule", CertificateResult::Verified);
        sampled_cert.strength = VerificationStrength::Statistical {
            sample_count: 100_000,
        };
        sampled_cert.solver = SolverUsed::MockStatistical { samples: 100_000 };

        let mut formal_cert =
            make_certificate_with_result("formal_rule", CertificateResult::Verified);
        formal_cert.strength = VerificationStrength::Formal;
        formal_cert.solver = SolverUsed::AYNative;

        let mut chain = CertificateChain::new("mixed_fn".to_string());
        chain.add(sampled_cert);
        chain.add(formal_cert);

        let cert = LoweringCertificate::from_verified_chain(
            "mixed_fn",
            "aarch64",
            b"trust_ir",
            b"machine",
            b"config",
            &chain,
        )
        .expect("verified chain must build");

        assert!(
            matches!(cert.overall_strength, LoweringProofStrength::Sampled { .. }),
            "a chain containing a Sampled rule must NEVER be labeled a proof tier overall, got {:?}",
            cert.overall_strength
        );
        let sampled_rule = cert
            .rule_proofs
            .iter()
            .find(|r| r.rule_name == "sampled_rule")
            .expect("sampled rule present");
        assert!(
            matches!(
                sampled_rule.result.strength(),
                LoweringProofStrength::Sampled { .. }
            ),
            "the sampled rule must record the Sampled tier, got {:?}",
            sampled_rule.result.strength()
        );
    }

    /// Criterion (b): the serialization tags/solvers for a Statistical verdict
    /// read "statistical" / a MOCK sampler — never "formal" or a real SMT solver
    /// backend. A sampled verdict can never be attributed to a solver it did not
    /// run.
    #[test]
    fn enc11_serialization_tags_never_upgrade_a_statistical_verdict() {
        let stat = VerificationStrength::Statistical {
            sample_count: 100_000,
        };
        assert_eq!(strength_to_tag(&stat), "statistical");
        assert_ne!(strength_to_tag(&stat), "formal");
        assert!(matches!(
            strength_to_solver(&stat),
            SolverUsed::MockStatistical { .. }
        ));
        assert!(
            !matches!(
                strength_to_solver(&stat),
                SolverUsed::AYNative | SolverUsed::AYCli | SolverUsed::Z3Cli
            ),
            "a Statistical verdict must never be attributed to a real SMT solver backend"
        );
        assert_eq!(strength_to_tag(&VerificationStrength::Formal), "formal");
    }
}
