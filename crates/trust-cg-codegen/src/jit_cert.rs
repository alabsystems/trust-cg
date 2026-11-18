// trust-cg-codegen/jit_cert.rs - Proof certificates attached to JIT buffers
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Proof certificates for JIT-compiled functions (issue #348).
//!
//! Attaches a [`JitCertificate`] to each function compiled by
//! [`crate::jit::JitCompiler`] when [`crate::jit::JitConfig::verify`] is
//! true. The certificate bundles:
//!
//! - the function name and its byte range within the executable buffer,
//! - a coarse, diagnostic (trust_ir op, MachInst index range) classification,
//! - a full [`trust_cg_verify::proof_certificate::CertificateChain`] summarizing
//!   what was verified by [`trust_cg_verify::verify_function`], and
//! - a cheap `replay_check()` that checks the chain's stored tuple hashes.
//!
//! Independent AY/Clean replay of supported source-bound obligations happens
//! during function verification, before certificate construction. The
//! certificate's `replay_check()` checks consistency of its summary; it does
//! not run that proof replay or check the published executable bytes.
//!
//! This certificate records verifier-visible `MachFunction` evidence and binds
//! the normalized machine bytes used for cache identity. Bounded source-bound
//! owners additionally check their exact LIR/machine correspondence. The
//! opcode-name table here remains diagnostic metadata, so it cannot establish
//! general TrustIR-to-MachIR provenance or supply a `LoweringCertificate`.
//!
//! # Example
//!
//! ```no_run
//! # use trust_cg_codegen::jit::{JitCompiler, JitConfig};
//! # use std::collections::HashMap;
//! let jit = JitCompiler::new(JitConfig { verify: true, ..Default::default() });
//! # let functions = vec![];
//! let buf = jit.compile_raw(&functions, &HashMap::new()).unwrap();
//! if let Some(cert) = buf.certificate("add") {
//!     assert!(cert.is_verified());
//!     assert!(cert.replay_check());
//! }
//! ```

use std::ops::Range;

#[cfg(all(test, feature = "verify"))]
#[path = "jit_request_cache_tests.rs"]
mod jit_request_cache_tests;

#[cfg(feature = "verify")]
use sha2::{Digest, Sha256};

#[cfg(feature = "verify")]
use std::collections::hash_map::DefaultHasher;
#[cfg(feature = "verify")]
use std::hash::Hasher;
#[cfg(feature = "verify")]
use trust_cg_ir::{AArch64Opcode, MachFunction};
#[cfg(feature = "verify")]
use trust_cg_verify::function_verifier::{
    FunctionVerificationReport, InstructionVerificationResult,
};
#[cfg(feature = "verify")]
use trust_cg_verify::lowering_proof::TransvalCheckKind;
#[cfg(feature = "verify")]
use trust_cg_verify::proof_certificate::{
    CertificateChain, CertificateResult, LoweringCertificate, LoweringCertificateStatus,
    LoweringProofStrength, LoweringRuleProof, LoweringSolverSummary, LoweringVerification,
    ProofCertificate, SolverUsed,
};
#[cfg(feature = "verify")]
use trust_cg_verify::verify::VerificationStrength;

#[cfg(feature = "verify")]
pub(crate) fn run_on_proof_verifier_stack<R, F>(name: &str, f: F) -> R
where
    R: Send,
    F: FnOnce() -> R + Send,
{
    trust_cg_verify::resource_limits::run_on_proof_verifier_stack(name, f)
}

// ---------------------------------------------------------------------------
// TrustIrPair
// ---------------------------------------------------------------------------

/// A coarse provenance entry: one trust_ir operation and the contiguous range of
/// MachInst indices that implements it after lowering.
///
/// Phase 1 populates this via a small opcode → trust_ir-name lookup table. Later
/// phases will replace the table with the real trust_ir-to-MachInst provenance
/// map from `trust_cg_ir::provenance`.
#[derive(Debug, Clone)]
pub struct TrustIrPair {
    /// Name of the trust_ir operation (e.g. "Iadd_I32"). `"<opaque>"` when the
    /// opcode is not covered by the Phase-1 lookup table.
    pub trust_ir_op: String,
    /// Contiguous half-open range of indices into `MachFunction::insts` that
    /// implements this trust_ir op.
    pub mach_insts: Range<u32>,
}

// ---------------------------------------------------------------------------
// JitCertificate
// ---------------------------------------------------------------------------

/// A proof certificate for a single JIT-compiled function.
///
/// Constructed from a [`FunctionVerificationReport`] at JIT compile time
/// when verification is enabled. The certificate is immutable after
/// construction and can be queried, displayed, exported as JSON, or
/// replay-checked.
///
/// When the `verify` feature is disabled at build time, this type still
/// exists but its constructor is unreachable — `ExecutableBuffer` will
/// return `None` for every `certificate(name)` call.
#[derive(Debug, Clone)]
pub struct JitCertificate {
    /// Canonical function name (matches `MachFunction::name`).
    function: String,
    /// Byte range `[start, end)` of this callable region within the owning
    /// `ExecutableBuffer`. The range can include integrity-bound auxiliary
    /// bytes such as a profiling prefix; it is not itself a lowering proof.
    code_range: Range<u64>,
    /// Canonical verifier-input digest computed once before cache lookup.
    verifier_input_sha256: String,
    /// SHA-256 of the machine bytes the verification cache keys on. On the
    /// core address-free artifact route these are the unrelocated bytes; on
    /// the JIT publisher they are this function's range of the image buffer
    /// after the image-internal `BRANCH26` and veneer patches and before the
    /// runtime literals, the baseline the installed-artifact replay compares
    /// against. Exact post-relocation published bytes are reported
    /// separately by `JitFunctionValidation::bytes_sha256`.
    normalized_machine_code_sha256: String,
    /// trust_ir → MachInst provenance. One entry per encoded MachInst in
    /// insertion order. Empty in the no-verify build.
    trust_ir_pairs: Vec<TrustIrPair>,
    /// Certificate chain produced by `trust-cg-verify`. Empty when no
    /// instruction in the function matched a proof obligation.
    #[cfg(feature = "verify")]
    chain: CertificateChain,
    /// Function-level lowering certificate for trust-proof-cert export.
    ///
    /// Populated only when the included proof chain is fail-closed clean:
    /// every recorded obligation verified and carries a typed lowering
    /// category. Existing JIT certificates remain attached even when this
    /// stronger export cannot be produced.
    #[cfg(feature = "verify")]
    lowering_certificate: Option<LoweringCertificate>,
    /// Proof-grade, non-vacuous machine-IR verdict. This requires at least one
    /// genuinely verified instruction, no failed/unpromotable opcode, and no
    /// statistically credited instruction.
    verified: bool,
    /// A separately classified trusted source/ABI check for an exact RET-only
    /// body. It contributes neither instruction coverage nor Formal credit.
    #[cfg(feature = "verify")]
    structural_return: Option<trust_cg_verify::CheckedAarch64StructuralReturn>,
    /// Genuine coverage percentage from the verification report
    /// (non-degenerate verified / (total - skipped) * 100).
    coverage_pct: f64,
    /// Whether this instance was rebound from a content-addressed cache hit.
    /// This is delivery telemetry, not part of the proof payload.
    served_from_cache: bool,
    /// When the function-verification request this certificate's report came
    /// from had no AY bound: that request's own refusal note
    /// (`trust_cg_verify::FunctionVerificationRequest::ay_refusal_note`), the
    /// note a promotion refusal over this certificate carries. A diagnostic,
    /// excluded from every digest, seal and the JSON export.
    ay_refusal_note: Option<String>,
    #[cfg(feature = "verify")]
    peer_entry_binding: Option<PeerEntryCertificateBinding>,
}

#[cfg(feature = "verify")]
#[derive(Debug, Clone)]
struct PeerEntryCertificateBinding {
    owner: PhysicalEntryOwner,
    digest: trust_ir::proof::ProofDigest,
}

#[cfg(feature = "verify")]
#[derive(Debug, Clone)]
enum PhysicalEntryOwner {
    #[cfg(feature = "source-defined-call")]
    FourPointerStatus(
        std::sync::Weak<crate::compiler::core_four_pointer_status::CoreBoundFourPointerStatusProof>,
    ),
    Peer(std::sync::Weak<crate::compiler::core_peer_entry::CoreBoundPeerProof>),
    #[cfg(feature = "source-defined-call")]
    ContextOutput(
        std::sync::Weak<crate::compiler::core_context_output::CoreBoundContextOutputProof>,
    ),
}

/// Allocation-free canonical writer for the Core certificate semantic seal.
/// Length-prefixing every byte string and exhaustively tagging every enum
/// keeps concatenation and variant boundaries unambiguous.
#[cfg(feature = "verify")]
struct CoreCertificateSemanticHasher(Sha256);

#[cfg(feature = "verify")]
impl CoreCertificateSemanticHasher {
    fn new() -> Self {
        let mut hasher = Sha256::new();
        hasher.update(b"trust-cg.jit-certificate.core-semantic.v2\0");
        Self(hasher)
    }

    fn u8(&mut self, value: u8) {
        self.0.update([value]);
    }

    fn u64(&mut self, value: u64) {
        self.0.update(value.to_be_bytes());
    }

    fn len(&mut self, value: usize) -> Option<()> {
        self.u64(u64::try_from(value).ok()?);
        Some(())
    }

    fn bytes(&mut self, value: &[u8]) -> Option<()> {
        self.len(value.len())?;
        self.0.update(value);
        Some(())
    }

    fn str(&mut self, value: &str) -> Option<()> {
        self.bytes(value.as_bytes())
    }

    fn finish(self) -> [u8; 32] {
        self.0.finalize().into()
    }
}

impl JitCertificate {
    /// Build a certificate from a verification report, function, and the
    /// byte range the encoded function occupies in the executable buffer.
    ///
    /// This is the primary constructor used by `JitCompiler::compile_raw`.
    /// The returned certificate is self-contained and does not borrow
    /// from `func`.
    #[cfg(feature = "verify")]
    pub(crate) fn from_report(
        func: &MachFunction,
        report: &FunctionVerificationReport,
        code_range: Range<u64>,
        _target: &str,
        verifier_input_digest: [u8; 32],
        normalized_machine_code_digest: [u8; 32],
    ) -> Self {
        Self::from_report_with_pair_policy(
            func,
            report,
            code_range,
            verifier_input_digest,
            normalized_machine_code_digest,
            true,
        )
    }

    /// Core artifacts already retain exact TV-1/TV-2 provenance evidence and
    /// must remain compact after dropping MachIR. The Phase-1 opcode-name pair
    /// table is diagnostic-only, allocates one `String` per machine
    /// instruction, and carries no proof authority, so this constructor omits
    /// it while retaining the complete semantic certificate chain.
    #[cfg(feature = "verify")]
    pub(crate) fn from_report_for_core_artifact(
        func: &MachFunction,
        report: &FunctionVerificationReport,
        code_range: Range<u64>,
        verifier_input_digest: [u8; 32],
        normalized_machine_code_digest: [u8; 32],
    ) -> Self {
        Self::from_report_with_pair_policy(
            func,
            report,
            code_range,
            verifier_input_digest,
            normalized_machine_code_digest,
            false,
        )
    }

    /// Only the private real-storage owner can create this conditional-call
    /// certificate. Weak custody prevents a cloned/exported certificate from
    /// retaining authority after that actual mapping/entry owner is gone.
    #[cfg(feature = "verify")]
    pub(crate) fn from_physically_bound_peer(
        func: &MachFunction,
        report: &FunctionVerificationReport,
        range: Range<u64>,
        input: [u8; 32],
        code: [u8; 32],
        owner: &std::sync::Arc<crate::compiler::core_peer_entry::CoreBoundPeerProof>,
    ) -> Self {
        let mut certificate = Self::from_report_for_core_artifact(func, report, range, input, code);
        certificate.peer_entry_binding = Some(PeerEntryCertificateBinding {
            owner: PhysicalEntryOwner::Peer(std::sync::Arc::downgrade(owner)),
            digest: owner.binding_digest(),
        });
        certificate
    }

    #[cfg(feature = "source-defined-call")]
    pub(crate) fn with_physically_bound_context_output(
        mut self,
        owner: &std::sync::Arc<crate::compiler::core_context_output::CoreBoundContextOutputProof>,
    ) -> Self {
        self.peer_entry_binding = Some(PeerEntryCertificateBinding {
            owner: PhysicalEntryOwner::ContextOutput(std::sync::Arc::downgrade(owner)),
            digest: owner.binding_digest(),
        });
        self
    }

    #[cfg(feature = "source-defined-call")]
    pub(crate) fn with_physically_bound_four_pointer_status(
        mut self,
        owner: &std::sync::Arc<
            crate::compiler::core_four_pointer_status::CoreBoundFourPointerStatusProof,
        >,
    ) -> Self {
        self.peer_entry_binding = Some(PeerEntryCertificateBinding {
            owner: PhysicalEntryOwner::FourPointerStatus(std::sync::Arc::downgrade(owner)),
            digest: owner.binding_digest(),
        });
        self
    }
    #[cfg(feature = "verify")]
    fn peer_storage_is_live(&self) -> bool {
        self.peer_entry_binding
            .as_ref()
            .is_none_or(|binding| match &binding.owner {
                #[cfg(feature = "source-defined-call")]
                PhysicalEntryOwner::FourPointerStatus(weak) => {
                    weak.upgrade().is_some_and(|owner| {
                        owner.matches_certificate(
                            &self.function,
                            &self.verifier_input_sha256,
                            &self.normalized_machine_code_sha256,
                            binding.digest,
                        )
                    })
                }
                PhysicalEntryOwner::Peer(weak) => weak.upgrade().is_some_and(|owner| {
                    owner.matches_certificate(
                        &self.function,
                        &self.verifier_input_sha256,
                        &self.normalized_machine_code_sha256,
                        binding.digest,
                    )
                }),
                #[cfg(feature = "source-defined-call")]
                PhysicalEntryOwner::ContextOutput(weak) => weak.upgrade().is_some_and(|owner| {
                    owner.matches_certificate(
                        &self.function,
                        &self.verifier_input_sha256,
                        &self.normalized_machine_code_sha256,
                        binding.digest,
                    )
                }),
            })
    }

    #[cfg(feature = "verify")]
    fn from_report_with_pair_policy(
        func: &MachFunction,
        report: &FunctionVerificationReport,
        code_range: Range<u64>,
        verifier_input_digest: [u8; 32],
        normalized_machine_code_digest: [u8; 32],
        retain_diagnostic_pairs: bool,
    ) -> Self {
        let function = func.name.clone();
        let trust_ir_pairs = if retain_diagnostic_pairs {
            build_trust_ir_pairs(func)
        } else {
            Vec::new()
        };

        let mut chain = CertificateChain::new(function.clone());
        for ir in &report.instructions {
            if let Some(cert) = instruction_report_to_cert(ir) {
                chain.add(cert);
            }
        }

        // Never let an empty/all-pseudo report certify itself by vacuous truth.
        // Statistical sampling is not a proof: the verifier reports a sampled
        // instruction as unverified, so the opcode inventory below refuses it.
        let opcode_inventory = report.emitted_opcode_inventory();
        let verified = report.precondition_failure.is_none()
            && report.genuinely_verified_count() > 0
            && report.degenerate_verified_count() == 0
            && report.failed_count() == 0
            && opcode_inventory.is_promotable();
        let coverage_pct = report.genuine_coverage_percent();

        // `build_trust_ir_pairs` is only an opcode-name classifier. Exporting a
        // LoweringCertificate here would put a MachFunction digest in its
        // TrustIR field and overstate the authority of this Phase-1 check.
        let lowering_certificate = None;
        let normalized_machine_code_sha256 = digest_hex(&normalized_machine_code_digest);

        Self {
            function,
            code_range,
            verifier_input_sha256: digest_hex(&verifier_input_digest),
            normalized_machine_code_sha256,
            trust_ir_pairs,
            chain,
            lowering_certificate,
            verified,
            structural_return: None,
            coverage_pct,
            served_from_cache: false,
            ay_refusal_note: None,
            peer_entry_binding: None,
        }
    }

    /// Stub constructor for `verify`-disabled builds. Never populated in
    /// practice because the no-verify `ExecutableBuffer` path skips
    /// certificate construction entirely; exposed so the struct compiles.
    #[cfg(not(feature = "verify"))]
    #[allow(dead_code)]
    pub(crate) fn empty(function: String, code_range: Range<u64>) -> Self {
        Self {
            function,
            code_range,
            verifier_input_sha256: String::new(),
            normalized_machine_code_sha256: String::new(),
            trust_ir_pairs: Vec::new(),
            verified: false,
            coverage_pct: 0.0,
            served_from_cache: false,
            ay_refusal_note: None,
        }
    }

    /// This certificate, carrying `note`: the AY refusal note of the
    /// function-verification request its report came from
    /// (`trust_cg_verify::CapturedFunctionVerificationReport::ay_refusal_note`).
    #[cfg_attr(not(feature = "verify"), allow(dead_code))]
    pub(crate) fn with_request_ay_refusal_note(mut self, note: Option<String>) -> Self {
        self.ay_refusal_note = note;
        self
    }

    /// The AY refusal note of the request this certificate's report came
    /// from (`None` when that request had an AY bound, or the build records
    /// none). It was resolved once with the request, never again.
    pub fn ay_refusal_note(&self) -> Option<&str> {
        self.ay_refusal_note.as_deref()
    }

    /// Transport an already checked certificate onto the exact same bytes at
    /// a final image range. This is publication, not a cache hit; the shared
    /// installed-byte replay independently checks the transported range.
    #[cfg(feature = "verify")]
    pub(crate) fn rebound_for_publication(&self, code_range: Range<u64>) -> Self {
        let mut certificate = self.clone();
        certificate.code_range = code_range;
        certificate
    }

    /// Return a clone of this certificate rebound to a new code range.
    ///
    /// Used when a cached verdict (JIT-5) is reattached to a fresh executable
    /// buffer where the same function landed at a different offset. Everything
    /// else — the verified verdict, the proof chain, the bytes-bound lowering
    /// certificate — is unchanged, because the cache key already proved the
    /// emitted bytes are identical.
    // Consumed only by the verifying JIT cache path (feature = "verify").
    #[cfg_attr(not(feature = "verify"), allow(dead_code))]
    pub(crate) fn rebound_from_cache(&self, code_range: Range<u64>) -> Self {
        let mut cloned = self.clone();
        cloned.code_range = code_range;
        cloned.served_from_cache = true;
        cloned
    }

    /// Function name this certificate covers.
    pub fn function(&self) -> &str {
        &self.function
    }

    /// Half-open byte range `[start, end)` of this function's code within
    /// the owning `ExecutableBuffer`.
    pub fn code_range(&self) -> Range<u64> {
        self.code_range.clone()
    }

    /// SHA-256 identity of the complete verifier-visible machine function.
    pub fn verifier_input_sha256(&self) -> &str {
        &self.verifier_input_sha256
    }

    /// SHA-256 of the normalized pre-relocation bytes used as verification and
    /// cache input. This is distinct from exact sealed-image integrity.
    pub fn normalized_machine_code_sha256(&self) -> &str {
        &self.normalized_machine_code_sha256
    }

    /// trust_ir → MachInst provenance entries.
    pub fn trust_ir_pairs(&self) -> &[TrustIrPair] {
        &self.trust_ir_pairs
    }

    /// Deterministic identity of the certificate's proof evidence for a sealed
    /// Core artifact.
    ///
    /// This deliberately excludes delivery/layout telemetry (`code_range`,
    /// cache-hit state, coverage formatting, creation timestamps, durations)
    /// and the coarse Phase-1 opcode-name table. It includes the accepted
    /// verdict, both verifier/byte digests, and an exhaustive typed encoding of
    /// every proof-chain and lowering-certificate semantic field. The legacy
    /// `verifier_input_sha256` binds the current toolchain's complete machine
    /// identity and, when supplied, canonical LIR source, so this is scoped
    /// to the compiler/build identity rather than advertised as a stable wire
    /// format across Rust or TrustCG revisions. `None` is possible only on a
    /// platform whose address-space length cannot fit the canonical `u64`
    /// sequence framing.
    #[cfg(feature = "verify")]
    pub(crate) fn core_semantic_digest(&self) -> Option<[u8; 32]> {
        let Self {
            function,
            code_range: _,
            verifier_input_sha256,
            normalized_machine_code_sha256,
            trust_ir_pairs: _,
            chain,
            lowering_certificate,
            verified,
            structural_return,
            coverage_pct: _,
            served_from_cache: _,
            ay_refusal_note: _,
            peer_entry_binding,
        } = self;

        let mut seal = CoreCertificateSemanticHasher::new();
        seal.str(function)?;
        seal.str(verifier_input_sha256)?;
        seal.str(normalized_machine_code_sha256)?;
        seal.u8(u8::from(*verified));
        match structural_return {
            None => seal.u8(0),
            Some(evidence) => {
                seal.u8(1);
                seal.bytes(evidence.input_digest())?;
            }
        }

        let CertificateChain {
            compilation_unit,
            certificates,
            created_epoch_secs: _,
        } = chain;
        seal.str(compilation_unit)?;
        seal.len(certificates.len())?;
        for certificate in certificates {
            seal_proof_certificate_semantics(&mut seal, certificate)?;
        }

        match lowering_certificate {
            None => seal.u8(0),
            Some(certificate) => {
                seal.u8(1);
                seal_lowering_certificate_semantics(&mut seal, certificate)?;
            }
        }
        if let Some(binding) = peer_entry_binding {
            seal.str(match &binding.owner {
                PhysicalEntryOwner::Peer(_) => "trust-cg.physically-owned-peer-entry.v1",
                #[cfg(feature = "source-defined-call")]
                PhysicalEntryOwner::FourPointerStatus(_) => {
                    "trust-cg.physically-owned-four-pointer-status-entry.v1"
                }
                #[cfg(feature = "source-defined-call")]
                PhysicalEntryOwner::ContextOutput(_) => {
                    "trust-cg.physically-owned-context-output-entry.v1"
                }
            })?;
            seal.bytes(&binding.digest.bytes)?;
        }
        Some(seal.finish())
    }

    /// Returns true iff this function has non-vacuous, proof-grade machine-IR
    /// evidence accepted by the verifier. This does not yet claim end-to-end
    /// TrustIR lowering provenance or proof coverage for auxiliary bytes.
    pub fn is_verified(&self) -> bool {
        #[cfg(feature = "verify")]
        {
            self.verified && self.peer_storage_is_live()
        }
        #[cfg(not(feature = "verify"))]
        {
            self.verified
        }
    }

    /// Exact RET-only source/ABI evidence, separately classified from
    /// non-vacuous instruction proofs. Raw or empty reports cannot mint it.
    #[cfg(feature = "verify")]
    pub(crate) fn with_checked_structural_return(
        mut self,
        captured: &trust_cg_verify::CapturedFunctionVerificationReport,
        function: &MachFunction,
        source: Option<&trust_cg_lower::Function>,
    ) -> Self {
        if !self.verified
            && let Some(source) = source
        {
            self.structural_return = captured.checked_aarch64_structural_return(function, source);
        }
        self
    }

    /// Whether complete semantics are checked by instruction proofs or the
    /// exact source-bound RET-only structural checker. Structural evidence
    /// does not make `is_verified()` true or increase coverage.
    pub fn has_checked_semantics(&self) -> bool {
        #[cfg(feature = "verify")]
        {
            (self.verified || self.structural_return.is_some()) && self.peer_storage_is_live()
        }
        #[cfg(not(feature = "verify"))]
        {
            self.verified
        }
    }

    /// Coverage percentage: verified / (total - skipped) * 100.
    pub fn coverage_percent(&self) -> f64 {
        #[cfg(feature = "verify")]
        if !self.peer_storage_is_live() {
            return 0.0;
        }
        self.coverage_pct
    }

    /// Whether this certificate instance was served from the JIT verdict cache
    /// without rerunning the verifier.
    pub fn served_from_cache(&self) -> bool {
        self.served_from_cache
    }

    /// Historical verification summary. It carries no physical entry permission;
    /// checked status must also pass `has_checked_semantics`/`replay_check`.
    /// Opaque owned-peer entries expose no certificate or chain projection.
    /// Available only with the `verify` feature enabled.
    #[cfg(feature = "verify")]
    pub fn chain(&self) -> &CertificateChain {
        &self.chain
    }

    /// Function-level TrustIR lowering certificate. The AArch64 Phase-1 JIT
    /// returns `None` until exact TrustIR-to-MachIR provenance is available.
    #[cfg(feature = "verify")]
    pub fn lowering_certificate(&self) -> Option<&LoweringCertificate> {
        self.lowering_certificate.as_ref()
    }

    /// Check consistency of the certificate summary's stored hashes.
    ///
    /// Re-derives a stable hash from each certificate's
    /// `(obligation_name, solver, strength, result)` tuple and confirms it
    /// matches the stored `formula_hash`. A changed tuple with its old hash
    /// fails this check.
    ///
    /// Independent AY/Clean proof replay happens in the verifier before
    /// certificate construction. This method checks neither that proof nor
    /// the executable bytes; it can also succeed on an empty chain. Use
    /// [`Self::is_verified`] for the non-vacuous verifier verdict.
    #[cfg(feature = "verify")]
    pub fn replay_check(&self) -> bool {
        if !self.peer_storage_is_live() {
            return false;
        }
        for cert in &self.chain.certificates {
            if cert.formula_hash != expected_formula_hash(cert) {
                return false;
            }
        }
        // A certificate with an empty chain is considered consistent —
        // `replay_check` only fails when at least one stored entry has
        // been tampered with. `is_verified` captures the "had any proof"
        // question for callers that care.
        true
    }

    /// Stub replay check for no-verify builds; always returns `true`.
    #[cfg(not(feature = "verify"))]
    pub fn replay_check(&self) -> bool {
        true
    }

    /// Serialize this certificate to a compact JSON object. When the
    /// `verify` feature is disabled the `chain` field is omitted.
    pub fn to_json(&self) -> String {
        let mut out = String::from("{\n");
        out.push_str(&format!(
            "  \"function\": \"{}\",\n",
            escape_json(&self.function)
        ));
        out.push_str(&format!(
            "  \"code_range\": [{}, {}],\n",
            self.code_range.start, self.code_range.end
        ));
        out.push_str(&format!(
            "  \"verifier_input_sha256\": \"{}\",\n",
            self.verifier_input_sha256
        ));
        out.push_str(&format!(
            "  \"normalized_machine_code_sha256\": \"{}\",\n",
            self.normalized_machine_code_sha256
        ));
        out.push_str(&format!("  \"verified\": {},\n", self.is_verified()));
        #[cfg(feature = "verify")]
        out.push_str(&format!(
            "  \"source_checked_structural_return\": {},\n",
            self.structural_return.is_some()
        ));
        out.push_str(&format!(
            "  \"served_from_cache\": {},\n",
            self.served_from_cache
        ));
        out.push_str(&format!(
            "  \"coverage_percent\": {:.4},\n",
            self.coverage_percent()
        ));
        out.push_str("  \"trust_ir_pairs\": [");
        for (i, p) in self.trust_ir_pairs.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            out.push_str(&format!(
                "{{\"trust_ir_op\": \"{}\", \"mach_insts\": [{}, {}]}}",
                escape_json(&p.trust_ir_op),
                p.mach_insts.start,
                p.mach_insts.end
            ));
        }
        out.push(']');

        #[cfg(feature = "verify")]
        {
            out.push_str(",\n  \"chain\": ");
            out.push_str(&self.chain.to_json());
        }

        out.push_str("\n}");
        out
    }
}

#[cfg(feature = "verify")]
fn seal_proof_certificate_semantics(
    seal: &mut CoreCertificateSemanticHasher,
    certificate: &ProofCertificate,
) -> Option<()> {
    let ProofCertificate {
        obligation_name,
        result,
        solver,
        strength,
        check_kind,
        // Replay-check checksum derived from the other fields below. It is a
        // local tamper sentinel, not an independent formula identity, and its
        // DefaultHasher/Debug construction is deliberately excluded from the
        // canonical Core evidence projection.
        formula_hash: _,
        timestamp_epoch_secs: _,
        duration_ms: _,
    } = certificate;
    seal.str(obligation_name)?;
    match result {
        CertificateResult::Verified => seal.u8(0),
        CertificateResult::Failed { counterexample } => {
            seal.u8(1);
            seal.str(counterexample)?;
        }
        CertificateResult::Timeout { seconds } => {
            seal.u8(2);
            seal.u64(seconds.to_bits());
        }
        CertificateResult::Skipped { reason } => {
            seal.u8(3);
            seal.str(reason)?;
        }
    }
    match solver {
        SolverUsed::MockExhaustive => seal.u8(0),
        SolverUsed::MockStatistical { samples } => {
            seal.u8(1);
            seal.u64(*samples);
        }
        SolverUsed::AYCli => seal.u8(2),
        SolverUsed::AYNative => seal.u8(3),
        SolverUsed::Z3Cli => seal.u8(4),
    }
    seal_verification_strength(seal, strength);
    match check_kind {
        None => seal.u8(0),
        Some(kind) => {
            seal.u8(1);
            seal.u8(match kind {
                TransvalCheckKind::DataFlow => 0,
                TransvalCheckKind::ControlFlow => 1,
                TransvalCheckKind::ReturnValue => 2,
                TransvalCheckKind::Termination => 3,
                TransvalCheckKind::InstructionLowering => 4,
                TransvalCheckKind::PeepholeOptimization => 5,
                TransvalCheckKind::MemoryModel => 6,
                TransvalCheckKind::RegisterAllocation => 7,
                TransvalCheckKind::Vectorization => 8,
            });
        }
    }
    Some(())
}

#[cfg(feature = "verify")]
fn seal_verification_strength(
    seal: &mut CoreCertificateSemanticHasher,
    strength: &VerificationStrength,
) {
    match strength {
        VerificationStrength::Exhaustive => seal.u8(0),
        VerificationStrength::Statistical { sample_count } => {
            seal.u8(1);
            seal.u64(*sample_count);
        }
        VerificationStrength::Formal => seal.u8(2),
    }
}

#[cfg(feature = "verify")]
fn seal_lowering_proof_strength(
    seal: &mut CoreCertificateSemanticHasher,
    strength: &LoweringProofStrength,
) {
    match strength {
        LoweringProofStrength::Sampled { sample_count } => {
            seal.u8(0);
            seal.u64(*sample_count);
        }
        LoweringProofStrength::ExhaustiveFinite { state_count } => {
            seal.u8(1);
            match state_count {
                None => seal.u8(0),
                Some(state_count) => {
                    seal.u8(1);
                    seal.u64(*state_count);
                }
            }
        }
        LoweringProofStrength::SmtUnsat => seal.u8(2),
    }
}

#[cfg(feature = "verify")]
fn seal_lowering_certificate_semantics(
    seal: &mut CoreCertificateSemanticHasher,
    certificate: &LoweringCertificate,
) -> Option<()> {
    let LoweringCertificate {
        schema,
        function,
        target,
        trust_ir_hash,
        machine_code_hash,
        compiler_config_hash,
        rule_proofs,
        overall_strength,
        covered_span,
        result,
        solver,
        ay,
        total_time_ms: _,
        created_epoch_secs: _,
    } = certificate;
    // WS7.2: one value, so nothing to seal; a second value (a trust-ir ->
    // machine span, WS7.16) must enter the seal, which this match forces.
    match covered_span {
        trust_cg_verify::proof_certificate::CoveredSpan::LirToMachine => {}
    }
    seal.str(schema)?;
    seal.str(function)?;
    seal.str(target)?;
    seal.str(trust_ir_hash)?;
    seal.str(machine_code_hash)?;
    seal.str(compiler_config_hash)?;
    seal.len(rule_proofs.len())?;
    for proof in rule_proofs {
        let LoweringRuleProof {
            rule_name,
            check_kind,
            result,
            obligation_hash,
            proof_hash,
        } = proof;
        seal.str(rule_name)?;
        seal.str(check_kind)?;
        match result {
            LoweringVerification::Proved {
                strength,
                solver,
                time_ms: _,
            } => {
                seal.u8(0);
                seal_lowering_proof_strength(seal, strength);
                seal.str(solver)?;
            }
        }
        seal.str(obligation_hash)?;
        seal.str(proof_hash)?;
    }
    seal_lowering_proof_strength(seal, overall_strength);
    match result {
        LoweringCertificateStatus::Verified => seal.u8(0),
    }
    let LoweringSolverSummary {
        name,
        version,
        total_time_ms: _,
    } = solver;
    seal.str(name)?;
    seal.str(version)?;
    // The formal-certificate AY record is sealed only when present, so every
    // certificate without one keeps its exact prior seal. This is the final
    // item of the lowering certificate, which is itself the final item of the
    // core seal (see `seal_lowering_certificate_semantics`'s caller), so the
    // optional suffix cannot alias a following field.
    if let Some(ay) = ay {
        seal.u8(1);
        seal.str(ay)?;
    }
    Some(())
}

// ---------------------------------------------------------------------------
// Internal helpers (feature-gated — all live inside the verify world)
// ---------------------------------------------------------------------------

/// Map an AArch64 opcode to a trust_ir operation name for the Phase-1 lookup
/// table. Returns "<opaque>" for any opcode not in the lookup.
#[cfg(feature = "verify")]
fn opcode_to_trust_ir_op(opcode: AArch64Opcode) -> &'static str {
    use AArch64Opcode::*;
    match opcode {
        AddRR | AddRI | AddRIShift12 => "Iadd_I32",
        SubRR | SubRI => "Isub_I32",
        MulRR => "Imul_I32",
        Neg => "Ineg_I32",
        SDiv => "Isdiv_I32",
        UDiv => "Iudiv_I32",
        CmpRR | CmpRI => "Icmp",
        Tst => "Itst",
        BCond | Bcc => "Ibrcond",
        AndRR | AndRI => "Iand",
        OrrRR | OrrRI => "Ior",
        EorRR | EorRI => "Ixor",
        LslRR | LslRI => "Ishl",
        LsrRR | LsrRI => "Ilshr",
        AsrRR | AsrRI => "Iashr",
        CSet => "Icset",
        FaddRR => "Fadd",
        FsubRR => "Fsub",
        FmulRR => "Fmul",
        FnegRR => "Fneg",
        _ => "<opaque>",
    }
}

/// Build a one-to-one TrustIrPair list: each MachInst in `func.insts`
/// produces a single pair with a unit range `[i, i+1)`. Coalescing runs
/// of the same trust_ir op is intentionally left for Phase 2 when real
/// provenance is available.
#[cfg(feature = "verify")]
fn build_trust_ir_pairs(func: &MachFunction) -> Vec<TrustIrPair> {
    func.insts
        .iter()
        .enumerate()
        .map(|(i, inst)| TrustIrPair {
            trust_ir_op: opcode_to_trust_ir_op(inst.opcode).to_string(),
            mach_insts: (i as u32)..((i as u32) + 1),
        })
        .collect()
}

#[cfg(all(feature = "verify", test))]
pub(crate) fn canonical_jit_function_bytes(
    func: &MachFunction,
) -> Result<Vec<u8>, JitIdentityEncodingError> {
    let mut out = String::new();
    write_aarch64_verifier_identity(func, &mut out)?;
    Ok(out.into_bytes())
}

#[cfg(feature = "verify")]
fn write_aarch64_verifier_identity(
    func: &MachFunction,
    out: &mut impl std::fmt::Write,
) -> std::fmt::Result {
    // `MachFunction` contains only ordered vectors/BTreeMaps. Its complete
    // derived Debug form gives a deterministic snapshot of every
    // verifier-visible field, including implicit defs/uses and lowering
    // provenance. Derived Debug renders all NaNs identically, however, so bind
    // every floating immediate again by raw IEEE payload and structural index.
    writeln!(out, "trust-cg.jit.aarch64-verifier-input.v3")?;
    writeln!(out, "{func:#?}")?;
    let mut payload_count = 0usize;
    for (instruction_index, instruction) in func.insts.iter().enumerate() {
        for (operand_index, operand) in instruction.operands.iter().enumerate() {
            if let trust_cg_ir::MachOperand::FImm(value) = operand {
                writeln!(
                    out,
                    "float_payload[{instruction_index}][{operand_index}]={:016x}",
                    value.to_bits()
                )?;
                payload_count += 1;
            }
        }
    }
    writeln!(out, "float_payloads={payload_count}")
}

#[cfg(feature = "verify")]
struct Sha256FmtWriter<'a>(&'a mut Sha256);

#[cfg(feature = "verify")]
impl std::fmt::Write for Sha256FmtWriter<'_> {
    fn write_str(&mut self, value: &str) -> std::fmt::Result {
        self.0.update(value.as_bytes());
        Ok(())
    }
}

#[cfg(feature = "verify")]
fn formatted_sha256(
    write: impl FnOnce(&mut Sha256FmtWriter<'_>) -> std::fmt::Result,
) -> Result<[u8; 32], JitIdentityEncodingError> {
    let mut hasher = Sha256::new();
    write(&mut Sha256FmtWriter(&mut hasher))?;
    Ok(hasher.finalize().into())
}

#[cfg(feature = "verify")]
pub(crate) fn aarch64_verifier_input_digest(
    func: &MachFunction,
) -> Result<[u8; 32], JitIdentityEncodingError> {
    formatted_sha256(|out| write_aarch64_verifier_identity(func, out))
}

/// Source-aware certificate identity, separate from the legacy raw-MachIR
/// digest. Stream both complete inputs without cloning their graphs. Absence
/// preserves the exact existing raw identity; it cannot alias source presence.
#[cfg(feature = "verify")]
pub(crate) fn aarch64_verifier_input_digest_with_lir(
    func: &MachFunction,
    lir_source: Option<&trust_cg_lower::Function>,
) -> Result<[u8; 32], JitIdentityEncodingError> {
    let machine = aarch64_verifier_input_digest(func)?;
    let Some(lir_source) = lir_source else {
        return Ok(machine);
    };
    let lir = formatted_sha256(|out| lir_source.write_canonical_verifier_identity(out))?;
    let mut hasher = Sha256::new();
    hasher.update(b"trust-cg.jit.aarch64-complete-verifier-input.v1\0");
    hasher.update(machine);
    hasher.update(lir);
    Ok(hasher.finalize().into())
}

#[cfg(feature = "verify")]
pub(crate) fn aarch64_verifier_input_digest_with_modules(
    func: &MachFunction,
    lir_source: Option<&trust_cg_lower::Function>,
    source: &trust_cg_verify::FunctionSourceModules<'_>,
) -> Result<[u8; 32], JitIdentityEncodingError> {
    let input = aarch64_verifier_input_digest_with_lir(func, lir_source)?;
    let mut hash = Sha256::new();
    hash.update(b"trust-cg.jit.aarch64-source-modules-input.v1\0");
    hash.update(input);
    hash.update(source.digest());
    Ok(hash.finalize().into())
}

/// The complete x86-64 verifier input: pre-RA ISel, the calling convention
/// the verifier was given (the source-bound body theorem depends on it), the
/// module definitions that can change the function's verdict (OD-210,
/// [`trust_cg_verify::X86ModuleDefinitions::input_line`]; nothing where none
/// can) and the exact LIR. A cached Formal report can never be reused under
/// another convention, or in a module that defines a runtime routine its
/// theorem would trust.
#[cfg(feature = "verify")]
pub(crate) fn x86_verifier_input_digest(
    func: &trust_cg_lower::x86_64_isel::X86ISelFunction,
    lir_source: &trust_cg_lower::Function,
    abi: Option<trust_cg_verify::X86SourceBoundAbi>,
    module: Option<&trust_cg_verify::X86ModuleDefinitions>,
) -> Result<[u8; 32], JitIdentityEncodingError> {
    let isel = formatted_sha256(|out| func.write_canonical_verifier_identity(out))?;
    let lir = formatted_sha256(|out| lir_source.write_canonical_verifier_identity(out))?;
    let mut hasher = Sha256::new();
    hasher.update(b"trust-cg.jit.x86_64-complete-verifier-input.v2\0");
    hasher.update(isel);
    hasher.update(format!("x86_source_bound_abi={abi:?}\n").as_bytes());
    if let Some(line) = trust_cg_verify::X86ModuleDefinitions::input_line(module, lir_source) {
        hasher.update(format!("{line}\n").as_bytes());
    }
    hasher.update(lir);
    Ok(hasher.finalize().into())
}

/// Convert a single `InstructionVerificationResult` into a synthesized
/// [`ProofCertificate`]. Returns `None` for `Skipped` results (pseudo-ops
/// have no proof to record) and `None` for `Unverified` results (no proof
/// obligation matched — not a failure, just absence). `Failed` and
/// `Verified` both yield certificates.
#[cfg(feature = "verify")]
fn instruction_report_to_cert(
    ir: &trust_cg_verify::function_verifier::InstructionReport,
) -> Option<ProofCertificate> {
    let (obligation_name, result, strength, check_kind) = match &ir.result {
        InstructionVerificationResult::Verified {
            proof_name,
            category: _,
            strength,
            // Cert records the discharged binding for provenance; STRICT
            // degeneracy lives on the verification report's genuine_* tally.
            degenerate: _,
        } => (
            proof_name.clone(),
            CertificateResult::Verified,
            *strength,
            Some(TransvalCheckKind::InstructionLowering),
        ),
        InstructionVerificationResult::Failed { proof_name, detail } => (
            proof_name.clone(),
            CertificateResult::Failed {
                counterexample: detail.clone(),
            },
            VerificationStrength::Exhaustive,
            Some(TransvalCheckKind::InstructionLowering),
        ),
        InstructionVerificationResult::Unverified { .. }
        | InstructionVerificationResult::Skipped { .. } => return None,
    };

    let solver = strength_to_solver(&strength);
    let mut cert = ProofCertificate {
        obligation_name,
        result,
        solver,
        strength,
        check_kind,
        formula_hash: 0,
        timestamp_epoch_secs: now_epoch_secs(),
        duration_ms: 0,
    };
    cert.formula_hash = expected_formula_hash(&cert);
    Some(cert)
}

/// Map a verification strength back to the solver tag the verifier would
/// have used. Mirrors `proof_certificate::strength_to_solver` without
/// duplicating the helper.
#[cfg(feature = "verify")]
fn strength_to_solver(strength: &VerificationStrength) -> SolverUsed {
    match strength {
        VerificationStrength::Exhaustive => SolverUsed::MockExhaustive,
        VerificationStrength::Statistical { sample_count } => SolverUsed::MockStatistical {
            samples: *sample_count,
        },
        // Formal rows in the current lowering verifier come from the AY CLI
        // route (with independent Alethe checking), never an in-process AY API.
        VerificationStrength::Formal => SolverUsed::AYCli,
    }
}

/// Derive a stable hash for a certificate from its
/// (obligation_name, solver_tag, strength, result) tuple. Used both at
/// construction time and by `replay_check` to detect tampering. The hash
/// is deliberately name-based rather than formula-based: the full SMT
/// formula is not serialized into the certificate in Phase 1.
#[cfg(feature = "verify")]
fn expected_formula_hash(cert: &ProofCertificate) -> u64 {
    let mut h = DefaultHasher::new();
    h.write(cert.obligation_name.as_bytes());
    h.write(format!("{:?}", cert.solver).as_bytes());
    h.write(format!("{:?}", cert.strength).as_bytes());
    // Only the tag of the result, not the counterexample/reason — we
    // want the hash stable across identical Verified entries.
    h.write(result_tag(&cert.result).as_bytes());
    h.finish()
}

#[cfg(feature = "verify")]
fn result_tag(r: &CertificateResult) -> &'static str {
    match r {
        CertificateResult::Verified => "verified",
        CertificateResult::Failed { .. } => "failed",
        CertificateResult::Timeout { .. } => "timeout",
        CertificateResult::Skipped { .. } => "skipped",
    }
}

#[cfg(feature = "verify")]
fn now_epoch_secs() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs()
}

/// Minimal JSON escape usable from the jit module's `export_proofs`.
pub(crate) fn escape_for_export(s: &str) -> String {
    escape_json(s)
}

/// Minimal JSON escape for function names and trust_ir op strings.
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

// ---------------------------------------------------------------------------
// JIT-5 / JIT-6: content-addressed certificate cache
// ---------------------------------------------------------------------------
//
// `CachedVerified` JIT compiles require proof-grade verifier evidence for every
// function and exact integrity hashes for the published image. The expensive
// discharge is amortized across compiles with
// identical bytes, verifier semantics, symbolic fixups, and policy. This is the
// in-process cut of that cache (JIT-6 makes it disk-backed, reusing this
// complete identity contract). Soundness rules baked in here:
//
//   * the key is NEVER name-only — it folds a canonical CONTENT hash with a
//     CONFIG fingerprint (PROOF-2/PROOF-3 content-key discipline), so a verdict
//     can only ever be reused for identical work under identical settings;
//   * relocation placeholders cannot erase target name/binding identity, and
//     proof-visible IR/provenance cannot alias merely because encodings match;
//   * a cache MISS re-verifies (never skips); the caller populates on the way
//     out. Nothing here can turn an unverified function into a verified one.

use std::collections::{HashMap, VecDeque};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

/// Whether a deep verifier override makes the outer JIT certificate cache
/// ineligible for this compile.
///
/// These controls are still consumed below the public verifier API and are
/// not yet represented by one typed, immutable policy object. They can change
/// proof strength or acceptance. Bypassing the outer cache whenever one is
/// active prevents an override-specific discharge from consuming or
/// populating a default-policy verdict on either architecture.
#[cfg(feature = "verify")]
pub(crate) fn deep_verifier_override_disables_outer_cache() -> bool {
    trust_cg_process_env::var_os("TCG_NO_VERDICT_DB").is_some()
        || trust_cg_process_env::var_os("TCG_NO_PROOF_CACHE").is_some()
        || trust_cg_process_env::var_os("TCG_NO_SOLVER_SERVER").is_some()
        || trust_cg_process_env::var_os("AY_SOLVER_PATH").is_some()
        || trust_cg_process_env::var_os("TCG_EXTERNAL_CLEAN_CHECKER").is_some()
        || trust_cg_process_env::var_os("TCG_CLEAN_CHECKER").is_some()
        || trust_cg_process_env::var_os("TCG_PRECISE_CITATIONS").is_some()
}

/// Resolve the JIT certificate-cache transport policy for one compile request.
///
/// This must be evaluated at the request boundary, not while initializing the
/// process-global cache: thread-scoped overrides and successive callers are
/// independent, and a temporary first caller must never freeze policy for the
/// lifetime of the process.
#[cfg(feature = "verify")]
pub(crate) fn jit_cert_cache_allowed_for_request() -> bool {
    !trust_cg_process_env::var("TCG_NO_JIT_CERT_CACHE").is_ok_and(|value| value == "1")
}

/// Content-addressed key for a per-function JIT verification verdict.
///
/// Both components are fixed-width SHA-256 digests. `content_sha256` covers the
/// canonical post-optimization form of the function (the exact input the
/// verifier and the encoder consume); `config_sha256` covers the compile
/// configuration fingerprint (target, opt level, alloc profile, validation
/// mode, and a compiler-rev salt) together with the exact verifier authority
/// (solver, clean checker, and sanitized child environment). Reusing a verdict
/// requires BOTH to match.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct JitCertCacheKey {
    /// SHA-256 of the canonical content the verdict was proven over.
    content_sha256: [u8; 32],
    /// SHA-256 of the config fingerprint and verifier authority.
    config_sha256: [u8; 32],
}

impl JitCertCacheKey {
    /// Build a key from the canonical content bytes, config fingerprint, and
    /// exact verifier authority. Never construct a key from a name alone.
    #[cfg(all(test, feature = "verify"))]
    pub(crate) fn new(
        content_bytes: &[u8],
        config_bytes: &[u8],
        verification_authority_id: &[u8; 32],
    ) -> Self {
        Self::from_content_digest(
            Sha256::digest(content_bytes).into(),
            config_bytes,
            verification_authority_id,
        )
    }

    /// Build a cache key over the complete verified-function and verifier
    /// authority identity.
    ///
    /// Machine bytes alone are insufficient: relocation holes erase symbol
    /// names and binding classes, while two functions with identical encoding
    /// can carry different proof/provenance inputs. Every production verifier
    /// cache lookup must bind all three content components below.
    #[cfg(all(test, feature = "verify"))]
    pub(crate) fn new_for_verified_function(
        emitted_bytes: &[u8],
        verifier_input: &[u8],
        symbolic_fixup_manifest: &[u8],
        config_bytes: &[u8],
        verification_authority_id: &[u8; 32],
    ) -> Self {
        let verifier_input_sha256 = Sha256::digest(verifier_input).into();
        Self::new_for_verified_function_digest(
            emitted_bytes,
            &verifier_input_sha256,
            symbolic_fixup_manifest,
            config_bytes,
            verification_authority_id,
        )
    }

    /// Production constructor for callers that stream the verifier input into
    /// SHA-256 instead of retaining a second full byte buffer.
    #[cfg(feature = "verify")]
    pub(crate) fn new_for_verified_function_digest(
        emitted_bytes: &[u8],
        verifier_input_sha256: &[u8; 32],
        symbolic_fixup_manifest: &[u8],
        config_bytes: &[u8],
        verification_authority_id: &[u8; 32],
    ) -> Self {
        let emitted_bytes_sha256 = Sha256::digest(emitted_bytes).into();
        Self::new_for_verified_function_digests(
            &emitted_bytes_sha256,
            verifier_input_sha256,
            symbolic_fixup_manifest,
            config_bytes,
            verification_authority_id,
        )
    }

    /// Build a key when both large verifier inputs have already been streamed
    /// into SHA-256 for certificate reporting. This avoids reading the emitted
    /// function body a second time on the AArch64 cold path.
    #[cfg(feature = "verify")]
    pub(crate) fn new_for_verified_function_digests(
        emitted_bytes_sha256: &[u8; 32],
        verifier_input_sha256: &[u8; 32],
        symbolic_fixup_manifest: &[u8],
        config_bytes: &[u8],
        verification_authority_id: &[u8; 32],
    ) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(b"trust-cg.jit-cert.verified-function-content.v3\0");
        hash_cache_key_part(&mut hasher, b"emitted-bytes-sha256", emitted_bytes_sha256);
        hash_cache_key_part(&mut hasher, b"verifier-input-sha256", verifier_input_sha256);
        hash_cache_key_part(
            &mut hasher,
            b"symbolic-fixup-manifest",
            symbolic_fixup_manifest,
        );
        Self::from_content_digest(
            hasher.finalize().into(),
            config_bytes,
            verification_authority_id,
        )
    }

    #[cfg(feature = "verify")]
    fn from_content_digest(
        content_digest: [u8; 32],
        config_bytes: &[u8],
        verification_authority_id: &[u8; 32],
    ) -> Self {
        let mut config_hasher = Sha256::new();
        config_hasher.update(b"trust-cg.jit-cert.config-authority.v1\0");
        hash_cache_key_part(&mut config_hasher, b"compiler-config", config_bytes);
        hash_cache_key_part(
            &mut config_hasher,
            b"verification-authority-id",
            verification_authority_id,
        );
        Self {
            content_sha256: content_digest,
            config_sha256: config_hasher.finalize().into(),
        }
    }
}

#[cfg(feature = "verify")]
fn hash_cache_key_part(hasher: &mut Sha256, label: &[u8], bytes: &[u8]) {
    hasher.update((label.len() as u64).to_be_bytes());
    hasher.update(label);
    hasher.update((bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
}

#[cfg(feature = "verify")]
fn bytes_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        out.push(char::from(HEX[(byte >> 4) as usize]));
        out.push(char::from(HEX[(byte & 0x0f) as usize]));
    }
    out
}

/// Lowercase hexadecimal form of a canonical SHA-256 digest.
#[cfg(feature = "verify")]
pub(crate) fn digest_hex(digest: &[u8; 32]) -> String {
    bytes_hex(digest)
}

/// Hash one already-materialized verifier input exactly once so callers can
/// share the fixed-width identity between cache keys and exported reporting.
#[cfg(feature = "verify")]
pub(crate) fn sha256_digest(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

fn push_cache_key_part(out: &mut Vec<u8>, label: &[u8], bytes: &[u8]) {
    out.extend_from_slice(&(label.len() as u64).to_be_bytes());
    out.extend_from_slice(label);
    out.extend_from_slice(&(bytes.len() as u64).to_be_bytes());
    out.extend_from_slice(bytes);
}

/// Canonical per-function AArch64 symbolic-fixup identity.
///
/// This is captured before module-absolute rebasing, with `body_offset` added
/// so profile trampolines remain part of the function-relative coordinate.
/// Target variant, raw name/index, relocation kind, TLS model, and addend all
/// affect the eventual executable even when the instruction placeholder bytes
/// are identical.
pub(crate) fn aarch64_symbolic_fixup_manifest(
    fixups: &crate::macho::fixup::FixupList,
    body_offset: u64,
) -> Result<Vec<u8>, JitIdentityEncodingError> {
    use crate::macho::fixup::FixupTarget;
    use trust_cg_ir::TlsModel;

    let mut out = Vec::new();
    out.extend_from_slice(b"trust-cg.jit.aarch64-symbolic-fixups.v1\0");
    out.extend_from_slice(&(fixups.len() as u64).to_be_bytes());
    for fixup in fixups.iter() {
        let offset = body_offset
            .checked_add(u64::from(fixup.offset))
            .ok_or(JitIdentityEncodingError::FixupOffsetOverflow)?;
        out.extend_from_slice(&offset.to_be_bytes());
        out.push(fixup.kind as u8);
        out.push(match fixup.tls_model {
            None => 0,
            Some(TlsModel::LocalExec) => 1,
            Some(TlsModel::InitialExec) => 2,
            Some(TlsModel::GeneralDynamic) => 3,
            Some(TlsModel::LocalDynamic) => 4,
            Some(TlsModel::Tlv) => 5,
        });
        match &fixup.target {
            FixupTarget::Symbol(index) => {
                out.push(0);
                out.extend_from_slice(&index.to_be_bytes());
            }
            FixupTarget::Section(section) => {
                out.push(1);
                out.extend_from_slice(&section.to_be_bytes());
            }
            FixupTarget::SymbolPlusOffset {
                symbol_index,
                section_offset,
            } => {
                out.push(2);
                out.extend_from_slice(&symbol_index.to_be_bytes());
                out.extend_from_slice(&section_offset.to_be_bytes());
            }
            FixupTarget::NamedSymbol(name) => {
                out.push(3);
                push_cache_key_part(&mut out, b"name", name.as_bytes());
            }
            FixupTarget::ExactNamedSymbol(name) => {
                out.push(4);
                push_cache_key_part(&mut out, b"exact-name", name.as_bytes());
            }
        }
        out.extend_from_slice(&fixup.addend.to_be_bytes());
    }
    Ok(out)
}

/// Canonical per-function x86-64 symbolic-fixup identity.
///
/// `CALL rel32` and RIP-relative symbol references contain zero displacement
/// placeholders before JIT patching, so their emitted bytes do not identify
/// the raw target name, exact/interposable policy, or address-materialization
/// kind. The manifest closes that alias for every symbolic x86 reference.
pub(crate) fn x86_symbolic_fixup_manifest(
    call_fixups: &[crate::x86_64::pipeline::X86CallFixup],
    global_ref_fixups: &[crate::x86_64::pipeline::X86GlobalRefFixup],
    body_offset: u64,
) -> Result<Vec<u8>, JitIdentityEncodingError> {
    use crate::x86_64::pipeline::X86SymbolRefFixupKind;

    enum Row<'a> {
        Call(&'a crate::x86_64::pipeline::X86CallFixup),
        Symbol(&'a crate::x86_64::pipeline::X86GlobalRefFixup),
    }

    let mut rows = Vec::with_capacity(call_fixups.len() + global_ref_fixups.len());
    rows.extend(call_fixups.iter().map(Row::Call));
    rows.extend(global_ref_fixups.iter().map(Row::Symbol));
    rows.sort_by_key(|row| match row {
        Row::Call(fixup) => (fixup.offset, 0u8),
        Row::Symbol(fixup) => (fixup.offset, 1u8),
    });

    let mut out = Vec::new();
    out.extend_from_slice(b"trust-cg.jit.x86_64-symbolic-fixups.v1\0");
    out.extend_from_slice(&(rows.len() as u64).to_be_bytes());
    for row in rows {
        match row {
            Row::Call(fixup) => {
                let offset = body_offset
                    .checked_add(fixup.offset as u64)
                    .ok_or(JitIdentityEncodingError::FixupOffsetOverflow)?;
                out.extend_from_slice(&offset.to_be_bytes());
                out.push(0);
                push_cache_key_part(&mut out, b"callee", fixup.callee.as_bytes());
                out.push(u8::from(fixup.exact_module));
            }
            Row::Symbol(fixup) => {
                let offset = body_offset
                    .checked_add(fixup.offset as u64)
                    .ok_or(JitIdentityEncodingError::FixupOffsetOverflow)?;
                out.extend_from_slice(&offset.to_be_bytes());
                out.push(1);
                push_cache_key_part(&mut out, b"symbol", fixup.symbol.as_bytes());
                out.push(match fixup.kind {
                    X86SymbolRefFixupKind::GlobalRef => 0,
                    X86SymbolRefFixupKind::ExternRefGot => 1,
                    X86SymbolRefFixupKind::TlsTlv => 2,
                    X86SymbolRefFixupKind::ExactFunctionAddr => 3,
                });
            }
        }
    }
    Ok(out)
}

/// Failure to encode all bytes required by a JIT verifier/cache identity.
/// Partial input never produces a reusable digest or fixup manifest.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum JitIdentityEncodingError {
    #[error("JIT verifier identity formatting failed: {0}")]
    Formatting(#[from] std::fmt::Error),
    #[error("JIT symbolic fixup offset exceeds the u64 identity domain")]
    FixupOffsetOverflow,
}

/// A cached per-function verdict, bound by its cache key to the normalized
/// pre-relocation byte image, verifier input, symbolic fixups, and policy.
#[derive(Debug)]
pub(crate) struct CachedFunctionVerdict {
    /// x86-64 per-instruction proof certificates (empty on other paths).
    pub(crate) x86_proof_certs: Vec<crate::compiler::ProofCertificate>,
    /// AArch64 buffer certificate (None on other paths).
    pub(crate) aarch64_cert: Option<JitCertificate>,
    /// Immutable verifier-owned attribution, retained for lookup validation.
    /// Transport-only cache fixtures have no receipt and cannot authorize a JIT hit.
    #[cfg(feature = "verify")]
    pub(crate) verification_report: Option<trust_cg_verify::CapturedFunctionVerificationReport>,
    /// The x86-64 ABI envelope verdict the certificates were built from, for
    /// a function whose source the envelope owner admits. A hit re-checks it
    /// against the request and the exact input before serving the entry.
    #[cfg(feature = "verify")]
    pub(crate) x86_envelope_report:
        Option<trust_cg_verify::x86_source_bound_envelope::X86EnvelopeReport>,
}

impl CachedFunctionVerdict {
    fn estimated_payload_bytes(&self) -> usize {
        let mut bytes = std::mem::size_of::<Self>().saturating_add(
            self.x86_proof_certs
                .capacity()
                .saturating_mul(std::mem::size_of::<crate::compiler::ProofCertificate>()),
        );
        for certificate in &self.x86_proof_certs {
            bytes = bytes
                .saturating_add(certificate.rule_name.capacity())
                .saturating_add(certificate.category.capacity())
                .saturating_add(certificate.strength.capacity())
                .saturating_add(certificate.function_name.capacity())
                .saturating_add(
                    certificate
                        .ay_refusal_note
                        .as_ref()
                        .map_or(0, String::capacity),
                );
        }
        if let Some(certificate) = &self.aarch64_cert {
            bytes = bytes.saturating_add(certificate.estimated_cache_bytes());
        }
        #[cfg(feature = "verify")]
        if let Some(report) = &self.verification_report {
            bytes = bytes.saturating_add(report.estimated_payload_bytes());
        }
        #[cfg(feature = "verify")]
        if let Some(report) = &self.x86_envelope_report {
            // Conservative: the report, its function name and one retained
            // theorem's rendered size.
            bytes = bytes
                .saturating_add(std::mem::size_of_val(report))
                .saturating_add(report.function_name().len())
                .saturating_add(report.estimated_theorem_bytes());
        }
        bytes
    }
}

impl JitCertificate {
    fn estimated_cache_bytes(&self) -> usize {
        let mut bytes = std::mem::size_of::<Self>()
            .saturating_add(self.function.capacity())
            .saturating_add(self.ay_refusal_note.as_ref().map_or(0, String::capacity))
            .saturating_add(self.verifier_input_sha256.capacity())
            .saturating_add(self.normalized_machine_code_sha256.capacity())
            .saturating_add(
                self.trust_ir_pairs
                    .capacity()
                    .saturating_mul(std::mem::size_of::<TrustIrPair>()),
            );
        for pair in &self.trust_ir_pairs {
            bytes = bytes.saturating_add(pair.trust_ir_op.capacity());
        }
        #[cfg(feature = "verify")]
        {
            bytes = bytes
                .saturating_add(self.chain.compilation_unit.capacity())
                .saturating_add(
                    self.chain
                        .certificates
                        .capacity()
                        .saturating_mul(std::mem::size_of::<ProofCertificate>()),
                );
            for certificate in &self.chain.certificates {
                bytes = bytes.saturating_add(certificate.obligation_name.capacity());
                match &certificate.result {
                    CertificateResult::Failed { counterexample } => {
                        bytes = bytes.saturating_add(counterexample.capacity());
                    }
                    CertificateResult::Skipped { reason } => {
                        bytes = bytes.saturating_add(reason.capacity());
                    }
                    CertificateResult::Verified | CertificateResult::Timeout { .. } => {}
                }
            }
        }
        bytes
    }
}

/// Cache hit/miss telemetry. All counters are process-monotonic within a
/// single [`JitCertCache`] instance.
#[derive(Debug, Default)]
pub struct JitCertCacheStats {
    /// Warm hits: verdict reused, bytes matched, verifier NOT re-run.
    pub hits: AtomicU64,
    /// Misses: verdict absent, full verification ran.
    pub misses: AtomicU64,
    /// Bytes-mismatch re-verifications: verdict present but the freshly
    /// emitted bytes did not match, so verification re-ran (fail-closed).
    pub reverifications: AtomicU64,
    /// Number of times the underlying verifier actually executed. On a warm
    /// hit this counter does NOT advance — the assertion behind
    /// "warm-cache hit does not re-spawn the solver".
    pub verifier_runs: AtomicU64,
    /// Entries evicted to enforce the resident cache bounds.
    pub evictions: AtomicU64,
}

const DEFAULT_JIT_CERT_CACHE_MAX_ENTRIES: usize = 2_048;
const DEFAULT_JIT_CERT_CACHE_MAX_PAYLOAD_BYTES: usize = 32 * 1024 * 1024;

#[derive(Debug)]
struct CachedEntry {
    verdict: Arc<CachedFunctionVerdict>,
    payload_bytes: usize,
}

#[derive(Debug, Default)]
struct JitCertCacheState {
    entries: HashMap<JitCertCacheKey, CachedEntry>,
    insertion_order: VecDeque<JitCertCacheKey>,
    resident_payload_bytes: usize,
}

impl JitCertCacheStats {
    fn snapshot(&self) -> (u64, u64, u64, u64) {
        (
            self.hits.load(Ordering::Relaxed),
            self.misses.load(Ordering::Relaxed),
            self.reverifications.load(Ordering::Relaxed),
            self.verifier_runs.load(Ordering::Relaxed),
        )
    }
}

/// In-process content-addressed JIT certificate cache (JIT-5).
///
/// Construct a fresh instance with [`Self::new`] for isolated per-test stats,
/// or share the process-global instance via [`Self::global`]. A cache built
/// with [`Self::disabled`] always misses. Request-specific bypasses such as
/// `AlwaysVerify` and `TCG_NO_JIT_CERT_CACHE=1` are resolved by callers and do
/// not mutate or permanently disable the process-global storage.
/// Poisoned storage always misses and declines writes. Its old contents are
/// never recovered into certificate authority; callers must verify again.
#[derive(Debug)]
pub struct JitCertCache {
    state: Mutex<JitCertCacheState>,
    stats: JitCertCacheStats,
    enabled: bool,
    max_entries: usize,
    max_payload_bytes: usize,
}

impl Default for JitCertCache {
    fn default() -> Self {
        Self::new()
    }
}

impl JitCertCache {
    /// A fresh, empty, enabled cache with its own stats.
    pub fn new() -> Self {
        Self::with_limits(
            true,
            DEFAULT_JIT_CERT_CACHE_MAX_ENTRIES,
            DEFAULT_JIT_CERT_CACHE_MAX_PAYLOAD_BYTES,
        )
    }

    /// A cache that never stores or serves entries — every lookup misses, so
    /// verification runs on every compile. Useful for explicit injection in
    /// tests and embedding APIs.
    pub fn disabled() -> Self {
        Self::with_limits(false, 0, 0)
    }

    fn with_limits(enabled: bool, max_entries: usize, max_payload_bytes: usize) -> Self {
        Self {
            state: Mutex::new(JitCertCacheState::default()),
            stats: JitCertCacheStats::default(),
            enabled,
            max_entries,
            max_payload_bytes,
        }
    }

    /// The process-global shared cache instance (default production cache).
    pub fn global() -> Arc<JitCertCache> {
        static GLOBAL: OnceLock<Arc<JitCertCache>> = OnceLock::new();
        GLOBAL.get_or_init(|| Arc::new(JitCertCache::new())).clone()
    }

    /// Whether caching is configured on. Poisoned storage still always misses
    /// and declines writes, even when this returns true.
    pub fn is_enabled(&self) -> bool {
        self.enabled
    }

    /// Look up a verdict. Returns a clone so the caller does not hold the lock.
    /// Does NOT touch stats — the caller records hit/miss after validating the
    /// bytes binding (a lookup that produces bytes-mismatched data is a
    /// re-verification, not a hit).
    /// A poisoned cache also misses; poison is not cleared or recovered.
    #[cfg_attr(not(feature = "verify"), allow(dead_code))]
    pub(crate) fn peek(&self, key: &JitCertCacheKey) -> Option<Arc<CachedFunctionVerdict>> {
        if !self.enabled {
            return None;
        }
        self.state
            .lock()
            .ok()?
            .entries
            .get(key)
            .map(|entry| Arc::clone(&entry.verdict))
    }

    /// Store (or overwrite) a verdict for `key`, unless storage is poisoned.
    #[cfg_attr(not(feature = "verify"), allow(dead_code))]
    pub(crate) fn store(&self, key: JitCertCacheKey, verdict: CachedFunctionVerdict) {
        if !self.enabled {
            return;
        }
        let payload_bytes = verdict
            .estimated_payload_bytes()
            .saturating_add(std::mem::size_of::<JitCertCacheKey>());
        if payload_bytes > self.max_payload_bytes || self.max_entries == 0 {
            return;
        }

        let Ok(mut state) = self.state.lock() else {
            // Cache storage is optional. Do not use a poisoned guard, and do
            // not turn successful fresh verification into a compiler panic.
            return;
        };
        if let Some(previous) = state.entries.remove(&key) {
            state.resident_payload_bytes = state
                .resident_payload_bytes
                .saturating_sub(previous.payload_bytes);
            state.insertion_order.retain(|queued| queued != &key);
        }
        state.resident_payload_bytes = state.resident_payload_bytes.saturating_add(payload_bytes);
        state.insertion_order.push_back(key.clone());
        state.entries.insert(
            key,
            CachedEntry {
                verdict: Arc::new(verdict),
                payload_bytes,
            },
        );

        let mut evicted = 0u64;
        while state.entries.len() > self.max_entries
            || state.resident_payload_bytes > self.max_payload_bytes
        {
            let Some(oldest) = state.insertion_order.pop_front() else {
                break;
            };
            if let Some(entry) = state.entries.remove(&oldest) {
                state.resident_payload_bytes = state
                    .resident_payload_bytes
                    .saturating_sub(entry.payload_bytes);
                evicted = evicted.saturating_add(1);
            }
        }
        drop(state);
        if evicted != 0 {
            self.stats.evictions.fetch_add(evicted, Ordering::Relaxed);
        }
    }

    /// Record a warm hit (verdict reused, verifier not run).
    pub fn record_hit(&self) {
        self.stats.hits.fetch_add(1, Ordering::Relaxed);
    }

    /// Record a miss (verdict absent, full verification ran).
    pub fn record_miss(&self) {
        self.stats.misses.fetch_add(1, Ordering::Relaxed);
        self.stats.verifier_runs.fetch_add(1, Ordering::Relaxed);
    }

    /// Record a bytes-mismatch re-verification (verdict present but stale bytes;
    /// verification re-ran fail-closed).
    pub fn record_reverification(&self) {
        self.stats.reverifications.fetch_add(1, Ordering::Relaxed);
        self.stats.verifier_runs.fetch_add(1, Ordering::Relaxed);
    }

    /// Record a verifier execution that deliberately bypassed cache lookup
    /// (AlwaysVerify or an untyped deep-policy override).
    pub fn record_uncached_verifier_run(&self) {
        self.stats.verifier_runs.fetch_add(1, Ordering::Relaxed);
    }

    /// `(hits, misses, reverifications, verifier_runs)`.
    pub fn stats(&self) -> (u64, u64, u64, u64) {
        self.stats.snapshot()
    }

    /// Number of times the underlying verifier actually ran through this cache.
    pub fn verifier_runs(&self) -> u64 {
        self.stats.verifier_runs.load(Ordering::Relaxed)
    }

    /// Number of entries evicted to maintain the bounded resident cache.
    pub fn evictions(&self) -> u64 {
        self.stats.evictions.load(Ordering::Relaxed)
    }
}

// ---------------------------------------------------------------------------
// Unit tests
// ---------------------------------------------------------------------------

#[cfg(all(test, feature = "verify"))]
mod tests {
    use super::*;
    use crate::macho::fixup::{Fixup, FixupList, FixupTarget};
    use crate::macho::reloc::AArch64RelocKind;
    use trust_cg_ir::aarch64_regs::{W0, X0};
    use trust_cg_ir::types::InstId;
    use trust_cg_ir::{MachInst, MachOperand, Signature};

    #[test]
    fn identity_formatter_refuses_partial_digest() {
        let result = formatted_sha256(|out| {
            use std::fmt::Write;
            out.write_str("partial identity")?;
            Err(std::fmt::Error)
        });
        assert_eq!(
            result,
            Err(JitIdentityEncodingError::Formatting(std::fmt::Error))
        );
    }

    #[test]
    fn symbolic_fixup_manifests_reject_offset_overflow() {
        let mut fixups = FixupList::new();
        fixups.push(Fixup {
            offset: 1,
            kind: AArch64RelocKind::Branch26,
            tls_model: None,
            target: FixupTarget::NamedSymbol("callee".into()),
            addend: 0,
        });
        assert_eq!(
            aarch64_symbolic_fixup_manifest(&fixups, u64::MAX),
            Err(JitIdentityEncodingError::FixupOffsetOverflow)
        );
        use crate::x86_64::pipeline::{X86CallFixup, X86GlobalRefFixup, X86SymbolRefFixupKind};
        let calls = [X86CallFixup {
            offset: 1,
            callee: "callee".into(),
            exact_module: false,
        }];
        assert_eq!(
            x86_symbolic_fixup_manifest(&calls, &[], u64::MAX),
            Err(JitIdentityEncodingError::FixupOffsetOverflow)
        );
        let globals = [X86GlobalRefFixup {
            offset: 1,
            symbol: "global".into(),
            kind: X86SymbolRefFixupKind::GlobalRef,
        }];
        assert_eq!(
            x86_symbolic_fixup_manifest(&[], &globals, u64::MAX),
            Err(JitIdentityEncodingError::FixupOffsetOverflow)
        );
        assert!(aarch64_symbolic_fixup_manifest(&fixups, u64::MAX - 1).is_ok());
        assert!(x86_symbolic_fixup_manifest(&calls, &globals, u64::MAX - 1).is_ok());
    }

    fn make_add_i32_func() -> MachFunction {
        let mut func = MachFunction::new("add".to_string(), Signature::new(vec![], vec![]));
        func.insts.push(MachInst::new(AArch64Opcode::AddRR, vec![]));
        func.blocks[0].insts.push(InstId(0));
        func
    }

    fn make_add_ret_func() -> MachFunction {
        let mut func = make_add_i32_func();
        func.insts.push(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.blocks[0].insts.push(InstId(1));
        func
    }

    fn make_genuine_cert_func() -> MachFunction {
        let mut func = MachFunction::new("add".to_string(), Signature::new(vec![], vec![]));
        func.insts.push(MachInst::new(
            AArch64Opcode::Movn,
            vec![MachOperand::PReg(W0), MachOperand::Imm(1)],
        ));
        func.blocks[0].insts.push(InstId(0));
        func
    }

    /// Certificate serialization tests use a synthetic, explicitly exhaustive
    /// proof row. Running a 32-bit AArch64 obligation through the sampling
    /// verifier and relabeling it would make the fixture itself dishonest.
    fn make_genuine_report() -> FunctionVerificationReport {
        FunctionVerificationReport {
            function_name: "add".to_string(),
            precondition_failure: None,
            instructions: vec![trust_cg_verify::function_verifier::InstructionReport {
                inst_index: 0,
                opcode: trust_cg_verify::function_verifier::InstructionOpcode::AArch64(
                    AArch64Opcode::Movn,
                ),
                result: InstructionVerificationResult::Verified {
                    proof_name: "synthetic exhaustive certificate fixture".to_string(),
                    category:
                        trust_cg_verify::proof_database::ProofCategory::ConstantMaterialization,
                    strength: VerificationStrength::Exhaustive,
                    degenerate: false,
                },
            }],
        }
    }

    fn make_cert(func: &MachFunction, report: &FunctionVerificationReport) -> JitCertificate {
        JitCertificate::from_report(
            func,
            report,
            0u64..4u64,
            "aarch64",
            aarch64_verifier_input_digest(func).unwrap(),
            Sha256::digest([0, 1, 2, 3]).into(),
        )
    }

    #[test]
    fn verified_function_cache_key_binds_every_semantic_component() {
        let authority_a = [0xa1; 32];
        let authority_b = [0xb2; 32];
        let baseline = JitCertCacheKey::new_for_verified_function(
            b"machine",
            b"verifier-a",
            b"fixup-a",
            b"config-a",
            &authority_a,
        );
        for distinct in [
            JitCertCacheKey::new_for_verified_function(
                b"machine-2",
                b"verifier-a",
                b"fixup-a",
                b"config-a",
                &authority_a,
            ),
            JitCertCacheKey::new_for_verified_function(
                b"machine",
                b"verifier-b",
                b"fixup-a",
                b"config-a",
                &authority_a,
            ),
            JitCertCacheKey::new_for_verified_function(
                b"machine",
                b"verifier-a",
                b"fixup-b",
                b"config-a",
                &authority_a,
            ),
            JitCertCacheKey::new_for_verified_function(
                b"machine",
                b"verifier-a",
                b"fixup-a",
                b"config-b",
                &authority_a,
            ),
        ] {
            assert_ne!(baseline, distinct);
        }
        let different_authority = JitCertCacheKey::new_for_verified_function(
            b"machine",
            b"verifier-a",
            b"fixup-a",
            b"config-a",
            &authority_b,
        );
        assert_eq!(
            baseline.content_sha256, different_authority.content_sha256,
            "verifier authority belongs in the config half of the shared key"
        );
        assert_ne!(
            baseline.config_sha256, different_authority.config_sha256,
            "changing only verifier authority must make a cache miss"
        );

        let verifier_input_sha256 = Sha256::digest(b"verifier-a").into();
        let emitted_bytes_sha256 = Sha256::digest(b"machine").into();
        let digest_key = JitCertCacheKey::new_for_verified_function_digests(
            &emitted_bytes_sha256,
            &verifier_input_sha256,
            b"fixup-a",
            b"config-a",
            &authority_a,
        );
        assert_eq!(
            baseline,
            JitCertCacheKey::new_for_verified_function_digest(
                b"machine",
                &verifier_input_sha256,
                b"fixup-a",
                b"config-a",
                &authority_a,
            ),
            "the convenience and streaming constructors must share one key format"
        );
        assert_eq!(baseline, digest_key);

        // Spell the v3 framing independently so a future accidental double
        // hash, label swap, or omitted component in the digest constructor is
        // caught rather than compared only through delegating constructors.
        let mut expected_content = Sha256::new();
        expected_content.update(b"trust-cg.jit-cert.verified-function-content.v3\0");
        for (label, bytes) in [
            (
                b"emitted-bytes-sha256".as_slice(),
                emitted_bytes_sha256.as_slice(),
            ),
            (
                b"verifier-input-sha256".as_slice(),
                verifier_input_sha256.as_slice(),
            ),
            (b"symbolic-fixup-manifest".as_slice(), b"fixup-a".as_slice()),
        ] {
            expected_content.update((label.len() as u64).to_be_bytes());
            expected_content.update(label);
            expected_content.update((bytes.len() as u64).to_be_bytes());
            expected_content.update(bytes);
        }
        assert_eq!(
            digest_key.content_sha256,
            <[u8; 32]>::from(expected_content.finalize())
        );
        let mut expected_config = Sha256::new();
        expected_config.update(b"trust-cg.jit-cert.config-authority.v1\0");
        for (label, bytes) in [
            (b"compiler-config".as_slice(), b"config-a".as_slice()),
            (
                b"verification-authority-id".as_slice(),
                authority_a.as_slice(),
            ),
        ] {
            expected_config.update((label.len() as u64).to_be_bytes());
            expected_config.update(label);
            expected_config.update((bytes.len() as u64).to_be_bytes());
            expected_config.update(bytes);
        }
        assert_eq!(
            digest_key.config_sha256,
            <[u8; 32]>::from(expected_config.finalize())
        );
        assert_eq!(
            std::mem::size_of::<JitCertCacheKey>(),
            64,
            "authority binding must not enlarge each resident cache key"
        );
    }

    #[test]
    fn aarch64_verifier_identity_binds_name_and_implicit_registers() {
        static IMPLICIT_X0: [trust_cg_ir::PReg; 1] = [X0];

        let baseline = make_add_i32_func();
        assert_eq!(
            <[u8; 32]>::from(Sha256::digest(
                canonical_jit_function_bytes(&baseline).unwrap()
            )),
            aarch64_verifier_input_digest(&baseline).unwrap(),
            "streaming and materialized canonical identities must stay byte-equivalent"
        );
        let mut renamed = baseline.clone();
        renamed.name = "different-name".to_string();
        let mut implicit = baseline.clone();
        implicit.insts[0].implicit_defs = &IMPLICIT_X0;

        assert_ne!(
            canonical_jit_function_bytes(&baseline),
            canonical_jit_function_bytes(&renamed)
        );
        assert_ne!(
            canonical_jit_function_bytes(&baseline),
            canonical_jit_function_bytes(&implicit)
        );

        let mut first_nan = baseline.clone();
        first_nan.insts[0]
            .operands
            .push(trust_cg_ir::MachOperand::FImm(f64::from_bits(
                0x7ff8_0000_0000_0001,
            )));
        let mut second_nan = first_nan.clone();
        second_nan.insts[0].operands[0] =
            trust_cg_ir::MachOperand::FImm(f64::from_bits(0x7ff8_0000_0000_0002));
        assert_ne!(
            canonical_jit_function_bytes(&first_nan),
            canonical_jit_function_bytes(&second_nan)
        );
    }

    #[test]
    fn aarch64_fixup_manifest_binds_raw_name_and_exactness() {
        let manifest = |target| {
            let mut fixups = FixupList::new();
            fixups.push(Fixup {
                offset: 4,
                kind: AArch64RelocKind::Branch26,
                tls_model: None,
                target,
                addend: 0,
            });
            aarch64_symbolic_fixup_manifest(&fixups, 16)
        };

        assert_ne!(
            manifest(FixupTarget::NamedSymbol("foo".to_string())),
            manifest(FixupTarget::NamedSymbol("bar".to_string()))
        );
        assert_ne!(
            manifest(FixupTarget::NamedSymbol("foo".to_string())),
            manifest(FixupTarget::ExactNamedSymbol("foo".to_string()))
        );
    }

    #[test]
    fn x86_fixup_manifest_binds_calls_globals_and_binding_class() {
        use crate::x86_64::pipeline::{X86CallFixup, X86GlobalRefFixup, X86SymbolRefFixupKind};

        let call = |callee: &str, exact_module| {
            x86_symbolic_fixup_manifest(
                &[X86CallFixup {
                    offset: 3,
                    callee: callee.to_string(),
                    exact_module,
                }],
                &[],
                8,
            )
        };
        assert_ne!(call("foo", false), call("bar", false));
        assert_ne!(call("foo", false), call("foo", true));

        let global = |symbol: &str, kind| {
            x86_symbolic_fixup_manifest(
                &[],
                &[X86GlobalRefFixup {
                    offset: 7,
                    symbol: symbol.to_string(),
                    kind,
                }],
                8,
            )
        };
        assert_ne!(
            global("data", X86SymbolRefFixupKind::GlobalRef),
            global("other", X86SymbolRefFixupKind::GlobalRef)
        );
        assert_ne!(
            global("data", X86SymbolRefFixupKind::GlobalRef),
            global("data", X86SymbolRefFixupKind::ExternRefGot)
        );
        assert_ne!(
            global("data", X86SymbolRefFixupKind::GlobalRef),
            global("data", X86SymbolRefFixupKind::ExactFunctionAddr)
        );
        assert_ne!(
            global("data", X86SymbolRefFixupKind::ExactFunctionAddr),
            global("_data", X86SymbolRefFixupKind::ExactFunctionAddr)
        );
    }

    #[test]
    fn opcode_to_trust_ir_op_covers_basic_arith() {
        assert_eq!(opcode_to_trust_ir_op(AArch64Opcode::AddRR), "Iadd_I32");
        assert_eq!(opcode_to_trust_ir_op(AArch64Opcode::SubRR), "Isub_I32");
        assert_eq!(opcode_to_trust_ir_op(AArch64Opcode::MulRR), "Imul_I32");
        assert_eq!(opcode_to_trust_ir_op(AArch64Opcode::Neg), "Ineg_I32");
    }

    #[test]
    fn build_trust_ir_pairs_single_add() {
        let func = make_add_i32_func();
        let pairs = build_trust_ir_pairs(&func);
        assert_eq!(pairs.len(), 1);
        assert_eq!(pairs[0].trust_ir_op, "Iadd_I32");
        assert_eq!(pairs[0].mach_insts, 0u32..1);
    }

    #[test]
    fn lowering_certificate_waits_for_exact_trust_ir_provenance() {
        let func = make_add_ret_func();
        let report = run_on_proof_verifier_stack("trust-cg-jit-cert-ret-proof-verifier", || {
            trust_cg_verify::verify_function(&func)
        });
        let cert = JitCertificate::from_report(
            &func,
            &report,
            0u64..8u64,
            "aarch64",
            aarch64_verifier_input_digest(&func).unwrap(),
            Sha256::digest([0, 1, 2, 3, 4, 5, 6, 7]).into(),
        );

        assert!(
            !cert.is_verified(),
            "degenerate opcode bindings must not promote a function"
        );
        assert!(
            cert.trust_ir_pairs()
                .iter()
                .any(|pair| pair.trust_ir_op == "<opaque>"),
            "Ret is not covered by the Phase-1 trust_ir provenance table"
        );
        assert!(cert.lowering_certificate().is_none());
    }

    #[test]
    fn certificate_roundtrip_from_report() {
        let func = make_genuine_cert_func();
        let report = make_genuine_report();
        let cert = make_cert(&func, &report);

        assert_eq!(cert.function(), "add");
        assert_eq!(cert.code_range(), 0u64..4u64);
        assert!(cert.is_verified(), "MOVN W-form must verify exhaustively");
        assert!(
            cert.coverage_percent() >= 99.9,
            "coverage = {}",
            cert.coverage_percent()
        );
        let pairs = cert.trust_ir_pairs();
        assert_eq!(pairs.len(), 1);
        assert_eq!(pairs[0].trust_ir_op, "<opaque>");

        let chain = cert.chain();
        assert!(!chain.certificates.is_empty());
        assert!(chain.all_verified());
        assert!(
            cert.lowering_certificate().is_none(),
            "an opcode-name lookup must never be exported as exact TrustIR provenance"
        );
        assert_eq!(
            cert.normalized_machine_code_sha256(),
            crate::jit_diagnostics::sha256_hex(&[0, 1, 2, 3])
        );
    }

    #[test]
    fn core_certificate_seal_excludes_delivery_telemetry_and_coarse_pairs() {
        let func = make_genuine_cert_func();
        let report = make_genuine_report();
        let full = make_cert(&func, &report);
        let compact = JitCertificate::from_report_for_core_artifact(
            &func,
            &report,
            0..4,
            aarch64_verifier_input_digest(&func).unwrap(),
            Sha256::digest([0, 1, 2, 3]).into(),
        );
        assert!(compact.trust_ir_pairs().is_empty());
        assert_eq!(
            full.core_semantic_digest(),
            compact.core_semantic_digest(),
            "diagnostic opcode-name pairs are not proof authority"
        );

        let mut telemetry_changed = full.clone();
        telemetry_changed.code_range = 91..127;
        telemetry_changed.coverage_pct = 12.5;
        telemetry_changed.served_from_cache = true;
        telemetry_changed.chain.created_epoch_secs += 10_000;
        telemetry_changed.chain.certificates[0].timestamp_epoch_secs += 20_000;
        telemetry_changed.chain.certificates[0].duration_ms += 30_000;
        telemetry_changed.trust_ir_pairs[0].trust_ir_op = "presentation-only".to_owned();
        assert_eq!(
            full.core_semantic_digest(),
            telemetry_changed.core_semantic_digest(),
            "wall-clock, layout-delivery, and diagnostic metadata must not perturb semantic identity"
        );

        let mut replay_checksum_changed = full.clone();
        replay_checksum_changed.chain.certificates[0].formula_hash ^= 1;
        assert_eq!(
            full.core_semantic_digest(),
            replay_checksum_changed.core_semantic_digest(),
            "the redundant build-local replay checksum is not semantic identity"
        );
        assert!(!replay_checksum_changed.replay_check());

        let mut semantic_changed = full.clone();
        semantic_changed.chain.certificates[0]
            .obligation_name
            .push_str("-changed");
        semantic_changed.chain.certificates[0].formula_hash =
            expected_formula_hash(&semantic_changed.chain.certificates[0]);
        assert_ne!(
            full.core_semantic_digest(),
            semantic_changed.core_semantic_digest(),
            "the typed proof obligation identity must remain bound"
        );
    }

    #[test]
    fn certificate_accepts_only_closed_structural_unverified_rows() {
        let mut func = make_genuine_cert_func();
        func.insts.push(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.blocks[0].insts.push(InstId(1));

        let mut report = make_genuine_report();
        report
            .instructions
            .push(trust_cg_verify::function_verifier::InstructionReport {
                inst_index: 1,
                opcode: trust_cg_verify::function_verifier::InstructionOpcode::AArch64(
                    AArch64Opcode::Ret,
                ),
                result: InstructionVerificationResult::Unverified {
                    reason: "return control transfer is structurally covered".to_string(),
                },
            });
        assert!(
            make_cert(&func, &report).is_verified(),
            "the certificate gate must agree with the closed opcode inventory: RET is covered by the structural branch proof"
        );

        report.instructions[1].opcode =
            trust_cg_verify::function_verifier::InstructionOpcode::AArch64(AArch64Opcode::Csinv);
        assert!(
            !make_cert(&func, &report).is_verified(),
            "an ordinary uncovered opcode must remain fail-closed"
        );
    }

    #[test]
    fn unbound_condition_gap_cannot_borrow_a_synthetic_verified_anchor() {
        // Transport/accounting regression only. The helper's exhaustive anchor
        // is synthetic, not a discharged theorem or source-to-code proof. The
        // bytes below are identity inputs, not an executable native fixture.
        let anchor_func = make_genuine_cert_func();
        let anchor_report = make_genuine_report();
        assert!(make_cert(&anchor_func, &anchor_report).is_verified());

        let mut rejected = 0;
        use trust_cg_ir::aarch64_regs::{D0, D1, D2, S0, S1, S2, W0, W1, W2, X0};
        let select = |registers: [_; 3]| {
            registers
                .into_iter()
                .map(MachOperand::PReg)
                .chain([MachOperand::Imm(0)])
                .collect::<Vec<_>>()
        };
        for (opcode, valid_operands) in [
            (AArch64Opcode::Csel, select([W0, W1, W2])),
            (AArch64Opcode::Csinc, select([W0, W1, W2])),
            (AArch64Opcode::Csneg, select([W0, W1, W2])),
            (AArch64Opcode::FcselRR, select([S0, S1, S2])),
            (AArch64Opcode::FcselRR, select([D0, D1, D2])),
            (
                AArch64Opcode::Fcmp,
                vec![MachOperand::PReg(S0), MachOperand::PReg(S1)],
            ),
            (
                AArch64Opcode::Fcmp,
                vec![MachOperand::PReg(D0), MachOperand::PReg(D1)],
            ),
            (
                AArch64Opcode::CSet,
                vec![MachOperand::PReg(W0), MachOperand::Imm(0)],
            ),
            (
                AArch64Opcode::CSet,
                vec![MachOperand::PReg(X0), MachOperand::Imm(0)],
            ),
        ] {
            for operands in [valid_operands, Vec::new()] {
                let mut func = anchor_func.clone();
                func.insts.push(MachInst::new(opcode, operands));
                func.blocks[0].insts.push(InstId(1));
                let mut report = anchor_report.clone();
                report
                    .instructions
                    .push(trust_cg_verify::function_verifier::InstructionReport {
                        inst_index: 1,
                        opcode: trust_cg_verify::function_verifier::InstructionOpcode::AArch64(
                            opcode,
                        ),
                        result: InstructionVerificationResult::Unverified {
                            reason: "no independently validated condition/input binding"
                                .to_string(),
                        },
                    });
                assert_eq!(report.genuinely_verified_count(), 1);
                assert_eq!(report.degenerate_verified_count(), 0);
                assert_eq!(report.failed_count(), 0);
                assert!(!report.emitted_opcode_inventory().is_promotable());

                let input_digest = aarch64_verifier_input_digest(&func).unwrap();
                let bytes_digest: [u8; 32] = Sha256::digest([0u8; 8]).into();
                for certificate in [
                    JitCertificate::from_report(
                        &func,
                        &report,
                        0..8,
                        "aarch64",
                        input_digest,
                        bytes_digest,
                    ),
                    JitCertificate::from_report_for_core_artifact(
                        &func,
                        &report,
                        0..8,
                        input_digest,
                        bytes_digest,
                    ),
                ] {
                    assert!(
                        !certificate.is_verified(),
                        "{opcode:?} gap must block publication credit"
                    );
                    assert!(
                        certificate.replay_check(),
                        "internal chain integrity cannot replace coverage"
                    );
                    assert_eq!(certificate.chain().certificates.len(), 1);
                    assert!(certificate.lowering_certificate().is_none());
                    rejected += 1;
                }
            }
        }
        assert_eq!(rejected, 36);
    }

    #[test]
    fn function_precondition_failure_blocks_otherwise_verified_certificate() {
        use trust_cg_verify::FunctionVerificationPreconditionFailure;

        let func = make_genuine_cert_func();
        let good_report = make_genuine_report();
        assert!(make_cert(&func, &good_report).is_verified());
        for failure in [
            FunctionVerificationPreconditionFailure::MissingLirSource,
            FunctionVerificationPreconditionFailure::LirSourceNameMismatch {
                source_function: "wrong_source".to_string(),
            },
        ] {
            for retain_instruction_rows in [true, false] {
                let mut report = good_report.clone();
                report.precondition_failure = Some(failure.clone());
                if !retain_instruction_rows {
                    report.instructions.clear();
                }
                let cert = make_cert(&func, &report);
                assert!(!cert.is_verified());
                assert_eq!(cert.coverage_percent(), 0.0);
                assert!(cert.replay_check(), "integrity is not proof authority");
            }
        }
    }

    #[test]
    fn empty_and_all_skipped_reports_are_not_vacuously_verified() {
        let empty = MachFunction::new("empty".to_string(), Signature::new(vec![], vec![]));
        let empty_report =
            run_on_proof_verifier_stack("trust-cg-jit-cert-empty-proof-verifier", || {
                trust_cg_verify::verify_function(&empty)
            });
        assert!(!make_cert(&empty, &empty_report).is_verified());

        let mut nop = MachFunction::new("nop".to_string(), Signature::new(vec![], vec![]));
        nop.insts.push(MachInst::new(AArch64Opcode::Nop, vec![]));
        nop.blocks[0].insts.push(InstId(0));
        let nop_report =
            run_on_proof_verifier_stack("trust-cg-jit-cert-nop-proof-verifier", || {
                trust_cg_verify::verify_function(&nop)
            });
        assert!(!make_cert(&nop, &nop_report).is_verified());
    }

    #[test]
    fn global_cache_disable_is_resolved_per_request() {
        trust_cg_process_env::with_env_edits(|environment| {
            environment.remove("TCG_NO_JIT_CERT_CACHE");
            assert!(jit_cert_cache_allowed_for_request());

            trust_cg_process_env::with_env_overrides(&[("TCG_NO_JIT_CERT_CACHE", "1")], || {
                assert!(!jit_cert_cache_allowed_for_request());
                assert!(
                    JitCertCache::global().is_enabled(),
                    "a temporary first request must not freeze global storage disabled"
                );
            });

            assert!(jit_cert_cache_allowed_for_request());
            assert!(JitCertCache::global().is_enabled());
        });
    }

    #[test]
    fn certificate_cache_poison_never_serves_a_cached_verdict() {
        let cache = JitCertCache::new();
        let key = JitCertCacheKey::new(b"poisoned", b"config", &[0xa1; 32]);
        cache.store(
            key.clone(),
            CachedFunctionVerdict {
                x86_proof_certs: Vec::new(),
                aarch64_cert: None,
                #[cfg(feature = "verify")]
                verification_report: None,
                #[cfg(feature = "verify")]
                x86_envelope_report: None,
            },
        );
        assert!(cache.peek(&key).is_some());
        poison_certificate_cache(&cache);
        assert!(cache.peek(&key).is_none());
        assert!(cache.state.is_poisoned(), "poison must not be cleared");
    }

    #[test]
    fn certificate_cache_poison_declines_new_storage() {
        let cache = JitCertCache::new();
        poison_certificate_cache(&cache);
        let key = JitCertCacheKey::new(b"after-poison", b"config", &[0xa1; 32]);
        cache.store(
            key.clone(),
            CachedFunctionVerdict {
                x86_proof_certs: Vec::new(),
                aarch64_cert: None,
                #[cfg(feature = "verify")]
                verification_report: None,
                #[cfg(feature = "verify")]
                x86_envelope_report: None,
            },
        );
        assert!(cache.peek(&key).is_none());
        // Inspect damaged state only in the test: production must never recover
        // it into authority or mutate it after the poison boundary.
        let state = cache.state.lock().unwrap_err().into_inner();
        assert!(state.entries.is_empty());
        assert!(state.insertion_order.is_empty());
        assert_eq!(state.resident_payload_bytes, 0);
    }

    fn poison_certificate_cache(cache: &JitCertCache) {
        let result = std::panic::catch_unwind(|| {
            let _guard = cache.state.lock().unwrap();
            panic!("armed certificate-cache poison");
        });
        assert!(result.is_err());
        assert!(cache.state.is_poisoned());
    }

    #[test]
    fn certificate_cache_evicts_to_fixed_resident_bounds() {
        let cache = JitCertCache::with_limits(true, 2, usize::MAX);
        let authority = [0xa1; 32];
        let key = |name: &[u8]| JitCertCacheKey::new(name, b"config", &authority);
        let verdict = || CachedFunctionVerdict {
            x86_proof_certs: Vec::new(),
            aarch64_cert: None,
            #[cfg(feature = "verify")]
            verification_report: None,
            #[cfg(feature = "verify")]
            x86_envelope_report: None,
        };

        cache.store(key(b"first"), verdict());
        cache.store(key(b"second"), verdict());
        assert!(cache.peek(&key(b"first")).is_some());
        cache.store(key(b"third"), verdict());

        assert!(cache.peek(&key(b"first")).is_none());
        assert!(cache.peek(&key(b"second")).is_some());
        assert!(cache.peek(&key(b"third")).is_some());
        assert_eq!(cache.evictions(), 1);

        let rejects_oversize = JitCertCache::with_limits(true, 8, 1);
        rejects_oversize.store(key(b"oversize"), verdict());
        assert!(rejects_oversize.peek(&key(b"oversize")).is_none());
    }

    #[test]
    fn replay_check_passes_on_untampered_certificate() {
        let func = make_genuine_cert_func();
        let report = make_genuine_report();
        let cert = make_cert(&func, &report);
        assert!(cert.replay_check());
    }

    #[test]
    fn replay_check_detects_hash_tampering() {
        let func = make_genuine_cert_func();
        let report = make_genuine_report();
        let mut cert = make_cert(&func, &report);
        // Tamper with the first certificate's stored hash.
        assert!(!cert.chain.certificates.is_empty());
        cert.chain.certificates[0].formula_hash =
            cert.chain.certificates[0].formula_hash.wrapping_add(1);
        assert!(
            !cert.replay_check(),
            "replay_check must fail after hash tampering"
        );
    }

    #[test]
    fn to_json_emits_core_fields() {
        let func = make_genuine_cert_func();
        let report = make_genuine_report();
        let cert = make_cert(&func, &report);
        let json = cert.to_json();
        assert!(json.contains("\"function\": \"add\""), "json: {json}");
        assert!(json.contains("\"verified\": true"), "json: {json}");
        assert!(
            json.contains("\"normalized_machine_code_sha256\""),
            "json: {json}"
        );
        assert!(json.contains("\"trust_ir_pairs\""), "json: {json}");
        assert!(json.contains("<opaque>"), "json: {json}");
        assert!(json.contains("\"chain\""), "json: {json}");
    }
}
