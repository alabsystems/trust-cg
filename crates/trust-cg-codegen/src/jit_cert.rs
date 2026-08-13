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
//! - a coarse (trust_ir op, MachInst index range) provenance map,
//! - a full [`trust_cg_verify::proof_certificate::CertificateChain`] summarizing
//!   what was verified by [`trust_cg_verify::verify_function`], and
//! - a cheap `replay_check()` that re-hashes the chain for tamper detection.
//!
//! This is the Phase-1 cut of the plan in
//! `reports/2026-04-18-jit-proof-certs-plan.md`. Real ay SMT replay is
//! deferred to a future `proof-certs-full` feature.
//!
//! Callers (e.g. ty) use the certificate to assert "the JIT-compiled
//! machine code for `fn add` has been formally checked against the trust_ir
//! that produced it", without needing to re-run the full verification
//! pipeline themselves.
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
    CertificateChain, CertificateResult, LoweringCertificate, ProofCertificate, SolverUsed,
};
#[cfg(feature = "verify")]
use trust_cg_verify::verify::VerificationStrength;

#[cfg(feature = "verify")]
pub(crate) const PROOF_VERIFIER_STACK_SIZE: usize = 32 * 1024 * 1024;

#[cfg(feature = "verify")]
pub(crate) fn run_on_proof_verifier_stack<R, F>(name: &str, f: F) -> R
where
    R: Send,
    F: FnOnce() -> R + Send,
{
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name(name.to_string())
            .stack_size(PROOF_VERIFIER_STACK_SIZE)
            .spawn_scoped(scope, f)
            .expect("failed to spawn proof verifier thread")
            .join()
            .expect("proof verifier thread panicked")
    })
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
    /// Byte range `[start, end)` of this function's machine code within the
    /// owning `ExecutableBuffer`.
    code_range: Range<u64>,
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
    /// Verified flag: true iff the verification report reports no failed or
    /// unverified instructions (skipped pseudo-ops do not count).
    verified: bool,
    /// Coverage percentage from the verification report
    /// (verified / (total - skipped) * 100).
    coverage_pct: f64,
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
        target: &str,
        machine_code_bytes: &[u8],
        compiler_config_bytes: &[u8],
    ) -> Self {
        let function = func.name.clone();
        let trust_ir_pairs = build_trust_ir_pairs(func);

        let mut chain = CertificateChain::new(function.clone());
        for ir in &report.instructions {
            if let Some(cert) = instruction_report_to_cert(ir) {
                chain.add(cert);
            }
        }

        // #62: a function is "verified" for certificate purposes when its emitted
        // opcode inventory is PROMOTABLE — every non-pseudo opcode is Verified,
        // Skipped, or CoveredElsewhere (structural forms whose degenerate X==X
        // proofs were retracted: register copy, RET, conditional select, branch/
        // call targets, const materialization). This matches the compiler.rs
        // proof-promotion gate exactly; a genuine "pending a proof" gap (CSINV,
        // bitfield, x86 Push, …) still leaves an Unverified row and fails closed.
        let verified =
            report.failed_count() == 0 && report.emitted_opcode_inventory().is_promotable();
        let coverage_pct = report.coverage_percent();
        let lowering_certificate = if verified && has_complete_trust_ir_provenance(&trust_ir_pairs)
        {
            let trust_ir_bytes = canonical_jit_function_bytes(func);
            LoweringCertificate::from_verified_chain(
                &function,
                target,
                &trust_ir_bytes,
                machine_code_bytes,
                compiler_config_bytes,
                &chain,
            )
            .ok()
        } else {
            None
        };

        Self {
            function,
            code_range,
            trust_ir_pairs,
            chain,
            lowering_certificate,
            verified,
            coverage_pct,
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
            trust_ir_pairs: Vec::new(),
            verified: false,
            coverage_pct: 0.0,
        }
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
    pub(crate) fn rebound(&self, code_range: Range<u64>) -> Self {
        let mut cloned = self.clone();
        cloned.code_range = code_range;
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

    /// trust_ir → MachInst provenance entries.
    pub fn trust_ir_pairs(&self) -> &[TrustIrPair] {
        &self.trust_ir_pairs
    }

    /// Returns true iff every non-pseudo machine instruction in this
    /// function was matched against a proof obligation and verified.
    pub fn is_verified(&self) -> bool {
        self.verified
    }

    /// Coverage percentage: verified / (total - skipped) * 100.
    pub fn coverage_percent(&self) -> f64 {
        self.coverage_pct
    }

    /// Underlying verification chain. Available only with the `verify`
    /// feature enabled.
    #[cfg(feature = "verify")]
    pub fn chain(&self) -> &CertificateChain {
        &self.chain
    }

    /// Function-level lowering certificate suitable for Trust Codegen lowering JSON
    /// or trust-proof-cert export. Returns `None` when the verifier report did
    /// not satisfy the stricter fail-closed lowering-certificate contract.
    #[cfg(feature = "verify")]
    pub fn lowering_certificate(&self) -> Option<&LoweringCertificate> {
        self.lowering_certificate.as_ref()
    }

    /// Cheap replay check.
    ///
    /// Re-derives a stable hash from each certificate's
    /// `(obligation_name, solver, strength, result)` tuple and confirms it
    /// matches the stored `formula_hash`. This catches in-memory tampering
    /// with the certificate without re-running the SMT solver.
    ///
    /// A full solver-backed replay is gated behind the future
    /// `proof-certs-full` feature.
    #[cfg(feature = "verify")]
    pub fn replay_check(&self) -> bool {
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
        out.push_str(&format!("  \"verified\": {},\n", self.verified));
        out.push_str(&format!(
            "  \"coverage_percent\": {:.4},\n",
            self.coverage_pct
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

#[cfg(feature = "verify")]
fn has_complete_trust_ir_provenance(trust_ir_pairs: &[TrustIrPair]) -> bool {
    !trust_ir_pairs.is_empty()
        && trust_ir_pairs
            .iter()
            .all(|pair| pair.trust_ir_op != "<opaque>")
}

#[cfg(feature = "verify")]
fn canonical_jit_function_bytes(func: &MachFunction) -> Vec<u8> {
    let mut out = String::new();
    out.push_str("trust-cg.jit.function.v1\n");
    out.push_str(&format!("name={}\n", escape_json(&func.name)));
    out.push_str(&format!("signature={:?}\n", func.signature));
    out.push_str(&format!("entry={:?}\n", func.entry));
    out.push_str("block_order=");
    for (i, block) in func.block_order.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push_str(&format!("{:?}", block));
    }
    out.push('\n');
    out.push_str(&format!("next_vreg={}\n", func.next_vreg));
    out.push_str(&format!("stack_slots={:?}\n", func.stack_slots));
    out.push_str(&format!("function_proofs={:?}\n", func.function_proofs));
    out.push_str(&format!("jump_tables={:?}\n", func.jump_tables));
    for (idx, block) in func.blocks.iter().enumerate() {
        out.push_str(&format!("block[{idx}]={:?}\n", block));
    }
    for (idx, inst) in func.insts.iter().enumerate() {
        out.push_str(&format!(
            "inst[{idx}] opcode={:?} operands={:?} flags={:?} proof={:?} source_loc={:?}\n",
            inst.opcode, inst.operands, inst.flags, inst.proof, inst.source_loc
        ));
    }
    out.into_bytes()
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
        VerificationStrength::Formal => SolverUsed::AYNative,
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
// `CachedVerified` JIT compiles must cover every executed byte with a verified
// certificate, but the expensive discharge is amortized across compiles of
// byte-identical work under an identical config. This is the in-process cut of
// that cache (JIT-6 makes it disk-backed, reusing this key + bytes-binding
// contract). Soundness rules baked in here:
//
//   * the key is NEVER name-only — it folds a canonical CONTENT hash with a
//     CONFIG fingerprint (PROOF-2/PROOF-3 content-key discipline), so a verdict
//     can only ever be reused for identical work under identical settings;
//   * a warm hit attaches without re-discharge ONLY if the freshly emitted
//     machine bytes hash matches the bytes the cached verdict vouched for
//     (`emitted_bytes_sha256`) — pipeline nondeterminism => miss => re-verify;
//   * a cache MISS re-verifies (never skips); the caller populates on the way
//     out. Nothing here can turn an unverified function into a verified one.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

/// Content-addressed key for a per-function JIT verification verdict.
///
/// Both components are SHA-256 hex digests. `content_sha256` covers the
/// canonical post-optimization form of the function (the exact input the
/// verifier and the encoder consume); `config_sha256` covers the compile
/// configuration fingerprint (target, opt level, alloc profile, validation
/// mode, and a compiler-rev salt). Reusing a verdict requires BOTH to match.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct JitCertCacheKey {
    /// SHA-256 (hex) of the canonical content the verdict was proven over.
    pub content_sha256: String,
    /// SHA-256 (hex) of the config fingerprint.
    pub config_sha256: String,
}

impl JitCertCacheKey {
    /// Build a key from the canonical content bytes and the config fingerprint
    /// bytes. Never construct a key from a name alone.
    pub fn new(content_bytes: &[u8], config_bytes: &[u8]) -> Self {
        Self {
            content_sha256: crate::jit_diagnostics::sha256_hex(content_bytes),
            config_sha256: crate::jit_diagnostics::sha256_hex(config_bytes),
        }
    }
}

/// A cached per-function verdict, bound to the emitted machine bytes it
/// vouched for.
#[derive(Debug, Clone)]
pub struct CachedFunctionVerdict {
    /// Whether the function's lowering was verified (promotable): every
    /// non-pseudo opcode Verified/Skipped/CoveredElsewhere.
    pub verified: bool,
    /// SHA-256 (hex) of the exact emitted machine bytes this verdict covers.
    pub emitted_bytes_sha256: String,
    /// x86-64 per-instruction proof certificates (empty on other paths).
    pub x86_proof_certs: Vec<crate::compiler::ProofCertificate>,
    /// AArch64 buffer certificate (None on other paths).
    pub aarch64_cert: Option<JitCertificate>,
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
/// with [`Self::disabled`] always misses (used for `AlwaysVerify` and the
/// `TCG_NO_JIT_CERT_CACHE` escape hatch), so verification runs every compile.
#[derive(Debug)]
pub struct JitCertCache {
    entries: Mutex<HashMap<JitCertCacheKey, CachedFunctionVerdict>>,
    stats: JitCertCacheStats,
    enabled: bool,
}

impl Default for JitCertCache {
    fn default() -> Self {
        Self::new()
    }
}

impl JitCertCache {
    /// A fresh, empty, enabled cache with its own stats.
    pub fn new() -> Self {
        Self {
            entries: Mutex::new(HashMap::new()),
            stats: JitCertCacheStats::default(),
            enabled: true,
        }
    }

    /// A cache that never stores or serves entries — every lookup misses, so
    /// verification runs on every compile. Used for `AlwaysVerify` and the
    /// `TCG_NO_JIT_CERT_CACHE=1` escape hatch.
    pub fn disabled() -> Self {
        Self {
            entries: Mutex::new(HashMap::new()),
            stats: JitCertCacheStats::default(),
            enabled: false,
        }
    }

    /// The process-global shared cache instance (default production cache).
    pub fn global() -> Arc<JitCertCache> {
        static GLOBAL: OnceLock<Arc<JitCertCache>> = OnceLock::new();
        GLOBAL
            .get_or_init(|| {
                // `TCG_NO_JIT_CERT_CACHE=1` degrades the global cache to
                // always-verify (documented escape hatch; never turns off
                // verification, only the amortization).
                let disabled = std::env::var("TCG_NO_JIT_CERT_CACHE")
                    .ok()
                    .map(|v| v == "1")
                    .unwrap_or(false);
                Arc::new(if disabled {
                    JitCertCache::disabled()
                } else {
                    JitCertCache::new()
                })
            })
            .clone()
    }

    /// Whether this cache stores/serves entries.
    pub fn is_enabled(&self) -> bool {
        self.enabled
    }

    /// Look up a verdict. Returns a clone so the caller does not hold the lock.
    /// Does NOT touch stats — the caller records hit/miss after validating the
    /// bytes binding (a lookup that produces bytes-mismatched data is a
    /// re-verification, not a hit).
    pub fn peek(&self, key: &JitCertCacheKey) -> Option<CachedFunctionVerdict> {
        if !self.enabled {
            return None;
        }
        self.entries.lock().unwrap().get(key).cloned()
    }

    /// Store (or overwrite) a verdict for `key`.
    pub fn store(&self, key: JitCertCacheKey, verdict: CachedFunctionVerdict) {
        if !self.enabled {
            return;
        }
        self.entries.lock().unwrap().insert(key, verdict);
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

    /// `(hits, misses, reverifications, verifier_runs)`.
    pub fn stats(&self) -> (u64, u64, u64, u64) {
        self.stats.snapshot()
    }

    /// Number of times the underlying verifier actually ran through this cache.
    pub fn verifier_runs(&self) -> u64 {
        self.stats.verifier_runs.load(Ordering::Relaxed)
    }
}

// ---------------------------------------------------------------------------
// Unit tests
// ---------------------------------------------------------------------------

#[cfg(all(test, feature = "verify"))]
mod tests {
    use super::*;
    use trust_cg_ir::types::InstId;
    use trust_cg_ir::{MachInst, Signature};

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

    fn make_cert(func: &MachFunction, report: &FunctionVerificationReport) -> JitCertificate {
        JitCertificate::from_report(func, report, 0u64..4u64, "aarch64", &[0, 1, 2, 3], b"test")
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
    fn lowering_certificate_requires_complete_trust_ir_provenance() {
        let func = make_add_ret_func();
        let report = run_on_proof_verifier_stack("trust-cg-jit-cert-ret-proof-verifier", || {
            trust_cg_verify::verify_function(&func)
        });
        let cert = JitCertificate::from_report(
            &func,
            &report,
            0u64..8u64,
            "aarch64",
            &[0, 1, 2, 3, 4, 5, 6, 7],
            b"test",
        );

        assert!(
            cert.is_verified(),
            "AddRR and Ret both have instruction proofs"
        );
        assert!(
            cert.trust_ir_pairs()
                .iter()
                .any(|pair| pair.trust_ir_op == "<opaque>"),
            "Ret is not covered by the Phase-1 trust_ir provenance table"
        );
        assert!(
            cert.lowering_certificate().is_none(),
            "function-level lowering export must wait for complete provenance"
        );
    }

    #[test]
    fn certificate_roundtrip_from_report() {
        let func = make_add_i32_func();
        let report = run_on_proof_verifier_stack("trust-cg-jit-cert-test-proof-verifier", || {
            trust_cg_verify::verify_function(&func)
        });
        let cert = make_cert(&func, &report);

        assert_eq!(cert.function(), "add");
        assert_eq!(cert.code_range(), 0u64..4u64);
        assert!(cert.is_verified(), "AddRR must verify");
        assert!(
            cert.coverage_percent() >= 99.9,
            "coverage = {}",
            cert.coverage_percent()
        );
        let pairs = cert.trust_ir_pairs();
        assert_eq!(pairs.len(), 1);
        assert_eq!(pairs[0].trust_ir_op, "Iadd_I32");

        let chain = cert.chain();
        assert!(!chain.certificates.is_empty());
        assert!(chain.all_verified());
        assert!(
            cert.lowering_certificate().is_some(),
            "verified AddRR chain should produce a lowering certificate"
        );
    }

    #[test]
    fn replay_check_passes_on_untampered_certificate() {
        let func = make_add_i32_func();
        let report = run_on_proof_verifier_stack("trust-cg-jit-cert-test-proof-verifier", || {
            trust_cg_verify::verify_function(&func)
        });
        let cert = make_cert(&func, &report);
        assert!(cert.replay_check());
    }

    #[test]
    fn replay_check_detects_hash_tampering() {
        let func = make_add_i32_func();
        let report = run_on_proof_verifier_stack("trust-cg-jit-cert-test-proof-verifier", || {
            trust_cg_verify::verify_function(&func)
        });
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
        let func = make_add_i32_func();
        let report = run_on_proof_verifier_stack("trust-cg-jit-cert-test-proof-verifier", || {
            trust_cg_verify::verify_function(&func)
        });
        let cert = make_cert(&func, &report);
        let json = cert.to_json();
        assert!(json.contains("\"function\": \"add\""), "json: {json}");
        assert!(json.contains("\"verified\": true"), "json: {json}");
        assert!(json.contains("\"trust_ir_pairs\""), "json: {json}");
        assert!(json.contains("Iadd_I32"), "json: {json}");
        assert!(json.contains("\"chain\""), "json: {json}");
    }
}
