// trust-cg-codegen — ENC-3: per-emission decode-check gate (arch-neutral core)
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//
// WHAT THIS IS (honest labeling)
// ------------------------------
// A per-compile, fail-closed REDUNDANCY gate that closes trusted-island-3 (the
// byte encoder `x86_64/encode.rs` is otherwise trusted, golden-tested only).
// After the emitter produces bytes for a function, this gate DECODES those bytes
// with an INDEPENDENT in-process decoder and structurally compares the decoded
// instruction (mnemonic + operand kinds/registers/widths + immediate/disp +
// fixup-hole placement) against the INTENDED post-RA instruction. Any mismatch,
// undecodable byte, or length drift = FAIL CLOSED (a would-be miscompile: the
// encoder emitted bytes that do not decode back to the instruction it was told
// to emit).
//
// This is NOT a proof. Two independent artifacts (emitter + decoder) must agree
// per compile — that catches encoder bugs (wrong ModR/M, wrong immediate) that
// ENC-2's offline llvm-objdump differential lane catches statically. It does NOT
// by itself prove the bytes against a formal model; that is ENC-4 (Lean
// linkage). Per the project soundness doctrine, decoder-agreement is REDUNDANCY,
// never counted in a "proven" numerator.
//
// ARCH-PARAMETRIC SEAM
// --------------------
// The [`DecodeCheck`] trait + [`run_decode_check`] driver + rollout mode +
// telemetry live here, arch-neutral. The x86 instantiation is
// `x86_64::decode_check`. ENC-5 (aarch64, AS lane) instantiates the SAME trait
// against the fixed-width A64 decoder in `trust-cg-lift`'s disasm surface — a
// clean seam, no plumbing change.
//
// ROLLOUT (soundness-doctrine gate rollout, §2.4)
// -----------------------------------------------
//   TCG_DECODE_CHECK = off | warn | enforce   (default: enforce — default-ON)
//   TCG_NO_DECODE_CHECK = 1                    triage opt-out (mirrors
//                                              TCG_NO_PROOF_CERTS; never weakens
//                                              a default silently)
//   TCG_TRACE_DECODE_CHECK = 1                 per-instruction trace + summary
//
// `warn` records telemetry and prints every disagreement LOUDLY (P0 evidence of
// a live encoder bug) without failing the compile — used to run the full
// differential corpus to 0 disagreements before flipping the default to
// `enforce`.

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};

/// Rollout mode for the decode-check gate.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DecodeCheckMode {
    /// Gate disabled (no recording, no check). Triage-only.
    Off,
    /// Decode and compare; a mismatch is logged loudly but does NOT fail the
    /// compile. Telemetry is still recorded. Used for the gate-rollout warm-up.
    Warn,
    /// Decode and compare; a mismatch FAILS the compile (default-ON).
    Enforce,
}

/// Resolve the gate mode from the environment (cached process-wide).
pub fn decode_check_mode() -> DecodeCheckMode {
    static MODE: OnceLock<DecodeCheckMode> = OnceLock::new();
    *MODE.get_or_init(|| {
        // Triage opt-out takes precedence, mirroring TCG_NO_PROOF_CERTS.
        if std::env::var_os("TCG_NO_DECODE_CHECK").is_some() {
            return DecodeCheckMode::Off;
        }
        match std::env::var("TCG_DECODE_CHECK").ok().as_deref() {
            Some("off") | Some("0") | Some("false") => DecodeCheckMode::Off,
            Some("warn") => DecodeCheckMode::Warn,
            Some("enforce") | Some("1") | Some("on") | Some("true") => DecodeCheckMode::Enforce,
            // DEFAULT-ON: any unset / unrecognized value enforces.
            _ => DecodeCheckMode::Enforce,
        }
    })
}

/// Whether per-instruction tracing is enabled (`TCG_TRACE_DECODE_CHECK=1`).
pub fn decode_check_trace_enabled() -> bool {
    static TRACE: OnceLock<bool> = OnceLock::new();
    *TRACE.get_or_init(|| std::env::var_os("TCG_TRACE_DECODE_CHECK").is_some())
}

// ---------------------------------------------------------------------------
// Telemetry (process-wide; used by the warn-only rollout + tests)
// ---------------------------------------------------------------------------

static N_CHECKED: AtomicU64 = AtomicU64::new(0);
static N_MATCHED: AtomicU64 = AtomicU64::new(0);
static N_MISMATCHED: AtomicU64 = AtomicU64::new(0);
static N_ALLOWLISTED: AtomicU64 = AtomicU64::new(0);

fn allowlist_reasons() -> &'static Mutex<BTreeMap<&'static str, u64>> {
    static R: OnceLock<Mutex<BTreeMap<&'static str, u64>>> = OnceLock::new();
    R.get_or_init(|| Mutex::new(BTreeMap::new()))
}

/// Snapshot of the decode-check telemetry counters.
#[derive(Clone, Debug, Default)]
pub struct DecodeCheckCounters {
    /// Instructions decoded and structurally compared.
    pub checked: u64,
    /// Comparisons that matched.
    pub matched: u64,
    /// Comparisons that disagreed (P0 in enforce mode).
    pub mismatched: u64,
    /// Instructions whose family is not covered by the decoder and was
    /// allowlisted-with-reason (logged, never silent).
    pub allowlisted: u64,
    /// Per-reason allowlist counts.
    pub allowlist_by_reason: BTreeMap<&'static str, u64>,
}

/// Read the current telemetry counters.
pub fn decode_check_counters() -> DecodeCheckCounters {
    DecodeCheckCounters {
        checked: N_CHECKED.load(Ordering::Relaxed),
        matched: N_MATCHED.load(Ordering::Relaxed),
        mismatched: N_MISMATCHED.load(Ordering::Relaxed),
        allowlisted: N_ALLOWLISTED.load(Ordering::Relaxed),
        allowlist_by_reason: allowlist_reasons().lock().unwrap().clone(),
    }
}

/// Reset all telemetry counters (test-only helper).
pub fn reset_decode_check_counters() {
    N_CHECKED.store(0, Ordering::Relaxed);
    N_MATCHED.store(0, Ordering::Relaxed);
    N_MISMATCHED.store(0, Ordering::Relaxed);
    N_ALLOWLISTED.store(0, Ordering::Relaxed);
    allowlist_reasons().lock().unwrap().clear();
}

// ---------------------------------------------------------------------------
// Fixup holes
// ---------------------------------------------------------------------------

/// The class of a relocation/patch hole in an emitted instruction. The gate
/// checks hole PLACEMENT (offset/width) only — the patched VALUES are covered
/// by the proven reloc formulas (macho_data_reloc_proofs.rs), so the pre-patch
/// sentinel value is not compared.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FixupHoleKind {
    /// Intra-function branch rel32 (patched by the branch-fixup pass).
    Branch,
    /// Direct CALL rel32 to a symbol.
    Call,
    /// GlobalRef RIP-relative disp32.
    GlobalRef,
    /// Extern-GOT RIP-relative disp32.
    ExternRefGot,
    /// Mach-O `@TLVP` thread-local descriptor RIP-relative disp32
    /// (`X86_64_RELOC_TLV`; same 4-byte hole shape as `ExternRefGot`).
    TlsTlv,
    /// Constant-pool RIP-relative disp32.
    ConstPool,
}

/// A relocation/patch hole: a byte range within the emitted instruction whose
/// value is a pre-patch sentinel and is filled later by a fixup pass.
#[derive(Clone, Copy, Debug)]
pub struct FixupHole {
    /// Offset of the hole from the start of the instruction.
    pub offset_in_inst: usize,
    /// Width of the hole in bytes.
    pub width: usize,
    /// The class of the hole.
    pub kind: FixupHoleKind,
}

// ---------------------------------------------------------------------------
// Trait + driver
// ---------------------------------------------------------------------------

/// A structural disagreement between the intended instruction and the decoded
/// bytes. In enforce mode this becomes a fail-closed pipeline error.
#[derive(Clone, Debug)]
pub struct DecodeCheckError {
    /// Human-readable description (intended vs decoded + raw bytes).
    pub message: String,
}

impl core::fmt::Display for DecodeCheckError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.message)
    }
}

/// Outcome of checking one emitted instruction against its intent.
#[derive(Clone, Debug)]
pub enum DecodeCheckOutcome {
    /// Decoded bytes structurally match the intended instruction.
    Match,
    /// The instruction's opcode family is not covered by this decoder. It is
    /// counted against the given static reason and NOT silently skipped.
    Allowlisted(&'static str),
    /// The decoded bytes disagree with the intended instruction.
    Mismatch(DecodeCheckError),
}

/// One recorded emitted instruction: its byte range, the intent it was emitted
/// from, and any fixup hole.
pub struct DecodeCheckItem<I> {
    /// Start offset of this instruction's bytes in the function code buffer.
    pub start: usize,
    /// End offset (exclusive).
    pub end: usize,
    /// The intended (post-RA) instruction the emitter was told to encode.
    pub intent: I,
    /// A relocation/patch hole in the instruction, if any.
    pub hole: Option<FixupHole>,
}

/// Arch-parametric per-emission decode-check. x86 implements it now; ENC-5
/// (aarch64) instantiates the same trait against a fixed-width A64 decoder.
pub trait DecodeCheck {
    /// The arch-specific intent descriptor (e.g. `X86IntentInst`).
    type Intent;

    /// Short arch tag for diagnostics (e.g. `"x86_64"`).
    fn arch(&self) -> &'static str;

    /// A short human-readable label for an intent (e.g. the opcode name),
    /// used in diagnostics.
    fn label(&self, intent: &Self::Intent) -> String;

    /// Decode `bytes` (exactly one instruction) with the independent decoder and
    /// structurally compare against `intent`. `hole` marks a pre-patch sentinel
    /// field whose VALUE must not be compared (its placement is checked).
    fn check_one(
        &self,
        intent: &Self::Intent,
        bytes: &[u8],
        hole: Option<&FixupHole>,
    ) -> DecodeCheckOutcome;
}

/// Run the decode-check over a whole function's recorded instruction stream.
///
/// Linear in the number of instructions (solver-free), so it is JIT-viable.
/// Returns `Err` only in [`DecodeCheckMode::Enforce`] on the first disagreement;
/// in [`DecodeCheckMode::Warn`] it logs every disagreement and returns `Ok`.
pub fn run_decode_check<C: DecodeCheck>(
    checker: &C,
    items: &[DecodeCheckItem<C::Intent>],
    code: &[u8],
    mode: DecodeCheckMode,
) -> Result<(), DecodeCheckError> {
    if mode == DecodeCheckMode::Off {
        return Ok(());
    }
    let trace = decode_check_trace_enabled();
    let arch = checker.arch();

    for item in items {
        // Length-drift / bounds guard: the recorded range must be inside the
        // buffer and non-empty. Anything else is itself a fail-closed defect.
        if item.start > item.end || item.end > code.len() {
            let err = DecodeCheckError {
                message: format!(
                    "[decode-check/{arch}] {label}: recorded byte range {start}..{end} is out of \
                     bounds for {len}-byte code buffer (length drift)",
                    label = checker.label(&item.intent),
                    start = item.start,
                    end = item.end,
                    len = code.len(),
                ),
            };
            N_MISMATCHED.fetch_add(1, Ordering::Relaxed);
            match mode {
                DecodeCheckMode::Warn => {
                    eprintln!("decode-check WARN: {}", err.message);
                    continue;
                }
                DecodeCheckMode::Enforce => return Err(err),
                DecodeCheckMode::Off => unreachable!(),
            }
        }

        let bytes = &code[item.start..item.end];
        match checker.check_one(&item.intent, bytes, item.hole.as_ref()) {
            DecodeCheckOutcome::Match => {
                N_CHECKED.fetch_add(1, Ordering::Relaxed);
                N_MATCHED.fetch_add(1, Ordering::Relaxed);
                if trace {
                    eprintln!(
                        "decode-check OK  [{arch}] {label} @{start} = {bytes:02x?}",
                        label = checker.label(&item.intent),
                        start = item.start,
                    );
                }
            }
            DecodeCheckOutcome::Allowlisted(reason) => {
                N_ALLOWLISTED.fetch_add(1, Ordering::Relaxed);
                *allowlist_reasons()
                    .lock()
                    .unwrap()
                    .entry(reason)
                    .or_insert(0) += 1;
                if trace {
                    eprintln!(
                        "decode-check SKIP [{arch}] {label} @{start} (allowlist: {reason})",
                        label = checker.label(&item.intent),
                        start = item.start,
                    );
                }
            }
            DecodeCheckOutcome::Mismatch(err) => {
                N_CHECKED.fetch_add(1, Ordering::Relaxed);
                N_MISMATCHED.fetch_add(1, Ordering::Relaxed);
                let full = DecodeCheckError {
                    message: format!(
                        "[decode-check/{arch}] {label} @byte {start}: {msg} | bytes={bytes:02x?}",
                        label = checker.label(&item.intent),
                        start = item.start,
                        msg = err.message,
                    ),
                };
                match mode {
                    DecodeCheckMode::Warn => {
                        // P0 evidence in warn-only: a live encoder disagreement.
                        eprintln!("decode-check WARN (P0 candidate): {}", full.message);
                    }
                    DecodeCheckMode::Enforce => return Err(full),
                    DecodeCheckMode::Off => unreachable!(),
                }
            }
        }
    }

    if trace {
        let c = decode_check_counters();
        eprintln!(
            "decode-check summary [{arch}]: checked={} matched={} mismatched={} allowlisted={} \
             ({} reasons)",
            c.checked,
            c.matched,
            c.mismatched,
            c.allowlisted,
            c.allowlist_by_reason.len(),
        );
    }

    Ok(())
}
