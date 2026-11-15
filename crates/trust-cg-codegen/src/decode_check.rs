// trust-cg-codegen — ENC-3: per-emission decode-check gate (arch-neutral core)
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//
// WHAT THIS IS (honest labeling)
// ------------------------------
// A per-compile REDUNDANCY gate for recorded instruction extents. In enforce
// mode, invalid extents and decoder disagreements fail compilation. Supported
// families use an independent in-process decoder to compare the decoded
// instruction (mnemonic + operand kinds/registers/widths + immediate/disp +
// fixup-hole placement) against the intended post-RA instruction. Unsupported
// families can return an explicit Allowlisted reason; this gate does not claim
// complete decoder coverage or check bytes absent from its recorded items.
//
// This is NOT a proof. Two independent artifacts (emitter + decoder) must agree
// per compile — that catches encoder bugs (wrong ModR/M, wrong immediate) that
// ENC-2's offline llvm-objdump differential lane catches statically. It does NOT
// by itself prove the bytes against a formal model. Formal evidence admission
// is separate. Per the project soundness doctrine, agreement is REDUNDANCY,
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

/// What a per-compile decode check establishes about the bytes of the compile
/// that issues a certificate: ENC-3 (`x86_64::decode_check`) on x86-64, ENC-5
/// (`aarch64::decode_check`) on AArch64.
///
/// A `covered_elsewhere` certificate whose credit cites a decode check as the
/// evidence for its emitted bytes (the x86-64 `MOV r, imm`, whose ENC-3 arm
/// runs `trust_cg_verify::x86_encoding_proofs::mov_imm_check_for_preg`, and
/// AArch64 `AlignNop`) is `verified: true` only under [`Self::Enforced`]. Under
/// any other backing the check did not gate the compile, so the certificate
/// would claim evidence that was not gathered; it is withheld instead
/// (`compiler::unverified_instruction_certificate`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DecodeCheckBacking {
    /// The check runs in [`DecodeCheckMode::Enforce`] over every instruction
    /// the compile records for it. A refutation fails the compile before any
    /// certificate is returned, so the bytes of a compile that returns one
    /// passed it.
    Enforced,
    /// The check ran in [`DecodeCheckMode::Warn`]: a refutation is logged and
    /// the compile continues, so a returned certificate's bytes are not known
    /// to have passed it.
    Warned,
    /// The check did not run ([`DecodeCheckMode::Off`]).
    NotRun,
    /// No decode check covers these bytes: the certificates were converted
    /// from a verifier report outside any compile's encode (a diagnostic or a
    /// test fixture).
    NoEncode,
}

impl DecodeCheckBacking {
    /// The backing a compile whose encode resolved `mode` gives its bytes.
    pub const fn from_mode(mode: DecodeCheckMode) -> Self {
        match mode {
            DecodeCheckMode::Enforce => Self::Enforced,
            DecodeCheckMode::Warn => Self::Warned,
            DecodeCheckMode::Off => Self::NotRun,
        }
    }

    /// Whether a refutation by the check fails the compile.
    pub const fn gates_the_compile(self) -> bool {
        matches!(self, Self::Enforced)
    }

    /// Why a certificate citing `check` (for example `"ENC-3"`) is withheld
    /// under this backing; `None` under [`Self::Enforced`].
    pub fn withheld_reason(self, check: &str) -> Option<String> {
        match self {
            Self::Enforced => None,
            Self::Warned => Some(format!(
                "{check} ran in warn mode: a refutation is logged and the compile continues, so \
                 these bytes are not known to have passed it"
            )),
            Self::NotRun => Some(format!(
                "{check} was off for this compile, so these bytes were not checked"
            )),
            Self::NoEncode => Some(format!(
                "no {check} run covers these bytes: the certificate was converted from a \
                 verifier report outside a compile's encode"
            )),
        }
    }
}

/// Test-only fault seam: while this key is set (through
/// `trust_cg_process_env`, so a compile's worker threads see it under the
/// environment snapshot they already run in) to an intent label, every
/// instruction with that label is treated as a decoder disagreement. It lets
/// a test force a decode check to fail inside a real compile and observe what
/// the compile and its certificates do. It exists only in this crate's own
/// unit-test build.
#[cfg(test)]
pub(crate) const FORCE_MISMATCH_TEST_ENV: &str = "TCG_TEST_DECODE_CHECK_FORCE_MISMATCH";

/// Test-only record of what one probe function went through in a real compile
/// route: the mode each encode of it ran its decode check in (ENC-3 in the x86
/// encode funnel, ENC-5 in the AArch64 encode) and the backing its certificate
/// lane handed the certificate builder, with the certificates that came out.
/// It lets a unit test check each lane's wiring (X-OPCODES-P13) through the
/// compile itself instead of copying it. Only functions whose name contains
/// [`lane_probe::PROBE`] are recorded, so concurrently running unit tests
/// neither see nor grow the record. It exists only in this crate's own
/// unit-test build.
#[cfg(all(test, feature = "verify"))]
pub(crate) mod lane_probe {
    use super::{DecodeCheckBacking, DecodeCheckMode};
    use std::sync::{Mutex, PoisonError};

    /// The function-name marker of a probe function.
    pub(crate) const PROBE: &str = "decode_backing_probe_";

    /// One recorded step of a probe function's compile.
    #[derive(Debug, Clone)]
    pub(crate) enum Event {
        /// An encode of the function resolved `mode` for `check`.
        Encode {
            check: &'static str,
            mode: DecodeCheckMode,
        },
        /// The certificate builder converted the function's verifier report
        /// under `backing` and returned `certs`.
        Certificates {
            backing: DecodeCheckBacking,
            certs: Vec<crate::compiler::ProofCertificate>,
        },
    }

    static EVENTS: Mutex<Vec<(String, Event)>> = Mutex::new(Vec::new());

    /// Record `event` for `function` when it is a probe function. A check
    /// encode under [`super::without_telemetry`] (the composed transition
    /// record's own) is not a lane's encode and records nothing.
    pub(crate) fn record(function: &str, event: impl FnOnce() -> Event) {
        if function.contains(PROBE) && !super::telemetry_suppressed() {
            EVENTS
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push((function.to_owned(), event()));
        }
    }

    /// Remove and return, in order, the events of every recorded function
    /// whose name contains `function`.
    pub(crate) fn take(function: &str) -> Vec<Event> {
        let mut events = EVENTS.lock().unwrap_or_else(PoisonError::into_inner);
        let (taken, kept): (Vec<_>, Vec<_>) = std::mem::take(&mut *events)
            .into_iter()
            .partition(|(name, _)| name.contains(function));
        *events = kept;
        taken.into_iter().map(|(_, event)| event).collect()
    }
}

/// Resolve the gate mode for the current compile request.
pub fn decode_check_mode() -> DecodeCheckMode {
    // Triage opt-out takes precedence, mirroring TCG_NO_PROOF_CERTS.
    if trust_cg_process_env::var_os("TCG_NO_DECODE_CHECK").is_some() {
        return DecodeCheckMode::Off;
    }
    match trust_cg_process_env::var("TCG_DECODE_CHECK")
        .ok()
        .as_deref()
    {
        Some("off") | Some("0") | Some("false") => DecodeCheckMode::Off,
        Some("warn") => DecodeCheckMode::Warn,
        Some("enforce") | Some("1") | Some("on") | Some("true") => DecodeCheckMode::Enforce,
        // DEFAULT-ON: any unset / unrecognized value enforces.
        _ => DecodeCheckMode::Enforce,
    }
}

// ---------------------------------------------------------------------------
// Telemetry (process-wide; used by the warn-only rollout + tests)
// ---------------------------------------------------------------------------

static N_CHECKED: AtomicU64 = AtomicU64::new(0);
static N_MATCHED: AtomicU64 = AtomicU64::new(0);
static N_MISMATCHED: AtomicU64 = AtomicU64::new(0);
static N_ALLOWLISTED: AtomicU64 = AtomicU64::new(0);

std::thread_local! {
    /// Set on this thread while [`without_telemetry`] runs its encode.
    static TELEMETRY_SUPPRESSED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Run `encode` with this thread's process-wide ENC-5 telemetry suppressed:
/// the counters below, the per-reason allowlist counts, the decode census
/// (`TCG_DECODE_CHECK_CENSUS_DIR`) and the unit tests' lane probes. The
/// composed transition record's own proof-grade check encode during
/// preparation ([`crate::composed_transition`]) runs under it: it re-checks
/// the bytes the route will publish, so counting it would describe each
/// published function twice. Verdicts and bytes are unchanged; only the
/// diagnostics are.
pub(crate) fn without_telemetry<T>(encode: impl FnOnce() -> T) -> T {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            let previous = self.0;
            TELEMETRY_SUPPRESSED.with(|flag| flag.set(previous));
        }
    }
    let _restore = Restore(TELEMETRY_SUPPRESSED.with(|flag| flag.replace(true)));
    encode()
}

/// Whether [`without_telemetry`] is running on this thread.
pub(crate) fn telemetry_suppressed() -> bool {
    TELEMETRY_SUPPRESSED.with(std::cell::Cell::get)
}

#[derive(Default)]
struct AllowlistReasonCounts {
    counts: Mutex<BTreeMap<&'static str, u64>>,
}

impl AllowlistReasonCounts {
    fn lock(&self) -> std::sync::MutexGuard<'_, BTreeMap<&'static str, u64>> {
        // These counts are diagnostic only, never decode/proof authority. Keep
        // best-effort observations after an interrupted update and preserve the
        // poison bit so every subsequent snapshot reports the lost integrity.
        self.counts
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    fn snapshot(&self) -> (BTreeMap<&'static str, u64>, bool) {
        let counts = self.lock();
        (counts.clone(), self.counts.is_poisoned())
    }

    fn record(&self, reason: &'static str) {
        let mut counts = self.lock();
        let count = counts.entry(reason).or_insert(0);
        *count = count.saturating_add(1);
    }

    fn reset(&self) {
        self.lock().clear();
    }
}

fn allowlist_reasons() -> &'static AllowlistReasonCounts {
    static R: OnceLock<AllowlistReasonCounts> = OnceLock::new();
    R.get_or_init(AllowlistReasonCounts::default)
}

fn increment_counter(counter: &AtomicU64) {
    if telemetry_suppressed() {
        return;
    }
    let mut previous = counter.load(Ordering::Relaxed);
    loop {
        let next = previous.saturating_add(1);
        match counter.compare_exchange_weak(previous, next, Ordering::Relaxed, Ordering::Relaxed) {
            Ok(_) => return,
            Err(current) => previous = current,
        }
    }
}

/// Snapshot of the decode-check telemetry counters.
/// Counts saturate at u64::MAX. Process-wide updates and resets are concurrent;
/// the individual fields are observations, not an atomic per-compile rollup.
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
    /// An earlier panic may have interrupted the best-effort reason counts.
    pub allowlist_counts_poisoned: bool,
}

/// Read the current telemetry counters.
pub fn decode_check_counters() -> DecodeCheckCounters {
    let (allowlist_by_reason, allowlist_counts_poisoned) = allowlist_reasons().snapshot();
    DecodeCheckCounters {
        checked: N_CHECKED.load(Ordering::Relaxed),
        matched: N_MATCHED.load(Ordering::Relaxed),
        mismatched: N_MISMATCHED.load(Ordering::Relaxed),
        allowlisted: N_ALLOWLISTED.load(Ordering::Relaxed),
        allowlist_by_reason,
        allowlist_counts_poisoned,
    }
}

/// Reset all telemetry counters (test helper). A previous poison health flag is
/// deliberately retained: clearing counts cannot repair an interrupted update.
pub fn reset_decode_check_counters() {
    N_CHECKED.store(0, Ordering::Relaxed);
    N_MATCHED.store(0, Ordering::Relaxed);
    N_MISMATCHED.store(0, Ordering::Relaxed);
    N_ALLOWLISTED.store(0, Ordering::Relaxed);
    allowlist_reasons().reset();
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

/// One recorded emitted instruction: its nonempty byte range, the intent it was emitted
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

/// What the driver does with an [`DecodeCheckOutcome::Allowlisted`] word,
/// one the independent decoder did not decode.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AllowlistPolicy {
    /// Count it against its reason and continue (compatibility routes).
    Count,
    /// Also count it, then treat it like a disagreement: an error in
    /// [`DecodeCheckMode::Enforce`] naming the instruction, the reason and
    /// [`UNDECODED_EMISSION_REFUSAL_TAG`]; a loud warning in
    /// [`DecodeCheckMode::Warn`]. Proof-grade routes select it, so an emitted
    /// form the decoder does not cover is refused instead of counted.
    Refuse,
}

/// The tag every [`AllowlistPolicy::Refuse`] refusal message starts with.
pub const UNDECODED_EMISSION_REFUSAL_TAG: &str = "[TCG-DECODE-CHECK-UNDECODED]";

/// Run the decode-check over a whole function's recorded instruction stream.
///
/// Linear in the number of instructions (solver-free), so it is JIT-viable.
/// Returns `Err` only in [`DecodeCheckMode::Enforce`] on the first disagreement;
/// in [`DecodeCheckMode::Warn`] it logs every disagreement and returns `Ok`.
/// Allowlisted words are counted ([`AllowlistPolicy::Count`]).
pub fn run_decode_check<C: DecodeCheck>(
    checker: &C,
    items: &[DecodeCheckItem<C::Intent>],
    code: &[u8],
    mode: DecodeCheckMode,
) -> Result<(), DecodeCheckError> {
    run_decode_check_with_allowlist_policy(checker, items, code, mode, AllowlistPolicy::Count)
}

/// [`run_decode_check`] with an explicit [`AllowlistPolicy`].
pub fn run_decode_check_with_allowlist_policy<C: DecodeCheck>(
    checker: &C,
    items: &[DecodeCheckItem<C::Intent>],
    code: &[u8],
    mode: DecodeCheckMode,
    allowlist_policy: AllowlistPolicy,
) -> Result<(), DecodeCheckError> {
    if mode == DecodeCheckMode::Off {
        return Ok(());
    }
    let arch = checker.arch();
    #[cfg(test)]
    let forced_mismatch = trust_cg_process_env::var(FORCE_MISMATCH_TEST_ENV).ok();

    for item in items {
        // Length-drift / bounds guard: the recorded range must be inside the
        // buffer and non-empty. Anything else is itself a fail-closed defect.
        if item.start >= item.end || item.end > code.len() {
            let err = DecodeCheckError {
                message: format!(
                    "[decode-check/{arch}] {label}: recorded byte range {start}..{end} is empty \
                     or out of bounds for {len}-byte code buffer (length drift)",
                    label = checker.label(&item.intent),
                    start = item.start,
                    end = item.end,
                    len = code.len(),
                ),
            };
            increment_counter(&N_MISMATCHED);
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
        let outcome = checker.check_one(&item.intent, bytes, item.hole.as_ref());
        #[cfg(test)]
        let outcome = match forced_mismatch.as_deref() {
            Some(label) if checker.label(&item.intent) == label => {
                DecodeCheckOutcome::Mismatch(DecodeCheckError {
                    message: format!("forced by {FORCE_MISMATCH_TEST_ENV}={label}"),
                })
            }
            _ => outcome,
        };
        match outcome {
            DecodeCheckOutcome::Match => {
                increment_counter(&N_CHECKED);
                increment_counter(&N_MATCHED);
            }
            DecodeCheckOutcome::Allowlisted(reason) => {
                increment_counter(&N_ALLOWLISTED);
                if !telemetry_suppressed() {
                    allowlist_reasons().record(reason);
                }
                if allowlist_policy == AllowlistPolicy::Refuse {
                    let refusal = DecodeCheckError {
                        message: format!(
                            "{UNDECODED_EMISSION_REFUSAL_TAG} [decode-check/{arch}] {label} @byte \
                             {start}: the emitted word was not independently decoded ({reason}); \
                             proof-grade routes refuse an undecoded form | bytes={bytes:02x?}",
                            label = checker.label(&item.intent),
                            start = item.start,
                        ),
                    };
                    // `Off` returned before the loop.
                    if mode == DecodeCheckMode::Enforce {
                        return Err(refusal);
                    }
                    eprintln!(
                        "decode-check WARN (refused on this route): {}",
                        refusal.message
                    );
                }
            }
            DecodeCheckOutcome::Mismatch(err) => {
                increment_counter(&N_CHECKED);
                increment_counter(&N_MISMATCHED);
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

    Ok(())
}

#[cfg(test)]
mod telemetry_tests {
    use super::*;

    /// The composed transition record's check encode runs under
    /// `without_telemetry`: nothing it does is counted, and the flag is
    /// restored afterwards (also when the encode panics).
    #[test]
    fn suppressed_telemetry_counts_nothing_and_restores_the_flag() {
        static LOCAL: AtomicU64 = AtomicU64::new(0);
        assert!(!telemetry_suppressed());
        without_telemetry(|| {
            assert!(telemetry_suppressed());
            increment_counter(&LOCAL);
            without_telemetry(|| increment_counter(&LOCAL));
            assert!(telemetry_suppressed(), "a nested scope keeps it");
        });
        assert!(!telemetry_suppressed());
        assert_eq!(LOCAL.load(Ordering::Relaxed), 0);
        increment_counter(&LOCAL);
        assert_eq!(LOCAL.load(Ordering::Relaxed), 1);
        let unwound = std::panic::catch_unwind(|| without_telemetry(|| panic!("encode")));
        assert!(unwound.is_err());
        assert!(!telemetry_suppressed(), "restored after a panic");
    }

    #[test]
    fn poisoned_reason_snapshot_is_flagged_without_panicking() {
        let reasons = AllowlistReasonCounts::default();
        reasons.record("retained");
        poison(&reasons);
        let (counts, poisoned) = reasons.snapshot();
        assert_eq!(counts.get("retained"), Some(&1));
        assert!(poisoned);
    }

    #[test]
    fn poisoned_reason_record_and_reset_preserve_the_health_flag() {
        let reasons = AllowlistReasonCounts::default();
        poison(&reasons);
        reasons.record("after-poison");
        assert_eq!(
            reasons.snapshot(),
            (BTreeMap::from([("after-poison", 1)]), true)
        );
        reasons.reset();
        assert_eq!(reasons.snapshot(), (BTreeMap::new(), true));
        assert!(reasons.counts.is_poisoned());
    }

    #[test]
    fn reason_counts_saturate_without_poisoning() {
        let reasons = AllowlistReasonCounts::default();
        reasons.counts.lock().unwrap().insert("full", u64::MAX - 1);
        reasons.record("full");
        reasons.record("full");
        assert_eq!(
            reasons.snapshot(),
            (BTreeMap::from([("full", u64::MAX)]), false)
        );
        reasons.reset();
        assert_eq!(reasons.snapshot(), (BTreeMap::new(), false));
    }

    #[test]
    fn atomic_counts_saturate_instead_of_wrapping() {
        let counter = AtomicU64::new(u64::MAX - 1);
        increment_counter(&counter);
        increment_counter(&counter);
        assert_eq!(counter.load(Ordering::Relaxed), u64::MAX);
        let ordinary = AtomicU64::new(0);
        increment_counter(&ordinary);
        assert_eq!(ordinary.load(Ordering::Relaxed), 1);
    }

    /// Only an enforced check backs a certificate; every other backing names
    /// why it does not.
    #[test]
    fn only_an_enforced_check_backs_a_certificate() {
        assert_eq!(
            DecodeCheckBacking::from_mode(DecodeCheckMode::Enforce),
            DecodeCheckBacking::Enforced
        );
        assert_eq!(
            DecodeCheckBacking::from_mode(DecodeCheckMode::Warn),
            DecodeCheckBacking::Warned
        );
        assert_eq!(
            DecodeCheckBacking::from_mode(DecodeCheckMode::Off),
            DecodeCheckBacking::NotRun
        );
        assert!(DecodeCheckBacking::Enforced.gates_the_compile());
        assert_eq!(DecodeCheckBacking::Enforced.withheld_reason("ENC-3"), None);
        for (backing, needle) in [
            (DecodeCheckBacking::Warned, "warn mode"),
            (DecodeCheckBacking::NotRun, "was off"),
            (DecodeCheckBacking::NoEncode, "outside a compile's encode"),
        ] {
            assert!(!backing.gates_the_compile(), "{backing:?}");
            let reason = backing.withheld_reason("ENC-3").unwrap();
            assert!(
                reason.contains("ENC-3") && reason.contains(needle),
                "{backing:?}: {reason}"
            );
        }
    }

    /// A checker whose every word matches, so any disagreement the driver
    /// reports came from the test seam.
    struct AlwaysMatches;

    impl DecodeCheck for AlwaysMatches {
        type Intent = &'static str;

        fn arch(&self) -> &'static str {
            "test"
        }

        fn label(&self, intent: &Self::Intent) -> String {
            (*intent).to_owned()
        }

        fn check_one(
            &self,
            _intent: &Self::Intent,
            _bytes: &[u8],
            _hole: Option<&FixupHole>,
        ) -> DecodeCheckOutcome {
            DecodeCheckOutcome::Match
        }
    }

    /// The forced-mismatch seam fails exactly the labelled instruction, in
    /// enforce mode, and leaves warn and off as they are.
    #[test]
    fn the_forced_mismatch_seam_fails_only_the_labelled_instruction() {
        let items = [
            DecodeCheckItem {
                start: 0,
                end: 1,
                intent: "Other",
                hole: None,
            },
            DecodeCheckItem {
                start: 1,
                end: 2,
                intent: "MovRI",
                hole: None,
            },
        ];
        let code = [0u8; 2];
        assert!(run_decode_check(&AlwaysMatches, &items, &code, DecodeCheckMode::Enforce).is_ok());
        let force = [(FORCE_MISMATCH_TEST_ENV, "MovRI")];
        crate::env_lock::with_env_overrides(&force, || {
            let err = run_decode_check(&AlwaysMatches, &items, &code, DecodeCheckMode::Enforce)
                .unwrap_err();
            assert!(
                err.message.contains("MovRI @byte 1") && err.message.contains("forced by"),
                "{}",
                err.message
            );
            assert!(run_decode_check(&AlwaysMatches, &items, &code, DecodeCheckMode::Warn).is_ok());
            assert!(run_decode_check(&AlwaysMatches, &items, &code, DecodeCheckMode::Off).is_ok());
        });
    }

    fn poison(reasons: &AllowlistReasonCounts) {
        assert!(
            std::panic::catch_unwind(|| {
                let _guard = reasons.counts.lock().unwrap();
                panic!("armed telemetry poison");
            })
            .is_err()
        );
        assert!(reasons.counts.is_poisoned());
    }
}
