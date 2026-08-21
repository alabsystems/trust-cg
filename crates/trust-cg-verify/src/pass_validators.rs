// trust-cg-verify/pass_validators.rs - Per-pass translation validation (P3d)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Per-pass translation validators for the trust-ir -> machine-IR glue passes,
//! producing [`CertifiedPassChainEntry`] certificates consumed by
//! [`crate::certified_pass_chain::CertifiedPassChain`].
//!
//! # What this closes
//!
//! The SMT-verified per-instruction lowering core proves *individual* opcode
//! lowerings. It does **not** prove the *glue passes* that rewrite one IR shape
//! into another before instruction selection. Two such passes had escaped
//! miscompiles:
//!
//! * **#62 — switch normalization / jump-table lowering.** A switch is
//!   normalized into a `SUB idx, x, min`-style jump table (or a binary-search
//!   tree). A dropped or duplicated case silently routes a scrutinee value to
//!   the wrong successor. The per-instruction proofs never see the *pass-level*
//!   case set, so this is invisible to them.
//!
//! * **#67 — overflow / checked-arith expansion.** `overflowing_mul` /
//!   `checked_mul` on narrow signed integers is expanded into a multi-instruction
//!   sequence. The original expansion computed the overflow flag with the
//!   AArch64 SDIV identity `q = (a*b) SDIV rhs; overflow = (rhs != 0) && (q != lhs)`,
//!   which *relies on AArch64 `SDIV`-by-zero returning 0*. Ported verbatim to
//!   x86-64 — where `IDIV` by zero raises `#DE` (SIGFPE) — `x.overflowing_mul(0)`
//!   *crashed* instead of reporting "no overflow". The fix (commit `9395663`)
//!   replaced it with a division-free signed wide-multiply check.
//!
//! Both bugs are **arch-divergent**: the *same* expansion is correct on one
//! target and a miscompile on another. A correct per-pass validator must
//! therefore be *arch-parameterized* and model the architecture's actual
//! division-by-zero / overflow semantics.
//!
//! # Design
//!
//! A [`PassValidator`] runs a *translation-validation* equivalence proof between
//! the *input* (source) semantics of a pass and the *output* (rewritten)
//! semantics, expressed as [`SmtExpr`] trees, and — on success — emits a
//! [`CertifiedPassChainEntry`] whose certificate carries the obligation hash and
//! a verified result. A corrupted rewrite (dropped/duplicated switch case, or an
//! AArch64-ism applied to x86) fails the equivalence proof and produces **no**
//! certificate, so the fail-closed [`CertifiedPassChain`] rejects the compile.
//!
//! The equivalence proof reuses the existing [`crate::lowering_proof`]
//! machinery: an obligation is *valid* iff `verify_by_evaluation` returns
//! [`VerificationResult::Valid`] (exhaustive for the <= 8-bit scrutinee /
//! operand widths used by these validators).

use serde_json::json;
use sha2::{Digest, Sha256};

use crate::ay_bridge::{self, AYConfig, AYResult};
use crate::certified_pass_chain::CertifiedPassChainEntry;
use crate::certified_pass_checker::{
    CheckerArtifactRef, Lean5CheckerMode, Lean5CheckerPolicy, Lean5PassCertificateCheckRequest,
    PlaceholderTransportEvidence,
};
use crate::lowering_proof::{
    EXHAUSTIVE_WIDTH_THRESHOLD, ProofObligation, TransvalCheckKind, verify_by_evaluation,
};
use crate::smt::SmtExpr;
use crate::switch_proofs::{
    Case, encode_binary_search_switch, encode_jump_table_switch, encode_trust_ir_switch,
};
use crate::verify::VerificationResult;
use crate::x86_64_semantics::{IntCmpFlags, encode_int_cmp_flags, eval_int_condition};
use trust_cg_ir::x86_64_ops::X86CondCode;

// ---------------------------------------------------------------------------
// Target architecture (arch-parameterization for #67)
// ---------------------------------------------------------------------------

/// Target architecture for arch-divergent pass validation.
///
/// The #67 mis-port is invisible unless the validator models the architecture's
/// *integer-divide trap* behaviour, and it is x86 — NOT AArch64 — that traps:
///   * AArch64 `SDIV`/`UDIV` is TOTAL: divide-by-zero returns 0, and the signed
///     overflow input `INT_MIN / -1` returns `INT_MIN` (no trap).
///   * x86-64 `IDIV`/`DIV` raises `#DE` (SIGFPE) on BOTH undefined inputs:
///     divide-by-zero, AND signed quotient overflow `INT_MIN / -1` (the
///     mathematical quotient `-INT_MIN` is unrepresentable).
///     So the same SDIV-identity expansion is correct on AArch64 but a trapping
///     miscompile on x86 — which is exactly what [`TargetArch::idiv_traps`] models.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TargetArch {
    /// AArch64: `SDIV`/`UDIV` is total — divide-by-zero returns 0, `INT_MIN / -1`
    /// returns `INT_MIN`; neither traps.
    Aarch64,
    /// x86-64: `IDIV`/`DIV` raises `#DE` (SIGFPE / trap) on divide-by-zero AND on
    /// signed quotient overflow (`INT_MIN / -1`).
    X86_64,
}

impl TargetArch {
    /// Short stable identifier used in obligation hashes and certificate fields.
    pub fn slug(self) -> &'static str {
        match self {
            TargetArch::Aarch64 => "aarch64",
            TargetArch::X86_64 => "x86_64",
        }
    }

    /// Triple recorded in the certificate's target profile.
    pub fn triple(self) -> &'static str {
        match self {
            TargetArch::Aarch64 => "aarch64-unknown-none",
            TargetArch::X86_64 => "x86_64-unknown-none",
        }
    }

    /// Does an integer divide on this architecture TRAP (`#DE` / SIGFPE) rather
    /// than return a defined value for its undefined inputs? On x86-64 `IDIV`
    /// traps on BOTH divide-by-zero AND signed quotient overflow
    /// (`dividend == INT_MIN && divisor == -1`, whose mathematical quotient
    /// `-INT_MIN` is unrepresentable). AArch64 `SDIV` traps on neither
    /// (divide-by-zero returns 0; `INT_MIN / -1` returns `INT_MIN`). This is the
    /// crux of #67: the SDIV-identity expansion is total on AArch64 but partial
    /// (trapping) on x86, so the same expansion is correct on one and a
    /// miscompile on the other.
    pub fn idiv_traps(self) -> bool {
        match self {
            TargetArch::Aarch64 => false,
            TargetArch::X86_64 => true,
        }
    }
}

// ---------------------------------------------------------------------------
// PassValidator: the per-pass certificate producer interface
// ---------------------------------------------------------------------------

/// A per-pass translation validator.
///
/// Implementors describe a single pass invocation as a *source semantics* and a
/// *rewritten semantics* over the same symbolic inputs. [`validate`] runs the
/// SMT equivalence proof and, on success, mints a [`CertifiedPassChainEntry`]
/// for the fail-closed [`crate::certified_pass_chain::CertifiedPassChain`].
///
/// [`validate`]: PassValidator::validate
pub trait PassValidator {
    /// Stable pass name recorded in the certificate (`certificate.pass.name`).
    fn pass_name(&self) -> &str;

    /// Build the proof obligation whose validity *is* the per-pass correctness
    /// statement: source semantics == rewritten semantics for every input.
    ///
    /// The obligation must be self-contained (it carries its own symbolic
    /// inputs) so that [`verify_by_evaluation`] can discharge it.
    fn obligation(&self) -> ProofObligation;

    /// Target architecture this pass invocation was validated against.
    fn target_arch(&self) -> TargetArch;

    /// Run the equivalence proof. Returns a [`PassValidation`] that is either
    /// `Verified` (with the discharging strength) or `Rejected` (with the
    /// counterexample / reason). This never panics on a counterexample.
    ///
    /// # Soundness: no statistical-only certificates
    ///
    /// [`verify_by_evaluation`] is COMPLETE (a real proof) only at or below
    /// [`EXHAUSTIVE_WIDTH_THRESHOLD`] (8 bits); above it the evaluator falls back
    /// to *random sampling*, which can miss a single dropped / re-targeted case
    /// (e.g. a width-32 switch whose value `0x12345` was silently re-routed) yet
    /// still return [`VerificationResult::Valid`]. Minting a certificate from
    /// such a result is UNSOUND — a sampled "pass" is not a proof.
    ///
    /// So for any obligation whose widest input exceeds the exhaustive
    /// threshold we REQUIRE the formal solver: a [`AYResult::Verified`] is a real
    /// proof; anything else (counterexample, timeout, unknown, error, or no
    /// solver at all) is **Rejected** (fail closed). We never downgrade a missing
    /// solver or a merely-statistical pass into a certificate.
    fn validate(&self) -> PassValidation {
        self.validate_with_config(&AYConfig::default())
    }

    /// As [`PassValidator::validate`], with an explicit proof configuration.
    /// This is also the hermetic seam that demonstrates a portable committed
    /// certificate can discharge a wide validator even when `solver_path`
    /// names no live AY executable.
    fn validate_with_config(&self, config: &AYConfig) -> PassValidation {
        let obligation = self.obligation();
        let max_width = max_input_width(&obligation);

        // SOUNDNESS: `verify_by_evaluation` is exhaustive ONLY on its 1-2
        // input lanes; with 3+ separate bitvector inputs it degrades to
        // random MULTI-INPUT SAMPLING regardless of width (see
        // `verify_by_evaluation_with_config`), and a sampled `Valid` is not a
        // proof (found live: a wrong AE->BE cc-inversion obligation phrased
        // over five 1-bit flag inputs sampled as "Valid"). Route such
        // obligations to the formal-solver lane exactly like
        // above-threshold widths: no solver / no `Verified` => Rejected.
        let exhaustive_is_complete =
            obligation.inputs.len() <= 2 && max_width <= EXHAUSTIVE_WIDTH_THRESHOLD;

        if !exhaustive_is_complete {
            // Do not pre-gate on live solver availability: verify_with_ay's
            // proof funnel consults portable, independently checked certs
            // before resolving AY. A miss still reaches the live path and
            // returns Error when no solver exists, preserving fail-closed
            // semantics.
            return match ay_bridge::verify_with_ay(&obligation, config) {
                AYResult::Verified => PassValidation::Verified {
                    obligation_name: obligation.name,
                },
                AYResult::SolverUnsat => PassValidation::Rejected {
                    obligation_name: obligation.name,
                    reason:
                        "fail-closed: solver UNSAT lacked an independently accepted exact proof"
                            .to_string(),
                },
                AYResult::CounterExample(cex) => PassValidation::Rejected {
                    obligation_name: obligation.name,
                    reason: format!("counterexample: {cex:?}"),
                },
                AYResult::Timeout => PassValidation::Rejected {
                    obligation_name: obligation.name,
                    reason: "fail-closed: solver timeout (obligation outside the exhaustive lanes)"
                        .to_string(),
                },
                AYResult::Unknown(m) => PassValidation::Rejected {
                    obligation_name: obligation.name,
                    reason: format!("fail-closed: solver unknown ({m})"),
                },
                AYResult::Error(m) => PassValidation::Rejected {
                    obligation_name: obligation.name,
                    reason: format!("fail-closed: solver error ({m})"),
                },
            };
        }

        // Inside the exhaustive lanes (<= 2 inputs at or below the width
        // threshold), `verify_by_evaluation` enumerates the full input space
        // and is therefore a complete proof.
        match verify_by_evaluation(&obligation) {
            VerificationResult::Valid => PassValidation::Verified {
                obligation_name: obligation.name,
            },
            VerificationResult::Invalid { counterexample } => PassValidation::Rejected {
                obligation_name: obligation.name,
                reason: format!("counterexample: {counterexample}"),
            },
            VerificationResult::Unknown { reason } => PassValidation::Rejected {
                obligation_name: obligation.name,
                reason: format!("inconclusive: {reason}"),
            },
        }
    }

    /// Validate and, on success, produce a certified pass-chain entry for the
    /// given compilation unit at the given zero-based chain index.
    ///
    /// On failure returns the rejecting [`PassValidation`] so the caller fails
    /// closed and refuses to certify the compile.
    fn certify(
        &self,
        compilation_unit: &str,
        certificate_index: u64,
    ) -> Result<CertifiedPassChainEntry, PassValidation> {
        let validation = self.validate();
        match &validation {
            PassValidation::Verified { obligation_name } => {
                let request = build_pass_certificate_request(
                    self.pass_name(),
                    obligation_name,
                    self.target_arch(),
                    compilation_unit,
                    certificate_index,
                );
                Ok(CertifiedPassChainEntry::check(request))
            }
            PassValidation::Rejected { .. } => Err(validation),
        }
    }
}

/// Outcome of a per-pass equivalence proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PassValidation {
    /// The rewritten semantics are provably equal to the source semantics.
    Verified {
        /// Name of the discharged proof obligation.
        obligation_name: String,
    },
    /// The rewrite is not equivalent — a miscompile, or an arch-incorrect
    /// expansion. No certificate is produced.
    Rejected {
        /// Name of the rejected proof obligation.
        obligation_name: String,
        /// Human-readable counterexample / reason.
        reason: String,
    },
}

impl PassValidation {
    /// True iff the pass was certified equivalent.
    pub fn is_verified(&self) -> bool {
        matches!(self, PassValidation::Verified { .. })
    }
}

// ---------------------------------------------------------------------------
// (1) Switch-normalization validator (#62)
// ---------------------------------------------------------------------------

/// How a switch is normalized by the lowering pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SwitchStrategy {
    /// Dense contiguous range -> `SUB idx, x, min` + indexed jump table.
    JumpTable,
    /// Sparse -> balanced binary-search tree of compare-and-branch.
    BinarySearch,
}

/// Validator for the switch-normalization pass (#62).
///
/// Holds the *source* switch (the input case set + default) and the case set the
/// *normalized* lowering actually emits. The two diverge exactly when the pass
/// drops, duplicates, or re-targets a case — the #62 failure mode. The
/// obligation proves "for every scrutinee value the normalized switch selects
/// the same successor block as the source switch", which is exhaustive over the
/// 8-bit scrutinee domain.
#[derive(Debug, Clone)]
pub struct SwitchNormalizationValidator {
    /// Pass name recorded in the certificate.
    pub pass_name: String,
    /// Scrutinee bit-width (these validators use 8 for an exhaustive proof).
    pub width: u32,
    /// Source switch cases `(value, target_block_id)`, in source order.
    pub source_cases: Vec<Case>,
    /// Source default/fall-through block id.
    pub default_id: u64,
    /// Case set the normalized lowering emits. For a *correct* normalization
    /// this equals `source_cases` (modulo order, which is semantics-preserving).
    pub normalized_cases: Vec<Case>,
    /// Normalization strategy chosen by the pass.
    pub strategy: SwitchStrategy,
    /// Target architecture (switch successor selection is arch-independent, but
    /// the certificate records which target it was validated for).
    pub arch: TargetArch,
}

impl SwitchNormalizationValidator {
    /// Construct a validator for a *faithful* normalization where the emitted
    /// case set is the source case set (the common, correct path).
    pub fn faithful(
        pass_name: impl Into<String>,
        width: u32,
        source_cases: Vec<Case>,
        default_id: u64,
        strategy: SwitchStrategy,
        arch: TargetArch,
    ) -> Self {
        let normalized_cases = source_cases.clone();
        Self {
            pass_name: pass_name.into(),
            width,
            source_cases,
            default_id,
            normalized_cases,
            strategy,
            arch,
        }
    }
}

impl PassValidator for SwitchNormalizationValidator {
    fn pass_name(&self) -> &str {
        &self.pass_name
    }

    fn target_arch(&self) -> TargetArch {
        self.arch
    }

    fn obligation(&self) -> ProofObligation {
        let x = SmtExpr::var("x", self.width);

        // Source (trust-ir) semantics: linear-scan ITE over the *input* cases.
        let source =
            encode_trust_ir_switch(x.clone(), &self.source_cases, self.default_id, self.width);

        // Rewritten (machine) semantics: the normalized lowering over the
        // *emitted* cases. A dropped/duplicated/re-targeted case changes this
        // expression, breaking equivalence.
        let rewritten = match self.strategy {
            SwitchStrategy::JumpTable => {
                encode_jump_table_switch(x, &self.normalized_cases, self.default_id, self.width)
            }
            SwitchStrategy::BinarySearch => {
                encode_binary_search_switch(x, &self.normalized_cases, self.default_id, self.width)
            }
        };

        ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: format!(
                "pass[{}]: switch normalization preserves successor selection ({:?}, {})",
                self.pass_name,
                self.strategy,
                self.arch.slug()
            ),
            trust_ir_expr: source,
            aarch64_expr: rewritten,
            inputs: vec![("x".to_string(), self.width)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(TransvalCheckKind::ControlFlow),
        }
    }
}

// ---------------------------------------------------------------------------
// (2) Overflow / checked-arith expansion validator (#67)
// ---------------------------------------------------------------------------

/// Which checked-overflow operation the expansion implements. These validators
/// focus on the *signed multiply* case, the #67 mis-port, but the add/sub
/// shapes are included so the same validator covers the whole expansion family.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckedOp {
    /// Signed add with overflow (`overflowing_add` / `checked_add`).
    SignedAdd,
    /// Signed sub with overflow (`overflowing_sub` / `checked_sub`).
    SignedSub,
    /// Signed mul with overflow (`overflowing_mul` / `checked_mul`) — #67.
    SignedMul,
}

/// The concrete expansion strategy the pass emitted for a checked operation.
///
/// This is what makes #67 catchable: the *same source op* can be expanded two
/// different ways, one of which is only correct on AArch64.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OverflowExpansion {
    /// Division-free wide-multiply overflow check (the #67 *fix*): sign-extend
    /// both operands to the next-wider type, multiply, truncate to the narrow
    /// type and sign-extend back; overflow iff the wide product differs from
    /// that round-trip. Never divides — correct on every target.
    DivisionFreeWideMul,
    /// SDIV-identity overflow check (the #67 *bug*): `q = result SDIV rhs;
    /// overflow = (rhs != 0) && (q != lhs)`. Correct **only** on AArch64, where
    /// `SDIV`-by-zero is defined to return 0. On x86-64 the `IDIV` traps.
    SdivIdentity,
    /// Sign-of-operands carry check for signed add/sub. Arch-independent.
    SignBitCheck,
}

/// Validator for the overflow / checked-arith expansion pass (#67).
///
/// Proves that the *expanded instruction sequence* computes the same
/// `(value, overflow_flag)` pair as the *spec checked-overflow opcode*, packed
/// as a single bitvector `overflow_b1 :: value_iN` (mirroring
/// [`crate::checked_overflow_proofs`]). Crucially, the expansion side is
/// **arch-parameterized**: a divide that would trap on the target architecture
/// makes the expansion ill-defined for that input, and the proof must fail.
#[derive(Debug, Clone)]
pub struct OverflowExpansionValidator {
    /// Pass name recorded in the certificate.
    pub pass_name: String,
    /// Operand bit-width. These validators use 8 for an exhaustive proof.
    pub width: u32,
    /// The checked operation being expanded.
    pub op: CheckedOp,
    /// The expansion strategy the pass actually emitted.
    pub expansion: OverflowExpansion,
    /// Target architecture — selects divide-by-zero semantics.
    pub arch: TargetArch,
}

impl OverflowExpansionValidator {
    /// Construct a validator for the canonical signed-mul-overflow case.
    pub fn signed_mul(
        pass_name: impl Into<String>,
        width: u32,
        expansion: OverflowExpansion,
        arch: TargetArch,
    ) -> Self {
        Self {
            pass_name: pass_name.into(),
            width,
            op: CheckedOp::SignedMul,
            expansion,
            arch,
        }
    }
}

impl PassValidator for OverflowExpansionValidator {
    fn pass_name(&self) -> &str {
        &self.pass_name
    }

    fn target_arch(&self) -> TargetArch {
        self.arch
    }

    fn obligation(&self) -> ProofObligation {
        let lhs = SmtExpr::var("a", self.width);
        let rhs = SmtExpr::var("b", self.width);

        // Spec semantics: the language-level checked-overflow contract.
        let spec = spec_checked(self.op, lhs.clone(), rhs.clone(), self.width);

        // Expanded semantics: what the pass actually emits, arch-parameterized.
        let expanded = expanded_checked(
            self.op,
            self.expansion,
            self.arch,
            lhs.clone(),
            rhs.clone(),
            self.width,
        );

        ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: format!(
                "pass[{}]: overflow expansion {:?}/{:?} matches spec on {}",
                self.pass_name,
                self.op,
                self.expansion,
                self.arch.slug()
            ),
            trust_ir_expr: spec,
            aarch64_expr: expanded,
            inputs: vec![("a".to_string(), self.width), ("b".to_string(), self.width)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(TransvalCheckKind::InstructionLowering),
        }
    }
}

// ---------------------------------------------------------------------------
// Popcount SWAR-expansion validator
// ---------------------------------------------------------------------------
//
// On the default `generic_x86_64` target (no POPCNT cpu feature) the x86
// pipeline expands a single proven `Popcnt` opcode into a ~27-31 instruction
// Hacker's-Delight shift/mask SWAR sequence (`expand_x86_popcnt_inst`). That
// expansion runs in the ENCODER, *after* the per-compile proof certificates are
// generated over the pre-encoder instruction stream, so the shipped SWAR bytes
// previously carried no proof obligation at all. This validator re-proves, as a
// translation-validation equivalence, that the fixed SWAR algorithm computes the
// population count — closing the post-expansion soundness gap for popcnt the same
// way `OverflowExpansionValidator` closes it for the signed-mul-overflow #67
// expansion.
//
// Width 8 keeps the proof EXHAUSTIVE (a complete proof, never a sampled one — see
// `EXHAUSTIVE_WIDTH_THRESHOLD`). At 8 bits the cross-byte reduction shifts (>>8,
// >>16, >>32) are no-ops, exactly as in the emitted code, so the obligation
// faithfully exercises the bit-folding core (the masks `m1/m2/m4` and the 1/2/4
// shift amounts) that does the actual counting. This is the same proxy-width
// fidelity the codebase already accepts for the overflow-mul canary.

/// Reference population count of `x` at width `w`: the sum, as a width-`w`
/// bitvector, of its individual bits.
fn popcount_spec(x: SmtExpr, w: u32) -> SmtExpr {
    let one = SmtExpr::bv_const(1, w);
    let mut acc = x.clone().bvand(one.clone());
    for i in 1..w {
        let bit = x
            .clone()
            .bvlshr(SmtExpr::bv_const(i as u64, w))
            .bvand(one.clone());
        acc = acc.bvadd(bit);
    }
    acc
}

/// The fixed Hacker's-Delight shift/mask SWAR popcount, symbolically mirroring
/// `expand_x86_popcnt_inst` at width `w` with the width-scaled masks. The
/// reduction shifts run 8, 16, … up to (but not including) `w`, matching the
/// emitted `[8, 16]` (+32 for 64-bit) shift-add chain (at w=8 there are none, as
/// `>>8` on an 8-bit value is identity).
fn popcount_swar(x: SmtExpr, w: u32, m1: u64, m2: u64, m4: u64, final_mask: u64) -> SmtExpr {
    // dst = x - ((x >> 1) & m1)
    let t = x
        .clone()
        .bvlshr(SmtExpr::bv_const(1, w))
        .bvand(SmtExpr::bv_const(m1, w));
    let dst = x.bvsub(t);
    // dst = (dst & m2) + ((dst >> 2) & m2)
    let lo = dst.clone().bvand(SmtExpr::bv_const(m2, w));
    let hi = dst
        .bvlshr(SmtExpr::bv_const(2, w))
        .bvand(SmtExpr::bv_const(m2, w));
    let dst = lo.bvadd(hi);
    // dst = (dst + (dst >> 4)) & m4
    let dst = dst
        .clone()
        .bvadd(dst.bvlshr(SmtExpr::bv_const(4, w)))
        .bvand(SmtExpr::bv_const(m4, w));
    // dst += dst >> shift, for shift = 8, 16, … < w
    let mut dst = dst;
    let mut shift = 8u32;
    while shift < w {
        dst = dst
            .clone()
            .bvadd(dst.bvlshr(SmtExpr::bv_const(shift as u64, w)));
        shift *= 2;
    }
    // dst & final_mask
    dst.bvand(SmtExpr::bv_const(final_mask, w))
}

/// Translation-validation validator for the x86 generic-target popcount SWAR
/// expansion (`expand_x86_popcnt_inst`).
pub struct PopcntSwarExpansionValidator {
    /// Pass name recorded in the certificate.
    pub pass_name: String,
    /// Operand bit-width. Use 8 for an exhaustive (complete) proof.
    pub width: u32,
}

impl PopcntSwarExpansionValidator {
    /// Construct a validator for the x86 generic-target SWAR popcount expansion.
    pub fn x86_generic(pass_name: impl Into<String>, width: u32) -> Self {
        Self {
            pass_name: pass_name.into(),
            width,
        }
    }

    /// Width-scaled SWAR masks (the byte pattern of the emitted 32/64-bit masks).
    fn masks(width: u32) -> (u64, u64, u64, u64) {
        let mask = |byte: u64| {
            let mut v = 0u64;
            let mut i = 0;
            while i < width {
                v |= byte << i;
                i += 8;
            }
            v
        };
        // final_mask just has to be >= the maximum count (width); 0x3f/0x7f in
        // the emitted code, here the tight power-of-two-minus-one cover.
        let final_mask = (width.next_power_of_two() * 2 - 1) as u64;
        (mask(0x55), mask(0x33), mask(0x0f), final_mask)
    }
}

impl PassValidator for PopcntSwarExpansionValidator {
    fn pass_name(&self) -> &str {
        &self.pass_name
    }

    fn target_arch(&self) -> TargetArch {
        TargetArch::X86_64
    }

    fn obligation(&self) -> ProofObligation {
        let x = SmtExpr::var("x", self.width);
        let (m1, m2, m4, final_mask) = Self::masks(self.width);

        let spec = popcount_spec(x.clone(), self.width);
        let expanded = popcount_swar(x, self.width, m1, m2, m4, final_mask);

        ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: format!(
                "pass[{}]: popcount SWAR expansion matches spec on x86_64 (i{})",
                self.pass_name, self.width
            ),
            trust_ir_expr: spec,
            aarch64_expr: expanded,
            inputs: vec![("x".to_string(), self.width)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(TransvalCheckKind::InstructionLowering),
        }
    }
}

// ---------------------------------------------------------------------------
// Sentinel-S5 guard-carrier expansion (translation validation)
// ---------------------------------------------------------------------------

/// Which Sentinel-S5 guard carrier a [`GuardCarrierExpansionValidator`] checks.
/// Each carrier is expanded (`expand_x86_{bounds,null,div_zero,shift_range}_check
/// _carriers`) to `CMP/TEST + Jcc<cc> + UD2` AFTER the per-instruction certs are
/// generated, so the certs see only the individually-correct `CMP` and `Jcc` —
/// NOTHING binds the chosen condition code to the carrier's intended trap set. A
/// wrong cc (e.g. `B` instead of `AE`, inverting a bounds check, or `NE` instead
/// of `E`, inverting a null check) still certifies instruction-by-instruction yet
/// silently drops/inverts the guard.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GuardCarrierKind {
    /// `TrapBoundsCheckExact [base, index, Imm(bound)]` → `CMP index, bound; Jcc
    /// AE`. Traps iff `index >=u bound`.
    Bounds,
    /// `TrapShiftRangeExact [amount, Imm(bitwidth)]` → `CMP amount, bitwidth; Jcc
    /// AE`. Traps iff `amount >=u bitwidth`.
    ShiftRange,
    /// `TrapNullIfZeroExact [ptr]` → `TEST ptr, ptr; Jcc E`. Traps iff `ptr == 0`.
    NullIfZero,
    /// `TrapDivZeroExact [divisor]` → `TEST divisor, divisor; Jcc E`. Traps iff
    /// `divisor == 0`.
    DivZero,
}

/// The flags `TEST x, x` sets, as genuine functions of `x`. `TEST` ANDs the
/// operand with itself (`x & x == x`) and so sets ZF = `(x & x) == 0`, SF =
/// `msb(x & x)`, PF = parity of the low byte, and clears CF and OF. Modeling the
/// emitted-side ZF as `(x & x) == 0` (rather than `x == 0`) keeps the obligation
/// non-degenerate: the proof genuinely discharges `(x & x) == 0  ⟺  x <u 1`.
fn test_self_flags(width: u32, x: SmtExpr) -> IntCmpFlags {
    let anded = x.clone().bvand(x.clone());
    let msb = |v: SmtExpr| {
        v.extract(width - 1, width - 1)
            .eq_expr(SmtExpr::bv_const(1, 1))
    };
    let zf = anded.clone().eq_expr(SmtExpr::bv_const(0, width));
    let sf = msb(anded.clone());
    let low8 = if width >= 8 {
        anded.clone().extract(7, 0)
    } else {
        anded.clone().zero_ext(8 - width)
    };
    let mut xor_acc = low8.clone().extract(0, 0);
    for i in 1..8u32 {
        xor_acc = xor_acc.bvxor(low8.clone().extract(i, i));
    }
    let pf = xor_acc.eq_expr(SmtExpr::bv_const(0, 1));
    IntCmpFlags {
        zf,
        sf,
        cf: SmtExpr::bool_const(false),
        of: SmtExpr::bool_const(false),
        pf,
    }
}

/// Translation-validation that a Sentinel-S5 guard-carrier expansion's chosen
/// condition code makes the emitted `Jcc` branch trap on EXACTLY the carrier's
/// intended set. The `cond` passed here is the SAME `X86CondCode` value the
/// expander emits (see the canary in `trust-cg-codegen` — it derives one local
/// `trap_cond` and uses it for both the proof and the emitted `Jcc`, so they
/// cannot drift). The obligation proves the emitted-condition predicate equals an
/// INDEPENDENTLY-expressed intended predicate (`bvuge` / `x <u 1`) against the
/// emitted CMP/TEST flags, so a wrong cc refutes and the correct cc is not a
/// degenerate `X == X`.
pub struct GuardCarrierExpansionValidator {
    /// Pass name recorded in the certificate.
    pub pass_name: String,
    /// Which carrier's expansion is checked.
    pub kind: GuardCarrierKind,
    /// The condition code the expander emits for the trap branch.
    pub cond: X86CondCode,
    /// Operand bit-width. Use 8 for an exhaustive (complete) proof.
    pub width: u32,
}

impl GuardCarrierExpansionValidator {
    /// Construct a validator for one guard-carrier expansion at `width` bits.
    pub fn new(
        pass_name: impl Into<String>,
        kind: GuardCarrierKind,
        cond: X86CondCode,
        width: u32,
    ) -> Self {
        Self {
            pass_name: pass_name.into(),
            kind,
            cond,
            width,
        }
    }
}

impl PassValidator for GuardCarrierExpansionValidator {
    fn pass_name(&self) -> &str {
        &self.pass_name
    }

    fn target_arch(&self) -> TargetArch {
        TargetArch::X86_64
    }

    fn obligation(&self) -> ProofObligation {
        let w = self.width;
        let lhs = SmtExpr::var("lhs", w);
        let (emitted_cond, intended, inputs) = match self.kind {
            // `CMP lhs, rhs; Jcc <cond>` — intended: trap iff lhs >=u rhs. The
            // intended side uses the independent `bvuge` primitive (the emitted AE
            // is `!cf == !(lhs <u rhs)`), so the obligation is non-degenerate.
            GuardCarrierKind::Bounds | GuardCarrierKind::ShiftRange => {
                let rhs = SmtExpr::var("rhs", w);
                let flags = encode_int_cmp_flags(w, lhs.clone(), rhs.clone());
                let emitted = eval_int_condition(self.cond, &flags);
                let intended = lhs.clone().bvuge(rhs);
                (
                    emitted,
                    intended,
                    vec![("lhs".to_string(), w), ("rhs".to_string(), w)],
                )
            }
            // `TEST lhs, lhs; Jcc <cond>` — intended: trap iff lhs == 0.
            // Express the independent intended predicate as `lhs <u 1` rather
            // than another syntactic equality-to-zero. Besides being exactly
            // equivalent for every unsigned bitvector, this keeps the formal
            // obligation non-degenerate through AY's SMT rewriting: the
            // emitted side remains TEST's `(lhs & lhs) == 0`, so offline
            // portable certification reaches a genuine bit-blast instead of
            // collapsing to an evidence-free canonical-false CNF.
            GuardCarrierKind::NullIfZero | GuardCarrierKind::DivZero => {
                let flags = test_self_flags(w, lhs.clone());
                let emitted = eval_int_condition(self.cond, &flags);
                let intended = lhs.clone().bvult(SmtExpr::bv_const(1, w));
                (emitted, intended, vec![("lhs".to_string(), w)])
            }
        };

        ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: format!(
                "pass[{}]: guard carrier {:?} traps iff intended on x86_64 (cc={:?}, i{w})",
                self.pass_name, self.kind, self.cond
            ),
            trust_ir_expr: bv1(intended),
            aarch64_expr: bv1(emitted_cond),
            inputs,
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(TransvalCheckKind::InstructionLowering),
        }
    }
}

// ---------------------------------------------------------------------------
// Condition-code inversion (OPT-8 branch layout — #3-trap-carriers class)
// ---------------------------------------------------------------------------

/// Translation-validation that a condition-code INVERSION is the exact
/// complement: for EVERY RFLAGS state, `Jcc <inverted>` branches iff
/// `Jcc <original>` does not.
///
/// # Why this obligation exists (the wrong-cc class, again)
///
/// The x86 branch-layout pass (OPT-8) rewrites a terminal `jcc cc, T; jmp F`
/// pair into `jcc invert(cc), F; jmp T` so the hot/fallthrough successor
/// stops paying a taken branch. The rewrite is layout-only EXCEPT for the one
/// semantic step: the substituted condition code must branch on exactly the
/// complementary flag set. The downstream per-instruction certs cannot catch
/// a wrong substitution — a `Jcc` with ANY cc is individually well-formed —
/// so a wrong inversion (e.g. `AE -> BE` where `AE -> B` was meant) would
/// silently invert a user branch or a bounds/null/div0 guard: exactly the
/// #3-trap-carriers failure mode [`GuardCarrierExpansionValidator`] closes
/// for guard expansion.
///
/// # The proof
///
/// The obligation quantifies over the five RFLAGS bits packed as ONE free
/// 5-bit input (32 states, exhaustively evaluated — a single input at width
/// 5 <= [`EXHAUSTIVE_WIDTH_THRESHOLD`], so [`PassValidator::validate`]
/// discharges it as a complete proof, never a sample; the packing matters:
/// `verify_by_evaluation` degrades to random SAMPLING for obligations with
/// 3+ separate inputs regardless of width):
///
/// ```text
///   forall flags: bv5 .   // bit i = zf, sf, cf, of, pf
///     eval_int_condition(inverted, flags) == NOT eval_int_condition(original, flags)
/// ```
///
/// Both sides use [`eval_int_condition`] — the SAME per-cc flag formulas the
/// guard-carrier proofs trust — applied to the two DIFFERENT cc values, so
/// the obligation is non-degenerate (each cc is a distinct formula over
/// distinct flag bits; a wrong `inverted` refutes on some flag state).
/// Quantifying over raw flag states is deliberately STRONGER than
/// quantifying over `CMP a, b` operands: it also covers flags produced by
/// `TEST` and by ALU-op flag writes, i.e. every producer a rewritten `Jcc`
/// might read.
///
/// # Production binding
///
/// The x86 pipeline's admission callback derives `inverted` from the SAME
/// local value the pass writes into the rewritten instruction and passes
/// both cc's here (the shared-local discipline from the guard-carrier
/// canary), then mints and checks a [`CertifiedPassChainEntry`] per admitted
/// cc via [`PassValidator::certify`]. Rejection skips the rewrite (an
/// admission gate) — it never fails the compile, because the un-rewritten
/// two-branch original is always correct.
pub struct CondCodeInversionValidator {
    /// Pass name recorded in the certificate.
    pub pass_name: String,
    /// The condition code of the original conditional branch.
    pub original: X86CondCode,
    /// The condition code the pass substitutes (the claimed complement).
    pub inverted: X86CondCode,
}

impl CondCodeInversionValidator {
    /// Construct a validator for one claimed inversion pair.
    pub fn new(pass_name: impl Into<String>, original: X86CondCode, inverted: X86CondCode) -> Self {
        Self {
            pass_name: pass_name.into(),
            original,
            inverted,
        }
    }
}

impl PassValidator for CondCodeInversionValidator {
    fn pass_name(&self) -> &str {
        &self.pass_name
    }

    fn target_arch(&self) -> TargetArch {
        TargetArch::X86_64
    }

    fn obligation(&self) -> ProofObligation {
        // The five RFLAGS bits packed into ONE free 5-bit input, so the
        // evaluator's single-input exhaustive lane enumerates all 32 states
        // (3+ separate inputs would silently degrade to random sampling —
        // not a proof).
        let packed = SmtExpr::var("flags", 5);
        let bit = |i: u32| {
            packed
                .clone()
                .extract(i, i)
                .eq_expr(SmtExpr::bv_const(1, 1))
        };
        let flags = IntCmpFlags {
            zf: bit(0),
            sf: bit(1),
            cf: bit(2),
            of: bit(3),
            pf: bit(4),
        };

        // Intended semantics: the complement of the ORIGINAL condition.
        let intended = eval_int_condition(self.original, &flags).not_expr();
        // Rewritten semantics: the SUBSTITUTED condition, as emitted.
        let rewritten = eval_int_condition(self.inverted, &flags);

        ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: format!(
                "pass[{}]: cc inversion {:?} -> {:?} is the exact complement over all RFLAGS \
                 states on x86_64",
                self.pass_name, self.original, self.inverted
            ),
            trust_ir_expr: bv1(intended),
            aarch64_expr: bv1(rewritten),
            inputs: vec![("flags".to_string(), 5)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(TransvalCheckKind::ControlFlow),
        }
    }
}

// ---------------------------------------------------------------------------
// Strength-reduction recurrence validator (x86 OPT-3a)
// ---------------------------------------------------------------------------

/// Per-width validator for the x86 induction-variable strength-reduction
/// rewrite (`trust_cg_opt::x86_strength_reduce`).
///
/// # What the pass claims
///
/// The pass replaces a loop-body multiply `d = iv * s` (with `iv` a simple
/// induction variable stepping by the compile-time constant `step` and `s`
/// a compile-time constant stride, possibly materialized in a
/// loop-invariant register) with a recurrence carrier `r`:
///
/// ```text
///   preheader:  r  = iv * s            ; SAME multiply, of the entering iv
///   loop body:  d  = r                 ; replaces the per-iteration multiply
///   after the iv update (iv' = iv + step):
///               r' = r + (s * step)    ; the recurrence advance
/// ```
///
/// By induction over iterations, `r == iv * s` holds at every loop point
/// (outside the two-instruction update window, where `r` is never read):
/// the base case is literally the same multiply instruction applied to the
/// entering `iv`, and the inductive step is THIS validator's obligation:
///
/// ```text
///   forall iv : bv<width> .  (iv + step) * s  ==  iv*s + (s * step)
/// ```
///
/// (all operations mod 2^width — exactly the x86 `imul`/`add` carrier
/// semantics at that register width, and exactly Rust's release-mode
/// wrapping multiply semantics the trust-ir carries here).
///
/// Everything else the pass relies on (loop-invariance and constancy of
/// `s`, the single in-loop `iv` definition, lockstep placement of the `r`
/// advance, dead RFLAGS at every insertion/replacement point, no side
/// entries into the loop) is *structural* and enforced by construction in
/// the pass; the algebraic identity above is the one semantic step, and it
/// is never assumed — each `(width, step, stride)` triple the pass wants to
/// use must be discharged through [`PassValidator::validate`] first.
///
/// # Discharge strength
///
/// Both `step` AND the stride `s` are per-instance compile-time literals
/// (the pass only admits constant strides — a symbolic-times-symbolic
/// `bvmul` miter is beyond the solver's practical reach at 32/64 bits, and
/// an undischargeable obligation would silently disable the pass; with a
/// literal stride the multiplies bit-blast to shift-add circuits). The
/// obligation therefore has exactly ONE symbolic input (`iv`), so:
///   * width <= 8: `verify_by_evaluation` enumerates the full input space —
///     a complete exhaustive proof.
///   * width 16/32/64: routed to the formal solver (AY); anything short of
///     `Verified` (counterexample / timeout / unknown / no solver) is
///     Rejected and the pass leaves the original multiply in place.
///
/// # Production binding
///
/// The x86 pipeline's admission callback constructs this validator from the
/// SAME `(width, step, stride)` values the pass writes into the rewritten
/// instructions (the shared-local discipline of the cc-inversion
/// validators), then mints and checks a [`CertifiedPassChainEntry`] via
/// [`PassValidator::certify`]. Rejection skips the rewrite (an admission
/// gate) — the un-rewritten multiply is always correct, so this never fails
/// the compile and never miscompiles.
pub struct StrengthReduceRecurrenceValidator {
    /// Pass name recorded in the certificate.
    pub pass_name: String,
    /// Carrier register width in bits (32 for Gpr32, 64 for Gpr64).
    pub width: u32,
    /// The induction variable's compile-time constant step.
    pub step: i64,
    /// The compile-time constant stride the multiply scales the IV by.
    pub stride: i64,
}

impl StrengthReduceRecurrenceValidator {
    /// Construct a validator for one `(width, step, stride)` recurrence
    /// instance.
    pub fn new(pass_name: impl Into<String>, width: u32, step: i64, stride: i64) -> Self {
        Self {
            pass_name: pass_name.into(),
            width,
            step,
            stride,
        }
    }

    /// Build the two sides of the ring-recurrence identity that
    /// [`Self::obligation`] poses, as standalone expressions, so the
    /// cited-lemma discharge below can structurally recognize the obligation
    /// without depending on `obligation()`'s exact spelling.
    ///
    /// `(intended, rewritten)` where
    /// `intended  = (iv + step) * stride` and
    /// `rewritten = iv*stride + stride*step`, all mod `2^width`.
    fn ring_recurrence_sides(&self) -> (SmtExpr, SmtExpr) {
        let iv = SmtExpr::var("iv", self.width);
        let step_c = SmtExpr::bv_const(self.step as u64, self.width);
        let stride_c = SmtExpr::bv_const(self.stride as u64, self.width);
        let intended = iv.clone().bvadd(step_c.clone()).bvmul(stride_c.clone());
        let rewritten = iv.bvmul(stride_c.clone()).bvadd(stride_c.bvmul(step_c));
        (intended, rewritten)
    }

    /// THE TRUST POINT (the one cited lemma) — discharge the strength-reduce
    /// recurrence obligation by CITING the ring axioms, with NO solver.
    ///
    /// # Cited lemma (distributivity + commutativity in Z/2^width)
    ///
    /// The obligation [`Self::obligation`] poses is
    ///
    /// ```text
    ///   forall iv .  (iv + step) * stride  ==  iv*stride + stride*step   (mod 2^width)
    /// ```
    ///
    /// This is a RING IDENTITY, unconditionally true for ALL `iv`, `step`,
    /// `stride` — no per-instance condition. It follows from exactly two
    /// axioms of the commutative ring `(Z/2^width, +, *)`:
    ///
    /// * **Distributivity** of `*` over `+`:
    ///   `(iv + step) * stride == iv*stride + step*stride`.
    /// * **Commutativity** of `*`:
    ///   `step*stride == stride*step`.
    ///
    /// Substituting the second into the first gives the right-hand side
    /// verbatim. `Z/2^width` (two's-complement bitvector arithmetic at the
    /// carrier width — the x86 `imul`/`add` and Rust wrapping-mul semantics)
    /// IS a commutative ring, so both axioms hold at every width. There is
    /// nothing to solve: bit-blasting `(iv+step)*stride == iv*stride +
    /// stride*step` for a concrete large stride spends seconds re-deriving an
    /// axiom the ring already grants us.
    ///
    /// **This citation — distributivity + commutativity of `*` over `+` in
    /// `Z/2^width` — is the SOLE trust point of this discharge path.** It is
    /// more basic than the Granlund-Montgomery lemma the magic-division
    /// transform cites (`magic_udiv.rs`); a future machine-checked LIA/BV
    /// discharge (AY's `la_generic` + the Clean checker, the project's §4.F
    /// theory-lemma path) can replace this citation with a checked proof of
    /// the ring identity — the recognition predicate below *is* exactly the
    /// hypothesis such a theory lemma would consume.
    ///
    /// # Fail-safe recognition (never admit an arbitrary obligation)
    ///
    /// The citation is applied ONLY when the posed obligation is EXACTLY the
    /// ring-recurrence shape for this `(width, step, stride)`. We rebuild both
    /// sides from `(width, step, stride)` ([`Self::ring_recurrence_sides`])
    /// and require them to be STRUCTURALLY EQUAL (derived `PartialEq` on the
    /// full `SmtExpr` tree — operand immediates and widths baked in) to the
    /// obligation's `trust_ir_expr` / `aarch64_expr`, with the input list the
    /// single `iv` at `width` and no preconditions. If ANY of these checks
    /// fails (a different obligation shape, a wrong rewrite such as
    /// `iv*stride + step` missing the `*stride`, extra inputs, or a
    /// precondition), we return `None` and the caller FALLS THROUGH to the
    /// solver — we never blindly admit. Recognizing the always-true ring
    /// identity and citing it is the whole story; an unrecognized obligation
    /// gets no free pass.
    ///
    /// On a successful recognition we still MINT a registered
    /// [`CertifiedPassChainEntry`] (via [`build_pass_certificate_request`],
    /// the same certificate the solver path mints) so the obligation stays a
    /// REGISTERED pass-chain obligation, discharged by the cited lemma rather
    /// than by a BV solve — mirroring how magic-division records its GM trust
    /// point. It is not deleted from the registry and it is never an `X == X`
    /// vacuity: the two sides are genuinely different expression trees whose
    /// equality is the ring identity we cite.
    pub fn certify_by_ring_axiom(
        &self,
        compilation_unit: &str,
        certificate_index: u64,
    ) -> Option<CertifiedPassChainEntry> {
        // Keep the validator building the obligation: it is both documentation
        // and the defensive structural check that what we are about to cite is
        // in fact the ring-recurrence identity and nothing else.
        let obligation = self.obligation();

        if !self.poses_ring_recurrence_identity(&obligation) {
            // NOT the exact always-true ring identity — do not cite; the caller
            // falls through to the fail-closed solver path.
            return None;
        }

        // Recognized the ring identity. Discharge by the cited lemma: mint the
        // SAME registered certificate a `Verified` solve would, so the
        // obligation stays honestly registered in the pass chain.
        let request = build_pass_certificate_request(
            self.pass_name(),
            &obligation.name,
            self.target_arch(),
            compilation_unit,
            certificate_index,
        );
        Some(CertifiedPassChainEntry::check(request))
    }

    /// The fail-safe recognition predicate for [`Self::certify_by_ring_axiom`]:
    /// `true` iff `obligation` is EXACTLY the always-true ring-recurrence
    /// identity `(iv + step)*stride == iv*stride + stride*step` for this
    /// `(width, step, stride)` — both sides structurally equal (derived
    /// `PartialEq` over the whole `SmtExpr` tree), the single `iv` input at
    /// `width`, and no preconditions / fp inputs. Anything else (a different
    /// shape, a wrong rewrite missing the `*stride`, extra inputs, a
    /// precondition) returns `false` so the caller routes to the solver.
    /// Exposed so a refutation test can confirm a non-ring obligation is not
    /// admitted by the citation.
    pub fn poses_ring_recurrence_identity(&self, obligation: &ProofObligation) -> bool {
        let (expected_intended, expected_rewritten) = self.ring_recurrence_sides();
        obligation.trust_ir_expr == expected_intended
            && obligation.aarch64_expr == expected_rewritten
            && obligation.preconditions.is_empty()
            && obligation.fp_inputs.is_empty()
            && obligation.inputs.len() == 1
            && obligation.inputs[0] == ("iv".to_string(), self.width)
    }
}

impl PassValidator for StrengthReduceRecurrenceValidator {
    fn pass_name(&self) -> &str {
        &self.pass_name
    }

    fn target_arch(&self) -> TargetArch {
        TargetArch::X86_64
    }

    fn obligation(&self) -> ProofObligation {
        let iv = SmtExpr::var("iv", self.width);
        // `bv_const` masks to the width, giving the two's-complement carrier
        // image of the literal (e.g. step -1 at width 32 is 0xFFFF_FFFF),
        // which is exactly what an x86 `add`/`imul` immediate sign-extends
        // to at that operand width.
        let step_c = SmtExpr::bv_const(self.step as u64, self.width);
        let stride_c = SmtExpr::bv_const(self.stride as u64, self.width);

        // Intended semantics: the value the DELETED per-iteration multiply
        // would compute on the NEXT iteration, `(iv + step) * s`.
        let intended = iv.clone().bvadd(step_c.clone()).bvmul(stride_c.clone());
        // Rewritten semantics: the recurrence advance the pass emits,
        // `r + u` with `r == iv*s` (induction hypothesis, established by the
        // preheader seed being the same multiply) and `u == s*step` (the
        // preheader `ImulRRI u, s, step`, the reused stride register when
        // step == 1, or the folded `AddRI` immediate `s*step`).
        let rewritten = iv.bvmul(stride_c.clone()).bvadd(stride_c.bvmul(step_c));

        ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: format!(
                "pass[{}]: strength-reduce recurrence (iv + {})*{} == iv*{} + {}*{} at width \
                 {} on x86_64",
                self.pass_name,
                self.step,
                self.stride,
                self.stride,
                self.stride,
                self.step,
                self.width
            ),
            trust_ir_expr: intended,
            aarch64_expr: rewritten,
            inputs: vec![("iv".to_string(), self.width)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(TransvalCheckKind::InstructionLowering),
        }
    }
}

// ---------------------------------------------------------------------------
// Checked-overflow semantic encoders (packed overflow_b1 :: value_iN)
// ---------------------------------------------------------------------------

/// `ite(cond, 1, 0)` as a 1-bit bitvector. Mirrors `checked_overflow_proofs::bv1`.
fn bv1(cond: SmtExpr) -> SmtExpr {
    SmtExpr::ite(cond, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1))
}

/// Pack `overflow :: value` into one bitvector (`overflow` is the high bit),
/// matching `checked_overflow_proofs::pack`.
fn pack(value: SmtExpr, overflow: SmtExpr) -> SmtExpr {
    bv1(overflow).concat(value)
}

/// Signed wide product `sext(lhs) * sext(rhs)` at width `2*width`.
fn signed_product(lhs: SmtExpr, rhs: SmtExpr, width: u32) -> SmtExpr {
    lhs.sign_ext(width).bvmul(rhs.sign_ext(width))
}

/// Spec semantics of a checked operation as `pack(value, overflow)`.
///
/// This is the *reference* contract `overflowing_{add,sub,mul}` must satisfy:
/// the wrapping value, plus an overflow bit that is the exact mathematical
/// overflow (computed at one extra bit for add/sub, at double width for mul).
/// It never divides, so it is identical on every target.
fn spec_checked(op: CheckedOp, lhs: SmtExpr, rhs: SmtExpr, width: u32) -> SmtExpr {
    match op {
        CheckedOp::SignedAdd => {
            let value = lhs.clone().bvadd(rhs.clone());
            let exact = lhs.sign_ext(1).bvadd(rhs.sign_ext(1));
            let wrapped = value.clone().sign_ext(1);
            pack(value, exact.eq_expr(wrapped).not_expr())
        }
        CheckedOp::SignedSub => {
            let value = lhs.clone().bvsub(rhs.clone());
            let exact = lhs.sign_ext(1).bvsub(rhs.sign_ext(1));
            let wrapped = value.clone().sign_ext(1);
            pack(value, exact.eq_expr(wrapped).not_expr())
        }
        CheckedOp::SignedMul => {
            // Exact overflow specified the way `checked_overflow_proofs` does it:
            // the high half of the double-width product must equal the
            // sign-replication of the low half (arithmetic-shift of `value`).
            // This is deliberately a DIFFERENT expression shape from the
            // division-free wide-mul expansion (`product != sext(trunc)`), so the
            // equivalence proof does real work rather than comparing an
            // expression with itself.
            let value = lhs.clone().bvmul(rhs.clone());
            let product = signed_product(lhs, rhs, width);
            let high = product.extract((2 * width) - 1, width);
            let sign = value
                .clone()
                .bvashr(SmtExpr::bv_const((width - 1) as u64, width));
            pack(value, high.eq_expr(sign).not_expr())
        }
    }
}

/// Arch-parameterized semantics of the *expanded instruction sequence*.
///
/// For [`OverflowExpansion::SdivIdentity`] the result depends on `arch`:
/// the expansion contains `result SDIV rhs`, and on a target where IDIV-by-zero
/// traps (x86-64) the sequence is **ill-defined** when `rhs == 0`. We model the
/// trap as a poison sentinel that cannot equal the spec's well-defined packed
/// result, so the equivalence proof yields a counterexample at `rhs == 0` —
/// exactly the #67 SIGFPE input `x.overflowing_mul(0)`.
fn expanded_checked(
    op: CheckedOp,
    expansion: OverflowExpansion,
    arch: TargetArch,
    lhs: SmtExpr,
    rhs: SmtExpr,
    width: u32,
) -> SmtExpr {
    match (op, expansion) {
        // --- Signed add/sub: sign-bit carry check (arch-independent) ---
        (CheckedOp::SignedAdd, OverflowExpansion::SignBitCheck) => {
            let value = lhs.clone().bvadd(rhs.clone());
            let lhs_sign = msb(&lhs, width);
            let rhs_sign = msb(&rhs, width);
            let value_sign = msb(&value, width);
            let overflow = lhs_sign
                .clone()
                .eq_expr(rhs_sign)
                .and_expr(lhs_sign.eq_expr(value_sign).not_expr());
            pack(value, overflow)
        }
        (CheckedOp::SignedSub, OverflowExpansion::SignBitCheck) => {
            let value = lhs.clone().bvsub(rhs.clone());
            let lhs_sign = msb(&lhs, width);
            let rhs_sign = msb(&rhs, width);
            let value_sign = msb(&value, width);
            let overflow = lhs_sign
                .clone()
                .eq_expr(rhs_sign)
                .not_expr()
                .and_expr(lhs_sign.eq_expr(value_sign).not_expr());
            pack(value, overflow)
        }

        // --- Signed mul: the #67 fork ---

        // The #67 FIX: division-free wide multiply. Correct on every target.
        (CheckedOp::SignedMul, OverflowExpansion::DivisionFreeWideMul) => {
            let value = lhs.clone().bvmul(rhs.clone());
            let product = signed_product(lhs, rhs, width);
            let trunc = product.clone().extract(width - 1, 0); // Trunc to narrow
            let roundtrip = trunc.sign_ext(width); // Sextend back
            pack(value, product.eq_expr(roundtrip).not_expr())
        }

        // The #67 BUG: SDIV identity. Models the actual emitted sequence
        // (`translate_overflow`, adapter.rs ~7192-7198):
        //   value    = a * b                              (wrapping)
        //   q        = value IDIV/SDIV b                  (the divided operand is
        //                                                  `value`, NOT `a`)
        //   overflow = (b != 0 AND q != a)
        //              OR (a == INT_MIN AND b == -1)       (flag MIN/-1 case)
        // The `(b != 0)` guard fixes only the *flag value*; the divide itself
        // still executes on `value`. On AArch64 `SDIV` is total (divide-by-zero
        // returns 0, INT_MIN/-1 returns INT_MIN), so the sequence is well
        // defined everywhere. On x86-64 the `IDIV` instruction raises `#DE`
        // (SIGFPE) on TWO inputs — `b == 0` AND `value == INT_MIN && b == -1`
        // (quotient overflow) — so on either of those inputs the program crashes
        // and never produces the spec result. That is miscompile #67
        // (`x.overflowing_mul(0)`, and the quotient-overflow sibling).
        (CheckedOp::SignedMul, OverflowExpansion::SdivIdentity) => {
            let value = lhs.clone().bvmul(rhs.clone());

            let q = value.clone().bvsdiv(rhs.clone());
            let nonzero = rhs.clone().eq_expr(SmtExpr::bv_const(0, width)).not_expr();
            let q_ne_lhs = q.eq_expr(lhs.clone()).not_expr();
            // INT_MIN/-1 special case for the OVERFLOW FLAG (the multiply
            // overflows when a == INT_MIN && b == -1). At narrow widths this
            // input is reachable (e.g. i8 -128 * -1), so the model must include
            // it or the AArch64 identity proof would spuriously fail.
            let int_min = SmtExpr::bv_const(1u64 << (width - 1), width);
            let minus_one = SmtExpr::bv_const(mask_all(width), width);
            let min_neg1 = lhs
                .clone()
                .eq_expr(int_min.clone())
                .and_expr(rhs.clone().eq_expr(minus_one.clone()));
            let identity_overflow = nonzero.clone().and_expr(q_ne_lhs).or_expr(min_neg1);
            let well_defined_result = pack(value.clone(), identity_overflow);

            if arch.idiv_traps() {
                // x86-64: the `IDIV value, b` instruction traps (#DE / SIGFPE) on
                // BOTH undefined inputs:
                //   * b == 0                          (divide by zero), and
                //   * value == INT_MIN && b == -1     (quotient overflow — the
                //     mathematical quotient -INT_MIN is unrepresentable).
                // NOTE the dividend is `value` (the wrapping product a*b), NOT
                // `a`. Model each trapping input with a packed sentinel the spec
                // can never produce there, so the equivalence proof finds a
                // deterministic counterexample at every trapping input (no free
                // variables, no evaluator panic). Both #DE conditions are
                // reachable at narrow widths (e.g. i8: a=1,b=0; or any a,b with
                // a*b = -128 and b = -1, i.e. a=-128,b=-1 -> value=-128).
                let traps = nonzero.clone().not_expr().or_expr(
                    value
                        .clone()
                        .eq_expr(int_min)
                        .and_expr(rhs.clone().eq_expr(minus_one)),
                );
                SmtExpr::ite(traps, trap_sentinel(width), well_defined_result)
            } else {
                // AArch64: SDIV is total (by-zero -> 0, INT_MIN/-1 -> INT_MIN),
                // so the identity is well defined and equals the spec for every
                // input.
                well_defined_result
            }
        }

        // Mismatched op/expansion pairings are validator misuse; surface them as
        // a deterministic sentinel so the proof fails loudly rather than silently
        // certifying nothing meaningful.
        _ => trap_sentinel(width),
    }
}

/// Most-significant (sign) bit of `value` as a 1-bit bitvector.
fn msb(value: &SmtExpr, width: u32) -> SmtExpr {
    value.clone().extract(width - 1, width - 1)
}

/// All-ones mask for a `width`-bit value (`-1` in two's complement).
fn mask_all(width: u32) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

/// A concrete packed `(width+1)`-bit sentinel modelling a trapping / undefined
/// expansion result. It is the all-ones packed value, which differs from the
/// spec's well-defined packed result on the trapping input (`b == 0`, where the
/// spec is the all-zero packed value). Using a constant — not a free symbolic
/// variable — keeps the obligation closed over its declared inputs so the
/// `verify_by_evaluation` evaluator never hits an undefined variable.
fn trap_sentinel(width: u32) -> SmtExpr {
    SmtExpr::bv_const(mask_all(width + 1), width + 1)
}

/// The widest declared input of an obligation, across both bitvector inputs and
/// floating-point inputs (`eb + sb`). Used to decide whether
/// [`verify_by_evaluation`] is a complete proof (width <=
/// [`EXHAUSTIVE_WIDTH_THRESHOLD`]) or merely a statistical sample (width above
/// it, where a formal solver is required for soundness).
fn max_input_width(obligation: &ProofObligation) -> u32 {
    let bv_max = obligation.inputs.iter().map(|(_, w)| *w).max().unwrap_or(0);
    let fp_max = obligation
        .fp_inputs
        .iter()
        .map(|(_, eb, sb)| eb + sb)
        .max()
        .unwrap_or(0);
    bv_max.max(fp_max)
}

// ---------------------------------------------------------------------------
// Certificate request construction
// ---------------------------------------------------------------------------

/// SHA-256 hex digest helper (matches the style in `certified_pass_chain` tests).
fn sha256_hex(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hasher
        .finalize()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// Build the `trust-cg.lean5_pass_check.request.v1` request a verified per-pass
/// validation emits. Its shape mirrors the synthetic certificate built in
/// `certified_pass_chain`'s tests: a verified result, a `must_be_verified`
/// chain marker, a proof artifact + canonical-obligation artifact pair, and the
/// shared obligation hash threaded through request / certificate / report.
fn build_pass_certificate_request(
    pass_name: &str,
    obligation_name: &str,
    arch: TargetArch,
    compilation_unit: &str,
    certificate_index: u64,
) -> Lean5PassCertificateCheckRequest {
    let pass_instance_id = format!("{pass_name}:{}:v1", arch.slug());
    let obligation_hash = format!(
        "trust-cg-pass-transval-v1:{compilation_unit}:{pass_instance_id}:{}",
        sha256_hex(obligation_name.as_bytes())
    );

    let run_record = json!({
        "format_version": "trust-cg.pass.transval_run.v1",
        "pass_name": pass_name,
        "pass_instance_id": pass_instance_id,
        "target": arch.slug(),
        "obligation_name": obligation_name,
        "status": "verified",
        "obligation_hash": obligation_hash,
    });
    let run_record_bytes = serde_json::to_vec(&run_record).expect("run record JSON serializes");
    let run_record_digest = sha256_hex(&run_record_bytes);
    let run_record_uri = format!("trust-cg-verify://pass-transval-run/{run_record_digest}.json");
    let proof_digest =
        sha256_hex(format!("{pass_instance_id}:{obligation_hash}:{run_record_digest}").as_bytes());
    let proof_uri =
        format!("builtin://trust-cg-verify/pass-transval/{pass_instance_id}/placeholder-lean5");

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
            note: "Per-pass translation-validation equivalence discharged by \
                   verify_by_evaluation; transport-checked here, semantic Lean replay \
                   is out of scope for this bounded slice."
                .to_string(),
        }),
    };
    let artifacts = vec![canonical_obligation, proof_artifact];
    let certificate_artifacts =
        serde_json::to_value(&artifacts).expect("artifacts JSON serializes");

    let certificate = json!({
        "format_version": "trust-cg.certified_pass.v1",
        "pass": {
            "name": pass_name,
            "version": "1",
            "implementation_commit": "workspace-local",
            "instance_id": pass_instance_id,
            "pipeline_ordinal": certificate_index + 1,
            "target_profile": {
                "triple": arch.triple(),
                "cpu": "unspecified",
                "features": [],
            },
            "options_hash": format!("sha256:{}", sha256_hex(b"O2")),
        },
        "provenance": {
            "source": {
                "program_id": format!(
                    "trust-cg://{compilation_unit}/before/{pass_instance_id}"
                ),
                "node_ids": [],
                "expression_digest": obligation_hash,
            },
            "rewrite": {
                "program_id": format!(
                    "trust-cg://{compilation_unit}/after/{pass_instance_id}"
                ),
                "node_ids": [],
                "expression_digest": obligation_hash,
            },
        },
        "contract": {
            "mode": "local_pass_certificate_summary",
            "semantic_policy": {
                "source": "trust-cg-verify per-pass translation validation",
                "fail_closed": true,
            },
        },
        "domain": {
            "kind": "machine-ir",
            "certified_pass_run": run_record,
        },
        "obligation_hash": obligation_hash,
        "checker": {
            "kind": "lean5",
            "name": "trust-cg-cert-check",
            "version": "0.1.0",
            "proof_family": "trust-cg-pass-transval-v1",
            "invocation": {
                "mode": "in_process",
                "command": ["trust-cg-verify", "per-pass-translation-validation"],
                "working_directory_policy": "process",
            },
            "limits": {"timeout_ms": 1000},
            "replay_inputs": certificate_artifacts.clone(),
            "trust_base": [
                "lean5-kernel",
                "trust-cg-verify-pass-transval",
                "placeholder-transport-fixture",
            ],
        },
        "result": {
            "status": "verified",
            "checked_at_unix": 0,
            "duration_ms": 0,
            "local_checker": {
                "kind": "trust-cg-verify-pass-transval",
                "name": "verify_by_evaluation",
                "version": "1",
                "status": "verified",
            },
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

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::certified_pass_chain::CertifiedPassChain;

    /// The pass-validator certification-gap probe (crate::formal_gap): a
    /// `Rejected` whose reason is the validator's `fail-closed: solver
    /// unknown ({…})` wrapping is unwrapped and confirmed against the
    /// validator's OWN obligation (same default config as `validate()`), so
    /// a guarded test skips LOUDLY only on the exact fail-closed gap
    /// diagnostics — a counterexample, timeout, error, or any other
    /// rejection still fails the original assertion.
    fn validator_certification_gap(
        obligation: &ProofObligation,
        validation: &PassValidation,
    ) -> Option<String> {
        let PassValidation::Rejected { reason, .. } = validation else {
            return None;
        };
        let inner = reason
            .strip_prefix("fail-closed: solver unknown (")?
            .strip_suffix(')')?;
        let config = AYConfig::default();
        crate::formal_gap::confirmed_certification_gap(
            obligation,
            &config,
            &crate::ay_bridge::AYResult::Unknown(inner.to_string()),
        )
    }

    // -----------------------------------------------------------------------
    // (a) Switch normalization — #62
    // -----------------------------------------------------------------------

    /// LOCKS IN #62: a faithful dense switch normalization (jump table) is
    /// validated and produces a certificate the fail-closed chain accepts.
    #[test]
    fn switch_jump_table_faithful_validates() {
        let cases: Vec<Case> = (0..8).map(|i| (i, 1 + i)).collect();
        let v = SwitchNormalizationValidator::faithful(
            "switch-normalize",
            8,
            cases,
            9,
            SwitchStrategy::JumpTable,
            TargetArch::Aarch64,
        );
        assert!(
            v.validate().is_verified(),
            "faithful jump table must validate"
        );

        let entry = v
            .certify("unit-switch-jt", 0)
            .expect("verified switch normalization must certify");
        let chain = CertifiedPassChain::from_entries(vec![entry])
            .expect("certified switch entry must validate in the fail-closed chain");
        assert_eq!(chain.entries().len(), 1);
        assert_eq!(chain.entries()[0].certificate_index(), Some(0));
    }

    /// LOCKS IN #62: a sparse switch normalized to a binary-search tree, when
    /// faithful, validates.
    #[test]
    fn switch_binary_search_faithful_validates() {
        let cases: Vec<Case> = vec![(5, 1), (20, 2), (42, 3), (77, 4), (100, 5)];
        let v = SwitchNormalizationValidator::faithful(
            "switch-normalize",
            8,
            cases,
            9,
            SwitchStrategy::BinarySearch,
            TargetArch::Aarch64,
        );
        assert!(
            v.validate().is_verified(),
            "faithful binary-search switch must validate"
        );
    }

    /// LOCKS IN #62: a normalization that DROPS a case is rejected — the
    /// scrutinee value of the dropped case now routes to default instead of its
    /// target, so the equivalence proof must find a counterexample.
    #[test]
    fn switch_dropped_case_is_rejected() {
        let source: Vec<Case> = (0..8).map(|i| (i, 1 + i)).collect();
        let mut normalized = source.clone();
        normalized.pop(); // drop case value 7 -> target 8
        let v = SwitchNormalizationValidator {
            pass_name: "switch-normalize".to_string(),
            width: 8,
            source_cases: source,
            default_id: 9,
            normalized_cases: normalized,
            strategy: SwitchStrategy::JumpTable,
            arch: TargetArch::Aarch64,
        };
        assert!(
            !v.validate().is_verified(),
            "dropped switch case must be rejected"
        );
        assert!(
            v.certify("unit", 0).is_err(),
            "a rejected switch normalization must produce no certificate"
        );
    }

    /// LOCKS IN #62: a normalization that DUPLICATES a case with a wrong target
    /// is rejected. The duplicate re-targets the value, diverging from source.
    #[test]
    fn switch_duplicated_case_wrong_target_is_rejected() {
        let source: Vec<Case> = vec![(0, 1), (1, 2), (2, 3), (3, 4)];
        // Duplicate value 2 but pointing at the wrong target (block 99). A
        // jump-table/linear-scan with a conflicting entry diverges from source.
        let normalized: Vec<Case> = vec![(0, 1), (1, 2), (2, 99), (3, 4)];
        let v = SwitchNormalizationValidator {
            pass_name: "switch-normalize".to_string(),
            width: 8,
            source_cases: source,
            default_id: 9,
            normalized_cases: normalized,
            strategy: SwitchStrategy::JumpTable,
            arch: TargetArch::Aarch64,
        };
        assert!(
            !v.validate().is_verified(),
            "re-targeted (duplicated) switch case must be rejected"
        );
    }

    // -----------------------------------------------------------------------
    // (b) Overflow / checked-arith expansion — #67
    // -----------------------------------------------------------------------

    /// LOCKS IN #67: the division-free wide-multiply expansion validates on
    /// BOTH architectures (it never divides). i8 width => exhaustive proof.
    #[test]
    fn overflow_division_free_validates_per_arch() {
        for arch in [TargetArch::Aarch64, TargetArch::X86_64] {
            let v = OverflowExpansionValidator::signed_mul(
                "overflow-expand",
                8,
                OverflowExpansion::DivisionFreeWideMul,
                arch,
            );
            assert!(
                v.validate().is_verified(),
                "division-free wide-mul overflow must validate on {}",
                arch.slug()
            );
            v.certify("unit-ovf", 0).unwrap_or_else(|_| {
                panic!("division-free expansion must certify on {}", arch.slug())
            });
        }
    }

    /// Closes the post-expansion soundness gap for popcnt: the fixed SWAR
    /// shift/mask sequence (`expand_x86_popcnt_inst`) is exhaustively (i8) proven
    /// equivalent to the population count.
    #[test]
    fn popcnt_swar_expansion_validates_exhaustively() {
        let v = PopcntSwarExpansionValidator::x86_generic("popcnt-expand", 8);
        assert!(
            v.validate().is_verified(),
            "the popcount SWAR expansion must validate (SWAR == popcount, exhaustive i8)"
        );
        v.certify("unit-popcnt", 0)
            .expect("popcount SWAR expansion must certify");
    }

    /// Pins the REAL emitted Gpr32 SWAR sequence: at width 8 the reduction-fold
    /// loop (`dst += dst >> {8,16}`) runs zero times, so the exhaustive width-8
    /// proof never exercises the multi-byte folds the shipped 32-bit code uses.
    /// The width-32 model is byte-for-byte `expand_x86_popcnt_inst` (masks
    /// 0x5555_5555/0x3333_3333/0x0f0f_0f0f, folds `>>8`,`>>16`, final mask 0x3f),
    /// so this is a genuine proof of the exact 32-bit instruction stream. The
    /// committed exact-query certificate is independently replayed before AY
    /// resolution, making this a mandatory solver-independent regression gate.
    #[test]
    fn popcnt_swar_32_emitted_width_genuinely_verifies() {
        let v = PopcntSwarExpansionValidator::x86_generic("popcnt-expand", 32);
        let validation = v.validate();
        assert!(
            validation.is_verified(),
            "the emitted Gpr32 popcount SWAR (>>8/>>16 folds) must genuinely verify"
        );
    }

    /// Pins the REAL emitted Gpr64 SWAR sequence — the only path that exercises
    /// the Gpr64-only `>>32` fold and the 0x7f final mask. The proof is genuine but
    /// expensive (the 64-term popcount spec runs ~2 min in AY, past the default
    /// 30 s `validate()` timeout), so the full-proof job opts in with
    /// `TRUST_CG_RUN_FORMAL_PROOF_TESTS=1` and a raised budget rather than
    /// running it per compile.
    #[test]
    fn popcnt_swar_64_emitted_width_genuinely_verifies() {
        if !matches!(
            std::env::var("TRUST_CG_RUN_FORMAL_PROOF_TESTS").as_deref(),
            Ok("1")
        ) {
            eprintln!(
                "formal proof campaign not requested; \
                 set TRUST_CG_RUN_FORMAL_PROOF_TESTS=1 to run"
            );
            return;
        }
        assert!(
            crate::ay_bridge::z3_available(),
            "formal proof campaign requested, but no AY/Z3 solver is available"
        );

        let v = PopcntSwarExpansionValidator::x86_generic("popcnt-expand", 64);
        let obligation = v.obligation();
        let cfg = crate::ay_bridge::AYConfig::default().with_timeout(240_000);
        assert!(
            matches!(
                crate::ay_bridge::verify_with_ay(&obligation, &cfg),
                crate::ay_bridge::AYResult::Verified
            ),
            "the emitted Gpr64 popcount SWAR (>>8/>>16/>>32 folds, final mask 0x7f) must \
             genuinely verify"
        );
    }

    /// The equivalence does REAL work: a corrupted SWAR fold mask (0x54 vs the
    /// correct 0x55) must be REJECTED, so the proof is not vacuous.
    #[test]
    fn popcnt_swar_wrong_mask_is_rejected() {
        let x = SmtExpr::var("x", 8);
        let spec = popcount_spec(x.clone(), 8);
        let broken = popcount_swar(x, 8, 0x54, 0x33, 0x0f, 0x0f);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "popcnt-broken-mask".to_string(),
            trust_ir_expr: spec,
            aarch64_expr: broken,
            inputs: vec![("x".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(TransvalCheckKind::InstructionLowering),
        };
        assert!(
            matches!(
                verify_by_evaluation(&obligation),
                VerificationResult::Invalid { .. }
            ),
            "a wrong SWAR fold mask must be caught (the equivalence is non-vacuous)"
        );
    }

    /// Sentinel-S5 guard-carrier expansions: the CORRECT condition code each
    /// expander emits must verify (i8 exhaustive).
    #[test]
    fn guard_carrier_correct_conds_verify() {
        use GuardCarrierKind::*;
        for (kind, cc) in [
            (Bounds, X86CondCode::AE),
            (ShiftRange, X86CondCode::AE),
            (NullIfZero, X86CondCode::E),
            (DivZero, X86CondCode::E),
        ] {
            assert!(
                GuardCarrierExpansionValidator::new("guard", kind, cc, 8)
                    .validate()
                    .is_verified(),
                "{kind:?} with the emitted cc {cc:?} must verify (i8 exhaustive)"
            );
        }
    }

    /// NON-VACUITY: the COMPLEMENT condition code inverts the guard (traps
    /// in-bounds / on a non-null pointer / on a nonzero divisor) and MUST be
    /// refuted, so the obligation genuinely constrains the cc rather than passing
    /// a degenerate `X == X`.
    #[test]
    fn guard_carrier_inverted_conds_refute() {
        use GuardCarrierKind::*;
        for (kind, bad) in [
            (Bounds, X86CondCode::B),
            (ShiftRange, X86CondCode::B),
            (NullIfZero, X86CondCode::NE),
            (DivZero, X86CondCode::NE),
        ] {
            assert!(
                !GuardCarrierExpansionValidator::new("guard", kind, bad, 8)
                    .validate()
                    .is_verified(),
                "{kind:?} with the inverted cc {bad:?} MUST be refuted (silent guard inversion)"
            );
        }
    }

    /// At the REAL operand widths (i32/i64), require the committed exact-query
    /// certificates to replay without a live solver. These are a single
    /// CMP/TEST-flag + `Jcc` equivalence, not a sampled result.
    #[test]
    fn guard_carrier_real_widths_verify() {
        use GuardCarrierKind::*;
        for w in [32u32, 64] {
            for (kind, cc) in [(Bounds, X86CondCode::AE), (NullIfZero, X86CondCode::E)] {
                let v = GuardCarrierExpansionValidator::new("guard", kind, cc, w);
                let validation = v.validate();
                assert!(
                    validation.is_verified(),
                    "{kind:?}/{cc:?} must verify at i{w}"
                );
            }
        }
    }

    #[test]
    fn wide_validators_use_portable_certs_before_missing_solver_and_mutation_fails_closed() {
        let config = AYConfig {
            solver_path: Some("/definitely/missing/ay".to_string()),
            timeout_ms: crate::verdict_db::DB_VERDICT_TIMEOUT_MS,
            produce_models: true,
        };
        let popcnt = PopcntSwarExpansionValidator::x86_generic("x86-popcnt-expand", 32);
        assert!(
            popcnt.validate_with_config(&config).is_verified(),
            "the expensive popcount cert must also be portable across AY absence"
        );
        let valid = GuardCarrierExpansionValidator::new(
            "x86-guard-carrier-expand",
            GuardCarrierKind::Bounds,
            X86CondCode::AE,
            32,
        );
        assert!(
            valid.validate_with_config(&config).is_verified(),
            "an exact portable cert hit must not require a live AY binary"
        );

        let mutated = GuardCarrierExpansionValidator::new(
            "x86-guard-carrier-expand",
            GuardCarrierKind::Bounds,
            X86CondCode::B,
            32,
        );
        assert!(
            !mutated.validate_with_config(&config).is_verified(),
            "a query mutation must miss the cert and fail closed without AY"
        );
    }

    /// LOCKS IN #67: the SDIV-identity expansion is correct on AArch64
    /// (SDIV-by-zero defined as 0) so it validates there...
    #[test]
    fn overflow_sdiv_identity_validates_on_aarch64() {
        let v = OverflowExpansionValidator::signed_mul(
            "overflow-expand",
            8,
            OverflowExpansion::SdivIdentity,
            TargetArch::Aarch64,
        );
        assert!(
            v.validate().is_verified(),
            "SDIV-identity overflow is correct on AArch64"
        );
    }

    /// LOCKS IN #67 (THE MIS-PORT): the *same* SDIV-identity expansion applied
    /// to x86-64 — where IDIV-by-zero traps — MUST be rejected. This is exactly
    /// the `x.overflowing_mul(0)` SIGFPE from commit 9395663. A verified compile
    /// would have crashed at runtime; the validator refuses to certify it.
    #[test]
    fn overflow_sdiv_identity_aarch64ism_on_x86_is_rejected() {
        let v = OverflowExpansionValidator::signed_mul(
            "overflow-expand",
            8,
            OverflowExpansion::SdivIdentity,
            TargetArch::X86_64,
        );
        assert!(
            !v.validate().is_verified(),
            "SDIV-identity (AArch64-ism) on x86 must be rejected (#67 SIGFPE)"
        );
        assert!(
            v.certify("unit-ovf", 0).is_err(),
            "an AArch64-ism applied to x86 must produce no certificate"
        );
    }

    /// LOCKS IN: a clean two-pass chain (switch normalize @ index 0, overflow
    /// expand @ index 1) certifies end-to-end through the fail-closed chain.
    #[test]
    fn mixed_pass_chain_certifies_end_to_end() {
        let cases: Vec<Case> = (0..8).map(|i| (i, 1 + i)).collect();
        let sw = SwitchNormalizationValidator::faithful(
            "switch-normalize",
            8,
            cases,
            9,
            SwitchStrategy::JumpTable,
            TargetArch::X86_64,
        );
        let ovf = OverflowExpansionValidator::signed_mul(
            "overflow-expand",
            8,
            OverflowExpansion::DivisionFreeWideMul,
            TargetArch::X86_64,
        );

        let e0 = sw.certify("unit-mixed", 0).expect("switch pass certifies");
        let e1 = ovf
            .certify("unit-mixed", 1)
            .expect("overflow pass certifies");
        let chain = CertifiedPassChain::from_entries(vec![e0, e1])
            .expect("two-pass certified chain must validate");
        assert_eq!(chain.entries().len(), 2);
        assert_eq!(chain.compilation_unit(), "unit-mixed");
    }

    /// Anti-tautology: the spec and a deliberately wrong expansion (sign-bit
    /// check applied to multiply) must NOT validate, proving the proof is doing
    /// real work rather than comparing an expression to itself.
    #[test]
    fn overflow_mismatched_expansion_is_rejected() {
        let v = OverflowExpansionValidator {
            pass_name: "overflow-expand".to_string(),
            width: 8,
            op: CheckedOp::SignedMul,
            expansion: OverflowExpansion::SignBitCheck, // wrong for mul
            arch: TargetArch::Aarch64,
        };
        assert!(
            !v.validate().is_verified(),
            "sign-bit check for a multiply must be rejected"
        );
    }

    // -----------------------------------------------------------------------
    // (c) P3d SOUNDNESS regressions
    // -----------------------------------------------------------------------

    /// P3d(4) — x86 IDIV's quotient-overflow trap (`value == INT_MIN && b == -1`)
    /// must be modeled, where `value` is the WRAPPING PRODUCT (a*b), not `a`.
    /// Witness with `b != 0` (so the divide-by-zero trap is NOT the cause): on
    /// i8, a = -128 (0x80), b = -1 (0xFF) gives value = -128*-1 = -128 (0x80) =
    /// INT_MIN, so `IDIV value, -1` raises #DE. The x86 expansion must therefore
    /// produce the trap sentinel (differing from the well-defined spec), while
    /// the AArch64 SDIV expansion stays total and equals the spec.
    #[test]
    fn x86_idiv_quotient_overflow_trap_is_modeled() {
        let width = 8u32;
        let a = SmtExpr::var("a", width);
        let b = SmtExpr::var("b", width);

        let spec = spec_checked(CheckedOp::SignedMul, a.clone(), b.clone(), width);
        let x86 = expanded_checked(
            CheckedOp::SignedMul,
            OverflowExpansion::SdivIdentity,
            TargetArch::X86_64,
            a.clone(),
            b.clone(),
            width,
        );
        let aarch64 = expanded_checked(
            CheckedOp::SignedMul,
            OverflowExpansion::SdivIdentity,
            TargetArch::Aarch64,
            a,
            b,
            width,
        );

        // a = -128 (0x80), b = -1 (0xFF): value = a*b wraps to -128 = INT_MIN,
        // b != 0, so x86 IDIV traps on quotient overflow.
        let mut env = std::collections::HashMap::new();
        env.insert("a".to_string(), 0x80u64);
        env.insert("b".to_string(), 0xFFu64);

        let spec_v = spec.eval(&env);
        let x86_v = x86.eval(&env);
        let aarch64_v = aarch64.eval(&env);

        assert!(
            !spec_v.semantically_equal(&x86_v),
            "x86 IDIV must TRAP (differ from spec) at value=INT_MIN, b=-1; got spec={spec_v:?} x86={x86_v:?}"
        );
        assert!(
            spec_v.semantically_equal(&aarch64_v),
            "AArch64 SDIV is total at INT_MIN/-1 and must equal the spec; got spec={spec_v:?} aarch64={aarch64_v:?}"
        );
    }

    /// P3d(4) end-to-end — the SDIV-identity expansion on x86 is rejected (the
    /// overflow trap, in addition to the divide-by-zero trap, makes it
    /// non-equivalent), while it validates on AArch64.
    #[test]
    fn sdiv_identity_rejected_on_x86_accepted_on_aarch64() {
        let x86 = OverflowExpansionValidator::signed_mul(
            "overflow-expand",
            8,
            OverflowExpansion::SdivIdentity,
            TargetArch::X86_64,
        );
        assert!(
            !x86.validate().is_verified(),
            "SDIV-identity on x86 must be rejected"
        );

        let aarch64 = OverflowExpansionValidator::signed_mul(
            "overflow-expand",
            8,
            OverflowExpansion::SdivIdentity,
            TargetArch::Aarch64,
        );
        assert!(
            aarch64.validate().is_verified(),
            "SDIV-identity on AArch64 must validate"
        );
    }

    /// P3d(5) — a width-32 switch with a DROPPED case must be REJECTED. Above the
    /// exhaustive threshold, `verify_by_evaluation` only SAMPLES, so it could
    /// miss the single dropped scrutinee value (e.g. 0x12345) and return a
    /// statistical "Valid" — minting a certificate for a miscompile. With the
    /// fail-closed fix, a width > 8 obligation either is proven by the formal
    /// solver (which finds the dropped-case counterexample) or, absent a solver,
    /// is rejected outright. Either way: rejected, no certificate.
    #[test]
    fn width32_dropped_switch_case_is_rejected() {
        let source: Vec<Case> = vec![
            (0x00, 1),
            (0x01, 2),
            (0x02, 3),
            (0x12345, 4), // the case that a sampler is unlikely to hit
        ];
        let mut normalized = source.clone();
        normalized.retain(|(v, _)| *v != 0x12345); // DROP the 0x12345 case
        let v = SwitchNormalizationValidator {
            pass_name: "switch-normalize".to_string(),
            width: 32,
            source_cases: source,
            default_id: 9,
            normalized_cases: normalized,
            strategy: SwitchStrategy::BinarySearch,
            arch: TargetArch::X86_64,
        };
        assert!(
            !v.validate().is_verified(),
            "a width-32 dropped switch case must be rejected (fail-closed or solver counterexample)"
        );
        assert!(
            v.certify("unit", 0).is_err(),
            "a rejected width-32 switch must produce no certificate"
        );
    }

    /// P3d(5) — even a FAITHFUL width-32 switch must NOT be certified from a
    /// merely-statistical (sampled) pass when no formal solver is available: a
    /// sample is not a proof. The validator fails closed. (When a solver IS
    /// available it is proven and validates — so this assertion is gated on the
    /// no-solver configuration, which is the soundness-critical one.)
    #[test]
    fn width32_faithful_switch_without_solver_fails_closed() {
        if crate::ay_bridge::z3_available() {
            // A solver is present: the obligation is formally proven; nothing to
            // assert about the fail-closed-without-solver path here.
            return;
        }
        let cases: Vec<Case> = vec![(0x00, 1), (0x01, 2), (0x02, 3), (0x12345, 4)];
        let v = SwitchNormalizationValidator::faithful(
            "switch-normalize",
            32,
            cases,
            9,
            SwitchStrategy::BinarySearch,
            TargetArch::X86_64,
        );
        assert!(
            !v.validate().is_verified(),
            "a width-32 obligation must fail closed without a formal solver (sampling is not a proof)"
        );
    }

    // -----------------------------------------------------------------------
    // (d) Condition-code inversion (OPT-8 branch layout)
    // -----------------------------------------------------------------------

    /// Every hardware inversion pair (`cc` vs `cc.invert()`, encoding bit 0
    /// flipped) is PROVEN complementary over all 32 RFLAGS states — the
    /// obligation the x86 branch-layout admission callback discharges before
    /// any `jcc` is rewritten.
    #[test]
    fn cc_inversion_all_sixteen_pairs_verify() {
        use X86CondCode::*;
        for cc in [O, NO, B, AE, E, NE, BE, A, S, NS, P, NP, L, GE, LE, G] {
            let v = CondCodeInversionValidator::new("x86-branch-layout", cc, cc.invert());
            assert!(
                v.validate().is_verified(),
                "{cc:?} -> {:?} must verify (exhaustive over 32 flag states)",
                cc.invert()
            );
        }
    }

    /// NON-VACUITY / refutation: a WRONG substituted cc must be rejected and
    /// produce no certificate. Covers the identity (no inversion at all), a
    /// near-miss unsigned mix-up (`AE -> BE` instead of `AE -> B`), and a
    /// signed/unsigned confusion (`L -> AE` instead of `L -> GE`) — each is a
    /// silent branch/guard inversion the #3-trap-carriers class describes.
    #[test]
    fn cc_inversion_wrong_substitution_is_rejected() {
        use X86CondCode::*;
        for (original, wrong) in [
            (E, E),   // identity: not a complement
            (AE, BE), // near-miss: BE = CF|ZF, complement of AE is B = CF
            (L, AE),  // signed/unsigned confusion
            (G, GE),  // dropped the ZF conjunct
        ] {
            let v = CondCodeInversionValidator::new("x86-branch-layout", original, wrong);
            assert!(
                !v.validate().is_verified(),
                "{original:?} -> {wrong:?} MUST refute (wrong-cc silent inversion)"
            );
            assert!(
                v.certify("unit-ccinv", 0).is_err(),
                "a refuted inversion must produce no certificate"
            );
        }
    }

    /// SOUNDNESS PIN (found live while building the cc-inversion validator):
    /// `verify_by_evaluation` degrades to random multi-input SAMPLING for 3+
    /// separate inputs regardless of width, and `validate()` previously
    /// credited that sampled `Valid` as an exhaustive proof — the original
    /// wrong `AE -> BE` inversion obligation phrased over five 1-bit flag
    /// inputs "verified" statistically. The strengthened gate must route any
    /// 3+-input obligation to the formal-solver lane (fail closed without a
    /// solver), never the sampled lane. Pinned with a TAUTOLOGY (x == x over
    /// three inputs): sampling would trivially report `Valid`; the gate must
    /// reject it anyway when no solver is present, proving the sampled lane
    /// can no longer mint certificates.
    #[test]
    fn multi_input_obligation_is_never_credited_as_exhaustive() {
        struct ThreeInputTautology;
        impl PassValidator for ThreeInputTautology {
            fn pass_name(&self) -> &str {
                "unit-three-input-tautology"
            }
            fn target_arch(&self) -> TargetArch {
                TargetArch::X86_64
            }
            fn obligation(&self) -> ProofObligation {
                let x = SmtExpr::var("x", 1)
                    .bvxor(SmtExpr::var("y", 1))
                    .bvxor(SmtExpr::var("z", 1));
                ProofObligation {
                    machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
                    name: "unit: three-input tautology (x^y^z == x^y^z)".to_string(),
                    trust_ir_expr: x.clone(),
                    aarch64_expr: x,
                    inputs: vec![
                        ("x".to_string(), 1),
                        ("y".to_string(), 1),
                        ("z".to_string(), 1),
                    ],
                    preconditions: vec![],
                    fp_inputs: vec![],
                    category: Some(TransvalCheckKind::InstructionLowering),
                }
            }
        }

        let outcome = ThreeInputTautology.validate();
        if crate::ay_bridge::z3_available() {
            // With a solver the tautology is formally PROVEN — fine. The
            // assertion of interest is the no-solver fail-closed path below.
            assert!(outcome.is_verified(), "solver present: tautology proves");
        } else {
            assert!(
                !outcome.is_verified(),
                "a 3+-input obligation must fail closed without a solver \
                 (multi-input evaluation is sampling, not a proof)"
            );
        }
    }

    /// The verified inversion mints a `CertifiedPassChainEntry` that the
    /// fail-closed chain accepts — the per-inversion certificate channel the
    /// production admission callback uses.
    #[test]
    fn cc_inversion_certifies_through_the_fail_closed_chain() {
        let v = CondCodeInversionValidator::new(
            "x86-branch-layout",
            X86CondCode::AE,
            X86CondCode::AE.invert(),
        );
        let entry = v
            .certify("unit-ccinv", 0)
            .expect("verified inversion must certify");
        let chain = CertifiedPassChain::from_entries(vec![entry])
            .expect("certified inversion entry must validate in the fail-closed chain");
        assert_eq!(chain.entries().len(), 1);
    }

    /// P3d(6) FALSE-POSITIVE FIX — a faithful normalization of a SIGNED switch
    /// that contains a NEGATIVE case must VALIDATE. Before the fix, the BST model
    /// sorted cases by raw UNSIGNED value while the tree compared with signed
    /// `bvslt`, so the negative case (-1 stored as 0xFF) sorted after the
    /// positives but compared less than them — breaking the partition and
    /// spuriously rejecting a correct lowering. With the signed sort the model is
    /// self-consistent and the faithful switch validates. Exhaustive at width 8.
    #[test]
    fn signed_switch_with_negative_case_validates() {
        // -1 is 0xFF at width 8; the rest are positive signed values.
        let cases: Vec<Case> = vec![(0xFF, 1), (5, 2), (20, 3), (42, 4), (100, 5)];
        let v = SwitchNormalizationValidator::faithful(
            "switch-normalize",
            8,
            cases,
            9,
            SwitchStrategy::BinarySearch,
            TargetArch::Aarch64,
        );
        assert!(
            v.validate().is_verified(),
            "a faithful signed switch with a negative case must validate (no false positive)"
        );
    }

    // -----------------------------------------------------------------------
    // Strength-reduce recurrence validator (x86 OPT-3a)
    // -----------------------------------------------------------------------

    /// The inductive-step identity `(iv + step)*s == iv*s + s*step` validates
    /// EXHAUSTIVELY at width 8 (1 input, width <= threshold => a complete
    /// proof, no solver needed) for representative (step, stride) pairs.
    #[test]
    fn strength_reduce_recurrence_width8_validates_exhaustively() {
        for (step, stride) in [(1i64, 24i64), (2, 8), (3, 24), (-1, 5), (1, -3), (8, 127)] {
            let v = StrengthReduceRecurrenceValidator::new("x86-strength-reduce", 8, step, stride);
            assert!(
                v.validate().is_verified(),
                "recurrence identity must validate exhaustively at width 8, step {step}, \
                 stride {stride}"
            );
            let entry = v
                .certify("unit-strength-reduce", 0)
                .expect("width-8 recurrence obligation must certify");
            let chain = CertifiedPassChain::from_entries(vec![entry])
                .expect("certified recurrence entry must validate in the fail-closed chain");
            assert_eq!(chain.entries().len(), 1);
        }
    }

    /// REFUTATION: the discharge machinery does real work. A WRONG recurrence
    /// advance (`r + step` instead of `r + s*step` — forgetting to scale the
    /// step by the stride) must be REJECTED with a counterexample.
    #[test]
    fn strength_reduce_recurrence_wrong_unscaled_advance_is_refuted() {
        let iv = SmtExpr::var("iv", 8);
        let s = SmtExpr::bv_const(24, 8);
        let step = SmtExpr::bv_const(2, 8);
        let intended = iv.clone().bvadd(step.clone()).bvmul(s.clone());
        // BROKEN: advances the carrier by the raw step, not by s*step.
        let broken = iv.bvmul(s).bvadd(step);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "strength-reduce-broken-unscaled-advance".to_string(),
            trust_ir_expr: intended,
            aarch64_expr: broken,
            inputs: vec![("iv".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(TransvalCheckKind::InstructionLowering),
        };
        assert!(
            matches!(
                verify_by_evaluation(&obligation),
                VerificationResult::Invalid { .. }
            ),
            "the unscaled recurrence advance must be refuted"
        );
    }

    /// REFUTATION: a WRONG step (the pass mis-reading the induction variable's
    /// increment — claiming step 1 while advancing for step 2) must be
    /// REJECTED. Exercised through the validator itself by comparing against
    /// a hand-built intended side with the true step.
    #[test]
    fn strength_reduce_recurrence_wrong_step_is_refuted() {
        let iv = SmtExpr::var("iv", 8);
        let s = SmtExpr::bv_const(24, 8);
        // Intended: the iv really steps by 1.
        let intended = iv.clone().bvadd(SmtExpr::bv_const(1, 8)).bvmul(s.clone());
        // BROKEN: the advance was built for step 2.
        let broken = iv.bvmul(s.clone()).bvadd(s.bvmul(SmtExpr::bv_const(2, 8)));
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "strength-reduce-broken-wrong-step".to_string(),
            trust_ir_expr: intended,
            aarch64_expr: broken,
            inputs: vec![("iv".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(TransvalCheckKind::InstructionLowering),
        };
        assert!(
            matches!(
                verify_by_evaluation(&obligation),
                VerificationResult::Invalid { .. }
            ),
            "a wrong-step recurrence advance must be refuted"
        );
    }

    /// REFUTATION: a WRONG stride (the advance scaled by 23 instead of the
    /// multiply's 24) must be REJECTED.
    #[test]
    fn strength_reduce_recurrence_wrong_stride_is_refuted() {
        let iv = SmtExpr::var("iv", 8);
        let intended = iv
            .clone()
            .bvadd(SmtExpr::bv_const(1, 8))
            .bvmul(SmtExpr::bv_const(24, 8));
        // BROKEN: recurrence built for stride 23.
        let broken = iv
            .bvmul(SmtExpr::bv_const(24, 8))
            .bvadd(SmtExpr::bv_const(23, 8));
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "strength-reduce-broken-wrong-stride".to_string(),
            trust_ir_expr: intended,
            aarch64_expr: broken,
            inputs: vec![("iv".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(TransvalCheckKind::InstructionLowering),
        };
        assert!(
            matches!(
                verify_by_evaluation(&obligation),
                VerificationResult::Invalid { .. }
            ),
            "a wrong-stride recurrence advance must be refuted"
        );
    }

    /// The production width: Gpr64 (width 64) routes to the formal solver
    /// (1 input but above the exhaustive width threshold). This is EXACTLY
    /// the call the pipeline admission gate makes per `(width, step,
    /// stride)`, so it doubles as a compile-time-cost canary: if this stops
    /// verifying (or times out), the pass silently stops firing at that
    /// width — fail-closed, but worth knowing. (The matmul instance is
    /// step 1, stride 24.)
    #[test]
    fn strength_reduce_recurrence_production_width_genuinely_verifies() {
        if !crate::ay_bridge::z3_available() {
            eprintln!("no formal solver; the width-64 recurrence proof requires one — skipping");
            return;
        }
        for (width, step, stride) in [(64u32, 1i64, 24i64), (32, 1, 24), (64, 1, 8)] {
            let started = std::time::Instant::now();
            let v =
                StrengthReduceRecurrenceValidator::new("x86-strength-reduce", width, step, stride);
            let validation = v.validate();
            // Certification-gap guard (crate::formal_gap): skip LOUDLY on the
            // exact fail-closed gap diagnostics only; anything else still
            // fails the original assertion.
            if let Some(reason) = validator_certification_gap(&v.obligation(), &validation) {
                crate::formal_gap::print_gap_skip(
                    &format!(
                        "strength_reduce_recurrence_production_width_genuinely_verifies \
                         width {width} step {step} stride {stride}"
                    ),
                    &reason,
                );
                continue;
            }
            assert!(
                validation.is_verified(),
                "recurrence identity must genuinely verify at width {width}, step {step}, \
                 stride {stride}"
            );
            eprintln!(
                "strength-reduce recurrence width {width} step {step} stride {stride}: \
                 verified in {:?}",
                started.elapsed()
            );
        }
    }

    /// ADMISSION (cited ring axiom, no solver): the ring-recurrence obligation
    /// IS admitted by [`StrengthReduceRecurrenceValidator::certify_by_ring_axiom`]
    /// with NO solve, even at the production widths (32/64, large concrete
    /// strides) where the OLD path bit-blasted for ~11-14s. `certify_by_ring_axiom`
    /// returns a registered `CertifiedPassChainEntry` that passes the
    /// fail-closed chain check — and it never touches the solver, so this test
    /// runs (and passes) with no solver available. These are exactly the
    /// fnv(stride=31)/crc(stride=131) instances.
    #[test]
    fn strength_reduce_recurrence_ring_identity_admitted_by_citation_no_solver() {
        for (width, step, stride) in [
            (32u32, 1i64, 31i64), // fnv_hash
            (32, 1, 131),         // crc32
            (64, 1, 24),          // matmul (was the width-64 solver instance)
            (64, 1, 8),
            (32, 2, 999_983), // a large stride the old BV solve would toil on
        ] {
            let v =
                StrengthReduceRecurrenceValidator::new("x86-strength-reduce", width, step, stride);
            let entry = v
                .certify_by_ring_axiom("unit-strength-reduce-cited", 0)
                .unwrap_or_else(|| {
                    panic!(
                        "the ring-recurrence identity must be admitted by the cited ring \
                         axiom (no solve) at width {width}, step {step}, stride {stride}"
                    )
                });
            let chain = CertifiedPassChain::from_entries(vec![entry]).expect(
                "the citation-discharged recurrence entry must validate in the fail-closed chain",
            );
            assert_eq!(chain.entries().len(), 1);
        }
    }

    /// REFUTATION (the citation is not a free pass): a NON-ring-identity
    /// obligation — a wrong rewrite `iv*stride + step` that DROPPED the
    /// `*stride` on the advance — must NOT be recognized by the cited-lemma
    /// path. The recognition predicate returns `false`, so
    /// `admit_x86_strength_reduce_recurrence` would fall through to the solver
    /// (which refutes it) rather than blindly admit. We also confirm the same
    /// broken advance is genuinely refuted by evaluation, so "not cited" is not
    /// masking an actual equivalence.
    #[test]
    fn strength_reduce_recurrence_non_ring_obligation_not_admitted_by_citation() {
        let width = 32u32;
        let step = 1i64;
        let stride = 31i64;
        let v = StrengthReduceRecurrenceValidator::new("x86-strength-reduce", width, step, stride);

        // Sanity: the validator's OWN (correct) obligation IS recognized.
        assert!(
            v.poses_ring_recurrence_identity(&v.obligation()),
            "the validator's genuine ring-recurrence obligation must be recognized"
        );

        // A BROKEN obligation: rewrite is `iv*stride + step`, dropping `*stride`
        // on the advance (an off-model recurrence that is NOT the ring identity).
        let iv = SmtExpr::var("iv", width);
        let stride_c = SmtExpr::bv_const(stride as u64, width);
        let step_c = SmtExpr::bv_const(step as u64, width);
        let intended = iv.clone().bvadd(step_c.clone()).bvmul(stride_c.clone());
        let broken = iv.bvmul(stride_c).bvadd(step_c); // missing the `* stride`
        let broken_obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "strength-reduce-non-ring-dropped-stride".to_string(),
            trust_ir_expr: intended,
            aarch64_expr: broken,
            inputs: vec![("iv".to_string(), width)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(TransvalCheckKind::InstructionLowering),
        };

        // The citation MUST NOT recognize the broken (non-ring) obligation.
        assert!(
            !v.poses_ring_recurrence_identity(&broken_obligation),
            "a non-ring obligation (dropped *stride) must NOT be admitted by the cited ring axiom"
        );

        // And the broken advance is a genuine miscompile: refuted by evaluation
        // (so the solver fall-through would correctly reject it, not admit).
        assert!(
            matches!(
                verify_by_evaluation(&broken_obligation),
                VerificationResult::Invalid { .. }
            ),
            "the dropped-stride advance must be genuinely refuted, confirming the fall-through \
             solver path would reject it"
        );
    }
}
