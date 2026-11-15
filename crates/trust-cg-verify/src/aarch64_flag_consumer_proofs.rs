// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Per-instruction NZCV producer/consumer obligations for emitted AArch64
//! FCMP, CSET, CSEL, CSINC and CSNEG (X-OPCODES-P3/P5).
//!
//! A conditional select or CSET reads NZCV; its value is determined by its own
//! condition, width, operand registers and arm transform, and by the flags the
//! REACHING producer wrote. The obligations here state that composite for one
//! emitted form at a time:
//!
//! * **FCMP packed NZCV** (per S/D width): the NZCV written by the decoded FCMP
//!   word, computed by an integer-only transcription of the Arm ARM
//!   `FPCompare` table (unordered `0011`, equal `0110`, less `1000`, greater
//!   `0010`) over the raw operand bits, equals the TrustIR IEEE relations
//!   packed as `N = olt, Z = oeq, C = uge, V = uno`. The two sides share no
//!   term: one is sign/magnitude bit arithmetic, the other SMT floating-point
//!   predicates on reinterpreted operands.
//! * **FCMP -> CSET** (per width and condition 0..=13): the decoded CSET word
//!   (`CSINC Rd, ZR, ZR, invert(cc)`) after the decoded FCMP equals the
//!   TrustIR `fcmp` predicate the condition denotes on IEEE operands, for
//!   example `NE` is the UNORDERED `une`, never the ordered `one`.
//! * **Select over a reaching producer** (per CSEL/CSINC/CSNEG, W/X width,
//!   producer kind and width, and condition): the decoded select word,
//!   executed by [`crate::aarch64_csel_semantics`] over the NZCV the producer
//!   writes (`CMP` and `TST` from [`crate::nzcv`], `FCMP` from the model
//!   above), equals the TrustIR `select` of the producer's comparison
//!   predicate, with the CSINC `+ 1` and CSNEG negation of the false arm and
//!   the W-write zeroing of `Xd[63:32]`.
//!
//! Integer CMP/TST -> CSET reuse the existing `Icmp_*` and `TST w*` condition
//! obligations; the function verifier selects them from the reaching producer.
//!
//! The machine side of every new obligation is built from instruction words
//! CAPTURED from the encoder ([`captured_flag_words`]), read by independent
//! decoders written from the Arm ARM encoding tables: the conditional-select
//! decoder in `aarch64_csel_semantics` and [`decode_fp_compare`] below. The
//! trust-cg-verify tests re-derive every captured word from the live encoder.
//!
//! Evidence strength. Registered obligations are discharged by the ordinary
//! evaluator: default acceptance is sampled `Statistical(N)` evidence (the
//! FCMP families route through the checked scalar-FP evaluator, which adds an
//! IEEE edge battery). The coverage-gate credit hook ([`flag_consumer_credit`])
//! additionally evaluates every new form over a deterministic boundary battery
//! (integer boundaries including equal operands, IEEE zeros of both signs,
//! subnormals, infinities and quiet/signaling NaNs), checks every captured word
//! decodes to exactly the instruction it was captured from, and requires every
//! negative control (wrong condition, swapped arms, wrong width, stale flags,
//! wrong arm transform, ordered-vs-unordered IEEE predicates, x86-style
//! unordered flags) to be refuted for its stated reason. None of this is a
//! formal proof or an independently checked certificate.
//!
//! Binding. [`reaching_flag_producer`] walks back from a consumer inside its
//! block and stops at the first NZCV writer; calls, opaque pseudos, control
//! flow, implicit NZCV definitions and the block start refuse. The function
//! verifier credits a consumer only when that producer is a well-formed
//! CMP/TST/FCMP (or, for CSET, a checked-arithmetic producer with its own
//! registered obligation) whose kind, width and the consumer's condition name a
//! registered obligation; anything else stays unverified.
//!
//! What this does NOT establish: that the lowering chose the right producer
//! operands, condition or arms for the SOURCE program (a wrong choice is a
//! correct instance of a different form); FPSR exception flags or FPCR
//! dependence of FCMP; FEAT_FP16 half-precision FCMP; NZCV live across block
//! boundaries; CSINV (not selected by lowering); or agreement with silicon, for
//! which `tests/aarch64_nzcv_silicon_bridge.rs` replays facts recorded natively
//! on Apple silicon.

use std::collections::HashMap;
use std::sync::{LazyLock, Mutex};

use crate::aarch64_csel_semantics::{
    ConditionalSelectOperation, DecodedConditionalSelect, SymbolicRegisterState,
    condition_holds_flags,
};
use crate::lowering_proof::{MachineSideProvenance, ProofObligation};
use crate::nzcv::{NzcvFlags, encode_cmp, encode_tst, pack_nzcv};
use crate::proof_database::ProofCategory;
use crate::smt::{EvalEnv, EvalResult, SmtExpr};
use crate::trust_ir_semantics::{
    encode_trust_ir_binop, encode_trust_ir_bitwise_binop, encode_trust_ir_fcmp,
    encode_trust_ir_icmp, encode_trust_ir_neg,
};
use trust_cg_ir::aarch64_regs::{SP, WSP, preg_class};
use trust_cg_ir::{
    AArch64Opcode, InstId, MachFunction, MachInst, MachOperand, PReg, RegClass, SpecialReg,
};
use trust_cg_lower::instructions::{FloatCC, IntCC, Opcode};
use trust_cg_lower::types::Type;

/// The proof category every obligation of this module is registered under.
pub const FLAG_CONSUMER_CATEGORY: ProofCategory = ProofCategory::Comparison;

// ===========================================================================
// Conditions
// ===========================================================================

/// Condition mnemonics in encoding order (`EQ` = 0 ... `LE` = 13). `AL`/`NV`
/// are not modeled consumer conditions: they do not select on NZCV.
pub const CONDITION_NAMES: [&str; 14] = [
    "eq", "ne", "hs", "lo", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt", "le",
];

fn condition_name(cc: u8) -> Option<&'static str> {
    CONDITION_NAMES.get(usize::from(cc)).copied()
}

/// The TrustIR integer predicate a condition denotes after `CMP a, b`.
/// `MI`/`PL`/`VS`/`VC` test result-sign/overflow bits that no `icmp` names.
fn cmp_predicate(cc: u8) -> Option<IntCC> {
    Some(match cc {
        0 => IntCC::Equal,
        1 => IntCC::NotEqual,
        2 => IntCC::UnsignedGreaterThanOrEqual,
        3 => IntCC::UnsignedLessThan,
        8 => IntCC::UnsignedGreaterThan,
        9 => IntCC::UnsignedLessThanOrEqual,
        10 => IntCC::SignedGreaterThanOrEqual,
        11 => IntCC::SignedLessThan,
        12 => IntCC::SignedGreaterThan,
        13 => IntCC::SignedLessThanOrEqual,
        _ => return None,
    })
}

/// The TrustIR predicate on `a & b` against zero a condition denotes after
/// `TST a, b` (C and V are cleared). The C readers are constant after TST and
/// are refused, as `and_cmp_fuse` refuses them.
fn tst_predicate(cc: u8) -> Option<IntCC> {
    Some(match cc {
        0 => IntCC::Equal,
        1 => IntCC::NotEqual,
        4 | 11 => IntCC::SignedLessThan,
        5 | 10 => IntCC::SignedGreaterThanOrEqual,
        12 => IntCC::SignedGreaterThan,
        13 => IntCC::SignedLessThanOrEqual,
        _ => return None,
    })
}

/// The TrustIR IEEE predicate a condition denotes after `FCMP a, b`, from the
/// FPCompare table: unordered `0011`, equal `0110`, less `1000`, greater
/// `0010`. Conditions true on an unordered result name UNORDERED predicates.
pub fn fcmp_predicate(cc: u8) -> Option<FloatCC> {
    Some(match cc {
        0 => FloatCC::Equal,
        1 => FloatCC::UnorderedNotEqual,
        2 | 5 => FloatCC::UnorderedGreaterThanOrEqual,
        3 | 4 => FloatCC::LessThan,
        6 => FloatCC::Unordered,
        7 => FloatCC::Ordered,
        8 => FloatCC::UnorderedGreaterThan,
        9 => FloatCC::LessThanOrEqual,
        10 => FloatCC::GreaterThanOrEqual,
        11 => FloatCC::UnorderedLessThan,
        12 => FloatCC::GreaterThan,
        13 => FloatCC::UnorderedLessThanOrEqual,
        _ => return None,
    })
}

// ===========================================================================
// Independent FP-compare decoder
// ===========================================================================

/// Fields of an Arm "Floating-point compare" class word:
/// `M 0 S 11110 ftype 1 Rm op(2) 1000 Rn opcode2(5)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DecodedFpCompare {
    /// Operand width in bits: 16 (ftype 11, FEAT_FP16), 32 (00) or 64 (01).
    pub width: u32,
    pub rn: u8,
    pub rm: u8,
    /// `FCMP{E} Vn, #0.0` (opcode2<3> set; Rm must be zero).
    pub against_zero: bool,
    /// `FCMPE` (opcode2<4> set): signals on quiet NaNs too.
    pub signaling: bool,
}

/// Why a word or a form could not be modeled.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum FlagWordRefusal {
    #[error("{0:#010x} is not a floating-point compare word")]
    NotFpCompare(u32),
    #[error("{word:#010x} is unallocated: {reason}")]
    Unallocated { word: u32, reason: &'static str },
    #[error("{0:#010x} is not a conditional-select word")]
    NotConditionalSelect(u32),
    #[error("the word decodes but is not this form: {0}")]
    Shape(String),
    #[error("the form is outside the modeled families: {0}")]
    OutOfModel(String),
}

/// Decode one A64 word of the floating-point compare class.
///
/// Every fixed bit of the class is tested: M = 0, S = 0, bits 28:24 = 11110,
/// bit 21 = 1, op (15:14) = 00, bits 13:10 = 1000 and opcode2<2:0> = 000.
/// `ftype = 10` is unallocated; the compare-with-zero forms require Rm = 0.
pub fn decode_fp_compare(word: u32) -> Result<DecodedFpCompare, FlagWordRefusal> {
    if word & 0xFF20_FC07 != 0x1E20_2000 {
        return Err(FlagWordRefusal::NotFpCompare(word));
    }
    let width = match (word >> 22) & 0b11 {
        0b00 => 32,
        0b01 => 64,
        0b11 => 16,
        _ => {
            return Err(FlagWordRefusal::Unallocated {
                word,
                reason: "FP compare ftype 10",
            });
        }
    };
    let against_zero = (word >> 3) & 1 == 1;
    let rm = ((word >> 16) & 31) as u8;
    if against_zero && rm != 0 {
        return Err(FlagWordRefusal::Unallocated {
            word,
            reason: "compare-with-zero form requires Rm = 0",
        });
    }
    Ok(DecodedFpCompare {
        width,
        rn: ((word >> 5) & 31) as u8,
        rm,
        against_zero,
        signaling: (word >> 4) & 1 == 1,
    })
}

// ===========================================================================
// Integer-only FPCompare
// ===========================================================================

/// The ordered relation of two raw IEEE operands, as Bool terms built only
/// from bit masks, equality and unsigned comparison (no floating-point term).
#[derive(Debug, Clone)]
pub struct FpCompareRelation {
    /// Either operand is a NaN (quiet or signaling).
    pub unordered: SmtExpr,
    /// Equal as numbers (`+0 == -0`); meaningful only when ordered.
    pub equal: SmtExpr,
    /// Strictly less as numbers; meaningful only when ordered.
    pub less: SmtExpr,
}

fn format_masks(width: u32) -> Option<(u64, u64, u64)> {
    // (sign, exponent, fraction)
    match width {
        32 => Some((0x8000_0000, 0x7F80_0000, 0x007F_FFFF)),
        64 => Some((
            0x8000_0000_0000_0000,
            0x7FF0_0000_0000_0000,
            0x000F_FFFF_FFFF_FFFF,
        )),
        _ => None,
    }
}

/// `FPCompare(a, b)` for raw `width`-bit operands (32 or 64), transcribed from
/// the Arm ARM table as integer comparisons on the sign/magnitude encoding.
pub fn fp_compare_relation(
    a_bits: &SmtExpr,
    b_bits: &SmtExpr,
    width: u32,
) -> Result<FpCompareRelation, FlagWordRefusal> {
    let (sign, exponent, fraction) = format_masks(width)
        .ok_or_else(|| FlagWordRefusal::OutOfModel(format!("FP compare width {width}")))?;
    let c = |value: u64| SmtExpr::bv_const(value, width);
    let masked = |x: &SmtExpr, mask: u64| x.clone().bvand(c(mask));
    let is_nan = |x: &SmtExpr| {
        masked(x, exponent)
            .eq_expr(c(exponent))
            .and_expr(masked(x, fraction).eq_expr(c(0)).not_expr())
    };
    let negative = |x: &SmtExpr| masked(x, sign).eq_expr(c(sign));
    let magnitude = |x: &SmtExpr| masked(x, !sign & (exponent | fraction));
    let both_zero = magnitude(a_bits)
        .eq_expr(c(0))
        .and_expr(magnitude(b_bits).eq_expr(c(0)));
    let equal = both_zero
        .clone()
        .or_expr(a_bits.clone().eq_expr(b_bits.clone()));
    let (a_neg, b_neg) = (negative(a_bits), negative(b_bits));
    let less = both_zero.not_expr().and_expr(
        a_neg
            .clone()
            .and_expr(b_neg.clone().not_expr())
            .or_expr(
                a_neg
                    .clone()
                    .not_expr()
                    .and_expr(b_neg.clone().not_expr())
                    .and_expr(magnitude(a_bits).bvult(magnitude(b_bits))),
            )
            .or_expr(
                a_neg
                    .and_expr(b_neg)
                    .and_expr(magnitude(b_bits).bvult(magnitude(a_bits))),
            ),
    );
    Ok(FpCompareRelation {
        unordered: is_nan(a_bits).or_expr(is_nan(b_bits)),
        equal,
        less,
    })
}

impl FpCompareRelation {
    /// The four flags of the FPCompare table as Bool terms.
    pub fn flags(&self) -> NzcvFlags {
        let ordered = self.unordered.clone().not_expr();
        NzcvFlags {
            n: ordered
                .clone()
                .and_expr(self.equal.clone().not_expr())
                .and_expr(self.less.clone()),
            z: ordered.and_expr(self.equal.clone()),
            c: self
                .unordered
                .clone()
                .or_expr(self.equal.clone())
                .or_expr(self.less.clone().not_expr()),
            v: self.unordered.clone(),
        }
    }

    /// The packed 4-bit NZCV in the table's literal shape:
    /// `if unordered then 0011 elif equal then 0110 elif less then 1000 else 0010`.
    pub fn packed(&self) -> SmtExpr {
        let nzcv = |value| SmtExpr::bv_const(value, 4);
        SmtExpr::ite(
            self.unordered.clone(),
            nzcv(0b0011),
            SmtExpr::ite(
                self.equal.clone(),
                nzcv(0b0110),
                SmtExpr::ite(self.less.clone(), nzcv(0b1000), nzcv(0b0010)),
            ),
        )
    }
}

fn fp_format(width: u32) -> Option<(u32, u32, Type)> {
    match width {
        32 => Some((8, 24, Type::F32)),
        64 => Some((11, 53, Type::F64)),
        _ => None,
    }
}

fn int_type(width: u32) -> Option<Type> {
    match width {
        32 => Some(Type::I32),
        64 => Some(Type::I64),
        _ => None,
    }
}

fn bv1_true(predicate: SmtExpr) -> SmtExpr {
    predicate.eq_expr(SmtExpr::bv_const(1, 1))
}

/// The TrustIR `fcmp` predicate (BV1) on the raw operands `a`, `b`.
fn trust_ir_fcmp(cc: FloatCC, a: &SmtExpr, b: &SmtExpr, width: u32) -> Option<SmtExpr> {
    let (eb, sb, ty) = fp_format(width)?;
    Some(encode_trust_ir_fcmp(
        &cc,
        ty,
        SmtExpr::bv_bits_to_fp(a.clone(), eb, sb),
        SmtExpr::bv_bits_to_fp(b.clone(), eb, sb),
    ))
}

/// The TrustIR relations packed as NZCV: `N = olt, Z = oeq, C = uge, V = uno`.
fn trust_ir_packed_relation(a: &SmtExpr, b: &SmtExpr, width: u32) -> Option<SmtExpr> {
    let bit = |cc: FloatCC, value: u64| -> Option<SmtExpr> {
        Some(SmtExpr::ite(
            bv1_true(trust_ir_fcmp(cc, a, b, width)?),
            SmtExpr::bv_const(value, 4),
            SmtExpr::bv_const(0, 4),
        ))
    };
    Some(
        bit(FloatCC::LessThan, 0b1000)?
            .bvor(bit(FloatCC::Equal, 0b0100)?)
            .bvor(bit(FloatCC::UnorderedGreaterThanOrEqual, 0b0010)?)
            .bvor(bit(FloatCC::Unordered, 0b0001)?),
    )
}

// ===========================================================================
// Forms
// ===========================================================================

/// The producer families a consumer is bound to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ProducerKind {
    Cmp,
    Tst,
    Fcmp,
}

/// A producer family at one operand width (32/64; S/D for FCMP).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ProducerForm {
    pub kind: ProducerKind,
    pub width: u32,
}

impl ProducerForm {
    /// Every producer form, in registration order.
    pub const ALL: [Self; 6] = [
        Self::new(ProducerKind::Cmp, 32),
        Self::new(ProducerKind::Cmp, 64),
        Self::new(ProducerKind::Tst, 32),
        Self::new(ProducerKind::Tst, 64),
        Self::new(ProducerKind::Fcmp, 32),
        Self::new(ProducerKind::Fcmp, 64),
    ];

    pub const fn new(kind: ProducerKind, width: u32) -> Self {
        Self { kind, width }
    }

    pub fn label(self) -> &'static str {
        match (self.kind, self.width) {
            (ProducerKind::Cmp, 32) => "cmp w32",
            (ProducerKind::Cmp, _) => "cmp w64",
            (ProducerKind::Tst, 32) => "tst w32",
            (ProducerKind::Tst, _) => "tst w64",
            (ProducerKind::Fcmp, 32) => "fcmp f32",
            (ProducerKind::Fcmp, _) => "fcmp f64",
        }
    }

    /// The consumer conditions with a TrustIR predicate after this producer.
    pub fn conditions(self) -> Vec<u8> {
        (0..14u8).filter(|&cc| self.admits(cc)).collect()
    }

    pub fn admits(self, cc: u8) -> bool {
        match self.kind {
            ProducerKind::Cmp => cmp_predicate(cc).is_some(),
            ProducerKind::Tst => tst_predicate(cc).is_some(),
            ProducerKind::Fcmp => fcmp_predicate(cc).is_some(),
        }
    }

    /// The raw operand variables `(Rn, Rm)` of the canonical producer.
    fn operands(self) -> (SmtExpr, SmtExpr) {
        match self.kind {
            ProducerKind::Cmp | ProducerKind::Tst => (
                SmtExpr::var("pa", self.width),
                SmtExpr::var("pb", self.width),
            ),
            ProducerKind::Fcmp => (
                SmtExpr::var("a_bits", self.width),
                SmtExpr::var("b_bits", self.width),
            ),
        }
    }

    /// Operand variables of an EARLIER producer over different values, for
    /// the stale-flags control.
    fn stale_operands(self) -> (SmtExpr, SmtExpr) {
        match self.kind {
            ProducerKind::Cmp | ProducerKind::Tst => (
                SmtExpr::var("pc", self.width),
                SmtExpr::var("pd", self.width),
            ),
            ProducerKind::Fcmp => (
                SmtExpr::var("c_bits", self.width),
                SmtExpr::var("d_bits", self.width),
            ),
        }
    }

    /// The TrustIR predicate (BV1) the condition denotes on `(lhs, rhs)`.
    fn source_predicate(self, cc: u8, lhs: &SmtExpr, rhs: &SmtExpr) -> Option<SmtExpr> {
        match self.kind {
            ProducerKind::Cmp => Some(encode_trust_ir_icmp(
                &cmp_predicate(cc)?,
                int_type(self.width)?,
                lhs.clone(),
                rhs.clone(),
            )),
            ProducerKind::Tst => {
                let ty = int_type(self.width)?;
                let masked = encode_trust_ir_bitwise_binop(
                    &Opcode::Band,
                    ty.clone(),
                    lhs.clone(),
                    rhs.clone(),
                );
                Some(encode_trust_ir_icmp(
                    &tst_predicate(cc)?,
                    ty,
                    masked,
                    SmtExpr::bv_const(0, self.width),
                ))
            }
            ProducerKind::Fcmp => trust_ir_fcmp(fcmp_predicate(cc)?, lhs, rhs, self.width),
        }
    }

    /// The NZCV the producer writes, from its machine model. FCMP flags come
    /// from the decoded canonical FCMP word (so its operand order and width are
    /// the word's); `operands` substitutes the operand variables.
    fn machine_flags(self, operands: (&SmtExpr, &SmtExpr)) -> Result<NzcvFlags, FlagWordRefusal> {
        Ok(match self.kind {
            ProducerKind::Cmp => encode_cmp(operands.0.clone(), operands.1.clone(), self.width),
            ProducerKind::Tst => encode_tst(operands.0.clone(), operands.1.clone(), self.width),
            ProducerKind::Fcmp => {
                fcmp_word_relation(canonical_fcmp_word(self.width)?, self.width, operands)?.flags()
            }
        })
    }
}

/// The emitted conditional-select operations with registered obligations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum SelectOp {
    Csel,
    Csinc,
    Csneg,
}

impl SelectOp {
    pub const ALL: [Self; 3] = [Self::Csel, Self::Csinc, Self::Csneg];

    pub fn opcode(self) -> AArch64Opcode {
        match self {
            Self::Csel => AArch64Opcode::Csel,
            Self::Csinc => AArch64Opcode::Csinc,
            Self::Csneg => AArch64Opcode::Csneg,
        }
    }

    pub fn of(opcode: AArch64Opcode) -> Option<Self> {
        match opcode {
            AArch64Opcode::Csel => Some(Self::Csel),
            AArch64Opcode::Csinc => Some(Self::Csinc),
            AArch64Opcode::Csneg => Some(Self::Csneg),
            _ => None,
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::Csel => "CSEL",
            Self::Csinc => "CSINC",
            Self::Csneg => "CSNEG",
        }
    }

    fn architectural(self) -> ConditionalSelectOperation {
        match self {
            Self::Csel => ConditionalSelectOperation::Csel,
            Self::Csinc => ConditionalSelectOperation::Csinc,
            Self::Csneg => ConditionalSelectOperation::Csneg,
        }
    }
}

/// One per-instruction select obligation: operation, destination width,
/// reaching producer and condition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SelectForm {
    pub op: SelectOp,
    pub width: u32,
    pub producer: ProducerForm,
    pub cond: u8,
}

impl SelectForm {
    /// Every select form, in registration order.
    pub fn all() -> Vec<Self> {
        let mut forms = Vec::new();
        for op in SelectOp::ALL {
            for width in [32, 64] {
                for producer in ProducerForm::ALL {
                    for cond in producer.conditions() {
                        forms.push(Self {
                            op,
                            width,
                            producer,
                            cond,
                        });
                    }
                }
            }
        }
        forms
    }

    /// Lower-case query token, a unique prefix of [`Self::obligation_name`].
    pub fn query(self) -> &'static str {
        interned(QueryKey::Select(self))
    }

    pub fn obligation_name(self) -> String {
        let width = if self.width == 32 { "W" } else { "X" };
        let cc = condition_name(self.cond).unwrap_or("??");
        let transform = match self.op {
            SelectOp::Csel => "f",
            SelectOp::Csinc => "f + 1",
            SelectOp::Csneg => "-f",
        };
        format!(
            "A64 NZCV {} {width} over {} {cc}: decoded {} word after the reaching {} == TrustIR \
             select({cc} predicate, t, {transform}){}",
            self.op.label(),
            self.producer.label(),
            self.op.label(),
            self.producer.label().to_uppercase(),
            if self.width == 32 {
                ", Xd[63:32] zero"
            } else {
                ""
            }
        )
    }
}

/// Lower-case query token of the FCMP packed-NZCV obligation at `width`.
pub fn fcmp_packed_query(width: u32) -> Option<&'static str> {
    matches!(width, 32 | 64).then(|| interned(QueryKey::FcmpPacked(width)))
}

/// Lower-case query token of the FCMP -> CSET obligation.
pub fn fcmp_cset_query(width: u32, cc: u8) -> Option<&'static str> {
    (matches!(width, 32 | 64) && fcmp_predicate(cc).is_some())
        .then(|| interned(QueryKey::FcmpCset(width, cc)))
}

fn fcmp_packed_name(width: u32) -> String {
    format!(
        "A64 NZCV FCMP f{width} packed: decoded FCMP word NZCV (integer-only FPCompare: \
         unordered 0011, equal 0110, less 1000, greater 0010) == TrustIR relations N=olt Z=oeq \
         C=uge V=uno"
    )
}

fn fcmp_cset_name(width: u32, cc: u8) -> String {
    format!(
        "A64 NZCV FCMP f{width} -> CSET {}: decoded CSET word after the reaching FCMP == TrustIR \
         fcmp {:?}",
        condition_name(cc).unwrap_or("??"),
        fcmp_predicate(cc)
    )
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum QueryKey {
    Select(SelectForm),
    FcmpPacked(u32),
    FcmpCset(u32, u8),
}

fn query_of(key: QueryKey) -> String {
    match key {
        QueryKey::Select(form) => {
            let width = if form.width == 32 { "w" } else { "x" };
            format!(
                "a64 nzcv {} {width} over {} {}:",
                form.op.label().to_lowercase(),
                form.producer.label(),
                condition_name(form.cond).unwrap_or("??")
            )
        }
        QueryKey::FcmpPacked(width) => format!("a64 nzcv fcmp f{width} packed:"),
        QueryKey::FcmpCset(width, cc) => format!(
            "a64 nzcv fcmp f{width} -> cset {}:",
            condition_name(cc).unwrap_or("??")
        ),
    }
}

/// Queries are `&'static str` for the function verifier's lookup. The key
/// space is finite (the registered forms), so each is leaked at most once.
fn interned(key: QueryKey) -> &'static str {
    static TABLE: LazyLock<Mutex<HashMap<QueryKey, &'static str>>> =
        LazyLock::new(|| Mutex::new(HashMap::new()));
    let mut table = TABLE
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    table
        .entry(key)
        .or_insert_with(|| Box::leak(query_of(key).into_boxed_str()))
}

// ===========================================================================
// Captured encoder words
// ===========================================================================

/// `CSEL/CSINC/CSNEG {W,X}0, {W,X}1, {W,X}2, EQ` as the encoder emits them.
const SELECT_BASE_WORDS: [(SelectOp, u32, u32); 6] = [
    (SelectOp::Csel, 32, 0x1A82_0020),
    (SelectOp::Csel, 64, 0x9A82_0020),
    (SelectOp::Csinc, 32, 0x1A82_0420),
    (SelectOp::Csinc, 64, 0x9A82_0420),
    (SelectOp::Csneg, 32, 0x5A82_0420),
    (SelectOp::Csneg, 64, 0xDA82_0420),
];
/// `CSET {W,X}0, EQ` (the `CSINC Rd, ZR, ZR, NE` alias).
const CSET_BASE_WORDS: [(u32, u32); 2] = [(32, 0x1A9F_17E0), (64, 0x9A9F_17E0)];
/// `FCMP S1, S2` and `FCMP D1, D2`.
const FCMP_WORDS: [(u32, u32); 2] = [(32, 0x1E22_2020), (64, 0x1E62_2020)];

/// Replace the 4-bit condition field (bits 15:12) of a conditional-select word.
pub const fn with_condition(word: u32, cond: u8) -> u32 {
    (word & !0xF000) | ((cond as u32 & 0xF) << 12)
}

fn out_of_model(what: String) -> FlagWordRefusal {
    FlagWordRefusal::OutOfModel(what)
}

/// The captured word of `op` at `width` with condition `cond`.
pub fn canonical_select_word(op: SelectOp, width: u32, cond: u8) -> Result<u32, FlagWordRefusal> {
    SELECT_BASE_WORDS
        .iter()
        .find(|(o, w, _)| *o == op && *w == width)
        .map(|(_, _, word)| with_condition(*word, cond))
        .ok_or_else(|| out_of_model(format!("{op:?} width {width}")))
}

/// The captured `CSET {W,X}0, cc` word: its condition field is `cc ^ 1`.
pub fn canonical_cset_word(width: u32, cc: u8) -> Result<u32, FlagWordRefusal> {
    if cc > 13 {
        return Err(out_of_model(format!("CSET condition {cc}")));
    }
    CSET_BASE_WORDS
        .iter()
        .find(|(w, _)| *w == width)
        .map(|(_, word)| with_condition(*word, cc ^ 1))
        .ok_or_else(|| out_of_model(format!("CSET width {width}")))
}

/// The captured `FCMP {S,D}1, {S,D}2` word.
pub fn canonical_fcmp_word(width: u32) -> Result<u32, FlagWordRefusal> {
    FCMP_WORDS
        .iter()
        .find(|(w, _)| *w == width)
        .map(|(_, word)| *word)
        .ok_or_else(|| out_of_model(format!("FCMP width {width}")))
}

/// One captured instruction: the machine-IR operands the encoder was given
/// and the word it produced.
#[derive(Debug, Clone)]
pub struct CapturedFlagWord {
    pub inst: MachInst,
    pub word: u32,
}

fn gpr(width: u32, n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(if width == 32 { 32 + n } else { n }))
}

fn fpr(width: u32, n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(if width == 32 { 128 + n } else { 96 + n }))
}

/// Every captured word the new obligations are built from, with the
/// instruction it was captured from: each select operation at W and X for
/// every condition 0..=13, CSET at W and X for every condition, and FCMP at S
/// and D. `tests/aarch64_flag_consumer_gate.rs` re-encodes every entry with the
/// live encoder and fails on any difference.
pub fn captured_flag_words() -> Vec<CapturedFlagWord> {
    let mut words = Vec::new();
    for op in SelectOp::ALL {
        for width in [32, 64] {
            for cond in 0..14u8 {
                if let Ok(word) = canonical_select_word(op, width, cond) {
                    words.push(CapturedFlagWord {
                        inst: MachInst::new(
                            op.opcode(),
                            vec![
                                gpr(width, 0),
                                gpr(width, 1),
                                gpr(width, 2),
                                MachOperand::Imm(i64::from(cond)),
                            ],
                        ),
                        word,
                    });
                }
            }
        }
    }
    for width in [32, 64] {
        for cond in 0..14u8 {
            if let Ok(word) = canonical_cset_word(width, cond) {
                words.push(CapturedFlagWord {
                    inst: MachInst::new(
                        AArch64Opcode::CSet,
                        vec![gpr(width, 0), MachOperand::Imm(i64::from(cond))],
                    ),
                    word,
                });
            }
        }
    }
    for (width, word) in FCMP_WORDS {
        words.push(CapturedFlagWord {
            inst: MachInst::new(AArch64Opcode::Fcmp, vec![fpr(width, 1), fpr(width, 2)]),
            word,
        });
    }
    words
}

/// Check that a captured word decodes, with the independent decoders, to
/// exactly the instruction it was captured from.
pub fn check_captured_flag_word(entry: &CapturedFlagWord) -> Result<(), FlagWordRefusal> {
    let shape = |what: String| Err(FlagWordRefusal::Shape(what));
    let reg = |index: usize| -> Option<(u32, u8)> {
        match entry.inst.operands.get(index)? {
            MachOperand::PReg(p) => {
                let width = preg_class(*p).size_bits();
                Some((width, p.hw_enc()))
            }
            _ => None,
        }
    };
    let imm = |index: usize| match entry.inst.operands.get(index) {
        Some(MachOperand::Imm(value)) => u8::try_from(*value).ok(),
        _ => None,
    };
    match entry.inst.opcode {
        AArch64Opcode::Fcmp => {
            let decoded = decode_fp_compare(entry.word)?;
            let (Some((wn, rn)), Some((wm, rm))) = (reg(0), reg(1)) else {
                return shape("FCMP operands".into());
            };
            if (decoded.width, decoded.rn, decoded.rm) != (wn, rn, rm)
                || wn != wm
                || decoded.against_zero
                || decoded.signaling
            {
                return shape(format!("FCMP word decodes as {decoded:?}"));
            }
            Ok(())
        }
        AArch64Opcode::CSet => {
            let decoded = DecodedConditionalSelect::decode(entry.word)
                .map_err(|_| FlagWordRefusal::NotConditionalSelect(entry.word))?;
            let (Some((width, rd)), Some(cc)) = (reg(0), imm(1)) else {
                return shape("CSET operands".into());
            };
            if decoded.operation() != ConditionalSelectOperation::Csinc
                || decoded.registers() != (rd, 31, 31)
                || decoded.width().bits() != width
                || cc > 13
                || decoded.condition() != cc ^ 1
            {
                return shape(format!("CSET word decodes as {decoded:?}"));
            }
            Ok(())
        }
        opcode => {
            let op = SelectOp::of(opcode)
                .ok_or_else(|| FlagWordRefusal::Shape(format!("{opcode:?} is not captured")))?;
            let decoded = DecodedConditionalSelect::decode(entry.word)
                .map_err(|_| FlagWordRefusal::NotConditionalSelect(entry.word))?;
            let (Some((width, rd)), Some((wn, rn)), Some((wm, rm)), Some(cc)) =
                (reg(0), reg(1), reg(2), imm(3))
            else {
                return shape("select operands".into());
            };
            if decoded.operation() != op.architectural()
                || decoded.registers() != (rd, rn, rm)
                || decoded.width().bits() != width
                || wn != width
                || wm != width
                || decoded.condition() != cc
            {
                return shape(format!("{op:?} word decodes as {decoded:?}"));
            }
            Ok(())
        }
    }
}

// ===========================================================================
// Machine sides from decoded words
// ===========================================================================

/// The relation a decoded FCMP word computes. Registers 1 and 2 are the
/// canonical operand registers and carry `operands.0` / `operands.1`; any other
/// register is outside the model. The compare-with-zero form compares against
/// `+0.0`. FCMPE and half precision are refused.
fn fcmp_word_relation(
    word: u32,
    width: u32,
    operands: (&SmtExpr, &SmtExpr),
) -> Result<FpCompareRelation, FlagWordRefusal> {
    let decoded = decode_fp_compare(word)?;
    if decoded.signaling {
        return Err(FlagWordRefusal::Shape(
            "FCMPE is not the emitted FCMP".into(),
        ));
    }
    if decoded.width != width {
        return Err(FlagWordRefusal::Shape(format!(
            "the word compares {}-bit operands, the form {width}-bit",
            decoded.width
        )));
    }
    let register = |n: u8| match n {
        1 => Ok(operands.0.clone()),
        2 => Ok(operands.1.clone()),
        other => Err(FlagWordRefusal::Shape(format!(
            "register {other} is outside the canonical operand map"
        ))),
    };
    let lhs = register(decoded.rn)?;
    let rhs = if decoded.against_zero {
        SmtExpr::bv_const(0, width)
    } else {
        register(decoded.rm)?
    };
    fp_compare_relation(&lhs, &rhs, width)
}

/// The architectural value of `X0` after the decoded select word executes
/// with `X1 = xn`, `X2 = xm` and the given packed NZCV. Every other register
/// is its own variable, so a word writing a different register leaves `X0`
/// unconstrained and refutes.
fn select_word_value(word: u32, nzcv: SmtExpr) -> Result<SmtExpr, FlagWordRefusal> {
    let decoded = DecodedConditionalSelect::decode(word)
        .map_err(|_| FlagWordRefusal::NotConditionalSelect(word))?;
    let registers = std::array::from_fn(|index| match index {
        1 => SmtExpr::var("xn", 64),
        2 => SmtExpr::var("xm", 64),
        other => SmtExpr::var(format!("x{other}"), 64),
    });
    let state = SymbolicRegisterState::from_parts(registers, SmtExpr::var("sp", 64), nzcv)
        .map_err(|error| FlagWordRefusal::OutOfModel(error.to_string()))?;
    let after = decoded.execute_symbolic(&state);
    after
        .register(0)
        .cloned()
        .ok_or_else(|| FlagWordRefusal::OutOfModel("X0 absent from the state".into()))
}

/// Every variable of `expr` with its width, in first-occurrence order.
fn collect_vars(expr: &SmtExpr, out: &mut Vec<(String, u32)>) {
    if let SmtExpr::Var { name, width } = expr {
        if !out.iter().any(|(existing, _)| existing == name) {
            out.push((name.clone(), *width));
        }
        return;
    }
    expr.for_each_child(&mut |child| collect_vars(child, out));
}

fn obligation(name: String, source: SmtExpr, machine: SmtExpr) -> ProofObligation {
    let mut inputs = Vec::new();
    collect_vars(&source, &mut inputs);
    collect_vars(&machine, &mut inputs);
    ProofObligation {
        machine_side_provenance: MachineSideProvenance::StaticDb,
        name,
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs,
        preconditions: Vec::new(),
        fp_inputs: Vec::new(),
        category: Some(FLAG_CONSUMER_CATEGORY.transval_check_kind()),
    }
}

// ===========================================================================
// Obligations
// ===========================================================================

/// A deliberately wrong statement, used as a negative control.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FlagMutation {
    /// Build the obligation from this word instead of the canonical one.
    Word(u32),
    /// Take the consumer's NZCV from an earlier producer over other operands.
    StaleFlags,
    /// CSINC claimed without its `+ 1` / CSNEG claimed as bitwise NOT (CSINV).
    WrongArmTransform,
    /// FCMP modeled with x86 UCOMIS unordered flags (`Z = C = 1`, V clear).
    X86UnorderedFlags,
    /// FCMP modeled with bitwise equality, so `+0 != -0`.
    BitwiseEquality,
    /// FCMP modeled with `C = ordered and not less` (C clear when unordered).
    OrderedCarry,
    /// FCMP -> CSET claimed as this TrustIR predicate instead.
    ClaimedPredicate(FloatCC),
}

/// The registered FCMP packed-NZCV obligation at `width`.
pub fn fcmp_packed_obligation(width: u32) -> Result<ProofObligation, FlagWordRefusal> {
    fcmp_packed_obligation_with(width, None)
}

fn fcmp_packed_obligation_with(
    width: u32,
    mutation: Option<FlagMutation>,
) -> Result<ProofObligation, FlagWordRefusal> {
    let (a, b) = ProducerForm::new(ProducerKind::Fcmp, width).operands();
    let word = match mutation {
        Some(FlagMutation::Word(word)) => word,
        _ => canonical_fcmp_word(width)?,
    };
    let relation = fcmp_word_relation(word, width, (&a, &b))?;
    let machine = match mutation {
        None | Some(FlagMutation::Word(_)) => relation.packed(),
        Some(FlagMutation::X86UnorderedFlags) => {
            let nzcv = |value| SmtExpr::bv_const(value, 4);
            // x86 UCOMIS reports unordered as ZF = PF = CF = 1: equal-and-carry.
            SmtExpr::ite(relation.unordered.clone(), nzcv(0b0110), relation.packed())
        }
        Some(FlagMutation::BitwiseEquality) => FpCompareRelation {
            equal: a.clone().eq_expr(b.clone()),
            ..relation
        }
        .packed(),
        Some(FlagMutation::OrderedCarry) => {
            let nzcv = |value| SmtExpr::bv_const(value, 4);
            SmtExpr::ite(relation.unordered.clone(), nzcv(0b0001), relation.packed())
        }
        Some(other) => {
            return Err(out_of_model(format!(
                "{other:?} does not apply to FCMP packed NZCV"
            )));
        }
    };
    let source = trust_ir_packed_relation(&a, &b, width)
        .ok_or_else(|| out_of_model(format!("FCMP width {width}")))?;
    Ok(obligation(fcmp_packed_name(width), source, machine))
}

/// The registered FCMP -> CSET obligation.
pub fn fcmp_cset_obligation(width: u32, cc: u8) -> Result<ProofObligation, FlagWordRefusal> {
    fcmp_cset_obligation_with(width, cc, None)
}

fn fcmp_cset_obligation_with(
    width: u32,
    cc: u8,
    mutation: Option<FlagMutation>,
) -> Result<ProofObligation, FlagWordRefusal> {
    let predicate =
        fcmp_predicate(cc).ok_or_else(|| out_of_model(format!("FCMP condition {cc}")))?;
    let (a, b) = ProducerForm::new(ProducerKind::Fcmp, width).operands();
    let word = match mutation {
        Some(FlagMutation::Word(word)) => word,
        _ => canonical_cset_word(64, cc)?,
    };
    let decoded = DecodedConditionalSelect::decode(word)
        .map_err(|_| FlagWordRefusal::NotConditionalSelect(word))?;
    if decoded.operation() != ConditionalSelectOperation::Csinc
        || decoded.registers().1 != 31
        || decoded.registers().2 != 31
    {
        return Err(FlagWordRefusal::Shape(format!(
            "{decoded:?} is not the CSET alias CSINC Rd, ZR, ZR"
        )));
    }
    let relation = fcmp_word_relation(canonical_fcmp_word(width)?, width, (&a, &b))?;
    let holds = condition_holds_flags(decoded.condition(), &relation.flags())
        .map_err(|error| out_of_model(error.to_string()))?;
    // CSINC Rd, ZR, ZR, c: Rd = c ? 0 : 0 + 1, the 0/1 carrier.
    let machine = SmtExpr::ite(holds, SmtExpr::bv_const(0, 1), SmtExpr::bv_const(1, 1));
    let claimed = match mutation {
        Some(FlagMutation::ClaimedPredicate(claimed)) => claimed,
        None | Some(FlagMutation::Word(_)) => predicate,
        Some(other) => {
            return Err(out_of_model(format!(
                "{other:?} does not apply to FCMP -> CSET"
            )));
        }
    };
    let source = trust_ir_fcmp(claimed, &a, &b, width)
        .ok_or_else(|| out_of_model(format!("FCMP width {width}")))?;
    Ok(obligation(fcmp_cset_name(width, cc), source, machine))
}

/// The registered select-over-producer obligation.
pub fn select_obligation(form: SelectForm) -> Result<ProofObligation, FlagWordRefusal> {
    select_obligation_with(form, None)
}

fn select_obligation_with(
    form: SelectForm,
    mutation: Option<FlagMutation>,
) -> Result<ProofObligation, FlagWordRefusal> {
    let producer = form.producer;
    if !producer.admits(form.cond) {
        return Err(out_of_model(format!(
            "condition {} after {}",
            form.cond,
            producer.label()
        )));
    }
    match mutation {
        None | Some(FlagMutation::Word(_) | FlagMutation::StaleFlags) => {}
        Some(FlagMutation::WrongArmTransform) if form.op != SelectOp::Csel => {}
        Some(other) => {
            return Err(out_of_model(format!(
                "{other:?} does not apply to {:?}",
                form.op
            )));
        }
    }
    let (lhs, rhs) = producer.operands();
    let flags = if mutation == Some(FlagMutation::StaleFlags) {
        let (stale_lhs, stale_rhs) = producer.stale_operands();
        producer.machine_flags((&stale_lhs, &stale_rhs))?
    } else {
        producer.machine_flags((&lhs, &rhs))?
    };
    let word = match mutation {
        Some(FlagMutation::Word(word)) => word,
        _ => canonical_select_word(form.op, form.width, form.cond)?,
    };
    let machine = select_word_value(word, pack_nzcv(&flags))?;

    let ty = int_type(form.width).ok_or_else(|| out_of_model(format!("width {}", form.width)))?;
    let predicate = producer
        .source_predicate(form.cond, &lhs, &rhs)
        .ok_or_else(|| out_of_model(format!("{} predicate", producer.label())))?;
    let arm = |name: &str| {
        let value = SmtExpr::var(name, 64);
        if form.width == 32 {
            value.extract(31, 0)
        } else {
            value
        }
    };
    let (t, f) = (arm("xn"), arm("xm"));
    let one = SmtExpr::bv_const(1, form.width);
    let wrong_transform = mutation == Some(FlagMutation::WrongArmTransform);
    let false_arm = match (form.op, wrong_transform) {
        (SelectOp::Csel, _) => f,
        (SelectOp::Csinc, false) => encode_trust_ir_binop(&Opcode::Iadd, ty, f, one),
        (SelectOp::Csinc, true) => f,
        (SelectOp::Csneg, false) => encode_trust_ir_neg(ty, f),
        (SelectOp::Csneg, true) => f.bvxor(SmtExpr::bv_const(
            crate::smt::mask(u64::MAX, form.width),
            form.width,
        )),
    };
    let selected = SmtExpr::ite(bv1_true(predicate), t, false_arm);
    let source = if form.width == 32 {
        selected.zero_ext(32)
    } else {
        selected
    };
    Ok(obligation(form.obligation_name(), source, machine))
}

/// Every registered obligation of this module, in registration order: the two
/// FCMP packed-NZCV obligations, the FCMP -> CSET family, then the select
/// forms. Registered last in `ProofCategory::Comparison`, so no older
/// first-contains query (`"cmp"`, `"icmp_*"`) resolves differently.
pub fn all_flag_consumer_proofs() -> Vec<(ProofCategory, ProofObligation)> {
    let mut proofs = Vec::new();
    for width in [32, 64] {
        if let Ok(ob) = fcmp_packed_obligation(width) {
            proofs.push((FLAG_CONSUMER_CATEGORY, ob));
        }
    }
    for width in [32, 64] {
        for cc in 0..14u8 {
            if let Ok(ob) = fcmp_cset_obligation(width, cc) {
                proofs.push((FLAG_CONSUMER_CATEGORY, ob));
            }
        }
    }
    for form in SelectForm::all() {
        if let Ok(ob) = select_obligation(form) {
            proofs.push((FLAG_CONSUMER_CATEGORY, ob));
        }
    }
    proofs
}

// ===========================================================================
// Boundary battery
// ===========================================================================

const F32_EDGES: [u64; 22] = [
    0x0000_0000,
    0x8000_0000,
    0x0000_0001,
    0x8000_0001,
    0x007f_ffff,
    0x807f_ffff,
    0x0080_0000,
    0x8080_0000,
    0x3f80_0000,
    0xbf80_0000,
    0x3f80_0001,
    0x4000_0000,
    0x7f7f_ffff,
    0xff7f_ffff,
    0x7f80_0000,
    0xff80_0000,
    0x7fc0_0000,
    0xffc0_0000,
    0x7fc1_2345,
    0x7f81_2345,
    0xff81_2346,
    0x7fbf_ffff,
];
const F64_EDGES: [u64; 22] = [
    0x0000_0000_0000_0000,
    0x8000_0000_0000_0000,
    0x0000_0000_0000_0001,
    0x8000_0000_0000_0001,
    0x000f_ffff_ffff_ffff,
    0x800f_ffff_ffff_ffff,
    0x0010_0000_0000_0000,
    0x8010_0000_0000_0000,
    0x3ff0_0000_0000_0000,
    0xbff0_0000_0000_0000,
    0x3ff0_0000_0000_0001,
    0x4000_0000_0000_0000,
    0x7fef_ffff_ffff_ffff,
    0xffef_ffff_ffff_ffff,
    0x7ff0_0000_0000_0000,
    0xfff0_0000_0000_0000,
    0x7ff8_0000_0000_0000,
    0xfff8_0000_0000_0000,
    0x7ff8_1234_5678_9abc,
    0x7ff0_1234_5678_9abc,
    0xfff0_1234_5678_9abd,
    0x7ff7_ffff_ffff_ffff,
];

fn integer_edges(width: u32) -> Vec<u64> {
    let mask = crate::smt::mask(u64::MAX, width);
    let msb = 1u64 << (width - 1);
    let mut values = vec![
        0,
        1,
        2,
        0x7f,
        0x80,
        0xff,
        msb - 1,
        msb,
        msb + 1,
        mask - 1,
        mask,
        0x5555_5555_5555_5555 & mask,
        0xaaaa_aaaa_aaaa_aaaa & mask,
    ];
    if width == 64 {
        values.extend([0xffff_ffff, 0x1_0000_0000]);
    }
    values
}

/// Arm register values `(xn, xm)`: distinct payloads, the CSINC wrap and the
/// CSNEG minimum, and nonzero upper halves observable through W forms.
const ARM_PAIRS: [(u64, u64); 3] = [
    (0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210),
    (0, u64::MAX),
    (0x8000_0000_0000_0000, 0x7fff_ffff_ffff_ffff),
];

fn edge_values(name: &str, width: u32) -> Vec<u64> {
    match name {
        "a_bits" | "b_bits" | "c_bits" | "d_bits" => match width {
            32 => F32_EDGES.to_vec(),
            64 => F64_EDGES.to_vec(),
            _ => vec![0],
        },
        "pa" | "pb" | "pc" | "pd" => integer_edges(width),
        _ => vec![0xa5a5_5a5a_c3c3_3c3c & crate::smt::mask(u64::MAX, width)],
    }
}

/// Outcome of evaluating an obligation over the boundary battery.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BatteryOutcome {
    /// Every battery point agreed; the count of points evaluated.
    Agreed(u64),
    /// A point where the two sides differ.
    Counterexample(String),
}

/// Evaluate `ob` over the deterministic boundary battery: every pair of
/// producer operands from the integer/IEEE edge lists (the cross product
/// includes equal operands, both zeros, both infinities and NaN pairs), each
/// with every [`ARM_PAIRS`] entry for the select arms. Other inputs take a
/// fixed sentinel. An evaluation error is an `Err`, never an agreement.
pub fn battery_check(ob: &ProofObligation) -> Result<BatteryOutcome, String> {
    let producers: Vec<&(String, u32)> = ob
        .inputs
        .iter()
        .filter(|(name, _)| {
            matches!(
                name.as_str(),
                "a_bits" | "b_bits" | "c_bits" | "d_bits" | "pa" | "pb" | "pc" | "pd"
            )
        })
        .collect();
    let has_arms = ob
        .inputs
        .iter()
        .any(|(name, _)| name == "xn" || name == "xm");
    let mut env = EvalEnv::default();
    for (name, width) in &ob.inputs {
        env.insert(name.clone(), edge_values(name, *width)[0]);
    }
    let lists: Vec<Vec<u64>> = producers
        .iter()
        .map(|(name, width)| edge_values(name, *width))
        .collect();
    let arm_pairs: &[(u64, u64)] = if has_arms { &ARM_PAIRS } else { &[(0, 0)] };
    let mut index = vec![0usize; lists.len()];
    let mut points = 0u64;
    loop {
        for (slot, (name, _)) in producers.iter().enumerate() {
            env.insert(name.clone(), lists[slot][index[slot]]);
        }
        for &(xn, xm) in arm_pairs {
            if has_arms {
                env.insert("xn".to_string(), xn);
                env.insert("xm".to_string(), xm);
            }
            let source = ob
                .trust_ir_expr
                .try_eval(&env)
                .map_err(|error| format!("{}: source evaluation failed: {error:?}", ob.name))?;
            let machine = ob
                .aarch64_expr
                .try_eval(&env)
                .map_err(|error| format!("{}: machine evaluation failed: {error:?}", ob.name))?;
            points += 1;
            let agree = match (&source, &machine) {
                (EvalResult::Bv(s), EvalResult::Bv(m)) => s == m,
                (EvalResult::Bool(s), EvalResult::Bool(m)) => s == m,
                _ => {
                    return Err(format!(
                        "{}: unexpected results {source:?} / {machine:?}",
                        ob.name
                    ));
                }
            };
            if !agree {
                let assignment: Vec<String> = ob
                    .inputs
                    .iter()
                    .map(|(name, _)| format!("{name}={:#x}", env.get(name).copied().unwrap_or(0)))
                    .collect();
                return Ok(BatteryOutcome::Counterexample(format!(
                    "{}: source {source:?} != machine {machine:?} at {}",
                    ob.name,
                    assignment.join(", ")
                )));
            }
        }
        // Mixed-radix increment over the producer operand lists.
        let mut slot = 0;
        loop {
            if slot == lists.len() {
                return Ok(BatteryOutcome::Agreed(points));
            }
            index[slot] += 1;
            if index[slot] < lists[slot].len() {
                break;
            }
            index[slot] = 0;
            slot += 1;
        }
    }
}

// ===========================================================================
// Negative controls and the coverage-gate credit hook
// ===========================================================================

/// What a negative control must be refused for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ControlExpectation {
    /// The obligation builds and the battery finds a counterexample.
    Counterexample,
    /// The independent decoders or the form check refuse to build it.
    Refused,
}

/// The obligation family a control mutates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ControlTarget {
    Select(SelectForm),
    FcmpPacked(u32),
    FcmpCset(u32, u8),
}

/// One negative control.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FlagControl {
    pub opcode: AArch64Opcode,
    pub label: String,
    pub target: ControlTarget,
    pub mutation: FlagMutation,
    pub expected: ControlExpectation,
}

/// Set bits `hi:lo` of `word` to `value`.
const fn set_field(word: u32, hi: u32, lo: u32, value: u32) -> u32 {
    let mask = (u32::MAX >> (31 - (hi - lo))) << lo;
    (word & !mask) | ((value << lo) & mask)
}

/// Representative condition per producer for select controls: asymmetric for
/// CMP, sign-reading for TST, NaN-sensitive for FCMP.
fn control_condition(producer: ProducerForm) -> u8 {
    match producer.kind {
        ProducerKind::Cmp => 11,  // LT
        ProducerKind::Tst => 1,   // NE
        ProducerKind::Fcmp => 10, // GE (ordered)
    }
}

/// The negative-control battery. Every select opcode has, for each width and
/// producer form, a wrong-condition, swapped-arm, wrong-width, stale-flags and
/// wrong-operation control, plus an arm-transform control for CSINC/CSNEG and
/// an always-true condition control. FCMP has x86-unordered, signed-zero,
/// unordered-carry, swapped-operand, compare-with-zero, FCMPE, wrong-precision,
/// half-precision and unallocated-type controls. FCMP -> CSET has the
/// ordered-vs-unordered predicate confusions (plain NE claimed as ordered
/// `one`, GE claimed as `uge`, LT claimed as `olt`) and CSET words with an
/// uninverted condition or a live source register.
pub fn flag_controls() -> Vec<FlagControl> {
    use ControlExpectation::{Counterexample, Refused};
    use FlagMutation::{
        BitwiseEquality, ClaimedPredicate, OrderedCarry, StaleFlags, WrongArmTransform,
        X86UnorderedFlags,
    };
    let mut controls = Vec::new();
    for op in SelectOp::ALL {
        for width in [32, 64] {
            for producer in ProducerForm::ALL {
                let cond = control_condition(producer);
                let form = SelectForm {
                    op,
                    width,
                    producer,
                    cond,
                };
                let Ok(word) = canonical_select_word(op, width, cond) else {
                    continue;
                };
                let mut push = |label: &str, mutation, expected| {
                    controls.push(FlagControl {
                        opcode: op.opcode(),
                        label: format!("{} {label}", form.query()),
                        target: ControlTarget::Select(form),
                        mutation,
                        expected,
                    });
                };
                push(
                    "wrong condition (complement)",
                    FlagMutation::Word(with_condition(word, cond ^ 1)),
                    Counterexample,
                );
                push(
                    "swapped arms (Rn <-> Rm)",
                    FlagMutation::Word(set_field(set_field(word, 20, 16, 1), 9, 5, 2)),
                    Counterexample,
                );
                push(
                    "wrong width (sf flipped)",
                    FlagMutation::Word(word ^ (1 << 31)),
                    Counterexample,
                );
                push(
                    "stale flags from an earlier producer",
                    StaleFlags,
                    Counterexample,
                );
                push(
                    "always-true condition (AL)",
                    FlagMutation::Word(with_condition(word, 14)),
                    Counterexample,
                );
                push(
                    "wrong destination (Rd = X3)",
                    FlagMutation::Word(set_field(word, 4, 0, 3)),
                    Counterexample,
                );
                let other = match op {
                    SelectOp::Csel => word | (1 << 10),   // CSINC
                    SelectOp::Csinc => word & !(1 << 10), // CSEL
                    SelectOp::Csneg => word & !(1 << 10), // CSINV
                };
                push("wrong operation", FlagMutation::Word(other), Counterexample);
                if op != SelectOp::Csel {
                    push(
                        "wrong false-arm transform",
                        WrongArmTransform,
                        Counterexample,
                    );
                }
            }
        }
    }
    for width in [32, 64] {
        let Ok(word) = canonical_fcmp_word(width) else {
            continue;
        };
        let mut push = |label: &str, mutation, expected| {
            controls.push(FlagControl {
                opcode: AArch64Opcode::Fcmp,
                label: format!("fcmp f{width} {label}"),
                target: ControlTarget::FcmpPacked(width),
                mutation,
                expected,
            });
        };
        push(
            "x86 UCOMIS unordered flags",
            X86UnorderedFlags,
            Counterexample,
        );
        push(
            "bitwise equality (+0 != -0)",
            BitwiseEquality,
            Counterexample,
        );
        push("carry clear when unordered", OrderedCarry, Counterexample);
        push(
            "swapped operands (FCMP Rm, Rn)",
            FlagMutation::Word(set_field(set_field(word, 20, 16, 1), 9, 5, 2)),
            Counterexample,
        );
        push(
            "compare with #0.0",
            FlagMutation::Word(set_field(set_field(word, 20, 16, 0), 4, 3, 0b01)),
            Counterexample,
        );
        push(
            "FCMPE word",
            FlagMutation::Word(set_field(word, 4, 3, 0b10)),
            Refused,
        );
        push(
            "other precision",
            FlagMutation::Word(set_field(
                word,
                23,
                22,
                if width == 32 { 0b01 } else { 0b00 },
            )),
            Refused,
        );
        push(
            "half precision (FEAT_FP16)",
            FlagMutation::Word(set_field(word, 23, 22, 0b11)),
            Refused,
        );
        push(
            "unallocated ftype 10",
            FlagMutation::Word(set_field(word, 23, 22, 0b10)),
            Refused,
        );
    }
    for width in [32, 64] {
        let mut push = |cc: u8, label: &str, mutation, expected| {
            controls.push(FlagControl {
                opcode: AArch64Opcode::CSet,
                label: format!(
                    "fcmp f{width} -> cset {} {label}",
                    CONDITION_NAMES[usize::from(cc)]
                ),
                target: ControlTarget::FcmpCset(width, cc),
                mutation,
                expected,
            });
        };
        push(
            1,
            "claimed as ordered one",
            ClaimedPredicate(FloatCC::NotEqual),
            Counterexample,
        );
        push(
            10,
            "claimed as uge",
            ClaimedPredicate(FloatCC::UnorderedGreaterThanOrEqual),
            Counterexample,
        );
        push(
            11,
            "claimed as olt",
            ClaimedPredicate(FloatCC::LessThan),
            Counterexample,
        );
        push(
            13,
            "claimed as ole",
            ClaimedPredicate(FloatCC::LessThanOrEqual),
            Counterexample,
        );
        for cc in [0u8, 10] {
            if let Ok(word) = canonical_cset_word(64, cc) {
                push(
                    cc,
                    "uninverted condition field",
                    FlagMutation::Word(with_condition(word, cc)),
                    Counterexample,
                );
                push(
                    cc,
                    "live source register (CSINC X0, X1, XZR)",
                    FlagMutation::Word(set_field(word, 9, 5, 1)),
                    Refused,
                );
            }
        }
    }
    controls
}

fn build_control(control: &FlagControl) -> Result<ProofObligation, FlagWordRefusal> {
    match control.target {
        ControlTarget::Select(form) => select_obligation_with(form, Some(control.mutation)),
        ControlTarget::FcmpPacked(width) => {
            fcmp_packed_obligation_with(width, Some(control.mutation))
        }
        ControlTarget::FcmpCset(width, cc) => {
            fcmp_cset_obligation_with(width, cc, Some(control.mutation))
        }
    }
}

/// Run one control: `Ok(())` when it is refused for its stated reason.
pub fn run_control(control: &FlagControl) -> Result<(), String> {
    match (build_control(control), control.expected) {
        (Err(_), ControlExpectation::Refused) => Ok(()),
        (Ok(ob), ControlExpectation::Counterexample) => match battery_check(&ob)? {
            BatteryOutcome::Counterexample(_) => Ok(()),
            BatteryOutcome::Agreed(points) => Err(format!(
                "control `{}` survived {points} battery points",
                control.label
            )),
        },
        (Ok(_), ControlExpectation::Refused) => Err(format!(
            "control `{}` must be refused but built an obligation",
            control.label
        )),
        (Err(error), ControlExpectation::Counterexample) => Err(format!(
            "control `{}` must build and refute but was refused: {error}",
            control.label
        )),
    }
}

/// One form an opcode row demands: a query and its category. `built` is the
/// obligation this module registers under that query, `None` for a form whose
/// obligation belongs to another module (the integer CMP/TST/checked CSET
/// families).
#[derive(Debug, Clone)]
pub struct FlagForm {
    pub query: &'static str,
    pub category: ProofCategory,
    pub built: Option<ProofObligation>,
}

/// The existing integer-producer CSET obligations, as `(query, category)`:
/// `Icmp_<cc>_I<w>` after CMP, `TST w<w>: <cc>` after TST and the checked
/// ADDS/SUBS (i64) and ADCS/SBCS (i128) overflow-bit idioms.
pub const INTEGER_CSET_QUERIES: &[(&str, ProofCategory)] = &[
    ("icmp_eq_i32", ProofCategory::Comparison),
    ("icmp_ne_i32", ProofCategory::Comparison),
    ("icmp_uge_i32", ProofCategory::Comparison),
    ("icmp_ult_i32", ProofCategory::Comparison),
    ("icmp_ugt_i32", ProofCategory::Comparison),
    ("icmp_ule_i32", ProofCategory::Comparison),
    ("icmp_sge_i32", ProofCategory::Comparison),
    ("icmp_slt_i32", ProofCategory::Comparison),
    ("icmp_sgt_i32", ProofCategory::Comparison),
    ("icmp_sle_i32", ProofCategory::Comparison),
    ("icmp_eq_i64", ProofCategory::Comparison),
    ("icmp_ne_i64", ProofCategory::Comparison),
    ("icmp_uge_i64", ProofCategory::Comparison),
    ("icmp_ult_i64", ProofCategory::Comparison),
    ("icmp_ugt_i64", ProofCategory::Comparison),
    ("icmp_ule_i64", ProofCategory::Comparison),
    ("icmp_sge_i64", ProofCategory::Comparison),
    ("icmp_slt_i64", ProofCategory::Comparison),
    ("icmp_sgt_i64", ProofCategory::Comparison),
    ("icmp_sle_i64", ProofCategory::Comparison),
    ("tst w32: eq", ProofCategory::CmpCombine),
    ("tst w32: ne", ProofCategory::CmpCombine),
    ("tst w32: mi", ProofCategory::CmpCombine),
    ("tst w32: pl", ProofCategory::CmpCombine),
    ("tst w32: ge", ProofCategory::CmpCombine),
    ("tst w32: lt", ProofCategory::CmpCombine),
    ("tst w32: gt", ProofCategory::CmpCombine),
    ("tst w32: le", ProofCategory::CmpCombine),
    ("tst w64: eq", ProofCategory::CmpCombine),
    ("tst w64: ne", ProofCategory::CmpCombine),
    ("tst w64: mi", ProofCategory::CmpCombine),
    ("tst w64: pl", ProofCategory::CmpCombine),
    ("tst w64: ge", ProofCategory::CmpCombine),
    ("tst w64: lt", ProofCategory::CmpCombine),
    ("tst w64: gt", ProofCategory::CmpCombine),
    ("tst w64: le", ProofCategory::CmpCombine),
    ("checkedsadd_i64", ProofCategory::Arithmetic),
    ("checkeduadd_i64", ProofCategory::Arithmetic),
    ("checkedssub_i64", ProofCategory::Arithmetic),
    ("checkedusub_i64", ProofCategory::Arithmetic),
    ("checkedsadd_i128 overflow bit", ProofCategory::Arithmetic),
    ("checkeduadd_i128 overflow bit", ProofCategory::Arithmetic),
    ("checkedssub_i128 overflow bit", ProofCategory::Arithmetic),
    ("checkedusub_i128 overflow bit", ProofCategory::Arithmetic),
];

/// The forms the coverage gate demands for `opcode`, or `None` when the
/// opcode is not credited by this module.
pub fn flag_consumer_forms(opcode: AArch64Opcode) -> Option<Vec<FlagForm>> {
    let own = |query: &'static str, built: Result<ProofObligation, FlagWordRefusal>| FlagForm {
        query,
        category: FLAG_CONSUMER_CATEGORY,
        built: built.ok(),
    };
    Some(match opcode {
        AArch64Opcode::Fcmp => [32, 64]
            .into_iter()
            .filter_map(|width| {
                Some(own(
                    fcmp_packed_query(width)?,
                    fcmp_packed_obligation(width),
                ))
            })
            .collect(),
        AArch64Opcode::CSet => {
            let mut forms: Vec<FlagForm> = INTEGER_CSET_QUERIES
                .iter()
                .map(|&(query, category)| FlagForm {
                    query,
                    category,
                    built: None,
                })
                .collect();
            for width in [32, 64] {
                for cc in 0..14u8 {
                    if let Some(query) = fcmp_cset_query(width, cc) {
                        forms.push(own(query, fcmp_cset_obligation(width, cc)));
                    }
                }
            }
            forms
        }
        opcode => {
            let op = SelectOp::of(opcode)?;
            SelectForm::all()
                .into_iter()
                .filter(|form| form.op == op)
                .map(|form| own(form.query(), select_obligation(form)))
                .collect()
        }
    })
}

/// What the credit hook established for one opcode.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FlagConsumerCredit {
    pub opcode: AArch64Opcode,
    /// Forms of this module demanded for the opcode (built and battery-checked).
    pub own_forms: usize,
    /// Integer-producer forms owned by other modules (discharged by the gate).
    pub borrowed_forms: usize,
    /// Battery points evaluated over the own forms.
    pub battery_points: u64,
    /// Captured words decoded back to their instruction.
    pub captured_words: usize,
    /// Negative controls refuted for their stated reason.
    pub controls_refuted: usize,
}

/// The coverage-gate credit hook. Refuses unless every own form builds, is not
/// a structural identity and agrees on the whole boundary battery, every
/// captured word of the opcode decodes to exactly its instruction, the opcode
/// has at least one control, and EVERY control of the opcode is refuted for its
/// stated reason. The gate separately discharges every form's registered
/// obligation. Deterministic, so the result is cached per opcode.
pub fn flag_consumer_credit(opcode: AArch64Opcode) -> Result<FlagConsumerCredit, String> {
    static CACHE: LazyLock<Mutex<HashMap<AArch64Opcode, Result<FlagConsumerCredit, String>>>> =
        LazyLock::new(|| Mutex::new(HashMap::new()));
    if let Some(hit) = CACHE
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .get(&opcode)
    {
        return hit.clone();
    }
    let result = flag_consumer_credit_with(opcode, &captured_flag_words(), &flag_controls());
    CACHE
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .insert(opcode, result.clone());
    result
}

/// [`flag_consumer_credit`] over an injected corpus and control battery, so a
/// test can hand the hook a stale word or a surviving control and watch it
/// refuse. Not cached.
pub fn flag_consumer_credit_with(
    opcode: AArch64Opcode,
    corpus: &[CapturedFlagWord],
    controls: &[FlagControl],
) -> Result<FlagConsumerCredit, String> {
    use rayon::prelude::*;
    let forms = flag_consumer_forms(opcode)
        .ok_or_else(|| format!("{opcode:?} is not a flag-consumer opcode"))?;
    let own: Vec<&FlagForm> = forms
        .iter()
        .filter(|form| {
            form.category == FLAG_CONSUMER_CATEGORY && form.query.starts_with("a64 nzcv")
        })
        .collect();
    let outcomes: Vec<Result<u64, String>> = own
        .par_iter()
        .map(|form| {
            let ob = form
                .built
                .as_ref()
                .ok_or_else(|| format!("{}: the obligation could not be built", form.query))?;
            if ob.is_degenerate() {
                return Err(format!("{}: structural identity", form.query));
            }
            if !ob.name.to_lowercase().starts_with(form.query) {
                return Err(format!("{}: query is not the name's prefix", form.query));
            }
            match battery_check(ob)? {
                BatteryOutcome::Agreed(points) => Ok(points),
                BatteryOutcome::Counterexample(detail) => Err(detail),
            }
        })
        .collect();
    let mut battery_points = 0;
    for outcome in outcomes {
        battery_points += outcome?;
    }
    let mut captured_words = 0;
    for entry in corpus.iter().filter(|entry| entry.inst.opcode == opcode) {
        check_captured_flag_word(entry).map_err(|error| {
            format!("captured {:?} = {:#010x}: {error}", entry.inst, entry.word)
        })?;
        captured_words += 1;
    }
    if captured_words == 0 {
        return Err(format!("{opcode:?} has no captured word"));
    }
    let own_controls: Vec<&FlagControl> = controls
        .iter()
        .filter(|control| control.opcode == opcode)
        .collect();
    if own_controls.is_empty() {
        return Err(format!("{opcode:?} has no negative control"));
    }
    let refusals: Vec<Result<(), String>> =
        own_controls.par_iter().map(|c| run_control(c)).collect();
    for refusal in refusals {
        refusal?;
    }
    Ok(FlagConsumerCredit {
        opcode,
        own_forms: own.len(),
        borrowed_forms: forms.len() - own.len(),
        battery_points,
        captured_words,
        controls_refuted: own_controls.len(),
    })
}

// ===========================================================================
// Function-verifier binding
// ===========================================================================

/// Width of a general-purpose register operand that may be read (ZR allowed,
/// SP/WSP refused): `(width, is_zero_register)`.
pub fn gpr_operand(op: &MachOperand) -> Option<(u32, bool)> {
    match op {
        MachOperand::VReg(v) => match v.class {
            RegClass::Gpr32 => Some((32, false)),
            RegClass::Gpr64 => Some((64, false)),
            _ => None,
        },
        MachOperand::PReg(p) if *p == SP || *p == WSP => None,
        MachOperand::PReg(p) => match (preg_class(*p), p.encoding()) {
            (RegClass::Gpr32, 161) => Some((32, true)),
            (RegClass::Gpr64, 160) => Some((64, true)),
            (RegClass::Gpr32, _) => Some((32, false)),
            (RegClass::Gpr64, _) => Some((64, false)),
            _ => None,
        },
        MachOperand::Special(SpecialReg::WZR) => Some((32, true)),
        MachOperand::Special(SpecialReg::XZR) => Some((64, true)),
        _ => None,
    }
}

/// Width of a scalar S/D floating-point register operand.
pub fn fpr_operand(op: &MachOperand) -> Option<u32> {
    let class = match op {
        MachOperand::VReg(v) => v.class,
        MachOperand::PReg(p) => preg_class(*p),
        _ => return None,
    };
    match class {
        RegClass::Fpr32 => Some(32),
        RegClass::Fpr64 => Some(64),
        _ => None,
    }
}

/// The width of a well-formed `FCMP {S,D}n, {S,D}m` (both operands the same
/// S or D register class). Half precision, mixed widths, immediates and any
/// other arity refuse.
pub fn fcmp_width(inst: &MachInst) -> Option<u32> {
    if inst.opcode != AArch64Opcode::Fcmp {
        return None;
    }
    let [a, b] = inst.operands.as_slice() else {
        return None;
    };
    let width = fpr_operand(a)?;
    (fpr_operand(b)? == width).then_some(width)
}

/// The query binding a concrete FCMP to its width's packed-NZCV obligation.
pub fn fcmp_query(inst: &MachInst) -> Option<(&'static str, ProofCategory)> {
    fcmp_packed_query(fcmp_width(inst)?).map(|query| (query, FLAG_CONSUMER_CATEGORY))
}

/// The width of a well-formed `CMP Rn, Rm` / `CMP Rn, #imm12`.
pub fn cmp_width(inst: &MachInst) -> Option<u32> {
    match (inst.opcode, inst.operands.as_slice()) {
        (AArch64Opcode::CmpRR, [a, b]) => {
            let (width, _) = gpr_operand(a)?;
            (gpr_operand(b)?.0 == width).then_some(width)
        }
        (AArch64Opcode::CmpRI, [a, MachOperand::Imm(imm)]) => {
            // Rn = 31 in the immediate form is SP, never the zero register.
            let (width, zero) = gpr_operand(a)?;
            (!zero && (0..=0xFFF).contains(imm)).then_some(width)
        }
        _ => None,
    }
}

/// The width of a well-formed `TST Rn, Rm` / `TST Rn, #bitmask`.
pub fn tst_width(inst: &MachInst) -> Option<u32> {
    if inst.opcode != AArch64Opcode::Tst {
        return None;
    }
    let [a, b] = inst.operands.as_slice() else {
        return None;
    };
    let (width, _) = gpr_operand(a)?;
    match b {
        MachOperand::Imm(mask)
            if trust_cg_opt::const_materialize::is_logical_immediate(*mask as u64, width) =>
        {
            Some(width)
        }
        other => (gpr_operand(other)?.0 == width).then_some(width),
    }
}

/// Which instructions a producer walk may pass over.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransparencyPolicy {
    /// Any instruction the AArch64 target model says does not write NZCV,
    /// except calls, opaque pseudos, control flow and anything naming NZCV as
    /// an implicit definition or operand.
    TargetFlagModel,
    /// Only the scalar-body instructions of the source-bound affine domain.
    SourceBoundScalarBody,
}

/// Why no reaching producer was found.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ProducerRefusal {
    #[error("the consumer position is outside the block")]
    OutOfBlock,
    #[error("a dangling instruction reference")]
    Dangling,
    #[error("no NZCV writer precedes the consumer in its block")]
    BlockStart,
    #[error("{0:?} may change NZCV without being a modeled producer")]
    Opaque(AArch64Opcode),
}

fn names_nzcv(inst: &MachInst) -> bool {
    use trust_cg_ir::aarch64_regs::NZCV;
    inst.implicit_defs.contains(&NZCV)
        || inst
            .operands
            .iter()
            .any(|op| matches!(op, MachOperand::PReg(p) if *p == NZCV))
}

fn transparent(inst: &MachInst, policy: TransparencyPolicy) -> bool {
    use AArch64Opcode as M;
    use trust_cg_ir::InstFlags;
    use trust_cg_ir::target_info::{AArch64Target, TargetInfo};
    match policy {
        TransparencyPolicy::TargetFlagModel => {
            // Control transfer is judged from BOTH the instance flags and the
            // opcode's declared flags: an instance whose flags were rebuilt
            // without IS_CALL (a `BL` carried through a pass that set explicit
            // flags) still clobbers NZCV and must not look transparent.
            let declared = inst.opcode.default_flags();
            let control = [
                InstFlags::IS_CALL,
                InstFlags::IS_BRANCH,
                InstFlags::IS_RETURN,
                InstFlags::IS_TERMINATOR,
            ]
            .into_iter()
            .any(|flag| declared.contains(flag) || inst.flags.contains(flag));
            !<AArch64Target as TargetInfo>::writes_flags(inst.opcode)
                && !control
                && !(inst.opcode.is_pseudo() && inst.opcode != M::Nop)
                && !names_nzcv(inst)
        }
        TransparencyPolicy::SourceBoundScalarBody => matches!(
            inst.opcode,
            M::Nop
                | M::MOVWrr
                | M::MOVXrr
                | M::MovR
                | M::Movz
                | M::Movn
                | M::Movk
                | M::AddRR
                | M::SubRR
                | M::AddRI
                | M::AddRIShift12
                | M::SubRI
                | M::CSet
                | M::Csel
                | M::Csinc
                | M::Csinv
                | M::Csneg
        ),
    }
}

/// The instruction whose NZCV reaches the consumer at `consumer_pos`, with its
/// block position: the nearest preceding NZCV writer, provided every
/// instruction in between is transparent under `policy`. Fails closed at the
/// block start (flags from a predecessor are not bound here) and at anything
/// opaque.
pub fn reaching_flag_producer<'a>(
    func: &'a MachFunction,
    block_insts: &[InstId],
    consumer_pos: usize,
    policy: TransparencyPolicy,
) -> Result<(usize, &'a MachInst), ProducerRefusal> {
    use trust_cg_ir::target_info::{AArch64Target, TargetInfo};
    if consumer_pos >= block_insts.len() {
        return Err(ProducerRefusal::OutOfBlock);
    }
    for pos in (0..consumer_pos).rev() {
        let inst = func
            .insts
            .get(block_insts[pos].0 as usize)
            .ok_or(ProducerRefusal::Dangling)?;
        if <AArch64Target as TargetInfo>::writes_flags(inst.opcode) {
            return Ok((pos, inst));
        }
        if !transparent(inst, policy) {
            return Err(ProducerRefusal::Opaque(inst.opcode));
        }
    }
    Err(ProducerRefusal::BlockStart)
}

/// The modeled producer form of a well-formed producer instruction.
pub fn producer_form(inst: &MachInst) -> Option<ProducerForm> {
    match inst.opcode {
        AArch64Opcode::CmpRR | AArch64Opcode::CmpRI => {
            Some(ProducerForm::new(ProducerKind::Cmp, cmp_width(inst)?))
        }
        AArch64Opcode::Tst => Some(ProducerForm::new(ProducerKind::Tst, tst_width(inst)?)),
        AArch64Opcode::Fcmp => Some(ProducerForm::new(ProducerKind::Fcmp, fcmp_width(inst)?)),
        _ => None,
    }
}

/// The destination width and condition of a well-formed consumer:
/// `CSET Rd, cc` or `CSEL/CSINC/CSNEG Rd, Rn, Rm, cc` with same-width
/// general registers, a real destination (not ZR or SP) and a condition in
/// 0..=13. AL/NV and malformed shapes refuse.
pub fn consumer_shape(inst: &MachInst) -> Option<(u32, u8)> {
    let condition = |op: &MachOperand| match op {
        MachOperand::Imm(cc) if (0..=13).contains(cc) => Some(*cc as u8),
        _ => None,
    };
    let destination = |op: &MachOperand| match gpr_operand(op)? {
        (width, false) => Some(width),
        (_, true) => None,
    };
    match (inst.opcode, inst.operands.as_slice()) {
        (AArch64Opcode::CSet, [rd, cc]) => Some((destination(rd)?, condition(cc)?)),
        (AArch64Opcode::Csel | AArch64Opcode::Csinc | AArch64Opcode::Csneg, [rd, rn, rm, cc]) => {
            let width = destination(rd)?;
            (gpr_operand(rn)?.0 == width && gpr_operand(rm)?.0 == width)
                .then_some((width, condition(cc)?))
        }
        _ => None,
    }
}

/// The query binding a concrete CSEL/CSINC/CSNEG to the select obligation of
/// its own operation, width and condition over its reaching producer's kind
/// and width. Anything unbound refuses.
pub fn select_query(
    func: &MachFunction,
    block_insts: &[InstId],
    pos: usize,
) -> Option<(&'static str, ProofCategory)> {
    let inst = func.insts.get(block_insts.get(pos)?.0 as usize)?;
    let op = SelectOp::of(inst.opcode)?;
    let (width, cond) = consumer_shape(inst)?;
    let (_, producer) =
        reaching_flag_producer(func, block_insts, pos, TransparencyPolicy::TargetFlagModel).ok()?;
    let producer = producer_form(producer)?;
    producer.admits(cond).then(|| {
        (
            SelectForm {
                op,
                width,
                producer,
                cond,
            }
            .query(),
            FLAG_CONSUMER_CATEGORY,
        )
    })
}

#[cfg(test)]
#[path = "aarch64_flag_consumer_proofs_tests.rs"]
mod tests;
