// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//
// Reference: Arm DDI 0487 (L.a), C6.2 SUBS (immediate), shared pseudocode
//            `AddWithCarry`; C4.1 "Add/subtract (immediate)".

//! Decoded-word value and flag obligations for the emitted `SUBS #imm`
//! (`SubsRI`; ledger `L04-P1`).
//!
//! # What is emitted
//!
//! The looped stack probe of a frame of five or more 4 KiB pages
//! (`trust-cg-codegen` `frame.rs`) decrements its counter with
//! `SUBS X16, X16, #1` and branches back on `B.NE`. The encoder admits
//! `SUBS Rd, Rn|SP, #imm12` at both widths (`sh = 0`).
//!
//! # The obligation
//!
//! For one instruction, every location its WORD writes — the destination
//! register (all 64 bits; a W write clears bits 63:32) and the four NZCV
//! flags — equals what the machine-IR instruction names, for every register
//! value:
//!
//! * the word is re-derived from the operands by this module's encoder
//!   ([`subs_imm_word`]), and per compile ENC-5 requires the emitted word to
//!   be exactly that word ([`check_emitted_subs_imm_word`]);
//! * the word is decoded by an independent field decoder of the
//!   "Add/subtract (immediate)" class ([`decode_add_sub_imm_word`]) and given
//!   its Arm ARM pseudocode for ALL four of ADD/ADDS/SUB/SUBS
//!   ([`denote_add_sub_imm`]): `imm = ZeroExtend(imm12 << (sh ? 12 : 0))`,
//!   `AddWithCarry(X[n]|SP, NOT(imm), 1)` for a subtraction with its
//!   `UInt`/`SInt` sums one bit wider than the operands, `C` set when the
//!   unsigned sum does not fit, `V` when the signed sum does not, and NZCV
//!   written only when `S = 1`; register 31 is SP as the source and the zero
//!   register as a flag-setting destination;
//! * the intent ([`subs_imm_intent`]) is stated from the operands as the
//!   comparison the flags encode: the difference `Rn - imm`, `N` its sign,
//!   `Z` its zero test, `C` the unsigned comparison `Rn >= imm`, `V` the
//!   signed overflow of a subtraction of a non-negative immediate
//!   (`Rn < 0` and the difference `>= 0`).
//!
//! # How it is decided, and what that is worth
//!
//! Each of the five written locations is decided EXACTLY, for every register
//! value, by [`crate::bitserial_decide`] (a bit-serial automaton over the
//! terms; the two sides share no subterm). A refutation carries an
//! evaluator-confirmed counterexample. This is an in-process decision by
//! unverified Rust code: testing-grade evidence, never proof credit. The
//! function verifier reports a holding instruction unverified
//! ([`SUBS_IMM_DECIDED_IS_NOT_CREDIT`]); the coverage gate counts the row as
//! accepted regression evidence, not as a formal proof.
//!
//! # What it does not establish
//!
//! That the probe loop runs the intended number of iterations or touches
//! every guard page (the frame layout's claim), that NZCV is not clobbered
//! between the `SUBS` and its `B.NE`, or agreement with silicon (the
//! differential `tests/aarch64_subs_imm_silicon_differential.rs` samples the
//! models against this CPU).

use std::sync::OnceLock;

use crate::bitserial_decide::{self, Exact};
use crate::smt::SmtExpr;
use trust_cg_ir::{AArch64Opcode as O, MachInst, MachOperand, PReg, RegClass, SpecialReg, VReg};

/// Reason prefix of a holding `SUBS #imm` row the function verifier does not
/// credit.
pub const SUBS_IMM_DECIDED_IS_NOT_CREDIT: &str = "SUBS #imm decoded-word obligation is decided \
     in process (bit-serial, every register value), which is testing-grade evidence, not proof \
     credit";

/// How a holding obligation was decided.
pub const METHOD_BITSERIAL: &str =
    "every written location decided in-process for every register value by a bit-serial automaton";

/// The two forms: the operand width (`sf`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum SubsImmForm {
    /// `SUBS Wd, Wn|WSP, #imm12`.
    W,
    /// `SUBS Xd, Xn|SP, #imm12`.
    X,
}

impl SubsImmForm {
    /// Both forms.
    pub const ALL: [Self; 2] = [Self::W, Self::X];

    /// Operand width in bits.
    pub fn width(self) -> u32 {
        match self {
            Self::W => 32,
            Self::X => 64,
        }
    }

    fn sf(self) -> u32 {
        u32::from(self == Self::X)
    }

    /// The Arm spelling.
    pub fn mnemonic(self) -> &'static str {
        match self {
            Self::W => "SUBS Wd, Wn, #imm12",
            Self::X => "SUBS Xd, Xn, #imm12",
        }
    }
}

// ===========================================================================
// Encoder and decoder
// ===========================================================================

/// The word of `SUBS Rd, Rn, #imm12` from the Arm A64 "Add/subtract
/// (immediate)" diagram: `sf | op=1 | S=1 | 100010 | sh=0 | imm12 | Rn | Rd`.
pub fn subs_imm_word(form: SubsImmForm, rd: u32, rn: u32, imm12: u32) -> u32 {
    const CLASS: u32 = 0b10_0010; // bits 28:23
    (form.sf() << 31)
        | (1 << 30)
        | (1 << 29)
        | (CLASS << 23)
        | ((imm12 & 0xFFF) << 10)
        | ((rn & 31) << 5)
        | (rd & 31)
}

/// The fields of a decoded "Add/subtract (immediate)" word.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DecodedAddSubImm {
    pub sf: u32,
    pub op: u32,
    pub s: u32,
    pub sh: u32,
    pub imm12: u32,
    pub rn: u32,
    pub rd: u32,
}

/// Why a word is not an add/subtract (immediate) instruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AddSubImmRefusal {
    /// Another encoding class.
    OtherClass,
}

const fn bits(word: u32, hi: u32, lo: u32) -> u32 {
    (word >> lo) & ((1 << (hi - lo + 1)) - 1)
}

/// Decode a word of the "Add/subtract (immediate)" class (bits 28:23 =
/// `100010`), from the encoding table.
pub fn decode_add_sub_imm_word(word: u32) -> Result<DecodedAddSubImm, AddSubImmRefusal> {
    if bits(word, 28, 23) != 0b10_0010 {
        return Err(AddSubImmRefusal::OtherClass);
    }
    Ok(DecodedAddSubImm {
        sf: bits(word, 31, 31),
        op: bits(word, 30, 30),
        s: bits(word, 29, 29),
        sh: bits(word, 22, 22),
        imm12: bits(word, 21, 10),
        rn: bits(word, 9, 5),
        rd: bits(word, 4, 0),
    })
}

// ===========================================================================
// Machine side
// ===========================================================================

/// The four flags as Boolean terms.
#[derive(Debug, Clone, PartialEq)]
pub struct Nzcv {
    pub n: SmtExpr,
    pub z: SmtExpr,
    pub c: SmtExpr,
    pub v: SmtExpr,
}

impl Nzcv {
    /// `(name, term)` per flag, N first.
    pub fn parts(&self) -> [(&'static str, &SmtExpr); 4] {
        [
            ("N", &self.n),
            ("Z", &self.z),
            ("C", &self.c),
            ("V", &self.v),
        ]
    }
}

/// The general-purpose register a write lands in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Dest {
    /// `X<n>`, n < 31.
    Gpr(u8),
    /// The stack pointer.
    Sp,
    /// The zero register: the write is discarded.
    Discarded,
}

/// What an add/subtract (immediate) word writes.
#[derive(Debug, Clone, PartialEq)]
pub struct AddSubImmEffect {
    pub dest: Dest,
    /// The 64-bit register value after the write.
    pub value: SmtExpr,
    /// The flags, when the word sets them.
    pub flags: Option<Nzcv>,
}

fn bv(value: u64, width: u32) -> SmtExpr {
    SmtExpr::bv_const(value, width)
}

/// `X<n>` as a 64-bit state variable; the stack pointer is `sp`.
pub fn xvar(n: u32) -> SmtExpr {
    SmtExpr::var(format!("x{n}"), 64)
}

fn low(expr: SmtExpr, width: u32) -> SmtExpr {
    if width == 64 {
        expr
    } else {
        expr.extract(width - 1, 0)
    }
}

/// `AddWithCarry(x, y, carry_in)` at `width`, as the Arm pseudocode states
/// it: the sums one bit wider than the operands, `C` set exactly when the
/// unsigned sum differs from the zero-extended result, `V` when the signed
/// sum differs from the sign-extended result. `N` is the result's sign bit,
/// stated as `result <s 0`.
fn add_with_carry(x: SmtExpr, y: SmtExpr, carry: u64, width: u32) -> (SmtExpr, Nzcv) {
    let unsigned_sum = x
        .clone()
        .zero_ext(1)
        .bvadd(y.clone().zero_ext(1))
        .bvadd(bv(carry, width + 1));
    let signed_sum = x
        .sign_ext(1)
        .bvadd(y.sign_ext(1))
        .bvadd(bv(carry, width + 1));
    let result = unsigned_sum.clone().extract(width - 1, 0);
    let flags = Nzcv {
        n: result.clone().bvslt(bv(0, width)),
        z: result.clone().eq_expr(bv(0, width)),
        c: result.clone().zero_ext(1).eq_expr(unsigned_sum).not_expr(),
        v: result.clone().sign_ext(1).eq_expr(signed_sum).not_expr(),
    };
    (result, flags)
}

/// The Arm ARM pseudocode of an add/subtract (immediate) word:
///
/// ```text
/// imm = ZeroExtend(imm12 << (sh ? 12 : 0), datasize);
/// operand1 = if n == 31 then SP[] else X[n];
/// if sub_op then operand2 = NOT(imm); carry_in = '1';
///           else operand2 = imm;      carry_in = '0';
/// (result, nzcv) = AddWithCarry(operand1, operand2, carry_in);
/// if setflags then PSTATE.<N,Z,C,V> = nzcv;
/// if d == 31 && !setflags then SP[] = result; else X[d] = result;
/// ```
pub fn denote_add_sub_imm(decoded: &DecodedAddSubImm) -> AddSubImmEffect {
    let width = 32 << decoded.sf;
    let imm = (u64::from(decoded.imm12)) << if decoded.sh == 1 { 12 } else { 0 };
    let source = if decoded.rn == 31 {
        SmtExpr::var("sp", 64)
    } else {
        xvar(decoded.rn)
    };
    let operand1 = low(source, width);
    let (operand2, carry) = if decoded.op == 1 {
        (bv(imm, width).bvxor(bv(u64::MAX, width)), 1)
    } else {
        (bv(imm, width), 0)
    };
    let (result, nzcv) = add_with_carry(operand1, operand2, carry, width);
    let value = if width == 64 {
        result
    } else {
        result.zero_ext(32)
    };
    let dest = match (decoded.rd, decoded.s) {
        (31, 0) => Dest::Sp,
        (31, _) => Dest::Discarded,
        (d, _) => Dest::Gpr(d as u8),
    };
    AddSubImmEffect {
        dest,
        value,
        flags: (decoded.s == 1).then_some(nzcv),
    }
}

// ===========================================================================
// Intent
// ===========================================================================

/// The machine-IR intent of a `SubsRI` instruction.
#[derive(Debug, Clone, PartialEq)]
pub struct SubsImmIntent {
    pub form: SubsImmForm,
    pub rd: u32,
    pub rn: u32,
    pub imm12: u32,
    pub dest: Dest,
    /// The 64-bit value of the destination after the instruction.
    pub value: SmtExpr,
    /// The flags the comparison names.
    pub flags: Nzcv,
}

/// Why an instruction was not accepted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SubsImmCheckError {
    /// Outside the model: no claim either way.
    OutOfModel(String),
    /// Names something no `SUBS #imm` word does. Fails closed.
    IllFormed(String),
    /// The word does not perform the intent. Fails closed.
    Refuted {
        class: SubsImmRefusalClass,
        detail: String,
    },
    /// The decision procedure refused the terms.
    Undecided(String),
}

impl std::fmt::Display for SubsImmCheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfModel(why) => write!(f, "outside the SUBS #imm model: {why}"),
            Self::IllFormed(why) => write!(f, "ill-formed SUBS #imm instruction: {why}"),
            Self::Refuted { class, detail } => write!(f, "refuted ({class:?}): {detail}"),
            Self::Undecided(why) => write!(f, "undecided: {why}"),
        }
    }
}

/// The reason class of a refutation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SubsImmRefusalClass {
    /// Not an add/subtract (immediate) word.
    NotDecoded,
    /// The word writes another register (or discards the write).
    Destination,
    /// The word does not write NZCV.
    MissingFlags,
    /// The destination value differs for some register value.
    Value,
    /// A flag differs for some register value.
    Flag,
}

/// A general-purpose operand of a `SubsRI` instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Gpr {
    Reg { n: u8, width: u32 },
    Sp { width: u32 },
    Zero { width: u32 },
}

impl Gpr {
    fn width(self) -> u32 {
        match self {
            Self::Reg { width, .. } | Self::Sp { width } | Self::Zero { width } => width,
        }
    }

    fn field(self) -> u32 {
        match self {
            Self::Reg { n, .. } => u32::from(n),
            Self::Sp { .. } | Self::Zero { .. } => 31,
        }
    }
}

fn gpr(op: &MachOperand) -> Result<Gpr, SubsImmCheckError> {
    match op {
        MachOperand::PReg(p) => match p.encoding() {
            e @ 0..=30 => Ok(Gpr::Reg {
                n: e as u8,
                width: 64,
            }),
            31 => Ok(Gpr::Sp { width: 64 }),
            e @ 32..=62 => Ok(Gpr::Reg {
                n: (e - 32) as u8,
                width: 32,
            }),
            63 => Ok(Gpr::Sp { width: 32 }),
            160 => Ok(Gpr::Zero { width: 64 }),
            161 => Ok(Gpr::Zero { width: 32 }),
            e => Err(SubsImmCheckError::IllFormed(format!(
                "physical register encoding {e} is not a general-purpose register"
            ))),
        },
        MachOperand::Special(SpecialReg::SP) => Ok(Gpr::Sp { width: 64 }),
        MachOperand::Special(SpecialReg::XZR) => Ok(Gpr::Zero { width: 64 }),
        MachOperand::Special(SpecialReg::WZR) => Ok(Gpr::Zero { width: 32 }),
        other => Err(SubsImmCheckError::OutOfModel(format!(
            "unmodeled SUBS operand {other:?}"
        ))),
    }
}

/// Number virtual registers apart from every physical register the
/// instruction names, keeping each class's view.
fn with_virtual_registers_numbered(inst: &MachInst) -> Result<MachInst, SubsImmCheckError> {
    let mut used: Vec<u16> = inst
        .operands
        .iter()
        .filter_map(|op| match op {
            MachOperand::PReg(p) if matches!(p.encoding(), 0..=30 | 32..=62) => {
                Some(p.encoding() % 32)
            }
            _ => None,
        })
        .collect();
    let mut seen: Vec<(VReg, u16)> = Vec::new();
    let mut operands = Vec::with_capacity(inst.operands.len());
    for op in &inst.operands {
        let MachOperand::VReg(v) = op else {
            operands.push(op.clone());
            continue;
        };
        let base = match v.class {
            RegClass::Gpr64 => 0,
            RegClass::Gpr32 => 32,
            other => {
                return Err(SubsImmCheckError::IllFormed(format!(
                    "virtual register class {other:?} is not a general-purpose register"
                )));
            }
        };
        let n = match seen.iter().find(|(known, _)| known == v) {
            Some(&(_, n)) => n,
            None => {
                let n = (0..31u16)
                    .find(|n| !used.contains(n))
                    .ok_or_else(|| SubsImmCheckError::OutOfModel("too many registers".into()))?;
                used.push(n);
                seen.push((*v, n));
                n
            }
        };
        operands.push(MachOperand::PReg(PReg::new(base + n)));
    }
    Ok(MachInst::new(inst.opcode, operands))
}

/// The intent of `SubsRI [Rd, Rn, #imm]`: the difference and the comparison
/// flags, at the destination's width. `Rd` is a general-purpose register or
/// the zero register (a discarded write: the `CMP` alias), `Rn` a register
/// or the stack pointer of the same width, and `imm` in `0..=4095`.
pub fn subs_imm_intent(inst: &MachInst) -> Result<SubsImmIntent, SubsImmCheckError> {
    if inst.opcode != O::SubsRI {
        return Err(SubsImmCheckError::OutOfModel(format!(
            "{:?} is not SubsRI",
            inst.opcode
        )));
    }
    if inst.operands.len() != 3 {
        return Err(SubsImmCheckError::IllFormed(format!(
            "SubsRI with {} operands (expected [Rd, Rn, #imm])",
            inst.operands.len()
        )));
    }
    let inst = with_virtual_registers_numbered(inst)?;
    let d = gpr(&inst.operands[0])?;
    let n = gpr(&inst.operands[1])?;
    let MachOperand::Imm(imm) = inst.operands[2] else {
        return Err(SubsImmCheckError::IllFormed(format!(
            "SubsRI immediate operand {:?}",
            inst.operands[2]
        )));
    };
    let imm12 = u32::try_from(imm)
        .ok()
        .filter(|imm| *imm <= 0xFFF)
        .ok_or_else(|| {
            SubsImmCheckError::IllFormed(format!("SUBS immediate {imm} is not an unsigned imm12"))
        })?;
    if matches!(d, Gpr::Sp { .. }) {
        return Err(SubsImmCheckError::IllFormed(
            "a flag-setting SUBS cannot write the stack pointer (register 31 is ZR)".into(),
        ));
    }
    if matches!(n, Gpr::Zero { .. }) {
        return Err(SubsImmCheckError::IllFormed(
            "SUBS #imm reads SP, not ZR, in register 31".into(),
        ));
    }
    let width = d.width();
    if n.width() != width {
        return Err(SubsImmCheckError::OutOfModel(format!(
            "SUBS with a {}-bit destination view and a {}-bit source view",
            width,
            n.width()
        )));
    }
    let form = if width == 64 {
        SubsImmForm::X
    } else {
        SubsImmForm::W
    };
    let source = match n {
        Gpr::Reg { n, .. } => xvar(u32::from(n)),
        _ => SmtExpr::var("sp", 64),
    };
    let a = low(source, width);
    let k = bv(u64::from(imm12), width);
    let difference = a.clone().bvsub(k.clone());
    let zero = bv(0, width);
    let flags = Nzcv {
        n: difference.clone().bvslt(zero.clone()),
        z: difference.clone().eq_expr(zero.clone()),
        c: a.clone().bvuge(k),
        // A non-negative subtrahend overflows only from a negative minuend
        // to a non-negative difference.
        v: a.bvslt(zero.clone())
            .and_expr(difference.clone().bvsge(zero)),
    };
    let value = if width == 64 {
        difference
    } else {
        difference.zero_ext(32)
    };
    Ok(SubsImmIntent {
        form,
        rd: d.field(),
        rn: n.field(),
        imm12,
        dest: match d {
            Gpr::Reg { n, .. } => Dest::Gpr(n),
            _ => Dest::Discarded,
        },
        value,
        flags,
    })
}

// ===========================================================================
// The per-word check
// ===========================================================================

fn refuted(class: SubsImmRefusalClass, detail: impl Into<String>) -> SubsImmCheckError {
    SubsImmCheckError::Refuted {
        class,
        detail: detail.into(),
    }
}

fn decide(
    part: &str,
    machine: &SmtExpr,
    intent: &SmtExpr,
    class: SubsImmRefusalClass,
    word: u32,
) -> Result<(), SubsImmCheckError> {
    match bitserial_decide::decide_equal(machine, intent) {
        Ok(Exact::Holds) => Ok(()),
        Ok(Exact::Refuted(witness)) => Err(refuted(
            class,
            format!(
                "{word:#010x} {part} differs from the intent at {}",
                witness
                    .iter()
                    .map(|(name, value)| format!("{name}={value:#x}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        )),
        Err(error) => Err(SubsImmCheckError::Undecided(format!("{part}: {error}"))),
    }
}

/// Decide whether `word` performs `intent`: the destination, its value and
/// every flag, each for every register value.
pub fn check_word_against_intent(
    intent: &SubsImmIntent,
    word: u32,
) -> Result<(), SubsImmCheckError> {
    use SubsImmRefusalClass as C;
    let decoded = decode_add_sub_imm_word(word).map_err(|_| {
        refuted(
            C::NotDecoded,
            format!("{word:#010x} is not an add/subtract (immediate) word"),
        )
    })?;
    let effect = denote_add_sub_imm(&decoded);
    if effect.dest != intent.dest {
        return Err(refuted(
            C::Destination,
            format!(
                "{word:#010x} writes {:?}, the instruction writes {:?}",
                effect.dest, intent.dest
            ),
        ));
    }
    let Some(flags) = effect.flags else {
        return Err(refuted(
            C::MissingFlags,
            format!("{word:#010x} does not set NZCV"),
        ));
    };
    if effect.dest != Dest::Discarded {
        decide("value", &effect.value, &intent.value, C::Value, word)?;
    }
    for ((name, machine), (_, want)) in flags.parts().into_iter().zip(intent.flags.parts()) {
        decide(name, machine, want, C::Flag, word)?;
    }
    Ok(())
}

/// The word this module re-derives for an instruction, with its intent.
pub fn subs_imm_instance(inst: &MachInst) -> Result<(SubsImmIntent, u32), SubsImmCheckError> {
    let intent = subs_imm_intent(inst)?;
    let word = subs_imm_word(intent.form, intent.rd, intent.rn, intent.imm12);
    Ok((intent, word))
}

/// The walk's verdict for one `SubsRI`: the re-derived word decided against
/// the operands' intent. `None` for every other opcode.
pub fn subs_imm_verdict(inst: &MachInst) -> Option<Result<u32, SubsImmCheckError>> {
    (inst.opcode == O::SubsRI).then(|| {
        subs_imm_instance(inst)
            .and_then(|(intent, word)| check_word_against_intent(&intent, word).map(|()| word))
    })
}

/// ENC-5's per-compile binding: the emitted word of an admitted `SubsRI` must
/// be exactly the re-derived word and hold against the intent. `None` for
/// other opcodes and for shapes outside the model.
pub fn check_emitted_subs_imm_word(inst: &MachInst, emitted: u32) -> Option<Result<(), String>> {
    if inst.opcode != O::SubsRI {
        return None;
    }
    let (intent, word) = match subs_imm_instance(inst) {
        Ok(instance) => instance,
        Err(SubsImmCheckError::OutOfModel(_)) => return None,
        Err(error) => return Some(Err(error.to_string())),
    };
    if emitted != word {
        return Some(Err(format!(
            "emitted SUBS word {emitted:#010x} is not the verified word {word:#010x}"
        )));
    }
    Some(check_word_against_intent(&intent, emitted).map_err(|error| error.to_string()))
}

// ===========================================================================
// Controls and credit
// ===========================================================================

/// A deliberately wrong intent.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SubsImmIntentMutation {
    /// The sum instead of the difference.
    Sum,
    /// `C` as the signed comparison.
    SignedCarry,
    /// `C` as a borrow (`Rn < imm`), the x86 convention.
    BorrowCarry,
    /// `V` never set.
    NoOverflow,
    /// `Z` inverted.
    InvertedZero,
    /// `N` from the minuend instead of the difference.
    MinuendSign,
    /// The immediate off by one.
    ImmediateOffByOne,
}

impl SubsImmIntentMutation {
    /// Every mutation.
    pub const ALL: [Self; 7] = [
        Self::Sum,
        Self::SignedCarry,
        Self::BorrowCarry,
        Self::NoOverflow,
        Self::InvertedZero,
        Self::MinuendSign,
        Self::ImmediateOffByOne,
    ];
}

/// `intent` under `mutation`.
pub fn mutated_intent(intent: &SubsImmIntent, mutation: SubsImmIntentMutation) -> SubsImmIntent {
    let width = intent.form.width();
    let source = if intent.rn == 31 {
        SmtExpr::var("sp", 64)
    } else {
        xvar(intent.rn)
    };
    let a = low(source, width);
    let imm = match mutation {
        SubsImmIntentMutation::ImmediateOffByOne => u64::from(intent.imm12) + 1,
        _ => u64::from(intent.imm12),
    };
    let k = bv(imm, width);
    let zero = bv(0, width);
    let difference = match mutation {
        SubsImmIntentMutation::Sum => a.clone().bvadd(k.clone()),
        _ => a.clone().bvsub(k.clone()),
    };
    let mut flags = Nzcv {
        n: difference.clone().bvslt(zero.clone()),
        z: difference.clone().eq_expr(zero.clone()),
        c: a.clone().bvuge(k.clone()),
        v: a.clone()
            .bvslt(zero.clone())
            .and_expr(difference.clone().bvsge(zero.clone())),
    };
    match mutation {
        SubsImmIntentMutation::SignedCarry => flags.c = a.clone().bvsge(k),
        SubsImmIntentMutation::BorrowCarry => flags.c = a.clone().bvult(k),
        SubsImmIntentMutation::NoOverflow => flags.v = SmtExpr::bool_const(false),
        SubsImmIntentMutation::InvertedZero => flags.z = flags.z.clone().not_expr(),
        SubsImmIntentMutation::MinuendSign => flags.n = a.bvslt(zero),
        _ => {}
    }
    let value = if width == 64 {
        difference
    } else {
        difference.zero_ext(32)
    };
    SubsImmIntent {
        value,
        flags,
        ..intent.clone()
    }
}

/// The canonical instruction of a form: `SUBS {W,X}d, {W,X}n, #imm`.
pub fn representative_instruction(form: SubsImmForm, rd: u32, rn: u32, imm12: u32) -> MachInst {
    let reg = |n: u32| {
        let base = if form == SubsImmForm::X { 0 } else { 32 };
        match n {
            31 => MachOperand::PReg(PReg::new(base + 31)),
            n => MachOperand::PReg(PReg::new(base + n as u16)),
        }
    };
    let dest = if rd == 31 {
        MachOperand::Special(if form == SubsImmForm::X {
            SpecialReg::XZR
        } else {
            SpecialReg::WZR
        })
    } else {
        reg(rd)
    };
    MachInst::new(
        O::SubsRI,
        vec![dest, reg(rn), MachOperand::Imm(i64::from(imm12))],
    )
}

/// The `(rd, rn, imm12)` assignments every form is decided over: the probe's
/// own `SUBS X16, X16, #1`, distinct registers, the immediate extremes, the
/// stack pointer as source and the zero register as destination.
pub const INSTANCE_BATTERY: [(u32, u32, u32); 6] = [
    (16, 16, 1),
    (0, 1, 0),
    (2, 3, 4095),
    (4, 31, 16),
    (31, 5, 7),
    (30, 29, 2048),
];

/// One negative control.
#[derive(Debug, Clone, PartialEq)]
pub struct SubsImmControl {
    pub label: String,
    pub word: u32,
    pub intent: SubsImmIntent,
    /// The class it must be refuted for; `None`: any refutation.
    pub class: Option<SubsImmRefusalClass>,
}

/// Every negative control: each form's canonical word with every single bit
/// flipped, the ADDS, SUB, other-width, shifted-immediate, off-by-one,
/// other-source and other-destination words, and every intent mutation.
pub fn subs_imm_controls() -> Vec<SubsImmControl> {
    use SubsImmRefusalClass as C;
    let mut out = Vec::new();
    for form in SubsImmForm::ALL {
        let inst = representative_instruction(form, 16, 16, 1);
        let intent = subs_imm_intent(&inst).expect("the representative is in the model");
        let word = subs_imm_word(form, 16, 16, 1);
        let other_width = if form == SubsImmForm::X {
            SubsImmForm::W
        } else {
            SubsImmForm::X
        };
        for bit in 0..32 {
            out.push(SubsImmControl {
                label: format!("{} word bit {bit} flipped", form.mnemonic()),
                word: word ^ (1 << bit),
                intent: intent.clone(),
                class: None,
            });
        }
        for (label, word, class) in [
            ("ADDS", word & !(1 << 30), C::Value),
            ("SUB (no flags)", word & !(1 << 29), C::MissingFlags),
            (
                "other width",
                subs_imm_word(other_width, 16, 16, 1),
                C::Value,
            ),
            ("LSL #12 immediate", word | (1 << 22), C::Value),
            ("immediate 2", subs_imm_word(form, 16, 16, 2), C::Value),
            ("immediate 0", subs_imm_word(form, 16, 16, 0), C::Value),
            ("source x17", subs_imm_word(form, 16, 17, 1), C::Value),
            (
                "destination x17",
                subs_imm_word(form, 17, 16, 1),
                C::Destination,
            ),
            ("CMP alias", subs_imm_word(form, 31, 16, 1), C::Destination),
        ] {
            out.push(SubsImmControl {
                label: format!("{} {label}", form.mnemonic()),
                word,
                intent: intent.clone(),
                class: Some(class),
            });
        }
        for mutation in SubsImmIntentMutation::ALL {
            let class = match mutation {
                SubsImmIntentMutation::Sum | SubsImmIntentMutation::ImmediateOffByOne => C::Value,
                _ => C::Flag,
            };
            out.push(SubsImmControl {
                label: format!("{} intent {mutation:?}", form.mnemonic()),
                word,
                intent: mutated_intent(&intent, mutation),
                class: Some(class),
            });
        }
    }
    out
}

/// What the coverage gate's `SubsRI` row rests on.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubsImmCredit {
    /// Forms decided to hold.
    pub forms: usize,
    /// Instances (form x operands) decided to hold.
    pub instances: usize,
    /// Negative controls refuted for their stated reason.
    pub controls_refuted: usize,
}

/// The row's credit: both forms hold over [`INSTANCE_BATTERY`] and every
/// control is refuted for its stated reason. Memoized for the process.
pub fn subs_imm_credit() -> Result<SubsImmCredit, String> {
    static MEMO: OnceLock<Result<SubsImmCredit, String>> = OnceLock::new();
    MEMO.get_or_init(compute_credit).clone()
}

fn compute_credit() -> Result<SubsImmCredit, String> {
    let mut instances = 0;
    for form in SubsImmForm::ALL {
        for (rd, rn, imm) in INSTANCE_BATTERY {
            let inst = representative_instruction(form, rd, rn, imm);
            match subs_imm_verdict(&inst) {
                Some(Ok(_)) => instances += 1,
                other => {
                    return Err(format!(
                        "{} {rd}/{rn}/#{imm} does not hold: {other:?}",
                        form.mnemonic()
                    ));
                }
            }
        }
    }
    let mut refuted_count = 0;
    let mut failures = Vec::new();
    for control in subs_imm_controls() {
        match check_word_against_intent(&control.intent, control.word) {
            Err(SubsImmCheckError::Refuted { class, .. })
                if control.class.is_none_or(|want| want == class) =>
            {
                refuted_count += 1;
            }
            other => failures.push(format!("{}: {other:?}", control.label)),
        }
    }
    if !failures.is_empty() {
        return Err(format!(
            "{} SUBS #imm control(s) not refuted for their reason: {failures:?}",
            failures.len()
        ));
    }
    Ok(SubsImmCredit {
        forms: SubsImmForm::ALL.len(),
        instances,
        controls_refuted: refuted_count,
    })
}

#[cfg(test)]
#[path = "aarch64_subs_imm_proofs_tests.rs"]
mod tests;
