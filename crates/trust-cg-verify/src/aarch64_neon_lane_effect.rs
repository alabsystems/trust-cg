// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Word-bound, decomposed lane-effect obligations for the emitted AArch64
//! NEON horizontal reductions and permutes (ledger `L04-P6`).
//!
//! # What this states
//!
//! The opcode-level NEON obligations ([`crate::neon_lowering_proofs`]) state
//! each operation once, over a representative register assignment, with the
//! machine side built from the `neon_semantics` model the opcode names. They
//! say nothing about the word a given instruction is encoded to. This module
//! states, per emitted instruction, that ITS word performs the lane movement
//! or reduction its machine-IR operands name, in the style of the memory-effect
//! decomposition ([`crate::aarch64_memory_effect`]):
//!
//! * the instruction WORD is a 32-bit literal inside every part, and the
//!   machine side of each part is computed from that literal's bits by SMT
//!   terms: the operation-selecting fields (`imm4`, `U:size:opcode`,
//!   `op:cmode:o2`) and the element size and lane index (`imm5`, `imm4`,
//!   `abc:defgh`) choose among the class's operations by `ite` over equalities
//!   of extracted fields, never by a Rust decoder;
//! * the intent side is built from the operands alone: the element the
//!   operands name, sliced directly from the raw 64-bit register halves, the
//!   arrangement and lane they name, the immediate they carry;
//! * the word is the one [`neon_lane_effect_word`] re-derives from the
//!   operands (a layout mirror of the codegen encoder, pinned against it by
//!   the silicon differential), and ENC-5 requires, per compile, the emitted
//!   word to equal it ([`check_emitted_neon_lane_effect_word`]).
//!
//! # The parts
//!
//! * `fields` (ground): every non-immediate field of the word equals the value
//!   the operands name: the encoding class, `Q`, the operation selector, the
//!   element-size marker and the register fields.
//! * `half 0`, `half 1` (a vector destination): the 64-bit view of the
//!   destination register the word writes, against the operands' value. A
//!   64-bit (`Q = 0`) vector form states `half 1` as zero. A scalar
//!   destination (`Sd`, `Dd`) has `half 0` only (the scalar, zero-extended):
//!   that the rest of its V register is zeroed is the scalar class's
//!   definition, which `fields` pins.
//! * `gpr` (UMOV): the 64-bit general register the word writes (`Wd`
//!   zero-extends).
//!
//! Inputs are `vn_lo`, `vn_hi`, `vm_lo`, `vm_hi`, `vd_lo`, `vd_hi` (the
//! 64-bit halves of `Vn`, `Vm` and the prior `Vd`) and `xn` (the general
//! source register); a zero-register source is the constant zero.
//!
//! # The composition, and its assumptions
//!
//! When every part holds, executing the word from any register file writes
//! the registers the operands' operation writes, with the values it writes:
//! `fields` fixes the class, the operation family and the registers read and
//! written, and the value parts fix every written bit. Assumptions: the
//! instruction does not trap (Advanced SIMD enabled, `CPACR_EL1.FPEN`), and
//! register naming as Arm defines it (field 31 is the zero register in a
//! general source, never SP). The operation semantics the machine sides use
//! for the reductions (`UMAXV`, `ADDP`) are this crate's models; their
//! agreement with the CPU is testing evidence
//! (`tests/aarch64_neon_silicon_differential.rs`).
//!
//! # Strength
//!
//! [`decide_in_process`] decides every part of an admitted word exactly: a
//! ground part by one evaluation; a permute or move part as a pure bit
//! routing (`aarch64_value_decode_proofs::exact_routing_equality`); a
//! reduction part by folding the word's fields and comparing the folded terms
//! syntactically (equal terms are equal for every input). A part none of
//! those rules decides (only a corrupted word's reduction part) reaches the
//! sampling lane. That is testing-grade evidence about this module's terms,
//! not a certificate: these parts are never proof credit, and the function
//! verifier only refutes or annotates a row with them
//! ([`crate::function_verifier::NEON_LANE_EFFECT_IS_NOT_CREDIT`]). No live
//! replay lane exists for them yet, so no part has a Clean-checked
//! certificate.

use crate::lowering_proof::{
    MachineSideProvenance, ProofObligation, TransvalCheckKind, VerificationConfig,
    memoized_verify_by_evaluation,
};
use crate::smt::{SmtExpr as E, VectorArrangement as A, lane_extract};
use crate::verify::{VerificationResult, VerificationStrength};
use trust_cg_ir::{AArch64Opcode as O, MachInst, MachOperand};

/// Every opcode this module decomposes (in the admitted shapes only).
pub const NEON_LANE_EFFECT_OPCODES: &[O] = &[
    O::NeonDupElem,
    O::NeonDupGen,
    O::NeonInsGen,
    O::NeonUmovGen,
    O::NeonDupScalarD,
    O::NeonUmaxv,
    O::NeonAddpScalar,
    O::NeonRev32V,
    O::NeonRev64V,
    O::NeonRbitV,
    O::NeonExtV,
    O::NeonMovi,
];

// ===========================================================================
// What the operands name
// ===========================================================================

/// A general source register: a numbered register, or the zero register.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GprSource {
    /// `Xn`/`Wn` with this five-bit number (0..=30).
    Reg(u8),
    /// `XZR`/`WZR` (field 31): reads as zero.
    Zero,
}

impl GprSource {
    fn field(self) -> u32 {
        match self {
            Self::Reg(n) => u32::from(n),
            Self::Zero => 31,
        }
    }

    fn value(self) -> E {
        match self {
            Self::Reg(_) => E::var("xn", 64),
            Self::Zero => zeros(64),
        }
    }
}

/// The operation the operands name. `log2` is the element size as
/// `log2(bytes)`; `q` the 128-bit (`true`) or 64-bit vector width.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LaneOp {
    /// `DUP Vd.<T>, Vn.<Ts>[index]`.
    DupElement { q: bool, log2: u32, index: u32 },
    /// `DUP Vd.<T>, <R>n`.
    DupGeneral {
        q: bool,
        log2: u32,
        source: GprSource,
    },
    /// `INS Vd.<Ts>[index], <R>n` (tied: the other lanes are kept).
    InsGeneral {
        log2: u32,
        index: u32,
        source: GprSource,
    },
    /// `UMOV <R>d, Vn.<Ts>[index]`.
    Umov { log2: u32, index: u32 },
    /// `DUP Dd, Vn.D[index]`.
    DupScalarD { index: u32 },
    /// `UMAXV Sd, Vn.4S`.
    Umaxv4S,
    /// `ADDP Dd, Vn.2D`.
    Addp2D,
    /// `REV64` (`container = 64`) or `REV32` (`container = 32`) at element
    /// size `log2`.
    Rev { q: bool, container: u32, log2: u32 },
    /// `RBIT Vd.<8B|16B>`.
    Rbit { q: bool },
    /// `EXT Vd.16B, Vn.16B, Vm.16B, #index`.
    Ext { index: u32 },
    /// `MOVI Vd.<8B|16B>, #imm8`.
    MoviByte { q: bool, imm8: u8 },
}

/// One admitted instruction, reduced to what its operands name.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NeonLaneAccess {
    /// The emitted opcode.
    pub opcode: O,
    /// The operation.
    pub op: LaneOp,
    /// Destination field.
    pub rd: u8,
    /// First source field (a general register's for DUP/INS general).
    pub rn: u8,
    /// Second source field (EXT only; 0 elsewhere).
    pub rm: u8,
}

/// Five-bit field of a SIMD&FP register of the given width (128: V, 64: D,
/// 32: S).
fn fp_reg(operand: &MachOperand, bits: u32) -> Option<u8> {
    let MachOperand::PReg(p) = operand else {
        return None;
    };
    let e = p.encoding();
    let (lo, width) = match e {
        64..=95 => (64, 128),
        96..=127 => (96, 64),
        128..=159 => (128, 32),
        _ => return None,
    };
    (width == bits).then(|| (e - lo) as u8)
}

/// A vector register for width `q`: Q=1 needs V; Q=0 admits V or D.
fn vector_reg(operand: &MachOperand, q: bool) -> Option<u8> {
    fp_reg(operand, 128).or_else(|| if q { None } else { fp_reg(operand, 64) })
}

/// A general source register: `(is_x, source)`.
fn gpr_source(operand: &MachOperand) -> Option<(bool, GprSource)> {
    use trust_cg_ir::regs::SpecialReg;
    match operand {
        MachOperand::PReg(p) => match p.encoding() {
            e @ 0..=30 => Some((true, GprSource::Reg(e as u8))),
            e @ 32..=62 => Some((false, GprSource::Reg((e - 32) as u8))),
            160 => Some((true, GprSource::Zero)),
            161 => Some((false, GprSource::Zero)),
            _ => None,
        },
        MachOperand::Special(SpecialReg::XZR) => Some((true, GprSource::Zero)),
        MachOperand::Special(SpecialReg::WZR) => Some((false, GprSource::Zero)),
        _ => None,
    }
}

fn imm(operand: &MachOperand) -> Option<i64> {
    match operand {
        MachOperand::Imm(value) => Some(*value),
        _ => None,
    }
}

fn element_log2(operand: &MachOperand) -> Option<u32> {
    match imm(operand)? {
        1 => Some(0),
        2 => Some(1),
        4 => Some(2),
        8 => Some(3),
        _ => None,
    }
}

fn lane_index(operand: &MachOperand, log2: u32) -> Option<u32> {
    let value = imm(operand)?;
    (0..i64::from(16u32 >> log2))
        .contains(&value)
        .then_some(value as u32)
}

/// The arrangement selector's `(Q, size)` (0 = 8B .. 6 = 2D).
fn arrangement(operand: &MachOperand) -> Option<(bool, u32)> {
    Some(match imm(operand)? {
        0 => (false, 0),
        1 => (true, 0),
        2 => (false, 1),
        3 => (true, 1),
        4 => (false, 2),
        5 => (true, 2),
        6 => (true, 3),
        _ => return None,
    })
}

/// The access `inst` names, or `None` when it is not an admitted shape. The
/// admission follows ENC-5's arm for each opcode, except that a DUP (element)
/// source must be a V register.
pub fn neon_lane_access(inst: &MachInst) -> Option<NeonLaneAccess> {
    let ops = inst.operands.as_slice();
    let access = |op, rd, rn, rm| {
        Some(NeonLaneAccess {
            opcode: inst.opcode,
            op,
            rd,
            rn,
            rm,
        })
    };
    match (inst.opcode, ops) {
        (O::NeonDupElem, [dst, src, lane, size]) => {
            let log2 = element_log2(size)?;
            let (q, rd) = match (fp_reg(dst, 128), fp_reg(dst, 64)) {
                (Some(rd), _) => (true, rd),
                (None, Some(rd)) if log2 < 3 => (false, rd),
                _ => return None,
            };
            let index = lane_index(lane, log2)?;
            let rn = fp_reg(src, 128)?;
            access(LaneOp::DupElement { q, log2, index }, rd, rn, 0)
        }
        (O::NeonDupGen, [dst, src, size]) => {
            let log2 = element_log2(size)?;
            let (q, rd) = match (fp_reg(dst, 128), fp_reg(dst, 64)) {
                (Some(rd), _) => (true, rd),
                (None, Some(rd)) if log2 < 3 => (false, rd),
                _ => return None,
            };
            let (is_x, source) = gpr_source(src)?;
            if log2 == 3 && !is_x {
                return None;
            }
            access(
                LaneOp::DupGeneral { q, log2, source },
                rd,
                source.field() as u8,
                0,
            )
        }
        (O::NeonInsGen, [dst, src, lane, size]) => {
            let log2 = element_log2(size)?;
            let rd = fp_reg(dst, 128)?;
            let index = lane_index(lane, log2)?;
            let (is_x, source) = gpr_source(src)?;
            if log2 == 3 && !is_x {
                return None;
            }
            access(
                LaneOp::InsGeneral {
                    log2,
                    index,
                    source,
                },
                rd,
                source.field() as u8,
                0,
            )
        }
        (O::NeonUmovGen, [dst, src, lane, size]) => {
            let log2 = element_log2(size)?;
            let index = lane_index(lane, log2)?;
            let rd = match gpr_source(dst)? {
                (is_x, GprSource::Reg(n)) if is_x == (log2 == 3) => n,
                _ => return None,
            };
            let rn = fp_reg(src, 128)?;
            access(LaneOp::Umov { log2, index }, rd, rn, 0)
        }
        (O::NeonDupScalarD, [dst, src, lane]) => {
            let rd = fp_reg(dst, 64)?;
            let rn = fp_reg(src, 128)?;
            let index = lane_index(lane, 3)?;
            access(LaneOp::DupScalarD { index }, rd, rn, 0)
        }
        (O::NeonUmaxv, [dst, src, selector]) => {
            (arrangement(selector)? == (true, 2)).then_some(())?;
            access(LaneOp::Umaxv4S, fp_reg(dst, 32)?, fp_reg(src, 128)?, 0)
        }
        (O::NeonAddpScalar, [dst, src, selector]) => {
            (arrangement(selector)? == (true, 3)).then_some(())?;
            access(LaneOp::Addp2D, fp_reg(dst, 64)?, fp_reg(src, 128)?, 0)
        }
        (O::NeonRev32V | O::NeonRev64V | O::NeonRbitV, [dst, src, selector]) => {
            let (q, size) = arrangement(selector)?;
            let op = match (inst.opcode, size) {
                (O::NeonRbitV, 0) => LaneOp::Rbit { q },
                (O::NeonRev32V, 0) => LaneOp::Rev {
                    q,
                    container: 32,
                    log2: 0,
                },
                (O::NeonRev64V, 0) | (O::NeonRev64V, 2) => LaneOp::Rev {
                    q,
                    container: 64,
                    log2: size,
                },
                _ => return None,
            };
            access(op, vector_reg(dst, q)?, vector_reg(src, q)?, 0)
        }
        (O::NeonExtV, [dst, n, m, bytes]) => {
            let index = u32::try_from(imm(bytes)?).ok().filter(|b| *b < 16)?;
            access(
                LaneOp::Ext { index },
                fp_reg(dst, 128)?,
                fp_reg(n, 128)?,
                fp_reg(m, 128)?,
            )
        }
        (O::NeonMovi, [dst, value]) => {
            let (q, rd) = match (fp_reg(dst, 128), fp_reg(dst, 64)) {
                (Some(rd), _) => (true, rd),
                (None, Some(rd)) => (false, rd),
                _ => return None,
            };
            let imm8 = u8::try_from(imm(value)?).ok()?;
            access(LaneOp::MoviByte { q, imm8 }, rd, 0, 0)
        }
        _ => None,
    }
}

// ===========================================================================
// The word the operands name
// ===========================================================================

/// `imm5` of the copy classes: the index above the element-size marker.
fn copy_imm5(log2: u32, index: u32) -> u32 {
    (index << (log2 + 1)) | (1 << log2)
}

/// The word `access` names (a layout mirror of the codegen encoder, pinned
/// against it by `tests/aarch64_neon_silicon_differential.rs`).
fn word_of(access: &NeonLaneAccess) -> u32 {
    let (rd, rn, rm) = (
        u32::from(access.rd),
        u32::from(access.rn),
        u32::from(access.rm),
    );
    let regs = (rn << 5) | rd;
    let q = |q: bool| u32::from(q) << 30;
    match access.op {
        LaneOp::DupElement {
            q: wide,
            log2,
            index,
        } => 0x0E00_0400 | q(wide) | (copy_imm5(log2, index) << 16) | regs,
        LaneOp::DupGeneral { q: wide, log2, .. } => {
            0x0E00_0C00 | q(wide) | (copy_imm5(log2, 0) << 16) | regs
        }
        LaneOp::InsGeneral { log2, index, .. } => {
            0x4E00_1C00 | (copy_imm5(log2, index) << 16) | regs
        }
        LaneOp::Umov { log2, index } => {
            0x0E00_3C00 | q(log2 == 3) | (copy_imm5(log2, index) << 16) | regs
        }
        LaneOp::DupScalarD { index } => 0x5E00_0400 | (copy_imm5(3, index) << 16) | regs,
        LaneOp::Umaxv4S => 0x6EB0_A800 | regs,
        LaneOp::Addp2D => 0x5EF1_B800 | regs,
        LaneOp::Rev {
            q: wide,
            container,
            log2,
        } => {
            let base = if container == 64 {
                0x0E20_0800
            } else {
                0x2E20_0800
            };
            base | q(wide) | (log2 << 22) | regs
        }
        LaneOp::Rbit { q: wide } => 0x2E60_5800 | q(wide) | regs,
        LaneOp::Ext { index } => 0x6E00_0000 | (rm << 16) | (index << 11) | regs,
        LaneOp::MoviByte { q: wide, imm8 } => {
            let (abc, defgh) = (u32::from(imm8) >> 5, u32::from(imm8) & 31);
            0x0F00_E400 | q(wide) | (abc << 16) | (defgh << 5) | rd
        }
    }
}

/// The word `inst` re-derives to, for an admitted shape.
pub fn neon_lane_effect_word(inst: &MachInst) -> Option<u32> {
    neon_lane_access(inst).map(|access| word_of(&access))
}

/// ENC-5's binding of the emitted word to the word the parts carry:
/// `Some(Ok(()))` when `emitted` equals [`neon_lane_effect_word`],
/// `Some(Err(_))` when it differs, `None` when `inst` is not an admitted shape.
pub fn check_emitted_neon_lane_effect_word(
    inst: &MachInst,
    emitted: u32,
) -> Option<Result<(), String>> {
    let expected = neon_lane_effect_word(inst)?;
    Some(if emitted == expected {
        Ok(())
    } else {
        Err(format!(
            "emitted word {emitted:#010x} is not the word {expected:#010x} the NEON \
             lane-effect obligations carry"
        ))
    })
}

// ===========================================================================
// Parts
// ===========================================================================

/// Which fact of the instruction one part states.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum NeonLaneEffectPart {
    /// Every non-immediate field of the word.
    Fields,
    /// 64-bit half `half` of the SIMD&FP destination.
    Half { half: u8 },
    /// The general destination register (UMOV).
    Gpr,
}

impl std::fmt::Display for NeonLaneEffectPart {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Fields => write!(f, "fields"),
            Self::Half { half } => write!(f, "half {half}"),
            Self::Gpr => write!(f, "gpr"),
        }
    }
}

/// One part and its obligation (`trust_ir_expr` is the operands' side,
/// `aarch64_expr` the word's).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NeonLaneEffectObligation {
    /// Which fact it states.
    pub part: NeonLaneEffectPart,
    /// The obligation.
    pub obligation: ProofObligation,
}

/// Every part of one admitted instruction, for one word.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NeonLaneEffectDecomposition {
    /// What the operands name.
    pub access: NeonLaneAccess,
    /// The word every part carries.
    pub word: u32,
    /// The parts: fields, then the destination's halves or the GPR.
    pub parts: Vec<NeonLaneEffectObligation>,
}

/// The decomposition of `inst` over its re-derived word, or `None` when `inst`
/// is not an admitted shape.
pub fn neon_lane_effect(inst: &MachInst) -> Option<NeonLaneEffectDecomposition> {
    let access = neon_lane_access(inst)?;
    Some(decompose(&access, word_of(&access)))
}

/// The decomposition of `inst` over a caller-supplied word: the seam the
/// negative controls feed mutated words through.
pub fn neon_lane_effect_for_word(
    inst: &MachInst,
    word: u32,
) -> Option<NeonLaneEffectDecomposition> {
    let access = neon_lane_access(inst)?;
    Some(decompose(&access, word))
}

fn decompose(access: &NeonLaneAccess, word: u32) -> NeonLaneEffectDecomposition {
    let label = format!("A64 NEON lane effect {:?} {word:#010x}", access.opcode);
    let mut parts = vec![part(
        &label,
        NeonLaneEffectPart::Fields,
        E::bool_const(true),
        fields_conjunction(access, word),
        access.opcode,
    )];
    if let LaneOp::Umov { log2, index } = access.op {
        parts.push(part(
            &label,
            NeonLaneEffectPart::Gpr,
            zext64(lane_of("vn", log2, index)),
            copy_gpr_machine(word),
            access.opcode,
        ));
    } else {
        // A scalar destination (`Sd`, `Dd`) zeroes the rest of its V register
        // by the class's definition, which `fields` pins: it has no `half 1`.
        let halves = if matches!(
            access.op,
            LaneOp::DupScalarD { .. } | LaneOp::Umaxv4S | LaneOp::Addp2D
        ) {
            1
        } else {
            2
        };
        for half in 0..halves {
            parts.push(part(
                &label,
                NeonLaneEffectPart::Half { half: half as u8 },
                intent_half(access, half),
                machine_half(access, word, half),
                access.opcode,
            ));
        }
    }
    NeonLaneEffectDecomposition {
        access: *access,
        word,
        parts,
    }
}

fn part(
    label: &str,
    which: NeonLaneEffectPart,
    intent: E,
    machine: E,
    opcode: O,
) -> NeonLaneEffectObligation {
    let mut inputs: Vec<(String, u32)> = Vec::new();
    for expr in [&intent, &machine] {
        collect_vars(expr, &mut inputs);
    }
    inputs.sort();
    NeonLaneEffectObligation {
        part: which,
        obligation: ProofObligation {
            name: format!("{label}: {which}"),
            trust_ir_expr: intent,
            aarch64_expr: machine,
            inputs,
            preconditions: Vec::new(),
            fp_inputs: Vec::new(),
            category: Some(TransvalCheckKind::Vectorization),
            machine_side_provenance: MachineSideProvenance::Reconstructed {
                from_opcode: format!("{opcode:?}"),
                arity: 1,
            },
        },
    }
}

fn collect_vars(expr: &E, out: &mut Vec<(String, u32)>) {
    if let E::Var { name, width } = expr {
        if !out.iter().any(|(seen, _)| seen == name) {
            out.push((name.clone(), *width));
        }
        return;
    }
    expr.for_each_child(&mut |child| collect_vars(child, out));
}

// ---------------------------------------------------------------------------
// Terms
// ---------------------------------------------------------------------------

fn literal(word: u32) -> E {
    E::bv_const(u64::from(word), 32)
}

fn field(word: u32, hi: u32, lo: u32) -> E {
    literal(word).extract(hi, lo)
}

fn field_is(word: u32, hi: u32, lo: u32, value: u64) -> E {
    field(word, hi, lo).eq_expr(E::bv_const(value, hi - lo + 1))
}

/// Concatenated field values, most significant first: `(value, width)` pairs
/// (the key an `ite` over concatenated word fields compares with).
fn field_key(fields: &[(u64, u32)]) -> u64 {
    fields
        .iter()
        .fold(0, |key, &(value, width)| (key << width) | value)
}

fn zeros(width: u32) -> E {
    E::bv_const(0, width)
}

/// `x` zero-extended to 64 bits, spelled `(concat (_ bv0 k) x)` (no
/// `zero_extend`; see `aarch64_memory_effect::zero_extend`).
fn zext64(x: E) -> E {
    let width = x.bv_width();
    if width >= 64 {
        x
    } else {
        zeros(64 - width).concat(x)
    }
}

/// `x` replicated to fill 64 bits.
fn replicate64(x: E) -> E {
    let width = x.bv_width();
    let mut out = x.clone();
    for _ in 1..(64 / width) {
        out = x.clone().concat(out);
    }
    out
}

/// A register's 128-bit value reassembled from its halves (the machine view).
fn reg128(prefix: &str) -> E {
    E::var(format!("{prefix}_hi"), 64).concat(E::var(format!("{prefix}_lo"), 64))
}

fn arrangement_of_log2(log2: u32) -> A {
    match log2 {
        0 => A::B16,
        1 => A::H8,
        2 => A::S4,
        _ => A::D2,
    }
}

/// Element `index` of size `2^log2` bytes, sliced directly from the raw half
/// that holds it (the operands' view).
fn lane_of(prefix: &str, log2: u32, index: u32) -> E {
    let bits = 8u32 << log2;
    let per_half = 64 / bits;
    let (half, local) = if index < per_half {
        ("lo", index)
    } else {
        ("hi", index - per_half)
    };
    E::var(format!("{prefix}_{half}"), 64).extract(local * bits + bits - 1, local * bits)
}

/// Byte `index` (0..16) of a register, from the raw halves (operands' view).
fn byte_of_halves(prefix: &str, index: u32) -> E {
    lane_of(prefix, 0, index)
}

/// Byte `index` (0..16) of a register's reassembled 128-bit value (machine view).
fn byte_of_reg(reg: &E, index: u32) -> E {
    reg.clone().extract(8 * index + 7, 8 * index)
}

/// Concatenate bytes (byte 0 least significant) into a 64-bit value.
fn bytes64(bytes: Vec<E>) -> E {
    let mut iter = bytes.into_iter();
    let first = iter.next().expect("eight bytes");
    iter.fold(first, |acc, byte| byte.concat(acc))
}

/// `ite` chain choosing `branches[k]` where `selector == k`; the last
/// branch is the default.
fn select(selector: E, width: u32, branches: Vec<E>) -> E {
    let count = branches.len();
    let mut iter = branches.into_iter().enumerate().rev();
    let (_, last) = iter.next().expect("one branch");
    iter.fold(last, |acc, (k, branch)| {
        debug_assert!(k < count);
        E::ite(
            selector.clone().eq_expr(E::bv_const(k as u64, width)),
            branch,
            acc,
        )
    })
}

// ---------------------------------------------------------------------------
// fields
// ---------------------------------------------------------------------------

/// `(hi, lo, value)` of every non-immediate field, from the operands.
fn intended_fields(access: &NeonLaneAccess) -> Vec<(u32, u32, u64)> {
    let rd = u64::from(access.rd);
    let rn = u64::from(access.rn);
    let regs = [(9, 5, rn), (4, 0, rd)];
    let mut fields = match access.op {
        // Advanced SIMD copy: `0 Q op 01110000 imm5 0 imm4 1 Rn Rd`. The
        // element-size marker (the low bits of imm5) is pinned; the index
        // above it is the value parts'.
        LaneOp::DupElement { q, log2, .. } => copy_fields(q, log2, 0b0000),
        // DUP (general) reads no index: its whole imm5 is the operands'.
        LaneOp::DupGeneral { q, log2, .. } => {
            let mut fields = copy_fields(q, log2, 0b0001);
            fields.push((20, 16, u64::from(copy_imm5(log2, 0))));
            fields
        }
        LaneOp::InsGeneral { log2, .. } => copy_fields(true, log2, 0b0011),
        LaneOp::Umov { log2, .. } => copy_fields(log2 == 3, log2, 0b0111),
        // Advanced SIMD scalar copy: `01 op 11110000 imm5 0 imm4 1 Rn Rd`.
        LaneOp::DupScalarD { .. } => vec![
            (31, 30, 0b01),
            (29, 29, 0),
            (28, 21, 0b1111_0000),
            (19, 16, 0b1000),
            (15, 15, 0),
            (14, 11, 0b0000),
            (10, 10, 1),
        ],
        // Advanced SIMD across lanes: `0 Q U 01110 size 11000 opcode 10 Rn Rd`.
        LaneOp::Umaxv4S => vec![
            (31, 31, 0),
            (30, 30, 1),
            (29, 29, 1),
            (28, 24, 0b01110),
            (23, 22, 0b10),
            (21, 17, 0b11000),
            (16, 12, 0b01010),
            (11, 10, 0b10),
        ],
        // Advanced SIMD scalar pairwise: `01 U 11110 size 11000 opcode 10 Rn Rd`.
        LaneOp::Addp2D => vec![
            (31, 30, 0b01),
            (29, 29, 0),
            (28, 24, 0b11110),
            (23, 22, 0b11),
            (21, 17, 0b11000),
            (16, 12, 0b11011),
            (11, 10, 0b10),
        ],
        // Advanced SIMD two-register miscellaneous:
        // `0 Q U 01110 size 10000 opcode 10 Rn Rd`.
        LaneOp::Rev { q, container, log2 } => {
            two_misc_fields(q, u64::from(container == 32), u64::from(log2), 0b00000)
        }
        LaneOp::Rbit { q } => two_misc_fields(q, 1, 0b01, 0b00101),
        // Advanced SIMD extract: `0 Q 101110 op2 0 Rm 0 imm4 0 Rn Rd`; imm4 is
        // the value parts'.
        LaneOp::Ext { .. } => vec![
            (31, 31, 0),
            (30, 30, 1),
            (29, 24, 0b10_1110),
            (23, 22, 0b00),
            (21, 21, 0),
            (20, 16, u64::from(access.rm)),
            (15, 15, 0),
            (10, 10, 0),
        ],
        // Advanced SIMD modified immediate:
        // `0 Q op 0111100000 abc cmode o2 1 defgh Rd`; abc:defgh is the value
        // parts'.
        LaneOp::MoviByte { q, .. } => {
            return vec![
                (31, 31, 0),
                (30, 30, u64::from(q)),
                (29, 29, 0),
                (28, 19, 0b01_1110_0000),
                (15, 12, 0b1110),
                (11, 11, 0),
                (10, 10, 1),
                (4, 0, rd),
            ];
        }
    };
    fields.extend(regs);
    fields
}

fn copy_fields(q: bool, log2: u32, imm4: u64) -> Vec<(u32, u32, u64)> {
    vec![
        (31, 31, 0),
        (30, 30, u64::from(q)),
        (29, 29, 0),
        (28, 21, 0b0111_0000),
        (16 + log2, 16, 1 << log2),
        (15, 15, 0),
        (14, 11, imm4),
        (10, 10, 1),
    ]
}

fn two_misc_fields(q: bool, u: u64, size: u64, opcode: u64) -> Vec<(u32, u32, u64)> {
    vec![
        (31, 31, 0),
        (30, 30, u64::from(q)),
        (29, 29, u),
        (28, 24, 0b01110),
        (23, 22, size),
        (21, 17, 0b10000),
        (16, 12, opcode),
        (11, 10, 0b10),
    ]
}

fn fields_conjunction(access: &NeonLaneAccess, word: u32) -> E {
    let mut conjuncts = intended_fields(access)
        .into_iter()
        .map(|(hi, lo, value)| field_is(word, hi, lo, value));
    let first = conjuncts.next().unwrap_or_else(|| E::bool_const(true));
    conjuncts.fold(first, E::and_expr)
}

// ---------------------------------------------------------------------------
// The operands' values
// ---------------------------------------------------------------------------

/// The operands' 64-bit half `half` of the SIMD&FP destination.
fn intent_half(access: &NeonLaneAccess, half: u32) -> E {
    let vector = |q: bool, value: E| if half == 1 && !q { zeros(64) } else { value };
    match access.op {
        LaneOp::DupElement { q, log2, index } => vector(q, replicate64(lane_of("vn", log2, index))),
        LaneOp::DupGeneral { q, log2, source } => {
            vector(q, replicate64(source.value().extract((8 << log2) - 1, 0)))
        }
        LaneOp::InsGeneral {
            log2,
            index,
            source,
        } => {
            let bits = 8u32 << log2;
            let per_half = 64 / bits;
            let old = E::var(if half == 0 { "vd_lo" } else { "vd_hi" }, 64);
            if index / per_half != half {
                return old;
            }
            let local = index % per_half;
            let low = local * bits;
            let mut value = source.value().extract(bits - 1, 0);
            if low > 0 {
                value = value.concat(old.clone().extract(low - 1, 0));
            }
            if low + bits < 64 {
                value = old.extract(63, low + bits).concat(value);
            }
            value
        }
        LaneOp::Umov { .. } => unreachable!("UMOV states its GPR, not a half"),
        LaneOp::DupScalarD { index } => {
            if half == 0 {
                lane_of("vn", 3, index)
            } else {
                zeros(64)
            }
        }
        LaneOp::Umaxv4S => {
            if half == 0 {
                zext64(across(Across::Umax, A::S4, &reg128("vn")))
            } else {
                zeros(64)
            }
        }
        LaneOp::Addp2D => {
            if half == 0 {
                let vn = reg128("vn");
                lane_extract(&vn, A::D2, 0).bvadd(lane_extract(&vn, A::D2, 1))
            } else {
                zeros(64)
            }
        }
        LaneOp::Rev { q, container, log2 } => vector(
            q,
            bytes64(
                (0..8)
                    .map(|k| byte_of_halves("vn", rev_source(container, log2, 8 * half + k)))
                    .collect(),
            ),
        ),
        LaneOp::Rbit { q } => vector(q, rbit_half(|k| byte_of_halves("vn", 8 * half + k))),
        LaneOp::Ext { index } => bytes64(
            (0..8)
                .map(|k| {
                    let at = index + 8 * half + k;
                    if at < 16 {
                        byte_of_halves("vn", at)
                    } else {
                        byte_of_halves("vm", at - 16)
                    }
                })
                .collect(),
        ),
        LaneOp::MoviByte { q, imm8 } => vector(q, replicate64(E::bv_const(u64::from(imm8), 8))),
    }
}

/// The source byte of output byte `out` (0..16) of `REV<container>` at element
/// size `2^log2` bytes: the element order is reversed within each container.
fn rev_source(container: u32, log2: u32, out: u32) -> u32 {
    let container_bytes = container / 8;
    let element = 1u32 << log2;
    let base = out / container_bytes * container_bytes;
    let offset = out % container_bytes;
    let elements = container_bytes / element;
    let (index, within) = (offset / element, offset % element);
    base + (elements - 1 - index) * element + within
}

/// One 64-bit half of a per-byte bit reversal, from a byte accessor.
fn rbit_half(byte: impl Fn(u32) -> E) -> E {
    bytes64(
        (0..8)
            .map(|k| {
                let b = byte(k);
                let mut bits = b.clone().extract(7, 7);
                for p in 1..8 {
                    bits = b.clone().extract(7 - p, 7 - p).concat(bits);
                }
                bits
            })
            .collect(),
    )
}

/// A horizontal reduction kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Across {
    Umax,
    Smax,
    Umin,
    Smin,
    Add,
}

/// The linear left fold of `kind` over the lanes of `vn` at `arr` (the
/// `neon_semantics::encode_neon_umaxv` shape for `Umax`).
fn across(kind: Across, arr: A, vn: &E) -> E {
    let mut acc = lane_extract(vn, arr, 0);
    for index in 1..arr.lane_count() {
        let lane = lane_extract(vn, arr, index);
        acc = match kind {
            Across::Umax => E::ite(lane.clone().bvugt(acc.clone()), lane, acc),
            Across::Smax => E::ite(lane.clone().bvsgt(acc.clone()), lane, acc),
            Across::Umin => E::ite(lane.clone().bvult(acc.clone()), lane, acc),
            Across::Smin => E::ite(lane.clone().bvslt(acc.clone()), lane, acc),
            Across::Add => acc.bvadd(lane),
        };
    }
    acc
}

// ---------------------------------------------------------------------------
// The word's values
// ---------------------------------------------------------------------------

/// The element of size `2^log2` bytes the word's `imm5` index selects from the
/// reassembled `Vn`.
fn copy_selected(word: u32, vn: &E, log2: u32) -> E {
    let arr = arrangement_of_log2(log2);
    let index_bits = 4 - log2;
    select(
        field(word, 20, 17 + log2),
        index_bits,
        (0..arr.lane_count())
            .map(|k| lane_extract(vn, arr, k))
            .collect(),
    )
}

/// Choose among per-element-size values by the word's `imm5` marker: B
/// `xxxx1`, H `xxx10`, S `xx100`, else D.
fn by_copy_size(word: u32, per_size: impl Fn(u32) -> E) -> E {
    E::ite(
        field_is(word, 16, 16, 1),
        per_size(0),
        E::ite(
            field_is(word, 17, 16, 0b10),
            per_size(1),
            E::ite(field_is(word, 18, 16, 0b100), per_size(2), per_size(3)),
        ),
    )
}

/// The value one of the copy class's vector-destination operations writes
/// into half `half`, chosen by `imm4` (DUP element 0000, DUP general 0001,
/// INS general 0011; any other value writes zero here).
fn copy_vector_half(word: u32, half: u32) -> E {
    let vn = reg128("vn");
    // A general source in field 31 is the zero register.
    let xn = E::ite(field_is(word, 9, 5, 31), zeros(64), E::var("xn", 64));
    let dup_element = by_copy_size(word, |log2| replicate64(copy_selected(word, &vn, log2)));
    let dup_general = by_copy_size(word, |log2| {
        replicate64(xn.clone().extract((8 << log2) - 1, 0))
    });
    let ins_general = by_copy_size(word, |log2| {
        let bits = 8u32 << log2;
        let arr = arrangement_of_log2(log2);
        let vd = reg128("vd");
        let lanes: Vec<E> = (0..arr.lane_count())
            .map(|k| {
                let mut lanes: Vec<E> = (0..arr.lane_count())
                    .map(|j| lane_extract(&vd, arr, j))
                    .collect();
                lanes[k as usize] = xn.clone().extract(bits - 1, 0);
                crate::smt::concat_lanes(&lanes, arr).extract(64 * half + 63, 64 * half)
            })
            .collect();
        select(field(word, 20, 17 + log2), 4 - log2, lanes)
    });
    let value = E::ite(
        field_is(word, 14, 11, 0b0000),
        dup_element,
        E::ite(
            field_is(word, 14, 11, 0b0001),
            dup_general,
            E::ite(field_is(word, 14, 11, 0b0011), ins_general, zeros(64)),
        ),
    );
    if half == 0 {
        value
    } else {
        E::ite(field_is(word, 30, 30, 1), value, zeros(64))
    }
}

/// The general register a copy-class word writes: UMOV (`imm4 = 0111`)
/// zero-extends the selected element; SMOV (`0101`) sign-extends it to 64
/// bits (`Q = 1`) or to 32 bits with the upper word zero (`Q = 0`); any
/// other value writes zero here.
fn copy_gpr_machine(word: u32) -> E {
    let vn = reg128("vn");
    let umov = by_copy_size(word, |log2| zext64(copy_selected(word, &vn, log2)));
    let smov = by_copy_size(word, |log2| {
        let element = copy_selected(word, &vn, log2);
        let bits = 8u32 << log2;
        let wide = if bits < 64 {
            element.clone().sign_ext(64 - bits)
        } else {
            element.clone()
        };
        let narrow = if bits < 32 {
            zeros(32).concat(element.sign_ext(32 - bits))
        } else {
            zext64(element.extract(31, 0))
        };
        E::ite(field_is(word, 30, 30, 1), wide, narrow)
    });
    E::ite(
        field_is(word, 14, 11, 0b0111),
        umov,
        E::ite(field_is(word, 14, 11, 0b0101), smov, zeros(64)),
    )
}

/// The word's 64-bit half `half` of the SIMD&FP destination.
fn machine_half(access: &NeonLaneAccess, word: u32, half: u32) -> E {
    match access.op {
        LaneOp::DupElement { .. } | LaneOp::DupGeneral { .. } | LaneOp::InsGeneral { .. } => {
            copy_vector_half(word, half)
        }
        LaneOp::Umov { .. } => unreachable!("UMOV states its GPR, not a half"),
        // Scalar copy: the selected element, zero-extended; the rest of Qd
        // is zeroed.
        LaneOp::DupScalarD { .. } => {
            if half == 1 {
                return zeros(64);
            }
            let vn = reg128("vn");
            E::ite(
                field_is(word, 14, 11, 0b0000),
                by_copy_size(word, |log2| zext64(copy_selected(word, &vn, log2))),
                zeros(64),
            )
        }
        LaneOp::Umaxv4S => {
            if half == 1 {
                return zeros(64);
            }
            across_machine(word)
        }
        LaneOp::Addp2D => {
            if half == 1 {
                return zeros(64);
            }
            let vn = reg128("vn");
            // U:size:opcode = 0:11:11011 is ADDP; the other scalar pairwise
            // encodings are floating point and write zero here.
            E::ite(
                field(word, 29, 29)
                    .concat(field(word, 23, 22))
                    .concat(field(word, 16, 12))
                    .eq_expr(E::bv_const(
                        field_key(&[(0, 1), (0b11, 2), (0b11011, 5)]),
                        8,
                    )),
                lane_extract(&vn, A::D2, 0).bvadd(lane_extract(&vn, A::D2, 1)),
                zeros(64),
            )
        }
        LaneOp::Rev { .. } | LaneOp::Rbit { .. } => two_misc_machine(word, half),
        LaneOp::Ext { .. } => ext_machine(word, half),
        LaneOp::MoviByte { .. } => {
            let imm8 = field(word, 18, 16).concat(field(word, 9, 5));
            let value = E::ite(
                field(word, 29, 29)
                    .concat(field(word, 15, 11))
                    .eq_expr(E::bv_const(field_key(&[(0, 1), (0b1110, 4), (0, 1)]), 6)),
                replicate64(imm8),
                zeros(64),
            );
            if half == 0 {
                value
            } else {
                E::ite(field_is(word, 30, 30, 1), value, zeros(64))
            }
        }
    }
}

/// The across-lanes class: `U:opcode` selects UMAXV (1:01010), SMAXV
/// (0:01010), UMINV (1:11010), SMINV (0:11010) or ADDV (0:11011); `Q:size`
/// the arrangement (8B, 16B, 4H, 8H, 4S). The scalar result is
/// zero-extended into the low half; any other encoding writes zero here.
fn across_machine(word: u32) -> E {
    let vn = reg128("vn");
    let by_arrangement = |kind: Across| {
        let q_size = field(word, 30, 30).concat(field(word, 23, 22));
        let reduce = |arr: A| zext64(across(kind, arr, &vn));
        select(
            q_size,
            3,
            vec![
                reduce(A::B8),
                reduce(A::H4),
                zeros(64),
                zeros(64),
                reduce(A::B16),
                reduce(A::H8),
                reduce(A::S4),
                zeros(64),
            ],
        )
    };
    let key = field(word, 29, 29).concat(field(word, 16, 12));
    let is = |value: u64| key.clone().eq_expr(E::bv_const(value, 6));
    E::ite(
        is(0b1_01010),
        by_arrangement(Across::Umax),
        E::ite(
            is(0b0_01010),
            by_arrangement(Across::Smax),
            E::ite(
                is(0b1_11010),
                by_arrangement(Across::Umin),
                E::ite(
                    is(0b0_11010),
                    by_arrangement(Across::Smin),
                    E::ite(is(0b0_11011), by_arrangement(Across::Add), zeros(64)),
                ),
            ),
        ),
    )
}

/// The two-register miscellaneous class, `U:size:opcode`: REV64 at B/H/S
/// (`0:ss:00000`), REV32 at B/H (`1:ss:00000`), RBIT (`1:01:00101`); any
/// other encoding writes zero here. `Q = 0` reads and writes the low half
/// only.
fn two_misc_machine(word: u32, half: u32) -> E {
    let vn = reg128("vn");
    let rev = |container: u32, log2: u32| {
        bytes64(
            (0..8)
                .map(|k| byte_of_reg(&vn, rev_source(container, log2, 8 * half + k)))
                .collect(),
        )
    };
    let key = field(word, 29, 29)
        .concat(field(word, 23, 22))
        .concat(field(word, 16, 12));
    let is = |value: u64| key.clone().eq_expr(E::bv_const(value, 8));
    let value = E::ite(
        is(field_key(&[(0, 1), (0b00, 2), (0b00000, 5)])),
        rev(64, 0),
        E::ite(
            is(field_key(&[(0, 1), (0b01, 2), (0b00000, 5)])),
            rev(64, 1),
            E::ite(
                is(field_key(&[(0, 1), (0b10, 2), (0b00000, 5)])),
                rev(64, 2),
                E::ite(
                    is(field_key(&[(1, 1), (0b00, 2), (0b00000, 5)])),
                    rev(32, 0),
                    E::ite(
                        is(field_key(&[(1, 1), (0b01, 2), (0b00000, 5)])),
                        rev(32, 1),
                        E::ite(
                            is(field_key(&[(1, 1), (0b01, 2), (0b00101, 5)])),
                            rbit_half(|k| byte_of_reg(&vn, 8 * half + k)),
                            zeros(64),
                        ),
                    ),
                ),
            ),
        ),
    );
    if half == 0 {
        value
    } else {
        E::ite(field_is(word, 30, 30, 1), value, zeros(64))
    }
}

/// EXT: bytes `imm4 ..` of `Vm:Vn` (16 bytes each with `Q = 1`; the low 8 of
/// each with `Q = 0`, which writes zero into the upper half).
fn ext_machine(word: u32, half: u32) -> E {
    let (vn, vm) = (reg128("vn"), reg128("vm"));
    let wide = |index: u32| {
        bytes64(
            (0..8)
                .map(|k| {
                    let at = index + 8 * half + k;
                    if at < 16 {
                        byte_of_reg(&vn, at)
                    } else {
                        byte_of_reg(&vm, at - 16)
                    }
                })
                .collect(),
        )
    };
    let narrow = |index: u32| {
        if half == 1 {
            return zeros(64);
        }
        bytes64(
            (0..8)
                .map(|k| {
                    let at = (index & 7) + k;
                    if at < 8 {
                        byte_of_reg(&vn, at)
                    } else {
                        byte_of_reg(&vm, at - 8)
                    }
                })
                .collect(),
        )
    };
    let imm4 = field(word, 14, 11);
    E::ite(
        field_is(word, 30, 30, 1),
        select(imm4.clone(), 4, (0..16).map(wide).collect()),
        select(imm4, 4, (0..16).map(narrow).collect()),
    )
}

// ===========================================================================
// In-process decision
// ===========================================================================

/// How a part fared in process: never proof credit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InProcess {
    /// No counterexample: `Exhaustive` when decided for every input,
    /// `Statistical` when only the sampling lane judged it.
    Holds(VerificationStrength),
    /// A counterexample: the word does not perform the operands' operation.
    Refuted(String),
    /// The evaluator could not decide it.
    Undecided(String),
}

/// Decide one part: a ground part by one evaluation, a symbolic part by
/// [`decide_exactly`] when it applies, else by the sampling lane.
pub fn decide_in_process(
    part: &NeonLaneEffectObligation,
    config: &VerificationConfig,
) -> InProcess {
    let obligation = &part.obligation;
    if obligation.inputs.is_empty() {
        let env = crate::smt::EvalEnv::default();
        return match obligation.negated_equivalence().try_eval(&env) {
            Ok(result) => {
                if result.as_bool() {
                    InProcess::Refuted("the ground part evaluates false".into())
                } else {
                    InProcess::Holds(VerificationStrength::Exhaustive)
                }
            }
            Err(error) => InProcess::Undecided(error.to_string()),
        };
    }
    match decide_exactly(obligation) {
        Some(Ok(())) => return InProcess::Holds(VerificationStrength::Exhaustive),
        Some(Err(why)) => return InProcess::Refuted(why),
        None => {}
    }
    match memoized_verify_by_evaluation(obligation, config) {
        VerificationResult::Valid => InProcess::Holds(
            VerificationStrength::for_obligation_with_config(obligation, config),
        ),
        VerificationResult::Invalid { counterexample } => InProcess::Refuted(counterexample),
        VerificationResult::Unknown { reason } => InProcess::Undecided(reason),
    }
}

/// Decide a symbolic part for every input, or `None` when neither rule
/// applies.
///
/// * Two pure bit routings (each bit a constant or one input bit, `ite` on
///   the word's ground fields resolved) are equal for every input exactly
///   when their routings are equal, and a differing bit can be driven apart
///   (`aarch64_value_decode_proofs::exact_routing_equality`).
/// * Otherwise both sides are folded (every variable-free subterm evaluated,
///   every `ite` on a now-constant condition replaced by its taken branch);
///   two syntactically equal folded terms are equal for every input. Unequal
///   folded terms are not decided here.
///
/// Each rule is an identity of bit-vector semantics; still an in-process
/// decision, never a certificate.
pub fn decide_exactly(obligation: &ProofObligation) -> Option<Result<(), String>> {
    let (intent, machine) = (&obligation.trust_ir_expr, &obligation.aarch64_expr);
    if let Some(verdict) =
        crate::aarch64_value_decode_proofs::exact_routing_equality(intent, machine)
    {
        return Some(verdict.map_err(|mismatch| {
            format!(
                "bit {} is {:?} in the operands' value but {:?} in the word's",
                mismatch.bit, mismatch.intended, mismatch.emitted
            )
        }));
    }
    let (intent, machine) = (fold(intent)?, fold(machine)?);
    (intent == machine).then_some(Ok(()))
}

/// Whether [`decide_in_process`] reaches the sampling lane for this part.
pub fn needs_sampling(part: &NeonLaneEffectObligation) -> bool {
    !part.obligation.inputs.is_empty() && decide_exactly(&part.obligation).is_none()
}

fn mentions_a_variable(expr: &E) -> bool {
    if matches!(expr, E::Var { .. }) {
        return true;
    }
    let mut found = false;
    expr.for_each_child(&mut |child| found = found || mentions_a_variable(child));
    found
}

/// `expr` with every variable-free subterm evaluated and every `ite` on a
/// constant condition replaced by its taken branch; `None` for a node outside
/// the vocabulary the reduction parts use.
fn fold(expr: &E) -> Option<E> {
    use crate::smt::EvalResult;
    if !mentions_a_variable(expr) {
        let width = if matches!(
            expr,
            E::BoolConst(_)
                | E::Eq { .. }
                | E::And { .. }
                | E::Or { .. }
                | E::Not { .. }
                | E::BvUgt { .. }
                | E::BvSgt { .. }
                | E::BvUlt { .. }
                | E::BvSlt { .. }
        ) {
            0
        } else {
            expr.bv_width()
        };
        return match expr.try_eval(&crate::smt::EvalEnv::default()).ok()? {
            EvalResult::Bool(value) => Some(E::bool_const(value)),
            EvalResult::Bv(value) if width <= 64 => Some(E::bv_const(value, width)),
            EvalResult::Bv128(value) if width == 128 => {
                Some(E::bv_const((value >> 64) as u64, 64).concat(E::bv_const(value as u64, 64)))
            }
            _ => None,
        };
    }
    Some(match expr {
        E::Var { .. } => expr.clone(),
        E::Ite {
            cond,
            then_expr,
            else_expr,
        } => match fold(cond)? {
            E::BoolConst(true) => fold(then_expr)?,
            E::BoolConst(false) => fold(else_expr)?,
            cond => E::ite(cond, fold(then_expr)?, fold(else_expr)?),
        },
        E::Extract {
            high, low, operand, ..
        } => fold(operand)?.extract(*high, *low),
        E::Concat { hi, lo, .. } => fold(hi)?.concat(fold(lo)?),
        E::BvAdd { lhs, rhs, .. } => fold(lhs)?.bvadd(fold(rhs)?),
        E::BvUgt { lhs, rhs, .. } => fold(lhs)?.bvugt(fold(rhs)?),
        E::BvSgt { lhs, rhs, .. } => fold(lhs)?.bvsgt(fold(rhs)?),
        E::BvUlt { lhs, rhs, .. } => fold(lhs)?.bvult(fold(rhs)?),
        E::BvSlt { lhs, rhs, .. } => fold(lhs)?.bvslt(fold(rhs)?),
        E::Eq { lhs, rhs } => fold(lhs)?.eq_expr(fold(rhs)?),
        _ => return None,
    })
}

#[cfg(test)]
#[path = "aarch64_neon_lane_effect_tests.rs"]
mod tests;
