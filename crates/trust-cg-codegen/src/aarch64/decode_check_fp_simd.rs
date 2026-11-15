//! ENC-5 FP/SIMD slice: independent decode of scalar floating-point and
//! Advanced SIMD words.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
//!
//! Every function here extracts fields from an emitted word by the Arm ARM
//! (DDI 0487, C4.1 A64 encoding index) field layout of one encoding class,
//! requires every bit that is not a field to hold the class's fixed value,
//! and compares every field with what the `MachInst` intent names. It is
//! written from the encoding diagrams, not by calling or inverting
//! `aarch64::encoding_fp`/`encoding_neon`; only the intent's operand
//! conventions (operand order, the arrangement selectors) are shared with the
//! encoder, because they are the machine IR's contract. Because each checked
//! word is fully determined by the intent, flipping any single bit of a
//! matching word is a mismatch.
//!
//! A verdict is agreement between two independently written artifacts, the
//! same REDUNDANCY evidence as the rest of ENC-5. It is not a proof of the
//! encoding against a formal ISA model and says nothing about semantics.

use trust_cg_ir::inst::{AArch64Opcode, MachInst};
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::regs::SpecialReg;

/// Decode-check detail for a disagreement; `Ok` is a field-by-field match.
pub(super) type FieldCheck = Result<(), String>;

macro_rules! want {
    ($what:expr, $got:expr, $want:expr) => {
        if $got != $want {
            return Err(format!(
                "{}: decoded {} but the intent requires {}",
                $what, $got, $want
            ));
        }
    };
}

fn field(word: u32, high: u32, low: u32) -> u32 {
    (word >> low) & ((1u32 << (high - low + 1)) - 1)
}

/// Require the class's fixed bits: `word & mask == value`.
fn class(word: u32, mask: u32, value: u32, name: &str) -> FieldCheck {
    if word & mask == value {
        Ok(())
    } else {
        Err(format!(
            "{word:#010x} is not {name} (fixed bits {:#010x} under mask {mask:#010x}, required {value:#010x})",
            word & mask
        ))
    }
}

// ---------------------------------------------------------------------------
// Intent-side operand readers
// ---------------------------------------------------------------------------

/// Register bank of an FP/SIMD physical register.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FpBank {
    B,
    H,
    S,
    D,
    V,
}

/// An FP/SIMD physical register: its bank and 5-bit register number. GPRs,
/// zero/stack registers, virtual registers and non-register operands are not.
fn fp_reg(inst: &MachInst, index: usize) -> Option<(FpBank, u32)> {
    let MachOperand::PReg(p) = inst.operands.get(index)? else {
        return None;
    };
    let e = u32::from(p.encoding());
    match e {
        64..=95 => Some((FpBank::V, e - 64)),
        96..=127 => Some((FpBank::D, e - 96)),
        128..=159 => Some((FpBank::S, e - 128)),
        165..=196 => Some((FpBank::H, e - 165)),
        197..=228 => Some((FpBank::B, e - 197)),
        _ => None,
    }
}

/// A general-purpose data register: (sf, field). W/X or the matching zero
/// register; SP/WSP are refused because field 31 denotes ZR in these classes.
fn gpr_data(inst: &MachInst, index: usize) -> Option<(u32, u32)> {
    match inst.operands.get(index)? {
        MachOperand::PReg(p) => match p.encoding() {
            0..=30 => Some((1, u32::from(p.encoding()))),
            32..=62 => Some((0, u32::from(p.encoding() - 32))),
            160 => Some((1, 31)),
            161 => Some((0, 31)),
            _ => None,
        },
        MachOperand::Special(SpecialReg::XZR) => Some((1, 31)),
        MachOperand::Special(SpecialReg::WZR) => Some((0, 31)),
        _ => None,
    }
}

/// An X/SP address base register field (31 is SP in load/store bases).
fn address_base(inst: &MachInst, index: usize) -> Option<u32> {
    match inst.operands.get(index)? {
        MachOperand::PReg(p) if p.encoding() <= 31 => Some(u32::from(p.encoding())),
        MachOperand::Special(SpecialReg::SP) => Some(31),
        _ => None,
    }
}

fn imm(inst: &MachInst, index: usize) -> Option<i64> {
    match inst.operands.get(index)? {
        MachOperand::Imm(value) => Some(*value),
        _ => None,
    }
}

fn arity(inst: &MachInst, expected: usize) -> FieldCheck {
    if inst.operands.len() == expected {
        Ok(())
    } else {
        Err(format!(
            "{:?} takes exactly {expected} operands, the intent has {}",
            inst.opcode,
            inst.operands.len()
        ))
    }
}

/// Scalar FP `ftype` (Arm ARM: 00 single, 01 double, 11 half) and register
/// field of an H/S/D operand.
fn scalar_fp(inst: &MachInst, index: usize) -> Result<(u32, u32), String> {
    match fp_reg(inst, index) {
        Some((FpBank::S, n)) => Ok((0b00, n)),
        Some((FpBank::D, n)) => Ok((0b01, n)),
        Some((FpBank::H, n)) => Ok((0b11, n)),
        _ => Err(format!(
            "{:?} operand {index} must be a scalar H/S/D register, got {:?}",
            inst.opcode,
            inst.operands.get(index)
        )),
    }
}

/// Scalar FP operands that must share one `ftype`.
fn scalar_fp_same(inst: &MachInst, indices: &[usize]) -> Result<(u32, Vec<u32>), String> {
    let mut ftype = None;
    let mut regs = Vec::with_capacity(indices.len());
    for &index in indices {
        let (t, n) = scalar_fp(inst, index)?;
        if ftype.is_some_and(|f| f != t) {
            return Err(format!(
                "{:?} operands must share one scalar FP width",
                inst.opcode
            ));
        }
        ftype = Some(t);
        regs.push(n);
    }
    Ok((ftype.unwrap_or(0), regs))
}

/// A vector register for an operation of width `q`: Q=1 needs the 128-bit V
/// bank; Q=0 admits V or the 64-bit D view (both name the low 64 bits).
fn vector_reg(inst: &MachInst, index: usize, q: u32) -> Result<u32, String> {
    match (fp_reg(inst, index), q) {
        (Some((FpBank::V, n)), _) | (Some((FpBank::D, n)), 0) => Ok(n),
        (other, _) => Err(format!(
            "{:?} operand {index} must be a {} vector register, got {other:?}",
            inst.opcode,
            if q == 1 { "128-bit V" } else { "V or D" }
        )),
    }
}

/// The integer arrangement selector (the last operand): 0 = 8B, 1 = 16B,
/// 2 = 4H, 3 = 8H, 4 = 2S, 5 = 4S, 6 = 2D. Returns (Q, size).
fn int_arrangement(inst: &MachInst, index: usize) -> Result<(u32, u32), String> {
    match imm(inst, index) {
        Some(0) => Ok((0, 0b00)),
        Some(1) => Ok((1, 0b00)),
        Some(2) => Ok((0, 0b01)),
        Some(3) => Ok((1, 0b01)),
        Some(4) => Ok((0, 0b10)),
        Some(5) => Ok((1, 0b10)),
        Some(6) => Ok((1, 0b11)),
        other => Err(format!(
            "{:?} operand {index} must be an integer arrangement selector 0..=6, got {other:?}",
            inst.opcode
        )),
    }
}

/// The FP arrangement selector: 0 = 2S, 1 = 4S, 2 = 2D. Returns (Q, sz).
fn fp_arrangement(inst: &MachInst, index: usize) -> Result<(u32, u32), String> {
    match imm(inst, index) {
        Some(0) => Ok((0, 0)),
        Some(1) => Ok((1, 0)),
        Some(2) => Ok((1, 1)),
        other => Err(format!(
            "{:?} operand {index} must be an FP arrangement selector 0..=2, got {other:?}",
            inst.opcode
        )),
    }
}

/// Element size in bytes (1, 2, 4, 8) as `log2`.
fn element_log2(inst: &MachInst, index: usize) -> Result<u32, String> {
    match imm(inst, index) {
        Some(1) => Ok(0),
        Some(2) => Ok(1),
        Some(4) => Ok(2),
        Some(8) => Ok(3),
        other => Err(format!(
            "{:?} operand {index} must be an element size of 1, 2, 4 or 8 bytes, got {other:?}",
            inst.opcode
        )),
    }
}

/// The lane operand as an index below `lanes`.
fn lane(inst: &MachInst, index: usize, lanes: u32) -> Result<u32, String> {
    match imm(inst, index) {
        Some(value) if (0..i64::from(lanes)).contains(&value) => Ok(value as u32),
        other => Err(format!(
            "{:?} operand {index} must be a lane below {lanes}, got {other:?}",
            inst.opcode
        )),
    }
}

// ---------------------------------------------------------------------------
// Scalar floating point (Arm ARM C4.1, data processing -- scalar FP and
// Advanced SIMD)
// ---------------------------------------------------------------------------

/// Floating-point data-processing (2 source):
/// `M=0 | 0 | S=0 | 11110 | ftype | 1 | Rm | opcode | 10 | Rn | Rd`.
fn check_fp_dp2(inst: &MachInst, w: u32, opcode: u32) -> FieldCheck {
    arity(inst, 3)?;
    let (ftype, regs) = scalar_fp_same(inst, &[0, 1, 2])?;
    class(w, 0xFF20_0C00, 0x1E20_0800, "FP data-processing (2 source)")?;
    want!("fp-dp2 ftype", field(w, 23, 22), ftype);
    want!("fp-dp2 opcode", field(w, 15, 12), opcode);
    want!("fp-dp2 Rd", field(w, 4, 0), regs[0]);
    want!("fp-dp2 Rn", field(w, 9, 5), regs[1]);
    want!("fp-dp2 Rm", field(w, 20, 16), regs[2]);
    Ok(())
}

/// Floating-point data-processing (3 source):
/// `M=0 | 0 | S=0 | 11111 | ftype | o1 | Rm | o0 | Ra | Rn | Rd`.
/// FMADD is o1=0, o0=0; the intent is `[Rd, Rn, Rm, Ra]`.
fn check_fmadd(inst: &MachInst, w: u32) -> FieldCheck {
    arity(inst, 4)?;
    let (ftype, regs) = scalar_fp_same(inst, &[0, 1, 2, 3])?;
    class(w, 0xFF00_0000, 0x1F00_0000, "FP data-processing (3 source)")?;
    want!("fp-dp3 ftype", field(w, 23, 22), ftype);
    want!("fp-dp3 o1", field(w, 21, 21), 0);
    want!("fp-dp3 o0", field(w, 15, 15), 0);
    want!("fp-dp3 Rd", field(w, 4, 0), regs[0]);
    want!("fp-dp3 Rn", field(w, 9, 5), regs[1]);
    want!("fp-dp3 Rm", field(w, 20, 16), regs[2]);
    want!("fp-dp3 Ra", field(w, 14, 10), regs[3]);
    Ok(())
}

/// Floating-point data-processing (1 source):
/// `M=0 | 0 | S=0 | 11110 | ftype | 1 | opcode(6) | 10000 | Rn | Rd`.
/// `src_ftype` is the source width `ftype`; the destination width is the
/// same except for FCVT, whose opcode names it.
fn check_fp_dp1(w: u32, src_ftype: u32, opcode: u32, rn: u32, rd: u32) -> FieldCheck {
    class(w, 0xFF20_7C00, 0x1E20_4000, "FP data-processing (1 source)")?;
    want!("fp-dp1 ftype", field(w, 23, 22), src_ftype);
    want!("fp-dp1 opcode", field(w, 20, 15), opcode);
    want!("fp-dp1 Rd", field(w, 4, 0), rd);
    want!("fp-dp1 Rn", field(w, 9, 5), rn);
    Ok(())
}

fn check_fp_unary(inst: &MachInst, w: u32, opcode: u32) -> FieldCheck {
    arity(inst, 2)?;
    let (ftype, regs) = scalar_fp_same(inst, &[0, 1])?;
    check_fp_dp1(w, ftype, opcode, regs[1], regs[0])
}

/// FCVT (scalar precision conversion): FP data-processing (1 source) with
/// opcode `0001:opc`, where `opc` is the destination type (00 single,
/// 01 double, 11 half) and `ftype` the source type.
fn check_fcvt(inst: &MachInst, w: u32, src: u32, dst: u32) -> FieldCheck {
    arity(inst, 2)?;
    let (dst_type, rd) = scalar_fp(inst, 0)?;
    let (src_type, rn) = scalar_fp(inst, 1)?;
    if (dst_type, src_type) != (dst, src) {
        return Err(format!(
            "{:?} converts ftype {src:#04b} to {dst:#04b}; the intent names {src_type:#04b} to {dst_type:#04b}",
            inst.opcode
        ));
    }
    check_fp_dp1(w, src, 0b000100 | dst, rn, rd)
}

/// FCMP (register, quiet) of two half-precision registers `[Hn, Hm]`
/// (FEAT_FP16): floating-point compare
/// `M=0 | 0 | S=0 | 11110 | ftype=11 | 1 | Rm | op=00 | 1000 | Rn | opcode2`
/// with `opcode2 = 00000` (not signaling, not against zero). ENC-5's FCMP arm
/// decodes the S/D compares with the flag-consumer obligation's decoder; this
/// is the half-precision form, which that obligation does not model.
pub(super) fn check_fcmp_half(inst: &MachInst, w: u32) -> FieldCheck {
    arity(inst, 2)?;
    let (ftype, regs) = scalar_fp_same(inst, &[0, 1])?;
    if ftype != 0b11 {
        return Err(format!(
            "{:?} half-precision compare needs two H registers",
            inst.opcode
        ));
    }
    class(w, 0xFF20_FC00, 0x1E20_2000, "FP compare")?;
    want!("fcmp ftype", field(w, 23, 22), ftype);
    want!("fcmp opcode2", field(w, 4, 0), 0b00000);
    want!("fcmp Rn", field(w, 9, 5), regs[0]);
    want!("fcmp Rm", field(w, 20, 16), regs[1]);
    Ok(())
}

/// VFPExpandImm (Arm ARM shared pseudocode) of `imm8 = a:b:c:d:e:f:g:h` as
/// the exact binary64 value: sign a, exponent `NOT(b):Replicate(b,8):c:d`,
/// fraction `e:f:g:h` followed by zeros. Every such value is exact in half,
/// single and double precision.
fn vfp_expand_imm_f64(imm8: u32) -> f64 {
    let a = u64::from((imm8 >> 7) & 1);
    let b = u64::from((imm8 >> 6) & 1);
    let cd = u64::from((imm8 >> 4) & 0b11);
    let efgh = u64::from(imm8 & 0b1111);
    let exponent = ((b ^ 1) << 10) | (if b == 1 { 0xFF } else { 0 } << 2) | cd;
    f64::from_bits((a << 63) | (exponent << 52) | (efgh << 48))
}

/// Floating-point move immediate:
/// `M=0 | 0 | S=0 | 11110 | ftype | 1 | imm8 | 100 | imm5=00000 | Rd`.
fn check_fmov_imm(inst: &MachInst, w: u32) -> FieldCheck {
    arity(inst, 2)?;
    let (ftype, rd) = scalar_fp(inst, 0)?;
    class(w, 0xFF20_1FE0, 0x1E20_1000, "FP move immediate")?;
    want!("fmov-imm ftype", field(w, 23, 22), ftype);
    want!("fmov-imm Rd", field(w, 4, 0), rd);
    let imm8 = field(w, 20, 13);
    match inst.operands.get(1) {
        Some(MachOperand::FImm(value)) => {
            let decoded = vfp_expand_imm_f64(imm8);
            if decoded.to_bits() != value.to_bits() {
                return Err(format!(
                    "fmov-imm imm8 {imm8:#04x} expands to {decoded:?}, the intent names {value:?}"
                ));
            }
        }
        Some(MachOperand::Imm(value)) => want!("fmov-imm imm8", i64::from(imm8), *value),
        other => return Err(format!("FmovImm needs an FImm or raw imm8, got {other:?}")),
    }
    Ok(())
}

/// Conversion between floating-point and integer:
/// `sf | 0 | S=0 | 11110 | ftype | 1 | rmode | opcode(3) | 000000 | Rn | Rd`.
/// `int_index` is the GPR operand (Rd for FP->int, Rn for int->FP).
fn check_fp_int(inst: &MachInst, w: u32, rmode: u32, opcode: u32, int_index: usize) -> FieldCheck {
    arity(inst, 2)?;
    let fp_index = 1 - int_index;
    let Some((sf, gpr)) = gpr_data(inst, int_index) else {
        return Err(format!(
            "{:?} operand {int_index} must be a W/X register or ZR, got {:?}",
            inst.opcode,
            inst.operands.get(int_index)
        ));
    };
    let (ftype, fpr) = scalar_fp(inst, fp_index)?;
    let (rd, rn) = if int_index == 0 {
        (gpr, fpr)
    } else {
        (fpr, gpr)
    };
    class(
        w,
        0x7F20_FC00,
        0x1E20_0000,
        "conversion between FP and integer",
    )?;
    want!("fp-int sf", field(w, 31, 31), sf);
    want!("fp-int ftype", field(w, 23, 22), ftype);
    want!("fp-int rmode", field(w, 20, 19), rmode);
    want!("fp-int opcode", field(w, 18, 16), opcode);
    want!("fp-int Rd", field(w, 4, 0), rd);
    want!("fp-int Rn", field(w, 9, 5), rn);
    Ok(())
}

/// FMOV (general) additionally exists only for W<->S, X<->D and W/X<->H
/// (the W<->D and X<->S rows are unallocated).
fn check_fmov_general(inst: &MachInst, w: u32, to_fp: bool) -> FieldCheck {
    let (int_index, fp_index) = if to_fp { (1, 0) } else { (0, 1) };
    if let (Some((sf, _)), Ok((ftype, _))) = (gpr_data(inst, int_index), scalar_fp(inst, fp_index))
        && matches!((sf, ftype), (0, 0b01) | (1, 0b00))
    {
        return Err(format!(
            "FMOV (general) between sf={sf} and ftype={ftype:#04b} is unallocated"
        ));
    }
    check_fp_int(inst, w, 0b00, if to_fp { 0b111 } else { 0b110 }, int_index)
}

// ---------------------------------------------------------------------------
// Advanced SIMD
// ---------------------------------------------------------------------------

/// Any FP/SIMD register view (B/H/S/D/V) of a bitwise operation: the
/// logical class reads and writes whole lanes of bits, so a narrower view
/// (the machine IR's `ORR Vd.16B, Vn.16B, Vn.16B` copy of an H/S/D value)
/// names the same architectural register, and the width is the selector's.
fn bitwise_reg(inst: &MachInst, index: usize) -> Result<u32, String> {
    fp_reg(inst, index).map(|(_, n)| n).ok_or_else(|| {
        format!(
            "{:?} operand {index} must be an FP/SIMD register, got {:?}",
            inst.opcode,
            inst.operands.get(index)
        )
    })
}

/// Advanced SIMD three same:
/// `0 | Q | U | 01110 | size | 1 | Rm | opcode(5) | 1 | Rn | Rd`.
fn simd_three_same(inst: &MachInst, w: u32, q: u32, u: u32, size: u32, opcode: u32) -> FieldCheck {
    let rd = vector_reg(inst, 0, q)?;
    let rn = vector_reg(inst, 1, q)?;
    let rm = vector_reg(inst, 2, q)?;
    three_same_fields(w, q, u, size, opcode, rd, rn, rm)
}

#[allow(clippy::too_many_arguments)]
fn three_same_fields(
    w: u32,
    q: u32,
    u: u32,
    size: u32,
    opcode: u32,
    rd: u32,
    rn: u32,
    rm: u32,
) -> FieldCheck {
    class(w, 0x9F20_0400, 0x0E20_0400, "Advanced SIMD three same")?;
    want!("simd-3same Q", field(w, 30, 30), q);
    want!("simd-3same U", field(w, 29, 29), u);
    want!("simd-3same size", field(w, 23, 22), size);
    want!("simd-3same opcode", field(w, 15, 11), opcode);
    want!("simd-3same Rd", field(w, 4, 0), rd);
    want!("simd-3same Rn", field(w, 9, 5), rn);
    want!("simd-3same Rm", field(w, 20, 16), rm);
    Ok(())
}

/// Integer three-same with the arrangement selector as operand 3.
fn check_int_three_same(inst: &MachInst, w: u32, u: u32, opcode: u32) -> FieldCheck {
    arity(inst, 4)?;
    let (q, size) = int_arrangement(inst, 3)?;
    simd_three_same(inst, w, q, u, size, opcode)
}

/// FP three-same: `size = a:sz`, the FP arrangement selector as operand 3.
/// `Q = 0` with `sz = 1` (1D) is reserved, and no selector names it.
fn check_fp_three_same(inst: &MachInst, w: u32, u: u32, a: u32, opcode: u32) -> FieldCheck {
    arity(inst, 4)?;
    let (q, sz) = fp_arrangement(inst, 3)?;
    simd_three_same(inst, w, q, u, (a << 1) | sz, opcode)
}

/// Logical three-same (opcode 00011; `U:size` selects the operation). The
/// width is the trailing selector's when present (an integer arrangement
/// selector; a bitwise operation reads only its Q: 8B, 4H and 2S are 64-bit,
/// 16B, 8H, 4S and 2D 128-bit), or the destination view's without one (V is
/// 16B, any narrower view 8B).
fn check_simd_logical(inst: &MachInst, w: u32, u: u32, size: u32) -> FieldCheck {
    let q = logical_width(inst, 3)?;
    let (rd, rn, rm) = (
        bitwise_reg(inst, 0)?,
        bitwise_reg(inst, 1)?,
        bitwise_reg(inst, 2)?,
    );
    three_same_fields(w, q, u, size, 0b00011, rd, rn, rm)
}

fn logical_width(inst: &MachInst, selector_index: usize) -> Result<u32, String> {
    match inst.operands.len() {
        n if n == selector_index + 1 => int_arrangement(inst, selector_index).map(|(q, _)| q),
        n if n == selector_index => match fp_reg(inst, 0) {
            Some((FpBank::V, _)) => Ok(1),
            Some(_) => Ok(0),
            None => Err(format!(
                "{:?} destination must be an FP/SIMD register, got {:?}",
                inst.opcode,
                inst.operands.first()
            )),
        },
        n => Err(format!(
            "{:?} takes {selector_index} registers and an optional width selector, the intent has {n} operands",
            inst.opcode
        )),
    }
}

/// Advanced SIMD two-register miscellaneous:
/// `0 | Q | U | 01110 | size | 10000 | opcode(5) | 10 | Rn | Rd`.
/// `rd_q` is the width the destination register must have (it differs from
/// the source's only for the long forms).
#[allow(clippy::too_many_arguments)]
fn simd_two_misc(
    inst: &MachInst,
    w: u32,
    q: u32,
    u: u32,
    size: u32,
    opcode: u32,
    rd_q: u32,
    rn_q: u32,
) -> FieldCheck {
    let rd = vector_reg(inst, 0, rd_q)?;
    let rn = vector_reg(inst, 1, rn_q)?;
    two_misc_fields(w, q, u, size, opcode, rd, rn)
}

fn two_misc_fields(w: u32, q: u32, u: u32, size: u32, opcode: u32, rd: u32, rn: u32) -> FieldCheck {
    class(
        w,
        0x9F3E_0C00,
        0x0E20_0800,
        "Advanced SIMD two-register miscellaneous",
    )?;
    want!("simd-2misc Q", field(w, 30, 30), q);
    want!("simd-2misc U", field(w, 29, 29), u);
    want!("simd-2misc size", field(w, 23, 22), size);
    want!("simd-2misc opcode", field(w, 16, 12), opcode);
    want!("simd-2misc Rd", field(w, 4, 0), rd);
    want!("simd-2misc Rn", field(w, 9, 5), rn);
    Ok(())
}

/// NOT (vector): two-register miscellaneous `U = 1, size = 00, opcode =
/// 00101`, bitwise like the logical class (any register view).
fn check_not(inst: &MachInst, w: u32) -> FieldCheck {
    let q = logical_width(inst, 2)?;
    let (rd, rn) = (bitwise_reg(inst, 0)?, bitwise_reg(inst, 1)?);
    two_misc_fields(w, q, 1, 0b00, 0b00101, rd, rn)
}

/// Same-width two-register miscellaneous with the integer arrangement as
/// operand 2.
fn check_int_two_misc(inst: &MachInst, w: u32, u: u32, opcode: u32) -> FieldCheck {
    arity(inst, 3)?;
    let (q, size) = int_arrangement(inst, 2)?;
    simd_two_misc(inst, w, q, u, size, opcode, q, q)
}

/// Byte-lane two-register miscellaneous (CNT, NOT, RBIT): the arrangement is
/// 8B or 16B and `size` is part of the operation.
fn check_byte_two_misc(inst: &MachInst, w: u32, u: u32, size: u32, opcode: u32) -> FieldCheck {
    arity(inst, 3)?;
    let (q, element) = int_arrangement(inst, 2)?;
    if element != 0 {
        return Err(format!("{:?} is defined on 8B/16B only", inst.opcode));
    }
    simd_two_misc(inst, w, q, u, size, opcode, q, q)
}

/// Advanced SIMD three different:
/// `0 | Q | U | 01110 | size | 1 | Rm | opcode(4) | 00 | Rn | Rd`.
/// The .2D-from-.4S forms (the only ones the machine IR names): `Q` selects
/// the high-half ("2") variant, `size = 10`.
fn check_three_different(inst: &MachInst, w: u32, high: u32, u: u32, opcode: u32) -> FieldCheck {
    arity(inst, 4)?;
    if int_arrangement(inst, 3)? != (1, 0b10) {
        return Err(format!(
            "{:?} widens .4S sources only (selector 5)",
            inst.opcode
        ));
    }
    let rd = vector_reg(inst, 0, 1)?;
    let rn = vector_reg(inst, 1, 1)?;
    let rm = vector_reg(inst, 2, 1)?;
    class(w, 0x9F20_0C00, 0x0E20_0000, "Advanced SIMD three different")?;
    want!("simd-3diff Q", field(w, 30, 30), high);
    want!("simd-3diff U", field(w, 29, 29), u);
    want!("simd-3diff size", field(w, 23, 22), 0b10);
    want!("simd-3diff opcode", field(w, 15, 12), opcode);
    want!("simd-3diff Rd", field(w, 4, 0), rd);
    want!("simd-3diff Rn", field(w, 9, 5), rn);
    want!("simd-3diff Rm", field(w, 20, 16), rm);
    Ok(())
}

/// FMLA (by element), Advanced SIMD vector x indexed element:
/// `0 | Q | U=0 | 01111 | size=1:sz | L | M | Rm(4) | opcode=0001 | H | 0 | Rn | Rd`.
/// Single: index `H:L`, Vm `M:Rm`. Double: index `H`, `L = 0`.
fn check_fmla_lane(inst: &MachInst, w: u32) -> FieldCheck {
    arity(inst, 5)?;
    let (q, sz) = fp_arrangement(inst, 4)?;
    if q == 0 {
        return Err("FMLA (by element) .2S is not a machine-IR form".to_string());
    }
    let index = lane(inst, 3, if sz == 1 { 2 } else { 4 })?;
    let rd = vector_reg(inst, 0, 1)?;
    let rn = vector_reg(inst, 1, 1)?;
    let rm = vector_reg(inst, 2, 1)?;
    class(
        w,
        0x9F00_0400,
        0x0F00_0000,
        "Advanced SIMD vector x indexed element",
    )?;
    want!("simd-elem Q", field(w, 30, 30), 1);
    want!("simd-elem U", field(w, 29, 29), 0);
    want!("simd-elem size", field(w, 23, 22), 0b10 | sz);
    want!("simd-elem opcode", field(w, 15, 12), 0b0001);
    let (h, l) = if sz == 1 {
        (index, 0)
    } else {
        (index >> 1, index & 1)
    };
    want!("simd-elem H", field(w, 11, 11), h);
    want!("simd-elem L", field(w, 21, 21), l);
    want!("simd-elem M:Rm", field(w, 20, 16), rm);
    want!("simd-elem Rd", field(w, 4, 0), rd);
    want!("simd-elem Rn", field(w, 9, 5), rn);
    Ok(())
}

/// `imm5` of the copy classes for an element of `2^log2` bytes at `index`:
/// B `xxxx1`, H `xxx10`, S `xx100`, D `x1000`, the index above the marker.
fn copy_imm5(log2: u32, index: u32) -> u32 {
    (index << (log2 + 1)) | (1 << log2)
}

/// Advanced SIMD copy:
/// `0 | Q | op | 01110000 | imm5 | 0 | imm4 | 1 | Rn | Rd`.
fn simd_copy(w: u32, q: u32, imm5: u32, imm4: u32, rn: u32, rd: u32) -> FieldCheck {
    class(w, 0x9FE0_8400, 0x0E00_0400, "Advanced SIMD copy")?;
    want!("simd-copy Q", field(w, 30, 30), q);
    want!("simd-copy op", field(w, 29, 29), 0);
    want!("simd-copy imm5", field(w, 20, 16), imm5);
    want!("simd-copy imm4", field(w, 14, 11), imm4);
    want!("simd-copy Rd", field(w, 4, 0), rd);
    want!("simd-copy Rn", field(w, 9, 5), rn);
    Ok(())
}

/// The vector width of a DUP destination: V is 128-bit, D 64-bit.
fn dup_q(inst: &MachInst) -> Result<(u32, u32), String> {
    match fp_reg(inst, 0) {
        Some((FpBank::V, n)) => Ok((1, n)),
        Some((FpBank::D, n)) => Ok((0, n)),
        other => Err(format!(
            "{:?} destination must be a V or D register, got {other:?}",
            inst.opcode
        )),
    }
}

/// DUP (element): `imm4 = 0000`; intent `[Vd, Vn, lane, element bytes]`.
/// The source is a V register, or the scalar view (B/H/S/D) of exactly the
/// element being broadcast: the same size, lane 0.
fn check_dup_element(inst: &MachInst, w: u32) -> FieldCheck {
    arity(inst, 4)?;
    let (q, rd) = dup_q(inst)?;
    let log2 = element_log2(inst, 3)?;
    if q == 0 && log2 == 3 {
        return Err("DUP (element) .1D is reserved".to_string());
    }
    let index = lane(inst, 2, 16 >> log2)?;
    let rn = match (fp_reg(inst, 1), log2, index) {
        (Some((FpBank::V, n)), _, _)
        | (Some((FpBank::B, n)), 0, 0)
        | (Some((FpBank::H, n)), 1, 0)
        | (Some((FpBank::S, n)), 2, 0)
        | (Some((FpBank::D, n)), 3, 0) => n,
        (other, _, _) => {
            return Err(format!(
                "NeonDupElem source must be a V register or the scalar view of lane 0 of \
                 its {}-byte element, got {other:?} for lane {index}",
                1 << log2
            ));
        }
    };
    simd_copy(w, q, copy_imm5(log2, index), 0b0000, rn, rd)
}

/// DUP (general): `imm4 = 0001`; intent `[Vd, Rn, element bytes]`. The
/// source is W for B/H/S elements and X for D.
fn check_dup_general(inst: &MachInst, w: u32) -> FieldCheck {
    arity(inst, 3)?;
    let (q, rd) = dup_q(inst)?;
    let log2 = element_log2(inst, 2)?;
    if q == 0 && log2 == 3 {
        return Err("DUP (general) .1D is reserved".to_string());
    }
    let rn = general_source(inst, 1, log2)?;
    simd_copy(w, q, copy_imm5(log2, 0), 0b0001, rn, rd)
}

/// A general-register source of a copy: the instruction reads Wn (the low
/// bits) for B/H/S elements, so either view names it, and all of Xn for D,
/// which a W view does not define.
fn general_source(inst: &MachInst, index: usize, log2: u32) -> Result<u32, String> {
    match gpr_data(inst, index) {
        Some((sf, n)) if log2 < 3 || sf == 1 => Ok(n),
        other => Err(format!(
            "{:?} operand {index} must be a GPR (an X register for 8-byte elements), \
             got {other:?} for {}-byte elements",
            inst.opcode,
            1 << log2
        )),
    }
}

/// A general-register destination of UMOV: W for B/H/S elements, X for D.
fn general_destination(inst: &MachInst, index: usize, log2: u32) -> Result<u32, String> {
    match gpr_data(inst, index) {
        Some((sf, n)) if sf == u32::from(log2 == 3) => Ok(n),
        other => Err(format!(
            "{:?} operand {index} must be a {} register for {}-byte elements, got {other:?}",
            inst.opcode,
            if log2 == 3 { "X" } else { "W" },
            1 << log2
        )),
    }
}

/// INS (general): `Q = 1, imm4 = 0011`; intent `[Vd, Rn, lane, element bytes]`.
fn check_ins_general(inst: &MachInst, w: u32) -> FieldCheck {
    arity(inst, 4)?;
    let rd = vector_reg(inst, 0, 1)?;
    let log2 = element_log2(inst, 3)?;
    let index = lane(inst, 2, 16 >> log2)?;
    let rn = general_source(inst, 1, log2)?;
    simd_copy(w, 1, copy_imm5(log2, index), 0b0011, rn, rd)
}

/// UMOV: `imm4 = 0111`, `Q = 1` only for the D element (Xd); intent
/// `[Wd/Xd, Vn, lane, element bytes]`.
fn check_umov(inst: &MachInst, w: u32) -> FieldCheck {
    arity(inst, 4)?;
    let log2 = element_log2(inst, 3)?;
    let index = lane(inst, 2, 16 >> log2)?;
    let rd = general_destination(inst, 0, log2)?;
    let rn = vector_reg(inst, 1, 1)?;
    simd_copy(
        w,
        u32::from(log2 == 3),
        copy_imm5(log2, index),
        0b0111,
        rn,
        rd,
    )
}

/// DUP (element, scalar), Advanced SIMD scalar copy:
/// `01 | op=0 | 11110000 | imm5 | 0 | imm4=0000 | 1 | Rn | Rd`; intent
/// `[Dd, Vn, lane]` (the D element).
fn check_dup_scalar_d(inst: &MachInst, w: u32) -> FieldCheck {
    arity(inst, 3)?;
    let rd = match fp_reg(inst, 0) {
        Some((FpBank::D, n)) => n,
        other => {
            return Err(format!(
                "NeonDupScalarD destination must be D, got {other:?}"
            ));
        }
    };
    let rn = vector_reg(inst, 1, 1)?;
    let index = lane(inst, 2, 2)?;
    class(w, 0xDFE0_8400, 0x5E00_0400, "Advanced SIMD scalar copy")?;
    want!("simd-scalar-copy op", field(w, 29, 29), 0);
    want!(
        "simd-scalar-copy imm5",
        field(w, 20, 16),
        copy_imm5(3, index)
    );
    want!("simd-scalar-copy imm4", field(w, 14, 11), 0);
    want!("simd-scalar-copy Rd", field(w, 4, 0), rd);
    want!("simd-scalar-copy Rn", field(w, 9, 5), rn);
    Ok(())
}

/// MOVI (8-bit, byte lanes), Advanced SIMD modified immediate:
/// `0 | Q | op=0 | 0111100000 | a:b:c | cmode=1110 | o2=0 | 1 | d:e:f:g:h | Rd`.
fn check_movi(inst: &MachInst, w: u32) -> FieldCheck {
    arity(inst, 2)?;
    let (q, rd) = dup_q(inst)?;
    let Some(imm8 @ 0..=255) = imm(inst, 1) else {
        return Err(format!(
            "NeonMovi needs an 8-bit immediate, got {:?}",
            inst.operands.get(1)
        ));
    };
    class(
        w,
        0x9FF8_0400,
        0x0F00_0400,
        "Advanced SIMD modified immediate",
    )?;
    want!("movi Q", field(w, 30, 30), q);
    want!("movi op", field(w, 29, 29), 0);
    want!("movi cmode", field(w, 15, 12), 0b1110);
    want!("movi o2", field(w, 11, 11), 0);
    want!(
        "movi imm8",
        i64::from((field(w, 18, 16) << 5) | field(w, 9, 5)),
        imm8
    );
    want!("movi Rd", field(w, 4, 0), rd);
    Ok(())
}

/// SHL/SSHR/USHR (vector), Advanced SIMD shift by immediate:
/// `0 | Q | U | 011110 | immh | immb | opcode(5) | 1 | Rn | Rd`, `immh != 0`.
/// The element size is the highest set bit of `immh`; a left shift encodes
/// `immh:immb = esize + shift`, a right shift `2*esize - shift`.
fn check_shift_imm(inst: &MachInst, w: u32, u: u32, opcode: u32, right: bool) -> FieldCheck {
    arity(inst, 4)?;
    let (q, size) = int_arrangement(inst, 3)?;
    let esize = 8i64 << size;
    let shift = imm(inst, 2).ok_or_else(|| {
        format!(
            "{:?} needs an immediate shift, got {:?}",
            inst.opcode,
            inst.operands.get(2)
        )
    })?;
    let valid = if right {
        (1..=esize).contains(&shift)
    } else {
        (0..esize).contains(&shift)
    };
    if !valid {
        return Err(format!(
            "{:?} shift {shift} is outside the {esize}-bit lane range",
            inst.opcode
        ));
    }
    let rd = vector_reg(inst, 0, q)?;
    let rn = vector_reg(inst, 1, q)?;
    class(
        w,
        0x9F80_0400,
        0x0F00_0400,
        "Advanced SIMD shift by immediate",
    )?;
    let immh = field(w, 22, 19);
    if immh == 0 {
        return Err(format!(
            "{w:#010x} has immh = 0 (modified immediate, not a shift)"
        ));
    }
    let decoded_esize = 8i64 << (31 - immh.leading_zeros());
    let immhb = i64::from(field(w, 22, 16));
    let decoded_shift = if right {
        2 * decoded_esize - immhb
    } else {
        immhb - decoded_esize
    };
    want!("simd-shift Q", field(w, 30, 30), q);
    want!("simd-shift U", field(w, 29, 29), u);
    want!("simd-shift opcode", field(w, 15, 11), opcode);
    want!("simd-shift element bits", decoded_esize, esize);
    want!("simd-shift amount", decoded_shift, shift);
    want!("simd-shift Rd", field(w, 4, 0), rd);
    want!("simd-shift Rn", field(w, 9, 5), rn);
    Ok(())
}

/// EXT, Advanced SIMD extract:
/// `0 | Q | 101110 | op2=00 | 0 | Rm | 0 | imm4 | 0 | Rn | Rd`; intent
/// `[Vd, Vn, Vm, #bytes]` on 16B.
fn check_ext(inst: &MachInst, w: u32) -> FieldCheck {
    arity(inst, 4)?;
    let Some(bytes @ 0..=15) = imm(inst, 3) else {
        return Err(format!(
            "NeonExtV byte index must be in 0..=15, got {:?}",
            inst.operands.get(3)
        ));
    };
    let rd = vector_reg(inst, 0, 1)?;
    let rn = vector_reg(inst, 1, 1)?;
    let rm = vector_reg(inst, 2, 1)?;
    class(w, 0xBFE0_8400, 0x2E00_0000, "Advanced SIMD extract")?;
    want!("ext Q", field(w, 30, 30), 1);
    want!("ext imm4", i64::from(field(w, 14, 11)), bytes);
    want!("ext Rd", field(w, 4, 0), rd);
    want!("ext Rn", field(w, 9, 5), rn);
    want!("ext Rm", field(w, 20, 16), rm);
    Ok(())
}

/// UDOT (vector), Advanced SIMD three same (extra):
/// `0 | Q | U=1 | 01110 | size=10 | 0 | Rm | 1 | opcode=0010 | 1 | Rn | Rd`;
/// intent `[Vd.4S, Vn.16B, Vm.16B, selector 1 (16B)]`.
fn check_udot(inst: &MachInst, w: u32) -> FieldCheck {
    arity(inst, 4)?;
    if int_arrangement(inst, 3)? != (1, 0b00) {
        return Err("NeonUdotV multiplies 16B sources only (selector 1)".to_string());
    }
    let rd = vector_reg(inst, 0, 1)?;
    let rn = vector_reg(inst, 1, 1)?;
    let rm = vector_reg(inst, 2, 1)?;
    class(
        w,
        0x9F20_8400,
        0x0E00_8400,
        "Advanced SIMD three same (extra)",
    )?;
    want!("udot Q", field(w, 30, 30), 1);
    want!("udot U", field(w, 29, 29), 1);
    want!("udot size", field(w, 23, 22), 0b10);
    want!("udot opcode", field(w, 14, 11), 0b0010);
    want!("udot Rd", field(w, 4, 0), rd);
    want!("udot Rn", field(w, 9, 5), rn);
    want!("udot Rm", field(w, 20, 16), rm);
    Ok(())
}

/// UMAXV, Advanced SIMD across lanes:
/// `0 | Q | U | 01110 | size | 11000 | opcode(5) | 10 | Rn | Rd`; intent
/// `[Sd, Vn, selector 5 (4S)]`.
fn check_umaxv(inst: &MachInst, w: u32) -> FieldCheck {
    arity(inst, 3)?;
    if int_arrangement(inst, 2)? != (1, 0b10) {
        return Err("NeonUmaxv reduces .4S only (selector 5)".to_string());
    }
    let rd = match fp_reg(inst, 0) {
        Some((FpBank::S, n)) => n,
        other => return Err(format!("NeonUmaxv destination must be S, got {other:?}")),
    };
    let rn = vector_reg(inst, 1, 1)?;
    class(w, 0x9F3E_0C00, 0x0E30_0800, "Advanced SIMD across lanes")?;
    want!("across Q", field(w, 30, 30), 1);
    want!("across U", field(w, 29, 29), 1);
    want!("across size", field(w, 23, 22), 0b10);
    want!("across opcode", field(w, 16, 12), 0b01010);
    want!("across Rd", field(w, 4, 0), rd);
    want!("across Rn", field(w, 9, 5), rn);
    Ok(())
}

/// ADDP (scalar), Advanced SIMD scalar pairwise:
/// `01 | U=0 | 11110 | size=11 | 11000 | opcode=11011 | 10 | Rn | Rd`; intent
/// `[Dd, Vn, selector 6 (2D)]`.
fn check_addp_scalar(inst: &MachInst, w: u32) -> FieldCheck {
    arity(inst, 3)?;
    if int_arrangement(inst, 2)? != (1, 0b11) {
        return Err("NeonAddpScalar reduces .2D only (selector 6)".to_string());
    }
    let rd = match fp_reg(inst, 0) {
        Some((FpBank::D, n)) => n,
        other => {
            return Err(format!(
                "NeonAddpScalar destination must be D, got {other:?}"
            ));
        }
    };
    let rn = vector_reg(inst, 1, 1)?;
    class(w, 0xDF3E_0C00, 0x5E30_0800, "Advanced SIMD scalar pairwise")?;
    want!("scalar-pairwise U", field(w, 29, 29), 0);
    want!("scalar-pairwise size", field(w, 23, 22), 0b11);
    want!("scalar-pairwise opcode", field(w, 16, 12), 0b11011);
    want!("scalar-pairwise Rd", field(w, 4, 0), rd);
    want!("scalar-pairwise Rn", field(w, 9, 5), rn);
    Ok(())
}

/// LD1/ST1 (multiple structures, one register), post-index by the transfer
/// size: Advanced SIMD load/store multiple structures (post-indexed)
/// `0 | Q | 0011001 | L | 0 | Rm=11111 | opcode=0111 | size | Rn | Rt`;
/// intent `[Vt, Xn|SP, selector]`.
fn check_ld1_st1_post(inst: &MachInst, w: u32, load: bool) -> FieldCheck {
    arity(inst, 3)?;
    let (q, size) = int_arrangement(inst, 2)?;
    let rt = vector_reg(inst, 0, q)?;
    let Some(rn) = address_base(inst, 1) else {
        return Err(format!(
            "{:?} base must be an X register or SP, got {:?}",
            inst.opcode,
            inst.operands.get(1)
        ));
    };
    class(
        w,
        0xBFA0_0000,
        0x0C80_0000,
        "Advanced SIMD load/store multiple structures (post-indexed)",
    )?;
    want!("ld1/st1 Q", field(w, 30, 30), q);
    want!("ld1/st1 L", field(w, 22, 22), u32::from(load));
    want!(
        "ld1/st1 Rm (immediate post-index)",
        field(w, 20, 16),
        0b11111
    );
    want!("ld1/st1 opcode (one register)", field(w, 15, 12), 0b0111);
    want!("ld1/st1 size", field(w, 11, 10), size);
    want!("ld1/st1 Rt", field(w, 4, 0), rt);
    want!("ld1/st1 Rn", field(w, 9, 5), rn);
    Ok(())
}

/// The FP/SIMD slice of ENC-5: `None` for an opcode this slice does not
/// own; otherwise the field-by-field verdict for `w`.
pub(super) fn check_fp_simd(inst: &MachInst, w: u32) -> Option<FieldCheck> {
    use AArch64Opcode as Op;
    Some(match inst.opcode {
        // ---- Scalar FP data-processing (2 source) ----------------------
        Op::FmulRR => check_fp_dp2(inst, w, 0b0000),
        Op::FdivRR => check_fp_dp2(inst, w, 0b0001),
        Op::FaddRR => check_fp_dp2(inst, w, 0b0010),
        Op::FsubRR => check_fp_dp2(inst, w, 0b0011),
        Op::FmaxnmRR => check_fp_dp2(inst, w, 0b0110),
        Op::FminnmRR => check_fp_dp2(inst, w, 0b0111),
        // ---- Scalar FP data-processing (3 source) ----------------------
        Op::FmaddRR => check_fmadd(inst, w),
        // ---- Scalar FP data-processing (1 source) ----------------------
        Op::FmovFprFpr => check_fp_unary(inst, w, 0b000000),
        Op::FabsRR => check_fp_unary(inst, w, 0b000001),
        Op::FnegRR => check_fp_unary(inst, w, 0b000010),
        Op::FsqrtRR => check_fp_unary(inst, w, 0b000011),
        // FRINT<rmode>: opcode `001:rmode`, rmode N=000 (ties to even),
        // P=001, M=010, Z=011.
        Op::FrintnRR => check_fp_unary(inst, w, 0b001000),
        Op::FrintpRR => check_fp_unary(inst, w, 0b001001),
        Op::FrintmRR => check_fp_unary(inst, w, 0b001010),
        Op::FrintzRR => check_fp_unary(inst, w, 0b001011),
        Op::FcvtSD => check_fcvt(inst, w, 0b00, 0b01),
        Op::FcvtDS => check_fcvt(inst, w, 0b01, 0b00),
        Op::FcvtHS => check_fcvt(inst, w, 0b11, 0b00),
        Op::FcvtHD => check_fcvt(inst, w, 0b11, 0b01),
        Op::FcvtSH => check_fcvt(inst, w, 0b00, 0b11),
        Op::FcvtDH => check_fcvt(inst, w, 0b01, 0b11),
        // ---- Scalar FP immediate / FP<->integer conversion -------------
        Op::FmovImm => check_fmov_imm(inst, w),
        Op::FcvtzsRR => check_fp_int(inst, w, 0b11, 0b000, 0),
        Op::FcvtzuRR => check_fp_int(inst, w, 0b11, 0b001, 0),
        Op::ScvtfRR => check_fp_int(inst, w, 0b00, 0b010, 1),
        Op::UcvtfRR => check_fp_int(inst, w, 0b00, 0b011, 1),
        Op::FmovGprFpr => check_fmov_general(inst, w, true),
        Op::FmovFprGpr => check_fmov_general(inst, w, false),
        // ---- Advanced SIMD three same (integer) ------------------------
        Op::NeonAddV => check_int_three_same(inst, w, 0, 0b10000),
        Op::NeonSubV => check_int_three_same(inst, w, 1, 0b10000),
        Op::NeonMulV => {
            if int_arrangement(inst, 3).is_ok_and(|(_, size)| size == 0b11) {
                Err("MUL (vector) .2D is reserved".to_string())
            } else {
                check_int_three_same(inst, w, 0, 0b10011)
            }
        }
        Op::NeonMlaV => {
            if int_arrangement(inst, 3).is_ok_and(|(_, size)| size == 0b11) {
                Err("MLA (vector) .2D is reserved".to_string())
            } else {
                check_int_three_same(inst, w, 0, 0b10010)
            }
        }
        Op::NeonSmaxV => check_int_three_same(inst, w, 0, 0b01100),
        Op::NeonSminV => check_int_three_same(inst, w, 0, 0b01101),
        Op::NeonUmaxV => check_int_three_same(inst, w, 1, 0b01100),
        Op::NeonUminV => check_int_three_same(inst, w, 1, 0b01101),
        Op::NeonCmgtV => check_int_three_same(inst, w, 0, 0b00110),
        Op::NeonCmgeV => check_int_three_same(inst, w, 0, 0b00111),
        Op::NeonCmhiV => check_int_three_same(inst, w, 1, 0b00110),
        Op::NeonCmhsV => check_int_three_same(inst, w, 1, 0b00111),
        Op::NeonCmeqV => check_int_three_same(inst, w, 1, 0b10001),
        // ---- Advanced SIMD three same (logical) ------------------------
        Op::NeonAndV => check_simd_logical(inst, w, 0, 0b00),
        Op::NeonBicV => check_simd_logical(inst, w, 0, 0b01),
        Op::NeonOrrV => check_simd_logical(inst, w, 0, 0b10),
        Op::NeonEorV => check_simd_logical(inst, w, 1, 0b00),
        Op::NeonBitV => check_simd_logical(inst, w, 1, 0b10),
        // ---- Advanced SIMD three same (FP), size = a:sz ----------------
        Op::NeonFaddV => check_fp_three_same(inst, w, 0, 0, 0b11010),
        Op::NeonFsubV => check_fp_three_same(inst, w, 0, 1, 0b11010),
        Op::NeonFmulV => check_fp_three_same(inst, w, 1, 0, 0b11011),
        Op::NeonFdivV => check_fp_three_same(inst, w, 1, 0, 0b11111),
        Op::NeonFmlaV => check_fp_three_same(inst, w, 0, 0, 0b11001),
        Op::NeonFmlsV => check_fp_three_same(inst, w, 0, 1, 0b11001),
        Op::NeonFcmgtV => check_fp_three_same(inst, w, 1, 1, 0b11100),
        // ---- Advanced SIMD two-register miscellaneous ------------------
        Op::NeonNotV => check_not(inst, w),
        Op::NeonCntV => check_byte_two_misc(inst, w, 0, 0b00, 0b00101),
        Op::NeonRbitV => check_byte_two_misc(inst, w, 1, 0b01, 0b00101),
        Op::NeonRev64V => check_int_two_misc(inst, w, 0, 0b00000),
        Op::NeonRev32V => check_int_two_misc(inst, w, 1, 0b00000),
        Op::NeonAbsV => check_int_two_misc(inst, w, 0, 0b01011),
        // The long pairwise adds read `Vn` at the selector's arrangement and
        // write the widened, half-lane-count arrangement of the same width.
        Op::NeonSaddlpV => check_int_two_misc(inst, w, 0, 0b00010),
        Op::NeonUaddlpV => check_int_two_misc(inst, w, 1, 0b00010),
        Op::NeonUadalpV => check_int_two_misc(inst, w, 1, 0b00110),
        // SCVTF/UCVTF (vector, integer): size = 0:sz.
        Op::NeonScvtfV | Op::NeonUcvtfV => {
            let u = u32::from(inst.opcode == Op::NeonUcvtfV);
            arity(inst, 3)
                .and_then(|()| fp_arrangement(inst, 2))
                .and_then(|(q, sz)| simd_two_misc(inst, w, q, u, sz, 0b11101, q, q))
        }
        // FCVTL/FCVTL2 .2S/.4S -> .2D: size = 0:sz with sz = 1; Q selects
        // the high half. The destination is always the 128-bit .2D.
        Op::NeonFcvtlV | Op::NeonFcvtl2V => {
            let high = u32::from(inst.opcode == Op::NeonFcvtl2V);
            arity(inst, 2).and_then(|()| simd_two_misc(inst, w, high, 0, 0b01, 0b10111, 1, high))
        }
        // ---- Advanced SIMD three different -----------------------------
        Op::NeonSmlalV => check_three_different(inst, w, 0, 0, 0b1000),
        Op::NeonSmlal2V => check_three_different(inst, w, 1, 0, 0b1000),
        Op::NeonUmlalV => check_three_different(inst, w, 0, 1, 0b1000),
        Op::NeonUmlal2V => check_three_different(inst, w, 1, 1, 0b1000),
        Op::NeonSaddwV => check_three_different(inst, w, 0, 0, 0b0001),
        Op::NeonSaddw2V => check_three_different(inst, w, 1, 0, 0b0001),
        Op::NeonUaddwV => check_three_different(inst, w, 0, 1, 0b0001),
        Op::NeonUaddw2V => check_three_different(inst, w, 1, 1, 0b0001),
        // ---- Indexed element, copies, immediates, shifts ---------------
        Op::NeonFmlaLaneV => check_fmla_lane(inst, w),
        Op::NeonDupElem => check_dup_element(inst, w),
        Op::NeonDupGen => check_dup_general(inst, w),
        Op::NeonInsGen => check_ins_general(inst, w),
        Op::NeonUmovGen => check_umov(inst, w),
        Op::NeonDupScalarD => check_dup_scalar_d(inst, w),
        Op::NeonMovi => check_movi(inst, w),
        Op::NeonShlVImm => check_shift_imm(inst, w, 0, 0b01010, false),
        Op::NeonSshrVImm => check_shift_imm(inst, w, 0, 0b00000, true),
        Op::NeonUshrVImm => check_shift_imm(inst, w, 1, 0b00000, true),
        Op::NeonExtV => check_ext(inst, w),
        Op::NeonUdotV => check_udot(inst, w),
        Op::NeonUmaxv => check_umaxv(inst, w),
        Op::NeonAddpScalar => check_addp_scalar(inst, w),
        Op::NeonLd1Post => check_ld1_st1_post(inst, w, true),
        Op::NeonSt1Post => check_ld1_st1_post(inst, w, false),
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::vfp_expand_imm_f64;

    /// VFPExpandImm against the closed form `(-1)^a * (16 + efgh) / 16 * 2^r`
    /// with `r = 1 + cd` for `b = 0` and `r = cd - 3` for `b = 1`, for all
    /// 256 immediates.
    #[test]
    fn vfp_expand_imm_matches_the_closed_form_for_every_imm8() {
        for imm8 in 0u32..256 {
            let sign = if imm8 & 0x80 != 0 { -1.0 } else { 1.0 };
            let b = (imm8 >> 6) & 1;
            let cd = ((imm8 >> 4) & 3) as i32;
            let efgh = f64::from(imm8 & 0xF);
            let r = if b == 0 { 1 + cd } else { cd - 3 };
            let expected = sign * (16.0 + efgh) / 16.0 * 2f64.powi(r);
            assert_eq!(vfp_expand_imm_f64(imm8), expected, "{imm8:#04x}");
        }
    }
}
