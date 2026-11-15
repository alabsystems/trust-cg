//! ENC-5 integer slice: independent decode of the general-purpose data
//! processing, PC-relative, atomic, barrier and trap words that ENC-5's
//! original arms left to its catch-all allowlist.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
//!
//! As in the FP/SIMD slice, each check extracts fields by one Arm ARM
//! (DDI 0487, C4.1 A64 encoding index) encoding class's layout, requires
//! every non-field bit to hold the class's fixed value and compares every
//! field with the `MachInst` intent. Fields a relocation or the final layout
//! owns are the only ones not compared: a relocated word's placeholder must
//! be zero and the word must carry its recorded hole, and an ADR naming a
//! jump table keeps its patched offset for the final-layout cross-check and
//! the switch binding, which re-derive it. Agreement is redundancy between
//! two independently written artifacts, not a proof.
//!
//! Register widths follow the machine IR's convention, which the encoder and
//! ENC-5's original arms share: a W or X view names one general-purpose
//! register, and the width a word encodes comes from one width-selecting
//! operand (the destination of a data-processing form, the tested register of
//! TBZ/TBNZ, the first register of TST, Rt of an LSE atomic, Rs of CAS, the
//! transfer register of LDAR/STLR) or from the opcode itself (SMULH, UMULH,
//! UMULL, ADR/ADRP, the GOT/TLV loads, LDRSW, LDR (literal), the TLS adds
//! and the typed GPR stores). Every other general-purpose operand is compared
//! by register number in either view, because the word has no field for its
//! view: register allocation gives a `Bool` (64-bit class) destination a
//! 32-bit source in `AND Xd, Wn, #1`, and the masked-UMULL fusion gives UMULL
//! 64-bit sources. Only TST's two registers must share a width, because the
//! encoder refuses a mixed TST.

use trust_cg_ir::inst::{AArch64Opcode, MachInst};
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::regs::SpecialReg;

use super::decode_check_fp_simd::FieldCheck;
use crate::decode_check::{FixupHole, FixupHoleKind};

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

fn operand_error(inst: &MachInst, index: usize, wanted: &str) -> String {
    format!(
        "{:?} operand {index} must be {wanted}, got {:?}",
        inst.opcode,
        inst.operands.get(index)
    )
}

/// A W/X data register or the matching zero register: (sf, field). Field 31
/// is ZR in these positions, so SP/WSP are refused.
fn gpr(inst: &MachInst, index: usize) -> Result<(u32, u32), String> {
    match inst.operands.get(index) {
        Some(MachOperand::PReg(p)) => match p.encoding() {
            0..=30 => Ok((1, u32::from(p.encoding()))),
            32..=62 => Ok((0, u32::from(p.encoding() - 32))),
            160 => Ok((1, 31)),
            161 => Ok((0, 31)),
            _ => Err(operand_error(inst, index, "a W/X register or ZR")),
        },
        Some(MachOperand::Special(SpecialReg::XZR)) => Ok((1, 31)),
        Some(MachOperand::Special(SpecialReg::WZR)) => Ok((0, 31)),
        _ => Err(operand_error(inst, index, "a W/X register or ZR")),
    }
}

/// A W/X register or the stack pointer: (sf, field). Field 31 is SP in
/// these positions, so the zero registers are refused.
fn gpr_or_sp(inst: &MachInst, index: usize) -> Result<(u32, u32), String> {
    match inst.operands.get(index) {
        Some(MachOperand::PReg(p)) => match p.encoding() {
            0..=31 => Ok((1, u32::from(p.encoding()))),
            32..=63 => Ok((0, u32::from(p.encoding() - 32))),
            _ => Err(operand_error(inst, index, "a W/X register or SP")),
        },
        Some(MachOperand::Special(SpecialReg::SP)) => Ok((1, 31)),
        _ => Err(operand_error(inst, index, "a W/X register or SP")),
    }
}

/// An X register or SP as a load/store base.
fn base(inst: &MachInst, index: usize) -> Result<u32, String> {
    match gpr_or_sp(inst, index)? {
        (1, n) => Ok(n),
        _ => Err(operand_error(inst, index, "an X register or SP base")),
    }
}

/// Register operands that must all name one width (TST only; see the module
/// comment).
fn same_width(inst: &MachInst, regs: &[(u32, u32)]) -> Result<u32, String> {
    let sf = regs.first().map_or(1, |r| r.0);
    if regs.iter().any(|r| r.0 != sf) {
        return Err(format!(
            "{:?} register operands must share one width",
            inst.opcode
        ));
    }
    Ok(sf)
}

fn imm(inst: &MachInst, index: usize) -> Result<i64, String> {
    match inst.operands.get(index) {
        Some(MachOperand::Imm(value)) => Ok(*value),
        _ => Err(operand_error(inst, index, "an immediate")),
    }
}

fn no_hole(inst: &MachInst, hole: Option<&FixupHole>) -> FieldCheck {
    match hole {
        None => Ok(()),
        Some(hole) => Err(format!(
            "{:?} cannot carry a {:?} relocation hole",
            inst.opcode, hole.kind
        )),
    }
}

fn is_symbolic(operand: Option<&MachOperand>) -> bool {
    matches!(
        operand,
        Some(MachOperand::Symbol(_) | MachOperand::ExactModuleSymbol(_))
    )
}

/// A symbolic operand requires a GlobalRef hole over the whole word; any
/// other operand requires no hole. Returns whether the word is relocated.
fn symbolic_hole(inst: &MachInst, index: usize, hole: Option<&FixupHole>) -> Result<bool, String> {
    let symbolic = is_symbolic(inst.operands.get(index));
    match (symbolic, hole) {
        (true, Some(h)) if h.kind == FixupHoleKind::GlobalRef => Ok(true),
        (false, None) => Ok(false),
        (true, _) => Err(format!(
            "{:?} with a symbolic operand requires its GlobalRef relocation hole, got {hole:?}",
            inst.opcode
        )),
        (false, Some(_)) => no_hole(inst, hole).map(|()| false),
    }
}

// ---------------------------------------------------------------------------
// Data processing -- register
// ---------------------------------------------------------------------------

/// Add/subtract (shifted register):
/// `sf | op | S | 01011 | shift | 0 | Rm | imm6 | Rn | Rd`.
#[allow(clippy::too_many_arguments)]
fn add_sub_shifted_fields(
    w: u32,
    sf: u32,
    op: u32,
    s: u32,
    shift: u32,
    imm6: u32,
    rm: u32,
    rn: u32,
    rd: u32,
) -> FieldCheck {
    class(
        w,
        0x1F20_0000,
        0x0B00_0000,
        "add/subtract (shifted register)",
    )?;
    want!("add/sub-shifted sf", field(w, 31, 31), sf);
    want!("add/sub-shifted op", field(w, 30, 30), op);
    want!("add/sub-shifted S", field(w, 29, 29), s);
    want!("add/sub-shifted shift", field(w, 23, 22), shift);
    want!("add/sub-shifted imm6", field(w, 15, 10), imm6);
    want!("add/sub-shifted Rd", field(w, 4, 0), rd);
    want!("add/sub-shifted Rn", field(w, 9, 5), rn);
    want!("add/sub-shifted Rm", field(w, 20, 16), rm);
    Ok(())
}

/// `[Rd, Rn, Rm, #k]` with a real in-register shift `1 <= k < regsize`.
fn check_add_sub_shift_amount(inst: &MachInst, w: u32, op: u32, shift: u32) -> FieldCheck {
    arity(inst, 4)?;
    let (rd, rn, rm) = (gpr(inst, 0)?, gpr(inst, 1)?, gpr(inst, 2)?);
    let sf = rd.0;
    let k = imm(inst, 3)?;
    if !(1..if sf == 1 { 64 } else { 32 }).contains(&k) {
        return Err(format!(
            "{:?} shift {k} is not a real in-register shift",
            inst.opcode
        ));
    }
    add_sub_shifted_fields(w, sf, op, 0, shift, k as u32, rm.1, rn.1, rd.1)
}

/// `[Rd, Rn, Rm]`, no shift.
fn check_add_sub_plain(inst: &MachInst, w: u32, op: u32, s: u32) -> FieldCheck {
    arity(inst, 3)?;
    let (rd, rn, rm) = (gpr(inst, 0)?, gpr(inst, 1)?, gpr(inst, 2)?);
    add_sub_shifted_fields(w, rd.0, op, s, 0, 0, rm.1, rn.1, rd.1)
}

/// SP spelled either way.
fn is_sp(op: &MachOperand) -> bool {
    matches!(op, MachOperand::Special(SpecialReg::SP))
        || matches!(op, MachOperand::PReg(p) if p.encoding() == 31)
}

/// `SUBS Rd, SP, Rm` `[Rd, SP, Rm]`: Add/subtract (extended register),
/// `sf | op=1 | S=1 | 01011 | 00 | 1 | Rm | option=UXTX | imm3=0 | Rn=SP | Rd`,
/// 64-bit only, Rd an X register or XZR, Rm an X register.
fn check_subs_from_sp(inst: &MachInst, w: u32) -> FieldCheck {
    arity(inst, 3)?;
    let (rd_sf, rd) = gpr(inst, 0)?;
    let (rm_sf, rm) = gpr(inst, 2)?;
    if rd_sf != 1 || rm_sf != 1 || rm == 31 {
        return Err(operand_error(
            inst,
            2,
            "a 64-bit X destination or XZR and an X0-X30 subtrahend",
        ));
    }
    class(
        w,
        0xFFE0_0000,
        0xEB20_0000,
        "SUBS (extended register, 64-bit)",
    )?;
    want!("subs-ext option", field(w, 15, 13), 0b011);
    want!("subs-ext imm3", field(w, 12, 10), 0);
    want!("subs-ext Rn", field(w, 9, 5), 31);
    want!("subs-ext Rd", field(w, 4, 0), rd);
    want!("subs-ext Rm", field(w, 20, 16), rm);
    Ok(())
}

/// NEG `[Rd, Rm]` = SUB Rd, ZR, Rm.
fn check_neg(inst: &MachInst, w: u32) -> FieldCheck {
    arity(inst, 2)?;
    let (rd, rm) = (gpr(inst, 0)?, gpr(inst, 1)?);
    add_sub_shifted_fields(w, rd.0, 1, 0, 0, 0, rm.1, 31, rd.1)
}

/// Add/subtract (with carry): `sf | op | S | 11010000 | Rm | 000000 | Rn | Rd`.
fn check_add_sub_carry(inst: &MachInst, w: u32, op: u32, s: u32) -> FieldCheck {
    arity(inst, 3)?;
    let (rd, rn, rm) = (gpr(inst, 0)?, gpr(inst, 1)?, gpr(inst, 2)?);
    class(w, 0x1FE0_FC00, 0x1A00_0000, "add/subtract (with carry)")?;
    want!("carry sf", field(w, 31, 31), rd.0);
    want!("carry op", field(w, 30, 30), op);
    want!("carry S", field(w, 29, 29), s);
    want!("carry Rd", field(w, 4, 0), rd.1);
    want!("carry Rn", field(w, 9, 5), rn.1);
    want!("carry Rm", field(w, 20, 16), rm.1);
    Ok(())
}

/// Logical (shifted register): `sf | opc | 01010 | shift | N | Rm | imm6 | Rn | Rd`.
#[allow(clippy::too_many_arguments)]
fn logical_shifted_fields(
    w: u32,
    sf: u32,
    opc: u32,
    n: u32,
    rm: u32,
    rn: u32,
    rd: u32,
) -> FieldCheck {
    class(w, 0x1F00_0000, 0x0A00_0000, "logical (shifted register)")?;
    want!("logical-shifted sf", field(w, 31, 31), sf);
    want!("logical-shifted opc", field(w, 30, 29), opc);
    want!("logical-shifted shift", field(w, 23, 22), 0);
    want!("logical-shifted N", field(w, 21, 21), n);
    want!("logical-shifted imm6", field(w, 15, 10), 0);
    want!("logical-shifted Rd", field(w, 4, 0), rd);
    want!("logical-shifted Rn", field(w, 9, 5), rn);
    want!("logical-shifted Rm", field(w, 20, 16), rm);
    Ok(())
}

/// BIC `[Rd, Rn, Rm]`: AND with N = 1.
fn check_bic(inst: &MachInst, w: u32) -> FieldCheck {
    arity(inst, 3)?;
    let (rd, rn, rm) = (gpr(inst, 0)?, gpr(inst, 1)?, gpr(inst, 2)?);
    logical_shifted_fields(w, rd.0, 0b00, 1, rm.1, rn.1, rd.1)
}

/// Arm ARM `DecodeBitMasks(N, imms, immr, immediate = TRUE, M)`: the
/// replicated, rotated run of ones, or `None` for a reserved (or, for the
/// rotation, non-canonical) encoding.
fn decode_bit_masks(n: u32, imms: u32, immr: u32, regsize: u32) -> Option<u64> {
    if regsize == 32 && n == 1 {
        return None;
    }
    let combined = (n << 6) | (!imms & 0x3F);
    if combined == 0 {
        return None;
    }
    let len = 31 - combined.leading_zeros();
    if len < 1 {
        return None;
    }
    let levels = (1u32 << len) - 1;
    // `immr` above `levels` is ignored by the pseudocode; ENC-5 requires the
    // canonical (zero) upper bits so one mask has exactly one word.
    if imms & levels == levels || immr & !levels != 0 {
        return None;
    }
    let s = imms & levels;
    let r = immr & levels;
    let esize = 1u32 << len;
    let welem: u64 = if s + 1 == 64 {
        u64::MAX
    } else {
        (1u64 << (s + 1)) - 1
    };
    let element_mask = if esize == 64 {
        u64::MAX
    } else {
        (1u64 << esize) - 1
    };
    let rotated = if r == 0 {
        welem
    } else {
        ((welem >> r) | (welem << (esize - r))) & element_mask
    };
    let mut out = 0u64;
    let mut offset = 0;
    while offset < regsize {
        out |= rotated << offset;
        offset += esize;
    }
    Some(if regsize == 64 {
        out
    } else {
        out & 0xFFFF_FFFF
    })
}

/// Logical (immediate): `sf | opc | 100100 | N | immr | imms | Rn | Rd`.
/// `mask` is the intent's operand list from `mask_index`: one immediate
/// (the value) or the pre-decomposed `N, immr, imms` fields.
fn logical_immediate_fields(
    inst: &MachInst,
    w: u32,
    sf: u32,
    opc: u32,
    rn: u32,
    rd: u32,
    mask_index: usize,
) -> FieldCheck {
    class(w, 0x1F80_0000, 0x1200_0000, "logical (immediate)")?;
    want!("logical-imm sf", field(w, 31, 31), sf);
    want!("logical-imm opc", field(w, 30, 29), opc);
    want!("logical-imm Rd", field(w, 4, 0), rd);
    want!("logical-imm Rn", field(w, 9, 5), rn);
    let (n, immr, imms) = (field(w, 22, 22), field(w, 21, 16), field(w, 15, 10));
    let regsize = if sf == 1 { 64 } else { 32 };
    let Some(decoded) = decode_bit_masks(n, imms, immr, regsize) else {
        return Err(format!(
            "logical-imm N={n} immr={immr} imms={imms} is reserved for a {regsize}-bit register"
        ));
    };
    match inst.operands.len() - mask_index {
        1 => {
            let value = imm(inst, mask_index)? as u64;
            let value = if regsize == 64 {
                value
            } else {
                value & 0xFFFF_FFFF
            };
            if decoded != value {
                return Err(format!(
                    "logical-imm N={n} immr={immr} imms={imms} decodes to {decoded:#x}, the intent names {value:#x}"
                ));
            }
        }
        3 => {
            want!("logical-imm N", i64::from(n), imm(inst, mask_index)?);
            want!(
                "logical-imm immr",
                i64::from(immr),
                imm(inst, mask_index + 1)?
            );
            want!(
                "logical-imm imms",
                i64::from(imms),
                imm(inst, mask_index + 2)?
            );
        }
        _ => {
            return Err(format!(
                "{:?} takes a mask immediate or N, immr, imms after its registers",
                inst.opcode
            ));
        }
    }
    Ok(())
}

/// AND/ORR/EOR (immediate) `[Rd|SP, Rn, mask]`: Rd 31 is SP here.
fn check_logical_immediate(inst: &MachInst, w: u32, opc: u32) -> FieldCheck {
    if !matches!(inst.operands.len(), 3 | 5) {
        return arity(inst, 3);
    }
    let (rd, rn) = (gpr_or_sp(inst, 0)?, gpr(inst, 1)?);
    logical_immediate_fields(inst, w, rd.0, opc, rn.1, rd.1, 2)
}

/// TST `[Rn, Rm]` (ANDS ZR, Rn, Rm) or `[Rn, #mask]` (ANDS ZR, Rn, #mask).
fn check_tst(inst: &MachInst, w: u32) -> FieldCheck {
    arity(inst, 2)?;
    let rn = gpr(inst, 0)?;
    if matches!(inst.operands.get(1), Some(MachOperand::Imm(_))) {
        return logical_immediate_fields(inst, w, rn.0, 0b11, rn.1, 31, 1);
    }
    let rm = gpr(inst, 1)?;
    let sf = same_width(inst, &[rn, rm])?;
    logical_shifted_fields(w, sf, 0b11, 0, rm.1, rn.1, 31)
}

/// ROR (immediate) `[Rd, Rn, #shift]` = EXTR Rd, Rn, Rn, #shift:
/// `sf | 00 | 100111 | N | 0 | Rm | imms | Rn | Rd` with N = sf; a zero
/// rotation is the ORR register move.
fn check_ror_immediate(inst: &MachInst, w: u32) -> FieldCheck {
    arity(inst, 3)?;
    let (rd, rn) = (gpr(inst, 0)?, gpr(inst, 1)?);
    let sf = rd.0;
    let shift = imm(inst, 2)?;
    if !(0..if sf == 1 { 64 } else { 32 }).contains(&shift) {
        return Err(format!("ROR amount {shift} is outside the register"));
    }
    if shift == 0 {
        return logical_shifted_fields(w, sf, 0b01, 0, rn.1, 31, rd.1);
    }
    class(w, 0x7FA0_0000, 0x1380_0000, "extract (EXTR)")?;
    want!("extr sf", field(w, 31, 31), sf);
    want!("extr N", field(w, 22, 22), sf);
    want!("extr imms", i64::from(field(w, 15, 10)), shift);
    want!("extr Rd", field(w, 4, 0), rd.1);
    want!("extr Rn", field(w, 9, 5), rn.1);
    want!("extr Rm", field(w, 20, 16), rn.1);
    Ok(())
}

/// Data-processing (3 source) multiply-high/long forms:
/// `sf | op54 | 11011 | op31 | Rm | o0 | Ra | Rn | Rd` with Ra = 11111.
/// SMULH/UMULH are `Xd, Xn, Xm` and UMULL is `Xd, Wn, Wm` whatever views the
/// intent spells: the opcode fixes every width, so only register numbers are
/// compared (the masked-UMULL fusion names its sources in the 64-bit view).
fn check_mul_high_long(inst: &MachInst, w: u32, op31: u32) -> FieldCheck {
    arity(inst, 3)?;
    let (rd, rn, rm) = (gpr(inst, 0)?, gpr(inst, 1)?, gpr(inst, 2)?);
    class(w, 0x1F00_0000, 0x1B00_0000, "data-processing (3 source)")?;
    want!("dp3 sf", field(w, 31, 31), 1);
    want!("dp3 op54", field(w, 30, 29), 0);
    want!("dp3 op31", field(w, 23, 21), op31);
    want!("dp3 o0", field(w, 15, 15), 0);
    want!("dp3 Ra", field(w, 14, 10), 31);
    want!("dp3 Rd", field(w, 4, 0), rd.1);
    want!("dp3 Rn", field(w, 9, 5), rn.1);
    want!("dp3 Rm", field(w, 20, 16), rm.1);
    Ok(())
}

// ---------------------------------------------------------------------------
// Immediates, PC-relative addressing and relocated loads
// ---------------------------------------------------------------------------

/// Add/subtract (immediate): `sf | op | S | 100010 | sh | imm12 | Rn | Rd`.
#[allow(clippy::too_many_arguments)]
fn add_sub_immediate_fields(
    w: u32,
    sf: u32,
    op: u32,
    s: u32,
    imm12: u32,
    rn: u32,
    rd: u32,
) -> FieldCheck {
    class(w, 0x1F80_0000, 0x1100_0000, "add/subtract (immediate)")?;
    want!("add/sub-imm sf", field(w, 31, 31), sf);
    want!("add/sub-imm op", field(w, 30, 30), op);
    want!("add/sub-imm S", field(w, 29, 29), s);
    want!("add/sub-imm sh", field(w, 22, 22), 0);
    want!("add/sub-imm imm12", field(w, 21, 10), imm12);
    want!("add/sub-imm Rd", field(w, 4, 0), rd);
    want!("add/sub-imm Rn", field(w, 9, 5), rn);
    Ok(())
}

/// ADDS/SUBS (immediate) `[Rd, Rn|SP, #imm12]`: Rd 31 is ZR, Rn 31 is SP.
fn check_add_sub_immediate_flags(inst: &MachInst, w: u32, op: u32) -> FieldCheck {
    arity(inst, 3)?;
    let (rd, rn) = (gpr(inst, 0)?, gpr_or_sp(inst, 1)?);
    let value = imm(inst, 2)?;
    if !(0..=0xFFF).contains(&value) {
        return Err(format!(
            "{:?} immediate {value} is not an imm12",
            inst.opcode
        ));
    }
    add_sub_immediate_fields(w, rd.0, op, 1, value as u32, rn.1, rd.1)
}

/// `ADD Xd, Xn, #:lo12:sym` (AddPCRel) `[Xd|SP, Xn|SP, sym | #imm12]`: a
/// symbolic word carries a GlobalRef hole and a zero imm12 placeholder.
fn check_add_pcrel(inst: &MachInst, w: u32, hole: Option<&FixupHole>) -> FieldCheck {
    arity(inst, 3)?;
    let (rd, rn) = (gpr_or_sp(inst, 0)?, gpr_or_sp(inst, 1)?);
    let imm12 = if symbolic_hole(inst, 2, hole)? {
        0
    } else {
        let value = imm(inst, 2)?;
        u32::try_from(value)
            .ok()
            .filter(|v| *v <= 0xFFF)
            .ok_or_else(|| format!("AddPCRel immediate {value} is not an imm12"))?
    };
    add_sub_immediate_fields(w, rd.0, 0, 0, imm12, rn.1, rd.1)
}

/// ELF local-exec TLS adds `[Xd, Xn, sym]`: `ADD Xd, Xn, #:tprel_hi12:sym,
/// LSL #12` (`sh = 1`) and `ADD Xd, Xn, #:tprel_lo12_nc:sym` (`sh = 0`),
/// always relocated: a GlobalRef hole and a zero imm12 placeholder. Both
/// registers are X by the opcode, in either view.
fn check_add_tprel(inst: &MachInst, w: u32, hole: Option<&FixupHole>, sh: u32) -> FieldCheck {
    arity(inst, 3)?;
    let (rd, rn) = (gpr_or_sp(inst, 0)?, gpr_or_sp(inst, 1)?);
    if !symbolic_hole(inst, 2, hole)? {
        return Err(format!("{:?} is only emitted relocated", inst.opcode));
    }
    class(w, 0x1F80_0000, 0x1100_0000, "add/subtract (immediate)")?;
    want!("tprel-add sf", field(w, 31, 31), 1);
    want!("tprel-add op", field(w, 30, 30), 0);
    want!("tprel-add S", field(w, 29, 29), 0);
    want!("tprel-add sh", field(w, 22, 22), sh);
    want!("tprel-add placeholder imm12", field(w, 21, 10), 0);
    want!("tprel-add Rd", field(w, 4, 0), rd.1);
    want!("tprel-add Rn", field(w, 9, 5), rn.1);
    Ok(())
}

/// PC-relative addressing: `op | immlo | 10000 | immhi | Rd`.
/// ADRP `[Xd, sym | #pages]`: a symbolic word carries a GlobalRef hole and a
/// zero placeholder. ADR `[Xd, jump table | #bytes]`: the jump-table offset
/// is patched after layout and re-derived by the final-layout cross-check
/// and the switch binding, so only its class, `op` and `Rd` are compared.
/// The destination is X by the opcode, in either view.
fn check_pc_relative(inst: &MachInst, w: u32, hole: Option<&FixupHole>, page: bool) -> FieldCheck {
    arity(inst, 2)?;
    let rd = gpr(inst, 0)?;
    class(w, 0x1F00_0000, 0x1000_0000, "PC-relative addressing")?;
    want!("pc-rel op", field(w, 31, 31), u32::from(page));
    want!("pc-rel Rd", field(w, 4, 0), rd.1);
    let imm21 = (field(w, 23, 5) << 2) | field(w, 30, 29);
    let decoded = i64::from(((imm21 << 11) as i32) >> 11);
    match inst.operands.get(1) {
        Some(MachOperand::JumpTableIndex(_)) if !page => no_hole(inst, hole),
        _ if symbolic_hole(inst, 1, hole)? => {
            want!("pc-rel placeholder imm21", decoded, 0);
            Ok(())
        }
        _ => {
            want!("pc-rel imm21", decoded, imm(inst, 1)?);
            Ok(())
        }
    }
}

/// Load register (unsigned immediate), 64-bit GPR: `11 | 111 | 0 | 01 |
/// opc=01 | imm12 | Rn | Rt`. The GOT/TLV loads `[Xt, Xn|SP, sym | #bytes]`:
/// a symbolic word carries a GlobalRef hole and a zero imm12 placeholder.
/// The pointer load is 64-bit by the opcode, in either view of Rt.
fn check_got_load(inst: &MachInst, w: u32, hole: Option<&FixupHole>) -> FieldCheck {
    if !matches!(inst.operands.len(), 2 | 3) {
        return arity(inst, 3);
    }
    let rt = gpr(inst, 0)?;
    let rn = base(inst, 1)?;
    let imm12 = if inst.operands.len() == 2 {
        no_hole(inst, hole)?;
        0
    } else if symbolic_hole(inst, 2, hole)? {
        0
    } else {
        let bytes = imm(inst, 2)?;
        if bytes < 0 || bytes % 8 != 0 || bytes / 8 > 0xFFF {
            return Err(format!(
                "{:?} offset {bytes} is not a scaled imm12",
                inst.opcode
            ));
        }
        (bytes / 8) as u32
    };
    class(
        w,
        0xFFC0_0000,
        0xF940_0000,
        "LDR (immediate, unsigned offset, 64-bit)",
    )?;
    want!("ldr-ui imm12", field(w, 21, 10), imm12);
    want!("ldr-ui Rt", field(w, 4, 0), rt.1);
    want!("ldr-ui Rn", field(w, 9, 5), rn);
    Ok(())
}

/// LDRSW (register) `[Xt, Xn|SP, Xm]` with `LSL #2`: load/store register
/// (register offset) `10 | 111 | 0 | 00 | opc=10 | 1 | Rm | option=011 | S=1
/// | 10 | Rn | Rt`. The destination and the index are X by the opcode, in
/// either view.
fn check_ldrsw_register(inst: &MachInst, w: u32) -> FieldCheck {
    arity(inst, 3)?;
    let rt = gpr(inst, 0)?;
    let rn = base(inst, 1)?;
    let rm = gpr(inst, 2)?;
    class(w, 0xFFE0_FC00, 0xB8A0_7800, "LDRSW (register, LSL #2)")?;
    want!("ldrsw Rt", field(w, 4, 0), rt.1);
    want!("ldrsw Rn", field(w, 9, 5), rn);
    want!("ldrsw Rm", field(w, 20, 16), rm.1);
    Ok(())
}

/// Test and branch (immediate) `[Rt, #bit, target]`:
/// `b5 | 011011 | op | b40 | imm14 | Rt`. A W register tests bits 0..31.
fn check_test_branch(
    inst: &MachInst,
    w: u32,
    hole: Option<&FixupHole>,
    nonzero: bool,
) -> FieldCheck {
    arity(inst, 3)?;
    let rt = gpr(inst, 0)?;
    let bit = imm(inst, 1)?;
    if !(0..if rt.0 == 1 { 64 } else { 32 }).contains(&bit) {
        return Err(format!(
            "{:?} bit {bit} is outside the register",
            inst.opcode
        ));
    }
    class(w, 0x7E00_0000, 0x3600_0000, "test and branch (immediate)")?;
    want!("tbz op", field(w, 24, 24), u32::from(nonzero));
    want!(
        "tbz bit (b5:b40)",
        i64::from((field(w, 31, 31) << 5) | field(w, 23, 19)),
        bit
    );
    want!("tbz Rt", field(w, 4, 0), rt.1);
    match hole {
        Some(hole) if hole.kind == FixupHoleKind::Branch => Ok(()),
        Some(_) => no_hole(inst, hole),
        None => {
            let target = imm(inst, 2)?;
            let decoded = i64::from(((field(w, 18, 5) << 18) as i32) >> 18);
            want!("tbz imm14", decoded, target);
            Ok(())
        }
    }
}

/// The typed stores `STRWui`/`STRXui`/`STRSui`/`STRDui` `[Rt, Xn|SP, #bytes]`
/// or `[Rt, [Xn, #bytes]]` (a base alone is offset 0): the scaled unsigned
/// form when the offset fits it, otherwise the unscaled signed form.
/// Load/store register (unsigned immediate)
/// `size | 111 | V | 01 | opc=00 | imm12 | Rn | Rt` or (unscaled immediate)
/// `size | 111 | V | 00 | opc=00 | 0 | imm9 | 00 | Rn | Rt`.
fn check_typed_store(inst: &MachInst, w: u32, size: u32, fp: bool) -> FieldCheck {
    let scale = 1i64 << size;
    let rt = if fp {
        let want = if size == 3 {
            (96u16, "D")
        } else {
            (128u16, "S")
        };
        match inst.operands.first() {
            Some(MachOperand::PReg(p)) if (want.0..want.0 + 32).contains(&p.encoding()) => {
                u32::from(p.encoding() - want.0)
            }
            _ => return Err(operand_error(inst, 0, &format!("an {} register", want.1))),
        }
    } else {
        // The opcode fixes the stored width; either GPR view names Rt.
        gpr(inst, 0)?.1
    };
    let (rn, offset) = match inst.operands.as_slice() {
        [_, MachOperand::MemOp { base, offset }] if base.encoding() <= 31 => {
            (u32::from(base.encoding()), *offset)
        }
        [_, _] => (base(inst, 1)?, 0),
        [_, _, MachOperand::Imm(offset)] => (base(inst, 1)?, *offset),
        _ => {
            return Err(format!(
                "{:?} takes a transfer register and an X/SP base with an immediate offset",
                inst.opcode
            ));
        }
    };
    let v = u32::from(fp);
    if offset >= 0 && offset % scale == 0 && offset / scale <= 0xFFF {
        class(
            w,
            0x3B00_0000,
            0x3900_0000,
            "load/store register (unsigned immediate)",
        )?;
        want!("str-ui imm12", i64::from(field(w, 21, 10)), offset / scale);
    } else if (-256..=255).contains(&offset) {
        class(
            w,
            0x3B20_0C00,
            0x3800_0000,
            "load/store register (unscaled immediate)",
        )?;
        want!(
            "str-unscaled imm9",
            i64::from(((field(w, 20, 12) << 23) as i32) >> 23),
            offset
        );
    } else {
        return Err(format!(
            "{:?} offset {offset} is not encodable",
            inst.opcode
        ));
    }
    want!("str size", field(w, 31, 30), size);
    want!("str V", field(w, 26, 26), v);
    want!("str opc", field(w, 23, 22), 0);
    want!("str Rt", field(w, 4, 0), rt);
    want!("str Rn", field(w, 9, 5), rn);
    Ok(())
}

/// LDR (literal), 64-bit GPR `[Xt, #words]`: load register (literal)
/// `opc=01 | 011 | V=0 | 00 | imm19 | Rt`. A constant-pool hole leaves the
/// offset to its fixup. The load is 64-bit by the opcode, in either view.
fn check_ldr_literal(inst: &MachInst, w: u32, hole: Option<&FixupHole>) -> FieldCheck {
    arity(inst, 2)?;
    let rt = gpr(inst, 0)?;
    class(w, 0xFF00_0000, 0x5800_0000, "LDR (literal, 64-bit)")?;
    want!("ldr-literal Rt", field(w, 4, 0), rt.1);
    match hole {
        Some(hole) if hole.kind == FixupHoleKind::ConstPool => Ok(()),
        Some(_) => no_hole(inst, hole),
        None => {
            let decoded = i64::from(((field(w, 23, 5) << 13) as i32) >> 13);
            want!("ldr-literal imm19", decoded, imm(inst, 1)?);
            Ok(())
        }
    }
}

// ---------------------------------------------------------------------------
// Atomics, barriers, hints and traps
// ---------------------------------------------------------------------------

/// The access size of an LSE atomic / CAS intent: an explicit trailing
/// size immediate (0 byte, 1 halfword) or the data register width (W word,
/// X doubleword). A narrow access names its data register by number; the
/// machine IR may spell it in either view.
fn atomic_size(inst: &MachInst, data: (u32, u32)) -> Result<u32, String> {
    match inst.operands.len() {
        3 => Ok(0b10 | data.0),
        4 => match imm(inst, 3)? {
            0 => Ok(0b00),
            1 => Ok(0b01),
            other => Err(format!(
                "{:?} narrow size selector {other} must be 0 (byte) or 1 (halfword)",
                inst.opcode
            )),
        },
        n => Err(format!(
            "{:?} takes Rs, Rt, Rn and an optional size, the intent has {n} operands",
            inst.opcode
        )),
    }
}

/// Atomic memory operations (LSE) `[Rs, Rt, Xn|SP, size?]`:
/// `size | 111 | V=0 | 00 | A | R | 1 | Rs | o3 | opc | 00 | Rn | Rt`.
/// Rt's view selects a word or doubleword access; Rs is compared by number.
fn check_lse(inst: &MachInst, w: u32, o3: u32, opc: u32, a: u32, r: u32) -> FieldCheck {
    let (rs, rt, rn) = (gpr(inst, 0)?, gpr(inst, 1)?, base(inst, 2)?);
    let size = atomic_size(inst, rt)?;
    class(w, 0x3F20_0C00, 0x3820_0000, "atomic memory operation (LSE)")?;
    want!("lse size", field(w, 31, 30), size);
    want!("lse A", field(w, 23, 23), a);
    want!("lse R", field(w, 22, 22), r);
    want!("lse o3", field(w, 15, 15), o3);
    want!("lse opc", field(w, 14, 12), opc);
    want!("lse Rs", field(w, 20, 16), rs.1);
    want!("lse Rt", field(w, 4, 0), rt.1);
    want!("lse Rn", field(w, 9, 5), rn);
    Ok(())
}

/// Compare and swap `[Rs, Rt, Xn|SP, size?]`:
/// `size | 001000 | 1 | L | 1 | Rs | o0 | 11111 | Rn | Rt` (L acquire,
/// o0 release). Rs's view selects a word or doubleword access; Rt is
/// compared by number.
fn check_cas(inst: &MachInst, w: u32, acquire: u32, release: u32) -> FieldCheck {
    let (rs, rt, rn) = (gpr(inst, 0)?, gpr(inst, 1)?, base(inst, 2)?);
    let size = atomic_size(inst, rs)?;
    class(w, 0x3FA0_7C00, 0x08A0_7C00, "compare and swap")?;
    want!("cas size", field(w, 31, 30), size);
    want!("cas L (acquire)", field(w, 22, 22), acquire);
    want!("cas o0 (release)", field(w, 15, 15), release);
    want!("cas Rs", field(w, 20, 16), rs.1);
    want!("cas Rt", field(w, 4, 0), rt.1);
    want!("cas Rn", field(w, 9, 5), rn);
    Ok(())
}

/// Load-acquire / store-release register `[Rt, Xn|SP]`: load/store ordered
/// `size | 001000 | 1 | L | 0 | 11111 | 1 | 11111 | Rn | Rt`. `fixed_size`
/// is the byte/halfword size (the data register by number, either view);
/// word forms follow the data width.
fn check_ordered(inst: &MachInst, w: u32, load: bool, fixed_size: Option<u32>) -> FieldCheck {
    arity(inst, 2)?;
    let (rt, rn) = (gpr(inst, 0)?, base(inst, 1)?);
    let size = fixed_size.unwrap_or(0b10 | rt.0);
    class(w, 0x3FBF_FC00, 0x089F_FC00, "load/store ordered")?;
    want!("ordered size", field(w, 31, 30), size);
    want!("ordered L", field(w, 22, 22), u32::from(load));
    want!("ordered Rt", field(w, 4, 0), rt.1);
    want!("ordered Rn", field(w, 9, 5), rn);
    Ok(())
}

/// Barriers `[#CRm]`: `1101010100 | 0 | 00 | 011 | 0011 | CRm | op2 | 11111`
/// with op2 100 (DSB), 101 (DMB), 110 (ISB).
fn check_barrier(inst: &MachInst, w: u32, op2: u32) -> FieldCheck {
    arity(inst, 1)?;
    let crm = imm(inst, 0)?;
    if !(0..=15).contains(&crm) {
        return Err(format!("{:?} option {crm} is not a 4-bit CRm", inst.opcode));
    }
    class(w, 0xFFFF_F01F, 0xD503_301F, "barrier")?;
    want!("barrier op2", field(w, 7, 5), op2);
    want!("barrier CRm", i64::from(field(w, 11, 8)), crm);
    Ok(())
}

/// BRK `[]` or `[#imm16]`: exception generation `11010100 | 001 | imm16 |
/// 000 | 00`. The machine IR's operand-less BRK is `BRK #1`.
fn check_brk(inst: &MachInst, w: u32) -> FieldCheck {
    let comment = match inst.operands.len() {
        0 => 1,
        1 => imm(inst, 0)?,
        _ => return arity(inst, 1),
    };
    class(w, 0xFFE0_001F, 0xD420_0000, "BRK")?;
    want!("brk imm16", i64::from(field(w, 20, 5)), comment);
    Ok(())
}

/// The integer slice of ENC-5: `None` for an opcode this slice does not
/// own; otherwise the field-by-field verdict for `w`.
pub(super) fn check_int(inst: &MachInst, w: u32, hole: Option<&FixupHole>) -> Option<FieldCheck> {
    use AArch64Opcode as Op;
    // Relocated forms check their own hole; every other form has none.
    let plain = |check: FieldCheck| no_hole(inst, hole).and(check);
    Some(match inst.opcode {
        Op::AddRRShift => plain(check_add_sub_shift_amount(inst, w, 0, 0b00)),
        Op::SubRRShift => plain(check_add_sub_shift_amount(inst, w, 1, 0b00)),
        Op::AddRRShiftLsr => plain(check_add_sub_shift_amount(inst, w, 0, 0b01)),
        Op::AddsRR => plain(check_add_sub_plain(inst, w, 0, 1)),
        Op::SubsRR if inst.operands.get(1).is_some_and(is_sp) => plain(check_subs_from_sp(inst, w)),
        Op::SubsRR => plain(check_add_sub_plain(inst, w, 1, 1)),
        Op::Neg => plain(check_neg(inst, w)),
        Op::AddsRI => plain(check_add_sub_immediate_flags(inst, w, 0)),
        Op::SubsRI => plain(check_add_sub_immediate_flags(inst, w, 1)),
        Op::Adc => plain(check_add_sub_carry(inst, w, 0, 0)),
        Op::Sbc => plain(check_add_sub_carry(inst, w, 1, 0)),
        Op::Adcs => plain(check_add_sub_carry(inst, w, 0, 1)),
        Op::Sbcs => plain(check_add_sub_carry(inst, w, 1, 1)),
        Op::BicRR => plain(check_bic(inst, w)),
        Op::AndRI => plain(check_logical_immediate(inst, w, 0b00)),
        Op::OrrRI => plain(check_logical_immediate(inst, w, 0b01)),
        Op::EorRI => plain(check_logical_immediate(inst, w, 0b10)),
        Op::Tst => plain(check_tst(inst, w)),
        Op::RorRI => plain(check_ror_immediate(inst, w)),
        Op::Smulh => plain(check_mul_high_long(inst, w, 0b010)),
        Op::Umulh => plain(check_mul_high_long(inst, w, 0b110)),
        Op::Umull => plain(check_mul_high_long(inst, w, 0b101)),
        Op::AddPCRel => check_add_pcrel(inst, w, hole),
        Op::Adrp => check_pc_relative(inst, w, hole, true),
        Op::Adr => check_pc_relative(inst, w, hole, false),
        Op::LdrGot | Op::LdrTlvp | Op::LdrGottprel => check_got_load(inst, w, hole),
        Op::AddTprelHi12 => check_add_tprel(inst, w, hole, 1),
        Op::AddTprelLo12 => check_add_tprel(inst, w, hole, 0),
        Op::LdrswRO => plain(check_ldrsw_register(inst, w)),
        Op::LdrLiteral => check_ldr_literal(inst, w, hole),
        Op::STRWui => plain(check_typed_store(inst, w, 2, false)),
        Op::STRXui => plain(check_typed_store(inst, w, 3, false)),
        Op::STRSui => plain(check_typed_store(inst, w, 2, true)),
        Op::STRDui => plain(check_typed_store(inst, w, 3, true)),
        Op::Tbz => check_test_branch(inst, w, hole, false),
        Op::Tbnz => check_test_branch(inst, w, hole, true),
        Op::Ldadd => plain(check_lse(inst, w, 0, 0b000, 0, 0)),
        Op::Ldadda => plain(check_lse(inst, w, 0, 0b000, 1, 0)),
        Op::Ldaddal => plain(check_lse(inst, w, 0, 0b000, 1, 1)),
        Op::Ldaddl => plain(check_lse(inst, w, 0, 0b000, 0, 1)),
        Op::Ldclr => plain(check_lse(inst, w, 0, 0b001, 0, 0)),
        Op::Ldclra => plain(check_lse(inst, w, 0, 0b001, 1, 0)),
        Op::Ldclral => plain(check_lse(inst, w, 0, 0b001, 1, 1)),
        Op::Ldclrl => plain(check_lse(inst, w, 0, 0b001, 0, 1)),
        Op::Ldeor => plain(check_lse(inst, w, 0, 0b010, 0, 0)),
        Op::Ldeora => plain(check_lse(inst, w, 0, 0b010, 1, 0)),
        Op::Ldeoral => plain(check_lse(inst, w, 0, 0b010, 1, 1)),
        Op::Ldeorl => plain(check_lse(inst, w, 0, 0b010, 0, 1)),
        Op::Ldset => plain(check_lse(inst, w, 0, 0b011, 0, 0)),
        Op::Ldseta => plain(check_lse(inst, w, 0, 0b011, 1, 0)),
        Op::Ldsetal => plain(check_lse(inst, w, 0, 0b011, 1, 1)),
        Op::Ldsetl => plain(check_lse(inst, w, 0, 0b011, 0, 1)),
        Op::Ldsmax => plain(check_lse(inst, w, 0, 0b100, 0, 0)),
        Op::Ldsmaxa => plain(check_lse(inst, w, 0, 0b100, 1, 0)),
        Op::Ldsmaxal => plain(check_lse(inst, w, 0, 0b100, 1, 1)),
        Op::Ldsmaxl => plain(check_lse(inst, w, 0, 0b100, 0, 1)),
        Op::Ldsmin => plain(check_lse(inst, w, 0, 0b101, 0, 0)),
        Op::Ldsmina => plain(check_lse(inst, w, 0, 0b101, 1, 0)),
        Op::Ldsminal => plain(check_lse(inst, w, 0, 0b101, 1, 1)),
        Op::Ldsminl => plain(check_lse(inst, w, 0, 0b101, 0, 1)),
        Op::Ldumax => plain(check_lse(inst, w, 0, 0b110, 0, 0)),
        Op::Ldumaxa => plain(check_lse(inst, w, 0, 0b110, 1, 0)),
        Op::Ldumaxal => plain(check_lse(inst, w, 0, 0b110, 1, 1)),
        Op::Ldumaxl => plain(check_lse(inst, w, 0, 0b110, 0, 1)),
        Op::Ldumin => plain(check_lse(inst, w, 0, 0b111, 0, 0)),
        Op::Ldumina => plain(check_lse(inst, w, 0, 0b111, 1, 0)),
        Op::Lduminal => plain(check_lse(inst, w, 0, 0b111, 1, 1)),
        Op::Lduminl => plain(check_lse(inst, w, 0, 0b111, 0, 1)),
        Op::Swp => plain(check_lse(inst, w, 1, 0b000, 0, 0)),
        Op::Swpa => plain(check_lse(inst, w, 1, 0b000, 1, 0)),
        Op::Swpal => plain(check_lse(inst, w, 1, 0b000, 1, 1)),
        Op::Swpl => plain(check_lse(inst, w, 1, 0b000, 0, 1)),
        Op::Cas => plain(check_cas(inst, w, 0, 0)),
        Op::Casa => plain(check_cas(inst, w, 1, 0)),
        Op::Casal => plain(check_cas(inst, w, 1, 1)),
        Op::Casl => plain(check_cas(inst, w, 0, 1)),
        Op::Ldar => plain(check_ordered(inst, w, true, None)),
        Op::Ldarb => plain(check_ordered(inst, w, true, Some(0b00))),
        Op::Ldarh => plain(check_ordered(inst, w, true, Some(0b01))),
        Op::Stlr => plain(check_ordered(inst, w, false, None)),
        Op::Stlrb => plain(check_ordered(inst, w, false, Some(0b00))),
        Op::Stlrh => plain(check_ordered(inst, w, false, Some(0b01))),
        Op::Dsb => plain(check_barrier(inst, w, 0b100)),
        Op::Dmb => plain(check_barrier(inst, w, 0b101)),
        Op::Isb => plain(check_barrier(inst, w, 0b110)),
        Op::Brk => plain(check_brk(inst, w)),
        // The unconditional trap pseudos are the machine IR's `BRK #1`. A
        // carrier with operands (a conditional or unexpanded guard) would be
        // miscompiled as an unconditional trap, so it is a mismatch.
        Op::TrapOverflow
        | Op::TrapBoundsCheck
        | Op::TrapNull
        | Op::TrapDivZero
        | Op::TrapShiftRange => plain(arity(inst, 0).and_then(|()| {
            if w == 0xD420_0020 {
                Ok(())
            } else {
                Err(format!(
                    "an unconditional trap is BRK #1 (0xd4200020), decoded {w:#010x}"
                ))
            }
        })),
        // A conditional trap carrier has no single-word encoding: the late
        // expansion replaces it by a compare, a conditional branch and BRK #1
        // (each decoded here against its own intent, and bound together by
        // the trap-expansion check after this pass), and the encoder refuses
        // a survivor. A word recorded for a carrier is therefore a mismatch.
        Op::TrapNullIfZero
        | Op::TrapDivZeroIfZero
        | Op::TrapBoundsCheckExact
        | Op::TrapShiftRangeIfOOB
        | Op::TrapOverflowExact => Err(format!(
            "{:?} is a trap carrier: only its expansion is emitted, decoded {w:#010x}",
            inst.opcode
        )),
        // The machine IR's Nop is the architectural NOP, whatever operands a
        // retired copy left on it.
        Op::Nop => plain(if w == 0xD503_201F {
            Ok(())
        } else {
            Err(format!(
                "Nop requires the architectural NOP 0xd503201f, decoded {w:#010x}"
            ))
        }),
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::decode_bit_masks;
    use std::collections::BTreeSet;

    /// Over every (N, immr, imms), the canonical decodes are exactly the
    /// bitmask immediates, each with one encoding: an element of size e has
    /// e - 1 run lengths and e rotations, so 5,334 = 2*1 + 4*3 + ... + 64*63
    /// for 64-bit registers and 1,302 (element sizes up to 32) for 32-bit
    /// ones; none is all-zeros or all-ones.
    #[test]
    fn decode_bit_masks_enumerates_each_bitmask_immediate_once() {
        for (regsize, expected) in [(64u32, 5334usize), (32, 1302)] {
            let mut masks = BTreeSet::new();
            let mut decoded = 0;
            for n in 0..2 {
                for immr in 0..64 {
                    for imms in 0..64 {
                        if let Some(mask) = decode_bit_masks(n, imms, immr, regsize) {
                            decoded += 1;
                            masks.insert(mask);
                            let all_ones = if regsize == 64 { u64::MAX } else { 0xFFFF_FFFF };
                            assert!(mask != 0 && mask != all_ones);
                        }
                    }
                }
            }
            assert_eq!((decoded, masks.len()), (expected, expected), "{regsize}");
        }
        // Non-canonical rotation bits above the element size are refused.
        assert_eq!(decode_bit_masks(1, 0, 0, 64), Some(1));
        assert_eq!(
            decode_bit_masks(0, 0b111100, 0, 64),
            Some(0x5555_5555_5555_5555)
        );
        assert_eq!(decode_bit_masks(0, 0b111100, 0b000010, 64), None);
        assert_eq!(decode_bit_masks(1, 0, 0, 32), None);
    }
}
