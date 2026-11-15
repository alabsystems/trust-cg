// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Independent A64 decoding for bounded scalar-cell caller observations.
//! Relocations are explicit input endpoints, not inferred from BL placeholders.
//! Whole-object parsing, linked destinations and callback contracts are separate.
//! A64 reference: https://documentation-service.arm.com/static/6245c734b059dc5ff9a8bdab

use super::{CheckedAarch64ScalarCellSource, ScalarCellFrameError, ScalarCellSourceError};
use trust_cg_ir::function::{Signature, StackSlot, Type};
use trust_cg_ir::regs::{D0, PReg, S0, SpecialReg, X0, X19, X20, X29, X30};
use trust_cg_ir::{AArch64Opcode as M, MachFunction, MachInst, MachOperand as O};
use trust_cg_lower::Function;

#[path = "source_bound_cell_elf.rs"]
pub(super) mod elf;

/// A function-relative ELF RELA record, including its resolved symbol name.
/// Callers must retain every relocation which can patch the supplied code.
/// This record alone does not establish correspondence to an object file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarCellRelocation<'a> {
    pub offset: u64,
    pub kind: u32,
    pub symbol: &'a str,
    pub addend: i64,
}

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ScalarCellByteError {
    #[error(transparent)]
    Source(#[from] ScalarCellSourceError),
    #[error("a complete bounded sequence of little-endian A64 words is required")]
    Length,
    #[error("invalid, duplicate or unsupported scalar-cell relocation")]
    Relocation,
    #[error("unsupported scalar-cell A64 word {word:#010x} at byte {offset}")]
    Word { offset: usize, word: u32 },
    #[error(transparent)]
    Observations(#[from] ScalarCellFrameError),
}

/// Immutable original-source, LIR, code and relocation endpoints. Construction
/// supplies diagnostic correspondence only, without compiler proof credit.
/// Any byte, symbol, offset, kind or addend change requires a new check.
pub struct CheckedAarch64ScalarCellBytes<'a> {
    source: CheckedAarch64ScalarCellSource<'a>,
    code: &'a [u8],
    relocations: &'a [ScalarCellRelocation<'a>],
}

impl<'a> CheckedAarch64ScalarCellBytes<'a> {
    pub fn source(&self) -> &CheckedAarch64ScalarCellSource<'a> {
        &self.source
    }
    pub fn code(&self) -> &'a [u8] {
        self.code
    }
    pub fn relocations(&self) -> &'a [ScalarCellRelocation<'a>] {
        self.relocations
    }
}

fn gpr(index: u32, width: usize) -> Option<O> {
    (index < 31).then(|| O::PReg(PReg::new(index as u16 + if width == 4 { 32 } else { 0 })))
}

fn fpr(index: u32, width: usize) -> O {
    O::PReg(PReg::new(index as u16 + if width == 4 { 128 } else { 96 }))
}

fn envelope_word(word: u32) -> Option<MachInst> {
    let pair = |a, b, offset| {
        vec![
            O::PReg(a),
            O::PReg(b),
            O::Special(SpecialReg::SP),
            O::Imm(offset),
        ]
    };
    let sp = |offset| {
        vec![
            O::Special(SpecialReg::SP),
            O::Special(SpecialReg::SP),
            O::Imm(offset),
        ]
    };
    let (op, args) = match word {
        0xa9be_4ff4 => (M::StpPreIndex, pair(X20, X19, -32)),
        0xa901_7bfd => (M::StpRI, pair(X29, X30, 16)),
        0x9100_43fd => (
            M::AddRI,
            vec![O::PReg(X29), O::Special(SpecialReg::SP), O::Imm(16)],
        ),
        0xd100_43ff => (M::SubRI, sp(16)),
        0x9100_43ff => (M::AddRI, sp(16)),
        0xa941_7bfd => (M::LdpRI, pair(X29, X30, 16)),
        0xa8c2_4ff4 => (M::LdpPostIndex, pair(X20, X19, 32)),
        _ => return None,
    };
    Some(MachInst::new(op, args))
}

fn decode(word: u32) -> Option<MachInst> {
    if let Some(inst) = envelope_word(word) {
        return Some(inst);
    }
    if matches!(word, 0xd503_201f | 0x1400_0001) {
        // Hardware NOP, or an unconditional branch to the next word. No
        // other branch, skipped instruction, loop or indirect transfer fits.
        return Some(MachInst::new(M::Nop, vec![]));
    }
    let rt = word & 31;
    let rn = (word >> 5) & 31;
    let rm = (word >> 16) & 31;
    let immediate = |n: u32| O::Imm(i64::from(n));
    let (opcode, operands) = if word & 0xffe0_ffe0 == 0xaa00_03e0 {
        (M::MOVXrr, vec![gpr(rt, 8)?, gpr(rm, 8)?])
    } else if matches!(word & 0xffc0_0000, 0x9100_0000 | 0xd100_0000) {
        let op = if word & 0x4000_0000 == 0 {
            M::AddRI
        } else {
            M::SubRI
        };
        (
            op,
            vec![gpr(rt, 8)?, gpr(rn, 8)?, immediate((word >> 10) & 4095)],
        )
    } else if word & 0xffe0_fc00 == 0x4ea0_1c00 {
        // ORR Vd.16B,Vn.16B,Vm.16B. The byte interpreter only accepts a copy
        // (n == m) and tracks the lower 64 bits used by this scalar ABI.
        (
            M::NeonOrrV,
            vec![fpr(rt, 8), fpr(rn, 8), fpr(rm, 8), O::Imm(1)],
        )
    } else if matches!(word & 0xffff_fc00, 0x1e27_0000 | 0x9e67_0000) {
        let width = if word >> 31 == 0 { 4 } else { 8 };
        (M::FmovGprFpr, vec![fpr(rt, width), gpr(rn, width)?])
    } else if matches!(
        word & 0xffc0_0000,
        0xbd00_0000 | 0xbd40_0000 | 0xfd00_0000 | 0xfd40_0000
    ) {
        let width = if word & 0x4000_0000 == 0 { 4 } else { 8 };
        let op = if word & 0x0040_0000 == 0 {
            M::StrRI
        } else {
            M::LdrRI
        };
        (
            op,
            vec![
                fpr(rt, width),
                gpr(rn, 8)?,
                immediate(((word >> 10) & 4095) * width as u32),
            ],
        )
    } else {
        let (op, width) = match word & 0xff80_0000 {
            0x5280_0000 => (M::Movz, 4),
            0x1280_0000 => (M::Movn, 4),
            0x7280_0000 => (M::Movk, 4),
            0xd280_0000 => (M::Movz, 8),
            0x9280_0000 => (M::Movn, 8),
            0xf280_0000 => (M::Movk, 8),
            _ => return None,
        };
        let shift = ((word >> 21) & 3) * 16;
        if shift >= width as u32 * 8 {
            return None;
        }
        (
            op,
            vec![
                gpr(rt, width)?,
                immediate((word >> 5) & 65535),
                immediate(shift),
            ],
        )
    };
    Some(MachInst::new(opcode, operands))
}

/// Decode the exact instruction words and match each BL to one zero-addend
/// R_AARCH64_CALL26 (283) record and its original source callee. This accepts
/// unresolved object code only; it cannot establish linked call destinations.
pub fn check_aarch64_scalar_cell_bytes<'a>(
    module: &'a trust_ir::Module,
    lir: &'a Function,
    code: &'a [u8],
    relocations: &'a [ScalarCellRelocation<'a>],
) -> Result<CheckedAarch64ScalarCellBytes<'a>, ScalarCellByteError> {
    let source = super::check_aarch64_scalar_cell_source(module, lir)?;
    if code.len() % 4 != 0 || !(9..=256).contains(&(code.len() / 4)) {
        return Err(ScalarCellByteError::Length);
    }
    if relocations.len() != source.call_count() {
        return Err(ScalarCellByteError::Relocation);
    }
    let mut sites = std::collections::BTreeMap::new();
    for relocation in relocations {
        let offset =
            usize::try_from(relocation.offset).map_err(|_| ScalarCellByteError::Relocation)?;
        if relocation.kind != 283
            || relocation.addend != 0
            || offset % 4 != 0
            || offset >= code.len()
            || sites.insert(offset, relocation).is_some()
        {
            return Err(ScalarCellByteError::Relocation);
        }
    }
    let width = source.cell_width();
    let ty = if width == 4 { Type::F32 } else { Type::F64 };
    let mut machine = MachFunction::new(
        lir.name.clone(),
        Signature::new(vec![ty.clone(); lir.signature.params.len()], vec![ty]),
    );
    machine.stack_slots = vec![StackSlot::new(width as u32, width as u32)];
    for (index, bytes) in code.chunks_exact(4).enumerate() {
        let offset = index * 4;
        let word = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
        let fail = || ScalarCellByteError::Word { offset, word };
        let inst = if let Some(relocation) = sites.remove(&offset) {
            if word != 0x9400_0000 {
                return Err(ScalarCellByteError::Relocation);
            }
            let mut inst = MachInst::new(M::Bl, vec![O::Symbol(relocation.symbol.into())]);
            inst.implicit_uses = if width == 4 { &[X0, S0] } else { &[X0, D0] };
            inst
        } else if index + 1 == code.len() / 4 {
            if word != 0xd65f_03c0 {
                return Err(fail());
            }
            let mut inst = MachInst::new(M::Ret, vec![O::PReg(X30)]);
            inst.implicit_uses = if width == 4 { &[S0] } else { &[D0] };
            inst
        } else {
            decode(word).ok_or_else(fail)?
        };
        let id = machine.push_inst(inst);
        machine.append_inst(machine.entry, id);
    }
    if !sites.is_empty() {
        return Err(ScalarCellByteError::Relocation);
    }
    super::cell_frame::checked(lir, &machine)?;
    Ok(CheckedAarch64ScalarCellBytes {
        source,
        code,
        relocations,
    })
}
