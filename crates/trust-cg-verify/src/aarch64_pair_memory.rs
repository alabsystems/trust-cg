// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Operand-exact encoding agreement for the existing AArch64 pair-memory slice.
//!
//! This is the independent pair decoder previously owned by codegen's ENC-5
//! check. It never calls the encoder or consumes its pair descriptor. Both the
//! always-on emission check and future memory semantics can use the same checked
//! word and operands without another opcode recognizer.
//!
//! Agreement is encoding evidence, NOT source correspondence, memory ownership,
//! instruction semantics, independent proof replay or execution authority. This
//! check does not interpret MachIR flags/implicit effects, nor establish that a
//! supplied word occupies an actual emitted instruction extent without fixups.
//! Those obligations remain with the consuming boundary. In particular, this
//! module supplies no opcode-registry or function-verifier promotion credit.

use std::fmt;
use trust_cg_ir::{AArch64Opcode as Op, MachInst, MachOperand, SpecialReg};

/// The exact transfer bank and width; SIMD field 31 is a real register, whereas
/// GPR field 31 is the zero register, never SP.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PairMemoryFormat {
    W32,
    X64,
    S32,
    D64,
    Q128,
}

impl PairMemoryFormat {
    pub const fn element_bytes(self) -> u8 {
        match self {
            Self::W32 | Self::S32 => 4,
            Self::X64 | Self::D64 => 8,
            Self::Q128 => 16,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PairMemoryMode {
    SignedOffset,
    PreIndex,
    PostIndex,
}

/// Field 31 in the address position denotes SP, not a zero register.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PairMemoryBase {
    Register(u8),
    Sp,
}

/// A refusal with the same diagnostic text as the existing ENC-5 pair check.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("{message}")]
pub struct PairEncodingError {
    message: String,
}

impl PairEncodingError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

#[derive(Debug)]
struct DecodedPairWord {
    opc: u32,
    v: u32,
    mode: u32,
    load: bool,
    imm7: i32,
    rt2: u32,
    rn: u32,
    rt: u32,
}

/// Immutable instruction/word agreement, constructed only by
/// [`check_pair_encoding`]. The word is copied; the instruction stays borrowed.
/// Its encoding fields cannot be replaced independently of the checked inputs.
/// This is not a proof or a caller-supplied trusted frame descriptor.
///
/// ```compile_fail
/// use trust_cg_ir::MachInst;
/// use trust_cg_verify::aarch64_pair_memory::CheckedPairEncoding;
/// fn forge(instruction: &MachInst) -> CheckedPairEncoding<'_> {
///     CheckedPairEncoding { instruction, word: 0, decoded: todo!() }
/// }
/// ```
///
/// ```compile_fail
/// use trust_cg_verify::aarch64_pair_memory::CheckedPairEncoding;
/// fn replace_word(checked: &mut CheckedPairEncoding<'_>) {
///     checked.word = 0;
/// }
/// ```
#[derive(Debug)]
pub struct CheckedPairEncoding<'a> {
    instruction: &'a MachInst,
    word: u32,
    decoded: DecodedPairWord,
}

impl<'a> CheckedPairEncoding<'a> {
    pub fn instruction(&self) -> &'a MachInst {
        self.instruction
    }

    pub fn word(&self) -> u32 {
        self.word
    }

    pub fn format(&self) -> PairMemoryFormat {
        match (self.decoded.v, self.decoded.opc) {
            (0, 0) => PairMemoryFormat::W32,
            (0, 2) => PairMemoryFormat::X64,
            (1, 0) => PairMemoryFormat::S32,
            (1, 1) => PairMemoryFormat::D64,
            (1, 2) => PairMemoryFormat::Q128,
            _ => unreachable!("private checked pair format"),
        }
    }

    pub fn mode(&self) -> PairMemoryMode {
        match self.decoded.mode {
            1 => PairMemoryMode::PostIndex,
            2 => PairMemoryMode::SignedOffset,
            3 => PairMemoryMode::PreIndex,
            _ => unreachable!("private checked pair addressing mode"),
        }
    }

    pub fn is_load(&self) -> bool {
        self.decoded.load
    }

    /// Architectural fields in transfer order. Interpret field 31 using
    /// [`Self::format`]: GPR zero, or the genuine SIMD/FP register 31.
    pub fn transfer_fields(&self) -> [u8; 2] {
        [self.decoded.rt as u8, self.decoded.rt2 as u8]
    }

    pub fn base(&self) -> PairMemoryBase {
        match self.decoded.rn {
            31 => PairMemoryBase::Sp,
            field => PairMemoryBase::Register(field as u8),
        }
    }

    pub fn byte_offset(&self) -> i64 {
        i64::from(self.decoded.imm7) * i64::from(self.format().element_bytes())
    }
}

// Arm A64 pair diagram: opc | 101 | V | 0 | mode | L | imm7 | Rt2 | Rn | Rt.
// Preserve the shipping ENC-5 subset: no non-temporal mode, LDPSW, tag pair,
// or unallocated width may stand in for one of its six modeled opcodes.
fn decode_pair_word(word: u32) -> Option<DecodedPairWord> {
    if (word >> 27) & 0b111 != 0b101 || (word >> 25) & 1 != 0 {
        return None;
    }
    let opc = word >> 30;
    let v = (word >> 26) & 1;
    let mode = (word >> 23) & 0b11;
    if mode == 0 || (v == 0 && !matches!(opc, 0 | 2)) || (v == 1 && opc == 3) {
        return None;
    }
    let raw7 = ((word >> 15) & 127) as i32;
    Some(DecodedPairWord {
        opc,
        v,
        mode,
        load: (word >> 22) & 1 != 0,
        imm7: (raw7 << 25) >> 25,
        rt2: (word >> 10) & 31,
        rn: (word >> 5) & 31,
        rt: word & 31,
    })
}

// Independent intent identity: (opc, V, byte scale, register field).
// Do not mask another physical bank down to its hardware register number.
fn transfer(operand: &MachOperand) -> Option<(u32, u32, i64, u32)> {
    match operand {
        MachOperand::PReg(reg) => match reg.encoding() {
            0..=30 => Some((2, 0, 8, u32::from(reg.encoding()))),
            32..=62 => Some((0, 0, 4, u32::from(reg.encoding() - 32))),
            64..=95 => Some((2, 1, 16, u32::from(reg.encoding() - 64))),
            96..=127 => Some((1, 1, 8, u32::from(reg.encoding() - 96))),
            128..=159 => Some((0, 1, 4, u32::from(reg.encoding() - 128))),
            160 => Some((2, 0, 8, 31)),
            161 => Some((0, 0, 4, 31)),
            _ => None,
        },
        MachOperand::Special(SpecialReg::XZR) => Some((2, 0, 8, 31)),
        MachOperand::Special(SpecialReg::WZR) => Some((0, 0, 4, 31)),
        _ => None,
    }
}

fn require_field<T: PartialEq + fmt::Display>(
    name: &str,
    actual: T,
    expected: T,
) -> Result<(), PairEncodingError> {
    if actual != expected {
        return Err(PairEncodingError::new(format!(
            "{name}: decoded {actual} but the intent requires {expected}"
        )));
    }
    Ok(())
}

/// Check one exact little-endian instruction word against its canonical pair
/// operands. All existing W/X/ZR and S/D/Q forms remain supported, including
/// the two Q-only post-index aliases and an omitted zero offset.
///
/// The caller must separately reject relocation holes and establish that these
/// are the actual emitted bytes before using the result at an emission boundary.
pub fn check_pair_encoding<'a>(
    instruction: &'a MachInst,
    bytes: &[u8],
) -> Result<CheckedPairEncoding<'a>, PairEncodingError> {
    let word_bytes: [u8; 4] = bytes.try_into().map_err(|_| {
        PairEncodingError::new(format!(
            "instruction byte range is {} bytes; AArch64 instructions are exactly 4",
            bytes.len()
        ))
    })?;
    let word = u32::from_le_bytes(word_bytes);
    let (load_want, mode_want, q_only) = match instruction.opcode {
        Op::StpRI => (false, 2, false),
        Op::LdpRI => (true, 2, false),
        Op::StpPreIndex => (false, 3, false),
        Op::LdpPostIndex => (true, 1, false),
        Op::NeonLdpQPost => (true, 1, true),
        Op::NeonStpQPost => (false, 1, true),
        _ => {
            return Err(PairEncodingError::new(
                "instruction is not a modeled pair memory opcode",
            ));
        }
    };
    let (first, second, base, offset) = match instruction.operands.as_slice() {
        [first, second, base] => (first, second, base, 0),
        [first, second, base, MachOperand::Imm(offset)] => (first, second, base, *offset),
        _ => {
            return Err(PairEncodingError::new(
                "pair memory requires exactly two transfers, X/SP base and optional immediate",
            ));
        }
    };
    let rn_want = match base {
        MachOperand::PReg(reg) if reg.encoding() <= 31 => u32::from(reg.encoding()),
        MachOperand::Special(SpecialReg::SP) => 31,
        _ => {
            return Err(PairEncodingError::new(
                "pair memory base must be canonical X/SP",
            ));
        }
    };
    let (Some((opc_want, v_want, scale, rt_want)), Some((opc2, v2, scale2, rt2_want))) =
        (transfer(first), transfer(second))
    else {
        return Err(PairEncodingError::new(
            "pair memory requires canonical W/X/ZR or S/D/Q transfers",
        ));
    };
    if (opc_want, v_want, scale) != (opc2, v2, scale2) {
        return Err(PairEncodingError::new(
            "pair memory transfers must have matching widths and banks",
        ));
    }
    if q_only && (v_want != 1 || opc_want != 2) {
        return Err(PairEncodingError::new(
            "NEON Q-pair alias requires two Q registers",
        ));
    }
    if offset % scale != 0 || !(-64..=63).contains(&(offset / scale)) {
        return Err(PairEncodingError::new(
            "pair memory offset must be an aligned signed scaled imm7",
        ));
    }
    if load_want && rt_want == rt2_want {
        return Err(PairEncodingError::new(
            "load pair duplicate destinations are unpredictable, including field31",
        ));
    }
    if v_want == 0 && mode_want != 2 && rn_want != 31 && (rt_want == rn_want || rt2_want == rn_want)
    {
        return Err(PairEncodingError::new(
            "GPR pair writeback transfer/base overlap is unpredictable",
        ));
    }
    let decoded = decode_pair_word(word).ok_or_else(|| {
        PairEncodingError::new("pair intent does not decode as modeled pair memory")
    })?;
    require_field("pair opc", decoded.opc, opc_want)?;
    require_field("pair V", decoded.v, v_want)?;
    require_field("pair mode", decoded.mode, mode_want)?;
    require_field("pair L", decoded.load, load_want)?;
    require_field("pair signed imm7", i64::from(decoded.imm7), offset / scale)?;
    require_field("pair Rt", decoded.rt, rt_want)?;
    require_field("pair Rt2", decoded.rt2, rt2_want)?;
    require_field("pair Rn", decoded.rn, rn_want)?;
    Ok(CheckedPairEncoding {
        instruction,
        word,
        decoded,
    })
}

/// Shared symbolic X-register pair semantics. This is actual-word mathematics,
/// not an instruction/source proof or permission to access the returned ranges.
/// Both addresses and transfer values use the pre-instruction state.
#[derive(Debug)]
pub(crate) struct Gpr64PairEffect {
    pub registers: Vec<(u8, crate::smt::SmtExpr)>,
    pub sp: Option<crate::smt::SmtExpr>,
    pub memory: crate::smt::SmtExpr,
    pub addresses: [crate::smt::SmtExpr; 2],
}

pub(crate) fn gpr64_pair_effect(
    word: u32,
    sp: &crate::smt::SmtExpr,
    registers: &std::collections::BTreeMap<u8, crate::smt::SmtExpr>,
    memory: &crate::smt::SmtExpr,
) -> Result<Gpr64PairEffect, PairEncodingError> {
    use crate::memory_proofs::{encode_load_le, encode_store_le};
    use crate::smt::SmtExpr as E;
    let d = decode_pair_word(word).ok_or_else(|| PairEncodingError::new("not a pair word"))?;
    if d.v != 0
        || d.opc != 2
        || (d.load && d.rt == d.rt2)
        || (d.mode != 2 && d.rn != 31 && (d.rt == d.rn || d.rt2 == d.rn))
    {
        return Err(PairEncodingError::new(
            "outside predictable GPR64 pair semantics",
        ));
    }
    let read = |n: u32| -> Result<E, PairEncodingError> {
        if n == 31 {
            return Ok(E::bv_const(0, 64));
        }
        registers
            .get(&(n as u8))
            .cloned()
            .ok_or_else(|| PairEncodingError::new("missing pair register"))
    };
    let base = if d.rn == 31 { sp.clone() } else { read(d.rn)? };
    let updated = base
        .clone()
        .bvadd(E::bv_const((i64::from(d.imm7) * 8) as u64, 64));
    let first = if d.mode == 1 { base } else { updated.clone() };
    let second = first.clone().bvadd(E::bv_const(8, 64));
    let mut writes = Vec::new();
    let next_memory = if d.load {
        for (n, address) in [(d.rt, &first), (d.rt2, &second)] {
            if n != 31 {
                writes.push((n as u8, encode_load_le(memory, address, 8)));
            }
        }
        memory.clone()
    } else {
        let first_store = encode_store_le(memory, &first, &read(d.rt)?, 8);
        encode_store_le(&first_store, &second, &read(d.rt2)?, 8)
    };
    let next_sp = if d.mode == 2 {
        None
    } else if d.rn == 31 {
        Some(updated)
    } else {
        writes.push((d.rn as u8, updated));
        None
    };
    Ok(Gpr64PairEffect {
        registers: writes,
        sp: next_sp,
        memory: next_memory,
        addresses: [first, second],
    })
}

#[cfg(test)]
#[path = "aarch64_pair_memory_tests.rs"]
mod tests;
