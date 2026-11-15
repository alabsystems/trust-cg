//! Strict ADD/SUB-immediate word binding and the existing decoded value model
//! applied to an explicit register state. No memory, ABI or proof authority.

use crate::aarch64_value_decode_proofs::{
    A64Effect, A64ValueWord, FieldOverrides, decode_a64_value_word,
    denote_add_sub_immediate_from_operand,
};
use crate::smt::{SmtExpr, SmtSort};
use std::collections::BTreeMap;
use trust_cg_ir::{AArch64Opcode as Op, MachInst, MachOperand, SpecialReg};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AddSubImmediateRegister {
    Gpr(u8),
    Sp,
}

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum AddSubImmediateError {
    #[error("add/sub-immediate intent: {0}")]
    Intent(&'static str),
    #[error("add/sub-immediate word: {0}")]
    Word(String),
    #[error("add/sub-immediate state: {0}")]
    State(&'static str),
}

/// The exact decoded word after every field was matched to the machine intent.
/// This can evaluate the existing architectural value model, not certify it.
#[derive(Debug, Clone, Copy)]
pub struct BoundAddSubImmediate {
    decoded: A64ValueWord,
    width: u32,
    source: AddSubImmediateRegister,
    destination: AddSubImmediateRegister,
    immediate: u64,
    subtract: bool,
}

impl BoundAddSubImmediate {
    pub fn width(&self) -> u32 {
        self.width
    }
    pub fn source(&self) -> AddSubImmediateRegister {
        self.source
    }
    pub fn destination(&self) -> AddSubImmediateRegister {
        self.destination
    }
    pub fn immediate(&self) -> u64 {
        self.immediate
    }
    pub fn subtracts(&self) -> bool {
        self.subtract
    }

    /// Read only the named full-X/SP source, then reuse the existing decoded
    /// ADD/SUB-immediate denotation. W reads and writes retain its truncation
    /// and zero-extension rules. No other register, NZCV or memory is written.
    pub fn effect(
        &self,
        sp: &SmtExpr,
        registers: &BTreeMap<u8, SmtExpr>,
    ) -> Result<A64Effect, AddSubImmediateError> {
        let source = match self.source {
            AddSubImmediateRegister::Sp => sp,
            AddSubImmediateRegister::Gpr(index) => registers
                .get(&index)
                .ok_or(AddSubImmediateError::State("missing source register"))?,
        };
        if source.sort() != SmtSort::BitVec(64) {
            return Err(AddSubImmediateError::State(
                "source must be a full 64-bit register",
            ));
        }
        let value = if self.width == 64 {
            source.clone()
        } else {
            source.clone().extract(31, 0)
        };
        denote_add_sub_immediate_from_operand(&self.decoded, &FieldOverrides::default(), value)
            .map_err(|error| AddSubImmediateError::Word(error.to_string()))
    }
}

fn register(operand: &MachOperand) -> Option<(u32, u32)> {
    match operand {
        MachOperand::PReg(p) => match p.encoding() {
            0..=31 => Some((1, u32::from(p.encoding()))),
            32..=63 => Some((0, u32::from(p.encoding() - 32))),
            _ => None,
        },
        MachOperand::Special(SpecialReg::SP) => Some((1, 31)),
        _ => None,
    }
}

/// Match every ADD/SUB-immediate field without treating ZR as SP, inferring a
/// bank, masking an immediate, or accepting an extra operand. Flag-writing
/// forms are outside this NZCV-preserving contract.
pub fn bind_add_sub_immediate_word(
    intent: &MachInst,
    word: u32,
) -> Result<BoundAddSubImmediate, AddSubImmediateError> {
    use AddSubImmediateError as E;
    let (want_op, want_sh) = match intent.opcode {
        Op::AddRI => (0, 0),
        Op::SubRI => (1, 0),
        Op::AddRIShift12 => (0, 1),
        _ => return Err(E::Intent("unsupported opcode")),
    };
    let [dst, src, MachOperand::Imm(imm @ 0..=4095)] = intent.operands.as_slice() else {
        return Err(E::Intent("requires two registers and one imm12"));
    };
    let (want_sf, want_rd) = register(dst).ok_or(E::Intent("destination is not W/X/SP"))?;
    let (source_sf, want_rn) = register(src).ok_or(E::Intent("source is not W/X/SP"))?;
    if want_sf != source_sf {
        return Err(E::Intent("register widths differ"));
    }
    let decoded = decode_a64_value_word(word).map_err(|e| E::Word(e.to_string()))?;
    let A64ValueWord::AddSubImm {
        sf,
        op,
        s,
        sh,
        imm12,
        rn,
        rd,
    } = decoded
    else {
        return Err(E::Word("different instruction class".into()));
    };
    if (sf, op, s, sh, imm12, rn, rd)
        != (want_sf, want_op, 0, want_sh, *imm as u32, want_rn, want_rd)
    {
        return Err(E::Word("decoded fields differ from intent".into()));
    }
    let location = |field| {
        if field == 31 {
            AddSubImmediateRegister::Sp
        } else {
            AddSubImmediateRegister::Gpr(field as u8)
        }
    };
    Ok(BoundAddSubImmediate {
        decoded,
        width: 32 << sf,
        source: location(rn),
        destination: location(rd),
        immediate: u64::from(imm12) << (12 * sh),
        subtract: op == 1,
    })
}

#[cfg(test)]
#[path = "aarch64_add_sub_immediate_tests.rs"]
mod tests;
