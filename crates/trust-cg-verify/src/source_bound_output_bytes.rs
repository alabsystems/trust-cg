// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Bounded LIR-to-byte output transport, without production admission.
//!
//! Decode actual A64 words independently of the encoder and allocated MachIR.
//! Compare every ordered output store with the original LIR before constructing
//! the conditional memory theorem. Live writable caller storage remains a
//! premise; framed code also requires separation from its private frame.
//! It does not bind TrustIR to LIR or prove this Rust checker's implementation.

use super::{Aarch64OutputFrame, M, MachineType, O, obligation_for_trace_in_frame};
use crate::lowering_proof::ProofObligation;
use trust_cg_ir::function::Signature;
use trust_cg_ir::regs::{PReg, X30};
use trust_cg_ir::{MachFunction, MachInst};
use trust_cg_lower::Function;

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum OutputByteError {
    #[error("source is outside the bounded output-store domain")]
    SourceDomain,
    #[error(
        "complete bounded A64 words with an ordinary return and a supported frame are required"
    )]
    FrameEnvelope,
    #[error("unsupported output-memory A64 word {word:#010x} at byte {offset}")]
    UnsupportedWord { offset: usize, word: u32 },
    #[error("decoded output body reads an undefined value or exceeds the bounded store domain")]
    BodyDomain,
    #[error("original LIR and decoded final bytes have different ordered stores")]
    StoreMismatch,
}

/// Immutable LIR and byte endpoints of a conditional diagnostic theorem.
///
/// This owner grants no instruction, publication, cache or JIT-installation
/// credit. Its theorem still requires caller-memory ownership and validity.
/// Any later relocation or byte change requires a new check.
pub struct CheckedAarch64OutputBytes<'a> {
    source: &'a Function,
    code: &'a [u8],
    frame: Aarch64OutputFrame,
    obligation: ProofObligation,
}

impl<'a> CheckedAarch64OutputBytes<'a> {
    pub fn source(&self) -> &'a Function {
        self.source
    }

    pub fn code(&self) -> &'a [u8] {
        self.code
    }

    pub fn frame(&self) -> Aarch64OutputFrame {
        self.frame
    }

    pub fn obligation(&self) -> &ProofObligation {
        &self.obligation
    }
}

fn register(index: u32) -> Option<O> {
    // Every body register has X width. SP/ZR, the platform register,
    // callee-saved registers and the saved FP/LR are outside this domain.
    (index <= 17).then(|| O::PReg(PReg::new(index as u16)))
}

fn decode_body(word: u32) -> Option<MachInst> {
    if word == 0xd503_201f {
        return Some(MachInst::new(M::Nop, vec![]));
    }
    let rt = || register(word & 31);
    let rn = || register((word >> 5) & 31);
    let rm = || register((word >> 16) & 31);
    let immediate = |value: u32| O::Imm(i64::from(value));
    let (opcode, operands) = if word & 0xffe0_ffe0 == 0xaa00_03e0 {
        // ORR Xd,XZR,Xm,LSL #0 (MOV register).
        (M::MOVXrr, vec![rt()?, rm()?])
    } else if word & 0xffc0_0000 == 0x9100_0000 {
        // ADD immediate, 64 bits, no flags, unshifted immediate.
        (M::AddRI, vec![rt()?, rn()?, immediate((word >> 10) & 4095)])
    } else if word & 0xffe0_fc00 == 0x8b00_0000 {
        // ADD shifted-register, 64 bits, no flags, LSL #0 only.
        (M::AddRR, vec![rt()?, rn()?, rm()?])
    } else if word & 0xffe0_8000 == 0x9b00_0000 {
        // MADD Xd,Xn,Xm,Xa: 64-bit wrapping multiply-add, not MSUB,
        // widening multiply, or an implicit-zero MUL alias.
        (
            M::Madd,
            vec![rt()?, rn()?, rm()?, register((word >> 10) & 31)?],
        )
    } else if word & 0xffc0_0000 == 0xf900_0000 {
        // STR Xt,[Xn,#imm12*8], unsigned offset, no writeback.
        (
            M::StrRI,
            vec![rt()?, rn()?, immediate(((word >> 10) & 4095) * 8)],
        )
    } else if word & 0xffc0_0000 == 0xa900_0000 {
        // STP Xt1,Xt2,[Xn,#signed-imm7*8], offset addressing only.
        let field = i64::from((word >> 15) & 127);
        let offset = if field >= 64 { field - 128 } else { field } * 8;
        (
            M::StpRI,
            vec![rt()?, register((word >> 10) & 31)?, rn()?, O::Imm(offset)],
        )
    } else {
        let opcode = match word & 0xff80_0000 {
            0xd280_0000 => M::Movz,
            0x9280_0000 => M::Movn,
            0xf280_0000 => M::Movk,
            _ => return None,
        };
        (
            opcode,
            vec![
                rt()?,
                immediate((word >> 5) & 65535),
                immediate(((word >> 21) & 3) * 16),
            ],
        )
    };
    Some(MachInst::new(opcode, operands))
}

pub(super) fn decoded_body(
    source: &Function,
    code: &[u8],
) -> Result<(MachFunction, Aarch64OutputFrame), OutputByteError> {
    if !code.len().is_multiple_of(4) || !(1..=259).contains(&(code.len() / 4)) {
        return Err(OutputByteError::FrameEnvelope);
    }
    let words: Vec<_> = code
        .as_chunks::<4>()
        .0
        .iter()
        .map(|b| u32::from_le_bytes(*b))
        .collect();
    let count = words.len();
    if words[count - 1] != 0xd65f_03c0 {
        return Err(OutputByteError::FrameEnvelope);
    }
    // Partial frame envelopes never fall through as frameless bodies.
    let framed = words[0] == 0xa9bf_7bfd
        || words.get(1) == Some(&0x9100_03fd)
        || count >= 2 && words[count - 2] == 0xa8c1_7bfd;
    let (start, end, frame) = if framed {
        if count < 4
            || words[0] != 0xa9bf_7bfd
            || words[1] != 0x9100_03fd
            || words[count - 2] != 0xa8c1_7bfd
        {
            return Err(OutputByteError::FrameEnvelope);
        }
        (2, count - 2, Aarch64OutputFrame::FpLr16)
    } else {
        if count > 256 {
            return Err(OutputByteError::FrameEnvelope);
        }
        (0, count - 1, Aarch64OutputFrame::Frameless)
    };
    let mut machine = MachFunction::new(
        source.name.clone(),
        Signature::new(
            vec![MachineType::I64; source.signature.params.len()],
            vec![],
        ),
    );
    for (index, &word) in words.iter().enumerate().take(end).skip(start) {
        let instruction = decode_body(word).ok_or(OutputByteError::UnsupportedWord {
            offset: index * 4,
            word,
        })?;
        let id = machine.push_inst(instruction);
        machine.append_inst(machine.entry, id);
    }
    let id = machine.push_inst(MachInst::new(M::Ret, vec![O::PReg(X30)]));
    machine.append_inst(machine.entry, id);
    Ok((machine, frame))
}

/// Compare a complete bounded output writer with its actual instruction bytes.
///
/// The result retains immutable endpoints and the conditional memory theorem.
/// It does not authorize an effectful frame in the production verifier.
pub fn check_aarch64_output_bytes<'a>(
    source: &'a Function,
    code: &'a [u8],
) -> Result<CheckedAarch64OutputBytes<'a>, OutputByteError> {
    let view = super::super::linear::source_view(source).ok_or(OutputByteError::SourceDomain)?;
    let expected = super::source_stores(&view).ok_or(OutputByteError::SourceDomain)?;
    let (machine, frame) = decoded_body(&view, code)?;
    let actual = super::machine_stores(&view, &machine).ok_or(OutputByteError::BodyDomain)?;
    if expected != actual {
        return Err(OutputByteError::StoreMismatch);
    }
    let obligation = obligation_for_trace_in_frame(&view, &machine, &expected, frame)
        .ok_or(OutputByteError::BodyDomain)?;
    Ok(CheckedAarch64OutputBytes {
        source,
        code,
        frame,
        obligation,
    })
}

#[cfg(test)]
#[path = "source_bound_output_bytes_tests.rs"]
mod tests;
