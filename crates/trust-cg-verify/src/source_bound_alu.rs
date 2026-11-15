// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Arithmetic inside an independently checked complete affine source/body pair.
//! The outer checker establishes actual source values, register dataflow and
//! observable results, including optimized instruction sequences. This owner
//! does not guess a one-to-one source instruction from a target opcode.
//! The local theorem separately checks wrapping arithmetic against the machine
//! value model. Neither a raw reconstructed identity nor this constructor alone
//! supplies Formal evidence; the exact theorem still needs independent replay.

use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr as E;
use crate::source_bound_frame::SourceBoundFrame;
use trust_cg_ir::cc::OperandSize;
use trust_cg_ir::regs::SpecialReg;
use trust_cg_ir::{AArch64Opcode as M, InstId, MachOperand as O};

pub(crate) struct SourceBoundAlu<'owner, 'inputs> {
    _frame: &'owner SourceBoundFrame<'inputs>,
    obligation: ProofObligation,
}

impl<'owner, 'inputs> SourceBoundAlu<'owner, 'inputs> {
    pub(crate) fn bind(frame: &'owner SourceBoundFrame<'inputs>, id: InstId) -> Option<Self> {
        if frame.envelope_instructions().contains(&id)
            || !frame
                .machine()
                .blocks
                .iter()
                .any(|block| block.insts.contains(&id))
        {
            return None;
        }
        let inst = frame.machine().insts.get(id.0 as usize)?;
        let [O::PReg(dst), left, right] = inst.operands.as_slice() else {
            return None;
        };
        let bits = match dst.encoding() {
            0..=17 => 64,
            32..=49 => 32,
            _ => return None,
        };
        let mut inputs = Vec::new();
        let mut register = |operand: &O| -> Option<E> {
            let name = match operand {
                O::PReg(reg)
                    if (bits == 64 && reg.encoding() <= 17)
                        || (bits == 32 && (32..=49).contains(&reg.encoding())) =>
                {
                    format!("input_r{}", reg.encoding())
                }
                O::Special(SpecialReg::XZR) if bits == 64 => return Some(E::bv_const(0, bits)),
                O::Special(SpecialReg::WZR) if bits == 32 => return Some(E::bv_const(0, bits)),
                _ => return None,
            };
            if !inputs.iter().any(|(existing, _)| existing == &name) {
                inputs.push((name.clone(), bits));
            }
            Some(E::var(&name, bits))
        };
        let lhs = register(left)?;
        let rhs = match inst.opcode {
            M::AddRR | M::SubRR => register(right)?,
            M::AddRI | M::SubRI | M::AddRIShift12 => {
                let O::Imm(value @ 0..=4095) = right else {
                    return None;
                };
                let value = (*value as u64)
                    << if inst.opcode == M::AddRIShift12 {
                        12
                    } else {
                        0
                    };
                E::bv_const(value, bits)
            }
            M::LslRI => {
                let O::Imm(shift) = right else {
                    return None;
                };
                if !(0..i64::from(bits)).contains(shift) {
                    return None;
                }
                E::bv_const(*shift as u64, bits)
            }
            _ => return None,
        };
        let size = if bits == 32 {
            OperandSize::S32
        } else {
            OperandSize::S64
        };
        let (source, machine) = match inst.opcode {
            M::SubRR | M::SubRI => (
                lhs.clone()
                    .zero_ext(1)
                    .bvsub(rhs.clone().zero_ext(1))
                    .extract(bits - 1, 0),
                crate::aarch64_semantics::encode_sub_rr(size, lhs, rhs),
            ),
            M::LslRI => {
                let O::Imm(shift) = right else {
                    return None;
                };
                let shift = *shift as u32;
                // Bit wiring defines the wrapping shift independently of the
                // machine model's BV shift operator, without a wider multiply.
                let source = if shift == 0 {
                    lhs.clone()
                } else {
                    lhs.clone()
                        .extract(bits - shift - 1, 0)
                        .concat(E::bv_const(0, shift))
                };
                (source, lhs.bvshl(rhs))
            }
            _ => (
                lhs.clone()
                    .zero_ext(1)
                    .bvadd(rhs.clone().zero_ext(1))
                    .extract(bits - 1, 0),
                crate::aarch64_semantics::encode_add_rr(size, lhs, rhs),
            ),
        };
        Some(Self {
            _frame: frame,
            obligation: ProofObligation {
                name: format!(
                    "Source-bound AArch64 affine ALU (Rust body binding; replayed local arithmetic): {:?} i{bits}",
                    inst.opcode
                ),
                trust_ir_expr: source,
                aarch64_expr: machine,
                inputs,
                preconditions: Vec::new(),
                fp_inputs: Vec::new(),
                category: Some(TransvalCheckKind::InstructionLowering),
                machine_side_provenance: MachineSideProvenance::StaticDb,
            },
        })
    }

    pub(crate) fn obligation(&self) -> &ProofObligation {
        &self.obligation
    }
}

#[cfg(test)]
#[path = "source_bound_alu_tests.rs"]
pub(crate) mod tests;
