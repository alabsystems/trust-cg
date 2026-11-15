// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! A2 of OD-35: an actual LIR Iconst against one move-wide materialization.
//! The Rust source/body check and a replayed frame remain prerequisites. The
//! residual compares the source's value and width with this instance's imm16,
//! halfword and W/X width. Even a dead materialization has refutable content.
//! MOVK sequences require a sequence owner and receive no credit here.

use std::collections::{HashMap, HashSet};

use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr as E;
use crate::source_bound_frame::SourceBoundFrame;
use trust_cg_ir::provenance::{LoweringProvenance, SourceInstDigest, SourceInstId};
use trust_cg_ir::{AArch64Opcode as M, InstId, MachOperand as O};
use trust_cg_lower::Type;
use trust_cg_lower::instructions::{Block, Opcode};

pub(crate) struct SourceBoundConstant<'owner, 'inputs> {
    _frame: &'owner SourceBoundFrame<'inputs>,
    obligation: ProofObligation,
}

#[cfg(test)]
#[path = "source_bound_constant_tests.rs"]
mod tests;

/// One immutable frame's move-wide provenance index, built once per walk.
/// Multiple words of one source constant cannot be credited separately.
pub(crate) struct SourceBoundConstants<'owner, 'inputs> {
    frame: &'owner SourceBoundFrame<'inputs>,
    counts: HashMap<SourceInstId, usize>,
    live: HashSet<InstId>,
}

impl<'owner, 'inputs> SourceBoundConstants<'owner, 'inputs> {
    pub(crate) fn new(frame: &'owner SourceBoundFrame<'inputs>) -> Self {
        let live: HashSet<_> = frame
            .machine()
            .blocks
            .iter()
            .flat_map(|block| block.insts.iter().copied())
            .collect();
        let mut counts = HashMap::new();
        for id in frame.machine().blocks.iter().flat_map(|block| &block.insts) {
            let inst = &frame.machine().insts[id.0 as usize];
            if matches!(inst.opcode, M::Movz | M::Movn | M::Movk)
                && let LoweringProvenance::SourceInst { id, .. } =
                    frame.machine().inst_lowering_provenance(*id)
            {
                *counts.entry(id).or_default() += 1;
            }
        }
        Self {
            frame,
            counts,
            live,
        }
    }

    pub(crate) fn bind(&self, id: InstId) -> Option<SourceBoundConstant<'owner, 'inputs>> {
        let frame = self.frame;
        if frame.envelope_instructions().contains(&id) || !self.live.contains(&id) {
            return None;
        }
        let inst = frame.machine().insts.get(id.0 as usize)?;
        if !matches!(inst.opcode, M::Movz | M::Movn) {
            return None;
        }
        let LoweringProvenance::SourceInst {
            id: source_id,
            digest,
            ..
        } = frame.machine().inst_lowering_provenance(id)
        else {
            return None;
        };
        // A multiword expansion's first word is not the complete Iconst.
        // Its MOVK writes need a sequence theorem, so decline the entire
        // shared-stamp expansion instead of calling its first word wrong code.
        if self.counts.get(&source_id) != Some(&1) {
            return None;
        }
        let source = frame
            .source()
            .blocks
            .get(&Block(source_id.block))?
            .instructions
            .get(source_id.index as usize)?;
        if digest
            != SourceInstDigest::compute_debug(
                &source.opcode,
                source.args.len(),
                source.results.len(),
            )
            || !source.args.is_empty()
            || source.results.len() != 1
        {
            return None;
        }
        let Opcode::Iconst { ty, imm: value } = &source.opcode else {
            return None;
        };
        let bits = match ty {
            Type::I32 => 32,
            Type::I64 => 64,
            _ => return None,
        };
        let (dst, immediate, shift) = match inst.operands.as_slice() {
            [O::PReg(dst), O::Imm(imm)] => (dst, *imm, 0),
            [O::PReg(dst), O::Imm(imm), O::Imm(shift)] => (dst, *imm, *shift),
            _ => return None,
        };
        if !(0..=65535).contains(&immediate)
            || !(0..i64::from(bits)).contains(&shift)
            || shift % 16 != 0
            || !matches!((bits, dst.encoding()), (64, 0..=17) | (32, 32..=49))
        {
            return None;
        }
        // An I32 source value is modulo 2^32 even when held in an i64 as
        // the positive 4294967295. Do not infer its width from the sign.
        let source_value = if bits == 32 {
            *value as u32 as u64
        } else {
            *value as u64
        };
        let shifted = E::bv_const(immediate as u64, bits).bvshl(E::bv_const(shift as u64, bits));
        let machine = if inst.opcode == M::Movn {
            shifted.bvxor(E::bv_const(
                if bits == 32 {
                    u32::MAX as u64
                } else {
                    u64::MAX
                },
                bits,
            ))
        } else {
            shifted
        };
        Some(SourceBoundConstant {
            _frame: frame,
            obligation: ProofObligation {
                name: format!(
                    "Source-bound AArch64 constant (Rust body binding): {:?} i{bits} {source_id}",
                    inst.opcode
                ),
                trust_ir_expr: E::bv_const(source_value, bits),
                aarch64_expr: machine,
                inputs: Vec::new(),
                preconditions: Vec::new(),
                fp_inputs: Vec::new(),
                category: Some(TransvalCheckKind::InstructionLowering),
                machine_side_provenance: MachineSideProvenance::StaticDb,
            },
        })
    }
}

impl<'owner, 'inputs> SourceBoundConstant<'owner, 'inputs> {
    #[cfg(test)]
    pub(crate) fn bind(frame: &'owner SourceBoundFrame<'inputs>, id: InstId) -> Option<Self> {
        SourceBoundConstants::new(frame).bind(id)
    }

    pub(crate) fn obligation(&self) -> &ProofObligation {
        &self.obligation
    }
}
