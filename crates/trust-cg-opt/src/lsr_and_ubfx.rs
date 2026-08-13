//! Fuse `LSR #k` followed by a low-mask `AND` into `UBFX`/`UBFM`.
//!
//! ```text
//! t = LsrRI(src, k)
//! d = AndRI(t, (1 << field_width) - 1)
//! ```
//!
//! becomes
//!
//! ```text
//! d = Ubfm(src, immr=k, imms=k+field_width-1)
//! ```
//!
//! The registered W/X UBFM encoding theorem is symbolic in `k` and
//! `field_width`. Its source side is exactly the pre-rewrite
//! `(src >>u k) & ((1 << field_width) - 1)` expression, while its machine side
//! independently decodes the UBFM immediates. The AY extension/truncation suite
//! discharges both carrier widths. A fixed representative theorem is not enough
//! authority for this pass and is deliberately not used.
//!
//! The rewrite fails closed unless the producer is the same-block reaching
//! definition, its result has exactly one function-wide read, all registers
//! have the same W/X width, the source is not redefined before the consumer,
//! the mask is a non-empty contiguous low run of ones, and the complete field
//! lies within the register. Operand roles come from the shared AArch64
//! use/definition oracle, including tied def-use instructions such as `MOVK`.

use std::collections::HashMap;

use trust_cg_ir::{
    AArch64Opcode, InstId, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap, VReg,
    regs::RegClass,
};

use crate::pass_manager::MachinePass;

/// `LSR #k` + `AND #low_mask` -> `UBFM` (the `UBFX` alias) fusion.
pub struct LsrAndUbfx;

impl MachinePass for LsrAndUbfx {
    fn name(&self) -> &str {
        "lsr-and-ubfx"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_lsr_and_ubfx(func, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_lsr_and_ubfx(func, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut crate::pass_manager::AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_lsr_and_ubfx(func, Some(provenance))
    }
}

fn pass_id() -> PassId {
    PassId::new("lsr-and-ubfx")
}

#[derive(Clone, Copy)]
struct ProducerDef {
    inst: InstId,
    pos: usize,
}

fn run_lsr_and_ubfx(func: &mut MachFunction, mut provenance: Option<&mut ProvenanceMap>) -> bool {
    let read_counts = count_vreg_reads(func);
    let mut changed = false;

    for block_id in func.block_order.clone() {
        let mut lsr_defs: HashMap<VReg, ProducerDef> = HashMap::new();
        let mut last_def_pos: HashMap<VReg, usize> = HashMap::new();

        for (pos, inst_id) in func.block(block_id).insts.clone().into_iter().enumerate() {
            if let Some((lsr_id, mut ubfm)) = try_fuse(
                func.inst(inst_id),
                func,
                &lsr_defs,
                &last_def_pos,
                &read_counts,
            ) {
                let original = func.inst(inst_id).clone();
                ubfm.proof = original.proof;
                ubfm.source_loc = original.source_loc;
                *func.inst_mut(inst_id) = ubfm;
                *func.inst_mut(lsr_id) = MachInst::new(AArch64Opcode::Nop, vec![]);
                if let Some(provenance) = provenance.as_deref_mut() {
                    provenance.record_merge(&[lsr_id, inst_id], inst_id, pass_id());
                }
                changed = true;
            }

            // Update reaching definitions after matching. This uses the shared
            // operand-role table rather than assuming operand zero is the only
            // definition.
            let mut defs = Vec::new();
            {
                let inst = func.inst(inst_id);
                crate::effects::aarch64_for_each_def_position(
                    inst.opcode,
                    inst.operands.len(),
                    |def_pos| {
                        if let Some(MachOperand::VReg(vreg)) = inst.operands.get(def_pos) {
                            defs.push(*vreg);
                        }
                    },
                );
            }
            for vreg in defs {
                lsr_defs.remove(&vreg);
                last_def_pos.insert(vreg, pos);
            }

            if func.inst(inst_id).opcode == AArch64Opcode::LsrRI
                && let Some(MachOperand::VReg(dst)) = func.inst(inst_id).operands.first()
            {
                lsr_defs.insert(*dst, ProducerDef { inst: inst_id, pos });
            }
        }
    }

    changed
}

fn try_fuse(
    and: &MachInst,
    func: &MachFunction,
    lsr_defs: &HashMap<VReg, ProducerDef>,
    last_def_pos: &HashMap<VReg, usize>,
    read_counts: &HashMap<VReg, u32>,
) -> Option<(InstId, MachInst)> {
    if and.opcode != AArch64Opcode::AndRI || and.operands.len() != 3 {
        return None;
    }
    let dst = and.operands.first()?.as_vreg()?;
    let temp = and.operands.get(1)?.as_vreg()?;
    let mask = and.operands.get(2)?.as_imm()?;

    // Deleting the LSR is valid only when this AND is its sole reader. The
    // shared read oracle counts tied reads (for example MOVK operand zero).
    if read_counts.get(&temp).copied().unwrap_or(0) != 1 {
        return None;
    }

    let producer = *lsr_defs.get(&temp)?;
    let lsr = func.inst(producer.inst);
    if lsr.opcode != AArch64Opcode::LsrRI || lsr.operands.len() != 3 {
        return None;
    }
    let source = lsr.operands.get(1)?.as_vreg()?;
    let shift = lsr.operands.get(2)?.as_imm()?;

    let reg_width = gpr_width(dst.class)?;
    if gpr_width(temp.class)? != reg_width || gpr_width(source.class)? != reg_width {
        return None;
    }

    // Folding moves the source read from the producer to the consumer.
    if last_def_pos
        .get(&source)
        .is_some_and(|&def_pos| def_pos > producer.pos)
    {
        return None;
    }

    let field_width = low_run_width(mask, reg_width)?;
    let lsb = u32::try_from(shift).ok()?;
    if lsb >= reg_width || lsb.checked_add(field_width)? > reg_width {
        return None;
    }

    Some((
        producer.inst,
        MachInst::new(
            AArch64Opcode::Ubfm,
            vec![
                MachOperand::VReg(dst),
                MachOperand::VReg(source),
                MachOperand::Imm(i64::from(lsb)),
                MachOperand::Imm(i64::from(lsb + field_width - 1)),
            ],
        ),
    ))
}

/// Width of a non-empty contiguous low run of ones in the selected W/X view.
fn low_run_width(mask: i64, reg_width: u32) -> Option<u32> {
    let value = match reg_width {
        32 => (mask as u64) & u64::from(u32::MAX),
        64 => mask as u64,
        _ => return None,
    };
    if value == 0 || value & value.wrapping_add(1) != 0 {
        return None;
    }
    Some(value.count_ones())
}

fn gpr_width(class: RegClass) -> Option<u32> {
    match class {
        RegClass::Gpr32 => Some(32),
        RegClass::Gpr64 => Some(64),
        _ => None,
    }
}

fn count_vreg_reads(func: &MachFunction) -> HashMap<VReg, u32> {
    let mut counts = HashMap::new();
    for &block_id in &func.block_order {
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            crate::effects::aarch64_for_each_use_position(
                inst.opcode,
                inst.operands.len(),
                |use_pos| {
                    if let Some(MachOperand::VReg(vreg)) = inst.operands.get(use_pos) {
                        *counts.entry(*vreg).or_insert(0) += 1;
                    }
                },
            );
        }
    }
    counts
}

#[cfg(test)]
mod tests;
