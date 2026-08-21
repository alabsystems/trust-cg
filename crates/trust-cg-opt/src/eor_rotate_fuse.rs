// trust-cg-opt - EOR-with-rotate fusion peephole
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! EOR-with-rotate fusion — the sibling/consumer of [`crate::rotate_idiom`].
//!
//! Collapses the frontend ARX idiom `x ^= ROTL(v, r)` (salsa20's double-round:
//! `x[b] ^= ROTL(x[c]+x[d], r)`) into a single AArch64 shifted-register
//! instruction. After [`crate::rotate_idiom`] has already turned
//! `(v << r) | (v >> (w - r))` into `RorRI(v, k)` (with `k = w - r`), a typical
//! statement is the three-instruction chain
//!
//! ```text
//!   t = RorRI(s, k)          ; ROR s, #k
//!   d = EorRR(x, t)          ; EOR x, t        (either operand order — EOR commutes)
//! ```
//!
//! which this pass rewrites to the two-instruction form
//!
//! ```text
//!   d = EorRRShift(x, s, k)  ; EOR d, x, s, ROR #k
//! ```
//!
//! (the `RorRI` is deleted, `Nop`ped in place). This removes one instruction AND
//! one serial node from the per-statement critical path (the inner ARX chains are
//! serial `add -> ror -> eor`) — the unfinished half of the 8c9e922 rotate arc.
//!
//! FAIL-CLOSED. The rewrite fires ONLY when:
//!   * the `EorRR` and the `RorRI` are in the SAME block (`RorRI` before the
//!     `EorRR`), so no cross-block/dominance reasoning is needed;
//!   * the `RorRI` result `t` is SINGLE-USE across the whole function (its only
//!     read is this `EorRR`), so folding it and deleting the `RorRI` is safe;
//!   * the matched `RorRI` is the REACHING definition of `t` at the `EorRR` —
//!     producer entries are invalidated when any later instruction redefines
//!     the vreg (a stale entry would fuse against a dead rotate);
//!   * the rotate SOURCE `s` is not redefined between the `RorRI` and the
//!     `EorRR` — the fusion moves the read of `s` DOWN to the `EorRR` site;
//!   * the rotate amount `k` is a real in-register rotate, `k` in `[1, width)`;
//!   * the operand register classes match (all W or all X).
//!
//! The single-use oracle is [`crate::effects::aarch64_for_each_use_position`],
//! which also counts TIED def-use reads (`Movk`/`Bfm` operand 0). A plain
//! "skip operand 0 of a `produces_value` opcode" scan would miss those and
//! overstate single-use in exactly the direction that authorizes deleting a
//! still-live producer.
//!
//! The emitted `EorRRShift` is the VERIFIED opcode
//! (`lowering_proof::all_eor_ror_shift_proofs`, gate-covered W+X); its encoder is
//! byte-verified against clang. Runs AFTER `rotate_idiom` (which creates the
//! `RorRI`) in the pipeline.

use std::collections::HashMap;

use trust_cg_ir::{
    AArch64Opcode, InstId, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap, VReg,
    regs::RegClass,
};

use crate::pass_manager::MachinePass;

/// EOR-with-rotate fusion pass.
pub struct EorRotateFuse;

impl MachinePass for EorRotateFuse {
    fn name(&self) -> &str {
        "eor-rotate-fuse"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_eor_rotate_fuse(func, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_eor_rotate_fuse(func, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut crate::pass_manager::AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_eor_rotate_fuse(func, Some(provenance))
    }
}

fn eor_rotate_fuse_pass_id() -> PassId {
    PassId::new("eor-rotate-fuse")
}

/// A same-block producer definition: the defining instruction plus its
/// position in the block walk (for reaching-def / source-redefinition guards).
#[derive(Clone, Copy)]
struct ProducerDef {
    inst: InstId,
    pos: usize,
}

fn run_eor_rotate_fuse(
    func: &mut MachFunction,
    mut provenance: Option<&mut ProvenanceMap>,
) -> bool {
    // Function-wide READ counts: a VReg's single-use status must hold across the
    // WHOLE function, not just the current block (a later block could read `t`).
    let read_counts = count_vreg_reads(func);

    let mut changed = false;
    for block_id in func.block_order.clone() {
        // RorRI defs seen so far IN THIS BLOCK (VReg -> producer). Only
        // same-block defs are eligible (the def precedes the use in program
        // order because we populate this as we walk), and entries are
        // INVALIDATED when any later instruction redefines the vreg, so a map
        // hit is the true reaching definition at the consumer.
        let mut ror_defs: HashMap<VReg, ProducerDef> = HashMap::new();
        // Most recent in-block def position of EVERY vreg (any opcode). Guards
        // the folded SOURCE operand: moving its read down to the consumer is
        // only sound if no intervening instruction redefined it.
        let mut last_def_pos: HashMap<VReg, usize> = HashMap::new();

        for (pos, inst_id) in func.block(block_id).insts.clone().into_iter().enumerate() {
            let opcode = func.inst(inst_id).opcode;
            match opcode {
                AArch64Opcode::EorRR => {
                    let result = try_fuse_eor(
                        func.inst(inst_id),
                        func,
                        &ror_defs,
                        &read_counts,
                        &last_def_pos,
                    );
                    if let Some((ror_id, fused)) = result {
                        // Rewrite the EOR in place, preserving proof/source_loc.
                        let orig = func.inst(inst_id);
                        let mut new_inst = fused;
                        new_inst.proof = orig.proof;
                        if new_inst.source_loc.is_none() {
                            new_inst.source_loc = orig.source_loc;
                        }
                        *func.inst_mut(inst_id) = new_inst;
                        // Delete the now-dead RorRI (single-use, consumed).
                        *func.inst_mut(ror_id) = MachInst::new(AArch64Opcode::Nop, vec![]);
                        if let Some(provenance) = provenance.as_deref_mut() {
                            provenance
                                .record_in_place_transform(inst_id, eor_rotate_fuse_pass_id());
                            provenance.record_in_place_transform(ror_id, eor_rotate_fuse_pass_id());
                        }
                        // The rewritten EOR no longer defines/uses via the RorRI;
                        // its dst def-map entry (if any) is unchanged.
                        changed = true;
                    }
                }
                _ => {}
            }

            // Record this instruction's defs (AFTER matching — an instruction
            // is never its own producer). Any def invalidates a stale producer
            // entry for that vreg; an eligible RorRI then (re)registers.
            let mut defs: Vec<VReg> = Vec::new();
            {
                let inst = func.inst(inst_id);
                crate::effects::aarch64_for_each_def_position(
                    inst.opcode,
                    inst.operands.len(),
                    |def_pos| {
                        if let Some(MachOperand::VReg(v)) = inst.operands.get(def_pos) {
                            defs.push(*v);
                        }
                    },
                );
            }
            for v in defs {
                ror_defs.remove(&v);
                last_def_pos.insert(v, pos);
            }
            if func.inst(inst_id).opcode == AArch64Opcode::RorRI {
                if let Some(MachOperand::VReg(dst)) = func.inst(inst_id).operands.first() {
                    ror_defs.insert(*dst, ProducerDef { inst: inst_id, pos });
                }
            }
        }
    }

    changed
}

/// Count, for every VReg, how many times it appears as a READ operand across the
/// whole function, using the shared operand-role oracle (which also counts TIED
/// def-use reads such as `Movk`/`Bfm` operand 0 — a plain "skip operand 0" scan
/// would miss those and overstate single-use). This is the single-use oracle:
/// `read_counts[t] == 1` means the only reader of `t` is the candidate `EorRR`,
/// so folding it and deleting its `RorRI` def is safe.
fn count_vreg_reads(func: &MachFunction) -> HashMap<VReg, u32> {
    let mut counts: HashMap<VReg, u32> = HashMap::new();
    for &block_id in &func.block_order {
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            crate::effects::aarch64_for_each_use_position(
                inst.opcode,
                inst.operands.len(),
                |pos| {
                    if let Some(MachOperand::VReg(vreg)) = inst.operands.get(pos) {
                        *counts.entry(*vreg).or_insert(0) += 1;
                    }
                },
            );
        }
    }
    counts
}

/// Try to fuse `eor` (an `EorRR`) with a single-use, same-block `RorRI` feeding
/// one of its two source operands. On success returns `(ror_inst_id,
/// EorRRShift MachInst)`. EOR commutes, so BOTH operand orders are tried.
fn try_fuse_eor(
    eor: &MachInst,
    func: &MachFunction,
    ror_defs: &HashMap<VReg, ProducerDef>,
    read_counts: &HashMap<VReg, u32>,
    last_def_pos: &HashMap<VReg, usize>,
) -> Option<(InstId, MachInst)> {
    if eor.operands.len() != 3 {
        return None;
    }
    let dst = eor.operands.first()?.as_vreg()?;
    // Operand 1 rotated (Rn = operand 2), or operand 2 rotated (Rn = operand 1).
    try_fuse_with_rotated(
        dst,
        &eor.operands[2],
        &eor.operands[1],
        func,
        ror_defs,
        read_counts,
        last_def_pos,
    )
    .or_else(|| {
        try_fuse_with_rotated(
            dst,
            &eor.operands[1],
            &eor.operands[2],
            func,
            ror_defs,
            read_counts,
            last_def_pos,
        )
    })
}

/// `rotated_op` is the candidate `RorRI` result (the operand to fold into the
/// shift); `plain_op` is the other EOR operand (becomes ARM `Rn`). Builds
/// `EorRRShift [dst, plain(Rn), s(Rm), Imm(k)]` when all fail-closed conditions
/// hold.
fn try_fuse_with_rotated(
    dst: VReg,
    rotated_op: &MachOperand,
    plain_op: &MachOperand,
    func: &MachFunction,
    ror_defs: &HashMap<VReg, ProducerDef>,
    read_counts: &HashMap<VReg, u32>,
    last_def_pos: &HashMap<VReg, usize>,
) -> Option<(InstId, MachInst)> {
    let t = rotated_op.as_vreg()?;
    // t must be SINGLE-USE (only this EOR reads it) so deleting its RorRI is safe.
    if read_counts.get(&t).copied().unwrap_or(0) != 1 {
        return None;
    }
    let ror_def = *ror_defs.get(&t)?;
    let ror_id = ror_def.inst;
    let ror = func.inst(ror_id);
    if ror.opcode != AArch64Opcode::RorRI || ror.operands.len() != 3 {
        return None;
    }
    let s = ror.operands[1].as_vreg()?; // rotated SOURCE
    let k = ror.operands[2].as_imm()?; // rotate amount

    // s must not be redefined between the RorRI and the EOR: the fusion moves
    // the read of s DOWN to the EOR site. A def AT the RorRI position is the
    // RorRI itself writing s (t == s) — also unsafe, also declined.
    if last_def_pos.get(&s).is_some_and(|&p| p >= ror_def.pos) {
        return None;
    }

    // Width match: dst, plain (Rn), s (Rm), t must all be the same GPR width, and
    // the rotate amount must be a real in-register rotate in [1, width).
    let width = gpr_width(dst.class)?;
    let plain = plain_op.as_vreg()?;
    if gpr_width(plain.class)? != width
        || gpr_width(s.class)? != width
        || gpr_width(t.class)? != width
    {
        return None;
    }
    if k < 1 || k >= i64::from(width) {
        return None;
    }

    // EorRRShift [Rd, Rn (un-shifted = plain), Rm (rotated source = s), Imm(k)].
    Some((
        ror_id,
        MachInst::new(
            AArch64Opcode::EorRRShift,
            vec![
                MachOperand::VReg(dst),
                MachOperand::VReg(plain),
                MachOperand::VReg(s),
                MachOperand::Imm(k),
            ],
        ),
    ))
}

/// The bit width of a GPR register class (32 for W, 64 for X); `None` for any
/// non-GPR class (fail-closed — the fusion only applies to integer EOR/ROR).
fn gpr_width(class: RegClass) -> Option<u32> {
    match class {
        RegClass::Gpr32 => Some(32),
        RegClass::Gpr64 => Some(64),
        _ => None,
    }
}

#[cfg(test)]
mod tests;
