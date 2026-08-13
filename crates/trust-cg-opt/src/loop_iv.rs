//! Shared loop induction-variable / trip-count analysis (X2 slice 1).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
//!
//! THE SHARED HOME for loop IV facts. Slice 1 is pure code motion: the
//! trip-count recognizer `analyze_trip_count` and its four helpers moved
//! verbatim from `loop_unroll.rs` (which now imports them), so every future
//! consumer (X3's LICM port, X9's mid-end ports, closed-form) has one
//! import point instead of growing private copies — the exact triplication
//! the mach_view migration just removed for CFG analyses. Slice 2 lifts the
//! recognizer onto `MachIrView` + per-arch semantic hooks so the x86 lane
//! gets trip counts too (task #6 metadata holds the design constraints).
//!
//! The recognized shape (unchanged): preheader `v_init = MovI #start`;
//! header `CmpRI v_iv, #limit` + `BCond`; latch `v_iv = AddRI v_prev,
//! #step`; trip = ceil((limit - start) / step).

use trust_cg_ir::{AArch64Opcode, BlockId, MachFunction, MachOperand, VReg};

use crate::loops::NaturalLoop;

/// Attempt to determine the constant trip count of a loop.
///
/// Recognizes this pattern:
/// - Preheader: `v_init = MovI #start`
/// - Header: `CmpRI v_iv, #limit` followed by `BCond exit, body`
/// - Latch: `v_iv = AddRI v_iv_prev, #step`
///
/// Trip count = ceil((limit - start) / step) for simple counting loops.
///
/// Returns `None` if the trip count cannot be statically determined.
pub fn analyze_trip_count(func: &MachFunction, lp: &NaturalLoop) -> Option<u64> {
    let preheader = lp.preheader?;

    // Look for a compare instruction in the header.
    let header_block = func.block(lp.header);
    let (cmp_vreg, limit) = find_header_cmp(func, header_block)?;

    // Look for a conditional branch in the header that uses the compare result.
    let header_terminates_with_bcond = header_block
        .insts
        .last()
        .map(|&id| func.inst(id).opcode == AArch64Opcode::BCond)
        .unwrap_or(false);

    if !header_terminates_with_bcond {
        return None;
    }

    // Find the induction variable initialization in the preheader.
    let init_val = find_iv_init(func, preheader, cmp_vreg, lp)?;

    // Find the back-edge vreg from the Phi that defines the IV.
    let backedge_vreg = find_phi_backedge_vreg(func, lp, cmp_vreg)?;

    // Find the IV update in the latch: AddRI v_backedge, v_prev, #step.
    let step = find_iv_step(func, lp, backedge_vreg, cmp_vreg)?;

    if step == 0 {
        return None; // infinite loop
    }

    // Compute trip count for a counting-up loop: ceil((limit - init) / step).
    if limit > init_val && step > 0 {
        let range = (limit - init_val) as u64;
        let step_u = step as u64;
        let trips = range.div_ceil(step_u);
        Some(trips)
    } else if limit < init_val && step < 0 {
        // Counting-down loop.
        let range = (init_val - limit) as u64;
        let step_u = (-step) as u64;
        let trips = range.div_ceil(step_u);
        Some(trips)
    } else if init_val == limit {
        Some(0) // zero trips
    } else {
        None // can't determine
    }
}

/// Find a CmpRI instruction in the header and extract the compared vreg and limit.
pub fn find_header_cmp(
    func: &MachFunction,
    header: &trust_cg_ir::MachBlock,
) -> Option<(VReg, i64)> {
    for &inst_id in &header.insts {
        let inst = func.inst(inst_id);
        if inst.opcode == AArch64Opcode::CmpRI {
            // CmpRI operands: [vreg, imm]
            if inst.operands.len() >= 2
                && let (Some(vreg), Some(imm)) =
                    (inst.operands[0].as_vreg(), inst.operands[1].as_imm())
            {
                return Some((vreg, imm));
            }
        }
    }
    None
}

/// Find the initialization value of the induction variable in the preheader.
///
/// Looks for `MovI v_target, #val` where v_target is the same vreg
/// compared in the header, or a vreg that flows into it via Phi/copy chain.
pub fn find_iv_init(
    func: &MachFunction,
    preheader: BlockId,
    cmp_vreg: VReg,
    lp: &NaturalLoop,
) -> Option<i64> {
    // Check for a Phi in the header that defines the compared vreg.
    // The Phi's preheader operand gives us the init value's source vreg.
    let header_block = func.block(lp.header);
    let mut init_vreg = cmp_vreg;

    for &inst_id in &header_block.insts {
        let inst = func.inst(inst_id);
        if inst.opcode == AArch64Opcode::Phi
            && let Some(def) = inst.operands.first().and_then(|op| op.as_vreg())
            && def == cmp_vreg
        {
            // Phi operands: [def, val_from_pred0, block0, val_from_pred1, block1, ...]
            // Find the operand pair where block == preheader.
            let mut i = 1;
            while i + 1 < inst.operands.len() {
                if let MachOperand::Block(bid) = &inst.operands[i + 1]
                    && *bid == preheader
                {
                    if let Some(v) = inst.operands[i].as_vreg() {
                        init_vreg = v;
                    }
                    break;
                }
                i += 2;
            }
            break;
        }
    }

    // Now find the MovI that defines init_vreg in the preheader.
    let ph_block = func.block(preheader);
    for &inst_id in &ph_block.insts {
        let inst = func.inst(inst_id);
        if inst.opcode == AArch64Opcode::MovI
            && let Some(def) = inst.operands.first().and_then(|op| op.as_vreg())
            && def == init_vreg
            && let Some(val) = inst.operands.get(1).and_then(|op| op.as_imm())
        {
            return Some(val);
        }
    }

    None
}

/// Find the back-edge vreg from the Phi that defines the IV.
///
/// In the header's Phi for the compared vreg, find the incoming value
/// from inside the loop (the latch). This is the vreg that the IV
/// update instruction must define.
pub fn find_phi_backedge_vreg(
    func: &MachFunction,
    lp: &NaturalLoop,
    cmp_vreg: VReg,
) -> Option<VReg> {
    let header_block = func.block(lp.header);
    for &inst_id in &header_block.insts {
        let inst = func.inst(inst_id);
        if inst.opcode != AArch64Opcode::Phi {
            continue;
        }
        if let Some(def) = inst.operands.first().and_then(|op| op.as_vreg()) {
            if def != cmp_vreg {
                continue;
            }
            // Phi operands: [def, val0, block0, val1, block1, ...]
            let mut i = 1;
            while i + 1 < inst.operands.len() {
                if let MachOperand::Block(bid) = &inst.operands[i + 1]
                    && lp.body.contains(bid)
                    && let Some(v) = inst.operands[i].as_vreg()
                {
                    return Some(v);
                }
                i += 2;
            }
        }
    }
    None
}

/// Find the step value of the induction variable in the latch.
///
/// Specifically looks for `AddRI v_backedge, v_iv, #step` or
/// `SubRI v_backedge, v_iv, #step` where `v_backedge` is the vreg
/// fed back through the Phi and `v_iv` is the IV Phi vreg.
pub fn find_iv_step(
    func: &MachFunction,
    lp: &NaturalLoop,
    backedge_vreg: VReg,
    iv_vreg: VReg,
) -> Option<i64> {
    let latch_block = func.block(lp.latch);
    for &inst_id in &latch_block.insts {
        let inst = func.inst(inst_id);
        match inst.opcode {
            AArch64Opcode::AddRI => {
                if inst.operands.len() >= 3
                    && let (Some(dst), Some(src), Some(step)) = (
                        inst.operands[0].as_vreg(),
                        inst.operands[1].as_vreg(),
                        inst.operands[2].as_imm(),
                    )
                    && dst == backedge_vreg
                    && src == iv_vreg
                {
                    return Some(step);
                }
            }
            AArch64Opcode::SubRI => {
                if inst.operands.len() >= 3
                    && let (Some(dst), Some(src), Some(step)) = (
                        inst.operands[0].as_vreg(),
                        inst.operands[1].as_vreg(),
                        inst.operands[2].as_imm(),
                    )
                    && dst == backedge_vreg
                    && src == iv_vreg
                {
                    return Some(-step);
                }
            }
            _ => {}
        }
    }
    None
}
