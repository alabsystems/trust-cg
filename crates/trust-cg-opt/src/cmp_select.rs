// trust-cg-opt - AArch64 Compare/Select Combines
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! AArch64 compare/select combine pass.
//!
//! Detects diamond CFG patterns produced by conditional value selection
//! and replaces them with AArch64's conditional select (CSEL) and
//! conditional set (CSET) instructions.
//!
//! # Patterns
//!
//! | Pattern | Transformation |
//! |---------|---------------|
//! | Diamond CFG: `CMP; B.cond; MOV Xd, Xn / MOV Xd, Xm` | `CMP; CSEL Xd, Xn, Xm, cond` |
//! | Diamond CFG: `CMP; B.cond; MOV Xd, #1 / MOV Xd, #0` | `CMP; CSET Xd, cond` |
//!
//! # Diamond CFG Shape
//!
//! ```text
//!   header:
//!     ...
//!     CMP Xn, Xm       (or CmpRI)
//!     B.cond true_block
//!   false_block:        (fallthrough successor)
//!     MOV Xd, Xm       (or MOV Xd, #0)
//!     B join
//!   true_block:
//!     MOV Xd, Xn       (or MOV Xd, #1)
//!     B join
//!   join:
//!     ...
//! ```
//!
//! # Safety Constraints
//!
//! - Both true and false blocks must have exactly 2 instructions: one MOV
//!   (MovR for CSEL, MovI #1/#0 for CSET) and one unconditional branch (B).
//! - Both blocks must have exactly 1 predecessor (the header).
//! - Both blocks must branch to the same join block by CFG successor and
//!   branch operand.
//! - Both MOVs must write to the same destination register.
//! - For CSET: one MOV must be `MovI dst, #1` and the other `MovI dst, #0`.
//! - The header block's last instruction must be a BCond.

use trust_cg_ir::{
    AArch64Opcode, BlockId, CondCode, InstId, MachFunction, MachInst, MachOperand, PassId,
    ProvenanceMap, SpecialReg,
};

use crate::pass_manager::{AnalysisCache, MachinePass};

/// AArch64 compare/select combine pass.
pub struct CmpSelectCombine;

impl MachinePass for CmpSelectCombine {
    fn name(&self) -> &str {
        "cmp-select"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_cmp_select(func, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_cmp_select(func, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        self.run_with_provenance(func, provenance)
    }
}

fn run_cmp_select(func: &mut MachFunction, mut provenance: Option<&mut ProvenanceMap>) -> bool {
    let mut changed = false;

    // We iterate over block_order looking for diamond patterns.
    // Collect transforms first, apply after (to avoid borrow issues).
    let transforms = collect_diamond_transforms(func);

    for xform in transforms {
        apply_transform(func, &xform, provenance.as_deref_mut());
        changed = true;
    }

    changed
}

/// A diamond transform to apply: replaces BCond + two MOV blocks with
/// a single CSEL or CSET instruction in the header block.
struct DiamondTransform {
    /// The header block containing the BCond.
    header: BlockId,
    /// The true block (BCond target).
    true_block: BlockId,
    /// The false block (fallthrough).
    false_block: BlockId,
    /// The join block (common successor).
    join_block: BlockId,
    /// The instruction to insert (CSEL or CSET).
    new_inst: MachInst,
    /// InstId of the true-arm MOV merged into the new select.
    true_mov_id: InstId,
    /// InstId of the false-arm MOV merged into the new select.
    false_mov_id: InstId,
    /// InstId of the true-arm branch removed with the true block.
    true_br_id: InstId,
    /// InstId of the false-arm branch removed with the false block.
    false_br_id: InstId,
    /// InstId of the BCond to replace with B .join.
    bcond_inst_id: InstId,
}

fn branch_target(inst: &MachInst) -> Option<BlockId> {
    match inst.operands.first()? {
        MachOperand::Block(block) => Some(*block),
        _ => None,
    }
}

fn is_cond_select_register_operand(operand: &MachOperand) -> bool {
    matches!(
        operand,
        MachOperand::VReg(_)
            | MachOperand::PReg(_)
            | MachOperand::Special(SpecialReg::XZR | SpecialReg::WZR)
    )
}

fn cond_select_register_operand_at(inst: &MachInst, index: usize) -> Option<MachOperand> {
    let operand = inst.operands.get(index)?.clone();
    is_cond_select_register_operand(&operand).then_some(operand)
}

/// Scan for diamond CFG patterns suitable for CSEL/CSET formation.
fn collect_diamond_transforms(func: &MachFunction) -> Vec<DiamondTransform> {
    let mut transforms = Vec::new();

    for &header_id in &func.block_order {
        let header = func.block(header_id);
        let Some(&last_inst_id) = header.insts.last() else {
            continue;
        };

        // Last instruction must be BCond.
        let last_inst = func.inst(last_inst_id);
        if last_inst.opcode != AArch64Opcode::BCond {
            continue;
        }

        // BCond operands: [Imm(cond_code), Block(target)]
        if last_inst.operands.len() < 2 {
            continue;
        }
        let cond_encoding = match last_inst.operands[0].as_imm() {
            Some(v) => v as u8,
            None => continue,
        };
        let true_block = match &last_inst.operands[1] {
            MachOperand::Block(bid) => *bid,
            _ => continue,
        };

        // Header must have exactly 2 successors.
        if header.succs.len() != 2 {
            continue;
        }

        // Determine false block: the successor that is NOT the BCond target.
        let false_block = if header.succs[0] == true_block {
            header.succs[1]
        } else if header.succs[1] == true_block {
            header.succs[0]
        } else {
            continue;
        };

        // Both arm blocks must have exactly 1 predecessor (the header).
        if func.block(true_block).preds.len() != 1 || func.block(false_block).preds.len() != 1 {
            continue;
        }

        // Both arm blocks must have exactly 2 instructions and 1 successor.
        let true_blk = func.block(true_block);
        let false_blk = func.block(false_block);
        if true_blk.insts.len() != 2 || false_blk.insts.len() != 2 {
            continue;
        }
        if true_blk.succs.len() != 1 || false_blk.succs.len() != 1 {
            continue;
        }

        // Both arms must branch to the same join block.
        let join_block = true_blk.succs[0];
        if false_blk.succs[0] != join_block {
            continue;
        }

        // First instruction in each arm must be a MOV (MovR or MovI).
        // Second instruction must be an unconditional B.
        let true_mov_id = true_blk.insts[0];
        let true_br_id = true_blk.insts[1];
        let false_mov_id = false_blk.insts[0];
        let false_br_id = false_blk.insts[1];

        let true_mov = func.inst(true_mov_id);
        let true_br = func.inst(true_br_id);
        let false_mov = func.inst(false_mov_id);
        let false_br = func.inst(false_br_id);

        if true_br.opcode != AArch64Opcode::B || false_br.opcode != AArch64Opcode::B {
            continue;
        }
        let branches_target_join = branch_target(true_br) == Some(join_block)
            && branch_target(false_br) == Some(join_block);
        if !branches_target_join {
            continue;
        }

        let is_true_mov = matches!(true_mov.opcode, AArch64Opcode::MovR | AArch64Opcode::MovI);
        let is_false_mov = matches!(false_mov.opcode, AArch64Opcode::MovR | AArch64Opcode::MovI);
        if !is_true_mov || !is_false_mov {
            continue;
        }

        // Both MOVs must write to the same destination register.
        if true_mov.operands.is_empty() || false_mov.operands.is_empty() {
            continue;
        }
        let true_dst = &true_mov.operands[0];
        let false_dst = &false_mov.operands[0];
        if true_dst != false_dst {
            continue;
        }

        // Decode the condition code.
        let cond = match decode_cond(cond_encoding) {
            Some(c) => c,
            None => continue,
        };

        // Try CSET first: true arm has MovI dst, #1 and false arm has MovI dst, #0
        // (or vice versa).
        if let Some(mut cset_inst) = try_cset(true_mov, false_mov, cond) {
            cset_inst.source_loc = true_mov.source_loc.or(false_mov.source_loc);
            transforms.push(DiamondTransform {
                header: header_id,
                true_block,
                false_block,
                join_block,
                new_inst: cset_inst,
                true_mov_id,
                false_mov_id,
                true_br_id,
                false_br_id,
                bcond_inst_id: last_inst_id,
            });
            continue;
        }

        // Try CSEL: both arms must be register moves. AArch64 CSEL cannot
        // select immediate operands directly.
        if let Some(mut csel_inst) = try_csel(true_mov, false_mov, cond) {
            csel_inst.source_loc = true_mov.source_loc.or(false_mov.source_loc);
            transforms.push(DiamondTransform {
                header: header_id,
                true_block,
                false_block,
                join_block,
                new_inst: csel_inst,
                true_mov_id,
                false_mov_id,
                true_br_id,
                false_br_id,
                bcond_inst_id: last_inst_id,
            });
        }
    }

    transforms
}

/// Try to form a CSET instruction from the diamond arms.
///
/// CSET Xd, cond: Xd = (cond) ? 1 : 0
///
/// True arm: MovI dst, #1 and false arm: MovI dst, #0 -> CSET dst, cond
/// True arm: MovI dst, #0 and false arm: MovI dst, #1 -> CSET dst, inverted_cond
fn try_cset(true_mov: &MachInst, false_mov: &MachInst, cond: CondCode) -> Option<MachInst> {
    // Both must be MovI.
    if true_mov.opcode != AArch64Opcode::MovI || false_mov.opcode != AArch64Opcode::MovI {
        return None;
    }

    let true_val = true_mov.operands.get(1)?.as_imm()?;
    let false_val = false_mov.operands.get(1)?.as_imm()?;
    let dst = cond_select_register_operand_at(true_mov, 0)?;
    if cond_select_register_operand_at(false_mov, 0)? != dst {
        return None;
    }

    if true_val == 1 && false_val == 0 {
        // CSET dst, cond
        Some(MachInst::new(
            AArch64Opcode::CSet,
            vec![dst, MachOperand::Imm(cond.encoding() as i64)],
        ))
    } else if true_val == 0 && false_val == 1 {
        // Invert: CSET dst, !cond
        let inv = cond.invert();
        Some(MachInst::new(
            AArch64Opcode::CSet,
            vec![dst, MachOperand::Imm(inv.encoding() as i64)],
        ))
    } else {
        None
    }
}

/// Try to form a CSEL instruction from the diamond arms.
///
/// CSEL Xd, Xn, Xm, cond: Xd = (cond) ? Xn : Xm
///
/// True arm: MOV dst, true_src; false arm: MOV dst, false_src
/// -> CSEL dst, true_src, false_src, cond
fn try_csel(true_mov: &MachInst, false_mov: &MachInst, cond: CondCode) -> Option<MachInst> {
    if true_mov.opcode != AArch64Opcode::MovR || false_mov.opcode != AArch64Opcode::MovR {
        return None;
    }

    let dst = cond_select_register_operand_at(true_mov, 0)?;
    if cond_select_register_operand_at(false_mov, 0)? != dst {
        return None;
    }
    let true_src = cond_select_register_operand_at(true_mov, 1)?;
    let false_src = cond_select_register_operand_at(false_mov, 1)?;

    Some(MachInst::new(
        AArch64Opcode::Csel,
        vec![
            dst,
            true_src,
            false_src,
            MachOperand::Imm(cond.encoding() as i64),
        ],
    ))
}

/// Decode a condition code encoding (0-15) to a CondCode variant.
fn decode_cond(encoding: u8) -> Option<CondCode> {
    match encoding {
        0b0000 => Some(CondCode::EQ),
        0b0001 => Some(CondCode::NE),
        0b0010 => Some(CondCode::HS),
        0b0011 => Some(CondCode::LO),
        0b0100 => Some(CondCode::MI),
        0b0101 => Some(CondCode::PL),
        0b0110 => Some(CondCode::VS),
        0b0111 => Some(CondCode::VC),
        0b1000 => Some(CondCode::HI),
        0b1001 => Some(CondCode::LS),
        0b1010 => Some(CondCode::GE),
        0b1011 => Some(CondCode::LT),
        0b1100 => Some(CondCode::GT),
        0b1101 => Some(CondCode::LE),
        0b1110 => Some(CondCode::AL),
        0b1111 => Some(CondCode::NV),
        _ => None,
    }
}

/// Apply a diamond transform: insert CSEL/CSET in the header, replace
/// BCond with B .join, remove the true/false arm blocks.
fn apply_transform(
    func: &mut MachFunction,
    xform: &DiamondTransform,
    provenance: Option<&mut ProvenanceMap>,
) {
    // 1. Insert the new CSEL/CSET instruction in the header block,
    //    just before the BCond.
    let new_inst_id = func.push_inst(xform.new_inst.clone());
    let header = func.block_mut(xform.header);
    // Find the BCond position and insert before it.
    if let Some(pos) = header
        .insts
        .iter()
        .position(|&id| id == xform.bcond_inst_id)
    {
        header.insts.insert(pos, new_inst_id);
    }

    // 2. Replace BCond with B .join.
    let bcond_source_loc = func.inst(xform.bcond_inst_id).source_loc;
    let mut b_join = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(xform.join_block)]);
    b_join.source_loc = bcond_source_loc;
    *func.inst_mut(xform.bcond_inst_id) = b_join;

    // 3. Update CFG: header's successors become just [join_block].
    let header = func.block_mut(xform.header);
    header.succs.clear();
    header.succs.push(xform.join_block);

    // 4. Remove header from the join block's preds (it will be re-added),
    //    and remove true/false blocks from join's preds.
    let join = func.block_mut(xform.join_block);
    join.preds
        .retain(|&bid| bid != xform.true_block && bid != xform.false_block);
    if !join.preds.contains(&xform.header) {
        join.preds.push(xform.header);
    }

    // 5. Remove true/false blocks from block_order.
    func.block_order
        .retain(|&bid| bid != xform.true_block && bid != xform.false_block);

    if let Some(provenance) = provenance {
        let pass = PassId::new("cmp-select");
        provenance.record_merge(
            &[xform.true_mov_id, xform.false_mov_id],
            new_inst_id,
            pass.clone(),
        );
        provenance.record_in_place_transform(xform.bcond_inst_id, pass.clone());
        provenance.record_deletion(
            xform.true_br_id,
            pass.clone(),
            "diamond arm branch removed after select formation",
        );
        provenance.record_deletion(
            xform.false_br_id,
            pass,
            "diamond arm branch removed after select formation",
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pass_manager::{AnalysisCache, MachinePass};
    use trust_cg_ir::{
        AArch64Opcode, BlockId, CondCode, MachFunction, MachInst, MachOperand, PassId,
        ProvenanceMap, ProvenanceStatus, RegClass, Signature, SourceLoc, TransformKind,
        TrustIrInstId, VReg,
    };

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn imm(val: i64) -> MachOperand {
        MachOperand::Imm(val)
    }

    /// Build a diamond CFG for testing CSEL/CSET patterns.
    ///
    /// ```text
    ///   bb0 (entry): CMP v0, v1; B.cond bb1
    ///   bb2 (false): <false_mov>; B bb3
    ///   bb1 (true):  <true_mov>; B bb3
    ///   bb3 (join):  RET
    /// ```
    ///
    /// Returns (func, bb0, bb1, bb2, bb3).
    fn make_diamond(
        cmp: MachInst,
        cond: CondCode,
        true_mov: MachInst,
        false_mov: MachInst,
    ) -> MachFunction {
        let mut func = MachFunction::new(
            "test_cmp_select".to_string(),
            Signature::new(vec![], vec![]),
        );

        let bb0 = func.entry; // BlockId(0)
        let bb1 = func.create_block(); // BlockId(1) — true block
        let bb2 = func.create_block(); // BlockId(2) — false block
        let bb3 = func.create_block(); // BlockId(3) — join block

        // bb0: CMP + BCond
        let cmp_id = func.push_inst(cmp);
        func.append_inst(bb0, cmp_id);

        let bcond = MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(cond.encoding() as i64), MachOperand::Block(bb1)],
        );
        let bcond_id = func.push_inst(bcond);
        func.append_inst(bb0, bcond_id);

        // bb1 (true): true_mov + B bb3
        let true_mov_id = func.push_inst(true_mov);
        func.append_inst(bb1, true_mov_id);
        let b_join1 = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb3)]);
        let b_join1_id = func.push_inst(b_join1);
        func.append_inst(bb1, b_join1_id);

        // bb2 (false): false_mov + B bb3
        let false_mov_id = func.push_inst(false_mov);
        func.append_inst(bb2, false_mov_id);
        let b_join2 = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb3)]);
        let b_join2_id = func.push_inst(b_join2);
        func.append_inst(bb2, b_join2_id);

        // bb3 (join): RET
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let ret_id = func.push_inst(ret);
        func.append_inst(bb3, ret_id);

        // CFG edges
        func.add_edge(bb0, bb1);
        func.add_edge(bb0, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb3);

        func
    }

    // ---- CSEL formation tests ----

    #[test]
    fn test_csel_formation_movr() {
        // Diamond: CMP v0, v1; B.EQ bb1
        // bb1 (true): MOV v2, v3; B bb3
        // bb2 (false): MOV v2, v4; B bb3
        // -> CMP v0, v1; CSEL v2, v3, v4, EQ; B bb3
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]);

        let mut func = make_diamond(cmp, CondCode::EQ, true_mov, false_mov);

        let mut pass = CmpSelectCombine;
        assert!(pass.run(&mut func));

        // Header should now have 3 instructions: CMP, CSEL, B
        let header = func.block(BlockId(0));
        assert_eq!(header.insts.len(), 3);

        // Check CSEL instruction.
        let csel = func.inst(header.insts[1]);
        assert_eq!(csel.opcode, AArch64Opcode::Csel);
        assert_eq!(csel.operands[0], vreg(2)); // dst
        assert_eq!(csel.operands[1], vreg(3)); // true_src
        assert_eq!(csel.operands[2], vreg(4)); // false_src
        assert_eq!(csel.operands[3], imm(CondCode::EQ.encoding() as i64));

        // Last instruction should be B to join (bb3).
        let last = func.inst(*header.insts.last().unwrap());
        assert_eq!(last.opcode, AArch64Opcode::B);
        assert_eq!(last.operands[0], MachOperand::Block(BlockId(3)));

        // True and false blocks should be removed from block_order.
        assert!(!func.block_order.contains(&BlockId(1)));
        assert!(!func.block_order.contains(&BlockId(2)));

        // Join block should have header as predecessor.
        let join = func.block(BlockId(3));
        assert!(join.preds.contains(&BlockId(0)));
    }

    #[test]
    fn test_movi_non_bool_values_do_not_form_invalid_csel() {
        // Diamond: CMP v0, v1; B.GE bb1
        // bb1 (true): MOV v2, #42; B bb3
        // bb2 (false): MOV v2, #99; B bb3
        // No transform: CSEL cannot encode immediate source operands.
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(2), imm(42)]);
        let false_mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(2), imm(99)]);

        let mut func = make_diamond(cmp, CondCode::GE, true_mov, false_mov);

        let mut pass = CmpSelectCombine;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block_order.len(), 4);
    }

    #[test]
    fn test_mixed_movr_movi_does_not_form_invalid_csel() {
        // Diamond: CMP v0, v1; B.GE bb1
        // bb1 (true): MOV v2, v3; B bb3
        // bb2 (false): MOV v2, #99; B bb3
        // No transform: CSEL requires both source operands to be registers.
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);
        let false_mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(2), imm(99)]);

        let mut func = make_diamond(cmp, CondCode::GE, true_mov, false_mov);

        let mut pass = CmpSelectCombine;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block_order.len(), 4);
    }

    #[test]
    fn test_movr_non_register_source_does_not_form_invalid_csel() {
        // Malformed MovR source operands must not be promoted into CSEL
        // register slots where the encoder will reject them later.
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), imm(7)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]);

        let mut func = make_diamond(cmp, CondCode::GE, true_mov, false_mov);

        let mut pass = CmpSelectCombine;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block_order.len(), 4);
    }

    // ---- CSET formation tests ----

    #[test]
    fn test_cset_formation() {
        // Diamond: CMP v0, v1; B.EQ bb1
        // bb1 (true): MOV v2, #1; B bb3
        // bb2 (false): MOV v2, #0; B bb3
        // -> CMP v0, v1; CSET v2, EQ; B bb3
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(2), imm(1)]);
        let false_mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(2), imm(0)]);

        let mut func = make_diamond(cmp, CondCode::EQ, true_mov, false_mov);

        let mut pass = CmpSelectCombine;
        assert!(pass.run(&mut func));

        let header = func.block(BlockId(0));
        assert_eq!(header.insts.len(), 3);

        let cset = func.inst(header.insts[1]);
        assert_eq!(cset.opcode, AArch64Opcode::CSet);
        assert_eq!(cset.operands[0], vreg(2)); // dst
        assert_eq!(cset.operands[1], imm(CondCode::EQ.encoding() as i64));
    }

    #[test]
    fn test_cset_inverted() {
        // Diamond: CMP v0, v1; B.NE bb1
        // bb1 (true): MOV v2, #0; B bb3  (true arm has 0!)
        // bb2 (false): MOV v2, #1; B bb3
        // -> CSET v2, EQ (inverted: B.NE true_arm has 0, so condition flips)
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(2), imm(0)]);
        let false_mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(2), imm(1)]);

        let mut func = make_diamond(cmp, CondCode::NE, true_mov, false_mov);

        let mut pass = CmpSelectCombine;
        assert!(pass.run(&mut func));

        let header = func.block(BlockId(0));
        let cset = func.inst(header.insts[1]);
        assert_eq!(cset.opcode, AArch64Opcode::CSet);
        // B.NE true_arm=0, false_arm=1 -> CSET with inverted NE = EQ
        assert_eq!(cset.operands[1], imm(CondCode::EQ.encoding() as i64));
    }

    #[test]
    fn test_cset_with_cmpri() {
        // CmpRI v0, #42; B.LT bb1
        // bb1 (true): MOV v1, #1; B bb3
        // bb2 (false): MOV v1, #0; B bb3
        // -> CmpRI v0, #42; CSET v1, LT; B bb3
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(0), imm(42)]);
        let true_mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(1)]);
        let false_mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(0)]);

        let mut func = make_diamond(cmp, CondCode::LT, true_mov, false_mov);

        let mut pass = CmpSelectCombine;
        assert!(pass.run(&mut func));

        let header = func.block(BlockId(0));
        let cset = func.inst(header.insts[1]);
        assert_eq!(cset.opcode, AArch64Opcode::CSet);
        assert_eq!(cset.operands[0], vreg(1));
        assert_eq!(cset.operands[1], imm(CondCode::LT.encoding() as i64));
    }

    #[test]
    fn test_cset_non_register_destination_does_not_convert() {
        // Boolean MovI arms with matching but non-register destinations must
        // not become an invalid CSET destination operand.
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovI, vec![imm(2), imm(1)]);
        let false_mov = MachInst::new(AArch64Opcode::MovI, vec![imm(2), imm(0)]);

        let mut func = make_diamond(cmp, CondCode::EQ, true_mov, false_mov);

        let mut pass = CmpSelectCombine;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block_order.len(), 4);
    }

    #[test]
    fn test_source_loc_preserved_across_csel_and_branch_replacement() {
        let select_loc = SourceLoc {
            file: 7,
            line: 41,
            col: 9,
        };
        let branch_loc = SourceLoc {
            file: 7,
            line: 40,
            col: 5,
        };
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov =
            MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]).with_source_loc(select_loc);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]);

        let mut func = make_diamond(cmp, CondCode::EQ, true_mov, false_mov);
        let bcond_id = *func.block(BlockId(0)).insts.last().unwrap();
        func.inst_mut(bcond_id).source_loc = Some(branch_loc);

        let mut pass = CmpSelectCombine;
        assert!(pass.run(&mut func));

        let header = func.block(BlockId(0));
        let csel = func.inst(header.insts[1]);
        assert_eq!(csel.opcode, AArch64Opcode::Csel);
        assert_eq!(
            csel.source_loc,
            Some(select_loc),
            "cmp-select must preserve source_loc from the selected MOV on CSEL"
        );

        let branch = func.inst(header.insts[2]);
        assert_eq!(branch.opcode, AArch64Opcode::B);
        assert_eq!(
            branch.source_loc,
            Some(branch_loc),
            "cmp-select must preserve source_loc when replacing BCond with B"
        );
    }

    #[test]
    fn test_source_loc_cset_falls_back_to_false_mov() {
        let false_loc = SourceLoc {
            file: 3,
            line: 88,
            col: 17,
        };
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(2), imm(1)]);
        let false_mov =
            MachInst::new(AArch64Opcode::MovI, vec![vreg(2), imm(0)]).with_source_loc(false_loc);

        let mut func = make_diamond(cmp, CondCode::EQ, true_mov, false_mov);

        let mut pass = CmpSelectCombine;
        assert!(pass.run(&mut func));

        let header = func.block(BlockId(0));
        let cset = func.inst(header.insts[1]);
        assert_eq!(cset.opcode, AArch64Opcode::CSet);
        assert_eq!(
            cset.source_loc,
            Some(false_loc),
            "cmp-select must preserve source_loc from the false MOV when the true MOV has none"
        );
    }

    // ---- Provenance preservation ----

    fn assert_optimized_away_by_cmp_select(provenance: &ProvenanceMap, inst_id: InstId) {
        let entry = provenance
            .get_entry(inst_id)
            .expect("removed branch should retain optimized-away provenance");
        match &entry.status {
            ProvenanceStatus::OptimizedAway {
                pass,
                justification,
            } => {
                assert_eq!(pass.name(), "cmp-select");
                assert_eq!(
                    justification,
                    "diamond arm branch removed after select formation"
                );
            }
            other => panic!("expected optimized-away branch provenance, got {other:?}"),
        }
    }

    #[test]
    fn test_cmp_select_provenance_merges_arm_movs_and_marks_removed_branches() {
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]);

        let mut func = make_diamond(cmp, CondCode::EQ, true_mov, false_mov);
        let cmp_id = func.block(BlockId(0)).insts[0];
        let bcond_id = func.block(BlockId(0)).insts[1];
        let true_mov_id = func.block(BlockId(1)).insts[0];
        let true_br_id = func.block(BlockId(1)).insts[1];
        let false_mov_id = func.block(BlockId(2)).insts[0];
        let false_br_id = func.block(BlockId(2)).insts[1];
        let ret_id = func.block(BlockId(3)).insts[0];

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(70), &[cmp_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(71), &[bcond_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(72), &[true_mov_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(73), &[false_mov_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(74), &[true_br_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(75), &[false_br_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(76), &[ret_id], PassId::new("isel"));

        let mut pass = CmpSelectCombine;
        let mut analyses = AnalysisCache::new();
        assert!(pass.run_with_analyses_and_provenance(&mut func, &mut analyses, &mut provenance));

        let header = func.block(BlockId(0));
        assert_eq!(header.insts.len(), 3);
        let csel_id = header.insts[1];
        assert_eq!(header.insts[2], bcond_id);

        let csel = func.inst(csel_id);
        assert_eq!(csel.opcode, AArch64Opcode::Csel);
        assert_eq!(csel.operands[0], vreg(2));
        assert_eq!(csel.operands[1], vreg(3));
        assert_eq!(csel.operands[2], vreg(4));

        let csel_entry = provenance.get_entry(csel_id).unwrap();
        assert!(csel_entry.trust_ir_origins.contains(&TrustIrInstId(72)));
        assert!(csel_entry.trust_ir_origins.contains(&TrustIrInstId(73)));
        let transform = csel_entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("cmp-select"));
        assert_eq!(
            transform.kind,
            TransformKind::Merged {
                sources: vec![true_mov_id, false_mov_id],
            }
        );
        assert!(csel_entry.is_active());
        assert!(provenance.get_entry(true_mov_id).is_none());
        assert!(provenance.get_entry(false_mov_id).is_none());
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(72)),
            Some(&[csel_id][..])
        );
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(73)),
            Some(&[csel_id][..])
        );

        let branch = func.inst(bcond_id);
        assert_eq!(branch.opcode, AArch64Opcode::B);
        let branch_entry = provenance.get_entry(bcond_id).unwrap();
        assert_eq!(branch_entry.trust_ir_origins, vec![TrustIrInstId(71)]);
        let transform = branch_entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("cmp-select"));
        assert_eq!(transform.kind, TransformKind::Survived);
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(71)),
            Some(&[bcond_id][..])
        );

        assert_optimized_away_by_cmp_select(&provenance, true_br_id);
        assert_optimized_away_by_cmp_select(&provenance, false_br_id);
        assert!(!func.block_order.contains(&BlockId(1)));
        assert!(!func.block_order.contains(&BlockId(2)));
    }

    #[test]
    fn test_cmp_select_direct_provenance_hook_merges_cset_arm_movs() {
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(2), imm(1)]);
        let false_mov = MachInst::new(AArch64Opcode::MovI, vec![vreg(2), imm(0)]);

        let mut func = make_diamond(cmp, CondCode::EQ, true_mov, false_mov);
        let true_mov_id = func.block(BlockId(1)).insts[0];
        let false_mov_id = func.block(BlockId(2)).insts[0];

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(80), &[true_mov_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(81), &[false_mov_id], PassId::new("isel"));

        let mut pass = CmpSelectCombine;
        assert!(pass.run_with_provenance(&mut func, &mut provenance));

        let header = func.block(BlockId(0));
        let cset_id = header.insts[1];
        let cset = func.inst(cset_id);
        assert_eq!(cset.opcode, AArch64Opcode::CSet);
        assert_eq!(cset.operands[0], vreg(2));
        assert_eq!(cset.operands[1], imm(CondCode::EQ.encoding() as i64));

        let cset_entry = provenance.get_entry(cset_id).unwrap();
        assert!(cset_entry.trust_ir_origins.contains(&TrustIrInstId(80)));
        assert!(cset_entry.trust_ir_origins.contains(&TrustIrInstId(81)));
        let transform = cset_entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("cmp-select"));
        assert_eq!(
            transform.kind,
            TransformKind::Merged {
                sources: vec![true_mov_id, false_mov_id],
            }
        );
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(80)),
            Some(&[cset_id][..])
        );
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(81)),
            Some(&[cset_id][..])
        );
    }

    // ---- Negative tests: no transformation ----

    #[test]
    fn test_no_combine_different_destinations() {
        // MOVs write to different VRegs -> no combine.
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(5), vreg(4)]);

        let mut func = make_diamond(cmp, CondCode::EQ, true_mov, false_mov);

        let mut pass = CmpSelectCombine;
        assert!(!pass.run(&mut func));

        // All 4 blocks should still exist.
        assert_eq!(func.block_order.len(), 4);
    }

    #[test]
    fn test_no_combine_non_mov_in_arm() {
        // True arm has an ADD, not a MOV -> no combine.
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(3), vreg(4)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(5)]);

        let mut func = make_diamond(cmp, CondCode::EQ, true_add, false_mov);

        let mut pass = CmpSelectCombine;
        assert!(!pass.run(&mut func));
    }

    #[test]
    fn test_no_combine_arm_too_many_insts() {
        // True arm has 3 instructions (extra computation) -> no combine.
        let mut func = MachFunction::new(
            "test_no_combine".to_string(),
            Signature::new(vec![], vec![]),
        );

        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        // bb0: CMP + BCond
        let cmp_id = func.push_inst(MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]));
        func.append_inst(bb0, cmp_id);
        let bcond_id = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(CondCode::EQ.encoding() as i64), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, bcond_id);

        // bb1 (true): ADD + MOV + B (3 instructions)
        let add_id = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(5), vreg(3), vreg(4)],
        ));
        func.append_inst(bb1, add_id);
        let mov_id = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(5)]));
        func.append_inst(bb1, mov_id);
        let b1_id = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, b1_id);

        // bb2 (false): MOV + B
        let fmov_id = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(6)]));
        func.append_inst(bb2, fmov_id);
        let b2_id = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb2, b2_id);

        // bb3: RET
        let ret_id = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb3, ret_id);

        func.add_edge(bb0, bb1);
        func.add_edge(bb0, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb3);

        let mut pass = CmpSelectCombine;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block_order.len(), 4);
    }

    #[test]
    fn test_no_combine_arms_different_join() {
        // Arms branch to different blocks -> no combine.
        let mut func =
            MachFunction::new("test_diff_join".to_string(), Signature::new(vec![], vec![]));

        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        let bb4 = func.create_block();

        let cmp_id = func.push_inst(MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]));
        func.append_inst(bb0, cmp_id);
        let bcond_id = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(CondCode::EQ.encoding() as i64), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, bcond_id);

        // bb1 -> bb3
        let m1 = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]));
        func.append_inst(bb1, m1);
        let b1 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, b1);

        // bb2 -> bb4 (different join!)
        let m2 = func.push_inst(MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]));
        func.append_inst(bb2, m2);
        let b2 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb4)],
        ));
        func.append_inst(bb2, b2);

        let r3 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb3, r3);
        let r4 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb4, r4);

        func.add_edge(bb0, bb1);
        func.add_edge(bb0, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb4);

        let mut pass = CmpSelectCombine;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block_order.len(), 5);
    }

    #[test]
    fn test_no_combine_when_branch_operand_misses_cfg_join() {
        // CFG metadata still forms a diamond, but the false arm branch operand
        // targets a different block. The pass must trust both representations.
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]);

        let mut func = make_diamond(cmp, CondCode::EQ, true_mov, false_mov);
        let wrong_target = func.create_block();
        let false_br_id = func.block(BlockId(2)).insts[1];
        func.inst_mut(false_br_id).operands[0] = MachOperand::Block(wrong_target);

        let mut pass = CmpSelectCombine;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block_order.len(), 5);
        assert_eq!(
            func.inst(false_br_id).operands[0],
            MachOperand::Block(wrong_target)
        );
    }

    // ---- Idempotency ----

    #[test]
    fn test_idempotent() {
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let true_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]);
        let false_mov = MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]);

        let mut func = make_diamond(cmp, CondCode::EQ, true_mov, false_mov);

        let mut pass = CmpSelectCombine;
        assert!(pass.run(&mut func)); // First: transforms
        assert!(!pass.run(&mut func)); // Second: no change
    }

    // ---- Edge: empty function ----

    #[test]
    fn test_no_change_empty() {
        let mut func = MachFunction::new("empty".to_string(), Signature::new(vec![], vec![]));
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let ret_id = func.push_inst(ret);
        func.append_inst(func.entry, ret_id);

        let mut pass = CmpSelectCombine;
        assert!(!pass.run(&mut func));
    }
}
