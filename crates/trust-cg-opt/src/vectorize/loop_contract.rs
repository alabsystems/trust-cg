// trust-cg-opt - Admission contract for the vectorizer's CFG-rewriting loop idioms
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Shared admission checks for the two loop idioms whose rewrite inserts a
//! vector main loop in front of the scalar loop and keeps the scalar loop as
//! the tail: the i32 induction store (`a[i] = i + 1`, counting up) and the
//! reverse accumulation (`dst[i] += src[i]`, counting down).
//!
//! Such a rewrite is a refinement only when the matched loop is exactly the
//! idiom. The vector loop runs *before* the scalar header, replaces a prefix
//! of the scalar iterations, and reproduces nothing but the carried induction
//! state and the idiom's memory effects. Matching every instruction against
//! an allowed set is therefore not enough; the matcher must also discharge:
//!
//! * **Shape** ([`idiom_loop_shape`]). The loop is `{header, body, latch}`,
//!   or `{header, body}` when the body is its own latch, with no other edge:
//!   the header is entered from one preheader and one latch and exits to a
//!   block outside the loop; exactly one preheader instruction names the
//!   header (the branch the rewrite retargets); and nothing reaches the header
//!   by layout fall-through, because the vector blocks are laid out directly
//!   in front of it.
//! * **Order** ([`reaching_def_in_block`]). Each datapath operand reads the
//!   definition the matcher assigned to it — the nearest preceding write in
//!   its block — or, where the matcher expects a value from outside the
//!   block, no write in the block precedes the read.
//! * **Constants** ([`dominating_unique_constant`]). A constant the idiom
//!   relies on (the element stride, a unit step, the zero it counts down to)
//!   has exactly one definition in the emitted layout, and that definition
//!   dominates the use. The shared def map is last-wins, so without this a
//!   second definition on another path is silently ignored.
//! * **Invariance** ([`defined_in_loop`]). Every register the vector loop
//!   reads, other than the carried induction variable, has no definition in
//!   the loop, so the value it holds when the preheader branches is the value
//!   every replaced scalar iteration reads. A copy made inside the loop is
//!   resolved to its source, which must satisfy the same condition.
//! * **Escape** (the crate's one loop-state contract,
//!   [`crate::loop_contract::LoopLocality`]). No register the loop writes other
//!   than a register-held induction variable is live into the header or into
//!   an exit. The vector loop never computes those values, so a scalar tail
//!   that runs zero iterations would otherwise expose stale ones. This module
//!   used to state the rule itself, with header values exempt at the exit;
//!   the shared statement checks every exit without that exemption (fail
//!   closed), so the rule has one statement for every pre-loop rewrite.
//! * **Private slot** ([`private_i32_stack_slot`]). A stack-slot-backed
//!   induction variable lives in a slot whose address never escapes: every
//!   reference to the slot is an address computation used only as the base
//!   of zero-offset 32-bit loads and stores. Otherwise an in-bounds store of
//!   the idiom could legally write the index, which the vector loop keeps in
//!   a register.
//!
//! The checks are sufficient conditions and fail closed: a loop they cannot
//! discharge stays scalar.

use crate::fast_hash::FxHashSet as HashSet;

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachOperand, RegClass, StackSlotId, VReg,
};

use super::block_target_operand;
use crate::dom::DomTree;
use crate::effects::{for_each_inst_def, for_each_inst_use, live_def_count};
use crate::loops::NaturalLoop;

/// The CFG of a loop an idiom rewrite may transform.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct IdiomLoopShape {
    pub(super) preheader: BlockId,
    pub(super) header: BlockId,
    pub(super) body: BlockId,
    pub(super) latch: BlockId,
    pub(super) exit: BlockId,
    /// The only preheader instruction that names the header.
    pub(super) branch_to_header: InstId,
}

impl IdiomLoopShape {
    /// The loop's blocks, without repeating a body that is its own latch.
    pub(super) fn blocks(&self) -> Vec<BlockId> {
        let mut blocks = vec![self.header, self.body];
        if self.latch != self.body {
            blocks.push(self.latch);
        }
        blocks
    }
}

/// `actual` names exactly the blocks in `expected`, each once.
fn exact_block_set(actual: &[BlockId], expected: &[BlockId]) -> bool {
    let actual_set: HashSet<BlockId> = actual.iter().copied().collect();
    let expected_set: HashSet<BlockId> = expected.iter().copied().collect();
    actual_set.len() == actual.len() && actual_set == expected_set
}

fn layout_position(func: &MachFunction, block: BlockId) -> Option<usize> {
    func.block_order
        .iter()
        .position(|&candidate| candidate == block)
}

/// Whether control can leave the end of `block` into its layout successor.
fn falls_off_end(func: &MachFunction, block: BlockId) -> bool {
    match func.block(block).insts.last() {
        Some(&last) => {
            let inst = func.inst(last);
            !(inst.opcode.is_unconditional_branch()
                || inst.opcode == AArch64Opcode::Ret
                || inst.is_return())
        }
        None => true,
    }
}

/// Whether the block laid out before `block` can fall through into it. A
/// block missing from the layout is treated as reachable that way.
fn is_fall_through_target(func: &MachFunction, block: BlockId) -> bool {
    let Some(position) = layout_position(func, block) else {
        return true;
    };
    position
        .checked_sub(1)
        .is_some_and(|previous| falls_off_end(func, func.block_order[previous]))
}

/// Match the exact loop CFG both idiom rewrites assume; see the module docs.
///
/// `body` and `exit` are the targets the matched header branches to.
pub(super) fn idiom_loop_shape(
    func: &MachFunction,
    lp: &NaturalLoop,
    body: BlockId,
    exit: BlockId,
) -> Option<IdiomLoopShape> {
    let (header, latch) = (lp.header, lp.latch);
    let loop_blocks: HashSet<BlockId> = [header, body, latch].into_iter().collect();
    if header == body || header == latch || lp.body != loop_blocks {
        return None;
    }
    let preheader = lp.preheader?;
    if loop_blocks.contains(&preheader) || loop_blocks.contains(&exit) {
        return None;
    }
    let block = |id: BlockId| func.block(id);
    if !exact_block_set(&block(header).preds, &[preheader, latch])
        || !exact_block_set(&block(header).succs, &[body, exit])
        || !exact_block_set(&block(body).preds, &[header])
        || !exact_block_set(&block(latch).succs, &[header])
    {
        return None;
    }
    if body != latch
        && (!exact_block_set(&block(body).succs, &[latch])
            || !exact_block_set(&block(latch).preds, &[body]))
    {
        return None;
    }
    let mut naming = block(preheader)
        .insts
        .iter()
        .copied()
        .filter(|&inst_id| block_target_operand(func.inst(inst_id), header));
    let branch_to_header = naming.next()?;
    if naming.next().is_some()
        || !matches!(
            func.inst(branch_to_header).opcode,
            AArch64Opcode::B | AArch64Opcode::BCond
        )
        || is_fall_through_target(func, header)
    {
        return None;
    }
    Some(IdiomLoopShape {
        preheader,
        header,
        body,
        latch,
        exit,
        branch_to_header,
    })
}

/// Whether the non-`Nop` instructions of `block` are exactly `allowed`, each
/// once and in any order, followed by one `B target` that ends the block.
///
/// Membership alone is not enough: a branch placed before the datapath would
/// leave the idiom's instructions unexecuted, and an instruction that merely
/// resembles an allowed one would be admitted twice.
pub(super) fn block_is_exactly(
    func: &MachFunction,
    block: BlockId,
    allowed: &[InstId],
    target: BlockId,
) -> bool {
    let Some((&last, rest)) = func.block(block).insts.split_last() else {
        return false;
    };
    let terminator = func.inst(last);
    if terminator.opcode != AArch64Opcode::B || terminator.operands != [MachOperand::Block(target)]
    {
        return false;
    }
    let body: Vec<InstId> = rest
        .iter()
        .copied()
        .filter(|&inst_id| func.inst(inst_id).opcode != AArch64Opcode::Nop)
        .collect();
    let distinct: HashSet<InstId> = body.iter().copied().collect();
    let expected: HashSet<InstId> = allowed.iter().copied().collect();
    distinct.len() == body.len() && distinct == expected
}

/// The block and position of `inst_id` in the emitted layout.
pub(super) fn layout_inst_position(
    func: &MachFunction,
    inst_id: InstId,
) -> Option<(BlockId, usize)> {
    func.block_order.iter().find_map(|&block| {
        func.block(block)
            .insts
            .iter()
            .position(|&candidate| candidate == inst_id)
            .map(|position| (block, position))
    })
}

fn writes_vreg_id(func: &MachFunction, inst_id: InstId, id: u32) -> bool {
    let mut hit = false;
    for_each_inst_def(func.inst(inst_id), |defined| hit |= defined.id == id);
    hit
}

/// The last instruction before position `before` of `block` that writes a
/// register with `vreg`'s id, of any class.
pub(super) fn reaching_def_in_block(
    func: &MachFunction,
    block: BlockId,
    before: usize,
    vreg: VReg,
) -> Option<InstId> {
    func.block(block).insts[..before.min(func.block(block).insts.len())]
        .iter()
        .rev()
        .copied()
        .find(|&inst_id| writes_vreg_id(func, inst_id, vreg.id))
}

/// Whether the read of `vreg` by `use_inst` sees exactly `expected`: the
/// write `Some(def)` made earlier in the same block, or — for `None` — a value
/// that enters the block, because no earlier instruction in it writes the
/// register.
pub(super) fn reads_def(
    func: &MachFunction,
    use_inst: InstId,
    vreg: VReg,
    expected: Option<InstId>,
) -> bool {
    let Some((block, position)) = layout_inst_position(func, use_inst) else {
        return false;
    };
    reaching_def_in_block(func, block, position, vreg) == expected
}

/// Whether `inst` can transfer control away from the rest of its block: a
/// branch, a return, a terminator, or a call (which may unwind).
fn may_leave_block(func: &MachFunction, inst_id: InstId) -> bool {
    let inst = func.inst(inst_id);
    inst.opcode.is_unconditional_branch()
        || inst.opcode.is_conditional_branch()
        || inst.is_branch()
        || inst.is_return()
        || inst.is_terminator()
        || inst.is_call()
        || inst
            .operands
            .iter()
            .any(|operand| matches!(operand, MachOperand::Block(_)))
}

/// Whether `def` dominates `use_inst` at instruction granularity.
///
/// Across blocks, `def`'s block must strictly dominate the use's block and
/// `def` must precede every instruction of its block that can leave it, so
/// every path out of that block toward the use has executed `def`.
fn inst_dominates(func: &MachFunction, dom: &DomTree, def: InstId, use_inst: InstId) -> bool {
    let (Some((def_block, def_pos)), Some((use_block, use_pos))) = (
        layout_inst_position(func, def),
        layout_inst_position(func, use_inst),
    ) else {
        return false;
    };
    if def_block == use_block {
        return def_pos < use_pos;
    }
    dom.strictly_dominates(def_block, use_block)
        && !func.block(def_block).insts[..def_pos]
            .iter()
            .any(|&inst_id| may_leave_block(func, inst_id))
}

/// The only instruction in the emitted layout that writes a register with
/// `vreg`'s id, when it dominates `use_inst` — so it is the definition that
/// reaches the use on every path.
pub(super) fn dominating_unique_def(
    func: &MachFunction,
    dom: &DomTree,
    vreg: VReg,
    use_inst: InstId,
) -> Option<InstId> {
    if live_def_count(func, vreg.id) != 1 {
        return None;
    }
    let def = func.block_order.iter().find_map(|&block| {
        func.block(block)
            .insts
            .iter()
            .copied()
            .find(|&inst_id| writes_vreg_id(func, inst_id, vreg.id))
    })?;
    inst_dominates(func, dom, def, use_inst).then_some(def)
}

/// The value `vreg` holds at `use_inst` when its only definition in the
/// emitted layout is a canonical `Movz`/`Movn` that dominates the use.
pub(super) fn dominating_unique_constant(
    func: &MachFunction,
    dom: &DomTree,
    vreg: VReg,
    use_inst: InstId,
) -> Option<u64> {
    let def = dominating_unique_def(func, dom, vreg, use_inst)?;
    let (defined, value) = crate::reaching_const::movz_value(func.inst(def))
        .or_else(|| crate::reaching_const::movn_value(func.inst(def)))?;
    (defined == vreg).then_some(value)
}

/// Whether any instruction in the loop writes a register with `vreg`'s id.
pub(super) fn defined_in_loop(func: &MachFunction, shape: &IdiomLoopShape, vreg: VReg) -> bool {
    shape.blocks().into_iter().any(|block| {
        func.block(block)
            .insts
            .iter()
            .any(|&inst_id| writes_vreg_id(func, inst_id, vreg.id))
    })
}

/// The loop instructions that write a register with `vreg`'s id.
pub(super) fn loop_defs_of(func: &MachFunction, shape: &IdiomLoopShape, vreg: VReg) -> Vec<InstId> {
    shape
        .blocks()
        .into_iter()
        .flat_map(|block| func.block(block).insts.iter().copied())
        .filter(|&inst_id| writes_vreg_id(func, inst_id, vreg.id))
        .collect()
}

/// The stack slot whose address `address` holds, when `address` has exactly
/// one definition and it is `AddPCRel address, _, StackSlot(slot)`.
fn unique_stack_slot_address(func: &MachFunction, address: VReg) -> Option<StackSlotId> {
    if address.class != RegClass::Gpr64 || live_def_count(func, address.id) != 1 {
        return None;
    }
    func.block_order.iter().find_map(|&block| {
        func.block(block).insts.iter().find_map(|&inst_id| {
            let inst = func.inst(inst_id);
            match inst.operands.as_slice() {
                [MachOperand::VReg(defined), _, MachOperand::StackSlot(slot)]
                    if inst.opcode == AArch64Opcode::AddPCRel && *defined == address =>
                {
                    Some(*slot)
                }
                _ => None,
            }
        })
    })
}

/// Whether `address` is the only address of a stack slot that nothing but
/// zero-offset 32-bit `LdrRI`/`StrRI` transfers ever touches.
///
/// Every reference to the slot in the emitted layout must be an `AddPCRel`
/// defining a Gpr64 register, and every read of such a register must be the
/// base operand of a `LdrRI`/`StrRI` with a Gpr32 data register and a zero
/// offset. Storing the address, copying it, offsetting it or passing it
/// anywhere else lets another pointer legally reach the slot.
pub(super) fn private_i32_stack_slot(func: &MachFunction, address: VReg) -> bool {
    let Some(slot) = unique_stack_slot_address(func, address) else {
        return false;
    };
    let layout_insts = || {
        func.block_order
            .iter()
            .flat_map(|&block| func.block(block).insts.iter().copied())
    };
    let slot_operand = MachOperand::StackSlot(slot);
    let mut slot_addresses = HashSet::default();
    for inst_id in layout_insts() {
        let inst = func.inst(inst_id);
        if !inst.operands.contains(&slot_operand) {
            continue;
        }
        match inst.operands.as_slice() {
            [MachOperand::VReg(defined), base, referenced]
                if inst.opcode == AArch64Opcode::AddPCRel
                    && defined.class == RegClass::Gpr64
                    && *base != slot_operand
                    && *referenced == slot_operand =>
            {
                slot_addresses.insert(defined.id);
            }
            _ => return false,
        }
    }
    layout_insts().all(|inst_id| {
        let inst = func.inst(inst_id);
        let mut reads_address = false;
        for_each_inst_use(inst, |used| reads_address |= slot_addresses.contains(&used.id));
        if !reads_address {
            return true;
        }
        let zero_offset = match inst.operands.get(2) {
            None => true,
            Some(offset) => *offset == MachOperand::Imm(0),
        };
        matches!(inst.opcode, AArch64Opcode::LdrRI | AArch64Opcode::StrRI)
            && (2..=3).contains(&inst.operands.len())
            && zero_offset
            && matches!(
                inst.operands[0],
                MachOperand::VReg(data)
                    if data.class == RegClass::Gpr32 && !slot_addresses.contains(&data.id)
            )
            && matches!(inst.operands[1], MachOperand::VReg(base) if slot_addresses.contains(&base.id))
    })
}
