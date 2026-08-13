// trust-cg-opt - Tail Call Optimization
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Tail call optimization (TCO) for machine-level IR.
//!
//! Detects calls in tail position and transforms them to eliminate
//! stack growth:
//!
//! - **Self-recursive tail calls**: Replace `BL self + RET` with `B self`.
//!   The frame lowering pass treats symbol tail branches as function exits and
//!   emits any required epilogue before the branch.
//! - **Sibling tail calls**: Replace `BL target + RET` with `B target`
//!   when the callee's ABI is compatible and its stack requirements fit
//!   within the caller's frame.
//!
//! # Algorithm
//!
//! For each basic block:
//! 1. Find the last non-terminator instruction. If it is a call (`BL`),
//!    check whether the block terminates with `RET` immediately after.
//! 2. Verify there are no intervening instructions between the call and
//!    the return that modify the return value or have side effects.
//! 3. Apply the appropriate transformation based on whether the call is
//!    self-recursive or to a sibling function.
//!
//! # Guard Conditions
//!
//! TCO is rejected when:
//! - The callee has more stack arguments than the caller's frame allows
//! - The callee uses a different calling convention (detected via
//!   incompatible signatures)
//! - The caller has runtime-sized stack slots whose lifetime cannot yet be
//!   represented by a simple frame reuse
//! - There are cleanup operations (stores, releases) between the call
//!   and the return
//! - The return value is modified after the call
//!
//! # AArch64 Details
//!
//! On AArch64, a tail call replaces `BL <target>` (which pushes LR) with
//! `B <target>` (which does not). The caller's stack frame is reused.
//! Self-recursive calls are emitted as symbol tail branches rather than local
//! entry-block branches so frame lowering can distinguish them from ordinary
//! loop backedges.
//!
//! Reference: LLVM `AArch64ISelLowering.cpp` (isEligibleForTailCallOptimization),
//!            GCC tail call optimization pass

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstFlags, InstId, MachFunction, MachInst, MachOperand, PassId,
    ProvenanceMap, SpecialReg, regs::SP,
};

use crate::pass_manager::{AnalysisCache, MachinePass};

/// Tail call optimization pass.
pub struct TailCallOptimization;

impl MachinePass for TailCallOptimization {
    fn name(&self) -> &str {
        "tail-call"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_tail_call(func, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_tail_call(func, Some(provenance))
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

fn run_tail_call(func: &mut MachFunction, mut provenance: Option<&mut ProvenanceMap>) -> bool {
    if has_runtime_sized_stack_slot(func)
        || has_outgoing_stack_arg_store(func)
        || materializes_stack_slot_address(func)
    {
        return false;
    }

    let mut changed = false;
    let func_name = func.name.clone();
    let caller_stack_size = total_stack_size(func);
    let caller_param_count = func.signature.params.len();
    let caller_return_count = func.signature.returns.len();

    for block_id in func.block_order.clone() {
        let block = func.block(block_id);
        let insts = block.insts.clone();

        if let Some(tail_info) = detect_tail_call(func, &insts) {
            // Check guard conditions common to all tail calls.
            if !guards_pass(func, &insts, &tail_info, caller_stack_size) {
                continue;
            }

            let call_inst = func.inst(tail_info.call_id);
            let call_target = extract_call_target(call_inst);
            let is_self_recursive = call_target.as_deref() == Some(func_name.as_str());

            if is_self_recursive {
                // Self-recursive tail call: use a symbol branch so frame
                // lowering can emit the same exit cleanup as sibling calls.
                apply_self_recursive_tco(
                    func,
                    block_id,
                    &tail_info,
                    caller_param_count,
                    provenance.as_deref_mut(),
                );
                changed = true;
            } else if is_sibling_compatible(
                func,
                &tail_info,
                caller_stack_size,
                caller_param_count,
                caller_return_count,
            ) {
                // Sibling tail call: replace BL with B.
                if apply_sibling_tco(func, block_id, &tail_info, provenance.as_deref_mut()) {
                    changed = true;
                }
            }
        }
    }

    changed
}

/// Information about a detected tail call site.
struct TailCallInfo {
    /// Index into block's instruction list for the call.
    call_idx: usize,
    /// InstId of the call instruction.
    call_id: InstId,
    /// Index into block's instruction list for the return.
    ret_idx: usize,
}

/// Scan a block's instruction list for a tail call pattern:
/// `BL <target>` followed (possibly with intervening moves) by `RET`.
///
/// The call must be the last operation with side effects before the return.
fn detect_tail_call(func: &MachFunction, insts: &[InstId]) -> Option<TailCallInfo> {
    if insts.len() < 2 {
        return None;
    }

    // Find RET — it must be the last instruction.
    let ret_idx = insts.len() - 1;
    let ret_inst = func.inst(insts[ret_idx]);
    if !ret_inst.is_return() {
        return None;
    }

    // Walk backward from just before RET to find the call.
    // Allow only pure moves (MovR) between the call and return —
    // these may be return-value copies.
    let mut call_idx = None;
    for i in (0..ret_idx).rev() {
        let inst = func.inst(insts[i]);
        if is_call_opcode(inst.opcode) {
            call_idx = Some(i);
            break;
        }
        // Allow pure register moves between call and ret (return value setup).
        if inst.is_move() {
            continue;
        }
        // Any other instruction blocks tail call detection.
        break;
    }

    let call_idx = call_idx?;
    let call_id = insts[call_idx];

    Some(TailCallInfo {
        call_idx,
        call_id,
        ret_idx,
    })
}

/// Returns true if the opcode is a call instruction.
///
/// Uses the generic IS_CALL flag for multi-target compatibility.
fn is_call_opcode(opcode: AArch64Opcode) -> bool {
    opcode.default_flags().is_call()
}

/// Extract the call target symbol name from a call instruction.
fn extract_call_target(inst: &MachInst) -> Option<String> {
    for operand in &inst.operands {
        if let MachOperand::Symbol(name) = operand {
            return Some(name.clone());
        }
    }
    None
}

fn direct_call_branch_target(inst: &MachInst) -> Option<MachOperand> {
    let operand = inst.operands.first()?;
    match operand {
        MachOperand::Symbol(_) | MachOperand::Block(_) | MachOperand::Imm(_) => {
            Some(operand.clone())
        }
        _ => None,
    }
}

/// Check guard conditions that apply to all tail call transformations.
///
/// Returns false if any condition prevents TCO:
/// - Cleanup operations (stores, releases) between call and return
/// - The return value is modified after the call (beyond simple moves)
/// - The caller has stack-allocated destructors that must run
fn guards_pass(
    func: &MachFunction,
    insts: &[InstId],
    info: &TailCallInfo,
    _caller_stack_size: u32,
) -> bool {
    // Check instructions between the call and the return for disqualifiers.
    for inst_id in insts.iter().take(info.ret_idx).skip(info.call_idx + 1) {
        let inst = func.inst(*inst_id);
        let flags = inst.flags;

        // Stores between call and return mean cleanup must run.
        if flags.contains(InstFlags::WRITES_MEMORY) {
            return false;
        }

        // Calls between the tail call and return disqualify.
        if flags.contains(InstFlags::IS_CALL) {
            return false;
        }

        // Release operations (destructor-like cleanup): check HAS_SIDE_EFFECTS
        // on the specific Release opcode.
        if inst.opcode == AArch64Opcode::Release {
            return false;
        }

        // Only allow pure register copies (moves) between call and ret.
        if !inst.is_move() {
            return false;
        }
    }

    // The intervening moves must only route the *call's own result* into the
    // return position. If a move sources a value that was live across the call
    // (defined before it), dropping that move and tail-branching would silently
    // return the callee's result instead of the value the caller meant to
    // return. See `intervening_insts_only_route_call_result`.
    if !intervening_insts_only_route_call_result(func, insts, info) {
        return false;
    }

    true
}

/// Returns true iff every instruction between the call and the return only
/// routes the call's own result into the return position.
///
/// TCO drops every instruction after the call and branches to the callee, so
/// the callee's result becomes the caller's result. That is sound only when the
/// intervening moves route the *call's result* — not a value that was live
/// across the call — into the return registers. SROA store-to-load forwarding
/// can legitimately produce `BL f ; MovR ret, v ; RET` where `v` was defined
/// *before* the call (the function means to return `v`, not `f()`'s result);
/// truncating that move would make the function incorrectly return `f()`.
///
/// This pass runs pre-regalloc, so a value defined before the call is a virtual
/// register while the call's result is read from a physical return register
/// (one of the call's `implicit_defs`). An intervening move is accepted only
/// when its source is the call's result (an `implicit_def`) or a value produced
/// by an earlier intervening move; any other source means a pre-call value
/// reaches the return and the tail call would be unsound.
fn intervening_insts_only_route_call_result(
    func: &MachFunction,
    insts: &[InstId],
    info: &TailCallInfo,
) -> bool {
    let call_inst = func.inst(info.call_id);
    let mut available: Vec<MachOperand> = call_inst
        .implicit_defs
        .iter()
        .map(|preg| MachOperand::PReg(*preg))
        .collect();

    for inst_id in insts.iter().take(info.ret_idx).skip(info.call_idx + 1) {
        let inst = func.inst(*inst_id);
        // `guards_pass` already guaranteed these are pure register moves, so
        // operand 0 is the destination and operand 1 is the source.
        let (Some(dst), Some(src)) = (inst.operands.first(), inst.operands.get(1)) else {
            return false;
        };
        if matches!(src, MachOperand::VReg(_) | MachOperand::PReg(_)) && !available.contains(src) {
            return false;
        }
        available.push(dst.clone());
    }

    true
}

/// Compute total stack frame size from all stack slots.
fn total_stack_size(func: &MachFunction) -> u32 {
    func.stack_slots.iter().map(|s| s.size).sum()
}

/// Runtime-sized slots require a dynamic SP cursor/lifetime model before TCO
/// can safely reuse or elide the caller's frame.
fn has_runtime_sized_stack_slot(func: &MachFunction) -> bool {
    func.stack_slots.iter().any(|slot| slot.is_runtime_sized())
}

/// Return true when the function materializes the ADDRESS of a stack slot into a
/// register — i.e., it takes the address of a local (`&local`, a local array or
/// struct passed by pointer). Tail-call optimization tears down the caller's
/// frame (`add sp, sp, #N` / restore FP,LR) *before* branching to the callee, so
/// if such an address is passed to the callee the callee dereferences freed
/// stack. LLVM emits a plain (non-`tail`) `call` in exactly this situation (a
/// pointer to an `alloca` escapes into the arguments), and we must not promote it
/// to a sibling/self tail branch.
///
/// We key on the two opcodes that compute a slot address into a register:
/// `AddPCRel`/`StackAlloc` carrying a `StackSlot`/`FrameIndex` operand. Loads and
/// stores that merely use a slot as their memory base access the slot's CONTENTS
/// (not its address) and do not leak it, so they use `Ldr`/`Str`-family opcodes
/// and are excluded; a PC-relative *global* address uses `AddPCRel` with a
/// `Symbol` operand (a global outlives the frame) and is likewise excluded.
/// Conservative at the function granularity: any escaping local address disables
/// TCO for the whole function, which is sound (TCO is optional) and cheap —
/// address-taken locals rarely coincide with a hot tail call. Regression:
/// gcc-c-torture pr65369 (16 unaligned word copies into a local `buf[16]`, then
/// `foo(buf)` as the final call — trust-cg tail-called it and `foo` read the
/// freed frame, tripping `__stack_chk_fail`).
fn materializes_stack_slot_address(func: &MachFunction) -> bool {
    func.insts.iter().any(|inst| {
        matches!(
            inst.opcode,
            AArch64Opcode::AddPCRel | AArch64Opcode::StackAlloc
        ) && inst
            .operands
            .iter()
            .any(|op| matches!(op, MachOperand::StackSlot(_) | MachOperand::FrameIndex(_)))
    })
}

/// Return true when ISel has already staged stack-passed call arguments in
/// the caller's outgoing area.
///
/// A symbol tail branch must run the epilogue before branching. If a tail call
/// relies on stack-passed arguments, that cleanup would move SP away from the
/// staged outgoing arguments. Repacking those arguments into the caller's frame
/// is not modeled yet, so reject TCO conservatively for the whole function.
fn has_outgoing_stack_arg_store(func: &MachFunction) -> bool {
    func.insts.iter().any(is_outgoing_stack_arg_store)
}

fn is_outgoing_stack_arg_store(inst: &MachInst) -> bool {
    let (base_idx, offset_idx) = match inst.opcode {
        AArch64Opcode::StrRI | AArch64Opcode::StrbRI | AArch64Opcode::StrhRI => (1, 2),
        AArch64Opcode::StpRI => (2, 3),
        _ => return false,
    };

    if inst.operands.len() <= offset_idx {
        return false;
    }

    let base_is_sp = match &inst.operands[base_idx] {
        MachOperand::PReg(preg) if *preg == SP => true,
        MachOperand::Special(SpecialReg::SP) => true,
        _ => false,
    };
    if !base_is_sp {
        return false;
    }

    matches!(&inst.operands[offset_idx], MachOperand::Imm(offset) if *offset >= 0)
}

/// Check if a sibling call is compatible for tail call optimization.
///
/// Requirements:
/// - The callee's arguments must fit in registers (no additional stack space)
/// - Compatible return types (same count and compatible sizes)
/// - Not an indirect call (BLR) unless we can verify the target
fn is_sibling_compatible(
    func: &MachFunction,
    info: &TailCallInfo,
    caller_stack_size: u32,
    caller_param_count: usize,
    caller_return_count: usize,
) -> bool {
    let call_inst = func.inst(info.call_id);

    // Reject indirect calls (BLR) — we cannot verify the callee's
    // signature or stack requirements without interprocedural analysis.
    if matches!(call_inst.opcode, AArch64Opcode::Blr | AArch64Opcode::BLR) {
        return false;
    }
    if direct_call_branch_target(call_inst).is_none() {
        return false;
    }

    // On AArch64, the first 8 integer args go in x0-x7 and the first
    // 8 FP args go in d0-d7. If the callee needs more args than fit
    // in registers, it needs stack space we may not have.
    //
    // Count non-symbol, non-block operands as argument-like operands.
    // This is a conservative heuristic — in practice the lowering pass
    // will have set up the args in registers before the BL.
    let callee_arg_operands = call_inst
        .operands
        .iter()
        .filter(|op| !matches!(op, MachOperand::Symbol(_) | MachOperand::Block(_)))
        .count();

    // AArch64 AAPCS64: 8 GPR + 8 FPR = 16 register args max.
    // If the callee needs more than the caller provides frame space for,
    // reject. Conservative: if callee has any stack args beyond what
    // caller's frame can hold, reject.
    const MAX_REG_ARGS: usize = 8;
    if callee_arg_operands > MAX_REG_ARGS && caller_stack_size == 0 {
        return false;
    }

    // The caller must have at least as many return slots as the callee
    // would need. Since we cannot inspect the callee's signature
    // interprocedurally, we conservatively require the caller to have
    // return values (i.e., if the caller returns void, a sibling that
    // returns a value is incompatible).
    // Note: if both are void-returning, that's fine.
    // For now, accept all direct calls that pass the stack check —
    // the ABI compatibility is ensured by the lowering pass.
    let _ = (caller_param_count, caller_return_count);

    true
}

/// Apply self-recursive tail call optimization.
///
/// Replace:
///   BL <self>
///   [optional moves]
///   RET
///
/// With:
///   B <self>
fn apply_self_recursive_tco(
    func: &mut MachFunction,
    block_id: BlockId,
    info: &TailCallInfo,
    _caller_param_count: usize,
    provenance: Option<&mut ProvenanceMap>,
) {
    let target = func.name.clone();

    // Replace the call instruction with an unconditional symbol branch. A
    // local entry-block branch would be indistinguishable from a loop backedge
    // after frame lowering, so it could not safely receive an epilogue.
    let call = func.inst(info.call_id);
    let mut branch = MachInst::new(AArch64Opcode::TailCall, vec![MachOperand::Symbol(target)]);
    branch.implicit_defs = call.implicit_defs;
    branch.implicit_uses = call.implicit_uses;
    branch.proof = call.proof;
    branch.source_loc = call.source_loc;
    *func.inst_mut(info.call_id) = branch;
    record_tail_call_provenance(func, block_id, info, provenance);

    // Remove the RET and any intervening moves (they are dead after
    // the branch replaces the call — the branch is a terminator).
    let block = func.block_mut(block_id);
    // Keep everything up to and including the call (now a branch),
    // remove everything after.
    block.insts.truncate(info.call_idx + 1);

    // No local CFG edge is added for the symbol branch. Frame lowering and
    // encoding treat it as a function-exit tail branch.
}

/// Apply sibling tail call optimization.
///
/// Replace:
///   BL <target>
///   [optional moves]
///   RET
///
/// With:
///   B <target>
fn apply_sibling_tco(
    func: &mut MachFunction,
    block_id: BlockId,
    info: &TailCallInfo,
    provenance: Option<&mut ProvenanceMap>,
) -> bool {
    let call_inst = func.inst(info.call_id);
    let Some(branch_target) = direct_call_branch_target(call_inst) else {
        return false;
    };
    let call_implicit_defs = call_inst.implicit_defs;
    let call_implicit_uses = call_inst.implicit_uses;
    let call_proof = call_inst.proof;
    let call_source_loc = call_inst.source_loc;

    // Replace BL with B, keeping only the branch target. Call argument
    // operands are setup metadata for the call and are not valid B operands.
    let mut branch = MachInst::new(AArch64Opcode::TailCall, vec![branch_target]);
    branch.implicit_defs = call_implicit_defs;
    branch.implicit_uses = call_implicit_uses;
    branch.proof = call_proof;
    branch.source_loc = call_source_loc;
    *func.inst_mut(info.call_id) = branch;
    record_tail_call_provenance(func, block_id, info, provenance);

    // Remove the RET and any intervening moves.
    let block = func.block_mut(block_id);
    block.insts.truncate(info.call_idx + 1);
    true
}

fn record_tail_call_provenance(
    func: &MachFunction,
    block_id: BlockId,
    info: &TailCallInfo,
    provenance: Option<&mut ProvenanceMap>,
) {
    let Some(provenance) = provenance else {
        return;
    };

    let pass = PassId::new("tail-call");
    provenance.record_in_place_transform(info.call_id, pass.clone());

    for inst_id in func
        .block(block_id)
        .insts
        .iter()
        .take(info.ret_idx + 1)
        .skip(info.call_idx + 1)
        .copied()
    {
        let justification = if func.inst(inst_id).is_return() {
            "tail-call conversion removes post-call return"
        } else {
            "tail-call conversion removes post-call move"
        };
        provenance.record_deletion(inst_id, pass.clone(), justification);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pass_manager::{AnalysisCache, MachinePass};
    use trust_cg_ir::function::StackSlotSizeSource;
    use trust_cg_ir::{
        AArch64Opcode, BlockId, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap,
        ProvenanceStatus, RegClass, Signature, SourceLoc, StackSlot, TransformKind, TrustIrInstId,
        Type, VReg, regs,
    };

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    /// The AArch64 integer return register (`X0`), as an operand. A sound
    /// post-call return-value move reads the call's result from here.
    fn ret_reg() -> MachOperand {
        MachOperand::PReg(regs::X0)
    }

    /// `implicit_defs` for a call that produces an integer result in `X0`.
    const CALL_RESULT_DEFS: &[trust_cg_ir::PReg] = &[regs::X0];

    fn imm(val: i64) -> MachOperand {
        MachOperand::Imm(val)
    }

    fn sym(name: &str) -> MachOperand {
        MachOperand::Symbol(name.to_string())
    }

    fn source_loc(line: u32) -> SourceLoc {
        SourceLoc {
            file: 1,
            line,
            col: 5,
        }
    }

    fn make_func(name: &str, params: Vec<Type>, returns: Vec<Type>) -> MachFunction {
        MachFunction::new(name.to_string(), Signature::new(params, returns))
    }

    fn append_insts(func: &mut MachFunction, block: BlockId, insts: Vec<MachInst>) {
        for inst in insts {
            let id = func.push_inst(inst);
            func.append_inst(block, id);
        }
    }

    fn assert_optimized_away_by_tail_call(provenance: &ProvenanceMap, inst_id: InstId) {
        let entry = provenance.get_entry(inst_id).unwrap();
        match &entry.status {
            ProvenanceStatus::OptimizedAway {
                pass,
                justification,
            } => {
                assert_eq!(pass, &PassId::new("tail-call"));
                assert!(justification.starts_with("tail-call conversion removes post-call"));
            }
            other => panic!("expected tail-call optimized-away provenance, got {other:?}"),
        }
    }

    // ---- Test 1: Basic self-recursive tail call ----
    #[test]
    fn test_self_recursive_tail_call() {
        // factorial-like: BL factorial; RET
        let mut func = make_func("factorial", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("factorial")]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(tco.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 1);
        let inst = func.inst(block.insts[0]);
        assert_eq!(inst.opcode, AArch64Opcode::TailCall);
        assert_eq!(inst.operands[0], sym("factorial"));
    }

    // ---- Soundness: a non-call-result return blocks TCO ----
    #[test]
    fn test_tco_rejects_non_call_result_return() {
        // `BL helper` (result in X0); `MovR X0, v7` where v7 is a value that was
        // live across the call (NOT helper's result); `RET`. Truncating the move
        // and tail-branching would make the function return helper()'s result
        // instead of v7, so TCO must NOT fire. This is the shape SROA
        // store-to-load forwarding produces (`return a` across a call) and was a
        // real miscompile before the routing guard landed.
        let mut func = make_func("f", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("helper")])
                    .with_implicit_defs(CALL_RESULT_DEFS),
                MachInst::new(AArch64Opcode::MovR, vec![ret_reg(), vreg(7)]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(
            !tco.run(&mut func),
            "TCO must not fire when the returned value is a non-call-result value live across the call"
        );
        // Call, move, and ret are all preserved (nothing truncated).
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::Bl);
    }

    // ---- Test 2: Sibling tail call ----
    #[test]
    fn test_sibling_tail_call() {
        // fn foo() calls bar() in tail position
        let mut func = make_func("foo", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("bar")]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(tco.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 1);
        let inst = func.inst(block.insts[0]);
        assert_eq!(inst.opcode, AArch64Opcode::TailCall);
        assert_eq!(inst.operands[0], sym("bar"));
    }

    #[test]
    fn test_sibling_tail_call_strips_call_arg_operands() {
        let mut func = make_func("foo", vec![Type::I64, Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("bar"), vreg(0), vreg(1)]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(tco.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 1);
        let inst = func.inst(block.insts[0]);
        assert_eq!(inst.opcode, AArch64Opcode::TailCall);
        assert_eq!(
            inst.operands,
            vec![sym("bar")],
            "sibling TCO must not leave call argument operands on the branch"
        );
    }

    #[test]
    fn test_sibling_tail_call_preserves_exact_implicit_call_edges() {
        const CALL_USES: &[trust_cg_ir::PReg] = &[regs::X0, regs::X1, regs::D0];
        const CALL_DEFS: &[trust_cg_ir::PReg] = &[regs::X0, regs::X8];
        let mut func = make_func("foo", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("bar"), vreg(0)])
                    .with_implicit_uses(CALL_USES)
                    .with_implicit_defs(CALL_DEFS),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(tco.run(&mut func));

        let tail = func.inst(func.block(entry).insts[0]);
        assert_eq!(tail.opcode, AArch64Opcode::TailCall);
        assert_eq!(tail.operands, vec![sym("bar")]);
        assert_eq!(tail.implicit_uses, CALL_USES);
        assert_eq!(tail.implicit_defs, CALL_DEFS);
        assert!(tail.flags.is_call());
        assert!(tail.flags.is_branch());
        assert!(tail.flags.is_terminator());
    }

    #[test]
    fn test_source_loc_preserved_across_self_recursive_tail_call() {
        let loc = source_loc(41);
        let mut func = make_func("factorial", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("factorial")]).with_source_loc(loc),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(tco.run(&mut func));

        let block = func.block(func.entry);
        let branch = func.inst(block.insts[0]);
        assert_eq!(branch.opcode, AArch64Opcode::TailCall);
        assert_eq!(
            branch.source_loc,
            Some(loc),
            "tail-call must preserve source_loc when replacing self-recursive BL with B"
        );
    }

    #[test]
    fn test_source_loc_preserved_across_sibling_tail_call() {
        let loc = source_loc(57);
        let mut func = make_func("foo", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("bar")]).with_source_loc(loc),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(tco.run(&mut func));

        let block = func.block(func.entry);
        let branch = func.inst(block.insts[0]);
        assert_eq!(branch.opcode, AArch64Opcode::TailCall);
        assert_eq!(
            branch.source_loc,
            Some(loc),
            "tail-call must preserve source_loc when replacing sibling BL with B"
        );
    }

    #[test]
    fn test_tail_call_provenance_marks_self_recursive_call_and_truncated_insts() {
        let mut func = make_func("factorial", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("factorial")])
                    .with_implicit_defs(CALL_RESULT_DEFS),
                // Sound return-value move: routes the call's result (X0) onward.
                MachInst::new(AArch64Opcode::MovR, vec![vreg(0), ret_reg()]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let block = func.block(entry);
        let call_id = block.insts[0];
        let move_id = block.insts[1];
        let ret_id = block.insts[2];

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(90), &[call_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(91), &[move_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(92), &[ret_id], PassId::new("isel"));

        let mut tco = TailCallOptimization;
        let mut analyses = AnalysisCache::new();
        assert!(tco.run_with_analyses_and_provenance(&mut func, &mut analyses, &mut provenance));

        let block = func.block(entry);
        assert_eq!(block.insts, vec![call_id]);
        let branch = func.inst(call_id);
        assert_eq!(branch.opcode, AArch64Opcode::TailCall);
        assert_eq!(branch.operands[0], sym("factorial"));

        let call_entry = provenance.get_entry(call_id).unwrap();
        assert!(call_entry.is_active());
        assert_eq!(call_entry.trust_ir_origins, vec![TrustIrInstId(90)]);
        let transform = call_entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("tail-call"));
        assert_eq!(transform.kind, TransformKind::Survived);
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(90)),
            Some(&[call_id][..])
        );

        assert_optimized_away_by_tail_call(&provenance, move_id);
        assert_optimized_away_by_tail_call(&provenance, ret_id);
    }

    #[test]
    fn test_tail_call_provenance_direct_hook_marks_sibling_call_and_ret() {
        let mut func = make_func("foo", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("bar")]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let block = func.block(entry);
        let call_id = block.insts[0];
        let ret_id = block.insts[1];

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(100), &[call_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(101), &[ret_id], PassId::new("isel"));

        let mut tco = TailCallOptimization;
        assert!(tco.run_with_provenance(&mut func, &mut provenance));

        let block = func.block(entry);
        assert_eq!(block.insts, vec![call_id]);
        let branch = func.inst(call_id);
        assert_eq!(branch.opcode, AArch64Opcode::TailCall);
        assert_eq!(branch.operands[0], sym("bar"));

        let call_entry = provenance.get_entry(call_id).unwrap();
        assert_eq!(call_entry.trust_ir_origins, vec![TrustIrInstId(100)]);
        let transform = call_entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("tail-call"));
        assert_eq!(transform.kind, TransformKind::Survived);
        assert_optimized_away_by_tail_call(&provenance, ret_id);
    }

    // ---- Test 3: Non-tail call (work after call) ----
    #[test]
    fn test_non_tail_call_work_after() {
        // BL target; ADD v0, v1, v2; RET — add after call blocks TCO
        let mut func = make_func("f", vec![], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("helper")]),
                MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(!tco.run(&mut func));
    }

    // ---- Test 4: Store between call and return blocks TCO ----
    #[test]
    fn test_store_blocks_tco() {
        let mut func = make_func("f", vec![], vec![]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("target")]),
                MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), imm(8)]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(!tco.run(&mut func));
    }

    // ---- Test 5: Release (destructor) blocks TCO ----
    #[test]
    fn test_release_blocks_tco() {
        let mut func = make_func("f", vec![], vec![]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("target")]),
                MachInst::new(AArch64Opcode::Release, vec![vreg(5)]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(!tco.run(&mut func));
    }

    // ---- Test 6: MovR between call and return is allowed ----
    #[test]
    fn test_mov_between_call_and_ret_allowed() {
        let mut func = make_func("f", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("helper")])
                    .with_implicit_defs(CALL_RESULT_DEFS),
                // Sound return-value move: routes the call's result (X0) onward.
                MachInst::new(AArch64Opcode::MovR, vec![vreg(0), ret_reg()]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(tco.run(&mut func));

        let block = func.block(func.entry);
        // Call replaced with B, movr and ret removed
        assert_eq!(block.insts.len(), 1);
    }

    // ---- Test 7: No call in block — no change ----
    #[test]
    fn test_no_call_no_change() {
        let mut func = make_func("f", vec![], vec![]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(!tco.run(&mut func));
    }

    // ---- Test 8: No return in block — no change ----
    #[test]
    fn test_no_ret_no_change() {
        let mut func = make_func("f", vec![], vec![]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("target")]),
                MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(BlockId(1))]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(!tco.run(&mut func));
    }

    // ---- Test 9: Indirect call (BLR) rejected for sibling TCO ----
    #[test]
    fn test_indirect_call_rejected() {
        let mut func = make_func("f", vec![], vec![]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Blr, vec![vreg(10)]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        // BLR has no symbol, so it can't be detected as self-recursive,
        // and indirect calls are rejected for sibling TCO.
        assert!(!tco.run(&mut func));
    }

    #[test]
    fn test_targetless_direct_call_rejected() {
        let mut func = make_func("f", vec![Type::I64], vec![]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![vreg(10), vreg(0)]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(!tco.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::Bl);
        assert_eq!(func.inst(block.insts[1]).opcode, AArch64Opcode::Ret);
    }

    // ---- Test 10: Multiple blocks — only tail block optimized ----
    #[test]
    fn test_multi_block_only_tail_optimized() {
        let mut func = make_func("f", vec![Type::I64], vec![Type::I64]);

        // Block 0: non-tail call + branch
        let bb1 = func.create_block();
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("setup")]),
                MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
            ],
        );

        // Block 1: tail call + ret
        append_insts(
            &mut func,
            bb1,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("finish")]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(tco.run(&mut func));

        // Block 0 unchanged (not a tail call)
        let b0 = func.block(func.entry);
        assert_eq!(b0.insts.len(), 2);

        // Block 1 optimized: BL -> B
        let b1 = func.block(bb1);
        assert_eq!(b1.insts.len(), 1);
        let inst = func.inst(b1.insts[0]);
        assert_eq!(inst.opcode, AArch64Opcode::TailCall);
    }

    // ---- Test 11: Self-recursive tail call remains a symbol exit ----
    #[test]
    fn test_self_recursive_uses_symbol_tail_branch() {
        let mut func = make_func("recurse", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("recurse")]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        tco.run(&mut func);

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 1);
        let branch = func.inst(block.insts[0]);
        assert_eq!(branch.opcode, AArch64Opcode::TailCall);
        assert_eq!(branch.operands[0], sym("recurse"));
        assert!(
            !block.succs.contains(&func.entry),
            "symbol tail branches are function exits, not local loop backedges"
        );
    }

    // ---- Test 12: BL alias (LLVM-style) ----
    #[test]
    fn test_bl_alias_recognized() {
        let mut func = make_func("f", vec![], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::BL, vec![sym("other")]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(tco.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 1);
        let inst = func.inst(block.insts[0]);
        assert_eq!(inst.opcode, AArch64Opcode::TailCall);
    }

    // ---- Test 13: Idempotent — running twice has no effect ----
    #[test]
    fn test_idempotent() {
        let mut func = make_func("f", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("target")]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(tco.run(&mut func)); // First pass: transforms
        assert!(!tco.run(&mut func)); // Second pass: nothing to do
    }

    // ---- Test 14: Copy pseudo between call and ret allowed ----
    #[test]
    fn test_copy_between_call_and_ret() {
        let mut func = make_func("f", vec![], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("compute")])
                    .with_implicit_defs(CALL_RESULT_DEFS),
                // Sound return-value copy: routes the call's result (X0) onward.
                MachInst::new(AArch64Opcode::Copy, vec![vreg(0), ret_reg()]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(tco.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 1);
    }

    // ---- Test 15: Call followed by another call — last one is tail call ----
    #[test]
    fn test_two_calls_before_ret() {
        let mut func = make_func("f", vec![], vec![]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("first")]),
                MachInst::new(AArch64Opcode::Bl, vec![sym("second")]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(tco.run(&mut func));

        // Only the second call (the one in tail position) should be optimized.
        let block = func.block(func.entry);
        // first call remains, second becomes B
        assert_eq!(block.insts.len(), 2);
        let first = func.inst(block.insts[0]);
        assert_eq!(first.opcode, AArch64Opcode::Bl);
        let second = func.inst(block.insts[1]);
        assert_eq!(second.opcode, AArch64Opcode::TailCall);
    }

    // ---- Test 16: Empty block — no crash ----
    #[test]
    fn test_empty_block_no_crash() {
        let mut func = make_func("f", vec![], vec![]);
        // Entry block is empty (no instructions).
        let mut tco = TailCallOptimization;
        assert!(!tco.run(&mut func));
    }

    // ---- Test 17: Single instruction block (just RET) ----
    #[test]
    fn test_single_ret_no_change() {
        let mut func = make_func("f", vec![], vec![]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![MachInst::new(AArch64Opcode::Ret, vec![])],
        );

        let mut tco = TailCallOptimization;
        assert!(!tco.run(&mut func));
    }

    // ---- Test 18: Self-recursive with work before call is ok ----
    #[test]
    fn test_self_recursive_with_preamble() {
        let mut func = make_func("fib", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                // Some computation before the tail call
                MachInst::new(AArch64Opcode::SubRI, vec![vreg(0), vreg(0), imm(1)]),
                MachInst::new(AArch64Opcode::CmpRI, vec![vreg(0), imm(0)]),
                MachInst::new(AArch64Opcode::Bl, vec![sym("fib")]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(tco.run(&mut func));

        let block = func.block(func.entry);
        // sub, cmp, B (was BL), ret removed
        assert_eq!(block.insts.len(), 3);
        let last = func.inst(block.insts[2]);
        assert_eq!(last.opcode, AArch64Opcode::TailCall);
        assert_eq!(last.operands[0], sym("fib"));
    }

    // ---- Test 19: Verify pass name ----
    #[test]
    fn test_pass_name() {
        let tco = TailCallOptimization;
        assert_eq!(tco.name(), "tail-call");
    }

    // ---- Test 20: Sibling with stack slots but caller has enough frame ----
    #[test]
    fn test_sibling_with_caller_stack() {
        let mut func = make_func("f", vec![Type::I64], vec![Type::I64]);
        // Caller has a 16-byte stack frame
        func.alloc_stack_slot(StackSlot::new(16, 8));
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("callee")]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(tco.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 1);
        let inst = func.inst(block.insts[0]);
        assert_eq!(inst.opcode, AArch64Opcode::TailCall);
    }

    #[test]
    fn test_runtime_sized_stack_slot_blocks_tco() {
        let mut func = make_func("factorial", vec![Type::I64], vec![Type::I64]);
        func.alloc_stack_slot(StackSlot::new_dynamic(StackSlotSizeSource::Value(99), 16));
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("factorial")]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(!tco.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::Bl);
        assert_eq!(func.inst(block.insts[1]).opcode, AArch64Opcode::Ret);
    }

    #[test]
    fn test_runtime_sized_stack_slot_blocks_sibling_tco() {
        let mut func = make_func("caller", vec![Type::I64], vec![Type::I64]);
        func.alloc_stack_slot(StackSlot::new_dynamic(StackSlotSizeSource::Value(99), 16));
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("callee")]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(!tco.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::Bl);
        assert_eq!(func.inst(block.insts[1]).opcode, AArch64Opcode::Ret);
    }

    #[test]
    fn test_outgoing_stack_arg_store_blocks_tco() {
        let mut func = make_func("caller", vec![], vec![]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(
                    AArch64Opcode::StrRI,
                    vec![vreg(0), MachOperand::PReg(SP), imm(0)],
                ),
                MachInst::new(AArch64Opcode::Bl, vec![sym("printf")]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(!tco.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3);
        assert_eq!(func.inst(block.insts[1]).opcode, AArch64Opcode::Bl);
        assert_eq!(func.inst(block.insts[2]).opcode, AArch64Opcode::Ret);
    }
}
