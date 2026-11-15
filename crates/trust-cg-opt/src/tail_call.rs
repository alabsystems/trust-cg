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
//!   when the call's classified ABI facts (recorded by instruction selection
//!   in [`MachFunction::call_abi_facts`]) show a compatible convention and
//!   stack arguments that fit the caller's own incoming argument area.
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
//! - The call has no classified ABI facts, or the facts name another callee
//!   (a pass-created or pass-rewritten call is unknown, never register-only)
//! - The call is indirect (`BLR`)
//! - The callee's convention preserves a different callee-saved set
//! - The call passes a hidden result pointer in X8 (`sret`)
//! - The call passes a composite by reference (AAPCS64 B.4): the pointer
//!   names a copy in the caller's frame, which the tail branch frees
//! - The callee needs stack arguments that do not fit the caller's own
//!   incoming argument area, are variadic or aggregate copies, or cannot be
//!   matched store-for-store with the classified stack arguments
//! - The caller materializes an address into its incoming argument area or
//!   reads that area after the call's first stack-argument store
//! - The caller has runtime-sized stack slots whose lifetime cannot yet be
//!   represented by a simple frame reuse
//! - There are cleanup operations (stores, releases) between the call
//!   and the return
//! - The return value is modified after the call
//!
//! # Stack-argument sibling calls
//!
//! A tail call cannot use its caller's outgoing argument area: the epilogue
//! frees the caller's frame before the branch. When every stack argument fits
//! in the caller's own incoming argument area (memory the caller's caller
//! reserved and no longer reads after the call), each outgoing store
//! `STR src, [SP, #off]` is redirected to `[FP, IncomingArg(off)]`, which
//! frame lowering resolves to the same offset above the caller's entry stack
//! pointer, where the callee finds it after the branch. The caller's own
//! incoming arguments are all loaded before the first redirected store, so the
//! overwrite cannot change a value the caller still reads.
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
    ProvenanceMap, RegClass, SpecialReg,
    regs::{SP, preg_class, reg_root},
};

use crate::effects::opcode_effect;
use crate::pass_manager::{AnalysisCache, MachinePass};
use trust_cg_ir::{CalleeSavedSet, StackArgStore, regs::FP};

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
    if has_runtime_sized_stack_slot(func) || materializes_stack_slot_address(func) {
        return false;
    }

    let protected = crate::eh_call_custody::ProtectedCalls::collect(func);
    let mut changed = false;
    let func_name = func.name.clone();
    let caller_stack_size = total_stack_size(func);
    let caller_param_count = func.signature.params.len();

    for block_id in func.block_order.clone() {
        let block = func.block(block_id);
        let insts = block.insts.clone();

        if let Some(tail_info) = detect_tail_call(func, &insts) {
            // A branch cannot retain the call's exceptional continuation.
            if protected.contains(tail_info.call_id) {
                continue;
            }
            // Check guard conditions common to all tail calls.
            if !guards_pass(func, &insts, &tail_info, caller_stack_size) {
                continue;
            }
            // The call's classified ABI facts decide whether its arguments
            // survive the frame teardown; a refusal keeps the `BL`.
            let Ok(plan) = tail_call_abi_plan(func, &insts, &tail_info) else {
                continue;
            };

            let call_inst = func.inst(tail_info.call_id);
            let call_target = extract_call_target(call_inst);
            let is_self_recursive = call_target.as_deref() == Some(func_name.as_str());

            if is_self_recursive {
                // Self-recursive tail call: use a symbol branch so frame
                // lowering can emit the same exit cleanup as sibling calls.
                if !redirect_stack_arguments(func, &plan, provenance.as_deref_mut()) {
                    continue;
                }
                apply_self_recursive_tco(
                    func,
                    block_id,
                    &tail_info,
                    caller_param_count,
                    provenance.as_deref_mut(),
                );
                changed = true;
            } else if direct_call_branch_target(func.inst(tail_info.call_id)).is_some() {
                // Sibling tail call: replace BL with B.
                if !redirect_stack_arguments(func, &plan, provenance.as_deref_mut()) {
                    continue;
                }
                if apply_sibling_tco(func, block_id, &tail_info, provenance.as_deref_mut()) {
                    changed = true;
                }
            }
        }
    }

    changed
}

/// How a tail call's arguments survive the caller's frame teardown.
#[derive(Debug, Clone, PartialEq, Eq)]
enum TailCallAbiPlan {
    /// Every argument is in a register.
    RegisterArguments,
    /// These outgoing stack-argument stores move into the caller's incoming
    /// argument area.
    StackArguments { stores: Vec<InstId> },
}

/// Why a call in tail position keeps its `BL`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TailCallRefusal {
    /// `BLR`: the callee and its ABI are unknown.
    IndirectCall,
    /// No direct branch target.
    NoDirectTarget,
    /// Instruction selection recorded no ABI facts for this call.
    UnclassifiedCall,
    /// The recorded facts name another callee.
    FactsNameAnotherCallee,
    /// The call passes a hidden result pointer in X8.
    HiddenResultPointer,
    /// An argument is the address of a by-reference composite's copy in the
    /// caller's frame.
    ByReferenceArgumentCopy,
    /// The call's stack arguments are variadic.
    VariadicStackArguments,
    /// A stack argument is an aggregate copy, not a list of scalar stores.
    AggregateStackArguments,
    /// The caller's incoming argument area was not recorded.
    UnrecordedIncomingArea,
    /// The callee needs more stack-argument bytes than the caller received.
    StackArgumentsExceedIncomingArea,
    /// The stores before the call do not match the classified stack
    /// arguments one for one.
    StackStoresDisagreeWithFacts,
    /// The caller computes an address into, or writes, its incoming area.
    IncomingAreaEscapes,
    /// The caller reads its incoming area after the first redirected store.
    IncomingAreaReadAfterStore,
}

/// Decide from the call's classified ABI facts whether it can become a tail
/// branch, and which stores must move with it.
fn tail_call_abi_plan(
    func: &MachFunction,
    insts: &[InstId],
    info: &TailCallInfo,
) -> Result<TailCallAbiPlan, TailCallRefusal> {
    let call_inst = func.inst(info.call_id);

    // Reject indirect calls (BLR): the callee, and so its signature, stack
    // requirements and callee-saved set, are unknown.
    if matches!(call_inst.opcode, AArch64Opcode::Blr | AArch64Opcode::BLR) {
        return Err(TailCallRefusal::IndirectCall);
    }
    if direct_call_branch_target(call_inst).is_none() {
        return Err(TailCallRefusal::NoDirectTarget);
    }
    let facts = func
        .call_abi_facts
        .get(&info.call_id)
        .ok_or(TailCallRefusal::UnclassifiedCall)?;
    if facts.callee.is_none() || facts.callee != extract_call_target(call_inst) {
        return Err(TailCallRefusal::FactsNameAnotherCallee);
    }
    // The callee must preserve every register the caller promised its own
    // caller to preserve. Every lowered function and every lowered callee
    // uses the AAPCS64 set today; a future convention must be admitted here
    // explicitly.
    match facts.callee_saved {
        CalleeSavedSet::Aapcs64 => {}
    }
    // An sret callee writes its result through X8. The caller's frame, where
    // a caller-allocated buffer would live, is gone after the branch; a
    // forwarded incoming pointer is not distinguished yet.
    if facts.hidden_result_pointer {
        return Err(TailCallRefusal::HiddenResultPointer);
    }
    // A composite over 16 bytes travels as a pointer to a copy the caller
    // made in its own frame (AAPCS64 B.4). The epilogue before the branch
    // frees that frame, so the callee would read and write released stack.
    // Refused by name, independently of the function-wide stack-address
    // guard in `run_tail_call`.
    if facts.by_reference_argument_copies {
        return Err(TailCallRefusal::ByReferenceArgumentCopy);
    }

    let stores = outgoing_stack_stores_before(func, insts, info.call_idx);
    if facts.stack_arg_bytes == 0 {
        // Register-only by classification: a staged stack store here would
        // contradict the facts, so refuse rather than drop it.
        return if stores.is_empty() && facts.stack_stores.is_empty() {
            Ok(TailCallAbiPlan::RegisterArguments)
        } else {
            Err(TailCallRefusal::StackStoresDisagreeWithFacts)
        };
    }

    if facts.variadic {
        return Err(TailCallRefusal::VariadicStackArguments);
    }
    if facts.aggregate_stack_args {
        return Err(TailCallRefusal::AggregateStackArguments);
    }
    let incoming = func
        .incoming_stack_arg_bytes
        .ok_or(TailCallRefusal::UnrecordedIncomingArea)?;
    if facts.stack_arg_bytes > incoming {
        return Err(TailCallRefusal::StackArgumentsExceedIncomingArea);
    }

    // Match the staged stores one for one with the classified arguments.
    let mut staged: Vec<StackArgStore> = Vec::with_capacity(stores.len());
    for &(_, inst_id) in &stores {
        staged.push(
            scalar_stack_store(func.inst(inst_id))
                .ok_or(TailCallRefusal::StackStoresDisagreeWithFacts)?,
        );
    }
    let mut expected = facts.stack_stores.clone();
    staged.sort_unstable();
    expected.sort_unstable();
    if staged != expected
        || expected.iter().any(|store| {
            store.offset < 0 || store.offset + i64::from(store.bytes) > i64::from(incoming)
        })
    {
        return Err(TailCallRefusal::StackStoresDisagreeWithFacts);
    }

    // The incoming area is rewritten below the caller: nothing may hold its
    // address, and every read of it must precede the first redirected store.
    for inst in &func.insts {
        let names_incoming_area = inst
            .operands
            .iter()
            .any(|operand| matches!(operand, MachOperand::IncomingArg(_)));
        if names_incoming_area && !is_incoming_argument_load(inst) {
            return Err(TailCallRefusal::IncomingAreaEscapes);
        }
    }
    // The facts named stack stores; a plan with none to redirect disagrees
    // with them and is refused rather than assumed.
    let Some(first_store) = stores.iter().map(|&(index, _)| index).min() else {
        return Err(TailCallRefusal::StackStoresDisagreeWithFacts);
    };
    let read_after = insts
        .iter()
        .take(info.call_idx)
        .skip(first_store)
        .any(|&inst_id| {
            func.inst(inst_id)
                .operands
                .iter()
                .any(|operand| matches!(operand, MachOperand::IncomingArg(_)))
        });
    if read_after {
        return Err(TailCallRefusal::IncomingAreaReadAfterStore);
    }

    Ok(TailCallAbiPlan::StackArguments {
        stores: stores.into_iter().map(|(_, inst_id)| inst_id).collect(),
    })
}

/// The outgoing stack-argument stores staged for the call at `call_idx`:
/// every `[SP, #nonneg]` store after the previous call in the block. Before
/// register allocation only call-argument staging writes there.
fn outgoing_stack_stores_before(
    func: &MachFunction,
    insts: &[InstId],
    call_idx: usize,
) -> Vec<(usize, InstId)> {
    let start = insts[..call_idx]
        .iter()
        .rposition(|&inst_id| func.inst(inst_id).flags.contains(InstFlags::IS_CALL))
        .map_or(0, |previous_call| previous_call + 1);
    insts
        .iter()
        .enumerate()
        .take(call_idx)
        .skip(start)
        .filter(|&(_, &inst_id)| is_outgoing_stack_arg_store(func.inst(inst_id)))
        .map(|(index, &inst_id)| (index, inst_id))
        .collect()
}

/// The `(offset, width)` of a single-register `STR{,B,H} src, [SP, #off]`
/// store, or `None` for any other shape (pairs included).
fn scalar_stack_store(inst: &MachInst) -> Option<StackArgStore> {
    let bytes = match inst.opcode {
        AArch64Opcode::StrbRI => 1,
        AArch64Opcode::StrhRI => 2,
        AArch64Opcode::StrRI => {
            let bits = match inst.operands.first()? {
                MachOperand::VReg(vreg) => vreg.class.size_bits(),
                MachOperand::PReg(preg) => preg_class(*preg).size_bits(),
                _ => return None,
            };
            u8::try_from(bits / 8).ok()?
        }
        _ => return None,
    };
    if inst.operands.len() != 3 {
        return None;
    }
    let base_is_sp = match &inst.operands[1] {
        MachOperand::PReg(preg) => *preg == SP,
        MachOperand::Special(SpecialReg::SP) => true,
        _ => false,
    };
    match &inst.operands[2] {
        MachOperand::Imm(offset) if base_is_sp && *offset >= 0 => Some(StackArgStore {
            offset: *offset,
            bytes,
        }),
        _ => None,
    }
}

/// A load from the incoming argument area: reads memory, writes none, and
/// names the area only as its offset.
fn is_incoming_argument_load(inst: &MachInst) -> bool {
    let effect = opcode_effect(inst.opcode);
    effect.reads_memory()
        && !effect.writes_memory()
        && !inst.flags.contains(InstFlags::WRITES_MEMORY)
        && matches!(inst.operands.get(1), Some(MachOperand::PReg(base)) if *base == FP)
        && matches!(inst.operands.get(2), Some(MachOperand::IncomingArg(_)))
}

/// Move a stack plan's stores from the caller's outgoing area into its
/// incoming argument area (`[FP, IncomingArg(off)]`, resolved by frame
/// lowering to the same offset above the entry stack pointer).
///
/// Returns `false`, having changed nothing, if a planned store no longer has
/// the `[SP, #imm]` shape `tail_call_abi_plan` admitted; the caller then
/// leaves that call untransformed instead of redirecting half of its stores.
fn redirect_stack_arguments(
    func: &mut MachFunction,
    plan: &TailCallAbiPlan,
    mut provenance: Option<&mut ProvenanceMap>,
) -> bool {
    let TailCallAbiPlan::StackArguments { stores } = plan else {
        return true;
    };
    let mut offsets = Vec::with_capacity(stores.len());
    for &inst_id in stores {
        let MachOperand::Imm(offset) = func.inst(inst_id).operands[2] else {
            return false;
        };
        offsets.push((inst_id, offset));
    }
    for (inst_id, offset) in offsets {
        let inst = func.inst_mut(inst_id);
        inst.operands[1] = MachOperand::PReg(FP);
        inst.operands[2] = MachOperand::IncomingArg(offset);
        if let Some(provenance) = provenance.as_deref_mut() {
            provenance.record_in_place_transform(inst_id, PassId::new("tail-call"));
        }
    }
    true
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

        // Side effects are a DELETION BARRIER, not a hint. Firing TCO
        // TRUNCATES this window (`block.insts.truncate(call_idx + 1)`), so an
        // instruction in it does not merely move -- it CEASES TO EXIST. Any
        // effect of it beyond routing a register value is silently lost.
        //
        // The sibling post-RA dead-code pass takes exactly this position: its
        // `has_side_effects` (trust-cg-regalloc/src/post_ra_opt.rs) refuses to
        // NOP an instruction carrying any of these flags. That pass deletes a
        // DEAD def; this one deletes a whole live window, so it may not be the
        // more permissive of the two.
        //
        // `is_move()` below cannot stand in for this check: it is an OPCODE
        // predicate, while flags are per-instruction (`MachInst::with_flags`,
        // preserved across the post-RA rebuild in `pipeline.rs`), so a move
        // opcode can carry side effects. MEASURED before this check: a `MovR`
        // flagged `IS_PSEUDO | HAS_SIDE_EFFECTS` between the call and the RET
        // fired and was deleted.
        if flags.contains(InstFlags::HAS_SIDE_EFFECTS)
            || flags.contains(InstFlags::READS_MEMORY)
            || flags.contains(InstFlags::IS_BRANCH)
            || flags.contains(InstFlags::IS_TERMINATOR)
        {
            return false;
        }

        // Release operations (destructor-like cleanup): check HAS_SIDE_EFFECTS
        // on the specific Release opcode. Kept as its own check even though
        // `Release`'s default flags include HAS_SIDE_EFFECTS: flags are
        // per-instruction and can be overwritten, the opcode cannot.
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
    intervening_insts_only_route_call_result(func, insts, info)
}

/// Returns true iff deleting every instruction between the call and the return
/// leaves the caller's observable result unchanged.
///
/// TCO does not KEEP the post-call moves: `apply_sibling_tco` and
/// `apply_self_recursive_tco` replace the call with a branch and truncate the
/// block at it. Control never comes back, so an instruction left after that
/// branch could not execute even if it were kept. The only two verdicts
/// available are therefore "this window is a no-op" and "reject the tail call":
/// a window that COMPUTES anything -- an i128 limb extraction (X1 -> X0), a
/// narrowing (a W-form write, or any write narrower than the register it lands
/// in) -- must reject.
///
/// The window is checked as an abstract transfer:
///
/// * every call-result register (`implicit_defs`) starts out holding its own
///   result, at its own width;
/// * each move copies a value, truncated to the narrowest width it passes
///   through -- the operand widths, and for `MOVWrr`/`MOVXrr` the opcode's form;
/// * physical locations are keyed by [`reg_root`], so `X0` and `W0` -- and `V0`,
///   `D0`, `S0` -- are ONE architectural register seen at different widths;
/// * every register an instruction DEFINES is part of the transfer -- the
///   operand destination AND every entry of its `implicit_defs`. Only the
///   CALL's own `implicit_defs` seed results; a window instruction's defs
///   CLOBBER ([`RoutedValue::Unknown`]) and enter the written set, so the final
///   obligation quantifies over them. MEASURED before that: a `BL` defining
///   (X0, X1) followed by `MovR v0, X0` carrying `implicit_defs = [X1]` fired
///   and deleted the window, leaving the callee's high limb in X1 instead of
///   what the deleted move had put there;
/// * a destination written twice keeps its LAST value. Machine IR is not SSA
///   (ISel deliberately reuses vregs -- see `gvn.rs`), and an append-only origin
///   list resolved to its FIRST entry re-opened the very miscompile this guard
///   exists to close.
///
/// The tail branch is sound iff every architectural register the window wrote
/// either (a) ends holding its OWN call result at the FULL width of that
/// register -- bit-for-bit what the branch leaves there -- or (b) is dead at
/// function exit ([`dead_at_function_exit`]). SROA store-to-load forwarding can
/// legitimately produce `BL f ; MovR ret, v ; RET` where `v` was defined
/// *before* the call: `v` is not a call result, the window is not a no-op, and
/// the tail call is refused.
///
/// MEASURED before any of this (aarch64, machine pipeline level 3):
/// `(callee_returning_u128() >> 64) as u64` compiled to a bare `b callee` and
/// returned the low half -- `hi()` in the
/// `trust-ir-cg-deref-field-scalar-borrow` run-make fixture, which aborted that
/// test binary with SIGABRT and empty output.
fn intervening_insts_only_route_call_result(
    func: &MachFunction,
    insts: &[InstId],
    info: &TailCallInfo,
) -> bool {
    let call_inst = func.inst(info.call_id);
    let mut state: Vec<(RouteLoc, RoutedValue)> = Vec::new();
    for preg in call_inst.implicit_defs {
        let Some(root) = reg_root(*preg) else {
            continue;
        };
        // Seed each root at the WIDEST width an implicit def names it with: a
        // narrower seed could never satisfy the full-width identity below.
        let named_width = preg_class(*preg).size_bits();
        let width = match route_lookup(&state, RouteLoc::Arch(root)) {
            RoutedValue::CallResult { width: seen, .. } => seen.max(named_width),
            RoutedValue::Unknown => named_width,
        };
        route_define(
            &mut state,
            RouteLoc::Arch(root),
            RoutedValue::CallResult { root, width },
        );
    }

    let mut written: Vec<(u8, u8)> = Vec::new();
    for inst_id in insts.iter().take(info.ret_idx).skip(info.call_idx + 1) {
        let inst = func.inst(*inst_id);
        // `guards_pass` already guaranteed these are pure register moves, so
        // operand 0 is the destination and operand 1 is the source.
        let (Some(dst), Some(src)) = (inst.operands.first(), inst.operands.get(1)) else {
            return false;
        };
        // A destination this guard does not model as a register (memory, a
        // special register, a symbol) is not a routed call result.
        let Some((dst_loc, dst_operand_width)) = route_loc(dst) else {
            return false;
        };
        let form_width = move_form_width(inst.opcode);
        let dst_width = dst_operand_width.min(form_width.unwrap_or(dst_operand_width));
        let value = match route_loc(src) {
            Some((src_loc, src_operand_width)) => {
                let src_width = src_operand_width.min(form_width.unwrap_or(src_operand_width));
                match route_lookup(&state, src_loc) {
                    RoutedValue::CallResult { root, width } => RoutedValue::CallResult {
                        root,
                        width: width.min(src_width).min(dst_width),
                    },
                    RoutedValue::Unknown => RoutedValue::Unknown,
                }
            }
            // An immediate, a symbol or a special register is a real definition,
            // not a routed call result.
            None => RoutedValue::Unknown,
        };
        route_define(&mut state, dst_loc, value);
        if let RouteLoc::Arch(root) = dst_loc {
            note_arch_write(&mut written, root);
        }

        // An instruction defines more than its operand destination. Every
        // entry of `implicit_defs` is written too, and the tail branch deletes
        // that write along with the rest of the window -- so each one is a
        // CLOBBER (`Unknown`) and enters `written`, which puts it INSIDE the
        // final full-width obligation instead of outside the quantifier.
        //
        // Applied AFTER the operand destination deliberately: an instruction
        // that names one register both ways then ends Unknown, which is the
        // fail-closed reading.
        //
        // Only the CALL's `implicit_defs` seed call results (above); on a
        // window instruction the same field destroys them. Keeping the two
        // apart is what lets a real AAPCS64 call still tail-call at all --
        // `call_implicit_defs` in trust-cg-lower gives every `Bl`/`Blr` the
        // whole caller-saved clobber set.
        //
        // A def this guard cannot key -- `NZCV`, `FPCR`, `FPSR`, or any
        // encoding outside the register model -- is REFUSED, not ignored: the
        // obligation cannot quantify over a register it cannot name.
        for preg in inst.implicit_defs {
            let Some(root) = reg_root(*preg) else {
                return false;
            };
            route_define(&mut state, RouteLoc::Arch(root), RoutedValue::Unknown);
            note_arch_write(&mut written, root);
        }
    }

    written.iter().all(|root| {
        // The one root this guard may not RESOLVE. [`reg_root`] keys SP, WSP,
        // XZR and WZR all to `(31, 0)`, although in A64 a register field's 31
        // selects SP or the zero register depending on the instruction: they
        // are distinct storage. Equal roots there mean "may overlap", not "is
        // the same register", so a value read back through that key is not
        // evidence about either register. Refusing it closes the one direction
        // in which the conflation could fail OPEN here: with `SP` among a
        // call's `implicit_defs`, `MovR SP, XZR` reads as SP forwarding its own
        // result at full width, and a real write to SP would be deleted.
        if conflated_sp_or_zero_root(*root) {
            return false;
        }
        let routed = route_lookup(&state, RouteLoc::Arch(*root));
        let holds_own_result_unchanged = matches!(
            routed,
            RoutedValue::CallResult { root: origin, width }
                if origin == *root && width == arch_full_width(*root)
        );
        let holds_own_result_as_returned = matches!(
            (routed, returned_view_width(func, insts, info, *root)),
            (RoutedValue::CallResult { root: origin, width }, Some(view))
                if origin == *root && width >= view
        );
        holds_own_result_unchanged || holds_own_result_as_returned || dead_at_function_exit(*root)
    })
}

/// The width of `root` that the caller of this function observes, when that is
/// a whole scalar return value narrower than the register: the RET reads a
/// single view of `root` (its authenticated return-register sink, e.g. `W0`
/// for an `i32` return, `S0` for an `f32` one), the function returns exactly
/// one value, and that value's type is exactly the view's width.
///
/// AAPCS64 (6.9, result return) leaves every bit of a result register above
/// the result's width unspecified: a caller of an `i32` function reads `W0`
/// and nothing of bits 63:32. So a window that forwards the low `view` bits of
/// the callee's own result into `root` leaves the caller exactly what the tail
/// branch leaves it. The type check keeps the one case where that is not
/// enough out: an `i8`/`i16`/`bool` return is read as `W0` too, but Darwin
/// requires the callee to extend it to 32 bits, which a forwarded wider result
/// need not be, so those still require the full-width identity.
fn returned_view_width(
    func: &MachFunction,
    insts: &[InstId],
    info: &TailCallInfo,
    root: (u8, u8),
) -> Option<u32> {
    use trust_cg_ir::function::Type;
    let [ret_ty] = func.signature.returns.as_slice() else {
        return None;
    };
    let ty_bits = match ret_ty {
        Type::I32 | Type::F32 => 32,
        Type::F16 => 16,
        Type::F64 => 64,
        _ => return None,
    };
    let ret = func.inst(*insts.get(info.ret_idx)?);
    let mut views = ret
        .implicit_uses
        .iter()
        .filter(|preg| reg_root(**preg) == Some(root));
    let view = *views.next()?;
    if views.next().is_some() {
        return None;
    }
    let view_bits = preg_class(view).size_bits();
    (view_bits == ty_bits && view_bits < arch_full_width(root)).then_some(view_bits)
}

/// Record that the window WROTE the architectural register `root`.
///
/// Only membership matters -- the final obligation quantifies over this set --
/// so a repeated write is not recorded twice. EVERY definition reaches here:
/// the operand destination and each entry of an instruction's `implicit_defs`.
fn note_arch_write(written: &mut Vec<(u8, u8)>, root: (u8, u8)) {
    if !written.contains(&root) {
        written.push(root);
    }
}

/// True for the single [`reg_root`] key that names more than one architectural
/// register: SP, WSP, XZR and WZR all key to `(31, 0)`.
///
/// `reg_root` is an OVER-approximation of overlap in that class and nowhere
/// else, which is safe for an interference test but not for a guard that reads
/// equal roots as "the same register". This pass is such a guard, so it refuses
/// the root rather than resolving it. Rejecting costs nothing real: `guards_pass`
/// admits only moves, and a move whose destination is SP or the zero register
/// is not a value route.
fn conflated_sp_or_zero_root(root: (u8, u8)) -> bool {
    root == (31, 0)
}

/// A value that may be flowing through the post-call move window.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum RoutedValue {
    /// The low `width` bits of the call's own result in the architectural
    /// register `root` (a [`reg_root`] key: register number, plus 0 for the GPR
    /// file / 1 for the FP-SIMD file). `width` is the width actually
    /// TRANSFERRED so far, so a hop through a `W`/`Gpr32` location records 32
    /// even when the value started in a 64-bit `X`.
    CallResult { root: (u8, u8), width: u32 },
    /// Anything else -- a value live across the call, an immediate, a special
    /// register. Never droppable into an architecturally observable register.
    Unknown,
}

/// Where a tracked value lives. Physical registers are keyed by [`reg_root`],
/// so `X0`/`W0` (and `V0`/`D0`/`S0`) are ONE location seen at two widths, which
/// is what lets this guard tell a narrowing from a forward instead of comparing
/// raw `PReg` numbers that make W0 and X0 look unrelated.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum RouteLoc {
    /// An architectural register, by its [`reg_root`] key.
    Arch((u8, u8)),
    /// A virtual register, by ID ALONE -- never by (id, class).
    ///
    /// A vreg's IDENTITY is its id; the class is a WIDTH ANNOTATION on that one
    /// register, not part of its name. Register allocation says so: intervals,
    /// spill slots and split parentage are all keyed by `vreg.id`
    /// (trust-cg-regalloc/src/lib.rs:678 and :1354, spill_slot_reuse.rs:109),
    /// and liveness recovers the class from an id->class map, MERGING the
    /// classes when one id is seen at two widths (`merge_vreg_class`,
    /// liveness.rs:563) -- a merge that exists precisely because the shape
    /// occurs.
    ///
    /// Keying on (id, class) instead SPLIT one machine register into two
    /// abstract locations, and that split was fail-OPEN in the WRITE direction:
    /// a second write under a different class landed on a different key and left
    /// the first entry live to be read back. A read miss fails closed; a write
    /// miss does not. MEASURED before this key:
    ///
    /// ```text
    /// BL raw_of              implicit_defs = [X0, X1]
    /// Copy v0:Gpr64, X0      low limb
    /// Copy v0:Gpr32, X1      SAME vreg -- high limb, 32 bits
    /// Copy X0, v0:Gpr64      reads the STALE low-limb entry
    /// RET                    => fired, truncated to 1 instruction
    /// ```
    ///
    /// which returns the callee's LOW limb: the u128 limb miscompile this guard
    /// exists to close, re-opened through the vreg key. The width is still taken
    /// from the operand's class (see [`route_loc`]), so narrowing detection is
    /// unchanged; only the LOCATION name is.
    ///
    /// A vreg defined inside the window cannot be read outside it: the window
    /// ends in a RET, which has no successors.
    Virt(u32),
}

/// The location and width an operand names, or `None` for an operand this guard
/// does not model as a register.
fn route_loc(op: &MachOperand) -> Option<(RouteLoc, u32)> {
    match op {
        MachOperand::PReg(preg) => {
            reg_root(*preg).map(|root| (RouteLoc::Arch(root), preg_class(*preg).size_bits()))
        }
        MachOperand::VReg(vreg) => {
            let class: RegClass = vreg.class;
            Some((RouteLoc::Virt(vreg.id), class.size_bits()))
        }
        _ => None,
    }
}

/// Width transferred by a move whose FORM fixes it: `MOVWrr` is the 32-bit form
/// and `MOVXrr` the 64-bit form, however their operands are spelled. The
/// pseudo-moves (`MovR`, `Copy`, `FmovFprFpr`) take their width from the
/// operands instead.
fn move_form_width(opcode: AArch64Opcode) -> Option<u32> {
    match opcode {
        AArch64Opcode::MOVWrr => Some(32),
        AArch64Opcode::MOVXrr => Some(64),
        _ => None,
    }
}

/// Full width of an architectural register: 64 bits for the GPR file, 128 for
/// the FP/SIMD file.
///
/// A narrower write ZEROES the rest of the register -- ARM ARM B1.2.1: a 32-bit
/// GPR write zero-extends into the 64-bit register, and the scalar FP forms zero
/// the upper lanes of the vector register -- so only a full-width write leaves a
/// register bit-identical to what the tail branch leaves there.
fn arch_full_width(root: (u8, u8)) -> u32 {
    if root.1 == 0 { 64 } else { 128 }
}

/// Volatile registers that carry no part of a function's result: X9-X15 and
/// V16-V31.
///
/// AAPCS64 6.1.1 lets any call corrupt these and 6.5 never returns a result in
/// one, so their contents at a function's return are unspecified and dropping a
/// write to one cannot be observed by the caller's caller. Everything else is
/// excluded deliberately: the argument/result registers X0-X7 and V0-V7 (a
/// result may live there -- the high limb of an i128 return lives in X1), the
/// callee-saved X19-X28 and V8-V15, the indirect-result register X8, the
/// IP0/IP1 veneer scratch X16/X17, the platform register X18, FP, LR, SP and the
/// zero registers.
fn dead_at_function_exit(root: (u8, u8)) -> bool {
    match root {
        (num, 0) => (9..=15).contains(&num),
        (num, 1) => (16..=31).contains(&num),
        _ => false,
    }
}

/// Look up a location's current value. Anything never written inside the window
/// -- and not a call-result register -- is [`RoutedValue::Unknown`].
fn route_lookup(state: &[(RouteLoc, RoutedValue)], loc: RouteLoc) -> RoutedValue {
    match state.iter().find(|(candidate, _)| *candidate == loc) {
        Some((_, value)) => *value,
        None => RoutedValue::Unknown,
    }
}

/// Record `loc := value`, REPLACING any previous entry for `loc`.
///
/// This is the fail-closed half of the redefinition rule: machine IR is not SSA,
/// so a location may be written more than once inside the window, and only the
/// LAST write is the one the return reads.
fn route_define(state: &mut Vec<(RouteLoc, RoutedValue)>, loc: RouteLoc, value: RoutedValue) {
    if let Some(idx) = state.iter().position(|(candidate, _)| *candidate == loc) {
        state[idx].1 = value;
    } else {
        state.push((loc, value));
    }
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
///
/// Only instructions the layout still executes count: a pass that removes an
/// instruction drops it from its block but leaves it in the arena, and a
/// scalarized (SROA) slot's dead address root is no escape.
fn materializes_stack_slot_address(func: &MachFunction) -> bool {
    func.block_order.iter().any(|block_id| {
        func.block(*block_id).insts.iter().any(|inst_id| {
            let inst = func.inst(*inst_id);
            matches!(
                inst.opcode,
                AArch64Opcode::AddPCRel | AArch64Opcode::StackAlloc
            ) && inst
                .operands
                .iter()
                .any(|op| matches!(op, MachOperand::StackSlot(_) | MachOperand::FrameIndex(_)))
        })
    })
}

/// A store into the outgoing argument area (`[SP, #nonneg]`), which before
/// register allocation only call-argument staging writes. A symbol tail
/// branch runs the epilogue first, so such a store belonging to the tail call
/// is either redirected into the incoming area or the call keeps its `BL`
/// (see [`tail_call_abi_plan`]).
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
    if call.flags.contains(InstFlags::EXACT_MODULE_CALL) {
        branch.flags.insert(InstFlags::EXACT_MODULE_CALL);
    }
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
    let exact_module_call = call_inst.flags.contains(InstFlags::EXACT_MODULE_CALL);

    // Replace BL with B, keeping only the branch target. Call argument
    // operands are setup metadata for the call and are not valid B operands.
    let mut branch = MachInst::new(AArch64Opcode::TailCall, vec![branch_target]);
    if exact_module_call {
        branch.flags.insert(InstFlags::EXACT_MODULE_CALL);
    }
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
    mod eh_call_custody_tests;
    use super::*;
    use crate::pass_manager::{AnalysisCache, MachinePass};
    use trust_cg_ir::function::StackSlotSizeSource;
    use trust_cg_ir::{
        AArch64Opcode, BlockId, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap,
        ProvenanceStatus, RegClass, Signature, SourceLoc, StackSlot, TransformKind, TrustIrInstId,
        Type, VReg, regs,
    };
    use trust_cg_ir::{CallAbiFacts, CalleeSavedSet, StackArgStore};

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

    /// Classified facts of a register-only direct call to `callee`.
    fn register_only_facts(callee: &str) -> CallAbiFacts {
        CallAbiFacts {
            callee: Some(callee.to_string()),
            stack_arg_bytes: 0,
            stack_stores: Vec::new(),
            aggregate_stack_args: false,
            hidden_result_pointer: false,
            by_reference_argument_copies: false,
            variadic: false,
            callee_saved: CalleeSavedSet::Aapcs64,
        }
    }

    /// Append `insts` as instruction selection would emit them: every direct
    /// call to a symbol carries register-only classified facts, so each test
    /// exercises the guard it names rather than the missing-facts refusal.
    fn append_insts(func: &mut MachFunction, block: BlockId, insts: Vec<MachInst>) {
        if func.incoming_stack_arg_bytes.is_none() {
            func.incoming_stack_arg_bytes = Some(0);
        }
        for inst in insts {
            let callee = (matches!(inst.opcode, AArch64Opcode::Bl | AArch64Opcode::BL))
                .then(|| extract_call_target(&inst))
                .flatten();
            let id = func.push_inst(inst);
            if let Some(callee) = callee {
                func.call_abi_facts.insert(id, register_only_facts(&callee));
            }
            func.append_inst(block, id);
        }
    }

    /// Append `insts` with no classified call facts.
    fn append_unclassified(func: &mut MachFunction, block: BlockId, insts: Vec<MachInst>) {
        for inst in insts {
            let id = func.push_inst(inst);
            func.append_inst(block, id);
        }
    }

    /// The single call instruction of `func`.
    fn call_id(func: &MachFunction) -> InstId {
        let calls: Vec<InstId> = func
            .block(func.entry)
            .insts
            .iter()
            .copied()
            .filter(|&id| func.inst(id).flags.contains(InstFlags::IS_CALL))
            .collect();
        assert_eq!(calls.len(), 1);
        calls[0]
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

    // ---- Classified call facts decide eligibility ----

    #[test]
    fn test_unclassified_call_keeps_its_bl() {
        let mut func = make_func("caller", vec![], vec![]);
        let entry = func.entry;
        append_unclassified(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("callee")]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        assert!(!TailCallOptimization.run(&mut func));
        assert_eq!(func.inst(call_id(&func)).opcode, AArch64Opcode::Bl);
    }

    #[test]
    fn test_facts_for_another_callee_keep_the_bl() {
        let mut func = make_func("caller", vec![], vec![]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("callee")]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let id = call_id(&func);
        func.call_abi_facts.insert(id, register_only_facts("other"));
        assert!(!TailCallOptimization.run(&mut func));
        assert_eq!(func.inst(id).opcode, AArch64Opcode::Bl);
    }

    #[test]
    fn test_hidden_result_pointer_keeps_the_bl() {
        let mut func = make_func("caller", vec![], vec![]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("callee")]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let id = call_id(&func);
        func.call_abi_facts
            .get_mut(&id)
            .unwrap()
            .hidden_result_pointer = true;
        assert!(!TailCallOptimization.run(&mut func));
        assert_eq!(func.inst(id).opcode, AArch64Opcode::Bl);
    }

    /// A composite passed by reference points at a copy in the caller's
    /// frame. The call keeps its `BL`, refused by name even with no stack
    /// address materialized in the function; the same call without the fact
    /// becomes a tail branch.
    #[test]
    fn test_by_reference_argument_copy_keeps_the_bl() {
        let build = |by_reference: bool| {
            let mut func = make_func("caller", vec![], vec![]);
            let entry = func.entry;
            append_insts(
                &mut func,
                entry,
                vec![
                    MachInst::new(AArch64Opcode::Bl, vec![sym("callee")]),
                    MachInst::new(AArch64Opcode::Ret, vec![]),
                ],
            );
            let id = call_id(&func);
            func.call_abi_facts
                .get_mut(&id)
                .unwrap()
                .by_reference_argument_copies = by_reference;
            (func, id)
        };

        let (func, _) = build(true);
        let insts = func.block(func.entry).insts.clone();
        let info = detect_tail_call(&func, &insts).expect("the call is in tail position");
        assert_eq!(
            tail_call_abi_plan(&func, &insts, &info),
            Err(TailCallRefusal::ByReferenceArgumentCopy)
        );
        let (mut func, id) = build(true);
        assert!(!TailCallOptimization.run(&mut func));
        assert_eq!(func.inst(id).opcode, AArch64Opcode::Bl);

        let (mut control, _) = build(false);
        assert!(TailCallOptimization.run(&mut control));
    }

    /// `caller(9 x i64 incoming, 16 stack bytes) -> callee(10 x i64)`: the two
    /// stack arguments fit the caller's incoming area.
    fn stack_argument_caller(incoming: u32, facts_bytes: u32) -> MachFunction {
        let mut func = make_func("caller", vec![Type::I64; 10], vec![Type::I64]);
        func.incoming_stack_arg_bytes = Some(incoming);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        vreg(20),
                        MachOperand::PReg(regs::FP),
                        MachOperand::IncomingArg(0),
                    ],
                ),
                MachInst::new(
                    AArch64Opcode::StrRI,
                    vec![vreg(21), MachOperand::PReg(SP), imm(0)],
                ),
                MachInst::new(
                    AArch64Opcode::StrRI,
                    vec![vreg(20), MachOperand::PReg(SP), imm(8)],
                ),
                MachInst::new(AArch64Opcode::Bl, vec![sym("callee")])
                    .with_implicit_defs(CALL_RESULT_DEFS),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let id = call_id(&func);
        let facts = func.call_abi_facts.get_mut(&id).unwrap();
        facts.stack_arg_bytes = facts_bytes;
        facts.stack_stores = vec![
            StackArgStore {
                offset: 0,
                bytes: 8,
            },
            StackArgStore {
                offset: 8,
                bytes: 8,
            },
        ];
        func
    }

    #[test]
    fn test_stack_argument_sibling_call_moves_stores_into_the_incoming_area() {
        let mut func = stack_argument_caller(16, 16);
        let stores = [
            func.block(func.entry).insts[1],
            func.block(func.entry).insts[2],
        ];
        let mut provenance = ProvenanceMap::new();
        for (origin, store) in stores.iter().enumerate() {
            provenance.record_lowering(
                TrustIrInstId(200 + origin as u32),
                &[*store],
                PassId::new("isel"),
            );
        }
        assert!(TailCallOptimization.run_with_provenance(&mut func, &mut provenance));
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
        for (index, offset) in [(1usize, 0i64), (2, 8)] {
            let store = func.inst(block.insts[index]);
            assert_eq!(store.opcode, AArch64Opcode::StrRI);
            assert_eq!(store.operands[1], MachOperand::PReg(regs::FP));
            assert_eq!(store.operands[2], MachOperand::IncomingArg(offset));
            let entry = provenance.get_entry(block.insts[index]).unwrap();
            assert!(
                entry
                    .transforms
                    .iter()
                    .any(|record| record.pass == PassId::new("tail-call")),
                "the redirected store records the tail-call transform"
            );
        }
        assert_eq!(func.inst(block.insts[3]).opcode, AArch64Opcode::TailCall);
    }

    #[test]
    fn test_stack_arguments_beyond_the_incoming_area_keep_the_bl() {
        let mut func = stack_argument_caller(8, 16);
        assert!(!TailCallOptimization.run(&mut func));
        let block = func.block(func.entry);
        assert_eq!(func.inst(block.insts[1]).operands[1], MachOperand::PReg(SP));
        assert_eq!(func.inst(block.insts[3]).opcode, AArch64Opcode::Bl);

        let mut unrecorded = stack_argument_caller(16, 16);
        unrecorded.incoming_stack_arg_bytes = None;
        assert!(!TailCallOptimization.run(&mut unrecorded));
    }

    #[test]
    fn test_stack_argument_refusal_controls() {
        type Mutate = Box<dyn Fn(&mut MachFunction)>;
        let variants: Vec<(&str, Mutate)> = vec![
            (
                "variadic",
                Box::new(|func: &mut MachFunction| {
                    let id = call_id(func);
                    func.call_abi_facts.get_mut(&id).unwrap().variadic = true;
                }),
            ),
            (
                "aggregate",
                Box::new(|func: &mut MachFunction| {
                    let id = call_id(func);
                    func.call_abi_facts
                        .get_mut(&id)
                        .unwrap()
                        .aggregate_stack_args = true;
                }),
            ),
            (
                "store list disagrees",
                Box::new(|func: &mut MachFunction| {
                    let id = call_id(func);
                    func.call_abi_facts.get_mut(&id).unwrap().stack_stores.pop();
                }),
            ),
            (
                "incoming-area address escapes",
                Box::new(|func: &mut MachFunction| {
                    let entry = func.entry;
                    let id = func.push_inst(MachInst::new(
                        AArch64Opcode::AddRI,
                        vec![
                            vreg(30),
                            MachOperand::PReg(regs::FP),
                            MachOperand::IncomingArg(0),
                        ],
                    ));
                    func.block_mut(entry).insts.insert(0, id);
                }),
            ),
            (
                "incoming-area read after a redirected store",
                Box::new(|func: &mut MachFunction| {
                    let entry = func.entry;
                    let id = func.push_inst(MachInst::new(
                        AArch64Opcode::LdrRI,
                        vec![
                            vreg(31),
                            MachOperand::PReg(regs::FP),
                            MachOperand::IncomingArg(8),
                        ],
                    ));
                    func.block_mut(entry).insts.insert(2, id);
                }),
            ),
        ];
        for (name, mutate) in variants {
            let mut func = stack_argument_caller(16, 16);
            mutate(&mut func);
            assert!(!TailCallOptimization.run(&mut func), "{name}");
            assert!(
                func.insts
                    .iter()
                    .all(|inst| inst.opcode != AArch64Opcode::TailCall),
                "{name}"
            );
        }
    }

    /// A self-recursive call is a sibling call to the same symbol: its stack
    /// arguments must move into the incoming area exactly as a sibling's do.
    /// Branching to itself with the stores left at `[SP, #off]` would write
    /// below the torn-down frame, and the next activation would read its own
    /// stale incoming arguments.
    #[test]
    fn test_self_recursive_stack_argument_call_redirects_its_stores() {
        let mut func = stack_argument_caller(16, 16);
        func.name = "callee".to_string();
        assert!(TailCallOptimization.run(&mut func));
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
        for (index, offset) in [(1usize, 0i64), (2, 8)] {
            let store = func.inst(block.insts[index]);
            assert_eq!(store.opcode, AArch64Opcode::StrRI);
            assert_eq!(store.operands[1], MachOperand::PReg(regs::FP), "{index}");
            assert_eq!(
                store.operands[2],
                MachOperand::IncomingArg(offset),
                "{index}"
            );
        }
        let branch = func.inst(block.insts[3]);
        assert_eq!(branch.opcode, AArch64Opcode::TailCall);
        assert_eq!(branch.operands, vec![sym("callee")]);

        // The same incoming-area bound applies to the recursive call.
        let mut overflow = stack_argument_caller(8, 16);
        overflow.name = "callee".to_string();
        assert!(!TailCallOptimization.run(&mut overflow));
        let block = overflow.block(overflow.entry);
        assert_eq!(
            overflow.inst(block.insts[1]).operands[1],
            MachOperand::PReg(SP)
        );
        assert_eq!(overflow.inst(block.insts[3]).opcode, AArch64Opcode::Bl);
    }

    #[test]
    fn test_register_only_facts_with_a_staged_stack_store_keep_the_bl() {
        // Classified register-only, yet a store stages an outgoing argument:
        // the facts and the code disagree, so nothing is dropped.
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
                MachInst::new(AArch64Opcode::Bl, vec![sym("callee")]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        assert!(!TailCallOptimization.run(&mut func));
    }

    #[test]
    fn test_register_only_tail_call_ignores_another_calls_stack_stores() {
        // The first call stages a stack argument; the tail call's own
        // arguments are all in registers, so the earlier store is irrelevant.
        let mut func = make_func("caller", vec![], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(
                    AArch64Opcode::StrRI,
                    vec![vreg(0), MachOperand::PReg(SP), imm(0)],
                ),
                MachInst::new(AArch64Opcode::Bl, vec![sym("first")]),
                MachInst::new(AArch64Opcode::Bl, vec![sym("second")])
                    .with_implicit_defs(CALL_RESULT_DEFS),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let first = func.block(entry).insts[1];
        let facts = func.call_abi_facts.get_mut(&first).unwrap();
        facts.stack_arg_bytes = 8;
        facts.stack_stores = vec![StackArgStore {
            offset: 0,
            bytes: 8,
        }];
        assert!(TailCallOptimization.run(&mut func));
        let block = func.block(entry);
        assert_eq!(func.inst(block.insts[1]).opcode, AArch64Opcode::Bl);
        assert_eq!(func.inst(block.insts[2]).opcode, AArch64Opcode::TailCall);
    }

    // ---- Soundness: cross-register limb routing after an i128-pair call ----
    /// A callee returning `u128` leaves its value in the ABI pair (X0, X1).
    /// `(callee() >> 64) as u64` routes the HIGH limb (X1) into the caller's
    /// single return register (X0). TCO deletes every post-call move, so firing
    /// here returns the callee's LOW limb instead. MEASURED miscompile: the
    /// `hi()` helper of the `trust-ir-cg-deref-field-scalar-borrow` run-make
    /// fixture compiled to a bare `b raw_of` and aborted that test binary.
    #[test]
    fn test_tco_rejects_cross_register_limb_route_from_pair_call() {
        const PAIR_RESULT_DEFS: &[trust_cg_ir::PReg] = &[regs::X0, regs::X1];
        let mut func = make_func("hi", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("raw_of")])
                    .with_implicit_defs(PAIR_RESULT_DEFS),
                // lo' = hi -- the `amt == 64` arm of the i128 constant-shift fold.
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![vreg(0), MachOperand::PReg(regs::X1)],
                ),
                // the truncation's ABI return copy into X0
                MachInst::new(AArch64Opcode::Copy, vec![ret_reg(), vreg(0)]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(
            !tco.run(&mut func),
            "TCO must not fire when a post-call move routes X1 into the X0 return slot"
        );
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4, "nothing may be truncated");
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::Bl);
    }

    /// The legitimate twin: an i128 result forwarded UNCHANGED keeps each limb
    /// in its own ABI register (X0 -> X0, X1 -> X1), so TCO must still fire.
    #[test]
    fn test_tco_allows_identity_pair_forwarding() {
        const PAIR_RESULT_DEFS: &[trust_cg_ir::PReg] = &[regs::X0, regs::X1];
        let mut func = make_func("fwd", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("raw_of")])
                    .with_implicit_defs(PAIR_RESULT_DEFS),
                MachInst::new(
                    AArch64Opcode::Copy,
                    vec![vreg(0), MachOperand::PReg(regs::X0)],
                ),
                MachInst::new(
                    AArch64Opcode::Copy,
                    vec![vreg(1), MachOperand::PReg(regs::X1)],
                ),
                MachInst::new(
                    AArch64Opcode::Copy,
                    vec![MachOperand::PReg(regs::X0), vreg(0)],
                ),
                MachInst::new(
                    AArch64Opcode::Copy,
                    vec![MachOperand::PReg(regs::X1), vreg(1)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(
            tco.run(&mut func),
            "identity limb forwarding must still tail-call"
        );
        assert_eq!(func.block(func.entry).insts.len(), 1);
    }

    // ======================================================================
    // Post-call move window: the four MEASURED defects of the first fix.
    //
    // Every test below states the verdict the guard must give. Each names the
    // ISA fact it turns on, so a later reviewer can attack the fact rather
    // than the code.
    // ======================================================================

    /// A virtual register of an explicit class — the class IS the width, which
    /// is what distinguishes a forward from a narrowing.
    fn vreg_in(id: u32, class: RegClass) -> MachOperand {
        MachOperand::VReg(VReg::new(id, class))
    }

    /// Machine IR is NOT SSA (see `gvn.rs`: ISel deliberately reuses vregs), so
    /// a vreg may be written twice inside the post-call window. The SECOND
    /// definition is the one the return copy reads; a guard that remembers only
    /// the FIRST origin re-opens the exact u128 limb miscompile it closed.
    #[test]
    fn test_tco_rejects_stale_origin_after_vreg_redefinition() {
        const PAIR_RESULT_DEFS: &[trust_cg_ir::PReg] = &[regs::X0, regs::X1];
        let mut func = make_func("hi_redef", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("raw_of")])
                    .with_implicit_defs(PAIR_RESULT_DEFS),
                // v0 := X0 (low limb)
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![vreg(0), MachOperand::PReg(regs::X0)],
                ),
                // v0 := X1 (high limb) -- v0 now holds the HIGH limb.
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![vreg(0), MachOperand::PReg(regs::X1)],
                ),
                // return v0: the HIGH limb routed into the X0 return slot.
                MachInst::new(AArch64Opcode::Copy, vec![ret_reg(), vreg(0)]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(
            !tco.run(&mut func),
            "a redefined vreg must be read at its LAST definition (X1, the high \
             limb), not its first (X0); firing here returns the callee's LOW limb"
        );
        assert_eq!(
            func.block(func.entry).insts.len(),
            5,
            "nothing may be truncated"
        );
    }

    /// `MOVWrr X0, X0` is `mov w0, w0`: an AArch64 32-bit register write ZEROES
    /// bits [63:32] of the 64-bit register (ARM ARM B1.2.1). It is a narrowing
    /// computation, not a no-op, so the tail branch may not delete it.
    #[test]
    fn test_tco_rejects_w_form_narrowing_of_the_call_result() {
        let mut func = make_func("narrow_same_name", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("g64")])
                    .with_implicit_defs(CALL_RESULT_DEFS),
                MachInst::new(
                    AArch64Opcode::MOVWrr,
                    vec![MachOperand::PReg(regs::X0), MachOperand::PReg(regs::X0)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(
            !tco.run(&mut func),
            "a W-form move zeroes the upper 32 bits -- deleting it changes the \
             returned value even though source and destination are both named X0"
        );
    }

    /// The same narrowing spelled the way ISel spells it for `g64() as i32`:
    /// a 32-bit vreg and the W0 return slot. It must get the SAME verdict as
    /// the X0/X0 spelling above -- register NAMING may not decide soundness.
    #[test]
    fn test_tco_rejects_i64_result_narrowed_to_a_w_return() {
        const WIDE_DEFS: &[trust_cg_ir::PReg] = &[regs::X0, regs::X1, regs::X8];
        let mut func = make_func("narrow_named", vec![Type::I64], vec![Type::I32]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("g64")]).with_implicit_defs(WIDE_DEFS),
                MachInst::new(
                    AArch64Opcode::MOVWrr,
                    vec![vreg_in(0, RegClass::Gpr32), MachOperand::PReg(regs::X0)],
                ),
                MachInst::new(
                    AArch64Opcode::Copy,
                    vec![MachOperand::PReg(regs::W0), vreg_in(0, RegClass::Gpr32)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(
            !tco.run(&mut func),
            "narrowing an i64 call result to a 32-bit return is a computation \
             the tail branch would delete"
        );
    }

    /// One semantics, one verdict: the two spellings of "narrow the callee's
    /// 64-bit result to 32 bits" must not disagree.
    #[test]
    fn test_tco_gives_narrowing_one_verdict_whatever_the_register_names() {
        const WIDE_DEFS: &[trust_cg_ir::PReg] = &[regs::X0, regs::X1, regs::X8];

        let mut same_name = make_func("narrow_a", vec![Type::I64], vec![Type::I64]);
        let entry = same_name.entry;
        append_insts(
            &mut same_name,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("g64")]).with_implicit_defs(WIDE_DEFS),
                MachInst::new(
                    AArch64Opcode::MOVWrr,
                    vec![MachOperand::PReg(regs::X0), MachOperand::PReg(regs::X0)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut named = make_func("narrow_b", vec![Type::I64], vec![Type::I32]);
        let entry = named.entry;
        append_insts(
            &mut named,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("g64")]).with_implicit_defs(WIDE_DEFS),
                MachInst::new(
                    AArch64Opcode::MOVWrr,
                    vec![vreg_in(0, RegClass::Gpr32), MachOperand::PReg(regs::X0)],
                ),
                MachInst::new(
                    AArch64Opcode::Copy,
                    vec![MachOperand::PReg(regs::W0), vreg_in(0, RegClass::Gpr32)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        let fired_same_name = tco.run(&mut same_name);
        let fired_named = tco.run(&mut named);
        assert_eq!(
            fired_same_name, fired_named,
            "the same narrowing got opposite verdicts: X0/X0 spelling fired={fired_same_name}, \
             v0/W0 spelling fired={fired_named}"
        );
        assert!(
            !fired_same_name,
            "a narrowing must reject, not fire, in either spelling"
        );
    }

    /// X0 -> X9 -> X0 is a pure no-op PAIR: the call result reaches the return
    /// register unchanged. X9 is a volatile temporary (AAPCS64 6.1.1) that holds
    /// no part of a result, so the scratch write is dead at function exit and
    /// TCO must still fire.
    #[test]
    fn test_tco_allows_forwarding_through_a_scratch_physical_register() {
        let mut func = make_func("scratch_fwd", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("callee")])
                    .with_implicit_defs(CALL_RESULT_DEFS),
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![MachOperand::PReg(regs::X9), MachOperand::PReg(regs::X0)],
                ),
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![MachOperand::PReg(regs::X0), MachOperand::PReg(regs::X9)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(
            tco.run(&mut func),
            "X0 -> X9 -> X0 leaves X0 holding the callee's result unchanged; \
             rejecting it loses a legitimate tail call"
        );
        assert_eq!(func.block(func.entry).insts.len(), 1);
    }

    /// The SAME shape with the scratch in a RESULT register (X1, the high limb
    /// of an i128 return) must still reject: X1's value at exit is observable.
    #[test]
    fn test_tco_rejects_forwarding_through_a_result_register() {
        let mut func = make_func("pair_scratch", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("callee")])
                    .with_implicit_defs(CALL_RESULT_DEFS),
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![MachOperand::PReg(regs::X1), MachOperand::PReg(regs::X0)],
                ),
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![MachOperand::PReg(regs::X0), MachOperand::PReg(regs::X1)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(
            !tco.run(&mut func),
            "X1 carries the high limb of an i128 return -- a write to it is not \
             dead at exit and may not be dropped"
        );
    }

    /// The narrowing hidden in a vreg CLASS while both physical registers are
    /// named X0: `Copy v0:Gpr32, X0 ; Copy X0, v0` is `g64() as u32 as u64`.
    /// Deleting it returns the full 64-bit result -- a live miscompile.
    #[test]
    fn test_tco_rejects_gpr32_vreg_narrowing_that_names_x0_twice() {
        let mut func = make_func("trunc_via_vreg", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("g64")])
                    .with_implicit_defs(CALL_RESULT_DEFS),
                MachInst::new(
                    AArch64Opcode::Copy,
                    vec![vreg_in(0, RegClass::Gpr32), MachOperand::PReg(regs::X0)],
                ),
                MachInst::new(
                    AArch64Opcode::Copy,
                    vec![MachOperand::PReg(regs::X0), vreg_in(0, RegClass::Gpr32)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(
            !tco.run(&mut func),
            "routing X0 through a 32-bit vreg and back into X0 zeroes bits \
             [63:32]; the destination NAME matching the origin does not make it \
             an identity"
        );
    }

    /// The FP twin: `Copy v0:Fpr64, V0 ; Copy V0, v0` writes only the low 64
    /// bits of V0 and zeroes lanes [127:64].
    #[test]
    fn test_tco_rejects_fpr64_vreg_narrowing_of_a_v_register_result() {
        const FP_DEFS: &[trust_cg_ir::PReg] = &[regs::V0];
        let mut func = make_func("fp_trunc_via_vreg", vec![], vec![]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("gvec")]).with_implicit_defs(FP_DEFS),
                MachInst::new(
                    AArch64Opcode::FmovFprFpr,
                    vec![vreg_in(0, RegClass::Fpr64), MachOperand::PReg(regs::V0)],
                ),
                MachInst::new(
                    AArch64Opcode::FmovFprFpr,
                    vec![MachOperand::PReg(regs::V0), vreg_in(0, RegClass::Fpr64)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(
            !tco.run(&mut func),
            "a 64-bit write of a 128-bit result register zeroes the upper lanes"
        );
    }

    /// The 32-bit ABI return lane (`W0` is the low half of the `X0` the call
    /// clobbers). Fail-closed: the guard understands W0 IS X0 at 32 bits, and a
    /// narrower write of a call-result register is not an identity it may drop.
    #[test]
    fn test_tco_rejects_w_lane_round_trip() {
        const WIDE_DEFS: &[trust_cg_ir::PReg] = &[regs::X0, regs::X1, regs::X8];
        let mut func = make_func("w_lane", vec![], vec![Type::I32]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("g32")]).with_implicit_defs(WIDE_DEFS),
                MachInst::new(
                    AArch64Opcode::Copy,
                    vec![vreg_in(0, RegClass::Gpr32), MachOperand::PReg(regs::W0)],
                ),
                MachInst::new(
                    AArch64Opcode::Copy,
                    vec![MachOperand::PReg(regs::W0), vreg_in(0, RegClass::Gpr32)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(
            !tco.run(&mut func),
            "the 32-bit return lane stays fail-closed until the caller's own \
             signature is consulted for which bits are observable"
        );
    }

    /// The `_main` entry wrapper's shape: `trunc(lang_start(...)) as i32`, an
    /// i64 call result narrowed into the W0 return lane of an `i32` function
    /// whose RET reads exactly `W0`. AAPCS64 leaves bits 63:32 of an `i32`
    /// result unspecified, so the caller observes only the low 32 bits, which
    /// the tail branch leaves identical: TCO fires.
    fn i32_return_of_narrowed_i64(
        returns: Vec<Type>,
        ret_uses: &'static [trust_cg_ir::PReg],
    ) -> MachFunction {
        const WIDE_DEFS: &[trust_cg_ir::PReg] = &[regs::X0, regs::X1, regs::X8];
        let mut func = make_func("entry_wrapper", vec![Type::I32, Type::Ptr], returns);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("lang_start")])
                    .with_implicit_defs(WIDE_DEFS),
                MachInst::new(
                    AArch64Opcode::Copy,
                    vec![vreg_in(6, RegClass::Gpr64), MachOperand::PReg(regs::X0)],
                ),
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![vreg_in(7, RegClass::Gpr32), vreg_in(6, RegClass::Gpr64)],
                ),
                MachInst::new(
                    AArch64Opcode::Copy,
                    vec![MachOperand::PReg(regs::W0), vreg_in(7, RegClass::Gpr32)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]).with_implicit_uses(ret_uses),
            ],
        );
        func
    }

    #[test]
    fn test_tco_fires_for_an_i32_return_that_reads_only_the_w_lane() {
        const W0_SINK: &[trust_cg_ir::PReg] = &[regs::W0];
        let mut func = i32_return_of_narrowed_i64(vec![Type::I32], W0_SINK);
        assert!(TailCallOptimization.run(&mut func));
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 1);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::TailCall);
    }

    /// Negative controls for the rule above: each keeps the `BL`.
    #[test]
    fn test_tco_narrow_return_rule_needs_signature_and_sink_agreement() {
        const W0_SINK: &[trust_cg_ir::PReg] = &[regs::W0];
        const X0_SINK: &[trust_cg_ir::PReg] = &[regs::X0];
        const BOTH_SINKS: &[trust_cg_ir::PReg] = &[regs::W0, regs::X0];
        for (returns, sink, why) in [
            // Darwin requires the callee to extend an i8 result to 32 bits; a
            // forwarded wider result need not be extended.
            (vec![Type::I8], W0_SINK, "i8 return"),
            (vec![Type::B1], W0_SINK, "bool return"),
            // An i64 return reads all of X0.
            (vec![Type::I64], W0_SINK, "i64 signature"),
            (vec![Type::I32], X0_SINK, "RET reads X0"),
            (vec![Type::I32], BOTH_SINKS, "RET reads two views"),
            (vec![Type::I32], &[], "no authenticated return sink"),
            (vec![Type::I32, Type::I32], W0_SINK, "two results"),
        ] {
            let mut func = i32_return_of_narrowed_i64(returns, sink);
            assert!(!TailCallOptimization.run(&mut func), "fired for {why}");
            assert_eq!(func.block(func.entry).insts.len(), 5, "{why}");
        }
    }

    /// A slot address root that an earlier pass deleted from its block (SROA
    /// full promotion) stays in the arena; it is not an escape.
    #[test]
    fn test_tco_ignores_a_deleted_stack_slot_address_root() {
        let mut func = make_func("shim", vec![Type::Ptr], vec![]);
        let slot = func.alloc_stack_slot(trust_cg_ir::StackSlot::new(8, 8));
        let dead_root = func.push_inst(MachInst::new(
            AArch64Opcode::AddPCRel,
            vec![vreg(1), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
        ));
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("callee")]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        assert!(!func.block(entry).insts.contains(&dead_root));
        assert!(TailCallOptimization.run(&mut func));

        // Control: the same root still in the block is an escape.
        let mut live = make_func("shim_live", vec![Type::Ptr], vec![]);
        let slot = live.alloc_stack_slot(trust_cg_ir::StackSlot::new(8, 8));
        let entry = live.entry;
        append_insts(
            &mut live,
            entry,
            vec![
                MachInst::new(
                    AArch64Opcode::AddPCRel,
                    vec![vreg(1), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
                ),
                MachInst::new(AArch64Opcode::Bl, vec![sym("callee")]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        assert!(!TailCallOptimization.run(&mut live));
    }

    /// The f64 ABI return lane (`D0` is the low half of `V0`). Same posture.
    #[test]
    fn test_tco_rejects_d_lane_round_trip() {
        const FP_DEFS: &[trust_cg_ir::PReg] = &[regs::V0, regs::V1];
        let mut func = make_func("d_lane", vec![], vec![]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("gf64")]).with_implicit_defs(FP_DEFS),
                MachInst::new(
                    AArch64Opcode::FmovFprFpr,
                    vec![vreg_in(0, RegClass::Fpr64), MachOperand::PReg(regs::D0)],
                ),
                MachInst::new(
                    AArch64Opcode::FmovFprFpr,
                    vec![MachOperand::PReg(regs::D0), vreg_in(0, RegClass::Fpr64)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(
            !tco.run(&mut func),
            "the f64 return lane stays fail-closed for the same reason as the \
             32-bit lane"
        );
    }

    /// The over-rejection pin: a FULL-WIDTH round trip through a vreg is a real
    /// identity and must keep firing.
    #[test]
    fn test_tco_allows_full_width_identity_through_a_vreg() {
        let mut func = make_func("full_width_fwd", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("g64")])
                    .with_implicit_defs(CALL_RESULT_DEFS),
                MachInst::new(
                    AArch64Opcode::Copy,
                    vec![vreg_in(0, RegClass::Gpr64), MachOperand::PReg(regs::X0)],
                ),
                MachInst::new(
                    AArch64Opcode::Copy,
                    vec![MachOperand::PReg(regs::X0), vreg_in(0, RegClass::Gpr64)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(
            tco.run(&mut func),
            "X0 -> v0:Gpr64 -> X0 is a genuine identity and must still tail-call"
        );
        assert_eq!(func.block(func.entry).insts.len(), 1);
    }

    /// The scratch exemption covers the scratch register's OWN value, not a
    /// laundering channel: X9 may be left holding anything, but whatever lands
    /// in a RESULT register must still be that register's own call result --
    /// including when the scratch is REDEFINED, where a first-match origin
    /// lookup would resolve it to the low limb.
    #[test]
    fn test_tco_rejects_limb_laundering_through_a_scratch_register() {
        const PAIR_RESULT_DEFS: &[trust_cg_ir::PReg] = &[regs::X0, regs::X1];
        let x0 = MachOperand::PReg(regs::X0);
        let x1 = MachOperand::PReg(regs::X1);
        let x9 = MachOperand::PReg(regs::X9);
        for window in [
            vec![
                MachInst::new(AArch64Opcode::MovR, vec![x9.clone(), x1.clone()]),
                MachInst::new(AArch64Opcode::MovR, vec![x0.clone(), x9.clone()]),
            ],
            vec![
                MachInst::new(AArch64Opcode::MovR, vec![x9.clone(), x0.clone()]),
                MachInst::new(AArch64Opcode::MovR, vec![x9.clone(), x1.clone()]),
                MachInst::new(AArch64Opcode::MovR, vec![x0.clone(), x9.clone()]),
            ],
        ] {
            let mut func = make_func("launder", vec![Type::I64], vec![Type::I64]);
            let entry = func.entry;
            let mut insts = vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("raw_of")])
                    .with_implicit_defs(PAIR_RESULT_DEFS),
            ];
            insts.extend(window);
            insts.push(MachInst::new(AArch64Opcode::Ret, vec![]));
            append_insts(&mut func, entry, insts);

            let mut tco = TailCallOptimization;
            assert!(
                !tco.run(&mut func),
                "the callee's HIGH limb reached the X0 return slot through a \
                 volatile temporary"
            );
        }
    }

    // ======================================================================
    // The two holes an ADVERSARIAL REVIEW measured in the window transfer
    // above, plus the one fail-open in `reg_root`'s SP/ZR conflation.
    //
    // All three are LATENT: ISel attaches `implicit_defs` only at call sites,
    // regalloc only clears them, and no `is_move()` opcode carries
    // HAS_SIDE_EFFECTS by default. They are reachable by construction through
    // public builders (`ISelInst::with_implicit_defs`, `MachInst::with_flags`,
    // both preserved by the post-RA rebuild), which is what these pin -- a
    // guard that DELETES instructions may not depend on no one ever producing
    // the shape it does not check.
    // ======================================================================

    /// HOLE 1. An intervening instruction defines more than its operands name.
    /// The transfer seeded from the CALL's `implicit_defs` and then read only
    /// operand 0 and operand 1 of each window instruction, so a register a
    /// window instruction defined IMPLICITLY was outside the final quantifier
    /// entirely: `MovR v0, X0` carrying `implicit_defs = [X1]` clobbers the
    /// high limb of an i128 return, and TCO DELETES it -- leaving X1 holding
    /// the callee's high limb instead of what the move put there.
    ///
    /// Both halves run in one test so the verdict is pinned to THE FIELD:
    /// identical windows, one with the implicit def and one without, must
    /// disagree. Before the fix they agreed (both fired).
    #[test]
    fn test_tco_rejects_a_window_implicit_def_of_a_result_register() {
        const PAIR_RESULT_DEFS: &[trust_cg_ir::PReg] = &[regs::X0, regs::X1];
        const CLOBBERS_HIGH_LIMB: &[trust_cg_ir::PReg] = &[regs::X1];

        let build = |window_defs: &'static [trust_cg_ir::PReg]| {
            let mut func = make_func("implicit_hi", vec![Type::I64], vec![Type::I64]);
            let entry = func.entry;
            append_insts(
                &mut func,
                entry,
                vec![
                    MachInst::new(AArch64Opcode::Bl, vec![sym("raw_of")])
                        .with_implicit_defs(PAIR_RESULT_DEFS),
                    MachInst::new(
                        AArch64Opcode::MovR,
                        vec![vreg(0), MachOperand::PReg(regs::X0)],
                    )
                    .with_implicit_defs(window_defs),
                    MachInst::new(AArch64Opcode::Copy, vec![ret_reg(), vreg(0)]),
                    MachInst::new(AArch64Opcode::Ret, vec![]),
                ],
            );
            func
        };

        let mut without_def = build(&[]);
        let fired_without = TailCallOptimization.run(&mut without_def);
        let mut with_def = build(CLOBBERS_HIGH_LIMB);
        let fired_with = TailCallOptimization.run(&mut with_def);

        assert!(
            fired_without,
            "control: X0 -> v0 -> X0 with no implicit def is a genuine identity \
             and must still tail-call"
        );
        assert!(
            !fired_with,
            "an implicit def of X1 in the window clobbers the high limb of an \
             i128 result and the tail branch DELETES that write, so TCO must \
             reject -- instead the verdict was independent of the field \
             (without={fired_without}, with={fired_with})"
        );
        assert_eq!(
            with_def.block(with_def.entry).insts.len(),
            4,
            "nothing may be truncated"
        );
    }

    /// The same shape with the implicit def on a CALLEE-SAVED register. X19 is
    /// preserved across a call (AAPCS64 6.1.1), so its value at the function's
    /// return is observable by the caller and a dropped write to it is not
    /// unobservable the way a scratch write is.
    #[test]
    fn test_tco_rejects_a_window_implicit_def_of_a_callee_saved_register() {
        const CLOBBERS_CALLEE_SAVED: &[trust_cg_ir::PReg] = &[regs::X19];
        let mut func = make_func("implicit_cs", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("callee")])
                    .with_implicit_defs(CALL_RESULT_DEFS),
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![vreg(0), MachOperand::PReg(regs::X0)],
                )
                .with_implicit_defs(CLOBBERS_CALLEE_SAVED),
                MachInst::new(AArch64Opcode::Copy, vec![ret_reg(), vreg(0)]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(
            !tco.run(&mut func),
            "a window instruction that implicitly defines the callee-saved X19 \
             is not a no-op, and the tail branch would delete that definition"
        );
    }

    /// The over-rejection pin for HOLE 1: an implicit def of a VOLATILE
    /// temporary (X9, AAPCS64 6.1.1 -- corruptible by any call, never part of
    /// a result) is dead at function exit, so the tail call must still fire.
    /// This one passes both before and after the fix: it pins that the fix did
    /// not become a blanket "any implicit def rejects", which would disable TCO
    /// on every real call site once ISel ever attaches one.
    #[test]
    fn test_tco_allows_a_window_implicit_def_of_a_dead_scratch_register() {
        const CLOBBERS_SCRATCH: &[trust_cg_ir::PReg] = &[regs::X9];
        let mut func = make_func("implicit_scratch", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("callee")])
                    .with_implicit_defs(CALL_RESULT_DEFS),
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![vreg(0), MachOperand::PReg(regs::X0)],
                )
                .with_implicit_defs(CLOBBERS_SCRATCH),
                MachInst::new(AArch64Opcode::Copy, vec![ret_reg(), vreg(0)]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(
            tco.run(&mut func),
            "an implicit def of the volatile X9 is dead at exit; rejecting it \
             loses a legitimate tail call"
        );
        assert_eq!(func.block(func.entry).insts.len(), 1);
    }

    /// HOLE 2. `guards_pass` checked WRITES_MEMORY, IS_CALL, the `Release`
    /// opcode and `is_move()` -- never HAS_SIDE_EFFECTS. `is_move()` is an
    /// OPCODE predicate while flags are per-instruction, so a side-effecting
    /// move walked through and was DELETED by the truncation. The sibling
    /// post-RA dead-code pass has always treated the flag as a barrier
    /// (`has_side_effects`, trust-cg-regalloc/src/post_ra_opt.rs), and this
    /// pass deletes strictly more than that one does.
    #[test]
    fn test_tco_rejects_a_side_effecting_move_in_the_window() {
        let build = |flags: InstFlags| {
            let mut func = make_func("side_effect_move", vec![Type::I64], vec![Type::I64]);
            let entry = func.entry;
            append_insts(
                &mut func,
                entry,
                vec![
                    MachInst::new(AArch64Opcode::Bl, vec![sym("callee")])
                        .with_implicit_defs(CALL_RESULT_DEFS),
                    MachInst::with_flags(
                        AArch64Opcode::MovR,
                        vec![vreg(0), MachOperand::PReg(regs::X0)],
                        flags,
                    ),
                    MachInst::new(AArch64Opcode::Copy, vec![ret_reg(), vreg(0)]),
                    MachInst::new(AArch64Opcode::Ret, vec![]),
                ],
            );
            func
        };

        // Control: the identical window with no barrier flag is a genuine
        // identity and must fire -- so the verdicts below are caused by the
        // flag and nothing else.
        let mut control = build(InstFlags::IS_PSEUDO);
        let mut tco = TailCallOptimization;
        assert!(
            tco.run(&mut control),
            "control: an unflagged X0 -> v0 -> X0 window must still tail-call"
        );

        for (name, flags) in [
            (
                "HAS_SIDE_EFFECTS",
                InstFlags::IS_PSEUDO.union(InstFlags::HAS_SIDE_EFFECTS),
            ),
            (
                "READS_MEMORY",
                InstFlags::IS_PSEUDO.union(InstFlags::READS_MEMORY),
            ),
        ] {
            let mut func = build(flags);
            let mut tco = TailCallOptimization;
            assert!(
                !tco.run(&mut func),
                "a move flagged {name} was admitted into a window the tail \
                 branch DELETES; the sibling post-RA pass refuses to NOP the \
                 same instruction"
            );
            assert_eq!(
                func.block(func.entry).insts.len(),
                4,
                "nothing may be truncated for {name}"
            );
        }
    }

    /// The `reg_root` SP/ZR conflation, CONTAINED at the consumer. `reg_root`
    /// keys SP, WSP, XZR and WZR to one root `(31, 0)`, but in A64 a register
    /// field's 31 selects SP or the zero register depending on the instruction
    /// -- distinct storage. Reading that key as "the same register" makes
    /// `MovR SP, XZR` look like SP forwarding its own full-width call result,
    /// and the write to SP is then deleted. The reported finding says this
    /// direction cannot happen here ("only ever OVER-rejects"); it can, once a
    /// call's `implicit_defs` name SP.
    #[test]
    fn test_tco_rejects_a_window_write_to_the_conflated_sp_zero_root() {
        const DEFS_WITH_SP: &[trust_cg_ir::PReg] = &[regs::X0, regs::SP];
        let mut func = make_func("sp_zero_root", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("callee")])
                    .with_implicit_defs(DEFS_WITH_SP),
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![MachOperand::PReg(regs::SP), MachOperand::PReg(regs::XZR)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(
            !tco.run(&mut func),
            "SP and XZR share a reg_root key but not storage; the guard must \
             refuse that root instead of reading `MovR SP, XZR` as SP \
             forwarding its own result"
        );
    }

    /// A vreg's NAME is its id. `Copy v0:Gpr64, X0 ; Copy v0:Gpr32, X1` writes
    /// ONE virtual register twice -- regalloc keys intervals and spill slots by
    /// `vreg.id` and merges the classes of an id seen at two widths -- so the
    /// second write DESTROYS the low limb the first one routed. A guard that
    /// keyed locations by (id, class) put the two writes on different keys, read
    /// the stale first entry back, and fired: MEASURED fired=true, truncated to
    /// 1 instruction, returning the callee's LOW limb.
    #[test]
    fn test_tco_rejects_limb_laundering_through_a_reclassed_vreg() {
        const PAIR_RESULT_DEFS: &[trust_cg_ir::PReg] = &[regs::X0, regs::X1];
        let mut func = make_func("reclass_launder", vec![Type::I64], vec![Type::I64]);
        let entry = func.entry;
        append_insts(
            &mut func,
            entry,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![sym("raw_of")])
                    .with_implicit_defs(PAIR_RESULT_DEFS),
                MachInst::new(
                    AArch64Opcode::Copy,
                    vec![vreg_in(0, RegClass::Gpr64), MachOperand::PReg(regs::X0)],
                ),
                MachInst::new(
                    AArch64Opcode::Copy,
                    vec![vreg_in(0, RegClass::Gpr32), MachOperand::PReg(regs::X1)],
                ),
                MachInst::new(
                    AArch64Opcode::Copy,
                    vec![ret_reg(), vreg_in(0, RegClass::Gpr64)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let mut tco = TailCallOptimization;
        assert!(
            !tco.run(&mut func),
            "the second write to v0 destroyed the low limb; naming it with a \
             different CLASS does not make it a different register"
        );
        assert_eq!(
            func.block(func.entry).insts.len(),
            5,
            "nothing may be truncated"
        );
    }

    /// One register, one verdict: re-spelling the CLASS of the clobbering write
    /// may not change the answer, because the class is not part of the vreg's
    /// name. Both spellings must reject -- the value read back is the high limb
    /// either way.
    #[test]
    fn test_tco_keys_a_vreg_by_id_not_by_id_and_class() {
        const PAIR_RESULT_DEFS: &[trust_cg_ir::PReg] = &[regs::X0, regs::X1];
        let verdict = |clobber_class: RegClass| {
            let mut func = make_func("reclass_verdict", vec![Type::I64], vec![Type::I64]);
            let entry = func.entry;
            append_insts(
                &mut func,
                entry,
                vec![
                    MachInst::new(AArch64Opcode::Bl, vec![sym("raw_of")])
                        .with_implicit_defs(PAIR_RESULT_DEFS),
                    MachInst::new(
                        AArch64Opcode::Copy,
                        vec![vreg_in(0, RegClass::Gpr64), MachOperand::PReg(regs::X0)],
                    ),
                    MachInst::new(
                        AArch64Opcode::Copy,
                        vec![vreg_in(0, clobber_class), MachOperand::PReg(regs::X1)],
                    ),
                    MachInst::new(
                        AArch64Opcode::Copy,
                        vec![ret_reg(), vreg_in(0, RegClass::Gpr64)],
                    ),
                    MachInst::new(AArch64Opcode::Ret, vec![]),
                ],
            );
            TailCallOptimization.run(&mut func)
        };

        let reclassed = verdict(RegClass::Gpr32);
        let same_class = verdict(RegClass::Gpr64);
        assert_eq!(
            reclassed, same_class,
            "one window got two verdicts from the CLASS of the clobbering write: \
             Gpr32 fired={reclassed}, Gpr64 fired={same_class}"
        );
        assert!(!reclassed, "both spellings must reject");
    }
}
