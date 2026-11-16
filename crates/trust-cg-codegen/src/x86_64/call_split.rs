// trust-cg-codegen/src/x86_64/call_split.rs - live-range splitting around
// conditional in-loop calls (x86-64, pre-RA).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Live-range splitting around conditional in-loop calls.
//!
//! A value live across a call must sit in a callee-saved register or in a
//! spill slot. x86-64 System V has five allocatable callee-saved GPRs, so a
//! loop that carries more values than that across a call spills the rest, and
//! a spilled value pays a reload at every use and a store at every definition
//! on EVERY iteration, including the iterations that never reach the call.
//! `h4_vec_dropper`'s push loop is the measured case: its `Vec::push` grow
//! path calls `__rust_realloc`, and the loop counter and the xorshift state
//! were kept in stack slots for all 5,000,000 iterations, of which a handful
//! grow the vector.
//!
//! The split: for a call `C` in a block that does not lie on every iteration
//! of its innermost loop, every GPR value `V` live across `C` is copied into a
//! fresh temporary `T` immediately before `C`'s argument setup and back
//! immediately after `C`'s result reads:
//!
//! ```text
//!     MovRR T, V        ; T lives only across the call sequence
//!     <argument setup>
//!     call  ...
//!     <result reads>
//!     MovRR V, T
//! ```
//!
//! x86 ISel virtual registers are not SSA, so `V` keeps its identity
//! everywhere else and only its range across `C` moves to `T`. `V` no longer
//! crosses `C` and can take a caller-saved register on the paths that do not
//! reach the call; `T` crosses it and is allocated or spilled like any value
//! live across a call, so whatever save and restore it costs is paid on the
//! call's own path only. The two copies are pinned opaque to the pre-RA
//! coalescer (`X86RegallocConversion::pinned_copy_vregs`), which would
//! otherwise merge `T` back into `V`.
//!
//! The rewrite inserts two register copies of one value and changes nothing
//! else, so it preserves the function's meaning provided nothing between the
//! two copies writes `V` and the copy-out reads `V`'s current value. The
//! conditions below make that hold structurally; the allocator, its always-on
//! translation validator and TV-5 then see two ordinary `MovRR`s.
//!
//! Conditions, each pinned by a test in this module:
//! * the call is in a natural loop, and some path from the innermost
//!   containing loop's header to one of its latches avoids the call's block
//!   (profitability: a call on every iteration gains nothing from moving its
//!   save and restore onto its own path);
//! * the value is `Gpr64` or `Gpr32` and its id appears in the function in
//!   that one class only (an id read through two width views is one
//!   register; splitting one view would leave the other stale);
//! * the innermost loop defines the value (profitability: a value the loop
//!   only reads is often a constant or frame address the spiller
//!   rematerializes for free, and the copy back would make it multiply
//!   defined and no longer rematerializable; the measured first version split
//!   those too and pinned `h4_vec_dropper`'s field addresses in stack slots);
//! * no instruction from the call through the last result read names the
//!   value's id in any operand, in any class (the call reading `V`, or a
//!   result read redefining it, keeps `V` unsplit);
//! * the copy out goes before the call's argument-setup window (the run of
//!   instructions right before the call that name a physical register and
//!   are not a call, branch, return or terminator), so the value is dead
//!   while the argument registers are reserved; a value that window DEFINES
//!   stays unsplit (the copy out would read its old value), a value it only
//!   reads is split and stays live up to that read;
//! * the copy back goes after the call's result-read window: the run of
//!   instructions right after the call that name a physical register and are
//!   not a call, branch, return or terminator (result moves, stack
//!   adjustment), so a result register is read before the copy back can
//!   write any register;
//! * two calls of one block whose windows overlap (the first call's result
//!   reads run into the second call's argument setup, as in `g(f(x))`) form
//!   one window from the first call's setup through the last call's result
//!   reads, and the window conditions above apply to the whole of it.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_lower::instructions::Block as LirBlock;
use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelInst, X86ISelOperand};
use trust_cg_regalloc::{InstId, compute_live_intervals, find_call_crossings_in};

use super::pipeline::{
    X86NaturalLoop, X86PipelineError, X86RegallocConversion, x86_isel_to_regalloc_with,
    x86_natural_loops, x86_operand_access,
};

/// What [`split_around_conditional_calls`] did.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(super) struct CallSplitOutcome {
    /// The split temporaries; every copy that reads or writes one of them is a
    /// split copy.
    pub(super) temps: HashSet<VReg>,
    /// Split windows: one call, or several calls of one block whose windows
    /// overlap and were merged, around which at least one value was split.
    pub(super) calls: usize,
}

/// Every virtual register `inst` names, in any operand position.
fn named_vregs(inst: &X86ISelInst) -> impl Iterator<Item = VReg> + '_ {
    inst.operands.iter().flat_map(|operand| {
        let mut out = Vec::new();
        collect_operand_vregs(operand, &mut out);
        out
    })
}

fn collect_operand_vregs(operand: &X86ISelOperand, out: &mut Vec<VReg>) {
    match operand {
        X86ISelOperand::VReg(vreg) => out.push(*vreg),
        X86ISelOperand::MemAddr { base, .. } => collect_operand_vregs(base, out),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            collect_operand_vregs(base, out);
            collect_operand_vregs(index, out);
        }
        _ => {}
    }
}

fn names_preg(inst: &X86ISelInst) -> bool {
    inst.operands
        .iter()
        .any(|operand| matches!(operand, X86ISelOperand::PReg(_)))
}

fn ends_window(inst: &X86ISelInst) -> bool {
    inst.flags.is_call()
        || inst.flags.is_terminator()
        || inst.flags.is_branch()
        || inst.flags.is_return()
        || inst
            .operands
            .iter()
            .any(|operand| matches!(operand, X86ISelOperand::Block(_)))
}

/// Whether some path from `natural_loop`'s header to one of its latches,
/// staying inside the loop body, avoids `block`. The header itself is never
/// avoidable.
fn loop_avoids_block(
    func: &X86ISelFunction,
    natural_loop: &X86NaturalLoop,
    header: LirBlock,
    block: LirBlock,
) -> bool {
    if block == header {
        return false;
    }
    let latches: HashSet<LirBlock> = natural_loop.latches.iter().copied().collect();
    let mut seen: HashSet<LirBlock> = HashSet::from([header]);
    let mut work = vec![header];
    while let Some(current) = work.pop() {
        if latches.contains(&current) {
            return true;
        }
        let Some(mblock) = func.blocks.get(&current) else {
            continue;
        };
        for &succ in &mblock.successors {
            if succ != block && natural_loop.body.contains(&succ) && seen.insert(succ) {
                work.push(succ);
            }
        }
    }
    false
}

/// The blocks whose calls are split candidates: blocks of a natural loop that
/// some iteration of their innermost loop does not execute, each with the ids
/// of the virtual registers that loop's body DEFINES (any class, any operand
/// position the x86 access model marks as a definition).
fn conditional_call_blocks(func: &X86ISelFunction) -> HashMap<LirBlock, HashSet<u32>> {
    let has_call: Vec<LirBlock> = func
        .block_order
        .iter()
        .copied()
        .filter(|block| {
            // A block with no successor ends in a call that does not return
            // (a panic or abort sink). It is in no loop body, so it could never
            // qualify; skipping it here only spares the loop analysis for a
            // function whose calls are all such sinks.
            func.blocks.get(block).is_some_and(|b| {
                !b.successors.is_empty() && b.insts.iter().any(|inst| inst.flags.is_call())
            })
        })
        .collect();
    if has_call.is_empty() {
        return HashMap::new();
    }
    let loops = x86_natural_loops(func);
    let mut out = HashMap::new();
    for block in has_call {
        let innermost = loops
            .iter()
            .filter(|(_, natural_loop)| natural_loop.body.contains(&block))
            .min_by_key(|(header, natural_loop)| (natural_loop.body.len(), header.0));
        if let Some((&header, natural_loop)) = innermost
            && loop_avoids_block(func, natural_loop, header, block)
        {
            out.insert(block, loop_defined_ids(func, natural_loop));
        }
    }
    out
}

/// The ids of every virtual register some instruction of `natural_loop`
/// defines through a register operand.
fn loop_defined_ids(func: &X86ISelFunction, natural_loop: &X86NaturalLoop) -> HashSet<u32> {
    let mut ids = HashSet::new();
    for block in &natural_loop.body {
        let Some(mblock) = func.blocks.get(block) else {
            continue;
        };
        for inst in &mblock.insts {
            for (idx, operand) in inst.operands.iter().enumerate() {
                if let X86ISelOperand::VReg(vreg) = operand
                    && x86_operand_access(inst, idx).is_def
                {
                    ids.insert(vreg.id);
                }
            }
        }
    }
    ids
}

/// Split every eligible value around every eligible call (module docs).
/// Returns the temporaries, or an empty outcome when nothing qualifies, in
/// which case `func` is unchanged.
pub(super) fn split_around_conditional_calls(
    func: &mut X86ISelFunction,
) -> Result<CallSplitOutcome, X86PipelineError> {
    let candidates = conditional_call_blocks(func);
    if candidates.is_empty() {
        return Ok(CallSplitOutcome::default());
    }

    // The allocator's own view of which values cross which call.
    let ra = x86_isel_to_regalloc_with(func, &X86RegallocConversion::default())?;
    let liveness = compute_live_intervals(&ra);
    let crossings =
        find_call_crossings_in(&ra, liveness.intervals.values(), &liveness.inst_numbering);
    if crossings.is_empty() {
        return Ok(CallSplitOutcome::default());
    }

    // InstId -> (block, index): the conversion numbers instructions in block
    // order, then instruction order.
    let mut location: HashMap<InstId, (LirBlock, usize)> = HashMap::new();
    let mut next = 0u32;
    for &block in &func.block_order {
        let Some(mblock) = func.blocks.get(&block) else {
            continue;
        };
        for idx in 0..mblock.insts.len() {
            location.insert(InstId(next), (block, idx));
            next += 1;
        }
    }

    // Ids named in more than one class anywhere in the function.
    let mut classes: HashMap<u32, RegClass> = HashMap::new();
    let mut multi_class: HashSet<u32> = HashSet::new();
    for mblock in func.blocks.values() {
        for inst in &mblock.insts {
            for vreg in named_vregs(inst) {
                match classes.get(&vreg.id) {
                    Some(class) if *class != vreg.class => {
                        multi_class.insert(vreg.id);
                    }
                    Some(_) => {}
                    None => {
                        classes.insert(vreg.id, vreg.class);
                    }
                }
            }
        }
    }

    // One window per eligible call: (block, copy-out index, call index,
    // copy-back index, candidate values). The window conditions are applied
    // after overlapping windows are merged, below.
    let mut windows: Vec<(LirBlock, usize, usize, usize, Vec<VReg>)> = Vec::new();
    for crossing in &crossings {
        let Some(&(block, call_idx)) = location.get(&crossing.call_inst_id) else {
            continue;
        };
        let Some(loop_defined) = candidates.get(&block) else {
            continue;
        };
        let insts = &func.blocks[&block].insts;
        // The argument setup right before the call: the copy out goes in
        // front of it, so the split value is dead while the argument
        // registers are reserved.
        let mut front = call_idx;
        while front > 0 && !ends_window(&insts[front - 1]) && names_preg(&insts[front - 1]) {
            front -= 1;
        }
        let mut back = call_idx + 1;
        while back < insts.len() && !ends_window(&insts[back]) && names_preg(&insts[back]) {
            back += 1;
        }
        let values: Vec<VReg> = crossing
            .live_across
            .iter()
            .copied()
            .filter(|vreg| matches!(vreg.class, RegClass::Gpr64 | RegClass::Gpr32))
            .filter(|vreg| !multi_class.contains(&vreg.id))
            .filter(|vreg| loop_defined.contains(&vreg.id))
            .collect();
        if !values.is_empty() {
            windows.push((block, front, call_idx, back, values));
        }
    }

    // Two calls of one block whose windows overlap (the first call's result
    // reads run into the second call's argument setup, as in `g(f(x))`) are
    // one window: copy out before the first call's setup, copy back after the
    // last call's result reads. Applying them as two plans would insert the
    // first plan's copy back at an index the second plan's copy out has
    // already shifted, and put the second copy out between the first call and
    // its result reads. Merged windows are disjoint, so applying them from
    // the last backwards keeps every earlier index valid.
    windows.sort_by_key(|w| (w.0.0, w.1, w.2));
    let mut merged: Vec<(LirBlock, usize, usize, usize, Vec<VReg>)> = Vec::new();
    for window in windows {
        if let Some(last) = merged.last_mut()
            && last.0 == window.0
            && window.1 < last.3
        {
            last.3 = last.3.max(window.3);
            last.4.extend(window.4);
            continue;
        }
        merged.push(window);
    }

    // (block, copy-out index, copy-back index, values to split).
    let mut plans: Vec<(LirBlock, usize, usize, Vec<VReg>)> = Vec::new();
    for (block, front, first_call, back, mut values) in merged {
        let insts = &func.blocks[&block].insts;
        // A value the first call's argument setup DEFINES stays unsplit (the
        // copy out would read its old value); one it only reads is split.
        let setup_defs: HashSet<u32> = insts[front..first_call]
            .iter()
            .flat_map(|inst| {
                inst.operands
                    .iter()
                    .enumerate()
                    .filter_map(move |(idx, operand)| match operand {
                        X86ISelOperand::VReg(vreg) if x86_operand_access(inst, idx).is_def => {
                            Some(vreg.id)
                        }
                        _ => None,
                    })
            })
            .collect();
        // No instruction from the first call through the last result read
        // may name a split value in any class.
        let window_ids: HashSet<u32> = insts[first_call..back]
            .iter()
            .flat_map(named_vregs)
            .map(|vreg| vreg.id)
            .collect();
        values.retain(|vreg| !window_ids.contains(&vreg.id) && !setup_defs.contains(&vreg.id));
        values.sort_by_key(|vreg| vreg.id);
        values.dedup();
        if !values.is_empty() {
            plans.push((block, front, back, values));
        }
    }
    if plans.is_empty() {
        return Ok(CallSplitOutcome::default());
    }

    // Apply each block's plans from the last window backwards so earlier
    // indices stay valid.
    plans.sort_by(|a, b| (a.0.0, a.1).cmp(&(b.0.0, b.1)).reverse());
    let mut outcome = CallSplitOutcome::default();
    for (block, front, back, values) in plans {
        let mut copy_out = Vec::with_capacity(values.len());
        let mut copy_back = Vec::with_capacity(values.len());
        for value in values {
            let temp = VReg {
                id: func.next_vreg,
                class: value.class,
            };
            func.next_vreg += 1;
            let opcode = if value.class == RegClass::Gpr32 {
                X86Opcode::MovRR32
            } else {
                X86Opcode::MovRR
            };
            copy_out.push(X86ISelInst::new(
                opcode,
                vec![X86ISelOperand::VReg(temp), X86ISelOperand::VReg(value)],
            ));
            copy_back.push(X86ISelInst::new(
                opcode,
                vec![X86ISelOperand::VReg(value), X86ISelOperand::VReg(temp)],
            ));
            outcome.temps.insert(temp);
        }
        let insts = &mut func
            .blocks
            .get_mut(&block)
            .expect("a planned block exists")
            .insts;
        insts.splice(back..back, copy_back);
        insts.splice(front..front, copy_out);
        outcome.calls += 1;
    }
    Ok(outcome)
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::x86_64_ops::X86CondCode;
    use trust_cg_ir::x86_64_regs::{RAX, RDI};
    use trust_cg_lower::function::Signature;

    const B0: LirBlock = LirBlock(0);
    const HEADER: LirBlock = LirBlock(1);
    const TEST: LirBlock = LirBlock(2);
    const CALL: LirBlock = LirBlock(3);
    const EXIT: LirBlock = LirBlock(4);
    const LATCH: LirBlock = LirBlock(5);

    fn g64(id: u32) -> VReg {
        VReg {
            id,
            class: RegClass::Gpr64,
        }
    }

    fn inst(opcode: X86Opcode, operands: Vec<X86ISelOperand>) -> X86ISelInst {
        X86ISelInst::new(opcode, operands)
    }

    fn mov_ri(dst: VReg, imm: i64) -> X86ISelInst {
        inst(
            X86Opcode::MovRI,
            vec![X86ISelOperand::VReg(dst), X86ISelOperand::Imm(imm)],
        )
    }

    fn cmp(a: VReg, b: VReg) -> X86ISelInst {
        inst(
            X86Opcode::CmpRR,
            vec![X86ISelOperand::VReg(a), X86ISelOperand::VReg(b)],
        )
    }

    fn jcc(target: LirBlock) -> X86ISelInst {
        inst(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(X86CondCode::E),
                X86ISelOperand::Block(target),
            ],
        )
    }

    fn jmp(target: LirBlock) -> X86ISelInst {
        inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(target)])
    }

    fn call() -> X86ISelInst {
        inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())])
    }

    fn block(
        func: &mut X86ISelFunction,
        id: LirBlock,
        insts: Vec<X86ISelInst>,
        succs: &[LirBlock],
    ) {
        func.ensure_block(id);
        for i in insts {
            func.push_inst(id, i);
        }
        for &s in succs {
            func.add_successor(id, s);
        }
    }

    /// `v1` and `v2` are loop-carried, read in the latch and redefined there;
    /// `v3` is defined before the loop and only read in it. The call block
    /// is entered from TEST, which also branches straight to the latch unless
    /// `conditional` is false, in which case TEST falls through to the call
    /// only. `call_body` replaces the call block's instructions before the
    /// final jump.
    fn loop_with_call(conditional: bool, call_body: Vec<X86ISelInst>) -> X86ISelFunction {
        let sig = Signature::default();
        let mut func = X86ISelFunction::new("split".into(), sig);
        let (v1, v2, v3) = (g64(1), g64(2), g64(3));
        func.next_vreg = 10;
        block(
            &mut func,
            B0,
            vec![mov_ri(v1, 0), mov_ri(v2, 7), mov_ri(v3, 100), jmp(HEADER)],
            &[HEADER],
        );
        block(
            &mut func,
            HEADER,
            vec![cmp(v1, v3), jcc(EXIT), jmp(TEST)],
            &[EXIT, TEST],
        );
        if conditional {
            block(
                &mut func,
                TEST,
                vec![cmp(v2, v3), jcc(LATCH), jmp(CALL)],
                &[LATCH, CALL],
            );
        } else {
            block(&mut func, TEST, vec![cmp(v2, v3), jmp(CALL)], &[CALL]);
        }
        let mut body = call_body;
        body.push(jmp(LATCH));
        block(&mut func, CALL, body, &[LATCH]);
        block(&mut func, EXIT, vec![inst(X86Opcode::Ret, vec![])], &[]);
        block(
            &mut func,
            LATCH,
            vec![
                cmp(v1, v2),
                inst(
                    X86Opcode::MovRR,
                    vec![X86ISelOperand::VReg(v1), X86ISelOperand::VReg(v2)],
                ),
                inst(
                    X86Opcode::MovRR,
                    vec![X86ISelOperand::VReg(v2), X86ISelOperand::VReg(v1)],
                ),
                jmp(HEADER),
            ],
            &[HEADER],
        );
        func
    }

    fn split_values(func: &X86ISelFunction) -> Vec<u32> {
        let insts = &func.blocks[&CALL].insts;
        let call_at = insts.iter().position(|i| i.flags.is_call()).unwrap();
        insts[..call_at]
            .iter()
            .filter(|i| !names_preg(i))
            .filter_map(|i| match i.operands.as_slice() {
                [X86ISelOperand::VReg(_), X86ISelOperand::VReg(src)]
                    if i.opcode == X86Opcode::MovRR =>
                {
                    Some(src.id)
                }
                _ => None,
            })
            .collect()
    }

    #[test]
    fn splits_every_gpr_value_live_across_a_conditional_in_loop_call() {
        let mut func = loop_with_call(true, vec![call()]);
        let outcome = split_around_conditional_calls(&mut func).unwrap();
        assert_eq!(outcome.calls, 1);
        assert_eq!(outcome.temps.len(), 2);
        assert_eq!(split_values(&func), vec![1, 2]);
        // Copy back follows the call, reading the temporaries.
        let insts = &func.blocks[&CALL].insts;
        let call_at = insts.iter().position(|i| i.flags.is_call()).unwrap();
        for back in &insts[call_at + 1..call_at + 3] {
            let [X86ISelOperand::VReg(_), X86ISelOperand::VReg(src)] = back.operands.as_slice()
            else {
                panic!("expected a copy back, got {back:?}");
            };
            assert!(outcome.temps.contains(src));
        }
    }

    #[test]
    fn leaves_a_call_on_every_iteration_unsplit() {
        let mut func = loop_with_call(false, vec![call()]);
        let before = func.blocks[&CALL].insts.len();
        let outcome = split_around_conditional_calls(&mut func).unwrap();
        assert_eq!(outcome, CallSplitOutcome::default());
        assert_eq!(func.blocks[&CALL].insts.len(), before);
    }

    #[test]
    fn leaves_a_call_outside_every_loop_unsplit() {
        let sig = Signature::default();
        let mut func = X86ISelFunction::new("straight".into(), sig);
        func.next_vreg = 10;
        let (v1, v2) = (g64(1), g64(2));
        block(
            &mut func,
            B0,
            vec![mov_ri(v1, 0), cmp(v1, v1), jcc(EXIT), jmp(CALL)],
            &[EXIT, CALL],
        );
        block(
            &mut func,
            CALL,
            vec![call(), mov_ri(v2, 1), cmp(v1, v2), jmp(EXIT)],
            &[EXIT],
        );
        block(&mut func, EXIT, vec![inst(X86Opcode::Ret, vec![])], &[]);
        assert_eq!(
            split_around_conditional_calls(&mut func).unwrap(),
            CallSplitOutcome::default()
        );
    }

    #[test]
    fn leaves_an_id_with_two_width_views_unsplit() {
        let narrow = VReg {
            id: 2,
            class: RegClass::Gpr32,
        };
        let mut func = loop_with_call(true, vec![call()]);
        func.blocks.get_mut(&B0).unwrap().insts.insert(
            0,
            inst(
                X86Opcode::MovRI,
                vec![X86ISelOperand::VReg(narrow), X86ISelOperand::Imm(0)],
            ),
        );
        split_around_conditional_calls(&mut func).unwrap();
        assert_eq!(split_values(&func), vec![1]);
    }

    #[test]
    fn leaves_a_value_the_loop_only_reads_unsplit() {
        // v3 is live across the call (the header reads it every iteration)
        // but no instruction of the loop defines it.
        let mut func = loop_with_call(true, vec![call()]);
        split_around_conditional_calls(&mut func).unwrap();
        assert!(!split_values(&func).contains(&3));
        // Redefined in the loop before the call, it is split.
        let mut func = loop_with_call(true, vec![call()]);
        func.blocks
            .get_mut(&TEST)
            .unwrap()
            .insts
            .insert(0, mov_ri(g64(3), 100));
        split_around_conditional_calls(&mut func).unwrap();
        assert_eq!(split_values(&func), vec![1, 2, 3]);
    }

    #[test]
    fn leaves_a_value_named_by_the_call_unsplit() {
        let target = inst(X86Opcode::CallR, vec![X86ISelOperand::VReg(g64(2))]);
        let mut func = loop_with_call(true, vec![target]);
        split_around_conditional_calls(&mut func).unwrap();
        assert_eq!(split_values(&func), vec![1]);
    }

    #[test]
    fn copies_back_after_the_result_reads_and_skips_a_value_they_name() {
        let result = inst(
            X86Opcode::MovRR,
            vec![X86ISelOperand::VReg(g64(7)), X86ISelOperand::PReg(RAX)],
        );
        let use_result = cmp(g64(7), g64(1));
        let mut func = loop_with_call(true, vec![call(), result.clone(), use_result]);
        split_around_conditional_calls(&mut func).unwrap();
        let insts = &func.blocks[&CALL].insts;
        let call_at = insts.iter().position(|i| i.flags.is_call()).unwrap();
        assert_eq!(
            insts[call_at + 1].operands,
            result.operands,
            "the result read stays next to the call"
        );
        assert_eq!(split_values(&func), vec![1, 2]);

        // A window instruction that names a crossing value keeps it unsplit.
        let reads_v2 = inst(
            X86Opcode::MovRR,
            vec![X86ISelOperand::PReg(RDI), X86ISelOperand::VReg(g64(2))],
        );
        let mut func = loop_with_call(true, vec![call(), result, reads_v2]);
        split_around_conditional_calls(&mut func).unwrap();
        assert_eq!(split_values(&func), vec![1]);
    }

    #[test]
    fn copies_out_before_the_argument_setup_and_skips_a_value_it_defines() {
        let setup = inst(
            X86Opcode::MovRR,
            vec![X86ISelOperand::PReg(RDI), X86ISelOperand::VReg(g64(2))],
        );
        let mut func = loop_with_call(true, vec![setup.clone(), call()]);
        split_around_conditional_calls(&mut func).unwrap();
        let insts = &func.blocks[&CALL].insts;
        let setup_at = insts
            .iter()
            .position(|i| i.operands == setup.operands)
            .unwrap();
        assert_eq!(
            insts[setup_at + 1].opcode,
            X86Opcode::Call,
            "the argument setup stays next to the call"
        );
        assert_eq!(
            split_values(&func),
            vec![1, 2],
            "a value the setup reads is split"
        );

        let defines_v1 = inst(
            X86Opcode::MovRR,
            vec![X86ISelOperand::VReg(g64(1)), X86ISelOperand::PReg(RDI)],
        );
        let mut func = loop_with_call(true, vec![defines_v1, setup, call()]);
        split_around_conditional_calls(&mut func).unwrap();
        assert_eq!(split_values(&func), vec![2]);
    }

    #[test]
    fn merges_two_calls_whose_windows_overlap() {
        // `g(f())`: the first call's result read and the second call's
        // argument setup are one run of physical-register moves.
        let v7 = g64(7);
        let body = vec![
            call(),
            inst(
                X86Opcode::MovRR,
                vec![X86ISelOperand::VReg(v7), X86ISelOperand::PReg(RAX)],
            ),
            inst(
                X86Opcode::MovRR,
                vec![X86ISelOperand::PReg(RDI), X86ISelOperand::VReg(v7)],
            ),
            call(),
        ];
        let mut func = loop_with_call(true, body);
        let outcome = split_around_conditional_calls(&mut func).unwrap();
        assert_eq!(outcome.calls, 1, "the two windows are one");
        assert_eq!(outcome.temps.len(), 2);
        assert_eq!(split_values(&func), vec![1, 2]);
        let insts = &func.blocks[&CALL].insts;
        let calls: Vec<usize> = insts
            .iter()
            .enumerate()
            .filter(|(_, i)| i.flags.is_call())
            .map(|(idx, _)| idx)
            .collect();
        assert_eq!(calls.len(), 2);
        // Nothing lands between the first call and the second call: its
        // result read and the second call's setup stay contiguous.
        assert_eq!(calls[1] - calls[0], 3, "{insts:?}");
        // Both copies back follow the second call, reading the temporaries.
        for back in &insts[calls[1] + 1..calls[1] + 3] {
            let [X86ISelOperand::VReg(_), X86ISelOperand::VReg(src)] = back.operands.as_slice()
            else {
                panic!("expected a copy back, got {back:?}");
            };
            assert!(outcome.temps.contains(src));
        }
        assert_eq!(
            insts.len(),
            4 + 4 + 1,
            "four copies, four body insts, the jump"
        );
    }

    #[test]
    fn a_merged_window_keeps_a_value_named_between_its_calls_unsplit() {
        // v2 is read between the two calls (inside the merged window), so it
        // stays unsplit; v1 is split around both calls.
        let body = vec![
            call(),
            inst(
                X86Opcode::MovRR,
                vec![X86ISelOperand::VReg(g64(7)), X86ISelOperand::PReg(RAX)],
            ),
            inst(
                X86Opcode::MovRR,
                vec![X86ISelOperand::PReg(RDI), X86ISelOperand::VReg(g64(2))],
            ),
            call(),
        ];
        let mut func = loop_with_call(true, body);
        let outcome = split_around_conditional_calls(&mut func).unwrap();
        assert_eq!(outcome.calls, 1);
        assert_eq!(split_values(&func), vec![1]);
    }

    // The cold-call-region weighting (`pipeline::x86_cold_call_regions`)
    // reads the same loop shape; its conditions are pinned here.
    use super::super::pipeline::{x86_cold_call_regions, x86_natural_loops};

    #[test]
    fn cold_region_is_the_call_arm_of_an_in_loop_branch() {
        let func = loop_with_call(true, vec![call()]);
        assert_eq!(x86_cold_call_regions(&func), HashSet::from([CALL]));
    }

    #[test]
    fn cold_region_needs_a_call() {
        let func = loop_with_call(true, vec![mov_ri(g64(9), 0)]);
        assert!(x86_cold_call_regions(&func).is_empty());
    }

    #[test]
    fn cold_region_needs_the_other_arm_call_free() {
        let mut func = loop_with_call(true, vec![call()]);
        func.blocks.get_mut(&LATCH).unwrap().insts.insert(0, call());
        assert!(x86_cold_call_regions(&func).is_empty());
    }

    #[test]
    fn cold_region_needs_the_other_arm_call_free_with_the_call_arm_first() {
        // The same as above with the branch's successors in the other order.
        let mut func = loop_with_call(true, vec![call()]);
        let test = func.blocks.get_mut(&TEST).unwrap();
        test.successors = vec![CALL, LATCH];
        let n = test.insts.len();
        test.insts[n - 2] = jcc(CALL);
        test.insts[n - 1] = jmp(LATCH);
        assert_eq!(x86_cold_call_regions(&func), HashSet::from([CALL]));
        func.blocks.get_mut(&LATCH).unwrap().insts.insert(0, call());
        assert!(x86_cold_call_regions(&func).is_empty());
    }

    #[test]
    fn cold_region_needs_an_arm_entered_only_from_the_branch() {
        // TEST branches to MID or CALL, MID to CALL or LATCH: CALL has two
        // predecessors inside the loop, so it is a join, not an arm. (An edge
        // from outside the loop would instead dissolve the loop.)
        const MID: LirBlock = LirBlock(6);
        let mut func = loop_with_call(true, vec![call()]);
        let test = func.blocks.get_mut(&TEST).unwrap();
        test.successors = vec![MID, CALL];
        let n = test.insts.len();
        test.insts[n - 2] = jcc(MID);
        block(&mut func, MID, vec![jcc(CALL), jmp(LATCH)], &[CALL, LATCH]);
        assert!(
            x86_natural_loops(&func)
                .values()
                .any(|l| l.body.contains(&MID))
        );
        assert!(x86_cold_call_regions(&func).is_empty());
    }

    #[test]
    fn cold_region_never_holds_a_latch() {
        let mut func = loop_with_call(true, vec![call()]);
        // The call block jumps straight back to the header: it is a latch.
        let call_block = func.blocks.get_mut(&CALL).unwrap();
        call_block.successors = vec![HEADER];
        *call_block.insts.last_mut().unwrap() = jmp(HEADER);
        assert!(x86_cold_call_regions(&func).is_empty());
    }

    #[test]
    fn cold_region_needs_a_loop() {
        let mut func = X86ISelFunction::new("straight".into(), Signature::default());
        block(&mut func, B0, vec![jcc(EXIT), jmp(CALL)], &[EXIT, CALL]);
        block(&mut func, CALL, vec![call(), jmp(EXIT)], &[EXIT]);
        block(&mut func, EXIT, vec![inst(X86Opcode::Ret, vec![])], &[]);
        assert!(x86_cold_call_regions(&func).is_empty());
    }

    #[test]
    fn a_call_block_without_successors_is_no_candidate() {
        let mut func = loop_with_call(true, vec![call()]);
        // Make the call block a sink (a call that does not return).
        let sink = func.blocks.get_mut(&CALL).unwrap();
        sink.successors.clear();
        *sink.insts.last_mut().unwrap() = inst(X86Opcode::Ud2, vec![]);
        assert!(conditional_call_blocks(&func).is_empty());
        let func = loop_with_call(true, vec![call()]);
        assert_eq!(conditional_call_blocks(&func).len(), 1);
    }
}
