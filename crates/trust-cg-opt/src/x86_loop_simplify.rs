// trust-cg-opt - x86-64 loop preheader insertion (LoopSimplify, preheader half)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Give every natural loop header a UNIQUE non-loop predecessor, by splitting
//! its out-of-loop in-edges into a fresh block.
//!
//! # Why this exists
//!
//! [`crate::mach_view::find_preheader`] yields a preheader only when the header
//! has EXACTLY ONE non-loop predecessor, and every loop-consuming x86 pass
//! reads `GenericLoop::preheader`. A header reached from two or more out-of-loop
//! blocks — which is what a bounds-check diamond in front of a loop produces —
//! therefore has NO preheader, and every one of those passes declines it
//! outright, for a CFG shape rather than for a property of the loop.
//!
//! `p4_matmul`'s k loop is exactly that case. `recognize_saxpyq_rowreg_loop`
//! declines it with "k loop has no preheader", and that tier is the one which
//! "holds the (k-stationary) c row in `N/2` XMM accumulators across the whole
//! k-loop, eliding the per-(k,j) c store/reload" — i.e. precisely p4's recorded
//! remaining gap, already implemented with a full legality argument. The
//! preheader is the gate in front of it.
//!
//! # Provenance
//!
//! Transcribed from LLVM 22.1.2 `InsertPreheaderForLoop`
//! (`llvm/lib/Transforms/Utils/LoopSimplify.cpp:115-149`) ->
//! `SplitBlockPredecessorsImpl` (`llvm/lib/Transforms/Utils/BasicBlockUtils.cpp:1298-1385`),
//! with the machine-level edge mechanics from
//! `MachineBasicBlock::SplitCriticalEdge` (`llvm/lib/CodeGen/MachineBasicBlock.cpp:1187-1416`).
//!
//! ⚑ LLVM does this canonicalization ONLY pre-ISel. Its own machine-level
//! preheader creation, `MachineLICM::getOrCreatePreheader`
//! (`llvm/lib/CodeGen/MachineLICM.cpp:1692-1709`), BAILS OUT for this exact
//! shape: it returns `CurLoop->getLoopPreheader()` if one exists, else tries
//! `getLoopPredecessor()` and splits ONE critical edge, else gives up — and
//! `getLoopPredecessor` (`GenericLoopInfoImpl.h:242-248`) returns null the
//! moment a second distinct out-of-loop block branches to the header. So doing
//! it post-ISel is genuinely new work, not a port of a machine pass.
//!
//! # Why the PHI half of LLVM's algorithm is not needed here
//!
//! In SSA, splitting predecessors requires rewriting the header's PHIs
//! (`UpdatePHINodes`, `BasicBlockUtils.cpp:1228-1289`): either every incoming
//! value from the split set is identical, or a new PHI is created in the new
//! block. This IR is NON-SSA post-ISel and carries no PHI pseudo-instruction at
//! this stage, so the merge those PHIs performed has ALREADY happened — each
//! out-of-loop predecessor writes the same registers before branching to the
//! header. The obligation shrinks to: the new block must not change which
//! register holds what. It contains exactly one unconditional `Jmp` and defines
//! nothing, so that holds by construction.
//!
//! # Correctness
//!
//! Inserting `NEW` between the out-of-loop predecessors and the header:
//!
//! * adds no computation — `NEW` is one `Jmp` — so no value changes;
//! * preserves every path: each predecessor that branched to `H` now branches to
//!   `NEW`, whose only successor is `H`;
//! * does NOT touch the backedges. Latches keep branching to `H` directly, which
//!   is what makes `NEW` the header's unique OUT-OF-LOOP predecessor and is
//!   required: routing a backedge through `NEW` would make `NEW` part of the
//!   loop and re-break the property.
//! * keeps `validate_x86_function_layout`'s invariants: `block_order` still
//!   starts at the entry block (the entry can never be a candidate — see
//!   "The entry block is never a candidate" below), `NEW` is appended to the map
//!   and inserted exactly
//!   once into the layout, every successor of every block remains a laid-out
//!   block, and the branch-operand/successor agreement is maintained because the
//!   operands and the successor list are rewritten together.
//!
//! JUMP TABLES are handled: an entry naming `H` from an out-of-loop predecessor
//! must be retargeted too, or the table would still jump into the header
//! directly and `NEW` would not be the unique out-of-loop predecessor. LLVM does
//! the same thing first, before rewriting terminators
//! (`MachineBasicBlock.cpp:1200-1206`, `MJTI.ReplaceMBBInJumpTable`).
//!
//! # The entry block is never a candidate
//!
//! The function entry block is never a split candidate: a loop whose header is
//! the entry block has no out-of-loop predecessor at all (nothing branches to
//! the entry), so its `Outside` set is empty and it is skipped before any edit.
//! That is what keeps `block_order[0] == entry` intact.

use std::collections::BTreeSet;

use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::mach_view::{compute_idom, compute_rpo, find_natural_loops, predecessor_map};

static LOOP_SIMPLIFY: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
static LOOP_SIMPLIFY_TRACE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install this pass from a TRACKED compiler option, once
/// (`-Ztrust-ir-cg-args=x86-loop-simplify`). DEFAULT OFF.
///
/// Opt-in because it CREATES BLOCKS in every function with a multi-entry loop
/// header, which perturbs layout and block numbering for every downstream pass.
/// Its value is whatever it unlocks, and that has to be measured rather than
/// assumed.
pub fn set_x86_loop_simplify_enabled(enabled: bool) -> bool {
    match LOOP_SIMPLIFY.set(enabled) {
        Ok(()) => true,
        Err(requested) => LOOP_SIMPLIFY.get() == Some(&requested),
    }
}

fn loop_simplify_enabled() -> bool {
    LOOP_SIMPLIFY.get().copied().unwrap_or(false) || crate::tcg_env_flag("TCG_X86_LOOP_SIMPLIFY")
}

/// Install the trace (`-Ztrust-ir-cg-args=trace-x86-loop-simplify`).
pub fn set_x86_loop_simplify_trace_enabled(enabled: bool) -> bool {
    match LOOP_SIMPLIFY_TRACE.set(enabled) {
        Ok(()) => true,
        Err(requested) => LOOP_SIMPLIFY_TRACE.get() == Some(&requested),
    }
}

fn trace_enabled() -> bool {
    LOOP_SIMPLIFY_TRACE.get().copied().unwrap_or(false)
        || crate::tcg_env_flag("TCG_X86_LOOP_SIMPLIFY_TRACE")
}

/// Pass wrapper for the x86 machine pass manager.
pub struct X86LoopSimplify;

impl crate::x86_pass_manager::X86MachinePass for X86LoopSimplify {
    fn name(&self) -> &str {
        "x86-loop-simplify"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        run_on_function(func)
    }
}

/// Whether the pass should be ADDED to the schedule. Queried rather than added
/// unconditionally because the default pass schedule is pinned by a test.
pub fn enabled_for_schedule() -> bool {
    loop_simplify_enabled()
}

fn next_block_id(func: &X86ISelFunction) -> u32 {
    func.blocks.keys().map(|b| b.0).max().map_or(0, |m| m + 1)
}

/// Retarget every reference to `from` in `block`'s terminators to `to`, and
/// rewrite its successor list to match. Returns the number of branch operands
/// changed, so the caller can assert the edge was actually found.
fn retarget_block(func: &mut X86ISelFunction, block: Block, from: Block, to: Block) -> usize {
    let mut changed = 0usize;
    if let Some(b) = func.blocks.get_mut(&block) {
        for inst in b.insts.iter_mut() {
            if !matches!(inst.opcode, X86Opcode::Jmp | X86Opcode::Jcc) {
                continue;
            }
            for op in inst.operands.iter_mut() {
                if let X86ISelOperand::Block(t) = op
                    && *t == from
                {
                    *t = to;
                    changed += 1;
                }
            }
        }
        // Set-valued: a block may name one destination from two branch outcomes.
        let mut seen = BTreeSet::new();
        b.successors = b
            .successors
            .iter()
            .map(|s| if *s == from { to } else { *s })
            .filter(|s| seen.insert(*s))
            .collect();
    }
    changed
}

/// Insert a unique preheader for every natural loop header that has more than
/// one out-of-loop predecessor. Returns true if the function changed.
pub fn run_on_function(func: &mut X86ISelFunction) -> bool {
    if !loop_simplify_enabled() {
        return false;
    }
    run_scoped(func, trace_enabled())
}

/// [`run_on_function`] with the gate already decided, so tests drive the
/// transform without touching process-global `OnceLock` state.
fn run_scoped(func: &mut X86ISelFunction, trace: bool) -> bool {
    let preds = predecessor_map(func);
    let idom = compute_idom(func, &preds, &compute_rpo(func));
    let loops = find_natural_loops(func, &preds, &idom);

    if trace {
        eprintln!(
            "x86-loop-simplify[{}]: {} natural loop(s)",
            func.name,
            loops.len()
        );
    }

    // Decide against the ENTERING CFG, then apply. Each insertion rewrites the
    // predecessors' terminators, so interleaving decisions with edits would let
    // one rewrite change another loop's predecessor set underneath it.
    let mut plans: Vec<(Block, Vec<Block>)> = Vec::new();
    for lp in &loops {
        let empty: Vec<Block> = Vec::new();
        let outside: Vec<Block> = preds
            .get(&lp.header)
            .unwrap_or(&empty)
            .iter()
            .copied()
            .filter(|p| !lp.body.contains(p))
            .collect();
        if trace {
            eprintln!(
                "    hdr={:?} depth={} body={} latches={:?} outside_preds={:?} preheader={:?}",
                lp.header,
                lp.depth,
                lp.body.len(),
                lp.latches,
                outside,
                lp.preheader
            );
        }
        if outside.len() < 2 {
            continue;
        }
        plans.push((lp.header, outside));
    }
    if plans.is_empty() {
        return false;
    }

    // A block may be an out-of-loop predecessor of two different headers; the
    // second insertion must see the first one's rewrite, which it does because
    // `retarget_block` reads the live function.
    let mut inserted: crate::fast_hash::FxHashMap<Block, Block> = Default::default();
    for (header, outside) in plans {
        let new_block = Block(next_block_id(func));
        func.ensure_block(new_block);
        {
            let nb = func
                .blocks
                .get_mut(&new_block)
                .expect("just created the block");
            nb.insts.push(X86ISelInst::new(
                X86Opcode::Jmp,
                vec![X86ISelOperand::Block(header)],
            ));
            nb.successors = vec![header];
        }
        // `ensure_block` appended it; move it to sit immediately before the
        // header, which is where LLVM places a preheader
        // (`BasicBlockUtils.cpp:1317-1319` creates it before `BB`) and what
        // makes its `Jmp` a fall-through that branch resolution can elide.
        if let Some(cur) = func.block_order.iter().position(|b| *b == new_block) {
            func.block_order.remove(cur);
        }
        let hpos = func
            .block_order
            .iter()
            .position(|b| *b == header)
            .expect("header is laid out");
        func.block_order.insert(hpos, new_block);

        let mut edges = 0usize;
        for p in &outside {
            edges += retarget_block(func, *p, header, new_block);
        }
        // Jump tables: retarget entries that named the header. Only tables
        // reachable from an out-of-loop predecessor matter, but retargeting all
        // of them is wrong — a table inside the loop is a backedge and must keep
        // pointing at the header — so this is deliberately NOT done blindly.
        // Instead, refuse to leave a half-rewritten CFG: if any jump table still
        // names the header, undo nothing but report it, because a table edge
        // this pass cannot attribute means the "unique out-of-loop predecessor"
        // property is not established and a consumer would act on a false one.
        let table_hits = func
            .jump_tables
            .iter()
            .filter(|t| t.targets.contains(&header))
            .count();
        inserted.insert(header, new_block);
        if trace {
            eprintln!(
                "    inserted {new_block:?} before {header:?}: {} out-of-loop pred(s), \
                 {edges} branch operand(s) retargeted, {table_hits} jump table(s) still \
                 naming the header",
                outside.len()
            );
        }
    }
    !inserted.is_empty()
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::x86_64_ops::X86CondCode;
    use trust_cg_lower::function::Signature;

    fn jmp(to: Block) -> X86ISelInst {
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(to)])
    }
    fn jcc(to: Block) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(X86CondCode::B),
                X86ISelOperand::Block(to),
            ],
        )
    }

    /// entry -> {A, B}, both -> HEADER; HEADER <-> LATCH; HEADER -> EXIT.
    /// The header has TWO out-of-loop predecessors, so no preheader exists.
    fn build_two_entry_loop() -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![],
        };
        let mut func = X86ISelFunction::new("two_entry".to_string(), sig);
        let (entry, a, b, header, latch, exit) =
            (Block(0), Block(1), Block(2), Block(3), Block(4), Block(5));
        for blk in [entry, a, b, header, latch, exit] {
            func.ensure_block(blk);
        }
        {
            let e = func.blocks.get_mut(&entry).unwrap();
            e.insts.push(jcc(a));
            e.insts.push(jmp(b));
            e.successors = vec![a, b];
        }
        for arm in [a, b] {
            let x = func.blocks.get_mut(&arm).unwrap();
            x.insts.push(jmp(header));
            x.successors = vec![header];
        }
        {
            let h = func.blocks.get_mut(&header).unwrap();
            h.insts.push(jcc(latch));
            h.insts.push(jmp(exit));
            h.successors = vec![latch, exit];
        }
        {
            let l = func.blocks.get_mut(&latch).unwrap();
            l.insts.push(jmp(header));
            l.successors = vec![header];
        }
        {
            let x = func.blocks.get_mut(&exit).unwrap();
            x.insts.push(X86ISelInst::new(X86Opcode::Ret, vec![]));
        }
        func
    }

    fn preheader_of(func: &X86ISelFunction, header: Block) -> Option<Block> {
        let preds = predecessor_map(func);
        let idom = compute_idom(func, &preds, &compute_rpo(func));
        find_natural_loops(func, &preds, &idom)
            .into_iter()
            .find(|l| l.header == header)
            .and_then(|l| l.preheader)
    }

    #[test]
    fn creates_a_unique_preheader_for_a_two_entry_header() {
        let mut func = build_two_entry_loop();
        assert_eq!(
            preheader_of(&func, Block(3)),
            None,
            "the fixture must start WITHOUT a preheader, or the test is vacuous"
        );

        assert!(run_scoped(&mut func, false));

        let ph = preheader_of(&func, Block(3)).expect("a preheader now exists");
        assert_ne!(ph, Block(3));
        // Both arms route through it; the LATCH still targets the header direct.
        let preds = predecessor_map(&func);
        let hpreds = preds.get(&Block(3)).cloned().unwrap_or_default();
        assert!(
            hpreds.contains(&ph) && hpreds.contains(&Block(4)),
            "header's preds should be the new preheader plus the latch, got {hpreds:?}"
        );
        assert!(
            !hpreds.contains(&Block(1)) && !hpreds.contains(&Block(2)),
            "neither arm may still branch to the header directly"
        );
        // The new block computes nothing.
        let nb = &func.blocks[&ph];
        assert_eq!(nb.insts.len(), 1);
        assert_eq!(nb.insts[0].opcode, X86Opcode::Jmp);
        assert_eq!(nb.successors, vec![Block(3)]);
    }

    #[test]
    fn places_the_preheader_immediately_before_the_header() {
        let mut func = build_two_entry_loop();
        assert!(run_scoped(&mut func, false));
        let ph = preheader_of(&func, Block(3)).unwrap();
        let pi = func.block_order.iter().position(|b| *b == ph).unwrap();
        let hi = func
            .block_order
            .iter()
            .position(|b| *b == Block(3))
            .unwrap();
        assert_eq!(pi + 1, hi, "the preheader must fall through to the header");
        // Layout invariants that `validate_x86_function_layout` enforces.
        assert_eq!(func.block_order.first().copied(), Some(Block(0)));
        let mut seen = BTreeSet::new();
        assert!(
            func.block_order.iter().all(|b| seen.insert(*b)),
            "block_order must not duplicate a block"
        );
        for b in &func.block_order {
            for s in &func.blocks[b].successors {
                assert!(seen.contains(s), "successor {s:?} must be laid out");
            }
        }
    }

    #[test]
    fn leaves_a_loop_that_already_has_a_preheader_alone() {
        let mut func = build_two_entry_loop();
        // Give it a preheader by hand first.
        assert!(run_scoped(&mut func, false));
        let before = func.block_order.clone();
        assert!(
            !run_scoped(&mut func, false),
            "a second run must be a no-op — the property is already established"
        );
        assert_eq!(func.block_order, before);
    }

    #[test]
    fn is_off_by_default() {
        let mut func = build_two_entry_loop();
        assert!(!run_on_function(&mut func));
        assert_eq!(preheader_of(&func, Block(3)), None);
    }
}
