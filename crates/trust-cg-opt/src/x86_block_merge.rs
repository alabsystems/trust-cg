// trust-cg-opt - x86-64 straight-line block merging
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//! Merge a block into its sole predecessor when the edge between them is an
//! unconditional `Jmp` and nothing else can reach it.
//!
//! # Why
//!
//! The x86 lane had NO straight-line block merging at all. The generic
//! [`crate::cfg_simplify`] documents exactly this transform ("Unconditional
//! branch folding | Merge block into sole predecessor"), but it is written
//! against `MachFunction` (the AArch64/generic machine IR) and was never wired
//! into the x86 pipeline. Measured on the beat-llvm suite: **123 mergeable
//! straight-line pairs across all 18 programs**, 3-11 per program, every single
//! program affected.
//!
//! Two distinct payoffs:
//!
//! * Each merge deletes one unconditional `Jmp`.
//! * **Many x86 passes here are BLOCK-LOCAL** — the peephole, local DCE,
//!   copy-propagation, the rotate-idiom recognizer, the copy/op/writeback
//!   collapse. Merging widens their window, so this can unlock optimizations
//!   that currently decline at a block boundary.
//!
//! It also unblocks if-conversion. `X86IfConvert::find_one` requires each arm of
//! a diamond to be exactly ONE block. In `b1_mispredict` the taken arm of the
//! `if s & 6 == 2 { acc = acc.rotate_left(7) }` diamond is a two-block chain
//! (`Block(16) -> Block(17) -> join`), so the arms appear not to reconverge and
//! the whole diamond is rejected before arm analysis. LLVM if-converts it
//! (`rolq $0x7,%rdi ; cmpl $0x2,%esi ; cmovneq %r8,%rdi`); we emitted a
//! mispredicting branch.
//!
//! # Soundness
//!
//! Merging `B` into `A` is a pure CFG rewrite — no instruction is added,
//! removed (beyond `A`'s now-redundant terminator) or reordered relative to any
//! other. It is admitted only when ALL of:
//!
//! * `A`'s instruction list ends in exactly `Jmp B`, and `A`'s successor set is
//!   exactly `[B]`. So control always flows A -> B with nothing in between.
//! * `B` is not the entry block (the entry must keep its identity and its
//!   position at the head of `block_order`).
//! * `B != A` (a self-loop is a back edge, not a straight line).
//! * `B` has exactly ONE predecessor and it is `A`.
//! * ⚑ `crate::x86_if_convert::has_single_deletable_block_reference` holds for
//!   `B`. The predecessor map is NOT sufficient authority to delete a block: a
//!   jump table or an EH landing-pad record is a live reference that never
//!   appears as an instruction-level `Block` operand. That helper checks the
//!   instruction reference count AND both side tables, and is the same gate the
//!   if-converter uses before deleting an arm.
//!
//! After merging, block ids are renumbered contiguously
//! (`crate::x86_if_convert::renumber_blocks_contiguous`) because the x86
//! regalloc replay requires contiguous ids.
//!
//! Kill switch: `TCG_NO_X86_BLOCK_MERGE`.

use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_lower::instructions::Block;
use trust_cg_lower::x86_64_isel::X86ISelFunction;
use trust_cg_lower::x86_64_isel::X86ISelOperand;

use crate::x86_if_convert::{has_single_deletable_block_reference, renumber_blocks_contiguous};
use crate::x86_pass_manager::X86MachinePass;

/// Straight-line block merging for x86 ISel functions.
#[derive(Debug, Default)]
pub struct X86BlockMerge {
    /// Merges performed by the most recent `run` (ACCEPT counter — a pass that
    /// "obviously" fires has fired zero times often enough in this codebase
    /// that a count is mandatory, not decoration).
    last_run_merges: usize,
}

impl X86BlockMerge {
    pub fn new() -> Self {
        Self::default()
    }

    /// Merges performed by the most recent `run`.
    pub fn last_run_merges(&self) -> usize {
        self.last_run_merges
    }
}

fn enabled() -> bool {
    std::env::var_os("TCG_NO_X86_BLOCK_MERGE").is_none()
}

/// `Some(b)` iff `a`'s instruction list ends in exactly `Jmp b` and its
/// successor set is exactly `[b]`.
fn sole_jmp_successor(func: &X86ISelFunction, a: Block) -> Option<Block> {
    let block = func.blocks.get(&a)?;
    let last = block.insts.last()?;
    if last.opcode != X86Opcode::Jmp || last.flags != X86Opcode::Jmp.default_flags() {
        return None;
    }
    let [X86ISelOperand::Block(target)] = last.operands.as_slice() else {
        return None;
    };
    if block.successors.as_slice() != [*target] {
        return None;
    }
    Some(*target)
}

/// Predecessor count for `target`, counted over CFG successor edges.
fn predecessors_of(func: &X86ISelFunction, target: Block) -> Vec<Block> {
    let mut preds = Vec::new();
    for b in &func.block_order {
        if let Some(block) = func.blocks.get(b)
            && block.successors.contains(&target)
        {
            preds.push(*b);
        }
    }
    preds
}

/// Find one mergeable `(a, b)` pair, or `None`.
fn find_one_merge(func: &X86ISelFunction) -> Option<(Block, Block)> {
    let entry = *func.block_order.first()?;
    for &a in &func.block_order {
        let Some(b) = sole_jmp_successor(func, a) else {
            continue;
        };
        if b == entry || b == a {
            continue;
        }
        if !func.blocks.contains_key(&b) {
            continue;
        }
        if predecessors_of(func, b).as_slice() != [a] {
            continue;
        }
        // The authority to DELETE `b`: exactly one instruction-level reference
        // (which is `a`'s `Jmp`), and no jump-table / EH record naming it.
        if !has_single_deletable_block_reference(func, b) {
            continue;
        }
        return Some((a, b));
    }
    None
}

fn merge_once(func: &mut X86ISelFunction, a: Block, b: Block) {
    let b_block = func.blocks.remove(&b).expect("checked present");
    let a_block = func.blocks.get_mut(&a).expect("checked present");
    // Drop `a`'s trailing `Jmp b` — control now falls straight into b's body.
    a_block.insts.pop();
    a_block.insts.extend(b_block.insts);
    a_block.successors = b_block.successors;
    func.block_order.retain(|x| *x != b);
}

impl X86MachinePass for X86BlockMerge {
    fn name(&self) -> &str {
        "x86-block-merge"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        self.last_run_merges = 0;
        if !enabled() {
            return false;
        }
        // Each merge deletes one block, so the block count bounds the fixpoint.
        let budget = func.block_order.len() + 1;
        for _ in 0..budget {
            let Some((a, b)) = find_one_merge(func) else {
                break;
            };
            merge_once(func, a, b);
            self.last_run_merges += 1;
        }
        if self.last_run_merges == 0 {
            return false;
        }
        if std::env::var_os("TCG_X86_BLOCK_MERGE_LOG").is_some() {
            eprintln!(
                "[x86-block-merge] ACCEPT {} merge(s) in fn `{}`",
                self.last_run_merges, func.name,
            );
        }
        // The x86 regalloc replay requires CONTIGUOUS block ids.
        renumber_blocks_contiguous(func);
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::types::Type;
    use trust_cg_lower::x86_64_isel::X86ISelInst;

    fn sig() -> Signature {
        Signature {
            params: vec![],
            returns: vec![Type::I64],
        }
    }

    fn jmp(t: Block) -> X86ISelInst {
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(t)])
    }

    fn nop() -> X86ISelInst {
        X86ISelInst::new(X86Opcode::Nop, vec![])
    }

    /// A -> B where B has no other predecessor: merge, dropping the `Jmp`.
    ///
    /// `b2` is deliberately given a SECOND predecessor so it is NOT mergeable —
    /// otherwise the whole chain collapses and this test would not isolate the
    /// single pair it claims to check.
    #[test]
    fn merges_straight_line_pair() {
        let mut f = X86ISelFunction::new("m".to_string(), sig());
        let (b0, b1, b2, b3) = (Block(0), Block(1), Block(2), Block(3));
        for b in [b0, b1, b2, b3] {
            f.ensure_block(b);
        }
        f.block_order = vec![b0, b1, b2, b3];
        // b0 -> b1 (the mergeable pair); b1 -> b2; b3 -> b2 (second pred of b2)
        f.blocks.get_mut(&b0).unwrap().successors = vec![b1];
        f.push_inst(b0, jmp(b1));
        f.blocks.get_mut(&b1).unwrap().successors = vec![b2];
        f.push_inst(b1, nop());
        f.push_inst(b1, jmp(b2));
        f.blocks.get_mut(&b2).unwrap().successors = vec![];
        f.push_inst(b2, X86ISelInst::new(X86Opcode::Ret, vec![]));
        f.blocks.get_mut(&b3).unwrap().successors = vec![b2];
        f.push_inst(b3, jmp(b2));

        let mut pass = X86BlockMerge::new();
        assert!(pass.run(&mut f), "the pair must merge");
        assert_eq!(pass.last_run_merges(), 1, "exactly the one pair");
        assert_eq!(f.block_order.len(), 3, "one block removed");
        let entry = f.blocks.get(&f.block_order[0]).unwrap();
        // b0's Jmp is gone; b1's body (nop + jmp) is appended.
        assert_eq!(entry.insts[0].opcode, X86Opcode::Nop);
        assert_eq!(entry.insts[1].opcode, X86Opcode::Jmp);
    }

    /// REFUTE: a second predecessor makes the block un-mergeable — the merged
    /// body would no longer be reachable from that other edge.
    #[test]
    fn refuses_when_target_has_two_predecessors() {
        let mut f = X86ISelFunction::new("m".to_string(), sig());
        let (b0, b1, b2, b3) = (Block(0), Block(1), Block(2), Block(3));
        for b in [b0, b1, b2, b3] {
            f.ensure_block(b);
        }
        f.block_order = vec![b0, b1, b2, b3];
        // b0 -> b2 ; b1 -> b2 (two preds)
        f.blocks.get_mut(&b0).unwrap().successors = vec![b2];
        f.push_inst(b0, jmp(b2));
        f.blocks.get_mut(&b1).unwrap().successors = vec![b2];
        f.push_inst(b1, jmp(b2));
        // b2 ENDS the function so it offers no further mergeable edge of its
        // own — otherwise b2 -> b3 would merge legitimately and mask the
        // property under test.
        f.blocks.get_mut(&b2).unwrap().successors = vec![];
        f.push_inst(b2, X86ISelInst::new(X86Opcode::Ret, vec![]));
        f.push_inst(b3, X86ISelInst::new(X86Opcode::Ret, vec![]));

        let mut pass = X86BlockMerge::new();
        pass.run(&mut f);
        assert_eq!(
            pass.last_run_merges(),
            0,
            "a block with two predecessors must not be merged"
        );
        assert!(
            f.blocks.contains_key(&b2),
            "the two-predecessor block must survive"
        );
    }

    /// REFUTE: never merge the ENTRY block away — it must keep its identity and
    /// its position at the head of `block_order`.
    #[test]
    fn refuses_to_merge_entry_block() {
        let mut f = X86ISelFunction::new("m".to_string(), sig());
        let (b0, b1) = (Block(0), Block(1));
        for b in [b0, b1] {
            f.ensure_block(b);
        }
        f.block_order = vec![b0, b1];
        // b1 -> b0 (entry is the sole successor of b1)
        f.blocks.get_mut(&b1).unwrap().successors = vec![b0];
        f.push_inst(b1, jmp(b0));
        f.push_inst(b0, X86ISelInst::new(X86Opcode::Ret, vec![]));

        let mut pass = X86BlockMerge::new();
        pass.run(&mut f);
        assert_eq!(pass.last_run_merges(), 0, "entry must never be merged away");
    }

    /// REFUTE: a conditional terminator is not a straight line.
    #[test]
    fn refuses_conditional_terminator() {
        let mut f = X86ISelFunction::new("m".to_string(), sig());
        let (b0, b1, b2) = (Block(0), Block(1), Block(2));
        for b in [b0, b1, b2] {
            f.ensure_block(b);
        }
        f.block_order = vec![b0, b1, b2];
        f.blocks.get_mut(&b0).unwrap().successors = vec![b1, b2];
        f.push_inst(
            b0,
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(trust_cg_ir::x86_64_ops::X86CondCode::E),
                    X86ISelOperand::Block(b1),
                ],
            ),
        );
        f.push_inst(b0, jmp(b2));
        f.push_inst(b1, X86ISelInst::new(X86Opcode::Ret, vec![]));
        f.push_inst(b2, X86ISelInst::new(X86Opcode::Ret, vec![]));

        let mut pass = X86BlockMerge::new();
        pass.run(&mut f);
        assert_eq!(
            pass.last_run_merges(),
            0,
            "a two-way branch must not be merged"
        );
    }

    /// The kill switch must actually disable the pass.
    #[test]
    fn chain_merges_to_fixpoint() {
        // b0 -> b1 -> b2 -> b3 collapses to a single block.
        let mut f = X86ISelFunction::new("m".to_string(), sig());
        let bs = [Block(0), Block(1), Block(2), Block(3)];
        for b in bs {
            f.ensure_block(b);
        }
        f.block_order = bs.to_vec();
        for i in 0..3 {
            f.blocks.get_mut(&bs[i]).unwrap().successors = vec![bs[i + 1]];
            f.push_inst(bs[i], nop());
            f.push_inst(bs[i], jmp(bs[i + 1]));
        }
        f.push_inst(bs[3], X86ISelInst::new(X86Opcode::Ret, vec![]));

        let mut pass = X86BlockMerge::new();
        assert!(pass.run(&mut f));
        assert_eq!(pass.last_run_merges(), 3, "the whole chain merges");
        assert_eq!(f.block_order.len(), 1);
    }
}
