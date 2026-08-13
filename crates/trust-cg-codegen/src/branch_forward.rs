// trust-cg-codegen/branch_forward.rs - Post-RA branch forwarding (OPT-8 lever)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Post-register-allocation branch forwarding and dead empty-block removal for
//! AArch64.
//!
//! # The deficit this closes
//!
//! `split_critical_edges` (in `trust-cg-regalloc`) inserts jump-only *trampoline*
//! blocks — a block whose sole instruction is an unconditional `B <target>` —
//! onto critical CFG edges so per-edge Phi copies have somewhere to live. This
//! happens *inside* the allocator, AFTER the last `CfgSimplify` pass could run
//! (Phis are still live there), so the empty-block cleanup never sees them.
//! `post_ra_coalesce` then deletes the trampolines' Phi copies, leaving blocks
//! that are *truly empty* except for the trailing jump. Any hot-loop back-edge
//! that was a critical edge therefore pays TWO taken branches per iteration:
//! `<latch> B <trampoline>; <trampoline> B <header>`.
//!
//! The encoder already elides a `B` to the *layout-next* block, but a trampoline
//! reached by a back-edge is not layout-next to its predecessor, so that elision
//! does not fire. This pass performs the missing transform: it retargets every
//! branch whose target is a pure trampoline directly at the trampoline's
//! ultimate destination, then drops the now-unreachable trampolines from the
//! layout.
//!
//! # Why it is validator-safe by construction
//!
//! The only mutation to live (laid-out) code is a *branch-target rewrite*: a
//! `Block(T)` operand of a direct branch becomes `Block(resolve(T))`, where
//! `resolve(T)` is the block `T`'s jump ultimately transfers to. No register is
//! read or written differently, no instruction is added to or removed from any
//! *reachable* block, and control flow is preserved edge-for-edge (a jump to a
//! block that only jumps onward is the same transfer as jumping onward
//! directly). Successor/predecessor metadata is rebuilt afterwards from the
//! canonical [`crate::pipeline::derive_ir_cfg_edges_from_branch_operands`], the
//! exact function the post-RA CFG validator checks against, so the rewritten
//! stream stays consistent with the always-on authority.
//!
//! # What is preserved untouched
//!
//! * **Jump-table / indirect targets.** A dense switch reaches its case blocks
//!   through a data-driven `Br`, recorded on `jump_tables[..].targets`, not as a
//!   `Block` operand. Those targets are never rewritten (there is no operand to
//!   rewrite) and are held in the protected set so a trampoline that is *also* a
//!   jump-table target is never removed from the layout.
//! * **Exception-handling structure.** Landing pads and protected call blocks
//!   are likewise protected from removal.
//! * **Jump cycles.** A trampoline that (transitively) jumps back to itself is a
//!   genuine infinite loop; `resolve` detects the cycle and leaves such branches
//!   exactly as they were.

use std::collections::{BTreeMap, BTreeSet};

use trust_cg_ir::{AArch64Opcode, BlockId, MachFunction, MachOperand};

/// Outcome of one [`forward_post_ra_branches`] run.
#[derive(Debug, Default, Clone, Copy)]
pub struct BranchForwardStats {
    /// Number of individual branch-operand retargets performed.
    pub branches_forwarded: u32,
    /// Number of now-unreachable trampoline blocks dropped from `block_order`.
    pub trampolines_removed: u32,
}

impl BranchForwardStats {
    /// True iff the pass altered the function in any way.
    pub fn changed(&self) -> bool {
        self.branches_forwarded > 0 || self.trampolines_removed > 0
    }
}

/// Return the single unconditional-jump destination of `block` iff `block` is a
/// *pure forwarding trampoline*: it is not the entry block, and its only
/// non-`Nop` instruction is an `AArch64Opcode::B` carrying exactly one `Block`
/// operand and nothing else.
///
/// Rigorous emptiness check: any second real instruction, any non-`Block`
/// operand, a conditional/indirect terminator, or a symbol/tail-call `B` (which
/// has a `Symbol` operand, not a `Block`) all disqualify the block. `Nop`
/// filler (the only genuinely effect-free instruction) is ignored.
fn trampoline_target(func: &MachFunction, block: BlockId) -> Option<BlockId> {
    if block == func.entry {
        return None;
    }
    let mut target: Option<BlockId> = None;
    for &inst_id in &func.block(block).insts {
        let inst = func.inst(inst_id);
        if inst.opcode == AArch64Opcode::Nop {
            continue;
        }
        if target.is_some() {
            // A second real instruction: this block does work, not just jump.
            return None;
        }
        if inst.opcode != AArch64Opcode::B || inst.operands.len() != 1 {
            return None;
        }
        match inst.operands[0] {
            MachOperand::Block(t) => target = Some(t),
            _ => return None,
        }
    }
    target
}

/// True iff `opcode` is a direct branch whose `Block` operands are real,
/// forwardable control-transfer targets.
///
/// Deliberately excludes:
/// * `TailCall` — its `Block`/`Symbol` operand is a call destination, not a
///   local edge to collapse;
/// * `Br` — indirect (register / jump-table) dispatch, carries no `Block`
///   operand to rewrite;
/// * every `Trap*` guard pseudo — cold, structurally special, and not yet
///   expanded at this stage.
fn is_forwardable_branch(opcode: AArch64Opcode) -> bool {
    matches!(
        opcode,
        AArch64Opcode::B
            | AArch64Opcode::BCond
            | AArch64Opcode::Bcc
            | AArch64Opcode::Cbz
            | AArch64Opcode::Cbnz
            | AArch64Opcode::Tbz
            | AArch64Opcode::Tbnz
    )
}

/// Follow the trampoline chain from `start` to the first non-trampoline block.
///
/// `tramp` maps each pure-trampoline block to the block its jump targets.
/// Terminates on a jump cycle (a trampoline that transitively jumps back to an
/// already-visited block) by returning `start` unchanged — such a chain is an
/// infinite loop and must not be "collapsed" past its entry.
fn resolve_target(start: BlockId, tramp: &BTreeMap<BlockId, BlockId>) -> BlockId {
    let mut visited: BTreeSet<BlockId> = BTreeSet::new();
    let mut cur = start;
    loop {
        match tramp.get(&cur) {
            // Not a trampoline: the ultimate destination.
            None => return cur,
            Some(&next) => {
                if !visited.insert(cur) {
                    // Revisited a block: the chain cycles. Leave the original
                    // target in place (the program's infinite loop is intended).
                    return start;
                }
                cur = next;
            }
        }
    }
}

/// The set of blocks that must never be dropped from the layout even when they
/// become unreachable through explicit `Block` operands: jump-table targets
/// (reached by the data-driven indirect branch) and every EH landing pad /
/// protected call block.
fn protected_blocks(func: &MachFunction) -> BTreeSet<BlockId> {
    let mut protected = BTreeSet::new();
    for table in &func.jump_tables {
        for &target in &table.targets {
            protected.insert(target);
        }
    }
    for pad in &func.eh_metadata.landing_pads {
        protected.insert(pad.block);
    }
    for call_site in &func.eh_metadata.call_sites {
        protected.insert(call_site.call_block);
        if let Some(pad) = call_site.landing_pad_block {
            protected.insert(pad);
        }
    }
    protected
}

/// Blocks reachable from the entry over `edges` (a directed edge list).
fn reachable_from_entry(func: &MachFunction, edges: &[(BlockId, BlockId)]) -> BTreeSet<BlockId> {
    let mut adjacency: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
    for &(from, to) in edges {
        adjacency.entry(from).or_default().push(to);
    }
    let mut seen: BTreeSet<BlockId> = BTreeSet::new();
    let mut stack = vec![func.entry];
    seen.insert(func.entry);
    while let Some(block) = stack.pop() {
        if let Some(succs) = adjacency.get(&block) {
            for &succ in succs {
                if seen.insert(succ) {
                    stack.push(succ);
                }
            }
        }
    }
    seen
}

/// Forward every direct branch through empty jump-only trampolines to fixpoint,
/// then drop the trampolines that this leaves unreachable.
///
/// Operates on the post-regalloc, post-copy-coalesce `MachFunction` (where phi
/// trampolines are already reduced to a lone `B`). Returns statistics; the
/// caller re-derives CFG metadata only when [`BranchForwardStats::changed`] so a
/// function with no trampolines is left byte-identical.
pub fn forward_post_ra_branches(func: &mut MachFunction) -> BranchForwardStats {
    let mut stats = BranchForwardStats::default();
    if func.block_order.len() < 2 {
        return stats;
    }

    // 1. Catalogue every pure trampoline and the block it jumps to.
    let mut tramp: BTreeMap<BlockId, BlockId> = BTreeMap::new();
    for &block_id in &func.block_order {
        if let Some(target) = trampoline_target(func, block_id) {
            tramp.insert(block_id, target);
        }
    }
    if tramp.is_empty() {
        return stats;
    }

    // 2. Retarget every forwardable branch operand at its ultimate destination.
    //    `resolve_target` collapses the whole chain in one call, so a single
    //    sweep reaches the fixpoint; the outer loop makes that explicit and is
    //    robust to any future single-step resolver.
    loop {
        let mut progressed = false;
        for block_id in func.block_order.clone() {
            for inst_id in func.block(block_id).insts.clone() {
                if !is_forwardable_branch(func.inst(inst_id).opcode) {
                    continue;
                }
                let operand_count = func.inst(inst_id).operands.len();
                for operand_idx in 0..operand_count {
                    let MachOperand::Block(target) = func.inst(inst_id).operands[operand_idx]
                    else {
                        continue;
                    };
                    if !tramp.contains_key(&target) {
                        continue;
                    }
                    let resolved = resolve_target(target, &tramp);
                    if resolved != target {
                        func.inst_mut(inst_id).operands[operand_idx] = MachOperand::Block(resolved);
                        stats.branches_forwarded += 1;
                        progressed = true;
                    }
                }
            }
        }
        if !progressed {
            break;
        }
    }

    if stats.branches_forwarded == 0 {
        // Every trampoline is reached only through paths we do not rewrite
        // (jump table, EH, or a cycle). Leave the function untouched.
        return stats;
    }

    // 3. Retire the trampolines the rewrite left unreachable. Reachability is
    //    taken over the canonical post-rewrite CFG (branch operands + jump-table
    //    + EH + fall-through), so a trampoline still reached by an un-rewritten
    //    edge (a jump-table dispatch or a live fall-through) stays reachable and
    //    is kept. Protected blocks are never retired.
    //
    //    Each retired block is (a) dropped from `block_order` so O1 — where the
    //    later reorder pass does not run — never lays it out, AND (b) emptied of
    //    its lone jump. Emptying remains defensive for callers that retain the
    //    block in an executable order snapshot; `compute_block_layout` itself
    //    now preserves the existing executable domain and will not resurrect a
    //    shell already detached from `block_order`. BlockId is never renumbered
    //    (jump tables index the arena), so the block stays as an inert shell.
    let edges = crate::pipeline::derive_ir_cfg_edges_from_branch_operands(func);
    let reachable = reachable_from_entry(func, &edges);
    let protected = protected_blocks(func);
    let removable: BTreeSet<BlockId> = tramp
        .keys()
        .copied()
        .filter(|block| {
            *block != func.entry && !reachable.contains(block) && !protected.contains(block)
        })
        .collect();
    if !removable.is_empty() {
        for &block in &removable {
            func.block_mut(block).insts.clear();
        }
        func.block_order.retain(|block| !removable.contains(block));
        stats.trampolines_removed = removable.len() as u32;
    }

    // 4. Re-derive succ/pred metadata from the final layout so it matches the
    //    rewritten branch operands exactly (the post-RA CFG validator checks
    //    against this same derivation).
    let final_edges = crate::pipeline::derive_ir_cfg_edges_from_branch_operands(func);
    crate::pipeline::install_ir_cfg_edges(func, final_edges);

    stats
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::function::JumpTableData;
    use trust_cg_ir::{MachInst, Signature};

    /// Build a `B target` branch instruction.
    fn jump(func: &mut MachFunction, target: BlockId) -> trust_cg_ir::InstId {
        func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(target)],
        ))
    }

    /// Build a two-target `BCond taken, not_taken` instruction.
    fn cond(func: &mut MachFunction, taken: BlockId, not_taken: BlockId) -> trust_cg_ir::InstId {
        func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(taken), MachOperand::Block(not_taken)],
        ))
    }

    fn ret(func: &mut MachFunction) -> trust_cg_ir::InstId {
        func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]))
    }

    /// Recompute succ/pred edges the way the pipeline seeds them before regalloc
    /// so hand-built fixtures start out consistent.
    fn install_edges(func: &mut MachFunction) {
        let edges = crate::pipeline::derive_ir_cfg_edges_from_branch_operands(func);
        crate::pipeline::install_ir_cfg_edges(func, edges);
    }

    /// The trailing `Block` operands actually carried by a block's branch.
    fn block_targets(func: &MachFunction, block: BlockId) -> Vec<BlockId> {
        func.block(block)
            .insts
            .iter()
            .flat_map(|&id| func.inst(id).operands.clone())
            .filter_map(|op| match op {
                MachOperand::Block(b) => Some(b),
                _ => None,
            })
            .collect()
    }

    /// Single-target conditional branch `BCond Block(target)`, matching the real
    /// post-ISel AArch64 shape where the not-taken path is the layout
    /// fall-through rather than an explicit second operand.
    fn cond1(func: &mut MachFunction, target: BlockId) -> trust_cg_ir::InstId {
        func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(target)],
        ))
    }

    #[test]
    fn cond_branch_forwards_through_trampoline() {
        // entry: BCond tramp (taken) / fall through to mid ; mid: ret ;
        // tramp: B target ; target: ret. Layout [entry, mid, tramp, target].
        let mut f = MachFunction::new("fwd".into(), Signature::new(vec![], vec![]));
        let entry = f.entry;
        let mid = f.create_block();
        let tramp = f.create_block();
        let target = f.create_block();

        let i = cond1(&mut f, tramp);
        f.append_inst(entry, i);
        let i = ret(&mut f);
        f.append_inst(mid, i);
        let i = jump(&mut f, target); // the trampoline: only a jump
        f.append_inst(tramp, i);
        let i = ret(&mut f);
        f.append_inst(target, i);
        install_edges(&mut f);

        let stats = forward_post_ra_branches(&mut f);
        assert_eq!(stats.branches_forwarded, 1, "the taken edge retargets");
        // entry now branches straight to target, skipping the trampoline.
        assert_eq!(block_targets(&f, entry), vec![target]);
        // trampoline is now unreachable and dropped from the layout.
        assert_eq!(stats.trampolines_removed, 1);
        assert!(!f.block_order.contains(&tramp));
        // The retired trampoline is emptied so a later block-layout re-append
        // cannot re-materialize its dead jump as encoded bytes.
        assert!(f.block(tramp).insts.is_empty());
        // succ/pred metadata reflects the new edge (and the fall-through to mid).
        assert!(f.block(entry).succs.contains(&target));
        assert!(f.block(entry).succs.contains(&mid));
        assert!(f.block(target).preds.contains(&entry));
        assert!(!f.block(target).preds.contains(&tramp));
    }

    #[test]
    fn chain_of_trampolines_collapses() {
        // entry: B a ; a: B b ; b: B c ; c: ret. a and b are trampolines; entry
        // is excluded (it is the entry block). The unconditional B out of entry
        // means no fall-through keeps a/b alive.
        let mut f = MachFunction::new("chain".into(), Signature::new(vec![], vec![]));
        let entry = f.entry;
        let a = f.create_block();
        let b = f.create_block();
        let c = f.create_block();

        let i = jump(&mut f, a);
        f.append_inst(entry, i);
        let i = jump(&mut f, b);
        f.append_inst(a, i);
        let i = jump(&mut f, c);
        f.append_inst(b, i);
        let i = ret(&mut f);
        f.append_inst(c, i);
        install_edges(&mut f);

        let stats = forward_post_ra_branches(&mut f);
        // entry's `a` target collapses A->B->C down to C in a single resolve,
        // and a's own `b` target collapses to c too.
        assert_eq!(block_targets(&f, entry), vec![c]);
        assert_eq!(stats.branches_forwarded, 2);
        // Both trampolines are unreachable afterwards.
        assert_eq!(stats.trampolines_removed, 2);
        assert!(!f.block_order.contains(&a));
        assert!(!f.block_order.contains(&b));
        assert!(f.block_order.contains(&c));
        assert!(f.block(a).insts.is_empty());
        assert!(f.block(b).insts.is_empty());
    }

    #[test]
    fn self_loop_trampoline_is_left_alone() {
        // entry: BCond loop, exit ; loop: B loop (self-jump) ; exit: ret.
        let mut f = MachFunction::new("selfloop".into(), Signature::new(vec![], vec![]));
        let entry = f.entry;
        let loop_b = f.create_block();
        let exit = f.create_block();

        let i = cond(&mut f, loop_b, exit);
        f.append_inst(entry, i);
        let i = jump(&mut f, loop_b); // jumps to itself: an infinite loop
        f.append_inst(loop_b, i);
        let i = ret(&mut f);
        f.append_inst(exit, i);
        install_edges(&mut f);

        let stats = forward_post_ra_branches(&mut f);
        assert!(
            !stats.changed(),
            "a self-looping trampoline must be untouched"
        );
        assert_eq!(block_targets(&f, entry), vec![loop_b, exit]);
        assert!(f.block_order.contains(&loop_b));
    }

    #[test]
    fn two_block_cycle_is_left_alone() {
        // entry: BCond a, exit ; a: B b ; b: B a ; exit: ret. a<->b cycle.
        let mut f = MachFunction::new("cycle".into(), Signature::new(vec![], vec![]));
        let entry = f.entry;
        let a = f.create_block();
        let b = f.create_block();
        let exit = f.create_block();

        let i = cond(&mut f, a, exit);
        f.append_inst(entry, i);
        let i = jump(&mut f, b);
        f.append_inst(a, i);
        let i = jump(&mut f, a);
        f.append_inst(b, i);
        let i = ret(&mut f);
        f.append_inst(exit, i);
        install_edges(&mut f);

        let stats = forward_post_ra_branches(&mut f);
        assert!(!stats.changed(), "a 2-block jump cycle must be untouched");
        assert_eq!(block_targets(&f, entry), vec![a, exit]);
        assert!(f.block_order.contains(&a));
        assert!(f.block_order.contains(&b));
    }

    #[test]
    fn jump_table_target_trampoline_is_preserved() {
        // A trampoline that is BOTH a jump-table target AND reached by a normal
        // branch: the normal branch forwards through it, but the block stays in
        // the layout because the jump table still dispatches to it.
        let mut f = MachFunction::new("jt".into(), Signature::new(vec![], vec![]));
        let entry = f.entry;
        let dispatch = f.create_block();
        let tramp = f.create_block();
        let real = f.create_block();
        let other = f.create_block();

        // entry: BCond dispatch, tramp  (normal branch to the trampoline)
        let i = cond(&mut f, dispatch, tramp);
        f.append_inst(entry, i);
        // dispatch: Adr x0, JumpTableIndex(0) ; Br x0
        let adr = f.push_inst(MachInst::new(
            AArch64Opcode::Adr,
            vec![MachOperand::JumpTableIndex(0)],
        ));
        f.append_inst(dispatch, adr);
        let br = f.push_inst(MachInst::new(AArch64Opcode::Br, vec![]));
        f.append_inst(dispatch, br);
        // tramp: B real   (a pure trampoline, but a jump-table target)
        let i = jump(&mut f, real);
        f.append_inst(tramp, i);
        let i = ret(&mut f);
        f.append_inst(real, i);
        let i = ret(&mut f);
        f.append_inst(other, i);

        f.jump_tables.push(JumpTableData {
            min_val: 0,
            targets: vec![tramp, other],
        });
        install_edges(&mut f);

        let stats = forward_post_ra_branches(&mut f);
        // The entry's not-taken edge to the trampoline is forwarded to `real`.
        assert_eq!(stats.branches_forwarded, 1);
        assert_eq!(block_targets(&f, entry), vec![dispatch, real]);
        // But the trampoline is a jump-table target, so it is NOT removed.
        assert_eq!(stats.trampolines_removed, 0);
        assert!(f.block_order.contains(&tramp));
        // The jump-table edge dispatch -> tramp survives.
        assert!(f.block(dispatch).succs.contains(&tramp));
    }

    #[test]
    fn forwarding_far_target_stays_relaxable() {
        // A TBZ (imm14, +/-32764 B) reaches a NEAR trampoline whose jump lands
        // on a FAR block (>8191 instructions away). Forwarding the TBZ through
        // the trampoline lengthens its span past the TBZ range, so branch
        // relaxation must then split it (TBZ far -> TBNZ +2 ; B far). Proves the
        // pass composes with the encoder's relaxation on retargeted offsets.
        let mut f = MachFunction::new("far".into(), Signature::new(vec![], vec![]));
        let entry = f.entry;
        let other = f.create_block();
        let tramp = f.create_block();
        let filler = f.create_block();
        let target = f.create_block();

        // entry: TBZ x0, #3, tramp ; fall through to `other`.
        let i = f.push_inst(MachInst::new(
            AArch64Opcode::Tbz,
            vec![
                MachOperand::Imm(0),
                MachOperand::Imm(3),
                MachOperand::Block(tramp),
            ],
        ));
        f.append_inst(entry, i);
        let i = ret(&mut f);
        f.append_inst(other, i);
        // tramp: B target — near trampoline whose destination is far.
        let i = jump(&mut f, target);
        f.append_inst(tramp, i);
        // filler: enough real instructions to push `target` out of TBZ range.
        for _ in 0..9000 {
            let a = f.push_inst(MachInst::new(AArch64Opcode::AddRI, vec![]));
            f.append_inst(filler, a);
        }
        let i = ret(&mut f);
        f.append_inst(target, i);
        install_edges(&mut f);

        let relaxer = crate::relax::BranchRelaxation::new();
        // Before forwarding, the TBZ reaches the near trampoline: in range.
        assert!(!relaxer.has_out_of_range_branches(&f).unwrap());

        let stats = forward_post_ra_branches(&mut f);
        assert_eq!(stats.branches_forwarded, 1);
        // The TBZ now targets the far block: out of TBZ's imm14 window.
        assert!(
            relaxer.has_out_of_range_branches(&f).unwrap(),
            "forwarding must have lengthened the TBZ span past its range"
        );

        // Relaxation resolves the retargeted branch without error, and no branch
        // remains out of range afterward.
        crate::relax::relax_branches(&mut f).expect("relaxation must handle the retargeted span");
        assert!(!relaxer.has_out_of_range_branches(&f).unwrap());
    }

    #[test]
    fn function_without_trampolines_is_untouched() {
        let mut f = MachFunction::new("plain".into(), Signature::new(vec![], vec![]));
        let entry = f.entry;
        let body = f.create_block();
        let i = cond(&mut f, body, body);
        f.append_inst(entry, i);
        let add = f.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                MachOperand::Imm(0),
                MachOperand::Imm(0),
                MachOperand::Imm(1),
            ],
        ));
        f.append_inst(body, add);
        let i = ret(&mut f);
        f.append_inst(body, i);
        install_edges(&mut f);

        let before = f.block_order.clone();
        let stats = forward_post_ra_branches(&mut f);
        assert!(!stats.changed());
        assert_eq!(f.block_order, before);
    }
}
