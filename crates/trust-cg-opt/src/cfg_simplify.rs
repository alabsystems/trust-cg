// trust-cg-opt - CFG Simplification
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! CFG simplification / branch folding pass for machine-level IR.
//!
//! Simplifies the control flow graph by eliminating unnecessary branches
//! and blocks. This is a pre-register-allocation pass that runs after DCE.
//!
//! # Transforms
//!
//! | Transform | Description |
//! |-----------|-------------|
//! | Unreachable block removal | Remove blocks not reachable from entry |
//! | Empty block elimination | Redirect predecessors past single-branch blocks |
//! | Branch target simplification | Thread branches through single-jump blocks |
//! | Unconditional branch folding | Merge block into sole predecessor |
//! | Constant branch folding | Convert known-constant conditionals to unconditional |
//! | Duplicate branch elimination | Convert same-target conditionals to unconditional |
//!
//! # Provenance policy
//!
//! Branch operand/opcode rewrites keep the same `InstId` and are recorded as
//! in-place transforms. Instructions removed from layout are recorded as
//! optimized away. Instructions moved unchanged between blocks keep their
//! `InstId`; no `ProvenanceMap` update is needed because provenance is keyed by
//! instruction identity rather than block placement.
//!
//! # Algorithm
//!
//! All six sub-passes are iterated in a single `run()` invocation until no
//! sub-pass reports a change (local fixed point). After any structural CFG
//! modification the predecessor/successor lists are rebuilt from scratch by
//! scanning every terminator for `Block` operands.
//!
//! Reference: LLVM `SimplifyCFG`, `BranchFolding`

use std::collections::{HashMap, HashSet, VecDeque};

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, PassId, ProvenanceMap,
    VReg,
};

use crate::effects::{for_each_inst_def, inst_defines_vreg};
use crate::pass_manager::{AnalysisCache, MachinePass};

/// CFG simplification pass.
pub struct CfgSimplify;

impl MachinePass for CfgSimplify {
    fn name(&self) -> &str {
        "cfg-simplify"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let config = CfgSimplifyConfig::from_env();
        run_cfg_simplify(func, &config)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let config = CfgSimplifyConfig::from_env();
        run_cfg_simplify_with_provenance(func, &config, provenance)
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

#[derive(Debug, Clone, Default)]
struct CfgSimplifyConfig {
    disabled_subpasses: HashSet<String>,
}

impl CfgSimplifyConfig {
    fn from_env() -> Self {
        Self::from_disabled_subpasses(
            &std::env::var("TRUST_CG_DISABLE_CFGSIMPLIFY_SUBPASSES").unwrap_or_default(),
        )
    }

    fn from_disabled_subpasses(disabled: &str) -> Self {
        let disabled_subpasses = disabled
            .split(',')
            .map(str::trim)
            .filter(|name| !name.is_empty())
            .map(str::to_string)
            .collect();
        Self { disabled_subpasses }
    }

    fn disables(&self, name: &str) -> bool {
        self.disabled_subpasses.contains(name)
    }
}

fn run_cfg_simplify(func: &mut MachFunction, config: &CfgSimplifyConfig) -> bool {
    run_cfg_simplify_impl(func, config, None)
}

fn run_cfg_simplify_with_provenance(
    func: &mut MachFunction,
    config: &CfgSimplifyConfig,
    provenance: &mut ProvenanceMap,
) -> bool {
    run_cfg_simplify_impl(func, config, Some(provenance))
}

fn run_cfg_simplify_impl(
    func: &mut MachFunction,
    config: &CfgSimplifyConfig,
    mut provenance: Option<&mut ProvenanceMap>,
) -> bool {
    let mut ever_changed = false;
    // Safety bound to prevent infinite loops if sub-passes oscillate.
    let max_iterations: usize = 32;

    // Iterate sub-passes until fixed point (bounded).
    for _ in 0..max_iterations {
        let mut changed = false;

        rebuild_cfg_edges(func);

        if !config.disables("unreachable") {
            changed |= remove_unreachable_blocks(func, provenance.as_deref_mut());
        }
        rebuild_cfg_edges(func);

        if !config.disables("empty-blocks") {
            changed |= eliminate_empty_blocks(func, provenance.as_deref_mut());
        }
        rebuild_cfg_edges(func);

        if !config.disables("branch-targets") {
            changed |= simplify_branch_targets(func, provenance.as_deref_mut());
        }
        rebuild_cfg_edges(func);

        if !config.disables("uncond-fold") {
            changed |= fold_unconditional_branches(func, provenance.as_deref_mut());
        }
        rebuild_cfg_edges(func);

        if !config.disables("const-fold") {
            changed |= fold_constant_branches(func, provenance.as_deref_mut());
        }
        rebuild_cfg_edges(func);

        if !config.disables("dominated-zero") {
            changed |= resolve_dominated_zero_tests(func, provenance.as_deref_mut());
        }
        rebuild_cfg_edges(func);

        if !config.disables("dup-branches") {
            changed |= eliminate_duplicate_branches(func, provenance.as_deref_mut());
        }
        rebuild_cfg_edges(func);

        if changed {
            ever_changed = true;
        } else {
            break;
        }
    }

    ever_changed
}

fn cfg_simplify_pass_id() -> PassId {
    PassId::new("cfg-simplify")
}

// ---------------------------------------------------------------------------
// CFG edge reconstruction
// ---------------------------------------------------------------------------

/// Blocks referenced by the function's exception-handling metadata: invoke
/// call-site blocks and landing-pad blocks.
///
/// These are structural anchors for the LSDA: after layout,
/// `resolve_eh_offsets` maps them to byte offsets, so CFG transforms must
/// neither drop them from `block_order` nor merge foreign code into a
/// protected call-site range (that would put unrelated calls under the pad —
/// a semantic change, not a cleanup). Empty for non-EH functions, so all
/// guards keyed on this set are no-ops on the common path.
fn eh_referenced_blocks(func: &MachFunction) -> HashSet<BlockId> {
    let mut set = HashSet::new();
    for pad in &func.eh_metadata.landing_pads {
        set.insert(pad.block);
    }
    for call_site in &func.eh_metadata.call_sites {
        set.insert(call_site.call_block);
        if let Some(pad) = call_site.landing_pad_block {
            set.insert(pad);
        }
    }
    set
}

/// Rebuild all predecessor/successor lists from scratch by scanning
/// every block's terminator instructions for `Block` operands and
/// inferring fallthrough edges for conditional branches.
fn rebuild_cfg_edges(func: &mut MachFunction) {
    // Clear all edges.
    for block in &mut func.blocks {
        block.preds.clear();
        block.succs.clear();
    }

    // First pass: collect all edges (block_id → target) to avoid borrow conflicts.
    let mut edges: Vec<(BlockId, BlockId)> = Vec::new();
    let order = func.block_order.clone();
    for (layout_idx, &block_id) in order.iter().enumerate() {
        let block = &func.blocks[block_id.0 as usize];
        let Some(&last_inst_id) = block.insts.last() else {
            continue;
        };
        let last_inst = &func.insts[last_inst_id.0 as usize];

        // Collect explicit Block targets from terminators.
        let mut has_explicit_target = false;
        let mut is_unconditional_jump = false;

        for &inst_id in &block.insts {
            let inst = &func.insts[inst_id.0 as usize];
            // Jump-table dispatch: the case/default targets of a dense switch are
            // reachable only through the data-driven indirect `Br`, recorded on
            // `func.jump_tables[idx].targets` rather than as explicit `Block`
            // operands. The block carries an `Adr ..., JumpTableIndex(idx)`. These
            // targets are real CFG successors; without them, unreachable-block
            // removal would drop the case blocks from `block_order` while the
            // jump table still references them, which later fails to encode
            // ("jump table target block has no byte offset"). See defect #5.
            for operand in &inst.operands {
                if let Some(jt_idx) = operand.as_jump_table_index()
                    && let Some(jt) = func.jump_tables.get(jt_idx as usize)
                {
                    for &target in &jt.targets {
                        edges.push((block_id, target));
                    }
                    // The block dispatches through the table; mark it as having
                    // explicit targets. It terminates with an indirect `Br`
                    // (an unconditional branch), so the fallthrough logic below
                    // already suppresses any spurious fallthrough edge.
                    has_explicit_target = true;
                }
            }
            if !inst.is_branch() && !inst.is_terminator() {
                continue;
            }
            for operand in &inst.operands {
                if let MachOperand::Block(target) = operand {
                    edges.push((block_id, *target));
                    has_explicit_target = true;
                }
            }
        }

        // Determine if the block falls through to the next in layout.
        // Unconditional branches (B, Br) and returns (Ret) do NOT fall through.
        // Conditional branches (BCond, Cbz, Cbnz, Tbz, Tbnz) DO fall through.
        if last_inst.is_unconditional_branch() || last_inst.is_return() {
            is_unconditional_jump = true;
        }

        if !is_unconditional_jump && has_explicit_target {
            // Conditional branch: add fallthrough edge to next block in layout.
            if let Some(&next_block) = order.get(layout_idx + 1) {
                edges.push((block_id, next_block));
            }
        }
    }

    // The unwinder transfers control from each protected call site to its
    // landing pad without an encoded branch operand. Without these edges the
    // pad has no predecessors, `remove_unreachable_blocks` drops it from
    // `block_order`, and the fail-closed pipeline validator rejects the
    // function ("laid-out block ... has successor target ... absent from
    // block_order" — the O2 `Invoke` regression). Mirrors the EH seeding in
    // the codegen pipeline's `derive_ir_cfg_edges_from_branch_operands`.
    for call_site in &func.eh_metadata.call_sites {
        if let Some(landing_pad) = call_site.landing_pad_block {
            edges.push((call_site.call_block, landing_pad));
        }
    }

    // Second pass: apply edges, deduplicating.
    for (from, to) in edges {
        if !func.blocks[from.0 as usize].succs.contains(&to) {
            func.blocks[from.0 as usize].succs.push(to);
            func.blocks[to.0 as usize].preds.push(from);
        }
    }
}

// ---------------------------------------------------------------------------
// 1. Unreachable block removal
// ---------------------------------------------------------------------------

/// Remove blocks that are not reachable from the entry block.
fn remove_unreachable_blocks(
    func: &mut MachFunction,
    provenance: Option<&mut ProvenanceMap>,
) -> bool {
    let reachable = compute_reachable(func);

    let removed: Vec<BlockId> = func
        .block_order
        .iter()
        .copied()
        .filter(|bid| !reachable.contains(bid))
        .collect();

    if removed.is_empty() {
        return false;
    }

    if let Some(provenance) = provenance {
        record_block_deletions(
            provenance,
            func,
            &removed,
            "unreachable block removed by cfg-simplify",
        );
    }

    func.block_order.retain(|bid| reachable.contains(bid));
    prune_eh_metadata_for_removed_blocks(func, &reachable);
    true
}

/// EH-metadata lockstep for unreachable-block removal.
///
/// `rebuild_cfg_edges` seeds an unwinder edge call-site -> landing-pad, so a
/// REACHABLE invoke region can never lose its pad here. But a FULLY-unreachable
/// invoke region (the call-site block itself has no path from entry — e.g. its
/// only predecessor edge was constant-folded away) is legitimately pruned from
/// `block_order`, and its `eh_metadata` entries must be dropped in the same
/// step: the fail-closed pipeline validator rejects any function whose
/// `eh_metadata` references a block absent from `block_order` ("exception
/// landing pad targets block ... absent from block_order").
///
/// Only entries anchored on removed blocks are dropped — a call site whose
/// call block survives is kept untouched even if (impossibly, given the edge
/// seeding) its pad died, so a genuine invariant break still fails closed in
/// the validator instead of being silently patched here. When the pruning
/// leaves no landing pads and no call sites, the personality reference is
/// cleared too: an LSDA-less function must not drag a personality symbol into
/// the object.
fn prune_eh_metadata_for_removed_blocks(func: &mut MachFunction, reachable: &HashSet<BlockId>) {
    let eh = &mut func.eh_metadata;
    if eh.landing_pads.is_empty() && eh.call_sites.is_empty() {
        return;
    }

    let before_pads = eh.landing_pads.len();
    let before_sites = eh.call_sites.len();
    eh.call_sites
        .retain(|cs| reachable.contains(&cs.call_block));
    eh.landing_pads.retain(|lp| reachable.contains(&lp.block));

    let pruned = eh.landing_pads.len() != before_pads || eh.call_sites.len() != before_sites;
    if pruned && eh.landing_pads.is_empty() && eh.call_sites.is_empty() {
        eh.personality = None;
    }
}

/// BFS from entry to find all reachable block IDs.
fn compute_reachable(func: &MachFunction) -> HashSet<BlockId> {
    let mut visited = HashSet::new();
    let mut queue = VecDeque::new();

    visited.insert(func.entry);
    queue.push_back(func.entry);

    while let Some(bid) = queue.pop_front() {
        let block = func.block(bid);
        for &succ in &block.succs {
            if visited.insert(succ) {
                queue.push_back(succ);
            }
        }
    }

    visited
}

// ---------------------------------------------------------------------------
// 2. Empty block elimination
// ---------------------------------------------------------------------------

/// If a block contains exactly one instruction — an unconditional `B` — then
/// redirect all predecessors to the target and remove the block from layout.
fn eliminate_empty_blocks(func: &mut MachFunction, provenance: Option<&mut ProvenanceMap>) -> bool {
    let mut changed = false;
    let mut rewritten_insts = Vec::new();

    let jump_map = single_jump_block_map(func);
    let resolved = resolve_chains(&jump_map);

    // Collect candidates: (empty_block, target).
    let candidates: Vec<(BlockId, BlockId)> = func
        .block_order
        .iter()
        .filter_map(|&bid| {
            // Never eliminate the entry block.
            if bid == func.entry {
                return None;
            }
            // Removing a layout fallthrough block changes the semantics of the
            // previous conditional block's not-taken edge. Keep it in layout
            // unless a stronger block-placement pass rewrites that edge.
            if is_layout_fallthrough_target(func, bid) {
                return None;
            }
            resolved.get(&bid).copied().map(|target| (bid, target))
        })
        .collect();

    for (empty_bid, target) in &candidates {
        // Redirect all branch operands that point to empty_bid → target.
        rewritten_insts.extend(redirect_branches(func, *empty_bid, *target));
        changed = true;
    }

    // Redirect JUMP-TABLE targets past the eliminated blocks, in lockstep with
    // the explicit branch operands above.
    //
    // A dense switch's case/default edges are recorded on
    // `func.jump_tables[..].targets` (indexed by the data-driven indirect `Br`),
    // NOT as explicit `Block` operands, so `redirect_branches` above never sees
    // them. An `empty_bid` here is a block whose SOLE instruction is an
    // unconditional `B target`; dispatching to it is identical to dispatching to
    // `target`. When a jump table targets such a block (e.g. a switch case whose
    // block-argument edge-transfer block collapsed to a bare jump once its
    // arg-move copies were coalesced away), the entry MUST follow the same
    // redirect. Otherwise the target block is dropped from `block_order` while
    // the table still references it, and encoding fails with
    // "jump table target block ... has no byte offset" (the block-argument
    // sibling of defect #5). Because `target` is the chain-resolved final
    // destination (never itself an eliminated single-jump block), a single-step
    // remap is complete.
    if changed && !func.jump_tables.is_empty() {
        let redirect: HashMap<BlockId, BlockId> = candidates.iter().copied().collect();
        for jt in &mut func.jump_tables {
            for t in &mut jt.targets {
                if let Some(&new_target) = redirect.get(t) {
                    *t = new_target;
                }
            }
        }
    }

    // Remove eliminated blocks from layout.
    if changed {
        let removed_blocks: Vec<BlockId> = candidates.iter().map(|(b, _)| *b).collect();
        if let Some(provenance) = provenance {
            record_unique_in_place_transforms(provenance, &mut rewritten_insts);
            record_block_deletions(
                provenance,
                func,
                &removed_blocks,
                "empty jump block removed by cfg-simplify",
            );
        }
        let removed: HashSet<BlockId> = removed_blocks.iter().copied().collect();
        func.block_order.retain(|b| !removed.contains(b));
    }

    changed
}

fn is_layout_fallthrough_target(func: &MachFunction, bid: BlockId) -> bool {
    let Some(pos) = func.block_order.iter().position(|&block| block == bid) else {
        return false;
    };
    let Some(&prev_bid) = pos.checked_sub(1).and_then(|idx| func.block_order.get(idx)) else {
        return false;
    };
    let prev_block = func.block(prev_bid);
    let Some(&last_inst_id) = prev_block.insts.last() else {
        return false;
    };
    let last = func.inst(last_inst_id);
    !last.is_unconditional_branch() && !last.is_return()
}

// ---------------------------------------------------------------------------
// 3. Branch target simplification (thread-through)
// ---------------------------------------------------------------------------

/// If a branch targets a block that contains only a single unconditional `B`,
/// rewrite the branch target to the final destination (thread through).
fn simplify_branch_targets(
    func: &mut MachFunction,
    provenance: Option<&mut ProvenanceMap>,
) -> bool {
    // Build a map of single-jump blocks: block → final target.
    let jump_map = single_jump_block_map(func);

    if jump_map.is_empty() {
        return false;
    }

    // Resolve chains: if A→B→C, resolve A→C.
    let resolved = resolve_chains(&jump_map);

    let mut changed = false;

    // Collect (inst_id, new_operands) pairs to apply after scanning.
    let mut rewrites: Vec<(InstId, Vec<MachOperand>)> = Vec::new();

    for &bid in &func.block_order {
        let block = &func.blocks[bid.0 as usize];
        for &inst_id in &block.insts {
            let inst = &func.insts[inst_id.0 as usize];
            if !inst.is_branch() && !inst.is_terminator() {
                continue;
            }
            let mut inst_changed = false;
            let new_operands: Vec<MachOperand> = inst
                .operands
                .iter()
                .map(|op| {
                    if let MachOperand::Block(target) = op
                        && let Some(&final_target) = resolved.get(target)
                    {
                        inst_changed = true;
                        return MachOperand::Block(final_target);
                    }
                    op.clone()
                })
                .collect();
            if inst_changed {
                rewrites.push((inst_id, new_operands));
            }
        }
    }

    // Apply rewrites.
    let mut rewritten_insts = Vec::new();
    for (inst_id, new_ops) in rewrites {
        func.insts[inst_id.0 as usize].operands = new_ops;
        rewritten_insts.push(inst_id);
        changed = true;
    }

    if let Some(provenance) = provenance
        && !rewritten_insts.is_empty()
    {
        record_unique_in_place_transforms(provenance, &mut rewritten_insts);
    }

    changed
}

fn single_jump_block_map(func: &MachFunction) -> HashMap<BlockId, BlockId> {
    let mut jump_map = HashMap::new();
    // A landing pad is entered by the UNWINDER (via the LSDA), not by a
    // branch: even when its body has collapsed to a bare `B`, it must keep
    // its own layout position, so it can never be an eliminate/thread-through
    // candidate. (Invoke call-site blocks always carry their `Bl`, so the
    // single-instruction filter already excludes them.)
    let eh_blocks = eh_referenced_blocks(func);
    for &bid in &func.block_order {
        if eh_blocks.contains(&bid) {
            continue;
        }
        let block = func.block(bid);
        if block.insts.len() == 1 {
            let inst = func.inst(block.insts[0]);
            if inst.is_unconditional_branch() {
                for op in &inst.operands {
                    if let MachOperand::Block(target) = op
                        && *target != bid
                    {
                        jump_map.insert(bid, *target);
                    }
                }
            }
        }
    }
    jump_map
}

/// Resolve chains in the jump map: if A→B and B→C, produce A→C.
/// Limit chain length to prevent infinite loops on cycles.
fn resolve_chains(jump_map: &HashMap<BlockId, BlockId>) -> HashMap<BlockId, BlockId> {
    let mut resolved = HashMap::new();
    for &src in jump_map.keys() {
        if let Some(target) = resolve_chain_target(jump_map, src) {
            resolved.insert(src, target);
        }
    }
    resolved
}

fn resolve_chain_target(jump_map: &HashMap<BlockId, BlockId>, src: BlockId) -> Option<BlockId> {
    let mut target = *jump_map.get(&src)?;
    let mut seen = HashSet::from([src]);
    let mut depth = 0;

    loop {
        if !seen.insert(target) {
            return None;
        }
        let Some(&next) = jump_map.get(&target) else {
            return Some(target);
        };
        target = next;
        depth += 1;
        if depth > 32 {
            return None;
        }
    }
}

// ---------------------------------------------------------------------------
// 4. Unconditional branch folding (merge single-predecessor blocks)
// ---------------------------------------------------------------------------

/// If block A ends with an unconditional `B` to block B, and B has exactly
/// one predecessor (A), then merge B's instructions into A (removing the
/// trailing `B` from A).
fn fold_unconditional_branches(
    func: &mut MachFunction,
    provenance: Option<&mut ProvenanceMap>,
) -> bool {
    let mut changed = false;
    let mut deleted_tail_branches = Vec::new();

    // We may need multiple passes since merging can create new opportunities.
    // But the outer loop in run() handles this; do one pass here.
    let order = func.block_order.clone();
    let mut merged_away: HashSet<BlockId> = HashSet::new();
    // EH boundary: never merge INTO an invoke call-site block (the merged
    // instructions would land inside the protected PC range and any call
    // among them would wrongly dispatch to this site's landing pad), and
    // never merge a landing pad away (the LSDA references its layout
    // position).
    let eh_blocks = eh_referenced_blocks(func);

    for &block_a in &order {
        if merged_away.contains(&block_a) {
            continue;
        }
        if eh_blocks.contains(&block_a) {
            continue;
        }

        let block = func.block(block_a);
        let Some(&last_inst_id) = block.insts.last() else {
            continue;
        };

        // Check if last instruction is unconditional B.
        let last_inst = func.inst(last_inst_id);
        if !last_inst.is_unconditional_branch() {
            continue;
        }

        // Extract target block.
        let target = match last_inst.operands.iter().find_map(|op| {
            if let MachOperand::Block(bid) = op {
                Some(*bid)
            } else {
                None
            }
        }) {
            Some(t) => t,
            None => continue,
        };

        // Don't merge a block into itself.
        if target == block_a {
            continue;
        }

        // Don't merge the entry block away.
        if target == func.entry {
            continue;
        }

        // Don't merge an EH-referenced block away (see `eh_blocks` above).
        if eh_blocks.contains(&target) {
            continue;
        }

        // This fold physically appends the target block's instructions into
        // block_a. Moving non-adjacent target code is layout-sensitive because
        // branch fallthrough is encoded by instruction order, and downstream
        // layout/regalloc code still assumes labels identify block starts.
        // Keep this optimization to adjacent blocks where removing the target
        // label does not move the target instruction stream.
        if !is_immediately_followed_by(func, block_a, target) {
            continue;
        }

        // If block_a already contains a branch/terminator before its tail B,
        // merging target into block_a creates an internal-control-flow block.
        // Downstream liveness, RA, and codegen still model block labels as the
        // only instruction-stream branch boundaries.
        if has_non_tail_branch_or_terminator(func, block_a, last_inst_id) {
            continue;
        }

        // Target must have exactly one predecessor (block_a).
        let target_preds = func.block(target).preds.clone();
        if target_preds.len() != 1 || target_preds[0] != block_a {
            continue;
        }

        // Keep a real block boundary for latch-style blocks that branch back
        // to their sole predecessor. Merging the latch into the body creates a
        // self-loop with loop-carried copies in the same block; downstream
        // post-RA copy coalescing does not model that edge boundary and can
        // rewrite the backedge values as ordinary same-block temporaries.
        if func.block(target).succs.contains(&block_a) {
            continue;
        }

        // Merge: remove trailing B from A, append B's instructions to A.
        // Target instructions keep the same InstIds while moving blocks, so
        // provenance for those instructions remains valid without rewriting.
        let target_insts = func.block(target).insts.clone();
        let block_a_mut = func.block_mut(block_a);
        block_a_mut.insts.pop(); // Remove trailing B
        block_a_mut.insts.extend(target_insts);
        deleted_tail_branches.push(last_inst_id);

        // Clear target block's instructions.
        func.block_mut(target).insts.clear();

        merged_away.insert(target);
        changed = true;
    }

    // Remove merged blocks from layout.
    if changed {
        if let Some(provenance) = provenance {
            let pass = cfg_simplify_pass_id();
            for inst_id in deleted_tail_branches {
                provenance.record_deletion(
                    inst_id,
                    pass.clone(),
                    "unconditional branch folded into successor block",
                );
            }
        }
        func.block_order.retain(|b| !merged_away.contains(b));
    }

    changed
}

fn is_immediately_followed_by(func: &MachFunction, first: BlockId, second: BlockId) -> bool {
    let Some(first_pos) = func.block_order.iter().position(|&bid| bid == first) else {
        return false;
    };
    func.block_order.get(first_pos + 1).copied() == Some(second)
}

// ---------------------------------------------------------------------------
// 5. Constant branch folding
// ---------------------------------------------------------------------------

/// If a Cbz/Cbnz instruction's condition register is defined by a MovI with
/// a known constant, convert the conditional branch to an unconditional B.
fn fold_constant_branches(func: &mut MachFunction, provenance: Option<&mut ProvenanceMap>) -> bool {
    let mut changed = false;
    let mut rewritten_insts = Vec::new();

    // Scan for Cbz/Cbnz with constant conditions.
    for &bid in &func.block_order.clone() {
        let block = func.block(bid);
        let Some(&last_inst_id) = block.insts.last() else {
            continue;
        };
        let inst = func.inst(last_inst_id);

        // Use generic opcode queries for dispatch; AArch64Opcode::B is
        // still used to construct the replacement unconditional branch.
        let is_cbz = inst.opcode.is_cbz();
        let is_cbnz = inst.opcode.is_cbnz();
        if !is_cbz && !is_cbnz {
            continue;
        }

        if let Some(MachOperand::VReg(cond)) = inst.operands.first()
            && let Some(val) = same_block_constant_def_before(func, bid, last_inst_id, *cond)
            && let Some(target) = find_block_operand(&inst.operands)
        {
            // Determine if the branch is taken based on the constant value.
            let branch_taken = (is_cbz && val == 0) || (is_cbnz && val != 0);

            if branch_taken {
                // Branch IS taken: convert to unconditional B to target.
                *func.inst_mut(last_inst_id) = make_unconditional_branch_rewrite(inst, target);
            } else {
                // Branch NOT taken: convert to unconditional B to fallthrough.
                if let Some(fallthrough) = get_fallthrough(func, bid) {
                    *func.inst_mut(last_inst_id) =
                        make_unconditional_branch_rewrite(inst, fallthrough);
                } else {
                    continue;
                }
            }
            rewritten_insts.push(last_inst_id);
            changed = true;
        }
    }

    if let Some(provenance) = provenance
        && !rewritten_insts.is_empty()
    {
        record_unique_in_place_transforms(provenance, &mut rewritten_insts);
    }

    changed
}

/// Return a same-block constant definition that dominates `before_inst_id`.
///
/// A global vreg->constant map is unsound here: vregs may be redefined on
/// different CFG paths or by later blocks, and those definitions do not
/// necessarily reach this branch. Only the nearest prior definition in the
/// same block is trivially dominating without a reaching-def analysis.
fn same_block_constant_def_before(
    func: &MachFunction,
    block_id: BlockId,
    before_inst_id: InstId,
    vreg: VReg,
) -> Option<i64> {
    let block = func.block(block_id);
    let branch_pos = block.insts.iter().position(|&id| id == before_inst_id)?;
    for &inst_id in block.insts[..branch_pos].iter().rev() {
        let inst = func.inst(inst_id);
        if !inst_defines_vreg(inst, vreg) {
            continue;
        }
        return match inst.opcode {
            AArch64Opcode::MovI => inst.operands.get(1).and_then(|op| {
                if let MachOperand::Imm(value) = op {
                    Some(*value)
                } else {
                    None
                }
            }),
            _ => None,
        };
    }
    None
}

/// Find the first `Block` operand in an operand list.
fn find_block_operand(operands: &[MachOperand]) -> Option<BlockId> {
    operands.iter().find_map(|op| {
        if let MachOperand::Block(bid) = op {
            Some(*bid)
        } else {
            None
        }
    })
}

/// Get the fallthrough block (next in layout order) for a given block.
fn get_fallthrough(func: &MachFunction, bid: BlockId) -> Option<BlockId> {
    let pos = func.block_order.iter().position(|b| *b == bid)?;
    func.block_order.get(pos + 1).copied()
}

/// The zero-ness fact a single CFG edge establishes for a register, read off
/// the predecessor's terminating `Cbz`/`Cbnz`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ZeroFact {
    Zero,
    NonZero,
}

/// Per-function def counts and single-def sites for the zero-test resolver's
/// copy-chain canonicalization (mirrors `aarch64_bounds_check_elim`'s
/// condition 1: single-def, same-class, value-preserving links only).
struct ZeroTestDefs {
    def_count: HashMap<VReg, u32>,
    single_def: HashMap<VReg, (BlockId, usize)>,
}

fn build_zero_test_defs(func: &MachFunction) -> ZeroTestDefs {
    let mut def_count: HashMap<VReg, u32> = HashMap::new();
    let mut single_def: HashMap<VReg, (BlockId, usize)> = HashMap::new();
    for &bid in &func.block_order {
        for (pos, &iid) in func.block(bid).insts.iter().enumerate() {
            let inst = func.inst(iid);
            for_each_inst_def(inst, |d| {
                *def_count.entry(d).or_insert(0) += 1;
                single_def.insert(d, (bid, pos));
            });
        }
    }
    ZeroTestDefs {
        def_count,
        single_def,
    }
}

/// Follow `v` through SINGLE-DEF, SAME-CLASS `MovR`/`Copy` links (bounded) to
/// the first vreg that is multi-def, undefined, or produced by a non-copy —
/// the canonical root. A single-def link's value can never change, so testing
/// any vreg in the chain tests the root's value AT THE LINK'S DEF SITE; the
/// caller must separately prove the root itself is not redefined between the
/// two test sites.
fn zero_test_chain_root(func: &MachFunction, defs: &ZeroTestDefs, mut v: VReg) -> VReg {
    for _ in 0..4 {
        if defs.def_count.get(&v).copied() != Some(1) {
            return v;
        }
        let Some(&(b, pos)) = defs.single_def.get(&v) else {
            return v;
        };
        let Some(&iid) = func.block(b).insts.get(pos) else {
            return v;
        };
        let inst = func.inst(iid);
        if !matches!(inst.opcode, AArch64Opcode::MovR | AArch64Opcode::Copy) {
            return v;
        }
        let Some(src) = inst.operands.get(1).and_then(MachOperand::as_vreg) else {
            return v;
        };
        if src.class != v.class {
            return v;
        }
        v = src;
    }
    v
}

/// The `(register, fact)` established on the edge `d -> p`, if `d`'s
/// terminator is a `Cbz`/`Cbnz` whose taken/fallthrough targets are distinct
/// and one of them is `p`.
fn edge_zero_fact(func: &MachFunction, d: BlockId, p: BlockId) -> Option<(VReg, ZeroFact)> {
    let insts = &func.block(d).insts;
    let (&last_id, rest) = insts.split_last()?;
    let last = func.inst(last_id);
    // The conditional is either the terminator itself (layout fallthrough) or
    // the instruction before a terminating unconditional `B`.
    let (cond, not_taken) = if last.opcode.is_cbz() || last.opcode.is_cbnz() {
        (last, get_fallthrough(func, d)?)
    } else if last.opcode == AArch64Opcode::B {
        let (&cid, _) = rest.split_last()?;
        let c = func.inst(cid);
        if !(c.opcode.is_cbz() || c.opcode.is_cbnz()) {
            return None;
        }
        (c, find_block_operand(&last.operands)?)
    } else {
        return None;
    };
    let taken = find_block_operand(&cond.operands)?;
    if taken == not_taken {
        return None; // ambiguous edge — no fact.
    }
    let Some(MachOperand::VReg(r)) = cond.operands.first() else {
        return None;
    };
    let is_cbz = cond.opcode.is_cbz();
    if p == taken {
        Some((
            *r,
            if is_cbz {
                ZeroFact::Zero
            } else {
                ZeroFact::NonZero
            },
        ))
    } else if p == not_taken {
        Some((
            *r,
            if is_cbz {
                ZeroFact::NonZero
            } else {
                ZeroFact::Zero
            },
        ))
    } else {
        None
    }
}

/// Resolve a `Cbz`/`Cbnz` whose register's zero-ness is already established
/// by the block's SINGLE predecessor edge — the dominated re-test shape the
/// bridge emits for a division-by-zero guard inside a `while b != 0` loop
/// (`cbz b, exit` at the header; `cbnz b, body; bl abort` immediately after:
/// the guard is always-taken, and its abort arm is dead). LLVM elides these;
/// this resolves them to unconditional branches, and the driver's
/// unreachable-block removal then drops the orphaned trap arm.
///
/// Soundness: the block has exactly one predecessor and the fact holds on
/// that edge, so it holds on every entry; the register must have no def in
/// the block before the resolved branch (same conservative same-block
/// discipline as `same_block_constant_def_before` — no cross-block reaching
/// analysis is attempted).
fn resolve_dominated_zero_tests(
    func: &mut MachFunction,
    provenance: Option<&mut ProvenanceMap>,
) -> bool {
    let mut changed = false;
    let mut rewritten_insts = Vec::new();
    let mut remove_after: Vec<(BlockId, InstId)> = Vec::new();
    let defs = build_zero_test_defs(func);

    for &bid in &func.block_order.clone() {
        let block = func.block(bid);
        if block.preds.len() != 1 || block.preds[0] == bid {
            continue;
        }
        let pred = block.preds[0];
        // Locate this block's conditional: terminal, or before a terminal `B`.
        let Some(&last_id) = block.insts.last() else {
            continue;
        };
        let last = func.inst(last_id);
        let (cond_id, trailing_b) = if last.opcode.is_cbz() || last.opcode.is_cbnz() {
            (last_id, None)
        } else if last.opcode == AArch64Opcode::B && block.insts.len() >= 2 {
            let cid = block.insts[block.insts.len() - 2];
            let c = func.inst(cid);
            if c.opcode.is_cbz() || c.opcode.is_cbnz() {
                (cid, Some(last_id))
            } else {
                continue;
            }
        } else {
            continue;
        };
        let cond = func.inst(cond_id);
        let Some(r) = cond.operands.first().and_then(MachOperand::as_vreg) else {
            continue;
        };
        let Some((fact_reg, fact)) = edge_zero_fact(func, pred, bid) else {
            continue;
        };
        // Both tested vregs must canonicalize to the SAME root through
        // single-def copy links (the importer emits a fresh carrier copy per
        // test: `MovR t1, b; cbz t1` at the header, `MovR t2, b; cbnz t2` at
        // the guard).
        let root = zero_test_chain_root(func, &defs, r);
        if zero_test_chain_root(func, &defs, fact_reg) != root {
            continue;
        }
        // The root's value must be provably the same at both test sites.
        // Conservative discipline, no cross-block reaching analysis:
        //  * pred side: the fact-carrying vreg is either the root itself, or
        //    its single def sits in `pred` with no later def of the root in
        //    that block;
        //  * this side: no def of the root (or of the tested vreg) before the
        //    conditional in this block.
        let root_def_positions = |b: BlockId, from: usize, to: usize| -> bool {
            func.block(b).insts[from..to]
                .iter()
                .any(|&id| inst_defines_vreg(func.inst(id), root))
        };
        if fact_reg != root {
            let Some(&(fb, fpos)) = defs.single_def.get(&fact_reg) else {
                continue;
            };
            if fb != pred {
                continue;
            }
            if root_def_positions(pred, fpos + 1, func.block(pred).insts.len()) {
                continue;
            }
        }
        let cond_pos = block.insts.iter().position(|&id| id == cond_id).unwrap();
        if root_def_positions(bid, 0, cond_pos) {
            continue;
        }
        // (No separate check on `r` itself: if `r` is multi-def it IS the
        // root and the root region check above covers it; if single-def, its
        // one def is the value-preserving chain link, whose source value the
        // root checks pin.)
        let taken = (matches!(fact, ZeroFact::Zero) && cond.opcode.is_cbz())
            || (matches!(fact, ZeroFact::NonZero) && cond.opcode.is_cbnz());
        if taken {
            let Some(target) = find_block_operand(&cond.operands) else {
                continue;
            };
            let template = func.inst(cond_id).clone();
            *func.inst_mut(cond_id) = make_unconditional_branch_rewrite(&template, target);
            // Any trailing unconditional `B` is now unreachable — unlink it.
            if let Some(tb) = trailing_b {
                remove_after.push((bid, tb));
            }
        } else {
            // Not taken: control continues past the conditional — unlink it.
            remove_after.push((bid, cond_id));
        }
        rewritten_insts.push(cond_id);
        changed = true;
    }

    for (bid, id) in remove_after {
        func.block_mut(bid).insts.retain(|&iid| iid != id);
    }

    if let Some(provenance) = provenance
        && !rewritten_insts.is_empty()
    {
        record_unique_in_place_transforms(provenance, &mut rewritten_insts);
    }

    changed
}

// ---------------------------------------------------------------------------
// 6. Duplicate branch elimination
// ---------------------------------------------------------------------------

/// If a conditional branch (BCond, Cbz, Cbnz, Tbz, Tbnz) targets the same
/// block for both taken and not-taken (fallthrough), convert to unconditional B.
fn eliminate_duplicate_branches(
    func: &mut MachFunction,
    provenance: Option<&mut ProvenanceMap>,
) -> bool {
    let mut changed = false;
    let mut rewritten_insts = Vec::new();

    for &bid in &func.block_order.clone() {
        let block = func.block(bid);
        let Some(&last_inst_id) = block.insts.last() else {
            continue;
        };
        let inst = func.inst(last_inst_id);

        // Only applies to conditional branches.
        if !inst.is_branch() {
            continue;
        }
        if !inst.is_conditional_branch() {
            continue;
        }

        // Get the taken target (Block operand).
        let taken = match find_block_operand(&inst.operands) {
            Some(t) => t,
            None => continue,
        };

        // Get the fallthrough (not-taken) target.
        let fallthrough = match get_fallthrough(func, bid) {
            Some(ft) => ft,
            None => continue,
        };

        if taken == fallthrough {
            *func.inst_mut(last_inst_id) = make_unconditional_branch_rewrite(inst, taken);
            rewritten_insts.push(last_inst_id);
            changed = true;
        }
    }

    if let Some(provenance) = provenance
        && !rewritten_insts.is_empty()
    {
        record_unique_in_place_transforms(provenance, &mut rewritten_insts);
    }

    changed
}

// ---------------------------------------------------------------------------
// Utility
// ---------------------------------------------------------------------------

/// Redirect all branch operands across the function that target `from` to
/// instead target `to`.
fn redirect_branches(func: &mut MachFunction, from: BlockId, to: BlockId) -> Vec<InstId> {
    let mut rewritten_insts = Vec::new();
    for &bid in &func.block_order.clone() {
        let block = func.block(bid);
        let inst_ids: Vec<InstId> = block.insts.clone();
        for &inst_id in &inst_ids {
            let inst = func.inst(inst_id);
            if !inst.is_branch() && !inst.is_terminator() {
                continue;
            }
            let mut rewritten = false;
            let new_ops: Vec<MachOperand> = inst
                .operands
                .iter()
                .map(|op| {
                    if let MachOperand::Block(target) = op
                        && *target == from
                    {
                        rewritten = true;
                        return MachOperand::Block(to);
                    }
                    op.clone()
                })
                .collect();
            if rewritten {
                func.inst_mut(inst_id).operands = new_ops;
                rewritten_insts.push(inst_id);
            }
        }
    }
    rewritten_insts
}

fn make_unconditional_branch_rewrite(source: &MachInst, target: BlockId) -> MachInst {
    let mut rewritten = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(target)]);
    rewritten.source_loc = source.source_loc;
    rewritten
}

fn record_unique_in_place_transforms(provenance: &mut ProvenanceMap, inst_ids: &mut Vec<InstId>) {
    inst_ids.sort_unstable();
    inst_ids.dedup();
    let pass = cfg_simplify_pass_id();
    for &inst_id in inst_ids.iter() {
        provenance.record_in_place_transform(inst_id, pass.clone());
    }
}

fn record_block_deletions(
    provenance: &mut ProvenanceMap,
    func: &MachFunction,
    block_ids: &[BlockId],
    justification: &'static str,
) {
    let pass = cfg_simplify_pass_id();
    for &block_id in block_ids {
        for &inst_id in &func.block(block_id).insts {
            provenance.record_deletion(inst_id, pass.clone(), justification);
        }
    }
}

fn has_non_tail_branch_or_terminator(
    func: &MachFunction,
    block_id: BlockId,
    tail_inst_id: InstId,
) -> bool {
    let block = func.block(block_id);
    block.insts.iter().any(|&inst_id| {
        if inst_id == tail_inst_id {
            return false;
        }
        let inst = func.inst(inst_id);
        inst.is_branch() || inst.is_terminator()
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pass_manager::{AnalysisCache, MachinePass};
    use std::collections::HashSet;
    use trust_cg_ir::{
        AArch64Opcode, BlockId, CondCode, InstId, MachFunction, MachInst, MachOperand, PassId,
        ProvenanceMap, ProvenanceStatus, RegClass, Signature, SourceLoc, TransformKind,
        TrustIrInstId, VReg,
    };

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn vreg_class(id: u32, class: RegClass) -> MachOperand {
        MachOperand::VReg(VReg::new(id, class))
    }

    fn imm(val: i64) -> MachOperand {
        MachOperand::Imm(val)
    }

    fn block(id: u32) -> MachOperand {
        MachOperand::Block(BlockId(id))
    }

    fn source_loc(line: u32) -> SourceLoc {
        SourceLoc {
            file: 1,
            line,
            col: 7,
        }
    }

    fn assert_block_targets_retained(func: &MachFunction) {
        let retained: HashSet<BlockId> = func.block_order.iter().copied().collect();
        for &bid in &func.block_order {
            let block = func.block(bid);
            for &inst_id in &block.insts {
                let inst = func.inst(inst_id);
                for operand in &inst.operands {
                    if let MachOperand::Block(target) = operand {
                        assert!(
                            retained.contains(target),
                            "block {:?} has {:?} targeting removed block {:?}",
                            bid,
                            inst.opcode,
                            target
                        );
                    }
                }
            }
        }
    }

    fn empty_func() -> MachFunction {
        MachFunction::new("test_cfg".to_string(), Signature::new(vec![], vec![]))
    }

    fn assert_cfg_simplify_survived(provenance: &ProvenanceMap, inst_id: InstId) {
        let entry = provenance
            .get_entry(inst_id)
            .expect("instruction should keep provenance");
        assert!(entry.is_active());
        assert!(
            entry.transforms.iter().any(|record| {
                record.pass == PassId::new("cfg-simplify")
                    && matches!(record.kind, TransformKind::Survived)
            }),
            "expected cfg-simplify in-place transform in {entry:?}"
        );
    }

    fn assert_optimized_away_by_cfg_simplify(
        provenance: &ProvenanceMap,
        inst_id: InstId,
        expected_justification: &str,
    ) {
        let entry = provenance
            .get_entry(inst_id)
            .expect("deleted instruction should keep provenance");
        match &entry.status {
            ProvenanceStatus::OptimizedAway {
                pass,
                justification,
            } => {
                assert_eq!(pass, &PassId::new("cfg-simplify"));
                assert_eq!(justification, expected_justification);
            }
            other => panic!("expected optimized-away provenance, got {other:?}"),
        }
    }

    // ---- Exception-handling boundaries ----

    fn add_eh_call_site(func: &mut MachFunction, call_block: BlockId, pad: BlockId) {
        func.eh_metadata
            .add_call_site(trust_cg_ir::EhCallSiteEntry {
                call_block,
                start_offset: 0,
                length: 0,
                landing_pad_block: Some(pad),
            });
        func.eh_metadata
            .add_landing_pad(trust_cg_ir::LandingPadEntry {
                block: pad,
                offset: 0,
                catch_type_indices: vec![0],
                is_cleanup: false,
            });
    }

    #[test]
    fn test_eh_landing_pad_stays_reachable_and_call_site_unmerged() {
        // The post-ISel Invoke shape (the O2 `Invoke` regression):
        //   bb0 (call site): Bl <callee>; B bb1      eh: bb0 -> pad bb2
        //   bb1 (normal dest, sole pred bb0): Ret
        //   bb2 (landing pad, entered by the UNWINDER only): Ret
        //
        // Without the EH edge seeding, bb2 has no predecessors and
        // `remove_unreachable_blocks` drops it from `block_order` while
        // `eh_metadata` still references it (the fail-closed pipeline
        // validator then rejects the function). And without the merge guard,
        // `fold_unconditional_branches` merges bb1 INTO the protected bb0
        // range.
        let mut func = empty_func();
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let bl = func.push_inst(MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("callee".to_string())],
        ));
        func.append_inst(BlockId(0), bl);
        let b = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(bb1.0)]));
        func.append_inst(BlockId(0), b);

        let ret1 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb1, ret1);

        let ret2 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret2);

        func.add_edge(BlockId(0), bb1);
        add_eh_call_site(&mut func, BlockId(0), bb2);

        let mut pass = CfgSimplify;
        pass.run(&mut func);

        // The landing pad must stay laid out and the call-site block must
        // keep its own boundary (nothing merged into the protected range).
        assert!(
            func.block_order.contains(&bb2),
            "landing pad must not be removed from block_order: {:?}",
            func.block_order
        );
        assert!(
            func.block_order.contains(&bb1),
            "normal dest must stay laid out: {:?}",
            func.block_order
        );
        assert_eq!(
            func.block(BlockId(0)).insts,
            vec![bl, b],
            "no instructions may be merged into the protected call-site block"
        );
        assert!(
            func.block(bb2).preds.contains(&BlockId(0)),
            "the unwinder edge call-site -> pad must be seeded: {:?}",
            func.block(bb2).preds
        );
        assert_block_targets_retained(&func);
    }

    #[test]
    fn test_eh_single_jump_landing_pad_not_eliminated() {
        // A cleanup pad whose body collapsed to a bare `B` must keep its own
        // layout position: the unwinder enters it via the LSDA, not via a
        // branch, so eliminate/thread-through must never treat it as an
        // empty jump block.
        //   bb0 (call site): Bl <callee>; B bb1     eh: bb0 -> pad bb2
        //   bb1 (normal dest): Ret
        //   bb2 (pad): B bb3
        //   bb3 (shared cleanup): Ret
        let mut func = empty_func();
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let bl = func.push_inst(MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("callee".to_string())],
        ));
        func.append_inst(BlockId(0), bl);
        let b = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(bb1.0)]));
        func.append_inst(BlockId(0), b);

        let ret1 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb1, ret1);

        let pad_b = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(bb3.0)]));
        func.append_inst(bb2, pad_b);

        let ret3 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb3, ret3);

        func.add_edge(BlockId(0), bb1);
        func.add_edge(bb2, bb3);
        add_eh_call_site(&mut func, BlockId(0), bb2);

        let mut pass = CfgSimplify;
        pass.run(&mut func);

        assert!(
            func.block_order.contains(&bb2),
            "single-jump landing pad must not be eliminated: {:?}",
            func.block_order
        );
        assert!(
            func.block_order.contains(&bb3),
            "the pad's target must stay laid out: {:?}",
            func.block_order
        );
        assert_eq!(
            func.block(bb2).insts,
            vec![pad_b],
            "the pad body must survive untouched"
        );
        assert_block_targets_retained(&func);
    }

    #[test]
    fn test_eh_metadata_pruned_in_lockstep_with_unreachable_invoke_region() {
        // A FULLY-unreachable invoke region: the call-site block itself has no
        // path from entry (its only inbound edge was folded away by an earlier
        // pass), so unreachable-block removal legitimately prunes the whole
        // region. Previously the `eh_metadata` entries survived the pruning and
        // the fail-closed pipeline validator rejected the function ("exception
        // landing pad targets block ... absent from block_order"). The EH
        // metadata must be dropped in the SAME step as the blocks.
        //   bb0 (entry):          Ret
        //   bb1 (dead call site): Bl <callee>; B bb2    eh: bb1 -> pad bb3
        //   bb2 (dead normal):    Ret
        //   bb3 (dead pad):       Ret
        let mut func = empty_func();
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let ret0 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(BlockId(0), ret0);

        let bl = func.push_inst(MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("callee".to_string())],
        ));
        func.append_inst(bb1, bl);
        let b = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(bb2.0)]));
        func.append_inst(bb1, b);

        let ret2 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret2);

        let ret3 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb3, ret3);

        func.add_edge(bb1, bb2);
        add_eh_call_site(&mut func, bb1, bb3);
        func.eh_metadata.personality = Some("rust_eh_personality".to_string());

        let mut pass = CfgSimplify;
        pass.run(&mut func);

        assert_eq!(
            func.block_order,
            vec![BlockId(0)],
            "the dead invoke region must be pruned from layout"
        );
        assert!(
            func.eh_metadata.call_sites.is_empty(),
            "call-site entries anchored on removed blocks must be pruned in lockstep: {:?}",
            func.eh_metadata.call_sites
        );
        assert!(
            func.eh_metadata.landing_pads.is_empty(),
            "landing-pad entries anchored on removed blocks must be pruned in lockstep: {:?}",
            func.eh_metadata.landing_pads
        );
        assert!(
            func.eh_metadata.personality.is_none(),
            "an LSDA-less function must not keep a personality reference"
        );
        assert!(!func.eh_metadata.has_eh_info());
        assert_block_targets_retained(&func);
    }

    #[test]
    fn test_eh_metadata_partial_prune_keeps_live_invoke_region() {
        // Two invoke regions: one reachable, one fully dead. Only the dead
        // region's EH entries may be pruned; the live pad/call-site (and the
        // personality) must survive byte-identically.
        //   bb0 (live call site): Bl <callee>; B bb1   eh: bb0 -> pad bb2
        //   bb1 (normal dest):    Ret
        //   bb2 (live pad):       Ret
        //   bb3 (dead call site): Bl <callee>; B bb4   eh: bb3 -> pad bb5
        //   bb4 (dead normal):    Ret
        //   bb5 (dead pad):       Ret
        let mut func = empty_func();
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        let bb4 = func.create_block();
        let bb5 = func.create_block();

        let bl0 = func.push_inst(MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("callee".to_string())],
        ));
        func.append_inst(BlockId(0), bl0);
        let b0 = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(bb1.0)]));
        func.append_inst(BlockId(0), b0);
        let ret1 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb1, ret1);
        let ret2 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret2);

        let bl3 = func.push_inst(MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("callee".to_string())],
        ));
        func.append_inst(bb3, bl3);
        let b3 = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(bb4.0)]));
        func.append_inst(bb3, b3);
        let ret4 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb4, ret4);
        let ret5 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb5, ret5);

        func.add_edge(BlockId(0), bb1);
        func.add_edge(bb3, bb4);
        add_eh_call_site(&mut func, BlockId(0), bb2);
        add_eh_call_site(&mut func, bb3, bb5);
        func.eh_metadata.personality = Some("rust_eh_personality".to_string());

        let mut pass = CfgSimplify;
        pass.run(&mut func);

        assert!(func.block_order.contains(&bb2), "live pad stays laid out");
        assert!(!func.block_order.contains(&bb3), "dead call site pruned");
        assert!(!func.block_order.contains(&bb5), "dead pad pruned");
        assert_eq!(
            func.eh_metadata.call_sites.len(),
            1,
            "only the dead call-site entry may be pruned: {:?}",
            func.eh_metadata.call_sites
        );
        assert_eq!(func.eh_metadata.call_sites[0].call_block, BlockId(0));
        assert_eq!(
            func.eh_metadata.landing_pads.len(),
            1,
            "only the dead landing-pad entry may be pruned: {:?}",
            func.eh_metadata.landing_pads
        );
        assert_eq!(func.eh_metadata.landing_pads[0].block, bb2);
        assert_eq!(
            func.eh_metadata.personality.as_deref(),
            Some("rust_eh_personality"),
            "a function that still has EH info must keep its personality"
        );
        assert_block_targets_retained(&func);
    }

    // ---- Unconditional branch folding ----

    #[test]
    fn test_uncond_branch_folding_single_pred() {
        // bb0: B bb1
        // bb1: ret   (single pred = bb0)
        // After: bb0: ret  (bb1 merged into bb0)
        let mut func = empty_func();
        let bb1 = func.create_block();

        let b_inst = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(1)]));
        func.append_inst(BlockId(0), b_inst);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb1, ret);

        func.add_edge(BlockId(0), bb1);

        let mut pass = CfgSimplify;
        assert!(pass.run(&mut func));

        // bb0 should now contain ret directly (bb1 merged in).
        let bb0 = func.block(BlockId(0));
        assert_eq!(bb0.insts.len(), 1);
        assert_eq!(func.inst(bb0.insts[0]).opcode, AArch64Opcode::Ret);

        // bb1 should be gone from layout.
        assert!(!func.block_order.contains(&bb1));
    }

    #[test]
    fn test_cfg_simplify_provenance_records_uncond_fold_tail_deletion() {
        let mut func = empty_func();
        let bb1 = func.create_block();

        let b_inst = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(bb1.0)]));
        func.append_inst(BlockId(0), b_inst);
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb1, ret);
        func.add_edge(BlockId(0), bb1);

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(10), &[b_inst], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(11), &[ret], PassId::new("isel"));

        let mut pass = CfgSimplify;
        assert!(pass.run_with_provenance(&mut func, &mut provenance));

        assert!(!func.block_order.contains(&bb1));
        assert_eq!(func.block(BlockId(0)).insts, vec![ret]);
        assert_optimized_away_by_cfg_simplify(
            &provenance,
            b_inst,
            "unconditional branch folded into successor block",
        );
        assert!(provenance.get_entry(ret).unwrap().is_active());
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(11)).unwrap(),
            &[ret]
        );
    }

    #[test]
    fn test_uncond_branch_folding_preserves_mid_block_join_target() {
        // bb0: cbnz v0, bb2; B bb1
        // bb1: B bb2
        // bb2: ret
        //
        // Folding bb1 into bb0 is legal, but bb2 must stay in layout because
        // bb0 still has a conditional branch to the bb2 label before its tail.
        let mut func = empty_func();
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let cbnz = func.push_inst(MachInst::new(AArch64Opcode::Cbnz, vec![vreg(0), block(2)]));
        func.append_inst(BlockId(0), cbnz);
        let b0 = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(1)]));
        func.append_inst(BlockId(0), b0);

        let b1 = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(2)]));
        func.append_inst(bb1, b1);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(BlockId(0), bb1);
        func.add_edge(BlockId(0), bb2);
        func.add_edge(bb1, bb2);

        let mut pass = CfgSimplify;
        assert!(pass.run(&mut func));

        assert!(!func.block_order.contains(&bb1));
        assert!(func.block_order.contains(&bb2));

        let bb0 = func.block(BlockId(0));
        assert!(bb0.insts.iter().any(|&inst_id| {
            let inst = func.inst(inst_id);
            inst.opcode == AArch64Opcode::Cbnz && inst.operands.contains(&MachOperand::Block(bb2))
        }));
    }

    #[test]
    fn test_fold_unconditional_branch_preserves_non_adjacent_target_block() {
        // Layout: [entry, A, X, T, F, Taken]
        //
        // entry: cbz g, X; b A
        // A:     mov; b T
        // X:     ret
        // T:     cbz v, Taken   (not-taken fallthrough = F)
        // F:     ret
        // Taken: ret
        //
        // Non-adjacent merge would move T's instruction stream across X. That
        // changes fallthrough semantics for conditional T and can also create
        // an internal terminator shape downstream passes do not model.
        let mut func = empty_func();
        let bb_a = func.create_block();
        let bb_x = func.create_block();
        let bb_t = func.create_block();
        let bb_f = func.create_block();
        let bb_taken = func.create_block();
        func.block_order = vec![BlockId(0), bb_a, bb_x, bb_t, bb_f, bb_taken];

        let entry_cond = func.push_inst(MachInst::new(
            AArch64Opcode::Cbz,
            vec![vreg(10), block(bb_x.0)],
        ));
        func.append_inst(BlockId(0), entry_cond);
        let entry_to_a = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(bb_a.0)]));
        func.append_inst(BlockId(0), entry_to_a);

        let work = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(11), imm(1)]));
        func.append_inst(bb_a, work);
        let a_to_t = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(bb_t.0)]));
        func.append_inst(bb_a, a_to_t);

        let x_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb_x, x_ret);

        let t_cond = func.push_inst(MachInst::new(
            AArch64Opcode::Cbz,
            vec![vreg(12), block(bb_taken.0)],
        ));
        func.append_inst(bb_t, t_cond);

        let f_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb_f, f_ret);
        let taken_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb_taken, taken_ret);

        func.add_edge(BlockId(0), bb_x);
        func.add_edge(BlockId(0), bb_a);
        func.add_edge(bb_a, bb_t);
        func.add_edge(bb_t, bb_f);
        func.add_edge(bb_t, bb_taken);

        let mut pass = CfgSimplify;
        pass.run(&mut func);

        assert!(
            func.block_order.contains(&bb_t),
            "non-adjacent unconditional fold must keep the target block laid out"
        );
        assert!(func.block_order.contains(&bb_f));
        assert_block_targets_retained(&func);
    }

    #[test]
    fn test_fold_unconditional_branch_preserves_non_adjacent_simple_target() {
        // Layout: [A, X, T]
        //
        // A:     cbz g, X; mov; b T
        // X:     ret
        // T:     ret
        //
        // The adjacent-only fold policy applies even when T has no conditional
        // fallthrough of its own: merging T would still move code across X.
        let mut func = empty_func();
        let bb_x = func.create_block();
        let bb_t = func.create_block();
        func.block_order = vec![BlockId(0), bb_x, bb_t];

        let a_cond = func.push_inst(MachInst::new(
            AArch64Opcode::Cbz,
            vec![vreg(10), block(bb_x.0)],
        ));
        func.append_inst(BlockId(0), a_cond);
        let work = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(11), imm(1)]));
        func.append_inst(BlockId(0), work);
        let a_to_t = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(bb_t.0)]));
        func.append_inst(BlockId(0), a_to_t);

        let x_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb_x, x_ret);
        let t_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb_t, t_ret);

        func.add_edge(BlockId(0), bb_x);
        func.add_edge(BlockId(0), bb_t);

        let mut pass = CfgSimplify;
        assert!(!pass.run(&mut func));

        assert!(
            func.block_order.contains(&bb_t),
            "non-adjacent unconditional fold must keep simple target blocks laid out"
        );
        assert_block_targets_retained(&func);
    }

    #[test]
    fn test_uncond_branch_folding_preserves_predecessor_with_internal_branch() {
        // Layout: [A, T, X, F]
        //
        // A: cbnz g, X; b T
        // T: mov; cbnz v, F
        // X: ret
        // F: ret
        //
        // T is adjacent and has a single predecessor, but merging it into A
        // would create an internal branch in A. Liveness/RA/codegen model
        // branch boundaries at block labels, so T must stay laid out.
        let mut func = empty_func();
        let bb_t = func.create_block();
        let bb_x = func.create_block();
        let bb_f = func.create_block();
        func.block_order = vec![BlockId(0), bb_t, bb_x, bb_f];

        let a_cond = func.push_inst(MachInst::new(
            AArch64Opcode::Cbnz,
            vec![vreg(10), block(bb_x.0)],
        ));
        func.append_inst(BlockId(0), a_cond);
        let a_to_t = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(bb_t.0)]));
        func.append_inst(BlockId(0), a_to_t);

        let t_work = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(11), imm(1)]));
        func.append_inst(bb_t, t_work);
        let t_cond = func.push_inst(MachInst::new(
            AArch64Opcode::Cbnz,
            vec![vreg(12), block(bb_f.0)],
        ));
        func.append_inst(bb_t, t_cond);

        let x_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb_x, x_ret);
        let f_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb_f, f_ret);

        func.add_edge(BlockId(0), bb_x);
        func.add_edge(BlockId(0), bb_t);
        func.add_edge(bb_t, bb_x);
        func.add_edge(bb_t, bb_f);

        let mut pass = CfgSimplify;
        pass.run(&mut func);

        assert!(
            func.block_order.contains(&bb_t),
            "unconditional fold must not create internal-control-flow blocks"
        );
        assert_block_targets_retained(&func);
    }

    #[test]
    fn test_fold_unconditional_branch_allows_adjacent_conditional_target() {
        // Layout: [A, T, F, Taken]. T's not-taken fallthrough is F both
        // before and after merging adjacent T into A.
        let mut func = empty_func();
        let bb_t = func.create_block();
        let bb_f = func.create_block();
        let bb_taken = func.create_block();
        func.block_order = vec![BlockId(0), bb_t, bb_f, bb_taken];

        let work = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(1)]));
        func.append_inst(BlockId(0), work);
        let a_to_t = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(bb_t.0)]));
        func.append_inst(BlockId(0), a_to_t);

        let t_cond = func.push_inst(MachInst::new(
            AArch64Opcode::Cbz,
            vec![vreg(2), block(bb_taken.0)],
        ));
        func.append_inst(bb_t, t_cond);

        let f_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb_f, f_ret);
        let taken_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb_taken, taken_ret);

        func.add_edge(BlockId(0), bb_t);
        func.add_edge(bb_t, bb_f);
        func.add_edge(bb_t, bb_taken);

        let mut pass = CfgSimplify;
        assert!(pass.run(&mut func));

        assert!(!func.block_order.contains(&bb_t));
        assert_eq!(func.block_order, vec![BlockId(0), bb_f, bb_taken]);
        let bb0 = func.block(BlockId(0));
        let last = func.inst(*bb0.insts.last().unwrap());
        assert_eq!(last.opcode, AArch64Opcode::Cbz);
        assert_eq!(last.operands, vec![vreg(2), block(bb_taken.0)]);
        assert_block_targets_retained(&func);
    }

    #[test]
    fn test_uncond_branch_folding_preserves_backedge_latch_boundary() {
        // Layout: [Body, Latch, Exit]
        //
        // Body:  work; b Latch
        // Latch: copy loop-carried value; cmp; b.lo Body
        // Exit:  ret
        //
        // The latch has a single predecessor, so plain branch folding is
        // tempting. It must remain a distinct block because the Body->Latch
        // edge carries the loop-state update; merging Latch into Body creates
        // a self-loop where post-RA copy coalescing can erase that boundary.
        let mut func = empty_func();
        let latch = func.create_block();
        let exit = func.create_block();
        func.block_order = vec![BlockId(0), latch, exit];

        let work = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(3), vreg(1), vreg(2)],
        ));
        func.append_inst(BlockId(0), work);
        let body_to_latch = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(latch.0)]));
        func.append_inst(BlockId(0), body_to_latch);

        let carry = func.push_inst(MachInst::new(AArch64Opcode::Copy, vec![vreg(1), vreg(3)]));
        func.append_inst(latch, carry);
        let cmp = func.push_inst(MachInst::new(AArch64Opcode::CmpRR, vec![vreg(1), vreg(4)]));
        func.append_inst(latch, cmp);
        let backedge = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(CondCode::LO.encoding() as i64), block(0)],
        ));
        func.append_inst(latch, backedge);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(exit, ret);

        func.add_edge(BlockId(0), latch);
        func.add_edge(latch, BlockId(0));
        func.add_edge(latch, exit);

        let mut pass = CfgSimplify;
        assert!(
            !pass.run(&mut func),
            "backedge latch should not be folded into its body"
        );
        assert!(func.block_order.contains(&latch));
        assert_eq!(func.block(BlockId(0)).insts, vec![work, body_to_latch]);
        assert_eq!(func.block(latch).insts, vec![carry, cmp, backedge]);
        assert_block_targets_retained(&func);
    }

    // ---- Empty block elimination ----

    #[test]
    fn test_empty_block_elimination() {
        // bb0: B bb1
        // bb1: B bb2   (empty: only an unconditional branch)
        // bb2: ret
        // After: bb0: B bb2, bb2: ret  (bb1 eliminated)
        let mut func = empty_func();
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let b0 = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(1)]));
        func.append_inst(BlockId(0), b0);

        let b1 = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(2)]));
        func.append_inst(bb1, b1);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(BlockId(0), bb1);
        func.add_edge(bb1, bb2);

        let mut pass = CfgSimplify;
        assert!(pass.run(&mut func));

        // After simplification, bb0 should reach bb2 (bb1 eliminated or threaded).
        // bb1 should be gone from layout.
        assert!(!func.block_order.contains(&bb1));

        // bb0's branch should target bb2 (via thread or merge).
        let bb0 = func.block(BlockId(0));
        // bb0 may have been merged with bb2 (only ret left) since bb1 was eliminated
        // and bb0→bb2 with single pred.
        let last = func.inst(*bb0.insts.last().unwrap());
        assert!(
            last.opcode == AArch64Opcode::Ret
                || (last.opcode == AArch64Opcode::B
                    && last.operands.contains(&MachOperand::Block(bb2)))
        );
    }

    #[test]
    fn test_cfg_simplify_provenance_records_empty_block_redirect_and_delete() {
        // Layout keeps bb1 away from bb0's fallthrough so empty-block
        // elimination can redirect bb0's branch and remove bb1.
        let mut func = empty_func();
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        func.block_order = vec![BlockId(0), bb3, bb1, bb2];

        let cbz = func.push_inst(MachInst::new(
            AArch64Opcode::Cbz,
            vec![vreg(0), block(bb1.0)],
        ));
        func.append_inst(BlockId(0), cbz);

        let ret3 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb3, ret3);
        let b1 = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(bb2.0)]));
        func.append_inst(bb1, b1);
        let ret2 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret2);

        func.add_edge(BlockId(0), bb1);
        func.add_edge(BlockId(0), bb3);
        func.add_edge(bb1, bb2);

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(20), &[cbz], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(21), &[b1], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(22), &[ret2], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(23), &[ret3], PassId::new("isel"));

        let mut pass = CfgSimplify;
        let mut analyses = AnalysisCache::new();
        assert!(pass.run_with_analyses_and_provenance(&mut func, &mut analyses, &mut provenance));

        assert!(!func.block_order.contains(&bb1));
        let bb0 = func.block(BlockId(0));
        let rewritten = func.inst(*bb0.insts.last().unwrap());
        assert_eq!(rewritten.opcode, AArch64Opcode::Cbz);
        assert_eq!(rewritten.operands, vec![vreg(0), block(bb2.0)]);

        assert_cfg_simplify_survived(&provenance, cbz);
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(20)).unwrap(),
            &[cbz]
        );
        assert_optimized_away_by_cfg_simplify(
            &provenance,
            b1,
            "empty jump block removed by cfg-simplify",
        );
        assert!(provenance.get_entry(ret2).unwrap().is_active());
        assert!(provenance.get_entry(ret3).unwrap().is_active());
    }

    #[test]
    fn test_cfg_simplify_provenance_records_threaded_branch_and_unreachable_jump() {
        // Disable empty-block elimination to isolate branch-target threading.
        // The threaded single-jump block then becomes unreachable and is
        // deleted by the next fixed-point iteration with an explicit reason.
        let mut func = empty_func();
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        func.block_order = vec![BlockId(0), bb3, bb1, bb2];

        let branch_loc = source_loc(41);
        let jump_loc = source_loc(42);
        let cbz = func.push_inst(
            MachInst::new(AArch64Opcode::Cbz, vec![vreg(0), block(bb1.0)])
                .with_source_loc(branch_loc),
        );
        func.append_inst(BlockId(0), cbz);

        let ret3 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb3, ret3);
        let b1 = func.push_inst(
            MachInst::new(AArch64Opcode::B, vec![block(bb2.0)]).with_source_loc(jump_loc),
        );
        func.append_inst(bb1, b1);
        let ret2 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret2);

        func.add_edge(BlockId(0), bb1);
        func.add_edge(BlockId(0), bb3);
        func.add_edge(bb1, bb2);

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(30), &[cbz], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(31), &[b1], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(32), &[ret2], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(33), &[ret3], PassId::new("isel"));

        let config = CfgSimplifyConfig::from_disabled_subpasses("empty-blocks");
        assert!(run_cfg_simplify_with_provenance(
            &mut func,
            &config,
            &mut provenance
        ));

        let rewritten = func.inst(cbz);
        assert_eq!(rewritten.opcode, AArch64Opcode::Cbz);
        assert_eq!(rewritten.operands, vec![vreg(0), block(bb2.0)]);
        assert_eq!(rewritten.source_loc, Some(branch_loc));
        assert_cfg_simplify_survived(&provenance, cbz);
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(30)).unwrap(),
            &[cbz]
        );

        assert!(!func.block_order.contains(&bb1));
        assert_optimized_away_by_cfg_simplify(
            &provenance,
            b1,
            "unreachable block removed by cfg-simplify",
        );
        assert!(provenance.get_entry(ret2).unwrap().is_active());
        assert!(provenance.get_entry(ret3).unwrap().is_active());
    }

    #[test]
    fn test_empty_block_elimination_preserves_conditional_fallthrough() {
        // Layout: [bb0, bb1, bb2, bb3]
        // bb0: cbz v0, bb2   (not-taken fallthrough = bb1)
        // bb1: B bb3         (empty fallthrough block)
        // bb2: ret
        // bb3: ret
        //
        // Removing bb1 would make bb2 the not-taken fallthrough and change
        // the conditional branch semantics.
        let mut func = empty_func();
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let cbz = func.push_inst(MachInst::new(AArch64Opcode::Cbz, vec![vreg(0), block(2)]));
        func.append_inst(BlockId(0), cbz);

        let b1 = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(3)]));
        func.append_inst(bb1, b1);

        let ret2 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret2);
        let ret3 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb3, ret3);

        func.add_edge(BlockId(0), bb1);
        func.add_edge(BlockId(0), bb2);
        func.add_edge(bb1, bb3);

        let mut pass = CfgSimplify;
        assert!(!pass.run(&mut func));

        assert!(
            func.block_order.contains(&bb1),
            "conditional fallthrough block must remain in layout"
        );

        let bb0 = func.block(BlockId(0));
        let last = func.inst(*bb0.insts.last().unwrap());
        assert_eq!(last.opcode, AArch64Opcode::Cbz);
        assert_eq!(last.operands, vec![vreg(0), block(bb2.0)]);
        let bb1_block = func.block(bb1);
        let bb1_last = func.inst(*bb1_block.insts.last().unwrap());
        assert_eq!(bb1_last.opcode, AArch64Opcode::B);
        assert_eq!(bb1_last.operands, vec![block(bb3.0)]);
    }

    #[test]
    fn test_empty_block_elim_does_not_leave_removed_jump_cycle_targets() {
        // bb0: b bb1
        // bb1: b bb2
        // bb2: b bb1
        //
        // Empty-block elimination must not collect the cycle as simultaneous
        // removals that leave retained branches pointing at removed labels.
        let mut func = empty_func();
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let b0 = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(bb1.0)]));
        func.append_inst(BlockId(0), b0);
        let b1 = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(bb2.0)]));
        func.append_inst(bb1, b1);
        let b2 = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(bb1.0)]));
        func.append_inst(bb2, b2);

        func.add_edge(BlockId(0), bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb2, bb1);

        let mut pass = CfgSimplify;
        pass.run(&mut func);
        assert_block_targets_retained(&func);
        assert!(!pass.run(&mut func));
        assert_block_targets_retained(&func);
    }

    // ---- Unreachable block removal ----

    #[test]
    fn test_unreachable_block_removal() {
        // bb0: ret
        // bb1: ret   (unreachable — no edges to bb1)
        let mut func = empty_func();
        let bb1 = func.create_block();

        let ret0 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(BlockId(0), ret0);

        let ret1 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb1, ret1);

        // No edge from bb0 to bb1.

        let mut pass = CfgSimplify;
        assert!(pass.run(&mut func));

        // bb1 should be removed from layout.
        assert!(!func.block_order.contains(&bb1));
        assert_eq!(func.block_order.len(), 1);
        assert_eq!(func.block_order[0], BlockId(0));
    }

    // ---- Branch target simplification (thread-through) ----

    #[test]
    fn test_branch_target_simplification() {
        // Layout: [bb0, bb3, bb1, bb2]
        // bb0: cbz v0, bb1   (fallthrough = bb3)
        // bb3: ret            (fallthrough target)
        // bb1: B bb2          (single jump block, not fallthrough)
        // bb2: ret
        // After thread-through: bb0 cbz target rewritten from bb1 → bb2.
        // bb1 becomes unreachable and is removed.
        let mut func = empty_func();
        let bb1 = func.create_block(); // BlockId(1)
        let bb2 = func.create_block(); // BlockId(2)
        let bb3 = func.create_block(); // BlockId(3)

        // Reorder layout: [bb0, bb3, bb1, bb2]
        func.block_order = vec![BlockId(0), bb3, bb1, bb2];

        let cbz = func.push_inst(MachInst::new(
            AArch64Opcode::Cbz,
            vec![vreg(0), block(bb1.0)],
        ));
        func.append_inst(BlockId(0), cbz);

        let ret3 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb3, ret3);

        let b1 = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(bb2.0)]));
        func.append_inst(bb1, b1);

        let ret2 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret2);

        func.add_edge(BlockId(0), bb1);
        func.add_edge(BlockId(0), bb3);
        func.add_edge(bb1, bb2);

        let mut pass = CfgSimplify;
        assert!(pass.run(&mut func));

        // bb1 (the single-jump block) should be eliminated.
        assert!(!func.block_order.contains(&bb1));

        // bb0's cbz should now reference bb2 directly.
        let bb0 = func.block(BlockId(0));
        let last = func.inst(*bb0.insts.last().unwrap());
        let has_bb2 = last.operands.contains(&MachOperand::Block(bb2));
        assert!(has_bb2, "branch target should be threaded to bb2");
    }

    #[test]
    fn test_resolve_chains_rejects_cycles() {
        let jump_map = HashMap::from([(BlockId(1), BlockId(2)), (BlockId(2), BlockId(1))]);
        let resolved = resolve_chains(&jump_map);
        assert!(resolved.is_empty());
    }

    // ---- Duplicate branch elimination ----

    #[test]
    fn test_duplicate_branch_elim() {
        // bb0: cbz v0, bb1   (fallthrough = bb1 too)
        // bb1: ret
        // Both arms go to bb1 → convert to B bb1 → merge bb1 into bb0.
        // Final: bb0 ends with Ret.
        let mut func = empty_func();
        let bb1 = func.create_block();

        let cbz = func.push_inst(MachInst::new(AArch64Opcode::Cbz, vec![vreg(0), block(1)]));
        func.append_inst(BlockId(0), cbz);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb1, ret);

        func.add_edge(BlockId(0), bb1);

        let mut pass = CfgSimplify;
        assert!(pass.run(&mut func));

        // After dup branch elim (cbz→B) and branch folding (merge bb1 into bb0),
        // bb0 ends with Ret and bb1 is removed.
        let bb0 = func.block(BlockId(0));
        let last = func.inst(*bb0.insts.last().unwrap());
        assert_eq!(last.opcode, AArch64Opcode::Ret);
        assert!(!func.block_order.contains(&bb1));
    }

    #[test]
    fn test_cfg_simplify_provenance_records_duplicate_branch_rewrite() {
        let mut func = empty_func();
        let bb1 = func.create_block();

        let branch_loc = source_loc(57);
        let cbz = func.push_inst(
            MachInst::new(AArch64Opcode::Cbz, vec![vreg(0), block(bb1.0)])
                .with_source_loc(branch_loc),
        );
        func.append_inst(BlockId(0), cbz);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb1, ret);

        func.add_edge(BlockId(0), bb1);

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(40), &[cbz], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(41), &[ret], PassId::new("isel"));

        assert!(eliminate_duplicate_branches(
            &mut func,
            Some(&mut provenance)
        ));

        let rewritten = func.inst(cbz);
        assert_eq!(rewritten.opcode, AArch64Opcode::B);
        assert_eq!(rewritten.operands, vec![block(bb1.0)]);
        assert_eq!(
            rewritten.source_loc,
            Some(branch_loc),
            "cfg-simplify must keep source_loc when replacing a duplicate conditional branch"
        );
        assert_cfg_simplify_survived(&provenance, cbz);
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(40)).unwrap(),
            &[cbz]
        );
        assert!(provenance.get_entry(ret).unwrap().is_active());
    }

    // ---- Constant branch folding ----

    #[test]
    fn test_constant_branch_fold_cbz_taken() {
        // bb0: v0 = movi #0; cbz v0, bb2
        // bb1: ret (fallthrough)
        // bb2: ret (target)
        // v0 == 0 → branch taken → B bb2 → merge bb2 into bb0.
        // Final: bb0 has [movi, ret], bb1 unreachable and removed.
        let mut func = empty_func();
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let movi = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(0)]));
        func.append_inst(BlockId(0), movi);

        let cbz = func.push_inst(MachInst::new(AArch64Opcode::Cbz, vec![vreg(0), block(2)]));
        func.append_inst(BlockId(0), cbz);

        let ret1 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb1, ret1);

        let ret2 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret2);

        func.add_edge(BlockId(0), bb1);
        func.add_edge(BlockId(0), bb2);

        let mut pass = CfgSimplify;
        assert!(pass.run(&mut func));

        // After constant fold + merge, bb0 ends with Ret.
        let bb0 = func.block(BlockId(0));
        let last = func.inst(*bb0.insts.last().unwrap());
        assert_eq!(last.opcode, AArch64Opcode::Ret);
        // bb1 becomes unreachable and is removed.
        assert!(!func.block_order.contains(&bb1));
    }

    #[test]
    fn test_constant_branch_fold_cbz_not_taken() {
        // bb0: v0 = movi #42; cbz v0, bb2
        // bb1: ret (fallthrough)
        // bb2: ret (target)
        // v0 != 0 → branch NOT taken → B bb1 → merge bb1 into bb0.
        // Final: bb0 has [movi, ret], bb2 unreachable and removed.
        let mut func = empty_func();
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let movi = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(42)]));
        func.append_inst(BlockId(0), movi);

        let cbz = func.push_inst(MachInst::new(AArch64Opcode::Cbz, vec![vreg(0), block(2)]));
        func.append_inst(BlockId(0), cbz);

        let ret1 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb1, ret1);

        let ret2 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret2);

        func.add_edge(BlockId(0), bb1);
        func.add_edge(BlockId(0), bb2);

        let mut pass = CfgSimplify;
        assert!(pass.run(&mut func));

        // After constant fold + merge, bb0 ends with Ret.
        let bb0 = func.block(BlockId(0));
        let last = func.inst(*bb0.insts.last().unwrap());
        assert_eq!(last.opcode, AArch64Opcode::Ret);
        // bb2 becomes unreachable and is removed.
        assert!(!func.block_order.contains(&bb2));
    }

    // ---- Idempotent ----

    #[test]
    fn test_idempotent() {
        // After running once, running again should produce no changes.
        let mut func = empty_func();
        let bb1 = func.create_block();

        let b = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(1)]));
        func.append_inst(BlockId(0), b);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb1, ret);

        func.add_edge(BlockId(0), bb1);

        let mut pass = CfgSimplify;
        assert!(pass.run(&mut func)); // First pass: merges bb1 into bb0
        assert!(!pass.run(&mut func)); // Second pass: nothing to do
    }

    // ---- Entry block preservation ----

    #[test]
    fn test_entry_block_preserved() {
        // Even with no branches, the entry block must not be removed.
        let mut func = empty_func();
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(BlockId(0), ret);

        let mut pass = CfgSimplify;
        assert!(!pass.run(&mut func));

        assert!(func.block_order.contains(&BlockId(0)));
    }

    // ---- No changes on already-simplified function ----

    #[test]
    fn test_no_changes_simple_function() {
        let mut func = empty_func();
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(BlockId(0), ret);

        let mut pass = CfgSimplify;
        assert!(!pass.run(&mut func));
    }

    // ---- Constant branch folding: cbnz ----

    #[test]
    fn test_constant_branch_fold_cbnz_taken() {
        // v0 = movi #5; cbnz v0, bb2  → v0 != 0, taken → B bb2 → merge.
        // Final: bb0 has [movi, ret], bb1 unreachable.
        let mut func = empty_func();
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let movi = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(5)]));
        func.append_inst(BlockId(0), movi);

        let cbnz = func.push_inst(MachInst::new(AArch64Opcode::Cbnz, vec![vreg(0), block(2)]));
        func.append_inst(BlockId(0), cbnz);

        let ret1 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb1, ret1);

        let ret2 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret2);

        func.add_edge(BlockId(0), bb1);
        func.add_edge(BlockId(0), bb2);

        let mut pass = CfgSimplify;
        assert!(pass.run(&mut func));

        // After fold + merge, bb0 ends with Ret.
        let bb0 = func.block(BlockId(0));
        let last = func.inst(*bb0.insts.last().unwrap());
        assert_eq!(last.opcode, AArch64Opcode::Ret);
        assert!(!func.block_order.contains(&bb1));
    }

    #[test]
    fn test_cfgsimplify_empty_config_runs_default() {
        let mut func = empty_func();
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let movi = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(0)]));
        func.append_inst(BlockId(0), movi);
        let cbz = func.push_inst(MachInst::new(
            AArch64Opcode::Cbz,
            vec![vreg(0), block(bb2.0)],
        ));
        func.append_inst(BlockId(0), cbz);

        let ret1 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb1, ret1);
        let ret2 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret2);

        func.add_edge(BlockId(0), bb1);
        func.add_edge(BlockId(0), bb2);

        let config = CfgSimplifyConfig::default();
        assert!(run_cfg_simplify(&mut func, &config));

        let bb0 = func.block(BlockId(0));
        let last = func.inst(*bb0.insts.last().unwrap());
        assert_eq!(last.opcode, AArch64Opcode::Ret);
        assert!(!func.block_order.contains(&bb1));
    }

    #[test]
    fn test_cfgsimplify_can_disable_const_fold_only() {
        let mut func = empty_func();
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let movi = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(0)]));
        func.append_inst(BlockId(0), movi);
        let cbz = func.push_inst(MachInst::new(
            AArch64Opcode::Cbz,
            vec![vreg(0), block(bb2.0)],
        ));
        func.append_inst(BlockId(0), cbz);

        let ret1 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb1, ret1);
        let ret2 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret2);

        func.add_edge(BlockId(0), bb1);
        func.add_edge(BlockId(0), bb2);

        let config = CfgSimplifyConfig::from_disabled_subpasses("const-fold");
        assert!(!run_cfg_simplify(&mut func, &config));

        let bb0 = func.block(BlockId(0));
        let last = func.inst(*bb0.insts.last().unwrap());
        assert_eq!(last.opcode, AArch64Opcode::Cbz);
        assert_eq!(last.operands, vec![vreg(0), block(bb2.0)]);
        assert!(func.block_order.contains(&bb1));
        assert!(func.block_order.contains(&bb2));
    }

    #[test]
    fn test_cfgsimplify_can_disable_empty_blocks_only() {
        let mut func = empty_func();
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let b0 = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(bb1.0)]));
        func.append_inst(BlockId(0), b0);
        let b1 = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(bb2.0)]));
        func.append_inst(bb1, b1);
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(BlockId(0), bb1);
        func.add_edge(bb1, bb2);

        let config = CfgSimplifyConfig::from_disabled_subpasses(
            "unreachable,empty-blocks,branch-targets,uncond-fold",
        );
        assert!(!run_cfg_simplify(&mut func, &config));
        assert!(func.block_order.contains(&bb1));
        let bb1_block = func.block(bb1);
        let last = func.inst(*bb1_block.insts.last().unwrap());
        assert_eq!(last.opcode, AArch64Opcode::B);
        assert_eq!(last.operands, vec![block(bb2.0)]);
    }

    #[test]
    fn test_constant_branch_fold_requires_same_block_dominating_def() {
        // bb1 and bb2 define different constants for v0 on different paths.
        // bb3's cbz must not be folded from either non-dominating definition.
        let mut func = empty_func();
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        let bb_zero = func.create_block();
        let bb_nonzero = func.create_block();
        // Keep the zero target distinct from bb3's layout fallthrough so this
        // test isolates constant folding rather than duplicate-branch folding.
        func.block_order = vec![BlockId(0), bb2, bb1, bb3, bb_nonzero, bb_zero];

        let entry_branch = func.push_inst(MachInst::new(
            AArch64Opcode::Cbz,
            vec![vreg(1), block(bb1.0)],
        ));
        func.append_inst(BlockId(0), entry_branch);

        let mov_zero = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(0)]));
        func.append_inst(bb1, mov_zero);
        let bb1_to_join = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(bb3.0)]));
        func.append_inst(bb1, bb1_to_join);

        let mov_one = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(1)]));
        func.append_inst(bb2, mov_one);
        let bb2_to_join = func.push_inst(MachInst::new(AArch64Opcode::B, vec![block(bb3.0)]));
        func.append_inst(bb2, bb2_to_join);

        let join_branch = func.push_inst(MachInst::new(
            AArch64Opcode::Cbz,
            vec![vreg(0), block(bb_zero.0)],
        ));
        func.append_inst(bb3, join_branch);

        let zero_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb_zero, zero_ret);
        let nonzero_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb_nonzero, nonzero_ret);

        func.add_edge(BlockId(0), bb1);
        func.add_edge(BlockId(0), bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb3);
        func.add_edge(bb3, bb_zero);
        func.add_edge(bb3, bb_nonzero);

        assert!(!fold_constant_branches(&mut func, None));

        let branch = func.inst(join_branch);
        assert_eq!(branch.opcode, AArch64Opcode::Cbz);
        assert_eq!(branch.operands, vec![vreg(0), block(bb_zero.0)]);
    }

    #[test]
    fn test_constant_branch_fold_uses_nearest_same_block_def() {
        let mut func = empty_func();
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let old_def = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(0)]));
        func.append_inst(BlockId(0), old_def);
        let new_def = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(7)]));
        func.append_inst(BlockId(0), new_def);
        let cbz = func.push_inst(MachInst::new(
            AArch64Opcode::Cbz,
            vec![vreg(0), block(bb2.0)],
        ));
        func.append_inst(BlockId(0), cbz);

        let ret1 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb1, ret1);
        let ret2 = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret2);

        func.add_edge(BlockId(0), bb1);
        func.add_edge(BlockId(0), bb2);

        let mut pass = CfgSimplify;
        assert!(pass.run(&mut func));

        let bb0 = func.block(BlockId(0));
        let last = func.inst(*bb0.insts.last().unwrap());
        assert_eq!(last.opcode, AArch64Opcode::Ret);
        assert!(!func.block_order.contains(&bb2));
    }

    #[test]
    fn test_constant_branch_fold_ignores_same_id_different_class_def() {
        let mut func = empty_func();
        let fallthrough = func.create_block();
        let taken = func.create_block();

        let wrong_class_def = func.push_inst(MachInst::new(
            AArch64Opcode::MovI,
            vec![vreg_class(0, RegClass::Gpr32), imm(0)],
        ));
        func.append_inst(BlockId(0), wrong_class_def);
        let cbz = func.push_inst(MachInst::new(
            AArch64Opcode::Cbz,
            vec![vreg_class(0, RegClass::Gpr64), block(taken.0)],
        ));
        func.append_inst(BlockId(0), cbz);

        let fallthrough_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(fallthrough, fallthrough_ret);
        let taken_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(taken, taken_ret);

        func.add_edge(BlockId(0), fallthrough);
        func.add_edge(BlockId(0), taken);

        assert!(
            !fold_constant_branches(&mut func, None),
            "same numeric id in a different register class must not fold the branch"
        );
        let branch = func.inst(cbz);
        assert_eq!(branch.opcode, AArch64Opcode::Cbz);
        assert_eq!(
            branch.operands,
            vec![vreg_class(0, RegClass::Gpr64), block(taken.0)]
        );
    }

    #[test]
    fn test_constant_branch_fold_skips_nearer_same_id_different_class_def() {
        let mut func = empty_func();
        let fallthrough = func.create_block();
        let taken = func.create_block();

        let matching_def = func.push_inst(MachInst::new(
            AArch64Opcode::MovI,
            vec![vreg_class(0, RegClass::Gpr64), imm(0)],
        ));
        func.append_inst(BlockId(0), matching_def);
        let nearer_wrong_class_def = func.push_inst(MachInst::new(
            AArch64Opcode::MovI,
            vec![vreg_class(0, RegClass::Gpr32), imm(7)],
        ));
        func.append_inst(BlockId(0), nearer_wrong_class_def);
        let cbnz = func.push_inst(MachInst::new(
            AArch64Opcode::Cbnz,
            vec![vreg_class(0, RegClass::Gpr64), block(taken.0)],
        ));
        func.append_inst(BlockId(0), cbnz);

        let fallthrough_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(fallthrough, fallthrough_ret);
        let taken_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(taken, taken_ret);

        func.add_edge(BlockId(0), fallthrough);
        func.add_edge(BlockId(0), taken);

        assert!(
            fold_constant_branches(&mut func, None),
            "nearest matching-class constant should fold the branch"
        );
        let branch = func.inst(cbnz);
        assert_eq!(branch.opcode, AArch64Opcode::B);
        assert_eq!(branch.operands, vec![block(fallthrough.0)]);
    }
}
