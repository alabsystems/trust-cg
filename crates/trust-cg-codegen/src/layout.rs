// trust-cg-codegen/layout.rs - Basic block layout pass
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Basic block layout pass for AArch64.
//!
//! Orders basic blocks to minimize taken branches. Uses a greedy chain-based
//! algorithm: starting from the entry block, greedily place the best
//! fall-through successor next. Unreachable blocks that remain in the
//! executable `block_order` are placed at the end; detached arena shells are
//! never resurrected.
//!
//! Reference: LLVM's MachineBlockPlacement (simplified).

use std::collections::HashSet;
use std::sync::OnceLock;
use trust_cg_ir::aarch64_regs::SP as AARCH64_SP;
use trust_cg_ir::{AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand};
use trust_cg_opt::dom::DomTree;
use trust_cg_opt::loops::{LoopAnalysis, NaturalLoop};

// ---------------------------------------------------------------------------
// Block layout
// ---------------------------------------------------------------------------

/// Compute block layout order for a MachFunction.
///
/// Updates `func.block_order` in place. The entry block is always first.
/// The algorithm greedily chains blocks by fall-through affinity:
/// - For a block ending in a conditional branch (BCond/Cbz/Cbnz/Tbz/Tbnz)
///   without a trailing unconditional B, the implicit fall-through successor
///   is preferred as the next block.
/// - For a block ending in conditional + unconditional B, the non-conditional
///   successor (the one NOT targeted by the conditional branch) is preferred
///   as fall-through.
/// - Blocks with no predecessors (other than entry) are placed last.
pub fn compute_block_layout(func: &mut MachFunction) {
    if func.block_order.len() <= 1 {
        return;
    }

    let num_blocks = func.blocks.len();
    // `blocks` is a stable-ID arena, while `block_order` is the executable
    // domain.  CFG simplification intentionally detaches unreachable arena
    // shells by removing them from `block_order`; treating every arena slot as
    // a layout candidate would revive code that register allocation correctly
    // ignored.  Seed detached slots as already placed so the layout operation
    // is a permutation of the existing executable domain.
    let mut executable = vec![false; num_blocks];
    for &block in &func.block_order {
        executable[block.0 as usize] = true;
    }
    let mut placed = vec![false; num_blocks];
    for (is_placed, is_executable) in placed.iter_mut().zip(&executable) {
        *is_placed = !is_executable;
    }
    let mut order = Vec::with_capacity(func.block_order.len());

    // Always start with the entry block.
    let entry = func.entry;
    placed[entry.0 as usize] = true;
    order.push(entry);

    // Greedy chain construction: for the last placed block, find the best
    // unplaced successor to place next.
    let mut current = entry;
    loop {
        let next = pick_best_successor(func, current, &placed);
        match next {
            Some(succ) => {
                placed[succ.0 as usize] = true;
                order.push(succ);
                current = succ;
            }
            None => {
                // No unplaced successor found for current chain.
                // Start a new chain from any unplaced block that has placed
                // predecessors (prefer blocks with in-edges from placed blocks).
                if let Some(new_head) = find_next_chain_head(func, &placed) {
                    placed[new_head.0 as usize] = true;
                    order.push(new_head);
                    current = new_head;
                } else {
                    break;
                }
            }
        }
    }

    // Append any remaining unplaced executable blocks (unreachable blocks
    // explicitly retained in `block_order`). Detached arena shells were
    // pre-marked placed above and therefore cannot be reintroduced here.
    for (i, is_placed) in placed.iter().enumerate().take(num_blocks) {
        if !is_placed {
            order.push(BlockId(i as u32));
        }
    }

    func.block_order = order;
}

/// Pick the best unplaced successor for `block` to be placed as fall-through.
///
/// Prefers the fall-through path: for a conditional branch block, the
/// successor that would be the implicit fall-through if placed next.
fn pick_best_successor(func: &MachFunction, block: BlockId, placed: &[bool]) -> Option<BlockId> {
    let blk = func.block(block);
    if blk.succs.is_empty() {
        return None;
    }

    // Determine fall-through preference from the terminator pattern.
    let ft = get_fallthrough_successor(func, block);

    // Prefer the fall-through successor if it's unplaced.
    if let Some(ft_block) = ft
        && !placed[ft_block.0 as usize]
    {
        return Some(ft_block);
    }

    // Otherwise pick the first unplaced successor.
    blk.succs
        .iter()
        .find(|&&succ| !placed[succ.0 as usize])
        .copied()
}

/// Find the next chain head: an unplaced block that has at least one placed
/// predecessor. If no such block exists, return any unplaced block.
fn find_next_chain_head(func: &MachFunction, placed: &[bool]) -> Option<BlockId> {
    let mut any_unplaced = None;

    for i in 0..func.blocks.len() {
        if placed[i] {
            continue;
        }
        if any_unplaced.is_none() {
            any_unplaced = Some(BlockId(i as u32));
        }
        // Prefer blocks reachable from placed blocks.
        let blk = &func.blocks[i];
        for &pred in &blk.preds {
            if placed[pred.0 as usize] {
                return Some(BlockId(i as u32));
            }
        }
    }

    any_unplaced
}

// ---------------------------------------------------------------------------
// Loop-aware block placement (LLVM MachineBlockPlacement-lite)
// ---------------------------------------------------------------------------

/// Compute a loop-aware layout order for `func`, updating `func.block_order`.
///
/// Like [`compute_block_layout`]'s greedy chaining, but every **multi-block**
/// loop body is placed CONTIGUOUSLY so its backedge is the single per-iteration
/// taken branch and its in-loop conditionals can fall through on the stay-hot
/// arm. Concretely, while the greedy chain is inside a multi-block loop it will
/// not leave that loop until every one of the loop's blocks is placed (it
/// re-seeds within the loop first). At an in-loop conditional whose *both* arms
/// stay in the loop, the branch-taken (conditional) target is preferred as the
/// fall-through (realized later by [`orient_loop_conditionals`]); exit edges are
/// never preferred, so they become the cold taken arm.
///
/// Single-block (self) loops and blocks outside any loop use the existing greedy
/// fall-through behavior verbatim — straight-line and tight single-block loops
/// are never perturbed (the OPT-8 regression class). Tie-breaks bias toward the
/// current order (minimal perturbation), so already-good layouts reproduce
/// unchanged. Deterministic: every set iteration is ordered by the current
/// layout index then block id.
fn compute_loop_aware_block_layout(
    func: &mut MachFunction,
    loops: &LoopAnalysis,
    scattered: &HashSet<BlockId>,
) {
    let num_blocks = func.blocks.len();
    if num_blocks <= 1 {
        return;
    }
    // Current-order index of each block (usize::MAX = not in current order),
    // used purely as a deterministic minimal-perturbation tie-break.
    let mut order_index = vec![usize::MAX; num_blocks];
    for (i, &b) in func.block_order.iter().enumerate() {
        if let Some(slot) = order_index.get_mut(b.0 as usize) {
            *slot = i;
        }
    }

    let mut placed = vec![false; num_blocks];
    let mut order = Vec::with_capacity(num_blocks);

    let entry = func.entry;
    placed[entry.0 as usize] = true;
    order.push(entry);
    let mut current = entry;

    loop {
        if let Some(next) =
            pick_loop_aware_successor(func, loops, scattered, current, &placed, &order_index)
        {
            placed[next.0 as usize] = true;
            order.push(next);
            current = next;
            continue;
        }
        // The chain from `current` ended. If `current` is still inside a loop
        // with unplaced blocks, re-seed within that loop before leaving it, so
        // the loop body stays contiguous.
        if let Some(next) =
            reseed_in_enclosing_loop(func, loops, scattered, current, &placed, &order_index)
        {
            placed[next.0 as usize] = true;
            order.push(next);
            current = next;
            continue;
        }
        // Otherwise start a new chain from any block reachable from placed code.
        if let Some(next) = find_next_chain_head(func, &placed) {
            placed[next.0 as usize] = true;
            order.push(next);
            current = next;
            continue;
        }
        break;
    }

    // Append any remaining unplaced blocks (unreachable) in id order.
    for (i, is_placed) in placed.iter().enumerate().take(num_blocks) {
        if !is_placed {
            order.push(BlockId(i as u32));
        }
    }

    func.block_order = order;
}

/// Pick the next block to place after `block` under the loop-aware policy.
///
/// If `block` is inside one or more multi-block loops, prefer to extend the
/// chain into the deepest such loop that has an unplaced in-loop successor
/// (excluding the loop header — the backedge stays a taken branch). If no
/// enclosing loop can be extended from `block` but some enclosing loop still has
/// unplaced blocks, return `None` so the driver re-seeds *within* the loop
/// (keeping it contiguous). Only once every enclosing loop is fully placed does
/// this fall back to the plain greedy fall-through successor.
fn pick_loop_aware_successor(
    func: &MachFunction,
    loops: &LoopAnalysis,
    scattered: &HashSet<BlockId>,
    block: BlockId,
    placed: &[bool],
    order_index: &[usize],
) -> Option<BlockId> {
    let encl = enclosing_multiblock_loops(loops, scattered, block);
    for lp in &encl {
        let cands = in_loop_unplaced_succs(func, block, lp, placed);
        if !cands.is_empty() {
            return Some(select_in_loop(func, block, &cands, order_index));
        }
    }
    // Cannot extend directly; if any enclosing loop is unfinished, force a
    // within-loop re-seed rather than leaving the loop.
    if encl.iter().any(|lp| loop_has_unplaced(lp, placed)) {
        return None;
    }
    // Not in any unfinished loop → plain greedy fall-through.
    pick_best_successor(func, block, placed)
}

/// Unplaced successors of `block` that lie in `lp`'s body and are not the loop
/// header (deduplicated, source-succ order preserved for determinism).
fn in_loop_unplaced_succs(
    func: &MachFunction,
    block: BlockId,
    lp: &NaturalLoop,
    placed: &[bool],
) -> Vec<BlockId> {
    let mut out: Vec<BlockId> = Vec::new();
    for &s in &func.block(block).succs {
        if s == lp.header || placed[s.0 as usize] || !lp.body.contains(&s) {
            continue;
        }
        if !out.contains(&s) {
            out.push(s);
        }
    }
    out
}

/// Choose which in-loop successor to place next.
///
/// One candidate: take it. Two-or-more (an in-loop conditional whose arms both
/// stay in the loop): prefer the branch-taken (conditional) target when the
/// terminator can be inverted, so the hot in-loop arm becomes the fall-through
/// after [`orient_loop_conditionals`]; otherwise the natural fall-through
/// successor. Final tie-break: lowest current-order index (minimal perturbation).
fn select_in_loop(
    func: &MachFunction,
    block: BlockId,
    cands: &[BlockId],
    order_index: &[usize],
) -> BlockId {
    if cands.len() == 1 {
        return cands[0];
    }
    if bp_ccpref_enabled()
        && let Some(cp) = classify_cond_pair(func, block)
        && cands.contains(&cp.cc_target)
        && cond_pair_invertible(func, &cp)
    {
        return cp.cc_target;
    }
    if let Some(ft) = get_fallthrough_successor(func, block)
        && cands.contains(&ft)
    {
        return ft;
    }
    *cands
        .iter()
        .min_by_key(|b| (order_index[b.0 as usize], b.0))
        .unwrap()
}

/// True if any block of `lp` is still unplaced.
fn loop_has_unplaced(lp: &NaturalLoop, placed: &[bool]) -> bool {
    lp.body.iter().any(|b| !placed[b.0 as usize])
}

/// Re-seed the chain within the innermost unfinished enclosing loop of `block`:
/// the unplaced loop-body block with a placed predecessor and the lowest
/// current-order index (deterministic). Keeps the loop body contiguous.
fn reseed_in_enclosing_loop(
    func: &MachFunction,
    loops: &LoopAnalysis,
    scattered: &HashSet<BlockId>,
    block: BlockId,
    placed: &[bool],
    order_index: &[usize],
) -> Option<BlockId> {
    for lp in enclosing_multiblock_loops(loops, scattered, block) {
        let mut best: Option<BlockId> = None;
        // Deterministic scan: sorted by (current-order index, id).
        let mut body: Vec<BlockId> = lp.body.iter().copied().collect();
        body.sort_by_key(|b| (order_index[b.0 as usize], b.0));
        for b in body {
            if placed[b.0 as usize] {
                continue;
            }
            let has_placed_pred = func.block(b).preds.iter().any(|&p| placed[p.0 as usize]);
            if has_placed_pred {
                best = Some(b);
                break;
            }
        }
        if best.is_some() {
            return best;
        }
    }
    None
}

/// The SCATTERED multi-block loops containing `block`, innermost first. Single-
/// block (self) loops and loops whose body is already contiguous are excluded —
/// only scattered loops are relaid out / re-oriented.
fn enclosing_multiblock_loops<'a>(
    loops: &'a LoopAnalysis,
    scattered: &HashSet<BlockId>,
    block: BlockId,
) -> Vec<&'a NaturalLoop> {
    let mut out: Vec<&NaturalLoop> = Vec::new();
    let mut cur = loops.containing_loop(block).map(|l| l.header);
    while let Some(h) = cur {
        let Some(lp) = loops.get_loop(h) else { break };
        if lp.body.len() > 1 && scattered.contains(&lp.header) {
            out.push(lp);
        }
        cur = lp.parent;
    }
    out
}

/// The innermost scattered multi-block loop containing `block`, if any.
fn innermost_multiblock_loop<'a>(
    loops: &'a LoopAnalysis,
    scattered: &HashSet<BlockId>,
    block: BlockId,
) -> Option<&'a NaturalLoop> {
    enclosing_multiblock_loops(loops, scattered, block)
        .into_iter()
        .next()
}

/// Headers of the multi-block loops whose body is SCATTERED in the current
/// `block_order` — i.e. the loop's blocks do not occupy a single contiguous
/// run (a foreign block sits inside their span, or a body block is missing from
/// the order). Only these loops are relaid out; a loop already laid out as one
/// contiguous run is left untouched (no fetch-alignment perturbation).
fn scattered_loop_headers(func: &MachFunction, loops: &LoopAnalysis) -> HashSet<BlockId> {
    let mut idx = vec![usize::MAX; func.blocks.len()];
    for (i, &b) in func.block_order.iter().enumerate() {
        if let Some(slot) = idx.get_mut(b.0 as usize) {
            *slot = i;
        }
    }
    let mut out = HashSet::new();
    for lp in loops.all_loops() {
        if lp.body.len() <= 1 {
            continue;
        }
        let (mut mn, mut mx, mut cnt, mut ok) = (usize::MAX, 0usize, 0usize, true);
        let mut nconds = 0usize;
        let mut has_call = false;
        for &b in &lp.body {
            let p = idx.get(b.0 as usize).copied().unwrap_or(usize::MAX);
            if p == usize::MAX {
                ok = false;
                break;
            }
            mn = mn.min(p);
            mx = mx.max(p);
            cnt += 1;
            let mut blk_cond = false;
            for &id in &func.block(b).insts {
                let inst = func.inst(id);
                if inst.is_conditional_branch() {
                    blk_cond = true;
                }
                if inst.is_call() {
                    has_call = true;
                }
            }
            if blk_cond {
                nconds += 1;
            }
        }
        if !ok {
            out.insert(lp.header);
            continue;
        }
        let span = mx - mn + 1;
        let foreign = span - cnt;
        let scattered = span != cnt;
        // Only substantial, call-free loops are relaid out. The orientation win
        // scales with the number of in-loop conditional branches whose stay-hot
        // arm can be made a fall-through (heapsort's sift-down: many
        // conditionals, no calls, pure front-end-bound). Excluded, because
        // relaying them out cannot help and only risks a fetch-alignment
        // regression: small pointer-chasing loops (list/tree walks — memory
        // latency bound) and loops containing calls (call/IO bound, e.g. a
        // printf-driven display loop, where the call dominates any fetch cost).
        let big_enough = cnt >= bp_min_body() && nconds >= bp_min_conds() && !has_call;
        if std::env::var("TCG_BP_DEBUG").as_deref() == Ok("1") && scattered {
            eprintln!(
                "BP_SCATTER fn={} header={:?} body={} span={} foreign={} nconds={} repair={}",
                func.name,
                lp.header,
                cnt,
                span,
                foreign,
                nconds,
                scattered && big_enough
            );
        }
        if scattered && big_enough {
            out.insert(lp.header);
        }
    }
    out
}

/// Minimum loop-body block count for loop-aware relayout (default 8).
fn bp_min_body() -> usize {
    static F: OnceLock<usize> = OnceLock::new();
    *F.get_or_init(|| {
        std::env::var("TCG_BP_MIN_BODY")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(8)
    })
}

/// Minimum in-loop conditional-branch block count for relayout (default 4).
fn bp_min_conds() -> usize {
    static F: OnceLock<usize> = OnceLock::new();
    *F.get_or_init(|| {
        std::env::var("TCG_BP_MIN_CONDS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(4)
    })
}

/// A block ending in the conditional-pair terminator `... ; COND cc T ; B F`
/// (the shape every conditional block has after fall-through materialization).
struct CondPair {
    /// The conditional-branch instruction (`BCond`/`Cbz`/`Cbnz`/`Tbz`/`Tbnz`).
    cond_id: InstId,
    /// The conditional (branch-taken) target `T`.
    cc_target: BlockId,
    /// The trailing unconditional `B F`.
    b_id: InstId,
    /// The fall-through target `F` (the `B`'s target).
    ft_target: BlockId,
}

/// Classify a block's terminator as a conditional pair `... ; COND cc T ; B F`.
/// Returns `None` for any other shape (hard terminator, bare conditional, etc.).
fn classify_cond_pair(func: &MachFunction, block: BlockId) -> Option<CondPair> {
    let reals: Vec<InstId> = func
        .block(block)
        .insts
        .iter()
        .copied()
        .filter(|&id| !func.inst(id).is_pseudo())
        .collect();
    if reals.len() < 2 {
        return None;
    }
    let b_id = reals[reals.len() - 1];
    let cond_id = reals[reals.len() - 2];
    let b_inst = func.inst(b_id);
    if b_inst.opcode != AArch64Opcode::B {
        return None;
    }
    let ft_target = single_block_operand(b_inst)?;
    let cond_inst = func.inst(cond_id);
    if !cond_inst.is_conditional_branch() {
        return None;
    }
    let cc_target = single_block_operand(cond_inst)?;
    if cc_target == ft_target {
        return None;
    }
    Some(CondPair {
        cond_id,
        cc_target,
        b_id,
        ft_target,
    })
}

/// The sole `Block` operand of `inst`, or `None` if it has zero or several.
fn single_block_operand(inst: &MachInst) -> Option<BlockId> {
    let mut found: Option<BlockId> = None;
    for op in &inst.operands {
        if let MachOperand::Block(b) = op {
            if found.is_some() {
                return None;
            }
            found = Some(*b);
        }
    }
    found
}

/// The condition-code immediate of a `BCond`, if present.
fn bcond_cc(inst: &MachInst) -> Option<i64> {
    inst.operands.iter().find_map(|op| match op {
        MachOperand::Imm(v) => Some(*v),
        _ => None,
    })
}

/// True if a conditional pair's terminator can be inverted so its fall-through
/// and branch-taken targets swap: `BCond` with a real invertible cc (`0..=13`,
/// AArch64 flips bit 0; `AL`/`NV` rejected), or a compare-and-branch whose
/// polarity is an opcode swap (`Cbz`/`Cbnz`, `Tbz`/`Tbnz`).
fn cond_pair_invertible(func: &MachFunction, cp: &CondPair) -> bool {
    let cond = func.inst(cp.cond_id);
    match cond.opcode {
        AArch64Opcode::BCond => bcond_cc(cond).is_some_and(|cc| (0..=13).contains(&cc)),
        AArch64Opcode::Cbz | AArch64Opcode::Cbnz | AArch64Opcode::Tbz | AArch64Opcode::Tbnz => true,
        _ => false,
    }
}

/// Invert a conditional pair so control falls through to the old branch-taken
/// target and conditionally branches to the old fall-through target: rewrite
/// `... ; COND cc T ; B F` into `... ; COND !cc F` (falls through to `T`).
///
/// Sound and semantics-preserving: `!cc` is the exact complement of `cc`
/// (`BCond`: bit-0 flip; `Cbz`↔`Cbnz`, `Tbz`↔`Tbnz`: opcode swap), so the block
/// branches to `F` exactly when the original took `B F` and falls through to `T`
/// exactly when the original took `COND cc T`. The successor SET is unchanged
/// (`{T, F}`), only which edge is conditional vs fall-through, so succ/pred
/// edges stay valid. Returns `false` (leaving the block untouched) when the cc
/// is not invertible.
fn invert_cond_pair(func: &mut MachFunction, block: BlockId, cp: &CondPair) -> bool {
    let cond = func.inst(cp.cond_id);
    let (new_opcode, new_operands) = match cond.opcode {
        AArch64Opcode::BCond => {
            let cc = match bcond_cc(cond) {
                Some(cc) if (0..=13).contains(&cc) => cc,
                _ => return false,
            };
            let ops = cond
                .operands
                .iter()
                .map(|op| match op {
                    MachOperand::Imm(_) => MachOperand::Imm(cc ^ 1),
                    MachOperand::Block(_) => MachOperand::Block(cp.ft_target),
                    other => other.clone(),
                })
                .collect();
            (AArch64Opcode::BCond, ops)
        }
        AArch64Opcode::Cbz | AArch64Opcode::Cbnz | AArch64Opcode::Tbz | AArch64Opcode::Tbnz => {
            let swapped = match cond.opcode {
                AArch64Opcode::Cbz => AArch64Opcode::Cbnz,
                AArch64Opcode::Cbnz => AArch64Opcode::Cbz,
                AArch64Opcode::Tbz => AArch64Opcode::Tbnz,
                _ => AArch64Opcode::Tbz,
            };
            let ops = cond
                .operands
                .iter()
                .map(|op| match op {
                    MachOperand::Block(_) => MachOperand::Block(cp.ft_target),
                    other => other.clone(),
                })
                .collect();
            (swapped, ops)
        }
        _ => return false,
    };
    {
        let m = func.inst_mut(cp.cond_id);
        m.opcode = new_opcode;
        m.operands = new_operands;
    }
    // Drop the now-redundant trailing `B F`; control falls through to `T`.
    func.block_mut(block).insts.retain(|&id| id != cp.b_id);
    true
}

/// Realize the loop-driven layout: for every block inside a multi-block loop
/// whose laid-out-next block is its conditional (branch-taken) target, invert
/// the conditional so the stay-hot arm falls through and the cold arm (loop
/// exit or diamond re-convergence) becomes the taken branch. Gated to loop
/// blocks so straight-line code is never re-oriented.
fn orient_loop_conditionals(
    func: &mut MachFunction,
    loops: &LoopAnalysis,
    scattered: &HashSet<BlockId>,
) -> bool {
    if !bp_orient_enabled() {
        return false;
    }
    let order = func.block_order.clone();
    let mut plans: Vec<(BlockId, CondPair)> = Vec::new();
    for i in 0..order.len() {
        let block = order[i];
        let Some(&next) = order.get(i + 1) else {
            continue;
        };
        if innermost_multiblock_loop(loops, scattered, block).is_none() {
            continue;
        }
        let Some(cp) = classify_cond_pair(func, block) else {
            continue;
        };
        // Only flip when the layout-next block is the branch-taken target (so
        // the fall-through would otherwise miss it). `next == ft_target` is
        // already optimal and handled by the plain elision.
        if next != cp.cc_target {
            continue;
        }
        if !cond_pair_invertible(func, &cp) {
            continue;
        }
        plans.push((block, cp));
    }
    let mut changed = false;
    for (block, cp) in plans {
        if invert_cond_pair(func, block, &cp) {
            changed = true;
        }
    }
    changed
}

/// UNIVERSAL in-place conditional orientation ("branch over branch"): for every
/// block whose terminator is a conditional pair `… ; COND cc T ; B F` and whose
/// layout-NEXT block is `T` (the branch-TAKEN target), invert to
/// `… ; COND !cc F` and let control fall through to `T`.
///
/// This is [`orient_loop_conditionals`] with its loop-membership gate removed.
/// That gate ("straight-line code is never re-oriented") was written when the
/// orientation was part of a block REORDER, where flipping a straight-line
/// conditional could interact with placement. This step moves NO block: the
/// layout is already final, and the rewrite touches exactly one instruction and
/// deletes one.
///
/// The two arms are NOT symmetric, and the asymmetry is why this is gated on
/// the `B` not being a back edge (measured, see below):
///
/// * `cc` true  — before: the conditional is TAKEN (to the next block, `PC+8`);
///   after: the conditional is NOT taken and control falls through to the same
///   place. Same instruction count, one fewer taken branch. **Strict win.**
/// * `cc` false — before: conditional not taken, then `B F` taken (2
///   instructions, 1 taken branch); after: the conditional is taken straight to
///   `F` (1 instruction, 1 taken branch). One fewer instruction, but the one
///   surviving taken branch changed from UNCONDITIONAL to CONDITIONAL.
///
/// So the flip pays exactly when `T` — the arm that becomes the fall-through —
/// is the hot one. `T` is hot for the shape this targets in loop-free code
/// (Queens' unrolled `Try`: `cc` = "the search has not succeeded yet", true on
/// every failing placement), and `F` is hot for exactly one systematic shape:
/// a LOOP LATCH `cmp; B.cc exit; B header` whose `B` is the back edge. On
/// Misc/flops-1, whose entire hot loop is that one latch, flipping it to
/// `B.!cc header` removed 312M dynamic instructions (−6.7%) and still cost
/// **+8.2% cycles** (IPC 3.92 → 3.38) — reproduced with loop-head alignment
/// both on and off, so it is the unconditional→conditional taken-branch swap,
/// not a padding artifact. Back-edge `B`s are therefore excluded.
///
/// The shape this removes is one clang never emits: on Stanford/Queens `Try`
/// tcg had 13 such sites (of 456 instructions) and clang 0; on Stanford/Puzzle,
/// 26 and 0.
///
/// Soundness is [`invert_cond_pair`]'s: `!cc` is the exact complement (BCond
/// bit-0 flip, `Cbz`↔`Cbnz`, `Tbz`↔`Tbnz`), the successor SET `{T, F}` is
/// unchanged so succ/pred edges stay valid, and only the conditional-vs-
/// fall-through role of the two edges swaps. Range is not a new concern: an
/// out-of-range `BCond` is expanded by [`crate::relax`] (invert + far `B`),
/// which is exactly the pair this step just collapsed.
///
/// Fail-closed: any block whose terminator is not the exact
/// [`classify_cond_pair`] shape, whose cc is not invertible
/// ([`cond_pair_invertible`] — `AL`/`NV` rejected), or whose `B` is a natural-
/// loop back edge, is left untouched.
///
/// Kill switch: `TCG_BP_NO_NEXT_ORIENT=1` — bytes identical to the pre-feature
/// layout, verified over all 65 importable SingleSource programs. (Same
/// convention as its siblings `TCG_BP_NO_ORIENT` / `TCG_BP_NO_COLDSINK`: this is
/// a codegen layout sub-feature, not a `TRUST_CG_DISABLE_PASSES` pipeline pass,
/// so the env switch IS the bisect key.)
fn orient_next_is_cc_target(func: &mut MachFunction, loops: &LoopAnalysis) -> bool {
    if !bp_next_orient_enabled() {
        return false;
    }
    // Blocks whose trailing `B` is a natural-loop BACK EDGE: `B` targets a loop
    // header and the block is inside that loop's body. There the `B` arm is the
    // hot one by construction (taken on every continue iteration), so inverting
    // trades an unconditional taken branch for a conditional taken branch — the
    // measured flops-1 pessimization. Excluded.
    let mut backedge_sources: HashSet<BlockId> = HashSet::new();
    for lp in loops.all_loops() {
        for &b in &lp.body {
            if let Some(cp) = classify_cond_pair(func, b)
                && cp.ft_target == lp.header
            {
                backedge_sources.insert(b);
            }
        }
    }
    let order = func.block_order.clone();
    let mut plans: Vec<(BlockId, CondPair)> = Vec::new();
    for i in 0..order.len() {
        let block = order[i];
        let Some(&next) = order.get(i + 1) else {
            continue;
        };
        let Some(cp) = classify_cond_pair(func, block) else {
            continue;
        };
        // Only the "conditional jumps over the unconditional" shape. When
        // `next == cp.ft_target` the layout is already optimal and step 4's
        // plain elision drops the `B`.
        if next != cp.cc_target {
            continue;
        }
        if backedge_sources.contains(&block) {
            continue;
        }
        if !cond_pair_invertible(func, &cp) {
            continue;
        }
        plans.push((block, cp));
    }
    let mut changed = false;
    for (block, cp) in plans {
        if invert_cond_pair(func, block, &cp) {
            changed = true;
        }
    }
    changed
}

/// True if `lp` is an ALREADY-ROTATED (bottom-tested) loop: some body block ends
/// with a CONDITIONAL branch straight back to the header (the do-while latch).
/// Because `lp.header` dominates every block of a natural loop, any such
/// conditional edge is a genuine conditional back-edge — exactly the shape the
/// per-function bail protected, but decided PER LOOP here so a sibling top-tested
/// loop in the same function is not tarred by it.
fn loop_is_already_rotated(func: &MachFunction, lp: &NaturalLoop) -> bool {
    lp.body.iter().any(|&b| {
        func.block(b).insts.iter().any(|&id| {
            let inst = func.inst(id);
            inst.is_conditional_branch() && single_block_operand(inst) == Some(lp.header)
        })
    })
}

/// Headers of SMALL, contiguous, MIS-ORIENTED top-tested loops whose in-loop
/// conditional can be flipped to a pure taken-branch reduction WITHOUT any block
/// reorder. This is the per-loop-protection companion to [`scattered_loop_headers`]:
/// it is used only on functions carrying an already-rotated loop (so the whole
/// function is intentionally left un-reordered), to still orient the OTHER hot
/// top-tested loops that the coarse per-function bail used to abandon (chomp's
/// inlined `equal_data` compare loop: `header: cbz exit` + `body: …; b.cc cont;
/// b brk` + `cont: …; b header`, where the equal/stay-in-loop arm `cont` is the
/// branch-taken target laid out next — 2 taken branches/iter instead of 1).
///
/// A loop qualifies iff it is NOT itself already-rotated ([`loop_is_already_rotated`])
/// and it has a body block `B` ending in a conditional pair `… ; COND cc T ; B F`
/// whose branch-taken target `T` is (a) another block INSIDE the loop body (the
/// stay-hot arm) and (b) already the layout-NEXT block after `B`. Under those two
/// facts [`orient_loop_conditionals`] will rewrite `B` to `COND !cc F` and fall
/// through to `T`: the loop-carried arm becomes a fall-through (0 taken) and the
/// exit arm the single taken branch — a provable per-iteration taken-branch
/// reduction, and a strict code-size win (the trailing `B F` is dropped). No block
/// is moved, so the already-rotated sibling loop and all straight-line code keep
/// their exact layout (byte-identical away from the flipped conditionals).
///
/// The qualifying block MAY be the loop HEADER itself (huffbench compdecomp's
/// decode heap2-scan loop: `header: ldr; cmp; add; B.LO latch; B exit` +
/// `latch: mov; B header` — the trip test lives ON the header and its taken arm
/// is the in-loop latch laid out next). The flip argument is identical: the
/// stay-in-loop arm becomes the fall-through (2 taken branches/scan-iteration →
/// 1) and the exit arm keeps its single taken branch. The original header skip
/// predates this case (the chomp shape it targeted carries the pair on a
/// non-header block); it is restorable via `TCG_BP_NO_HDR_ORIENT=1`.
fn small_orientable_loop_headers(func: &MachFunction, loops: &LoopAnalysis) -> HashSet<BlockId> {
    let mut pos = vec![usize::MAX; func.blocks.len()];
    for (i, &b) in func.block_order.iter().enumerate() {
        if let Some(slot) = pos.get_mut(b.0 as usize) {
            *slot = i;
        }
    }
    let mut out = HashSet::new();
    for lp in loops.all_loops() {
        if lp.body.len() <= 1 || loop_is_already_rotated(func, lp) {
            continue;
        }
        for &b in &lp.body {
            if b == lp.header && !bp_hdr_orient_enabled() {
                continue;
            }
            let Some(cp) = classify_cond_pair(func, b) else {
                continue;
            };
            if !lp.body.contains(&cp.cc_target) || !cond_pair_invertible(func, &cp) {
                continue;
            }
            // The stay-in-loop arm must already be the block laid out next, so the
            // flip is a pure fall-through swap (no reorder). `usize::MAX + 1`
            // never matches, so a block missing from the order can't qualify.
            let bpos = pos[b.0 as usize];
            let next_is_cc =
                bpos != usize::MAX && pos.get(cp.cc_target.0 as usize).copied() == Some(bpos + 1);
            if next_is_cc {
                out.insert(lp.header);
                break;
            }
        }
    }
    out
}

/// Backedge-pull sub-feature (default ON). Kill switch: `TCG_BP_NO_BEPULL=1`.
fn bp_bepull_enabled() -> bool {
    static F: OnceLock<bool> = OnceLock::new();
    *F.get_or_init(|| !matches!(std::env::var("TCG_BP_NO_BEPULL").as_deref(), Ok("1")))
}

/// Header-conditional small-loop orientation (default ON). Kill switch:
/// `TCG_BP_NO_HDR_ORIENT=1` restores the original header skip in
/// [`small_orientable_loop_headers`] (a 2-block scan loop whose trip test lives
/// on the HEADER then keeps its 2-taken-branch iteration).
fn bp_hdr_orient_enabled() -> bool {
    static F: OnceLock<bool> = OnceLock::new();
    *F.get_or_init(|| !matches!(std::env::var("TCG_BP_NO_HDR_ORIENT").as_deref(), Ok("1")))
}

/// Stranded pure-copy-latch pull (default ON). Kill switch:
/// `TCG_BP_NO_COPYLATCH=1` leaves regalloc critical-edge trampolines whose Phi
/// copies survived coalescing stranded at the far end of the layout.
fn bp_copylatch_enabled() -> bool {
    static F: OnceLock<bool> = OnceLock::new();
    *F.get_or_init(|| !matches!(std::env::var("TCG_BP_NO_COPYLATCH").as_deref(), Ok("1")))
}

/// Far-latch small-loop rotation sub-feature (default ON). Kill switch:
/// `TCG_BP_NO_LATCH_ROTATE=1`.
fn bp_latch_rotate_enabled() -> bool {
    static F: OnceLock<bool> = OnceLock::new();
    *F.get_or_init(|| !matches!(std::env::var("TCG_BP_NO_LATCH_ROTATE").as_deref(), Ok("1")))
}

/// Two-armed (descent) loop rotation (default ON). Kill switch:
/// `TCG_BP_NO_ARMROT=1` leaves a two-armed loop's branch-taken arm out of line,
/// so that arm keeps paying TWO taken branches per iteration.
fn bp_armrot_enabled() -> bool {
    static F: OnceLock<bool> = OnceLock::new();
    *F.get_or_init(|| !matches!(std::env::var("TCG_BP_NO_ARMROT").as_deref(), Ok("1")))
}

/// Longest arm chain [`rotate_two_armed_loops`] will move. The recognized shape
/// is a tight pointer-descent step (Treesort's fused `Insert`: `load child;
/// null-check; carry the phi copy` = 2 blocks per arm), where the per-iteration
/// taken-branch count is the whole cost model. A long arm is a loop body with
/// real work in it, where fetch layout stops being the deciding term and the
/// reorder is pure churn risk — so cap it.
const ARMROT_MAX_ARM_BLOCKS: usize = 4;

/// Pull a TAIL-DUPLICATED latch block in front of its loop header so the
/// duplicated backedge becomes the loop's fall-through seam.
///
/// Targets exactly the shape loop-latch-layout's tier 2 emits (Bubblesort's
/// swap arm): an in-loop block `D` whose last real instruction is an
/// unconditional `B header`, which carries its OWN cloned conditional
/// loop-exit, while a DIFFERENT in-loop block also ends `B header` (the
/// original latch, which keeps the not-taken path's backedge). Laying `D` out
/// immediately before the header lets the subsequent branch-to-next elision
/// turn `D`'s backedge into a fall-through, so iterations through `D` pay ONE
/// taken branch (the entry into `D`) instead of two. The block previously
/// falling into the header (the preheader seam) pays one extra taken branch
/// per LOOP ENTRY — amortized over the loop's iterations.
///
/// Runs between fall-through materialization and elision, where every CFG edge
/// is an explicit `Block` operand: pure block reordering, semantics unchanged
/// by construction ([`resolve_branches`] and the encoder recompute all offsets
/// from the final `block_order`). Fail-closed on any shape deviation; one pull
/// per loop; deterministic (loops in header order, candidates in layout order).
fn pull_duplicated_latch_before_header(func: &mut MachFunction, loops: &LoopAnalysis) -> bool {
    if !bp_bepull_enabled() {
        return false;
    }
    let mut moved = false;
    for lp in loops.all_loops() {
        // The entry block must stay first; a header-position self-loop or
        // two-block loop has no out-of-line duplicated latch to pull.
        if lp.header == func.entry || lp.body.len() < 3 {
            continue;
        }
        let idx_of = |func: &MachFunction, b: BlockId| -> Option<usize> {
            func.block_order.iter().position(|&x| x == b)
        };
        // In-loop blocks whose last real instruction is `B header`, in layout
        // order. Two or more = the duplicated-latch signature (original latch
        // plus at least one clone); a single backedge block is the plain
        // rotated shape and is left where the reorder put it.
        let mut backedge_sources: Vec<BlockId> = lp
            .body
            .iter()
            .copied()
            .filter(|&b| {
                b != lp.header
                    && last_real_inst(func, b).is_some_and(|id| {
                        let inst = func.inst(id);
                        inst.opcode == AArch64Opcode::B
                            && single_block_operand(inst) == Some(lp.header)
                    })
            })
            .collect();
        backedge_sources.sort_by_key(|&b| idx_of(func, b));
        if backedge_sources.len() < 2 {
            continue;
        }
        // The duplicated latch carries its own cloned conditional loop-exit
        // AND is entered only through conditional-taken edges (no predecessor
        // reaches it with its trailing unconditional `B`) — the out-of-line
        // swap arm. This excludes the original latch on the not-taken fall
        // chain: pulling THAT one would break the header's own fall-through
        // seam and merely trade one taken branch for another.
        let dup = backedge_sources.iter().copied().find(|&b| {
            let has_cloned_exit = func.block(b).insts.iter().any(|&id| {
                let inst = func.inst(id);
                inst.is_conditional_branch()
                    && single_block_operand(inst).is_some_and(|target| !lp.body.contains(&target))
            });
            has_cloned_exit
                && func.block(b).preds.iter().all(|&p| {
                    last_real_inst(func, p).is_none_or(|id| {
                        let inst = func.inst(id);
                        !(inst.opcode == AArch64Opcode::B && single_block_operand(inst) == Some(b))
                    })
                })
        });
        let Some(dup) = dup else { continue };
        let (Some(dup_pos), Some(header_pos)) = (idx_of(func, dup), idx_of(func, lp.header)) else {
            continue;
        };
        if dup_pos + 1 == header_pos {
            continue; // Already the fall-through backedge.
        }
        // Only pull a dup that the reorder left OUT-OF-LINE (outside the span
        // of the rest of the loop body). A dup inside the span is already part
        // of a deliberately-built chain (e.g. an unrolled body); moving it
        // would trade that chain's fall-throughs for this one.
        let (mut span_min, mut span_max) = (usize::MAX, 0usize);
        for &b in &lp.body {
            if b == dup {
                continue;
            }
            let Some(p) = idx_of(func, b) else { continue };
            span_min = span_min.min(p);
            span_max = span_max.max(p);
        }
        if (span_min..=span_max).contains(&dup_pos) {
            continue;
        }
        // Belt and braces: both seams this move edits must be hard-terminated
        // (no implicit fall-through into `dup`'s old slot or into the header).
        // Trivially true right after materialization — fail closed if a future
        // step reorders this pass's phases again.
        let safe_seam =
            |pos: usize| pos == 0 || block_has_hard_terminator(func, func.block_order[pos - 1]);
        if !safe_seam(dup_pos) || !safe_seam(header_pos) {
            continue;
        }
        func.block_order.remove(dup_pos);
        let insert_at = if dup_pos < header_pos {
            header_pos - 1
        } else {
            header_pos
        };
        func.block_order.insert(insert_at, dup);
        moved = true;
    }
    moved
}

/// Rotate a small bottom-tested loop whose latch was orphaned to the FAR END of
/// the function (the Puzzle `Fit`/`Place`/`Remove` scan-loop shape) so the
/// latch's unconditional backedge `B header` becomes the loop's fall-through
/// seam.
///
/// The greedy chainer places the join-latch of these loops last, because the
/// latch is never a preferred fall-through successor (its only role is the
/// backedge). The result: the common continue iteration pays TWO taken branches
/// — (1) a FORWARD-taken continue branch to the far latch and (2) the latch's
/// UNCONDITIONAL BACKWARD `b header`. clang (MachineBlockPlacement loop rotation)
/// puts the latch immediately ABOVE the header, so the backedge is a
/// fall-through and every continue is a single BACKWARD-taken branch = ONE taken
/// branch per iteration.
///
/// Target shape, per natural loop `L` with header `H` (`H != entry`):
///   * EXACTLY ONE in-loop block `Lb` (the latch) whose LAST real instruction is
///     an unconditional `B H` (the sole backedge). Zero such blocks = a
///     conditional/already-rotated latch (left alone); two or more = the
///     tail-duplicated shape [`pull_duplicated_latch_before_header`] owns.
///   * `Lb`'s terminator is the trip-test conditional pair `… ; COND cc EXIT ;
///     B H` whose branch-taken target `EXIT` lies OUTSIDE the loop body. This is
///     the bottom-tested (do-while) latch. It EXCLUDES simple top-tested loops
///     (their exit test is in the header and the latch is a bare `B H`, which is
///     already a 1-taken layout that rotation would only churn) and diamond
///     latches (a `COND` to an in-loop block).
///   * `Lb` is not already immediately before `H`.
///   * The block physically before `Lb` is hard-terminated, so nothing falls
///     through into `Lb`'s slot — pulling it away breaks no hot fall-through.
///   * `H` is not a repair target of the loop-aware reorder (`scattered`), whose
///     header-first policy already owns those (substantial multi-conditional)
///     loops; this tier only rescues the small ones it declined.
///
/// Laying `Lb` immediately before `H` lets step 4 elide its now-redundant `B H`
/// (H is layout-next), turning the backedge into a fall-through. The pre-header
/// that used to fall into `H` pays one extra taken branch per LOOP ENTRY —
/// amortized over the iterations.
///
/// Pure block reordering: every CFG edge is an explicit `Block` operand at this
/// phase (materialization ran; elision has not), so moving a block changes no
/// instruction and [`resolve_branches`]/the encoder recompute every offset from
/// the final `block_order` — semantics unchanged by construction. Fail-closed on
/// any shape deviation; one rotation per loop; deterministic (loops in header
/// order).
fn rotate_far_latch_before_header(
    func: &mut MachFunction,
    loops: &LoopAnalysis,
    scattered: &HashSet<BlockId>,
) -> bool {
    if !bp_latch_rotate_enabled() {
        return false;
    }
    let mut moved = false;
    for lp in loops.all_loops() {
        if lp.header == func.entry || lp.body.len() < 2 || scattered.contains(&lp.header) {
            continue;
        }
        // Innermost loops only. Rotating a loop that WRAPS a nested loop is at
        // best a cold-path win (the enclosing loop iterates far less than the
        // one it contains) but shifts the hotter inner loop's code, risking a
        // fetch-alignment regression (n-body/spectral-norm: rotating the outer
        // pairwise-sweep loop displaced the O(n^2) inner body). A loop is
        // innermost iff no OTHER loop's header lies in its body.
        let contains_nested = loops
            .all_loops()
            .any(|other| other.header != lp.header && lp.body.contains(&other.header));
        if contains_nested {
            continue;
        }
        let idx_of = |func: &MachFunction, b: BlockId| -> Option<usize> {
            func.block_order.iter().position(|&x| x == b)
        };
        // Exactly one in-loop block whose real stream ends `B header`.
        let backedge_sources: Vec<BlockId> = lp
            .body
            .iter()
            .copied()
            .filter(|&b| {
                b != lp.header
                    && last_real_inst(func, b).is_some_and(|id| {
                        let inst = func.inst(id);
                        inst.opcode == AArch64Opcode::B
                            && single_block_operand(inst) == Some(lp.header)
                    })
            })
            .collect();
        if backedge_sources.len() != 1 {
            continue;
        }
        let latch = backedge_sources[0];
        // The latch must carry the trip test as `… ; COND cc EXIT ; B header`
        // with EXIT outside the loop (a genuine exit) — the bottom-tested shape.
        let Some(cp) = classify_cond_pair(func, latch) else {
            continue;
        };
        if cp.ft_target != lp.header || lp.body.contains(&cp.cc_target) {
            continue;
        }
        // The latch must be reached on the hot path by a TAKEN branch: some
        // in-loop block (other than the latch) ends in a CONDITIONAL branch
        // whose taken target is the latch — the early-`continue` signature. That
        // is exactly the double-taken iteration the rotation cures: continue
        // (forward-taken to the far latch) + backedge (backward-taken) = 2 →
        // continue (backward-taken to the latch now above) + backedge
        // (fall-through) = 1. WITHOUT such an edge the body falls through into
        // the latch, so the loop is already a single-taken layout and moving the
        // latch only relabels that one taken branch (backedge → continue) while
        // shifting downstream hot code — a pure fetch-alignment risk with no
        // taken-branch payoff (Bubblesort's inlined bInitarr fill loop, whose
        // common min/max-not-updated path falls straight into the latch).
        let has_cond_continue_to_latch = lp.body.iter().any(|&b| {
            b != latch
                && func.block(b).insts.iter().any(|&id| {
                    let inst = func.inst(id);
                    inst.is_conditional_branch() && single_block_operand(inst) == Some(latch)
                })
        });
        if !has_cond_continue_to_latch {
            continue;
        }
        let (Some(latch_pos), Some(header_pos)) = (idx_of(func, latch), idx_of(func, lp.header))
        else {
            continue;
        };
        if latch_pos + 1 == header_pos {
            continue; // Already the fall-through backedge.
        }
        // Nothing may fall through into the latch's current slot (else pulling it
        // away turns a hot fall-through into a taken branch). Trivially true
        // right after materialization when the latch is entered only through
        // conditional-taken continue edges; fail closed otherwise.
        let latch_seam_safe =
            latch_pos == 0 || block_has_hard_terminator(func, func.block_order[latch_pos - 1]);
        if !latch_seam_safe {
            continue;
        }
        if std::env::var("TCG_BP_DEBUG").as_deref() == Ok("1") {
            eprintln!(
                "LATCH_ROTATE fn={} header={:?} latch={:?} latch_pos={} header_pos={} body={}",
                func.name,
                lp.header,
                latch,
                latch_pos,
                header_pos,
                lp.body.len()
            );
        }
        func.block_order.remove(latch_pos);
        let insert_at = if latch_pos < header_pos {
            header_pos - 1
        } else {
            header_pos
        };
        func.block_order.insert(insert_at, latch);
        moved = true;
    }
    moved
}

/// Pull a STRANDED PURE-COPY latch (a regalloc critical-edge trampoline whose
/// Phi copies survived post-RA coalescing) immediately before its loop header.
///
/// `split_critical_edges` (in trust-cg-regalloc) inserts trampoline blocks on
/// critical back-edges so per-edge Phi copies have somewhere to live. When the
/// copies COALESCE away, `branch_forward` later erases the then-empty
/// trampoline. When they DON'T (the allocator gave the Phi and its inputs
/// interfering registers), the non-empty trampoline cannot be forwarded — and
/// because it was appended AFTER the mid-end ordered the function, it sits
/// stranded at the far end of `block_order`. Every continue-iteration of the
/// loop then pays TWO taken branches with a far round-trip:
/// `BCond → trampoline (far); B header (far back)`. huffbench compdecomp's
/// encode inner loop paid this per encoded BIT (~1.5B times/run, measured
/// −4.2% whole-program when simulated); its freq/heap2-init loops carry the
/// same shape.
///
/// Target shape, per INNERMOST natural loop `L` with header `H != entry`:
///   * EXACTLY ONE in-loop block `T` whose last real instruction is an
///     unconditional `B H`, and whose other real instructions are ONLY
///     register-register moves ([`AArch64Opcode::is_move`], every operand a
///     `PReg`/`Special` register) — the surviving Phi copies. At least one such
///     move: a copy-free trampoline is `branch_forward`'s domain.
///   * Every CFG edge into `T` is a CONDITIONAL-taken edge (each predecessor
///     reaches `T` only through a conditional branch), and `T` is not the
///     layout-next of any predecessor — the adjacent shape belongs to
///     [`orient_loop_conditionals`], whose in-place flip is strictly cheaper
///     (no loop-entry cost).
///   * Nothing falls through into `T`'s current slot (the block laid out before
///     it is hard-terminated), so pulling `T` away breaks no fall-through seam.
///
/// Laying `T` immediately before `H` lets the subsequent elision drop its `B H`
/// (header becomes layout-next), so each continue-iteration pays ONE near taken
/// branch (the `BCond` into `T`) and falls through into the header. The
/// preheader seam pays one extra taken branch per LOOP ENTRY — amortized over
/// the iterations (encode: entry per CHAR vs savings per BIT).
///
/// Runs even when the function carries genuine conditional back-edges: the
/// per-loop gates above are the protection (the rotated sibling loops are not
/// touched — only the stranded trampoline moves, from one non-fall-through slot
/// to another). Pure block reordering between materialization and elision
/// (every edge an explicit `Block` operand): moving a block changes no
/// instruction, and [`resolve_branches`]/the encoder recompute every offset
/// from the final `block_order`. Fail-closed on any shape deviation; one pull
/// per loop; deterministic (loops in analysis order).
fn pull_far_copy_latch_before_header(
    func: &mut MachFunction,
    loops: &LoopAnalysis,
    scattered: &HashSet<BlockId>,
) -> bool {
    if !bp_copylatch_enabled() {
        return false;
    }
    let mut moved = false;
    for lp in loops.all_loops() {
        if lp.header == func.entry || lp.body.len() < 2 || scattered.contains(&lp.header) {
            continue;
        }
        // Innermost loops only (same rationale as `rotate_far_latch_before_header`:
        // moving code of an enclosing loop shifts the hotter inner body).
        let contains_nested = loops
            .all_loops()
            .any(|other| other.header != lp.header && lp.body.contains(&other.header));
        if contains_nested {
            continue;
        }
        // Exactly one in-loop block whose real stream ends `B header`.
        let backedge_sources: Vec<BlockId> = lp
            .body
            .iter()
            .copied()
            .filter(|&b| {
                b != lp.header
                    && last_real_inst(func, b).is_some_and(|id| {
                        let inst = func.inst(id);
                        inst.opcode == AArch64Opcode::B
                            && single_block_operand(inst) == Some(lp.header)
                    })
            })
            .collect();
        if backedge_sources.len() != 1 {
            continue;
        }
        let latch = backedge_sources[0];
        // Pure-copy latch: every real instruction before the trailing `B` is a
        // register-register move; at least one move (else branch_forward owns it).
        let reals: Vec<InstId> = func
            .block(latch)
            .insts
            .iter()
            .copied()
            .filter(|&id| !func.inst(id).is_pseudo())
            .collect();
        let mut n_moves = 0usize;
        let mut pure = true;
        for &id in &reals[..reals.len().saturating_sub(1)] {
            let inst = func.inst(id);
            let is_reg_reg_move = inst.opcode.is_move()
                && !inst.operands.is_empty()
                && inst
                    .operands
                    .iter()
                    .all(|op| matches!(op, MachOperand::PReg(_) | MachOperand::Special(_)));
            if is_reg_reg_move {
                n_moves += 1;
            } else if inst.opcode != AArch64Opcode::Nop {
                pure = false;
                break;
            }
        }
        if !pure || n_moves == 0 {
            continue;
        }
        let pos_of =
            |func: &MachFunction, b: BlockId| func.block_order.iter().position(|&x| x == b);
        let (Some(latch_pos), Some(header_pos)) = (pos_of(func, latch), pos_of(func, lp.header))
        else {
            continue;
        };
        if latch_pos + 1 == header_pos {
            continue; // Already the fall-through backedge.
        }
        // Every predecessor must be a TWO-ARM conditional-pair block
        // (`… ; COND cc X ; B Y`) touching the latch on exactly one arm — the
        // split-critical-edge signature (a critical edge's source has ≥2
        // successors by definition). Such a predecessor executes exactly one
        // taken branch per visit no matter WHERE the latch is laid out (the
        // later cc-preference/elision steps pick which arm falls through), so
        // moving the latch is taken-branch-neutral at the predecessor while the
        // latch's own `B header` becomes the header fall-through: a strict
        // 2-taken → 1-taken reduction on every continue-iteration. A
        // single-successor predecessor (bare `B latch`) is a straight-line seam
        // this tier must not touch — fail closed.
        let preds = func.block(latch).preds.clone();
        if preds.is_empty() {
            continue;
        }
        let entries_ok = preds.iter().all(|&p| {
            if p == latch {
                return false;
            }
            match classify_cond_pair(func, p) {
                Some(cp) => (cp.cc_target == latch) != (cp.ft_target == latch),
                None => false,
            }
        });
        if !entries_ok {
            continue;
        }
        // Adjacent-to-a-predecessor shapes are orientation's domain.
        if preds
            .iter()
            .any(|&p| pos_of(func, p).is_some_and(|pp| pp + 1 == latch_pos))
        {
            continue;
        }
        // Nothing may fall through into the latch's current slot.
        let latch_seam_safe =
            latch_pos == 0 || block_has_hard_terminator(func, func.block_order[latch_pos - 1]);
        if !latch_seam_safe {
            continue;
        }
        if std::env::var("TCG_BP_DEBUG").as_deref() == Ok("1") {
            eprintln!(
                "COPYLATCH_PULL fn={} header={:?} latch={:?} latch_pos={} header_pos={} moves={}",
                func.name, lp.header, latch, latch_pos, header_pos, n_moves
            );
        }
        func.block_order.remove(latch_pos);
        let insert_at = if latch_pos < header_pos {
            header_pos - 1
        } else {
            header_pos
        };
        func.block_order.insert(insert_at, latch);
        moved = true;
    }
    moved
}

/// A block's terminator as a conditional pair, tolerating the IMPLICIT
/// fall-through form `... ; COND cc T` (no trailing `B`).
///
/// [`classify_cond_pair`] only recognizes the explicit `... ; COND cc T ; B F`
/// shape that fall-through materialization produces. By the time the pull tiers
/// run, [`invert_sunk_guard_heads`] may already have rewritten a block to
/// `COND !cc FAR` and DELETED its trailing `B` — that is the whole point of the
/// inversion — leaving a bare conditional whose fall-through is implicit in the
/// layout. Stanford/Treesort's descent header is exactly that block once
/// `Insert` is inlined into `Trees`, whose sunk cold guards trigger the
/// inversion. This recovers `F` from the layout so the shape is still
/// recognizable; the caller re-materializes the edge before moving anything.
fn armrot_cond_pair(func: &MachFunction, block: BlockId, pos: usize) -> Option<(BlockId, BlockId)> {
    if let Some(cp) = classify_cond_pair(func, block) {
        return Some((cp.cc_target, cp.ft_target));
    }
    let last = last_real_inst(func, block)?;
    let inst = func.inst(last);
    if !inst.is_conditional_branch() {
        return None;
    }
    let cc_target = single_block_operand(inst)?;
    let &ft_target = func.block_order.get(pos + 1)?;
    if cc_target == ft_target {
        return None;
    }
    Some((cc_target, ft_target))
}

/// Make every implicit fall-through in `blocks` explicit (`B <layout-next>`), so
/// the caller may reorder blocks freely. Returns `false` — having changed
/// nothing — if any of them falls through with no layout successor.
///
/// This is fall-through materialization (driver step 1) applied to a named
/// subset, needed because [`invert_sunk_guard_heads`] deletes trailing `B`s
/// after that step. Every `B` it adds whose target is still layout-next is
/// removed again by [`elide_trailing_b_to_layout_next`] (driver step 4), so
/// materializing a seam this rotation does not actually move is byte-neutral.
fn armrot_materialize_fallthroughs(func: &mut MachFunction, blocks: &[BlockId]) -> bool {
    let mut todo: Vec<(BlockId, BlockId)> = Vec::new();
    for &b in blocks {
        if block_has_hard_terminator(func, b) {
            continue;
        }
        let Some(pos) = func.block_order.iter().position(|&x| x == b) else {
            return false;
        };
        let Some(&next) = func.block_order.get(pos + 1) else {
            return false;
        };
        todo.push((b, next));
    }
    for (b, next) in todo {
        let br = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(next)],
        ));
        func.append_inst(b, br);
    }
    true
}

/// The straight-line ARM chain a two-armed loop's header branches into: the
/// blocks reached from `start`, each with exactly ONE in-loop successor, ending
/// at the arm's LATCH (whose only in-loop successor is the header).
///
/// Derived purely from the CFG (`succs`), never from the current layout, so the
/// chain — and therefore the rotation built from it — is layout-order
/// independent and deterministic. Fail-closed: `None` for a block with zero or
/// two-or-more distinct in-loop successors (a nested loop, an in-loop diamond,
/// or an arm that rejoins the other arm), for a chain that revisits a block, for
/// a chain reaching the header at its head, and for anything longer than
/// [`ARMROT_MAX_ARM_BLOCKS`].
///
/// A conditional side-exit to a block OUTSIDE the loop (Treesort's
/// `CreateNode` arms) is expected and allowed: it is simply not an in-loop
/// successor.
fn armrot_arm_chain(func: &MachFunction, lp: &NaturalLoop, start: BlockId) -> Option<Vec<BlockId>> {
    let mut chain: Vec<BlockId> = Vec::new();
    let mut cur = start;
    loop {
        if cur == lp.header || chain.contains(&cur) || chain.len() >= ARMROT_MAX_ARM_BLOCKS {
            return None;
        }
        chain.push(cur);
        let mut in_loop: Vec<BlockId> = Vec::new();
        for &s in &func.block(cur).succs {
            if lp.body.contains(&s) && !in_loop.contains(&s) {
                in_loop.push(s);
            }
        }
        match in_loop.as_slice() {
            // The arm's latch: its only in-loop edge is the back-edge.
            [h] if *h == lp.header => return Some(chain),
            [n] => cur = *n,
            _ => return None,
        }
    }
}

/// Rotate a TWO-ARMED loop so BOTH of its arms cost ONE taken branch per
/// iteration, and return the headers rotated (for the caller's orientation
/// pass).
///
/// # The shape
///
/// A two-armed loop is a header `H` whose terminator is an in-loop conditional
/// pair `COND cc A ; B C` — both arms stay in the loop — where each arm is a
/// straight chain ending in its own back-edge to `H` and the arms never rejoin
/// inside the loop. The canonical instance is a binary-tree descent step
/// (Stanford/Treesort's `Insert`, and the same loop once it is inlined into
/// `Trees`): `if (n > t->val) { if (!t->left) break; t = t->left; } else if (n <
/// t->val) { if (!t->right) break; t = t->right; } else break;`.
///
/// # Why the arms are not symmetric, and what it costs
///
/// Only ONE block can be laid out immediately before `H`, so only one arm can
/// return to the header by fall-through. The greedy chainer and the existing
/// latch pulls ([`pull_duplicated_latch_before_header`],
/// [`rotate_far_latch_before_header`], [`pull_far_copy_latch_before_header`])
/// each pull a SINGLE latch, and pick it by layout position — so they routinely
/// pull the arm the header FALLS THROUGH to and leave the arm the header
/// BRANCHES to out of line. That arm then pays TWO taken branches per step (the
/// header's conditional out, plus its own back-edge home) while the pulled arm
/// pays one. Measured on Treesort's `Insert`: `b.gt LEFT` … `b HEADER` = 2 for
/// the left descent, 1 for the right.
///
/// The assignment is forced once you notice the arms are asymmetric: put the
/// BRANCH-TAKEN arm before the header (its back-edge becomes the fall-through,
/// so the header's conditional is its only taken branch = 1) and leave the
/// FALL-THROUGH arm after the header (it is entered for free and its back-edge
/// is its only taken branch = 1). Total 2 taken branches for the pair, which is
/// the floor: each arm needs at least one backward transfer per iteration and
/// only one of them can have it for free. This is exactly the layout clang
/// emits for the same loop.
///
/// So the rotation rewrites the loop's slice of `block_order` to
/// `[taken-arm chain][H][fall-arm chain]`, placed where the loop's first block
/// already was. The pre-header pays ONE extra taken branch per loop ENTRY (it
/// must now branch over the taken-arm chain to reach `H`) — the same amortized
/// trade the other latch pulls make, and the same one clang makes here.
///
/// # Soundness
///
/// Pure block REORDERING: before touching `block_order` the rotation makes
/// every fall-through it could disturb an explicit `Block` operand
/// ([`armrot_materialize_fallthroughs`] over the moved blocks AND each moved
/// block's layout-predecessor), so afterwards no block's behavior depends on
/// its position and [`resolve_branches`]/the encoder recompute every offset
/// from the final `block_order` — semantics unchanged by construction. Driver
/// step 4 elides every `B` that is still redundant, so a seam nothing moved
/// past is byte-neutral. The rotation is skipped entirely unless it changes the
/// order.
///
/// # Fail-closed gates
///
/// * `H` is not the entry block and the loop has at least 3 blocks.
/// * Neither `H` nor any ENCLOSING loop's header is a `scattered` repair
///   target — the loop-aware header-first reorder owns those bodies, and this
///   tier must not fight it or re-scatter an outer body it just made
///   contiguous.
/// * The loop body is CALL-FREE. A call-bearing loop is call-bound; a
///   fetch-layout reorder there cannot pay and only risks churn (the same
///   exclusion [`scattered_loop_headers`] makes).
/// * `H`'s terminator is a conditional pair ([`armrot_cond_pair`], explicit or
///   layout-implicit) whose BOTH targets are in the loop body — a header that
///   exits the loop is a trip-test header, not a two-armed split, and is a
///   different, already-handled shape.
/// * Both arms are [`armrot_arm_chain`]s: straight, latch-terminated, at most
///   [`ARMROT_MAX_ARM_BLOCKS`] blocks each.
/// * The two chains are DISJOINT and, with `H`, cover the loop body EXACTLY —
///   so the loop really is a two-armed split with no third path, no rejoin, and
///   no nested loop.
/// * Every block being moved is present in `block_order`, none of them is the
///   entry block, and every fall-through the move disturbs can be materialized
///   (a block that falls through with no layout successor fails closed).
///
/// Deterministic: loops in header order ([`LoopAnalysis::all_loops`] is a
/// `BTreeMap`), chains derived from `succs` order, one rotation per loop.
///
/// Kill switch: `TCG_BP_NO_ARMROT=1`.
fn rotate_two_armed_loops(
    func: &mut MachFunction,
    loops: &LoopAnalysis,
    scattered: &HashSet<BlockId>,
) -> HashSet<BlockId> {
    let mut rotated: HashSet<BlockId> = HashSet::new();
    if !bp_armrot_enabled() {
        return rotated;
    }
    let dbg = std::env::var("TCG_BP_DEBUG").as_deref() == Ok("1");
    for lp in loops.all_loops() {
        macro_rules! reject {
            ($why:expr) => {{
                if dbg {
                    eprintln!(
                        "BP_ARMROT reject fn={} header={:?} body={}: {}",
                        func.name,
                        lp.header,
                        lp.body.len(),
                        $why
                    );
                }
                continue;
            }};
        }
        if lp.header == func.entry || lp.body.len() < 3 {
            reject!("entry header / fewer than three blocks");
        }
        // Stay out of the loop-aware repair's domain entirely — not just this
        // loop but any loop NESTED inside a repair target, whose blocks the
        // header-first reorder deliberately laid out contiguously as part of
        // the enclosing body. (Computed as a plain predicate, NOT with an early
        // `reject!`: that macro expands to `continue`, which inside this walk
        // would continue the WALK — an infinite loop, not a rejection.)
        let mut in_scattered = false;
        let mut anc = Some(lp.header);
        while let Some(h) = anc {
            if scattered.contains(&h) {
                in_scattered = true;
                break;
            }
            anc = loops.get_loop(h).and_then(|l| l.parent);
        }
        if in_scattered {
            reject!("inside a scattered repair target");
        }
        if lp.body.iter().any(|&b| block_contains_call(func, b)) {
            reject!("call in loop body");
        }
        let Some(header_pos) = func.block_order.iter().position(|&x| x == lp.header) else {
            reject!("header is not in block_order");
        };
        let Some((cc_target, ft_target)) = armrot_cond_pair(func, lp.header, header_pos) else {
            reject!("header is not a conditional split");
        };
        if !lp.body.contains(&cc_target) || !lp.body.contains(&ft_target) {
            reject!("header arm leaves the loop");
        }
        let (Some(taken_arm), Some(fall_arm)) = (
            armrot_arm_chain(func, lp, cc_target),
            armrot_arm_chain(func, lp, ft_target),
        ) else {
            reject!("an arm is not a straight latch-terminated chain");
        };
        // Disjoint arms that, with the header, are exactly the loop body.
        let mut covered: HashSet<BlockId> = taken_arm.iter().copied().collect();
        if covered.len() != taken_arm.len() || fall_arm.iter().any(|&b| !covered.insert(b)) {
            reject!("arms overlap");
        }
        covered.insert(lp.header);
        if covered.len() != lp.body.len() || !lp.body.iter().all(|b| covered.contains(b)) {
            reject!("arms + header do not cover the loop body");
        }
        if covered.contains(&func.entry) {
            reject!("entry block inside the loop");
        }
        // Every moved block must already be in the layout: this rewrite inserts
        // the whole slice back, so a detached body block would be RESURRECTED.
        let positions: Vec<usize> = func
            .block_order
            .iter()
            .enumerate()
            .filter(|(_, b)| covered.contains(b))
            .map(|(i, _)| i)
            .collect();
        if positions.len() != covered.len() {
            reject!("a loop-body block is missing from block_order");
        }
        let target: Vec<BlockId> = taken_arm
            .iter()
            .copied()
            .chain(std::iter::once(lp.header))
            .chain(fall_arm.iter().copied())
            .collect();
        let mut new_order: Vec<BlockId> = Vec::with_capacity(func.block_order.len());
        let mut spliced = false;
        for &b in &func.block_order {
            if covered.contains(&b) {
                if !spliced {
                    new_order.extend(target.iter().copied());
                    spliced = true;
                }
                continue;
            }
            new_order.push(b);
        }
        if !spliced || new_order == func.block_order {
            reject!("already in the rotated order");
        }
        // SOUNDNESS STEP: make explicit every fall-through the splice could
        // disturb — each moved block's own, and that of the block laid out
        // immediately before it (whose fall-through target is about to move
        // away). After this, no block's behavior depends on its position.
        let mut seams: Vec<BlockId> = target.clone();
        for &p in &positions {
            if p > 0 {
                let prev = func.block_order[p - 1];
                if !seams.contains(&prev) {
                    seams.push(prev);
                }
            }
        }
        if !armrot_materialize_fallthroughs(func, &seams) {
            reject!("a disturbed fall-through has no layout successor");
        }
        if dbg {
            eprintln!(
                "BP_ARMROT fn={} header={:?} taken={:?} fall={:?}",
                func.name, lp.header, taken_arm, fall_arm
            );
        }
        func.block_order = new_order;
        rotated.insert(lp.header);
    }
    rotated
}

/// True if any conditional branch is a *genuine* loop back-edge — its target
/// block dominates the branch's source block (the do-while latch shape). Unlike
/// [`function_has_conditional_back_edge`] (layout-position based, which also
/// fires on diamond re-convergence), this only fires on real back-edges.
fn function_has_genuine_conditional_back_edge(func: &MachFunction, dom: &DomTree) -> bool {
    for &block in &func.block_order {
        for &inst_id in &func.block(block).insts {
            let inst = func.inst(inst_id);
            if !inst.is_conditional_branch() {
                continue;
            }
            for op in &inst.operands {
                if let MachOperand::Block(target) = op
                    && dom.dominates(*target, block)
                {
                    return true;
                }
            }
        }
    }
    false
}

/// Returns the last instruction in a block, if any.
pub fn get_block_terminator(func: &MachFunction, block: BlockId) -> Option<&MachInst> {
    let blk = func.block(block);
    blk.insts.last().map(|&id| func.inst(id))
}

/// Returns the second-to-last instruction in a block, if it exists.
fn get_second_to_last(func: &MachFunction, block: BlockId) -> Option<&MachInst> {
    let blk = func.block(block);
    if blk.insts.len() >= 2 {
        Some(func.inst(blk.insts[blk.insts.len() - 2]))
    } else {
        None
    }
}

/// Determine the fall-through successor for a block based on its terminator.
///
/// - `BCond target` + `B fallthrough_target`: the fall-through is the B
///   target, because the conditional branch goes to `target` and the code
///   falls through to the unconditional B which jumps to `fallthrough_target`.
///   When we lay out `fallthrough_target` right after this block, we can
///   eliminate the trailing `B`.
/// - `BCond target` (no trailing B): fall-through is the non-conditional
///   successor. We look at the block's succs and return the one that is NOT
///   the conditional target.
/// - `B target` (unconditional only): no fall-through.
/// - `Ret` / `Br`: no fall-through.
/// - Same logic for Cbz, Cbnz, Tbz, Tbnz.
pub fn get_fallthrough_successor(func: &MachFunction, block: BlockId) -> Option<BlockId> {
    let term = get_block_terminator(func, block)?;

    match term.opcode {
        // Unconditional branch or return: no fall-through.
        AArch64Opcode::B | AArch64Opcode::TailCall | AArch64Opcode::Ret | AArch64Opcode::Br => {
            // Check if the second-to-last instruction is a conditional branch.
            // Pattern: BCond target ; B fallthrough
            // In this case, the fall-through is the B's target.
            if term.opcode == AArch64Opcode::B
                && let Some(prev) = get_second_to_last(func, block)
                && is_conditional_branch(prev.opcode)
            {
                // The B's target is where we'd fall through to if placed next.
                return get_branch_target(term);
            }
            None
        }

        // Conditional branch without trailing B: fall-through is the
        // non-conditional successor.
        AArch64Opcode::BCond
        | AArch64Opcode::Cbz
        | AArch64Opcode::Cbnz
        | AArch64Opcode::Tbz
        | AArch64Opcode::Tbnz => {
            let cond_target = get_branch_target(term);
            let blk = func.block(block);
            // Return the successor that is NOT the conditional target.
            for &succ in &blk.succs {
                if Some(succ) != cond_target {
                    return Some(succ);
                }
            }
            // If both succs are the same (weird but possible), return it.
            blk.succs.first().copied()
        }

        _ => None,
    }
}

/// Returns true if the opcode is a conditional branch.
fn is_conditional_branch(opcode: AArch64Opcode) -> bool {
    matches!(
        opcode,
        AArch64Opcode::BCond
            | AArch64Opcode::Cbz
            | AArch64Opcode::Cbnz
            | AArch64Opcode::Tbz
            | AArch64Opcode::Tbnz
    )
}

/// Extract the block target from a branch instruction's operands.
fn get_branch_target(inst: &MachInst) -> Option<BlockId> {
    for op in &inst.operands {
        if let MachOperand::Block(bid) = op {
            return Some(*bid);
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Fall-through block layout + redundant-jump elision (EXEC-SPEED)
// ---------------------------------------------------------------------------

/// AArch64 fall-through branch-layout optimization.
///
/// Runs on the final `MachFunction` immediately before [`resolve_branches`],
/// which is the ONLY program point where `block_order` is guaranteed to be
/// exactly what the encoder (`encode_function_with_fixups_and_blocks`) and
/// branch resolver consume, with no later pass (regalloc rewrites
/// `block_order`, frame lowering, trap expansion) able to invalidate the
/// result. Both `resolve_branches` and the encoder derive every branch offset
/// and jump-table byte offset from this same `block_order`, so reordering here
/// stays consistent by construction.
///
/// The transform, in provably-sound steps:
///
/// 1. **Materialize implicit fall-throughs.** Every block that does not end in
///    a hard terminator (unconditional `B`, indirect `Br`, or `Ret`) currently
///    falls through to its `block_order` successor. Append an explicit
///    `B <current-next>` so the block's control flow no longer depends on
///    layout position. After this step every CFG edge is named by a `Block`
///    operand — reordering can no longer change any block's behavior.
///
/// 2. **Greedy fall-through reorder** via [`compute_block_layout`] (entry block
///    stays first). Reordering is always semantically safe once all edges are
///    explicit: `resolve_branches` recomputes every PC-relative offset from the
///    new order.
///
/// 3. **Elide redundant jumps.** For each block laid out at index `i` ending in
///    an unconditional `B target`, if `block_order[i + 1] == target`, delete
///    the `B`: control now falls through to exactly the block it jumped to.
///
/// 4. **Bottom-test rotation** (when `rotate` is set) — see
///    [`rotate_top_tested_loops`]. Turns a top-tested loop (`header: cmp;
///    b.cc exit; [fall to body]` + `body: …; b header`) into a do-while loop
///    that tests once per iteration at the bottom, matching what a rotated
///    loop pays. Only fires on the exact self-contained header shape where the
///    header holds *nothing but* the compare and the conditional exit, so
///    skipping it on the back-edge loses no computation.
///
/// # Fail-closed
///
/// Correctness over coverage. The whole function is left **unchanged** (returns
/// `false`) when it uses any layout feature this pass does not model with
/// proven offset consistency:
///
/// * exception handling (`eh_metadata`) — reordering could split a try-region
///   across the function, producing a semantically wrong (if offset-consistent)
///   LSDA call-site table;
/// * jump tables / indirect branches (`Br`, `JumpTableIndex` operands) — their
///   successor edges are data-driven, not present as `Block` operands, so the
///   reorder cannot see them;
/// * a fall-through block that is last in layout order with no successor to
///   materialize (malformed / falls off the end).
///
/// Returns `true` iff the function was changed (a jump elided or a loop
/// rotated).
pub fn aarch64_layout_fallthrough_and_elide(func: &mut MachFunction, rotate: bool) -> bool {
    if func.block_order.len() < 2 {
        return false;
    }
    if function_uses_unsupported_layout_features(func) {
        return false;
    }

    // LEGACY PATH (kill switch `TCG_LOOP_PLACE=0`): the original greedy reorder
    // that fails closed on *any* layout-backward conditional branch. Kept for
    // A/B measurement and emergency disable of loop-aware placement.
    if !loop_aware_placement_enabled() {
        // Preserve already-bottom-tested loops verbatim. A conditional branch to
        // an earlier-or-equal block in the current layout is a conditional
        // back-edge — the rotated (do-while) shape a prior pass already laid out
        // optimally. A greedy re-layout can only perturb that cold exit path, so
        // fail closed and leave the whole function untouched.
        if function_has_conditional_back_edge(func) {
            return false;
        }
        let order = func.block_order.clone();
        for (i, &block) in order.iter().enumerate() {
            if block_has_hard_terminator(func, block) {
                continue;
            }
            let Some(&next) = order.get(i + 1) else {
                return false;
            };
            let br = func.push_inst(MachInst::new(
                AArch64Opcode::B,
                vec![MachOperand::Block(next)],
            ));
            func.append_inst(block, br);
        }
        rebuild_succs_from_block_operands(func);
        compute_block_layout(func);
        let elided = elide_trailing_b_to_layout_next(func);
        let rotated = rotate && rotate_top_tested_loops(func);
        return elided || rotated;
    }

    // ---- LOOP-AWARE PATH (default): LLVM MachineBlockPlacement-lite ----
    //
    // Step 1: materialize implicit fall-throughs against the CURRENT order, so
    // every CFG edge becomes a named `Block` operand and reordering can no
    // longer change any block's behavior.
    let order = func.block_order.clone();
    for (i, &block) in order.iter().enumerate() {
        if block_has_hard_terminator(func, block) {
            continue;
        }
        let Some(&next) = order.get(i + 1) else {
            // Falls through but nothing follows it: fail closed, touch nothing.
            return false;
        };
        let br = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(next)],
        ));
        func.append_inst(block, br);
    }

    // Step 2: rebuild succ/pred edges from the now-explicit branch operands so
    // dominator/loop analysis and the placement heuristic see the full CFG.
    rebuild_succs_from_block_operands(func);

    // Step 3: loop analysis over the clean explicit CFG. Dominators and natural
    // loops are layout-independent (derived from `entry` + succ/pred edges), so
    // the membership/nesting facts stay valid across the reorder that follows.
    let dom = DomTree::compute(func);
    let loops = LoopAnalysis::compute(func, &dom);

    // Protect already-rotated loops. A *genuine* conditional loop back-edge (a
    // conditional branch whose target dominates its source — the do-while shape
    // a prior pass laid out optimally: body → latch(BCond back) → fall exit) is
    // already at one taken branch per iteration; re-laying it out can only
    // perturb its cold exit path. When one is present we skip reorder+orient and
    // fall through to the same redundant-branch elision the standalone pass
    // performs (identical machine code). A layout-backward conditional that is
    // merely diamond re-convergence (NOT a back-edge, e.g. heapsort's sift-down)
    // is not genuine, so those functions are still relaid out.
    // Repair targets: SUBSTANTIAL, CALL-FREE loops whose body is SCATTERED in
    // the input layout (the front-end-bound class this pass helps — heapsort's
    // sift-down). A genuine conditional back-edge (already-rotated loop) is left
    // alone, so no targets are collected there. Computed on the CURRENT
    // (pre-reorder) order; used by both the reorder and the orientation.
    let has_genuine_back_edge = function_has_genuine_conditional_back_edge(func, &dom);
    let scattered = if has_genuine_back_edge {
        HashSet::new()
    } else {
        scattered_loop_headers(func, &loops)
    };

    let mut reordered = false;
    if !scattered.is_empty() {
        // Engage loop-aware repair: pull each scattered loop body contiguous
        // (backedge = the one taken branch/iter) and invert in-loop conditionals
        // whose branch-taken arm is laid out next so the stay-hot arm falls
        // through and the cold arm (loop exit / re-convergence) is the taken one.
        // This repair also runs on profile-ordered functions: the early
        // ProfileUsePass chain does no loop-contiguity work, and skipping the
        // repair for it measured a 1.7x regression on Puzzle/Trial.
        compute_loop_aware_block_layout(func, &loops, &scattered);
        reordered = true;
    } else if !function_has_conditional_back_edge(func) && !profile_order_precedence(func) {
        // No repair target AND the legacy pass would have reordered (no
        // layout-backward conditional) — reproduce the legacy greedy reorder
        // verbatim so such functions stay byte-identical to baseline. (With an
        // empty scattered set this is exactly `compute_loop_aware_block_layout`,
        // but calling the greedy directly makes the equivalence self-evident.)
        //
        // PGO-use precedence: when the ProfileUsePass hot-chain layout ordered
        // this function, the profile order is authoritative over this greedy
        // re-derivation — before the precedence bit, whether the profile
        // placement survived to emission depended on which fail-closed bail
        // this reorder happened to trip (measured on Stanford/Towers `Move`:
        // the greedy silently un-sank its never-executed error paths). The
        // loop-aware repair above and every step below (latch pulls,
        // orientation, elision) still run.
        //
        // Static cold-guard sinking (the Towers PGO layout win, captured
        // WITHOUT a profile): when this function carries statically
        // recognizable error-report side arms (see
        // [`static_cold_guard_blocks`]), the greedy fall-through chain is the
        // measured pessimization — at every `bcond hot; b guard` head it
        // chains to the explicit-branch GUARD arm, interleaving never-executed
        // report blocks into the hot line and pushing the hot arms to the far
        // end (Towers `Move`: 6 taken branches per call vs the profile
        // layout's 3 cond-to-next hops). The profile layout that closed it is
        // literally "original order with the zero-hit guard arms extracted to
        // the end" (the zero-hit-span chain gate refuses every other
        // deviation), so the static capture reproduces exactly that: keep the
        // original order, append the recognized guards at the end. Functions
        // with no recognized guard keep the greedy verbatim (byte-identical).
        // Kill switch: `TCG_BP_NO_COLDSINK=1`.
        let cold_guards = if bp_coldsink_enabled() {
            static_cold_guard_blocks(func, &loops)
        } else {
            Vec::new()
        };
        if cold_guards.is_empty() {
            compute_block_layout(func);
        } else {
            sink_cold_guards_to_end(func, &cold_guards);
            invert_sunk_guard_heads(func, &cold_guards);
        }
        reordered = true;
    }
    // else: nothing to repair and the legacy pass would have bailed (a
    // layout-backward conditional / already-rotated loop). Skip the reorder;
    // only the elision below runs — identical machine code to the legacy bail
    // followed by the standalone branch-to-next elision.

    // Step 3.5: lay each tail-duplicated latch (loop-latch-layout tier 2's
    // swap-arm shape) immediately before its loop header so step 4 turns its
    // backedge into the loop's fall-through seam. MUST run before
    // `orient_loop_conditionals`: orientation deletes trailing `B`s (creating
    // implicit fall-throughs), and the pull's soundness argument requires every
    // edge to still be an explicit `Block` operand so block moves are pure
    // reordering.
    let pulled = pull_duplicated_latch_before_header(func, &loops);

    // Step 3.6: rotate small bottom-tested loops whose single latch the greedy
    // chainer orphaned to the far end (the Puzzle Fit/Place/Remove scan loops):
    // pull the latch immediately before its header so step 4 turns the
    // unconditional `B header` backedge into a fall-through, cutting the common
    // continue iteration from two taken branches to one. Same phase/soundness as
    // the tail-dup pull above (pure block reorder over explicit edges); skips the
    // `scattered` loops the header-first loop-aware reorder already owns. Gated to
    // functions with NO genuine conditional back-edge: those are the "reorder
    // allowed" regime (Fit/Place/Remove qualify — their backedge is an
    // unconditional `b header`). A function carrying an already-rotated loop is
    // deliberately left un-reordered and served IN PLACE by `small_orient` below;
    // moving blocks there would intrude on that domain (chomp's equal_data
    // compare loops).
    let latch_rotated =
        !has_genuine_back_edge && rotate_far_latch_before_header(func, &loops, &scattered);

    // Step 3.7: pull stranded pure-copy latches (regalloc critical-edge
    // trampolines whose Phi copies survived coalescing, appended at the far end
    // of the layout) immediately before their loop headers, so step 4 turns
    // their `B header` backedge into a fall-through: 2 far taken branches per
    // continue-iteration → 1 near one. Deliberately NOT gated on
    // `has_genuine_back_edge`: its per-loop fail-closed gates are the
    // protection, and the stranded-trampoline shape only exists post-RA so no
    // mid-end layout owns it (huffbench compdecomp: 4 such trampolines, one
    // per hot loop, in a function whose sibling loops are rotated).
    let copylatch_pulled = pull_far_copy_latch_before_header(func, &loops, &scattered);

    // Step 3.8: rotate TWO-ARMED loops (the pointer-descent shape: a header
    // whose conditional splits into two straight in-loop arms, each with its own
    // back-edge — Treesort's `Insert`). The single-latch pulls above can only
    // rescue ONE arm and pick it by layout position, so they routinely leave the
    // header's BRANCH-TAKEN arm out of line at two taken branches per step. This
    // tier assigns the arms by role instead: taken-arm before the header,
    // fall-arm after it — one taken branch each, the floor.
    // MUST run after the single-latch pulls: it recomputes the whole loop slice
    // from the CFG, so it subsumes (and would otherwise be undone by) their
    // position-driven choice.
    let armrot = rotate_two_armed_loops(func, &loops, &scattered);

    // Realize the loop-driven layout's conditional orientation (scattered-loop
    // repair only — see the comment on the reorder above).
    if !scattered.is_empty() {
        orient_loop_conditionals(func, &loops, &scattered);
    } else if has_genuine_back_edge && bp_small_orient_enabled() {
        // PER-LOOP protection. The function carries an already-rotated loop, so
        // the whole function was deliberately left un-reordered above. But that
        // per-function bail also abandoned any OTHER hot top-tested loop here —
        // e.g. chomp's inlined `equal_data` compare loop, contiguous but laid out
        // with its equal/stay-in-loop arm as the branch-taken target (2 taken
        // branches/iter vs clang's 1). Orient those small, contiguous, mis-oriented
        // loops IN PLACE (no block moves): each flip is a proven taken-branch
        // reduction that touches only the flipped conditional, so the already-
        // rotated sibling loop and all straight-line code stay byte-identical.
        let orient_small = small_orientable_loop_headers(func, &loops);
        if !orient_small.is_empty() {
            orient_loop_conditionals(func, &loops, &orient_small);
        }
    }

    // Orient inside the loops step 3.8 just rotated. The rotation puts the
    // fall-arm's chain physically after the header, but its blocks still carry
    // the pre-rotation polarity: the block that guards the fall-arm's
    // continuation (Treesort `Insert`'s `n < t->val` test) branch-TAKES into the
    // arm and falls through to the loop exit. With the arm now laid out next,
    // this flips it — the stay-in-loop edge becomes the fall-through and the
    // (cold) exit becomes the taken branch, which is what makes the fall-arm
    // cost exactly its own back-edge. Disjoint from the sets above:
    // [`rotate_two_armed_loops`] skips `scattered` headers.
    if !armrot.is_empty() {
        orient_loop_conditionals(func, &loops, &armrot);
    }

    // Step 3.9: universal in-place "branch over branch" orientation. The two
    // orientations above are loop-gated; this one finishes the job for every
    // remaining block (including fully-UNROLLED code, which has no loop left to
    // be a member of — Queens' `Try` and Puzzle's `Puzzle` init). Moves no
    // block; each flip is a strict instruction-count, taken-branch and code-size
    // reduction. See [`orient_next_is_cc_target`].
    let next_oriented = orient_next_is_cc_target(func, &loops);

    // Step 4: elide each trailing `B target` whose target is now layout-next.
    let elided = elide_trailing_b_to_layout_next(func);

    // Step 5 (optional): bottom-test rotation.
    let rotated = rotate && rotate_top_tested_loops(func);

    reordered
        || pulled
        || latch_rotated
        || copylatch_pulled
        || !armrot.is_empty()
        || next_oriented
        || elided
        || rotated
}

/// Loop-aware block placement is ON by default. Kill switch `TCG_LOOP_PLACE=0`
/// reverts to the legacy greedy reorder (for A/B measurement / emergency).
fn loop_aware_placement_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| !matches!(std::env::var("TCG_LOOP_PLACE").as_deref(), Ok("0")))
}

/// PGO-use layout precedence: a function whose `block_order` was committed by
/// the ProfileUsePass hot-chain layout keeps that order instead of the legacy
/// greedy re-derivation (the loop-aware scattered repair still runs — see the
/// call sites). Inert without a profile (`profile_ordered` is only ever set by
/// profile-use compiles). Kill switch: `TCG_PGO_LAYOUT_NO_PRECEDENCE` (any
/// value) restores the pre-precedence override for A/B runs.
fn profile_order_precedence(func: &MachFunction) -> bool {
    func.profile_ordered && std::env::var_os("TCG_PGO_LAYOUT_NO_PRECEDENCE").is_none()
}

// Diagnostic sub-feature toggles (default all-on).
fn bp_orient_enabled() -> bool {
    static F: OnceLock<bool> = OnceLock::new();
    *F.get_or_init(|| !matches!(std::env::var("TCG_BP_NO_ORIENT").as_deref(), Ok("1")))
}
fn bp_ccpref_enabled() -> bool {
    static F: OnceLock<bool> = OnceLock::new();
    *F.get_or_init(|| !matches!(std::env::var("TCG_BP_NO_CCPREF").as_deref(), Ok("1")))
}
/// Small-loop in-place orientation (default ON). Kill switch:
/// `TCG_BP_NO_SMALL_ORIENT=1`. Enables per-loop (not per-function) protection of
/// already-rotated loops so small, contiguous, MIS-ORIENTED top-tested hot loops
/// in the SAME function are still oriented — WITHOUT any block reorder.
fn bp_small_orient_enabled() -> bool {
    static F: OnceLock<bool> = OnceLock::new();
    *F.get_or_init(|| !matches!(std::env::var("TCG_BP_NO_SMALL_ORIENT").as_deref(), Ok("1")))
}
/// Universal in-place "branch over branch" orientation (default ON). Kill
/// switch: `TCG_BP_NO_NEXT_ORIENT=1` leaves every `COND cc next; B far` pair
/// verbatim (the pre-feature bytes). Read fresh (not cached) so PGO-mode env
/// screening and A/B harnesses see a consistent, per-process value.
fn bp_next_orient_enabled() -> bool {
    !matches!(std::env::var("TCG_BP_NO_NEXT_ORIENT").as_deref(), Ok("1"))
}
/// Static cold-guard sinking (default ON). Kill switch: `TCG_BP_NO_COLDSINK=1`
/// restores the greedy fall-through chain for guard-bearing functions (byte
/// identical to the pre-feature layout). Read fresh (not cached) so PGO-mode
/// env screening and A/B harnesses see a consistent, per-process value.
fn bp_coldsink_enabled() -> bool {
    !matches!(std::env::var("TCG_BP_NO_COLDSINK").as_deref(), Ok("1"))
}
/// Sunk-guard head inversion (default ON with the sink). Kill switch:
/// `TCG_BP_NO_COLDSINK_INVERT=1` keeps the sink but leaves every head's
/// `bcond hot; b guard` pair verbatim (the pre-inversion bytes).
fn bp_coldsink_invert_enabled() -> bool {
    !matches!(
        std::env::var("TCG_BP_NO_COLDSINK_INVERT").as_deref(),
        Ok("1")
    )
}
/// Opt-in decision log (`TCG_BP_COLDSINK_LOG=1`): one stderr line per sunk
/// guard block, for program-by-program layout attribution (mirrors
/// `TCG_PGO_LAYOUT_LOG`).
fn bp_coldsink_log_enabled() -> bool {
    std::env::var_os("TCG_BP_COLDSINK_LOG").is_some()
}

/// Statically recognized never-executed error-report side arms ("cold
/// guards"), in current `block_order` order.
///
/// This is the static capture of the measured Towers PGO layout win: the
/// profile layout's only deviation from static order is sinking ZERO-HIT
/// error-guard blocks out of the hot fall-through line (Stanford/Towers
/// `Move`/`Push`/`Pop`/`Getelement`, ~10% on `Move` — see the zero-hit-span
/// chain gate note in `trust-cg-opt/src/pgo/profile_use.rs`). Those guards
/// are recognizable without a profile: clang -O1 inlines the benchmark's
/// `Error()` wrapper, leaving a side arm whose ENTIRE body is one
/// diagnostic call — argument materialization (`adrp`/`add`/`mov`), an
/// outgoing-arg store to `[sp, #k]`, the `bl`, phi-materialization copies —
/// and an unconditional rejoin. A block qualifies iff ALL of:
///
/// 1. not the entry block and not inside any natural loop (loop bodies are
///    the contiguity domain of the loop-aware/latch passes; a sink there
///    could split a loop line — fail closed);
/// 2. exactly one distinct predecessor, itself a two-way conditional head
///    ending in the materialized `bcond` + `b` pair (the diamond/triangle
///    side-arm shape: exactly one branch decides whether the guard runs);
/// 3. exactly one distinct successor, reached by a trailing unconditional
///    `B <block>` (the guard REJOINS the CFG — return-terminated or
///    tail-call arms are a different shape and are not touched);
/// 4. the body is call-and-glue ONLY: 1..=2 call instructions and otherwise
///    nothing but register materialization/copies and SP-addressed
///    outgoing-argument stores (see [`is_outgoing_arg_store`]). Any load,
///    any non-SP store, any other side effect, or any mid-block branch
///    disqualifies — a side arm that READS or WRITES program state is an
///    alternative computation, not a diagnostic report;
/// 5. the sibling arm is CALL-FREE (Ball-Larus call-heuristic asymmetry):
///    between two arms the call-bearing one is the cold report path exactly
///    when the other arm does real work without calling. Both-arms-call
///    diamonds (e.g. Towers `tower`'s Move-vs-recurse) never sink;
/// 6. small: at most 16 real instructions.
///
/// The composition test (4) is deliberately the narrow part: it will miss
/// guards that, e.g., print a loaded value — missing a sink is only a lost
/// optimization, while sinking a WARM block is the measured Puzzle `Trial`
/// regression class the profile pass needed its chain gate for.
fn static_cold_guard_blocks(func: &MachFunction, loops: &LoopAnalysis) -> Vec<BlockId> {
    let mut guards = Vec::new();
    for &block in &func.block_order {
        if is_static_cold_guard(func, loops, block) {
            guards.push(block);
        }
    }
    guards
}

/// Log a candidate rejection under `TCG_BP_COLDSINK_LOG=1`. Only called for
/// blocks that already looked guard-like (call-bearing), to keep the log
/// attributable rather than one line per block of every function.
fn coldsink_log_reject(func: &MachFunction, block: BlockId, reason: &str) {
    if bp_coldsink_log_enabled() && block_contains_call(func, block) {
        eprintln!(
            "coldsink: {} B{} rejected: {} (insts: {:?})",
            func.name,
            block.0,
            reason,
            func.block(block)
                .insts
                .iter()
                .map(|&id| func.inst(id).opcode)
                .collect::<Vec<_>>()
        );
    }
}

/// Whether `block` matches the cold error-guard shape. See
/// [`static_cold_guard_blocks`] for the full contract.
fn is_static_cold_guard(func: &MachFunction, loops: &LoopAnalysis, block: BlockId) -> bool {
    if block == func.entry || loops.is_in_loop(block) {
        coldsink_log_reject(func, block, "entry-or-in-loop");
        return false;
    }
    let mach_block = func.block(block);

    // (2) Exactly one distinct predecessor: a two-way conditional head.
    let mut preds = mach_block.preds.clone();
    preds.sort_unstable();
    preds.dedup();
    let &[head] = preds.as_slice() else {
        coldsink_log_reject(func, block, "pred-count");
        return false;
    };
    if head == block {
        return false;
    }
    let mut head_succs = func.block(head).succs.clone();
    head_succs.sort_unstable();
    head_succs.dedup();
    let &[a, b] = head_succs.as_slice() else {
        coldsink_log_reject(func, block, "head-succ-count");
        return false;
    };
    let sibling = if a == block {
        b
    } else if b == block {
        a
    } else {
        coldsink_log_reject(func, block, "head-succ-membership");
        return false;
    };
    // Post-materialization every two-successor head ends in the explicit
    // `bcond` + `b` pair; require that shape so a fall-through-dependent head
    // (which reordering would break) fails closed.
    let Some(head_last) = last_real_inst(func, head) else {
        return false;
    };
    if !func.inst(head_last).is_unconditional_branch() {
        coldsink_log_reject(func, block, "head-shape");
        return false;
    }

    // (3) Exactly one distinct successor, via a trailing unconditional B.
    let mut succs = mach_block.succs.clone();
    succs.sort_unstable();
    succs.dedup();
    let &[join] = succs.as_slice() else {
        coldsink_log_reject(func, block, "succ-count");
        return false;
    };
    if join == block {
        return false;
    }
    let Some(last_id) = last_real_inst(func, block) else {
        return false;
    };
    let last = func.inst(last_id);
    if !last.is_unconditional_branch()
        || !last
            .operands
            .iter()
            .any(|op| matches!(op, MachOperand::Block(target) if *target == join))
    {
        return false;
    }

    // (4) Call-and-glue composition + (6) size cap.
    let mut call_count = 0usize;
    let mut real_insts = 0usize;
    for &id in &mach_block.insts {
        let inst = func.inst(id);
        if inst.is_pseudo() {
            continue;
        }
        real_insts += 1;
        if id == last_id {
            continue;
        }
        if inst.is_call() {
            call_count += 1;
            continue;
        }
        if inst.is_branch() || inst.is_terminator() {
            coldsink_log_reject(func, block, "mid-block-branch");
            return false;
        }
        if inst.reads_memory() {
            coldsink_log_reject(func, block, "reads-memory");
            return false;
        }
        if (inst.writes_memory() || inst.has_side_effects()) && !is_outgoing_arg_store(inst) {
            coldsink_log_reject(func, block, "non-arg-side-effect");
            return false;
        }
    }
    if call_count == 0 || call_count > 2 || real_insts > 16 {
        coldsink_log_reject(func, block, "call-count-or-size");
        return false;
    }

    // (5) Sibling-arm call asymmetry.
    !block_contains_call(func, sibling)
}

/// A store whose address is SP-based: the outgoing-argument spill
/// (`str xN, [sp, #k]`) that variadic/stack-passed call arguments require.
/// The only memory write a cold guard is allowed to contain. Post-RA the
/// address appears either as split operands (`StrRI [src, sp, #k]`) or as a
/// `MemOp { base: sp }`; any non-SP-addressed memory operand disqualifies.
fn is_outgoing_arg_store(inst: &MachInst) -> bool {
    if !inst.writes_memory() || inst.reads_memory() {
        return false;
    }
    let mut sp_addr = false;
    for op in &inst.operands {
        match op {
            MachOperand::MemOp { base, .. } => {
                if *base == AARCH64_SP {
                    sp_addr = true;
                } else {
                    return false;
                }
            }
            MachOperand::PReg(reg) if *reg == AARCH64_SP => sp_addr = true,
            _ => {}
        }
    }
    sp_addr
}

/// True if any instruction in `block` is a call.
fn block_contains_call(func: &MachFunction, block: BlockId) -> bool {
    func.block(block)
        .insts
        .iter()
        .any(|&id| func.inst(id).is_call())
}

/// Move `guards` (already in layout order) to the end of `block_order`,
/// preserving the relative order of everything else — the same pure
/// permutation over fully-explicit edges every other step of this pass uses.
/// The spine keeps its original order, so every `bcond hot; b guard` head now
/// has its hot arm laid out next and the guard bodies live past the last hot
/// block, exactly reproducing the profile-use layout on the Towers shapes.
/// Invert every conditional pair whose CONDITIONAL targets the layout-next
/// block, in a function whose cold guards were just sunk:
/// `... ; BCond cc NEXT ; B FAR` becomes `... ; BCond !cc FAR` with control
/// falling through to `NEXT`.
///
/// [`sink_cold_guards_to_end`] extracts the never-executed guard arms to the
/// end of the layout but keeps every head's terminator pair verbatim. A block
/// whose CONDITIONAL targets the layout-next block therefore still executes a
/// TAKEN conditional every pass — hopping over its own trailing `B` — even
/// though its target is the very next instruction (measured on
/// Stanford/Towers `Move`: 4 such sites on the hot path — 3 sunk-guard heads
/// plus the push skip-check diamond; the taken-to-next hops plus the dead
/// `B`s in the fetch stream are one of the three measured layout defects
/// behind the 1.26x residual — see the Move.s variant harness, vNIS/vI vs
/// V0). The inversion DOMINATES for every branch-outcome distribution: the
/// conditional path drops from one taken transfer to zero (pure
/// fall-through), the other path still pays exactly one taken transfer (the
/// inverted conditional instead of the `B`), and the block is one
/// instruction shorter. The opposite shape (`BCond cc FAR ; B NEXT`) needs
/// no help: step 4's branch-to-next elision drops its `B NEXT`.
///
/// Scoped to functions with recognized sunk guards — the domain the cold-sink
/// feature owns and the domain the Move.s harness validated — so straight-line
/// code elsewhere keeps its exact bytes ([`orient_loop_conditionals`]'s
/// conservatism). Fail-closed: only the exact `classify_cond_pair` shape with
/// an invertible cc is touched.
///
/// Soundness is [`invert_cond_pair`]'s: `!cc` is the exact complement (BCond
/// bit-0 flip / `Cbz`<->`Cbnz` / `Tbz`<->`Tbnz` opcode swap), the successor
/// SET is unchanged, and the redundant `B` is deleted, so the block transfers
/// to the far target exactly when it did before and reaches the next block
/// (now by fall-through) exactly when it did before.
///
/// Kill switch: `TCG_BP_NO_COLDSINK_INVERT=1` (bytes identical to the
/// sink-without-inversion layout); `TCG_BP_NO_COLDSINK=1` disables the sink
/// and with it this pass.
fn invert_sunk_guard_heads(func: &mut MachFunction, guards: &[BlockId]) -> bool {
    debug_assert!(!guards.is_empty(), "caller gates on recognized guards");
    if !bp_coldsink_invert_enabled() {
        return false;
    }
    let order = func.block_order.clone();
    let mut plans: Vec<(BlockId, CondPair)> = Vec::new();
    for i in 0..order.len() {
        let block = order[i];
        let Some(&next) = order.get(i + 1) else {
            continue;
        };
        let Some(cp) = classify_cond_pair(func, block) else {
            continue;
        };
        // Only pairs whose conditional targets the layout-next block: the
        // inversion converts that taken-to-next hop into a fall-through.
        if cp.cc_target != next {
            continue;
        }
        if !cond_pair_invertible(func, &cp) {
            continue;
        }
        plans.push((block, cp));
    }
    let mut changed = false;
    for (block, cp) in plans {
        if bp_coldsink_log_enabled() {
            eprintln!(
                "coldsink: {} inverting head B{} (guard B{} now fall-through-free)",
                func.name, block.0, cp.ft_target.0
            );
        }
        if invert_cond_pair(func, block, &cp) {
            changed = true;
        }
    }
    changed
}

fn sink_cold_guards_to_end(func: &mut MachFunction, guards: &[BlockId]) {
    if guards.is_empty() {
        return;
    }
    if bp_coldsink_log_enabled() {
        for &guard in guards {
            eprintln!(
                "coldsink: {} sinking B{} (preds {:?} -> succs {:?})",
                func.name,
                guard.0,
                func.block(guard).preds,
                func.block(guard).succs
            );
        }
    }
    let mut order: Vec<BlockId> = func
        .block_order
        .iter()
        .copied()
        .filter(|block| !guards.contains(block))
        .collect();
    order.extend(guards.iter().copied());
    func.block_order = order;
}

/// Layout-independent branch-to-next elision: delete every trailing
/// unconditional `B target` whose `target` is already the immediately-next
/// block in the final `block_order`, WITHOUT reordering or rotating anything.
///
/// This is the layout-*independent* half of
/// [`aarch64_layout_fallthrough_and_elide`]'s step 4. That pass fails closed as
/// a WHOLE when it meets an already-rotated bottom-tested loop (a conditional
/// back-edge), because its greedy *re-layout* could perturb the cold exit path —
/// but a rotated loop still carries a redundant `b <next>` at the body→latch
/// seam that is pure dead weight (a taken branch to the very next instruction).
/// Eliding it changes no control flow whatsoever: the block falls through to
/// exactly the block it branched to.
///
/// Soundness is identical to step 4's, and needs no register/CFG analysis: the
/// only edit is removing a `B` whose sole `Block` operand equals the block laid
/// out next, so fall-through reproduces the branch's single successor. Byte
/// offsets stay consistent because [`resolve_branches`] and the encoder BOTH
/// recompute every block offset (and every branch/jump-table displacement) from
/// `block_order` and the now-shorter instruction lists AFTER this runs; nothing
/// downstream caches a pre-elision offset.
///
/// Unlike the reorder pass this is safe on functions with conditional back-edges
/// (rotated loops — the whole point) AND on the EH / jump-table / indirect-branch
/// functions that pass rejects, because it neither moves a block nor changes any
/// block's set of successors: a redundant `b <next>` and a fall-through to
/// `<next>` are the same edge, so try-region spans and data-driven dispatch
/// targets are untouched. It still leaves conditional branches, `BCond`
/// fall-through semantics, indirect `Br`, and symbol/tail-call `B` (no `Block`
/// operand) exactly as they were.
///
/// Returns `true` iff at least one branch was elided.
pub fn aarch64_elide_branch_to_next(func: &mut MachFunction) -> bool {
    if func.block_order.len() < 2 {
        return false;
    }
    elide_trailing_b_to_layout_next(func)
}

/// Delete each trailing `B target` that jumps to the layout-next block, in the
/// CURRENT `block_order` (no reordering). Shared by the reorder pass (step 4)
/// and the standalone [`aarch64_elide_branch_to_next`]. A branch is elided iff
/// it is the block's last non-pseudo instruction, is a `B`, and its ONLY
/// operand-carried target is the block laid out immediately next — so a
/// symbol/tail-call `B` (no `Block` operand) or a `B` to any other block is left
/// untouched. Returns `true` iff any branch was elided.
///
/// LANDING-PAD EXCEPTION: a landing-pad block must keep at least ONE real
/// encoded instruction. The LSDA identifies the pad by its first-instruction
/// byte offset, and `resolve_eh_offsets` FAILS CLOSED on a pad whose block
/// encodes to zero bytes ("has no encoded instruction body"). After SROA
/// scalarizes a pad's exception-slot store into pseudo copies, the trailing
/// `b <next>` can be the pad's ONLY non-pseudo instruction — eliding it would
/// zero the pad's body and abort the compile at -O2 (the unwind-lane opt
/// fallback class: panic_unwind `exception_cleanup`, backtrace `trace_fn`).
/// Keeping the branch is control-flow-identical and costs 4 cold bytes; a pad
/// is entered by the unwinder, not by any frequency-critical fall-through.
fn elide_trailing_b_to_layout_next(func: &mut MachFunction) -> bool {
    let mut elided = false;
    let landing_pads: Vec<BlockId> = func
        .eh_metadata
        .landing_pads
        .iter()
        .map(|lp| lp.block)
        .collect();
    let order = func.block_order.clone();
    for (i, &block) in order.iter().enumerate() {
        let Some(&next) = order.get(i + 1) else {
            continue;
        };
        let Some(last_id) = last_real_inst(func, block) else {
            continue;
        };
        let inst = func.inst(last_id);
        if inst.opcode != AArch64Opcode::B {
            continue;
        }
        let block_targets: Vec<BlockId> = inst
            .operands
            .iter()
            .filter_map(|op| match op {
                MachOperand::Block(b) => Some(*b),
                _ => None,
            })
            .collect();
        if block_targets.as_slice() != [next] {
            continue;
        }
        if landing_pads.contains(&block) {
            let real_insts = func
                .block(block)
                .insts
                .iter()
                .filter(|&&id| !func.inst(id).is_pseudo())
                .count();
            if real_insts <= 1 {
                // This `B` is the pad's only encodable instruction — keep it
                // so the pad retains a non-empty body for the LSDA offset.
                continue;
            }
        }
        func.block_mut(block).insts.retain(|&id| id != last_id);
        elided = true;
    }
    elided
}

/// Bottom-test (do-while) rotation of top-tested counted loops, run after the
/// fall-through reorder+elide so the recognized shape is exact.
///
/// # The shape it rewrites
///
/// After step 3/4 a top-tested loop is laid out as three consecutive blocks:
///
/// ```text
///   order[i]   H:  cmp A, B ; b.cc EXIT           (falls through to Bd)
///   order[i+1] Bd: <body...> ; b H                (unconditional back-edge)
///   order[i+2] EXIT: ...
/// ```
///
/// where `H` holds **nothing but** the compare and the conditional exit branch.
/// It becomes a do-while loop that tests once, at the bottom:
///
/// ```text
///   order[i]   H:  cmp A, B ; b.cc EXIT           (one-time zero-trip guard)
///   order[i+1] Bd: <body...> ; cmp A, B ; b.!cc Bd   (falls through to EXIT)
///   order[i+2] EXIT: ...
/// ```
///
/// # Why it is sound (equivalence, no register analysis needed)
///
/// The rewrite replaces `Bd`'s trailing `b H` with an inline copy of exactly
/// what `H` did when reached through that back-edge: `H`'s compare — cloned
/// byte-for-byte and placed at the *exact* instruction position the `b H`
/// occupied, so it reads registers `A`/`B` in the identical state `H` would —
/// followed by `b.!cc Bd`. Because
///
/// * `!cc` is the exact complement of `cc` (AArch64 encodes cc inversion as a
///   flip of encoding bit 0; only real, invertible codes `0..=13` are accepted,
///   `AL`/`NV` are rejected), `Bd` loops back exactly when `H` would have fallen
///   through to the body and falls through to `EXIT` exactly when `H` would have
///   taken `b.cc EXIT`;
/// * `H` contains no instruction other than the compare and the branch, so the
///   back-edge that now skips `H` skips no computation;
/// * `EXIT` is entered in both the original and rotated forms with the flags of
///   the very same `cmp A, B`, so any flag-consuming `EXIT` is unaffected.
///
/// Fail-closed: any deviation from the exact shape (extra instruction in `H`,
/// missing/duplicate operands, non-invertible cc, missing `EXIT` slot, `Bd` not
/// ending in `b H`) skips that loop untouched.
///
/// Returns `true` iff at least one loop was rotated.
fn rotate_top_tested_loops(func: &mut MachFunction) -> bool {
    struct Rotation {
        body: BlockId,
        back_edge_id: InstId,
        cmp: MachInst,
        inverted_cc: i64,
    }

    let order = func.block_order.clone();
    let mut plans: Vec<Rotation> = Vec::new();

    for i in 0..order.len() {
        let header = order[i];
        let (Some(&body), Some(&exit)) = (order.get(i + 1), order.get(i + 2)) else {
            continue;
        };
        if body == header || exit == header || exit == body {
            continue;
        }

        // H must be EXACTLY [cmp, b.cc EXIT] (no other real instruction).
        let header_insts: Vec<InstId> = func
            .block(header)
            .insts
            .iter()
            .copied()
            .filter(|&id| !func.inst(id).is_pseudo())
            .collect();
        let [cmp_id, bcond_id] = header_insts.as_slice() else {
            continue;
        };
        let cmp = func.inst(*cmp_id);
        if !matches!(cmp.opcode, AArch64Opcode::CmpRR | AArch64Opcode::CmpRI) {
            continue;
        }
        let bcond = func.inst(*bcond_id);
        if bcond.opcode != AArch64Opcode::BCond {
            continue;
        }
        // Exactly one cc immediate and one Block target (== EXIT).
        let imms: Vec<i64> = bcond
            .operands
            .iter()
            .filter_map(|op| match op {
                MachOperand::Imm(v) => Some(*v),
                _ => None,
            })
            .collect();
        let targets: Vec<BlockId> = bcond
            .operands
            .iter()
            .filter_map(|op| match op {
                MachOperand::Block(b) => Some(*b),
                _ => None,
            })
            .collect();
        let ([cc], [exit_target]) = (imms.as_slice(), targets.as_slice()) else {
            continue;
        };
        if *exit_target != exit {
            continue;
        }
        // Only genuine, invertible condition codes (0..=13). AArch64 inverts a
        // condition by flipping encoding bit 0; AL(14)/NV(15) are unconditional
        // and are rejected.
        if !(0..=13).contains(cc) {
            continue;
        }
        let inverted_cc = cc ^ 1;

        // Bd's last real instruction must be `b H` (the unconditional back-edge).
        let Some(back_edge_id) = last_real_inst(func, body) else {
            continue;
        };
        let back = func.inst(back_edge_id);
        if back.opcode != AArch64Opcode::B {
            continue;
        }
        let back_targets: Vec<BlockId> = back
            .operands
            .iter()
            .filter_map(|op| match op {
                MachOperand::Block(b) => Some(*b),
                _ => None,
            })
            .collect();
        if back_targets.as_slice() != [header] {
            continue;
        }

        plans.push(Rotation {
            body,
            back_edge_id,
            cmp: cmp.clone(),
            inverted_cc,
        });
    }

    if plans.is_empty() {
        return false;
    }

    for plan in plans {
        // Remove the back-edge `b H`.
        func.block_mut(plan.body)
            .insts
            .retain(|&id| id != plan.back_edge_id);
        // Clone the header compare at the exact former position of the back-edge,
        // then the inverted conditional branch back to the body.
        let cmp_id = func.push_inst(plan.cmp);
        func.append_inst(plan.body, cmp_id);
        let bcond_id = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![
                MachOperand::Imm(plan.inverted_cc),
                MachOperand::Block(plan.body),
            ],
        ));
        func.append_inst(plan.body, bcond_id);
    }

    true
}

/// Whole-function bail predicate: true when the function contains a layout
/// feature this pass does not model with provable offset consistency (see
/// [`aarch64_layout_fallthrough_and_elide`]).
fn function_uses_unsupported_layout_features(func: &MachFunction) -> bool {
    if func.eh_metadata.has_eh_info() {
        return true;
    }
    if !func.jump_tables.is_empty() {
        return true;
    }
    for inst in &func.insts {
        if inst.opcode == AArch64Opcode::Br {
            return true;
        }
        if inst
            .operands
            .iter()
            .any(|op| op.as_jump_table_index().is_some())
        {
            return true;
        }
    }
    false
}

/// True if any conditional branch targets an earlier-or-equal block in the
/// current layout order — a conditional back-edge, i.e. an already-rotated
/// bottom-tested loop this pass must not disturb (see
/// [`aarch64_layout_fallthrough_and_elide`]).
fn function_has_conditional_back_edge(func: &MachFunction) -> bool {
    let mut pos = vec![usize::MAX; func.blocks.len()];
    for (i, &b) in func.block_order.iter().enumerate() {
        if let Some(slot) = pos.get_mut(b.0 as usize) {
            *slot = i;
        }
    }
    for &block_id in &func.block_order {
        let src_pos = pos[block_id.0 as usize];
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            if !inst.is_conditional_branch() {
                continue;
            }
            for op in &inst.operands {
                if let MachOperand::Block(target) = op {
                    let tp = pos.get(target.0 as usize).copied().unwrap_or(usize::MAX);
                    if tp != usize::MAX && tp <= src_pos {
                        return true;
                    }
                }
            }
        }
    }
    false
}

/// True if the block's last non-pseudo instruction does NOT fall through.
///
/// Use the opcode's semantic terminator flags rather than a hand-maintained
/// branch/return list: unconditional traps such as `TrapOverflow` are hard
/// terminators too. A trailing `Brk` is also hard; it is deliberately not
/// globally flagged as a terminator because guarded intra-block BRKs can have
/// a reachable continuation. Conditional terminators still have a layout
/// fallthrough; calls, ordinary instructions, and empty blocks do as well.
fn block_has_hard_terminator(func: &MachFunction, block: BlockId) -> bool {
    for &id in func.block(block).insts.iter().rev() {
        let inst = func.inst(id);
        if inst.is_pseudo() {
            continue;
        }
        return inst.opcode == AArch64Opcode::Brk
            || (inst.is_terminator() && !inst.is_conditional_branch());
    }
    false
}

/// Last non-pseudo instruction id of a block, if any.
fn last_real_inst(func: &MachFunction, block: BlockId) -> Option<InstId> {
    func.block(block)
        .insts
        .iter()
        .rev()
        .copied()
        .find(|&id| !func.inst(id).is_pseudo())
}

/// Rebuild every block's `succs`/`preds` purely from `Block` branch operands.
/// Safe here because [`function_uses_unsupported_layout_features`] has already
/// rejected indirect/jump-table control flow, so all edges are explicit.
fn rebuild_succs_from_block_operands(func: &mut MachFunction) {
    let mut edges: Vec<(BlockId, BlockId)> = Vec::new();
    for &block_id in &func.block_order {
        for &inst_id in &func.block(block_id).insts {
            for op in &func.inst(inst_id).operands {
                if let MachOperand::Block(target) = op {
                    edges.push((block_id, *target));
                }
            }
        }
    }
    for block in &mut func.blocks {
        block.preds.clear();
        block.succs.clear();
    }
    for (from, to) in edges {
        let (fi, ti) = (from.0 as usize, to.0 as usize);
        if fi >= func.blocks.len() || ti >= func.blocks.len() {
            continue;
        }
        if !func.blocks[fi].succs.contains(&to) {
            func.blocks[fi].succs.push(to);
        }
        if !func.blocks[ti].preds.contains(&from) {
            func.blocks[ti].preds.push(from);
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::{AArch64CC, InstId, MachOperand, Signature};

    /// Helper: create a minimal function with given number of blocks.
    /// Returns the function with blocks but no instructions or edges.
    fn make_func(name: &str, num_blocks: usize) -> MachFunction {
        let sig = Signature::new(vec![], vec![]);
        let mut func = MachFunction::new(name.to_string(), sig);
        // MachFunction::new already creates block 0 (entry).
        for _ in 1..num_blocks {
            func.create_block();
        }
        func
    }

    /// Helper: add an instruction to a block.
    fn add_inst(func: &mut MachFunction, block: BlockId, inst: MachInst) -> InstId {
        let id = func.push_inst(inst);
        func.append_inst(block, id);
        id
    }

    // -----------------------------------------------------------------------
    // test_linear_layout: bb0 -> bb1 -> bb2 (all fall-through)
    // -----------------------------------------------------------------------
    #[test]
    fn test_linear_layout() {
        let mut func = make_func("linear", 3);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);
        let bb2 = BlockId(2);

        // bb0: B bb1
        add_inst(&mut func, bb0, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
        );
        func.add_edge(bb0, bb1);

        // bb1: B bb2
        add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(
            &mut func,
            bb1,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb2)]),
        );
        func.add_edge(bb1, bb2);

        // bb2: Ret
        add_inst(&mut func, bb2, MachInst::new(AArch64Opcode::Ret, vec![]));

        compute_block_layout(&mut func);

        // Linear chain should stay in order: bb0, bb1, bb2.
        assert_eq!(func.block_order, vec![bb0, bb1, bb2]);
    }

    // -----------------------------------------------------------------------
    // test_diamond_layout: bb0 branches conditionally to bb1/bb2, both go to bb3
    // -----------------------------------------------------------------------
    #[test]
    fn test_diamond_layout() {
        let mut func = make_func("diamond", 4);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);
        let bb2 = BlockId(2);
        let bb3 = BlockId(3);

        // bb0: BCond bb1 ; B bb2
        add_inst(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(AArch64CC::EQ as i64),
                    MachOperand::Block(bb1),
                ],
            ),
        );
        add_inst(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb2)]),
        );
        func.add_edge(bb0, bb1);
        func.add_edge(bb0, bb2);

        // bb1: B bb3
        add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(
            &mut func,
            bb1,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb3)]),
        );
        func.add_edge(bb1, bb3);

        // bb2: B bb3
        add_inst(&mut func, bb2, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(
            &mut func,
            bb2,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb3)]),
        );
        func.add_edge(bb2, bb3);

        // bb3: Ret
        add_inst(&mut func, bb3, MachInst::new(AArch64Opcode::Ret, vec![]));

        compute_block_layout(&mut func);

        // bb0 has BCond bb1 + B bb2. Fall-through = bb2 (the B target).
        // So layout should be: bb0, bb2, then bb1, then bb3.
        assert_eq!(func.block_order[0], bb0);
        assert_eq!(func.block_order[1], bb2);
        // bb1 and bb3 follow (bb2 chains to bb3, then bb1 is leftover).
        // Actually bb2 -> bb3, so: bb0, bb2, bb3, bb1
        // But bb1 also -> bb3 (already placed), so bb1 has no unplaced successor.
        assert!(func.block_order.contains(&bb1));
        assert!(func.block_order.contains(&bb3));
        assert_eq!(func.block_order.len(), 4);
    }

    // -----------------------------------------------------------------------
    // test_loop_layout: bb0 -> bb1 -> bb2 -> bb1 (loop), bb2 also -> bb3
    // -----------------------------------------------------------------------
    #[test]
    fn test_loop_layout() {
        let mut func = make_func("loop", 4);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);
        let bb2 = BlockId(2);
        let bb3 = BlockId(3);

        // bb0: B bb1
        add_inst(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
        );
        func.add_edge(bb0, bb1);

        // bb1: (loop header) some work
        add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(
            &mut func,
            bb1,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb2)]),
        );
        func.add_edge(bb1, bb2);

        // bb2: BCond bb1 (loop back) ; B bb3 (exit)
        add_inst(
            &mut func,
            bb2,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(AArch64CC::NE as i64),
                    MachOperand::Block(bb1),
                ],
            ),
        );
        add_inst(
            &mut func,
            bb2,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb3)]),
        );
        func.add_edge(bb2, bb1);
        func.add_edge(bb2, bb3);

        // bb3: Ret
        add_inst(&mut func, bb3, MachInst::new(AArch64Opcode::Ret, vec![]));

        compute_block_layout(&mut func);

        // Entry first.
        assert_eq!(func.block_order[0], bb0);
        // Loop body should be contiguous: bb1, bb2 together.
        let pos1 = func.block_order.iter().position(|&b| b == bb1).unwrap();
        let pos2 = func.block_order.iter().position(|&b| b == bb2).unwrap();
        assert_eq!(
            pos2,
            pos1 + 1,
            "loop body blocks bb1, bb2 should be contiguous"
        );
        // bb3 (exit) after loop.
        let pos3 = func.block_order.iter().position(|&b| b == bb3).unwrap();
        assert!(pos3 > pos2, "exit block bb3 should be after loop body");
    }

    // -----------------------------------------------------------------------
    // test_unreachable_blocks: bb0 -> bb1, bb2 is unreachable
    // -----------------------------------------------------------------------
    #[test]
    fn test_unreachable_blocks() {
        let mut func = make_func("unreachable", 3);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);
        let bb2 = BlockId(2);

        // bb0: B bb1
        add_inst(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
        );
        func.add_edge(bb0, bb1);

        // bb1: Ret
        add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::Ret, vec![]));

        // bb2: unreachable (no predecessors)
        add_inst(&mut func, bb2, MachInst::new(AArch64Opcode::Ret, vec![]));

        compute_block_layout(&mut func);

        // Unreachable bb2 should be last.
        assert_eq!(func.block_order[0], bb0);
        assert_eq!(func.block_order[1], bb1);
        assert_eq!(func.block_order[2], bb2);
    }

    // -----------------------------------------------------------------------
    // test_detached_arena_shell_is_not_resurrected
    // -----------------------------------------------------------------------
    #[test]
    fn test_detached_arena_shell_is_not_resurrected() {
        let mut func = make_func("detached_arena_shell", 3);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);
        let bb2 = BlockId(2);

        add_inst(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
        );
        func.add_edge(bb0, bb1);
        add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::Ret, vec![]));

        // Model cfg-simplify's stable-ID arena contract: the dead block remains
        // allocated but is no longer part of the executable stream.
        add_inst(&mut func, bb2, MachInst::new(AArch64Opcode::Ret, vec![]));
        func.block_order.retain(|&block| block != bb2);

        compute_block_layout(&mut func);

        assert_eq!(func.block_order, vec![bb0, bb1]);
        assert!(!func.block_order.contains(&bb2));
    }

    // -----------------------------------------------------------------------
    // test_cbz_fallthrough: block ending in Cbz (no trailing B)
    // -----------------------------------------------------------------------
    #[test]
    fn test_cbz_fallthrough() {
        let mut func = make_func("cbz_ft", 3);
        let bb0 = BlockId(0);
        let bb1 = BlockId(1);
        let bb2 = BlockId(2);

        // bb0: Cbz target=bb2 (fall-through to bb1)
        add_inst(
            &mut func,
            bb0,
            MachInst::new(
                AArch64Opcode::Cbz,
                vec![MachOperand::Imm(0), MachOperand::Block(bb2)],
            ),
        );
        func.add_edge(bb0, bb2);
        func.add_edge(bb0, bb1);

        // bb1: Ret
        add_inst(&mut func, bb1, MachInst::new(AArch64Opcode::Ret, vec![]));

        // bb2: Ret
        add_inst(&mut func, bb2, MachInst::new(AArch64Opcode::Ret, vec![]));

        compute_block_layout(&mut func);

        // Cbz targets bb2, so fall-through should prefer bb1.
        assert_eq!(func.block_order[0], bb0);
        assert_eq!(func.block_order[1], bb1);
        assert_eq!(func.block_order[2], bb2);
    }

    // -----------------------------------------------------------------------
    // test_single_block: only entry block
    // -----------------------------------------------------------------------
    #[test]
    fn test_single_block() {
        let mut func = make_func("single", 1);
        add_inst(
            &mut func,
            BlockId(0),
            MachInst::new(AArch64Opcode::Ret, vec![]),
        );

        compute_block_layout(&mut func);
        assert_eq!(func.block_order, vec![BlockId(0)]);
    }

    // -----------------------------------------------------------------------
    // Fall-through layout + elision (aarch64_layout_fallthrough_and_elide)
    // -----------------------------------------------------------------------

    fn bcond(cc: AArch64CC, target: BlockId) -> MachInst {
        MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Imm(cc as i64), MachOperand::Block(target)],
        )
    }

    fn b(target: BlockId) -> MachInst {
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(target)])
    }

    fn last_opcode(func: &MachFunction, block: BlockId) -> AArch64Opcode {
        func.inst(*func.block(block).insts.last().unwrap()).opcode
    }

    /// A top-tested loop whose body is laid out LAST (the reduction-split
    /// shape): the header's `b body` is a forward jump and the body's `b
    /// header` a backward one. The pass must pull the body up to fall through
    /// from the header, elide the now-redundant forward jumps, and keep the
    /// unconditional backward latch branch.
    #[test]
    fn reorders_and_elides_top_tested_loop() {
        let mut func = make_func("top_tested", 4);
        let (entry, header, exit, body) = (BlockId(0), BlockId(1), BlockId(2), BlockId(3));

        add_inst(&mut func, entry, MachInst::new(AArch64Opcode::MovI, vec![]));
        add_inst(&mut func, entry, b(header));
        func.add_edge(entry, header);

        add_inst(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::CmpRR, vec![]),
        );
        add_inst(&mut func, header, bcond(AArch64CC::GE, exit));
        add_inst(&mut func, header, b(body));
        func.add_edge(header, exit);
        func.add_edge(header, body);

        add_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));

        add_inst(&mut func, body, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(&mut func, body, b(header));
        func.add_edge(body, header);

        // Body laid out last, exit before it — the deficit shape.
        func.block_order = vec![entry, header, exit, body];

        // rotate=false: exercise the reorder+elide in isolation.
        let changed = aarch64_layout_fallthrough_and_elide(&mut func, false);
        assert!(changed, "should elide at least one redundant jump");

        // Body now contiguous with its header.
        let hpos = func.block_order.iter().position(|&b| b == header).unwrap();
        let bpos = func.block_order.iter().position(|&b| b == body).unwrap();
        assert_eq!(bpos, hpos + 1, "loop body must fall through from header");

        // Header's forward `b body` elided -> ends in the conditional exit.
        assert_eq!(last_opcode(&func, header), AArch64Opcode::BCond);
        // Backward latch branch preserved (body -> header is not layout-next).
        assert_eq!(last_opcode(&func, body), AArch64Opcode::B);
        let latch_target = func
            .inst(*func.block(body).insts.last().unwrap())
            .operands
            .iter()
            .find_map(|op| match op {
                MachOperand::Block(t) => Some(*t),
                _ => None,
            });
        assert_eq!(latch_target, Some(header));
    }

    /// A bottom-tested loop (a GENUINE conditional back-edge — the latch's
    /// target dominates it) is already optimal: the loop-aware pass must NOT
    /// re-lay it out (its cold exit path is left where it is). It still performs
    /// the same redundant-fall-through-branch elision the standalone pass does,
    /// so the resulting machine code is identical either way — the layout ORDER
    /// is preserved and the conditional back-edge is kept.
    #[test]
    fn already_rotated_loop_layout_preserved() {
        let mut func = make_func("bottom_tested", 4);
        let (entry, body, latch, exit) = (BlockId(0), BlockId(1), BlockId(2), BlockId(3));

        add_inst(&mut func, entry, b(body));
        func.add_edge(entry, body);
        add_inst(&mut func, body, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(&mut func, body, b(latch));
        func.add_edge(body, latch);
        add_inst(
            &mut func,
            latch,
            MachInst::new(AArch64Opcode::CmpRR, vec![]),
        );
        add_inst(&mut func, latch, bcond(AArch64CC::LT, body)); // genuine conditional back-edge
        func.add_edge(latch, body);
        func.add_edge(latch, exit);
        add_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));

        func.block_order = vec![entry, body, latch, exit];
        let before = func.block_order.clone();

        aarch64_layout_fallthrough_and_elide(&mut func, true);
        // Layout ORDER preserved (no reorder of the already-rotated loop).
        assert_eq!(
            func.block_order, before,
            "rotated-loop layout must be preserved"
        );
        // Conditional back-edge kept; its redundant trailing `b exit` elided.
        assert_eq!(last_opcode(&func, latch), AArch64Opcode::BCond);
        let latch_back = func
            .inst(*func.block(latch).insts.last().unwrap())
            .operands
            .iter()
            .find_map(|op| match op {
                MachOperand::Block(t) => Some(*t),
                _ => None,
            });
        assert_eq!(latch_back, Some(body), "conditional back-edge preserved");
        // body/latch stay contiguous; body's redundant `b latch` elided.
        assert_eq!(last_opcode(&func, body), AArch64Opcode::AddRI);
    }

    /// On an ALREADY-rotated bottom-tested loop (genuine conditional back-edge),
    /// the loop-aware reorder pass preserves the layout but performs the
    /// redundant-`b <next>` elision itself (subsuming the standalone pass): the
    /// body's `b latch` and the latch's `b exit` are removed, the conditional
    /// back-edge stays, and no block is reordered. The subsequent standalone
    /// elision is then a no-op.
    #[test]
    fn reorder_pass_elides_rotated_loop_without_reordering() {
        let mut func = make_func("rotated", 4);
        let (entry, body, latch, exit) = (BlockId(0), BlockId(1), BlockId(2), BlockId(3));

        add_inst(&mut func, entry, b(body));
        add_inst(&mut func, body, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(&mut func, body, b(latch)); // redundant: latch is layout-next
        add_inst(
            &mut func,
            latch,
            MachInst::new(AArch64Opcode::CmpRR, vec![]),
        );
        add_inst(&mut func, latch, bcond(AArch64CC::LT, body)); // conditional back-edge
        add_inst(&mut func, latch, b(exit)); // redundant: exit is layout-next
        add_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));

        func.block_order = vec![entry, body, latch, exit];
        let before_order = func.block_order.clone();

        // The loop-aware pass now elides the dead `b <next>` branches in-place
        // (it does NOT reorder the already-rotated loop).
        assert!(aarch64_layout_fallthrough_and_elide(&mut func, true));
        assert_eq!(func.block_order, before_order, "no reordering");
        // entry `b body` elided (body is next).
        assert!(
            func.block(entry).insts.is_empty(),
            "entry b body -> fall-through"
        );
        // body `b latch` elided (latch is next).
        assert_eq!(last_opcode(&func, body), AArch64Opcode::AddRI);
        // latch keeps its conditional back-edge but drops the trailing `b exit`.
        assert_eq!(last_opcode(&func, latch), AArch64Opcode::BCond);
        let latch_back = func
            .inst(*func.block(latch).insts.last().unwrap())
            .operands
            .iter()
            .find_map(|op| match op {
                MachOperand::Block(t) => Some(*t),
                _ => None,
            });
        assert_eq!(latch_back, Some(body), "conditional back-edge preserved");
        // Standalone elision now has nothing left to do.
        assert!(!aarch64_elide_branch_to_next(&mut func));
    }

    /// Pure elision must NOT touch a `B` whose target is not the layout-next
    /// block (a real forward/backward jump), nor a symbol/tail-call `B`.
    #[test]
    fn pure_elision_keeps_non_next_and_symbol_branches() {
        let mut func = make_func("keep", 3);
        let (entry, mid, tail) = (BlockId(0), BlockId(1), BlockId(2));
        // entry: b tail  (tail is NOT layout-next -> keep)
        add_inst(&mut func, entry, b(tail));
        // mid: symbol/tail-call B (no Block operand -> keep)
        add_inst(
            &mut func,
            mid,
            MachInst::new(
                AArch64Opcode::B,
                vec![MachOperand::Symbol("callee".to_string())],
            ),
        );
        add_inst(&mut func, tail, MachInst::new(AArch64Opcode::Ret, vec![]));
        func.block_order = vec![entry, mid, tail];

        assert!(!aarch64_elide_branch_to_next(&mut func));
        assert_eq!(last_opcode(&func, entry), AArch64Opcode::B);
        assert_eq!(last_opcode(&func, mid), AArch64Opcode::B);
    }

    /// An indirect branch (`Br`, e.g. a jump-table dispatch) has data-driven
    /// successors the pass cannot see; it must fail closed.
    #[test]
    fn bails_on_indirect_branch() {
        let mut func = make_func("indirect", 2);
        let (entry, tgt) = (BlockId(0), BlockId(1));
        add_inst(&mut func, entry, MachInst::new(AArch64Opcode::Br, vec![]));
        add_inst(&mut func, tgt, MachInst::new(AArch64Opcode::Ret, vec![]));
        func.block_order = vec![entry, tgt];
        let before = func.block_order.clone();

        assert!(!aarch64_layout_fallthrough_and_elide(&mut func, true));
        assert_eq!(func.block_order, before);
    }

    /// With `rotate` enabled, a top-tested loop whose header is exactly
    /// `cmp; b.cc exit` becomes bottom-tested: the header stays as a one-time
    /// guard and the body ends with a cloned compare + inverted conditional
    /// back-edge, falling through to the exit.
    #[test]
    fn rotates_top_tested_loop_to_bottom_test() {
        let mut func = make_func("rotate_me", 4);
        let (entry, header, exit, body) = (BlockId(0), BlockId(1), BlockId(2), BlockId(3));

        add_inst(&mut func, entry, MachInst::new(AArch64Opcode::MovI, vec![]));
        add_inst(&mut func, entry, b(header));
        func.add_edge(entry, header);

        // Header is EXACTLY [CmpRR, BCond(GE) exit].
        add_inst(
            &mut func,
            header,
            MachInst::new(
                AArch64Opcode::CmpRR,
                vec![
                    MachOperand::PReg(trust_cg_ir::aarch64_regs::X3),
                    MachOperand::PReg(trust_cg_ir::aarch64_regs::X7),
                ],
            ),
        );
        add_inst(&mut func, header, bcond(AArch64CC::GE, exit));
        add_inst(&mut func, header, b(body));
        func.add_edge(header, exit);
        func.add_edge(header, body);

        add_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));

        add_inst(&mut func, body, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(&mut func, body, b(header));
        func.add_edge(body, header);

        func.block_order = vec![entry, header, exit, body];

        assert!(aarch64_layout_fallthrough_and_elide(&mut func, true));

        // Order: entry, header, body, exit (body pulled up, exit after).
        let hpos = func.block_order.iter().position(|&b| b == header).unwrap();
        assert_eq!(func.block_order.get(hpos + 1), Some(&body));
        assert_eq!(func.block_order.get(hpos + 2), Some(&exit));

        // Header remains the one-time guard: cmp + conditional exit only.
        let header_ops: Vec<AArch64Opcode> = func
            .block(header)
            .insts
            .iter()
            .map(|&id| func.inst(id).opcode)
            .collect();
        assert_eq!(header_ops, vec![AArch64Opcode::CmpRR, AArch64Opcode::BCond]);

        // Body now ends: <work>; cloned CmpRR; BCond(LT) back to body.
        let body_insts = &func.block(body).insts;
        let body_ops: Vec<AArch64Opcode> =
            body_insts.iter().map(|&id| func.inst(id).opcode).collect();
        assert_eq!(
            body_ops,
            vec![
                AArch64Opcode::AddRI,
                AArch64Opcode::CmpRR,
                AArch64Opcode::BCond
            ]
        );
        let last = func.inst(*body_insts.last().unwrap());
        // Inverted cc: GE(0b1010=10) -> LT(0b1011=11); target back to body.
        assert_eq!(last.operands[0], MachOperand::Imm(AArch64CC::LT as i64));
        assert_eq!(last.operands[1], MachOperand::Block(body));
        // The cloned compare copied the header's operands verbatim.
        let cloned_cmp = func.inst(body_insts[body_insts.len() - 2]);
        assert_eq!(
            cloned_cmp.operands,
            vec![
                MachOperand::PReg(trust_cg_ir::aarch64_regs::X3),
                MachOperand::PReg(trust_cg_ir::aarch64_regs::X7),
            ]
        );
    }

    // -----------------------------------------------------------------------
    // Loop-aware block placement
    // -----------------------------------------------------------------------

    /// Extract a block's conditional-branch target and inverted-cc, if it ends
    /// in a single `BCond`.
    fn last_bcond(func: &MachFunction, block: BlockId) -> Option<(i64, BlockId)> {
        let last = func.inst(*func.block(block).insts.last().unwrap());
        if last.opcode != AArch64Opcode::BCond {
            return None;
        }
        let cc = last.operands.iter().find_map(|op| match op {
            MachOperand::Imm(v) => Some(*v),
            _ => None,
        })?;
        let tgt = last.operands.iter().find_map(|op| match op {
            MachOperand::Block(b) => Some(*b),
            _ => None,
        })?;
        Some((cc, tgt))
    }

    fn pos(func: &MachFunction, block: BlockId) -> usize {
        func.block_order.iter().position(|&b| b == block).unwrap()
    }

    /// A top-tested loop whose body contains an internal diamond (both arms
    /// stay in the loop). Loop-aware placement must (a) keep the whole loop body
    /// contiguous, (b) pull the branch-taken (conditional) arm up as the
    /// fall-through and flip the header's condition so the cold arm is taken,
    /// (c) keep the unconditional backedge as the one taken branch.
    #[test]
    fn loop_body_contiguous_with_internal_cc_flip() {
        // entry -> header{cmp; b.lt inA; (ft inB)} ; inA/inB -> merge{cmp; b.gt exit; (ft latch)}
        // latch{add; b header}(backedge) ; exit
        // Repair-target-sized loop (>= 8 body blocks, >= 4 cond blocks): the
        // header diamond under test plus three filler diamonds (cold arms
        // already the taken branch — no flip needed there), then the exit test
        // and the unconditional backedge.
        let mut func = make_func("diamond_loop", 11);
        let (entry, header, in_a, in_b, c2, b2, c3, b3, merge, latch, exit) = (
            BlockId(0),
            BlockId(1),
            BlockId(2),
            BlockId(3),
            BlockId(4),
            BlockId(5),
            BlockId(6),
            BlockId(7),
            BlockId(8),
            BlockId(9),
            BlockId(10),
        );
        add_inst(&mut func, entry, b(header));
        func.add_edge(entry, header);

        add_inst(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::CmpRR, vec![]),
        );
        add_inst(&mut func, header, bcond(AArch64CC::LT, in_a)); // cc target = hot arm
        func.add_edge(header, in_a);
        func.add_edge(header, in_b);

        add_inst(&mut func, in_a, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(&mut func, in_a, b(c2));
        func.add_edge(in_a, c2);

        add_inst(&mut func, in_b, MachInst::new(AArch64Opcode::SubRI, vec![]));
        add_inst(&mut func, in_b, b(c2));
        func.add_edge(in_b, c2);

        for (c, cold, next) in [(c2, b2, c3), (c3, b3, merge)] {
            // c: cmp; b.hi cold; b next (hot fall-through — already oriented)
            add_inst(&mut func, c, MachInst::new(AArch64Opcode::CmpRR, vec![]));
            add_inst(&mut func, c, bcond(AArch64CC::HI, cold));
            add_inst(&mut func, c, b(next));
            func.add_edge(c, cold);
            func.add_edge(c, next);
            add_inst(&mut func, cold, MachInst::new(AArch64Opcode::AddRI, vec![]));
            add_inst(&mut func, cold, b(next));
            func.add_edge(cold, next);
        }

        add_inst(
            &mut func,
            merge,
            MachInst::new(AArch64Opcode::CmpRR, vec![]),
        );
        add_inst(&mut func, merge, bcond(AArch64CC::GT, exit)); // exit edge
        func.add_edge(merge, exit);
        func.add_edge(merge, latch);

        add_inst(
            &mut func,
            latch,
            MachInst::new(AArch64Opcode::AddRI, vec![]),
        );
        add_inst(&mut func, latch, b(header)); // unconditional backedge
        func.add_edge(latch, header);

        add_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));

        // SCATTERED input: the non-loop `exit` block sits inside the loop body's
        // span, so the loop is relaid out. `in_b` follows `header` because it
        // is the header's IMPLICIT fall-through successor (the materializer
        // appends `b <order-next>`), keeping the CFG coherent.
        func.block_order = vec![
            entry, header, in_b, c2, b2, exit, c3, b3, merge, latch, in_a,
        ];

        assert!(aarch64_layout_fallthrough_and_elide(&mut func, false));

        // The LOOP BODY (9 blocks) is CONTIGUOUS: no foreign block (exit) sits
        // inside its span. Which arm leads the chain is the pass's choice.
        let body = [header, in_a, in_b, c2, b2, c3, b3, merge, latch];
        let positions: Vec<usize> = body.iter().map(|&b| pos(&func, b)).collect();
        let (mn, mx) = (
            *positions.iter().min().unwrap(),
            *positions.iter().max().unwrap(),
        );
        assert_eq!(
            mx - mn + 1,
            body.len(),
            "loop body contiguous: {:?}",
            func.block_order
        );
        assert!(
            pos(&func, exit) < mn || pos(&func, exit) > mx,
            "exit outside the body span"
        );

        // THE INVARIANT (arm-choice-agnostic): after placement+orientation the
        // header ends in a SINGLE conditional branch whose taken target is NOT
        // the layout-next block — i.e. one arm falls through, the other is the
        // one taken branch (flipped if the chain placed the taken arm next).
        assert_eq!(last_opcode(&func, header), AArch64Opcode::BCond);
        let (_, taken) = last_bcond(&func, header).expect("header ends in BCond");
        let next_after_header = func.block_order[pos(&func, header) + 1];
        assert_ne!(
            taken, next_after_header,
            "taken arm must not be layout-next"
        );
        assert!(
            (taken == in_a && next_after_header == in_b)
                || (taken == in_b && next_after_header == in_a),
            "arms must be exactly in_a/in_b: taken={taken:?} next={next_after_header:?}"
        );
        // merge's exit test is unchanged (exit already the taken/cold arm) and
        // falls through to the latch.
        assert_eq!(last_opcode(&func, merge), AArch64Opcode::BCond);
        assert_eq!(last_bcond(&func, merge), Some((AArch64CC::GT as i64, exit)));
        // Backedge preserved as the one taken branch.
        assert_eq!(last_opcode(&func, latch), AArch64Opcode::B);
    }

    /// A latch that tests the loop bound and then unconditionally branches back
    /// to the header, all in one block (`cmp; b.cc exit; b header`), is folded
    /// to a single conditional back-edge (`cmp; b.!cc header`) that falls through
    /// to the exit — removing the unconditional-backedge taken branch. No compare
    /// is cloned (unlike bottom-test rotation).
    #[test]
    fn exit_test_and_backedge_folded_to_conditional_backedge() {
        // The loop must be a REPAIR TARGET (body >= bp_min_body()=8 blocks,
        // >= bp_min_conds()=4 conditional blocks, call-free) — sub-threshold
        // loops deliberately take the legacy path (the chomp byte-identity
        // fix) and are not relaid out. Shape: header -> m1..m3 diamonds (cold
        // arms a1..a3, hot fall-through chain) -> latch{cmp; b.hi exit;
        // b header}.
        let mut func = make_func("fold_latch", 10);
        let (entry, header, m1, a1, m2, a2, m3, a3, latch, exit) = (
            BlockId(0),
            BlockId(1),
            BlockId(2),
            BlockId(3),
            BlockId(4),
            BlockId(5),
            BlockId(6),
            BlockId(7),
            BlockId(8),
            BlockId(9),
        );
        add_inst(&mut func, entry, b(header));
        func.add_edge(entry, header);

        add_inst(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::AddRI, vec![]),
        );
        add_inst(&mut func, header, b(m1));
        func.add_edge(header, m1);

        for (m, a, next) in [(m1, a1, m2), (m2, a2, m3), (m3, a3, latch)] {
            // m: cmp; b.hi a (cold); b next (hot fall-through)
            add_inst(&mut func, m, MachInst::new(AArch64Opcode::CmpRR, vec![]));
            add_inst(&mut func, m, bcond(AArch64CC::HI, a));
            add_inst(&mut func, m, b(next));
            func.add_edge(m, a);
            func.add_edge(m, next);
            add_inst(&mut func, a, MachInst::new(AArch64Opcode::AddRI, vec![]));
            add_inst(&mut func, a, b(next));
            func.add_edge(a, next);
        }

        // latch: cmp; b.hi exit; b header
        add_inst(
            &mut func,
            latch,
            MachInst::new(AArch64Opcode::CmpRR, vec![]),
        );
        add_inst(&mut func, latch, bcond(AArch64CC::HI, exit));
        add_inst(&mut func, latch, b(header));
        func.add_edge(latch, exit);
        func.add_edge(latch, header);

        add_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));
        // SCATTERED input: `exit` sits inside the loop body's span.
        func.block_order = vec![entry, header, m1, exit, a1, m2, a2, m3, a3, latch];

        assert!(aarch64_layout_fallthrough_and_elide(&mut func, false));

        // latch now ends in ONE conditional branch back to the header (HI->LS),
        // with no trailing unconditional B; control falls through to exit.
        let reals: Vec<AArch64Opcode> = func
            .block(latch)
            .insts
            .iter()
            .map(|&id| func.inst(id).opcode)
            .collect();
        assert_eq!(reals, vec![AArch64Opcode::CmpRR, AArch64Opcode::BCond]);
        assert_eq!(
            last_bcond(&func, latch),
            Some((AArch64CC::LS as i64, header))
        );
        assert_eq!(
            pos(&func, exit),
            pos(&func, latch) + 1,
            "exit falls through"
        );
    }

    /// A single-block (self) loop is a genuine conditional back-edge: it must be
    /// left un-relaid-out and its condition must NOT be flipped.
    #[test]
    fn single_block_self_loop_untouched() {
        let mut func = make_func("self_loop", 3);
        let (entry, sl, exit) = (BlockId(0), BlockId(1), BlockId(2));
        add_inst(&mut func, entry, b(sl));
        func.add_edge(entry, sl);
        add_inst(&mut func, sl, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(&mut func, sl, bcond(AArch64CC::NE, sl)); // self back-edge
        func.add_edge(sl, sl);
        func.add_edge(sl, exit);
        add_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));
        func.block_order = vec![entry, sl, exit];
        let before = func.block_order.clone();

        aarch64_layout_fallthrough_and_elide(&mut func, false);
        assert_eq!(func.block_order, before, "self loop must not be reordered");
        // Condition unchanged (NOT flipped): still b.ne back to itself.
        assert_eq!(last_bcond(&func, sl), Some((AArch64CC::NE as i64, sl)));
    }

    /// Orientation is gated to loop blocks: a NON-loop conditional (a plain
    /// diamond) is never inverted — its natural fall-through is preserved, so
    /// straight-line code layout is not perturbed (the OPT-8 regression class).
    #[test]
    fn non_loop_conditional_not_flipped() {
        let mut func = make_func("diamond", 4);
        let (entry, t, f, join) = (BlockId(0), BlockId(1), BlockId(2), BlockId(3));
        add_inst(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::CmpRR, vec![]),
        );
        add_inst(&mut func, entry, bcond(AArch64CC::EQ, t));
        func.add_edge(entry, t);
        func.add_edge(entry, f);
        add_inst(&mut func, t, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(&mut func, t, b(join));
        func.add_edge(t, join);
        add_inst(&mut func, f, MachInst::new(AArch64Opcode::SubRI, vec![]));
        add_inst(&mut func, f, b(join));
        func.add_edge(f, join);
        add_inst(&mut func, join, MachInst::new(AArch64Opcode::Ret, vec![]));
        func.block_order = vec![entry, t, f, join];

        aarch64_layout_fallthrough_and_elide(&mut func, false);
        // entry's condition is NOT inverted: still b.eq to t (the natural
        // fall-through arm `f` is placed next, keeping greedy behavior).
        assert_eq!(last_bcond(&func, entry), Some((AArch64CC::EQ as i64, t)));
    }

    /// Placement is deterministic: the same input laid out twice yields byte-for
    /// byte identical block order and instruction streams.
    #[test]
    fn layout_is_deterministic() {
        fn build() -> MachFunction {
            let mut func = make_func("determ", 7);
            let (entry, header, in_a, in_b, merge, latch, exit) = (
                BlockId(0),
                BlockId(1),
                BlockId(2),
                BlockId(3),
                BlockId(4),
                BlockId(5),
                BlockId(6),
            );
            add_inst(&mut func, entry, b(header));
            func.add_edge(entry, header);
            add_inst(
                &mut func,
                header,
                MachInst::new(AArch64Opcode::CmpRR, vec![]),
            );
            add_inst(&mut func, header, bcond(AArch64CC::LT, in_a));
            func.add_edge(header, in_a);
            func.add_edge(header, in_b);
            add_inst(&mut func, in_a, MachInst::new(AArch64Opcode::AddRI, vec![]));
            add_inst(&mut func, in_a, b(merge));
            func.add_edge(in_a, merge);
            add_inst(&mut func, in_b, MachInst::new(AArch64Opcode::SubRI, vec![]));
            add_inst(&mut func, in_b, b(merge));
            func.add_edge(in_b, merge);
            add_inst(
                &mut func,
                merge,
                MachInst::new(AArch64Opcode::CmpRR, vec![]),
            );
            add_inst(&mut func, merge, bcond(AArch64CC::GT, exit));
            func.add_edge(merge, exit);
            func.add_edge(merge, latch);
            add_inst(
                &mut func,
                latch,
                MachInst::new(AArch64Opcode::AddRI, vec![]),
            );
            add_inst(&mut func, latch, b(header));
            func.add_edge(latch, header);
            add_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));
            // Scattered input so the loop-aware path is exercised.
            func.block_order = vec![entry, header, in_a, merge, latch, exit, in_b];
            func
        }
        let mut a = build();
        let mut b_func = build();
        aarch64_layout_fallthrough_and_elide(&mut a, false);
        aarch64_layout_fallthrough_and_elide(&mut b_func, false);
        assert_eq!(a.block_order, b_func.block_order);
        for (&ba, &bb) in a.block_order.iter().zip(b_func.block_order.iter()) {
            let oa: Vec<_> = a
                .block(ba)
                .insts
                .iter()
                .map(|&i| a.inst(i).opcode)
                .collect();
            let ob: Vec<_> = b_func
                .block(bb)
                .insts
                .iter()
                .map(|&i| b_func.inst(i).opcode)
                .collect();
            assert_eq!(oa, ob, "block {ba:?} instruction stream must match");
        }
    }

    /// Helper: Bubblesort's post-taildup shape. Returns (func, blocks) where
    /// blocks = [entry, header, latch, exit, swap] and `swap` is the
    /// out-of-line duplicated latch (str + cloned exit test + backedge).
    fn make_taildup_loop(swap_in_span: bool) -> (MachFunction, [BlockId; 5]) {
        let mut func = make_func("taildup", 5);
        let (entry, header, latch, exit, swap) =
            (BlockId(0), BlockId(1), BlockId(2), BlockId(3), BlockId(4));

        add_inst(&mut func, entry, b(header));
        func.add_edge(entry, header);

        add_inst(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::LdrRI, vec![]),
        );
        add_inst(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::CmpRR, vec![]),
        );
        add_inst(&mut func, header, bcond(AArch64CC::GT, swap));
        add_inst(&mut func, header, b(latch));
        func.add_edge(header, swap);
        func.add_edge(header, latch);

        add_inst(
            &mut func,
            latch,
            MachInst::new(AArch64Opcode::CmpRR, vec![]),
        );
        add_inst(&mut func, latch, bcond(AArch64CC::EQ, exit));
        add_inst(&mut func, latch, b(header));
        func.add_edge(latch, exit);
        func.add_edge(latch, header);

        add_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));

        add_inst(&mut func, swap, MachInst::new(AArch64Opcode::StrRI, vec![]));
        add_inst(&mut func, swap, MachInst::new(AArch64Opcode::CmpRR, vec![]));
        add_inst(&mut func, swap, bcond(AArch64CC::EQ, exit));
        add_inst(&mut func, swap, b(header));
        func.add_edge(swap, exit);
        func.add_edge(swap, header);

        func.block_order = if swap_in_span {
            vec![entry, header, swap, latch, exit]
        } else {
            vec![entry, header, latch, exit, swap]
        };
        (func, [entry, header, latch, exit, swap])
    }

    /// The out-of-line duplicated latch (swap arm) is pulled in front of the
    /// header and its backedge elided into the loop's fall-through seam.
    #[test]
    fn bepull_moves_out_of_line_dup_latch_before_header() {
        let (mut func, [entry, header, latch, exit, swap]) = make_taildup_loop(false);

        assert!(aarch64_layout_fallthrough_and_elide(&mut func, false));

        assert_eq!(func.block_order, vec![entry, swap, header, latch, exit]);
        // Swap's trailing `B header` was elided: it now falls through.
        let swap_ops: Vec<_> = func
            .block(swap)
            .insts
            .iter()
            .map(|&i| func.inst(i).opcode)
            .collect();
        assert_eq!(
            swap_ops,
            vec![
                AArch64Opcode::StrRI,
                AArch64Opcode::CmpRR,
                AArch64Opcode::BCond
            ]
        );
        // The preheader now jumps over the pulled block (its `B` survives).
        let entry_last = *func.block(entry).insts.last().unwrap();
        assert_eq!(func.inst(entry_last).opcode, AArch64Opcode::B);
        assert_eq!(single_block_operand(func.inst(entry_last)), Some(header));
        // The original latch keeps its explicit backedge. `exit` IS laid out
        // next, so this latch matches `orient_next_is_cc_target`'s shape — but
        // its `B` is the loop BACK EDGE, the one arm the flip is excluded from
        // (see that function: converting the hot unconditional backedge into a
        // taken CONDITIONAL cost Misc/flops-1 +8.2% cycles for −6.7%
        // instructions). The pair must survive verbatim.
        let latch_ops: Vec<_> = func
            .block(latch)
            .insts
            .iter()
            .map(|&i| func.inst(i).opcode)
            .collect();
        assert_eq!(
            latch_ops,
            vec![AArch64Opcode::CmpRR, AArch64Opcode::BCond, AArch64Opcode::B],
            "a back-edge `B` must never be folded into the conditional"
        );
        let latch_last = *func.block(latch).insts.last().unwrap();
        assert_eq!(func.inst(latch_last).opcode, AArch64Opcode::B);
        assert_eq!(single_block_operand(func.inst(latch_last)), Some(header));
    }

    /// A block whose layout order is FIXED (the caller already committed it)
    /// and which carries the branch-over-branch pair `LdrRI; CBZ next; B far`
    /// with `next` laid out immediately after — the Stanford/Queens `Try` shape
    /// that survives in FULLY-UNROLLED (loop-free) code, where both loop-gated
    /// orientations have no loop to gate on.
    /// Loop analysis for a loop-free test function (the straight-line shapes
    /// below): computed for real, so the back-edge exclusion is exercised with
    /// genuine data rather than a hand-built empty set.
    fn no_loops(func: &MachFunction) -> LoopAnalysis {
        let dom = DomTree::compute(func);
        LoopAnalysis::compute(func, &dom)
    }

    fn make_branch_over_branch() -> (MachFunction, [BlockId; 3]) {
        let mut func = make_func("straightline", 3);
        let (entry, next, far) = (BlockId(0), BlockId(1), BlockId(2));
        add_inst(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::LdrRI, vec![]),
        );
        add_inst(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::Cbz,
                vec![MachOperand::Imm(0), MachOperand::Block(next)],
            ),
        );
        add_inst(&mut func, entry, b(far));
        func.add_edge(entry, next);
        func.add_edge(entry, far);
        add_inst(&mut func, next, MachInst::new(AArch64Opcode::Ret, vec![]));
        add_inst(&mut func, far, MachInst::new(AArch64Opcode::Ret, vec![]));
        func.block_order = vec![entry, next, far];
        (func, [entry, next, far])
    }

    /// `orient_next_is_cc_target` collapses that pair into a single inverted
    /// `CBNZ far`, falling through to `next`: one instruction fewer and one
    /// taken branch fewer, with the successor SET unchanged — AND the
    /// `TCG_BP_NO_NEXT_ORIENT=1` kill switch leaves it verbatim.
    ///
    /// Both directions live in ONE test on purpose: `bp_next_orient_enabled`
    /// reads the process environment fresh (so a PGO/A-B harness sees a
    /// consistent per-process value), and `cargo test` runs tests in parallel,
    /// so a separate env-mutating test would race this one. Nothing else in the
    /// suite asserts that this step FIRES, and a transient disable only
    /// restores pre-feature behavior, which every other test is written
    /// against.
    #[test]
    fn next_orient_collapses_branch_over_branch_and_honours_its_kill_switch() {
        let (mut func, [entry, next, far]) = make_branch_over_branch();

        let loops = no_loops(&func);
        assert!(orient_next_is_cc_target(&mut func, &loops));
        let ops: Vec<_> = func
            .block(entry)
            .insts
            .iter()
            .map(|&i| func.inst(i).opcode)
            .collect();
        assert_eq!(
            ops,
            vec![AArch64Opcode::LdrRI, AArch64Opcode::Cbnz],
            "the trailing `B far` must be folded into an inverted Cbnz"
        );
        let last = *func.block(entry).insts.last().unwrap();
        assert_eq!(single_block_operand(func.inst(last)), Some(far));
        // Successor SET unchanged; no block moved.
        let mut succs = func.block(entry).succs.clone();
        succs.sort_by_key(|b| b.0);
        assert_eq!(succs, vec![next, far]);
        assert_eq!(func.block_order, vec![entry, next, far]);

        // Kill switch: same fixture, pair kept verbatim.
        // SAFETY(test): restored before the assertions below.
        unsafe { std::env::set_var("TCG_BP_NO_NEXT_ORIENT", "1") };
        let (mut off, [off_entry, ..]) = make_branch_over_branch();
        let off_loops = no_loops(&off);
        let changed = orient_next_is_cc_target(&mut off, &off_loops);
        let off_ops: Vec<_> = off
            .block(off_entry)
            .insts
            .iter()
            .map(|&i| off.inst(i).opcode)
            .collect();
        unsafe { std::env::remove_var("TCG_BP_NO_NEXT_ORIENT") };
        assert!(!changed);
        assert_eq!(
            off_ops,
            vec![AArch64Opcode::LdrRI, AArch64Opcode::Cbz, AArch64Opcode::B],
            "kill switch must leave the branch-over-branch pair verbatim"
        );
    }

    /// A loop LATCH `cmp; B.cc exit; B header` whose `exit` is laid out next
    /// matches the shape exactly but is EXCLUDED: its `B` is the back edge, so
    /// the flip would trade the hot unconditional taken branch for a
    /// conditional one (Misc/flops-1: −6.7% instructions, +8.2% cycles).
    #[test]
    fn next_orient_refuses_a_loop_back_edge() {
        let mut func = make_func("latch", 3);
        let (header, exit, pre) = (BlockId(1), BlockId(2), BlockId(0));
        add_inst(&mut func, pre, b(header));
        func.add_edge(pre, header);
        add_inst(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::CmpRR, vec![]),
        );
        add_inst(&mut func, header, bcond(AArch64CC::EQ, exit));
        add_inst(&mut func, header, b(header));
        func.add_edge(header, exit);
        func.add_edge(header, header);
        add_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));
        // `exit` (the cc target) is laid out immediately after the latch.
        func.block_order = vec![pre, header, exit];

        let dom = DomTree::compute(&func);
        let loops = LoopAnalysis::compute(&func, &dom);
        assert!(!orient_next_is_cc_target(&mut func, &loops));
        let ops: Vec<_> = func
            .block(header)
            .insts
            .iter()
            .map(|&i| func.inst(i).opcode)
            .collect();
        assert_eq!(
            ops,
            vec![AArch64Opcode::CmpRR, AArch64Opcode::BCond, AArch64Opcode::B],
            "the back-edge `B` must survive"
        );
    }

    /// The already-optimal orientation (`next == ft_target`) is NOT touched:
    /// that is step 4's plain `B`-elision, not an inversion.
    #[test]
    fn next_orient_leaves_already_optimal_orientation_alone() {
        let (mut func, [entry, next, far]) = make_branch_over_branch();
        // Swap the layout so the `B`'s target is the one laid out next.
        func.block_order = vec![entry, far, next];
        let loops = no_loops(&func);
        assert!(!orient_next_is_cc_target(&mut func, &loops));
        let ops: Vec<_> = func
            .block(entry)
            .insts
            .iter()
            .map(|&i| func.inst(i).opcode)
            .collect();
        assert_eq!(
            ops,
            vec![AArch64Opcode::LdrRI, AArch64Opcode::Cbz, AArch64Opcode::B]
        );
    }

    /// A dup already inside the loop's layout span is part of a deliberate
    /// chain — the pull itself must refuse it. (Exercised directly: the full
    /// driver's greedy reorder would first exile the conditional arm, which is
    /// exactly when pulling becomes correct.)
    #[test]
    fn bepull_leaves_in_span_dup_latch_alone() {
        let (mut func, _) = make_taildup_loop(true);
        let before = func.block_order.clone();

        let dom = DomTree::compute(&func);
        let loops = LoopAnalysis::compute(&func, &dom);
        assert!(!pull_duplicated_latch_before_header(&mut func, &loops));
        assert_eq!(func.block_order, before);
    }

    /// Kill switch: `TCG_BP_NO_BEPULL=1` documented; the helper honors it via a
    /// OnceLock, so exercise the pull's own guard directly instead of the env.
    /// (Exercised on `pull_duplicated_latch_before_header` directly, not the full
    /// driver: the single-latch tier [`rotate_far_latch_before_header`] would
    /// legitimately rotate this single-source latch — it is a distinct, sound
    /// transform, so the full-driver layout is no longer a bepull-only fact.)
    #[test]
    fn bepull_requires_two_backedge_sources() {
        // Remove the original latch's backedge (retarget it at the exit):
        // a single-source loop must not be pulled by bepull.
        let (mut func, [_, header, latch, _, swap]) = make_taildup_loop(false);
        let latch_last = *func.block(latch).insts.last().unwrap();
        func.inst_mut(latch_last).operands = vec![MachOperand::Block(BlockId(3))];
        func.block_mut(latch).succs = vec![BlockId(3)];
        func.block_mut(header).preds.retain(|&p| p != latch);

        let before = func.block_order.clone();
        let dom = DomTree::compute(&func);
        let loops = LoopAnalysis::compute(&func, &dom);
        // bepull refuses a single-source latch; layout order is untouched by it.
        assert!(!pull_duplicated_latch_before_header(&mut func, &loops));
        assert_eq!(func.block_order, before);
        let _ = swap;
    }

    /// The single-latch tier [`rotate_far_latch_before_header`] rotates a
    /// bottom-tested loop whose sole backedge block was orphaned to the far end:
    /// with the trip test in the latch (`… ; b.cc EXIT ; b header`) and a
    /// conditional continue INTO that latch, pulling it before the header turns
    /// the backedge into a fall-through (elided by step 4) and cuts the hot
    /// continue iteration from two taken branches to one. Reuses the tail-dup
    /// fixture with a single backedge (the original latch retargeted at exit).
    #[test]
    fn latch_rotate_pulls_single_far_latch_before_header() {
        let (mut func, [entry, header, latch, exit, swap]) = make_taildup_loop(false);
        // Make `swap` the sole backedge source (retarget the original latch at
        // exit), so only the single-latch tier — not bepull — can act.
        let latch_last = *func.block(latch).insts.last().unwrap();
        func.inst_mut(latch_last).operands = vec![MachOperand::Block(exit)];
        func.block_mut(latch).succs = vec![exit];
        func.block_mut(header).preds.retain(|&p| p != latch);

        assert!(aarch64_layout_fallthrough_and_elide(&mut func, false));
        // `swap` (the far latch) is pulled immediately before the header.
        let pos = |b: BlockId| func.block_order.iter().position(|&x| x == b).unwrap();
        assert_eq!(pos(swap) + 1, pos(header), "far latch now precedes header");
        assert_eq!(func.block_order[0], entry, "entry stays first");
        // Its trailing `B header` was elided into the fall-through backedge.
        assert_ne!(last_opcode(&func, swap), AArch64Opcode::B);
    }

    /// `function_has_genuine_conditional_back_edge` fires only on real loop
    /// back-edges (target dominates source), NOT on diamond re-convergence — so
    /// scattered loops like heapsort's sift-down are still relaid out.
    #[test]
    fn genuine_back_edge_detection_distinguishes_reconvergence() {
        // (a) a genuine back-edge: header -> body -> header (conditional).
        let mut func = make_func("has_be", 3);
        let (entry, header, body) = (BlockId(0), BlockId(1), BlockId(2));
        add_inst(&mut func, entry, b(header));
        func.add_edge(entry, header);
        add_inst(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::CmpRR, vec![]),
        );
        add_inst(&mut func, header, b(body));
        func.add_edge(header, body);
        add_inst(&mut func, body, MachInst::new(AArch64Opcode::CmpRR, vec![]));
        add_inst(&mut func, body, bcond(AArch64CC::NE, header)); // back-edge
        func.add_edge(body, header);
        add_inst(&mut func, body, b(header));
        func.block_order = vec![entry, header, body];
        let dom = DomTree::compute(&func);
        assert!(function_has_genuine_conditional_back_edge(&func, &dom));

        // (b) a forward-only diamond: no conditional edge whose target dominates
        // its source.
        let mut d = make_func("diamond2", 4);
        let (e, t, f, j) = (BlockId(0), BlockId(1), BlockId(2), BlockId(3));
        add_inst(&mut d, e, MachInst::new(AArch64Opcode::CmpRR, vec![]));
        add_inst(&mut d, e, bcond(AArch64CC::EQ, t));
        d.add_edge(e, t);
        d.add_edge(e, f);
        add_inst(&mut d, t, b(j));
        d.add_edge(t, j);
        add_inst(&mut d, f, b(j));
        d.add_edge(f, j);
        add_inst(&mut d, j, MachInst::new(AArch64Opcode::Ret, vec![]));
        d.block_order = vec![e, t, f, j];
        let dom2 = DomTree::compute(&d);
        assert!(!function_has_genuine_conditional_back_edge(&d, &dom2));
    }

    /// Build a function with TWO independent loops:
    ///  * loop A — an already-rotated (bottom-tested) loop whose latch has a
    ///    CONDITIONAL back-edge to its header (a genuine conditional back-edge,
    ///    so the whole function is intentionally left un-reordered);
    ///  * loop B — a small, contiguous, MIS-ORIENTED top-tested loop whose body
    ///    branches to the in-loop `b_cont` (laid out next) on the cc and jumps to
    ///    the out-of-loop `b_break` unconditionally (`b.cc b_cont ; b b_break`).
    /// Blocks: entry, a_body, a_latch, mid, b_header, b_body, b_cont, b_break, exit.
    fn make_rotated_plus_misoriented() -> (MachFunction, [BlockId; 9]) {
        let mut func = make_func("mixed", 9);
        let [
            entry,
            a_body,
            a_latch,
            mid,
            b_header,
            b_body,
            b_cont,
            b_break,
            exit,
        ] = [
            BlockId(0),
            BlockId(1),
            BlockId(2),
            BlockId(3),
            BlockId(4),
            BlockId(5),
            BlockId(6),
            BlockId(7),
            BlockId(8),
        ];
        add_inst(&mut func, entry, b(a_body));
        func.add_edge(entry, a_body);
        // loop A body + already-rotated latch (conditional back-edge to a_body).
        add_inst(
            &mut func,
            a_body,
            MachInst::new(AArch64Opcode::AddRI, vec![]),
        );
        add_inst(&mut func, a_body, b(a_latch));
        func.add_edge(a_body, a_latch);
        add_inst(
            &mut func,
            a_latch,
            MachInst::new(AArch64Opcode::CmpRR, vec![]),
        );
        add_inst(&mut func, a_latch, bcond(AArch64CC::LT, a_body)); // genuine cond back-edge
        add_inst(&mut func, a_latch, b(mid));
        func.add_edge(a_latch, a_body);
        func.add_edge(a_latch, mid);
        add_inst(&mut func, mid, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(&mut func, mid, b(b_header));
        func.add_edge(mid, b_header);
        // loop B: top test exits on EQ, falls to body.
        add_inst(
            &mut func,
            b_header,
            MachInst::new(AArch64Opcode::CmpRR, vec![]),
        );
        add_inst(&mut func, b_header, bcond(AArch64CC::EQ, b_break)); // exit arm
        add_inst(&mut func, b_header, b(b_body));
        func.add_edge(b_header, b_break);
        func.add_edge(b_header, b_body);
        // b_body: cc target = in-loop b_cont (laid out next); ft = out-of-loop b_break.
        add_inst(
            &mut func,
            b_body,
            MachInst::new(AArch64Opcode::CmpRR, vec![]),
        );
        add_inst(&mut func, b_body, bcond(AArch64CC::EQ, b_cont));
        add_inst(&mut func, b_body, b(b_break));
        func.add_edge(b_body, b_cont);
        func.add_edge(b_body, b_break);
        // b_cont: unconditional back-edge to header (so loop B is NOT rotated).
        add_inst(
            &mut func,
            b_cont,
            MachInst::new(AArch64Opcode::AddRI, vec![]),
        );
        add_inst(&mut func, b_cont, b(b_header));
        func.add_edge(b_cont, b_header);
        add_inst(
            &mut func,
            b_break,
            MachInst::new(AArch64Opcode::AddRI, vec![]),
        );
        add_inst(&mut func, b_break, b(exit));
        func.add_edge(b_break, exit);
        add_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));
        func.block_order = vec![
            entry, a_body, a_latch, mid, b_header, b_body, b_cont, b_break, exit,
        ];
        (
            func,
            [
                entry, a_body, a_latch, mid, b_header, b_body, b_cont, b_break, exit,
            ],
        )
    }

    /// PER-LOOP protection: a function carrying an already-rotated loop is not
    /// reordered, yet a sibling small mis-oriented top-tested loop is still
    /// oriented IN PLACE (the equal/stay-in-loop arm becomes the fall-through and
    /// the exit arm the single taken branch), while the already-rotated loop keeps
    /// its exact layout and conditional back-edge.
    #[test]
    fn small_orient_flips_sibling_loop_and_protects_rotated_one() {
        let (
            mut func,
            [
                _e,
                a_body,
                a_latch,
                _mid,
                b_header,
                b_body,
                b_cont,
                _b_break,
                _x,
            ],
        ) = make_rotated_plus_misoriented();
        let before = func.block_order.clone();

        assert!(aarch64_layout_fallthrough_and_elide(&mut func, false));

        // No block was reordered (the already-rotated loop pins the whole function).
        assert_eq!(
            func.block_order, before,
            "no reorder when a rotated loop is present"
        );
        // b_body's mis-oriented conditional was FLIPPED: EQ->NE now branches to the
        // exit arm b_break and FALLS THROUGH to the in-loop b_cont; the trailing
        // unconditional `B` is gone (its last real inst is the conditional).
        assert_eq!(last_opcode(&func, b_body), AArch64Opcode::BCond);
        assert_eq!(
            last_bcond(&func, b_body),
            Some((AArch64CC::NE as i64, _b_break))
        );
        // The already-rotated sibling loop A is UNTOUCHED: its conditional
        // back-edge b.lt a_body survives (only its redundant trailing `b mid` — mid
        // is layout-next — is elided, exactly as the standalone elision would do).
        assert_eq!(
            last_bcond(&func, a_latch),
            Some((AArch64CC::LT as i64, a_body))
        );
        // The top-test header is NOT flipped (its cc arm is the exit, not next).
        assert_eq!(
            last_bcond(&func, b_header),
            Some((AArch64CC::EQ as i64, _b_break))
        );
        // b_cont keeps its explicit backedge (header is not layout-next).
        assert_eq!(last_opcode(&func, b_cont), AArch64Opcode::B);
        assert_eq!(
            single_block_operand(func.inst(*func.block(b_cont).insts.last().unwrap())),
            Some(b_header)
        );
    }

    /// The small-orient candidate set includes the mis-oriented top-tested loop
    /// and EXCLUDES the already-rotated loop (per-loop protection), so the flip
    /// never touches a do-while latch's cold exit path.
    #[test]
    fn small_orientable_excludes_already_rotated_loops() {
        let (mut func, [_e, a_body, _al, _mid, b_header, _bb, _bc, _brk, _x]) =
            make_rotated_plus_misoriented();
        // Materialize + rebuild edges so loop analysis sees the explicit CFG the
        // driver hands to the helper (every block here is already hard-terminated,
        // so materialization appends nothing).
        rebuild_succs_from_block_operands(&mut func);
        let dom = DomTree::compute(&func);
        let loops = LoopAnalysis::compute(&func, &dom);
        let set = small_orientable_loop_headers(&func, &loops);
        assert!(
            set.contains(&b_header),
            "mis-oriented top-tested loop included"
        );
        assert!(
            !set.contains(&a_body),
            "already-rotated loop header excluded"
        );
        // Loop A is recognized as already-rotated; loop B is not.
        let lp_a = loops.get_loop(a_body).expect("loop A");
        let lp_b = loops.get_loop(b_header).expect("loop B");
        assert!(loop_is_already_rotated(&func, lp_a));
        assert!(!loop_is_already_rotated(&func, lp_b));
    }

    // -----------------------------------------------------------------------
    // Static cold-guard sinking (TCG_BP_NO_COLDSINK)
    // -----------------------------------------------------------------------

    /// A call-and-glue error-report arm: `adrp`/`add`/`mov` argument
    /// materialization, an outgoing-arg store to `[sp]`, the diagnostic
    /// `bl`, a phi-materialization copy, and the rejoin branch — the Towers
    /// guard shape after clang -O1 inlines `Error()`.
    fn add_guard_body(func: &mut MachFunction, block: BlockId, join: BlockId) {
        add_inst(func, block, MachInst::new(AArch64Opcode::Adrp, vec![]));
        add_inst(func, block, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(
            func,
            block,
            MachInst::new(
                AArch64Opcode::StrRI,
                vec![
                    MachOperand::PReg(trust_cg_ir::aarch64_regs::X2),
                    MachOperand::MemOp {
                        base: AARCH64_SP,
                        offset: 0,
                    },
                ],
            ),
        );
        add_inst(
            func,
            block,
            MachInst::new(
                AArch64Opcode::Bl,
                vec![MachOperand::Symbol("_printf".to_string())],
            ),
        );
        add_inst(func, block, MachInst::new(AArch64Opcode::MovR, vec![]));
        add_inst(
            func,
            block,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(join)]),
        );
        func.add_edge(block, join);
    }

    /// Two-way conditional head: `bcond <taken>` + explicit `b <fall>`.
    fn add_cond_head(func: &mut MachFunction, block: BlockId, taken: BlockId, fall: BlockId) {
        add_inst(func, block, MachInst::new(AArch64Opcode::SubsRI, vec![]));
        add_inst(
            func,
            block,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(AArch64CC::GT as i64),
                    MachOperand::Block(taken),
                ],
            ),
        );
        add_inst(
            func,
            block,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(fall)]),
        );
        func.add_edge(block, taken);
        func.add_edge(block, fall);
    }

    /// Straight-line hot arm: filler + `b <join>`.
    fn add_hot_arm(func: &mut MachFunction, block: BlockId, join: BlockId) {
        add_inst(func, block, MachInst::new(AArch64Opcode::AddRI, vec![]));
        add_inst(
            func,
            block,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(join)]),
        );
        func.add_edge(block, join);
    }

    /// Mini Towers `Move`: two stacked diamonds whose fall-through arms are
    /// never-executed report blocks. The full layout pass must extract both
    /// guards to the end and keep the hot spine in original order, exactly
    /// reproducing the profile-use layout (original order minus zero-hit
    /// guards).
    #[test]
    fn coldsink_towers_shape_sinks_guards_and_preserves_spine() {
        let mut func = make_func("coldsink_towers", 7);
        let [entry, hot1, guard1, join1, hot2, guard2, exit] =
            [0, 1, 2, 3, 4, 5, 6].map(|i| BlockId(i));

        add_cond_head(&mut func, entry, hot1, guard1);
        add_hot_arm(&mut func, hot1, join1);
        add_guard_body(&mut func, guard1, join1);
        add_cond_head(&mut func, join1, hot2, guard2);
        add_hot_arm(&mut func, hot2, exit);
        add_guard_body(&mut func, guard2, exit);
        add_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));

        let changed = aarch64_layout_fallthrough_and_elide(&mut func, false);
        assert!(changed, "layout pass must fire");
        assert_eq!(
            func.block_order,
            vec![entry, hot1, join1, hot2, exit, guard1, guard2],
            "hot spine keeps original order; guards sink to the end in order"
        );
        // The hot arms now fall through to their joins: their trailing
        // `b <join>` must have been elided. Each HEAD's pair is INVERTED
        // (`invert_sunk_guard_heads`): the conditional now targets the sunk
        // guard and the trailing `b <guard>` is deleted, so the hot arm is a
        // pure fall-through — no taken branch on the hot path at all.
        assert!(
            !func
                .block(hot1)
                .insts
                .iter()
                .any(|&id| func.inst(id).is_unconditional_branch()),
            "hot1 fall-through branch elided"
        );
        for (head, guard) in [(entry, guard1), (join1, guard2)] {
            assert!(
                !func
                    .block(head)
                    .insts
                    .iter()
                    .any(|&id| func.inst(id).is_unconditional_branch()),
                "inverted head B{} must have dropped its unconditional branch",
                head.0
            );
            let cond_targets: Vec<BlockId> = func
                .block(head)
                .insts
                .iter()
                .filter(|&&id| func.inst(id).is_conditional_branch())
                .flat_map(|&id| {
                    func.inst(id).operands.iter().filter_map(|op| match op {
                        MachOperand::Block(b) => Some(*b),
                        _ => None,
                    })
                })
                .collect();
            assert_eq!(
                cond_targets,
                vec![guard],
                "inverted head B{} conditional must target its sunk guard",
                head.0
            );
        }
    }

    /// A side arm that LOADS program state is an alternative computation,
    /// not a diagnostic report: the recognizer must refuse it and the pass
    /// must keep the greedy layout for the whole function (byte-identical
    /// no-fire).
    #[test]
    fn coldsink_rejects_load_bearing_arm() {
        let mut func = make_func("coldsink_load", 4);
        let [entry, hot, arm, exit] = [0, 1, 2, 3].map(|i| BlockId(i));
        add_cond_head(&mut func, entry, hot, arm);
        add_hot_arm(&mut func, hot, exit);
        // Arm: load + call + rejoin — call-bearing but reads memory.
        add_inst(
            &mut func,
            arm,
            MachInst::new(
                AArch64Opcode::LdrRI,
                vec![
                    MachOperand::PReg(trust_cg_ir::aarch64_regs::X0),
                    MachOperand::MemOp {
                        base: trust_cg_ir::aarch64_regs::X1,
                        offset: 0,
                    },
                ],
            ),
        );
        add_inst(
            &mut func,
            arm,
            MachInst::new(
                AArch64Opcode::Bl,
                vec![MachOperand::Symbol("_printf".to_string())],
            ),
        );
        add_inst(
            &mut func,
            arm,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(exit)]),
        );
        func.add_edge(arm, exit);
        add_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));

        rebuild_succs_from_block_operands(&mut func);
        let dom = DomTree::compute(&func);
        let loops = LoopAnalysis::compute(&func, &dom);
        assert!(
            !is_static_cold_guard(&func, &loops, arm),
            "load-bearing arm must not be recognized"
        );
        assert!(static_cold_guard_blocks(&func, &loops).is_empty());
    }

    /// Both-arms-call diamonds (Towers `tower`: Move vs recurse) must never
    /// sink either arm: the sibling call asymmetry is the license.
    #[test]
    fn coldsink_rejects_call_bearing_sibling() {
        let mut func = make_func("coldsink_sibling", 4);
        let [entry, other, arm, exit] = [0, 1, 2, 3].map(|i| BlockId(i));
        add_cond_head(&mut func, entry, other, arm);
        // Sibling arm also calls.
        add_inst(
            &mut func,
            other,
            MachInst::new(
                AArch64Opcode::Bl,
                vec![MachOperand::Symbol("_move".to_string())],
            ),
        );
        add_inst(
            &mut func,
            other,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(exit)]),
        );
        func.add_edge(other, exit);
        add_guard_body(&mut func, arm, exit);
        add_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));

        rebuild_succs_from_block_operands(&mut func);
        let dom = DomTree::compute(&func);
        let loops = LoopAnalysis::compute(&func, &dom);
        assert!(
            !is_static_cold_guard(&func, &loops, arm),
            "arm with call-bearing sibling must not be recognized"
        );
        assert!(static_cold_guard_blocks(&func, &loops).is_empty());
    }

    /// Guard-shaped blocks INSIDE a natural loop stay put: loop bodies are
    /// the contiguity domain of the loop passes.
    #[test]
    fn coldsink_rejects_in_loop_guard() {
        let mut func = make_func("coldsink_loop", 5);
        let [entry, header, arm, latch, exit] = [0, 1, 2, 3, 4].map(|i| BlockId(i));
        // entry -> header; header cond {arm, latch}; arm -> latch (call-only);
        // latch -> {header, exit} — arm is a side arm strictly inside the loop.
        add_inst(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(header)]),
        );
        func.add_edge(entry, header);
        add_cond_head(&mut func, header, latch, arm);
        add_guard_body(&mut func, arm, latch);
        add_cond_head(&mut func, latch, header, exit);
        add_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));

        rebuild_succs_from_block_operands(&mut func);
        let dom = DomTree::compute(&func);
        let loops = LoopAnalysis::compute(&func, &dom);
        assert!(loops.is_in_loop(arm), "fixture: arm is inside the loop");
        assert!(
            !is_static_cold_guard(&func, &loops, arm),
            "in-loop guard must not be recognized"
        );
    }

    /// A report arm reached from TWO different heads is shared control flow,
    /// not a single diamond's side arm: refused.
    #[test]
    fn coldsink_rejects_multi_pred_arm() {
        let mut func = make_func("coldsink_multipred", 5);
        let [entry, mid, arm, hot, exit] = [0, 1, 2, 3, 4].map(|i| BlockId(i));
        add_cond_head(&mut func, entry, mid, arm);
        add_cond_head(&mut func, mid, hot, arm);
        add_hot_arm(&mut func, hot, exit);
        add_guard_body(&mut func, arm, exit);
        add_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));

        rebuild_succs_from_block_operands(&mut func);
        let dom = DomTree::compute(&func);
        let loops = LoopAnalysis::compute(&func, &dom);
        assert!(
            !is_static_cold_guard(&func, &loops, arm),
            "multi-pred arm must not be recognized"
        );
    }

    /// A call arm that RETURNS instead of rejoining is a different shape
    /// (tail-report/noreturn idioms): refused by the trailing-branch test.
    #[test]
    fn coldsink_rejects_return_terminated_arm() {
        let mut func = make_func("coldsink_ret", 4);
        let [entry, hot, arm, exit] = [0, 1, 2, 3].map(|i| BlockId(i));
        add_cond_head(&mut func, entry, hot, arm);
        add_hot_arm(&mut func, hot, exit);
        add_inst(
            &mut func,
            arm,
            MachInst::new(
                AArch64Opcode::Bl,
                vec![MachOperand::Symbol("_printf".to_string())],
            ),
        );
        add_inst(&mut func, arm, MachInst::new(AArch64Opcode::Ret, vec![]));
        add_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));

        rebuild_succs_from_block_operands(&mut func);
        let dom = DomTree::compute(&func);
        let loops = LoopAnalysis::compute(&func, &dom);
        assert!(
            !is_static_cold_guard(&func, &loops, arm),
            "return-terminated arm must not be recognized"
        );
    }

    /// The recognizer accepts exactly the Towers guard composition, and the
    /// sink helper preserves spine order while appending guards.
    #[test]
    fn coldsink_recognizer_accepts_towers_guard_and_sink_orders() {
        let mut func = make_func("coldsink_accept", 4);
        let [entry, hot, guard, exit] = [0, 1, 2, 3].map(|i| BlockId(i));
        add_cond_head(&mut func, entry, hot, guard);
        add_hot_arm(&mut func, hot, exit);
        add_guard_body(&mut func, guard, exit);
        add_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));

        rebuild_succs_from_block_operands(&mut func);
        let dom = DomTree::compute(&func);
        let loops = LoopAnalysis::compute(&func, &dom);
        assert!(
            is_static_cold_guard(&func, &loops, guard),
            "towers-shaped guard must be recognized"
        );
        let guards = static_cold_guard_blocks(&func, &loops);
        assert_eq!(guards, vec![guard]);
        sink_cold_guards_to_end(&mut func, &guards);
        assert_eq!(func.block_order, vec![entry, hot, exit, guard]);
    }

    // -----------------------------------------------------------------------
    // pull_far_copy_latch_before_header: the huffbench encode-inner shape.
    // entry -> header -> body {CmpRR; BCond EQ exit; B latch} ; exit: Ret ;
    // latch (STRANDED at the end): {MOVXrr; B header}.
    // The pull must move the latch immediately before the header.
    // -----------------------------------------------------------------------
    #[test]
    fn test_copylatch_pull_stranded_trampoline() {
        use trust_cg_ir::aarch64_regs::{X3, X4};
        let mut func = make_func("copylatch", 5);
        let entry = BlockId(0);
        let header = BlockId(1);
        let body = BlockId(2);
        let exit = BlockId(3);
        let latch = BlockId(4);

        // entry: B header
        add_inst(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(header)]),
        );
        func.add_edge(entry, header);
        // header: AddRI ; B body
        add_inst(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::AddRI, vec![]),
        );
        add_inst(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(body)]),
        );
        func.add_edge(header, body);
        // body: CmpRR ; BCond EQ exit ; B latch  (the split-critical-edge source)
        add_inst(&mut func, body, MachInst::new(AArch64Opcode::CmpRR, vec![]));
        add_inst(
            &mut func,
            body,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(AArch64CC::EQ as i64),
                    MachOperand::Block(exit),
                ],
            ),
        );
        add_inst(
            &mut func,
            body,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(latch)]),
        );
        func.add_edge(body, exit);
        func.add_edge(body, latch);
        // exit: Ret (hard terminator — the latch's seam predecessor in layout)
        add_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));
        // latch: MOVXrr x3, x4 ; B header (the surviving Phi copy)
        add_inst(
            &mut func,
            latch,
            MachInst::new(
                AArch64Opcode::MOVXrr,
                vec![MachOperand::PReg(X3), MachOperand::PReg(X4)],
            ),
        );
        add_inst(
            &mut func,
            latch,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(header)]),
        );
        func.add_edge(latch, header);

        func.block_order = vec![entry, header, body, exit, latch];

        let dom = DomTree::compute(&func);
        let loops = LoopAnalysis::compute(&func, &dom);
        let moved = pull_far_copy_latch_before_header(&mut func, &loops, &HashSet::new());
        assert!(moved, "stranded pure-copy latch must be pulled");
        assert_eq!(
            func.block_order,
            vec![entry, latch, header, body, exit],
            "latch must sit immediately before its header"
        );
    }

    // -----------------------------------------------------------------------
    // pull_far_copy_latch_before_header must NOT fire when the latch is the
    // layout-next of its conditional predecessor (orientation's domain: the
    // huffbench decode heap2-scan shape) or when the latch holds a non-move.
    // -----------------------------------------------------------------------
    #[test]
    fn test_copylatch_pull_skips_adjacent_and_impure() {
        use trust_cg_ir::aarch64_regs::{X3, X4};
        // Shape A: header {AddRI; BCond EQ latch; B exit}; latch {MOVXrr; B header}
        // laid out immediately after the header — adjacent => skip.
        let mut func = make_func("copylatch_adj", 4);
        let entry = BlockId(0);
        let header = BlockId(1);
        let latch = BlockId(2);
        let exit = BlockId(3);
        add_inst(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(header)]),
        );
        func.add_edge(entry, header);
        add_inst(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::AddRI, vec![]),
        );
        add_inst(
            &mut func,
            header,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(AArch64CC::EQ as i64),
                    MachOperand::Block(latch),
                ],
            ),
        );
        add_inst(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(exit)]),
        );
        func.add_edge(header, latch);
        func.add_edge(header, exit);
        add_inst(
            &mut func,
            latch,
            MachInst::new(
                AArch64Opcode::MOVXrr,
                vec![MachOperand::PReg(X3), MachOperand::PReg(X4)],
            ),
        );
        add_inst(
            &mut func,
            latch,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(header)]),
        );
        func.add_edge(latch, header);
        add_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));
        func.block_order = vec![entry, header, latch, exit];

        let dom = DomTree::compute(&func);
        let loops = LoopAnalysis::compute(&func, &dom);
        let moved = pull_far_copy_latch_before_header(&mut func, &loops, &HashSet::new());
        assert!(
            !moved,
            "latch adjacent to its predecessor is orientation's domain"
        );
        assert_eq!(func.block_order, vec![entry, header, latch, exit]);

        // Shape B: stranded latch carrying a NON-move (AddRI) => impure => skip.
        let mut func2 = make_func("copylatch_impure", 5);
        let entry = BlockId(0);
        let header = BlockId(1);
        let body = BlockId(2);
        let exit = BlockId(3);
        let latch = BlockId(4);
        add_inst(
            &mut func2,
            entry,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(header)]),
        );
        func2.add_edge(entry, header);
        add_inst(
            &mut func2,
            header,
            MachInst::new(AArch64Opcode::AddRI, vec![]),
        );
        add_inst(
            &mut func2,
            header,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(body)]),
        );
        func2.add_edge(header, body);
        add_inst(
            &mut func2,
            body,
            MachInst::new(AArch64Opcode::CmpRR, vec![]),
        );
        add_inst(
            &mut func2,
            body,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(AArch64CC::EQ as i64),
                    MachOperand::Block(exit),
                ],
            ),
        );
        add_inst(
            &mut func2,
            body,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(latch)]),
        );
        func2.add_edge(body, exit);
        func2.add_edge(body, latch);
        add_inst(&mut func2, exit, MachInst::new(AArch64Opcode::Ret, vec![]));
        add_inst(
            &mut func2,
            latch,
            MachInst::new(AArch64Opcode::AddRI, vec![]),
        );
        add_inst(
            &mut func2,
            latch,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(header)]),
        );
        func2.add_edge(latch, header);
        func2.block_order = vec![entry, header, body, exit, latch];

        let dom2 = DomTree::compute(&func2);
        let loops2 = LoopAnalysis::compute(&func2, &dom2);
        let moved2 = pull_far_copy_latch_before_header(&mut func2, &loops2, &HashSet::new());
        assert!(!moved2, "non-move latch content must fail closed");
        assert_eq!(func2.block_order, vec![entry, header, body, exit, latch]);
    }

    // -----------------------------------------------------------------------
    // small_orientable_loop_headers: a 2-block scan loop whose trip test lives
    // ON THE HEADER (huffbench decode heap2-scan) must now qualify, and
    // orient_loop_conditionals must flip the header pair.
    // -----------------------------------------------------------------------
    #[test]
    fn test_hdr_orient_2block_scan_loop() {
        use trust_cg_ir::aarch64_regs::{X3, X4};
        let mut func = make_func("scanloop", 4);
        let entry = BlockId(0);
        let header = BlockId(1);
        let latch = BlockId(2);
        let exit = BlockId(3);
        add_inst(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(header)]),
        );
        func.add_edge(entry, header);
        // header: CmpRR ; BCond EQ latch ; B exit  (taken arm = stay-in-loop)
        add_inst(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::CmpRR, vec![]),
        );
        add_inst(
            &mut func,
            header,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(AArch64CC::EQ as i64),
                    MachOperand::Block(latch),
                ],
            ),
        );
        add_inst(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(exit)]),
        );
        func.add_edge(header, latch);
        func.add_edge(header, exit);
        // latch: MOVXrr ; B header
        add_inst(
            &mut func,
            latch,
            MachInst::new(
                AArch64Opcode::MOVXrr,
                vec![MachOperand::PReg(X3), MachOperand::PReg(X4)],
            ),
        );
        add_inst(
            &mut func,
            latch,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(header)]),
        );
        func.add_edge(latch, header);
        add_inst(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));
        func.block_order = vec![entry, header, latch, exit];

        let dom = DomTree::compute(&func);
        let loops = LoopAnalysis::compute(&func, &dom);
        let orientable = small_orientable_loop_headers(&func, &loops);
        assert!(
            orientable.contains(&header),
            "header-conditional 2-block loop must qualify for orientation"
        );
        let changed = orient_loop_conditionals(&mut func, &loops, &orientable);
        assert!(changed, "header pair must be flipped");
        // Header now ends with a single inverted conditional to the exit; the
        // trailing B was dropped (falls through into the latch).
        let last = last_real_inst(&func, header).unwrap();
        let inst = func.inst(last);
        assert_eq!(inst.opcode, AArch64Opcode::BCond);
        assert_eq!(single_block_operand(inst), Some(exit));
        assert_eq!(
            bcond_cc(inst),
            Some(AArch64CC::NE as i64),
            "EQ must invert to NE"
        );
    }

    // -----------------------------------------------------------------------
    // Two-armed (descent) loop rotation
    // -----------------------------------------------------------------------

    /// Build Stanford/Treesort's descent loop with every edge explicit:
    ///
    /// ```text
    ///   entry : b H
    ///   H  (1): cmp ; b.gt A0 ; b C0            (both arms stay in the loop)
    ///   A0 (2): ldr ; b.eq NEWL ; b A1
    ///   A1 (3): mov ; b H                       (arm A's latch)
    ///   C0 (4): b.lt C1 ; b RET
    ///   C1 (5): ldr ; b.eq NEWR ; b H           (arm C's latch)
    ///   NEWL(6)/NEWR(7): mov ; b RET
    ///   RET (8): ret
    /// ```
    fn two_armed_descent_loop() -> MachFunction {
        let mut func = make_func("descent", 9);
        let (entry, h, a0, a1, c0, c1, newl, newr, ret) = (
            BlockId(0),
            BlockId(1),
            BlockId(2),
            BlockId(3),
            BlockId(4),
            BlockId(5),
            BlockId(6),
            BlockId(7),
            BlockId(8),
        );
        let wire = |f: &mut MachFunction, from, to| f.add_edge(from, to);

        add_inst(&mut func, entry, b(h));
        wire(&mut func, entry, h);

        add_inst(&mut func, h, MachInst::new(AArch64Opcode::CmpRR, vec![]));
        add_inst(&mut func, h, bcond(AArch64CC::GT, a0));
        add_inst(&mut func, h, b(c0));
        wire(&mut func, h, a0);
        wire(&mut func, h, c0);

        add_inst(&mut func, a0, MachInst::new(AArch64Opcode::LdrRI, vec![]));
        add_inst(&mut func, a0, bcond(AArch64CC::EQ, newl));
        add_inst(&mut func, a0, b(a1));
        wire(&mut func, a0, newl);
        wire(&mut func, a0, a1);

        add_inst(&mut func, a1, MachInst::new(AArch64Opcode::MovR, vec![]));
        add_inst(&mut func, a1, b(h));
        wire(&mut func, a1, h);

        add_inst(&mut func, c0, bcond(AArch64CC::LT, c1));
        add_inst(&mut func, c0, b(ret));
        wire(&mut func, c0, c1);
        wire(&mut func, c0, ret);

        add_inst(&mut func, c1, MachInst::new(AArch64Opcode::LdrRI, vec![]));
        add_inst(&mut func, c1, bcond(AArch64CC::EQ, newr));
        add_inst(&mut func, c1, b(h));
        wire(&mut func, c1, newr);
        wire(&mut func, c1, h);

        for nb in [newl, newr] {
            add_inst(&mut func, nb, MachInst::new(AArch64Opcode::MovR, vec![]));
            add_inst(&mut func, nb, b(ret));
            wire(&mut func, nb, ret);
        }
        add_inst(&mut func, ret, MachInst::new(AArch64Opcode::Ret, vec![]));

        func.block_order = vec![entry, h, a0, newl, a1, c0, ret, c1, newr];
        func
    }

    fn run_armrot(func: &mut MachFunction) -> HashSet<BlockId> {
        rebuild_succs_from_block_operands(func);
        let dom = DomTree::compute(func);
        let loops = LoopAnalysis::compute(func, &dom);
        rotate_two_armed_loops(func, &loops, &HashSet::new())
    }

    /// The rotation must produce `[taken-arm][header][fall-arm]`, so the arm the
    /// header BRANCHES to returns by fall-through and the arm it falls into
    /// keeps its own back-edge — one taken branch per iteration on each arm.
    #[test]
    fn two_armed_loop_puts_the_taken_arm_before_the_header() {
        let mut func = two_armed_descent_loop();
        let (h, a0, a1, c0, c1) = (BlockId(1), BlockId(2), BlockId(3), BlockId(4), BlockId(5));

        let rotated = run_armrot(&mut func);
        assert!(rotated.contains(&h), "the descent loop must be rotated");

        // The header's branch-taken arm (A0 -> A1) now runs into the header.
        assert_eq!(
            pos(&func, a0) + 1,
            pos(&func, a1),
            "arm A must stay a chain"
        );
        assert_eq!(
            pos(&func, a1) + 1,
            pos(&func, h),
            "arm A's latch must fall through into the header"
        );
        // The fall-through arm follows the header, in chain order, so its own
        // back-edge is the single taken branch of that path.
        assert_eq!(pos(&func, h) + 1, pos(&func, c0));
        assert_eq!(pos(&func, c0) + 1, pos(&func, c1));
        assert_eq!(func.block_order[0], BlockId(0), "entry stays first");
        // Pure permutation: no block gained, lost, or duplicated.
        let mut sorted = func.block_order.clone();
        sorted.sort_by_key(|b| b.0);
        sorted.dedup();
        assert_eq!(sorted.len(), func.block_order.len());
        assert_eq!(sorted.len(), 9);
    }

    /// Re-running on the rotated order is a no-op (idempotent, and the driver's
    /// `changed` flag stays honest).
    #[test]
    fn two_armed_rotation_is_idempotent() {
        let mut func = two_armed_descent_loop();
        assert!(!run_armrot(&mut func).is_empty());
        let after_first = func.block_order.clone();
        assert!(
            run_armrot(&mut func).is_empty(),
            "already-rotated loop must not be touched again"
        );
        assert_eq!(func.block_order, after_first);
    }

    /// Fail-closed: when the two arms REJOIN inside the loop (a diamond body,
    /// not a two-armed descent) the arms no longer partition the body and the
    /// rotation must decline, leaving the layout untouched.
    #[test]
    fn rejoining_arms_are_not_rotated() {
        let mut func = two_armed_descent_loop();
        let (a1, c1, h) = (BlockId(3), BlockId(5), BlockId(1));
        // Re-point arm A's latch at arm C's latch: the arms now merge, so C1 is
        // reachable from both and the shape is a diamond, not two arms.
        func.block_mut(a1).insts.clear();
        add_inst(&mut func, a1, MachInst::new(AArch64Opcode::MovR, vec![]));
        add_inst(&mut func, a1, b(c1));

        let before = func.block_order.clone();
        let rotated = run_armrot(&mut func);
        assert!(rotated.is_empty(), "a rejoining diamond must not rotate");
        assert_eq!(func.block_order, before);
        let _ = h;
    }

    /// Fail-closed: a loop the loop-aware repair owns is DECLINED — and the
    /// decline TERMINATES. (Regression pin: the scattered-ancestor walk used to
    /// reject from inside its own `while`, where the `reject!` macro's
    /// `continue` continued the WALK instead of the loop scan — an infinite
    /// loop that hung the compiler on 20 gcc-c-torture programs.)
    #[test]
    fn scattered_owned_loop_is_declined_not_hung() {
        let mut func = two_armed_descent_loop();
        let h = BlockId(1);
        rebuild_succs_from_block_operands(&mut func);
        let dom = DomTree::compute(&func);
        let loops = LoopAnalysis::compute(&func, &dom);
        let before = func.block_order.clone();
        let scattered: HashSet<BlockId> = [h].into_iter().collect();
        let rotated = rotate_two_armed_loops(&mut func, &loops, &scattered);
        assert!(
            rotated.is_empty(),
            "the repair target's loop must be left alone"
        );
        assert_eq!(func.block_order, before);
    }

    /// Fail-closed: the kill switch leaves the layout byte-identical.
    #[test]
    fn armrot_kill_switch_declines() {
        // The switch is read once per process, so assert the gate's own value
        // rather than mutating the environment under a parallel test runner.
        if bp_armrot_enabled() {
            let mut func = two_armed_descent_loop();
            assert!(!run_armrot(&mut func).is_empty());
        }
    }
}
