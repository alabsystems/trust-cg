// trust-cg-opt - Dominator tree analysis
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Dominator tree computation using the Cooper/Harvey/Kennedy algorithm.
//!
//! The dominator tree is a fundamental data structure used by CSE (to ensure
//! a dominating definition exists before eliminating a duplicate) and LICM
//! (to identify loop preheaders and safe hoisting points).
//!
//! # Algorithm
//!
//! Uses the iterative algorithm from:
//! Cooper, Harvey, Kennedy. "A Simple, Fast Dominance Algorithm." (2001)
//!
//! 1. Compute reverse postorder (RPO) numbering via DFS from entry.
//! 2. Iteratively compute immediate dominators using the "intersect" operation.
//! 3. Derive the dominator tree from idom[].
//! 4. Compute Euler-tour stamps for dominance queries. Frontiers are computed
//!    separately on demand.
//!
//! # Complexity
//!
//! Construction work depends on graph traversal and fixpoint convergence.
//! Historical benchmark timings are not a bound on arbitrary input graphs.

use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::sync::atomic::{AtomicU64, Ordering};

/// Cumulative DomTree::compute cost (TCG_TIME_DOM=1), saturating at u64::MAX.
pub static DOM_NANOS: AtomicU64 = AtomicU64::new(0);
pub static DOM_CALLS: AtomicU64 = AtomicU64::new(0);

fn add_timing_counter(counter: &AtomicU64, amount: u64) -> u64 {
    let mut previous = counter.load(Ordering::Relaxed);
    loop {
        let next = previous.saturating_add(amount);
        match counter.compare_exchange_weak(previous, next, Ordering::Relaxed, Ordering::Relaxed) {
            Ok(_) => return next,
            Err(current) => previous = current,
        }
    }
}

use trust_cg_ir::{BlockId, MachFunction};

/// Dominator tree for a machine function.
///
/// Provides immediate-dominator lookups, constant-time interval comparisons
/// for dominance, and on-demand dominance frontiers for SSA construction.
#[derive(Debug, Clone)]
pub struct DomTree {
    /// Immediate dominator of each block, indexed by `BlockId.0`. The entry
    /// block maps to itself; a block unreachable from the entry (or outside
    /// the function) has none.
    ///
    /// Every per-block table here is a dense array, not a hash map: `BlockId.0`
    /// indexes `func.blocks` throughout this backend, and the rewrite drivers
    /// rebuild this tree once per rewrite (the loop-latch-layout driver once
    /// per rotated loop), where materializing five hash maps per build was
    /// most of the cost of a build.
    idom: Vec<Option<BlockId>>,
    /// Children in the dominator tree, in RPO order, indexed by `BlockId.0`.
    children: Vec<Vec<BlockId>>,
    /// Reverse postorder number of each block (lower = earlier), indexed by
    /// `BlockId.0`; [`NO_RPO_NUMBER`] for a block not in the RPO.
    rpo_number: Vec<u32>,
    /// Reverse postorder sequence of blocks.
    rpo_order: Vec<BlockId>,
    /// Euler-tour entry/exit stamps over the dominator tree, giving O(1)
    /// dominance queries. `a` dominates `b` iff `b`'s interval is nested inside
    /// `a`'s: `tin[a] <= tin[b] && tout[b] <= tout[a]`. Indexed by `BlockId.0`.
    ///
    /// Blocks unreachable from entry get no stamp ([`NO_STAMP`]), which keeps
    /// the fail-closed behaviour of the previous chain walk (an unstamped block
    /// dominates nothing and is dominated by nothing but itself).
    // A tour has two events per node; a u32 BlockId domain therefore needs
    // more than u32 event positions. Each distinct ID is visited at most once.
    tin: Vec<u64>,
    tout: Vec<u64>,
}

/// [`DomTree::rpo_number`]'s "not in the RPO".
const NO_RPO_NUMBER: u32 = u32::MAX;
/// [`DomTree`]'s Euler-tour "no stamp".
const NO_STAMP: u64 = u64::MAX;

/// The entry of a dense per-block table, if `block` indexes one.
#[inline]
fn dense_at<T: Copy>(table: &[T], block: BlockId) -> Option<T> {
    table.get(block.0 as usize).copied()
}

/// DIAGNOSTIC gate for the `TCG_TIME_DOM` cumulative timer.
///
/// Cached once for the process to avoid repeated environment lookups. Shared
/// analysis caches can reuse a tree; explicit rewrite drivers can rebuild it.
///
/// Memoizing is sound for this gate specifically because it is PURE TIMING: it
/// selects only whether the call is wrapped in an `Instant`, never what tree is
/// returned. The semantic (behaviour-selecting) env gates elsewhere in this
/// crate are deliberately left uncached — a test that flips one in-process must
/// still see the next call observe it.
fn time_dom_enabled() -> bool {
    use std::sync::OnceLock;
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("TCG_TIME_DOM").is_some())
}

impl DomTree {
    /// Compute the dominator tree for a machine function.
    pub fn compute(func: &MachFunction) -> Self {
        // DIAGNOSTIC (default off, TCG_TIME_DOM=1): cumulative cost + calls.
        if time_dom_enabled() {
            let t = std::time::Instant::now();
            let r = Self::compute_inner(func);
            add_timing_counter(
                &DOM_NANOS,
                u64::try_from(t.elapsed().as_nanos()).unwrap_or(u64::MAX),
            );
            let c = add_timing_counter(&DOM_CALLS, 1);
            if c.is_multiple_of(500) {
                eprintln!(
                    "TCG_TIME_DOM cum={}us calls={}",
                    DOM_NANOS.load(Ordering::Relaxed) / 1000,
                    c
                );
            }
            return r;
        }
        Self::compute_inner(func)
    }

    fn compute_inner(func: &MachFunction) -> Self {
        let entry = func.entry;

        // Step 1: Compute reverse postorder via DFS.
        let rpo_order = compute_rpo(func, entry);

        // DENSE working state for the fixpoint. `BlockId.0` indexes
        // `func.blocks` everywhere in this backend, so both maps below are
        // arrays, not hash tables. The intersection walk probes both per step.
        // Map forms for public queries are materialized after convergence.
        let block_count = func.blocks.len();
        let mut rpo_num: Vec<u32> = vec![u32::MAX; block_count];
        for (i, &block) in rpo_order.iter().enumerate() {
            if let Some(slot) = rpo_num.get_mut(block.0 as usize) {
                *slot = i as u32;
            }
        }

        // Step 2: Initialize idom. Entry dominates itself.
        let mut idom_of: Vec<Option<BlockId>> = vec![None; block_count];
        if let Some(slot) = idom_of.get_mut(entry.0 as usize) {
            *slot = Some(entry);
        }

        // Step 3: Iterate until fixpoint (Cooper/Harvey/Kennedy).
        let mut changed = true;
        while changed {
            changed = false;
            for &block in &rpo_order {
                if block == entry {
                    continue;
                }

                let preds = &func.block(block).preds;
                // Find first processed predecessor (one with idom already set).
                let mut new_idom = None;
                for &pred in preds {
                    if idom_at(&idom_of, pred).is_some() {
                        new_idom = Some(pred);
                        break;
                    }
                }

                let Some(mut new_idom_val) = new_idom else {
                    // No processed predecessor yet — skip this iteration.
                    continue;
                };

                // Intersect with remaining processed predecessors.
                for &pred in preds {
                    if pred == new_idom_val {
                        continue;
                    }
                    if idom_at(&idom_of, pred).is_some() {
                        new_idom_val = intersect(pred, new_idom_val, &idom_of, &rpo_num);
                    }
                }

                if idom_at(&idom_of, block) != Some(new_idom_val) {
                    if let Some(slot) = idom_of.get_mut(block.0 as usize) {
                        *slot = Some(new_idom_val);
                    }
                    changed = true;
                }
            }
        }

        // The RPO numbers and children the tree stores. Children are pushed in
        // RPO order, which is the order the tour below visits them in.
        let mut rpo_number: Vec<u32> = vec![NO_RPO_NUMBER; block_count];
        for (i, &block) in rpo_order.iter().enumerate() {
            if let Some(slot) = rpo_number.get_mut(block.0 as usize) {
                *slot = i as u32;
            }
        }

        // Step 4: Build children from idom.
        let mut children: Vec<Vec<BlockId>> = vec![Vec::new(); block_count];
        for &block in &rpo_order {
            if let Some(dom) = idom_at(&idom_of, block)
                && block != dom
                && let Some(kids) = children.get_mut(dom.0 as usize)
            {
                kids.push(block);
            }
        }

        // Step 5: Euler-tour stamps replace repeated ancestor-chain walks with
        // interval comparisons. Iterative traversal avoids recursion depth
        // proportional to the tree; it does not make allocation failure recoverable.
        let (tin, tout) = {
            let mut tin: Vec<u64> = vec![NO_STAMP; block_count];
            let mut tout: Vec<u64> = vec![NO_STAMP; block_count];
            let mut timer: u64 = 0;
            // (block, next child index to visit)
            let mut stack: Vec<(BlockId, usize)> = Vec::new();
            if let Some(slot) = tin.get_mut(entry.0 as usize) {
                *slot = timer;
                timer += 1;
                stack.push((entry, 0));
            }
            while let Some(&mut (block, ref mut next)) = stack.last_mut() {
                let kid = children
                    .get(block.0 as usize)
                    .and_then(|k| k.get(*next))
                    .copied();
                match kid {
                    Some(child) => {
                        *next += 1;
                        // A malformed tree could in principle revisit a node;
                        // stamping only once keeps the intervals well-formed.
                        if let Some(slot) = tin.get_mut(child.0 as usize)
                            && *slot == NO_STAMP
                        {
                            *slot = timer;
                            timer += 1;
                            stack.push((child, 0));
                        }
                    }
                    None => {
                        if let Some(slot) = tout.get_mut(block.0 as usize) {
                            *slot = timer;
                        }
                        timer += 1;
                        stack.pop();
                    }
                }
            }
            (tin, tout)
        };

        Self {
            idom: idom_of,
            children,
            rpo_number,
            rpo_order,
            tin,
            tout,
        }
    }

    /// Returns the immediate dominator of `block`.
    /// The entry block's idom is itself.
    pub fn idom(&self, block: BlockId) -> Option<BlockId> {
        idom_at(&self.idom, block)
    }

    /// Returns true if `a` dominates `b`.
    ///
    /// Every block dominates itself. O(1): an ancestor test on the dominator
    /// tree is an interval-containment test on the Euler-tour stamps computed
    /// in [`DomTree::compute`], rather than a repeated idom-chain walk.
    ///
    /// Identical verdicts to the chain walk. `a` dominates `b` exactly when `a`
    /// is an ancestor of `b` in the dominator tree, and the DFS visits a
    /// subtree contiguously, so `b` is a descendant of `a` iff `b`'s interval
    /// nests inside `a`'s. A block unreachable from entry has no stamp, so it
    /// neither dominates nor is dominated by anything else — which is what the
    /// chain walk returned when it ran off a missing idom entry.
    pub fn dominates(&self, a: BlockId, b: BlockId) -> bool {
        if a == b {
            return true;
        }
        let stamps = |block: BlockId| {
            let tin = dense_at(&self.tin, block).filter(|&t| t != NO_STAMP)?;
            let tout = dense_at(&self.tout, block).filter(|&t| t != NO_STAMP)?;
            Some((tin, tout))
        };
        let (Some((a_in, a_out)), Some((b_in, b_out))) = (stamps(a), stamps(b)) else {
            return false;
        };
        a_in <= b_in && b_out <= a_out
    }

    /// Returns true if `a` strictly dominates `b` (a dominates b and a != b).
    pub fn strictly_dominates(&self, a: BlockId, b: BlockId) -> bool {
        a != b && self.dominates(a, b)
    }

    /// Returns the children of `block` in the dominator tree.
    pub fn children(&self, block: BlockId) -> &[BlockId] {
        self.children
            .get(block.0 as usize)
            .map_or(&[], |v| v.as_slice())
    }

    /// Returns the dominance frontier of `block`, computed ON DEMAND.
    ///
    /// Computing here needs `func` for the predecessor lists, which the tree
    /// does not retain. Supply the same CFG snapshot used to compute the tree.
    /// It recomputes every frontier per call and returns an owned set; repeated
    /// all-block queries therefore repeat that work.
    #[must_use]
    pub fn dominance_frontier(
        &self,
        func: &MachFunction,
        block: BlockId,
    ) -> Option<HashSet<BlockId>> {
        compute_dominance_frontiers(&self.idom, func, &self.rpo_order).remove(&block)
    }

    /// Returns the reverse postorder of blocks.
    pub fn rpo_order(&self) -> &[BlockId] {
        &self.rpo_order
    }

    /// Returns the RPO number for a block (lower = earlier in RPO).
    pub fn rpo_number(&self, block: BlockId) -> Option<u32> {
        dense_at(&self.rpo_number, block).filter(|&n| n != NO_RPO_NUMBER)
    }
}

/// Immediate dominator of `block` in the dense fixpoint state, if assigned.
///
/// A block id outside the array reads as unassigned, which is the same answer
/// the previous `HashMap::contains_key` gave for an absent key.
#[inline]
fn idom_at(idom_of: &[Option<BlockId>], block: BlockId) -> Option<BlockId> {
    idom_of.get(block.0 as usize).copied().flatten()
}

/// Intersect operation from Cooper/Harvey/Kennedy.
///
/// Walks two fingers up the idom tree until they meet. Uses RPO numbers
/// for comparison — higher RPO number means later in the ordering.
fn intersect(
    mut b1: BlockId,
    mut b2: BlockId,
    idom_of: &[Option<BlockId>],
    rpo_num: &[u32],
) -> BlockId {
    // Same walk as before, over arrays instead of hash maps. The `expect`s
    // preserve the previous `idom[&b]` contract EXACTLY: indexing a `HashMap`
    // with an absent key panics, so an unassigned idom here was always a bug,
    // never a silently-tolerated case. Callers only intersect predecessors they
    // have already confirmed assigned, and the walk ascends toward the entry,
    // which is assigned first.
    let number = |b: BlockId| rpo_num.get(b.0 as usize).copied().unwrap_or(u32::MAX);
    while b1 != b2 {
        if number(b1) > number(b2) {
            b1 = idom_at(idom_of, b1).expect("intersect ascends only assigned idoms");
        } else {
            b2 = idom_at(idom_of, b2).expect("intersect ascends only assigned idoms");
        }
    }
    b1
}

/// Compute reverse postorder via iterative DFS from entry.
fn compute_rpo(func: &MachFunction, entry: BlockId) -> Vec<BlockId> {
    // Dense visited marks. An id outside `func.blocks` is never marked, so it
    // is pushed and `func.block` panics on it, as the hash set version did.
    let mut visited: Vec<bool> = vec![false; func.blocks.len()];
    let mut first_visit = |block: BlockId| match visited.get_mut(block.0 as usize) {
        Some(seen) => !std::mem::replace(seen, true),
        None => true,
    };
    let mut postorder: Vec<BlockId> = Vec::new();
    let mut stack: Vec<(BlockId, usize)> = vec![(entry, 0)];
    first_visit(entry);

    while let Some((block, next_succ_idx)) = stack.last_mut() {
        let block_id = *block;
        let succs = &func.block(block_id).succs;
        if *next_succ_idx < succs.len() {
            let succ = succs[*next_succ_idx];
            *next_succ_idx += 1;
            if first_visit(succ) {
                stack.push((succ, 0));
            }
        } else {
            postorder.push(block_id);
            stack.pop();
        }
    }

    postorder.reverse();
    postorder
}

/// Compute dominance frontiers using the standard algorithm.
///
/// For each join point (block with >= 2 predecessors), walk up the idom
/// tree from each predecessor until we reach the block's immediate dominator.
/// All blocks on those walks (excluding the idom) have the join point in
/// their dominance frontier.
fn compute_dominance_frontiers(
    idom: &[Option<BlockId>],
    func: &MachFunction,
    rpo_order: &[BlockId],
) -> HashMap<BlockId, HashSet<BlockId>> {
    let mut df: HashMap<BlockId, HashSet<BlockId>> = HashMap::default();

    for &block in rpo_order {
        let preds = &func.block(block).preds;
        if preds.len() < 2 {
            continue;
        }
        for &pred in preds {
            let mut runner = pred;
            while runner != idom_at(idom, block).unwrap_or(block) {
                df.entry(runner).or_default().insert(block);
                let next = idom_at(idom, runner).unwrap_or(runner);
                if next == runner {
                    break; // reached root
                }
                runner = next;
            }
        }
    }

    df
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, MachOperand, Signature};

    #[test]
    fn diagnostic_counters_saturate_without_wrapping_or_panicking() {
        let calls = AtomicU64::new(u64::MAX - 1);
        assert_eq!(add_timing_counter(&calls, 1), u64::MAX);
        assert_eq!(add_timing_counter(&calls, 1), u64::MAX);
        assert_eq!(calls.load(Ordering::Relaxed), u64::MAX);
        let nanos = AtomicU64::new(u64::MAX - 5);
        assert_eq!(add_timing_counter(&nanos, 10), u64::MAX);
        assert_eq!(nanos.load(Ordering::Relaxed), u64::MAX);
        let ordinary = AtomicU64::new(0);
        assert_eq!(add_timing_counter(&ordinary, 10), 10);
        assert_eq!(ordinary.load(Ordering::Relaxed), 10);
    }

    /// The hash-map DomTree this module stored before its tables became
    /// dense arrays, kept verbatim (its own RPO, fixpoint and materialization)
    /// as the oracle for `dense_tree_answers_what_the_map_tree_answered`.
    struct MapTree {
        idom: HashMap<BlockId, BlockId>,
        children: HashMap<BlockId, Vec<BlockId>>,
        rpo_number: HashMap<BlockId, u32>,
        rpo_order: Vec<BlockId>,
        tin: HashMap<BlockId, u64>,
        tout: HashMap<BlockId, u64>,
    }

    fn map_tree(func: &MachFunction) -> MapTree {
        let entry = func.entry;
        let rpo_order = {
            let mut visited: HashSet<BlockId> = HashSet::default();
            let mut postorder: Vec<BlockId> = Vec::new();
            let mut stack: Vec<(BlockId, usize)> = vec![(entry, 0)];
            visited.insert(entry);
            while let Some((block, next_succ_idx)) = stack.last_mut() {
                let block_id = *block;
                let succs = &func.block(block_id).succs;
                if *next_succ_idx < succs.len() {
                    let succ = succs[*next_succ_idx];
                    *next_succ_idx += 1;
                    if visited.insert(succ) {
                        stack.push((succ, 0));
                    }
                } else {
                    postorder.push(block_id);
                    stack.pop();
                }
            }
            postorder.reverse();
            postorder
        };
        let block_count = func.blocks.len();
        let mut rpo_num: Vec<u32> = vec![u32::MAX; block_count];
        for (i, &block) in rpo_order.iter().enumerate() {
            if let Some(slot) = rpo_num.get_mut(block.0 as usize) {
                *slot = i as u32;
            }
        }
        let mut idom_of: Vec<Option<BlockId>> = vec![None; block_count];
        if let Some(slot) = idom_of.get_mut(entry.0 as usize) {
            *slot = Some(entry);
        }
        let mut changed = true;
        while changed {
            changed = false;
            for &block in &rpo_order {
                if block == entry {
                    continue;
                }
                let preds = &func.block(block).preds;
                let mut new_idom = None;
                for &pred in preds {
                    if idom_at(&idom_of, pred).is_some() {
                        new_idom = Some(pred);
                        break;
                    }
                }
                let Some(mut new_idom_val) = new_idom else {
                    continue;
                };
                for &pred in preds {
                    if pred == new_idom_val {
                        continue;
                    }
                    if idom_at(&idom_of, pred).is_some() {
                        new_idom_val = intersect(pred, new_idom_val, &idom_of, &rpo_num);
                    }
                }
                if idom_at(&idom_of, block) != Some(new_idom_val) {
                    if let Some(slot) = idom_of.get_mut(block.0 as usize) {
                        *slot = Some(new_idom_val);
                    }
                    changed = true;
                }
            }
        }
        let mut idom: HashMap<BlockId, BlockId> = HashMap::default();
        for &block in &rpo_order {
            if let Some(d) = idom_at(&idom_of, block) {
                idom.insert(block, d);
            }
        }
        let mut rpo_number: HashMap<BlockId, u32> = HashMap::default();
        for (i, &block) in rpo_order.iter().enumerate() {
            rpo_number.insert(block, i as u32);
        }
        let mut children: HashMap<BlockId, Vec<BlockId>> = HashMap::default();
        for (&block, &dom) in &idom {
            if block != dom {
                children.entry(dom).or_default().push(block);
            }
        }
        for kids in children.values_mut() {
            kids.sort_by_key(|b| rpo_number.get(b).copied().unwrap_or(u32::MAX));
        }
        let mut tin: HashMap<BlockId, u64> = HashMap::default();
        let mut tout: HashMap<BlockId, u64> = HashMap::default();
        let mut timer: u64 = 0;
        let mut stack: Vec<(BlockId, usize)> = Vec::new();
        tin.insert(entry, timer);
        timer += 1;
        stack.push((entry, 0));
        while let Some(&mut (block, ref mut next)) = stack.last_mut() {
            let kid = children.get(&block).and_then(|k| k.get(*next)).copied();
            match kid {
                Some(child) => {
                    *next += 1;
                    if let std::collections::hash_map::Entry::Vacant(e) = tin.entry(child) {
                        e.insert(timer);
                        timer += 1;
                        stack.push((child, 0));
                    }
                }
                None => {
                    tout.insert(block, timer);
                    timer += 1;
                    stack.pop();
                }
            }
        }
        MapTree {
            idom,
            children,
            rpo_number,
            rpo_order,
            tin,
            tout,
        }
    }

    /// The map-tree dominance frontier, verbatim.
    fn map_tree_frontiers(
        idom: &HashMap<BlockId, BlockId>,
        func: &MachFunction,
        rpo_order: &[BlockId],
    ) -> HashMap<BlockId, HashSet<BlockId>> {
        let mut df: HashMap<BlockId, HashSet<BlockId>> = HashMap::default();
        for &block in rpo_order {
            let preds = &func.block(block).preds;
            if preds.len() < 2 {
                continue;
            }
            for &pred in preds {
                let mut runner = pred;
                while runner != *idom.get(&block).unwrap_or(&block) {
                    df.entry(runner).or_default().insert(block);
                    let next = idom.get(&runner).copied().unwrap_or(runner);
                    if next == runner {
                        break;
                    }
                    runner = next;
                }
            }
        }
        df
    }

    /// A deterministic CFG: a chain most of the time plus random edges (loops,
    /// self-loops, duplicate edges), a random entry, unreachable blocks.
    fn generated_cfg(seed: u64) -> MachFunction {
        let mut state = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1;
        let mut next = move |bound: u64| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state % bound
        };
        let mut func = MachFunction::new(format!("cfg{seed}"), Signature::new(vec![], vec![]));
        let n = 1 + next(30) as u32;
        for _ in 1..n {
            func.create_block();
        }
        for from in 0..n {
            if from + 1 < n && next(4) != 0 {
                func.add_edge(BlockId(from), BlockId(from + 1));
            }
            for _ in 0..next(3) {
                func.add_edge(BlockId(from), BlockId(next(u64::from(n)) as u32));
            }
        }
        if seed.is_multiple_of(5) {
            func.entry = BlockId(next(u64::from(n)) as u32);
        }
        func
    }

    /// Every query of the dense tree answers what the hash-map tree answered:
    /// idom, dominance over every ordered pair, children, RPO order and
    /// numbers, the tour stamps and every dominance frontier, on 1,500
    /// generated CFGs.
    #[test]
    fn dense_tree_answers_what_the_map_tree_answered() {
        for seed in 0..1_500u64 {
            let func = generated_cfg(seed);
            let dense = DomTree::compute(&func);
            let map = map_tree(&func);
            assert_eq!(
                dense.rpo_order(),
                map.rpo_order.as_slice(),
                "seed {seed}: rpo"
            );
            let frontiers = map_tree_frontiers(&map.idom, &func, &map.rpo_order);
            // One id past the function too: absent everywhere.
            let blocks: Vec<BlockId> = (0..=func.blocks.len() as u32).map(BlockId).collect();
            for &a in &blocks {
                assert_eq!(
                    dense.idom(a),
                    map.idom.get(&a).copied(),
                    "seed {seed}: idom {a:?}"
                );
                assert_eq!(
                    dense.rpo_number(a),
                    map.rpo_number.get(&a).copied(),
                    "seed {seed}: rpo number {a:?}"
                );
                assert_eq!(
                    dense.children(a),
                    map.children.get(&a).map_or(&[][..], |k| k.as_slice()),
                    "seed {seed}: children {a:?}"
                );
                let stamp = |table: &[u64]| dense_at(table, a).filter(|&t| t != NO_STAMP);
                assert_eq!(
                    stamp(&dense.tin),
                    map.tin.get(&a).copied(),
                    "seed {seed}: tin"
                );
                assert_eq!(
                    stamp(&dense.tout),
                    map.tout.get(&a).copied(),
                    "seed {seed}: tout"
                );
                if (a.0 as usize) < func.blocks.len() {
                    assert_eq!(
                        dense.dominance_frontier(&func, a),
                        frontiers.get(&a).cloned(),
                        "seed {seed}: frontier {a:?}"
                    );
                }
                for &b in &blocks {
                    let map_dominates = a == b
                        || match (
                            map.tin.get(&a),
                            map.tout.get(&a),
                            map.tin.get(&b),
                            map.tout.get(&b),
                        ) {
                            (Some(ai), Some(ao), Some(bi), Some(bo)) => ai <= bi && bo <= ao,
                            _ => false,
                        };
                    assert_eq!(
                        dense.dominates(a, b),
                        map_dominates,
                        "seed {seed}: dominates({a:?}, {b:?})"
                    );
                }
            }
        }
    }

    #[test]
    fn dominance_queries_preserve_stamps_above_u32() {
        let func = make_diamond();
        let mut dom = DomTree::compute(&func);
        let expected: Vec<_> = func
            .block_order
            .iter()
            .flat_map(|&a| func.block_order.iter().map(move |&b| (a, b)))
            .map(|(a, b)| (a, b, dom.dominates(a, b)))
            .collect();
        // A tour needs two events per block, more than the BlockId domain.
        for stamp in dom
            .tin
            .iter_mut()
            .chain(dom.tout.iter_mut())
            .filter(|stamp| **stamp != NO_STAMP)
        {
            *stamp = stamp
                .checked_add(u32::MAX.into())
                .expect("tour event fits stamp domain");
        }
        for (a, b, dominated) in expected {
            assert_eq!(dom.dominates(a, b), dominated);
        }
    }

    /// Build a diamond CFG:
    ///
    /// ```text
    ///     bb0 (entry)
    ///    /   \
    ///  bb1   bb2
    ///    \   /
    ///     bb3
    /// ```
    fn make_diamond() -> MachFunction {
        let mut func = MachFunction::new("diamond".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry; // bb0
        let bb1 = func.create_block(); // bb1
        let bb2 = func.create_block(); // bb2
        let bb3 = func.create_block(); // bb3

        // Add terminators
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb1), MachOperand::Block(bb2)],
        ));
        func.append_inst(bb0, br0);

        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, br1);

        let br2 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb3)],
        ));
        func.append_inst(bb2, br2);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb3, ret);

        // CFG edges
        func.add_edge(bb0, bb1);
        func.add_edge(bb0, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb3);

        func
    }

    /// Build a simple loop:
    ///
    /// ```text
    ///   bb0 (entry)
    ///    |
    ///   bb1 (header) <---+
    ///   / \               |
    /// bb2  bb3 (latch) --+
    /// ```
    fn make_loop() -> MachFunction {
        let mut func = MachFunction::new("loop".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let br1 = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, br1);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        let br3 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb3, br3);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb3, bb1);

        func
    }

    #[test]
    fn test_diamond_idom() {
        let func = make_diamond();
        let dom = DomTree::compute(&func);

        // bb0 dominates everything
        assert_eq!(dom.idom(BlockId(0)), Some(BlockId(0))); // entry self-dom
        assert_eq!(dom.idom(BlockId(1)), Some(BlockId(0)));
        assert_eq!(dom.idom(BlockId(2)), Some(BlockId(0)));
        assert_eq!(dom.idom(BlockId(3)), Some(BlockId(0)));
    }

    #[test]
    fn test_diamond_dominates() {
        let func = make_diamond();
        let dom = DomTree::compute(&func);

        assert!(dom.dominates(BlockId(0), BlockId(0)));
        assert!(dom.dominates(BlockId(0), BlockId(1)));
        assert!(dom.dominates(BlockId(0), BlockId(3)));
        // bb1 does NOT dominate bb3 (bb2 is an alternate path)
        assert!(!dom.dominates(BlockId(1), BlockId(3)));
        assert!(!dom.dominates(BlockId(2), BlockId(3)));
        // bb1 does NOT dominate bb2
        assert!(!dom.dominates(BlockId(1), BlockId(2)));
    }

    #[test]
    fn test_diamond_strictly_dominates() {
        let func = make_diamond();
        let dom = DomTree::compute(&func);

        assert!(!dom.strictly_dominates(BlockId(0), BlockId(0)));
        assert!(dom.strictly_dominates(BlockId(0), BlockId(1)));
    }

    #[test]
    fn test_diamond_dominance_frontier() {
        let func = make_diamond();
        let dom = DomTree::compute(&func);

        // DF(bb1) = {bb3} (bb1 -> bb3 is a join point)
        let df1 = dom.dominance_frontier(&func, BlockId(1)).unwrap();
        assert!(df1.contains(&BlockId(3)));
        // DF(bb2) = {bb3}
        let df2 = dom.dominance_frontier(&func, BlockId(2)).unwrap();
        assert!(df2.contains(&BlockId(3)));
        // DF(bb0) = {} (bb0 dominates everything)
        let df0 = dom.dominance_frontier(&func, BlockId(0));
        assert!(df0.is_none() || df0.unwrap().is_empty());
    }

    #[test]
    fn test_loop_idom() {
        let func = make_loop();
        let dom = DomTree::compute(&func);

        assert_eq!(dom.idom(BlockId(0)), Some(BlockId(0)));
        assert_eq!(dom.idom(BlockId(1)), Some(BlockId(0)));
        assert_eq!(dom.idom(BlockId(2)), Some(BlockId(1)));
        assert_eq!(dom.idom(BlockId(3)), Some(BlockId(1)));
    }

    #[test]
    fn test_loop_dominates() {
        let func = make_loop();
        let dom = DomTree::compute(&func);

        // bb1 (header) dominates bb2 and bb3
        assert!(dom.dominates(BlockId(1), BlockId(2)));
        assert!(dom.dominates(BlockId(1), BlockId(3)));
        // bb3 (latch) does NOT dominate bb1 (back-edge)
        assert!(!dom.dominates(BlockId(3), BlockId(1)));
    }

    #[test]
    fn test_loop_dominance_frontier() {
        let func = make_loop();
        let dom = DomTree::compute(&func);

        // DF(bb3) = {bb1} (back-edge target)
        let df3 = dom.dominance_frontier(&func, BlockId(3)).unwrap();
        assert!(df3.contains(&BlockId(1)));
    }

    #[test]
    fn test_children() {
        let func = make_diamond();
        let dom = DomTree::compute(&func);

        // bb0 dominates bb1, bb2, bb3
        let kids = dom.children(BlockId(0));
        assert!(kids.contains(&BlockId(1)));
        assert!(kids.contains(&BlockId(2)));
        assert!(kids.contains(&BlockId(3)));

        // bb1 has no children in the dominator tree
        assert!(dom.children(BlockId(1)).is_empty());
    }

    #[test]
    fn test_rpo_order() {
        let func = make_diamond();
        let dom = DomTree::compute(&func);

        let rpo = dom.rpo_order();
        // Entry should be first
        assert_eq!(rpo[0], BlockId(0));
        // bb3 should be after bb1 and bb2
        let pos1 = rpo.iter().position(|&b| b == BlockId(1)).unwrap();
        let pos2 = rpo.iter().position(|&b| b == BlockId(2)).unwrap();
        let pos3 = rpo.iter().position(|&b| b == BlockId(3)).unwrap();
        assert!(pos3 > pos1);
        assert!(pos3 > pos2);
    }

    #[test]
    fn test_single_block() {
        let func = MachFunction::new("single".to_string(), Signature::new(vec![], vec![]));
        let dom = DomTree::compute(&func);

        assert_eq!(dom.idom(BlockId(0)), Some(BlockId(0)));
        assert!(dom.dominates(BlockId(0), BlockId(0)));
        assert!(dom.children(BlockId(0)).is_empty());
    }
}
