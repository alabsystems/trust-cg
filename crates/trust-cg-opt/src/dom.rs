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
//! 4. Compute dominance frontiers from the tree (for future SSA passes).
//!
//! # Complexity
//!
//! Almost linear in practice (O(N * alpha(N)) for structured programs).
//!
//! Reference: LLVM `llvm/include/llvm/Support/GenericDomTree.h`

use std::collections::{HashMap, HashSet};

/// Cumulative DomTree::compute cost (TCG_TIME_DOM=1).
pub static DOM_NANOS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static DOM_CALLS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

use trust_cg_ir::{BlockId, MachFunction};

/// Dominator tree for a machine function.
///
/// Provides O(1) immediate-dominator queries and O(depth) dominance
/// checks. Also computes dominance frontiers for SSA construction.
#[derive(Debug, Clone)]
pub struct DomTree {
    /// Immediate dominator for each block. Entry block maps to itself.
    idom: HashMap<BlockId, BlockId>,
    /// Children in the dominator tree (block -> dominated children).
    children: HashMap<BlockId, Vec<BlockId>>,
    /// Dominance frontiers: DF(b) = set of blocks where b's dominance ends.
    dom_frontier: HashMap<BlockId, HashSet<BlockId>>,
    /// Reverse postorder numbering (block -> RPO index). Lower = earlier.
    rpo_number: HashMap<BlockId, u32>,
    /// Reverse postorder sequence of blocks.
    rpo_order: Vec<BlockId>,
    /// Euler-tour entry/exit stamps over the dominator tree, giving O(1)
    /// dominance queries. `a` dominates `b` iff `b`'s interval is nested inside
    /// `a`'s: `tin[a] <= tin[b] && tout[b] <= tout[a]`.
    ///
    /// Blocks unreachable from entry get no stamp and are absent, which keeps
    /// the fail-closed behaviour of the previous chain walk (an unstamped block
    /// dominates nothing and is dominated by nothing but itself).
    tin: HashMap<BlockId, u32>,
    tout: HashMap<BlockId, u32>,
}

impl DomTree {
    /// Compute the dominator tree for a machine function.
    pub fn compute(func: &MachFunction) -> Self {
        // DIAGNOSTIC (default off, TCG_TIME_DOM=1): cumulative cost + calls.
        if std::env::var_os("TCG_TIME_DOM").is_some() {
            let t = std::time::Instant::now();
            let r = Self::compute_inner(func);
            DOM_NANOS.fetch_add(
                t.elapsed().as_nanos() as u64,
                std::sync::atomic::Ordering::Relaxed,
            );
            let c = DOM_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
            if c % 500 == 0 {
                eprintln!(
                    "TCG_TIME_DOM cum={}us calls={}",
                    DOM_NANOS.load(std::sync::atomic::Ordering::Relaxed) / 1000,
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
        let mut rpo_number: HashMap<BlockId, u32> = HashMap::new();
        for (i, &block) in rpo_order.iter().enumerate() {
            rpo_number.insert(block, i as u32);
        }

        // Step 2: Initialize idom. Entry dominates itself.
        let mut idom: HashMap<BlockId, BlockId> = HashMap::new();
        idom.insert(entry, entry);

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
                    if idom.contains_key(&pred) {
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
                    if idom.contains_key(&pred) {
                        new_idom_val = intersect(pred, new_idom_val, &idom, &rpo_number);
                    }
                }

                if idom.get(&block) != Some(&new_idom_val) {
                    idom.insert(block, new_idom_val);
                    changed = true;
                }
            }
        }

        // Step 4: Build children map from idom.
        let mut children: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
        for (&block, &dom) in &idom {
            if block != dom {
                children.entry(dom).or_default().push(block);
            }
        }
        // Sort children by RPO order for deterministic traversal.
        for kids in children.values_mut() {
            kids.sort_by_key(|b| rpo_number.get(b).copied().unwrap_or(u32::MAX));
        }

        // Step 5: Compute dominance frontiers.
        let dom_frontier = compute_dominance_frontiers(&idom, func, &rpo_order);

        // Step 6: Euler-tour stamps over the dominator tree.
        //
        // `dominates` was an idom-CHAIN WALK: O(tree depth) with a SipHash
        // lookup per level. CSE calls it once per candidate instruction, and on
        // block-dense code the tree is deep (an if/else ladder gives a chain),
        // so the pass was O(depth x instructions) — the measured quadratic in
        // the `branchy` shape. An ancestor test over a tree is exactly an
        // interval-containment test, so one DFS makes every later query O(1).
        //
        // Iterative DFS: recursion would blow the stack on the 1202-block
        // functions this is meant to speed up.
        let (tin, tout) = {
            let mut tin: HashMap<BlockId, u32> = HashMap::new();
            let mut tout: HashMap<BlockId, u32> = HashMap::new();
            let mut timer: u32 = 0;
            // (block, next child index to visit)
            let mut stack: Vec<(BlockId, usize)> = Vec::new();
            tin.insert(entry, timer);
            timer += 1;
            stack.push((entry, 0));
            while let Some(&mut (block, ref mut next)) = stack.last_mut() {
                let kids = children.get(&block);
                let kid = kids.and_then(|k| k.get(*next)).copied();
                match kid {
                    Some(child) => {
                        *next += 1;
                        // A malformed tree could in principle revisit a node;
                        // stamping only once keeps the intervals well-formed.
                        if !tin.contains_key(&child) {
                            tin.insert(child, timer);
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
            (tin, tout)
        };

        Self {
            idom,
            children,
            dom_frontier,
            rpo_number,
            rpo_order,
            tin,
            tout,
        }
    }

    /// Returns the immediate dominator of `block`.
    /// The entry block's idom is itself.
    pub fn idom(&self, block: BlockId) -> Option<BlockId> {
        self.idom.get(&block).copied()
    }

    /// Returns true if `a` dominates `b`.
    ///
    /// Every block dominates itself. O(1): an ancestor test on the dominator
    /// tree is an interval-containment test on the Euler-tour stamps computed
    /// in [`DomTree::compute`]. This replaced an O(depth) idom chain walk that
    /// made CSE quadratic on block-dense functions.
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
        let (Some(&a_in), Some(&a_out)) = (self.tin.get(&a), self.tout.get(&a)) else {
            return false;
        };
        let (Some(&b_in), Some(&b_out)) = (self.tin.get(&b), self.tout.get(&b)) else {
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
        self.children.get(&block).map_or(&[], |v| v.as_slice())
    }

    /// Returns the dominance frontier of `block`.
    pub fn dominance_frontier(&self, block: BlockId) -> Option<&HashSet<BlockId>> {
        self.dom_frontier.get(&block)
    }

    /// Returns the reverse postorder of blocks.
    pub fn rpo_order(&self) -> &[BlockId] {
        &self.rpo_order
    }

    /// Returns the RPO number for a block (lower = earlier in RPO).
    pub fn rpo_number(&self, block: BlockId) -> Option<u32> {
        self.rpo_number.get(&block).copied()
    }
}

/// Intersect operation from Cooper/Harvey/Kennedy.
///
/// Walks two fingers up the idom tree until they meet. Uses RPO numbers
/// for comparison — higher RPO number means later in the ordering.
fn intersect(
    mut b1: BlockId,
    mut b2: BlockId,
    idom: &HashMap<BlockId, BlockId>,
    rpo_number: &HashMap<BlockId, u32>,
) -> BlockId {
    while b1 != b2 {
        let n1 = rpo_number.get(&b1).copied().unwrap_or(u32::MAX);
        let n2 = rpo_number.get(&b2).copied().unwrap_or(u32::MAX);
        if n1 > n2 {
            b1 = idom[&b1];
        } else {
            b2 = idom[&b2];
        }
    }
    b1
}

/// Compute reverse postorder via iterative DFS from entry.
fn compute_rpo(func: &MachFunction, entry: BlockId) -> Vec<BlockId> {
    let mut visited: HashSet<BlockId> = HashSet::new();
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
}

/// Compute dominance frontiers using the standard algorithm.
///
/// For each join point (block with >= 2 predecessors), walk up the idom
/// tree from each predecessor until we reach the block's immediate dominator.
/// All blocks on those walks (excluding the idom) have the join point in
/// their dominance frontier.
fn compute_dominance_frontiers(
    idom: &HashMap<BlockId, BlockId>,
    func: &MachFunction,
    rpo_order: &[BlockId],
) -> HashMap<BlockId, HashSet<BlockId>> {
    let mut df: HashMap<BlockId, HashSet<BlockId>> = HashMap::new();

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
        let df1 = dom.dominance_frontier(BlockId(1)).unwrap();
        assert!(df1.contains(&BlockId(3)));
        // DF(bb2) = {bb3}
        let df2 = dom.dominance_frontier(BlockId(2)).unwrap();
        assert!(df2.contains(&BlockId(3)));
        // DF(bb0) = {} (bb0 dominates everything)
        let df0 = dom.dominance_frontier(BlockId(0));
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
        let df3 = dom.dominance_frontier(BlockId(3)).unwrap();
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
