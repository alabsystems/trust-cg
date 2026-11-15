// crates/trust-cg-eqsat/src/cfg.rs - control-flow graph, reachability and dominator tree of one body
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The block structure the reader and the elaborator need: block indices,
//! one terminator at the end of every block, reachability from the entry
//! (an unreachable block is a section 2.5 refusal), immediate dominators (the iterative Cooper-Harvey-Kennedy
//! algorithm over reverse postorder), the dominator tree with children in
//! block-declaration order (the reader walks it in preorder, section 6
//! "Order") and pre/post numbers for constant-time dominance queries.
//!
//! Successors are every edge `Inst::successor_edges` reports, normal and
//! unwind alike; predecessors keep one entry per edge, so the edge-dominance
//! query of section 4 ([`Cfg::normal_edge_dominates`]) sees parallel edges.
//! Every walk is iterative, so a long chain of blocks cannot exhaust the
//! stack.

use std::collections::BTreeMap;

use trust_ir::{BlockId, Function};

use crate::Decline;

#[derive(Debug, Clone)]
pub(crate) struct Cfg {
    /// The entry block's index.
    pub(crate) entry: usize,
    /// Block index by `BlockId`.
    index: BTreeMap<BlockId, usize>,
    /// Depth in the dominator tree (entry 0).
    pub(crate) depth: Vec<u32>,
    /// Dominator-tree children, in declaration order.
    pub(crate) children: Vec<Vec<usize>>,
    /// Per block, the source block of every incoming edge (one entry per
    /// edge, in body order of the sources' terminators).
    preds: Vec<Vec<usize>>,
    pre: Vec<u32>,
    post: Vec<u32>,
}

impl Cfg {
    pub(crate) fn build(function: &Function) -> Result<Cfg, Decline> {
        let count = function.blocks.len();
        let mut index = BTreeMap::new();
        for (position, block) in function.blocks.iter().enumerate() {
            if index.insert(block.id, position).is_some() {
                return Err(Decline::Unsupported(format!(
                    "block id {} is declared twice",
                    block.id.0
                )));
            }
        }
        let Some(&entry) = index.get(&function.entry) else {
            return Err(Decline::Unsupported(format!(
                "entry block {} is not declared",
                function.entry.0
            )));
        };
        let mut succs: Vec<Vec<usize>> = vec![Vec::new(); count];
        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); count];
        for (position, block) in function.blocks.iter().enumerate() {
            // Section 2.5: every block ends with its one terminator.
            let last = block.body.len().checked_sub(1);
            for (index, node) in block.body.iter().enumerate() {
                if node.inst.is_terminator() != (Some(index) == last) {
                    return Err(Decline::Unsupported(format!(
                        "block {} does not have exactly one terminator, at its end",
                        block.id.0
                    )));
                }
            }
            if last.is_none() {
                return Err(Decline::Unsupported(format!(
                    "block {} is empty (it has no terminator)",
                    block.id.0
                )));
            }
            for node in &block.body {
                for edge in node.inst.successor_edges() {
                    let Some(&target) = index.get(&edge.target) else {
                        return Err(Decline::Unsupported(format!(
                            "an edge to undeclared block {}",
                            edge.target.0
                        )));
                    };
                    if let Some(list) = succs.get_mut(position) {
                        list.push(target);
                    }
                    if let Some(list) = preds.get_mut(target) {
                        list.push(position);
                    }
                }
            }
        }

        // Reachability and postorder (iterative DFS).
        let mut visited = vec![false; count];
        let mut postorder = Vec::with_capacity(count);
        let mut stack: Vec<(usize, usize)> = vec![(entry, 0)];
        if let Some(slot) = visited.get_mut(entry) {
            *slot = true;
        }
        while let Some((block, next)) = stack.pop() {
            let list = succs.get(block).map_or(&[][..], Vec::as_slice);
            if let Some(&target) = list.get(next) {
                stack.push((block, next + 1));
                if let Some(seen) = visited.get_mut(target)
                    && !*seen
                {
                    *seen = true;
                    stack.push((target, 0));
                }
            } else {
                postorder.push(block);
            }
        }
        if visited.iter().any(|seen| !seen) {
            return Err(Decline::UnreachableBlock);
        }
        let mut po_number = vec![0usize; count];
        for (number, block) in postorder.iter().enumerate() {
            if let Some(slot) = po_number.get_mut(*block) {
                *slot = number;
            }
        }

        // Immediate dominators (Cooper, Harvey, Kennedy).
        let mut idom: Vec<Option<usize>> = vec![None; count];
        if let Some(slot) = idom.get_mut(entry) {
            *slot = Some(entry);
        }
        let po = |block: usize| po_number.get(block).copied().unwrap_or(0);
        let mut changed = true;
        while changed {
            changed = false;
            for &block in postorder.iter().rev() {
                if block == entry {
                    continue;
                }
                let mut new_idom: Option<usize> = None;
                for &pred in preds.get(block).map_or(&[][..], Vec::as_slice) {
                    if idom.get(pred).copied().flatten().is_none() {
                        continue;
                    }
                    new_idom = Some(match new_idom {
                        None => pred,
                        Some(current) => {
                            let (mut a, mut b) = (pred, current);
                            while a != b {
                                while po(a) < po(b) {
                                    a = idom.get(a).copied().flatten().unwrap_or(entry);
                                }
                                while po(b) < po(a) {
                                    b = idom.get(b).copied().flatten().unwrap_or(entry);
                                }
                            }
                            a
                        }
                    });
                }
                if new_idom.is_some() && idom.get(block).copied().flatten() != new_idom {
                    if let Some(slot) = idom.get_mut(block) {
                        *slot = new_idom;
                    }
                    changed = true;
                }
            }
        }

        let mut children: Vec<Vec<usize>> = vec![Vec::new(); count];
        for block in 0..count {
            if block == entry {
                continue;
            }
            let Some(parent) = idom.get(block).copied().flatten() else {
                return Err(Decline::Unsupported(
                    "a reachable block without an immediate dominator".to_owned(),
                ));
            };
            if let Some(list) = children.get_mut(parent) {
                list.push(block);
            }
        }

        // Preorder, depth and pre/post numbers of the dominator tree.
        let mut depth = vec![0u32; count];
        let mut pre = vec![0u32; count];
        let mut post = vec![0u32; count];
        let mut clock = 0u32;
        let mut walk: Vec<(usize, usize)> = vec![(entry, 0)];
        if let Some(slot) = pre.get_mut(entry) {
            *slot = clock;
        }
        clock += 1;
        while let Some((block, next)) = walk.pop() {
            let kids = children.get(block).map_or(&[][..], Vec::as_slice);
            if let Some(&child) = kids.get(next) {
                walk.push((block, next + 1));
                let parent_depth = depth.get(block).copied().unwrap_or(0);
                if let Some(slot) = depth.get_mut(child) {
                    *slot = parent_depth + 1;
                }
                if let Some(slot) = pre.get_mut(child) {
                    *slot = clock;
                }
                clock += 1;
                walk.push((child, 0));
            } else {
                if let Some(slot) = post.get_mut(block) {
                    *slot = clock;
                }
                clock += 1;
            }
        }

        Ok(Cfg {
            entry,
            index,
            depth,
            children,
            preds,
            pre,
            post,
        })
    }

    /// Whether block `a` dominates block `b` (reflexive).
    pub(crate) fn dominates(&self, a: usize, b: usize) -> bool {
        match (
            self.pre.get(a),
            self.pre.get(b),
            self.post.get(a),
            self.post.get(b),
        ) {
            (Some(pa), Some(pb), Some(qa), Some(qb)) => pa <= pb && qb <= qa,
            _ => false,
        }
    }

    /// The index of the block `id`.
    pub(crate) fn block_index(&self, id: BlockId) -> Option<usize> {
        self.index.get(&id).copied()
    }

    /// Whether one edge `source -> target` dominates `target` (section 4,
    /// the normal-edge rule for terminator results): `target` is not the
    /// entry block, the edge exists, and every other incoming edge of
    /// `target` (a second edge from `source` included) comes from a block
    /// `target` dominates. Then every path from the entry to `target` enters
    /// it through that edge.
    pub(crate) fn normal_edge_dominates(&self, source: usize, target: usize) -> bool {
        if target == self.entry {
            return false;
        }
        let Some(incoming) = self.preds.get(target) else {
            return false;
        };
        let mut found = false;
        for &pred in incoming {
            if pred == source && !found {
                found = true;
            } else if !self.dominates(target, pred) {
                return false;
            }
        }
        found
    }

    pub(crate) fn depth(&self, block: usize) -> u32 {
        self.depth.get(block).copied().unwrap_or(0)
    }
}
