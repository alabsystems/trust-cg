// trust-cg-eqsat-check/src/dom.rs - the checker's own reachability and dominator tree
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Reachability, reverse postorder and dominators over a CFG given as
//! successor lists of block indices.
//!
//! The immediate dominators come from the iterative intersection algorithm
//! over reverse postorder (Cooper, Harvey and Kennedy, "A Simple, Fast
//! Dominance Algorithm"); dominance queries use pre/post numbers of the
//! dominator tree. Nothing here depends on trust-ir's own analyses.
//!
//! Precondition: `succs[i]` holds only indices `< succs.len()`, and `entry <
//! succs.len()`. Unreachable blocks get no dominator and dominate nothing.

pub(crate) struct DomTree {
    /// Reachable blocks in reverse postorder from the entry.
    pub(crate) rpo: Vec<usize>,
    reachable: Vec<bool>,
    pre: Vec<usize>,
    post: Vec<usize>,
}

impl DomTree {
    pub(crate) fn compute(succs: &[Vec<usize>], entry: usize) -> DomTree {
        let n = succs.len();
        // Iterative DFS postorder.
        let mut visited = vec![false; n];
        let mut postorder = Vec::with_capacity(n);
        let mut stack: Vec<(usize, usize)> = Vec::new();
        if entry < n {
            visited[entry] = true;
            stack.push((entry, 0));
        }
        while let Some((b, next)) = stack.pop() {
            if let Some(&s) = succs[b].get(next) {
                stack.push((b, next + 1));
                if s < n && !visited[s] {
                    visited[s] = true;
                    stack.push((s, 0));
                }
            } else {
                postorder.push(b);
            }
        }
        let mut po_num = vec![usize::MAX; n];
        for (i, &b) in postorder.iter().enumerate() {
            po_num[b] = i;
        }
        let rpo: Vec<usize> = postorder.iter().rev().copied().collect();

        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (b, ss) in succs.iter().enumerate() {
            if !visited[b] {
                continue;
            }
            for &s in ss {
                if s < n {
                    preds[s].push(b);
                }
            }
        }

        let mut idom: Vec<Option<usize>> = vec![None; n];
        if entry < n {
            idom[entry] = Some(entry);
        }
        let intersect = |idom: &[Option<usize>], mut a: usize, mut b: usize| -> usize {
            while a != b {
                while po_num[a] < po_num[b] {
                    a = idom[a].unwrap_or(entry);
                }
                while po_num[b] < po_num[a] {
                    b = idom[b].unwrap_or(entry);
                }
            }
            a
        };
        let mut changed = true;
        while changed {
            changed = false;
            for &b in rpo.iter().skip(1) {
                let mut new_idom: Option<usize> = None;
                for &p in &preds[b] {
                    if idom[p].is_none() {
                        continue;
                    }
                    new_idom = Some(match new_idom {
                        None => p,
                        Some(cur) => intersect(&idom, p, cur),
                    });
                }
                if new_idom.is_some() && idom[b] != new_idom {
                    idom[b] = new_idom;
                    changed = true;
                }
            }
        }

        // Dominator-tree pre/post numbering.
        let mut children: Vec<Vec<usize>> = vec![Vec::new(); n];
        for &b in &rpo {
            if b == entry {
                continue;
            }
            if let Some(d) = idom[b] {
                children[d].push(b);
            }
        }
        let mut pre = vec![usize::MAX; n];
        let mut post = vec![usize::MAX; n];
        let mut counter = 0usize;
        let mut stack: Vec<(usize, usize)> = Vec::new();
        if entry < n {
            stack.push((entry, 0));
            pre[entry] = counter;
            counter += 1;
        }
        while let Some((b, next)) = stack.pop() {
            if let Some(&c) = children[b].get(next) {
                stack.push((b, next + 1));
                pre[c] = counter;
                counter += 1;
                stack.push((c, 0));
            } else {
                post[b] = counter;
                counter += 1;
            }
        }
        DomTree {
            rpo,
            reachable: visited,
            pre,
            post,
        }
    }

    pub(crate) fn is_reachable(&self, b: usize) -> bool {
        self.reachable.get(b).copied().unwrap_or(false)
    }

    /// Whether `a` dominates `b` (reflexive). False when either is
    /// unreachable.
    pub(crate) fn dominates(&self, a: usize, b: usize) -> bool {
        if !self.is_reachable(a) || !self.is_reachable(b) {
            return false;
        }
        self.pre[a] <= self.pre[b] && self.post[b] <= self.post[a]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn diamond_and_loop() {
        // 0 -> 1, 2; 1 -> 3; 2 -> 3; 3 -> 1 (loop), 4
        let succs = vec![vec![1, 2], vec![3], vec![3], vec![1, 4], vec![], vec![0]];
        let d = DomTree::compute(&succs, 0);
        assert!(d.dominates(0, 3));
        assert!(!d.dominates(1, 3));
        assert!(!d.dominates(2, 3));
        assert!(d.dominates(3, 4));
        assert!(!d.dominates(1, 2));
        assert!(d.dominates(1, 1));
        assert!(!d.is_reachable(5));
        assert!(!d.dominates(5, 0));
        assert_eq!(d.rpo.first(), Some(&0));
        assert_eq!(d.rpo.len(), 5);
    }

    #[test]
    fn straight_line() {
        let succs = vec![vec![1], vec![2], vec![]];
        let d = DomTree::compute(&succs, 0);
        assert!(d.dominates(1, 2));
        assert!(!d.dominates(2, 1));
    }
}
