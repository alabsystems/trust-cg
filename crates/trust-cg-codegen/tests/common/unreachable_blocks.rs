// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Drop the blocks no edge reaches from a fixture's functions.
//!
//! Several fixture generators create every block a shape might use and branch
//! to only some of them (a guard's own early-exit block when the shape exits
//! to a shared block, and the reverse). trust-ir refuses a block no edge
//! reaches (`UnreachableBlock`: the validator's reachability walk from the
//! entry), and since WS7.3 every trust-cg ingestion entry refuses what that
//! validator refuses. A block no edge reaches is never executed and its values
//! cannot be used by a reachable block (dominance), so removing it changes
//! nothing the program computes; the reachable control-flow graph — the shape
//! under test — is untouched.

// Declared unconditionally; a target whose callers are all cfg'd out for this
// host must not trip the workspace's `warnings = "deny"`.
#![allow(dead_code)]

use std::collections::{BTreeSet, VecDeque};

use trust_ir::{BlockId, Module};

/// `module` without the blocks no edge reaches from their function's entry.
pub fn without_unreachable_blocks(module: &Module) -> Module {
    let mut module = module.clone();
    for function in &mut module.functions {
        if function.blocks.is_empty() {
            continue;
        }
        let mut reachable: BTreeSet<BlockId> = BTreeSet::from([function.entry]);
        let mut queue = VecDeque::from([function.entry]);
        while let Some(id) = queue.pop_front() {
            let Some(block) = function.blocks.iter().find(|block| block.id == id) else {
                continue;
            };
            let Some(terminator) = block.terminator() else {
                continue;
            };
            for edge in terminator.inst.successor_edges() {
                if reachable.insert(edge.target) {
                    queue.push_back(edge.target);
                }
            }
        }
        function
            .blocks
            .retain(|block| reachable.contains(&block.id));
    }
    module
}
