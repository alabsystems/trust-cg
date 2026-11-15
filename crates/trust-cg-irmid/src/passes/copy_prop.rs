// trust-cg-irmid/passes/copy_prop.rs - copy propagation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Copy propagation: `%v = copy T %x`, where `%x` has exactly type `T`, is the
//! identity, so every use of `%v` may read `%x` (following chains of copies to
//! their root) and the copy goes. A copy that changes its operand's type (the
//! MIR lowering writes `copy u32 %i` of an `i32`) is not an identity in
//! trust-ir's typing and stays, as does a copy whose operand's type the pass
//! cannot read.

use std::collections::{HashMap, HashSet};

use trust_cg_verify::trust_ir_mid_tv::{CopyForward, CopyPropWitness, PassWitness};
use trust_ir::{Function, Inst, ValueId};

use super::{MidPass, PassContext, drop_names, value_types};

pub(crate) struct CopyProp;

impl MidPass for CopyProp {
    fn name(&self) -> &'static str {
        "copy_prop"
    }

    fn run(&self, _cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let types = value_types(func);
        let mut direct: HashMap<ValueId, ValueId> = HashMap::new();
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            if let (Inst::Copy { ty, operand }, [result]) = (&node.inst, node.results.as_slice())
                && types.get(operand) == Some(ty)
                && operand != result
            {
                direct.insert(*result, *operand);
            }
        }
        if direct.is_empty() {
            return None;
        }
        // Follow each chain to its root; a chain that cycles (only possible in
        // malformed or unreachable code) is left alone.
        // Roots are memoized, so a long chain is walked once.
        let mut map: HashMap<ValueId, ValueId> = HashMap::new();
        let mut cyclic: HashSet<ValueId> = HashSet::new();
        for &copy in direct.keys() {
            let mut path = Vec::new();
            let mut at = copy;
            let root = loop {
                if let Some(&root) = map.get(&at) {
                    break Some(root);
                }
                if cyclic.contains(&at) || path.len() > direct.len() {
                    break None;
                }
                match direct.get(&at) {
                    Some(&next) => {
                        path.push(at);
                        at = next;
                    }
                    None => break Some(at),
                }
            };
            match root {
                Some(root) => {
                    for value in path {
                        map.insert(value, root);
                    }
                }
                None => cyclic.extend(path),
            }
        }
        if map.is_empty() {
            return None;
        }
        let removed: HashSet<ValueId> = map.keys().copied().collect();
        let mut out = func.clone();
        for block in &mut out.blocks {
            block
                .body
                .retain(|n| !(n.results.len() == 1 && removed.contains(&n.results[0])));
            for node in &mut block.body {
                trust_ir::mem2reg::rewrite_inst(&mut node.inst, &map);
            }
        }
        drop_names(&mut out, &removed);
        let mut forwards: Vec<CopyForward> = map
            .into_iter()
            .map(|(copy, root)| CopyForward { copy, root })
            .collect();
        forwards.sort_by_key(|f| f.copy.index());
        Some((out, PassWitness::CopyProp(CopyPropWitness { forwards })))
    }
}
