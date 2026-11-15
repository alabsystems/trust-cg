// trust-cg-irmid/passes/byaddr_reading.rs - how by-address cloning reads a callee
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! By-address cloning's typing and prologue of a callee: the pass's own copy
//! of its checker's `types_of` and `prologue` (`trust-cg-verify`'s
//! `trust_ir_mid_tv_byaddr.rs`), kept separate as OD-117 keeps every pass
//! table apart from its checker's. `trust-cg-irmid` depends on
//! `trust-cg-verify`, so the checker's crate cannot name this pass; its tests
//! compile this file (it names nothing but `std` and `trust_ir`) and compare
//! the two over a corpus of shapes
//! (`the_pass_reads_a_callee_as_the_checker_does`), so a change to either
//! side alone fails there.

use std::collections::{HashMap, HashSet};

use trust_ir::{Function, Inst, Ty, ValueId};

/// The checker's typing of `func`'s values: block parameters, copies, loads,
/// constants and casts at their stated type, and `alloca`, `gep` and
/// `globaladdr` results as `ptr`. Every other result (`select`, `undef`,
/// `nullptr`, arithmetic, a comparison, an `insertfield` or
/// `make_aggregate`) has no type here, so an argument or an `insertfield`
/// operand defined by one is not admitted, as the checker does not admit it.
pub(super) fn types_of(func: &Function) -> HashMap<ValueId, Ty> {
    let mut out = HashMap::new();
    for block in &func.blocks {
        for (v, t) in &block.params {
            out.insert(*v, t.clone());
        }
        for node in &block.body {
            let [r] = node.results.as_slice() else {
                continue;
            };
            let ty = match &node.inst {
                Inst::Copy { ty, .. } | Inst::Load { ty, .. } | Inst::Const { ty, .. } => {
                    ty.clone()
                }
                Inst::Cast { dst_ty, .. } => dst_ty.clone(),
                Inst::Alloca { .. } | Inst::GEP { .. } | Inst::GlobalAddr { .. } => Ty::Ptr,
                _ => continue,
            };
            out.insert(*r, ty);
        }
    }
    out
}

/// The length of the prologue of `func`'s entry block when the parameters
/// `promoted` are promoted (the checker's `prologue`; 0 without an entry
/// block): the longest prefix of the entry block made only of count-free
/// `alloca`s (the prefix's slots), `const`, `gep`, casts, `copy`, `binop`,
/// `unop`, `icmp`, `select`, non-volatile loads, `extractfield`s of a
/// promoted parameter, and `insertfield`s through and non-volatile stores
/// to a slot of the prefix or a `gep` of one by constant indices. Any other
/// form ends it, including forms that write no memory (`globaladdr`,
/// `nullptr`, `undef`, `overflow`, `fcmp`) or only the callee's own slot (a
/// `memset` of it).
pub(super) fn prologue(func: &Function, promoted: &HashSet<ValueId>) -> usize {
    let Some(entry) = func.blocks.iter().find(|b| b.id == func.entry) else {
        return 0;
    };
    let mut defs: HashMap<ValueId, &Inst> = HashMap::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        if let [r] = node.results.as_slice() {
            defs.insert(*r, &node.inst);
        }
    }
    let constant = |v: &ValueId| matches!(defs.get(v), Some(Inst::Const { .. }));
    let mut slots: HashSet<ValueId> = HashSet::new();
    for (n, node) in entry.body.iter().enumerate() {
        let into_slot = |slots: &HashSet<ValueId>, p: &ValueId| {
            slots.contains(p)
                || matches!(defs.get(p), Some(Inst::GEP { base, indices, .. })
                    if slots.contains(base) && indices.iter().all(constant))
        };
        let ok = match &node.inst {
            Inst::Alloca { count: None, .. } => {
                slots.extend(node.results.iter().copied());
                true
            }
            Inst::Const { .. }
            | Inst::GEP { .. }
            | Inst::Cast { .. }
            | Inst::Copy { .. }
            | Inst::BinOp { .. }
            | Inst::UnOp { .. }
            | Inst::ICmp { .. }
            | Inst::Select { .. }
            | Inst::Load {
                volatile: false, ..
            } => true,
            Inst::ExtractField { aggregate, .. } => promoted.contains(aggregate),
            Inst::ExtractElement { array, .. } => promoted.contains(array),
            Inst::InsertField { aggregate, .. } => into_slot(&slots, aggregate),
            Inst::Store {
                ptr,
                volatile: false,
                ..
            } => into_slot(&slots, ptr),
            _ => false,
        };
        if !ok {
            return n;
        }
    }
    entry.body.len()
}
