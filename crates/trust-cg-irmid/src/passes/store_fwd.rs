// trust-cg-irmid/passes/store_fwd.rs - single-dominating-store forwarding
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A plain load from an unobservable slot (`slots.rs`) becomes `copy` of the
//! value a plain store wrote when that store is, on every path from the
//! entry, the last write of exactly the load's bytes: the same offset, the
//! same type and alignment, with no store overlapping them and no execution
//! of the `alloca` (a fresh allocation) in between. Only types a reload
//! returns exactly are forwarded (integers, `bool`, `char`, floats — not
//! pointers), never a stored `undef`, and only a value whose own type is the
//! load's (a store may write a value of another type, an enum a call
//! returns stored as its tag byte, and `copy` would then change its type).
//!
//! The analysis is a forward "available store" data flow per slot over its
//! distinct `(offset, type)` keys: a store makes its key available and kills
//! every overlapping key, the `alloca` kills all, and a join keeps a key only
//! when every predecessor makes the same store available. A key nothing
//! makes available on some path (an undefined read), a partial overlap or a
//! mixed width therefore leaves the load alone. A function whose CFG is
//! irreducible is left alone whole.

use std::collections::HashMap;

use trust_cg_verify::trust_ir_mid_tv::{LoadForward, PassWitness, StoreFwdWitness};
use trust_ir::{BlockId, Function, Inst, Module, Ty};

use super::slots::{Slot, round_trips, unobservable_slots};
use super::{MidPass, PassContext, sole_defs, value_types};
use crate::cfg::TrustIrCfg;
use trust_cg_opt::mach_view::CfgAnalysis;

pub(crate) struct StoreFwd;

/// What is available for one key.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Avail {
    /// Not reached yet (the join's identity).
    Top,
    /// No single store.
    None,
    /// The store at `(block position, node index)`.
    Store(usize, usize),
}

impl Avail {
    fn meet(self, other: Avail) -> Avail {
        match (self, other) {
            (Avail::Top, x) | (x, Avail::Top) => x,
            (a, b) if a == b => a,
            _ => Avail::None,
        }
    }
}

/// Whether the CFG is reducible: every edge that retreats in reverse
/// postorder goes to a block that dominates its source.
pub(crate) fn reducible(func: &Function, cfg: &CfgAnalysis<BlockId>) -> bool {
    let rank: HashMap<BlockId, usize> = cfg.rpo.iter().enumerate().map(|(i, b)| (*b, i)).collect();
    for block in &func.blocks {
        let Some(&from) = rank.get(&block.id) else {
            continue;
        };
        let Some(last) = block.body.last() else {
            continue;
        };
        for edge in last.inst.successor_edges() {
            if let Some(&to) = rank.get(&edge.target)
                && to <= from
                && !cfg.dominates(edge.target, block.id)
            {
                return false;
            }
        }
    }
    true
}

impl MidPass for StoreFwd {
    fn name(&self) -> &'static str {
        "store_fwd"
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let slots: Vec<Slot> = unobservable_slots(cx.module, func)
            .into_iter()
            .filter(|s| s.accesses.iter().any(|a| a.store) && s.accesses.iter().any(|a| !a.store))
            .collect();
        if slots.is_empty() {
            return None;
        }
        let view = TrustIrCfg::new(func);
        let cfg = view.analysis();
        if !reducible(func, &cfg) {
            return None;
        }
        let positions: HashMap<BlockId, usize> = func
            .blocks
            .iter()
            .enumerate()
            .map(|(i, b)| (b.id, i))
            .collect();
        let order: Vec<usize> = cfg
            .rpo
            .iter()
            .filter_map(|b| positions.get(b).copied())
            .collect();
        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); func.blocks.len()];
        for (bi, block) in func.blocks.iter().enumerate() {
            if let Some(last) = block.body.last() {
                for edge in last.inst.successor_edges() {
                    if let Some(&ti) = positions.get(&edge.target) {
                        preds[ti].push(bi);
                    }
                }
            }
        }
        let entry = *positions.get(&func.entry)?;
        let defs = sole_defs(func);
        let types = value_types(func);
        let mut forwards: Vec<LoadForward> = Vec::new();
        for slot in &slots {
            forward_slot(
                cx.module,
                func,
                &types,
                slot,
                &order,
                &preds,
                entry,
                &defs,
                &mut forwards,
            );
        }
        if forwards.is_empty() {
            return None;
        }
        forwards.sort_by_key(|f| (f.block.index(), f.index));
        let mut out = func.clone();
        for f in &forwards {
            let bi = positions[&f.block];
            let Inst::Load { ty, .. } = &out.blocks[bi].body[f.index].inst else {
                return None;
            };
            out.blocks[bi].body[f.index].inst = Inst::Copy {
                ty: ty.clone(),
                operand: f.value,
            };
        }
        Some((out, PassWitness::StoreFwd(StoreFwdWitness { forwards })))
    }
}

/// The available-store data flow of one slot, and the loads it forwards.
#[allow(clippy::too_many_arguments)]
fn forward_slot(
    module: &Module,
    func: &Function,
    types: &HashMap<trust_ir::ValueId, Ty>,
    slot: &Slot,
    order: &[usize],
    preds: &[Vec<usize>],
    entry: usize,
    defs: &HashMap<trust_ir::ValueId, &Inst>,
    forwards: &mut Vec<LoadForward>,
) {
    // Keys: distinct (offset, type) of the slot's accesses.
    let mut keys: Vec<(u64, Ty, u64)> = Vec::new();
    let mut key_of: Vec<usize> = Vec::with_capacity(slot.accesses.len());
    for access in &slot.accesses {
        let (Inst::Load { ty, .. } | Inst::Store { ty, .. }) =
            &func.blocks[access.at.0].body[access.at.1].inst
        else {
            return;
        };
        let k = keys
            .iter()
            .position(|(o, t, _)| *o == access.offset && t == ty)
            .unwrap_or_else(|| {
                keys.push((access.offset, ty.clone(), access.size));
                keys.len() - 1
            });
        key_of.push(k);
    }
    let overlap = |a: usize, b: usize| {
        let (ao, _, an) = &keys[a];
        let (bo, _, bn) = &keys[b];
        *ao < bo.saturating_add(*bn) && *bo < ao.saturating_add(*an)
    };
    // Events per block, in node order: `Some(key)` a store, `None` the
    // alloca, loads apart.
    let mut events: HashMap<usize, Vec<(usize, Option<usize>)>> = HashMap::new();
    events.entry(slot.at.0).or_default().push((slot.at.1, None));
    for (access, &k) in slot.accesses.iter().zip(&key_of) {
        if access.store {
            events
                .entry(access.at.0)
                .or_default()
                .push((access.at.1, Some(k)));
        }
    }
    for list in events.values_mut() {
        list.sort_by_key(|(ni, _)| *ni);
    }
    let n = func.blocks.len();
    let transfer = |bi: usize, state: &mut Vec<Avail>, upto: usize| {
        if let Some(list) = events.get(&bi) {
            for &(ni, event) in list {
                if ni >= upto {
                    break;
                }
                match event {
                    None => state.iter_mut().for_each(|s| *s = Avail::None),
                    Some(k) => {
                        for (j, s) in state.iter_mut().enumerate() {
                            if j != k && overlap(j, k) {
                                *s = Avail::None;
                            }
                        }
                        state[k] = Avail::Store(bi, ni);
                    }
                }
            }
        }
    };
    let mut reachable = vec![false; n];
    for &bi in order {
        reachable[bi] = true;
    }
    let mut out_state: Vec<Option<Vec<Avail>>> = vec![None; n];
    let mut in_state: Vec<Vec<Avail>> = vec![vec![Avail::Top; keys.len()]; n];
    let mut changed = true;
    while changed {
        changed = false;
        for &bi in order {
            // The function's start makes nothing available, and neither does
            // an unreachable predecessor (conservatively: the checker walks
            // every CFG path, feasible or not).
            let mut state = if bi == entry {
                vec![Avail::None; keys.len()]
            } else {
                vec![Avail::Top; keys.len()]
            };
            for &p in &preds[bi] {
                match &out_state[p] {
                    Some(ps) => {
                        for (s, o) in state.iter_mut().zip(ps) {
                            *s = s.meet(*o);
                        }
                    }
                    None if !reachable[p] => state.iter_mut().for_each(|s| *s = Avail::None),
                    None => {}
                }
            }
            in_state[bi] = state.clone();
            transfer(bi, &mut state, usize::MAX);
            if out_state[bi].as_ref() != Some(&state) {
                out_state[bi] = Some(state);
                changed = true;
            }
        }
    }
    for (access, &k) in slot.accesses.iter().zip(&key_of) {
        if access.store {
            continue;
        }
        let (bi, ni) = access.at;
        if out_state[bi].is_none() {
            continue; // unreachable
        }
        let mut state = in_state[bi].clone();
        transfer(bi, &mut state, ni);
        let Avail::Store(sb, sn) = state[k] else {
            continue;
        };
        let load = &func.blocks[bi].body[ni];
        let store = &func.blocks[sb].body[sn];
        let (
            Inst::Load {
                ty,
                volatile: false,
                align,
                ..
            },
            Inst::Store {
                ty: store_ty,
                value,
                volatile: false,
                align: store_align,
                ..
            },
            [result],
        ) = (&load.inst, &store.inst, load.results.as_slice())
        else {
            continue;
        };
        if ty != store_ty || align != store_align || !round_trips(ty) {
            continue;
        }
        if matches!(defs.get(value), Some(Inst::Undef { .. })) {
            continue;
        }
        // Only a value of the load's own type: `copy` is the identity there.
        let value_ty = types.get(value).cloned().or_else(|| match defs.get(value) {
            Some(Inst::Call { callee, .. }) => module
                .function_by_id(*callee)
                .and_then(|f| module.func_type(f.ty))
                .and_then(|ft| match ft.returns.as_slice() {
                    [r] => Some(r.clone()),
                    _ => None,
                }),
            _ => None,
        });
        if value_ty.as_ref() != Some(ty) {
            continue;
        }
        forwards.push(LoadForward {
            block: func.blocks[bi].id,
            index: ni,
            result: *result,
            store_block: func.blocks[sb].id,
            store_index: sn,
            value: *value,
        });
    }
}
