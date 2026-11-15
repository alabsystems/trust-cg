// trust-cg-codegen/wasm/lower/storage.rs - who may read a home slot, and when
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Storage facts for memory-carried values (`Carrier::Mem`), used to decide
//! where a value's bytes may live.
//!
//! A value that OWNS storage (a *source*: a home slot, or a by-address entry
//! parameter's caller storage) is read through its own name and through every
//! ALIAS of it — a `Copy`, a `Select`, an aggregate lane of an `ExtractField` /
//! `ExtractElement` — which the lane lowers as the same address
//! (`value.rs`). [`analyze`] maps every value to the sources its address may
//! be (its *roots*), and marks a source PINNED when an address that may be its
//! storage flows anywhere other than a position that only reads the bytes
//! during the instruction (or aliases them into another memory-carried value,
//! which is tracked): a pinned source's storage may be read at any later time,
//! so nothing may ever share or outlive it.
//!
//! [`home_conflicts`] is the liveness of the remaining sources over the
//! function's CFG. Two homes may share frame bytes only when they never
//! conflict: at no instruction is one written while the other (or an alias of
//! it) is live, read, or written. Every instruction is modelled as reading all
//! its operands and writing all its results at one point, so a result never
//! shares storage with an operand of its own definition — the lowering of
//! `InsertField`, the wide integer operators and calls read operands after
//! writing part of the result, which that rule keeps sound.

use std::collections::{HashMap, HashSet};

use trust_ir::{BlockId, Function, Inst, Module, Ty, ValueId};

use super::super::layout;
use super::WasmLowerError;

/// Where each value's address may point, and which sources escape.
pub(super) struct Storage {
    /// Value → the sources whose storage its address may be (sorted, unique).
    /// Values with no entry (scalars, pooled constants, pointees of pointer
    /// carriers, a by-address parameter that is not a source) name no source.
    pub(super) roots: HashMap<ValueId, Vec<ValueId>>,
    /// Sources whose address may be observed outside a bounded read.
    pub(super) pinned: HashSet<ValueId>,
}

impl Storage {
    fn roots_of(&self, v: ValueId) -> &[ValueId] {
        self.roots.get(&v).map_or(&[], Vec::as_slice)
    }
}

/// The operands of `inst` whose ADDRESS (when memory-carried) may leave the
/// bounded-read discipline: used as a pointer, copied into a scalar, or
/// consumed by an instruction this analysis does not model. Every other
/// operand position either reads the bytes during the instruction or makes the
/// memory-carried result an alias (whose roots [`analyze`] tracks).
fn escaping_operands(inst: &Inst, result_is_mem: bool) -> Vec<ValueId> {
    let fat = |t: &Ty| matches!(t, Ty::FatPtr(_));
    match inst {
        Inst::Copy { operand, .. } if !result_is_mem => vec![*operand],
        Inst::Select {
            then_val, else_val, ..
        } if !result_is_mem => vec![*then_val, *else_val],
        Inst::PtrData { ptr_ty, ptr } | Inst::PtrMetadata { ptr_ty, ptr, .. }
            if !fat(ptr_ty) && !result_is_mem =>
        {
            vec![*ptr]
        }
        Inst::PtrFromParts { ptr_ty, data, .. } if !fat(ptr_ty) && !result_is_mem => {
            vec![*data]
        }
        Inst::Store { ptr, .. } | Inst::AtomicStore { ptr, .. } => vec![*ptr],
        Inst::Copy { .. }
        | Inst::Select { .. }
        | Inst::PtrData { .. }
        | Inst::PtrMetadata { .. }
        | Inst::PtrFromParts { .. }
        | Inst::ExtractField { .. }
        | Inst::ExtractElement { .. }
        | Inst::InsertField { .. }
        | Inst::InsertElement { .. }
        | Inst::MakeAggregate { .. }
        | Inst::ArraySplat { .. }
        | Inst::Cast { .. }
        | Inst::BinOp { .. }
        | Inst::UnOp { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Overflow { .. }
        | Inst::Call { .. }
        | Inst::CallIndirect { .. }
        | Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Return { .. }
        | Inst::Unreachable
        | Inst::Assume { .. }
        // A sited check (v54) passes a run-time location to its panic entry;
        // it takes the conservative arm below.
        | Inst::Assert {
            cond: _,
            kind: _,
            site: None,
        }
        | Inst::Fence { .. }
        | Inst::EndBorrow { .. }
        | Inst::Const { .. }
        | Inst::Undef { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. } => Vec::new(),
        other => {
            let mut all = Vec::new();
            other.visit_value_operands(|v| all.push(v));
            all
        }
    }
}

/// Compute [`Storage`] for `func`, given which values are memory-carried and
/// which own storage.
pub(super) fn analyze(
    func: &Function,
    is_mem: &dyn Fn(ValueId) -> bool,
    sources: &HashSet<ValueId>,
) -> Storage {
    let mut roots: HashMap<ValueId, Vec<ValueId>> =
        sources.iter().map(|s| (*s, vec![*s])).collect();
    // A non-owning memory-carried result aliases (a part of) an operand; the
    // union over every operand over-approximates which one. Iterated to a
    // fixpoint because block order need not follow definition order.
    loop {
        let mut changed = false;
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            for &r in &node.results {
                if sources.contains(&r) || !is_mem(r) {
                    continue;
                }
                let mut acc: Vec<ValueId> = roots.get(&r).cloned().unwrap_or_default();
                let before = acc.len();
                node.inst.visit_value_operands(|o| {
                    if let Some(rs) = roots.get(&o) {
                        acc.extend(rs.iter().copied());
                    }
                });
                acc.sort_unstable();
                acc.dedup();
                if acc.len() != before {
                    roots.insert(r, acc);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    let mut storage = Storage {
        roots,
        pinned: HashSet::new(),
    };
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        let result_is_mem = node.results.first().is_some_and(|r| is_mem(*r));
        for o in escaping_operands(&node.inst, result_is_mem) {
            let rs: Vec<ValueId> = storage.roots_of(o).to_vec();
            storage.pinned.extend(rs);
        }
    }
    storage
}

/// The entry parameters among `candidates` (by-address parameters) whose
/// caller storage would escape if the callee aliased it: the analysis runs
/// before any local is bound, over the lane's typing `types`.
pub(super) fn escaping_sources(
    func: &Function,
    module: &Module,
    entry: usize,
    types: &HashMap<ValueId, Ty>,
    candidates: &[ValueId],
) -> Result<HashSet<ValueId>, WasmLowerError> {
    let mut mem: HashSet<ValueId> = HashSet::new();
    // Visited in value order, so the first layout error reported is the same
    // on every run.
    let mut typed: Vec<(&ValueId, &Ty)> = types.iter().collect();
    typed.sort_unstable_by_key(|(v, _)| **v);
    for (v, ty) in typed {
        if layout::carrier_of(module, ty)?.is_mem() {
            mem.insert(*v);
        }
    }
    let mut sources: HashSet<ValueId> = candidates.iter().copied().collect();
    for (bi, block) in func.blocks.iter().enumerate() {
        for (v, _) in &block.params {
            if bi != entry && mem.contains(v) {
                sources.insert(*v);
            }
        }
        for node in &block.body {
            if super::owns_storage_typed(&node.inst, types) {
                sources.extend(node.results.iter().filter(|r| mem.contains(r)));
            }
        }
    }
    let storage = analyze(func, &|v| mem.contains(&v), &sources);
    Ok(candidates
        .iter()
        .copied()
        .filter(|c| storage.pinned.contains(c))
        .collect())
}

/// One program point of a block: the sources it writes and the sources whose
/// storage it reads.
struct Event {
    defs: Vec<usize>,
    uses: Vec<usize>,
}

/// A fixed-width bit set over source indices.
#[derive(Clone, PartialEq, Eq)]
pub(super) struct Bits(Vec<u64>);

impl Bits {
    fn new(n: usize) -> Self {
        Bits(vec![0; n.div_ceil(64)])
    }
    fn set(&mut self, i: usize) {
        self.0[i / 64] |= 1 << (i % 64);
    }
    fn clear(&mut self, i: usize) {
        self.0[i / 64] &= !(1 << (i % 64));
    }
    fn union_with(&mut self, o: &Bits) {
        for (a, b) in self.0.iter_mut().zip(&o.0) {
            *a |= *b;
        }
    }
    fn get(&self, i: usize) -> bool {
        self.0[i / 64] & (1 << (i % 64)) != 0
    }
    fn count(&self) -> usize {
        self.0.iter().map(|w| w.count_ones() as usize).sum()
    }
    fn for_each(&self, mut f: impl FnMut(usize)) {
        for (w, &word) in self.0.iter().enumerate() {
            let mut x = word;
            while x != 0 {
                let b = x.trailing_zeros() as usize;
                f(w * 64 + b);
                x &= x - 1;
            }
        }
    }
}

/// The most homes whose pairwise conflicts [`home_conflicts`] records
/// exactly, as one bit row per home (`n * n / 8` bytes: 32 MiB at the
/// limit). Past it every home gets a live HULL instead.
pub(super) const MAX_EXACT_HOMES: usize = 1 << 14;

/// Which homes may not share frame bytes (see [`home_conflicts`]).
pub(super) enum Interference {
    /// The exact pairwise relation: `rows[i]` holds every `j` whose storage
    /// must not overlap `i`'s (symmetric, no diagonal).
    Exact(Vec<Bits>),
    /// Per home, the closed range of program events (numbered in block
    /// order) that contains every point where it is written, read, or live.
    /// Two homes whose hulls are disjoint never conflict — every conflicting
    /// point lies in both hulls — so disjoint hulls may share bytes; this
    /// over-approximates the exact relation (it shares less inside loops).
    Hulls(Vec<(usize, usize)>),
}

impl Interference {
    /// Whether homes `i` and `j` must be kept apart.
    pub(super) fn conflict(&self, i: usize, j: usize) -> bool {
        match self {
            Interference::Exact(rows) => rows[i].get(j),
            Interference::Hulls(h) => h[i].0 <= h[j].1 && h[j].0 <= h[i].1,
        }
    }

    /// How many homes `i` conflicts with ([`Interference::Exact`] only).
    pub(super) fn degree(&self, i: usize) -> Option<usize> {
        match self {
            Interference::Exact(rows) => Some(rows[i].count()),
            Interference::Hulls(_) => None,
        }
    }

    /// Visit every home `i` conflicts with ([`Interference::Exact`] only).
    pub(super) fn for_each_conflict(&self, i: usize, f: impl FnMut(usize)) {
        if let Interference::Exact(rows) = self {
            rows[i].for_each(f);
        }
    }
}

/// Every edge `inst` leaves by: its target block and the arguments that edge
/// copies into the target's parameters.
pub(super) fn edges(inst: &Inst) -> Vec<(BlockId, &[ValueId])> {
    match inst {
        Inst::Br { target, args } => vec![(*target, args.as_slice())],
        Inst::CondBr {
            then_target,
            then_args,
            else_target,
            else_args,
            ..
        } => vec![
            (*then_target, then_args.as_slice()),
            (*else_target, else_args.as_slice()),
        ],
        Inst::Switch {
            default,
            default_args,
            cases,
            ..
        } => {
            let mut t = vec![(*default, default_args.as_slice())];
            t.extend(cases.iter().map(|c| (c.target, c.args.as_slice())));
            t
        }
        _ => Vec::new(),
    }
}

/// One CFG edge as liveness sees it: the target block, and the sources the
/// edge copy reads (the roots of its arguments).
struct Edge {
    target: usize,
    arg_roots: Vec<usize>,
}

/// Which `sources` (indexed by position) may not share storage: the exact
/// pairwise relation for up to [`MAX_EXACT_HOMES`] of them, live hulls past
/// that ([`Interference`]). Pinned sources are kept apart from everything by
/// the caller, whatever this reports.
///
/// Liveness is over storage, not names: a use of any value reads every source
/// in its roots. An entry parameter's home is written by the prologue (at the
/// entry block's start). A block parameter's home is written by the copy ON
/// EACH INCOMING EDGE, which runs only when that edge is taken: a `CondBr` or
/// `Switch` writes the parameters of the target it branches to and no other,
/// so a parameter still live along another edge (a loop exit that reads the
/// header's parameter) stays live across the terminator. Hence
/// `live_out(B) = ∪ over edges B→S of (live_in(S) \ params(S))`, and each
/// edge's copy writes `params(S)` while reading its arguments' roots, with
/// `live_in(S) \ params(S)` live after it.
pub(super) fn home_conflicts(
    func: &Function,
    block_index: &HashMap<BlockId, usize>,
    entry: usize,
    storage: &Storage,
    sources: &[ValueId],
) -> Interference {
    home_conflicts_limited(func, block_index, entry, storage, sources, MAX_EXACT_HOMES)
}

/// [`home_conflicts`] with the exact relation kept up to `exact_limit`
/// sources.
fn home_conflicts_limited(
    func: &Function,
    block_index: &HashMap<BlockId, usize>,
    entry: usize,
    storage: &Storage,
    sources: &[ValueId],
    exact_limit: usize,
) -> Interference {
    let n = sources.len();
    let index: HashMap<ValueId, usize> = sources.iter().enumerate().map(|(i, v)| (*v, i)).collect();
    let root_ids = |v: ValueId, out: &mut Vec<usize>| {
        for r in storage.roots_of(v) {
            if let Some(&i) = index.get(r) {
                out.push(i);
            }
        }
    };
    let nb = func.blocks.len();
    let params: Vec<Vec<usize>> = func
        .blocks
        .iter()
        .map(|b| {
            b.params
                .iter()
                .filter_map(|(v, _)| index.get(v).copied())
                .collect()
        })
        .collect();
    let mut block_edges: Vec<Vec<Edge>> = Vec::with_capacity(nb);
    let mut events: Vec<Vec<Event>> = Vec::with_capacity(nb);
    for (bi, block) in func.blocks.iter().enumerate() {
        let mut evs = Vec::with_capacity(block.body.len() + 1);
        let mut out_edges = Vec::new();
        if bi == entry {
            evs.push(Event {
                defs: params[bi].clone(),
                uses: Vec::new(),
            });
        }
        for node in &block.body {
            let mut uses = Vec::new();
            node.inst.visit_value_operands(|o| root_ids(o, &mut uses));
            let defs: Vec<usize> = node
                .results
                .iter()
                .filter_map(|r| index.get(r).copied())
                .collect();
            for (t, args) in edges(&node.inst) {
                let Some(&ti) = block_index.get(&t) else {
                    continue;
                };
                let mut arg_roots = Vec::new();
                for &a in args {
                    root_ids(a, &mut arg_roots);
                }
                out_edges.push(Edge {
                    target: ti,
                    arg_roots,
                });
            }
            evs.push(Event { defs, uses });
        }
        events.push(evs);
        block_edges.push(out_edges);
    }
    // What is live on edge `e` after its copy: the target's live-in minus the
    // parameters the copy writes.
    let after_edge = |e: &Edge, live_in: &[Bits]| -> Bits {
        let mut b = live_in[e.target].clone();
        for &p in &params[e.target] {
            b.clear(p);
        }
        b
    };
    let live_out = |bi: usize, live_in: &[Bits]| -> Bits {
        let mut out = Bits::new(n);
        for e in &block_edges[bi] {
            out.union_with(&after_edge(e, live_in));
        }
        out
    };
    // Backward liveness to a fixpoint.
    let transfer = |evs: &[Event], mut live: Bits| -> Bits {
        for ev in evs.iter().rev() {
            for &d in &ev.defs {
                live.clear(d);
            }
            for &u in &ev.uses {
                live.set(u);
            }
        }
        live
    };
    let mut live_in: Vec<Bits> = vec![Bits::new(n); nb];
    loop {
        let mut changed = false;
        for bi in (0..nb).rev() {
            let inn = transfer(&events[bi], live_out(bi, &live_in));
            if inn != live_in[bi] {
                live_in[bi] = inn;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    if n > exact_limit {
        return Interference::Hulls(home_hulls(
            &events,
            &block_edges,
            &params,
            &live_in,
            |bi, live_in| live_out(bi, live_in),
            n,
        ));
    }
    // Conflicts: at every event, each written source against everything live
    // after it, everything it reads, and every other source it writes; at
    // every edge copy, each written parameter likewise. One bit row per
    // source, filled word-parallel from the live set, then made symmetric.
    let mut rows: Vec<Bits> = vec![Bits::new(n); n];
    for bi in 0..nb {
        for e in &block_edges[bi] {
            let live = after_edge(e, &live_in);
            for &d in &params[e.target] {
                rows[d].union_with(&live);
                for &u in &e.arg_roots {
                    rows[d].set(u);
                }
                for &d2 in &params[e.target] {
                    rows[d].set(d2);
                }
            }
        }
        let mut live = live_out(bi, &live_in);
        for ev in events[bi].iter().rev() {
            for &d in &ev.defs {
                rows[d].union_with(&live);
                for &u in &ev.uses {
                    rows[d].set(u);
                }
                for &d2 in &ev.defs {
                    rows[d].set(d2);
                }
            }
            for &d in &ev.defs {
                live.clear(d);
            }
            for &u in &ev.uses {
                live.set(u);
            }
        }
    }
    let mut row_bits: Vec<usize> = Vec::new();
    for i in 0..n {
        row_bits.clear();
        rows[i].for_each(|j| row_bits.push(j));
        for &j in &row_bits {
            rows[j].set(i);
        }
    }
    for (i, row) in rows.iter_mut().enumerate() {
        row.clear(i);
    }
    Interference::Exact(rows)
}

/// The live hull of every source (see [`Interference::Hulls`]): the events
/// that write it (a block parameter is written by each incoming edge's copy,
/// at its predecessor's terminator), that read it through any value whose
/// roots include it, and the first event of every block it is live into and
/// the last of every block it is live out of.
fn home_hulls(
    events: &[Vec<Event>],
    block_edges: &[Vec<Edge>],
    params: &[Vec<usize>],
    live_in: &[Bits],
    live_out: impl Fn(usize, &[Bits]) -> Bits,
    n: usize,
) -> Vec<(usize, usize)> {
    let mut hull = vec![(usize::MAX, 0usize); n];
    let mut touch = |i: usize, at: usize| {
        let h = &mut hull[i];
        h.0 = h.0.min(at);
        h.1 = h.1.max(at);
    };
    let mut at = 0usize;
    for (bi, evs) in events.iter().enumerate() {
        let first = at;
        for ev in evs {
            for &x in ev.defs.iter().chain(&ev.uses) {
                touch(x, at);
            }
            at += 1;
        }
        let last = at.saturating_sub(1).max(first);
        live_in[bi].for_each(|x| touch(x, first));
        live_out(bi, live_in).for_each(|x| touch(x, last));
        for e in &block_edges[bi] {
            for &p in &params[e.target] {
                touch(p, last);
            }
            for &u in &e.arg_roots {
                touch(u, last);
            }
        }
    }
    hull
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Homes carried in a loop, across a `switch`, and along an exit edge
    /// that reads the header's parameters.
    const LOOPY: &str = r#"module "m"
target "wasm32-unknown-unknown" 4 little

struct @P { : i64 @0, : i64 @8 } size=16 align=8 id=0

functy.0 = (i64, i64) -> (i64)

fn @f(functy.0) {
bb0(%0: i64, %1: i64):
    %2 = make_aggregate struct.0 (%0, %1)
    %3 = const i64 0
    br bb1(%2, %3)
bb1(%4: struct.0, %5: i64):
    %6 = extractfield i64 %4, 0
    %7 = make_aggregate struct.0 (%6, %5)
    %8 = make_aggregate struct.0 (%5, %6)
    %9 = const i64 3
    %10 = icmp slt i64 %5, %9
    condbr %10, bb2, bb4
bb2:
    %11 = extractfield i64 %7, 1
    switch %11 [ 0: bb3 1: bb3 default: bb5 ]
bb3:
    %12 = const i64 1
    %13 = add i64 %5, %12
    %14 = make_aggregate struct.0 (%13, %11)
    br bb1(%14, %13)
bb5:
    %15 = extractfield i64 %8, 0
    %16 = make_aggregate struct.0 (%15, %15)
    %17 = const i64 2
    %18 = add i64 %5, %17
    br bb1(%16, %18)
bb4:
    %19 = extractfield i64 %4, 1
    %20 = extractfield i64 %8, 1
    %21 = add i64 %19, %20
    ret %21
}
"#;

    /// Live hulls over-approximate the exact relation: every pair of homes
    /// that conflicts exactly also has overlapping hulls, so a placement
    /// that shares bytes only between disjoint hulls never shares a
    /// conflicting pair.
    #[test]
    fn live_hulls_contain_every_exact_conflict() {
        let module = trust_ir::parser::parse_module(LOOPY).expect("parse");
        let func = &module.functions[0];
        let types = super::super::value_types(&module, func).expect("types");
        let mem: HashSet<ValueId> = types
            .iter()
            .filter(|(_, t)| layout::carrier_of(&module, t).is_ok_and(|c| c.is_mem()))
            .map(|(v, _)| *v)
            .collect();
        let mut sources: Vec<ValueId> = Vec::new();
        for block in &func.blocks {
            sources.extend(
                block
                    .params
                    .iter()
                    .map(|(v, _)| *v)
                    .filter(|v| mem.contains(v)),
            );
            for node in &block.body {
                if super::super::owns_storage(&node.inst) {
                    sources.extend(node.results.iter().filter(|r| mem.contains(r)));
                }
            }
        }
        let set: HashSet<ValueId> = sources.iter().copied().collect();
        let storage = analyze(func, &|v| mem.contains(&v), &set);
        let block_index: HashMap<BlockId, usize> = func
            .blocks
            .iter()
            .enumerate()
            .map(|(i, b)| (b.id, i))
            .collect();
        let entry = block_index[&func.entry];
        let exact =
            home_conflicts_limited(func, &block_index, entry, &storage, &sources, usize::MAX);
        let hulls = home_conflicts_limited(func, &block_index, entry, &storage, &sources, 0);
        assert!(matches!(exact, Interference::Exact(_)));
        assert!(matches!(hulls, Interference::Hulls(_)));
        let n = sources.len();
        assert!(n >= 6, "{n} homes");
        let mut apart = 0;
        for i in 0..n {
            for j in 0..n {
                if i == j {
                    continue;
                }
                assert_eq!(exact.conflict(i, j), exact.conflict(j, i), "symmetric");
                if exact.conflict(i, j) {
                    assert!(hulls.conflict(i, j), "hulls miss the conflict {i}-{j}");
                } else {
                    apart += 1;
                }
            }
        }
        assert!(apart > 0, "some homes never conflict");
    }
}
