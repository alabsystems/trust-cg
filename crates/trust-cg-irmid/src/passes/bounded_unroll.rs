// trust-cg-irmid/passes/bounded_unroll.rs - unrolling to an interval bound
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Interval-bounded unrolling: a loop whose trip count is not a constant but
//! is at most a small constant `B` by the intervals of the values its exit
//! test reads (`min_zip2`'s `zip` over `a[..k % 5]` and a 4-element array:
//! `min(k % 5, 4)` trips) becomes `B` copies of its iterations, each keeping
//! its own exit test, and one last visit of the header, which leaves. LLVM
//! unrolls the same loop to its bound. The copies' induction variables are
//! constants, so their element addresses are slot offsets that store
//! forwarding and scalar replacement resolve, and their exit tests compare
//! a constant with the trip count.
//!
//! **Which loops** (each re-derived by the checker,
//! `trust_ir_mid_tv_bounded.rs`): full unrolling's loops (a natural loop
//! with a dedicated preheader, one back edge, no inner cycle, the admitted
//! terminators), whose header ends in a `condbr` or `switch` that both
//! stays in and leaves the loop, whose values are read outside the loop
//! only by exit blocks (entered by one edge from the loop, copied per
//! iteration), and whose header's terminator takes an edge out of the loop
//! on visit `B`: its induction variables are constants there, the values
//! from before the loop are read by their intervals, and the header's own
//! instructions are evaluated on those.
//!
//! **Policy** (not the checker's): the smallest such `B` up to
//! [`POLICY_BOUND`]; full unrolling's cost model (no copy keeping a call or
//! a 128-bit operation, at most 256 instructions left after folding, the
//! loop allocating nothing, every copied instruction one trust-ir's
//! validator reads without a finding). Full unrolling runs first; this pass
//! takes the loops whose trip count it could not decide.
//!
//! **The rewrite** is the checker's construction; the witness names the
//! header, the bound and the fresh blocks and values in its order.

use std::collections::{HashMap, HashSet};

use trust_cg_verify::trust_ir_mid_tv::{
    BoundedUnrollLoop, BoundedUnrollWitness, MAX_UNROLLED_INSTS, PassWitness,
};
use trust_ir::{
    BinOp, Block, BlockId, CastOp, Constant, Function, ICmpOp, Inst, InstrNode, Ty, ValueId,
};

use super::loops::{Loop, clean, def_blocks, first_free_value, rewritable_loops};
use super::unroll::{Lin, LinRoot, Lins, copy_cost, inner_cycle, low, redirect};
use super::{MidPass, PassContext, drop_names, int_shape, value_types, value_types_with_overflow};

pub(crate) struct BoundedUnroll;

/// The evidence name of interval-bounded unrolling.
pub(crate) const BOUNDED_UNROLL_NAME: &str = "bounded_unroll";

/// The largest bound the pass unrolls to.
const POLICY_BOUND: u32 = 8;

/// The most instructions the copies may keep once the induction variables
/// are constants (full unrolling's bound).
const POLICY_INSTS: usize = 256;

/// The pass's abstract value: a constant, or an unsigned interval, at a
/// width.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Span {
    lo: u128,
    hi: u128,
    w: u32,
}

fn span(lo: u128, hi: u128, w: u32) -> Span {
    Span { lo, hi, w }
}

/// The pass's facts over one function.
struct Ranges<'f> {
    pb: u32,
    defs: HashMap<ValueId, &'f Inst>,
    types: HashMap<ValueId, Ty>,
    param_at: HashMap<ValueId, (usize, usize)>,
    entering: Vec<Vec<Vec<ValueId>>>,
    /// The entry block's position: the call also enters it.
    entry: Option<usize>,
    /// Derivation steps left: a definition DAG with shared operands would
    /// otherwise be walked once per path.
    budget: std::cell::Cell<usize>,
}

/// The derivation steps one function's intervals may take.
const INTERVAL_STEPS: usize = 4096;

impl<'f> Ranges<'f> {
    fn new(func: &'f Function, pb: u32) -> Self {
        let at: HashMap<BlockId, usize> = func
            .blocks
            .iter()
            .enumerate()
            .map(|(i, b)| (b.id, i))
            .collect();
        let mut defs = HashMap::new();
        let mut param_at = HashMap::new();
        let mut entering = vec![Vec::new(); func.blocks.len()];
        for (bi, block) in func.blocks.iter().enumerate() {
            for (j, (p, _)) in block.params.iter().enumerate() {
                param_at.insert(*p, (bi, j));
            }
            for node in &block.body {
                if let [r] = node.results.as_slice() {
                    defs.insert(*r, &node.inst);
                }
            }
            if let Some(last) = block.body.last() {
                for e in last.inst.successor_edges() {
                    if let Some(&t) = at.get(&e.target) {
                        entering[t].push(e.args.to_vec());
                    }
                }
            }
        }
        Self {
            pb,
            defs,
            types: value_types(func),
            param_at,
            entering,
            entry: at.get(&func.entry).copied(),
            budget: std::cell::Cell::new(INTERVAL_STEPS),
        }
    }

    fn width(&self, ty: &Ty) -> Option<u32> {
        if *ty == Ty::Bool {
            return Some(1);
        }
        int_shape(ty, self.pb).map(|(w, _)| w).or(matches!(
            ty,
            Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
        )
        .then_some(self.pb))
    }

    fn konst(&self, v: ValueId) -> Option<Span> {
        match self.defs.get(&v)? {
            Inst::Const {
                ty,
                value: Constant::Int(k),
            } => {
                let w = self.width(ty)?;
                let k = (*k as u128) & low(w);
                Some(span(k, k, w))
            }
            Inst::Const {
                value: Constant::Bool(b),
                ..
            } => Some(span(u128::from(*b), u128::from(*b), 1)),
            _ => None,
        }
    }

    /// `v`'s unsigned interval from its definition.
    fn interval(&self, v: ValueId, seen: &mut Vec<ValueId>) -> Option<Span> {
        if seen.len() > 64 || self.budget.get() == 0 {
            return None;
        }
        self.budget.set(self.budget.get() - 1);
        let w = self.width(self.types.get(&v)?)?;
        let all = Some(span(0, low(w), w));
        if let Some(&(b, j)) = self.param_at.get(&v) {
            // The call binds the entry's parameters as well as its edges.
            if self.entry.is_none_or(|e| e == b) {
                return all;
            }
            if seen.contains(&v) || self.entering[b].is_empty() {
                return None;
            }
            seen.push(v);
            let mut hull: Option<(u128, u128)> = None;
            let mut whole = false;
            for args in &self.entering[b] {
                match args.get(j).and_then(|a| self.interval(*a, seen)) {
                    Some(s) if s.w == w => {
                        hull = Some(hull.map_or((s.lo, s.hi), |(l, h)| (l.min(s.lo), h.max(s.hi))));
                    }
                    _ => whole = true,
                }
            }
            seen.pop();
            return match (whole, hull) {
                (false, Some((lo, hi))) => Some(span(lo, hi, w)),
                _ => all,
            };
        }
        if let Some(k) = self.konst(v) {
            return (k.w == w).then_some(k);
        }
        let of = |x: ValueId, seen: &mut Vec<ValueId>| self.interval(x, seen).filter(|s| s.w == w);
        let k = |x: ValueId| self.konst(x).filter(|s| s.w == w).map(|s| s.lo);
        let found = match self.defs.get(&v)? {
            Inst::Copy { operand, .. } => of(*operand, seen),
            Inst::Cast {
                op,
                src_ty,
                operand,
                ..
            } => {
                let sw = self.width(src_ty)?;
                match op {
                    CastOp::Bitcast | CastOp::PtrToPtr if sw == w => of(*operand, seen),
                    CastOp::ZExt if sw <= w => {
                        let s = self
                            .interval(*operand, seen)
                            .filter(|s| s.w == sw)
                            .unwrap_or(span(0, low(sw), sw));
                        Some(span(s.lo, s.hi, w))
                    }
                    CastOp::Trunc if sw >= w => self
                        .interval(*operand, seen)
                        .filter(|s| s.hi <= low(w))
                        .map(|s| span(s.lo, s.hi, w)),
                    _ => None,
                }
            }
            Inst::BinOp { op, lhs, rhs, .. } => match op {
                BinOp::And => k(*lhs).or(k(*rhs)).map(|c| span(0, c, w)),
                BinOp::URem => k(*rhs).filter(|c| *c > 0).map(|c| span(0, c - 1, w)),
                BinOp::UDiv => k(*rhs)
                    .filter(|c| *c > 0)
                    .and_then(|c| of(*lhs, seen).map(|s| span(s.lo / c, s.hi / c, w))),
                BinOp::LShr => k(*rhs)
                    .filter(|c| *c < u128::from(w))
                    .and_then(|c| of(*lhs, seen).map(|s| span(s.lo >> c, s.hi >> c, w))),
                BinOp::Mul => {
                    let (c, x) = match (k(*lhs), k(*rhs)) {
                        (Some(c), _) => (c, *rhs),
                        (_, Some(c)) => (c, *lhs),
                        _ => return all,
                    };
                    of(x, seen).and_then(|s| {
                        let top = s.hi.checked_mul(c).filter(|t| *t <= low(w))?;
                        Some(span(s.lo * c, top, w))
                    })
                }
                BinOp::Add => match (of(*lhs, seen), of(*rhs, seen)) {
                    (Some(a), Some(b)) => {
                        a.hi.checked_add(b.hi)
                            .filter(|t| *t <= low(w))
                            .map(|t| span(a.lo + b.lo, t, w))
                    }
                    _ => None,
                },
                BinOp::Sub => k(*rhs).and_then(|c| {
                    of(*lhs, seen)
                        .filter(|s| s.lo >= c)
                        .map(|s| span(s.lo - c, s.hi - c, w))
                }),
                _ => None,
            },
            Inst::Select {
                then_val, else_val, ..
            } => match (of(*then_val, seen), of(*else_val, seen)) {
                (Some(a), Some(b)) => Some(span(a.lo.min(b.lo), a.hi.max(b.hi), w)),
                _ => None,
            },
            Inst::ICmp { .. } => Some(span(0, 1, 1)),
            _ => None,
        };
        found.or(all)
    }
}

/// `pred` on two spans of width `w`, when they decide it.
fn decide(pred: ICmpOp, a: Span, b: Span, w: u32) -> Option<bool> {
    if a.lo == a.hi && b.lo == b.hi {
        let s = |r: u128| -> i128 {
            if w >= 128 {
                r as i128
            } else {
                let k = 128 - w;
                ((r << k) as i128) >> k
            }
        };
        let (x, y) = (a.lo, b.lo);
        return Some(match pred {
            ICmpOp::Eq => x == y,
            ICmpOp::Ne => x != y,
            ICmpOp::Ult => x < y,
            ICmpOp::Ule => x <= y,
            ICmpOp::Ugt => x > y,
            ICmpOp::Uge => x >= y,
            ICmpOp::Slt => s(x) < s(y),
            ICmpOp::Sle => s(x) <= s(y),
            ICmpOp::Sgt => s(x) > s(y),
            ICmpOp::Sge => s(x) >= s(y),
        });
    }
    let sign = 1u128 << (w.max(1) - 1);
    let p = match pred {
        ICmpOp::Slt | ICmpOp::Sle | ICmpOp::Sgt | ICmpOp::Sge if a.hi >= sign || b.hi >= sign => {
            return None;
        }
        ICmpOp::Slt => ICmpOp::Ult,
        ICmpOp::Sle => ICmpOp::Ule,
        ICmpOp::Sgt => ICmpOp::Ugt,
        ICmpOp::Sge => ICmpOp::Uge,
        other => other,
    };
    match p {
        ICmpOp::Ult => (a.hi < b.lo)
            .then_some(true)
            .or((a.lo >= b.hi).then_some(false)),
        ICmpOp::Ule => (a.hi <= b.lo)
            .then_some(true)
            .or((a.lo > b.hi).then_some(false)),
        ICmpOp::Ugt => (a.lo > b.hi)
            .then_some(true)
            .or((a.hi <= b.lo).then_some(false)),
        ICmpOp::Uge => (a.lo >= b.hi)
            .then_some(true)
            .or((a.hi < b.lo).then_some(false)),
        ICmpOp::Eq | ICmpOp::Ne => (a.hi < b.lo || b.hi < a.lo).then_some(pred == ICmpOp::Ne),
        _ => None,
    }
}

/// The header's values on one visit: induction variables known, the rest
/// evaluated on demand.
struct OnVisit<'r, 'f> {
    r: &'r Ranges<'f>,
    header: BlockId,
    body: &'r HashSet<BlockId>,
    def_at: &'r HashMap<ValueId, BlockId>,
    known: HashMap<ValueId, Span>,
}

impl OnVisit<'_, '_> {
    fn get(&self, v: ValueId, depth: usize) -> Option<Span> {
        if depth > 64 {
            return None;
        }
        if let Some(s) = self.known.get(&v) {
            return Some(*s);
        }
        let at = *self.def_at.get(&v)?;
        if !self.body.contains(&at) {
            return self.r.interval(v, &mut Vec::new());
        }
        if at != self.header {
            return None;
        }
        let pb = self.r.pb;
        let word = |ty: &Ty| int_shape(ty, pb).is_some_and(|(w, _)| w == pb);
        let get = |x: ValueId| self.get(x, depth + 1);
        match self.r.defs.get(&v)? {
            Inst::Const { .. } => self.r.konst(v),
            Inst::NullPtr => Some(span(0, 0, pb)),
            Inst::Copy { operand, .. } => get(*operand),
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => {
                let (sw, dw) = (self.r.width(src_ty)?, self.r.width(dst_ty)?);
                let x = get(*operand).filter(|s| s.w == sw)?;
                match op {
                    CastOp::ZExt if dw >= sw => Some(span(x.lo, x.hi, dw)),
                    CastOp::Trunc if dw <= sw && x.hi <= low(dw) => Some(span(x.lo, x.hi, dw)),
                    CastOp::Bitcast if dw == sw && int_shape(src_ty, pb).is_some() => Some(x),
                    CastOp::PtrToPtr => Some(x),
                    CastOp::IntToPtr if word(src_ty) => Some(x),
                    CastOp::PtrToInt if word(dst_ty) => Some(x),
                    CastOp::PtrToInt if dw > pb => Some(span(x.lo, x.hi, dw)),
                    _ => None,
                }
            }
            Inst::ICmp { op, ty, lhs, rhs } => {
                let w = self.r.width(ty)?;
                let (a, b) = (get(*lhs)?, get(*rhs)?);
                if a.w != w || b.w != w {
                    return None;
                }
                decide(*op, a, b, w).map(|t| span(u128::from(t), u128::from(t), 1))
            }
            Inst::Select {
                cond,
                then_val,
                else_val,
                ..
            } => match get(*cond)? {
                Span { lo: 1, hi: 1, w: 1 } => get(*then_val),
                Span { lo: 0, hi: 0, w: 1 } => get(*else_val),
                _ => None,
            },
            Inst::BinOp { op, ty, lhs, rhs } => {
                let w = int_shape(ty, pb)?.0;
                let (a, b) = (get(*lhs)?, get(*rhs)?);
                if a.w != w || b.w != w || a.lo != a.hi || b.lo != b.hi {
                    return None;
                }
                let (x, y) = (a.lo, b.lo);
                let k = || u32::try_from(y).ok().filter(|k| *k < w);
                let r = match op {
                    BinOp::Add => x.wrapping_add(y),
                    BinOp::Sub => x.wrapping_sub(y),
                    BinOp::Mul => x.wrapping_mul(y),
                    BinOp::And => x & y,
                    BinOp::Or => x | y,
                    BinOp::Xor => x ^ y,
                    BinOp::Shl => x << k()?,
                    BinOp::LShr => x >> k()?,
                    _ => return None,
                } & low(w);
                Some(span(r, r, w))
            }
            _ => None,
        }
    }
}

/// The edge `term` takes on the scrutinee `s`.
fn taken(term: &Inst, s: Span) -> Option<(BlockId, Vec<ValueId>)> {
    if s.lo != s.hi {
        return None;
    }
    match term {
        Inst::CondBr {
            then_target,
            then_args,
            else_target,
            else_args,
            ..
        } if s.w == 1 => Some(if s.lo == 1 {
            (*then_target, then_args.clone())
        } else {
            (*else_target, else_args.clone())
        }),
        Inst::Switch {
            default,
            default_args,
            cases,
            ..
        } => {
            for case in cases {
                let Constant::Int(k) = case.value else {
                    return None;
                };
                if (k as u128) & low(s.w) == s.lo {
                    return Some((case.target, case.args.clone()));
                }
            }
            Some((*default, default_args.clone()))
        }
        _ => None,
    }
}

impl MidPass for BoundedUnroll {
    fn name(&self) -> &'static str {
        BOUNDED_UNROLL_NAME
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let mut cur = func.clone();
        let mut next_value = first_free_value(func);
        let mut next_block = func.blocks.iter().map(|b| b.id.index() + 1).max()?;
        let mut loops = Vec::new();
        for _ in 0..16 {
            let mut done = None;
            for lp in rewritable_loops(&cur) {
                if let Some(out) = bounded(&cur, cx, &lp, next_value, next_block) {
                    done = Some(out);
                    break;
                }
            }
            let Some((out, claim)) = done else {
                break;
            };
            next_value += u32::try_from(claim.values.len()).ok()?;
            next_block += u32::try_from(claim.blocks.len()).ok()?;
            cur = out;
            loops.push(claim);
        }
        if loops.is_empty() {
            return None;
        }
        Some((
            cur,
            PassWitness::BoundedUnroll(BoundedUnrollWitness { loops }),
        ))
    }
}

/// `lp` unrolled to its bound, or `None`.
fn bounded(
    func: &Function,
    cx: &PassContext<'_>,
    lp: &Loop,
    next_value: u32,
    next_block: u32,
) -> Option<(Function, BoundedUnrollLoop)> {
    if lp.back_edges != 1 || inner_cycle(func, lp) {
        return None;
    }
    let pos = |id: BlockId| func.blocks.iter().position(|b| b.id == id);
    let h = pos(lp.header)?;
    let def_at = def_blocks(func);
    let types = value_types_with_overflow(func);
    let in_loop = |id: BlockId| lp.body.contains(&id);
    // ---- Terminators, allocations, the latch.
    let mut latch = None;
    for block in func.blocks.iter().filter(|b| in_loop(b.id)) {
        let last = &block.body.last()?.inst;
        if !matches!(
            last,
            Inst::Br { .. }
                | Inst::CondBr { .. }
                | Inst::Switch { .. }
                | Inst::Return { .. }
                | Inst::Unreachable
        ) || block
            .body
            .iter()
            .any(|n| matches!(n.inst, Inst::Alloca { .. }))
        {
            return None;
        }
        if last.successor_edges().iter().any(|e| e.target == lp.header) {
            latch = Some(block.id);
        }
    }
    let latch = latch?;
    let term = func.blocks[h].body.last()?.inst.clone();
    if !matches!(term, Inst::CondBr { .. } | Inst::Switch { .. }) {
        return None;
    }
    let edges = term.successor_edges();
    if !edges.iter().any(|e| in_loop(e.target)) || edges.iter().all(|e| in_loop(e.target)) {
        return None;
    }
    // ---- Exit blocks; no other use of the loop's values outside it.
    let mut entering: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for block in &func.blocks {
        if let Some(last) = block.body.last() {
            for e in last.inst.successor_edges() {
                entering.entry(e.target).or_default().push(block.id);
            }
        }
    }
    let mut exits: HashSet<BlockId> = HashSet::new();
    for block in func
        .blocks
        .iter()
        .filter(|b| !in_loop(b.id) && b.id != func.entry)
    {
        let Some([from]) = entering.get(&block.id).map(Vec::as_slice) else {
            continue;
        };
        if !in_loop(*from) {
            continue;
        }
        let Some(last) = block.body.last() else {
            continue;
        };
        let leaves = matches!(
            last.inst,
            Inst::Br { .. }
                | Inst::CondBr { .. }
                | Inst::Switch { .. }
                | Inst::Return { .. }
                | Inst::Unreachable
        ) && last
            .inst
            .successor_edges()
            .iter()
            .all(|e| !in_loop(e.target));
        let mut reads = false;
        for node in &block.body {
            node.inst.visit_value_operands(|v| {
                reads |= def_at.get(&v).is_some_and(|d| in_loop(*d));
            });
        }
        let own: HashSet<ValueId> = block
            .params
            .iter()
            .map(|(v, _)| *v)
            .chain(block.body.iter().flat_map(|n| n.results.iter().copied()))
            .collect();
        let elsewhere = func.blocks.iter().filter(|b| b.id != block.id).any(|b| {
            b.body.iter().any(|n| {
                let mut hit = false;
                n.inst.visit_value_operands(|v| hit |= own.contains(&v));
                hit
            })
        });
        if leaves && reads && !elsewhere {
            exits.insert(block.id);
        }
    }
    for block in func
        .blocks
        .iter()
        .filter(|b| !in_loop(b.id) && !exits.contains(&b.id))
    {
        for node in &block.body {
            let mut leak = false;
            node.inst
                .visit_value_operands(|v| leak |= def_at.get(&v).is_some_and(|d| in_loop(*d)));
            if leak {
                return None;
            }
        }
    }
    // ---- Arguments and induction variables.
    let pre = pos(lp.preheader)?;
    let Inst::Br { args: init, .. } = &func.blocks[pre].body.last()?.inst else {
        return None;
    };
    let back: Vec<ValueId> = func.blocks[pos(latch)?]
        .body
        .last()?
        .inst
        .successor_edges()
        .into_iter()
        .find(|e| e.target == lp.header)?
        .args
        .to_vec();
    let params: Vec<(ValueId, Ty)> = func.blocks[h].params.clone();
    if init.len() != params.len()
        || back.len() != params.len()
        || params
            .iter()
            .enumerate()
            .any(|(j, (_, ty))| types.get(&init[j]) != Some(ty) || types.get(&back[j]) != Some(ty))
    {
        return None;
    }
    let mut nodes: HashMap<ValueId, &Inst> = HashMap::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        if let [r] = node.results.as_slice() {
            nodes.insert(*r, &node.inst);
        }
    }
    let lins = Lins {
        func,
        pointer_bits: cx.pointer_bits,
        nodes,
        def_at: def_at.clone(),
        body: &lp.body,
        params: params.iter().map(|(v, _)| *v).collect(),
        types: types.clone(),
    };
    let ivs: Vec<Option<(Lin, u128)>> = (0..params.len())
        .map(|j| {
            let step = lins.lin(back[j], 0)?;
            let start = lins.lin(init[j], 0)?;
            (step.root == LinRoot::Param(j)
                && start.bits == step.bits
                && !matches!(start.root, LinRoot::Param(_)))
            .then_some((start, step.off))
        })
        .collect();
    // ---- The bound.
    let ranges = Ranges::new(func, cx.pointer_bits);
    let scrutinee = match &term {
        Inst::CondBr { cond, .. } => *cond,
        Inst::Switch { value, .. } => *value,
        _ => return None,
    };
    let mut found = None;
    for k in 1..=POLICY_BOUND {
        let known: HashMap<ValueId, Span> = params
            .iter()
            .enumerate()
            .filter_map(|(j, (p, _))| {
                let (start, step) = ivs[j]?;
                (start.root == LinRoot::Const).then(|| {
                    let v =
                        start.off.wrapping_add(u128::from(k).wrapping_mul(step)) & low(start.bits);
                    (*p, span(v, v, start.bits))
                })
            })
            .collect();
        let visit = OnVisit {
            r: &ranges,
            header: lp.header,
            body: &lp.body,
            def_at: &def_at,
            known,
        };
        if let Some(edge) = visit.get(scrutinee, 0).and_then(|s| taken(&term, s))
            && !in_loop(edge.0)
        {
            found = Some((k, edge));
            break;
        }
    }
    let (bound, (exit_target, exit_args)) = found?;
    let n = bound as usize;
    // ---- Policy.
    let size: usize = func
        .blocks
        .iter()
        .filter(|b| in_loop(b.id) || exits.contains(&b.id))
        .map(|b| b.body.len())
        .sum();
    let cost = copy_cost(func, lp, &ivs, &params);
    if n * size > MAX_UNROLLED_INSTS || n * cost.unfolded_insts > POLICY_INSTS || cost.heavy > 0 {
        return None;
    }
    let mut typed = types.clone();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        if let Inst::Call { callee, .. } = &node.inst
            && let Some(sig) = cx
                .module
                .function_by_id(*callee)
                .and_then(|f| cx.module.func_type(f.ty))
            && sig.returns.len() == node.results.len()
        {
            for (value, ty) in node.results.iter().zip(&sig.returns) {
                typed.insert(*value, ty.clone());
            }
        }
    }
    let others: Vec<usize> = func
        .blocks
        .iter()
        .enumerate()
        .filter(|(i, b)| in_loop(b.id) && *i != h)
        .map(|(i, _)| i)
        .chain(
            func.blocks
                .iter()
                .enumerate()
                .filter(|(_, b)| exits.contains(&b.id))
                .map(|(i, _)| i),
        )
        .collect();
    for &bi in std::iter::once(&h).chain(&others) {
        if !func.blocks[bi]
            .body
            .iter()
            .all(|n| clean(cx.module, func, cx.pointer_bits, &n.inst, &typed))
        {
            return None;
        }
    }
    // ---- The copies.
    let per_copy = 1 + others.len();
    let blocks: Vec<BlockId> = (0..n * per_copy)
        .map(|i| BlockId::new(next_block + i as u32))
        .collect();
    let mut fresh = next_value;
    let mut values: Vec<ValueId> = Vec::new();
    let mut out_blocks: Vec<Block> = Vec::new();
    let mut last_map: HashMap<ValueId, ValueId> = HashMap::new();
    for k in 0..n {
        let name = |m: &HashMap<ValueId, ValueId>, v: ValueId| m.get(&v).copied().unwrap_or(v);
        let mut map: HashMap<ValueId, ValueId> = HashMap::new();
        for (j, (p, _)) in params.iter().enumerate() {
            let v = if k == 0 {
                init[j]
            } else {
                name(&last_map, back[j])
            };
            map.insert(*p, v);
        }
        let mut take = |m: &mut HashMap<ValueId, ValueId>, r: ValueId| {
            let v = ValueId::new(fresh);
            fresh += 1;
            values.push(v);
            m.insert(r, v);
        };
        for node in &func.blocks[h].body {
            for r in &node.results {
                take(&mut map, *r);
            }
        }
        for &bi in &others {
            let block = &func.blocks[bi];
            for (p, _) in &block.params {
                take(&mut map, *p);
            }
            for node in &block.body {
                for r in &node.results {
                    take(&mut map, *r);
                }
            }
        }
        let last = k + 1 == n;
        let next_head = if last {
            lp.header
        } else {
            blocks[(k + 1) * per_copy]
        };
        let here = |id: BlockId| -> BlockId {
            match others.iter().position(|&bi| func.blocks[bi].id == id) {
                Some(j) => blocks[k * per_copy + 1 + j],
                None => id,
            }
        };
        let to = |id: BlockId| {
            if id == lp.header { next_head } else { here(id) }
        };
        let clear = (!last).then_some(lp.header);
        let copy_block = |block: &Block| -> Vec<InstrNode> {
            block
                .body
                .iter()
                .map(|node| {
                    let mut c = node.clone();
                    trust_ir::mem2reg::rewrite_node(&mut c, &map);
                    if c.inst.is_terminator() {
                        redirect(&mut c.inst, &to, clear);
                    }
                    c
                })
                .collect()
        };
        out_blocks.push(Block {
            id: blocks[k * per_copy],
            params: Vec::new(),
            body: copy_block(&func.blocks[h]),
        });
        for &bi in &others {
            let block = &func.blocks[bi];
            out_blocks.push(Block {
                id: here(block.id),
                params: block
                    .params
                    .iter()
                    .map(|(p, t)| (name(&map, *p), t.clone()))
                    .collect(),
                body: copy_block(block),
            });
        }
        last_map = map;
    }
    // ---- The preheader, the header, the removed blocks.
    let mut out = func.clone();
    if let Some(t) = out.blocks[pre].body.last_mut() {
        t.inst = Inst::Br {
            target: blocks[0],
            args: Vec::new(),
        };
    }
    if let Some(t) = out.blocks[h].body.last_mut() {
        t.inst = Inst::Br {
            target: exit_target,
            args: exit_args,
        };
    }
    let removed_blocks: HashSet<BlockId> = others
        .iter()
        .map(|&bi| func.blocks[bi].id)
        .filter(|id| *id != exit_target || !exits.contains(id))
        .collect();
    let mut removed: HashSet<ValueId> = HashSet::new();
    for block in func
        .blocks
        .iter()
        .filter(|b| removed_blocks.contains(&b.id))
    {
        removed.extend(block.params.iter().map(|(v, _)| *v));
        for node in &block.body {
            removed.extend(node.results.iter().copied());
        }
    }
    out.blocks.retain(|b| !removed_blocks.contains(&b.id));
    let at = out.blocks.iter().position(|b| b.id == lp.header)?;
    out.blocks.splice(at..at, out_blocks);
    drop_names(&mut out, &removed);
    Some((
        out,
        BoundedUnrollLoop {
            header: lp.header,
            bound,
            blocks,
            values,
        },
    ))
}
