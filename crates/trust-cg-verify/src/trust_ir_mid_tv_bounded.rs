// trust-cg-verify/trust_ir_mid_tv_bounded.rs - the interval-bounded unrolling checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The checker of the mid-end's interval-bounded unrolling
//! ([`BoundedUnrollWitness`]): a loop whose trip count is not a constant but
//! is at most a constant `B` (`min_zip2`'s `min(k % 5, 4)` trips) becomes
//! `B` copies of its iterations, each keeping its own exit test, and one
//! last visit of the header that leaves. Everything is derived here from the
//! SOURCE function with this module's own code (the loop's shape and the
//! affine reading of its header's parameters are the full-unrolling
//! checker's, `trust_ir_mid_tv_unroll.rs`); the witness names the header,
//! the bound and the fresh blocks and values.
//!
//! **The loop** is the natural loop of the named header `H` with one back
//! edge, from the LATCH, whose blocks other than `H` form no cycle, every
//! block of which ends in `br`, `condbr`, `switch`, `ret` or `unreachable`,
//! and whose header ends in `condbr` or `switch` with at least one edge
//! leaving the loop and one staying in it. An EXIT BLOCK is a block outside
//! the loop, not the entry, entered by exactly one edge, from a block of
//! the loop (the header included), that ends in one of those terminators
//! with no edge back into the loop, reads a value of the loop, and whose
//! own values no other block reads; each copy takes its own. No value of
//! the loop may be read anywhere else outside it: the copies leave from
//! different places, so no single definition would dominate such a use.
//!
//! **The bound.** The header's parameters evolve as in full unrolling: one
//! whose back-edge argument reads as itself plus `s` holds `init + k * s`
//! on visit `k` (`init` the preheader's argument read as affine). On visit
//! `B` the header's terminator is evaluated: a parameter that evolves from
//! a constant start is its value on that visit; a value defined outside the
//! loop is known by its INTERVAL (below); an instruction of the header is
//! evaluated on its operands (constants, `copy`, integer `zext`, `trunc`
//! and same-width `bitcast`, address casts at the pointer width,
//! `ptrtoint` to a wider integer, `null`, integer arithmetic on known
//! operands, `select` on a known condition, and `icmp`, decided when both
//! operands are known or their intervals decide it, the signed predicates
//! only on intervals below the sign bit). The terminator must take an edge
//! leaving the loop. The source therefore leaves the loop no later than on
//! visit `B`, so `B` copies hold every iteration it can run.
//!
//! **Intervals** (unsigned, at the value's width), from definitions: a
//! constant; `copy`, same-width `bitcast` and `ptrtoptr` keep it; `zext`
//! keeps it (a value without one: its source type's range); `trunc` keeps
//! one that fits; `and` with a constant is at most the constant; `urem` by
//! a constant `c > 0` is below `c`; `udiv` and `lshr` by a constant divide
//! both ends; `mul` by a constant and `add` that cannot wrap, `sub` of a
//! constant that cannot borrow; `select` is the hull of its arms; `icmp` is
//! `[0, 1]`; a block parameter is the hull of every argument its entering
//! edges pass (a parameter met again while its own interval is derived has
//! none), except that a parameter of the function's entry block has its
//! type's whole range: the call enters the entry too, with arguments no
//! edge names. Each holds wherever the value is read: the function is SSA.
//!
//! **The rewrite.** With `B1..Bm` the loop's blocks other than `H` in
//! layout order followed by the exit blocks in layout order, copy `k` (`k <
//! B`) is `H_k`, `B1_k..Bm_k`. `H`'s parameters are substituted (copy 0 by
//! the preheader's arguments, copy `k + 1` by the back edge's as copy `k`
//! names them, each of the parameter's type). `H_k` holds all of `H`'s
//! instructions, renamed, its terminator included: an edge into the loop
//! goes to copy `k` of its target (to `H_(k+1)`, or `H` from the last copy,
//! when it is the back edge), an edge to an exit block to copy `k` of it,
//! any other edge to its target, arguments renamed. The other copied blocks
//! are full unrolling's. The preheader branches to `H_0`; `H` keeps its
//! parameters and instructions, runs on the last copy's back-edge
//! arguments, and ends in `br` along the edge its terminator was shown to
//! take on visit `B`; the loop's other blocks and every exit block but that
//! edge's target go. The copies come before `H`, in order, under the
//! witness's fresh names (per copy: `H_k`, then each `Bj_k`; per copy the
//! values of `H_k`'s instructions, then each `Bj_k`'s parameters and
//! results).
//!
//! Exact: every iteration the source runs is a copy executing the same
//! instructions on the same values, every exit test is still made, and the
//! only branch the rewrite removed is the one shown to leave.

use std::collections::{HashMap, HashSet};

use trust_ir::{
    BinOp, Block, BlockId, CastOp, Constant, Function, ICmpOp, Inst, InstrNode, Ty, ValueId,
};

use super::loops::{def_blocks, loop_shape, refuse, value_types};
use super::unroll::{Reader, Root, admitted_terminator, mask, retarget};
use super::{
    MidTvError, WitnessVerdict, block_positions, drop_names, incoming_edges, int_shape, used_values,
};

/// The largest bound this checker accepts.
pub const MAX_BOUNDED_TRIPS: u32 = 16;

/// One loop at `header` replaced by `bound` copies of its iterations with
/// their exit tests; the copies' blocks and values take `blocks` and
/// `values` in the order the module docs fix.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoundedUnrollLoop {
    pub header: BlockId,
    pub bound: u32,
    pub blocks: Vec<BlockId>,
    pub values: Vec<ValueId>,
}

/// Interval-bounded unrolling's claim, applied loop by loop.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct BoundedUnrollWitness {
    pub loops: Vec<BoundedUnrollLoop>,
}

impl BoundedUnrollWitness {
    /// Loops unrolled.
    pub fn rewrite_count(&self) -> usize {
        self.loops.len()
    }
}

/// An abstract value on the bound's visit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Abs {
    Known(u128, u32),
    Range(u128, u128, u32),
}

impl Abs {
    fn width(self) -> u32 {
        match self {
            Abs::Known(_, w) | Abs::Range(_, _, w) => w,
        }
    }

    fn bounds(self) -> (u128, u128) {
        match self {
            Abs::Known(k, _) => (k, k),
            Abs::Range(lo, hi, _) => (lo, hi),
        }
    }
}

fn range(lo: u128, hi: u128, w: u32) -> Abs {
    if lo == hi {
        Abs::Known(lo, w)
    } else {
        Abs::Range(lo, hi, w)
    }
}

/// The interval derivation and the visit-`B` evaluation over one function.
struct Facts<'f> {
    func: &'f Function,
    pointer_bits: u32,
    defs: HashMap<ValueId, (usize, usize)>,
    types: HashMap<ValueId, Ty>,
    /// Each block parameter: its block's position and its index.
    params: HashMap<ValueId, (usize, usize)>,
    /// Each block's entering edges' arguments.
    incoming: Vec<Vec<Vec<ValueId>>>,
    /// The entry block's position: the call also enters it.
    entry: Option<usize>,
    /// Derivation steps left ([`INTERVAL_STEPS`]); none left is no interval.
    budget: std::cell::Cell<usize>,
}

/// The derivation steps one check's intervals may take: a definition DAG
/// with shared operands is otherwise walked once per path.
const INTERVAL_STEPS: usize = 16_384;

impl<'f> Facts<'f> {
    fn new(func: &'f Function, pointer_bits: u32) -> Self {
        let positions = block_positions(func);
        let mut defs = HashMap::new();
        let mut params = HashMap::new();
        let mut incoming = vec![Vec::new(); func.blocks.len()];
        for (bi, block) in func.blocks.iter().enumerate() {
            for (j, (p, _)) in block.params.iter().enumerate() {
                params.insert(*p, (bi, j));
            }
            for (ni, node) in block.body.iter().enumerate() {
                if let [r] = node.results.as_slice() {
                    defs.entry(*r).or_insert((bi, ni));
                }
            }
            if let Some(last) = block.body.last() {
                for edge in last.inst.successor_edges() {
                    if let Some(&t) = positions.get(&edge.target) {
                        incoming[t].push(edge.args.to_vec());
                    }
                }
            }
        }
        Self {
            func,
            pointer_bits,
            defs,
            types: value_types(func),
            params,
            incoming,
            entry: positions.get(&func.entry).copied(),
            budget: std::cell::Cell::new(INTERVAL_STEPS),
        }
    }

    fn inst(&self, v: ValueId) -> Option<&'f Inst> {
        let &(b, n) = self.defs.get(&v)?;
        Some(&self.func.blocks[b].body[n].inst)
    }

    fn width(&self, ty: &Ty) -> Option<u32> {
        if *ty == Ty::Bool {
            return Some(1);
        }
        int_shape(ty, self.pointer_bits)
            .map(|(w, _)| w)
            .or(matches!(
                ty,
                Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
            )
            .then_some(self.pointer_bits))
    }

    fn int_const(&self, v: ValueId) -> Option<(u128, u32)> {
        match self.inst(v)? {
            Inst::Const {
                ty,
                value: Constant::Int(k),
            } => {
                let w = self.width(ty)?;
                Some(((*k as u128) & mask(w), w))
            }
            Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(b),
            } => Some((u128::from(*b), 1)),
            _ => None,
        }
    }

    /// `v`'s interval (module docs); `stack` holds the parameters being
    /// derived.
    fn interval(&self, v: ValueId, stack: &mut Vec<ValueId>) -> Option<Abs> {
        if stack.len() > 64 || self.budget.get() == 0 {
            return None;
        }
        self.budget.set(self.budget.get() - 1);
        let w = self.width(self.types.get(&v)?)?;
        let full = || Some(Abs::Range(0, mask(w), w));
        if let Some(&(b, j)) = self.params.get(&v) {
            // The call binds the entry's parameters as well as its edges.
            if self.entry.is_none_or(|e| e == b) {
                return full();
            }
            if stack.contains(&v) {
                return None;
            }
            stack.push(v);
            let mut hull: Option<(u128, u128)> = None;
            let mut ok = !self.incoming[b].is_empty();
            for args in &self.incoming[b] {
                let Some(arg) = args.get(j) else {
                    ok = false;
                    break;
                };
                match self.interval(*arg, stack) {
                    Some(a) if a.width() == w => {
                        let (lo, hi) = a.bounds();
                        hull = Some(hull.map_or((lo, hi), |(l, h)| (l.min(lo), h.max(hi))));
                    }
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            stack.pop();
            return match (ok, hull) {
                (true, Some((lo, hi))) => Some(range(lo, hi, w)),
                _ => full(),
            };
        }
        if let Some((k, kw)) = self.int_const(v) {
            return (kw == w).then_some(Abs::Known(k, w));
        }
        let sub = |x: ValueId, stack: &mut Vec<ValueId>| self.interval(x, stack);
        let derived = match self.inst(v)? {
            Inst::Copy { operand, .. } => sub(*operand, stack).filter(|a| a.width() == w),
            Inst::Cast {
                op,
                src_ty,
                operand,
                ..
            } => {
                let sw = self.width(src_ty)?;
                match op {
                    CastOp::Bitcast | CastOp::PtrToPtr if sw == w => {
                        sub(*operand, stack).filter(|a| a.width() == w)
                    }
                    CastOp::ZExt if sw <= w => {
                        let (lo, hi) = sub(*operand, stack)
                            .filter(|a| a.width() == sw)
                            .map_or((0, mask(sw)), Abs::bounds);
                        Some(range(lo, hi, w))
                    }
                    CastOp::Trunc if sw >= w => sub(*operand, stack)
                        .filter(|a| a.bounds().1 <= mask(w))
                        .map(|a| range(a.bounds().0, a.bounds().1, w)),
                    _ => None,
                }
            }
            Inst::BinOp { op, lhs, rhs, .. } => {
                let k = |x: ValueId| self.int_const(x).filter(|(_, kw)| *kw == w).map(|(k, _)| k);
                let interval_of = |x: ValueId, stack: &mut Vec<ValueId>| {
                    sub(x, stack).filter(|a| a.width() == w).map(Abs::bounds)
                };
                match op {
                    BinOp::And => match (k(*lhs), k(*rhs)) {
                        (Some(c), _) | (_, Some(c)) => Some(range(0, c, w)),
                        _ => None,
                    },
                    BinOp::URem => k(*rhs).filter(|c| *c > 0).map(|c| range(0, c - 1, w)),
                    BinOp::UDiv => match k(*rhs).filter(|c| *c > 0) {
                        Some(c) => {
                            interval_of(*lhs, stack).map(|(lo, hi)| range(lo / c, hi / c, w))
                        }
                        None => None,
                    },
                    BinOp::LShr => match k(*rhs).filter(|c| *c < u128::from(w)) {
                        Some(c) => {
                            interval_of(*lhs, stack).map(|(lo, hi)| range(lo >> c, hi >> c, w))
                        }
                        None => None,
                    },
                    BinOp::Mul => {
                        let (c, x) = match (k(*lhs), k(*rhs)) {
                            (Some(c), _) => (c, *rhs),
                            (_, Some(c)) => (c, *lhs),
                            _ => return full(),
                        };
                        interval_of(x, stack).and_then(|(lo, hi)| {
                            let top = hi.checked_mul(c).filter(|t| *t <= mask(w))?;
                            Some(range(lo * c, top, w))
                        })
                    }
                    BinOp::Add => {
                        let a = interval_of(*lhs, stack);
                        let b = interval_of(*rhs, stack);
                        match (a, b) {
                            (Some((al, ah)), Some((bl, bh))) => ah
                                .checked_add(bh)
                                .filter(|t| *t <= mask(w))
                                .map(|t| range(al + bl, t, w)),
                            _ => None,
                        }
                    }
                    BinOp::Sub => match k(*rhs) {
                        Some(c) => interval_of(*lhs, stack)
                            .filter(|(lo, _)| *lo >= c)
                            .map(|(lo, hi)| range(lo - c, hi - c, w)),
                        None => None,
                    },
                    _ => None,
                }
            }
            Inst::Select {
                then_val, else_val, ..
            } => {
                let a = sub(*then_val, stack).filter(|a| a.width() == w);
                let b = sub(*else_val, stack).filter(|a| a.width() == w);
                match (a, b) {
                    (Some(a), Some(b)) => {
                        let ((al, ah), (bl, bh)) = (a.bounds(), b.bounds());
                        Some(range(al.min(bl), ah.max(bh), w))
                    }
                    _ => None,
                }
            }
            Inst::ICmp { .. } => Some(Abs::Range(0, 1, 1)),
            _ => None,
        };
        derived.or_else(full)
    }
}

/// `pred` decided on two abstract operands of width `w`, or `None`.
fn compare(pred: ICmpOp, a: Abs, b: Abs, w: u32) -> Option<bool> {
    let ((al, ah), (bl, bh)) = (a.bounds(), b.bounds());
    if let (Abs::Known(x, _), Abs::Known(y, _)) = (a, b) {
        let sx = |r: u128| -> i128 {
            if w >= 128 {
                r as i128
            } else {
                let s = 128 - w;
                ((r << s) as i128) >> s
            }
        };
        return Some(match pred {
            ICmpOp::Eq => x == y,
            ICmpOp::Ne => x != y,
            ICmpOp::Ult => x < y,
            ICmpOp::Ule => x <= y,
            ICmpOp::Ugt => x > y,
            ICmpOp::Uge => x >= y,
            ICmpOp::Slt => sx(x) < sx(y),
            ICmpOp::Sle => sx(x) <= sx(y),
            ICmpOp::Sgt => sx(x) > sx(y),
            ICmpOp::Sge => sx(x) >= sx(y),
        });
    }
    // The signed predicates only below the sign bit, where they are the
    // unsigned ones.
    let half = if w >= 1 { 1u128 << (w - 1) } else { 0 };
    let unsigned = match pred {
        ICmpOp::Slt => ICmpOp::Ult,
        ICmpOp::Sle => ICmpOp::Ule,
        ICmpOp::Sgt => ICmpOp::Ugt,
        ICmpOp::Sge => ICmpOp::Uge,
        other => other,
    };
    if unsigned != pred && (ah >= half || bh >= half) {
        return None;
    }
    match unsigned {
        ICmpOp::Ult if ah < bl => Some(true),
        ICmpOp::Ult if al >= bh => Some(false),
        ICmpOp::Ule if ah <= bl => Some(true),
        ICmpOp::Ule if al > bh => Some(false),
        ICmpOp::Ugt if al > bh => Some(true),
        ICmpOp::Ugt if ah <= bl => Some(false),
        ICmpOp::Uge if al >= bh => Some(true),
        ICmpOp::Uge if ah < bl => Some(false),
        ICmpOp::Eq | ICmpOp::Ne if ah < bl || bh < al => Some(pred == ICmpOp::Ne),
        _ => None,
    }
}

/// The header's values on visit `bound`: `params[j]` the parameters'
/// values where they evolve from a constant start.
struct Visit<'a, 'f> {
    facts: &'a Facts<'f>,
    header: usize,
    body: &'a HashSet<usize>,
    params: HashMap<ValueId, Abs>,
    memo: std::cell::RefCell<HashMap<ValueId, Option<Abs>>>,
}

impl Visit<'_, '_> {
    fn eval(&self, v: ValueId, depth: usize) -> Option<Abs> {
        if depth > 64 {
            return None;
        }
        if let Some(a) = self.params.get(&v) {
            return Some(*a);
        }
        if let Some(a) = self.memo.borrow().get(&v) {
            return *a;
        }
        let out = self.eval_uncached(v, depth);
        self.memo.borrow_mut().insert(v, out);
        out
    }

    fn eval_uncached(&self, v: ValueId, depth: usize) -> Option<Abs> {
        let f = self.facts;
        let at = match (f.defs.get(&v), f.params.get(&v)) {
            (Some((b, _)), _) => *b,
            (None, Some((b, _))) => *b,
            _ => return None,
        };
        if !self.body.contains(&at) {
            return f.interval(v, &mut Vec::new());
        }
        if at != self.header {
            return None;
        }
        let inst = f.inst(v)?;
        let get = |x: ValueId| self.eval(x, depth + 1);
        let pb = f.pointer_bits;
        let word = |ty: &Ty| int_shape(ty, pb).is_some_and(|(w, _)| w == pb);
        match inst {
            Inst::Const { .. } => f.int_const(v).map(|(k, w)| Abs::Known(k, w)),
            Inst::NullPtr => Some(Abs::Known(0, pb)),
            Inst::Copy { operand, .. } => get(*operand),
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => {
                let (sw, dw) = (f.width(src_ty)?, f.width(dst_ty)?);
                let x = get(*operand).filter(|a| a.width() == sw)?;
                let (lo, hi) = x.bounds();
                match op {
                    CastOp::ZExt if dw >= sw => Some(range(lo, hi, dw)),
                    CastOp::Trunc if dw <= sw && hi <= mask(dw) => Some(range(lo, hi, dw)),
                    CastOp::Bitcast if dw == sw && int_shape(src_ty, pb).is_some() => Some(x),
                    CastOp::PtrToPtr => Some(x),
                    CastOp::IntToPtr if word(src_ty) => Some(x),
                    CastOp::PtrToInt if word(dst_ty) => Some(x),
                    CastOp::PtrToInt if dw > pb => Some(range(lo, hi, dw)),
                    _ => None,
                }
            }
            Inst::ICmp { op, ty, lhs, rhs } => {
                let w = f.width(ty)?;
                let (a, b) = (get(*lhs)?, get(*rhs)?);
                if a.width() != w || b.width() != w {
                    return None;
                }
                compare(*op, a, b, w).map(|r| Abs::Known(u128::from(r), 1))
            }
            Inst::Select {
                cond,
                then_val,
                else_val,
                ..
            } => match get(*cond)? {
                Abs::Known(1, 1) => get(*then_val),
                Abs::Known(0, 1) => get(*else_val),
                _ => None,
            },
            Inst::BinOp { op, ty, lhs, rhs } => {
                let w = int_shape(ty, pb)?.0;
                let (Abs::Known(a, wa), Abs::Known(b, wb)) = (get(*lhs)?, get(*rhs)?) else {
                    return None;
                };
                if wa != w || wb != w {
                    return None;
                }
                let k = || u32::try_from(b).ok().filter(|k| *k < w);
                Some(Abs::Known(
                    match op {
                        BinOp::Add => a.wrapping_add(b),
                        BinOp::Sub => a.wrapping_sub(b),
                        BinOp::Mul => a.wrapping_mul(b),
                        BinOp::And => a & b,
                        BinOp::Or => a | b,
                        BinOp::Xor => a ^ b,
                        BinOp::Shl => a << k()?,
                        BinOp::LShr => a >> k()?,
                        _ => return None,
                    } & mask(w),
                    w,
                ))
            }
            _ => None,
        }
    }
}

/// The edge `term` takes when its scrutinee is `s`.
fn edge_of(term: &Inst, s: Abs) -> Option<(BlockId, Vec<ValueId>)> {
    let Abs::Known(raw, width) = s else {
        return None;
    };
    match term {
        Inst::CondBr {
            then_target,
            then_args,
            else_target,
            else_args,
            ..
        } if width == 1 => Some(if raw == 1 {
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
                if (k as u128) & mask(width) == raw {
                    return Some((case.target, case.args.clone()));
                }
            }
            Some((*default, default_args.clone()))
        }
        _ => None,
    }
}

pub(super) fn rebuild_bounded_unroll(
    pointer_bits: u32,
    source: &Function,
    witness: &BoundedUnrollWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let mut taken: HashSet<ValueId> = used_values(source);
    let mut blocks: HashSet<BlockId> = HashSet::new();
    for block in &source.blocks {
        blocks.insert(block.id);
        taken.extend(block.params.iter().map(|(v, _)| *v));
        for node in &block.body {
            taken.extend(node.results.iter().copied());
        }
    }
    if let Some(names) = &source.value_names {
        taken.extend(names.iter().map(|(v, _)| *v));
    }
    for lp in &witness.loops {
        for value in &lp.values {
            if !taken.insert(*value) {
                return Err(refuse(lp.header, format!("%{value} is not fresh")));
            }
        }
        for block in &lp.blocks {
            if !blocks.insert(*block) {
                return Err(refuse(lp.header, format!("block {block} is not fresh")));
            }
        }
    }
    let mut cur = source.clone();
    for lp in &witness.loops {
        bounded_unroll(&mut cur, pointer_bits, lp)?;
    }
    Ok((
        cur,
        WitnessVerdict {
            exact: witness.loops.len(),
            refinements: 0,
        },
    ))
}

/// Unroll the loop at `lp.header` in place.
fn bounded_unroll(
    cur: &mut Function,
    pointer_bits: u32,
    lp: &BoundedUnrollLoop,
) -> Result<(), MidTvError> {
    let header = lp.header;
    let shape = loop_shape(cur, header)?;
    if shape.back_edges != 1 {
        return Err(refuse(header, "the loop has more than one back edge"));
    }
    if lp.bound == 0 || lp.bound > MAX_BOUNDED_TRIPS {
        return Err(refuse(
            header,
            format!("the bound {} is not in 1..={MAX_BOUNDED_TRIPS}", lp.bound),
        ));
    }
    let positions = block_positions(cur);
    let h = shape.header;
    let in_body = |id: BlockId| positions.get(&id).is_some_and(|p| shape.body.contains(p));
    // ---- No inner cycle (a topological order of the other blocks).
    {
        let mut indegree: HashMap<usize, usize> = shape
            .body
            .iter()
            .filter(|b| **b != h)
            .map(|b| (*b, 0))
            .collect();
        let succs = |b: usize| -> Vec<usize> {
            cur.blocks[b]
                .body
                .last()
                .map(|t| t.inst.successor_edges())
                .unwrap_or_default()
                .iter()
                .filter_map(|e| positions.get(&e.target).copied())
                .filter(|t| *t != h && shape.body.contains(t))
                .collect()
        };
        for &b in indegree.clone().keys() {
            for s in succs(b) {
                *indegree.entry(s).or_default() += 1;
            }
        }
        let mut ready: Vec<usize> = indegree
            .iter()
            .filter(|(_, d)| **d == 0)
            .map(|(b, _)| *b)
            .collect();
        let mut seen = 0;
        while let Some(b) = ready.pop() {
            seen += 1;
            for s in succs(b) {
                if let Some(d) = indegree.get_mut(&s) {
                    *d -= 1;
                    if *d == 0 {
                        ready.push(s);
                    }
                }
            }
        }
        if seen != shape.body.len() - 1 {
            return Err(refuse(header, "the loop body has an inner cycle"));
        }
    }
    // ---- Terminators and the latch.
    let mut latch = None;
    for &b in &shape.body {
        let Some(last) = cur.blocks[b].body.last() else {
            return Err(refuse(header, "a loop block has no terminator"));
        };
        if !admitted_terminator(&last.inst) {
            return Err(refuse(
                header,
                format!(
                    "block {} ends in a terminator the copies cannot take",
                    cur.blocks[b].id
                ),
            ));
        }
        if last
            .inst
            .successor_edges()
            .iter()
            .any(|e| e.target == header)
        {
            latch = Some(b);
        }
    }
    let latch = latch.ok_or_else(|| refuse(header, "no back edge"))?;
    let term = cur.blocks[h]
        .body
        .last()
        .map(|n| n.inst.clone())
        .ok_or_else(|| refuse(header, "the header is empty"))?;
    if !matches!(term, Inst::CondBr { .. } | Inst::Switch { .. }) {
        return Err(refuse(
            header,
            "the header does not end in a condbr or switch",
        ));
    }
    {
        let edges = term.successor_edges();
        if !edges.iter().any(|e| in_body(e.target)) || edges.iter().all(|e| in_body(e.target)) {
            return Err(refuse(
                header,
                "the header's terminator does not both stay in and leave the loop",
            ));
        }
    }
    // ---- Exit blocks, and no other use of the loop's values outside it.
    let preds = incoming_edges(cur, &positions);
    let entry = positions[&cur.entry];
    let defs_at = def_blocks(cur);
    let mut exits: Vec<usize> = Vec::new();
    for (e, block) in cur.blocks.iter().enumerate() {
        if shape.body.contains(&e) || e == entry {
            continue;
        }
        let [from] = preds[e].as_slice() else {
            continue;
        };
        if !shape.body.contains(from) {
            continue;
        }
        let Some(last) = block.body.last() else {
            continue;
        };
        if !admitted_terminator(&last.inst)
            || last
                .inst
                .successor_edges()
                .iter()
                .any(|t| in_body(t.target))
        {
            continue;
        }
        let mut reads_loop = false;
        for node in &block.body {
            node.inst.visit_value_operands(|v| {
                reads_loop |= defs_at.get(&v).is_some_and(|d| shape.body.contains(d));
            });
        }
        let own: HashSet<ValueId> = block
            .params
            .iter()
            .map(|(v, _)| *v)
            .chain(block.body.iter().flat_map(|n| n.results.iter().copied()))
            .collect();
        let escapes = cur.blocks.iter().enumerate().any(|(o, other)| {
            o != e
                && other.body.iter().any(|n| {
                    let mut hit = false;
                    n.inst.visit_value_operands(|v| hit |= own.contains(&v));
                    hit
                })
        });
        if reads_loop && !escapes {
            exits.push(e);
        }
    }
    for (bi, block) in cur.blocks.iter().enumerate() {
        if shape.body.contains(&bi) || exits.contains(&bi) {
            continue;
        }
        for node in &block.body {
            let mut leak = false;
            node.inst.visit_value_operands(|v| {
                leak |= defs_at.get(&v).is_some_and(|d| shape.body.contains(d));
            });
            if leak {
                return Err(refuse(
                    header,
                    "a value of the loop is used outside it, where no copy dominates the use",
                ));
            }
        }
    }
    // ---- The arguments.
    let Some(Inst::Br { args: init, .. }) =
        cur.blocks[shape.preheader].body.last().map(|n| &n.inst)
    else {
        return Err(refuse(header, "the preheader lost its branch"));
    };
    let init = init.clone();
    let back: Vec<ValueId> = cur.blocks[latch]
        .body
        .last()
        .map(|t| t.inst.successor_edges())
        .unwrap_or_default()
        .into_iter()
        .find(|e| e.target == header)
        .map(|e| e.args.to_vec())
        .unwrap_or_default();
    let params: Vec<(ValueId, Ty)> = cur.blocks[h].params.clone();
    if init.len() != params.len() || back.len() != params.len() {
        return Err(refuse(
            header,
            "an edge into the header passes the wrong arity",
        ));
    }
    let types = value_types(cur);
    for (j, (param, ty)) in params.iter().enumerate() {
        if types.get(&init[j]) != Some(ty) || types.get(&back[j]) != Some(ty) {
            return Err(refuse(
                header,
                format!("an argument of %{param} does not have its type"),
            ));
        }
    }
    // ---- The exit on visit `bound`.
    let exit_edge = {
        let reader = Reader::new(cur, pointer_bits, &shape);
        let facts = Facts::new(cur, pointer_bits);
        let k = u128::from(lp.bound);
        let mut at_visit: HashMap<ValueId, Abs> = HashMap::new();
        for (j, (param, _)) in params.iter().enumerate() {
            let (Some(step), Some(start)) = (reader.read(back[j], 0), reader.read(init[j], 0))
            else {
                continue;
            };
            if step.root != Root::Param(j) || start.root != Root::Zero || start.bits != step.bits {
                continue;
            }
            at_visit.insert(
                *param,
                Abs::Known(
                    start.off.wrapping_add(k.wrapping_mul(step.off)) & mask(start.bits),
                    start.bits,
                ),
            );
        }
        let visit = Visit {
            facts: &facts,
            header: h,
            body: &shape.body,
            params: at_visit,
            memo: std::cell::RefCell::new(HashMap::new()),
        };
        let scrutinee = match &term {
            Inst::CondBr { cond, .. } => *cond,
            Inst::Switch { value, .. } => *value,
            _ => unreachable!("checked above"),
        };
        let edge = visit
            .eval(scrutinee, 0)
            .and_then(|s| edge_of(&term, s))
            .ok_or_else(|| {
                refuse(
                    header,
                    format!("the header's exit is not decided on visit {}", lp.bound),
                )
            })?;
        if in_body(edge.0) {
            return Err(refuse(
                header,
                format!("the header stays in the loop on visit {}", lp.bound),
            ));
        }
        edge
    };
    // ---- The bound on the copies.
    let n = lp.bound as usize;
    let size: usize = shape
        .body
        .iter()
        .chain(&exits)
        .map(|&b| cur.blocks[b].body.len())
        .sum();
    if n.saturating_mul(size) > super::MAX_UNROLLED_INSTS {
        return Err(refuse(
            header,
            format!(
                "{n} copies of {size} instructions are over the bound of {}",
                super::MAX_UNROLLED_INSTS
            ),
        ));
    }
    // ---- The fresh names.
    let others: Vec<usize> = (0..cur.blocks.len())
        .filter(|b| shape.body.contains(b) && *b != h)
        .chain(exits.iter().copied())
        .collect();
    let per_copy_values: usize = cur.blocks[h]
        .body
        .iter()
        .map(|n| n.results.len())
        .sum::<usize>()
        + others
            .iter()
            .map(|&b| {
                let block = &cur.blocks[b];
                block.params.len() + block.body.iter().map(|n| n.results.len()).sum::<usize>()
            })
            .sum::<usize>();
    if lp.blocks.len() != n * (1 + others.len()) {
        return Err(refuse(
            header,
            format!(
                "the witness names {} blocks, the copies need {}",
                lp.blocks.len(),
                n * (1 + others.len())
            ),
        ));
    }
    if lp.values.len() != n * per_copy_values {
        return Err(refuse(
            header,
            format!(
                "the witness names {} values, the copies define {}",
                lp.values.len(),
                n * per_copy_values
            ),
        ));
    }
    // ---- The copies.
    let mut fresh_values = lp.values.iter().copied();
    let mut copies: Vec<Block> = Vec::new();
    let mut prev: HashMap<ValueId, ValueId> = HashMap::new();
    let exit_ids: HashSet<BlockId> = exits.iter().map(|&b| cur.blocks[b].id).collect();
    for k in 0..n {
        let rename = |m: &HashMap<ValueId, ValueId>, v: ValueId| *m.get(&v).unwrap_or(&v);
        let mut sigma: HashMap<ValueId, ValueId> = HashMap::new();
        for (j, (param, _)) in params.iter().enumerate() {
            let v = if k == 0 {
                init[j]
            } else {
                rename(&prev, back[j])
            };
            sigma.insert(*param, v);
        }
        let block_of = |id: BlockId| -> BlockId {
            if id == header {
                return id;
            }
            match others.iter().position(|&b| cur.blocks[b].id == id) {
                Some(j) => lp.blocks[k * (1 + others.len()) + 1 + j],
                None => id,
            }
        };
        let h_k = lp.blocks[k * (1 + others.len())];
        let last = k + 1 == n;
        let next_header = if last {
            header
        } else {
            lp.blocks[(k + 1) * (1 + others.len())]
        };
        for node in &cur.blocks[h].body {
            for r in &node.results {
                sigma.insert(*r, fresh_values.next().unwrap_or(*r));
            }
        }
        for &b in &others {
            let block = &cur.blocks[b];
            for (p, _) in &block.params {
                sigma.insert(*p, fresh_values.next().unwrap_or(*p));
            }
            for node in &block.body {
                for r in &node.results {
                    sigma.insert(*r, fresh_values.next().unwrap_or(*r));
                }
            }
        }
        let map = |id: BlockId| {
            if id == header {
                next_header
            } else if in_body(id) || exit_ids.contains(&id) {
                block_of(id)
            } else {
                id
            }
        };
        let drop = (!last).then_some(header);
        // H_k, its terminator kept.
        let mut body: Vec<InstrNode> = Vec::new();
        for node in &cur.blocks[h].body {
            let mut copy = node.clone();
            trust_ir::mem2reg::rewrite_node(&mut copy, &sigma);
            if copy.inst.is_terminator() {
                retarget(&mut copy.inst, &map, drop);
            }
            body.push(copy);
        }
        copies.push(Block {
            id: h_k,
            params: Vec::new(),
            body,
        });
        for &b in &others {
            let block = &cur.blocks[b];
            let mut body: Vec<InstrNode> = Vec::new();
            for node in &block.body {
                let mut copy = node.clone();
                trust_ir::mem2reg::rewrite_node(&mut copy, &sigma);
                if copy.inst.is_terminator() {
                    retarget(&mut copy.inst, &map, drop);
                }
                body.push(copy);
            }
            copies.push(Block {
                id: block_of(block.id),
                params: block
                    .params
                    .iter()
                    .map(|(p, t)| (rename(&sigma, *p), t.clone()))
                    .collect(),
                body,
            });
        }
        prev = sigma;
    }
    // ---- The preheader, the header and the removed blocks.
    if let Some(last) = cur.blocks[shape.preheader].body.last_mut() {
        last.inst = Inst::Br {
            target: lp.blocks[0],
            args: Vec::new(),
        };
    }
    let (exit_target, exit_args) = exit_edge;
    if let Some(last) = cur.blocks[h].body.last_mut() {
        last.inst = Inst::Br {
            target: exit_target,
            args: exit_args,
        };
    }
    let removed_ids: HashSet<BlockId> = others
        .iter()
        .map(|&b| cur.blocks[b].id)
        .filter(|id| *id != exit_target || !exit_ids.contains(id))
        .collect();
    let mut removed: HashSet<ValueId> = HashSet::new();
    for block in cur.blocks.iter().filter(|b| removed_ids.contains(&b.id)) {
        removed.extend(block.params.iter().map(|(v, _)| *v));
        for node in &block.body {
            removed.extend(node.results.iter().copied());
        }
    }
    let header_block = cur.blocks[h].id;
    cur.blocks.retain(|b| !removed_ids.contains(&b.id));
    let at = cur
        .blocks
        .iter()
        .position(|b| b.id == header_block)
        .unwrap_or(cur.blocks.len());
    cur.blocks.splice(at..at, copies);
    drop_names(cur, &removed);
    Ok(())
}

#[cfg(test)]
#[path = "trust_ir_mid_tv_bounded_tests.rs"]
mod tests;
