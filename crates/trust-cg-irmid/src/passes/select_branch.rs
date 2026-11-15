// trust-cg-irmid/passes/select_branch.rs - branches on selects, and selects under their branch
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The select-branch rules. The rustc bridge spells an early-exit test as
//! a `switch` on the `zext` of a `select c, 1, 0` (a `RangeInclusive`'s
//! `next`, a labeled break's flag), and an `Option<&T>`'s niche as `switch
//! select(p == 0, trunc p, 1)` on the address of `select c, q, null` (a
//! `Zip`'s `next`), with the `Some` arm loading through the select. LLVM
//! branches on `c` and loads through `q`. Two rules:
//!
//! - **terminators**: a `switch` or `condbr` whose scrutinee, evaluated
//!   assuming a `bool` `c` of its operand chain is `true` and then `false`,
//!   takes a decided edge both times becomes `condbr c` to those edges (or
//!   `br` when they agree). The evaluator knows constants, `null`, selects
//!   on known conditions, casts, compares and integer arithmetic, the value
//!   an equality condition pins (`p == 0` assumed true makes `p` zero), and
//!   that an `alloca` plus a constant offset at most its size is not null.
//!   A block's terminator is retried on its new condition, so the niche
//!   test above becomes `condbr (p == 0)` and then `condbr c` once `q` is a
//!   slot address at a constant offset (after unrolling);
//! - **forwards**: in a block that only the `true` (or `false`) edge of a
//!   `condbr c` reaches (never the function's entry block, which the call
//!   enters too), an operand that is `select c, a, b` behind at most
//!   two casts reads `a` (or `b`) through a copy of the casts placed just
//!   before its use, so the `Some` arm's load reads the slot address that
//!   store forwarding and scalar replacement then resolve. Policy (not the
//!   checker's): only an edge's argument and an address (a pointer cast, a
//!   `gep` base, a load's or store's pointer) are forwarded; anywhere else
//!   the arm would be a new value where the range rules read their facts of
//!   the select by its name (a bounds check guarded by a compare of it).
//!
//! Each rule is re-derived by the checker (`trust_ir_mid_tv_selbr.rs`) with
//! its own evaluator and dominance.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use trust_cg_verify::trust_ir_mid_tv::{
    PassWitness, SelectBranchWitness, SelectForward, SelectTerminator,
};
use trust_ir::{BinOp, BlockId, CastOp, Constant, Function, ICmpOp, Inst, InstrNode, Ty, ValueId};

use super::loops::{clean, first_free_value};
use super::{MidPass, PassContext, drop_names, int_shape, sole_defs, value_types};
use crate::cfg::TrustIrCfg;

pub(crate) struct SelectBranch;

/// The evidence name of the select-branch rules.
pub(crate) const SELECT_BRANCH_NAME: &str = "select_branch";

/// Policy: the longest cast chain a forward copies (the checker admits
/// more).
const POLICY_CHAIN: usize = 2;

/// How often one block's terminator is retried on its new condition.
const RETRIES: usize = 4;

/// The most conditions tried on one terminator, nearest first.
const MAX_CANDIDATES: usize = 8;

/// The most dominating guards a forward consults, nearest first.
const MAX_GUARDS: usize = 8;

fn ones(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

/// What the pass's evaluator knows of a value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Val {
    Bits(u128, u32),
    NotNull,
}

fn bits(raw: u128, width: u32) -> Val {
    Val::Bits(raw & ones(width), width)
}

fn sext(raw: u128, width: u32) -> i128 {
    if width == 0 || width >= 128 {
        return raw as i128;
    }
    let s = 128 - width;
    ((raw << s) as i128) >> s
}

struct Eval<'a> {
    cx: &'a PassContext<'a>,
    defs: &'a HashMap<ValueId, Inst>,
    cond: ValueId,
    value: bool,
    pinned: Option<(ValueId, Val)>,
    /// Each value's reading under the assumption, once computed.
    memo: RefCell<HashMap<ValueId, Option<Val>>>,
}

impl Eval<'_> {
    fn width(&self, ty: &Ty) -> Option<u32> {
        if *ty == Ty::Bool {
            return Some(1);
        }
        int_shape(ty, self.cx.pointer_bits)
            .map(|(w, _)| w)
            .or(matches!(
                ty,
                Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
            )
            .then_some(self.cx.pointer_bits))
    }

    fn pointer_int(&self, ty: &Ty) -> bool {
        int_shape(ty, self.cx.pointer_bits).is_some_and(|(w, _)| w == self.cx.pointer_bits)
    }

    fn const_int(&self, v: ValueId) -> Option<u128> {
        match self.defs.get(&v)? {
            Inst::Const {
                ty,
                value: Constant::Int(k),
            } if self.pointer_int(ty) => Some((*k as u128) & ones(self.cx.pointer_bits)),
            _ => None,
        }
    }

    /// `v` as an `alloca` plus a constant byte offset.
    fn in_slot(&self, v: ValueId, depth: usize) -> Option<(ValueId, u128)> {
        if depth > 32 {
            return None;
        }
        match self.defs.get(&v)? {
            Inst::Alloca { .. } => Some((v, 0)),
            Inst::Copy { operand, .. } => self.in_slot(*operand, depth + 1),
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => {
                let ok = match op {
                    CastOp::PtrToPtr => true,
                    CastOp::PtrToInt => self.pointer_int(dst_ty),
                    CastOp::IntToPtr => self.pointer_int(src_ty),
                    CastOp::Bitcast => self.pointer_int(src_ty) && self.pointer_int(dst_ty),
                    _ => false,
                };
                if ok {
                    self.in_slot(*operand, depth + 1)
                } else {
                    None
                }
            }
            Inst::BinOp {
                op: BinOp::Add,
                ty,
                lhs,
                rhs,
            } if self.pointer_int(ty) => match (self.const_int(*lhs), self.const_int(*rhs)) {
                (_, Some(k)) => {
                    let (s, o) = self.in_slot(*lhs, depth + 1)?;
                    Some((s, o.checked_add(k)?))
                }
                (Some(k), None) => {
                    let (s, o) = self.in_slot(*rhs, depth + 1)?;
                    Some((s, o.checked_add(k)?))
                }
                _ => None,
            },
            Inst::GEP {
                pointee_ty: Ty::U8 | Ty::I8,
                base,
                indices,
                ..
            } if indices.len() == 1 => {
                let k = self.const_int(indices[0])?;
                let (s, o) = self.in_slot(*base, depth + 1)?;
                Some((s, o.checked_add(k)?))
            }
            _ => None,
        }
    }

    fn not_null(&self, v: ValueId) -> bool {
        let Some((slot, off)) = self.in_slot(v, 0) else {
            return false;
        };
        let Some(Inst::Alloca { ty, count, .. }) = self.defs.get(&slot) else {
            return false;
        };
        let Some(size) = self
            .cx
            .module
            .ty_layout_shape(ty)
            .ok()
            .and_then(|s| s.size_bytes())
        else {
            return false;
        };
        let n = match count {
            None => 1u128,
            Some(c) => match self.defs.get(c) {
                Some(Inst::Const {
                    value: Constant::Int(k),
                    ..
                }) if *k >= 1 => *k as u128,
                _ => return false,
            },
        };
        size > 0 && u128::from(size).checked_mul(n).is_some_and(|t| off <= t)
    }

    fn get(&self, v: ValueId, depth: usize) -> Option<Val> {
        if depth > 64 {
            return None;
        }
        if v == self.cond {
            return Some(bits(u128::from(self.value), 1));
        }
        if let Some((x, k)) = self.pinned
            && x == v
        {
            return Some(k);
        }
        if let Some(known) = self.memo.borrow().get(&v) {
            return *known;
        }
        let known = self
            .def(v, depth)
            .or_else(|| self.not_null(v).then_some(Val::NotNull));
        self.memo.borrow_mut().insert(v, known);
        known
    }

    fn def(&self, v: ValueId, depth: usize) -> Option<Val> {
        let get = |x: ValueId| self.get(x, depth + 1);
        match self.defs.get(&v)? {
            Inst::Const { ty, value } => {
                let w = self.width(ty)?;
                match value {
                    Constant::Int(k) => Some(bits(*k as u128, w)),
                    Constant::Bool(b) => Some(bits(u128::from(*b), 1)),
                    _ => None,
                }
            }
            Inst::NullPtr => Some(bits(0, self.cx.pointer_bits)),
            Inst::Copy { operand, .. } => get(*operand),
            Inst::Select {
                cond,
                then_val,
                else_val,
                ..
            } => match get(*cond)? {
                Val::Bits(1, 1) => get(*then_val),
                Val::Bits(0, 1) => get(*else_val),
                _ => None,
            },
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => {
                let pb = self.cx.pointer_bits;
                let (s, d) = (self.width(src_ty)?, self.width(dst_ty)?);
                let x = get(*operand)?;
                if let Val::Bits(_, w) = x
                    && w != s
                {
                    return None;
                }
                match (op, x) {
                    (CastOp::ZExt, Val::Bits(r, _)) if d >= s => Some(bits(r, d)),
                    (CastOp::SExt, Val::Bits(r, _)) if d >= s => Some(bits(sext(r, s) as u128, d)),
                    (CastOp::Trunc, Val::Bits(r, _)) if d <= s => Some(bits(r, d)),
                    (CastOp::Bitcast, x) if d == s && int_shape(src_ty, pb).is_some() => Some(x),
                    (CastOp::PtrToPtr, x) => Some(x),
                    (CastOp::IntToPtr, x) if s == pb => Some(x),
                    (CastOp::PtrToInt, x) if d == pb => Some(x),
                    (CastOp::PtrToInt, Val::Bits(r, _)) if d > pb => Some(bits(r, d)),
                    (CastOp::PtrToInt, Val::NotNull) if d > pb => Some(Val::NotNull),
                    _ => None,
                }
            }
            Inst::ICmp { op, ty, lhs, rhs } => {
                let w = self.width(ty)?;
                match (get(*lhs), get(*rhs)) {
                    (Some(Val::Bits(x, wx)), Some(Val::Bits(y, wy))) if wx == w && wy == w => {
                        let (a, b) = (sext(x, w), sext(y, w));
                        Some(bits(
                            u128::from(match op {
                                ICmpOp::Eq => x == y,
                                ICmpOp::Ne => x != y,
                                ICmpOp::Ult => x < y,
                                ICmpOp::Ule => x <= y,
                                ICmpOp::Ugt => x > y,
                                ICmpOp::Uge => x >= y,
                                ICmpOp::Slt => a < b,
                                ICmpOp::Sle => a <= b,
                                ICmpOp::Sgt => a > b,
                                ICmpOp::Sge => a >= b,
                            }),
                            1,
                        ))
                    }
                    (Some(Val::NotNull), Some(Val::Bits(0, _)))
                    | (Some(Val::Bits(0, _)), Some(Val::NotNull))
                        if matches!(op, ICmpOp::Eq | ICmpOp::Ne) =>
                    {
                        Some(bits(u128::from(*op == ICmpOp::Ne), 1))
                    }
                    _ => None,
                }
            }
            Inst::BinOp { op, ty, lhs, rhs } => {
                let w = int_shape(ty, self.cx.pointer_bits)?.0;
                let (Val::Bits(a, wa), Val::Bits(b, wb)) = (get(*lhs)?, get(*rhs)?) else {
                    return None;
                };
                if wa != w || wb != w {
                    return None;
                }
                let k = || u32::try_from(b).ok().filter(|k| *k < w);
                Some(bits(
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
                    },
                    w,
                ))
            }
            _ => None,
        }
    }
}

/// The edge `term` takes on the scrutinee `s`.
fn edge_on(term: &Inst, s: Val) -> Option<(BlockId, Vec<ValueId>)> {
    let Val::Bits(raw, width) = s else {
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
                if (k as u128) & ones(width) == raw {
                    return Some((case.target, case.args.clone()));
                }
            }
            Some((*default, default_args.clone()))
        }
        _ => None,
    }
}

/// The `bool` conditions of selects and compares on `s`'s operand chain,
/// nearest first.
fn candidates(
    defs: &HashMap<ValueId, Inst>,
    types: &HashMap<ValueId, Ty>,
    s: ValueId,
) -> Vec<ValueId> {
    let mut out = Vec::new();
    let mut seen: HashSet<ValueId> = HashSet::new();
    let mut frontier = vec![s];
    for _ in 0..16 {
        let mut next = Vec::new();
        for v in frontier {
            if !seen.insert(v) {
                continue;
            }
            if v != s && types.get(&v) == Some(&Ty::Bool) && !out.contains(&v) {
                out.push(v);
            }
            if let Some(inst) = defs.get(&v) {
                if let Inst::Select { cond, .. } = inst
                    && types.get(cond) == Some(&Ty::Bool)
                    && !out.contains(cond)
                {
                    out.push(*cond);
                }
                inst.visit_value_operands(|x| next.push(x));
            }
        }
        frontier = next;
    }
    out
}

fn pinned_by(
    defs: &HashMap<ValueId, Inst>,
    width: &dyn Fn(&Ty) -> Option<u32>,
    cond: ValueId,
    value: bool,
) -> Option<(ValueId, Val)> {
    let Inst::ICmp { op, lhs, rhs, .. } = defs.get(&cond)? else {
        return None;
    };
    if !((*op == ICmpOp::Eq && value) || (*op == ICmpOp::Ne && !value)) {
        return None;
    }
    let k = |x: ValueId| match defs.get(&x)? {
        Inst::Const {
            ty,
            value: Constant::Int(k),
        } => Some(bits(*k as u128, width(ty)?)),
        _ => None,
    };
    k(*rhs)
        .map(|c| (*lhs, c))
        .or_else(|| k(*lhs).map(|c| (*rhs, c)))
}

/// The terminator of block `b` decided by a candidate condition: the
/// condition and the new terminator.
fn decide(
    cx: &PassContext<'_>,
    func: &Function,
    defs: &HashMap<ValueId, Inst>,
    types: &HashMap<ValueId, Ty>,
    b: usize,
) -> Option<(ValueId, Inst)> {
    let term = &func.blocks[b].body.last()?.inst;
    let (scrutinee, own) = match term {
        Inst::Switch { value, .. } => (*value, None),
        Inst::CondBr { cond, .. } => (*cond, Some(*cond)),
        _ => return None,
    };
    for c in candidates(defs, types, scrutinee)
        .into_iter()
        .take(MAX_CANDIDATES)
    {
        if Some(c) == own {
            continue;
        }
        let mut edges = Vec::new();
        for value in [true, false] {
            let probe = Eval {
                cx,
                defs,
                cond: c,
                value,
                pinned: None,
                memo: RefCell::new(HashMap::new()),
            };
            let width = |ty: &Ty| probe.width(ty);
            let pinned = pinned_by(defs, &width, c, value);
            let ev = Eval { pinned, ..probe };
            let Some(e) = ev.get(scrutinee, 0).and_then(|s| edge_on(term, s)) else {
                break;
            };
            edges.push(e);
        }
        let [t, f] = edges.as_slice() else {
            continue;
        };
        // Policy: the lane emits a `condbr`'s `then` edge as the fall-through
        // arm of an `if`; a branch whose `then` edge would lead to a block
        // that ends in `unreachable` (a panic path) while its `else` edge
        // does not is left alone, since V8's baseline tier runs the hot
        // path through the jump then (measured on `utf8_dfa`'s
        // remainder-by-zero check under Liftoff).
        let cold = |id: BlockId| {
            func.blocks.iter().any(|b| {
                b.id == id && matches!(b.body.last().map(|n| &n.inst), Some(Inst::Unreachable))
            })
        };
        if t != f && cold(t.0) && !cold(f.0) {
            continue;
        }
        let inst = if t == f {
            Inst::Br {
                target: t.0,
                args: t.1.clone(),
            }
        } else {
            Inst::CondBr {
                cond: c,
                then_target: t.0,
                then_args: t.1.clone(),
                else_target: f.0,
                else_args: f.1.clone(),
            }
        };
        return Some((c, inst));
    }
    None
}

/// The casts from `w` back to a select on `cond`, outermost first, and the
/// select's arms.
fn casts_to_select(
    defs: &HashMap<ValueId, Inst>,
    w: ValueId,
) -> Option<(Vec<Inst>, ValueId, ValueId, ValueId)> {
    let mut chain = Vec::new();
    let mut v = w;
    loop {
        match defs.get(&v)? {
            Inst::Select {
                cond,
                then_val,
                else_val,
                ..
            } => return Some((chain, *cond, *then_val, *else_val)),
            inst @ (Inst::Copy { operand, .. }
            | Inst::Cast {
                op:
                    CastOp::ZExt
                    | CastOp::SExt
                    | CastOp::Trunc
                    | CastOp::Bitcast
                    | CastOp::PtrToInt
                    | CastOp::IntToPtr
                    | CastOp::PtrToPtr,
                operand,
                ..
            }) if chain.len() < POLICY_CHAIN => {
                chain.push((*inst).clone());
                v = *operand;
            }
            _ => return None,
        }
    }
}

/// The value the guards `held` (each a `condbr` condition and the value
/// that takes the guarding edge) fix for `c`: a guard on `c` itself, or one
/// that assuming `c` is `x` the evaluator decides against its edge, fixes
/// `c` to `!x`. `None` when no guard fixes it or two disagree.
fn implied(
    cx: &PassContext<'_>,
    defs: &HashMap<ValueId, Inst>,
    held: &[(ValueId, bool)],
    c: ValueId,
) -> Option<bool> {
    let mut found: Option<bool> = None;
    for &(g, edge) in held {
        let fixed = if g == c {
            Some(edge)
        } else {
            [true, false].into_iter().find_map(|x| {
                let probe = Eval {
                    cx,
                    defs,
                    cond: c,
                    value: x,
                    pinned: None,
                    memo: RefCell::new(HashMap::new()),
                };
                let width = |ty: &Ty| probe.width(ty);
                let pinned = pinned_by(defs, &width, c, x);
                let ev = Eval { pinned, ..probe };
                match ev.get(g, 0) {
                    Some(Val::Bits(b, 1)) if (b == 1) != edge => Some(!x),
                    _ => None,
                }
            })
        };
        if let Some(v) = fixed {
            if found.is_some_and(|f| f != v) {
                return None;
            }
            found = Some(v);
        }
    }
    found
}

impl MidPass for SelectBranch {
    fn name(&self) -> &'static str {
        SELECT_BRANCH_NAME
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let mut cur = func.clone();
        let mut witness = SelectBranchWitness::default();
        // ---- Terminators, each block retried on its new condition. A
        // terminator defines no value, so the definitions stay valid.
        let defs: HashMap<ValueId, Inst> = sole_defs(func)
            .into_iter()
            .map(|(v, i)| (v, i.clone()))
            .collect();
        let types = value_types(func);
        for b in 0..cur.blocks.len() {
            for _ in 0..RETRIES {
                let Some((cond, inst)) = decide(cx, &cur, &defs, &types, b) else {
                    break;
                };
                witness.terminators.push(SelectTerminator {
                    block: cur.blocks[b].id,
                    cond,
                });
                let last = cur.blocks[b].body.last_mut()?;
                last.inst = inst;
            }
        }
        // ---- The blocks the rewrites left unreachable go.
        if !witness.terminators.is_empty() {
            let live: HashSet<BlockId> = TrustIrCfg::new(&cur).rpo().into_iter().collect();
            let mut removed: HashSet<ValueId> = HashSet::new();
            for block in &cur.blocks {
                if block.id != cur.entry && !live.contains(&block.id) {
                    witness.removed_blocks.push(block.id);
                    removed.extend(block.params.iter().map(|(v, _)| *v));
                    for node in &block.body {
                        removed.extend(node.results.iter().copied());
                    }
                }
            }
            let used_by_live = cur
                .blocks
                .iter()
                .filter(|b| live.contains(&b.id))
                .flat_map(|b| &b.body)
                .any(|n| {
                    let mut hit = false;
                    n.inst.visit_value_operands(|v| hit |= removed.contains(&v));
                    hit
                });
            if used_by_live {
                return None;
            }
            let doomed: HashSet<BlockId> = witness.removed_blocks.iter().copied().collect();
            cur.blocks.retain(|b| !doomed.contains(&b.id));
            drop_names(&mut cur, &removed);
        }
        // ---- Forwards under the branches.
        let mut next = first_free_value(&cur);
        let guards: Vec<(ValueId, BlockId, bool)> = {
            let mut entering: HashMap<BlockId, usize> = HashMap::new();
            for block in &cur.blocks {
                if let Some(last) = block.body.last() {
                    for e in last.inst.successor_edges() {
                        *entering.entry(e.target).or_default() += 1;
                    }
                }
            }
            cur.blocks
                .iter()
                .filter_map(|block| match block.body.last().map(|n| &n.inst) {
                    Some(Inst::CondBr {
                        cond,
                        then_target,
                        else_target,
                        ..
                    }) if then_target != else_target => {
                        Some([(*cond, *then_target, true), (*cond, *else_target, false)])
                    }
                    _ => None,
                })
                .flatten()
                // The call also enters the entry block, without the edge.
                .filter(|(_, g, _)| *g != cur.entry && entering.get(g) == Some(&1))
                .collect()
        };
        if !guards.is_empty() {
            // The guards dominating each block, nearest first: a walk of the
            // dominator tree keeps the guards of the blocks on its path.
            let (rpo, idom) = TrustIrCfg::new(&cur).rpo_and_idom();
            let guard_of: HashMap<BlockId, Vec<(ValueId, bool)>> = {
                let mut m: HashMap<BlockId, Vec<(ValueId, bool)>> = HashMap::new();
                for (c, g, v) in &guards {
                    m.entry(*g).or_default().push((*c, *v));
                }
                m
            };
            let mut held_at: HashMap<BlockId, Vec<(ValueId, bool)>> = HashMap::new();
            for b in &rpo {
                // Reverse postorder visits a block's immediate dominator
                // first.
                let mut held: Vec<(ValueId, bool)> = guard_of.get(b).cloned().unwrap_or_default();
                if let Some(parent) = idom.get(b).filter(|p| *p != b)
                    && let Some(above) = held_at.get(parent)
                {
                    held.extend(above.iter().take(MAX_GUARDS).copied());
                }
                held.truncate(MAX_GUARDS);
                held_at.insert(*b, held);
            }
            let mut defs: HashMap<ValueId, Inst> = sole_defs(&cur)
                .into_iter()
                .map(|(v, i)| (v, i.clone()))
                .collect();
            let mut typed = value_types(&cur);
            for u in 0..cur.blocks.len() {
                let uid = cur.blocks[u].id;
                let Some(held) = held_at.get(&uid).cloned() else {
                    continue;
                };
                if held.is_empty() {
                    continue;
                }
                let mut i = 0usize;
                while i < cur.blocks[u].body.len() {
                    // Policy: forward only into an edge's arguments (a loop's
                    // stepped state) and into an address (a pointer cast, a
                    // `gep` base, a load's or store's pointer). Elsewhere the
                    // arm is a new value where the range rules read facts
                    // of the select by its name.
                    let mut operands = Vec::new();
                    match &cur.blocks[u].body[i].inst {
                        inst if inst.is_terminator() => {
                            for e in inst.successor_edges() {
                                operands.extend(e.args.iter().copied());
                            }
                        }
                        Inst::Cast {
                            op: CastOp::IntToPtr | CastOp::PtrToPtr,
                            operand,
                            ..
                        } => operands.push(*operand),
                        Inst::GEP { base, .. } => operands.push(*base),
                        Inst::Load { ptr, .. } | Inst::Store { ptr, .. } => operands.push(*ptr),
                        _ => {}
                    }
                    let mut done = None;
                    for w in operands {
                        if let Some((chain, c, a, b)) = casts_to_select(&defs, w)
                            && let Some(value) = implied(cx, &defs, &held, c)
                        {
                            done = Some((w, c, value, chain, a, b));
                            break;
                        }
                    }
                    let Some((w, c, value, chain, a, b)) = done else {
                        i += 1;
                        continue;
                    };
                    let fresh: Vec<ValueId> = (0..chain.len())
                        .map(|k| ValueId::new(next + k as u32))
                        .collect();
                    let mut current = if value { a } else { b };
                    let mut inserted = Vec::new();
                    let mut clean_copies = true;
                    for (inst, v) in chain.iter().rev().zip(&fresh) {
                        let mut copy = inst.clone();
                        let ty = match &mut copy {
                            Inst::Copy { operand, ty } => {
                                *operand = current;
                                ty.clone()
                            }
                            Inst::Cast {
                                operand, dst_ty, ..
                            } => {
                                *operand = current;
                                dst_ty.clone()
                            }
                            _ => {
                                clean_copies = false;
                                break;
                            }
                        };
                        // Policy: copy only what trust-ir's validator reads
                        // without a finding (`loops::clean`).
                        clean_copies &= clean(cx.module, &cur, cx.pointer_bits, &copy, &typed);
                        typed.insert(*v, ty);
                        inserted.push(InstrNode::new(copy).with_results([*v]));
                        current = *v;
                    }
                    if !clean_copies {
                        i += 1;
                        continue;
                    }
                    next += chain.len() as u32;
                    witness.forwards.push(SelectForward {
                        block: uid,
                        index: i,
                        operand: w,
                        cond: c,
                        values: fresh,
                    });
                    let map: HashMap<ValueId, ValueId> = [(w, current)].into_iter().collect();
                    trust_ir::mem2reg::rewrite_node(&mut cur.blocks[u].body[i], &map);
                    // Keep the definitions current: the rewritten instruction
                    // and the copies are what later forwards read.
                    if let [r] = cur.blocks[u].body[i].results.as_slice() {
                        defs.insert(*r, cur.blocks[u].body[i].inst.clone());
                    }
                    let n = inserted.len();
                    for (k, node) in inserted.into_iter().enumerate() {
                        if let [r] = node.results.as_slice() {
                            defs.insert(*r, node.inst.clone());
                        }
                        cur.blocks[u].body.insert(i + k, node);
                    }
                    // The same instruction may read another such operand.
                    i += n;
                }
            }
        }
        if witness.terminators.is_empty() && witness.forwards.is_empty() {
            return None;
        }
        Some((cur, PassWitness::SelectBranch(witness)))
    }
}
