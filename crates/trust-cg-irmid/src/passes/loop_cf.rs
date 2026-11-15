// trust-cg-irmid/passes/loop_cf.rs - closed-form induction
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Closed-form induction: the counted-loop recognizer of the native lanes'
//! `trust_cg_opt::loop_iv` (preheader initial value, header compare against
//! a limit, `+ step` on the back edge) lifted to trust-ir, and its
//! reductions replaced by their closed forms, as LLVM's scalar evolution
//! does for `(0..n).sum()`.
//!
//! A loop qualifies when its header ends in the loop's only exit, a
//! `condbr` on `i <u n`, `i <s n` or `i != n` (in either operand order, on
//! either edge) of a header parameter `i` stepping by `+ 1` and a bound
//! defined outside the loop; its other blocks form no cycle; every
//! instruction in it is on the dead-code pass's removable list; values of
//! the blocks after the header are not used outside the loop; and every
//! other header parameter is passed back unchanged or is an accumulator
//! `p + t` / `p - t` (also through `add.overflow` / `sub.overflow` whose
//! flag nothing reads) with `t` affine in `i`: a constant or invariant
//! `b`, or `a * x` with `x` the induction variable, its `zext` under the
//! `<u` exit or its `sext` under the `<s` exit, at a type at least as wide.
//! Initial values and coefficients must never be poison: the loop may run
//! zero times, and the closed form reads them.
//!
//! The rewrite computes the trip count `N` and each accumulator's final
//! value `p0 +- (a * (N * x0 + T(N)) + b * N)` at the end of the preheader
//! (a coefficient of one multiplies nothing; `N` at each wider type and
//! `S = N * x0 + T(N)` at each type and extension are computed once and
//! shared by every accumulator that reads them)
//! (`T(N) = N (N - 1) / 2` with the even factor halved first, everything
//! modulo the accumulator's width), passes the final values into the
//! header, turns the header's exit test into a `br` to the exit and removes
//! the loop's other blocks: the header runs once, on the values of the
//! source's last visit. The instruction order is the checker's
//! (`trust_ir_mid_tv_loop.rs`, `closed_form`); the witness names the
//! header and the fresh values in that order.

use std::collections::{HashMap, HashSet};

use trust_cg_verify::trust_ir_mid_tv::{LoopCfLoop, LoopCfWitness, PassWitness};
use trust_ir::{
    BinOp, BlockId, CastOp, Constant, Function, ICmpOp, Inst, InstrNode, OverflowOp, Ty, ValueId,
};

use super::dce::removable;
use super::loops::{
    Loop, back_edge_args, def_blocks, first_free_value, never_poison, preheader_args,
    rewritable_loops,
};
use super::{MidPass, PassContext, drop_names, int_shape, sole_defs, value_types};

pub(crate) struct LoopClosedForm;

/// The evidence name of closed-form induction.
pub(crate) const LOOP_CF_NAME: &str = "loop_cf";

impl MidPass for LoopClosedForm {
    fn name(&self) -> &'static str {
        LOOP_CF_NAME
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let mut cur = func.clone();
        let mut next = first_free_value(func);
        let mut loops = Vec::new();
        // A closed loop may leave its enclosing loop closable: look again
        // until nothing changes (bounded by the loop count).
        for _ in 0..64 {
            let mut done = None;
            for lp in rewritable_loops(&cur) {
                if let Some((out, values)) = close(&cur, cx.pointer_bits, &lp, next) {
                    next += u32::try_from(values.len()).ok()?;
                    done = Some((out, lp.header, values));
                    break;
                }
            }
            let Some((out, header, values)) = done else {
                break;
            };
            cur = out;
            loops.push(LoopCfLoop { header, values });
        }
        if loops.is_empty() {
            return None;
        }
        Some((cur, PassWitness::LoopCf(LoopCfWitness { loops })))
    }
}

/// How the loop continues.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Exit {
    Ult,
    Slt,
    Ne,
}

/// A coefficient: exactly one, a constant re-emitted at the accumulator's
/// type, or a value available in the preheader.
#[derive(Debug, Clone, PartialEq)]
enum Coef {
    One,
    Const(Constant),
    Value(ValueId),
}

/// The induction variable's form in a term.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Ext {
    Same,
    Zext,
    Sext,
}

#[derive(Debug, Clone, PartialEq)]
struct Accumulator {
    subtract: bool,
    a: Option<(Coef, Ext)>,
    b: Option<Coef>,
}

/// The closed form of `lp` in `func` with fresh values from `next`: the
/// rewritten function and the values it defines, or `None`.
fn close(
    func: &Function,
    pointer_bits: u32,
    lp: &Loop,
    next: u32,
) -> Option<(Function, Vec<ValueId>)> {
    if lp.back_edges != 1 {
        return None;
    }
    let types = value_types(func);
    let defs = sole_defs(func);
    let def = |v: ValueId| defs.get(&v).copied();
    let defs_at = def_blocks(func);
    let in_loop = |v: ValueId| defs_at.get(&v).is_some_and(|b| lp.body.contains(b));
    let block = |id: BlockId| func.blocks.iter().find(|b| b.id == id);
    let header = block(lp.header)?;
    // ---- Every instruction removable, the body acyclic, one exit.
    for id in &lp.body {
        let b = block(*id)?;
        let (last, rest) = b.body.split_last()?;
        for node in rest {
            removable(&node.inst, |v| types.get(&v).cloned(), def)?;
        }
        if !matches!(
            last.inst,
            Inst::Br { .. } | Inst::CondBr { .. } | Inst::Switch { .. }
        ) {
            return None;
        }
        if *id != lp.header
            && last
                .inst
                .successor_edges()
                .iter()
                .any(|e| !lp.body.contains(&e.target))
        {
            return None;
        }
    }
    if has_inner_cycle(func, lp) {
        return None;
    }
    for b in func.blocks.iter().filter(|b| !lp.body.contains(&b.id)) {
        for node in &b.body {
            let mut leaks = false;
            node.inst.visit_value_operands(|v| {
                leaks |= in_loop(v) && defs_at.get(&v) != Some(&lp.header);
            });
            if leaks {
                return None;
            }
        }
    }
    let Some(Inst::CondBr {
        cond,
        then_target,
        then_args,
        else_target,
        else_args,
    }) = header.body.last().map(|n| &n.inst)
    else {
        return None;
    };
    let then_in = lp.body.contains(then_target);
    if then_in == lp.body.contains(else_target) {
        return None;
    }
    let (exit_target, exit_args) = if then_in {
        (*else_target, else_args.clone())
    } else {
        (*then_target, then_args.clone())
    };
    if defs_at.get(cond) != Some(&lp.header) {
        return None;
    }
    let Some(Inst::ICmp {
        op,
        ty: cmp_ty,
        lhs,
        rhs,
    }) = def(*cond)
    else {
        return None;
    };
    let params: Vec<ValueId> = header.params.iter().map(|(v, _)| *v).collect();
    // Continue while `pred(i, bound)`.
    let pred = if then_in { *op } else { negate(*op) };
    let (iv, bound, pred) = if params.contains(lhs) {
        (*lhs, *rhs, pred)
    } else if params.contains(rhs) {
        (*rhs, *lhs, flip(pred))
    } else {
        return None;
    };
    let exit = match pred {
        ICmpOp::Ult => Exit::Ult,
        ICmpOp::Slt => Exit::Slt,
        ICmpOp::Ne => Exit::Ne,
        _ => return None,
    };
    let k = params.iter().position(|p| *p == iv)?;
    let iv_ty = header.params[k].1.clone();
    if *cmp_ty != iv_ty || int_shape(&iv_ty, pointer_bits).is_none() {
        return None;
    }
    let init: Vec<ValueId> = preheader_args(func, lp)?.to_vec();
    let backs = back_edge_args(func, lp);
    let [back] = backs.as_slice() else {
        return None;
    };
    if init.len() != params.len() || back.len() != params.len() {
        return None;
    }
    // Multi-result nodes by result, for the overflow forms.
    let mut nodes: HashMap<ValueId, &InstrNode> = HashMap::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        for r in &node.results {
            nodes.insert(*r, node);
        }
    }
    let ty_of = |v: ValueId| -> Option<Ty> {
        types.get(&v).cloned().or_else(|| match nodes.get(&v)? {
            InstrNode {
                inst: Inst::Overflow { ty, .. },
                results,
                ..
            } => Some(if results.first() == Some(&v) {
                ty.clone()
            } else {
                Ty::Bool
            }),
            _ => None,
        })
    };
    let resolve = |mut v: ValueId| {
        for _ in 0..64 {
            match def(v) {
                Some(Inst::Copy { ty, operand })
                    if in_loop(v) && ty_of(*operand).as_ref() == Some(ty) =>
                {
                    v = *operand;
                }
                _ => break,
            }
        }
        v
    };
    let invariant = |j: usize| resolve(back[j]) == params[j];
    let available = |v: ValueId| -> Option<ValueId> {
        if !in_loop(v) && defs_at.contains_key(&v) {
            return Some(v);
        }
        let j = params.iter().position(|p| *p == v)?;
        invariant(j).then_some(init[j])
    };
    let bound = available(bound)?;
    // The closed form's instructions are well typed (the lane re-validates
    // the module): the bound and the initial values have their types.
    if types.get(&bound) != Some(&iv_ty)
        || header
            .params
            .iter()
            .zip(&init)
            .any(|((_, ty), v)| types.get(v) != Some(ty))
    {
        return None;
    }
    let mut used: HashSet<ValueId> = HashSet::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        node.inst.visit_value_operands(|v| {
            used.insert(v);
        });
    }
    let (bits_iv, _) = int_shape(&iv_ty, pointer_bits)?;
    let mut roles: Vec<Option<Accumulator>> = Vec::new();
    for (j, (param, ty)) in header.params.iter().enumerate() {
        if invariant(j) {
            roles.push(None);
            continue;
        }
        let (bits, _) = int_shape(ty, pointer_bits)?;
        if bits < bits_iv {
            return None;
        }
        let step = resolve(back[j]);
        if !in_loop(step) {
            return None;
        }
        let (subtract, term) = match nodes.get(&step).map(|n| (&n.inst, n.results.as_slice()))? {
            (
                Inst::BinOp {
                    op: BinOp::Add,
                    ty: t,
                    lhs,
                    rhs,
                },
                [_],
            ) if t == ty => {
                if resolve(*lhs) == *param {
                    (false, *rhs)
                } else if resolve(*rhs) == *param {
                    (false, *lhs)
                } else {
                    return None;
                }
            }
            (
                Inst::BinOp {
                    op: BinOp::Sub,
                    ty: t,
                    lhs,
                    rhs,
                },
                [_],
            ) if t == ty && resolve(*lhs) == *param => (true, *rhs),
            (
                Inst::Overflow {
                    op: OverflowOp::AddOverflow,
                    ty: t,
                    lhs,
                    rhs,
                },
                [value, flag],
            ) if t == ty && *value == step && !used.contains(flag) => {
                if resolve(*lhs) == *param {
                    (false, *rhs)
                } else if resolve(*rhs) == *param {
                    (false, *lhs)
                } else {
                    return None;
                }
            }
            (
                Inst::Overflow {
                    op: OverflowOp::SubOverflow,
                    ty: t,
                    lhs,
                    rhs,
                },
                [value, flag],
            ) if t == ty && *value == step && !used.contains(flag) && resolve(*lhs) == *param => {
                (true, *rhs)
            }
            _ => return None,
        };
        let coef = |v: ValueId| -> Option<Coef> {
            let v = resolve(v);
            match def(v) {
                Some(Inst::Const {
                    ty: t,
                    value: value @ (Constant::Int(_) | Constant::U128(_)),
                }) if t == ty => Some(Coef::Const(value.clone())),
                _ => available(v).map(Coef::Value),
            }
        };
        let xform = |v: ValueId| -> Option<Ext> {
            let v = resolve(v);
            if v == iv {
                return (*ty == iv_ty).then_some(Ext::Same);
            }
            match def(v) {
                Some(Inst::Cast {
                    op,
                    src_ty,
                    dst_ty,
                    operand,
                }) if in_loop(v) && *src_ty == iv_ty && dst_ty == ty && resolve(*operand) == iv => {
                    match (op, exit) {
                        (CastOp::ZExt, Exit::Ult) if bits > bits_iv => Some(Ext::Zext),
                        (CastOp::SExt, Exit::Slt) if bits > bits_iv => Some(Ext::Sext),
                        _ => None,
                    }
                }
                _ => None,
            }
        };
        let t = resolve(term);
        let (a, b) = if let Some(x) = xform(t) {
            (Some((Coef::One, x)), None)
        } else if let Some(c) = coef(t) {
            (None, Some(c))
        } else {
            match def(t) {
                Some(Inst::BinOp {
                    op: BinOp::Mul,
                    ty: mt,
                    lhs,
                    rhs,
                }) if mt == ty && in_loop(t) => {
                    match (xform(*lhs), coef(*rhs), coef(*lhs), xform(*rhs)) {
                        (Some(x), Some(c), _, _) | (_, _, Some(c), Some(x)) => (Some((c, x)), None),
                        _ => return None,
                    }
                }
                _ => return None,
            }
        };
        if j == k && !(a.is_none() && !subtract && b == Some(Coef::Const(Constant::Int(1)))) {
            return None;
        }
        roles.push(Some(Accumulator { subtract, a, b }));
    }
    roles[k].as_ref()?;
    let defined = never_poison(func);
    for (j, role) in roles.iter().enumerate() {
        let Some(acc) = role else {
            continue;
        };
        let mut need = Vec::new();
        if j != k {
            need.push(init[j]);
        }
        if let Some((Coef::Value(v), _)) = &acc.a {
            need.push(*v);
        }
        if let Some(Coef::Value(v)) = &acc.b {
            need.push(*v);
        }
        if need.iter().any(|v| !defined.contains(v)) {
            return None;
        }
        let ty = &header.params[j].1;
        for coef in [acc.a.as_ref().map(|(c, _)| c), acc.b.as_ref()]
            .into_iter()
            .flatten()
        {
            if let Coef::Value(v) = coef
                && types.get(v) != Some(ty)
            {
                return None;
            }
        }
    }
    // ---- The closed form.
    let mut fresh = next;
    let mut nodes_out: Vec<InstrNode> = Vec::new();
    let mut emit = |inst: Inst| {
        let v = ValueId::new(fresh);
        fresh += 1;
        nodes_out.push(InstrNode::new(inst).with_results([v]));
        v
    };
    let i0 = init[k];
    let bin = |op: BinOp, ty: &Ty, lhs: ValueId, rhs: ValueId| Inst::BinOp {
        op,
        ty: ty.clone(),
        lhs,
        rhs,
    };
    let cast = |op: CastOp, src: &Ty, dst: &Ty, operand: ValueId| Inst::Cast {
        op,
        src_ty: src.clone(),
        dst_ty: dst.clone(),
        operand,
    };
    let konst = |ty: &Ty, value: Constant| Inst::Const {
        ty: ty.clone(),
        value,
    };
    let n = match exit {
        Exit::Ult | Exit::Slt => {
            let c = emit(Inst::ICmp {
                op: if exit == Exit::Ult {
                    ICmpOp::Ult
                } else {
                    ICmpOp::Slt
                },
                ty: iv_ty.clone(),
                lhs: i0,
                rhs: bound,
            });
            let d = emit(bin(BinOp::Sub, &iv_ty, bound, i0));
            let z = emit(konst(&iv_ty, Constant::Int(0)));
            emit(Inst::Select {
                ty: iv_ty.clone(),
                cond: c,
                then_val: d,
                else_val: z,
            })
        }
        Exit::Ne => emit(bin(BinOp::Sub, &iv_ty, bound, i0)),
    };
    let mut finals = Vec::with_capacity(roles.len());
    let mut widened: Vec<(Ty, ValueId)> = Vec::new();
    let mut sums: Vec<(Ty, Ext, ValueId)> = Vec::new();
    for (j, role) in roles.iter().enumerate() {
        let Some(acc) = role else {
            finals.push(init[j]);
            continue;
        };
        let ty = header.params[j].1.clone();
        if j == k {
            finals.push(emit(bin(BinOp::Add, &ty, i0, n)));
            continue;
        }
        let scale = |emit: &mut dyn FnMut(Inst) -> ValueId, coef: &Coef, v: ValueId| match coef {
            Coef::One | Coef::Const(Constant::Int(1)) => v,
            Coef::Value(c) => emit(bin(BinOp::Mul, &ty, *c, v)),
            Coef::Const(value) => {
                let c = emit(konst(&ty, value.clone()));
                emit(bin(BinOp::Mul, &ty, c, v))
            }
        };
        let mut terms = Vec::new();
        if acc.a.is_some() || acc.b.is_some() {
            // `N` at `ty` and the induction variable's sum `S` are emitted
            // once per type (and extension) and shared by later accumulators.
            let na = if ty == iv_ty {
                n
            } else if let Some((_, v)) = widened.iter().find(|(t, _)| *t == ty) {
                *v
            } else {
                let v = emit(cast(CastOp::ZExt, &iv_ty, &ty, n));
                widened.push((ty.clone(), v));
                v
            };
            if let Some((coef, ext)) = &acc.a {
                let sum =
                    if let Some((_, _, v)) = sums.iter().find(|(t, e, _)| *t == ty && e == ext) {
                        *v
                    } else {
                        let x0 = match ext {
                            Ext::Same => i0,
                            Ext::Zext => emit(cast(CastOp::ZExt, &iv_ty, &ty, i0)),
                            Ext::Sext => emit(cast(CastOp::SExt, &iv_ty, &ty, i0)),
                        };
                        let one = emit(konst(&ty, Constant::Int(1)));
                        let odd = emit(bin(BinOp::And, &ty, na, one));
                        let even = emit(bin(BinOp::Sub, &ty, na, odd));
                        let half = emit(bin(BinOp::LShr, &ty, even, one));
                        let less = emit(bin(BinOp::Sub, &ty, na, one));
                        let other = emit(bin(BinOp::Add, &ty, less, odd));
                        let tri = emit(bin(BinOp::Mul, &ty, half, other));
                        let base = emit(bin(BinOp::Mul, &ty, na, x0));
                        let sum = emit(bin(BinOp::Add, &ty, base, tri));
                        sums.push((ty.clone(), *ext, sum));
                        sum
                    };
                terms.push(scale(&mut emit, coef, sum));
            }
            if let Some(coef) = &acc.b {
                terms.push(scale(&mut emit, coef, na));
            }
        }
        let mut value = init[j];
        for term in terms {
            let op = if acc.subtract { BinOp::Sub } else { BinOp::Add };
            value = emit(bin(op, &ty, value, term));
        }
        finals.push(value);
    }
    let values: Vec<ValueId> = (next..fresh).map(ValueId::new).collect();
    // ---- The rewrite.
    let mut out = func.clone();
    let mut removed: HashSet<ValueId> = HashSet::new();
    for b in out
        .blocks
        .iter()
        .filter(|b| lp.body.contains(&b.id) && b.id != lp.header)
    {
        removed.extend(b.params.iter().map(|(v, _)| *v));
        for node in &b.body {
            removed.extend(node.results.iter().copied());
        }
    }
    let pre = out.blocks.iter_mut().find(|b| b.id == lp.preheader)?;
    let at = pre.body.len() - 1;
    if let Some(Inst::Br { args, .. }) = pre.body.last_mut().map(|n| &mut n.inst) {
        *args = finals;
    }
    for (i, node) in nodes_out.into_iter().enumerate() {
        pre.body.insert(at + i, node);
    }
    let h = out.blocks.iter_mut().find(|b| b.id == lp.header)?;
    if let Some(last) = h.body.last_mut() {
        last.inst = Inst::Br {
            target: exit_target,
            args: exit_args,
        };
    }
    out.blocks
        .retain(|b| !lp.body.contains(&b.id) || b.id == lp.header);
    drop_names(&mut out, &removed);
    Some((out, values))
}

/// Whether the loop's blocks other than its header contain a cycle.
fn has_inner_cycle(func: &Function, lp: &Loop) -> bool {
    let succs = |id: BlockId| -> Vec<BlockId> {
        func.blocks
            .iter()
            .find(|b| b.id == id)
            .and_then(|b| b.body.last())
            .map(|t| t.inst.successor_edges())
            .unwrap_or_default()
            .into_iter()
            .map(|e| e.target)
            .filter(|t| *t != lp.header && lp.body.contains(t))
            .collect()
    };
    // 0 unvisited, 1 on the stack, 2 done.
    let mut state: HashMap<BlockId, u8> = HashMap::new();
    for &start in &lp.body {
        if start == lp.header || state.contains_key(&start) {
            continue;
        }
        let mut stack = vec![(start, succs(start), 0usize)];
        state.insert(start, 1);
        while let Some((b, s, i)) = stack.pop() {
            if i < s.len() {
                let next = s[i];
                stack.push((b, s, i + 1));
                match state.get(&next) {
                    Some(1) => return true,
                    Some(_) => {}
                    None => {
                        state.insert(next, 1);
                        stack.push((next, succs(next), 0));
                    }
                }
            } else {
                state.insert(b, 2);
            }
        }
    }
    false
}

/// `pred` negated.
fn negate(pred: ICmpOp) -> ICmpOp {
    match pred {
        ICmpOp::Eq => ICmpOp::Ne,
        ICmpOp::Ne => ICmpOp::Eq,
        ICmpOp::Ult => ICmpOp::Uge,
        ICmpOp::Uge => ICmpOp::Ult,
        ICmpOp::Ule => ICmpOp::Ugt,
        ICmpOp::Ugt => ICmpOp::Ule,
        ICmpOp::Slt => ICmpOp::Sge,
        ICmpOp::Sge => ICmpOp::Slt,
        ICmpOp::Sle => ICmpOp::Sgt,
        ICmpOp::Sgt => ICmpOp::Sle,
    }
}

/// `pred` with its operands exchanged.
fn flip(pred: ICmpOp) -> ICmpOp {
    match pred {
        ICmpOp::Ult => ICmpOp::Ugt,
        ICmpOp::Ugt => ICmpOp::Ult,
        ICmpOp::Ule => ICmpOp::Uge,
        ICmpOp::Uge => ICmpOp::Ule,
        ICmpOp::Slt => ICmpOp::Sgt,
        ICmpOp::Sgt => ICmpOp::Slt,
        ICmpOp::Sle => ICmpOp::Sge,
        ICmpOp::Sge => ICmpOp::Sle,
        other => other,
    }
}
