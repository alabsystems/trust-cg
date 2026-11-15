// trust-cg-irmid/passes/iv_sr.rs - induction-variable strength reduction
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Induction-variable strength reduction: the native lanes'
//! `trust_cg_opt::strength_reduce` (a multiply of the induction variable by
//! an invariant becomes an added stride) and `trust_cg_opt::ptr_iv_sr` (an
//! address `base + i * size` becomes a pointer induction variable) lifted
//! to trust-ir. The bridge computes an element address as integers,
//! `ptrtoint(base) + (i + k) * size`, a `mul` and two `add`s per access; the
//! value is linear in the induction variable `i` (`A * i + base + c`), so a
//! new header parameter `q` starting at `A * i0 + base` and stepping by
//! `A * s` with `i` holds `A * i + base` on every iteration, and each such
//! access becomes `q + c` (one `add`, or none).
//!
//! Per loop with a dedicated preheader and one back edge (from a `br`,
//! `condbr` or `switch`): the induction variables are the header parameters
//! stepping by a constant `s` whose initial value has their integer type and
//! is never poison; a loop value of an integer type as wide as one, read
//! (through constants, copies, same-width casts, the address casts, `add`,
//! `sub`, and `mul` and `shl` by constants) as `A * i + R + c` with `A` not 0,
//! 1 or -1, `R` a never-poison value from before the loop (a pointer or an
//! integer of the width) or none, is replaced when some use of it is not
//! itself replaced; values sharing `(i, A, R, type)` share one new
//! parameter. The witness names each strand's parameter, scale, root, fresh
//! values and replaced values with their offsets; the checker
//! (`trust_ir_mid_tv_ivsr.rs`) reads every value again with its own code and
//! rebuilds the rewrite, the inductive invariant being an identity of
//! arithmetic modulo the width.

use std::collections::{BTreeMap, HashMap, HashSet};

use trust_cg_verify::trust_ir_mid_tv::{IvSrLoop, IvSrStrand, IvSrUse, IvSrWitness, PassWitness};
use trust_ir::{BinOp, BlockId, CastOp, Constant, Function, Inst, InstrNode, Ty, ValueId};

use super::loops::{Loop, def_blocks, first_free_value, never_poison, rewritable_loops};
use super::{MidPass, PassContext, int_shape, value_types};

pub(crate) struct IvStrength;

/// The evidence name of strength reduction.
pub(crate) const IV_SR_NAME: &str = "iv_sr";

impl MidPass for IvStrength {
    fn name(&self) -> &'static str {
        IV_SR_NAME
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let mut cur = func.clone();
        let mut next = first_free_value(func);
        let mut loops = Vec::new();
        let headers: Vec<BlockId> = rewritable_loops(func).iter().map(|l| l.header).collect();
        for header in headers {
            let Some(lp) = rewritable_loops(&cur)
                .into_iter()
                .find(|l| l.header == header)
            else {
                continue;
            };
            if let Some((out, claim, used)) = reduce(&cur, cx.pointer_bits, &lp, next) {
                cur = out;
                next += used;
                loops.push(claim);
            }
        }
        if loops.is_empty() {
            return None;
        }
        Some((cur, PassWitness::IvSr(IvSrWitness { loops })))
    }
}

fn mask(bits: u32) -> u128 {
    if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

/// `a * x + sum(b * r) + c` modulo `2^bits` (`r`: nonzero coefficients).
#[derive(Debug, Clone, PartialEq, Eq)]
struct Lin {
    a: u128,
    x: Option<ValueId>,
    r: BTreeMap<ValueId, u128>,
    c: u128,
    bits: u32,
}

impl Lin {
    fn times(&self, k: u128) -> Lin {
        let m = mask(self.bits);
        Lin {
            a: self.a.wrapping_mul(k) & m,
            x: self.x,
            r: self
                .r
                .iter()
                .map(|(v, b)| (*v, b.wrapping_mul(k) & m))
                .filter(|(_, b)| *b != 0)
                .collect(),
            c: self.c.wrapping_mul(k) & m,
            bits: self.bits,
        }
    }
}

struct Eval<'f> {
    pb: u32,
    defs: HashMap<ValueId, &'f Inst>,
    def_at: HashMap<ValueId, BlockId>,
    body: &'f HashSet<BlockId>,
    params: HashSet<ValueId>,
    types: &'f HashMap<ValueId, Ty>,
}

impl Eval<'_> {
    fn width(&self, ty: &Ty) -> Option<u32> {
        int_shape(ty, self.pb).map(|(b, _)| b).or(matches!(
            ty,
            Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
        )
        .then_some(self.pb))
    }

    fn eval(&self, v: ValueId, depth: u32) -> Option<Lin> {
        if depth > 64 {
            return None;
        }
        let bits = self.width(self.types.get(&v)?)?;
        if self.params.contains(&v) {
            return Some(Lin {
                a: 1,
                x: Some(v),
                r: BTreeMap::new(),
                c: 0,
                bits,
            });
        }
        let outside = !self.body.contains(self.def_at.get(&v)?);
        let leaf = || {
            outside.then(|| Lin {
                a: 0,
                x: None,
                r: BTreeMap::from([(v, 1)]),
                c: 0,
                bits,
            })
        };
        let Some(inst) = self.defs.get(&v) else {
            return leaf();
        };
        let m = mask(bits);
        let ib = |ty: &Ty| int_shape(ty, self.pb).map(|(b, _)| b);
        let sub = |x: ValueId| self.eval(x, depth + 1).filter(|l| l.bits == bits);
        let k_of = |x: ValueId| {
            sub(x)
                .filter(|l| l.x.is_none() && l.r.is_empty())
                .map(|l| l.c)
        };
        let out = match inst {
            Inst::Const {
                ty,
                value: Constant::Int(k),
            } if ib(ty) == Some(bits) => Some(Lin {
                a: 0,
                x: None,
                r: BTreeMap::new(),
                c: (*k as u128) & m,
                bits,
            }),
            Inst::Copy { operand, .. } => sub(*operand),
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => {
                let same = match op {
                    CastOp::Bitcast => ib(src_ty).is_some() && ib(src_ty) == ib(dst_ty),
                    CastOp::PtrToInt => ib(dst_ty) == Some(self.pb),
                    CastOp::IntToPtr => ib(src_ty) == Some(self.pb),
                    CastOp::PtrToPtr => true,
                    _ => false,
                };
                if same { sub(*operand) } else { None }
            }
            Inst::BinOp { op, ty, lhs, rhs } if ib(ty) == Some(bits) => match op {
                BinOp::Add | BinOp::Sub => match (sub(*lhs), sub(*rhs)) {
                    (Some(p), Some(q)) => {
                        let q = if *op == BinOp::Sub { q.times(m) } else { q };
                        let x = match (p.x, q.x) {
                            (Some(a), Some(b)) if a != b => None,
                            (a, b) => Some(a.or(b)),
                        };
                        x.map(|x| {
                            let mut r = p.r.clone();
                            for (v, b) in &q.r {
                                let e = r.entry(*v).or_insert(0);
                                *e = e.wrapping_add(*b) & m;
                            }
                            r.retain(|_, b| *b != 0);
                            Lin {
                                a: p.a.wrapping_add(q.a) & m,
                                x,
                                r,
                                c: p.c.wrapping_add(q.c) & m,
                                bits,
                            }
                        })
                    }
                    _ => None,
                },
                BinOp::Mul => match (k_of(*lhs), k_of(*rhs)) {
                    (_, Some(k)) => sub(*lhs).map(|p| p.times(k)),
                    (Some(k), None) => sub(*rhs).map(|p| p.times(k)),
                    _ => None,
                },
                BinOp::Shl => match k_of(*rhs) {
                    Some(k) if k < u128::from(bits) => sub(*lhs).map(|p| p.times(1u128 << k)),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        };
        out.map(|mut l| {
            if l.a == 0 {
                l.x = None;
            }
            l
        })
        .or_else(leaf)
    }
}

/// The canonical constant of `raw` at the integer type `ty`.
fn spell(ty: &Ty, bits: u32, raw: u128) -> Constant {
    let shift = 128 - bits;
    if ty.is_signed() {
        Constant::Int(((raw << shift) as i128) >> shift)
    } else {
        Constant::Int(raw as i128)
    }
}

/// One strand being built: `(iv, scale, root, type)` and its uses.
struct Strand {
    iv: ValueId,
    iv_ty: Ty,
    init: ValueId,
    step: u128,
    bits: u32,
    scale: u128,
    roots: Vec<(ValueId, u128)>,
    ty: Ty,
    uses: Vec<(ValueId, u128)>,
}

/// The strength reduction of `lp` in `func` with fresh values from `next`:
/// the rewritten function, the loop's claim and the values it used.
fn reduce(func: &Function, pb: u32, lp: &Loop, next: u32) -> Option<(Function, IvSrLoop, u32)> {
    if lp.back_edges != 1 {
        return None;
    }
    let pos = |id: BlockId| func.blocks.iter().position(|b| b.id == id);
    let h = pos(lp.header)?;
    let pre = pos(lp.preheader)?;
    let latch = func.blocks.iter().position(|b| {
        lp.body.contains(&b.id)
            && b.body.last().is_some_and(|t| {
                t.inst
                    .successor_edges()
                    .iter()
                    .any(|e| e.target == lp.header)
            })
    })?;
    if !matches!(
        func.blocks[latch].body.last()?.inst,
        Inst::Br { .. } | Inst::CondBr { .. } | Inst::Switch { .. }
    ) {
        return None;
    }
    let Inst::Br { args: init, .. } = &func.blocks[pre].body.last()?.inst else {
        return None;
    };
    let back: Vec<ValueId> = func.blocks[latch]
        .body
        .last()?
        .inst
        .successor_edges()
        .into_iter()
        .find(|e| e.target == lp.header)?
        .args
        .to_vec();
    let params = &func.blocks[h].params;
    if init.len() != params.len() || back.len() != params.len() {
        return None;
    }
    let types = value_types(func);
    let safe = never_poison(func);
    let mut defs: HashMap<ValueId, &Inst> = HashMap::new();
    let mut uses_of: HashMap<ValueId, Vec<ValueId>> = HashMap::new();
    let mut used_outright: HashSet<ValueId> = HashSet::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        if let [r] = node.results.as_slice() {
            defs.insert(*r, &node.inst);
        }
        let user = node.results.first().copied();
        node.inst.visit_value_operands(|v| match user {
            Some(u) if node.results.len() == 1 => uses_of.entry(v).or_default().push(u),
            _ => {
                used_outright.insert(v);
            }
        });
    }
    let eval = Eval {
        pb,
        defs,
        def_at: def_blocks(func),
        body: &lp.body,
        params: params.iter().map(|(v, _)| *v).collect(),
        types: &types,
    };
    // ---- Induction variables.
    let mut ivs: HashMap<ValueId, (Ty, ValueId, u128, u32)> = HashMap::new();
    for (j, (p, ty)) in params.iter().enumerate() {
        let Some((bits, _)) = int_shape(ty, pb) else {
            continue;
        };
        let Some(step) = eval.eval(back[j], 0) else {
            continue;
        };
        if step.a == 1
            && step.x == Some(*p)
            && step.r.is_empty()
            && step.bits == bits
            && types.get(&init[j]) == Some(ty)
            && safe.contains(&init[j])
        {
            ivs.insert(*p, (ty.clone(), init[j], step.c, bits));
        }
    }
    if ivs.is_empty() {
        return None;
    }
    // ---- Candidates.
    let mut candidates: HashMap<ValueId, Lin> = HashMap::new();
    for block in func.blocks.iter().filter(|b| lp.body.contains(&b.id)) {
        for node in &block.body {
            let [v] = node.results.as_slice() else {
                continue;
            };
            if !matches!(
                node.inst,
                Inst::BinOp {
                    op: BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Shl,
                    ..
                } | Inst::Cast { .. }
                    | Inst::Copy { .. }
            ) {
                continue;
            }
            let Some(ty) = types.get(v) else {
                continue;
            };
            let Some((bits, _)) = int_shape(ty, pb) else {
                continue;
            };
            let Some(l) = eval.eval(*v, 0) else {
                continue;
            };
            let Some(x) = l.x else {
                continue;
            };
            let Some((_, _, _, iv_bits)) = ivs.get(&x) else {
                continue;
            };
            let m = mask(bits);
            if *iv_bits != bits || l.bits != bits || l.a == 0 || l.a == 1 || l.a == m {
                continue;
            }
            let root_ok = l.r.keys().all(|r| {
                safe.contains(r)
                    && types.get(r).is_some_and(|t| {
                        int_shape(t, pb).is_some_and(|(b, _)| b == bits)
                            || (bits == pb
                                && matches!(
                                    t,
                                    Ty::Ptr
                                        | Ty::PtrConst(_)
                                        | Ty::PtrMut(_)
                                        | Ty::Ref(_)
                                        | Ty::RefMut(_)
                                ))
                    })
            });
            if root_ok {
                candidates.insert(*v, l.clone());
            }
        }
    }
    // Keep a candidate some use of which is not a candidate itself.
    let kept: Vec<ValueId> = func
        .blocks
        .iter()
        .filter(|b| lp.body.contains(&b.id))
        .flat_map(|b| &b.body)
        .filter_map(|n| n.results.first().copied())
        .filter(|v| {
            candidates.contains_key(v)
                && (used_outright.contains(v)
                    || uses_of
                        .get(v)
                        .is_some_and(|us| us.iter().any(|u| !candidates.contains_key(u))))
        })
        .collect();
    if kept.is_empty() {
        return None;
    }
    let mut strands: Vec<Strand> = Vec::new();
    for v in kept {
        let l = candidates[&v].clone();
        let x = l.x?;
        let roots: Vec<(ValueId, u128)> = l.r.iter().map(|(v, b)| (*v, *b)).collect();
        let ty = types.get(&v)?.clone();
        let (iv_ty, i0, step, _) = ivs.get(&x)?.clone();
        if let Some(s) = strands
            .iter_mut()
            .find(|s| s.iv == x && s.scale == l.a && s.roots == roots && s.ty == ty)
        {
            s.uses.push((v, l.c));
        } else {
            strands.push(Strand {
                iv: x,
                iv_ty,
                init: i0,
                step,
                bits: l.bits,
                scale: l.a,
                roots,
                ty,
                uses: vec![(v, l.c)],
            });
        }
    }
    // ---- The rewrite, in the checker's order.
    let mut fresh = next;
    let mut new = || {
        let v = ValueId::new(fresh);
        fresh += 1;
        v
    };
    let mut out = func.clone();
    let mut claims = Vec::new();
    let mut replace: HashMap<ValueId, Vec<InstrNode>> = HashMap::new();
    let mut pre_nodes: Vec<(Vec<InstrNode>, ValueId)> = Vec::new();
    let mut step_nodes: Vec<(Vec<InstrNode>, ValueId)> = Vec::new();
    for s in &strands {
        let m = mask(s.bits);
        let q = new();
        let mut init_vals = Vec::new();
        let mut pre: Vec<InstrNode> = Vec::new();
        let push = |pre: &mut Vec<InstrNode>, inst: Inst, v: ValueId| {
            pre.push(InstrNode::new(inst).with_results([v]));
        };
        let x0 = if s.iv_ty == s.ty {
            s.init
        } else {
            let v = new();
            init_vals.push(v);
            push(
                &mut pre,
                Inst::Cast {
                    op: CastOp::Bitcast,
                    src_ty: s.iv_ty.clone(),
                    dst_ty: s.ty.clone(),
                    operand: s.init,
                },
                v,
            );
            v
        };
        let a = new();
        init_vals.push(a);
        push(
            &mut pre,
            Inst::Const {
                ty: s.ty.clone(),
                value: spell(&s.ty, s.bits, s.scale),
            },
            a,
        );
        let mul = new();
        init_vals.push(mul);
        push(
            &mut pre,
            Inst::BinOp {
                op: BinOp::Mul,
                ty: s.ty.clone(),
                lhs: x0,
                rhs: a,
            },
            mul,
        );
        let mut q0 = mul;
        for &(r, b) in &s.roots {
            let rty = types.get(&r)?;
            let as_t = if *rty == s.ty {
                r
            } else if int_shape(rty, pb).is_some() {
                let v = new();
                init_vals.push(v);
                push(
                    &mut pre,
                    Inst::Cast {
                        op: CastOp::Bitcast,
                        src_ty: rty.clone(),
                        dst_ty: s.ty.clone(),
                        operand: r,
                    },
                    v,
                );
                v
            } else {
                let p = if *rty == Ty::Ptr {
                    r
                } else {
                    let v = new();
                    init_vals.push(v);
                    push(
                        &mut pre,
                        Inst::Cast {
                            op: CastOp::PtrToPtr,
                            src_ty: rty.clone(),
                            dst_ty: Ty::Ptr,
                            operand: r,
                        },
                        v,
                    );
                    v
                };
                let v = new();
                init_vals.push(v);
                push(
                    &mut pre,
                    Inst::Cast {
                        op: CastOp::PtrToInt,
                        src_ty: Ty::Ptr,
                        dst_ty: s.ty.clone(),
                        operand: p,
                    },
                    v,
                );
                v
            };
            let term = if b == 1 {
                as_t
            } else {
                let k = new();
                init_vals.push(k);
                push(
                    &mut pre,
                    Inst::Const {
                        ty: s.ty.clone(),
                        value: spell(&s.ty, s.bits, b),
                    },
                    k,
                );
                let v = new();
                init_vals.push(v);
                push(
                    &mut pre,
                    Inst::BinOp {
                        op: BinOp::Mul,
                        ty: s.ty.clone(),
                        lhs: as_t,
                        rhs: k,
                    },
                    v,
                );
                v
            };
            let v = new();
            init_vals.push(v);
            push(
                &mut pre,
                Inst::BinOp {
                    op: BinOp::Add,
                    ty: s.ty.clone(),
                    lhs: q0,
                    rhs: term,
                },
                v,
            );
            q0 = v;
        }
        pre_nodes.push((pre, q0));
        let (d, q1) = (new(), new());
        step_nodes.push((
            vec![
                InstrNode::new(Inst::Const {
                    ty: s.ty.clone(),
                    value: spell(&s.ty, s.bits, s.scale.wrapping_mul(s.step) & m),
                })
                .with_results([d]),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: s.ty.clone(),
                    lhs: q,
                    rhs: d,
                })
                .with_results([q1]),
            ],
            q1,
        ));
        let mut uses = Vec::new();
        for &(v, c) in &s.uses {
            let at = func
                .blocks
                .iter()
                .flat_map(|b| &b.body)
                .find(|n| n.results.as_slice() == [v])?;
            let mut nodes = Vec::new();
            let mut node = at.clone();
            let constant = if c == 0 {
                node.inst = Inst::Copy {
                    ty: s.ty.clone(),
                    operand: q,
                };
                None
            } else {
                let k = new();
                let mut kn = at.clone();
                kn.inst = Inst::Const {
                    ty: s.ty.clone(),
                    value: spell(&s.ty, s.bits, c),
                };
                kn.results = vec![k];
                nodes.push(kn);
                node.inst = Inst::BinOp {
                    op: BinOp::Add,
                    ty: s.ty.clone(),
                    lhs: q,
                    rhs: k,
                };
                Some(k)
            };
            nodes.push(node);
            replace.insert(v, nodes);
            uses.push(IvSrUse {
                value: v,
                offset: c,
                constant,
            });
        }
        claims.push(IvSrStrand {
            param: q,
            ty: s.ty.clone(),
            iv: s.iv,
            scale: s.scale,
            roots: s.roots.clone(),
            init: init_vals,
            step: vec![d, q1],
            uses,
        });
    }
    for block in &mut out.blocks {
        let body = std::mem::take(&mut block.body);
        block.body = body
            .into_iter()
            .flat_map(|n| {
                n.results
                    .first()
                    .filter(|_| n.results.len() == 1)
                    .and_then(|v| replace.remove(v))
                    .unwrap_or_else(|| vec![n])
            })
            .collect();
    }
    for (((pre_list, q0), (steps, q1)), claim) in pre_nodes.into_iter().zip(step_nodes).zip(&claims)
    {
        out.blocks[h].params.push((claim.param, claim.ty.clone()));
        let pb_ = &mut out.blocks[pre].body;
        let at = pb_.len() - 1;
        for (k, n) in pre_list.into_iter().enumerate() {
            pb_.insert(at + k, n);
        }
        if let Some(Inst::Br { args, .. }) = pb_.last_mut().map(|n| &mut n.inst) {
            args.push(q0);
        }
        let lb = &mut out.blocks[latch].body;
        let at = lb.len() - 1;
        for (k, n) in steps.into_iter().enumerate() {
            lb.insert(at + k, n);
        }
        if let Some(last) = lb.last_mut() {
            let header = lp.header;
            let add = |t: &BlockId, a: &mut Vec<ValueId>| {
                if *t == header {
                    a.push(q1);
                }
            };
            match &mut last.inst {
                Inst::Br { target, args } => add(target, args),
                Inst::CondBr {
                    then_target,
                    then_args,
                    else_target,
                    else_args,
                    ..
                } => {
                    add(then_target, then_args);
                    add(else_target, else_args);
                }
                Inst::Switch {
                    default,
                    default_args,
                    cases,
                    ..
                } => {
                    add(default, default_args);
                    for case in cases {
                        add(&case.target, &mut case.args);
                    }
                }
                _ => {}
            }
        }
    }
    Some((
        out,
        IvSrLoop {
            header: lp.header,
            strands: claims,
        },
        fresh - next,
    ))
}
