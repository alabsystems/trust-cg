// trust-cg-verify/trust_ir_mid_tv_ivsr.rs - the strength reduction checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The checker of the mid-end's induction-variable strength reduction
//! ([`IvSrWitness`]), the trust-ir form of the native machine passes
//! `trust-cg-opt/src/strength_reduce.rs` (a multiply of the induction
//! variable by a constant becomes an added stride) and `ptr_iv_sr.rs` (an
//! address `base + i * size` becomes a pointer induction variable),
//! restated over trust-ir's semantics. Everything is derived here from the
//! SOURCE function with this module's own code.
//!
//! **The loop** is the natural loop of the named header `H`
//! ([`super::loops`]: dominated by `H`, entered only from a preheader `P`
//! ending in `br H(init)`) with exactly one back edge, from the LATCH, a
//! `br`, `condbr` or `switch`.
//!
//! **Linear values.** A value is LINEAR when this module reads it, at a
//! width `w`, as `a * x + b1 * r1 + ... + bn * rn + c` modulo `2^w`: `x` a
//! parameter of `H` (or none), `a`, the `bj` and `c` constants, and the `rj`
//! ROOTS, values defined outside the loop. The reading goes through integer
//! constants, `copy`, a same-width integer `bitcast`, `ptrtoint`/`inttoptr`
//! between pointers and integers of pointer width and `ptrtoptr` (each the
//! identity on the bits, in the reference interpreter and on wasm), `add`
//! and `sub` of linear values (of at most one parameter), and `mul` and
//! `shl` by a constant (the shift below the width); a value defined outside
//! the loop that none of these peels is a root. Every step is an identity
//! of arithmetic modulo `2^w`.
//!
//! **The induction variable** `i` is a parameter of `H` whose back-edge
//! argument reads as `i + s` (`a = 1`, no root): on visit `k` of `H` it holds
//! `i0 + k * s`, with `i0` `P`'s argument, which must have `i`'s integer
//! type.
//!
//! **A strand** names a new parameter `q` of `H` of an integer type `T` as
//! wide as `i`, a scale `A`, its roots `R = b1 * r1 + ...` (in ascending
//! value order, each `rj` pointer-like or an integer as wide as `T`, each
//! `bj` nonzero) and the loop values it replaces, each with an offset `c`:
//! every one must have type `T` and read as `A * i + R + c`. The rewrite
//! (fresh values in this order, from the witness):
//!
//! * at the end of `P`: `i0` as a `T` (itself, or its `bitcast`), `const T
//!   A`, their `mul`; then per root `rj` as a `T` (itself, its `bitcast`,
//!   or `ptrtoint` to `T` of it, through `ptrtoptr` to `ptr` for another
//!   pointer type), times `bj` when it is not 1 (`const T bj` and a `mul`),
//!   added to the sum so far: that is `q`'s initial value `q0`, appended to
//!   `P`'s arguments;
//! * at the end of the latch: `const T (A * s)` and `add T q, it`, appended
//!   to the back edge's arguments;
//! * each replaced value's instruction becomes `copy T q` (offset 0) or
//!   `add T q, c` after a fresh `const T c`.
//!
//! On visit `k`, `q = A * i0 + R + k * A * s = A * (i0 + k * s) + R`, which is
//! `A * i + R` modulo `2^w` (the inductive invariant: it holds at entry, and
//! the step preserves it, by distributivity in the ring of integers modulo
//! `2^w`), so each replaced value equals `q + c` where the source computed
//! it. The preheader's instructions run where the source may not compute
//! them (the loop may run zero times): they raise nothing on operands that
//! are never poison, which `i0` and every root must be ([`super::loops`]'
//! `never_poison`). Exact: the replaced instructions are integer `add`,
//! `sub`, `mul`, `shl`, casts and copies, which the target computes as the
//! same value; their operands stay for dead-code elimination.

use std::collections::{BTreeMap, HashMap, HashSet};

use trust_ir::{BinOp, BlockId, CastOp, Constant, Function, Inst, InstrNode, Ty, ValueId};

use super::loops::{def_blocks, loop_shape, never_poison, refuse, value_types};
use super::{MidTvError, WitnessVerdict, int_shape, used_values};

/// One replaced loop value: `value` becomes `q + offset`; `constant` names
/// the fresh `const` defining the offset (none for offset 0).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IvSrUse {
    pub value: ValueId,
    pub offset: u128,
    pub constant: Option<ValueId>,
}

/// One new induction parameter `param` of type `ty`, equal to `scale * iv +
/// sum(coefficient * root)` on every visit (`roots` in ascending value
/// order); `init` and `step` name the fresh values of its initial
/// computation and of its step, in the module docs' order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IvSrStrand {
    pub param: ValueId,
    pub ty: Ty,
    pub iv: ValueId,
    pub scale: u128,
    pub roots: Vec<(ValueId, u128)>,
    pub init: Vec<ValueId>,
    pub step: Vec<ValueId>,
    pub uses: Vec<IvSrUse>,
}

/// The strands of the loop at `header`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IvSrLoop {
    pub header: BlockId,
    pub strands: Vec<IvSrStrand>,
}

/// Strength reduction's claim, applied loop by loop.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct IvSrWitness {
    pub loops: Vec<IvSrLoop>,
}

impl IvSrWitness {
    /// Values replaced.
    pub fn rewrite_count(&self) -> usize {
        self.loops
            .iter()
            .flat_map(|l| &l.strands)
            .map(|s| s.uses.len())
            .sum()
    }
}

fn ones(bits: u32) -> u128 {
    if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

/// `a * x + sum(b * r) + c` modulo `2^bits` (module docs); `r` holds the
/// nonzero coefficients by root.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Linear {
    a: u128,
    x: Option<ValueId>,
    r: BTreeMap<ValueId, u128>,
    c: u128,
    bits: u32,
}

impl Linear {
    /// `self * k` modulo `2^bits`.
    fn scaled(self, k: u128) -> Self {
        let m = ones(self.bits);
        let r = self
            .r
            .into_iter()
            .map(|(v, b)| (v, b.wrapping_mul(k) & m))
            .filter(|(_, b)| *b != 0)
            .collect();
        Self {
            a: self.a.wrapping_mul(k) & m,
            x: self.x,
            r,
            c: self.c.wrapping_mul(k) & m,
            bits: self.bits,
        }
    }
}

struct Reading<'f> {
    func: &'f Function,
    pointer_bits: u32,
    at: HashMap<ValueId, (usize, usize)>,
    blocks: HashMap<ValueId, usize>,
    body: &'f HashSet<usize>,
    header_params: HashSet<ValueId>,
    types: HashMap<ValueId, Ty>,
}

impl Reading<'_> {
    fn width(&self, ty: &Ty) -> Option<u32> {
        int_shape(ty, self.pointer_bits)
            .map(|(b, _)| b)
            .or(matches!(
                ty,
                Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
            )
            .then_some(self.pointer_bits))
    }

    fn read(&self, v: ValueId, depth: usize) -> Option<Linear> {
        if depth > 64 {
            return None;
        }
        let bits = self.width(self.types.get(&v)?)?;
        if self.header_params.contains(&v) {
            return Some(Linear {
                a: 1,
                x: Some(v),
                r: BTreeMap::new(),
                c: 0,
                bits,
            });
        }
        let inside = self.body.contains(self.blocks.get(&v)?);
        let root = || {
            (!inside).then(|| Linear {
                a: 0,
                x: None,
                r: BTreeMap::from([(v, 1)]),
                c: 0,
                bits,
            })
        };
        let Some(&(bi, ni)) = self.at.get(&v) else {
            return root();
        };
        let m = ones(bits);
        let sub = |x: ValueId| self.read(x, depth + 1).filter(|l| l.bits == bits);
        let konst = |x: ValueId| {
            sub(x)
                .filter(|l| l.x.is_none() && l.r.is_empty())
                .map(|l| l.c)
        };
        let ibits = |ty: &Ty| int_shape(ty, self.pointer_bits).map(|(b, _)| b);
        let found = match &self.func.blocks[bi].body[ni].inst {
            Inst::Const {
                ty,
                value: Constant::Int(k),
            } if ibits(ty) == Some(bits) => Some(Linear {
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
                let identity = match op {
                    CastOp::Bitcast => ibits(src_ty).is_some() && ibits(src_ty) == ibits(dst_ty),
                    CastOp::PtrToInt => ibits(dst_ty) == Some(self.pointer_bits),
                    CastOp::IntToPtr => ibits(src_ty) == Some(self.pointer_bits),
                    CastOp::PtrToPtr => true,
                    _ => false,
                };
                if identity { sub(*operand) } else { None }
            }
            Inst::BinOp { op, ty, lhs, rhs } if ibits(ty) == Some(bits) => match op {
                BinOp::Add | BinOp::Sub => {
                    let (p, q) = (sub(*lhs)?, sub(*rhs)?);
                    let x = match (p.x, q.x) {
                        (Some(a), Some(b)) if a != b => return root(),
                        (a, b) => a.or(b),
                    };
                    let q = if *op == BinOp::Sub { q.scaled(m) } else { q };
                    let mut r = p.r;
                    for (v, b) in q.r {
                        let e = r.entry(v).or_insert(0);
                        *e = e.wrapping_add(b) & m;
                    }
                    r.retain(|_, b| *b != 0);
                    Some(Linear {
                        a: p.a.wrapping_add(q.a) & m,
                        x,
                        r,
                        c: p.c.wrapping_add(q.c) & m,
                        bits,
                    })
                }
                BinOp::Mul => match (konst(*lhs), konst(*rhs)) {
                    (_, Some(k)) => Some(sub(*lhs)?.scaled(k)),
                    (Some(k), None) => Some(sub(*rhs)?.scaled(k)),
                    _ => None,
                },
                BinOp::Shl => {
                    let k = konst(*rhs)?;
                    if k >= u128::from(bits) {
                        return root();
                    }
                    Some(sub(*lhs)?.scaled(1u128 << k))
                }
                _ => None,
            },
            _ => None,
        };
        found
            .map(|mut l| {
                if l.a == 0 {
                    l.x = None;
                }
                l
            })
            .or_else(root)
    }
}

/// The canonical spelling of `raw` at the integer type `ty` (`bits` wide).
fn spelled(ty: &Ty, bits: u32, raw: u128) -> Constant {
    if ty.is_signed() && bits < 128 && raw & (1u128 << (bits - 1)) != 0 {
        Constant::Int((raw | !ones(bits)) as i128)
    } else {
        Constant::Int(raw as i128)
    }
}

pub(super) fn rebuild_ivsr(
    pointer_bits: u32,
    source: &Function,
    witness: &IvSrWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let mut taken: HashSet<ValueId> = used_values(source);
    for block in &source.blocks {
        taken.extend(block.params.iter().map(|(v, _)| *v));
        for node in &block.body {
            taken.extend(node.results.iter().copied());
        }
    }
    if let Some(names) = &source.value_names {
        taken.extend(names.iter().map(|(v, _)| *v));
    }
    for lp in &witness.loops {
        for strand in &lp.strands {
            let fresh = std::iter::once(strand.param)
                .chain(strand.init.iter().copied())
                .chain(strand.step.iter().copied())
                .chain(strand.uses.iter().filter_map(|u| u.constant));
            for v in fresh {
                if !taken.insert(v) {
                    return Err(refuse(lp.header, format!("%{v} is not fresh")));
                }
            }
        }
    }
    let mut cur = source.clone();
    let mut verdict = WitnessVerdict::default();
    for lp in &witness.loops {
        reduce_loop(&mut cur, pointer_bits, lp)?;
        verdict.exact += lp.strands.iter().map(|s| s.uses.len()).sum::<usize>();
    }
    Ok((cur, verdict))
}

fn node(inst: Inst, result: ValueId) -> InstrNode {
    InstrNode::new(inst).with_results([result])
}

fn reduce_loop(cur: &mut Function, pointer_bits: u32, lp: &IvSrLoop) -> Result<(), MidTvError> {
    let header = lp.header;
    if lp.strands.is_empty() {
        return Err(refuse(header, "the loop claims no strand"));
    }
    let shape = loop_shape(cur, header)?;
    if shape.back_edges != 1 {
        return Err(refuse(header, "the loop has more than one back edge"));
    }
    let h = shape.header;
    let latch = shape
        .body
        .iter()
        .copied()
        .find(|&b| {
            cur.blocks[b].body.last().is_some_and(|t| {
                matches!(
                    t.inst,
                    Inst::Br { .. } | Inst::CondBr { .. } | Inst::Switch { .. }
                ) && t.inst.successor_edges().iter().any(|e| e.target == header)
            })
        })
        .ok_or_else(|| refuse(header, "the back edge is not a br, condbr or switch"))?;
    let params: Vec<ValueId> = cur.blocks[h].params.iter().map(|(v, _)| *v).collect();
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
    if init.len() != params.len() || back.len() != params.len() {
        return Err(refuse(
            header,
            "an edge into the header passes the wrong arity",
        ));
    }
    let types = value_types(cur);
    let defined = never_poison(cur);
    let mut at: HashMap<ValueId, (usize, usize)> = HashMap::new();
    for (bi, block) in cur.blocks.iter().enumerate() {
        for (ni, n) in block.body.iter().enumerate() {
            if let [r] = n.results.as_slice() {
                at.insert(*r, (bi, ni));
            }
        }
    }
    // Every claim is checked on the source before anything moves.
    struct Plan {
        pre: Vec<InstrNode>,
        q0: ValueId,
        step: Vec<InstrNode>,
        q1: ValueId,
        replaced: Vec<(usize, usize, Vec<InstrNode>)>,
    }
    let mut plans: Vec<Plan> = Vec::new();
    {
        let reading = Reading {
            func: cur,
            pointer_bits,
            at: at.clone(),
            blocks: def_blocks(cur),
            body: &shape.body,
            header_params: params.iter().copied().collect(),
            types: types.clone(),
        };
        let mut replaced_once: HashSet<ValueId> = HashSet::new();
        for strand in &lp.strands {
            let bad = |why: String| refuse(header, format!("strand %{}: {why}", strand.param));
            let j = params
                .iter()
                .position(|p| *p == strand.iv)
                .ok_or_else(|| bad("the induction variable is not a header parameter".into()))?;
            let iv_ty = &cur.blocks[h].params[j].1;
            let (bits, _) = int_shape(iv_ty, pointer_bits)
                .ok_or_else(|| bad("the induction variable is not an integer".into()))?;
            let t_bits = int_shape(&strand.ty, pointer_bits)
                .map(|(b, _)| b)
                .ok_or_else(|| bad("the strand's type is not an integer".into()))?;
            if t_bits != bits {
                return Err(bad(
                    "the strand's type is not as wide as the induction variable".into(),
                ));
            }
            let step = reading
                .read(back[j], 0)
                .filter(|l| l.a == 1 && l.x == Some(strand.iv) && l.r.is_empty())
                .ok_or_else(|| bad("the induction variable does not step by a constant".into()))?
                .c;
            if types.get(&init[j]) != Some(iv_ty) {
                return Err(bad(
                    "the induction variable's initial value has another type".into(),
                ));
            }
            if !defined.contains(&init[j]) {
                return Err(bad(
                    "the induction variable's initial value may be poison".into()
                ));
            }
            let m = ones(bits);
            let scale = strand.scale & m;
            if strand.uses.is_empty() {
                return Err(bad("the strand replaces nothing".into()));
            }
            for u in &strand.uses {
                if !replaced_once.insert(u.value) {
                    return Err(bad(format!("%{} is replaced twice", u.value)));
                }
                let &(bi, _) = at
                    .get(&u.value)
                    .ok_or_else(|| bad(format!("%{} is not an instruction's result", u.value)))?;
                if !shape.body.contains(&bi) {
                    return Err(bad(format!("%{} is not in the loop", u.value)));
                }
                if types.get(&u.value) != Some(&strand.ty) {
                    return Err(bad(format!("%{} does not have the strand's type", u.value)));
                }
                let l = reading
                    .read(u.value, 0)
                    .ok_or_else(|| bad(format!("%{} is not linear", u.value)))?;
                let claimed: BTreeMap<ValueId, u128> =
                    strand.roots.iter().map(|(v, b)| (*v, b & m)).collect();
                if l.bits != bits
                    || l.a != scale
                    || l.x != Some(strand.iv)
                    || l.r != claimed
                    || claimed.len() != strand.roots.len()
                    || strand.roots.windows(2).any(|w| w[0].0 >= w[1].0)
                    || l.c != u.offset & m
                    || (u.offset & m == 0) != u.constant.is_none()
                {
                    return Err(bad(format!(
                        "%{} is not the strand's scale times the variable plus its root and offset",
                        u.value
                    )));
                }
                let (bi, ni) = at[&u.value];
                let inst = &cur.blocks[bi].body[ni].inst;
                if !matches!(
                    inst,
                    Inst::BinOp {
                        op: BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Shl,
                        ..
                    } | Inst::Cast { .. }
                        | Inst::Copy { .. }
                ) {
                    return Err(bad(format!("%{} is not an arithmetic form", u.value)));
                }
            }
            // The preheader's computation.
            let mut fresh = strand.init.iter().copied();
            let mut take = || {
                fresh
                    .next()
                    .ok_or_else(|| bad("the witness names too few initial values".into()))
            };
            let mut pre: Vec<InstrNode> = Vec::new();
            let x0 = if types.get(&init[j]) == Some(&strand.ty) {
                init[j]
            } else {
                let v = take()?;
                pre.push(node(
                    Inst::Cast {
                        op: CastOp::Bitcast,
                        src_ty: iv_ty.clone(),
                        dst_ty: strand.ty.clone(),
                        operand: init[j],
                    },
                    v,
                ));
                v
            };
            let a = take()?;
            pre.push(node(
                Inst::Const {
                    ty: strand.ty.clone(),
                    value: spelled(&strand.ty, bits, scale),
                },
                a,
            ));
            let mul = take()?;
            pre.push(node(
                Inst::BinOp {
                    op: BinOp::Mul,
                    ty: strand.ty.clone(),
                    lhs: x0,
                    rhs: a,
                },
                mul,
            ));
            let mut q0 = mul;
            for &(root, coef) in &strand.roots {
                if !defined.contains(&root) {
                    return Err(bad("a root may be poison".into()));
                }
                let rty = types
                    .get(&root)
                    .ok_or_else(|| bad("a root has no type".into()))?;
                let as_t = if *rty == strand.ty {
                    root
                } else if int_shape(rty, pointer_bits).is_some_and(|(b, _)| b == bits) {
                    let v = take()?;
                    pre.push(node(
                        Inst::Cast {
                            op: CastOp::Bitcast,
                            src_ty: rty.clone(),
                            dst_ty: strand.ty.clone(),
                            operand: root,
                        },
                        v,
                    ));
                    v
                } else if matches!(
                    rty,
                    Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
                ) && bits == pointer_bits
                {
                    let p = if *rty == Ty::Ptr {
                        root
                    } else {
                        let v = take()?;
                        pre.push(node(
                            Inst::Cast {
                                op: CastOp::PtrToPtr,
                                src_ty: rty.clone(),
                                dst_ty: Ty::Ptr,
                                operand: root,
                            },
                            v,
                        ));
                        v
                    };
                    let v = take()?;
                    pre.push(node(
                        Inst::Cast {
                            op: CastOp::PtrToInt,
                            src_ty: Ty::Ptr,
                            dst_ty: strand.ty.clone(),
                            operand: p,
                        },
                        v,
                    ));
                    v
                } else {
                    return Err(bad(
                        "a root is neither a pointer nor an integer of the width".into(),
                    ));
                };
                let term = if coef & m == 1 {
                    as_t
                } else {
                    let k = take()?;
                    pre.push(node(
                        Inst::Const {
                            ty: strand.ty.clone(),
                            value: spelled(&strand.ty, bits, coef & m),
                        },
                        k,
                    ));
                    let v = take()?;
                    pre.push(node(
                        Inst::BinOp {
                            op: BinOp::Mul,
                            ty: strand.ty.clone(),
                            lhs: as_t,
                            rhs: k,
                        },
                        v,
                    ));
                    v
                };
                let v = take()?;
                pre.push(node(
                    Inst::BinOp {
                        op: BinOp::Add,
                        ty: strand.ty.clone(),
                        lhs: q0,
                        rhs: term,
                    },
                    v,
                ));
                q0 = v;
            }
            if fresh.next().is_some() {
                return Err(bad("the witness names too many initial values".into()));
            }
            // The step.
            let [d, q1] = strand.step.as_slice() else {
                return Err(bad("the step does not name two values".into()));
            };
            let step_nodes = vec![
                node(
                    Inst::Const {
                        ty: strand.ty.clone(),
                        value: spelled(&strand.ty, bits, scale.wrapping_mul(step) & m),
                    },
                    *d,
                ),
                node(
                    Inst::BinOp {
                        op: BinOp::Add,
                        ty: strand.ty.clone(),
                        lhs: strand.param,
                        rhs: *d,
                    },
                    *q1,
                ),
            ];
            // The replacements.
            let mut replaced = Vec::new();
            for u in &strand.uses {
                let (bi, ni) = at[&u.value];
                let original = &cur.blocks[bi].body[ni];
                let mut nodes = Vec::new();
                let mut new = original.clone();
                match u.constant {
                    None => {
                        new.inst = Inst::Copy {
                            ty: strand.ty.clone(),
                            operand: strand.param,
                        };
                    }
                    Some(c) => {
                        let mut k = original.clone();
                        k.inst = Inst::Const {
                            ty: strand.ty.clone(),
                            value: spelled(&strand.ty, bits, u.offset & m),
                        };
                        k.results = vec![c];
                        nodes.push(k);
                        new.inst = Inst::BinOp {
                            op: BinOp::Add,
                            ty: strand.ty.clone(),
                            lhs: strand.param,
                            rhs: c,
                        };
                    }
                }
                nodes.push(new);
                replaced.push((bi, ni, nodes));
            }
            plans.push(Plan {
                pre,
                q0,
                step: step_nodes,
                q1: *q1,
                replaced,
            });
        }
    }
    // ---- Apply: replacements first (by position, before anything moves).
    let mut by_position: HashMap<(usize, usize), Vec<InstrNode>> = HashMap::new();
    for plan in &mut plans {
        for (bi, ni, nodes) in plan.replaced.drain(..) {
            by_position.insert((bi, ni), nodes);
        }
    }
    for (bi, block) in cur.blocks.iter_mut().enumerate() {
        let body = std::mem::take(&mut block.body);
        block.body = body
            .into_iter()
            .enumerate()
            .flat_map(|(ni, n)| by_position.remove(&(bi, ni)).unwrap_or_else(|| vec![n]))
            .collect();
    }
    for (plan, strand) in plans.iter().zip(&lp.strands) {
        cur.blocks[h].params.push((strand.param, strand.ty.clone()));
        let pre = &mut cur.blocks[shape.preheader].body;
        let at = pre.len() - 1;
        for (k, n) in plan.pre.iter().enumerate() {
            pre.insert(at + k, n.clone());
        }
        if let Some(Inst::Br { args, .. }) = pre.last_mut().map(|n| &mut n.inst) {
            args.push(plan.q0);
        }
        let lb = &mut cur.blocks[latch].body;
        let at = lb.len() - 1;
        for (k, n) in plan.step.iter().enumerate() {
            lb.insert(at + k, n.clone());
        }
        if let Some(last) = lb.last_mut() {
            let push = |t: &BlockId, a: &mut Vec<ValueId>| {
                if *t == header {
                    a.push(plan.q1);
                }
            };
            match &mut last.inst {
                Inst::Br { target, args } => push(target, args),
                Inst::CondBr {
                    then_target,
                    then_args,
                    else_target,
                    else_args,
                    ..
                } => {
                    push(then_target, then_args);
                    push(else_target, else_args);
                }
                Inst::Switch {
                    default,
                    default_args,
                    cases,
                    ..
                } => {
                    push(default, default_args);
                    for case in cases {
                        push(&case.target, &mut case.args);
                    }
                }
                _ => {}
            }
        }
    }
    Ok(())
}

#[cfg(test)]
#[path = "trust_ir_mid_tv_ivsr_tests.rs"]
mod tests;
