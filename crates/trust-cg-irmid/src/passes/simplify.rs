// trust-cg-irmid/passes/simplify.rs - algebraic simplification
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Algebraic simplification of integer operations, the identities that the
//! other passes leave: an operation by its identity element (`x + 0`,
//! `x | 0`, `x >> 0`, a rotate by 0, `x * 1`, `x & ~0`, which constant
//! folding and the
//! unroller's constant induction variables produce), and the pair packing
//! of scalar replacement, which carries a word copied over two narrower
//! fields as one integer (`c = (zext a) | (zext b << 32)`) and reads the
//! parts back as `trunc c` and `trunc (c >> 32)`: those reads are `a` and
//! `b` again (a mask over an extension's bits, a truncation of an
//! extension back to its source, a bitcast round trip, the low part of an
//! `or` with a high part shifted past it, and the high part of such an
//! `or`). The rewrites become `copy`s (or a `trunc` of the low part), which
//! copy propagation removes; a slice iterator scalar replacement packed
//! into a `u64` then reads as its two pointers again, so the loop passes
//! see its bounds.
//!
//! After them, a rotate left by a constant whose every use masks only the
//! bits it brings round from the top becomes a right shift by a fresh
//! constant (`masked_rotates`).
//!
//! The pass applies the rules to a fixed point, looking through `copy`s of
//! a value's own type; the witness lists each rewrite with its rule and the
//! value it keeps, in order, and the checker
//! (`trust_cg_verify::trust_ir_mid_tv`, `trust_ir_mid_tv_fold.rs`) matches
//! each rule again with its own code. Each is a refinement: the source's
//! operation inspects its operands (and faults on poison) where a `copy`
//! does not.

use std::collections::HashMap;

use trust_cg_verify::trust_ir_mid_tv::{
    PassWitness, Respell, RespellRule, RespellWitness, Simplify, SimplifyRule, SimplifyWitness,
};
use trust_ir::{BinOp, CastOp, Constant, Function, Inst, InstrNode, Ty, ValueId};

use super::{MidPass, PassContext, int_shape};

pub(crate) struct SimplifyPass;

/// The evidence name of algebraic simplification.
pub(crate) const SIMPLIFY_NAME: &str = "simplify";

impl MidPass for SimplifyPass {
    fn name(&self) -> &'static str {
        SIMPLIFY_NAME
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let mut out = func.clone();
        let mut view = View::new(func, cx.pointer_bits);
        let mut rewrites = Vec::new();
        for _ in 0..8 {
            let mut changed = false;
            for block in &mut out.blocks {
                for node in &mut block.body {
                    let [value] = node.results.as_slice() else {
                        continue;
                    };
                    let value = *value;
                    if let Some((rule, operand, inst)) = rewrite(&view, &node.inst) {
                        view.defs.insert(value, inst.clone());
                        node.inst = inst;
                        rewrites.push(Simplify {
                            value,
                            rule,
                            operand,
                        });
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        masked_rotates(&mut out, &view, &mut rewrites);
        if rewrites.is_empty() {
            return None;
        }
        Some((out, PassWitness::Simplify(SimplifyWitness { rewrites })))
    }
}

/// The respelling of the rustc bridge's sign-reinterpreting copies
/// ([`SimplifyRule::ReinterpretCopy`]): a `copy T x` whose operand is an
/// integer of another type of the same width becomes `bitcast` of `x` to
/// `T`, and one whose operand is a thin pointer of another pointer type
/// than the thin pointer `T` becomes `ptrtoptr` of `x` to `T` (the bridge
/// reads a `*const` lane as `*mut`), which is what the wasm32 lane and the
/// differential's view read them as. trust-ir's validator reports the copy (`OperandTypeMismatch`), and
/// the lane emits a mid-end output only when no function of it has a
/// finding kind more often than its input did, so a callee carrying one
/// was left a call wherever the inliner spliced it (the finding is the
/// caller's once copied there). It runs first in the pipeline, so every
/// callee is spliced without it; its witness is algebraic
/// simplification's.
pub(crate) struct RetypeCopyPass;

/// A thin pointer type: one address word, no metadata.
fn thin(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
    )
}

/// The evidence name of the copy respelling.
pub(crate) const RETYPE_COPY_NAME: &str = "retype_copy";

impl MidPass for RetypeCopyPass {
    fn name(&self) -> &'static str {
        RETYPE_COPY_NAME
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let types = super::value_types(func);
        let width = |ty: &Ty| int_shape(ty, cx.pointer_bits).map(|(bits, _)| bits);
        let mut out = func.clone();
        let mut rewrites = Vec::new();
        for node in out.blocks.iter_mut().flat_map(|b| &mut b.body) {
            let ([value], Inst::Copy { ty, operand }) = (node.results.as_slice(), &node.inst)
            else {
                continue;
            };
            let Some(from) = types.get(operand) else {
                continue;
            };
            let op = if from != ty && thin(from) && thin(ty) {
                CastOp::PtrToPtr
            } else if from == ty || width(from).is_none() || width(from) != width(ty) {
                continue;
            } else {
                CastOp::Bitcast
            };
            rewrites.push(Simplify {
                value: *value,
                rule: SimplifyRule::ReinterpretCopy,
                operand: *operand,
            });
            node.inst = Inst::Cast {
                op,
                src_ty: from.clone(),
                dst_ty: ty.clone(),
                operand: *operand,
            };
        }
        if rewrites.is_empty() {
            return None;
        }
        Some((out, PassWitness::Simplify(SimplifyWitness { rewrites })))
    }
}

/// The operand respelling of two forms the rustc bridge emits that
/// trust-ir's validator reports, which a splice would carry into a caller:
/// a pointer comparison at a typed pointer (`icmp eq *mut T a, b`, a slice
/// iterator's position against its end; `ICmpRequiresIntegerOrPtr`) compares
/// its operands cast to `ptr` by fresh `ptrtoptr`s just before it, and a
/// `memcopy` or `memset` whose byte count is a pointer-width unsigned integer
/// other than `usize` (the bridge's `u32`; `OperandTypeMismatch`) takes a
/// fresh `usize` of it (a `const usize`, or a `zext`). The wasm32 lane and
/// the differential's view read both alike either way; the checker is
/// `trust_ir_mid_tv_fold.rs`'s `rebuild_respell`.
pub(crate) struct RespellPass;

/// The evidence name of the operand respelling.
pub(crate) const RESPELL_NAME: &str = "respell";

impl MidPass for RespellPass {
    fn name(&self) -> &'static str {
        RESPELL_NAME
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let types = super::value_types(func);
        let defs = super::sole_defs(func);
        let typed_pointer = |t: &Ty| {
            matches!(
                t,
                Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
            )
        };
        let mut next = super::loops::first_free_value(func);
        let mut fresh = || {
            let v = ValueId::new(next);
            next += 1;
            v
        };
        let mut out = func.clone();
        let mut rewrites = Vec::new();
        for block in &mut out.blocks {
            let body = std::mem::take(&mut block.body);
            let mut rebuilt = Vec::with_capacity(body.len());
            for (index, node) in body.into_iter().enumerate() {
                match &node.inst {
                    Inst::ICmp { op, ty, lhs, rhs }
                        if typed_pointer(ty)
                            && types.get(lhs) == Some(ty)
                            && types.get(rhs) == Some(ty) =>
                    {
                        let (a, b) = (fresh(), fresh());
                        for (operand, result) in [(*lhs, a), (*rhs, b)] {
                            let mut cast = node.clone();
                            cast.inst = Inst::Cast {
                                op: CastOp::PtrToPtr,
                                src_ty: ty.clone(),
                                dst_ty: Ty::Ptr,
                                operand,
                            };
                            cast.results = vec![result];
                            rebuilt.push(cast);
                        }
                        let mut compare = node.clone();
                        compare.inst = Inst::ICmp {
                            op: *op,
                            ty: Ty::Ptr,
                            lhs: a,
                            rhs: b,
                        };
                        rebuilt.push(compare);
                        rewrites.push(Respell {
                            block: block.id,
                            index,
                            rule: RespellRule::PointerCompare { lhs: a, rhs: b },
                        });
                    }
                    Inst::MemCopy { bytes, .. } | Inst::MemSet { bytes, .. }
                        if types.get(bytes).is_some_and(|t| {
                            *t != Ty::Usize
                                && int_shape(t, cx.pointer_bits) == Some((cx.pointer_bits, false))
                        }) =>
                    {
                        let from = types[bytes].clone();
                        let count = fresh();
                        let mut def = node.clone();
                        def.inst = match defs.get(bytes) {
                            Some(Inst::Const {
                                value: Constant::Int(k),
                                ..
                            }) if *k >= 0 && *k >> cx.pointer_bits == 0 => Inst::Const {
                                ty: Ty::Usize,
                                value: Constant::Int(*k),
                            },
                            _ => Inst::Cast {
                                op: CastOp::ZExt,
                                src_ty: from,
                                dst_ty: Ty::Usize,
                                operand: *bytes,
                            },
                        };
                        def.results = vec![count];
                        rebuilt.push(def);
                        let mut op = node.clone();
                        if let Inst::MemCopy { bytes, .. } | Inst::MemSet { bytes, .. } =
                            &mut op.inst
                        {
                            *bytes = count;
                        }
                        rebuilt.push(op);
                        rewrites.push(Respell {
                            block: block.id,
                            index,
                            rule: RespellRule::ByteCount { count },
                        });
                    }
                    _ => rebuilt.push(node),
                }
            }
            block.body = rebuilt;
        }
        if rewrites.is_empty() {
            return None;
        }
        Some((out, PassWitness::Respell(RespellWitness { rewrites })))
    }
}

/// [`SimplifyRule::MaskedRotate`], after the other rules: a `rotl x, c`
/// (`0 < c < width`) whose every use is an `and` of its type with a
/// constant mask below `2^c` reads only the bits the rotate brings round
/// from the top, `x >> (width - c)`; it becomes that shift, by a fresh
/// constant inserted just before it. On wasm a rotate by a constant costs
/// what a shift does under TurboFan, but V8's baseline compiler calls out of
/// line for it (spilling every cached register), so a masked rotate in
/// straight-line code (a fully unrolled loop over `rotate_left(k * c)`) is
/// far slower there than the shift LLVM's instruction combining leaves.
fn masked_rotates(out: &mut Function, view: &View, rewrites: &mut Vec<Simplify>) {
    // Per value: the widest mask of its uses, or `None` once a use is not
    // an `and` of its type with a constant (each operand slot counted).
    let mut masks: HashMap<ValueId, Option<u128>> = HashMap::new();
    for node in out.blocks.iter().flat_map(|b| &b.body) {
        let masked = match &node.inst {
            Inst::BinOp {
                op: BinOp::And,
                ty,
                lhs,
                rhs,
            } if lhs != rhs => view.width(ty).and_then(|bits| {
                [(*lhs, *rhs), (*rhs, *lhs)].into_iter().find_map(|(v, m)| {
                    (view.ty(v).as_ref() == Some(ty))
                        .then(|| view.konst(m, bits).map(|c| (v, c)))
                        .flatten()
                })
            }),
            _ => None,
        };
        node.inst.visit_value_operands(|v| {
            let entry = masks.entry(v).or_insert(Some(0));
            *entry = match (*entry, masked) {
                (Some(widest), Some((x, m))) if x == v => Some(widest.max(m)),
                _ => None,
            };
        });
    }
    let mut next = super::loops::first_free_value(out);
    for block in &mut out.blocks {
        let mut i = 0;
        while i < block.body.len() {
            let node = &block.body[i];
            let (
                Inst::BinOp {
                    op: BinOp::RotL,
                    ty,
                    lhs: x,
                    rhs: amount,
                },
                [value],
            ) = (&node.inst, node.results.as_slice())
            else {
                i += 1;
                continue;
            };
            let (value, ty, x) = (*value, ty.clone(), *x);
            let fits = view.width(&ty).and_then(|bits| {
                let c = view.konst(*amount, bits)?;
                let widest = masks.get(&value).copied().flatten()?;
                (c > 0 && c < u128::from(bits) && widest < (1u128 << c))
                    .then_some(u128::from(bits) - c)
            });
            let Some(k) = fits else {
                i += 1;
                continue;
            };
            let fresh = ValueId::new(next);
            next += 1;
            block.body[i].inst = Inst::BinOp {
                op: BinOp::LShr,
                ty: ty.clone(),
                lhs: x,
                rhs: fresh,
            };
            block.body.insert(
                i,
                InstrNode::new(Inst::Const {
                    ty,
                    value: Constant::Int(k as i128),
                })
                .with_results([fresh]),
            );
            rewrites.push(Simplify {
                value,
                rule: SimplifyRule::MaskedRotate,
                operand: fresh,
            });
            i += 2;
        }
    }
}

/// The function's current definitions and types, for matching (updated as
/// each rewrite is made, so every match sees the rewrites before it).
struct View {
    defs: HashMap<ValueId, Inst>,
    params: HashMap<ValueId, Ty>,
    pb: u32,
}

impl View {
    fn new(func: &Function, pb: u32) -> Self {
        let mut defs = HashMap::new();
        let mut params = HashMap::new();
        for block in &func.blocks {
            for (v, t) in &block.params {
                params.insert(*v, t.clone());
            }
            for node in &block.body {
                if let [r] = node.results.as_slice() {
                    defs.insert(*r, node.inst.clone());
                }
            }
        }
        Self { defs, params, pb }
    }

    fn ty(&self, v: ValueId) -> Option<Ty> {
        if let Some(t) = self.params.get(&v) {
            return Some(t.clone());
        }
        match self.defs.get(&v)? {
            Inst::Copy { ty, .. }
            | Inst::Load { ty, .. }
            | Inst::Const { ty, .. }
            | Inst::Select { ty, .. }
            | Inst::BinOp { ty, .. }
            | Inst::UnOp { ty, .. } => Some(ty.clone()),
            Inst::Cast { dst_ty, .. } => Some(dst_ty.clone()),
            Inst::ICmp { .. } | Inst::FCmp { .. } => Some(Ty::Bool),
            _ => None,
        }
    }

    fn through(&self, mut v: ValueId) -> ValueId {
        for _ in 0..64 {
            match self.defs.get(&v) {
                Some(Inst::Copy { ty, operand }) if self.ty(*operand).as_ref() == Some(ty) => {
                    v = *operand;
                }
                _ => return v,
            }
        }
        v
    }

    fn def(&self, v: ValueId) -> Option<&Inst> {
        self.defs.get(&self.through(v))
    }

    fn width(&self, ty: &Ty) -> Option<u32> {
        int_shape(ty, self.pb).map(|(b, _)| b)
    }

    fn konst(&self, v: ValueId, bits: u32) -> Option<u128> {
        match self.def(v)? {
            Inst::Const {
                ty,
                value: Constant::Int(k),
            } if self.width(ty) == Some(bits) => Some((*k as u128) & ones(bits)),
            _ => None,
        }
    }

    /// `v` through `copy`, `ptrtoptr`, pointer-width `ptrtoint`, `inttoptr`
    /// and integer `bitcast`: the casts that keep an address.
    fn address(&self, mut v: ValueId) -> ValueId {
        let word = |ty: &Ty| self.width(ty) == Some(self.pb);
        for _ in 0..64 {
            v = match self.defs.get(&v) {
                Some(Inst::Copy { operand, .. }) => *operand,
                Some(Inst::Cast {
                    op,
                    src_ty,
                    dst_ty,
                    operand,
                }) if match op {
                    CastOp::PtrToPtr => true,
                    CastOp::PtrToInt => word(dst_ty),
                    CastOp::IntToPtr => word(src_ty),
                    CastOp::Bitcast => word(src_ty) && word(dst_ty),
                    _ => false,
                } =>
                {
                    *operand
                }
                _ => return v,
            };
        }
        v
    }

    fn zext_from(&self, v: ValueId) -> Option<u32> {
        match self.def(v)? {
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty,
                ..
            } => self.width(src_ty),
            _ => None,
        }
    }
}

fn ones(bits: u32) -> u128 {
    if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

/// The first rule that rewrites `inst`: the rule, the value it keeps, and
/// the new instruction.
fn rewrite(view: &View, inst: &Inst) -> Option<(SimplifyRule, ValueId, Inst)> {
    let copy_of = |ty: &Ty, v: ValueId| {
        (view.ty(v).as_ref() == Some(ty)).then(|| Inst::Copy {
            ty: ty.clone(),
            operand: v,
        })
    };
    match inst {
        Inst::BinOp { op, ty, lhs, rhs } => {
            let bits = view.width(ty)?;
            // Identity elements.
            let identity = |c: u128, right: bool| match op {
                BinOp::Add | BinOp::Or | BinOp::Xor => c == 0,
                BinOp::Mul => c == 1,
                BinOp::And => c == ones(bits),
                BinOp::Sub | BinOp::Shl | BinOp::LShr | BinOp::AShr => right && c == 0,
                BinOp::RotL | BinOp::RotR => right && c.is_multiple_of(u128::from(bits)),
                BinOp::UDiv | BinOp::SDiv => right && c == 1,
                _ => false,
            };
            for (keep, other, right) in [(*lhs, *rhs, true), (*rhs, *lhs, false)] {
                if view.konst(other, bits).is_some_and(|c| identity(c, right))
                    && let Some(i) = copy_of(ty, keep)
                {
                    return Some((SimplifyRule::Identity, keep, i));
                }
            }
            // A pointer difference: `(r + x) - r` behind address casts.
            if *op == BinOp::Sub
                && bits == view.pb
                && let Some(Inst::BinOp {
                    op: BinOp::Add,
                    ty: t,
                    lhs: p,
                    rhs: x,
                }) = view.defs.get(&view.address(*lhs))
                && view.width(t) == Some(view.pb)
            {
                let base = view.address(*rhs);
                let kept = if view.address(*p) == base {
                    Some(*x)
                } else if view.address(*x) == base {
                    Some(*p)
                } else {
                    None
                };
                if let Some(k) = kept
                    && let Some(i) = copy_of(ty, k)
                {
                    return Some((SimplifyRule::PointerDifference, k, i));
                }
            }
            if *op == BinOp::And {
                for (x, m) in [(*lhs, *rhs), (*rhs, *lhs)] {
                    if let (Some(from), Some(c)) = (view.zext_from(x), view.konst(m, bits))
                        && c & ones(from) == ones(from)
                        && let Some(i) = copy_of(ty, x)
                    {
                        return Some((SimplifyRule::MaskedExtension, x, i));
                    }
                }
            }
            if *op == BinOp::LShr {
                let k = view.konst(*rhs, bits)?;
                if k == 0 || k >= u128::from(bits) {
                    return None;
                }
                let Some(Inst::BinOp {
                    op: BinOp::Or,
                    ty: t,
                    lhs: a,
                    rhs: b,
                }) = view.def(*lhs)
                else {
                    return None;
                };
                if t != ty {
                    return None;
                }
                let high = |v: &ValueId| match view.def(*v) {
                    Some(Inst::BinOp {
                        op: BinOp::Shl,
                        ty: st,
                        lhs: y,
                        rhs: amount,
                    }) if st == ty && view.konst(*amount, bits) == Some(k) => Some(*y),
                    _ => None,
                };
                let below = |v: &ValueId| {
                    if let Some(from) = view.zext_from(*v) {
                        return u128::from(from) <= k;
                    }
                    if let Some(c) = view.konst(*v, bits) {
                        return c < (1u128 << k);
                    }
                    matches!(view.def(*v), Some(Inst::BinOp { op: BinOp::And, lhs: l, rhs: r, .. })
                        if [l, r].iter().any(|m| view.konst(**m, bits).is_some_and(|c| c < (1u128 << k))))
                };
                let (low, y) = match (high(a), high(b)) {
                    (_, Some(y)) => (*a, y),
                    (Some(y), None) => (*b, y),
                    _ => return None,
                };
                let fits = view
                    .zext_from(y)
                    .is_some_and(|from| u128::from(from) <= u128::from(bits) - k);
                if below(&low) && fits {
                    return copy_of(ty, y).map(|i| (SimplifyRule::HighPart, y, i));
                }
            }
            None
        }
        Inst::Cast {
            op: CastOp::Trunc,
            src_ty,
            dst_ty,
            operand,
        } => {
            match view.def(*operand)? {
                Inst::Cast {
                    op: CastOp::ZExt | CastOp::SExt,
                    src_ty: inner,
                    operand: a,
                    ..
                } if inner == dst_ty => {
                    return copy_of(dst_ty, *a).map(|i| (SimplifyRule::TruncExtension, *a, i));
                }
                Inst::BinOp {
                    op: BinOp::Or | BinOp::Xor | BinOp::Add,
                    ty,
                    lhs,
                    rhs,
                } if ty == src_ty => {
                    let (from, to) = (view.width(src_ty)?, view.width(dst_ty)?);
                    let high = |v: &ValueId| match view.def(*v) {
                        Some(Inst::BinOp {
                            op: BinOp::Shl,
                            ty: st,
                            rhs: amount,
                            ..
                        }) if st == src_ty => view
                            .konst(*amount, from)
                            .is_some_and(|k| k >= u128::from(to) && k < u128::from(from)),
                        _ => false,
                    };
                    let keep = if high(rhs) {
                        *lhs
                    } else if high(lhs) {
                        *rhs
                    } else {
                        return None;
                    };
                    if to > from || view.ty(keep).as_ref() != Some(src_ty) {
                        return None;
                    }
                    return Some((
                        SimplifyRule::TruncLowPart,
                        keep,
                        Inst::Cast {
                            op: CastOp::Trunc,
                            src_ty: src_ty.clone(),
                            dst_ty: dst_ty.clone(),
                            operand: keep,
                        },
                    ));
                }
                _ => {}
            }
            None
        }
        Inst::Cast {
            op: CastOp::Bitcast,
            dst_ty,
            operand,
            ..
        } => match view.def(*operand)? {
            Inst::Cast {
                op: CastOp::Bitcast,
                operand: a,
                ..
            } => copy_of(dst_ty, *a).map(|i| (SimplifyRule::BitcastRoundTrip, *a, i)),
            _ => None,
        },
        _ => None,
    }
}
