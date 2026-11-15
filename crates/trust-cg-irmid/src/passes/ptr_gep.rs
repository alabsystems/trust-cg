// trust-cg-irmid/passes/ptr_gep.rs - pointer chain to byte-offset GEP
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The MIR lowering addresses a field of a memory-backed local as
//! `inttoptr(ptrtoint(p) + k)`, and moves an address through an integer as
//! `inttoptr(ptrtoint(p))`. When `p` lies `d` bytes into an `alloca`
//! (count-free, or counted by an integer constant `k >= 1`) of `S > 0` bytes
//! (the `alloca` itself, or a pointer derived from it by copies,
//! `ptrtoptr`s and `gep`s by non-negative constants, every step inside the
//! allocation), the integer type is at least as wide as a pointer,
//! and `k` is a constant `0 <= d + k < S` (an integer constant, the
//! `bitcast` of one of the same width, or an `add` or `mul` of two such, each
//! step in `[0, 2^(bits - 1))` so no reading of the bits differs), that
//! pointer is exactly `p` advanced `k` bytes inside its own allocation, so
//! the chain becomes `gep u8, p, [k]` (`copy p` when `k = 0`, and for the
//! round trip without an `add`), which copy propagation then forwards; an
//! offset computed by a constant expression is folded into a fresh `const`
//! first, so the slot passes see a constant index. Any
//! other chain — an unknown base, a variable or out-of-range offset, a
//! narrower integer — is left alone: there `inttoptr` may resolve to another
//! allocation, which a GEP never does. The `ptrtoint`, `add` and constants
//! stay; dead-code elimination removes them when nothing else reads them.

use std::collections::HashMap;
use trust_cg_verify::trust_ir_mid_tv::{GepRewrite, PassWitness, PtrGepWitness};

use trust_ir::{BinOp, CastOp, Constant, Function, Inst, Module, Ty, ValueId};

use super::{MidPass, PassContext, alloca_count, int_shape, sole_defs};

pub(crate) struct PtrGep;

/// The steps a provenance or constant walk takes before giving up.
const MAX_WALK: usize = 64;

/// The `alloca` (count-free, or counted by an integer constant `k >= 1`) `v`
/// lies in, its size and `v`'s displacement into it, when `v` is the
/// `alloca` or derived from it by copies, `ptrtoptr`s and `gep`s by
/// non-negative integer constants, every step inside it.
pub(super) fn displacement(
    module: &Module,
    defs: &HashMap<ValueId, &Inst>,
    mut v: ValueId,
) -> Option<(ValueId, u64, u64)> {
    let size_of = |ty: &Ty| {
        module
            .ty_layout_shape(ty)
            .ok()
            .and_then(|shape| shape.size_bytes())
    };
    let mut disp: u64 = 0;
    for _ in 0..MAX_WALK {
        match defs.get(&v)? {
            Inst::Alloca { ty, count, .. } => {
                let size = size_of(ty)?
                    .checked_mul(alloca_count(defs, *count)?)
                    .filter(|&s| s > 0)?;
                return (disp < size).then_some((v, size, disp));
            }
            Inst::Copy { operand, .. }
            | Inst::Cast {
                op: CastOp::PtrToPtr,
                operand,
                ..
            } => v = *operand,
            Inst::GEP {
                pointee_ty,
                base,
                indices,
                ..
            } => {
                let elem = size_of(pointee_ty)?;
                for k in indices {
                    let Some(Inst::Const {
                        ty,
                        value: Constant::Int(k),
                    }) = defs.get(k)
                    else {
                        return None;
                    };
                    if !ty.is_integer() {
                        return None;
                    }
                    let k = u64::try_from(*k).ok()?;
                    disp = disp.checked_add(elem.checked_mul(k)?)?;
                }
                v = *base;
            }
            _ => return None,
        }
    }
    None
}

/// The value of the constant expression `v` (module docs), every step in
/// `[0, 2^(bits - 1))` at the integer width `bits`.
fn constant_offset(
    defs: &HashMap<ValueId, &Inst>,
    v: ValueId,
    bits: u32,
    pointer_bits: u32,
    depth: usize,
) -> Option<u64> {
    if depth > MAX_WALK {
        return None;
    }
    let width = |ty: &Ty| int_shape(ty, pointer_bits).map(|(b, _)| b);
    let limit: i128 = 1i128.checked_shl(bits.checked_sub(1)?)?;
    let in_range = |k: i128| (0..limit).contains(&k).then_some(k);
    let value = match defs.get(&v)? {
        Inst::Const {
            ty,
            value: Constant::Int(k),
        } if width(ty) == Some(bits) => in_range(*k)?,
        Inst::Cast {
            op: CastOp::Bitcast,
            src_ty,
            dst_ty,
            operand,
        } if width(src_ty) == Some(bits) && width(dst_ty) == Some(bits) => {
            match defs.get(operand)? {
                Inst::Const {
                    ty,
                    value: Constant::Int(k),
                } if ty == src_ty => in_range(*k)?,
                _ => return None,
            }
        }
        Inst::BinOp {
            op: op @ (BinOp::Add | BinOp::Mul),
            ty,
            lhs,
            rhs,
        } if width(ty) == Some(bits) => {
            let l = i128::from(constant_offset(defs, *lhs, bits, pointer_bits, depth + 1)?);
            let r = i128::from(constant_offset(defs, *rhs, bits, pointer_bits, depth + 1)?);
            in_range(if *op == BinOp::Add { l + r } else { l * r })?
        }
        _ => return None,
    };
    u64::try_from(value).ok()
}

impl MidPass for PtrGep {
    fn name(&self) -> &'static str {
        "ptr_gep"
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let defs = sole_defs(func);
        let mut fresh = func.fresh_value_ids();
        let mut rewrites: Vec<(usize, usize, Vec<trust_ir::InstrNode>, GepRewrite)> = Vec::new();
        for (bi, block) in func.blocks.iter().enumerate() {
            for (ni, node) in block.body.iter().enumerate() {
                let (
                    Inst::Cast {
                        op: CastOp::IntToPtr,
                        src_ty: int_ty,
                        dst_ty: Ty::Ptr,
                        operand: sum,
                    },
                    [result],
                ) = (&node.inst, node.results.as_slice())
                else {
                    continue;
                };
                let Some((bits, _)) = int_shape(int_ty, cx.pointer_bits) else {
                    continue;
                };
                if bits < cx.pointer_bits {
                    continue;
                }
                let base_of = |v: &ValueId| match defs.get(v) {
                    Some(Inst::Cast {
                        op: CastOp::PtrToInt,
                        src_ty: Ty::Ptr,
                        dst_ty,
                        operand,
                    }) if dst_ty == int_ty => Some(*operand),
                    _ => None,
                };
                // The round trip `inttoptr(ptrtoint(p))`, or `p` plus a
                // constant expression.
                let (base, offset_value, offset) = if let Some(base) = base_of(sum) {
                    (base, *sum, 0)
                } else {
                    let Some(Inst::BinOp {
                        op: BinOp::Add,
                        ty,
                        lhs,
                        rhs,
                    }) = defs.get(sum)
                    else {
                        continue;
                    };
                    if ty != int_ty {
                        continue;
                    }
                    let (base, offset_value) = match (base_of(lhs), base_of(rhs)) {
                        (Some(base), _) => (base, *rhs),
                        (None, Some(base)) => (base, *lhs),
                        (None, None) => continue,
                    };
                    let typed = match defs.get(&offset_value) {
                        Some(Inst::Const { ty, .. } | Inst::BinOp { ty, .. }) => ty == int_ty,
                        Some(Inst::Cast { dst_ty, .. }) => dst_ty == int_ty,
                        _ => false,
                    };
                    let Some(offset) =
                        constant_offset(&defs, offset_value, bits, cx.pointer_bits, 0)
                            .filter(|_| typed)
                    else {
                        continue;
                    };
                    (base, offset_value, offset)
                };
                // `copy ptr p` and `gep u8, p` read `p` as a `ptr`.
                let base_is_ptr = matches!(
                    defs.get(&base),
                    Some(
                        Inst::Alloca { .. }
                            | Inst::GEP { .. }
                            | Inst::Copy { ty: Ty::Ptr, .. }
                            | Inst::Cast {
                                op: CastOp::PtrToPtr,
                                dst_ty: Ty::Ptr,
                                ..
                            }
                    )
                );
                let Some((_, size, disp)) =
                    displacement(cx.module, &defs, base).filter(|_| base_is_ptr)
                else {
                    continue;
                };
                if disp.checked_add(offset).is_none_or(|end| end >= size) {
                    continue;
                }
                // An offset computed by a constant expression is folded into a
                // fresh `const`, so the slot passes see a constant index.
                let literal = matches!(defs.get(&offset_value), Some(Inst::Const { .. }));
                let folded = if offset == 0 || literal {
                    None
                } else {
                    let Ok(id) = fresh.take() else {
                        continue;
                    };
                    Some(id)
                };
                let mut nodes = Vec::new();
                let mut rewritten = node.clone();
                rewritten.inst = match folded {
                    None if offset == 0 => Inst::Copy {
                        ty: Ty::Ptr,
                        operand: base,
                    },
                    None => Inst::GEP {
                        pointee_ty: Ty::U8,
                        base,
                        indices: vec![offset_value],
                        inbounds: true,
                    },
                    Some(id) => {
                        let mut constant = node.clone();
                        constant.inst = Inst::Const {
                            ty: int_ty.clone(),
                            value: Constant::Int(i128::from(offset)),
                        };
                        constant.results = vec![id];
                        nodes.push(constant);
                        Inst::GEP {
                            pointee_ty: Ty::U8,
                            base,
                            indices: vec![id],
                            inbounds: true,
                        }
                    }
                };
                nodes.push(rewritten);
                rewrites.push((
                    bi,
                    ni,
                    nodes,
                    GepRewrite {
                        block: block.id,
                        index: ni,
                        result: *result,
                        base,
                        offset,
                        offset_value,
                        folded,
                    },
                ));
            }
        }
        if rewrites.is_empty() {
            return None;
        }
        let mut out = func.clone();
        let mut witness = PtrGepWitness::default();
        let mut replaced: HashMap<(usize, usize), Vec<trust_ir::InstrNode>> = HashMap::new();
        for (bi, ni, nodes, rewrite) in rewrites {
            replaced.insert((bi, ni), nodes);
            witness.rewrites.push(rewrite);
        }
        for (bi, block) in out.blocks.iter_mut().enumerate() {
            let body = std::mem::take(&mut block.body);
            block.body = body
                .into_iter()
                .enumerate()
                .flat_map(|(ni, node)| replaced.remove(&(bi, ni)).unwrap_or_else(|| vec![node]))
                .collect();
        }
        Some((out, PassWitness::PtrGep(witness)))
    }
}
