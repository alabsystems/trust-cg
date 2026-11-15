// trust-cg-irmid/passes/addr_fold.rs - integer address chains to `gep`s
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Address folding: an `inttoptr` to `ptr` whose integer is, through the
//! bridge's address casts and constant offsets, the address of an `alloca`
//! or a global plus a constant inside it becomes `gep inbounds u8` of that
//! allocation (or `copy` of it at offset zero). The pointer-chain rewrite
//! (`ptr_gep.rs`) takes one `inttoptr(ptrtoint(p) + k)` with `k` a
//! non-negative constant expression; the copies of an unrolled pointer loop
//! chain such steps with negative strides from a pointer one past the end
//! (`inttoptr(ptrtoint(inttoptr(ptrtoint(slot) + 48)) - 8)`), which this
//! pass reads whole. The folded accesses are at constant offsets of the
//! slot, which store forwarding and scalar replacement then see.
//!
//! The reading (`root + offset` modulo the pointer width): integer
//! constants, `copy`, same-width integer `bitcast`, `ptrtoint`, `inttoptr`
//! and `ptrtoptr` at pointer width, `add` and `sub` of a constant, `mul` of
//! constants, and `gep` by constant indices; the root must be an `alloca`
//! (count-free or counted by a positive constant) or `global_addr` of known
//! size dominating the `inttoptr`, and the offset must lie inside it. The
//! checker (`trust_ir_mid_tv_addr.rs`) reads the chain again with its own
//! code and the interpreter's layout.

use std::collections::{HashMap, HashSet};

use trust_cg_verify::trust_ir_mid_tv::{AddrFold, AddrFoldWitness, PassWitness};
use trust_ir::{BinOp, BlockId, CastOp, Constant, Function, Inst, InstrNode, Module, Ty, ValueId};

use super::loops::first_free_value;
use super::{MidPass, PassContext, alloca_count, int_shape, sole_defs};
use crate::cfg::TrustIrCfg;

pub(crate) struct AddrFoldPass;

/// The evidence name of address folding.
pub(crate) const ADDR_FOLD_NAME: &str = "addr_fold";

/// Bounds the reading's recursion.
const DEPTH: usize = 96;

impl MidPass for AddrFoldPass {
    fn name(&self) -> &'static str {
        ADDR_FOLD_NAME
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let defs = sole_defs(func);
        let pb = cx.pointer_bits;
        let mut candidates: Vec<(usize, usize, ValueId, ValueId, u64, Ty)> = Vec::new();
        for (bi, block) in func.blocks.iter().enumerate() {
            for (ni, node) in block.body.iter().enumerate() {
                let Inst::Cast {
                    op: CastOp::IntToPtr,
                    src_ty,
                    dst_ty: Ty::Ptr,
                    operand,
                } = &node.inst
                else {
                    continue;
                };
                let [result] = node.results.as_slice() else {
                    continue;
                };
                if int_shape(src_ty, pb).is_none_or(|(b, _)| b != pb) {
                    continue;
                }
                let Some((Some(root), off)) = read(cx.module, &defs, pb, *operand, 0) else {
                    continue;
                };
                let Some(size) = extent(cx.module, &defs, root) else {
                    continue;
                };
                let Ok(off) = u64::try_from(off) else {
                    continue;
                };
                if off >= size {
                    continue;
                }
                candidates.push((bi, ni, *result, root, off, src_ty.clone()));
            }
        }
        if candidates.is_empty() {
            return None;
        }
        // The root must dominate the `inttoptr`.
        let view = TrustIrCfg::new(func);
        let cfg = view.analysis();
        let mut at: HashMap<ValueId, (usize, usize)> = HashMap::new();
        for (bi, block) in func.blocks.iter().enumerate() {
            for (ni, node) in block.body.iter().enumerate() {
                for r in &node.results {
                    at.insert(*r, (bi, ni));
                }
            }
        }
        let ids: Vec<BlockId> = func.blocks.iter().map(|b| b.id).collect();
        let mut next = first_free_value(func);
        let mut folds = Vec::new();
        let mut replaced: HashMap<(usize, usize), Vec<InstrNode>> = HashMap::new();
        let mut done: HashSet<ValueId> = HashSet::new();
        for (bi, ni, value, root, off, int_ty) in candidates {
            let Some(&(rb, rn)) = at.get(&root) else {
                continue;
            };
            let dominated = if rb == bi {
                rn < ni
            } else {
                cfg.idom.contains_key(&ids[bi]) && cfg.dominates(ids[rb], ids[bi])
            };
            if !dominated || !done.insert(value) {
                continue;
            }
            let node = &func.blocks[bi].body[ni];
            let mut nodes = Vec::new();
            let mut gep = node.clone();
            let index = if off == 0 {
                gep.inst = Inst::Copy {
                    ty: Ty::Ptr,
                    operand: root,
                };
                None
            } else {
                let index = ValueId::new(next);
                next += 1;
                let mut constant = node.clone();
                constant.inst = Inst::Const {
                    ty: int_ty,
                    value: Constant::Int(i128::from(off)),
                };
                constant.results = vec![index];
                nodes.push(constant);
                gep.inst = Inst::GEP {
                    pointee_ty: Ty::U8,
                    base: root,
                    indices: vec![index],
                    inbounds: true,
                };
                Some(index)
            };
            nodes.push(gep);
            replaced.insert((bi, ni), nodes);
            folds.push(AddrFold {
                value,
                base: root,
                offset: off,
                index,
            });
        }
        if folds.is_empty() {
            return None;
        }
        let mut out = func.clone();
        for (bi, block) in out.blocks.iter_mut().enumerate() {
            let body = std::mem::take(&mut block.body);
            block.body = body
                .into_iter()
                .enumerate()
                .flat_map(|(ni, node)| replaced.remove(&(bi, ni)).unwrap_or_else(|| vec![node]))
                .collect();
        }
        Some((out, PassWitness::AddrFold(AddrFoldWitness { folds })))
    }
}

fn mask(bits: u32) -> u128 {
    if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

pub(super) fn size_of(module: &Module, ty: &Ty) -> Option<u64> {
    module.ty_layout_shape(ty).ok()?.size_bytes()
}

/// The byte size of the allocation `root` defines.
pub(super) fn extent(
    module: &Module,
    defs: &HashMap<ValueId, &Inst>,
    root: ValueId,
) -> Option<u64> {
    match defs.get(&root)? {
        Inst::Alloca { ty, count, .. } => {
            size_of(module, ty)?.checked_mul(alloca_count(defs, *count)?)
        }
        Inst::GlobalAddr { global } => {
            size_of(module, &module.globals.get(global.index() as usize)?.ty)
        }
        _ => None,
    }
}

/// `v` as `root + offset` at pointer width (`root` `None`: a constant).
pub(super) fn read(
    module: &Module,
    defs: &HashMap<ValueId, &Inst>,
    pb: u32,
    v: ValueId,
    depth: usize,
) -> Option<(Option<ValueId>, u128)> {
    if depth > DEPTH {
        return None;
    }
    let word = |ty: &Ty| int_shape(ty, pb).is_some_and(|(b, _)| b == pb);
    let address = |ty: &Ty| {
        matches!(
            ty,
            Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
        )
    };
    let next = |x: ValueId| read(module, defs, pb, x, depth + 1);
    let m = mask(pb);
    match defs.get(&v)? {
        Inst::Alloca { .. } | Inst::GlobalAddr { .. } => Some((Some(v), 0)),
        Inst::Const {
            ty,
            value: Constant::Int(k),
        } if word(ty) => Some((None, (*k as u128) & m)),
        Inst::Copy { ty, operand } if word(ty) || address(ty) => next(*operand),
        Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => match op {
            CastOp::PtrToPtr if address(src_ty) && address(dst_ty) => next(*operand),
            CastOp::PtrToInt if address(src_ty) && word(dst_ty) => next(*operand),
            CastOp::IntToPtr if word(src_ty) && address(dst_ty) => next(*operand),
            CastOp::Bitcast if word(src_ty) && word(dst_ty) => next(*operand),
            _ => None,
        },
        Inst::BinOp { op, ty, lhs, rhs } if word(ty) => {
            let (a, b) = (next(*lhs)?, next(*rhs)?);
            match (op, a.0, b.0) {
                (BinOp::Add, _, None) => Some((a.0, a.1.wrapping_add(b.1) & m)),
                (BinOp::Add, None, Some(_)) => Some((b.0, a.1.wrapping_add(b.1) & m)),
                (BinOp::Sub, _, None) => Some((a.0, a.1.wrapping_sub(b.1) & m)),
                (BinOp::Mul, None, None) => Some((None, a.1.wrapping_mul(b.1) & m)),
                _ => None,
            }
        }
        Inst::GEP {
            pointee_ty,
            base,
            indices,
            ..
        } => {
            let elem = u128::from(size_of(module, pointee_ty)?);
            let (root, mut off) = next(*base)?;
            for index in indices {
                let Some(Inst::Const {
                    ty,
                    value: Constant::Int(k),
                }) = defs.get(index)
                else {
                    return None;
                };
                let (bits, _) = int_shape(ty, pb)?;
                off = off.wrapping_add(elem.wrapping_mul((*k as u128) & mask(bits))) & m;
            }
            Some((root, off))
        }
        _ => None,
    }
}
