// trust-cg-irmid/passes/dce.rs - pure dead-code elimination
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Pure dead-code elimination: an instruction from the removable allowlist
//! whose results no live instruction uses is removed. `insertfield` and
//! `extractfield` are on the list only over a value of their own aggregate
//! type: the rustc bridge's forms over a pointer are a store and a load. An
//! instruction whose definedness depends on its operands' values (division,
//! remainder and shifts, except by a constant that cannot fault at a fixed
//! width, float-to-int, `bool`/`char` conversions and
//! int-to-pointer conversions from an integer wider than a wasm32 address
//! (one at most 32 bits wide, `isize` or `usize`, is total on a defined
//! integer and the lane does not read it as exposing anything), a load or GEP from anything but a fresh allocation (an
//! `alloca`, count-free or counted by an integer constant of at least 1) or a
//! global, or a pointer computed from one by constant `gep`s, `ptrtoptr`s
//! and copies) is not on it: the wasm lane reads such an
//! instruction over an address's bits as exposing the address, and removing
//! it would let the lane share bytes the source program could still reach. Liveness starts at every
//! instruction outside the allowlist (effects, terminators, anything the pass
//! does not know) and flows back through operands.
//!
//! Each removal is labelled: `Exact` for an instruction that raises nothing on
//! any input of a well-typed module (a constant, a global's address, `undef`,
//! a type-preserving `copy`), `Refinement` for one that may raise undefined
//! behaviour on some input (arithmetic inspecting poison, a division by zero,
//! a load, an address computation, an allocation). The checker re-derives the
//! label and refuses a mislabelled removal.

use std::collections::HashSet;

use trust_cg_verify::trust_ir_mid_tv::{DceWitness, DeadRemoval, PassWitness, RemovalClass};
use trust_ir::{BinOp, CastOp, Function, Inst, Ty, ValueId};

use super::{MidPass, PassContext, drop_names, sole_defs, value_types};

pub(crate) struct Dce;

/// The pass's removable allowlist and labels. `operand_ty` types an operand;
/// `def` names the single-result instruction defining one.
pub(crate) fn removable<'f>(
    inst: &Inst,
    operand_ty: impl Fn(ValueId) -> Option<Ty>,
    def: impl Fn(ValueId) -> Option<&'f Inst>,
) -> Option<RemovalClass> {
    // An allocation's count: none, or an integer constant of at least 1.
    let counted = |count: Option<ValueId>| match count {
        None => true,
        Some(count) => matches!(
            def(count),
            Some(Inst::Const {
                ty,
                value: trust_ir::Constant::Int(k),
            }) if ty.is_integer() && *k >= 1
        ),
    };
    // A fresh allocation or a global's address, or a pointer computed from
    // one by `gep`s by constants, `ptrtoptr`s and copies (a bounded chain).
    let fresh = |v: ValueId| {
        let mut v = v;
        for _ in 0..64 {
            match def(v) {
                Some(Inst::Alloca { count, .. }) => return counted(*count),
                Some(Inst::GlobalAddr { .. }) => return true,
                Some(Inst::GEP { base, indices, .. })
                    if indices
                        .iter()
                        .all(|i| matches!(def(*i), Some(Inst::Const { .. }))) =>
                {
                    v = *base;
                }
                Some(
                    Inst::Cast {
                        op: CastOp::PtrToPtr,
                        operand,
                        ..
                    }
                    | Inst::Copy { operand, .. },
                ) => v = *operand,
                _ => return false,
            }
        }
        false
    };
    match inst {
        Inst::Const { .. } | Inst::NullPtr | Inst::GlobalAddr { .. } | Inst::Undef { .. } => {
            Some(RemovalClass::Exact)
        }
        Inst::Copy { ty, operand } => Some(if operand_ty(*operand).as_ref() == Some(ty) {
            RemovalClass::Exact
        } else {
            RemovalClass::Refinement
        }),
        Inst::BinOp { op, ty, rhs, .. } => match op {
            BinOp::UDiv
            | BinOp::SDiv
            | BinOp::URem
            | BinOp::SRem
            | BinOp::Shl
            | BinOp::LShr
            | BinOp::AShr => {
                // Total on a constant amount or divisor that cannot fault,
                // at a fixed width.
                let bits = ty
                    .bit_width()
                    .filter(|_| ty.is_integer() && !matches!(ty, Ty::Isize | Ty::Usize))?;
                let k = match def(*rhs)? {
                    Inst::Const {
                        ty: kt,
                        value: trust_ir::Constant::Int(k),
                    } if kt.bit_width() == Some(bits) => *k,
                    _ => return None,
                };
                let all = if bits >= 128 {
                    u128::MAX
                } else {
                    (1u128 << bits) - 1
                };
                let k = (k as u128) & all;
                let total = match op {
                    BinOp::Shl | BinOp::LShr | BinOp::AShr => k < u128::from(bits),
                    BinOp::UDiv | BinOp::URem => k != 0,
                    _ => k != 0 && k != all,
                };
                total.then_some(RemovalClass::Refinement)
            }
            _ => Some(RemovalClass::Refinement),
        },
        Inst::Cast {
            op, src_ty, dst_ty, ..
        } => match (op, dst_ty) {
            (_, Ty::Bool | Ty::Char) => None,
            (CastOp::IntToPtr, _)
                if matches!(src_ty, Ty::Isize | Ty::Usize)
                    || (src_ty.is_integer() && src_ty.bit_width().is_some_and(|w| w <= 32)) =>
            {
                Some(RemovalClass::Refinement)
            }
            (CastOp::FPToUI | CastOp::FPToSI | CastOp::IntToPtr | CastOp::Transmute, _) => None,
            _ => Some(RemovalClass::Refinement),
        },
        Inst::UnOp { .. }
        | Inst::Overflow { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Select { .. }
        | Inst::PtrData { .. }
        | Inst::PtrMetadata { .. }
        | Inst::MakeAggregate { .. }
        | Inst::ArraySplat { .. }
        | Inst::Alloca { count: None, .. } => Some(RemovalClass::Refinement),
        Inst::Alloca {
            count: Some(count), ..
        } if counted(Some(*count)) => Some(RemovalClass::Refinement),
        Inst::ExtractField { ty, aggregate, .. } | Inst::InsertField { ty, aggregate, .. }
            if operand_ty(*aggregate).as_ref() == Some(ty) =>
        {
            Some(RemovalClass::Refinement)
        }
        Inst::Load {
            volatile: false,
            ptr,
            ..
        } if fresh(*ptr) => Some(RemovalClass::Refinement),
        Inst::GEP { base, indices, .. }
            if fresh(*base)
                && indices
                    .iter()
                    .all(|i| matches!(def(*i), Some(Inst::Const { .. }))) =>
        {
            Some(RemovalClass::Refinement)
        }
        _ => None,
    }
}

impl MidPass for Dce {
    fn name(&self) -> &'static str {
        "dce"
    }

    fn run(&self, _cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let types = value_types(func);
        let operand_ty = |v: ValueId| types.get(&v).cloned();
        let defs = sole_defs(func);
        let def = |v: ValueId| defs.get(&v).copied();
        // Seed liveness with every operand of a node that must stay.
        let mut live: HashSet<ValueId> = HashSet::new();
        let mut work: Vec<ValueId> = Vec::new();
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            let stays = node.results.is_empty() || removable(&node.inst, operand_ty, def).is_none();
            if stays {
                node.inst.visit_value_operands(|v| {
                    if live.insert(v) {
                        work.push(v);
                    }
                });
            }
        }
        // A live value defined by a removable node keeps that node's operands.
        // Multi-result removable nodes are kept whole when any result is live.
        let mut multi: Vec<&trust_ir::InstrNode> = Vec::new();
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            if node.results.len() > 1 {
                multi.push(node);
            }
        }
        loop {
            while let Some(value) = work.pop() {
                if let Some(inst) = defs.get(&value) {
                    inst.visit_value_operands(|v| {
                        if live.insert(v) {
                            work.push(v);
                        }
                    });
                }
            }
            let mut grew = false;
            for node in &multi {
                if node.results.iter().any(|r| live.contains(r)) {
                    node.inst.visit_value_operands(|v| {
                        if live.insert(v) {
                            work.push(v);
                            grew = true;
                        }
                    });
                }
            }
            if !grew {
                break;
            }
        }
        let mut removals = Vec::new();
        let mut removed: HashSet<ValueId> = HashSet::new();
        for block in &func.blocks {
            for (index, node) in block.body.iter().enumerate() {
                if node.results.is_empty() || node.results.iter().any(|r| live.contains(r)) {
                    continue;
                }
                let Some(class) = removable(&node.inst, operand_ty, def) else {
                    continue;
                };
                removed.extend(node.results.iter().copied());
                removals.push(DeadRemoval {
                    block: block.id,
                    index,
                    results: node.results.clone(),
                    class,
                });
            }
        }
        if removals.is_empty() {
            return None;
        }
        let mut out = func.clone();
        for block in &mut out.blocks {
            block
                .body
                .retain(|n| n.results.is_empty() || !n.results.iter().all(|r| removed.contains(r)));
        }
        drop_names(&mut out, &removed);
        Some((out, PassWitness::Dce(DceWitness { removals })))
    }
}
