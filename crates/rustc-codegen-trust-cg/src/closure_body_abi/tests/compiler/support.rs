// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn closure<'tcx>(
    tcx: TyCtxt<'tcx>,
    name: &str,
) -> (MirLoweringCtx<'tcx>, Instance<'tcx>) {
    let owner = tcx
        .hir_body_owners()
        .find(|definition| {
            matches!(
                tcx.def_kind(definition.to_def_id()),
                rustc_hir::def::DefKind::Fn
            ) && tcx.item_name(definition.to_def_id()).as_str() == name
        })
        .unwrap_or_else(|| panic!("missing original source function {name}"));
    let parent = Instance::mono(tcx, owner.to_def_id());
    let body = tcx.instance_mir(parent.def);
    let ctx = MirLoweringCtx::new(name, tcx, parent);
    let closure_ty = body
        .local_decls
        .iter()
        .map(|decl| ctx.monomorphize_ty(decl.ty))
        .find(|ty| matches!(ty.kind(), ty::Closure(..)))
        .unwrap_or_else(|| panic!("{name}: actual closure local"));
    let instance = closure_body_instance(&ctx, closure_ty).unwrap();
    (MirLoweringCtx::new(name, tcx, instance), instance)
}

pub(super) fn loads(block: &Block) -> Vec<TrustIrTy> {
    block
        .body
        .iter()
        .filter_map(|node| match &node.inst {
            Inst::Load { ty, .. } => Some(ty.clone()),
            _ => None,
        })
        .collect()
}

pub(super) fn addresses(block: &Block, slot: ValueId) -> Vec<u64> {
    load_origins(block)
        .into_iter()
        .map(|(base, offset)| {
            assert_eq!(base, slot);
            offset
        })
        .collect()
}

pub(super) fn load_origins(block: &Block) -> Vec<(ValueId, u64)> {
    block
        .body
        .iter()
        .filter_map(|node| match &node.inst {
            Inst::Load { ptr, .. } => Some(*ptr),
            _ => None,
        })
        .map(|address| {
            let Inst::Cast {
                op: CastOp::IntToPtr,
                operand,
                ..
            } = definition(block, address)
            else {
                panic!("byte address must use the canonical pointer conversion")
            };
            let Inst::BinOp {
                op: TrustIrBinOp::Add,
                lhs,
                rhs,
                ..
            } = definition(block, *operand)
            else {
                panic!("original byte offset plus original slot base")
            };
            let Inst::Cast {
                op: CastOp::PtrToInt,
                operand,
                ..
            } = definition(block, *lhs)
            else {
                panic!("original slot base")
            };
            let slot = uncopy(block, *operand);
            let Inst::Const {
                value: Constant::Int(offset),
                ..
            } = definition(block, uncopy(block, *rhs))
            else {
                panic!("literal original layout offset")
            };
            (
                slot,
                u64::try_from(*offset).expect("nonnegative original layout offset"),
            )
        })
        .collect()
}

fn definition(block: &Block, value: ValueId) -> &Inst {
    &block
        .body
        .iter()
        .find(|node| node.results.contains(&value))
        .expect("actual emitted value definition")
        .inst
}

fn uncopy(block: &Block, mut value: ValueId) -> ValueId {
    while let Some(node) = block.body.iter().find(|node| node.results.contains(&value)) {
        let Inst::Copy { operand, .. } = &node.inst else {
            break;
        };
        value = *operand;
    }
    value
}
