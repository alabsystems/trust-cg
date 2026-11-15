// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Emit only already-selected compiler-owned argument plans.

use super::*;
use argument_plan::{Address, Input, PlannedArg};
use copy_layout::{FieldCopy, LaneCopyShape};

fn address(ctx: &mut MirLoweringCtx<'_>, block: &mut Block, source: Address) -> ValueId {
    match source {
        Address::Slot(ptr) => ptr,
        Address::Field { slot, offset } => iter_field_addr(ctx, block, slot, offset),
    }
}

pub(super) fn emit<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    block: &mut Block,
    plan: PlannedArg<'tcx>,
) -> Result<ClosureArgValues, String> {
    let mut out = ClosureArgValues::default();
    match plan {
        PlannedArg::Ignore => {}
        PlannedArg::Scalar { ty, input } => {
            let value = match input {
                Input::Value(value) => value,
                Input::Address(src) => {
                    let ptr = address(ctx, block, src);
                    emit_typed_load(ctx, block, ptr, ty.clone())
                }
            };
            out.push(ty, value);
        }
        PlannedArg::WasmCopy {
            plan,
            layout,
            address: src,
        } => {
            let src = address(ctx, block, src);
            let buffer = plan.emit_buffer(ctx, block)?;
            copy_aggregate_slot_bytes(ctx, block, &layout, src, buffer)?;
            out.push(TrustIrTy::Ptr, buffer);
        }
        PlannedArg::IndirectScalar { plan, input } => {
            let leaf = plan
                .scalar
                .expect("the checked scalar sub-lane owns its leaf");
            let value = match input {
                Input::Value(value) => value,
                Input::Address(src) => {
                    let ptr = address(ctx, block, src);
                    emit_typed_load(ctx, block, ptr, leaf.clone())
                }
            };
            let copy =
                materialize_fresh_scalar_arg_copy(ctx, block, value, leaf, plan.size, plan.align);
            out.push(TrustIrTy::Ptr, copy);
        }
        PlannedArg::IndirectCopy {
            layout,
            shape,
            address: src,
        } => {
            let src = address(ctx, block, src);
            let copy = ctx.fresh_value();
            block.body.push(
                InstrNode::new(Inst::Alloca {
                    ty: layout.slot_ty.clone(),
                    count: None,
                    align: Some(layout.align),
                })
                .with_result(copy),
            );
            emit_lane_copy(ctx, block, src, copy, &layout, shape)?;
            ctx.fresh_arg_copies.insert(copy);
            out.push(TrustIrTy::Ptr, copy);
        }
        PlannedArg::Pair {
            plan,
            address: src,
            slice,
        } => {
            let ptr = address(ctx, block, src);
            let [carrier0, carrier1] = plan.declared();
            if slice {
                out.push(carrier0, load_fat_ptr_data_at(ctx, block, ptr)?);
                out.push(carrier1, load_fat_ptr_meta_at(ctx, block, ptr));
            } else {
                for (lane, carrier) in [(0usize, carrier0), (1usize, carrier1)] {
                    let ptr = slot_byte_ptr(ctx, block, ptr, plan.offsets()[lane]);
                    let value = plan.plan.load_lane_carrier(ctx, block, ptr, lane);
                    out.push(carrier, value);
                }
            }
        }
        PlannedArg::SmallCast { plan, address: src } => {
            let ptr = address(ctx, block, src);
            out.push(plan.carrier(), plan.load_carrier(ctx, block, ptr));
        }
        PlannedArg::NarrowCast { plan, address: src } => {
            let ptr = address(ctx, block, src);
            out.push(plan.carrier.clone(), plan.load_carrier(ctx, block, ptr));
        }
        PlannedArg::Dyn {
            address: src,
            metadata_offset,
        } => {
            let ptr = address(ctx, block, src);
            out.push(
                TrustIrTy::Ptr,
                emit_typed_load(ctx, block, ptr, TrustIrTy::Ptr),
            );
            let vtable_ptr = iter_field_addr(ctx, block, ptr, metadata_offset);
            out.push(
                TrustIrTy::Ptr,
                emit_typed_load(ctx, block, vtable_ptr, TrustIrTy::Ptr),
            );
        }
        PlannedArg::Slot { ty, address: src } => out.push(ty, address(ctx, block, src)),
        PlannedArg::FieldCopy { plan, slot, offset } => {
            let ty = plan.layout.slot_ty.clone();
            let copy = emit_field_copy(ctx, block, slot, offset, *plan)?;
            out.push(ty, copy);
        }
    }
    Ok(out)
}

pub(in super::super) fn emit_lane_copy(
    ctx: &mut MirLoweringCtx<'_>,
    block: &mut Block,
    src: ValueId,
    dst: ValueId,
    layout: &MemoryAggregateLayout,
    shape: LaneCopyShape,
) -> Result<(), String> {
    match shape {
        LaneCopyShape::Bytes => copy_aggregate_slot_bytes(ctx, block, layout, src, dst),
        LaneCopyShape::Fields { fields, lane_size } => {
            for (field, ty) in fields {
                let ptr = slot_byte_ptr(ctx, block, src, u64::from(field) * lane_size);
                let value = emit_typed_load(ctx, block, ptr, ty);
                emit_aggregate_field_store(ctx, block, layout.slot_ty.clone(), dst, field, value)?;
            }
            Ok(())
        }
    }
}

pub(in super::super) fn emit_field_copy(
    ctx: &mut MirLoweringCtx<'_>,
    block: &mut Block,
    src: ValueId,
    offset: u64,
    plan: FieldCopy,
) -> Result<ValueId, String> {
    let layout = plan.layout;
    let agg = ctx.fresh_value();
    block.body.push(
        InstrNode::new(Inst::Alloca {
            ty: layout.slot_ty.clone(),
            count: None,
            align: Some(layout.align),
        })
        .with_result(agg),
    );
    for (field, ty) in plan.fields {
        let ptr = iter_field_addr(ctx, block, src, offset + u64::from(field) * plan.lane_size);
        let value = emit_typed_load(ctx, block, ptr, ty);
        emit_aggregate_field_store(ctx, block, layout.slot_ty.clone(), agg, field, value)?;
    }
    ctx.fresh_arg_copies.insert(agg);
    Ok(agg)
}
