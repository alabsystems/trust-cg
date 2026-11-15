// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Select the existing declaration's plans without emitting instructions.

use super::*;
use copy_layout::{FieldCopy, LaneCopyShape};

#[derive(Clone, Copy)]
pub(super) enum Address {
    Slot(ValueId),
    Field { slot: ValueId, offset: u64 },
}

pub(super) enum Input {
    Value(ValueId),
    Address(Address),
}

pub(super) enum PlannedArg<'tcx> {
    Ignore,
    Scalar {
        ty: TrustIrTy,
        input: Input,
    },
    WasmCopy {
        plan: Box<Wasm32IndirectCarrier>,
        layout: Box<MemoryAggregateLayout>,
        address: Address,
    },
    IndirectScalar {
        plan: Box<IndirectArgPlan<'tcx>>,
        input: Input,
    },
    IndirectCopy {
        layout: Box<MemoryAggregateLayout>,
        shape: LaneCopyShape,
        address: Address,
    },
    Pair {
        plan: Box<ScalarPairParamPlan<'tcx>>,
        address: Address,
        slice: bool,
    },
    SmallCast {
        plan: Box<SmallAggregateCastPlan>,
        address: Address,
    },
    NarrowCast {
        plan: Box<NarrowCastPlan<'tcx>>,
        address: Address,
    },
    Dyn {
        address: Address,
        metadata_offset: u64,
    },
    Slot {
        ty: TrustIrTy,
        address: Address,
    },
    FieldCopy {
        plan: Box<FieldCopy>,
        slot: ValueId,
        offset: u64,
    },
}

pub(super) fn plan<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    source: RustcFnAbiSource<'tcx>,
    arg: ClosureArg<'tcx>,
) -> Result<PlannedArg<'tcx>, String> {
    let ty = ctx.normalize_ty(ctx.monomorphize_ty(arg.ty));
    let index = arg.abi_arg_index;
    let refuse = |why: &str| {
        format!(
            "[TCG-ARG-ABI] closure argument {index} `{ty:?}`: {why}; failing closed rather than \
             passing a value in another convention than the closure body declares"
        )
    };
    let fn_abi = source.query(ctx.tcx)?;
    if !fn_abi
        .args
        .get(index)
        .is_some_and(|abi| ctx.normalize_ty(abi.layout.ty) == ty)
    {
        return Err(refuse(
            "the original FnAbi ordinal does not describe this argument type",
        ));
    }
    if is_zero_sized_call_ty(ctx.tcx, ty) {
        return Ok(PlannedArg::Ignore);
    }
    // Every field address comes from an actual tuple layout. Retain its full
    // extent and refuse a stale field coordinate before any prefix is emitted.
    if let ClosureArgSrc::TupleField {
        offset, tuple_size, ..
    } = arg.src
    {
        let size = ctx
            .tcx
            .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
            .map_err(|e| refuse(&format!("argument layout query failed: {e:?}")))?
            .size
            .bytes();
        if offset.checked_add(size).is_none_or(|end| end > tuple_size) {
            return Err(refuse(
                "the original tuple field escapes its enclosing byte image",
            ));
        }
    }
    let address = || match arg.src {
        ClosureArgSrc::Slot(ptr) => Ok(Address::Slot(ptr)),
        ClosureArgSrc::TupleField { slot, offset, .. } => Ok(Address::Field { slot, offset }),
        ClosureArgSrc::Scalar(_) => Err(refuse(
            "the call site holds it as one scalar, not its original slot bytes",
        )),
    };
    let input = || -> Result<Input, String> {
        match arg.src {
            ClosureArgSrc::Scalar(value) => Ok(Input::Value(value)),
            _ => Ok(Input::Address(address()?)),
        }
    };
    // Keep EXACTLY the plan order the declaration asks, with the same source.
    if let Some(plan) = ctx.wasm32_indirect_carrier_param(ty, index, source)? {
        if plan.carrier.is_some() {
            return Err(refuse(
                "it has a wasm32 scalar carrier through memory, which a closure body never declares",
            ));
        }
        let address = address()?;
        let layout = plan.slot_layout(ctx.tcx, ty)?;
        memory_slot_lane_ty(plan.size, plan.align)?;
        byte_copy_shape(&layout)?;
        return Ok(PlannedArg::WasmCopy {
            plan: Box::new(plan),
            layout: Box::new(layout),
            address,
        });
    }
    if let Some(plan) = ctx
        .indirect_arg_param_plan(ty, index, source)?
        .filter(|plan| plan.ty == ty)
    {
        if plan.scalar.is_some() {
            return Ok(PlannedArg::IndirectScalar {
                plan: Box::new(plan),
                input: input()?,
            });
        }
        if matches!(arg.src, ClosureArgSrc::Scalar(_)) {
            return Err(refuse("rustc passes a pointer to a copy of its bytes"));
        }
        let Some(layout) = fat_ptr_or_memory_aggregate_layout(ctx.tcx, ty)? else {
            return Err(refuse("the bridge has no memory layout for it"));
        };
        let shape = lane_copy_shape(&layout)?;
        return Ok(PlannedArg::IndirectCopy {
            layout: Box::new(layout),
            shape,
            address: address()?,
        });
    }
    if unsized_arguments::plan(ctx, ty, index, source)? {
        return Err(refuse(
            "an unsized by-value argument is not built for a closure call",
        ));
    }
    if let Some(plan) = ctx
        .scalar_pair_param_plan(ty, index, source)?
        .filter(|plan| plan.ty == ty)
    {
        let address = address()?;
        let slice =
            is_slice_fat_ptr_or_carrier(ctx.tcx, ty) || is_length_metadata_wide_ptr_ty(ctx.tcx, ty);
        if slice {
            let [carrier0, carrier1] = plan.declared();
            if carrier0 != TrustIrTy::Ptr
                || carrier1 != pointer_lane_ty()
                || plan.plan.lane_ext.iter().any(Option::is_some)
            {
                return Err(refuse(&format!(
                    "its `Pair` carriers are {carrier0:?} / {carrier1:?}, not the `Ptr` / \
                     pointer-lane pair of a `{{ data, len }}` slot"
                )));
            }
        }
        return Ok(PlannedArg::Pair {
            plan: Box::new(plan),
            address,
            slice,
        });
    }
    if let Some(plan) = ctx.small_cast_param_plan(ty, index, source)? {
        return Ok(PlannedArg::SmallCast {
            plan: Box::new(plan),
            address: address()?,
        });
    }
    if let Some(plan) = ctx
        .narrow_cast_param_plan(ty, index, source)?
        .filter(|plan| plan.ty == ty)
    {
        return Ok(PlannedArg::NarrowCast {
            plan: Box::new(plan),
            address: address()?,
        });
    }
    if is_vtable_pair_abi_ref_ty(ctx.tcx, ty) {
        return Ok(PlannedArg::Dyn {
            address: address()?,
            metadata_offset: fat_ptr_metadata_offset(ctx.tcx, ty)?,
        });
    }
    if let Some(layout) = fat_ptr_or_memory_aggregate_layout(ctx.tcx, ty)? {
        return match arg.src {
            ClosureArgSrc::Slot(ptr) => Ok(PlannedArg::Slot {
                ty: layout.slot_ty,
                address: Address::Slot(ptr),
            }),
            ClosureArgSrc::TupleField {
                slot,
                offset,
                tuple_size,
            } => {
                if is_slice_fat_ptr_or_carrier(ctx.tcx, ty)
                    || is_length_metadata_wide_ptr_ty(ctx.tcx, ty)
                {
                    if wide_slice_carrier_layout(ctx.tcx, ty).is_some() {
                        return Err(refuse(
                            "a transparent wide-slice newtype element of the argument tuple carries one lane",
                        ));
                    }
                    Ok(PlannedArg::Slot {
                        ty: layout.slot_ty,
                        address: Address::Field { slot, offset },
                    })
                } else {
                    let plan = plan_field_copy(ctx.tcx, ty, offset, tuple_size)?;
                    Ok(PlannedArg::FieldCopy {
                        plan: Box::new(plan),
                        slot,
                        offset,
                    })
                }
            }
            ClosureArgSrc::Scalar(_) => Err(refuse("its declaration is a memory slot")),
        };
    }
    let elem_ir = rust_ty_to_trust_ir_ty(ctx.tcx, ty)?;
    if trust_ir_ty_is_zero_sized(&elem_ir) {
        return Ok(PlannedArg::Ignore);
    }
    if elem_ir.bit_width().is_none() && !is_pointer_like_trust_ir_ty(&elem_ir) {
        return Err(refuse("it is not a scalar"));
    }
    ctx.refuse_scalar_declared_memory_arg(ty, index, source, &elem_ir)?;
    Ok(PlannedArg::Scalar {
        ty: elem_ir,
        input: input()?,
    })
}
