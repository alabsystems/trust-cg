// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The existing byte/lane-copy checks, reusable before any emitted prefix.

use super::*;

pub(in super::super) enum LaneCopyShape {
    Bytes,
    Fields {
        fields: Vec<(u32, TrustIrTy)>,
        lane_size: u64,
    },
}

pub(in super::super) fn byte_copy_shape(
    layout: &MemoryAggregateLayout,
) -> Result<(TrustIrTy, u64), String> {
    let align = layout.align;
    let (lane_ty, lane_size) = memory_aggregate_lane(align).map_err(|_| {
        format!(
            "[TCG-SRET-ABI] aggregate buffer copy with {align}-byte alignment is not \
             modeled; failing closed rather than moving the bytes at a width the layout \
             does not tile."
        )
    })?;
    if layout.size % lane_size != 0 {
        return Err(format!(
            "[TCG-SRET-ABI] aggregate buffer of {} bytes does not tile into {lane_size}-byte \
             lanes; failing closed rather than copying a partial trailing lane.",
            layout.size
        ));
    }
    Ok((lane_ty, lane_size))
}

pub(in super::super) fn lane_copy_shape(
    layout: &MemoryAggregateLayout,
) -> Result<LaneCopyShape, String> {
    if layout.size == 24 && layout.align == 8 && layout.slot_ty == vec_slot_ty() {
        byte_copy_shape(layout)?;
        return Ok(LaneCopyShape::Bytes);
    }
    let (lane_ty, lane_size) = memory_aggregate_lane(layout.align)?;
    let fields = aggregate_memory_field_tys(&layout.slot_ty)?;
    let covers = u64::try_from(fields.len())
        .ok()
        .and_then(|n| n.checked_mul(lane_size))
        == Some(layout.size);
    if !covers || fields.iter().any(|(_, ty)| *ty != lane_ty) {
        return Err(format!(
            "[TCG-ARG-ABI] the {}-byte / align-{} slot {:?} is not a uniform tuple of \
             {lane_size}-byte lanes, so a lane copy would not reproduce its bytes; failing \
             closed",
            layout.size, layout.align, layout.slot_ty
        ));
    }
    Ok(LaneCopyShape::Fields { fields, lane_size })
}

pub(in super::super) struct FieldCopy {
    pub(in super::super) layout: std::rc::Rc<MemoryAggregateLayout>,
    pub(in super::super) fields: Vec<(u32, TrustIrTy)>,
    pub(in super::super) lane_size: u64,
}

pub(in super::super) fn plan_field_copy<'tcx>(
    tcx: TyCtxt<'tcx>,
    elem_ty: Ty<'tcx>,
    base_offset: u64,
    enclosing_size: u64,
) -> Result<FieldCopy, String> {
    let Some(layout) = memory_aggregate_layout_shared(tcx, elem_ty)? else {
        return Err(format!(
            "by-value aggregate element has no aggregate layout: {elem_ty:?}"
        ));
    };
    if layout.align == 0 || layout.size % layout.align != 0 {
        return Err(format!(
            "by-value aggregate element size {} is not a multiple of align {} ({elem_ty:?})",
            layout.size, layout.align
        ));
    }
    if base_offset
        .checked_add(layout.size)
        .is_none_or(|end| end > enclosing_size)
    {
        return Err(format!(
            "by-value aggregate element [{base_offset}, +{}) escapes the enclosing {enclosing_size}-byte slot ({elem_ty:?})",
            layout.size
        ));
    }
    let fields = aggregate_memory_field_tys(&layout.slot_ty)?;
    let (_, lane_size) = memory_aggregate_lane(layout.align)?;
    if u64::try_from(fields.len())
        .ok()
        .and_then(|n| n.checked_mul(lane_size))
        != Some(layout.size)
    {
        return Err(format!(
            "by-value aggregate element lane tuple ({} lanes of {}B) does not cover its {}B size ({elem_ty:?})",
            fields.len(),
            lane_size,
            layout.size
        ));
    }
    Ok(FieldCopy {
        layout,
        fields,
        lane_size,
    })
}
