//! Zero-size field addresses share their scalar owner's checked storage.
// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
use super::*;

/// The ordinary scalar-wrapper path, plus genuine pointer-valued owners on
/// targets whose scalar cells retain pointer extent metadata. Collection
/// images and owning/drop values remain subject to the caller's exclusions.
pub(super) fn field_owner_has_scalar_storage<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    local: Local,
) -> bool {
    let ty = ctx.monomorphize_ty(local_rust_ty(ctx, body, local));
    rust_ty_to_trust_ir_ty(ctx.tcx, ty)
        .map(|leaf| {
            (leaf.bit_width().is_some() && !is_pointer_like_trust_ir_ty(&leaf))
                || (is_pointer_like_trust_ir_ty(&leaf)
                    && scalar_cell_storage_for_target(ctx, &leaf).is_some()
                    && local_is_single_scalar_storage(ctx, local))
        })
        .unwrap_or(false)
}

/// Resolve only a Field chain ending at a sized zero-byte leaf. A cell's
/// actual allocation, rustc's container layouts, and the MIR leaf type must
/// agree. In particular a tail ZST may be at the allocation's end; it has
/// that one-past address, not a separate placeholder or the owner's value.
pub(super) fn field_offset<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    source: &Place<'tcx>,
) -> Result<Option<u64>, String> {
    if source.projection.is_empty()
        || !source
            .projection
            .iter()
            .all(|elem| matches!(elem, ProjectionElem::Field(..)))
    {
        return Ok(None);
    }
    let leaf_ty = ctx.normalize_ty(ctx.monomorphize_ty(place_rust_ty(ctx, body, source)));
    if !is_zero_sized_ty(ctx.tcx, leaf_ty) {
        return Ok(None);
    }
    let Some(cell) = exclusive_scalar_cell(&ctx.scalar_cells, &ctx.memory_slots, source.local)
    else {
        return Ok(None);
    };
    let reject = || {
        "[TCG-SCALAR-CELL-LAYOUT] zero-sized field must lie in its scalar owner's checked allocation".to_owned()
    };
    let storage = cell.storage.ok_or_else(reject)?;
    let owner_ty = ctx.normalize_ty(ctx.monomorphize_ty(local_rust_ty(ctx, body, source.local)));
    if memory_scalar_leaf_ty(ctx.tcx, owner_ty)? != cell.allocated_ty {
        return Err(reject());
    }
    let cx = LayoutCx(ctx.tcx);
    let mut layout = ctx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(owner_ty))
        .map_err(|_| reject())?;
    if !layout.is_sized() || layout.size.bytes() < storage.size {
        return Err(reject());
    }
    if let Some(home) = cell.home {
        if layout.size.bytes() != home.size || layout.align.bytes() != home.align {
            return Err(reject());
        }
    } else {
        // This is the same extent/alignment admission used to allocate the cell,
        // including a padded scalar on wasm32. It cannot license another home.
        scalar_leaf_object_extent(ctx.tcx, owner_ty, &cell.allocated_ty)?;
    }
    let owner_size = layout.size.bytes();
    let owner_align = layout.align.bytes();
    let mut offset = 0_u64;
    for elem in source.projection.iter() {
        let ProjectionElem::Field(field, _) = elem else {
            return Err(reject());
        };
        let container = matches!(layout.ty.kind(), ty::Adt(def, _) if def.is_struct())
            || matches!(layout.ty.kind(), ty::Tuple(_) | ty::Closure(..));
        if !container || !layout.is_sized() || field.index() >= layout.fields.count() {
            return Err(reject());
        }
        let selected = layout.field(&cx, field.index());
        let field_offset = layout.fields.offset(field.index()).bytes();
        let field_end = field_offset
            .checked_add(selected.size.bytes())
            .ok_or_else(reject)?;
        offset = offset.checked_add(field_offset).ok_or_else(reject)?;
        if !selected.is_sized()
            || field_end > layout.size.bytes()
            || offset > owner_size
            || selected.align.bytes() > owner_align
            || offset % selected.align.bytes() != 0
        {
            return Err(reject());
        }
        layout = selected;
    }
    if !layout.is_zst() || ctx.normalize_ty(ctx.monomorphize_ty(layout.ty)) != leaf_ty {
        return Err(reject());
    }
    Ok(Some(offset))
}

pub(super) fn field_address<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    source: &Place<'tcx>,
) -> Result<Option<ValueId>, String> {
    let Some(offset) = field_offset(ctx, body, source)? else {
        return Ok(None);
    };
    let base = ctx.scalar_cells[&source.local].ptr;
    Ok(Some(slot_byte_ptr(ctx, block, base, offset)))
}
