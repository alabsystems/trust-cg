//! Whole two-word pointer images read or written through fixed projections.
//! Rust layout supplies the field offset; both lanes are loaded before either
//! destination lane is written, including self-copies and overlapping images.

use super::*;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Metadata {
    Length,
    Vtable,
}

impl Metadata {
    fn ty(self) -> TrustIrTy {
        match self {
            Self::Length => TrustIrTy::I64,
            Self::Vtable => TrustIrTy::Ptr,
        }
    }
}

fn metadata<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<Metadata> {
    let pointee = pointer_coercions::wide_pointee(tcx, ty)?;
    let tail = tcx.struct_tail_for_codegen(pointee, ty::TypingEnv::fully_monomorphized());
    match tail.kind() {
        ty::Slice(_) | ty::Str => Some(Metadata::Length),
        ty::Dynamic(..) => Some(Metadata::Vtable),
        _ => None,
    }
}

pub(super) fn is_deref_read<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    place: &Place<'tcx>,
) -> bool {
    matches!(place.projection.first(), Some(ProjectionElem::Deref))
        && place.projection[1..]
            .iter()
            .all(|p| matches!(p, ProjectionElem::Field(..) | ProjectionElem::Downcast(..)))
        && is_thin_pointer_ref_ty(
            ctx.tcx,
            ctx.monomorphize_ty(local_rust_ty(ctx, body, place.local)),
        )
        && metadata(ctx.tcx, place_rust_ty(ctx, body, place)).is_some()
}

fn address<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    place: &Place<'tcx>,
    write: bool,
) -> Result<Option<ValueId>, String> {
    let leading_deref = matches!(place.projection.first(), Some(ProjectionElem::Deref));
    if !place.projection[usize::from(leading_deref)..]
        .iter()
        .all(|p| matches!(p, ProjectionElem::Field(..) | ProjectionElem::Downcast(..)))
    {
        return Ok(None);
    }
    let local_ty = ctx.monomorphize_ty(local_rust_ty(ctx, body, place.local));
    let base_ty = if leading_deref {
        let (ty::Ref(_, pointee, mutability) | ty::RawPtr(pointee, mutability)) = local_ty.kind()
        else {
            return Ok(None);
        };
        if !is_thin_pointer_ref_ty(ctx.tcx, local_ty) {
            return Ok(None);
        }
        if write
            && matches!(local_ty.kind(), ty::Ref(..))
            && *mutability != rustc_hir::Mutability::Mut
        {
            return Err("wide-pointer image store through shared reference".to_owned());
        }
        ctx.monomorphize_ty(*pointee)
    } else {
        if !ctx.memory_slots.contains_key(&place.local) {
            return Ok(None);
        }
        local_ty
    };
    let layout = ctx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(base_ty))
        .map_err(|e| format!("wide-pointer projection layout: {e:?}"))?;
    if !layout.is_sized() {
        return Ok(None);
    }
    // A reference to an intercepted collection does not denote rustc's inline
    // image. Keep the same recursive exclusions as actual aggregate storage.
    validate_memory_aggregate_field_leaves(ctx.tcx, &LayoutCx(ctx.tcx), &layout)?;
    let (offset, leaf_ty) = walk_memory_projection_offset_raw(ctx, base_ty, &place.projection)?;
    if ctx.normalize_ty(leaf_ty) != ctx.normalize_ty(place_rust_ty(ctx, body, place))
        || metadata(ctx.tcx, leaf_ty).is_none()
        || offset
            .checked_add(16)
            .is_none_or(|end| end > layout.size.bytes())
    {
        return Err("wide-pointer projection does not identify a complete image".to_owned());
    }
    let base = if leading_deref {
        lower_operand_to_value(ctx, body, block, &Operand::Copy(Place::from(place.local)))?
    } else {
        memory_slot_ptr(ctx, place.local)?
    };
    let base = coerce_to_plain_ptr(ctx, block, base);
    Ok(Some(iter_field_addr(ctx, block, base, offset)))
}

pub(super) fn assign<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    dst: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Result<bool, String> {
    let (source, cast) = match rvalue {
        Rvalue::Use(Operand::Copy(p) | Operand::Move(p), _) => (p, false),
        Rvalue::Cast(
            mir::CastKind::Transmute | mir::CastKind::PtrToPtr,
            Operand::Copy(p) | Operand::Move(p),
            _,
        ) => (p, true),
        _ => return Ok(false),
    };
    if dst.projection.is_empty() && source.projection.is_empty() {
        return Ok(false);
    }
    let src_ty = ctx.normalize_ty(place_rust_ty(ctx, body, source));
    let dst_ty = ctx.normalize_ty(place_rust_ty(ctx, body, dst));
    let (Some(src_meta), Some(dst_meta)) = (metadata(ctx.tcx, src_ty), metadata(ctx.tcx, dst_ty))
    else {
        return Ok(false);
    };
    if src_meta != dst_meta || (!cast && src_ty != dst_ty) {
        return Ok(false);
    }
    // Existing bare-pointer paths retain their representation decisions. This
    // path adds checked wrappers as either the source or destination image.
    if !matches!(src_ty.kind(), ty::Adt(..)) && !matches!(dst_ty.kind(), ty::Adt(..)) {
        return Ok(false);
    }
    let (data, meta) = if let Some(address) = address(ctx, body, block, source, false)? {
        let data = emit_typed_load(ctx, block, address, TrustIrTy::Ptr);
        let metadata_address = iter_field_addr(ctx, block, address, 8);
        let meta = emit_typed_load(ctx, block, metadata_address, src_meta.ty());
        (data, meta)
    } else if source.projection.is_empty() {
        let (Some(data), Some(meta)) = (
            ctx.projected_values.get(&(source.local, 0)).copied(),
            ctx.projected_values.get(&(source.local, 1)).copied(),
        ) else {
            return Ok(false);
        };
        (data, meta)
    } else {
        return Ok(false);
    };
    let data = coerce_to_plain_ptr(ctx, block, data);
    let meta = match dst_meta {
        Metadata::Length => coerce_to_i64(ctx, block, meta),
        Metadata::Vtable => coerce_to_plain_ptr(ctx, block, meta),
    };
    if let Some(address) = address(ctx, body, block, dst, true)? {
        emit_typed_store(block, address, TrustIrTy::Ptr, data);
        let metadata_address = iter_field_addr(ctx, block, address, 8);
        emit_typed_store(block, metadata_address, dst_meta.ty(), meta);
        if dst.projection.is_empty() {
            ctx.clear_full_place_bindings(dst.local);
        }
    } else if dst.projection.is_empty() {
        ctx.clear_full_place_bindings(dst.local);
        ctx.bind_projected_value(dst.local, 0, data);
        ctx.bind_projected_value(dst.local, 1, meta);
    } else {
        return Ok(false);
    }
    Ok(true)
}
