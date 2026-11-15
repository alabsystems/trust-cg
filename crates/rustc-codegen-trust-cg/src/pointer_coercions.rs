//! Unsize actual pointer-wrapper images on Linux AArch64. The wrapper walk
//! proves that both source and destination have exactly their pointer's image;
//! the data address remains the address of the whole allocation, even when its
//! unsized tail is preceded by a header (for example RcInner or ArcInner).

use super::*;

fn payload<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<(usize, Ty<'tcx>)> {
    let ty::Adt(adt, args) = ty.kind() else {
        return None;
    };
    if !adt.is_struct() {
        return None;
    }
    let env = ty::TypingEnv::fully_monomorphized();
    let layout = tcx.layout_of(env.as_query_input(ty)).ok()?;
    let mut payload = None;
    for (index, field) in adt.non_enum_variant().fields.iter().enumerate() {
        let field_ty = tcx.normalize_erasing_regions(env, field.ty(tcx, *args));
        let field_layout = tcx.layout_of(env.as_query_input(field_ty)).ok()?;
        if field_layout.is_zst() {
            continue;
        }
        if payload.is_some()
            || layout.fields.offset(index).bytes() != 0
            || layout.size != field_layout.size
            || layout.align.bytes() != field_layout.align.bytes()
            || layout.backend_repr != field_layout.backend_repr
        {
            return None;
        }
        payload = Some((index, field_ty));
    }
    payload
}

/// Walk the same ADT chain on both sides, checking every actual layout.
/// Multi-field custom allocators and wrappers are deliberately outside this path.
fn pointer_pair<'tcx>(
    tcx: TyCtxt<'tcx>,
    mut src: Ty<'tcx>,
    mut dst: Ty<'tcx>,
) -> Option<(Ty<'tcx>, Ty<'tcx>, bool)> {
    let env = ty::TypingEnv::fully_monomorphized();
    for _ in 0..32 {
        if let ty::Pat(base, _) = src.kind() {
            src = *base;
            continue;
        }
        if let ty::Pat(base, _) = dst.kind() {
            dst = *base;
            continue;
        }
        match (src.kind(), dst.kind()) {
            (ty::Adt(a, _), ty::Adt(b, _)) if a.did() == b.did() => {
                let (si, s) = payload(tcx, src)?;
                let (di, d) = payload(tcx, dst)?;
                if si != di {
                    return None;
                }
                src = s;
                dst = d;
            }
            (ty::Ref(_, s, _) | ty::RawPtr(s, _), ty::Ref(_, d, _) | ty::RawPtr(d, _)) => {
                let sl = tcx.layout_of(env.as_query_input(src)).ok()?;
                let dl = tcx.layout_of(env.as_query_input(dst)).ok()?;
                let wide = crate::scalar_pair::view(sl.backend_repr).is_some();
                if dl.size.bytes() != 16
                    || dl.align.bytes() != 8
                    || !crate::scalar_pair::view(dl.backend_repr).is_some()
                    || fat_ptr_metadata_offset(tcx, dst).ok()? != 8
                    || sl.align.bytes() != 8
                    || if wide {
                        sl.size.bytes() != 16 || fat_ptr_metadata_offset(tcx, src).ok()? != 8
                    } else {
                        sl.size.bytes() != 8
                            || !matches!(sl.backend_repr, rustc_abi::BackendRepr::Scalar(s) if matches!(s.primitive(), rustc_abi::Primitive::Pointer(_)))
                    }
                {
                    return None;
                }
                return Some((*s, *d, wide));
            }
            _ => return None,
        }
    }
    None
}

/// The pointee of a fully checked two-word pointer or pointer-wrapper image.
pub(super) fn wide_pointee<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    if tcx.sess.target.arch.desc() != "aarch64"
        || tcx.sess.target.os != rustc_target::spec::Os::Linux
    {
        return None;
    }
    let (pointee, _, wide) = pointer_pair(tcx, ty, ty)?;
    wide.then_some(pointee)
}

pub(super) fn assign<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Result<bool, String> {
    if ctx.tcx.sess.target.arch.desc() != "aarch64"
        || ctx.tcx.sess.target.os != rustc_target::spec::Os::Linux
    {
        return Ok(false);
    }
    if constant_image(ctx, body, block, place, rvalue)? {
        return Ok(true);
    }
    let Rvalue::Cast(mir::CastKind::PointerCoercion(PointerCoercion::Unsize, _), operand, dst_ty) =
        rvalue
    else {
        return Ok(false);
    };
    let dst_ty = ctx.monomorphize_ty(*dst_ty);
    if !matches!(dst_ty.kind(), ty::Adt(..)) {
        return Ok(false);
    }
    let src_ty = ctx.monomorphize_ty(operand.ty(&body.local_decls, ctx.tcx));
    let Some((src, dst, wide)) = pointer_pair(ctx.tcx, src_ty, dst_ty) else {
        return Err(format!(
            "[TCG-POINTER-COERCION-IMAGE] unsupported wrapper images: {src_ty:?} -> {dst_ty:?}"
        ));
    };
    if !place.projection.is_empty() {
        return Err("[TCG-POINTER-COERCION-IMAGE] projected unsize destination".to_owned());
    }
    let (src_tail, dst_tail) =
        ctx.tcx
            .struct_lockstep_tails_for_codegen(src, dst, ty::TypingEnv::fully_monomorphized());
    // Linux's wrapper path also handles genuine Box<T> -> Box<dyn Trait>.
    // Only an exact live constructor value may name the bridge's map image;
    // the Box type or an address recovered through a load grants no receipt.
    let locally_owned_image = box_dyn_dynamic_data(ctx.tcx, dst_ty).is_some()
        && box_element_ty(ctx.tcx, src_ty).is_some()
        && operand_is_bridge_map_image(ctx, operand);
    let (data, old_meta) = if wide {
        let (Operand::Copy(p) | Operand::Move(p)) = operand else {
            return Err(
                "pointer-wrapper unsize requires a complete runtime wide source".to_owned(),
            );
        };
        if !p.projection.is_empty() {
            return Err("pointer-wrapper unsize projected wide source".to_owned());
        }
        let (data, meta) = dyn_fat_ptr_halves_of_local(ctx, block, p.local)
            .ok_or_else(|| "pointer-wrapper unsize has no complete source pair".to_owned())?;
        (data, Some(meta))
    } else {
        let data = match operand {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
                if let Some(slot) = ctx.memory_slots.get(&p.local).cloned() {
                    let address = coerce_to_plain_ptr(ctx, block, slot.ptr);
                    emit_typed_load(ctx, block, address, TrustIrTy::Ptr)
                } else {
                    lower_operand_to_value(ctx, body, block, operand)?
                }
            }
            _ => lower_operand_to_value(ctx, body, block, operand)?,
        };
        (coerce_to_plain_ptr(ctx, block, data), None)
    };
    let (meta, meta_ty) = match (src_tail.kind(), dst_tail.kind()) {
        (ty::Array(se, len), ty::Slice(de)) if se == de && !wide => {
            let len = len
                .try_to_target_usize(ctx.tcx)
                .ok_or_else(|| "pointer-wrapper unsize length is not concrete".to_owned())?;
            (emit_i64_const(ctx, block, i128::from(len)), TrustIrTy::I64)
        }
        (_, ty::Dynamic(dst_traits, _)) => {
            let vtable = if let ty::Dynamic(src_traits, _) = src_tail.kind() {
                let mut vtable = old_meta
                    .ok_or_else(|| "pointer-wrapper dyn source has no metadata".to_owned())?;
                if src_traits.principal_def_id() != dst_traits.principal_def_id()
                    && dst_traits.principal_def_id().is_some()
                {
                    if let Some(index) = ctx.tcx.supertrait_vtable_slot((src_tail, dst_tail)) {
                        let offset = u64::try_from(index)
                            .ok()
                            .and_then(|n| n.checked_mul(8))
                            .ok_or_else(|| "pointer-wrapper upcast offset overflow".to_owned())?;
                        let address = iter_field_addr(ctx, block, vtable, offset);
                        vtable = emit_typed_load(ctx, block, address, TrustIrTy::Ptr);
                    }
                }
                vtable
            } else {
                if wide {
                    return Err("pointer-wrapper dyn unsize requires a sized source".to_owned());
                }
                let principal = dst_traits
                    .principal()
                    .map(|p| ctx.tcx.instantiate_bound_regions_with_erased(p))
                    .ok_or_else(|| {
                        "pointer-wrapper dyn unsize has no principal trait".to_owned()
                    })?;
                emit_vtable_ptr_value(
                    ctx,
                    block,
                    src_tail,
                    principal.with_self_ty(ctx.tcx, src_tail),
                    if locally_owned_image {
                        heap_image_glue::VtableDropOrigin::OwnedBox
                    } else {
                        heap_image_glue::VtableDropOrigin::Other
                    },
                )?
            };
            (vtable, TrustIrTy::Ptr)
        }
        _ => {
            return Err(format!(
                "unsupported pointer-wrapper unsize tails: {src_tail:?} -> {dst_tail:?}"
            ));
        }
    };
    ctx.clear_full_place_bindings(place.local);
    ctx.bind_projected_value(place.local, 0, data);
    ctx.bind_projected_value(place.local, 1, meta);
    if let Some(slot) = ctx.memory_slots.get(&place.local).cloned() {
        let address = coerce_to_plain_ptr(ctx, block, slot.ptr);
        emit_typed_store(block, address, TrustIrTy::Ptr, data);
        let address = iter_field_addr(ctx, block, address, 8);
        emit_typed_store(block, address, meta_ty, meta);
    }
    Ok(true)
}

/// Const propagation can replace the coercion with a complete wrapper image.
/// Load its two initialized words from the emitted allocation so real pointer
/// relocations and address-only dangling pointers both retain their meaning.
fn constant_image<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Result<bool, String> {
    let Rvalue::Use(Operand::Constant(constant), _) = rvalue else {
        return Ok(false);
    };
    if !place.projection.is_empty() {
        return Ok(false);
    }
    let dst_ty = ctx.monomorphize_ty(local_rust_ty(ctx, body, place.local));
    if !matches!(dst_ty.kind(), ty::Adt(..))
        || dst_ty != ctx.monomorphize_ty(constant.const_.ty())
        || wide_slice_carrier_layout(ctx.tcx, dst_ty).is_none()
        || !matches!(pointer_pair(ctx.tcx, dst_ty, dst_ty), Some((_, _, true)))
    {
        return Ok(false);
    }
    let Some(slot) = ctx.memory_slots.get(&place.local).cloned() else {
        return Ok(false);
    };
    let mir::Const::Val(ConstValue::Indirect { alloc_id, offset }, _) =
        ctx.eval_const_operand(constant)
    else {
        return Ok(false);
    };
    let Some(GlobalAlloc::Memory(allocation)) = ctx.tcx.try_get_global_alloc(alloc_id) else {
        return Ok(false);
    };
    let allocation = allocation.inner();
    let base = offset.bytes();
    let end = base
        .checked_add(16)
        .ok_or_else(|| "constant pointer-wrapper image offset overflow".to_owned())?;
    if end > allocation.len() as u64
        || !(base..end).all(|i| allocation.init_mask().get(rustc_abi::Size::from_bytes(i)))
    {
        return Err("constant pointer-wrapper image is not fully initialized".to_owned());
    }
    let address = emit_const_alloc_addr(ctx, block, alloc_id, base, TrustIrTy::Ptr)?;
    let data = emit_typed_load(ctx, block, address, TrustIrTy::Ptr);
    let metadata_address = iter_field_addr(ctx, block, address, 8);
    let metadata = emit_typed_load(ctx, block, metadata_address, TrustIrTy::I64);
    store_fat_ptr_slot_into(ctx, block, slot.ptr, data, metadata);
    Ok(true)
}
