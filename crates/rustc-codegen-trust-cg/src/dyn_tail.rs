//! Struct pointers whose metadata is the vtable of an unsized trait-object tail.
//! The data lane addresses the whole struct. Each unsized field projection must
//! round its rustc offset to that field's runtime alignment, including nesting.

use super::*;

/// Return the terminal trait object only for an unsized, unpacked struct chain.
/// Layouts and pointer carriers are checked before admitting the new family.
fn tail<'tcx>(tcx: TyCtxt<'tcx>, mut ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    let env = ty::TypingEnv::fully_monomorphized();
    for _ in 0..32 {
        match ty.kind() {
            ty::Dynamic(..) => return Some(ty),
            ty::Adt(adt, _) if adt.is_struct() && !adt.repr().packed() => {
                let layout = tcx.layout_of(env.as_query_input(ty)).ok()?;
                if layout.is_sized() {
                    return None;
                }
                let index = adt.non_enum_variant().fields.len().checked_sub(1)?;
                ty = layout.field(&LayoutCx(tcx), index).ty;
            }
            _ => return None,
        }
    }
    None
}

pub(super) fn pointee<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    let (ty::Ref(_, inner, _) | ty::RawPtr(inner, _)) = ty.kind() else {
        return None;
    };
    if !matches!(inner.kind(), ty::Adt(..)) {
        return None;
    }
    tail(tcx, *inner)?;
    let layout = tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
        .ok()?;
    (tcx.data_layout.pointer_size().bytes() == 8
        && crate::scalar_pair::view(layout.backend_repr).is_some()
        && layout.size.bytes() == 16
        && layout.align.bytes() == 8
        && fat_ptr_metadata_offset(tcx, ty).ok() == Some(8))
    .then_some(*inner)
}

pub(super) fn metadata_offset<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<u64> {
    pointee(tcx, ty).map(|_| 8)
}

pub(super) fn is_pointer<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    pointee(tcx, ty).is_some()
}

fn round_up(
    ctx: &mut MirLoweringCtx<'_>,
    block: &mut Block,
    size: ValueId,
    align: ValueId,
) -> ValueId {
    let one = emit_i64_const(ctx, block, 1);
    let zero = emit_i64_const(ctx, block, 0);
    let padding = emit_i64_binop(ctx, block, TrustIrBinOp::Sub, align, one);
    let padded = emit_i64_binop(ctx, block, TrustIrBinOp::Add, size, padding);
    let mask = emit_i64_binop(ctx, block, TrustIrBinOp::Sub, zero, align);
    emit_i64_binop(ctx, block, TrustIrBinOp::And, padded, mask)
}

/// The same recursive DST layout law rustc's size_of_val codegen implements:
/// align=max(prefix_align,tail_align); size=round_up(prefix_offset+tail_size,align).
/// The tail size is a multiple of its alignment, so this includes tail padding.
fn size_align<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    block: &mut Block,
    mut ty: Ty<'tcx>,
    vtable: ValueId,
) -> Result<(ValueId, ValueId), String> {
    tail(ctx.tcx, ty).ok_or_else(|| "unsupported dynamic-tail layout".to_owned())?;
    let mut levels = Vec::new();
    while !matches!(ty.kind(), ty::Dynamic(..)) {
        let layout = ctx
            .tcx
            .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
            .map_err(|e| format!("dynamic-tail layout_of: {e:?}"))?;
        let index = layout.fields.count() - 1;
        levels.push((layout.fields.offset(index).bytes(), layout.align.bytes()));
        ty = layout.field(&LayoutCx(ctx.tcx), index).ty;
    }
    let size_addr = iter_field_addr(
        ctx,
        block,
        vtable,
        ty::COMMON_VTABLE_ENTRIES_SIZE as u64 * 8,
    );
    let mut size = emit_typed_load(ctx, block, size_addr, TrustIrTy::I64);
    let align_addr = iter_field_addr(
        ctx,
        block,
        vtable,
        ty::COMMON_VTABLE_ENTRIES_ALIGN as u64 * 8,
    );
    let mut align = emit_typed_load(ctx, block, align_addr, TrustIrTy::I64);
    for (offset, minimum_align) in levels.into_iter().rev() {
        let minimum = emit_i64_const(ctx, block, i128::from(minimum_align));
        let larger = emit_i64_icmp(ctx, block, ICmpOp::Ugt, minimum, align);
        let full_align = ctx.fresh_value();
        block.body.push(
            InstrNode::new(Inst::Select {
                ty: TrustIrTy::I64,
                cond: larger,
                then_val: minimum,
                else_val: align,
            })
            .with_result(full_align),
        );
        let prefix = emit_i64_const(ctx, block, i128::from(offset));
        size = emit_i64_binop(ctx, block, TrustIrBinOp::Add, prefix, size);
        size = round_up(ctx, block, size, full_align);
        align = full_align;
    }
    Ok((size, align))
}

fn bind(
    ctx: &mut MirLoweringCtx<'_>,
    block: &mut Block,
    local: Local,
    data: ValueId,
    vtable: ValueId,
) {
    ctx.clear_full_place_bindings(local);
    ctx.bind_projected_value(local, 0, data);
    ctx.bind_projected_value(local, 1, vtable);
    if let Some(slot) = ctx.memory_slots.get(&local).cloned() {
        emit_typed_store(block, slot.ptr, TrustIrTy::Ptr, data);
        let meta_addr = iter_field_addr(ctx, block, slot.ptr, 8);
        emit_typed_store(block, meta_addr, TrustIrTy::Ptr, vtable);
    }
}

fn check_metadata_layout<'tcx>(ctx: &MirLoweringCtx<'tcx>, ty: Ty<'tcx>) -> Result<(), String> {
    let layout = ctx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
        .map_err(|e| format!("dynamic-tail metadata layout_of: {e:?}"))?;
    if layout.size.bytes() != 8
        || layout.align.bytes() != 8
        || !matches!(layout.backend_repr, rustc_abi::BackendRepr::Scalar(scalar)
            if matches!(scalar.primitive(), rustc_abi::Primitive::Pointer(_)))
    {
        return Err("dynamic-tail metadata is not one pointer-sized scalar".to_owned());
    }
    Ok(())
}

pub(super) fn force_slots<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    locals: &mut HashSet<Local>,
) {
    for local in body.local_decls.indices() {
        if pointee(
            ctx.tcx,
            ctx.monomorphize_ty(local_rust_ty(ctx, body, local)),
        )
        .is_some()
        {
            locals.insert(local);
        }
    }
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            if let StatementKind::Assign(assignment) = &statement.kind {
                let (dst, value) = &**assignment;
                if let Rvalue::UnaryOp(mir::UnOp::PtrMetadata, operand) = value {
                    if dst.projection.is_empty()
                        && pointee(
                            ctx.tcx,
                            ctx.monomorphize_ty(operand.ty(&body.local_decls, ctx.tcx)),
                        )
                        .is_some()
                    {
                        locals.insert(dst.local);
                    }
                }
            }
        }
    }
}

fn projection<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    place: &Place<'tcx>,
) -> Result<Option<(ValueId, ValueId, Ty<'tcx>)>, String> {
    if !matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
        return Ok(None);
    }
    let pointer_ty = ctx.monomorphize_ty(local_rust_ty(ctx, body, place.local));
    let Some(inner) = pointee(ctx.tcx, pointer_ty) else {
        return Ok(None);
    };
    let (mut address, vtable) = dyn_fat_ptr_halves_of_local(ctx, block, place.local)
        .ok_or_else(|| "dynamic-tail projection has no fat-pointer binding".to_owned())?;
    let cx = LayoutCx(ctx.tcx);
    let mut layout = ctx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(inner))
        .map_err(|e| format!("dynamic-tail projection layout_of: {e:?}"))?;
    for elem in place.projection.iter().skip(1) {
        match elem {
            ProjectionElem::Field(field, _) => {
                let offset = layout.fields.offset(field.index()).bytes();
                let child = layout.field(&cx, field.index());
                if offset != 0 {
                    let mut offset = emit_i64_const(ctx, block, i128::from(offset));
                    if !child.is_sized() {
                        let (_, align) = size_align(ctx, block, child.ty, vtable)?;
                        offset = round_up(ctx, block, offset, align);
                    }
                    address = emit_element_addr(ctx, block, address, offset, 1);
                }
                layout = child;
            }
            ProjectionElem::Downcast(_, variant) => layout = layout.for_variant(&cx, variant),
            ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => {
                let (stride, _) = array_element_layout(&cx, &layout)?;
                let index = resolve_index_value(ctx, block, &elem)?;
                address = emit_element_addr(ctx, block, address, index, stride);
                layout = layout.field(&cx, 0);
            }
            other => return Err(format!("dynamic-tail projection {other:?} unsupported")),
        }
    }
    Ok(Some((address, vtable, layout.ty)))
}

pub(super) fn read<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    place: &Place<'tcx>,
) -> Result<Option<ValueId>, String> {
    let Some((address, _, leaf)) = projection(ctx, body, block, place)? else {
        return Ok(None);
    };
    let leaf = memory_scalar_leaf_ty(ctx.tcx, leaf)?;
    Ok(Some(emit_typed_load(ctx, block, address, leaf)))
}

pub(super) fn assign<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Result<bool, String> {
    if place.projection.is_empty() {
        if let Rvalue::UnaryOp(mir::UnOp::PtrMetadata, operand) = rvalue {
            let src = ctx.monomorphize_ty(operand.ty(&body.local_decls, ctx.tcx));
            if pointee(ctx.tcx, src).is_some() {
                check_metadata_layout(
                    ctx,
                    ctx.monomorphize_ty(local_rust_ty(ctx, body, place.local)),
                )?;
                let (_, vtable) = read_trait_object_fat_ptr(ctx, block, operand)?;
                let slot = memory_slot_ptr(ctx, place.local)?;
                ctx.clear_full_place_bindings(place.local);
                emit_typed_store(block, slot, TrustIrTy::Ptr, vtable);
                return Ok(true);
            }
        }
        if let Rvalue::Aggregate(kind, operands) = rvalue {
            let dst_ty = ctx.monomorphize_ty(local_rust_ty(ctx, body, place.local));
            if matches!(&**kind, mir::AggregateKind::RawPtr(..))
                && pointee(ctx.tcx, dst_ty).is_some()
            {
                if operands.len() != 2 {
                    return Err("dynamic-tail from-parts arity".to_owned());
                }
                let data = lower_operand_to_value(ctx, body, block, &operands[FieldIdx::new(0)])?;
                let data = coerce_to_plain_ptr(ctx, block, data);
                let meta = &operands[FieldIdx::new(1)];
                check_metadata_layout(
                    ctx,
                    ctx.monomorphize_ty(meta.ty(&body.local_decls, ctx.tcx)),
                )?;
                let vtable = match meta {
                    Operand::Copy(src) | Operand::Move(src)
                        if local_is_memory_backed(ctx, src.local) =>
                    {
                        let address = memory_place_address_raw(ctx, body, block, src)?;
                        emit_typed_load(ctx, block, address, TrustIrTy::Ptr)
                    }
                    _ => {
                        let value = lower_operand_to_value(ctx, body, block, meta)?;
                        coerce_to_plain_ptr(ctx, block, value)
                    }
                };
                bind(ctx, block, place.local, data, vtable);
                return Ok(true);
            }
        }
    }
    if let Some((address, _, leaf)) = projection(ctx, body, block, place)? {
        let pointer_ty = ctx.monomorphize_ty(local_rust_ty(ctx, body, place.local));
        if matches!(pointer_ty.kind(), ty::Ref(_, _, rustc_hir::Mutability::Not)) {
            return Err("dynamic-tail store through shared reference".to_owned());
        }
        let leaf = memory_scalar_leaf_ty(ctx.tcx, leaf)?;
        let value = ctx.fresh_value();
        lower_scalar_memory_store_value(ctx, body, block, rvalue, leaf.clone(), value)?;
        emit_typed_store(block, address, leaf, value);
        return Ok(true);
    }
    let (Rvalue::Ref(_, _, source) | Rvalue::RawPtr(_, source)) = rvalue else {
        return Ok(false);
    };
    let Some((address, vtable, leaf)) = projection(ctx, body, block, source)? else {
        return Ok(false);
    };
    if !place.projection.is_empty() {
        return Err("dynamic-tail borrow into projected destination".to_owned());
    }
    if !leaf.is_sized(ctx.tcx, ty::TypingEnv::fully_monomorphized()) {
        tail(ctx.tcx, leaf).ok_or_else(|| "dynamic-tail borrow metadata unsupported".to_owned())?;
        bind(ctx, block, place.local, address, vtable);
    } else {
        let ty = local_trust_ir_ty(ctx, body, place.local)?;
        if !is_pointer_like_trust_ir_ty(&ty) {
            return Err("dynamic-tail sized field borrow is not a thin pointer".to_owned());
        }
        let value = ctx.fresh_value();
        block.body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: TrustIrTy::Ptr,
                dst_ty: ty,
                operand: address,
            })
            .with_result(value),
        );
        ctx.clear_full_place_bindings(place.local);
        ctx.bind_scalar_value(place.local, value);
    }
    Ok(true)
}

pub(super) fn unsize<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    place: &Place<'tcx>,
    operand: &Operand<'tcx>,
    dst_ty: Ty<'tcx>,
) -> Result<bool, String> {
    let Some(dst) = pointee(ctx.tcx, dst_ty) else {
        return Ok(false);
    };
    if !place.projection.is_empty() {
        return Err("dynamic-tail unsize into projected destination".to_owned());
    }
    let source_ty = ctx.monomorphize_ty(operand.ty(&body.local_decls, ctx.tcx));
    let (ty::Ref(_, src, _) | ty::RawPtr(src, _)) = source_ty.kind() else {
        return Err("dynamic-tail unsize source is not a pointer".to_owned());
    };
    let (src_tail, dst_tail) =
        ctx.tcx
            .struct_lockstep_tails_for_codegen(*src, dst, ty::TypingEnv::fully_monomorphized());
    let ty::Dynamic(dst_traits, _) = dst_tail.kind() else {
        return Err("dynamic-tail unsize destination has no trait metadata".to_owned());
    };
    let (data, vtable) = if let ty::Dynamic(src_traits, _) = src_tail.kind() {
        let (data, mut vtable) = read_trait_object_fat_ptr(ctx, block, operand)?;
        if src_traits.principal_def_id() != dst_traits.principal_def_id()
            && dst_traits.principal_def_id().is_some()
        {
            if let Some(index) = ctx.tcx.supertrait_vtable_slot((src_tail, dst_tail)) {
                let offset = u64::try_from(index)
                    .ok()
                    .and_then(|n| n.checked_mul(8))
                    .ok_or_else(|| "dynamic-tail upcast offset overflow".to_owned())?;
                let address = iter_field_addr(ctx, block, vtable, offset);
                vtable = emit_typed_load(ctx, block, address, TrustIrTy::Ptr);
            }
        }
        (data, vtable)
    } else {
        let data = slice_unsize_source_data_ptr(ctx, body, block, operand)?
            .ok_or_else(|| "dynamic-tail unsize source has no stable address".to_owned())?;
        let principal = dst_traits
            .principal()
            .map(|p| ctx.tcx.instantiate_bound_regions_with_erased(p))
            .ok_or_else(|| "dynamic-tail unsize has no principal trait".to_owned())?;
        let trait_ref = principal.with_self_ty(ctx.tcx, src_tail);
        let origin = heap_image_glue::VtableDropOrigin::Other;
        let vtable = emit_vtable_ptr_value(ctx, block, src_tail, trait_ref, origin)?;
        (coerce_to_plain_ptr(ctx, block, data), vtable)
    };
    bind(ctx, block, place.local, data, vtable);
    Ok(true)
}

pub(super) fn intrinsic<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    call: &DirectCallTerminator<'_, 'tcx>,
    callee: Instance<'tcx>,
    name: &str,
) -> Result<bool, String> {
    if !matches!(name, "size_of_val" | "align_of_val") {
        return Ok(false);
    }
    let ty = ctx.monomorphize_ty(callee.args.type_at(0));
    if !matches!(ty.kind(), ty::Adt(..)) || tail(ctx.tcx, ty).is_none() {
        return Ok(false);
    }
    if call.args.len() != 1 {
        return Err("dynamic-tail layout intrinsic arity".to_owned());
    }
    let (_, vtable) = read_trait_object_fat_ptr(ctx, block, &call.args[0].node)?;
    let (size, align) = size_align(ctx, block, ty, vtable)?;
    let result = if name == "size_of_val" { size } else { align };
    lower_elided_scalar_return_call(ctx, body, block, call.destination, call.target, result)?;
    Ok(true)
}

/// Refuse a projection `Field` step that lands on an UNSIZED field whose tail is a
/// trait object at a NON-ZERO static offset.
///
/// rustc's layout gives such a field the offset it would have at alignment 1, but
/// its real offset is rounded up to the trait object's alignment, read from the
/// vtable at run time (`rustc_codegen_ssa`'s `project_field` computes it
/// dynamically in exactly this case: an unsized field that is not `[T]` / `str` /
/// an extern type, at a non-zero offset). A `dyn`-tailed pointer only reaches the
/// projection walkers once `classify_func_ty` admits it as a parameter, and no
/// walker models the vtable read, so every walker calls this after each `Field`
/// step: a sized header field keeps its exact static offset, an offset-0 step keeps
/// its (trivially aligned) address, and a step into the tail itself is refused
/// rather than addressed at a guessed offset. Slice / `str` tails are untouched —
/// their alignment is static, so their static offset is exact.
pub(super) fn refuse_dynamic_offset_field<'tcx>(
    tcx: TyCtxt<'tcx>,
    field: &rustc_middle::ty::layout::TyAndLayout<'tcx>,
    offset: u64,
) -> Result<(), String> {
    if field.is_sized() || offset == 0 {
        return Ok(());
    }
    let mut current = *field;
    for _ in 0..32 {
        match current.ty.kind() {
            ty::Dynamic(..) => {
                return Err(format!(
                    "[TCG-POINTEE-UNSIZED-TAIL] projection into the unsized field `{:?}` at \
                     static offset {offset}: its tail is a trait object, so its real offset is \
                     rounded up to the vtable's alignment at run time and the static layout \
                     offset would address the wrong bytes. Failing closed rather than \
                     projecting at a guessed offset. Options: read the sized header fields \
                     only, pass the trait object separately as a `&dyn Trait`, or use the \
                     LLVM backend for this function.",
                    field.ty
                ));
            }
            ty::Adt(adt, _) if adt.is_struct() && !current.is_sized() => {
                let Some(index) = adt.non_enum_variant().fields.len().checked_sub(1) else {
                    return Ok(());
                };
                current = current.field(&LayoutCx(tcx), index);
            }
            _ => return Ok(()),
        }
    }
    Ok(())
}
