//! Pointers to structs with slice/str tails. The data lane addresses the whole
//! struct; its length metadata counts tail elements, excluding the sized prefix.

use super::*;

pub(super) struct TailLayout<'tcx> {
    pub offset: u64,
    pub align: u64,
    pub tail: Ty<'tcx>,
}

pub(super) fn layout<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<TailLayout<'tcx>> {
    if !matches!(ty.kind(), ty::Adt(adt, _) if adt.is_struct()) {
        return None;
    }
    let env = ty::TypingEnv::fully_monomorphized();
    let top = tcx.layout_of(env.as_query_input(ty)).ok()?;
    if top.is_sized() {
        return None;
    }
    let mut current = top;
    let mut offset = 0u64;
    for _ in 0..32 {
        match current.ty.kind() {
            ty::Slice(_) | ty::Str => {
                return Some(TailLayout {
                    offset,
                    align: top.align.abi.bytes(),
                    tail: current.ty,
                });
            }
            ty::Adt(adt, _) if adt.is_struct() && !current.is_sized() => {
                let index = adt.non_enum_variant().fields.len().checked_sub(1)?;
                offset = offset.checked_add(current.fields.offset(index).bytes())?;
                current = current.field(&LayoutCx(tcx), index);
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
    layout(tcx, *inner)?;
    let pointer = tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
        .ok()?;
    (matches!(pointer.backend_repr, rustc_abi::BackendRepr::ScalarPair(..))
        && pointer.size.bytes() == 16
        && pointer.align.abi.bytes() == 8
        && fat_ptr_metadata_offset(tcx, ty).ok() == Some(8))
    .then_some(*inner)
}

pub(super) fn is_pointer(ty: Ty<'_>) -> bool {
    rustc_middle::ty::tls::with_opt(|tcx| {
        tcx.is_some_and(|tcx| pointee(tcx, tcx.lift(ty)).is_some())
    })
}

fn projection<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    place: &Place<'tcx>,
) -> Result<Option<(ValueId, Ty<'tcx>)>, String> {
    if !matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
        return Ok(None);
    }
    let pointer_ty = ctx.monomorphize_ty(local_rust_ty(ctx, body, place.local));
    let Some(inner) = pointee(ctx.tcx, pointer_ty) else {
        return Ok(None);
    };
    let data = load_fat_ptr_data(ctx, block, place.local)?;
    // Optimized MIR can fold a slice borrow into `(*r).tail[-k]`. This
    // pointer's metadata is the tail's actual element count; `min_length`
    // records only the pattern's minimum and cannot locate its last element.
    // Require the checked tail-element shape so an index into a sized prefix
    // or another projection cannot accidentally consume the tail's length.
    if ctx.tcx.sess.target.arch.desc() == "aarch64"
        && ctx.tcx.sess.target.os == rustc_target::spec::Os::Linux
        && let Some(ProjectionElem::ConstantIndex {
            offset,
            from_end: true,
            ..
        }) = place.projection.last()
        && is_slice_tail_dst_element_place(ctx, body, place)
    {
        let (_, element, tail_offset) = slice_tail_dst_ref_pointee(ctx.tcx, pointer_ty)
            .expect("tail-element predicate checked the pointer and pointee layout");
        let len = load_fat_ptr_meta(ctx, block, place.local)?;
        let distance = emit_i64_const(ctx, block, i128::from(*offset));
        let index = ctx.fresh_value();
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: TrustIrBinOp::Sub,
                ty: TrustIrTy::I64,
                lhs: len,
                rhs: distance,
            })
            .with_result(index),
        );
        let tail = iter_field_addr(ctx, block, data, tail_offset);
        let stride = layout_size_of(ctx, element)?;
        return Ok(Some((
            emit_element_addr(ctx, block, tail, index, stride),
            element,
        )));
    }
    // Every prefix/tail field uses its actual rustc byte offset. Indexing then
    // adds the element stride; unsupported projections remain explicit errors.
    walk_memory_projection_runtime_place_address(ctx, block, data, inner, &place.projection)
        .map(Some)
}

pub(super) fn read<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    place: &Place<'tcx>,
) -> Result<Option<ValueId>, String> {
    let Some((address, leaf)) = projection(ctx, body, block, place)? else {
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
    if let Some((address, leaf)) = projection(ctx, body, block, place)? {
        let pointer_ty = ctx.monomorphize_ty(local_rust_ty(ctx, body, place.local));
        if matches!(pointer_ty.kind(), ty::Ref(_, _, rustc_hir::Mutability::Not)) {
            return Err("slice-tail struct store through a shared reference".to_owned());
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
    let source_ty = ctx.monomorphize_ty(local_rust_ty(ctx, body, source.local));
    if pointee(ctx.tcx, source_ty).is_none() {
        return Ok(false);
    }
    let Some((address, leaf)) = projection(ctx, body, block, source)? else {
        return Ok(false);
    };
    if !place.projection.is_empty() {
        return Err("slice-tail struct borrow into a projected destination".to_owned());
    }
    if !leaf.is_sized(ctx.tcx, ty::TypingEnv::fully_monomorphized()) {
        if !matches!(leaf.kind(), ty::Slice(_) | ty::Str) && layout(ctx.tcx, leaf).is_none() {
            return Err("slice-tail struct borrow has unsupported metadata".to_owned());
        }
        let meta = load_fat_ptr_meta(ctx, block, source.local)?;
        store_fat_ptr_slot(ctx, block, place.local, address, meta)?;
    } else {
        let ty = local_trust_ir_ty(ctx, body, place.local)?;
        if !is_pointer_like_trust_ir_ty(&ty) {
            return Err("slice-tail field borrow destination is not a thin pointer".to_owned());
        }
        let value = ctx.fresh_value();
        block.body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: TrustIrTy::Ptr,
                dst_ty: ty.clone(),
                operand: address,
            })
            .with_result(value),
        );
        // A destination whose address is taken (`&r` passed to a call or put in
        // an aggregate) is a SCALAR CELL, and every read of it loads the cell.
        // This arm runs before `lower_assign`'s whole-local cell store, so it
        // must store into the cell itself: an SSA-only binding would leave the
        // cell uninitialized.
        if let Some(cell) = ctx.scalar_cells.get(&place.local).cloned() {
            if cell.allocated_ty != ty {
                return Err(format!(
                    "slice-tail field borrow into a scalar cell of type {:?}, not the \
                     destination's {ty:?}",
                    cell.allocated_ty
                ));
            }
            emit_typed_store(block, cell.ptr, ty, value);
        } else if local_is_memory_backed(ctx, place.local) {
            return Err("slice-tail field borrow into a memory-backed destination".to_owned());
        } else {
            ctx.clear_full_place_bindings(place.local);
            ctx.bind_scalar_value(place.local, value);
        }
    }
    Ok(true)
}

pub(super) fn force_slots<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    locals: &mut HashSet<Local>,
) {
    for local in body.local_decls.indices() {
        if is_pointer(ctx.monomorphize_ty(local_rust_ty(ctx, body, local))) {
            locals.insert(local);
        }
    }
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assignment) = &statement.kind else {
                continue;
            };
            let (dest, value) = &**assignment;
            let (Rvalue::Ref(_, _, source) | Rvalue::RawPtr(_, source)) = value else {
                continue;
            };
            if dest.projection.is_empty()
                && is_pointer(ctx.monomorphize_ty(local_rust_ty(ctx, body, source.local)))
                && is_slice_reference_ty(ctx.monomorphize_ty(local_rust_ty(ctx, body, dest.local)))
            {
                locals.insert(dest.local);
            }
        }
    }
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
    let source_ty = ctx.monomorphize_ty(operand.ty(&body.local_decls, ctx.tcx));
    let (ty::Ref(_, src, _) | ty::RawPtr(src, _)) = source_ty.kind() else {
        return Err("slice-tail unsize source is not a pointer".to_owned());
    };
    let (src_tail, dst_tail) =
        ctx.tcx
            .struct_lockstep_tails_for_codegen(*src, dst, ty::TypingEnv::fully_monomorphized());
    let (ty::Array(src_element, len), ty::Slice(dst_element)) = (src_tail.kind(), dst_tail.kind())
    else {
        return Err("slice-tail unsize requires matching array-to-slice tails".to_owned());
    };
    if src_element != dst_element {
        return Err("slice-tail unsize element types differ".to_owned());
    }
    let len = len
        .try_to_target_usize(ctx.tcx)
        .ok_or_else(|| "slice-tail array length is not concrete".to_owned())?;
    let data = slice_unsize_source_data_ptr(ctx, body, block, operand)?
        .ok_or_else(|| "slice-tail unsize has no source address".to_owned())?;
    let data = coerce_to_plain_ptr(ctx, block, data);
    let meta = emit_i64_const(ctx, block, i128::from(len));
    store_fat_ptr_slot(ctx, block, place.local, data, meta)?;
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
    let Some(info) = layout(ctx.tcx, ty) else {
        return Ok(false);
    };
    if call.args.len() != 1 {
        return Err("slice-tail layout intrinsic argument count".to_owned());
    }
    let result = if name == "align_of_val" {
        emit_i64_const(ctx, block, i128::from(info.align))
    } else {
        let (_, len) = resolve_slice_source_data_len(ctx, body, block, &call.args[0].node)?;
        let element = match info.tail.kind() {
            ty::Slice(element) => *element,
            ty::Str => ctx.tcx.types.u8,
            other => {
                return Err(format!(
                    "slice-tail layout intrinsic: tail {other:?} is neither a slice nor str"
                ));
            }
        };
        let (stride, _) = element_layout_size_align(ctx.tcx, element)?;
        let stride = emit_i64_const(ctx, block, i128::from(stride));
        let bytes = emit_i64_binop(ctx, block, TrustIrBinOp::Mul, len, stride);
        let prefix = emit_i64_const(ctx, block, i128::from(info.offset));
        let bytes = emit_i64_binop(ctx, block, TrustIrBinOp::Add, bytes, prefix);
        let padding = emit_i64_const(ctx, block, i128::from(info.align - 1));
        let padded = emit_i64_binop(ctx, block, TrustIrBinOp::Add, bytes, padding);
        let mask = emit_i64_const(ctx, block, -i128::from(info.align));
        emit_i64_binop(ctx, block, TrustIrBinOp::And, padded, mask)
    };
    lower_elided_scalar_return_call(ctx, body, block, call.destination, call.target, result)?;
    Ok(true)
}
