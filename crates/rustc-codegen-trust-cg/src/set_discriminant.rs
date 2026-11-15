//! `StatementKind::SetDiscriminant` for every enum layout rustc gives a place
//! the bridge can address (ledger L06-P8).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
//!
//! # The semantics this mirrors
//!
//! `rustc_codegen_ssa`'s `PlaceRef::codegen_set_discr` is the reference:
//!
//! * `Variants::Single { index }`: there is no tag; the statement names the one
//!   variant (rustc asserts `index == variant_index`) and writes nothing;
//! * `TagEncoding::Direct`: the variant's discriminant, truncated to the tag
//!   width, is stored at the tag offset;
//! * `TagEncoding::Niche`: the untagged variant writes nothing (its payload is
//!   the niche field's valid value); every other variant stores
//!   `niche_start + (variant - niche_variants.start)` at the niche offset.
//!
//! The tag store is the one the construction and `Rvalue::Discriminant` paths
//! already use (`store_memory_enum_tag_at_base` / `store_memory_niche_tag`,
//! over `memory_aggregate_layout`, whose offsets and encodings come from
//! rustc's `layout_of`), so a write here and a later read cannot disagree.
//!
//! # Which places
//!
//! The two shapes `lower_set_discriminant` always admitted (`(*r)` and a bare
//! memory-backed local) plus any PROJECTED place whose address the memory
//! model already resolves for a `&raw` borrow of the same place:
//!
//! * `(*r).f…` through a thin pointer `r` to a sized pointee: the address is
//!   `r`'s value plus the Field/Downcast/Index walk over the pointee's layout
//!   (`walk_memory_projection_runtime_place_address`), under the same base
//!   admission the through-reference `Rvalue::RawPtr` arm asks
//!   (`wide_deref_base_value_is_not_pointee_addr`, a bound or entry-argument
//!   base);
//! * `l.f…` of a memory-backed local `l`: `memory_place_address_raw`, the
//!   walker every field read and write of that slot uses.
//!
//! A tagged place reached any other way (a scalarized local, a fat or
//! slot-backed DST base, an unbound pointer) is refused by name, as before.
//!
//! # Fieldless enums
//!
//! A C-like enum (every variant without fields, so its whole value is a Direct
//! tag) has no aggregate memory layout here: the memory model keeps it as a
//! scalar leaf. Its tag is read straight from rustc's layout
//! ([`fieldless_enum_tag`]), and through `(*r)` or a projected place it is
//! stored at the place's address like any other Direct tag. A bare fieldless
//! local keeps the legacy refusal.
//!
//! # The read at a runtime index
//!
//! `Rvalue::Discriminant` of `(*r)…[i]…` (an enum reached through a pointer
//! and a runtime array index) was refused ("Rvalue::Discriminant projected
//! source"): `lower_reference_deref_discriminant` folds only static offsets.
//! [`lower_indexed_read`] resolves the same address the write above does and
//! decodes the tag with `emit_tag_discriminant_from_base`, the decoder every
//! memory and through-reference read uses.

use super::*;

/// Lower `SetDiscriminant(place, variant_index)` for a PROJECTED place or a
/// single-variant layout. Returns `Ok(false)` when `place` is one of the two
/// original shapes (`(*r)`, a bare memory-backed local) with a tagged layout,
/// which the caller keeps lowering, and an `Err` naming the shape for every
/// projected place it cannot address.
pub(super) fn lower_general<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    place: &Place<'tcx>,
    variant_index: VariantIdx,
) -> Result<bool, String> {
    let place_ty = place_rust_ty(ctx, body, place);
    let layout = ctx
        .tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(place_ty))
        .map_err(|e| format!("SetDiscriminant layout_of {place_ty:?} failed: {e:?}"))?;
    if let rustc_abi::Variants::Single { index } = layout.variants {
        // `codegen_set_discr` asserts the named variant is the layout's one
        // variant and stores nothing; a mismatch is invalid MIR.
        if index != variant_index {
            return Err(format!(
                "SetDiscriminant to variant {variant_index:?} of {place_ty:?}, whose layout has \
                 the single variant {index:?}"
            ));
        }
        return Ok(true);
    }
    let fieldless = fieldless_enum_tag(ctx.tcx, place_ty)?;
    let through_ref = matches!(place.projection.as_ref(), [ProjectionElem::Deref]);
    let original_shape = (through_ref && fieldless.is_none())
        || (place.projection.is_empty() && local_is_memory_backed(ctx, place.local));
    if original_shape || place.projection.is_empty() {
        return Ok(false);
    }

    let tag = match fieldless {
        Some(tag) => tag,
        None => tagged_layout(ctx.tcx, place_ty)?,
    };
    let discriminant = match &tag.encoding {
        MemoryTagEncoding::Direct => Some(enumlike_discriminant_value(
            ctx.tcx,
            place_ty,
            variant_index,
        )?),
        MemoryTagEncoding::Niche { .. } => None,
    };
    let addr = projected_place_address(ctx, body, block, place, "SetDiscriminant")?;
    match discriminant {
        Some(discriminant) => store_memory_enum_tag_at_base(ctx, block, addr, &tag, discriminant),
        None => store_memory_niche_tag(ctx, block, addr, &tag, variant_index)?,
    }
    if place.projection.first() != Some(&ProjectionElem::Deref) {
        // The slot is the source of truth; nothing cached about the local's
        // variant or payload may survive a tag (or niche) write into it.
        ctx.clear_projected_values(place.local);
        ctx.clear_adt_discriminant(place.local);
    }
    Ok(true)
}

/// Lower `place = Discriminant(source)` for a `source` reached through a thin
/// pointer and at least one runtime index (`(*r)[i]`, `(*r).f[i].g`). Returns
/// `Ok(false)` for every other source, which the caller keeps refusing.
pub(super) fn lower_indexed_read<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    place: &Place<'tcx>,
    source: &Place<'tcx>,
) -> Result<bool, String> {
    let Some((ProjectionElem::Deref, rest)) = source.projection.as_ref().split_first() else {
        return Ok(false);
    };
    if !rest
        .iter()
        .any(|elem| matches!(elem, ProjectionElem::Index(_)))
    {
        return Ok(false);
    }
    let source_ty = place_rust_ty(ctx, body, source);
    let tag = match fieldless_enum_tag(ctx.tcx, source_ty)? {
        Some(tag) => tag,
        None => match memory_aggregate_layout(ctx.tcx, source_ty)?.and_then(|layout| layout.tag) {
            Some(tag) => tag,
            None => return Ok(false),
        },
    };
    let result_ty = place_trust_ir_ty(ctx, body, place)?;
    if !result_ty.is_integer() {
        return Err(format!(
            "Rvalue::Discriminant non-integer result {result_ty:?}"
        ));
    }
    let addr = projected_place_address(ctx, body, block, source, "Rvalue::Discriminant")?;
    let value = emit_tag_discriminant_from_base(ctx, block, addr, &tag, &result_ty)?;
    let target = prepare_assign_target(ctx, place)?;
    block.body.push(
        InstrNode::new(Inst::Copy {
            ty: result_ty,
            operand: value,
        })
        .with_result(target.value),
    );
    finish_assign_target(ctx, body, block, place, target)?;
    Ok(true)
}

/// The Direct tag of a multi-variant enum `ty` none of whose variants has a
/// field, whose value is exactly the tag (offset and width from rustc's
/// `layout_of`), or `None` for every other type.
fn fieldless_enum_tag<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
) -> Result<Option<MemoryEnumTag>, String> {
    let ty::Adt(adt, _) = ty.kind() else {
        return Ok(None);
    };
    if !adt.is_enum()
        || adt
            .variants()
            .iter()
            .any(|variant| !variant.fields.is_empty())
    {
        return Ok(None);
    }
    let layout = tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
        .map_err(|e| format!("SetDiscriminant layout_of {ty:?} failed: {e:?}"))?;
    let rustc_abi::Variants::Multiple {
        tag,
        tag_encoding: rustc_abi::TagEncoding::Direct,
        tag_field,
        ..
    } = &layout.variants
    else {
        return Ok(None);
    };
    if tag.size(&tcx) != layout.size {
        return Ok(None);
    }
    Ok(Some(MemoryEnumTag {
        offset: layout.fields.offset(tag_field.index()).bytes(),
        ty: scalar_primitive_trust_ir_ty(tcx, tag)?,
        encoding: MemoryTagEncoding::Direct,
    }))
}

/// The tag of a multi-variant enum or coroutine `ty`, from the same layout the
/// construction and discriminant-read paths use.
fn tagged_layout<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Result<MemoryEnumTag, String> {
    let layout = match memory_aggregate_layout(tcx, ty)? {
        Some(layout) => layout,
        None => coroutine_memory_layout(tcx, ty)?.ok_or_else(|| {
            format!("SetDiscriminant on {ty:?}, which has no modeled memory layout")
        })?,
    };
    layout
        .tag
        .ok_or_else(|| format!("SetDiscriminant on {ty:?}: its memory layout carries no tag"))
}

/// The byte address of a projected `place`, by the rule the `&raw` borrow of
/// the same place uses; `what` names the statement in a refusal.
fn projected_place_address<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    place: &Place<'tcx>,
    what: &str,
) -> Result<ValueId, String> {
    if place.projection.first() == Some(&ProjectionElem::Deref) {
        let base_ty = ctx.monomorphize_ty(local_rust_ty(ctx, body, place.local));
        let pointee = match base_ty.kind() {
            ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => ctx.monomorphize_ty(*inner),
            _ => {
                return Err(format!(
                    "{what} through a non-pointer base {base_ty:?} (projection {:?})",
                    place.projection
                ));
            }
        };
        if !pointee.is_sized(ctx.tcx, ty::TypingEnv::fully_monomorphized())
            || wide_deref_base_value_is_not_pointee_addr(ctx.tcx, base_ty)
        {
            return Err(format!(
                "{what} through {base_ty:?}, whose value is not the pointee's address \
                 (projection {:?})",
                place.projection
            ));
        }
        if ctx.memory_slots.contains_key(&place.local)
            || !(ctx.scalar_values.contains_key(&place.local)
                || ctx.scalar_cells.contains_key(&place.local)
                || is_entry_arg(body, place.local))
        {
            return Err(format!(
                "{what} through {base_ty:?} before its pointer value is bound \
                 (projection {:?})",
                place.projection
            ));
        }
        let base = value_for_runtime_scalar_local(ctx, block, place.local)?;
        let (addr, _leaf) = walk_memory_projection_runtime_place_address(
            ctx,
            block,
            base,
            pointee,
            &place.projection[1..],
        )?;
        return Ok(addr);
    }
    if !local_is_memory_backed(ctx, place.local) {
        return Err(format!(
            "{what} on a projection {:?} of a local that has no memory slot",
            place.projection
        ));
    }
    if slot_dst_ref_walk_pointee(ctx, body, place).is_some() {
        return Err(format!(
            "{what} through a slot-backed DST reference (projection {:?})",
            place.projection
        ));
    }
    memory_place_address_raw(ctx, body, block, place)
}
