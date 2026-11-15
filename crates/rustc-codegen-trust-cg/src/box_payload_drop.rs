//! [TCG-BOX-PAYLOAD-DROP] Dropping a `Box<T>` whose payload has rustc's own
//! drop glue, and a `Box` reached through a projection (ledger L06-P8).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
//!
//! # What rustc does
//!
//! `drop_glue::<Box<T, Global>>` drops the payload in place
//! (`drop_glue::<T>(ptr)`) and then frees the allocation
//! (`<Box<T> as Drop>::drop` -> `__rust_dealloc(ptr, size_of::<T>(),
//! align_of::<T>())`, nothing for a zero-sized `T`). If the payload's glue
//! unwinds, the box's NESTED cleanup frees the allocation and the unwind
//! continues at the `Drop` terminator's own unwind action.
//!
//! # What this lane emits
//!
//! Exactly that: the box pointer is read from the dropped place, rustc's own
//! `drop_glue::<T>` is called on it (an `Invoke` whose synthesized pad frees
//! the box and leaves through the `Drop`'s unwind action, as
//! `lower_box_drop_needs_drop_element` does for its narrower payload class),
//! and the allocation is freed with the same `emit_box_dealloc` every `Box`
//! drop uses. The payload's destruction is not re-derived here; the glue body
//! is compiled by this backend like any other mono item and refuses on its own
//! terms.
//!
//! # When the glue may be handed the box pointer
//!
//! rustc's glue reads the payload at rustc's layout, so the payload bytes must
//! BE that layout. [`payload_is_rustc_image`] admits a payload type only when
//! no part of it is a value the bridge models some other way (an intercepted
//! `Vec`/`String`/map, a dead-internal map type, a union, a trait object, a
//! closure or coroutine), with nested `Box<U, Global>` fields admitted when `U`
//! is (co-inductively, so a recursive list or tree is admitted, whether it
//! links through `Option<Box<Node>>` or through a `Box<Self>` variant field
//! whose drop is a self-call of the glue). Anything else keeps the named
//! refusal.
//!
//! # Which places
//!
//! A bare local (its genuine scalar binding, checked by the caller's
//! double-free gate), `(*p).f…` through a genuinely bound thin pointer
//! (`general_drop_glue_projected_base`, the base rule of
//! `[TCG-DROP-GLUE-GENERAL-FIELD]`; the walk must land on the dropped place's
//! own type), and a field of a memory-backed local (`memory_place_address_raw`).
//! A projected place is a `Box` stored in memory, so its pointer is loaded
//! from that address. That projected shape is what rustc's own glue for an
//! enclosing `Option<Box<T>>`, tuple or struct drops (`drop(((*_1) as
//! Some).0)`), and it was refused for every payload before.
//!
//! # Where
//!
//! Projected boxes with a drop-free payload use the existing allocator shim
//! on Linux AArch64/x86-64 and Darwin AArch64. Payload destructors run on
//! Darwin AArch64 ([`lane_target`]) and, under `panic=abort` only, on x86-64
//! Linux ([`abort_payload_lane`]); nested unwind cleanup retains its Darwin
//! qualification.

use super::*;

/// Targets qualified for payload glue and nested cleanup: AArch64 Darwin.
fn lane_target(tcx: TyCtxt<'_>) -> bool {
    tcx.sess.target.arch.desc() == "aarch64" && tcx.sess.target.is_like_darwin
}

/// Targets qualified for payload glue WITHOUT nested cleanup: x86-64 Linux
/// under `panic=abort`. The payload glue is then a plain `Call` (no glue can
/// unwind, so the box's nested cleanup pad never exists) followed by the same
/// free; the glue body is compiled by this backend and refuses on its own
/// terms. Under `panic=unwind` the nested cleanup is still Darwin-qualified
/// only (x86-64 Linux native EH is not qualified), so that keeps the refusal.
fn abort_payload_lane(tcx: TyCtxt<'_>) -> bool {
    tcx.sess.target.arch.desc() == "x86_64"
        && tcx.sess.target.os == rustc_target::spec::Os::Linux
        && panic_is_abort(tcx)
}

/// Lower `drop(place)` of a `Box<element_ty, Global>` when this lane owns the
/// shape. Returns `Ok(false)` to leave the drop to the caller's existing arms
/// (a bare-local box whose payload needs no drop, or a target/payload outside
/// the qualified lanes), and a named `Err` for a shape it recognizes but cannot
/// lower faithfully.
pub(super) fn lower<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    place: &Place<'tcx>,
    element_ty: Ty<'tcx>,
    target: mir::BasicBlock,
    unwind: &mir::UnwindAction,
) -> Result<bool, String> {
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let payload_needs_drop = element_ty.needs_drop(ctx.tcx, typing_env);
    // A projected box with a drop-free payload needs only its actual stored
    // pointer and the existing target's allocator shim. Payload destructors
    // and their nested unwind cleanup retain the Darwin-only qualification.
    let linux_pointer_lane = matches!(ctx.tcx.sess.target.arch.desc(), "aarch64" | "x86_64")
        && ctx.tcx.sess.target.os == rustc_target::spec::Os::Linux;
    if !lane_target(ctx.tcx)
        && !(linux_pointer_lane && (!payload_needs_drop || abort_payload_lane(ctx.tcx)))
    {
        return Ok(false);
    }
    if place.projection.is_empty() && !payload_needs_drop {
        return Ok(false);
    }
    let glue = if payload_needs_drop {
        if !payload_is_rustc_image(ctx.tcx, element_ty) {
            return Err(format!(
                "[TCG-BOX-PAYLOAD-DROP] Drop of Box<{element_ty:?}>: the payload holds a value \
                 this backend does not keep at rustc's layout (an intercepted collection, a \
                 union, a trait object, a closure or coroutine), so rustc's drop glue cannot \
                 be handed it — failing closed"
            ));
        }
        let drop_instance = Instance::resolve_drop_glue(ctx.tcx, element_ty);
        if !matches!(
            drop_instance.def,
            ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, Some(_)))
        ) {
            return Err(format!(
                "[TCG-BOX-PAYLOAD-DROP] Drop of Box<{element_ty:?}>: the payload's drop glue \
                 resolved to {:?}, not the `Shim(DropGlue(_, Some(_)))` the mono collector \
                 emits — failing closed",
                drop_instance.def
            ));
        }
        if !panic_is_abort(ctx.tcx) && !ctx.eh_active {
            return Err(format!(
                "[TCG-BOX-PAYLOAD-DROP] Drop of Box<{element_ty:?}> under panic=unwind without \
                 EH lowering (disable-unwind) — failing closed rather than skipping the box's \
                 nested cleanup"
            ));
        }
        // A `Box<Self>` field inside `drop_glue::<Self>` (an enum cons list or
        // tree) names this body's own glue: `extern_callee` resolves that
        // self-call to the definition, as for any directly recursive
        // function. The recursion is bounded by the data, as in rustc's glue.
        Some(ctx.extern_callee(drop_instance)?)
    } else {
        None
    };
    let Some(box_ptr) = box_pointer(ctx, body, block, place)? else {
        return Err(format!(
            "[TCG-BOX-PAYLOAD-DROP] Drop of a projected Box<{element_ty:?}> place {:?}: its base \
             is not a genuinely bound thin pointer or a memory-backed local",
            place.projection
        ));
    };
    // User code may replace an image through an escaped mutable alias.
    ctx.bridge_map_images.clear();
    if let Some(glue) = glue {
        if !panic_is_abort(ctx.tcx) {
            let cont_id = ctx.fresh_block_id();
            let pad_id = ctx.fresh_block_id();
            block.body.push(InstrNode::new(Inst::Invoke {
                callee: glue,
                args: vec![box_ptr],
                normal_dest: cont_id,
                normal_args: Vec::new(),
                unwind_dest: pad_id,
            }));
            let finished = std::mem::replace(block, Block::new(cont_id));
            ctx.extra_blocks.push(finished);
            // The box's nested cleanup: the payload counts as dropped, the
            // allocation is freed, and the unwind continues at the `Drop`'s
            // own action.
            let mut pad = Block::new(pad_id);
            let exn = ctx.fresh_value();
            let selector = ctx.fresh_value();
            pad.body.push(
                InstrNode::new(Inst::LandingPad {
                    is_cleanup: true,
                    catch_type_indices: Vec::new(),
                })
                .with_results(vec![exn, selector]),
            );
            let slot = ctx.eh_exn_slot.ok_or_else(|| {
                "[TCG-BOX-PAYLOAD-DROP] box payload-drop pad without an exn slot".to_owned()
            })?;
            emit_exn_slot_store(&mut pad, slot, exn);
            emit_box_dealloc(ctx, &mut pad, box_ptr, element_ty)?;
            emit_elem_cleanup_unwind_exit(ctx, &mut pad, unwind)?;
            ctx.extra_blocks.push(pad);
        } else {
            block.body.push(InstrNode::new(Inst::Call {
                callee: glue,
                args: vec![box_ptr],
            }));
        }
    }
    emit_box_dealloc(ctx, block, box_ptr, element_ty)?;
    block.body.push(InstrNode::new(Inst::Br {
        target: BlockId::new(target.index() as u32),
        args: Vec::new(),
    }));
    Ok(true)
}

/// The dropped box's pointer value, or `None` for a base this lane does not
/// address.
fn box_pointer<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    place: &Place<'tcx>,
) -> Result<Option<ValueId>, String> {
    if place.projection.is_empty() {
        // The caller's double-free gate has established a genuine binding.
        return value_for_runtime_scalar_local(ctx, block, place.local).map(Some);
    }
    let place_ty = place_rust_ty(ctx, body, place);
    let addr = if matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
        let Some((base, pointee_ty)) = general_drop_glue_projected_base(ctx, body, place)? else {
            return Ok(None);
        };
        let (offset, walked_ty) =
            walk_memory_projection_offset_raw(ctx, pointee_ty, place.projection)?;
        if walked_ty != place_ty {
            return Err(format!(
                "[TCG-BOX-PAYLOAD-DROP] the projection walk over {pointee_ty:?} landed on \
                 {walked_ty:?}, not the dropped {place_ty:?} — failing closed"
            ));
        }
        if offset == 0 {
            base
        } else {
            let index = emit_i64_const(ctx, block, i128::from(offset));
            emit_element_addr(ctx, block, base, index, 1)
        }
    } else if local_is_memory_backed(ctx, place.local)
        && slot_dst_ref_walk_pointee(ctx, body, place).is_none()
        && place
            .projection
            .iter()
            .all(|e| matches!(e, ProjectionElem::Field(..) | ProjectionElem::Downcast(..)))
    {
        memory_place_address_raw(ctx, body, block, place)?
    } else {
        return Ok(None);
    };
    Ok(Some(emit_typed_load(ctx, block, addr, TrustIrTy::Ptr)))
}

/// Whether a `drop(place)` of a `Box<element_ty>` reaches this lane's nested
/// cleanup (the payload glue call), so `seed_eh_landing_pads` must activate
/// EH for its body even when the `Drop`'s own unwind action is `Continue`.
/// The bare-local payload classes the older arms own are left out, so their
/// bodies keep their existing EH decision.
pub(super) fn needs_nested_cleanup<'tcx>(
    tcx: TyCtxt<'tcx>,
    place: &Place<'tcx>,
    element_ty: Ty<'tcx>,
) -> bool {
    lane_target(tcx)
        && element_ty.needs_drop(tcx, ty::TypingEnv::fully_monomorphized())
        && payload_is_rustc_image(tcx, element_ty)
        && (!place.projection.is_empty()
            || !(drop_glue_needs_drop_element_lowerable(tcx, element_ty)
                || boxed_payload_drop_recursively_lowerable(tcx, element_ty, 1)
                || boxed_dyn_field_drop_plan(tcx, element_ty).is_some()))
}

/// Whether every byte of a `ty` value is kept at rustc's own layout by this
/// backend, so rustc's `drop_glue::<ty>` may be handed its address.
pub(super) fn payload_is_rustc_image<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let typing_env = ty::TypingEnv::fully_monomorphized();
    if !tcx
        .layout_of(typing_env.as_query_input(ty))
        .is_ok_and(|layout| layout.is_sized())
    {
        return false;
    }
    let mut visiting = Vec::new();
    image(tcx, ty, &mut visiting)
}

fn image<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, visiting: &mut Vec<Ty<'tcx>>) -> bool {
    // A type already being checked is admitted on the assumption being
    // established (a recursive list or tree): every other node still has to
    // pass on its own.
    if visiting.contains(&ty) {
        return true;
    }
    if visiting.len() > 64 {
        return false;
    }
    if vec_element_ty(tcx, ty).is_some()
        || btreemap_kv_ty(tcx, ty).is_some()
        || any_hashmap_kv_ty(tcx, ty).is_some()
        || is_hashmap_dead_internal_ty(tcx, ty)
        || is_string_ty(tcx, ty)
        || is_fmt_internal_ty(tcx, ty)
    {
        return false;
    }
    let typing_env = ty::TypingEnv::fully_monomorphized();
    visiting.push(ty);
    let admitted = if let Some(boxed) = box_element_ty(tcx, ty) {
        image(tcx, boxed, visiting)
    } else {
        match ty.kind() {
            ty::Adt(adt, args) if !adt.is_union() && !adt.is_box() => {
                adt.variants().iter().all(|variant| {
                    variant.fields.iter().all(|field| {
                        let field_ty =
                            tcx.normalize_erasing_regions(typing_env, field.ty(tcx, *args));
                        image(tcx, field_ty, visiting)
                    })
                })
            }
            ty::Tuple(fields) => fields.iter().all(|field| image(tcx, field, visiting)),
            ty::Array(element, _) => image(tcx, *element, visiting),
            ty::Pat(inner, _) => image(tcx, *inner, visiting),
            ty::Int(_)
            | ty::Uint(_)
            | ty::Float(_)
            | ty::Bool
            | ty::Char
            | ty::Never
            | ty::FnPtr(..)
            | ty::FnDef(..) => true,
            // A thin reference or raw pointer is one address word; a wide one
            // carries metadata the bridge may hold in a lane pair, which is
            // rustc's `ScalarPair` too, but nothing pins it here yet.
            ty::Ref(_, pointee, _) | ty::RawPtr(pointee, _) => pointee.is_sized(tcx, typing_env),
            _ => false,
        }
    };
    visiting.pop();
    admitted
}
