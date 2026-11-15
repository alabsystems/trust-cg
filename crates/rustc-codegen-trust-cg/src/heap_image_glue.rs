//! [TCG-HEAP-IMAGE-GLUE] The drop glue a `dyn` vtable's drop slot names for an
//! intercepted heap value, lowered for real.
//!
//! # The capability this recovers
//!
//! A `Box<dyn Trait>` whose concrete type is an intercepted heap value (a `Box`
//! chain such as `Box<Box<u32>>` or `Box<Vec<u8>>`, a `BTreeMap`, a `Vec<u8>`,
//! a `String`, ...) is dropped by `drop_in_place::<dyn Trait>`, which calls the
//! vtable's drop slot: `drop_glue::<C>`. No bridge interception sees that call
//! (it is indirect), so the slot needs a real body. rustc's own body for it
//! reads `C` at rustc's layout (`<BTreeMap<..> as Drop>::drop`, a projected
//! `Box` place), which is not how the bridge represents `C`, so it never
//! lowered: it refused ("`BTreeMap::<u64, u64>::drop` is not an intercepted
//! BTreeMap method" / "Drop of a projected Box place"). It used to be replaced
//! by a trapping stub (SIGTRAP at the drop); since 0e8241693 an executable
//! refuses it at compile time instead, and a library crate type still gets the
//! stub. (A top-level `Vec` / `String` with `Global` and no-drop elements is
//! the exception: `normalize_real_collection_drop_glue` already lowers its glue
//! to the same `drop((*_1))`, and this module's body for it is that one too.)
//! A chain that holds a `HashMap` is not admitted (`holds_hashmap`).
//!
//! # What the body is
//!
//! `drop_glue::<C>` means `drop((*_1))`: destroy the `C` its `&mut C` argument
//! points at. That is literally rustc's own definition of the glue (the drop
//! shim's pre-elaboration form), so the body this module gives the instance is
//! exactly that one terminator, and `lower_drop` lowers it with
//! `emit_recursive_payload_drop` — the SAME emission the bridge already uses for a
//! direct `drop(Box<C>)` (`lower_box_drop_recursive`), admitted by the SAME
//! predicate (`boxed_payload_drop_recursively_lowerable`). There is one
//! destruction model for a boxed `C`, not two.
//!
//! # Representation origin
//!
//! Pure Box chains ending in a scalar, Vec or String retain rustc's payload
//! layout. Vec/String destruction reads the real inline header and frees its
//! buffer; the caller owns and frees the header storage.
//!
//! A slot-modeled map instead uses a forwarding cell naming a separate
//! 24-byte heap slot. The drop body frees its buffer and that slot, so every
//! Box chain containing such a map needs an actual construction receipt.
//! `Box<Map>` by itself proves neither layout nor origin: a value from LLVM
//! contains the real rustc map representation instead.
//!
//! Owning unsize admits only fresh SSA images constructed locally by the
//! intercepted map and Box producers. Exact copies preserve that receipt;
//! incoming values, memory loads, new joins and values surviving a real call
//! have no representation guarantee. Nonowning unsizes and direct references
//! to map-bearing glue refuse. Pure Box/Vec/String routes keep their independent
//! layout admission. These conservative boundaries are compile-time checks,
//! not formal proof credit.

use super::*;

/// Where an emitted vtable's data pointer comes from, as far as its drop slot
/// is concerned.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum VtableDropOrigin {
    /// `Box<C> -> Box<dyn Trait>`: the data pointer is the box's own cell, built
    /// by `lower_box_new_call` (a heap image for a slot-modeled map `C`).
    OwnedBox,
    /// Every other unsizing: `&C`, `&mut C`, `*const C`, `*mut C`, a struct whose
    /// tail is `C`, a pointer-wrapper ADT (`Rc<C>`, `Arc<C>`, a user `Box`).
    Other,
}

/// Whether a Box chain eventually contains a slot-modeled map. Every link
/// then depends on the map's construction origin, unlike real Vec/String
/// headers. Excessive recursion has no admissible representation receipt.
pub(super) fn contains_slot_map<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let mut current = ty;
    for _ in 0..=16 {
        if btreemap_kv_ty(tcx, current).is_some() || any_hashmap_kv_ty(tcx, current).is_some() {
            return true;
        }
        let Some(element) = box_element_ty(tcx, current) else {
            return false;
        };
        current = element;
    }
    true
}

/// Whether `ty` is a top-level intercepted collection: a `Vec` / `String` (a
/// real rustc-layout header) or a `BTreeMap` / `HashMap` (the address of a
/// `{ptr,cap,len}` slot). Only the maps are heap-image-only (`heap_image_only`).
fn is_intercepted_collection<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    vec_element_ty(tcx, ty).is_some()
        || is_string_ty(tcx, ty)
        || btreemap_kv_ty(tcx, ty).is_some()
        || any_hashmap_kv_ty(tcx, ty).is_some()
}

/// Whether this module lowers `drop_glue::<payload>`: an intercepted heap value
/// (`Box` or intercepted collection) that needs drop and whose whole
/// destruction `boxed_payload_drop_recursively_lowerable` admits — the exact set
/// `emit_recursive_payload_drop` can emit — minus any chain that holds a
/// `HashMap` (`holds_hashmap`).
fn payload_is_lowered<'tcx>(tcx: TyCtxt<'tcx>, payload: Ty<'tcx>) -> bool {
    payload.needs_drop(tcx, ty::TypingEnv::fully_monomorphized())
        && (box_element_ty(tcx, payload).is_some() || is_intercepted_collection(tcx, payload))
        && boxed_payload_drop_recursively_lowerable(tcx, payload, 1)
        && frees_through_global(tcx, payload, 0)
        && !holds_hashmap(tcx, payload, 0)
}

/// Whether `ty`'s box chain ends in a `HashMap` (std's or hashbrown's). Such a
/// glue is NOT lowered here, so a `Box<HashMap<..>> as Box<dyn Trait>` keeps
/// refusing as it did before this module. The glue itself would be right (at
/// -O0/-O1 it builds and matches LLVM under the heap ledger); the value it
/// would destroy is not: the bridge's -O2/-O3 empty-`HashMap` construction
/// lowers BOTH map-typed struct literals rustc inlines `HashMap::new` into
/// (the inner `hashbrown::map::HashMap { .. }` and the outer
/// `HashMap { base }`) with `emit_btreemap_empty_slot`, so the inner literal's
/// reserved 16-byte buffer is never freed. Measured on 16a86a97b: a plain local
/// `HashMap::<u64, u64>::new()` at -O2/-O3 nets `1 16` live where LLVM nets
/// `0 0`, and admitting this glue turned the refused `Box<dyn Trait>` owning
/// one into a build with the same leak. Lift this when that construction
/// forwards the inner literal's slot instead of reserving a second one.
fn holds_hashmap<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, depth: u32) -> bool {
    if depth > 16 {
        return true;
    }
    if any_hashmap_kv_ty(tcx, ty).is_some() {
        return true;
    }
    match box_element_ty(tcx, ty) {
        Some(element) => holds_hashmap(tcx, element, depth + 1),
        None => false,
    }
}

/// Whether every allocator on `ty`'s heap chain is `alloc::alloc::Global` (the
/// `global_alloc_ty` lang item, by identity): the destruction
/// `emit_recursive_payload_drop` emits frees through `__rust_dealloc`, which is
/// `Global`'s free and no other allocator's. `box_element_ty` does not check
/// `Box`'s allocator, and `vec_element_ty` accepts any ZST one, so a
/// `Box<T, A>` / `Vec<T, A>` with a custom `A` would otherwise be freed into the
/// wrong allocator — rustc's own glue (which this replaces) calls
/// `A::deallocate`. `BTreeMap`'s allocator is its third parameter; `String` and
/// std's `HashMap` have none.
fn frees_through_global<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, depth: u32) -> bool {
    if depth > 16 {
        return false;
    }
    let ty::Adt(_, args) = ty.kind() else {
        return true;
    };
    let is_global = |index: usize| -> bool {
        match args.types().nth(index) {
            None => true,
            Some(alloc) => matches!(alloc.kind(), ty::Adt(a, _)
                if Some(a.did()) == tcx.lang_items().global_alloc_ty()),
        }
    };
    if let Some(element) = box_element_ty(tcx, ty) {
        return is_global(1) && frees_through_global(tcx, element, depth + 1);
    }
    if vec_element_ty(tcx, ty).is_some() {
        return is_global(1);
    }
    if btreemap_kv_ty(tcx, ty).is_some() {
        return is_global(2);
    }
    // `String` (always `Global`) and a std `HashMap` (no allocator parameter).
    true
}

/// The payload `C` when `instance` is a `drop_glue::<C>` this module lowers.
pub(super) fn glue_payload<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>) -> Option<Ty<'tcx>> {
    let ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, Some(payload))) = instance.def else {
        return None;
    };
    let payload = tcx.normalize_erasing_regions(
        ty::TypingEnv::fully_monomorphized(),
        ty::Unnormalized::new_wip(payload),
    );
    payload_is_lowered(tcx, payload).then_some(payload)
}

/// Whether the body this module gives `drop_glue::<payload>` is valid only for a
/// locally constructed `Box<payload>` image: a map or a Box chain holding one, whose
/// destruction frees the 24-byte `{ptr,cap,len}` slot block its cell forwards
/// to. A `Vec` / `String` is NOT here: its header is rustc's own inline layout
/// (`real_vec_string_header_layout`) and its destruction frees only the data
/// buffer that header names, which is right for a header at any address.
/// (`HashMap` is listed although `payload_is_lowered` does not admit it today,
/// so lifting `holds_hashmap` cannot also lift this origin check.)
fn heap_image_only<'tcx>(tcx: TyCtxt<'tcx>, payload: Ty<'tcx>) -> bool {
    contains_slot_map(tcx, payload) && payload_is_lowered(tcx, payload)
}

/// The body lowered for an admitted `drop_glue::<C>` in place of rustc's shim:
///
/// ```text
/// bb0: drop((*_1)) -> [return: bb1, unwind unreachable]
/// bb1: return
/// ```
///
/// rustc's own body is opt-level dependent (inlined `Vec::drop` / `RawVec` reads
/// at `-O2`) and reads `C` at rustc's layout; this one is the glue's definition
/// and is the same at every opt level. The unwind edge is unreachable: the
/// destruction it lowers to is loads plus `__rust_dealloc`, which never unwinds,
/// and no user code runs inside it (the admitted payloads have no `Drop` impl of
/// their own anywhere in the chain).
pub(super) fn canonical_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    original: &Body<'tcx>,
) -> Result<Body<'tcx>, String> {
    if original.arg_count != 1 {
        return Err(format!(
            "[TCG-HEAP-IMAGE-GLUE] drop glue body has {} arguments, expected the one \
             `&mut T` receiver — failing closed",
            original.arg_count
        ));
    }
    let mut body = original.clone();
    // Both terminators reuse the shim's first one, for its source info.
    let source_info = original.basic_blocks[mir::START_BLOCK]
        .terminator()
        .source_info;
    let ret_terminator = crate::synthetic_terminator::new(source_info, TerminatorKind::Return);
    let blocks = body.basic_blocks.as_mut();
    blocks.raw.truncate(1);
    blocks[mir::START_BLOCK].statements.clear();
    blocks[mir::START_BLOCK].is_cleanup = false;
    let ret = blocks.push(mir::BasicBlockData::new(Some(ret_terminator), false));
    *blocks[mir::START_BLOCK].terminator_mut() = crate::synthetic_terminator::new(
        source_info,
        TerminatorKind::Drop {
            place: tcx.mk_place_deref(Place::from(Local::new(1))),
            target: ret,
            unwind: mir::UnwindAction::Unreachable,
            replace: false,
            drop: None,
        },
    );
    body.var_debug_info.clear();
    body.local_decls.raw.truncate(body.arg_count + 1);
    Ok(body)
}

/// Lower the canonical body's one `drop((*_1))`. `Ok(false)` for every other
/// drop (any other function, or a place that is not that one), so the caller's
/// ordinary arms see it unchanged.
pub(super) fn lower_drop<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    place: &Place<'tcx>,
    place_ty: Ty<'tcx>,
    target: mir::BasicBlock,
) -> Result<bool, String> {
    let Some(payload) = glue_payload(ctx.tcx, ctx.instance) else {
        return Ok(false);
    };
    if place.local != Local::new(1)
        || !is_entry_arg(body, place.local)
        || !matches!(place.projection.as_ref(), [ProjectionElem::Deref])
    {
        return Ok(false);
    }
    if ctx.tcx.erase_and_anonymize_regions(place_ty) != ctx.tcx.erase_and_anonymize_regions(payload)
    {
        return Err(format!(
            "[TCG-HEAP-IMAGE-GLUE] `drop_glue::<{payload:?}>` drops a `{place_ty:?}` \
             through its receiver — the glue's own type and the dropped place disagree; \
             failing closed"
        ));
    }
    let cell = value_for_scalar_binding(ctx, ScalarPlaceBinding::Local(place.local))?;
    let cell = coerce_to_plain_ptr(ctx, block, cell);
    emit_recursive_payload_drop(ctx, block, cell, payload, 1)?;
    block.body.push(InstrNode::new(Inst::Br {
        target: BlockId::new(target.index() as u32),
        args: Vec::new(),
    }));
    Ok(true)
}

/// Refuse a vtable for `self_ty` whose drop slot would be this module's
/// heap-image body but whose data pointer is not a `Box<self_ty>`'s own cell.
pub(super) fn check_vtable_drop_origin<'tcx>(
    tcx: TyCtxt<'tcx>,
    self_ty: Ty<'tcx>,
    origin: VtableDropOrigin,
) -> Result<(), String> {
    if origin == VtableDropOrigin::OwnedBox || !heap_image_only(tcx, self_ty) {
        return Ok(());
    }
    Err(format!(
        "[TCG-HEAP-IMAGE-VTABLE] a vtable for `{self_ty:?}` built from a value that is \
         not a locally constructed bridge-owned map image (including an incoming \
         `Box`, a borrow, a raw pointer, a dyn-tail struct or a pointer wrapper): \
         its drop slot is `drop_glue::<{self_ty:?}>`, \
         whose body frees the heap {{ptr,cap,len}} image a `Box` of that type owns \
         (data buffer AND slot block), and this data pointer is not such an image — a \
         drop through it could read or free unrelated storage. Failing closed. \
         Construct the map and its owning Box locally through the bridge, or build \
         this crate with the LLVM backend."
    ))
}

/// Refuse a direct (non-vtable) reference to a heap-image-only glue: its body is
/// valid only for a `Box`'s own cell, and a direct caller —
/// `ptr::drop_in_place::<C>(&mut v)` — can hand it a frame-local value.
pub(super) fn refuse_direct_reference<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
) -> Result<(), String> {
    let Some(payload) = glue_payload(tcx, instance) else {
        return Ok(());
    };
    if !heap_image_only(tcx, payload) {
        return Ok(());
    }
    Err(format!(
        "[TCG-HEAP-IMAGE-GLUE] direct call of `drop_glue::<{payload:?}>` (e.g. \
         `ptr::drop_in_place` on a `{payload:?}`): this backend lowers that glue only for \
         the vtable of a `Box<{payload:?}> as Box<dyn Trait>`, whose argument is the \
         box's heap image; a direct caller can pass a frame-local value, whose slot the \
         body would free. Failing closed. Fix options: (a) let the value drop normally \
         (`drop(v)` / scope end), (b) build this crate with the LLVM backend."
    ))
}
