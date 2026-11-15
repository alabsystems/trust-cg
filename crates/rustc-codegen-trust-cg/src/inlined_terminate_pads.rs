// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! A `panic=abort` frame that LLVM gives an exception table by inlining a
//! callee that holds a terminate pad.
//!
//! Under `panic=abort` a body whose MIR has no live foreign edge has no
//! exception table, so an unwinder walks through its frame: a panic from a
//! `nounwind` callee keeps unwinding to the caller. When LLVM inlines into
//! such a frame a callee whose own call to an `extern "C-unwind"` function
//! has a terminate pad (`fn wcb(id: u64) { unsafe { cb(id) } }`), the frame
//! acquires that invoke, its LSDA and LLVM's region rule: the region holding
//! the frame's other `nounwind` calls becomes a gap where the phase-one search
//! fails. Measured (a `nounwind` driver call next to such a wrapper, O0-O3):
//! `#[inline(always)]` at every level, `#[inline]` and a small plain local
//! function at O1-O3, a cross-crate `#[inline]` function handed the wrapper
//! as a `fn` pointer at O1-O3. Without a table this backend's frame keeps
//! unwinding there.
//!
//! LLVM's inliner turns on cost heuristics this lowering cannot see, so the
//! rule records the inlining wherever LLVM may perform it: a call to a callee
//! LLVM may inline at this level ([`may_inline`]) whose body, or the body of
//! one it may inline in turn (to [`INLINE_DEPTH`] levels, through a `fn`
//! pointer argument the frame passes it as well), holds a call with a
//! terminate or cleanup edge to a callee that can unwind. Such a call is
//! lowered as an invoke with a terminate pad, as if its callee could unwind:
//! the frame gets the table LLVM's would have, and the callee, a `nounwind`
//! Rust function, never unwinds into the pad (its own table stops every
//! exception inside it). Where LLVM does not inline, its frame has no table
//! and its search continues past the frame, so this one's fails phase one
//! there earlier (OD-58), never later. The top-level call is limited to a
//! plain `fn` item or method returning `()`, a primitive scalar or a thin
//! pointer: a closure called directly, or a call returning an aggregate, an
//! enum or a fat pointer, takes a lane with no terminate edge, which leaves
//! those shapes open.

use std::collections::{HashMap, HashSet};

use crate::compiler_attributes::InlineAttr;

use super::{
    Body, Instance, MirLoweringCtx, TerminatorKind, created_call_unwind, is_real_std_crate_def,
    mir, panic_is_abort, ty,
};

mod depth_visit;

/// How deep the walk follows callees LLVM may inline into one another.
const INLINE_DEPTH: usize = 3;

/// How many callee bodies the walk reads for one frame. A frame whose walk
/// runs out is treated as one LLVM gives no table (the open direction): the
/// bound limits total body reads, including revisits at greater remaining
/// depth. Exhaustion does not establish absence or call-order independence.
const BODY_BUDGET: usize = 256;

/// The unwind action a call inherits a terminate pad through
/// ([`unwind_action`]). Recognized by address ([`is_inherited`]).
static INHERITED_TERMINATE: mir::UnwindAction =
    mir::UnwindAction::Terminate(mir::UnwindTerminateReason::Abi);

/// Record the calls of `body` through which LLVM may inline a terminate pad
/// into this frame, when the frame has no live foreign edge of its own, and
/// give the frame its exception table (`MirLoweringCtx::eh_active`). Returns
/// whether it did.
pub(super) fn seed<'tcx>(ctx: &mut MirLoweringCtx<'tcx>, body: &Body<'tcx>) -> bool {
    if ctx.eh_active || !panic_is_abort(ctx.tcx) {
        return false;
    }
    let optimizes = ctx.session_optimizes();
    let mut calls = HashSet::new();
    let mut budget = BODY_BUDGET;
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if data.is_cleanup {
            continue;
        }
        let TerminatorKind::Call {
            func,
            args,
            destination,
            unwind,
            target: Some(_),
            ..
        } = &data.terminator().kind
        else {
            continue;
        };
        if !scalar_result(ctx, ctx.monomorphize_ty(destination.ty(body, ctx.tcx).ty)) {
            continue;
        }
        if matches!(
            unwind,
            mir::UnwindAction::Cleanup(_) | mir::UnwindAction::Terminate(_)
        ) {
            continue;
        }
        // A static callee, or the item a `fn` pointer certainly holds (the
        // call is then lowered as the direct call LLVM makes,
        // `created_call_unwind::static_fn_pointer_callee`).
        let callee_ty = ctx.monomorphize_ty(func.ty(body, ctx.tcx));
        let callee = match callee_ty.kind() {
            ty::FnPtr(..) => created_call_unwind::direct_fn_pointer_target(ctx, body, func),
            _ => resolve(ctx, callee_ty),
        };
        let Some(callee) = callee else {
            continue;
        };
        if !matches!(
            ctx.tcx.def_kind(callee.def_id()),
            rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
        ) || !may_inline(ctx, callee, optimizes)
        {
            continue;
        }
        let pointer_targets: Vec<Instance<'tcx>> = args
            .iter()
            .filter_map(|arg| created_call_unwind::fn_pointer_operand_target(ctx, body, &arg.node))
            .collect();
        let mut seen = HashMap::new();
        let mut walk = Walk {
            pointer_targets: &pointer_targets,
            optimizes,
            seen: &mut seen,
            budget: &mut budget,
        };
        if holds_terminate_pad(ctx, callee, INLINE_DEPTH, &mut walk) {
            calls.insert(bb);
        }
    }
    if calls.is_empty() {
        return false;
    }
    ctx.inherited_terminate_calls = calls;
    ctx.eh_active = true;
    true
}

/// Whether a call returning `ty` takes the direct call lane that carries a
/// terminate edge: `()`, a primitive scalar, or a thin pointer. A call whose
/// result is an aggregate, an enum or a fat pointer may take a lane with no
/// normal-edge continuation for its result (measured: a by-value struct and
/// `Option<u64>` refused), so it is not given the inherited edge and stays
/// open.
fn scalar_result<'tcx>(ctx: &MirLoweringCtx<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    match ty.kind() {
        ty::Tuple(fields) => fields.is_empty(),
        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) => true,
        ty::RawPtr(pointee, _) | ty::Ref(_, pointee, _) => {
            pointee.is_sized(ctx.tcx, ty::TypingEnv::fully_monomorphized())
        }
        _ => false,
    }
}

/// The unwind action the call terminating `bb` is lowered with: a terminate
/// edge for a call [`seed`] recorded, its own otherwise.
pub(super) fn unwind_action<'a>(
    ctx: &MirLoweringCtx<'_>,
    bb: mir::BasicBlock,
    unwind: &'a mir::UnwindAction,
) -> &'a mir::UnwindAction {
    if ctx.inherited_terminate_calls.contains(&bb) {
        &INHERITED_TERMINATE
    } else {
        unwind
    }
}

/// Whether `unwind` is the terminate edge of a call [`seed`] recorded: a live
/// edge although its callee cannot unwind.
pub(super) fn is_inherited(unwind: &mir::UnwindAction) -> bool {
    std::ptr::eq(unwind, &INHERITED_TERMINATE)
}

/// The instance a call through a callee of type `callee_ty` reaches, when it
/// names one statically.
fn resolve<'tcx>(ctx: &MirLoweringCtx<'tcx>, callee_ty: ty::Ty<'tcx>) -> Option<Instance<'tcx>> {
    let item = crate::fn_items::view(callee_ty.kind())?;
    let def_id = item.def_id();
    let args = item.unbound_args()?;
    Instance::try_resolve(ctx.tcx, ty::TypingEnv::fully_monomorphized(), def_id, args)
        .ok()
        .flatten()
}

/// Whether LLVM may inline `instance` into a caller at this level: a plain
/// item (a function, a method or a closure body) with a body LLVM can see
/// (local, cross-crate inlinable, or a generic instantiated here) that is not
/// `#[inline(never)]`. At O0 only `#[inline(always)]` (LLVM's always-inliner);
/// above O0 any such item, whatever LLVM's cost model would decide. The
/// standard library's own items are not followed: its bodies are built
/// `panic=unwind`, where no call carries the terminate edge an abort crate's
/// foreign call does.
fn may_inline<'tcx>(ctx: &MirLoweringCtx<'tcx>, instance: Instance<'tcx>, optimizes: bool) -> bool {
    let ty::InstanceKind::Item(def_id) = instance.def else {
        return false;
    };
    if ctx.tcx.is_foreign_item(def_id)
        || ctx.tcx.intrinsic(def_id).is_some()
        || is_real_std_crate_def(ctx.tcx, def_id)
        || !ctx.tcx.is_mir_available(def_id)
    {
        return false;
    }
    match ctx.tcx.codegen_fn_attrs(def_id).inline {
        InlineAttr::Never => false,
        InlineAttr::Always | InlineAttr::Force { .. } => true,
        InlineAttr::None | InlineAttr::Hint => {
            optimizes
                && (def_id.is_local()
                    || ctx.tcx.cross_crate_inlinable(def_id)
                    || instance.args.non_erasable_generics().next().is_some())
        }
    }
}

/// The state of one walk from a frame's call ([`holds_terminate_pad`]).
struct Walk<'a, 'tcx> {
    /// The functions the frame passes the call as `fn` pointers: what a call
    /// through a `fn` pointer in an inlined body may reach.
    pointer_targets: &'a [Instance<'tcx>],
    optimizes: bool,
    /// Greatest remaining depth at which each body has been admitted. A
    /// shorter route may expose callees a prior depth-zero visit could not.
    seen: &'a mut HashMap<Instance<'tcx>, usize>,
    /// Callee bodies left to read for the frame ([`BODY_BUDGET`]).
    budget: &'a mut usize,
}

/// Whether the body of `instance`, inlined, brings a terminate or cleanup pad:
/// it holds a call with such an edge to a callee that can unwind, or (within
/// `depth` levels) a call to a callee LLVM may inline that does, statically or
/// through a `fn` pointer, which may hold any of the walk's pointer targets.
fn holds_terminate_pad<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    instance: Instance<'tcx>,
    depth: usize,
    walk: &mut Walk<'_, 'tcx>,
) -> bool {
    if !depth_visit::admit(walk.seen, walk.budget, instance, depth) {
        return false;
    }
    let mir = ctx.tcx.instance_mir(instance.def);
    for data in mir.basic_blocks.iter() {
        if data.is_cleanup {
            continue;
        }
        let TerminatorKind::Call { func, unwind, .. } = &data.terminator().kind else {
            continue;
        };
        let Ok(callee_ty) = instance.try_instantiate_mir_and_normalize_erasing_regions(
            ctx.tcx,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(ctx.tcx, func.ty(mir, ctx.tcx)),
        ) else {
            continue;
        };
        let can_unwind = match *callee_ty.kind() {
            ty::FnDef(def_id, _) => rustc_middle::ty::layout::fn_can_unwind(
                ctx.tcx,
                Some(def_id),
                callee_ty.fn_sig(ctx.tcx).abi(),
            ),
            ty::FnPtr(..) => rustc_middle::ty::layout::fn_can_unwind(
                ctx.tcx,
                None,
                callee_ty.fn_sig(ctx.tcx).abi(),
            ),
            _ => true,
        };
        if can_unwind
            && matches!(
                unwind,
                mir::UnwindAction::Cleanup(_) | mir::UnwindAction::Terminate(_)
            )
        {
            return true;
        }
        if depth == 0 {
            continue;
        }
        let targets: Vec<Instance<'tcx>> = match *callee_ty.kind() {
            ty::FnDef(..) => resolve(ctx, callee_ty).into_iter().collect(),
            ty::FnPtr(..) => walk.pointer_targets.to_vec(),
            _ => Vec::new(),
        };
        for target in targets {
            if may_inline(ctx, target, walk.optimizes)
                && holds_terminate_pad(ctx, target, depth - 1, walk)
            {
                return true;
            }
        }
    }
    false
}
