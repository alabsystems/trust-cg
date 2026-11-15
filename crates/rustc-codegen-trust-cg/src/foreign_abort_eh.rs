// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! A Rust abort strategy does not make a foreign C-unwind call nounwind.
//! Keep only its actual source-owned unwind CFG live; Rust panic entries and
//! Rust-defined Drop bodies still obey their queried nounwind abort ABI.

use rustc_span::Span;

use super::{
    Body, MirLoweringCtx, Operand, RustcFnAbiSource, TerminatorKind, call_callee_can_unwind,
    call_func_is_static_fn_item, direct_callee_instance, mir, panic_is_abort, ty,
};

fn refusal(ctx: &MirLoweringCtx<'_>, why: &str) -> String {
    format!(
        "[TCG-EH-FOREIGN-ABORT] `{}`: {why}; refusing rather than dropping a live foreign unwind edge",
        ctx.tcx.symbol_name(ctx.instance).name
    )
}

/// The Mach-O adapter is implemented first. Other targets keep the existing
/// foreign-abort refusal until their own native controls qualify the contract.
fn supported(ctx: &MirLoweringCtx<'_>) -> bool {
    ctx.tcx.sess.target.arch.desc() == "aarch64" && ctx.tcx.sess.target.is_like_darwin
}

/// Whether this exact MIR call has a live, modeled unwind edge. The cheap rustc
/// ABI predicate excludes ordinary Rust abort calls; an admitted foreign edge
/// additionally needs the real resolved instance's FnAbi, never a symbol guess.
pub(super) fn live_call_edge<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    func: &Operand<'tcx>,
    span: Span,
    unwind: &mir::UnwindAction,
) -> Result<bool, String> {
    if !matches!(
        unwind,
        mir::UnwindAction::Cleanup(_) | mir::UnwindAction::Terminate(_)
    ) {
        return Ok(false);
    }
    // A call through which LLVM may inline a terminate pad into this frame:
    // lowered as an invoke although its callee cannot unwind.
    if super::inlined_terminate_pads::is_inherited(unwind) {
        return Ok(true);
    }
    if !panic_is_abort(ctx.tcx) {
        return Ok(true);
    }
    if !call_callee_can_unwind(ctx, body, func) {
        return Ok(false);
    }
    if !supported(ctx) || crate::knobs::is_enabled(crate::knobs::DISABLE_UNWIND) {
        return Err(refusal(
            ctx,
            "foreign-exception abort adapter is unavailable or EH is disabled",
        ));
    }
    if !call_func_is_static_fn_item(ctx, body, func) {
        return Err(refusal(
            ctx,
            "foreign function-pointer abort continuation is not modeled",
        ));
    }
    let instance = direct_callee_instance(ctx, body, func, span)
        .map_err(|why| refusal(ctx, &format!("actual foreign instance: {why}")))?;
    let callee_ty = instance.ty(ctx.tcx, ty::TypingEnv::fully_monomorphized());
    let signature = ctx
        .tcx
        .instantiate_bound_regions_with_erased(callee_ty.fn_sig(ctx.tcx));
    if signature.c_variadic() {
        return Err(refusal(
            ctx,
            "variadic foreign abort continuation is not modeled",
        ));
    }
    let abi = RustcFnAbiSource::Instance(instance)
        .query(ctx.tcx)
        .map_err(|why| refusal(ctx, &format!("actual foreign FnAbi: {why}")))?;
    Ok(abi.can_unwind)
}

/// Seed foreign call landing pads and the transitive cleanup domain before
/// ordinary cleanup scalar homes/dataflow are computed. Dead Rust-panic unwind
/// successors must not revive other cleanup bodies in an abort crate.
pub(super) fn seed<'tcx>(ctx: &mut MirLoweringCtx<'tcx>, body: &Body<'tcx>) -> Result<(), String> {
    let mut pending = Vec::new();
    for data in body.basic_blocks.iter() {
        if data.is_cleanup {
            continue;
        }
        let TerminatorKind::Call {
            func,
            fn_span,
            unwind,
            ..
        } = &data.terminator().kind
        else {
            continue;
        };
        if live_call_edge(ctx, body, func, *fn_span, unwind)? {
            ctx.eh_active = true;
            if let mir::UnwindAction::Cleanup(pad) = unwind {
                ctx.eh_landing_pad_blocks.insert(*pad);
                pending.push(*pad);
            }
        }
    }
    while let Some(bb) = pending.pop() {
        if !ctx.foreign_abort_cleanup_blocks.insert(bb) {
            continue;
        }
        let data = &body.basic_blocks[bb];
        if !data.is_cleanup {
            return Err(refusal(
                ctx,
                "foreign unwind destination is not a source cleanup block",
            ));
        }
        let terminator = data.terminator();
        match &terminator.kind {
            TerminatorKind::Call {
                func,
                fn_span,
                target,
                unwind,
                ..
            } => {
                pending.extend(*target);
                if live_call_edge(ctx, body, func, *fn_span, unwind)? {
                    if let mir::UnwindAction::Cleanup(pad) = unwind {
                        ctx.eh_landing_pad_blocks.insert(*pad);
                        pending.push(*pad);
                    }
                }
            }
            TerminatorKind::Drop { target, .. } | TerminatorKind::Assert { target, .. } => {
                // Both callees obey their real Rust nounwind ABI under abort.
                pending.push(*target);
            }
            TerminatorKind::UnwindResume => {
                return Err(refusal(
                    ctx,
                    "live cleanup resumes through a nounwind abort body instead of source Terminate(Abi)",
                ));
            }
            _ => pending.extend(terminator.successors()),
        }
    }
    // A frame with no foreign edge of its own that LLVM may give one by
    // inlining a callee that holds a terminate pad.
    if !ctx.eh_active && supported(ctx) && !crate::knobs::is_enabled(crate::knobs::DISABLE_UNWIND) {
        super::inlined_terminate_pads::seed(ctx, body);
    }
    if ctx.eh_active {
        require_non_unwinding_frame(ctx)?;
    }
    Ok(())
}

/// A live foreign edge gives this body an LSDA, which the backend emits as a
/// non-unwinding frame under abort (`CompilerConfig::eh_frames_cannot_unwind`):
/// the region rule of LLVM's call-site table for a `nounwind` function, which
/// keeps unwinding only through a region holding an indirect call or a call to
/// a callee not known to be `nounwind`. That is rustc's contract for every body
/// it defines under `panic=abort`, an `extern "C-unwind"` export included.
/// Re-query this body's own FnAbi rather than infer it from the strategy, and
/// refuse a body that could unwind.
fn require_non_unwinding_frame(ctx: &MirLoweringCtx<'_>) -> Result<(), String> {
    let abi = RustcFnAbiSource::Instance(ctx.instance)
        .query(ctx.tcx)
        .map_err(|why| refusal(ctx, &format!("actual frame FnAbi: {why}")))?;
    if abi.can_unwind {
        return Err(refusal(
            ctx,
            "this abort body's own FnAbi can unwind, so its exception table cannot omit \
             propagation",
        ));
    }
    Ok(())
}
