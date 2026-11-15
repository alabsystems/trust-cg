// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! MIR assertion failure calls resolved through rustc's actual lang-item ABI.
//!
//! This bridge has a `TyCtxt` and a MIR source scope. A general TrustIR producer
//! does not acquire those runtime/location authorities by using the same symbol
//! spelling. The standalone source-Assert refusal floor remains separate.

use crate::lang_items::LangItem;
use rustc_span::Spanned;
use rustc_target::callconv::PassMode;

use super::{
    Block, BlockId, Body, FuncId, Inst, Instance, InstrNode, MirLoweringCtx, Operand,
    RustcFnAbiSource, Ty, ValueId, caller_location_for_call, emit_diverging_panic_call,
    instance_abi_has_caller_location, lower_direct_call_args, mir, operand_rust_ty, ty,
};

/// The operands a failed assertion's panic entry READS at run time, in the
/// entry's parameter order: exactly the ones rustc's `codegen_assert_terminator`
/// evaluates in its panic block — `(index, len)` for a bounds check,
/// `(required, found)` for a misalignment, `source` for an invalid enum
/// construction. Every other kind's entry takes only the caller Location (the
/// operands an overflow / division assert carries are for diagnostics and are
/// never evaluated). Only the failure block reads them.
fn payload_operands<'a, 'tcx>(message: &'a mir::AssertMessage<'tcx>) -> Vec<&'a Operand<'tcx>> {
    match message {
        mir::AssertKind::BoundsCheck { index, len } => vec![index, len],
        mir::AssertKind::MisalignedPointerDereference { required, found } => {
            vec![required, found]
        }
        mir::AssertKind::InvalidEnumConstruction(source) => vec![source],
        _ => Vec::new(),
    }
}

/// The entry rustc's codegen calls for `message`: `panic_bounds_check`,
/// `panic_misaligned_pointer_dereference`, and `AssertKind::panic_function` —
/// the very table rustc reads — for the other admitted kinds. `None` for a kind
/// this bridge has not qualified (`ResumedAfterDrop`, an overflow assert on an
/// operator that cannot overflow, on which `panic_function` would ICE).
fn entry_lang_item(message: &mir::AssertMessage<'_>) -> Option<LangItem> {
    match message {
        mir::AssertKind::BoundsCheck { .. } => Some(LangItem::PanicBoundsCheck),
        mir::AssertKind::MisalignedPointerDereference { .. } => {
            Some(LangItem::PanicMisalignedPointerDereference)
        }
        mir::AssertKind::Overflow(
            mir::BinOp::Add
            | mir::BinOp::Sub
            | mir::BinOp::Mul
            | mir::BinOp::Div
            | mir::BinOp::Rem
            | mir::BinOp::Shl
            | mir::BinOp::Shr,
            _,
            _,
        )
        | mir::AssertKind::OverflowNeg(_)
        | mir::AssertKind::DivisionByZero(_)
        | mir::AssertKind::RemainderByZero(_)
        | mir::AssertKind::NullPointerDereference
        | mir::AssertKind::NullReferenceConstructed
        | mir::AssertKind::InvalidEnumConstruction(_)
        | mir::AssertKind::ResumedAfterReturn(_)
        | mir::AssertKind::ResumedAfterPanic(_) => Some(message.panic_function()),
        _ => None,
    }
}

/// A resolved panic entry: its declaration and rustc's actual unwind
/// permission for it (`FnAbi::can_unwind`).
struct Entry<'tcx> {
    instance: Instance<'tcx>,
    callee: FuncId,
    can_unwind: bool,
}

/// Resolve `lang_item` as a non-generic `#[track_caller]` Rust entry taking
/// exactly `payload` (then its hidden caller Location) and returning `!`,
/// checked against both its source signature and its queried `FnAbi`, then
/// declare it through the common instance classifier: the same source FnAbi
/// authority determines this declaration and ordinary Rust calls. Never
/// infers a C signature from the entry's symbol or copies a register ABI.
fn resolve_entry<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    lang_item: LangItem,
    payload: &[Ty<'tcx>],
    refusal: &dyn Fn(&str) -> String,
) -> Result<Entry<'tcx>, String> {
    let def_id = ctx
        .tcx
        .lang_items()
        .get(lang_item)
        .ok_or_else(|| refusal(&format!("missing actual {lang_item:?} lang item")))?;
    if ctx.tcx.generics_of(def_id).count() != 0 {
        return Err(refusal(&format!(
            "{lang_item:?} has unsupported generic parameters"
        )));
    }
    let instance = Instance::mono(ctx.tcx, def_id);
    let instance_ty = instance.ty(ctx.tcx, ty::TypingEnv::fully_monomorphized());
    let signature = ctx
        .tcx
        .instantiate_bound_regions_with_erased(instance_ty.fn_sig(ctx.tcx));
    if signature.abi() != rustc_abi::ExternAbi::Rust
        || signature.c_variadic()
        || !signature.output().is_never()
        || signature.inputs() != payload
        || !instance_abi_has_caller_location(ctx.tcx, instance)
    {
        return Err(refusal(&format!(
            "{lang_item:?} requires unsupported source/caller-location signature {signature:?} \
             for payload {payload:?}"
        )));
    }

    let abi = RustcFnAbiSource::Instance(instance)
        .query(ctx.tcx)
        .map_err(|why| refusal(&format!("{lang_item:?} FnAbi query: {why}")))?;
    // rustc's layout query erases regions, while caller_location_ty returns
    // &'static Location<'static>. Compare the same erased runtime type, not
    // lifetime spelling; this retains the actual lang item's pointee identity.
    let location_ty = ctx
        .tcx
        .erase_and_anonymize_regions(ctx.tcx.caller_location_ty());
    if abi.conv != rustc_abi::CanonAbi::Rust
        || abi.c_variadic
        || abi.fixed_count != payload.len() as u32
        || !matches!(abi.ret.mode, PassMode::Ignore)
        || !abi.ret.layout.ty.is_never()
        || abi.args.len() != payload.len() + 1
        || abi.args.iter().enumerate().any(|(index, argument)| {
            let expected = payload.get(index).copied().unwrap_or(location_ty);
            argument.layout.ty != expected || !matches!(argument.mode, PassMode::Direct(_))
        })
    {
        return Err(refusal(&format!(
            "{lang_item:?} requires unsupported actual argument/return FnAbi {abi:?}"
        )));
    }
    let callee = ctx
        .extern_callee(instance)
        .map_err(|why| refusal(&format!("{lang_item:?} declaration: {why}")))?;
    Ok(Entry {
        instance,
        callee,
        can_unwind: abi.can_unwind,
    })
}

/// Emit only in the assertion's explicit failure block. The success edge must
/// never evaluate a dynamic panic payload, including memory-backed operands.
pub(super) fn emit<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    message: &mir::AssertMessage<'tcx>,
    site: mir::SourceInfo,
    unwind: &mir::UnwindAction,
) -> Result<(), String> {
    let refusal = |why: &str| {
        format!(
            "[TCG-ASSERT-PANIC] {message:?} at {site:?}: {why}; no generic panic or trap substitution"
        )
    };
    if matches!(
        ctx.tcx.sess.panic_strategy(),
        rustc_target::spec::PanicStrategy::ImmediateAbort
    ) {
        // A caller strategy is not evidence that its precompiled core runtime
        // uses the same immediate-abort policy. Neither a normal panic hook nor
        // libc abort's signal may be substituted for that intrinsic policy.
        return Err(refusal("immediate-abort runtime policy is not qualified"));
    }

    let lang_item =
        entry_lang_item(message).ok_or_else(|| refusal("unsupported MIR panic kind"))?;
    let operands = payload_operands(message);
    // The entry's real parameter types must be the MIR payload's own types
    // (`usize` index/len/alignment/address, the `u128` enum source), so the
    // marshalling below passes each operand unconverted.
    let mut payload = Vec::with_capacity(operands.len());
    for operand in &operands {
        let operand_ty = operand_rust_ty(ctx, body, operand)
            .map_err(|why| refusal(&format!("payload type: {why}")))?;
        payload.push(ctx.monomorphize_ty(operand_ty));
    }
    let entry = resolve_entry(ctx, lang_item, &payload, &refusal)?;
    let explicit: Vec<_> = operands
        .into_iter()
        .map(|operand| Spanned {
            node: operand.clone(),
            span: site.span,
        })
        .collect();
    let (arguments, reloads) =
        lower_direct_call_args(ctx, body, block, entry.instance, &explicit, site)
            .map_err(|why| refusal(&format!("{lang_item:?} argument marshalling: {why}")))?;
    if !reloads.is_empty() || arguments.len() != payload.len() + 1 {
        return Err(refusal(&format!(
            "{lang_item:?} argument marshalling disagrees with actual FnAbi"
        )));
    }
    emit_diverging_panic_call(
        ctx,
        block,
        entry.callee,
        arguments,
        unwind,
        entry.can_unwind,
    )
    .map_err(|why| refusal(&format!("{lang_item:?}: {why}")))
}

/// The FAILURE target of a bounds check the bridge itself emits for an
/// INTERCEPTED single-element index (`v[i]` on a `Vec`, `lower_vec_index`):
/// a block calling rustc's own `panic_bounds_check(index, len)` with the
/// intercepted call's caller Location — what the std impl the interception
/// replaces reaches (`<usize as SliceIndex<[T]>>::index`'s MIR bounds check) —
/// so the hook sees rustc's message, "index out of bounds: the len is {len} but
/// the index is {index}". The entry is resolved and checked exactly as a MIR
/// `BoundsCheck` assert's is (`resolve_entry`).
///
/// `index` and `len` are 64-bit values computed in the block that branches
/// here, so they dominate the failure block; each is rebound to the
/// declaration's parameter type by a same-width register `Copy` (a `Vec`
/// slot's length lane is declared `I64`, the `usize` parameter `U64`). The
/// caller admits only 64-bit `usize` sessions.
///
/// Every edge raises through `emit_diverging_panic_call`, as a MIR assert's
/// does: a `Terminate` edge (an intercepted index inside an `extern "C"` body
/// under `panic=unwind`) invokes the entry into the function's terminate pad,
/// so the hook runs with rustc's message before "panic in a function that
/// cannot unwind" aborts; an edge it cannot represent is refused. Only
/// `panic=immediate-abort`, whose real entries are `intrinsics::abort()` and
/// run no hook, keeps the reserved trap block.
pub(super) fn intercepted_bounds_check_fail_target<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    unwind: &mir::UnwindAction,
    index: ValueId,
    len: ValueId,
    site: mir::SourceInfo,
) -> Result<BlockId, String> {
    if matches!(
        ctx.tcx.sess.panic_strategy(),
        rustc_target::spec::PanicStrategy::ImmediateAbort
    ) {
        return Ok(ctx.assert_trap_block(body));
    }
    let refusal = |why: &str| {
        format!(
            "[TCG-ASSERT-PANIC] intercepted bounds check at {site:?}: {why}; no generic panic \
             or trap substitution"
        )
    };
    let usize_ty = ctx.tcx.types.usize;
    let entry = resolve_entry(
        ctx,
        LangItem::PanicBoundsCheck,
        &[usize_ty, usize_ty],
        &refusal,
    )?;
    let params = ctx
        .module
        .function_by_id(entry.callee)
        .map(|function| function.ty)
        .map(|ty| ctx.module.func_types[ty.index() as usize].params.clone())
        .ok_or_else(|| refusal("the panic_bounds_check declaration is missing"))?;
    if params.len() != 3
        || params[..2]
            .iter()
            .any(|param| param.bit_width() != Some(64))
    {
        return Err(refusal(&format!(
            "panic_bounds_check declared with {params:?}, not two 64-bit usize lanes and a \
             Location"
        )));
    }
    let raise_id = ctx.fresh_block_id();
    let mut raise = Block::new(raise_id);
    let mut arguments = Vec::with_capacity(3);
    for (value, param) in [index, len].into_iter().zip(&params) {
        let rebound = ctx.fresh_value();
        raise.body.push(
            InstrNode::new(Inst::Copy {
                ty: param.clone(),
                operand: value,
            })
            .with_result(rebound),
        );
        arguments.push(rebound);
    }
    arguments.push(caller_location_for_call(ctx, body, &mut raise, site)?);
    emit_diverging_panic_call(
        ctx,
        &mut raise,
        entry.callee,
        arguments,
        unwind,
        entry.can_unwind,
    )
    .map_err(|why| refusal(&format!("PanicBoundsCheck: {why}")))?;
    ctx.extra_blocks.push(raise);
    Ok(raise_id)
}

/// Resolve the nounwind diverging runtime entry used by a real Rust terminate
/// landing pad. The reason's lang item and queried instance ABI authorize the
/// declaration, including the absence of a hidden caller-location argument.
pub(super) fn terminate_callee<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    reason: mir::UnwindTerminateReason,
) -> Result<FuncId, String> {
    let lang_item = reason.lang_item();
    let refusal = |why: &str| {
        format!("[TCG-EH-TERMINATE] {reason:?}/{lang_item:?}: {why}; no inferred panic ABI")
    };
    let def_id = ctx
        .tcx
        .lang_items()
        .get(lang_item)
        .ok_or_else(|| refusal("missing actual terminate lang item"))?;
    if ctx.tcx.generics_of(def_id).count() != 0 {
        return Err(refusal("unsupported generic terminate entry"));
    }
    let instance = Instance::mono(ctx.tcx, def_id);
    let instance_ty = instance.ty(ctx.tcx, ty::TypingEnv::fully_monomorphized());
    let signature = ctx
        .tcx
        .instantiate_bound_regions_with_erased(instance_ty.fn_sig(ctx.tcx));
    if signature.abi() != rustc_abi::ExternAbi::Rust
        || signature.c_variadic()
        || !signature.inputs().is_empty()
        || !signature.output().is_never()
        || instance_abi_has_caller_location(ctx.tcx, instance)
    {
        return Err(refusal(&format!(
            "unsupported source/caller-location signature {signature:?}"
        )));
    }
    let abi = RustcFnAbiSource::Instance(instance)
        .query(ctx.tcx)
        .map_err(|why| refusal(&format!("FnAbi query: {why}")))?;
    if abi.conv != rustc_abi::CanonAbi::Rust
        || abi.c_variadic
        || abi.fixed_count != 0
        || !abi.args.is_empty()
        || !matches!(abi.ret.mode, PassMode::Ignore)
        || !abi.ret.layout.ty.is_never()
        || abi.can_unwind
    {
        return Err(refusal(&format!(
            "unsupported actual argument/return/unwind FnAbi {abi:?}"
        )));
    }
    ctx.extern_callee(instance)
        .map_err(|why| refusal(&format!("instance declaration: {why}")))
}
