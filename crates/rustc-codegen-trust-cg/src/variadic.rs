//! Direct scalar C varargs on Linux AArch64. The fixed declaration stays shared
//! across calls; each anonymous argument is checked against rustc's call FnAbi,
//! and each whole call (fixed and anonymous values) by the whole-signature
//! placement check, which is the only placement judgment such a declaration
//! gets (`classify_func_ty` records its fixed half instead of judging it).

use super::*;

/// The fixed half of a C-variadic declaration as `classify_func_ty` declared
/// it: the declared values, where each rustc argument's values start
/// (`(FnAbi argument index, first declared value)`), and whether a hidden
/// return buffer leads them. [`call`] extends it with the anonymous tail and
/// judges the whole call against the call-site `FnAbi`; nothing judges the
/// fixed half alone.
#[derive(Clone, Debug)]
pub(super) struct FixedDeclaration {
    pub(super) params: Vec<TrustIrTy>,
    pub(super) arg_starts: Vec<(usize, usize)>,
    pub(super) sret: bool,
}

pub(super) fn declaration<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    source: RustcFnAbiSource<'tcx>,
) -> Result<bool, String> {
    if ctx.tcx.sess.target.arch.desc() != "aarch64"
        || ctx.tcx.sess.target.os != rustc_target::spec::Os::Linux
        || ctx.tcx.data_layout.pointer_size().bytes() != 8
    {
        return Ok(false);
    }
    let source @ RustcFnAbiSource::Instance(instance) = source else {
        return Ok(false);
    };
    let callable = instance.ty(ctx.tcx, ty::TypingEnv::fully_monomorphized());
    if !matches!(callable.kind(), ty::FnDef(..)) {
        return Ok(false);
    }
    let sig = callable.fn_sig(ctx.tcx);
    if !sig.skip_binder().c_variadic() {
        return Ok(false);
    }
    let abi = source.query(ctx.tcx)?;
    if !abi.c_variadic || abi.conv != rustc_abi::CanonAbi::C {
        return Err("[TCG-VARARG-ABI] variadic declaration needs the canonical C ABI".into());
    }
    // Only direct declarations acquire this path. Indirect call argument and
    // signature handling keep their existing admission rules.
    Ok(true)
}

pub(super) fn call<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    callee: Instance<'tcx>,
    inputs: &[Ty<'tcx>],
    args: &[rustc_span::Spanned<Operand<'tcx>>],
) -> Result<Option<(Vec<ValueId>, Vec<MutableReferenceArgReload>)>, String> {
    let source = RustcFnAbiSource::Instance(callee);
    if !declaration(ctx, source)? {
        return Ok(None);
    }
    if args.len() < inputs.len() {
        return Err("[TCG-VARARG-ABI] call omits a fixed argument".into());
    }
    let anonymous = &args[inputs.len()..];
    let types: Vec<_> = anonymous
        .iter()
        .map(|arg| operand_rust_ty(ctx, body, &arg.node).map(|ty| ctx.normalize_ty(ty)))
        .collect::<Result<_, _>>()?;
    // The CALL-SITE `FnAbi`: the fixed arguments followed by the anonymous ones.
    // The anonymous tail is lowered against this same source below.
    let extra = ctx.tcx.mk_type_list(&types);
    let call_source = RustcFnAbiSource::VariadicCall(callee, extra);
    let abi = ctx
        .tcx
        .fn_abi_of_instance(ty::TypingEnv::fully_monomorphized().as_query_input((callee, extra)))
        .map_err(|err| format!("[TCG-VARARG-ABI] call FnAbi query failed: {err:?}"))?;
    if !abi.c_variadic
        || abi.conv != rustc_abi::CanonAbi::C
        || abi.fixed_count as usize != inputs.len()
        || abi.args.len() != args.len()
    {
        return Err("[TCG-VARARG-ABI] call FnAbi disagrees with the fixed/anonymous split".into());
    }
    for (offset, ty) in types.iter().copied().enumerate() {
        // C default promotions are already explicit in well-typed Rust MIR.
        // Do not silently promote, split a wide value, or pass an aggregate's
        // storage address as an anonymous scalar.
        let bytes = match ty.kind() {
            ty::Int(ty::IntTy::I32) | ty::Uint(ty::UintTy::U32) => 4,
            ty::Int(ty::IntTy::I64 | ty::IntTy::Isize)
            | ty::Uint(ty::UintTy::U64 | ty::UintTy::Usize)
            | ty::Float(ty::FloatTy::F64) => 8,
            // Keep the Rust reference type for the existing call-argument
            // preparation below, including mutable writeback and the guards
            // against snapshots of shared interior-mutable storage.
            ty::RawPtr(..) | ty::Ref(..) if is_thin_pointer_ref_ty(ctx.tcx, ty) => 8,
            _ => {
                return Err(format!(
                    "[TCG-VARARG-ABI] anonymous argument {offset} `{ty:?}` is not a supported promoted scalar, thin pointer or thin reference"
                ));
            }
        };
        let arg = &abi.args[inputs.len() + offset];
        if ctx.normalize_ty(arg.layout.ty) != ty
            || !arg.layout.is_sized()
            || arg.layout.size.bytes() != bytes
            || !matches!(arg.layout.backend_repr, rustc_abi::BackendRepr::Scalar(_))
            || !matches!(arg.mode, rustc_target::callconv::PassMode::Direct(_))
        {
            return Err(format!(
                "[TCG-VARARG-ABI] anonymous argument {offset} `{ty:?}` is not one direct scalar in rustc's call FnAbi"
            ));
        }
        if matches!(ty.kind(), ty::Ref(..)) {
            if let Operand::Copy(place) | Operand::Move(place) = &anonymous[offset].node {
                if ctx.borrowed_scalars.contains_key(&place.local)
                    || ctx.borrowed_aggregates.contains_key(&place.local)
                {
                    return Err(format!(
                        "[TCG-VARARG-ABI] anonymous reference {offset} has no stable referent address; a temporary would change pointer identity"
                    ));
                }
            }
        }
    }
    // THE WHOLE CALL, judged by the one whole-signature check
    // (`check_signature_placement`) against the call-site `FnAbi`: the fixed
    // values exactly as the declaration declared them (recorded by
    // `classify_func_ty`, which does not judge them alone on this lane), then
    // one declared value per anonymous argument, the type its lowering below
    // passes. This is the only placement judgment of the call: a fixed argument
    // rustc places elsewhere is refused here, and so is a fixed half that
    // leaves trust-cg's classifier in another state than rustc's values would,
    // which moves the anonymous tail.
    ctx.func_ty_for_instance(callee)?;
    let Some(fixed) = ctx.variadic_declarations.get(&callee).cloned() else {
        return Err(
            "[TCG-VARARG-ABI] the C-variadic callee's declaration recorded no fixed half to \
             judge the call against. Failing closed. Report this — it is a bridge lane defect."
                .into(),
        );
    };
    let (mut declared, mut arg_starts) = (fixed.params, fixed.arg_starts);
    for (offset, ty) in types.iter().copied().enumerate() {
        arg_starts.push((inputs.len() + offset, declared.len()));
        declared.push(rust_ty_to_trust_ir_ty(ctx.tcx, ty)?);
    }
    ctx.check_signature_placement(call_source, &declared, fixed.sret, &arg_starts)?;
    let (mut values, mut reloads) =
        lower_call_args_from_inputs(ctx, body, block, inputs, &args[..inputs.len()], (source, 0))?;
    // The anonymous tail against the CALL-SITE `FnAbi`, whose argument
    // `inputs.len() + offset` is anonymous argument `offset` (checked above to
    // be one direct scalar): every argument of a call is lowered against the
    // `FnAbi` entry that describes it.
    let (tail, tail_reloads) = lower_call_args_from_inputs(
        ctx,
        body,
        block,
        &types,
        anonymous,
        (call_source, inputs.len()),
    )?;
    values.extend(tail);
    reloads.extend(tail_reloads);
    Ok(Some((values, reloads)))
}
