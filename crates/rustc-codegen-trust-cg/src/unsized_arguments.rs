//! Unsized slice/str parameters use the caller's storage plus length metadata.
//! The MIR view is a mutable wide pointer: every original place gets a leading
//! dereference, so ordinary slice lowering addresses the same caller-owned bytes.

use super::*;
use rustc_middle::mir::visit::{MutVisitor, PlaceContext};
use std::borrow::Cow;

pub(super) fn plan<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    input: Ty<'tcx>,
    index: usize,
    source: RustcFnAbiSource<'tcx>,
) -> Result<bool, String> {
    // Admitted only where a differential against LLVM has run: AArch64 Linux
    // (`aarch64_c_fnabi_aggregate_linux`) and AArch64 macOS
    // (`unsized_arguments_aarch64`). Other Apple OSes share the Darwin
    // calling convention but nothing has executed there, so they stay refused.
    let os = &ctx.tcx.sess.target.os;
    if ctx.tcx.sess.target.arch.desc() != "aarch64"
        || !matches!(
            os,
            rustc_target::spec::Os::Linux | rustc_target::spec::Os::MacOs
        )
    {
        return Ok(false);
    }
    let input = ctx.normalize_ty(input);
    if !matches!(input.kind(), ty::Slice(_) | ty::Str) {
        return Ok(false);
    }
    let abi = source.query(ctx.tcx)?;
    let Some(arg) = abi.args.get(index) else {
        return Ok(false);
    };
    if ctx.normalize_ty(arg.layout.ty) != input {
        return Ok(false);
    }
    check_aggregate_abi_scope(ctx.tcx, abi)?;
    if abi.conv != rustc_abi::CanonAbi::Rust
        || arg.layout.is_sized()
        || !crate::indirect_abi::checked(&arg.mode)
            .map_err(|why| format!("[TCG-UNSIZED-ARG] argument {index} `{input:?}` uses {why}"))?
            .is_some_and(|view| {
                view.kind == crate::indirect_abi::Kind::Pointer && view.meta_attrs.is_some()
            })
    {
        return Err(format!(
            "[TCG-UNSIZED-ARG] argument {index} `{input:?}` lacks the Rust indirect data/metadata ABI"
        ));
    }
    // Destruction of an unsized owned payload needs its own drop loop; a view
    // alone must never make its destruction disappear.
    if input.needs_drop(ctx.tcx, ty::TypingEnv::fully_monomorphized()) {
        return Err(format!(
            "[TCG-UNSIZED-ARG] argument {index} `{input:?}` requires unsized payload destruction"
        ));
    }
    Ok(true)
}

pub(super) fn body<'a, 'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    original: &'a Body<'tcx>,
) -> Result<Cow<'a, Body<'tcx>>, String> {
    let mut arguments = HashSet::new();
    for local in original.args_iter() {
        if plan(
            ctx,
            ctx.monomorphize_ty(original.local_decls[local].ty),
            local.index() - 1,
            RustcFnAbiSource::Instance(ctx.instance),
        )? {
            arguments.insert(local);
        }
    }
    if arguments.is_empty() {
        return Ok(Cow::Borrowed(original));
    }
    struct Reborrow<'tcx> {
        tcx: TyCtxt<'tcx>,
        arguments: HashSet<Local>,
    }
    impl<'tcx> MutVisitor<'tcx> for Reborrow<'tcx> {
        fn tcx(&self) -> TyCtxt<'tcx> {
            self.tcx
        }
        fn visit_place(
            &mut self,
            place: &mut Place<'tcx>,
            context: PlaceContext,
            location: mir::Location,
        ) {
            self.super_place(place, context, location);
            if self.arguments.contains(&place.local) {
                let mut projection = Vec::with_capacity(place.projection.len() + 1);
                projection.push(ProjectionElem::Deref);
                projection.extend(place.projection.iter());
                place.projection = self.tcx.mk_place_elems(&projection);
            }
        }
    }
    let mut rewritten = original.clone();
    for &local in &arguments {
        // Keep generic field/element types in the body; the usual instance
        // substitution still occurs at every lowering query.
        let pointee = rewritten.local_decls[local].ty;
        rewritten.local_decls[local].ty =
            Ty::new_mut_ref(ctx.tcx, ctx.tcx.lifetimes.re_erased, pointee);
    }
    Reborrow {
        tcx: ctx.tcx,
        arguments,
    }
    .visit_body_preserves_cfg(&mut rewritten);
    Ok(Cow::Owned(rewritten))
}

pub(super) fn entry<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    arg: Local,
) -> Result<bool, String> {
    let view = ctx.normalize_ty(local_rust_ty(ctx, body, arg));
    let ty::Ref(_, pointee, rustc_hir::Mutability::Mut) = view.kind() else {
        return Ok(false);
    };
    if !plan(
        ctx,
        *pointee,
        arg.index() - 1,
        RustcFnAbiSource::Instance(ctx.instance),
    )? {
        return Ok(false);
    }
    let data = ValueId::new(arg.index() as u32);
    let len = ctx.fresh_value();
    block.params.push((data, TrustIrTy::Ptr));
    block.params.push((len, TrustIrTy::I64));
    store_fat_ptr_slot(ctx, block, arg, data, len)?;
    Ok(true)
}

pub(super) fn operand<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    value: &Operand<'tcx>,
    expected: Ty<'tcx>,
) -> Result<(ValueId, ValueId), String> {
    let (Operand::Copy(place) | Operand::Move(place)) = value else {
        return Err("[TCG-UNSIZED-ARG] operand is not an indirect place".into());
    };
    if !matches!(place.projection.as_ref(), [ProjectionElem::Deref])
        || ctx.normalize_ty(place_rust_ty(ctx, body, place)) != ctx.normalize_ty(expected)
    {
        return Err("[TCG-UNSIZED-ARG] operand has no matching whole indirect slice image".into());
    }
    // This is the same indirect-place transfer rustc's LLVM codegen performs
    // for PassMode::Indirect with metadata, including MIR Copy operands.
    scalarized_slice_reborrow_source_data_len(ctx, body, block, place.local)
        .ok_or_else(|| "[TCG-UNSIZED-ARG] operand has no complete data/length pair".into())
}
