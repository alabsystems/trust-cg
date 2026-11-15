//! `extern "rust-call"` callables, untupled exactly as rustc's own ABI sees them.
//!
//! rustc's `FnAbi` for an `extern "rust-call"` signature UNTUPLES its last input
//! (`rustc_ty_utils::abi::fn_abi_new_uncached`, which `fn_sig_for_fn_abi` feeds
//! for instances and `fn_abi_of_fn_ptr` for `fn` pointers): every element of the
//! argument tuple is its own argument, with its own `PassMode`. That covers every
//! `Fn*` call shim (`FnPtrShim`, `ClosureOnceShim`, a `VTableShim`), every `Fn*`
//! impl method (`<&F as Fn<A>>::call`, `<Box<F> as FnOnce<A>>::call_once`), a
//! `rust-call` trait method reached through a vtable, and a user
//! `extern "rust-call" fn`. A closure BODY is not this shape: MIR building gives
//! it the plain Rust ABI with its arguments already untupled (`func_ty_for_instance`
//! declares it that way).
//!
//! The MIR body of such a callable keeps the tuple as ONE argument local,
//! `Body::spread_arg`, and `rustc_codegen_ssa` rebuilds it at function entry by
//! storing each incoming element into the tuple's field.
//!
//! This module states that rule ONCE for the bridge, and every side reads it:
//!
//! * [`abi_inputs`]: a signature's inputs as its `FnAbi` lists them. The
//!   declaration (`func_ty_for_instance`), the `fn`-pointer lane, and every call
//!   site that spreads a tuple operand (`lower_direct_call_args`,
//!   `lower_indirect_call_terminator`, the virtual lane, through
//!   `spread_fn_call_tuple_untupled`) take their argument list from it.
//! * [`body`]: the body rewritten so that its argument locals ARE those inputs,
//!   with the tuple rebuilt from them at entry, as `rustc_codegen_ssa` rebuilds
//!   it. The entry block then needs no tuple-specific code: each element is an
//!   ordinary argument at its own `FnAbi` index (`rustc_fn_abi_arg_index_for_mir_arg`)
//!   and takes whichever lane its mode asks for (pair, narrow cast, a pointer to a
//!   copy, a whole slot, a scalar).
//!
//! Before this, the bridge declared such a callable TUPLED (one parameter for
//! the tuple) and refused it by name wherever code another backend compiled could
//! reach it: shared by symbol (`-Zshare-generics`, an exported or upstream item),
//! or through an address (a vtable slot, a `fn` pointer). MEASURED then
//! (2026-09-28): a bridge rlib's exported `<Box<dyn Fn(u64, u64, u64)> as
//! Fn<..>>::call` read the three `u64` from a 24-byte stack copy while an LLVM
//! caller passed them in RSI / RDX / RCX (oracle 231, 40 or 194).

use super::*;
use rustc_middle::mir::visit::{MutVisitor, PlaceContext};
use std::borrow::Cow;

/// `sig`'s inputs as rustc's `FnAbi` lists its arguments: unchanged, except
/// that an `extern "rust-call"` signature's last input — its argument tuple — is
/// replaced by the tuple's elements, in order. A `rust-call` signature whose
/// last input is not a tuple is refused (rustc's own ABI computation treats it
/// as a compiler bug).
pub(super) fn abi_inputs<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig: &ty::FnSig<'tcx>,
) -> Result<Vec<Ty<'tcx>>, String> {
    let inputs = sig.inputs();
    if sig.abi() != rustc_abi::ExternAbi::RustCall {
        return Ok(inputs.to_vec());
    }
    let Some((&tuple, leading)) = inputs.split_last() else {
        return Err(
            "[TCG-ARG-ABI] an `extern \"rust-call\"` signature has no argument tuple; \
             failing closed"
                .to_owned(),
        );
    };
    let tuple = tcx.normalize_erasing_regions(
        ty::TypingEnv::fully_monomorphized(),
        ty::Unnormalized::new_wip(tuple),
    );
    let ty::Tuple(elems) = tuple.kind() else {
        return Err(format!(
            "[TCG-ARG-ABI] the last input of an `extern \"rust-call\"` signature is `{tuple:?}`, \
             not a tuple; rustc's ABI untuples only a tuple, so failing closed"
        ));
    };
    let mut untupled = Vec::with_capacity(leading.len() + elems.len());
    untupled.extend_from_slice(leading);
    untupled.extend(elems.iter());
    Ok(untupled)
}

/// Whether `instance`'s callable is declared from an `extern "rust-call"`
/// `fn` signature — the shape whose `FnAbi` [`abi_inputs`] untuples and whose
/// MIR body carries a `spread_arg`. A closure body is `ty::Closure` and never
/// this shape.
pub(super) fn instance_is_rust_call_fn<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>) -> bool {
    let instance_ty = instance.ty(tcx, ty::TypingEnv::fully_monomorphized());
    matches!(instance_ty.kind(), ty::FnDef(..))
        && instance_ty.fn_sig(tcx).abi() == rustc_abi::ExternAbi::RustCall
}

/// `original` with its `spread_arg` untupled (see the module doc), or `original`
/// itself when it has none.
///
/// For a body with arguments `_1 ..= _k` whose LAST argument `_k` is the spread
/// tuple of `n` elements, the rewritten body has arguments `_1 ..= _{k-1}`
/// unchanged, then `_k ..= _{k+n-1}` — one per element, of the element's
/// (instance-substituted) type — and every local the original numbered `_k` or
/// above is renumbered `+ n`, so the tuple itself becomes the ordinary local
/// `_{k+n}`. Its first statement is `_{k+n} = (move _k, .., move _{k+n-1})`,
/// executed once on entry: prepended to the start block when nothing branches
/// back to it, otherwise in a new start block that falls through to the
/// original one.
///
/// SOUNDNESS. The tuple holds exactly the values rustc's codegen stores into it
/// (`rustc_codegen_ssa`'s `spread_arg` arm writes each incoming argument into
/// the tuple's field `i`; the aggregate writes the same values into the same
/// fields), before any other statement runs. Every other local keeps its type,
/// declaration and every use, under a renumbering applied uniformly to the
/// whole body (places, `Index` projections, debug info). Nothing else changes.
///
/// The body and the declaration must agree on the shape: `instance` is a
/// `rust-call` `fn` ([`instance_is_rust_call_fn`]) exactly when its body has a
/// `spread_arg`, and the spread local is the last argument. Anything else is
/// refused by name rather than lowered in two conventions.
pub(super) fn body<'a, 'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    original: &'a Body<'tcx>,
) -> Result<Cow<'a, Body<'tcx>>, String> {
    let tcx = ctx.tcx;
    let declared_rust_call = instance_is_rust_call_fn(tcx, ctx.instance);
    let Some(spread) = original.spread_arg else {
        if declared_rust_call {
            return Err(format!(
                "[TCG-ARG-ABI] `{}` is an `extern \"rust-call\"` callable, which the bridge \
                 declares untupled as rustc does, but its MIR body has no spread argument to \
                 rebuild the tuple into; failing closed rather than binding the elements to \
                 the wrong locals",
                tcx.symbol_name(ctx.instance).name
            ));
        }
        return Ok(Cow::Borrowed(original));
    };
    let refuse = |why: String| -> String {
        format!(
            "[TCG-ARG-ABI] `{}`: the MIR body spreads argument `{spread:?}`, {why}; failing \
             closed rather than declaring the elements and binding the body another way",
            tcx.symbol_name(ctx.instance).name
        )
    };
    if !declared_rust_call {
        return Err(refuse(
            "but the callable is not an `extern \"rust-call\"` `fn`, so its declaration \
             keeps the tuple as one parameter"
                .to_owned(),
        ));
    }
    let k = spread.index();
    if original.arg_count == 0 || k != original.arg_count {
        return Err(refuse(format!(
            "which is not its last argument (argument count {})",
            original.arg_count
        )));
    }
    if original.coroutine.is_some() {
        return Err(refuse("and it is a coroutine body".to_owned()));
    }
    let tuple_ty = ctx.normalize_ty(ctx.monomorphize_ty(original.local_decls[spread].ty));
    let ty::Tuple(elems) = tuple_ty.kind() else {
        return Err(refuse(format!("whose type `{tuple_ty:?}` is not a tuple")));
    };
    let n = elems.len();
    let span = original.local_decls[spread].source_info.span;

    let mut rewritten = original.clone();
    struct Shift<'tcx> {
        tcx: TyCtxt<'tcx>,
        from: usize,
        by: usize,
    }
    impl<'tcx> MutVisitor<'tcx> for Shift<'tcx> {
        fn tcx(&self) -> TyCtxt<'tcx> {
            self.tcx
        }
        fn visit_local(&mut self, local: &mut Local, _: PlaceContext, _: mir::Location) {
            if local.index() >= self.from {
                *local = Local::new(local.index() + self.by);
            }
        }
    }
    if n > 0 {
        Shift {
            tcx,
            from: k,
            by: n,
        }
        .visit_body_preserves_cfg(&mut rewritten);
    }
    let mut local_decls = IndexVec::with_capacity(original.local_decls.len() + n);
    for (local, decl) in original.local_decls.iter_enumerated() {
        if local == spread {
            for elem in elems.iter() {
                local_decls.push(mir::LocalDecl::new(elem, span));
            }
        }
        local_decls.push(decl.clone());
    }
    rewritten.local_decls = local_decls;
    rewritten.arg_count = k - 1 + n;
    rewritten.spread_arg = None;

    let tuple_local = Local::new(k + n);
    let operands: IndexVec<FieldIdx, Operand<'tcx>> = (0..n)
        .map(|i| Operand::Move(Place::from(Local::new(k + i))))
        .collect();
    let source_info = mir::SourceInfo::outermost(original.span);
    let assemble = mir::Statement::new(
        source_info,
        StatementKind::Assign(Box::new((
            Place::from(tuple_local),
            Rvalue::Aggregate(Box::new(mir::AggregateKind::Tuple), operands),
        ))),
    );
    let start_has_predecessors = !original.basic_blocks.predecessors()[mir::START_BLOCK].is_empty();
    if start_has_predecessors {
        // Keep the complete original entry (including loop hints) in the moved
        // block. Only the fresh assembly connector starts with empty attributes.
        crate::entry_connector::move_start(&mut rewritten, assemble);
    } else {
        rewritten.basic_blocks_mut()[mir::START_BLOCK]
            .statements
            .insert(0, assemble);
    }
    Ok(Cow::Owned(rewritten))
}
