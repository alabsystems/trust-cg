// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! The failure edge of an INTERCEPTED std call, raised through std's own panic.
//!
//! An interception replaces a std function's body with the bridge's lowering,
//! including the precondition check that body performs. When that check fails,
//! std's body panics through its own route: a never-returning helper given the
//! offending values (`slice_index_fail(start, end, len)`, `Vec::insert`'s
//! `assert_failed(index, len)`), a MIR assertion (`panic_bounds_check(index,
//! len)`, an overflow `panic_const_*`), or a `panic!` / `assert!` / `expect`
//! whose message is a constant. A panic hook observes that route: the payload's
//! text AND type (`&'static str` for a literal message, `String` for a formatted
//! one), and the `#[track_caller]` Location, which is the intercepted call's own
//! Location only when every frame between it and the panic is
//! `#[track_caller]`; otherwise it is a span inside std.
//!
//! The route is derived from std's own MIR, never from a copied message, symbol
//! or line number. The optimized MIR of the intercepted callee, and of the
//! callees it reaches to a bounded depth, is searched for panic sites of the
//! class the bridge's failing check stands for. Each site's Location is resolved
//! by rustc's own `Body::caller_location_span` walk, frame by frame, as
//! rustc_codegen_ssa resolves it at every call it emits. The shallowest sites of
//! that class must agree on the entry and the Location (and on the constant
//! payload, where std's payload is constant). The failure block then calls that
//! entry, as rustc codegens it, with the bridge's runtime payload and that
//! Location, honoring the intercepted call's unwind edge with the entry's actual
//! `FnAbi` unwind permission. A route not derived uniquely is refused by name
//! (`[TCG-STD-PANIC-ROUTE]`); nothing here synthesizes a message or substitutes
//! a trap for a hook, except under `panic=immediate-abort`, whose real entries
//! are `intrinsics::abort()` and run no hook.
//!
//! Two narrower entries share that call. `StdFailure::OverflowAt` takes an
//! overflow assertion its caller already identified in std's MIR, with the
//! Location rustc's walk gives it there, instead of searching: core's
//! `Sum` / `Product` closure, whose check the bridge's reduction step stands
//! for (`std_reduction_overflow_span`). `raise_parts` returns the entry call
//! without emitting it, for a failure edge whose unwind the caller routes
//! through a pad of its own (`Vec::insert` dropping the moved-in element).
//!
//! EVIDENCE BOUNDARY. A site is identified by its class, the helper's name and
//! signature, the shape of the arguments std passes (a constant, or a value
//! read out of a `Bound` variant), and its call depth — not by proving that
//! its guard is the bridge's failing condition. That the shallowest agreeing
//! site IS std's route for each interception is measured, per shape, against
//! LLVM's binary on the pinned std (`tests/std_panic_payload_differential.rs`);
//! a std whose MIR no longer yields a unique site refuses rather than guesses.
//!
//! A constant-payload site is the weakest identification (any `panic!` literal
//! or `expect` message qualifies), and the search descends through every call
//! that returns, so it can reach a check std's failing path never runs: a
//! `-Cdebug-assertions` precondition check below the call that actually fails.
//! A constant route is therefore refused whenever a panic site of ANOTHER class
//! (a diverging call it does not match, or a MIR assertion) sits at a
//! SHALLOWER depth than the chosen site: that site, not the constant one, may
//! be the failure the bridge's check stands for. A site of another class at the
//! SAME depth does not refuse it: in one frame, `chunks_exact`'s
//! `assert!(chunk_size != 0)` precedes the inlined `len % chunk_size` assertion
//! it makes unreachable; which of two sites at one depth fails first is
//! measured per shape, like the rest.

use crate::lang_items::LangItem;
use rustc_middle::mir::interpret::{AllocId, GlobalAlloc};
use rustc_span::Span;
use rustc_target::callconv::PassMode;

use super::{
    Block, BlockId, Body, ConstValue, DirectCallTerminator, FuncId, Inst, Instance, InstrNode,
    MirLoweringCtx, Operand, RustcFnAbiSource, TerminatorKind, TrustIrTy, Ty, TyCtxt, ValueId,
    caller_location_for_call, decode_pure_literal_fmt_arguments, emit_caller_location_const_as,
    emit_const_alloc_addr, emit_diverging_panic_call, emit_i64_const, is_real_std_crate_def, mir,
    pointer_casts, resolve_call_callee, ty,
};

/// How many call levels below the intercepted callee are searched.
const MAX_DEPTH: usize = 6;
/// How many distinct frames one search may read before it refuses.
const MAX_FRAMES: usize = 192;

/// What the bridge's failing check stands for in std's body, with the runtime
/// values the bridge holds for its payload.
pub(super) enum StdFailure<'tcx> {
    /// std calls the never-returning helper `name` with exactly `payload`
    /// (its parameter types, in order).
    Helper {
        name: &'static str,
        payload: Vec<Payload<'tcx>>,
    },
    /// A MIR bounds check `index < len` fails: `panic_bounds_check(index, len)`.
    BoundsCheck { index: ValueId, len: ValueId },
    /// A MIR overflow assertion of `op` fails: its `panic_const_*` entry.
    Overflow(mir::BinOp),
    /// The MIR overflow assertion of `op` that the caller identified in std's
    /// MIR fails, and `span` is the span rustc's `caller_location_span` walk
    /// gives it there: its `panic_const_*` entry with that Location, and no
    /// search. Only for a check in std code the bridge models in place of a
    /// body it does not lower, where the search from the intercepted call can
    /// meet other assertions of the same class first: core's
    /// `#[rustc_inherit_overflow_checks] |a, b| a + b` (`a * b`) closure of the
    /// `Sum` / `Product` impl rustc selects (`std_reduction_overflow_span`).
    OverflowAt { op: mir::BinOp, span: Span },
    /// std raises a panic whose whole payload is constant in its MIR:
    /// `panic(const)`, `panic_fmt` of a pure literal, or a never-returning
    /// helper given only constant `&str` arguments (`Option::expect`'s
    /// `expect_failed(msg)`).
    Constant,
}

/// One argument of a helper's payload, and what the matching std site must
/// pass in that position. A helper std calls from several sites (one per
/// failing condition, each with its own Location) is told apart by the shape of
/// the argument std passes there; a payload that matches no site, or sites that
/// disagree, is refused.
pub(super) enum Payload<'tcx> {
    /// A scalar of Rust type `ty` (an integer lane); std's operand is any.
    Scalar(ValueId, Ty<'tcx>),
    /// A scalar std passes as this CONSTANT at the failing site (`0` for the
    /// start of `slice_index_fail(0, end, len)`).
    Constant(u128, Ty<'tcx>),
    /// A scalar std reads out of a `core::ops::Bound` it matched as the variant
    /// named `variant` (`Included` / `Excluded`) at the failing site: the
    /// variant the intercepted range type's `RangeBounds` impl returns.
    Bound(ValueId, Ty<'tcx>, &'static str),
    /// A `&str` as its data pointer and byte length; std's operand is any.
    Str { data: ValueId, len: ValueId },
}

impl<'tcx> Payload<'tcx> {
    fn rust_ty(&self, tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
        match self {
            Payload::Scalar(_, ty) | Payload::Constant(_, ty) | Payload::Bound(_, ty, _) => *ty,
            Payload::Str { .. } => str_ref_ty(tcx),
        }
    }

    /// Whether std's `operand`, in `body`, is the argument this payload stands
    /// for.
    fn matches(
        &self,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        block: mir::BasicBlock,
        operand: &Operand<'tcx>,
    ) -> bool {
        match self {
            Payload::Scalar(..) | Payload::Str { .. } => true,
            Payload::Constant(value, _) => {
                let Operand::Constant(constant) = operand else {
                    return false;
                };
                constant
                    .const_
                    .try_eval_bits(tcx, ty::TypingEnv::fully_monomorphized())
                    == Some(*value)
            }
            Payload::Bound(_, _, variant) => downcast_variant(tcx, body, block, operand)
                .is_some_and(|name| name.as_str() == *variant),
        }
    }
}

fn str_ref_ty(tcx: TyCtxt<'_>) -> Ty<'_> {
    Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, tcx.types.str_)
}

/// Where a panic site takes its `#[track_caller]` Location from, relative to
/// the frame that holds it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Loc {
    /// The Location this frame was itself called with.
    Caller,
    /// The Location of a span: an untracked frame's own call site.
    Span(Span),
}

/// A panic site of the wanted class.
#[derive(Clone, PartialEq, Debug)]
struct Site<'tcx> {
    /// The entry to call; `None` for a MIR assertion (its entry is the kind's).
    entry: Option<Instance<'tcx>>,
    /// The constant `&str` payload, for `StdFailure::Constant`.
    strings: Vec<Vec<u8>>,
    /// The Location the entry receives (meaningful only when it is tracked).
    location: Loc,
    /// Call levels below the intercepted callee.
    depth: usize,
}

/// The class of site one search looks for.
enum Want<'a, 'tcx> {
    Helper {
        name: &'static str,
        payload: &'a [Payload<'tcx>],
    },
    BoundsCheck,
    Overflow(mir::BinOp),
    Constant,
}

struct Search<'a, 'tcx> {
    ctx: &'a MirLoweringCtx<'tcx>,
    want: Want<'a, 'tcx>,
    frames: usize,
    stack: Vec<Instance<'tcx>>,
    /// Whether the depth bound cut a call off unread: then a missing site is
    /// not evidence that std has none ([`has_site`]).
    truncated: bool,
    /// The shallowest panic site of ANOTHER class the search met — a
    /// never-returning call that is not of the wanted class, or a MIR assertion
    /// that is not — as its depth and what it is (module docs).
    other: Option<(usize, String)>,
}

impl<'tcx> Search<'_, 'tcx> {
    /// Record a panic site of another class at `depth`.
    fn note_other(&mut self, depth: usize, what: impl FnOnce() -> String) {
        if self.other.as_ref().is_none_or(|(at, _)| depth < *at) {
            self.other = Some((depth, what()));
        }
    }

    /// Collect the wanted sites reachable from `instance`, with Locations
    /// relative to `instance`. `strings` binds each parameter of `instance` to a
    /// constant `&str` argument its caller passed, when it passed one.
    fn frame(
        &mut self,
        instance: Instance<'tcx>,
        depth: usize,
        strings: &[Option<Vec<u8>>],
    ) -> Result<Vec<Site<'tcx>>, String> {
        let tcx = self.ctx.tcx;
        let ty::InstanceKind::Item(def_id) = instance.def else {
            return Ok(Vec::new());
        };
        if !tcx.is_mir_available(def_id) || self.stack.contains(&instance) {
            return Ok(Vec::new());
        }
        self.frames += 1;
        if self.frames > MAX_FRAMES {
            return Err(format!(
                "the search read more than {MAX_FRAMES} frames below the intercepted call"
            ));
        }
        let generic = tcx.instance_mir(instance.def);
        let body: Body<'tcx> = instance.instantiate_mir_and_normalize_erasing_regions(
            tcx,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(tcx, generic.clone()),
        );
        let tracked = instance.def.requires_caller_location(tcx);
        let inherited = tracked.then_some(Loc::Caller);
        self.stack.push(instance);
        let mut sites = Vec::new();
        for (block, data) in body.basic_blocks.iter_enumerated() {
            if data.is_cleanup {
                continue;
            }
            let Some(terminator) = &data.terminator else {
                continue;
            };
            match &terminator.kind {
                TerminatorKind::Assert { msg, .. } => {
                    let wanted = match (&self.want, &**msg) {
                        (Want::BoundsCheck, mir::AssertKind::BoundsCheck { .. }) => true,
                        (Want::Overflow(op), mir::AssertKind::Overflow(found, _, _)) => op == found,
                        _ => false,
                    };
                    if wanted {
                        sites.push(Site {
                            entry: None,
                            strings: Vec::new(),
                            location: body.caller_location_span(
                                terminator.source_info,
                                inherited,
                                tcx,
                                Loc::Span,
                            ),
                            depth,
                        });
                    } else {
                        self.note_other(depth, || {
                            format!("a MIR `{msg:?}` assertion in {instance:?}")
                        });
                    }
                }
                TerminatorKind::Call {
                    func,
                    args,
                    target,
                    fn_span,
                    ..
                } => {
                    let Some(callee) = resolve_mono_callee(tcx, func) else {
                        if target.is_none() {
                            self.note_other(depth, || {
                                format!("a never-returning call through {func:?} in {instance:?}")
                            });
                        }
                        continue;
                    };
                    let site_info = mir::SourceInfo {
                        span: *fn_span,
                        scope: terminator.source_info.scope,
                    };
                    let location = body.caller_location_span(site_info, inherited, tcx, Loc::Span);
                    let arg_strings: Vec<Option<Vec<u8>>> = args
                        .iter()
                        .map(|arg| self.const_str(&body, &arg.node, strings))
                        .collect();
                    if target.is_none() {
                        if let Some(site) = self.diverging_site(
                            &body,
                            block,
                            callee,
                            args,
                            &arg_strings,
                            location,
                            depth,
                        )? {
                            sites.push(site);
                        } else {
                            self.note_other(depth, || {
                                format!("a never-returning call to {callee:?} in {instance:?}")
                            });
                        }
                        continue;
                    }
                    if depth >= MAX_DEPTH {
                        self.truncated = true;
                        continue;
                    }
                    let callee_tracked = callee.def.requires_caller_location(tcx);
                    for mut site in self.frame(callee, depth + 1, &arg_strings)? {
                        // A site inheriting its Location from the callee
                        // receives what this call passes the callee.
                        if site.location == Loc::Caller {
                            if !callee_tracked {
                                continue;
                            }
                            site.location = location;
                        }
                        sites.push(site);
                    }
                }
                _ => {}
            }
        }
        self.stack.pop();
        Ok(sites)
    }

    /// Classify a never-returning call against the wanted class.
    #[allow(clippy::too_many_arguments)]
    fn diverging_site(
        &self,
        body: &Body<'tcx>,
        block: mir::BasicBlock,
        callee: Instance<'tcx>,
        args: &[rustc_span::Spanned<Operand<'tcx>>],
        arg_strings: &[Option<Vec<u8>>],
        location: Loc,
        depth: usize,
    ) -> Result<Option<Site<'tcx>>, String> {
        let tcx = self.ctx.tcx;
        let def_id = callee.def_id();
        let lang = tcx.lang_items();
        match &self.want {
            Want::Helper { name, payload } => {
                if !is_real_std_crate_def(tcx, def_id)
                    || tcx
                        .opt_item_name(def_id)
                        .is_none_or(|item| item.as_str() != *name)
                    || args.len() != payload.len()
                {
                    return Ok(None);
                }
                let signature = callee_signature(tcx, callee);
                let inputs: Vec<Ty<'tcx>> = payload.iter().map(|arg| arg.rust_ty(tcx)).collect();
                if signature.inputs() != inputs.as_slice() || !signature.output().is_never() {
                    return Ok(None);
                }
                if !payload
                    .iter()
                    .zip(args)
                    .all(|(expected, arg)| expected.matches(tcx, body, block, &arg.node))
                {
                    return Ok(None);
                }
                Ok(Some(Site {
                    entry: Some(callee),
                    strings: Vec::new(),
                    location,
                    depth,
                }))
            }
            Want::Constant => {
                // `panic!("literal")` / `assert!(c, "literal")`: `panic` is
                // `panic_fmt(Arguments::from_str(expr))`, so `panic(literal)`
                // with the same Location is the very call.
                if Some(def_id) == lang.panic_fmt() && args.len() == 1 {
                    let Some(local) = operand_local(&args[0].node) else {
                        return Ok(None);
                    };
                    let Some(text) = decode_pure_literal_fmt_arguments(self.ctx, body, local)
                    else {
                        return Ok(None);
                    };
                    let panic = lang
                        .panic_fn()
                        .ok_or_else(|| "missing actual `panic` lang item".to_owned())?;
                    return Ok(Some(Site {
                        entry: Some(Instance::mono(tcx, panic)),
                        strings: vec![text],
                        location,
                        depth,
                    }));
                }
                if !is_real_std_crate_def(tcx, def_id) || args.is_empty() {
                    return Ok(None);
                }
                let signature = callee_signature(tcx, callee);
                let str_ref = str_ref_ty(tcx);
                if !signature.output().is_never()
                    || signature.inputs().iter().any(|input| *input != str_ref)
                {
                    return Ok(None);
                }
                let Some(strings) = arg_strings.iter().cloned().collect::<Option<Vec<_>>>() else {
                    return Ok(None);
                };
                Ok(Some(Site {
                    entry: Some(callee),
                    strings,
                    location,
                    depth,
                }))
            }
            Want::BoundsCheck | Want::Overflow(_) => Ok(None),
        }
    }

    /// The bytes of a constant `&str` operand: a literal, or a parameter of
    /// this frame its caller bound to one. A parameter the body reassigns is
    /// not bound.
    fn const_str(
        &self,
        body: &Body<'tcx>,
        operand: &Operand<'tcx>,
        strings: &[Option<Vec<u8>>],
    ) -> Option<Vec<u8>> {
        match operand {
            Operand::Constant(constant) => const_str_bytes(self.ctx, constant),
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                let index = place.local.as_usize();
                if index == 0 || index > body.arg_count || local_is_reassigned(body, place.local) {
                    return None;
                }
                strings.get(index - 1).cloned().flatten()
            }
            _ => None,
        }
    }
}

/// The name of the enum variant whose payload `operand`, at the end of
/// `block`'s statements, reads: the `Downcast` in the operand's place, or in
/// the place its local was last copied from (`reaching_copy`), followed through
/// whole-local copies.
fn downcast_variant<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    block: mir::BasicBlock,
    operand: &Operand<'tcx>,
) -> Option<rustc_span::Symbol> {
    let (Operand::Copy(place) | Operand::Move(place)) = operand else {
        return None;
    };
    let mut place = *place;
    let mut at = (block, body.basic_blocks[block].statements.len());
    for _ in 0..16 {
        for (index, elem) in place.projection.iter().enumerate() {
            if let mir::ProjectionElem::Downcast(_, variant) = elem {
                let base =
                    mir::Place::ty_from(place.local, &place.projection[..index], body, tcx).ty;
                let ty::Adt(adt, _) = base.kind() else {
                    return None;
                };
                return Some(adt.variant(variant).name);
            }
        }
        if !place.projection.is_empty() {
            return None;
        }
        let (source, from) = reaching_copy(body, at, place.local)?;
        place = source;
        at = from;
    }
    None
}

/// The place `local` holds a copy of at `(block, statement)`: its last
/// whole-local assignment before that point, found within `block` and then up
/// a chain of single-predecessor blocks, when that assignment is a plain
/// `copy`/`move` of a place. `None` when the definition is anything else, is
/// not unique along the walk (a join), or `local` may be written through a
/// borrow or a call.
fn reaching_copy<'tcx>(
    body: &Body<'tcx>,
    (mut block, mut end): (mir::BasicBlock, usize),
    local: mir::Local,
) -> Option<(mir::Place<'tcx>, (mir::BasicBlock, usize))> {
    let borrowed = body.basic_blocks.iter().any(|data| {
        data.statements.iter().any(|statement| {
            matches!(&statement.kind, mir::StatementKind::Assign(assign)
                if matches!(&assign.1,
                    mir::Rvalue::Ref(_, _, place) | mir::Rvalue::RawPtr(_, place)
                        if place.local == local))
        })
    });
    if borrowed || local.as_usize() <= body.arg_count {
        return None;
    }
    let predecessors = body.basic_blocks.predecessors();
    for _ in 0..64 {
        let data = &body.basic_blocks[block];
        for index in (0..end).rev() {
            match &data.statements[index].kind {
                mir::StatementKind::Assign(assign) if assign.0.local == local => {
                    if !assign.0.projection.is_empty() {
                        return None;
                    }
                    return match &assign.1 {
                        mir::Rvalue::Use(Operand::Copy(source) | Operand::Move(source), _) => {
                            Some((*source, (block, index)))
                        }
                        _ => None,
                    };
                }
                mir::StatementKind::SetDiscriminant { place, .. } if place.local == local => {
                    return None;
                }
                _ => {}
            }
        }
        let [predecessor] = predecessors[block].as_slice() else {
            return None;
        };
        if body.basic_blocks[*predecessor]
            .terminator
            .as_ref()
            .is_some_and(|terminator| {
                matches!(&terminator.kind, TerminatorKind::Call { destination, .. }
                    if destination.local == local)
            })
        {
            return None;
        }
        block = *predecessor;
        end = body.basic_blocks[block].statements.len();
    }
    None
}

/// Resolve a monomorphic MIR call operand to its callee instance.
fn resolve_mono_callee<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>) -> Option<Instance<'tcx>> {
    let Operand::Constant(constant) = func else {
        return None;
    };
    let item = crate::fn_items::view(constant.const_.ty().kind())?;
    let def_id = item.def_id();
    let args = item.unbound_args()?;
    Instance::try_resolve(tcx, ty::TypingEnv::fully_monomorphized(), def_id, args)
        .ok()
        .flatten()
}

/// The callee's monomorphic signature with every region erased, so a
/// `&'static str` parameter compares equal to the payload's `&str`.
fn callee_signature<'tcx>(tcx: TyCtxt<'tcx>, callee: Instance<'tcx>) -> ty::FnSig<'tcx> {
    let callee_ty = callee.ty(tcx, ty::TypingEnv::fully_monomorphized());
    tcx.erase_and_anonymize_regions(
        tcx.instantiate_bound_regions_with_erased(callee_ty.fn_sig(tcx)),
    )
}

fn operand_local(operand: &Operand<'_>) -> Option<mir::Local> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            Some(place.local)
        }
        _ => None,
    }
}

/// Whether any statement or call writes `local` as a whole or in part.
fn local_is_reassigned(body: &Body<'_>, local: mir::Local) -> bool {
    body.basic_blocks.iter().any(|data| {
        data.statements
            .iter()
            .any(|statement| match &statement.kind {
                mir::StatementKind::Assign(assign) => assign.0.local == local,
                mir::StatementKind::SetDiscriminant { place, .. } => place.local == local,
                _ => false,
            })
            || data.terminator.as_ref().is_some_and(|terminator| {
                matches!(&terminator.kind, TerminatorKind::Call { destination, .. }
                if destination.local == local)
            })
    })
}

/// The provenance-free bytes of a constant `&str`.
fn const_str_bytes<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    constant: &mir::ConstOperand<'tcx>,
) -> Option<Vec<u8>> {
    let tcx = ctx.tcx;
    if !matches!(constant.const_.ty().kind(), ty::Ref(_, inner, _) if inner.is_str()) {
        return None;
    }
    let mir::Const::Val(ConstValue::Slice { alloc_id, meta }, _) = ctx.eval_const_operand(constant)
    else {
        return None;
    };
    alloc_bytes(tcx, alloc_id, meta)
}

fn alloc_bytes(tcx: TyCtxt<'_>, alloc_id: AllocId, len: u64) -> Option<Vec<u8>> {
    let GlobalAlloc::Memory(allocation) = tcx.try_get_global_alloc(alloc_id)? else {
        return None;
    };
    let allocation = allocation.inner();
    let len = usize::try_from(len).ok()?;
    if !allocation.provenance().ptrs().is_empty() || len > allocation.len() {
        return None;
    }
    Some(
        allocation
            .inspect_with_uninit_and_ptr_outside_interpreter(0..len)
            .to_vec(),
    )
}

/// Whether this session's real panic entries are `intrinsics::abort()`, which
/// run no hook (`panic=immediate-abort`): the one strategy whose failure edge
/// keeps the trap.
fn raises_no_hook(tcx: TyCtxt<'_>) -> bool {
    matches!(
        tcx.sess.panic_strategy(),
        rustc_target::spec::PanicStrategy::ImmediateAbort
    )
}

/// The FAILURE target of an intercepted call whose check stands for
/// `failure`: a block raising std's own panic for it (module docs).
pub(super) fn fail_target<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    call: &DirectCallTerminator<'_, 'tcx>,
    failure: StdFailure<'tcx>,
) -> Result<BlockId, String> {
    if raises_no_hook(ctx.tcx) || super::panic_edge_traps(ctx.tcx, call.unwind) {
        // The real entries are `intrinsics::abort()` and run no hook; or the
        // edge is one this target's call lowering cannot keep.
        return Ok(ctx.assert_trap_block(body));
    }
    let raise_id = ctx.fresh_block_id();
    let mut raise = Block::new(raise_id);
    let Some((callee, arguments, can_unwind)) = raise_parts(ctx, body, &mut raise, call, failure)?
    else {
        return Ok(ctx.assert_trap_block(body));
    };
    emit_diverging_panic_call(ctx, &mut raise, callee, arguments, call.unwind, can_unwind)
        .map_err(|why| refusal(ctx, call, &why))?;
    ctx.extra_blocks.push(raise);
    Ok(raise_id)
}

/// The `[TCG-STD-PANIC-ROUTE]` refusal of the intercepted `call`'s route.
fn refusal<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    call: &DirectCallTerminator<'_, 'tcx>,
    why: &str,
) -> String {
    let root = resolve_call_callee(ctx, call.func);
    format!(
        "[TCG-STD-PANIC-ROUTE] intercepted call to {root:?} at {:?}: {why}; no synthesized \
         message, Location or trap substitution",
        call.fn_span
    )
}

/// Whether std's MIR under the intercepted `call` may hold a panic site for
/// `failure`: false only when the complete search finds none. An edge std
/// itself never checks is not built rather than refused: the slice iterator's
/// `position` override counts with a plain `+= 1` in a std built without
/// overflow checks, so it wraps where core's default `position`
/// (`#[rustc_inherit_overflow_checks]`) panics. A site the search meets in
/// the user's predicate (an overflow-checked `+`) still counts, and the
/// route then refuses as before.
pub(super) fn has_site<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    call: &DirectCallTerminator<'_, 'tcx>,
    failure: &StdFailure<'tcx>,
) -> Result<bool, String> {
    let want = match failure {
        StdFailure::Helper { name, payload } => Want::Helper {
            name: *name,
            payload,
        },
        StdFailure::BoundsCheck { .. } => Want::BoundsCheck,
        StdFailure::Overflow(op) => Want::Overflow(*op),
        StdFailure::OverflowAt { .. } => return Ok(true),
        StdFailure::Constant => Want::Constant,
    };
    let root = resolve_call_callee(ctx, call.func)
        .ok_or_else(|| refusal(ctx, call, "the callee does not resolve to an instance"))?;
    let mut search = Search {
        ctx,
        want,
        frames: 0,
        stack: Vec::new(),
        truncated: false,
        other: None,
    };
    let sites = search
        .frame(root, 0, &[])
        .map_err(|why| refusal(ctx, call, &why))?;
    // A search the depth bound cut short cannot show that std never checks;
    // the route then searches again and refuses as before.
    Ok(!sites.is_empty() || search.truncated)
}

/// The callee, arguments (emitted into `block`) and actual `FnAbi` unwind
/// permission of std's own panic for `failure` at the intercepted `call`: the
/// call `fail_target` emits, for a failure edge whose unwind the caller routes
/// itself (`Vec::insert`'s model-owned pad that drops the moved-in element,
/// `insert_fail_target_dropping_element`). `None` under
/// `panic=immediate-abort`, whose real entries run no hook: the caller keeps
/// the trap there, as `fail_target` does.
pub(super) fn raise_parts<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    call: &DirectCallTerminator<'_, 'tcx>,
    failure: StdFailure<'tcx>,
) -> Result<Option<(FuncId, Vec<ValueId>, bool)>, String> {
    if raises_no_hook(ctx.tcx) {
        return Ok(None);
    }
    let tcx = ctx.tcx;
    let usize_ty = tcx.types.usize;
    if let StdFailure::OverflowAt { op, span } = failure {
        // The caller identified the failing assertion in std's MIR and its
        // Location; no search runs.
        let item = mir::AssertKind::Overflow(op, (), ()).panic_function();
        let entry = lang_entry(ctx, item).map_err(|why| refusal(ctx, call, &why))?;
        return entry_call_parts(ctx, body, block, entry, &[], SiteLocation::Span(span))
            .map(Some)
            .map_err(|why| refusal(ctx, call, &why));
    }
    let root = resolve_call_callee(ctx, call.func)
        .ok_or_else(|| refusal(ctx, call, "the callee does not resolve to an instance"))?;
    let want = match &failure {
        StdFailure::Helper { name, payload } => Want::Helper {
            name: *name,
            payload,
        },
        StdFailure::BoundsCheck { .. } => Want::BoundsCheck,
        StdFailure::Overflow(op) => Want::Overflow(*op),
        StdFailure::OverflowAt { .. } => unreachable!("handled above"),
        StdFailure::Constant => Want::Constant,
    };
    let mut search = Search {
        ctx: &*ctx,
        want,
        frames: 0,
        stack: Vec::new(),
        truncated: false,
        other: None,
    };
    let sites = search
        .frame(root, 0, &[])
        .map_err(|why| refusal(ctx, call, &why))?;
    let other_class = search.other;
    let Some(shallowest) = sites.iter().map(|site| site.depth).min() else {
        return Err(refusal(
            ctx,
            call,
            "std's MIR has no panic site of this class",
        ));
    };
    // A constant-payload site is chosen only when no panic site of another
    // class sits above it (module docs): never a debug-only check in place of
    // the call that actually fails.
    if let (StdFailure::Constant, Some((depth, what))) = (&failure, &other_class) {
        if *depth < shallowest {
            return Err(refusal(
                ctx,
                call,
                &format!(
                    "std's MIR has a panic site of another class ({what}) at depth {depth}, \
                     above its shallowest constant-payload site (depth {shallowest}); that site \
                     may be the failure, not the constant one"
                ),
            ));
        }
    }
    let mut chosen = sites.iter().filter(|site| site.depth == shallowest);
    let site = chosen.next().cloned().expect("a site at the minimum depth");
    if let Some(other) = chosen.find(|other| {
        other.entry != site.entry
            || other.strings != site.strings
            || other.location != site.location
    }) {
        return Err(refusal(
            ctx,
            call,
            &format!("std's MIR has disagreeing panic sites of this class: {site:?} and {other:?}"),
        ));
    }
    let location = match site.location {
        Loc::Caller => SiteLocation::Caller(call.caller_source_info()),
        Loc::Span(span) => SiteLocation::Span(span),
    };

    let (entry, payload) = match failure {
        StdFailure::Helper { payload, .. } => (
            site.entry
                .ok_or_else(|| refusal(ctx, call, "a helper site without an entry"))?,
            payload,
        ),
        StdFailure::BoundsCheck { index, len } => (
            lang_entry(ctx, LangItem::PanicBoundsCheck).map_err(|why| refusal(ctx, call, &why))?,
            vec![
                Payload::Scalar(index, usize_ty),
                Payload::Scalar(len, usize_ty),
            ],
        ),
        StdFailure::Overflow(op) => {
            let item = mir::AssertKind::Overflow(op, (), ()).panic_function();
            (
                lang_entry(ctx, item).map_err(|why| refusal(ctx, call, &why))?,
                Vec::new(),
            )
        }
        StdFailure::OverflowAt { .. } => unreachable!("handled above"),
        StdFailure::Constant => {
            let entry = site
                .entry
                .ok_or_else(|| refusal(ctx, call, "a constant site without an entry"))?;
            let mut payload = Vec::with_capacity(site.strings.len());
            for text in &site.strings {
                let len = text.len() as u64;
                let alloc = tcx.allocate_bytes_dedup(text.clone(), 0);
                let data = emit_const_alloc_addr(ctx, block, alloc, 0, TrustIrTy::Ptr)
                    .map_err(|why| refusal(ctx, call, &why))?;
                let len = emit_i64_const(ctx, block, i128::from(len));
                payload.push(Payload::Str { data, len });
            }
            (entry, payload)
        }
    };
    entry_call_parts(ctx, body, block, entry, &payload, location)
        .map(Some)
        .map_err(|why| refusal(ctx, call, &why))
}

/// The resolved Location an entry receives.
enum SiteLocation {
    /// What the intercepted call passes its tracked callee.
    Caller(mir::SourceInfo),
    /// The Location of a span inside std.
    Span(Span),
}

fn lang_entry<'tcx>(ctx: &MirLoweringCtx<'tcx>, item: LangItem) -> Result<Instance<'tcx>, String> {
    let def_id = ctx
        .tcx
        .lang_items()
        .get(item)
        .ok_or_else(|| format!("missing actual {item:?} lang item"))?;
    if ctx.tcx.generics_of(def_id).count() != 0 {
        return Err(format!("{item:?} has unsupported generic parameters"));
    }
    Ok(Instance::mono(ctx.tcx, def_id))
}

/// The callee and arguments (emitted into `block`) of a call to `entry` with
/// `payload` (then its hidden Location when it is tracked), checked against
/// its source signature and queried `FnAbi`, and the entry's actual unwind
/// permission, with which the caller honors the intercepted call's unwind
/// edge.
fn entry_call_parts<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    entry: Instance<'tcx>,
    payload: &[Payload<'tcx>],
    location: SiteLocation,
) -> Result<(FuncId, Vec<ValueId>, bool), String> {
    let tcx = ctx.tcx;
    let signature = callee_signature(tcx, entry);
    let tracked = entry.def.requires_caller_location(tcx);
    let inputs: Vec<Ty<'tcx>> = payload.iter().map(|arg| arg.rust_ty(tcx)).collect();
    if signature.abi() != rustc_abi::ExternAbi::Rust
        || signature.c_variadic()
        || !signature.output().is_never()
        || signature.inputs() != inputs.as_slice()
    {
        return Err(format!(
            "{entry:?} has source signature {signature:?}, not `fn({inputs:?}) -> !`"
        ));
    }
    let abi = RustcFnAbiSource::Instance(entry).query(tcx)?;
    let location_ty = tcx.erase_and_anonymize_regions(tcx.caller_location_ty());
    let arguments_match = abi.args.len() == payload.len() + usize::from(tracked)
        && abi
            .args
            .iter()
            .enumerate()
            .all(|(index, argument)| match payload.get(index) {
                Some(
                    Payload::Scalar(_, ty) | Payload::Constant(_, ty) | Payload::Bound(_, ty, _),
                ) => argument.layout.ty == *ty && matches!(argument.mode, PassMode::Direct(_)),
                Some(Payload::Str { .. }) => matches!(argument.mode, PassMode::Pair(..)),
                None => {
                    argument.layout.ty == location_ty
                        && matches!(argument.mode, PassMode::Direct(_))
                }
            });
    if abi.conv != rustc_abi::CanonAbi::Rust
        || abi.c_variadic
        || !matches!(abi.ret.mode, PassMode::Ignore)
        || !abi.ret.layout.ty.is_never()
        || !arguments_match
    {
        return Err(format!(
            "{entry:?} has unsupported actual argument/return FnAbi {abi:?}"
        ));
    }
    let callee: FuncId = ctx.extern_callee(entry)?;
    let params = ctx
        .module
        .function_by_id(callee)
        .map(|function| function.ty)
        .map(|ty| ctx.module.func_types[ty.index() as usize].params.clone())
        .ok_or_else(|| format!("the {entry:?} declaration is missing"))?;
    let mut lanes = Vec::new();
    for argument in payload {
        match argument {
            Payload::Scalar(value, _) | Payload::Bound(value, _, _) => lanes.push(*value),
            Payload::Constant(value, _) => {
                let value = i128::try_from(*value)
                    .map_err(|_| format!("constant payload {value} exceeds a 64-bit lane"))?;
                lanes.push(emit_i64_const(ctx, block, value));
            }
            Payload::Str { data, len } => {
                lanes.push(*data);
                lanes.push(*len);
            }
        }
    }
    if params.len() != lanes.len() + usize::from(tracked) {
        return Err(format!(
            "{entry:?} declared with {params:?}, not {} payload lanes{}",
            lanes.len(),
            if tracked { " and a Location" } else { "" }
        ));
    }
    let mut arguments = Vec::with_capacity(params.len());
    for (value, param) in lanes.into_iter().zip(&params) {
        arguments.push(rebind_lane(ctx, block, value, param)?);
    }
    if tracked {
        let param = params
            .last()
            .expect("a tracked entry declares its Location");
        let value = match location {
            SiteLocation::Caller(site) => {
                let value = caller_location_for_call(ctx, body, block, site)?;
                retype_location(ctx, block, value, param)?
            }
            SiteLocation::Span(span) => emit_caller_location_const_as(ctx, block, span, param)?,
        };
        arguments.push(value);
    }
    Ok((callee, arguments, abi.can_unwind))
}

/// Bind a 64-bit lane value to the declared parameter type: a same-width
/// register move, a truncation to a narrower integer (a 32-bit `usize`), or a
/// pointer move.
fn rebind_lane(
    ctx: &mut MirLoweringCtx<'_>,
    block: &mut Block,
    value: ValueId,
    param: &TrustIrTy,
) -> Result<ValueId, String> {
    let result = ctx.fresh_value();
    let inst = match param.bit_width() {
        Some(64) => Inst::Copy {
            ty: param.clone(),
            operand: value,
        },
        Some(width) if width < 64 && param.is_integer() => Inst::Cast {
            op: super::CastOp::Trunc,
            src_ty: TrustIrTy::I64,
            dst_ty: param.clone(),
            operand: value,
        },
        _ if super::is_pointer_like_trust_ir_ty(param) => Inst::Copy {
            ty: param.clone(),
            operand: value,
        },
        _ => return Err(format!("a payload lane declared as {param:?}")),
    };
    block.body.push(InstrNode::new(inst).with_result(result));
    Ok(result)
}

fn retype_location(
    ctx: &mut MirLoweringCtx<'_>,
    block: &mut Block,
    value: ValueId,
    param: &TrustIrTy,
) -> Result<ValueId, String> {
    let declared = super::rust_ty_to_trust_ir_ty(ctx.tcx, ctx.tcx.caller_location_ty())?;
    if declared == *param {
        return Ok(value);
    }
    if !pointer_casts::can_retype_thin_address(&declared, param) {
        return Err(format!(
            "[TCG-TRACK-CALLER-ABI] caller location of type {declared:?} cannot be passed as \
             {param:?}"
        ));
    }
    let retyped = ctx.fresh_value();
    block.body.push(
        InstrNode::new(Inst::Cast {
            op: super::CastOp::PtrToPtr,
            src_ty: declared,
            dst_ty: param.clone(),
            operand: value,
        })
        .with_result(retyped),
    );
    Ok(retyped)
}
