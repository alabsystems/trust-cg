// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! The calls of a `panic=abort` frame whose callee LLVM's call-site table and
//! this backend's would otherwise read differently: the libm and compiler-rt
//! calls no MIR call names, and the calls through a `fn` pointer or a vtable
//! whose target the MIR states (the later sections).
//!
//! Under `panic=abort` the AArch64 LSDA of a frame with a foreign edge applies
//! LLVM's region rule (`EhPropagation::NounwindFrame`): a region keeps
//! unwinding exactly when it holds an indirect call or a direct call to a
//! callee missing from the frame's `nounwind` callees. A call MIR names is
//! recorded from rustc's own `FnAbi`. The calls handled here stand for an
//! operation LLVM lowers on its own terms instead: a libm routine for a float
//! intrinsic (`sin`, `pow`, `__powidf2`, ...), and the routines the backend
//! calls for an operation this lowering emits (`__udivti3` and the other
//! 128-bit division and remainder routines, `fmod` / `fmodf`, the 128-bit
//! integer <-> float conversions). LLVM emits the same routine as an
//! `ExternalSymbol` libcall, which its table treats as one that may unwind
//! (covered), unless it folds, expands, narrows or deletes the operation (no
//! call: a gap). So such a callee may be left out of the `nounwind` set only
//! where LLVM certainly emits the libcall at the same program point
//! ([`llvm_certainly_calls`]); everywhere else it is recorded, and the search
//! fails phase one at most earlier than LLVM's (OD-58), never later.
//!
//! LLVM's choice turns on what this lowering cannot see in general: its
//! constant propagation through calls and loads (`sin(two())`, a `static`,
//! interprocedural propagation through an `#[inline(never)]` helper), full
//! unrolling, algebra (`a * 0.0 + 100.0` of a non-negative `a`), division by a
//! constant (`x / 3`, `x % 10` on `u128` expand to multiplies), narrowing of
//! zero-extended operands (`(a as u128) / (b as u128)` is one 64-bit `udiv`)
//! and deletion of a result nothing reads (at every level, O0 included). The
//! rule therefore states what is provable:
//!
//! * At O0 LLVM runs no folding, expansion or narrowing pass, and deletes only
//!   an operation whose result nothing reads (measured: `let _q = x as i128`,
//!   `let _m = a % b`, `let _q = w / black_box(3u128)` leave no call at O0).
//!   A site is certain unless its result is dead ([`BodyFacts::dead`]: no
//!   observable effect reads it, through copies and pure operations).
//! * Above O0 a site is certain only when LLVM can know nothing about its
//!   operands and must produce its result at that point: every operand is the
//!   result of a `black_box` (an asm barrier LLVM cannot see through), the
//!   result is passed to a `black_box`, and the stretch from those operands to
//!   that consumer holds no invoke and no call LLVM could inline (so LLVM's
//!   call lies in the same region as this lowering's). Every other site is
//!   recorded.
//!
//! The decision is per site; the record is per callee and per lowered
//! function, so one uncertain site makes every call of that routine in the
//! function a gap.

use std::collections::{BTreeSet, HashSet};
use std::rc::Rc;

use crate::compiler_attributes::InlineAttr;
use rustc_middle::mir::interpret::{AllocId, GlobalAlloc, Scalar, alloc_range};
use rustc_middle::mir::visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor};
use rustc_middle::ty::adjustment::PointerCoercion;
use rustc_middle::ty::{Instance, Ty, TyCtxt};
use trust_cg_lower::runtime_calls::RuntimeSymbol;

use super::{
    Block, BlockId, Body, CastOp, FuncId, Inst, InstrNode, Local, MirLoweringCtx, Operand, Place,
    ProjectionElem, Rvalue, StatementKind, TerminatorKind, TrustIrBinOp, TrustIrModule, TrustIrTy,
    ValueId, call_func_is_static_fn_item, inlined_terminate_pads, instance_abi_has_caller_location,
    is_pointer_like_trust_ir_ty, is_std_black_box, mir, panic_is_abort, ty,
};

/// The callees of one lowered function's non-unwinding frame that its object
/// compile treats as `nounwind` (`CompilerConfig::eh_nounwind_callees`).
#[derive(Clone, Debug, Default)]
pub(super) struct NounwindCallees {
    /// Module callees, by `FuncId` (every later symbol rename keeps them):
    /// those whose rustc `FnAbi` cannot unwind and the calls this lowering
    /// creates itself where LLVM has no call (`MirLoweringCtx::nounwind_callees`).
    pub(super) ids: Vec<FuncId>,
    /// Runtime routines the backend calls by name for an operation of the
    /// module ([`runtime_libcall_symbols`]) at a site where LLVM's table may
    /// have no call ([`runtime_libcall_nounwind_symbols`]).
    pub(super) runtime: Vec<&'static str>,
}

impl NounwindCallees {
    /// The final symbols of these callees in `module`.
    pub(super) fn symbols(&self, module: &TrustIrModule) -> BTreeSet<String> {
        module
            .functions
            .iter()
            .filter(|function| self.ids.binary_search(&function.id).is_ok())
            .map(|function| function.name.clone())
            .chain(self.runtime.iter().map(|symbol| (*symbol).to_owned()))
            .collect()
    }
}

/// Per-lowering state of these rules, held by `MirLoweringCtx`.
#[derive(Default)]
pub(super) struct CreatedCallState {
    /// The MIR location being lowered (a statement or a terminator) and the
    /// address of its body, set around each one ([`set_site`]) so the site
    /// rules can name their site ([`site`]).
    site: Option<(usize, mir::Location)>,
    /// Results of the operations in `FuncId(0)` lowered from a site LLVM
    /// certainly calls a libcall for ([`note_statement_libcalls`]).
    certain: HashSet<ValueId>,
    /// [`BodyFacts`] of the body last asked about, keyed by its address.
    facts: Option<(usize, Rc<BodyFacts>)>,
}

/// The address that identifies `body` while it is lowered.
fn body_key(body: &Body<'_>) -> usize {
    std::ptr::from_ref(body) as usize
}

/// Name `location` of `body` as the site being lowered (`None` once it is
/// lowered).
pub(super) fn set_site<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    location: Option<mir::Location>,
) {
    ctx.created_calls.site = location.map(|location| (body_key(body), location));
}

/// The site of `body` being lowered, when one is named for this very body
/// (a nested lowering of another body never sees it).
pub(super) fn site<'tcx>(ctx: &MirLoweringCtx<'tcx>, body: &Body<'tcx>) -> Option<mir::Location> {
    ctx.created_calls
        .site
        .filter(|(key, _)| *key == body_key(body))
        .map(|(_, location)| location)
}

/// The runtime routines the backend's lowering of `inst` calls by name, where
/// LLVM would emit the same libcall or expand the operation: a 128-bit integer
/// division or remainder (`__udivti3`, `__divti3`, `__umodti3`, `__modti3`),
/// a float remainder (`fmod` / `fmodf`, per lane for a vector), and a 128-bit
/// integer <-> float conversion (`__fix*ti`, `__float*ti*`). Empty for every
/// other instruction.
pub(super) fn runtime_libcall_symbols(inst: &Inst) -> Vec<&'static str> {
    let names = |symbols: &[RuntimeSymbol]| symbols.iter().map(|symbol| symbol.name()).collect();
    match inst {
        Inst::BinOp { op, ty, .. } => match (op, ty) {
            (TrustIrBinOp::UDiv, TrustIrTy::I128 | TrustIrTy::U128) => {
                names(&[RuntimeSymbol::Udivti3])
            }
            (TrustIrBinOp::SDiv, TrustIrTy::I128 | TrustIrTy::U128) => {
                names(&[RuntimeSymbol::Divti3])
            }
            (TrustIrBinOp::URem, TrustIrTy::I128 | TrustIrTy::U128) => {
                names(&[RuntimeSymbol::Umodti3])
            }
            (TrustIrBinOp::SRem, TrustIrTy::I128 | TrustIrTy::U128) => {
                names(&[RuntimeSymbol::Modti3])
            }
            (TrustIrBinOp::FRem, TrustIrTy::F64) => names(&[RuntimeSymbol::Fmod]),
            (TrustIrBinOp::FRem, TrustIrTy::F32 | TrustIrTy::F16) => names(&[RuntimeSymbol::Fmodf]),
            (TrustIrBinOp::FRem, _) => names(&[RuntimeSymbol::Fmod, RuntimeSymbol::Fmodf]),
            _ => Vec::new(),
        },
        Inst::Cast {
            op, src_ty, dst_ty, ..
        } => {
            let wide = |ty: &TrustIrTy| matches!(ty, TrustIrTy::I128 | TrustIrTy::U128);
            let double = |ty: &TrustIrTy| matches!(ty, TrustIrTy::F64);
            match op {
                CastOp::FPToSI | CastOp::FPToSISat if wide(dst_ty) => names(&[if double(src_ty) {
                    RuntimeSymbol::Fixdfti
                } else {
                    RuntimeSymbol::Fixsfti
                }]),
                CastOp::FPToUI | CastOp::FPToUISat if wide(dst_ty) => names(&[if double(src_ty) {
                    RuntimeSymbol::Fixunsdfti
                } else {
                    RuntimeSymbol::Fixunssfti
                }]),
                CastOp::SIToFP if wide(src_ty) => names(&[if double(dst_ty) {
                    RuntimeSymbol::Floattidf
                } else {
                    RuntimeSymbol::Floattisf
                }]),
                CastOp::UIToFP if wide(src_ty) => names(&[if double(dst_ty) {
                    RuntimeSymbol::Floatuntidf
                } else {
                    RuntimeSymbol::Floatuntisf
                }]),
                _ => Vec::new(),
            }
        }
        _ => Vec::new(),
    }
}

/// The runtime routines of the lowered module ([`runtime_libcall_symbols`])
/// its non-unwinding frame records as `nounwind`: every one some instruction
/// calls for, except at an instruction of the lowered definition (`FuncId(0)`)
/// whose MIR site LLVM certainly calls the libcall for
/// ([`note_statement_libcalls`]). Any other instruction (a lowering's own
/// expansion, such as an `i128` `Display` digit loop, a site the rules cannot
/// prove, another function of the module) records its routines, so an
/// unanalysed site only ever aborts earlier.
pub(super) fn runtime_libcall_nounwind_symbols(ctx: &MirLoweringCtx<'_>) -> Vec<&'static str> {
    if !panic_is_abort(ctx.tcx) {
        return Vec::new();
    }
    let mut symbols = BTreeSet::new();
    for function in &ctx.module.functions {
        let definition = function.id == FuncId::new(0);
        for node in function.blocks.iter().flat_map(|block| &block.body) {
            let routines = runtime_libcall_symbols(&node.inst);
            if routines.is_empty() {
                continue;
            }
            let certain = definition
                && !node.results.is_empty()
                && node
                    .results
                    .iter()
                    .all(|result| ctx.created_calls.certain.contains(result));
            if !certain {
                symbols.extend(routines);
            }
        }
    }
    symbols.into_iter().collect()
}

/// After lowering `statement` (at `location`) into `block`, which held `mark`
/// (its id and body length) before: when the statement is a MIR site of a
/// runtime libcall (a division or remainder, a float <-> integer cast), it
/// lowered to exactly one instruction the backend lowers to such a call, in
/// the same block, and LLVM certainly calls the libcall there
/// ([`llvm_certainly_calls`]), remember that instruction's results. Any other
/// shape is left unremembered, so its routine is recorded.
pub(super) fn note_statement_libcalls<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &Block,
    mark: (BlockId, usize),
    statement: &mir::Statement<'tcx>,
    location: mir::Location,
) {
    if !panic_is_abort(ctx.tcx) {
        return;
    }
    let StatementKind::Assign(assign) = &statement.kind else {
        return;
    };
    let (destination, rvalue) = &**assign;
    let operands: Vec<&Operand<'tcx>> = match rvalue {
        Rvalue::BinaryOp(mir::BinOp::Div | mir::BinOp::Rem, operands) => {
            vec![&operands.0, &operands.1]
        }
        Rvalue::Cast(mir::CastKind::FloatToInt | mir::CastKind::IntToFloat, operand, _) => {
            vec![operand]
        }
        _ => return,
    };
    if block.id != mark.0 {
        return;
    }
    let created: Vec<&InstrNode> = block
        .body
        .get(mark.1..)
        .unwrap_or(&[])
        .iter()
        .filter(|node| !runtime_libcall_symbols(&node.inst).is_empty())
        .collect();
    let [node] = created.as_slice() else {
        return;
    };
    let results = node.results.clone();
    if !results.is_empty()
        && llvm_certainly_calls(ctx, body, Some(location), &operands, destination, true)
    {
        ctx.created_calls.certain.extend(results);
    }
}

/// Whether LLVM certainly emits a libcall that may unwind (an `ExternalSymbol`
/// call, so its region is covered) for the operation at MIR `site` whose
/// operands are `operands` and whose result is `destination`. See the module
/// documentation for the rule; a site this lowering cannot name is never
/// certain.
pub(super) fn llvm_certainly_calls<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    site: Option<mir::Location>,
    operands: &[&Operand<'tcx>],
    destination: &Place<'tcx>,
    folds_constants: bool,
) -> bool {
    let Some(site) = site.filter(|site| location_is_in(body, *site)) else {
        return false;
    };
    let facts = body_facts(ctx, body);
    if !ctx.session_optimizes() {
        // At O0 only IR construction folds, and only an instruction
        // (`folds_constants`: a division, remainder or int/float conversion)
        // all of whose operands are constants; a math call stays a call.
        return !facts.place_is_dead(destination)
            && (!folds_constants
                || operands
                    .iter()
                    .any(|operand| facts.operand_is_runtime_value(ctx, body, operand)));
    }
    // Each operand opaque on its own is not enough: LLVM folds `X / X` and
    // `X % X` (InstSimplify) without knowing X, so two operands traced to
    // one black_box result are not opaque to each other.
    let mut sources = Vec::with_capacity(operands.len());
    for operand in operands {
        let Some(source) = facts.opaque_source(ctx, body, site, operand) else {
            return false;
        };
        if sources.contains(&source) {
            return false;
        }
        sources.push(source);
    }
    facts.result_reaches_black_box(ctx, body, site, destination)
}

/// Whether LLVM certainly keeps the `memset` of a `[v; N]` fill of `place` at
/// MIR `site` above O0: `place` is a whole local whose address the stretch
/// after the fill passes to a `black_box` (which reads the memory, so the fill
/// cannot be deleted, forwarded or folded) before anything else touches it,
/// with no invoke and no call LLVM could inline in between.
pub(super) fn fill_reaches_black_box<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    place: &Place<'tcx>,
) -> bool {
    let Some(site) = site(ctx, body).filter(|site| location_is_in(body, *site)) else {
        return false;
    };
    if !place.projection.is_empty() {
        return false;
    }
    let facts = body_facts(ctx, body);
    facts.address_reaches_black_box(ctx, body, site, place.local)
}

/// Whether `location` names a statement or the terminator of `body`.
fn location_is_in(body: &Body<'_>, location: mir::Location) -> bool {
    body.basic_blocks
        .get(location.block)
        .is_some_and(|data| location.statement_index <= data.statements.len())
}

/// The [`BodyFacts`] of `body`, computed once per body.
fn body_facts<'tcx>(ctx: &mut MirLoweringCtx<'tcx>, body: &Body<'tcx>) -> Rc<BodyFacts> {
    let key = body_key(body);
    if let Some((cached, facts)) = &ctx.created_calls.facts {
        if *cached == key {
            return Rc::clone(facts);
        }
    }
    let facts = Rc::new(BodyFacts::of(body));
    ctx.created_calls.facts = Some((key, Rc::clone(&facts)));
    facts
}

/// The facts about a MIR body's locals the site rules read.
struct BodyFacts {
    /// Whether no observable effect reads the local: its every read is an
    /// operand of a side-effect-free assignment into a local that is itself
    /// dead (a copy, arithmetic, a cast, an aggregate), so LLVM deletes the
    /// computation even at O0. The return place, a local read by a
    /// terminator, a borrow, a write through a pointer or any other statement
    /// is live.
    dead: Vec<bool>,
    /// Each local's whole-local definitions: assignments and call
    /// destinations.
    defs: Vec<Vec<mir::Location>>,
    /// Whether a borrow, a partial write or any other mutation besides a
    /// whole-local definition reaches the local.
    mutated: Vec<bool>,
    /// Whether any borrow of the local (shared or mutable) exists.
    borrowed: Vec<bool>,
    /// The body's argument count: locals `1..=args` hold the caller's values
    /// at entry, a definition `defs` never lists.
    args: usize,
}

/// Every local a visited MIR fragment reads or borrows (not a `NonUse`).
struct LocalUses(Vec<Local>);

impl<'tcx> Visitor<'tcx> for LocalUses {
    fn visit_local(&mut self, local: Local, context: PlaceContext, _: mir::Location) {
        if !matches!(context, PlaceContext::NonUse(_)) {
            self.0.push(local);
        }
    }
}

/// Classifies every local use of a body: definitions, mutations, borrows.
struct LocalAccess<'a> {
    facts: &'a mut BodyFacts,
}

impl<'tcx> Visitor<'tcx> for LocalAccess<'_> {
    fn visit_local(&mut self, local: Local, context: PlaceContext, _: mir::Location) {
        let index = local.as_usize();
        match context {
            PlaceContext::MutatingUse(MutatingUseContext::Store | MutatingUseContext::Call) => {}
            PlaceContext::MutatingUse(
                MutatingUseContext::Borrow | MutatingUseContext::RawBorrow,
            ) => {
                self.facts.mutated[index] = true;
                self.facts.borrowed[index] = true;
            }
            // A raw pointer may be written through (`cast_mut`), so `&raw
            // const` is a possible mutation, as rustc's own analyses take it;
            // a shared reference may not.
            PlaceContext::NonMutatingUse(NonMutatingUseContext::RawBorrow) => {
                self.facts.mutated[index] = true;
                self.facts.borrowed[index] = true;
            }
            PlaceContext::NonMutatingUse(
                NonMutatingUseContext::SharedBorrow | NonMutatingUseContext::FakeBorrow,
            ) => self.facts.borrowed[index] = true,
            // A drop ends the value; a later value needs a second definition.
            PlaceContext::MutatingUse(MutatingUseContext::Drop) => {}
            PlaceContext::MutatingUse(_) => self.facts.mutated[index] = true,
            PlaceContext::NonMutatingUse(_) | PlaceContext::NonUse(_) => {}
        }
    }

    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: mir::Location) {
        // A use of a projection also classifies its base local by the whole
        // place's context, as rustc's `SsaVisitor` does: `&raw const t.f` may
        // be written through and `&t.f` borrows `t`. A store or call result
        // into a projection mutates part of the local; the visitor then
        // reports the base local as a `Projection` use.
        if !place.projection.is_empty()
            && !matches!(place.projection.first(), Some(ProjectionElem::Deref))
        {
            self.visit_local(place.local, context, location);
        }
        self.super_place(place, context, location);
    }
}

impl BodyFacts {
    fn of(body: &Body<'_>) -> Self {
        let locals = body.local_decls.len();
        let mut facts = BodyFacts {
            dead: vec![false; locals],
            defs: vec![Vec::new(); locals],
            mutated: vec![false; locals],
            borrowed: vec![false; locals],
            args: body.arg_count,
        };
        LocalAccess { facts: &mut facts }.visit_body(body);
        // Whole-local definitions.
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                if let StatementKind::Assign(assign) = &statement.kind {
                    if assign.0.projection.is_empty() {
                        facts.defs[assign.0.local.as_usize()].push(mir::Location {
                            block: bb,
                            statement_index,
                        });
                    }
                }
            }
            if let TerminatorKind::Call { destination, .. } = &data.terminator().kind {
                if destination.projection.is_empty() {
                    facts.defs[destination.local.as_usize()].push(body.terminator_loc(bb));
                }
            }
        }
        // Liveness: roots are the locals an observable effect reads; a local
        // read only by side-effect-free assignments into a dead local is dead.
        let mut live = vec![false; locals];
        let mut feeds: Vec<Vec<Local>> = vec![Vec::new(); locals];
        let mut roots: Vec<Local> = vec![mir::RETURN_PLACE];
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                let location = mir::Location {
                    block: bb,
                    statement_index,
                };
                let mut reads = LocalUses(Vec::new());
                match &statement.kind {
                    StatementKind::Assign(assign) => {
                        let (place, rvalue) = &**assign;
                        reads.visit_rvalue(rvalue, location);
                        let mut through_pointer = false;
                        for element in place.projection.iter() {
                            match element {
                                ProjectionElem::Index(index) => reads.0.push(index),
                                ProjectionElem::Deref => through_pointer = true,
                                _ => {}
                            }
                        }
                        let pure = matches!(
                            rvalue,
                            Rvalue::Use(..)
                                | Rvalue::BinaryOp(..)
                                | Rvalue::UnaryOp(..)
                                | Rvalue::Cast(..)
                                | Rvalue::Aggregate(..)
                                | Rvalue::Repeat(..)
                                | Rvalue::Discriminant(..)
                                | Rvalue::CopyForDeref(..)
                        );
                        if pure && !through_pointer && place.local != mir::RETURN_PLACE {
                            feeds[place.local.as_usize()].extend(reads.0);
                        } else {
                            roots.extend(reads.0);
                            if through_pointer {
                                roots.push(place.local);
                            }
                        }
                    }
                    // No code: not a read of anything.
                    StatementKind::StorageLive(_)
                    | StatementKind::StorageDead(_)
                    | StatementKind::FakeRead(_)
                    | StatementKind::PlaceMention(_)
                    | StatementKind::AscribeUserType(..)
                    | StatementKind::Coverage(_)
                    | StatementKind::ConstEvalCounter
                    | StatementKind::BackwardIncompatibleDropHint { .. }
                    | StatementKind::Nop => {}
                    _ => {
                        reads.visit_statement(statement, location);
                        roots.extend(reads.0);
                    }
                }
            }
            let terminator = data.terminator();
            let location = body.terminator_loc(bb);
            let mut reads = LocalUses(Vec::new());
            match &terminator.kind {
                // The destination of a call is its write, not a read; a
                // projected destination reads its base pointer.
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } => {
                    reads.visit_operand(func, location);
                    for arg in args.iter() {
                        reads.visit_operand(&arg.node, location);
                    }
                    if !destination.projection.is_empty() {
                        reads.0.push(destination.local);
                        for element in destination.projection.iter() {
                            if let ProjectionElem::Index(index) = element {
                                reads.0.push(index);
                            }
                        }
                    }
                }
                _ => reads.visit_terminator(terminator, location),
            }
            roots.extend(reads.0);
        }
        while let Some(local) = roots.pop() {
            let index = local.as_usize();
            if live[index] {
                continue;
            }
            live[index] = true;
            roots.extend(feeds[index].iter().copied());
        }
        facts.dead = live.into_iter().map(|live| !live).collect();
        facts
    }

    /// Whether `place` is a whole local no observable effect reads.
    fn place_is_dead(&self, place: &Place<'_>) -> bool {
        place.projection.is_empty()
            && place.local != mir::RETURN_PLACE
            && self.dead[place.local.as_usize()]
    }

    /// The single whole-local definition of `local`, when it has exactly one
    /// and nothing else mutates it. An argument never has one: its value at
    /// entry is the caller's, so one assignment in the body still leaves two
    /// values reaching a use.
    fn single_def(&self, local: Local) -> Option<mir::Location> {
        let index = local.as_usize();
        if self.is_argument(local) {
            return None;
        }
        match self.defs[index].as_slice() {
            [def] if !self.mutated[index] => Some(*def),
            _ => None,
        }
    }

    /// Whether `local` is one of the body's arguments.
    fn is_argument(&self, local: Local) -> bool {
        (1..=self.args).contains(&local.as_usize())
    }

    /// Whether `operand` is certainly not a constant when rustc builds its IR
    /// at O0. LLVM's IRBuilder folds an operation whose operands are all
    /// constants as it builds it, at every level, and rustc keeps a local
    /// defined by constants as an SSA constant; it folds nothing else. So a
    /// value is a runtime one when it is an argument the body never writes,
    /// the result of a call codegen makes (not an intrinsic it may evaluate,
    /// black_box aside), or, through locals defined once, a unary, binary or
    /// cast operation (or a checked operation's field) with a runtime
    /// operand. Anything else may be a constant.
    fn operand_is_runtime_value<'tcx>(
        &self,
        ctx: &MirLoweringCtx<'tcx>,
        body: &Body<'tcx>,
        operand: &Operand<'tcx>,
    ) -> bool {
        self.runtime_operand(ctx, body, operand, 16)
    }

    fn runtime_operand<'tcx>(
        &self,
        ctx: &MirLoweringCtx<'tcx>,
        body: &Body<'tcx>,
        operand: &Operand<'tcx>,
        depth: usize,
    ) -> bool {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.runtime_place(ctx, body, *place, depth)
            }
            _ => false,
        }
    }

    fn runtime_place<'tcx>(
        &self,
        ctx: &MirLoweringCtx<'tcx>,
        body: &Body<'tcx>,
        place: Place<'tcx>,
        depth: usize,
    ) -> bool {
        let Some(depth) = depth.checked_sub(1) else {
            return false;
        };
        // A field is followed only into a checked operation's result pair.
        let projected = !place.projection.is_empty();
        if place
            .projection
            .iter()
            .any(|element| !matches!(element, ProjectionElem::Field(..)))
        {
            return false;
        }
        let local = place.local;
        let index = local.as_usize();
        if self.is_argument(local) {
            return !projected && self.defs[index].is_empty() && !self.mutated[index];
        }
        let Some(def) = self.single_def(local) else {
            return false;
        };
        let data = &body.basic_blocks[def.block];
        if def.statement_index == data.statements.len() {
            let TerminatorKind::Call { func, .. } = &data.terminator().kind else {
                return false;
            };
            if projected {
                return false;
            }
            if call_is_black_box(ctx, func) {
                return true;
            }
            let Some(instance) = super::resolve_call_callee(ctx, func) else {
                // An indirect call LLVM cannot inline; an unresolved direct
                // one may be anything.
                return func.const_fn_def().is_none();
            };
            // An intrinsic codegen may evaluate, or a body LLVM's O0
            // AlwaysInliner inlines (it may return a constant), is not
            // certainly a runtime value.
            return ctx.tcx.intrinsic(instance.def_id()).is_none()
                && !matches!(
                    ctx.tcx.codegen_fn_attrs(instance.def_id()).inline,
                    InlineAttr::Always | InlineAttr::Force { .. }
                );
        }
        let StatementKind::Assign(assign) = &data.statements[def.statement_index].kind else {
            return false;
        };
        match &assign.1 {
            Rvalue::BinaryOp(_, operands) => {
                self.runtime_operand(ctx, body, &operands.0, depth)
                    || self.runtime_operand(ctx, body, &operands.1, depth)
            }
            _ if projected => false,
            // A pointer's metadata is often static (an unsized array's length,
            // a vtable), whatever the pointer.
            Rvalue::UnaryOp(mir::UnOp::PtrMetadata, _) => false,
            Rvalue::Use(operand, ..)
            | Rvalue::Cast(_, operand, _)
            | Rvalue::UnaryOp(_, operand) => self.runtime_operand(ctx, body, operand, depth),
            _ => false,
        }
    }

    /// The `black_box` call `operand` is, through copies of locals defined
    /// once, the result of, when that call's stretch reaches `site`
    /// ([`stretch_reaches`]): a value LLVM can know nothing about there.
    fn opaque_source<'tcx>(
        &self,
        ctx: &MirLoweringCtx<'tcx>,
        body: &Body<'tcx>,
        site: mir::Location,
        operand: &Operand<'tcx>,
    ) -> Option<mir::Location> {
        let place = operand.place()?;
        if !place.projection.is_empty() {
            return None;
        }
        let mut local = place.local;
        for _ in 0..8 {
            if self.borrowed[local.as_usize()] {
                return None;
            }
            let Some(def) = self.single_def(local) else {
                return None;
            };
            let data = &body.basic_blocks[def.block];
            if def.statement_index == data.statements.len() {
                let TerminatorKind::Call { func, .. } = &data.terminator().kind else {
                    return None;
                };
                return (call_is_black_box(ctx, func) && stretch_reaches(ctx, body, def, site))
                    .then_some(def);
            }
            let StatementKind::Assign(assign) = &data.statements[def.statement_index].kind else {
                return None;
            };
            let Rvalue::Use(Operand::Copy(source) | Operand::Move(source), _) = &assign.1 else {
                return None;
            };
            if !source.projection.is_empty() {
                return None;
            }
            local = source.local;
        }
        None
    }

    /// Whether the value `destination` receives at `site` reaches a
    /// `black_box` call within the stretch after `site`, by value or by
    /// shared reference, through copies.
    fn result_reaches_black_box<'tcx>(
        &self,
        ctx: &MirLoweringCtx<'tcx>,
        body: &Body<'tcx>,
        site: mir::Location,
        destination: &Place<'tcx>,
    ) -> bool {
        if !destination.projection.is_empty() || self.single_def(destination.local) != Some(site) {
            return false;
        }
        let mut values: HashSet<Local> = HashSet::from([destination.local]);
        let mut refs: HashSet<Local> = HashSet::new();
        walk_stretch(ctx, body, site, |event| match event {
            StretchEvent::Statement(statement) => {
                let StatementKind::Assign(assign) = &statement.kind else {
                    return StretchStep::Continue;
                };
                let (place, rvalue) = &**assign;
                if !place.projection.is_empty() {
                    return StretchStep::Continue;
                }
                let target = place.local;
                values.remove(&target);
                refs.remove(&target);
                match rvalue {
                    Rvalue::Use(Operand::Copy(source) | Operand::Move(source), _)
                        if source.projection.is_empty() =>
                    {
                        if values.contains(&source.local) {
                            values.insert(target);
                        } else if refs.contains(&source.local) {
                            refs.insert(target);
                        }
                    }
                    Rvalue::Ref(_, mir::BorrowKind::Shared, source)
                    | Rvalue::RawPtr(mir::RawPtrKind::Const, source)
                        if source.projection.is_empty() && values.contains(&source.local) =>
                    {
                        refs.insert(target);
                    }
                    _ => {}
                }
                StretchStep::Continue
            }
            StretchEvent::Call { func, args } => {
                if call_is_black_box(ctx, func)
                    && args.iter().any(|arg| {
                        arg.node.place().is_some_and(|place| {
                            place.projection.is_empty()
                                && (values.contains(&place.local) || refs.contains(&place.local))
                        })
                    })
                {
                    StretchStep::Found
                } else {
                    StretchStep::Continue
                }
            }
        })
    }

    /// Whether the address of `local` (just filled at `site`) reaches a
    /// `black_box` call within the stretch after `site` before anything else
    /// reads, writes or borrows `local`.
    fn address_reaches_black_box<'tcx>(
        &self,
        ctx: &MirLoweringCtx<'tcx>,
        body: &Body<'tcx>,
        site: mir::Location,
        local: Local,
    ) -> bool {
        let mut refs: HashSet<Local> = HashSet::new();
        let mut touched = false;
        let found = walk_stretch(ctx, body, site, |event| {
            let mut uses = LocalUses(Vec::new());
            match event {
                StretchEvent::Statement(statement) => {
                    if let StatementKind::Assign(assign) = &statement.kind {
                        let (place, rvalue) = &**assign;
                        if place.projection.is_empty() && place.local != local {
                            let target = place.local;
                            refs.remove(&target);
                            match rvalue {
                                Rvalue::Ref(_, mir::BorrowKind::Shared, source)
                                | Rvalue::RawPtr(mir::RawPtrKind::Const, source)
                                    if source.projection.is_empty() && source.local == local =>
                                {
                                    refs.insert(target);
                                    return StretchStep::Continue;
                                }
                                Rvalue::Use(Operand::Copy(source) | Operand::Move(source), _)
                                    if source.projection.is_empty()
                                        && refs.contains(&source.local) =>
                                {
                                    refs.insert(target);
                                    return StretchStep::Continue;
                                }
                                _ => {}
                            }
                        }
                    }
                    uses.visit_statement(statement, mir::Location::START);
                }
                StretchEvent::Call { func, args } => {
                    if call_is_black_box(ctx, func)
                        && args.iter().any(|arg| {
                            arg.node.place().is_some_and(|place| {
                                place.projection.is_empty() && refs.contains(&place.local)
                            })
                        })
                    {
                        return StretchStep::Found;
                    }
                    uses.visit_operand(func, mir::Location::START);
                    for arg in args {
                        uses.visit_operand(&arg.node, mir::Location::START);
                    }
                }
            }
            if uses.0.contains(&local) {
                touched = true;
                StretchStep::Stop
            } else {
                StretchStep::Continue
            }
        });
        found && !touched
    }
}

/// One step of [`walk_stretch`]'s caller.
enum StretchStep {
    Continue,
    Found,
    Stop,
}

/// What [`walk_stretch`] shows its caller, in program order.
enum StretchEvent<'a, 'tcx> {
    Statement(&'a mir::Statement<'tcx>),
    Call {
        func: &'a Operand<'tcx>,
        args: &'a [rustc_span::Spanned<Operand<'tcx>>],
    },
}

/// The longest stretch [`walk_stretch`] follows, in basic blocks.
const STRETCH_BLOCKS: usize = 32;

/// Walk the straight-line stretch after `from` (exclusive): the statements of
/// its block and then, across each terminator that continues the stretch, of
/// the next block. A terminator continues it when it is a `Goto`, an
/// `Assert` with no unwind edge, or a call with no cleanup or terminate edge
/// to a callee LLVM cannot inline into this frame (a `black_box`, an
/// intrinsic, a foreign item): so the stretch holds no invoke, now or after
/// LLVM's inlining, and LLVM's table puts it in one region. Each call is shown
/// to `visit` as it is reached; returns whether `visit` reported `Found`.
fn walk_stretch<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    from: mir::Location,
    mut visit: impl FnMut(StretchEvent<'_, 'tcx>) -> StretchStep,
) -> bool {
    let mut bb = from.block;
    let mut first = from.statement_index + 1;
    for _ in 0..STRETCH_BLOCKS {
        let data = &body.basic_blocks[bb];
        for statement in data.statements.iter().skip(first) {
            match visit(StretchEvent::Statement(statement)) {
                StretchStep::Continue => {}
                StretchStep::Found => return true,
                StretchStep::Stop => return false,
            }
        }
        // The terminator at `from` itself is the site or the operand's own
        // call: it has already happened.
        let terminator = data.terminator();
        let at_from = bb == from.block && from.statement_index == data.statements.len();
        let next = if let Some(goto) = crate::mir_goto::view(&terminator.kind) {
            goto.target()
        } else {
            match &terminator.kind {
                TerminatorKind::Assert { target, unwind, .. } if !invoke_like(unwind) => *target,
                TerminatorKind::Call {
                    func,
                    args,
                    target: Some(target),
                    unwind,
                    ..
                } if !invoke_like(unwind) && call_is_leaf(ctx, func) => {
                    if !at_from {
                        match visit(StretchEvent::Call { func, args }) {
                            StretchStep::Continue => {}
                            StretchStep::Found => return true,
                            StretchStep::Stop => return false,
                        }
                    }
                    *target
                }
                _ => return false,
            }
        };
        bb = next;
        first = 0;
    }
    false
}

/// Whether the stretch after `from` reaches `to` ([`walk_stretch`]).
fn stretch_reaches<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    from: mir::Location,
    to: mir::Location,
) -> bool {
    if from.block == to.block && from.statement_index < to.statement_index {
        return true;
    }
    let mut bb = from.block;
    for _ in 0..STRETCH_BLOCKS {
        let data = &body.basic_blocks[bb];
        let terminator = data.terminator();
        let next = if let Some(goto) = crate::mir_goto::view(&terminator.kind) {
            goto.target()
        } else {
            match &terminator.kind {
                TerminatorKind::Assert { target, unwind, .. } if !invoke_like(unwind) => *target,
                TerminatorKind::Call {
                    func,
                    target: Some(target),
                    unwind,
                    ..
                } if !invoke_like(unwind) && call_is_leaf(ctx, func) => *target,
                _ => return false,
            }
        };
        if next == to.block {
            return true;
        }
        bb = next;
    }
    false
}

/// Whether a call's unwind action makes it an LLVM `invoke` (a cleanup or a
/// terminate landing pad): a region boundary of the frame's table.
fn invoke_like(unwind: &mir::UnwindAction) -> bool {
    matches!(
        unwind,
        mir::UnwindAction::Cleanup(_) | mir::UnwindAction::Terminate(_)
    )
}

/// Whether `func` names core's `black_box` (the hint or the intrinsic).
fn call_is_black_box<'tcx>(ctx: &MirLoweringCtx<'tcx>, func: &Operand<'tcx>) -> bool {
    func.const_fn_def()
        .is_some_and(|(def_id, _)| is_std_black_box(ctx.tcx, def_id))
}

/// Whether `func` names a callee whose body LLVM cannot inline into this frame:
/// core's `black_box`, a compiler intrinsic, or a foreign item.
fn call_is_leaf<'tcx>(ctx: &MirLoweringCtx<'tcx>, func: &Operand<'tcx>) -> bool {
    func.const_fn_def().is_some_and(|(def_id, _)| {
        is_std_black_box(ctx.tcx, def_id)
            || ctx.tcx.intrinsic(def_id).is_some()
            || ctx.tcx.is_foreign_item(def_id)
    })
}

// ---------------------------------------------------------------------------
// Calls through a fn pointer whose target the MIR states
// ---------------------------------------------------------------------------
//
// LLVM calls such a pointer's function directly. rustc's codegen keeps a local
// holding a reified fn item (`let f: fn(u64) = nwf; f(2)`) as an SSA value
// whose constant is the function itself, so the call's operand is the
// `Function` at every level, O0 included; and rustc_codegen_llvm's
// `load_operand` reads a load from an immutable `static` holding a fn pointer
// (`static FP: fn(u64) -> u64 = nw; FP(2)`) out of the constant global's
// initializer, again at O0 (above O0 LLVM folds any such load). LLVM's table
// then reads the callee's own `nounwind`, so a region holding only such calls
// is a gap, where this lowering's indirect call (`blr`) would cover the region
// and keep unwinding (measured: both shapes at O0-O3). Such a call is lowered
// as the direct call LLVM makes, to the same function with the same ABI.

/// The direct callee of a call through the `fn` pointer `func`, as a `FnDef`
/// operand the direct-call lowering resolves to the same instance, when the
/// MIR states the pointer's target and the frame is a `panic=abort` frame with
/// an exception table (the only frame whose table reads callees): `func` is,
/// through copies of locals defined once, a reified fn item, a constant
/// pointer to a function, or a load through a constant pointer into an
/// immutable allocation holding one. Only a plain item (`InstanceKind::Item`,
/// never a `#[track_caller]` reify shim or a closure) qualifies, and only a
/// call with no cleanup or terminate edge.
pub(super) fn static_fn_pointer_callee<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    func: &Operand<'tcx>,
    unwind: &mir::UnwindAction,
    span: rustc_span::Span,
) -> Option<Operand<'tcx>> {
    if !panic_is_abort(ctx.tcx)
        || !ctx.eh_active
        || (invoke_like(unwind) && !inlined_terminate_pads::is_inherited(unwind))
    {
        return None;
    }
    let instance = direct_fn_pointer_target(ctx, body, func)?;
    Some(Operand::Constant(Box::new(mir::ConstOperand {
        span,
        user_ty: None,
        const_: mir::Const::zero_sized(crate::fn_items::from_instance(ctx.tcx, instance)),
    })))
}

/// The plain `fn` item or method a call through the `fn` pointer `func`
/// certainly reaches and that a direct call names as the same instance
/// ([`static_fn_pointer_callee`]), whatever frame it is in.
pub(super) fn direct_fn_pointer_target<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    func: &Operand<'tcx>,
) -> Option<Instance<'tcx>> {
    if call_func_is_static_fn_item(ctx, body, func) {
        return None;
    }
    let facts = body_facts(ctx, body);
    let instance = fn_pointer_target(ctx, &facts, body, func, 0)?;
    let ty::InstanceKind::Item(def_id) = instance.def else {
        return None;
    };
    if !matches!(
        ctx.tcx.def_kind(def_id),
        rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
    ) {
        return None;
    }
    let resolved = Instance::try_resolve(
        ctx.tcx,
        ty::TypingEnv::fully_monomorphized(),
        def_id,
        instance.args,
    );
    (resolved == Ok(Some(instance))).then_some(instance)
}

/// The instance the `fn` pointer `operand` of `body` certainly holds: through
/// copies of locals defined once, a reified fn item, a constant pointer to a
/// function, or a load through a constant pointer into an immutable
/// allocation holding one.
pub(super) fn fn_pointer_operand_target<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> Option<Instance<'tcx>> {
    let facts = body_facts(ctx, body);
    fn_pointer_target(ctx, &facts, body, operand, 0)
}

/// The instance the `fn` pointer `operand` certainly holds
/// ([`static_fn_pointer_callee`]).
fn fn_pointer_target<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    facts: &BodyFacts,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
    depth: usize,
) -> Option<Instance<'tcx>> {
    if depth > 8 {
        return None;
    }
    let place = match operand {
        Operand::Constant(constant) => {
            return constant_pointer(ctx, constant)
                .and_then(|(alloc_id, offset)| function_at(ctx, alloc_id, offset));
        }
        Operand::Copy(place) | Operand::Move(place) => place,
        _ => return None,
    };
    if facts.borrowed[place.local.as_usize()] {
        return None;
    }
    let def = facts.single_def(place.local)?;
    let assign = assignment_at(body, def)?;
    match (place.projection.as_slice(), &assign.1) {
        // A load through a constant pointer into an immutable allocation, at
        // the pointer itself or (above O0, where LLVM folds such a load) at a
        // field or constant index inside the pointee.
        ([ProjectionElem::Deref, inner @ ..], Rvalue::Use(Operand::Constant(constant), _)) => {
            if !inner.is_empty() && !ctx.session_optimizes() {
                return None;
            }
            let (alloc_id, offset) = constant_pointer(ctx, constant)?;
            let pointee = ctx
                .monomorphize_ty(constant.const_.ty())
                .builtin_deref(true)?;
            let offset = offset + projection_offset(ctx, facts, body, pointee, inner)?;
            let allocation = match ctx.tcx.try_get_global_alloc(alloc_id)? {
                GlobalAlloc::Static(def_id)
                    if !ctx.tcx.is_thread_local_static(def_id)
                        && !ctx.tcx.is_foreign_item(def_id) =>
                {
                    ctx.tcx.eval_static_initializer(def_id).ok()?
                }
                GlobalAlloc::Memory(allocation) => allocation,
                _ => return None,
            };
            let allocation = allocation.inner();
            if allocation.mutability != rustc_hir::Mutability::Not {
                return None;
            }
            let pointer_size = ctx.tcx.data_layout.pointer_size();
            let Ok(Scalar::Ptr(pointer, _)) =
                allocation.read_scalar(&ctx.tcx, alloc_range(offset, pointer_size), true)
            else {
                return None;
            };
            let (provenance, pointer_offset) = pointer.prov_and_relative_offset();
            function_at(ctx, provenance.alloc_id(), pointer_offset)
        }
        // A field of a struct or tuple this body built once.
        ([ProjectionElem::Field(field, _)], Rvalue::Aggregate(kind, operands)) => {
            let structure = match **kind {
                mir::AggregateKind::Tuple => true,
                mir::AggregateKind::Adt(def_id, _, _, _, None) => {
                    ctx.tcx.adt_def(def_id).is_struct()
                }
                _ => false,
            };
            if !structure {
                return None;
            }
            fn_pointer_target(ctx, facts, body, operands.get(*field)?, depth + 1)
        }
        ([], Rvalue::Cast(mir::CastKind::PointerCoercion(coercion, _), source, _))
            if matches!(coercion, PointerCoercion::ReifyFnPointer(_)) =>
        {
            let source_ty = match source {
                Operand::Constant(constant) => constant.const_.ty(),
                Operand::Copy(source) | Operand::Move(source) => source.ty(body, ctx.tcx).ty,
                _ => return None,
            };
            let item = crate::fn_items::view(ctx.monomorphize_ty(source_ty).kind())?;
            let def_id = item.def_id();
            let args = item.unbound_args()?;
            Instance::resolve_for_fn_ptr(
                ctx.tcx,
                ty::TypingEnv::fully_monomorphized(),
                def_id,
                args,
            )
        }
        ([], Rvalue::Use(source, _)) => fn_pointer_target(ctx, facts, body, source, depth + 1),
        _ => None,
    }
}

/// The byte offset of `projections` (struct or tuple fields, constant
/// indices, indices held by a local assigned one constant) within a value of
/// type `ty`.
fn projection_offset<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    facts: &BodyFacts,
    body: &Body<'tcx>,
    ty: Ty<'tcx>,
    projections: &[mir::PlaceElem<'tcx>],
) -> Option<rustc_abi::Size> {
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let mut ty = ty;
    let mut offset = rustc_abi::Size::ZERO;
    for element in projections {
        let layout = ctx.tcx.layout_of(typing_env.as_query_input(ty)).ok()?;
        match *element {
            ProjectionElem::Field(field, field_ty) => {
                if !matches!(ty.kind(), ty::Adt(adt, _) if adt.is_struct())
                    && !matches!(ty.kind(), ty::Tuple(_))
                {
                    return None;
                }
                offset += layout.fields.offset(field.as_usize());
                ty = ctx.monomorphize_ty(field_ty);
            }
            ProjectionElem::ConstantIndex {
                offset: index,
                from_end: false,
                ..
            } => {
                let element_ty = ty.builtin_index()?;
                let element = ctx
                    .tcx
                    .layout_of(typing_env.as_query_input(element_ty))
                    .ok()?;
                offset += element.size.checked_mul(index, &ctx.tcx)?;
                ty = element_ty;
            }
            ProjectionElem::Index(local) => {
                let element_ty = ty.builtin_index()?;
                let assign = assignment_at(body, facts.single_def(local)?)?;
                let Rvalue::Use(Operand::Constant(constant), _) = &assign.1 else {
                    return None;
                };
                let index = ctx
                    .eval_const_operand(constant)
                    .try_eval_target_usize(ctx.tcx, typing_env)?;
                let element = ctx
                    .tcx
                    .layout_of(typing_env.as_query_input(element_ty))
                    .ok()?;
                offset += element.size.checked_mul(index, &ctx.tcx)?;
                ty = element_ty;
            }
            _ => return None,
        }
    }
    Some(offset)
}

/// The closure `call_once` shim a `fn` pointer `operand` certainly holds: the
/// pointer is, through copies of locals defined once, a non-capturing
/// closure coerced to `fn(..)` (`PointerCoercion::ClosureFnPointer`).
fn closure_pointer_shim<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    facts: &BodyFacts,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> Option<Instance<'tcx>> {
    let mut place = operand.place()?;
    for _ in 0..8 {
        match defining_rvalue(facts, body, place)? {
            Rvalue::Use(Operand::Copy(source) | Operand::Move(source), _) => place = *source,
            Rvalue::Cast(mir::CastKind::PointerCoercion(coercion, _), source, _)
                if matches!(coercion, PointerCoercion::ClosureFnPointer(_)) =>
            {
                let source_ty = match source {
                    Operand::Constant(constant) => constant.const_.ty(),
                    Operand::Copy(source) | Operand::Move(source) => source.ty(body, ctx.tcx).ty,
                    _ => return None,
                };
                let ty::Closure(def_id, args) = *ctx.monomorphize_ty(source_ty).kind() else {
                    return None;
                };
                return Some(Instance::resolve_closure(
                    ctx.tcx,
                    def_id,
                    args,
                    ty::ClosureKind::FnOnce,
                ));
            }
            _ => return None,
        }
    }
    None
}

/// The module-local fn-pointer entry of the closure a call through the `fn`
/// pointer `func` certainly reaches ([`closure_pointer_shim`]), when the frame
/// is a `panic=abort` frame with an exception table and the entry's
/// signature is the call's own `sig`. LLVM calls the closure's `call_once`
/// shim directly (rustc's codegen keeps the coerced constant in an SSA value,
/// as for a reified fn item), which rustc declares `nounwind` under
/// `panic=abort`; the entry calls the closure body, which cannot unwind
/// either, so it is recorded `nounwind`.
pub(super) fn known_closure_entry<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    func: &Operand<'tcx>,
    unwind: &mir::UnwindAction,
    sig: trust_ir::FuncTyId,
) -> Option<FuncId> {
    if !panic_is_abort(ctx.tcx)
        || !ctx.eh_active
        || (invoke_like(unwind) && !inlined_terminate_pads::is_inherited(unwind))
    {
        return None;
    }
    let facts = body_facts(ctx, body);
    let shim = closure_pointer_shim(ctx, &facts, body, func)?;
    let entry = ctx.closure_fn_pointer_entry(shim).ok()?;
    let entry_ty = ctx.module.function_by_id(entry)?.ty;
    if ctx.module.func_type(entry_ty)? != ctx.module.func_type(sig)? {
        return None;
    }
    ctx.note_synthesized_call_nounwind(entry);
    Some(entry)
}

/// The assignment statement at `location`, if it is one.
fn assignment_at<'a, 'tcx>(
    body: &'a Body<'tcx>,
    location: mir::Location,
) -> Option<&'a (Place<'tcx>, Rvalue<'tcx>)> {
    let data = body.basic_blocks.get(location.block)?;
    match &data.statements.get(location.statement_index)?.kind {
        StatementKind::Assign(assign) => Some(&**assign),
        _ => None,
    }
}

/// The allocation and offset a pointer constant points to.
fn constant_pointer<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    constant: &mir::ConstOperand<'tcx>,
) -> Option<(AllocId, rustc_abi::Size)> {
    let Scalar::Ptr(pointer, _) = ctx.eval_const_operand(constant).try_to_scalar()? else {
        return None;
    };
    let (provenance, offset) = pointer.prov_and_relative_offset();
    Some((provenance.alloc_id(), offset))
}

/// The function a pointer to `alloc_id` at `offset` is the address of.
fn function_at<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    alloc_id: AllocId,
    offset: rustc_abi::Size,
) -> Option<Instance<'tcx>> {
    match ctx.tcx.try_get_global_alloc(alloc_id)? {
        GlobalAlloc::Function { instance } if offset.bytes() == 0 => Some(instance),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Virtual calls through a vtable this body built
// ---------------------------------------------------------------------------
//
// Above O0 LLVM folds the method load from a constant vtable once it sees the
// unsizing that built the trait object (`let o: &dyn Tk = &k; o.k(2)`, `&dyn
// Fn` of a closure: measured at O1-O3), and calls the concrete method
// directly; at O0 the load stays and the call is indirect. A `Box<dyn Fn>`
// call is a direct call at every level: at O0 to the `nounwind` `<Box<F> as
// Fn>::call`, above O0 the devirtualized method after inlining it (measured:
// `Box::new(nw)` as `Box<dyn Fn(u64) -> u64>` at O0-O3). LLVM's table then
// reads the method's own `nounwind`. Such a call is lowered as the direct call
// to the very function the vtable holds, with the vtable call's own
// arguments.

/// The direct target of a virtual call ([`known_vtable_callee`]).
pub(super) struct VtableCallee {
    /// The function the receiver's vtable holds at the called slot, declared.
    pub(super) func: FuncId,
    /// The slot holds a shim over a fn item (`ShimKind::FnPtr`), which calls
    /// the item with the untupled arguments alone: the target takes the vtable
    /// call's arguments without its leading receiver.
    drops_receiver: bool,
    /// The pointer type the target declares its receiver as, where it is not
    /// the vtable call's untyped `Ptr` (`&Known` is `Ref(..)`): the same
    /// address, retyped with a `PtrToPtr` cast.
    receiver_ty: Option<TrustIrTy>,
}

impl VtableCallee {
    /// The direct call's arguments from the vtable call's `args` (receiver
    /// first), emitting the receiver's retyping cast into `block`.
    pub(super) fn args(
        &self,
        ctx: &mut MirLoweringCtx<'_>,
        block: &mut Block,
        args: &[ValueId],
    ) -> Vec<ValueId> {
        let Some((receiver, rest)) = args.split_first() else {
            return Vec::new();
        };
        if self.drops_receiver {
            return rest.to_vec();
        }
        let receiver = match &self.receiver_ty {
            Some(ty) => {
                let retyped = ctx.fresh_value();
                block.body.push(
                    InstrNode::new(Inst::Cast {
                        op: CastOp::PtrToPtr,
                        src_ty: TrustIrTy::Ptr,
                        dst_ty: ty.clone(),
                        operand: *receiver,
                    })
                    .with_result(retyped),
                );
                retyped
            }
            None => *receiver,
        };
        std::iter::once(receiver)
            .chain(rest.iter().copied())
            .collect()
    }
}

/// The function a virtual call to `dyn_method` (an `InstanceKind::Virtual`)
/// through `receiver` certainly reaches, when this body built the receiver
/// from a known concrete type: a `&T` unsized to `&dyn Trait` (`boxed` false;
/// above O0 only, as LLVM), or a `Box<T>` unsized to `Box<dyn Fn*>` that the
/// call borrows (`boxed` true; every level), through locals defined once. The
/// slot must hold a plain method or closure body, or a shim over a fn item,
/// with no caller location, whose declared signature is the vtable call's own
/// `sig` (less the receiver for a shim); anything else, and any call outside a
/// `panic=abort` frame with an exception table, keeps the indirect call.
pub(super) fn known_vtable_callee<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    receiver: &Operand<'tcx>,
    unwind: &mir::UnwindAction,
    dyn_method: Instance<'tcx>,
    sig: trust_ir::FuncTyId,
    boxed: bool,
) -> Option<VtableCallee> {
    if !panic_is_abort(ctx.tcx)
        || !ctx.eh_active
        || invoke_like(unwind)
        || !(boxed || ctx.session_optimizes())
    {
        return None;
    }
    let ty::InstanceKind::Virtual(_, index) = dyn_method.def else {
        return None;
    };
    let ty::Dynamic(predicates, ..) = *dyn_method.args.type_at(0).kind() else {
        return None;
    };
    let principal = predicates.principal()?;
    let facts = body_facts(ctx, body);
    let self_ty = receiver_concrete_type(ctx, &facts, body, receiver, boxed)?;
    let trait_ref = ctx
        .tcx
        .instantiate_bound_regions_with_erased(principal.with_self_ty(ctx.tcx, self_ty));
    let trait_ref = ctx.tcx.erase_and_anonymize_regions(trait_ref);
    let entry = match ctx.tcx.vtable_entries(trait_ref).get(index)? {
        ty::VtblEntry::Method(entry) => *entry,
        _ => return None,
    };
    let (target, drops_receiver) = match entry.def {
        ty::InstanceKind::Item(_) => (entry, false),
        ty::InstanceKind::Shim(ty::ShimKind::FnPtr(_, shim_ty)) => {
            let item = crate::fn_items::view(shim_ty.kind())?;
            let def_id = item.def_id();
            let args = item.unbound_args()?;
            if !matches!(
                ctx.tcx.def_kind(def_id),
                rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
            ) {
                return None;
            }
            let target =
                Instance::try_resolve(ctx.tcx, ty::TypingEnv::fully_monomorphized(), def_id, args)
                    .ok()
                    .flatten()?;
            (target, true)
        }
        _ => return None,
    };
    if !matches!(target.def, ty::InstanceKind::Item(_))
        || instance_abi_has_caller_location(ctx.tcx, target)
    {
        return None;
    }
    let wanted = ctx.func_ty_for_instance(target).ok()?;
    // The vtable call's signature less its receiver for a shim, and with the
    // receiver retyped to the target's own pointer type otherwise; every other
    // parameter and the return must be the very types the target declares.
    let (wanted, called) = (ctx.module.func_type(wanted)?, ctx.module.func_type(sig)?);
    if wanted.returns != called.returns || wanted.is_vararg || called.is_vararg {
        return None;
    }
    let receiver_ty = if drops_receiver {
        if called.params.get(1..)? != wanted.params.as_slice() {
            return None;
        }
        None
    } else {
        let (Some((called_receiver, called_rest)), Some((wanted_receiver, wanted_rest))) =
            (called.params.split_first(), wanted.params.split_first())
        else {
            return None;
        };
        if called_rest != wanted_rest
            || *called_receiver != TrustIrTy::Ptr
            || !is_pointer_like_trust_ir_ty(wanted_receiver)
        {
            return None;
        }
        (*wanted_receiver != TrustIrTy::Ptr).then(|| wanted_receiver.clone())
    };
    let func = ctx.extern_callee(target).ok()?;
    Some(VtableCallee {
        func,
        drops_receiver,
        receiver_ty,
    })
}

/// The thunk a `Box<dyn Fn*>` call whose vtable this body cannot name is made
/// through at O0, recorded `nounwind`. At O0 LLVM calls `<Box<F, A> as
/// Fn<Args>>::call` itself, a direct call rustc declares `nounwind` under
/// `panic=abort` (the vtable call happens inside that frame), so the region is
/// a gap whatever the box holds; this lowering's vtable call would cover it.
/// The thunk (`indirect_unwind_thunk`, a module-local function that makes the
/// indirect call) is that frame. Above O0 LLVM inlines the impl and the
/// indirect call is its own, covered, unless it learns the vtable.
pub(super) fn box_dyn_call_thunk<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    unwind: &mir::UnwindAction,
    sig: trust_ir::FuncTyId,
) -> Option<FuncId> {
    if !panic_is_abort(ctx.tcx)
        || !ctx.eh_active
        || ctx.session_optimizes()
        || (invoke_like(unwind) && !inlined_terminate_pads::is_inherited(unwind))
    {
        return None;
    }
    let thunk = ctx.indirect_unwind_thunk(sig).ok()?;
    ctx.note_synthesized_call_nounwind(thunk);
    Some(thunk)
}

/// The concrete type behind a virtual call's `receiver` ([`known_vtable_callee`]):
/// following, through locals defined once, copies, a reborrow `&(*p)`, a
/// transmute or pointer cast between pointers to the same `dyn` type, and a
/// read of a `Box` / `Unique` / `NonNull`'s pointer field, back to the
/// unsizing of a pointer to a sized, non-`dyn` type. For a `boxed` call the
/// receiver is first the borrow of the box.
fn receiver_concrete_type<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    facts: &BodyFacts,
    body: &Body<'tcx>,
    receiver: &Operand<'tcx>,
    boxed: bool,
) -> Option<Ty<'tcx>> {
    let mut place = receiver.place()?;
    if boxed {
        let Rvalue::Ref(_, _, borrowed) = defining_rvalue(facts, body, place)? else {
            return None;
        };
        place = *borrowed;
    }
    for _ in 0..12 {
        place = pointer_field_base(ctx, body, place)?;
        match defining_rvalue(facts, body, place)? {
            Rvalue::Use(Operand::Copy(source) | Operand::Move(source), _) => place = *source,
            Rvalue::Ref(_, _, borrowed) => match borrowed.projection.as_slice() {
                [ProjectionElem::Deref] => place = Place::from(borrowed.local),
                _ => return None,
            },
            Rvalue::Cast(
                mir::CastKind::Transmute | mir::CastKind::PtrToPtr,
                Operand::Copy(source) | Operand::Move(source),
                target_ty,
            ) => {
                let source_ty = ctx.monomorphize_ty(source.ty(body, ctx.tcx).ty);
                let target_ty = ctx.monomorphize_ty(*target_ty);
                let same_object = match (
                    dyn_pointee(ctx.tcx, source_ty),
                    dyn_pointee(ctx.tcx, target_ty),
                ) {
                    (Some(from), Some(to)) => from == to && matches!(from.kind(), ty::Dynamic(..)),
                    _ => false,
                };
                if !same_object {
                    return None;
                }
                place = *source;
            }
            Rvalue::Cast(mir::CastKind::PointerCoercion(PointerCoercion::Unsize, _), source, _) => {
                let source_ty = match source {
                    Operand::Copy(source) | Operand::Move(source) => source.ty(body, ctx.tcx).ty,
                    // A promoted constant reference (`let o: &dyn Tr = &S;`).
                    Operand::Constant(constant) => constant.const_.ty(),
                    _ => return None,
                };
                let source_ty = ctx.monomorphize_ty(source_ty);
                let pointee = dyn_pointee(ctx.tcx, source_ty)?;
                let sized = pointee.is_sized(ctx.tcx, ty::TypingEnv::fully_monomorphized());
                return (sized && !matches!(pointee.kind(), ty::Dynamic(..))).then_some(pointee);
            }
            _ => return None,
        }
    }
    None
}

/// The pointee of a pointer type: a reference, a raw pointer, a `Box`, or a
/// pointer wrapper ([`is_pointer_wrapper`]: its first type argument).
fn dyn_pointee<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    match *ty.kind() {
        ty::Ref(_, pointee, _) | ty::RawPtr(pointee, _) => Some(pointee),
        ty::Adt(adt, args) if ty.is_box() || is_pointer_wrapper(tcx, adt, args) => {
            args.types().next()
        }
        _ => None,
    }
}

/// Whether `adt<args>` IS a pointer to its first type argument: core's
/// `NonNull<T>` (by its diagnostic item, never its name), or a transparent
/// struct whose field is `NonNull<T>` for that same `T` (core's `Unique<T>`).
/// Other transparent wrappers hold their first argument by value (`Pin<P>`
/// holds the pointer `P`, `Cell<T>` a `T`), so it is not their pointee.
fn is_pointer_wrapper<'tcx>(
    tcx: TyCtxt<'tcx>,
    adt: ty::AdtDef<'tcx>,
    args: crate::fn_items::GenericArgsRef<'tcx>,
) -> bool {
    let non_null = tcx.get_diagnostic_item(rustc_span::Symbol::intern("NonNull"));
    if non_null.is_some() && Some(adt.did()) == non_null {
        return true;
    }
    let Some(pointee) = args.types().next() else {
        return false;
    };
    adt.is_struct()
        && adt.repr().transparent()
        && adt.non_enum_variant().fields.iter().any(|field| {
            matches!(
                *super::normalized_adt_field_ty(tcx, field, args).kind(),
                ty::Adt(inner, inner_args)
                    if non_null.is_some()
                        && Some(inner.did()) == non_null
                        && inner_args.types().next() == Some(pointee)
            )
        })
}

/// `place` with a trailing read of a pointer wrapper's field removed: the
/// pointer field of a `Box`, `Unique` or `NonNull` holds the same fat pointer
/// (the same vtable) as the wrapper. Any other projection is not followed.
fn pointer_field_base<'tcx>(
    ctx: &MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    place: Place<'tcx>,
) -> Option<Place<'tcx>> {
    let mut base = Place::from(place.local);
    for element in place.projection.iter() {
        let ProjectionElem::Field(..) = element else {
            return None;
        };
        let base_ty = ctx.monomorphize_ty(base.ty(body, ctx.tcx).ty);
        let wrapper = match base_ty.kind() {
            ty::Adt(adt, args) => base_ty.is_box() || is_pointer_wrapper(ctx.tcx, *adt, *args),
            _ => false,
        };
        if !wrapper {
            return None;
        }
        base = base.project_deeper(&[element], ctx.tcx);
    }
    Some(Place::from(place.local))
}

/// The rvalue that defines the whole local `place` once, when `place` is a
/// bare local with a single definition that nothing else mutates.
fn defining_rvalue<'a, 'tcx>(
    facts: &BodyFacts,
    body: &'a Body<'tcx>,
    place: Place<'tcx>,
) -> Option<&'a Rvalue<'tcx>> {
    if !place.projection.is_empty() {
        return None;
    }
    let def = facts.single_def(place.local)?;
    assignment_at(body, def).map(|assign| &assign.1)
}
