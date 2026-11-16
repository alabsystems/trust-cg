//! Locals whose ADDRESS may outlive the statement or call that received it.
//!
//! The bridge keeps most locals in SSA registers. A `&mut local` handed to a
//! call is materialized in a temporary slot for the call and reloaded after it
//! (`lower_scalar_reference_call_arg`), which is exact only while nobody writes
//! through that address after the call returns. A callee that KEEPS the address
//! (stores it in a static or an out-parameter, returns a pointer derived from
//! it, exposes it as an integer) breaks that: a later write through the kept
//! address lands in the dead temporary, and a later read of the local reads its
//! stale register copy. LLVM keeps such an escaped alloca in memory; this
//! analysis finds the same locals so the lowering can give each one a memory
//! home (`compute_memory_backed_locals` rule 4r, `compute_scalar_cell_locals`)
//! and read it through memory everywhere, or refuse the function by name.
//!
//! The analysis is a flow-insensitive points-to over abstract objects. A local
//! of the analyzed body is an object; a pointer value's points-to set is the
//! set of objects it may address. An object ESCAPES when a pointer to it may be
//! kept beyond the analyzed body's view:
//!
//! * it is stored through a pointer (any assignment whose destination place
//!   dereferences, and the destination of `copy_nonoverlapping`);
//! * its address is exposed (`ptr as usize`, `PointerExposeProvenance`), or an
//!   integer carrying it is turned back into a pointer (`usize as *mut T`, an
//!   integer-to-pointer `transmute`), since such a pointer is not tracked;
//! * it reaches an argument of a call whose callee is not PROVEN to keep only
//!   what it may keep (see below), a dropped value, inline assembly or a
//!   coroutine `yield`.
//!
//! Everything reachable from an escaped object escapes too. A plain read or
//! write through a pointer, a comparison of addresses, and an address turned
//! into an integer inside the analyzed body (a transmute or a pointer-to-address
//! cast that never becomes a pointer again) keep nothing. A call is judged by
//! its callee's summary instead, and a callee's return value counts as kept
//! (see below), so a local whose address reaches a pointer helper that is a
//! call here (`p.addr()`, `p.add(1)`, `p.wrapping_add(0)`, `a.as_mut_ptr()`)
//! is given a home: conservative, never unsound. A local that escapes only
//! through SHARED borrows of a `Freeze` type needs no home: nothing may write
//! through such a pointer (see [`retained_address_locals`]).
//!
//! Callees. A callee with MIR (a crate-local function, an inlinable or generic
//! foreign one, a closure body, a drop/closure/fn-pointer/vtable shim) is
//! summarized by the same analysis, run with each argument as an object: per
//! argument, whether the callee may keep the argument's pointers themselves
//! (`ArgCapture::Address`), may keep only pointers it READS through them
//! (`ArgCapture::Contents`), or keeps neither. Returning a value counts as
//! keeping it: the caller does not track a returned pointer back to its origin.
//! Recursive callees are summarized together as the least fixpoint of their
//! monotone system, which is sound for a may-escape property. A callee without
//! MIR, a virtual (`dyn`) or function-pointer call, an intrinsic outside the
//! table in [`intrinsic_summary`], and a callee whose reach exceeds
//! [`MAX_SUMMARY_REACH`] instances keep every argument (`CalleeSummary::All`).

use super::*;
use std::collections::{BTreeMap, BTreeSet};

/// The most instances one summary request may add to the summaries of the body
/// being lowered (the callee included; callees that body already summarized
/// are not counted or walked) before the request gives up and keeps every
/// argument. The bound keeps a pathological call graph from dominating a
/// compile; the fallback is the conservative answer. Exact summaries are solved
/// once per crate, callees first (see [`SummaryMemo`]), so a chain of calls
/// costs one analysis per body.
const MAX_SUMMARY_REACH: usize = 1024;

/// An object an address may name.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Obj {
    /// A local of the analyzed body, and whether a pointer to it may be written
    /// through: `false` only for a pointer made by a SHARED borrow (`&local`,
    /// `&(*p).f`), through which no write is allowed.
    Local(Local, bool),
    /// Callee summaries only: an object a pointer in argument `i`'s value
    /// addresses directly.
    Arg(usize),
    /// Callee summaries only: anything reachable from [`Obj::Arg`] `i` by
    /// reading memory.
    ArgDeep(usize),
}

/// What a callee may keep of one argument, ordered by strength.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum ArgCapture {
    /// Neither the argument's pointers nor anything read through them.
    None,
    /// Pointers the callee READS through the argument's pointers, not the
    /// argument's pointers themselves.
    Contents,
    /// The argument's pointers themselves (and so everything behind them).
    Address,
}

/// A callee's [`ArgCapture`] per MIR argument.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum CalleeSummary {
    /// Every argument may be kept whole.
    All,
    /// One entry per argument; an argument past the end is kept whole.
    Args(Vec<ArgCapture>),
}

impl CalleeSummary {
    fn arg(&self, index: usize) -> ArgCapture {
        match self {
            CalleeSummary::All => ArgCapture::Address,
            CalleeSummary::Args(args) => args.get(index).copied().unwrap_or(ArgCapture::Address),
        }
    }
}

/// Why an object escaped (for the refusal text and the trace).
#[derive(Clone, Debug)]
enum EscapeReason {
    StoredThroughPointer,
    CopiedIntoMemory,
    Exposed,
    IntegerToPointer,
    CallArgument { callee: Option<DefId>, index: usize },
    Dropped,
    InlineAsm,
    Yielded,
    Returned,
    Reachable(Local),
}

impl EscapeReason {
    fn describe(&self, tcx: TyCtxt<'_>) -> String {
        match self {
            EscapeReason::StoredThroughPointer => {
                "its address is stored through a pointer".to_owned()
            }
            EscapeReason::CopiedIntoMemory => {
                "its address is copied into memory by `copy_nonoverlapping`".to_owned()
            }
            EscapeReason::Exposed => "its address is exposed as an integer".to_owned(),
            EscapeReason::IntegerToPointer => {
                "an integer carrying its address is turned back into a pointer".to_owned()
            }
            EscapeReason::CallArgument { callee, index } => {
                let callee = match callee {
                    // Untrimmed paths: a trimmed path must not be computed
                    // outside a diagnostic.
                    Some(def_id) => {
                        rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(*def_id))
                    }
                    None => "an indirect callee".to_owned(),
                };
                format!("its address reaches argument {index} of `{callee}`, which may keep it")
            }
            EscapeReason::Dropped => "its address is held by a dropped value".to_owned(),
            EscapeReason::InlineAsm => "its address is an inline-assembly operand".to_owned(),
            EscapeReason::Yielded => "its address is yielded by a coroutine".to_owned(),
            EscapeReason::Returned => "its address is returned".to_owned(),
            EscapeReason::Reachable(from) => {
                format!("its address is reachable from escaped local {from:?}")
            }
        }
    }
}

/// Whether a value of `ty` can carry no address at all: primitive scalars and
/// arrays/tuples of them.
fn ty_is_address_free<'tcx>(ty: Ty<'tcx>) -> bool {
    match ty.kind() {
        ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Bool | ty::Char | ty::Never => true,
        ty::Array(elem, _) => ty_is_address_free(*elem),
        ty::Tuple(elems) => elems.iter().all(ty_is_address_free),
        _ => false,
    }
}

/// The points-to state of one body.
struct Flow<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    body: &'a Body<'tcx>,
    pts: Vec<BTreeSet<Obj>>,
}

impl<'a, 'tcx> Flow<'a, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>, body: &'a Body<'tcx>, args: bool) -> Self {
        let mut pts = vec![BTreeSet::new(); body.local_decls.len()];
        if args {
            for index in 0..body.arg_count {
                pts[index + 1].insert(Obj::Arg(index));
            }
        }
        let mut flow = Flow {
            tcx,
            instance,
            body,
            pts,
        };
        flow.solve();
        flow
    }

    fn mono(&self, ty: Ty<'tcx>) -> Ty<'tcx> {
        self.instance.instantiate_mir_and_normalize_erasing_regions(
            self.tcx,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(self.tcx, ty),
        )
    }

    fn contents(&self, obj: Obj) -> BTreeSet<Obj> {
        match obj {
            Obj::Local(local, _) => self.pts[local.index()].clone(),
            Obj::Arg(index) | Obj::ArgDeep(index) => BTreeSet::from([Obj::ArgDeep(index)]),
        }
    }

    fn contents_of(&self, objs: &BTreeSet<Obj>) -> BTreeSet<Obj> {
        let mut out = BTreeSet::new();
        for obj in objs {
            out.extend(self.contents(*obj));
        }
        out
    }

    /// The objects the place's storage may belong to.
    fn place_addr(&self, place: &Place<'tcx>) -> BTreeSet<Obj> {
        let mut cur = BTreeSet::from([Obj::Local(place.local, true)]);
        for elem in place.projection.iter() {
            if matches!(elem, ProjectionElem::Deref) {
                cur = self.contents_of(&cur);
            }
        }
        cur
    }

    /// The objects a value read from the place may address.
    fn place_value(&self, place: &Place<'tcx>) -> BTreeSet<Obj> {
        self.contents_of(&self.place_addr(place))
    }

    fn operand_value(&self, operand: &Operand<'tcx>) -> BTreeSet<Obj> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.place_value(place),
            _ => BTreeSet::new(),
        }
    }

    fn rvalue_value(&self, rvalue: &Rvalue<'tcx>) -> BTreeSet<Obj> {
        match rvalue {
            Rvalue::Use(op, _)
            | Rvalue::Repeat(op, _)
            | Rvalue::Cast(_, op, _)
            | Rvalue::WrapUnsafeBinder(op, _) => self.operand_value(op),
            Rvalue::UnaryOp(mir::UnOp::PtrMetadata, _) => BTreeSet::new(),
            Rvalue::UnaryOp(_, op) => self.operand_value(op),
            Rvalue::BinaryOp(op, boxed) => match op {
                mir::BinOp::Eq
                | mir::BinOp::Ne
                | mir::BinOp::Lt
                | mir::BinOp::Le
                | mir::BinOp::Gt
                | mir::BinOp::Ge
                | mir::BinOp::Cmp => BTreeSet::new(),
                _ => {
                    let mut out = self.operand_value(&boxed.0);
                    out.extend(self.operand_value(&boxed.1));
                    out
                }
            },
            // A shared borrow's pointer cannot be written through; every other
            // borrow keeps the writability of the place's storage.
            Rvalue::Ref(_, mir::BorrowKind::Shared | mir::BorrowKind::Fake(_), place) => self
                .place_addr(place)
                .into_iter()
                .map(|obj| match obj {
                    Obj::Local(local, _) => Obj::Local(local, false),
                    other => other,
                })
                .collect(),
            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) | Rvalue::Reborrow(_, _, place) => {
                self.place_addr(place)
            }
            Rvalue::CopyForDeref(place) => self.place_value(place),
            Rvalue::Aggregate(_, operands) => {
                let mut out = BTreeSet::new();
                for op in operands {
                    out.extend(self.operand_value(op));
                }
                out
            }
            Rvalue::Discriminant(_) | Rvalue::ThreadLocalRef(_) => BTreeSet::new(),
        }
    }

    /// The flow-insensitive fixpoint of every assignment into a body local.
    /// A store through a pointer and a call destination add nothing here: the
    /// first is an escape, and a callee returns no pointer to this body's
    /// objects that the argument summaries have not already counted.
    fn solve(&mut self) {
        loop {
            let mut changed = false;
            for data in self.body.basic_blocks.iter() {
                for statement in &data.statements {
                    let StatementKind::Assign(boxed) = &statement.kind else {
                        continue;
                    };
                    let (dst, rvalue) = &**boxed;
                    if dst
                        .projection
                        .iter()
                        .any(|elem| matches!(elem, ProjectionElem::Deref))
                    {
                        continue;
                    }
                    let value = self.rvalue_value(rvalue);
                    if value.is_empty() {
                        continue;
                    }
                    let entry = &mut self.pts[dst.local.index()];
                    for obj in value {
                        changed |= entry.insert(obj);
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    fn operand_ty(&self, operand: &Operand<'tcx>) -> Ty<'tcx> {
        self.mono(operand.ty(&self.body.local_decls, self.tcx))
    }

    /// Every escape of the body, given each call's callee summary.
    /// `summarize` answers a call's callee summary and shape given the call's
    /// argument values, or `None` when the caller does not need that call's
    /// escapes at all (see [`retained_address_locals`]); the call then
    /// contributes no seed.
    fn escapes(
        &self,
        summarize: &mut dyn FnMut(
            &Flow<'a, 'tcx>,
            &Operand<'tcx>,
            &[BTreeSet<Obj>],
        ) -> Option<(CalleeSummary, CallShape)>,
        returned: bool,
    ) -> Vec<(BTreeSet<Obj>, EscapeReason)> {
        let mut out: Vec<(BTreeSet<Obj>, EscapeReason)> = Vec::new();
        let mut push = |set: BTreeSet<Obj>, reason: EscapeReason| {
            if !set.is_empty() {
                out.push((set, reason));
            }
        };
        for data in self.body.basic_blocks.iter() {
            for statement in &data.statements {
                match &statement.kind {
                    StatementKind::Assign(boxed) => {
                        let (dst, rvalue) = &**boxed;
                        if dst
                            .projection
                            .iter()
                            .any(|elem| matches!(elem, ProjectionElem::Deref))
                        {
                            push(
                                self.rvalue_value(rvalue),
                                EscapeReason::StoredThroughPointer,
                            );
                        }
                        match rvalue {
                            Rvalue::Cast(mir::CastKind::PointerExposeProvenance, op, _) => {
                                push(self.operand_value(op), EscapeReason::Exposed);
                            }
                            Rvalue::Cast(mir::CastKind::PointerWithExposedProvenance, op, _) => {
                                push(self.operand_value(op), EscapeReason::IntegerToPointer);
                            }
                            Rvalue::Cast(mir::CastKind::Transmute, op, dst_ty) => {
                                if ty_is_address_free(self.operand_ty(op))
                                    && !ty_is_address_free(self.mono(*dst_ty))
                                {
                                    push(self.operand_value(op), EscapeReason::IntegerToPointer);
                                }
                            }
                            _ => {}
                        }
                    }
                    StatementKind::Intrinsic(intrinsic) => {
                        if let mir::NonDivergingIntrinsic::CopyNonOverlapping(copy) = &**intrinsic {
                            let copied = self.contents_of(&self.operand_value(&copy.src));
                            push(copied, EscapeReason::CopiedIntoMemory);
                        }
                    }
                    StatementKind::FakeRead(_)
                    | StatementKind::SetDiscriminant { .. }
                    | StatementKind::StorageLive(_)
                    | StatementKind::StorageDead(_)
                    | StatementKind::PlaceMention(_)
                    | StatementKind::AscribeUserType(_, _)
                    | StatementKind::Coverage(_)
                    | StatementKind::ConstEvalCounter
                    | StatementKind::BackwardIncompatibleDropHint { .. }
                    | StatementKind::Nop => {}
                }
            }
            match &data.terminator().kind {
                TerminatorKind::Call { func, args, .. }
                | TerminatorKind::TailCall { func, args, .. } => {
                    let values: Vec<BTreeSet<Obj>> = args
                        .iter()
                        .map(|arg| self.operand_value(&arg.node))
                        .collect();
                    if values.iter().all(BTreeSet::is_empty) {
                        continue;
                    }
                    let Some((summary, shape)) = summarize(self, func, &values) else {
                        continue;
                    };
                    for (index, value) in values.into_iter().enumerate() {
                        let capture = shape.capture(&summary, index);
                        let reason = EscapeReason::CallArgument {
                            callee: shape.callee,
                            index,
                        };
                        match capture {
                            ArgCapture::Address => push(value, reason),
                            ArgCapture::Contents => push(self.contents_of(&value), reason),
                            ArgCapture::None => {}
                        }
                    }
                }
                TerminatorKind::Drop { place, .. } => {
                    push(self.place_value(place), EscapeReason::Dropped);
                }
                TerminatorKind::InlineAsm { operands, .. } => {
                    for operand in operands.iter() {
                        match operand {
                            mir::InlineAsmOperand::In { value, .. } => {
                                push(self.operand_value(value), EscapeReason::InlineAsm);
                            }
                            mir::InlineAsmOperand::InOut { in_value, .. } => {
                                push(self.operand_value(in_value), EscapeReason::InlineAsm);
                            }
                            _ => {}
                        }
                    }
                }
                TerminatorKind::Yield { value, .. } => {
                    push(self.operand_value(value), EscapeReason::Yielded);
                }
                TerminatorKind::Return => {
                    if returned {
                        push(
                            self.pts[mir::RETURN_PLACE.index()].clone(),
                            EscapeReason::Returned,
                        );
                    }
                }
                TerminatorKind::Goto { .. }
                | TerminatorKind::SwitchInt { .. }
                | TerminatorKind::UnwindResume
                | TerminatorKind::UnwindTerminate(_)
                | TerminatorKind::Unreachable
                | TerminatorKind::Assert { .. }
                | TerminatorKind::CoroutineDrop
                | TerminatorKind::FalseEdge { .. }
                | TerminatorKind::FalseUnwind { .. } => {}
            }
        }
        out
    }

    /// Close `seeds` under [`Flow::contents`]: everything a holder of an
    /// escaped address can read escapes too. Returns each object with the first
    /// reason it escaped for.
    fn close(&self, seeds: Vec<(BTreeSet<Obj>, EscapeReason)>) -> BTreeMap<Obj, EscapeReason> {
        let mut escaped: BTreeMap<Obj, EscapeReason> = BTreeMap::new();
        let mut work: Vec<Obj> = Vec::new();
        for (set, reason) in seeds {
            for obj in set {
                if !escaped.contains_key(&obj) {
                    escaped.insert(obj, reason.clone());
                    work.push(obj);
                }
            }
        }
        while let Some(obj) = work.pop() {
            let from = match obj {
                Obj::Local(local, _) => Some(local),
                _ => None,
            };
            for next in self.contents(obj) {
                if !escaped.contains_key(&next) {
                    let reason = match from {
                        Some(local) => EscapeReason::Reachable(local),
                        None => escaped[&obj].clone(),
                    };
                    escaped.insert(next, reason);
                    work.push(next);
                }
            }
        }
        escaped
    }
}

/// How a call's operands map onto the callee's MIR arguments.
#[derive(Clone, Debug)]
pub(super) struct CallShape {
    callee: Option<DefId>,
    /// The callee body takes the closure-call tuple UNTUPLED: operand 1 (the
    /// argument tuple) feeds MIR arguments `1..`.
    untupled: bool,
}

impl CallShape {
    fn capture(&self, summary: &CalleeSummary, index: usize) -> ArgCapture {
        match (self.untupled, summary) {
            (true, CalleeSummary::Args(args)) if index == 1 => args
                .iter()
                .skip(1)
                .copied()
                .max()
                .unwrap_or(ArgCapture::None),
            (true, CalleeSummary::Args(_)) if index > 1 => ArgCapture::Address,
            _ => summary.arg(index),
        }
    }
}

/// The fixed summary of an intrinsic, by name. Arguments of an intrinsic whose
/// every input is address-free carry nothing it could keep; every other
/// intrinsic not listed keeps all its arguments.
fn intrinsic_summary<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>) -> CalleeSummary {
    use ArgCapture::{Address, Contents, None as Keep0};
    let name = tcx.item_name(instance.def_id());
    let name = name.as_str();
    let sig = tcx.instantiate_bound_regions_with_erased(
        instance
            .ty(tcx, ty::TypingEnv::fully_monomorphized())
            .fn_sig(tcx),
    );
    let inputs = sig.inputs();
    let n = inputs.len();
    if inputs.iter().all(|ty| ty_is_address_free(*ty)) {
        return CalleeSummary::Args(vec![Keep0; n]);
    }
    let args = |v: &[ArgCapture]| {
        if v.len() == n {
            CalleeSummary::Args(v.to_vec())
        } else {
            CalleeSummary::All
        }
    };
    match name {
        // Pure reads or measurements of the pointee.
        "size_of_val"
        | "align_of_val"
        | "min_align_of_val"
        | "compare_bytes"
        | "raw_eq"
        | "ptr_guaranteed_cmp"
        | "ptr_offset_from"
        | "ptr_offset_from_unsigned"
        | "discriminant_value"
        | "assume"
        | "abort"
        | "unreachable"
        | "cold_path"
        | "likely"
        | "unlikely" => CalleeSummary::Args(vec![Keep0; n]),
        // The value read back is the pointee's contents.
        "volatile_load" | "unaligned_volatile_load" | "read_via_copy" => args(&[Contents]),
        n2 if n2.starts_with("atomic_load") => args(&[Contents]),
        // Stores: the stored value is kept by the pointee; the old value read
        // back is its contents.
        "volatile_store" | "unaligned_volatile_store" | "write_via_move" => {
            args(&[Contents, Address])
        }
        n2 if n2.starts_with("atomic_store") => args(&[Contents, Address]),
        n2 if n2.starts_with("atomic_cxchg") => args(&[Contents, Address, Address]),
        n2 if [
            "atomic_xchg",
            "atomic_xadd",
            "atomic_xsub",
            "atomic_and",
            "atomic_nand",
        ]
        .iter()
        .chain(["atomic_or", "atomic_xor", "atomic_max", "atomic_min"].iter())
        .chain(["atomic_umax", "atomic_umin"].iter())
        .any(|p| n2.starts_with(p)) =>
        {
            args(&[Contents, Address])
        }
        // Copies between pointees: the source's contents land in memory.
        "copy" | "copy_nonoverlapping" => args(&[Contents, Keep0, Keep0]),
        "volatile_copy_memory" | "volatile_copy_nonoverlapping_memory" => {
            args(&[Keep0, Contents, Keep0])
        }
        "typed_swap_nonoverlapping" => args(&[Contents, Contents]),
        "write_bytes" | "volatile_set_memory" => args(&[Keep0, Keep0, Keep0]),
        _ => CalleeSummary::All,
    }
}

/// Exact callee summaries for one crate compile, shared by every lowered body.
///
/// The summaries a body sees are its own ([`Summaries::done`]): a request that
/// would add more than [`MAX_SUMMARY_REACH`] instances to them answers
/// [`CalleeSummary::All`], and every other request is the least fixpoint of the
/// summaries it adds, read against the ones the body already holds. Which
/// requests the cap shapes therefore depends on the body and on the order of
/// its calls, so a capped answer, and every summary solved against one, stays
/// in that body. Every other summary is EXACT: the least fixpoint of the whole
/// system of its reach, a function of the callees' `tcx.instance_mir` alone.
/// Only exact summaries are kept here, and a strongly connected component whose
/// outside callees are all exact takes its summaries from here instead of
/// solving them again. The least fixpoint does not depend on the order in which
/// it is solved, so a body sees exactly the summaries a solve of its own would
/// produce.
#[derive(Default)]
pub(super) struct SummaryMemo<'tcx> {
    exact: HashMap<Instance<'tcx>, CalleeSummary>,
    /// The analyzable (`CalleeKind::Body`) callees of a body, deduplicated, in
    /// first-call order.
    callees: HashMap<Instance<'tcx>, Vec<Instance<'tcx>>>,
}

/// The summary solver of one lowered body over a crate's [`SummaryMemo`].
struct Summaries<'m, 'tcx> {
    tcx: TyCtxt<'tcx>,
    memo: &'m mut SummaryMemo<'tcx>,
    /// The summaries this body has requested and their callees, each with
    /// whether it is exact (see [`SummaryMemo`]).
    done: HashMap<Instance<'tcx>, (CalleeSummary, bool)>,
}

/// How a callee is summarized.
enum CalleeKind<'tcx> {
    Fixed(CalleeSummary),
    Body(&'tcx Body<'tcx>),
}

fn callee_kind<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>) -> CalleeKind<'tcx> {
    match instance.def {
        ty::InstanceKind::Intrinsic(_) => CalleeKind::Fixed(intrinsic_summary(tcx, instance)),
        ty::InstanceKind::Item(def_id) if tcx.is_mir_available(def_id) => {
            CalleeKind::Body(tcx.instance_mir(instance.def))
        }
        ty::InstanceKind::Shim(
            ty::ShimKind::DropGlue(..)
            | ty::ShimKind::ClosureOnce { .. }
            | ty::ShimKind::FnPtr(..)
            | ty::ShimKind::VTable(..),
        ) => CalleeKind::Body(tcx.instance_mir(instance.def)),
        _ => CalleeKind::Fixed(CalleeSummary::All),
    }
}

/// The strongly connected components of the graph whose node `n` has the
/// edges `edges[n]`, callees before callers: Tarjan's algorithm emits a
/// component only after every component it reaches. Iterative, so a deep call
/// chain cannot exhaust the stack.
fn components_callees_first(edges: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let n = edges.len();
    let mut index: Vec<Option<usize>> = vec![None; n];
    let mut low = vec![0usize; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut next_index = 0usize;
    let mut out = Vec::new();
    for root in 0..n {
        if index[root].is_some() {
            continue;
        }
        // An explicit DFS stack of (node, next edge to visit).
        let mut dfs: Vec<(usize, usize)> = vec![(root, 0)];
        index[root] = Some(next_index);
        low[root] = next_index;
        next_index += 1;
        stack.push(root);
        on_stack[root] = true;
        while let Some(&mut (node, ref mut edge)) = dfs.last_mut() {
            if let Some(&callee) = edges[node].get(*edge) {
                *edge += 1;
                match index[callee] {
                    None => {
                        index[callee] = Some(next_index);
                        low[callee] = next_index;
                        next_index += 1;
                        stack.push(callee);
                        on_stack[callee] = true;
                        dfs.push((callee, 0));
                    }
                    Some(callee_index) if on_stack[callee] => {
                        low[node] = low[node].min(callee_index);
                    }
                    Some(_) => {}
                }
                continue;
            }
            dfs.pop();
            if let Some(&(parent, _)) = dfs.last() {
                low[parent] = low[parent].min(low[node]);
            }
            if Some(low[node]) == index[node] {
                let mut component = Vec::new();
                loop {
                    let member = stack.pop().expect("Tarjan stack holds the component");
                    on_stack[member] = false;
                    component.push(member);
                    if member == node {
                        break;
                    }
                }
                out.push(component);
            }
        }
    }
    out
}

impl<'m, 'tcx> Summaries<'m, 'tcx> {
    fn kind(&self, instance: Instance<'tcx>) -> CalleeKind<'tcx> {
        callee_kind(self.tcx, instance)
    }

    /// Resolve a call's callee from its `func` operand in `flow`'s body.
    fn resolve(flow: &Flow<'_, 'tcx>, func: &Operand<'tcx>) -> Option<Instance<'tcx>> {
        let fn_ty = flow.operand_ty(func);
        let item = crate::fn_items::view(fn_ty.kind())?;
        let def_id = item.def_id();
        let args = item.unbound_args()?;
        Instance::try_resolve(flow.tcx, ty::TypingEnv::fully_monomorphized(), def_id, args)
            .ok()
            .flatten()
    }

    fn shape(&self, instance: Option<Instance<'tcx>>, arg_len: usize) -> CallShape {
        let Some(instance) = instance else {
            return CallShape {
                callee: None,
                untupled: false,
            };
        };
        let untupled = match self.kind(instance) {
            CalleeKind::Body(body) => {
                arg_len == 2
                    && body.arg_count != 2
                    && body.spread_arg.is_none()
                    && self.tcx.is_closure_like(instance.def_id())
            }
            CalleeKind::Fixed(_) => false,
        };
        CallShape {
            callee: Some(instance.def_id()),
            untupled,
        }
    }

    /// The summary of `instance` given already-final and in-progress summaries.
    fn lookup(
        &self,
        tmp: &HashMap<Instance<'tcx>, CalleeSummary>,
        instance: Option<Instance<'tcx>>,
        arg_len: usize,
    ) -> CalleeSummary {
        let Some(instance) = instance else {
            return CalleeSummary::All;
        };
        let kind = self.kind(instance);
        let summary = if let Some((done, _)) = self.done.get(&instance) {
            done.clone()
        } else if let Some(pending) = tmp.get(&instance) {
            pending.clone()
        } else {
            match &kind {
                CalleeKind::Fixed(summary) => summary.clone(),
                CalleeKind::Body(_) => CalleeSummary::All,
            }
        };
        // A body taking a different number of arguments than the call passes
        // (outside the closure-tuple shape) is not mapped argument by argument.
        if let (CalleeKind::Body(body), CalleeSummary::Args(_)) = (kind, &summary) {
            let untupled = self.shape(Some(instance), arg_len).untupled;
            if !untupled && body.arg_count != arg_len {
                return CalleeSummary::All;
            }
        }
        summary
    }

    /// The analyzable callees of a body (deduplicated, in first-call order),
    /// computed once per crate.
    fn callees(&mut self, instance: Instance<'tcx>, body: &'tcx Body<'tcx>) -> &[Instance<'tcx>] {
        let tcx = self.tcx;
        self.memo.callees.entry(instance).or_insert_with(|| {
            let flow = Flow {
                tcx,
                instance,
                body,
                pts: Vec::new(),
            };
            let mut seen = HashSet::new();
            let mut out = Vec::new();
            for data in body.basic_blocks.iter() {
                if let TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } =
                    &data.terminator().kind
                {
                    if let Some(callee) = Self::resolve(&flow, func) {
                        if matches!(callee_kind(tcx, callee), CalleeKind::Body(_))
                            && seen.insert(callee)
                        {
                            out.push(callee);
                        }
                    }
                }
            }
            out
        })
    }

    /// One body's argument summary, given the current summaries of its callees.
    /// `flow` is the body's points-to state, which no callee summary affects.
    fn analyze(
        &self,
        tmp: &HashMap<Instance<'tcx>, CalleeSummary>,
        flow: &Flow<'tcx, 'tcx>,
    ) -> CalleeSummary {
        let seeds = flow.escapes(
            &mut |flow, func, values| {
                let callee = Self::resolve(flow, func);
                Some((
                    self.lookup(tmp, callee, values.len()),
                    self.shape(callee, values.len()),
                ))
            },
            true,
        );
        let escaped = flow.close(seeds);
        let args = (0..flow.body.arg_count)
            .map(|index| {
                if escaped.contains_key(&Obj::Arg(index)) {
                    ArgCapture::Address
                } else if escaped.contains_key(&Obj::ArgDeep(index)) {
                    ArgCapture::Contents
                } else {
                    ArgCapture::None
                }
            })
            .collect();
        CalleeSummary::Args(args)
    }

    /// The summary of `instance` for this body (see [`SummaryMemo`]), solving
    /// and recording every summary its reach adds to the body's.
    fn summary(&mut self, instance: Instance<'tcx>) -> CalleeSummary {
        if let Some((done, _)) = self.done.get(&instance) {
            return done.clone();
        }
        let root_body = match self.kind(instance) {
            CalleeKind::Body(body) => body,
            CalleeKind::Fixed(summary) => return summary,
        };
        let mut reach: Vec<(Instance<'tcx>, &'tcx Body<'tcx>)> = vec![(instance, root_body)];
        let mut seen: HashSet<Instance<'tcx>> = HashSet::from([instance]);
        let mut next = 0;
        while next < reach.len() {
            let (current, body) = reach[next];
            next += 1;
            let callees = self.callees(current, body).to_vec();
            for callee in callees {
                if self.done.contains_key(&callee) || !seen.insert(callee) {
                    continue;
                }
                let CalleeKind::Body(callee_body) = self.kind(callee) else {
                    continue;
                };
                reach.push((callee, callee_body));
                if reach.len() > MAX_SUMMARY_REACH {
                    self.done.insert(instance, (CalleeSummary::All, false));
                    return CalleeSummary::All;
                }
            }
        }
        for component in self.components(&reach) {
            self.solve_component(&component);
        }
        self.done[&instance].0.clone()
    }

    /// The strongly connected components of the call graph among `members`,
    /// callees before callers (Tarjan's order), so each component is solved
    /// against final summaries of everything it calls outside itself.
    fn components(
        &mut self,
        members: &[(Instance<'tcx>, &'tcx Body<'tcx>)],
    ) -> Vec<Vec<(Instance<'tcx>, &'tcx Body<'tcx>, bool)>> {
        let position: HashMap<Instance<'tcx>, usize> = members
            .iter()
            .enumerate()
            .map(|(position, (member, _))| (*member, position))
            .collect();
        let edges: Vec<Vec<usize>> = members
            .iter()
            .map(|(member, body)| {
                self.callees(*member, body)
                    .iter()
                    .filter_map(|callee| position.get(callee).copied())
                    .collect()
            })
            .collect();
        components_callees_first(&edges)
            .into_iter()
            .map(|component| {
                let recursive = component.len() > 1
                    || component
                        .iter()
                        .any(|&member| edges[member].contains(&member));
                component
                    .into_iter()
                    .map(|member| (members[member].0, members[member].1, recursive))
                    .collect()
            })
            .collect()
    }

    /// Solve one strongly connected component as the least fixpoint of its
    /// members' monotone system, from [`ArgCapture::None`], against the body's
    /// summaries of everything it calls outside itself, and record it. An
    /// exact component already solved for the crate is taken from the memo.
    fn solve_component(&mut self, component: &[(Instance<'tcx>, &'tcx Body<'tcx>, bool)]) {
        let members: HashSet<Instance<'tcx>> =
            component.iter().map(|(member, _, _)| *member).collect();
        let mut exact = true;
        for (member, body, _) in component {
            for callee in self.callees(*member, body).to_vec() {
                if !members.contains(&callee) {
                    // A callee outside the component was summarized for this
                    // body before the request or in an earlier component of it.
                    exact &= self.done.get(&callee).is_some_and(|(_, exact)| *exact);
                }
            }
        }
        if exact {
            let memoized: Option<Vec<CalleeSummary>> = component
                .iter()
                .map(|(member, _, _)| self.memo.exact.get(member).cloned())
                .collect();
            if let Some(memoized) = memoized {
                for ((member, _, _), summary) in component.iter().zip(memoized) {
                    self.done.insert(*member, (summary, true));
                }
                return;
            }
        }
        let flows: Vec<(Instance<'tcx>, Flow<'tcx, 'tcx>)> = component
            .iter()
            .map(|(member, body, _)| (*member, Flow::new(self.tcx, *member, body, true)))
            .collect();
        let mut tmp: HashMap<Instance<'tcx>, CalleeSummary> = component
            .iter()
            .map(|(member, body, _)| {
                (
                    *member,
                    CalleeSummary::Args(vec![ArgCapture::None; body.arg_count]),
                )
            })
            .collect();
        // A member that calls nothing in its own component reads only final
        // summaries, so one analysis is its fixpoint.
        let recursive = component.iter().any(|(_, _, recursive)| *recursive);
        loop {
            let mut changed = false;
            for (member, flow) in &flows {
                let new = self.analyze(&tmp, flow);
                if tmp.get(member) != Some(&new) {
                    tmp.insert(*member, new);
                    changed = true;
                }
            }
            if !changed || !recursive {
                break;
            }
        }
        for (member, summary) in tmp {
            if exact {
                self.memo.exact.insert(member, summary.clone());
            }
            self.done.insert(member, (summary, exact));
        }
    }
}

/// Every local of `body` (the body being lowered for `instance`) whose address
/// may be kept beyond this body's view in a pointer that may be written
/// through, with the first reason found for it.
///
/// A local whose address escapes only through SHARED borrows is left out when
/// its type is `Freeze`: nothing may write through such a pointer, and a read
/// through it is defined only while the local keeps the value it had when
/// borrowed, which is the value the borrow's materialized home holds (it is
/// stored again only by a later borrow of the same local). An interior-mutable
/// (`!Freeze`) local is kept, as a shared pointer to it may write.
///
/// `memo` holds the crate's exact callee summaries (see [`SummaryMemo`]); this
/// body's own escapes are not memoized, since the lowering may rewrite its MIR.
pub(super) fn retained_address_locals<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    body: &Body<'tcx>,
    memo: &mut SummaryMemo<'tcx>,
) -> BTreeMap<Local, String> {
    // Only a body that takes an address can have a local whose address escapes.
    let takes_address = body.basic_blocks.iter().any(|data| {
        data.statements.iter().any(|statement| {
            matches!(
                &statement.kind,
                StatementKind::Assign(boxed)
                    if matches!(boxed.1, Rvalue::Ref(..) | Rvalue::RawPtr(..) | Rvalue::Reborrow(..))
            )
        })
    });
    if !takes_address {
        return BTreeMap::new();
    }
    let flow = Flow::new(tcx, instance, body, false);
    let mut summaries = Summaries {
        tcx,
        memo,
        done: HashMap::new(),
    };
    let typing_env = ty::TypingEnv::fully_monomorphized();
    // Whether an escaped object can be reported below.
    let reportable = |obj: Obj| match obj {
        Obj::Local(local, writable) => {
            writable
                || !flow
                    .mono(body.local_decls[local].ty)
                    .is_freeze(tcx, typing_env)
        }
        // Not produced by a body analyzed without argument objects; counted
        // as reportable so it never lets a call be skipped.
        Obj::Arg(_) | Obj::ArgDeep(_) => true,
    };
    // A call whose arguments can reach no reportable object is not
    // summarized: whatever its callee keeps, everything that escapes through
    // it is in the closure of its argument values under `Flow::contents`, so
    // it adds no reported local, and no reported local's first reason is set
    // through it (an object reached from it is in that closure too). Its
    // callee's summary request is DEFERRED, not dropped: `Summaries::summary`
    // counts a request's reach net of the summaries this body already holds,
    // so the reach cap of a later request depends on the earlier ones. Every
    // deferred request is therefore replayed, in call order, before the next
    // request that is answered, so every answered request sees the summaries
    // it saw when all requests were made. On `std::rt::lang_start`, whose only
    // address-carrying call passes a shared borrow of a `Freeze` closure to
    // `lang_start_internal`, this skips summarizing that function's whole
    // callee reach in every program.
    let mut deferred: Vec<Instance<'tcx>> = Vec::new();
    let seeds = flow.escapes(
        &mut |flow, func, values| {
            let callee = Summaries::resolve(flow, func);
            if !reaches_reportable(values, |obj| flow.contents(obj), &reportable) {
                deferred.extend(callee);
                return None;
            }
            for earlier in deferred.drain(..) {
                summaries.summary(earlier);
            }
            let summary = match callee {
                Some(callee) => {
                    summaries.summary(callee);
                    summaries.lookup(&HashMap::new(), Some(callee), values.len())
                }
                None => CalleeSummary::All,
            };
            Some((summary, summaries.shape(callee, values.len())))
        },
        false,
    );
    let mut out: BTreeMap<Local, String> = BTreeMap::new();
    for (obj, reason) in flow.close(seeds) {
        if !reportable(obj) {
            continue;
        }
        let Obj::Local(local, _) = obj else {
            continue;
        };
        out.entry(local).or_insert_with(|| reason.describe(tcx));
    }
    out
}

/// Whether the closure of `values` under `contents` holds an object for which
/// `reportable` is true.
fn reaches_reportable(
    values: &[BTreeSet<Obj>],
    contents: impl Fn(Obj) -> BTreeSet<Obj>,
    reportable: impl Fn(Obj) -> bool,
) -> bool {
    let mut seen: BTreeSet<Obj> = BTreeSet::new();
    let mut work: Vec<Obj> = values.iter().flatten().copied().collect();
    while let Some(obj) = work.pop() {
        if !seen.insert(obj) {
            continue;
        }
        if reportable(obj) {
            return true;
        }
        work.extend(contents(obj));
    }
    false
}

#[cfg(test)]
mod tests {
    use super::{
        ArgCapture, CallShape, CalleeSummary, Obj, components_callees_first, reaches_reportable,
    };
    use std::collections::{BTreeMap, BTreeSet};

    /// A call is skipped only when NO object in the closure of its argument
    /// values is reportable: a reportable object reached only through memory
    /// (two `contents` steps, across a cycle) still counts, and the walk ends
    /// on a cycle that reaches none. Fails if the walk stops at the argument
    /// values themselves or does not follow `contents`.
    #[test]
    fn reaches_reportable_follows_the_whole_contents_closure() {
        let local =
            |i: u32, writable: bool| Obj::Local(rustc_middle::mir::Local::from_u32(i), writable);
        // 0 -> 1 -> {0, 2}; 2 -> 3 (writable). 4 <-> 5, neither writable.
        let edges: BTreeMap<Obj, BTreeSet<Obj>> = [
            (local(0, false), BTreeSet::from([local(1, false)])),
            (
                local(1, false),
                BTreeSet::from([local(0, false), local(2, false)]),
            ),
            (local(2, false), BTreeSet::from([local(3, true)])),
            (local(4, false), BTreeSet::from([local(5, false)])),
            (local(5, false), BTreeSet::from([local(4, false)])),
        ]
        .into_iter()
        .collect();
        let contents = |obj: Obj| edges.get(&obj).cloned().unwrap_or_default();
        let writable = |obj: Obj| matches!(obj, Obj::Local(_, true));
        assert!(reaches_reportable(
            &[BTreeSet::new(), BTreeSet::from([local(0, false)])],
            contents,
            writable
        ));
        assert!(!reaches_reportable(
            &[BTreeSet::from([local(4, false)])],
            contents,
            writable
        ));
        assert!(!reaches_reportable(&[BTreeSet::new()], contents, writable));
        assert!(reaches_reportable(
            &[BTreeSet::from([local(4, false)])],
            contents,
            |obj| obj == local(5, false)
        ));
    }

    /// Components come callees first, a cycle is one component, and a chain
    /// deeper than any thread stack is walked without recursion.
    #[test]
    fn components_are_emitted_callees_first() {
        // 0 -> 1 -> {2 <-> 3} -> 4, and 0 -> 4.
        let edges = vec![vec![1, 4], vec![2], vec![3], vec![2, 4], vec![]];
        let mut components = components_callees_first(&edges);
        for component in &mut components {
            component.sort_unstable();
        }
        assert_eq!(components, vec![vec![4], vec![2, 3], vec![1], vec![0]]);
        let depth = 200_000;
        let chain: Vec<Vec<usize>> = (0..depth)
            .map(|node| {
                if node + 1 < depth {
                    vec![node + 1]
                } else {
                    vec![]
                }
            })
            .collect();
        let components = components_callees_first(&chain);
        assert_eq!(components.len(), depth);
        assert!(components.iter().rev().map(|c| c[0]).eq(0..depth));
    }

    /// An argument past a summary's end is kept whole, and `All` keeps every
    /// argument.
    #[test]
    fn summary_defaults_are_conservative() {
        let s = CalleeSummary::Args(vec![ArgCapture::None, ArgCapture::Contents]);
        assert_eq!(s.arg(0), ArgCapture::None);
        assert_eq!(s.arg(1), ArgCapture::Contents);
        assert_eq!(s.arg(2), ArgCapture::Address);
        assert_eq!(CalleeSummary::All.arg(0), ArgCapture::Address);
    }

    /// A closure-call tuple operand is kept as strongly as the strongest
    /// untupled argument it feeds; an operand past the tuple is kept whole.
    #[test]
    fn untupled_closure_call_takes_the_strongest_tuple_field() {
        let shape = CallShape {
            callee: None,
            untupled: true,
        };
        let s = CalleeSummary::Args(vec![
            ArgCapture::None,
            ArgCapture::None,
            ArgCapture::Contents,
            ArgCapture::None,
        ]);
        assert_eq!(shape.capture(&s, 0), ArgCapture::None);
        assert_eq!(shape.capture(&s, 1), ArgCapture::Contents);
        assert_eq!(shape.capture(&s, 2), ArgCapture::Address);
        let unit = CalleeSummary::Args(vec![ArgCapture::Address]);
        assert_eq!(shape.capture(&unit, 1), ArgCapture::None);
    }
}
