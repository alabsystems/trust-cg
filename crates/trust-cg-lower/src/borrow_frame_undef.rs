// trust-cg-lower/borrow_frame_undef.rs - Borrow, binding-frame and Undef legalization
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The named legalization stage for trust-ir borrows, binding frames and
//! `Undef` (ledger L05-P9): [`STAGE`].
//!
//! The stage runs inside the adapter, once per function, BEFORE any of that
//! function's instructions are lowered, and on every entry (compatibility,
//! prepared and strict). It never clones or rewrites the caller's module, so
//! it is not a [`crate::PreLirTransform`] and the strict entry's identity
//! contract is untouched. It decides, for the whole function, whether every
//! borrow, binding-frame and `Undef` instruction is in the shape its lowering
//! honours, and refuses the function by name
//! ([`AdapterError::LegalizationRefused`]) otherwise. The per-instruction
//! lowering then consumes only the plan this stage produced, and records what
//! it emitted in the function's [`BorrowFrameUndefReceipt`]
//! (`ProofContext::borrow_frame_undef`), which the retained strict-LIR identity
//! hashes. The receipt is a record, not authority: no optimization reads it.
//!
//! # Semantics consumed (pinned trust-ir `dcc5b9a3`)
//!
//! * `Borrow` / `BorrowMut` (`interpret.rs`): the result is the operand
//!   pointer VERBATIM (a thin operand is re-typed `Ptr`, a fat one keeps its
//!   type, `bridge::borrow_result_ty`). `EndBorrow` has no runtime effect.
//!   The validator decides borrow STRUCTURE (no `BorrowMut` through a shared
//!   reference, `EndBorrow` only of a borrow); borrow LIVENESS is a producer
//!   obligation the interpreter does not check either. Lowering: a LIR `Copy`
//!   of the operand, with the borrowed root and the borrow kind recorded.
//! * Binding frames (`inst.rs`, `interpret.rs`): `OpenFrame` mints a frame
//!   whose slots are all unbound; `BindSlot` is FUNCTIONAL — it yields a new
//!   handle and every older handle keeps its prior contents; `LoadSlot` reads
//!   the handle's own snapshot (an unbound slot reads as poison);
//!   `CloseFrame` has no runtime effect. The representation is
//!   backend-chosen. Lowering: one zero-filled stack slot per `OpenFrame`,
//!   laid out from the slots' LIR carriers; `BindSlot` stores in place and
//!   returns the same address; `LoadSlot` loads; `CloseFrame` emits nothing.
//!   In-place storage honours the functional semantics only while no
//!   superseded handle is still live, so the stage checks that by SSA
//!   liveness (within each block and across every block edge) and refuses
//!   every function where the check does not pass. The check is a static
//!   analysis exercised by tests, not a proof.
//! * `Undef` (`inst.rs`, ub-numerics-policy §4): a POISON value. Executing it
//!   is defined; INSPECTING it (arithmetic, comparison, cast, a
//!   branch/switch/select condition, projection, call argument or return, a
//!   strict store, a dereference) is undefined behaviour. It may only be
//!   transported: `Copy`, a `Select` arm, a plain `Store`, a block argument
//!   (and, here, a `BindSlot` value). Lowering, the NoUndef model
//!   ([`NO_UNDEF_MODEL`]): a scalar `Undef` materializes as the all-zero bit
//!   pattern of its LIR carrier. The stage traces every poison value (each
//!   `Undef`, and each `LoadSlot` of a slot that may be unbound or bound to
//!   poison) through the transports above and refuses the function if one
//!   reaches any other use, so a zero is never presented where trust-ir
//!   answers undefined behaviour on the SSA path.
//!
//! # What stays refused (each by name)
//!
//! A `BorrowMut` whose operand is typed `Ref`/`PtrConst` or may root at a
//! shared `Borrow`; a borrow of a value that is not a pointer, or of the
//! statically null pointer (undefined behaviour in trust-ir); an `EndBorrow`
//! of a non-borrow; a frame handle used by anything other than
//! `BindSlot`/`LoadSlot`/`CloseFrame`/a `Br`/`CondBr`/`Switch` argument; a
//! block parameter mixing frame and non-frame values or handles of two
//! `OpenFrame`s; a frame handle reaching an entry-block parameter (which
//! also receives the caller's argument); a slot type outside the scalar carrier set; a slot index or
//! type that disagrees with the frame definition; a frame no `CloseFrame`
//! ends; a superseded handle live across a rebind; an `Undef` of an aggregate,
//! vector, `Char`, `F16`, refined, handle or other non-scalar type; an
//! `Undef` carrying any proof annotation (a `FreshSymbolicHavoc` marker is a
//! nondeterministic choice, not poison, and stays outside the lowering-target
//! subset: must-refuse row `refuse/undef_fresh_havoc_feeds_assume`); and any
//! poison value reaching an inspecting use.
//!
//! # Residual, stated
//!
//! Poison written to memory by a plain `Store` is not traced through the
//! later `Load`: a program that stores an `Undef` and inspects the reloaded
//! value has undefined behaviour in trust-ir, and the zero this backend
//! stored is what it reads. That is a refinement of undefined behaviour, not
//! a claim of agreement. Evidence for the whole stage is test-strength: the
//! Darwin AArch64 native differential against the trust-ir reference
//! interpreter (`e2e_aarch64_borrows_frames`) and the adapter-level
//! conformance rows. Nothing here is a proof.

use std::collections::{BTreeSet, HashMap, HashSet};

use trust_ir::inst::BindingFrameDef;
use trust_ir::{
    Block as TrustIrBlock, BlockId, CastOp, Function as TrustIrFunction, Inst, InstrNode,
    ProofAnnotation, Ty, ValueId,
};

use crate::adapter::AdapterError;
use crate::handle_transport::inst_name;
use crate::instructions::Value;
use crate::types::Type;

/// Stable identity of this legalization stage (diagnostics and receipts).
pub const STAGE: &str = "borrow-frame-undef-legalization";

/// The NoUndef model an admitted `Undef` is materialized under: the all-zero
/// bit pattern of its LIR carrier (`0`, `false`, a null pointer, `+0.0`).
/// Frame storage is zero-filled at `OpenFrame` under the same model.
pub const NO_UNDEF_MODEL: &str = "zero-bits";

/// Which borrow instruction produced a [`BorrowRecord`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BorrowKind {
    /// `Inst::Borrow` (`&*p`).
    Shared,
    /// `Inst::BorrowMut` (`&mut *p`).
    Unique,
}

/// A lowered borrow: the result is a value-preserving copy of `operand`.
/// `root` is the trust-ir address the borrow chain starts from (the first
/// value in the chain no borrow defines). A provenance RECORD only; it
/// authorizes no aliasing or validity assumption.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BorrowRecord {
    /// The trust-ir borrow result.
    pub source: ValueId,
    /// The trust-ir root the borrow chain starts from.
    pub root: ValueId,
    /// `Borrow` or `BorrowMut`.
    pub kind: BorrowKind,
    /// The LIR value the borrow result is carried in.
    pub result: Value,
    /// The LIR value it copies.
    pub operand: Value,
}

/// A retired borrow: an `EndBorrow`, which emits nothing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RetiredBorrowRecord {
    /// The trust-ir borrow the `EndBorrow` names.
    pub source: ValueId,
    /// Its LIR carrier.
    pub borrow: Value,
}

/// One slot of a lowered binding frame.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FrameSlotRecord {
    /// Byte offset inside the frame's stack slot.
    pub offset: u32,
    /// The slot's LIR carrier.
    pub carrier: Type,
}

/// A lowered binding frame: one `OpenFrame` and the stack storage every
/// handle descending from it shares.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FrameRecord {
    /// The trust-ir `OpenFrame` result.
    pub source: ValueId,
    /// The frame's `BindingFrameId`.
    pub frame_id: u32,
    /// The LIR value holding the frame address.
    pub handle: Value,
    /// The function stack slot backing the frame.
    pub stack_slot: u32,
    /// Stack slot size (a multiple of 8, zero-filled at `OpenFrame`).
    pub bytes: u32,
    /// Stack slot alignment.
    pub align: u32,
    /// Slot layout, in declaration order.
    pub slots: Vec<FrameSlotRecord>,
}

/// An `Undef` materialized under [`NO_UNDEF_MODEL`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UndefRecord {
    /// The trust-ir `Undef` result.
    pub source: ValueId,
    /// The LIR value holding the zero pattern.
    pub result: Value,
    /// Its LIR carrier.
    pub carrier: Type,
}

/// What [`STAGE`] lowered in one function, in lowering order. Empty for every
/// function without these constructs. Hashed into the retained strict-LIR
/// identity; consumed by no optimization.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct BorrowFrameUndefReceipt {
    /// Every lowered `Borrow` / `BorrowMut`.
    pub borrows: Vec<BorrowRecord>,
    /// Every `EndBorrow`.
    pub retired_borrows: Vec<RetiredBorrowRecord>,
    /// Every lowered `OpenFrame`.
    pub frames: Vec<FrameRecord>,
    /// Every materialized `Undef`.
    pub undefs: Vec<UndefRecord>,
}

impl BorrowFrameUndefReceipt {
    /// Whether the stage lowered nothing in this function.
    pub fn is_empty(&self) -> bool {
        self.borrows.is_empty()
            && self.retired_borrows.is_empty()
            && self.frames.is_empty()
            && self.undefs.is_empty()
    }
}

/// One slot of a planned frame.
#[derive(Debug, Clone)]
pub(crate) struct PlannedSlot {
    pub(crate) ty: Ty,
    pub(crate) carrier: Type,
    pub(crate) offset: u32,
}

/// A planned frame: every handle of one `OpenFrame` lineage shares it.
#[derive(Debug, Clone)]
pub(crate) struct FramePlan {
    pub(crate) frame_id: u32,
    pub(crate) slots: Vec<PlannedSlot>,
    pub(crate) bytes: u32,
    pub(crate) align: u32,
}

/// A planned borrow.
#[derive(Debug, Clone, Copy)]
pub(crate) struct BorrowPlan {
    pub(crate) root: ValueId,
    pub(crate) kind: BorrowKind,
}

/// The stage's decision for one function. Lowering consumes only this.
#[derive(Debug, Clone, Default)]
pub(crate) struct LegalizationPlan {
    frame_of: HashMap<ValueId, usize>,
    frames: Vec<FramePlan>,
    borrows: HashMap<ValueId, BorrowPlan>,
    undefs: HashSet<ValueId>,
}

impl LegalizationPlan {
    /// The frame a handle belongs to.
    pub(crate) fn frame(&self, handle: ValueId) -> Option<&FramePlan> {
        self.frame_of
            .get(&handle)
            .and_then(|index| self.frames.get(*index))
    }

    /// The plan for a borrow result.
    pub(crate) fn borrow(&self, result: ValueId) -> Option<BorrowPlan> {
        self.borrows.get(&result).copied()
    }

    /// Whether the `Undef` defining `result` was admitted.
    pub(crate) fn undef_admitted(&self, result: ValueId) -> bool {
        self.undefs.contains(&result)
    }
}

/// Whether `ty` is in the scalar carrier set this stage materializes (an
/// `Undef` type or a frame slot type): integers, pointer-width integers,
/// `Bool`, `F32`/`F64` and thin pointers. `Char` and `F16` are outside the
/// lowering-target subset at these positions; `Rc`, fat pointers, vectors,
/// aggregates, handles and refinements are not scalar carriers here.
///
/// Public so a non-native lane admits `Undef` at exactly this set (the wasm32
/// lane's body-construct floor applies it with this stage's reason).
pub fn scalar_carrier_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Bool
            | Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::F32
            | Ty::F64
            | Ty::Ptr
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
    )
}

/// Whether `ty` is an address a borrow may take (a thin or fat pointer).
fn borrowable_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr | Ty::Ref(_) | Ty::RefMut(_) | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::FatPtr(_)
    )
}

fn involves_this_stage(inst: &Inst) -> bool {
    match inst {
        Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::EndBorrow { .. }
        | Inst::OpenFrame { .. }
        | Inst::BindSlot { .. }
        | Inst::LoadSlot { .. }
        | Inst::CloseFrame { .. } => true,
        Inst::Undef { ty } => !matches!(ty, Ty::Unit | Ty::Never),
        _ => false,
    }
}

/// Every control edge an instruction leaves along, with the block arguments
/// it passes (an `Invoke` unwind edge passes none).
fn edges(inst: &Inst) -> Vec<(BlockId, &[ValueId])> {
    match inst {
        Inst::Br { target, args } => vec![(*target, args.as_slice())],
        Inst::CondBr {
            then_target,
            then_args,
            else_target,
            else_args,
            ..
        } => vec![
            (*then_target, then_args.as_slice()),
            (*else_target, else_args.as_slice()),
        ],
        Inst::Switch {
            default,
            default_args,
            cases,
            ..
        } => {
            let mut out = vec![(*default, default_args.as_slice())];
            out.extend(cases.iter().map(|case| (case.target, case.args.as_slice())));
            out
        }
        Inst::Invoke {
            normal_dest,
            normal_args,
            unwind_dest,
            ..
        } => vec![
            (*normal_dest, normal_args.as_slice()),
            (*unwind_dest, &[][..]),
        ],
        _ => Vec::new(),
    }
}

fn operands(inst: &Inst) -> Vec<ValueId> {
    let mut out = Vec::new();
    inst.visit_value_operands(|operand| out.push(operand));
    out
}

/// The operands an instruction only TRANSPORTS (trust-ir's poison transport
/// set, plus a `BindSlot` value, which a frame carries verbatim), with
/// multiplicity. Every other operand position inspects its value.
fn transported_operands(inst: &Inst) -> Vec<ValueId> {
    match inst {
        Inst::Copy { operand, .. } => vec![*operand],
        Inst::Select {
            then_val, else_val, ..
        } => vec![*then_val, *else_val],
        Inst::Store {
            value,
            volatile: false,
            ..
        } => vec![*value],
        Inst::BindSlot { value, .. } => vec![*value],
        Inst::Br { .. } | Inst::CondBr { .. } | Inst::Switch { .. } | Inst::Invoke { .. } => {
            edges(inst)
                .into_iter()
                .flat_map(|(_, args)| args.iter().copied())
                .collect()
        }
        _ => Vec::new(),
    }
}

/// The operands an instruction inspects: every operand minus one occurrence
/// of each transported one.
fn inspected_operands(inst: &Inst) -> Vec<ValueId> {
    let mut all = operands(inst);
    for transported in transported_operands(inst) {
        if let Some(position) = all.iter().position(|value| *value == transported) {
            all.swap_remove(position);
        }
    }
    all
}

fn align_up(offset: u32, align: u32) -> Option<u32> {
    if align <= 1 {
        return Some(offset);
    }
    let rem = offset % align;
    if rem == 0 {
        Some(offset)
    } else {
        offset.checked_add(align - rem)
    }
}

/// Union-find over frame handle values.
#[derive(Default)]
struct Classes {
    parent: HashMap<ValueId, ValueId>,
}

impl Classes {
    fn find(&mut self, value: ValueId) -> ValueId {
        let mut root = value;
        while let Some(&parent) = self.parent.get(&root) {
            if parent == root {
                break;
            }
            root = parent;
        }
        // Path compression keeps repeated queries linear.
        let mut cursor = value;
        while let Some(&parent) = self.parent.get(&cursor) {
            if parent == root {
                break;
            }
            self.parent.insert(cursor, root);
            cursor = parent;
        }
        root
    }

    fn union(&mut self, a: ValueId, b: ValueId) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra != rb {
            self.parent.insert(ra, rb);
        }
    }
}

struct Context<'f> {
    function: &'f TrustIrFunction,
    blocks: HashMap<BlockId, &'f TrustIrBlock>,
    /// Defining node of each instruction result.
    defs: HashMap<ValueId, &'f InstrNode>,
    /// `(block, param index)` of each block parameter.
    params: HashMap<ValueId, (BlockId, usize)>,
    /// Incoming arguments of each block parameter.
    incoming: HashMap<ValueId, Vec<ValueId>>,
}

impl<'f> Context<'f> {
    fn new(function: &'f TrustIrFunction) -> Self {
        let blocks: HashMap<BlockId, &TrustIrBlock> = function
            .blocks
            .iter()
            .map(|block| (block.id, block))
            .collect();
        let mut defs = HashMap::new();
        let mut params = HashMap::new();
        let mut incoming: HashMap<ValueId, Vec<ValueId>> = HashMap::new();
        for block in &function.blocks {
            for (index, (param, _)) in block.params.iter().enumerate() {
                params.insert(*param, (block.id, index));
            }
            for node in &block.body {
                for result in &node.results {
                    defs.entry(*result).or_insert(node);
                }
                for (target, args) in edges(&node.inst) {
                    if let Some(target) = blocks.get(&target) {
                        for ((param, _), arg) in target.params.iter().zip(args) {
                            incoming.entry(*param).or_default().push(*arg);
                        }
                    }
                }
            }
        }
        Self {
            function,
            blocks,
            defs,
            params,
            incoming,
        }
    }

    fn refuse(&self, construct: &'static str, reason: impl Into<String>) -> AdapterError {
        AdapterError::LegalizationRefused {
            stage: STAGE,
            construct,
            function: self.function.name.clone(),
            reason: reason.into(),
        }
    }

    fn successors(&self, block: &TrustIrBlock) -> Vec<BlockId> {
        block
            .body
            .iter()
            .flat_map(|node| edges(&node.inst).into_iter().map(|(target, _)| target))
            .collect()
    }
}

/// Plan the stage for `function`, or `None` when it carries none of the
/// constructs (the common path pays one scan). `value_ty` is the adapter's
/// trust-ir type map for the function (borrow results already resolved by
/// `trust_ir::bridge::borrow_result_types`); `carrier` is the adapter's own
/// type translation, which fixes every slot's LIR carrier.
pub(crate) fn plan_function<S: std::hash::BuildHasher>(
    function: &TrustIrFunction,
    value_ty: &std::collections::HashMap<ValueId, Ty, S>,
    carrier: &dyn Fn(&Ty) -> Result<Type, AdapterError>,
) -> Result<Option<LegalizationPlan>, AdapterError> {
    let involved = function
        .blocks
        .iter()
        .flat_map(|block| &block.body)
        .any(|node| involves_this_stage(&node.inst));
    if !involved {
        return Ok(None);
    }
    let cx = Context::new(function);
    let mut plan = LegalizationPlan::default();
    let frame_values = plan_frames(&cx, value_ty, carrier, &mut plan)?;
    plan_borrows(&cx, value_ty, &frame_values, &mut plan)?;
    plan_undefs(&cx, &frame_values, &mut plan)?;
    Ok(Some(plan))
}

// ---------------------------------------------------------------------------
// Binding frames
// ---------------------------------------------------------------------------

fn plan_frames<S: std::hash::BuildHasher>(
    cx: &Context<'_>,
    value_ty: &std::collections::HashMap<ValueId, Ty, S>,
    carrier: &dyn Fn(&Ty) -> Result<Type, AdapterError>,
    plan: &mut LegalizationPlan,
) -> Result<HashSet<ValueId>, AdapterError> {
    let function = cx.function;
    let mut frames: HashSet<ValueId> = HashSet::new();
    let mut opens: Vec<(ValueId, &BindingFrameDef)> = Vec::new();
    for node in function.blocks.iter().flat_map(|block| &block.body) {
        match &node.inst {
            Inst::OpenFrame { def } => {
                let [result] = node.results.as_slice() else {
                    return Err(cx.refuse(
                        "Inst::OpenFrame",
                        format!(
                            "declares {} results; a frame handle is one value",
                            node.results.len()
                        ),
                    ));
                };
                frames.insert(*result);
                opens.push((*result, def));
            }
            Inst::BindSlot { .. } | Inst::LoadSlot { .. } if node.results.len() != 1 => {
                return Err(cx.refuse(
                    if matches!(node.inst, Inst::BindSlot { .. }) {
                        "Inst::BindSlot"
                    } else {
                        "Inst::LoadSlot"
                    },
                    format!(
                        "declares {} results; exactly one is defined",
                        node.results.len()
                    ),
                ));
            }
            Inst::CloseFrame { .. } if !node.results.is_empty() => {
                return Err(cx.refuse("Inst::CloseFrame", "declares a result; it produces none"));
            }
            _ => {}
        }
    }

    // Frame-ness propagates from `OpenFrame` through `BindSlot` results and
    // along block arguments to parameters (the validator's own propagation).
    loop {
        let mut changed = false;
        for block in &function.blocks {
            for node in &block.body {
                if let Inst::BindSlot { frame, .. } = &node.inst
                    && frames.contains(frame)
                    && let Some(result) = node.results.first()
                {
                    changed |= frames.insert(*result);
                }
                for (target, args) in edges(&node.inst) {
                    if let Some(target) = cx.blocks.get(&target) {
                        for ((param, _), arg) in target.params.iter().zip(args) {
                            if frames.contains(arg) {
                                changed |= frames.insert(*param);
                            }
                        }
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    // An entry-block parameter also receives the caller's argument on
    // function entry, which is not a handle any `OpenFrame` produced; the
    // incoming-edge merge check below sees only branch arguments, so a back
    // edge that feeds the entry block a handle is refused here.
    if let Some(entry) = cx.blocks.get(&function.entry)
        && let Some((param, _)) = entry
            .params
            .iter()
            .find(|(param, _)| frames.contains(param))
    {
        return Err(cx.refuse(
            "Inst::OpenFrame",
            format!(
                "entry-block parameter {param:?} receives a frame handle along a back edge, but \
                 on function entry it holds the caller's argument, which no OpenFrame produced"
            ),
        ));
    }
    if frames.is_empty() {
        // No `OpenFrame`: any frame operation names a value no frame produced.
        for node in function.blocks.iter().flat_map(|block| &block.body) {
            let construct = match node.inst {
                Inst::BindSlot { .. } => "Inst::BindSlot",
                Inst::LoadSlot { .. } => "Inst::LoadSlot",
                Inst::CloseFrame { .. } => "Inst::CloseFrame",
                _ => continue,
            };
            return Err(cx.refuse(
                construct,
                "its frame operand is not a handle any OpenFrame produced (trust-ir \
                 BindingFrameNotOpen/BindingFrameUnopened)",
            ));
        }
        return Ok(frames);
    }

    // Classes (lineages), and where a handle may be used.
    let mut classes = Classes::default();
    let mut closes: HashMap<ValueId, usize> = HashMap::new();
    for block in &function.blocks {
        for node in &block.body {
            let inst = &node.inst;
            match inst {
                Inst::BindSlot { frame, value, .. } => {
                    if !frames.contains(frame) {
                        return Err(cx.refuse(
                            "Inst::BindSlot",
                            format!(
                                "frame operand {frame:?} is not a handle any OpenFrame produced \
                                 (trust-ir BindingFrameNotOpen)"
                            ),
                        ));
                    }
                    if frames.contains(value) {
                        return Err(cx.refuse(
                            "Inst::BindSlot",
                            format!("binds frame handle {value:?} into a slot: a frame is not a slot value"),
                        ));
                    }
                    if let Some(result) = node.results.first() {
                        classes.union(*result, *frame);
                    }
                }
                Inst::LoadSlot { frame, .. } => {
                    if !frames.contains(frame) {
                        return Err(cx.refuse(
                            "Inst::LoadSlot",
                            format!(
                                "frame operand {frame:?} is not a handle any OpenFrame produced \
                                 (trust-ir BindingFrameNotOpen)"
                            ),
                        ));
                    }
                }
                Inst::CloseFrame { frame } => {
                    if !frames.contains(frame) {
                        return Err(cx.refuse(
                            "Inst::CloseFrame",
                            format!(
                                "frame operand {frame:?} is not a handle any OpenFrame produced \
                                 (trust-ir BindingFrameUnopened)"
                            ),
                        ));
                    }
                    *closes.entry(*frame).or_default() += 1;
                }
                Inst::OpenFrame { .. } => {}
                Inst::Br { .. } | Inst::CondBr { .. } | Inst::Switch { .. } => {
                    let selector = match inst {
                        Inst::CondBr { cond, .. } => Some(*cond),
                        Inst::Switch { value, .. } => Some(*value),
                        _ => None,
                    };
                    if let Some(selector) = selector
                        && frames.contains(&selector)
                    {
                        return Err(cx.refuse(
                            "Inst::OpenFrame",
                            format!(
                                "frame handle {selector:?} is inspected as a {} selector",
                                inst_name(inst)
                            ),
                        ));
                    }
                    for (target, args) in edges(inst) {
                        let Some(target) = cx.blocks.get(&target) else {
                            continue;
                        };
                        for ((param, _), arg) in target.params.iter().zip(args) {
                            match (frames.contains(arg), frames.contains(param)) {
                                (true, true) => classes.union(*param, *arg),
                                (false, false) => {}
                                _ => {
                                    return Err(cx.refuse(
                                        "Inst::OpenFrame",
                                        format!(
                                            "block parameter {param:?} merges a frame handle with \
                                             a value no OpenFrame produced"
                                        ),
                                    ));
                                }
                            }
                        }
                    }
                }
                other => {
                    if let Some(escaped) = operands(other)
                        .into_iter()
                        .find(|operand| frames.contains(operand))
                    {
                        return Err(cx.refuse(
                            "Inst::OpenFrame",
                            format!(
                                "frame handle {escaped:?} escapes into Inst::{}: a binding-frame \
                                 handle is not a pointer, a storable, callable or returnable \
                                 value (only BindSlot/LoadSlot/CloseFrame and branch arguments \
                                 may use it)",
                                inst_name(other)
                            ),
                        ));
                    }
                }
            }
        }
    }

    // One OpenFrame per class, a scalar slot layout, and at least one close.
    let mut class_index: HashMap<ValueId, usize> = HashMap::new();
    let mut class_open: Vec<ValueId> = Vec::new();
    for (open, def) in &opens {
        let root = classes.find(*open);
        if let Some(&existing) = class_index.get(&root) {
            return Err(cx.refuse(
                "Inst::OpenFrame",
                format!(
                    "handles of two OpenFrame instructions ({:?} and {open:?}) merge at a block \
                     parameter; their storage is not one frame",
                    class_open[existing]
                ),
            ));
        }
        let mut slots = Vec::with_capacity(def.slots.len());
        let mut cursor = 0u32;
        let mut align = 8u32;
        for (index, slot) in def.slots.iter().enumerate() {
            if !scalar_carrier_ty(&slot.ty) {
                return Err(cx.refuse(
                    "Inst::OpenFrame",
                    format!(
                        "frame #{} slot {index} (`{}`) has type {}: only scalar integer, Bool, \
                         F32/F64 and thin-pointer slots have a frame layout here (aggregate, \
                         vector, fat-pointer, handle, Char, F16 and refined slots are not lowered)",
                        def.id.index(),
                        slot.name,
                        slot.ty
                    ),
                ));
            }
            let lir = carrier(&slot.ty)?;
            let slot_align = lir.align().max(1);
            let offset = align_up(cursor, slot_align)
                .ok_or_else(|| cx.refuse("Inst::OpenFrame", "frame layout overflows u32"))?;
            cursor = offset
                .checked_add(lir.bytes())
                .ok_or_else(|| cx.refuse("Inst::OpenFrame", "frame layout overflows u32"))?;
            align = align.max(slot_align);
            slots.push(PlannedSlot {
                ty: slot.ty.clone(),
                carrier: lir,
                offset,
            });
        }
        let bytes = align_up(cursor.max(8), 8)
            .ok_or_else(|| cx.refuse("Inst::OpenFrame", "frame layout overflows u32"))?;
        class_index.insert(root, plan.frames.len());
        class_open.push(*open);
        plan.frames.push(FramePlan {
            frame_id: def.id.index(),
            slots,
            bytes,
            align,
        });
    }
    let mut closed_classes: HashSet<usize> = HashSet::new();
    for (frame, _) in closes {
        let root = classes.find(frame);
        if let Some(&index) = class_index.get(&root) {
            closed_classes.insert(index);
        }
    }
    for (index, open) in class_open.iter().enumerate() {
        if !closed_classes.contains(&index) {
            return Err(cx.refuse(
                "Inst::OpenFrame",
                format!(
                    "frame opened at {open:?} is never closed: no CloseFrame ends its lifetime \
                     (trust-ir BindingFrameUnclosed)"
                ),
            ));
        }
    }
    for value in &frames {
        let root = classes.find(*value);
        let Some(&index) = class_index.get(&root) else {
            return Err(cx.refuse(
                "Inst::OpenFrame",
                format!("frame handle {value:?} descends from no OpenFrame"),
            ));
        };
        plan.frame_of.insert(*value, index);
    }

    // Slot indices and types agree with the frame definition.
    for node in function.blocks.iter().flat_map(|block| &block.body) {
        match &node.inst {
            Inst::BindSlot { frame, slot, value } => {
                let frame_plan = plan.frame(*frame).ok_or_else(|| {
                    cx.refuse("Inst::BindSlot", format!("no frame plan for {frame:?}"))
                })?;
                let slot_plan = frame_plan.slots.get(*slot as usize).ok_or_else(|| {
                    cx.refuse(
                        "Inst::BindSlot",
                        format!(
                            "slot {slot} is out of range for frame #{} of {} slots",
                            frame_plan.frame_id,
                            frame_plan.slots.len()
                        ),
                    )
                })?;
                match value_ty.get(value) {
                    Some(ty) if *ty == slot_plan.ty => {}
                    Some(ty) => {
                        return Err(cx.refuse(
                            "Inst::BindSlot",
                            format!(
                                "binds a {ty} value into slot {slot} of frame #{}, declared {}",
                                frame_plan.frame_id, slot_plan.ty
                            ),
                        ));
                    }
                    None => {
                        return Err(cx.refuse(
                            "Inst::BindSlot",
                            format!("the type of bound value {value:?} is not determined"),
                        ));
                    }
                }
            }
            Inst::LoadSlot { frame, slot, ty } => {
                let frame_plan = plan.frame(*frame).ok_or_else(|| {
                    cx.refuse("Inst::LoadSlot", format!("no frame plan for {frame:?}"))
                })?;
                let slot_plan = frame_plan.slots.get(*slot as usize).ok_or_else(|| {
                    cx.refuse(
                        "Inst::LoadSlot",
                        format!(
                            "slot {slot} is out of range for frame #{} of {} slots",
                            frame_plan.frame_id,
                            frame_plan.slots.len()
                        ),
                    )
                })?;
                if *ty != slot_plan.ty {
                    return Err(cx.refuse(
                        "Inst::LoadSlot",
                        format!(
                            "reads slot {slot} of frame #{} at {ty}, declared {}",
                            frame_plan.frame_id, slot_plan.ty
                        ),
                    ));
                }
            }
            _ => {}
        }
    }

    refuse_superseded_live_handles(cx, &frames, plan)?;
    Ok(frames)
}

/// In-place slot storage honours trust-ir's FUNCTIONAL `BindSlot` only when,
/// after every write to a frame's storage (its `OpenFrame`, each `BindSlot`
/// of its lineage), no handle of that lineage other than the write's own
/// result is still live. Checked by backward SSA liveness over the frame
/// handles (live-out seeded from every successor's live-in, so a superseded
/// handle read in a later block counts); refused wherever the check fails.
fn refuse_superseded_live_handles(
    cx: &Context<'_>,
    frames: &HashSet<ValueId>,
    plan: &LegalizationPlan,
) -> Result<(), AdapterError> {
    let function = cx.function;
    // A `CloseFrame` reads no slot, so closing through a superseded handle
    // observes nothing the in-place storage changed; it is not a use here.
    let frame_uses = |node: &InstrNode| -> Vec<ValueId> {
        if matches!(node.inst, Inst::CloseFrame { .. }) {
            return Vec::new();
        }
        operands(&node.inst)
            .into_iter()
            .filter(|operand| frames.contains(operand))
            .collect()
    };
    let mut live_in: HashMap<BlockId, BTreeSet<ValueId>> = HashMap::new();
    loop {
        let mut changed = false;
        for block in function.blocks.iter().rev() {
            let mut live: BTreeSet<ValueId> = BTreeSet::new();
            for successor in cx.successors(block) {
                if let Some(set) = live_in.get(&successor) {
                    live.extend(set.iter().copied());
                }
            }
            for node in block.body.iter().rev() {
                for result in &node.results {
                    live.remove(result);
                }
                live.extend(frame_uses(node));
            }
            for (param, _) in &block.params {
                live.remove(param);
            }
            if live_in.get(&block.id) != Some(&live) {
                live_in.insert(block.id, live);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let class_of = |value: &ValueId| plan.frame_of.get(value).copied();
    for block in &function.blocks {
        let mut live: BTreeSet<ValueId> = BTreeSet::new();
        for successor in cx.successors(block) {
            if let Some(set) = live_in.get(&successor) {
                live.extend(set.iter().copied());
            }
        }
        for node in block.body.iter().rev() {
            if matches!(node.inst, Inst::OpenFrame { .. } | Inst::BindSlot { .. })
                && let Some(result) = node.results.first()
                && let Some(class) = class_of(result)
                && let Some(stale) = live
                    .iter()
                    .find(|value| *value != result && class_of(value) == Some(class))
            {
                return Err(cx.refuse(
                    if matches!(node.inst, Inst::OpenFrame { .. }) {
                        "Inst::OpenFrame"
                    } else {
                        "Inst::BindSlot"
                    },
                    format!(
                        "frame handle {stale:?} is still live after {result:?} rewrites its \
                         frame: BindSlot is functional in trust-ir (an older handle keeps its \
                         prior slots) and this backend's in-place slot storage cannot honour a \
                         superseded handle"
                    ),
                ));
            }
            for result in &node.results {
                live.remove(result);
            }
            live.extend(frame_uses(node));
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Borrows
// ---------------------------------------------------------------------------

fn plan_borrows<S: std::hash::BuildHasher>(
    cx: &Context<'_>,
    value_ty: &std::collections::HashMap<ValueId, Ty, S>,
    frames: &HashSet<ValueId>,
    plan: &mut LegalizationPlan,
) -> Result<(), AdapterError> {
    for node in cx.function.blocks.iter().flat_map(|block| &block.body) {
        match &node.inst {
            Inst::Borrow { ptr } | Inst::BorrowMut { ptr } => {
                let unique = matches!(node.inst, Inst::BorrowMut { .. });
                let construct = if unique {
                    "Inst::BorrowMut"
                } else {
                    "Inst::Borrow"
                };
                let [result] = node.results.as_slice() else {
                    return Err(cx.refuse(
                        construct,
                        format!(
                            "declares {} results; a borrow defines one",
                            node.results.len()
                        ),
                    ));
                };
                if frames.contains(ptr) {
                    return Err(cx.refuse(
                        construct,
                        format!("borrows frame handle {ptr:?}, which is not an address"),
                    ));
                }
                let ty = value_ty.get(ptr).ok_or_else(|| {
                    cx.refuse(
                        construct,
                        format!("the type of borrowed operand {ptr:?} is not determined"),
                    )
                })?;
                if !borrowable_ty(ty) {
                    return Err(cx.refuse(
                        construct,
                        format!(
                            "borrows a non-addressable value {ptr:?} of type {ty}: a borrow takes \
                             a thin or fat pointer"
                        ),
                    ));
                }
                if definitely_null(cx, *ptr) {
                    return Err(cx.refuse(
                        construct,
                        format!(
                            "borrows {ptr:?}, which is the null pointer: a borrow of null is \
                             undefined behaviour in trust-ir (the reference interpreter faults \
                             on it), not an address to copy"
                        ),
                    ));
                }
                if unique && matches!(ty, Ty::Ref(_) | Ty::PtrConst(_)) {
                    return Err(cx.refuse(
                        construct,
                        format!(
                            "unique borrow of {ptr:?} through a shared {ty}: a shared-to-unique \
                             upgrade is not a reborrow trust-ir admits (BorrowMutThroughSharedRef)"
                        ),
                    ));
                }
                if unique && may_root_at_shared_borrow(cx, *ptr) {
                    return Err(cx.refuse(
                        construct,
                        format!(
                            "unique borrow of {ptr:?}, which may be the result of a shared \
                             Borrow: a shared-to-unique reborrow is not admitted \
                             (BorrowMutThroughSharedRef)"
                        ),
                    ));
                }
                let root = borrow_root(cx, *ptr);
                plan.borrows.insert(
                    *result,
                    BorrowPlan {
                        root,
                        kind: if unique {
                            BorrowKind::Unique
                        } else {
                            BorrowKind::Shared
                        },
                    },
                );
            }
            Inst::EndBorrow { borrow_ptr } => {
                let is_borrow = cx.defs.get(borrow_ptr).is_some_and(|def| {
                    matches!(def.inst, Inst::Borrow { .. } | Inst::BorrowMut { .. })
                });
                if !is_borrow {
                    return Err(cx.refuse(
                        "Inst::EndBorrow",
                        format!(
                            "retires {borrow_ptr:?}, which no Borrow/BorrowMut defines \
                             (EndBorrowOfNonBorrow)"
                        ),
                    ));
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// Is `value` statically the null pointer: `NullPtr` or a zero pointer
/// constant, through `Copy` and `Cast PtrToPtr`? (A value that is null only
/// on some paths, or only at run time, is not decided here.)
fn definitely_null(cx: &Context<'_>, value: ValueId) -> bool {
    let mut cursor = value;
    for _ in 0..=cx.defs.len() {
        match cx.defs.get(&cursor).map(|node| &node.inst) {
            Some(Inst::NullPtr) => return true,
            Some(Inst::Const {
                ty,
                value: trust_ir::Constant::Int(0),
            }) => return borrowable_ty(ty),
            Some(
                Inst::Copy { operand, .. }
                | Inst::Cast {
                    op: CastOp::PtrToPtr,
                    operand,
                    ..
                },
            ) => cursor = *operand,
            _ => return false,
        }
    }
    false
}

/// The first value in `value`'s borrow chain that no borrow defines.
fn borrow_root(cx: &Context<'_>, value: ValueId) -> ValueId {
    let mut cursor = value;
    for _ in 0..=cx.defs.len() {
        match cx.defs.get(&cursor).map(|node| &node.inst) {
            Some(Inst::Borrow { ptr } | Inst::BorrowMut { ptr }) => cursor = *ptr,
            _ => break,
        }
    }
    cursor
}

/// Can `address` be the result of a SHARED `Borrow` on any path? The same
/// trace as trust-ir-build's `may_root_at_shared_borrow`: `GEP` base, `Copy`,
/// `Cast PtrToPtr`, both `Select` arms and every incoming argument of a block
/// parameter.
fn may_root_at_shared_borrow(cx: &Context<'_>, address: ValueId) -> bool {
    let mut seen = HashSet::new();
    let mut stack = vec![address];
    while let Some(current) = stack.pop() {
        if !seen.insert(current) {
            continue;
        }
        if let Some(node) = cx.defs.get(&current) {
            match &node.inst {
                Inst::Borrow { .. } => return true,
                Inst::GEP { base, .. } => stack.push(*base),
                Inst::Copy { operand, .. }
                | Inst::Cast {
                    op: CastOp::PtrToPtr,
                    operand,
                    ..
                } => stack.push(*operand),
                Inst::Select {
                    then_val, else_val, ..
                } => {
                    stack.push(*then_val);
                    stack.push(*else_val);
                }
                _ => {}
            }
        } else if cx.params.contains_key(&current)
            && let Some(args) = cx.incoming.get(&current)
        {
            stack.extend(args.iter().copied());
        }
    }
    false
}

// ---------------------------------------------------------------------------
// Undef and poison
// ---------------------------------------------------------------------------

/// Per-handle slot state for the poison trace: slots every path has bound
/// (`None` = not yet known, the optimistic top) and slots some path bound to
/// poison.
#[derive(Default, Clone, PartialEq, Eq)]
struct SlotState {
    bound: Option<BTreeSet<u32>>,
    poisoned: BTreeSet<u32>,
}

fn plan_undefs(
    cx: &Context<'_>,
    frames: &HashSet<ValueId>,
    plan: &mut LegalizationPlan,
) -> Result<(), AdapterError> {
    let function = cx.function;
    // Admission of each Undef on its own.
    for node in function.blocks.iter().flat_map(|block| &block.body) {
        let Inst::Undef { ty } = &node.inst else {
            continue;
        };
        if matches!(ty, Ty::Unit | Ty::Never) {
            continue;
        }
        if node
            .proofs
            .iter()
            .any(|proof| matches!(proof, ProofAnnotation::FreshSymbolicHavoc))
        {
            return Err(cx.refuse(
                "Inst::Undef",
                "a FreshSymbolicHavoc-marked undef is a nondeterministic-choice marker, not \
                 poison; it stays outside the lowering-target subset and a narrowing consumer \
                 must refuse it (must-refuse row refuse/undef_fresh_havoc_feeds_assume)",
            ));
        }
        if !node.proofs.is_empty() {
            return Err(cx.refuse(
                "Inst::Undef",
                "an undef carries proof annotations: a claim about a poison value has no value \
                 to hold of, and the NoUndef zero model would make it look discharged",
            ));
        }
        let [result] = node.results.as_slice() else {
            return Err(cx.refuse(
                "Inst::Undef",
                format!(
                    "declares {} results; exactly one is defined",
                    node.results.len()
                ),
            ));
        };
        if !scalar_carrier_ty(ty) {
            return Err(cx.refuse(
                "Inst::Undef",
                format!(
                    "undef of type {ty}: only scalar integer, Bool, F32/F64 and thin-pointer \
                     poison is materialized; aggregate/vector poison is unmodelled by the pinned \
                     trust-ir reference semantics, and Char/F16/refined/fat-pointer/handle undef \
                     is outside the lowering-target subset or this carrier set"
                ),
            ));
        }
        plan.undefs.insert(*result);
    }

    // Forward may-poison trace to a fixpoint.
    let mut poison: HashMap<ValueId, String> = HashMap::new();
    let mut slots: HashMap<ValueId, SlotState> = HashMap::new();
    let frame_id_of = |handle: &ValueId| plan.frame(*handle).map_or(0, |frame| frame.frame_id);
    loop {
        let mut changed = false;
        for block in &function.blocks {
            for node in &block.body {
                let result = node.results.first().copied();
                match &node.inst {
                    Inst::Undef { .. } => {
                        if let Some(result) = result
                            && plan.undefs.contains(&result)
                            && !poison.contains_key(&result)
                        {
                            poison.insert(result, format!("Inst::Undef {result:?}"));
                            changed = true;
                        }
                    }
                    Inst::Copy { operand, .. } => {
                        if let (Some(result), Some(origin)) = (result, poison.get(operand))
                            && !poison.contains_key(&result)
                        {
                            poison.insert(result, origin.clone());
                            changed = true;
                        }
                    }
                    Inst::Select {
                        then_val, else_val, ..
                    } => {
                        let origin = poison.get(then_val).or_else(|| poison.get(else_val));
                        if let (Some(result), Some(origin)) = (result, origin)
                            && !poison.contains_key(&result)
                        {
                            poison.insert(result, origin.clone());
                            changed = true;
                        }
                    }
                    Inst::OpenFrame { .. } => {
                        if let Some(result) = result {
                            let fresh = SlotState {
                                bound: Some(BTreeSet::new()),
                                poisoned: BTreeSet::new(),
                            };
                            if slots.get(&result) != Some(&fresh) {
                                slots.insert(result, fresh);
                                changed = true;
                            }
                        }
                    }
                    Inst::BindSlot { frame, slot, value } => {
                        if let Some(result) = result {
                            let input = slots.get(frame).cloned().unwrap_or_default();
                            let mut next = SlotState {
                                bound: input.bound.map(|mut bound| {
                                    bound.insert(*slot);
                                    bound
                                }),
                                poisoned: input.poisoned,
                            };
                            next.poisoned.remove(slot);
                            if poison.contains_key(value) {
                                next.poisoned.insert(*slot);
                            }
                            if slots.get(&result) != Some(&next) {
                                slots.insert(result, next);
                                changed = true;
                            }
                        }
                    }
                    Inst::LoadSlot { frame, slot, .. } => {
                        if let Some(result) = result
                            && !poison.contains_key(&result)
                            && let Some(state) = slots.get(frame)
                        {
                            let unbound = state
                                .bound
                                .as_ref()
                                .is_some_and(|bound| !bound.contains(slot));
                            let poisoned = state.poisoned.contains(slot);
                            if unbound || poisoned {
                                poison.insert(
                                    result,
                                    format!(
                                        "LoadSlot {result:?} of slot {slot} of frame #{}, which \
                                         may be {}",
                                        frame_id_of(frame),
                                        if unbound {
                                            "unbound"
                                        } else {
                                            "bound to poison"
                                        }
                                    ),
                                );
                                changed = true;
                            }
                        }
                    }
                    _ => {}
                }
                for (target, args) in edges(&node.inst) {
                    let Some(target) = cx.blocks.get(&target) else {
                        continue;
                    };
                    for ((param, _), arg) in target.params.iter().zip(args) {
                        if let Some(origin) = poison.get(arg)
                            && !poison.contains_key(param)
                        {
                            poison.insert(*param, origin.clone());
                            changed = true;
                        }
                    }
                }
            }
            // Frame-handle parameters: meet over every incoming handle.
            for (param, _) in &block.params {
                if !frames.contains(param) {
                    continue;
                }
                let mut met: Option<SlotState> = None;
                for arg in cx.incoming.get(param).into_iter().flatten() {
                    let Some(state) = slots.get(arg) else {
                        continue;
                    };
                    met = Some(match met {
                        None => state.clone(),
                        Some(mut acc) => {
                            acc.bound = match (acc.bound, &state.bound) {
                                (None, other) => other.clone(),
                                (Some(bound), None) => Some(bound),
                                (Some(bound), Some(other)) => {
                                    Some(bound.intersection(other).copied().collect())
                                }
                            };
                            acc.poisoned.extend(state.poisoned.iter().copied());
                            acc
                        }
                    });
                }
                if let Some(met) = met
                    && slots.get(param) != Some(&met)
                {
                    slots.insert(*param, met);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Every poison value may only be transported.
    for node in function.blocks.iter().flat_map(|block| &block.body) {
        for operand in inspected_operands(&node.inst) {
            if let Some(origin) = poison.get(&operand) {
                return Err(cx.refuse(
                    "Inst::Undef",
                    format!(
                        "poison value {operand:?} (from {origin}) reaches an inspecting use in \
                         Inst::{}: trust-ir makes inspecting poison undefined behaviour \
                         (ub-numerics-policy §4), and the NoUndef zero model would present a \
                         defined result instead; poison may only be copied, selected as an \
                         arm, stored plainly, bound into a frame slot or passed as a block \
                         argument",
                        inst_name(&node.inst)
                    ),
                ));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::inst::BindingSlot;
    use trust_ir::value::BindingFrameId;
    use trust_ir::{BinOp, Block, FuncTyId, Function};

    fn v(index: u32) -> ValueId {
        ValueId::new(index)
    }

    fn b(index: u32) -> BlockId {
        BlockId::new(index)
    }

    fn node(inst: Inst, results: &[u32]) -> InstrNode {
        let mut node = InstrNode::new(inst);
        node.results = results.iter().copied().map(v).collect();
        node
    }

    fn function(blocks: Vec<Block>) -> Function {
        let mut function =
            Function::new(trust_ir::FuncId::new(0), "bfu_unit", FuncTyId::new(0), b(0));
        function.blocks = blocks;
        function
    }

    fn block(id: u32, params: Vec<(u32, Ty)>, body: Vec<InstrNode>) -> Block {
        Block {
            id: b(id),
            params: params
                .into_iter()
                .map(|(value, ty)| (v(value), ty))
                .collect(),
            body,
        }
    }

    fn types(function: &Function) -> HashMap<ValueId, Ty> {
        let mut map = HashMap::new();
        for block in &function.blocks {
            for (param, ty) in &block.params {
                map.insert(*param, ty.clone());
            }
            for node in &block.body {
                let ty = match &node.inst {
                    Inst::Const { ty, .. }
                    | Inst::Undef { ty }
                    | Inst::Copy { ty, .. }
                    | Inst::BinOp { ty, .. }
                    | Inst::LoadSlot { ty, .. } => Some(ty.clone()),
                    Inst::OpenFrame { .. }
                    | Inst::BindSlot { .. }
                    | Inst::Borrow { .. }
                    | Inst::BorrowMut { .. }
                    | Inst::Alloca { .. } => Some(Ty::Ptr),
                    _ => None,
                };
                if let (Some(ty), Some(result)) = (ty, node.results.first()) {
                    map.insert(*result, ty);
                }
            }
        }
        map
    }

    fn carrier(ty: &Ty) -> Result<Type, AdapterError> {
        crate::adapter::translate_type(ty)
    }

    fn plan(function: &Function) -> Result<Option<LegalizationPlan>, AdapterError> {
        plan_function(function, &types(function), &carrier)
    }

    fn refused(function: &Function, needle: &str) {
        match plan(function) {
            Err(AdapterError::LegalizationRefused { reason, .. }) => {
                assert!(reason.contains(needle), "`{needle}` not in `{reason}`");
            }
            other => panic!("expected a LegalizationRefused naming `{needle}`, got {other:?}"),
        }
    }

    fn frame(slots: Vec<Ty>) -> Inst {
        Inst::OpenFrame {
            def: BindingFrameDef::new(
                BindingFrameId::new(0),
                "unit",
                slots
                    .into_iter()
                    .enumerate()
                    .map(|(index, ty)| BindingSlot::new(format!("s{index}"), ty))
                    .collect(),
            ),
        }
    }

    #[test]
    fn a_function_without_the_constructs_is_not_planned() {
        let f = function(vec![block(
            0,
            vec![(0, Ty::I64)],
            vec![node(Inst::Return { values: vec![v(0)] }, &[])],
        )]);
        assert!(plan(&f).unwrap().is_none());
    }

    #[test]
    fn frame_layout_follows_the_slot_carriers() {
        let f = function(vec![block(
            0,
            vec![(0, Ty::I64), (1, Ty::U8)],
            vec![
                node(frame(vec![Ty::U8, Ty::I64, Ty::I32]), &[2]),
                node(
                    Inst::BindSlot {
                        frame: v(2),
                        slot: 1,
                        value: v(0),
                    },
                    &[3],
                ),
                node(
                    Inst::BindSlot {
                        frame: v(3),
                        slot: 0,
                        value: v(1),
                    },
                    &[4],
                ),
                node(
                    Inst::LoadSlot {
                        frame: v(4),
                        slot: 1,
                        ty: Ty::I64,
                    },
                    &[5],
                ),
                node(Inst::CloseFrame { frame: v(4) }, &[]),
                node(Inst::Return { values: vec![v(5)] }, &[]),
            ],
        )]);
        let plan = plan(&f).unwrap().unwrap();
        let frame = plan.frame(v(4)).unwrap();
        let offsets: Vec<u32> = frame.slots.iter().map(|slot| slot.offset).collect();
        assert_eq!(offsets, [0, 8, 16]);
        assert_eq!((frame.bytes, frame.align), (24, 8));
    }

    #[test]
    fn a_superseded_handle_read_after_a_rebind_is_refused() {
        let f = function(vec![block(
            0,
            vec![(0, Ty::I64), (1, Ty::I64)],
            vec![
                node(frame(vec![Ty::I64]), &[2]),
                node(
                    Inst::BindSlot {
                        frame: v(2),
                        slot: 0,
                        value: v(0),
                    },
                    &[3],
                ),
                node(
                    Inst::BindSlot {
                        frame: v(3),
                        slot: 0,
                        value: v(1),
                    },
                    &[4],
                ),
                // `%3` still holds `%0` in trust-ir; in-place storage holds `%1`.
                node(
                    Inst::LoadSlot {
                        frame: v(3),
                        slot: 0,
                        ty: Ty::I64,
                    },
                    &[5],
                ),
                node(Inst::CloseFrame { frame: v(4) }, &[]),
                node(Inst::Return { values: vec![v(5)] }, &[]),
            ],
        )]);
        refused(&f, "still live after");
    }

    /// The superseded handle is read in a SUCCESSOR block: only the
    /// live-out seeding from successor blocks sees it. In trust-ir `%5`
    /// is `%0`; in-place storage would read `%1`.
    #[test]
    fn a_superseded_handle_read_in_a_successor_block_is_refused() {
        let f = function(vec![
            block(
                0,
                vec![(0, Ty::I64), (1, Ty::I64)],
                vec![
                    node(frame(vec![Ty::I64]), &[2]),
                    node(
                        Inst::BindSlot {
                            frame: v(2),
                            slot: 0,
                            value: v(0),
                        },
                        &[3],
                    ),
                    node(
                        Inst::BindSlot {
                            frame: v(3),
                            slot: 0,
                            value: v(1),
                        },
                        &[4],
                    ),
                    node(
                        Inst::Br {
                            target: b(1),
                            args: vec![],
                        },
                        &[],
                    ),
                ],
            ),
            block(
                1,
                vec![],
                vec![
                    node(
                        Inst::LoadSlot {
                            frame: v(3),
                            slot: 0,
                            ty: Ty::I64,
                        },
                        &[5],
                    ),
                    node(Inst::CloseFrame { frame: v(4) }, &[]),
                    node(Inst::Return { values: vec![v(5)] }, &[]),
                ],
            ),
        ]);
        refused(&f, "still live after");
    }

    /// A slot bound on one `CondBr` arm only is unbound on the other, so the
    /// frame-parameter meet must INTERSECT the bound sets: the load after the
    /// merge may read poison, and returning it inspects it.
    #[test]
    fn a_slot_bound_on_one_path_only_is_refused_when_inspected_after_the_merge() {
        let f = function(vec![
            block(
                0,
                vec![(0, Ty::Bool), (1, Ty::I64)],
                vec![
                    node(frame(vec![Ty::I64]), &[2]),
                    node(
                        Inst::CondBr {
                            cond: v(0),
                            then_target: b(1),
                            then_args: vec![],
                            else_target: b(2),
                            else_args: vec![],
                        },
                        &[],
                    ),
                ],
            ),
            block(
                1,
                vec![],
                vec![
                    node(
                        Inst::BindSlot {
                            frame: v(2),
                            slot: 0,
                            value: v(1),
                        },
                        &[3],
                    ),
                    node(
                        Inst::Br {
                            target: b(3),
                            args: vec![v(3)],
                        },
                        &[],
                    ),
                ],
            ),
            block(
                2,
                vec![],
                vec![node(
                    Inst::Br {
                        target: b(3),
                        args: vec![v(2)],
                    },
                    &[],
                )],
            ),
            block(
                3,
                vec![(4, Ty::Ptr)],
                vec![
                    node(
                        Inst::LoadSlot {
                            frame: v(4),
                            slot: 0,
                            ty: Ty::I64,
                        },
                        &[5],
                    ),
                    node(Inst::CloseFrame { frame: v(4) }, &[]),
                    node(Inst::Return { values: vec![v(5)] }, &[]),
                ],
            ),
        ]);
        refused(&f, "may be unbound");
    }

    /// Only a PLAIN store transports poison; a volatile store inspects it
    /// (the reference interpreter faults on it).
    #[test]
    fn a_volatile_store_of_undef_is_refused() {
        let f = function(vec![block(
            0,
            vec![(0, Ty::I64)],
            vec![
                node(Inst::Undef { ty: Ty::I64 }, &[1]),
                node(
                    Inst::Alloca {
                        ty: Ty::I64,
                        count: None,
                        align: None,
                    },
                    &[2],
                ),
                node(
                    Inst::Store {
                        ty: Ty::I64,
                        ptr: v(2),
                        value: v(1),
                        volatile: true,
                        align: None,
                    },
                    &[],
                ),
                node(Inst::Return { values: vec![v(0)] }, &[]),
            ],
        )]);
        refused(&f, "reaches an inspecting use in Inst::Store");
    }

    /// A back edge into the entry block that carries a frame handle: on
    /// function entry the same parameter holds the caller's argument.
    #[test]
    fn a_frame_handle_in_an_entry_block_parameter_is_refused() {
        let f = function(vec![
            block(
                0,
                vec![(0, Ty::Bool), (1, Ty::Ptr), (2, Ty::I64)],
                vec![
                    node(
                        Inst::LoadSlot {
                            frame: v(1),
                            slot: 0,
                            ty: Ty::I64,
                        },
                        &[3],
                    ),
                    node(frame(vec![Ty::I64]), &[4]),
                    node(
                        Inst::BindSlot {
                            frame: v(4),
                            slot: 0,
                            value: v(2),
                        },
                        &[5],
                    ),
                    node(
                        Inst::CondBr {
                            cond: v(0),
                            then_target: b(0),
                            then_args: vec![v(0), v(5), v(3)],
                            else_target: b(1),
                            else_args: vec![],
                        },
                        &[],
                    ),
                ],
            ),
            block(
                1,
                vec![],
                vec![
                    node(Inst::CloseFrame { frame: v(5) }, &[]),
                    node(Inst::Return { values: vec![v(3)] }, &[]),
                ],
            ),
        ]);
        refused(&f, "entry-block parameter");
    }

    /// A borrow of a FAT pointer is admitted (the result keeps the fat
    /// type in trust-ir) and records its root like a thin one.
    #[test]
    fn a_fat_pointer_borrow_and_reborrow_record_their_root() {
        let fat = Ty::FatPtr(trust_ir::FatPtrKind::Str);
        let f = function(vec![block(
            0,
            vec![(0, fat)],
            vec![
                node(Inst::Borrow { ptr: v(0) }, &[1]),
                node(Inst::Borrow { ptr: v(1) }, &[2]),
                node(Inst::EndBorrow { borrow_ptr: v(2) }, &[]),
                node(Inst::EndBorrow { borrow_ptr: v(1) }, &[]),
                node(Inst::Return { values: vec![] }, &[]),
            ],
        )]);
        let plan = plan(&f).unwrap().unwrap();
        for borrow in [v(1), v(2)] {
            let planned = plan.borrow(borrow).unwrap();
            assert_eq!((planned.root, planned.kind), (v(0), BorrowKind::Shared));
        }
    }

    #[test]
    fn a_frame_handle_escaping_to_a_return_is_refused() {
        let f = function(vec![block(
            0,
            vec![],
            vec![
                node(frame(vec![Ty::I64]), &[0]),
                node(Inst::CloseFrame { frame: v(0) }, &[]),
                node(Inst::Return { values: vec![v(0)] }, &[]),
            ],
        )]);
        refused(&f, "escapes into Inst::Return");
    }

    #[test]
    fn an_unclosed_frame_is_refused() {
        let f = function(vec![block(
            0,
            vec![],
            vec![
                node(frame(vec![Ty::I64]), &[0]),
                node(Inst::Return { values: vec![] }, &[]),
            ],
        )]);
        refused(&f, "never closed");
    }

    #[test]
    fn a_read_of_an_unbound_slot_that_is_inspected_is_refused() {
        let f = function(vec![block(
            0,
            vec![],
            vec![
                node(frame(vec![Ty::I64]), &[0]),
                node(
                    Inst::LoadSlot {
                        frame: v(0),
                        slot: 0,
                        ty: Ty::I64,
                    },
                    &[1],
                ),
                node(Inst::CloseFrame { frame: v(0) }, &[]),
                node(Inst::Return { values: vec![v(1)] }, &[]),
            ],
        )]);
        refused(&f, "may be unbound");
    }

    #[test]
    fn undef_masked_by_arithmetic_is_refused_as_inspection() {
        let f = function(vec![block(
            0,
            vec![],
            vec![
                node(Inst::Undef { ty: Ty::I64 }, &[0]),
                node(
                    Inst::Const {
                        ty: Ty::I64,
                        value: trust_ir::Constant::Int(0),
                    },
                    &[1],
                ),
                node(
                    Inst::BinOp {
                        op: BinOp::And,
                        ty: Ty::I64,
                        lhs: v(0),
                        rhs: v(1),
                    },
                    &[2],
                ),
                node(Inst::Return { values: vec![v(2)] }, &[]),
            ],
        )]);
        refused(&f, "reaches an inspecting use in Inst::BinOp");
    }

    #[test]
    fn select_cond_is_inspected_while_its_arms_are_transported() {
        let transported = inspected_operands(&Inst::Select {
            ty: Ty::I64,
            cond: v(0),
            then_val: v(1),
            else_val: v(1),
        });
        assert_eq!(transported, [v(0)]);
        let same = inspected_operands(&Inst::Select {
            ty: Ty::I64,
            cond: v(1),
            then_val: v(1),
            else_val: v(2),
        });
        assert_eq!(same, [v(1)]);
    }

    #[test]
    fn a_unique_borrow_of_a_shared_borrow_is_refused() {
        let f = function(vec![block(
            0,
            vec![(0, Ty::Ptr)],
            vec![
                node(Inst::Borrow { ptr: v(0) }, &[1]),
                node(Inst::BorrowMut { ptr: v(1) }, &[2]),
                node(Inst::Return { values: vec![v(2)] }, &[]),
            ],
        )]);
        refused(&f, "BorrowMutThroughSharedRef");
    }

    #[test]
    fn a_borrow_of_the_null_pointer_is_refused() {
        let f = function(vec![block(
            0,
            vec![],
            vec![
                node(Inst::NullPtr, &[0]),
                node(
                    Inst::Copy {
                        ty: Ty::Ptr,
                        operand: v(0),
                    },
                    &[1],
                ),
                node(Inst::Borrow { ptr: v(1) }, &[2]),
                node(Inst::Return { values: vec![] }, &[]),
            ],
        )]);
        refused(&f, "the null pointer");
    }

    #[test]
    fn an_end_borrow_of_a_non_borrow_is_refused() {
        let f = function(vec![block(
            0,
            vec![(0, Ty::Ptr)],
            vec![
                node(Inst::EndBorrow { borrow_ptr: v(0) }, &[]),
                node(Inst::Return { values: vec![] }, &[]),
            ],
        )]);
        refused(&f, "EndBorrowOfNonBorrow");
    }

    #[test]
    fn a_reborrow_chain_records_its_root() {
        let f = function(vec![block(
            0,
            vec![(0, Ty::Ptr)],
            vec![
                node(Inst::BorrowMut { ptr: v(0) }, &[1]),
                node(Inst::Borrow { ptr: v(1) }, &[2]),
                node(Inst::EndBorrow { borrow_ptr: v(2) }, &[]),
                node(Inst::EndBorrow { borrow_ptr: v(1) }, &[]),
                node(Inst::Return { values: vec![v(0)] }, &[]),
            ],
        )]);
        let plan = plan(&f).unwrap().unwrap();
        let reborrow = plan.borrow(v(2)).unwrap();
        assert_eq!(reborrow.root, v(0));
        assert_eq!(reborrow.kind, BorrowKind::Shared);
    }
}
