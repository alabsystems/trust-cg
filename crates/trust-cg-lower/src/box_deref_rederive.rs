// trust-cg-lower/src/box_deref_rederive.rs - this backend's own re-derivation of BoxDeref validity
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The consumer re-derivation of the validity conjuncts of one trust-ir
//! `Inst::BoxDeref` (wire v74, `SPEC_RATIFICATIONS` section 28), decided from
//! the instructions of its own function and nothing else.
//!
//! # What this is, and what it is not
//!
//! trust-ir's top tier, `ConsumerRederived`, is "evidence every consumer
//! re-derives from the instructions themselves", and no evidence kind of the
//! v74 wire reaches it. This module is THIS backend's re-derivation: a
//! consumer-side decision, used only by the shared acceptance check
//! ([`crate::box_deref::admit_box_derefs`] and the two entries that classify
//! trust-ir's own findings). It is never written back into the module as
//! evidence, it changes no fact, and it licenses no transformation (section
//! 28, "No licence from the undefined behaviour"): an admitted `BoxDeref` is
//! still lowered as the identity on its pointer.
//!
//! It is NOT trust-ir's `ConsumerRederived` tier. That tier is defined as
//! evidence EVERY consumer re-derives, and section 28 states that no
//! evidence reaches it in v74. This module is one consumer's local analysis,
//! so a conjunct it establishes is reported as re-derived by this backend
//! (`BoxDerefManifestRow::rederived`), never under trust-ir's tier name, and
//! it is consulted only at the floors that opt into it
//! ([`crate::box_deref::BoxValidityFloor::rederives`]): never at the default
//! `Refuse` floor, and so never by a proof-emitting, verified-promotion or
//! JIT-verified compile, whose gate is that floor.
//!
//! A conjunct is re-derived only when it holds on EVERY execution the
//! reference semantics allows that reaches the instruction, by an argument
//! that reads only this function: no premise root, no standing assumption,
//! no callee contract, no type invariant of memory. Anything else is
//! reported as not re-derived, with its reason, and the shared acceptance
//! check then keeps trust-ir's floor refusal.
//!
//! # The shapes, and exactly what each establishes
//!
//! The operand is traced backwards through address-preserving definitions
//! (`Cast PtrToPtr` between thin pointers, `Copy`, an earlier `BoxDeref`)
//! and constant-index `GEP`s, whose offset is summed exactly. The chain ends
//! at its ROOT:
//!
//! * a stack slot of this function (`Alloca`): `NonNull` when the access is
//!   in bounds (an address inside an allocation is never 0); `Aligned` when
//!   the slot's alignment and the summed offset are multiples of the
//!   pointee's; `Dereferenceable` when the access is in bounds AND no
//!   instruction on any path from the slot's definition to the deref frees
//!   a value derived from it or lets one escape (section "Liveness").
//! * a Rust-heap allocation of this function (`HeapAlloc`, origin
//!   `RustHeap`): the same three rules, and in addition each conjunct
//!   requires the allocation's success to be TESTED on every path to the
//!   deref (a dominating null test, below). trust-ir's `HeapAlloc` never
//!   fails, but this backend lowers it to an allocator call whose null
//!   result it does not check (`translate_heap_alloc`), so without the test
//!   the conjunct would rest on the allocator succeeding.
//! * anything else (a parameter, a block parameter, a load, a call result):
//!   only `NonNull`, and only from a null test of the same pointer value
//!   whose non-null edge dominates the deref. `Aligned` and
//!   `Dereferenceable` would need the caller's, the callee's or memory's
//!   promise, which is a premise, so they are not re-derived.
//!
//! `MetadataValid` belongs to wide pointees, which v74 has no shape for; it
//! is never re-derived here.
//!
//! # The null test
//!
//! A `CondBr` whose condition is `ICmp Eq|Ne` of (a) a value of the
//! operand's address class against `NullPtr`, or (b) `PtrToInt` of such a
//! value against the integer constant 0, whose non-null successor edge
//! (`else` for `Eq`, `then` for `Ne`) dominates the deref's block
//! (`DominatorTree::edge_dominates`). The address class is the operand and
//! every value equal to it as an address through zero-offset
//! address-preserving definitions, in either direction. A test of another
//! value, even one derived from the same root by an offset, is not a test
//! of this one.
//!
//! # Liveness
//!
//! An instruction lies BETWEEN the root (block `A`, index `i`) and the deref
//! (block `D`, index `j`) when some CFG path runs from just after the root
//! through it to just before the deref without executing the root again:
//! it is after the root (`A` at an index above `i`, or a block reachable
//! from `A`'s successors without entering `A`) and before the deref (`D` at
//! an index below `j`, or a block from whose successors `D` is reachable
//! without entering `A`). The derived set is the root and every value
//! defined from a derived value by `Cast PtrToPtr`, `Copy`, `GEP` (as base)
//! or `BoxDeref`. Between root and deref, a derived value may only be read
//! as an address (`Load`, `Store` address, `GEP` base), re-derived
//! (`PtrToPtr`, `Copy`, `BoxDeref`), compared (`ICmp` of pointers) or turned
//! into an integer whose every use is an `ICmp` (the bridge's null test).
//! Any other use there is an escape (a call or invoke argument, a stored
//! value, a block argument, a return, any other `PtrToInt`, a `Select`, an
//! aggregate, drop glue, any instruction not listed) and a `Dealloc` of it
//! is a free; either
//! refuses `Dereferenceable`. An allocation whose address never escaped
//! cannot be freed by anything else (provenance), so calls that receive no
//! derived value are harmless. Uses after the deref, or on paths that
//! re-execute the root, are not between and do not matter: `Dereferenceable`
//! is a statement about the instruction's own program point (section 28,
//! clause 3), and this module never carries it elsewhere.
//!
//! # Fail-closed preconditions
//!
//! Nothing is re-derived when the function exceeds the analysis budget
//! ([`REDERIVATION_MAX_BLOCKS`], [`REDERIVATION_MAX_INSTRUCTIONS`],
//! [`REDERIVATION_MAX_BOX_DEREFS`]), the CFG is not well formed for
//! dominance, a value has two definitions, the function holds a
//! `CoroSuspend` (a frame
//! that outlives a return), the pointee has no computable byte layout or is
//! uninhabited or zero-sized, a count or index is not a non-negative integer
//! constant, offset arithmetic overflows, or the root does not dominate the
//! deref.
//!
//! # Cost
//!
//! A [`FunctionRederiver`] builds the function's view (definitions,
//! dominator tree, successor lists) once, memoizes each deref's verdict by
//! position, and memoizes the reachability sets, derived sets and integer-use
//! checks the liveness rule asks for. The budget bounds what one function can
//! cost; a function over it is refused in every conjunct, never analysed
//! partially. The bounds are a fail-closed ceiling, not a measured choice:
//! no real program reaches this analysis today.

use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::rc::Rc;

use trust_ir::analysis::DominatorTree;
use trust_ir::box_validity::ValidityConjunct;
use trust_ir::inst::{AllocOrigin, CastOp, ICmpOp};
use trust_ir::{BlockId, Constant, Function, Inst, Module, Ty, ValueId};

/// Where the operand's address chain ends.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RederivedRoot {
    /// An `Alloca` of this function.
    StackSlot,
    /// A `HeapAlloc` (origin `RustHeap`) of this function.
    HeapAllocation,
    /// A value whose allocation this function does not show.
    Opaque,
}

impl RederivedRoot {
    /// The diagnostic spelling.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::StackSlot => "stack_slot",
            Self::HeapAllocation => "heap_allocation",
            Self::Opaque => "opaque",
        }
    }
}

/// Why one conjunct was not re-derived. Each is a refusal reason, never a
/// repair.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NotRederived {
    /// The function has more blocks, instructions or `BoxDeref`s than the
    /// analysis budget admits.
    FunctionTooLarge,
    /// The function is not well formed for this analysis: its CFG has no
    /// usable dominator tree, or a value is defined twice.
    MalformedFunction,
    /// The function holds a `CoroSuspend`.
    Coroutine,
    /// The pointee has no computable byte layout, is uninhabited or is
    /// zero-sized.
    PointeeLayout,
    /// The operand's chain ends at a value whose allocation this function
    /// does not show (a parameter, block parameter, load or call result):
    /// only a caller's, callee's or memory's promise could establish it.
    OperandNotRooted,
    /// A `GEP` on the chain has an index that is not a non-negative integer
    /// constant, or the offset arithmetic overflows.
    OffsetNotConstant,
    /// The allocation's element count is not a positive integer constant,
    /// or its element type has no byte layout.
    AllocationLayout,
    /// The heap allocation's origin is not the Rust heap.
    AllocationOrigin,
    /// The root does not dominate the deref.
    RootNotDominating,
    /// `[offset, offset + size)` is not inside the allocation.
    OutOfBounds,
    /// The allocation's alignment is not a multiple of the pointee's.
    AllocationUnderAligned,
    /// The summed offset is not a multiple of the pointee's alignment.
    OffsetMisaligned,
    /// No null test of the operand's address class has a non-null edge
    /// that dominates the deref.
    NoDominatingNullTest,
    /// A heap allocation whose success is not tested on every path to the
    /// deref.
    AllocationSuccessUntested,
    /// A value derived from the allocation escapes between it and the deref.
    EscapesBeforeDeref,
    /// A value derived from the allocation is deallocated between it and
    /// the deref.
    FreedBeforeDeref,
    /// The conjunct is not one a sized pointee has.
    NotASizedConjunct,
}

impl NotRederived {
    /// The text a refusal carries.
    #[must_use]
    pub const fn reason(self) -> &'static str {
        match self {
            Self::FunctionTooLarge => {
                "the function exceeds the re-derivation budget (blocks, instructions or Box \
                 derefs)"
            }
            Self::MalformedFunction => {
                "the function has no usable dominator tree or defines a value twice"
            }
            Self::Coroutine => "the function holds a coroutine suspension",
            Self::PointeeLayout => {
                "the pointee has no computable, inhabited, positive-size byte layout"
            }
            Self::OperandNotRooted => {
                "the pointer is not traced to an allocation of this function, so only a \
                 caller's, callee's or memory's promise could establish it"
            }
            Self::OffsetNotConstant => {
                "an offset on the pointer's chain is not a non-negative integer constant"
            }
            Self::AllocationLayout => {
                "the allocation's count is not a positive integer constant or its element \
                 has no byte layout"
            }
            Self::AllocationOrigin => "the heap allocation is not a Rust-heap allocation",
            Self::RootNotDominating => "the allocation does not dominate the deref",
            Self::OutOfBounds => "the pointee does not lie inside the allocation",
            Self::AllocationUnderAligned => {
                "the allocation's alignment is not a multiple of the pointee's"
            }
            Self::OffsetMisaligned => {
                "the pointer's offset is not a multiple of the pointee's alignment"
            }
            Self::NoDominatingNullTest => {
                "no null test of this pointer value has a non-null edge dominating the deref"
            }
            Self::AllocationSuccessUntested => {
                "the heap allocation's success is not tested on every path to the deref"
            }
            Self::EscapesBeforeDeref => {
                "a pointer derived from the allocation escapes between the allocation and \
                 the deref"
            }
            Self::FreedBeforeDeref => {
                "a pointer derived from the allocation is deallocated between the allocation \
                 and the deref"
            }
            Self::NotASizedConjunct => "the conjunct belongs to a wide pointee",
        }
    }
}

/// What this backend re-derived about one `BoxDeref`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rederivation {
    /// Where the operand's chain ends (`Opaque` when the analysis did not
    /// get as far as tracing it).
    pub root: RederivedRoot,
    /// One verdict per conjunct of a sized pointee, in canonical order.
    pub conjuncts: [(ValidityConjunct, Result<(), NotRederived>); 3],
}

impl Rederivation {
    fn refused(root: RederivedRoot, why: NotRederived) -> Self {
        Self {
            root,
            conjuncts: ValidityConjunct::THIN.map(|conjunct| (conjunct, Err(why))),
        }
    }

    /// The verdict on `conjunct`.
    pub fn verdict(&self, conjunct: ValidityConjunct) -> Result<(), NotRederived> {
        self.conjuncts
            .iter()
            .find(|(c, _)| *c == conjunct)
            .map_or(Err(NotRederived::NotASizedConjunct), |(_, verdict)| {
                *verdict
            })
    }

    /// Whether `conjunct` was re-derived.
    #[must_use]
    pub fn established(&self, conjunct: ValidityConjunct) -> bool {
        self.verdict(conjunct).is_ok()
    }

    /// The re-derived conjuncts, in canonical order.
    #[must_use]
    pub fn established_conjuncts(&self) -> Vec<ValidityConjunct> {
        self.conjuncts
            .iter()
            .filter(|(_, verdict)| verdict.is_ok())
            .map(|(conjunct, _)| *conjunct)
            .collect()
    }

    /// Whether every conjunct was re-derived.
    #[must_use]
    pub fn is_complete(&self) -> bool {
        self.conjuncts.iter().all(|(_, verdict)| verdict.is_ok())
    }
}

/// The most blocks a function may have for this analysis to run on it.
pub const REDERIVATION_MAX_BLOCKS: usize = 512;
/// The most instructions (summed over every block) a function may have.
pub const REDERIVATION_MAX_INSTRUCTIONS: usize = 4096;
/// The most `BoxDeref` instructions a function may hold.
pub const REDERIVATION_MAX_BOX_DEREFS: usize = 64;

/// Whether `func` is within the analysis budget. Counted before anything
/// else is built, so an over-budget function costs one linear scan.
fn within_budget(func: &Function) -> Result<(), NotRederived> {
    if func.blocks.len() > REDERIVATION_MAX_BLOCKS {
        return Err(NotRederived::FunctionTooLarge);
    }
    let mut instructions = 0usize;
    let mut derefs = 0usize;
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        instructions += 1;
        if matches!(node.inst, Inst::BoxDeref { .. }) {
            derefs += 1;
        }
    }
    if instructions > REDERIVATION_MAX_INSTRUCTIONS || derefs > REDERIVATION_MAX_BOX_DEREFS {
        return Err(NotRederived::FunctionTooLarge);
    }
    Ok(())
}

/// A shared set of block positions (a memoized reachability answer).
type BlockSet = Rc<HashSet<usize>>;

/// Where a value is defined: its block's position in `Function::blocks`, and
/// the instruction index (`None` for a block parameter).
type DefSite = (usize, Option<usize>);

struct FunctionView<'f> {
    func: &'f Function,
    defs: HashMap<ValueId, DefSite>,
    dominators: DominatorTree,
    position: HashMap<BlockId, usize>,
    successors: Vec<Vec<BlockId>>,
    /// Whether the function holds a `CoroSuspend`.
    has_coroutine: bool,
    /// [`Self::reach_avoiding`], by `(from, barrier)`.
    reach_memo: RefCell<HashMap<(usize, usize), BlockSet>>,
    /// [`derived_set`], by root.
    derived_memo: RefCell<HashMap<ValueId, Rc<HashSet<ValueId>>>>,
    /// [`only_compared`], by value.
    compared_memo: RefCell<HashMap<ValueId, bool>>,
}

impl<'f> FunctionView<'f> {
    fn new(func: &'f Function) -> Option<Self> {
        let dominators = DominatorTree::new(func);
        if !dominators.is_well_formed() {
            return None;
        }
        let mut defs = HashMap::new();
        let mut position = HashMap::new();
        let mut successors = Vec::with_capacity(func.blocks.len());
        for (block_pos, block) in func.blocks.iter().enumerate() {
            if position.insert(block.id, block_pos).is_some() {
                return None;
            }
            for (value, _) in &block.params {
                if defs.insert(*value, (block_pos, None)).is_some() {
                    return None;
                }
            }
            for (inst_index, node) in block.body.iter().enumerate() {
                for value in &node.results {
                    if defs.insert(*value, (block_pos, Some(inst_index))).is_some() {
                        return None;
                    }
                }
            }
            successors.push(
                block
                    .body
                    .last()
                    .map(|node| {
                        node.inst
                            .successor_edges()
                            .into_iter()
                            .map(|edge| edge.target)
                            .collect()
                    })
                    .unwrap_or_default(),
            );
        }
        let has_coroutine = func
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|node| matches!(node.inst, Inst::CoroSuspend { .. }));
        Some(Self {
            func,
            defs,
            dominators,
            position,
            successors,
            has_coroutine,
            reach_memo: RefCell::default(),
            derived_memo: RefCell::default(),
            compared_memo: RefCell::default(),
        })
    }

    /// The instruction defining `value`, when an instruction (not a block
    /// parameter) defines it.
    fn def_inst(&self, value: ValueId) -> Option<&'f Inst> {
        let (block_pos, inst_index) = *self.defs.get(&value)?;
        Some(&self.func.blocks[block_pos].body[inst_index?].inst)
    }

    /// Blocks reachable from `from`'s successors without entering
    /// `barrier` (which is neither added nor expanded). Memoized.
    fn reach_avoiding(&self, from: usize, barrier: usize) -> BlockSet {
        if let Some(done) = self.reach_memo.borrow().get(&(from, barrier)) {
            return Rc::clone(done);
        }
        let reached = Rc::new(self.compute_reach_avoiding(from, barrier));
        self.reach_memo
            .borrow_mut()
            .insert((from, barrier), Rc::clone(&reached));
        reached
    }

    fn compute_reach_avoiding(&self, from: usize, barrier: usize) -> HashSet<usize> {
        let mut seen = HashSet::new();
        let mut queue: VecDeque<usize> = VecDeque::new();
        let push = |queue: &mut VecDeque<usize>, seen: &mut HashSet<usize>, id: &BlockId| {
            if let Some(&pos) = self.position.get(id)
                && pos != barrier
                && seen.insert(pos)
            {
                queue.push_back(pos);
            }
        };
        for target in &self.successors[from] {
            push(&mut queue, &mut seen, target);
        }
        while let Some(pos) = queue.pop_front() {
            for target in &self.successors[pos] {
                push(&mut queue, &mut seen, target);
            }
        }
        seen
    }
}

fn is_thin_raw_pointer(ty: &Ty) -> bool {
    matches!(ty, Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_))
}

/// The value of a non-negative integer constant small enough that no
/// integer type of this format reinterprets it, else `None`.
fn small_nonnegative_const(view: &FunctionView<'_>, value: ValueId) -> Option<u64> {
    let Inst::Const {
        ty,
        value: Constant::Int(n),
    } = view.def_inst(value)?
    else {
        return None;
    };
    if !ty.is_integer() {
        return None;
    }
    // Non-negative (the conversion refuses a negative value) and below the
    // sign bit of the narrowest width the type could have (`usize`/`isize`
    // are taken at 16 bits, the narrowest pointer width), so no reading of
    // a non-canonical constant changes it.
    let n = u64::try_from(*n).ok()?;
    let bits = ty.bit_width().unwrap_or(16).min(64);
    (bits >= 2 && n < 1u64 << (bits - 1)).then_some(n)
}

/// `(size, align)` in bytes of `ty` in the module's layout, refusing a type
/// with no byte-granular, power-of-two-aligned, inhabited layout.
fn byte_layout(module: &Module, ty: &Ty) -> Option<(u64, u64)> {
    let layouts = module.layout_table();
    if layouts.ty_is_uninhabited(ty) {
        return None;
    }
    let shape = layouts.ty_layout(ty).ok()?;
    let align_bits = shape.align_bits?;
    if shape.size_bits % 8 != 0 || align_bits % 8 != 0 {
        return None;
    }
    let (size, align) = (shape.size_bits / 8, align_bits / 8);
    align.is_power_of_two().then_some((size, align))
}

/// The address class of `operand`: every value equal to it as an address
/// through zero-offset address-preserving definitions, in either direction.
fn address_class(view: &FunctionView<'_>, operand: ValueId) -> BTreeSet<ValueId> {
    let preserving_source = |inst: &Inst| -> Option<ValueId> {
        match inst {
            Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty,
                dst_ty,
                operand,
            } if is_thin_raw_pointer(src_ty) && is_thin_raw_pointer(dst_ty) => Some(*operand),
            Inst::Copy { operand, .. } | Inst::BoxDeref { operand, .. } => Some(*operand),
            _ => None,
        }
    };
    let mut class = BTreeSet::from([operand]);
    loop {
        let mut grew = false;
        // Backwards: the source of a member's preserving definition.
        for value in class.clone() {
            if let Some(source) = view.def_inst(value).and_then(preserving_source)
                && class.insert(source)
            {
                grew = true;
            }
        }
        // Forwards: every value a preserving definition makes from a member.
        for block in &view.func.blocks {
            for node in &block.body {
                if let Some(source) = preserving_source(&node.inst)
                    && class.contains(&source)
                {
                    for result in &node.results {
                        grew |= class.insert(*result);
                    }
                }
            }
        }
        if !grew {
            return class;
        }
    }
}

/// Whether a null test of a member of `class` has a non-null edge that
/// dominates `deref_block`.
fn null_test_dominates(
    view: &FunctionView<'_>,
    class: &BTreeSet<ValueId>,
    deref_block: BlockId,
) -> bool {
    let is_null_spelling = |value: ValueId, pointer_compare: bool| -> bool {
        match view.def_inst(value) {
            Some(Inst::NullPtr) => pointer_compare,
            Some(Inst::Const {
                ty,
                value: Constant::Int(0),
            }) => !pointer_compare && ty.is_integer(),
            _ => false,
        }
    };
    let is_member = |value: ValueId, pointer_compare: bool| -> bool {
        if pointer_compare {
            return class.contains(&value);
        }
        matches!(
            view.def_inst(value),
            Some(Inst::Cast {
                op: CastOp::PtrToInt,
                operand,
                ..
            }) if class.contains(operand)
        )
    };
    view.func.blocks.iter().any(|block| {
        let Some(Inst::CondBr { cond, .. }) = block.body.last().map(|node| &node.inst) else {
            return false;
        };
        let Some(Inst::ICmp { op, ty, lhs, rhs }) = view.def_inst(*cond) else {
            return false;
        };
        let non_null_successor = match op {
            ICmpOp::Eq => 1,
            ICmpOp::Ne => 0,
            _ => return false,
        };
        let pointer_compare = is_thin_raw_pointer(ty);
        if !pointer_compare && !ty.is_integer() {
            return false;
        }
        let tests_member = (is_member(*lhs, pointer_compare)
            && is_null_spelling(*rhs, pointer_compare))
            || (is_member(*rhs, pointer_compare) && is_null_spelling(*lhs, pointer_compare));
        tests_member
            && view
                .dominators
                .edge_dominates(block.id, non_null_successor, deref_block)
    })
}

/// The root of `operand`'s chain and the summed byte offset of `operand`
/// from it, or the reason the chain has no exact offset.
fn trace_root(
    module: &Module,
    view: &FunctionView<'_>,
    operand: ValueId,
) -> Result<(ValueId, u64), NotRederived> {
    let mut value = operand;
    let mut offset: u64 = 0;
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(value) {
            return Err(NotRederived::MalformedFunction);
        }
        match view.def_inst(value) {
            Some(Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty,
                dst_ty,
                operand,
            }) if is_thin_raw_pointer(src_ty) && is_thin_raw_pointer(dst_ty) => value = *operand,
            Some(Inst::Copy { operand, .. } | Inst::BoxDeref { operand, .. }) => value = *operand,
            Some(Inst::GEP {
                pointee_ty,
                base,
                indices,
                ..
            }) => {
                let (element, _) =
                    byte_layout(module, pointee_ty).ok_or(NotRederived::OffsetNotConstant)?;
                let mut sum: u64 = 0;
                for index in indices {
                    let index = small_nonnegative_const(view, *index)
                        .ok_or(NotRederived::OffsetNotConstant)?;
                    sum = sum
                        .checked_add(index)
                        .ok_or(NotRederived::OffsetNotConstant)?;
                }
                let step = sum
                    .checked_mul(element)
                    .ok_or(NotRederived::OffsetNotConstant)?;
                offset = offset
                    .checked_add(step)
                    .ok_or(NotRederived::OffsetNotConstant)?;
                value = *base;
            }
            _ => return Ok((value, offset)),
        }
    }
}

/// Every value derived from `root` by `PtrToPtr`, `Copy`, `GEP` (as base) or
/// `BoxDeref`, and `root` itself. Memoized per root.
fn derived_set(view: &FunctionView<'_>, root: ValueId) -> Rc<HashSet<ValueId>> {
    if let Some(done) = view.derived_memo.borrow().get(&root) {
        return Rc::clone(done);
    }
    let derived = Rc::new(compute_derived_set(view, root));
    view.derived_memo
        .borrow_mut()
        .insert(root, Rc::clone(&derived));
    derived
}

fn compute_derived_set(view: &FunctionView<'_>, root: ValueId) -> HashSet<ValueId> {
    let mut derived = HashSet::from([root]);
    loop {
        let mut grew = false;
        for block in &view.func.blocks {
            for node in &block.body {
                let source = match &node.inst {
                    Inst::Cast {
                        op: CastOp::PtrToPtr,
                        operand,
                        ..
                    }
                    | Inst::Copy { operand, .. }
                    | Inst::BoxDeref { operand, .. } => *operand,
                    Inst::GEP { base, .. } => *base,
                    _ => continue,
                };
                if derived.contains(&source) {
                    for result in &node.results {
                        grew |= derived.insert(*result);
                    }
                }
            }
        }
        if !grew {
            return derived;
        }
    }
}

/// What one instruction does with the derived set: nothing, a use that
/// keeps the allocation private, an escape, or a free.
#[derive(Debug, PartialEq, Eq)]
enum DerivedUse {
    None,
    Private,
    Escape,
    Free,
}

/// Whether every use of `value` anywhere in the function is an `ICmp`: an
/// address turned into an integer that only ever decides a comparison
/// cannot be turned back into a pointer or handed to anyone. Memoized.
fn only_compared(view: &FunctionView<'_>, value: ValueId) -> bool {
    if let Some(&done) = view.compared_memo.borrow().get(&value) {
        return done;
    }
    let compared = compute_only_compared(view, value);
    view.compared_memo.borrow_mut().insert(value, compared);
    compared
}

fn compute_only_compared(view: &FunctionView<'_>, value: ValueId) -> bool {
    view.func
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .all(|node| !node.inst.uses_value(value) || matches!(node.inst, Inst::ICmp { .. }))
}

fn derived_use(
    view: &FunctionView<'_>,
    node: &trust_ir::InstrNode,
    derived: &HashSet<ValueId>,
) -> DerivedUse {
    let inst = &node.inst;
    let mut uses = false;
    inst.visit_value_operands(|value| uses |= derived.contains(&value));
    if !uses {
        return DerivedUse::None;
    }
    let only_at = |position: ValueId, rest: &[ValueId]| -> bool {
        derived.contains(&position) && rest.iter().all(|value| !derived.contains(value))
    };
    let private = match inst {
        Inst::Load { .. } => true,
        Inst::Store { ptr, value, .. } => only_at(*ptr, &[*value]),
        Inst::GEP { base, indices, .. } => only_at(*base, indices),
        Inst::Cast {
            op: CastOp::PtrToPtr,
            ..
        }
        | Inst::Copy { .. }
        | Inst::BoxDeref { .. } => true,
        Inst::ICmp { ty, .. } => is_thin_raw_pointer(ty),
        // The bridge's allocation guard spells its null test this way.
        Inst::Cast {
            op: CastOp::PtrToInt,
            ..
        } => node
            .results
            .iter()
            .all(|result| only_compared(view, *result)),
        Inst::Dealloc { .. } => return DerivedUse::Free,
        _ => false,
    };
    if private {
        DerivedUse::Private
    } else {
        DerivedUse::Escape
    }
}

/// THE re-derivation of the `BoxDeref` at `func`'s block `block`, index
/// `inst_index`. Anything that is not a sized `BoxDeref` there is refused
/// for every conjunct. One-off: an entry that judges several derefs of one
/// function uses a [`FunctionRederiver`] (or a [`ModuleRederiver`]), which
/// returns the same verdicts.
#[must_use]
pub fn rederive_box_deref(
    module: &Module,
    func: &Function,
    block: BlockId,
    inst_index: usize,
) -> Rederivation {
    FunctionRederiver::new(module, func).rederive(block, inst_index)
}

/// The re-derivations of one function's derefs: the function's view is built
/// once (or the budget refusal decided once), and each position's verdict is
/// computed at most once.
pub struct FunctionRederiver<'m> {
    module: &'m Module,
    view: Result<FunctionView<'m>, NotRederived>,
    memo: HashMap<(BlockId, usize), Rederivation>,
}

impl<'m> FunctionRederiver<'m> {
    /// The re-deriver of `func`, a function of `module`.
    #[must_use]
    pub fn new(module: &'m Module, func: &'m Function) -> Self {
        let view = within_budget(func)
            .and_then(|()| FunctionView::new(func).ok_or(NotRederived::MalformedFunction));
        Self {
            module,
            view,
            memo: HashMap::new(),
        }
    }

    /// The verdict on the `BoxDeref` at `block`, index `inst_index`.
    pub fn rederive(&mut self, block: BlockId, inst_index: usize) -> Rederivation {
        if let Some(done) = self.memo.get(&(block, inst_index)) {
            return done.clone();
        }
        let verdict = match &self.view {
            Ok(view) => rederive_in(self.module, view, block, inst_index),
            Err(why) => Rederivation::refused(RederivedRoot::Opaque, *why),
        };
        self.memo.insert((block, inst_index), verdict.clone());
        verdict
    }
}

/// The re-derivations of a module's derefs, one [`FunctionRederiver`] per
/// function, built on first use. An entry that classifies several findings
/// holds one of these, so no function is analysed twice by it.
pub struct ModuleRederiver<'m> {
    module: &'m Module,
    functions: HashMap<usize, FunctionRederiver<'m>>,
}

impl<'m> ModuleRederiver<'m> {
    #[must_use]
    pub fn new(module: &'m Module) -> Self {
        Self {
            module,
            functions: HashMap::new(),
        }
    }

    /// The module the verdicts are about.
    #[must_use]
    pub fn module(&self) -> &'m Module {
        self.module
    }

    /// The verdict on the `BoxDeref` of `module.functions[function]` at
    /// `block`, index `inst_index`; `None` when there is no such function.
    pub fn rederive(
        &mut self,
        function: usize,
        block: BlockId,
        inst_index: usize,
    ) -> Option<Rederivation> {
        let module = self.module;
        let func = module.functions.get(function)?;
        Some(
            self.functions
                .entry(function)
                .or_insert_with(|| FunctionRederiver::new(module, func))
                .rederive(block, inst_index),
        )
    }
}

fn rederive_in(
    module: &Module,
    view: &FunctionView<'_>,
    block: BlockId,
    inst_index: usize,
) -> Rederivation {
    let func = view.func;
    let opaque = |why| Rederivation::refused(RederivedRoot::Opaque, why);
    let Some(&deref_pos) = view.position.get(&block) else {
        return opaque(NotRederived::MalformedFunction);
    };
    let Some(Inst::BoxDeref {
        pointee, operand, ..
    }) = func.blocks[deref_pos]
        .body
        .get(inst_index)
        .map(|node| &node.inst)
    else {
        return opaque(NotRederived::MalformedFunction);
    };
    if view.has_coroutine {
        return opaque(NotRederived::Coroutine);
    }
    let Some((size, align)) = byte_layout(module, pointee.ty()).filter(|(size, _)| *size > 0)
    else {
        return opaque(NotRederived::PointeeLayout);
    };

    let class = address_class(view, *operand);
    let null_tested = null_test_dominates(view, &class, block);

    let (root, offset) = match trace_root(module, view, *operand) {
        Ok(traced) => traced,
        Err(why) => {
            // An inexact chain: only the value's own null test is evidence.
            let mut rederivation = opaque(why);
            if null_tested {
                rederivation.conjuncts[0].1 = Ok(());
            }
            return rederivation;
        }
    };

    let allocation = match view.def_inst(root) {
        Some(Inst::Alloca { ty, count, align }) => {
            Some((RederivedRoot::StackSlot, ty, count, *align, None))
        }
        Some(Inst::HeapAlloc {
            ty,
            count,
            align,
            origin,
        }) => Some((
            RederivedRoot::HeapAllocation,
            ty,
            count,
            *align,
            Some(*origin),
        )),
        _ => None,
    };
    let Some((root_kind, element_ty, count, alloc_align, origin)) = allocation else {
        let mut rederivation = opaque(NotRederived::OperandNotRooted);
        if null_tested {
            rederivation.conjuncts[0].1 = Ok(());
        } else {
            rederivation.conjuncts[0].1 = Err(NotRederived::NoDominatingNullTest);
        }
        return rederivation;
    };
    let refused = |why| Rederivation::refused(root_kind, why);
    if origin.is_some_and(|origin| origin != AllocOrigin::RustHeap) {
        return refused(NotRederived::AllocationOrigin);
    }
    let Some((element_size, element_align)) = byte_layout(module, element_ty) else {
        return refused(NotRederived::AllocationLayout);
    };
    let count = match count {
        None => 1,
        Some(count) => match small_nonnegative_const(view, *count) {
            Some(count) if count > 0 => count,
            _ => return refused(NotRederived::AllocationLayout),
        },
    };
    let Some(alloc_size) = element_size.checked_mul(count) else {
        return refused(NotRederived::AllocationLayout);
    };
    let alloc_align = match alloc_align {
        Some(explicit) if explicit.is_power_of_two() => explicit,
        Some(_) => return refused(NotRederived::AllocationLayout),
        None => element_align,
    };

    // Dominance of the root over the deref (SSA implies it; it is checked).
    let (root_pos, Some(root_index)) = view.defs[&root] else {
        return refused(NotRederived::OperandNotRooted);
    };
    let root_block = func.blocks[root_pos].id;
    if !view.dominators.dominates(root_block, block)
        || (root_pos == deref_pos && root_index >= inst_index)
    {
        return refused(NotRederived::RootNotDominating);
    }

    let in_bounds = offset
        .checked_add(size)
        .is_some_and(|end| end <= alloc_size);

    // A heap allocation is evidence only once its success is tested: the
    // test must be of the ROOT's own address class.
    let success = match root_kind {
        RederivedRoot::HeapAllocation => {
            if null_test_dominates(view, &address_class(view, root), block) {
                Ok(())
            } else {
                Err(NotRederived::AllocationSuccessUntested)
            }
        }
        _ => Ok(()),
    };

    let non_null = success.and(if in_bounds {
        Ok(())
    } else {
        Err(NotRederived::OutOfBounds)
    });
    let aligned = success.and(if alloc_align % align != 0 {
        Err(NotRederived::AllocationUnderAligned)
    } else if offset % align != 0 {
        Err(NotRederived::OffsetMisaligned)
    } else {
        Ok(())
    });
    let live = live_between(view, root, root_pos, root_index, deref_pos, inst_index);
    let dereferenceable = success
        .and(if in_bounds {
            Ok(())
        } else {
            Err(NotRederived::OutOfBounds)
        })
        .and(live);

    Rederivation {
        root: root_kind,
        conjuncts: [
            (ValidityConjunct::NonNull, non_null),
            (ValidityConjunct::Aligned, aligned),
            (ValidityConjunct::Dereferenceable, dereferenceable),
        ],
    }
}

/// No instruction between the root and the deref frees a derived value or
/// lets one escape.
fn live_between(
    view: &FunctionView<'_>,
    root: ValueId,
    root_pos: usize,
    root_index: usize,
    deref_pos: usize,
    deref_index: usize,
) -> Result<(), NotRederived> {
    let derived = derived_set(view, root);
    let after_root = view.reach_avoiding(root_pos, root_pos);
    let mut reaches_deref: HashMap<usize, bool> = HashMap::new();
    let mut before_deref_block = |pos: usize| -> bool {
        *reaches_deref
            .entry(pos)
            .or_insert_with(|| view.reach_avoiding(pos, root_pos).contains(&deref_pos))
    };
    for (pos, block) in view.func.blocks.iter().enumerate() {
        let block_after_root = pos != root_pos && after_root.contains(&pos);
        let block_reaches_deref = before_deref_block(pos);
        for (index, node) in block.body.iter().enumerate() {
            let after = (pos == root_pos && index > root_index) || block_after_root;
            let before = (pos == deref_pos && index < deref_index) || block_reaches_deref;
            if !(after && before) {
                continue;
            }
            match derived_use(view, node, &derived) {
                DerivedUse::None | DerivedUse::Private => {}
                DerivedUse::Escape => return Err(NotRederived::EscapesBeforeDeref),
                DerivedUse::Free => return Err(NotRederived::FreedBeforeDeref),
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    //! One positive control per shape and one near miss per condition. Each
    //! near miss differs from a control in one place and names the reason
    //! that refuses it, so removing a condition fails its test by name.

    use super::{NotRederived, RederivedRoot, rederive_box_deref};
    use trust_ir::box_validity::ValidityConjunct::{Aligned, Dereferenceable, NonNull};
    use trust_ir::box_validity::{BoxDerefSite, BoxFactSession, BoxValidityFact, PremiseRoot};
    use trust_ir::inst::{AllocOrigin, CastOp, ICmpOp};
    use trust_ir::{
        BlockId, Endianness, FuncId, Inst, Module, StructPassingPolicy, TargetInfo, Ty, ValueId,
    };
    use trust_ir_build::{FunctionBuilder, ModuleBuilder};

    fn fact() -> BoxValidityFact {
        BoxValidityFact::premise(
            BoxDerefSite {
                item: [0x3c; 16],
                ordinal: 0,
            },
            BoxFactSession::PROOF_SNAPSHOT,
            PremiseRoot::ParamByValue,
        )
    }

    pub(super) struct Env {
        pub p: ValueId,
        pub q: ValueId,
        pub n: ValueId,
        pub g: FuncId,
        pub h: FuncId,
    }

    fn target(triple: &str, pointer_size: u32) -> TargetInfo {
        TargetInfo {
            triple: triple.to_owned(),
            pointer_size,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: StructPassingPolicy::NativeC,
        }
    }

    /// `f(p: ptr, q: ptr, n: i64) -> i64` in a module that also declares
    /// `g(ptr)` and `h() -> ptr`, with `body` emitted from the entry block.
    pub(super) fn build_on(
        target: TargetInfo,
        body: impl FnOnce(&mut FunctionBuilder<'_>, &Env),
    ) -> Module {
        let mut mb = ModuleBuilder::new_with_target_info("box_deref_rederive", target);
        let g_ty = mb.add_func_type(vec![Ty::Ptr], vec![]);
        let g = mb.declare_function("g", g_ty);
        let h_ty = mb.add_func_type(vec![], vec![Ty::Ptr]);
        let h = mb.declare_function("h", h_ty);
        let ft = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        let p = fb.add_block_param(entry, Ty::Ptr);
        let q = fb.add_block_param(entry, Ty::Ptr);
        let n = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        body(&mut fb, &Env { p, q, n, g, h });
        fb.build();
        mb.build().expect("the fixture builds")
    }

    fn build(body: impl FnOnce(&mut FunctionBuilder<'_>, &Env)) -> Module {
        build_on(target("x86_64-unknown-linux-gnu", 8), body)
    }

    /// The re-derivation of the one `BoxDeref` of `f`.
    fn rederive(module: &Module) -> super::Rederivation {
        let func = module
            .functions
            .iter()
            .find(|func| func.name == "f")
            .expect("f");
        let mut found = None;
        for block in &func.blocks {
            for (index, node) in block.body.iter().enumerate() {
                if matches!(node.inst, Inst::BoxDeref { .. }) {
                    assert!(found.is_none(), "one BoxDeref per fixture");
                    found = Some((block.id, index));
                }
            }
        }
        let (block, index) = found.expect("a BoxDeref");
        rederive_box_deref(module, func, block, index)
    }

    fn assert_complete(module: &Module, root: RederivedRoot) {
        let rederivation = rederive(module);
        assert_eq!(rederivation.root, root, "{rederivation:?}");
        assert!(rederivation.is_complete(), "{rederivation:?}");
    }

    fn assert_verdicts(
        module: &Module,
        non_null: Result<(), NotRederived>,
        aligned: Result<(), NotRederived>,
        dereferenceable: Result<(), NotRederived>,
    ) {
        let rederivation = rederive(module);
        assert_eq!(
            (
                rederivation.verdict(NonNull),
                rederivation.verdict(Aligned),
                rederivation.verdict(Dereferenceable)
            ),
            (non_null, aligned, dereferenceable),
            "{rederivation:?}"
        );
    }

    /// Deref `pointer` as an `I64` box, load through it and return.
    fn deref_and_return(fb: &mut FunctionBuilder<'_>, pointer: ValueId) {
        let boxed = fb.box_deref(Ty::I64, pointer, fact());
        let read = fb.load(Ty::I64, boxed);
        fb.ret(vec![read]);
    }

    /// The bridge's allocation guard: `ptrtoint` of `pointer` compared with
    /// 0, the error edge returning -1; the builder continues on the non-null
    /// edge. `eq` selects `Eq` (non-null on else) or `Ne` (non-null on then).
    fn null_guard(fb: &mut FunctionBuilder<'_>, pointer: ValueId, eq: bool) {
        let bits = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::I64, pointer);
        let zero = fb.iconst(Ty::I64, 0);
        let op = if eq { ICmpOp::Eq } else { ICmpOp::Ne };
        let cond = fb.icmp(op, Ty::I64, bits, zero);
        let failed = fb.create_block();
        let ready = fb.create_block();
        if eq {
            fb.condbr(cond, failed, vec![], ready, vec![]);
        } else {
            fb.condbr(cond, ready, vec![], failed, vec![]);
        }
        fb.switch_to_block(failed);
        let minus_one = fb.iconst(Ty::I64, -1);
        fb.ret(vec![minus_one]);
        fb.switch_to_block(ready);
    }

    fn heap(fb: &mut FunctionBuilder<'_>) -> ValueId {
        fb.heap_alloc(Ty::I64, None, None, AllocOrigin::RustHeap)
    }

    /// Set the `count` of the first `Alloca` of `f` to `count` (the builder
    /// spells no counted stack slot).
    fn with_alloca_count(mut module: Module, count: ValueId) -> Module {
        let func = module
            .functions
            .iter_mut()
            .find(|func| func.name == "f")
            .expect("f");
        let node = func
            .blocks
            .iter_mut()
            .flat_map(|block| &mut block.body)
            .find(|node| matches!(node.inst, Inst::Alloca { .. }))
            .expect("an alloca");
        let Inst::Alloca { count: slot, .. } = &mut node.inst else {
            unreachable!()
        };
        *slot = Some(count);
        module
    }

    // ---- the stack-slot shape -------------------------------------------

    #[test]
    fn a_stack_slot_of_the_pointee_is_rederived_in_every_conjunct() {
        let module = build(|fb, _| {
            let slot = fb.alloca(Ty::I64);
            let seven = fb.iconst(Ty::I64, 7);
            fb.store(Ty::I64, slot, seven);
            deref_and_return(fb, slot);
        });
        assert_complete(&module, RederivedRoot::StackSlot);
    }

    #[test]
    fn address_preserving_copies_and_dominated_blocks_keep_the_root() {
        let module = build(|fb, _| {
            let slot = fb.alloca(Ty::I64);
            let typed = fb.cast(
                CastOp::PtrToPtr,
                Ty::Ptr,
                Ty::PtrMut(Box::new(Ty::I64)),
                slot,
            );
            let next = fb.create_block();
            fb.br(next, vec![]);
            fb.switch_to_block(next);
            let back = fb.cast(
                CastOp::PtrToPtr,
                Ty::PtrMut(Box::new(Ty::I64)),
                Ty::Ptr,
                typed,
            );
            let copied = fb.copy(Ty::Ptr, back);
            deref_and_return(fb, copied);
        });
        assert_complete(&module, RederivedRoot::StackSlot);
    }

    #[test]
    fn an_exact_aligned_offset_inside_a_counted_slot_is_rederived() {
        let mut count = ValueId::new(0);
        let module = build(|fb, _| {
            count = fb.iconst(Ty::I64, 4);
            let slot = fb.alloca(Ty::I64);
            let two = fb.iconst(Ty::I64, 2);
            let element = fb.gep(Ty::I64, slot, vec![two]);
            deref_and_return(fb, element);
        });
        let module = with_alloca_count(module, count);
        assert_complete(&module, RederivedRoot::StackSlot);
    }

    #[test]
    fn an_offset_that_is_not_a_multiple_of_the_alignment_refuses_aligned_only() {
        let mut count = ValueId::new(0);
        let module = build(|fb, _| {
            count = fb.iconst(Ty::I64, 2);
            let slot = fb.alloca(Ty::I64);
            let four = fb.iconst(Ty::I64, 4);
            let unaligned = fb.gep(Ty::U8, slot, vec![four]);
            deref_and_return(fb, unaligned);
        });
        let module = with_alloca_count(module, count);
        assert_verdicts(&module, Ok(()), Err(NotRederived::OffsetMisaligned), Ok(()));
    }

    #[test]
    fn an_access_past_the_slot_refuses_non_null_and_dereferenceable() {
        let module = build(|fb, _| {
            let slot = fb.alloca(Ty::I64);
            let one = fb.iconst(Ty::I64, 1);
            let past = fb.gep(Ty::I64, slot, vec![one]);
            deref_and_return(fb, past);
        });
        assert_verdicts(
            &module,
            Err(NotRederived::OutOfBounds),
            Ok(()),
            Err(NotRederived::OutOfBounds),
        );
    }

    #[test]
    fn a_slot_smaller_than_the_pointee_is_out_of_bounds() {
        let module = build(|fb, _| {
            let slot = fb.alloca_aligned(Ty::U32, 8);
            deref_and_return(fb, slot);
        });
        assert_verdicts(
            &module,
            Err(NotRederived::OutOfBounds),
            Ok(()),
            Err(NotRederived::OutOfBounds),
        );
    }

    #[test]
    fn an_under_aligned_slot_refuses_aligned() {
        let mut count = ValueId::new(0);
        let module = build(|fb, _| {
            count = fb.iconst(Ty::I64, 8);
            let slot = fb.alloca_aligned(Ty::U8, 1);
            deref_and_return(fb, slot);
        });
        let module = with_alloca_count(module, count);
        assert_verdicts(
            &module,
            Ok(()),
            Err(NotRederived::AllocationUnderAligned),
            Ok(()),
        );
    }

    #[test]
    fn a_non_constant_index_has_no_exact_offset() {
        let module = build(|fb, env| {
            let slot = fb.alloca(Ty::I64);
            let element = fb.gep(Ty::I64, slot, vec![env.n]);
            deref_and_return(fb, element);
        });
        assert_verdicts(
            &module,
            Err(NotRederived::OffsetNotConstant),
            Err(NotRederived::OffsetNotConstant),
            Err(NotRederived::OffsetNotConstant),
        );
    }

    #[test]
    fn a_negative_index_has_no_exact_offset() {
        let module = build(|fb, _| {
            let slot = fb.alloca(Ty::I64);
            let minus_one = fb.iconst(Ty::I64, -1);
            let element = fb.gep(Ty::I64, slot, vec![minus_one]);
            deref_and_return(fb, element);
        });
        assert_verdicts(
            &module,
            Err(NotRederived::OffsetNotConstant),
            Err(NotRederived::OffsetNotConstant),
            Err(NotRederived::OffsetNotConstant),
        );
    }

    #[test]
    fn a_non_constant_count_has_no_extent() {
        let mut count = ValueId::new(0);
        let module = build(|fb, env| {
            count = env.n;
            let slot = fb.alloca(Ty::I64);
            deref_and_return(fb, slot);
        });
        let module = with_alloca_count(module, count);
        assert_verdicts(
            &module,
            Err(NotRederived::AllocationLayout),
            Err(NotRederived::AllocationLayout),
            Err(NotRederived::AllocationLayout),
        );
    }

    #[test]
    fn a_zero_count_has_no_extent() {
        let mut count = ValueId::new(0);
        let module = build(|fb, _| {
            count = fb.iconst(Ty::I64, 0);
            let slot = fb.alloca(Ty::I64);
            deref_and_return(fb, slot);
        });
        let module = with_alloca_count(module, count);
        let layout = Err(NotRederived::AllocationLayout);
        assert_verdicts(&module, layout, layout, layout);
    }

    #[test]
    fn a_constant_past_the_sign_bit_of_its_type_is_not_read() {
        // `i8` 100 is read; `i8` 200 is not a value of the type, so it is
        // never taken at face value.
        for (value, expected) in [(100, true), (200, false)] {
            let mut count = ValueId::new(0);
            let module = build(|fb, _| {
                count = fb.iconst(Ty::I8, value);
                let slot = fb.alloca(Ty::I64);
                deref_and_return(fb, slot);
            });
            let module = with_alloca_count(module, count);
            let rederivation = rederive(&module);
            assert_eq!(
                rederivation.is_complete(),
                expected,
                "{value}: {rederivation:?}"
            );
            if !expected {
                assert_eq!(
                    rederivation.verdict(Dereferenceable),
                    Err(NotRederived::AllocationLayout)
                );
            }
        }
    }

    #[test]
    fn a_cast_to_a_reference_type_is_not_followed() {
        let module = build(|fb, _| {
            let slot = fb.alloca(Ty::I64);
            let reference = fb.cast(CastOp::PtrToPtr, Ty::Ptr, Ty::Ref(Box::new(Ty::I64)), slot);
            let back = fb.cast(
                CastOp::PtrToPtr,
                Ty::Ref(Box::new(Ty::I64)),
                Ty::Ptr,
                reference,
            );
            deref_and_return(fb, back);
        });
        assert_verdicts(
            &module,
            Err(NotRederived::NoDominatingNullTest),
            Err(NotRederived::OperandNotRooted),
            Err(NotRederived::OperandNotRooted),
        );
    }

    #[test]
    fn a_root_that_does_not_dominate_the_deref_is_refused() {
        // Ill-formed SSA, built on purpose: the slot is defined on one arm
        // and dereffed at the join.
        let mut slot = ValueId::new(0);
        let module = build(|fb, env| {
            let zero = fb.iconst(Ty::I64, 0);
            let cond = fb.icmp(ICmpOp::Eq, Ty::I64, env.n, zero);
            let left = fb.create_block();
            let right = fb.create_block();
            let join = fb.create_block();
            fb.condbr(cond, left, vec![], right, vec![]);
            fb.switch_to_block(left);
            slot = fb.alloca(Ty::I64);
            fb.br(join, vec![]);
            fb.switch_to_block(right);
            fb.br(join, vec![]);
            fb.switch_to_block(join);
            deref_and_return(fb, slot);
        });
        let refused = Err(NotRederived::RootNotDominating);
        assert_verdicts(&module, refused, refused, refused);
    }

    #[test]
    fn a_coroutine_body_is_refused_in_every_conjunct() {
        let mut module = build(|fb, _| {
            let slot = fb.alloca(Ty::I64);
            deref_and_return(fb, slot);
        });
        let func = module
            .functions
            .iter_mut()
            .find(|func| func.name == "f")
            .expect("f");
        let frame = func.blocks[0].body[0].results[0];
        let mut suspend = trust_ir::Block::new(BlockId::new(90));
        suspend
            .body
            .push(trust_ir::InstrNode::new(Inst::CoroSuspend {
                frame,
                state_slot: 0,
                next_state: 1,
                value: frame,
            }));
        func.blocks.push(suspend);
        let coroutine = Err(NotRederived::Coroutine);
        assert_verdicts(&module, coroutine, coroutine, coroutine);
    }

    // ---- liveness: escapes and frees between the root and the deref ----

    #[test]
    fn an_escape_through_a_call_before_the_deref_refuses_dereferenceable() {
        let module = build(|fb, env| {
            let slot = fb.alloca(Ty::I64);
            fb.call_void(env.g, vec![slot]);
            deref_and_return(fb, slot);
        });
        assert_verdicts(
            &module,
            Ok(()),
            Ok(()),
            Err(NotRederived::EscapesBeforeDeref),
        );
    }

    #[test]
    fn an_escape_of_a_derived_copy_is_an_escape() {
        let module = build(|fb, env| {
            let slot = fb.alloca(Ty::I64);
            let copied = fb.copy(Ty::Ptr, slot);
            fb.call_void(env.g, vec![copied]);
            deref_and_return(fb, slot);
        });
        assert_verdicts(
            &module,
            Ok(()),
            Ok(()),
            Err(NotRederived::EscapesBeforeDeref),
        );
    }

    #[test]
    fn storing_the_pointer_into_memory_before_the_deref_is_an_escape() {
        let module = build(|fb, env| {
            let slot = fb.alloca(Ty::I64);
            fb.store(Ty::Ptr, env.p, slot);
            deref_and_return(fb, slot);
        });
        assert_verdicts(
            &module,
            Ok(()),
            Ok(()),
            Err(NotRederived::EscapesBeforeDeref),
        );
    }

    #[test]
    fn an_address_turned_into_an_integer_that_is_stored_is_an_escape() {
        // `PtrToInt` is private only when its every use is a comparison.
        let module = build(|fb, env| {
            let raw = heap(fb);
            null_guard(fb, raw, true);
            let bits = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::I64, raw);
            fb.store(Ty::I64, env.p, bits);
            deref_and_return(fb, raw);
        });
        assert_verdicts(
            &module,
            Ok(()),
            Ok(()),
            Err(NotRederived::EscapesBeforeDeref),
        );
    }

    #[test]
    fn a_call_that_receives_no_derived_value_is_harmless() {
        let module = build(|fb, env| {
            let slot = fb.alloca(Ty::I64);
            fb.call_void(env.g, vec![env.p]);
            deref_and_return(fb, slot);
        });
        assert_complete(&module, RederivedRoot::StackSlot);
    }

    #[test]
    fn an_escape_after_the_deref_does_not_matter() {
        let module = build(|fb, env| {
            let slot = fb.alloca(Ty::I64);
            let boxed = fb.box_deref(Ty::I64, slot, fact());
            fb.call_void(env.g, vec![slot]);
            let read = fb.load(Ty::I64, boxed);
            fb.ret(vec![read]);
        });
        assert_complete(&module, RederivedRoot::StackSlot);
    }

    #[test]
    fn an_escape_on_one_path_to_the_deref_refuses_dereferenceable() {
        let module = build(|fb, env| {
            let slot = fb.alloca(Ty::I64);
            let zero = fb.iconst(Ty::I64, 0);
            let cond = fb.icmp(ICmpOp::Eq, Ty::I64, env.n, zero);
            let escapes = fb.create_block();
            let quiet = fb.create_block();
            let join = fb.create_block();
            fb.condbr(cond, escapes, vec![], quiet, vec![]);
            fb.switch_to_block(escapes);
            fb.call_void(env.g, vec![slot]);
            fb.br(join, vec![]);
            fb.switch_to_block(quiet);
            fb.br(join, vec![]);
            fb.switch_to_block(join);
            deref_and_return(fb, slot);
        });
        assert_verdicts(
            &module,
            Ok(()),
            Ok(()),
            Err(NotRederived::EscapesBeforeDeref),
        );
    }

    #[test]
    fn a_dealloc_on_one_path_to_the_deref_refuses_dereferenceable() {
        // The `Dealloc` does not dominate the deref, so trust-ir's rule 9
        // (which sees only a dominating one) passes this body.
        let module = build(|fb, env| {
            let raw = heap(fb);
            null_guard(fb, raw, true);
            let zero = fb.iconst(Ty::I64, 0);
            let cond = fb.icmp(ICmpOp::Eq, Ty::I64, env.n, zero);
            let frees = fb.create_block();
            let quiet = fb.create_block();
            let join = fb.create_block();
            fb.condbr(cond, frees, vec![], quiet, vec![]);
            fb.switch_to_block(frees);
            fb.dealloc(raw);
            fb.br(join, vec![]);
            fb.switch_to_block(quiet);
            fb.br(join, vec![]);
            fb.switch_to_block(join);
            deref_and_return(fb, raw);
        });
        assert_verdicts(&module, Ok(()), Ok(()), Err(NotRederived::FreedBeforeDeref));
    }

    #[test]
    fn a_dealloc_after_the_deref_does_not_matter() {
        let module = build(|fb, _| {
            let raw = heap(fb);
            null_guard(fb, raw, true);
            let boxed = fb.box_deref(Ty::I64, raw, fact());
            let read = fb.load(Ty::I64, boxed);
            fb.dealloc(raw);
            fb.ret(vec![read]);
        });
        assert_complete(&module, RederivedRoot::HeapAllocation);
    }

    #[test]
    fn an_escape_reached_again_through_a_loop_before_the_deref_is_an_escape() {
        // entry: slot; br head. head: deref; escape; condbr head|exit. The
        // deref of the second iteration follows the first iteration's escape
        // of the same slot, with no re-execution of the slot between.
        let module = build(|fb, env| {
            let slot = fb.alloca(Ty::I64);
            let head = fb.create_block();
            let exit = fb.create_block();
            fb.br(head, vec![]);
            fb.switch_to_block(head);
            let boxed = fb.box_deref(Ty::I64, slot, fact());
            let read = fb.load(Ty::I64, boxed);
            fb.call_void(env.g, vec![slot]);
            let zero = fb.iconst(Ty::I64, 0);
            let cond = fb.icmp(ICmpOp::Eq, Ty::I64, read, zero);
            fb.condbr(cond, head, vec![], exit, vec![]);
            fb.switch_to_block(exit);
            fb.ret(vec![read]);
        });
        assert_verdicts(
            &module,
            Ok(()),
            Ok(()),
            Err(NotRederived::EscapesBeforeDeref),
        );
    }

    #[test]
    fn a_root_re_executed_by_a_loop_starts_a_fresh_allocation() {
        // head: slot; deref; escape; condbr head|exit. Every path back to
        // the deref re-executes the slot, so the escape is never between.
        let module = build(|fb, env| {
            let head = fb.create_block();
            let exit = fb.create_block();
            fb.br(head, vec![]);
            fb.switch_to_block(head);
            let slot = fb.alloca(Ty::I64);
            let boxed = fb.box_deref(Ty::I64, slot, fact());
            let read = fb.load(Ty::I64, boxed);
            fb.call_void(env.g, vec![slot]);
            let cond = fb.icmp(ICmpOp::Eq, Ty::I64, read, env.n);
            fb.condbr(cond, head, vec![], exit, vec![]);
            fb.switch_to_block(exit);
            fb.ret(vec![read]);
        });
        assert_complete(&module, RederivedRoot::StackSlot);
    }

    #[test]
    fn a_loop_carried_pointer_is_not_rooted() {
        let module = build(|fb, env| {
            let slot = fb.alloca(Ty::I64);
            let head = fb.create_block();
            let exit = fb.create_block();
            let carried = fb.add_block_param(head, Ty::Ptr);
            fb.br(head, vec![slot]);
            fb.switch_to_block(head);
            let boxed = fb.box_deref(Ty::I64, carried, fact());
            let read = fb.load(Ty::I64, boxed);
            let cond = fb.icmp(ICmpOp::Eq, Ty::I64, read, env.n);
            fb.condbr(cond, head, vec![carried], exit, vec![]);
            fb.switch_to_block(exit);
            fb.ret(vec![read]);
        });
        assert_verdicts(
            &module,
            Err(NotRederived::NoDominatingNullTest),
            Err(NotRederived::OperandNotRooted),
            Err(NotRederived::OperandNotRooted),
        );
    }

    // ---- the heap shape ---------------------------------------------------

    #[test]
    fn a_success_tested_rust_heap_allocation_is_rederived_in_every_conjunct() {
        for eq in [true, false] {
            let module = build(|fb, _| {
                let raw = heap(fb);
                null_guard(fb, raw, eq);
                deref_and_return(fb, raw);
            });
            assert_complete(&module, RederivedRoot::HeapAllocation);
        }
    }

    #[test]
    fn a_pointer_compare_with_null_tests_success() {
        let module = build(|fb, _| {
            let raw = heap(fb);
            let null = fb.null_ptr();
            let cond = fb.icmp(ICmpOp::Eq, Ty::Ptr, raw, null);
            let failed = fb.create_block();
            let ready = fb.create_block();
            fb.condbr(cond, failed, vec![], ready, vec![]);
            fb.switch_to_block(failed);
            fb.unreachable();
            fb.switch_to_block(ready);
            deref_and_return(fb, raw);
        });
        assert_complete(&module, RederivedRoot::HeapAllocation);
    }

    #[test]
    fn an_untested_heap_allocation_is_not_evidence() {
        let module = build(|fb, _| {
            let raw = heap(fb);
            deref_and_return(fb, raw);
        });
        let untested = Err(NotRederived::AllocationSuccessUntested);
        assert_verdicts(&module, untested, untested, untested);
    }

    #[test]
    fn a_null_test_of_a_different_allocation_is_not_a_test_of_this_one() {
        let module = build(|fb, _| {
            let raw = heap(fb);
            let other = heap(fb);
            null_guard(fb, other, true);
            deref_and_return(fb, raw);
        });
        let untested = Err(NotRederived::AllocationSuccessUntested);
        assert_verdicts(&module, untested, untested, untested);
    }

    #[test]
    fn a_pointer_compare_of_a_different_allocation_is_not_a_test_of_this_one() {
        let module = build(|fb, _| {
            let raw = heap(fb);
            let other = heap(fb);
            let null = fb.null_ptr();
            let cond = fb.icmp(ICmpOp::Eq, Ty::Ptr, other, null);
            let failed = fb.create_block();
            let ready = fb.create_block();
            fb.condbr(cond, failed, vec![], ready, vec![]);
            fb.switch_to_block(failed);
            fb.unreachable();
            fb.switch_to_block(ready);
            deref_and_return(fb, raw);
        });
        let untested = Err(NotRederived::AllocationSuccessUntested);
        assert_verdicts(&module, untested, untested, untested);
    }

    #[test]
    fn a_null_test_whose_non_null_edge_does_not_dominate_is_not_a_test() {
        // The deref is in a block reached from both edges of the test.
        let module = build(|fb, _| {
            let raw = heap(fb);
            let bits = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::I64, raw);
            let zero = fb.iconst(Ty::I64, 0);
            let cond = fb.icmp(ICmpOp::Eq, Ty::I64, bits, zero);
            let left = fb.create_block();
            let right = fb.create_block();
            let join = fb.create_block();
            fb.condbr(cond, left, vec![], right, vec![]);
            fb.switch_to_block(left);
            fb.br(join, vec![]);
            fb.switch_to_block(right);
            fb.br(join, vec![]);
            fb.switch_to_block(join);
            deref_and_return(fb, raw);
        });
        let untested = Err(NotRederived::AllocationSuccessUntested);
        assert_verdicts(&module, untested, untested, untested);
    }

    #[test]
    fn the_null_edge_of_a_test_is_not_the_non_null_edge() {
        // `Eq` to zero, deref on the THEN (null) edge.
        let module = build(|fb, _| {
            let raw = heap(fb);
            let bits = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::I64, raw);
            let zero = fb.iconst(Ty::I64, 0);
            let cond = fb.icmp(ICmpOp::Eq, Ty::I64, bits, zero);
            let null_edge = fb.create_block();
            let other = fb.create_block();
            fb.condbr(cond, null_edge, vec![], other, vec![]);
            fb.switch_to_block(other);
            let minus_one = fb.iconst(Ty::I64, -1);
            fb.ret(vec![minus_one]);
            fb.switch_to_block(null_edge);
            deref_and_return(fb, raw);
        });
        let untested = Err(NotRederived::AllocationSuccessUntested);
        assert_verdicts(&module, untested, untested, untested);
    }

    #[test]
    fn a_comparison_with_a_non_zero_constant_is_not_a_null_test() {
        let module = build(|fb, _| {
            let raw = heap(fb);
            let bits = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::I64, raw);
            let one = fb.iconst(Ty::I64, 1);
            let cond = fb.icmp(ICmpOp::Eq, Ty::I64, bits, one);
            let failed = fb.create_block();
            let ready = fb.create_block();
            fb.condbr(cond, failed, vec![], ready, vec![]);
            fb.switch_to_block(failed);
            fb.unreachable();
            fb.switch_to_block(ready);
            deref_and_return(fb, raw);
        });
        let untested = Err(NotRederived::AllocationSuccessUntested);
        assert_verdicts(&module, untested, untested, untested);
    }

    #[test]
    fn an_ordered_comparison_is_not_a_null_test() {
        // `p >u 0` with the deref on its then edge, and `p <=u 0` with the
        // deref on its else edge: each is a valid null test in fact, and
        // neither is recognised, on either edge.
        for (op, deref_on_then) in [(ICmpOp::Ugt, true), (ICmpOp::Ule, false)] {
            let module = build(|fb, _| {
                let raw = heap(fb);
                let bits = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::I64, raw);
                let zero = fb.iconst(Ty::I64, 0);
                let cond = fb.icmp(op, Ty::I64, bits, zero);
                let failed = fb.create_block();
                let ready = fb.create_block();
                if deref_on_then {
                    fb.condbr(cond, ready, vec![], failed, vec![]);
                } else {
                    fb.condbr(cond, failed, vec![], ready, vec![]);
                }
                fb.switch_to_block(failed);
                fb.unreachable();
                fb.switch_to_block(ready);
                deref_and_return(fb, raw);
            });
            let untested = Err(NotRederived::AllocationSuccessUntested);
            assert_verdicts(&module, untested, untested, untested);
        }
    }

    #[test]
    fn a_c_malloc_allocation_is_not_a_rust_heap_allocation() {
        let module = build(|fb, _| {
            let raw = fb.heap_alloc(Ty::I64, None, None, AllocOrigin::CMalloc);
            null_guard(fb, raw, true);
            deref_and_return(fb, raw);
        });
        let origin = Err(NotRederived::AllocationOrigin);
        assert_verdicts(&module, origin, origin, origin);
    }

    // ---- values whose allocation the function does not show -------------

    #[test]
    fn a_parameter_is_never_aligned_or_dereferenceable_here() {
        let module = build(|fb, env| deref_and_return(fb, env.p));
        assert_verdicts(
            &module,
            Err(NotRederived::NoDominatingNullTest),
            Err(NotRederived::OperandNotRooted),
            Err(NotRederived::OperandNotRooted),
        );
    }

    #[test]
    fn a_null_tested_parameter_is_non_null_and_nothing_more() {
        let module = build(|fb, env| {
            null_guard(fb, env.p, true);
            deref_and_return(fb, env.p);
        });
        assert_verdicts(
            &module,
            Ok(()),
            Err(NotRederived::OperandNotRooted),
            Err(NotRederived::OperandNotRooted),
        );
    }

    #[test]
    fn a_null_test_of_another_parameter_is_not_a_test_of_this_one() {
        let module = build(|fb, env| {
            null_guard(fb, env.q, true);
            deref_and_return(fb, env.p);
        });
        assert_verdicts(
            &module,
            Err(NotRederived::NoDominatingNullTest),
            Err(NotRederived::OperandNotRooted),
            Err(NotRederived::OperandNotRooted),
        );
    }

    #[test]
    fn a_null_test_of_an_offset_of_the_value_is_not_a_test_of_it() {
        let module = build(|fb, env| {
            let one = fb.iconst(Ty::I64, 1);
            let next = fb.gep(Ty::I64, env.p, vec![one]);
            null_guard(fb, next, true);
            deref_and_return(fb, env.p);
        });
        assert_verdicts(
            &module,
            Err(NotRederived::NoDominatingNullTest),
            Err(NotRederived::OperandNotRooted),
            Err(NotRederived::OperandNotRooted),
        );
    }

    #[test]
    fn a_null_test_of_a_copy_of_the_value_tests_it() {
        let module = build(|fb, env| {
            let copied = fb.copy(Ty::Ptr, env.p);
            null_guard(fb, copied, true);
            let other = fb.cast(
                CastOp::PtrToPtr,
                Ty::Ptr,
                Ty::PtrConst(Box::new(Ty::I64)),
                env.p,
            );
            let back = fb.cast(
                CastOp::PtrToPtr,
                Ty::PtrConst(Box::new(Ty::I64)),
                Ty::Ptr,
                other,
            );
            deref_and_return(fb, back);
        });
        assert_verdicts(
            &module,
            Ok(()),
            Err(NotRederived::OperandNotRooted),
            Err(NotRederived::OperandNotRooted),
        );
    }

    #[test]
    fn a_call_result_is_not_rooted_even_when_null_tested() {
        // The bridge's `Box::new` shape: an allocator CALL and its null
        // guard. Only the guard is in this function; the allocator's
        // alignment and extent are the callee's promise.
        let module = build(|fb, env| {
            let raw = fb.call(env.h, vec![]);
            null_guard(fb, raw, true);
            deref_and_return(fb, raw);
        });
        assert_verdicts(
            &module,
            Ok(()),
            Err(NotRederived::OperandNotRooted),
            Err(NotRederived::OperandNotRooted),
        );
    }

    #[test]
    fn a_pointer_loaded_from_memory_is_not_rooted() {
        let module = build(|fb, env| {
            let loaded = fb.load(Ty::Ptr, env.p);
            deref_and_return(fb, loaded);
        });
        assert_verdicts(
            &module,
            Err(NotRederived::NoDominatingNullTest),
            Err(NotRederived::OperandNotRooted),
            Err(NotRederived::OperandNotRooted),
        );
    }

    // ---- preconditions ----------------------------------------------------

    #[test]
    fn a_pointee_with_no_byte_layout_is_refused_in_every_conjunct() {
        let module = build(|fb, _| {
            let slot = fb.alloca(Ty::I64);
            let boxed = fb.box_deref(Ty::Never, slot, fact());
            let read = fb.load(Ty::I64, boxed);
            fb.ret(vec![read]);
        });
        let layout = Err(NotRederived::PointeeLayout);
        assert_verdicts(&module, layout, layout, layout);
    }

    #[test]
    fn a_pointee_holding_never_is_refused_in_every_conjunct() {
        // `(i64, !)` has no value. (trust-ir's layout already refuses it,
        // so the explicit inhabitedness check is a second, independent
        // refusal of the same type; a mutation removing it survives.)
        let pointee = Ty::Tuple(vec![Ty::I64, Ty::Never]);
        let module = build(|fb, _| {
            let slot = fb.alloca(Ty::I64);
            let boxed = fb.box_deref(pointee.clone(), slot, fact());
            let read = fb.load(Ty::I64, boxed);
            fb.ret(vec![read]);
        });
        let layout = Err(NotRederived::PointeeLayout);
        assert_verdicts(&module, layout, layout, layout);
    }

    #[test]
    fn a_value_defined_twice_is_refused_in_every_conjunct() {
        let mut module = build(|fb, _| {
            let slot = fb.alloca(Ty::I64);
            let other = fb.alloca(Ty::I64);
            let _ = other;
            deref_and_return(fb, slot);
        });
        // Give the second slot the first one's result id.
        let func = module
            .functions
            .iter_mut()
            .find(|func| func.name == "f")
            .expect("f");
        let first = func.blocks[0].body[0].results[0];
        func.blocks[0].body[1].results[0] = first;
        let malformed = Err(NotRederived::MalformedFunction);
        assert_verdicts(&module, malformed, malformed, malformed);
    }

    #[test]
    fn the_same_body_is_judged_the_same_at_every_pointer_width() {
        for (triple, width) in [
            ("x86_64-unknown-linux-gnu", 8),
            ("aarch64-unknown-linux-gnu", 8),
            ("riscv64-unknown-linux-gnu", 8),
            ("wasm32-unknown-unknown", 4),
        ] {
            let complete = build_on(target(triple, width), |fb, _| {
                let raw = heap(fb);
                null_guard(fb, raw, true);
                deref_and_return(fb, raw);
            });
            assert_complete(&complete, RederivedRoot::HeapAllocation);
            let escaping = build_on(target(triple, width), |fb, env| {
                let slot = fb.alloca(Ty::I64);
                fb.call_void(env.g, vec![slot]);
                deref_and_return(fb, slot);
            });
            assert_verdicts(
                &escaping,
                Ok(()),
                Ok(()),
                Err(NotRederived::EscapesBeforeDeref),
            );
        }
    }

    #[test]
    fn anything_but_a_box_deref_at_the_position_is_refused() {
        let module = build(|fb, _| {
            let slot = fb.alloca(Ty::I64);
            deref_and_return(fb, slot);
        });
        let func = &module.functions.iter().find(|f| f.name == "f").expect("f");
        let malformed = rederive_box_deref(&module, func, BlockId::new(0), 0);
        assert!(
            malformed
                .conjuncts
                .iter()
                .all(|(_, v)| *v == Err(NotRederived::MalformedFunction)),
            "{malformed:?}"
        );
        let absent = rederive_box_deref(&module, func, BlockId::new(77), 0);
        assert!(!absent.is_complete());
    }

    // ---- the budget and the memo ----------------------------------------

    fn f_of(module: &Module) -> &trust_ir::Function {
        module.functions.iter().find(|f| f.name == "f").expect("f")
    }

    fn instruction_count(module: &Module) -> usize {
        f_of(module).blocks.iter().map(|b| b.body.len()).sum()
    }

    fn assert_too_large(rederivation: &super::Rederivation) {
        assert!(
            rederivation
                .conjuncts
                .iter()
                .all(|(_, v)| *v == Err(NotRederived::FunctionTooLarge)),
            "{rederivation:?}"
        );
    }

    /// The stack-slot control with `pad` integer constants before the deref.
    fn padded_slot(pad: usize) -> Module {
        build(|fb, _| {
            let slot = fb.alloca(Ty::I64);
            for n in 0..pad {
                let _ = fb.iconst(Ty::I64, n as i128);
            }
            deref_and_return(fb, slot);
        })
    }

    #[test]
    fn a_function_at_the_instruction_budget_is_analysed_and_one_over_is_refused() {
        let base = instruction_count(&padded_slot(0));
        let at = padded_slot(super::REDERIVATION_MAX_INSTRUCTIONS - base);
        assert_eq!(instruction_count(&at), super::REDERIVATION_MAX_INSTRUCTIONS);
        assert_complete(&at, RederivedRoot::StackSlot);
        let over = padded_slot(super::REDERIVATION_MAX_INSTRUCTIONS - base + 1);
        assert_too_large(&rederive(&over));
    }

    /// The stack-slot control reached through a chain of `extra` blocks.
    fn chained_slot(extra: usize) -> Module {
        build(|fb, _| {
            let slot = fb.alloca(Ty::I64);
            for _ in 0..extra {
                let next = fb.create_block();
                fb.br(next, vec![]);
                fb.switch_to_block(next);
            }
            deref_and_return(fb, slot);
        })
    }

    #[test]
    fn a_function_at_the_block_budget_is_analysed_and_one_over_is_refused() {
        let at = chained_slot(super::REDERIVATION_MAX_BLOCKS - 1);
        assert_eq!(f_of(&at).blocks.len(), super::REDERIVATION_MAX_BLOCKS);
        assert_complete(&at, RederivedRoot::StackSlot);
        let over = chained_slot(super::REDERIVATION_MAX_BLOCKS);
        assert_too_large(&rederive(&over));
    }

    /// `derefs` derefs of one stack slot; the verdict on the last.
    fn many_derefs(derefs: usize) -> super::Rederivation {
        let module = build(|fb, _| {
            let slot = fb.alloca(Ty::I64);
            for _ in 1..derefs {
                let _ = fb.box_deref(Ty::I64, slot, fact());
            }
            deref_and_return(fb, slot);
        });
        let func = f_of(&module);
        let block = &func.blocks[0];
        let last = block
            .body
            .iter()
            .rposition(|node| matches!(node.inst, Inst::BoxDeref { .. }))
            .expect("a BoxDeref");
        rederive_box_deref(&module, func, block.id, last)
    }

    #[test]
    fn a_function_at_the_deref_budget_is_analysed_and_one_over_is_refused() {
        let at = many_derefs(super::REDERIVATION_MAX_BOX_DEREFS);
        assert!(at.is_complete(), "{at:?}");
        assert_too_large(&many_derefs(super::REDERIVATION_MAX_BOX_DEREFS + 1));
    }

    #[test]
    fn the_memoized_rederiver_returns_the_one_off_verdicts() {
        // The one-escape near miss, so the memo carries a refusal as well.
        let module = build(|fb, env| {
            let slot = fb.alloca(Ty::I64);
            fb.store(Ty::Ptr, env.q, slot);
            deref_and_return(fb, slot);
        });
        let func = f_of(&module);
        let index = func
            .blocks
            .iter()
            .flat_map(|b| b.body.iter().enumerate().map(move |(i, n)| (b.id, i, n)))
            .find(|(_, _, n)| matches!(n.inst, Inst::BoxDeref { .. }))
            .map(|(b, i, _)| (b, i))
            .expect("a BoxDeref");
        let one_off = rederive_box_deref(&module, func, index.0, index.1);
        assert_eq!(
            one_off.verdict(Dereferenceable),
            Err(NotRederived::EscapesBeforeDeref)
        );
        let mut function = super::FunctionRederiver::new(&module, func);
        assert_eq!(function.rederive(index.0, index.1), one_off);
        assert_eq!(function.rederive(index.0, index.1), one_off);
        // Another position of the same function is judged as itself, never
        // by the memo of the first.
        assert_ne!(index.1, 0);
        let other = function.rederive(index.0, 0);
        assert!(
            other
                .conjuncts
                .iter()
                .all(|(_, v)| *v == Err(NotRederived::MalformedFunction)),
            "{other:?}"
        );
        let position = module
            .functions
            .iter()
            .position(|f| f.name == "f")
            .expect("f");
        let mut whole = super::ModuleRederiver::new(&module);
        assert_eq!(whole.rederive(position, index.0, index.1), Some(one_off));
        assert_eq!(
            whole.rederive(module.functions.len(), index.0, index.1),
            None
        );
    }
}
