// trust-cg-lower/sequence_layout.rs - the one machine image and ABI for
// trust-ir sequences and boxed sets
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! THE one definition of this backend's machine image for `Ty::Sequence` and
//! `Ty::Set(_, SetRepr::Boxed)`, of the ABI that carries such a value, and of
//! the static result-length contract a sequence-returning function publishes.
//! Every lowering path (constants, parameters, results, block parameters,
//! `Copy`/`Select`, the `SeqMap` family) reads its offsets, strides and sizes
//! from here; no other module computes a sequence offset.
//!
//! # What the pinned trust-ir states, and what it leaves to a backend
//!
//! * `Ty::Sequence(T)` is an "ordered variable-length sequence of elements of
//!   type `T`. Lowered to a packed buffer (length-prefixed) when the element
//!   type has known size" (`trust-ir/src/ty.rs`). That is the FORM this image
//!   follows: a length prefix, then the elements packed in order.
//! * trust-ir states no concrete layout: `Module::ty_layout_shape` answers
//!   `UnsupportedTyShape` for `Sequence` and `Set`, and the reference
//!   interpreter's `byte_size` answers "has no byte layout". So a sequence has
//!   no in-memory reference semantics at all: `Load`/`Store`/`Alloca`/
//!   `HeapAlloc`/`GEP`/atomics over one are not executable there, and they are
//!   refused here by name. The header width, the element slots and the
//!   pointer-carrier ABI below are this backend's own definitions.
//! * `trust_ir_build::codegen_lowerability_errors` names `ExtractElement` and
//!   `InsertElement` over a `Ty::Sequence` `UnlowerableForCodegen` ("no
//!   conforming backend can address an element of one"), and the must-refuse
//!   corpus row `sequence_element_op` pins it. That list is a FORMAT boundary
//!   ("cannot be closed by a backend author"), so this image is never used to
//!   address one element from an instruction: both element ops are refused by
//!   name whatever the operand's provenance.
//! * `Ty::Set(T, repr)` is an UNORDERED set; `Constant::Set` keeps "a canonical
//!   order chosen by the constructor" and leaves duplicate suppression to the
//!   frontend. `SetRepr::Boxed` is the "boxed runtime container" hint, so a
//!   boxed set is carried exactly like a sequence whose element order is the
//!   constructor's canonical order; a `Constant::Set` two of whose elements
//!   store the same image ([`CollectionLayout::element_image_bits`]: after
//!   narrowing to the slot width and rounding to its precision, so `Int(-1)`
//!   and `Int(255)` of an `I8` set repeat) is refused rather than choosing
//!   between the set and multiset readings. `SetRepr::Bitset` names a "flat
//!   bitset" over a universe trust-ir does not state, so it is refused. No
//!   trust-ir instruction reads a set element or maps a set, so a set value only
//!   moves (constant, parameter, result, block parameter, `Copy`, `Select`).
//!
//! # The image
//!
//! A sequence (or boxed set) VALUE is a pointer to an immutable buffer:
//!
//! ```text
//!   offset 0            u64 element count `len`
//!   offset data_offset  element 0, element 1, ... element len-1   (stride apart)
//! ```
//!
//! `data_offset = align_up(8, element align)` and `stride = element size`; the
//! buffer is aligned to `max(8, element align)`. Admitted elements are the
//! fixed-width scalars `Bool` (one byte, 0 or 1), `I8`..`I64`, `U8`..`U64`,
//! `F32` and `F64` (IEEE bit patterns, little-endian). Every other element type
//! (F16, I128/U128, pointer-width integers, `Char`, pointers, aggregates,
//! nested collections) is refused by name, as is a collection nested inside any
//! other type.
//!
//! # The ABI (AArch64, C calling convention; the only target and convention
//! it is defined for)
//!
//! * A collection PARAMETER, block parameter or `Copy`/`Select` operand is the
//!   buffer pointer in one general-purpose register (an ordinary pointer
//!   argument). The callee never writes through it.
//! * A function whose single result is a collection takes ONE extra trailing
//!   pointer parameter, after its declared parameters: the caller-provided
//!   result buffer. The callee copies the whole image of its result
//!   (`data_offset + len * stride` bytes) into it and returns that pointer in
//!   `x0`. The caller sizes the buffer from the callee's published
//!   [`ResultLength`]: a static element count, or the element count of one
//!   named sequence parameter. A C caller must allocate the same capacity.
//!   A function whose result length is not one such term is refused, as is a
//!   variadic, multi-result or indirectly called sequence-returning function,
//!   and an `Invoke` of one.
//! * The capacity rests on the callee being the body this module analyzed.
//!   A body another object may replace at link or load time (`Weak` or
//!   `LinkOnce` linkage; a definition preemptible under a shared-object
//!   relocation model; a weak definition dyld may coalesce) publishes no
//!   length ([`ModuleLengthFacts::compute`]), so a call to it is refused by
//!   name, exactly like a call to a declaration.
//! * Run-time witnesses (each a trap). The callee checks, before it copies,
//!   that the image it returns has exactly its published length (for a
//!   `Param` length, the parameter's header as read at the return). The
//!   caller re-reads the header of the returned image after the call and
//!   checks it is the count it sized the buffer for; that check runs after
//!   the callee wrote, so it detects a broken length but cannot undo an
//!   overrun. A fixed slot sized from a SOURCE image's static length (a
//!   `SeqMap` result, a call result sized by a parameter whose length is
//!   static) checks the source's header has that count before anything is
//!   written into the slot. Every header read is checked below 2^56, which
//!   keeps every byte count below 2^64.
//!
//! # Lifetime
//!
//! Buffers are never written after they are filled. A `Constant` image lives in
//! a fixed frame slot (re-executing it rewrites identical bytes). A `SeqMap`
//! result or a call's result buffer lives in a fixed frame slot only when its
//! length is static AND its block lies on no CFG cycle (so it executes at most
//! once per activation); otherwise it is a fresh runtime-sized stack
//! allocation per execution, released when the function returns. A loop that
//! produces a sequence per iteration therefore grows the stack per iteration.
//!
//! A `SeqMap` with an element function gives each element its own cell, as
//! trust-ir's interpreter does (a fresh `alloca` per element that stays
//! allocated for the rest of the frame): the cells are one array of `len`
//! element slots allocated by the same rule as the result image, and element
//! `i` round-trips through slot `i`, so a cell pointer the element function
//! keeps stays distinct and valid until the function returns.

use std::collections::HashMap;

use trust_ir::{BlockId, FuncId, Function, Inst, Module, SetRepr, Ty, ValueId};

use crate::adapter::AdapterError;
use crate::types::Type;

/// Width of the element-count prefix, in bytes (one `u64`).
pub const SEQUENCE_HEADER_BYTES: u32 = 8;

/// Diagnostic prefix every sequence/set refusal carries.
pub const SEQUENCE_DIAGNOSTIC: &str = "[TCG-SEQ]";

/// Which trust-ir collection a value slot carries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CollectionKind {
    /// `Ty::Sequence(_)`.
    Sequence,
    /// `Ty::Set(_, SetRepr::Boxed)`.
    Set,
}

impl CollectionKind {
    /// The spelling used in diagnostics.
    pub const fn spelling(self) -> &'static str {
        match self {
            Self::Sequence => "Ty::Sequence",
            Self::Set => "Ty::Set",
        }
    }
}

/// The machine image of one collection type (see the module docs).
#[derive(Debug, Clone, PartialEq)]
pub struct CollectionLayout {
    /// Sequence or boxed set.
    pub kind: CollectionKind,
    /// The resolved trust-ir element type.
    pub elem: Ty,
    /// The LIR type one element slot is loaded and stored as (`Bool` is an
    /// `I8` holding 0 or 1).
    pub storage: Type,
    /// Distance between consecutive elements, in bytes.
    pub stride: u32,
    /// Byte offset of element 0 from the buffer base.
    pub data_offset: u32,
    /// Alignment of the whole buffer, in bytes.
    pub align: u32,
}

impl CollectionLayout {
    /// Bytes an image of `len` elements occupies, header included.
    pub fn byte_size(&self, len: u64) -> Option<u64> {
        u64::from(self.stride)
            .checked_mul(len)?
            .checked_add(u64::from(self.data_offset))
    }

    /// The header measured in element strides: an image of `len` elements
    /// occupies exactly `(len + header_units) * stride` bytes, because the
    /// stride of every admitted element divides `data_offset`.
    pub fn header_units(&self) -> u32 {
        self.data_offset / self.stride
    }

    /// The bit pattern one element slot stores for `constant` (zero-extended
    /// to 64 bits): an integer narrowed to the slot width in two's complement,
    /// `Bool` as 0 or 1, `F32` rounded to single precision exactly as the
    /// instruction selector materializes it, `F64` as its IEEE bits. `None`
    /// when `constant` is not a constant the slot can hold (the wrong kind,
    /// or an integer outside the element type's literal range); the
    /// materializer refuses those by name.
    ///
    /// Two elements store the same image exactly when these patterns are
    /// equal, which is the identity a set image can observe; `Constant`
    /// equality is only the identity of the literal (`Int(-1)` and
    /// `Int(255)` are distinct literals of one `I8` image).
    pub fn element_image_bits(&self, constant: &trust_ir::Constant) -> Option<u64> {
        use trust_ir::Constant;
        let bits = |width: u32| {
            if width >= 64 {
                u64::MAX
            } else {
                (1u64 << width) - 1
            }
        };
        match (&self.elem, constant) {
            (Ty::Bool, Constant::Bool(flag)) => Some(u64::from(*flag)),
            (Ty::F32, Constant::Float(float)) => Some(u64::from((*float as f32).to_bits())),
            (Ty::F64, Constant::Float(float)) => Some(float.to_bits()),
            (
                Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64,
                Constant::Int(int),
            ) => {
                let width = self.stride * 8;
                let signed = matches!(self.elem, Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64);
                // The literal range `translate_int_const_into` admits: a
                // signed element also takes its unsigned bit pattern.
                let min = if signed { -(1i128 << (width - 1)) } else { 0 };
                let max = (1i128 << width) - 1;
                if *int < min || *int > max {
                    return None;
                }
                Some((*int as u64) & bits(width))
            }
            _ => None,
        }
    }

    /// Whether `ty` is an element this image admits, with its storage type.
    fn element_storage(elem: &Ty) -> Option<Type> {
        match elem {
            Ty::Bool | Ty::I8 | Ty::U8 => Some(Type::I8),
            Ty::I16 | Ty::U16 => Some(Type::I16),
            Ty::I32 | Ty::U32 => Some(Type::I32),
            Ty::I64 | Ty::U64 => Some(Type::I64),
            Ty::F32 => Some(Type::F32),
            Ty::F64 => Some(Type::F64),
            _ => None,
        }
    }
}

/// The collection kind `ty` spells, if any (a `Set` of either repr counts, so
/// a bitset is refused by name rather than treated as an ordinary type).
pub fn collection_kind(ty: &Ty) -> Option<CollectionKind> {
    match ty {
        Ty::Sequence(_) => Some(CollectionKind::Sequence),
        Ty::Set(_, _) => Some(CollectionKind::Set),
        _ => None,
    }
}

/// Whether `ty` is a `Ty::Sequence` or `Ty::Set`.
pub fn is_collection(ty: &Ty) -> bool {
    collection_kind(ty).is_some()
}

/// The image of `ty`, or `None` when `ty` is not a collection. `types` is the
/// module's type table (element `TyId`s index it).
pub fn collection_layout(ty: &Ty, types: &[Ty]) -> Option<Result<CollectionLayout, AdapterError>> {
    let (kind, elem_id) = match ty {
        Ty::Sequence(elem) => (CollectionKind::Sequence, *elem),
        Ty::Set(elem, SetRepr::Boxed) => (CollectionKind::Set, *elem),
        Ty::Set(_, SetRepr::Bitset) => {
            return Some(Err(AdapterError::UnsupportedType(format!(
                "{SEQUENCE_DIAGNOSTIC} {ty:?}: SetRepr::Bitset names a flat bitset over a \
                 universe trust-ir does not state (no bound, no base), so no bit image can be \
                 chosen; only SetRepr::Boxed sets are lowered"
            ))));
        }
        _ => return None,
    };
    Some(resolve_layout(ty, kind, elem_id.as_usize(), types))
}

fn resolve_layout(
    ty: &Ty,
    kind: CollectionKind,
    elem_index: usize,
    types: &[Ty],
) -> Result<CollectionLayout, AdapterError> {
    let elem = types.get(elem_index).cloned().ok_or_else(|| {
        AdapterError::UnsupportedType(format!(
            "{SEQUENCE_DIAGNOSTIC} {ty:?}: element TyId({elem_index}) is not in the module types \
             table ({} entries), so the element size is unknown",
            types.len()
        ))
    })?;
    let storage = CollectionLayout::element_storage(&elem).ok_or_else(|| {
        AdapterError::UnsupportedType(format!(
            "{SEQUENCE_DIAGNOSTIC} {} element type {elem:?} is not admitted: the image carries \
             only Bool, I8..I64, U8..U64, F32 and F64 elements",
            kind.spelling()
        ))
    })?;
    let stride = storage.bytes();
    let elem_align = storage.align();
    let data_offset = SEQUENCE_HEADER_BYTES.next_multiple_of(elem_align);
    Ok(CollectionLayout {
        kind,
        elem,
        storage,
        stride,
        data_offset,
        align: SEQUENCE_HEADER_BYTES.max(elem_align),
    })
}

/// The refusal for a collection reached through another type (a struct or
/// tuple field, an array element, a refinement base, ...): the image is a
/// pointer to a frame-owned buffer, and giving it an in-memory position would
/// let it outlive that buffer.
pub fn nested_collection_refusal(ty: &Ty) -> AdapterError {
    AdapterError::UnsupportedType(format!(
        "{SEQUENCE_DIAGNOSTIC} {ty:?} nested inside another type has no in-memory layout: \
         trust-ir gives a collection no byte layout, and this backend carries one only in a \
         value slot (parameter, result, block parameter)"
    ))
}

/// The static element count of a sequence-returning function's result.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ResultLength {
    /// Always this many elements.
    Static(u64),
    /// As many elements as the sequence argument at this declared parameter
    /// index.
    Param(usize),
}

/// One point of the length lattice: unknown yet, one term, or conflicting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LengthFact {
    /// No value reached yet (the optimistic start of the fixpoint).
    Bottom,
    /// Every value reaching here has this length.
    Known(ResultLength),
    /// Two different terms, or an origin whose length is not stated.
    Top,
}

impl LengthFact {
    fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bottom, x) | (x, Self::Bottom) => x,
            (Self::Known(a), Self::Known(b)) if a == b => Self::Known(a),
            _ => Self::Top,
        }
    }
}

/// The single collection result type of `func`'s signature, if it has one.
pub fn collection_result_ty<'m>(module: &'m Module, func: &Function) -> Option<&'m Ty> {
    let sig = module.func_types.get(func.ty.as_usize())?;
    sig.returns.iter().find(|ty| is_collection(ty))
}

/// Per-module length facts: the result length of every defined function
/// whose result is a collection, as a least fixpoint over the call graph.
#[derive(Debug, Clone, Default)]
pub struct ModuleLengthFacts {
    signatures: HashMap<FuncId, LengthFact>,
}

impl ModuleLengthFacts {
    /// Compute the facts for `module`. `replaceable` names each defined
    /// function whose body another object may replace at link or load time
    /// (the caller passes the backend's replacement predicates for its
    /// access model): such a body grants its callers no length authority, so
    /// it is treated exactly like a declaration and publishes nothing. A
    /// caller that sized its buffer from the body in THIS module would
    /// otherwise overflow it when a replacing definition returns more.
    pub fn compute(module: &Module, replaceable: impl Fn(&Function) -> bool) -> Self {
        let mut ids: HashMap<FuncId, usize> = HashMap::new();
        for func in &module.functions {
            *ids.entry(func.id).or_insert(0) += 1;
        }
        let returning: Vec<&Function> = module
            .functions
            .iter()
            .filter(|func| {
                func.has_body()
                    && ids.get(&func.id) == Some(&1)
                    && !replaceable(func)
                    && collection_result_ty(module, func).is_some()
            })
            .collect();
        let mut facts = Self {
            signatures: returning
                .iter()
                .map(|func| (func.id, LengthFact::Bottom))
                .collect(),
        };
        // Monotone over a flat lattice of height 2: each signature changes at
        // most twice, so this terminates within 2 * |returning| + 1 sweeps.
        loop {
            let mut changed = false;
            for func in &returning {
                let values = function_length_facts(func, &facts);
                let result = result_fact(func, &values);
                if facts.signatures.get(&func.id) != Some(&result) {
                    facts.signatures.insert(func.id, result);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        facts
    }

    /// The published result length of `func` (a defined, uniquely identified,
    /// non-replaceable function whose single result is a collection), or
    /// `None` when it has none: a declaration, a replaceable body, a
    /// conflicting or unstated length, or a result no return ever reaches.
    pub fn result_length(&self, func: FuncId) -> Option<ResultLength> {
        match self.signatures.get(&func) {
            Some(LengthFact::Known(length)) => Some(*length),
            _ => None,
        }
    }

    fn callee_fact(&self, callee: FuncId) -> Option<LengthFact> {
        self.signatures.get(&callee).copied()
    }
}

/// The length facts of one function's collection-typed values.
#[derive(Debug, Clone, Default)]
pub struct FunctionLengthFacts {
    facts: HashMap<ValueId, LengthFact>,
    /// Values whose producer this analysis models (block parameters and the
    /// recognized producers). Any other value has no stated length.
    modelled: std::collections::HashSet<ValueId>,
}

impl FunctionLengthFacts {
    /// The fact for `value`: `Top` for a value whose producer is not modelled
    /// (a `Load`, an indirect call, a declaration's result, ...), so an
    /// unmodelled origin can never be joined away as "not reached yet".
    pub fn get(&self, value: ValueId) -> LengthFact {
        match self.facts.get(&value) {
            Some(fact) => *fact,
            None if self.modelled.contains(&value) => LengthFact::Bottom,
            None => LengthFact::Top,
        }
    }

    /// The element count of `value` when it is one statically known number.
    pub fn static_length(&self, value: ValueId) -> Option<u64> {
        match self.get(value) {
            LengthFact::Known(ResultLength::Static(length)) => Some(length),
            _ => None,
        }
    }

    fn update(&mut self, value: ValueId, fact: LengthFact) -> bool {
        let old = self
            .facts
            .get(&value)
            .copied()
            .unwrap_or(LengthFact::Bottom);
        let new = old.join(fact);
        if new == old {
            return false;
        }
        self.facts.insert(value, new);
        true
    }
}

/// Whether `node` is a producer this analysis models, and the fact it
/// produces from the current `facts`.
fn produced_fact(
    inst: &Inst,
    facts: &FunctionLengthFacts,
    signatures: &ModuleLengthFacts,
) -> Option<LengthFact> {
    match inst {
        Inst::Const { ty, value } if is_collection(ty) => Some(match value {
            trust_ir::Constant::Sequence(elems) | trust_ir::Constant::Set(elems) => {
                LengthFact::Known(ResultLength::Static(elems.len() as u64))
            }
            _ => LengthFact::Top,
        }),
        Inst::Copy { ty, operand } if is_collection(ty) => Some(facts.get(*operand)),
        Inst::Select {
            ty,
            then_val,
            else_val,
            ..
        } if is_collection(ty) => Some(facts.get(*then_val).join(facts.get(*else_val))),
        Inst::SeqMapAddK { seq, .. } | Inst::SeqMapNot { seq, .. } | Inst::SeqMap { seq, .. } => {
            Some(facts.get(*seq))
        }
        Inst::Call { callee, args } => {
            signatures
                .callee_fact(*callee)
                .map(|signature| match signature {
                    LengthFact::Known(ResultLength::Param(index)) => args
                        .get(index)
                        .map_or(LengthFact::Top, |arg| facts.get(*arg)),
                    other => other,
                })
        }
        _ => None,
    }
}

/// The branch edges `inst` carries: `(target, arguments)`.
fn branch_edges(inst: &Inst) -> Vec<(BlockId, &[ValueId])> {
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
            let mut edges = vec![(*default, default_args.as_slice())];
            edges.extend(cases.iter().map(|case| (case.target, case.args.as_slice())));
            edges
        }
        Inst::Invoke {
            normal_dest,
            normal_args,
            ..
        } => vec![(*normal_dest, normal_args.as_slice())],
        _ => Vec::new(),
    }
}

/// The length fact of every collection-typed value `func` defines.
pub fn function_length_facts(
    func: &Function,
    signatures: &ModuleLengthFacts,
) -> FunctionLengthFacts {
    let mut facts = FunctionLengthFacts::default();
    for block in &func.blocks {
        for (param, _) in &block.params {
            facts.modelled.insert(*param);
        }
        for node in &block.body {
            if let [result] = node.results.as_slice()
                && produced_fact(&node.inst, &facts, signatures).is_some()
            {
                facts.modelled.insert(*result);
            }
        }
    }
    if let Some(entry) = func.blocks.iter().find(|block| block.id == func.entry) {
        for (index, (param, ty)) in entry.params.iter().enumerate() {
            if is_collection(ty) {
                facts.update(*param, LengthFact::Known(ResultLength::Param(index)));
            }
        }
    }
    let params_of: HashMap<BlockId, &[(ValueId, Ty)]> = func
        .blocks
        .iter()
        .map(|block| (block.id, block.params.as_slice()))
        .collect();
    loop {
        let mut changed = false;
        for block in &func.blocks {
            for node in &block.body {
                if let [result] = node.results.as_slice()
                    && let Some(fact) = produced_fact(&node.inst, &facts, signatures)
                {
                    changed |= facts.update(*result, fact);
                }
                for (target, args) in branch_edges(&node.inst) {
                    let Some(params) = params_of.get(&target) else {
                        continue;
                    };
                    for ((param, ty), arg) in params.iter().zip(args) {
                        if is_collection(ty) {
                            let fact = facts.get(*arg);
                            changed |= facts.update(*param, fact);
                        }
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    facts
}

/// The result length `func` publishes, from its own value facts: one term
/// on every return path, or `None`.
pub fn published_result_length(
    func: &Function,
    values: &FunctionLengthFacts,
) -> Option<ResultLength> {
    match result_fact(func, values) {
        LengthFact::Known(length) => Some(length),
        LengthFact::Bottom | LengthFact::Top => None,
    }
}

/// Join of the length of every value `func` returns.
fn result_fact(func: &Function, values: &FunctionLengthFacts) -> LengthFact {
    let mut fact = LengthFact::Bottom;
    for block in &func.blocks {
        for node in &block.body {
            if let Inst::Return { values: returned } = &node.inst {
                for value in returned {
                    fact = fact.join(values.get(*value));
                }
            }
        }
    }
    fact
}

/// Blocks of `func` that lie on a CFG cycle (Tarjan's strongly connected
/// components, iterative). An instruction in any other block executes at most
/// once per activation.
pub fn cyclic_blocks(func: &Function) -> std::collections::HashSet<BlockId> {
    let index_of: HashMap<BlockId, usize> = func
        .blocks
        .iter()
        .enumerate()
        .map(|(index, block)| (block.id, index))
        .collect();
    let successors: Vec<Vec<usize>> = func
        .blocks
        .iter()
        .map(|block| {
            let mut out = Vec::new();
            let mut push = |target: &BlockId| {
                if let Some(index) = index_of.get(target) {
                    out.push(*index);
                }
            };
            for node in &block.body {
                match &node.inst {
                    Inst::Br { target, .. } => push(target),
                    Inst::CondBr {
                        then_target,
                        else_target,
                        ..
                    } => {
                        push(then_target);
                        push(else_target);
                    }
                    Inst::Switch { default, cases, .. } => {
                        push(default);
                        for case in cases {
                            push(&case.target);
                        }
                    }
                    Inst::Invoke {
                        normal_dest,
                        unwind_dest,
                        ..
                    } => {
                        push(normal_dest);
                        push(unwind_dest);
                    }
                    _ => {}
                }
            }
            out
        })
        .collect();

    let n = func.blocks.len();
    let mut index = vec![usize::MAX; n];
    let mut lowlink = vec![0usize; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut next_index = 0usize;
    let mut cyclic = std::collections::HashSet::new();
    for root in 0..n {
        if index[root] != usize::MAX {
            continue;
        }
        // (node, next successor position)
        let mut work: Vec<(usize, usize)> = vec![(root, 0)];
        index[root] = next_index;
        lowlink[root] = next_index;
        next_index += 1;
        stack.push(root);
        on_stack[root] = true;
        while let Some(&mut (node, ref mut position)) = work.last_mut() {
            if let Some(&succ) = successors[node].get(*position) {
                *position += 1;
                if index[succ] == usize::MAX {
                    index[succ] = next_index;
                    lowlink[succ] = next_index;
                    next_index += 1;
                    stack.push(succ);
                    on_stack[succ] = true;
                    work.push((succ, 0));
                } else if on_stack[succ] {
                    lowlink[node] = lowlink[node].min(index[succ]);
                }
                continue;
            }
            work.pop();
            if let Some(&(parent, _)) = work.last() {
                lowlink[parent] = lowlink[parent].min(lowlink[node]);
            }
            if lowlink[node] == index[node] {
                let mut component = Vec::new();
                while let Some(member) = stack.pop() {
                    on_stack[member] = false;
                    component.push(member);
                    if member == node {
                        break;
                    }
                }
                let self_loop = successors[node].contains(&node);
                if component.len() > 1 || self_loop {
                    for member in component {
                        cyclic.insert(func.blocks[member].id);
                    }
                }
            }
        }
    }
    cyclic
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{Block, Constant, FuncTy, InstrNode, TyId};

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }

    fn b(n: u32) -> BlockId {
        BlockId::new(n)
    }

    #[test]
    fn scalar_elements_have_packed_images_after_an_eight_byte_header() {
        let types = [
            Ty::Bool,
            Ty::I8,
            Ty::U16,
            Ty::I32,
            Ty::U64,
            Ty::F32,
            Ty::F64,
        ];
        let expected = [
            (Type::I8, 1),
            (Type::I8, 1),
            (Type::I16, 2),
            (Type::I32, 4),
            (Type::I64, 8),
            (Type::F32, 4),
            (Type::F64, 8),
        ];
        for (index, (storage, stride)) in expected.into_iter().enumerate() {
            let layout = collection_layout(&Ty::Sequence(TyId::new(index as u32)), &types)
                .expect("a sequence")
                .expect("admitted element");
            assert_eq!(layout.storage, storage);
            assert_eq!(layout.stride, stride);
            assert_eq!(layout.data_offset, 8);
            assert_eq!(layout.align, 8);
            assert_eq!(layout.byte_size(3), Some(8 + 3 * u64::from(stride)));
            assert_eq!(
                u64::from(layout.header_units() + 3) * u64::from(stride),
                layout.byte_size(3).unwrap()
            );
        }
    }

    #[test]
    fn unadmitted_elements_bitsets_and_dangling_elements_are_refused_by_name() {
        let types = [Ty::I128, Ty::F16, Ty::Ptr, Ty::Sequence(TyId::new(0))];
        for index in 0..types.len() {
            let error = collection_layout(&Ty::Sequence(TyId::new(index as u32)), &types)
                .expect("a sequence")
                .expect_err("not admitted");
            assert!(error.to_string().contains("is not admitted"), "{error}");
        }
        let error = collection_layout(&Ty::Set(TyId::new(0), SetRepr::Bitset), &[Ty::U8])
            .expect("a set")
            .expect_err("bitset");
        assert!(error.to_string().contains("SetRepr::Bitset"), "{error}");
        let error = collection_layout(&Ty::Sequence(TyId::new(7)), &[Ty::U8])
            .expect("a sequence")
            .expect_err("dangling");
        assert!(
            error.to_string().contains("not in the module types"),
            "{error}"
        );
        assert!(collection_layout(&Ty::I64, &[]).is_none());
        let set = collection_layout(&Ty::Set(TyId::new(0), SetRepr::Boxed), &[Ty::I32])
            .expect("a set")
            .expect("boxed set");
        assert_eq!(set.kind, CollectionKind::Set);
        assert_eq!(set.stride, 4);
    }

    fn seq_module() -> (Module, Ty) {
        let mut module = Module::new("lengths");
        let elem = module
            .add_type(Ty::I32)
            .expect("Module::add_type: test fixture");
        let seq = Ty::Sequence(elem);
        let unary = module
            .add_func_type(FuncTy {
                params: vec![Ty::Bool, seq.clone()],
                returns: vec![seq.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        // f(c, s) = if c { seq_map_add_k(s) } else { copy s }  -> Param(1)
        let mut f = Function::new(FuncId::new(0), "f", unary, b(0));
        let mut entry = Block::new(b(0))
            .with_param(v(0), Ty::Bool)
            .with_param(v(1), seq.clone());
        entry.body.push(InstrNode::new(Inst::CondBr {
            cond: v(0),
            then_target: b(1),
            then_args: vec![],
            else_target: b(2),
            else_args: vec![],
        }));
        let mut then_block = Block::new(b(1));
        then_block.body.push(
            InstrNode::new(Inst::SeqMapAddK {
                ty: seq.clone(),
                seq: v(1),
                k: 1,
            })
            .with_result(v(2)),
        );
        then_block.body.push(InstrNode::new(Inst::Br {
            target: b(3),
            args: vec![v(2)],
        }));
        let mut else_block = Block::new(b(2));
        else_block.body.push(
            InstrNode::new(Inst::Copy {
                ty: seq.clone(),
                operand: v(1),
            })
            .with_result(v(3)),
        );
        else_block.body.push(InstrNode::new(Inst::Br {
            target: b(3),
            args: vec![v(3)],
        }));
        let mut join = Block::new(b(3)).with_param(v(4), seq.clone());
        join.body
            .push(InstrNode::new(Inst::Return { values: vec![v(4)] }));
        f.blocks = vec![entry, then_block, else_block, join];
        module
            .try_add_function(f)
            .expect("Module::try_add_function: test fixture");
        (module, seq)
    }

    #[test]
    fn a_result_that_is_always_one_parameter_long_publishes_that_parameter() {
        let (module, _) = seq_module();
        let facts = ModuleLengthFacts::compute(&module, |_| false);
        assert_eq!(
            facts.result_length(FuncId::new(0)),
            Some(ResultLength::Param(1))
        );
        assert!(cyclic_blocks(&module.functions[0]).is_empty());
    }

    #[test]
    fn conflicting_lengths_publish_nothing_and_callers_inherit_arguments() {
        let (mut module, seq) = seq_module();
        // Make the else arm return a two-element constant instead: conflict.
        module.functions[0].blocks[2].body[0] = InstrNode::new(Inst::Const {
            ty: seq.clone(),
            value: Constant::Sequence(vec![Constant::Int(1), Constant::Int(2)]),
        })
        .with_result(v(3));
        let facts = ModuleLengthFacts::compute(&module, |_| false);
        assert_eq!(facts.result_length(FuncId::new(0)), None);

        // g() = f(true, [7, 8, 9]) reaches Static(3) through f's Param(1)
        // once f is consistent again.
        let (mut module, seq) = seq_module();
        let nullary = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![seq.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut g = Function::new(FuncId::new(1), "g", nullary, b(0));
        let mut entry = Block::new(b(0));
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(true),
            })
            .with_result(v(0)),
        );
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: seq.clone(),
                value: Constant::Sequence(vec![
                    Constant::Int(7),
                    Constant::Int(8),
                    Constant::Int(9),
                ]),
            })
            .with_result(v(1)),
        );
        entry.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![v(0), v(1)],
            })
            .with_result(v(2)),
        );
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        g.blocks = vec![entry];
        module
            .try_add_function(g)
            .expect("Module::try_add_function: test fixture");
        let facts = ModuleLengthFacts::compute(&module, |_| false);
        assert_eq!(
            facts.result_length(FuncId::new(1)),
            Some(ResultLength::Static(3))
        );
    }

    #[test]
    fn a_replaceable_body_publishes_nothing_and_its_callers_inherit_nothing() {
        // g() = f(true, [7, 8, 9]) where f's body may be replaced at link
        // time: neither f nor g may publish a length from f's body.
        let (mut module, seq) = seq_module();
        let nullary = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![seq.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut g = Function::new(FuncId::new(1), "g", nullary, b(0));
        let mut entry = Block::new(b(0));
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(true),
            })
            .with_result(v(0)),
        );
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: seq,
                value: Constant::Sequence(vec![Constant::Int(7)]),
            })
            .with_result(v(1)),
        );
        entry.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![v(0), v(1)],
            })
            .with_result(v(2)),
        );
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        g.blocks = vec![entry];
        module
            .try_add_function(g)
            .expect("Module::try_add_function: test fixture");
        let facts = ModuleLengthFacts::compute(&module, |func| func.name == "f");
        assert_eq!(facts.result_length(FuncId::new(0)), None);
        assert_eq!(facts.result_length(FuncId::new(1)), None);
        let facts = ModuleLengthFacts::compute(&module, |_| false);
        assert_eq!(
            facts.result_length(FuncId::new(1)),
            Some(ResultLength::Static(1))
        );
    }

    #[test]
    fn element_image_bits_identify_literals_that_store_one_image() {
        let types = [Ty::I8, Ty::U16, Ty::F32, Ty::F64, Ty::Bool, Ty::I64];
        let layout = |index: u32| {
            collection_layout(&Ty::Set(TyId::new(index), SetRepr::Boxed), &types)
                .expect("a set")
                .expect("admitted element")
        };
        let i8_set = layout(0);
        assert_eq!(i8_set.element_image_bits(&Constant::Int(-1)), Some(0xFF));
        assert_eq!(i8_set.element_image_bits(&Constant::Int(255)), Some(0xFF));
        assert_eq!(i8_set.element_image_bits(&Constant::Int(256)), None);
        assert_eq!(i8_set.element_image_bits(&Constant::Int(-129)), None);
        assert_eq!(i8_set.element_image_bits(&Constant::Float(1.0)), None);
        let u16_set = layout(1);
        assert_eq!(u16_set.element_image_bits(&Constant::Int(-1)), None);
        assert_eq!(
            u16_set.element_image_bits(&Constant::Int(65535)),
            Some(0xFFFF)
        );
        // Two f64 literals that round to one f32.
        let f32_set = layout(2);
        let a = 1.0f64;
        let b = 1.0f64 + f64::EPSILON;
        assert_ne!(a.to_bits(), b.to_bits());
        assert_eq!(
            f32_set.element_image_bits(&Constant::Float(a)),
            f32_set.element_image_bits(&Constant::Float(b))
        );
        // -0.0 and +0.0 are distinct images (trust-ir's bit-exact identity).
        assert_ne!(
            f32_set.element_image_bits(&Constant::Float(0.0)),
            f32_set.element_image_bits(&Constant::Float(-0.0))
        );
        let f64_set = layout(3);
        assert_ne!(
            f64_set.element_image_bits(&Constant::Float(a)),
            f64_set.element_image_bits(&Constant::Float(b))
        );
        let bool_set = layout(4);
        assert_eq!(bool_set.element_image_bits(&Constant::Bool(true)), Some(1));
        assert_eq!(bool_set.element_image_bits(&Constant::Int(1)), None);
        let i64_set = layout(5);
        assert_eq!(
            i64_set.element_image_bits(&Constant::Int(-1)),
            i64_set.element_image_bits(&Constant::Int(i128::from(u64::MAX)))
        );
        assert_eq!(
            i64_set.element_image_bits(&Constant::Int(i128::from(u64::MAX) + 1)),
            None
        );
    }

    #[test]
    fn loop_blocks_are_cyclic_and_straight_line_blocks_are_not() {
        let (mut module, _) = seq_module();
        // Turn the join block into a self-loop.
        module.functions[0].blocks[3].body.insert(
            0,
            InstrNode::new(Inst::Br {
                target: b(3),
                args: vec![v(4)],
            }),
        );
        let cyclic = cyclic_blocks(&module.functions[0]);
        assert!(cyclic.contains(&b(3)));
        assert!(!cyclic.contains(&b(0)));
        assert!(!cyclic.contains(&b(1)));
    }
}
