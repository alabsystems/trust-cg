// trust-cg-irmid/passes/argpromo.rs - argument promotion into clones
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Argument promotion: a caller's frame slot whose address is passed to a
//! callee the inliner leaves (`#[inline(never)]`, too large, several call
//! sites) is passed as the VALUES of the bytes the callee reads, and the
//! bytes it writes come back as extra results, through a specialized clone of
//! the callee. Scalar replacement then dissolves the caller's slot (its
//! only escape was the call) and the clone's private copy of it.
//!
//! A current typed aggregate argument may also be a nonvolatile load from
//! an eligible local slot. Its selected fields are proved initialized at
//! that load and extracted from the captured SSA value at the call. Later
//! writes to its source slot cannot change these arguments. The following
//! lane-load cleanup places scalar reads at the original snapshot.
//!
//! **Which calls.** A plain `call` of a function defined in the module under
//! the rustc bridge's crate-private name (`<symbol>.tcg.crate.<tag>`), strong
//! and hidden, so only this crate names it and the clone's name
//! (`<symbol>.tcg.ap<h>.tcg.crate.<tag>`) is unique to the object that
//! defines the callee; not variadic, naked or feature-stating, no parameter
//! passed by copy, no proof material, an entry block no edge targets, at
//! most [`MAX_CALLEE_INSTS`] instructions, and every parameter the clone
//! keeps of exactly its declared type at the entry (the clone declares the
//! signature's type and keeps the entry's, so a kept thin pointer of another
//! pointer type would copy the callee's module-level `EntryParamsMismatch`).
//! An argument is promoted when it
//! is a typed value loaded from, or an address derived from, a fresh slot
//! of the caller by copies, `ptrtoptr`s and
//! constant `gep`s (and the bridge's integer address chains: `ptrtoint`,
//! `add` of a constant, `inttoptr`), and
//!
//! * the callee's parameter is a pointer used only as the address of plain
//!   loads and stores (and the bridge's read-through `extractfield` and
//!   write-through `insertfield`) at constant offsets, of scalar types
//!   (integers, floats, `bool`, `char`, thin pointers), each at an offset
//!   its alignment divides, through copies, `ptrtoptr`s, constant `gep`s and
//!   integer address chains whose integers feed nothing else: no call,
//!   return, block argument, comparison, observed integer view or store of
//!   it. The fields it reads are copied in, the fields it writes copied
//!   out. Or the parameter is an aggregate (a struct, tuple or array the
//!   bridge passes by address) whose every use reads a constant scalar lane
//!   by `extractfield` or typed `extractelement`: the lanes it reads are
//!   copied in;
//! * the slot's address goes nowhere but such accesses and parameters of
//!   calls with that use, of functions no other definition can replace at
//!   link time (so nothing else can reach it during the call), and
//!   no other argument of the call is derived from it; every field lies
//!   inside the slot;
//! * every byte copied in is, on every path to the call, last written by a
//!   store of a value that is never poison (a poison argument is undefined
//!   behaviour at a call), an integer or float for an integer or float field,
//!   an exact store of the field's type otherwise — an aggregate's lanes
//!   included (the lane reads an aggregate passed by address lazily, and an
//!   array of `MaybeUninit` lanes reaches trust-ir as an array of its
//!   payload type, so no lane is known initialized at the call);
//! * in the clone, every byte copied out is, on every path to each `ret`,
//!   last written the same way (the prologue's stores of the copied-in
//!   values included): a poison result is undefined behaviour at a `ret`.
//!
//! **The clone** takes the copied-in values in place of the pointer,
//! allocates its own copy of the bytes (`alloca u8, extent`, aligned to the
//! largest alignment an access requires), stores the values into it, runs the
//! callee's body over it, and returns its written fields after the callee's
//! own results; an aggregate's lane reads become copies of its new
//! parameters. The caller loads the copied-in fields before the call and
//! stores the copied-out results after it (`align 1`, so no access is
//! misaligned). `trust_cg_verify::trust_ir_mid_tv` (`trust_ir_mid_tv_argpromo.rs`)
//! re-derives every condition, the clone and the rewrite from the source.
//!
//! **Policy** (not checked): only a slot whose every escape is such a call is
//! a candidate (otherwise it stays in memory anyway); at most
//! [`MAX_FIELDS`] fields per parameter and [`MAX_CLONE_PARAMS`] parameters,
//! a parameter extent of at most [`MAX_EXTENT`] bytes, at most
//! [`MAX_RESULT_WORDS`] wasm results (a 128-bit integer counts two: the
//! wasm32 lane's internal multi-value ABI returns at most four, more would
//! come back through memory; a session that withholds the `multivalue`
//! feature gets no internal ABI, and the clone's extra results come back
//! through its C form's `sret` buffer in memory), one result for a callee of the Rust calling
//! convention (the lane's own convention returns more through `sret`, which
//! it refuses for an externally visible definition), no copied-out field
//! beside an aggregate result of the callee, and at most
//! [`MAX_CLONES`] clones per module.
//! The pass visits callees first, so a clone copies a callee whose own calls
//! were promoted already. The original callee stays for every other caller;
//! the linker drops it when nothing references it.

use std::collections::{BTreeSet, HashMap, HashSet};

use trust_cg_verify::trust_ir_mid_tv::{
    ARGPROMO_CLONE_MARK, ArgPromoField, ArgPromoParam, ArgPromoSite, ArgPromoWitness, PassWitness,
    argpromo_clone_name,
};
use trust_ir::{
    CastOp, Constant, FuncId, FuncTy, FuncTyId, Function, Inst, InstrNode, Linkage, Module,
    ParamAttrs, PassMode, Ty, ValueId, Visibility,
};

use super::{MidPass, PassContext, alloca_count, record_lane, sole_defs};

#[cfg(test)]
#[path = "argpromo_signature_abi_tests.rs"]
mod signature_abi_tests;

/// The largest callee cloned.
pub(crate) const MAX_CALLEE_INSTS: usize = 400;
/// The most fields copied in (and, separately, out) per parameter.
pub(crate) const MAX_FIELDS: usize = 8;
/// The most parameters a clone takes.
pub(crate) const MAX_CLONE_PARAMS: usize = 16;
/// The most bytes of a promoted parameter's extent.
pub(crate) const MAX_EXTENT: u64 = 64;
/// The most wasm results a clone returns.
pub(crate) const MAX_RESULT_WORDS: usize = 4;
/// The most clones in one module.
pub(crate) const MAX_CLONES: usize = 16;

/// Argument promotion, with the callees it never clones (the caller's
/// [`crate::MidConfig::no_arg_promotion`]).
pub(crate) struct ArgPromo {
    excluded: BTreeSet<String>,
}

impl ArgPromo {
    pub(crate) fn new(excluded: BTreeSet<String>) -> Self {
        Self { excluded }
    }
}

/// A thin pointer: one address word, no metadata.
fn thin_pointer(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
    )
}

/// Integers and floats: initialized bytes always decode as one.
fn number(ty: &Ty) -> bool {
    ty.is_integer() || matches!(ty, Ty::F32 | Ty::F64)
}

fn scalar_field(ty: &Ty) -> bool {
    number(ty) || matches!(ty, Ty::Bool | Ty::Char) || thin_pointer(ty)
}

fn size_of(module: &Module, ty: &Ty) -> Option<u64> {
    module.ty_layout_shape(ty).ok()?.size_bytes()
}

fn align_of(module: &Module, ty: &Ty) -> Option<u64> {
    let bits = module.ty_layout_shape(ty).ok()?.align_bits?;
    (bits % 8 == 0 && bits > 0).then_some(bits / 8)
}

/// The function's value uses, per value, as `(block, node)` positions.
struct Uses {
    at: HashMap<ValueId, Vec<(usize, usize)>>,
}

impl Uses {
    fn of(func: &Function) -> Self {
        let mut at: HashMap<ValueId, Vec<(usize, usize)>> = HashMap::new();
        for (bi, block) in func.blocks.iter().enumerate() {
            for (ni, node) in block.body.iter().enumerate() {
                node.inst.visit_value_operands(|v| {
                    let list = at.entry(v).or_default();
                    if list.last() != Some(&(bi, ni)) {
                        list.push((bi, ni));
                    }
                });
            }
        }
        Self { at }
    }

    fn of_value(&self, v: ValueId) -> &[(usize, usize)] {
        self.at.get(&v).map_or(&[], Vec::as_slice)
    }

    fn used(&self, v: ValueId) -> bool {
        self.at.contains_key(&v)
    }
}

/// The values derived from an allocation or parameter `root`: each with its
/// byte offset from `root`, and which of them are integers.
struct Family {
    at: HashMap<ValueId, u64>,
    ints: HashSet<ValueId>,
}

impl Family {
    fn contains(&self, v: &ValueId) -> bool {
        self.at.contains_key(v)
    }

    /// The pointers of the family (the integers are only ever turned back
    /// into pointers).
    fn pointers(&self) -> impl Iterator<Item = (ValueId, u64)> + '_ {
        self.at
            .iter()
            .filter(|(v, _)| !self.ints.contains(v))
            .map(|(v, o)| (*v, *o))
    }
}

/// The values derived from `root`: pointers by copies, `ptrtoptr`s and
/// `gep`s by non-negative integer constants, and the bridge's integer
/// address chains (`ptrtoint` to the pointer-width integer, `add` of a
/// non-negative constant below 2^31, copies, `inttoptr` back), with their
/// byte offsets; `None` when an address is derived otherwise (a variable
/// index, an address as an index) or an integer view of it is used for
/// anything but the chain.
fn family(
    module: &Module,
    func: &Function,
    defs: &HashMap<ValueId, &Inst>,
    uses: &Uses,
    root: ValueId,
) -> Option<Family> {
    let constant = |v: ValueId| match defs.get(&v) {
        Some(Inst::Const {
            ty,
            value: Constant::Int(k),
        }) if ty.is_integer() => u64::try_from(*k).ok(),
        _ => None,
    };
    let word = |ty: &Ty| matches!(ty, Ty::I32 | Ty::U32 | Ty::Isize | Ty::Usize);
    let mut out = Family {
        at: HashMap::from([(root, 0u64)]),
        ints: HashSet::new(),
    };
    let mut work = vec![root];
    while let Some(v) = work.pop() {
        let off = out.at[&v];
        let int = out.ints.contains(&v);
        for &(bi, ni) in uses.of_value(v) {
            let node = &func.blocks[bi].body[ni];
            let (next, next_int) = match &node.inst {
                Inst::Copy { operand, .. } if *operand == v => (off, int),
                Inst::Cast {
                    op: CastOp::PtrToPtr,
                    operand,
                    ..
                } if !int && *operand == v => (off, false),
                Inst::Cast {
                    op: CastOp::PtrToInt,
                    operand,
                    dst_ty,
                    ..
                } if !int && *operand == v && word(dst_ty) && module.pointer_bits() == 32 => {
                    (off, true)
                }
                Inst::Cast {
                    op: CastOp::IntToPtr,
                    operand,
                    ..
                } if int && *operand == v => (off, false),
                Inst::BinOp {
                    op: trust_ir::BinOp::Add,
                    lhs,
                    rhs,
                    ..
                } if int && (*lhs == v) != (*rhs == v) => {
                    let k = constant(if *lhs == v { *rhs } else { *lhs })?;
                    let next = off.checked_add(k)?;
                    if next >= 1 << 31 {
                        return None;
                    }
                    (next, true)
                }
                _ if int => return None,
                Inst::GEP {
                    pointee_ty,
                    base,
                    indices,
                    ..
                } if *base == v && !indices.contains(&v) => {
                    let elem = size_of(module, pointee_ty)?;
                    let sum = indices
                        .iter()
                        .try_fold(0u64, |acc, k| acc.checked_add(constant(*k)?))?;
                    (off.checked_add(elem.checked_mul(sum)?)?, false)
                }
                Inst::GEP { .. } => return None,
                _ => continue,
            };
            let [r] = node.results.as_slice() else {
                return None;
            };
            match out.at.get(r) {
                Some(&o) if o != next || out.ints.contains(r) != next_int => return None,
                Some(_) => {}
                None => {
                    out.at.insert(*r, next);
                    if next_int {
                        out.ints.insert(*r);
                    }
                    work.push(*r);
                }
            }
        }
    }
    Some(out)
}

/// What a callee does with one parameter: a pointer it loads and stores
/// through, or an aggregate passed by value (by address in the rustc
/// bridge's spelling) whose lanes it reads.
#[derive(Debug, Clone)]
struct Shape {
    reads: Vec<ArgPromoField>,
    writes: Vec<ArgPromoField>,
    extent: u64,
    align: u64,
    by_value: bool,
}

/// A struct, tuple or array type: an aggregate the rustc bridge passes by
/// address.
fn record(ty: &Ty) -> bool {
    matches!(ty, Ty::Struct(_) | Ty::Tuple(_) | Ty::Array(..))
}

/// Whether every use of `value` reads it as `ty`: scalar replacement's rule
/// (`sroa::reads_as`), or the value written through the rustc bridge's
/// write-through `insertfield` at a lane of type `ty`.
fn read_as_lane(module: &Module, func: &Function, uses: &Uses, value: ValueId, ty: &Ty) -> bool {
    uses.of_value(value).iter().all(|&at| {
        let (bi, ni) = at;
        match &func.blocks[bi].body[ni].inst {
            Inst::InsertField {
                ty: record,
                aggregate,
                field,
                value: v,
            } if *v == value && *aggregate != value => {
                record_lane(module, record, *field).is_some_and(|(_, lane)| lane == *ty)
            }
            _ => super::sroa::reads_as(func, &[at], value, ty),
        }
    })
}

/// A constant scalar lane read of a record value. Legacy declared-record
/// field reads remain supported; typed tuples/structs name their result
/// type, and arrays use a constant `usize` extractelement index.
fn value_lane(
    module: &Module,
    func: &Function,
    p: ValueId,
    pty: &Ty,
    inst: &Inst,
) -> Option<(u32, u64, Ty)> {
    let field = match inst {
        Inst::ExtractField {
            ty,
            aggregate,
            field,
        } if *aggregate == p => {
            let (_, lane) = record_lane(module, pty, *field)?;
            if ty != pty && (matches!(pty, Ty::Array(..)) || *ty != lane) {
                return None;
            }
            *field
        }
        Inst::ExtractElement { ty, array, index }
            if *array == p && matches!(pty, Ty::Array(..)) =>
        {
            let defs = sole_defs(func);
            let Inst::Const {
                ty: Ty::Usize,
                value: Constant::Int(i),
            } = defs.get(index).copied()?
            else {
                return None;
            };
            let field = u32::try_from(*i).ok()?;
            if record_lane(module, pty, field)?.1 != *ty {
                return None;
            }
            field
        }
        _ => return None,
    };
    let (offset, ty) = record_lane(module, pty, field)?;
    Some((field, offset, ty))
}

/// Every use must be a constant scalar lane read of the immutable value.
fn lanes_read(module: &Module, func: &Function, p: ValueId, pty: &Ty) -> Option<Shape> {
    let uses = Uses::of(func);
    let mut reads = Vec::new();
    let mut extent = 1u64;
    for &(bi, ni) in uses.of_value(p) {
        let node = &func.blocks[bi].body[ni];
        let (_, offset, lane_ty) = value_lane(module, func, p, pty, &node.inst)?;
        let [result] = node.results.as_slice() else {
            return None;
        };
        if !scalar_field(&lane_ty) || !read_as_lane(module, func, &uses, *result, &lane_ty) {
            return None;
        }
        extent = extent.max(offset.checked_add(size_of(module, &lane_ty)?)?);
        reads.push(ArgPromoField {
            offset,
            ty: lane_ty,
        });
    }
    canonical(module, &mut reads);
    Some(Shape {
        reads,
        writes: Vec::new(),
        extent,
        align: 1,
        by_value: true,
    })
}

/// A typed aggregate snapshot and its load position. Its selected fields
/// are proved initialized at the load, and are extracted from this SSA
/// value at the call; later writes to the slot cannot change the snapshot.
fn value_snapshot(func: &Function, arg: ValueId, ty: &Ty) -> Option<(ValueId, (usize, usize))> {
    for (bi, block) in func.blocks.iter().enumerate() {
        for (ni, node) in block.body.iter().enumerate() {
            if node.results.as_slice() == [arg] {
                return match &node.inst {
                    Inst::Load {
                        ty: loaded,
                        ptr,
                        volatile: false,
                        ..
                    } if loaded == ty => Some((*ptr, (bi, ni))),
                    _ => None,
                };
            }
        }
    }
    None
}

/// Sort fields by offset, width and type text, without duplicates (the
/// checker's canonical order).
fn canonical(module: &Module, fields: &mut Vec<ArgPromoField>) {
    fields.sort_by_key(|f| {
        (
            f.offset,
            size_of(module, &f.ty).unwrap_or(0),
            f.ty.to_string(),
        )
    });
    fields.dedup();
}

/// The parameter's use in the callee (module documentation), or `None`.
fn shape(module: &Module, func: &Function, index: usize) -> Option<Shape> {
    let entry = func.blocks.iter().find(|b| b.id == func.entry)?;
    let (p, pty) = entry.params.get(index)?;
    if record(pty) {
        return lanes_read(module, func, *p, pty);
    }
    if !thin_pointer(pty) {
        return None;
    }
    let defs = sole_defs(func);
    let uses = Uses::of(func);
    let fam = family(module, func, &defs, &uses, *p)?;
    let (mut reads, mut writes) = (Vec::new(), Vec::new());
    let (mut extent, mut align) = (1u64, 1u64);
    let mut note = |off: u64, ty: &Ty, explicit: Option<u64>, write: bool| -> Option<()> {
        if !scalar_field(ty) {
            return None;
        }
        let size = size_of(module, ty)?;
        let required = explicit.or_else(|| align_of(module, ty))?;
        if required == 0 || !off.is_multiple_of(required) {
            return None;
        }
        extent = extent.max(off.checked_add(size)?);
        align = align.max(required);
        let field = ArgPromoField {
            offset: off,
            ty: ty.clone(),
        };
        if write {
            writes.push(field);
        } else {
            reads.push(field);
        }
        Some(())
    };
    for (v, off) in fam.pointers() {
        for &(bi, ni) in uses.of_value(v) {
            let node = &func.blocks[bi].body[ni];
            match &node.inst {
                Inst::Load {
                    ty,
                    ptr,
                    volatile: false,
                    align,
                } if *ptr == v => note(off, ty, *align, false)?,
                Inst::Store {
                    ty,
                    ptr,
                    value,
                    volatile: false,
                    align,
                } if *ptr == v && !fam.contains(value) => note(off, ty, *align, true)?,
                Inst::ExtractField {
                    ty,
                    aggregate,
                    field,
                } if *aggregate == v => {
                    let (lo, lane_ty) = record_lane(module, ty, *field)?;
                    note(off.checked_add(lo)?, &lane_ty, None, false)?;
                }
                Inst::InsertField {
                    ty,
                    aggregate,
                    field,
                    value,
                } if *aggregate == v
                    && !fam.contains(value)
                    && !node.results.iter().any(|r| uses.used(*r)) =>
                {
                    let (lo, lane_ty) = record_lane(module, ty, *field)?;
                    note(off.checked_add(lo)?, &lane_ty, None, true)?;
                }
                Inst::Copy { .. }
                | Inst::Cast {
                    op: CastOp::PtrToPtr | CastOp::PtrToInt,
                    ..
                }
                | Inst::GEP { .. }
                    if node.results.iter().all(|r| fam.contains(r)) => {}
                _ => return None,
            }
        }
    }
    // Every address derived from the parameter lies inside the bytes the
    // clone allocates (an access ends at or before the extent).
    if fam.pointers().any(|(_, off)| off >= extent) {
        return None;
    }
    canonical(module, &mut reads);
    canonical(module, &mut writes);
    Some(Shape {
        reads,
        writes,
        extent,
        align,
        by_value: false,
    })
}

/// The callee as a clone's template, with its signature, or `None`.
fn template(module: &Module, id: FuncId) -> Option<(&Function, &FuncTy)> {
    let func = module.function_by_id(id)?;
    if func.is_declaration()
        || func.linkage != Linkage::External
        || func.visibility != Visibility::Hidden
        || func.name.contains(ARGPROMO_CLONE_MARK)
        || argpromo_clone_name(&func.name, &[]).is_none()
        || func.attrs.naked
        || !func.attrs.target_features.is_empty()
        || func
            .attrs
            .params
            .iter()
            .any(|p| p.byval || matches!(p.pass, Some(PassMode::Indirect { .. })))
        || !func.proofs.is_empty()
        || func.summary.is_some()
        || func.source_provenance.is_some()
        || func.body_gate.is_some()
        || func
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| !n.proofs.is_empty() || n.proof_context.is_some())
        || func.blocks.iter().map(|b| b.body.len()).sum::<usize>() > MAX_CALLEE_INSTS
    {
        return None;
    }
    if !module.spec_modules.is_empty()
        || module.proof_obligations.iter().any(|o| {
            (o.function.is_none() && o.site.is_none())
                || o.function == Some(id)
                || o.site.as_ref().is_some_and(|s| s.function == id)
        })
    {
        return None;
    }
    let sig = module.func_type(func.ty)?;
    let entry = func.blocks.iter().find(|b| b.id == func.entry)?;
    // Promotion changes carrier slots; it cannot reuse or erase a recorded ABI.
    if sig.abi.is_some()
        || sig.is_vararg
        || entry.params.len() != sig.params.len()
        || entry
            .params
            .iter()
            .zip(&sig.params)
            .any(|((_, t), p)| t != p && !(thin_pointer(t) && thin_pointer(p)))
        || func.blocks.iter().any(|b| {
            b.body.last().is_some_and(|n| {
                n.inst
                    .successor_edges()
                    .iter()
                    .any(|e| e.target == func.entry)
            })
        })
    {
        return None;
    }
    Some((func, sig))
}

/// Whether every parameter of `func` that `promoted` does not name is of
/// exactly its declared type at the entry (the clone declares the
/// signature's type and keeps the entry's).
fn kept_params_declared(func: &Function, sig: &FuncTy, promoted: impl Fn(usize) -> bool) -> bool {
    func.blocks
        .iter()
        .find(|b| b.id == func.entry)
        .is_some_and(|entry| {
            entry
                .params
                .iter()
                .zip(&sig.params)
                .enumerate()
                .all(|(j, ((_, t), p))| t == p || promoted(j))
        })
}

/// The values never the poison image of uninitialized bytes (the checker's
/// rule, derived here independently): arithmetic, comparisons, casts and
/// address results, scalar constants, `null`, global addresses, allocations,
/// a defined callee's results; copies and selects of such; block
/// parameters every normal edge into whose block passes such a value (an
/// entry parameter, which the caller never passes poisoned, included).
/// `clones` are functions with a body the module does not hold yet (this
/// witness's new clones).
fn never_poison(module: &Module, clones: &[Function], func: &Function) -> HashSet<ValueId> {
    let mut set = HashSet::new();
    let mut moves: Vec<(ValueId, Vec<ValueId>)> = Vec::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        match &node.inst {
            Inst::BinOp { .. }
            | Inst::UnOp { .. }
            | Inst::Overflow { .. }
            | Inst::ICmp { .. }
            | Inst::FCmp { .. }
            | Inst::Cast { .. }
            | Inst::NullPtr
            | Inst::GlobalAddr { .. }
            | Inst::Alloca { .. }
            | Inst::GEP { .. } => set.extend(node.results.iter().copied()),
            Inst::Call { callee, .. }
                if module
                    .function_by_id(*callee)
                    .is_some_and(|f| !f.is_declaration())
                    || clones.iter().any(|f| f.id == *callee) =>
            {
                set.extend(node.results.iter().copied());
            }
            Inst::Const { ty, value }
                if (ty.is_integer() || ty.is_float() || matches!(ty, Ty::Bool | Ty::Char))
                    && matches!(
                        value,
                        Constant::Int(_)
                            | Constant::U128(_)
                            | Constant::Float(_)
                            | Constant::Bool(_)
                    ) =>
            {
                set.extend(node.results.iter().copied());
            }
            Inst::Copy { operand, .. } => {
                if let [r] = node.results.as_slice() {
                    moves.push((*r, vec![*operand]));
                }
            }
            Inst::Select {
                then_val, else_val, ..
            } => {
                if let [r] = node.results.as_slice() {
                    moves.push((*r, vec![*then_val, *else_val]));
                }
            }
            _ => {}
        }
    }
    let index: HashMap<_, _> = func
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.id, i))
        .collect();
    let mut incoming: Vec<Vec<Option<Vec<ValueId>>>> = vec![Vec::new(); func.blocks.len()];
    for block in &func.blocks {
        if let Some(last) = block.body.last() {
            for edge in last.inst.successor_edges() {
                if let Some(&ti) = index.get(&edge.target) {
                    incoming[ti].push(
                        (edge.kind == trust_ir::EdgeKind::Normal).then(|| edge.args.to_vec()),
                    );
                }
            }
        }
    }
    let mut params = Vec::new();
    for (bi, block) in func.blocks.iter().enumerate() {
        for (pi, (value, _)) in block.params.iter().enumerate() {
            params.push((*value, bi, pi));
            set.insert(*value);
        }
    }
    set.extend(moves.iter().map(|(r, _)| *r));
    loop {
        let before = set.len();
        for (r, operands) in &moves {
            if set.contains(r) && !operands.iter().all(|o| set.contains(o)) {
                set.remove(r);
            }
        }
        for &(value, bi, pi) in &params {
            if set.contains(&value)
                && !incoming[bi].iter().all(|args| {
                    args.as_ref()
                        .and_then(|a| a.get(pi))
                        .is_some_and(|a| set.contains(a))
                })
            {
                set.remove(&value);
            }
        }
        if set.len() == before {
            return set;
        }
    }
}

/// Whether, on every path from the entry to position `at` (exclusive), byte
/// `byte` of the allocation `root` (whose pointers are `fam`) is last
/// written by a store of a never-poison value admitted for the field
/// `(field_off, field_ty)`.
#[allow(clippy::too_many_arguments)]
fn proved_byte(
    module: &Module,
    func: &Function,
    preds: &[Vec<usize>],
    entry: usize,
    fam: &Family,
    root: ValueId,
    full: &HashSet<ValueId>,
    at: (usize, usize),
    byte: u64,
    field_off: u64,
    field_ty: &Ty,
) -> bool {
    // Some(true): the byte's proved last write; Some(false): unprovable;
    // None: no write of it.
    let written = |off: u64, ty: &Ty, value: ValueId| -> Option<bool> {
        let Some(size) = size_of(module, ty) else {
            return Some(false);
        };
        if byte < off || byte - off >= size {
            return None;
        }
        let typed = if number(field_ty) {
            number(ty)
        } else {
            off == field_off && ty == field_ty
        };
        Some(typed && full.contains(&value))
    };
    let step = |n: &InstrNode| -> Option<bool> {
        if n.results.contains(&root) {
            return Some(false);
        }
        match &n.inst {
            Inst::Store { ty, ptr, value, .. } if fam.contains(ptr) => {
                return written(fam.at[ptr], ty, *value);
            }
            Inst::InsertField {
                ty,
                aggregate,
                field,
                value,
            } if fam.contains(aggregate) => {
                return match record_lane(module, ty, *field) {
                    Some((lo, lane_ty)) => written(fam.at[aggregate] + lo, &lane_ty, *value),
                    None => Some(false),
                };
            }
            // Reads, derivations and the integer address chain write
            // nothing.
            Inst::Load { .. }
            | Inst::ExtractField { .. }
            | Inst::GEP { .. }
            | Inst::Copy { .. }
            | Inst::Cast { .. }
            | Inst::BinOp { .. } => return None,
            _ => {}
        }
        let mut touches = false;
        n.inst.visit_value_operands(|v| touches |= fam.contains(&v));
        touches.then_some(false)
    };
    let mut seen: HashSet<usize> = HashSet::new();
    let mut work: Vec<(usize, usize)> = vec![at];
    while let Some((bi, end)) = work.pop() {
        let mut resolved = false;
        for n in func.blocks[bi].body[..end].iter().rev() {
            match step(n) {
                Some(true) => {
                    resolved = true;
                    break;
                }
                Some(false) => return false,
                None => {}
            }
        }
        if resolved {
            continue;
        }
        if bi == entry {
            return false;
        }
        for &p in &preds[bi] {
            if seen.insert(p) {
                work.push((p, func.blocks[p].body.len()));
            }
        }
    }
    true
}

/// Predecessor positions and the entry position of `func`.
fn cfg(func: &Function) -> Option<(Vec<Vec<usize>>, usize)> {
    let index: HashMap<_, _> = func
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.id, i))
        .collect();
    let mut preds = vec![Vec::new(); func.blocks.len()];
    for (bi, block) in func.blocks.iter().enumerate() {
        if let Some(last) = block.body.last() {
            for edge in last.inst.successor_edges() {
                preds[*index.get(&edge.target)?].push(bi);
            }
        }
    }
    Some((preds, *index.get(&func.entry)?))
}

/// Whether every byte of every field in `fields` (offsets from `base_off`
/// into the allocation) is proved at `at`.
#[allow(clippy::too_many_arguments)]
fn fields_proved(
    module: &Module,
    func: &Function,
    fam: &Family,
    root: ValueId,
    full: &HashSet<ValueId>,
    at: (usize, usize),
    base_off: u64,
    fields: &[ArgPromoField],
) -> bool {
    let Some((preds, entry)) = cfg(func) else {
        return false;
    };
    fields.iter().all(|f| {
        let off = base_off + f.offset;
        size_of(module, &f.ty).is_some_and(|size| {
            (off..off + size).all(|byte| {
                proved_byte(
                    module, func, &preds, entry, fam, root, full, at, byte, off, &f.ty,
                )
            })
        })
    })
}

/// One past the largest value `func` names.
fn first_fresh(func: &Function) -> u32 {
    let mut max: Option<u32> = None;
    let mut see = |v: ValueId| max = Some(max.map_or(v.index(), |m: u32| m.max(v.index())));
    for block in &func.blocks {
        block.params.iter().for_each(|(v, _)| see(*v));
        for node in &block.body {
            node.results.iter().for_each(|r| see(*r));
            node.inst.visit_value_operands(&mut see);
        }
    }
    if let Some(names) = &func.value_names {
        names.iter().for_each(|(v, _)| see(*v));
    }
    max.map_or(0, |m| m + 1)
}

/// Offset address nodes: nothing at offset 0, else a `const i32` and a byte
/// `gep` from `base`.
fn offset_address(
    next: &mut u32,
    base: ValueId,
    off: u64,
    template: &InstrNode,
    out: &mut Vec<InstrNode>,
) -> ValueId {
    if off == 0 {
        return base;
    }
    let c = ValueId::new(*next);
    let g = ValueId::new(*next + 1);
    *next += 2;
    out.push(with(
        template,
        Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(i128::from(off)),
        },
        vec![c],
    ));
    out.push(with(
        template,
        Inst::GEP {
            pointee_ty: Ty::U8,
            base,
            indices: vec![c],
            inbounds: true,
        },
        vec![g],
    ));
    g
}

fn with(template: &InstrNode, inst: Inst, results: Vec<ValueId>) -> InstrNode {
    let mut n = template.clone();
    n.inst = inst;
    n.results = results;
    n.proofs.clear();
    n.proof_context = None;
    n
}

/// The clone of `func` for `plan` and its allocations (one per promoted
/// parameter): the layout `trust_ir_mid_tv_argpromo.rs` documents.
fn make_clone(
    module: &Module,
    func: &Function,
    sig: &FuncTy,
    plan: &[(ArgPromoParam, Shape)],
    id: FuncId,
    name: String,
    ty: FuncTyId,
) -> Option<(Function, Vec<Option<ValueId>>)> {
    let mut clone = func.clone();
    clone.id = id;
    clone.name = name;
    clone.ty = ty;
    clone.retained = false;
    clone.attrs.readonly = false;
    clone.attrs.readnone = false;
    let mut attrs = Vec::new();
    for j in 0..sig.params.len() {
        match plan.iter().find(|(p, _)| p.index == j) {
            Some((p, _)) => attrs.extend(p.reads.iter().map(|_| ParamAttrs::default())),
            None => attrs.push(func.attrs.params.get(j).cloned().unwrap_or_default()),
        }
    }
    if func.attrs.params.is_empty() && attrs.iter().all(|a| *a == ParamAttrs::default()) {
        attrs.clear();
    }
    clone.attrs.params = attrs;
    let blank = InstrNode::new(Inst::Unreachable);
    let mut next = first_fresh(func);
    let ei = clone.blocks.iter().position(|b| b.id == func.entry)?;
    let old = clone.blocks[ei].params.clone();
    let mut params = Vec::new();
    let mut values: Vec<Vec<ValueId>> = Vec::new();
    for (j, (v, t)) in old.iter().enumerate() {
        match plan.iter().find(|(p, _)| p.index == j) {
            Some((p, _)) => {
                let vs: Vec<ValueId> = p
                    .reads
                    .iter()
                    .map(|_| {
                        next += 1;
                        ValueId::new(next - 1)
                    })
                    .collect();
                params.extend(vs.iter().zip(&p.reads).map(|(v, f)| (*v, f.ty.clone())));
                values.push(vs);
            }
            None => params.push((*v, t.clone())),
        }
    }
    clone.blocks[ei].params = params;
    let mut prologue = Vec::new();
    let mut roots = Vec::new();
    // An aggregate parameter's lane reads become copies of its new
    // parameters.
    let mut lanes: HashMap<ValueId, (Ty, Vec<(ArgPromoField, ValueId)>)> = HashMap::new();
    for ((p, s), vs) in plan.iter().zip(&values) {
        let (pv, pty) = old.get(p.index)?.clone();
        if s.by_value {
            let pairs = p.reads.iter().cloned().zip(vs.iter().copied()).collect();
            lanes.insert(pv, (pty, pairs));
            roots.push(None);
            continue;
        }
        let n = ValueId::new(next);
        next += 1;
        prologue.push(with(
            &blank,
            Inst::Const {
                ty: Ty::U32,
                value: Constant::Int(i128::from(s.extent)),
            },
            vec![n],
        ));
        let root = if pty == Ty::Ptr {
            pv
        } else {
            next += 1;
            ValueId::new(next - 1)
        };
        prologue.push(with(
            &blank,
            Inst::Alloca {
                ty: Ty::U8,
                count: Some(n),
                align: Some(s.align),
            },
            vec![root],
        ));
        if root != pv {
            prologue.push(with(
                &blank,
                Inst::Cast {
                    op: CastOp::PtrToPtr,
                    src_ty: Ty::Ptr,
                    dst_ty: pty,
                    operand: root,
                },
                vec![pv],
            ));
        }
        for (f, v) in p.reads.iter().zip(vs) {
            let at = offset_address(&mut next, root, f.offset, &blank, &mut prologue);
            prologue.push(with(
                &blank,
                Inst::Store {
                    ty: f.ty.clone(),
                    ptr: at,
                    value: *v,
                    volatile: false,
                    align: Some(1),
                },
                Vec::new(),
            ));
        }
        roots.push(Some(root));
    }
    for node in clone.blocks.iter_mut().flat_map(|b| &mut b.body) {
        let read = lanes.iter().find_map(|(aggregate, (pty, pairs))| {
            let (_, offset, lane_ty) = value_lane(module, func, *aggregate, pty, &node.inst)?;
            let (_, v) = pairs
                .iter()
                .find(|(f, _)| f.offset == offset && f.ty == lane_ty)?;
            Some((lane_ty, *v))
        });
        if let Some((ty, operand)) = read {
            node.inst = Inst::Copy { ty, operand };
        }
    }
    let body = std::mem::take(&mut clone.blocks[ei].body);
    clone.blocks[ei].body = prologue.into_iter().chain(body).collect();
    for block in &mut clone.blocks {
        let Some(last) = block.body.pop() else {
            continue;
        };
        let Inst::Return { values } = &last.inst else {
            block.body.push(last);
            continue;
        };
        let mut values = values.clone();
        for ((p, _), root) in plan.iter().zip(&roots) {
            let Some(root) = root else {
                continue;
            };
            for f in &p.writes {
                let at = offset_address(&mut next, *root, f.offset, &blank, &mut block.body);
                let l = ValueId::new(next);
                next += 1;
                block.body.push(with(
                    &blank,
                    Inst::Load {
                        ty: f.ty.clone(),
                        ptr: at,
                        volatile: false,
                        align: Some(1),
                    },
                    vec![l],
                ));
                values.push(l);
            }
        }
        let mut ret = last;
        ret.inst = Inst::Return { values };
        block.body.push(ret);
    }
    Some((clone, roots))
}

/// The wasm results a type takes (a 128-bit integer is two).
fn words(ty: &Ty) -> usize {
    if matches!(ty, Ty::I128 | Ty::U128) {
        2
    } else {
        1
    }
}

/// The clone for `callee` under `plan`, checked: an existing one of the
/// module (or one this witness added) when its body is the derivation, else
/// a new one with its signature id. `None` when the copied-out fields are
/// not proved, the name is taken by another body, or the budget is spent.
struct Clones<'w> {
    new_types: &'w mut Vec<FuncTy>,
    new_functions: &'w mut Vec<Function>,
}

impl Clones<'_> {
    fn get(
        &mut self,
        module: &Module,
        callee: &Function,
        sig: &FuncTy,
        plan: &[(ArgPromoParam, Shape)],
    ) -> Option<FuncId> {
        if sig.abi.is_some() {
            return None;
        }
        let params: Vec<ArgPromoParam> = plan.iter().map(|(p, _)| p.clone()).collect();
        let name = argpromo_clone_name(&callee.name, &params)?;
        let mut csig = FuncTy {
            params: Vec::new(),
            returns: sig.returns.clone(),
            abi: None,
            is_vararg: false,
        };
        for (j, t) in sig.params.iter().enumerate() {
            match params.iter().find(|p| p.index == j) {
                Some(p) => csig.params.extend(p.reads.iter().map(|f| f.ty.clone())),
                None => csig.params.push(t.clone()),
            }
        }
        for p in &params {
            csig.returns.extend(p.writes.iter().map(|f| f.ty.clone()));
        }
        // A Rust-convention function's results beyond one come back through
        // `sret` in the wasm32 lane's own convention, which an externally
        // visible definition may not use (the lane refuses it at a link
        // boundary): such a clone returns at most one value.
        // The wasm32 lane returns several values only when each is a
        // scalar (an aggregate result keeps its own return form).
        if csig.params.len() > MAX_CLONE_PARAMS
            || csig.returns.iter().map(words).sum::<usize>() > MAX_RESULT_WORDS
            || (callee.calling_conv == trust_ir::CallingConv::Rust && csig.returns.len() > 1)
            || (csig.returns.len() > sig.returns.len() && !sig.returns.iter().all(scalar_field))
        {
            return None;
        }
        let ty_index = module
            .func_types
            .iter()
            .chain(self.new_types.iter())
            .position(|t| *t == csig)
            .unwrap_or(module.func_types.len() + self.new_types.len());
        let ty = FuncTyId::new(u32::try_from(ty_index).ok()?);
        let existing = module
            .functions
            .iter()
            .chain(self.new_functions.iter())
            .find(|f| f.name == name);
        let id = match existing {
            Some(f) => f.id,
            None => {
                let clones = module
                    .functions
                    .iter()
                    .chain(self.new_functions.iter())
                    .filter(|f| f.name.contains(ARGPROMO_CLONE_MARK))
                    .count();
                if clones >= MAX_CLONES {
                    return None;
                }
                let max = module
                    .functions
                    .iter()
                    .chain(self.new_functions.iter())
                    .map(|f| f.id.index())
                    .max()?;
                FuncId::new(max.checked_add(1)?)
            }
        };
        let (clone, roots) = make_clone(module, callee, sig, plan, id, name, ty)?;
        if let Some(f) = existing {
            return (*f == clone).then_some(id);
        }
        // The copied-out fields must be proved at every `ret` of the clone.
        let full = never_poison(module, self.new_functions, &clone);
        let defs = sole_defs(&clone);
        let uses = Uses::of(&clone);
        let mut promoted: HashSet<ValueId> = HashSet::new();
        for ((p, _), root) in plan.iter().zip(&roots) {
            let Some(root) = root else {
                continue;
            };
            let fam = family(module, &clone, &defs, &uses, *root)?;
            promoted.extend(fam.at.keys().copied());
            for (bi, block) in clone.blocks.iter().enumerate() {
                if !matches!(
                    block.body.last().map(|n| &n.inst),
                    Some(Inst::Return { .. })
                ) {
                    continue;
                }
                let at = (bi, block.body.len() - 1);
                if !fields_proved(module, &clone, &fam, *root, &full, at, 0, &p.writes) {
                    return None;
                }
            }
        }
        // Policy: a clone copies its callee's body, validation findings
        // included, and trust-ir's validator reports the rustc bridge's field
        // access through a pointer; the wasm32 lane emits the mid-end's
        // output only when it adds no finding. So the clone keeps only those
        // through allocations (scalar replacement reads them as the loads and
        // stores they are).
        // The callee's own slots' through-accesses are left to scalar
        // replacement (and to the caller's re-run without this callee when
        // they stay); one through a pointer parameter never goes.
        for node in clone.blocks.iter().flat_map(|b| &b.body) {
            if let (Inst::Alloca { .. }, [slot]) = (&node.inst, node.results.as_slice())
                && let Some(fam) = family(module, &clone, &defs, &uses, *slot)
            {
                promoted.extend(fam.at.keys().copied());
            }
        }
        let types = super::value_types(&clone);
        let through_other = clone
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| match &n.inst {
                Inst::ExtractField { aggregate, .. } | Inst::InsertField { aggregate, .. } => {
                    !promoted.contains(aggregate)
                        && !types.get(aggregate).is_some_and(record)
                        && !matches!(
                            types.get(aggregate),
                            Some(Ty::Enum(_) | Ty::Record(_) | Ty::Closure(_))
                        )
                }
                _ => false,
            });
        if through_other {
            return None;
        }
        if ty_index == module.func_types.len() + self.new_types.len() {
            self.new_types.push(csig);
        }
        self.new_functions.push(clone);
        Some(id)
    }
}

/// A candidate slot of the caller: its pointers with offsets, its root and
/// size, when every escape of its address is an access or a promotable
/// parameter.
struct Slot {
    root: ValueId,
    size: u64,
    fam: Family,
}

fn candidate_slots(module: &Module, clones: &[Function], func: &Function) -> Vec<Slot> {
    let defs = sole_defs(func);
    let uses = Uses::of(func);
    let mut out = Vec::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        let (Inst::Alloca { ty, count, .. }, [root]) = (&node.inst, node.results.as_slice()) else {
            continue;
        };
        let Some(size) = size_of(module, ty)
            .zip(alloca_count(&defs, *count))
            .and_then(|(s, k)| s.checked_mul(k))
            .filter(|&s| s > 0)
        else {
            continue;
        };
        let Some(fam) = family(module, func, &defs, &uses, *root) else {
            continue;
        };
        let mut calls = 0usize;
        let inside = fam.pointers().all(|(_, off)| off < size);
        let contained = fam.pointers().all(|(v, _)| {
            uses.of_value(v).iter().all(|&(bi, ni)| {
                let n = &func.blocks[bi].body[ni];
                match &n.inst {
                    Inst::Load {
                        ptr,
                        volatile: false,
                        ..
                    } => {
                        if *ptr == v && n.results.iter().any(|r| uses.of_value(*r).iter().any(|&(b, i)|
                            matches!(&func.blocks[b].body[i].inst, Inst::Call { args, .. } if args.contains(r)))) {
                            calls += 1;
                        }
                        *ptr == v
                    },
                    Inst::Store {
                        ptr,
                        value,
                        volatile: false,
                        ..
                    } => *ptr == v && !fam.contains(value),
                    Inst::ExtractField { aggregate, .. } => *aggregate == v,
                    Inst::InsertField {
                        aggregate, value, ..
                    } => {
                        *aggregate == v
                            && !fam.contains(value)
                            && !n.results.iter().any(|r| uses.used(*r))
                    }
                    Inst::Copy { .. }
                    | Inst::Cast {
                        op: CastOp::PtrToPtr | CastOp::PtrToInt,
                        ..
                    }
                    | Inst::GEP { .. } => n.results.iter().all(|r| fam.contains(r)),
                    Inst::Call { callee, args } => {
                        calls += 1;
                        module
                            .function_by_id(*callee)
                            .or_else(|| clones.iter().find(|f| f.id == *callee))
                            .filter(|f| {
                                !f.is_declaration()
                                    && matches!(
                                        f.linkage,
                                        Linkage::External | Linkage::Internal | Linkage::Private
                                    )
                            })
                            .is_some_and(|f| {
                                args.iter()
                                    .enumerate()
                                    .all(|(j, a)| !fam.contains(a) || shape(module, f, j).is_some())
                            })
                    }
                    _ => false,
                }
            })
        });
        if inside && contained && calls > 0 {
            out.push(Slot {
                root: *root,
                size,
                fam,
            });
        }
    }
    out
}

/// The pointer type of `v`, from the pass-side typing.
fn type_of(func: &Function, v: ValueId) -> Option<Ty> {
    super::value_types(func).remove(&v)
}

impl MidPass for ArgPromo {
    fn name(&self) -> &'static str {
        "argpromo"
    }

    fn callee_first(&self) -> bool {
        true
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let module = cx.module;
        let mut state = State {
            slots: candidate_slots(module, &[], func),
            full: None,
        };
        if state.slots.is_empty() {
            return None;
        }
        let mut cur = func.clone();
        let mut witness = ArgPromoWitness::default();
        // Each call once, in block order; positions move as sites expand,
        // and the slots and never-poison values are derived again after each
        // rewrite (its stores are later sites' writes).
        let mut bi = 0;
        while bi < cur.blocks.len() {
            let mut ni = 0;
            while ni < cur.blocks[bi].body.len() {
                let rewritten = self.site(module, &mut cur, &mut witness, &mut state, bi, ni);
                if rewritten.is_some() {
                    state = State {
                        slots: candidate_slots(module, &witness.new_functions, &cur),
                        full: None,
                    };
                }
                ni = rewritten.unwrap_or(ni) + 1;
            }
            bi += 1;
        }
        if witness.sites.is_empty() {
            return None;
        }
        Some((cur, PassWitness::ArgPromo(witness)))
    }
}

/// The caller's candidate slots and never-poison values, derived again
/// after each rewrite.
struct State {
    slots: Vec<Slot>,
    full: Option<HashSet<ValueId>>,
}

impl ArgPromo {
    /// Promote the call at `(bi, ni)` of `cur` if it qualifies; the call's
    /// new position.
    fn site(
        &self,
        module: &Module,
        cur: &mut Function,
        witness: &mut ArgPromoWitness,
        state: &mut State,
        bi: usize,
        ni: usize,
    ) -> Option<usize> {
        let call = cur.blocks[bi].body[ni].clone();
        let Inst::Call { callee, args } = &call.inst else {
            return None;
        };
        // A proof annotation or context describes this call of this callee
        // with these arguments; it does not carry over to the clone's call.
        if !call.proofs.is_empty() || call.proof_context.is_some() {
            return None;
        }
        let slots = &state.slots;
        if !args.iter().any(|a| {
            slots.iter().any(|s| s.fam.contains(a)) || type_of(cur, *a).is_some_and(|t| record(&t))
        }) {
            return None;
        }
        let (target, sig) = template(module, *callee)?;
        if call.results.len() != sig.returns.len() || self.excluded.contains(&target.name) {
            return None;
        }
        let full = state
            .full
            .get_or_insert_with(|| never_poison(module, &witness.new_functions, cur));
        let full = &*full;
        let mut plan: Vec<(ArgPromoParam, Shape, ValueId)> = Vec::new();
        for (j, arg) in args.iter().enumerate() {
            let Some(s) = shape(module, target, j) else {
                continue;
            };
            let Some(aty) = type_of(cur, *arg) else {
                continue;
            };
            let (address, at) = if record(&aty) {
                if !s.by_value || sig.params.get(j) != Some(&aty) {
                    continue;
                }
                let Some(snapshot) = value_snapshot(cur, *arg, &aty) else {
                    continue;
                };
                snapshot
            } else {
                if !thin_pointer(&aty) {
                    continue;
                }
                (*arg, (bi, ni))
            };
            let Some(slot) = slots.iter().find(|s| s.fam.contains(&address)) else {
                continue;
            };
            if args
                .iter()
                .enumerate()
                .any(|(k, a)| k != j && slot.fam.contains(a))
            {
                continue;
            }
            let o = slot.fam.at[&address];
            // Every copied-in byte is proved, an aggregate's lanes included:
            // the lane reads an aggregate passed by address lazily, and the
            // bridge lowers `[MaybeUninit<T>; N]` as `[T x N]`, so no lane of
            // any aggregate is known initialized at the call.
            if s.reads.len() > MAX_FIELDS
                || s.writes.len() > MAX_FIELDS
                || s.extent > MAX_EXTENT
                || o.checked_add(s.extent).is_none_or(|end| end > slot.size)
                || !fields_proved(module, cur, &slot.fam, slot.root, full, at, o, &s.reads)
            {
                continue;
            }
            plan.push((
                ArgPromoParam {
                    index: j,
                    reads: s.reads.clone(),
                    writes: s.writes.clone(),
                },
                s,
                *arg,
            ));
        }
        // Drop parameters until the clone's copied-out fields are proved (a
        // parameter whose writes are not is left a pointer).
        let mut clones = Clones {
            new_types: &mut witness.new_func_types,
            new_functions: &mut witness.new_functions,
        };
        let clone = loop {
            if plan.is_empty() {
                return None;
            }
            let pairs: Vec<(ArgPromoParam, Shape)> = plan
                .iter()
                .map(|(p, s, _)| (p.clone(), s.clone()))
                .collect();
            if !kept_params_declared(target, sig, |k| plan.iter().any(|(p, _, _)| p.index == k)) {
                return None;
            }
            if let Some(id) = clones.get(module, target, sig, &pairs) {
                break id;
            }
            // Retry without the parameter with the most written fields (a
            // read-only one never fails the copy-out proof).
            let worst = plan
                .iter()
                .enumerate()
                .max_by_key(|(_, (p, _, _))| p.writes.len())
                .map(|(i, _)| i)?;
            if plan[worst].0.writes.is_empty() {
                return None;
            }
            plan.remove(worst);
        };
        // The rewrite (the checker's order of fresh values).
        let mut next = first_fresh(cur);
        let mut before = Vec::new();
        let mut bases = Vec::new();
        let mut loaded: Vec<Vec<ValueId>> = Vec::new();
        for (p, _, arg) in &plan {
            let aty = type_of(cur, *arg)?;
            if record(&aty) {
                let entry = target.blocks.iter().find(|b| b.id == target.entry)?;
                let param = entry.params.get(p.index)?.0;
                let mut vs = Vec::new();
                for f in &p.reads {
                    let field = target.blocks.iter().flat_map(|b| &b.body).find_map(|n| {
                        let (field, offset, ty) = value_lane(module, target, param, &aty, &n.inst)?;
                        (offset == f.offset && ty == f.ty).then_some(field)
                    })?;
                    let inst = if matches!(aty, Ty::Array(..)) {
                        let index = ValueId::new(next);
                        next += 1;
                        before.push(with(
                            &call,
                            Inst::Const {
                                ty: Ty::Usize,
                                value: Constant::Int(i128::from(field)),
                            },
                            vec![index],
                        ));
                        Inst::ExtractElement {
                            ty: f.ty.clone(),
                            array: *arg,
                            index,
                        }
                    } else {
                        Inst::ExtractField {
                            ty: f.ty.clone(),
                            aggregate: *arg,
                            field,
                        }
                    };
                    let v = ValueId::new(next);
                    next += 1;
                    before.push(with(&call, inst, vec![v]));
                    vs.push(v);
                }
                bases.push(*arg); // No copied-out fields for a value parameter.
                loaded.push(vs);
                continue;
            }
            let base = if aty == Ty::Ptr {
                *arg
            } else {
                next += 1;
                let b = ValueId::new(next - 1);
                before.push(with(
                    &call,
                    Inst::Cast {
                        op: CastOp::PtrToPtr,
                        src_ty: aty,
                        dst_ty: Ty::Ptr,
                        operand: *arg,
                    },
                    vec![b],
                ));
                b
            };
            let mut vs = Vec::new();
            for f in &p.reads {
                let at = offset_address(&mut next, base, f.offset, &call, &mut before);
                let v = ValueId::new(next);
                next += 1;
                before.push(with(
                    &call,
                    Inst::Load {
                        ty: f.ty.clone(),
                        ptr: at,
                        volatile: false,
                        align: Some(1),
                    },
                    vec![v],
                ));
                vs.push(v);
            }
            bases.push(base);
            loaded.push(vs);
        }
        let mut new_args = Vec::new();
        for (j, a) in args.iter().enumerate() {
            match plan.iter().position(|(p, _, _)| p.index == j) {
                Some(k) => new_args.extend(loaded[k].iter().copied()),
                None => new_args.push(*a),
            }
        }
        let mut results = call.results.clone();
        let mut outs: Vec<Vec<ValueId>> = Vec::new();
        for (p, _, _) in &plan {
            let o: Vec<ValueId> = p
                .writes
                .iter()
                .map(|_| {
                    next += 1;
                    ValueId::new(next - 1)
                })
                .collect();
            results.extend(o.iter().copied());
            outs.push(o);
        }
        let mut after = Vec::new();
        for (((p, _, _), base), o) in plan.iter().zip(&bases).zip(&outs) {
            for (f, v) in p.writes.iter().zip(o) {
                let at = offset_address(&mut next, *base, f.offset, &call, &mut after);
                after.push(with(
                    &call,
                    Inst::Store {
                        ty: f.ty.clone(),
                        ptr: at,
                        value: *v,
                        volatile: false,
                        align: Some(1),
                    },
                    Vec::new(),
                ));
            }
        }
        let mut redirected = call.clone();
        redirected.inst = Inst::Call {
            callee: clone,
            args: new_args,
        };
        redirected.results = results;
        witness.sites.push(ArgPromoSite {
            block: cur.blocks[bi].id,
            index: ni,
            callee: *callee,
            clone,
            params: plan.iter().map(|(p, _, _)| p.clone()).collect(),
        });
        let at = ni + before.len();
        let n_after = after.len();
        let body = &mut cur.blocks[bi].body;
        let tail: Vec<InstrNode> = body.drain(ni..).skip(1).collect();
        body.extend(before);
        body.push(redirected);
        body.extend(after);
        body.extend(tail);
        Some(at + n_after)
    }
}

/// Why each argument of a direct call that is derived from a frame slot of
/// `func` is not promoted, as `(callee, argument index, reason)` (the probes
/// that measure what stays; the reasons are this pass's own).
#[cfg(test)]
pub(crate) fn refusals(
    cx: &PassContext<'_>,
    func: &Function,
) -> Vec<(String, usize, &'static str)> {
    let module = cx.module;
    let defs = sole_defs(func);
    let uses = Uses::of(func);
    let slots = candidate_slots(module, &[], func);
    let full = never_poison(module, &[], func);
    let mut roots: Vec<(ValueId, Option<Family>)> = Vec::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        if let (Inst::Alloca { .. }, [root]) = (&node.inst, node.results.as_slice()) {
            roots.push((*root, family(module, func, &defs, &uses, *root)));
        }
    }
    let mut out = Vec::new();
    for (bi, block) in func.blocks.iter().enumerate() {
        for (ni, node) in block.body.iter().enumerate() {
            let Inst::Call { callee, args } = &node.inst else {
                continue;
            };
            let name = module
                .function_by_id(*callee)
                .map(|f| f.name.clone())
                .unwrap_or_default();
            for (j, arg) in args.iter().enumerate() {
                let Some((_, fam)) = roots
                    .iter()
                    .find(|(r, f)| r == arg || f.as_ref().is_some_and(|f| f.contains(arg)))
                else {
                    continue;
                };
                let why = (|| {
                    if fam.is_none() {
                        return "slot_derivation";
                    }
                    if !node.proofs.is_empty() || node.proof_context.is_some() {
                        return "call_proof_material";
                    }
                    let Some((target, sig)) = template(module, *callee) else {
                        return "callee_not_admitted";
                    };
                    let Some(s) = shape(module, target, j) else {
                        return "callee_param_use";
                    };
                    let Some(slot) = slots.iter().find(|s| s.fam.contains(arg)) else {
                        return "slot_escapes";
                    };
                    if args
                        .iter()
                        .enumerate()
                        .any(|(k, a)| k != j && slot.fam.contains(a))
                    {
                        return "aliased_argument";
                    }
                    let o = slot.fam.at[arg];
                    if s.reads.len() > MAX_FIELDS || s.writes.len() > MAX_FIELDS {
                        return "too_many_fields";
                    }
                    if s.extent > MAX_EXTENT {
                        return "extent";
                    }
                    if o.checked_add(s.extent).is_none_or(|end| end > slot.size) {
                        return "outside_slot";
                    }
                    if !fields_proved(
                        module,
                        func,
                        &slot.fam,
                        slot.root,
                        &full,
                        (bi, ni),
                        o,
                        &s.reads,
                    ) {
                        return "copy_in_unproved";
                    }
                    if !kept_params_declared(target, sig, |k| k == j) {
                        return "kept_param_retyped";
                    }
                    let mut types = Vec::new();
                    let mut fns = Vec::new();
                    let mut clones = Clones {
                        new_types: &mut types,
                        new_functions: &mut fns,
                    };
                    let param = ArgPromoParam {
                        index: j,
                        reads: s.reads.clone(),
                        writes: s.writes.clone(),
                    };
                    if clones.get(module, target, sig, &[(param, s)]).is_none() {
                        return "copy_out_unproved_or_budget";
                    }
                    "promotable"
                })();
                out.push((name.clone(), j, why));
            }
        }
    }
    out
}
