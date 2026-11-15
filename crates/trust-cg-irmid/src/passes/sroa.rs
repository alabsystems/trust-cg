// trust-cg-irmid/passes/sroa.rs - scalar replacement of frame slots
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Scalar replacement (mem2reg proper): a frame slot whose bytes are read and
//! written only at constant offsets becomes one SSA value per field, joined
//! by block parameters, and its loads and stores go. Dead-code elimination
//! then removes the `alloca` and its derived pointers, and the wasm32 lane
//! lays out no frame for a function left without one.
//!
//! **Which slots.** An `alloca` of known size (count-free, or counted by an
//! integer constant `k >= 1`: `k` elements) whose address is used only by
//! plain (non-volatile) loads and stores through it, by the rustc bridge's
//! field access through a pointer (a write-through `insertfield`, which
//! stores lane `field` of its record type, its result unused: the lane types
//! that result as the record, so an access through it is not one through the
//! slot; and a read-through `extractfield`, which loads that lane), by `gep`s of it
//! by constant non-negative indices (the flat trust-ir GEP: `size(pointee) *
//! sum(indices)` bytes on, from the `alloca` or from another such pointer),
//! by `ptrtoptr` casts to thin pointer types and by copies, every derived
//! pointer and every access inside the allocation. No other value is
//! computed from the address — no `ptrtoint`, call, block argument, store or
//! return of it — so only these accesses reach its bytes (`escape.rs`'s
//! premise). Volatile and atomic accesses, bulk memory operations and every
//! other use leave the slot alone. A read-through `extractfield`'s result
//! must be read as its lane's type: trust-ir's validator types it as the
//! declared record, so a use expecting another type (the bridge's
//! sign-reinterpreting `copy`) would become a new finding once the result is
//! a typed `copy`, and the wasm32 lane emits the mid-end's output only when it
//! adds none.
//!
//! **Fields.** The maximal runs of overlapping access ranges are the fields.
//! A run of one range is a whole field. A field whose accesses all have one
//! type a reload returns exactly (an integer, `bool`, `char` or float) is
//! carried as that type. A field read and written only as thin pointers of
//! the target's width, every store writing an address strictly inside a
//! fresh allocation (an `alloca` or a pointer derived from it by constant
//! steps, each inside it), is carried as a `ptr`: a reload resolves that
//! address to the same allocation and offset (the interpreter's allocations
//! are bump-allocated, never overlap and are never reused), so the loads
//! become copies (or `ptrtoptr`s) of the stored pointer, and the pointee's
//! address stays a pointer of its provenance instead of an integer. Otherwise
//! every access must be a word of the field's width (an integer or float, or
//! a thin pointer when the width is the pointer's), the carrier is an integer
//! (the first store's integer type, else the first load's, else the
//! pointer-width `i32`/`i64`), and an access of another type is a
//! reinterpretation of the same bytes: `bitcast` between words, `ptrtoint`
//! from and `inttoptr` to a pointer (a pointer reload resolves the stored
//! address to the live allocation containing it, which is what `inttoptr`
//! does at the load), through a `ptrtoptr` to or from `ptr` for another
//! pointer type (trust-ir's validator admits `ptrtoint` and `inttoptr` on
//! `ptr` only). A one-byte field may mix `bool` with one-byte integers: it is
//! carried as the integer, a `bool` store becomes its `zext` (the bytes zero
//! and one) and a `bool` load the nonzero test `icmp ne c, 0` (the interpreter
//! reads a `bool` byte as nonzero). The interpreter's casts and compares fault
//! on the poison image a load of uninitialized bytes carries, so a converted
//! store needs a value that is never poison, and a converted load needs every
//! unconverted store of its field to store one. A read of the slot itself
//! counts as never poison when every value stored into the slot is: once
//! promoted it is the field's carrier, which holds only the initial zero,
//! the stored values and merges of them (so a loop that reloads an iterator
//! field, steps it and stores it back keeps its field promotable). A field
//! wider than 8 bytes is promoted only when it
//! is 16 bytes read and written as 128-bit integers alone (the wasm32 lane
//! carries such a value in two `i64` locals at O1 and above, the levels this
//! pass runs at); any other wide field stays in memory.
//!
//! **Fields accessed in parts.** A run of several ranges (the bridge's word
//! copies of structs and enums over narrower fields) of 2, 4 or 8 bytes is
//! one field carried as the unsigned integer of its width. Byte images are
//! little-endian, so a part `[d, d + w)` read as `ty` is `trunc(c >> 8d)`
//! then its bits as `ty` (`bitcast`, or `inttoptr` for a pointer), and a
//! part written is `(c & !(M << 8d)) | (zext(bits) << 8d)` with `bits` the
//! value's bytes (`bitcast`, or `ptrtoint` of a pointer); a whole access is
//! a reinterpretation of the carrier as above. Parts are integers, `f32`s or
//! pointers of the target's width, and every value stored into the field is
//! never poison: its bytes are shifted and masked.
//!
//! **Initial values.** A read that only the `alloca` reaches reads the fresh
//! allocation's bytes, poison in the source: an integer field is given an
//! initial `const 0` right after the `alloca`, which refines that poison (a
//! read of it is undefined behaviour in the source or a value nobody may
//! inspect), and a part store merges into it. Any other field with such a
//! read stays.
//!
//! **Joins.** Each field's carrier values meet at the iterated dominance
//! frontier of the blocks that write the field (its stores, the `alloca`,
//! which renews every byte, and the entry), restricted to the blocks where
//! the field is live (pruned SSA; `field_liveness`); there the block gains a
//! parameter and every edge into it passes the value that reaches the end of
//! its predecessor, found by renaming over the dominator tree. A read some
//! path reaches before the `alloca` runs, a join at the entry block or
//! behind an unwind edge, an unreachable block, and an irreducible CFG (a
//! dispatch loop) leave the slot (or the function) alone.
//!
//! The rewrite and its witness are checked by
//! `trust_cg_verify::trust_ir_mid_tv` (`trust_ir_mid_tv_sroa.rs`), which
//! re-derives the slot, the fields, the conversions, the parts and, by
//! backward walks over every path, each claimed reaching definition from the
//! source.

use std::collections::{HashMap, HashSet};

use trust_cg_verify::trust_ir_mid_tv::{
    PassWitness, SroaField, SroaIncoming, SroaLoad, SroaMerge, SroaParam, SroaSlot, SroaStore,
    SroaWitness,
};
use trust_ir::{BinOp, BlockId, CastOp, Constant, EdgeKind, Function, Inst, Module, Ty, ValueId};

use super::ptr_gep::displacement;
use super::slots::round_trips;
use super::store_fwd::reducible;
use super::{MidPass, PassContext, alloca_count, record_lane, sole_defs, value_types};
use crate::cfg::TrustIrCfg;

pub(crate) struct Sroa;

/// One access through a candidate slot.
#[derive(Debug, Clone)]
struct Access {
    /// `(block position, node index)`.
    at: (usize, usize),
    offset: u64,
    size: u64,
    /// The access type: a load's or store's, or the lane's for the bridge's
    /// field access through a pointer.
    ty: Ty,
    /// The stored value, for a store.
    value: Option<ValueId>,
    /// The load's result, for a load.
    result: Option<ValueId>,
}

/// A thin pointer: one address word, no metadata.
fn thin_pointer(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
    )
}

/// An integer or `f32`/`f64`: its bytes are its raw bits.
fn word(ty: &Ty) -> bool {
    ty.is_integer() || matches!(ty, Ty::F32 | Ty::F64)
}

/// A one-byte integer: the carrier of a `bool` field also accessed as an
/// integer.
fn byte_int(ty: &Ty) -> bool {
    matches!(ty, Ty::I8 | Ty::U8)
}

/// The cast reading a `from` value's bytes as a `to` value of `size` bytes,
/// `None` for the identity, `Err(())` when there is none. A `bool`'s byte
/// read as a one-byte integer is its `zext` (the interpreter writes a
/// `bool` as the byte 0 or 1); a one-byte integer read as a `bool` is the
/// nonzero test (the interpreter reads a `bool` byte as `byte != 0`), which
/// is no cast: `Trunc` names it here, and the rewrite spells it `icmp ne c,
/// zero` with a fresh `const` zero of the carrier ([`bool_read`]).
fn reinterpretation(
    from: &Ty,
    to: &Ty,
    size: u64,
    pointer_bits: u32,
) -> Result<Option<CastOp>, ()> {
    let pointer_word = |ty: &Ty| ty.is_integer() && size * 8 == u64::from(pointer_bits);
    if from == to {
        Ok(None)
    } else if *from == Ty::Bool && byte_int(to) && size == 1 {
        Ok(Some(CastOp::ZExt))
    } else if byte_int(from) && *to == Ty::Bool && size == 1 {
        Ok(Some(CastOp::Trunc))
    } else if word(from) && word(to) {
        Ok(Some(CastOp::Bitcast))
    } else if thin_pointer(from) && pointer_word(to) {
        Ok(Some(CastOp::PtrToInt))
    } else if pointer_word(from) && thin_pointer(to) {
        Ok(Some(CastOp::IntToPtr))
    } else if thin_pointer(from) && thin_pointer(to) {
        Ok(Some(CastOp::PtrToPtr))
    } else {
        Err(())
    }
}

/// The values never the poison image of uninitialized bytes (the checker's
/// rule, derived here independently): results of arithmetic, comparisons,
/// casts and address computations, scalar constants, `null`, global
/// addresses, allocations and the results of a call to a function with a
/// body; copies and selects of such; and block parameters every edge into
/// whose block passes such a value. `seeds` adds values that are such when
/// every one of their operands is (a slot's reads over the values stored
/// into it, [`plan_slot`]).
fn defined_values(
    module: &Module,
    func: &Function,
    seeds: &[(ValueId, Vec<ValueId>)],
) -> HashSet<ValueId> {
    let mut defined = HashSet::new();
    let mut moves: Vec<(ValueId, Vec<ValueId>)> = seeds.to_vec();
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
            | Inst::GEP { .. } => defined.extend(node.results.iter().copied()),
            Inst::Call { callee, .. }
                if module
                    .function_by_id(*callee)
                    .is_some_and(|f| !f.is_declaration()) =>
            {
                defined.extend(node.results.iter().copied());
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
                defined.extend(node.results.iter().copied());
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
    let positions: HashMap<BlockId, usize> = func
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.id, i))
        .collect();
    // Per block, the argument list of every edge into it (`None`: unwind).
    let mut incoming: Vec<Vec<Option<Vec<ValueId>>>> = vec![Vec::new(); func.blocks.len()];
    for block in &func.blocks {
        if let Some(last) = block.body.last() {
            for edge in last.inst.successor_edges() {
                if let Some(&ti) = positions.get(&edge.target) {
                    incoming[ti].push((edge.kind == EdgeKind::Normal).then(|| edge.args.to_vec()));
                }
            }
        }
    }
    let mut params = Vec::new();
    for (bi, block) in func.blocks.iter().enumerate() {
        for (pi, (value, _)) in block.params.iter().enumerate() {
            params.push((*value, bi, pi));
            defined.insert(*value);
        }
    }
    defined.extend(moves.iter().map(|(r, _)| *r));
    loop {
        let mut changed = false;
        for (r, operands) in &moves {
            if defined.contains(r) && !operands.iter().all(|o| defined.contains(o)) {
                defined.remove(r);
                changed = true;
            }
        }
        for &(value, bi, pi) in &params {
            if defined.contains(&value)
                && !incoming[bi].iter().all(|args| {
                    args.as_ref()
                        .and_then(|a| a.get(pi))
                        .is_some_and(|a| defined.contains(a))
                })
            {
                defined.remove(&value);
                changed = true;
            }
        }
        if !changed {
            return defined;
        }
    }
}

// Why a slot stays in memory: the pass's refusals, by name.
const NO_LAYOUT: &str = "no_layout";
const OUT_OF_BOUNDS: &str = "out_of_bounds";
const VARIABLE_INDEX: &str = "variable_index";
const OTHER_USE: &str = "other_use";
const NOT_READ_AND_WRITTEN: &str = "not_read_and_written";
const MIXED_WIDTH: &str = "mixed_width";
const PARTIAL_OVERLAP: &str = "partial_overlap";
const WIDE_FIELD: &str = "wide_field";
const NO_CARRIER: &str = "no_carrier";
const STORED_UNDEF: &str = "stored_undef";
const STORED_TYPE: &str = "stored_type";
const MAY_BE_POISON: &str = "may_be_poison";
const MIXED_WIDTH_MAY_BE_POISON: &str = "mixed_width_may_be_poison";
const POINTER_MAY_BE_POISON: &str = "pointer_may_be_poison";
const JOIN_AT_ENTRY: &str = "join_at_entry";
const JOIN_BEHIND_UNWIND: &str = "join_behind_unwind";
const UNDEFINED_READ: &str = "undefined_read";
const READ_THROUGH_RETYPED: &str = "read_through_retyped";
const WRITE_THROUGH_RESULT_USED: &str = "write_through_result_used";

/// Why `inst`, a use of the slot pointer `pointer` that is not an access
/// or an offset, keeps the slot in memory.
fn escape_reason(inst: &Inst, pointer: ValueId) -> &'static str {
    match inst {
        Inst::Store { value, .. } | Inst::InsertField { value, .. } if *value == pointer => {
            "escape_store"
        }
        Inst::Load { volatile: true, .. } | Inst::Store { volatile: true, .. } => "volatile",
        Inst::MemCopy { .. } | Inst::MemSet { .. } => "bulk_memory",
        Inst::AtomicLoad { .. }
        | Inst::AtomicStore { .. }
        | Inst::AtomicRMW { .. }
        | Inst::CmpXchg { .. } => "atomic",
        Inst::Call { .. }
        | Inst::CallIndirect { .. }
        | Inst::Invoke { .. }
        | Inst::InvokeIndirect { .. }
        | Inst::CallCannotUnwind { .. }
        | Inst::CallIndirectCannotUnwind { .. } => "escape_call",
        Inst::Return { .. } => "escape_return",
        Inst::Br { .. } | Inst::CondBr { .. } | Inst::Switch { .. } => "escape_block_arg",
        Inst::Cast {
            op: CastOp::PtrToInt,
            ..
        } => "ptrtoint",
        Inst::GEP { .. } => "variable_index",
        Inst::InsertField { aggregate, .. } if *aggregate == pointer => "write_through_insertfield",
        Inst::ExtractField { aggregate, .. } if *aggregate == pointer => {
            "read_through_extractfield"
        }
        Inst::ExtractElement { array, .. } if *array == pointer => "read_through_extractelement",
        _ => OTHER_USE,
    }
}

/// Whether every use of `value`, the result of a read-through `extractfield`
/// of lane type `ty`, reads it as `ty`. trust-ir's validator leaves such a
/// result untyped, so the bridge's sign-reinterpreting `copy` of one (the
/// lane moves the bits) is no finding there; replaced by a `copy` typed
/// `ty`, a use expecting another type would become one, and the wasm32
/// lane emits the mid-end's output only when it adds no finding.
pub(super) fn reads_as(func: &Function, uses: &[(usize, usize)], value: ValueId, ty: &Ty) -> bool {
    uses.iter().all(|&(bi, ni)| {
        let inst = &func.blocks[bi].body[ni].inst;
        let edge_types_agree = || {
            inst.successor_edges().iter().all(|edge| {
                let Some(target) = func.blocks.iter().find(|b| b.id == edge.target) else {
                    return false;
                };
                edge.args
                    .iter()
                    .zip(&target.params)
                    .all(|(arg, (_, param_ty))| *arg != value || param_ty == ty)
            })
        };
        match inst {
            Inst::Copy { ty: t, .. }
            | Inst::BinOp { ty: t, .. }
            | Inst::Select { ty: t, .. }
            | Inst::Cast { src_ty: t, .. } => t == ty,
            Inst::Store {
                ty: t,
                value: v,
                ptr,
                ..
            } => t == ty && *v == value && *ptr != value,
            Inst::ICmp { ty: t, .. } => t == ty && (ty.is_integer() || *ty == Ty::Ptr),
            Inst::FCmp { ty: t, .. } => t == ty,
            Inst::Br { .. } => edge_types_agree(),
            Inst::CondBr { cond, .. } => (*cond != value || *ty == Ty::Bool) && edge_types_agree(),
            Inst::Switch { value: v, .. } => (*v != value || ty.is_integer()) && edge_types_agree(),
            _ => false,
        }
    })
}

/// The accesses of the slot `alloca` (module docs), or why it stays.
fn slot_accesses(
    module: &Module,
    func: &Function,
    uses: &HashMap<ValueId, Vec<(usize, usize)>>,
    defs: &HashMap<ValueId, &Inst>,
    alloca: ValueId,
    size: u64,
) -> Result<Vec<Access>, &'static str> {
    let size_of = |ty: &Ty| {
        module
            .ty_layout_shape(ty)
            .ok()
            .and_then(|shape| shape.size_bytes())
    };
    let constant = |v: ValueId| match defs.get(&v) {
        Some(Inst::Const {
            ty,
            value: Constant::Int(k),
        }) if ty.is_integer() => u64::try_from(*k).ok(),
        _ => None,
    };
    // Each derived pointer: its offset into the slot.
    let mut pointers: HashMap<ValueId, u64> = HashMap::from([(alloca, 0)]);
    let mut pending = vec![alloca];
    let mut accesses = Vec::new();
    while let Some(pointer) = pending.pop() {
        let offset = pointers[&pointer];
        let mut access = |at, at_offset: u64, ty: &Ty, value, result| {
            let width = size_of(ty).filter(|&w| w > 0).ok_or(NO_LAYOUT)?;
            if at_offset.checked_add(width).is_none_or(|end| end > size) {
                return Err(OUT_OF_BOUNDS);
            }
            accesses.push(Access {
                at,
                offset: at_offset,
                size: width,
                ty: ty.clone(),
                value,
                result,
            });
            Ok(())
        };
        for &(bi, ni) in uses.get(&pointer).map_or(&[][..], Vec::as_slice) {
            let node = &func.blocks[bi].body[ni];
            let derived = match &node.inst {
                Inst::Load {
                    ty,
                    ptr,
                    volatile: false,
                    ..
                } if *ptr == pointer => {
                    access((bi, ni), offset, ty, None, node.results.first().copied())?;
                    None
                }
                Inst::Store {
                    ty,
                    ptr,
                    value,
                    volatile: false,
                    ..
                } if *ptr == pointer && !pointers.contains_key(value) => {
                    access((bi, ni), offset, ty, Some(*value), None)?;
                    None
                }
                // The bridge's write-through `insertfield`: lane `field` of
                // the record `ty` is stored through the pointer. Its result
                // must be unused: the lane types it as the record, so a
                // further access through it is not one through the slot.
                Inst::InsertField {
                    ty,
                    aggregate,
                    field,
                    value,
                } if *aggregate == pointer && !pointers.contains_key(value) => {
                    if node.results.iter().any(|r| uses.contains_key(r)) {
                        return Err(WRITE_THROUGH_RESULT_USED);
                    }
                    let (lane_offset, lane_ty) =
                        record_lane(module, ty, *field).ok_or("write_through_insertfield")?;
                    let at_offset = offset.checked_add(lane_offset).ok_or(OUT_OF_BOUNDS)?;
                    access((bi, ni), at_offset, &lane_ty, Some(*value), None)?;
                    None
                }
                // The read-through `extractfield`: lane `field` of the record
                // `ty` loaded through the pointer.
                Inst::ExtractField {
                    ty,
                    aggregate,
                    field,
                } if *aggregate == pointer => {
                    let (lane_offset, lane_ty) =
                        record_lane(module, ty, *field).ok_or("read_through_extractfield")?;
                    let at_offset = offset.checked_add(lane_offset).ok_or(OUT_OF_BOUNDS)?;
                    let [result] = node.results.as_slice() else {
                        return Err(OTHER_USE);
                    };
                    let result_uses = uses.get(result).map_or(&[][..], Vec::as_slice);
                    if !reads_as(func, result_uses, *result, &lane_ty) {
                        return Err(READ_THROUGH_RETYPED);
                    }
                    access((bi, ni), at_offset, &lane_ty, None, Some(*result))?;
                    None
                }
                Inst::GEP {
                    pointee_ty,
                    base,
                    indices,
                    ..
                } if *base == pointer && !indices.contains(&pointer) => {
                    let elem = size_of(pointee_ty).ok_or(NO_LAYOUT)?;
                    let mut delta = 0u64;
                    for k in indices {
                        let k = constant(*k).ok_or(VARIABLE_INDEX)?;
                        delta = elem
                            .checked_mul(k)
                            .and_then(|d| delta.checked_add(d))
                            .ok_or(OUT_OF_BOUNDS)?;
                    }
                    Some(offset.checked_add(delta).ok_or(OUT_OF_BOUNDS)?)
                }
                Inst::Cast {
                    op: CastOp::PtrToPtr,
                    dst_ty,
                    operand,
                    ..
                } if *operand == pointer && thin_pointer(dst_ty) => Some(offset),
                Inst::Copy { ty, operand } if *operand == pointer && thin_pointer(ty) => {
                    Some(offset)
                }
                _ => return Err(escape_reason(&node.inst, pointer)),
            };
            if let Some(derived) = derived {
                if derived >= size {
                    return Err(OUT_OF_BOUNDS);
                }
                let [r] = node.results.as_slice() else {
                    return Err(OTHER_USE);
                };
                match pointers.insert(*r, derived) {
                    None => pending.push(*r),
                    Some(old) if old == derived => {}
                    Some(_) => return Err(OTHER_USE),
                }
            }
        }
    }
    Ok(accesses)
}

/// The function-wide facts every slot's plan reads.
struct Facts<'f> {
    module: &'f Module,
    func: &'f Function,
    positions: HashMap<BlockId, usize>,
    entry: usize,
    /// Successor edges per block: (target position, edge number, kind).
    succs: Vec<Vec<(usize, usize, EdgeKind)>>,
    /// Distinct predecessors per block.
    preds: Vec<Vec<usize>>,
    /// Every block, in CFG postorder (the reverse of the analysis' RPO).
    postorder: Vec<usize>,
    /// Dominator-tree children per block, in layout order.
    children: Vec<Vec<usize>>,
    /// Dominance frontier per block.
    frontier: Vec<Vec<usize>>,
    types: HashMap<ValueId, Ty>,
    op_types: HashMap<ValueId, Ty>,
    pointer_bits: u32,
}

impl<'f> Facts<'f> {
    /// `None` when the function has an unreachable block or an irreducible
    /// CFG.
    fn new(module: &'f Module, func: &'f Function, pointer_bits: u32) -> Option<Self> {
        let view = TrustIrCfg::new(func);
        let cfg = view.analysis();
        if cfg.rpo.len() != func.blocks.len() || !reducible(func, &cfg) {
            return None;
        }
        let positions: HashMap<BlockId, usize> = func
            .blocks
            .iter()
            .enumerate()
            .map(|(i, b)| (b.id, i))
            .collect();
        let entry = *positions.get(&func.entry)?;
        let n = func.blocks.len();
        let mut succs = vec![Vec::new(); n];
        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (bi, block) in func.blocks.iter().enumerate() {
            if let Some(last) = block.body.last() {
                for (ei, edge) in last.inst.successor_edges().iter().enumerate() {
                    let ti = *positions.get(&edge.target)?;
                    succs[bi].push((ti, ei, edge.kind));
                    if !preds[ti].contains(&bi) {
                        preds[ti].push(bi);
                    }
                }
            }
        }
        let mut postorder = Vec::with_capacity(n);
        for b in cfg.rpo.iter().rev() {
            postorder.push(*positions.get(b)?);
        }
        let mut idom = vec![usize::MAX; n];
        for (b, d) in &cfg.idom {
            idom[*positions.get(b)?] = *positions.get(d)?;
        }
        let mut children = vec![Vec::new(); n];
        for (b, &d) in idom.iter().enumerate() {
            if b != entry && d != usize::MAX {
                children[d].push(b);
            }
        }
        // Cooper/Harvey/Kennedy dominance frontiers.
        let mut frontier: Vec<Vec<usize>> = vec![Vec::new(); n];
        for b in 0..n {
            if preds[b].len() < 2 {
                continue;
            }
            for &p in &preds[b] {
                let mut runner = p;
                while runner != idom[b] {
                    if !frontier[runner].contains(&b) {
                        frontier[runner].push(b);
                    }
                    if runner == entry {
                        break;
                    }
                    runner = idom[runner];
                }
            }
        }
        Some(Self {
            module,
            func,
            positions,
            entry,
            succs,
            preds,
            postorder,
            children,
            frontier,
            types: value_types(func),
            op_types: op_types(module, func),
            pointer_bits,
        })
    }
}

/// The type of a stored value: the pass-side typing, or the result types of
/// unary, overflow and call operations ([`op_types`]).
fn stored_type(facts: &Facts<'_>, value: ValueId) -> Option<Ty> {
    facts
        .types
        .get(&value)
        .or_else(|| facts.op_types.get(&value))
        .cloned()
}

/// The result types the shared typing leaves out: a unary operation's (its
/// operand type), an overflow operation's (its type and `bool`), and a call's
/// (its signature's returns, one per result).
fn op_types(module: &Module, func: &Function) -> HashMap<ValueId, Ty> {
    let mut types = HashMap::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        let returns: Vec<Ty> = match &node.inst {
            Inst::UnOp { ty, .. } => vec![ty.clone()],
            Inst::Overflow { ty, .. } => vec![ty.clone(), Ty::Bool],
            Inst::Call { callee, .. } => module
                .function_by_id(*callee)
                .and_then(|f| module.func_type(f.ty))
                .map(|ft| ft.returns.clone())
                .unwrap_or_default(),
            Inst::CallIndirect { sig, .. } => module
                .func_type(*sig)
                .map(|ft| ft.returns.clone())
                .unwrap_or_default(),
            _ => continue,
        };
        if returns.len() == node.results.len() {
            types.extend(node.results.iter().copied().zip(returns));
        }
    }
    types
}

/// One event of a slot in a block: the node index, and `Some((field, is a
/// load))` for an access or `None` for the `alloca`.
type SlotEvent = (usize, Option<(usize, bool)>);

/// One bit per (block, field), stored block-major.
struct FieldBits {
    words: usize,
    bits: Vec<u64>,
}

impl FieldBits {
    fn new(blocks: usize, fields: usize) -> Self {
        let words = fields.div_ceil(64);
        Self {
            words,
            bits: vec![0; blocks * words],
        }
    }

    fn row(&self, b: usize) -> &[u64] {
        &self.bits[b * self.words..(b + 1) * self.words]
    }

    fn get(&self, b: usize, f: usize) -> bool {
        (self.row(b)[f / 64] >> (f % 64)) & 1 == 1
    }
}

/// Liveness of each field at block entry (backward): a load reads it, a
/// store or the `alloca` ends it. A worklist seeded in postorder, which
/// re-queues a block's predecessors only when its live-in set grows, so an
/// acyclic CFG takes one visit per block whatever its layout.
fn field_liveness(facts: &Facts<'_>, events: &[Vec<SlotEvent>], nf: usize) -> FieldBits {
    let n = facts.func.blocks.len();
    let mut live_in = FieldBits::new(n, nf);
    let words = live_in.words;
    let mut queue: std::collections::VecDeque<usize> = facts.postorder.iter().copied().collect();
    let mut queued = vec![true; n];
    let mut live = vec![0u64; words];
    while let Some(b) = queue.pop_front() {
        queued[b] = false;
        #[cfg(test)]
        LIVENESS_VISITS.with(|c| c.set(c.get() + 1));
        live.iter_mut().for_each(|w| *w = 0);
        for &(t, _, _) in &facts.succs[b] {
            for (w, &x) in live.iter_mut().zip(live_in.row(t)) {
                *w |= x;
            }
        }
        for &(_, event) in events[b].iter().rev() {
            match event {
                None => live.iter_mut().for_each(|w| *w = 0),
                Some((f, true)) => live[f / 64] |= 1 << (f % 64),
                Some((f, false)) => live[f / 64] &= !(1 << (f % 64)),
            }
        }
        if live[..] != *live_in.row(b) {
            live_in.bits[b * words..(b + 1) * words].copy_from_slice(&live);
            for &p in &facts.preds[b] {
                if !queued[p] {
                    queued[p] = true;
                    queue.push_back(p);
                }
            }
        }
    }
    live_in
}

#[cfg(test)]
thread_local! {
    /// Block visits of [`field_liveness`] on this thread, for the tests that
    /// bound its work.
    pub(crate) static LIVENESS_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The unsigned integer type of a part of `bytes` bytes of a field.
fn part_ty(bytes: u64) -> Option<Ty> {
    match bytes {
        1 => Some(Ty::U8),
        2 => Some(Ty::U16),
        4 => Some(Ty::U32),
        _ => None,
    }
}

/// The carrier of a field accessed in parts: the unsigned integer of its
/// width.
fn composite_carrier(bytes: u64) -> Option<Ty> {
    match bytes {
        2 => Some(Ty::U16),
        4 => Some(Ty::U32),
        8 => Some(Ty::U64),
        _ => None,
    }
}

/// Whether an access of `ty` and `bytes` bytes may read or write part of a
/// field: an integer or `f32` (its bits), or a thin pointer of the target's
/// width (its address).
fn part_access(ty: &Ty, bytes: u64, pointer_bits: u32) -> bool {
    part_ty(bytes).is_some()
        && (ty.is_integer()
            || *ty == Ty::F32
            || (thin_pointer(ty) && bytes * 8 == u64::from(pointer_bits)))
}

/// The fresh values a part access takes besides its `via`: a load, the shift
/// (amount and result) when the part is not at the field's start, then the
/// truncation; a store, the bits as the part's integer when its type is
/// another, the zero extension, the shift, then the mask, the masked field
/// and the merged field.
fn part_values(store: bool, d: u64, ty: &Ty, part: &Ty) -> usize {
    let shift = if d > 0 { 2 } else { 0 };
    if store {
        usize::from(ty != part) + 1 + shift + 3
    } else {
        shift + 1
    }
}

/// The part accesses of a plan: `(block, node index)` to the part's offset
/// into its field and its width.
type Parts = HashMap<(BlockId, usize), (u64, u64)>;

/// A field's value at a point of the renaming: no `alloca` yet on this
/// path, the `alloca`'s fresh bytes, or a carried value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Reaching {
    Unallocated,
    Fresh,
    Value(ValueId),
}

/// Plan the promotion of one slot, or why it stays.
fn plan_slot(
    facts: &Facts<'_>,
    defs: &HashMap<ValueId, &Inst>,
    alloca: ValueId,
    alloca_at: (usize, usize),
    accesses: &[Access],
    fresh: &mut trust_ir::FreshIds<ValueId>,
) -> Result<(SroaSlot, Parts), &'static str> {
    if !accesses.iter().any(|a| a.value.is_some()) || !accesses.iter().any(|a| a.result.is_some()) {
        return Err(NOT_READ_AND_WRITTEN);
    }
    let mut take = || fresh.take().map_err(|_| OTHER_USE);
    // The slot's reads are never poison when no value stored into it is:
    // once promoted, a read is the field's carrier, which holds only the
    // initial zero, the stored values (converted) and merges of them, so
    // by induction over an execution a read feeding a store of the slot
    // (a loop's update of an iterator field) keeps it so.
    let stored_into: Vec<ValueId> = accesses.iter().filter_map(|a| a.value).collect();
    let seeds: Vec<(ValueId, Vec<ValueId>)> = accesses
        .iter()
        .filter_map(|a| a.result.map(|r| (r, stored_into.clone())))
        .collect();
    let seeded = defined_values(facts.module, facts.func, &seeds);
    let defined = &seeded;
    // Fields: the maximal runs of overlapping access ranges. A run of one
    // range is a whole field; a longer one is a field accessed in parts.
    let mut ranges: Vec<(u64, u64)> = accesses.iter().map(|a| (a.offset, a.size)).collect();
    ranges.sort_unstable();
    ranges.dedup();
    let mut runs: Vec<(u64, u64, usize)> = Vec::new();
    for &(offset, size) in &ranges {
        match runs.last_mut() {
            Some(run) if offset < run.1 => {
                run.1 = run.1.max(offset + size);
                run.2 += 1;
            }
            _ => runs.push((offset, offset + size, 1)),
        }
    }
    let field_of = |a: &Access| runs.iter().position(|r| r.0 <= a.offset && a.offset < r.1);
    let mut fields: Vec<SroaField> = Vec::with_capacity(runs.len());
    let mut composite = vec![false; runs.len()];
    for (fi, &(offset, end, distinct)) in runs.iter().enumerate() {
        let size = end - offset;
        let of_field: Vec<&Access> = accesses
            .iter()
            .filter(|a| field_of(a) == Some(fi))
            .collect();
        if size > 8 && !(size == 16 && of_field.iter().all(|a| matches!(a.ty, Ty::I128 | Ty::U128)))
        {
            // Wide fields other than 128-bit integers stay in memory (module
            // docs).
            return Err(WIDE_FIELD);
        }
        if distinct > 1 {
            // Accessed in parts: an unsigned integer carrier of the field's
            // width, parts that are integers, `f32`s or pointers, and whole
            // accesses that reinterpret the carrier; every stored value is
            // never poison, since a part's bytes are shifted and masked.
            let carrier = composite_carrier(size).ok_or(PARTIAL_OVERLAP)?;
            for a in &of_field {
                let whole = a.offset == offset && a.size == size;
                let fits = if whole {
                    reinterpretation(&carrier, &a.ty, size, facts.pointer_bits).is_ok()
                } else {
                    part_access(&a.ty, a.size, facts.pointer_bits)
                };
                if !fits {
                    return Err(MIXED_WIDTH);
                }
                if a.value.is_some_and(|v| !defined.contains(&v)) {
                    return Err(MIXED_WIDTH_MAY_BE_POISON);
                }
            }
            composite[fi] = true;
            fields.push(SroaField {
                offset,
                size,
                carrier,
                init: None,
            });
            continue;
        }
        let first = &of_field[0].ty;
        // A field read and written only as thin pointers whose every store
        // writes an address strictly inside a fresh allocation is carried
        // as a `ptr`: a reload resolves that address to the same allocation
        // and offset (allocations never overlap and are never reused), so it
        // is the stored pointer itself, and the address it holds stays a
        // value of its own provenance rather than an observed integer.
        let pointer_field = size * 8 == u64::from(facts.pointer_bits)
            && of_field.iter().all(|a| thin_pointer(&a.ty))
            && of_field
                .iter()
                .filter_map(|a| a.value)
                .all(|v| displacement(facts.module, defs, v).is_some());
        let carrier = if pointer_field {
            Ty::Ptr
        } else if of_field.iter().all(|a| &a.ty == first) && round_trips(first) {
            first.clone()
        } else {
            // A one-byte field may mix `bool` with one-byte integers: it is
            // carried as the integer, a `bool` store its `zext`, a `bool`
            // load the nonzero test.
            let words = of_field.iter().all(|a| {
                word(&a.ty)
                    || (thin_pointer(&a.ty) && size * 8 == u64::from(facts.pointer_bits))
                    || (a.ty == Ty::Bool && size == 1)
            });
            if !words {
                return Err(NO_CARRIER);
            }
            let pick = |stores: bool| {
                of_field
                    .iter()
                    .find(|a| a.value.is_some() == stores && a.ty.is_integer())
                    .map(|a| a.ty.clone())
            };
            match pick(true).or_else(|| pick(false)) {
                Some(ty) => ty,
                None if of_field.iter().any(|a| thin_pointer(&a.ty)) => {
                    if facts.pointer_bits == 32 {
                        Ty::I32
                    } else {
                        Ty::I64
                    }
                }
                None => of_field
                    .iter()
                    .find(|a| a.value.is_some())
                    .map(|a| a.ty.clone())
                    .ok_or(NO_CARRIER)?,
            }
        };
        fields.push(SroaField {
            offset,
            size,
            carrier,
            init: None,
        });
    }
    // Conversions and the never-poison conditions. A part access is
    // `(offset into the field, width)`.
    let part_of = |a: &Access, fi: usize| {
        let f = &fields[fi];
        (composite[fi] && !(a.offset == f.offset && a.size == f.size))
            .then(|| (a.offset - f.offset, a.size))
    };
    let mut plain_full = vec![true; fields.len()];
    let mut converts_a_load = vec![false; fields.len()];
    let mut stores = Vec::new();
    let mut carried_at: HashMap<(usize, usize), (usize, ValueId)> = HashMap::new();
    let mut load_via: HashMap<(usize, usize), ValueId> = HashMap::new();
    let mut load_extract: HashMap<(usize, usize), Vec<ValueId>> = HashMap::new();
    // Per part store: its index in `stores`, to fill in the reaching value.
    let mut part_store_at: HashMap<(usize, usize), usize> = HashMap::new();
    for a in accesses {
        let fi = field_of(a).ok_or(OTHER_USE)?;
        let carrier = fields[fi].carrier.clone();
        let carrier = &carrier;
        let needs_ptr_via = thin_pointer(&a.ty) && a.ty != Ty::Ptr;
        match a.value {
            Some(value) => {
                if matches!(defs.get(&value), Some(Inst::Undef { .. })) {
                    return Err(STORED_UNDEF);
                }
                if stored_type(facts, value).as_ref() != Some(&a.ty) {
                    return Err(STORED_TYPE);
                }
                if let Some((d, w)) = part_of(a, fi) {
                    let part = part_ty(w).ok_or(MIXED_WIDTH)?;
                    let via = if needs_ptr_via { Some(take()?) } else { None };
                    let values = (0..part_values(true, d, &a.ty, &part))
                        .map(|_| take())
                        .collect::<Result<Vec<_>, _>>()?;
                    let merged = *values.last().ok_or(OTHER_USE)?;
                    carried_at.insert(a.at, (fi, merged));
                    part_store_at.insert(a.at, stores.len());
                    stores.push(SroaStore {
                        block: facts.func.blocks[a.at.0].id,
                        index: a.at.1,
                        field: fi,
                        converted: None,
                        via,
                        merge: Some(SroaMerge {
                            // Filled in by the renaming below.
                            prev: merged,
                            values,
                        }),
                    });
                    continue;
                }
                let conversion = reinterpretation(&a.ty, carrier, a.size, facts.pointer_bits)
                    .map_err(|()| NO_CARRIER)?;
                let (converted, via) = match conversion {
                    None => {
                        plain_full[fi] &= defined.contains(&value);
                        (None, None)
                    }
                    Some(op) => {
                        if !defined.contains(&value) {
                            return Err(if thin_pointer(&a.ty) {
                                POINTER_MAY_BE_POISON
                            } else {
                                MAY_BE_POISON
                            });
                        }
                        // trust-ir's `ptrtoint` takes a `ptr`.
                        let via = if op == CastOp::PtrToInt && a.ty != Ty::Ptr {
                            Some(take()?)
                        } else {
                            None
                        };
                        (Some(take()?), via)
                    }
                };
                carried_at.insert(a.at, (fi, converted.unwrap_or(value)));
                stores.push(SroaStore {
                    block: facts.func.blocks[a.at.0].id,
                    index: a.at.1,
                    field: fi,
                    converted,
                    via,
                    merge: None,
                });
            }
            None => {
                if let Some((d, w)) = part_of(a, fi) {
                    let part = part_ty(w).ok_or(MIXED_WIDTH)?;
                    if needs_ptr_via {
                        load_via.insert(a.at, take()?);
                    }
                    let values = (0..part_values(false, d, &a.ty, &part))
                        .map(|_| take())
                        .collect::<Result<Vec<_>, _>>()?;
                    load_extract.insert(a.at, values);
                    continue;
                }
                let conversion = reinterpretation(carrier, &a.ty, a.size, facts.pointer_bits)
                    .map_err(|()| NO_CARRIER)?;
                if conversion.is_none() && !round_trips(carrier) && *carrier != Ty::Ptr {
                    return Err(NO_CARRIER);
                }
                converts_a_load[fi] |= conversion.is_some();
                // trust-ir's `inttoptr` yields a `ptr`; the nonzero test of a
                // `bool` read compares with a fresh zero.
                if (conversion == Some(CastOp::IntToPtr) && a.ty != Ty::Ptr)
                    || conversion == Some(CastOp::Trunc)
                {
                    load_via.insert(a.at, take()?);
                }
            }
        }
    }
    if (0..fields.len()).any(|fi| converts_a_load[fi] && !plain_full[fi]) {
        return Err(
            if (0..fields.len()).any(|fi| {
                converts_a_load[fi] && !plain_full[fi] && thin_pointer(&fields[fi].carrier)
            }) {
                POINTER_MAY_BE_POISON
            } else {
                MAY_BE_POISON
            },
        );
    }
    // Per block, the slot's events in node order.
    let n = facts.func.blocks.len();
    let mut events: Vec<Vec<SlotEvent>> = vec![Vec::new(); n];
    events[alloca_at.0].push((alloca_at.1, None));
    for a in accesses {
        // A part store also reads the field it merges into.
        let fi = field_of(a).ok_or(OTHER_USE)?;
        events[a.at.0].push((
            a.at.1,
            Some((fi, a.result.is_some() || part_store_at.contains_key(&a.at))),
        ));
    }
    for list in &mut events {
        list.sort_unstable_by_key(|e| e.0);
    }
    let nf = fields.len();
    let live_in = field_liveness(facts, &events, nf);
    // Parameters: the iterated frontier of each field's writers, where live.
    let mut param_of: HashMap<(usize, usize), ValueId> = HashMap::new();
    let mut params: Vec<SroaParam> = Vec::new();
    let mut order: Vec<(usize, usize)> = Vec::new();
    for (f, _) in fields.iter().enumerate() {
        let mut work: Vec<usize> = vec![facts.entry, alloca_at.0];
        for a in accesses {
            if a.value.is_some() && field_of(a) == Some(f) {
                work.push(a.at.0);
            }
        }
        let mut queued: HashSet<usize> = work.iter().copied().collect();
        let mut placed: HashSet<usize> = HashSet::new();
        while let Some(b) = work.pop() {
            for &d in &facts.frontier[b] {
                if placed.insert(d) && queued.insert(d) {
                    work.push(d);
                }
            }
        }
        let mut blocks: Vec<usize> = placed.into_iter().filter(|&b| live_in.get(b, f)).collect();
        blocks.sort_unstable();
        for b in blocks {
            if b == facts.entry {
                return Err(JOIN_AT_ENTRY);
            }
            order.push((b, f));
        }
    }
    order.sort_unstable();
    for &(b, f) in &order {
        let value = take()?;
        param_of.insert((b, f), value);
        params.push(SroaParam {
            block: facts.func.blocks[b].id,
            field: f,
            value,
            incoming: Vec::new(),
        });
    }
    let param_index: HashMap<(usize, usize), usize> =
        order.iter().enumerate().map(|(i, k)| (*k, i)).collect();
    // A field read where only the `alloca` reaches reads its fresh bytes:
    // an integer field gets an initial zero, which refines the poison the
    // source reads there; any other field stays.
    let mut init: Vec<Option<ValueId>> = vec![None; nf];
    let mut read = |f: usize, state: Reaching| -> Result<ValueId, &'static str> {
        match state {
            Reaching::Value(v) => Ok(v),
            Reaching::Unallocated => Err(UNDEFINED_READ),
            Reaching::Fresh if fields[f].carrier.is_integer() => match init[f] {
                Some(v) => Ok(v),
                None => {
                    let v = take()?;
                    init[f] = Some(v);
                    Ok(v)
                }
            },
            Reaching::Fresh => Err(UNDEFINED_READ),
        }
    };
    // Renaming over the dominator tree.
    let mut loads = Vec::new();
    let mut stack: Vec<(usize, Vec<Reaching>)> =
        vec![(facts.entry, vec![Reaching::Unallocated; nf])];
    while let Some((b, mut cur)) = stack.pop() {
        for (f, slot) in cur.iter_mut().enumerate() {
            if let Some(&p) = param_of.get(&(b, f)) {
                *slot = Reaching::Value(p);
            }
        }
        for &(ni, event) in &events[b] {
            match event {
                None => cur.iter_mut().for_each(|c| *c = Reaching::Fresh),
                Some((f, true)) if part_store_at.contains_key(&(b, ni)) => {
                    let prev = read(f, cur[f])?;
                    if let Some(merge) = stores[part_store_at[&(b, ni)]].merge.as_mut() {
                        merge.prev = prev;
                    }
                    cur[f] = Reaching::Value(carried_at.get(&(b, ni)).ok_or(OTHER_USE)?.1);
                }
                Some((f, false)) => {
                    cur[f] = Reaching::Value(carried_at.get(&(b, ni)).ok_or(OTHER_USE)?.1);
                }
                Some((f, true)) => {
                    let result = facts.func.blocks[b].body[ni]
                        .results
                        .first()
                        .copied()
                        .ok_or(OTHER_USE)?;
                    loads.push(SroaLoad {
                        block: facts.func.blocks[b].id,
                        index: ni,
                        result,
                        field: f,
                        value: read(f, cur[f])?,
                        via: load_via.get(&(b, ni)).copied(),
                        extract: load_extract.get(&(b, ni)).cloned().unwrap_or_default(),
                    });
                }
            }
        }
        for &(t, ei, kind) in &facts.succs[b] {
            for (f, state) in cur.iter().enumerate() {
                if let Some(&pi) = param_index.get(&(t, f)) {
                    if kind != EdgeKind::Normal {
                        return Err(JOIN_BEHIND_UNWIND);
                    }
                    let value = read(f, *state)?;
                    params[pi].incoming.push(SroaIncoming {
                        pred: facts.func.blocks[b].id,
                        edge: ei,
                        value,
                    });
                }
            }
        }
        for &c in facts.children[b].iter().rev() {
            stack.push((c, cur.clone()));
        }
    }
    loads.sort_unstable_by_key(|l| (facts.positions[&l.block], l.index));
    let parts: Parts = accesses
        .iter()
        .filter_map(|a| {
            let fi = field_of(a)?;
            let (d, w) = part_of(a, fi)?;
            Some(((facts.func.blocks[a.at.0].id, a.at.1), (d, w)))
        })
        .collect();
    for (field, init) in fields.iter_mut().zip(init) {
        field.init = init;
    }
    Ok((
        SroaSlot {
            alloca,
            fields,
            stores,
            loads,
            params,
        },
        parts,
    ))
}

/// The mutable argument list of the `edge`-th normal edge of `inst`.
fn edge_args_mut(inst: &mut Inst, edge: usize) -> Option<&mut Vec<ValueId>> {
    match inst {
        Inst::Br { args, .. } if edge == 0 => Some(args),
        Inst::CondBr {
            then_args,
            else_args,
            ..
        } => match edge {
            0 => Some(then_args),
            1 => Some(else_args),
            _ => None,
        },
        Inst::Switch {
            cases,
            default_args,
            ..
        } => match edge.cmp(&cases.len()) {
            std::cmp::Ordering::Less => Some(&mut cases[edge].args),
            std::cmp::Ordering::Equal => Some(default_args),
            std::cmp::Ordering::Greater => None,
        },
        Inst::Invoke { normal_args, .. }
        | Inst::AssertInvoke { normal_args, .. }
        | Inst::DropInvoke { normal_args, .. }
        | Inst::InvokeIndirect { normal_args, .. }
            if edge == 0 =>
        {
            Some(normal_args)
        }
        _ => None,
    }
}

/// A node like `template` defining `result` by `inst`.
fn node_like(template: &trust_ir::InstrNode, inst: Inst, result: ValueId) -> trust_ir::InstrNode {
    let mut node = template.clone();
    node.inst = inst;
    node.results = vec![result];
    node
}

/// The nodes reading part `(d, w)` of the field value `value` (a `carrier`
/// integer) as `ty`, the last defining `result`: `trunc(value >> 8d)` to the
/// part's unsigned integer (byte images are little-endian), then its bits
/// as `ty`.
#[allow(clippy::too_many_arguments)]
fn part_read_nodes(
    template: &trust_ir::InstrNode,
    carrier: &Ty,
    (d, w): (u64, u64),
    ty: &Ty,
    value: ValueId,
    extract: &[ValueId],
    via: Option<ValueId>,
    result: ValueId,
) -> Option<Vec<trust_ir::InstrNode>> {
    let part = part_ty(w)?;
    let mut ids = extract.iter().copied();
    let mut nodes = Vec::new();
    let mut cur = value;
    if d > 0 {
        let (k, shifted) = (ids.next()?, ids.next()?);
        nodes.push(node_like(
            template,
            Inst::Const {
                ty: carrier.clone(),
                value: Constant::Int(i128::from(d * 8)),
            },
            k,
        ));
        nodes.push(node_like(
            template,
            Inst::BinOp {
                op: BinOp::LShr,
                ty: carrier.clone(),
                lhs: cur,
                rhs: k,
            },
            shifted,
        ));
        cur = shifted;
    }
    let truncated = ids.next()?;
    let cast = |op, src_ty: &Ty, dst_ty: &Ty, operand| Inst::Cast {
        op,
        src_ty: src_ty.clone(),
        dst_ty: dst_ty.clone(),
        operand,
    };
    nodes.push(node_like(
        template,
        cast(CastOp::Trunc, carrier, &part, cur),
        truncated,
    ));
    if *ty == part {
        nodes.push(node_like(
            template,
            Inst::Copy {
                ty: part,
                operand: truncated,
            },
            result,
        ));
    } else if thin_pointer(ty) {
        nodes.push(node_like(
            template,
            cast(CastOp::IntToPtr, &part, &Ty::Ptr, truncated),
            via.unwrap_or(result),
        ));
        if let Some(via) = via {
            nodes.push(node_like(
                template,
                cast(CastOp::PtrToPtr, &Ty::Ptr, ty, via),
                result,
            ));
        }
    } else {
        nodes.push(node_like(
            template,
            cast(CastOp::Bitcast, &part, ty, truncated),
            result,
        ));
    }
    Some(nodes)
}

/// The nodes writing `value` (of type `ty`) over part `(d, w)` of the field
/// value `merge.prev` (a `carrier` integer of `size` bytes):
/// `(prev & !(M << 8d)) | (zext(bits) << 8d)`, `M` the part's all-ones and
/// `bits` the value's bytes as the part's unsigned integer.
#[allow(clippy::too_many_arguments)]
fn part_write_nodes(
    template: &trust_ir::InstrNode,
    carrier: &Ty,
    size: u64,
    (d, w): (u64, u64),
    ty: &Ty,
    value: ValueId,
    merge: &SroaMerge,
    via: Option<ValueId>,
) -> Option<Vec<trust_ir::InstrNode>> {
    let part = part_ty(w)?;
    let mut ids = merge.values.iter().copied();
    let mut nodes = Vec::new();
    let cast = |op, src_ty: &Ty, dst_ty: &Ty, operand| Inst::Cast {
        op,
        src_ty: src_ty.clone(),
        dst_ty: dst_ty.clone(),
        operand,
    };
    let mut cur = value;
    if *ty != part {
        if thin_pointer(ty) {
            if let Some(via) = via {
                nodes.push(node_like(
                    template,
                    cast(CastOp::PtrToPtr, ty, &Ty::Ptr, cur),
                    via,
                ));
                cur = via;
            }
            let bits = ids.next()?;
            nodes.push(node_like(
                template,
                cast(CastOp::PtrToInt, &Ty::Ptr, &part, cur),
                bits,
            ));
            cur = bits;
        } else {
            let bits = ids.next()?;
            nodes.push(node_like(
                template,
                cast(CastOp::Bitcast, ty, &part, cur),
                bits,
            ));
            cur = bits;
        }
    }
    let widened = ids.next()?;
    nodes.push(node_like(
        template,
        cast(CastOp::ZExt, &part, carrier, cur),
        widened,
    ));
    cur = widened;
    let constant = |k: u128| Inst::Const {
        ty: carrier.clone(),
        value: Constant::Int(i128::try_from(k).unwrap_or(0)),
    };
    let binop = |op, lhs, rhs| Inst::BinOp {
        op,
        ty: carrier.clone(),
        lhs,
        rhs,
    };
    if d > 0 {
        let (k, shifted) = (ids.next()?, ids.next()?);
        nodes.push(node_like(template, constant(u128::from(d * 8)), k));
        nodes.push(node_like(template, binop(BinOp::Shl, cur, k), shifted));
        cur = shifted;
    }
    let all = (1u128 << (size * 8)) - 1;
    let mask = all & !(((1u128 << (w * 8)) - 1) << (d * 8));
    let (m, masked, merged) = (ids.next()?, ids.next()?, ids.next()?);
    nodes.push(node_like(template, constant(mask), m));
    nodes.push(node_like(
        template,
        binop(BinOp::And, merge.prev, m),
        masked,
    ));
    nodes.push(node_like(template, binop(BinOp::Or, masked, cur), merged));
    Some(nodes)
}

fn apply(
    func: &Function,
    witness: &SroaWitness,
    parts: &Parts,
    pointer_bits: u32,
    module: &Module,
) -> Option<Function> {
    let positions: HashMap<BlockId, usize> = func
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.id, i))
        .collect();
    let size_of = |ty: &Ty| {
        module
            .ty_layout_shape(ty)
            .ok()
            .and_then(|shape| shape.size_bytes())
    };
    let mut out = func.clone();
    let mut replaced: HashMap<(usize, usize), Vec<trust_ir::InstrNode>> = HashMap::new();
    for slot in &witness.slots {
        for param in &slot.params {
            let bi = *positions.get(&param.block)?;
            out.blocks[bi]
                .params
                .push((param.value, slot.fields[param.field].carrier.clone()));
        }
    }
    for slot in &witness.slots {
        for param in &slot.params {
            for incoming in &param.incoming {
                let pi = *positions.get(&incoming.pred)?;
                let last = out.blocks[pi].body.last_mut()?;
                edge_args_mut(&mut last.inst, incoming.edge)?.push(incoming.value);
            }
        }
    }
    for slot in &witness.slots {
        // Each initial zero follows its slot's `alloca`.
        if slot.fields.iter().any(|f| f.init.is_some()) {
            let at = func.blocks.iter().enumerate().find_map(|(bi, b)| {
                b.body
                    .iter()
                    .position(|n| n.results == [slot.alloca])
                    .map(|ni| (bi, ni))
            })?;
            let template = &func.blocks[at.0].body[at.1];
            let mut nodes = vec![template.clone()];
            for field in &slot.fields {
                if let Some(init) = field.init {
                    nodes.push(node_like(
                        template,
                        Inst::Const {
                            ty: field.carrier.clone(),
                            value: Constant::Int(0),
                        },
                        init,
                    ));
                }
            }
            replaced.insert(at, nodes);
        }
        for store in &slot.stores {
            let at = (*positions.get(&store.block)?, store.index);
            let node = &func.blocks[at.0].body[at.1];
            let cast = |op, src_ty: &Ty, dst_ty: &Ty, operand, result| {
                let mut node = node.clone();
                node.inst = Inst::Cast {
                    op,
                    src_ty: src_ty.clone(),
                    dst_ty: dst_ty.clone(),
                    operand,
                };
                node.results = vec![result];
                node
            };
            let (ty, value) = match &node.inst {
                Inst::Store { ty, value, .. } => (ty.clone(), *value),
                Inst::InsertField {
                    ty, field, value, ..
                } => (record_lane(module, ty, *field)?.1, *value),
                _ => return None,
            };
            let ty = &ty;
            let field = &slot.fields[store.field];
            let replacement = match (&store.merge, store.converted) {
                (Some(merge), _) => part_write_nodes(
                    node,
                    &field.carrier,
                    field.size,
                    *parts.get(&(store.block, store.index))?,
                    ty,
                    value,
                    merge,
                    store.via,
                )?,
                (None, None) => Vec::new(),
                (None, Some(converted)) => {
                    let carrier = &slot.fields[store.field].carrier;
                    let op = reinterpretation(ty, carrier, size_of(ty)?, pointer_bits).ok()??;
                    match store.via {
                        None => vec![cast(op, ty, carrier, value, converted)],
                        Some(via) => vec![
                            cast(CastOp::PtrToPtr, ty, &Ty::Ptr, value, via),
                            cast(op, &Ty::Ptr, carrier, via, converted),
                        ],
                    }
                }
            };
            replaced.insert(at, replacement);
        }
        for load in &slot.loads {
            let at = (*positions.get(&load.block)?, load.index);
            let mut node = func.blocks[at.0].body[at.1].clone();
            let ty = match &node.inst {
                Inst::Load { ty, .. } => ty.clone(),
                Inst::ExtractField { ty, field, .. } => record_lane(module, ty, *field)?.1,
                _ => return None,
            };
            if let Some(&part) = parts.get(&(load.block, load.index)) {
                let nodes = part_read_nodes(
                    &node,
                    &slot.fields[load.field].carrier,
                    part,
                    &ty,
                    load.value,
                    &load.extract,
                    load.via,
                    load.result,
                )?;
                replaced.insert(at, nodes);
                continue;
            }
            let carrier = &slot.fields[load.field].carrier;
            let conversion = reinterpretation(carrier, &ty, size_of(&ty)?, pointer_bits).ok()?;
            let nodes = match (conversion, load.via) {
                (None, _) => {
                    node.inst = Inst::Copy {
                        ty,
                        operand: load.value,
                    };
                    vec![node]
                }
                (Some(op), None) => {
                    node.inst = Inst::Cast {
                        op,
                        src_ty: carrier.clone(),
                        dst_ty: ty,
                        operand: load.value,
                    };
                    vec![node]
                }
                (Some(CastOp::Trunc), Some(via)) => bool_read(&node, carrier, load.value, via),
                (Some(op), Some(via)) => {
                    let mut first = node.clone();
                    first.inst = Inst::Cast {
                        op,
                        src_ty: carrier.clone(),
                        dst_ty: Ty::Ptr,
                        operand: load.value,
                    };
                    first.results = vec![via];
                    node.inst = Inst::Cast {
                        op: CastOp::PtrToPtr,
                        src_ty: Ty::Ptr,
                        dst_ty: ty,
                        operand: via,
                    };
                    vec![first, node]
                }
            };
            replaced.insert(at, nodes);
        }
    }
    for (bi, block) in out.blocks.iter_mut().enumerate() {
        let body = std::mem::take(&mut block.body);
        block.body = body
            .into_iter()
            .enumerate()
            .flat_map(|(ni, node)| replaced.remove(&(bi, ni)).unwrap_or_else(|| vec![node]))
            .collect();
    }
    Some(out)
}

/// A `bool` read of a one-byte integer carrier `value`, in place of the
/// load `node`: `via = const <carrier> 0`, then the load's result `= icmp
/// ne <carrier> value, via`.
fn bool_read(
    node: &trust_ir::InstrNode,
    carrier: &Ty,
    value: ValueId,
    via: ValueId,
) -> Vec<trust_ir::InstrNode> {
    let mut zero = node.clone();
    zero.inst = Inst::Const {
        ty: carrier.clone(),
        value: Constant::Int(0),
    };
    zero.results = vec![via];
    let mut test = node.clone();
    test.inst = Inst::ICmp {
        op: trust_ir::ICmpOp::Ne,
        ty: carrier.clone(),
        lhs: value,
        rhs: via,
    };
    vec![zero, test]
}

/// Every `alloca` of `func` this pass leaves in memory (count-free, counted
/// by a constant, or `counted_alloca` for any other count), with the reason
/// (the pass's own refusal; the probes that measure what stays).
#[cfg(test)]
pub(crate) fn refusals(cx: &PassContext<'_>, func: &Function) -> Vec<(ValueId, &'static str)> {
    let defs = sole_defs(func);
    let mut uses: HashMap<ValueId, Vec<(usize, usize)>> = HashMap::new();
    for (bi, block) in func.blocks.iter().enumerate() {
        for (ni, node) in block.body.iter().enumerate() {
            node.inst.visit_value_operands(|v| {
                let list = uses.entry(v).or_default();
                if list.last() != Some(&(bi, ni)) {
                    list.push((bi, ni));
                }
            });
        }
    }
    let facts = Facts::new(cx.module, func, cx.pointer_bits);
    let mut fresh = func.fresh_value_ids();
    let mut out = Vec::new();
    for (bi, block) in func.blocks.iter().enumerate() {
        for (ni, node) in block.body.iter().enumerate() {
            let (Inst::Alloca { ty, .. }, [alloca]) = (&node.inst, node.results.as_slice()) else {
                continue;
            };
            let count = match &node.inst {
                Inst::Alloca { count, .. } => alloca_count(&defs, *count),
                _ => None,
            };
            let size = cx
                .module
                .ty_layout_shape(ty)
                .ok()
                .and_then(|shape| shape.size_bytes())
                .zip(count)
                .and_then(|(s, k)| s.checked_mul(k))
                .filter(|&s| s > 0);
            let reason = match (size, count) {
                (_, None) => "counted_alloca",
                (None, _) => NO_LAYOUT,
                (Some(size), _) => {
                    match slot_accesses(cx.module, func, &uses, &defs, *alloca, size) {
                        Err(why) => why,
                        Ok(accesses) => match &facts {
                            None => "irreducible_or_unreachable",
                            Some(facts) => match plan_slot(
                                facts,
                                &defs,
                                *alloca,
                                (bi, ni),
                                &accesses,
                                &mut fresh,
                            ) {
                                Err(why) => why,
                                Ok(_) => "promotable",
                            },
                        },
                    }
                }
            };
            out.push((*alloca, reason));
        }
    }
    out
}

impl MidPass for Sroa {
    fn name(&self) -> &'static str {
        "sroa"
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let defs = sole_defs(func);
        let candidates: Vec<((usize, usize), ValueId, u64)> = func
            .blocks
            .iter()
            .enumerate()
            .flat_map(|(bi, b)| b.body.iter().enumerate().map(move |(ni, n)| (bi, ni, n)))
            .filter_map(
                |(bi, ni, node)| match (&node.inst, node.results.as_slice()) {
                    (Inst::Alloca { ty, count, .. }, [alloca]) => {
                        let size = cx
                            .module
                            .ty_layout_shape(ty)
                            .ok()
                            .and_then(|shape| shape.size_bytes())?
                            .checked_mul(alloca_count(&defs, *count)?)
                            .filter(|&s| s > 0)?;
                        Some(((bi, ni), *alloca, size))
                    }
                    _ => None,
                },
            )
            .collect();
        if candidates.is_empty() {
            return None;
        }
        let mut uses: HashMap<ValueId, Vec<(usize, usize)>> = HashMap::new();
        for (bi, block) in func.blocks.iter().enumerate() {
            for (ni, node) in block.body.iter().enumerate() {
                node.inst.visit_value_operands(|v| {
                    let list = uses.entry(v).or_default();
                    if list.last() != Some(&(bi, ni)) {
                        list.push((bi, ni));
                    }
                });
            }
        }
        // The slots with a load and a store (dead-slot removal takes those
        // nothing reads).
        let found: Vec<((usize, usize), ValueId, Vec<Access>)> = candidates
            .into_iter()
            .filter_map(|(at, alloca, size)| {
                let accesses = slot_accesses(cx.module, func, &uses, &defs, alloca, size).ok()?;
                (accesses.iter().any(|a| a.value.is_some())
                    && accesses.iter().any(|a| a.result.is_some()))
                .then_some((at, alloca, accesses))
            })
            .collect();
        if found.is_empty() {
            return None;
        }
        let facts = Facts::new(cx.module, func, cx.pointer_bits)?;
        let mut fresh = func.fresh_value_ids();
        let mut slots = Vec::new();
        let mut parts = Parts::new();
        for (at, alloca, accesses) in found {
            // A failed plan may have taken ids; they stay unused, and the
            // ids a kept plan takes are still fresh and distinct.
            if let Ok((slot, slot_parts)) =
                plan_slot(&facts, &defs, alloca, at, &accesses, &mut fresh)
            {
                slots.push(slot);
                parts.extend(slot_parts);
            }
        }
        if slots.is_empty() {
            return None;
        }
        let witness = SroaWitness { slots };
        let out = apply(func, &witness, &parts, cx.pointer_bits, cx.module)?;
        Some((out, PassWitness::Sroa(witness)))
    }
}
