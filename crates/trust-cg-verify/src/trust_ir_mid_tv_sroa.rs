// trust-cg-verify/trust_ir_mid_tv_sroa.rs - the scalar-replacement checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The checker of scalar replacement ([`SroaWitness`]): a frame slot whose
//! bytes are read and written only at constant offsets becomes one SSA value
//! per field, joined by block parameters, and its loads and stores go.
//!
//! What is re-derived here from the SOURCE alone, with the interpreter's
//! layout ([`FsymLayout`]):
//!
//! * **The slot is unobservable.** The `alloca` is count-free or counted by
//!   an integer constant `k >= 1` (`size(T) * k` bytes). Every use of it, and
//!   of every pointer derived from it, is a plain (non-volatile) load or
//!   store through it, the rustc bridge's field access through a pointer (a
//!   write-through `insertfield`, which stores lane `field` of its record
//!   type at that lane's offset, its result unused (the lane types that
//!   result as the record, so an access through it is not one through the
//!   slot), or a read-through `extractfield`, which loads that lane: the
//!   wasm32 lane's meaning of both, and the differential's view of them), a `gep` of it by
//!   constant non-negative integer indices (the interpreter's flat GEP:
//!   `size(pointee) * sum(indices)` bytes on), a `ptrtoptr` to a thin pointer
//!   type, or a `copy` of it; every derived pointer stays inside the
//!   allocation and every access lies in it. No other value is computed from
//!   the address (no `ptrtoint`, call, block argument, store or return of
//!   it), so only these accesses reach the allocation's bytes: the capture
//!   analysis's premise (`trust_cg_irmid::escape`), the same as store
//!   forwarding's. Atomic and volatile accesses, bulk memory operations and
//!   anything else leave the slot alone.
//! * **The fields partition the accesses.** The claimed fields are pairwise
//!   disjoint byte ranges, and every access lies in exactly one of them: all
//!   of it (a whole access), or part of it. The claimed loads and stores are
//!   exactly the slot's.
//! * **Each whole access is the same bytes as its field's carrier.** A field
//!   is carried as one SSA value of its `carrier` type, an integer, `bool`,
//!   `char` or float (a type whose reload returns exactly the stored value),
//!   or a `ptr` (below). An access of the carrier's own type moves the value
//!   (`copy` for a load); an access of another type of the field's width is
//!   a reinterpretation of the same bytes: `bitcast` between integers and
//!   floats, `ptrtoint` from and `inttoptr` to a thin pointer at an integer
//!   carrier of pointer width (a pointer reload resolves the stored address
//!   to whichever live allocation contains it, which is exactly `inttoptr` at
//!   the load), and, at a one-byte integer carrier, `zext` of a stored
//!   `bool` (the interpreter encodes `false` as the byte zero and `true` as
//!   the byte one) and `icmp ne c, 0` against a fresh zero for a `bool` load
//!   (it decodes a `bool` byte as nonzero; `trunc` would keep the low bit
//!   and read the byte 2 as `false`). Each conversion is exact only on a
//!   fully initialized value (the interpreter's casts and compares fault on
//!   the poison image a load of uninitialized bytes carries), so a converted
//!   store needs a value that is never poison, and a converted load needs
//!   every unconverted store of its field to store one ([`defined_values`];
//!   a read of the promoted slot counts as never poison when every value
//!   stored into the slot is, by induction over an execution of the target,
//!   where the read is the field's carrier: `defined_values_seeded`).
//!   A stored value must have exactly the store's type (the lane's type for
//!   a write-through), and no stored value may be `undef`.
//! * **A `ptr` carrier holds stable addresses.** A field carried as a `ptr`
//!   is read and written only as whole thin pointers, and every store writes
//!   an address `(A, d)` strictly inside a fresh allocation `A`
//!   ([`super::alloca_displacement`]): an `alloca`, or a pointer derived
//!   from one by copies, `ptrtoptr`s and `gep`s by non-negative constants,
//!   every step inside it. The interpreter's allocations are bump-allocated,
//!   never overlap and are never reused, so a reload of those bytes resolves
//!   to exactly `(A, d)`: the stored pointer itself (a `ptrtoptr` of it for
//!   another thin pointer type).
//! * **Parts.** A field accessed in parts is carried as the unsigned integer
//!   of its width (2, 4 or 8 bytes), and every value stored into it is never
//!   poison. A part `[d, d + w)` of an integer, `f32` or pointer of the
//!   target's width is read as `trunc(c >> 8d)` and its bits as the access
//!   type, and written as `(prev & !(M << 8d)) | (zext(bits) << 8d)`, where
//!   `prev` is the field's value reaching the store (proven like a load's)
//!   and `M` the part's all-ones: the interpreter's byte images are
//!   little-endian, so these are exactly the bytes the source reads and
//!   writes. Every value of such a field is never poison (zero, stored
//!   values, merges and joins of them), so the shifts and truncations never
//!   fault where the source did not.
//! * **Initial zeros.** A field may name a fresh value its `alloca` defines
//!   as `const 0` (an integer carrier only), inserted just after it: a read
//!   that only the `alloca` reaches reads fresh bytes, which the source
//!   reads as poison (a non-strict scalar load) or faults on; the zero
//!   refines them.
//! * **Every read has one reaching definition.** For each load, walking the
//!   CFG backward from it over every path (feasible or not), the walk meets,
//!   before the slot's `alloca` (a fresh allocation: an undefined read,
//!   unless the claimed value is the field's initial zero), the function's
//!   entry, a block without predecessors, a store of the field with another
//!   carrier value, or a redefinition of the claimed value, either a store of
//!   the field whose carrier value is the claimed one or the start of the
//!   block whose new parameter the claimed value is. The same walk, from the
//!   end of the predecessor, proves the value each normal edge passes to a
//!   new parameter, and from a part store the value it merges into. By
//!   induction over an execution, the SSA value claimed at each read is the
//!   field's bytes at that point (zero where the source's are uninitialized),
//!   so the load's result is unchanged (or refines poison). A block that
//!   gains a parameter is not the entry and is entered by no unwind edge,
//!   and every edge into it passes exactly one claimed value. The walks need
//!   no reducible CFG, but an irreducible one (a dispatch loop) is refused:
//!   the pass leaves those alone and so does the checker.
//!
//! The rewrite is a REFINEMENT: a removed store or a replaced load may be
//! undefined in the source (misaligned) where the target does nothing, and a
//! zero may stand for poison, so each counts as one. The `alloca` and its
//! derived pointers stay, unused, for dead-code elimination. The rebuilt
//! target is exactly: the initial zeros after their `alloca`; the claimed
//! parameters appended to their blocks in witness order; on every edge into
//! such a block, the claimed incoming values appended in the same order; each
//! store removed, or replaced in place by its conversion (`<cast> S value to
//! carrier` defining `converted`, preceded by `ptrtoptr S value to ptr`
//! defining `via` for a pointer type other than `ptr`, which trust-ir's
//! `ptrtoint` requires) or its merge; each load replaced in place by
//! `copy L value`, `<cast> carrier value to L` (for a pointer type other than
//! `ptr`, `inttoptr carrier value to ptr` defining `via`, then `ptrtoptr ptr
//! via to L`) or its part's extraction. Fresh values are fresh: defined and
//! used nowhere in the source, and pairwise distinct.

use std::collections::{BTreeSet, HashMap, HashSet};

use trust_ir::{BlockId, CastOp, Constant, EdgeKind, Function, ICmpOp, Inst, Module, Ty, ValueId};

use super::{Defs, MidTvError, WitnessVerdict, block_positions, round_trips, use_positions};
use crate::fsym_layout::FsymLayout;

/// One field of a promoted slot: its bytes `[offset, offset + size)`,
/// carried as an SSA value of type `carrier`. `init`, when set, is a fresh
/// value defined by `const <carrier> 0` just after the `alloca`: the field's
/// value where no store reaches (the fresh allocation's bytes, which the
/// source reads as poison; zero refines them). Additive field, pending the
/// owner's sign-off on the mid-end's witnesses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SroaField {
    pub offset: u64,
    pub size: u64,
    pub carrier: Ty,
    pub init: Option<ValueId>,
}

/// How a store into PART of a field (fewer bytes than the field, the bridge's
/// narrower writes beside a word copy) builds the field's new value: from
/// `prev`, the field's value reaching the store, and the stored value's
/// bits, through the fresh `values` in the order the checker rebuilds them
/// (the stored value's bits as the part's unsigned integer when its type is
/// another, their zero extension to the carrier, the shift amount and the
/// shift when the part is not at the field's start, the mask, the masked
/// field and the merged field, which is the store's carried value).
/// Additive, pending the owner's sign-off on the mid-end's witnesses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SroaMerge {
    pub prev: ValueId,
    pub values: Vec<ValueId>,
}

/// A store through the slot, at `(block, index)` of the SOURCE, of field
/// `field`: removed, or, when its type is not the carrier's, replaced in place
/// by the conversion of its value defining `converted`. A pointer of another
/// type than `ptr` is first cast to `ptr`, defining `via` (trust-ir's
/// `ptrtoint` takes a `ptr`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SroaStore {
    pub block: BlockId,
    pub index: usize,
    pub field: usize,
    pub converted: Option<ValueId>,
    pub via: Option<ValueId>,
    /// For a store into part of the field, how the new field value is built
    /// (`converted` is then unset). Additive, pending the owner's sign-off on
    /// the mid-end's witnesses.
    pub merge: Option<SroaMerge>,
}

/// A load through the slot, at `(block, index)` of the SOURCE, defining
/// `result`: replaced in place by `copy` or a conversion of `value`, the
/// field's carrier value on every path to it. A pointer of another type than
/// `ptr` is built as `ptr`, defining `via`, then cast to the load's type
/// (trust-ir's `inttoptr` yields a `ptr`); a `bool` read of a one-byte
/// integer carrier is the nonzero test against a fresh zero constant `via`
/// (round 15, pending the owner's sign-off).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SroaLoad {
    pub block: BlockId,
    pub index: usize,
    pub result: ValueId,
    pub field: usize,
    pub value: ValueId,
    pub via: Option<ValueId>,
    /// For a load of part of the field, the fresh values extracting it, in
    /// the order the checker rebuilds them (the shift amount and the shift
    /// when the part is not at the field's start, then the truncation to the
    /// part's unsigned integer). Additive, pending the owner's sign-off.
    pub extract: Vec<ValueId>,
}

/// The value the normal edge number `edge` (in `successor_edges` order) of
/// `pred`'s terminator passes to a new parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SroaIncoming {
    pub pred: BlockId,
    pub edge: usize,
    pub value: ValueId,
}

/// A new parameter `value` of `block`, of the carrier type of field `field`,
/// with the value every edge into `block` passes it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SroaParam {
    pub block: BlockId,
    pub field: usize,
    pub value: ValueId,
    pub incoming: Vec<SroaIncoming>,
}

/// One promoted slot: the `alloca` defining `alloca`, its fields, and the
/// rewrite of each of its accesses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SroaSlot {
    pub alloca: ValueId,
    pub fields: Vec<SroaField>,
    pub stores: Vec<SroaStore>,
    pub loads: Vec<SroaLoad>,
    pub params: Vec<SroaParam>,
}

/// Scalar replacement's claim.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SroaWitness {
    pub slots: Vec<SroaSlot>,
}

impl SroaWitness {
    /// Number of rewritten accesses.
    pub fn rewrite_count(&self) -> usize {
        self.slots
            .iter()
            .map(|s| s.stores.len() + s.loads.len())
            .sum()
    }
}

/// A thin pointer: one address word, no metadata.
fn thin_pointer(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
    )
}

/// An integer or a float wide enough to be one word of bytes in the
/// interpreter (`encode_leaf`/`decode_leaf`: its raw bits, little-endian).
fn word(ty: &Ty) -> bool {
    ty.is_integer() || matches!(ty, Ty::F32 | Ty::F64)
}

/// A one-byte integer type.
fn one_byte_int(ty: &Ty) -> bool {
    matches!(ty, Ty::I8 | Ty::U8)
}

/// The instruction that reads a value of type `from` as the same bytes of
/// type `to`: `None` for the identity, `Some(op)` for a reinterpretation, or
/// `Err` when the bytes of one are not a value of the other. A `bool`
/// stored into a one-byte integer is its `zext`: the interpreter encodes a
/// `bool` as the byte 0 or 1. The other direction is not a cast (the
/// interpreter decodes a `bool` byte as nonzero, `trunc` keeps the low bit):
/// the load rebuild handles it before calling this ([`bool_view`]).
fn reinterpretation(
    layout: &FsymLayout<'_>,
    pointer_bits: u32,
    from: &Ty,
    to: &Ty,
) -> Result<Option<CastOp>, &'static str> {
    if from == to {
        return Ok(None);
    }
    let size = |ty: &Ty| layout.size(ty).ok();
    let (Some(from_size), Some(to_size)) = (size(from), size(to)) else {
        return Err("an access type has no layout");
    };
    if from_size != to_size {
        return Err("an access is not the field's width");
    }
    let pointer_word = |ty: &Ty| ty.is_integer() && to_size * 8 == u64::from(pointer_bits);
    if *from == Ty::Bool && one_byte_int(to) {
        Ok(Some(CastOp::ZExt))
    } else if word(from) && word(to) {
        Ok(Some(CastOp::Bitcast))
    } else if thin_pointer(from) && pointer_word(to) {
        Ok(Some(CastOp::PtrToInt))
    } else if pointer_word(from) && thin_pointer(to) {
        Ok(Some(CastOp::IntToPtr))
    } else if thin_pointer(from) && thin_pointer(to) {
        Ok(Some(CastOp::PtrToPtr))
    } else {
        Err("an access type is not a reinterpretation of the carrier")
    }
}

/// Whether a load of type `ty` from a field carried as `carrier` is the
/// `bool` view of a one-byte integer: the interpreter decodes a `bool` load
/// as `byte != 0`, so the read is `icmp ne carrier, 0`.
fn bool_view(carrier: &Ty, ty: &Ty) -> bool {
    *ty == Ty::Bool && one_byte_int(carrier)
}

/// Lane `field` of the record type `ty` with the interpreter's layout: its
/// byte offset and type. The bridge's field access through a pointer reads
/// or writes exactly these bytes (the lane's `insertfield`/`extractfield`
/// over a pointer carrier, and the differential's view of them).
fn record_lane(layout: &FsymLayout<'_>, module: &Module, ty: &Ty, field: u32) -> Option<(u64, Ty)> {
    match ty {
        Ty::Struct(_) => layout
            .struct_layout(ty)
            .ok()?
            .fields
            .get(field as usize)
            .cloned(),
        Ty::Tuple(_) => layout
            .tuple_layout(ty)
            .ok()?
            .fields
            .get(field as usize)
            .cloned(),
        Ty::Array(elem, count) if u64::from(field) < *count => {
            let elem = module.ty(*elem)?.clone();
            let stride = layout.size(&elem).ok()?;
            Some((u64::from(field).checked_mul(stride)?, elem))
        }
        _ => None,
    }
}

/// A part of a field: its byte offset into the field and its width.
type Part = (u64, u64);

/// The unsigned integer type of a part of `bytes` bytes of a field.
fn part_ty(bytes: u64) -> Option<Ty> {
    match bytes {
        1 => Some(Ty::U8),
        2 => Some(Ty::U16),
        4 => Some(Ty::U32),
        _ => None,
    }
}

/// The carrier of a field read or written in parts: the unsigned integer of
/// its width.
fn composite_carrier(bytes: u64) -> Option<Ty> {
    match bytes {
        2 => Some(Ty::U16),
        4 => Some(Ty::U32),
        8 => Some(Ty::U64),
        _ => None,
    }
}

/// Whether a `bytes`-byte access of type `ty` may read or write part of a
/// field: an integer or `f32` (its bits), or a thin pointer of the target's
/// width (its address).
fn part_access(ty: &Ty, bytes: u64, pointer_bits: u32) -> bool {
    part_ty(bytes).is_some()
        && (ty.is_integer()
            || *ty == Ty::F32
            || (thin_pointer(ty) && bytes * 8 == u64::from(pointer_bits)))
}

/// A node like `template` defining `result` by `inst`.
fn node_like(template: &trust_ir::InstrNode, inst: Inst, result: ValueId) -> trust_ir::InstrNode {
    let mut node = template.clone();
    node.inst = inst;
    node.results = vec![result];
    node
}

/// The fresh values a rebuild takes in order; it refuses too few or too many.
struct Takes<'a>(std::slice::Iter<'a, ValueId>);

impl Takes<'_> {
    fn next(&mut self) -> Result<ValueId, &'static str> {
        self.0
            .next()
            .copied()
            .ok_or("a part access names too few values")
    }

    fn done(mut self) -> Result<(), &'static str> {
        match self.0.next() {
            None => Ok(()),
            Some(_) => Err("a part access names too many values"),
        }
    }
}

/// The nodes reading bytes `[d, d + w)` of the field value `value` (a
/// `carrier` integer) as `ty`, the last defining `result`. Byte images are
/// little-endian in the interpreter, so those bytes are
/// `trunc(value >> 8d)` to the part's unsigned integer, then its bits read as
/// `ty` (`bitcast`, or `inttoptr`, which resolves the address exactly as a
/// pointer load of those bytes does, through `via` for a pointer type other
/// than `ptr`).
#[allow(clippy::too_many_arguments)]
fn part_read(
    template: &trust_ir::InstrNode,
    carrier: &Ty,
    d: u64,
    w: u64,
    ty: &Ty,
    value: ValueId,
    extract: &[ValueId],
    via: Option<ValueId>,
    result: ValueId,
) -> Result<Vec<trust_ir::InstrNode>, &'static str> {
    let part = part_ty(w).ok_or("a part is not 1, 2 or 4 bytes")?;
    let mut takes = Takes(extract.iter());
    let mut nodes = Vec::new();
    let mut cur = value;
    if d > 0 {
        let k = takes.next()?;
        nodes.push(node_like(
            template,
            Inst::Const {
                ty: carrier.clone(),
                value: Constant::Int(i128::from(d * 8)),
            },
            k,
        ));
        let shifted = takes.next()?;
        nodes.push(node_like(
            template,
            Inst::BinOp {
                op: trust_ir::BinOp::LShr,
                ty: carrier.clone(),
                lhs: cur,
                rhs: k,
            },
            shifted,
        ));
        cur = shifted;
    }
    let truncated = takes.next()?;
    nodes.push(node_like(
        template,
        Inst::Cast {
            op: CastOp::Trunc,
            src_ty: carrier.clone(),
            dst_ty: part.clone(),
            operand: cur,
        },
        truncated,
    ));
    takes.done()?;
    let cast = |op, src_ty: &Ty, dst_ty: &Ty, operand| Inst::Cast {
        op,
        src_ty: src_ty.clone(),
        dst_ty: dst_ty.clone(),
        operand,
    };
    let needs_via = thin_pointer(ty) && *ty != Ty::Ptr;
    if needs_via != via.is_some() {
        return Err("a part load's pointer cast is not the one its type needs");
    }
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
        let pointer = via.unwrap_or(result);
        nodes.push(node_like(
            template,
            cast(CastOp::IntToPtr, &part, &Ty::Ptr, truncated),
            pointer,
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
    Ok(nodes)
}

/// The nodes writing `value` (of type `ty`) over bytes `[d, d + w)` of the
/// field value `prev` (a `carrier` integer of `size` bytes), and the merged
/// field value they define: `(prev & !(M << 8d)) | (zext(bits) << 8d)` with
/// `M` the part's all-ones, `bits` the value's bytes as the part's unsigned
/// integer (`bitcast`, or `ptrtoint` of the address, through `via` for a
/// pointer type other than `ptr`). The value must never be poison (a
/// conversion inspects it), as must `prev`.
#[allow(clippy::too_many_arguments)]
fn part_write(
    template: &trust_ir::InstrNode,
    carrier: &Ty,
    size: u64,
    d: u64,
    w: u64,
    ty: &Ty,
    value: ValueId,
    merge: &SroaMerge,
    via: Option<ValueId>,
) -> Result<(Vec<trust_ir::InstrNode>, ValueId), &'static str> {
    let part = part_ty(w).ok_or("a part is not 1, 2 or 4 bytes")?;
    let mut takes = Takes(merge.values.iter());
    let mut nodes = Vec::new();
    let cast = |op, src_ty: &Ty, dst_ty: &Ty, operand| Inst::Cast {
        op,
        src_ty: src_ty.clone(),
        dst_ty: dst_ty.clone(),
        operand,
    };
    let needs_via = thin_pointer(ty) && *ty != Ty::Ptr;
    if needs_via != via.is_some() {
        return Err("a part store's pointer cast is not the one its type needs");
    }
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
            let bits = takes.next()?;
            nodes.push(node_like(
                template,
                cast(CastOp::PtrToInt, &Ty::Ptr, &part, cur),
                bits,
            ));
            cur = bits;
        } else {
            let bits = takes.next()?;
            nodes.push(node_like(
                template,
                cast(CastOp::Bitcast, ty, &part, cur),
                bits,
            ));
            cur = bits;
        }
    }
    let widened = takes.next()?;
    nodes.push(node_like(
        template,
        cast(CastOp::ZExt, &part, carrier, cur),
        widened,
    ));
    cur = widened;
    let constant = |k: u128| Inst::Const {
        ty: carrier.clone(),
        value: Constant::Int(k as i128),
    };
    let binop = |op, lhs, rhs| Inst::BinOp {
        op,
        ty: carrier.clone(),
        lhs,
        rhs,
    };
    if d > 0 {
        let k = takes.next()?;
        nodes.push(node_like(template, constant(u128::from(d * 8)), k));
        let shifted = takes.next()?;
        nodes.push(node_like(
            template,
            binop(trust_ir::BinOp::Shl, cur, k),
            shifted,
        ));
        cur = shifted;
    }
    let all = (1u128 << (size * 8)) - 1;
    let mask = all & !(((1u128 << (w * 8)) - 1) << (d * 8));
    let m = takes.next()?;
    nodes.push(node_like(template, constant(mask), m));
    let masked = takes.next()?;
    nodes.push(node_like(
        template,
        binop(trust_ir::BinOp::And, merge.prev, m),
        masked,
    ));
    let merged = takes.next()?;
    nodes.push(node_like(
        template,
        binop(trust_ir::BinOp::Or, masked, cur),
        merged,
    ));
    takes.done()?;
    Ok((nodes, merged))
}

/// The values of `func` that are never the poison image of uninitialized
/// bytes: the greatest set closed under the interpreter's rules. Arithmetic,
/// comparisons, casts and address computations fault on a poison operand and
/// return a full value; a scalar constant, a global's address, `null` and an
/// allocation are full. A `copy` is full when its operand is, a `select`
/// when both arms are, and a block parameter when every edge into its block
/// passes a full value (an entry parameter also receives the caller's
/// argument, which a call never passes poisoned; a landing pad's parameters
/// are the unwinder's). A call's results are full when the callee has a body
/// (its `return` is checked against the signature, which refuses poison).
/// Loads, `undef`, a declaration's or an indirect call's results and every
/// other form may carry poison and are excluded.
pub(super) fn defined_values(module: &Module, func: &Function) -> HashSet<ValueId> {
    defined_values_seeded(module, func, &[])
}

/// [`defined_values`] with `seeds`: each `(value, operands)` is full when
/// every one of its operands is, as a `select` over them would be. The
/// scalar-replacement check seeds the reads of the slot it promotes with
/// every value stored into the slot: in the target such a read is the
/// field's carrier (a `copy`, a reinterpretation or a part extraction of
/// it), and the carrier only ever holds the initial zero, the stored
/// values (converted) and merges of them, so by induction over an
/// execution it is never poison when no stored value is, even where a
/// stored value is itself computed from a read of the slot (a loop's
/// update of an iterator field).
fn defined_values_seeded(
    module: &Module,
    func: &Function,
    seeds: &[(ValueId, Vec<ValueId>)],
) -> HashSet<ValueId> {
    let mut defined: HashSet<ValueId> = HashSet::new();
    let mut copies: Vec<(ValueId, Vec<ValueId>)> = seeds.to_vec();
    for block in &func.blocks {
        for node in &block.body {
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
                // A return is checked against the signature, which refuses a
                // poison value, when the callee has a body; a declaration's
                // results come from the host.
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
                        copies.push((*r, vec![*operand]));
                    }
                }
                Inst::Select {
                    then_val, else_val, ..
                } => {
                    if let [r] = node.results.as_slice() {
                        copies.push((*r, vec![*then_val, *else_val]));
                    }
                }
                _ => {}
            }
        }
    }
    // Block parameters: the arguments each edge passes, by position.
    let positions = block_positions(func);
    let mut incoming: Vec<Vec<Option<&[ValueId]>>> = vec![Vec::new(); func.blocks.len()];
    for block in &func.blocks {
        if let Some(last) = block.body.last() {
            for edge in last.inst.successor_edges() {
                if let Some(&ti) = positions.get(&edge.target) {
                    incoming[ti].push(match edge.kind {
                        EdgeKind::Normal => Some(edge.args),
                        EdgeKind::Unwind => None,
                    });
                }
            }
        }
    }
    let mut params: Vec<(ValueId, usize, usize)> = Vec::new();
    for (bi, block) in func.blocks.iter().enumerate() {
        for (pi, (value, _)) in block.params.iter().enumerate() {
            params.push((*value, bi, pi));
        }
    }
    // Optimistic start: every candidate full, then remove until stable.
    defined.extend(copies.iter().map(|(r, _)| *r));
    defined.extend(params.iter().map(|(v, ..)| *v));
    loop {
        let mut changed = false;
        for (r, operands) in &copies {
            if defined.contains(r) && operands.iter().any(|o| !defined.contains(o)) {
                defined.remove(r);
                changed = true;
            }
        }
        for &(value, bi, pi) in &params {
            if !defined.contains(&value) {
                continue;
            }
            let full = incoming[bi].iter().all(|edge| {
                edge.is_some_and(|args| args.get(pi).is_some_and(|a| defined.contains(a)))
            });
            if !full {
                defined.remove(&value);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    defined
}

/// Whether `func`'s CFG is reducible: every edge that retreats in a reverse
/// postorder from the entry goes to a block that dominates its source.
/// This module's own walk (dominators by the iterative data-flow).
pub(super) fn reducible(func: &Function) -> bool {
    let positions = block_positions(func);
    let Some(&entry) = positions.get(&func.entry) else {
        return false;
    };
    let succs: Vec<Vec<usize>> = func
        .blocks
        .iter()
        .map(|b| {
            b.body
                .last()
                .map(|n| n.inst.successor_edges())
                .unwrap_or_default()
                .iter()
                .filter_map(|e| positions.get(&e.target).copied())
                .collect()
        })
        .collect();
    // Reverse postorder.
    let n = func.blocks.len();
    let mut seen = vec![false; n];
    let mut post = Vec::with_capacity(n);
    let mut stack = vec![(entry, 0usize)];
    seen[entry] = true;
    while let Some((b, next)) = stack.last_mut() {
        let b = *b;
        if let Some(&s) = succs[b].get(*next) {
            *next += 1;
            if !seen[s] {
                seen[s] = true;
                stack.push((s, 0));
            }
        } else {
            post.push(b);
            stack.pop();
        }
    }
    let rpo: Vec<usize> = post.into_iter().rev().collect();
    let mut rank = vec![usize::MAX; n];
    for (i, &b) in rpo.iter().enumerate() {
        rank[b] = i;
    }
    let mut preds = vec![Vec::new(); n];
    for (b, list) in succs.iter().enumerate() {
        for &s in list {
            preds[s].push(b);
        }
    }
    // Immediate dominators (Cooper/Harvey/Kennedy), reachable blocks only.
    let mut idom = vec![usize::MAX; n];
    idom[entry] = entry;
    let mut changed = true;
    while changed {
        changed = false;
        for &b in rpo.iter().skip(1) {
            let mut new = usize::MAX;
            for &p in &preds[b] {
                if idom[p] == usize::MAX {
                    continue;
                }
                new = if new == usize::MAX {
                    p
                } else {
                    let (mut x, mut y) = (p, new);
                    while x != y {
                        while rank[x] > rank[y] {
                            x = idom[x];
                        }
                        while rank[y] > rank[x] {
                            y = idom[y];
                        }
                    }
                    x
                };
            }
            if new != usize::MAX && idom[b] != new {
                idom[b] = new;
                changed = true;
            }
        }
    }
    let dominates = |a: usize, mut b: usize| loop {
        if a == b {
            return true;
        }
        if idom[b] == b || idom[b] == usize::MAX {
            return false;
        }
        b = idom[b];
    };
    for (b, list) in succs.iter().enumerate() {
        if rank[b] == usize::MAX {
            continue;
        }
        for &s in list {
            if rank[s] <= rank[b] && !dominates(s, b) {
                return false;
            }
        }
    }
    true
}

/// One access through a slot: `(block position, node index)`, byte offset,
/// whether it is a store, its type (a load's or store's, or the lane's for
/// the bridge's field access through a pointer) and the stored value.
#[derive(Debug, Clone)]
struct Access {
    at: (usize, usize),
    offset: u64,
    store: bool,
    ty: Ty,
    value: Option<ValueId>,
}

/// The slot of `alloca` (module docs): its size, the position of the
/// `alloca`, and its accesses, or why it is not one.
fn slot_of(
    module: &Module,
    source: &Function,
    index: &Defs<'_>,
    uses: &HashMap<ValueId, Vec<(usize, usize)>>,
    defs: &HashMap<ValueId, (usize, usize)>,
    alloca: ValueId,
) -> Result<((usize, usize), Vec<Access>), &'static str> {
    let layout = FsymLayout::new(module);
    let at = *defs.get(&alloca).ok_or("not defined by an instruction")?;
    let node = &source.blocks[at.0].body[at.1];
    let Inst::Alloca { ty, count, .. } = &node.inst else {
        return Err("not an alloca");
    };
    // Count-free, or counted by an integer constant `k >= 1`: `size(T) * k`
    // bytes, allocated afresh at each execution like a count-free one.
    let count = super::alloca_count(index, *count)
        .ok_or("the allocation's count is not a positive constant")?;
    if node.results != [alloca] {
        return Err("not a single-result alloca");
    }
    let size = layout
        .size(ty)
        .ok()
        .and_then(|s| s.checked_mul(count))
        .ok_or("the allocation has no layout")?;
    if size == 0 {
        return Err("the allocation is empty");
    }
    let constant = |v: ValueId| match index.inst(v) {
        Some(Inst::Const {
            ty,
            value: Constant::Int(k),
        }) if ty.is_integer() => u64::try_from(*k).ok(),
        _ => None,
    };
    // Each derived pointer: its offset into the slot.
    let mut pointers: HashMap<ValueId, u64> = HashMap::from([(alloca, 0)]);
    let mut pending = vec![alloca];
    let mut accesses: Vec<Access> = Vec::new();
    while let Some(pointer) = pending.pop() {
        let offset = pointers[&pointer];
        let mut access = |at, at_offset: u64, ty: &Ty, value: Option<ValueId>| {
            let width = layout.size(ty).map_err(|_| "an access has no layout")?;
            if width == 0 || at_offset.checked_add(width).is_none_or(|end| end > size) {
                return Err("an access leaves the allocation");
            }
            accesses.push(Access {
                at,
                offset: at_offset,
                store: value.is_some(),
                ty: ty.clone(),
                value,
            });
            Ok(())
        };
        for &(bi, ni) in uses.get(&pointer).map_or(&[][..], Vec::as_slice) {
            let node = &source.blocks[bi].body[ni];
            let derived = match &node.inst {
                Inst::Load {
                    ty,
                    ptr,
                    volatile: false,
                    ..
                } if *ptr == pointer => {
                    access((bi, ni), offset, ty, None)?;
                    None
                }
                Inst::Store {
                    ty,
                    ptr,
                    value,
                    volatile: false,
                    ..
                } if *ptr == pointer && !pointers.contains_key(value) => {
                    access((bi, ni), offset, ty, Some(*value))?;
                    None
                }
                // The bridge's write-through form: lane `field` of the record
                // `ty` is stored through the pointer. Its result is unused:
                // the lane types it as the record (an access through it is
                // no access through the slot), so the store is all it does.
                Inst::InsertField {
                    ty,
                    aggregate,
                    field,
                    value,
                } if *aggregate == pointer && !pointers.contains_key(value) => {
                    if node.results.iter().any(|r| uses.contains_key(r)) {
                        return Err("a write-through's result is used");
                    }
                    let (lane_offset, lane_ty) = record_lane(&layout, module, ty, *field)
                        .ok_or("a field written through the address has no lane")?;
                    let at_offset = offset
                        .checked_add(lane_offset)
                        .ok_or("an access leaves the allocation")?;
                    access((bi, ni), at_offset, &lane_ty, Some(*value))?;
                    None
                }
                // The read-through form: lane `field` of the record `ty`
                // loaded through the pointer.
                Inst::ExtractField {
                    ty,
                    aggregate,
                    field,
                } if *aggregate == pointer => {
                    let (lane_offset, lane_ty) = record_lane(&layout, module, ty, *field)
                        .ok_or("a field read through the address has no lane")?;
                    let at_offset = offset
                        .checked_add(lane_offset)
                        .ok_or("an access leaves the allocation")?;
                    access((bi, ni), at_offset, &lane_ty, None)?;
                    None
                }
                Inst::GEP {
                    pointee_ty,
                    base,
                    indices,
                    ..
                } if *base == pointer && !indices.contains(&pointer) => {
                    let elem = layout
                        .size(pointee_ty)
                        .map_err(|_| "an offset's element has no layout")?;
                    let mut delta: u64 = 0;
                    for k in indices {
                        let k = constant(*k).ok_or("the address is offset by a non-constant")?;
                        delta = elem
                            .checked_mul(k)
                            .and_then(|d| delta.checked_add(d))
                            .ok_or("the address offset overflows")?;
                    }
                    Some(
                        offset
                            .checked_add(delta)
                            .ok_or("the address offset overflows")?,
                    )
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
                _ => return Err("the address is used other than by a plain access or offset"),
            };
            if let Some(derived) = derived {
                if derived >= size {
                    return Err("an offset address leaves the allocation");
                }
                let [r] = node.results.as_slice() else {
                    return Err("an offset address is not one value");
                };
                match pointers.insert(*r, derived) {
                    None => pending.push(*r),
                    Some(old) if old == derived => {}
                    Some(_) => return Err("an offset address is defined twice"),
                }
            }
        }
    }
    Ok((at, accesses))
}

/// A node's verdict for a walk: `Ok` the claimed definition, `Err` a
/// failure.
type Event = (usize, Result<(), &'static str>);

/// What one walk key (slot, field, value) has established: each block's
/// events, collected once, and the blocks proven from their end (every
/// backward path from the end meets the claimed definition first). A failed
/// walk discards the key's state.
#[derive(Debug, Default)]
struct Walks {
    events: HashMap<usize, Vec<Event>>,
    proven: HashSet<usize>,
}

/// The facts one slot's walks read.
struct SlotFacts<'a> {
    alloca_at: (usize, usize),
    /// Per field, the fresh value the `alloca` defines it as (`const 0`).
    init: Vec<Option<ValueId>>,
    /// Stores per block: `(node, field, carrier value)`.
    stores: HashMap<usize, Vec<(usize, usize, ValueId)>>,
    /// The blocks with a new parameter, per field: block position -> value.
    params: HashMap<(usize, usize), ValueId>,
    preds: &'a [Vec<usize>],
    entry: usize,
    source: &'a Function,
    value_defs: &'a HashMap<ValueId, Vec<(usize, usize)>>,
}

impl SlotFacts<'_> {
    fn block_events(&self, field: usize, value: ValueId, bi: usize) -> Vec<Event> {
        let mut events: Vec<Event> = Vec::new();
        if self.alloca_at.0 == bi {
            events.push((
                self.alloca_at.1,
                if self.init.get(field).copied().flatten() == Some(value) {
                    Ok(())
                } else {
                    Err("the slot is allocated afresh on a path to the read (an undefined read)")
                },
            ));
        }
        for &(ni, f, carried) in self.stores.get(&bi).map_or(&[][..], Vec::as_slice) {
            if f == field {
                events.push((
                    ni,
                    if carried == value {
                        Ok(())
                    } else {
                        Err("another store of the field reaches the read")
                    },
                ));
            }
        }
        for &(db, dn) in self.value_defs.get(&value).map_or(&[][..], Vec::as_slice) {
            if db == bi {
                events.push((
                    dn,
                    Err("the carried value is redefined on a path to the read"),
                ));
            }
        }
        // At one node a failure sorts first and wins.
        events.sort_by_key(|&(ni, verdict)| (ni, verdict.is_ok()));
        events.dedup_by_key(|event| event.0);
        events
    }

    /// Whether every backward path from node `at.1` of block `at.0` (the
    /// whole block when `at.1` is its length) meets the claimed definition of
    /// `value` for `field` first.
    fn reaches(
        &self,
        walks: &mut HashMap<(usize, ValueId), Walks>,
        field: usize,
        value: ValueId,
        at: (usize, usize),
    ) -> Result<(), &'static str> {
        let key = (field, value);
        let outcome = {
            let state = walks.entry(key).or_default();
            let at_start = |bi: usize, pending: &mut Vec<usize>| -> Result<bool, &'static str> {
                if self.params.get(&(bi, field)) == Some(&value) {
                    return Ok(true);
                }
                if bi == self.entry {
                    return Err("a path from the function entry reaches the read undefined");
                }
                if self.source.blocks[bi]
                    .params
                    .iter()
                    .any(|(v, _)| *v == value)
                {
                    return Err("the carried value is redefined on a path to the read");
                }
                if self.preds[bi].is_empty() {
                    return Err("a block without predecessors reaches the read");
                }
                pending.extend(self.preds[bi].iter().copied());
                Ok(false)
            };
            let (lb, li) = at;
            let here = state
                .events
                .entry(lb)
                .or_insert_with(|| self.block_events(field, value, lb))
                .clone();
            let before = here.partition_point(|&(ni, _)| ni < li);
            match before.checked_sub(1).map(|i| here[i].1) {
                Some(verdict) => verdict,
                None => (|| {
                    let mut pending = Vec::new();
                    at_start(lb, &mut pending)?;
                    while let Some(bi) = pending.pop() {
                        if !state.proven.insert(bi) {
                            continue;
                        }
                        let last = state
                            .events
                            .entry(bi)
                            .or_insert_with(|| self.block_events(field, value, bi))
                            .last()
                            .map(|e| e.1);
                        match last {
                            Some(verdict) => verdict?,
                            None => {
                                at_start(bi, &mut pending)?;
                            }
                        }
                    }
                    Ok(())
                })(),
            }
        };
        if outcome.is_err() {
            walks.remove(&key);
        }
        outcome
    }
}

/// The type of a stored value: this module's typing, or the declared result
/// type of the operation defining it: a unary operation's (its operand type),
/// an overflow operation's (its type, then `bool`), a call's (its signature's
/// returns, one per result).
fn stored_type(
    module: &Module,
    source: &Function,
    index: &Defs<'_>,
    defs: &HashMap<ValueId, (usize, usize)>,
    value: ValueId,
) -> Option<Ty> {
    if let Some(ty) = index.value_type(value) {
        return Some(ty);
    }
    let &(bi, ni) = defs.get(&value)?;
    let node = &source.blocks[bi].body[ni];
    let returns: Vec<Ty> = match &node.inst {
        Inst::UnOp { ty, .. } => vec![ty.clone()],
        Inst::Overflow { ty, .. } => vec![ty.clone(), Ty::Bool],
        Inst::Call { callee, .. } => module
            .function_by_id(*callee)
            .and_then(|f| module.func_type(f.ty))?
            .returns
            .clone(),
        Inst::CallIndirect { sig, .. } => module.func_type(*sig)?.returns.clone(),
        _ => return None,
    };
    if returns.len() != node.results.len() {
        return None;
    }
    let position = node.results.iter().position(|r| *r == value)?;
    returns.get(position).cloned()
}

/// The mutable argument list of the `edge`-th normal edge of `inst`, in
/// `successor_edges` order.
pub(super) fn edge_args_mut(inst: &mut Inst, edge: usize) -> Option<&mut Vec<ValueId>> {
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
        } => {
            if edge < cases.len() {
                Some(&mut cases[edge].args)
            } else if edge == cases.len() {
                Some(default_args)
            } else {
                None
            }
        }
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

pub(super) fn rebuild_sroa(
    module: &Module,
    pointer_bits: u32,
    source: &Function,
    witness: &SroaWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let layout = FsymLayout::new(module);
    let index = Defs::of(source);
    let uses = use_positions(source);
    let positions = block_positions(source);
    let entry = *positions
        .get(&source.entry)
        .ok_or(MidTvError::TargetDiffers {
            detail: "the source has no entry block".to_string(),
        })?;
    let mut defs: HashMap<ValueId, (usize, usize)> = HashMap::new();
    let mut value_defs: HashMap<ValueId, Vec<(usize, usize)>> = HashMap::new();
    let mut known: HashSet<ValueId> = HashSet::new();
    for (bi, block) in source.blocks.iter().enumerate() {
        known.extend(block.params.iter().map(|(v, _)| *v));
        for (ni, node) in block.body.iter().enumerate() {
            for r in &node.results {
                defs.entry(*r).or_insert((bi, ni));
                value_defs.entry(*r).or_default().push((bi, ni));
                known.insert(*r);
            }
            node.inst.visit_value_operands(|v| {
                known.insert(v);
            });
        }
    }
    // Every edge into each block: (predecessor, edge number, kind).
    let mut into: Vec<Vec<(usize, usize, EdgeKind)>> = vec![Vec::new(); source.blocks.len()];
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); source.blocks.len()];
    for (bi, block) in source.blocks.iter().enumerate() {
        if let Some(last) = block.body.last() {
            for (ei, edge) in last.inst.successor_edges().iter().enumerate() {
                if let Some(&ti) = positions.get(&edge.target) {
                    into[ti].push((bi, ei, edge.kind));
                    preds[ti].push(bi);
                }
            }
        }
    }
    let unscalarizable =
        |alloca: ValueId, why: &'static str| MidTvError::NotScalarizable { alloca, why };
    if let Some(slot) = witness.slots.first()
        && !reducible(source)
    {
        return Err(unscalarizable(
            slot.alloca,
            "the CFG is irreducible (a dispatch loop)",
        ));
    }
    let defined = defined_values(module, source);
    let mut fresh_seen: HashSet<ValueId> = HashSet::new();
    let mut fresh = |v: ValueId| !known.contains(&v) && fresh_seen.insert(v);
    let mut claimed_slots = HashSet::new();
    let mut expected = source.clone();
    // (block position, node index) -> replacement node (`None`: removed).
    let mut replaced: HashMap<(usize, usize), Vec<trust_ir::InstrNode>> = HashMap::new();
    let mut new_params: Vec<(usize, ValueId, Ty)> = Vec::new();
    let mut edge_values: Vec<((usize, usize), ValueId)> = Vec::new();
    let mut rewrites = 0usize;
    for slot in &witness.slots {
        let alloca = slot.alloca;
        let bad = |why| unscalarizable(alloca, why);
        if !claimed_slots.insert(alloca) {
            return Err(bad("the slot is claimed twice"));
        }
        let (alloca_at, accesses) = slot_of(module, source, &index, &uses, &defs, alloca)
            .map_err(|why| MidTvError::SlotObservable { slot: alloca, why })?;
        // The slot's reads are full when every value stored into it is
        // (`defined_values_seeded`).
        let stored_into: Vec<ValueId> = accesses
            .iter()
            .filter(|a| a.store)
            .filter_map(|a| a.value)
            .collect();
        let seeds: Vec<(ValueId, Vec<ValueId>)> = accesses
            .iter()
            .filter(|a| !a.store)
            .filter_map(
                |a| match source.blocks[a.at.0].body[a.at.1].results.as_slice() {
                    [read] => Some((*read, stored_into.clone())),
                    _ => None,
                },
            )
            .collect();
        let slot_defined = if seeds.is_empty() {
            None
        } else {
            Some(defined_values_seeded(module, source, &seeds))
        };
        let defined = slot_defined.as_ref().unwrap_or(&defined);
        // The fields: disjoint, each the width of its carrier, a carrier a
        // reload returns exactly; an initial value is a fresh integer zero.
        let mut sorted: Vec<(u64, u64)> = Vec::new();
        let template = source.blocks[alloca_at.0].body[alloca_at.1].clone();
        let mut after_alloca = vec![template.clone()];
        for field in &slot.fields {
            // A `ptr` carrier is admitted below only for a field accessed as
            // thin pointers alone whose every store writes a stable address.
            if !round_trips(&field.carrier) && field.carrier != Ty::Ptr {
                return Err(bad(
                    "a field's carrier is not a type a reload returns exactly",
                ));
            }
            if layout.size(&field.carrier).ok() != Some(field.size) || field.size == 0 {
                return Err(bad("a field's carrier is not the field's width"));
            }
            if let Some(init) = field.init {
                if !field.carrier.is_integer() {
                    return Err(bad("an initial value is not an integer zero"));
                }
                if !fresh(init) {
                    return Err(bad("an initial value is not a fresh value"));
                }
                after_alloca.push(node_like(
                    &template,
                    Inst::Const {
                        ty: field.carrier.clone(),
                        value: Constant::Int(0),
                    },
                    init,
                ));
            }
            sorted.push((field.offset, field.size));
        }
        sorted.sort_unstable();
        if sorted
            .windows(2)
            .any(|w| w[0].0.saturating_add(w[0].1) > w[1].0)
        {
            return Err(bad("two fields overlap"));
        }
        if after_alloca.len() > 1 {
            replaced.insert(alloca_at, after_alloca);
        }
        // Each access lies in one field: all of it (a whole access), or part
        // of it. A field accessed in parts is carried as the unsigned integer
        // of its width, and every store into it writes a value never poison
        // (its bytes are shifted and masked); a `ptr`-carried field is read
        // and written as whole thin pointers only (an integer access would
        // resolve, or observe, the address at another time than the source's
        // reload).
        let width = |access: &Access| layout.size(&access.ty).ok();
        let containing = |access: &Access| {
            let w = width(access)?;
            slot.fields.iter().position(|f| {
                f.offset <= access.offset
                    && access
                        .offset
                        .checked_add(w)
                        .is_some_and(|end| end <= f.offset + f.size)
            })
        };
        let mut composite = vec![false; slot.fields.len()];
        for access in &accesses {
            let Some(fi) = containing(access) else {
                continue;
            };
            let f = &slot.fields[fi];
            let whole = f.offset == access.offset && width(access) == Some(f.size);
            if f.carrier == Ty::Ptr && !(whole && thin_pointer(&access.ty)) {
                return Err(bad("a pointer-carried field is accessed as a non-pointer"));
            }
            composite[fi] |= !whole;
        }
        for (fi, f) in slot.fields.iter().enumerate() {
            if composite[fi] && composite_carrier(f.size).as_ref() != Some(&f.carrier) {
                return Err(bad(
                    "a field accessed in parts is not carried as an unsigned integer of 2, 4 or 8 bytes",
                ));
            }
        }
        // The claimed accesses are exactly the slot's, each of one field.
        let derived: HashMap<(usize, usize), &Access> =
            accesses.iter().map(|a| (a.at, a)).collect();
        let mut claimed: HashSet<(usize, usize)> = HashSet::new();
        let at_of = |block: BlockId, index_in: usize| {
            positions
                .get(&block)
                .map(|&bi| (bi, index_in))
                .filter(|at| derived.contains_key(at))
        };
        // The claimed field of an access: `(field, part)` with `part` the
        // access's byte offset into the field and its width when it does not
        // cover the whole field.
        let field_of = |field: usize,
                        access: &Access|
         -> Result<(&SroaField, Option<Part>), MidTvError> {
            let f = slot
                .fields
                .get(field)
                .ok_or(bad("an access names no field"))?;
            let w = width(access).ok_or(bad("an access has no layout"))?;
            if f.offset == access.offset && f.size == w {
                return Ok((f, None));
            }
            if !composite[field]
                || access.offset < f.offset
                || access.offset + w > f.offset + f.size
            {
                return Err(bad(
                    "an access does not cover exactly its field (a mixed width or a partial overlap)",
                ));
            }
            if !part_access(&access.ty, w, pointer_bits) {
                return Err(bad(
                    "a part of a field is accessed as a type other than an integer, an f32 or a pointer",
                ));
            }
            Ok((f, Some((access.offset - f.offset, w))))
        };
        // Per field: whether every unconverted store stores a full value.
        let mut plain_full: Vec<bool> = vec![true; slot.fields.len()];
        let mut stores: HashMap<usize, Vec<(usize, usize, ValueId)>> = HashMap::new();
        // The field values read by stores into part of a field: proven like
        // a load's once the walks' facts exist.
        let mut part_reads: Vec<(usize, ValueId, (usize, usize))> = Vec::new();
        for store in &slot.stores {
            let at = at_of(store.block, store.index)
                .ok_or(bad("a claimed store is not an access of the slot"))?;
            let access = derived[&at];
            if !access.store || !claimed.insert(at) {
                return Err(bad(
                    "a claimed store is not a store of the slot, or is claimed twice",
                ));
            }
            let (Some(value), ty) = (access.value.as_ref(), &access.ty) else {
                return Err(bad("a claimed store is not a store"));
            };
            let (field, part) = field_of(store.field, access)?;
            if field.carrier == Ty::Ptr {
                // The stored address lies strictly inside a fresh allocation,
                // `(A, d)` with `d < size(A)`: a reload of its bytes resolves
                // to exactly `(A, d)` (allocations are bump-allocated, never
                // overlap and are never reused), so it IS the stored pointer.
                super::alloca_displacement(&layout, &index, *value).map_err(|_| {
                    bad("a pointer-carried field stores an address not inside a fresh allocation")
                })?;
            }
            if matches!(index.inst(*value), Some(Inst::Undef { .. })) {
                return Err(bad("a store writes undef"));
            }
            if stored_type(module, source, &index, &defs, *value).as_ref() != Some(ty) {
                return Err(bad(
                    "a stored value's type is not the store's (or is unknown)",
                ));
            }
            if composite[store.field] && !defined.contains(value) {
                return Err(bad(
                    "a store into a field accessed in parts may write poison",
                ));
            }
            let template = &source.blocks[at.0].body[at.1];
            let carried = match part {
                Some((d, w)) => {
                    let merge = store
                        .merge
                        .as_ref()
                        .ok_or(bad("a store into part of a field names no merge"))?;
                    if store.converted.is_some() {
                        return Err(bad("a store into part of a field claims a conversion"));
                    }
                    if !merge.values.iter().all(|v| fresh(*v))
                        || store.via.is_some_and(|via| !fresh(via))
                    {
                        return Err(bad("a part store's value is not a fresh value"));
                    }
                    let (nodes, merged) = part_write(
                        template,
                        &field.carrier,
                        field.size,
                        d,
                        w,
                        ty,
                        *value,
                        merge,
                        store.via,
                    )
                    .map_err(bad)?;
                    part_reads.push((store.field, merge.prev, at));
                    replaced.insert(at, nodes);
                    merged
                }
                None => {
                    if store.merge.is_some() {
                        return Err(bad("a store of a whole field names a merge"));
                    }
                    let conversion =
                        reinterpretation(&layout, pointer_bits, ty, &field.carrier).map_err(bad)?;
                    if conversion == Some(CastOp::PtrToPtr) && field.carrier != Ty::Ptr {
                        return Err(bad("a pointer view of a field not carried as a pointer"));
                    }
                    // `ptrtoint` takes a `ptr`: another pointer type is cast
                    // first.
                    let needs_via = conversion == Some(CastOp::PtrToInt) && *ty != Ty::Ptr;
                    if needs_via != store.via.is_some() {
                        return Err(bad("a store's pointer cast is not the one its type needs"));
                    }
                    match (conversion, store.converted) {
                        (None, None) => {
                            if !defined.contains(value) {
                                plain_full[store.field] = false;
                            }
                            *value
                        }
                        (Some(op), Some(converted)) => {
                            if !defined.contains(value) {
                                return Err(bad(
                                    "a converted store's value may be poison (a conversion inspects it)",
                                ));
                            }
                            if !fresh(converted) || store.via.is_some_and(|via| !fresh(via)) {
                                return Err(bad("a conversion's result is not a fresh value"));
                            }
                            let cast = |op, src_ty: &Ty, dst_ty: &Ty, operand, result| {
                                node_like(
                                    template,
                                    Inst::Cast {
                                        op,
                                        src_ty: src_ty.clone(),
                                        dst_ty: dst_ty.clone(),
                                        operand,
                                    },
                                    result,
                                )
                            };
                            let nodes = match store.via {
                                None => vec![cast(op, ty, &field.carrier, *value, converted)],
                                Some(via) => vec![
                                    cast(CastOp::PtrToPtr, ty, &Ty::Ptr, *value, via),
                                    cast(op, &Ty::Ptr, &field.carrier, via, converted),
                                ],
                            };
                            replaced.insert(at, nodes);
                            converted
                        }
                        _ => {
                            return Err(bad("a store's conversion is not the one its types need"));
                        }
                    }
                }
            };
            replaced.entry(at).or_default();
            stores
                .entry(at.0)
                .or_default()
                .push((at.1, store.field, carried));
            rewrites += 1;
        }
        for list in stores.values_mut() {
            list.sort_unstable_by_key(|s| s.0);
        }
        // The new parameters.
        let mut params: HashMap<(usize, usize), ValueId> = HashMap::new();
        for param in &slot.params {
            let bi = *positions
                .get(&param.block)
                .ok_or(bad("a parameter's block is not in the function"))?;
            let field = slot
                .fields
                .get(param.field)
                .ok_or(bad("a parameter names no field"))?;
            if bi == entry {
                return Err(bad("the entry block gains a parameter"));
            }
            if !fresh(param.value) || params.insert((bi, param.field), param.value).is_some() {
                return Err(bad(
                    "a parameter is not a fresh value, or a block gains two for one field",
                ));
            }
            new_params.push((bi, param.value, field.carrier.clone()));
        }
        let facts = SlotFacts {
            alloca_at,
            init: slot.fields.iter().map(|f| f.init).collect(),
            stores,
            params,
            preds: &preds,
            entry,
            source,
            value_defs: &value_defs,
        };
        let mut walks: HashMap<(usize, ValueId), Walks> = HashMap::new();
        // Each edge into a parameter's block passes its reaching definition.
        for param in &slot.params {
            let bi = positions[&param.block];
            let mut passed: BTreeSet<(usize, usize)> = BTreeSet::new();
            for incoming in &param.incoming {
                let pi = *positions
                    .get(&incoming.pred)
                    .ok_or(bad("an incoming edge's block is not in the function"))?;
                if !into[bi].contains(&(pi, incoming.edge, EdgeKind::Normal))
                    || !passed.insert((pi, incoming.edge))
                {
                    return Err(bad(
                        "an incoming value names no normal edge into the block, or one twice",
                    ));
                }
                facts
                    .reaches(
                        &mut walks,
                        param.field,
                        incoming.value,
                        (pi, source.blocks[pi].body.len()),
                    )
                    .map_err(|why| MidTvError::NoUniqueReachingStore {
                        load: param.value,
                        why,
                    })?;
                edge_values.push(((pi, incoming.edge), incoming.value));
            }
            if into[bi]
                .iter()
                .any(|&(pi, ei, kind)| kind == EdgeKind::Unwind || !passed.contains(&(pi, ei)))
            {
                return Err(bad(
                    "an edge into a parameter's block passes no value (or unwinds)",
                ));
            }
        }
        // A store into part of a field reads the field's value there.
        for (field, prev, at) in part_reads {
            facts
                .reaches(&mut walks, field, prev, at)
                .map_err(|why| MidTvError::NoUniqueReachingStore { load: prev, why })?;
        }
        for load in &slot.loads {
            let at = at_of(load.block, load.index)
                .ok_or(bad("a claimed load is not an access of the slot"))?;
            let access = derived[&at];
            if access.store || !claimed.insert(at) {
                return Err(bad(
                    "a claimed load is not a load of the slot, or is claimed twice",
                ));
            }
            let node = &source.blocks[at.0].body[at.1];
            let ty = &access.ty;
            if node.results != [load.result] {
                return Err(MidTvError::NotForwardable {
                    load: load.result,
                    why: "the load does not define the claimed result",
                });
            }
            let (field, part) = field_of(load.field, access)?;
            facts
                .reaches(&mut walks, load.field, load.value, at)
                .map_err(|why| MidTvError::NoUniqueReachingStore {
                    load: load.result,
                    why,
                })?;
            if let Some((d, w)) = part {
                if !load.extract.iter().all(|v| fresh(*v))
                    || load.via.is_some_and(|via| !fresh(via))
                {
                    return Err(bad("a part load's value is not a fresh value"));
                }
                let nodes = part_read(
                    node,
                    &field.carrier,
                    d,
                    w,
                    ty,
                    load.value,
                    &load.extract,
                    load.via,
                    load.result,
                )
                .map_err(bad)?;
                replaced.insert(at, nodes);
                rewrites += 1;
                continue;
            }
            if !load.extract.is_empty() {
                return Err(bad("a load of a whole field names part values"));
            }
            if bool_view(&field.carrier, ty) {
                // The nonzero test: exact on every byte the field holds,
                // and an inspection, so no store may leave it poison.
                if !plain_full[load.field] {
                    return Err(MidTvError::NotForwardable {
                        load: load.result,
                        why: "a converted read of a field some store may leave poison",
                    });
                }
                let via = load
                    .via
                    .filter(|via| fresh(*via))
                    .ok_or(bad("a bool read names no fresh zero"))?;
                let zero = node_like(
                    node,
                    Inst::Const {
                        ty: field.carrier.clone(),
                        value: Constant::Int(0),
                    },
                    via,
                );
                let test = node_like(
                    node,
                    Inst::ICmp {
                        op: ICmpOp::Ne,
                        ty: field.carrier.clone(),
                        lhs: load.value,
                        rhs: via,
                    },
                    load.result,
                );
                replaced.insert(at, vec![zero, test]);
                rewrites += 1;
                continue;
            }
            let conversion =
                reinterpretation(&layout, pointer_bits, &field.carrier, ty).map_err(bad)?;
            if conversion == Some(CastOp::PtrToPtr) && field.carrier != Ty::Ptr {
                return Err(bad("a pointer view of a field not carried as a pointer"));
            }
            if conversion.is_some() && !plain_full[load.field] {
                return Err(MidTvError::NotForwardable {
                    load: load.result,
                    why: "a converted read of a field some store may leave poison",
                });
            }
            // `inttoptr` yields a `ptr`: another pointer type is cast after.
            let needs_via = conversion == Some(CastOp::IntToPtr) && *ty != Ty::Ptr;
            if needs_via != load.via.is_some() || load.via.is_some_and(|via| !fresh(via)) {
                return Err(bad(
                    "a load's pointer cast is not the one its type needs, or is not fresh",
                ));
            }
            let mut first = node.clone();
            let nodes = match (conversion, load.via) {
                (None, _) => {
                    first.inst = Inst::Copy {
                        ty: ty.clone(),
                        operand: load.value,
                    };
                    vec![first]
                }
                (Some(op), None) => {
                    first.inst = Inst::Cast {
                        op,
                        src_ty: field.carrier.clone(),
                        dst_ty: ty.clone(),
                        operand: load.value,
                    };
                    vec![first]
                }
                (Some(op), Some(via)) => {
                    first.inst = Inst::Cast {
                        op,
                        src_ty: field.carrier.clone(),
                        dst_ty: Ty::Ptr,
                        operand: load.value,
                    };
                    first.results = vec![via];
                    let mut second = node.clone();
                    second.inst = Inst::Cast {
                        op: CastOp::PtrToPtr,
                        src_ty: Ty::Ptr,
                        dst_ty: ty.clone(),
                        operand: via,
                    };
                    vec![first, second]
                }
            };
            replaced.insert(at, nodes);
            rewrites += 1;
        }
        if claimed.len() != accesses.len() {
            return Err(bad("an access of the slot is not rewritten"));
        }
    }
    // Rebuild: parameters, edge values, then the accesses.
    for (bi, value, ty) in new_params {
        expected.blocks[bi].params.push((value, ty));
    }
    for ((pi, edge), value) in edge_values {
        let last = expected.blocks[pi]
            .body
            .last_mut()
            .ok_or(MidTvError::TargetDiffers {
                detail: "a predecessor has no terminator".to_string(),
            })?;
        edge_args_mut(&mut last.inst, edge)
            .ok_or(MidTvError::TargetDiffers {
                detail: "an incoming edge has no argument list".to_string(),
            })?
            .push(value);
    }
    for (bi, block) in expected.blocks.iter_mut().enumerate() {
        let body = std::mem::take(&mut block.body);
        block.body = body
            .into_iter()
            .enumerate()
            .flat_map(|(ni, node)| replaced.remove(&(bi, ni)).unwrap_or_else(|| vec![node]))
            .collect();
    }
    Ok((
        expected,
        WitnessVerdict {
            exact: 0,
            refinements: rewrites,
        },
    ))
}

#[cfg(test)]
#[path = "trust_ir_mid_tv_sroa_tests.rs"]
mod tests;
