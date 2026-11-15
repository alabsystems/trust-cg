// trust-cg-verify/trust_ir_mid_tv_argpromo.rs - argument promotion's checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The checker of argument promotion ([`ArgPromoWitness`]): a direct `call`
//! that passes the address of a caller's frame slot to a callee that only
//! loads and stores through that parameter at constant offsets calls a
//! specialized clone of the callee instead, which receives the bytes it reads
//! as values and returns the bytes it writes as extra results. A parameter
//! of an aggregate type (a struct, tuple or array) that the call is given a
//! pointer for — the rustc bridge passes an aggregate by address, and the
//! differential's view of the lane reads such an argument as the pointee's
//! bytes at the call — is promoted to the lanes the callee reads.
//!
//! For a typed aggregate load, the checker locates the original snapshot,
//! proves its selected fields initialized at that position, and reconstructs
//! scalar extractions from the immutable value at the call. It never reloads
//! the mutable source slot at that later position.
//!
//! **The clone** of callee `F` for a plan (per promoted parameter `p`: the
//! READ fields `R` and the WRITTEN fields `W`, each an `(offset, type)`; an
//! aggregate parameter has no `W`) is `F` with
//!
//! * `p` removed from the entry block's parameters and, in its place, one
//!   new parameter per `R` field, in `R`'s order;
//! * for an aggregate parameter, every `extractfield` of `p` (at `p`'s type)
//!   replaced by a `copy` of the new parameter of its lane;
//! * at the head of the entry block, per promoted pointer parameter in
//!   parameter order: `%n = const u32 extent`, `%a = alloca u8, %n, align A` (the
//!   allocation's result is `p` itself when `p` is a `ptr`, else a fresh
//!   value that `p = ptrtoptr ptr %a to <p's type>` re-types), then per `R`
//!   field a store of its parameter at its offset (`gep inbounds u8` by a
//!   fresh `const i32` unless the offset is 0), `align 1`;
//! * before each `ret`, per promoted parameter and `W` field, a load of the
//!   field (`align 1`), the loaded values appended to the returned ones;
//! * signature: the declared parameters with each promoted one replaced by
//!   its `R` types, the declared returns followed by the `W` types; a
//!   strong (`external`) hidden symbol named `<prefix>.tcg.ap<h>.tcg.crate.<tag>`
//!   where `F` is `<prefix>.tcg.crate.<tag>` (the rustc bridge's crate-private
//!   name) and `h` is the FNV-1a digest of the plan's text; function
//!   attributes with the parameter attributes moved with their parameters
//!   (default ones for the new parameters) and no `readonly`/`readnone`
//!   claim, not `retained`; everything else (span, scopes, names, calling
//!   convention, section) as `F`.
//!
//! Fresh values are minted in a fixed order from one past the largest value
//! the function names (parameters, results, operands, debug names): the new
//! entry parameters, then per promoted parameter the count, the allocation
//! (when re-typed) and each `R` field's offset and address, then per
//! returning block (in block order) per promoted parameter per `W` field its
//! offset, address and loaded value. The checker mints them itself, so a
//! clone that uses any other value is refused by the exact comparison.
//!
//! **What is re-derived from the source and the module**, per site, on the
//! caller as the earlier sites of the witness left it:
//!
//! * **The callee admits a clone.** A plain `call` (not `invoke`, not an
//!   indirect or no-unwind call, carrying no proof annotation or proof
//!   context of its own) of a function defined in the module under a
//!   crate-private name, strong (`external`) with hidden visibility, not
//!   variadic, naked or feature-stating, no parameter passed by copy, no
//!   proof annotation, call-site proof context, summary, source provenance,
//!   body gate or module obligation naming it (nor an unscoped obligation or
//!   a spec module), entry parameters of the declared types (thin pointers may
//!   be of other pointer types) and an entry block no edge targets. Every
//!   parameter the clone keeps is of exactly its declared type at the entry:
//!   the clone declares the signature's type and keeps the entry's, so a
//!   kept thin pointer of another pointer type would copy the callee's
//!   module-level `EntryParamsMismatch` into the clone.
//! * **The parameter's use** in the callee, for a pointer: every value
//!   derived from `p` by copies, `ptrtoptr`s and `gep`s by non-negative
//!   integer constants (the flat trust-ir GEP: `size(pointee) * sum(indices)`
//!   bytes on), and by the bridge's integer address chains (`ptrtoint` to
//!   the 32-bit pointer word, `add` of a non-negative constant, copies,
//!   `inttoptr` back, the offset below 2^31; the integers used for nothing
//!   else), lies before the extent of the bytes accessed and is used only
//!   as the address of a plain (non-volatile, non-atomic) `load` or `store`
//!   (never as a stored value), of the rustc bridge's read-through
//!   `extractfield` or write-through `insertfield` (lane `field` of its record
//!   type, the interpreter's layout; the write-through's result unused), or
//!   to derive another such value. So the callee reads and writes the
//!   pointee only at those offsets, and its address leaves no trace: no
//!   call, return, block argument, comparison, integer view or store of it.
//!   Each access is of a field type (an integer, `f32`, `f64`, `bool`,
//!   `char` or thin pointer) and its offset is a multiple of the alignment
//!   it requires (its own, or its type's natural one), so the clone's
//!   allocation, aligned to the largest, keeps every access aligned. `R` is
//!   the set of read fields and `W` the set of written fields, each sorted
//!   by offset, width and type text, exactly. For an aggregate: every use
//!   of `p` is an `extractfield` of it at its own type of a lane of a field
//!   type (the interpreter's layout); `R` is the set of lanes read.
//! * **The returned fields are never poison** (a poison value is undefined
//!   behaviour at a `ret`): in the clone, every byte of every `W` field is,
//!   on every path from the clone's entry to each `ret`, last written by a
//!   store (or write-through) of a value that is never poison
//!   (`sroa::defined_values`: arithmetic, casts, constants, addresses,
//!   parameters, the results of a function with a body (this witness's
//!   clones included), and moves of such) — the
//!   prologue's stores of the new parameters included — and, for a field of
//!   a type other than an integer or float, by an exact store of that type
//!   at its offset (so the load decodes it); for an integer or float field
//!   the writes are integers or floats.
//! * **An aggregate passed by address** is proved like a pointer: its
//!   argument is derived from a slot (below) and every lane it reads is a
//!   copied-in field. The wasm32 lane reads such an aggregate's lanes where
//!   the callee extracts them, not at the call, and the rustc bridge lowers
//!   `[MaybeUninit<T>; N]` as `[T x N]`, so neither an array's nor a
//!   struct's lanes are known initialized at the call.
//! * **The caller's slot.** The argument is derived from a fresh allocation
//!   `S` (an `alloca` of known size, count-free or counted by a positive
//!   integer constant) by copies, `ptrtoptr`s and constant `gep`s, at offset
//!   `o`, and `o + off + size` is inside `S` for every field. Every value
//!   derived from `S` that way is used only as the address of a plain load or
//!   store (never stored), of a read-through `extractfield` or a
//!   write-through `insertfield` whose result is unused, to derive another
//!   such value, or as the argument of a plain `call` of a function defined
//!   in the module with a linkage no other definition can replace at link
//!   time (`external`, `internal`, `private`), whose parameter there
//!   satisfies the use condition above: so `S`'s
//!   address is never stored, returned, compared, passed to a block or seen as
//!   an integer, and no function holds it beyond a call. No other argument of
//!   the promoted call is derived from `S`. During the call nothing but the
//!   callee's accesses through `p` can therefore read or write `S`.
//! * **The copied-in fields are never poison** (a poison argument is
//!   undefined behaviour at a call): every byte of every `R` field (at
//!   `o + off`) is, on every path from the caller's entry to the call, last
//!   written by a store (or write-through) through `S` of a never-poison
//!   value, with the type condition above; the `alloca` of `S` itself, a
//!   write at an unknown offset or of a maybe-poison value over the byte, a
//!   bulk or atomic write, and a call passing any value derived from `S` end
//!   the path unproved.
//!
//! **The rewrite**, at the call: before it, per promoted parameter, the
//! argument re-typed to `ptr` by `ptrtoptr` unless it is one, then per `R`
//! field its offset, address and `load <type>, align 1`; the call names the
//! clone, passes the loaded values in place of the argument and gets the
//! `W` values as extra results; after it, per promoted parameter per `W`
//! field, a `store <type>, align 1` of the result at its offset. The new
//! instructions take the call's span and scope. Fresh values: per promoted
//! parameter the re-typed argument and each `R` field's offset, address and
//! value; then the `W` results; then per promoted parameter per `W` field
//! its offset and address.
//!
//! Each site is a REFINEMENT of the reference interpreter's semantics. For an
//! aggregate, the source's callee reads lanes of the slot's bytes (the
//! interpreter's view copies them at the call, the wasm32 lane reads each
//! where the callee extracts it; nothing but the callee reaches the slot
//! during the call, so both read the bytes the call saw) and the target's
//! reads the same lanes, loaded at the call. For a pointer, in the source the callee runs with `p = S + o`; nothing else
//! reads or writes
//! `S` while it runs, its accesses through `p` are exactly the `R` and `W`
//! fields, and its address is never observed. In the target the caller
//! loads the `R` fields (in bounds, `align 1`, never poison, decodable by
//! the type condition), the clone stores them into a fresh allocation `L`
//! and runs the callee's body with `p = L`: every read through `p` reads a
//! byte the callee wrote before on that path or one copied in (all of `R`),
//! so it reads what the source reads; every write lands in `L` as it lands
//! in `S` (an integer address chain rebuilds `L + k` exactly as `S + o + k`:
//! the integers flow only into `inttoptr`, which resolves each to the same
//! allocation and offset); and at each `ret` the `W` fields of `L` hold the
//! bytes `S` holds
//! at the source's return, which the caller stores back. The callee's other
//! effects are unchanged and in the same order, and `S` is unobservable
//! during the call, so writing it after the call is unobservable too. The
//! target allocates `L` per call (the interpreter never frees an `alloca`).
//! The allocation bound is policy: the pass bounds a parameter's extent.

use std::collections::{HashMap, HashSet};

use trust_ir::{
    BlockId, CastOp, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Linkage, Module,
    ParamAttrs, PassMode, Ty, ValueId, Visibility,
};

use super::{MidTvError, WitnessVerdict, block_positions};
use crate::fsym_layout::FsymLayout;

/// The rustc bridge's crate-private symbol mark (`<symbol>.tcg.crate.<16
/// lowercase hex digits>`): the round-11 provisional scheme's one constant.
use crate::wasm_internal_abi::CRATE_PRIVATE_MARK as CRATE_MARK;

/// The infix that names a clone.
pub const ARGPROMO_CLONE_MARK: &str = ".tcg.ap";

/// One field of a promoted parameter: its byte offset from the parameter
/// and its type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArgPromoField {
    pub offset: u64,
    pub ty: Ty,
}

/// One promoted parameter of a callee: its index and the fields the callee
/// reads (copied in) and writes (copied out) through it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArgPromoParam {
    pub index: usize,
    pub reads: Vec<ArgPromoField>,
    pub writes: Vec<ArgPromoField>,
}

/// One promoted call, in the function the witness's earlier sites produced.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArgPromoSite {
    /// The block holding the `call` and the call's index in it.
    pub block: BlockId,
    pub index: usize,
    /// The callee and the clone the call is redirected to.
    pub callee: FuncId,
    pub clone: FuncId,
    /// The promoted parameters, in increasing index order.
    pub params: Vec<ArgPromoParam>,
}

/// Argument promotion's claim about one caller: the sites, applied in order,
/// and the clones and signatures the rewrite appends to the module (a clone
/// another caller's rewrite added earlier is named by its id and found in
/// the module).
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ArgPromoWitness {
    pub sites: Vec<ArgPromoSite>,
    pub new_func_types: Vec<FuncTy>,
    pub new_functions: Vec<Function>,
}

impl ArgPromoWitness {
    /// Number of claimed rewrites (promoted calls).
    pub fn rewrite_count(&self) -> usize {
        self.sites.len()
    }
}

fn refuse(site: usize, why: impl Into<String>) -> MidTvError {
    MidTvError::NotPromotableArgument {
        site,
        why: why.into(),
    }
}

/// A thin pointer type: one address word, no metadata.
fn thin_pointer(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
    )
}

/// An integer or float: any initialized bytes decode as one.
fn numeric(ty: &Ty) -> bool {
    ty.is_integer() || matches!(ty, Ty::F32 | Ty::F64)
}

/// A type a field may have.
fn field_type(ty: &Ty) -> bool {
    numeric(ty) || matches!(ty, Ty::Bool | Ty::Char) || thin_pointer(ty)
}

/// The canonical order of fields: offset, width, type text.
fn sort_fields(layout: &FsymLayout<'_>, fields: &mut Vec<ArgPromoField>) {
    let key = |f: &ArgPromoField| (f.offset, layout.size(&f.ty).unwrap_or(0), f.ty.to_string());
    fields.sort_by_key(key);
    fields.dedup();
}

/// Lane `field` of the record type `ty` with the interpreter's layout.
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

/// The integer constant `v` is defined as (sole definition), if any.
fn const_of(func: &Function, v: ValueId) -> Option<i128> {
    func.blocks
        .iter()
        .flat_map(|b| &b.body)
        .find(|n| n.results.as_slice() == [v])
        .and_then(|n| match &n.inst {
            Inst::Const {
                ty,
                value: Constant::Int(k),
            } if ty.is_integer() => Some(*k),
            _ => None,
        })
}

/// Every use of each value: `(block position, node index)`, once per node.
fn uses_of(func: &Function) -> HashMap<ValueId, Vec<(usize, usize)>> {
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
    uses
}

/// The values derived from an allocation or a parameter: each with its byte
/// offset from it, and which of them are integers.
struct Derived {
    offsets: HashMap<ValueId, u64>,
    ints: HashSet<ValueId>,
}

impl Derived {
    fn has(&self, v: &ValueId) -> bool {
        self.offsets.contains_key(v)
    }

    fn pointers(&self) -> Vec<(ValueId, u64)> {
        self.offsets
            .iter()
            .filter(|(v, _)| !self.ints.contains(v))
            .map(|(v, o)| (*v, *o))
            .collect()
    }
}

/// The values derived from `root`: pointers by copies, `ptrtoptr`s and
/// `gep`s by non-negative integer constants; integers by `ptrtoint` of one
/// to the 32-bit pointer word (`i32`, `u32`, `isize`, `usize` at 32-bit
/// pointers), `add` of a non-negative integer constant (the sum below 2^31)
/// and copies, which `inttoptr` turns back into pointers. Each value has its
/// byte offset from `root`. `Err` when an address is a `gep` index or offset
/// by a variable or negative index, or an integer is used for anything else
/// (compared, stored, returned, passed, combined with a non-constant): an
/// integer view of the address may then be observed.
fn derived(
    layout: &FsymLayout<'_>,
    module: &Module,
    func: &Function,
    uses: &HashMap<ValueId, Vec<(usize, usize)>>,
    root: ValueId,
) -> Result<Derived, &'static str> {
    let mut out = Derived {
        offsets: HashMap::from([(root, 0)]),
        ints: HashSet::new(),
    };
    let word = |ty: &Ty| {
        module.pointer_bits() == 32 && matches!(ty, Ty::I32 | Ty::U32 | Ty::Isize | Ty::Usize)
    };
    let mut work = vec![root];
    while let Some(v) = work.pop() {
        let off = out.offsets[&v];
        let int = out.ints.contains(&v);
        for &(bi, ni) in uses.get(&v).map(Vec::as_slice).unwrap_or_default() {
            let node = &func.blocks[bi].body[ni];
            let next: Option<(u64, bool)> = if int {
                match &node.inst {
                    Inst::Copy { .. } => Some((off, true)),
                    Inst::Cast {
                        op: CastOp::IntToPtr,
                        ..
                    } => Some((off, false)),
                    Inst::BinOp {
                        op: trust_ir::BinOp::Add,
                        lhs,
                        rhs,
                        ..
                    } if (*lhs == v) != (*rhs == v) => {
                        let k = const_of(func, if *lhs == v { *rhs } else { *lhs })
                            .ok_or("an integer address plus a non-constant")?;
                        let k = u64::try_from(k).map_err(|_| "an integer address minus")?;
                        let sum = off.checked_add(k).filter(|&s| s < 1 << 31);
                        Some((sum.ok_or("an integer address past 2^31")?, true))
                    }
                    _ => return Err("an integer view of the address is observed"),
                }
            } else {
                match &node.inst {
                    Inst::Copy { operand, .. }
                    | Inst::Cast {
                        op: CastOp::PtrToPtr,
                        operand,
                        ..
                    } if *operand == v => Some((off, false)),
                    Inst::Cast {
                        op: CastOp::PtrToInt,
                        operand,
                        dst_ty,
                        ..
                    } if *operand == v => {
                        if !word(dst_ty) {
                            return Err("an integer view of the address of another width");
                        }
                        Some((off, true))
                    }
                    Inst::GEP {
                        pointee_ty,
                        base,
                        indices,
                        ..
                    } if *base == v => {
                        if indices.contains(&v) {
                            return Err("an address is a gep index");
                        }
                        let elem = layout
                            .size(pointee_ty)
                            .map_err(|_| "a gep element has no size")?;
                        let mut sum: u64 = 0;
                        for k in indices {
                            let k = const_of(func, *k).ok_or("a gep by a variable index")?;
                            let k = u64::try_from(k).map_err(|_| "a gep by a negative index")?;
                            sum = sum.checked_add(k).ok_or("a gep index overflows")?;
                        }
                        Some((
                            elem.checked_mul(sum)
                                .and_then(|d| off.checked_add(d))
                                .ok_or("a gep offset overflows")?,
                            false,
                        ))
                    }
                    Inst::GEP { indices, .. } if indices.contains(&v) => {
                        return Err("an address is a gep index");
                    }
                    _ => None,
                }
            };
            if let Some((o, is_int)) = next {
                let [r] = node.results.as_slice() else {
                    return Err("a derivation without one result");
                };
                match out.offsets.get(r) {
                    Some(&known) if known != o || out.ints.contains(r) != is_int => {
                        return Err("a value with two offsets");
                    }
                    Some(_) => {}
                    None => {
                        out.offsets.insert(*r, o);
                        if is_int {
                            out.ints.insert(*r);
                        }
                        work.push(*r);
                    }
                }
            }
        }
    }
    Ok(out)
}

/// What a callee does through one pointer parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Shape {
    reads: Vec<ArgPromoField>,
    writes: Vec<ArgPromoField>,
    /// One past the last byte accessed (at least 1).
    extent: u64,
    /// The largest alignment an access requires (at least 1).
    align: u64,
    /// An aggregate passed by value (by address in the rustc bridge's
    /// spelling) whose lanes the callee reads, rather than a pointer.
    by_value: bool,
}

/// A struct, tuple or array type: an aggregate the rustc bridge passes by
/// address.
fn record(ty: &Ty) -> bool {
    matches!(ty, Ty::Struct(_) | Ty::Tuple(_) | Ty::Array(..))
}

/// Decode a scalar lane read independently of the producer. Typed arrays
/// use a constant usize index; typed records declare the result lane type.
/// The older declared-record spelling remains checked under its old rule.
fn value_lane(
    layout: &FsymLayout<'_>,
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
            let (_, lane) = record_lane(layout, module, pty, *field)?;
            if ty != pty && (matches!(pty, Ty::Array(..)) || *ty != lane) {
                return None;
            }
            *field
        }
        Inst::ExtractElement { ty, array, index }
            if *array == p && matches!(pty, Ty::Array(..)) =>
        {
            let node = func
                .blocks
                .iter()
                .flat_map(|b| &b.body)
                .find(|n| n.results.as_slice() == [*index])?;
            let Inst::Const {
                ty: Ty::Usize,
                value: Constant::Int(i),
            } = node.inst
            else {
                return None;
            };
            let field = u32::try_from(i).ok()?;
            if record_lane(layout, module, pty, field)?.1 != *ty {
                return None;
            }
            field
        }
        _ => return None,
    };
    let (offset, ty) = record_lane(layout, module, pty, field)?;
    Some((field, offset, ty))
}

/// Every use of an aggregate parameter is a constant scalar lane read.
fn aggregate_lanes(
    layout: &FsymLayout<'_>,
    module: &Module,
    func: &Function,
    p: ValueId,
    pty: &Ty,
) -> Result<Shape, &'static str> {
    let uses = uses_of(func);
    let mut reads = Vec::new();
    let mut extent: u64 = 1;
    for &(bi, ni) in uses.get(&p).map(Vec::as_slice).unwrap_or_default() {
        let (_, offset, lane) =
            value_lane(layout, module, func, p, pty, &func.blocks[bi].body[ni].inst)
                .ok_or("the aggregate is used other than by reading its lanes")?;
        if !field_type(&lane) {
            return Err("a lane of a type other than a scalar field's");
        }
        let size = layout.size(&lane).map_err(|_| "a lane has no size")?;
        extent = extent.max(offset.checked_add(size).ok_or("a lane overflows")?);
        reads.push(ArgPromoField { offset, ty: lane });
    }
    sort_fields(layout, &mut reads);
    Ok(Shape {
        reads,
        writes: Vec::new(),
        extent,
        align: 1,
        by_value: true,
    })
}

/// Locate the original typed value load, whose initialized bytes are
/// checked at this position rather than at the later call. The rewrite
/// extracts from the SSA snapshot and never reloads its mutable source.
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

/// The use condition of parameter `index` of `func` (module documentation).
fn param_shape(
    layout: &FsymLayout<'_>,
    module: &Module,
    func: &Function,
    index: usize,
) -> Result<Shape, &'static str> {
    let entry = func
        .blocks
        .iter()
        .find(|b| b.id == func.entry)
        .ok_or("no entry block")?;
    let (p, pty) = entry.params.get(index).ok_or("no such parameter")?;
    if record(pty) {
        return aggregate_lanes(layout, module, func, *p, pty);
    }
    if !thin_pointer(pty) {
        return Err("the parameter is neither a thin pointer nor an aggregate");
    }
    let uses = uses_of(func);
    let family = derived(layout, module, func, &uses, *p)?;
    let mut reads = Vec::new();
    let mut writes = Vec::new();
    let mut extent: u64 = 1;
    let mut align: u64 = 1;
    let mut access = |off: u64, ty: &Ty, explicit: Option<u64>, list: &mut Vec<ArgPromoField>| {
        if !field_type(ty) {
            return Err("an access of a type other than a scalar field's");
        }
        let size = layout.size(ty).map_err(|_| "an access type has no size")?;
        let required = match explicit {
            Some(a) => a,
            None => layout
                .align(ty)
                .map_err(|_| "an access type has no alignment")?,
        };
        if required == 0 || !off.is_multiple_of(required) {
            return Err("an access at an offset its alignment does not divide");
        }
        extent = extent.max(off.checked_add(size).ok_or("an access overflows")?);
        align = align.max(required);
        list.push(ArgPromoField {
            offset: off,
            ty: ty.clone(),
        });
        Ok(())
    };
    for (v, off) in family.pointers() {
        for &(bi, ni) in uses.get(&v).map(Vec::as_slice).unwrap_or_default() {
            let node = &func.blocks[bi].body[ni];
            match &node.inst {
                Inst::Load {
                    ty,
                    ptr,
                    volatile: false,
                    align: a,
                } if *ptr == v => access(off, ty, *a, &mut reads)?,
                Inst::Store {
                    ty,
                    ptr,
                    value,
                    volatile: false,
                    align: a,
                } if *ptr == v && !family.has(value) => {
                    access(off, ty, *a, &mut writes)?;
                }
                Inst::ExtractField {
                    ty,
                    aggregate,
                    field,
                } if *aggregate == v => {
                    let (lo, lane) =
                        record_lane(layout, module, ty, *field).ok_or("an unknown lane")?;
                    access(off + lo, &lane, None, &mut reads)?;
                }
                Inst::InsertField {
                    ty,
                    aggregate,
                    field,
                    value,
                } if *aggregate == v && !family.has(value) => {
                    if node.results.iter().any(|r| uses.contains_key(r)) {
                        return Err("a write-through whose result is used");
                    }
                    let (lo, lane) =
                        record_lane(layout, module, ty, *field).ok_or("an unknown lane")?;
                    access(off + lo, &lane, None, &mut writes)?;
                }
                Inst::Copy { .. }
                | Inst::Cast {
                    op: CastOp::PtrToPtr | CastOp::PtrToInt,
                    ..
                }
                | Inst::GEP { .. } => {
                    if !node.results.iter().all(|r| family.has(r)) {
                        return Err("a derived address outside the family");
                    }
                }
                _ => return Err("the address escapes or is accessed otherwise"),
            }
        }
    }
    if family.pointers().iter().any(|(_, off)| *off >= extent) {
        return Err("an address derived past the bytes accessed");
    }
    sort_fields(layout, &mut reads);
    sort_fields(layout, &mut writes);
    Ok(Shape {
        reads,
        writes,
        extent,
        align,
        by_value: false,
    })
}

/// The callee as a clone's template: its declared signature (module
/// documentation, "the callee admits a clone").
fn admit(module: &Module, callee: FuncId) -> Result<(&Function, &FuncTy), &'static str> {
    let func = module
        .function_by_id(callee)
        .ok_or("the module defines no such function")?;
    if func.is_declaration() {
        return Err("a declaration");
    }
    if func.linkage != Linkage::External || func.visibility != Visibility::Hidden {
        return Err("not a strong hidden symbol");
    }
    if crate_split(&func.name).is_none() {
        return Err("not a crate-private name");
    }
    if func.attrs.naked
        || !func.attrs.target_features.is_empty()
        || func
            .attrs
            .params
            .iter()
            .any(|p| p.byval || matches!(p.pass, Some(PassMode::Indirect { .. })))
    {
        return Err("naked, feature-stating or with a parameter passed by copy");
    }
    if !func.proofs.is_empty()
        || func.summary.is_some()
        || func.source_provenance.is_some()
        || func.body_gate.is_some()
        || func
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| !n.proofs.is_empty() || n.proof_context.is_some())
    {
        return Err("it carries proof material");
    }
    if !module.spec_modules.is_empty()
        || module.proof_obligations.iter().any(|o| {
            (o.function.is_none() && o.site.is_none())
                || o.function == Some(callee)
                || o.site.as_ref().is_some_and(|s| s.function == callee)
        })
    {
        return Err("a module proof obligation names it (or protects every function)");
    }
    let sig = module.func_type(func.ty).ok_or("no signature")?;
    if sig.abi.is_some() {
        return Err("recorded signature ABI needs carrier-placement rederivation");
    }
    if sig.is_vararg {
        return Err("variadic");
    }
    let entry = func
        .blocks
        .iter()
        .find(|b| b.id == func.entry)
        .ok_or("no entry block")?;
    if entry.params.len() != sig.params.len()
        || entry
            .params
            .iter()
            .zip(&sig.params)
            .any(|((_, t), p)| t != p && !(thin_pointer(t) && thin_pointer(p)))
    {
        return Err("the entry parameters are not the declared ones");
    }
    if func.blocks.iter().any(|b| {
        b.body.last().is_some_and(|n| {
            n.inst
                .successor_edges()
                .iter()
                .any(|e| e.target == func.entry)
        })
    }) {
        return Err("the entry block is the target of an edge");
    }
    Ok((func, sig))
}

/// `(prefix, tag)` of a crate-private name `<prefix>.tcg.crate.<tag>`.
fn crate_split(name: &str) -> Option<(&str, &str)> {
    let at = name.rfind(CRATE_MARK)?;
    let tag = &name[at + CRATE_MARK.len()..];
    (at > 0
        && tag.len() == 16
        && tag
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)))
    .then(|| (&name[..at], tag))
}

/// The plan's text, which names the clone.
fn plan_text(params: &[ArgPromoParam]) -> String {
    let mut text = String::new();
    for p in params {
        text.push_str(&format!("{}:", p.index));
        for f in &p.reads {
            text.push_str(&format!("r{}@{};", f.ty, f.offset));
        }
        for f in &p.writes {
            text.push_str(&format!("w{}@{};", f.ty, f.offset));
        }
        text.push('|');
    }
    text
}

/// The clone's name for `callee` and the plan (module documentation).
pub fn argpromo_clone_name(callee: &str, params: &[ArgPromoParam]) -> Option<String> {
    let (prefix, tag) = crate_split(callee)?;
    let mut hash: u32 = 0x811c_9dc5;
    for byte in plan_text(params).bytes() {
        hash ^= u32::from(byte);
        hash = hash.wrapping_mul(0x0100_0193);
    }
    Some(format!(
        "{prefix}{ARGPROMO_CLONE_MARK}{hash:08x}{CRATE_MARK}{tag}"
    ))
}

/// The clone's signature.
fn clone_sig(sig: &FuncTy, params: &[ArgPromoParam]) -> FuncTy {
    let mut out = FuncTy {
        params: Vec::new(),
        returns: sig.returns.clone(),
        abi: None,
        is_vararg: false,
    };
    for (j, ty) in sig.params.iter().enumerate() {
        match params.iter().find(|p| p.index == j) {
            Some(p) => out.params.extend(p.reads.iter().map(|f| f.ty.clone())),
            None => out.params.push(ty.clone()),
        }
    }
    for p in params {
        out.returns.extend(p.writes.iter().map(|f| f.ty.clone()));
    }
    out
}

/// One past the largest value `func` names.
fn first_fresh(func: &Function) -> u32 {
    let mut max: Option<u32> = None;
    let mut see = |v: ValueId| max = Some(max.map_or(v.index(), |m| m.max(v.index())));
    for block in &func.blocks {
        for (v, _) in &block.params {
            see(*v);
        }
        for node in &block.body {
            for r in &node.results {
                see(*r);
            }
            node.inst.visit_value_operands(&mut see);
        }
    }
    if let Some(names) = &func.value_names {
        for (v, _) in names {
            see(*v);
        }
    }
    max.map_or(0, |m| m + 1)
}

/// A fresh-value cursor.
struct Fresh(u32);

impl Fresh {
    fn next(&mut self) -> ValueId {
        let v = ValueId::new(self.0);
        self.0 += 1;
        v
    }
}

fn node(inst: Inst, results: Vec<ValueId>) -> InstrNode {
    let mut n = InstrNode::new(inst);
    n.results = results;
    n
}

/// `[%c = const i32 off, %g = gep inbounds u8, ptr base, %c]` (nothing at
/// offset 0) and the address.
fn address(fresh: &mut Fresh, base: ValueId, off: u64, out: &mut Vec<InstrNode>) -> ValueId {
    if off == 0 {
        return base;
    }
    let (c, g) = (fresh.next(), fresh.next());
    out.push(node(
        Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(i128::from(off)),
        },
        vec![c],
    ));
    out.push(node(
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

/// The clone of `func` (signature `sig`) under the plan (module
/// documentation), with the shapes the plan's parameters were derived with,
/// and each promoted parameter's allocation.
#[allow(clippy::too_many_arguments)]
fn derive_clone(
    layout: &FsymLayout<'_>,
    module: &Module,
    func: &Function,
    sig: &FuncTy,
    params: &[ArgPromoParam],
    shapes: &[Shape],
    id: FuncId,
    name: String,
    ty: trust_ir::FuncTyId,
) -> (Function, Vec<Option<ValueId>>) {
    let mut clone = func.clone();
    clone.id = id;
    clone.name = name;
    clone.ty = ty;
    clone.linkage = Linkage::External;
    clone.visibility = Visibility::Hidden;
    clone.retained = false;
    clone.attrs.readonly = false;
    clone.attrs.readnone = false;
    let mut attrs = Vec::new();
    for j in 0..sig.params.len() {
        match params.iter().find(|p| p.index == j) {
            Some(p) => attrs.extend(p.reads.iter().map(|_| ParamAttrs::default())),
            None => attrs.push(func.attrs.params.get(j).cloned().unwrap_or_default()),
        }
    }
    if attrs.iter().all(|a| *a == ParamAttrs::default()) && func.attrs.params.is_empty() {
        attrs.clear();
    }
    clone.attrs.params = attrs;
    let mut fresh = Fresh(first_fresh(func));
    let Some(ei) = clone.blocks.iter().position(|b| b.id == func.entry) else {
        return (clone, Vec::new());
    };
    // New entry parameters.
    let old_params = clone.blocks[ei].params.clone();
    let mut entry_params = Vec::new();
    let mut field_values: Vec<Vec<ValueId>> = Vec::new();
    for (j, (v, t)) in old_params.iter().enumerate() {
        match params.iter().find(|p| p.index == j) {
            Some(p) => {
                let vals: Vec<ValueId> = p.reads.iter().map(|_| fresh.next()).collect();
                for (val, f) in vals.iter().zip(&p.reads) {
                    entry_params.push((*val, f.ty.clone()));
                }
                field_values.push(vals);
            }
            None => entry_params.push((*v, t.clone())),
        }
    }
    clone.blocks[ei].params = entry_params;
    // The prologue; an aggregate's lane reads become copies of its new
    // parameters instead.
    let mut prologue = Vec::new();
    let mut bases = Vec::new();
    let mut lanes: HashMap<ValueId, (Ty, Vec<(ArgPromoField, ValueId)>)> = HashMap::new();
    for ((p, shape), vals) in params.iter().zip(shapes).zip(&field_values) {
        let (pv, pty) = old_params[p.index].clone();
        if shape.by_value {
            lanes.insert(
                pv,
                (
                    pty,
                    p.reads.iter().cloned().zip(vals.iter().copied()).collect(),
                ),
            );
            bases.push(None);
            continue;
        }
        let n = fresh.next();
        prologue.push(node(
            Inst::Const {
                ty: Ty::U32,
                value: Constant::Int(i128::from(shape.extent)),
            },
            vec![n],
        ));
        let base = if pty == Ty::Ptr { pv } else { fresh.next() };
        prologue.push(node(
            Inst::Alloca {
                ty: Ty::U8,
                count: Some(n),
                align: Some(shape.align),
            },
            vec![base],
        ));
        if base != pv {
            prologue.push(node(
                Inst::Cast {
                    op: CastOp::PtrToPtr,
                    src_ty: Ty::Ptr,
                    dst_ty: pty.clone(),
                    operand: base,
                },
                vec![pv],
            ));
        }
        for (f, val) in p.reads.iter().zip(vals) {
            let at = address(&mut fresh, base, f.offset, &mut prologue);
            prologue.push(node(
                Inst::Store {
                    ty: f.ty.clone(),
                    ptr: at,
                    value: *val,
                    volatile: false,
                    align: Some(1),
                },
                Vec::new(),
            ));
        }
        bases.push(Some(base));
    }
    for n in clone.blocks.iter_mut().flat_map(|b| &mut b.body) {
        let read = lanes.iter().find_map(|(aggregate, (pty, pairs))| {
            let (_, offset, lane) = value_lane(layout, module, func, *aggregate, pty, &n.inst)?;
            let (_, value) = pairs
                .iter()
                .find(|(f, _)| f.offset == offset && f.ty == lane)?;
            Some((lane, *value))
        });
        if let Some((ty, operand)) = read {
            n.inst = Inst::Copy { ty, operand };
        }
    }
    let body = std::mem::take(&mut clone.blocks[ei].body);
    clone.blocks[ei].body = prologue.into_iter().chain(body).collect();
    // The epilogues.
    for block in &mut clone.blocks {
        let Some(last) = block.body.pop() else {
            continue;
        };
        let Inst::Return { values } = &last.inst else {
            block.body.push(last);
            continue;
        };
        let mut values = values.clone();
        for (p, base) in params.iter().zip(&bases) {
            let Some(base) = base else {
                continue;
            };
            for f in &p.writes {
                let at = address(&mut fresh, *base, f.offset, &mut block.body);
                let l = fresh.next();
                block.body.push(node(
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
        let mut ret = last.clone();
        ret.inst = Inst::Return { values };
        block.body.push(ret);
    }
    (clone, bases)
}

/// What a backward walk meets at one instruction for one byte.
enum Meet {
    /// The byte's last write: a never-poison value of an admitted type.
    Def,
    /// A write the byte's value cannot be proved through.
    Clobber,
    /// Nothing that writes the byte.
    Pass,
}

/// Whether every path from `func`'s entry to `(block, index)` (exclusive)
/// last writes byte `byte` of the allocation whose derived values are
/// `family` (offsets from the allocation, defined by `root`) through it, with
/// a never-poison value (`defined`) admitted for a field `(field_off,
/// field_ty)` (module documentation).
#[allow(clippy::too_many_arguments)]
fn byte_written(
    layout: &FsymLayout<'_>,
    module: &Module,
    func: &Function,
    family: &Derived,
    root: ValueId,
    defined: &HashSet<ValueId>,
    at: (usize, usize),
    byte: u64,
    field: (u64, &Ty),
) -> bool {
    let positions = block_positions(func);
    let Some(&entry) = positions.get(&func.entry) else {
        return false;
    };
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); func.blocks.len()];
    for (bi, block) in func.blocks.iter().enumerate() {
        if let Some(last) = block.body.last() {
            for edge in last.inst.successor_edges() {
                if let Some(&ti) = positions.get(&edge.target) {
                    preds[ti].push(bi);
                }
            }
        }
    }
    let admitted = |off: u64, ty: &Ty, value: ValueId| -> Meet {
        let Ok(size) = layout.size(ty) else {
            return Meet::Clobber;
        };
        if byte < off || byte >= off.saturating_add(size) {
            return Meet::Pass;
        }
        let typed = if numeric(field.1) {
            numeric(ty)
        } else {
            off == field.0 && ty == field.1
        };
        if typed && defined.contains(&value) {
            Meet::Def
        } else {
            Meet::Clobber
        }
    };
    let meet = |n: &InstrNode| -> Meet {
        if n.results.contains(&root) {
            return Meet::Clobber;
        }
        match &n.inst {
            Inst::Store { ty, ptr, value, .. } if family.has(ptr) => {
                return admitted(family.offsets[ptr], ty, *value);
            }
            Inst::InsertField {
                ty,
                aggregate,
                field,
                value,
            } if family.has(aggregate) => {
                return match record_lane(layout, module, ty, *field) {
                    Some((lo, lane)) => admitted(family.offsets[aggregate] + lo, &lane, *value),
                    None => Meet::Clobber,
                };
            }
            // Reads and derivations of the address (the integer chain
            // included) write nothing.
            Inst::Load { .. }
            | Inst::ExtractField { .. }
            | Inst::GEP { .. }
            | Inst::Copy { .. }
            | Inst::Cast { .. }
            | Inst::BinOp { .. } => return Meet::Pass,
            _ => {}
        }
        // Any other instruction given an address of the allocation (a call
        // that passes it, a bulk or atomic write) may write any of its
        // bytes; one given none cannot reach them (the allocation's address
        // is never stored, returned or seen as an integer).
        let mut given = false;
        n.inst.visit_value_operands(|v| given |= family.has(&v));
        if given { Meet::Clobber } else { Meet::Pass }
    };
    let mut seen: HashSet<usize> = HashSet::new();
    let mut work: Vec<(usize, Option<usize>)> = vec![(at.0, Some(at.1))];
    while let Some((bi, upto)) = work.pop() {
        let body = &func.blocks[bi].body;
        let end = upto.unwrap_or(body.len()).min(body.len());
        let mut done = false;
        for n in body[..end].iter().rev() {
            match meet(n) {
                Meet::Def => {
                    done = true;
                    break;
                }
                Meet::Clobber => return false,
                Meet::Pass => {}
            }
        }
        if done {
            continue;
        }
        if bi == entry {
            return false;
        }
        for &p in &preds[bi] {
            if seen.insert(p) {
                work.push((p, None));
            }
        }
    }
    true
}

/// The values of `func` of a thin pointer type, from this module's typing.
fn pointer_type(module: &Module, func: &Function, v: ValueId) -> Option<Ty> {
    super::inline::value_types_of(module, func).remove(&v)
}

/// The clone a site names, re-derived from its callee and plan and compared
/// with the one the module or the witness holds; returns its signature.
#[allow(clippy::too_many_arguments)]
fn check_clone(
    layout: &FsymLayout<'_>,
    module: &Module,
    witness: &ArgPromoWitness,
    s: usize,
    site: &ArgPromoSite,
    callee: &Function,
    sig: &FuncTy,
    shapes: &[Shape],
    checked: &mut HashMap<FuncId, Vec<ArgPromoParam>>,
) -> Result<FuncTy, MidTvError> {
    let name = argpromo_clone_name(&callee.name, &site.params)
        .ok_or_else(|| refuse(s, "the callee has no crate-private name"))?;
    let entry = callee
        .blocks
        .iter()
        .find(|b| b.id == callee.entry)
        .ok_or_else(|| refuse(s, "the callee has no entry block"))?;
    if entry
        .params
        .iter()
        .zip(&sig.params)
        .enumerate()
        .any(|(j, ((_, t), p))| t != p && !site.params.iter().any(|q| q.index == j))
    {
        return Err(refuse(
            s,
            "a parameter the clone keeps has an entry type other than its declared one",
        ));
    }
    let csig = clone_sig(sig, &site.params);
    let claimed = witness
        .new_functions
        .iter()
        .find(|f| f.id == site.clone)
        .or_else(|| module.function_by_id(site.clone))
        .ok_or_else(|| refuse(s, "the clone is neither new nor in the module"))?;
    if let Some(plan) = checked.get(&site.clone) {
        if *plan != site.params || claimed.name != name {
            return Err(refuse(s, "two plans name one clone"));
        }
        return Ok(csig);
    }
    // The clone's signature: the first equal entry of the module's table
    // followed by the witness's new entries.
    let table: Vec<&FuncTy> = module
        .func_types
        .iter()
        .chain(&witness.new_func_types)
        .collect();
    let ty_index = table
        .iter()
        .position(|t| **t == csig)
        .ok_or_else(|| refuse(s, "the clone's signature is in no table"))?;
    let ty = trust_ir::FuncTyId::new(
        u32::try_from(ty_index).map_err(|_| refuse(s, "too many signatures"))?,
    );
    let (expected, roots) = derive_clone(
        layout,
        module,
        callee,
        sig,
        &site.params,
        shapes,
        site.clone,
        name,
        ty,
    );
    if *claimed != expected {
        return Err(refuse(
            s,
            "the clone is not the callee's body under the plan",
        ));
    }
    // The fields returned are never poison at any `ret`.
    let defined = super::sroa::defined_values(module, &expected);
    let uses = uses_of(&expected);
    for (p, root) in site.params.iter().zip(roots) {
        let Some(root) = root else {
            continue;
        };
        let family = derived(layout, module, &expected, &uses, root)
            .map_err(|why| refuse(s, format!("the clone's allocation: {why}")))?;
        for (bi, block) in expected.blocks.iter().enumerate() {
            let Some(last) = block.body.last() else {
                continue;
            };
            if !matches!(last.inst, Inst::Return { .. }) {
                continue;
            }
            for f in &p.writes {
                let size = layout
                    .size(&f.ty)
                    .map_err(|_| refuse(s, "a field has no size"))?;
                for byte in f.offset..f.offset + size {
                    if !byte_written(
                        layout,
                        module,
                        &expected,
                        &family,
                        root,
                        &defined,
                        (bi, block.body.len() - 1),
                        byte,
                        (f.offset, &f.ty),
                    ) {
                        return Err(refuse(
                            s,
                            format!(
                                "byte {byte} of returned field {}@{} may be poison at a ret",
                                f.ty, f.offset
                            ),
                        ));
                    }
                }
            }
        }
    }
    checked.insert(site.clone, site.params.clone());
    Ok(csig)
}

/// The allocation `v` is derived from by copies, `ptrtoptr`s and constant
/// `gep`s, and its size (known layout, count-free or a positive constant
/// count).
fn slot_root(layout: &FsymLayout<'_>, func: &Function, mut v: ValueId) -> Option<(ValueId, u64)> {
    let def = |v: ValueId| {
        func.blocks
            .iter()
            .flat_map(|b| &b.body)
            .find(|n| n.results.as_slice() == [v])
            .map(|n| &n.inst)
    };
    for _ in 0..64 {
        match def(v)? {
            Inst::Alloca { ty, count, .. } => {
                let count = match count {
                    None => 1,
                    Some(c) => u64::try_from(const_of(func, *c)?)
                        .ok()
                        .filter(|&k| k >= 1)?,
                };
                let size = layout.size(ty).ok()?.checked_mul(count)?;
                return (size > 0).then_some((v, size));
            }
            Inst::Copy { operand, .. }
            | Inst::Cast {
                op: CastOp::PtrToPtr,
                operand,
                ..
            } => v = *operand,
            Inst::GEP { base, .. } => v = *base,
            _ => return None,
        }
    }
    None
}

/// Whether every use of the slot family is one the module documentation
/// admits ("the caller's slot").
fn slot_contained(
    layout: &FsymLayout<'_>,
    module: &Module,
    func: &Function,
    uses: &HashMap<ValueId, Vec<(usize, usize)>>,
    family: &Derived,
    size: u64,
) -> Result<(), &'static str> {
    if family.pointers().iter().any(|(_, off)| *off >= size) {
        return Err("an address derived outside the slot");
    }
    for (v, _) in family.pointers() {
        for &(bi, ni) in uses.get(&v).map(Vec::as_slice).unwrap_or_default() {
            let node = &func.blocks[bi].body[ni];
            match &node.inst {
                Inst::Load {
                    ptr,
                    volatile: false,
                    ..
                } if *ptr == v => {}
                Inst::Store {
                    ptr,
                    value,
                    volatile: false,
                    ..
                } if *ptr == v && !family.has(value) => {}
                Inst::ExtractField { aggregate, .. } if *aggregate == v => {}
                Inst::InsertField {
                    aggregate, value, ..
                } if *aggregate == v && !family.has(value) => {
                    if node.results.iter().any(|r| uses.contains_key(r)) {
                        return Err("a write-through whose result is used");
                    }
                }
                Inst::Copy { .. }
                | Inst::Cast {
                    op: CastOp::PtrToPtr | CastOp::PtrToInt,
                    ..
                }
                | Inst::GEP { .. } => {
                    if !node.results.iter().all(|r| family.has(r)) {
                        return Err("a derived address outside the family");
                    }
                }
                Inst::Call { callee, args } => {
                    let callee = module
                        .function_by_id(*callee)
                        .filter(|f| !f.is_declaration())
                        .ok_or("passed to a function without a body")?;
                    if !matches!(
                        callee.linkage,
                        Linkage::External | Linkage::Internal | Linkage::Private
                    ) {
                        return Err("passed to a function another definition may replace");
                    }
                    for (j, a) in args.iter().enumerate() {
                        if family.has(a) {
                            param_shape(layout, module, callee, j)?;
                        }
                    }
                }
                _ => return Err("the address escapes"),
            }
        }
    }
    Ok(())
}

/// Rebuild the caller the witness claims (module documentation).
pub(super) fn rebuild_argpromo(
    module: &Module,
    source: &Function,
    witness: &ArgPromoWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let layout = FsymLayout::new(module);
    // The new signatures and functions: fresh ids, each named by a site.
    let mut ids: HashSet<FuncId> = module.functions.iter().map(|f| f.id).collect();
    let mut names: HashSet<&str> = module.functions.iter().map(|f| f.name.as_str()).collect();
    for f in &witness.new_functions {
        if !ids.insert(f.id) || !names.insert(f.name.as_str()) {
            return Err(refuse(0, "a new function reuses an id or a name"));
        }
        if !witness.sites.iter().any(|s| s.clone == f.id) {
            return Err(refuse(0, "a new function no site calls"));
        }
    }
    for (k, t) in witness.new_func_types.iter().enumerate() {
        if module.func_types.contains(t) || witness.new_func_types[..k].contains(t) {
            return Err(refuse(0, "a new signature the table already holds"));
        }
        let id = module.func_types.len() + k;
        if !witness
            .new_functions
            .iter()
            .any(|f| f.ty.index() as usize == id)
        {
            return Err(refuse(0, "a new signature no new function has"));
        }
    }
    // The module with the new clones, so a call of one reads as a call of a
    // function with a body (its results are never poison).
    let mut extended = module.clone();
    extended
        .functions
        .extend(witness.new_functions.iter().cloned());
    extended
        .func_types
        .extend(witness.new_func_types.iter().cloned());
    let mut cur = source.clone();
    let mut checked: HashMap<FuncId, Vec<ArgPromoParam>> = HashMap::new();
    for (s, site) in witness.sites.iter().enumerate() {
        let positions = block_positions(&cur);
        let bi = *positions
            .get(&site.block)
            .ok_or_else(|| refuse(s, "no such block"))?;
        let call = cur.blocks[bi]
            .body
            .get(site.index)
            .ok_or_else(|| refuse(s, "no such instruction"))?
            .clone();
        let Inst::Call { callee, args } = &call.inst else {
            return Err(refuse(s, "not a plain direct call"));
        };
        // An annotation or context describes this call of this callee with
        // these arguments, not the clone's call.
        if !call.proofs.is_empty() || call.proof_context.is_some() {
            return Err(refuse(
                s,
                "the call carries a proof annotation or proof context",
            ));
        }
        if *callee != site.callee {
            return Err(refuse(s, "the call names another callee"));
        }
        let (func, sig) = admit(module, *callee).map_err(|why| refuse(s, why))?;
        if site.params.is_empty()
            || site.params.windows(2).any(|w| w[0].index >= w[1].index)
            || site.params.iter().any(|p| p.index >= args.len())
            || call.results.len() != sig.returns.len()
        {
            return Err(refuse(s, "the plan's parameters are not the call's"));
        }
        let uses = uses_of(&cur);
        let defined = super::sroa::defined_values(&extended, &cur);
        let mut shapes = Vec::new();
        for p in &site.params {
            let shape = param_shape(&layout, module, func, p.index)
                .map_err(|why| refuse(s, format!("parameter {}: {why}", p.index)))?;
            if shape.reads != p.reads || shape.writes != p.writes {
                return Err(refuse(
                    s,
                    format!("parameter {}: the fields are not the callee's", p.index),
                ));
            }
            let arg = args[p.index];
            let aty = pointer_type(module, &cur, arg)
                .ok_or_else(|| refuse(s, "the argument type is unknown"))?;
            let (address, at) = if record(&aty) {
                if !shape.by_value || sig.params.get(p.index) != Some(&aty) {
                    return Err(refuse(
                        s,
                        "the value argument does not have its declared aggregate type",
                    ));
                }
                value_snapshot(&cur, arg, &aty).ok_or_else(|| {
                    refuse(s, "the value argument is not a nonvolatile typed load")
                })?
            } else {
                if !thin_pointer(&aty) {
                    return Err(refuse(
                        s,
                        "the argument is neither a thin pointer nor an aggregate snapshot",
                    ));
                }
                (arg, (bi, site.index))
            };
            let (root, size) = slot_root(&layout, &cur, address)
                .ok_or_else(|| refuse(s, "the argument is not derived from a slot"))?;
            let family = derived(&layout, module, &cur, &uses, root)
                .map_err(|why| refuse(s, format!("the slot: {why}")))?;
            let o = *family
                .offsets
                .get(&address)
                .ok_or_else(|| refuse(s, "the argument is not in its slot's family"))?;
            if o.checked_add(shape.extent).is_none_or(|end| end > size) {
                return Err(refuse(s, "a field lies outside the slot"));
            }
            if args
                .iter()
                .enumerate()
                .any(|(j, a)| j != p.index && family.has(a))
            {
                return Err(refuse(s, "another argument is derived from the slot"));
            }
            slot_contained(&layout, &extended, &cur, &uses, &family, size)
                .map_err(|why| refuse(s, format!("the slot: {why}")))?;
            for f in &p.reads {
                let fsize = layout
                    .size(&f.ty)
                    .map_err(|_| refuse(s, "a field has no size"))?;
                for byte in o + f.offset..o + f.offset + fsize {
                    if !byte_written(
                        &layout,
                        module,
                        &cur,
                        &family,
                        root,
                        &defined,
                        at,
                        byte,
                        (o + f.offset, &f.ty),
                    ) {
                        return Err(refuse(
                            s,
                            format!(
                                "byte {byte} of the slot, copied in for {}@{}, may be poison \
                                 at the call",
                                f.ty, f.offset
                            ),
                        ));
                    }
                }
            }
            shapes.push(shape);
        }
        check_clone(
            &layout,
            module,
            witness,
            s,
            site,
            func,
            sig,
            &shapes,
            &mut checked,
        )?;
        // The rewrite.
        let mut fresh = Fresh(first_fresh(&cur));
        let template = |inst: Inst, results: Vec<ValueId>| {
            let mut n = call.clone();
            n.inst = inst;
            n.results = results;
            n.proofs.clear();
            n.proof_context = None;
            n
        };
        let mut before: Vec<InstrNode> = Vec::new();
        let mut bases = Vec::new();
        let mut new_args: Vec<ValueId> = Vec::new();
        let mut loaded: Vec<Vec<ValueId>> = Vec::new();
        for p in &site.params {
            let arg = args[p.index];
            let aty = pointer_type(module, &cur, arg)
                .ok_or_else(|| refuse(s, "the argument type is unknown"))?;
            if record(&aty) {
                let entry = func
                    .blocks
                    .iter()
                    .find(|b| b.id == func.entry)
                    .ok_or_else(|| refuse(s, "the callee has no entry"))?;
                let param = entry.params[p.index].0;
                let mut vals = Vec::new();
                for f in &p.reads {
                    let field = func
                        .blocks
                        .iter()
                        .flat_map(|b| &b.body)
                        .find_map(|n| {
                            let (field, offset, ty) =
                                value_lane(&layout, module, func, param, &aty, &n.inst)?;
                            (offset == f.offset && ty == f.ty).then_some(field)
                        })
                        .ok_or_else(|| refuse(s, "the field has no source lane"))?;
                    let inst = if matches!(aty, Ty::Array(..)) {
                        let index = fresh.next();
                        before.push(template(
                            Inst::Const {
                                ty: Ty::Usize,
                                value: Constant::Int(i128::from(field)),
                            },
                            vec![index],
                        ));
                        Inst::ExtractElement {
                            ty: f.ty.clone(),
                            array: arg,
                            index,
                        }
                    } else {
                        Inst::ExtractField {
                            ty: f.ty.clone(),
                            aggregate: arg,
                            field,
                        }
                    };
                    let v = fresh.next();
                    before.push(template(inst, vec![v]));
                    vals.push(v);
                }
                bases.push(arg); // Value parameters have no copied-out fields.
                loaded.push(vals);
                continue;
            }
            let base = if aty == Ty::Ptr {
                arg
            } else {
                let b = fresh.next();
                before.push(template(
                    Inst::Cast {
                        op: CastOp::PtrToPtr,
                        src_ty: aty,
                        dst_ty: Ty::Ptr,
                        operand: arg,
                    },
                    vec![b],
                ));
                b
            };
            let mut vals = Vec::new();
            for f in &p.reads {
                let mut extra = Vec::new();
                let at = address(&mut fresh, base, f.offset, &mut extra);
                before.extend(extra.into_iter().map(|n| template(n.inst, n.results)));
                let v = fresh.next();
                before.push(template(
                    Inst::Load {
                        ty: f.ty.clone(),
                        ptr: at,
                        volatile: false,
                        align: Some(1),
                    },
                    vec![v],
                ));
                vals.push(v);
            }
            bases.push(base);
            loaded.push(vals);
        }
        for (j, a) in args.iter().enumerate() {
            match site.params.iter().position(|p| p.index == j) {
                Some(k) => new_args.extend(loaded[k].iter().copied()),
                None => new_args.push(*a),
            }
        }
        let mut results = call.results.clone();
        let mut outs: Vec<Vec<ValueId>> = Vec::new();
        for p in &site.params {
            let o: Vec<ValueId> = p.writes.iter().map(|_| fresh.next()).collect();
            results.extend(o.iter().copied());
            outs.push(o);
        }
        let mut after: Vec<InstrNode> = Vec::new();
        for ((p, base), o) in site.params.iter().zip(&bases).zip(&outs) {
            for (f, v) in p.writes.iter().zip(o) {
                let mut extra = Vec::new();
                let at = address(&mut fresh, *base, f.offset, &mut extra);
                after.extend(extra.into_iter().map(|n| template(n.inst, n.results)));
                after.push(template(
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
            callee: site.clone,
            args: new_args,
        };
        redirected.results = results;
        let body = &mut cur.blocks[bi].body;
        let tail: Vec<InstrNode> = body.drain(site.index..).skip(1).collect();
        body.extend(before);
        body.push(redirected);
        body.extend(after);
        body.extend(tail);
    }
    let verdict = WitnessVerdict {
        exact: 0,
        refinements: witness.sites.len(),
    };
    Ok((cur, verdict))
}

#[cfg(test)]
#[path = "trust_ir_mid_tv_argpromo_tests.rs"]
mod tests;
