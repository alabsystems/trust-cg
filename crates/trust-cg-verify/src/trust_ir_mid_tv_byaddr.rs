// trust-cg-verify/trust_ir_mid_tv_byaddr.rs - an array parameter read through its address
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The checker of by-address cloning ([`ByAddrWitness`]): a direct `call`
//! that passes a pointer for an ARRAY parameter (`[T x n]`, the rustc
//! bridge's spelling of an aggregate passed by value, which the wasm32 lane
//! passes by the address of its bytes and the differential's view reads as
//! the load of the pointee's bytes at the call) calls a clone of the callee
//! that takes the address (`ptr`) and loads the lanes it reads. The bridge
//! opens such a callee by copying the array's lanes into a frame slot of its
//! own (`insertfield` of each `extractfield`) and reads the fields from the
//! slot; when nothing else can write memory in the callee, the clone reads
//! them from the caller's bytes instead and the slot goes (a `#[repr(packed)]`
//! value's fifteen byte copies and four field loads become four loads).
//!
//! For current typed array arguments, only the value of an immediately
//! preceding nonvolatile load may supply its address. The existing callee
//! effect restriction keeps those bytes unchanged during the call. Typed
//! lane/store copies are independently matched at their actual byte offsets;
//! a stale snapshot or a mismatched copy is refused.
//!
//! **The callee admits a clone** (re-derived per site): a plain `call` (not
//! `invoke`, an indirect or a no-unwind call) carrying no proof annotation
//! or proof context, of a function defined in the module, other than the
//! caller, under a crate-private name (`<prefix>.tcg.crate.<16 hex>`),
//! strong (`external`) with hidden visibility, not variadic, naked or
//! feature-stating, no parameter passed by copy, no proof annotation, call
//! proof context, summary, source provenance, body gate or module
//! obligation naming it (nor an unscoped obligation or a spec module), entry
//! parameters of the declared types (thin pointers may be of other pointer
//! types here, but the clone declares the signature's types and keeps the
//! entry's, so a site is refused whose clone keeps a parameter of another
//! entry type; a promoted parameter is an array, so no thin pointer of
//! another type survives, OD-82) and an entry block no edge targets.
//!
//! **Each promoted parameter** `p` (index `i`) has an array type `[T x n]`
//! whose element `T` is an integer, float, `bool`, `char` or thin pointer
//! of known size `s`; the call's argument is a thin pointer or the adjacent
//! typed snapshot above; and every use of `p` in the callee is a constant
//! lane read: `extractfield [T x n] p, j` or `extractelement T p, j`, `j < n`,
//! in the callee's entry block, inside its PROLOGUE: the longest prefix of
//! the entry block made only of these forms, none of which writes memory
//! but a fresh slot — count-free `alloca`s, constants, lane reads of
//! promoted parameters, `insertfield`s through (and plain stores to) an
//! `alloca` of the prologue itself or a `gep` of one by constant indices,
//! `gep`s, casts, copies, `binop`s and `unop`s (integer or float), integer
//! comparisons (`icmp`), selects and plain loads. Any other form ends it,
//! even one that writes no memory (`globaladdr`, `nullptr`, `undef`,
//! `overflow`, `fcmp`) or only a fresh slot (a `memset` of one).
//!
//! **The clone** of callee `F` for the plan (the promoted indices, each
//! with or without a SLOT) is `F` with each promoted entry parameter typed
//! `ptr` (its value id kept), each `extractfield [T x n] p, j` replaced by
//! `o = const usize j * s; g = gep u8, p, [o]; x = load T, g` (align 1, not
//! volatile; `x` the read's own result), and, for a parameter with a slot
//! `S`: the `insertfield`s into `S` removed, the `alloca` of `S` removed,
//! every lane read whose every use is such an `insertfield` removed (not
//! loaded), and every other use of `S` replaced by `p`. Fresh values are
//! minted in that order (per read loaded, `o` then `g`, in block order)
//! from one past the largest value `F` names. Signature: the declared one with each promoted
//! parameter `ptr`; a strong hidden symbol named
//! `<prefix>.tcg.ap<h>.tcg.crate.<tag>` (argument promotion's clone mark, so
//! the wasm32 lane's re-validation withdraws it as one of those), `h` the
//! FNV-1a digest of the plan's text `ba:` then `<i>` (and `s` with a slot)
//! and `|` per parameter; the promoted parameters' attributes default, no
//! `readonly`/`readnone` claim, not `retained`; everything else as `F`.
//!
//! **A slot `S`** of a promoted `p` of type `[T x n]`: an `alloca [T x n]`
//! (count-free) of the prologue, written in the prologue by exactly one
//! `insertfield [T x n] S, j, x_j` per lane `j < n`, `x_j` an
//! `extractfield [T x n] p, j` (each `insertfield`'s result unused); every
//! other use of `S` (in any block) is the address of a plain load, or of a
//! `gep` by constant indices whose results are only such addresses (one
//! level). And the callee writes no memory but its own fresh slots
//! anywhere and calls nothing, checked by an ALLOWLIST of its instructions:
//! every store, `memcopy` and `memset` writes through an `alloca` of the
//! callee (or a `gep` of one by constant indices); every `insertfield` does
//! too, or its aggregate operand is one this module types as an aggregate
//! VALUE it names (a struct, tuple, array, record or enum), which no lane
//! writes through. Any other `insertfield` refuses: the lanes write the
//! field through a POINTER CARRIER (a thin pointer, or on wasm32 an `i64`
//! or `u64` read as the address of the aggregate's bytes, as
//! `trust-cg-irmid`'s `escape::is_pointer_carrier` names them), and a type
//! not named is never assumed to be a value. Every other instruction is a
//! count-free `alloca`, a plain (non-atomic, not volatile) load, or a
//! value-only form (`const`, `nullptr`, `undef`, `globaladdr`, `binop`,
//! `unop`, `overflow`, `icmp`, `fcmp`, a cast, `copy`, `select`, `gep`,
//! the pointer part forms, `extractfield`, `extractelement`,
//! `insertelement`, `make_aggregate`, `array_splat`, `assume`, `assert`,
//! `unreachable`) or a terminator (`br`, `condbr`, `switch`, `return`).
//! Every other form refuses: a call of any kind, an atomic access or
//! fence, `drop`, `dealloc`, `retain`/`release`, a heap allocation, a
//! coroutine suspension, a dialect operation, the borrow and frame forms
//! and the unwinding forms.
//!
//! **The rewrite**, at the call: per promoted argument whose type is not
//! `ptr`, a fresh `ptrtoptr` of it to `ptr` before the call (minted from
//! the caller's first free value, in parameter order); the call names the
//! clone and passes those.
//!
//! Each site is a REFINEMENT of the view's semantics. The source binds `p`
//! to the bytes at the argument at the call (undefined behaviour unless
//! each is initialised and decodes); the clone reads each lane it extracts
//! from those bytes, in the prologue, after which only writes to the clone's
//! own fresh slots have run (allocations made during the call, which the
//! argument cannot point into), so it reads what the source extracts (a
//! lane over an uninitialised byte loads poison where the source raised
//! undefined behaviour). With a slot, the source reads the slot's bytes,
//! all copied from the array; the clone reads the argument's bytes at the
//! same offsets, which nothing writes while the clone runs: it writes only
//! its own fresh slots and calls nothing. That rests on the allowlist
//! naming every form that writes memory as the lanes lower it; the
//! differential's view does not model an integer carrier's write and stops
//! both runs as a type error, so it cannot catch a gap there. The wasm32
//! lane passes such an array by its address either way.

use std::collections::{HashMap, HashSet};

use trust_ir::{
    BlockId, CastOp, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Linkage, Module,
    ParamAttrs, PassMode, Ty, ValueId, Visibility,
};

use super::argpromo::ARGPROMO_CLONE_MARK;
use super::{MidTvError, WitnessVerdict, block_positions};
use crate::fsym_layout::FsymLayout;
use crate::wasm_internal_abi::CRATE_PRIVATE_MARK as CRATE_MARK;

/// One promoted parameter: its index, and the slot the clone replaces by it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ByAddrParam {
    pub index: usize,
    pub slot: Option<ValueId>,
}

/// One call redirected to a clone, in the function the witness's earlier
/// sites produced: the call's position, its callee and clone, the plan, and
/// the fresh `ptrtoptr`s of its arguments (per promoted parameter whose
/// argument is not a `ptr`, in parameter order).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ByAddrSite {
    pub block: BlockId,
    pub index: usize,
    pub callee: FuncId,
    pub clone: FuncId,
    pub params: Vec<ByAddrParam>,
    pub casts: Vec<ValueId>,
}

/// By-address cloning's claim about one caller, with the signatures and
/// clones it appends to the module.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ByAddrWitness {
    pub sites: Vec<ByAddrSite>,
    pub new_func_types: Vec<FuncTy>,
    pub new_functions: Vec<Function>,
}

impl ByAddrWitness {
    /// Number of claimed rewrites (redirected calls).
    pub fn rewrite_count(&self) -> usize {
        self.sites.len()
    }
}

fn refuse(site: usize, why: impl Into<String>) -> MidTvError {
    MidTvError::NotByAddr {
        site,
        why: why.into(),
    }
}

fn thin_pointer(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
    )
}

fn scalar(ty: &Ty) -> bool {
    ty.is_integer() || ty.is_float() || matches!(ty, Ty::Bool | Ty::Char) || thin_pointer(ty)
}

/// An aggregate VALUE type (module documentation, a slot): an `insertfield`
/// over a value of one writes no memory. An allowlist that names no pointer
/// carrier (a thin pointer, or the wasm32 lane's `i64`/`u64` address, which
/// the lanes write the field through); a type not named refuses.
fn value_aggregate(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Struct(_) | Ty::Tuple(_) | Ty::Array(..) | Ty::Record(_) | Ty::Enum(_)
    )
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

/// The clone's name for `callee` under `params` (module documentation).
pub fn byaddr_clone_name(callee: &str, params: &[ByAddrParam]) -> Option<String> {
    let (prefix, tag) = crate_split(callee)?;
    let mut text = String::from("ba:");
    for p in params {
        text.push_str(&p.index.to_string());
        if p.slot.is_some() {
            text.push('s');
        }
        text.push('|');
    }
    let mut hash: u32 = 0x811c_9dc5;
    for byte in text.bytes() {
        hash ^= u32::from(byte);
        hash = hash.wrapping_mul(0x0100_0193);
    }
    Some(format!(
        "{prefix}{ARGPROMO_CLONE_MARK}{hash:08x}{CRATE_MARK}{tag}"
    ))
}

/// The callee as a clone's template (module documentation).
fn admit(
    module: &Module,
    caller: FuncId,
    callee: FuncId,
) -> Result<(&Function, &FuncTy), &'static str> {
    if callee == caller {
        return Err("the call is the caller's own");
    }
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

/// The single-result definitions of `func`.
fn defs(func: &Function) -> HashMap<ValueId, &Inst> {
    let mut out = HashMap::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        if let [r] = node.results.as_slice() {
            out.insert(*r, &node.inst);
        }
    }
    out
}

/// This module's typing of `func`'s values: block parameters and the forms
/// whose result type is a field of the instruction.
fn types_of(func: &Function) -> HashMap<ValueId, Ty> {
    let mut out = HashMap::new();
    for block in &func.blocks {
        for (v, t) in &block.params {
            out.insert(*v, t.clone());
        }
        for node in &block.body {
            let [r] = node.results.as_slice() else {
                continue;
            };
            let ty = match &node.inst {
                Inst::Copy { ty, .. } | Inst::Load { ty, .. } | Inst::Const { ty, .. } => {
                    ty.clone()
                }
                Inst::Cast { dst_ty, .. } => dst_ty.clone(),
                Inst::Alloca { .. } | Inst::GEP { .. } | Inst::GlobalAddr { .. } => Ty::Ptr,
                _ => continue,
            };
            out.insert(*r, ty);
        }
    }
    out
}

/// The length of the callee's prologue (the longest prefix of its entry
/// block made only of the forms the module documentation lists), and the
/// slots the prefix allocates.
fn prologue(func: &Function, promoted: &HashSet<ValueId>) -> (usize, HashSet<ValueId>) {
    let Some(entry) = func.blocks.iter().find(|b| b.id == func.entry) else {
        return (0, HashSet::new());
    };
    let defs = defs(func);
    let mut slots: HashSet<ValueId> = HashSet::new();
    // A slot of the prefix, or a `gep` of one by constant indices.
    let into_slot = |slots: &HashSet<ValueId>, ptr: &ValueId| {
        slots.contains(ptr)
            || matches!(
                defs.get(ptr),
                Some(Inst::GEP { base, indices, .. }) if slots.contains(base)
                    && indices.iter().all(|i| matches!(defs.get(i), Some(Inst::Const { .. })))
            )
    };
    for (n, node) in entry.body.iter().enumerate() {
        let ok = match &node.inst {
            Inst::Alloca { count: None, .. } => {
                slots.extend(node.results.iter().copied());
                true
            }
            Inst::Const { .. }
            | Inst::GEP { .. }
            | Inst::Cast { .. }
            | Inst::Copy { .. }
            | Inst::BinOp { .. }
            | Inst::UnOp { .. }
            | Inst::ICmp { .. }
            | Inst::Select { .. } => true,
            Inst::Load {
                volatile: false, ..
            } => true,
            Inst::ExtractField { aggregate, .. } => promoted.contains(aggregate),
            Inst::ExtractElement { array, .. } => promoted.contains(array),
            Inst::InsertField { aggregate, .. } => into_slot(&slots, aggregate),
            Inst::Store {
                ptr,
                volatile: false,
                ..
            } => into_slot(&slots, ptr),
            _ => false,
        };
        if !ok {
            return (n, slots);
        }
    }
    (entry.body.len(), slots)
}

/// Whether `func` writes memory only through its own `alloca`s (or `gep`s
/// of them by constant indices) and calls nothing (module documentation, a
/// slot).
fn writes_only_own_slots(func: &Function) -> bool {
    let defs = defs(func);
    let types = types_of(func);
    let own = |ptr: &ValueId| match defs.get(ptr) {
        Some(Inst::Alloca { .. }) => true,
        Some(Inst::GEP { base, indices, .. }) => {
            matches!(defs.get(base), Some(Inst::Alloca { .. }))
                && indices
                    .iter()
                    .all(|i| matches!(defs.get(i), Some(Inst::Const { .. })))
        }
        _ => false,
    };
    func.blocks
        .iter()
        .flat_map(|b| &b.body)
        .all(|node| match &node.inst {
            Inst::Store { ptr, .. } => own(ptr),
            // A write-through `insertfield` writes its carrier's bytes, so
            // only into the callee's own slots; one over an aggregate value
            // of a type the allowlist names writes no memory.
            Inst::InsertField { aggregate, .. } => {
                own(aggregate) || types.get(aggregate).is_some_and(value_aggregate)
            }
            Inst::MemCopy { dst, .. } | Inst::MemSet { dst, .. } => own(dst),
            Inst::Alloca { count: None, .. }
            | Inst::Load {
                volatile: false, ..
            } => true,
            other => value_only(other),
        })
}

/// Whether `inst` is one of the forms that touch no memory and call nothing
/// (module documentation, a slot): an ALLOWLIST, so a form not named here
/// (`dealloc`, `drop`, `retain`, a dialect operation, any call) refuses.
fn value_only(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::Const { .. }
            | Inst::NullPtr
            | Inst::Undef { .. }
            | Inst::GlobalAddr { .. }
            | Inst::BinOp { .. }
            | Inst::UnOp { .. }
            | Inst::Overflow { .. }
            | Inst::ICmp { .. }
            | Inst::FCmp { .. }
            | Inst::Cast { .. }
            | Inst::Copy { .. }
            | Inst::Select { .. }
            | Inst::GEP { .. }
            | Inst::PtrData { .. }
            | Inst::PtrMetadata { .. }
            | Inst::PtrFromParts { .. }
            | Inst::ExtractField { .. }
            | Inst::ExtractElement { .. }
            | Inst::InsertElement { .. }
            | Inst::MakeAggregate { .. }
            | Inst::ArraySplat { .. }
            | Inst::Assume { .. }
            | Inst::Assert { .. }
            | Inst::Unreachable
            | Inst::Br { .. }
            | Inst::CondBr { .. }
            | Inst::Switch { .. }
            | Inst::Return { .. }
    )
}

/// Why `p` (entry parameter `index` of `func`) cannot be promoted under the
/// plan entry `param`, or its array's element type, size and length.
/// A constant lane read in either the legacy declared-array form or
/// current typed extractelement form. No variable or out-of-bounds lane.
fn read_lane(module: &Module, func: &Function, p: ValueId, array: &Ty, inst: &Inst) -> Option<u32> {
    let Ty::Array(elem, length) = array else {
        return None;
    };
    let field = match inst {
        Inst::ExtractField {
            ty,
            aggregate,
            field,
        } if *aggregate == p && ty == array => *field,
        Inst::ExtractElement { ty, array, index }
            if *array == p && module.ty(*elem) == Some(ty) =>
        {
            let def = func
                .blocks
                .iter()
                .flat_map(|b| &b.body)
                .find(|n| n.results.as_slice() == [*index])?;
            let Inst::Const {
                ty: Ty::Usize,
                value: Constant::Int(i),
            } = def.inst
            else {
                return None;
            };
            u32::try_from(i).ok()?
        }
        _ => return None,
    };
    (u64::from(field) < *length).then_some(field)
}

/// A store that copies exactly the corresponding lane of the parameter
/// into the array slot. The byte offset is derived from the GEP's actual
/// pointee size, not inferred from its spelling.
fn copied_lane(
    module: &Module,
    func: &Function,
    p: ValueId,
    array: &Ty,
    slot: ValueId,
    inst: &Inst,
) -> Option<u32> {
    let def = |v| {
        func.blocks
            .iter()
            .flat_map(|b| &b.body)
            .find(|n| n.results.as_slice() == [v])
            .map(|n| &n.inst)
    };
    match inst {
        Inst::InsertField {
            ty,
            aggregate,
            field,
            value,
        } if *aggregate == slot && ty == array => {
            (read_lane(module, func, p, array, def(*value)?)? == *field).then_some(*field)
        }
        Inst::Store {
            ty,
            ptr,
            value,
            volatile: false,
            ..
        } => {
            let Ty::Array(elem, _) = array else {
                return None;
            };
            if module.ty(*elem) != Some(ty) {
                return None;
            }
            let field = read_lane(module, func, p, array, def(*value)?)?;
            let offset = if *ptr == slot {
                0
            } else {
                let Inst::GEP {
                    pointee_ty,
                    base,
                    indices,
                    ..
                } = def(*ptr)?
                else {
                    return None;
                };
                if *base != slot {
                    return None;
                }
                let mut index = 0u64;
                for i in indices {
                    let Inst::Const {
                        value: Constant::Int(k),
                        ty,
                    } = def(*i)?
                    else {
                        return None;
                    };
                    if !ty.is_integer() {
                        return None;
                    }
                    index = index.checked_add(u64::try_from(*k).ok()?)?;
                }
                FsymLayout::new(module)
                    .size(pointee_ty)
                    .ok()?
                    .checked_mul(index)?
            };
            (offset == u64::from(field).checked_mul(FsymLayout::new(module).size(ty).ok()?)?)
                .then_some(field)
        }
        _ => None,
    }
}

/// A current by-value array may be replaced by its source address only
/// for an immediately preceding nonvolatile load of the exact parameter
/// type. No intervening write can change the captured bytes.
fn snapshot_address(
    func: &Function,
    bi: usize,
    ni: usize,
    arg: ValueId,
    ty: &Ty,
) -> Option<ValueId> {
    let node = func.blocks.get(bi)?.body.get(ni.checked_sub(1)?)?;
    if node.results.as_slice() != [arg] {
        return None;
    }
    match &node.inst {
        Inst::Load {
            ty: loaded,
            ptr,
            volatile: false,
            ..
        } if loaded == ty => Some(*ptr),
        _ => None,
    }
}

fn check_param(
    layout: &FsymLayout<'_>,
    module: &Module,
    func: &Function,
    promoted: &HashSet<ValueId>,
    param: &ByAddrParam,
) -> Result<(Ty, u64, u64), String> {
    let entry = func
        .blocks
        .iter()
        .find(|b| b.id == func.entry)
        .ok_or("no entry block")?;
    let (p, ty) = entry
        .params
        .get(param.index)
        .ok_or("no such parameter")?
        .clone();
    let Ty::Array(elem, length) = &ty else {
        return Err("not an array".into());
    };
    let elem = module
        .ty(*elem)
        .ok_or("the element type is not in the module's table")?
        .clone();
    if !scalar(&elem) {
        return Err("the element is not a scalar".into());
    }
    let size = layout
        .size(&elem)
        .map_err(|_| "the element's size is unknown")?;
    let (len, slots) = prologue(func, promoted);
    let entry_index = func
        .blocks
        .iter()
        .position(|b| b.id == func.entry)
        .ok_or("no entry block")?;
    // Every use of `p` is a lane read of it in the prologue.
    for (bi, block) in func.blocks.iter().enumerate() {
        for (ni, node) in block.body.iter().enumerate() {
            let mut uses = false;
            node.inst.visit_value_operands(|v| uses |= v == p);
            if !uses {
                continue;
            }
            let lane_read = read_lane(module, func, p, &ty, &node.inst).is_some();
            if !lane_read || bi != entry_index || ni >= len {
                return Err("a use of the parameter is not a lane read in the prologue".into());
            }
        }
    }
    if let Some(slot) = param.slot {
        check_slot(
            module,
            func,
            p,
            &ty,
            *length,
            slot,
            &slots,
            len,
            entry_index,
        )?;
    }
    Ok((elem, size, *length))
}

/// The slot conditions (module documentation).
#[allow(clippy::too_many_arguments)]
fn check_slot(
    module: &Module,
    func: &Function,
    p: ValueId,
    ty: &Ty,
    length: u64,
    slot: ValueId,
    prologue_slots: &HashSet<ValueId>,
    prologue_len: usize,
    entry_index: usize,
) -> Result<(), String> {
    let defs = defs(func);
    if !prologue_slots.contains(&slot)
        || !matches!(defs.get(&slot), Some(Inst::Alloca { ty: t, count: None, .. }) if t == ty)
    {
        return Err("the slot is not a count-free alloca of the array type in the prologue".into());
    }
    let mut used: HashSet<ValueId> = HashSet::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        node.inst.visit_value_operands(|v| {
            used.insert(v);
        });
    }
    let constant = |v: &ValueId| matches!(defs.get(v), Some(Inst::Const { .. }));
    // The `gep`s of the slot by constant indices.
    let geps: HashSet<ValueId> = func
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .filter(|n| {
            matches!(&n.inst, Inst::GEP { base, indices, .. }
                if *base == slot && indices.iter().all(constant))
        })
        .flat_map(|n| n.results.iter().copied())
        .collect();
    let mut lanes: HashSet<u64> = HashSet::new();
    for (bi, block) in func.blocks.iter().enumerate() {
        for (ni, node) in block.body.iter().enumerate() {
            let mut touches = false;
            node.inst
                .visit_value_operands(|v| touches |= v == slot || geps.contains(&v));
            if !touches {
                continue;
            }
            if let Some(field) = copied_lane(module, func, p, ty, slot, &node.inst) {
                if bi != entry_index
                    || ni >= prologue_len
                    || node.results.iter().any(|r| used.contains(r))
                    || !lanes.insert(u64::from(field))
                {
                    return Err(
                        "a write of the slot is not one copy of a lane in the prologue".into(),
                    );
                }
                continue;
            }
            match &node.inst {
                Inst::Load { ptr, .. } if *ptr == slot || geps.contains(ptr) => {}
                Inst::GEP { base, indices, .. }
                    if *base == slot && indices.iter().all(constant) =>
                {
                    for r in &node.results {
                        let allowed = func.blocks.iter().flat_map(|b| &b.body).all(|n| {
                            let mut reads = false;
                            n.inst.visit_value_operands(|v| reads |= v == *r);
                            !reads
                                || matches!(&n.inst, Inst::Load { ptr, .. } if ptr == r)
                                || copied_lane(module, func, p, ty, slot, &n.inst).is_some()
                        });
                        if !allowed {
                            return Err("a gep of the slot escapes its copies and loads".into());
                        }
                    }
                }
                _ => return Err("the slot is used other than by its lane copies and loads".into()),
            }
        }
    }
    if lanes.len() as u64 != length {
        return Err("the slot is not written in every lane".into());
    }
    if !writes_only_own_slots(func) {
        return Err("the callee writes memory other than its own slots, or calls".into());
    }
    Ok(())
}

/// One past the largest value `func` names (parameters, results, operands,
/// debug names).
fn first_free(func: &Function) -> u32 {
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

/// The clone of `func` under `params` (module documentation).
#[allow(clippy::too_many_arguments)]
fn derive_clone(
    module: &Module,
    func: &Function,
    params: &[ByAddrParam],
    lanes: &[(Ty, u64)],
    id: FuncId,
    name: String,
    ty: trust_ir::FuncTyId,
) -> Function {
    let mut clone = func.clone();
    clone.id = id;
    clone.name = name;
    clone.ty = ty;
    clone.linkage = Linkage::External;
    clone.visibility = Visibility::Hidden;
    clone.retained = false;
    clone.attrs.readonly = false;
    clone.attrs.readnone = false;
    if !clone.attrs.params.is_empty() {
        for p in params {
            if let Some(a) = clone.attrs.params.get_mut(p.index) {
                *a = ParamAttrs::default();
            }
        }
        if clone
            .attrs
            .params
            .iter()
            .all(|a| *a == ParamAttrs::default())
        {
            clone.attrs.params.clear();
        }
    }
    let entry_index = clone
        .blocks
        .iter()
        .position(|b| b.id == clone.entry)
        .expect("admitted: an entry block");
    let mut values: HashMap<ValueId, (Ty, u64)> = HashMap::new();
    let mut slots: HashMap<ValueId, ValueId> = HashMap::new();
    let mut arrays: HashMap<ValueId, Ty> = HashMap::new();
    for (p, lane) in params.iter().zip(lanes) {
        let (v, _) = clone.blocks[entry_index].params[p.index];
        arrays.insert(v, clone.blocks[entry_index].params[p.index].1.clone());
        clone.blocks[entry_index].params[p.index].1 = Ty::Ptr;
        values.insert(v, lane.clone());
        if let Some(s) = p.slot {
            slots.insert(s, v);
        }
    }
    // A lane read whose every use is a copy into a replaced slot goes with
    // the copy.
    let mut uses: HashMap<ValueId, Vec<&Inst>> = HashMap::new();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        node.inst
            .visit_value_operands(|v| uses.entry(v).or_default().push(&node.inst));
    }
    let copied = |inst: &Inst| {
        slots.iter().any(|(slot, parameter)| {
            copied_lane(module, func, *parameter, &arrays[parameter], *slot, inst).is_some()
        })
    };
    let dropped: HashSet<ValueId> = func
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .filter(|n| {
            arrays
                .iter()
                .any(|(p, ty)| read_lane(module, func, *p, ty, &n.inst).is_some())
        })
        .flat_map(|n| n.results.iter().copied())
        .filter(|r| {
            uses.get(r)
                .is_some_and(|list| list.iter().all(|i| copied(i)))
        })
        .collect();
    let mut next = first_free(func);
    for block in &mut clone.blocks {
        let body = std::mem::take(&mut block.body);
        let mut rebuilt = Vec::with_capacity(body.len());
        for mut node in body {
            if node.results.iter().any(|r| dropped.contains(r))
                || copied(&node.inst)
                || matches!(node.inst, Inst::Alloca { .. })
                    && node.results.iter().any(|r| slots.contains_key(r))
            {
                continue;
            }
            let read = arrays.iter().find_map(|(p, array)| {
                read_lane(module, func, *p, array, &node.inst).map(|field| (*p, field))
            });
            if let Some((base, field)) = read {
                let (elem, size) = values[&base].clone();
                let (o, g) = (ValueId::new(next), ValueId::new(next + 1));
                next += 2;
                let mut constant = node.clone();
                constant.inst = Inst::Const {
                    ty: Ty::Usize,
                    value: Constant::Int(i128::from(u64::from(field) * size)),
                };
                constant.results = vec![o];
                let mut gep = node.clone();
                gep.inst = Inst::GEP {
                    pointee_ty: Ty::U8,
                    base,
                    indices: vec![o],
                    inbounds: false,
                };
                gep.results = vec![g];
                node.inst = Inst::Load {
                    ty: elem,
                    ptr: g,
                    volatile: false,
                    align: Some(1),
                };
                rebuilt.extend([constant, gep, node]);
            } else {
                trust_ir::mem2reg::rewrite_node(&mut node, &slots);
                rebuilt.push(node);
            }
        }
        block.body = rebuilt;
    }
    if let Some(names) = &mut clone.value_names {
        names.retain(|(v, _)| !slots.contains_key(v));
    }
    clone
}

/// The clone's signature: the declared one with each promoted parameter
/// `ptr`.
fn clone_sig(sig: &FuncTy, params: &[ByAddrParam]) -> FuncTy {
    let mut out = sig.clone();
    for p in params {
        out.params[p.index] = Ty::Ptr;
    }
    out
}

pub(super) fn rebuild_byaddr(
    module: &Module,
    source: &Function,
    witness: &ByAddrWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let layout = FsymLayout::new(module);
    if witness.sites.is_empty() {
        return Err(refuse(0, "the witness claims no site"));
    }
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
    let table: Vec<&FuncTy> = module
        .func_types
        .iter()
        .chain(&witness.new_func_types)
        .collect();
    let mut cur = source.clone();
    let mut checked: HashMap<FuncId, Vec<ByAddrParam>> = HashMap::new();
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
        if !call.proofs.is_empty() || call.proof_context.is_some() {
            return Err(refuse(
                s,
                "the call carries a proof annotation or proof context",
            ));
        }
        if *callee != site.callee {
            return Err(refuse(s, "the call names another callee"));
        }
        let (func, sig) = admit(module, cur.id, *callee).map_err(|why| refuse(s, why))?;
        if site.params.is_empty()
            || site.params.windows(2).any(|w| w[0].index >= w[1].index)
            || site.params.iter().any(|p| p.index >= args.len())
            || call.results.len() != sig.returns.len()
            || args.len() != sig.params.len()
        {
            return Err(refuse(s, "the plan's parameters are not the call's"));
        }
        let entry = func
            .blocks
            .iter()
            .find(|b| b.id == func.entry)
            .ok_or_else(|| refuse(s, "no entry block"))?;
        let promoted: HashSet<ValueId> = site
            .params
            .iter()
            .map(|p| entry.params[p.index].0)
            .collect();
        let mut lanes = Vec::new();
        for p in &site.params {
            let (elem, size, _) = check_param(&layout, module, func, &promoted, p)
                .map_err(|why| refuse(s, format!("parameter {}: {why}", p.index)))?;
            lanes.push((elem, size));
        }
        // The kept parameters have their declared types at the entry: the
        // clone declares the signature's and keeps the entry's.
        if entry
            .params
            .iter()
            .zip(&sig.params)
            .enumerate()
            .any(|(j, ((_, t), d))| t != d && !site.params.iter().any(|p| p.index == j))
        {
            return Err(refuse(
                s,
                "a parameter the clone keeps has an entry type other than its declared one",
            ));
        }
        // The clone, new or in the module, is the derivation.
        let name = byaddr_clone_name(&func.name, &site.params)
            .ok_or_else(|| refuse(s, "the callee has no crate-private name"))?;
        let claimed = witness
            .new_functions
            .iter()
            .find(|f| f.id == site.clone)
            .or_else(|| module.function_by_id(site.clone))
            .ok_or_else(|| refuse(s, "the clone is neither new nor in the module"))?;
        match checked.get(&site.clone) {
            Some(plan) if *plan != site.params || claimed.name != name => {
                return Err(refuse(s, "two plans name one clone"));
            }
            Some(_) => {}
            None => {
                let csig = clone_sig(sig, &site.params);
                let ty_index = table
                    .iter()
                    .position(|t| **t == csig)
                    .ok_or_else(|| refuse(s, "the clone's signature is in no table"))?;
                let ty = trust_ir::FuncTyId::new(
                    u32::try_from(ty_index).map_err(|_| refuse(s, "too many signatures"))?,
                );
                let expected =
                    derive_clone(module, func, &site.params, &lanes, site.clone, name, ty);
                if *claimed != expected {
                    return Err(refuse(
                        s,
                        "the clone is not the callee's body under the plan",
                    ));
                }
                checked.insert(site.clone, site.params.clone());
            }
        }
        // The arguments: thin pointers, cast to `ptr` unless they are one.
        let caller_types = types_of(&cur);
        let mut fresh = first_free(&cur);
        let mut before: Vec<InstrNode> = Vec::new();
        let mut new_args = args.clone();
        let mut casts = Vec::new();
        for p in &site.params {
            let arg = args[p.index];
            let (arg, aty) = match caller_types.get(&arg) {
                Some(ty) if thin_pointer(ty) => (arg, ty.clone()),
                Some(ty) if sig.params.get(p.index) == Some(ty) => {
                    let address =
                        snapshot_address(&cur, bi, site.index, arg, ty).ok_or_else(|| {
                            refuse(s, "the array is not an adjacent immutable snapshot")
                        })?;
                    let aty = caller_types
                        .get(&address)
                        .filter(|t| thin_pointer(t))
                        .ok_or_else(|| refuse(s, "the snapshot has no thin address"))?;
                    (address, aty.clone())
                }
                _ => {
                    return Err(refuse(
                        s,
                        "the argument is not a thin pointer or typed array snapshot",
                    ));
                }
            };
            new_args[p.index] = arg;
            if aty != Ty::Ptr {
                let c = ValueId::new(fresh);
                fresh += 1;
                let mut node = call.clone();
                node.inst = Inst::Cast {
                    op: CastOp::PtrToPtr,
                    src_ty: aty,
                    dst_ty: Ty::Ptr,
                    operand: arg,
                };
                node.results = vec![c];
                node.proofs.clear();
                node.proof_context = None;
                before.push(node);
                new_args[p.index] = c;
                casts.push(c);
            }
        }
        if casts != site.casts {
            return Err(refuse(
                s,
                "the argument casts are not the claimed fresh values",
            ));
        }
        let mut redirected = call.clone();
        redirected.inst = Inst::Call {
            callee: site.clone,
            args: new_args,
        };
        before.push(redirected);
        cur.blocks[bi].body.splice(site.index..=site.index, before);
    }
    Ok((
        cur,
        WitnessVerdict {
            exact: 0,
            refinements: witness.sites.len(),
        },
    ))
}

#[cfg(test)]
#[path = "trust_ir_mid_tv_byaddr_tests.rs"]
mod tests;
