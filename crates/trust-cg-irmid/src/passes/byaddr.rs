// trust-cg-irmid/passes/byaddr.rs - an array parameter read through its address
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! By-address cloning: a call passing a pointer for an ARRAY parameter
//! (`[T x n]`: the rustc bridge's spelling of an aggregate passed by value,
//! which the wasm32 lane passes by the address of its bytes) calls a clone
//! of the callee that takes the address and loads the lanes it reads. The
//! bridge opens such a callee by copying every lane into a frame slot of
//! its own and reads the fields from the slot (`#[repr(packed)]`'s `sumpk`:
//! fifteen byte copies, then four loads); when the callee writes no memory
//! but its own slots and calls nothing, the clone reads the fields from the
//! caller's bytes and the slot and its copies go.
//!
//! Current typed callers may pass the value of an immediately preceding
//! nonvolatile array load. Under the same no-external-writes callee rule its
//! source address is stable through the call. Typed `extractelement`/store
//! copies must map each source lane to exactly its own byte offset before
//! their slot can be removed; an intervening write keeps the call unchanged.
//!
//! **Which calls** (each re-derived by the checker,
//! `trust_ir_mid_tv_byaddr.rs`; the pass reads a callee by its own copy of the
//! checker's prologue and typing, `byaddr_reading.rs`, which the checker's
//! tests compare with the checker's, and keeps no parameter of another entry
//! type than declared, so none of these three makes it propose a clone the
//! checker refuses): a plain `call` of a function of the module under the rustc
//! bridge's crate-private name, strong and hidden, not the caller, without
//! proof material, an entry block no edge targets, and every entry parameter of
//! exactly its declared type (the checker refuses a clone that keeps a thin
//! pointer entered as another pointer type, OD-82); per promoted parameter: an
//! array of scalars, the argument a thin pointer or the adjacent typed
//! snapshot above, every use of the parameter a constant lane read
//! (`extractfield` at the array's own type or typed `extractelement`) in the
//! callee's prologue: the longest prefix of its entry block made only of
//! count-free `alloca`s (the prefix's slots), `const`, `gep`, casts, `copy`,
//! `binop`, `unop`, `icmp`, `select`, plain loads, `extractfield`s of the
//! parameters the plan promotes, typed `extractelement`s of those parameters,
//! and `insertfield`s through and plain stores to
//! a slot of the prefix or a `gep` of one by constant indices. Any other form
//! ends it, even one that writes no memory (`globaladdr`, `overflow`, `fcmp`,
//! `nullptr`, `undef`) or only the callee's own slot (a `memset` of it). The
//! typing is the checker's: a block parameter, copy, load, constant or cast has
//! its stated type and an `alloca`, `gep` or `globaladdr` is `ptr`; any other
//! value (a `select`, an `undef`, a `nullptr`, an `insertfield`'s result) has
//! none. Policy: only parameters with a SLOT (an `alloca` of the array type the
//! prologue fills lane by lane from the parameter, read afterwards only by
//! loads, in a callee that writes only its own slots and calls nothing, judged
//! by an allowlist of value-only forms, plain loads, count-free `alloca`s,
//! terminators, writes into its own slots and `insertfield`s over an operand it
//! types as an aggregate value it names (a struct, tuple, array, record or
//! enum), so `drop`, `dealloc`, `retain`/`release`, an `insertfield` over a
//! pointer carrier ([`crate::escape::is_pointer_carrier`]: the lanes write the
//! field through it), over a type not named or over an untyped value, and any
//! form not named keep the slot) are promoted, and only when the array has more
//! lanes than argument promotion passes as values or the callee reads the slot
//! wider than a lane (a packed struct's bytes read as an `f64`: argument
//! promotion's clone would keep the slot), a callee in
//! [`crate::MidConfig::no_arg_promotion`] is never cloned, and a clone counts
//! toward argument promotion's budget (its name carries argument promotion's
//! mark). The original callee stays for every other caller.

use std::collections::{BTreeSet, HashMap, HashSet};

use trust_cg_verify::trust_ir_mid_tv::{
    ARGPROMO_CLONE_MARK, ByAddrParam, ByAddrSite, ByAddrWitness, PassWitness, byaddr_clone_name,
};
use trust_ir::{
    CastOp, Constant, FuncId, FuncTy, FuncTyId, Function, Inst, Linkage, Module, ParamAttrs,
    PassMode, Ty, ValueId, Visibility,
};

use super::byaddr_reading::{prologue, types_of};
use super::loops::first_free_value;
use super::{MidPass, PassContext};

/// The evidence name of by-address cloning.
pub(crate) const BYADDR_NAME: &str = "byaddr";

/// The most clones (by-address and argument promotion's) in one module.
const MAX_CLONES: usize = 16;

/// By-address cloning, with the callees it never clones.
pub(crate) struct ByAddr {
    excluded: BTreeSet<String>,
}

impl ByAddr {
    pub(crate) fn new(excluded: BTreeSet<String>) -> Self {
        Self { excluded }
    }
}

fn thin(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
    )
}

fn scalar(ty: &Ty) -> bool {
    ty.is_integer() || ty.is_float() || matches!(ty, Ty::Bool | Ty::Char) || thin(ty)
}

/// An aggregate VALUE type: an `insertfield` over a value of one builds a
/// new value and writes no memory. An allowlist (OD-166 ruling 2) that
/// names no pointer carrier ([`crate::escape::is_pointer_carrier`]: a thin
/// pointer, or the raw `i64`/`u64` address the wasm32 lane writes the field
/// through); a type not named is never assumed to be a value.
fn value_aggregate(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Struct(_) | Ty::Tuple(_) | Ty::Array(..) | Ty::Record(_) | Ty::Enum(_)
    )
}

/// Whether `func` may be cloned at all (the checker's `admit`, the pass's
/// own reading).
fn clonable(module: &Module, func: &Function) -> bool {
    let crate_private = func
        .name
        .rfind(".tcg.crate.")
        .is_some_and(|at| at > 0 && func.name.len() - at == ".tcg.crate.".len() + 16);
    let Some(sig) = module.func_type(func.ty) else {
        return false;
    };
    let Some(entry) = func.blocks.iter().find(|b| b.id == func.entry) else {
        return false;
    };
    !func.is_declaration()
        && func.linkage == Linkage::External
        && func.visibility == Visibility::Hidden
        && crate_private
        && !func.name.contains(ARGPROMO_CLONE_MARK)
        && !func.attrs.naked
        && func.attrs.target_features.is_empty()
        && !func
            .attrs
            .params
            .iter()
            .any(|p| p.byval || matches!(p.pass, Some(PassMode::Indirect { .. })))
        && func.proofs.is_empty()
        && func.summary.is_none()
        && func.source_provenance.is_none()
        && func.body_gate.is_none()
        && func
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .all(|n| n.proofs.is_empty() && n.proof_context.is_none())
        && module.spec_modules.is_empty()
        && module.proof_obligations.iter().all(|o| {
            !(o.function.is_none() && o.site.is_none())
                && o.function != Some(func.id)
                && o.site.as_ref().is_none_or(|s| s.function != func.id)
        })
        && !sig.is_vararg
        && entry.params.len() == sig.params.len()
        && entry
            .params
            .iter()
            .zip(&sig.params)
            .all(|((_, t), p)| t == p || (thin(t) && thin(p)))
        && !func.blocks.iter().any(|b| {
            b.body.last().is_some_and(|n| {
                n.inst
                    .successor_edges()
                    .iter()
                    .any(|e| e.target == func.entry)
            })
        })
}

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
                module
                    .ty_layout_shape(pointee_ty)
                    .ok()?
                    .size_bytes()?
                    .checked_mul(index)?
            };
            (offset
                == u64::from(field).checked_mul(module.ty_layout_shape(ty).ok()?.size_bytes()?)?)
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

/// The plan for `func`: each array parameter of scalars read only by lanes
/// in the prologue of the parameters the plan promotes, with its slot;
/// `None` when no parameter has a slot or the clone would keep a parameter
/// whose entry type is not its declared one.
fn plan(module: &Module, func: &Function) -> Option<Vec<(ByAddrParam, Ty, u64)>> {
    let entry_index = func.blocks.iter().position(|b| b.id == func.entry)?;
    let entry = &func.blocks[entry_index];
    let mut defs: HashMap<ValueId, &Inst> = HashMap::new();
    let mut uses: HashMap<ValueId, Vec<(usize, usize)>> = HashMap::new();
    for (bi, block) in func.blocks.iter().enumerate() {
        for (ni, node) in block.body.iter().enumerate() {
            if let [r] = node.results.as_slice() {
                defs.insert(*r, &node.inst);
            }
            node.inst.visit_value_operands(|v| {
                uses.entry(v).or_default().push((bi, ni));
            });
        }
    }
    let arrays: Vec<(usize, ValueId, Ty)> = entry
        .params
        .iter()
        .enumerate()
        .filter(|(_, (_, t))| matches!(t, Ty::Array(e, _) if module.ty(*e).is_some_and(scalar)))
        .map(|(i, (v, t))| (i, *v, t.clone()))
        .collect();
    if arrays.is_empty() {
        return None;
    }
    let constant = |v: &ValueId| matches!(defs.get(v), Some(Inst::Const { .. }));
    // The callee writes only its own slots and calls nothing.
    let types = types_of(func);
    let own = |p: &ValueId| match defs.get(p) {
        Some(Inst::Alloca { .. }) => true,
        Some(Inst::GEP { base, indices, .. }) => {
            matches!(defs.get(base), Some(Inst::Alloca { .. })) && indices.iter().all(constant)
        }
        _ => false,
    };
    let quiet = func
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .all(|n| match &n.inst {
            Inst::Store { ptr, .. } => own(ptr),
            // Into its own slot, or over an aggregate value; one over a
            // pointer carrier writes the carrier's bytes.
            Inst::InsertField { aggregate, .. } => {
                own(aggregate) || types.get(aggregate).is_some_and(value_aggregate)
            }
            Inst::MemCopy { dst, .. } | Inst::MemSet { dst, .. } => own(dst),
            // An allowlist: every form not named (a call of any kind, an
            // atomic access, `drop`, `dealloc`, `retain`, a dialect
            // operation, ...) keeps the slot.
            Inst::Alloca { count: None, .. }
            | Inst::Load {
                volatile: false, ..
            }
            | Inst::Const { .. }
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
            | Inst::Return { .. } => true,
            _ => false,
        });
    if !quiet {
        return None;
    }
    // The checker reads a plan under the prologue of the parameters it
    // promotes, which ends at a lane read of any other parameter: the plan
    // is derived under the prologue of every array parameter, then again
    // under that of the parameters it kept, until the two agree (the set
    // only shrinks, and a prologue of fewer parameters is no longer).
    let mut promoted: HashSet<ValueId> = arrays.iter().map(|(_, v, _)| *v).collect();
    loop {
        let len = prologue(func, &promoted);
        let mut out = Vec::new();
        for (index, p, ty) in arrays
            .iter()
            .filter(|(_, p, _)| promoted.contains(p))
            .cloned()
        {
            let Ty::Array(elem, length) = &ty else {
                continue;
            };
            let (Some(elem), true) = (module.ty(*elem).cloned(), *length > 0) else {
                continue;
            };
            let Some(size) = module
                .ty_layout_shape(&elem)
                .ok()
                .and_then(|s| s.size_bytes())
            else {
                continue;
            };
            let reads_ok = uses.get(&p).into_iter().flatten().all(|&(bi, ni)| {
                bi == entry_index
                    && ni < len
                    && read_lane(module, func, p, &ty, &func.blocks[bi].body[ni].inst).is_some()
            });
            if !reads_ok {
                continue;
            }
            // The slot: an alloca of the array type the prologue fills lane by
            // lane from `p`, read afterwards only by loads.
            let slot = entry.body[..len].iter().find_map(|node| {
                let ([s], Inst::Alloca { ty: t, count: None, .. }) = (node.results.as_slice(), &node.inst)
                else {
                    return None;
                };
                if *t != ty {
                    return None;
                }
                let mut lanes: HashSet<u32> = HashSet::new();
                let ok = func.blocks.iter().enumerate().all(|(bi, block)| block.body.iter().enumerate().all(|(ni, n)| {
                    let mut touches = false;
                    n.inst.visit_value_operands(|v| touches |= v == *s || matches!(defs.get(&v), Some(Inst::GEP { base, indices, .. }) if *base == *s && indices.iter().all(constant)));
                    if !touches { return true; }
                    if let Some(field) = copied_lane(module, func, p, &ty, *s, &n.inst) {
                        return bi == entry_index && ni < len && !n.results.iter().any(|r| uses.contains_key(r)) && lanes.insert(field);
                    }
                    match &n.inst {
                        Inst::Load { .. } => true,
                        Inst::GEP { base, indices, .. } if base == s && indices.iter().all(constant) => n.results.iter().all(|r| {
                            uses.get(r).into_iter().flatten().all(|&(b, i)| {
                                let user = &func.blocks[b].body[i].inst;
                                matches!(user, Inst::Load { ptr, .. } if ptr == r) || copied_lane(module, func, p, &ty, *s, user).is_some()
                            })
                        }),
                        _ => false,
                    }
                }));
                (ok && lanes.len() as u64 == *length).then_some(*s)
            });
            let Some(slot) = slot else {
                continue;
            };
            // Policy: argument promotion passes up to `MAX_FIELDS` lanes as
            // values, which beats a load of each once the clone's slot of them
            // dissolves; it does not when the callee reads the slot wider than a
            // lane (scalar replacement does not reassemble bytes into a word).
            let wider = |ptr: &ValueId| {
                uses.get(ptr).into_iter().flatten().any(|&(bi, ni)| {
                    matches!(&func.blocks[bi].body[ni].inst, Inst::Load { ty: t, ptr: q, .. }
                        if q == ptr && module.ty_layout_shape(t).ok().and_then(|s| s.size_bytes())
                            .is_some_and(|b| b > size))
                })
            };
            let reassembles = wider(&slot)
                || uses.get(&slot).into_iter().flatten().any(|&(bi, ni)| {
                    matches!(&func.blocks[bi].body[ni].inst, Inst::GEP { base, .. } if *base == slot)
                        && func.blocks[bi].body[ni].results.iter().any(wider)
                });
            if *length <= super::argpromo::MAX_FIELDS as u64 && !reassembles {
                continue;
            }
            out.push((
                ByAddrParam {
                    index,
                    slot: Some(slot),
                },
                elem,
                size,
            ));
        }
        let kept: HashSet<ValueId> = out
            .iter()
            .map(|(param, _, _): &(ByAddrParam, Ty, u64)| entry.params[param.index].0)
            .collect();
        if kept == promoted {
            // The clone declares the signature's types and keeps the entry's,
            // so the checker refuses a site whose clone keeps a parameter of
            // another entry type (a thin pointer of another pointer type,
            // which `clonable` admits): argument promotion's
            // `kept_params_declared` (OD-82).
            let sig = module.func_type(func.ty)?;
            let declared = entry
                .params
                .iter()
                .zip(&sig.params)
                .enumerate()
                .all(|(j, ((_, t), d))| t == d || out.iter().any(|(p, _, _)| p.index == j));
            return (declared && !out.is_empty()).then_some(out);
        }
        promoted = kept;
    }
}

/// The clone of `func` under `plan` (the checker's derivation, the pass's
/// own code).
fn make_clone(
    module: &Module,
    func: &Function,
    plan: &[(ByAddrParam, Ty, u64)],
    id: FuncId,
    name: String,
    ty: FuncTyId,
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
        for (p, _, _) in plan {
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
        .expect("clonable: an entry block");
    let mut lanes: HashMap<ValueId, (Ty, u64)> = HashMap::new();
    let mut slots: HashMap<ValueId, ValueId> = HashMap::new();
    let mut arrays: HashMap<ValueId, Ty> = HashMap::new();
    for (p, elem, size) in plan {
        let (v, _) = clone.blocks[entry_index].params[p.index];
        arrays.insert(v, clone.blocks[entry_index].params[p.index].1.clone());
        clone.blocks[entry_index].params[p.index].1 = Ty::Ptr;
        lanes.insert(v, (elem.clone(), *size));
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
    let mut next = first_free_value(func);
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
                let (elem, size) = lanes[&base].clone();
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

impl MidPass for ByAddr {
    fn name(&self) -> &'static str {
        BYADDR_NAME
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let module = cx.module;
        // The caller's arguments by the checker's typing: one it does not
        // type as a thin pointer gets no clone.
        let types = types_of(func);
        let mut sites: Vec<ByAddrSite> = Vec::new();
        let mut new_func_types: Vec<FuncTy> = Vec::new();
        let mut new_functions: Vec<Function> = Vec::new();
        let mut cur = func.clone();
        let mut next = first_free_value(func);
        let mut bi = 0;
        while bi < cur.blocks.len() {
            let mut ni = 0;
            while ni < cur.blocks[bi].body.len() {
                let node = cur.blocks[bi].body[ni].clone();
                let Inst::Call { callee, args } = &node.inst else {
                    ni += 1;
                    continue;
                };
                let Some(callee_fn) = module.function_by_id(*callee) else {
                    ni += 1;
                    continue;
                };
                let admissible = *callee != func.id
                    && node.proofs.is_empty()
                    && node.proof_context.is_none()
                    && !self.excluded.contains(&callee_fn.name)
                    && clonable(module, callee_fn);
                let plan = admissible.then(|| plan(module, callee_fn)).flatten();
                let Some(plan) = plan.filter(|plan| {
                    let Some(sig) = module.func_type(callee_fn.ty) else {
                        return false;
                    };
                    plan.iter().all(|(p, _, _)| {
                        let Some(arg) = args.get(p.index) else {
                            return false;
                        };
                        types.get(arg).is_some_and(|ty| {
                            thin(ty)
                                || sig.params.get(p.index) == Some(ty)
                                    && snapshot_address(&cur, bi, ni, *arg, ty)
                                        .is_some_and(|ptr| types.get(&ptr).is_some_and(thin))
                        })
                    })
                }) else {
                    ni += 1;
                    continue;
                };
                let Some(sig) = module.func_type(callee_fn.ty) else {
                    ni += 1;
                    continue;
                };
                let params: Vec<ByAddrParam> = plan.iter().map(|(p, _, _)| p.clone()).collect();
                let Some(name) = byaddr_clone_name(&callee_fn.name, &params) else {
                    ni += 1;
                    continue;
                };
                let mut csig = sig.clone();
                for p in &params {
                    csig.params[p.index] = Ty::Ptr;
                }
                let ty_index = module
                    .func_types
                    .iter()
                    .chain(new_func_types.iter())
                    .position(|t| *t == csig)
                    .unwrap_or(module.func_types.len() + new_func_types.len());
                let Some(ty) = u32::try_from(ty_index).ok().map(FuncTyId::new) else {
                    ni += 1;
                    continue;
                };
                let existing = module
                    .functions
                    .iter()
                    .chain(new_functions.iter())
                    .find(|f| f.name == name)
                    .cloned();
                let id = match &existing {
                    Some(f) => f.id,
                    None => {
                        let clones = module
                            .functions
                            .iter()
                            .chain(new_functions.iter())
                            .filter(|f| f.name.contains(ARGPROMO_CLONE_MARK))
                            .count();
                        let max = module
                            .functions
                            .iter()
                            .chain(new_functions.iter())
                            .map(|f| f.id.index())
                            .max();
                        match (clones < MAX_CLONES, max.and_then(|m| m.checked_add(1))) {
                            (true, Some(m)) => FuncId::new(m),
                            _ => {
                                ni += 1;
                                continue;
                            }
                        }
                    }
                };
                let clone = make_clone(module, callee_fn, &plan, id, name, ty);
                match &existing {
                    Some(f) if *f != clone => {
                        ni += 1;
                        continue;
                    }
                    Some(_) => {}
                    None => {
                        if ty_index == module.func_types.len() + new_func_types.len() {
                            new_func_types.push(csig);
                        }
                        new_functions.push(clone);
                    }
                }
                // The call: each promoted argument as `ptr`, then the clone.
                let mut before = Vec::new();
                let mut new_args = args.clone();
                let mut casts = Vec::new();
                for p in &params {
                    let mut arg = args[p.index];
                    let mut aty = types[&arg].clone();
                    if !thin(&aty) {
                        arg = snapshot_address(&cur, bi, ni, arg, &aty).expect("checked snapshot");
                        aty = types[&arg].clone();
                    }
                    new_args[p.index] = arg;
                    if aty != Ty::Ptr {
                        let c = ValueId::new(next);
                        next += 1;
                        let mut cast = node.clone();
                        cast.inst = Inst::Cast {
                            op: CastOp::PtrToPtr,
                            src_ty: aty,
                            dst_ty: Ty::Ptr,
                            operand: arg,
                        };
                        cast.results = vec![c];
                        before.push(cast);
                        new_args[p.index] = c;
                        casts.push(c);
                    }
                }
                let mut call = node.clone();
                call.inst = Inst::Call {
                    callee: id,
                    args: new_args,
                };
                before.push(call);
                let added = before.len();
                sites.push(ByAddrSite {
                    block: cur.blocks[bi].id,
                    index: ni,
                    callee: *callee,
                    clone: id,
                    params,
                    casts,
                });
                cur.blocks[bi].body.splice(ni..=ni, before);
                ni += added;
            }
            bi += 1;
        }
        if sites.is_empty() {
            return None;
        }
        Some((
            cur,
            PassWitness::ByAddr(ByAddrWitness {
                sites,
                new_func_types,
                new_functions,
            }),
        ))
    }
}
