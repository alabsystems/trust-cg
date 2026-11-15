// trust-cg-irmid/passes/licm.rs - loop-invariant code motion
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Loop-invariant code motion: the native machine pass
//! (`trust_cg_opt::licm`) ported to `trust_ir::Function`, with its tiers
//! restated over trust-ir's semantics, where arithmetic that inspects poison
//! is undefined.
//!
//! Per natural loop with a dedicated preheader (one edge from outside, a
//! `br` to the header), innermost first:
//!
//! 1. A header parameter every back edge passes back unchanged holds the
//!    preheader's argument on every iteration: its uses become that argument
//!    and it goes, with its argument on every edge.
//! 2. An instruction whose operands are defined outside the loop (or by an
//!    instruction already moved) moves to the end of the preheader when it
//!    is SPECULATABLE (it raises nothing on operands that are never poison,
//!    and its operands are never poison: constants at their own type (a
//!    null `ptr`, and the bridge's global-address stub of a module global at
//!    offset zero at a pointer type, among the pointer ones), integer and
//!    float arithmetic, shifts by a constant below the width, division by a
//!    safe constant (nonzero, and for a signed one not all ones, at the
//!    operation's width), compares of scalars, the casts that cannot fault,
//!    `ptrtoint`, and `inttoptr` of a pointer-width integer in a loop that
//!    allocates and calls nothing), or when it is GUARANTEED to execute: it is in the
//!    header after only quiet instructions (no call, `assert`, store or
//!    atomic), which also admits a division, shift or `gep` of any operands,
//!    an `inttoptr` of any width in a loop that allocates and calls nothing,
//!    and a non-volatile load from a loop whose every instruction is quiet
//!    (the native pass's tier (a): no in-loop writer, no call, no
//!    synchronization) or whose only other instructions are non-volatile
//!    stores disjoint from it (tier (b), the native `addr_bases_disjoint`:
//!    the load and each store at a constant offset inside an `alloca` or
//!    global, each store to another allocation or to disjoint bytes, an
//!    allocation identified by its `alloca` instruction or its global's
//!    name, so every `global_addr` of one global is the same allocation).
//!
//! Only instructions whose operands have the types they declare move (and
//! a parameter goes only when its argument has its type): the lane refuses
//! an optimized module with a validation finding its input lacks at the same
//! place. What moves: on wasm a constant is an immediate and a `copy`, `ptrtoptr`,
//! `ptrtoint`, `inttoptr` or same-width integer cast emits nothing, so only
//! instructions that cost an operation (arithmetic, compares, selects,
//! loads, `gep`s, widening and narrowing casts) are moved, with the free
//! instructions and constants they read, and never a constant expression
//! (operands all constants), which is folded or rematerialized where it is
//! used. The witness names each loop's
//! removed parameters and moved instructions in order; the checker
//! re-derives the loop, invariance, the never-poison values and the tiers.

use std::collections::{HashMap, HashSet};

use trust_cg_verify::trust_ir_mid_tv::{LicmLoop, LicmWitness, PassWitness, global_addr_stub};
use trust_ir::{BinOp, BlockId, CastOp, Constant, Function, Inst, InstrNode, Module, Ty, ValueId};

use super::addr_fold::{extent, read, size_of};
use super::loops::{
    Loop, back_edge_args, def_blocks, never_poison, preheader_args, rewritable_loops, well_typed,
};
use super::{MidPass, PassContext, drop_names, int_shape, sole_defs, value_types};

pub(crate) struct Licm;

/// The evidence name of loop-invariant code motion.
pub(crate) const LICM_NAME: &str = "licm";

impl MidPass for Licm {
    fn name(&self) -> &'static str {
        LICM_NAME
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let mut cur = func.clone();
        let mut loops = Vec::new();
        for lp in rewritable_loops(func) {
            if let Some(claim) = hoist_loop(&mut cur, cx.module, cx.pointer_bits, &lp) {
                loops.push(claim);
            }
        }
        if loops.is_empty() {
            return None;
        }
        Some((cur, PassWitness::Licm(LicmWitness { loops })))
    }
}

/// Instructions that neither write memory, allocate, free, synchronize nor
/// stop execution in a defined way.
fn quiet(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::Const { .. }
            | Inst::NullPtr
            | Inst::GlobalAddr { .. }
            | Inst::Undef { .. }
            | Inst::Copy { .. }
            | Inst::BinOp { .. }
            | Inst::UnOp { .. }
            | Inst::Overflow { .. }
            | Inst::ICmp { .. }
            | Inst::FCmp { .. }
            | Inst::Cast { .. }
            | Inst::Select { .. }
            | Inst::GEP { .. }
            | Inst::PtrData { .. }
            | Inst::PtrMetadata { .. }
            | Inst::Load {
                volatile: false,
                ..
            }
            | Inst::Br { .. }
            | Inst::CondBr { .. }
            | Inst::Switch { .. }
    )
}

/// The bits the integer constant `k` holds at a width of `bits`.
fn at_width(k: i128, bits: u32) -> u128 {
    let mask = if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    };
    (k as u128) & mask
}

/// Whether the constant `value` at `ty` is one the checker's speculatable
/// tier admits: an integer, `u128`, `bool` or float constant at its own
/// type, a null `ptr`, or the bridge's global-address stub of a global of
/// `module` at offset zero at a pointer type (the differential reads it as
/// that global's address; a nonzero offset is a `gep` there, which faults
/// past the address space). Any other constant, such as a `bool` spelled as
/// an integer, is left in the loop: the checker would refuse the witness.
fn speculatable_constant(module: &Module, pointer_bits: u32, ty: &Ty, value: &Constant) -> bool {
    match value {
        Constant::Int(k) => {
            int_shape(ty, pointer_bits).is_some()
                || (*ty == Ty::Ptr && *k == 0)
                || (matches!(
                    ty,
                    Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
                ) && global_addr_stub(*k).is_some_and(|(index, offset)| {
                    offset == 0 && (index as usize) < module.globals.len()
                }))
        }
        Constant::U128(_) => *ty == Ty::U128,
        Constant::Bool(_) => *ty == Ty::Bool,
        Constant::Float(_) => matches!(ty, Ty::F32 | Ty::F64),
        _ => false,
    }
}

/// Whether `inst` raises nothing on operands that are never poison.
fn speculatable(
    consts: &HashMap<ValueId, i128>,
    module: &Module,
    pointer_bits: u32,
    inst: &Inst,
    allocates: bool,
) -> bool {
    let is_int = |ty: &Ty| int_shape(ty, pointer_bits).is_some();
    let is_float = |ty: &Ty| matches!(ty, Ty::F32 | Ty::F64);
    match inst {
        Inst::Const { ty, value } => speculatable_constant(module, pointer_bits, ty, value),
        Inst::Select { ty, .. } => !matches!(ty, Ty::Vector(..)),
        Inst::NullPtr | Inst::GlobalAddr { .. } | Inst::Copy { .. } => true,
        Inst::BinOp { op, ty, rhs, .. } => match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::RotL | BinOp::RotR => is_int(ty),
            BinOp::And | BinOp::Or | BinOp::Xor => is_int(ty) || *ty == Ty::Bool,
            BinOp::BAnd | BinOp::BOr | BinOp::BXor => *ty == Ty::Bool,
            BinOp::FAdd | BinOp::FSub | BinOp::FMul | BinOp::FDiv => is_float(ty),
            // An amount or divisor is the bits its constant holds at the
            // operation's width (the interpreter masks constants), and a
            // signed division reads them as signed whatever the type's
            // signedness: `sdiv u32 x, 4294967295` divides by -1.
            BinOp::Shl | BinOp::LShr | BinOp::AShr => {
                match (int_shape(ty, pointer_bits), consts.get(rhs)) {
                    (Some((bits, _)), Some(&k)) => at_width(k, bits) < u128::from(bits),
                    _ => false,
                }
            }
            BinOp::UDiv | BinOp::URem => match (int_shape(ty, pointer_bits), consts.get(rhs)) {
                (Some((bits, _)), Some(&k)) => at_width(k, bits) != 0,
                _ => false,
            },
            BinOp::SDiv | BinOp::SRem => match (int_shape(ty, pointer_bits), consts.get(rhs)) {
                (Some((bits, _)), Some(&k)) => {
                    let k = at_width(k, bits);
                    k != 0 && k != at_width(-1, bits)
                }
                _ => false,
            },
            _ => false,
        },
        Inst::ICmp { ty, .. } => is_int(ty) || *ty == Ty::Bool,
        Inst::FCmp { ty, .. } => is_float(ty),
        Inst::Cast {
            op, src_ty, dst_ty, ..
        } => match op {
            CastOp::ZExt | CastOp::SExt | CastOp::Trunc => is_int(src_ty) && is_int(dst_ty),
            CastOp::Bitcast => {
                (is_int(src_ty) || is_float(src_ty)) && (is_int(dst_ty) || is_float(dst_ty))
            }
            CastOp::UIToFP
            | CastOp::SIToFP
            | CastOp::FPExt
            | CastOp::FPTrunc
            | CastOp::PtrToPtr
            | CastOp::PtrToInt => true,
            CastOp::IntToPtr => {
                !allocates
                    && int_shape(src_ty, pointer_bits).is_some_and(|(bits, _)| bits <= pointer_bits)
            }
            _ => false,
        },
        Inst::Overflow { ty, .. } => is_int(ty),
        _ => false,
    }
}

/// Whether moving `inst` saves an operation on wasm (module docs).
fn costs(inst: &Inst, pointer_bits: u32) -> bool {
    match inst {
        Inst::Const { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Copy { .. }
        | Inst::Undef { .. } => false,
        Inst::Cast {
            op, src_ty, dst_ty, ..
        } => match op {
            CastOp::PtrToPtr | CastOp::PtrToInt | CastOp::IntToPtr => false,
            CastOp::ZExt | CastOp::SExt | CastOp::Trunc | CastOp::Bitcast => {
                let width = |ty: &Ty| {
                    int_shape(ty, pointer_bits)
                        .map(|(bits, _)| bits.max(32))
                        .or(match ty {
                            Ty::F32 => Some(0),
                            Ty::F64 => Some(1),
                            _ => None,
                        })
                };
                width(src_ty) != width(dst_ty)
            }
            _ => true,
        },
        _ => true,
    }
}

/// Hoist what `lp` admits in `cur`, returning the loop's claim.
fn hoist_loop(
    cur: &mut Function,
    module: &Module,
    pointer_bits: u32,
    lp: &Loop,
) -> Option<LicmLoop> {
    let init: Vec<ValueId> = preheader_args(cur, lp)?.to_vec();
    let header_index = cur.blocks.iter().position(|b| b.id == lp.header)?;
    let defs_at = def_blocks(cur);
    let types = value_types(cur);
    let outside = |v: &ValueId| defs_at.get(v).is_some_and(|b| !lp.body.contains(b));
    // ---- Invariant parameters.
    let backs = back_edge_args(cur, lp);
    let params: Vec<ValueId> = cur.blocks[header_index]
        .params
        .iter()
        .map(|(v, _)| *v)
        .collect();
    let mut map: HashMap<ValueId, ValueId> = HashMap::new();
    let mut drop: Vec<usize> = Vec::new();
    for (i, &param) in params.iter().enumerate() {
        let arg = *init.get(i)?;
        let same_type = types
            .get(&arg)
            .is_some_and(|t| *t == cur.blocks[header_index].params[i].1);
        if backs.iter().all(|args| args.get(i) == Some(&param)) && outside(&arg) && same_type {
            map.insert(param, arg);
            drop.push(i);
        }
    }
    let mut work = cur.clone();
    if !map.is_empty() && !remove_params(&mut work, lp.header, &drop, &map) {
        map.clear();
        drop.clear();
        work = cur.clone();
    }
    // ---- Candidates, in the order their operands become available.
    let poison_free = never_poison(&work);
    let work_types = value_types(&work);
    let consts: HashMap<ValueId, i128> = sole_defs(&work)
        .into_iter()
        .filter_map(|(v, inst)| match inst {
            Inst::Const {
                ty,
                value: Constant::Int(k),
            } if ty.is_integer() => Some((v, *k)),
            _ => None,
        })
        .collect();
    let mut body_quiet = true;
    let mut allocates = false;
    for block in work.blocks.iter().filter(|b| lp.body.contains(&b.id)) {
        for node in &block.body {
            body_quiet &= quiet(&node.inst);
            allocates |= !quiet(&node.inst)
                && !matches!(
                    node.inst,
                    Inst::Store {
                        volatile: false,
                        ..
                    }
                );
        }
    }
    let header_block = &work.blocks[header_index];
    // Position of each value's node in the header, and whether every node
    // before it is quiet.
    let mut clear_prefix: HashSet<ValueId> = HashSet::new();
    for node in &header_block.body {
        if let Some(first) = node.results.first() {
            clear_prefix.insert(*first);
        }
        if !quiet(&node.inst) {
            break;
        }
    }
    let mut available: HashSet<ValueId> = HashSet::new();
    let mut order: Vec<(BlockId, ValueId)> = Vec::new();
    loop {
        let mut grew = false;
        for block in work.blocks.iter().filter(|b| lp.body.contains(&b.id)) {
            for node in &block.body {
                let Some(&first) = node.results.first() else {
                    continue;
                };
                if node.inst.is_terminator() || available.contains(&first) {
                    continue;
                }
                let mut ready = true;
                let mut defined = true;
                node.inst.visit_value_operands(|v| {
                    let out = defs_at.get(&v).is_some_and(|b| !lp.body.contains(b));
                    ready &= out || available.contains(&v);
                    defined &= poison_free.contains(&v);
                });
                if !ready || !well_typed(&node.inst, &work_types) {
                    continue;
                }
                let spec = speculatable(&consts, module, pointer_bits, &node.inst, allocates);
                let admitted = (spec && defined)
                    || (block.id == lp.header
                        && clear_prefix.contains(&first)
                        && (spec
                            || match &node.inst {
                                Inst::BinOp { .. } | Inst::GEP { .. } => true,
                                Inst::Cast {
                                    op: CastOp::IntToPtr,
                                    ..
                                } => !allocates,
                                Inst::Load {
                                    volatile: false,
                                    ptr,
                                    ty,
                                    ..
                                } => {
                                    body_quiet
                                        || unclobbered(module, pointer_bits, &work, lp, *ptr, ty)
                                }
                                _ => false,
                            }));
                if admitted {
                    available.extend(node.results.iter().copied());
                    order.push((block.id, first));
                    grew = true;
                }
            }
        }
        if !grew {
            break;
        }
    }
    // ---- Keep what costs an operation, with what it reads.
    let nodes: HashMap<ValueId, &InstrNode> = work
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .filter_map(|n| n.results.first().map(|r| (*r, n)))
        .collect();
    let owner: HashMap<ValueId, ValueId> = order
        .iter()
        .flat_map(|(_, first)| nodes[first].results.iter().map(|r| (*r, *first)))
        .collect();
    let mut keep: HashSet<ValueId> = HashSet::new();
    // A constant expression (operands all constants or constant
    // expressions) is folded or rematerialized where it is used: moving it
    // only lengthens a live range.
    let mut constant: HashSet<ValueId> = HashSet::new();
    for node in work.blocks.iter().flat_map(|b| &b.body) {
        let [result] = node.results.as_slice() else {
            continue;
        };
        let folds = match &node.inst {
            Inst::Const { .. } => true,
            Inst::BinOp { .. } | Inst::Cast { .. } | Inst::ICmp { .. } | Inst::Copy { .. } => {
                let mut all = true;
                node.inst
                    .visit_value_operands(|v| all &= constant.contains(&v));
                all
            }
            _ => false,
        };
        if folds {
            constant.insert(*result);
        }
    }
    let mut stack: Vec<ValueId> = order
        .iter()
        .filter(|(_, first)| !constant.contains(first) && costs(&nodes[first].inst, pointer_bits))
        .map(|(_, first)| *first)
        .collect();
    while let Some(first) = stack.pop() {
        if !keep.insert(first) {
            continue;
        }
        nodes[&first].inst.visit_value_operands(|v| {
            if let Some(o) = owner.get(&v) {
                stack.push(*o);
            }
        });
    }
    let hoisted: Vec<ValueId> = order
        .iter()
        .map(|(_, first)| *first)
        .filter(|first| keep.contains(first))
        .collect();
    if hoisted.is_empty() && map.is_empty() {
        return None;
    }
    // ---- Move them.
    let mut moved: Vec<InstrNode> = Vec::new();
    for first in &hoisted {
        for block in work.blocks.iter_mut().filter(|b| lp.body.contains(&b.id)) {
            if let Some(i) = block
                .body
                .iter()
                .position(|n| n.results.first() == Some(first))
            {
                moved.push(block.body.remove(i));
                break;
            }
        }
    }
    let pre = work.blocks.iter_mut().find(|b| b.id == lp.preheader)?;
    let at = pre.body.len() - 1;
    for (k, node) in moved.into_iter().enumerate() {
        pre.body.insert(at + k, node);
    }
    *cur = work;
    let mut invariant_params: Vec<ValueId> = drop.iter().map(|&i| params[i]).collect();
    invariant_params.sort_by_key(|v| params.iter().position(|p| p == v));
    Some(LicmLoop {
        header: lp.header,
        invariant_params,
        hoisted,
    })
}

/// The identity of an allocation tier (b) compares (see [`unclobbered`]).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Allocation<'m> {
    Slot(ValueId),
    Global(&'m str),
}

/// Tier (b): whether no instruction of `lp` writes the bytes the load
/// `ptr`/`ty` reads. The body holds only quiet instructions and
/// non-volatile stores; the load and every store are at a constant offset
/// inside an `alloca` or global (read through the bridge's address casts
/// and constant offsets), and each store is to another allocation or to
/// bytes of the same one disjoint from the load's. An allocation is its
/// `alloca` instruction or its global's name: two `global_addr` of one
/// global (the bridge emits one per thread-local access, and the inliner
/// copies them) name the same bytes.
fn unclobbered<'m>(
    module: &'m Module,
    pointer_bits: u32,
    func: &Function,
    lp: &Loop,
    ptr: ValueId,
    ty: &Ty,
) -> bool {
    let defs = sole_defs(func);
    let span = |p: ValueId, t: &Ty| -> Option<(Allocation<'m>, u128, u128)> {
        let (Some(root), off) = read(module, &defs, pointer_bits, p, 0)? else {
            return None;
        };
        let size = u128::from(extent(module, &defs, root)?);
        let len = u128::from(size_of(module, t)?);
        let end = off.checked_add(len)?;
        let allocation = match defs.get(&root)? {
            Inst::Alloca { .. } => Allocation::Slot(root),
            Inst::GlobalAddr { global } => {
                Allocation::Global(&module.globals.get(global.index() as usize)?.name)
            }
            _ => return None,
        };
        (len > 0 && end <= size).then_some((allocation, off, end))
    };
    let Some((root, lo, hi)) = span(ptr, ty) else {
        return false;
    };
    func.blocks
        .iter()
        .filter(|b| lp.body.contains(&b.id))
        .flat_map(|b| &b.body)
        .all(|node| match &node.inst {
            Inst::Store {
                ty: st,
                ptr: sp,
                volatile: false,
                ..
            } => span(*sp, st).is_some_and(|(r, a, z)| r != root || z <= lo || hi <= a),
            other => quiet(other),
        })
}

/// Remove the parameters at `drop` from `header` and their arguments from
/// every edge into it, and rename their uses by `map`; `false` (and `func`
/// partly rewritten) when an edge into the header is not a `br`, `condbr`
/// or `switch` edge.
fn remove_params(
    func: &mut Function,
    header: BlockId,
    drop: &[usize],
    map: &HashMap<ValueId, ValueId>,
) -> bool {
    let mut order = drop.to_vec();
    order.sort_unstable_by(|a, b| b.cmp(a));
    for block in &mut func.blocks {
        let Some(last) = block.body.last_mut() else {
            continue;
        };
        let lists: Vec<&mut Vec<ValueId>> = match &mut last.inst {
            Inst::Br { target, args } => {
                if *target == header {
                    vec![args]
                } else {
                    vec![]
                }
            }
            Inst::CondBr {
                then_target,
                then_args,
                else_target,
                else_args,
                ..
            } => {
                let mut lists = Vec::new();
                if *then_target == header {
                    lists.push(then_args);
                }
                if *else_target == header {
                    lists.push(else_args);
                }
                lists
            }
            Inst::Switch {
                default,
                default_args,
                cases,
                ..
            } => {
                let mut lists = Vec::new();
                if *default == header {
                    lists.push(default_args);
                }
                for case in cases {
                    if case.target == header {
                        lists.push(&mut case.args);
                    }
                }
                lists
            }
            other => {
                if other.successor_edges().iter().any(|e| e.target == header) {
                    return false;
                }
                vec![]
            }
        };
        for list in lists {
            for &i in &order {
                if i < list.len() {
                    list.remove(i);
                }
            }
        }
    }
    if let Some(block) = func.blocks.iter_mut().find(|b| b.id == header) {
        for &i in &order {
            block.params.remove(i);
        }
    }
    for block in &mut func.blocks {
        for node in &mut block.body {
            trust_ir::mem2reg::rewrite_inst(&mut node.inst, map);
        }
    }
    let removed: HashSet<ValueId> = map.keys().copied().collect();
    drop_names(func, &removed);
    true
}
