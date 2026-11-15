// trust-cg-verify/trust_ir_mid_tv_addr.rs - address folding and dead parameters
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Two checkers of the cleanup that follows full unrolling, each deriving
//! its premises from the SOURCE function with this module's own code.
//!
//! **Address folding** ([`AddrFoldWitness`]). The rustc bridge computes an
//! address as integers (`inttoptr(ptrtoint(p) + k)`), and the copies of an
//! unrolled pointer loop chain those computations (`inttoptr(ptrtoint(
//! inttoptr(ptrtoint(slot) + 48)) - 8)`). Each claimed fold names an
//! `inttoptr` to `ptr` from an integer of pointer width whose operand this
//! module reads as `addr(B) + d` modulo `2^pointer_bits`: through integer
//! constants, `copy`, same-width integer `bitcast`, `ptrtoint` and `inttoptr`
//! between pointers and integers of pointer width and `ptrtoptr` (each the
//! identity on an address: the reference interpreter's `inttoptr` makes a
//! pointer, of whichever live allocation contains the address or of none,
//! whose `ptrtoint` is that address, and on wasm both are no-ops), `add` and
//! `sub` of a constant, `mul` of two constants, and a `gep` by constant
//! indices (`size(pointee) * sum(indices)` bytes). The root `B` must be an
//! `alloca` (count-free or counted by a positive integer constant) or a
//! `global_addr`, whose definition dominates the `inttoptr`, and `d` must lie
//! in `[0, size)` of the allocation (the interpreter's layout). Then the
//! `inttoptr` resolves to the pointer at offset `d` of `B`'s allocation
//! (allocations never overlap, and the dominating `B` names the instance the
//! address was computed from), which is `gep inbounds u8, B, d`; with `d = 0`
//! it is `copy ptr B`. The fold replaces the `inttoptr` in place, after a
//! fresh `const <its integer type> d` for a nonzero `d`. Exact: the source's
//! `inttoptr` raises nothing on an address inside a live allocation, and the
//! integer chain it read stays in the function until dead-code elimination
//! judges it.
//!
//! **Block merging** ([`BlockMergeWitness`]). Each step names a block `B`,
//! not the entry, that exactly one edge enters, from another block `P` whose
//! terminator is a `br`, `condbr` or `switch`, passing an argument of each
//! parameter's own type. With `into` naming `P` (whose terminator must then
//! be that `br`), `B`'s instructions are appended to `P` in place of the
//! `br` and `B` goes; without it, `B` keeps its place and loses its
//! parameters, and the edge its arguments. Either way every use of a
//! parameter becomes its argument, which dominates `B` (it is defined in
//! `P` or dominates `P`, and `P` alone reaches `B`). Exact: a `br` and a
//! block binding of values of the parameters' types do nothing else. The
//! unroller leaves chains of `br`s and the original header entered by the
//! last copy alone; merging them lets the loop passes see an enclosing
//! loop's invariant parameters again.
//!
//! **Field access through a pointer** ([`FieldAccessWitness`]). The rustc
//! bridge reads and writes a record's field through a pointer to it as
//! `extractfield T %p, i` and `insertfield T %p, i, %v` with `%p` a pointer
//! (trust-ir's validator reports both, `FieldAccessInvalid`, and the
//! inliner copies no callee carrying one). The wasm32 lane and the
//! differential's view of the lane's idioms read them as the load or store
//! of lane `i` of `T` (the interpreter's layout: a struct's or tuple's
//! field, an array's element) at that many bytes past `%p`; each claimed
//! rewrite spells that access: a fresh `const usize` of the lane's offset, a
//! fresh `gep u8, %p, [it]` (not `inbounds`, as the view builds it), and
//! `load <lane>` defining the read's result, or `store <lane> %v` for a
//! write, whose result no instruction may use and whose value must have
//! the lane's type. Exact under the lane's and the view's reading.
//!
//! **Dead block parameters** ([`DeadParamWitness`]). A claimed parameter of
//! a block other than the entry is used only as an argument of an edge into
//! a claimed parameter (so the claimed set computes nothing), and every edge
//! into its block is a `br`, `condbr` or `switch` edge passing an argument
//! of the parameter's own type (this module's typing: the binding the
//! removal drops faults on any other). The parameters and their arguments
//! on every edge go. Exact: a block binding inspects nothing but the type.

use std::collections::{HashMap, HashSet};

use trust_ir::{BinOp, BlockId, CastOp, Constant, Function, Inst, Module, Ty, ValueId};

use super::loops::value_types;
use super::{
    Defs, MidTvError, WitnessVerdict, alloca_count, block_positions, dominator_tree,
    incoming_edges, int_shape, used_values,
};
use crate::fsym_layout::FsymLayout;

/// One `inttoptr` (defining `value`) replaced by the pointer `offset` bytes
/// into the allocation `base` defines: `gep inbounds u8, base, index` with
/// `index` a fresh `const` of the `inttoptr`'s integer type, or `copy ptr
/// base` (`index` `None`) for offset 0.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AddrFold {
    pub value: ValueId,
    pub base: ValueId,
    pub offset: u64,
    pub index: Option<ValueId>,
}

/// Address folding's claim.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AddrFoldWitness {
    pub folds: Vec<AddrFold>,
}

/// One block parameter removed with its arguments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeadParam {
    pub block: BlockId,
    pub param: ValueId,
}

/// Dead block-parameter removal's claim.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DeadParamWitness {
    pub params: Vec<DeadParam>,
}

/// Bounds the address reading's recursion.
const MAX_READ: usize = 96;

fn ones(bits: u32) -> u128 {
    if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

/// `v` read as an address `root + off` (module docs); a root of `None` is
/// zero (a constant).
pub(super) fn address(
    defs: &Defs<'_>,
    layout: &FsymLayout<'_>,
    pointer_bits: u32,
    v: ValueId,
    depth: usize,
) -> Option<(Option<ValueId>, u128)> {
    if depth > MAX_READ {
        return None;
    }
    let pw = |ty: &Ty| -> bool {
        int_shape(ty, pointer_bits).is_some_and(|(bits, _)| bits == pointer_bits)
    };
    let pointer = |ty: &Ty| {
        matches!(
            ty,
            Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
        )
    };
    let read = |x: ValueId| address(defs, layout, pointer_bits, x, depth + 1);
    let m = ones(pointer_bits);
    match defs.inst(v)? {
        Inst::Alloca { .. } | Inst::GlobalAddr { .. } => Some((Some(v), 0)),
        Inst::Const {
            ty,
            value: Constant::Int(k),
        } if pw(ty) => Some((None, (*k as u128) & m)),
        Inst::Copy { ty, operand } if pw(ty) || pointer(ty) => read(*operand),
        Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => {
            let identity = match op {
                CastOp::PtrToPtr => pointer(src_ty) && pointer(dst_ty),
                CastOp::PtrToInt => pointer(src_ty) && pw(dst_ty),
                CastOp::IntToPtr => pw(src_ty) && pointer(dst_ty),
                CastOp::Bitcast => pw(src_ty) && pw(dst_ty),
                _ => false,
            };
            if identity { read(*operand) } else { None }
        }
        Inst::BinOp { op, ty, lhs, rhs } if pw(ty) => {
            let (a, b) = (read(*lhs)?, read(*rhs)?);
            match (op, a.0, b.0) {
                (BinOp::Add, _, None) => Some((a.0, a.1.wrapping_add(b.1) & m)),
                (BinOp::Add, None, _) => Some((b.0, a.1.wrapping_add(b.1) & m)),
                (BinOp::Sub, _, None) => Some((a.0, a.1.wrapping_sub(b.1) & m)),
                (BinOp::Mul, None, None) => Some((None, a.1.wrapping_mul(b.1) & m)),
                _ => None,
            }
        }
        Inst::GEP {
            pointee_ty,
            base,
            indices,
            ..
        } => {
            let elem = u128::from(layout.size(pointee_ty).ok()?);
            let (root, mut off) = read(*base)?;
            // The interpreter reads an index as the unsigned bits it holds at
            // its width (a negative signed index is UB, so no execution
            // reaches the fold through it).
            for index in indices {
                let Some(Inst::Const {
                    ty,
                    value: Constant::Int(k),
                }) = defs.inst(*index)
                else {
                    return None;
                };
                let (bits, _) = int_shape(ty, pointer_bits)?;
                let raw = (*k as u128) & ones(bits);
                off = off.wrapping_add(elem.wrapping_mul(raw)) & m;
            }
            Some((root, off))
        }
        _ => None,
    }
}

/// The byte size of the allocation `base` defines.
pub(super) fn allocation_size(
    module: &Module,
    defs: &Defs<'_>,
    layout: &FsymLayout<'_>,
    base: ValueId,
) -> Option<u64> {
    match defs.inst(base)? {
        Inst::Alloca { ty, count, .. } => {
            let count = alloca_count(defs, *count)?;
            layout.size(ty).ok()?.checked_mul(count)
        }
        Inst::GlobalAddr { global } => {
            let global = module.globals.get(global.index() as usize)?;
            layout.size(&global.ty).ok()
        }
        _ => None,
    }
}

pub(super) fn rebuild_addr_fold(
    module: &Module,
    pointer_bits: u32,
    source: &Function,
    witness: &AddrFoldWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let defs = Defs::of(source);
    let layout = FsymLayout::new(module);
    let positions = block_positions(source);
    let preds = incoming_edges(source, &positions);
    let (_, idom) = dominator_tree(source, &positions, &preds).ok_or(MidTvError::MalformedCfg {
        detail: "the function has no entry block".to_string(),
    })?;
    let entry = positions.get(&source.entry).copied().unwrap_or(usize::MAX);
    let dominates = |a: usize, mut b: usize| loop {
        if b == a {
            return true;
        }
        if b == entry || idom.get(b).is_none_or(|d| *d == usize::MAX) {
            return false;
        }
        b = idom[b];
    };
    let mut at: HashMap<ValueId, (usize, usize)> = HashMap::new();
    for (bi, block) in source.blocks.iter().enumerate() {
        for (ni, node) in block.body.iter().enumerate() {
            for r in &node.results {
                at.insert(*r, (bi, ni));
            }
        }
    }
    let mut taken = used_values(source);
    taken.extend(at.keys().copied());
    for block in &source.blocks {
        taken.extend(block.params.iter().map(|(v, _)| *v));
    }
    if let Some(names) = &source.value_names {
        taken.extend(names.iter().map(|(v, _)| *v));
    }
    let mut seen: HashSet<ValueId> = HashSet::new();
    let mut replaced: HashMap<(usize, usize), Vec<trust_ir::InstrNode>> = HashMap::new();
    for fold in &witness.folds {
        let bad = |why: &str| MidTvError::NotAddressFold {
            value: fold.value,
            why: why.to_string(),
        };
        if !seen.insert(fold.value) {
            return Err(bad("folded twice"));
        }
        let &(bi, ni) = at
            .get(&fold.value)
            .ok_or_else(|| bad("no defining instruction"))?;
        let node = &source.blocks[bi].body[ni];
        let Inst::Cast {
            op: CastOp::IntToPtr,
            src_ty,
            dst_ty: Ty::Ptr,
            operand,
        } = &node.inst
        else {
            return Err(bad("not an inttoptr to ptr"));
        };
        if node.results.len() != 1
            || int_shape(src_ty, pointer_bits).is_none_or(|(b, _)| b != pointer_bits)
        {
            return Err(bad("not an inttoptr from an integer of pointer width"));
        }
        let (root, off) = address(&defs, &layout, pointer_bits, *operand, 0)
            .ok_or_else(|| bad("the address is not a constant offset from a root"))?;
        if root != Some(fold.base) || off != u128::from(fold.offset) {
            return Err(bad("the address is not the claimed base and offset"));
        }
        let size = allocation_size(module, &defs, &layout, fold.base)
            .ok_or_else(|| bad("the base is not an allocation of known size"))?;
        if fold.offset >= size {
            return Err(MidTvError::OffsetOutOfBounds {
                value: fold.value,
                offset: fold.offset,
                size,
            });
        }
        let &(base_block, base_index) = at.get(&fold.base).ok_or_else(|| bad("no base"))?;
        let dominated = if base_block == bi {
            base_index < ni
        } else {
            dominates(base_block, bi)
        };
        if !dominated {
            return Err(bad("the base does not dominate the inttoptr"));
        }
        let mut nodes = Vec::new();
        let mut rewritten = node.clone();
        match (fold.offset, fold.index) {
            (0, None) => {
                rewritten.inst = Inst::Copy {
                    ty: Ty::Ptr,
                    operand: fold.base,
                };
            }
            (offset, Some(index)) if offset != 0 => {
                if !taken.insert(index) {
                    return Err(bad("the index is not a fresh value"));
                }
                let mut constant = node.clone();
                constant.inst = Inst::Const {
                    ty: src_ty.clone(),
                    value: Constant::Int(i128::from(offset)),
                };
                constant.results = vec![index];
                nodes.push(constant);
                rewritten.inst = Inst::GEP {
                    pointee_ty: Ty::U8,
                    base: fold.base,
                    indices: vec![index],
                    inbounds: true,
                };
            }
            _ => return Err(bad("an index is named for offset 0, or missing")),
        }
        nodes.push(rewritten);
        replaced.insert((bi, ni), nodes);
    }
    let mut expected = source.clone();
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
            exact: witness.folds.len(),
            refinements: 0,
        },
    ))
}

pub(super) fn rebuild_dead_param(
    source: &Function,
    witness: &DeadParamWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let bad = |value: ValueId, why: &str| MidTvError::NotDeadParam {
        value,
        why: why.to_string(),
    };
    let positions = block_positions(source);
    // The claimed positions, per block.
    let mut dead: HashMap<BlockId, HashSet<usize>> = HashMap::new();
    let mut claimed: HashSet<ValueId> = HashSet::new();
    for p in &witness.params {
        if p.block == source.entry {
            return Err(bad(p.param, "a parameter of the entry block"));
        }
        let Some(&bi) = positions.get(&p.block) else {
            return Err(bad(p.param, "the named block does not exist"));
        };
        let Some(i) = source.blocks[bi]
            .params
            .iter()
            .position(|(v, _)| *v == p.param)
        else {
            return Err(bad(p.param, "not a parameter of the named block"));
        };
        if !claimed.insert(p.param) || !dead.entry(p.block).or_default().insert(i) {
            return Err(bad(p.param, "claimed twice"));
        }
    }
    let types = value_types(source);
    // Every use of a claimed parameter is an argument into a claimed one, and
    // every edge into a block with a claimed parameter can be rewritten and
    // passes an argument of the parameter's type.
    for block in &source.blocks {
        for node in &block.body {
            let mut operands: Vec<ValueId> = Vec::new();
            match &node.inst {
                Inst::Br { .. } | Inst::CondBr { .. } | Inst::Switch { .. } => {
                    if let Inst::CondBr { cond, .. } = &node.inst {
                        operands.push(*cond);
                    }
                    if let Inst::Switch { value, .. } = &node.inst {
                        operands.push(*value);
                    }
                    for edge in node.inst.successor_edges() {
                        let removed = dead.get(&edge.target);
                        let target = positions.get(&edge.target).map(|&t| &source.blocks[t]);
                        for (i, arg) in edge.args.iter().enumerate() {
                            if removed.is_some_and(|r| r.contains(&i)) {
                                let ty = target.and_then(|t| t.params.get(i)).map(|(_, t)| t);
                                if ty.is_none() || types.get(arg) != ty {
                                    return Err(bad(
                                        *arg,
                                        "an argument does not have the removed parameter's type",
                                    ));
                                }
                            } else {
                                operands.push(*arg);
                            }
                        }
                    }
                }
                other => {
                    if other
                        .successor_edges()
                        .iter()
                        .any(|e| dead.contains_key(&e.target))
                    {
                        return Err(bad(
                            node.results.first().copied().unwrap_or(ValueId::new(0)),
                            "an edge into a block with a removed parameter cannot be rewritten",
                        ));
                    }
                    other.visit_value_operands(|v| operands.push(v));
                }
            }
            if let Some(v) = operands.iter().find(|v| claimed.contains(v)) {
                return Err(bad(*v, "the parameter is used"));
            }
        }
    }
    let mut expected = source.clone();
    for block in &mut expected.blocks {
        if let Some(last) = block.body.last_mut() {
            let edit = |target: &BlockId, args: &mut Vec<ValueId>| {
                if let Some(removed) = dead.get(target) {
                    let mut i = 0usize;
                    args.retain(|_| {
                        let keep = !removed.contains(&i);
                        i += 1;
                        keep
                    });
                }
            };
            match &mut last.inst {
                Inst::Br { target, args } => edit(target, args),
                Inst::CondBr {
                    then_target,
                    then_args,
                    else_target,
                    else_args,
                    ..
                } => {
                    edit(then_target, then_args);
                    edit(else_target, else_args);
                }
                Inst::Switch {
                    default,
                    default_args,
                    cases,
                    ..
                } => {
                    edit(default, default_args);
                    for case in cases {
                        edit(&case.target, &mut case.args);
                    }
                }
                _ => {}
            }
        }
    }
    for block in &mut expected.blocks {
        if let Some(removed) = dead.get(&block.id) {
            let mut i = 0usize;
            block.params.retain(|_| {
                let keep = !removed.contains(&i);
                i += 1;
                keep
            });
        }
    }
    super::drop_names(&mut expected, &claimed);
    Ok((
        expected,
        WitnessVerdict {
            exact: witness.params.len(),
            refinements: 0,
        },
    ))
}

// ---------------------------------------------------------------------------
// Block merging
// ---------------------------------------------------------------------------

/// One step of block merging: `block`, which exactly one edge enters,
/// either appended to `into` (whose terminator is that edge's `br`) or,
/// with `into` `None`, only its parameters forwarded from that edge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockMerge {
    pub block: BlockId,
    pub into: Option<BlockId>,
}

/// Block merging's claim, applied in order.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct BlockMergeWitness {
    pub merges: Vec<BlockMerge>,
}

/// Apply one merge step to `cur` (module docs, **Block merging**).
fn merge_step(cur: &mut Function, step: &BlockMerge) -> Result<(), MidTvError> {
    let bad = |why: &str| MidTvError::NotBlockMerge {
        block: step.block,
        why: why.to_string(),
    };
    if step.block == cur.entry {
        return Err(bad("the entry block has no predecessor to merge into"));
    }
    let positions = block_positions(cur);
    let b = *positions
        .get(&step.block)
        .ok_or_else(|| bad("no such block"))?;
    // The one edge entering the block.
    let mut edges: Vec<(usize, Vec<ValueId>, bool)> = Vec::new();
    for (pi, block) in cur.blocks.iter().enumerate() {
        let Some(last) = block.body.last() else {
            continue;
        };
        let plain = matches!(last.inst, Inst::Br { .. });
        let editable = matches!(
            last.inst,
            Inst::Br { .. } | Inst::CondBr { .. } | Inst::Switch { .. }
        );
        for edge in last.inst.successor_edges() {
            if edge.target == step.block {
                if !editable {
                    return Err(bad(
                        "an edge enters the block from a terminator that cannot drop it",
                    ));
                }
                edges.push((pi, edge.args.to_vec(), plain));
            }
        }
    }
    let [(p, args, plain)] = edges.as_slice() else {
        return Err(bad("the block is not entered by exactly one edge"));
    };
    let (p, plain) = (*p, *plain);
    if p == b {
        return Err(bad("the block enters itself"));
    }
    let types = value_types(cur);
    let params = cur.blocks[b].params.clone();
    if args.len() != params.len() {
        return Err(bad("the edge passes the wrong arity"));
    }
    let mut map: HashMap<ValueId, ValueId> = HashMap::new();
    for ((param, ty), arg) in params.iter().zip(args) {
        if types.get(arg) != Some(ty) {
            return Err(bad("an argument does not have its parameter's type"));
        }
        map.insert(*param, *arg);
    }
    match step.into {
        Some(into) => {
            if cur.blocks[p].id != into || !plain {
                return Err(bad(
                    "the block's one predecessor is not the claimed block ending in br",
                ));
            }
            let moved = cur.blocks.remove(b);
            let p = if p > b { p - 1 } else { p };
            cur.blocks[p].body.pop();
            cur.blocks[p].body.extend(moved.body);
        }
        None => {
            cur.blocks[b].params.clear();
            if let Some(last) = cur.blocks[p].body.last_mut() {
                let target = step.block;
                let clear = |t: &BlockId, a: &mut Vec<ValueId>| {
                    if *t == target {
                        a.clear();
                    }
                };
                match &mut last.inst {
                    Inst::Br { target: t, args } => clear(t, args),
                    Inst::CondBr {
                        then_target,
                        then_args,
                        else_target,
                        else_args,
                        ..
                    } => {
                        clear(then_target, then_args);
                        clear(else_target, else_args);
                    }
                    Inst::Switch {
                        default,
                        default_args,
                        cases,
                        ..
                    } => {
                        clear(default, default_args);
                        for case in cases {
                            clear(&case.target, &mut case.args);
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    for block in &mut cur.blocks {
        for node in &mut block.body {
            trust_ir::mem2reg::rewrite_inst(&mut node.inst, &map);
        }
    }
    let removed: HashSet<ValueId> = map.keys().copied().collect();
    super::drop_names(cur, &removed);
    Ok(())
}

pub(super) fn rebuild_block_merge(
    source: &Function,
    witness: &BlockMergeWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let mut cur = source.clone();
    for step in &witness.merges {
        merge_step(&mut cur, step)?;
    }
    Ok((
        cur,
        WitnessVerdict {
            exact: witness.merges.len(),
            refinements: 0,
        },
    ))
}

#[cfg(test)]
#[path = "trust_ir_mid_tv_addr_tests.rs"]
mod tests;

// ---------------------------------------------------------------------------
// Field access through a pointer
// ---------------------------------------------------------------------------

/// One field access through a pointer (the instruction defining `value`)
/// spelled as the access it is: `index` and `address` name the fresh
/// `const usize` offset and `gep u8` of the module docs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldAccess {
    pub value: ValueId,
    pub index: ValueId,
    pub address: ValueId,
}

/// Field-access lowering's claim.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FieldAccessWitness {
    pub rewrites: Vec<FieldAccess>,
}

/// Lane `field` of the record `ty` in the interpreter's layout: its byte
/// offset and type (a struct's or tuple's field, an array's element).
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

pub(super) fn rebuild_field_access(
    module: &Module,
    source: &Function,
    witness: &FieldAccessWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let layout = FsymLayout::new(module);
    let types = value_types(source);
    let mut at: HashMap<ValueId, (usize, usize)> = HashMap::new();
    for (bi, block) in source.blocks.iter().enumerate() {
        for (ni, node) in block.body.iter().enumerate() {
            if let [r] = node.results.as_slice() {
                at.insert(*r, (bi, ni));
            }
        }
    }
    let used = used_values(source);
    let mut taken = used.clone();
    for block in &source.blocks {
        taken.extend(block.params.iter().map(|(v, _)| *v));
        for node in &block.body {
            taken.extend(node.results.iter().copied());
        }
    }
    if let Some(names) = &source.value_names {
        taken.extend(names.iter().map(|(v, _)| *v));
    }
    let pointer = |ty: &Ty| {
        matches!(
            ty,
            Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
        )
    };
    let mut replaced: HashMap<(usize, usize), Vec<trust_ir::InstrNode>> = HashMap::new();
    for rewrite in &witness.rewrites {
        let bad = |why: &str| MidTvError::NotFieldAccess {
            value: rewrite.value,
            why: why.to_string(),
        };
        let &(bi, ni) = at
            .get(&rewrite.value)
            .ok_or_else(|| bad("not the single result of an instruction"))?;
        if replaced.contains_key(&(bi, ni)) {
            return Err(bad("rewritten twice"));
        }
        for v in [rewrite.index, rewrite.address] {
            if !taken.insert(v) {
                return Err(bad("a named value is not fresh"));
            }
        }
        let node = &source.blocks[bi].body[ni];
        let (ty, aggregate, field, value) = match &node.inst {
            Inst::ExtractField {
                ty,
                aggregate,
                field,
            } => (ty, *aggregate, *field, None),
            Inst::InsertField {
                ty,
                aggregate,
                field,
                value,
            } => (ty, *aggregate, *field, Some(*value)),
            _ => return Err(bad("not a field access")),
        };
        if !types.get(&aggregate).is_some_and(pointer) {
            return Err(bad("the operand is not a pointer"));
        }
        let (offset, lane_ty) = record_lane(&layout, module, ty, field)
            .ok_or_else(|| bad("the declared type has no such lane"))?;
        let mut constant = node.clone();
        constant.inst = Inst::Const {
            ty: Ty::Usize,
            value: Constant::Int(i128::from(offset)),
        };
        constant.results = vec![rewrite.index];
        let mut gep = node.clone();
        gep.inst = Inst::GEP {
            pointee_ty: Ty::U8,
            base: aggregate,
            indices: vec![rewrite.index],
            inbounds: false,
        };
        gep.results = vec![rewrite.address];
        let mut access = node.clone();
        match value {
            None => {
                access.inst = Inst::Load {
                    ty: lane_ty,
                    ptr: rewrite.address,
                    volatile: false,
                    align: None,
                };
            }
            Some(value) => {
                if used.contains(&rewrite.value) {
                    return Err(bad("a write-through's result is used"));
                }
                if types.get(&value) != Some(&lane_ty) {
                    return Err(bad("the stored value does not have the lane's type"));
                }
                access.inst = Inst::Store {
                    ty: lane_ty,
                    ptr: rewrite.address,
                    value,
                    volatile: false,
                    align: None,
                };
                access.results = Vec::new();
            }
        }
        replaced.insert((bi, ni), vec![constant, gep, access]);
    }
    let mut expected = source.clone();
    for (bi, block) in expected.blocks.iter_mut().enumerate() {
        let body = std::mem::take(&mut block.body);
        block.body = body
            .into_iter()
            .enumerate()
            .flat_map(|(ni, node)| replaced.remove(&(bi, ni)).unwrap_or_else(|| vec![node]))
            .collect();
    }
    let removed: HashSet<ValueId> = witness
        .rewrites
        .iter()
        .filter(|r| {
            at.get(&r.value).is_some_and(|&(bi, ni)| {
                matches!(source.blocks[bi].body[ni].inst, Inst::InsertField { .. })
            })
        })
        .map(|r| r.value)
        .collect();
    super::drop_names(&mut expected, &removed);
    Ok((
        expected,
        WitnessVerdict {
            exact: witness.rewrites.len(),
            refinements: 0,
        },
    ))
}
