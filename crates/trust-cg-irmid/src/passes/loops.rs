// trust-cg-irmid/passes/loops.rs - what the loop passes share
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The loop passes' own analyses: the natural loops with a dedicated
//! preheader (from the generic `CfgAnalysis` through [`TrustIrCfg`], the
//! same discovery the native loop passes use), the values that are never
//! poison, and the edge arguments into a block. The checker
//! (`trust_cg_verify::trust_ir_mid_tv`, `trust_ir_mid_tv_loop.rs`) derives
//! each of them again with its own code.

use std::collections::{HashMap, HashSet};

use trust_ir::{BinOp, BlockId, CastOp, Constant, Function, Inst, Module, Ty, ValueId};

use super::int_shape;
use crate::cfg::TrustIrCfg;

/// A natural loop the loop passes may rewrite: every block of its body is
/// dominated by its header, and exactly one edge enters the header from
/// outside, from a reachable preheader ending in `br header(args)`. The
/// header is not the entry block: the call enters the entry with any
/// arguments besides its CFG edges, so an unreachable block branching to it
/// would pass for the only way in.
#[derive(Debug, Clone)]
pub(crate) struct Loop {
    pub header: BlockId,
    pub body: HashSet<BlockId>,
    pub preheader: BlockId,
    /// The edges into the header from the body.
    pub back_edges: usize,
    /// Nesting depth (outermost 1).
    pub depth: u32,
}

/// The loops of `func` the passes may rewrite, innermost first.
pub(crate) fn rewritable_loops(func: &Function) -> Vec<Loop> {
    let view = TrustIrCfg::new(func);
    let cfg = view.analysis();
    let index: HashMap<BlockId, usize> = func
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.id, i))
        .collect();
    let mut loops = Vec::new();
    for lp in &cfg.loops {
        let Some(preheader) = lp.preheader else {
            continue;
        };
        if lp.header == func.entry || !cfg.idom.contains_key(&preheader) {
            continue;
        }
        if lp
            .body
            .iter()
            .any(|b| !cfg.idom.contains_key(b) || !cfg.dominates(lp.header, *b))
        {
            continue;
        }
        // Every edge into the header, counted per edge.
        let mut outside = 0usize;
        let mut back_edges = 0usize;
        for block in &func.blocks {
            let Some(last) = block.body.last() else {
                continue;
            };
            for edge in last.inst.successor_edges() {
                if edge.target != lp.header {
                    continue;
                }
                if lp.body.contains(&block.id) {
                    back_edges += 1;
                } else {
                    outside += 1;
                }
            }
        }
        let branches = index
            .get(&preheader)
            .and_then(|&i| func.blocks[i].body.last())
            .is_some_and(|n| matches!(&n.inst, Inst::Br { target, .. } if *target == lp.header));
        if outside != 1 || !branches {
            continue;
        }
        loops.push(Loop {
            header: lp.header,
            body: lp.body.iter().copied().collect(),
            preheader,
            back_edges,
            depth: lp.depth,
        });
    }
    loops.sort_by_key(|l| std::cmp::Reverse(l.depth));
    loops
}

/// The values of `func` that are never poison: entry parameters, constants
/// (integer, `bool`, float), null and global or allocation addresses, the
/// results of integer, float, compare, cast and overflow operations (each
/// inspects its operands: a concrete value or a fault), and copies, selects
/// and block parameters of such values, as a greatest fixed point.
pub(crate) fn never_poison(func: &Function) -> HashSet<ValueId> {
    let mut set: HashSet<ValueId> = HashSet::new();
    let mut moves: Vec<(ValueId, Vec<ValueId>)> = Vec::new();
    let mut incoming: HashMap<BlockId, Vec<Vec<ValueId>>> = HashMap::new();
    for block in &func.blocks {
        set.extend(block.params.iter().map(|(v, _)| *v));
        for node in &block.body {
            for edge in node.inst.successor_edges() {
                incoming
                    .entry(edge.target)
                    .or_default()
                    .push(edge.args.to_vec());
            }
            match &node.inst {
                Inst::Const {
                    value:
                        Constant::Int(_) | Constant::U128(_) | Constant::Bool(_) | Constant::Float(_),
                    ..
                }
                | Inst::NullPtr
                | Inst::GlobalAddr { .. }
                | Inst::Alloca { .. }
                | Inst::BinOp { .. }
                | Inst::UnOp { .. }
                | Inst::ICmp { .. }
                | Inst::FCmp { .. }
                | Inst::Cast { .. }
                | Inst::Overflow { .. } => set.extend(node.results.iter().copied()),
                Inst::Select {
                    then_val, else_val, ..
                } if node.results.len() == 1 => {
                    set.insert(node.results[0]);
                    moves.push((node.results[0], vec![*then_val, *else_val]));
                }
                Inst::Copy { operand, .. } if node.results.len() == 1 => {
                    set.insert(node.results[0]);
                    moves.push((node.results[0], vec![*operand]));
                }
                _ => {}
            }
        }
    }
    let empty = Vec::new();
    loop {
        let mut changed = false;
        for (result, from) in &moves {
            if set.contains(result) && from.iter().any(|v| !set.contains(v)) {
                set.remove(result);
                changed = true;
            }
        }
        for block in &func.blocks {
            let edges = incoming.get(&block.id).unwrap_or(&empty);
            for (i, (param, _)) in block.params.iter().enumerate() {
                if set.contains(param)
                    && edges
                        .iter()
                        .any(|args| args.get(i).is_none_or(|a| !set.contains(a)))
                {
                    set.remove(param);
                    changed = true;
                }
            }
        }
        if !changed {
            return set;
        }
    }
}

/// The block each value is defined in.
pub(crate) fn def_blocks(func: &Function) -> HashMap<ValueId, BlockId> {
    let mut defs = HashMap::new();
    for block in &func.blocks {
        for (value, _) in &block.params {
            defs.insert(*value, block.id);
        }
        for node in &block.body {
            for result in &node.results {
                defs.insert(*result, block.id);
            }
        }
    }
    defs
}

/// The arguments of every edge from a block of `body` into `header`.
pub(crate) fn back_edge_args(func: &Function, lp: &Loop) -> Vec<Vec<ValueId>> {
    let mut lists = Vec::new();
    for block in func.blocks.iter().filter(|b| lp.body.contains(&b.id)) {
        if let Some(last) = block.body.last() {
            for edge in last.inst.successor_edges() {
                if edge.target == lp.header {
                    lists.push(edge.args.to_vec());
                }
            }
        }
    }
    lists
}

/// The preheader's arguments into the header.
pub(crate) fn preheader_args<'f>(func: &'f Function, lp: &Loop) -> Option<&'f [ValueId]> {
    let block = func.blocks.iter().find(|b| b.id == lp.preheader)?;
    match &block.body.last()?.inst {
        Inst::Br { target, args } if *target == lp.header => Some(args),
        _ => None,
    }
}

/// The first value number no value of `func` uses (parameters, results,
/// operands and debug names).
pub(crate) fn first_free_value(func: &Function) -> u32 {
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

/// Whether every operand of `inst` has the type `inst` declares for it, by
/// the pass-side typing (`types`; an operand it cannot type fails). The
/// wasm32 lane re-validates the optimized module and refuses it for a
/// finding the input lacks at the same place, so the loop passes neither
/// move nor create an instruction trust-ir's validator could flag anew.
pub(crate) fn well_typed(inst: &Inst, types: &HashMap<ValueId, Ty>) -> bool {
    let is = |v: &ValueId, ty: &Ty| types.get(v) == Some(ty);
    match inst {
        Inst::Const { .. } | Inst::NullPtr | Inst::GlobalAddr { .. } => true,
        Inst::BinOp { ty, lhs, rhs, .. }
        | Inst::ICmp { ty, lhs, rhs, .. }
        | Inst::FCmp { ty, lhs, rhs, .. }
        | Inst::Overflow { ty, lhs, rhs, .. } => is(lhs, ty) && is(rhs, ty),
        Inst::Cast {
            src_ty, operand, ..
        } => is(operand, src_ty),
        Inst::Copy { ty, operand } => is(operand, ty),
        Inst::Select {
            ty,
            cond,
            then_val,
            else_val,
        } => is(cond, &Ty::Bool) && is(then_val, ty) && is(else_val, ty),
        Inst::Load { ptr, .. } => matches!(
            types.get(ptr),
            Some(Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_))
        ),
        Inst::GEP { base, indices, .. } => {
            is(base, &Ty::Ptr)
                && indices
                    .iter()
                    .all(|i| types.get(i).is_some_and(Ty::is_integer))
        }
        _ => false,
    }
}

/// Whether trust-ir's validator reads `inst` in `func` without a finding,
/// by the pass's typing `types` (an operand whose type is unknown fails):
/// operands of the types the instruction declares, edges passing
/// arguments of their targets' parameter types, no field access through a
/// pointer, no aggregate or pointer constant. The wasm32 lane emits a
/// mid-end output only when it adds no finding, and a finding's text names
/// its block, so the passes that copy an instruction (full unrolling) or
/// move it to another block (block merging) touch only instructions this
/// admits (policy: the rewrites themselves are exact).
pub(crate) fn clean(
    module: &Module,
    func: &Function,
    pointer_bits: u32,
    inst: &Inst,
    types: &HashMap<ValueId, Ty>,
) -> bool {
    let is = |v: &ValueId, ty: &Ty| types.get(v) == Some(ty);
    let pointer = |ty: &Ty| {
        matches!(
            ty,
            Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
        )
    };
    let pointer_value = |v: &ValueId| types.get(v).is_some_and(pointer);
    let float = |ty: &Ty| matches!(ty, Ty::F32 | Ty::F64);
    let block_params = |target: &BlockId| {
        func.blocks
            .iter()
            .find(|b| b.id == *target)
            .map(|b| b.params.iter().map(|(_, t)| t.clone()).collect::<Vec<_>>())
    };
    let edges_typed = |inst: &Inst| {
        inst.successor_edges().iter().all(|e| {
            block_params(&e.target).is_some_and(|ps| {
                ps.len() == e.args.len() && e.args.iter().zip(&ps).all(|(a, t)| is(a, t))
            })
        })
    };
    match inst {
        Inst::Const { ty, value } => match value {
            Constant::Int(k) => int_shape(ty, pointer_bits).is_some_and(|(bits, signed)| {
                let k = *k;
                if bits >= 128 {
                    return true;
                }
                let lo = if signed { -(1i128 << (bits - 1)) } else { 0 };
                let hi = if signed {
                    (1i128 << (bits - 1)) - 1
                } else {
                    (1i128 << bits) - 1
                };
                (lo..=hi).contains(&k)
            }),
            Constant::Bool(_) => *ty == Ty::Bool,
            Constant::Float(_) => float(ty),
            _ => false,
        },
        Inst::BinOp { op, ty, lhs, rhs } => {
            let form = if ty.is_integer() {
                !matches!(
                    op,
                    BinOp::FAdd
                        | BinOp::FSub
                        | BinOp::FMul
                        | BinOp::FDiv
                        | BinOp::FRem
                        | BinOp::FMin
                        | BinOp::FMax
                        | BinOp::FCopySign
                        | BinOp::BAnd
                        | BinOp::BOr
                        | BinOp::BXor
                )
            } else if float(ty) {
                matches!(
                    op,
                    BinOp::FAdd | BinOp::FSub | BinOp::FMul | BinOp::FDiv | BinOp::FRem
                )
            } else {
                *ty == Ty::Bool
                    && matches!(
                        op,
                        BinOp::And
                            | BinOp::Or
                            | BinOp::Xor
                            | BinOp::BAnd
                            | BinOp::BOr
                            | BinOp::BXor
                    )
            };
            form && is(lhs, ty) && is(rhs, ty)
        }
        Inst::UnOp { ty, operand, .. } => (ty.is_integer() || float(ty)) && is(operand, ty),
        Inst::Overflow { ty, lhs, rhs, .. } => ty.is_integer() && is(lhs, ty) && is(rhs, ty),
        Inst::ICmp { ty, lhs, rhs, .. } => {
            (ty.is_integer() || *ty == Ty::Ptr || *ty == Ty::Bool) && is(lhs, ty) && is(rhs, ty)
        }
        Inst::FCmp { ty, lhs, rhs, .. } => float(ty) && is(lhs, ty) && is(rhs, ty),
        Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => {
            let ibits = |ty: &Ty| int_shape(ty, pointer_bits).map(|(b, _)| b);
            let form = match op {
                CastOp::ZExt | CastOp::SExt => {
                    matches!((ibits(src_ty), ibits(dst_ty)), (Some(s), Some(d)) if d > s)
                }
                CastOp::Trunc => {
                    matches!((ibits(src_ty), ibits(dst_ty)), (Some(s), Some(d)) if d < s)
                }
                CastOp::Bitcast => {
                    let width = |ty: &Ty| match ty {
                        Ty::F32 => Some(32),
                        Ty::F64 => Some(64),
                        _ => ibits(ty),
                    };
                    width(src_ty).is_some() && width(src_ty) == width(dst_ty)
                }
                CastOp::UIToFP | CastOp::SIToFP => src_ty.is_integer() && float(dst_ty),
                CastOp::FPToUI | CastOp::FPToSI | CastOp::FPToUISat | CastOp::FPToSISat => {
                    float(src_ty) && dst_ty.is_integer()
                }
                CastOp::FPExt => *src_ty == Ty::F32 && *dst_ty == Ty::F64,
                CastOp::FPTrunc => *src_ty == Ty::F64 && *dst_ty == Ty::F32,
                CastOp::PtrToPtr => pointer(src_ty) && pointer(dst_ty),
                CastOp::PtrToInt => pointer(src_ty) && dst_ty.is_integer(),
                CastOp::IntToPtr => src_ty.is_integer() && pointer(dst_ty),
                _ => false,
            };
            form && is(operand, src_ty)
        }
        Inst::Select {
            ty,
            cond,
            then_val,
            else_val,
        } => {
            !matches!(ty, Ty::Vector(..))
                && is(cond, &Ty::Bool)
                && is(then_val, ty)
                && is(else_val, ty)
        }
        Inst::Copy { ty, operand } => is(operand, ty),
        Inst::Load {
            ptr,
            volatile: false,
            ..
        } => pointer_value(ptr),
        Inst::Store {
            ty,
            ptr,
            value,
            volatile: false,
            ..
        } => pointer_value(ptr) && is(value, ty),
        Inst::GEP { base, indices, .. } => {
            pointer_value(base)
                && indices
                    .iter()
                    .all(|i| types.get(i).is_some_and(Ty::is_integer))
        }
        Inst::Call { callee, args } => module
            .function_by_id(*callee)
            .and_then(|f| module.func_type(f.ty))
            .is_some_and(|sig| {
                sig.params.len() == args.len()
                    && args.iter().zip(&sig.params).all(|(a, t)| is(a, t))
            }),
        Inst::Br { .. } => edges_typed(inst),
        Inst::CondBr { cond, .. } => is(cond, &Ty::Bool) && edges_typed(inst),
        Inst::Switch { value, .. } => {
            types.get(value).is_some_and(Ty::is_integer) && edges_typed(inst)
        }
        Inst::Return { values } => module.func_type(func.ty).is_some_and(|sig| {
            sig.returns.len() == values.len()
                && values.iter().zip(&sig.returns).all(|(v, t)| is(v, t))
        }),
        Inst::Unreachable => true,
        _ => false,
    }
}
