// trust-cg-irmid/passes/merge.rs - block merging
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Block merging: a block that exactly one edge enters takes that edge's
//! arguments for its parameters, and when the edge is its predecessor's
//! `br` the two blocks become one. The unroller leaves a chain of `br`s per
//! copy and the original header entered by the last copy alone, whose
//! parameters then hide that an enclosing loop's parameter is passed back
//! unchanged (invariant code motion reads the back edge's arguments);
//! branch folding and the range rules leave the same shapes. Every argument
//! must have its parameter's type, and the entering terminator must be a
//! `br`, `condbr` or `switch`; a block is merged only when trust-ir's
//! validator reads every instruction it moves without a finding (policy),
//! and otherwise only loses its parameters. The witness lists the steps in order, and
//! the checker (`trust_ir_mid_tv_addr.rs`) re-derives each on the function
//! the steps before it produced.

use std::collections::{HashMap, HashSet};

use trust_cg_verify::trust_ir_mid_tv::{BlockMerge, BlockMergeWitness, PassWitness};
use trust_ir::{BlockId, Function, Inst, ValueId};

use super::loops::clean;
use super::{MidPass, PassContext, drop_names, value_types};

pub(crate) struct MergeBlocks;

/// The evidence name of block merging.
pub(crate) const MERGE_NAME: &str = "merge";

impl MidPass for MergeBlocks {
    fn name(&self) -> &'static str {
        MERGE_NAME
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let mut cur = func.clone();
        let mut merges = Vec::new();
        for _ in 0..256 {
            let steps = round(cx, &cur);
            if steps.is_empty() {
                break;
            }
            for step in steps {
                apply(&mut cur, &step);
                merges.push(step);
            }
        }
        if merges.is_empty() {
            return None;
        }
        Some((cur, PassWitness::BlockMerge(BlockMergeWitness { merges })))
    }
}

/// An incoming edge of a block: the predecessor, the edge's arguments,
/// whether it is a `br`, and whether its terminator can be edited.
type Incoming = (BlockId, Vec<ValueId>, bool, bool);

/// The steps one round takes: per block entered by one edge, a merge or a
/// forwarding, never two touching the same block. A block is merged only
/// when every instruction it moves is one trust-ir's validator reads
/// without a finding (`loops::clean`: a finding's text names its block);
/// otherwise only its parameters are forwarded.
fn round(cx: &PassContext<'_>, func: &Function) -> Vec<BlockMerge> {
    let types = value_types(func);
    let mut with_calls = types.clone();
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        if let Inst::Call { callee, .. } = &node.inst
            && let Some(sig) = cx
                .module
                .function_by_id(*callee)
                .and_then(|f| cx.module.func_type(f.ty))
            && sig.returns.len() == node.results.len()
        {
            for (value, ty) in node.results.iter().zip(&sig.returns) {
                with_calls.insert(*value, ty.clone());
            }
        }
    }
    let mut incoming: HashMap<BlockId, Vec<Incoming>> = HashMap::new();
    for block in &func.blocks {
        let Some(last) = block.body.last() else {
            continue;
        };
        let plain = matches!(last.inst, Inst::Br { .. });
        let editable = matches!(
            last.inst,
            Inst::Br { .. } | Inst::CondBr { .. } | Inst::Switch { .. }
        );
        for edge in last.inst.successor_edges() {
            incoming.entry(edge.target).or_default().push((
                block.id,
                edge.args.to_vec(),
                plain,
                editable,
            ));
        }
    }
    let mut touched: HashSet<BlockId> = HashSet::new();
    let mut steps = Vec::new();
    for block in &func.blocks {
        if block.id == func.entry || touched.contains(&block.id) {
            continue;
        }
        let Some([(pred, args, plain, editable)]) = incoming.get(&block.id).map(Vec::as_slice)
        else {
            continue;
        };
        if !editable || *pred == block.id || touched.contains(pred) {
            continue;
        }
        let typed = args.len() == block.params.len()
            && block
                .params
                .iter()
                .zip(args)
                .all(|((_, t), a)| types.get(a) == Some(t));
        if !typed {
            continue;
        }
        let movable = block
            .body
            .iter()
            .all(|n| clean(cx.module, func, cx.pointer_bits, &n.inst, &with_calls));
        if *plain && movable {
            steps.push(BlockMerge {
                block: block.id,
                into: Some(*pred),
            });
        } else if !block.params.is_empty() {
            steps.push(BlockMerge {
                block: block.id,
                into: None,
            });
        } else {
            continue;
        }
        touched.insert(block.id);
        touched.insert(*pred);
    }
    steps
}

/// Apply a step [`round`] produced.
fn apply(func: &mut Function, step: &BlockMerge) {
    let Some(b) = func.blocks.iter().position(|x| x.id == step.block) else {
        return;
    };
    let mut args: Vec<ValueId> = Vec::new();
    let mut pred_at = None;
    for (pi, block) in func.blocks.iter().enumerate() {
        if let Some(last) = block.body.last()
            && let Some(edge) = last
                .inst
                .successor_edges()
                .into_iter()
                .find(|e| e.target == step.block)
        {
            args = edge.args.to_vec();
            pred_at = Some(pi);
        }
    }
    let Some(p) = pred_at else {
        return;
    };
    let map: HashMap<ValueId, ValueId> = func.blocks[b]
        .params
        .iter()
        .map(|(v, _)| *v)
        .zip(args)
        .collect();
    if step.into.is_some() {
        let moved = func.blocks.remove(b);
        let p = if p > b { p - 1 } else { p };
        func.blocks[p].body.pop();
        func.blocks[p].body.extend(moved.body);
    } else {
        func.blocks[b].params.clear();
        let target = step.block;
        if let Some(last) = func.blocks[p].body.last_mut() {
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
    for block in &mut func.blocks {
        for node in &mut block.body {
            trust_ir::mem2reg::rewrite_inst(&mut node.inst, &map);
        }
    }
    let removed: HashSet<ValueId> = map.keys().copied().collect();
    drop_names(func, &removed);
}
