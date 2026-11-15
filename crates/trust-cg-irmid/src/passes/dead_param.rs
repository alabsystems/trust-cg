// trust-cg-irmid/passes/dead_param.rs - dead block parameters
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Dead block-parameter removal: a parameter of a block other than the entry
//! that computes nothing (no instruction reads it; at most an edge passes it
//! on to another such parameter) goes, with its argument on every edge into
//! its block. Dead-code elimination removes instructions only, so the
//! arguments of a dead parameter kept their definitions alive: after full
//! unrolling the original header runs once on the last visit's values, and
//! an induction pointer passed to a parameter nothing reads kept the slot's
//! address exposed through its `ptrtoint`.
//!
//! The dead set is the greatest one closed under that rule. Every edge into
//! a block losing a parameter must be a `br`, `condbr` or `switch` edge and
//! pass an argument of the parameter's own type (the binding the removal
//! drops faults on any other); a block failing that keeps its parameters,
//! and the set is recomputed without them. The checker
//! (`trust_ir_mid_tv_addr.rs`) re-derives that the claimed set computes
//! nothing and that every edge can drop it.

use std::collections::{HashMap, HashSet};

use trust_cg_verify::trust_ir_mid_tv::{DeadParam, DeadParamWitness, PassWitness};
use trust_ir::{BlockId, Function, Inst, ValueId};

use super::{MidPass, PassContext, drop_names, value_types};

pub(crate) struct DeadParamPass;

/// The evidence name of dead block-parameter removal.
pub(crate) const DEAD_PARAM_NAME: &str = "dead_param";

impl MidPass for DeadParamPass {
    fn name(&self) -> &'static str {
        DEAD_PARAM_NAME
    }

    fn run(&self, _cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let types = value_types(func);
        let params: HashMap<BlockId, Vec<ValueId>> = func
            .blocks
            .iter()
            .map(|b| (b.id, b.params.iter().map(|(v, _)| *v).collect()))
            .collect();
        // Blocks whose every incoming edge can drop an argument of the
        // parameter's type, per parameter position.
        let mut droppable: HashSet<(BlockId, usize)> = HashSet::new();
        for block in func.blocks.iter().filter(|b| b.id != func.entry) {
            droppable.extend((0..block.params.len()).map(|i| (block.id, i)));
        }
        for block in &func.blocks {
            let Some(last) = block.body.last() else {
                continue;
            };
            let editable = matches!(
                last.inst,
                Inst::Br { .. } | Inst::CondBr { .. } | Inst::Switch { .. }
            );
            for edge in last.inst.successor_edges() {
                let Some(target) = func.blocks.iter().find(|b| b.id == edge.target) else {
                    continue;
                };
                for (i, (_, ty)) in target.params.iter().enumerate() {
                    let typed = edge.args.get(i).is_some_and(|a| types.get(a) == Some(ty));
                    if !editable || !typed {
                        droppable.remove(&(edge.target, i));
                    }
                }
            }
        }
        // Greatest fixed point: a parameter is dead while every use of it is
        // an argument into a dead parameter.
        let mut dead: HashSet<(BlockId, usize)> = droppable.clone();
        loop {
            let mut live: HashSet<ValueId> = HashSet::new();
            for node in func.blocks.iter().flat_map(|b| &b.body) {
                match &node.inst {
                    Inst::Br { .. } | Inst::CondBr { .. } | Inst::Switch { .. } => {
                        if let Inst::CondBr { cond, .. } = &node.inst {
                            live.insert(*cond);
                        }
                        if let Inst::Switch { value, .. } = &node.inst {
                            live.insert(*value);
                        }
                        for edge in node.inst.successor_edges() {
                            for (i, a) in edge.args.iter().enumerate() {
                                if !dead.contains(&(edge.target, i)) {
                                    live.insert(*a);
                                }
                            }
                        }
                    }
                    other => other.visit_value_operands(|v| {
                        live.insert(v);
                    }),
                }
            }
            let before = dead.len();
            dead.retain(|(b, i)| {
                params
                    .get(b)
                    .and_then(|ps| ps.get(*i))
                    .is_some_and(|v| !live.contains(v))
            });
            if dead.len() == before {
                break;
            }
        }
        if dead.is_empty() {
            return None;
        }
        let mut out = func.clone();
        for block in &mut out.blocks {
            let Some(last) = block.body.last_mut() else {
                continue;
            };
            let edit = |target: &BlockId, args: &mut Vec<ValueId>| {
                let mut i = 0usize;
                args.retain(|_| {
                    let keep = !dead.contains(&(*target, i));
                    i += 1;
                    keep
                });
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
        let mut claims = Vec::new();
        let mut removed: HashSet<ValueId> = HashSet::new();
        for block in &mut out.blocks {
            let id = block.id;
            let mut i = 0usize;
            block.params.retain(|(v, _)| {
                let keep = !dead.contains(&(id, i));
                if !keep {
                    claims.push(DeadParam {
                        block: id,
                        param: *v,
                    });
                    removed.insert(*v);
                }
                i += 1;
                keep
            });
        }
        drop_names(&mut out, &removed);
        Some((
            out,
            PassWitness::DeadParam(DeadParamWitness { params: claims }),
        ))
    }
}
