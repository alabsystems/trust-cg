// trust-cg-irmid/passes/branch_fold.rs - constant-branch folding
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Constant-branch folding: a `condbr` on a `const bool`, or a `switch` on an
//! integer `const` whose case values are integer constants of its type,
//! becomes a `br` to the edge it always takes (the first matching case, else
//! the default). A `switch` that matches no case and declares its default
//! unreachable is left: taking the default there is undefined behaviour, and
//! folding it would only pick one outcome of it. When a branch was folded,
//! blocks no longer reachable from the entry (by the shared `CfgAnalysis`)
//! are then removed.

use std::collections::{BTreeSet, HashMap, HashSet};

use trust_cg_verify::trust_ir_mid_tv::{BranchFoldWitness, PassWitness};
use trust_ir::{BlockId, Constant, Function, Inst, Ty, ValueId};

use super::{MidPass, PassContext, drop_names, int_shape, sole_defs};
use crate::cfg::TrustIrCfg;

pub(crate) struct BranchFold;

fn in_range(value: i128, bits: u32, signed: bool) -> bool {
    if bits >= 128 {
        return signed || value >= 0;
    }
    if signed {
        let half = 1i128 << (bits - 1);
        value >= -half && value < half
    } else {
        value >= 0 && value < (1i128 << bits)
    }
}

/// The edge the terminator `inst` always takes, if it branches on a constant.
fn folded_edge(
    defs: &HashMap<ValueId, &Inst>,
    pointer_bits: u32,
    inst: &Inst,
) -> Option<(BlockId, Vec<ValueId>)> {
    match inst {
        Inst::CondBr {
            cond,
            then_target,
            then_args,
            else_target,
            else_args,
        } => match defs.get(cond)? {
            Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(b),
            } => Some(if *b {
                (*then_target, then_args.clone())
            } else {
                (*else_target, else_args.clone())
            }),
            _ => None,
        },
        Inst::Switch {
            value,
            default,
            default_args,
            cases,
            exhaustive_enum_unreachable,
        } => {
            let Inst::Const {
                ty,
                value: Constant::Int(scrutinee),
            } = defs.get(value)?
            else {
                return None;
            };
            let (bits, signed) = int_shape(ty, pointer_bits)?;
            if !in_range(*scrutinee, bits, signed) {
                return None;
            }
            let mut edge = None;
            for case in cases {
                let Constant::Int(c) = case.value else {
                    return None;
                };
                if !in_range(c, bits, signed) {
                    return None;
                }
                if edge.is_none() && c == *scrutinee {
                    edge = Some((case.target, case.args.clone()));
                }
            }
            match edge {
                Some(edge) => Some(edge),
                None if *exhaustive_enum_unreachable => None,
                None => Some((*default, default_args.clone())),
            }
        }
        _ => None,
    }
}

impl MidPass for BranchFold {
    fn name(&self) -> &'static str {
        "branch_fold"
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let defs = sole_defs(func);
        let mut out = func.clone();
        let mut witness = BranchFoldWitness::default();
        for block in &mut out.blocks {
            let Some(last) = block.body.last_mut() else {
                continue;
            };
            if !matches!(last.inst, Inst::CondBr { .. } | Inst::Switch { .. }) {
                continue;
            }
            if let Some((target, args)) = folded_edge(&defs, cx.pointer_bits, &last.inst) {
                last.inst = Inst::Br { target, args };
                witness
                    .folds
                    .push(trust_cg_verify::trust_ir_mid_tv::BranchFold {
                        block: block.id,
                        target,
                    });
            }
        }
        if witness.folds.is_empty() {
            // Only a fold makes blocks unreachable; a function without one is
            // left as it is (the analysis is not free on a wide `switch`).
            return None;
        }
        let reachable: BTreeSet<BlockId> =
            TrustIrCfg::new(&out).analysis().rpo.into_iter().collect();
        let mut removed_values = HashSet::new();
        for block in &out.blocks {
            if reachable.contains(&block.id) || block.id == out.entry {
                continue;
            }
            witness.removed_blocks.push(block.id);
            removed_values.extend(block.params.iter().map(|(v, _)| *v));
            for node in &block.body {
                removed_values.extend(node.results.iter().copied());
            }
        }
        if witness.folds.is_empty() && witness.removed_blocks.is_empty() {
            return None;
        }
        let doomed: HashSet<BlockId> = witness.removed_blocks.iter().copied().collect();
        out.blocks.retain(|b| !doomed.contains(&b.id));
        drop_names(&mut out, &removed_values);
        Some((out, PassWitness::BranchFold(witness)))
    }
}
