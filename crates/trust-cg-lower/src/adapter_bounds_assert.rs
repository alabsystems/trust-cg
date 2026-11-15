// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Historical compare/assert shape analysis, retained for regression evidence.
//! v52 source Assert admission refuses unknown and unsupported panic semantics
//! before this analysis. A stated panic kind must never become a bare trap.

use super::{GuardCarrierArch, Inst, TrustIrFunction, Ty, ValueId};
use trust_cg_ir::fast_hash::FxHashMap as HashMap;
use trust_ir::{Constant, ICmpOp};

pub(super) fn index(
    function: &TrustIrFunction,
    arch: GuardCarrierArch,
) -> HashMap<ValueId, (ValueId, u64)> {
    if !function
        .blocks
        .iter()
        .flat_map(|block| &block.body)
        .any(|node| matches!(node.inst, Inst::Assert { .. }))
    {
        return HashMap::default();
    }
    let mut definitions = HashMap::<ValueId, usize>::default();
    let mut uses = HashMap::<ValueId, usize>::default();
    let mut constants = HashMap::default();
    for block in &function.blocks {
        for (id, _) in &block.params {
            *definitions.entry(*id).or_default() += 1;
        }
        for (position, node) in block.body.iter().enumerate() {
            for id in &node.results {
                *definitions.entry(*id).or_default() += 1;
            }
            node.inst.visit_value_operands(|id| {
                *uses.entry(id).or_default() += 1;
            });
            if let Inst::Const {
                ty: ty @ (Ty::I64 | Ty::U64),
                value: Constant::Int(value),
            } = &node.inst
                && let [id] = node.results.as_slice()
                && let Ok(value) = u64::try_from(*value)
            {
                constants.insert(*id, (ty, value, block.id, position));
            }
        }
    }
    let mut pairs = HashMap::default();
    for block in &function.blocks {
        for (position, nodes) in block.body.windows(2).enumerate() {
            let (compare, assertion) = (&nodes[0], &nodes[1]);
            let Inst::ICmp {
                op: ICmpOp::Ult,
                ty: ty @ (Ty::I64 | Ty::U64),
                lhs,
                rhs,
            } = &compare.inst
            else {
                continue;
            };
            let [result] = compare.results.as_slice() else {
                continue;
            };
            // A sited check (v54) is not the historical kindless shape.
            let Inst::Assert {
                cond,
                kind,
                site: None,
            } = assertion.inst
            else {
                continue;
            };
            if !kind.is_unspecified() {
                continue;
            }
            let Some(&(bound_ty, bound, bound_block, bound_position)) = constants.get(rhs) else {
                continue;
            };
            // Keep other consumers, metadata and debug value bindings intact.
            // Unique definitions prevent a reused SSA id from selecting a
            // different bound or from suppressing another comparison.
            if cond != *result
                || uses.get(result) != Some(&1)
                || [result, lhs, rhs]
                    .into_iter()
                    .any(|id| definitions.get(id) != Some(&1))
                || bound_ty != ty
                || bound_block != block.id
                || bound_position >= position
                || bound > arch.max_exact_bound()
                || !compare.proofs.is_empty()
                || compare.span.is_some()
                || compare.proof_context.is_some()
                || assertion.proof_context.is_some()
                || !assertion.proofs.is_empty()
                || !assertion.results.is_empty()
            {
                continue;
            }
            pairs.insert(*result, (*lhs, bound));
        }
    }
    pairs
}

#[cfg(test)]
#[path = "adapter_bounds_assert_tests.rs"]
mod tests;
