// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Control over the original typed Core graph. Nodes are never rewritten,
//! cloned into a synthetic source, or stripped of proof/guard metadata.

use super::*;
use TrustIrAffineLoweringError::{InvalidTrustIr as Invalid, UnsupportedTrustIr as Unsupported};
use std::collections::HashSet;
use trust_ir::value::BlockId;

fn control_node(node: &trust_ir::InstrNode) -> Result<(), TrustIrAffineLoweringError> {
    if !node.results.is_empty() || node.proof_context.is_some() {
        return Err(Invalid(
            "control node has results or a non-call proof context".into(),
        ));
    }
    Ok(())
}

fn read(
    values: &SourceValues,
    id: ValueId,
    expected: SourceType,
) -> Result<ScalarValue, TrustIrAffineLoweringError> {
    let (ty, value) = values
        .get(&id)
        .copied()
        .ok_or_else(|| Invalid(format!("control edge uses undefined source value {id:?}")))?;
    if ty != expected {
        return Err(Invalid(format!(
            "control edge operand {id:?} has wrong type"
        )));
    }
    Ok(value)
}

fn find(
    source: &trust_ir::Function,
    id: BlockId,
) -> Result<&trust_ir::Block, TrustIrAffineLoweringError> {
    source
        .block(id)
        .ok_or_else(|| Invalid(format!("control edge names missing block {id:?}")))
}

pub(super) fn diamond_result(
    source: &trust_ir::Function,
    signature: &FuncTy,
    return_type: Option<SourceType>,
    domain: &mut Option<IntegerType>,
    mut values: SourceValues,
    pointer_bits: u32,
) -> Result<(Option<ScalarValue>, usize), TrustIrAffineLoweringError> {
    let Some(SourceType::Integer(integer)) = return_type else {
        return Err(Unsupported(
            "arithmetic diamond needs one integer result".into(),
        ));
    };
    let mut count = 0usize;
    for block in &source.blocks {
        count = count
            .checked_add(block.body.len())
            .ok_or_else(|| Unsupported("source instruction count overflow".into()))?;
        if count > 256 {
            return Err(Unsupported(
                "arithmetic diamond exceeds 256 source instructions".into(),
            ));
        }
        if block.params.len() > 8 {
            return Err(Unsupported(
                "arithmetic diamond exceeds eight block parameters".into(),
            ));
        }
        if block.body.iter().any(|node| node.results.len() > 1) {
            return Err(Invalid("scalar source node has multiple results".into()));
        }
    }
    // Bound the work before allocating a global SSA namespace or cloning arm
    // environments. Independent branches cannot reuse each other's result IDs.
    let mut blocks = HashSet::new();
    let mut definitions = HashSet::new();
    for block in &source.blocks {
        if !blocks.insert(block.id) {
            return Err(Invalid("duplicate source block ID".into()));
        }
        for value in block
            .params
            .iter()
            .map(|(id, _)| id)
            .chain(block.body.iter().flat_map(|node| node.results.iter()))
        {
            if !definitions.insert(*value) {
                return Err(Invalid(format!(
                    "duplicate source SSA definition {value:?}"
                )));
            }
        }
    }
    let entry = find(source, source.entry)?;
    let (branch, prefix) = entry
        .body
        .split_last()
        .ok_or_else(|| Invalid("entry has no terminator".into()))?;
    let Inst::CondBr {
        cond,
        then_target,
        then_args,
        else_target,
        else_args,
    } = &branch.inst
    else {
        return Err(Unsupported(
            "arithmetic diamond needs one entry CondBr".into(),
        ));
    };
    control_node(branch)?;
    if then_args.len() != find(source, *then_target)?.params.len()
        || else_args.len() != find(source, *else_target)?.params.len()
    {
        return Err(Invalid("diamond entry edge argument arity mismatch".into()));
    }
    if !then_args.is_empty() || !else_args.is_empty() {
        return Err(Unsupported(
            "arithmetic diamond arm parameters are outside the profile".into(),
        ));
    }
    if *then_target == *else_target || *then_target == source.entry || *else_target == source.entry
    {
        return Err(Invalid(
            "diamond entry edges do not name two distinct arms".into(),
        ));
    }
    if evaluate_nodes(
        prefix,
        signature,
        return_type,
        domain,
        &mut values,
        pointer_bits,
    )?
    .0
    {
        return Err(Invalid("entry prefix returns before its branch".into()));
    }
    let ScalarValue::Bool(condition) = read(&values, *cond, SourceType::Bool)? else {
        return Err(Invalid("noncanonical source branch condition".into()));
    };
    // ScalarValue is a fixed-size affine/predicate/flat-select value. The
    // global 256-node/8-parameter profile bounds both environment clones.
    let mut join_id = None;
    let mut arm_values = Vec::new();
    for target in [*then_target, *else_target] {
        let arm = find(source, target)?;
        if !arm.params.is_empty() {
            return Err(Unsupported(
                "arithmetic diamond arm has block parameters".into(),
            ));
        }
        let (jump, body) = arm
            .body
            .split_last()
            .ok_or_else(|| Invalid("source arm has no terminator".into()))?;
        let Inst::Br { target: join, args } = &jump.inst else {
            return Err(Unsupported(
                "arithmetic diamond arm does not end in Br".into(),
            ));
        };
        control_node(jump)?;
        if *join == source.entry || *join == *then_target || *join == *else_target {
            return Err(Invalid(
                "arithmetic diamond arm has a cyclic/rejoining edge".into(),
            ));
        }
        if join_id.is_some_and(|prior| prior != *join) {
            return Err(Invalid(
                "arithmetic diamond arms target different merges".into(),
            ));
        }
        join_id = Some(*join);
        let [arg] = args.as_slice() else {
            return Err(Invalid(
                "arithmetic diamond merge edge needs one argument".into(),
            ));
        };
        let mut environment = values.clone();
        // Every original node is evaluated, including an untaken arm and
        // dead comparison guard. Nothing is admitted by a constant condition.
        if evaluate_nodes(
            body,
            signature,
            return_type,
            domain,
            &mut environment,
            pointer_bits,
        )?
        .0
        {
            return Err(Invalid("source arm returns before its merge edge".into()));
        }
        arm_values.push(
            read(&environment, *arg, SourceType::Integer(integer))?
                .as_affine(integer.bits())
                .ok_or_else(|| {
                    Unsupported("arithmetic diamond arm result is a nested selection".into())
                })?,
        );
    }
    let join = find(
        source,
        join_id.ok_or_else(|| Invalid("missing merge".into()))?,
    )?;
    let [(parameter, ty)] = join.params.as_slice() else {
        return Err(Invalid(
            "arithmetic diamond merge needs one parameter".into(),
        ));
    };
    if SourceType::from_ty(ty)? != SourceType::Integer(integer) {
        return Err(Invalid(
            "arithmetic diamond merge has wrong integer type".into(),
        ));
    }
    let [ret] = join.body.as_slice() else {
        return Err(Unsupported(
            "arithmetic diamond merge must contain only Return".into(),
        ));
    };
    control_node(ret)?;
    let Inst::Return { values: operands } = &ret.inst else {
        return Err(Unsupported(
            "arithmetic diamond merge does not return".into(),
        ));
    };
    if operands.as_slice() != [*parameter] {
        return Err(Invalid(
            "arithmetic diamond return does not read its merge parameter".into(),
        ));
    }
    admit_type(domain, integer)?;
    Ok((
        Some(ScalarValue::select(
            integer.bits(),
            condition,
            arm_values[0],
            arm_values[1],
        )),
        count,
    ))
}
