// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Independent normalization of a four-block diamond with pure scalar arms.
//! Copies, canonical constants, wrapping add/subtract, integer comparisons and
//! Eq/Ne integer selects have no effects or exceptional execution to move
//! across the branch. The existing scalar evaluator checks their exact types
//! and semantics, including flat/nested selection bounds; this only renames SSA.
//! This view supplies the Rust frame gate, never raw replay terms or proof credit.

use std::collections::{HashMap, HashSet};
use trust_cg_lower::instructions::{Instruction, IntCC, Opcode as L, Value};
use trust_cg_lower::{Function, Type};

pub(super) fn source_view(source: &Function) -> Option<Function> {
    if source.blocks.len() != 4 {
        return None;
    }
    let instruction_count = source.blocks.values().try_fold(0usize, |count, block| {
        count.checked_add(block.instructions.len())
    })?;
    // All admitted scalar nodes have at most three inputs and one result.
    // Bound malformed LIR before collecting SSA IDs or cloning source/views;
    // the later scalar evaluator remains authoritative for exact arities and
    // types. These shapes were already outside its register-ABI domain.
    if source.signature.returns.len() != 1
        || source.signature.params.len() > 8
        || instruction_count > 256
        || source.value_types.len()
            > instruction_count.checked_add(source.signature.params.len())?
        || source.blocks.values().any(|block| {
            block.params.len() > 8
                || block
                    .instructions
                    .iter()
                    .any(|inst| inst.args.len() > 3 || inst.results.len() > 1)
        })
        || (!source.block_order.is_empty()
            && (source.block_order.len() != 4
                || source.block_order.iter().collect::<HashSet<_>>().len() != 4
                || source
                    .block_order
                    .iter()
                    .any(|id| !source.blocks.contains_key(id))))
    {
        return None;
    }
    let return_type = &source.signature.returns[0];
    if !matches!(return_type, Type::I32 | Type::I64)
        || source.signature.params.iter().any(|ty| ty != return_type)
    {
        return None;
    }
    let entry = source.blocks.get(&source.entry_block)?;
    let (branch, prefix) = entry.instructions.split_last()?;
    let L::Brif {
        cond,
        then_dest,
        else_dest,
    } = branch.opcode
    else {
        return None;
    };
    if branch.args != [cond] || !branch.results.is_empty() {
        return None;
    }
    let mut ids = HashSet::from([source.entry_block]);
    if !ids.insert(then_dest) || !ids.insert(else_dest) {
        return None;
    }
    let mut arms = Vec::new();
    let mut join_id = None;
    for id in [then_dest, else_dest] {
        let block = source.blocks.get(&id)?;
        let (last, body) = block.instructions.split_last()?;
        let L::Jump { dest } = last.opcode else {
            return None;
        };
        if !block.params.is_empty()
            || !last.args.is_empty()
            || !last.results.is_empty()
            || join_id.is_some_and(|previous| previous != dest)
        {
            return None;
        }
        join_id = Some(dest);
        arms.push(body);
    }
    let join_id = join_id?;
    if !ids.insert(join_id) {
        return None;
    }
    let join = source.blocks.get(&join_id)?;
    let [ret] = join.instructions.as_slice() else {
        return None;
    };
    let [returned] = ret.args.as_slice() else {
        return None;
    };
    if ret.opcode != L::Return
        || !ret.results.is_empty()
        || join.params.as_slice() != [(*returned, source.signature.returns[0].clone())]
    {
        return None;
    }
    // Prefix semantics, definitions and types are checked by the scalar
    // interpreter. Each arm reads only prefix or earlier same-arm values.
    // The sole cross-arm definition alias is the lowered merge parameter;
    // fresh view IDs keep the two independently evaluated values distinct.
    let mut common: HashSet<Value> = (0..source.signature.params.len())
        .map(|n| Value(n as u32))
        .collect();
    common.extend(prefix.iter().flat_map(|inst| inst.results.iter().copied()));
    if !common.contains(&cond) || common.contains(returned) {
        return None;
    }
    let mut next = source
        .blocks
        .values()
        .flat_map(|b| b.instructions.iter())
        .flat_map(|i| i.args.iter().chain(&i.results))
        .map(|v| v.0)
        .chain(common.iter().map(|v| v.0))
        .max()?
        .checked_add(1)?;
    let mut instructions = prefix.to_vec();
    let mut destinations: HashMap<Value, Vec<Value>> =
        common.iter().map(|v| (*v, vec![*v])).collect();
    let mut arm_results = Vec::new();
    let mut prior_definitions = HashSet::new();
    for body in arms {
        let mut values: HashMap<Value, Value> = common.iter().map(|v| (*v, *v)).collect();
        let mut definitions = HashSet::new();
        for inst in body {
            let arity = match &inst.opcode {
                L::Copy => 1,
                L::Iconst { ty, .. } if ty == return_type => 0,
                L::Iconst {
                    ty: Type::B1,
                    imm: 0 | 1,
                } => 0,
                L::Iadd | L::Isub | L::Icmp { .. } => 2,
                L::Select {
                    cond: IntCC::Equal | IntCC::NotEqual,
                } => 3,
                _ => return None,
            };
            let [output] = inst.results.as_slice() else {
                return None;
            };
            if inst.args.len() != arity
                || values.contains_key(output)
                || (prior_definitions.contains(output) && output != returned)
            {
                return None;
            }
            let args = inst
                .args
                .iter()
                .map(|input| values.get(input).copied())
                .collect::<Option<Vec<_>>>()?;
            let output_new = Value(next);
            next = next.checked_add(1)?;
            values.insert(*output, output_new);
            definitions.insert(*output);
            destinations.entry(*output).or_default().push(output_new);
            instructions.push(Instruction {
                opcode: inst.opcode.clone(),
                args,
                results: vec![output_new],
            });
        }
        if !definitions.contains(returned) {
            return None;
        }
        arm_results.push(*values.get(returned)?);
        prior_definitions.extend(definitions);
    }
    let selected = Value(next);
    instructions.push(Instruction {
        opcode: L::Select {
            cond: IntCC::NotEqual,
        },
        args: vec![cond, arm_results[0], arm_results[1]],
        results: vec![selected],
    });
    instructions.push(Instruction {
        opcode: L::Return,
        args: vec![selected],
        results: vec![],
    });
    let mut view = source.clone();
    view.value_types.clear();
    for (old, ty) in source
        .value_types
        .iter()
        .chain(join.params.iter().map(|(v, t)| (v, t)))
    {
        for new in destinations.get(old)? {
            if view
                .value_types
                .insert(*new, ty.clone())
                .is_some_and(|prior| prior != *ty)
            {
                return None;
            }
        }
    }
    let mut block = entry.clone();
    block.instructions = instructions;
    block.source_locs.clear();
    view.blocks.clear();
    view.blocks.insert(source.entry_block, block);
    view.block_order = vec![source.entry_block];
    view.trust_ir_origins.clear();
    Some(view)
}
