// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! A conservative projection of the actual explicit-edge-copy LIR. Block
//! parameter annotations declare types; only instructions assign values. The
//! graph retains every normal edge, including inner-loop stuttering and sinks.

use super::{Effect, EuclideanExit, Graph, MAX_NODES, MAX_VARIABLES, Node, Operand, Recurrence};
use crate::aarch64_omitted_trap::{EuclideanSource, bind_euclidean_loop};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use trust_cg_ir::provenance::SourceInstId;
use trust_cg_lower::instructions::{
    Block, DirectCallBinding, Instruction, IntCC, Opcode as Op, Value,
};
use trust_cg_lower::{Function, Type};

const MAX_INSTRUCTIONS: usize = MAX_NODES * 8;

fn scalar(ty: &Type) -> bool {
    matches!(ty, Type::B1 | Type::I8 | Type::I16 | Type::I32 | Type::I64)
}

pub(super) struct SourceLoop<'a> {
    pub(super) compare: SourceInstId,
    pub(super) branch: SourceInstId,
    pub(super) call: SourceInstId,
    pub(super) symbol: &'a str,
    pub(super) recurrence: Recurrence,
    pub(super) euclidean: Option<EuclideanSource>,
}

fn shape(inst: &Instruction, args: usize, results: usize) -> bool {
    inst.args.len() == args && inst.results.len() == results
}

// No unknown control or implicit register definitions are projected away.
fn ordinary(inst: &Instruction, function: &Function) -> bool {
    match &inst.opcode {
        Op::Iconst { ty, .. } => scalar(ty) && shape(inst, 0, 1),
        Op::GlobalRef { name } => name.len() <= 4096 && shape(inst, 0, 1),
        Op::StackAddr { slot } => {
            shape(inst, 0, 1) && (*slot as usize) < function.stack_slots.len()
        }
        Op::Copy => shape(inst, 1, 1),
        Op::Load { ty, .. } => scalar(ty) && shape(inst, 1, 1),
        Op::Iadd | Op::Imul | Op::Bor | Op::Ushr | Op::Urem | Op::Icmp { .. } => shape(inst, 2, 1),
        Op::Store { ty, .. } => scalar(ty) && shape(inst, 2, 0),
        Op::Call {
            name,
            binding: DirectCallBinding::Interposable,
        } => !name.is_empty() && name.len() <= 4096,
        _ => false,
    }
}

fn successors(inst: &Instruction) -> Option<Vec<Block>> {
    if !inst.results.is_empty() {
        return None;
    }
    Some(match &inst.opcode {
        Op::Jump { dest } if inst.args.is_empty() => vec![*dest],
        Op::Brif {
            cond,
            then_dest,
            else_dest,
        } if inst.args == [*cond] && then_dest != else_dest => vec![*then_dest, *else_dest],
        Op::Switch { cases, default } if inst.args.len() == 1 => {
            if cases.len() > MAX_NODES {
                return None;
            }
            let mut keys = HashSet::new();
            if cases.iter().any(|(key, _)| !keys.insert(*key)) {
                return None;
            }
            cases
                .iter()
                .map(|(_, dest)| *dest)
                .chain(std::iter::once(*default))
                .collect()
        }
        Op::Trap | Op::Return if inst.args.is_empty() => vec![],
        _ => return None,
    })
}

fn put(types: &mut HashMap<Value, Type>, value: Value, ty: Type) -> Option<bool> {
    match types.get(&value) {
        Some(old) if *old != ty => None,
        Some(_) => Some(false),
        None => {
            types.insert(value, ty);
            Some(true)
        }
    }
}

fn infer(function: &Function, blocks: &BTreeMap<Block, usize>) -> Option<HashMap<Value, Type>> {
    let mut types = function.value_types.clone();
    for block in blocks.keys() {
        for (value, ty) in &function.blocks.get(block)?.params {
            put(&mut types, *value, ty.clone())?;
        }
    }
    // A Value has one carrier type even though predecessor Copies can assign
    // it repeatedly. This fixpoint never infers a value or reaching definition.
    for _ in 0..=MAX_VARIABLES {
        let mut changed = false;
        for id in blocks.keys() {
            for inst in &function.blocks.get(id)?.instructions {
                let [dst] = inst.results.as_slice() else {
                    continue;
                };
                let ty = match &inst.opcode {
                    Op::Iconst { ty, .. } | Op::Load { ty, .. } => Some(ty.clone()),
                    Op::StackAddr { .. } | Op::GlobalRef { .. } => Some(Type::I64),
                    Op::Icmp { .. } => Some(Type::B1),
                    Op::Copy if inst.args.len() == 1 => types.get(&inst.args[0]).cloned(),
                    Op::Iadd | Op::Imul | Op::Bor | Op::Ushr | Op::Urem
                        if inst.args.len() == 2
                            && inst.args.iter().all(|v| types.get(v) == Some(&Type::I64)) =>
                    {
                        Some(Type::I64)
                    }
                    _ => None,
                };
                if let Some(ty) = ty {
                    changed |= put(&mut types, *dst, ty)?;
                }
            }
        }
        if !changed {
            return Some(types);
        }
    }
    None
}

fn predecessors_of(edges: &[Vec<usize>], target: usize) -> Vec<bool> {
    let mut reverse = vec![Vec::new(); edges.len()];
    for (from, next) in edges.iter().enumerate() {
        for &to in next {
            reverse[to].push(from);
        }
    }
    let mut seen = vec![false; edges.len()];
    let mut todo = vec![target];
    while let Some(node) = todo.pop() {
        if seen[node] {
            continue;
        }
        seen[node] = true;
        todo.extend(reverse[node].iter().copied());
    }
    seen
}

pub(super) fn bind(function: &Function, trap: SourceInstId) -> Option<SourceLoop<'_>> {
    if function.blocks.is_empty()
        || function.blocks.len() > MAX_NODES
        || !function.signature.params.is_empty()
        || !function.signature.returns.is_empty()
        || !function
            .blocks
            .get(&function.entry_block)?
            .params
            .is_empty()
        || !function.eh_info.is_empty()
        || function.stack_limit.is_some()
        || function.stack_protector != trust_cg_ir::function::StackProtectorMode::None
        || function.abi_sret_param.is_some()
        || !function.param_pointee_types.is_empty()
        || !function.sret_arg_callees.is_empty()
        || !function.sret_arg_indirect_callees.is_empty()
    {
        return None;
    }
    if function.value_types.len() > MAX_VARIABLES
        || function.value_types.values().any(|ty| !scalar(ty))
    {
        return None;
    }
    let mut seen_layout = HashSet::new();
    for id in &function.block_order {
        if !function.blocks.contains_key(id) || !seen_layout.insert(*id) {
            return None;
        }
    }
    let blocks: BTreeMap<_, _> = function
        .blocks
        .keys()
        .copied()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .enumerate()
        .map(|(n, id)| (id, n))
        .collect();
    let mut values = BTreeSet::new();
    let mut owners = HashMap::new();
    let mut count = 0usize;
    let mut edges = vec![Vec::new(); blocks.len()];
    for (id, number) in &blocks {
        let block = function.blocks.get(id)?;
        count = count.checked_add(block.instructions.len())?;
        if count > MAX_INSTRUCTIONS {
            return None;
        }
        if block.params.len() > MAX_VARIABLES {
            return None;
        }
        for (value, ty) in &block.params {
            if !scalar(ty) {
                return None;
            }
            if owners.insert(*value, (*id, ty.clone())).is_some() {
                return None;
            }
            values.insert(value.0);
        }
        let (last, prefix) = block.instructions.split_last()?;
        if !prefix.iter().all(|inst| ordinary(inst, function)) {
            return None;
        }
        edges[*number] = successors(last)?
            .iter()
            .map(|id| blocks.get(id).copied())
            .collect::<Option<Vec<_>>>()?;
        for inst in &block.instructions {
            if inst.args.len() > MAX_VARIABLES || inst.results.len() > MAX_VARIABLES {
                return None;
            }
            values.extend(inst.args.iter().map(|v| v.0));
            values.extend(inst.results.iter().map(|v| v.0));
        }
    }
    values.extend(function.value_types.keys().map(|v| v.0));
    if values.len() > MAX_VARIABLES {
        return None;
    }
    let variables: HashMap<_, _> = values
        .into_iter()
        .enumerate()
        .map(|(n, value)| (Value(value), n))
        .collect();
    let types = infer(function, &blocks)?;
    // Adapter/ISel convention: a parameter is assigned only by explicit,
    // well-typed predecessor Copy before Jump to the parameter's owner. An
    // unchanged carrier on a backedge receives NO implicit fresh assignment.
    for id in blocks.keys() {
        let block = function.blocks.get(id)?;
        let jump = match &block.instructions.last()?.opcode {
            Op::Jump { dest } => Some(*dest),
            _ => None,
        };
        let mut assigned = HashSet::new();
        for inst in &block.instructions {
            for dst in &inst.results {
                if let Some((owner, ty)) = owners.get(dst) {
                    if inst.opcode != Op::Copy
                        || !shape(inst, 1, 1)
                        || jump != Some(*owner)
                        || types.get(&inst.args[0]) != Some(ty)
                        || !assigned.insert(*dst)
                    {
                        return None;
                    }
                }
            }
        }
    }
    let terminal = Block(trap.block);
    let body = function.blocks.get(&terminal)?;
    if terminal == function.entry_block
        || !body.params.is_empty()
        || body.instructions.len().checked_sub(1)? != trap.index as usize
        || body.instructions.len() < 2
    {
        return None;
    }
    let last = body.instructions.last()?;
    if last.opcode != Op::Trap || !shape(last, 0, 0) {
        return None;
    }
    let call_index = body.instructions.len() - 2;
    let call = &body.instructions[call_index];
    let Op::Call {
        name: symbol,
        binding: DirectCallBinding::Interposable,
    } = &call.opcode
    else {
        return None;
    };
    if !call.results.is_empty()
        || body.instructions[..call_index]
            .iter()
            .any(|i| matches!(i.opcode, Op::Call { .. }))
    {
        return None;
    }
    let term_number = *blocks.get(&terminal)?;
    // Count edge occurrences, not just predecessor blocks: a second branch
    // arm or switch case cannot hide behind a deduplicated predecessor set.
    let mut incoming = edges.iter().enumerate().flat_map(|(source, targets)| {
        targets
            .iter()
            .filter_map(move |dest| (*dest == term_number).then_some(source))
    });
    let header_number = incoming.next()?;
    if incoming.next().is_some() {
        return None;
    }
    let header = *blocks.iter().find(|(_, n)| **n == header_number)?.0;
    let instructions = &function.blocks.get(&header)?.instructions;
    let (copy, compare_index) = match instructions.as_slice() {
        [cmp, _]
            if matches!(
                cmp.opcode,
                Op::Icmp {
                    cond: IntCC::UnsignedLessThan
                }
            ) =>
        {
            (None, 0usize)
        }
        [copy, cmp, _]
            if copy.opcode == Op::Copy
                && matches!(
                    cmp.opcode,
                    Op::Icmp {
                        cond: IntCC::UnsignedLessThan
                    }
                ) =>
        {
            (Some(copy), 1usize)
        }
        _ => return None,
    };
    let cmp = &instructions[compare_index];
    if !shape(cmp, 2, 1)
        || cmp.args[0] == cmp.args[1]
        || !cmp.args.iter().all(|v| types.get(v) == Some(&Type::I64))
    {
        return None;
    }
    let branch = instructions.last()?;
    let Op::Brif {
        cond,
        then_dest: work,
        else_dest,
    } = &branch.opcode
    else {
        return None;
    };
    if *else_dest != terminal
        || *work == terminal
        || *work == header
        || branch.args != [*cond]
        || cmp.results != [*cond]
    {
        return None;
    }
    let counter = if let Some(copy) = copy {
        if !shape(copy, 1, 1)
            || copy.results != [cmp.args[0]]
            || types.get(&copy.args[0]) != Some(&Type::I64)
        {
            return None;
        }
        copy.args[0]
    } else {
        cmp.args[0]
    };
    let limit = cmp.args[1];
    if counter == limit || cmp.results.contains(&counter) || cmp.results.contains(&limit) {
        return None;
    }
    let reaches_header = predecessors_of(&edges, header_number);
    let mut memory_or_call = vec![false; blocks.len()];
    let mut remainder = vec![false; blocks.len()];
    for (id, number) in &blocks {
        for inst in &function.blocks.get(id)?.instructions {
            match inst.opcode {
                Op::Call { .. } if reaches_header[*number] => return None,
                Op::Call { .. } | Op::Load { .. } | Op::Store { .. } => {
                    memory_or_call[*number] = true;
                }
                Op::Urem => remainder[*number] = true,
                _ => {}
            }
        }
    }
    let mut nodes = Vec::with_capacity(blocks.len());
    for (id, number) in &blocks {
        let mut effects = Vec::new();
        for inst in &function.blocks.get(id)?.instructions {
            let precise = match (&inst.opcode, inst.args.as_slice(), inst.results.as_slice()) {
                (Op::Iconst { ty: Type::I64, imm }, [], [dst]) => Some(Effect::Constant {
                    dst: variables[dst],
                    value: *imm as u64,
                }),
                (Op::Copy, [src], [dst])
                    if types.get(src) == Some(&Type::I64) && types.get(dst) == Some(&Type::I64) =>
                {
                    Some(Effect::Copy {
                        dst: variables[dst],
                        src: variables[src],
                    })
                }
                (Op::Iadd, [lhs, rhs], [dst])
                    if [lhs, rhs, dst]
                        .iter()
                        .all(|v| types.get(*v) == Some(&Type::I64)) =>
                {
                    Some(Effect::Add {
                        dst: variables[dst],
                        lhs: Operand::Variable(variables[lhs]),
                        rhs: Operand::Variable(variables[rhs]),
                    })
                }
                _ => None,
            };
            if let Some(effect) = precise {
                effects.push(effect);
            } else {
                effects.extend(
                    inst.results
                        .iter()
                        .map(|value| Effect::Unknown(variables[value])),
                );
            }
        }
        nodes.push(Node {
            effects,
            next: edges[*number].clone(),
        });
    }
    let graph = Graph {
        nodes,
        variables: variables.len(),
    };
    let work_number = *blocks.get(work)?;
    let recurrence = graph.recurrence(
        *blocks.get(&function.entry_block)?,
        header_number,
        work_number,
        [variables[&counter], variables[&limit]],
    )?;

    let euclidean = blocks.keys().filter(|&&id| id != terminal).find_map(|id| {
        let (last, prefix) = function.blocks[id].instructions.split_last()?;
        if last.opcode != Op::Trap {
            return None;
        }
        let phase = bind_euclidean_loop(
            function,
            SourceInstId {
                block: id.0,
                index: u32::try_from(prefix.len()).ok()?,
            },
        )?;
        let remainder_block = *blocks.get(&Block(phase.remainder.0.block))?;
        graph.finite_work(
            work_number,
            header_number,
            EuclideanExit {
                backedge: (remainder_block, *blocks.get(&Block(phase.switch.0.block))?),
                zero: *blocks.get(&phase.zero)?,
                impossible: Some((
                    *blocks.get(&phase.impossible.0)?,
                    *blocks.get(&phase.impossible.1)?,
                )),
            },
            |at| !memory_or_call[at] && (!remainder[at] || at == remainder_block),
        )?;
        Some(phase)
    });
    Some(SourceLoop {
        compare: SourceInstId {
            block: header.0,
            index: compare_index as u32,
        },
        branch: SourceInstId {
            block: header.0,
            index: (instructions.len() - 1) as u32,
        },
        call: SourceInstId {
            block: terminal.0,
            index: call_index as u32,
        },
        symbol,
        recurrence,
        euclidean,
    })
}
