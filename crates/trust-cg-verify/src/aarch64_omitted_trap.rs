// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Account for a plain source trap behind two contradictory tests of one
//! I64 value. The proof is local to the switch edge and the unmodified
//! value flowing along it, including when the switch is a loop header.
//! The separate machine binder checks that the final division remains
//! guarded. Neither check grants instruction, ABI, or encoding credit.

#[path = "../../../formal/lean/Trust/A64/RedundantZeroGuard.lean"]
clean mod redundant_zero_guard;

use trust_cg_ir::MachFunction;
use trust_cg_ir::provenance::{SourceInstDigest, SourceInstId};
use trust_cg_lower::instructions::{Block, Instruction, IntCC, Opcode as Op, Value};
use trust_cg_lower::{Function, Type};

struct SourceEdges {
    switch: (SourceInstId, SourceInstDigest),
    remainder: (SourceInstId, SourceInstDigest),
    divisor: Value,
    dividend: Value,
    remainder_value: Value,
    zero: Block,
    retest: Block,
}

pub(crate) struct EuclideanSource {
    pub(crate) switch: (SourceInstId, SourceInstDigest),
    pub(crate) remainder: (SourceInstId, SourceInstDigest),
    pub(crate) zero: Block,
    pub(crate) impossible: (Block, Block),
}

fn unique_predecessor(source: &Function, target: Block) -> Option<Block> {
    if source.entry_block == target {
        return None;
    }
    let mut predecessors = source
        .blocks
        .iter()
        .filter_map(|(&id, block)| block.successors().contains(&target).then_some(id));
    let predecessor = predecessors.next()?;
    predecessors.next().is_none().then_some(predecessor)
}

fn result(inst: &Instruction, args: &[Value]) -> Option<Value> {
    let [value] = inst.results.as_slice() else {
        return None;
    };
    (inst.args == args).then_some(*value)
}

fn hint_agrees(source: &Function, value: Value, ty: Type) -> bool {
    source
        .value_types
        .get(&value)
        .is_none_or(|hint| *hint == ty)
}

fn coordinate(block: Block, index: u32, inst: &Instruction) -> (SourceInstId, SourceInstDigest) {
    (
        SourceInstId {
            block: block.0,
            index,
        },
        inst.lowering_digest(),
    )
}

fn bind_source(source: &Function, trap: SourceInstId) -> Option<SourceEdges> {
    if !source.eh_info.is_empty() || !source.blocks.contains_key(&source.entry_block) {
        return None;
    }
    let trap_block = Block(trap.block);
    let trapped = source.blocks.get(&trap_block)?;
    let last = trapped.instructions.last()?;
    if !trapped.params.is_empty()
        || trapped.instructions.len() - 1 != trap.index as usize
        || !matches!(last.opcode, Op::Trap)
        || !last.args.is_empty()
        || !last.results.is_empty()
    {
        return None;
    }

    let retest_block = unique_predecessor(source, trap_block)?;
    let header_block = unique_predecessor(source, retest_block)?;
    if header_block == trap_block || header_block == retest_block {
        return None;
    }
    let header = source.blocks.get(&header_block)?;
    let retest = source.blocks.get(&retest_block)?;
    let [copy_selector, switch] = header.instructions.as_slice() else {
        return None;
    };
    let Op::Switch { cases, default } = &switch.opcode else {
        return None;
    };
    let [(0, zero_block)] = cases.as_slice() else {
        return None;
    };
    let [divisor] = copy_selector.args.as_slice() else {
        return None;
    };
    let selector = result(copy_selector, &[*divisor])?;
    if !matches!(copy_selector.opcode, Op::Copy)
        || *default != retest_block
        || *zero_block == retest_block
        || !source.blocks.contains_key(zero_block)
        || switch.args != [selector]
        || !switch.results.is_empty()
        || !retest.params.is_empty()
    {
        return None;
    }

    let [
        copy_divisor,
        integer_zero,
        is_zero,
        boolean_false,
        is_nonzero,
        branch,
    ] = retest.instructions.as_slice()
    else {
        return None;
    };
    let divisor_copy = result(copy_divisor, &[*divisor])?;
    let zero = result(integer_zero, &[])?;
    let equals_zero = result(is_zero, &[divisor_copy, zero])?;
    let zero_flag = result(boolean_false, &[])?;
    let differs_from_zero = result(is_nonzero, &[equals_zero, zero_flag])?;
    let Op::Brif {
        cond,
        then_dest,
        else_dest,
    } = branch.opcode
    else {
        return None;
    };
    if !matches!(copy_divisor.opcode, Op::Copy)
        || !matches!(
            integer_zero.opcode,
            Op::Iconst {
                ty: Type::I64,
                imm: 0
            }
        )
        || !matches!(
            boolean_false.opcode,
            Op::Iconst {
                ty: Type::B1,
                imm: 0
            }
        )
        || !matches!(is_zero.opcode, Op::Icmp { cond: IntCC::Equal })
        || !matches!(is_nonzero.opcode, Op::Icmp { cond: IntCC::Equal })
        || cond != differs_from_zero
        || branch.args != [differs_from_zero]
        || !branch.results.is_empty()
        || else_dest != trap_block
        || then_dest == trap_block
        || unique_predecessor(source, then_dest)? != retest_block
    {
        return None;
    }
    let safe = source.blocks.get(&then_dest)?;
    let remainder = safe.instructions.first()?;
    let [dividend, _] = remainder.args.as_slice() else {
        return None;
    };
    let remainder_value = result(remainder, &[*dividend, divisor_copy])?;
    if !safe.params.is_empty() || !matches!(remainder.opcode, Op::Urem) {
        return None;
    }

    // These values must refer to the same live I64 parameters throughout
    // this visit to the switch and retest. A later latch can assign the
    // next iteration's parameters, so a function-wide def lookup is wrong.
    let mut params = std::collections::HashMap::with_capacity(header.params.len());
    for (value, ty) in &header.params {
        if params.insert(*value, ty).is_some() {
            return None;
        }
    }
    if [dividend, divisor].into_iter().any(|value| {
        params.get(value).copied() != Some(&Type::I64) || !hint_agrees(source, *value, Type::I64)
    }) {
        return None;
    }
    let results = [
        (selector, Type::I64),
        (divisor_copy, Type::I64),
        (zero, Type::I64),
        (equals_zero, Type::B1),
        (zero_flag, Type::B1),
        (differs_from_zero, Type::B1),
        (remainder_value, Type::I64),
    ];
    for (value, ty) in &results {
        if params.insert(*value, ty).is_some() || !hint_agrees(source, *value, ty.clone()) {
            return None;
        }
    }

    // The switch default fixes the repeated I64 zero test to false.
    // The source then compares that Boolean to false, and the trap is
    // reached only on the false edge of this second comparison.
    let take_then = trust_cg_a64_zero_guard_not(false);
    let take_trap = trust_cg_a64_zero_guard_not(take_then);
    (!take_trap).then(|| SourceEdges {
        switch: coordinate(header_block, 1, switch),
        remainder: coordinate(then_dest, 0, remainder),
        divisor: *divisor,
        dividend: *dividend,
        remainder_value,
        zero: *zero_block,
        retest: retest_block,
    })
}

pub(crate) fn bind_euclidean_loop(
    source: &Function,
    trap: SourceInstId,
) -> Option<EuclideanSource> {
    let edges = bind_source(source, trap)?;
    let header = Block(edges.switch.0.block);
    let safe = source.blocks.get(&Block(edges.remainder.0.block))?;
    let [
        _,
        save_divisor,
        save_remainder,
        assign_dividend,
        assign_divisor,
        jump,
    ] = safe.instructions.as_slice()
    else {
        return None;
    };
    let next_dividend = result(save_divisor, &[edges.divisor])?;
    let next_divisor = result(save_remainder, &[edges.remainder_value])?;
    if [
        save_divisor,
        save_remainder,
        assign_dividend,
        assign_divisor,
    ]
    .iter()
    .any(|inst| inst.opcode != Op::Copy)
        || result(assign_dividend, &[next_dividend])? != edges.dividend
        || result(assign_divisor, &[next_divisor])? != edges.divisor
        || !matches!(jump.opcode, Op::Jump { dest } if dest == header)
        || !jump.args.is_empty()
        || !jump.results.is_empty()
        || edges.dividend == edges.divisor
        || next_dividend == next_divisor
    {
        return None;
    }
    let params = &source.blocks.get(&header)?.params;
    for temp in [next_dividend, next_divisor] {
        if temp == edges.remainder_value
            || params.iter().any(|(param, _)| *param == temp)
            || !hint_agrees(source, temp, Type::I64)
        {
            return None;
        }
    }

    Some(EuclideanSource {
        switch: edges.switch,
        remainder: edges.remainder,
        zero: edges.zero,
        impossible: (edges.retest, Block(trap.block)),
    })
}

pub(crate) fn allows_omission(
    source: &Function,
    machine: &MachFunction,
    trap: SourceInstId,
) -> bool {
    if source.name != machine.name {
        return false;
    }
    let Some(edges) = bind_source(source, trap) else {
        return false;
    };
    let trap_block_omitted = machine.block_order.iter().all(|block| {
        machine.blocks.get(block.0 as usize).is_some_and(|body| {
            body.insts.iter().all(|&id| {
                machine
                    .inst_lowering_provenance(id)
                    .source_id()
                    .is_none_or(|source_id| source_id.block != trap.block)
            })
        })
    });
    trap_block_omitted
        && crate::aarch64_omitted_trap_machine::bind_guarded_remainder(
            machine,
            edges.switch,
            edges.remainder,
        )
        .is_some()
}
