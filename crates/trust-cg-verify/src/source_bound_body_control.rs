// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Raw source and actual machine control are walked independently. A normalized
//! source view may decide applicability, but supplies neither return term.

use super::*;
use trust_cg_lower::Function;
use trust_cg_lower::instructions::Instruction;

fn source_fork_fits(values: &HashMap<Value, SourceValue>) -> Option<()> {
    let nodes = values
        .values()
        .try_fold(0usize, |total, value| total.checked_add(value.term.nodes))?;
    (nodes.checked_mul(2)? <= MAX_NODES).then_some(())
}

pub(super) fn source_result(
    source: &Function,
    view: &Function,
    integer_type: &Type,
    bits: u32,
    comparison: bool,
    mut values: HashMap<Value, SourceValue>,
) -> Option<Term> {
    let entry = source.blocks.get(&source.entry_block)?;
    // Applicability already admits only chains or an entry Brif diamond.
    // Inspect that original terminator instead of cloning a second chain view.
    if !matches!(entry.instructions.last()?.opcode, L::Brif { .. }) {
        let block = view.blocks.get(&view.entry_block)?;
        return source_run(
            &block.instructions,
            integer_type,
            bits,
            comparison,
            &mut values,
        )?;
    }
    // Independently read the original CFG's branch and each arm's merge
    // definition. Do not use the frame normalizer's renamed values or Select.
    if source.blocks.len() != 4 || comparison {
        return None;
    }
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
    if source_run(prefix, integer_type, bits, comparison, &mut values)?.is_some() {
        return None;
    }
    let selector = values.get(&cond)?;
    if !selector.boolean {
        return None;
    }
    let selector = selector
        .term
        .unary(3, |value| value.eq_expr(E::bv_const(0, 1)).not_expr())?;
    let mut merge = None;
    let mut arms: Vec<&[Instruction]> = Vec::new();
    for id in [then_dest, else_dest] {
        let arm = source.blocks.get(&id)?;
        let (jump, instructions) = arm.instructions.split_last()?;
        let L::Jump { dest } = jump.opcode else {
            return None;
        };
        if !arm.params.is_empty()
            || !jump.args.is_empty()
            || !jump.results.is_empty()
            || merge.is_some_and(|prior| prior != dest)
        {
            return None;
        }
        merge = Some(dest);
        arms.push(instructions);
    }
    let merge = source.blocks.get(&merge?)?;
    let [ret] = merge.instructions.as_slice() else {
        return None;
    };
    let [returned] = ret.args.as_slice() else {
        return None;
    };
    if ret.opcode != L::Return
        || !ret.results.is_empty()
        || merge.params.as_slice() != [(*returned, integer_type.clone())]
    {
        return None;
    }
    source_fork_fits(&values)?; // Before either branch clones raw prefix terms.
    let mut results = Vec::new();
    for instructions in arms {
        let mut arm_values = values.clone();
        if source_run(
            instructions,
            integer_type,
            bits,
            comparison,
            &mut arm_values,
        )?
        .is_some()
        {
            return None;
        }
        let value = arm_values.remove(returned)?;
        if value.boolean {
            return None;
        }
        results.push(value.term);
    }
    selector.ternary(&results[0], &results[1], 1, E::ite)
}

fn machine_fork_fits(registers: &Registers, flags: &Option<ReachingFlags>) -> Option<()> {
    let nodes = registers.0.iter().flatten().try_fold(
        flags.as_ref().map_or(0, |flags| flags.nodes),
        |total, word| total.checked_add(word.term.nodes),
    )?;
    (nodes.checked_mul(2)? <= MAX_NODES).then_some(())
}

fn returned(registers: &Registers, bits: u32, comparison: bool) -> Option<Word> {
    let width = if comparison { 64 } else { bits };
    registers.read(
        &O::PReg(trust_cg_ir::regs::PReg::new(if width == 32 {
            32
        } else {
            0
        })),
        width,
        false,
    )
}

fn branch_condition(
    machine: &trust_cg_ir::MachFunction,
    branch: InstId,
    registers: &Registers,
    flags: &Option<ReachingFlags>,
) -> Option<Word> {
    let inst = machine.insts.get(branch.0 as usize)?;
    let mut condition = match (inst.opcode, inst.operands.as_slice()) {
        (M::BCond, [O::Imm(cc @ 0..=13), _]) => {
            let cc = crate::aarch64_value_decode_proofs::cset_condition_from_encoding(*cc)?;
            let flags = flags.as_ref()?;
            let nodes = flags.nodes.checked_add(16)?;
            if nodes > MAX_NODES {
                return None;
            }
            Word {
                term: Term {
                    expr: crate::nzcv::eval_condition(cc, &flags.flags),
                    nodes,
                },
                slice: flags.slice.clone(),
            }
        }
        (M::Cbz | M::Cbnz, [input @ O::PReg(_), _]) => {
            let width = operand_bits(input)?;
            let mut word = registers.read(input, width, false)?;
            word.term = word.term.unary(3, |value| {
                let zero = value.eq_expr(E::bv_const(0, width));
                if inst.opcode == M::Cbz {
                    zero
                } else {
                    zero.not_expr()
                }
            })?;
            word
        }
        _ => return None,
    };
    condition.slice.insert(branch);
    Some(condition)
}

pub(super) fn machine_result(
    machine: &trust_cg_ir::MachFunction,
    control: RawControl,
    envelope: [InstId; 3],
    mut registers: Registers,
    bits: u32,
    comparison: bool,
) -> Option<(Word, HashSet<InstId>)> {
    let mut flags = None;
    let mut credited = HashSet::new();
    match control {
        RawControl::Chain(chain) => {
            if !machine_run(
                machine,
                &chain,
                envelope,
                &mut registers,
                &mut flags,
                &mut credited,
            )? {
                return None;
            }
            Some((returned(&registers, bits, comparison)?, credited))
        }
        RawControl::Diamond {
            prefix,
            branch,
            paths,
        } => {
            if comparison
                || machine_run(
                    machine,
                    &prefix,
                    envelope,
                    &mut registers,
                    &mut flags,
                    &mut credited,
                )?
            {
                return None;
            }
            machine_fork_fits(&registers, &flags)?; // Before raw flags/register clones.
            let condition = branch_condition(machine, branch, &registers, &flags)?;
            let mut results = Vec::new();
            for path in paths {
                let mut arm_registers = registers.clone();
                let mut arm_flags = flags.clone();
                if !machine_run(
                    machine,
                    &path,
                    envelope,
                    &mut arm_registers,
                    &mut arm_flags,
                    &mut credited,
                )? {
                    return None;
                }
                results.push(returned(&arm_registers, bits, comparison)?);
            }
            let mut result = results.remove(0);
            let other = results.remove(0);
            result.term = condition
                .term
                .ternary(&result.term, &other.term, 1, E::ite)?;
            result.slice.extend(other.slice);
            result.slice.extend(condition.slice);
            credited.insert(branch);
            Some((result, credited))
        }
    }
}
