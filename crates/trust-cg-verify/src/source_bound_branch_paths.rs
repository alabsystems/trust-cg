// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Validate actual machine edges for one conditional entry and two leaf paths.

use std::collections::HashSet;
use trust_cg_ir::{AArch64Opcode as M, BlockId, InstId, MachFunction, MachOperand};

use super::{BranchTargetDefect, ControlRefusal, FrameBindingMismatch};

pub(crate) struct Diamond {
    pub prefix: Vec<InstId>,
    pub branch: InstId,
    pub paths: [Vec<InstId>; 2],
    pub live: Vec<InstId>,
}

pub(super) fn removed_edge(inst: &trust_cg_ir::MachInst, machine: &MachFunction) -> bool {
    let [MachOperand::Block(target)] = inst.operands.as_slice() else {
        return false;
    };
    // Empty arm elimination leaves its old edge to a still-live join in the
    // instruction arena. The ownership check calls this only for instructions
    // absent from every laid-out block; they cannot execute or emit bytes.
    super::exact_instruction(inst, M::B, &inst.operands)
        && machine.block_order.contains(target)
        && machine.blocks.iter().enumerate().any(|(i, block)| {
            !machine.block_order.contains(&BlockId(i as u32))
                && block.insts.is_empty()
                && block.preds.is_empty()
                && block.succs.is_empty()
                && block.loop_depth == 0
        })
}

/// Recognize one entry conditional and its two leaf paths.
///
/// Shapes outside this skeleton are [`ControlRefusal::Shape`]. A direct branch
/// displacement that is unencodable or lands on no laid-out block start, a
/// symbolic target that is not laid out, and (when every laid-out control
/// transfer is a modeled direct branch or return) branch-derived edges that
/// differ from the recorded CFG are definite [`ControlRefusal::Branch`]
/// defects. Word offsets use the encoder's emission predicate.
pub(super) fn machine_paths(machine: &MachFunction) -> Result<Diamond, ControlRefusal> {
    machine_paths_with_virtuals(machine, false)
}

/// The same complete control/layout reconstruction before register allocation.
/// Only a CBZ/CBNZ's explicit GPR virtual input is additionally admitted; its
/// reaching definition and width are still checked by the raw body interpreter.
pub(crate) fn machine_paths_raw(machine: &MachFunction) -> Result<Diamond, ControlRefusal> {
    machine_paths_with_virtuals(machine, true)
}

fn machine_paths_with_virtuals(
    machine: &MachFunction,
    allow_virtuals: bool,
) -> Result<Diamond, ControlRefusal> {
    use ControlRefusal::Shape;
    let count = machine.blocks.len();
    if count == 0
        || count > 16
        || machine.insts.len() > 256
        || machine.entry != BlockId(0)
        || machine.block_order.first() != Some(&machine.entry)
    {
        return Err(Shape);
    }
    let mut active = vec![false; count];
    let mut seen = vec![false; machine.insts.len()];
    let mut block_words = vec![0i64; count];
    let mut inst_words = vec![0i64; machine.insts.len()];
    let mut following = vec![None; count];
    let mut live = Vec::new();
    let mut word = 0;
    for (position, id) in machine.block_order.iter().enumerate() {
        let index = id.0 as usize;
        if std::mem::replace(active.get_mut(index).ok_or(Shape)?, true) {
            return Err(Shape);
        }
        block_words[index] = word;
        following[index] = machine.block_order.get(position + 1).copied();
        for id in &machine.blocks[index].insts {
            let index = id.0 as usize;
            if std::mem::replace(seen.get_mut(index).ok_or(Shape)?, true) {
                return Err(Shape);
            }
            inst_words[index] = word;
            // The encoder emits exactly one word for every non-pseudo
            // instruction, including an EMPTY-flags NOP, and none for a
            // pseudo. The body checks still reject unsupported pseudos.
            word += i64::from(!machine.insts.get(index).ok_or(Shape)?.is_pseudo());
            live.push(*id);
        }
    }
    let branch_defect = |block: usize, id: InstId, defect| {
        ControlRefusal::Branch(FrameBindingMismatch::BranchTarget {
            block: BlockId(block as u32),
            instruction: Some(id),
            defect,
        })
    };
    let target = |block: usize,
                  id: InstId,
                  operand: &MachOperand,
                  bits: u32|
     -> Result<BlockId, ControlRefusal> {
        let result = match operand {
            MachOperand::Block(id) => *id,
            MachOperand::Imm(offset) => {
                if !(-(1i64 << (bits - 1))..(1i64 << (bits - 1))).contains(offset) {
                    return Err(branch_defect(
                        block,
                        id,
                        BranchTargetDefect::DisplacementOutOfRange {
                            displacement: *offset,
                            bits,
                        },
                    ));
                }
                let destination = inst_words[id.0 as usize]
                    .checked_add(*offset)
                    .ok_or(Shape)?;
                let mut candidates = block_words
                    .iter()
                    .enumerate()
                    .filter(|(i, word)| active[*i] && **word == destination);
                let Some((index, _)) = candidates.next() else {
                    return Err(branch_defect(
                        block,
                        id,
                        BranchTargetDefect::NoBlockStart {
                            displacement: *offset,
                        },
                    ));
                };
                // Empty laid-out blocks share a start word; the intended one
                // is not determined by the layout.
                if candidates.next().is_some() {
                    return Err(Shape);
                }
                BlockId(index as u32)
            }
            _ => return Err(Shape),
        };
        if !active.get(result.0 as usize).copied().ok_or(Shape)? {
            return Err(branch_defect(
                block,
                id,
                BranchTargetDefect::TargetNotLaidOut { target: result },
            ));
        }
        Ok(result)
    };
    let mut successors = vec![Vec::new(); count];
    let mut bodies = vec![Vec::new(); count];
    let mut conditional = None;
    let mut direct_targets = vec![Vec::new(); count];
    for (index, block) in machine.blocks.iter().enumerate() {
        if block.loop_depth != 0 {
            return Err(Shape);
        }
        if !active[index] {
            if !block.insts.is_empty() || !block.preds.is_empty() || !block.succs.is_empty() {
                return Err(Shape);
            }
            continue;
        }
        let mut body = block.insts.as_slice();
        let mut fallthrough = following[index];
        if let Some(id) = body.last().copied() {
            let inst = &machine.insts[id.0 as usize];
            if inst.opcode == M::B {
                let [operand] = inst.operands.as_slice() else {
                    return Err(Shape);
                };
                if !super::exact_instruction(inst, M::B, &inst.operands) {
                    return Err(Shape);
                }
                let resolved = target(index, id, operand, 26)?;
                direct_targets[index].push((id, resolved));
                fallthrough = Some(resolved);
                body = &body[..body.len() - 1];
            } else if inst.opcode == M::Ret {
                fallthrough = None;
            }
        }
        if let Some(id) = body.last().copied() {
            let inst = &machine.insts[id.0 as usize];
            if matches!(inst.opcode, M::BCond | M::Cbz | M::Cbnz) {
                if index != 0
                    || conditional.is_some()
                    || !super::exact_instruction(inst, inst.opcode, &inst.operands)
                {
                    return Err(Shape);
                }
                let [condition, operand] = inst.operands.as_slice() else {
                    return Err(Shape);
                };
                match (inst.opcode, condition) {
                    (M::BCond, MachOperand::Imm(0..=13)) => {}
                    (M::Cbz | M::Cbnz, MachOperand::PReg(reg)) if matches!(reg.encoding(), 0..=17 | 32..=49) =>
                        {}
                    (M::Cbz | M::Cbnz, MachOperand::VReg(reg))
                        if allow_virtuals
                            && reg.id < machine.next_vreg
                            && matches!(
                                reg.class,
                                trust_cg_ir::regs::RegClass::Gpr32
                                    | trust_cg_ir::regs::RegClass::Gpr64
                            ) => {}
                    _ => return Err(Shape),
                }
                let taken = target(index, id, operand, 19)?;
                direct_targets[index].push((id, taken));
                let not_taken = fallthrough.ok_or(Shape)?;
                if taken == not_taken {
                    return Err(Shape);
                }
                successors[index] = vec![taken, not_taken];
                conditional = Some(id);
                body = &body[..body.len() - 1];
            } else {
                successors[index] = fallthrough.into_iter().collect();
            }
        } else {
            successors[index] = fallthrough.into_iter().collect();
        }
        bodies[index] = body.to_vec();
    }
    let same_edges = |actual: &[BlockId], expected: &[BlockId]| {
        actual.len() == expected.len()
            && actual.iter().collect::<HashSet<_>>().len() == actual.len()
            && actual.iter().all(|id| expected.contains(id))
    };
    // Branch-derived edges are complete only when every laid-out control
    // transfer is one this walker modeled. Otherwise (indirect branches,
    // test-bit branches, calls, traps) disagreement is merely unsupported.
    let modeled_control = live.iter().all(|id| {
        let inst = &machine.insts[id.0 as usize];
        matches!(inst.opcode, M::B | M::BCond | M::Cbz | M::Cbnz | M::Ret)
            || !super::linear::transfers_control(inst)
    });
    let succ_disagreement = machine
        .blocks
        .iter()
        .enumerate()
        .find(|(i, block)| !same_edges(&block.succs, &successors[*i]));
    let pred_disagreement = || {
        machine.blocks.iter().enumerate().find(|(i, block)| {
            let predecessors: Vec<_> = successors
                .iter()
                .enumerate()
                .filter(|(_, edges)| edges.contains(&BlockId(*i as u32)))
                .map(|(i, _)| BlockId(i as u32))
                .collect();
            !same_edges(&block.preds, &predecessors)
        })
    };
    if let Some((i, block)) = succ_disagreement.or_else(pred_disagreement) {
        if !modeled_control || conditional.is_none() {
            return Err(Shape);
        }
        // Blame the direct branch whose own target is absent from the
        // recorded successors, when there is one.
        let instruction = direct_targets[i]
            .iter()
            .find(|(_, target)| !block.succs.contains(target))
            .map(|(id, _)| *id);
        return Err(ControlRefusal::Branch(FrameBindingMismatch::BranchTarget {
            block: BlockId(i as u32),
            instruction,
            defect: BranchTargetDefect::DisagreesWithCfg,
        }));
    }
    let branch = conditional.ok_or(Shape)?;
    let [taken, not_taken] = successors[0].as_slice() else {
        return Err(Shape);
    };
    let mut covered = HashSet::from([machine.entry]);
    let mut paths = Vec::new();
    for start in [*taken, *not_taken] {
        let mut visited = HashSet::from([machine.entry]);
        let mut current = start;
        let mut instructions = Vec::new();
        loop {
            if !visited.insert(current) {
                return Err(Shape);
            }
            covered.insert(current);
            instructions.extend_from_slice(&bodies[current.0 as usize]);
            match successors[current.0 as usize].as_slice() {
                [next] => current = *next,
                [] => {
                    let last = instructions.last().ok_or(Shape)?;
                    if machine.insts.get(last.0 as usize).ok_or(Shape)?.opcode != M::Ret {
                        return Err(Shape);
                    }
                    break;
                }
                _ => return Err(Shape),
            }
        }
        paths.push(instructions);
    }
    if machine.block_order.iter().any(|id| !covered.contains(id)) {
        return Err(Shape);
    }
    Ok(Diamond {
        prefix: bodies[0].clone(),
        branch,
        paths: paths.try_into().map_err(|_| Shape)?,
        live,
    })
}
