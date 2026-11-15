// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Independently follow bounded unconditional source and machine block chains.
//! These views are private inputs to the complete scalar-body comparison;
//! neither normalization grants proof authority or replaces the original input.

use trust_cg_ir::{AArch64Opcode as M, BlockId, InstId, MachFunction, MachOperand};

use super::{BranchTargetDefect, ControlRefusal, FrameBindingMismatch};
use trust_cg_lower::Function;

/// The ISA-neutral flattened chain view (`crate::source_bound_source`). The
/// frame owner and its diagnostic checkers keep this name; the logic moved
/// unchanged so the x86-64 body owner can share it.
pub(super) fn source_view(source: &Function) -> Option<Function> {
    crate::source_bound_source::linear_chain_view(source)
}

pub(crate) struct MachineChain {
    pub instructions: Vec<InstId>,
    pub live: Vec<InstId>,
}

/// Follow the complete machine chain in execution order.
///
/// Any shape outside a bounded unconditional chain is [`ControlRefusal::Shape`]
/// and makes no claim. A recognized direct `B` in a block with no other
/// control transfer is judged against the final layout: a displacement that
/// is unencodable or lands on no laid-out block start, a symbolic target that
/// is not laid out, or a resolved target other than the block's single
/// recorded successor is a definite [`ControlRefusal::Branch`] defect.
pub(crate) fn machine_chain(machine: &MachFunction) -> Result<MachineChain, ControlRefusal> {
    use ControlRefusal::Shape;
    let count = machine.blocks.len();
    if count == 0
        || count > 16
        || machine.insts.len() > 256
        || machine.entry != BlockId(0)
        || machine.block_order.is_empty()
        || machine.block_order.len() > count
        || machine.block_order.first() != Some(&machine.entry)
    {
        return Err(Shape);
    }
    let mut layout_seen = vec![false; count];
    let mut inst_seen = vec![false; machine.insts.len()];
    let mut block_words = vec![0i64; count];
    let mut instruction_words = vec![0i64; machine.insts.len()];
    let mut following = vec![None; count];
    let mut word = 0;
    for (position, id) in machine.block_order.iter().enumerate() {
        let index = id.0 as usize;
        if std::mem::replace(layout_seen.get_mut(index).ok_or(Shape)?, true) {
            return Err(Shape);
        }
        block_words[index] = word;
        following[index] = machine.block_order.get(position + 1).copied();
        for instruction in &machine.blocks[index].insts {
            let i = instruction.0 as usize;
            if std::mem::replace(inst_seen.get_mut(i).ok_or(Shape)?, true) {
                return Err(Shape);
            }
            instruction_words[i] = word;
            // Match the encoder's emission predicate, not just the opcode:
            // an EMPTY-flags Nop emits one hardware word, while IS_PSEUDO
            // Nop emits none. Both are inert, but resolved branch offsets
            // must distinguish them. The later complete body check still
            // rejects unsupported pseudos, opcodes and invalid flags.
            word += i64::from(!machine.insts.get(i).ok_or(Shape)?.is_pseudo());
        }
    }
    // CFG merging retains empty arena slots outside the actual layout. They
    // contribute no code or edges and cannot be used as execution targets.
    if machine
        .blocks
        .iter()
        .zip(&layout_seen)
        .any(|(block, laid_out)| {
            !laid_out
                && (!block.insts.is_empty()
                    || !block.preds.is_empty()
                    || !block.succs.is_empty()
                    || block.loop_depth != 0)
        })
    {
        return Err(Shape);
    }
    let mut visited = vec![false; count];
    let mut current = machine.entry;
    let mut previous = None;
    let mut instructions = Vec::new();
    let mut live = Vec::new();
    loop {
        let index = current.0 as usize;
        if std::mem::replace(visited.get_mut(index).ok_or(Shape)?, true) {
            return Err(Shape);
        }
        let block = machine.blocks.get(index).ok_or(Shape)?;
        if block.preds != previous.into_iter().collect::<Vec<_>>() || block.loop_depth != 0 {
            return Err(Shape);
        }
        live.extend_from_slice(&block.insts);
        let last = block.insts.last().copied();
        let next = match last.map(|id| (id, &machine.insts[id.0 as usize])) {
            Some((id, inst)) if inst.opcode == M::B => {
                let [operand] = inst.operands.as_slice() else {
                    return Err(Shape);
                };
                if !super::exact_instruction(inst, M::B, &inst.operands) {
                    return Err(Shape);
                }
                // Only a block whose sole control transfer is this B is a
                // chain block; others belong to the diamond walker.
                let sole_transfer = block.insts[..block.insts.len() - 1]
                    .iter()
                    .all(|id| !transfers_control(&machine.insts[id.0 as usize]));
                let defect = |defect| {
                    if sole_transfer {
                        ControlRefusal::Branch(FrameBindingMismatch::BranchTarget {
                            block: current,
                            instruction: Some(id),
                            defect,
                        })
                    } else {
                        Shape
                    }
                };
                let target = match operand {
                    MachOperand::Block(target) => *target,
                    MachOperand::Imm(displacement) => {
                        if !(-(1 << 25)..(1 << 25)).contains(displacement) {
                            return Err(defect(BranchTargetDefect::DisplacementOutOfRange {
                                displacement: *displacement,
                                bits: 26,
                            }));
                        }
                        let destination = instruction_words[id.0 as usize]
                            .checked_add(*displacement)
                            .ok_or(Shape)?;
                        let mut matches = block_words
                            .iter()
                            .enumerate()
                            .filter(|(index, word)| layout_seen[*index] && **word == destination);
                        let Some((target, _)) = matches.next() else {
                            return Err(defect(BranchTargetDefect::NoBlockStart {
                                displacement: *displacement,
                            }));
                        };
                        // Empty laid-out blocks share a start word; the
                        // intended one is not determined by the layout.
                        if matches.next().is_some() {
                            return Err(Shape);
                        }
                        BlockId(target as u32)
                    }
                    _ => return Err(Shape),
                };
                if !layout_seen.get(target.0 as usize).copied().ok_or(Shape)? {
                    return Err(defect(BranchTargetDefect::TargetNotLaidOut { target }));
                }
                if let [recorded] = block.succs.as_slice()
                    && *recorded != target
                {
                    return Err(defect(BranchTargetDefect::DisagreesWithSuccessor {
                        target,
                        recorded: *recorded,
                    }));
                }
                instructions.extend_from_slice(&block.insts[..block.insts.len() - 1]);
                Some(target)
            }
            Some((_, inst)) if inst.opcode == M::Ret => {
                instructions.extend_from_slice(&block.insts);
                None
            }
            _ => {
                instructions.extend_from_slice(&block.insts);
                Some(following[index].ok_or(Shape)?)
            }
        };
        if block.succs != next.into_iter().collect::<Vec<_>>() {
            return Err(Shape);
        }
        match next {
            Some(target) => {
                previous = Some(current);
                current = target;
            }
            None => break,
        }
    }
    if visited != layout_seen {
        return Err(Shape);
    }
    Ok(MachineChain { instructions, live })
}

/// Whether `inst` can transfer control. Direct and indirect branches, calls,
/// returns and traps all qualify; only straight-line computation does not.
pub(super) fn transfers_control(inst: &trust_cg_ir::MachInst) -> bool {
    inst.is_branch()
        || inst.is_terminator()
        || inst.is_return()
        || matches!(
            inst.opcode,
            M::B | M::BCond | M::Cbz | M::Cbnz | M::Tbz | M::Tbnz | M::Br | M::Ret
        )
}

pub(super) fn inactive_branch_tombstone(
    inst: &trust_cg_ir::MachInst,
    machine: &MachFunction,
) -> bool {
    let [MachOperand::Block(target)] = inst.operands.as_slice() else {
        return false;
    };
    super::exact_instruction(inst, M::B, &inst.operands)
        && !machine.block_order.contains(target)
        && machine.blocks.get(target.0 as usize).is_some_and(|block| {
            block.insts.is_empty()
                && block.preds.is_empty()
                && block.succs.is_empty()
                && block.loop_depth == 0
        })
}
