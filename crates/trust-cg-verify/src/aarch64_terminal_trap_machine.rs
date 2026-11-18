// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Terminal-trap projection of the final allocated MachFunction. Where an
//! independent instruction model exists, decode its re-derived word. This
//! verifier stage does not receive the published byte image or resolve calls.

use std::collections::HashSet;

use trust_cg_ir::{AArch64Opcode as Op, InstId, MachFunction, MachInst, MachOperand as O};

use super::{Effect, EuclideanExit, Graph, MAX_NODES, Node, Operand, Recurrence};
use crate::aarch64_control_decode::{A64ControlWord as ControlWord, decode_a64_control_word};
use crate::aarch64_instruction_word_proofs::{DecodedWord, decode_word, instruction_word};
use crate::aarch64_omitted_trap::EuclideanSource;
use crate::aarch64_omitted_trap_machine::bind_guarded_remainder;
use crate::aarch64_pair_memory::{PairMemoryBase, PairMemoryMode, check_pair_encoding};
use crate::aarch64_pair_memory_proofs::{pair_memory_intent, pair_memory_word};
use crate::aarch64_trap_expansion::{Word as TrapWord, decode as decode_trap, expansion_word};

pub(super) struct MachineLoop<'a> {
    pub(super) compare: InstId,
    pub(super) branch: InstId,
    pub(super) call: InstId,
    pub(super) symbol: &'a str,
    pub(super) recurrence: Recurrence,
    pub(super) euclidean_rows: Option<[InstId; 3]>,
}

#[derive(Clone, Copy)]
enum Flow<'a> {
    Next,
    Compare([usize; 2]),
    Branch(i64),
    FlagBranch { condition: u8, displacement: i64 },
    CompareBranch(i64),
    Call(&'a str),
    Trap,
}

struct Row<'a> {
    id: InstId,
    flow: Flow<'a>,
    effects: Vec<Effect>,
    may_fault: bool,
}

pub(super) fn bind<'a>(
    function: &'a MachFunction,
    trap: InstId,
    source_phase: Option<&EuclideanSource>,
) -> Option<MachineLoop<'a>> {
    let (rows, starts) = layout(function)?;
    let end = rows.len().checked_sub(1)?;
    let call = end.checked_sub(1)?;
    if rows[end].id != trap || !matches!(rows[end].flow, Flow::Trap) {
        return None;
    }
    let Flow::Call(symbol) = rows[call].flow else {
        return None;
    };
    if symbol == function.name.as_str() || starts.contains(&end) {
        return None;
    }
    let call_id = rows[call].id;
    let exit = *starts.iter().filter(|&&start| start <= call).max()?;
    // The exit has one straight-line prefix and one opaque normal call
    // continuation. Its terminal role says nothing about the call or memory.
    if rows[exit..call]
        .iter()
        .any(|row| !matches!(row.flow, Flow::Next))
    {
        return None;
    }

    let mut header = None;
    let mut branch = None;
    let mut incoming = vec![Vec::new(); rows.len()];
    let mut nodes = Vec::with_capacity(rows.len());
    let safe_work: Vec<_> = rows.iter().map(|row| !row.may_fault).collect();
    for (at, row) in rows.into_iter().enumerate() {
        let target = |displacement: i64| {
            let destination = at.checked_add_signed(isize::try_from(displacement).ok()?)?;
            starts.contains(&destination).then_some(destination)
        };
        let next = match row.flow {
            Flow::Next => vec![at + 1],
            Flow::Compare(roots) if header.is_none() && starts.contains(&at) => {
                header = Some((at, row.id, roots));
                vec![at + 1]
            }
            Flow::Branch(displacement) => vec![target(displacement)?],
            Flow::CompareBranch(displacement) => vec![at + 1, target(displacement)?],
            Flow::FlagBranch {
                condition: 2,
                displacement,
            } if header.is_some_and(|(compare, _, _)| compare + 1 == at)
                && target(displacement)? == exit
                && !starts.contains(&at)
                && at + 1 < exit
                && starts.contains(&(at + 1)) =>
            {
                branch = Some(row.id);
                vec![at + 1, exit]
            }
            Flow::Call(_) if at == call => vec![at + 1],
            Flow::Trap if at == end => vec![],
            _ => return None,
        };
        for &to in &next {
            incoming.get_mut(to)?.push(at);
        }
        nodes.push(Node {
            effects: row.effects,
            next,
        });
    }
    let (compare_at, compare, roots) = header?;
    let branch = branch?;
    let branch_at = compare_at + 1;
    let work = branch_at + 1;
    if compare_at == 0
        || roots[0] == roots[1]
        || nodes.get(branch_at)?.next.as_slice() != [work, exit]
        || incoming.get(branch_at)?.as_slice() != [compare_at]
        || incoming[exit].as_slice() != [branch_at]
        || (exit + 1..=end).any(|at| incoming[at].as_slice() != [at - 1])
        || !incoming[0].is_empty()
        || (1..compare_at).any(|at| incoming[at].as_slice() != [at - 1])
        || (0..compare_at).any(|at| nodes[at].next.as_slice() != [at + 1])
    {
        return None;
    }
    let graph = Graph {
        nodes,
        variables: 32,
    };
    // The comparison does not write either operand. Cut at the branch so
    // the graph applies the comparison on both entry and loop-back routes.
    let recurrence = graph.recurrence(0, branch_at, work, roots)?;
    let euclidean_rows = source_phase.and_then(|source| {
        let remainder = bind_guarded_remainder(function, source.switch, source.remainder)?;
        let (back, rows) = remainder.euclidean_loop()?;
        graph.finite_work(
            work,
            branch_at,
            EuclideanExit {
                backedge: (back.from, back.to),
                zero: back.zero,
                impossible: None,
            },
            |at| safe_work[at],
        )?;
        Some(rows)
    });
    // Layout order remains the only instruction-to-word map. No CFG metadata
    // or allocation debug snapshot participates in the counter projection.
    Some(MachineLoop {
        compare,
        branch,
        call: call_id,
        symbol,
        recurrence,
        euclidean_rows,
    })
}

fn layout(function: &MachFunction) -> Option<(Vec<Row<'_>>, HashSet<usize>)> {
    if function.block_order.first() != Some(&function.entry)
        || function.eh_metadata.has_eh_info()
        || function.stack_limit_overflow_block.is_some()
        || !function.jump_tables.is_empty()
        || !function.jump_table_address_expansions.is_empty()
    {
        return None;
    }
    let mut starts = HashSet::new();
    let mut blocks = HashSet::new();
    let mut seen = HashSet::new();
    let mut rows = Vec::new();
    for block in &function.block_order {
        if !blocks.insert(*block) || !starts.insert(rows.len()) {
            return None;
        }
        let previous = rows.len();
        for id in &function.blocks.get(block.0 as usize)?.insts {
            if seen.len() == MAX_NODES || !seen.insert(*id) {
                return None;
            }
            let inst = function.insts.get(id.0 as usize)?;
            if !inst.is_pseudo() {
                rows.push(row(*id, inst)?);
            }
        }
        if rows.len() == previous {
            return None;
        }
    }
    Some((rows, starts))
}

fn plain_word(inst: &MachInst) -> Option<u32> {
    let word = instruction_word(inst)?;
    (word.hole_mask == 0).then_some(word.word)
}

fn row(id: InstId, inst: &MachInst) -> Option<Row<'_>> {
    if !inst.implicit_defs.is_empty() && inst.opcode != Op::Bl {
        return None;
    }
    let flow = match inst.opcode {
        Op::CmpRR => {
            let DecodedWord::AddSubShifted {
                sf: 1,
                op: 1,
                s: 1,
                shift: 0,
                rm: right @ 0..=30,
                imm6: 0,
                rn: left @ 0..=30,
                rd: 31,
            } = decode_word(plain_word(inst)?)?
            else {
                return None;
            };
            Flow::Compare([left as usize, right as usize])
        }
        Op::B => {
            let ControlWord::Branch { displacement } = decode_a64_control_word(plain_word(inst)?)?
            else {
                return None;
            };
            Flow::Branch(displacement)
        }
        Op::BCond => {
            let ControlWord::ConditionalBranch {
                condition,
                displacement,
            } = decode_a64_control_word(plain_word(inst)?)?
            else {
                return None;
            };
            Flow::FlagBranch {
                condition,
                displacement,
            }
        }
        Op::Cbz | Op::Cbnz => {
            let ControlWord::CompareBranch { displacement, .. } =
                decode_a64_control_word(expansion_word(inst).ok()?)?
            else {
                return None;
            };
            Flow::CompareBranch(displacement)
        }
        Op::Bl => {
            let [O::Symbol(symbol)] = inst.operands.as_slice() else {
                return None;
            };
            let word = instruction_word(inst)?;
            if symbol.is_empty() || word.word != 0x9400_0000 || word.hole_mask != 0x03ff_ffff {
                return None;
            }
            Flow::Call(symbol)
        }
        Op::Brk => {
            if !matches!(
                decode_trap(expansion_word(inst).ok()?).ok()?,
                TrapWord::Brk { imm16: 1 }
            ) {
                return None;
            }
            Flow::Trap
        }
        _ => Flow::Next,
    };
    let effects = match flow {
        Flow::Next => writes(inst)?.into_iter().collect(),
        // Only the terminal opaque call has these clobbers. No recurrence
        // edge may depend on a callee ABI summary or reuse its return state.
        Flow::Call(_) => (0..32).map(Effect::Unknown).collect(),
        _ => vec![],
    };
    let may_fault = matches!(inst.opcode, Op::StpRI | Op::StpPreIndex);
    Some(Row {
        id,
        flow,
        effects,
        may_fault,
    })
}

// A closed set of plain scalar instructions. An opaque result affects its
// actual destination, with W and X views sharing one graph variable. Never
// infer no-write from an unfamiliar opcode or from a missing def annotation.
fn writes(inst: &MachInst) -> Option<Option<Effect>> {
    let operands = inst.operands.as_slice();
    Some(Some(match inst.opcode {
        Op::Nop | Op::AlignNop if operands.is_empty() => return Some(None),
        Op::Movz | Op::Movk => {
            let DecodedWord::MoveWide {
                sf,
                opc,
                hw,
                imm16,
                rd: dst @ 0..=30,
            } = decode_word(plain_word(inst)?)?
            else {
                return None;
            };
            let dst = dst as usize;
            let shift = hw * 16;
            let value = u64::from(imm16) << shift;
            if opc == 2 {
                Effect::Constant { dst, value }
            } else {
                let clear_upper = if sf == 0 { !u64::from(u32::MAX) } else { 0 };
                Effect::ReplaceBits {
                    dst,
                    mask: (0xffff << shift) | clear_upper,
                    value,
                }
            }
        }
        Op::MovR | Op::MOVXrr | Op::MOVWrr => {
            let DecodedWord::LogicalShifted {
                sf,
                opc: 1,
                shift: 0,
                n: 0,
                rm: src @ 0..=30,
                imm6: 0,
                rn: 31,
                rd: dst @ 0..=30,
            } = decode_word(plain_word(inst)?)?
            else {
                return None;
            };
            if sf == 1 {
                Effect::Copy {
                    dst: dst as usize,
                    src: src as usize,
                }
            } else {
                Effect::Unknown(dst as usize)
            }
        }
        Op::AddRI | Op::SubRI => {
            let DecodedWord::AddSubImm {
                sf,
                op,
                s: 0,
                sh: 0,
                imm12,
                rn,
                rd,
            } = decode_word(plain_word(inst)?)?
            else {
                return None;
            };
            if sf == 1 && op == 0 {
                Effect::Add {
                    dst: rd as usize,
                    lhs: Operand::Variable(rn as usize),
                    rhs: Operand::Immediate(u64::from(imm12)),
                }
            } else {
                Effect::Unknown(rd as usize)
            }
        }
        Op::StpRI | Op::StpPreIndex => {
            let word = pair_memory_word(&pair_memory_intent(inst)?)?;
            let pair = check_pair_encoding(inst, &word.to_le_bytes()).ok()?;
            if pair.is_load() {
                return None;
            }
            if pair.mode() == PairMemoryMode::SignedOffset {
                return Some(None);
            }
            Effect::Unknown(match pair.base() {
                PairMemoryBase::Sp => 31,
                PairMemoryBase::Register(reg) => usize::from(reg),
            })
        }
        Op::AddRR | Op::MulRR | Op::UDiv => {
            let [dst, left, right] = operands else {
                return None;
            };
            let (dst, width) = gpr(dst)?;
            if gpr(left)?.1 != width || gpr(right)?.1 != width {
                return None;
            }
            Effect::Unknown(dst)
        }
        Op::Msub => {
            let [dst, rest @ ..] = operands else {
                return None;
            };
            let (dst, width) = gpr(dst)?;
            if rest.len() != 3
                || rest
                    .iter()
                    .any(|o| !gpr(o).is_some_and(|(_, w)| w == width))
            {
                return None;
            }
            Effect::Unknown(dst)
        }
        Op::LsrRI | Op::OrrRI => {
            let [dst, src, O::Imm(value)] = operands else {
                return None;
            };
            let (dst, width) = gpr(dst)?;
            if gpr(src)?.1 != width
                || if inst.opcode == Op::LsrRI {
                    !(0..i64::from(width)).contains(value)
                } else {
                    !trust_cg_opt::const_materialize::is_logical_immediate(*value as u64, width)
                }
            {
                return None;
            }
            Effect::Unknown(dst)
        }
        _ => return None,
    }))
}

fn gpr(operand: &O) -> Option<(usize, u32)> {
    let O::PReg(register) = operand else {
        return None;
    };
    match register.encoding() {
        n @ 0..=30 => Some((usize::from(n), 64)),
        n @ 32..=62 => Some((usize::from(n - 32), 32)),
        _ => None,
    }
}
