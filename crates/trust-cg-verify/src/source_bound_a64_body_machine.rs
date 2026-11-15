// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! The machine side of the AArch64 whole-body theorem: the final allocated,
//! frameless `MachFunction`, walked as the words the encoder emits for it.
//!
//! **Control.** The laid-out blocks, their word offsets (one word per
//! non-pseudo instruction, as the encoder emits) and every direct transfer
//! (`B`, `B.cond`, `CBZ`, `CBNZ`, `TBZ`, `TBNZ`: a `Block` operand or a word
//! displacement resolved against the layout, as `source_bound_branch_paths`
//! resolves it) give the edges; a block without a final transfer falls
//! through to the next laid-out block, and `RET` ends a path. The edges must
//! equal the recorded successors and predecessors and form an acyclic graph
//! in which every laid-out block is reachable. A loop is refused by name.
//!
//! **State.** X0-X30 (the W view is the low half of its X register; a W
//! write zeroes the upper half) and NZCV. At entry, the register of parameter
//! `i` holds the caller's 64-bit value (for a `B1`, with bits 1..7 cleared:
//! the AAPCS64 0/1 byte); every other register and the flags hold the
//! caller's arbitrary value, a free input. Only X0-X17 may be written; a
//! write to X18-X30 (the platform register, callee-saved registers, FP, LR)
//! is a mismatch, and any SP operand is outside the owner.
//!
//! **Rows.** Each admitted row's semantics is the architectural meaning of
//! the word the encoder emits for it (`trust-cg-codegen` `aarch64/encode.rs`,
//! Arm ARM DDI 0487): the operation width is the encoder's `sf` (the
//! destination's register class, or the opcode's for `UXTB`/`SXTB`/`MOVW`/
//! `MOVX`-style forms), register operands are read at that width, shifts by
//! register take their amount modulo the width, `UBFM`/`SBFM` follow
//! `DecodeBitMasks`, `CMP`/`TST` set NZCV as `SUBS`/`ANDS`, and every
//! condition code is evaluated from NZCV by its architectural table (no
//! LIR-to-condition mapping participates). Blocks merge by their taken edge:
//! a register or flag that differs between predecessors takes the value of
//! the one edge taken, so the machine is one gated DAG, like the source.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::regs::SpecialReg;
use trust_cg_ir::{AArch64Opcode as M, BlockId, InstFlags, InstId, MachFunction, MachInst};
use trust_cg_ir::{MachOperand as O, function::Type as MType};

use super::source::Admitted;
use super::{
    A64BodyMismatch, A64BodyRefusal, A64BodyUnsupported, Defs, Ty, and_bit, bool_bv, is_one,
    mismatch, unsupported,
};
use crate::smt::SmtExpr as E;
use crate::source_bound_frame::BranchTargetDefect;

#[cfg(test)]
#[path = "source_bound_a64_body_machine_resource_tests.rs"]
mod resource_tests;

/// Most laid-out blocks and instructions a machine body may have.
const MAX_MACHINE_BLOCKS: usize = 16;
const MAX_MACHINE_INSTRUCTIONS: usize = 256;

/// The AArch64 opcodes a bound body may contain, by name (the census binds
/// this list to [`admitted_row`]).
pub const ADMITTED_MACHINE_OPCODES: &[&str] = &[
    "AddRR",
    "SubRR",
    "AddRI",
    "AddRIShift12",
    "SubRI",
    "Neg",
    "AddRRShift",
    "SubRRShift",
    "AddRRShiftLsr",
    "EorRRLsl",
    "EorRRLsr",
    "EorRRShift",
    "AndRR",
    "OrrRR",
    "EorRR",
    "BicRR",
    "OrnRR",
    "AndRI",
    "OrrRI",
    "EorRI",
    "LslRR",
    "LsrRR",
    "AsrRR",
    "LslRI",
    "LsrRI",
    "AsrRI",
    "Ubfm",
    "Sbfm",
    "Uxtb",
    "Uxth",
    "Uxtw",
    "Sxtb",
    "Sxth",
    "Sxtw",
    "CmpRR",
    "CmpRI",
    "Tst",
    "CSet",
    "Csel",
    "Csinc",
    "Csinv",
    "Csneg",
    "Movz",
    "Movn",
    "Movk",
    "MovI",
    "MovR",
    "MOVWrr",
    "MOVXrr",
    "B",
    "BCond",
    "Cbz",
    "Cbnz",
    "Tbz",
    "Tbnz",
    "Ret",
    "Nop",
    "AlignNop",
];

/// Whether a bound body may contain `opcode` (its operands are checked by the
/// walk).
pub(crate) fn admitted_row(opcode: M) -> bool {
    use M::*;
    matches!(
        opcode,
        AddRR
            | SubRR
            | AddRI
            | AddRIShift12
            | SubRI
            | Neg
            | AddRRShift
            | SubRRShift
            | AddRRShiftLsr
            | EorRRLsl
            | EorRRLsr
            | EorRRShift
            | AndRR
            | OrrRR
            | EorRR
            | BicRR
            | OrnRR
            | AndRI
            | OrrRI
            | EorRI
            | LslRR
            | LsrRR
            | AsrRR
            | LslRI
            | LsrRI
            | AsrRI
            | Ubfm
            | Sbfm
            | Uxtb
            | Uxth
            | Uxtw
            | Sxtb
            | Sxth
            | Sxtw
            | CmpRR
            | CmpRI
            | Tst
            | CSet
            | Csel
            | Csinc
            | Csinv
            | Csneg
            | Movz
            | Movn
            | Movk
            | MovI
            | MovR
            | MOVWrr
            | MOVXrr
            | B
            | BCond
            | Cbz
            | Cbnz
            | Tbz
            | Tbnz
            | Ret
            | Nop
            | AlignNop
    )
}

/// Register copies and wide-move constants. In the returned value's slice the
/// replayed theorem credits them (OD-35 route C;
/// `reports/2026-09-27-e02-copy-constant-credit`). A live materialization
/// can admit a scalar body; numbered-register copies alone cannot.
pub(crate) fn copy_or_constant(opcode: M) -> bool {
    matches!(
        opcode,
        M::MovR | M::MOVWrr | M::MOVXrr | M::Movz | M::Movn | M::Movk | M::MovI
    )
}

/// A row whose encoded meaning materializes a literal or zero register.
/// Called only after the machine walk has validated operand shapes/widths.
/// MOVK may retain other input bits; the full body theorem must still prove
/// every returned bit, including those not supplied by its immediate.
pub(super) fn constant_materialization(inst: &MachInst) -> bool {
    matches!(inst.opcode, M::Movz | M::Movn | M::Movk | M::MovI)
        || (matches!(inst.opcode, M::MovR | M::MOVWrr | M::MOVXrr)
            && inst
                .operands
                .get(1)
                .and_then(gpr)
                .is_some_and(|reg| matches!(reg, Gpr::Zero { .. })))
}

/// The machine side of the theorem.
pub(super) struct MachineTheorem {
    /// The observed return bits (64 for `I64`, the W view otherwise).
    pub(super) result: E,
    /// Every laid-out row, in layout order.
    pub(super) rows: Vec<InstId>,
}

fn row_refusal(inst: InstId, detail: impl Into<String>) -> A64BodyRefusal {
    unsupported(A64BodyUnsupported::MachineRow {
        inst,
        detail: detail.into(),
    })
}

fn control(detail: impl Into<String>) -> A64BodyRefusal {
    unsupported(A64BodyUnsupported::MachineControl(detail.into()))
}

/// A general-purpose register operand as the encoder reads it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Gpr {
    /// X/W register number 0..=30, with the width its spelling names.
    Reg { number: u8, width: u32 },
    /// XZR (64) or WZR (32).
    Zero { width: u32 },
}

impl Gpr {
    fn width(self) -> u32 {
        match self {
            Gpr::Reg { width, .. } | Gpr::Zero { width } => width,
        }
    }
}

/// A scalar GPR or zero register; SP/WSP and every other bank are refused.
fn gpr(operand: &O) -> Option<Gpr> {
    match operand {
        O::PReg(reg) => match reg.encoding() {
            n @ 0..=30 => Some(Gpr::Reg {
                number: n as u8,
                width: 64,
            }),
            n @ 32..=62 => Some(Gpr::Reg {
                number: (n - 32) as u8,
                width: 32,
            }),
            160 => Some(Gpr::Zero { width: 64 }),
            161 => Some(Gpr::Zero { width: 32 }),
            _ => None,
        },
        O::Special(SpecialReg::XZR) => Some(Gpr::Zero { width: 64 }),
        O::Special(SpecialReg::WZR) => Some(Gpr::Zero { width: 32 }),
        _ => None,
    }
}

fn mask(width: u32) -> u64 {
    crate::smt::mask(u64::MAX, width)
}

fn ones(count: u32, width: u32) -> u64 {
    if count >= 64 {
        mask(width)
    } else {
        ((1u64 << count) - 1) & mask(width)
    }
}

fn rotate_right(value: u64, amount: u32, width: u32) -> u64 {
    let value = value & mask(width);
    if amount == 0 {
        value
    } else {
        ((value >> amount) | (value << (width - amount))) & mask(width)
    }
}

/// `ROR(term, amount)` at `width` by constant shifts.
fn ror_term(term: E, amount: u32, width: u32) -> E {
    if amount == 0 {
        return term;
    }
    term.clone()
        .bvlshr(E::bv_const(u64::from(amount), width))
        .bvor(term.bvshl(E::bv_const(u64::from(width - amount), width)))
}

/// `UBFM`/`SBFM Rd, Rn, #r, #s` (Arm ARM `DecodeBitMasks` with
/// `immediate = FALSE`, `esize` the operation width).
pub(super) fn bitfield(source: E, r: u32, s: u32, signed: bool, width: u32) -> E {
    let d = s.wrapping_sub(r) & (width - 1);
    let wmask = rotate_right(ones(s + 1, width), r, width);
    let tmask = ones(d + 1, width);
    let bottom = ror_term(source.clone(), r, width).bvand(E::bv_const(wmask, width));
    let top = if signed {
        E::ite(
            is_one(source.extract(s, s)),
            E::bv_const(mask(width), width),
            E::bv_const(0, width),
        )
    } else {
        E::bv_const(0, width)
    };
    top.bvand(E::bv_const(!tmask & mask(width), width))
        .bvor(bottom.bvand(E::bv_const(tmask, width)))
}

/// The four NZCV flags, one bit each.
#[derive(Clone, Debug, PartialEq)]
pub(super) struct Flags {
    pub(super) n: E,
    pub(super) z: E,
    pub(super) c: E,
    pub(super) v: E,
}

/// The architectural condition `cc` (0..=15) over NZCV.
pub(super) fn condition(flags: &Flags, cc: u8) -> E {
    let n = is_one(flags.n.clone());
    let z = is_one(flags.z.clone());
    let c = is_one(flags.c.clone());
    let v = is_one(flags.v.clone());
    let ge = n.clone().eq_expr(v.clone());
    let hi = c.clone().and_expr(z.clone().not_expr());
    let gt = z.clone().not_expr().and_expr(ge.clone());
    match cc {
        0 => z,
        1 => z.not_expr(),
        2 => c,
        3 => c.not_expr(),
        4 => n,
        5 => n.not_expr(),
        6 => v,
        7 => v.not_expr(),
        8 => hi,
        9 => hi.not_expr(),
        10 => ge,
        11 => ge.not_expr(),
        12 => gt,
        13 => gt.not_expr(),
        _ => E::bool_const(true),
    }
}

/// Register and flag state at one program point.
#[derive(Clone)]
struct State {
    regs: Vec<E>,
    flags: Flags,
}

/// The fixed transfer at the end of one laid-out block.
#[derive(Clone)]
enum Exit {
    /// Fall through or `B` (the row, when there is one) to one block.
    Goto {
        target: BlockId,
        row: Option<InstId>,
    },
    /// A conditional transfer (row `branch`) to `taken`, else to `other`
    /// (through the `B` row `jump`, when there is one).
    Branch {
        branch: InstId,
        taken: BlockId,
        other: BlockId,
        jump: Option<InstId>,
    },
    /// `RET`.
    Return,
}

struct Walker<'m> {
    machine: &'m MachFunction,
    observe: Ty,
}

impl Walker<'_> {
    fn inst(&self, id: InstId) -> &MachInst {
        &self.machine.insts[id.0 as usize]
    }
}

/// Check the machine function's signature and metadata against the source.
fn check_function(machine: &MachFunction, admitted: &Admitted<'_>) -> Result<(), A64BodyRefusal> {
    let machine_type = |ty: Ty| match ty {
        Ty::I8 => MType::I8,
        Ty::I16 => MType::I16,
        Ty::I32 => MType::I32,
        Ty::I64 => MType::I64,
        Ty::B1 => MType::B1,
    };
    if machine.signature.params.len() != admitted.params.len()
        || machine
            .signature
            .params
            .iter()
            .zip(&admitted.params)
            .any(|(machine, source)| *machine != machine_type(*source))
        || machine.signature.returns.as_slice() != [machine_type(admitted.returns)]
    {
        return Err(mismatch(A64BodyMismatch::Signature));
    }
    if !machine.stack_slots.is_empty()
        || machine.eh_metadata.has_eh_info()
        || machine.stack_protector != trust_cg_ir::function::StackProtectorMode::None
        || machine.stack_protector_slot.is_some()
        || machine.stack_limit.is_some()
        || !machine.jump_tables.is_empty()
    {
        return Err(unsupported(A64BodyUnsupported::MachineFunction(
            "stack slots, EH, stack protection, a stack-limit check or jump tables".into(),
        )));
    }
    Ok(())
}

/// Encode the machine side. `entry` holds the 64-bit entry input of each
/// parameter register (its name is shared with the source side).
pub(super) fn encode(
    machine: &MachFunction,
    admitted: &Admitted<'_>,
    defs: &mut Defs,
    entry: &[E],
) -> Result<MachineTheorem, A64BodyRefusal> {
    check_function(machine, admitted)?;
    let walker = Walker {
        machine,
        observe: admitted.returns,
    };
    let count = machine.block_order.len();
    if machine.blocks.is_empty()
        || machine.block_order.is_empty()
        || machine.block_order.len() > MAX_MACHINE_BLOCKS
        || machine.insts.len() > 4 * MAX_MACHINE_INSTRUCTIONS
        || machine.entry != BlockId(0)
        || machine.block_order.first() != Some(&machine.entry)
    {
        return Err(control(format!(
            "{} laid-out blocks from entry {:?} (the owner admits 1 to {MAX_MACHINE_BLOCKS} \
             starting at block 0)",
            machine.block_order.len(),
            machine.entry
        )));
    }
    // Execution scratch uses the bounded live layout, NEVER the append-only
    // block arena. Empty retired slots remain outside execution; original IDs
    // still identify every operand, recorded edge and diagnostic. The complete
    // arena is scanned below for hidden rows/edges, with honest O(arena) work.
    let mut laid_out = HashMap::with_capacity(count);
    let mut seen = vec![false; machine.insts.len()];
    let mut block_words = vec![0i64; count];
    let mut row_words = vec![0i64; machine.insts.len()];
    let mut following: Vec<Option<BlockId>> = vec![None; count];
    let mut rows = Vec::new();
    let mut word = 0i64;
    for (position, block) in machine.block_order.iter().enumerate() {
        let arena_index = block.0 as usize;
        let Some(body) = machine.blocks.get(arena_index) else {
            return Err(control(
                "the block order names a block twice or out of range",
            ));
        };
        if laid_out.insert(arena_index, position).is_some() {
            return Err(control(
                "the block order names a block twice or out of range",
            ));
        }
        block_words[position] = word;
        following[position] = machine.block_order.get(position + 1).copied();
        for id in &body.insts {
            let i = id.0 as usize;
            if i >= machine.insts.len() || std::mem::replace(&mut seen[i], true) {
                return Err(control("a row is laid out twice or out of range"));
            }
            row_words[i] = word;
            word += i64::from(!machine.insts[i].is_pseudo());
            rows.push(*id);
        }
    }
    if rows.len() > MAX_MACHINE_INSTRUCTIONS {
        return Err(control(format!(
            "{} laid-out rows (the owner admits at most {MAX_MACHINE_INSTRUCTIONS})",
            rows.len()
        )));
    }
    for (index, block) in machine.blocks.iter().enumerate() {
        let live = laid_out.contains_key(&index);
        if !live && (!block.insts.is_empty() || !block.preds.is_empty() || !block.succs.is_empty())
        {
            return Err(control(format!(
                "block {index} holds rows or edges but is not laid out"
            )));
        }
        if live && block.loop_depth != 0 {
            return Err(control(format!(
                "block {index} is recorded inside a loop; loops stay outside the body owner"
            )));
        }
    }
    // Resolve a direct transfer's operand to a laid-out block.
    let branch_defect = |block: usize, id: InstId, defect| {
        mismatch(A64BodyMismatch::BranchTarget {
            block: BlockId(block as u32),
            instruction: Some(id),
            defect,
        })
    };
    let target =
        |block: usize, id: InstId, operand: &O, bits: u32| -> Result<BlockId, A64BodyRefusal> {
            let resolved = match operand {
                O::Block(target) => *target,
                O::Imm(offset) => {
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
                    let destination = row_words[id.0 as usize]
                        .checked_add(*offset)
                        .ok_or_else(|| control("branch displacement overflows"))?;
                    let mut candidates = block_words
                        .iter()
                        .enumerate()
                        .filter(|(_, word)| **word == destination);
                    let Some((index, _)) = candidates.next() else {
                        return Err(branch_defect(
                            block,
                            id,
                            BranchTargetDefect::NoBlockStart {
                                displacement: *offset,
                            },
                        ));
                    };
                    // Empty laid-out blocks share a start word: the intended one
                    // is not determined by the layout.
                    if candidates.next().is_some() {
                        return Err(control(
                            "a branch lands on a word several laid-out blocks start at",
                        ));
                    }
                    machine.block_order[index]
                }
                _ => {
                    return Err(row_refusal(
                        id,
                        "branch target is not a block or displacement",
                    ));
                }
            };
            if !laid_out.contains_key(&(resolved.0 as usize)) {
                return Err(branch_defect(
                    block,
                    id,
                    BranchTargetDefect::TargetNotLaidOut { target: resolved },
                ));
            }
            Ok(resolved)
        };
    // Each laid-out block: its straight-line rows and its exit.
    let mut bodies: Vec<Vec<InstId>> = vec![Vec::new(); count];
    let mut exits: Vec<Option<Exit>> = vec![None; count];
    for (index, block) in machine.block_order.iter().enumerate() {
        let arena_index = block.0 as usize;
        let insts = &machine.blocks[arena_index].insts;
        // Every row is admitted, exact in flags and free of implicit
        // definitions before its semantics is read.
        for id in insts {
            let inst = walker.inst(*id);
            if !admitted_row(inst.opcode) {
                return Err(row_refusal(
                    *id,
                    format!("{:?} is outside the body owner", inst.opcode),
                ));
            }
            let flags_exact = inst.flags == inst.opcode.default_flags()
                || (matches!(inst.opcode, M::Nop | M::AlignNop)
                    && matches!(inst.flags, InstFlags::EMPTY | InstFlags::IS_PSEUDO));
            if !flags_exact || !inst.implicit_defs.is_empty() {
                return Err(row_refusal(
                    *id,
                    format!(
                        "{:?} carries nondefault flags or implicit definitions",
                        inst.opcode
                    ),
                ));
            }
        }
        let mut body: &[InstId] = insts;
        let mut fallthrough = following[index];
        let mut jump = None;
        if let Some(id) = body.last().copied() {
            let inst = walker.inst(id);
            if inst.opcode == M::B {
                let [operand] = inst.operands.as_slice() else {
                    return Err(row_refusal(id, "B takes one target"));
                };
                fallthrough = Some(target(arena_index, id, operand, 26)?);
                jump = Some(id);
                body = &body[..body.len() - 1];
            } else if inst.opcode == M::Ret {
                if inst.operands.as_slice() != [O::PReg(trust_cg_ir::regs::X30)] {
                    return Err(row_refusal(id, "RET does not return through X30"));
                }
                exits[index] = Some(Exit::Return);
                body = &body[..body.len() - 1];
            }
        }
        let conditional = body.last().copied().filter(|id| {
            exits[index].is_none()
                && matches!(
                    walker.inst(*id).opcode,
                    M::BCond | M::Cbz | M::Cbnz | M::Tbz | M::Tbnz
                )
        });
        if let Some(id) = conditional {
            let inst = walker.inst(id);
            let (operand, bits) = match inst.opcode {
                M::BCond => match inst.operands.as_slice() {
                    [O::Imm(0..=13), target] => (target, 19),
                    _ => {
                        return Err(row_refusal(
                            id,
                            "B.cond needs a condition 0..=13 and a target",
                        ));
                    }
                },
                M::Cbz | M::Cbnz => match inst.operands.as_slice() {
                    [_, target] => (target, 19),
                    _ => return Err(row_refusal(id, "CBZ/CBNZ take a register and a target")),
                },
                _ => match inst.operands.as_slice() {
                    [_, O::Imm(_), target] => (target, 14),
                    _ => {
                        return Err(row_refusal(
                            id,
                            "TBZ/TBNZ take a register, a bit and a target",
                        ));
                    }
                },
            };
            let taken = target(arena_index, id, operand, bits)?;
            let other = fallthrough.ok_or_else(|| {
                control(format!(
                    "block {arena_index} falls off the end of the layout"
                ))
            })?;
            if taken == other {
                return Err(control(format!(
                    "block {arena_index} branches to {taken:?} on both edges"
                )));
            }
            exits[index] = Some(Exit::Branch {
                branch: id,
                taken,
                other,
                jump,
            });
            body = &body[..body.len() - 1];
        } else if exits[index].is_none() {
            let target = fallthrough.ok_or_else(|| {
                control(format!(
                    "block {arena_index} falls off the end of the layout"
                ))
            })?;
            exits[index] = Some(Exit::Goto { target, row: jump });
        }
        if let Some(stray) = body.iter().find(|id| transfers_control(walker.inst(**id))) {
            return Err(row_refusal(
                *stray,
                "a control transfer before the end of its block",
            ));
        }
        bodies[index] = body.to_vec();
    }
    // The derived edges must be the recorded CFG.
    let successors = |index: usize| -> Vec<BlockId> {
        match exits[index].as_ref() {
            Some(Exit::Goto { target, .. }) => vec![*target],
            Some(Exit::Branch { taken, other, .. }) => vec![*taken, *other],
            Some(Exit::Return) | None => Vec::new(),
        }
    };
    for (index, block) in machine.block_order.iter().enumerate() {
        let arena_index = block.0 as usize;
        let derived = successors(index);
        let recorded = &machine.blocks[arena_index].succs;
        let derived_preds: Vec<BlockId> = machine
            .block_order
            .iter()
            .enumerate()
            .filter(|(position, _)| successors(*position).contains(block))
            .map(|(_, predecessor)| *predecessor)
            .collect();
        let same = |a: &[BlockId], b: &[BlockId]| {
            a.len() == b.len()
                && a.iter().collect::<HashSet<_>>().len() == a.len()
                && a.iter().all(|x| b.contains(x))
        };
        if !same(&derived, recorded) || !same(&derived_preds, &machine.blocks[arena_index].preds) {
            let instruction = match exits[index].as_ref() {
                Some(Exit::Branch { branch, taken, .. }) if !recorded.contains(taken) => {
                    Some(*branch)
                }
                Some(Exit::Branch { jump, .. }) | Some(Exit::Goto { row: jump, .. }) => *jump,
                _ => None,
            };
            return Err(mismatch(A64BodyMismatch::BranchTarget {
                block: *block,
                instruction,
                defect: BranchTargetDefect::DisagreesWithCfg,
            }));
        }
    }
    // Every exit target was validated against `laid_out` above, so these
    // translations preserve original BlockIds while indexing bounded scratch.
    let entry_index = laid_out[&(machine.entry.0 as usize)];
    // Topological order of the laid-out DAG from the entry.
    #[derive(Clone, Copy, PartialEq)]
    enum Colour {
        Open,
        Done,
    }
    let mut colour: HashMap<usize, Colour> = HashMap::new();
    let mut postorder = Vec::new();
    let mut stack = vec![(entry_index, 0usize)];
    colour.insert(entry_index, Colour::Open);
    while let Some((block, next)) = stack.pop() {
        let succs = successors(block);
        let Some(target) = succs.get(next).map(|b| laid_out[&(b.0 as usize)]) else {
            colour.insert(block, Colour::Done);
            postorder.push(block);
            continue;
        };
        stack.push((block, next + 1));
        match colour.get(&target) {
            Some(Colour::Open) => {
                let block = machine.block_order[block].0;
                let target = machine.block_order[target].0;
                return Err(control(format!(
                    "a loop (block {block} branches back to block {target}); loops stay outside \
                     the body owner"
                )));
            }
            Some(Colour::Done) => {}
            None => {
                colour.insert(target, Colour::Open);
                stack.push((target, 0));
            }
        }
    }
    if postorder.len() != machine.block_order.len() {
        return Err(control(
            "a laid-out block is unreachable from the entry block",
        ));
    }
    let order: Vec<usize> = postorder.into_iter().rev().collect();
    // Gated symbolic execution.
    let mut garbage = 0usize;
    let mut fresh_input = |defs: &mut Defs, width: u32| {
        garbage += 1;
        defs.input(format!("g{garbage}"), width)
    };
    let mut initial_regs = Vec::with_capacity(31);
    for number in 0..31usize {
        initial_regs.push(match (entry.get(number), admitted.params.get(number)) {
            // AAPCS64: a B1 argument is an 8-bit 0/1 whose bits 1..7 are zero;
            // bits 8..63 stay the caller's.
            (Some(input), Some(Ty::B1)) => input.clone().bvand(E::bv_const(!0xFEu64, 64)),
            (Some(input), Some(_)) => input.clone(),
            _ => fresh_input(defs, 64),
        });
    }
    let initial = State {
        regs: initial_regs,
        flags: Flags {
            n: fresh_input(defs, 1),
            z: fresh_input(defs, 1),
            c: fresh_input(defs, 1),
            v: fresh_input(defs, 1),
        },
    };
    let mut reach: HashMap<usize, E> = HashMap::new();
    let mut exit_states: HashMap<usize, State> = HashMap::new();
    let mut incoming: HashMap<usize, Vec<(E, usize)>> = HashMap::new();
    let mut returns: Vec<(E, E)> = Vec::new();
    for &index in &order {
        let (reached, mut state) = if index == entry_index {
            (E::bv_const(1, 1), initial.clone())
        } else {
            let edges = incoming.remove(&index).unwrap_or_default();
            let (first, rest) = edges.split_first().expect("reachable");
            let mut flag = first.0.clone();
            for (taken, _) in rest {
                flag = flag.bvor(taken.clone());
            }
            let reached = if rest.is_empty() {
                flag
            } else {
                defs.machine(flag, &[])
            };
            let states: Vec<&State> = edges.iter().map(|(_, pred)| &exit_states[pred]).collect();
            let merge = |defs: &mut Defs, values: Vec<&E>| -> E {
                if values.iter().all(|value| *value == values[0]) {
                    return values[0].clone();
                }
                let mut term = values[values.len() - 1].clone();
                for (position, value) in values[..values.len() - 1].iter().enumerate().rev() {
                    term = E::ite(is_one(edges[position].0.clone()), (*value).clone(), term);
                }
                defs.machine(term, &[])
            };
            let regs = (0..31)
                .map(|n| merge(defs, states.iter().map(|s| &s.regs[n]).collect()))
                .collect();
            let flags = Flags {
                n: merge(defs, states.iter().map(|s| &s.flags.n).collect()),
                z: merge(defs, states.iter().map(|s| &s.flags.z).collect()),
                c: merge(defs, states.iter().map(|s| &s.flags.c).collect()),
                v: merge(defs, states.iter().map(|s| &s.flags.v).collect()),
            };
            (reached, State { regs, flags })
        };
        reach.insert(index, reached.clone());
        for id in &bodies[index] {
            walker.step(*id, &mut state, defs)?;
        }
        match exits[index]
            .clone()
            .expect("every laid-out block has an exit")
        {
            Exit::Goto { target, .. } => {
                // A `B` is credited as a transfer of the CFG the theorem
                // is stated over; its edge carries its block's reach.
                let taken = reached.clone();
                incoming
                    .entry(laid_out[&(target.0 as usize)])
                    .or_default()
                    .push((taken, index));
            }
            Exit::Branch {
                branch,
                taken,
                other,
                jump,
            } => {
                let test = walker.branch_test(branch, &state)?;
                let taken_flag =
                    defs.machine(and_bit(reached.clone(), bool_bv(test.clone())), &[branch]);
                let rows: Vec<InstId> = std::iter::once(branch).chain(jump).collect();
                let other_flag =
                    defs.machine(and_bit(reached.clone(), bool_bv(test.not_expr())), &rows);
                incoming
                    .entry(laid_out[&(taken.0 as usize)])
                    .or_default()
                    .push((taken_flag, index));
                incoming
                    .entry(laid_out[&(other.0 as usize)])
                    .or_default()
                    .push((other_flag, index));
            }
            Exit::Return => {
                let x0 = state.regs[0].clone();
                let observed = match walker.observe {
                    Ty::I64 => x0,
                    Ty::I8 | Ty::I16 | Ty::I32 | Ty::B1 => x0.extract(31, 0),
                };
                returns.push((reached.clone(), observed));
            }
        }
        exit_states.insert(index, state);
    }
    let (_, last) = returns.last().cloned().ok_or_else(|| control("no RET"))?;
    let mut result = last;
    for (reached, value) in returns[..returns.len() - 1].iter().rev() {
        result = E::ite(is_one(reached.clone()), value.clone(), result);
    }
    let result = defs.machine(result, &[]);
    Ok(MachineTheorem { result, rows })
}

impl Walker<'_> {
    /// The condition under which the conditional transfer `id` is taken.
    fn branch_test(&self, id: InstId, state: &State) -> Result<E, A64BodyRefusal> {
        let inst = self.inst(id);
        match (inst.opcode, inst.operands.as_slice()) {
            (M::BCond, [O::Imm(cc), _]) => Ok(condition(&state.flags, *cc as u8)),
            (M::Cbz | M::Cbnz, [register, _]) => {
                let register = gpr(register)
                    .filter(|r| matches!(r, Gpr::Reg { .. }))
                    .ok_or_else(|| row_refusal(id, "CBZ/CBNZ tests a non-GPR"))?;
                let width = register.width();
                let zero = read(state, register, width).eq_expr(E::bv_const(0, width));
                Ok(if inst.opcode == M::Cbz {
                    zero
                } else {
                    zero.not_expr()
                })
            }
            (M::Tbz | M::Tbnz, [register, O::Imm(bit), _]) => {
                let register = gpr(register)
                    .filter(|r| matches!(r, Gpr::Reg { .. }))
                    .ok_or_else(|| row_refusal(id, "TBZ/TBNZ tests a non-GPR"))?;
                let width = register.width();
                if !(0..i64::from(width)).contains(bit) {
                    return Err(row_refusal(id, "TBZ/TBNZ bit outside the register"));
                }
                let bit = *bit as u32;
                let set = is_one(read(state, register, 64).extract(bit, bit));
                Ok(if inst.opcode == M::Tbnz {
                    set
                } else {
                    set.not_expr()
                })
            }
            _ => Err(row_refusal(id, "malformed conditional transfer")),
        }
    }

    /// Apply one straight-line row.
    fn step(&self, id: InstId, state: &mut State, defs: &mut Defs) -> Result<(), A64BodyRefusal> {
        let inst = self.inst(id);
        let ops = inst.operands.as_slice();
        let refuse = |detail: &str| Err(row_refusal(id, format!("{:?}: {detail}", inst.opcode)));
        // A register operand that must name a GPR or zero register of the
        // operation width.
        let at = |operand: &O, width: u32| -> Result<Gpr, A64BodyRefusal> {
            match gpr(operand) {
                Some(register) if register.width() == width => Ok(register),
                _ => Err(row_refusal(
                    id,
                    format!(
                        "{:?}: operand {operand:?} is not a {width}-bit GPR or zero register",
                        inst.opcode
                    ),
                )),
            }
        };
        // The destination: a GPR whose class gives the operation width.
        let destination = |operand: &O| -> Result<(u8, u32), A64BodyRefusal> {
            match gpr(operand) {
                Some(Gpr::Reg { number, width }) => Ok((number, width)),
                _ => Err(row_refusal(
                    id,
                    format!("{:?}: destination {operand:?} is not a GPR", inst.opcode),
                )),
            }
        };
        let imm = |operand: &O| match operand {
            O::Imm(value) => Some(*value),
            _ => None,
        };
        match inst.opcode {
            M::Nop | M::AlignNop => Ok(()),
            M::AddRR
            | M::SubRR
            | M::AndRR
            | M::OrrRR
            | M::EorRR
            | M::BicRR
            | M::OrnRR
            | M::LslRR
            | M::LsrRR
            | M::AsrRR => {
                let [d, n, m] = ops else {
                    return refuse("takes exactly three registers");
                };
                let (number, width) = destination(d)?;
                let a = read(state, at(n, width)?, width);
                let b = read(state, at(m, width)?, width);
                let modulus = E::bv_const(u64::from(width - 1), width);
                let value = match inst.opcode {
                    M::AddRR => a.bvadd(b),
                    M::SubRR => a.bvsub(b),
                    M::AndRR => a.bvand(b),
                    M::OrrRR => a.bvor(b),
                    M::EorRR => a.bvxor(b),
                    M::BicRR => a.bvand(b.bvxor(E::bv_const(mask(width), width))),
                    M::OrnRR => a.bvor(b.bvxor(E::bv_const(mask(width), width))),
                    M::LslRR => a.bvshl(b.bvand(modulus)),
                    M::LsrRR => a.bvlshr(b.bvand(modulus)),
                    _ => a.bvashr(b.bvand(modulus)),
                };
                write(state, defs, id, number, width, value)
            }
            M::AddRRShift
            | M::SubRRShift
            | M::AddRRShiftLsr
            | M::EorRRLsl
            | M::EorRRLsr
            | M::EorRRShift => {
                // [Rd, Rn, Rm, Imm(k)]: Rn op (Rm shifted by k), 1 <= k < width
                // (the shifted-register forms the encoder emits).
                let [d, n, m, O::Imm(amount)] = ops else {
                    return refuse("takes three registers and an amount");
                };
                let (number, width) = destination(d)?;
                if !(1..i64::from(width)).contains(amount) {
                    return refuse("shift amount outside 1..width");
                }
                let a = read(state, at(n, width)?, width);
                let b = read(state, at(m, width)?, width);
                let k = *amount as u32;
                let constant = |value: u32| E::bv_const(u64::from(value), width);
                let shifted = match inst.opcode {
                    M::AddRRShift | M::SubRRShift | M::EorRRLsl => b.bvshl(constant(k)),
                    M::AddRRShiftLsr | M::EorRRLsr => b.bvlshr(constant(k)),
                    _ => ror_term(b, k, width),
                };
                let value = match inst.opcode {
                    M::AddRRShift | M::AddRRShiftLsr => a.bvadd(shifted),
                    M::SubRRShift => a.bvsub(shifted),
                    _ => a.bvxor(shifted),
                };
                write(state, defs, id, number, width, value)
            }
            M::AddRI | M::SubRI | M::AddRIShift12 => {
                let [d, n, O::Imm(value @ 0..=4095)] = ops else {
                    return refuse("takes two registers and an imm12");
                };
                let (number, width) = destination(d)?;
                // Rn = 31 is SP in these encodings: a zero register is refused.
                let n = at(n, width)?;
                if matches!(n, Gpr::Zero { .. }) {
                    return refuse("reads register 31, which is SP in this encoding");
                }
                let shift = if inst.opcode == M::AddRIShift12 {
                    12
                } else {
                    0
                };
                let constant = E::bv_const((*value as u64) << shift, width);
                let a = read(state, n, width);
                let value = if inst.opcode == M::SubRI {
                    a.bvsub(constant)
                } else {
                    a.bvadd(constant)
                };
                write(state, defs, id, number, width, value)
            }
            M::Neg => {
                let [d, n] = ops else {
                    return refuse("takes two registers");
                };
                let (number, width) = destination(d)?;
                let value = E::bv_const(0, width).bvsub(read(state, at(n, width)?, width));
                write(state, defs, id, number, width, value)
            }
            M::AndRI | M::OrrRI | M::EorRI => {
                let [d, n, O::Imm(raw)] = ops else {
                    return refuse(
                        "takes two registers and one mask (the decomposed form is refused)",
                    );
                };
                let (number, width) = destination(d)?;
                let value = (*raw as u64) & mask(width);
                if value == 0 || value == mask(width) {
                    return refuse("mask has no logical-immediate encoding");
                }
                let a = read(state, at(n, width)?, width);
                let constant = E::bv_const(value, width);
                let value = match inst.opcode {
                    M::AndRI => a.bvand(constant),
                    M::OrrRI => a.bvor(constant),
                    _ => a.bvxor(constant),
                };
                write(state, defs, id, number, width, value)
            }
            M::LslRI | M::LsrRI | M::AsrRI => {
                let [d, n, O::Imm(amount)] = ops else {
                    return refuse("takes two registers and an amount");
                };
                let (number, width) = destination(d)?;
                if !(0..i64::from(width)).contains(amount) {
                    return refuse("shift amount outside the register");
                }
                let a = read(state, at(n, width)?, width);
                let amount = E::bv_const(*amount as u64, width);
                let value = match inst.opcode {
                    M::LslRI => a.bvshl(amount),
                    M::LsrRI => a.bvlshr(amount),
                    _ => a.bvashr(amount),
                };
                write(state, defs, id, number, width, value)
            }
            M::Ubfm | M::Sbfm => {
                let [d, n, O::Imm(r), O::Imm(s)] = ops else {
                    return refuse("takes two registers, immr and imms");
                };
                let (number, width) = destination(d)?;
                if !(0..i64::from(width)).contains(r) || !(0..i64::from(width)).contains(s) {
                    return refuse("bitfield index outside the register");
                }
                let a = read(state, at(n, width)?, width);
                let value = bitfield(a, *r as u32, *s as u32, inst.opcode == M::Sbfm, width);
                write(state, defs, id, number, width, value)
            }
            M::Uxtb | M::Uxth | M::Uxtw | M::Sxtb | M::Sxth | M::Sxtw => {
                // The encoder fixes the width: UXTB/UXTH = UBFM Wd (sf=0),
                // UXTW = ORR Wd, WZR, Wn (sf=0), SXTB/SXTH/SXTW = SBFM Xd (sf=1).
                let [d, n] = ops else {
                    return refuse("takes two registers");
                };
                let Some(Gpr::Reg { number, .. }) = gpr(d) else {
                    return refuse("destination is not a GPR");
                };
                let Some(n) = gpr(n) else {
                    return refuse("source is not a GPR or zero register");
                };
                let source = read(state, n, 64);
                let (bits, signed) = match inst.opcode {
                    M::Uxtb => (8, false),
                    M::Uxth => (16, false),
                    M::Uxtw => (32, false),
                    M::Sxtb => (8, true),
                    M::Sxth => (16, true),
                    _ => (32, true),
                };
                let field = source.extract(bits - 1, 0);
                let (value, width) = if signed {
                    (field.sign_ext(64 - bits), 64)
                } else {
                    (
                        if bits == 32 {
                            field
                        } else {
                            field.zero_ext(32 - bits)
                        },
                        32,
                    )
                };
                write(state, defs, id, number, width, value)
            }
            M::CmpRR => {
                let [n, m] = ops else {
                    return refuse("takes two registers");
                };
                let width = gpr(n)
                    .map(Gpr::width)
                    .ok_or_else(|| row_refusal(id, "CMP reads a non-GPR"))?;
                let a = read(state, at(n, width)?, width);
                let b = read(state, at(m, width)?, width);
                state.flags = subs_flags(defs, id, a, b, width);
                Ok(())
            }
            M::CmpRI => {
                let [n, O::Imm(value @ 0..=4095)] = ops else {
                    return refuse("takes a register and an imm12");
                };
                // Rn = 31 is SP here: only X0-X30/W0-W30 are admitted.
                let Some(register @ Gpr::Reg { width, .. }) = gpr(n) else {
                    return refuse("reads register 31, which is SP in this encoding");
                };
                let a = read(state, register, width);
                state.flags = subs_flags(defs, id, a, E::bv_const(*value as u64, width), width);
                Ok(())
            }
            M::Tst => {
                let [n, m] = ops else {
                    return refuse("takes a register and a register or mask");
                };
                let width = gpr(n)
                    .map(Gpr::width)
                    .ok_or_else(|| row_refusal(id, "TST reads a non-GPR"))?;
                let a = read(state, at(n, width)?, width);
                let b = match imm(m) {
                    Some(raw) => {
                        let value = (raw as u64) & mask(width);
                        if value == 0 || value == mask(width) {
                            return refuse("mask has no logical-immediate encoding");
                        }
                        E::bv_const(value, width)
                    }
                    None => read(state, at(m, width)?, width),
                };
                let result = defs.machine(a.bvand(b), &[id]);
                state.flags = Flags {
                    n: defs.machine(result.clone().extract(width - 1, width - 1), &[id]),
                    z: defs.machine(bool_bv(result.eq_expr(E::bv_const(0, width))), &[id]),
                    c: E::bv_const(0, 1),
                    v: E::bv_const(0, 1),
                };
                Ok(())
            }
            M::CSet => {
                let [d, O::Imm(cc @ 0..=13)] = ops else {
                    return refuse("takes a register and a condition 0..=13");
                };
                let (number, width) = destination(d)?;
                let holds = condition(&state.flags, *cc as u8);
                let value = E::ite(holds, E::bv_const(1, width), E::bv_const(0, width));
                write(state, defs, id, number, width, value)
            }
            M::Csel | M::Csinc | M::Csinv | M::Csneg => {
                let [d, n, m, O::Imm(cc @ 0..=15)] = ops else {
                    return refuse("takes three registers and a condition");
                };
                let (number, width) = destination(d)?;
                let a = read(state, at(n, width)?, width);
                let b = read(state, at(m, width)?, width);
                let otherwise = match inst.opcode {
                    M::Csel => b,
                    M::Csinc => b.bvadd(E::bv_const(1, width)),
                    M::Csinv => b.bvxor(E::bv_const(mask(width), width)),
                    _ => E::bv_const(0, width).bvsub(b),
                };
                let value = E::ite(condition(&state.flags, *cc as u8), a, otherwise);
                write(state, defs, id, number, width, value)
            }
            M::Movz | M::Movn | M::MovI => {
                let (d, value, shift) = match ops {
                    [d, O::Imm(value)] => (d, *value, 0),
                    [d, O::Imm(value), O::Imm(0)] if inst.opcode != M::MovI => (d, *value, 0),
                    _ => return refuse("takes a register and an imm16 at shift 0"),
                };
                if !(0..=0xffff).contains(&value) {
                    return refuse("immediate outside imm16");
                }
                let (number, width) = destination(d)?;
                let shifted = (value as u64) << shift;
                let constant = if inst.opcode == M::Movn {
                    !shifted & mask(width)
                } else {
                    shifted
                };
                write(state, defs, id, number, width, E::bv_const(constant, width))
            }
            M::Movk => {
                let (d, value, shift) = match ops {
                    [d, O::Imm(value)] => (d, *value, 0),
                    [d, O::Imm(value), O::Imm(shift)] => (d, *value, *shift),
                    _ => return refuse("takes a register, an imm16 and a shift"),
                };
                let (number, width) = destination(d)?;
                if !(0..=0xffff).contains(&value)
                    || shift % 16 != 0
                    || !(0..i64::from(width)).contains(&shift)
                {
                    return refuse("immediate or shift outside the move-wide field");
                }
                let field = 0xffffu64 << shift;
                let old = read(state, Gpr::Reg { number, width }, width);
                let value = old
                    .bvand(E::bv_const(!field & mask(width), width))
                    .bvor(E::bv_const((value as u64) << shift, width));
                write(state, defs, id, number, width, value)
            }
            M::MovR | M::MOVWrr | M::MOVXrr => {
                let [d, n] = ops else {
                    return refuse("takes two registers");
                };
                let Some(Gpr::Reg {
                    number,
                    width: class,
                }) = gpr(d)
                else {
                    return refuse("destination is not a GPR");
                };
                // The typed copies fix their width whatever view an operand
                // retains after allocation; MovR takes the destination's.
                let width = match inst.opcode {
                    M::MOVWrr => 32,
                    M::MOVXrr => 64,
                    _ => class,
                };
                let Some(source) = gpr(n) else {
                    return refuse("source is not a GPR or zero register");
                };
                if inst.opcode == M::MovR && source.width() != width {
                    return refuse("operand widths differ");
                }
                let value = read(state, source, width);
                write(state, defs, id, number, width, value)
            }
            _ => refuse("is not a straight-line row of the body owner"),
        }
    }
}

/// Read `register` at `width` (the W view is the low half).
fn read(state: &State, register: Gpr, width: u32) -> E {
    match register {
        Gpr::Zero { .. } => E::bv_const(0, width),
        Gpr::Reg { number, .. } => {
            let value = state.regs[number as usize].clone();
            if width == 64 {
                value
            } else {
                value.extract(width - 1, 0)
            }
        }
    }
}

/// Write `value` (at `width`) to X`number`, naming it as row `id`'s
/// definition. A W write zeroes the upper half.
fn write(
    state: &mut State,
    defs: &mut Defs,
    id: InstId,
    number: u8,
    width: u32,
    value: E,
) -> Result<(), A64BodyRefusal> {
    if number > 17 {
        return Err(mismatch(A64BodyMismatch::PreservedWrite {
            inst: id,
            register: format!("x{number}"),
        }));
    }
    let value = defs.machine(value, &[id]);
    state.regs[number as usize] = if width == 64 {
        value
    } else {
        value.zero_ext(32)
    };
    Ok(())
}

/// NZCV of `SUBS a, b` at `width`, each flag named as row `id`'s definition.
pub(super) fn subs_flags(defs: &mut Defs, id: InstId, a: E, b: E, width: u32) -> Flags {
    let top = width - 1;
    let difference = defs.machine(a.clone().bvsub(b.clone()), &[id]);
    let sign = |term: E| term.extract(top, top);
    let overflow = sign(a.clone())
        .bvxor(sign(b.clone()))
        .bvand(sign(a.clone()).bvxor(sign(difference.clone())));
    Flags {
        n: defs.machine(sign(difference.clone()), &[id]),
        z: defs.machine(bool_bv(difference.eq_expr(E::bv_const(0, width))), &[id]),
        c: defs.machine(bool_bv(a.bvult(b).not_expr()), &[id]),
        v: defs.machine(overflow, &[id]),
    }
}

/// Direct transfers inside a bound body (`RET` excluded).
pub(super) fn is_transfer(opcode: M) -> bool {
    matches!(
        opcode,
        M::B | M::BCond | M::Cbz | M::Cbnz | M::Tbz | M::Tbnz
    )
}

/// Whether `inst` can transfer control (as `source_bound_frame` decides it).
fn transfers_control(inst: &MachInst) -> bool {
    inst.is_branch()
        || inst.is_terminator()
        || inst.is_return()
        || matches!(
            inst.opcode,
            M::B | M::BCond | M::Cbz | M::Cbnz | M::Tbz | M::Tbnz | M::Br | M::Ret
        )
}

/// Machine opcodes whose rows sit on a laid-out path but carry no value
/// (covered by the CFG/encoding checks, not by this theorem's slice).
pub(super) fn is_inert(inst: &MachInst) -> bool {
    matches!(inst.opcode, M::Nop | M::AlignNop) || inst.flags.contains(InstFlags::IS_PSEUDO)
}
