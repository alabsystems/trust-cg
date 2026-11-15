// trust-cg-verify/aarch64_i128_chain_dataflow.rs - data flow behind the i128
// NZCV-consumer bindings
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The DATA-FLOW facts the AArch64 i128 `CSET`/`CSEL` bindings need and that no
//! per-instruction row, condition table or opcode shape can supply.
//!
//! `2e194289f` bound a `CSET`/`CSEL` citation to the SOURCE condition and named
//! the holes it left open. Three of them are the same defect wearing different
//! clothes: every fact the bindings checked was read off ONE instruction and its
//! immediate neighbourhood, so any mutation that permutes ROLES between
//! instructions of the same lowering — while each instruction individually keeps
//! a shape the lowering could emit — stayed promotable:
//!
//!   * the i128 comparison's `{hi_cc, EQ, lo_cc}` triple was admitted at every
//!     position, so the right conditions in the wrong ORDER passed;
//!   * the i128 shift's `dst_lo`/`dst_hi` selects could exchange their arm
//!     PAIRS and both still satisfy the asymmetry fact;
//!   * nothing reconstructed the funnel (`hi_normal == (hi << s) | (lo >> (64 -
//!     s))`) against the cited theorem.
//!
//! Each is a question about WHERE A VALUE FLOWS, so this module answers it with
//! reaching definitions over the emitted machine code, and anchors the ends of
//! the flow on facts instruction selection does not author: the typed LIR
//! (`provenance_xcheck::LirValueFlow`) and the AAPCS64 calling convention.
//!
//! # Soundness of the reaching-definition walk
//!
//! A register's reaching definition is found by scanning BACKWARD from the use.
//! The scan is only ever allowed to step OVER an instruction when it can prove
//! that instruction does not write the register:
//!
//!   * it does not name the register (by hardware number — `Wn` and `Xn` are one
//!     register) in any operand, and does not list it in `implicit_defs`; or
//!   * its opcode is in the CLOSED table [`register_effect`], which says exactly
//!     which operand, if any, it writes.
//!
//! An opcode outside that table that names the register — as an operand, or as
//! the base of a memory operand, which a writeback form updates — ends the walk
//! with `None`. So does a call, unless the register is AAPCS64 callee-saved
//! (`x19`-`x28`), which is a calling-convention fact about every callee, not a
//! claim the code under test makes about itself. At the top of a block the walk
//! continues into EVERY predecessor and requires them all to agree on one
//! definition; a cycle, an unreachable block or a disagreement is `None`. At the
//! top of the function's entry block (with no predecessors) the value is the
//! register's value ON ENTRY, which is where the calling convention places the
//! arguments.
//!
//! Every `None` here is a REFUSAL at the binding site: a chain whose data flow
//! cannot be reconstructed is never credited to a theorem about one that can.

use super::FunctionVerifier;
use crate::aarch64_source_condition::I128CmpCsetRole;
use crate::provenance_xcheck::{LirSourceInst, LirValueOrigin};
use trust_cg_ir::provenance::{LoweringProvenance, SourceInstId};
use trust_cg_ir::{AArch64Opcode as M, BlockId, InstId, MachFunction, MachInst, MachOperand};

/// Bound on the instructions one reaching-definition query may visit, across
/// every predecessor path. A function too large to answer within it is refused,
/// never guessed about.
const REACHING_DEF_BUDGET: usize = 4096;

/// Bound on the copy chain [`resolve_copies`] follows.
const COPY_CHAIN_CAP: usize = 16;

/// The storage a register operand names. `Wn` and `Xn` are the SAME register
/// (a W write zero-extends into X), so a physical register is its hardware
/// number; a virtual register is its id.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Storage {
    Gpr(u8),
    Virtual(u32),
}

/// The storage `operand` names, or `None` for anything that is not a general
/// purpose data register (`SP`/`WSP`, the zero registers, immediates, ...).
pub(super) fn storage(operand: &MachOperand) -> Option<Storage> {
    match operand {
        MachOperand::VReg(v) => Some(Storage::Virtual(v.id)),
        MachOperand::PReg(p) => match p.encoding() {
            e @ 0..=30 => Some(Storage::Gpr(e as u8)),
            e @ 32..=62 => Some(Storage::Gpr((e - 32) as u8)),
            _ => None,
        },
        _ => None,
    }
}

/// AAPCS64 callee-saved general purpose registers: a callee must return with
/// these unchanged, so a value in one survives a call.
fn callee_saved(storage: Storage) -> bool {
    matches!(storage, Storage::Gpr(19..=28))
}

/// What an opcode does to its register operands. CLOSED: an opcode not listed
/// here is unknown, and a reaching-definition walk that meets one naming the
/// register it is tracking gives up.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum RegisterEffect {
    /// Writes operand 0 (and nothing else); every other operand is read.
    WritesOperand0,
    /// Writes no register operand.
    ReadsOnly,
}

fn register_effect(opcode: M) -> Option<RegisterEffect> {
    use RegisterEffect::{ReadsOnly, WritesOperand0};
    Some(match opcode {
        // Moves, constants, and the ALU forms the i128 lowerings use. MOVK is
        // deliberately absent: it READS its destination (a halfword splice),
        // so treating it as a plain definition would hide the prior value.
        M::Movz
        | M::Movn
        | M::MovR
        | M::MOVXrr
        | M::MOVWrr
        | M::Copy
        | M::LslRR
        | M::LsrRR
        | M::AsrRR
        | M::OrrRR
        | M::AndRR
        | M::AndRI
        | M::SubRR
        | M::SubRI
        | M::AddRR
        | M::AddRI
        | M::Csel
        | M::CSet => WritesOperand0,
        // Flag writers, branches and the inert NOP: no register is written.
        // (A NOP that still carries its coalesced copy's operands emits a
        // hardware `NOP`, or nothing: it moves no data.)
        M::CmpRR
        | M::CmpRI
        | M::CMPWrr
        | M::CMPXrr
        | M::CMPWri
        | M::CMPXri
        | M::Nop
        | M::Ret
        | M::B
        | M::BCond
        | M::Bcc
        | M::Cbz
        | M::Cbnz => ReadsOnly,
        _ => return None,
    })
}

/// Where the value a register holds at some program point was defined.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Def {
    /// Written by the instruction at this position of this block.
    At { block: BlockId, pos: usize },
    /// The register's value on FUNCTION ENTRY — an incoming argument register.
    FunctionEntry(Storage),
}

/// The block whose instruction list `block_insts` is — the NZCV-consumer arms
/// receive the slice, and a cross-block walk needs the block. Requires the
/// instruction at `block_pos` to sit at that position of exactly one block.
pub(super) fn block_of(
    func: &MachFunction,
    block_insts: &[InstId],
    block_pos: usize,
) -> Option<BlockId> {
    let id = block_insts.get(block_pos)?;
    let mut found = None;
    for (index, block) in func.blocks.iter().enumerate() {
        if block.insts.as_slice() == block_insts && block.insts.get(block_pos) == Some(id) {
            if found.is_some() {
                return None;
            }
            found = Some(BlockId(index as u32));
        }
    }
    found
}

fn inst_at(func: &MachFunction, block: BlockId, pos: usize) -> Option<&MachInst> {
    let id = func.blocks.get(block.0 as usize)?.insts.get(pos)?;
    func.insts.get(id.0 as usize)
}

fn stamp(func: &MachFunction, block: BlockId, pos: usize) -> Option<SourceInstId> {
    let id = func.blocks.get(block.0 as usize)?.insts.get(pos)?;
    match func.inst_lowering_provenance(*id) {
        LoweringProvenance::SourceInst { id, .. } => Some(id),
        LoweringProvenance::Synthetic { .. } => None,
    }
}

/// The definition reaching the use at `(block, use_pos)` of the register
/// `operand` names. See the module docs for why every step is sound.
pub(super) fn reaching_def(
    func: &MachFunction,
    block: BlockId,
    use_pos: usize,
    operand: &MachOperand,
) -> Option<Def> {
    let target = storage(operand)?;
    let mut budget = REACHING_DEF_BUDGET;
    let mut path = Vec::new();
    reaching_def_in(func, block, use_pos, target, &mut path, &mut budget)
}

fn reaching_def_in(
    func: &MachFunction,
    block: BlockId,
    use_pos: usize,
    target: Storage,
    path: &mut Vec<BlockId>,
    budget: &mut usize,
) -> Option<Def> {
    let insts = &func.blocks.get(block.0 as usize)?.insts;
    for pos in (0..use_pos.min(insts.len())).rev() {
        *budget = budget.checked_sub(1)?;
        let inst = func.insts.get(insts[pos].0 as usize)?;
        if inst.is_call() && !(matches!(target, Storage::Virtual(_)) || callee_saved(target)) {
            return None;
        }
        if inst
            .implicit_defs
            .iter()
            .any(|reg| storage(&MachOperand::PReg(*reg)) == Some(target))
        {
            return None;
        }
        // A memory operand's base register counts as NAMED: a writeback form
        // updates it, so an unknown opcode carrying it must stop the walk.
        let names = |operand: &MachOperand| match operand {
            MachOperand::MemOp { base, .. } => storage(&MachOperand::PReg(*base)) == Some(target),
            other => storage(other) == Some(target),
        };
        if !inst.operands.iter().any(names) {
            continue;
        }
        match register_effect(inst.opcode)? {
            RegisterEffect::WritesOperand0 if storage(inst.operands.first()?) == Some(target) => {
                return Some(Def::At { block, pos });
            }
            RegisterEffect::WritesOperand0 | RegisterEffect::ReadsOnly => {}
        }
    }
    let this = func.blocks.get(block.0 as usize)?;
    if block == func.entry {
        // Entry-block top: the value on function entry, but only when nothing
        // can branch back here — otherwise it is also a loop-carried value.
        return this
            .preds
            .is_empty()
            .then_some(Def::FunctionEntry(target))
            .filter(|_| matches!(target, Storage::Gpr(_)));
    }
    if this.preds.is_empty() || path.contains(&block) {
        return None;
    }
    path.push(block);
    let mut agreed = None;
    for pred in &this.preds {
        let end = func.blocks.get(pred.0 as usize)?.insts.len();
        let found = reaching_def_in(func, *pred, end, target, path, budget)?;
        match agreed {
            None => agreed = Some(found),
            Some(seen) if seen == found => {}
            Some(_) => return None,
        }
    }
    path.pop();
    agreed
}

/// Register width of an operand, in bits, when it is a data register.
fn width(operand: &MachOperand) -> Option<u32> {
    super::operand_reg_width_bits(operand)
}

/// Follow full-width register-to-register copies back to the definition that
/// produced the value. A copy is followed only when the width it MOVES is at
/// least `min_width` bits, so a 32-bit copy never stands in for a 64-bit limb.
///
/// That width is the narrower of the two register views, except for `MOVWrr`:
/// the encoder takes its `sf = 0` from the OPCODE, so it moves 32 bits (the
/// low word, zero-extended) even when both operands name X registers.
pub(super) fn resolve_copies(func: &MachFunction, mut def: Def, min_width: u32) -> Option<Def> {
    for _ in 0..COPY_CHAIN_CAP {
        let Def::At { block, pos } = def else {
            return Some(def);
        };
        let inst = inst_at(func, block, pos)?;
        let is_copy = matches!(inst.opcode, M::MovR | M::MOVXrr | M::MOVWrr | M::Copy)
            && inst.operands.len() == 2
            && inst.implicit_defs.is_empty();
        if !is_copy {
            return Some(def);
        }
        let (dst, src) = (inst.operands.first()?, inst.operands.get(1)?);
        let moved = width(dst)?.min(width(src)?);
        let moved = if inst.opcode == M::MOVWrr {
            moved.min(32)
        } else {
            moved
        };
        if moved < min_width {
            return Some(def);
        }
        def = reaching_def(func, block, pos, src)?;
    }
    None
}

/// The copy-resolved definition of operand `index` of the instruction at
/// `(block, pos)`.
fn operand_def(
    func: &MachFunction,
    block: BlockId,
    pos: usize,
    index: usize,
    min_width: u32,
) -> Option<Def> {
    let inst = inst_at(func, block, pos)?;
    let def = reaching_def(func, block, pos, inst.operands.get(index)?)?;
    resolve_copies(func, def, min_width)
}

/// The instruction a definition names (`None` for an entry value).
fn def_inst(func: &MachFunction, def: Def) -> Option<(&MachInst, BlockId, usize)> {
    match def {
        Def::At { block, pos } => Some((inst_at(func, block, pos)?, block, pos)),
        Def::FunctionEntry(_) => None,
    }
}

/// True when `def` is a single `MOVZ` of the constant `value` with no shift.
/// (`MOVZ Wd` zero-extends, so either width materialises the same 64-bit value.)
fn is_movz_constant(func: &MachFunction, def: Def, value: i64) -> bool {
    let Some((inst, _, _)) = def_inst(func, def) else {
        return false;
    };
    inst.opcode == M::Movz
        && inst.implicit_defs.is_empty()
        && match inst.operands.as_slice() {
            [_, MachOperand::Imm(imm)] | [_, MachOperand::Imm(imm), MachOperand::Imm(0)] => {
                *imm == value
            }
            _ => false,
        }
}

// ---------------------------------------------------------------------------
// AAPCS64 argument and result registers
// ---------------------------------------------------------------------------

/// The general purpose registers a formal parameter or result occupies.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum GprAssignment {
    One(u8),
    /// A 128-bit integer: low limb, high limb (little-endian register pair).
    Pair {
        lo: u8,
        hi: u8,
    },
}

/// The AAPCS64 registers of formal parameter `index`, computed from the SOURCE
/// signature by the calling convention's own rule (next general register
/// number; a 128-bit integer takes two).
///
/// Refuses (`None`) whenever the rule would need a case this does not model: an
/// aggregate or vector before or at `index`, a stack-passed argument, or a
/// 128-bit integer at an ODD register number, where the even-pair rounding
/// would apply — so no result here depends on that rounding at all.
pub(super) fn formal_gprs(params: &[trust_cg_lower::Type], index: usize) -> Option<GprAssignment> {
    use trust_cg_lower::Type as T;
    let mut next = 0u8;
    for (position, ty) in params.iter().enumerate().take(index + 1) {
        let assignment = match ty {
            T::I8 | T::I16 | T::I32 | T::I64 | T::B1 => {
                let reg = next;
                next = next.checked_add(1)?;
                Some(GprAssignment::One(reg))
            }
            T::I128 => {
                if !next.is_multiple_of(2) {
                    return None;
                }
                let lo = next;
                next = next.checked_add(2)?;
                Some(GprAssignment::Pair { lo, hi: lo + 1 })
            }
            // Floating-point and vector formals travel in V registers and
            // consume no general register.
            T::F16 | T::F32 | T::F64 | T::V64 | T::V128 => None,
            T::Struct(_) | T::Array(..) | T::Enum { .. } => return None,
        };
        if next > 8 {
            return None;
        }
        if position == index {
            return assignment;
        }
    }
    None
}

// ---------------------------------------------------------------------------
// HOLE 3: the i128 comparison's CSET roles
// ---------------------------------------------------------------------------

/// The ROLE of the `CSET` at `block_pos` inside `select_i128_cmp`'s limb
/// decomposition, derived from the DATA FLOW of the instructions stamped with
/// the same source instruction — never from the `CSET`'s own condition, and
/// never from its position alone.
///
/// Position alone is not enough, and that is not a hypothetical: the two
/// high-limb `CSET`s read the same flags and write different registers, so they
/// are INDEPENDENT and may appear in either order. `CSET hi_cond, LT ; CSET
/// hi_eq, EQ` and `CSET hi_eq, LT ; CSET hi_cond, EQ` place the same conditions
/// at the same positions and compute different predicates. The role is
/// therefore what the value is USED for:
///
///   * `EQ`/`NE` (two `CSET`s): each reads a DIFFERENT same-stamp `CMP`, and
///     one same-stamp combiner reads both — an `AND` makes them
///     [`I128CmpCsetRole::LimbConjunct`], an `ORR`
///     [`I128CmpCsetRole::LimbDisjunct`];
///   * ordered (three `CSET`s): `result = ORR(hi_cond, AND(hi_eq, lo_cond))`.
///     The `CMP` two `CSET`s read is the HIGH comparison and the other is the
///     LOW one; of the two high `CSET`s, the one the `ORR` reads is
///     [`I128CmpCsetRole::HighDecision`] and the one the `AND` reads is
///     [`I128CmpCsetRole::HighEqual`]; the low one must feed the `AND` and is
///     [`I128CmpCsetRole::LowDecision`].
///
/// Every operand link is a reaching definition (see the module docs), so a
/// register reused between the `CSET` and its reader cannot fake one. Any other
/// arrangement — a third `CMP`, a `CSET` whose flags come from outside the
/// group, a missing or duplicated combiner — is `None`.
///
/// What this does NOT establish: that the HIGH comparison compares the high
/// LIMBS. Which registers hold which limb of the two operands is a question
/// about their producers (loads, carry chains, constants, arguments), each with
/// its own limb rule, and is not answered here.
pub(super) fn i128_cmp_cset_role(
    func: &MachFunction,
    block_insts: &[InstId],
    block: BlockId,
    block_pos: usize,
) -> Option<I128CmpCsetRole> {
    let anchor = stamp(func, block, block_pos)?;
    let same = |pos: usize| stamp(func, block, pos) == Some(anchor);
    let group: Vec<usize> = (0..block_insts.len()).filter(|&pos| same(pos)).collect();
    let opcode = |pos: usize| inst_at(func, block, pos).map(|inst| inst.opcode);
    let cmps: Vec<usize> = group
        .iter()
        .copied()
        .filter(|&pos| opcode(pos).is_some_and(FunctionVerifier::is_cmp_opcode))
        .collect();
    let csets: Vec<usize> = group
        .iter()
        .copied()
        .filter(|&pos| opcode(pos) == Some(M::CSet))
        .collect();
    if cmps.len() != 2 || !csets.contains(&block_pos) {
        return None;
    }
    // Every CSET must read the flags of one of the group's two CMPs.
    let mut reads = Vec::with_capacity(csets.len());
    for &pos in &csets {
        let (producer, _, _) = FunctionVerifier::reaching_flag_producer_at(func, block_insts, pos)?;
        reads.push((pos, cmps.iter().position(|&cmp| cmp == producer)?));
    }
    let reads_of = |pos: usize| -> Option<[Def; 2]> {
        Some([
            operand_def(func, block, pos, 1, 1)?,
            operand_def(func, block, pos, 2, 1)?,
        ])
    };
    let at = |pos: usize| Def::At { block, pos };
    match csets.len() {
        2 => {
            if reads[0].1 == reads[1].1 {
                return None;
            }
            // The two limb tests are COMBINED by exactly one same-stamp `AND`
            // or `ORR` that reads both; which one decides the role, because
            // `hi_eq & lo_eq` is `a == b` and `hi_eq | lo_eq` is not.
            let combiners: Vec<(usize, M)> = group
                .iter()
                .filter_map(|&pos| match opcode(pos)? {
                    op @ (M::AndRR | M::OrrRR) => Some((pos, op)),
                    _ => None,
                })
                .collect();
            let [(combiner, op)] = combiners.as_slice() else {
                return None;
            };
            let combined = reads_of(*combiner)?;
            if !(combined.contains(&at(csets[0])) && combined.contains(&at(csets[1]))) {
                return None;
            }
            Some(if *op == M::AndRR {
                I128CmpCsetRole::LimbConjunct
            } else {
                I128CmpCsetRole::LimbDisjunct
            })
        }
        3 => {
            let high_cmp = if reads.iter().filter(|(_, cmp)| *cmp == 0).count() == 2 {
                0
            } else if reads.iter().filter(|(_, cmp)| *cmp == 1).count() == 2 {
                1
            } else {
                return None;
            };
            let low = reads.iter().find(|(_, cmp)| *cmp != high_cmp)?.0;
            let ands: Vec<usize> = group
                .iter()
                .copied()
                .filter(|&pos| opcode(pos) == Some(M::AndRR))
                .collect();
            let orrs: Vec<usize> = group
                .iter()
                .copied()
                .filter(|&pos| opcode(pos) == Some(M::OrrRR))
                .collect();
            let ([and], [orr]) = (ands.as_slice(), orrs.as_slice()) else {
                return None;
            };
            let and_reads = reads_of(*and)?;
            let orr_reads = reads_of(*orr)?;
            let high: Vec<usize> = reads
                .iter()
                .filter(|(_, cmp)| *cmp == high_cmp)
                .map(|(pos, _)| *pos)
                .collect();
            let (equal, decision) = match high.as_slice() {
                [a, b] if and_reads.contains(&at(*a)) => (*a, *b),
                [a, b] if and_reads.contains(&at(*b)) => (*b, *a),
                _ => return None,
            };
            // result = ORR(decision, AND(equal, low)): both links, both ways.
            let and_ok = and_reads.contains(&at(equal)) && and_reads.contains(&at(low));
            let orr_ok = orr_reads.contains(&at(decision)) && orr_reads.contains(&at(*and));
            if !(and_ok && orr_ok) {
                return None;
            }
            Some(if block_pos == decision {
                I128CmpCsetRole::HighDecision
            } else if block_pos == equal {
                I128CmpCsetRole::HighEqual
            } else {
                I128CmpCsetRole::LowDecision
            })
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// HOLES 2 and 4: the i128 variable-shift funnel
// ---------------------------------------------------------------------------

/// The shift direction a chain implements, from the SOURCE opcode.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum ShiftDirection {
    Left,
    LogicalRight,
    ArithmeticRight,
}

/// The three selects of one i128 variable-shift chain, by ROLE, plus the chain's
/// three leaves as the reconstruction found them.
///
/// Roles are assigned by the ONE structural asymmetry every direction shares:
/// the `HS` select whose FALSE arm is the funnel's `ORR` is the "combined" limb
/// (`dst_hi` for a left shift, `dst_lo` for a right shift). Nothing here is
/// read off a destination register, which is the point: the destinations are
/// what [`I128ShiftChain::outputs_anchored`] then checks.
#[derive(Clone, Copy, Debug)]
pub(super) struct I128ShiftChain {
    pub(super) direction: ShiftDirection,
    pub(super) block: BlockId,
    pub(super) spill_guard: usize,
    pub(super) lo_select: usize,
    pub(super) hi_select: usize,
    /// The chain's low source limb, as the combined limb's funnel reads it.
    pub(super) src_lo: Option<Def>,
    /// The chain's high source limb, as the combined limb's funnel reads it.
    pub(super) src_hi: Option<Def>,
    /// The value the `CMP ..., #0` guard compares.
    pub(super) amount: Option<Def>,
}

impl I128ShiftChain {
    /// Identify the chain's three selects by role. `None` when the same-stamp
    /// group is not exactly one `EQ` guard and two `HS` selects of which exactly
    /// one has an `ORR` false arm.
    pub(super) fn identify(
        func: &MachFunction,
        block: BlockId,
        block_insts: &[InstId],
        block_pos: usize,
        direction: ShiftDirection,
    ) -> Option<Self> {
        let anchor = stamp(func, block, block_pos)?;
        let csels: Vec<usize> = (0..block_insts.len())
            .filter(|&pos| {
                stamp(func, block, pos) == Some(anchor)
                    && inst_at(func, block, pos).is_some_and(|inst| inst.opcode == M::Csel)
            })
            .collect();
        if csels.len() != 3 {
            return None;
        }
        let cc = |pos: usize| match inst_at(func, block, pos)?.operands.get(3)? {
            MachOperand::Imm(cc) => Some(*cc),
            _ => None,
        };
        let guards: Vec<usize> = csels
            .iter()
            .copied()
            .filter(|&p| cc(p) == Some(0))
            .collect();
        let selects: Vec<usize> = csels
            .iter()
            .copied()
            .filter(|&p| cc(p) == Some(2))
            .collect();
        let ([spill_guard], [a, b]) = (guards.as_slice(), selects.as_slice()) else {
            return None;
        };
        let false_arm_is_orr = |pos: usize| {
            operand_def(func, block, pos, 2, 64)
                .and_then(|def| def_inst(func, def))
                .is_some_and(|(inst, _, _)| inst.opcode == M::OrrRR)
        };
        let (combined, plain) = match (false_arm_is_orr(*a), false_arm_is_orr(*b)) {
            (true, false) => (*a, *b),
            (false, true) => (*b, *a),
            _ => return None,
        };
        let (lo_select, hi_select) = match direction {
            ShiftDirection::Left => (plain, combined),
            ShiftDirection::LogicalRight | ShiftDirection::ArithmeticRight => (combined, plain),
        };
        let mut chain = Self {
            direction,
            block,
            spill_guard: *spill_guard,
            lo_select,
            hi_select,
            src_lo: None,
            src_hi: None,
            amount: None,
        };
        chain.read_leaves(func);
        Some(chain)
    }

    /// The leaves, read from ONE place each: the amount from the guard's own
    /// `CMP`, and both source limbs from the combined limb's funnel — for a left
    /// shift `ORR(LSL(hi, s), spill)` reads `hi` and the spill guard's raw arm
    /// `LSR(lo, 64 - s)` reads `lo`; for a right shift `ORR(LSR(lo, s), spill)`
    /// reads `lo` and the raw arm `LSL(hi, 64 - s)` reads `hi`.
    /// [`Self::shape_mismatch`] then requires every other occurrence to agree.
    fn read_leaves(&mut self, func: &MachFunction) {
        let block = self.block;
        self.amount = FunctionVerifier::reaching_flag_producer_at(
            func,
            &func.blocks[block.0 as usize].insts,
            self.spill_guard,
        )
        .and_then(|(cmp, _, _)| operand_def(func, block, cmp, 0, 32));
        let raw_spill_value =
            operand_def(func, block, self.spill_guard, 2, 64).and_then(|def| match def {
                Def::At { block, pos } => operand_def(func, block, pos, 1, 64),
                Def::FunctionEntry(_) => None,
            });
        let combined = match self.direction {
            ShiftDirection::Left => self.hi_select,
            ShiftDirection::LogicalRight | ShiftDirection::ArithmeticRight => self.lo_select,
        };
        let combined_shift_value = operand_def(func, block, combined, 2, 64).and_then(|orr| {
            let Def::At { block, pos } = orr else {
                return None;
            };
            // The ORR operand that is NOT the spill guard is the shifted limb.
            let guard = Def::At {
                block: self.block,
                pos: self.spill_guard,
            };
            let first = operand_def(func, block, pos, 1, 64)?;
            let shifted = if first == guard {
                operand_def(func, block, pos, 2, 64)?
            } else {
                first
            };
            let Def::At { block, pos } = shifted else {
                return None;
            };
            operand_def(func, block, pos, 1, 64)
        });
        match self.direction {
            ShiftDirection::Left => {
                self.src_lo = raw_spill_value;
                self.src_hi = combined_shift_value;
            }
            ShiftDirection::LogicalRight | ShiftDirection::ArithmeticRight => {
                self.src_hi = raw_spill_value;
                self.src_lo = combined_shift_value;
            }
        }
    }

    /// HOLE 4 — the DATA FLOW. `None` when every select's arms are built from
    /// the leaves exactly as the cited whole-chain theorem
    /// (`lowering_proof::proof_{ishl,ushr,sshr}_i128`) builds them; otherwise
    /// the first disagreement, for the refusal trace.
    ///
    /// ```text
    ///   n = SUB(#64, s)      b = SUB(s, #64)      z = MOVZ #0
    ///   left:  spill = CSEL.EQ(z, LSR(lo, n))
    ///          dst_lo = CSEL.HS(z, LSL(lo, s))
    ///          dst_hi = CSEL.HS(LSL(lo, b), ORR(LSL(hi, s), spill))
    ///   lshr:  spill = CSEL.EQ(z, LSL(hi, n))
    ///          dst_hi = CSEL.HS(z, LSR(hi, s))
    ///          dst_lo = CSEL.HS(LSR(hi, b), ORR(LSR(lo, s), spill))
    ///   ashr:  spill = CSEL.EQ(z, LSL(hi, n))
    ///          dst_hi = CSEL.HS(ASR(hi, #63), ASR(hi, s))
    ///          dst_lo = CSEL.HS(ASR(hi, b), ORR(LSR(lo, s), spill))
    /// ```
    ///
    /// Every limb operation must be 64-bit (destination and value operand); the
    /// amount may be read through either register view, because register shifts
    /// use it modulo 64 and the guards compare it directly. Both `HS` selects and
    /// the `EQ` guard must read the flags of a `CMP` of THIS amount against the
    /// boundary their condition pairs with. `lo` and `hi` must be different
    /// values.
    pub(super) fn shape_mismatch(&self, func: &MachFunction) -> Option<&'static str> {
        let (Some(lo), Some(hi), Some(s)) = (self.src_lo, self.src_hi, self.amount) else {
            return Some("a chain leaf could not be read");
        };
        if lo == hi {
            return Some("the two source limbs are the same value");
        }
        let block = self.block;
        let guard = Def::At {
            block,
            pos: self.spill_guard,
        };
        // `op(value, amount)` at `def`, with a 64-bit destination and value.
        let shift = |def: Def, opcode: M, value: Def, amount: &dyn Fn(Def) -> bool| -> bool {
            let Some((inst, b, p)) = def_inst(func, def) else {
                return false;
            };
            inst.opcode == opcode
                && inst.operands.len() == 3
                && inst.implicit_defs.is_empty()
                && width(&inst.operands[0]) == Some(64)
                && width(&inst.operands[1]) == Some(64)
                && operand_def(func, b, p, 1, 64) == Some(value)
                && operand_def(func, b, p, 2, 32).is_some_and(amount)
        };
        let is_amount = |def: Def| def == s;
        // `SUB(x, y)` at `def`, 64-bit destination, operands matched by `x`/`y`.
        let sub = |def: Def, x: &dyn Fn(Def) -> bool, y: &dyn Fn(Def) -> bool| -> bool {
            let Some((inst, b, p)) = def_inst(func, def) else {
                return false;
            };
            inst.opcode == M::SubRR
                && inst.operands.len() == 3
                && inst.implicit_defs.is_empty()
                && width(&inst.operands[0]) == Some(64)
                && operand_def(func, b, p, 1, 32).is_some_and(x)
                && operand_def(func, b, p, 2, 32).is_some_and(y)
        };
        let c64 = |def: Def| is_movz_constant(func, def, 64);
        let neg = |def: Def| sub(def, &c64, &is_amount);
        let big = |def: Def| sub(def, &is_amount, &c64);
        let zero = |def: Def| is_movz_constant(func, def, 0);
        let arms = |pos: usize| -> Option<(Def, Def)> {
            Some((
                operand_def(func, block, pos, 1, 64)?,
                operand_def(func, block, pos, 2, 64)?,
            ))
        };
        // `ORR(shifted, spill)`, either operand order.
        let orr_with_spill = |def: Def, shifted: &dyn Fn(Def) -> bool| -> bool {
            let Some((inst, b, p)) = def_inst(func, def) else {
                return false;
            };
            let (Some(x), Some(y)) = (
                operand_def(func, b, p, 1, 64),
                operand_def(func, b, p, 2, 64),
            ) else {
                return false;
            };
            inst.opcode == M::OrrRR
                && inst.operands.len() == 3
                && inst.implicit_defs.is_empty()
                && width(&inst.operands[0]) == Some(64)
                && ((x == guard && shifted(y)) || (y == guard && shifted(x)))
        };
        // The three guards' flags: `CMP s, #0` for EQ, `CMP s, #64` for HS.
        let insts = &func.blocks[block.0 as usize].insts;
        let compares_amount = |pos: usize, boundary: i64| {
            FunctionVerifier::reaching_flag_producer_at(func, insts, pos).is_some_and(
                |(cmp, opcode, _)| {
                    FunctionVerifier::is_cmp_opcode(opcode)
                        && inst_at(func, block, cmp).is_some_and(|inst| {
                            matches!(inst.operands.get(1), Some(MachOperand::Imm(b)) if *b == boundary)
                                && inst.operands.len() == 2
                        })
                        && operand_def(func, block, cmp, 0, 32) == Some(s)
                },
            )
        };
        if !compares_amount(self.spill_guard, 0) {
            return Some("the EQ guard does not test this amount against #0");
        }
        if !compares_amount(self.lo_select, 64) || !compares_amount(self.hi_select, 64) {
            return Some("an HS select does not test this amount against #64");
        }
        let (Some((g_true, g_false)), Some((lo_true, lo_false)), Some((hi_true, hi_false))) = (
            arms(self.spill_guard),
            arms(self.lo_select),
            arms(self.hi_select),
        ) else {
            return Some("a select arm has no reconstructible definition");
        };
        let by_neg = |def: Def| neg(def);
        let by_big = |def: Def| big(def);
        let ok = match self.direction {
            ShiftDirection::Left => {
                zero(g_true)
                    && shift(g_false, M::LsrRR, lo, &by_neg)
                    && zero(lo_true)
                    && shift(lo_false, M::LslRR, lo, &is_amount)
                    && shift(hi_true, M::LslRR, lo, &by_big)
                    && orr_with_spill(hi_false, &|d| shift(d, M::LslRR, hi, &is_amount))
            }
            ShiftDirection::LogicalRight => {
                zero(g_true)
                    && shift(g_false, M::LslRR, hi, &by_neg)
                    && zero(hi_true)
                    && shift(hi_false, M::LsrRR, hi, &is_amount)
                    && shift(lo_true, M::LsrRR, hi, &by_big)
                    && orr_with_spill(lo_false, &|d| shift(d, M::LsrRR, lo, &is_amount))
            }
            ShiftDirection::ArithmeticRight => {
                let c63 = |def: Def| is_movz_constant(func, def, 63);
                zero(g_true)
                    && shift(g_false, M::LslRR, hi, &by_neg)
                    && shift(hi_true, M::AsrRR, hi, &c63)
                    && shift(hi_false, M::AsrRR, hi, &is_amount)
                    && shift(lo_true, M::AsrRR, hi, &by_big)
                    && orr_with_spill(lo_false, &|d| shift(d, M::LsrRR, lo, &is_amount))
            }
        };
        (!ok).then_some("the select arms are not the cited theorem's funnel")
    }

    /// HOLE 4, the LEAVES — the source limbs are the SHIFTED OPERAND's limbs.
    ///
    /// The source's shifted operand must be a FORMAL parameter of type `i128`
    /// whose AAPCS64 register pair is known, and the chain's `lo`/`hi` leaves
    /// must be exactly that pair's registers ON FUNCTION ENTRY. A shifted value
    /// with any other origin (a load, another chain's result, a join) has no
    /// limb rule here, so the binding refuses it rather than trusting ISel's
    /// private value map for which register is which limb.
    pub(super) fn inputs_anchored(&self, func: &MachFunction, source: &LirSourceInst) -> bool {
        use trust_cg_ir::function::Type as MachType;
        let flow = &source.value_flow;
        let Some(LirValueOrigin::Formal { index }) = flow.args.first() else {
            return false;
        };
        let index = *index as usize;
        if flow.signature.params.get(index) != Some(&trust_cg_lower::Type::I128)
            || func.signature.params.get(index) != Some(&MachType::I128)
        {
            return false;
        }
        let Some(GprAssignment::Pair { lo, hi }) = formal_gprs(&flow.signature.params, index)
        else {
            return false;
        };
        self.src_lo == Some(Def::FunctionEntry(Storage::Gpr(lo)))
            && self.src_hi == Some(Def::FunctionEntry(Storage::Gpr(hi)))
    }

    /// HOLE 4, the AMOUNT — the value the guards compare and the limbs shift by
    /// is the source's SHIFT AMOUNT operand.
    ///
    /// Either the amount is a single-register formal and the chain's amount is
    /// that register on function entry (the low limb, for an `i128` count, which
    /// is what `use_i128_shift_amount` reads), or it is the single result of a
    /// scalar LIR instruction and the chain's amount is written by the LAST
    /// machine instruction stamped with THAT instruction in its block — the one
    /// whose destination is the lowered value. Anything else is refused.
    pub(super) fn amount_anchored(&self, func: &MachFunction, source: &LirSourceInst) -> bool {
        use trust_cg_lower::Type as T;
        let flow = &source.value_flow;
        let amount_type = flow.arg_types.get(1).and_then(Option::as_ref);
        let Some(amount) = self.amount else {
            return false;
        };
        match flow.args.get(1) {
            Some(LirValueOrigin::Formal { index }) => {
                let reg = match formal_gprs(&flow.signature.params, *index as usize) {
                    Some(GprAssignment::One(reg)) => reg,
                    Some(GprAssignment::Pair { lo, .. }) => lo,
                    None => return false,
                };
                amount == Def::FunctionEntry(Storage::Gpr(reg))
            }
            Some(LirValueOrigin::Def { id }) => {
                if !matches!(amount_type, Some(T::I8 | T::I16 | T::I32 | T::I64)) {
                    return false;
                }
                let Def::At { block, pos } = amount else {
                    return false;
                };
                let Some(insts) = func.blocks.get(block.0 as usize).map(|b| &b.insts) else {
                    return false;
                };
                stamp(func, block, pos) == Some(*id)
                    && ((pos + 1)..insts.len()).all(|later| stamp(func, block, later) != Some(*id))
            }
            Some(LirValueOrigin::Unknown) | None => false,
        }
    }

    /// HOLE 2 — each select's destination flows to the result limb its role
    /// names.
    ///
    /// The source result's ONLY use must be the function's `Return` of exactly
    /// that value, with an `i128` return type in both the LIR and the machine
    /// signature, so the calling convention (not ISel) fixes the limbs: `x0` is
    /// the low limb and `x1` the high limb at `RET`. The chain's block must end
    /// in a `RET` stamped with that `Return`, and the reaching definitions of
    /// `x0` and `x1` there (through 64-bit copies) must be exactly the low and
    /// high selects. Exchanging the two selects' arm pairs — the hole
    /// `2e194289f` disclosed — leaves every per-select fact intact and fails
    /// here, because the select that now computes the high limb is the one whose
    /// value `x0` returns.
    pub(super) fn outputs_anchored(&self, func: &MachFunction, source: &LirSourceInst) -> bool {
        use trust_cg_ir::function::Type as MachType;
        let flow = &source.value_flow;
        let Some(returned_by) = flow.sole_result_returned_by else {
            return false;
        };
        if flow.signature.returns.as_slice() != [trust_cg_lower::Type::I128]
            || func.signature.returns.as_slice() != [MachType::I128]
        {
            return false;
        }
        let Some(insts) = func.blocks.get(self.block.0 as usize).map(|b| &b.insts) else {
            return false;
        };
        let Some(ret) = insts.len().checked_sub(1) else {
            return false;
        };
        if inst_at(func, self.block, ret).map(|inst| inst.opcode) != Some(M::Ret)
            || stamp(func, self.block, ret) != Some(returned_by)
        {
            return false;
        }
        let limb = |reg: u8| {
            reaching_def(
                func,
                self.block,
                ret,
                &MachOperand::PReg(trust_cg_ir::PReg::new(reg as u16)),
            )
            .and_then(|def| resolve_copies(func, def, 64))
        };
        limb(0)
            == Some(Def::At {
                block: self.block,
                pos: self.lo_select,
            })
            && limb(1)
                == Some(Def::At {
                    block: self.block,
                    pos: self.hi_select,
                })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::{PReg, SpecialReg};
    use trust_cg_lower::Type as T;

    fn x(n: u16) -> MachOperand {
        MachOperand::PReg(PReg::new(n))
    }
    fn w(n: u16) -> MachOperand {
        MachOperand::PReg(PReg::new(32 + n))
    }

    /// One block, the given instructions, entry with no predecessors.
    fn one_block(insts: Vec<MachInst>) -> MachFunction {
        let mut func = MachFunction::new(
            "dataflow".into(),
            trust_cg_ir::function::Signature::new(vec![], vec![]),
        );
        for inst in insts {
            let id = func.push_inst(inst);
            func.append_inst(func.entry, id);
        }
        func
    }

    /// The AAPCS64 rule, including the cases it refuses rather than model.
    #[test]
    fn formal_gprs_follows_aapcs64_and_refuses_what_it_does_not_model() {
        assert_eq!(
            formal_gprs(&[T::I128, T::I32], 0),
            Some(GprAssignment::Pair { lo: 0, hi: 1 })
        );
        assert_eq!(
            formal_gprs(&[T::I128, T::I32], 1),
            Some(GprAssignment::One(2))
        );
        assert_eq!(
            formal_gprs(&[T::F64, T::I128], 1),
            Some(GprAssignment::Pair { lo: 0, hi: 1 })
        );
        // An i128 at an ODD register number would need the even-pair rounding.
        assert_eq!(formal_gprs(&[T::I64, T::I128], 1), None);
        // Floating-point formals have no general register.
        assert_eq!(formal_gprs(&[T::F64], 0), None);
        // Aggregates are not modelled, before or at the index.
        assert_eq!(formal_gprs(&[T::Struct(vec![T::I64]), T::I64], 1), None);
        // The ninth general register is on the stack.
        let nine: Vec<T> = std::iter::repeat_n(T::I64, 9).collect();
        assert_eq!(formal_gprs(&nine, 7), Some(GprAssignment::One(7)));
        assert_eq!(formal_gprs(&nine, 8), None);
        assert_eq!(formal_gprs(&nine[..3], 5), None);
    }

    /// `Wn` and `Xn` are one register; `SP` and the zero registers are none.
    #[test]
    fn storage_aliases_w_and_x_views() {
        assert_eq!(storage(&x(5)), storage(&w(5)));
        assert_ne!(storage(&x(5)), storage(&x(6)));
        assert_eq!(storage(&MachOperand::Special(SpecialReg::SP)), None);
        assert_eq!(storage(&MachOperand::Special(SpecialReg::XZR)), None);
        assert_eq!(storage(&MachOperand::Imm(0)), None);
    }

    /// A call preserves exactly the AAPCS64 callee-saved registers; an unknown
    /// opcode naming the register — including as a memory base — ends the walk;
    /// a W write is a definition of the X register.
    #[test]
    fn reaching_def_is_conservative_at_calls_unknown_opcodes_and_aliases() {
        let call = MachInst::new(M::Bl, vec![MachOperand::Symbol("callee".into())]);
        let func = one_block(vec![
            MachInst::new(M::MOVXrr, vec![x(19), x(0)]),
            MachInst::new(M::MOVXrr, vec![x(9), x(1)]),
            call,
            MachInst::new(M::OrrRR, vec![x(2), x(19), x(9)]),
        ]);
        let entry = func.entry;
        assert_eq!(
            reaching_def(&func, entry, 3, &x(19)),
            Some(Def::At {
                block: entry,
                pos: 0
            })
        );
        assert_eq!(
            reaching_def(&func, entry, 3, &x(9)),
            None,
            "x9 is caller-saved"
        );
        // Through the copy to the argument register, on entry.
        let def = reaching_def(&func, entry, 3, &x(19)).unwrap();
        assert_eq!(
            resolve_copies(&func, def, 64),
            Some(Def::FunctionEntry(Storage::Gpr(0)))
        );

        let func = one_block(vec![
            MachInst::new(M::Movz, vec![x(3), MachOperand::Imm(1)]),
            MachInst::new(M::LdrRI, vec![x(4), x(3), MachOperand::Imm(8)]),
            MachInst::new(M::Movz, vec![w(5), MachOperand::Imm(7)]),
            MachInst::new(M::OrrRR, vec![x(6), x(3), x(5)]),
        ]);
        let entry = func.entry;
        assert_eq!(
            reaching_def(&func, entry, 3, &x(3)),
            None,
            "LdrRI is not modelled"
        );
        assert_eq!(
            reaching_def(&func, entry, 3, &x(5)),
            Some(Def::At {
                block: entry,
                pos: 2
            })
        );

        let func = one_block(vec![
            MachInst::new(M::Movz, vec![x(3), MachOperand::Imm(1)]),
            MachInst::new(
                M::LdrRI,
                vec![
                    x(4),
                    MachOperand::MemOp {
                        base: PReg::new(3),
                        offset: 8,
                    },
                ],
            ),
            MachInst::new(M::OrrRR, vec![x(6), x(3), x(3)]),
        ]);
        assert_eq!(
            reaching_def(&func, func.entry, 2, &x(3)),
            None,
            "a memory base may be written back"
        );
    }

    /// A 32-bit copy never stands in for a 64-bit value.
    #[test]
    fn resolve_copies_respects_the_width() {
        let func = one_block(vec![
            MachInst::new(M::MOVWrr, vec![w(9), x(2)]),
            MachInst::new(M::OrrRR, vec![x(6), x(9), x(9)]),
        ]);
        let def = reaching_def(&func, func.entry, 1, &x(9)).unwrap();
        assert_eq!(
            resolve_copies(&func, def, 64),
            Some(Def::At {
                block: func.entry,
                pos: 0
            })
        );
        assert_eq!(
            resolve_copies(&func, def, 32),
            Some(Def::FunctionEntry(Storage::Gpr(2)))
        );
    }

    /// `MOVWrr` moves 32 bits by OPCODE, whatever views its operands name, so
    /// `MOVWrr x9, x2` truncates and is not followed for a 64-bit value;
    /// `MOVXrr` over the same views is.
    #[test]
    fn resolve_copies_takes_movwrr_width_from_the_opcode() {
        for (opcode, followed_at_64) in [(M::MOVWrr, false), (M::MOVXrr, true)] {
            let func = one_block(vec![
                MachInst::new(opcode, vec![x(9), x(2)]),
                MachInst::new(M::OrrRR, vec![x(6), x(9), x(9)]),
            ]);
            let def = reaching_def(&func, func.entry, 1, &x(9)).unwrap();
            let entry = Some(Def::FunctionEntry(Storage::Gpr(2)));
            let copy = Some(Def::At {
                block: func.entry,
                pos: 0,
            });
            assert_eq!(
                resolve_copies(&func, def, 64),
                if followed_at_64 { entry } else { copy },
                "{opcode:?} at 64 bits"
            );
            assert_eq!(
                resolve_copies(&func, def, 32),
                entry,
                "{opcode:?} at 32 bits"
            );
        }
    }
}
