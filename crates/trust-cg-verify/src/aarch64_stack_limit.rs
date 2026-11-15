// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `[TCG-A64-STACK-LIMIT]`: the U10 prologue stack-limit net over the final
//! AArch64 stream (`docs/u10-prologue-stack-limit.md` §6), and the module
//! reserve bound (§5).
//!
//! # What the net establishes
//!
//! For a function whose [`MachFunction::stack_limit`] is set, [`check`]
//! accepts the stream only when:
//!
//! 1. the entry block has no predecessor and starts with callee-saved stores
//!    and frame-pointer setup only (pre-index and offset `STP` on SP, then
//!    `ADD X29, SP, #k`): nothing else runs before the check, so in
//!    particular nothing writes the limit register;
//! 2. the check follows: an optional `LDR X17, [Xk, #off]` (`Pointee`), then
//!    `SUBS X16|XZR, SP, Xl` with `Xl` the declared source, `B.LO overflow`,
//!    and, with `X16`, a compare of X16 with `F` (`CMP #F`, or a
//!    `MOVZ`/`MOVK` chain into X17 and `CMP X16, X17`) and a second
//!    `B.LO overflow`. It branches exactly when `P − F <ℤ L` for `P` = SP at
//!    the check (lemma, §7 of the design);
//! 3. the pass path is the only way into the rest of the function, so every
//!    SP decrement below the callee-saved area, probe, frame access, call and
//!    tail call is dominated by the check;
//! 4. the deepest CFA offset the function reaches — its SP height and every
//!    SP-, FP- or frame-address-based load and store — is at most
//!    `total = csa + F`;
//! 5. the overflow block has no predecessor but the check and either is
//!    `BRK #0x534c` alone (`Trap`) or restores exactly the saved pairs with
//!    loads only, returns SP to its entry value, and ends in a `TailCall` of
//!    the declared handler (`Handler`).
//!
//! A function with no stack storage at all (no SP write, no SP/FP access, no
//! non-tail call) needs no check; [`check`] certifies that elision instead.
//!
//! # Model and assumptions
//!
//! SP height and frame addresses are byte offsets from the CFA (SP at
//! entry). Registers holding `CFA + c` (from `ADD/SUB` on SP, X29 or another
//! frame address, `MOV`, and `MOVZ`/`MOVK` constants added to a frame
//! address) are tracked through the whole function with a must-agree join;
//! SP must have one height at every join. The counted static probe loop is
//! summarized from its counter's constant entry value. As in the TV-6 frame
//! net, frame cells are private (an access through a register that is not a
//! known frame address is not a frame access) and a call writes only below
//! its own SP. The net is per-compile structural validation, never a proof:
//! it has no diagnostic mode, no environment switch and no decline — a
//! stream it cannot model is a refusal.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use trust_cg_ir::function::{
    MachStackLimit, STACK_LIMIT_TRAP_IMM, StackLimitOverflow, StackLimitSource,
};
use trust_cg_ir::types::{BlockId, InstId};
use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, MachOperand, PReg, SpecialReg};

mod entry_demand;
pub use entry_demand::{
    EntryStackDemand, EntryStackDemandUnknown, entry_stack_demand,
    entry_stack_demand_with_assumptions,
};

/// AArch64 condition code `LO` (`CC`, unsigned lower).
pub const COND_LO: i64 = 0b0011;

/// Why a stream fails the stack-limit net. Each kind is a named mutation
/// control of the design (§6).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum StackLimitViolationKind {
    /// The entry block is a branch target, or the code before the check is
    /// not the callee-saved prologue (including a write to the limit
    /// register before the check).
    PreCheckCode,
    /// The compare sequence is missing, moved, or has the wrong source,
    /// destination, condition or constant.
    CheckShape,
    /// The overflow block is wrong: other predecessors, a store, an SP
    /// decrement, an incomplete restore, a wrong handler or trap.
    OverflowPath,
    /// The function reaches deeper than the checked total, or its SP cannot
    /// be modeled (an unknown SP write, a height disagreement at a join).
    FrameDepth,
    /// A frame access this net cannot decode.
    UnmodeledFrameAccess,
    /// The stream is malformed for this net (dangling ids, no entry).
    Malformed,
}

impl StackLimitViolationKind {
    /// Stable tag for diagnostics.
    pub fn tag(self) -> &'static str {
        match self {
            Self::PreCheckCode => "pre-check-code",
            Self::CheckShape => "check-shape",
            Self::OverflowPath => "overflow-path",
            Self::FrameDepth => "frame-depth",
            Self::UnmodeledFrameAccess => "unmodeled-frame-access",
            Self::Malformed => "malformed",
        }
    }
}

/// A refused stream.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackLimitViolation {
    /// What failed.
    pub kind: StackLimitViolationKind,
    /// Where and why.
    pub detail: String,
}

impl std::fmt::Display for StackLimitViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.kind.tag(), self.detail)
    }
}

impl std::error::Error for StackLimitViolation {}

fn violation(kind: StackLimitViolationKind, detail: impl Into<String>) -> StackLimitViolation {
    StackLimitViolation {
        kind,
        detail: detail.into(),
    }
}

/// What [`check`] certified for one requesting function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StackLimitOutcome {
    /// The check is present and verified.
    Checked(CheckedStackLimit),
    /// The function has no stack storage and makes no non-tail call, so it
    /// needs no check.
    Elided,
}

/// The verified facts of one present check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedStackLimit {
    /// Callee-saved area bytes written before the check.
    pub csa: u32,
    /// The SP adjustment `F` the check compares against.
    pub sp_adj: u32,
    /// `csa + F`: the frame the check guarantees lies at or above `L`.
    pub total: u32,
    /// Deepest CFA offset the function reaches (at most `total`).
    pub deepest: u32,
    /// The X register holding (or pointing at) the limit.
    pub limit_reg: PReg,
    /// The limit source.
    pub source: StackLimitSource,
    /// The overflow action.
    pub overflow: StackLimitOverflow,
    /// The check's instructions, in order (for instruction-ID crediting).
    pub check_insts: Vec<InstId>,
    /// The overflow block.
    pub overflow_block: BlockId,
}

/// The certificate [`check`] issues for a requesting function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackLimitCertificate {
    /// The function's symbol.
    pub function: String,
    /// What was certified.
    pub outcome: StackLimitOutcome,
}

impl StackLimitCertificate {
    /// Bytes the function can write below its entry SP before its check
    /// passes (the callee-saved area), 0 when elided.
    pub fn pre_check_bytes(&self) -> u32 {
        match &self.outcome {
            StackLimitOutcome::Checked(checked) => checked.csa,
            StackLimitOutcome::Elided => 0,
        }
    }
}

// ---------------------------------------------------------------------------
// Register and operand helpers (independent of the encoder)
// ---------------------------------------------------------------------------

const X16_NUM: u8 = 16;
const X17_NUM: u8 = 17;
const X29_NUM: u8 = 29;

/// The X/W register number 0..=30 of a GPR, if `reg` is one.
fn gpr_num(reg: PReg) -> Option<u8> {
    match reg.encoding() {
        e @ 0..=30 => Some(e as u8),
        e @ 32..=62 => Some((e - 32) as u8),
        _ => None,
    }
}

fn is_x_reg(reg: PReg, num: u8) -> bool {
    reg.encoding() == u16::from(num)
}

fn is_sp_operand(op: &MachOperand) -> bool {
    match op {
        MachOperand::Special(SpecialReg::SP) => true,
        MachOperand::PReg(p) => matches!(p.encoding(), 31 | 63),
        _ => false,
    }
}

fn is_xzr_operand(op: &MachOperand) -> bool {
    match op {
        MachOperand::Special(SpecialReg::XZR) => true,
        MachOperand::PReg(p) => p.encoding() == 160,
        _ => false,
    }
}

fn is_x_operand(op: &MachOperand, num: u8) -> bool {
    matches!(op, MachOperand::PReg(p) if is_x_reg(*p, num))
}

/// Transfer width in bytes of a data register.
fn reg_bytes(reg: PReg) -> Option<i64> {
    match reg.encoding() {
        0..=30 | 160 => Some(8),
        32..=62 | 161 => Some(4),
        64..=95 => Some(16),
        96..=127 => Some(8),
        128..=159 => Some(4),
        165..=196 => Some(2),
        197..=228 => Some(1),
        _ => None,
    }
}

fn is_call(inst: &MachInst) -> bool {
    use AArch64Opcode::*;
    inst.is_call() || matches!(inst.opcode, Bl | BL | Blr | BLR | TlsDescCall | BlrTlsdesc)
}

fn is_non_tail_call(inst: &MachInst) -> bool {
    is_call(inst) && inst.opcode != AArch64Opcode::TailCall
}

fn is_compare(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        CmpRR | CmpRI | CMPWrr | CMPXrr | CMPWri | CMPXri | Tst | Fcmp
    )
}

// ---------------------------------------------------------------------------
// Memory decoding
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Base {
    Sp,
    Reg(u8),
}

#[derive(Debug, Clone)]
struct Access {
    base: Base,
    /// Displacement of the first byte from the base before writeback.
    disp: i64,
    /// Base update of a pre/post-index form.
    writeback: Option<i64>,
    /// Data registers in address order.
    data: Vec<PReg>,
    /// Bytes per data register.
    width: i64,
    is_load: bool,
}

enum Mem {
    None,
    Access(Access),
    Unmodeled,
}

fn base_of(op: &MachOperand) -> Option<Base> {
    match op {
        op if is_sp_operand(op) => Some(Base::Sp),
        MachOperand::PReg(p) => gpr_num(*p).map(Base::Reg),
        _ => None,
    }
}

fn addressing(ops: &[MachOperand]) -> Option<(Base, i64)> {
    match ops {
        [MachOperand::MemOp { base, offset }] => {
            let base = if matches!(base.encoding(), 31 | 63) {
                Base::Sp
            } else {
                Base::Reg(gpr_num(*base)?)
            };
            Some((base, *offset))
        }
        [base, MachOperand::Imm(offset)] => Some((base_of(base)?, *offset)),
        [base] => Some((base_of(base)?, 0)),
        _ => None,
    }
}

fn data_reg(op: &MachOperand) -> Option<PReg> {
    match op {
        MachOperand::PReg(p) if !matches!(p.encoding(), 31 | 63) => Some(*p),
        MachOperand::Special(SpecialReg::XZR) => Some(trust_cg_ir::aarch64_regs::XZR),
        MachOperand::Special(SpecialReg::WZR) => Some(trust_cg_ir::aarch64_regs::WZR),
        _ => None,
    }
}

fn scalar_width(op: AArch64Opcode, data: PReg) -> Option<i64> {
    use AArch64Opcode::*;
    match op {
        LdrRI | StrRI | VolatileLdrRI | VolatileStrRI | LdrPreIndex | StrPreIndex
        | LdrPostIndex | StrPostIndex => reg_bytes(data),
        LdrbRI | StrbRI | LdrsbRI | VolatileLdrbRI | VolatileStrbRI => Some(1),
        LdrhRI | StrhRI | LdrshRI | VolatileLdrhRI | VolatileStrhRI => Some(2),
        STRWui | STRSui => Some(4),
        STRXui | STRDui => Some(8),
        _ => None,
    }
}

fn decode_memory(inst: &MachInst) -> Mem {
    use AArch64Opcode::*;
    let ops = inst.operands.as_slice();
    let op = inst.opcode;
    let decoded = match op {
        LdrRI | LdrbRI | LdrhRI | LdrsbRI | LdrshRI | VolatileLdrRI | VolatileLdrbRI
        | VolatileLdrhRI | StrRI | StrbRI | StrhRI | VolatileStrRI | VolatileStrbRI
        | VolatileStrhRI | STRWui | STRXui | STRSui | STRDui => (|| {
            let data = data_reg(ops.first()?)?;
            let (base, disp) = addressing(&ops[1..])?;
            Some(Access {
                base,
                disp,
                writeback: None,
                data: vec![data],
                width: scalar_width(op, data)?,
                is_load: matches!(
                    op,
                    LdrRI
                        | LdrbRI
                        | LdrhRI
                        | LdrsbRI
                        | LdrshRI
                        | VolatileLdrRI
                        | VolatileLdrbRI
                        | VolatileLdrhRI
                ),
            })
        })(),
        LdrPreIndex | StrPreIndex | LdrPostIndex | StrPostIndex => (|| {
            let [data, base, MachOperand::Imm(amount)] = ops else {
                return None;
            };
            let data = data_reg(data)?;
            let pre = matches!(op, LdrPreIndex | StrPreIndex);
            Some(Access {
                base: base_of(base)?,
                disp: if pre { *amount } else { 0 },
                writeback: Some(*amount),
                data: vec![data],
                width: scalar_width(op, data)?,
                is_load: matches!(op, LdrPreIndex | LdrPostIndex),
            })
        })(),
        StpRI | LdpRI => (|| {
            let first = data_reg(ops.first()?)?;
            let second = data_reg(ops.get(1)?)?;
            let (base, disp) = addressing(ops.get(2..)?)?;
            let width = reg_bytes(first)?;
            (reg_bytes(second)? == width).then_some(Access {
                base,
                disp,
                writeback: None,
                data: vec![first, second],
                width,
                is_load: op == LdpRI,
            })
        })(),
        StpPreIndex | LdpPostIndex | NeonStpQPost | NeonLdpQPost => (|| {
            let [first, second, base, MachOperand::Imm(amount)] = ops else {
                return None;
            };
            let first = data_reg(first)?;
            let second = data_reg(second)?;
            let width = reg_bytes(first)?;
            if reg_bytes(second)? != width {
                return None;
            }
            let pre = op == StpPreIndex;
            Some(Access {
                base: base_of(base)?,
                disp: if pre { *amount } else { 0 },
                writeback: Some(*amount),
                data: vec![first, second],
                width,
                is_load: matches!(op, LdpPostIndex | NeonLdpQPost),
            })
        })(),
        _ => {
            return if inst.reads_memory() || inst.writes_memory() {
                Mem::Unmodeled
            } else {
                Mem::None
            };
        }
    };
    decoded.map_or(Mem::Unmodeled, Mem::Access)
}

// ---------------------------------------------------------------------------
// Abstract state
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Val {
    /// `CFA + c`.
    Frame(i64),
    /// A known constant.
    Const(u64),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct State {
    /// SP height relative to the CFA.
    sp: i64,
    /// Known X register values by number.
    regs: BTreeMap<u8, Val>,
}

impl State {
    fn entry() -> Self {
        Self {
            sp: 0,
            regs: BTreeMap::new(),
        }
    }

    fn base_value(&self, base: Base) -> Option<i64> {
        match base {
            Base::Sp => Some(self.sp),
            Base::Reg(num) => match self.regs.get(&num) {
                Some(Val::Frame(address)) => Some(*address),
                _ => None,
            },
        }
    }

    fn meet(&self, other: &Self) -> Option<Self> {
        if self.sp != other.sp {
            return None;
        }
        let regs = self
            .regs
            .iter()
            .filter(|(num, val)| other.regs.get(num) == Some(val))
            .map(|(num, val)| (*num, *val))
            .collect();
        Some(Self { sp: self.sp, regs })
    }

    fn kill(&mut self, reg: PReg) {
        if let Some(num) = gpr_num(reg) {
            self.regs.remove(&num);
        }
    }

    fn operand_val(&self, op: &MachOperand) -> Option<Val> {
        match op {
            op if is_sp_operand(op) => Some(Val::Frame(self.sp)),
            MachOperand::PReg(p) => gpr_num(*p).and_then(|num| self.regs.get(&num).copied()),
            MachOperand::Imm(v) => u64::try_from(*v).ok().map(Val::Const),
            _ => None,
        }
    }
}

/// Deepest point tracked so far (most negative CFA offset).
#[derive(Debug, Clone, Copy)]
struct Depth {
    deepest: i64,
}

impl Depth {
    fn reach(&mut self, offset: i64) {
        self.deepest = self.deepest.min(offset);
    }
}

fn add_val(a: Val, b: Val, negate_b: bool) -> Option<Val> {
    match (a, b) {
        (Val::Frame(f), Val::Const(c)) => {
            let c = i64::try_from(c).ok()?;
            Some(Val::Frame(if negate_b {
                f.checked_sub(c)?
            } else {
                f.checked_add(c)?
            }))
        }
        (Val::Const(c), Val::Frame(f)) if !negate_b => {
            Some(Val::Frame(f.checked_add(i64::try_from(c).ok()?)?))
        }
        (Val::Const(x), Val::Const(y)) => Some(Val::Const(if negate_b {
            x.wrapping_sub(y)
        } else {
            x.wrapping_add(y)
        })),
        _ => None,
    }
}

/// Apply one instruction. `deep` collects the deepest frame byte. Returns
/// the violation for an SP write or frame access the model cannot follow.
fn transfer(
    inst: &MachInst,
    state: &mut State,
    deep: &mut Depth,
) -> Result<(), StackLimitViolation> {
    use AArch64Opcode::*;
    if inst.is_pseudo() {
        return Ok(());
    }
    match decode_memory(inst) {
        Mem::Access(access) => {
            if let Some(base) = state.base_value(access.base) {
                let span = access.width * access.data.len() as i64;
                deep.reach(base + access.disp);
                deep.reach(base + access.disp + span - 1);
                if let Some(amount) = access.writeback {
                    let updated = base + amount;
                    match access.base {
                        Base::Sp => {
                            state.sp = updated;
                            deep.reach(updated);
                        }
                        Base::Reg(num) => {
                            state.regs.insert(num, Val::Frame(updated));
                        }
                    }
                }
            } else if access.writeback.is_some()
                && let Base::Reg(num) = access.base
            {
                state.regs.remove(&num);
            }
            if access.is_load {
                for data in &access.data {
                    state.kill(*data);
                }
            }
            return Ok(());
        }
        Mem::Unmodeled => {
            let frame_operand = inst.operands.iter().any(|op| {
                is_sp_operand(op)
                    || matches!(op, MachOperand::MemOp { base, .. } if matches!(base.encoding(), 31 | 63) || gpr_num(*base).is_some_and(|num| state.regs.contains_key(&num)))
                    || matches!(op, MachOperand::PReg(p) if gpr_num(*p).is_some_and(|num| matches!(state.regs.get(&num), Some(Val::Frame(_)))))
            });
            if frame_operand {
                return Err(violation(
                    StackLimitViolationKind::UnmodeledFrameAccess,
                    format!(
                        "{:?} {:?} touches memory through a frame address",
                        inst.opcode, inst.operands
                    ),
                ));
            }
            for def in inst.implicit_defs {
                state.kill(*def);
            }
            if let Some(MachOperand::PReg(dst)) = inst.operands.first() {
                state.kill(*dst);
            }
            return Ok(());
        }
        Mem::None => {}
    }

    if is_call(inst) {
        // The callee preserves SP and X19-X29; everything else is clobbered.
        state.regs.retain(|num, _| (19..=29).contains(num));
        return Ok(());
    }
    if inst.flags.is_branch() || inst.is_return() || is_compare(inst.opcode) {
        return Ok(());
    }

    let ops = inst.operands.as_slice();
    let Some(dst) = ops.first() else {
        return Ok(());
    };
    if is_sp_operand(dst) {
        let new_sp = match (inst.opcode, ops) {
            (AddRI, [_, src, MachOperand::Imm(k)]) => match state.operand_val(src) {
                Some(Val::Frame(f)) => Some(f + k),
                _ => None,
            },
            (SubRI, [_, src, MachOperand::Imm(k)]) => match state.operand_val(src) {
                Some(Val::Frame(f)) => Some(f - k),
                _ => None,
            },
            _ => None,
        };
        let Some(new_sp) = new_sp else {
            return Err(violation(
                StackLimitViolationKind::FrameDepth,
                format!(
                    "{:?} {:?} sets SP to a value this net cannot follow",
                    inst.opcode, ops
                ),
            ));
        };
        state.sp = new_sp;
        deep.reach(new_sp);
        return Ok(());
    }
    let MachOperand::PReg(dst_reg) = dst else {
        return Ok(());
    };
    let value = match (inst.opcode, ops) {
        (AddRI, [_, src, MachOperand::Imm(k)]) => state
            .operand_val(src)
            .and_then(|v| add_val(v, Val::Const(u64::try_from(*k).ok()?), false)),
        (SubRI, [_, src, MachOperand::Imm(k)]) => state
            .operand_val(src)
            .and_then(|v| add_val(v, Val::Const(u64::try_from(*k).ok()?), true)),
        (AddRR, [_, a, b]) => match (state.operand_val(a), state.operand_val(b)) {
            (Some(a), Some(b)) => add_val(a, b, false),
            _ => None,
        },
        (SubRR, [_, a, b]) => match (state.operand_val(a), state.operand_val(b)) {
            (Some(a), Some(b)) => add_val(a, b, true),
            _ => None,
        },
        (MovR, [_, src]) => state.operand_val(src),
        (Movz | MOVZWi | MOVZXi, [_, MachOperand::Imm(v)]) => {
            u64::try_from(*v).ok().map(Val::Const)
        }
        (Movz | MOVZXi, [_, MachOperand::Imm(v), MachOperand::Imm(shift)]) => {
            let (v, shift) = (u64::try_from(*v).ok(), u32::try_from(*shift).ok());
            match (v, shift) {
                (Some(v), Some(shift)) if shift < 64 => Some(Val::Const(v << shift)),
                _ => None,
            }
        }
        (Movk, [_, MachOperand::Imm(v), MachOperand::Imm(shift)]) => {
            match (
                state.operand_val(dst),
                u64::try_from(*v).ok(),
                u32::try_from(*shift).ok(),
            ) {
                (Some(Val::Const(c)), Some(v), Some(shift)) if shift < 64 => Some(Val::Const(
                    (c & !(0xFFFF << shift)) | ((v & 0xFFFF) << shift),
                )),
                _ => None,
            }
        }
        _ => None,
    };
    // Only 64-bit destinations carry addresses.
    match (gpr_num(*dst_reg), value) {
        (Some(num), Some(value)) if dst_reg.encoding() <= 30 => {
            state.regs.insert(num, value);
        }
        _ => state.kill(*dst_reg),
    }
    for def in inst.implicit_defs {
        state.kill(*def);
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Whole-function SP model
// ---------------------------------------------------------------------------

/// The counted probe loop frame lowering emits: one or more
/// `SUB SP, SP, #a`, `STR XZR, [SP]`, `SUBS Xc, Xc, #1`, `B.NE self`.
/// Returns (bytes per iteration, counter register number).
fn probe_loop_shape(func: &MachFunction, block: BlockId) -> Option<(i64, u8)> {
    let b = func.blocks.get(block.0 as usize)?;
    if !b.succs.contains(&block) || b.succs.len() != 2 {
        return None;
    }
    let insts: Vec<&MachInst> = b
        .insts
        .iter()
        .map(|id| func.insts.get(id.0 as usize))
        .collect::<Option<Vec<_>>>()?
        .into_iter()
        .filter(|inst| !inst.is_pseudo())
        .collect();
    let mut step = 0i64;
    let mut i = 0;
    while let Some(inst) = insts.get(i) {
        match (inst.opcode, inst.operands.as_slice()) {
            (AArch64Opcode::SubRI, [dst, src, MachOperand::Imm(a)])
                if is_sp_operand(dst) && is_sp_operand(src) && *a > 0 =>
            {
                step = step.checked_add(*a)?;
                i += 1;
            }
            _ => break,
        }
    }
    if step == 0 {
        return None;
    }
    let probe = insts.get(i)?;
    let Mem::Access(access) = decode_memory(probe) else {
        return None;
    };
    if probe.opcode != AArch64Opcode::StrRI
        || access.base != Base::Sp
        || access.disp != 0
        || !access.data.iter().all(|d| d.encoding() == 160)
    {
        return None;
    }
    let counter = insts.get(i + 1)?;
    let (
        AArch64Opcode::SubsRI,
        [
            MachOperand::PReg(d),
            MachOperand::PReg(s),
            MachOperand::Imm(1),
        ],
    ) = (counter.opcode, counter.operands.as_slice())
    else {
        return None;
    };
    if d != s || d.encoding() > 30 {
        return None;
    }
    let branch = insts.get(i + 2)?;
    if branch.opcode != AArch64Opcode::BCond || insts.len() != i + 3 {
        return None;
    }
    Some((step, gpr_num(*d)?))
}

/// Run the SP/frame-address model over every block reachable from `start`
/// in state `start_state`, skipping `exclude` (the overflow block, checked
/// separately), and record the deepest CFA offset in `deep`.
///
/// A conditional branch inside a block hands its target the state at the
/// branch; the block's end state goes to every other successor. A target
/// reached in two different SP heights is refused.
fn model_depth(
    func: &MachFunction,
    layout: &Layout,
    start: BlockId,
    start_state: State,
    exclude: Option<BlockId>,
    deep: &mut Depth,
) -> Result<(), StackLimitViolation> {
    let block_count = func.blocks.len();
    let mut in_states: Vec<Option<State>> = vec![None; block_count];
    in_states[start.0 as usize] = Some(start_state);
    let mut work = VecDeque::from([start]);
    let mut visits = 0usize;
    let budget = block_count.saturating_mul(64).max(1024);
    while let Some(block) = work.pop_front() {
        visits += 1;
        if visits > budget {
            return Err(violation(
                StackLimitViolationKind::FrameDepth,
                "frame-address model did not converge",
            ));
        }
        let Some(mut state) = in_states[block.0 as usize].clone() else {
            continue;
        };
        let b = &func.blocks[block.0 as usize];
        let mut edges: Vec<(BlockId, State)> = Vec::new();
        let probe_loop = probe_loop_shape(func, block);
        if let Some((step, counter)) = probe_loop {
            // Summarize the counted loop from its counter's constant entry.
            let Some(Val::Const(iterations)) = state.regs.get(&counter).copied() else {
                return Err(violation(
                    StackLimitViolationKind::FrameDepth,
                    format!("probe loop {block:?} has no constant iteration count"),
                ));
            };
            let iterations = i64::try_from(iterations)
                .ok()
                .filter(|n| *n > 0)
                .ok_or_else(|| {
                    violation(
                        StackLimitViolationKind::FrameDepth,
                        format!("probe loop {block:?} has a non-positive iteration count"),
                    )
                })?;
            let allocated = step.checked_mul(iterations).ok_or_else(|| {
                violation(
                    StackLimitViolationKind::FrameDepth,
                    "probe loop size overflows",
                )
            })?;
            state.sp -= allocated;
            deep.reach(state.sp);
            state.regs.insert(counter, Val::Const(0));
        } else {
            let last_real = b
                .insts
                .iter()
                .rev()
                .find(|id| {
                    func.insts
                        .get(id.0 as usize)
                        .is_some_and(|i| !i.is_pseudo())
                })
                .copied();
            for id in &b.insts {
                let inst = func.insts.get(id.0 as usize).ok_or_else(|| {
                    violation(
                        StackLimitViolationKind::Malformed,
                        format!("dangling {id:?}"),
                    )
                })?;
                if Some(*id) != last_real
                    && inst.is_conditional_branch()
                    && let Some(target) = branch_target(layout, *id, inst)
                {
                    edges.push((target, state.clone()));
                }
                transfer(inst, &mut state, deep)?;
            }
        }
        let mid_targets: BTreeSet<BlockId> = edges.iter().map(|(t, _)| *t).collect();
        for &succ in &b.succs {
            if probe_loop.is_some() && succ == block {
                continue;
            }
            if !mid_targets.contains(&succ) {
                edges.push((succ, state.clone()));
            }
        }
        for (succ, out) in edges {
            if Some(succ) == exclude {
                continue;
            }
            let slot = in_states.get_mut(succ.0 as usize).ok_or_else(|| {
                violation(
                    StackLimitViolationKind::Malformed,
                    format!("dangling {succ:?}"),
                )
            })?;
            let merged = match slot {
                None => Some(out),
                Some(existing) => {
                    let merged = existing.meet(&out).ok_or_else(|| {
                        violation(
                            StackLimitViolationKind::FrameDepth,
                            format!(
                                "SP height disagrees entering {succ:?} ({} vs {})",
                                existing.sp, out.sp
                            ),
                        )
                    })?;
                    (merged != *existing).then_some(merged)
                }
            };
            if let Some(merged) = merged {
                *slot = Some(merged);
                work.push_back(succ);
            }
        }
    }
    Ok(())
}

/// The deepest CFA offset (bytes below the entry SP) `func` reaches through
/// its own SP and frame accesses, under the model above. Calls are not
/// followed. Used for the frame of every function in the module bound.
pub fn frame_depth(func: &MachFunction) -> Result<u32, StackLimitViolation> {
    if func.entry.0 as usize >= func.blocks.len() {
        return Err(violation(
            StackLimitViolationKind::Malformed,
            "no entry block",
        ));
    }
    let mut deep = Depth { deepest: 0 };
    model_depth(
        func,
        &layout(func),
        func.entry,
        State::entry(),
        None,
        &mut deep,
    )?;
    u32::try_from(-deep.deepest).map_err(|_| {
        violation(
            StackLimitViolationKind::FrameDepth,
            "frame depth exceeds 4 GiB",
        )
    })
}

// ---------------------------------------------------------------------------
// The check
// ---------------------------------------------------------------------------

/// Layout offsets (in instructions) of each real instruction, and the first
/// block starting at each offset, for resolved branch immediates.
struct Layout {
    inst_offset: BTreeMap<InstId, i64>,
    block_at: BTreeMap<i64, BlockId>,
}

fn layout(func: &MachFunction) -> Layout {
    let mut inst_offset = BTreeMap::new();
    let mut block_at = BTreeMap::new();
    let mut offset = 0i64;
    for &block in &func.block_order {
        block_at.entry(offset).or_insert(block);
        if let Some(b) = func.blocks.get(block.0 as usize) {
            for &id in &b.insts {
                if func
                    .insts
                    .get(id.0 as usize)
                    .is_some_and(|inst| !inst.is_pseudo())
                {
                    inst_offset.insert(id, offset);
                    offset += 1;
                }
            }
        }
    }
    Layout {
        inst_offset,
        block_at,
    }
}

/// The block a conditional branch targets: its `Block` operand, or the
/// block its resolved displacement (in instructions) lands on.
fn branch_target(layout: &Layout, id: InstId, inst: &MachInst) -> Option<BlockId> {
    let index = match inst.opcode {
        AArch64Opcode::BCond | AArch64Opcode::Bcc | AArch64Opcode::Cbz | AArch64Opcode::Cbnz => 1,
        AArch64Opcode::Tbz | AArch64Opcode::Tbnz => 2,
        _ => return None,
    };
    match inst.operands.get(index)? {
        MachOperand::Block(block) => Some(*block),
        MachOperand::Imm(displacement) => {
            let at = layout.inst_offset.get(&id)? + displacement;
            layout.block_at.get(&at).copied()
        }
        _ => None,
    }
}

fn expect_lo_branch(
    func: &MachFunction,
    layout: &Layout,
    stream: &[(InstId, &MachInst)],
    at: usize,
) -> Result<BlockId, StackLimitViolation> {
    let Some((id, inst)) = stream.get(at) else {
        return Err(violation(
            StackLimitViolationKind::CheckShape,
            "the check ends before its B.LO",
        ));
    };
    if inst.opcode != AArch64Opcode::BCond {
        return Err(violation(
            StackLimitViolationKind::CheckShape,
            format!("expected B.LO, found {:?} {:?}", inst.opcode, inst.operands),
        ));
    }
    if inst.operands.first() != Some(&MachOperand::Imm(COND_LO)) {
        return Err(violation(
            StackLimitViolationKind::CheckShape,
            format!("the check branches on {:?}, not LO", inst.operands.first()),
        ));
    }
    branch_target(layout, *id, inst)
        .filter(|block| (block.0 as usize) < func.blocks.len())
        .ok_or_else(|| {
            violation(
                StackLimitViolationKind::CheckShape,
                "B.LO has no target block",
            )
        })
}

/// Parse a `MOVZ`/`MOVK` chain into X17 starting at `at`; returns the value
/// and the index after it.
fn parse_x17_constant(stream: &[(InstId, &MachInst)], mut at: usize) -> Option<(u64, usize)> {
    let mut value = None;
    while let Some((_, inst)) = stream.get(at) {
        match (inst.opcode, inst.operands.as_slice()) {
            (AArch64Opcode::Movz, [dst, MachOperand::Imm(v)])
                if value.is_none() && is_x_operand(dst, X17_NUM) =>
            {
                value = Some(u64::try_from(*v).ok()? & 0xFFFF);
            }
            (AArch64Opcode::Movk, [dst, MachOperand::Imm(v), MachOperand::Imm(shift)])
                if is_x_operand(dst, X17_NUM) =>
            {
                let shift = u32::try_from(*shift)
                    .ok()
                    .filter(|s| *s < 64 && s % 16 == 0)?;
                let current = value?;
                value = Some(
                    (current & !(0xFFFF << shift)) | ((u64::try_from(*v).ok()? & 0xFFFF) << shift),
                );
            }
            _ => break,
        }
        at += 1;
    }
    value.map(|value| (value, at))
}

/// The real (non-pseudo) instructions of `block`.
fn real_stream(
    func: &MachFunction,
    block: BlockId,
) -> Result<Vec<(InstId, &MachInst)>, StackLimitViolation> {
    let b = func
        .blocks
        .get(block.0 as usize)
        .ok_or_else(|| violation(StackLimitViolationKind::Malformed, format!("no {block:?}")))?;
    let mut stream = Vec::with_capacity(b.insts.len());
    for id in &b.insts {
        let inst = func.insts.get(id.0 as usize).ok_or_else(|| {
            violation(
                StackLimitViolationKind::Malformed,
                format!("dangling {id:?}"),
            )
        })?;
        if !inst.is_pseudo() {
            stream.push((*id, inst));
        }
    }
    Ok(stream)
}

/// The check `B.LO` at `at` must end `block` (optionally followed by an
/// unconditional branch to the fall-through), and `block` must have exactly
/// the overflow block and one continuation as successors. Returns the
/// continuation.
fn check_block_end(
    func: &MachFunction,
    block: BlockId,
    stream: &[(InstId, &MachInst)],
    at: usize,
    overflow: BlockId,
) -> Result<BlockId, StackLimitViolation> {
    let rest = &stream[at + 1..];
    let succs = &func.blocks[block.0 as usize].succs;
    let others: Vec<BlockId> = succs.iter().copied().filter(|s| *s != overflow).collect();
    let [continuation] = others.as_slice() else {
        return Err(violation(
            StackLimitViolationKind::CheckShape,
            format!("the check block {block:?} has successors {succs:?}"),
        ));
    };
    match rest {
        [] => Ok(*continuation),
        [(_, branch)] if branch.opcode == AArch64Opcode::B => Ok(*continuation),
        _ => Err(violation(
            StackLimitViolationKind::CheckShape,
            format!(
                "code follows the check branch in {block:?}: {:?}",
                rest.iter().map(|(_, inst)| inst.opcode).collect::<Vec<_>>()
            ),
        )),
    }
}

/// Check `func`'s stack-limit requirement on its final stream.
///
/// `Ok(None)`: the function requests no limit. `Ok(Some(certificate))`: the
/// check is present and verified, or legitimately elided. `Err`: refused.
pub fn check(func: &MachFunction) -> Result<Option<StackLimitCertificate>, StackLimitViolation> {
    let Some(limit) = &func.stack_limit else {
        return Ok(None);
    };
    check_against(func, limit).map(Some)
}

/// [`check`] against an explicitly supplied requirement (the source LIR's,
/// for custody). The function's own field must equal it.
pub fn check_against(
    func: &MachFunction,
    limit: &MachStackLimit,
) -> Result<StackLimitCertificate, StackLimitViolation> {
    if func.stack_limit.as_ref() != Some(limit) {
        return Err(violation(
            StackLimitViolationKind::CheckShape,
            format!(
                "the function's stack-limit field {:?} differs from the requirement {limit:?}",
                func.stack_limit
            ),
        ));
    }
    let entry = func.entry;
    let Some(entry_block) = func.blocks.get(entry.0 as usize) else {
        return Err(violation(
            StackLimitViolationKind::Malformed,
            "no entry block",
        ));
    };
    let stream: Vec<(InstId, &MachInst)> = entry_block
        .insts
        .iter()
        .map(|id| {
            func.insts
                .get(id.0 as usize)
                .map(|inst| (*id, inst))
                .ok_or_else(|| {
                    violation(
                        StackLimitViolationKind::Malformed,
                        format!("dangling {id:?}"),
                    )
                })
        })
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .filter(|(_, inst)| !inst.is_pseudo())
        .collect();

    // Elision: no stack storage and no non-tail call anywhere.
    if func.stack_limit_overflow_block.is_none() {
        return check_elided(func, limit);
    }

    if !entry_block.preds.is_empty() || func.blocks.iter().any(|block| block.succs.contains(&entry))
    {
        return Err(violation(
            StackLimitViolationKind::PreCheckCode,
            "the entry block is a branch target, so the prologue and check could re-run",
        ));
    }

    // 1. Callee-saved prologue: STP pre-index/offset on SP, then the FP setup.
    let mut state = State::entry();
    let mut deep = Depth { deepest: 0 };
    let mut saved: BTreeMap<i64, PReg> = BTreeMap::new();
    let mut at = 0usize;
    let mut fp_set = false;
    while let Some((_, inst)) = stream.get(at) {
        match (inst.opcode, inst.operands.as_slice()) {
            (AArch64Opcode::StpPreIndex, [r1, r2, base, MachOperand::Imm(amount)])
                if at == 0 && is_sp_operand(base) && *amount < 0 =>
            {
                let (MachOperand::PReg(r1), MachOperand::PReg(r2)) = (r1, r2) else {
                    break;
                };
                state.sp += amount;
                saved.insert(state.sp, *r1);
                saved.insert(state.sp + 8, *r2);
            }
            (AArch64Opcode::StpRI, [r1, r2, base, MachOperand::Imm(offset)])
                if at > 0 && !fp_set && is_sp_operand(base) && *offset > 0 =>
            {
                let (MachOperand::PReg(r1), MachOperand::PReg(r2)) = (r1, r2) else {
                    break;
                };
                let address = state.sp + offset;
                if address + 16 > 0 {
                    return Err(violation(
                        StackLimitViolationKind::PreCheckCode,
                        "a pre-check store lies outside the callee-saved area",
                    ));
                }
                saved.insert(address, *r1);
                saved.insert(address + 8, *r2);
            }
            (AArch64Opcode::AddRI, [dst, src, MachOperand::Imm(k)])
                if at > 0 && !fp_set && is_x_operand(dst, X29_NUM) && is_sp_operand(src) =>
            {
                state.regs.insert(X29_NUM, Val::Frame(state.sp + k));
                fp_set = true;
            }
            _ => break,
        }
        at += 1;
    }
    if !fp_set || state.sp >= 0 {
        return Err(violation(
            StackLimitViolationKind::PreCheckCode,
            format!(
                "the check is not preceded by exactly the callee-saved prologue (stopped at {:?})",
                stream
                    .get(at)
                    .map(|(_, inst)| (inst.opcode, &inst.operands))
            ),
        ));
    }
    deep.reach(state.sp);
    let csa = u32::try_from(-state.sp).map_err(|_| {
        violation(
            StackLimitViolationKind::PreCheckCode,
            "callee-saved area overflows",
        )
    })?;

    // 2. The compare sequence. Frame insertion ends a block after each
    // check `B.LO`, so the sequence runs through the entry block and, for a
    // nonzero `F`, one more block whose only predecessor is the entry.
    let layout = layout(func);
    let mut check_insts = Vec::new();
    let limit_value = match limit.request.source {
        StackLimitSource::Value => limit.limit_reg,
        StackLimitSource::Pointee { offset } => {
            let Some((id, inst)) = stream.get(at) else {
                return Err(violation(
                    StackLimitViolationKind::CheckShape,
                    "no limit load",
                ));
            };
            let base_ok = match (inst.opcode, inst.operands.as_slice()) {
                (AArch64Opcode::LdrRI, [dst, base, MachOperand::Imm(off)]) => {
                    is_x_operand(dst, X17_NUM)
                        && matches!(base, MachOperand::PReg(p) if *p == limit.limit_reg)
                        && *off == i64::from(offset)
                }
                (AArch64Opcode::LdrRI, [dst, MachOperand::MemOp { base, offset: off }]) => {
                    is_x_operand(dst, X17_NUM)
                        && *base == limit.limit_reg
                        && *off == i64::from(offset)
                }
                _ => false,
            };
            if !base_ok {
                return Err(violation(
                    StackLimitViolationKind::CheckShape,
                    format!(
                        "expected LDR X17, [{:?}, #{offset}], found {:?} {:?}",
                        limit.limit_reg, inst.opcode, inst.operands
                    ),
                ));
            }
            check_insts.push(*id);
            at += 1;
            trust_cg_ir::aarch64_regs::X17
        }
    };
    let Some((subs_id, subs)) = stream.get(at) else {
        return Err(violation(
            StackLimitViolationKind::CheckShape,
            "no SUBS from SP",
        ));
    };
    let wide = match (subs.opcode, subs.operands.as_slice()) {
        (AArch64Opcode::SubsRR, [dst, src, rhs])
            if is_sp_operand(src) && matches!(rhs, MachOperand::PReg(p) if *p == limit_value) =>
        {
            if is_x_operand(dst, X16_NUM) {
                true
            } else if is_xzr_operand(dst) {
                false
            } else {
                return Err(violation(
                    StackLimitViolationKind::CheckShape,
                    format!("SUBS from SP writes {dst:?}, not X16 or XZR"),
                ));
            }
        }
        _ => {
            return Err(violation(
                StackLimitViolationKind::CheckShape,
                format!(
                    "expected SUBS X16|XZR, SP, {limit_value:?}, found {:?} {:?}",
                    subs.opcode, subs.operands
                ),
            ));
        }
    };
    check_insts.push(*subs_id);
    at += 1;
    let overflow = expect_lo_branch(func, &layout, &stream, at)?;
    check_insts.push(stream[at].0);
    let mut continuation = check_block_end(func, entry, &stream, at, overflow)?;
    let mut sp_adj = 0u64;
    if wide {
        let second_block = continuation;
        let preds = &func.blocks[second_block.0 as usize].preds;
        if preds.as_slice() != [entry]
            || func
                .blocks
                .iter()
                .enumerate()
                .any(|(index, b)| index != entry.0 as usize && b.succs.contains(&second_block))
        {
            return Err(violation(
                StackLimitViolationKind::CheckShape,
                "the second half of the check is reachable from outside the check",
            ));
        }
        let second = real_stream(func, second_block)?;
        let mut at = 0usize;
        let (cmp_id, cmp) = second
            .get(at)
            .ok_or_else(|| violation(StackLimitViolationKind::CheckShape, "no frame compare"))?;
        match (cmp.opcode, cmp.operands.as_slice()) {
            (AArch64Opcode::CmpRI, [lhs, MachOperand::Imm(f)]) if is_x_operand(lhs, X16_NUM) => {
                sp_adj = u64::try_from(*f).map_err(|_| {
                    violation(
                        StackLimitViolationKind::CheckShape,
                        "negative frame compare",
                    )
                })?;
                check_insts.push(*cmp_id);
                at += 1;
            }
            _ => {
                let (value, next) = parse_x17_constant(&second, at).ok_or_else(|| {
                    violation(
                        StackLimitViolationKind::CheckShape,
                        format!(
                            "expected CMP X16, #F or a constant into X17, found {:?} {:?}",
                            cmp.opcode, cmp.operands
                        ),
                    )
                })?;
                check_insts.extend(second[at..next].iter().map(|(id, _)| *id));
                at = next;
                let (cmp_id, cmp) = second.get(at).ok_or_else(|| {
                    violation(StackLimitViolationKind::CheckShape, "no CMP X16, X17")
                })?;
                if !(cmp.opcode == AArch64Opcode::CmpRR
                    && cmp.operands.len() == 2
                    && is_x_operand(&cmp.operands[0], X16_NUM)
                    && is_x_operand(&cmp.operands[1], X17_NUM))
                {
                    return Err(violation(
                        StackLimitViolationKind::CheckShape,
                        format!(
                            "expected CMP X16, X17, found {:?} {:?}",
                            cmp.opcode, cmp.operands
                        ),
                    ));
                }
                sp_adj = value;
                check_insts.push(*cmp_id);
                at += 1;
            }
        }
        if sp_adj == 0 {
            return Err(violation(
                StackLimitViolationKind::CheckShape,
                "a zero frame compare is the narrow form",
            ));
        }
        let second_target = expect_lo_branch(func, &layout, &second, at)?;
        if second_target != overflow {
            return Err(violation(
                StackLimitViolationKind::CheckShape,
                format!("the two B.LO target {overflow:?} and {second_target:?}"),
            ));
        }
        check_insts.push(second[at].0);
        continuation = check_block_end(func, second_block, &second, at, overflow)?;
    }
    if func.stack_limit_overflow_block != Some(overflow) {
        return Err(violation(
            StackLimitViolationKind::CheckShape,
            format!(
                "the check branches to {overflow:?}, not the recorded overflow block {:?}",
                func.stack_limit_overflow_block
            ),
        ));
    }
    let sp_adj = u32::try_from(sp_adj).map_err(|_| {
        violation(
            StackLimitViolationKind::CheckShape,
            "frame compare exceeds 4 GiB",
        )
    })?;
    let total = csa
        .checked_add(sp_adj)
        .ok_or_else(|| violation(StackLimitViolationKind::CheckShape, "total overflows"))?;

    // 3-4. Everything after the check is reached only through its pass
    // edge: the entry has no predecessor and the check's blocks only their
    // fall-through, so the pass edge dominates the rest of the function.
    // Model it from the state after the CSA (the check writes only X16/X17
    // and NZCV, none of which the model tracks as a frame address).
    let mut after_check = State {
        sp: state.sp,
        regs: state.regs.clone(),
    };
    after_check.regs.remove(&X16_NUM);
    after_check.regs.remove(&X17_NUM);
    let mut sub = Depth { deepest: 0 };
    model_depth(
        func,
        &layout,
        continuation,
        after_check,
        Some(overflow),
        &mut sub,
    )?;
    deep.reach(sub.deepest);
    let deepest = u32::try_from(-deep.deepest)
        .map_err(|_| violation(StackLimitViolationKind::FrameDepth, "depth overflows"))?;
    if deepest > total {
        return Err(violation(
            StackLimitViolationKind::FrameDepth,
            format!(
                "the function reaches {deepest} bytes below its entry SP, past the checked total {total}"
            ),
        ));
    }

    // 5. The overflow block.
    let check_blocks: Vec<BlockId> = if wide {
        let second = func.blocks[entry.0 as usize]
            .succs
            .iter()
            .copied()
            .find(|s| *s != overflow)
            .unwrap_or(entry);
        vec![entry, second]
    } else {
        vec![entry]
    };
    check_overflow_block(func, limit, overflow, &check_blocks, &saved, state.sp)?;

    Ok(StackLimitCertificate {
        function: func.name.clone(),
        outcome: StackLimitOutcome::Checked(CheckedStackLimit {
            csa,
            sp_adj,
            total,
            deepest,
            limit_reg: limit.limit_reg,
            source: limit.request.source,
            overflow: limit.request.overflow.clone(),
            check_insts,
            overflow_block: overflow,
        }),
    })
}

fn check_elided(
    func: &MachFunction,
    _limit: &MachStackLimit,
) -> Result<StackLimitCertificate, StackLimitViolation> {
    for block in &func.blocks {
        for id in &block.insts {
            let inst = func.insts.get(id.0 as usize).ok_or_else(|| {
                violation(
                    StackLimitViolationKind::Malformed,
                    format!("dangling {id:?}"),
                )
            })?;
            if inst.is_pseudo() {
                continue;
            }
            let frame = inst
                .operands
                .iter()
                .any(|op| is_sp_operand(op) || is_x_operand(op, X29_NUM))
                || matches!(decode_memory(inst), Mem::Access(ref a) if a.base == Base::Sp || a.base == Base::Reg(X29_NUM));
            if frame || is_non_tail_call(inst) {
                return Err(violation(
                    StackLimitViolationKind::CheckShape,
                    format!(
                        "no check was emitted, but {:?} {:?} uses the stack or calls",
                        inst.opcode, inst.operands
                    ),
                ));
            }
        }
    }
    Ok(StackLimitCertificate {
        function: func.name.clone(),
        outcome: StackLimitOutcome::Elided,
    })
}

fn check_overflow_block(
    func: &MachFunction,
    limit: &MachStackLimit,
    overflow: BlockId,
    check_blocks: &[BlockId],
    saved: &BTreeMap<i64, PReg>,
    csa_sp: i64,
) -> Result<(), StackLimitViolation> {
    let block = &func.blocks[overflow.0 as usize];
    if !block.succs.is_empty() {
        return Err(violation(
            StackLimitViolationKind::OverflowPath,
            "the overflow block has successors",
        ));
    }
    if block.preds.iter().any(|pred| !check_blocks.contains(pred))
        || func.blocks.iter().enumerate().any(|(index, b)| {
            !check_blocks.contains(&BlockId(index as u32)) && b.succs.contains(&overflow)
        })
    {
        return Err(violation(
            StackLimitViolationKind::OverflowPath,
            "the overflow block is reachable from outside the check",
        ));
    }
    let insts: Vec<&MachInst> = block
        .insts
        .iter()
        .map(|id| func.insts.get(id.0 as usize))
        .collect::<Option<Vec<_>>>()
        .ok_or_else(|| violation(StackLimitViolationKind::Malformed, "dangling overflow inst"))?
        .into_iter()
        .filter(|inst| !inst.is_pseudo())
        .collect();
    match &limit.request.overflow {
        StackLimitOverflow::Trap => {
            let [brk] = insts.as_slice() else {
                return Err(violation(
                    StackLimitViolationKind::OverflowPath,
                    "a Trap overflow block is exactly one BRK",
                ));
            };
            if brk.opcode != AArch64Opcode::Brk
                || brk.operands != [MachOperand::Imm(i64::from(STACK_LIMIT_TRAP_IMM))]
            {
                return Err(violation(
                    StackLimitViolationKind::OverflowPath,
                    format!(
                        "expected BRK #{STACK_LIMIT_TRAP_IMM:#x}, found {:?} {:?}",
                        brk.opcode, brk.operands
                    ),
                ));
            }
            Ok(())
        }
        StackLimitOverflow::Handler { symbol } => {
            let Some((tail, restore)) = insts.split_last() else {
                return Err(violation(
                    StackLimitViolationKind::OverflowPath,
                    "empty overflow block",
                ));
            };
            if tail.opcode != AArch64Opcode::TailCall
                || tail.operands != [MachOperand::Symbol(symbol.clone())]
            {
                return Err(violation(
                    StackLimitViolationKind::OverflowPath,
                    format!(
                        "the overflow block must end in TailCall {symbol}, found {:?} {:?}",
                        tail.opcode, tail.operands
                    ),
                ));
            }
            let mut sp = csa_sp;
            let mut restored: BTreeMap<i64, PReg> = BTreeMap::new();
            for inst in restore {
                let Mem::Access(access) = decode_memory(inst) else {
                    return Err(violation(
                        StackLimitViolationKind::OverflowPath,
                        format!(
                            "{:?} {:?} is not a callee-saved restore",
                            inst.opcode, inst.operands
                        ),
                    ));
                };
                if !access.is_load || access.base != Base::Sp || access.data.len() != 2 {
                    return Err(violation(
                        StackLimitViolationKind::OverflowPath,
                        format!(
                            "{:?} {:?} stores or is not an SP pair load",
                            inst.opcode, inst.operands
                        ),
                    ));
                }
                let address = sp + access.disp;
                restored.insert(address, access.data[0]);
                restored.insert(address + 8, access.data[1]);
                if let Some(amount) = access.writeback {
                    if amount <= 0 {
                        return Err(violation(
                            StackLimitViolationKind::OverflowPath,
                            "the overflow path lowers SP",
                        ));
                    }
                    sp += amount;
                }
            }
            if sp != 0 {
                return Err(violation(
                    StackLimitViolationKind::OverflowPath,
                    format!("the overflow path leaves SP at CFA{sp:+}, not at its entry value"),
                ));
            }
            if &restored != saved {
                return Err(violation(
                    StackLimitViolationKind::OverflowPath,
                    format!(
                        "the overflow path restores {restored:?}, the prologue saved {saved:?}"
                    ),
                ));
            }
            Ok(())
        }
    }
}

// ---------------------------------------------------------------------------
// Module reserve bound (§5)
// ---------------------------------------------------------------------------

/// A function's role in the module bound.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StackRole {
    /// A requester whose check is present: `csa` bytes precede it and
    /// `handler` (if any) runs on overflow.
    Checked {
        /// Callee-saved bytes before the check.
        csa: u32,
        /// The overflow handler's symbol (`None` for `Trap`).
        handler: Option<String>,
    },
    /// A requester whose check was elided (no frame).
    Elided,
    /// Any other function.
    Plain,
}

/// The stack facts of one emitted function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionStackFacts {
    /// Symbol.
    pub name: String,
    /// Role.
    pub role: StackRole,
    /// Deepest CFA offset of its own frame ([`frame_depth`]); `None` when
    /// it cannot be modeled.
    pub frame: Option<u32>,
    /// Direct callee symbols (calls and tail calls).
    pub direct_callees: BTreeSet<String>,
    /// Whether it makes an indirect call.
    pub indirect_call: bool,
}

/// Collect [`FunctionStackFacts`] from a final function and its
/// certificate (when it requested a limit).
pub fn function_stack_facts(
    func: &MachFunction,
    certificate: Option<&StackLimitCertificate>,
) -> FunctionStackFacts {
    let role = match certificate.map(|c| &c.outcome) {
        Some(StackLimitOutcome::Checked(checked)) => StackRole::Checked {
            csa: checked.csa,
            handler: match &checked.overflow {
                StackLimitOverflow::Handler { symbol } => Some(symbol.clone()),
                StackLimitOverflow::Trap => None,
            },
        },
        Some(StackLimitOutcome::Elided) => StackRole::Elided,
        None => StackRole::Plain,
    };
    let mut direct_callees = BTreeSet::new();
    let mut indirect_call = false;
    for block in &func.blocks {
        for id in &block.insts {
            let Some(inst) = func.insts.get(id.0 as usize) else {
                continue;
            };
            if !is_call(inst) {
                continue;
            }
            match inst.operands.first() {
                Some(MachOperand::Symbol(symbol)) => {
                    direct_callees.insert(symbol.clone());
                }
                _ if inst.opcode == AArch64Opcode::TailCall => {
                    // A resolved in-function tail branch is a self call.
                    direct_callees.insert(func.name.clone());
                }
                _ if matches!(
                    inst.opcode,
                    AArch64Opcode::TlsDescCall | AArch64Opcode::BlrTlsdesc
                ) =>
                {
                    // The TLS resolver is external runtime code.
                    direct_callees.insert(String::from("<tlsdesc>"));
                }
                _ => indirect_call = true,
            }
        }
    }
    FunctionStackFacts {
        name: func.name.clone(),
        role,
        frame: frame_depth(func).ok(),
        direct_callees,
        indirect_call,
    }
}

/// The module bound R of §5: the most bytes the stack can reach below the
/// limit between two consecutive checks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackLimitModuleBound {
    /// The declared allowance for any call that leaves the module (runtime
    /// imports, libc, the TLS resolver): an assumption, not computed.
    pub external_allowance: u64,
    /// `Some(R)`, or `None` when unbounded (see `unbounded_reason`).
    pub reserve: Option<u64>,
    /// Why R is unbounded: a call cycle among unchecked functions, or a
    /// frame the model cannot bound.
    pub unbounded_reason: Option<String>,
}

/// Compute R over the module's emitted functions. Only meaningful when at
/// least one function requested a limit.
pub fn module_bound(
    functions: &[FunctionStackFacts],
    external_allowance: u64,
) -> StackLimitModuleBound {
    let index: BTreeMap<&str, usize> = functions
        .iter()
        .enumerate()
        .map(|(i, f)| (f.name.as_str(), i))
        .collect();
    let mut memo: Vec<Option<u64>> = vec![None; functions.len()];
    let mut on_stack = vec![false; functions.len()];
    let mut solver = BoundSolver {
        functions,
        index: &index,
        memo: &mut memo,
        on_stack: &mut on_stack,
        external_allowance,
    };
    let mut reserve = 0u64;
    for (i, f) in functions.iter().enumerate() {
        let bound = match &f.role {
            StackRole::Checked { .. } => solver
                .d(i)
                .and_then(|own| Ok(own.max(solver.callees_max(i)?))),
            StackRole::Elided => solver.d(i),
            StackRole::Plain => continue,
        };
        match bound {
            Ok(bound) => reserve = reserve.max(bound),
            Err(reason) => {
                return StackLimitModuleBound {
                    external_allowance,
                    reserve: None,
                    unbounded_reason: Some(reason),
                };
            }
        }
    }
    StackLimitModuleBound {
        external_allowance,
        reserve: Some(reserve),
        unbounded_reason: None,
    }
}

struct BoundSolver<'a> {
    functions: &'a [FunctionStackFacts],
    index: &'a BTreeMap<&'a str, usize>,
    memo: &'a mut Vec<Option<u64>>,
    on_stack: &'a mut Vec<bool>,
    external_allowance: u64,
}

impl BoundSolver<'_> {
    /// `D(f)`: bytes below `f`'s entry SP reachable before the next check.
    fn d(&mut self, i: usize) -> Result<u64, String> {
        if let Some(value) = self.memo[i] {
            return Ok(value);
        }
        let f = &self.functions[i];
        if let StackRole::Checked { csa, handler } = &f.role {
            let handler_bytes = match handler {
                None => 0,
                Some(symbol) => match self.index.get(symbol.as_str()) {
                    Some(&h) => self.d(h)?,
                    None => self.external_allowance,
                },
            };
            let value = u64::from(*csa).max(handler_bytes);
            self.memo[i] = Some(value);
            return Ok(value);
        }
        if self.on_stack[i] {
            return Err(format!(
                "the call graph has a cycle through unchecked function `{}`",
                f.name
            ));
        }
        let frame = f
            .frame
            .ok_or_else(|| format!("the frame of `{}` cannot be bounded", f.name))?;
        self.on_stack[i] = true;
        let callees = self.callees_max(i);
        self.on_stack[i] = false;
        let value = u64::from(frame) + callees?;
        self.memo[i] = Some(value);
        Ok(value)
    }

    /// The most any callee of `f` can reach below `f`'s call SP.
    fn callees_max(&mut self, i: usize) -> Result<u64, String> {
        let f = &self.functions[i];
        let mut most = 0u64;
        let callees: Vec<String> = f.direct_callees.iter().cloned().collect();
        for callee in &callees {
            let bytes = match self.index.get(callee.as_str()) {
                Some(&c) => self.d(c)?,
                None => self.external_allowance,
            };
            most = most.max(bytes);
        }
        if self.functions[i].indirect_call {
            // v1 counts every emitted function as a possible indirect
            // target, plus anything outside the module.
            most = most.max(self.external_allowance);
            for c in 0..self.functions.len() {
                most = most.max(self.d(c)?);
            }
        }
        Ok(most)
    }
}

/// The 64-bit check lemma, evaluated directly: the compare sequence branches
/// (`(P <u L) ∨ (P − L <u F)`) exactly when `P <ℤ L + F`.
pub fn lemma_branches(p: u64, l: u64, f: u64) -> bool {
    p < l || p.wrapping_sub(l) < f
}

/// The lemma's reference side: `P <ℤ L + F`, computed without wrap.
pub fn lemma_reference(p: u64, l: u64, f: u64) -> bool {
    u128::from(p) < u128::from(l) + u128::from(f)
}

/// The 64-bit check lemma as one QF_BV obligation for the solver lane:
/// for every 64-bit `P`, `L` and `F`, the compare sequence's branch condition
/// `(P <u L) ∨ (P − L <u F)` equals `P <ℤ L + F`. The reference side states
/// `P <ℤ L + F` on 64 bits without wrap: `L + F` carries out (then every
/// 64-bit `P` is below it) or `P <u L + F`. Each side is a one-bit verdict.
///
/// Evidence class: `Solver discharge` only when AY answers and Clean checks
/// the proof (`ay_bridge::verify_with_ay` returning `Verified`); the
/// in-process exhaustive (8-bit) and sampled (64-bit) tests of this module
/// are tests, never this proof.
pub fn lemma_obligation() -> crate::lowering_proof::ProofObligation {
    use crate::smt::SmtExpr;
    let p = SmtExpr::var("p", 64);
    let l = SmtExpr::var("l", 64);
    let f = SmtExpr::var("f", 64);
    let one = || SmtExpr::bv_const(1, 1);
    let zero = || SmtExpr::bv_const(0, 1);
    let sum = l.clone().bvadd(f.clone());
    let reference = SmtExpr::ite(
        sum.clone().bvult(l.clone()).or_expr(p.clone().bvult(sum)),
        one(),
        zero(),
    );
    let branches = SmtExpr::ite(
        p.clone().bvult(l.clone()).or_expr(p.bvsub(l).bvult(f)),
        one(),
        zero(),
    );
    crate::lowering_proof::ProofObligation {
        name: "U10 stack-limit check lemma (64-bit)".to_string(),
        trust_ir_expr: reference,
        aarch64_expr: branches,
        inputs: vec![
            ("p".to_string(), 64),
            ("l".to_string(), 64),
            ("f".to_string(), 64),
        ],
        preconditions: Vec::new(),
        fp_inputs: Vec::new(),
        category: Some(crate::lowering_proof::TransvalCheckKind::ControlFlow),
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
    }
}

#[cfg(test)]
mod tests;
