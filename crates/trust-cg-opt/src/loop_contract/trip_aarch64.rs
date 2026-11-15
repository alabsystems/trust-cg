// trust-cg-opt - AArch64 MachIR as the iteration-coverage clause reads it
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! [`TripEffect`]s of one AArch64 [`MachInst`] (pre-register-allocation
//! form). Each modeled opcode is described with the operand layout the
//! AArch64 encoder (`trust-cg-codegen/src/aarch64/encode.rs`) gives it; a
//! W-form instruction (a `Gpr32` destination, or the typed `MOVWrr` whatever
//! its registers' class) computes at 32 bits and zero-extends, as the
//! hardware does. A falls-through trap pseudo is the test its expansion
//! (`trust-cg-codegen/src/lower.rs`, `expand_trap_*`) emits, or a trap on a
//! condition the model does not compute ([`TripCond::Unknown`]). Anything else
//! writes unknown values to every register the shared operand-role model says
//! it defines, and unknown flags when it writes them; an unmodeled transfer is
//! [`TripEffect::Opaque`].

use trust_cg_ir::{
    AArch64Opcode, BlockId, MachFunction, MachInst, MachOperand, OverflowOp, RegClass, VReg,
    unpack_overflow_tag,
};

use super::coverage::{
    FlagOp, SelectPost, StopKind, TripBin, TripCond, TripEffect, TripOp, TripOperand, UnknownTest,
};
use crate::effects::{for_each_inst_def, writes_flags};

fn gpr_width(vreg: VReg) -> Option<u8> {
    match vreg.class {
        RegClass::Gpr32 => Some(32),
        RegClass::Gpr64 => Some(64),
        _ => None,
    }
}

fn vreg_at(inst: &MachInst, position: usize) -> Option<VReg> {
    match inst.operands.get(position)? {
        MachOperand::VReg(vreg) => Some(*vreg),
        _ => None,
    }
}

fn imm_at(inst: &MachInst, position: usize) -> Option<i64> {
    match inst.operands.get(position)? {
        MachOperand::Imm(value) => Some(*value),
        _ => None,
    }
}

fn block_at(inst: &MachInst, position: usize) -> Option<BlockId> {
    match inst.operands.get(position)? {
        MachOperand::Block(block) => Some(*block),
        _ => None,
    }
}

/// A GPR or immediate source operand, read at `width` bits.
fn source(inst: &MachInst, position: usize, width: u8) -> Option<TripOperand> {
    match inst.operands.get(position)? {
        MachOperand::VReg(vreg) => {
            gpr_width(*vreg)?;
            Some(TripOperand::Reg { id: vreg.id, width })
        }
        MachOperand::Imm(value) => Some(TripOperand::Imm(*value as u64)),
        _ => None,
    }
}

/// The modeled effects of a value-producing ALU instruction, or `None` when
/// its form is not modeled.
fn alu(inst: &MachInst) -> Option<(VReg, u8, TripOp)> {
    use AArch64Opcode::*;
    let dst = vreg_at(inst, 0)?;
    let width = gpr_width(dst)?;
    let n = inst.operands.len();
    let src = |position: usize| source(inst, position, width);
    let bin = |op: TripBin| -> Option<TripOp> {
        (n == 3).then_some(())?;
        Some(TripOp::Bin(op, src(1)?, src(2)?))
    };
    let shifted = |op: TripBin, shift: TripBin| -> Option<TripOp> {
        (n == 4).then_some(())?;
        let amount = imm_at(inst, 3)?;
        if !(1..i64::from(width)).contains(&amount) {
            return None;
        }
        Some(TripOp::BinShifted {
            op,
            a: src(1)?,
            b: src(2)?,
            shift,
            amount: amount as u8,
        })
    };
    let op = match inst.opcode {
        MovR | Copy => {
            (n == 2).then_some(())?;
            TripOp::Copy(src(1)?)
        }
        // The typed opcode, not the registers' class, owns the width
        // (`encode.rs`: MOVWrr is `sf = 0`, MOVXrr `sf = 1`); regalloc keeps
        // MOVWrr over `Gpr64` registers as a 32-bit truncation.
        MOVWrr | MOVXrr => {
            (n == 2).then_some(())?;
            let width = if inst.opcode == MOVWrr { 32 } else { 64 };
            return Some((dst, width, TripOp::Copy(source(inst, 1, width)?)));
        }
        Movz | Movn | Movk | MovI | MOVZWi | MOVZXi => {
            let (parsed, imm, shift) = crate::reaching_const::parse_move_wide_inst(inst)?;
            if parsed != dst {
                return None;
            }
            match inst.opcode {
                Movn => TripOp::Copy(TripOperand::Imm(!(imm << shift))),
                Movk => TripOp::Insert16 {
                    old: TripOperand::Reg { id: dst.id, width },
                    imm: imm as u16,
                    shift: shift as u8,
                },
                _ => TripOp::Copy(TripOperand::Imm(imm << shift)),
            }
        }
        AddRI | AddRR => bin(TripBin::Add)?,
        SubRI | SubRR => bin(TripBin::Sub)?,
        AddRIShift12 => {
            (n == 3).then_some(())?;
            let imm = imm_at(inst, 2)?;
            TripOp::Bin(TripBin::Add, src(1)?, TripOperand::Imm((imm as u64) << 12))
        }
        MulRR => bin(TripBin::Mul)?,
        AndRR | AndRI => bin(TripBin::And)?,
        OrrRR | OrrRI => bin(TripBin::Or)?,
        EorRR | EorRI => bin(TripBin::Xor)?,
        BicRR => bin(TripBin::AndNot)?,
        OrnRR => bin(TripBin::OrNot)?,
        LslRR | LslRI => bin(TripBin::Shl)?,
        LsrRR | LsrRI => bin(TripBin::LShr)?,
        AsrRR | AsrRI => bin(TripBin::AShr)?,
        RorRI => bin(TripBin::Ror)?,
        UDiv => bin(TripBin::UDiv)?,
        SDiv => bin(TripBin::SDiv)?,
        AddRRShift => shifted(TripBin::Add, TripBin::Shl)?,
        SubRRShift => shifted(TripBin::Sub, TripBin::Shl)?,
        AddRRShiftLsr => shifted(TripBin::Add, TripBin::LShr)?,
        EorRRLsl => shifted(TripBin::Xor, TripBin::Shl)?,
        EorRRLsr => shifted(TripBin::Xor, TripBin::LShr)?,
        EorRRShift => shifted(TripBin::Xor, TripBin::Ror)?,
        Neg => {
            (n == 2).then_some(())?;
            TripOp::Neg(src(1)?)
        }
        Madd => {
            (n == 4).then_some(())?;
            TripOp::MulAdd(src(1)?, src(2)?, src(3)?)
        }
        Msub => {
            let addend = if n == 4 { src(3)? } else { TripOperand::Imm(0) };
            (n == 3 || n == 4).then_some(())?;
            TripOp::MulSub(src(1)?, src(2)?, addend)
        }
        Sxtw | Uxtw | Sxtb | Sxth | Uxtb | Uxth => {
            (n == 2).then_some(())?;
            let source_vreg = vreg_at(inst, 1)?;
            let source_width = gpr_width(source_vreg)?;
            let (signed, from) = match inst.opcode {
                Sxtw => (true, 32),
                Uxtw => (false, 32),
                Sxtb => (true, 8),
                Sxth => (true, 16),
                Uxtb => (false, 8),
                _ => (false, 16),
            };
            TripOp::Ext {
                signed,
                from,
                src: TripOperand::Reg {
                    id: source_vreg.id,
                    width: source_width,
                },
            }
        }
        CSet => {
            (n == 2).then_some(())?;
            TripOp::SetCond(TripCond::Arm(condition(imm_at(inst, 1)?)?))
        }
        Csel | Csinc | Csinv | Csneg => {
            (n == 4).then_some(())?;
            let post = match inst.opcode {
                Csel => SelectPost::Plain,
                Csinc => SelectPost::Inc,
                Csinv => SelectPost::Inv,
                _ => SelectPost::Neg,
            };
            TripOp::Select {
                cond: TripCond::Arm(condition(imm_at(inst, 3)?)?),
                then: src(1)?,
                otherwise: src(2)?,
                post,
            }
        }
        _ => return None,
    };
    Some((dst, width, op))
}

/// A 4-bit AArch64 condition encoding.
fn condition(cc: i64) -> Option<u8> {
    (0..=15).contains(&cc).then_some(cc as u8)
}

/// The base register a pre/post-indexed transfer advances, and by how much.
fn writeback(inst: &MachInst) -> Option<(usize, i64)> {
    use AArch64Opcode::*;
    match inst.opcode {
        LdrPreIndex | LdrPostIndex | StrPreIndex | StrPostIndex => Some((1, imm_at(inst, 2)?)),
        LdpPostIndex | StpPreIndex | NeonLdpQPost | NeonStpQPost => Some((2, imm_at(inst, 3)?)),
        _ => None,
    }
}

/// Append the effects of `inst` to `out`.
pub(super) fn trip_effects(inst: &MachInst, out: &mut Vec<TripEffect<BlockId>>) {
    use AArch64Opcode::*;
    match inst.opcode {
        Nop | AlignNop => return,
        B => {
            out.push(match block_at(inst, 0) {
                Some(target) if inst.operands.len() == 1 => TripEffect::Jump(target),
                _ => TripEffect::Opaque,
            });
            return;
        }
        BCond | Bcc => {
            let effect = match (imm_at(inst, 0).and_then(condition), block_at(inst, 1)) {
                (Some(cc), Some(target)) if inst.operands.len() == 2 => TripEffect::Branch {
                    cond: TripCond::Arm(cc),
                    target,
                },
                _ => TripEffect::Opaque,
            };
            out.push(effect);
            return;
        }
        Cbz | Cbnz => {
            let effect = match (vreg_at(inst, 0), block_at(inst, 1)) {
                (Some(reg), Some(target)) if inst.operands.len() == 2 => match gpr_width(reg) {
                    Some(width) => {
                        let operand = TripOperand::Reg { id: reg.id, width };
                        let cond = if inst.opcode == Cbz {
                            TripCond::Zero(operand)
                        } else {
                            TripCond::NonZero(operand)
                        };
                        TripEffect::Branch { cond, target }
                    }
                    None => TripEffect::Opaque,
                },
                _ => TripEffect::Opaque,
            };
            out.push(effect);
            return;
        }
        Tbz | Tbnz => {
            let effect = match (vreg_at(inst, 0), imm_at(inst, 1), block_at(inst, 2)) {
                (Some(reg), Some(bit), Some(target))
                    if inst.operands.len() == 3 && (0..64).contains(&bit) =>
                {
                    match gpr_width(reg) {
                        Some(width) => {
                            let operand = TripOperand::Reg { id: reg.id, width };
                            let cond = if inst.opcode == Tbz {
                                TripCond::BitClear(operand, bit as u8)
                            } else {
                                TripCond::BitSet(operand, bit as u8)
                            };
                            TripEffect::Branch { cond, target }
                        }
                        None => TripEffect::Opaque,
                    }
                }
                _ => TripEffect::Opaque,
            };
            out.push(effect);
            return;
        }
        Ret => {
            out.push(TripEffect::Stop(StopKind::Return));
            return;
        }
        TailCall => {
            out.push(TripEffect::Stop(StopKind::TailCall));
            return;
        }
        Br => {
            out.push(TripEffect::Stop(StopKind::IndirectBranch));
            return;
        }
        Brk => {
            out.push(TripEffect::Stop(StopKind::Trap));
            return;
        }
        _ => {}
    }
    if inst.opcode.is_trap_pseudo() {
        if !inst.opcode.is_falls_through_trap_pseudo() {
            // A bare carrier always traps.
            out.push(TripEffect::Stop(StopKind::Trap));
        } else if inst
            .operands
            .iter()
            .any(|operand| matches!(operand, MachOperand::Block(_)))
        {
            out.push(TripEffect::Opaque);
        } else {
            guard(inst, out);
        }
        return;
    }
    if inst
        .operands
        .iter()
        .any(|operand| matches!(operand, MachOperand::Block(_)))
    {
        // Any other instruction that names a block is a transfer this model
        // does not describe.
        out.push(TripEffect::Opaque);
        return;
    }
    match inst.opcode {
        CmpRR | CmpRI | CMPWrr | CMPXrr | CMPWri | CMPXri | Tst => {
            let flag = match inst.opcode {
                Tst => FlagOp::And,
                _ => FlagOp::Sub,
            };
            let modeled = (inst.operands.len() == 2)
                .then(|| {
                    let lhs = vreg_at(inst, 0)?;
                    let width = gpr_width(lhs)?;
                    Some(TripEffect::Flags {
                        op: flag,
                        a: TripOperand::Reg { id: lhs.id, width },
                        b: source(inst, 1, width)?,
                        width,
                    })
                })
                .flatten();
            out.push(modeled.unwrap_or(TripEffect::ClobberFlags));
            return;
        }
        AddsRR | AddsRI | SubsRR | SubsRI => {
            let modeled = (inst.operands.len() == 3)
                .then(|| {
                    let dst = vreg_at(inst, 0)?;
                    let width = gpr_width(dst)?;
                    let (a, b) = (source(inst, 1, width)?, source(inst, 2, width)?);
                    let (bin, flag) = if matches!(inst.opcode, AddsRR | AddsRI) {
                        (TripBin::Add, FlagOp::Add)
                    } else {
                        (TripBin::Sub, FlagOp::Sub)
                    };
                    Some((dst, width, a, b, bin, flag))
                })
                .flatten();
            match modeled {
                Some((dst, width, a, b, bin, flag)) => {
                    out.push(TripEffect::Flags {
                        op: flag,
                        a,
                        b,
                        width,
                    });
                    out.push(TripEffect::Set {
                        dst: dst.id,
                        width,
                        op: TripOp::Bin(bin, a, b),
                    });
                }
                None => {
                    for_each_inst_def(inst, |def| out.push(TripEffect::Clobber(def.id)));
                    out.push(TripEffect::ClobberFlags);
                }
            }
            return;
        }
        _ => {}
    }
    if let Some((dst, width, op)) = alu(inst) {
        out.push(TripEffect::Set {
            dst: dst.id,
            width,
            op,
        });
        // None of the modeled ALU forms writes the flags.
        return;
    }
    // Unmodeled: unknown values in every register it defines, except a
    // pre/post-indexed base it advances by a known immediate.
    let advanced = writeback(inst).and_then(|(position, offset)| {
        let base = vreg_at(inst, position)?;
        (gpr_width(base) == Some(64)).then_some((base, offset))
    });
    for_each_inst_def(inst, |def| {
        if advanced.is_none_or(|(base, _)| base.id != def.id) {
            out.push(TripEffect::Clobber(def.id));
        }
    });
    if let Some((base, offset)) = advanced {
        out.push(TripEffect::Set {
            dst: base.id,
            width: 64,
            op: TripOp::Bin(
                TripBin::Add,
                TripOperand::Reg {
                    id: base.id,
                    width: 64,
                },
                TripOperand::Imm(offset as u64),
            ),
        });
    }
    if writes_flags(inst.opcode) || inst.is_call() {
        out.push(TripEffect::ClobberFlags);
    }
}

/// The effects of a falls-through trap pseudo: the flags its expansion's test
/// writes and a trap when the test fails. A carrier the expansion degrades to
/// an unconditional trap (an operand missing, an overflow tag it cannot
/// decode) always traps. A form whose test the model does not compute
/// clobbers the flags and traps on [`TripCond::Unknown`], naming the two
/// registers the multiply-overflow test reads; the coverage clause admits it
/// only where it stands for such a trap of the scalar loop, and never when
/// its run knows both registers (they are in its trip slice).
fn guard(inst: &MachInst, out: &mut Vec<TripEffect<BlockId>>) {
    use AArch64Opcode::*;
    let degraded = match inst.opcode {
        TrapNullIfZero | TrapDivZeroIfZero => inst.operands.is_empty(),
        TrapBoundsCheckExact => inst.operands.len() < 3,
        TrapShiftRangeIfOOB => inst.operands.len() < 2,
        TrapOverflowExact => match imm_at(inst, 2).and_then(unpack_overflow_tag) {
            Some((op, width)) => op.is_mul() && width != 64,
            None => true,
        },
        _ => false,
    };
    if degraded {
        out.push(TripEffect::Stop(StopKind::Trap));
        return;
    }
    let gpr = |position: usize| -> Option<TripOperand> {
        let reg = vreg_at(inst, position)?;
        Some(TripOperand::Reg {
            id: reg.id,
            width: gpr_width(reg)?,
        })
    };
    // `CMP index, bound; B.LO skip; BRK`: traps iff `index >=u bound`, at
    // the index register's width.
    let unsigned_bound = |index_at: usize, bound: TripOperand| -> Option<TripEffect<BlockId>> {
        let index = gpr(index_at)?;
        let TripOperand::Reg { width, .. } = index else {
            return None;
        };
        let bound = match bound {
            TripOperand::Reg { id, .. } => TripOperand::Reg { id, width },
            imm => imm,
        };
        Some(TripEffect::Flags {
            op: FlagOp::Sub,
            a: index,
            b: bound,
            width,
        })
    };
    // `(flags written, trap condition)`; `None`: the test writes no flags.
    let modeled: Option<(Option<TripEffect<BlockId>>, TripCond)> = match inst.opcode {
        // `TrapBoundsCheckExact base, index, bound` (a register or immediate
        // bound).
        TrapBoundsCheckExact => (inst.operands.len() == 3)
            .then(|| {
                Some((
                    Some(unsigned_bound(1, source(inst, 2, 64)?)?),
                    TripCond::Arm(2),
                ))
            })
            .flatten(),
        // `TrapShiftRangeIfOOB amount, #bitwidth` (`CMP amount, #bitwidth`).
        TrapShiftRangeIfOOB => match inst.operands.as_slice() {
            [_, MachOperand::Imm(bitwidth)] => {
                unsigned_bound(0, TripOperand::Imm(*bitwidth as u64))
                    .map(|flags| (Some(flags), TripCond::Arm(2)))
            }
            _ => None,
        },
        // `CBNZ reg, skip; BRK`: traps iff the register is zero.
        TrapNullIfZero | TrapDivZeroIfZero => (inst.operands.len() == 1)
            .then(|| Some((None, TripCond::Zero(gpr(0)?))))
            .flatten(),
        // `ADDS/SUBS ZR, lhs, rhs` at the tag's width, then the trap on
        // overflow: V for the signed ops, carry for an unsigned add, borrow
        // for an unsigned subtract. The multiply form's high-half test is not
        // modeled.
        TrapOverflowExact => (inst.operands.len() == 3)
            .then(|| {
                let (op, width) = unpack_overflow_tag(imm_at(inst, 2)?)?;
                let width = u8::try_from(width).ok()?;
                let (flag, cc) = match op {
                    OverflowOp::SignedAdd => (FlagOp::Add, 6),
                    OverflowOp::SignedSub => (FlagOp::Sub, 6),
                    OverflowOp::UnsignedAdd => (FlagOp::Add, 2),
                    OverflowOp::UnsignedSub => (FlagOp::Sub, 3),
                    OverflowOp::SignedMul | OverflowOp::UnsignedMul => return None,
                };
                gpr(0)?;
                gpr(1)?;
                let flags = TripEffect::Flags {
                    op: flag,
                    a: source(inst, 0, width)?,
                    b: source(inst, 1, width)?,
                    width,
                };
                Some((Some(flags), TripCond::Arm(cc)))
            })
            .flatten(),
        _ => None,
    };
    match modeled {
        Some((flags, cond)) => {
            out.extend(flags);
            out.push(TripEffect::StopIf(cond));
        }
        None => {
            // `TrapOverflowExact a, b, <mul at 64>`: `UMULH`/`SMULH` of the
            // two 64-bit registers, a function of their values only. Any
            // other form here names what it reads in no way the model knows.
            let reads = match (inst.opcode, inst.operands.as_slice()) {
                (TrapOverflowExact, [_, _, _]) => match (gpr(0), gpr(1)) {
                    (
                        Some(TripOperand::Reg { id: a, width: 64 }),
                        Some(TripOperand::Reg { id: b, width: 64 }),
                    ) => UnknownTest::Reads([
                        Some(TripOperand::Reg { id: a, width: 64 }),
                        Some(TripOperand::Reg { id: b, width: 64 }),
                    ]),
                    _ => UnknownTest::Unnamed,
                },
                _ => UnknownTest::Unnamed,
            };
            out.push(TripEffect::ClobberFlags);
            out.push(TripEffect::StopIf(TripCond::Unknown(reads)));
        }
    }
}

/// [`trip_effects`] for instruction `index` of `block`.
pub(super) fn block_trip_effects(
    func: &MachFunction,
    block: BlockId,
    index: usize,
    out: &mut Vec<TripEffect<BlockId>>,
) {
    trip_effects(func.inst(func.block(block).insts[index]), out);
}
