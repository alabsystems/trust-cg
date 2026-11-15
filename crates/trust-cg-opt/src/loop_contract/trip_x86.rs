// trust-cg-opt - x86-64 ISel functions as the iteration-coverage clause reads them
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! [`TripEffect`]s of one x86-64 [`X86ISelInst`] (pre-register-allocation
//! form). Each modeled form follows the operand layout the instruction
//! selector emits and the width the x86-64 encoder
//! (`trust-cg-codegen/src/x86_64/encode.rs`) gives it: a register-register
//! ALU op is 32-bit only when both registers are `Gpr32`, a register-immediate
//! one when its destination is; `CmpRI8`, `TestRI`, the extensions and `LEA`
//! are 64-bit; a 32-bit write zero-extends, as the hardware does, and `SETcc`
//! writes only the low byte. Two-operand ALU forms are tied (`[d, s]` is `d =
//! d OP s`, the shared `x86_dce` rule). Anything else writes unknown values to
//! every register the shared x86 def model says it may define, and unknown
//! flags when it writes them; a guard carrier other than the bounds check is
//! a trap on [`TripCond::Unknown`]; an unmodeled transfer is
//! [`TripEffect::Opaque`].

use trust_cg_ir::regs::RegClass;
use trust_cg_ir::{VReg, X86Opcode};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelInst, X86ISelOperand};

use super::coverage::{
    FlagOp, SelectPost, StopKind, TripBin, TripCond, TripEffect, TripOp, TripOperand, UnknownTest,
};
use crate::effects::{FlagOverwrite, condition_flag_overwrite, x86_may_defined_vregs};

fn gpr_width(vreg: VReg) -> Option<u8> {
    match vreg.class {
        RegClass::Gpr32 => Some(32),
        RegClass::Gpr64 => Some(64),
        _ => None,
    }
}

fn gpr_at(inst: &X86ISelInst, position: usize) -> Option<VReg> {
    match inst.operands.get(position)? {
        X86ISelOperand::VReg(vreg) if gpr_width(*vreg).is_some() => Some(*vreg),
        _ => None,
    }
}

fn imm_at(inst: &X86ISelInst, position: usize) -> Option<i64> {
    match inst.operands.get(position)? {
        X86ISelOperand::Imm(value) => Some(*value),
        _ => None,
    }
}

fn reg(vreg: VReg, width: u8) -> TripOperand {
    TripOperand::Reg { id: vreg.id, width }
}

/// `[d, s]` (tied) or `[d, a, b]` register-register ALU: `(d, a, b, width)`.
fn rr(inst: &X86ISelInst) -> Option<(VReg, TripOperand, TripOperand, u8)> {
    match inst.operands.len() {
        2 => {
            let (d, s) = (gpr_at(inst, 0)?, gpr_at(inst, 1)?);
            let width = if d.class == RegClass::Gpr32 && s.class == RegClass::Gpr32 {
                32
            } else {
                64
            };
            Some((d, reg(d, width), reg(s, width), width))
        }
        3 => {
            let (d, a, b) = (gpr_at(inst, 0)?, gpr_at(inst, 1)?, gpr_at(inst, 2)?);
            let width = if [d, a, b].iter().all(|v| v.class == RegClass::Gpr32) {
                32
            } else {
                64
            };
            Some((d, reg(a, width), reg(b, width), width))
        }
        _ => None,
    }
}

/// `[d, imm]` (tied) or `[d, s, imm]` register-immediate ALU.
fn ri(inst: &X86ISelInst) -> Option<(VReg, TripOperand, TripOperand, u8)> {
    let d = gpr_at(inst, 0)?;
    let width = gpr_width(d)?;
    match inst.operands.len() {
        2 => Some((
            d,
            reg(d, width),
            TripOperand::Imm(imm_at(inst, 1)? as u64),
            width,
        )),
        3 => Some((
            d,
            reg(gpr_at(inst, 1)?, width),
            TripOperand::Imm(imm_at(inst, 2)? as u64),
            width,
        )),
        _ => None,
    }
}

fn block_at(inst: &X86ISelInst, position: usize) -> Option<Block> {
    match inst.operands.get(position)? {
        X86ISelOperand::Block(block) => Some(*block),
        _ => None,
    }
}

fn names_block(inst: &X86ISelInst) -> bool {
    inst.operands
        .iter()
        .any(|operand| matches!(operand, X86ISelOperand::Block(_)))
}

/// Append the effects of `inst` to `out`.
pub(super) fn trip_effects(inst: &X86ISelInst, out: &mut Vec<TripEffect<Block>>) {
    use X86Opcode::*;
    match inst.opcode {
        Nop | NopMulti => return,
        Jmp => {
            out.push(match (block_at(inst, 0), inst.operands.len()) {
                (Some(target), 1) => TripEffect::Jump(target),
                _ => TripEffect::Opaque,
            });
            return;
        }
        Jcc => {
            out.push(match inst.operands.as_slice() {
                [X86ISelOperand::CondCode(cc), X86ISelOperand::Block(target)] => {
                    TripEffect::Branch {
                        cond: TripCond::X86(*cc),
                        target: *target,
                    }
                }
                _ => TripEffect::Opaque,
            });
            return;
        }
        Ret => {
            out.push(TripEffect::Stop(StopKind::Return));
            return;
        }
        Ud2 => {
            out.push(TripEffect::Stop(StopKind::Trap));
            return;
        }
        JmpR => {
            out.push(TripEffect::Stop(StopKind::IndirectBranch));
            return;
        }
        TrapBoundsCheckExact => {
            // `CMP index, bound; JAE -> UD2`.
            let modeled = (inst.operands.len() == 3)
                .then(|| {
                    let index = gpr_at(inst, 1)?;
                    let width = gpr_width(index)?;
                    let bound = match inst.operands.get(2)? {
                        X86ISelOperand::VReg(v) if gpr_width(*v).is_some() => reg(*v, width),
                        X86ISelOperand::Imm(value) => TripOperand::Imm(*value as u64),
                        _ => return None,
                    };
                    Some((reg(index, width), bound, width))
                })
                .flatten();
            match modeled {
                Some((a, b, width)) => {
                    out.push(TripEffect::Flags {
                        op: FlagOp::Sub,
                        a,
                        b,
                        width,
                    });
                    out.push(TripEffect::StopIf(TripCond::X86(
                        trust_cg_ir::X86CondCode::AE,
                    )));
                }
                None => {
                    out.push(TripEffect::ClobberFlags);
                    out.push(TripEffect::StopIf(TripCond::Unknown(UnknownTest::Unnamed)));
                }
            }
            return;
        }
        TrapNullIfZeroExact | TrapDivZeroExact | TrapShiftRangeExact => {
            // A guard whose condition is not modeled: a trap on an unknown
            // test of its operands (a GPR or an immediate each, else unnamed),
            // which the coverage clause admits only where it stands for such
            // a trap of the scalar loop, and never when its run knows every
            // operand named (they are in its trip slice); flags clobbered by
            // its expansion.
            let operand = |position: usize| match inst.operands.get(position)? {
                X86ISelOperand::VReg(v) => Some(Some(reg(*v, gpr_width(*v)?))),
                X86ISelOperand::Imm(value) => Some(Some(TripOperand::Imm(*value as u64))),
                _ => None,
            };
            let reads = match inst.operands.len() {
                1 => operand(0).map(|a| [a, None]),
                2 => operand(0).zip(operand(1)).map(|(a, b)| [a, b]),
                _ => None,
            };
            let test = reads.map_or(UnknownTest::Unnamed, UnknownTest::Reads);
            out.push(TripEffect::ClobberFlags);
            out.push(TripEffect::StopIf(TripCond::Unknown(test)));
            return;
        }
        _ => {}
    }
    if names_block(inst) {
        out.push(TripEffect::Opaque);
        return;
    }
    if let Some(effects) = modeled(inst) {
        out.extend(effects);
        return;
    }
    for def in x86_may_defined_vregs(inst) {
        out.push(TripEffect::Clobber(def.id));
    }
    if condition_flag_overwrite(inst) != FlagOverwrite::None || inst.flags.is_call() {
        out.push(TripEffect::ClobberFlags);
    }
}

/// The effects of a modeled form, or `None`.
fn modeled(inst: &X86ISelInst) -> Option<Vec<TripEffect<Block>>> {
    use X86Opcode::*;
    let set = |dst: VReg, width: u8, op: TripOp| TripEffect::Set {
        dst: dst.id,
        width,
        op,
    };
    Some(match inst.opcode {
        MovRR => {
            (inst.operands.len() == 2).then_some(())?;
            let (d, s) = (gpr_at(inst, 0)?, gpr_at(inst, 1)?);
            let width = gpr_width(d)?;
            vec![set(d, width, TripOp::Copy(reg(s, width)))]
        }
        MovRR32 => {
            (inst.operands.len() == 2).then_some(())?;
            let (d, s) = (gpr_at(inst, 0)?, gpr_at(inst, 1)?);
            vec![set(d, 32, TripOp::Copy(reg(s, 32)))]
        }
        MovRI => {
            (inst.operands.len() == 2).then_some(())?;
            let d = gpr_at(inst, 0)?;
            let width = gpr_width(d)?;
            vec![set(
                d,
                width,
                TripOp::Copy(TripOperand::Imm(imm_at(inst, 1)? as u64)),
            )]
        }
        AddRR | SubRR | AddRI | SubRI => {
            let (d, a, b, width) = if matches!(inst.opcode, AddRR | SubRR) {
                rr(inst)?
            } else {
                ri(inst)?
            };
            let (bin, flag) = if matches!(inst.opcode, AddRR | AddRI) {
                (TripBin::Add, FlagOp::Add)
            } else {
                (TripBin::Sub, FlagOp::Sub)
            };
            vec![
                TripEffect::Flags {
                    op: flag,
                    a,
                    b,
                    width,
                },
                set(d, width, TripOp::Bin(bin, a, b)),
            ]
        }
        AndRR | OrRR | XorRR | AndRI | OrRI | XorRI => {
            let (d, a, b, width) = if matches!(inst.opcode, AndRR | OrRR | XorRR) {
                rr(inst)?
            } else {
                ri(inst)?
            };
            let bin = match inst.opcode {
                AndRR | AndRI => TripBin::And,
                OrRR | OrRI => TripBin::Or,
                _ => TripBin::Xor,
            };
            // Logic flags of the result: ZF/SF from it, CF = OF = 0.
            vec![
                set(d, width, TripOp::Bin(bin, a, b)),
                TripEffect::Flags {
                    op: FlagOp::And,
                    a: reg(d, width),
                    b: TripOperand::Imm(u64::MAX),
                    width,
                },
            ]
        }
        ImulRR => {
            let (d, a, b, width) = rr(inst)?;
            vec![
                set(d, width, TripOp::Bin(TripBin::Mul, a, b)),
                TripEffect::ClobberFlags,
            ]
        }
        ImulRRI => {
            (inst.operands.len() == 3).then_some(())?;
            let (d, s) = (gpr_at(inst, 0)?, gpr_at(inst, 1)?);
            let width = if d.class == RegClass::Gpr32 && s.class == RegClass::Gpr32 {
                32
            } else {
                64
            };
            vec![
                set(
                    d,
                    width,
                    TripOp::Bin(
                        TripBin::Mul,
                        reg(s, width),
                        TripOperand::Imm(imm_at(inst, 2)? as u64),
                    ),
                ),
                TripEffect::ClobberFlags,
            ]
        }
        ShlRI | ShrRI | SarRI => {
            let (d, a, b, width) = ri(inst)?;
            let bin = match inst.opcode {
                ShlRI => TripBin::Shl,
                ShrRI => TripBin::LShr,
                _ => TripBin::AShr,
            };
            let mut effects = vec![set(d, width, TripOp::Bin(bin, a, b))];
            if condition_flag_overwrite(inst) != FlagOverwrite::None {
                effects.push(TripEffect::ClobberFlags);
            }
            effects
        }
        Lea => {
            let [
                X86ISelOperand::VReg(d),
                X86ISelOperand::MemAddr { base, disp },
            ] = inst.operands.as_slice()
            else {
                return None;
            };
            gpr_width(*d)?;
            let X86ISelOperand::VReg(base) = base.as_ref() else {
                return None;
            };
            gpr_width(*base)?;
            vec![set(
                *d,
                64,
                TripOp::Bin(
                    TripBin::Add,
                    reg(*base, 64),
                    TripOperand::Imm(*disp as i64 as u64),
                ),
            )]
        }
        LeaSib => {
            let [
                X86ISelOperand::VReg(d),
                X86ISelOperand::SibMemAddr {
                    base,
                    index,
                    scale,
                    disp,
                },
            ] = inst.operands.as_slice()
            else {
                return None;
            };
            gpr_width(*d)?;
            let (X86ISelOperand::VReg(base), X86ISelOperand::VReg(index)) =
                (base.as_ref(), index.as_ref())
            else {
                return None;
            };
            gpr_width(*base)?;
            gpr_width(*index)?;
            vec![
                set(
                    *d,
                    64,
                    TripOp::MulAdd(
                        reg(*index, 64),
                        TripOperand::Imm(u64::from(*scale)),
                        reg(*base, 64),
                    ),
                ),
                set(
                    *d,
                    64,
                    TripOp::Bin(
                        TripBin::Add,
                        reg(*d, 64),
                        TripOperand::Imm(*disp as i64 as u64),
                    ),
                ),
            ]
        }
        Movzx | MovzxW | MovsxB | MovsxW | Movsx => {
            (inst.operands.len() == 2).then_some(())?;
            let (d, s) = (gpr_at(inst, 0)?, gpr_at(inst, 1)?);
            let (signed, from) = match inst.opcode {
                Movzx => (false, 8),
                MovzxW => (false, 16),
                MovsxB => (true, 8),
                MovsxW => (true, 16),
                _ => (true, 32),
            };
            vec![set(
                d,
                64,
                TripOp::Ext {
                    signed,
                    from,
                    src: reg(s, gpr_width(s)?),
                },
            )]
        }
        CmpRR | TestRR => {
            (inst.operands.len() == 2).then_some(())?;
            let (a, b) = (gpr_at(inst, 0)?, gpr_at(inst, 1)?);
            let width = if a.class == RegClass::Gpr32 && b.class == RegClass::Gpr32 {
                32
            } else {
                64
            };
            vec![TripEffect::Flags {
                op: if inst.opcode == CmpRR {
                    FlagOp::Sub
                } else {
                    FlagOp::And
                },
                a: reg(a, width),
                b: reg(b, width),
                width,
            }]
        }
        CmpRI | CmpRI8 | TestRI => {
            (inst.operands.len() == 2).then_some(())?;
            let a = gpr_at(inst, 0)?;
            let width = if inst.opcode == CmpRI {
                gpr_width(a)?
            } else {
                64
            };
            vec![TripEffect::Flags {
                op: if inst.opcode == TestRI {
                    FlagOp::And
                } else {
                    FlagOp::Sub
                },
                a: reg(a, width),
                b: TripOperand::Imm(imm_at(inst, 1)? as u64),
                width,
            }]
        }
        Setcc => {
            let [X86ISelOperand::VReg(d), X86ISelOperand::CondCode(cc)] = inst.operands.as_slice()
            else {
                return None;
            };
            gpr_width(*d)?;
            // Only the low byte changes: the rest of the 64-bit register,
            // whatever width last wrote it, is kept.
            vec![set(
                *d,
                64,
                TripOp::SetLow8 {
                    old: reg(*d, 64),
                    cond: TripCond::X86(*cc),
                },
            )]
        }
        Cmovcc | Cmovcc32 => {
            let [
                X86ISelOperand::VReg(d),
                X86ISelOperand::VReg(s),
                X86ISelOperand::CondCode(cc),
            ] = inst.operands.as_slice()
            else {
                return None;
            };
            gpr_width(*d)?;
            gpr_width(*s)?;
            let width = if inst.opcode == Cmovcc32 { 32 } else { 64 };
            vec![set(
                *d,
                width,
                TripOp::Select {
                    cond: TripCond::X86(*cc),
                    then: reg(*s, width),
                    otherwise: reg(*d, width),
                    post: SelectPost::Plain,
                },
            )]
        }
        _ => return None,
    })
}
