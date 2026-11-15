// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Obligations for the AArch64 trap carriers and their late expansion
//! (ledger `L04-P12`).
//!
//! # The carriers
//!
//! Instruction selection emits a guard as one pseudo-instruction that names
//! the trap condition of the source operation:
//!
//! | carrier | operands | traps iff |
//! | --- | --- | --- |
//! | `TrapNullIfZero` | `ptr` | `ptr == 0` |
//! | `TrapDivZeroIfZero` | `divisor` | `divisor == 0` |
//! | `TrapBoundsCheckExact` | `base, index, bound` | `index >=u bound` (immediate or register bound; `base` is identity metadata) |
//! | `TrapShiftRangeIfOOB` | `amount, #bitwidth` | `amount >=u bitwidth` |
//! | `TrapOverflowExact` | `lhs, rhs, #tag` | the tagged add/sub/mul overflows at the tagged width |
//! | `Brk`, `TrapOverflow`, `TrapBoundsCheck`, `TrapNull`, `TrapDivZero`, `TrapShiftRange` | none (or `Brk #imm16`) | always |
//!
//! After register allocation `trust-cg-codegen`'s `lower::expand_trap_*`
//! rewrites each conditional carrier into a compare (or nothing, for the
//! `CBNZ` forms), a conditional branch that skips exactly the next word, and
//! `BRK #1`. The unconditional forms encode as `BRK #imm16` (`#1` unless the
//! `Brk` names its immediate).
//!
//! # The obligation
//!
//! [`trap_expansion_obligation`] states, for one carrier and the words of one
//! expansion, that the words trap exactly when the carrier's condition holds:
//!
//! * The machine side is computed from the WORDS. Each word is decoded here
//!   by fields written from the Arm A64 encoding tables (Arm DDI 0487, C4.1),
//!   not by `trust-cg-codegen`'s decoder, and executed over a symbolic
//!   register file: `x0`..`x30` are 64-bit variables, a W operand reads the
//!   low 32 bits, a W write zeroes the upper half, register 31 is the zero
//!   register (and SP as the base of an immediate add/sub, which is refused).
//!   NZCV is the Arm ARM `AddWithCarry` of the flag-setting word, stated in
//!   its pseudo-code form (`UInt`/`SInt` sums one bit wider than the operands).
//!   `MUL`, `SMULH` and `UMULH` are the low and high halves of the widened
//!   product, `ASR` is `bvashr`. The branch is taken per the Arm
//!   `ConditionHolds` table (`B.cond`) or the register test (`CBZ`/`CBNZ`).
//! * The words must form an expansion: the conditional branch is the
//!   penultimate word and targets the word after the last one (it skips
//!   exactly the trap), the last word is `BRK #1`, and no word writes a
//!   register other than the scratch registers `x16`/`x17` (or the zero
//!   register). A violation REFUTES the expansion. The machine predicate is
//!   "the branch is not taken".
//! * The intent side is stated from the CARRIER alone, in a form that shares
//!   no term with the machine side: `ptr == 0`, `divisor == 0`,
//!   `index >=u bound`, `amount >=u bitwidth`, and, for overflow, "the result
//!   one bit wider (two's complement or unsigned) differs from the extended
//!   wrapped result" (or, for the 64-bit multiplications, "the 128-bit product
//!   differs from the extension of its low half"). Operand values are the
//!   carrier's registers at the operand's view: the register class for the
//!   guards, the tag's width for overflow.
//!
//! For a pre-allocation carrier (virtual registers) [`stated_expansion`] states
//! the expansion `lower::expand_trap_*` produces, over distinct role registers
//! that avoid `x16`/`x17`, and the obligation is over that statement's words
//! ([`expansion_word`] is this module's own encoder). After allocation the
//! verifier judges the expansion actually in the function (recorded in
//! `MachFunction::trap_expansions`), and per compile ENC-5
//! ([`check_emitted_trap_expansion`]) judges the words in the object.
//!
//! # How it is decided, and what that is worth
//!
//! [`decide`] decides every obligation exactly, in process:
//!
//! * the guards, bounds, shift ranges and add/sub overflow by
//!   [`crate::bitserial_decide`], an automaton over every input assignment;
//! * the multiplication overflows by sound rewriting to identical terms
//!   (truncation of a product is the product of the truncations, a sign or
//!   zero extension is a concatenation, an equality with a concatenation is
//!   the equality of its halves, `x + ~y + 1 == 0` is `x == y`), because a
//!   product has no bit-serial form.
//!
//! A refutation carries a counterexample (or names the structural violation).
//! A holding verdict is cross-checked by sampling the ordinary evaluator. This
//! is testing-grade evidence about this module's terms and decoders, not a
//! certificate. A holding conditional verdict carries a
//! [`TrapExpansionReplay`], the capability to send the same obligation
//! (register-renamed) through a verification request's admitted AY and
//! explicit Clean checker. The function verifier replays it only under an
//! enforced source-bound replay policy, through the request (its AY, policy,
//! refusals, budget and reuse identity), and credits only a Clean-checked
//! proof; every other answer leaves the row uncredited.
//!
//! # What it does not establish
//!
//! That the carrier is the right guard for the source operation (instruction
//! selection's choice of operand, bound or tag is trusted, as for every
//! machine-IR row); that NZCV is dead across a flag-setting expansion (the
//! function verifier checks that separately in the final stream); the
//! process-level effect of `BRK` (a debug exception, SIGTRAP under the hosted
//! operating systems; the native tests observe it); or agreement with silicon.

use std::collections::HashMap;
use std::sync::{LazyLock, Mutex};

use crate::bitserial_decide::{self, Exact, evaluations_equal};
use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::smt::{EvalEnv, SmtExpr as E};
use trust_cg_ir::overflow_tag::{OverflowOp, unpack_overflow_tag};
use trust_cg_ir::{AArch64Opcode as O, MachInst, MachOperand, PReg, RegClass, SpecialReg};

/// The trap code every trap the backend emits carries (`BRK #1`).
pub const TRAP_CODE: u16 = 1;

/// Every trap opcode: the five conditional carriers and the unconditional
/// forms.
pub const TRAP_OPCODES: &[O] = &[
    O::TrapNullIfZero,
    O::TrapDivZeroIfZero,
    O::TrapBoundsCheckExact,
    O::TrapShiftRangeIfOOB,
    O::TrapOverflowExact,
    O::Brk,
    O::TrapOverflow,
    O::TrapBoundsCheck,
    O::TrapNull,
    O::TrapDivZero,
    O::TrapShiftRange,
];

/// The carriers whose expansion is conditional.
pub const CONDITIONAL_TRAP_OPCODES: &[O] = &[
    O::TrapNullIfZero,
    O::TrapDivZeroIfZero,
    O::TrapBoundsCheckExact,
    O::TrapShiftRangeIfOOB,
    O::TrapOverflowExact,
];

/// The reason prefix of a holding conditional trap row the function verifier
/// does not credit.
pub const TRAP_EXPANSION_IS_NOT_CREDIT: &str = "trap expansion is not proof credit without a \
     Clean-checked certificate";

/// Why a carrier or an expansion is outside the model, or refuted.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum TrapRefusal {
    /// The carrier's shape is not one the backend's expansion handles; it is
    /// refused by name rather than judged.
    #[error("{opcode:?} is not a modeled trap carrier: {why}")]
    Unmodeled { opcode: O, why: String },
    /// The words are not an expansion of the carrier.
    #[error("the expansion words are refuted: {0}")]
    Refuted(String),
}

fn unmodeled<T>(opcode: O, why: impl Into<String>) -> Result<T, TrapRefusal> {
    Err(TrapRefusal::Unmodeled {
        opcode,
        why: why.into(),
    })
}

fn refuted<T>(why: impl Into<String>) -> Result<T, TrapRefusal> {
    Err(TrapRefusal::Refuted(why.into()))
}

// ===========================================================================
// Registers
// ===========================================================================

/// A general-purpose register: number 0..=30 and the view (32 or 64 bits).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Gpr {
    pub number: u8,
    pub width: u32,
}

impl Gpr {
    pub fn preg(self) -> PReg {
        PReg::new(u16::from(self.number) + if self.width == 32 { 32 } else { 0 })
    }

    fn operand(self) -> MachOperand {
        MachOperand::PReg(self.preg())
    }

    fn with_width(self, width: u32) -> Self {
        Self { width, ..self }
    }
}

const X16: Gpr = Gpr {
    number: 16,
    width: 64,
};
const X17: Gpr = Gpr {
    number: 17,
    width: 64,
};

fn gpr(operand: &MachOperand) -> Option<Gpr> {
    match operand {
        MachOperand::PReg(p) => match p.encoding() {
            e @ 0..=30 => Some(Gpr {
                number: e as u8,
                width: 64,
            }),
            e @ 32..=62 => Some(Gpr {
                number: (e - 32) as u8,
                width: 32,
            }),
            _ => None,
        },
        _ => None,
    }
}

/// Width of a register-or-zero-register destination/source operand.
fn operand_width(operand: &MachOperand) -> Option<(u32, u32)> {
    match operand {
        MachOperand::PReg(p) => match p.encoding() {
            e @ 0..=30 => Some((64, u32::from(e))),
            e @ 32..=62 => Some((32, u32::from(e - 32))),
            160 => Some((64, 31)),
            161 => Some((32, 31)),
            _ => None,
        },
        MachOperand::Special(SpecialReg::XZR) => Some((64, 31)),
        MachOperand::Special(SpecialReg::WZR) => Some((32, 31)),
        _ => None,
    }
}

fn imm(operand: &MachOperand) -> Option<i64> {
    match operand {
        MachOperand::Imm(value) => Some(*value),
        _ => None,
    }
}

// ===========================================================================
// Carriers
// ===========================================================================

/// A bounds-check bound.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Bound {
    Imm(u64),
    Reg(Gpr),
}

/// The trap condition a carrier names.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TrapKind {
    Null {
        ptr: Gpr,
    },
    DivZero {
        divisor: Gpr,
    },
    Bounds {
        index: Gpr,
        bound: Bound,
    },
    ShiftRange {
        amount: Gpr,
        bitwidth: u32,
    },
    Overflow {
        lhs: Gpr,
        rhs: Gpr,
        op: OverflowOp,
        width: u32,
    },
    Unconditional {
        code: u16,
    },
}

/// One carrier with physical (or role) registers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TrapCarrier {
    pub opcode: O,
    pub kind: TrapKind,
}

impl TrapCarrier {
    pub fn is_conditional(&self) -> bool {
        !matches!(self.kind, TrapKind::Unconditional { .. })
    }

    /// Short name of the source trap condition.
    pub fn condition_name(&self) -> String {
        match self.kind {
            TrapKind::Null { .. } => "null pointer".into(),
            TrapKind::DivZero { .. } => "zero divisor".into(),
            TrapKind::Bounds {
                bound: Bound::Imm(k),
                ..
            } => format!("index >=u {k}"),
            TrapKind::Bounds { .. } => "index >=u length".into(),
            TrapKind::ShiftRange { bitwidth, .. } => format!("shift amount >=u {bitwidth}"),
            TrapKind::Overflow { op, width, .. } => format!("{op:?} overflow at {width} bits"),
            TrapKind::Unconditional { code } => format!("unconditional BRK #{code}"),
        }
    }
}

/// Is `opcode` one of the trap opcodes this module models?
pub fn is_trap_opcode(opcode: O) -> bool {
    TRAP_OPCODES.contains(&opcode)
}

/// Replace every virtual register of `inst` by a distinct role register
/// (`x0`, `x1`, ..., never `x16`/`x17`) of its class's width. Physical
/// operands are kept.
fn with_role_registers(inst: &MachInst) -> Result<MachInst, TrapRefusal> {
    let mut roles: Vec<u32> = Vec::new();
    let mut out = inst.clone();
    // Role registers avoid the scratch registers and every physical register
    // the carrier already names, so distinct operands stay distinct values.
    let taken: Vec<u8> = inst
        .operands
        .iter()
        .filter_map(gpr)
        .map(|g| g.number)
        .collect();
    let pool: Vec<u8> = (0u8..=30)
        .filter(|n| *n != 16 && *n != 17 && !taken.contains(n))
        .collect();
    for operand in &mut out.operands {
        if let MachOperand::VReg(vreg) = operand {
            let width = match vreg.class {
                RegClass::Gpr32 => 32,
                RegClass::Gpr64 => 64,
                other => {
                    return unmodeled(inst.opcode, format!("operand class {other:?}"));
                }
            };
            let slot = match roles.iter().position(|&id| id == vreg.id) {
                Some(slot) => slot,
                None => {
                    roles.push(vreg.id);
                    roles.len() - 1
                }
            };
            let number = pool
                .get(slot)
                .copied()
                .ok_or_else(|| TrapRefusal::Unmodeled {
                    opcode: inst.opcode,
                    why: "more register operands than role registers".into(),
                })?;
            *operand = Gpr { number, width }.operand();
        }
    }
    Ok(out)
}

/// The carrier `inst` names; virtual registers become role registers.
pub fn trap_carrier(inst: &MachInst) -> Result<TrapCarrier, TrapRefusal> {
    let inst = with_role_registers(inst)?;
    let opcode = inst.opcode;
    let ops = inst.operands.as_slice();
    let reg = |index: usize, role: &str| {
        ops.get(index)
            .and_then(gpr)
            .ok_or_else(|| TrapRefusal::Unmodeled {
                opcode,
                why: format!("operand {index} ({role}) is not a general-purpose register"),
            })
    };
    let arity = |n: usize| {
        if ops.len() == n {
            Ok(())
        } else {
            unmodeled(opcode, format!("{} operands, expected {n}", ops.len()))
        }
    };
    let kind = match opcode {
        O::TrapNullIfZero => {
            arity(1)?;
            TrapKind::Null {
                ptr: reg(0, "ptr")?,
            }
        }
        O::TrapDivZeroIfZero => {
            arity(1)?;
            TrapKind::DivZero {
                divisor: reg(0, "divisor")?,
            }
        }
        O::TrapBoundsCheckExact => {
            arity(3)?;
            let index = reg(1, "index")?;
            let bound = match &ops[2] {
                MachOperand::Imm(k) if (0..=i64::from(i32::MAX)).contains(k) => {
                    Bound::Imm(*k as u64)
                }
                MachOperand::Imm(k) => {
                    return unmodeled(opcode, format!("immediate bound {k} outside [0, i32::MAX]"));
                }
                _ => {
                    let bound = reg(2, "bound")?;
                    if bound.width != index.width {
                        return unmodeled(opcode, "index and bound registers differ in width");
                    }
                    Bound::Reg(bound)
                }
            };
            TrapKind::Bounds { index, bound }
        }
        O::TrapShiftRangeIfOOB => {
            arity(2)?;
            let amount = reg(0, "amount")?;
            let bitwidth = match imm(&ops[1]) {
                Some(bw @ 1..=4095) => bw as u32,
                _ => return unmodeled(opcode, "bit width is not an immediate in [1, 4095]"),
            };
            TrapKind::ShiftRange { amount, bitwidth }
        }
        O::TrapOverflowExact => {
            arity(3)?;
            let lhs = reg(0, "lhs")?;
            let rhs = reg(1, "rhs")?;
            let Some((op, width)) = imm(&ops[2]).and_then(unpack_overflow_tag) else {
                return unmodeled(opcode, "the overflow tag does not decode");
            };
            let width = u32::from(width);
            if op.is_mul() && width != 64 {
                return unmodeled(opcode, "a multiplication carrier is 64-bit only");
            }
            TrapKind::Overflow {
                lhs,
                rhs,
                op,
                width,
            }
        }
        O::Brk => match ops {
            [] => TrapKind::Unconditional { code: TRAP_CODE },
            [MachOperand::Imm(k)] if (0..=0xFFFF).contains(k) => {
                TrapKind::Unconditional { code: *k as u16 }
            }
            _ => return unmodeled(opcode, "BRK takes no operand or one 16-bit immediate"),
        },
        O::TrapOverflow | O::TrapBoundsCheck | O::TrapNull | O::TrapDivZero | O::TrapShiftRange => {
            arity(0)?;
            TrapKind::Unconditional { code: TRAP_CODE }
        }
        other => return unmodeled(other, "not a trap opcode"),
    };
    Ok(TrapCarrier { opcode, kind })
}

// ===========================================================================
// The stated expansion (mirrors trust-cg-codegen lower::expand_trap_*)
// ===========================================================================

/// Condition codes.
const EQ: i64 = 0;
const HS: i64 = 2;
const LO: i64 = 3;
const VC: i64 = 7;

fn zr(width: u32) -> MachOperand {
    MachOperand::Special(if width == 32 {
        SpecialReg::WZR
    } else {
        SpecialReg::XZR
    })
}

fn mi(opcode: O, operands: Vec<MachOperand>) -> MachInst {
    MachInst::new(opcode, operands)
}

/// The expansion `lower::expand_trap_*` emits for `carrier`, as machine
/// instructions. The unconditional forms are the single `BRK`.
pub fn stated_expansion(carrier: &TrapCarrier) -> Vec<MachInst> {
    let skip = |cc: i64| mi(O::BCond, vec![MachOperand::Imm(cc), MachOperand::Imm(2)]);
    let brk = || mi(O::Brk, vec![]);
    match carrier.kind {
        TrapKind::Null { ptr: reg } | TrapKind::DivZero { divisor: reg } => {
            vec![mi(O::Cbnz, vec![reg.operand(), MachOperand::Imm(2)]), brk()]
        }
        TrapKind::Bounds { index, bound } => {
            let mut out = Vec::new();
            match bound {
                Bound::Imm(k) if k <= 0xFFF => out.push(mi(
                    O::CmpRI,
                    vec![index.operand(), MachOperand::Imm(k as i64)],
                )),
                Bound::Imm(k) => {
                    // The scratch takes the index's width (`CMP` compares two
                    // registers of one width): W16 for a 32-bit index, whose
                    // write zero-extends into X16; the bound fits 32 bits.
                    let scratch = X16.with_width(index.width);
                    out.push(mi(
                        O::Movz,
                        vec![scratch.operand(), MachOperand::Imm((k & 0xFFFF) as i64)],
                    ));
                    if (k >> 16) & 0xFFFF != 0 {
                        out.push(mi(
                            O::Movk,
                            vec![
                                scratch.operand(),
                                MachOperand::Imm(((k >> 16) & 0xFFFF) as i64),
                                MachOperand::Imm(16),
                            ],
                        ));
                    }
                    out.push(mi(O::CmpRR, vec![index.operand(), scratch.operand()]));
                }
                Bound::Reg(bound) => {
                    out.push(mi(O::CmpRR, vec![index.operand(), bound.operand()]));
                }
            }
            out.push(skip(LO));
            out.push(brk());
            out
        }
        TrapKind::ShiftRange { amount, bitwidth } => vec![
            mi(
                O::CmpRI,
                vec![amount.operand(), MachOperand::Imm(i64::from(bitwidth))],
            ),
            skip(LO),
            brk(),
        ],
        TrapKind::Overflow {
            lhs,
            rhs,
            op: OverflowOp::SignedMul,
            ..
        } => vec![
            mi(O::MulRR, vec![X16.operand(), lhs.operand(), rhs.operand()]),
            mi(O::Smulh, vec![X17.operand(), lhs.operand(), rhs.operand()]),
            mi(
                O::AsrRI,
                vec![X16.operand(), X16.operand(), MachOperand::Imm(63)],
            ),
            mi(O::CmpRR, vec![X17.operand(), X16.operand()]),
            skip(EQ),
            brk(),
        ],
        TrapKind::Overflow {
            lhs,
            rhs,
            op: OverflowOp::UnsignedMul,
            ..
        } => vec![
            mi(O::Umulh, vec![X16.operand(), lhs.operand(), rhs.operand()]),
            mi(O::CmpRI, vec![X16.operand(), MachOperand::Imm(0)]),
            skip(EQ),
            brk(),
        ],
        TrapKind::Overflow {
            lhs,
            rhs,
            op,
            width,
        } => {
            let setter = if op.is_sub() { O::SubsRR } else { O::AddsRR };
            let cc = match op {
                OverflowOp::UnsignedAdd => LO,
                OverflowOp::UnsignedSub => HS,
                _ => VC,
            };
            vec![
                mi(setter, vec![zr(width), lhs.operand(), rhs.operand()]),
                skip(cc),
                brk(),
            ]
        }
        TrapKind::Unconditional { code } if code == TRAP_CODE => vec![brk()],
        TrapKind::Unconditional { code } => {
            vec![mi(O::Brk, vec![MachOperand::Imm(i64::from(code))])]
        }
    }
}

// ===========================================================================
// This module's encoder (Arm DDI 0487, C4.1), for the expansion forms only
// ===========================================================================

fn sf(width: u32) -> u32 {
    u32::from(width == 64)
}

fn branch_imm19(inst: &MachInst, index: usize) -> Result<u32, TrapRefusal> {
    match inst.operands.get(index).and_then(imm) {
        Some(words) if (-(1 << 18)..(1 << 18)).contains(&words) => {
            Ok((words as i32 as u32) & 0x7FFFF)
        }
        _ => unmodeled(
            inst.opcode,
            "branch offset is not a resolved 19-bit word offset",
        ),
    }
}

fn three_regs(inst: &MachInst) -> Result<(u32, u32, u32, u32), TrapRefusal> {
    match inst.operands.as_slice() {
        [d, n, m] => match (operand_width(d), operand_width(n), operand_width(m)) {
            (Some((width, d)), Some((_, n)), Some((_, m))) if n != 31 && m != 31 => {
                Ok((width, d, n, m))
            }
            _ => unmodeled(inst.opcode, "operands are not general-purpose registers"),
        },
        _ => unmodeled(inst.opcode, "expected three register operands"),
    }
}

/// The word this module encodes for one expansion instruction.
pub fn expansion_word(inst: &MachInst) -> Result<u32, TrapRefusal> {
    let ops = inst.operands.as_slice();
    match inst.opcode {
        O::Cbz | O::Cbnz => {
            let Some(reg) = ops.first().and_then(gpr) else {
                return unmodeled(inst.opcode, "operand 0 is not a general-purpose register");
            };
            if ops.len() != 2 {
                return unmodeled(inst.opcode, "expected a register and a word offset");
            }
            let op = u32::from(inst.opcode == O::Cbnz);
            Ok((sf(reg.width) << 31)
                | (0b011010 << 25)
                | (op << 24)
                | (branch_imm19(inst, 1)? << 5)
                | u32::from(reg.number))
        }
        O::BCond => match ops {
            [MachOperand::Imm(cond), _] if (0..=15).contains(cond) => {
                Ok(0x5400_0000 | (branch_imm19(inst, 1)? << 5) | (*cond as u32))
            }
            _ => unmodeled(inst.opcode, "expected a condition and a word offset"),
        },
        O::Brk => match ops {
            [] => Ok(0xD420_0000 | (u32::from(TRAP_CODE) << 5)),
            [MachOperand::Imm(k)] if (0..=0xFFFF).contains(k) => {
                Ok(0xD420_0000 | ((*k as u32) << 5))
            }
            _ => unmodeled(inst.opcode, "BRK takes no operand or one 16-bit immediate"),
        },
        O::CmpRI => match ops {
            [n, MachOperand::Imm(k)] if (0..=0xFFF).contains(k) => {
                let Some(n) = gpr(n) else {
                    return unmodeled(inst.opcode, "operand 0 is not a general-purpose register");
                };
                Ok((sf(n.width) << 31)
                    | (0b11 << 29)
                    | (0b100010 << 23)
                    | ((*k as u32) << 10)
                    | (u32::from(n.number) << 5)
                    | 31)
            }
            _ => unmodeled(inst.opcode, "expected a register and a 12-bit immediate"),
        },
        O::CmpRR => match ops {
            [n, m] => match (gpr(n), gpr(m)) {
                (Some(n), Some(m)) if n.width == m.width => Ok((sf(n.width) << 31)
                    | (0b11 << 29)
                    | (0b01011 << 24)
                    | (u32::from(m.number) << 16)
                    | (u32::from(n.number) << 5)
                    | 31),
                _ => unmodeled(inst.opcode, "expected two registers of one width"),
            },
            _ => unmodeled(inst.opcode, "expected two registers"),
        },
        O::AddsRR | O::SubsRR => {
            let (width, d, n, m) = three_regs(inst)?;
            let op = u32::from(inst.opcode == O::SubsRR);
            Ok((sf(width) << 31)
                | (op << 30)
                | (1 << 29)
                | (0b01011 << 24)
                | (m << 16)
                | (n << 5)
                | d)
        }
        O::Movz | O::Movk => {
            let (width, d) =
                ops.first()
                    .and_then(operand_width)
                    .ok_or_else(|| TrapRefusal::Unmodeled {
                        opcode: inst.opcode,
                        why: "operand 0 is not a register".into(),
                    })?;
            let (value, shift) = match ops {
                [_, MachOperand::Imm(v)] => (*v, 0),
                [_, MachOperand::Imm(v), MachOperand::Imm(s)] => (*v, *s),
                _ => return unmodeled(inst.opcode, "expected a register, imm16 and shift"),
            };
            if !(0..=0xFFFF).contains(&value) || !matches!(shift, 0 | 16 | 32 | 48) {
                return unmodeled(inst.opcode, "immediate or shift out of range");
            }
            let hw = (shift / 16) as u32;
            if width == 32 && hw > 1 {
                return unmodeled(inst.opcode, "a W move-wide shifts by 0 or 16 only");
            }
            let opc = if inst.opcode == O::Movz { 0b10 } else { 0b11 };
            Ok((sf(width) << 31)
                | (opc << 29)
                | (0b100101 << 23)
                | (hw << 21)
                | ((value as u32) << 5)
                | d)
        }
        O::MulRR => {
            let (width, d, n, m) = three_regs(inst)?;
            Ok((sf(width) << 31) | (0b0011011 << 24) | (m << 16) | (31 << 10) | (n << 5) | d)
        }
        O::Smulh | O::Umulh => {
            let (width, d, n, m) = three_regs(inst)?;
            if width != 64 {
                return unmodeled(inst.opcode, "a multiply-high is 64-bit only");
            }
            let op31 = if inst.opcode == O::Smulh {
                0b010
            } else {
                0b110
            };
            Ok(
                (1 << 31)
                    | (0b0011011 << 24)
                    | (op31 << 21)
                    | (m << 16)
                    | (31 << 10)
                    | (n << 5)
                    | d,
            )
        }
        O::AsrRI => match ops {
            [d, n, MachOperand::Imm(s)] => match (operand_width(d), gpr(n)) {
                (Some((width, d)), Some(n)) if (0..i64::from(width)).contains(s) => Ok((sf(width)
                    << 31)
                    | (0b100110 << 23)
                    | (sf(width) << 22)
                    | ((*s as u32) << 16)
                    | ((width - 1) << 10)
                    | (u32::from(n.number) << 5)
                    | d),
                _ => unmodeled(
                    inst.opcode,
                    "expected registers and a shift below the width",
                ),
            },
            _ => unmodeled(inst.opcode, "expected two registers and a shift"),
        },
        other => unmodeled(other, "not an expansion instruction"),
    }
}

/// The words of [`stated_expansion`].
pub fn stated_words(carrier: &TrapCarrier) -> Result<Vec<u32>, TrapRefusal> {
    stated_expansion(carrier)
        .iter()
        .map(expansion_word)
        .collect()
}

// ===========================================================================
// This module's decoder and machine semantics
// ===========================================================================

/// One decoded expansion word.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Word {
    CompareBranch {
        width: u32,
        nonzero: bool,
        imm19: i32,
        rt: u32,
    },
    CondBranch {
        imm19: i32,
        cond: u32,
    },
    Brk {
        imm16: u16,
    },
    AddSubReg {
        width: u32,
        sub: bool,
        rm: u32,
        rn: u32,
        rd: u32,
    },
    AddSubImm {
        width: u32,
        sub: bool,
        imm: u64,
        rn: u32,
        rd: u32,
    },
    MoveWide {
        width: u32,
        keep: bool,
        hw: u32,
        imm16: u64,
        rd: u32,
    },
    Mul {
        width: u32,
        rm: u32,
        rn: u32,
        rd: u32,
    },
    MulHigh {
        signed: bool,
        rm: u32,
        rn: u32,
        rd: u32,
    },
    Asr {
        width: u32,
        shift: u32,
        rn: u32,
        rd: u32,
    },
}

fn field(w: u32, hi: u32, lo: u32) -> u32 {
    (w >> lo) & ((1u32 << (hi - lo + 1)) - 1)
}

fn signed19(value: u32) -> i32 {
    ((value << 13) as i32) >> 13
}

/// Decode one word of the classes an expansion uses; any other word (or an
/// unallocated or out-of-shape encoding of these classes) is refused.
pub fn decode(w: u32) -> Result<Word, TrapRefusal> {
    let width = if field(w, 31, 31) == 1 { 64 } else { 32 };
    let (rd, rn, rm) = (field(w, 4, 0), field(w, 9, 5), field(w, 20, 16));
    let out = if w & 0x7E00_0000 == 0x3400_0000 {
        Word::CompareBranch {
            width,
            nonzero: field(w, 24, 24) == 1,
            imm19: signed19(field(w, 23, 5)),
            rt: rd,
        }
    } else if w & 0xFF00_0010 == 0x5400_0000 {
        Word::CondBranch {
            imm19: signed19(field(w, 23, 5)),
            cond: field(w, 3, 0),
        }
    } else if w & 0xFFE0_001F == 0xD420_0000 {
        Word::Brk {
            imm16: field(w, 20, 5) as u16,
        }
    } else if w & 0x1F20_0000 == 0x0B00_0000 {
        // Add/subtract (shifted register): only the flag-setting form with no
        // shift is an expansion word.
        if field(w, 29, 29) != 1 || field(w, 23, 22) != 0 || field(w, 15, 10) != 0 {
            return refuted(format!(
                "{w:#010x}: add/sub (shifted register) outside the expansion shapes"
            ));
        }
        Word::AddSubReg {
            width,
            sub: field(w, 30, 30) == 1,
            rm,
            rn,
            rd,
        }
    } else if w & 0x1F80_0000 == 0x1100_0000 {
        if field(w, 29, 29) != 1 {
            return refuted(format!("{w:#010x}: a non-flag-setting add/sub immediate"));
        }
        let imm12 = u64::from(field(w, 21, 10));
        Word::AddSubImm {
            width,
            sub: field(w, 30, 30) == 1,
            imm: if field(w, 22, 22) == 1 {
                imm12 << 12
            } else {
                imm12
            },
            rn,
            rd,
        }
    } else if w & 0x1F80_0000 == 0x1280_0000 {
        let opc = field(w, 30, 29);
        let hw = field(w, 22, 21);
        if opc == 0b01 || (width == 32 && hw > 1) {
            return refuted(format!("{w:#010x}: unallocated move-wide"));
        }
        if opc == 0b00 {
            return refuted(format!("{w:#010x}: MOVN is outside the expansion shapes"));
        }
        Word::MoveWide {
            width,
            keep: opc == 0b11,
            hw,
            imm16: u64::from(field(w, 20, 5)),
            rd,
        }
    } else if w & 0x1F00_0000 == 0x1B00_0000 {
        let (op54, op31, o0, ra) = (
            field(w, 30, 29),
            field(w, 23, 21),
            field(w, 15, 15),
            field(w, 14, 10),
        );
        match (op54, op31, o0, ra, width) {
            (0, 0b000, 0, 31, _) => Word::Mul { width, rm, rn, rd },
            (0, 0b010, 0, 31, 64) => Word::MulHigh {
                signed: true,
                rm,
                rn,
                rd,
            },
            (0, 0b110, 0, 31, 64) => Word::MulHigh {
                signed: false,
                rm,
                rn,
                rd,
            },
            _ => {
                return refuted(format!(
                    "{w:#010x}: data-processing (3 source) outside the expansion shapes"
                ));
            }
        }
    } else if w & 0x1F80_0000 == 0x1300_0000 {
        let (opc, n, immr, imms) = (
            field(w, 30, 29),
            field(w, 22, 22),
            field(w, 21, 16),
            field(w, 15, 10),
        );
        if opc != 0 || n != sf(width) || imms != width - 1 || immr >= width {
            return refuted(format!("{w:#010x}: bitfield word other than ASR #imm"));
        }
        Word::Asr {
            width,
            shift: immr,
            rn,
            rd,
        }
    } else {
        return refuted(format!(
            "{w:#010x} is in no instruction class of a trap expansion"
        ));
    };
    Ok(out)
}

fn ones(width: u32) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

fn konst(value: u64, width: u32) -> E {
    E::bv_const(value & ones(width), width)
}

fn reg_var(number: u32) -> E {
    E::var(format!("x{number}"), 64)
}

/// The view of a 64-bit register value at `width`.
fn low(value: E, width: u32) -> E {
    if width == 64 {
        value
    } else {
        value.extract(width - 1, 0)
    }
}

fn bv1(cond: E) -> E {
    E::ite(cond, E::bv_const(1, 1), E::bv_const(0, 1))
}

/// The four flags as Boolean terms.
#[derive(Clone)]
struct Nzcv {
    n: E,
    z: E,
    c: E,
    v: E,
}

impl Nzcv {
    fn unknown() -> Self {
        let flag = |name: &str| E::var(format!("nzcv_in_{name}"), 1).eq_expr(E::bv_const(1, 1));
        Self {
            n: flag("n"),
            z: flag("z"),
            c: flag("c"),
            v: flag("v"),
        }
    }
}

/// Arm `AddWithCarry(x, y, carry_in)` at `width`: the result and NZCV, in the
/// pseudo-code's form (sums one bit wider than the operands).
fn add_with_carry(x: E, y: E, carry: u64, width: u32) -> (E, Nzcv) {
    let unsigned_sum = x
        .clone()
        .zero_ext(1)
        .bvadd(y.clone().zero_ext(1))
        .bvadd(konst(carry, width + 1));
    let signed_sum = x
        .sign_ext(1)
        .bvadd(y.sign_ext(1))
        .bvadd(konst(carry, width + 1));
    let result = unsigned_sum.clone().extract(width - 1, 0);
    let flags = Nzcv {
        n: result.clone().bvslt(konst(0, width)),
        z: result.clone().eq_expr(konst(0, width)),
        c: result.clone().zero_ext(1).eq_expr(unsigned_sum).not_expr(),
        v: result.clone().sign_ext(1).eq_expr(signed_sum).not_expr(),
    };
    (result, flags)
}

/// Arm `ConditionHolds(cond)`.
fn condition_holds(cond: u32, f: &Nzcv) -> E {
    let base = match cond >> 1 {
        0b000 => f.z.clone(),
        0b001 => f.c.clone(),
        0b010 => f.n.clone(),
        0b011 => f.v.clone(),
        0b100 => f.c.clone().and_expr(f.z.clone().not_expr()),
        0b101 => f.n.clone().eq_expr(f.v.clone()),
        0b110 => {
            f.n.clone()
                .eq_expr(f.v.clone())
                .and_expr(f.z.clone().not_expr())
        }
        _ => E::bool_const(true),
    };
    if cond & 1 == 1 && cond != 0b1111 {
        base.not_expr()
    } else {
        base
    }
}

/// The machine side of an expansion: the predicate under which the words
/// reach the `BRK`, from the decoded words alone.
pub fn machine_trap_predicate(words: &[u32]) -> Result<E, TrapRefusal> {
    let decoded: Vec<Word> = words.iter().map(|&w| decode(w)).collect::<Result<_, _>>()?;
    let Some((&last, body)) = decoded.split_last() else {
        return refuted("an empty expansion");
    };
    let Word::Brk { imm16 } = last else {
        return refuted(format!("the last word is {last:?}, not BRK"));
    };
    if imm16 != TRAP_CODE {
        return refuted(format!(
            "the trap is BRK #{imm16}, not the backend's trap code #{TRAP_CODE}"
        ));
    }
    let Some((&branch, setup)) = body.split_last() else {
        // A lone BRK traps unconditionally.
        return Ok(E::bool_const(true));
    };
    let mut regs: HashMap<u32, E> = HashMap::new();
    let read = |regs: &HashMap<u32, E>, number: u32, width: u32| -> E {
        if number == 31 {
            konst(0, width)
        } else {
            low(
                regs.get(&number)
                    .cloned()
                    .unwrap_or_else(|| reg_var(number)),
                width,
            )
        }
    };
    let mut flags = Nzcv::unknown();
    let write = |regs: &mut HashMap<u32, E>, number: u32, width: u32, value: E| {
        if number == 31 {
            return Ok(());
        }
        if number != 16 && number != 17 {
            return refuted(format!(
                "the expansion writes x{number}; only x16/x17 are scratch"
            ));
        }
        let value = if width == 64 {
            value
        } else {
            value.zero_ext(32)
        };
        regs.insert(number, value);
        Ok(())
    };
    for (index, &word) in setup.iter().enumerate() {
        match word {
            Word::AddSubReg {
                width,
                sub,
                rm,
                rn,
                rd,
            } => {
                let x = read(&regs, rn, width);
                let y = read(&regs, rm, width);
                let y = if sub {
                    y.bvxor(konst(u64::MAX, width))
                } else {
                    y
                };
                let (result, f) = add_with_carry(x, y, u64::from(sub), width);
                flags = f;
                write(&mut regs, rd, width, result)?;
            }
            Word::AddSubImm {
                width,
                sub,
                imm,
                rn,
                rd,
            } => {
                if rn == 31 {
                    return refuted("an immediate compare against SP");
                }
                let x = read(&regs, rn, width);
                let y = konst(imm, width);
                let y = if sub {
                    y.bvxor(konst(u64::MAX, width))
                } else {
                    y
                };
                let (result, f) = add_with_carry(x, y, u64::from(sub), width);
                flags = f;
                write(&mut regs, rd, width, result)?;
            }
            Word::MoveWide {
                width,
                keep,
                hw,
                imm16,
                rd,
            } => {
                let placed = konst(imm16 << (16 * hw), width);
                let value = if keep {
                    let hole = !(0xFFFFu64 << (16 * hw));
                    read(&regs, rd, width)
                        .bvand(konst(hole, width))
                        .bvor(placed)
                } else {
                    placed
                };
                write(&mut regs, rd, width, value)?;
            }
            Word::Mul { width, rm, rn, rd } => {
                // Arm: result = UInt(Ra) + UInt(Rn) * UInt(Rm), low `width` bits;
                // Ra is the zero register.
                let product = read(&regs, rn, width)
                    .zero_ext(width)
                    .bvmul(read(&regs, rm, width).zero_ext(width));
                let value = konst(0, width)
                    .zero_ext(width)
                    .bvadd(product)
                    .extract(width - 1, 0);
                write(&mut regs, rd, width, value)?;
            }
            Word::MulHigh { signed, rm, rn, rd } => {
                let (n, m) = (read(&regs, rn, 64), read(&regs, rm, 64));
                let product = if signed {
                    n.sign_ext(64).bvmul(m.sign_ext(64))
                } else {
                    n.zero_ext(64).bvmul(m.zero_ext(64))
                };
                write(&mut regs, rd, 64, product.extract(127, 64))?;
            }
            Word::Asr {
                width,
                shift,
                rn,
                rd,
            } => {
                let value = read(&regs, rn, width).bvashr(konst(u64::from(shift), width));
                write(&mut regs, rd, width, value)?;
            }
            other => {
                return refuted(format!(
                    "word {index} ({other:?}) precedes the conditional branch"
                ));
            }
        }
    }
    let taken = match branch {
        Word::CondBranch { imm19, cond } => {
            if imm19 != 2 {
                return refuted(format!(
                    "the conditional branch moves {imm19} words; it must skip exactly the BRK (2)"
                ));
            }
            condition_holds(cond, &flags)
        }
        Word::CompareBranch {
            width,
            nonzero,
            imm19,
            rt,
        } => {
            if imm19 != 2 {
                return refuted(format!(
                    "the compare-and-branch moves {imm19} words; it must skip exactly the BRK (2)"
                ));
            }
            let zero = read(&regs, rt, width).eq_expr(konst(0, width));
            if nonzero { zero.not_expr() } else { zero }
        }
        other => {
            return refuted(format!(
                "the word before BRK is {other:?}, not a conditional branch"
            ));
        }
    };
    Ok(taken.not_expr())
}

/// The intent side: the carrier's trap condition over its registers.
pub fn source_trap_condition(carrier: &TrapCarrier) -> E {
    let view = |g: Gpr, width: u32| low(reg_var(u32::from(g.number)), width);
    let role = |g: Gpr| view(g, g.width);
    match carrier.kind {
        TrapKind::Null { ptr: g } | TrapKind::DivZero { divisor: g } => {
            role(g).eq_expr(konst(0, g.width))
        }
        TrapKind::Bounds {
            index,
            bound: Bound::Imm(k),
        } => role(index).bvuge(konst(k, index.width)),
        TrapKind::Bounds {
            index,
            bound: Bound::Reg(bound),
        } => role(index).bvuge(role(bound)),
        TrapKind::ShiftRange { amount, bitwidth } => {
            role(amount).bvuge(konst(u64::from(bitwidth), amount.width))
        }
        TrapKind::Overflow {
            lhs,
            rhs,
            op,
            width,
        } => {
            let (l, r) = (view(lhs, width), view(rhs, width));
            match op {
                OverflowOp::SignedAdd => l
                    .clone()
                    .sign_ext(1)
                    .bvadd(r.clone().sign_ext(1))
                    .eq_expr(l.bvadd(r).sign_ext(1))
                    .not_expr(),
                OverflowOp::SignedSub => l
                    .clone()
                    .sign_ext(1)
                    .bvsub(r.clone().sign_ext(1))
                    .eq_expr(l.bvsub(r).sign_ext(1))
                    .not_expr(),
                OverflowOp::UnsignedAdd => l
                    .clone()
                    .zero_ext(1)
                    .bvadd(r.clone().zero_ext(1))
                    .eq_expr(l.bvadd(r).zero_ext(1))
                    .not_expr(),
                OverflowOp::UnsignedSub => l
                    .clone()
                    .zero_ext(1)
                    .bvsub(r.clone().zero_ext(1))
                    .eq_expr(l.bvsub(r).zero_ext(1))
                    .not_expr(),
                OverflowOp::SignedMul => {
                    let product = l.sign_ext(64).bvmul(r.sign_ext(64));
                    product
                        .clone()
                        .eq_expr(product.extract(63, 0).sign_ext(64))
                        .not_expr()
                }
                OverflowOp::UnsignedMul => {
                    let product = l.zero_ext(64).bvmul(r.zero_ext(64));
                    product
                        .clone()
                        .eq_expr(product.extract(63, 0).zero_ext(64))
                        .not_expr()
                }
            }
        }
        TrapKind::Unconditional { .. } => E::bool_const(true),
    }
}

// ===========================================================================
// The obligation
// ===========================================================================

/// One expansion's obligation: the words trap exactly when the carrier's
/// condition holds.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TrapExpansionObligation {
    pub carrier: TrapCarrier,
    pub words: Vec<u32>,
    /// The carrier's trap condition (Boolean).
    pub source: E,
    /// The predicate under which the words reach the `BRK` (Boolean).
    pub machine: E,
    /// The same statement as a `ProofObligation` over `bv1` sides, for replay.
    pub obligation: ProofObligation,
}

/// The obligation for `carrier` and the words of one expansion. A word
/// sequence that is not an expansion (a wrong class, a branch that does not
/// skip exactly the `BRK`, another trap code, a write outside `x16`/`x17`)
/// is refused as [`TrapRefusal::Refuted`].
pub fn trap_expansion_obligation(
    carrier: &TrapCarrier,
    words: &[u32],
) -> Result<TrapExpansionObligation, TrapRefusal> {
    if let TrapKind::Unconditional { code } = carrier.kind {
        // The unconditional forms are exactly one BRK with their own code.
        return match words {
            [w] => match decode(*w)? {
                Word::Brk { imm16 } if imm16 == code => Ok(obligation_of(
                    carrier,
                    words,
                    E::bool_const(true),
                    E::bool_const(true),
                )),
                other => refuted(format!(
                    "an unconditional trap must be BRK #{code}; decoded {other:?}"
                )),
            },
            _ => refuted(format!(
                "an unconditional trap is one word; got {}",
                words.len()
            )),
        };
    }
    let machine = machine_trap_predicate(words)?;
    Ok(obligation_of(
        carrier,
        words,
        source_trap_condition(carrier),
        machine,
    ))
}

fn obligation_of(
    carrier: &TrapCarrier,
    words: &[u32],
    source: E,
    machine: E,
) -> TrapExpansionObligation {
    let mut inputs: Vec<(String, u32)> = Vec::new();
    for side in [&source, &machine] {
        for var in bitserial_decide::variables(side).unwrap_or_default() {
            if !inputs.contains(&var) {
                inputs.push(var);
            }
        }
    }
    let words_text: Vec<String> = words.iter().map(|w| format!("{w:#010x}")).collect();
    let obligation = ProofObligation {
        name: format!(
            "A64 trap expansion {:?} ({}): [{}]",
            carrier.opcode,
            carrier.condition_name(),
            words_text.join(" ")
        ),
        trust_ir_expr: bv1(source.clone()),
        aarch64_expr: bv1(machine.clone()),
        inputs,
        preconditions: Vec::new(),
        fp_inputs: Vec::new(),
        category: Some(TransvalCheckKind::ControlFlow),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: format!("{:?}", carrier.opcode),
            arity: u8::try_from(words.len()).unwrap_or(u8::MAX),
        },
    };
    TrapExpansionObligation {
        carrier: *carrier,
        words: words.to_vec(),
        source,
        machine,
        obligation,
    }
}

// ===========================================================================
// In-process decision
// ===========================================================================

/// The in-process verdict.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision {
    /// Holds for every input; `method` names how it was decided.
    Holds { method: &'static str },
    /// Fails: a counterexample or a structural violation.
    Refuted { reason: String },
    /// Neither decided nor refuted (fail closed).
    Undecided { reason: String },
}

impl Decision {
    pub fn holds(&self) -> bool {
        matches!(self, Self::Holds { .. })
    }
}

/// How the bit-serial automaton decides.
pub const METHOD_BITSERIAL: &str = "decided in-process for every input by a bit-serial automaton";
/// How the multiplication forms are decided.
pub const METHOD_NORMALIZATION: &str =
    "decided in-process for every input by sound rewriting to identical terms";

fn rebuild(expr: &E, children: Vec<E>) -> E {
    let mut it = children.into_iter();
    let mut next = || it.next().expect("child count");
    match expr {
        E::BvAdd { .. } => next().bvadd(next()),
        E::BvSub { .. } => next().bvsub(next()),
        E::BvMul { .. } => next().bvmul(next()),
        E::BvAnd { .. } => next().bvand(next()),
        E::BvOr { .. } => next().bvor(next()),
        E::BvXor { .. } => next().bvxor(next()),
        E::BvAshr { .. } => next().bvashr(next()),
        E::Eq { .. } => next().eq_expr(next()),
        E::And { .. } => next().and_expr(next()),
        E::Or { .. } => next().or_expr(next()),
        E::BvUlt { .. } => next().bvult(next()),
        E::BvUle { .. } => next().bvule(next()),
        E::BvUgt { .. } => next().bvugt(next()),
        E::BvUge { .. } => next().bvuge(next()),
        E::BvSlt { .. } => next().bvslt(next()),
        E::BvSle { .. } => next().bvsle(next()),
        E::BvSgt { .. } => next().bvsgt(next()),
        E::BvSge { .. } => next().bvsge(next()),
        E::Concat { .. } => next().concat(next()),
        E::BvNeg { .. } => next().bvneg(),
        E::Not { .. } => next().not_expr(),
        E::Extract { high, low, .. } => next().extract(*high, *low),
        E::ZeroExtend { extra_bits, .. } => next().zero_ext(*extra_bits),
        E::SignExtend { extra_bits, .. } => next().sign_ext(*extra_bits),
        E::Ite { .. } => E::ite(next(), next(), next()),
        other => other.clone(),
    }
}

fn width_of(expr: &E) -> Option<u32> {
    expr.try_bv_width().ok()
}

/// One bottom-up pass of the sound rewrites; `None` when the term has a kind
/// the rewrites do not walk.
fn normalize(expr: &E) -> Option<E> {
    let children: Vec<E> = bitserial_decide::children(expr)?
        .into_iter()
        .map(normalize)
        .collect::<Option<_>>()?;
    let e = rebuild(expr, children);
    Some(rewrite(e))
}

fn rewrite(e: E) -> E {
    match &e {
        // A full-width low extract is the operand.
        E::Extract {
            high,
            low: 0,
            operand,
            ..
        } if width_of(operand) == Some(high + 1) => operand.as_ref().clone(),
        // Constant fold.
        E::Extract {
            high, low, operand, ..
        } if matches!(operand.as_ref(), E::BvConst { .. }) => {
            let E::BvConst { value, .. } = operand.as_ref() else {
                unreachable!()
            };
            konst(value >> low, high - low + 1)
        }
        // Truncation of a ring operation is the operation on the truncations.
        E::Extract {
            high,
            low: 0,
            operand,
            ..
        } if matches!(
            operand.as_ref(),
            E::BvAdd { .. } | E::BvSub { .. } | E::BvMul { .. }
        ) =>
        {
            let parts = bitserial_decide::children(operand).unwrap_or_default();
            let (a, b) = (
                rewrite(parts[0].clone().extract(*high, 0)),
                rewrite(parts[1].clone().extract(*high, 0)),
            );
            rewrite(rebuild(operand, vec![a, b]))
        }
        // The low part of a concatenation.
        E::Extract {
            high,
            low: 0,
            operand,
            ..
        } if matches!(operand.as_ref(), E::Concat { lo, .. } if width_of(lo).is_some_and(|w| *high < w)) =>
        {
            let E::Concat { lo, .. } = operand.as_ref() else {
                unreachable!()
            };
            rewrite(lo.as_ref().clone().extract(*high, 0))
        }
        // An extension is a concatenation with its sign or zero bits.
        E::ZeroExtend {
            operand,
            extra_bits,
            ..
        } => konst(0, *extra_bits).concat(operand.as_ref().clone()),
        E::SignExtend {
            operand,
            extra_bits,
            ..
        } if width_of(operand) == Some(*extra_bits) => {
            let width = *extra_bits;
            rewrite(
                operand
                    .as_ref()
                    .clone()
                    .bvashr(konst(u64::from(width - 1), width)),
            )
            .concat(operand.as_ref().clone())
        }
        // `x + 0`.
        E::BvAdd { lhs, rhs, .. } if is_zero(lhs) => rhs.as_ref().clone(),
        E::BvAdd { lhs, rhs, .. } if is_zero(rhs) => lhs.as_ref().clone(),
        // `x + ~y + 1 == 0` is `x == y`.
        E::Eq { lhs, rhs } if is_zero(rhs) || is_zero(lhs) => {
            let sum = if is_zero(rhs) { lhs } else { rhs };
            if let Some((x, y)) = subtraction_operands(sum) {
                return rewrite(x.eq_expr(y));
            }
            canonical_eq(e)
        }
        // Equality with a concatenation is equality of the halves.
        E::Eq { lhs, rhs }
            if matches!(rhs.as_ref(), E::Concat { .. })
                || matches!(lhs.as_ref(), E::Concat { .. }) =>
        {
            let (whole, concat) = if matches!(rhs.as_ref(), E::Concat { .. }) {
                (lhs, rhs)
            } else {
                (rhs, lhs)
            };
            let E::Concat { hi, lo, .. } = concat.as_ref() else {
                unreachable!()
            };
            let (Some(total), Some(low_width)) = (width_of(whole), width_of(lo)) else {
                return e;
            };
            let high_part = rewrite(whole.as_ref().clone().extract(total - 1, low_width));
            let low_part = rewrite(whole.as_ref().clone().extract(low_width - 1, 0));
            rewrite(
                rewrite(high_part.eq_expr(hi.as_ref().clone()))
                    .and_expr(rewrite(low_part.eq_expr(lo.as_ref().clone()))),
            )
        }
        E::Eq { lhs, rhs } if lhs == rhs => E::bool_const(true),
        E::Eq { .. } => canonical_eq(e),
        E::And { lhs, rhs } => match (lhs.as_ref(), rhs.as_ref()) {
            (E::BoolConst(true), other) | (other, E::BoolConst(true)) => other.clone(),
            (E::BoolConst(false), _) | (_, E::BoolConst(false)) => E::bool_const(false),
            _ => e,
        },
        E::Not { operand } => match operand.as_ref() {
            E::Not { operand } => operand.as_ref().clone(),
            E::BoolConst(b) => E::bool_const(!b),
            _ => e,
        },
        _ => e,
    }
}

fn is_zero(expr: &E) -> bool {
    matches!(expr, E::BvConst { value: 0, .. })
}

/// `(x + (y ^ ones)) + 1` -> `(x, y)`.
fn subtraction_operands(sum: &E) -> Option<(E, E)> {
    let E::BvAdd { lhs, rhs, width } = sum else {
        return None;
    };
    if !matches!(rhs.as_ref(), E::BvConst { value: 1, .. }) {
        return None;
    }
    let E::BvAdd { lhs: x, rhs: t, .. } = lhs.as_ref() else {
        return None;
    };
    let E::BvXor {
        lhs: y, rhs: mask, ..
    } = t.as_ref()
    else {
        return None;
    };
    matches!(mask.as_ref(), E::BvConst { value, .. } if *value == ones(*width))
        .then(|| (x.as_ref().clone(), y.as_ref().clone()))
}

fn canonical_eq(e: E) -> E {
    if let E::Eq { lhs, rhs } = &e
        && format!("{rhs:?}") < format!("{lhs:?}")
    {
        return rhs.as_ref().clone().eq_expr(lhs.as_ref().clone());
    }
    e
}

fn normal_form(expr: &E) -> Option<E> {
    let mut current = expr.clone();
    for _ in 0..8 {
        let next = normalize(&current)?;
        if next == current {
            return Some(next);
        }
        current = next;
    }
    Some(current)
}

/// Boundary and pseudo-random assignments of the variables; the first one on
/// which the two sides differ.
fn search_counterexample(
    source: &E,
    machine: &E,
    inputs: &[(String, u32)],
) -> Option<Vec<(String, u64)>> {
    let corners = |width: u32| {
        let top = ones(width);
        let sign = 1u64 << (width - 1);
        let quarter = |k: u32| {
            if width >= 4 {
                1u64 << (k * width / 4)
            } else {
                1
            }
        };
        vec![
            0,
            1,
            2,
            3,
            top,
            top - 1,
            sign,
            sign - 1,
            sign + 1,
            sign >> 1,
            quarter(1),
            quarter(2),
            quarter(2) >> 1,
            quarter(2) + 1,
            quarter(3),
            0xFFF,
            0x1000,
        ]
        .into_iter()
        .map(move |v| v & top)
        .collect::<Vec<_>>()
    };
    let mut state = 0x9E37_79B9_7F4A_7C15u64;
    let mut random = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let try_values = |values: &[u64]| {
        let mut env = EvalEnv::default();
        for ((name, _), v) in inputs.iter().zip(values) {
            env.insert(name.clone(), *v);
        }
        (!evaluations_equal(&source.eval(&env), &machine.eval(&env))).then(|| {
            inputs
                .iter()
                .zip(values)
                .map(|((name, _), v)| (name.clone(), *v))
                .collect::<Vec<_>>()
        })
    };
    // Every combination of corner values (at most four inputs), then random.
    let corner_sets: Vec<Vec<u64>> = inputs.iter().map(|(_, w)| corners(*w)).collect();
    if inputs.len() <= 4 {
        let mut index = vec![0usize; inputs.len()];
        loop {
            let values: Vec<u64> = index
                .iter()
                .zip(&corner_sets)
                .map(|(&i, set)| set[i])
                .collect();
            if let Some(cex) = try_values(&values) {
                return Some(cex);
            }
            // Next combination (odometer).
            let mut position = 0;
            loop {
                if position == index.len() {
                    break;
                }
                index[position] += 1;
                if index[position] < corner_sets[position].len() {
                    break;
                }
                index[position] = 0;
                position += 1;
            }
            if position == index.len() {
                break;
            }
        }
    }
    for _ in 0..4096 {
        let values: Vec<u64> = inputs.iter().map(|(_, w)| random() & ones(*w)).collect();
        if let Some(cex) = try_values(&values) {
            return Some(cex);
        }
    }
    None
}

/// Holding decisions, memoised per process under the register renaming of
/// [`replay_obligation`] (injective, so validity is invariant under it): a
/// form is decided once whatever registers carry it, which bounds the
/// per-compile cost of the ENC-5 binding and of the verifier by the number of
/// distinct forms. A refutation or an undecided verdict is recomputed, since
/// its text names the registers.
static HOLDING: LazyLock<Mutex<HashMap<(E, E), &'static str>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

/// Decide an obligation exactly, in process.
pub fn decide(ob: &TrapExpansionObligation) -> Decision {
    let names = input_renaming(&ob.obligation.inputs);
    let key = (renamed(&ob.source, &names), renamed(&ob.machine, &names));
    if let Some(&method) = HOLDING
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .get(&key)
    {
        return Decision::Holds { method };
    }
    let decision = decide_uncached(ob);
    if let Decision::Holds { method } = decision {
        HOLDING
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .insert(key, method);
    }
    decision
}

fn decide_uncached(ob: &TrapExpansionObligation) -> Decision {
    let inputs = ob.obligation.inputs.clone();
    let decision = match bitserial_decide::decide_equal(&ob.source, &ob.machine) {
        Ok(Exact::Holds) => Decision::Holds {
            method: METHOD_BITSERIAL,
        },
        Ok(Exact::Refuted(witness)) => Decision::Refuted {
            reason: format!("counterexample {witness:?}"),
        },
        Err(unsupported) => match (normal_form(&ob.source), normal_form(&ob.machine)) {
            (Some(a), Some(b)) if a == b => Decision::Holds {
                method: METHOD_NORMALIZATION,
            },
            _ => match search_counterexample(&ob.source, &ob.machine, &inputs) {
                Some(witness) => Decision::Refuted {
                    reason: format!("counterexample {witness:?}"),
                },
                None => Decision::Undecided {
                    reason: format!(
                        "{unsupported}; the normal forms differ and no counterexample was found"
                    ),
                },
            },
        },
    };
    // A holding verdict must survive sampling by the ordinary evaluator.
    if decision.holds()
        && let Some(witness) = search_counterexample(&ob.source, &ob.machine, &inputs)
    {
        return Decision::Undecided {
            reason: format!(
                "internal disagreement: decided to hold, but the evaluator separates the sides \
                 at {witness:?}"
            ),
        };
    }
    decision
}

// ===========================================================================
// Replay through the request's AY and Clean
// ===========================================================================

/// The capability to replay one holding conditional obligation through a
/// verification request's admitted AY and explicit Clean checker. It is built
/// only here, from an obligation decided to hold in process, and carries that
/// obligation register-renamed ([`replay_obligation`]). It is a sealed
/// [`crate::source_bound_replay::SourceBoundReplay`] owner, so the replay is
/// the request's (`FunctionDischargeContext::trap_expansion`): the request's
/// AY and policy, its refusals (the tier-0 recorder armed,
/// `TCG_REFINE_SOLVER=0`, an executed query that is not the request's), its
/// budget and its reuse identity. Nothing here memoises a replay verdict.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrapExpansionReplay {
    obligation: Box<ProofObligation>,
}

impl TrapExpansionReplay {
    fn of(ob: &TrapExpansionObligation) -> Self {
        Self {
            obligation: Box::new(replay_obligation(ob)),
        }
    }

    /// The register-renamed obligation the replay sends.
    pub fn obligation(&self) -> &ProofObligation {
        &self.obligation
    }

    /// The capability for an obligation that need not hold (the replay
    /// census sends corruption controls through the same route; a request
    /// must never certify one).
    #[cfg(test)]
    pub(crate) fn for_test(ob: &TrapExpansionObligation) -> Self {
        Self::of(ob)
    }
}

fn renamed(expr: &E, names: &HashMap<String, String>) -> E {
    if let E::Var { name, width } = expr {
        return E::var(
            names.get(name).cloned().unwrap_or_else(|| name.clone()),
            *width,
        );
    }
    match bitserial_decide::children(expr) {
        Some(children) => rebuild(
            expr,
            children.into_iter().map(|c| renamed(c, names)).collect(),
        ),
        None => expr.clone(),
    }
}

/// The renaming of `inputs` to `v0`, `v1`, ... in input order. It is
/// injective (register variables are named `x0`..`x30`), so validity is
/// invariant under it.
fn input_renaming(inputs: &[(String, u32)]) -> HashMap<String, String> {
    inputs
        .iter()
        .enumerate()
        .map(|(index, (name, _))| (name.clone(), format!("v{index}")))
        .collect()
}

/// `ob` with its register variables renamed `v0`, `v1`, ... in input order
/// and a register-free name. Validity is invariant under the renaming, and
/// two expansions that differ only in their registers then replay as one
/// query, so the request's reuse serves each distinct form.
pub fn replay_obligation(ob: &TrapExpansionObligation) -> ProofObligation {
    let names = input_renaming(&ob.obligation.inputs);
    let mut out = ob.obligation.clone();
    out.name = format!(
        "A64 trap expansion {:?} ({}), registers renamed",
        ob.carrier.opcode,
        ob.carrier.condition_name()
    );
    out.trust_ir_expr = renamed(&ob.obligation.trust_ir_expr, &names);
    out.aarch64_expr = renamed(&ob.obligation.aarch64_expr, &names);
    out.inputs = ob
        .obligation
        .inputs
        .iter()
        .map(|(name, width)| (names[name].clone(), *width))
        .collect();
    out
}

// ===========================================================================
// Verdicts for the function verifier and ENC-5
// ===========================================================================

/// The verdict on one carrier (or one recorded expansion).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TrapVerdict {
    /// The expansion traps exactly when the carrier's condition holds.
    /// `replay` is the capability to replay a conditional expansion's
    /// obligation through a verification request; an unconditional trap has
    /// none (it has no condition to bind).
    Holds {
        name: String,
        conditional: bool,
        method: &'static str,
        replay: Option<TrapExpansionReplay>,
    },
    /// The expansion does not.
    Refuted { name: String, detail: String },
    /// Outside the model, or undecided: refused by name.
    Refused { reason: String },
}

fn verdict_of(carrier: &TrapCarrier, words: Result<Vec<u32>, TrapRefusal>) -> TrapVerdict {
    let name = format!(
        "A64 trap expansion {:?} ({})",
        carrier.opcode,
        carrier.condition_name()
    );
    let words = match words {
        Ok(words) => words,
        Err(TrapRefusal::Refuted(detail)) => return TrapVerdict::Refuted { name, detail },
        Err(other) => {
            return TrapVerdict::Refused {
                reason: other.to_string(),
            };
        }
    };
    let ob = match trap_expansion_obligation(carrier, &words) {
        Ok(ob) => ob,
        Err(TrapRefusal::Refuted(detail)) => return TrapVerdict::Refuted { name, detail },
        Err(other) => {
            return TrapVerdict::Refused {
                reason: other.to_string(),
            };
        }
    };
    match decide(&ob) {
        Decision::Holds { method } => TrapVerdict::Holds {
            name: ob.obligation.name.clone(),
            conditional: carrier.is_conditional(),
            method,
            replay: carrier
                .is_conditional()
                .then(|| TrapExpansionReplay::of(&ob)),
        },
        Decision::Refuted { reason } => TrapVerdict::Refuted {
            name: ob.obligation.name,
            detail: reason,
        },
        Decision::Undecided { reason } => TrapVerdict::Refused {
            reason: format!("{}: undecided: {reason}", ob.obligation.name),
        },
    }
}

/// The verdict on a carrier as instruction selection emitted it: its stated
/// expansion, over role registers when it has virtual ones.
pub fn carrier_verdict(inst: &MachInst) -> TrapVerdict {
    match trap_carrier(inst) {
        Ok(carrier) => verdict_of(&carrier, stated_words(&carrier)),
        Err(refusal) => TrapVerdict::Refused {
            reason: refusal.to_string(),
        },
    }
}

/// The verdict on a recorded expansion: `carrier` as it was before the
/// expansion, and the instructions the expansion left in the function.
pub fn recorded_expansion_verdict(carrier: &MachInst, expansion: &[&MachInst]) -> TrapVerdict {
    match trap_carrier(carrier) {
        Ok(carrier) => {
            let words = expansion.iter().map(|inst| expansion_word(inst)).collect();
            verdict_of(&carrier, words)
        }
        Err(refusal) => TrapVerdict::Refused {
            reason: refusal.to_string(),
        },
    }
}

/// ENC-5 binding of one recorded expansion to the words the object carries:
/// `Err` when the emitted words do not trap exactly when the carrier's
/// condition holds, and when the carrier is outside the model (refused by
/// name: an expansion this module cannot judge is not passed on its per-word
/// checks alone).
pub fn check_emitted_trap_expansion(carrier: &MachInst, emitted: &[u32]) -> Result<(), String> {
    let carrier = trap_carrier(carrier).map_err(|refusal| {
        format!("{refusal}; ENC-5 cannot bind the expansion of a carrier outside the model")
    })?;
    match verdict_of(&carrier, Ok(emitted.to_vec())) {
        TrapVerdict::Holds { .. } => Ok(()),
        TrapVerdict::Refuted { name, detail } => Err(format!("{name}: {detail}")),
        TrapVerdict::Refused { reason } => Err(reason),
    }
}

// ===========================================================================
// Battery, controls and the coverage-gate credit
// ===========================================================================

fn x(number: u8) -> Gpr {
    Gpr { number, width: 64 }
}

/// One carrier of every modeled form: each opcode, both register widths, the
/// immediate, wide-immediate (with and without `MOVK`) and register bounds,
/// both shift widths, and every overflow tag.
pub fn trap_battery() -> Vec<TrapCarrier> {
    let mut out = Vec::new();
    for width in [32, 64] {
        let r = |n| x(n).with_width(width);
        out.push(TrapCarrier {
            opcode: O::TrapDivZeroIfZero,
            kind: TrapKind::DivZero { divisor: r(3) },
        });
        out.push(TrapCarrier {
            opcode: O::TrapShiftRangeIfOOB,
            kind: TrapKind::ShiftRange {
                amount: r(5),
                bitwidth: width,
            },
        });
        for bound in [
            Bound::Imm(0),
            Bound::Imm(1),
            Bound::Imm(10),
            Bound::Imm(0xFFF),
            Bound::Reg(r(4)),
        ] {
            out.push(TrapCarrier {
                opcode: O::TrapBoundsCheckExact,
                kind: TrapKind::Bounds { index: r(2), bound },
            });
        }
        for op in [
            OverflowOp::SignedAdd,
            OverflowOp::SignedSub,
            OverflowOp::UnsignedAdd,
            OverflowOp::UnsignedSub,
        ] {
            out.push(TrapCarrier {
                opcode: O::TrapOverflowExact,
                kind: TrapKind::Overflow {
                    lhs: r(0),
                    rhs: r(1),
                    op,
                    width,
                },
            });
        }
    }
    out.push(TrapCarrier {
        opcode: O::TrapNullIfZero,
        kind: TrapKind::Null { ptr: x(0) },
    });
    for k in [0x1000, 0xFFFF, 0x1_0000, 0x12_3456, i32::MAX as u64] {
        // A wide bound on a 64-bit index (X16 scratch) and on a 32-bit index
        // (W16 scratch).
        for index in [x(2), x(2).with_width(32)] {
            out.push(TrapCarrier {
                opcode: O::TrapBoundsCheckExact,
                kind: TrapKind::Bounds {
                    index,
                    bound: Bound::Imm(k),
                },
            });
        }
    }
    for op in [OverflowOp::SignedMul, OverflowOp::UnsignedMul] {
        out.push(TrapCarrier {
            opcode: O::TrapOverflowExact,
            kind: TrapKind::Overflow {
                lhs: x(0),
                rhs: x(1),
                op,
                width: 64,
            },
        });
    }
    // The same register on both sides of an overflow.
    out.push(TrapCarrier {
        opcode: O::TrapOverflowExact,
        kind: TrapKind::Overflow {
            lhs: x(7),
            rhs: x(7),
            op: OverflowOp::SignedAdd,
            width: 64,
        },
    });
    for opcode in [
        O::Brk,
        O::TrapOverflow,
        O::TrapBoundsCheck,
        O::TrapNull,
        O::TrapDivZero,
        O::TrapShiftRange,
    ] {
        out.push(TrapCarrier {
            opcode,
            kind: TrapKind::Unconditional { code: TRAP_CODE },
        });
    }
    out
}

/// The carrier instruction a [`TrapCarrier`] stands for, over physical
/// registers (a bounds carrier's identity `base` is its index register).
pub fn carrier_instruction(carrier: &TrapCarrier) -> MachInst {
    let op = |g: Gpr| g.operand();
    let operands = match carrier.kind {
        TrapKind::Null { ptr: g } | TrapKind::DivZero { divisor: g } => vec![op(g)],
        TrapKind::Bounds { index, bound } => vec![
            op(index),
            op(index),
            match bound {
                Bound::Imm(k) => MachOperand::Imm(k as i64),
                Bound::Reg(b) => op(b),
            },
        ],
        TrapKind::ShiftRange { amount, bitwidth } => {
            vec![op(amount), MachOperand::Imm(i64::from(bitwidth))]
        }
        TrapKind::Overflow {
            lhs,
            rhs,
            op: kind,
            width,
        } => vec![
            op(lhs),
            op(rhs),
            MachOperand::Imm(trust_cg_ir::overflow_tag::pack_overflow_tag(
                kind,
                width as u16,
            )),
        ],
        TrapKind::Unconditional { code } if code != TRAP_CODE => {
            vec![MachOperand::Imm(i64::from(code))]
        }
        TrapKind::Unconditional { .. } => Vec::new(),
    };
    MachInst::new(carrier.opcode, operands)
}

/// A corruption of one expansion that must be refuted.
#[derive(Clone, Debug)]
pub struct TrapControl {
    pub label: String,
    pub words: Vec<u32>,
}

fn with_word(words: &[u32], index: usize, word: u32) -> Vec<u32> {
    let mut out = words.to_vec();
    out[index] = word;
    out
}

/// Every corruption of `carrier`'s stated expansion this module requires to
/// be refuted: an inverted condition, a wrong `BRK` immediate, branches that
/// go around the trap (always taken, or past the next word), a wrong
/// register, a wrong width and, for bounds and shift ranges, a bound off by
/// one in each direction.
pub fn trap_controls(carrier: &TrapCarrier) -> Vec<TrapControl> {
    let Ok(words) = stated_words(carrier) else {
        return Vec::new();
    };
    let n = words.len();
    let mut out = Vec::new();
    let brk = n - 1;
    out.push(TrapControl {
        label: "BRK #2 instead of the trap code".into(),
        words: with_word(&words, brk, 0xD420_0000 | (2 << 5)),
    });
    out.push(TrapControl {
        label: "BRK #0 instead of the trap code".into(),
        words: with_word(&words, brk, 0xD420_0000),
    });
    if !carrier.is_conditional() {
        out.push(TrapControl {
            label: "an unconditional trap that is not a BRK".into(),
            words: vec![0xD503_201F],
        });
        return out;
    }
    let branch = n - 2;
    let bw = words[branch];
    let is_cond = bw & 0xFF00_0010 == 0x5400_0000;
    out.push(TrapControl {
        label: if is_cond {
            "inverted branch condition".into()
        } else {
            "CBZ instead of CBNZ".into()
        },
        words: with_word(&words, branch, bw ^ if is_cond { 1 } else { 1 << 24 }),
    });
    out.push(TrapControl {
        label: "branch past the next word (around the trap)".into(),
        words: with_word(&words, branch, (bw & !(0x7FFFF << 5)) | (3 << 5)),
    });
    out.push(TrapControl {
        label: "branch to itself".into(),
        words: with_word(&words, branch, bw & !(0x7FFFF << 5)),
    });
    if is_cond {
        out.push(TrapControl {
            label: "branch always taken (B.AL around the trap)".into(),
            words: with_word(&words, branch, (bw & !0xF) | 0b1110),
        });
    } else {
        out.push(TrapControl {
            label: "CBNZ on the wrong width".into(),
            words: with_word(&words, branch, bw ^ (1 << 31)),
        });
        out.push(TrapControl {
            label: "CBNZ on the wrong register".into(),
            words: with_word(&words, branch, (bw & !0x1F) | ((bw & 0x1F) ^ 0b01001)),
        });
    }
    out.push(TrapControl {
        label: "the conditional branch removed".into(),
        words: words[..branch]
            .iter()
            .chain(&words[brk..])
            .copied()
            .collect(),
    });
    // The flag-setting word just before the branch.
    if branch >= 1 {
        let setter_index = branch - 1;
        let sw = words[setter_index];
        // `index >=u 0` always holds: the operand register and width of that
        // compare cannot change whether it traps, so those two are no control.
        let always = matches!(
            carrier.kind,
            TrapKind::Bounds {
                bound: Bound::Imm(0),
                ..
            }
        );
        if !always {
            out.push(TrapControl {
                label: "flag-setting word on the wrong width".into(),
                words: with_word(&words, setter_index, sw ^ (1 << 31)),
            });
            out.push(TrapControl {
                label: "flag-setting word reads the wrong register".into(),
                words: with_word(&words, setter_index, sw ^ (0b01001 << 5)),
            });
        }
        // An immediate compare: the bound off by one.
        if sw & 0x1F80_0000 == 0x1100_0000 {
            let k = field(sw, 21, 10);
            if k < 0xFFF {
                out.push(TrapControl {
                    label: "bound one too large".into(),
                    words: with_word(
                        &words,
                        setter_index,
                        (sw & !(0xFFF << 10)) | ((k + 1) << 10),
                    ),
                });
            }
            if k > 0 {
                out.push(TrapControl {
                    label: "bound one too small".into(),
                    words: with_word(
                        &words,
                        setter_index,
                        (sw & !(0xFFF << 10)) | ((k - 1) << 10),
                    ),
                });
            }
        }
        // ADDS <-> SUBS.
        if sw & 0x1F20_0000 == 0x0B00_0000 {
            out.push(TrapControl {
                label: "ADDS/SUBS exchanged".into(),
                words: with_word(&words, setter_index, sw ^ (1 << 30)),
            });
        }
    }
    // A wide-immediate bound: the MOVZ halfword off by one.
    if let Some(movz) = words.iter().position(|w| w & 0x7F80_0000 == 0x5280_0000) {
        let w = words[movz];
        let k = field(w, 20, 5);
        out.push(TrapControl {
            label: "materialized bound one too large".into(),
            words: with_word(
                &words,
                movz,
                (w & !(0xFFFF << 5)) | (((k + 1) & 0xFFFF) << 5),
            ),
        });
        out.push(TrapControl {
            label: "MOVZ writes a live register instead of x16".into(),
            words: with_word(&words, movz, (w & !0x1F) | 2),
        });
    }
    // The multiplication forms: SMULH <-> UMULH and the ASR amount.
    if let Some(high) = words.iter().position(|w| w & 0xFF60_FC00 == 0x9B40_7C00) {
        out.push(TrapControl {
            label: "SMULH/UMULH exchanged".into(),
            words: with_word(&words, high, words[high] ^ (1 << 23)),
        });
    }
    if let Some(asr) = words.iter().position(|w| w & 0x7F80_0000 == 0x1300_0000) {
        let w = words[asr];
        out.push(TrapControl {
            label: "ASR #62 instead of #63".into(),
            words: with_word(&words, asr, (w & !(0x3F << 16)) | (62 << 16)),
        });
    }
    out
}

/// What the coverage-gate credit hook established.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrapExpansionCredit {
    pub forms: usize,
    pub controls_refuted: usize,
}

/// The coverage-gate credit hook for the conditional carriers: every form of
/// [`trap_battery`] must decide to hold, every control of [`trap_controls`]
/// must be refuted, and every stated word must decode back to its
/// instruction's class. Testing-grade evidence: no certificate is involved.
pub fn trap_expansion_credit() -> Result<TrapExpansionCredit, String> {
    let mut forms = 0;
    let mut controls_refuted = 0;
    for carrier in trap_battery() {
        let words = stated_words(&carrier).map_err(|e| format!("{carrier:?}: {e}"))?;
        for &w in &words {
            decode(w).map_err(|e| format!("{carrier:?}: stated word does not decode: {e}"))?;
        }
        let ob =
            trap_expansion_obligation(&carrier, &words).map_err(|e| format!("{carrier:?}: {e}"))?;
        match decide(&ob) {
            Decision::Holds { .. } => forms += 1,
            other => return Err(format!("{carrier:?}: {other:?}")),
        }
        for control in trap_controls(&carrier) {
            let refuted = match trap_expansion_obligation(&carrier, &control.words) {
                Err(TrapRefusal::Refuted(_)) => true,
                Err(other) => return Err(format!("{carrier:?} / {}: {other}", control.label)),
                Ok(ob) => matches!(decide(&ob), Decision::Refuted { .. }),
            };
            if !refuted {
                return Err(format!(
                    "{carrier:?}: control `{}` was not refuted",
                    control.label
                ));
            }
            controls_refuted += 1;
        }
    }
    Ok(TrapExpansionCredit {
        forms,
        controls_refuted,
    })
}

#[cfg(test)]
#[path = "aarch64_trap_expansion_tests.rs"]
mod tests;
