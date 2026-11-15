// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Instruction-derived obligations for the AArch64 opcodes whose only
//! candidate evidence was a registry theorem selected by name (the
//! registry-name-lookup class of the Darwin proof-wall census, ledger L07-P2).
//!
//! # The obligation
//!
//! For one emitted instruction, the obligation states that the architectural
//! effect of the instruction WORD equals the effect the machine-IR instruction
//! names.
//!
//! * The word is re-derived here from the instruction's operands
//!   ([`instruction_word`]) by an encoder written from the Arm A64 encoding
//!   diagrams (Arm DDI 0487, C4.1), not by calling `trust-cg-codegen`'s
//!   encoder. Per compile, ENC-5 (`trust-cg-codegen/src/aarch64/decode_check.rs`)
//!   requires the emitted word to be exactly this word outside its fixup and
//!   relocation holes ([`check_emitted_instruction_word`]). In ENC-5's default
//!   `enforce` mode the word decoded here is therefore the word the object
//!   carries; under `TCG_DECODE_CHECK_A64=warn|off` that binding is not
//!   enforced.
//! * The word is decoded by an independent field decoder ([`decode_word`]) and
//!   given its Arm ARM pseudo-code semantics over a symbolic machine state: the
//!   general-purpose registers and SP (64 bits each), NZCV, the PC, and the bytes
//!   a load reads or a store writes. A W write zeroes bits 63:32, register 31 is
//!   SP or ZR as the instruction class decides, and the flags of a SUBS are
//!   Arm's `AddWithCarry(x, NOT(y), 1)`.
//! * The intent is stated separately from the operands: which locations the
//!   instruction writes and the value each receives. A compare's flags are
//!   stated as the comparison predicates they encode (`C` is unsigned
//!   `a >= b`, `V` is signed overflow of `a - b`), and a branch condition as the
//!   meaning of the instruction-selection condition code the operand carries.
//!
//! The obligation holds when both sides write exactly the same locations with
//! equal values. A different write set (a wrong destination, a flag write, a
//! discarded write, a different transfer size or direction, a link write)
//! refutes structurally; a value difference refutes by a counterexample.
//!
//! # How a location is decided, and what that is worth
//!
//! Each written location is decided by the first of: syntactic identity of the
//! two terms; exact bit routing
//! ([`crate::aarch64_value_decode_proofs::exact_routing_equality`]); a search
//! of boundary points built from the constants either term mentions, which
//! can only refute; the ordinary evaluator over role-named inputs (complete for
//! a small domain, such as the four NZCV bits a branch condition reads, and
//! sampled otherwise, as for a compare's flags over two 64-bit operands).
//! Identity and routing hold for every input. The boundary search exists
//! because sampling alone accepts a compare whose immediate is off by one: the
//! two flag results differ only where the register equals one of the two
//! immediates. All of these are in-process decisions; none is an
//! independently checked certificate.
//!
//! None of it is proof credit. The obligation binds the emitted word to the
//! machine-IR instruction's operands. It does not bind that instruction to a
//! source (trust-ir or LIR) instruction, so a lowering that chose the wrong
//! constant, register, condition or branch target encodes and decodes
//! perfectly, and no mutation of the instruction itself can refute it. The
//! function verifier reports every holding row as unverified
//! ([`crate::function_verifier::INSTRUCTION_DERIVED_IS_NOT_CREDIT`]) and every
//! refuted row as failed; proof-required promotion refuses both.
//!
//! The function verifier decodes the RE-DERIVED word ([`instruction_word_verdict`]),
//! not the emitted one: on the certificates-on path promotion runs before the
//! object is encoded. A refutation there can therefore come only from an
//! inconsistency between this module's encoder, decoder and intent, and a
//! walk that refutes nothing says nothing about the emitted words. The binding
//! of the emitted word to the decoded one is ENC-5's
//! ([`check_emitted_instruction_word`]), which runs when the object is encoded.
//!
//! It also does not establish: what a fixup or relocation writes into a
//! displacement field (the field is one symbolic value on both sides); memory
//! contents (a load's bytes are one symbolic value); alignment, permissions or
//! ordering of a memory access; the callee's behaviour after a call; or
//! agreement with silicon.

use std::collections::BTreeMap;

use crate::aarch64_value_decode_proofs::exact_routing_equality;
use crate::lowering_proof::{
    MachineSideProvenance, ProofObligation, TransvalCheckKind, VerificationConfig,
    memoized_verify_by_evaluation,
};
use crate::smt::SmtExpr as E;
use crate::verify::{VerificationResult, VerificationStrength};
use trust_cg_ir::{AArch64Opcode as O, MachInst, MachOperand, SpecialReg};

/// Every opcode this module builds an instruction-derived obligation for. An
/// instance whose operands are outside the admitted shapes gets none.
pub const INSTRUCTION_WORD_OPCODES: &[O] = &[
    O::Movz,
    O::MovI,
    O::MOVZWi,
    O::MOVZXi,
    O::Movn,
    O::Movk,
    O::MovR,
    O::MOVWrr,
    O::MOVXrr,
    O::AddRI,
    O::SubRI,
    O::CmpRI,
    O::CMPWri,
    O::CMPXri,
    O::CmpRR,
    O::CMPWrr,
    O::CMPXrr,
    O::AddRRShift,
    O::SubRRShift,
    O::AddRRShiftLsr,
    O::EorRRShift,
    O::Umulh,
    O::B,
    O::TailCall,
    O::Bl,
    O::BL,
    O::BCond,
    O::Bcc,
    O::LdrRI,
    O::StrRI,
    O::LdrbRI,
    O::StrbRI,
    O::LdrhRI,
    O::StrhRI,
    O::LdrsbRI,
    O::LdrshRI,
    O::LdrPreIndex,
    O::StrPreIndex,
    O::LdrPostIndex,
    O::StrPostIndex,
    O::LdrRO,
    O::StrRO,
    O::LdrbRO,
    O::LdrhRO,
    O::StrbRO,
    O::StrhRO,
    O::LdrswRO,
];

// ===========================================================================
// Operands
// ===========================================================================

/// A general-purpose register as an operand names it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Reg {
    X(u8),
    Sp,
    Zr,
}

impl Reg {
    fn field(self) -> u32 {
        match self {
            Self::X(n) => u32::from(n),
            Self::Sp | Self::Zr => 31,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Gpr {
    width: u32,
    reg: Reg,
}

/// A general-purpose register operand with the view its register class names.
fn gpr(op: &MachOperand) -> Option<Gpr> {
    let (width, reg) = match op {
        MachOperand::PReg(p) => match p.encoding() {
            e @ 0..=30 => (64, Reg::X(e as u8)),
            31 => (64, Reg::Sp),
            e @ 32..=62 => (32, Reg::X((e - 32) as u8)),
            63 => (32, Reg::Sp),
            160 => (64, Reg::Zr),
            161 => (32, Reg::Zr),
            _ => return None,
        },
        MachOperand::Special(SpecialReg::SP) => (64, Reg::Sp),
        MachOperand::Special(SpecialReg::XZR) => (64, Reg::Zr),
        MachOperand::Special(SpecialReg::WZR) => (32, Reg::Zr),
        _ => return None,
    };
    Some(Gpr { width, reg })
}

fn imm(op: &MachOperand) -> Option<i64> {
    match op {
        MachOperand::Imm(value) => Some(*value),
        _ => None,
    }
}

/// A branch or call target: a symbolic target filled by a fixup or a
/// relocation (the displacement field is a hole), or a resolved word offset.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Target {
    Hole,
    Words(i64),
}

fn target(op: &MachOperand, bits: u32) -> Option<Target> {
    match op {
        MachOperand::Block(_) | MachOperand::Symbol(_) | MachOperand::ExactModuleSymbol(_) => {
            Some(Target::Hole)
        }
        MachOperand::Imm(words) => {
            let half = 1i64 << (bits - 1);
            (-half..half)
                .contains(words)
                .then_some(Target::Words(*words))
        }
        _ => None,
    }
}

// ===========================================================================
// The admitted shapes, and the word each re-derives to
// ===========================================================================

/// One admitted instruction, reduced to the fields its word and its intent
/// are built from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Shape {
    /// MOVZ (opc 10), MOVN (opc 00) or MOVK (opc 11) at halfword `hw`.
    MoveWide {
        opc: u32,
        width: u32,
        hw: u32,
        imm16: u32,
        dst: Reg,
    },
    /// A register copy, `ORR Rd, ZR, Rm`, or `ADD Rd, Rn, #0` when SP is named.
    Copy { width: u32, dst: Reg, src: Reg },
    /// ADD/SUB (immediate), no flags.
    AddSubImm {
        sub: bool,
        width: u32,
        dst: Reg,
        src: Reg,
        imm12: u32,
    },
    /// CMP Rn, #imm12 (`SUBS ZR, Rn|SP, #imm12`).
    CmpImm { width: u32, src: Reg, imm12: u32 },
    /// CMP Rn, Rm (`SUBS ZR, Rn, Rm`).
    CmpReg { width: u32, lhs: Reg, rhs: Reg },
    /// ADD/SUB (shifted register) with shift type LSL (0) or LSR (1).
    AddSubShifted {
        sub: bool,
        shift: u32,
        amount: u32,
        width: u32,
        dst: Reg,
        lhs: Reg,
        rhs: Reg,
    },
    /// EOR Rd, Rn, Rm, ROR #amount.
    EorRor {
        amount: u32,
        width: u32,
        dst: Reg,
        lhs: Reg,
        rhs: Reg,
    },
    /// UMULH Xd, Xn, Xm.
    Umulh { dst: Reg, lhs: Reg, rhs: Reg },
    /// B (link false) or BL (link true).
    Branch { link: bool, target: Target },
    /// B.cond with the instruction-selection condition code `cc` (0..=13).
    CondBranch { cc: u32, target: Target },
    /// A scalar general-purpose load or store with an immediate offset,
    /// `bytes` wide.
    Memory {
        load: bool,
        bytes: u32,
        /// LDRSB/LDRSH: the width the loaded bytes are sign-extended to (32
        /// for a W destination, 64 for an X one). `None` for a zero-extending
        /// load or a store.
        sign_to: Option<u32>,
        data: Gpr,
        base: Reg,
        offset: i64,
    },
    /// A W/X load or store with base writeback: `[Xn|SP, #imm9]!` accesses
    /// `Xn + imm9` (`pre`), `[Xn|SP], #imm9` accesses `Xn`; both then set
    /// `Xn = Xn + imm9`.
    MemoryWriteback {
        pre: bool,
        load: bool,
        data: Gpr,
        base: Reg,
        offset: i64,
    },
    /// A scalar general-purpose load or store with a register offset,
    /// `[Xn|SP, Rm, extend {#amount}]`, `bytes` wide.
    MemoryRegister {
        load: bool,
        bytes: u32,
        /// LDRSW: sign-extended to 64. `None` otherwise.
        sign_to: Option<u32>,
        data: Gpr,
        base: Reg,
        index: Gpr,
        extend: IndexExtend,
        /// Whether the extended index is scaled by the access size.
        shifted: bool,
    },
}

/// How a register-offset access extends its index register, as the machine
/// IR's mode immediate names it (`(option << 1) | S`: 4/5 UXTW, 6/7 LSL, 12/13
/// SXTW, 14/15 SXTX, `S` in bit 0).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum IndexExtend {
    /// The low 32 bits, zero-extended.
    Uxtw,
    /// All 64 bits.
    Lsl,
    /// The low 32 bits, sign-extended.
    Sxtw,
    /// All 64 bits (sign-extending 64 bits is the identity).
    Sxtx,
}

impl IndexExtend {
    /// `(extend, shifted)` of a mode immediate, or `None` for any other value.
    fn from_mode(mode: i64) -> Option<(Self, bool)> {
        let extend = match mode >> 1 {
            0b010 => Self::Uxtw,
            0b011 => Self::Lsl,
            0b110 => Self::Sxtw,
            0b111 => Self::Sxtx,
            _ => return None,
        };
        Some((extend, mode & 1 == 1))
    }

    /// The Arm `option` field.
    fn option(self) -> u32 {
        match self {
            Self::Uxtw => 0b010,
            Self::Lsl => 0b011,
            Self::Sxtw => 0b110,
            Self::Sxtx => 0b111,
        }
    }

    /// Whether the extend reads the whole 64-bit index register.
    fn reads_64_bits(self) -> bool {
        matches!(self, Self::Lsl | Self::Sxtx)
    }
}

/// The re-derived word of an admitted instruction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InstructionWord {
    /// The encoded word, with every hole bit zero.
    pub word: u32,
    /// Bits a fixup or a relocation fills after emission (a branch
    /// displacement to a symbolic target).
    pub hole_mask: u32,
}

const IMM26_MASK: u32 = 0x03FF_FFFF;
const IMM19_MASK: u32 = 0x7FFFF << 5;

/// The admitted shape of `inst`, or `None`: an opcode outside
/// [`INSTRUCTION_WORD_OPCODES`], or operands of any other shape (a virtual
/// register, an unresolved frame placeholder, a register class the encoding
/// cannot name, an immediate out of the field's range).
fn shape(inst: &MachInst) -> Option<Shape> {
    let ops = inst.operands.as_slice();
    match inst.opcode {
        O::Movz | O::MovI | O::MOVZWi | O::MOVZXi | O::Movn | O::Movk => {
            let (dst, imm16, shift) = match (inst.opcode, ops) {
                (_, [dst, imm16]) => (dst, imm16, 0),
                (O::Movz | O::Movn | O::Movk, [dst, imm16, shift]) => (dst, imm16, imm(shift)?),
                _ => return None,
            };
            let dst = gpr(dst)?;
            if dst.reg == Reg::Sp {
                return None;
            }
            match inst.opcode {
                O::MOVZWi if dst.width != 32 => return None,
                O::MOVZXi if dst.width != 64 => return None,
                _ => {}
            }
            let imm16 = u32::try_from(imm(imm16)?).ok().filter(|v| *v <= 0xFFFF)?;
            if shift < 0 || shift % 16 != 0 {
                return None;
            }
            let hw = u32::try_from(shift / 16).ok()?;
            let max_hw = if dst.width == 64 { 3 } else { 1 };
            // The encoder emits MOVZ and MOVN only at halfword 0; MOVK at any
            // halfword the width has.
            if hw > max_hw || (inst.opcode != O::Movk && hw != 0) {
                return None;
            }
            let opc = match inst.opcode {
                O::Movn => 0b00,
                O::Movk => 0b11,
                _ => 0b10,
            };
            Some(Shape::MoveWide {
                opc,
                width: dst.width,
                hw,
                imm16,
                dst: dst.reg,
            })
        }
        O::MovR | O::MOVWrr | O::MOVXrr => {
            let [dst, src] = ops else { return None };
            let (dst, src) = (gpr(dst)?, gpr(src)?);
            let width = match inst.opcode {
                O::MOVWrr => 32,
                O::MOVXrr => 64,
                _ => dst.width,
            };
            let sp = dst.reg == Reg::Sp || src.reg == Reg::Sp;
            let zr = dst.reg == Reg::Zr || src.reg == Reg::Zr;
            if sp && zr {
                return None;
            }
            Some(Shape::Copy {
                width,
                dst: dst.reg,
                src: src.reg,
            })
        }
        O::AddRI | O::SubRI => {
            let [dst, src, value] = ops else { return None };
            let (dst, src) = (gpr(dst)?, gpr(src)?);
            // Register 31 is SP in ADD/SUB (immediate): a zero register cannot
            // be named on either side.
            if dst.reg == Reg::Zr || src.reg == Reg::Zr || dst.width != src.width {
                return None;
            }
            let imm12 = u32::try_from(imm(value)?).ok().filter(|v| *v <= 0xFFF)?;
            Some(Shape::AddSubImm {
                sub: inst.opcode == O::SubRI,
                width: dst.width,
                dst: dst.reg,
                src: src.reg,
                imm12,
            })
        }
        O::CmpRI | O::CMPWri | O::CMPXri => {
            let [src, value] = ops else { return None };
            let src = gpr(src)?;
            if src.reg == Reg::Zr || !typed_width_agrees(inst.opcode, src.width) {
                return None;
            }
            let imm12 = u32::try_from(imm(value)?).ok().filter(|v| *v <= 0xFFF)?;
            Some(Shape::CmpImm {
                width: src.width,
                src: src.reg,
                imm12,
            })
        }
        O::CmpRR | O::CMPWrr | O::CMPXrr => {
            let [lhs, rhs] = ops else { return None };
            let (lhs, rhs) = (gpr(lhs)?, gpr(rhs)?);
            if lhs.reg == Reg::Sp
                || rhs.reg == Reg::Sp
                || lhs.width != rhs.width
                || !typed_width_agrees(inst.opcode, lhs.width)
            {
                return None;
            }
            Some(Shape::CmpReg {
                width: lhs.width,
                lhs: lhs.reg,
                rhs: rhs.reg,
            })
        }
        O::AddRRShift | O::SubRRShift | O::AddRRShiftLsr | O::EorRRShift => {
            let [dst, lhs, rhs, amount] = ops else {
                return None;
            };
            let (dst, lhs, rhs) = (gpr(dst)?, gpr(lhs)?, gpr(rhs)?);
            // Register 31 is ZR in the shifted-register classes: SP cannot be
            // named.
            if [dst.reg, lhs.reg, rhs.reg].contains(&Reg::Sp) {
                return None;
            }
            let width = dst.width;
            let amount = u32::try_from(imm(amount)?)
                .ok()
                .filter(|k| (1..width).contains(k))?;
            if inst.opcode == O::EorRRShift {
                return Some(Shape::EorRor {
                    amount,
                    width,
                    dst: dst.reg,
                    lhs: lhs.reg,
                    rhs: rhs.reg,
                });
            }
            Some(Shape::AddSubShifted {
                sub: inst.opcode == O::SubRRShift,
                shift: u32::from(inst.opcode == O::AddRRShiftLsr),
                amount,
                width,
                dst: dst.reg,
                lhs: lhs.reg,
                rhs: rhs.reg,
            })
        }
        O::Umulh => {
            let [dst, lhs, rhs] = ops else { return None };
            let (dst, lhs, rhs) = (gpr(dst)?, gpr(lhs)?, gpr(rhs)?);
            if dst.width != 64 || [dst.reg, lhs.reg, rhs.reg].contains(&Reg::Sp) {
                return None;
            }
            Some(Shape::Umulh {
                dst: dst.reg,
                lhs: lhs.reg,
                rhs: rhs.reg,
            })
        }
        // A call or tail call carries its arguments as further operands; the
        // word encodes only the target.
        O::B | O::TailCall | O::Bl | O::BL => {
            let first = ops.first()?;
            if inst.opcode == O::B && ops.len() != 1 {
                return None;
            }
            Some(Shape::Branch {
                link: matches!(inst.opcode, O::Bl | O::BL),
                target: target(first, 26)?,
            })
        }
        O::BCond | O::Bcc => {
            let [cc, dest] = ops else { return None };
            let cc = u32::try_from(imm(cc)?).ok().filter(|cc| *cc <= 13)?;
            Some(Shape::CondBranch {
                cc,
                target: target(dest, 19)?,
            })
        }
        O::LdrRI
        | O::StrRI
        | O::LdrbRI
        | O::StrbRI
        | O::LdrhRI
        | O::StrhRI
        | O::LdrsbRI
        | O::LdrshRI => {
            let data = gpr(ops.first()?)?;
            if data.reg == Reg::Sp {
                return None;
            }
            let (base, offset) = match ops.get(1..)? {
                [MachOperand::MemOp { base, offset }] => (gpr(&MachOperand::PReg(*base))?, *offset),
                [base] => (gpr(base)?, 0),
                [base, MachOperand::Imm(offset)] => (gpr(base)?, *offset),
                _ => return None,
            };
            // Addresses are 64-bit: an X register or SP, never a W view or ZR.
            if base.width != 64 || base.reg == Reg::Zr {
                return None;
            }
            // A sign-extending load extends to the destination's view: LDRSB
            // Wt (opc 11) or LDRSB Xt (opc 10), and the same for LDRSH.
            let (load, bytes, sign_to) = match inst.opcode {
                O::LdrRI => (true, data.width / 8, None),
                O::StrRI => (false, data.width / 8, None),
                O::LdrbRI => (true, 1, None),
                O::StrbRI => (false, 1, None),
                O::LdrhRI => (true, 2, None),
                O::StrhRI => (false, 2, None),
                O::LdrsbRI => (true, 1, Some(data.width)),
                _ => (true, 2, Some(data.width)),
            };
            let _encodable = memory_offset_field(offset, bytes)?;
            Some(Shape::Memory {
                load,
                bytes,
                sign_to,
                data,
                base: base.reg,
                offset,
            })
        }
        O::LdrPreIndex | O::StrPreIndex | O::LdrPostIndex | O::StrPostIndex => {
            let [data, base, offset] = ops else {
                return None;
            };
            let (data, base, offset) = (gpr(data)?, gpr(base)?, imm(offset)?);
            if data.reg == Reg::Sp
                || base.width != 64
                || base.reg == Reg::Zr
                || !(-256..=255).contains(&offset)
            {
                return None;
            }
            // A writeback whose base is also the transfer register (n == t,
            // n != 31) is CONSTRAINED UNPREDICTABLE in the Arm ARM; the
            // encoder refuses it too.
            if base.reg != Reg::Sp && base.reg == data.reg {
                return None;
            }
            Some(Shape::MemoryWriteback {
                pre: matches!(inst.opcode, O::LdrPreIndex | O::StrPreIndex),
                load: matches!(inst.opcode, O::LdrPreIndex | O::LdrPostIndex),
                data,
                base: base.reg,
                offset,
            })
        }
        O::LdrRO | O::StrRO | O::LdrbRO | O::LdrhRO | O::StrbRO | O::StrhRO | O::LdrswRO => {
            let data = gpr(ops.first()?)?;
            let base = gpr(ops.get(1)?)?;
            let index = gpr(ops.get(2)?)?;
            let (extend, shifted) = match (inst.opcode, ops.get(3..)?) {
                // The encoder emits `LDRSW Xt, [Xn, Xm, LSL #2]` for every
                // operand list, so only that exact three-operand spelling is
                // admitted.
                (O::LdrswRO, []) => (IndexExtend::Lsl, true),
                (O::LdrswRO, _) => return None,
                (_, []) => (IndexExtend::Lsl, false),
                (_, [MachOperand::Imm(mode)]) => IndexExtend::from_mode(*mode)?,
                _ => return None,
            };
            // Register 31 is ZR in the transfer and index fields and SP in the
            // base field.
            if data.reg == Reg::Sp
                || base.width != 64
                || base.reg == Reg::Zr
                || index.reg == Reg::Sp
            {
                return None;
            }
            // A 64-bit extend reads the whole index register: a W view names
            // only its low half, so it is refused unless it is the zero
            // register (known zero at either width), as the encoder does.
            if extend.reads_64_bits() && index.width == 32 && index.reg != Reg::Zr {
                return None;
            }
            let (load, bytes, sign_to) = match inst.opcode {
                O::LdrRO => (true, data.width / 8, None),
                O::StrRO => (false, data.width / 8, None),
                O::LdrbRO => (true, 1, None),
                O::LdrhRO => (true, 2, None),
                O::StrbRO => (false, 1, None),
                O::StrhRO => (false, 2, None),
                // LDRSW writes all 64 bits: a W view names only half of them.
                _ if data.width == 64 => (true, 4, Some(64)),
                _ => return None,
            };
            Some(Shape::MemoryRegister {
                load,
                bytes,
                sign_to,
                data,
                base: base.reg,
                index,
                extend,
                shifted,
            })
        }
        _ => None,
    }
}

fn typed_width_agrees(opcode: O, width: u32) -> bool {
    match opcode {
        O::CMPWri | O::CMPWrr => width == 32,
        O::CMPXri | O::CMPXrr => width == 64,
        _ => true,
    }
}

/// The addressing form an immediate offset takes: `Ok(imm12)` for the
/// unsigned scaled form (a non-negative multiple of the access size whose
/// quotient fits 12 bits), `Err(imm9)` for the unscaled form (LDUR/STUR,
/// -256..=255), or `None` when neither can carry it.
fn memory_offset_field(offset: i64, bytes: u32) -> Option<Result<u32, u32>> {
    let scale = i64::from(bytes);
    if offset >= 0 && offset % scale == 0 && offset / scale <= 0xFFF {
        return Some(Ok((offset / scale) as u32));
    }
    (-256..=255)
        .contains(&offset)
        .then_some(Err((offset as u32) & 0x1FF))
}

fn sf(width: u32) -> u32 {
    u32::from(width == 64)
}

fn size_field(bytes: u32) -> u32 {
    match bytes {
        1 => 0b00,
        2 => 0b01,
        4 => 0b10,
        _ => 0b11,
    }
}

/// Encode an admitted shape from the Arm A64 encoding diagrams.
fn encode(shape: &Shape) -> InstructionWord {
    let plain = |word: u32| InstructionWord { word, hole_mask: 0 };
    let logical = |sf: u32, opc: u32, shift: u32, n: u32, rm: u32, imm6: u32, rn: u32, rd: u32| {
        (sf << 31)
            | (opc << 29)
            | (0b01010 << 24)
            | (shift << 22)
            | (n << 21)
            | (rm << 16)
            | (imm6 << 10)
            | (rn << 5)
            | rd
    };
    let add_sub_imm = |sf: u32, op: u32, s: u32, imm12: u32, rn: u32, rd: u32| {
        (sf << 31) | (op << 30) | (s << 29) | (0b100010 << 23) | (imm12 << 10) | (rn << 5) | rd
    };
    let add_sub_shifted =
        |sf: u32, op: u32, s: u32, shift: u32, rm: u32, imm6: u32, rn: u32, rd: u32| {
            (sf << 31)
                | (op << 30)
                | (s << 29)
                | (0b01011 << 24)
                | (shift << 22)
                | (rm << 16)
                | (imm6 << 10)
                | (rn << 5)
                | rd
        };
    match *shape {
        Shape::MoveWide {
            opc,
            width,
            hw,
            imm16,
            dst,
        } => plain(
            (sf(width) << 31)
                | (opc << 29)
                | (0b100101 << 23)
                | (hw << 21)
                | (imm16 << 5)
                | dst.field(),
        ),
        Shape::Copy { width, dst, src } => {
            if dst == Reg::Sp || src == Reg::Sp {
                plain(add_sub_imm(sf(width), 0, 0, 0, src.field(), dst.field()))
            } else {
                plain(logical(
                    sf(width),
                    0b01,
                    0,
                    0,
                    src.field(),
                    0,
                    31,
                    dst.field(),
                ))
            }
        }
        Shape::AddSubImm {
            sub,
            width,
            dst,
            src,
            imm12,
        } => plain(add_sub_imm(
            sf(width),
            u32::from(sub),
            0,
            imm12,
            src.field(),
            dst.field(),
        )),
        Shape::CmpImm { width, src, imm12 } => {
            plain(add_sub_imm(sf(width), 1, 1, imm12, src.field(), 31))
        }
        Shape::CmpReg { width, lhs, rhs } => plain(add_sub_shifted(
            sf(width),
            1,
            1,
            0,
            rhs.field(),
            0,
            lhs.field(),
            31,
        )),
        Shape::AddSubShifted {
            sub,
            shift,
            amount,
            width,
            dst,
            lhs,
            rhs,
        } => plain(add_sub_shifted(
            sf(width),
            u32::from(sub),
            0,
            shift,
            rhs.field(),
            amount,
            lhs.field(),
            dst.field(),
        )),
        Shape::EorRor {
            amount,
            width,
            dst,
            lhs,
            rhs,
        } => plain(logical(
            sf(width),
            0b10,
            0b11,
            0,
            rhs.field(),
            amount,
            lhs.field(),
            dst.field(),
        )),
        Shape::Umulh { dst, lhs, rhs } => plain(
            (1 << 31)
                | (0b11011 << 24)
                | (0b110 << 21)
                | (rhs.field() << 16)
                | (0b11111 << 10)
                | (lhs.field() << 5)
                | dst.field(),
        ),
        Shape::Branch { link, target } => {
            let base = (u32::from(link) << 31) | (0b00101 << 26);
            match target {
                Target::Hole => InstructionWord {
                    word: base,
                    hole_mask: IMM26_MASK,
                },
                Target::Words(words) => plain(base | ((words as u32) & IMM26_MASK)),
            }
        }
        Shape::CondBranch { cc, target } => {
            let base = (0b0101010 << 25) | cc;
            match target {
                Target::Hole => InstructionWord {
                    word: base,
                    hole_mask: IMM19_MASK,
                },
                Target::Words(words) => plain(base | (((words as u32) & 0x7FFFF) << 5)),
            }
        }
        Shape::Memory {
            load,
            bytes,
            sign_to,
            data,
            base,
            offset,
        } => {
            let head =
                (size_field(bytes) << 30) | (0b111 << 27) | (memory_opc(load, sign_to) << 22);
            let regs = (base.field() << 5) | data.reg.field();
            match memory_offset_field(offset, bytes) {
                Some(Ok(imm12)) => plain(head | (0b01 << 24) | (imm12 << 10) | regs),
                Some(Err(imm9)) => plain(head | (imm9 << 12) | regs),
                // `shape` admitted only encodable offsets.
                None => plain(0),
            }
        }
        // Load/store register (immediate pre-/post-indexed):
        // `size 111 0 00 opc 0 imm9 P1 Rn Rt`, P = 1 for pre-index.
        Shape::MemoryWriteback {
            pre,
            load,
            data,
            base,
            offset,
        } => plain(
            (size_field(data.width / 8) << 30)
                | (0b111 << 27)
                | (memory_opc(load, None) << 22)
                | (((offset as u32) & 0x1FF) << 12)
                | ((if pre { 0b11 } else { 0b01 }) << 10)
                | (base.field() << 5)
                | data.reg.field(),
        ),
        // Load/store register (register offset):
        // `size 111 0 00 opc 1 Rm option S 10 Rn Rt`.
        Shape::MemoryRegister {
            load,
            bytes,
            sign_to,
            data,
            base,
            index,
            extend,
            shifted,
        } => plain(
            (size_field(bytes) << 30)
                | (0b111 << 27)
                | (memory_opc(load, sign_to) << 22)
                | (1 << 21)
                | (index.reg.field() << 16)
                | (extend.option() << 13)
                | (u32::from(shifted) << 12)
                | (0b10 << 10)
                | (base.field() << 5)
                | data.reg.field(),
        ),
    }
}

/// The `opc` field of a general-purpose load or store: 00 store, 01
/// zero-extending load, 10 load sign-extended to 64, 11 load sign-extended to
/// 32.
fn memory_opc(load: bool, sign_to: Option<u32>) -> u32 {
    match (load, sign_to) {
        (false, _) => 0b00,
        (true, None) => 0b01,
        (true, Some(64)) => 0b10,
        (true, Some(_)) => 0b11,
    }
}

/// The word `inst` re-derives to, or `None` when `inst` is not an admitted
/// shape.
pub fn instruction_word(inst: &MachInst) -> Option<InstructionWord> {
    shape(inst).map(|shape| encode(&shape))
}

/// An admitted scalar immediate load or store, as its operands name it: the
/// same admission [`instruction_word`] re-derives the word from, so ENC-5's
/// [`check_emitted_instruction_word`] binds exactly these shapes. Only the
/// zero-extending loads and the stores: a sign-extending immediate load
/// (LDRSB/LDRSH, [`Shape::Memory`] with `sign_to`), a writeback form and a
/// register-offset form are instruction-word shapes this access does not
/// describe, so the word-bound memory-effect decomposition
/// (`aarch64_memory_effect`) makes no claim about them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ScalarMemoryAccess {
    /// True for a load.
    pub(crate) load: bool,
    /// Bytes transferred: 1, 2, 4 or 8.
    pub(crate) bytes: u32,
    /// Five-bit data field (31 is the zero register in this position).
    pub(crate) data: u8,
    /// The data operand is the zero register.
    pub(crate) data_is_zero: bool,
    /// Five-bit base field (31 is SP in this position).
    pub(crate) base: u8,
    /// Byte offset the operands carry.
    pub(crate) offset: i64,
    /// True when the word takes the unsigned scaled form (`imm12`), false for
    /// the unscaled form (`imm9`, LDUR/STUR).
    pub(crate) unsigned_form: bool,
}

/// The scalar memory access `inst` names, when it is an admitted shape.
pub(crate) fn scalar_memory_access(inst: &MachInst) -> Option<ScalarMemoryAccess> {
    let Shape::Memory {
        load,
        bytes,
        sign_to: None,
        data,
        base,
        offset,
    } = shape(inst)?
    else {
        return None;
    };
    Some(ScalarMemoryAccess {
        load,
        bytes,
        data: data.reg.field() as u8,
        data_is_zero: data.reg == Reg::Zr,
        base: base.field() as u8,
        offset,
        unsigned_form: memory_offset_field(offset, bytes)?.is_ok(),
    })
}

/// ENC-5's per-compile binding of the emitted word to the word the verifier's
/// obligation decodes: `Some(Ok(()))` when `emitted` equals the re-derived
/// word outside its hole bits, `Some(Err(_))` when it differs, `None` when
/// `inst` is not an admitted shape (no claim).
pub fn check_emitted_instruction_word(inst: &MachInst, emitted: u32) -> Option<Result<(), String>> {
    let expected = instruction_word(inst)?;
    let keep = !expected.hole_mask;
    Some(if emitted & keep == expected.word & keep {
        Ok(())
    } else {
        Err(format!(
            "emitted word {emitted:#010x} is not the verifier's re-derived word {:#010x} \
             (hole mask {:#010x}) that the instruction-derived obligation decodes",
            expected.word, expected.hole_mask
        ))
    })
}

// ===========================================================================
// Independent decoder
// ===========================================================================

/// The instruction classes the decoder models, with raw fields named after
/// the Arm ARM encoding diagrams.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DecodedWord {
    /// Move wide (immediate): `sf opc 100101 hw imm16 Rd`.
    MoveWide {
        sf: u32,
        opc: u32,
        hw: u32,
        imm16: u32,
        rd: u32,
    },
    /// Add/subtract (immediate): `sf op S 100010 sh imm12 Rn Rd`.
    AddSubImm {
        sf: u32,
        op: u32,
        s: u32,
        sh: u32,
        imm12: u32,
        rn: u32,
        rd: u32,
    },
    /// Add/subtract (shifted register): `sf op S 01011 shift 0 Rm imm6 Rn Rd`.
    AddSubShifted {
        sf: u32,
        op: u32,
        s: u32,
        shift: u32,
        rm: u32,
        imm6: u32,
        rn: u32,
        rd: u32,
    },
    /// Logical (shifted register): `sf opc 01010 shift N Rm imm6 Rn Rd`.
    LogicalShifted {
        sf: u32,
        opc: u32,
        shift: u32,
        n: u32,
        rm: u32,
        imm6: u32,
        rn: u32,
        rd: u32,
    },
    /// Data-processing (3 source): `sf op54 11011 op31 Rm o0 Ra Rn Rd`.
    Dp3 {
        sf: u32,
        op54: u32,
        op31: u32,
        rm: u32,
        o0: u32,
        ra: u32,
        rn: u32,
        rd: u32,
    },
    /// Unconditional branch (immediate): `op 00101 imm26`.
    BranchImm { op: u32, imm26: u32 },
    /// Conditional branch (immediate): `0101010 o1 imm19 o0 cond`.
    CondBranch {
        o1: u32,
        imm19: u32,
        o0: u32,
        cond: u32,
    },
    /// Load/store register (unsigned immediate):
    /// `size 111 V 01 opc imm12 Rn Rt`.
    LoadStoreUnsigned {
        size: u32,
        v: u32,
        opc: u32,
        imm12: u32,
        rn: u32,
        rt: u32,
    },
    /// Load/store register (unscaled immediate):
    /// `size 111 V 00 opc 0 imm9 00 Rn Rt`.
    LoadStoreUnscaled {
        size: u32,
        v: u32,
        opc: u32,
        imm9: u32,
        rn: u32,
        rt: u32,
    },
    /// Load/store register (immediate post-indexed, `pre = 0`, or
    /// pre-indexed, `pre = 1`): `size 111 V 00 opc 0 imm9 pre 1 Rn Rt`.
    LoadStoreIndexed {
        size: u32,
        v: u32,
        opc: u32,
        imm9: u32,
        pre: u32,
        rn: u32,
        rt: u32,
    },
    /// Load/store register (register offset):
    /// `size 111 V 00 opc 1 Rm option S 10 Rn Rt`.
    LoadStoreRegister {
        size: u32,
        v: u32,
        opc: u32,
        rm: u32,
        option: u32,
        s: u32,
        rn: u32,
        rt: u32,
    },
}

const fn bits(word: u32, hi: u32, lo: u32) -> u32 {
    (word >> lo) & ((1 << (hi - lo + 1)) - 1)
}

/// Decode `word` into a modeled class, or `None` when it is in none of them.
pub fn decode_word(w: u32) -> Option<DecodedWord> {
    Some(if w & 0x1F80_0000 == 0x1280_0000 {
        DecodedWord::MoveWide {
            sf: bits(w, 31, 31),
            opc: bits(w, 30, 29),
            hw: bits(w, 22, 21),
            imm16: bits(w, 20, 5),
            rd: bits(w, 4, 0),
        }
    } else if w & 0x1F80_0000 == 0x1100_0000 {
        DecodedWord::AddSubImm {
            sf: bits(w, 31, 31),
            op: bits(w, 30, 30),
            s: bits(w, 29, 29),
            sh: bits(w, 22, 22),
            imm12: bits(w, 21, 10),
            rn: bits(w, 9, 5),
            rd: bits(w, 4, 0),
        }
    } else if w & 0x1F20_0000 == 0x0B00_0000 {
        DecodedWord::AddSubShifted {
            sf: bits(w, 31, 31),
            op: bits(w, 30, 30),
            s: bits(w, 29, 29),
            shift: bits(w, 23, 22),
            rm: bits(w, 20, 16),
            imm6: bits(w, 15, 10),
            rn: bits(w, 9, 5),
            rd: bits(w, 4, 0),
        }
    } else if w & 0x1F00_0000 == 0x0A00_0000 {
        DecodedWord::LogicalShifted {
            sf: bits(w, 31, 31),
            opc: bits(w, 30, 29),
            shift: bits(w, 23, 22),
            n: bits(w, 21, 21),
            rm: bits(w, 20, 16),
            imm6: bits(w, 15, 10),
            rn: bits(w, 9, 5),
            rd: bits(w, 4, 0),
        }
    } else if w & 0x1F00_0000 == 0x1B00_0000 {
        DecodedWord::Dp3 {
            sf: bits(w, 31, 31),
            op54: bits(w, 30, 29),
            op31: bits(w, 23, 21),
            rm: bits(w, 20, 16),
            o0: bits(w, 15, 15),
            ra: bits(w, 14, 10),
            rn: bits(w, 9, 5),
            rd: bits(w, 4, 0),
        }
    } else if w & 0x7C00_0000 == 0x1400_0000 {
        DecodedWord::BranchImm {
            op: bits(w, 31, 31),
            imm26: bits(w, 25, 0),
        }
    } else if w & 0xFE00_0000 == 0x5400_0000 {
        DecodedWord::CondBranch {
            o1: bits(w, 24, 24),
            imm19: bits(w, 23, 5),
            o0: bits(w, 4, 4),
            cond: bits(w, 3, 0),
        }
    } else if w & 0x3B00_0000 == 0x3900_0000 {
        DecodedWord::LoadStoreUnsigned {
            size: bits(w, 31, 30),
            v: bits(w, 26, 26),
            opc: bits(w, 23, 22),
            imm12: bits(w, 21, 10),
            rn: bits(w, 9, 5),
            rt: bits(w, 4, 0),
        }
    } else if w & 0x3B20_0C00 == 0x3800_0000 {
        DecodedWord::LoadStoreUnscaled {
            size: bits(w, 31, 30),
            v: bits(w, 26, 26),
            opc: bits(w, 23, 22),
            imm9: bits(w, 20, 12),
            rn: bits(w, 9, 5),
            rt: bits(w, 4, 0),
        }
    } else if w & 0x3B20_0400 == 0x3800_0400 {
        DecodedWord::LoadStoreIndexed {
            size: bits(w, 31, 30),
            v: bits(w, 26, 26),
            opc: bits(w, 23, 22),
            imm9: bits(w, 20, 12),
            pre: bits(w, 11, 11),
            rn: bits(w, 9, 5),
            rt: bits(w, 4, 0),
        }
    } else if w & 0x3B20_0C00 == 0x3820_0800 {
        DecodedWord::LoadStoreRegister {
            size: bits(w, 31, 30),
            v: bits(w, 26, 26),
            opc: bits(w, 23, 22),
            rm: bits(w, 20, 16),
            option: bits(w, 15, 13),
            s: bits(w, 12, 12),
            rn: bits(w, 9, 5),
            rt: bits(w, 4, 0),
        }
    } else {
        return None;
    })
}

// ===========================================================================
// Symbolic state
// ===========================================================================

/// A location an instruction writes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Location {
    /// `X<n>` (n < 31), all 64 bits.
    Gpr(u8),
    /// The stack pointer, all 64 bits.
    Sp,
    /// PSTATE.{N,Z,C,V} as four bits, N most significant.
    Nzcv,
    /// Whether a branch is taken (one bit).
    BranchTaken,
    /// A branch's destination when taken.
    BranchTarget,
    /// A load of this many bytes: the value is its 64-bit address.
    Load(u32),
    /// A store of this many bytes: the value is `data ++ address`.
    Store(u32),
}

impl Location {
    /// The location with any register number dropped, as an obligation names
    /// it. With the role-named inputs ([`Roles`]) this makes the obligations
    /// of instances that differ only in register numbers EQUAL (name included),
    /// so the process-wide memos answer the second. A writeback load writes two
    /// general-purpose registers (the destination and the base), whose
    /// obligations then share the name `Gpr`; that is only a name, because both
    /// memos compare the whole obligation, so two obligations of different
    /// content never share an entry.
    fn label(self) -> String {
        match self {
            Self::Gpr(_) => "Gpr".to_owned(),
            other => format!("{other:?}"),
        }
    }
}

type Effect = BTreeMap<Location, E>;

/// Role names for the registers an instruction reads, shared by both sides:
/// the first register read is `r0`, the next distinct one `r1`, and so on.
/// With [`Location::label`] naming the obligation, instances that differ only
/// in register numbers have equal obligations and so share one evaluation.
#[derive(Default)]
struct Roles {
    regs: Vec<Reg>,
}

impl Roles {
    /// The 64-bit value of `X<n>` or SP; zero for ZR.
    fn value(&mut self, reg: Reg) -> E {
        if reg == Reg::Zr {
            return E::bv_const(0, 64);
        }
        let index = match self.regs.iter().position(|seen| *seen == reg) {
            Some(index) => index,
            None => {
                self.regs.push(reg);
                self.regs.len() - 1
            }
        };
        E::var(format!("r{index}"), 64)
    }

    /// `X[reg, width]`.
    fn read(&mut self, reg: Reg, width: u32) -> E {
        low(self.value(reg), width)
    }
}

fn nzcv() -> E {
    E::var("nzcv", 4)
}

fn pc() -> E {
    E::var("pc", 64)
}

fn loaded(bytes: u32) -> E {
    E::var(format!("mem{}", bytes * 8), bytes * 8)
}

fn low(expr: E, width: u32) -> E {
    if expr.bv_width() == width {
        expr
    } else {
        expr.extract(width - 1, 0)
    }
}

fn zext(expr: E, to: u32) -> E {
    let width = expr.bv_width();
    if width == to {
        expr
    } else {
        expr.zero_ext(to - width)
    }
}

fn sext(expr: E, to: u32) -> E {
    let width = expr.bv_width();
    if width == to {
        expr
    } else {
        expr.sign_ext(to - width)
    }
}

fn mask(width: u32) -> u64 {
    if width == 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

fn bit(cond: E) -> E {
    E::ite(cond, E::bv_const(1, 1), E::bv_const(0, 1))
}

fn flag(nzcv: &E, index: u32) -> E {
    nzcv.clone()
        .extract(index, index)
        .eq_expr(E::bv_const(1, 1))
}

/// Record a write of `value` (at its width) to `reg`: a W write zeroes bits
/// 63:32, a write to ZR is discarded.
fn write(effect: &mut Effect, reg: Reg, value: E) {
    let value = zext(value, 64);
    match reg {
        Reg::X(n) => {
            effect.insert(Location::Gpr(n), value);
        }
        Reg::Sp => {
            effect.insert(Location::Sp, value);
        }
        Reg::Zr => {}
    }
}

/// Register field 31 in a class where it names SP.
fn sp_or(field: u32) -> Reg {
    if field == 31 {
        Reg::Sp
    } else {
        Reg::X(field as u8)
    }
}

/// Register field 31 in a class where it names ZR.
fn zr_or(field: u32) -> Reg {
    if field == 31 {
        Reg::Zr
    } else {
        Reg::X(field as u8)
    }
}

fn ror(x: E, amount: u32, width: u32) -> E {
    if amount == 0 {
        x
    } else {
        x.clone()
            .extract(amount - 1, 0)
            .concat(x.extract(width - 1, amount))
    }
}

// ===========================================================================
// The machine side: Arm ARM semantics of a decoded word
// ===========================================================================

/// `(result, nzcv)` of Arm's `AddWithCarry(x, y, carry_in)`: the sum at
/// `width` bits, and N, Z, C, V from the unbounded unsigned and signed sums,
/// computed here at `width + 1` bits.
fn add_with_carry(x: E, y: E, carry_in: u64, width: u32) -> (E, E) {
    let wide = width + 1;
    let carry = E::bv_const(carry_in, wide);
    let unsigned_sum = zext(x.clone(), wide)
        .bvadd(zext(y.clone(), wide))
        .bvadd(carry.clone());
    let signed_sum = sext(x, wide).bvadd(sext(y, wide)).bvadd(carry);
    let result = low(unsigned_sum.clone(), width);
    let n = result.clone().extract(width - 1, width - 1);
    let z = bit(result.clone().eq_expr(E::bv_const(0, width)));
    let c = bit(zext(result.clone(), wide).eq_expr(unsigned_sum).not_expr());
    let v = bit(sext(result.clone(), wide).eq_expr(signed_sum).not_expr());
    (result, n.concat(z).concat(c).concat(v))
}

/// Arm's `ShiftReg` for a constant amount.
fn shift_reg(x: E, shift: u32, amount: u32, width: u32) -> E {
    if amount == 0 {
        return x;
    }
    let by = E::bv_const(u64::from(amount), width);
    match shift {
        0b00 => x.bvshl(by),
        0b01 => x.bvlshr(by),
        0b10 => x.bvashr(by),
        _ => ror(x, amount, width),
    }
}

/// Arm's `ConditionHolds(cond)` over the symbolic NZCV.
fn condition_holds(cond: u32) -> E {
    let flags = nzcv();
    let (n, z, c, v) = (
        flag(&flags, 3),
        flag(&flags, 2),
        flag(&flags, 1),
        flag(&flags, 0),
    );
    let base = match cond >> 1 {
        0b000 => z,
        0b001 => c,
        0b010 => n,
        0b011 => v,
        0b100 => c.and_expr(z.not_expr()),
        0b101 => n.eq_expr(v),
        0b110 => n.eq_expr(v).and_expr(z.not_expr()),
        _ => E::bool_const(true),
    };
    if cond & 1 == 1 && cond != 0b1111 {
        base.not_expr()
    } else {
        base
    }
}

/// `SignExtend(value, 64)` of a `field_bits`-wide field, as a 64-bit integer.
fn sign_extended(value: u32, field_bits: u32) -> u64 {
    let shift = 64 - field_bits;
    ((i64::from(value) << shift) >> shift) as u64
}

/// The displacement `SignExtend(field:'00', 64)` of a branch whose field is
/// `field_bits` wide: over the hole variable when a fixup fills the field,
/// else the constant it denotes.
fn displacement(value: u32, field_bits: u32, hole: bool) -> E {
    if hole {
        let field = E::var(format!("hole{field_bits}"), field_bits);
        sext(field.concat(E::bv_const(0, 2)), 64)
    } else {
        E::bv_const(sign_extended(value, field_bits).wrapping_mul(4), 64)
    }
}

/// Next PC of a fully decoded B, retaining its actual immediate field in the
/// checked expression instead of substituting a source/CFG destination.
pub(crate) fn decoded_b_next_pc(pc: E, imm26: u32) -> E {
    pc.bvadd(
        E::bv_const(u64::from(imm26), 26)
            .concat(E::bv_const(0, 2))
            .sign_ext(36),
    )
}

/// The architectural effect of `decoded`, or why it has none modeled here.
fn machine_effect(
    decoded: DecodedWord,
    hole_mask: u32,
    roles: &mut Roles,
) -> Result<Effect, String> {
    let mut effect = Effect::new();
    let datasize = |sf: u32| if sf == 1 { 64 } else { 32 };
    match decoded {
        DecodedWord::MoveWide {
            sf,
            opc,
            hw,
            imm16,
            rd,
        } => {
            if opc == 0b01 {
                return Err("move-wide opc 01 is unallocated".into());
            }
            if sf == 0 && hw >= 2 {
                return Err("32-bit move-wide with hw >= 2 is unallocated".into());
            }
            let width = datasize(sf);
            let pos = hw * 16;
            let result = if opc == 0b11 {
                // MOVK: the halfword at `pos` of X[d] becomes imm16.
                let old = roles.read(zr_or(rd), width);
                let mut value = E::bv_const(u64::from(imm16), 16);
                if pos > 0 {
                    value = value.concat(old.clone().extract(pos - 1, 0));
                }
                if pos + 16 < width {
                    value = old.extract(width - 1, pos + 16).concat(value);
                }
                value
            } else {
                let placed = u64::from(imm16) << pos;
                let value = if opc == 0b00 {
                    !placed & mask(width)
                } else {
                    placed
                };
                E::bv_const(value, width)
            };
            write(&mut effect, zr_or(rd), result);
        }
        DecodedWord::AddSubImm {
            sf,
            op,
            s,
            sh,
            imm12,
            rn,
            rd,
        } => {
            let width = datasize(sf);
            let imm = u64::from(imm12) << (12 * sh);
            let operand1 = roles.read(sp_or(rn), width);
            let operand2 = E::bv_const(imm, width);
            // AddWithCarry(x, NOT(y), 1).result is x - y.
            let result = if op == 1 {
                operand1.clone().bvsub(operand2.clone())
            } else {
                operand1.clone().bvadd(operand2.clone())
            };
            if s == 1 {
                let operand2 = if op == 1 {
                    E::bv_const(!imm & mask(width), width)
                } else {
                    operand2
                };
                let (_, flags) = add_with_carry(operand1, operand2, u64::from(op), width);
                effect.insert(Location::Nzcv, flags);
                write(&mut effect, zr_or(rd), result);
            } else {
                write(&mut effect, sp_or(rd), result);
            }
        }
        DecodedWord::AddSubShifted {
            sf,
            op,
            s,
            shift,
            rm,
            imm6,
            rn,
            rd,
        } => {
            if shift == 0b11 {
                return Err("add/sub shifted-register shift 11 is reserved".into());
            }
            if sf == 0 && imm6 >= 32 {
                return Err(
                    "32-bit add/sub shifted-register with imm6 >= 32 is unallocated".into(),
                );
            }
            let width = datasize(sf);
            let operand1 = roles.read(zr_or(rn), width);
            let rm_value = roles.read(zr_or(rm), width);
            let operand2 = shift_reg(rm_value, shift, imm6, width);
            let result = if op == 1 {
                operand1.clone().bvsub(operand2.clone())
            } else {
                operand1.clone().bvadd(operand2.clone())
            };
            if s == 1 {
                let operand2 = if op == 1 {
                    operand2.bvxor(E::bv_const(mask(width), width))
                } else {
                    operand2
                };
                let (_, flags) = add_with_carry(operand1, operand2, u64::from(op), width);
                effect.insert(Location::Nzcv, flags);
            }
            write(&mut effect, zr_or(rd), result);
        }
        DecodedWord::LogicalShifted {
            sf,
            opc,
            shift,
            n,
            rm,
            imm6,
            rn,
            rd,
        } => {
            if sf == 0 && imm6 >= 32 {
                return Err(
                    "32-bit logical shifted-register with imm6 >= 32 is unallocated".into(),
                );
            }
            let width = datasize(sf);
            let operand1 = roles.read(zr_or(rn), width);
            let rm_value = roles.read(zr_or(rm), width);
            let mut operand2 = shift_reg(rm_value, shift, imm6, width);
            if n == 1 {
                operand2 = operand2.bvxor(E::bv_const(mask(width), width));
            }
            let result = match opc {
                0b00 | 0b11 => operand1.bvand(operand2),
                0b01 => operand1.bvor(operand2),
                _ => operand1.bvxor(operand2),
            };
            if opc == 0b11 {
                let n = result.clone().extract(width - 1, width - 1);
                let z = bit(result.clone().eq_expr(E::bv_const(0, width)));
                effect.insert(Location::Nzcv, n.concat(z).concat(E::bv_const(0, 2)));
            }
            write(&mut effect, zr_or(rd), result);
        }
        DecodedWord::Dp3 {
            sf,
            op54,
            op31,
            rm,
            o0,
            ra,
            rn,
            rd,
        } => {
            if (sf, op54, op31, o0, ra) != (1, 0b00, 0b110, 0, 31) {
                return Err(format!(
                    "data-processing (3 source) sf/op54/op31/o0/Ra = {sf}/{op54}/{op31}/{o0}/{ra} \
                     is not UMULH"
                ));
            }
            let lhs = zext(roles.read(zr_or(rn), 64), 128);
            let rhs = zext(roles.read(zr_or(rm), 64), 128);
            write(&mut effect, zr_or(rd), lhs.bvmul(rhs).extract(127, 64));
        }
        DecodedWord::BranchImm { op, imm26 } => {
            let hole = hole_mask & IMM26_MASK == IMM26_MASK;
            effect.insert(Location::BranchTaken, E::bv_const(1, 1));
            effect.insert(
                Location::BranchTarget,
                pc().bvadd(displacement(imm26, 26, hole)),
            );
            if op == 1 {
                effect.insert(Location::Gpr(30), pc().bvadd(E::bv_const(4, 64)));
            }
        }
        DecodedWord::CondBranch {
            o1,
            imm19,
            o0,
            cond,
        } => {
            if o1 == 1 {
                return Err("conditional branch with o1 = 1 is unallocated".into());
            }
            if o0 == 1 {
                return Err("BC.cond (o0 = 1) is not modeled".into());
            }
            let hole = hole_mask & IMM19_MASK == IMM19_MASK;
            effect.insert(Location::BranchTaken, bit(condition_holds(cond)));
            effect.insert(
                Location::BranchTarget,
                pc().bvadd(displacement(imm19, 19, hole)),
            );
        }
        DecodedWord::LoadStoreUnsigned {
            size,
            v,
            opc,
            imm12,
            rn,
            rt,
        } => {
            let offset = E::bv_const(u64::from(imm12) << size, 64);
            let address = roles.value(sp_or(rn)).bvadd(offset);
            memory_effect(&mut effect, roles, size, v, opc, address, rt)?;
        }
        DecodedWord::LoadStoreUnscaled {
            size,
            v,
            opc,
            imm9,
            rn,
            rt,
        } => {
            let offset = E::bv_const(sign_extended(imm9, 9), 64);
            let address = roles.value(sp_or(rn)).bvadd(offset);
            memory_effect(&mut effect, roles, size, v, opc, address, rt)?;
        }
        DecodedWord::LoadStoreIndexed {
            size,
            v,
            opc,
            imm9,
            pre,
            rn,
            rt,
        } => {
            // `if wback && n == t && n != 31`: CONSTRAINED UNPREDICTABLE for a
            // load (WBOVERLAPLD) and a store (WBOVERLAPST) alike.
            if v == 0 && rn == rt && rn != 31 {
                return Err(
                    "writeback base is also the transfer register (constrained unpredictable)"
                        .into(),
                );
            }
            let base = roles.value(sp_or(rn));
            let updated = base.clone().bvadd(E::bv_const(sign_extended(imm9, 9), 64));
            let address = if pre == 1 { updated.clone() } else { base };
            memory_effect(&mut effect, roles, size, v, opc, address, rt)?;
            write(&mut effect, sp_or(rn), updated);
        }
        DecodedWord::LoadStoreRegister {
            size,
            v,
            opc,
            rm,
            option,
            s,
            rn,
            rt,
        } => {
            // `if option<1> == '0' then UNDEFINED`.
            if option & 0b010 == 0 {
                return Err(format!(
                    "load/store register-offset option {option:#05b} is unallocated"
                ));
            }
            let base = roles.value(sp_or(rn));
            // `shift = if S == '1' then scale else 0`, with `scale = size`
            // for the general-purpose forms.
            let offset = extend_reg(roles, zr_or(rm), option, if s == 1 { size } else { 0 })
                .ok_or_else(|| "unsupported register-offset extension fields".to_string())?;
            memory_effect(&mut effect, roles, size, v, opc, base.bvadd(offset), rt)?;
        }
    }
    Ok(effect)
}

/// Complete state for the shared bounded GPR word-step mathematics. No source,
/// ABI, executable storage or proof authority is carried by this value.
#[derive(Clone, Debug)]
pub(crate) struct LinkedWordState {
    pub registers: BTreeMap<u8, E>,
    pub sp: E,
    pub pc: E,
    pub nzcv: E,
    pub memory: E,
}

impl LinkedWordState {
    /// One actual decoded word. Returned addresses are all eight-byte memory
    /// lanes touched by a pair. The narrow profile deliberately refuses general
    /// memory/system instructions and conditional control. RET reads the actual
    /// architectural register; BL writes actual PC+4 and changes actual PC.
    /// Scalar effects are exactly machine_effect's, with role variables bound
    /// to this pre-state through the shared DAG rewrite, without simplification.
    pub(crate) fn step(&mut self, word: u32) -> Result<Vec<E>, String> {
        if word == 0xd503201f {
            self.pc = self.pc.clone().bvadd(E::bv_const(4, 64));
            return Ok(Vec::new());
        }
        if let Some(crate::aarch64_control_decode::A64ControlWord::Return { register }) =
            crate::aarch64_control_decode::decode_a64_control_word(word)
        {
            if register == 31 {
                return Err("RET register31 is outside linked profile".into());
            }
            self.pc = self
                .registers
                .get(&register)
                .cloned()
                .ok_or("missing RET register")?;
            return Ok(Vec::new());
        }
        let decoded = decode_word(word);
        if !matches!(
            decoded,
            Some(
                DecodedWord::MoveWide { .. }
                    | DecodedWord::AddSubImm { .. }
                    | DecodedWord::LogicalShifted { .. }
                    | DecodedWord::BranchImm { op: 1, .. }
            )
        ) {
            let effect = crate::aarch64_pair_memory::gpr64_pair_effect(
                word,
                &self.sp,
                &self.registers,
                &self.memory,
            )
            .map_err(|e| e.to_string())?;
            for (register, value) in effect.registers {
                self.registers.insert(register, value);
            }
            if let Some(sp) = effect.sp {
                self.sp = sp;
            }
            self.memory = effect.memory;
            self.pc = self.pc.clone().bvadd(E::bv_const(4, 64));
            return Ok(effect.addresses.into());
        }
        let mut roles = Roles::default();
        let effects = machine_effect(decoded.ok_or("unsupported linked word")?, 0, &mut roles)?;
        let mut bindings = BTreeMap::new();
        for (index, register) in roles.regs.iter().enumerate() {
            let value = match register {
                Reg::X(n) => self
                    .registers
                    .get(n)
                    .cloned()
                    .ok_or("missing role register")?,
                Reg::Sp => self.sp.clone(),
                Reg::Zr => E::bv_const(0, 64),
            };
            bindings.insert(format!("r{index}"), value);
        }
        bindings.insert("pc".into(), self.pc.clone());
        bindings.insert("nzcv".into(), self.nzcv.clone());
        let instantiate = |value: E| -> Result<E, String> {
            let rewritten = value.try_rewrite_dag(&mut |node| match node {
                E::Var { name, .. } => bindings
                    .get(name)
                    .cloned()
                    .map(Some)
                    .ok_or_else(|| format!("unbound word-step input {name}")),
                _ => Ok(None),
            })?;
            Ok(rewritten.unwrap_or(value))
        };
        // All effects read the old state before any write becomes visible.
        let effects = effects
            .into_iter()
            .map(|(location, value)| instantiate(value).map(|value| (location, value)))
            .collect::<Result<Vec<_>, _>>()?;
        let mut next_pc = self.pc.clone().bvadd(E::bv_const(4, 64));
        for (location, value) in effects {
            match location {
                Location::Gpr(n) => {
                    self.registers.insert(n, value);
                }
                Location::Sp => self.sp = value,
                Location::Nzcv => self.nzcv = value,
                Location::BranchTarget => next_pc = value,
                Location::BranchTaken => (), // Only unconditional BL is admitted.
                Location::Load(_) | Location::Store(_) => {
                    return Err("unbound memory effect".into());
                }
            }
        }
        self.pc = next_pc;
        Ok(Vec::new())
    }
}

/// Arm's `ExtendReg(m, DecodeRegExtend(option), shift, 64)`, transcribed from
/// the pseudocode: take `len = Min(extend width, 64 - shift)` low bits of
/// `X[m]`, append `shift` zeros, and zero- (`option<2> = 0`) or sign-extend
/// (`option<2> = 1`) to 64 bits.
fn extend_reg(roles: &mut Roles, reg: Reg, option: u32, shift: u32) -> Option<E> {
    extend_reg_value(roles.value(reg), option, shift)
}

/// Pure value portion of Arm's `ExtendReg(..., 64)`. Callers independently
/// validate their instruction class and allocated register identities. This
/// helper grants no instruction, memory, encoding or proof attribution.
/// The bounded subset covers shifts through the largest scalar/SIMD scale.
pub(crate) fn extend_reg_value(value: E, option: u32, shift: u32) -> Option<E> {
    if value.try_bv_width().ok() != Some(64) || option > 7 || shift > 4 {
        return None;
    }
    let width = match option & 0b011 {
        0b00 => 8,
        0b01 => 16,
        0b10 => 32,
        _ => 64,
    };
    let len = width.min(64 - shift);
    let mut field = low(value, len);
    if shift > 0 {
        field = field.concat(E::bv_const(0, shift));
    }
    Some(if option & 0b100 == 0 {
        zext(field, 64)
    } else {
        sext(field, 64)
    })
}

/// A general-purpose load or store at `address`: a load writes `Rt` with its
/// bytes extended as `opc` says, a store writes `X[t]`'s low bytes.
fn memory_effect(
    effect: &mut Effect,
    roles: &mut Roles,
    size: u32,
    v: u32,
    opc: u32,
    address: E,
    rt: u32,
) -> Result<(), String> {
    if v == 1 {
        return Err("SIMD/FP load/store is not modeled".into());
    }
    let bytes = 1u32 << size;
    match (size, opc) {
        (_, 0b00) => {
            let data = roles.read(zr_or(rt), bytes * 8);
            effect.insert(Location::Store(bytes), data.concat(address));
        }
        (_, 0b01) => {
            effect.insert(Location::Load(bytes), address);
            write(effect, zr_or(rt), loaded(bytes));
        }
        (0b00..=0b10, 0b10) => {
            effect.insert(Location::Load(bytes), address);
            write(effect, zr_or(rt), sext(loaded(bytes), 64));
        }
        (0b00 | 0b01, 0b11) => {
            effect.insert(Location::Load(bytes), address);
            write(effect, zr_or(rt), sext(loaded(bytes), 32));
        }
        _ => {
            return Err(format!(
                "load/store size {size:#04b} opc {opc:#04b} is a prefetch or unallocated"
            ));
        }
    }
    Ok(())
}

// ===========================================================================
// The intent side: what the machine-IR instruction names
// ===========================================================================

/// What the instruction-selection condition code `cc` means (its `AArch64CC`
/// in the order the lowering numbers it: EQ NE HS LO MI PL VS VC HI LS GE LT
/// GT LE).
fn intended_condition(cc: u32) -> E {
    let flags = nzcv();
    let (n, z, c, v) = (
        flag(&flags, 3),
        flag(&flags, 2),
        flag(&flags, 1),
        flag(&flags, 0),
    );
    match cc {
        0 => z,
        1 => z.not_expr(),
        2 => c,
        3 => c.not_expr(),
        4 => n,
        5 => n.not_expr(),
        6 => v,
        7 => v.not_expr(),
        8 => c.and_expr(z.not_expr()),
        9 => c.not_expr().or_expr(z),
        10 => n.eq_expr(v),
        11 => n.eq_expr(v).not_expr(),
        12 => z.not_expr().and_expr(n.eq_expr(v)),
        _ => z.or_expr(n.eq_expr(v).not_expr()),
    }
}

/// The flags a compare of `a` with `b` sets, stated as the predicates they
/// encode: N is the sign of `a - b`, Z is `a == b`, C is unsigned `a >= b`,
/// V is signed overflow of `a - b`.
fn intended_compare_flags(a: E, b: E, width: u32) -> E {
    let difference = a.clone().bvsub(b.clone());
    let top = |x: &E| x.clone().extract(width - 1, width - 1);
    let n = top(&difference);
    let z = bit(a.clone().eq_expr(b.clone()));
    let c = bit(a.clone().bvuge(b.clone()));
    let signs_differ = top(&a).eq_expr(top(&b)).not_expr();
    let result_sign_flips = top(&difference).eq_expr(top(&a)).not_expr();
    let v = bit(signs_differ.and_expr(result_sign_flips));
    n.concat(z).concat(c).concat(v)
}

fn intended_target(target: Target, field_bits: u32) -> E {
    match target {
        Target::Hole => pc().bvadd(displacement(0, field_bits, true)),
        Target::Words(words) => pc().bvadd(E::bv_const((words as u64).wrapping_mul(4), 64)),
    }
}

fn intended_effect(shape: &Shape, roles: &mut Roles) -> Effect {
    let mut effect = Effect::new();
    match *shape {
        Shape::MoveWide {
            opc,
            width,
            hw,
            imm16,
            dst,
        } => {
            let shift = hw * 16;
            let placed = u64::from(imm16) << shift;
            let value = match opc {
                // MOVK keeps every bit of the destination outside the halfword.
                0b11 => roles
                    .read(dst, width)
                    .bvand(E::bv_const(!(0xFFFF_u64 << shift) & mask(width), width))
                    .bvor(E::bv_const(placed, width)),
                0b00 => E::bv_const(placed, width).bvxor(E::bv_const(mask(width), width)),
                _ => E::bv_const(placed, width),
            };
            write(&mut effect, dst, value);
        }
        Shape::Copy { width, dst, src } => {
            let value = roles.read(src, width);
            write(&mut effect, dst, value);
        }
        Shape::AddSubImm {
            sub,
            width,
            dst,
            src,
            imm12,
        } => {
            let lhs = roles.read(src, width);
            let rhs = E::bv_const(u64::from(imm12), width);
            write(
                &mut effect,
                dst,
                if sub { lhs.bvsub(rhs) } else { lhs.bvadd(rhs) },
            );
        }
        Shape::CmpImm { width, src, imm12 } => {
            let lhs = roles.read(src, width);
            effect.insert(
                Location::Nzcv,
                intended_compare_flags(lhs, E::bv_const(u64::from(imm12), width), width),
            );
        }
        Shape::CmpReg { width, lhs, rhs } => {
            let (a, b) = (roles.read(lhs, width), roles.read(rhs, width));
            effect.insert(Location::Nzcv, intended_compare_flags(a, b, width));
        }
        Shape::AddSubShifted {
            sub,
            shift,
            amount,
            width,
            dst,
            lhs,
            rhs,
        } => {
            let a = roles.read(lhs, width);
            let by = E::bv_const(u64::from(amount), width);
            let b = roles.read(rhs, width);
            let b = if shift == 0 {
                b.bvshl(by)
            } else {
                b.bvlshr(by)
            };
            write(&mut effect, dst, if sub { a.bvsub(b) } else { a.bvadd(b) });
        }
        Shape::EorRor {
            amount,
            width,
            dst,
            lhs,
            rhs,
        } => {
            let a = roles.read(lhs, width);
            let b = roles.read(rhs, width);
            write(&mut effect, dst, a.bvxor(ror(b, amount, width)));
        }
        Shape::Umulh { dst, lhs, rhs } => {
            let product = zext(roles.read(lhs, 64), 128).bvmul(zext(roles.read(rhs, 64), 128));
            write(&mut effect, dst, product.extract(127, 64));
        }
        Shape::Branch { link, target } => {
            effect.insert(Location::BranchTaken, E::bv_const(1, 1));
            effect.insert(Location::BranchTarget, intended_target(target, 26));
            if link {
                effect.insert(Location::Gpr(30), pc().bvadd(E::bv_const(4, 64)));
            }
        }
        Shape::CondBranch { cc, target } => {
            effect.insert(Location::BranchTaken, bit(intended_condition(cc)));
            effect.insert(Location::BranchTarget, intended_target(target, 19));
        }
        Shape::Memory {
            load,
            bytes,
            sign_to,
            data,
            base,
            offset,
        } => {
            let address = roles.value(base).bvadd(E::bv_const(offset as u64, 64));
            intended_access(&mut effect, roles, load, bytes, sign_to, data.reg, address);
        }
        Shape::MemoryWriteback {
            pre,
            load,
            data,
            base,
            offset,
        } => {
            let old = roles.value(base);
            let updated = old.clone().bvadd(E::bv_const(offset as u64, 64));
            let address = if pre { updated.clone() } else { old };
            intended_access(
                &mut effect,
                roles,
                load,
                data.width / 8,
                None,
                data.reg,
                address,
            );
            write(&mut effect, base, updated);
        }
        Shape::MemoryRegister {
            load,
            bytes,
            sign_to,
            data,
            base,
            index,
            extend,
            shifted,
        } => {
            let base = roles.value(base);
            // The index as the mode names it, then scaled by the access size
            // when the mode says so.
            let index = match extend {
                IndexExtend::Uxtw => zext(roles.read(index.reg, 32), 64),
                IndexExtend::Sxtw => sext(roles.read(index.reg, 32), 64),
                IndexExtend::Lsl | IndexExtend::Sxtx => roles.read(index.reg, 64),
            };
            let scale = bytes.trailing_zeros();
            let offset = if shifted && scale > 0 {
                index.bvshl(E::bv_const(u64::from(scale), 64))
            } else {
                index
            };
            intended_access(
                &mut effect,
                roles,
                load,
                bytes,
                sign_to,
                data.reg,
                base.bvadd(offset),
            );
        }
    }
    effect
}

/// The locations a general-purpose load or store of `bytes` at `address`
/// writes, as its operands name them: a load reads `bytes` at `address` and
/// writes `data` with them, zero-extended or sign-extended to `sign_to`
/// (a W write then clears bits 63:32); a store writes `data`'s low bytes at
/// `address`.
fn intended_access(
    effect: &mut Effect,
    roles: &mut Roles,
    load: bool,
    bytes: u32,
    sign_to: Option<u32>,
    data: Reg,
    address: E,
) {
    if load {
        effect.insert(Location::Load(bytes), address);
        let value = match sign_to {
            None => loaded(bytes),
            Some(width) => sext(loaded(bytes), width),
        };
        write(effect, data, value);
    } else {
        let value = roles.read(data, bytes * 8);
        effect.insert(Location::Store(bytes), value.concat(address));
    }
}

// ===========================================================================
// The obligation and its verdict
// ===========================================================================

/// How every written location of a holding obligation was decided.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision {
    /// Every location is syntactically identical or equal as an exact bit
    /// routing, for every input.
    Exact,
    /// Some location needed the evaluator; this is its weakest strength.
    Evaluated(VerificationStrength),
}

impl std::fmt::Display for Decision {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Exact => f.write_str(
                "decided in-process for every input by term identity or exact bit routing",
            ),
            Self::Evaluated(strength) => write!(
                f,
                "decided in-process; a location needed the evaluator: {strength}"
            ),
        }
    }
}

/// The outcome of an instruction-derived obligation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    /// Both sides write the same locations with equal values.
    Holds(Decision),
    /// The word does not do what the instruction names.
    Refuted(String),
    /// The evaluator neither confirmed nor refuted a location.
    Undecided(String),
}

/// An instruction-derived obligation and its outcome.
#[derive(Clone, Debug)]
pub struct InstructionWordVerdict {
    /// `A64 instruction word <opcode> <word>`.
    pub name: String,
    /// The word the obligation decoded.
    pub word: InstructionWord,
    /// The written locations, and per location the intent and machine terms
    /// (`trust_ir_expr` is the intent, `aarch64_expr` the decoded word), with
    /// role-named inputs. Each is named `A64 instruction word <opcode>:
    /// <location label>`, without the word or any register number, so
    /// instances that differ only in register numbers have equal obligations.
    /// Empty when the write sets differ.
    pub locations: Vec<(Location, ProofObligation)>,
    /// The outcome.
    pub outcome: Outcome,
}

fn obligation(location: Location, intent: E, machine: E, opcode: O) -> ProofObligation {
    let mut inputs = Vec::new();
    for side in [&intent, &machine] {
        for (var, width) in variables(side) {
            if !inputs.iter().any(|(seen, _): &(String, u32)| *seen == var) {
                inputs.push((var, width));
            }
        }
    }
    ProofObligation {
        name: format!("A64 instruction word {opcode:?}: {}", location.label()),
        trust_ir_expr: intent,
        aarch64_expr: machine,
        inputs,
        preconditions: Vec::new(),
        fp_inputs: Vec::new(),
        category: Some(TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: format!("{opcode:?}"),
            arity: 1,
        },
    }
}

/// Boundary points of one input: the width's corner values and, for every
/// constant either side mentions, the constant, its neighbours, its
/// complement and its negation (`NOT(c) + 1`), all at the input's width.
fn boundary_values(width: u32, constants: &[u64]) -> Vec<u64> {
    let m = mask(width);
    let sign = 1u64 << (width - 1);
    let mut values = vec![0, 1, 2, m, m - 1, sign, sign - 1, sign + 1];
    for &c in constants {
        for value in [
            c,
            c.wrapping_add(1),
            c.wrapping_sub(1),
            !c,
            (!c).wrapping_add(1),
        ] {
            values.push(value & m);
        }
    }
    values.sort_unstable();
    values.dedup();
    values
}

fn constants(expr: &E, out: &mut Vec<u64>) {
    if let E::BvConst { value, .. } = expr {
        out.push(*value);
        return;
    }
    expr.for_each_child(&mut |child| constants(child, out));
}

/// Search the boundary points of `obligation` for an input where its two
/// sides differ. Sampling misses a difference confined to a few points (a
/// compare immediate off by one differs only where the register equals one of
/// the two immediates); every such point is built from the constants the two
/// sides mention. At most two inputs are varied jointly; a third or later
/// input is held at zero. Finding nothing proves nothing: the evaluator runs
/// next.
fn boundary_counterexample(obligation: &ProofObligation) -> Option<String> {
    use crate::smt::EvalEnv;
    let mut constants_seen = Vec::new();
    constants(&obligation.trust_ir_expr, &mut constants_seen);
    constants(&obligation.aarch64_expr, &mut constants_seen);
    constants_seen.sort_unstable();
    constants_seen.dedup();
    let axes: Vec<Vec<u64>> = obligation
        .inputs
        .iter()
        .take(2)
        .map(|(_, width)| boundary_values(*width, &constants_seen))
        .collect();
    let first = axes.first().cloned().unwrap_or_else(|| vec![0]);
    let second = axes.get(1).cloned().unwrap_or_else(|| vec![0]);
    for a in &first {
        for b in &second {
            let mut env = EvalEnv::default();
            for (index, (name, width)) in obligation.inputs.iter().enumerate() {
                let value = match index {
                    0 => *a,
                    1 => *b,
                    _ => 0,
                };
                env.insert(name.clone(), value & mask(*width));
            }
            let (Ok(intended), Ok(emitted)) = (
                obligation.trust_ir_expr.try_eval(&env),
                obligation.aarch64_expr.try_eval(&env),
            ) else {
                continue;
            };
            if !intended.semantically_equal(&emitted) {
                return Some(format!(
                    "at {:?}: intent {intended:?}, word {emitted:?}",
                    obligation
                        .inputs
                        .iter()
                        .map(|(name, _)| (name.clone(), env.get(name).copied()))
                        .collect::<Vec<_>>()
                ));
            }
        }
    }
    None
}

/// Entries [`memoized_boundary_counterexample`] keeps before it starts over,
/// so a long-lived process (a JIT, a compile service) holds a bounded memo.
const BOUNDARY_MEMO_CAPACITY: usize = 4096;

/// [`boundary_counterexample`], memoized on the whole obligation. Obligation
/// names carry no word or register number ([`Location::label`], [`Roles`]),
/// so instances that differ only in register numbers share one entry. The
/// memo is cleared when it reaches [`BOUNDARY_MEMO_CAPACITY`]; the search is
/// a pure function of the obligation, so clearing changes no answer.
fn memoized_boundary_counterexample(obligation: &ProofObligation) -> Option<String> {
    use std::collections::HashMap;
    use std::sync::{Mutex, OnceLock};
    static MEMO: OnceLock<Mutex<HashMap<ProofObligation, Option<String>>>> = OnceLock::new();
    let memo = MEMO.get_or_init(|| Mutex::new(HashMap::new()));
    if let Some(hit) = memo
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .get(obligation)
    {
        return hit.clone();
    }
    let found = boundary_counterexample(obligation);
    let mut memo = memo
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    if memo.len() >= BOUNDARY_MEMO_CAPACITY {
        memo.clear();
    }
    memo.insert(obligation.clone(), found.clone());
    found
}

fn variables(expr: &E) -> Vec<(String, u32)> {
    fn walk(expr: &E, out: &mut Vec<(String, u32)>) {
        if let E::Var { name, width } = expr {
            if !out.iter().any(|(seen, _)| seen == name) {
                out.push((name.clone(), *width));
            }
            return;
        }
        expr.for_each_child(&mut |child| walk(child, out));
    }
    let mut out = Vec::new();
    walk(expr, &mut out);
    out
}

/// The instruction-derived obligation of `inst` and its outcome, or `None`
/// when `inst` is not an admitted shape.
pub fn instruction_word_verdict(
    inst: &MachInst,
    config: &VerificationConfig,
) -> Option<InstructionWordVerdict> {
    let word = instruction_word(inst)?;
    instruction_word_verdict_for(inst, word.word, config)
}

/// [`instruction_word_verdict`] for a word the caller supplies.
///
/// Test seam for the negative controls: hand it a MUTATED word and the
/// outcome must not hold. The instruction's hole mask still applies, since a
/// fixup overwrites those bits whatever the encoder left there. Production
/// callers use [`instruction_word_verdict`], which re-derives the word from
/// the instruction.
#[doc(hidden)]
pub fn instruction_word_verdict_for(
    inst: &MachInst,
    word: u32,
    config: &VerificationConfig,
) -> Option<InstructionWordVerdict> {
    let shape = shape(inst)?;
    let hole_mask = encode(&shape).hole_mask;
    let word = InstructionWord { word, hole_mask };
    let name = format!("A64 instruction word {:?} {:#010x}", inst.opcode, word.word);
    let mut roles = Roles::default();
    let intent = intended_effect(&shape, &mut roles);
    let verdict = |locations, outcome| InstructionWordVerdict {
        name: name.clone(),
        word,
        locations,
        outcome,
    };
    let Some(decoded) = decode_word(word.word) else {
        return Some(verdict(
            Vec::new(),
            Outcome::Refuted(format!(
                "{:#010x} is in no instruction class the decoder models",
                word.word
            )),
        ));
    };
    let machine = match machine_effect(decoded, hole_mask, &mut roles) {
        Ok(machine) => machine,
        Err(why) => {
            return Some(verdict(
                Vec::new(),
                Outcome::Refuted(format!("{decoded:?}: {why}")),
            ));
        }
    };
    let (intended, emitted): (Vec<_>, Vec<_>) = (
        intent.keys().copied().collect(),
        machine.keys().copied().collect(),
    );
    if intended != emitted {
        return Some(verdict(
            Vec::new(),
            Outcome::Refuted(format!(
                "the word writes {emitted:?}, the instruction names {intended:?}"
            )),
        ));
    }
    let mut locations = Vec::new();
    let mut evaluated: Vec<VerificationStrength> = Vec::new();
    for (location, intended) in intent {
        let Some(emitted) = machine.get(&location).cloned() else {
            continue;
        };
        let obligation = obligation(location, intended, emitted, inst.opcode);
        let (lhs, rhs) = (&obligation.trust_ir_expr, &obligation.aarch64_expr);
        if lhs.bv_width() != rhs.bv_width() {
            return Some(verdict(
                Vec::new(),
                Outcome::Refuted(format!(
                    "{location:?} is {} bits in the word and {} in the intent",
                    rhs.bv_width(),
                    lhs.bv_width()
                )),
            ));
        }
        if lhs != rhs {
            match exact_routing_equality(lhs, rhs) {
                Some(Ok(())) => {}
                Some(Err(mismatch)) => {
                    return Some(verdict(
                        Vec::new(),
                        Outcome::Refuted(format!(
                            "{location:?} bit {} is {:?} in the intent but {:?} in the word",
                            mismatch.bit, mismatch.intended, mismatch.emitted
                        )),
                    ));
                }
                None => {
                    if let Some(counterexample) = memoized_boundary_counterexample(&obligation) {
                        return Some(verdict(
                            Vec::new(),
                            Outcome::Refuted(format!("{location:?} {counterexample}")),
                        ));
                    }
                    match memoized_verify_by_evaluation(&obligation, config) {
                        VerificationResult::Valid => evaluated.push(
                            VerificationStrength::for_obligation_with_config(&obligation, config),
                        ),
                        VerificationResult::Invalid { counterexample } => {
                            return Some(verdict(
                                Vec::new(),
                                Outcome::Refuted(format!("{location:?}: {counterexample}")),
                            ));
                        }
                        VerificationResult::Unknown { reason } => {
                            return Some(verdict(
                                Vec::new(),
                                Outcome::Undecided(format!("{location:?}: {reason}")),
                            ));
                        }
                    }
                }
            }
        }
        locations.push((location, obligation));
    }
    // The weakest evaluated location names the decision: any sampled one makes
    // the whole obligation sampled.
    let decision = match evaluated
        .iter()
        .find(|strength| !strength.is_complete())
        .or_else(|| evaluated.first())
    {
        None => Decision::Exact,
        Some(strength) => Decision::Evaluated(*strength),
    };
    Some(verdict(locations, Outcome::Holds(decision)))
}

#[cfg(test)]
#[path = "aarch64_instruction_word_proofs_tests.rs"]
mod tests;
