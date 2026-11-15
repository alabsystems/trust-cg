//! ENC-5 — independent AArch64 instruction decode-check.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
//!
//! The aarch64 twin of `x86_64::decode_check`: every emitted instruction word
//! is re-decoded by an INDEPENDENT decoder — field extraction written from
//! the Arm ARM (A-profile, C4 encoding diagrams), deliberately NOT by
//! inverting `aarch64::encoding` — and structurally compared against the
//! `MachInst` intent it was emitted from. A disagreement is an encoder bug
//! surfacing as a fail-closed diagnostic instead of silently wrong bytes.
//! The check runs during emission, including on hosts that cannot execute
//! AArch64 code. Native execution tests provide a separate oracle where available.
//!
//! Covered families include integer moves, arithmetic/logical operations,
//! branches, scalar loads/stores, conditional selection, scalar H/S/D
//! floating-point compare, multiply/divide, bitfields, extends, shifts, and
//! alignment NOPs here, every scalar floating-point and Advanced SIMD form in
//! `decode_check_fp_simd`, and the general-purpose, PC-relative, atomic,
//! barrier and trap forms in `decode_check_int` (L10-P6). `check_one` defines
//! the exact opcode/operand coverage; unsupported forms return a named
//! [`DecodeCheckOutcome::Allowlisted`] reason. Those outcomes are counted, not
//! verified matches, on compatibility routes; proof-grade routes refuse them
//! (`crate::decode_check::AllowlistPolicy::Refuse`). The Darwin floor census
//! (`decode_census`, `tests/aarch64_enc5_floor_census.rs`) measures which
//! forms a corpus reaches.
//!
//! Every emitted MOV (register), scalar FMOV (register and general), SMULL,
//! BFM, RBIT, `ADD #imm12, LSL #12`, MRS and half-precision FCVT
//! (`FCVT Sd|Dd, Hn`, `FCVT Hd, Sn|Dn`) additionally has to pass
//! `trust_cg_verify::aarch64_value_decode_proofs::check_emitted_a64_value_word`:
//! a second independent decode whose Arm ARM semantics over the whole
//! destination register are compared with what the instruction names (exactly,
//! as a bit routing, for the copies, RBIT, BFM and MRS; as an instance of the
//! captured, separately checked form for SMULL, the shifted ADD and FCVT). A
//! refutation or an ill-formed instruction is a Mismatch; a shape outside that
//! model keeps the structural verdict below, or a named allowlist reason.
//!
//! Every emitted CRC32/CRC32C word likewise has to be exactly the word
//! `trust_cg_verify::aarch64_crc32_proofs::check_emitted_crc32_word`
//! re-derives from the operands, and that word must hold against the
//! reflected-CRC intent for every register value (L04-P1), and every emitted
//! `SUBS #imm` word the one `aarch64_subs_imm_proofs::check_emitted_subs_imm_word`
//! re-derives, its destination value and NZCV holding for every register
//! value.

use trust_cg_ir::inst::{AArch64Opcode, MachInst};
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::regs::{RegClass, SpecialReg, preg_class};
use trust_cg_verify::aarch64_flag_consumer_proofs as flag_proofs;
use trust_cg_verify::aarch64_pair_memory::check_pair_encoding;
use trust_cg_verify::aarch64_value_decode_proofs as value_proofs;

use crate::decode_check::{DecodeCheck, DecodeCheckError, DecodeCheckOutcome, FixupHole};

/// The allowlist reason of every opcode ENC-5 has no arm for: its words are
/// not decoded at all. Returned only by the final catch-all arm of
/// [`A64DecodeCheck`], so an inventory can tell those opcodes apart.
pub const A64_UNDECODED_FAMILY: &str = "a64-slice1: format family not yet decoded";

/// Independently decoded fields for the modeled AArch64 instruction families.
/// Field names follow the Arm ARM diagrams.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum A64Decoded {
    /// Move wide (immediate): MOVN (opc=00), MOVZ (opc=10), MOVK (opc=11).
    MoveWide {
        sf: u32,
        opc: u32,
        hw: u32,
        imm16: u32,
        rd: u32,
    },
    /// Add/subtract (immediate).
    AddSubImm {
        sf: u32,
        op: u32,
        s: u32,
        sh: u32,
        imm12: u32,
        rn: u32,
        rd: u32,
    },
    /// B (link=false) / BL (link=true); `imm26` is the raw 26-bit field.
    BranchImm { link: bool, imm26: u32 },
    /// B.cond; `imm19` is the raw 19-bit field.
    CondBranch { cond: u32, imm19: u32 },
    /// CBZ (negated=false) / CBNZ (negated=true).
    CmpBranch {
        sf: u32,
        negated: bool,
        imm19: u32,
        rt: u32,
    },
    /// Unconditional branch (register): BR (opc=0000), BLR (0001), RET (0010).
    BranchReg { opc: u32, rn: u32 },
    /// Add/subtract (shifted register).
    AddSubShiftedReg {
        sf: u32,
        op: u32,
        s: u32,
        shift: u32,
        rm: u32,
        imm6: u32,
        rn: u32,
        rd: u32,
    },
    /// Logical (shifted register): AND (opc=00), ORR (01), EOR (10), ANDS (11);
    /// `n` selects the inverted forms (BIC/ORN/EON/BICS).
    LogicalShiftedReg {
        sf: u32,
        opc: u32,
        shift: u32,
        n: u32,
        rm: u32,
        imm6: u32,
        rn: u32,
        rd: u32,
    },
    /// Load/store register (unsigned immediate): scaled imm12 form.
    LoadStoreUi {
        size: u32,
        v: u32,
        opc: u32,
        imm12: u32,
        rn: u32,
        rt: u32,
    },
    /// Load/store register (unscaled immediate): LDUR/STUR, signed imm9.
    LoadStoreUnscaled {
        size: u32,
        v: u32,
        opc: u32,
        imm9: i32,
        rn: u32,
        rt: u32,
    },
    /// Load/store register with writeback: signed byte imm9, pre/post-index.
    LoadStoreWriteback {
        size: u32,
        v: u32,
        opc: u32,
        imm9: i32,
        pre_index: bool,
        rn: u32,
        rt: u32,
    },
    /// Load/store register offset: index extension and optional access scaling.
    LoadStoreRegisterOffset {
        size: u32,
        v: u32,
        opc: u32,
        rm: u32,
        option: u32,
        s: u32,
        rn: u32,
        rt: u32,
    },
    /// Conditional select: CSEL (op=0,op2=00), CSINC (0,01), CSINV (1,00),
    /// CSNEG (1,01).
    CondSelect {
        sf: u32,
        op: u32,
        rm: u32,
        cond: u32,
        op2: u32,
        rn: u32,
        rd: u32,
    },
    /// Scalar FP conditional select. Only S/D are admitted by this checker;
    /// register field31 names S31/D31, not a zero register.
    FpCondSelect {
        ftype: u32,
        rm: u32,
        cond: u32,
        rn: u32,
        rd: u32,
    },
    /// Data-processing (2 source): UDIV (opcode=000010), SDIV (000011),
    /// LSLV/LSRV/ASRV/RORV (0010xx).
    DataProc2Src {
        sf: u32,
        rm: u32,
        opcode: u32,
        rn: u32,
        rd: u32,
    },
    /// Data-processing (3 source): MADD (op31=000,o0=0), MSUB (o0=1),
    /// SMULH/UMULH (op31=x10, ra=11111).
    DataProc3Src {
        sf: u32,
        op54: u32,
        op31: u32,
        rm: u32,
        o0: u32,
        ra: u32,
        rn: u32,
        rd: u32,
    },
    /// Load/store exclusive register (single register, no pair):
    /// size | 001000 | o2=0 | L | o1=0 | Rs | o0 | Rt2=11111 | Rn | Rt.
    /// `o0` is acquire (loads) or release (stores).
    LoadStoreExclusive {
        size: u32,
        load: bool,
        o0: u32,
        rs: u32,
        rn: u32,
        rt: u32,
    },
    /// Load/store exclusive pair: 1 | sz | 001000 | o2=0 | L | o1=1 | Rs |
    /// o0 | Rt2 | Rn | Rt.
    LoadStoreExclusivePair {
        sz: u32,
        load: bool,
        o0: u32,
        rs: u32,
        rt2: u32,
        rn: u32,
        rt: u32,
    },
    /// CLREX: 1101010100 0 00 011 0011 CRm 010 11111.
    ClearExclusive { crm: u32 },
    /// Bitfield: SBFM (opc=00), BFM (01), UBFM (10) — the extend and
    /// shift-immediate aliases live here.
    Bitfield {
        sf: u32,
        opc: u32,
        n: u32,
        immr: u32,
        imms: u32,
        rn: u32,
        rd: u32,
    },
}

/// Decode one instruction word into a modeled family, or `None` for an
/// unallocated encoding or an unmodeled family.
///
/// Field extraction is transcribed from the Arm ARM C4 encoding diagrams:
///  * Move wide (immediate):  sf | opc(2) | 100101 | hw(2) | imm16 | Rd
///  * Add/sub (immediate):    sf | op | S | 100010 | sh | imm12 | Rn | Rd
///  * B / BL:                 op | 00101 | imm26            (op: 0=B, 1=BL)
///  * B.cond:                 01010100 | imm19 | 0 | cond
///  * CBZ/CBNZ:               sf | 011010 | op | imm19 | Rt (op: 0=Z, 1=NZ)
///  * Branch (register):      1101011 | opc(4) | 11111 | 000000 | Rn | 00000
fn decode_word(w: u32) -> Option<A64Decoded> {
    // Move wide (immediate): bits 28:23 == 100101.
    if (w >> 23) & 0b111111 == 0b100101 {
        let opc = (w >> 29) & 0b11;
        if opc == 0b01 {
            return None; // unallocated
        }
        return Some(A64Decoded::MoveWide {
            sf: w >> 31,
            opc,
            hw: (w >> 21) & 0b11,
            imm16: (w >> 5) & 0xFFFF,
            rd: w & 0b11111,
        });
    }
    // Add/subtract (immediate): bits 28:23 == 100010.
    if (w >> 23) & 0b111111 == 0b100010 {
        return Some(A64Decoded::AddSubImm {
            sf: w >> 31,
            op: (w >> 30) & 1,
            s: (w >> 29) & 1,
            sh: (w >> 22) & 1,
            imm12: (w >> 10) & 0xFFF,
            rn: (w >> 5) & 0b11111,
            rd: w & 0b11111,
        });
    }
    // B / BL: bits 30:26 == 00101.
    if (w >> 26) & 0b11111 == 0b00101 {
        return Some(A64Decoded::BranchImm {
            link: (w >> 31) == 1,
            imm26: w & 0x03FF_FFFF,
        });
    }
    // B.cond: bits 31:24 == 01010100 and bit 4 == 0.
    if (w >> 24) == 0b0101_0100 && (w >> 4) & 1 == 0 {
        return Some(A64Decoded::CondBranch {
            cond: w & 0b1111,
            imm19: (w >> 5) & 0x7FFFF,
        });
    }
    // CBZ / CBNZ: bits 30:25 == 011010.
    if (w >> 25) & 0b111111 == 0b011010 {
        return Some(A64Decoded::CmpBranch {
            sf: w >> 31,
            negated: (w >> 24) & 1 == 1,
            imm19: (w >> 5) & 0x7FFFF,
            rt: w & 0b11111,
        });
    }
    // Add/subtract (shifted register): bits 28:24 == 01011 and bit 21 == 0.
    if (w >> 24) & 0b11111 == 0b01011 && (w >> 21) & 1 == 0 {
        return Some(A64Decoded::AddSubShiftedReg {
            sf: w >> 31,
            op: (w >> 30) & 1,
            s: (w >> 29) & 1,
            shift: (w >> 22) & 0b11,
            rm: (w >> 16) & 0b11111,
            imm6: (w >> 10) & 0b111111,
            rn: (w >> 5) & 0b11111,
            rd: w & 0b11111,
        });
    }
    // Logical (shifted register): bits 28:24 == 01010.
    if (w >> 24) & 0b11111 == 0b01010 {
        return Some(A64Decoded::LogicalShiftedReg {
            sf: w >> 31,
            opc: (w >> 29) & 0b11,
            shift: (w >> 22) & 0b11,
            n: (w >> 21) & 1,
            rm: (w >> 16) & 0b11111,
            imm6: (w >> 10) & 0b111111,
            rn: (w >> 5) & 0b11111,
            rd: w & 0b11111,
        });
    }
    // Load/store register (unsigned immediate): bits 29:27 == 111, 25:24 == 01.
    if (w >> 27) & 0b111 == 0b111 && (w >> 24) & 0b11 == 0b01 {
        return Some(A64Decoded::LoadStoreUi {
            size: w >> 30,
            v: (w >> 26) & 1,
            opc: (w >> 22) & 0b11,
            imm12: (w >> 10) & 0xFFF,
            rn: (w >> 5) & 0b11111,
            rt: w & 0b11111,
        });
    }
    // Load/store register (unscaled immediate, LDUR/STUR): bits 29:27 == 111,
    // 25:24 == 00, bit 21 == 0, bits 11:10 == 00 (01/11 are post/pre-index).
    if (w >> 27) & 0b111 == 0b111
        && (w >> 24) & 0b11 == 0b00
        && (w >> 21) & 1 == 0
        && (w >> 10) & 0b11 == 0b00
    {
        // Sign-extend the 9-bit immediate.
        let raw9 = ((w >> 12) & 0x1FF) as i32;
        let imm9 = (raw9 << 23) >> 23;
        return Some(A64Decoded::LoadStoreUnscaled {
            size: w >> 30,
            v: (w >> 26) & 1,
            opc: (w >> 22) & 0b11,
            imm9,
            rn: (w >> 5) & 0b11111,
            rt: w & 0b11111,
        });
    }
    // Load/store pre/post-index: bits 29:27 == 111, 25:24 == 00,
    // bit21 == 0, bit10 == 1; bit11 selects pre (1) versus post (0).
    // This is distinct from the unchanged unscaled mode00 decoder above.
    if (w >> 27) & 0b111 == 0b111
        && (w >> 24) & 0b11 == 0b00
        && (w >> 21) & 1 == 0
        && (w >> 10) & 1 == 1
    {
        let raw9 = ((w >> 12) & 0x1FF) as i32;
        let imm9 = (raw9 << 23) >> 23;
        return Some(A64Decoded::LoadStoreWriteback {
            size: w >> 30,
            v: (w >> 26) & 1,
            opc: (w >> 22) & 0b11,
            imm9,
            pre_index: (w >> 11) & 1 != 0,
            rn: (w >> 5) & 0b11111,
            rt: w & 0b11111,
        });
    }
    // Register offset: size | 111 | V | 00 | opc | 1 | Rm | option | S | 10 | Rn | Rt.
    // Keep the immediate and writeback families above independent of this form.
    if (w >> 27) & 0b111 == 0b111
        && (w >> 24) & 0b11 == 0b00
        && (w >> 21) & 1 == 1
        && (w >> 10) & 0b11 == 0b10
    {
        return Some(A64Decoded::LoadStoreRegisterOffset {
            size: w >> 30,
            v: (w >> 26) & 1,
            opc: (w >> 22) & 0b11,
            rm: (w >> 16) & 0b11111,
            option: (w >> 13) & 0b111,
            s: (w >> 12) & 1,
            rn: (w >> 5) & 0b11111,
            rt: w & 0b11111,
        });
    }
    // Load/store exclusive register: bits 29:24 == 001000, o2 (bit 23) == 0,
    // o1 (bit 21) == 0 and Rt2 (bits 14:10) == 11111. The pair (o1 == 1) and
    // ordered/compare-and-swap (o2 == 1) spaces are out of this slice.
    if (w >> 24) & 0b111111 == 0b001000
        && (w >> 23) & 1 == 0
        && (w >> 21) & 1 == 0
        && (w >> 10) & 0b11111 == 0b11111
    {
        return Some(A64Decoded::LoadStoreExclusive {
            size: w >> 30,
            load: (w >> 22) & 1 == 1,
            o0: (w >> 15) & 1,
            rs: (w >> 16) & 0b11111,
            rn: (w >> 5) & 0b11111,
            rt: w & 0b11111,
        });
    }
    // Load/store exclusive pair: bit 31 == 1, bits 29:24 == 001000,
    // o2 (bit 23) == 0 and o1 (bit 21) == 1.
    if w >> 31 == 1 && (w >> 24) & 0b111111 == 0b001000 && (w >> 23) & 1 == 0 && (w >> 21) & 1 == 1
    {
        return Some(A64Decoded::LoadStoreExclusivePair {
            sz: (w >> 30) & 1,
            load: (w >> 22) & 1 == 1,
            o0: (w >> 15) & 1,
            rs: (w >> 16) & 0b11111,
            rt2: (w >> 10) & 0b11111,
            rn: (w >> 5) & 0b11111,
            rt: w & 0b11111,
        });
    }
    // CLREX: system instruction op0=00, op1=011, CRn=0011, op2=010, Rt=11111.
    if w & 0xffff_f0ff == 0xd503_305f {
        return Some(A64Decoded::ClearExclusive {
            crm: (w >> 8) & 0b1111,
        });
    }
    // Bitfield: bits 28:23 == 100110.
    if (w >> 23) & 0b111111 == 0b100110 {
        let opc = (w >> 29) & 0b11;
        if opc == 0b11 {
            return None; // unallocated
        }
        return Some(A64Decoded::Bitfield {
            sf: w >> 31,
            opc,
            n: (w >> 22) & 1,
            immr: (w >> 16) & 0b111111,
            imms: (w >> 10) & 0b111111,
            rn: (w >> 5) & 0b11111,
            rd: w & 0b11111,
        });
    }
    // Conditional select: bits 28:21 == 11010100, S(29) == 0,
    // and the fixed high bit of op2 (bit 11) == 0.
    if (w >> 21) & 0xFF == 0b1101_0100 && (w >> 29) & 1 == 0 && (w >> 11) & 1 == 0 {
        return Some(A64Decoded::CondSelect {
            sf: w >> 31,
            op: (w >> 30) & 1,
            rm: (w >> 16) & 0b11111,
            cond: (w >> 12) & 0b1111,
            op2: (w >> 10) & 0b11,
            rn: (w >> 5) & 0b11111,
            rd: w & 0b11111,
        });
    }
    // Scalar FP conditional select: fixed bits31:24=00011110, bit21=1,
    // and bits11:10=11. ftype23:22 is00(S) or01(D) for this admitted slice.
    // Half11 and reserved10 do not establish an S/D intent match.
    if w & 0xff20_0c00 == 0x1e20_0c00 {
        let ftype = (w >> 22) & 0b11;
        if ftype > 1 {
            return None;
        }
        return Some(A64Decoded::FpCondSelect {
            ftype,
            rm: (w >> 16) & 0b11111,
            cond: (w >> 12) & 0b1111,
            rn: (w >> 5) & 0b11111,
            rd: w & 0b11111,
        });
    }
    // Data-processing (2 source): bits 30:21 == 0011010110 (S == 0).
    if (w >> 21) & 0b11_1111_1111 == 0b00_1101_0110 {
        return Some(A64Decoded::DataProc2Src {
            sf: w >> 31,
            rm: (w >> 16) & 0b11111,
            opcode: (w >> 10) & 0b111111,
            rn: (w >> 5) & 0b11111,
            rd: w & 0b11111,
        });
    }
    // Data-processing (3 source): bits 28:24 == 11011.
    if (w >> 24) & 0b11111 == 0b11011 {
        return Some(A64Decoded::DataProc3Src {
            sf: w >> 31,
            op54: (w >> 29) & 0b11,
            op31: (w >> 21) & 0b111,
            rm: (w >> 16) & 0b11111,
            o0: (w >> 15) & 1,
            ra: (w >> 10) & 0b11111,
            rn: (w >> 5) & 0b11111,
            rd: w & 0b11111,
        });
    }
    // Unconditional branch (register): bits 31:25 == 1101011, and the fixed
    // op2/op3/op4 fields must hold their required values.
    if (w >> 25) == 0b1101011 {
        if (w >> 16) & 0b11111 != 0b11111 || (w >> 10) & 0b111111 != 0 || w & 0b11111 != 0 {
            return None; // PAC/ERET/DRPS variants — out of slice.
        }
        return Some(A64Decoded::BranchReg {
            opc: (w >> 21) & 0b1111,
            rn: (w >> 5) & 0b11111,
        });
    }
    None
}

// ---------------------------------------------------------------------------
// Intent-side accessors (reading what the MachInst CLAIMS; independence is
// required of the byte decoding above, not of reading the intent).
// ---------------------------------------------------------------------------

fn intent_reg(inst: &MachInst, idx: usize) -> Option<u32> {
    match inst.operands.get(idx)? {
        MachOperand::PReg(p) => Some(p.hw_enc() as u32),
        MachOperand::Special(SpecialReg::SP | SpecialReg::XZR | SpecialReg::WZR) => Some(31),
        _ => None,
    }
}

fn intent_sf(inst: &MachInst, idx: usize) -> u32 {
    match inst.operands.get(idx) {
        Some(MachOperand::PReg(p)) => match preg_class(*p) {
            RegClass::Gpr32 => 0,
            RegClass::Gpr64 => 1,
            _ => 1,
        },
        Some(MachOperand::Special(SpecialReg::SP | SpecialReg::XZR)) => 1,
        Some(MachOperand::Special(SpecialReg::WZR)) => 0,
        _ => 1,
    }
}

fn intent_imm(inst: &MachInst, idx: usize) -> Option<i64> {
    match inst.operands.get(idx)? {
        MachOperand::Imm(v) => Some(*v),
        _ => None,
    }
}

/// Conditional-select operands are W/X GPRs or the matching zero register,
/// never SP. Return (sf, register field) without defaulting malformed intents
/// to X registers or conflating SP with ZR's architectural encoding 31.
fn intent_cond_select_reg(inst: &MachInst, idx: usize) -> Option<(u32, u32)> {
    trust_cg_verify::aarch64_csel_semantics::conditional_select_register_fields(
        inst.operands.get(idx)?,
    )
}

/// Unlike register CMP, immediate CMP interprets register 31 as SP, not ZR.
/// Read the intent's actual W/X bank, including WSP; never infer a width from
/// a typed opcode to conceal a conflicting physical-register spelling.
fn intent_cmp_immediate_base(inst: &MachInst) -> Option<(u32, u32)> {
    match inst.operands.first()? {
        MachOperand::PReg(p) => match p.encoding() {
            0..=31 => Some((1, u32::from(p.encoding()))),
            32..=63 => Some((0, u32::from(p.encoding() - 32))),
            _ => None,
        },
        MachOperand::Special(SpecialReg::SP) => Some((1, 31)),
        _ => None,
    }
}

/// Read only canonical S/D physical registers, preserving the real register31
/// in both banks. Neither general-purpose/ZR nor generic V/H spellings denote
/// an admitted scalar FCSEL intent. Return (ftype, register field).
fn intent_fp_cond_select_reg(inst: &MachInst, idx: usize) -> Option<(u32, u32)> {
    let MachOperand::PReg(p) = inst.operands.get(idx)? else {
        return None;
    };
    match p.encoding() {
        96..=127 => Some((1, u32::from(p.encoding() - 96))),
        128..=159 => Some((0, u32::from(p.encoding() - 128))),
        _ => None,
    }
}

/// Canonical H/S/D/Q transfer intent: (size, byte scale, high opc bit, Rt).
/// Q needs size00/opc1x; it is not the scalar D view. Every FP bank has a
/// genuine register31. B and malformed/virtual/system operands are excluded.
fn intent_fp_memory_transfer(inst: &MachInst) -> Option<(u32, i64, u32, u32)> {
    let MachOperand::PReg(p) = inst.operands.first()? else {
        return None;
    };
    match p.encoding() {
        64..=95 => Some((0, 16, 2, u32::from(p.encoding() - 64))),
        96..=127 => Some((3, 8, 0, u32::from(p.encoding() - 96))),
        128..=159 => Some((2, 4, 0, u32::from(p.encoding() - 128))),
        165..=196 => Some((1, 2, 0, u32::from(p.encoding() - 165))),
        _ => None,
    }
}

/// Canonical GPR immediate-memory intent: (size, byte scale, opc, Rt).
/// The same W/X/ZR data banks as conditional select exclude SP. Unsigned
/// byte/halfword operations admit both W and X aliases (including X-carried
/// Bool values); signed loads use the actual bank to select the extension.
fn intent_gpr_memory_transfer(inst: &MachInst) -> Option<(u32, i64, u32, u32)> {
    use AArch64Opcode as Op;
    let (sf, rt) = intent_cond_select_reg(inst, 0)?;
    let (size, scale, opc) = match inst.opcode {
        Op::LdrRI | Op::VolatileLdrRI => {
            if sf == 1 {
                (3, 8, 1)
            } else {
                (2, 4, 1)
            }
        }
        Op::StrRI | Op::VolatileStrRI => {
            if sf == 1 {
                (3, 8, 0)
            } else {
                (2, 4, 0)
            }
        }
        Op::LdrbRI | Op::VolatileLdrbRI => (0, 1, 1),
        Op::StrbRI | Op::VolatileStrbRI => (0, 1, 0),
        Op::LdrhRI | Op::VolatileLdrhRI => (1, 2, 1),
        Op::StrhRI | Op::VolatileStrhRI => (1, 2, 0),
        Op::LdrsbRI => (0, 1, if sf == 1 { 2 } else { 3 }),
        Op::LdrshRI => (1, 2, if sf == 1 { 2 } else { 3 }),
        _ => return None,
    };
    Some((size, scale, opc, rt))
}

/// Read the entire memory address shape, preserving X/SP identity rather
/// than accepting another register bank with the same five hardware bits.
fn intent_memory_address(inst: &MachInst) -> Option<(u32, i64)> {
    let base_field = |arg: &MachOperand| match arg {
        MachOperand::PReg(p) if p.encoding() <= 31 => Some(u32::from(p.encoding())),
        MachOperand::Special(SpecialReg::SP) => Some(31),
        _ => None,
    };
    match inst.operands.as_slice() {
        [_, MachOperand::MemOp { base, offset }] if base.encoding() <= 31 => {
            Some((u32::from(base.encoding()), *offset))
        }
        [_, base] => Some((base_field(base)?, 0)),
        [_, base, MachOperand::Imm(offset)] => Some((base_field(base)?, *offset)),
        _ => None,
    }
}

/// Exact RO address: X/SP base, W/X/ZR index, and the closed packed-mode set.
/// Low32 extensions can observe W or X carriers. Full64 modes require X,
/// except either zero-register spelling denotes the same known 64-bit zero.
/// This does not infer zero-extension for an arbitrary physical W register.
fn intent_register_offset_address(inst: &MachInst) -> Option<(u32, u32, u32, u32)> {
    let packed = match inst.operands.as_slice() {
        [_, _, _] => 6,
        [_, _, _, MachOperand::Imm(value)]
            if matches!(*value, 4 | 5 | 6 | 7 | 12 | 13 | 14 | 15) =>
        {
            *value
        }
        _ => return None,
    };
    let rn = match &inst.operands[1] {
        MachOperand::PReg(p) if p.encoding() <= 31 => u32::from(p.encoding()),
        MachOperand::Special(SpecialReg::SP) => 31,
        _ => return None,
    };
    let (sf, rm) = intent_cond_select_reg(inst, 2)?;
    let option = (packed >> 1) as u32;
    if sf == 0 && !matches!(option, 0b010 | 0b110) && rm != 31 {
        return None;
    }
    Some((rn, rm, option, (packed & 1) as u32))
}

fn mismatch(msg: String) -> DecodeCheckOutcome {
    DecodeCheckOutcome::Mismatch(DecodeCheckError { message: msg })
}

/// Compare a decoded field against the intent's claim.
macro_rules! expect_field {
    ($what:expr, $got:expr, $want:expr) => {
        if $got != $want {
            return mismatch(format!(
                "{}: decoded {} but the intent requires {}",
                $what, $got, $want
            ));
        }
    };
}

/// Mode for the AArch64 gate: enforce by default, including for unrecognized
/// `TCG_DECODE_CHECK_A64` values. That variable accepts explicit off/warn
/// overrides; the shared `TCG_NO_DECODE_CHECK` triage opt-out takes precedence.
/// Disabling enforcement is diagnostic policy, not evidence of correctness.
pub fn a64_decode_check_mode() -> crate::decode_check::DecodeCheckMode {
    use crate::decode_check::DecodeCheckMode;
    if trust_cg_process_env::var_os("TCG_NO_DECODE_CHECK").is_some() {
        return DecodeCheckMode::Off;
    }
    match trust_cg_process_env::var("TCG_DECODE_CHECK_A64")
        .ok()
        .as_deref()
    {
        Some("off") | Some("0") | Some("false") => DecodeCheckMode::Off,
        Some("warn") => DecodeCheckMode::Warn,
        // DEFAULT-ON: any unset / unrecognized value enforces.
        _ => DecodeCheckMode::Enforce,
    }
}

/// The AArch64 [`DecodeCheck`] implementation.
pub struct A64DecodeCheck;

impl DecodeCheck for A64DecodeCheck {
    type Intent = MachInst;

    fn arch(&self) -> &'static str {
        "aarch64"
    }

    fn label(&self, intent: &Self::Intent) -> String {
        format!("{:?}", intent.opcode)
    }

    fn check_one(
        &self,
        intent: &Self::Intent,
        bytes: &[u8],
        hole: Option<&FixupHole>,
    ) -> DecodeCheckOutcome {
        // Every AArch64 instruction is exactly one little-endian 32-bit word.
        let Ok(word_bytes): Result<[u8; 4], _> = bytes.try_into() else {
            return mismatch(format!(
                "instruction byte range is {} bytes; AArch64 instructions are exactly 4",
                bytes.len()
            ));
        };
        let w = u32::from_le_bytes(word_bytes);
        let decoded = decode_word(w);

        // Decoded-word value obligation (the per-compile run the coverage
        // gate's MovR/MOVWrr/MOVXrr/FMOV/SMULL/BFM/RBIT/ADD-LSL#12/MRS/FCVT
        // credits name; the typed post-allocation copies also keep the
        // structural register-move arm below). It
        // decodes the same word independently of `decode_word` and compares its
        // Arm ARM effect on the whole destination register with the intent. A
        // refutation or an ill-formed instruction (for example an FMOV between
        // a W register and a D register, whose word is unallocated) fails the
        // compile in `enforce` mode; a shape outside the model makes no claim.
        let value_verdict = value_proofs::a64_value_forms(intent.opcode)
            .map(|_| value_proofs::check_emitted_a64_value_word(intent, w));
        if let Some(Err(
            error @ (value_proofs::A64ValueCheckError::Refuted(_)
            | value_proofs::A64ValueCheckError::IllFormed(_)),
        )) = &value_verdict
        {
            return mismatch(format!(
                "aarch64_value_decode_proofs rejected {:?} = {w:#010x}: {error}",
                intent.opcode
            ));
        }

        // Instruction-word binding (L07-P2): for every admitted shape of the
        // opcodes the verifier judges by an instruction-derived obligation
        // (`aarch64_instruction_word_proofs`), the emitted word must be the
        // word that obligation decodes, outside fixup/relocation holes. The
        // structural arms below still decide the fields independently.
        if let Some(Err(detail)) =
            trust_cg_verify::aarch64_instruction_word_proofs::check_emitted_instruction_word(
                intent, w,
            )
        {
            return mismatch(format!("{:?}: {detail}", intent.opcode));
        }

        // Memory-effect binding (L07-P2, X-OPCODES-P1): for every admitted
        // scalar immediate or pair memory shape, the emitted word must be the
        // literal every part of the verifier's word-bound memory-effect
        // decomposition (`aarch64_memory_effect`) carries, so a checked
        // certificate of a part is a certificate about the word the object
        // carries. The pair and scalar field checks below still run.
        if let Some(Err(detail)) =
            trust_cg_verify::aarch64_memory_effect::check_emitted_memory_effect_word(intent, w)
        {
            return mismatch(format!("{:?}: {detail}", intent.opcode));
        }

        // Atomic binding (X-OPCODES-P2): for every admitted single-instruction
        // atomic shape (LDAR/STLR/CAS/SWP/LD<op>), the emitted word must be the
        // literal every part of the verifier's word-bound atomic decomposition
        // (`aarch64_atomic_effect`) carries and must decode back to the
        // operands' atomic form, so the certificate of that form theorem is
        // about the word the object carries. The integer slice below still
        // decodes the fields independently.
        if let Some(Err(detail)) =
            trust_cg_verify::aarch64_atomic_effect::check_emitted_atomic_word(intent, w)
        {
            return mismatch(format!("{:?}: {detail}", intent.opcode));
        }

        // CRC32 binding (L04-P1): for every admitted CRC32/CRC32C shape the
        // emitted word must be the word the verifier's decoded-word
        // obligation re-derives (`aarch64_crc32_proofs`), and that word must
        // hold against the operands' reflected-CRC intent for every register
        // value. The integer slice below still decodes the fields
        // independently.
        if let Some(Err(detail)) =
            trust_cg_verify::aarch64_crc32_proofs::check_emitted_crc32_word(intent, w)
        {
            return mismatch(format!("{:?}: {detail}", intent.opcode));
        }

        // SUBS #imm binding (L04-P1): the emitted word of an admitted
        // `SubsRI` must be the word the verifier's decoded-word obligation
        // re-derives (`aarch64_subs_imm_proofs`), holding for every register
        // value.
        if let Some(Err(detail)) =
            trust_cg_verify::aarch64_subs_imm_proofs::check_emitted_subs_imm_word(intent, w)
        {
            return mismatch(format!("{:?}: {detail}", intent.opcode));
        }

        // NEON lane-effect binding (L04-P6): for every admitted NEON
        // horizontal-reduction or permute shape, the emitted word must be the
        // literal every part of the verifier's word-bound lane-effect
        // decomposition (`aarch64_neon_lane_effect`) carries. The FP/SIMD
        // slice below still decodes every field independently.
        if let Some(Err(detail)) =
            trust_cg_verify::aarch64_neon_lane_effect::check_emitted_neon_lane_effect_word(
                intent, w,
            )
        {
            return mismatch(format!("{:?}: {detail}", intent.opcode));
        }

        Self::check_structural_tail(intent, bytes, w, decoded, value_verdict, hole)
    }
}

// Keep the structural match's frame out of the mandatory value, instruction,
// memory and NEON obligation calls. Both stages retain their original order;
// the already independently decoded fields and value verdict are transferred,
// not recomputed, and every original structural/allowlist arm remains below.
impl A64DecodeCheck {
    #[inline(never)]
    fn check_structural_tail(
        intent: &MachInst,
        bytes: &[u8],
        w: u32,
        decoded: Option<A64Decoded>,
        value_verdict: Option<
            Result<value_proofs::A64ValueVerdict, value_proofs::A64ValueCheckError>,
        >,
        hole: Option<&FixupHole>,
    ) -> DecodeCheckOutcome {
        // ---- Scalar FP and Advanced SIMD (the FP/SIMD slice) -------------
        // Every opcode the slice owns is decoded field by field from its Arm
        // ARM encoding class, whatever the value obligation above concluded:
        // for the scalar FMOV/FCVT-half copies and the NEON bitwise ops that
        // obligation (and the bound 16B check) is a second, independent
        // decode that must also agree, never a substitute for this one. No
        // FP/SIMD word carries a relocation hole.
        if let Some(verdict) = super::decode_check_fp_simd::check_fp_simd(intent, w) {
            if hole.is_some() {
                return mismatch(format!(
                    "{:?} is an FP/SIMD word and cannot contain a relocation hole",
                    intent.opcode
                ));
            }
            if let Some(Err(detail)) = value_proofs::check_neon_bitwise_16b_word(intent, w) {
                return mismatch(format!(
                    "{:?} {w:#010x} does not encode the bound 16B intent: {detail}",
                    intent.opcode
                ));
            }
            return match verdict {
                Ok(()) => DecodeCheckOutcome::Match,
                Err(detail) => mismatch(format!("{:?} {w:#010x}: {detail}", intent.opcode)),
            };
        }
        // ---- General-purpose, PC-relative, atomic, barrier and trap words --
        // (the integer slice). It checks its own relocation holes.
        if let Some(verdict) = super::decode_check_int::check_int(intent, w, hole) {
            return match verdict {
                Ok(()) => DecodeCheckOutcome::Match,
                Err(detail) => mismatch(format!("{:?} {w:#010x}: {detail}", intent.opcode)),
            };
        }

        use AArch64Opcode as Op;
        match intent.opcode {
            // ---- Decoded-value opcodes without a structural arm ------------
            // The value obligation above is their decode check: it accepted the
            // word (Match) or made no claim for this shape (named allowlist).
            Op::Smull | Op::Rbit | Op::Mrs => match value_verdict {
                Some(Ok(_)) => DecodeCheckOutcome::Match,
                _ => DecodeCheckOutcome::Allowlisted(
                    "a64-value: shape outside the decoded value model",
                ),
            },

            // ---- Move wide -------------------------------------------------
            Op::MovI | Op::Movz | Op::Movn | Op::Movk | Op::MOVZWi | Op::MOVZXi => {
                let Some(A64Decoded::MoveWide {
                    sf,
                    opc,
                    hw,
                    imm16,
                    rd,
                }) = decoded
                else {
                    return mismatch(format!(
                        "intent {:?} but the word does not decode as move-wide",
                        intent.opcode
                    ));
                };
                let want_opc = match intent.opcode {
                    Op::MovI | Op::Movz | Op::MOVZWi | Op::MOVZXi => 0b10,
                    Op::Movn => 0b00,
                    Op::Movk => 0b11,
                    _ => unreachable!(),
                };
                // The typed MOVZ aliases own their width; the intent's
                // destination bank must agree with it.
                let want_sf = match intent.opcode {
                    Op::MOVZWi => 0,
                    Op::MOVZXi => 1,
                    _ => intent_sf(intent, 0),
                };
                expect_field!("move-wide typed width", intent_sf(intent, 0), want_sf);
                expect_field!("move-wide opc", opc, want_opc);
                expect_field!("move-wide sf", sf, want_sf);
                let Some(rd_want) = intent_reg(intent, 0) else {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice1: non-register move-wide dst",
                    );
                };
                expect_field!("move-wide Rd", rd, rd_want);
                let Some(imm_want) = intent_imm(intent, 1) else {
                    return DecodeCheckOutcome::Allowlisted("a64-slice1: non-imm move-wide source");
                };
                expect_field!("move-wide imm16", i64::from(imm16), imm_want & 0xFFFF);
                // Only MOVK carries a nonzero LSL shift in the v0.1
                // publication subset. MovI, MOVZ, and MOVN all emit hw=0.
                let hw_want = if intent.opcode == Op::Movk {
                    match intent_imm(intent, 2) {
                        Some(shift) => (shift / 16) as u32,
                        None => 0,
                    }
                } else {
                    0
                };
                expect_field!("move-wide hw", hw, hw_want);
                DecodeCheckOutcome::Match
            }

            // ---- Add/sub immediate ----------------------------------------
            Op::AddRI | Op::AddRIShift12 | Op::SubRI => {
                match trust_cg_verify::aarch64_add_sub_immediate::bind_add_sub_immediate_word(
                    intent, w,
                ) {
                    Ok(_) => DecodeCheckOutcome::Match,
                    Err(error) => mismatch(error.to_string()),
                }
            }

            // ---- B / BL ----------------------------------------------------
            Op::B | Op::TailCall | Op::Bl | Op::BL => {
                let Some(A64Decoded::BranchImm { link, imm26 }) = decoded else {
                    return mismatch(format!(
                        "intent {:?} but the word does not decode as B/BL",
                        intent.opcode
                    ));
                };
                let want_link = matches!(intent.opcode, Op::Bl | Op::BL);
                expect_field!("branch link bit", u32::from(link), u32::from(want_link));
                // A Symbol/Block target is a pre-layout placeholder patched by
                // the fixup pass — the imm26 VALUE is checked only when the
                // emission recorded a hole (placement verified by the driver)
                // or the intent carries a resolved immediate.
                if hole.is_some() {
                    return DecodeCheckOutcome::Match;
                }
                match intent_imm(intent, 0) {
                    Some(imm_want) => {
                        expect_field!("branch imm26", i64::from(imm26), imm_want & 0x03FF_FFFF);
                        DecodeCheckOutcome::Match
                    }
                    None => DecodeCheckOutcome::Allowlisted(
                        "a64-slice1: unresolved branch target (no fixup hole recorded)",
                    ),
                }
            }

            // ---- BR / BLR / RET -------------------------------------------
            Op::Br | Op::Blr | Op::BLR | Op::Ret => {
                let Some(A64Decoded::BranchReg { opc, rn }) = decoded else {
                    return mismatch(format!(
                        "intent {:?} but the word does not decode as a register branch",
                        intent.opcode
                    ));
                };
                let want_opc = match intent.opcode {
                    Op::Br => 0b0000,
                    Op::Blr | Op::BLR => 0b0001,
                    Op::Ret => 0b0010,
                    _ => unreachable!(),
                };
                expect_field!("branch-reg opc", opc, want_opc);
                let rn_want = if matches!(intent.opcode, Op::Ret) {
                    // RET's operand-less form implies X30.
                    intent_reg(intent, 0).unwrap_or(30)
                } else {
                    match intent_reg(intent, 0) {
                        Some(r) => r,
                        None => {
                            return DecodeCheckOutcome::Allowlisted(
                                "a64-slice1: non-register branch-reg operand",
                            );
                        }
                    }
                };
                expect_field!("branch-reg Rn", rn, rn_want);
                DecodeCheckOutcome::Match
            }

            // ---- CBZ / CBNZ ------------------------------------------------
            Op::Cbz | Op::Cbnz => {
                let Some(A64Decoded::CmpBranch {
                    sf,
                    negated,
                    imm19,
                    rt,
                }) = decoded
                else {
                    return mismatch(format!(
                        "intent {:?} but the word does not decode as CBZ/CBNZ",
                        intent.opcode
                    ));
                };
                expect_field!(
                    "cmp-branch negated",
                    u32::from(negated),
                    u32::from(matches!(intent.opcode, Op::Cbnz))
                );
                expect_field!("cmp-branch sf", sf, intent_sf(intent, 0));
                let Some(rt_want) = intent_reg(intent, 0) else {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice1: non-register cmp-branch operand",
                    );
                };
                expect_field!("cmp-branch Rt", rt, rt_want);
                if hole.is_some() {
                    return DecodeCheckOutcome::Match;
                }
                match intent_imm(intent, 1) {
                    Some(imm_want) => {
                        expect_field!("cmp-branch imm19", i64::from(imm19), imm_want & 0x7FFFF);
                        DecodeCheckOutcome::Match
                    }
                    None => {
                        DecodeCheckOutcome::Allowlisted("a64-slice1: unresolved cmp-branch target")
                    }
                }
            }

            // ---- Plain shifted-register ALU (shift amount 0) ---------------
            Op::AddRR | Op::SubRR => {
                if intent.operands.len() > 3 {
                    // A shifted variant (extra shift operand) — later slice.
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice3: shifted add/sub variant not yet decoded",
                    );
                }
                let Some(A64Decoded::AddSubShiftedReg {
                    sf,
                    op,
                    s,
                    shift,
                    rm,
                    imm6,
                    rn,
                    rd,
                }) = decoded
                else {
                    return mismatch(format!(
                        "intent {:?} but the word does not decode as add/sub shifted-reg",
                        intent.opcode
                    ));
                };
                expect_field!(
                    "add/sub-reg op",
                    op,
                    u32::from(matches!(intent.opcode, Op::SubRR))
                );
                expect_field!("add/sub-reg S", s, 0);
                expect_field!("add/sub-reg shift", shift, 0);
                expect_field!("add/sub-reg imm6", imm6, 0);
                expect_field!("add/sub-reg sf", sf, intent_sf(intent, 0));
                let (Some(rd_want), Some(rn_want), Some(rm_want)) = (
                    intent_reg(intent, 0),
                    intent_reg(intent, 1),
                    intent_reg(intent, 2),
                ) else {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice3: non-register add/sub-reg operand",
                    );
                };
                expect_field!("add/sub-reg Rd", rd, rd_want);
                expect_field!("add/sub-reg Rn", rn, rn_want);
                expect_field!("add/sub-reg Rm", rm, rm_want);
                DecodeCheckOutcome::Match
            }

            Op::AndRR | Op::OrrRR | Op::EorRR => {
                if intent.operands.len() > 3 {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice3: shifted logical variant not yet decoded",
                    );
                }
                let Some(A64Decoded::LogicalShiftedReg {
                    sf,
                    opc,
                    shift,
                    n,
                    rm,
                    imm6,
                    rn,
                    rd,
                }) = decoded
                else {
                    return mismatch(format!(
                        "intent {:?} but the word does not decode as logical shifted-reg",
                        intent.opcode
                    ));
                };
                let want_opc = match intent.opcode {
                    Op::AndRR => 0b00,
                    Op::OrrRR => 0b01,
                    Op::EorRR => 0b10,
                    _ => unreachable!(),
                };
                expect_field!("logical-reg opc", opc, want_opc);
                expect_field!("logical-reg N", n, 0);
                expect_field!("logical-reg shift", shift, 0);
                expect_field!("logical-reg imm6", imm6, 0);
                expect_field!("logical-reg sf", sf, intent_sf(intent, 0));
                let (Some(rd_want), Some(rn_want), Some(rm_want)) = (
                    intent_reg(intent, 0),
                    intent_reg(intent, 1),
                    intent_reg(intent, 2),
                ) else {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice3: non-register logical-reg operand",
                    );
                };
                expect_field!("logical-reg Rd", rd, rd_want);
                expect_field!("logical-reg Rn", rn, rn_want);
                expect_field!("logical-reg Rm", rm, rm_want);
                DecodeCheckOutcome::Match
            }

            Op::EorRRShift | Op::EorRRLsl | Op::EorRRLsr => {
                let Some(A64Decoded::LogicalShiftedReg {
                    sf,
                    opc,
                    shift,
                    n,
                    rm,
                    imm6,
                    rn,
                    rd,
                }) = decoded
                else {
                    return mismatch(format!(
                        "intent {:?} but the word does not decode as logical shifted-reg",
                        intent.opcode
                    ));
                };
                let want_shift = match intent.opcode {
                    Op::EorRRLsl => 0b00,
                    Op::EorRRLsr => 0b01,
                    Op::EorRRShift => 0b11,
                    _ => unreachable!(),
                };
                let Some(imm_want) = intent_imm(intent, 3) else {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice3: non-immediate EOR shifted-register amount",
                    );
                };
                expect_field!("EOR-shift opc", opc, 0b10);
                expect_field!("EOR-shift N", n, 0);
                expect_field!("EOR-shift kind", shift, want_shift);
                expect_field!("EOR-shift imm6", i64::from(imm6), imm_want);
                expect_field!("EOR-shift sf", sf, intent_sf(intent, 0));
                let (Some(rd_want), Some(rn_want), Some(rm_want)) = (
                    intent_reg(intent, 0),
                    intent_reg(intent, 1),
                    intent_reg(intent, 2),
                ) else {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice3: non-register EOR shifted-register operand",
                    );
                };
                expect_field!("EOR-shift Rd", rd, rd_want);
                expect_field!("EOR-shift Rn", rn, rn_want);
                expect_field!("EOR-shift Rm", rm, rm_want);
                DecodeCheckOutcome::Match
            }

            // ---- Matched W/X/ZR or S/D/Q pair memory -----------------------
            Op::StpRI
            | Op::LdpRI
            | Op::StpPreIndex
            | Op::LdpPostIndex
            | Op::NeonLdpQPost
            | Op::NeonStpQPost => {
                if hole.is_some() {
                    return mismatch("pair memory cannot contain a relocation hole".into());
                }
                // Shared encoding evidence only; no instruction/source proof
                // credit follows from a descriptor. The encoder is independent.
                match check_pair_encoding(intent, bytes) {
                    Ok(_) => DecodeCheckOutcome::Match,
                    Err(error) => mismatch(error.to_string()),
                }
            }

            // ---- Scalar GPR or H/S/D/Q register-offset memory -------------
            Op::LdrRO | Op::StrRO | Op::LdrbRO | Op::LdrhRO | Op::StrbRO | Op::StrhRO => {
                if hole.is_some() {
                    return mismatch(
                        "register-offset memory cannot contain a relocation hole".into(),
                    );
                }
                let Some((rn_want, rm_want, option_want, s_want)) =
                    intent_register_offset_address(intent)
                else {
                    return mismatch("register-offset memory requires exactly transfer, X/SP base, a mode-compatible W/X/ZR index, and optional exact packed mode".into());
                };
                let is_load =
                    u32::from(matches!(intent.opcode, Op::LdrRO | Op::LdrbRO | Op::LdrhRO));
                let narrow_size = match intent.opcode {
                    Op::LdrbRO | Op::StrbRO => Some(0),
                    Op::LdrhRO | Op::StrhRO => Some(1),
                    _ => None,
                };
                let (size_want, v_want, opc_want, rt_want) = if let Some(size) = narrow_size {
                    let Some((_, rt)) = intent_cond_select_reg(intent, 0) else {
                        return mismatch(
                        "narrow register-offset transfer requires W/X/ZR, never SP or an FP bank"
                            .into(),
                    );
                    };
                    (size, 0, is_load, rt)
                } else if let Some((sf, rt)) = intent_cond_select_reg(intent, 0) {
                    (2 + sf, 0, is_load, rt)
                } else if let Some((size, _, high_opc, rt)) = intent_fp_memory_transfer(intent) {
                    (size, 1, high_opc | is_load, rt)
                } else {
                    return mismatch("register-offset memory requires a canonical W/X/ZR or H/S/D/Q transfer register".into());
                };
                let Some(A64Decoded::LoadStoreRegisterOffset {
                    size,
                    v,
                    opc,
                    rm,
                    option,
                    s,
                    rn,
                    rt,
                }) = decoded
                else {
                    return mismatch(
                        "register-offset intent does not decode as register-offset memory".into(),
                    );
                };
                // RO has no base writeback: matching data/base/index hardware
                // fields are legal and must not inherit a writeback overlap ban.
                expect_field!("register-offset size", size, size_want);
                expect_field!("register-offset V", v, v_want);
                expect_field!("register-offset opc", opc, opc_want);
                expect_field!("register-offset Rt", rt, rt_want);
                expect_field!("register-offset Rn", rn, rn_want);
                expect_field!("register-offset Rm", rm, rm_want);
                expect_field!("register-offset option", option, option_want);
                expect_field!("register-offset S", s, s_want);
                DecodeCheckOutcome::Match
            }

            // ---- Scalar GPR load/store with pre/post-index writeback -------
            Op::LdrPreIndex | Op::StrPreIndex | Op::LdrPostIndex | Op::StrPostIndex => {
                if hole.is_some() {
                    return mismatch(
                        "scalar writeback memory cannot contain a relocation hole".into(),
                    );
                }
                // Unlike non-writeback immediate memory, neither an omitted
                // offset nor a MemOp spelling is admitted by these opcodes.
                if !matches!(intent.operands.as_slice(), [_, _, MachOperand::Imm(_)]) {
                    return mismatch("scalar writeback memory requires exactly transfer, base, and immediate operands".into());
                }
                let Some((sf, rt_want)) = intent_cond_select_reg(intent, 0) else {
                    return mismatch(
                        "scalar writeback memory requires a canonical W/X/ZR transfer register"
                            .into(),
                    );
                };
                let Some((rn_want, offset)) = intent_memory_address(intent) else {
                    return mismatch(
                        "scalar writeback memory requires an X/SP base register".into(),
                    );
                };
                if !(-256..=255).contains(&offset) {
                    return mismatch(format!(
                        "scalar writeback memory offset {offset} is outside signed imm9"
                    ));
                }
                // Arm LDR/STR (immediate) constrains writeback overlap by
                // hardware register number, including Wt/Xn aliases. Rn31 is
                // SP and does not alias the transfer's zero-register meaning.
                if rn_want == rt_want && rn_want != 31 {
                    return mismatch(
                        "scalar writeback memory transfer overlaps its base register".into(),
                    );
                }
                let Some(A64Decoded::LoadStoreWriteback {
                    size,
                    v,
                    opc,
                    imm9,
                    pre_index,
                    rn,
                    rt,
                }) = decoded
                else {
                    return mismatch(
                        "scalar writeback intent does not decode as pre/post-index memory".into(),
                    );
                };
                let is_load = matches!(intent.opcode, Op::LdrPreIndex | Op::LdrPostIndex);
                let want_pre = matches!(intent.opcode, Op::LdrPreIndex | Op::StrPreIndex);
                expect_field!("scalar-writeback V", v, 0);
                expect_field!("scalar-writeback size", size, if sf == 1 { 3 } else { 2 });
                expect_field!("scalar-writeback opc", opc, u32::from(is_load));
                expect_field!("scalar-writeback pre-index", pre_index, want_pre);
                expect_field!("scalar-writeback Rt", rt, rt_want);
                expect_field!("scalar-writeback Rn", rn, rn_want);
                expect_field!("scalar-writeback imm9", i64::from(imm9), offset);
                DecodeCheckOutcome::Match
            }

            // ---- Load/store register (GPR or H/S/D/Q, imm offset) ----------
            // Volatile aliases have the same architectural words; these
            // checks establish byte/intent agreement, not memory ordering.
            Op::LdrRI
            | Op::StrRI
            | Op::VolatileLdrRI
            | Op::VolatileStrRI
            | Op::LdrbRI
            | Op::StrbRI
            | Op::LdrhRI
            | Op::StrhRI
            | Op::VolatileLdrbRI
            | Op::VolatileStrbRI
            | Op::VolatileLdrhRI
            | Op::VolatileStrhRI
            | Op::LdrsbRI
            | Op::LdrshRI => {
                // The fused `ADRP; LDR/STR Rt, [Xn, #:lo12:sym]` form is the
                // only immediate-memory word allowed to carry a relocation
                // hole: intent `[Rt, Xn, Symbol]`, a GlobalRef hole, and a
                // non-volatile opcode. Its fields are checked below with the
                // placeholder imm12 == 0 the linker later overwrites.
                let lo12_symbolic = matches!(
                    intent.operands.as_slice(),
                    [_, MachOperand::PReg(_), MachOperand::Symbol(_)]
                );
                match hole {
                    Some(hole)
                        if lo12_symbolic
                            && matches!(
                                hole.kind,
                                crate::decode_check::FixupHoleKind::GlobalRef
                            )
                            && !matches!(
                                intent.opcode,
                                Op::VolatileLdrRI
                                    | Op::VolatileStrRI
                                    | Op::VolatileLdrbRI
                                    | Op::VolatileStrbRI
                                    | Op::VolatileLdrhRI
                                    | Op::VolatileStrhRI
                            ) => {}
                    Some(_) => {
                        return mismatch(
                            "immediate memory cannot contain a relocation hole".into(),
                        );
                    }
                    None if lo12_symbolic => {
                        return mismatch(
                            "a symbolic lo12 memory operand requires its relocation hole".into(),
                        );
                    }
                    None => {}
                }
                let (want_v, want_size, scale, want_opc, rt_want) =
                    if let Some((size, scale, opc, rt)) = intent_gpr_memory_transfer(intent) {
                        (0, size, scale, opc, rt)
                    } else if matches!(
                        intent.opcode,
                        Op::LdrRI | Op::StrRI | Op::VolatileLdrRI | Op::VolatileStrRI
                    ) {
                        let Some((size, scale, high_opc, rt)) = intent_fp_memory_transfer(intent)
                        else {
                            return mismatch(
                        "immediate memory requires a canonical W/X/ZR or H/S/D/Q transfer register"
                            .into(),
                    );
                        };
                        let is_load = matches!(intent.opcode, Op::LdrRI | Op::VolatileLdrRI);
                        (1, size, scale, high_opc | u32::from(is_load), rt)
                    } else {
                        return mismatch(
                            "narrow immediate memory requires a canonical W/X/ZR transfer register"
                                .into(),
                        );
                    };
                if lo12_symbolic {
                    let Some(rn_want) = intent_reg(intent, 1).filter(|&rn| rn < 31) else {
                        return mismatch("a lo12 memory base must be an X register".into());
                    };
                    let Some(A64Decoded::LoadStoreUi {
                        size,
                        v,
                        opc,
                        imm12,
                        rn,
                        rt,
                    }) = decoded
                    else {
                        return mismatch(format!(
                            "intent {:?} with a lo12 relocation but the word does not decode as load/store unsigned-immediate",
                            intent.opcode
                        ));
                    };
                    let _ = scale;
                    expect_field!("load/store-ui lo12 V", v, want_v);
                    expect_field!("load/store-ui lo12 size", size, want_size);
                    expect_field!("load/store-ui lo12 opc", opc, want_opc);
                    expect_field!("load/store-ui lo12 Rt", rt, rt_want);
                    expect_field!("load/store-ui lo12 Rn", rn, rn_want);
                    expect_field!("load/store-ui lo12 placeholder imm12", imm12, 0);
                    return DecodeCheckOutcome::Match;
                }
                let Some((rn_want, offset)) = intent_memory_address(intent) else {
                    return mismatch(
                        "immediate memory requires an exact X/SP address shape".into(),
                    );
                };
                // The canonical intent uses unsigned scaled form whenever
                // possible, otherwise signed imm9. Check the original i64
                // before comparing fields; no truncation can legalize it.
                let scaled_ui = offset >= 0 && offset % scale == 0 && (offset / scale) <= 0xFFF;
                if !scaled_ui && !(-256..=255).contains(&offset) {
                    return mismatch(format!("immediate memory offset {offset} is not encodable"));
                }
                if scaled_ui {
                    let Some(A64Decoded::LoadStoreUi {
                        size,
                        v,
                        opc,
                        imm12,
                        rn,
                        rt,
                    }) = decoded
                    else {
                        return mismatch(format!(
                            "intent {:?} (offset {offset}) but the word does not decode as                              load/store unsigned-immediate",
                            intent.opcode
                        ));
                    };
                    expect_field!("load/store-ui V", v, want_v);
                    expect_field!("load/store-ui size", size, want_size);
                    expect_field!("load/store-ui opc", opc, want_opc);
                    expect_field!("load/store-ui Rt", rt, rt_want);
                    expect_field!("load/store-ui Rn", rn, rn_want);
                    expect_field!("load/store-ui imm12", i64::from(imm12), offset / scale);
                    DecodeCheckOutcome::Match
                } else {
                    let Some(A64Decoded::LoadStoreUnscaled {
                        size,
                        v,
                        opc,
                        imm9,
                        rn,
                        rt,
                    }) = decoded
                    else {
                        return mismatch(format!(
                            "intent {:?} (offset {offset}) but the word does not decode as                              LDUR/STUR unscaled",
                            intent.opcode
                        ));
                    };
                    expect_field!("load/store-unscaled V", v, want_v);
                    expect_field!("load/store-unscaled size", size, want_size);
                    expect_field!("load/store-unscaled opc", opc, want_opc);
                    expect_field!("load/store-unscaled Rt", rt, rt_want);
                    expect_field!("load/store-unscaled Rn", rn, rn_want);
                    expect_field!("load/store-unscaled imm9", i64::from(imm9), offset);
                    DecodeCheckOutcome::Match
                }
            }

            // ---- Register-move aliases -------------------------------------
            // MOVXrr/MOVWrr/MovR encode as ORR Rd, XZR, Rm — or ADD Rd, Rn, #0
            // when either side is SP (spelled `SpecialReg::SP` or the physical
            // SP/WSP register), because register 31 is XZR in ORR and SP in
            // ADD. Uxtw is the 32-bit register move (ORR Wd, WZR, Wn: writing
            // a W register zero-extends, which IS the uxtw); it has no SP form.
            Op::MOVXrr | Op::MOVWrr | Op::MovR | Op::Uxtw => {
                let names_sp = |index: usize| match intent.operands.get(index) {
                    Some(MachOperand::Special(SpecialReg::SP)) => true,
                    Some(MachOperand::PReg(p)) => {
                        *p == trust_cg_ir::regs::SP || *p == trust_cg_ir::regs::WSP
                    }
                    _ => false,
                };
                let sp_move = intent.opcode != Op::Uxtw && (names_sp(0) || names_sp(1));
                let (Some(rd_want), Some(rm_want)) = (intent_reg(intent, 0), intent_reg(intent, 1))
                else {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice5: non-register move operand",
                    );
                };
                // Typed move opcodes own their architectural width even when
                // the allocated PReg uses the other view. Generic MovR keeps
                // its operand-selected width. Mirroring an operand-derived
                // typed-encoder bug here would falsely accept it.
                let want_sf = match intent.opcode {
                    Op::MOVWrr | Op::Uxtw => 0,
                    Op::MOVXrr => 1,
                    Op::MovR => intent_sf(intent, 0),
                    _ => unreachable!(),
                };
                if sp_move {
                    let Some(A64Decoded::AddSubImm {
                        sf,
                        op,
                        s,
                        sh,
                        imm12,
                        rn,
                        rd,
                    }) = decoded
                    else {
                        return mismatch(format!(
                            "intent {:?} (SP operand) but the word does not decode as ADD Rd, Rn, #0",
                            intent.opcode
                        ));
                    };
                    expect_field!("mov-sp op", op, 0);
                    expect_field!("mov-sp S", s, 0);
                    expect_field!("mov-sp sh", sh, 0);
                    expect_field!("mov-sp imm12", imm12, 0);
                    expect_field!("mov-sp Rn", rn, rm_want);
                    expect_field!("mov-sp sf", sf, want_sf);
                    expect_field!("mov-sp Rd", rd, rd_want);
                    return DecodeCheckOutcome::Match;
                }
                let Some(A64Decoded::LogicalShiftedReg {
                    sf,
                    opc,
                    shift,
                    n,
                    rm,
                    imm6,
                    rn,
                    rd,
                }) = decoded
                else {
                    return mismatch(format!(
                        "intent {:?} but the word does not decode as ORR (register move)",
                        intent.opcode
                    ));
                };
                expect_field!("reg-move opc", opc, 0b01);
                expect_field!("reg-move N", n, 0);
                expect_field!("reg-move shift", shift, 0);
                expect_field!("reg-move imm6", imm6, 0);
                expect_field!("reg-move Rn", rn, 31);
                expect_field!("reg-move sf", sf, want_sf);
                expect_field!("reg-move Rd", rd, rd_want);
                expect_field!("reg-move Rm", rm, rm_want);
                DecodeCheckOutcome::Match
            }

            // ---- Compares: SUBS with Rd == XZR -----------------------------
            Op::CmpRR | Op::CMPWrr | Op::CMPXrr => {
                if intent.operands.len() != 2 {
                    return mismatch("register CMP requires exactly two operands".to_string());
                }
                let (Some((want_sf, rn_want)), Some((rhs_sf, rm_want))) = (
                    intent_cond_select_reg(intent, 0),
                    intent_cond_select_reg(intent, 1),
                ) else {
                    return mismatch(
                        "register CMP operands must be W/X GPRs or ZR, not SP".to_string(),
                    );
                };
                if want_sf != rhs_sf
                    || (intent.opcode == Op::CMPWrr && want_sf != 0)
                    || (intent.opcode == Op::CMPXrr && want_sf != 1)
                {
                    return mismatch(
                        "register CMP operand and typed-opcode widths must agree".to_string(),
                    );
                }
                let Some(A64Decoded::AddSubShiftedReg {
                    sf,
                    op,
                    s,
                    shift,
                    rm,
                    imm6,
                    rn,
                    rd,
                }) = decoded
                else {
                    return mismatch(
                        "intent CmpRR but the word does not decode as SUBS shifted-reg".to_string(),
                    );
                };
                expect_field!("cmp-rr op", op, 1);
                expect_field!("cmp-rr S", s, 1);
                expect_field!("cmp-rr Rd", rd, 31);
                expect_field!("cmp-rr shift", shift, 0);
                expect_field!("cmp-rr imm6", imm6, 0);
                expect_field!("cmp-rr sf", sf, want_sf);
                expect_field!("cmp-rr Rn", rn, rn_want);
                expect_field!("cmp-rr Rm", rm, rm_want);
                DecodeCheckOutcome::Match
            }

            Op::CmpRI | Op::CMPWri | Op::CMPXri => {
                if intent.operands.len() != 2 {
                    return mismatch("immediate CMP requires exactly two operands".to_string());
                }
                let Some((want_sf, rn_want)) = intent_cmp_immediate_base(intent) else {
                    return mismatch(
                        "immediate CMP base must be a W/X GPR or SP, not ZR".to_string(),
                    );
                };
                if (intent.opcode == Op::CMPWri && want_sf != 0)
                    || (intent.opcode == Op::CMPXri && want_sf != 1)
                {
                    return mismatch(
                        "immediate CMP operand and typed-opcode widths must agree".to_string(),
                    );
                }
                let Some(imm_want @ 0..=4095) = intent_imm(intent, 1) else {
                    return mismatch("CMP immediate must be an integer in 0..=4095".to_string());
                };
                let Some(A64Decoded::AddSubImm {
                    sf,
                    op,
                    s,
                    sh,
                    imm12,
                    rn,
                    rd,
                }) = decoded
                else {
                    return mismatch(
                        "intent CmpRI but the word does not decode as SUBS immediate".to_string(),
                    );
                };
                expect_field!("cmp-ri op", op, 1);
                expect_field!("cmp-ri S", s, 1);
                expect_field!("cmp-ri Rd", rd, 31);
                expect_field!("cmp-ri sh", sh, 0);
                expect_field!("cmp-ri sf", sf, want_sf);
                expect_field!("cmp-ri Rn", rn, rn_want);
                expect_field!("cmp-ri imm12", i64::from(imm12), imm_want);
                DecodeCheckOutcome::Match
            }

            // ---- Conditional select family ---------------------------------
            // CSet Rd, cond == CSINC Rd, XZR, XZR, invert(cond).
            Op::CSet | Op::Csel | Op::Csinc | Op::Csinv | Op::Csneg => {
                match trust_cg_verify::aarch64_csel_semantics::bind_conditional_select_word(
                    intent, w,
                ) {
                    Ok(_) => DecodeCheckOutcome::Match,
                    Err(error) => mismatch(error.to_string()),
                }
            }

            Op::FcselRR => {
                if intent.operands.len() != 4 {
                    return mismatch("FCSEL requires exactly four operands".to_string());
                }
                let (
                    Some((want_type, want_rd)),
                    Some((rn_type, want_rn)),
                    Some((rm_type, want_rm)),
                ) = (
                    intent_fp_cond_select_reg(intent, 0),
                    intent_fp_cond_select_reg(intent, 1),
                    intent_fp_cond_select_reg(intent, 2),
                )
                else {
                    return mismatch("FCSEL requires three S/D physical registers".to_string());
                };
                if want_type != rn_type || want_type != rm_type {
                    return mismatch("FCSEL requires equal-width S/D operands".to_string());
                }
                let Some(want_cond @ 0..=15) = intent_imm(intent, 3) else {
                    return mismatch("FCSEL condition must be an immediate in 0..=15".to_string());
                };
                let Some(A64Decoded::FpCondSelect {
                    ftype,
                    rm,
                    cond,
                    rn,
                    rd,
                }) = decoded
                else {
                    return mismatch(
                        "intent FCSEL but the word is not scalar S/D conditional select"
                            .to_string(),
                    );
                };
                expect_field!("fcsel ftype", ftype, want_type);
                expect_field!("fcsel Rd", rd, want_rd);
                expect_field!("fcsel Rn", rn, want_rn);
                expect_field!("fcsel Rm", rm, want_rm);
                expect_field!("fcsel cond", i64::from(cond), want_cond);
                DecodeCheckOutcome::Match
            }

            // ---- FCMP (floating-point compare) -----------------------------
            // An S/D compare is decoded by
            // `aarch64_flag_consumer_proofs::decode_fp_compare`, the same
            // independent decoder the FCMP packed-NZCV obligation is built
            // from, so every emitted S/D FCMP word is the register-register,
            // non-signaling compare the obligation models. The half-precision
            // (FEAT_FP16) compare an F16 `fcmp` lowers to is decoded field by
            // field by the FP/SIMD slice; the obligation does not model it.
            Op::Fcmp => {
                if intent.operands.len() != 2 {
                    return mismatch("FCMP requires exactly two operands".to_string());
                }
                let (Some((want_type, want_rn)), Some((rm_type, want_rm))) = (
                    intent_fp_cond_select_reg(intent, 0),
                    intent_fp_cond_select_reg(intent, 1),
                ) else {
                    // The encoder takes the compare width from operand 0 and
                    // treats any non-S/H register class as D, so a GPR,
                    // special or immediate operand would still encode. Such an
                    // intent is malformed. Q/V operands are not a scalar
                    // compare: counted, not verified (and refused on
                    // proof-grade routes).
                    let bank = |index: usize| match intent.operands.get(index) {
                        Some(MachOperand::PReg(p)) => match p.encoding() {
                            64..=95 => Some('V'),
                            96..=159 => Some('F'),
                            165..=196 => Some('H'),
                            _ => None,
                        },
                        _ => None,
                    };
                    return match (bank(0), bank(1)) {
                        (Some('H'), Some('H')) if hole.is_some() => {
                            mismatch("FCMP cannot contain a relocation hole".to_string())
                        }
                        (Some('H'), Some('H')) => {
                            match super::decode_check_fp_simd::check_fcmp_half(intent, w) {
                                Ok(()) => DecodeCheckOutcome::Match,
                                Err(detail) => mismatch(format!("Fcmp {w:#010x}: {detail}")),
                            }
                        }
                        (Some('H'), Some('F')) | (Some('F'), Some('H')) => {
                            mismatch("FCMP requires equal-width H/S/D operands".to_string())
                        }
                        (Some(_), Some(_)) => DecodeCheckOutcome::Allowlisted(
                            "a64-fcmp: operand outside the scalar H/S/D register banks",
                        ),
                        _ => mismatch(
                            "FCMP requires two floating-point register operands".to_string(),
                        ),
                    };
                };
                if want_type != rm_type {
                    return mismatch("FCMP requires equal-width S/D operands".to_string());
                }
                let decoded = match flag_proofs::decode_fp_compare(w) {
                    Ok(decoded) => decoded,
                    Err(error) => return mismatch(format!("intent FCMP but {error}")),
                };
                if decoded.against_zero || decoded.signaling {
                    return mismatch(format!(
                        "intent register FCMP but the word is {}",
                        if decoded.signaling {
                            "FCMPE"
                        } else {
                            "FCMP #0.0"
                        }
                    ));
                }
                expect_field!(
                    "fcmp width",
                    i64::from(decoded.width),
                    if want_type == 0 { 32 } else { 64 }
                );
                expect_field!("fcmp Rn", u32::from(decoded.rn), want_rn);
                expect_field!("fcmp Rm", u32::from(decoded.rm), want_rm);
                DecodeCheckOutcome::Match
            }

            // ---- B.cond ----------------------------------------------------
            Op::BCond | Op::Bcc => {
                let Some(A64Decoded::CondBranch { cond, imm19 }) = decoded else {
                    return mismatch(
                        "intent BCond but the word does not decode as B.cond".to_string(),
                    );
                };
                let Some(c) = intent_imm(intent, 0) else {
                    return DecodeCheckOutcome::Allowlisted("a64-slice5: non-imm BCond cond");
                };
                expect_field!("bcond cond", i64::from(cond), c & 0xF);
                if hole.is_some() {
                    return DecodeCheckOutcome::Match;
                }
                match intent_imm(intent, 1) {
                    Some(off) => {
                        expect_field!("bcond imm19", i64::from(imm19), off & 0x7FFFF);
                        DecodeCheckOutcome::Match
                    }
                    None => DecodeCheckOutcome::Allowlisted("a64-slice5: unresolved BCond target"),
                }
            }

            // ---- MUL / division -------------------------------------------
            // MulRR == MADD Rd, Rn, Rm, XZR.
            Op::MulRR => {
                let Some(A64Decoded::DataProc3Src {
                    sf,
                    op54,
                    op31,
                    rm,
                    o0,
                    ra,
                    rn,
                    rd,
                }) = decoded
                else {
                    return mismatch(
                        "intent MulRR but the word does not decode as MADD".to_string(),
                    );
                };
                expect_field!("mul op54", op54, 0);
                expect_field!("mul op31", op31, 0);
                expect_field!("mul o0", o0, 0);
                expect_field!("mul Ra", ra, 31);
                expect_field!("mul sf", sf, intent_sf(intent, 0));
                let (Some(rd_want), Some(rn_want), Some(rm_want)) = (
                    intent_reg(intent, 0),
                    intent_reg(intent, 1),
                    intent_reg(intent, 2),
                ) else {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice5: non-register MulRR operand",
                    );
                };
                expect_field!("mul Rd", rd, rd_want);
                expect_field!("mul Rn", rn, rn_want);
                expect_field!("mul Rm", rm, rm_want);
                DecodeCheckOutcome::Match
            }

            Op::Madd | Op::Msub => {
                let Some(A64Decoded::DataProc3Src {
                    sf,
                    op54,
                    op31,
                    rm,
                    o0,
                    ra,
                    rn,
                    rd,
                }) = decoded
                else {
                    return mismatch(format!(
                        "intent {:?} but the word does not decode as MADD/MSUB",
                        intent.opcode
                    ));
                };
                expect_field!("madd op54", op54, 0);
                expect_field!("madd op31", op31, 0);
                expect_field!("madd o0", o0, u32::from(matches!(intent.opcode, Op::Msub)));
                expect_field!("madd sf", sf, intent_sf(intent, 0));
                let (Some(rd_want), Some(rn_want), Some(rm_want), Some(ra_want)) = (
                    intent_reg(intent, 0),
                    intent_reg(intent, 1),
                    intent_reg(intent, 2),
                    intent_reg(intent, 3),
                ) else {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice7: non-register madd/msub operand",
                    );
                };
                expect_field!("madd Rd", rd, rd_want);
                expect_field!("madd Rn", rn, rn_want);
                expect_field!("madd Rm", rm, rm_want);
                expect_field!("madd Ra", ra, ra_want);
                DecodeCheckOutcome::Match
            }

            // Variable shifts: data-processing 2-source LSLV/LSRV/ASRV/RORV.
            Op::LslRR | Op::LsrRR | Op::AsrRR => {
                let Some(A64Decoded::DataProc2Src {
                    sf,
                    rm,
                    opcode,
                    rn,
                    rd,
                }) = decoded
                else {
                    return mismatch(format!(
                        "intent {:?} but the word does not decode as a variable shift",
                        intent.opcode
                    ));
                };
                let want_opcode = match intent.opcode {
                    Op::LslRR => 0b001000,
                    Op::LsrRR => 0b001001,
                    Op::AsrRR => 0b001010,
                    _ => unreachable!(),
                };
                expect_field!("shift-var opcode", opcode, want_opcode);
                expect_field!("shift-var sf", sf, intent_sf(intent, 0));
                let (Some(rd_want), Some(rn_want), Some(rm_want)) = (
                    intent_reg(intent, 0),
                    intent_reg(intent, 1),
                    intent_reg(intent, 2),
                ) else {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice7: non-register variable-shift operand",
                    );
                };
                expect_field!("shift-var Rd", rd, rd_want);
                expect_field!("shift-var Rn", rn, rn_want);
                expect_field!("shift-var Rm", rm, rm_want);
                DecodeCheckOutcome::Match
            }

            // ORN Rd, Rn, Rm: logical shifted-reg opc=01, N=1.
            Op::OrnRR => {
                let Some(A64Decoded::LogicalShiftedReg {
                    sf,
                    opc,
                    shift,
                    n,
                    rm,
                    imm6,
                    rn,
                    rd,
                }) = decoded
                else {
                    return mismatch(
                        "intent OrnRR but the word does not decode as logical shifted-reg"
                            .to_string(),
                    );
                };
                expect_field!("orn opc", opc, 0b01);
                expect_field!("orn N", n, 1);
                expect_field!("orn shift", shift, 0);
                expect_field!("orn imm6", imm6, 0);
                expect_field!("orn sf", sf, intent_sf(intent, 0));
                let (Some(rd_want), Some(rn_want), Some(rm_want)) = (
                    intent_reg(intent, 0),
                    intent_reg(intent, 1),
                    intent_reg(intent, 2),
                ) else {
                    return DecodeCheckOutcome::Allowlisted("a64-slice7: non-register ORN operand");
                };
                expect_field!("orn Rd", rd, rd_want);
                expect_field!("orn Rn", rn, rn_want);
                expect_field!("orn Rm", rm, rm_want);
                DecodeCheckOutcome::Match
            }

            Op::SDiv | Op::UDiv => {
                let Some(A64Decoded::DataProc2Src {
                    sf,
                    rm,
                    opcode,
                    rn,
                    rd,
                }) = decoded
                else {
                    return mismatch(format!(
                        "intent {:?} but the word does not decode as data-processing 2-source",
                        intent.opcode
                    ));
                };
                let want_opcode = if matches!(intent.opcode, Op::SDiv) {
                    0b000011
                } else {
                    0b000010
                };
                expect_field!("div opcode", opcode, want_opcode);
                expect_field!("div sf", sf, intent_sf(intent, 0));
                let (Some(rd_want), Some(rn_want), Some(rm_want)) = (
                    intent_reg(intent, 0),
                    intent_reg(intent, 1),
                    intent_reg(intent, 2),
                ) else {
                    return DecodeCheckOutcome::Allowlisted("a64-slice5: non-register div operand");
                };
                expect_field!("div Rd", rd, rd_want);
                expect_field!("div Rn", rn, rn_want);
                expect_field!("div Rm", rm, rm_want);
                DecodeCheckOutcome::Match
            }

            // FEAT_CRC32 (Arm ARM C6.2, CRC32/CRC32C): data-processing
            // 2-source with opcode = 010 C sz, where C selects the Castagnoli
            // polynomial and sz the data width (B=00, H=01, W=10, X=11); sf is
            // 1 exactly for the X forms. Register 31 is ZR in every field, so
            // an intent naming SP (or a non-GPR) is not this word. Written from
            // the encoding class, not from the encoder's field table.
            Op::Crc32B
            | Op::Crc32H
            | Op::Crc32W
            | Op::Crc32X
            | Op::Crc32Cb
            | Op::Crc32Ch
            | Op::Crc32Cw
            | Op::Crc32Cx => {
                let Some(A64Decoded::DataProc2Src {
                    sf,
                    rm,
                    opcode,
                    rn,
                    rd,
                }) = decoded
                else {
                    return mismatch(format!(
                        "intent {:?} but the word does not decode as data-processing 2-source",
                        intent.opcode
                    ));
                };
                let (want_opcode, want_sf) = match intent.opcode {
                    Op::Crc32B => (0b010_0_00, 0),
                    Op::Crc32H => (0b010_0_01, 0),
                    Op::Crc32W => (0b010_0_10, 0),
                    Op::Crc32X => (0b010_0_11, 1),
                    Op::Crc32Cb => (0b010_1_00, 0),
                    Op::Crc32Ch => (0b010_1_01, 0),
                    Op::Crc32Cw => (0b010_1_10, 0),
                    _ => (0b010_1_11, 1),
                };
                expect_field!("crc32 opcode", opcode, want_opcode);
                expect_field!("crc32 sf", sf, want_sf);
                if intent.operands.len() != 3 {
                    return mismatch(format!(
                        "intent {:?} has {} operands, CRC32 has three",
                        intent.opcode,
                        intent.operands.len()
                    ));
                }
                // SP is PReg 31 and WSP PReg 63; XZR/WZR (160/161) are GPR views.
                let gpr_or_zr = |index: usize| match intent.operands.get(index) {
                    Some(MachOperand::PReg(p)) => {
                        matches!(preg_class(*p), RegClass::Gpr32 | RegClass::Gpr64)
                            && !matches!(p.encoding(), 31 | 63)
                    }
                    Some(MachOperand::Special(SpecialReg::XZR | SpecialReg::WZR)) => true,
                    _ => false,
                };
                if let Some(index) = (0..3).find(|&index| !gpr_or_zr(index)) {
                    return mismatch(format!(
                        "intent {:?} operand {index} {:?} is not a GPR or ZR (register 31 is \
                         ZR in CRC32)",
                        intent.opcode, intent.operands[index]
                    ));
                }
                let (Some(rd_want), Some(rn_want), Some(rm_want)) = (
                    intent_reg(intent, 0),
                    intent_reg(intent, 1),
                    intent_reg(intent, 2),
                ) else {
                    return mismatch(format!(
                        "intent {:?} names a non-register operand",
                        intent.opcode
                    ));
                };
                expect_field!("crc32 Rd", rd, rd_want);
                expect_field!("crc32 Rn", rn, rn_want);
                expect_field!("crc32 Rm", rm, rm_want);
                DecodeCheckOutcome::Match
            }

            // ---- Bitfield extend aliases -----------------------------------
            // Sxtb/Sxth/Sxtw = SBFM sf=1,N=1,immr=0,imms=7/15/31;
            // Uxtb/Uxth     = UBFM sf=0,N=0,immr=0,imms=7/15.
            Op::Sxtb | Op::Sxth | Op::Sxtw | Op::Uxtb | Op::Uxth => {
                let Some(A64Decoded::Bitfield {
                    sf,
                    opc,
                    n,
                    immr,
                    imms,
                    rn,
                    rd,
                }) = decoded
                else {
                    return mismatch(format!(
                        "intent {:?} but the word does not decode as a bitfield op",
                        intent.opcode
                    ));
                };
                let signed = matches!(intent.opcode, Op::Sxtb | Op::Sxth | Op::Sxtw);
                let (want_sf, want_opc, want_n) = if signed { (1, 0b00, 1) } else { (0, 0b10, 0) };
                let want_imms = match intent.opcode {
                    Op::Sxtb | Op::Uxtb => 7,
                    Op::Sxth | Op::Uxth => 15,
                    Op::Sxtw => 31,
                    _ => unreachable!(),
                };
                expect_field!("extend sf", sf, want_sf);
                expect_field!("extend opc", opc, want_opc);
                expect_field!("extend N", n, want_n);
                expect_field!("extend immr", immr, 0);
                expect_field!("extend imms", imms, want_imms);
                let (Some(rd_want), Some(rn_want)) = (intent_reg(intent, 0), intent_reg(intent, 1))
                else {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice6: non-register extend operand",
                    );
                };
                expect_field!("extend Rd", rd, rd_want);
                expect_field!("extend Rn", rn, rn_want);
                DecodeCheckOutcome::Match
            }

            // ---- General bitfield moves ----------------------------------
            // Exact UBFM/SBFM/BFM field ownership. In particular, LsrAndUbfx
            // synthesizes UBFM and therefore may not sit on the generic
            // decode-check allowlist.
            Op::Ubfm | Op::Sbfm | Op::Bfm => {
                let Some(A64Decoded::Bitfield {
                    sf,
                    opc,
                    n,
                    immr,
                    imms,
                    rn,
                    rd,
                }) = decoded
                else {
                    return mismatch(format!(
                        "intent {:?} but the word does not decode as a bitfield op",
                        intent.opcode
                    ));
                };
                let want_opc = match intent.opcode {
                    Op::Sbfm => 0b00,
                    Op::Bfm => 0b01,
                    Op::Ubfm => 0b10,
                    _ => unreachable!(),
                };
                let want_sf = intent_sf(intent, 0);
                let (Some(rd_want), Some(rn_want)) = (intent_reg(intent, 0), intent_reg(intent, 1))
                else {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice6: non-register bitfield operand",
                    );
                };
                let (Some(immr_want), Some(imms_want)) =
                    (intent_imm(intent, 2), intent_imm(intent, 3))
                else {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice6: non-immediate bitfield control",
                    );
                };
                expect_field!("bitfield sf", sf, want_sf);
                expect_field!("bitfield opc", opc, want_opc);
                expect_field!("bitfield N", n, want_sf);
                expect_field!("bitfield immr", i64::from(immr), immr_want);
                expect_field!("bitfield imms", i64::from(imms), imms_want);
                expect_field!("bitfield Rd", rd, rd_want);
                expect_field!("bitfield Rn", rn, rn_want);
                DecodeCheckOutcome::Match
            }

            // ---- Shift-by-immediate aliases --------------------------------
            // LSL #s = UBFM N=sf, immr=(regsize-s) mod regsize, imms=regsize-1-s
            //   (s == 0 emits the ORR register-move alias instead);
            // LSR #s = UBFM immr=s, imms=regsize-1;
            // ASR #s = SBFM immr=s, imms=regsize-1.
            Op::LslRI | Op::LsrRI | Op::AsrRI => {
                let sf_i = intent_sf(intent, 0);
                let regsize: i64 = if sf_i == 1 { 64 } else { 32 };
                // The encoder refuses a missing or non-immediate amount; such
                // an intent has no word to match.
                let Some(shift) = intent_imm(intent, 2) else {
                    return mismatch(format!(
                        "intent {:?} has no immediate shift amount",
                        intent.opcode
                    ));
                };
                if !(0..regsize).contains(&shift) {
                    return mismatch(format!(
                        "intent {:?} shift {shift} is outside 0..{regsize}",
                        intent.opcode
                    ));
                }
                let (Some(rd_want), Some(rn_want)) = (intent_reg(intent, 0), intent_reg(intent, 1))
                else {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice6: non-register shift operand",
                    );
                };
                if shift == 0 {
                    // Every shift-by-#0 emits the ORR register-move alias
                    // (the #447 zero-shift normalization).
                    let Some(A64Decoded::LogicalShiftedReg {
                        sf,
                        opc,
                        shift: sh,
                        n,
                        rm,
                        imm6,
                        rn,
                        rd,
                    }) = decoded
                    else {
                        return mismatch(format!(
                            "intent {:?} #0 but the word is not the ORR move alias",
                            intent.opcode
                        ));
                    };
                    expect_field!("lsl0-move opc", opc, 0b01);
                    expect_field!("lsl0-move N", n, 0);
                    expect_field!("lsl0-move shift", sh, 0);
                    expect_field!("lsl0-move imm6", imm6, 0);
                    expect_field!("lsl0-move Rn", rn, 31);
                    expect_field!("lsl0-move sf", sf, sf_i);
                    expect_field!("lsl0-move Rd", rd, rd_want);
                    expect_field!("lsl0-move Rm", rm, rn_want);
                    return DecodeCheckOutcome::Match;
                }
                let Some(A64Decoded::Bitfield {
                    sf,
                    opc,
                    n,
                    immr,
                    imms,
                    rn,
                    rd,
                }) = decoded
                else {
                    return mismatch(format!(
                        "intent {:?} but the word does not decode as a bitfield op",
                        intent.opcode
                    ));
                };
                let want_opc = if matches!(intent.opcode, Op::AsrRI) {
                    0b00
                } else {
                    0b10
                };
                let (want_immr, want_imms) = match intent.opcode {
                    Op::LslRI => (
                        ((regsize - shift) & (regsize - 1)) as u32,
                        (regsize - 1 - shift) as u32,
                    ),
                    Op::LsrRI | Op::AsrRI => (shift as u32, (regsize - 1) as u32),
                    _ => unreachable!(),
                };
                expect_field!("shift-imm opc", opc, want_opc);
                expect_field!("shift-imm N", n, sf_i);
                expect_field!("shift-imm sf", sf, sf_i);
                expect_field!("shift-imm immr", immr, want_immr);
                expect_field!("shift-imm imms", imms, want_imms);
                expect_field!("shift-imm Rd", rd, rd_want);
                expect_field!("shift-imm Rn", rn, rn_want);
                DecodeCheckOutcome::Match
            }

            // ---- Baseline LL/SC load/store exclusive ----------------------
            Op::Ldxr
            | Op::Ldxrb
            | Op::Ldxrh
            | Op::Ldaxr
            | Op::Ldaxrb
            | Op::Ldaxrh
            | Op::Stxr
            | Op::Stxrb
            | Op::Stxrh
            | Op::Stlxr
            | Op::Stlxrb
            | Op::Stlxrh => {
                let Some(A64Decoded::LoadStoreExclusive {
                    size,
                    load,
                    o0,
                    rs,
                    rn,
                    rt,
                }) = decoded
                else {
                    return mismatch(format!(
                        "intent {:?} but the word does not decode as load/store exclusive",
                        intent.opcode
                    ));
                };
                let store = matches!(
                    intent.opcode,
                    Op::Stxr | Op::Stxrb | Op::Stxrh | Op::Stlxr | Op::Stlxrb | Op::Stlxrh
                );
                let ordered = matches!(
                    intent.opcode,
                    Op::Ldaxr | Op::Ldaxrb | Op::Ldaxrh | Op::Stlxr | Op::Stlxrb | Op::Stlxrh
                );
                let data_index = usize::from(store);
                let want_size = match intent.opcode {
                    Op::Ldxrb | Op::Ldaxrb | Op::Stxrb | Op::Stlxrb => 0b00,
                    Op::Ldxrh | Op::Ldaxrh | Op::Stxrh | Op::Stlxrh => 0b01,
                    _ if intent_sf(intent, data_index) == 1 => 0b11,
                    _ => 0b10,
                };
                let (Some(rt_want), Some(rn_want)) = (
                    intent_reg(intent, data_index),
                    intent_reg(intent, data_index + 1),
                ) else {
                    return mismatch(format!(
                        "intent {:?} lacks register data/address operands",
                        intent.opcode
                    ));
                };
                let rs_want = if store {
                    let Some(status) = intent_reg(intent, 0) else {
                        return mismatch("store-exclusive intent lacks a status register".into());
                    };
                    status
                } else {
                    0b11111
                };
                expect_field!("exclusive L", load, !store);
                expect_field!("exclusive o0", o0, u32::from(ordered));
                expect_field!("exclusive size", size, want_size);
                expect_field!("exclusive Rs", rs, rs_want);
                expect_field!("exclusive Rn", rn, rn_want);
                expect_field!("exclusive Rt", rt, rt_want);
                if store && (rs == rt || (rs == rn && rn != 31)) {
                    return mismatch(format!(
                        "store-exclusive status {rs} aliases data {rt} or base {rn} \
                         (constrained unpredictable)"
                    ));
                }
                DecodeCheckOutcome::Match
            }

            // ---- 128-bit pair exclusives (64-bit X pairs only) -------------
            Op::Ldxp | Op::Ldaxp | Op::Stxp | Op::Stlxp => {
                let Some(A64Decoded::LoadStoreExclusivePair {
                    sz,
                    load,
                    o0,
                    rs,
                    rt2,
                    rn,
                    rt,
                }) = decoded
                else {
                    return mismatch(format!(
                        "intent {:?} but the word does not decode as a load/store exclusive pair",
                        intent.opcode
                    ));
                };
                let store = matches!(intent.opcode, Op::Stxp | Op::Stlxp);
                let ordered = matches!(intent.opcode, Op::Ldaxp | Op::Stlxp);
                let first = usize::from(store);
                let (Some(rt_want), Some(rt2_want), Some(rn_want)) = (
                    intent_reg(intent, first),
                    intent_reg(intent, first + 1),
                    intent_reg(intent, first + 2),
                ) else {
                    return mismatch(format!(
                        "intent {:?} lacks register data/address operands",
                        intent.opcode
                    ));
                };
                let rs_want = if store {
                    let Some(status) = intent_reg(intent, 0) else {
                        return mismatch(
                            "store-exclusive pair intent lacks a status register".into(),
                        );
                    };
                    status
                } else {
                    0b11111
                };
                expect_field!("exclusive pair sz", sz, 1);
                expect_field!("exclusive pair L", load, !store);
                expect_field!("exclusive pair o0", o0, u32::from(ordered));
                expect_field!("exclusive pair Rs", rs, rs_want);
                expect_field!("exclusive pair Rt", rt, rt_want);
                expect_field!("exclusive pair Rt2", rt2, rt2_want);
                expect_field!("exclusive pair Rn", rn, rn_want);
                if load && rt == rt2 {
                    return mismatch(format!(
                        "load-exclusive pair names Rt {rt} twice (constrained unpredictable)"
                    ));
                }
                if store && (rs == rt || rs == rt2 || (rs == rn && rn != 31)) {
                    return mismatch(format!(
                        "store-exclusive pair status {rs} aliases data {rt}/{rt2} or base {rn} \
                         (constrained unpredictable)"
                    ));
                }
                DecodeCheckOutcome::Match
            }

            Op::Clrex => match decoded {
                Some(A64Decoded::ClearExclusive { crm: 0b1111 }) => DecodeCheckOutcome::Match,
                _ => mismatch(format!(
                    "intent CLREX requires the word 0xD5033F5F, decoded {w:#010X}"
                )),
            },

            // ---- Alignment padding: the word must BE the architectural ----
            // ---- NOP (0xD503201F), byte-exact — no fields, no slack.   ----
            Op::AlignNop => {
                if w == 0xD503_201F {
                    DecodeCheckOutcome::Match
                } else {
                    mismatch(format!(
                        "intent AlignNop requires the architectural NOP 0xD503201F, decoded {w:#010X}"
                    ))
                }
            }

            // ---- ELF TLS descriptor (TLSDESC) slots ------------------------
            // A static linker relaxing the sequence rewrites these slots in
            // place with FIXED registers, so besides agreeing with the intent
            // the words must name the ABI registers (x0 descriptor/result, x1
            // resolver) and carry zero relocation placeholders.
            Op::LdrTlsdesc => {
                let Some(A64Decoded::LoadStoreUi {
                    size,
                    v,
                    opc,
                    imm12,
                    rn,
                    rt,
                }) = decoded
                else {
                    return mismatch(
                        "intent LdrTlsdesc but the word does not decode as an unsigned-offset load"
                            .into(),
                    );
                };
                let (Some(rt_want), Some(rn_want)) = (intent_reg(intent, 0), intent_reg(intent, 1))
                else {
                    return mismatch("intent LdrTlsdesc requires register Rt and Rn".into());
                };
                expect_field!("tlsdesc-ldr size", size, 0b11);
                expect_field!("tlsdesc-ldr V", v, 0);
                expect_field!("tlsdesc-ldr opc", opc, 0b01);
                expect_field!("tlsdesc-ldr imm12 placeholder", imm12, 0);
                expect_field!("tlsdesc-ldr Rt", rt, rt_want);
                expect_field!("tlsdesc-ldr Rn", rn, rn_want);
                expect_field!("tlsdesc-ldr ABI Rt", rt, 1);
                expect_field!("tlsdesc-ldr ABI Rn", rn, 0);
                DecodeCheckOutcome::Match
            }
            Op::AddTlsdescLo12 => {
                let Some(A64Decoded::AddSubImm {
                    sf,
                    op,
                    s,
                    sh,
                    imm12,
                    rn,
                    rd,
                }) = decoded
                else {
                    return mismatch(
                        "intent AddTlsdescLo12 but the word does not decode as add/sub-immediate"
                            .into(),
                    );
                };
                let (Some(rd_want), Some(rn_want)) = (intent_reg(intent, 0), intent_reg(intent, 1))
                else {
                    return mismatch("intent AddTlsdescLo12 requires register Rd and Rn".into());
                };
                expect_field!("tlsdesc-add sf", sf, 1);
                expect_field!("tlsdesc-add op", op, 0);
                expect_field!("tlsdesc-add S", s, 0);
                expect_field!("tlsdesc-add sh", sh, 0);
                expect_field!("tlsdesc-add imm12 placeholder", imm12, 0);
                expect_field!("tlsdesc-add Rd", rd, rd_want);
                expect_field!("tlsdesc-add Rn", rn, rn_want);
                expect_field!("tlsdesc-add ABI Rd", rd, 0);
                expect_field!("tlsdesc-add ABI Rn", rn, 0);
                DecodeCheckOutcome::Match
            }
            Op::BlrTlsdesc => {
                let Some(A64Decoded::BranchReg { opc, rn }) = decoded else {
                    return mismatch(
                        "intent BlrTlsdesc but the word does not decode as a register branch"
                            .into(),
                    );
                };
                let Some(rn_want) = intent_reg(intent, 0) else {
                    return mismatch("intent BlrTlsdesc requires a register target".into());
                };
                expect_field!("tlsdesc-call opc (BLR)", opc, 0b0001);
                expect_field!("tlsdesc-call Rn", rn, rn_want);
                expect_field!("tlsdesc-call ABI Rn", rn, 1);
                DecodeCheckOutcome::Match
            }

            // ---- Everything else: named allowlist, shrinks per slice. -----
            _ => DecodeCheckOutcome::Allowlisted(A64_UNDECODED_FAMILY),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aarch64::encode::encode_instruction;
    use trust_cg_ir::regs::PReg;

    /// GPR64 X<hw> — PReg encodings 0..=30 are X0-X30.
    fn preg64(hw: u8) -> MachOperand {
        MachOperand::PReg(PReg::new(hw as u16))
    }

    /// GPR32 W<hw> — PReg encodings 32..=62 are W0-W30.
    fn preg32(hw: u8) -> MachOperand {
        MachOperand::PReg(PReg::new(u16::from(hw) + 32))
    }

    fn imm(v: i64) -> MachOperand {
        MachOperand::Imm(v)
    }

    fn mk(opcode: AArch64Opcode, operands: Vec<MachOperand>) -> MachInst {
        MachInst::new(opcode, operands)
    }

    fn roundtrip(inst: &MachInst) -> DecodeCheckOutcome {
        let w = encode_instruction(inst).expect("encode");
        A64DecodeCheck.check_one(inst, &w.to_le_bytes(), None)
    }

    fn assert_match(inst: MachInst) {
        match roundtrip(&inst) {
            DecodeCheckOutcome::Match => {}
            other => panic!("{:?}: expected Match, got {other:?}", inst.opcode),
        }
    }

    /// The TLSDESC slots are checked against independently written words:
    /// clang `--target=aarch64-linux-gnu -fPIC -O1` emits `f9400001` (LDR x1,
    /// [x0]), `91000000` (ADD x0, x0, #0) and `d63f0020` (BLR x1) for a
    /// general-dynamic access. Any register, width, shift, placeholder or
    /// opcode change must mismatch.
    #[test]
    fn tlsdesc_slots_match_canonical_words_and_reject_mutations() {
        use AArch64Opcode as Op;
        let symbol = MachOperand::Symbol("tv".into());
        let rows = [
            (
                mk(Op::LdrTlsdesc, vec![preg64(1), preg64(0), symbol.clone()]),
                0xf940_0001u32,
            ),
            (
                mk(
                    Op::AddTlsdescLo12,
                    vec![preg64(0), preg64(0), symbol.clone()],
                ),
                0x9100_0000,
            ),
            (
                mk(Op::BlrTlsdesc, vec![preg64(1), symbol.clone()]),
                0xd63f_0020,
            ),
        ];
        for (intent, word) in &rows {
            assert!(
                matches!(
                    A64DecodeCheck.check_one(intent, &word.to_le_bytes(), None),
                    DecodeCheckOutcome::Match
                ),
                "{:?}",
                intent.opcode
            );
            // Every single-bit flip of the canonical word must be caught.
            for bit in 0..32 {
                let mutated = word ^ (1 << bit);
                assert!(
                    matches!(
                        A64DecodeCheck.check_one(intent, &mutated.to_le_bytes(), None),
                        DecodeCheckOutcome::Mismatch(_)
                    ),
                    "{:?}: bit {bit} flip of {word:#010x} must mismatch",
                    intent.opcode
                );
            }
        }
        // An intent naming a non-ABI register is refused even when the word
        // agrees with it: the linker's relaxation assumes x0/x1.
        let off_abi = mk(Op::LdrTlsdesc, vec![preg64(2), preg64(0), symbol]);
        assert!(matches!(
            A64DecodeCheck.check_one(&off_abi, &0xf940_0002u32.to_le_bytes(), None),
            DecodeCheckOutcome::Mismatch(_)
        ));
    }

    // Independent Arm load/store immediate base words: W/X transfer forms,
    // then their byte scales. No encoder or production intent accessor is used
    // to construct the expected words in the following finite matrices.
    fn gpr_memory_rows() -> [(AArch64Opcode, u32, u32, i64, i64); 14] {
        use AArch64Opcode as Op;
        [
            (Op::LdrRI, 0xb940_0000, 0xf940_0000, 4, 8),
            (Op::StrRI, 0xb900_0000, 0xf900_0000, 4, 8),
            (Op::VolatileLdrRI, 0xb940_0000, 0xf940_0000, 4, 8),
            (Op::VolatileStrRI, 0xb900_0000, 0xf900_0000, 4, 8),
            (Op::LdrbRI, 0x3940_0000, 0x3940_0000, 1, 1),
            (Op::StrbRI, 0x3900_0000, 0x3900_0000, 1, 1),
            (Op::LdrhRI, 0x7940_0000, 0x7940_0000, 2, 2),
            (Op::StrhRI, 0x7900_0000, 0x7900_0000, 2, 2),
            (Op::VolatileLdrbRI, 0x3940_0000, 0x3940_0000, 1, 1),
            (Op::VolatileStrbRI, 0x3900_0000, 0x3900_0000, 1, 1),
            (Op::VolatileLdrhRI, 0x7940_0000, 0x7940_0000, 2, 2),
            (Op::VolatileStrhRI, 0x7900_0000, 0x7900_0000, 2, 2),
            (Op::LdrsbRI, 0x39c0_0000, 0x3980_0000, 1, 1),
            (Op::LdrshRI, 0x79c0_0000, 0x7980_0000, 2, 2),
        ]
    }

    fn gpr_memory_word(base: u32, scale: i64, offset: i64, rt: u32, rn: u32) -> u32 {
        if offset >= 0 && offset % scale == 0 && offset / scale <= 4095 {
            base | ((offset / scale) as u32) << 10 | rn << 5 | rt
        } else {
            assert!((-256..=255).contains(&offset));
            (base & !0x0100_0000) | ((offset as u32) & 511) << 12 | rn << 5 | rt
        }
    }

    #[derive(Default)]
    struct MemoryDecodeCensus {
        attempted: usize,
        failed: usize,
        examples: Vec<String>,
    }

    impl MemoryDecodeCensus {
        fn observe(
            &mut self,
            intent: &MachInst,
            bytes: &[u8],
            hole: Option<&FixupHole>,
            valid: bool,
        ) {
            let outcome = A64DecodeCheck.check_one(intent, bytes, hole);
            self.attempted += 1;
            let correct = if valid {
                matches!(outcome, DecodeCheckOutcome::Match)
            } else {
                matches!(outcome, DecodeCheckOutcome::Mismatch(_))
            };
            if !correct {
                self.failed += 1;
                if self.examples.len() < 12 {
                    self.examples.push(format!(
                        "valid={valid}, {intent:?}, bytes={bytes:02x?}, hole={hole:?}: {outcome:?}"
                    ));
                }
            }
        }

        fn finish(self, expected: usize) {
            assert_eq!(self.attempted, expected, "finite control census");
            assert_eq!(
                self.failed,
                0,
                "{} of {} decoder controls failed (first 12):\n{}",
                self.failed,
                self.attempted,
                self.examples.join("\n")
            );
        }
    }

    #[test]
    fn gpr_immediate_memory_valid_alias_address_and_offset_matrix() {
        let mut census = MemoryDecodeCensus::default();
        for (opcode, word_w, word_x, scale_w, scale_x) in gpr_memory_rows() {
            for (wide, base_word, scale) in [(false, word_w, scale_w), (true, word_x, scale_x)] {
                let data = |n| if wide { preg64(n) } else { preg32(n) };
                let zero = if wide {
                    SpecialReg::XZR
                } else {
                    SpecialReg::WZR
                };
                let transfers = [
                    (data(0), 0),
                    (data(15), 15),
                    (data(30), 30),
                    (
                        MachOperand::PReg(PReg::new(if wide { 160 } else { 161 })),
                        31,
                    ),
                    (MachOperand::Special(zero), 31),
                ];
                for (rt, rt_field) in transfers {
                    for (rn, rn_field) in [
                        (preg64(0), 0),
                        (preg64(17), 17),
                        (preg64(31), 31),
                        (MachOperand::Special(SpecialReg::SP), 31),
                    ] {
                        for offset in [-256, -1, 0, 1, 255, scale, 4095 * scale] {
                            let word =
                                gpr_memory_word(base_word, scale, offset, rt_field, rn_field);
                            for operands in [
                                vec![rt.clone(), rn.clone(), imm(offset)],
                                vec![
                                    rt.clone(),
                                    MachOperand::MemOp {
                                        base: PReg::new(rn_field as u16),
                                        offset,
                                    },
                                ],
                            ] {
                                census.observe(
                                    &mk(opcode, operands),
                                    &word.to_le_bytes(),
                                    None,
                                    true,
                                );
                            }
                        }
                        let word = gpr_memory_word(base_word, scale, 0, rt_field, rn_field);
                        census.observe(
                            &mk(opcode, vec![rt.clone(), rn]),
                            &word.to_le_bytes(),
                            None,
                            true,
                        );
                    }
                }
            }
        }
        // Boundary entries intentionally retain duplicate offsets when scale
        // is one; these are exact attempted checks, not unique encodings.
        census.finish(14 * 2 * 5 * 4 * 15);
    }

    #[test]
    fn gpr_immediate_memory_literal_anchors_and_single_bit_mutations() {
        let mut census = MemoryDecodeCensus::default();
        for (opcode, word_w, word_x, scale_w, scale_x) in gpr_memory_rows() {
            for (rt, base_word, scale) in
                [(preg32(2), word_w, scale_w), (preg64(2), word_x, scale_x)]
            {
                // Unsigned imm12=1, Rn=3, Rt=2. Every bit is constrained by
                // the fixed intent, including family/V/opc and address mode.
                let word = base_word | 0x462;
                let intent = mk(opcode, vec![rt, preg64(3), imm(scale)]);
                census.observe(&intent, &word.to_le_bytes(), None, true);
                for bit in 0..32 {
                    census.observe(&intent, &(word ^ (1 << bit)).to_le_bytes(), None, false);
                }
            }
        }
        census.finish(14 * 2 * 33);
    }

    #[test]
    fn gpr_immediate_memory_rejects_matching_low_field_malformed_intents() {
        use trust_cg_ir::VReg;
        let mut census = MemoryDecodeCensus::default();
        for (opcode, word_w, word_x, _, _) in gpr_memory_rows() {
            for (rt, base_word) in [(preg32(5), word_w), (preg64(5), word_x)] {
                // These pairs intentionally agree with the five hardware bits
                // the old permissive accessor erased the register bank into.
                for (encoding, field) in [
                    (33, 1),
                    (63, 31),
                    (160, 31),
                    (161, 31),
                    (65, 1),
                    (97, 1),
                    (129, 1),
                    (166, 1),
                    (198, 1),
                    (162, 0),
                    (512, 0),
                ] {
                    let word = base_word | field << 5 | 5;
                    for address in [
                        vec![rt.clone(), MachOperand::PReg(PReg::new(encoding)), imm(0)],
                        vec![
                            rt.clone(),
                            MachOperand::MemOp {
                                base: PReg::new(encoding),
                                offset: 0,
                            },
                        ],
                    ] {
                        census.observe(&mk(opcode, address), &word.to_le_bytes(), None, false);
                    }
                }
                for (base, field) in [
                    (MachOperand::Special(SpecialReg::XZR), 31),
                    (MachOperand::Special(SpecialReg::WZR), 31),
                    (MachOperand::VReg(VReg::new(0, RegClass::Gpr64)), 0),
                    (imm(0), 0),
                    (MachOperand::Symbol("base".into()), 0),
                ] {
                    let word = base_word | field << 5 | 5;
                    census.observe(
                        &mk(opcode, vec![rt.clone(), base, imm(0)]),
                        &word.to_le_bytes(),
                        None,
                        false,
                    );
                }
                let word = base_word | 5;
                for operands in [
                    vec![],
                    vec![rt.clone()],
                    vec![rt.clone(), preg64(0), MachOperand::FImm(0.0)],
                    vec![
                        rt.clone(),
                        preg64(0),
                        MachOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                    ],
                    vec![rt.clone(), preg64(0), imm(0), imm(0)],
                    vec![
                        rt.clone(),
                        MachOperand::MemOp {
                            base: PReg::new(0),
                            offset: 0,
                        },
                        imm(0),
                    ],
                    vec![
                        rt.clone(),
                        preg64(0),
                        imm(0),
                        MachOperand::MemOp {
                            base: PReg::new(0),
                            offset: 0,
                        },
                    ],
                    vec![rt.clone(), preg64(0), MachOperand::Symbol("offset".into())],
                ] {
                    census.observe(&mk(opcode, operands), &word.to_le_bytes(), None, false);
                }
                for (transfer, field) in [
                    (preg64(31), 31),
                    (preg32(31), 31),
                    (MachOperand::Special(SpecialReg::SP), 31),
                    (MachOperand::PReg(PReg::new(64)), 0),
                    (MachOperand::PReg(PReg::new(96)), 0),
                    (MachOperand::PReg(PReg::new(128)), 0),
                    (MachOperand::PReg(PReg::new(165)), 0),
                    (MachOperand::PReg(PReg::new(197)), 0),
                    (MachOperand::PReg(PReg::new(162)), 0),
                    (MachOperand::PReg(PReg::new(512)), 0),
                    (imm(0), 0),
                    (MachOperand::VReg(VReg::new(0, RegClass::Gpr64)), 0),
                    (MachOperand::Symbol("transfer".into()), 0),
                    (
                        MachOperand::MemOp {
                            base: PReg::new(0),
                            offset: 0,
                        },
                        0,
                    ),
                ] {
                    census.observe(
                        &mk(opcode, vec![transfer, preg64(0), imm(0)]),
                        &(base_word | field).to_le_bytes(),
                        None,
                        false,
                    );
                }
            }
        }
        census.finish(14 * 2 * (22 + 5 + 8 + 14));
    }

    /// The fused `LDR/STR Rt, [Xn, #:lo12:sym]` intent is checked field by
    /// field against the independent base words above with imm12 == 0, and
    /// only with a GlobalRef hole on a non-volatile opcode.
    #[test]
    fn lo12_symbolic_memory_checks_every_field_and_its_hole() {
        use crate::decode_check::FixupHoleKind;
        let hole = |kind| FixupHole {
            offset_in_inst: 0,
            width: 4,
            kind,
        };
        let global = hole(FixupHoleKind::GlobalRef);
        for (opcode, word_w, word_x, _, _) in gpr_memory_rows() {
            let volatile = matches!(
                opcode,
                AArch64Opcode::VolatileLdrRI
                    | AArch64Opcode::VolatileStrRI
                    | AArch64Opcode::VolatileLdrbRI
                    | AArch64Opcode::VolatileStrbRI
                    | AArch64Opcode::VolatileLdrhRI
                    | AArch64Opcode::VolatileStrhRI
            );
            for (rt, base_word) in [(preg32(3), word_w), (preg64(3), word_x)] {
                let intent = mk(
                    opcode,
                    vec![rt, preg64(8), MachOperand::Symbol("sym".into())],
                );
                // Rt = 3, Rn = 8, imm12 = 0.
                let word = base_word | (8 << 5) | 3;
                let outcome = A64DecodeCheck.check_one(&intent, &word.to_le_bytes(), Some(&global));
                if volatile {
                    assert!(
                        matches!(outcome, DecodeCheckOutcome::Mismatch(_)),
                        "{opcode:?}: {outcome:?}"
                    );
                    continue;
                }
                assert!(
                    matches!(outcome, DecodeCheckOutcome::Match),
                    "{opcode:?}: {outcome:?}"
                );
                for wrong in [
                    word | (1 << 10),               // nonzero imm12 placeholder
                    (word & !(31 << 5)) | (9 << 5), // wrong base
                    (word & !31) | 4,               // wrong transfer register
                ] {
                    assert!(
                        matches!(
                            A64DecodeCheck.check_one(&intent, &wrong.to_le_bytes(), Some(&global)),
                            DecodeCheckOutcome::Mismatch(_)
                        ),
                        "{opcode:?} {wrong:#010x}"
                    );
                }
                for bad_hole in [None, Some(hole(FixupHoleKind::ExternRefGot))] {
                    assert!(
                        matches!(
                            A64DecodeCheck.check_one(
                                &intent,
                                &word.to_le_bytes(),
                                bad_hole.as_ref()
                            ),
                            DecodeCheckOutcome::Mismatch(_)
                        ),
                        "{opcode:?} {bad_hole:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn gpr_immediate_memory_rejects_holes_invalid_offsets_and_byte_lengths() {
        use crate::decode_check::FixupHoleKind;
        let mut census = MemoryDecodeCensus::default();
        for (opcode, word_w, word_x, scale_w, scale_x) in gpr_memory_rows() {
            for (rt, word, scale) in [(preg32(0), word_w, scale_w), (preg64(0), word_x, scale_x)] {
                let intent = mk(opcode, vec![rt.clone(), preg64(0), imm(0)]);
                for kind in [
                    FixupHoleKind::Branch,
                    FixupHoleKind::Call,
                    FixupHoleKind::GlobalRef,
                    FixupHoleKind::ExternRefGot,
                    FixupHoleKind::TlsTlv,
                    FixupHoleKind::ConstPool,
                ] {
                    for (offset_in_inst, width) in [(0, 0), (0, 4), (1, 1), (4, 1)] {
                        let hole = FixupHole {
                            offset_in_inst,
                            width,
                            kind,
                        };
                        census.observe(&intent, &word.to_le_bytes(), Some(&hole), false);
                    }
                }
                for offset in [
                    -257,
                    4096 * scale,
                    4096 * scale + 1,
                    i64::MIN,
                    i64::MAX,
                    (1_i64 << 32) * scale,
                    (1_i64 << 32) * scale + scale,
                ] {
                    let malformed = mk(opcode, vec![rt.clone(), preg64(0), imm(offset)]);
                    census.observe(&malformed, &word.to_le_bytes(), None, false);
                }
                for len in [0, 1, 2, 3, 5, 8] {
                    census.observe(&intent, &vec![0; len], None, false);
                }
                // Zero has a canonical unsigned-offset encoding. The otherwise
                // equivalent LDUR/STUR zero spelling is not the selected intent.
                census.observe(&intent, &(word & !0x0100_0000).to_le_bytes(), None, false);
            }
        }
        census.finish(14 * 2 * (24 + 7 + 6 + 1));
    }

    // Arm A64 v2025-03, LDR/STR (immediate), pages 509-511/910-912:
    // pre-index bits11:10=11, post-index=01; signed imm9 is in byte units.
    // These literal bases and the test field construction do not use encoder
    // helpers or production intent accessors.
    fn scalar_writeback_rows() -> [(AArch64Opcode, u32, u32); 4] {
        use AArch64Opcode as Op;
        [
            (Op::LdrPreIndex, 0xb840_0c00, 0xf840_0c00),
            (Op::StrPreIndex, 0xb800_0c00, 0xf800_0c00),
            (Op::LdrPostIndex, 0xb840_0400, 0xf840_0400),
            (Op::StrPostIndex, 0xb800_0400, 0xf800_0400),
        ]
    }

    fn scalar_writeback_word(base: u32, offset: i64, rt: u32, rn: u32) -> u32 {
        assert!((-256..=255).contains(&offset));
        base | (((offset as u32) & 511) << 12) | (rn << 5) | rt
    }

    fn scalar_writeback_transfer(wide: bool, number: u8) -> MachOperand {
        if number == 31 {
            MachOperand::PReg(PReg::new(if wide { 160 } else { 161 }))
        } else if wide {
            preg64(number)
        } else {
            preg32(number)
        }
    }

    #[test]
    fn scalar_writeback_literal_words_and_all_single_bit_mutants() {
        let mut census = MemoryDecodeCensus::default();
        for (opcode, word_w, word_x) in scalar_writeback_rows() {
            for (rt, base) in [(preg32(2), word_w), (preg64(2), word_x)] {
                // Rt=2, Rn=3, signed offset=0. Mode, load/store, width and
                // every other field remain constrained by the fixed intent.
                let word = base | 0x62;
                let intent = mk(opcode, vec![rt, preg64(3), imm(0)]);
                census.observe(&intent, &word.to_le_bytes(), None, true);
                for bit in 0..32 {
                    census.observe(&intent, &(word ^ (1 << bit)).to_le_bytes(), None, false);
                }
            }
        }
        census.finish(4 * 2 * 33);
    }

    #[test]
    fn scalar_writeback_all_register_pairs_boundaries_and_overlap_refusal() {
        let mut census = MemoryDecodeCensus::default();
        for (opcode, word_w, word_x) in scalar_writeback_rows() {
            for (wide, base) in [(false, word_w), (true, word_x)] {
                for rt in 0..32u8 {
                    for rn in 0..32u8 {
                        for offset in [-256, -1, 0, 1, 255] {
                            let intent = mk(
                                opcode,
                                vec![scalar_writeback_transfer(wide, rt), preg64(rn), imm(offset)],
                            );
                            let word =
                                scalar_writeback_word(base, offset, u32::from(rt), u32::from(rn));
                            // Constrained-unpredictable writeback overlap is
                            // refused for Wn/Xn aliases too. Rn31 is SP, not ZR.
                            census.observe(
                                &intent,
                                &word.to_le_bytes(),
                                None,
                                rt != rn || rn == 31,
                            );
                        }
                    }
                }
            }
        }
        // 39,720 accepted controls and 1,240 overlap refusals.
        census.finish(4 * 2 * 32 * 32 * 5);
    }

    #[test]
    fn scalar_writeback_every_signed_offset_and_special_zero_sp_aliases() {
        let mut census = MemoryDecodeCensus::default();
        for (opcode, word_w, word_x) in scalar_writeback_rows() {
            for (wide, base) in [(false, word_w), (true, word_x)] {
                for transfer in [
                    scalar_writeback_transfer(wide, 31),
                    MachOperand::Special(if wide {
                        SpecialReg::XZR
                    } else {
                        SpecialReg::WZR
                    }),
                ] {
                    for address in [preg64(31), MachOperand::Special(SpecialReg::SP)] {
                        for offset in -256..=255 {
                            let intent =
                                mk(opcode, vec![transfer.clone(), address.clone(), imm(offset)]);
                            let word = scalar_writeback_word(base, offset, 31, 31);
                            census.observe(&intent, &word.to_le_bytes(), None, true);
                        }
                    }
                }
            }
        }
        census.finish(4 * 2 * 2 * 2 * 512);
    }

    #[test]
    fn scalar_writeback_malformed_intents_holes_and_byte_lengths_refuse() {
        use crate::decode_check::FixupHoleKind;
        use trust_cg_ir::VReg;
        let mut census = MemoryDecodeCensus::default();
        for (opcode, word_w, word_x) in scalar_writeback_rows() {
            for (wide, base) in [(false, word_w), (true, word_x)] {
                let rt = scalar_writeback_transfer(wide, 2);
                let word = scalar_writeback_word(base, 0, 2, 3);
                let good = mk(opcode, vec![rt.clone(), preg64(3), imm(0)]);
                for (transfer, field) in [
                    (preg64(31), 31),
                    (preg32(31), 31),
                    (MachOperand::Special(SpecialReg::SP), 31),
                    (MachOperand::PReg(PReg::new(64)), 0),
                    (MachOperand::PReg(PReg::new(96)), 0),
                    (MachOperand::PReg(PReg::new(128)), 0),
                    (MachOperand::PReg(PReg::new(165)), 0),
                    (MachOperand::PReg(PReg::new(197)), 0),
                    (MachOperand::PReg(PReg::new(162)), 0),
                    (MachOperand::PReg(PReg::new(163)), 0),
                    (MachOperand::PReg(PReg::new(164)), 0),
                    (MachOperand::PReg(PReg::new(u16::MAX)), 0),
                    (MachOperand::VReg(VReg::new(0, RegClass::Gpr64)), 0),
                    (imm(0), 0),
                    (MachOperand::Symbol("transfer".into()), 0),
                ] {
                    let intent = mk(opcode, vec![transfer, preg64(3), imm(0)]);
                    let spoof = scalar_writeback_word(base, 0, field, 3);
                    census.observe(&intent, &spoof.to_le_bytes(), None, false);
                }
                for (encoding, field) in [
                    (33, 1),
                    (63, 31),
                    (160, 31),
                    (161, 31),
                    (65, 1),
                    (97, 1),
                    (129, 1),
                    (166, 1),
                    (198, 1),
                    (162, 0),
                    (u16::MAX, 0),
                ] {
                    let intent = mk(
                        opcode,
                        vec![rt.clone(), MachOperand::PReg(PReg::new(encoding)), imm(0)],
                    );
                    let spoof = scalar_writeback_word(base, 0, 2, field);
                    census.observe(&intent, &spoof.to_le_bytes(), None, false);
                }
                for (address, field) in [
                    (MachOperand::Special(SpecialReg::XZR), 31),
                    (MachOperand::Special(SpecialReg::WZR), 31),
                    (imm(0), 0),
                    (MachOperand::VReg(VReg::new(0, RegClass::Gpr64)), 0),
                    (MachOperand::Symbol("address".into()), 0),
                ] {
                    let intent = mk(opcode, vec![rt.clone(), address, imm(0)]);
                    let spoof = scalar_writeback_word(base, 0, 2, field);
                    census.observe(&intent, &spoof.to_le_bytes(), None, false);
                }
                for operands in [
                    vec![],
                    vec![rt.clone()],
                    vec![rt.clone(), preg64(3)],
                    vec![rt.clone(), preg64(3), MachOperand::FImm(0.0)],
                    vec![
                        rt.clone(),
                        preg64(3),
                        MachOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                    ],
                    vec![rt.clone(), preg64(3), MachOperand::Symbol("offset".into())],
                    vec![rt.clone(), preg64(3), imm(0), imm(0)],
                    vec![
                        rt.clone(),
                        MachOperand::MemOp {
                            base: PReg::new(3),
                            offset: 0,
                        },
                    ],
                    vec![
                        rt.clone(),
                        MachOperand::MemOp {
                            base: PReg::new(3),
                            offset: 0,
                        },
                        imm(0),
                    ],
                    vec![
                        rt.clone(),
                        preg64(3),
                        MachOperand::MemOp {
                            base: PReg::new(3),
                            offset: 0,
                        },
                    ],
                ] {
                    census.observe(&mk(opcode, operands), &word.to_le_bytes(), None, false);
                }
                for offset in [-257, 256, i64::MIN, i64::MAX, -512, 512, 1_i64 << 32] {
                    census.observe(
                        &mk(opcode, vec![rt.clone(), preg64(3), imm(offset)]),
                        &word.to_le_bytes(),
                        None,
                        false,
                    );
                }
                for kind in [
                    FixupHoleKind::Branch,
                    FixupHoleKind::Call,
                    FixupHoleKind::GlobalRef,
                    FixupHoleKind::ExternRefGot,
                    FixupHoleKind::TlsTlv,
                    FixupHoleKind::ConstPool,
                ] {
                    for (offset_in_inst, width) in [(0, 0), (0, 4), (1, 1), (4, 1)] {
                        let hole = FixupHole {
                            offset_in_inst,
                            width,
                            kind,
                        };
                        census.observe(&good, &word.to_le_bytes(), Some(&hole), false);
                    }
                }
                for len in [0, 1, 2, 3, 5, 8] {
                    census.observe(&good, &vec![0; len], None, false);
                }
            }
        }
        census.finish(4 * 2 * (15 + 11 + 5 + 10 + 7 + 24 + 6));
    }

    // Independent Arm A64 register-offset bases, before Rm/option/S/Rn/Rt.
    // GPR pages513-514/913-914, SIMD&FP pages1624-1626/1978-1980.
    fn register_offset_rows() -> [(AArch64Opcode, u16, u32); 12] {
        use AArch64Opcode as Op;
        [
            (Op::LdrRO, 32, 0xb860_0800),
            (Op::StrRO, 32, 0xb820_0800),
            (Op::LdrRO, 0, 0xf860_0800),
            (Op::StrRO, 0, 0xf820_0800),
            (Op::LdrRO, 165, 0x7c60_0800),
            (Op::StrRO, 165, 0x7c20_0800),
            (Op::LdrRO, 128, 0xbc60_0800),
            (Op::StrRO, 128, 0xbc20_0800),
            (Op::LdrRO, 96, 0xfc60_0800),
            (Op::StrRO, 96, 0xfc20_0800),
            (Op::LdrRO, 64, 0x3ce0_0800),
            (Op::StrRO, 64, 0x3ca0_0800),
        ]
    }

    fn register_offset_transfer(bank: u16, number: u8) -> MachOperand {
        if bank == 0 || bank == 32 {
            scalar_writeback_transfer(bank == 0, number)
        } else {
            MachOperand::PReg(PReg::new(bank + u16::from(number)))
        }
    }

    fn register_offset_word(base: u32, mode: i64, rt: u32, rn: u32, rm: u32) -> u32 {
        assert!(matches!(mode, 4 | 5 | 6 | 7 | 12 | 13 | 14 | 15));
        base | (rm << 16)
            | (((mode as u32) >> 1) << 13)
            | (((mode as u32) & 1) << 12)
            | (rn << 5)
            | rt
    }

    #[test]
    fn register_offset_literal_modes_and_all_single_bit_mutations() {
        let mut census = MemoryDecodeCensus::default();
        for (opcode, bank, base) in register_offset_rows() {
            for mode in [4, 5, 6, 7, 12, 13, 14, 15] {
                let intent = mk(
                    opcode,
                    vec![
                        register_offset_transfer(bank, 2),
                        preg64(3),
                        preg64(4),
                        imm(mode),
                    ],
                );
                let word = register_offset_word(base, mode, 2, 3, 4);
                census.observe(&intent, &word.to_le_bytes(), None, true);
                for bit in 0..32 {
                    census.observe(&intent, &(word ^ (1 << bit)).to_le_bytes(), None, false);
                }
            }
        }
        census.finish(12 * 8 * 33);
    }

    #[test]
    fn register_offset_all_physical_fields_and_modes_keep_overlap_legal() {
        let mut census = MemoryDecodeCensus::default();
        for (opcode, bank, base) in register_offset_rows() {
            for mode in [4, 5, 6, 7, 12, 13, 14, 15] {
                for rt in 0..32u8 {
                    for rn in 0..32u8 {
                        for rm in 0..32u8 {
                            let intent = mk(
                                opcode,
                                vec![
                                    register_offset_transfer(bank, rt),
                                    preg64(rn),
                                    scalar_writeback_transfer(true, rm),
                                    imm(mode),
                                ],
                            );
                            let word = register_offset_word(
                                base,
                                mode,
                                u32::from(rt),
                                u32::from(rn),
                                u32::from(rm),
                            );
                            census.observe(&intent, &word.to_le_bytes(), None, true);
                        }
                    }
                }
            }
        }
        // No writeback occurs: data/base/index hardware-number overlap is legal.
        census.finish(12 * 8 * 32 * 32 * 32);
    }

    #[test]
    fn register_offset_index_width_default_mode_and_zero_sp_spellings() {
        let mut census = MemoryDecodeCensus::default();
        for (opcode, bank, base) in register_offset_rows() {
            let mut transfers = vec![register_offset_transfer(bank, 31)];
            if bank == 0 || bank == 32 {
                transfers.push(MachOperand::Special(if bank == 0 {
                    SpecialReg::XZR
                } else {
                    SpecialReg::WZR
                }));
            }
            for transfer in transfers {
                for address in [preg64(31), MachOperand::Special(SpecialReg::SP)] {
                    for explicit in [
                        None,
                        Some(4),
                        Some(5),
                        Some(6),
                        Some(7),
                        Some(12),
                        Some(13),
                        Some(14),
                        Some(15),
                    ] {
                        let mode = explicit.unwrap_or(6);
                        for (index, field, needs_low32) in [
                            (preg64(0), 0, false),
                            (preg32(0), 0, true),
                            (preg64(15), 15, false),
                            (preg32(15), 15, true),
                            (preg64(30), 30, false),
                            (preg32(30), 30, true),
                            (MachOperand::PReg(PReg::new(160)), 31, false),
                            (MachOperand::PReg(PReg::new(161)), 31, false),
                            (MachOperand::Special(SpecialReg::XZR), 31, false),
                            (MachOperand::Special(SpecialReg::WZR), 31, false),
                        ] {
                            let mut args = vec![transfer.clone(), address.clone(), index];
                            if let Some(mode) = explicit {
                                args.push(imm(mode));
                            }
                            let valid = !needs_low32 || matches!(mode, 4 | 5 | 12 | 13);
                            let word = register_offset_word(base, mode, 31, 31, field);
                            census.observe(&mk(opcode, args), &word.to_le_bytes(), None, valid);
                        }
                    }
                }
            }
        }
        // Sixteen data spellings, including both zero-register widths and
        // real H/S/D/Q31. 2,400 valid rows, 480 ordinary-W full64 refusals.
        census.finish(16 * 2 * 9 * 10);
    }

    #[test]
    fn register_offset_malformed_banks_modes_and_operand_shapes_refuse() {
        use trust_cg_ir::VReg;
        let mut census = MemoryDecodeCensus::default();
        for (opcode, bank, base) in register_offset_rows() {
            let rt = register_offset_transfer(bank, 2);
            let word = register_offset_word(base, 6, 2, 3, 4);
            for (transfer, field) in [
                (preg64(31), 31),
                (preg32(31), 31),
                (MachOperand::Special(SpecialReg::SP), 31),
                (MachOperand::PReg(PReg::new(162)), 0),
                (MachOperand::PReg(PReg::new(163)), 0),
                (MachOperand::PReg(PReg::new(164)), 0),
                (MachOperand::PReg(PReg::new(197)), 0),
                (MachOperand::PReg(PReg::new(u16::MAX)), 0),
                (MachOperand::VReg(VReg::new(0, RegClass::Gpr64)), 0),
                (imm(0), 0),
                (MachOperand::FImm(0.0), 0),
                (
                    MachOperand::MemOp {
                        base: PReg::new(0),
                        offset: 0,
                    },
                    0,
                ),
            ] {
                let intent = mk(opcode, vec![transfer, preg64(3), preg64(4)]);
                let spoof = register_offset_word(base, 6, field, 3, 4);
                census.observe(&intent, &spoof.to_le_bytes(), None, false);
            }
            for (encoding, field) in [
                (33, 1),
                (63, 31),
                (160, 31),
                (161, 31),
                (65, 1),
                (97, 1),
                (129, 1),
                (166, 1),
                (198, 1),
                (162, 0),
                (u16::MAX, 0),
            ] {
                let intent = mk(
                    opcode,
                    vec![
                        rt.clone(),
                        MachOperand::PReg(PReg::new(encoding)),
                        preg64(4),
                    ],
                );
                let spoof = register_offset_word(base, 6, 2, field, 4);
                census.observe(&intent, &spoof.to_le_bytes(), None, false);
            }
            for (address, field) in [
                (MachOperand::Special(SpecialReg::XZR), 31),
                (MachOperand::Special(SpecialReg::WZR), 31),
                (imm(0), 0),
                (MachOperand::VReg(VReg::new(0, RegClass::Gpr64)), 0),
                (MachOperand::FImm(0.0), 0),
            ] {
                let intent = mk(opcode, vec![rt.clone(), address, preg64(4)]);
                let spoof = register_offset_word(base, 6, 2, field, 4);
                census.observe(&intent, &spoof.to_le_bytes(), None, false);
            }
            for mode in [6, 12] {
                for (index, field) in [
                    (preg64(31), 31),
                    (preg32(31), 31),
                    (MachOperand::PReg(PReg::new(64)), 0),
                    (MachOperand::PReg(PReg::new(96)), 0),
                    (MachOperand::PReg(PReg::new(128)), 0),
                    (MachOperand::PReg(PReg::new(165)), 0),
                    (MachOperand::PReg(PReg::new(197)), 0),
                    (MachOperand::PReg(PReg::new(162)), 0),
                    (MachOperand::PReg(PReg::new(u16::MAX)), 0),
                    (MachOperand::Special(SpecialReg::SP), 31),
                    (imm(0), 0),
                    (MachOperand::VReg(VReg::new(0, RegClass::Gpr64)), 0),
                    (MachOperand::FImm(0.0), 0),
                ] {
                    let intent = mk(opcode, vec![rt.clone(), preg64(3), index, imm(mode)]);
                    let spoof = register_offset_word(base, mode, 2, 3, field);
                    census.observe(&intent, &spoof.to_le_bytes(), None, false);
                }
            }
            for args in [
                vec![],
                vec![rt.clone()],
                vec![rt.clone(), preg64(3)],
                vec![rt.clone(), preg64(3), preg64(4), imm(6), imm(0)],
                vec![
                    rt.clone(),
                    MachOperand::MemOp {
                        base: PReg::new(3),
                        offset: 0,
                    },
                    preg64(4),
                ],
                vec![rt.clone(), preg64(3), preg64(4), MachOperand::FImm(0.0)],
                vec![
                    rt.clone(),
                    preg64(3),
                    preg64(4),
                    MachOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                ],
                vec![
                    rt.clone(),
                    preg64(3),
                    preg64(4),
                    MachOperand::Symbol("mode".into()),
                ],
                vec![
                    rt.clone(),
                    preg64(3),
                    MachOperand::MemOp {
                        base: PReg::new(4),
                        offset: 0,
                    },
                ],
                vec![rt.clone(), preg64(3), imm(0)],
            ] {
                census.observe(&mk(opcode, args), &word.to_le_bytes(), None, false);
            }
            for mode in [
                -1,
                i64::MIN,
                i64::MAX,
                0,
                1,
                2,
                3,
                8,
                9,
                10,
                11,
                16,
                20,
                (1_i64 << 32) | 6,
                (1_i64 << 32) | 12,
            ] {
                let intent = mk(opcode, vec![rt.clone(), preg64(3), preg64(4), imm(mode)]);
                census.observe(&intent, &word.to_le_bytes(), None, false);
            }
        }
        census.finish(12 * (12 + 11 + 5 + 26 + 10 + 15));
    }

    #[test]
    fn register_offset_all_modes_refuse_holes_and_bad_byte_lengths() {
        use crate::decode_check::FixupHoleKind;
        let mut census = MemoryDecodeCensus::default();
        for (opcode, bank, base) in register_offset_rows() {
            for mode in [4, 5, 6, 7, 12, 13, 14, 15] {
                let intent = mk(
                    opcode,
                    vec![
                        register_offset_transfer(bank, 2),
                        preg64(3),
                        preg64(4),
                        imm(mode),
                    ],
                );
                let word = register_offset_word(base, mode, 2, 3, 4);
                for kind in [
                    FixupHoleKind::Branch,
                    FixupHoleKind::Call,
                    FixupHoleKind::GlobalRef,
                    FixupHoleKind::ExternRefGot,
                    FixupHoleKind::TlsTlv,
                    FixupHoleKind::ConstPool,
                ] {
                    for (offset_in_inst, width) in [(0, 0), (0, 4), (1, 1), (4, 1)] {
                        let hole = FixupHole {
                            offset_in_inst,
                            width,
                            kind,
                        };
                        census.observe(&intent, &word.to_le_bytes(), Some(&hole), false);
                    }
                }
                for len in [0, 1, 2, 3, 5, 8] {
                    census.observe(&intent, &vec![0; len], None, false);
                }
            }
        }
        census.finish(12 * 8 * (24 + 6));
    }

    // Pair words independently transcribed from Arm A64 2025-03 LDP/STP
    // integer and SIMD&FP diagrams (pp.503/907/1615/1971). These tests never
    // call the encoder or a production pair-intent descriptor.
    fn pair_memory_rows() -> [(AArch64Opcode, u16, i64, u32); 22] {
        use AArch64Opcode as O;
        [
            (O::StpRI, 32, 4, 0x2900_0000),
            (O::StpRI, 0, 8, 0xa900_0000),
            (O::StpRI, 128, 4, 0x2d00_0000),
            (O::StpRI, 96, 8, 0x6d00_0000),
            (O::StpRI, 64, 16, 0xad00_0000),
            (O::LdpRI, 32, 4, 0x2940_0000),
            (O::LdpRI, 0, 8, 0xa940_0000),
            (O::LdpRI, 128, 4, 0x2d40_0000),
            (O::LdpRI, 96, 8, 0x6d40_0000),
            (O::LdpRI, 64, 16, 0xad40_0000),
            (O::StpPreIndex, 32, 4, 0x2980_0000),
            (O::StpPreIndex, 0, 8, 0xa980_0000),
            (O::StpPreIndex, 128, 4, 0x2d80_0000),
            (O::StpPreIndex, 96, 8, 0x6d80_0000),
            (O::StpPreIndex, 64, 16, 0xad80_0000),
            (O::LdpPostIndex, 32, 4, 0x28c0_0000),
            (O::LdpPostIndex, 0, 8, 0xa8c0_0000),
            (O::LdpPostIndex, 128, 4, 0x2cc0_0000),
            (O::LdpPostIndex, 96, 8, 0x6cc0_0000),
            (O::LdpPostIndex, 64, 16, 0xacc0_0000),
            (O::NeonLdpQPost, 64, 16, 0xacc0_0000),
            (O::NeonStpQPost, 64, 16, 0xac80_0000),
        ]
    }

    fn pair_memory_transfer(bank: u16, field: u8) -> MachOperand {
        let encoding = match (bank, field) {
            (0, 31) => 160,  // XZR, not SP
            (32, 31) => 161, // WZR, not WSP
            _ => bank + u16::from(field),
        };
        MachOperand::PReg(PReg::new(encoding))
    }

    fn pair_memory_word(base: u32, scaled: i64, rt: u8, rt2: u8, rn: u8) -> u32 {
        assert!((-64..=63).contains(&scaled));
        base | ((scaled as u32) & 127) << 15
            | u32::from(rt2) << 10
            | u32::from(rn) << 5
            | u32::from(rt)
    }

    fn pair_memory_fields_valid(op: AArch64Opcode, bank: u16, rt: u8, rt2: u8, rn: u8) -> bool {
        use AArch64Opcode as O;
        let load = matches!(op, O::LdpRI | O::LdpPostIndex | O::NeonLdpQPost);
        let writeback = matches!(
            op,
            O::StpPreIndex | O::LdpPostIndex | O::NeonLdpQPost | O::NeonStpQPost
        );
        (!load || rt != rt2) && !(writeback && bank <= 32 && rn != 31 && (rt == rn || rt2 == rn))
    }

    #[test]
    fn pair_memory_literal_anchors_and_every_single_bit_mutation() {
        let mut census = MemoryDecodeCensus::default();
        for (op, bank, scale, base) in pair_memory_rows() {
            for scaled in [0, -1, -64, 63] {
                let inst = mk(
                    op,
                    vec![
                        pair_memory_transfer(bank, 0),
                        pair_memory_transfer(bank, 31),
                        preg64(2),
                        imm(scaled * scale),
                    ],
                );
                let word = pair_memory_word(base, scaled, 0, 31, 2);
                census.observe(&inst, &word.to_le_bytes(), None, true);
                for bit in 0..32 {
                    census.observe(&inst, &(word ^ (1 << bit)).to_le_bytes(), None, false);
                }
            }
        }
        census.finish(22 * 4 * 33);
    }

    #[test]
    fn pair_memory_all_register_fields_and_architectural_overlap_rules() {
        let mut census = MemoryDecodeCensus::default();
        let mut valid_count = 0;
        for (op, bank, _, base) in pair_memory_rows() {
            for rt in 0..32 {
                for rt2 in 0..32 {
                    for rn in 0..32 {
                        let inst = mk(
                            op,
                            vec![
                                pair_memory_transfer(bank, rt),
                                pair_memory_transfer(bank, rt2),
                                preg64(rn),
                                imm(0),
                            ],
                        );
                        let valid = pair_memory_fields_valid(op, bank, rt, rt2, rn);
                        valid_count += usize::from(valid);
                        census.observe(
                            &inst,
                            &pair_memory_word(base, 0, rt, rt2, rn).to_le_bytes(),
                            None,
                            valid,
                        );
                    }
                }
            }
        }
        assert_eq!(valid_count, 701_882);
        assert_eq!(22 * 32 * 32 * 32 - valid_count, 19_014);
        census.finish(720_896);
    }

    #[test]
    fn pair_memory_complete_imm7_fields_and_omitted_zero_offset() {
        let mut census = MemoryDecodeCensus::default();
        for (op, bank, scale, base) in pair_memory_rows() {
            for (rt, rt2, rn) in [
                (0, 1, 2),
                (30, 31, 29),
                (31, 30, 0),
                (0, 31, 31),
                (31, 0, 31),
                (15, 16, 17),
            ] {
                for scaled in -64..=63 {
                    let inst = mk(
                        op,
                        vec![
                            pair_memory_transfer(bank, rt),
                            pair_memory_transfer(bank, rt2),
                            preg64(rn),
                            imm(scaled * scale),
                        ],
                    );
                    census.observe(
                        &inst,
                        &pair_memory_word(base, scaled, rt, rt2, rn).to_le_bytes(),
                        None,
                        true,
                    );
                }
                let inst = mk(
                    op,
                    vec![
                        pair_memory_transfer(bank, rt),
                        pair_memory_transfer(bank, rt2),
                        preg64(rn),
                    ],
                );
                census.observe(
                    &inst,
                    &pair_memory_word(base, 0, rt, rt2, rn).to_le_bytes(),
                    None,
                    true,
                );
            }
        }
        census.finish(22 * 6 * 129);
    }

    #[test]
    fn pair_memory_strict_banks_shapes_offsets_and_zero_sp_spellings() {
        use trust_cg_ir::VReg;
        let mut census = MemoryDecodeCensus::default();
        for (op, bank, scale, base) in pair_memory_rows() {
            let rt = pair_memory_transfer(bank, 0);
            let rt2 = pair_memory_transfer(bank, 1);
            let args = vec![rt.clone(), rt2.clone(), preg64(2), imm(0)];
            let word = pair_memory_word(base, 0, 0, 1, 2);
            for (bad, field) in [
                (preg64(31), 31),
                (preg32(31), 31),
                (MachOperand::Special(SpecialReg::SP), 31),
                (MachOperand::PReg(PReg::new(165)), 0),
                (MachOperand::PReg(PReg::new(197)), 0),
                (MachOperand::PReg(PReg::new(162)), 0),
                (MachOperand::PReg(PReg::new(512)), 0),
                (imm(0), 0),
                (MachOperand::VReg(VReg::new(0, RegClass::Gpr64)), 0),
            ] {
                for position in [0, 1] {
                    let mut bad_args = args.clone();
                    bad_args[position] = bad.clone();
                    let mutant_word = if position == 0 {
                        pair_memory_word(base, 0, field, 1, 2)
                    } else {
                        pair_memory_word(base, 0, 0, field, 2)
                    };
                    census.observe(&mk(op, bad_args), &mutant_word.to_le_bytes(), None, false);
                }
            }
            for other_bank in [0, 32, 64, 96, 128]
                .into_iter()
                .filter(|other| *other != bank)
            {
                for position in [0, 1] {
                    let mut bad_args = args.clone();
                    bad_args[position] = pair_memory_transfer(other_bank, position as u8);
                    census.observe(&mk(op, bad_args), &word.to_le_bytes(), None, false);
                }
                // Matched alternate data width with stale bytes must also fail.
                let other = mk(
                    op,
                    vec![
                        pair_memory_transfer(other_bank, 0),
                        pair_memory_transfer(other_bank, 1),
                        preg64(2),
                        imm(0),
                    ],
                );
                census.observe(&other, &word.to_le_bytes(), None, false);
                if matches!(
                    op,
                    AArch64Opcode::NeonLdpQPost | AArch64Opcode::NeonStpQPost
                ) {
                    // The Q aliases may not admit otherwise-valid non-Q pairs,
                    // even when their bytes agree with the non-Q data operands.
                    let size_v = match other_bank {
                        0 => 0x8000_0000,
                        32 => 0,
                        96 => 0x4400_0000,
                        128 => 0x0400_0000,
                        _ => unreachable!(),
                    };
                    let non_q_word = (word & !0xc400_0000) | size_v;
                    census.observe(&other, &non_q_word.to_le_bytes(), None, false);
                }
            }
            for (bad, field) in [
                (preg32(2), 2),
                (preg32(31), 31),
                (pair_memory_transfer(0, 31), 31),
                (pair_memory_transfer(32, 31), 31),
                (MachOperand::Special(SpecialReg::XZR), 31),
                (MachOperand::Special(SpecialReg::WZR), 31),
                (MachOperand::PReg(PReg::new(130)), 2),
                (MachOperand::PReg(PReg::new(98)), 2),
                (MachOperand::PReg(PReg::new(66)), 2),
                (MachOperand::PReg(PReg::new(167)), 2),
                (MachOperand::PReg(PReg::new(199)), 2),
                (MachOperand::PReg(PReg::new(162)), 0),
                (MachOperand::PReg(PReg::new(512)), 0),
                (imm(2), 2),
                (MachOperand::VReg(VReg::new(2, RegClass::Gpr64)), 2),
            ] {
                let mut bad_args = args.clone();
                bad_args[2] = bad;
                census.observe(
                    &mk(op, bad_args),
                    &pair_memory_word(base, 0, 0, 1, field).to_le_bytes(),
                    None,
                    false,
                );
            }
            for bad_args in [
                vec![],
                vec![rt.clone()],
                vec![rt.clone(), rt2.clone()],
                vec![rt.clone(), rt2.clone(), preg64(2), imm(0), imm(0)],
                vec![rt.clone(), rt2.clone(), preg64(2), preg64(3)],
                vec![rt.clone(), rt2.clone(), preg64(2), MachOperand::FImm(0.0)],
                vec![
                    rt.clone(),
                    rt2.clone(),
                    MachOperand::MemOp {
                        base: PReg::new(2),
                        offset: 0,
                    },
                ],
                vec![
                    rt.clone(),
                    MachOperand::MemOp {
                        base: PReg::new(2),
                        offset: 0,
                    },
                ],
            ] {
                census.observe(&mk(op, bad_args), &word.to_le_bytes(), None, false);
            }
            for offset in [
                1,
                -1,
                -65 * scale,
                64 * scale,
                i64::MIN,
                i64::MAX,
                (1_i64 << 32) * scale,
                -(1_i64 << 32) * scale,
            ] {
                let mut bad_args = args.clone();
                bad_args[3] = imm(offset);
                census.observe(&mk(op, bad_args), &word.to_le_bytes(), None, false);
            }
            for sp in [preg64(31), MachOperand::Special(SpecialReg::SP)] {
                for (a, b) in [(0, 31), (31, 0), (31, 31)] {
                    let intent = mk(
                        op,
                        vec![
                            pair_memory_transfer(bank, a),
                            pair_memory_transfer(bank, b),
                            sp.clone(),
                            imm(0),
                        ],
                    );
                    census.observe(
                        &intent,
                        &pair_memory_word(base, 0, a, b, 31).to_le_bytes(),
                        None,
                        pair_memory_fields_valid(op, bank, a, b, 31),
                    );
                }
                if bank <= 32 {
                    let zero = MachOperand::Special(if bank == 0 {
                        SpecialReg::XZR
                    } else {
                        SpecialReg::WZR
                    });
                    let physical_zero = pair_memory_transfer(bank, 31);
                    for (a, b, ra, rb) in [
                        (zero.clone(), rt.clone(), 31, 0),
                        (rt.clone(), zero.clone(), 0, 31),
                        (zero.clone(), physical_zero.clone(), 31, 31),
                        (physical_zero, zero.clone(), 31, 31),
                        (zero.clone(), zero, 31, 31),
                    ] {
                        census.observe(
                            &mk(op, vec![a, b, sp.clone(), imm(0)]),
                            &pair_memory_word(base, 0, ra, rb, 31).to_le_bytes(),
                            None,
                            pair_memory_fields_valid(op, bank, ra, rb, 31),
                        );
                    }
                }
            }
        }
        census.finish(22 * (18 + 8 + 4 + 15 + 8 + 8 + 6) + 8 + 80);
    }

    #[test]
    fn pair_memory_refuses_every_hole_kind_and_wrong_byte_length() {
        use crate::decode_check::FixupHoleKind;
        let mut census = MemoryDecodeCensus::default();
        for (op, bank, _, base) in pair_memory_rows() {
            let intent = mk(
                op,
                vec![
                    pair_memory_transfer(bank, 0),
                    pair_memory_transfer(bank, 1),
                    preg64(2),
                    imm(0),
                ],
            );
            let bytes = pair_memory_word(base, 0, 0, 1, 2).to_le_bytes();
            for kind in [
                FixupHoleKind::Branch,
                FixupHoleKind::Call,
                FixupHoleKind::GlobalRef,
                FixupHoleKind::ExternRefGot,
                FixupHoleKind::TlsTlv,
                FixupHoleKind::ConstPool,
            ] {
                for (offset_in_inst, width) in [(0, 0), (0, 4), (1, 1), (4, 1)] {
                    census.observe(
                        &intent,
                        &bytes,
                        Some(&FixupHole {
                            offset_in_inst,
                            width,
                            kind,
                        }),
                        false,
                    );
                }
            }
            for length in [0, 1, 2, 3, 5, 8] {
                census.observe(&intent, &vec![0; length], None, false);
            }
        }
        census.finish(22 * 30);
    }

    #[test]
    fn conditional_select_decode_checks_independent_words_and_every_bit() {
        // Literal words, not output from the encoder under test: Rd=2, Rn=3,
        // Rm=4, condition=PL (5), in both architectural widths.
        let mut words = 0;
        let mut mutants = 0;
        for (opcode, word32, word64) in [
            (AArch64Opcode::Csel, 0x1a84_5062u32, 0x9a84_5062u32),
            (AArch64Opcode::Csinc, 0x1a84_5462, 0x9a84_5462),
            (AArch64Opcode::Csinv, 0x5a84_5062, 0xda84_5062),
            (AArch64Opcode::Csneg, 0x5a84_5462, 0xda84_5462),
        ] {
            for (word, operands) in [
                (word32, vec![preg32(2), preg32(3), preg32(4), imm(5)]),
                (word64, vec![preg64(2), preg64(3), preg64(4), imm(5)]),
            ] {
                let intent = mk(opcode, operands);
                assert!(matches!(
                    A64DecodeCheck.check_one(&intent, &word.to_le_bytes(), None),
                    DecodeCheckOutcome::Match
                ));
                words += 1;
                for bit in 0..32 {
                    let wrong = word ^ (1 << bit);
                    assert!(
                        matches!(
                            A64DecodeCheck.check_one(&intent, &wrong.to_le_bytes(), None),
                            DecodeCheckOutcome::Mismatch(_)
                        ),
                        "{opcode:?}: bit {bit} mutant must mismatch"
                    );
                    mutants += 1;
                }
            }
        }
        assert_eq!((words, mutants), (8, 256));
    }

    #[test]
    fn add_sub_immediate_decode_preserves_strict_width_shift_and_sp_binding() {
        for (opcode, word) in [
            (AArch64Opcode::AddRI, 0x9101_03fdu32),
            (AArch64Opcode::SubRI, 0xd101_03fd),
            (AArch64Opcode::AddRIShift12, 0x9141_03fd),
        ] {
            let intent = mk(
                opcode,
                vec![preg64(29), MachOperand::Special(SpecialReg::SP), imm(64)],
            );
            assert!(matches!(
                A64DecodeCheck.check_one(&intent, &word.to_le_bytes(), None),
                DecodeCheckOutcome::Match
            ));
            for bit in 0..32 {
                assert!(
                    matches!(
                        A64DecodeCheck.check_one(&intent, &(word ^ (1 << bit)).to_le_bytes(), None),
                        DecodeCheckOutcome::Mismatch(_)
                    ),
                    "{opcode:?} bit={bit}"
                );
            }
            for bad in [
                MachOperand::Special(SpecialReg::XZR),
                MachOperand::Special(SpecialReg::WZR),
                MachOperand::PReg(PReg::new(160)),
                MachOperand::PReg(PReg::new(161)),
                MachOperand::PReg(PReg::new(63)),
            ] {
                let mut malformed = intent.clone();
                malformed.operands[1] = bad;
                assert!(matches!(
                    A64DecodeCheck.check_one(&malformed, &word.to_le_bytes(), None),
                    DecodeCheckOutcome::Mismatch(_)
                ));
            }
            let mut malformed = intent.clone();
            malformed.operands.push(imm(0));
            assert!(matches!(
                A64DecodeCheck.check_one(&malformed, &word.to_le_bytes(), None),
                DecodeCheckOutcome::Mismatch(_)
            ));
        }
        let intent = mk(AArch64Opcode::AddRI, vec![preg64(0), preg32(1), imm(64)]);
        assert!(matches!(
            A64DecodeCheck.check_one(&intent, &0x9101_0020u32.to_le_bytes(), None),
            DecodeCheckOutcome::Mismatch(_)
        ));
        let intent = mk(
            AArch64Opcode::AddRI,
            vec![preg64(0), MachOperand::PReg(PReg::new(64)), imm(64)],
        );
        assert!(matches!(
            A64DecodeCheck.check_one(&intent, &0x9101_0000u32.to_le_bytes(), None),
            DecodeCheckOutcome::Mismatch(_)
        ));
    }

    #[test]
    fn conditional_select_decode_rejects_malformed_intents_not_allowlisted() {
        let mut rejected = 0;
        for (opcode, word) in [
            (AArch64Opcode::Csel, 0x9a84_5062u32),
            (AArch64Opcode::Csinc, 0x9a84_5462),
            (AArch64Opcode::Csinv, 0xda84_5062),
            (AArch64Opcode::Csneg, 0xda84_5462),
        ] {
            let valid = vec![preg64(2), preg64(3), preg64(4), imm(5)];
            let mut shapes = vec![Vec::new(), valid[..3].to_vec()];
            let mut extra = valid.clone();
            extra.push(imm(0));
            shapes.push(extra);
            for index in 0..3 {
                for bad_register in [
                    preg32(2),
                    MachOperand::PReg(PReg::new(31)),  // SP
                    MachOperand::PReg(PReg::new(63)),  // WSP
                    MachOperand::PReg(PReg::new(64)),  // V0
                    MachOperand::PReg(PReg::new(96)),  // D0
                    MachOperand::PReg(PReg::new(162)), // NZCV
                    MachOperand::Special(SpecialReg::SP),
                    MachOperand::Special(SpecialReg::WZR), // wrong width
                    MachOperand::VReg(trust_cg_ir::VReg::new(0, RegClass::Gpr64)),
                    imm(0),
                ] {
                    let mut malformed = valid.clone();
                    malformed[index] = bad_register;
                    shapes.push(malformed);
                }
            }
            for condition in [imm(-1), imm(16), imm(i64::MAX), preg64(0)] {
                let mut malformed = valid.clone();
                malformed[3] = condition;
                shapes.push(malformed);
            }
            for operands in shapes {
                let intent = mk(opcode, operands);
                assert!(
                    matches!(
                        A64DecodeCheck.check_one(&intent, &word.to_le_bytes(), None),
                        DecodeCheckOutcome::Mismatch(_)
                    ),
                    "{intent:?} must not match or receive allowlist credit"
                );
                rejected += 1;
            }
        }
        assert_eq!(rejected, 148);
    }

    #[test]
    fn conditional_select_decode_keeps_raw_al_nv_and_zero_registers() {
        let mut checked = 0;
        for (opcode, base) in [
            (AArch64Opcode::Csel, 0x1a9f_03ffu32),
            (AArch64Opcode::Csinc, 0x1a9f_07ff),
            (AArch64Opcode::Csinv, 0x5a9f_03ff),
            (AArch64Opcode::Csneg, 0x5a9f_07ff),
        ] {
            for (sf, special, physical) in [
                (0, SpecialReg::WZR, PReg::new(161)),
                (1, SpecialReg::XZR, PReg::new(160)),
            ] {
                for condition in 0..16 {
                    let word = base | (sf << 31) | ((condition as u32) << 12);
                    let intent = mk(
                        opcode,
                        vec![
                            MachOperand::Special(special),
                            MachOperand::PReg(physical),
                            MachOperand::Special(special),
                            imm(condition),
                        ],
                    );
                    assert!(matches!(
                        A64DecodeCheck.check_one(&intent, &word.to_le_bytes(), None),
                        DecodeCheckOutcome::Match
                    ));
                    checked += 1;
                }
            }
        }
        assert_eq!(checked, 128);
    }

    #[test]
    fn conditional_select_decode_cset_alias_is_exact_and_excludes_al_nv() {
        for (word, dst) in [(0x1a9f_47e2u32, preg32(2)), (0x9a9f_47e2, preg64(2))] {
            let intent = mk(AArch64Opcode::CSet, vec![dst, imm(5)]);
            assert!(matches!(
                A64DecodeCheck.check_one(&intent, &word.to_le_bytes(), None),
                DecodeCheckOutcome::Match
            ));
            for bit in 0..32 {
                assert!(matches!(
                    A64DecodeCheck.check_one(&intent, &(word ^ (1 << bit)).to_le_bytes(), None),
                    DecodeCheckOutcome::Mismatch(_)
                ));
            }
        }
        let mut rejected = 0;
        let mut shapes = vec![Vec::new(), vec![preg64(2)], vec![preg64(2), imm(5), imm(0)]];
        for condition in [imm(-1), imm(14), imm(15), imm(16), imm(i64::MAX), preg64(0)] {
            shapes.push(vec![preg64(2), condition]);
        }
        for destination in [
            MachOperand::PReg(PReg::new(31)),
            MachOperand::PReg(PReg::new(63)),
            MachOperand::PReg(PReg::new(64)),
            MachOperand::PReg(PReg::new(96)),
            MachOperand::PReg(PReg::new(162)),
            MachOperand::Special(SpecialReg::SP),
            MachOperand::VReg(trust_cg_ir::VReg::new(0, RegClass::Gpr64)),
            imm(0),
        ] {
            shapes.push(vec![destination, imm(5)]);
        }
        for operands in shapes {
            let intent = mk(AArch64Opcode::CSet, operands);
            assert!(
                matches!(
                    A64DecodeCheck.check_one(&intent, &0x9a9f_47e2u32.to_le_bytes(), None),
                    DecodeCheckOutcome::Mismatch(_)
                ),
                "{intent:?}"
            );
            rejected += 1;
        }
        assert_eq!(rejected, 17);
    }

    /// Encode→independently-decode roundtrip over the slice-1 matrix: every
    /// covered family, several registers and immediates.
    #[test]
    fn slice1_roundtrip_matrix_matches() {
        for rd in [0u8, 1, 5, 17, 29] {
            for immv in [0i64, 1, 0x7F, 0xFFF] {
                assert_match(mk(
                    AArch64Opcode::AddRI,
                    vec![preg64(rd), preg64((rd + 1) % 30), imm(immv)],
                ));
                assert_match(mk(
                    AArch64Opcode::SubRI,
                    vec![preg64(rd), preg64((rd + 3) % 30), imm(immv)],
                ));
            }
            for imm16 in [0i64, 1, 0xBEEF, 0xFFFF] {
                assert_match(mk(AArch64Opcode::Movz, vec![preg64(rd), imm(imm16)]));
                assert_match(mk(AArch64Opcode::Movn, vec![preg64(rd), imm(imm16)]));
                assert_match(mk(
                    AArch64Opcode::Movn,
                    vec![preg64(rd), imm(imm16), imm(0)],
                ));
            }
            for shift in [0i64, 16, 32, 48] {
                assert_match(mk(
                    AArch64Opcode::Movk,
                    vec![preg64(rd), imm(0x1234), imm(shift)],
                ));
            }
        }
        for (op, a, b, d) in [
            (AArch64Opcode::AddRR, 1u8, 2u8, 3u8),
            (AArch64Opcode::SubRR, 4, 5, 6),
            (AArch64Opcode::AndRR, 7, 8, 9),
            (AArch64Opcode::OrrRR, 10, 11, 12),
            (AArch64Opcode::EorRR, 13, 14, 15),
        ] {
            assert_match(mk(op, vec![preg64(d), preg64(a), preg64(b)]));
        }
        for (op, shift) in [
            (AArch64Opcode::EorRRLsl, 13i64),
            (AArch64Opcode::EorRRLsr, 7),
            (AArch64Opcode::EorRRShift, 17),
        ] {
            assert_match(mk(op, vec![preg64(3), preg64(4), preg64(5), imm(shift)]));
        }
        // Load/store: scaled-UI offsets, the unscaled negative/unaligned
        // forms, and both address layouts (PReg+Imm, SP base).
        for off in [0i64, 8, 256, 32760] {
            assert_match(mk(
                AArch64Opcode::LdrRI,
                vec![preg64(2), preg64(3), imm(off)],
            ));
            assert_match(mk(
                AArch64Opcode::StrRI,
                vec![preg64(4), preg64(5), imm(off)],
            ));
        }
        for off in [-8i64, -256, 3, 13] {
            assert_match(mk(
                AArch64Opcode::LdrRI,
                vec![preg64(6), preg64(7), imm(off)],
            ));
            assert_match(mk(
                AArch64Opcode::StrRI,
                vec![preg64(8), preg64(9), imm(off)],
            ));
        }
        // Slice-5 families.
        for (d, sr) in [(0u8, 1u8), (5, 6), (29, 30)] {
            assert_match(mk(AArch64Opcode::MOVXrr, vec![preg64(d), preg64(sr)]));
        }
        assert_match(mk(AArch64Opcode::CmpRR, vec![preg64(3), preg64(4)]));
        assert_match(mk(AArch64Opcode::CmpRI, vec![preg64(3), imm(0x7F)]));
        for cond in [0i64, 1, 10, 11] {
            assert_match(mk(AArch64Opcode::CSet, vec![preg64(2), imm(cond)]));
            assert_match(mk(
                AArch64Opcode::Csel,
                vec![preg64(2), preg64(3), preg64(4), imm(cond)],
            ));
            assert_match(mk(AArch64Opcode::BCond, vec![imm(cond), imm(8)]));
        }
        assert_match(mk(
            AArch64Opcode::MulRR,
            vec![preg64(1), preg64(2), preg64(3)],
        ));
        assert_match(mk(
            AArch64Opcode::Madd,
            vec![preg64(1), preg64(2), preg64(3), preg64(4)],
        ));
        assert_match(mk(
            AArch64Opcode::Msub,
            vec![preg64(5), preg64(6), preg64(7), preg64(8)],
        ));
        for op in [
            AArch64Opcode::LslRR,
            AArch64Opcode::LsrRR,
            AArch64Opcode::AsrRR,
        ] {
            assert_match(mk(op, vec![preg64(1), preg64(2), preg64(3)]));
        }
        assert_match(mk(
            AArch64Opcode::OrnRR,
            vec![preg64(1), preg64(2), preg64(3)],
        ));
        assert_match(mk(AArch64Opcode::MovR, vec![preg64(9), preg64(10)]));
        assert_match(mk(
            AArch64Opcode::SDiv,
            vec![preg64(1), preg64(2), preg64(3)],
        ));
        assert_match(mk(
            AArch64Opcode::UDiv,
            vec![preg64(4), preg64(5), preg64(6)],
        ));
        // Slice-6: extends and immediate shifts.
        for op in [
            AArch64Opcode::Sxtb,
            AArch64Opcode::Sxth,
            AArch64Opcode::Sxtw,
            AArch64Opcode::Uxtb,
            AArch64Opcode::Uxth,
        ] {
            assert_match(mk(op, vec![preg64(3), preg64(4)]));
        }
        for shift in [0i64, 1, 5, 31, 63] {
            assert_match(mk(
                AArch64Opcode::LslRI,
                vec![preg64(1), preg64(2), imm(shift)],
            ));
            assert_match(mk(
                AArch64Opcode::LsrRI,
                vec![preg64(1), preg64(2), imm(shift)],
            ));
            assert_match(mk(
                AArch64Opcode::AsrRI,
                vec![preg64(1), preg64(2), imm(shift)],
            ));
        }
        for (op, immr, imms) in [
            (AArch64Opcode::Ubfm, 8i64, 11i64),
            (AArch64Opcode::Sbfm, 7, 19),
            (AArch64Opcode::Bfm, 13, 29),
        ] {
            assert_match(mk(op, vec![preg64(3), preg64(4), imm(immr), imm(imms)]));
            assert_match(mk(op, vec![preg32(5), preg32(6), imm(immr), imm(imms)]));
        }
        assert_match(mk(AArch64Opcode::Ret, vec![]));
        for rn in [0u8, 7, 30] {
            assert_match(mk(AArch64Opcode::Blr, vec![preg64(rn)]));
        }
        for target in [1i64, 4, 100] {
            assert_match(mk(AArch64Opcode::Cbz, vec![preg64(3), imm(target)]));
            assert_match(mk(AArch64Opcode::Cbnz, vec![preg64(3), imm(target)]));
        }
    }

    #[test]
    fn immediate_shift_decode_check_rejects_out_of_domain_intent() {
        for opcode in [
            AArch64Opcode::LslRI,
            AArch64Opcode::LsrRI,
            AArch64Opcode::AsrRI,
        ] {
            for (rd, rn, width) in [(preg32(1), preg32(2), 32), (preg64(1), preg64(2), 64)] {
                let valid = mk(opcode, vec![rd.clone(), rn.clone(), imm(1)]);
                let word = encode_instruction(&valid).unwrap().to_le_bytes();
                for shift in [i64::MIN, -1, width, width + 1, (1i64 << 32) + 1, i64::MAX] {
                    let invalid = mk(opcode, vec![rd.clone(), rn.clone(), imm(shift)]);
                    assert!(
                        matches!(
                            A64DecodeCheck.check_one(&invalid, &word, None),
                            DecodeCheckOutcome::Mismatch(_)
                        ),
                        "{opcode:?} width {width}, invalid shift {shift}"
                    );
                }
                for shift in 0..width {
                    assert_match(mk(opcode, vec![rd.clone(), rn.clone(), imm(shift)]));
                }
            }
        }
    }

    #[test]
    fn ubfm_decode_check_rejects_wrong_extract_window() {
        let inst = mk(
            AArch64Opcode::Ubfm,
            vec![preg64(3), preg64(4), imm(8), imm(11)],
        );
        let mut word = encode_instruction(&inst).expect("encode UBFM");
        word ^= 1 << 10; // change imms while leaving the intent untouched
        assert!(matches!(
            A64DecodeCheck.check_one(&inst, &word.to_le_bytes(), None),
            DecodeCheckOutcome::Mismatch { .. }
        ));
    }

    /// Regression: large byte-sum bounds must pass through the real encoder and
    /// independent decoder using the canonical MOVZ#0 + MOVK sequence.
    #[test]
    fn large_bound_materialization_roundtrips_without_shifted_movz() {
        let bound = 100_000i64 - (128 - 1);
        let lo = bound & 0xFFFF;
        let hi = (bound >> 16) & 0xFFFF;

        assert_match(mk(AArch64Opcode::Movz, vec![preg64(2), imm(lo)]));
        assert_match(mk(AArch64Opcode::Movk, vec![preg64(2), imm(hi), imm(16)]));

        // A low-zero constant must still seed the register with MOVZ#0 before
        // installing the high halfword with MOVK.
        assert_match(mk(AArch64Opcode::Movz, vec![preg64(3), imm(0)]));
        assert_match(mk(AArch64Opcode::Movk, vec![preg64(3), imm(1), imm(16)]));

        let shifted = mk(AArch64Opcode::Movz, vec![preg64(3), imm(1), imm(16)]);
        assert!(
            encode_instruction(&shifted).is_err(),
            "nonzero-shift MOVZ must not be emitted"
        );

        let shifted = mk(AArch64Opcode::Movn, vec![preg64(3), imm(1), imm(16)]);
        assert!(
            encode_instruction(&shifted).is_err(),
            "nonzero-shift MOVN must not be emitted"
        );
    }

    /// The checker accepts opcode-owned typed widths and catches a word whose
    /// sf bit instead follows the mismatched allocated-register view. Since
    /// L04-P11 the typed copies carry the decoded-word value obligation, which
    /// runs before the structural arm and refutes the wrong width at bit 32.
    #[test]
    fn typed_move_width_is_opcode_owned_and_mismatches_are_caught() {
        let movw_over_x = mk(AArch64Opcode::MOVWrr, vec![preg64(3), preg64(4)]);
        let movw_word = encode_instruction(&movw_over_x).expect("encode MOVWrr truncation");
        assert_eq!(movw_word >> 31, 0, "MOVWrr must encode the W-form");
        assert!(matches!(
            A64DecodeCheck.check_one(&movw_over_x, &movw_word.to_le_bytes(), None),
            DecodeCheckOutcome::Match
        ));
        let wrong_movw_word = movw_word | (1 << 31);
        match A64DecodeCheck.check_one(&movw_over_x, &wrong_movw_word.to_le_bytes(), None) {
            DecodeCheckOutcome::Mismatch(e) => assert!(
                e.message
                    .contains("aarch64_value_decode_proofs rejected MOVWrr")
                    && e.message.contains("bit 32"),
                "width mismatch must be refuted by the value obligation, got: {}",
                e.message
            ),
            other => panic!("X-form MOVWrr must mismatch, got {other:?}"),
        }

        let movx_over_w = mk(AArch64Opcode::MOVXrr, vec![preg32(5), preg32(6)]);
        let movx_word = encode_instruction(&movx_over_w).expect("encode MOVXrr width override");
        assert_eq!(movx_word >> 31, 1, "MOVXrr must encode the X-form");
        assert!(matches!(
            A64DecodeCheck.check_one(&movx_over_w, &movx_word.to_le_bytes(), None),
            DecodeCheckOutcome::Match
        ));
        let wrong_movx_word = movx_word & !(1 << 31);
        match A64DecodeCheck.check_one(&movx_over_w, &wrong_movx_word.to_le_bytes(), None) {
            DecodeCheckOutcome::Mismatch(e) => assert!(
                e.message
                    .contains("aarch64_value_decode_proofs rejected MOVXrr")
                    && e.message.contains("bit 32"),
                "width mismatch must be refuted by the value obligation, got: {}",
                e.message
            ),
            other => panic!("W-form MOVXrr must mismatch, got {other:?}"),
        }
    }

    /// Field corruption must be CAUGHT: flipping a register or immediate bit
    /// in the emitted word turns Match into Mismatch (this is the property
    /// that makes the check a net — a bug that alters any compared field is
    /// visible).
    #[test]
    fn slice1_field_corruption_is_caught() {
        let cases = vec![
            (
                mk(AArch64Opcode::AddRI, vec![preg64(4), preg64(9), imm(0x2A)]),
                0u32,
            ),
            (mk(AArch64Opcode::Movz, vec![preg64(2), imm(0x1234)]), 0),
            (mk(AArch64Opcode::Movz, vec![preg64(2), imm(0x1234)]), 7), // imm16 bit
            (
                mk(AArch64Opcode::Movk, vec![preg64(2), imm(0x1234), imm(48)]),
                21,
            ), // hw bit
            (mk(AArch64Opcode::Ret, vec![]), 5),                        // Rn bit
            (mk(AArch64Opcode::Cbnz, vec![preg64(6), imm(8)]), 0),      // Rt bit
            (
                mk(AArch64Opcode::AddRR, vec![preg64(1), preg64(2), preg64(3)]),
                16,
            ), // Rm bit
            (
                mk(AArch64Opcode::OrrRR, vec![preg64(1), preg64(2), preg64(3)]),
                5,
            ), // Rn bit
            (
                mk(AArch64Opcode::LdrRI, vec![preg64(1), preg64(2), imm(16)]),
                0,
            ), // Rt bit
            (
                mk(AArch64Opcode::StrRI, vec![preg64(1), preg64(2), imm(-8)]),
                12,
            ), // imm9 bit
            (mk(AArch64Opcode::CmpRR, vec![preg64(3), preg64(4)]), 16), // Rm bit
            (mk(AArch64Opcode::CSet, vec![preg64(2), imm(4)]), 12),     // cond bit
            (
                mk(AArch64Opcode::MulRR, vec![preg64(1), preg64(2), preg64(3)]),
                10,
            ), // Ra bit
            (
                mk(AArch64Opcode::SDiv, vec![preg64(1), preg64(2), preg64(3)]),
                10,
            ), // opcode bit
            (mk(AArch64Opcode::Sxtw, vec![preg64(1), preg64(2)]), 10),  // imms bit
            (
                mk(AArch64Opcode::LsrRI, vec![preg64(1), preg64(2), imm(7)]),
                16,
            ), // immr bit
        ];
        for (inst, bit) in cases {
            let w = encode_instruction(&inst).expect("encode") ^ (1 << bit);
            match A64DecodeCheck.check_one(&inst, &w.to_le_bytes(), None) {
                DecodeCheckOutcome::Mismatch(_) => {}
                other => panic!(
                    "{:?} with bit {bit} flipped: expected Mismatch, got {other:?}",
                    inst.opcode
                ),
            }
        }
    }

    /// A wrong LENGTH (not 4 bytes) is always a mismatch.
    #[test]
    fn slice1_wrong_length_is_caught() {
        let inst = mk(AArch64Opcode::Ret, vec![]);
        let w = encode_instruction(&inst).expect("encode").to_le_bytes();
        for len in [0usize, 3, 5] {
            let mut buf = w.to_vec();
            buf.resize(len, 0);
            match A64DecodeCheck.check_one(&inst, &buf, None) {
                DecodeCheckOutcome::Mismatch(_) => {}
                other => panic!("len {len}: expected Mismatch, got {other:?}"),
            }
        }
    }

    /// Every LL/SC exclusive and CLREX word decode-checks, and every
    /// single-bit mutant of it is a mismatch.
    #[test]
    fn llsc_exclusive_and_clrex_words_decode_check_and_mutants_are_caught() {
        let cases = [
            mk(AArch64Opcode::Ldxr, vec![preg32(0), preg64(1)]),
            mk(AArch64Opcode::Ldxr, vec![preg64(2), preg64(3)]),
            mk(AArch64Opcode::Ldxrb, vec![preg32(4), preg64(5)]),
            mk(AArch64Opcode::Ldxrh, vec![preg32(6), preg64(7)]),
            mk(AArch64Opcode::Ldaxr, vec![preg64(8), preg64(9)]),
            mk(AArch64Opcode::Ldaxrb, vec![preg32(8), preg64(9)]),
            mk(AArch64Opcode::Ldaxrh, vec![preg32(10), preg64(11)]),
            mk(AArch64Opcode::Stxr, vec![preg32(0), preg32(1), preg64(2)]),
            mk(AArch64Opcode::Stxr, vec![preg32(3), preg64(4), preg64(5)]),
            mk(AArch64Opcode::Stxrb, vec![preg32(7), preg32(8), preg64(9)]),
            mk(
                AArch64Opcode::Stxrh,
                vec![preg32(10), preg32(11), preg64(12)],
            ),
            mk(
                AArch64Opcode::Stlxr,
                vec![preg32(13), preg64(14), preg64(15)],
            ),
            mk(
                AArch64Opcode::Stlxrb,
                vec![preg32(13), preg32(14), preg64(15)],
            ),
            mk(
                AArch64Opcode::Stlxrh,
                vec![preg32(16), preg32(17), preg64(18)],
            ),
            mk(AArch64Opcode::Clrex, vec![]),
            mk(AArch64Opcode::Ldxp, vec![preg64(0), preg64(1), preg64(2)]),
            mk(AArch64Opcode::Ldaxp, vec![preg64(3), preg64(4), preg64(5)]),
            mk(
                AArch64Opcode::Stxp,
                vec![preg32(0), preg64(1), preg64(2), preg64(3)],
            ),
            mk(
                AArch64Opcode::Stlxp,
                vec![preg32(4), preg64(5), preg64(6), preg64(7)],
            ),
        ];
        for inst in cases {
            let word = encode_instruction(&inst).unwrap();
            assert!(
                matches!(
                    A64DecodeCheck.check_one(&inst, &word.to_le_bytes(), None),
                    DecodeCheckOutcome::Match
                ),
                "{inst:?}"
            );
            // Every single-bit mutation of the emitted word is caught: a
            // mutant either decodes to different fields or leaves the family.
            for bit in 0..32 {
                let mutant = word ^ (1 << bit);
                if inst.opcode == AArch64Opcode::Clrex && (8..12).contains(&bit) {
                    // CRm is architecturally ignored, but the checker pins 15.
                    assert!(matches!(
                        A64DecodeCheck.check_one(&inst, &mutant.to_le_bytes(), None),
                        DecodeCheckOutcome::Mismatch(_)
                    ));
                    continue;
                }
                assert!(
                    matches!(
                        A64DecodeCheck.check_one(&inst, &mutant.to_le_bytes(), None),
                        DecodeCheckOutcome::Mismatch(_)
                    ),
                    "{inst:?}: bit {bit} mutant {mutant:#010x} escaped"
                );
            }
        }
    }

    /// Uncovered families are counted allowlist entries, never silent skips
    /// and never spurious mismatches.
    #[test]
    fn slice1_uncovered_family_is_allowlisted() {
        // A retain/release pseudo encodes as NOP when a caller does not skip
        // it; ENC-5 has no arm for it.
        let inst = mk(AArch64Opcode::Retain, vec![preg64(0)]);
        let w = encode_instruction(&inst).expect("encode");
        match A64DecodeCheck.check_one(&inst, &w.to_le_bytes(), None) {
            DecodeCheckOutcome::Allowlisted(_) => {}
            other => panic!("expected Allowlisted, got {other:?}"),
        }
    }

    /// The decoded-word value obligation runs on every MOV (register), scalar
    /// FMOV, SMULL, BFM, RBIT, shifted ADD and MRS: live encoder output
    /// matches, and wrong pairings the structural fields would not name are
    /// rejected — a copy from SP spelled as ORR (it reads XZR), an FMOV whose
    /// word moves a different width, a UMULL word for SMULL, a TPIDRRO_EL0
    /// read for TPIDR_EL0.
    #[test]
    fn decoded_value_obligation_runs_per_emitted_word() {
        use trust_cg_ir::regs::{PReg, SP};
        let preg = |encoding: u16| MachOperand::PReg(PReg::new(encoding));
        let s = |n: u16| preg(128 + n);
        let d = |n: u16| preg(96 + n);
        let tpidr = imm(0xDE82);
        for inst in [
            mk(AArch64Opcode::MovR, vec![preg64(3), preg64(7)]),
            mk(AArch64Opcode::MovR, vec![preg32(3), preg32(7)]),
            mk(AArch64Opcode::MovR, vec![preg64(3), MachOperand::PReg(SP)]),
            mk(AArch64Opcode::MovR, vec![MachOperand::PReg(SP), preg64(4)]),
            mk(AArch64Opcode::FmovFprFpr, vec![s(3), s(7)]),
            mk(AArch64Opcode::FmovFprFpr, vec![d(3), d(7)]),
            mk(AArch64Opcode::FmovFprGpr, vec![preg32(3), s(7)]),
            mk(AArch64Opcode::FmovFprGpr, vec![preg64(3), d(7)]),
            mk(AArch64Opcode::FmovGprFpr, vec![s(3), preg32(7)]),
            mk(AArch64Opcode::FmovGprFpr, vec![d(3), preg64(7)]),
            mk(AArch64Opcode::Smull, vec![preg64(3), preg32(7), preg32(12)]),
            mk(AArch64Opcode::Rbit, vec![preg32(3), preg32(7)]),
            mk(AArch64Opcode::Rbit, vec![preg64(3), preg64(7)]),
            mk(
                AArch64Opcode::Bfm,
                vec![preg64(3), preg64(7), imm(56), imm(4)],
            ),
            mk(
                AArch64Opcode::AddRIShift12,
                vec![preg64(3), preg64(7), imm(0x123)],
            ),
            mk(AArch64Opcode::Mrs, vec![preg64(3), tpidr.clone()]),
        ] {
            assert_match(inst);
        }
        let check =
            |inst: &MachInst, word: u32| A64DecodeCheck.check_one(inst, &word.to_le_bytes(), None);
        for (inst, word) in [
            // ORR X3, XZR, XZR for MOV X3, SP: register 31 in ORR is XZR.
            (
                mk(AArch64Opcode::MovR, vec![preg64(3), MachOperand::PReg(SP)]),
                0xAA1F_03E3,
            ),
            // FMOV W3, H7 for FMOV W3, S7.
            (
                mk(AArch64Opcode::FmovFprGpr, vec![preg32(3), s(7)]),
                0x1EE6_00E3,
            ),
            // FMOV S3, W7 (the other direction) for FMOV W3, S7.
            (
                mk(AArch64Opcode::FmovFprGpr, vec![preg32(3), s(7)]),
                0x1E27_00E3,
            ),
            // UMULL X3, W7, W12 for SMULL.
            (
                mk(AArch64Opcode::Smull, vec![preg64(3), preg32(7), preg32(12)]),
                0x9BAC_7CE3,
            ),
            // MRS X3, TPIDRRO_EL0 for TPIDR_EL0.
            (
                mk(AArch64Opcode::Mrs, vec![preg64(3), tpidr.clone()]),
                0xD53B_D063,
            ),
            // REV W3, W7 for RBIT W3, W7.
            (
                mk(AArch64Opcode::Rbit, vec![preg32(3), preg32(7)]),
                0x5AC0_08E3,
            ),
        ] {
            match check(&inst, word) {
                DecodeCheckOutcome::Mismatch(error) => {
                    assert!(
                        error.message.contains("aarch64_value_decode_proofs"),
                        "{inst:?}: {error:?}"
                    );
                }
                other => panic!("{inst:?} = {word:#010x}: expected Mismatch, got {other:?}"),
            }
        }
        // An ill-formed cross-class FMOV fails closed even before a word is
        // considered; an unmodeled MRS key makes no claim (named allowlist).
        match check(
            &mk(AArch64Opcode::FmovFprGpr, vec![preg32(3), d(7)]),
            0x1E66_00E3,
        ) {
            DecodeCheckOutcome::Mismatch(_) => {}
            other => panic!("ill-formed FMOV W, D must mismatch, got {other:?}"),
        }
        match check(
            &mk(AArch64Opcode::Mrs, vec![preg64(3), imm(0xDA20)]),
            0xD53B_4203,
        ) {
            DecodeCheckOutcome::Allowlisted(_) => {}
            other => panic!("unmodeled MRS key must be allowlisted, got {other:?}"),
        }
    }

    /// ENC-5 binds every NEON lane-effect opcode's emitted word to the word
    /// the verifier's word-bound lane-effect decomposition carries (L04-P6).
    /// For one admitted shape of each opcode in
    /// `trust_cg_verify::aarch64_neon_lane_effect::NEON_LANE_EFFECT_OPCODES`,
    /// the encoder's word is the decomposition's and matches; every
    /// single-bit flip of it mismatches with the binding's own message. The
    /// binding runs before the FP/SIMD slice, so deleting it changes every
    /// one of these messages even where the slice's independent decode would
    /// still refuse the word.
    #[test]
    fn neon_lane_effect_binding_names_every_single_bit_corruption() {
        use AArch64Opcode as Op;
        use trust_cg_verify::aarch64_neon_lane_effect::{
            NEON_LANE_EFFECT_OPCODES, neon_lane_effect_word,
        };
        let preg = |n: u16| MachOperand::PReg(PReg::new(n));
        let (v, d, s) = (
            |n: u16| preg(64 + n),
            |n: u16| preg(96 + n),
            |n: u16| preg(128 + n),
        );
        let shapes = [
            mk(Op::NeonDupElem, vec![v(3), v(17), imm(1), imm(4)]),
            mk(Op::NeonDupGen, vec![v(2), preg32(5), imm(4)]),
            mk(Op::NeonInsGen, vec![v(9), preg64(7), imm(1), imm(8)]),
            mk(Op::NeonUmovGen, vec![preg32(3), v(4), imm(2), imm(4)]),
            mk(Op::NeonDupScalarD, vec![d(1), v(30), imm(1)]),
            mk(Op::NeonUmaxv, vec![s(2), v(5), imm(5)]),
            mk(Op::NeonAddpScalar, vec![d(0), v(31), imm(6)]),
            mk(Op::NeonRev32V, vec![v(1), v(2), imm(1)]),
            mk(Op::NeonRev64V, vec![v(1), v(2), imm(5)]),
            mk(Op::NeonRbitV, vec![v(6), v(7), imm(1)]),
            mk(Op::NeonExtV, vec![v(0), v(1), v(2), imm(12)]),
            mk(Op::NeonMovi, vec![v(3), imm(0xA5)]),
        ];
        let covered: Vec<Op> = shapes.iter().map(|inst| inst.opcode).collect();
        assert_eq!(covered, NEON_LANE_EFFECT_OPCODES);
        for inst in &shapes {
            let derived = neon_lane_effect_word(inst)
                .unwrap_or_else(|| panic!("{inst:?} is an admitted lane-effect shape"));
            let word = encode_instruction(inst).expect("encode");
            assert_eq!(word, derived, "{inst:?}: encoder and decomposition words");
            assert!(
                matches!(
                    A64DecodeCheck.check_one(inst, &word.to_le_bytes(), None),
                    DecodeCheckOutcome::Match
                ),
                "{inst:?}"
            );
            for bit in 0..32 {
                let corrupted = word ^ (1 << bit);
                match A64DecodeCheck.check_one(inst, &corrupted.to_le_bytes(), None) {
                    DecodeCheckOutcome::Mismatch(error) => assert!(
                        error
                            .message
                            .contains("the NEON lane-effect obligations carry"),
                        "{inst:?} bit {bit}: {}",
                        error.message
                    ),
                    other => panic!("{inst:?} bit {bit}: {other:?}"),
                }
            }
        }
    }
}
