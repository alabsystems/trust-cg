//! ENC-5 — independent AArch64 decode-check (slice 1).
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
//! Disproportionately valuable on aarch64: the x86 dev box cannot execute
//! a64 code, so an encoding bug has no native-run net to catch it.
//!
//! SLICE 1 covers the highest-frequency integer format families:
//! move-wide (MOVN/MOVZ/MOVK), add/sub-immediate, B/BL, BR/BLR/RET,
//! CBZ/CBNZ, and B.cond. Every other opcode family is
//! [`DecodeCheckOutcome::Allowlisted`] under a named reason — counted,
//! never silently skipped — and shrinks with each slice.

use trust_cg_ir::inst::{AArch64Opcode, MachInst};
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::regs::{RegClass, SpecialReg, preg_class};

use crate::decode_check::{DecodeCheck, DecodeCheckError, DecodeCheckOutcome, FixupHole};

/// The independent decoding of one AArch64 instruction word — only the
/// families slice 1 knows. Field names follow the Arm ARM diagrams.
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

/// Decode one instruction word into a slice-1 family, or `None` when the word
/// belongs to a family this slice does not model.
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
    // Conditional select: bits 28:21 == 11010100 and S(29) == 0.
    if (w >> 21) & 0xFF == 0b1101_0100 && (w >> 29) & 1 == 0 {
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

/// Mirror of the encoder's `extract_base_offset`: the memory operand is
/// either `[.., Rn(PReg), Imm]` (pre-frame-lowering) or `[.., MemOp{base,
/// offset}]` (post-frame-lowering).
fn intent_base_offset(inst: &MachInst, base_idx: usize, imm_idx: usize) -> Option<(u32, i64)> {
    match inst.operands.get(base_idx)? {
        MachOperand::PReg(p) => {
            let off = intent_imm(inst, imm_idx).unwrap_or(0);
            Some((p.hw_enc() as u32, off))
        }
        MachOperand::Special(SpecialReg::SP) => {
            let off = intent_imm(inst, imm_idx).unwrap_or(0);
            Some((31, off))
        }
        MachOperand::MemOp { base, offset } => Some((base.hw_enc() as u32, *offset)),
        _ => None,
    }
}

/// Whether the intent's operand `idx` is a GPR (the slice-4 load/store
/// coverage; FPR forms decline to a later slice).
fn intent_is_gpr(inst: &MachInst, idx: usize) -> bool {
    match inst.operands.get(idx) {
        Some(MachOperand::PReg(p)) => {
            matches!(preg_class(*p), RegClass::Gpr32 | RegClass::Gpr64)
        }
        Some(MachOperand::Special(_)) => true,
        _ => false,
    }
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

/// Rollout mode for the aarch64 gate. `TCG_DECODE_CHECK_A64` overrides
/// (off/warn/enforce); the arch default is ENFORCE — ratcheted 2026-07-19
/// per the soundness-doctrine gate rollout after the warn evidence ran
/// clean: repeated a64_corpus_sweep runs at 97% instruction coverage with
/// 16305/16305 matches and ZERO disagreements, plus the bridge-driven
/// real_program_corpus_a64 row compiling under enforce with zero
/// decode-check refusals. The shared `TCG_NO_DECODE_CHECK` triage opt-out
/// is honored.
pub fn a64_decode_check_mode() -> crate::decode_check::DecodeCheckMode {
    use crate::decode_check::DecodeCheckMode;
    static MODE: std::sync::OnceLock<DecodeCheckMode> = std::sync::OnceLock::new();
    *MODE.get_or_init(|| {
        if std::env::var_os("TCG_NO_DECODE_CHECK").is_some() {
            return DecodeCheckMode::Off;
        }
        match std::env::var("TCG_DECODE_CHECK_A64").ok().as_deref() {
            Some("off") | Some("0") | Some("false") => DecodeCheckMode::Off,
            Some("warn") => DecodeCheckMode::Warn,
            // DEFAULT-ON: any unset / unrecognized value enforces.
            _ => DecodeCheckMode::Enforce,
        }
    })
}

/// The aarch64 [`DecodeCheck`] implementation (slice 1).
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

        use AArch64Opcode as Op;
        match intent.opcode {
            // ---- Move wide -------------------------------------------------
            Op::MovI | Op::Movz | Op::Movn | Op::Movk => {
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
                    Op::MovI | Op::Movz => 0b10,
                    Op::Movn => 0b00,
                    Op::Movk => 0b11,
                    _ => unreachable!(),
                };
                expect_field!("move-wide opc", opc, want_opc);
                expect_field!("move-wide sf", sf, intent_sf(intent, 0));
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
                        "intent {:?} but the word does not decode as add/sub-immediate",
                        intent.opcode
                    ));
                };
                let want_op = match intent.opcode {
                    Op::AddRI | Op::AddRIShift12 => 0,
                    Op::SubRI => 1,
                    _ => unreachable!(),
                };
                let want_sh = u32::from(matches!(intent.opcode, Op::AddRIShift12));
                expect_field!("add/sub-imm op", op, want_op);
                expect_field!("add/sub-imm S", s, 0);
                expect_field!("add/sub-imm sh", sh, want_sh);
                expect_field!("add/sub-imm sf", sf, intent_sf(intent, 0));
                let (Some(rd_want), Some(rn_want)) = (intent_reg(intent, 0), intent_reg(intent, 1))
                else {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice1: non-register add/sub-imm operand",
                    );
                };
                expect_field!("add/sub-imm Rd", rd, rd_want);
                expect_field!("add/sub-imm Rn", rn, rn_want);
                let Some(imm_want) = intent_imm(intent, 2) else {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice1: non-imm add/sub-imm operand",
                    );
                };
                expect_field!("add/sub-imm imm12", i64::from(imm12), imm_want);
                DecodeCheckOutcome::Match
            }

            // ---- B / BL ----------------------------------------------------
            Op::B | Op::TailCall | Op::Bl => {
                let Some(A64Decoded::BranchImm { link, imm26 }) = decoded else {
                    return mismatch(format!(
                        "intent {:?} but the word does not decode as B/BL",
                        intent.opcode
                    ));
                };
                let want_link = matches!(intent.opcode, Op::Bl);
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
            Op::Br | Op::Blr | Op::Ret => {
                let Some(A64Decoded::BranchReg { opc, rn }) = decoded else {
                    return mismatch(format!(
                        "intent {:?} but the word does not decode as a register branch",
                        intent.opcode
                    ));
                };
                let want_opc = match intent.opcode {
                    Op::Br => 0b0000,
                    Op::Blr => 0b0001,
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

            // ---- Load/store register (GPR, imm offset) --------------------
            Op::LdrRI | Op::StrRI => {
                if !intent_is_gpr(intent, 0) {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice4: FP/SIMD load/store not yet decoded",
                    );
                }
                let Some(rt_want) = intent_reg(intent, 0) else {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice4: non-register load/store transfer operand",
                    );
                };
                let Some((rn_want, offset)) = intent_base_offset(intent, 1, 2) else {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice4: unmodeled load/store address operand",
                    );
                };
                let is_load = matches!(intent.opcode, Op::LdrRI);
                let want_opc = if is_load { 0b01 } else { 0b00 };
                let sf = intent_sf(intent, 0);
                let (want_size, scale) = if sf == 1 {
                    (0b11u32, 8i64)
                } else {
                    (0b10u32, 4i64)
                };
                // The encoder picks UI (scaled, non-negative) or unscaled
                // (LDUR/STUR) from the byte offset — mirror that choice and
                // demand the matching form.
                let scaled_ui = offset >= 0 && offset % scale == 0 && (offset / scale) <= 0xFFF;
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
                    expect_field!("load/store-ui V", v, 0);
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
                    expect_field!("load/store-unscaled V", v, 0);
                    expect_field!("load/store-unscaled size", size, want_size);
                    expect_field!("load/store-unscaled opc", opc, want_opc);
                    expect_field!("load/store-unscaled Rt", rt, rt_want);
                    expect_field!("load/store-unscaled Rn", rn, rn_want);
                    expect_field!("load/store-unscaled imm9", i64::from(imm9), offset);
                    DecodeCheckOutcome::Match
                }
            }

            // ---- Register-move aliases -------------------------------------
            // MOVXrr/MOVWrr encode as ORR Rd, XZR, Rm — or ADD Rd, SP, #0 for
            // an SP source. Uxtw is the 32-bit register move (ORR Wd, WZR,
            // Wn: writing a W register zero-extends, which IS the uxtw).
            Op::MOVXrr | Op::MOVWrr | Op::MovR | Op::Uxtw => {
                let sp_source = matches!(
                    intent.operands.get(1),
                    Some(MachOperand::Special(SpecialReg::SP))
                );
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
                if sp_source {
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
                            "intent {:?} (SP source) but the word does not decode as                              ADD Rd, SP, #0",
                            intent.opcode
                        ));
                    };
                    expect_field!("mov-from-sp op", op, 0);
                    expect_field!("mov-from-sp S", s, 0);
                    expect_field!("mov-from-sp sh", sh, 0);
                    expect_field!("mov-from-sp imm12", imm12, 0);
                    expect_field!("mov-from-sp Rn", rn, 31);
                    expect_field!("mov-from-sp sf", sf, want_sf);
                    expect_field!("mov-from-sp Rd", rd, rd_want);
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
            Op::CmpRR => {
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
                expect_field!("cmp-rr sf", sf, intent_sf(intent, 0));
                let (Some(rn_want), Some(rm_want)) = (intent_reg(intent, 0), intent_reg(intent, 1))
                else {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice5: non-register compare operand",
                    );
                };
                expect_field!("cmp-rr Rn", rn, rn_want);
                expect_field!("cmp-rr Rm", rm, rm_want);
                DecodeCheckOutcome::Match
            }

            Op::CmpRI => {
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
                expect_field!("cmp-ri sf", sf, intent_sf(intent, 0));
                let Some(rn_want) = intent_reg(intent, 0) else {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice5: non-register compare operand",
                    );
                };
                expect_field!("cmp-ri Rn", rn, rn_want);
                let Some(imm_want) = intent_imm(intent, 1) else {
                    return DecodeCheckOutcome::Allowlisted("a64-slice5: non-imm compare operand");
                };
                expect_field!("cmp-ri imm12", i64::from(imm12), imm_want);
                DecodeCheckOutcome::Match
            }

            // ---- Conditional select family ---------------------------------
            // CSet Rd, cond == CSINC Rd, XZR, XZR, invert(cond).
            Op::CSet => {
                let Some(A64Decoded::CondSelect {
                    sf,
                    op,
                    rm,
                    cond,
                    op2,
                    rn,
                    rd,
                }) = decoded
                else {
                    return mismatch(
                        "intent CSet but the word does not decode as conditional select"
                            .to_string(),
                    );
                };
                expect_field!("cset op", op, 0);
                expect_field!("cset op2", op2, 0b01);
                expect_field!("cset Rn", rn, 31);
                expect_field!("cset Rm", rm, 31);
                expect_field!("cset sf", sf, intent_sf(intent, 0));
                let Some(rd_want) = intent_reg(intent, 0) else {
                    return DecodeCheckOutcome::Allowlisted("a64-slice5: non-register CSet dst");
                };
                expect_field!("cset Rd", rd, rd_want);
                let Some(c) = intent_imm(intent, 1) else {
                    return DecodeCheckOutcome::Allowlisted("a64-slice5: non-imm CSet cond");
                };
                // The encoder inverts the condition (CSINC semantics).
                expect_field!("cset cond", i64::from(cond), (c & 0xF) ^ 1);
                DecodeCheckOutcome::Match
            }

            Op::Csel => {
                let Some(A64Decoded::CondSelect {
                    sf,
                    op,
                    rm,
                    cond,
                    op2,
                    rn,
                    rd,
                }) = decoded
                else {
                    return mismatch(
                        "intent Csel but the word does not decode as conditional select"
                            .to_string(),
                    );
                };
                expect_field!("csel op", op, 0);
                expect_field!("csel op2", op2, 0b00);
                expect_field!("csel sf", sf, intent_sf(intent, 0));
                let (Some(rd_want), Some(rn_want), Some(rm_want)) = (
                    intent_reg(intent, 0),
                    intent_reg(intent, 1),
                    intent_reg(intent, 2),
                ) else {
                    return DecodeCheckOutcome::Allowlisted(
                        "a64-slice5: non-register Csel operand",
                    );
                };
                expect_field!("csel Rd", rd, rd_want);
                expect_field!("csel Rn", rn, rn_want);
                expect_field!("csel Rm", rm, rm_want);
                let Some(c) = intent_imm(intent, 3) else {
                    return DecodeCheckOutcome::Allowlisted("a64-slice5: non-imm Csel cond");
                };
                expect_field!("csel cond", i64::from(cond), c & 0xF);
                DecodeCheckOutcome::Match
            }

            // ---- B.cond ----------------------------------------------------
            Op::BCond => {
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
                let Some(shift) = intent_imm(intent, 2) else {
                    return DecodeCheckOutcome::Allowlisted("a64-slice6: non-imm shift amount");
                };
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

            // ---- Everything else: named allowlist, shrinks per slice. -----
            _ => DecodeCheckOutcome::Allowlisted("a64-slice1: format family not yet decoded"),
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
    /// sf bit instead follows the mismatched allocated-register view.
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
                e.message.contains("reg-move sf"),
                "width mismatch must retain the sf diagnostic, got: {}",
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
                e.message.contains("reg-move sf"),
                "width mismatch must retain the sf diagnostic, got: {}",
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

    /// Uncovered families are counted allowlist entries, never silent skips
    /// and never spurious mismatches.
    #[test]
    fn slice1_uncovered_family_is_allowlisted() {
        let inst = mk(AArch64Opcode::Smulh, vec![preg64(0), preg64(1), preg64(2)]);
        let w = encode_instruction(&inst).expect("encode");
        match A64DecodeCheck.check_one(&inst, &w.to_le_bytes(), None) {
            DecodeCheckOutcome::Allowlisted(_) => {}
            other => panic!("expected Allowlisted, got {other:?}"),
        }
    }
}
