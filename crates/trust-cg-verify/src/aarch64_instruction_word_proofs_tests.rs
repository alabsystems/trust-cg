// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Tests for the instruction-derived obligations: the re-derived words against
//! assembler words (clang, and GNU as for the sign-extending, writeback and
//! register-offset scalar forms), the decision each admitted form reaches, the
//! negative controls every family must refute, the single-bit corruption
//! sweep, and the shapes that get no obligation. Testing evidence about the
//! encoder, decoder and semantics here, not a proof of them.

use super::*;
use trust_cg_ir::regs::{PReg, VReg};
use trust_cg_ir::{BlockId, RegClass};

fn x(n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(n))
}
fn w(n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(32 + n))
}
fn sp() -> MachOperand {
    MachOperand::Special(SpecialReg::SP)
}
fn xzr() -> MachOperand {
    MachOperand::Special(SpecialReg::XZR)
}
fn imm(value: i64) -> MachOperand {
    MachOperand::Imm(value)
}
fn mem(base: u16, offset: i64) -> MachOperand {
    MachOperand::MemOp {
        base: PReg::new(base),
        offset,
    }
}
fn inst(opcode: O, operands: Vec<MachOperand>) -> MachInst {
    MachInst::new(opcode, operands)
}
fn config() -> VerificationConfig {
    VerificationConfig::default()
}

/// Words assembled by clang (`clang -c -target arm64-apple-macos`, read back
/// with `otool -tvj`) for the listed instructions. Branch offsets are in
/// words. The last column is the decision the obligation must reach.
fn assembler_rows() -> Vec<(MachInst, u32, &'static str)> {
    let exact = "exact";
    let sampled = "statistical";
    let complete = "exhaustive";
    vec![
        (inst(O::Movz, vec![x(3), imm(0x1234)]), 0xd282_4683, exact),
        (inst(O::Movz, vec![w(4), imm(0xffff)]), 0x529f_ffe4, exact),
        (inst(O::MOVZXi, vec![x(3), imm(0x1234)]), 0xd282_4683, exact),
        (inst(O::MovI, vec![w(4), imm(0xffff)]), 0x529f_ffe4, exact),
        (inst(O::Movn, vec![x(5), imm(0)]), 0x9280_0005, exact),
        (inst(O::Movn, vec![w(6), imm(7)]), 0x1280_00e6, exact),
        (
            inst(O::Movk, vec![x(7), imm(0xbeef), imm(16)]),
            0xf2b7_dde7,
            exact,
        ),
        (
            inst(O::Movk, vec![x(8), imm(1), imm(48)]),
            0xf2e0_0028,
            exact,
        ),
        (
            inst(O::Movk, vec![w(9), imm(2), imm(16)]),
            0x72a0_0049,
            exact,
        ),
        (inst(O::Movk, vec![x(10), imm(0xabcd)]), 0xf295_79aa, exact),
        (inst(O::MovR, vec![x(1), x(2)]), 0xaa02_03e1, exact),
        (inst(O::MovR, vec![w(3), w(4)]), 0x2a04_03e3, exact),
        (inst(O::MovR, vec![x(5), sp()]), 0x9100_03e5, exact),
        (inst(O::MovR, vec![x(6), x(31)]), 0x9100_03e6, exact),
        (inst(O::MovR, vec![x(31), x(6)]), 0x9100_00df, exact),
        (inst(O::MovR, vec![x(7), xzr()]), 0xaa1f_03e7, exact),
        (inst(O::MOVXrr, vec![x(1), x(2)]), 0xaa02_03e1, exact),
        // The typed copy's opcode, not the register view, fixes the width.
        (inst(O::MOVWrr, vec![x(3), x(4)]), 0x2a04_03e3, exact),
        (
            inst(O::AddRI, vec![x(29), sp(), imm(16)]),
            0x9100_43fd,
            exact,
        ),
        (
            inst(O::SubRI, vec![sp(), sp(), imm(48)]),
            0xd100_c3ff,
            exact,
        ),
        (
            inst(O::AddRI, vec![w(1), w(2), imm(4095)]),
            0x113f_fc41,
            exact,
        ),
        (inst(O::SubRI, vec![x(3), x(4), imm(1)]), 0xd100_0483, exact),
        (inst(O::CmpRI, vec![x(1), imm(0)]), 0xf100_003f, sampled),
        (inst(O::CmpRI, vec![w(2), imm(64)]), 0x7101_005f, sampled),
        (inst(O::CMPXri, vec![sp(), imm(16)]), 0xf100_43ff, sampled),
        (inst(O::CmpRR, vec![x(3), x(4)]), 0xeb04_007f, sampled),
        (inst(O::CMPWrr, vec![w(5), w(6)]), 0x6b06_00bf, sampled),
        (
            inst(O::AddRRShift, vec![x(0), x(1), x(2), imm(3)]),
            0x8b02_0c20,
            exact,
        ),
        (
            inst(O::SubRRShift, vec![x(6), x(7), x(8), imm(1)]),
            0xcb08_04e6,
            exact,
        ),
        (
            inst(O::AddRRShiftLsr, vec![x(9), x(10), x(11), imm(63)]),
            0x8b4b_fd49,
            exact,
        ),
        (
            inst(O::AddRRShiftLsr, vec![w(12), w(13), w(14), imm(1)]),
            0x0b4e_05ac,
            exact,
        ),
        (
            inst(O::EorRRShift, vec![x(0), x(1), x(2), imm(40)]),
            0xcac2_a020,
            exact,
        ),
        (inst(O::Umulh, vec![x(3), x(4), x(5)]), 0x9bc5_7c83, exact),
        (inst(O::LdrRI, vec![x(1), mem(31, 16)]), 0xf940_0be1, exact),
        (
            inst(O::LdrRI, vec![w(2), x(3), imm(4092)]),
            0xb94f_fc62,
            exact,
        ),
        (inst(O::LdrRI, vec![x(4), mem(29, -8)]), 0xf85f_83a4, exact),
        (inst(O::StrRI, vec![x(5), mem(31, 8)]), 0xf900_07e5, exact),
        (
            inst(O::StrRI, vec![w(6), x(7), imm(-4)]),
            0xb81f_c0e6,
            exact,
        ),
        (
            inst(O::StrbRI, vec![w(8), x(9), imm(3)]),
            0x3900_0d28,
            exact,
        ),
        (
            inst(O::LdrbRI, vec![w(10), x(11), imm(4095)]),
            0x397f_fd6a,
            exact,
        ),
        (
            inst(O::LdrhRI, vec![w(12), x(13), imm(2)]),
            0x7940_05ac,
            exact,
        ),
        (
            inst(O::StrhRI, vec![w(14), x(15), imm(-2)]),
            0x781f_e1ee,
            exact,
        ),
        (inst(O::LdrRI, vec![x(16), x(17)]), 0xf940_0230, exact),
        (
            inst(O::LdrRI, vec![w(18), x(19), imm(1)]),
            0xb840_1272,
            exact,
        ),
        (inst(O::B, vec![imm(2)]), 0x1400_0002, exact),
        (inst(O::Bl, vec![imm(-1)]), 0x97ff_ffff, exact),
        (inst(O::BCond, vec![imm(1), imm(3)]), 0x5400_0061, exact),
        (
            inst(O::BCond, vec![imm(13), imm(-2)]),
            0x54ff_ffcd,
            complete,
        ),
    ]
    .into_iter()
    .chain(scalar_memory_rows())
    .collect()
}

/// Words assembled by GNU as 2.42 (`as` on aarch64 Linux, read back with
/// `objdump -d`) for the sign-extending, writeback and register-offset scalar
/// forms. A register-offset index scaled by a nonzero amount is stated as a
/// shift on the intent side and as Arm's `ExtendReg` (low bits, appended
/// zeros, extension) on the word side, so those two terms are equal but not
/// identical, and their address is decided by the evaluator.
fn scalar_memory_rows() -> Vec<(MachInst, u32, &'static str)> {
    let exact = "exact";
    let sampled = "statistical";
    vec![
        // ldrsb x1, [x2, #5] / ldrsb w3, [sp, #4095] / ldursb x4, [x5, #-1]
        (
            inst(O::LdrsbRI, vec![x(1), x(2), imm(5)]),
            0x3980_1441,
            exact,
        ),
        (
            inst(O::LdrsbRI, vec![w(3), sp(), imm(4095)]),
            0x39ff_ffe3,
            exact,
        ),
        (
            inst(O::LdrsbRI, vec![x(4), x(5), imm(-1)]),
            0x389f_f0a4,
            exact,
        ),
        // ldrsh w6, [x7, #2] / ldrsh x8, [x9, #8190] / ldursh w10, [x11, #-3]
        (
            inst(O::LdrshRI, vec![w(6), x(7), imm(2)]),
            0x79c0_04e6,
            exact,
        ),
        (
            inst(O::LdrshRI, vec![x(8), x(9), imm(8190)]),
            0x79bf_fd28,
            exact,
        ),
        (
            inst(O::LdrshRI, vec![w(10), x(11), imm(-3)]),
            0x78df_d16a,
            exact,
        ),
        // str x0, [sp, #-16]! / ldr x1, [sp], #16 / ldr w2, [x3, #255]!
        (
            inst(O::StrPreIndex, vec![x(0), sp(), imm(-16)]),
            0xf81f_0fe0,
            exact,
        ),
        (
            inst(O::LdrPostIndex, vec![x(1), sp(), imm(16)]),
            0xf841_07e1,
            exact,
        ),
        (
            inst(O::LdrPreIndex, vec![w(2), x(3), imm(255)]),
            0xb84f_fc62,
            exact,
        ),
        // str w4, [x5], #-256 / str xzr, [x6, #8]! / ldr x7, [x8], #0
        (
            inst(O::StrPostIndex, vec![w(4), x(5), imm(-256)]),
            0xb810_04a4,
            exact,
        ),
        (
            inst(O::StrPreIndex, vec![xzr(), x(6), imm(8)]),
            0xf800_8cdf,
            exact,
        ),
        (
            inst(O::LdrPostIndex, vec![x(7), x(8), imm(0)]),
            0xf840_0507,
            exact,
        ),
        // ldr x0, [x1, x2] / ldr x3, [x4, x5, lsl #3]
        (inst(O::LdrRO, vec![x(0), x(1), x(2)]), 0xf862_6820, exact),
        (
            inst(O::LdrRO, vec![x(3), x(4), x(5), imm(7)]),
            0xf865_7883,
            sampled,
        ),
        // ldr w6, [sp, w7, uxtw] / ldr w8, [x9, w10, sxtw #2]
        (
            inst(O::LdrRO, vec![w(6), sp(), w(7), imm(4)]),
            0xb867_4be6,
            exact,
        ),
        (
            inst(O::LdrRO, vec![w(8), x(9), w(10), imm(13)]),
            0xb86a_d928,
            sampled,
        ),
        // str x11, [x12, x13, sxtx] / str w14, [x15, x16, sxtx #2] /
        // str x9, [sp, xzr]
        (
            inst(O::StrRO, vec![x(11), x(12), x(13), imm(14)]),
            0xf82d_e98b,
            exact,
        ),
        (
            inst(O::StrRO, vec![w(14), x(15), x(16), imm(15)]),
            0xb830_f9ee,
            sampled,
        ),
        (inst(O::StrRO, vec![x(9), sp(), xzr()]), 0xf83f_6be9, exact),
        // ldrb w17, [x18, x19] / ldrb w20, [x21, w22, uxtw] /
        // ldrb w23, [x24, x25, lsl #0] / ldrh w26, [x27, x28, lsl #1]
        (
            inst(O::LdrbRO, vec![w(17), x(18), x(19)]),
            0x3873_6a51,
            exact,
        ),
        (
            inst(O::LdrbRO, vec![w(20), x(21), w(22), imm(4)]),
            0x3876_4ab4,
            exact,
        ),
        (
            inst(O::LdrbRO, vec![w(23), x(24), x(25), imm(7)]),
            0x3879_7b17,
            exact,
        ),
        (
            inst(O::LdrhRO, vec![w(26), x(27), x(28), imm(7)]),
            0x787c_7b7a,
            sampled,
        ),
        // strb w0, [x1, w2, sxtw] / strh w3, [x4, x5] /
        // ldrsw x6, [x7, x8, lsl #2]
        (
            inst(O::StrbRO, vec![w(0), x(1), w(2), imm(12)]),
            0x3822_c820,
            exact,
        ),
        (inst(O::StrhRO, vec![w(3), x(4), x(5)]), 0x7825_6883, exact),
        (
            inst(O::LdrswRO, vec![x(6), x(7), x(8)]),
            0xb8a8_78e6,
            sampled,
        ),
    ]
}

fn decision_name(outcome: &Outcome) -> &'static str {
    match outcome {
        Outcome::Holds(Decision::Exact) => "exact",
        Outcome::Holds(Decision::Evaluated(VerificationStrength::Exhaustive)) => "exhaustive",
        Outcome::Holds(Decision::Evaluated(VerificationStrength::Statistical { .. })) => {
            "statistical"
        }
        Outcome::Holds(Decision::Evaluated(VerificationStrength::Formal)) => "formal",
        Outcome::Refuted(_) => "refuted",
        Outcome::Undecided(_) => "undecided",
    }
}

#[test]
fn re_derived_words_are_the_assembled_words_and_hold() {
    for (inst, word, decision) in assembler_rows() {
        let derived = instruction_word(&inst).unwrap_or_else(|| panic!("{inst:?} not admitted"));
        assert_eq!(
            derived,
            InstructionWord { word, hole_mask: 0 },
            "{inst:?}: re-derived {:#010x}, assembled {word:#010x}",
            derived.word
        );
        assert_eq!(check_emitted_instruction_word(&inst, word), Some(Ok(())));
        let verdict = instruction_word_verdict(&inst, &config()).expect("admitted");
        assert_eq!(
            decision_name(&verdict.outcome),
            decision,
            "{inst:?}: {:?}",
            verdict.outcome
        );
        assert!(!verdict.locations.is_empty(), "{inst:?}");
        assert!(
            verdict
                .locations
                .iter()
                .all(|(_, obligation)| obligation.is_reconstructed()),
            "{inst:?}"
        );
    }
}

/// The census's registry-class opcodes this module covers, all of them.
#[test]
fn every_listed_opcode_has_an_admitted_row() {
    let rows = assembler_rows();
    let mut missing: Vec<O> = INSTRUCTION_WORD_OPCODES
        .iter()
        .copied()
        .filter(|opcode| !rows.iter().any(|(inst, _, _)| inst.opcode == *opcode))
        .collect();
    // Aliases and symbolic-target forms are covered by the tests below.
    missing.retain(|opcode| {
        !matches!(
            opcode,
            O::MOVZWi | O::CMPWri | O::CMPXrr | O::TailCall | O::BL | O::Bcc
        )
    });
    assert_eq!(missing, Vec::<O>::new());
    for (opcode, operands) in [
        (O::MOVZWi, vec![w(1), imm(5)]),
        (O::CMPWri, vec![w(1), imm(5)]),
        (O::CMPXrr, vec![x(1), x(2)]),
        (O::TailCall, vec![MachOperand::Symbol("callee".into())]),
        (O::BL, vec![MachOperand::Symbol("callee".into())]),
        (O::Bcc, vec![imm(0), MachOperand::Block(BlockId(1))]),
    ] {
        let inst = inst(opcode, operands);
        let verdict = instruction_word_verdict(&inst, &config()).expect("admitted");
        assert!(matches!(verdict.outcome, Outcome::Holds(_)), "{inst:?}");
    }
}

#[test]
fn symbolic_targets_leave_the_displacement_a_hole() {
    for (inst, word, mask) in [
        (
            inst(O::Bl, vec![MachOperand::Symbol("callee".into()), x(0)]),
            0x9400_0000,
            IMM26_MASK,
        ),
        (
            inst(
                O::TailCall,
                vec![MachOperand::ExactModuleSymbol("f".into())],
            ),
            0x1400_0000,
            IMM26_MASK,
        ),
        (
            inst(O::B, vec![MachOperand::Block(BlockId(3))]),
            0x1400_0000,
            IMM26_MASK,
        ),
        (
            inst(O::BCond, vec![imm(8), MachOperand::Block(BlockId(3))]),
            0x5400_0008,
            IMM19_MASK,
        ),
    ] {
        assert_eq!(
            instruction_word(&inst),
            Some(InstructionWord {
                word,
                hole_mask: mask
            }),
            "{inst:?}"
        );
        // A fixup overwrites the hole: whatever the emitted placeholder
        // holds there, the binding and the obligation are unchanged.
        let patched = word | (0x0001_2340 & mask);
        assert_eq!(check_emitted_instruction_word(&inst, patched), Some(Ok(())));
        let verdict = instruction_word_verdict_for(&inst, patched, &config()).expect("admitted");
        assert!(matches!(verdict.outcome, Outcome::Holds(_)), "{inst:?}");
        // Outside the hole, one flipped bit is a binding mismatch.
        assert!(
            matches!(
                check_emitted_instruction_word(&inst, word ^ 0x8000_0000),
                Some(Err(_))
            ),
            "{inst:?}"
        );
    }
}

/// Every instruction-selection condition code (EQ..LE, 0..=13) is the Arm
/// `cond` field of the same meaning: the word's `ConditionHolds` and the
/// stated meaning agree on all 16 NZCV values, and the inverse condition
/// refutes.
#[test]
fn every_condition_code_encodes_its_meaning_and_its_inverse_refutes() {
    for cc in 0..=13i64 {
        let branch = inst(O::BCond, vec![imm(cc), MachOperand::Block(BlockId(1))]);
        let word = instruction_word(&branch).expect("admitted");
        assert_eq!(word.word & 0xF, cc as u32);
        let verdict = instruction_word_verdict(&branch, &config()).expect("admitted");
        assert!(
            matches!(
                verdict.outcome,
                Outcome::Holds(Decision::Exact)
                    | Outcome::Holds(Decision::Evaluated(VerificationStrength::Exhaustive))
            ),
            "cc {cc}: {:?}",
            verdict.outcome
        );
        let inverted =
            instruction_word_verdict_for(&branch, word.word ^ 1, &config()).expect("admitted");
        assert!(
            matches!(inverted.outcome, Outcome::Refuted(_)),
            "cc {cc} inverted: {:?}",
            inverted.outcome
        );
    }
}

/// Named field mutations of each family's word: every one must REFUTE (not
/// merely fail to hold).
#[test]
fn negative_controls_refute() {
    let set = |word: u32, hi: u32, lo: u32, value: u32| {
        let mask = ((1u64 << (hi - lo + 1)) - 1) as u32;
        (word & !(mask << lo)) | ((value & mask) << lo)
    };
    let controls: Vec<(MachInst, &str, u32)> = vec![
        // Move wide.
        (
            inst(O::Movz, vec![x(3), imm(0x1234)]),
            "imm16",
            0xd282_4683 ^ (1 << 5),
        ),
        (
            inst(O::Movz, vec![x(3), imm(0x1234)]),
            "hw 0 -> 1",
            set(0xd282_4683, 22, 21, 1),
        ),
        (
            inst(O::Movz, vec![x(3), imm(0x1234)]),
            "MOVZ -> MOVN",
            set(0xd282_4683, 30, 29, 0),
        ),
        (
            inst(O::Movz, vec![x(3), imm(0x1234)]),
            "MOVZ -> MOVK",
            set(0xd282_4683, 30, 29, 3),
        ),
        (
            inst(O::Movz, vec![x(3), imm(0x1234)]),
            "Rd",
            set(0xd282_4683, 4, 0, 4),
        ),
        (
            inst(O::Movn, vec![x(5), imm(0)]),
            "sf",
            0x9280_0005 ^ (1 << 31),
        ),
        (
            inst(O::Movk, vec![x(7), imm(0xbeef), imm(16)]),
            "hw 1 -> 2",
            set(0xf2b7_dde7, 22, 21, 2),
        ),
        (
            inst(O::Movk, vec![x(7), imm(0xbeef), imm(16)]),
            "MOVK -> MOVZ",
            set(0xf2b7_dde7, 30, 29, 2),
        ),
        // Register copies.
        (
            inst(O::MovR, vec![x(1), x(2)]),
            "Rm",
            set(0xaa02_03e1, 20, 16, 3),
        ),
        (
            inst(O::MovR, vec![x(1), x(2)]),
            "Rd",
            set(0xaa02_03e1, 4, 0, 5),
        ),
        (
            inst(O::MovR, vec![x(1), x(2)]),
            "sf",
            0xaa02_03e1 ^ (1 << 31),
        ),
        (
            inst(O::MovR, vec![x(1), x(2)]),
            "ORR -> AND",
            set(0xaa02_03e1, 30, 29, 0),
        ),
        (
            inst(O::MovR, vec![x(1), x(2)]),
            "N (ORN)",
            0xaa02_03e1 ^ (1 << 21),
        ),
        (
            inst(O::MovR, vec![x(5), sp()]),
            "Rn SP -> X30",
            set(0x9100_03e5, 9, 5, 30),
        ),
        // Add/subtract immediate.
        (
            inst(O::AddRI, vec![x(29), sp(), imm(16)]),
            "ADD -> SUB",
            0x9100_43fd ^ (1 << 30),
        ),
        (
            inst(O::AddRI, vec![x(29), sp(), imm(16)]),
            "imm12",
            0x9100_43fd ^ (1 << 10),
        ),
        (
            inst(O::AddRI, vec![x(29), sp(), imm(16)]),
            "sh",
            0x9100_43fd ^ (1 << 22),
        ),
        (
            inst(O::AddRI, vec![x(29), sp(), imm(16)]),
            "S (ADDS)",
            0x9100_43fd ^ (1 << 29),
        ),
        (
            inst(O::SubRI, vec![sp(), sp(), imm(48)]),
            "Rd SP -> X30",
            set(0xd100_c3ff, 4, 0, 30),
        ),
        // Compare.
        (
            inst(O::CmpRI, vec![x(1), imm(0)]),
            "S clear (SUB SP)",
            0xf100_003f ^ (1 << 29),
        ),
        (
            inst(O::CmpRI, vec![w(2), imm(64)]),
            "imm12",
            0x7101_005f ^ (1 << 11),
        ),
        (
            inst(O::CmpRI, vec![w(2), imm(64)]),
            "CMP -> CMN",
            0x7101_005f ^ (1 << 30),
        ),
        (
            inst(O::CmpRI, vec![w(2), imm(64)]),
            "sf",
            0x7101_005f ^ (1 << 31),
        ),
        (inst(O::CmpRR, vec![x(3), x(4)]), "Rn/Rm swap", 0xeb03_009f),
        (
            inst(O::CmpRR, vec![x(3), x(4)]),
            "Rd",
            set(0xeb04_007f, 4, 0, 3),
        ),
        // Shifted register.
        (
            inst(O::AddRRShift, vec![x(0), x(1), x(2), imm(3)]),
            "LSL -> LSR",
            set(0x8b02_0c20, 23, 22, 1),
        ),
        (
            inst(O::AddRRShift, vec![x(0), x(1), x(2), imm(3)]),
            "amount",
            set(0x8b02_0c20, 15, 10, 4),
        ),
        (
            inst(O::SubRRShift, vec![x(6), x(7), x(8), imm(1)]),
            "SUB -> ADD",
            0xcb08_04e6 ^ (1 << 30),
        ),
        (
            inst(O::AddRRShiftLsr, vec![x(9), x(10), x(11), imm(63)]),
            "LSR -> ASR",
            set(0x8b4b_fd49, 23, 22, 2),
        ),
        (
            inst(O::EorRRShift, vec![x(0), x(1), x(2), imm(40)]),
            "ROR -> LSR",
            set(0xcac2_a020, 23, 22, 1),
        ),
        (
            inst(O::EorRRShift, vec![x(0), x(1), x(2), imm(40)]),
            "EOR -> ORR",
            set(0xcac2_a020, 30, 29, 1),
        ),
        // Multiply high.
        (
            inst(O::Umulh, vec![x(3), x(4), x(5)]),
            "Rm",
            set(0x9bc5_7c83, 20, 16, 6),
        ),
        (
            inst(O::Umulh, vec![x(3), x(4), x(5)]),
            "UMULH -> SMULH",
            set(0x9bc5_7c83, 23, 21, 2),
        ),
        // Branches.
        (inst(O::B, vec![imm(2)]), "B -> BL", 0x1400_0002 ^ (1 << 31)),
        (
            inst(O::Bl, vec![imm(-1)]),
            "BL -> B",
            0x97ff_ffff ^ (1 << 31),
        ),
        (inst(O::B, vec![imm(2)]), "imm26", 0x1400_0002 ^ 1),
        (
            inst(O::Bl, vec![MachOperand::Symbol("f".into())]),
            "BL -> B (hole)",
            0x1400_0000,
        ),
        (
            inst(O::BCond, vec![imm(1), imm(3)]),
            "NE -> EQ",
            0x5400_0060,
        ),
        (
            inst(O::BCond, vec![imm(1), imm(3)]),
            "imm19",
            0x5400_0061 ^ (1 << 5),
        ),
        (
            inst(O::BCond, vec![imm(1), imm(3)]),
            "B.cond -> B",
            0x1400_0003,
        ),
        // Memory.
        (
            inst(O::LdrRI, vec![x(1), mem(31, 16)]),
            "load -> store",
            0xf940_0be1 ^ (1 << 22),
        ),
        (
            inst(O::LdrRI, vec![x(1), mem(31, 16)]),
            "size 8 -> 4",
            set(0xf940_0be1, 31, 30, 2),
        ),
        (
            inst(O::LdrRI, vec![x(1), mem(31, 16)]),
            "imm12",
            0xf940_0be1 ^ (1 << 10),
        ),
        (
            inst(O::LdrRI, vec![x(1), mem(31, 16)]),
            "Rn",
            set(0xf940_0be1, 9, 5, 2),
        ),
        (
            inst(O::LdrRI, vec![x(1), mem(31, 16)]),
            "Rt",
            set(0xf940_0be1, 4, 0, 2),
        ),
        (
            inst(O::LdrRI, vec![w(2), x(3), imm(4092)]),
            "LDR -> LDRSW",
            set(0xb94f_fc62, 23, 22, 2),
        ),
        (
            inst(O::LdrRI, vec![x(1), mem(31, 16)]),
            "unsigned -> unscaled",
            0xf940_0be1 ^ (1 << 24),
        ),
        (
            inst(O::LdrRI, vec![x(4), mem(29, -8)]),
            "imm9",
            0xf85f_83a4 ^ (1 << 12),
        ),
        (
            inst(O::StrbRI, vec![w(8), x(9), imm(3)]),
            "size 1 -> 2",
            set(0x3900_0d28, 31, 30, 1),
        ),
        (
            inst(O::StrbRI, vec![w(8), x(9), imm(3)]),
            "Rt",
            set(0x3900_0d28, 4, 0, 9),
        ),
        (
            inst(O::StrRI, vec![x(5), mem(31, 8)]),
            "SIMD&FP (V)",
            0xf900_07e5 ^ (1 << 26),
        ),
        // Sign-extending immediate loads.
        (
            inst(O::LdrsbRI, vec![x(1), x(2), imm(5)]),
            "LDRSB X -> LDRSB W",
            set(0x3980_1441, 23, 22, 0b11),
        ),
        (
            inst(O::LdrsbRI, vec![x(1), x(2), imm(5)]),
            "LDRSB -> LDRB",
            set(0x3980_1441, 23, 22, 0b01),
        ),
        (
            inst(O::LdrshRI, vec![w(6), x(7), imm(2)]),
            "LDRSH W -> LDRSH X",
            set(0x79c0_04e6, 23, 22, 0b10),
        ),
        (
            inst(O::LdrshRI, vec![w(6), x(7), imm(2)]),
            "LDRSH -> LDRSB",
            set(0x79c0_04e6, 31, 30, 0),
        ),
        // Writeback.
        (
            inst(O::StrPreIndex, vec![x(0), sp(), imm(-16)]),
            "pre -> post",
            0xf81f_0fe0 ^ (1 << 11),
        ),
        (
            inst(O::StrPreIndex, vec![x(0), sp(), imm(-16)]),
            "writeback dropped (STUR)",
            set(0xf81f_0fe0, 11, 10, 0b00),
        ),
        (
            inst(O::StrPreIndex, vec![x(0), sp(), imm(-16)]),
            "imm9",
            0xf81f_0fe0 ^ (1 << 12),
        ),
        (
            inst(O::LdrPostIndex, vec![x(1), sp(), imm(16)]),
            "post -> pre",
            0xf841_07e1 ^ (1 << 11),
        ),
        (
            inst(O::LdrPreIndex, vec![w(2), x(3), imm(255)]),
            "Rn := Rt (constrained unpredictable)",
            set(0xb84f_fc62, 9, 5, 2),
        ),
        (
            inst(O::LdrPreIndex, vec![w(2), x(3), imm(255)]),
            "Rn",
            set(0xb84f_fc62, 9, 5, 4),
        ),
        (
            inst(O::StrPostIndex, vec![w(4), x(5), imm(-256)]),
            "size 4 -> 8",
            set(0xb810_04a4, 31, 30, 3),
        ),
        // Register offset.
        (
            inst(O::LdrRO, vec![w(6), sp(), w(7), imm(4)]),
            "UXTW -> SXTW",
            0xb867_4be6 ^ (1 << 15),
        ),
        (
            inst(O::LdrRO, vec![w(6), sp(), w(7), imm(4)]),
            "UXTW -> LSL",
            set(0xb867_4be6, 15, 13, 0b011),
        ),
        (
            inst(O::LdrRO, vec![w(6), sp(), w(7), imm(4)]),
            "option 000 (unallocated)",
            set(0xb867_4be6, 15, 13, 0b000),
        ),
        (
            inst(O::LdrRO, vec![x(3), x(4), x(5), imm(7)]),
            "S cleared",
            0xf865_7883 ^ (1 << 12),
        ),
        (
            inst(O::LdrRO, vec![x(3), x(4), x(5), imm(7)]),
            "Rn/Rm swap",
            0xf864_78a3,
        ),
        (
            inst(O::LdrRO, vec![x(0), x(1), x(2)]),
            "Rm",
            set(0xf862_6820, 20, 16, 3),
        ),
        (
            inst(O::LdrRO, vec![x(0), x(1), x(2)]),
            "SIMD&FP (V)",
            0xf862_6820 ^ (1 << 26),
        ),
        (
            inst(O::LdrswRO, vec![x(6), x(7), x(8)]),
            "LDRSW -> LDR W",
            set(0xb8a8_78e6, 23, 22, 0b01),
        ),
        (
            inst(O::StrbRO, vec![w(0), x(1), w(2), imm(12)]),
            "store -> load",
            0x3822_c820 ^ (1 << 22),
        ),
        (
            inst(O::LdrhRO, vec![w(26), x(27), x(28), imm(7)]),
            "size 2 -> 4",
            set(0x787c_7b7a, 31, 30, 2),
        ),
    ];
    let mut not_refuted = Vec::new();
    for (inst, what, word) in &controls {
        let verdict = instruction_word_verdict_for(inst, *word, &config()).expect("admitted");
        if !matches!(verdict.outcome, Outcome::Refuted(_)) {
            not_refuted.push(format!("{:?} {what}: {:?}", inst.opcode, verdict.outcome));
        }
    }
    assert!(not_refuted.is_empty(), "{not_refuted:#?}");
    assert_eq!(controls.len(), 72);
}

/// Every single-bit corruption of every assembled word, outside its hole,
/// either fails to hold or is one of the pinned architecturally equivalent
/// words (a flip that leaves every written location's value unchanged).
#[test]
fn single_bit_corruptions_do_not_hold_except_pinned_equivalents() {
    let mut equivalent = Vec::new();
    for (inst, word, _) in assembler_rows() {
        for bit in 0..32 {
            let corrupted = word ^ (1 << bit);
            let verdict =
                instruction_word_verdict_for(&inst, corrupted, &config()).expect("admitted");
            if matches!(verdict.outcome, Outcome::Holds(_)) {
                equivalent.push((format!("{:?} {word:#010x}", inst.opcode), bit));
            }
        }
    }
    let pinned: Vec<(String, u32)> = [
        // MOVZ of a value below 2^32 writes the same X register at either
        // width (sf).
        ("Movz 0xd2824683", 31),
        ("Movz 0x529fffe4", 31),
        ("MOVZXi 0xd2824683", 31),
        ("MovI 0x529fffe4", 31),
        // MOVN of #0 is all ones at every halfword (hw).
        ("Movn 0x92800005", 21),
        ("Movn 0x92800005", 22),
        // A register copy's shift type is irrelevant at amount 0 (bits 23:22).
        ("MovR 0xaa0203e1", 22),
        ("MovR 0xaa0203e1", 23),
        ("MovR 0x2a0403e3", 22),
        ("MovR 0x2a0403e3", 23),
        // `ADD Rd, Rn, #0` equals `SUB Rd, Rn, #0`, with either sh.
        ("MovR 0x910003e5", 22),
        ("MovR 0x910003e5", 30),
        ("MovR 0x910003e6", 22),
        ("MovR 0x910003e6", 30),
        ("MovR 0x910000df", 22),
        ("MovR 0x910000df", 30),
        // `MOV Xd, XZR` writes zero whatever its shift (imm6, type), with AND
        // for ORR, and at either width.
        ("MovR 0xaa1f03e7", 10),
        ("MovR 0xaa1f03e7", 11),
        ("MovR 0xaa1f03e7", 12),
        ("MovR 0xaa1f03e7", 13),
        ("MovR 0xaa1f03e7", 14),
        ("MovR 0xaa1f03e7", 15),
        ("MovR 0xaa1f03e7", 22),
        ("MovR 0xaa1f03e7", 23),
        ("MovR 0xaa1f03e7", 29),
        ("MovR 0xaa1f03e7", 31),
        ("MOVXrr 0xaa0203e1", 22),
        ("MOVXrr 0xaa0203e1", 23),
        ("MOVWrr 0x2a0403e3", 22),
        ("MOVWrr 0x2a0403e3", 23),
        // `CMP Rn, #0` with sh set compares with 0 << 12.
        ("CmpRI 0xf100003f", 22),
        // A compare's shift type is irrelevant at amount 0.
        ("CmpRR 0xeb04007f", 22),
        ("CmpRR 0xeb04007f", 23),
        ("CMPWrr 0x6b0600bf", 22),
        ("CMPWrr 0x6b0600bf", 23),
        // `LDR Xt, [Xn]` (unsigned offset 0) equals `LDUR Xt, [Xn, #0]`.
        ("LdrRI 0xf9400230", 24),
        // Post-index and pre-index by #0 both access Xn and leave it
        // unchanged (bit 11).
        ("LdrPostIndex 0xf8400507", 11),
        // A 64-bit index: LSL/UXTX (option 011) and SXTX (111) both take all
        // 64 bits, and sign-extending 64 bits is the identity (bit 15).
        ("LdrRO 0xf8626820", 15),
        ("LdrRO 0xf8657883", 15),
        ("StrRO 0xf82de98b", 15),
        ("StrRO 0xb830f9ee", 15),
        // The zero register as the index is zero under every extend and
        // shift: S (bit 12), UXTW (bit 13), SXTX (bit 15).
        ("StrRO 0xf83f6be9", 12),
        ("StrRO 0xf83f6be9", 13),
        ("StrRO 0xf83f6be9", 15),
        // A byte access scales by 2^0, so S (bit 12) changes nothing; a
        // 64-bit index is as above (bit 15).
        ("LdrbRO 0x38736a51", 12),
        ("LdrbRO 0x38736a51", 15),
        ("LdrbRO 0x38764ab4", 12),
        ("LdrbRO 0x38797b17", 12),
        ("LdrbRO 0x38797b17", 15),
        ("LdrhRO 0x787c7b7a", 15),
        ("StrbRO 0x3822c820", 12),
        ("StrhRO 0x78256883", 15),
        ("LdrswRO 0xb8a878e6", 15),
    ]
    .into_iter()
    .map(|(row, bit)| (row.to_string(), bit))
    .collect();
    assert_eq!(equivalent, pinned);
}

/// Shapes outside the admitted forms get no obligation, so the walk falls
/// through to its previous arm for them.
#[test]
fn unadmitted_shapes_get_no_obligation() {
    let vreg = MachOperand::VReg(VReg::new(0, RegClass::Gpr64));
    for inst in [
        inst(O::Movz, vec![vreg.clone(), imm(1)]),
        inst(O::Movz, vec![x(0), imm(1), imm(16)]),
        inst(O::Movz, vec![x(0), imm(0x1_0000)]),
        inst(O::Movz, vec![sp(), imm(1)]),
        inst(O::MovI, vec![x(0), imm(1), imm(0)]),
        inst(O::MOVZWi, vec![x(0), imm(1)]),
        inst(O::Movk, vec![w(0), imm(1), imm(32)]),
        inst(O::Movk, vec![x(0), imm(1), imm(8)]),
        inst(O::Movn, vec![x(0), imm(1), imm(16)]),
        inst(O::MovR, vec![x(0), x(1), imm(0)]),
        inst(O::MovR, vec![sp(), xzr()]),
        inst(O::MovR, vec![x(0), MachOperand::PReg(PReg::new(64))]),
        inst(O::AddRI, vec![xzr(), x(1), imm(1)]),
        inst(O::AddRI, vec![x(0), x(1), imm(4096)]),
        inst(O::AddRI, vec![x(0), x(1), x(2)]),
        inst(
            O::AddRI,
            vec![
                x(0),
                MachOperand::FrameIndex(trust_cg_ir::FrameIdx(0)),
                imm(0),
            ],
        ),
        inst(O::CmpRI, vec![xzr(), imm(1)]),
        inst(O::CMPWri, vec![x(1), imm(1)]),
        inst(O::CmpRR, vec![sp(), x(1)]),
        inst(O::CmpRR, vec![x(1), w(2)]),
        inst(O::AddRRShift, vec![x(0), sp(), x(2), imm(1)]),
        inst(O::AddRRShift, vec![x(0), x(1), x(2), imm(0)]),
        inst(O::SubRRShift, vec![w(0), w(1), w(2), imm(32)]),
        inst(O::Umulh, vec![w(0), w(1), w(2)]),
        inst(O::B, vec![MachOperand::Block(BlockId(1)), imm(0)]),
        inst(O::B, vec![imm(1 << 25)]),
        inst(O::BCond, vec![imm(14), MachOperand::Block(BlockId(1))]),
        inst(O::BCond, vec![imm(0)]),
        inst(O::LdrRI, vec![MachOperand::PReg(PReg::new(96)), mem(31, 8)]),
        inst(O::LdrRI, vec![x(0), w(1), imm(0)]),
        inst(O::LdrRI, vec![x(0), x(1), imm(1 << 16)]),
        inst(O::StrRI, vec![sp(), x(1), imm(0)]),
        inst(
            O::StrRI,
            vec![x(0), MachOperand::StackSlot(trust_cg_ir::StackSlotId(0))],
        ),
        inst(O::AddRR, vec![x(0), x(1), x(2)]),
        // Sign-extending immediate loads.
        inst(O::LdrsbRI, vec![sp(), x(1), imm(0)]),
        inst(O::LdrshRI, vec![x(0), x(1), imm(1 << 16)]),
        // Writeback: the base is the transfer register (either view), the
        // offset leaves imm9, the offset is missing, SP data, a W base.
        inst(O::LdrPreIndex, vec![x(5), x(5), imm(8)]),
        inst(O::StrPostIndex, vec![w(5), x(5), imm(8)]),
        inst(O::LdrPostIndex, vec![x(1), x(2), imm(256)]),
        inst(O::StrPreIndex, vec![x(1), x(2), imm(-257)]),
        inst(O::StrPreIndex, vec![x(1), x(2)]),
        inst(O::LdrPreIndex, vec![sp(), x(2), imm(8)]),
        inst(O::LdrPreIndex, vec![x(1), w(2), imm(8)]),
        // Register offset: a W index under a 64-bit extend, modes outside
        // {4..7, 12..15}, an SP index, a ZR base, SIMD&FP data, a fifth
        // operand.
        inst(O::LdrRO, vec![x(0), x(1), w(2)]),
        inst(O::LdrRO, vec![x(0), x(1), w(2), imm(14)]),
        inst(O::LdrRO, vec![x(0), x(1), x(2), imm(0)]),
        inst(O::LdrRO, vec![x(0), x(1), x(2), imm(8)]),
        inst(O::LdrRO, vec![x(0), x(1), x(2), imm(16)]),
        inst(O::LdrRO, vec![x(0), x(1), sp()]),
        inst(O::LdrRO, vec![x(0), xzr(), x(2)]),
        inst(O::LdrRO, vec![MachOperand::PReg(PReg::new(96)), x(1), x(2)]),
        inst(O::LdrRO, vec![x(0), x(1), x(2), imm(6), imm(0)]),
        // LDRSW writes an X register, and is emitted only as LSL #2.
        inst(O::LdrswRO, vec![w(0), x(1), x(2)]),
        inst(O::LdrswRO, vec![x(0), x(1), x(2), imm(6)]),
        inst(O::LdrswRO, vec![x(0), x(1), w(2)]),
    ] {
        assert_eq!(instruction_word(&inst), None, "{inst:?}");
        assert!(
            instruction_word_verdict(&inst, &config()).is_none(),
            "{inst:?}"
        );
        assert_eq!(check_emitted_instruction_word(&inst, 0), None, "{inst:?}");
    }
}

/// Role names and register-free obligation names make instances that differ
/// only in register numbers carry EQUAL obligations, name included: the memo
/// key of both the boundary search and the evaluator is the whole obligation,
/// so the second instance is a memo hit. Content equality alone would not
/// show that; the words (and so the verdict names) differ.
#[test]
fn register_numbers_do_not_change_the_obligation() {
    let first =
        instruction_word_verdict(&inst(O::CmpRR, vec![x(3), x(4)]), &config()).expect("admitted");
    let second =
        instruction_word_verdict(&inst(O::CmpRR, vec![x(9), x(1)]), &config()).expect("admitted");
    assert_ne!(first.word, second.word);
    assert_ne!(first.name, second.name);
    assert_eq!(first.locations, second.locations);
    assert_eq!(
        first
            .locations
            .iter()
            .map(|(_, obligation)| obligation.name.as_str())
            .collect::<Vec<_>>(),
        vec!["A64 instruction word CmpRR: Nzcv"]
    );
    // The destination's register number is in the location, not in the
    // obligation.
    let add = |dst: u16, src: u16, value: i64| {
        let verdict =
            instruction_word_verdict(&inst(O::AddRI, vec![x(dst), x(src), imm(value)]), &config())
                .expect("admitted");
        assert_eq!(verdict.locations.len(), 1);
        verdict.locations[0].clone()
    };
    assert_eq!(add(5, 3, 5).0, Location::Gpr(5));
    assert_eq!(add(17, 2, 5).0, Location::Gpr(17));
    assert_eq!(add(5, 3, 5).1, add(17, 2, 5).1);
    assert_eq!(add(5, 3, 5).1.name, "A64 instruction word AddRI: Gpr");
    // A different immediate is a different obligation under the same name.
    assert_eq!(add(5, 3, 6).1.name, add(5, 3, 5).1.name);
    assert_ne!(add(5, 3, 6).1, add(5, 3, 5).1);
    // A compare of a register with itself is a different obligation.
    let same =
        instruction_word_verdict(&inst(O::CmpRR, vec![x(3), x(3)]), &config()).expect("admitted");
    assert_ne!(first.locations, same.locations);
    assert!(matches!(same.outcome, Outcome::Holds(_)));
}

#[test]
fn shared_linked_word_step_keeps_actual_bl_link_and_ret_register() {
    use crate::smt::{EvalResult, SmtSort};
    let mut state = LinkedWordState {
        registers: (0..31)
            .map(|n| (n, E::bv_const(100 + u64::from(n), 64)))
            .collect(),
        sp: E::bv_const(0x2000, 64),
        pc: E::bv_const(0x1000, 64),
        nzcv: E::bv_const(0, 4),
        memory: E::const_array(SmtSort::BitVec(64), E::bv_const(0, 8)),
    };
    let env = std::collections::HashMap::<String, u64>::new();
    state.step(0x94000003).unwrap();
    assert!(matches!(
        state.pc.try_eval(&env),
        Ok(EvalResult::Bv(0x100c))
    ));
    assert!(matches!(
        state.registers[&30].try_eval(&env),
        Ok(EvalResult::Bv(0x1004))
    ));
    state.step(0xd2800540).unwrap(); // MOVZ X0,42.
    state.step(0xf2a00020).unwrap(); // MOVK X0,1,LSL16.
    assert!(matches!(
        state.registers[&0].try_eval(&env),
        Ok(EvalResult::Bv(0x1002a))
    ));
    state.step(0xd65f03c0).unwrap();
    assert!(matches!(
        state.pc.try_eval(&env),
        Ok(EvalResult::Bv(0x1004))
    ));
    assert!(state.step(0x14000000).is_err()); // No generic/infinite B profile.
    assert!(state.step(0xd63f0000).is_err()); // No indirect callee assumption.
}

#[test]
fn shared_pair_step_restores_actual_entry_fp_lr_and_sp_after_bl() {
    use crate::smt::{EvalResult, SmtSort};
    let mut state = LinkedWordState {
        registers: (0..31)
            .map(|n| (n, E::bv_const(100 + u64::from(n), 64)))
            .collect(),
        sp: E::bv_const(0x2000, 64),
        pc: E::bv_const(0x1000, 64),
        nzcv: E::bv_const(0, 4),
        memory: E::const_array(SmtSort::BitVec(64), E::bv_const(0x7d, 8)),
    };
    let env = std::collections::HashMap::<String, u64>::new();
    let accesses = state.step(0xa9bf7bfd).unwrap();
    assert_eq!(accesses.len(), 2);
    assert!(matches!(
        accesses[0].try_eval(&env),
        Ok(EvalResult::Bv(0x1ff0))
    ));
    assert!(matches!(
        accesses[1].try_eval(&env),
        Ok(EvalResult::Bv(0x1ff8))
    ));
    state.step(0x910003fd).unwrap();
    state.step(0x94000003).unwrap();
    state.step(0xa8c17bfd).unwrap();
    assert!(matches!(
        state.sp.try_eval(&env),
        Ok(EvalResult::Bv(0x2000))
    ));
    assert!(matches!(
        state.registers[&29].try_eval(&env),
        Ok(EvalResult::Bv(129))
    ));
    assert!(matches!(
        state.registers[&30].try_eval(&env),
        Ok(EvalResult::Bv(130))
    ));
    state.step(0xd65f03c0).unwrap();
    assert!(matches!(state.pc.try_eval(&env), Ok(EvalResult::Bv(130))));
}
