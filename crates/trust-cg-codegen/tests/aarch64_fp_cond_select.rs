// Copyright 2026 Andrew Yates | Apache-2.0
//! FCSEL encoding/admission controls, not a source-lowering proof.

use trust_cg_codegen::{
    aarch64::{
        decode_check::A64DecodeCheck,
        encode::encode_instruction,
        encoding_fp::{FpEncodeError, FpSize, encode_fcsel},
    },
    decode_check::{DecodeCheck, DecodeCheckOutcome},
};
use trust_cg_ir::{
    AArch64Opcode as Op, MachInst, MachOperand as Arg, RegClass, VReg,
    regs::{self, PReg, SpecialReg},
};

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[path = "common/rosetta.rs"]
mod process;

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[path = "common/native_host.rs"]
mod native_host;

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[path = "common/fp_cond_select_native.rs"]
mod native;

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu")),
    feature = "verify"
))]
#[path = "common/fp_cond_select_pipeline_native.rs"]
mod pipeline_native;

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu")),
    feature = "verify"
))]
#[path = "common/fp_cond_select_fcmp_native.rs"]
mod fcmp_native;

fn fpr(width: u16, index: u16) -> Arg {
    assert!(index < 32);
    Arg::PReg(PReg::new(match width {
        32 => 128 + index,
        64 => 96 + index,
        _ => panic!("test supports only S/D MachIR"),
    }))
}

fn instruction(width: u16, cc: i64, regs: [u16; 3]) -> MachInst {
    let mut operands: Vec<_> = regs.into_iter().map(|index| fpr(width, index)).collect();
    operands.push(Arg::Imm(cc));
    MachInst::new(Op::FcselRR, operands)
}

fn check(inst: &MachInst, word: u32) -> DecodeCheckOutcome {
    A64DecodeCheck.check_one(inst, &word.to_le_bytes(), None)
}

fn expected_word(width: u16, cc: u32, [rd, rn, rm]: [u16; 3]) -> u32 {
    // Independent field transcription, not an encoder helper: fixed prefix
    // 00011110, S/D ftype00/01, bit21=1, bits11:10=11.
    0x1e20_0c00
        | (u32::from(width == 64) << 22)
        | (u32::from(rm) << 16)
        | (cc << 12)
        | (u32::from(rn) << 5)
        | u32::from(rd)
}

#[test]
fn fcsel_all_sd_register_tuples_and_conditions_match_independent_words() {
    // Literal assembler-oracle anchors precede the complete field matrix.
    for (width, cc, regs, word) in [
        (32, 0, [0, 1, 2], 0x1e22_0c20),
        (64, 0, [0, 1, 2], 0x1e62_0c20),
        (32, 14, [5, 4, 3], 0x1e23_ec85),
        (64, 14, [5, 4, 3], 0x1e63_ec85),
    ] {
        assert_eq!(expected_word(width, cc, regs), word);
        assert_eq!(
            encode_instruction(&instruction(width, cc.into(), regs)).unwrap(),
            word
        );
    }
    let mut cases = 0;
    for width in [32, 64] {
        for cc in 0..16 {
            for rd in 0..32 {
                for rn in 0..32 {
                    for rm in 0..32 {
                        let regs = [rd, rn, rm];
                        let inst = instruction(width, cc.into(), regs);
                        let word = expected_word(width, cc, regs);
                        assert_eq!(encode_instruction(&inst).unwrap(), word, "{inst:?}");
                        assert!(
                            matches!(check(&inst, word), DecodeCheckOutcome::Match),
                            "{inst:?}"
                        );
                        cases += 1;
                    }
                }
            }
        }
    }
    // Every S/D register31 tuple is included: FPR31 is real storage, not ZR.
    assert_eq!(cases, 1_048_576);
}

#[test]
fn fcsel_rejects_missing_extra_and_noncanonical_conditions() {
    let mut cases = 0;
    for width in [32, 64] {
        let valid = instruction(width, 0, [0, 1, 2]);
        let word = expected_word(width, 0, [0, 1, 2]);
        let mut malformed = Vec::new();
        for condition in [
            Arg::Imm(-1),
            Arg::Imm(16),
            Arg::Imm(256),
            Arg::Imm(i64::MIN),
            Arg::Imm(i64::MAX),
            fpr(width, 0),
            Arg::PReg(regs::X0),
            Arg::Special(SpecialReg::XZR),
            Arg::VReg(VReg::new(0, RegClass::Gpr64)),
        ] {
            let mut inst = valid.clone();
            inst.operands[3] = condition;
            malformed.push(inst);
        }
        for length in 0..4 {
            malformed.push(MachInst::new(
                Op::FcselRR,
                valid.operands[..length].to_vec(),
            ));
        }
        for extra in [Arg::Imm(0), fpr(width, 0)] {
            let mut inst = valid.clone();
            inst.operands.push(extra);
            malformed.push(inst);
        }
        for inst in malformed {
            assert!(
                encode_instruction(&inst).is_err(),
                "encoder admitted {inst:?}"
            );
            assert!(
                matches!(check(&inst, word), DecodeCheckOutcome::Mismatch(_)),
                "decoder admitted {inst:?}"
            );
            cases += 1;
        }
    }
    assert_eq!(cases, 30);
}

#[test]
fn fcsel_rejects_every_wrong_register_bank_and_mixed_width() {
    let mut cases = 0;
    for width in [32, 64] {
        let valid = instruction(width, 0, [0, 1, 2]);
        let word = expected_word(width, 0, [0, 1, 2]);
        for index in 0..3 {
            for operand in [
                Arg::PReg(regs::X0),
                Arg::PReg(regs::W0),
                Arg::PReg(regs::SP),
                Arg::PReg(regs::WSP),
                Arg::PReg(regs::XZR),
                Arg::PReg(regs::WZR),
                Arg::PReg(regs::V0),
                Arg::PReg(regs::H0),
                Arg::PReg(regs::B0),
                Arg::PReg(regs::NZCV),
                Arg::PReg(PReg::new(u16::MAX)),
                Arg::Special(SpecialReg::SP),
                Arg::Special(SpecialReg::XZR),
                Arg::Special(SpecialReg::WZR),
                Arg::VReg(VReg::new(
                    0,
                    if width == 32 {
                        RegClass::Fpr32
                    } else {
                        RegClass::Fpr64
                    },
                )),
                Arg::Imm(0),
                fpr(if width == 32 { 64 } else { 32 }, 0),
            ] {
                let mut inst = valid.clone();
                inst.operands[index] = operand;
                assert!(
                    encode_instruction(&inst).is_err(),
                    "encoder admitted {inst:?}"
                );
                assert!(
                    matches!(check(&inst, word), DecodeCheckOutcome::Mismatch(_)),
                    "decoder admitted {inst:?}"
                );
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 102);
}

#[test]
fn fcsel_decoder_rejects_every_word_bit_mutation_and_invalid_byte_count() {
    let mut mutants = 0;
    for width in [32, 64] {
        for cc in 0..16 {
            let inst = instruction(width, cc.into(), [0, 1, 2]);
            let word = expected_word(width, cc, [0, 1, 2]);
            for bit in 0..32 {
                assert!(
                    matches!(
                        check(&inst, word ^ (1 << bit)),
                        DecodeCheckOutcome::Mismatch(_)
                    ),
                    "width{width} cc{cc} bit{bit}"
                );
                mutants += 1;
            }
            for bytes in [&[][..], &[0u8; 3][..], &[0u8; 5][..], &[0u8; 8][..]] {
                assert!(matches!(
                    A64DecodeCheck.check_one(&inst, bytes, None),
                    DecodeCheckOutcome::Mismatch(_)
                ));
            }
            // Half and the reserved ftype must not receive S/D intent credit.
            for ftype in [2, 3] {
                assert!(matches!(
                    check(&inst, (word & !(3 << 22)) | (ftype << 22)),
                    DecodeCheckOutcome::Mismatch(_)
                ));
            }
        }
    }
    assert_eq!(mutants, 1024);
}

#[test]
fn fcsel_public_helper_rejects_invalid_conditions_without_panicking() {
    let mut cases = 0;
    for size in [FpSize::Single, FpSize::Double, FpSize::Half] {
        for condition in [16, 17, 255, 256, u32::MAX] {
            let result = std::panic::catch_unwind(|| encode_fcsel(size, condition, 2, 1, 0));
            assert!(
                result.is_ok_and(|encoded| encoded.is_err()),
                "condition {condition} must return an error in every build profile"
            );
            assert_eq!(
                encode_fcsel(size, condition, 2, 1, 0),
                Err(FpEncodeError::ConditionOutOfRange {
                    cond: condition,
                    max: 15
                })
            );
            cases += 1;
        }
    }
    assert_eq!(cases, 15);
}

#[test]
fn fcsel_public_helper_preserves_valid_half_api_and_register_bounds() {
    let mut cases = 0;
    for (size, base) in [
        (FpSize::Single, 0x1e20_0c00),
        (FpSize::Double, 0x1e60_0c00),
        (FpSize::Half, 0x1ee0_0c00),
    ] {
        for condition in 0..16 {
            for [rm, rn, rd] in [[2, 1, 0], [31, 31, 31]] {
                let expected = base
                    | (u32::from(rm) << 16)
                    | (condition << 12)
                    | (u32::from(rn) << 5)
                    | u32::from(rd);
                assert_eq!(encode_fcsel(size, condition, rm, rn, rd), Ok(expected));
                cases += 1;
            }
        }
        for index in 0..3 {
            for bad in [32, u8::MAX] {
                let mut regs = [2, 1, 0];
                regs[index] = bad;
                assert!(encode_fcsel(size, 0, regs[0], regs[1], regs[2]).is_err());
            }
        }
    }
    assert_eq!(cases, 96);
}

#[path = "common/fresh_dir.rs"]
mod fresh_dir;
