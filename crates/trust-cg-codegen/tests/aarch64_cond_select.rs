// Copyright 2026 Andrew Yates | Apache-2.0
//! Conditional-select encoding/admission controls, not source or formal proofs.
//! Arm DDI0602 ID062025 (2025-06), printed pp373–384 and5947:
//! https://documentation-service.arm.com/static/685eb35c3cb5b729562ba389

use trust_cg_codegen::{
    aarch64::{decode_check::A64DecodeCheck, encode::encode_instruction},
    decode_check::{DecodeCheck, DecodeCheckOutcome},
};
use trust_cg_ir::{
    AArch64Opcode as Op, MachInst, MachOperand as Arg, RegClass, VReg,
    regs::{self, PReg, SpecialReg},
};

const FAMILY: [Op; 4] = [Op::Csel, Op::Csinc, Op::Csinv, Op::Csneg];

// Native controls execute on AArch64 Linux GNU (ELF) and AArch64 macOS
// (Mach-O); see common/native_host.rs. Other hosts compile them out.
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
#[path = "common/cond_select_native.rs"]
mod native;

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu")),
    feature = "verify"
))]
#[path = "common/cond_select_pass_native.rs"]
mod pass_native;

fn gpr(width: u16, index: u16) -> Arg {
    Arg::PReg(match (width, index) {
        (32, 31) => regs::WZR,
        (64, 31) => regs::XZR,
        (32, _) => PReg::new(32 + index),
        (64, _) => PReg::new(index),
        _ => panic!("unsupported test width"),
    })
}

fn instruction(op: Op, width: u16, cc: i64, registers: [u16; 3]) -> MachInst {
    let mut args: Vec<_> = registers.into_iter().map(|r| gpr(width, r)).collect();
    args.push(Arg::Imm(cc));
    MachInst::new(op, args)
}

fn check(inst: &MachInst, word: u32) -> DecodeCheckOutcome {
    A64DecodeCheck.check_one(inst, &word.to_le_bytes(), None)
}

#[test]
fn conditional_select_known_words_and_every_register_tuple() {
    let mut checks = 0;
    for (op, base) in FAMILY
        .into_iter()
        .zip([0x1a80_0000, 0x1a80_0400, 0x5a80_0000, 0x5a80_0400])
    {
        for width in [32, 64] {
            for rd in 0..32 {
                for rn in 0..32 {
                    for rm in 0..32 {
                        let inst = instruction(op, width, 0, [rd, rn, rm]);
                        let expected = base
                            | (u32::from(width == 64) << 31)
                            | (u32::from(rm) << 16)
                            | (u32::from(rn) << 5)
                            | u32::from(rd);
                        assert_eq!(encode_instruction(&inst).unwrap(), expected);
                        assert!(
                            matches!(check(&inst, expected), DecodeCheckOutcome::Match),
                            "{inst:?}"
                        );
                        checks += 1;
                    }
                }
            }
            for cc in 0..16 {
                let inst = instruction(op, width, cc, [0, 1, 2]);
                let word = encode_instruction(&inst).unwrap();
                assert_eq!(
                    word,
                    base | (u32::from(width == 64) << 31) | 0x20020 | ((cc as u32) << 12)
                );
                assert!(matches!(check(&inst, word), DecodeCheckOutcome::Match));
            }
            // Both public ZR representations must preserve width and encode
            // identically in each source/destination slot, including aliases.
            for spellings in 0..8 {
                let mut inst = instruction(op, width, 14, [31, 31, 31]);
                for (index, operand) in inst.operands[..3].iter_mut().enumerate() {
                    if spellings & (1 << index) != 0 {
                        *operand = Arg::Special(if width == 32 {
                            SpecialReg::WZR
                        } else {
                            SpecialReg::XZR
                        });
                    }
                }
                let expected = base | (u32::from(width == 64) << 31) | 0x1fe3ff;
                assert_eq!(encode_instruction(&inst).unwrap(), expected);
                assert!(matches!(check(&inst, expected), DecodeCheckOutcome::Match));
            }
        }
    }
    assert_eq!(checks, 262144);
}

#[test]
fn conditional_select_rejects_malformed_intent_without_masking_or_bank_aliases() {
    let bad_registers = [
        Arg::PReg(regs::SP),
        Arg::PReg(regs::WSP),
        Arg::Special(SpecialReg::SP),
        Arg::PReg(regs::S0),
        Arg::PReg(regs::D0),
        Arg::PReg(regs::V0),
        Arg::PReg(regs::NZCV),
        Arg::PReg(PReg::new(u16::MAX)),
        Arg::VReg(VReg::new(0, RegClass::Gpr64)),
        Arg::Imm(0),
    ];
    for op in FAMILY {
        for width in [32, 64] {
            let valid = instruction(op, width, 0, [0, 1, 2]);
            let word = encode_instruction(&valid).unwrap();
            let mut invalid = Vec::new();
            for index in 0..3 {
                for bad in bad_registers
                    .iter()
                    .cloned()
                    .chain([gpr(if width == 32 { 64 } else { 32 }, index as u16)])
                {
                    let mut inst = valid.clone();
                    inst.operands[index] = bad;
                    invalid.push(inst);
                }
            }
            for bad in [
                Arg::Imm(-1),
                Arg::Imm(16),
                Arg::Imm(256),
                Arg::Imm(i64::MIN),
                Arg::Imm(i64::MAX),
                gpr(64, 0),
            ] {
                let mut inst = valid.clone();
                inst.operands[3] = bad;
                invalid.push(inst);
            }
            for len in 0..4 {
                invalid.push(MachInst::new(op, valid.operands[..len].to_vec()));
            }
            let mut extra = valid.clone();
            extra.operands.push(Arg::Imm(0));
            invalid.push(extra);
            for inst in invalid {
                assert!(
                    encode_instruction(&inst).is_err(),
                    "encoder admitted {inst:?}"
                );
                assert!(
                    matches!(check(&inst, word), DecodeCheckOutcome::Mismatch(_)),
                    "decoder admitted {inst:?}"
                );
            }
        }
    }
}

#[test]
fn conditional_select_decoded_field_mutants_are_rejected() {
    for op in FAMILY {
        for width in [32, 64] {
            for cc in 0..16 {
                let inst = instruction(op, width, cc, [0, 1, 2]);
                let word = encode_instruction(&inst).unwrap();
                // Destination, both operands, condition, variant bits, width,
                // reserved bit11 and S29 must all remain tied to the intent.
                for bit in [0, 5, 16, 12, 10, 30, 31, 11, 29] {
                    assert!(
                        matches!(
                            check(&inst, word ^ (1 << bit)),
                            DecodeCheckOutcome::Mismatch(_)
                        ),
                        "{inst:?}, bit{bit}"
                    );
                }
            }
        }
    }
}

#[test]
fn cset_alias_requires_an_invertible_condition_and_exact_gpr_shape() {
    for width in [32, 64] {
        for cc in 0..14 {
            for rd in [0, 30, 31] {
                let inst = MachInst::new(Op::CSet, vec![gpr(width, rd), Arg::Imm(cc)]);
                let expected = 0x1a9f_07e0
                    | (u32::from(width == 64) << 31)
                    | (((cc as u32) ^ 1) << 12)
                    | u32::from(rd);
                assert_eq!(encode_instruction(&inst).unwrap(), expected);
                assert!(matches!(check(&inst, expected), DecodeCheckOutcome::Match));
                if rd == 31 {
                    let special = MachInst::new(
                        Op::CSet,
                        vec![
                            Arg::Special(if width == 32 {
                                SpecialReg::WZR
                            } else {
                                SpecialReg::XZR
                            }),
                            Arg::Imm(cc),
                        ],
                    );
                    assert_eq!(encode_instruction(&special).unwrap(), expected);
                    assert!(matches!(
                        check(&special, expected),
                        DecodeCheckOutcome::Match
                    ));
                }
            }
        }
        let valid = MachInst::new(Op::CSet, vec![gpr(width, 0), Arg::Imm(0)]);
        let word = encode_instruction(&valid).unwrap();
        let mut invalid = Vec::new();
        for cond in [-1, 14, 15, 16, 256, i64::MIN, i64::MAX] {
            invalid.push(MachInst::new(Op::CSet, vec![gpr(width, 0), Arg::Imm(cond)]));
        }
        for bad in [
            Arg::PReg(regs::SP),
            Arg::PReg(regs::WSP),
            Arg::Special(SpecialReg::SP),
            Arg::PReg(regs::S0),
            Arg::PReg(regs::NZCV),
            Arg::Imm(0),
        ] {
            invalid.push(MachInst::new(Op::CSet, vec![bad, Arg::Imm(0)]));
        }
        invalid.push(MachInst::new(Op::CSet, vec![gpr(width, 0), gpr(width, 1)]));
        invalid.push(MachInst::new(Op::CSet, vec![]));
        invalid.push(MachInst::new(Op::CSet, vec![gpr(width, 0)]));
        invalid.push(MachInst::new(
            Op::CSet,
            vec![gpr(width, 0), Arg::Imm(0), Arg::Imm(0)],
        ));
        for inst in invalid {
            assert!(
                encode_instruction(&inst).is_err(),
                "encoder admitted {inst:?}"
            );
            assert!(
                matches!(check(&inst, word), DecodeCheckOutcome::Mismatch(_)),
                "decoder admitted {inst:?}"
            );
        }
    }
}

#[path = "common/fresh_dir.rs"]
mod fresh_dir;
