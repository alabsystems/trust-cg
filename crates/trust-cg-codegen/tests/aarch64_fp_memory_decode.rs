// Copyright 2026 Andrew Yates | Apache-2.0
//! Immediate FP/SIMD byte checks; not a memory-semantics or lowering proof.

use trust_cg_codegen::{
    aarch64::{decode_check::A64DecodeCheck, encode::encode_instruction},
    decode_check::{
        DecodeCheck, DecodeCheckItem, DecodeCheckMode, DecodeCheckOutcome, FixupHole,
        FixupHoleKind, run_decode_check,
    },
};
use trust_cg_ir::{
    AArch64Opcode as Op, MachInst, MachOperand as Arg,
    regs::{self, PReg, SpecialReg},
};

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[path = "common/fp_memory_native.rs"]
mod native;

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[test]
fn fp_memory_native_words_and_exact_memory_effects() {
    native::run();
}

fn transfer(width: u16, rt: u16) -> Arg {
    Arg::PReg(PReg::new(match width {
        16 => 165 + rt,
        32 => 128 + rt,
        64 => 96 + rt,
        128 => 64 + rt,
        _ => panic!("only H/S/D/Q are in this slice"),
    }))
}

fn inst(width: u16, load: bool, rt: u16, rn: u16, offset: i64, mem: bool) -> MachInst {
    let mut args = vec![transfer(width, rt)];
    if mem {
        args.push(Arg::MemOp {
            base: PReg::new(rn),
            offset,
        });
    } else {
        args.extend([Arg::PReg(PReg::new(rn)), Arg::Imm(offset)]);
    }
    MachInst::new(if load { Op::LdrRI } else { Op::StrRI }, args)
}

fn check(inst: &MachInst, word: u32) -> DecodeCheckOutcome {
    A64DecodeCheck.check_one(inst, &word.to_le_bytes(), None)
}

fn word(width: u16, load: bool, rt: u16, rn: u16, offset: i64) -> u32 {
    // Independent LLVM/Arm format transcription, not production helpers.
    // V=1; Q uses size00/opc1x, H/S/D size01/10/11 and opc0x.
    let (size, high_opc) = match width {
        16 => (1, 0),
        32 => (2, 0),
        64 => (3, 0),
        128 => (0, 2),
        _ => unreachable!(),
    };
    let scale = i64::from(width / 8);
    let base = (size << 30)
        | 0x3c00_0000
        | ((high_opc | u32::from(load)) << 22)
        | (u32::from(rn) << 5)
        | u32::from(rt);
    if offset >= 0 && offset % scale == 0 && offset / scale <= 4095 {
        base | 0x0100_0000 | ((offset / scale) as u32) << 10
    } else {
        assert!((-256..=255).contains(&offset));
        base | ((offset as u32 & 0x1ff) << 12)
    }
}

// Literal anchors, separately checked with GNU as; no production-generated words.
const ANCHORS: [(u16, bool, u16, u16, i64, u32); 16] = [
    (16, true, 0, 1, 2, 0x7d40_0420),
    (16, false, 31, 31, 8190, 0x7d3f_ffff),
    (32, true, 0, 1, 4, 0xbd40_0420),
    (32, false, 31, 31, 16380, 0xbd3f_ffff),
    (64, true, 0, 1, 8, 0xfd40_0420),
    (64, false, 31, 31, 32760, 0xfd3f_ffff),
    (128, true, 0, 1, 16, 0x3dc0_0420),
    (128, false, 31, 31, 65520, 0x3dbf_ffff),
    (16, true, 31, 31, -256, 0x7c50_03ff),
    (16, false, 0, 1, 255, 0x7c0f_f020),
    (32, true, 31, 31, -256, 0xbc50_03ff),
    (32, false, 0, 1, 255, 0xbc0f_f020),
    (64, true, 31, 31, -256, 0xfc50_03ff),
    (64, false, 0, 1, 255, 0xfc0f_f020),
    (128, true, 31, 31, -256, 0x3cd0_03ff),
    (128, false, 0, 1, 255, 0x3c8f_f020),
];

#[test]
fn fp_memory_literal_anchors_and_all_single_bit_mutations() {
    for (width, load, rt, rn, offset, expected) in ANCHORS {
        assert_eq!(word(width, load, rt, rn, offset), expected);
        for mem in [false, true] {
            let intent = inst(width, load, rt, rn, offset, mem);
            assert_eq!(encode_instruction(&intent).unwrap(), expected);
            assert!(
                matches!(check(&intent, expected), DecodeCheckOutcome::Match),
                "{intent:?}"
            );
            for bit in 0..32 {
                assert!(
                    matches!(
                        check(&intent, expected ^ (1 << bit)),
                        DecodeCheckOutcome::Mismatch(_)
                    ),
                    "{intent:?}, bit{bit}"
                );
            }
        }
    }
}

#[test]
fn fp_memory_all_registers_and_address_layouts_at_boundaries() {
    let mut cases = 0;
    for width in [16, 32, 64, 128] {
        let scale = i64::from(width / 8);
        for load in [false, true] {
            for rt in 0..32 {
                for rn in 0..32 {
                    for offset in [-256, -1, 0, 1, 255, scale, 4095 * scale] {
                        for mem in [false, true] {
                            let intent = inst(width, load, rt, rn, offset, mem);
                            let expected = word(width, load, rt, rn, offset);
                            assert_eq!(
                                encode_instruction(&intent).unwrap(),
                                expected,
                                "{intent:?}"
                            );
                            assert!(
                                matches!(check(&intent, expected), DecodeCheckOutcome::Match),
                                "{intent:?}"
                            );
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 114_688);
}

#[test]
fn fp_memory_every_immediate_field_at_representative_registers() {
    let mut cases = 0;
    for width in [16, 32, 64, 128] {
        let scale = i64::from(width / 8);
        for load in [false, true] {
            for offset in (0..4096)
                .map(|v| v * scale)
                .chain((-256..=255).filter(|v| *v < 0 || v % scale != 0))
            {
                for mem in [false, true] {
                    let intent = inst(width, load, 31, 31, offset, mem);
                    let expected = word(width, load, 31, 31, offset);
                    assert_eq!(encode_instruction(&intent).unwrap(), expected, "{intent:?}");
                    assert!(
                        matches!(check(&intent, expected), DecodeCheckOutcome::Match),
                        "{intent:?}"
                    );
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 72_768);
}

#[test]
fn fp_memory_zero_offset_spellings_preserve_real_register31() {
    for width in [16, 32, 64, 128] {
        for load in [false, true] {
            for base in [
                Arg::PReg(regs::X0),
                Arg::PReg(regs::SP),
                Arg::Special(SpecialReg::SP),
            ] {
                let rn = if base == Arg::PReg(regs::X0) { 0 } else { 31 };
                for explicit in [false, true] {
                    let mut args = vec![transfer(width, 31), base.clone()];
                    if explicit {
                        args.push(Arg::Imm(0));
                    }
                    let intent = MachInst::new(if load { Op::LdrRI } else { Op::StrRI }, args);
                    let expected = word(width, load, 31, rn, 0);
                    assert_eq!(encode_instruction(&intent).unwrap(), expected);
                    assert!(matches!(
                        check(&intent, expected),
                        DecodeCheckOutcome::Match
                    ));
                }
            }
        }
    }
}

#[test]
fn fp_memory_rejects_noncanonical_addresses_and_extra_operands() {
    for width in [16, 32, 64, 128] {
        for load in [false, true] {
            let good = inst(width, load, 0, 1, 0, false);
            let expected = word(width, load, 0, 1, 0);
            let mut bad = Vec::new();
            for base in [
                regs::W0,
                regs::W1,
                regs::WSP,
                regs::XZR,
                regs::WZR,
                regs::V0,
                regs::V1,
                regs::D0,
                regs::D1,
                regs::S0,
                regs::S1,
                regs::H0,
                regs::H1,
                regs::B0,
                regs::B1,
                regs::NZCV,
                PReg::new(u16::MAX),
            ] {
                for address in [Arg::PReg(base), Arg::MemOp { base, offset: 0 }] {
                    let invalid = MachInst::new(good.opcode, vec![transfer(width, 0), address]);
                    // Match the misleading low hardware bits: refusal must
                    // depend on the bank, not an incidental Rn disagreement.
                    let spoof = word(width, load, 0, u16::from(base.hw_enc()), 0);
                    assert!(
                        matches!(check(&invalid, spoof), DecodeCheckOutcome::Mismatch(_)),
                        "checker accepted aliased base {invalid:?}"
                    );
                    bad.push(invalid);
                }
            }
            for base in [
                Arg::Special(SpecialReg::XZR),
                Arg::Special(SpecialReg::WZR),
                Arg::Imm(0),
            ] {
                let invalid = MachInst::new(good.opcode, vec![transfer(width, 0), base]);
                assert!(matches!(
                    check(&invalid, word(width, load, 0, 31, 0)),
                    DecodeCheckOutcome::Mismatch(_)
                ));
                bad.push(invalid);
            }
            bad.push(MachInst::new(good.opcode, vec![transfer(width, 0)]));
            for extra in [Arg::Imm(0), Arg::PReg(regs::X1)] {
                let mut normal = good.clone();
                normal.operands.push(extra.clone());
                bad.push(normal);
                let mut mem = inst(width, load, 0, 1, 0, true);
                mem.operands.push(extra);
                bad.push(mem);
            }
            let mut wrong_offset = good.clone();
            wrong_offset.operands[2] = Arg::PReg(regs::X0);
            bad.push(wrong_offset);
            for intent in bad {
                assert!(
                    encode_instruction(&intent).is_err(),
                    "encoder admitted {intent:?}"
                );
                assert!(
                    matches!(check(&intent, expected), DecodeCheckOutcome::Mismatch(_)),
                    "checker admitted {intent:?}"
                );
            }
        }
    }
}

#[test]
fn fp_memory_rejects_unencodable_and_wrapping_offsets() {
    for width in [16, 32, 64, 128] {
        let scale = i64::from(width / 8);
        for load in [false, true] {
            for offset in [
                (1_i64 << 32) * scale,
                ((1_i64 << 32) + 4095) * scale,
                -257,
                i64::MIN,
                i64::MAX,
                4096 * scale,
            ] {
                for mem in [false, true] {
                    let intent = inst(width, load, 0, 1, offset, mem);
                    assert!(
                        encode_instruction(&intent).is_err(),
                        "encoder truncated {intent:?}"
                    );
                    assert!(
                        matches!(
                            check(&intent, word(width, load, 0, 1, 0)),
                            DecodeCheckOutcome::Mismatch(_)
                        ),
                        "checker admitted {intent:?}"
                    );
                }
            }
        }
    }
}

#[test]
fn integer_memory_shared_offset_helper_must_not_wrap() {
    for (opcode, rt, scale) in [
        (Op::LdrRI, regs::X0, 8),
        (Op::StrRI, regs::W0, 4),
        (Op::LdrbRI, regs::W0, 1),
        (Op::StrhRI, regs::W0, 2),
    ] {
        for offset in [(1_i64 << 32) * scale, ((1_i64 << 32) + 4095) * scale] {
            let intent = MachInst::new(
                opcode,
                vec![Arg::PReg(rt), Arg::PReg(regs::X1), Arg::Imm(offset)],
            );
            assert!(
                encode_instruction(&intent).is_err(),
                "encoder truncated {intent:?}"
            );
        }
    }
}

#[test]
fn fp_byte_registers_remain_outside_the_admitted_slice() {
    for opcode in [Op::LdrRI, Op::StrRI] {
        let intent = MachInst::new(
            opcode,
            vec![Arg::PReg(regs::B0), Arg::PReg(regs::X1), Arg::Imm(0)],
        );
        assert!(encode_instruction(&intent).is_err());
        let encoded = if opcode == Op::LdrRI {
            0x3d40_0020
        } else {
            0x3d00_0020
        };
        assert!(!matches!(
            check(&intent, encoded),
            DecodeCheckOutcome::Match
        ));
    }
}

#[test]
fn fp_memory_rejects_relocation_holes_and_noncanonical_zero_unscaled_form() {
    for width in [16, 32, 64, 128] {
        for load in [false, true] {
            let intent = inst(width, load, 31, 31, 0, false);
            let expected = word(width, load, 31, 31, 0);
            // LDUR/STUR #0 is legal machine code but not the canonical RI form.
            assert!(matches!(
                check(&intent, expected & !0x0100_0000),
                DecodeCheckOutcome::Mismatch(_)
            ));
            for kind in [
                FixupHoleKind::Branch,
                FixupHoleKind::Call,
                FixupHoleKind::GlobalRef,
                FixupHoleKind::ExternRefGot,
                FixupHoleKind::TlsTlv,
                FixupHoleKind::ConstPool,
            ] {
                for (offset_in_inst, width) in [(0, 4), (1, 2), (0, 0), (4, 8)] {
                    let hole = FixupHole {
                        offset_in_inst,
                        width,
                        kind,
                    };
                    assert!(matches!(
                        A64DecodeCheck.check_one(&intent, &expected.to_le_bytes(), Some(&hole)),
                        DecodeCheckOutcome::Mismatch(_)
                    ));
                }
            }
        }
    }
}

#[test]
fn volatile_fp_aliases_are_checked_and_bad_addresses_refused() {
    for opcode in [Op::VolatileLdrRI, Op::VolatileStrRI] {
        let mut intent = inst(128, opcode == Op::VolatileLdrRI, 0, 1, 0, false);
        intent.opcode = opcode;
        let expected = word(128, opcode == Op::VolatileLdrRI, 0, 1, 0);
        assert_eq!(encode_instruction(&intent).unwrap(), expected);
        assert!(matches!(
            check(&intent, expected),
            DecodeCheckOutcome::Match
        ));
        intent.operands[1] = Arg::PReg(regs::W1);
        assert!(encode_instruction(&intent).is_err());
        assert!(matches!(
            check(&intent, expected),
            DecodeCheckOutcome::Mismatch(_)
        ));
        intent.operands[1] = Arg::PReg(regs::X1);
        intent.operands[2] = Arg::Imm(1_i64 << 36);
        assert!(encode_instruction(&intent).is_err());
        assert!(matches!(
            check(&intent, expected),
            DecodeCheckOutcome::Mismatch(_)
        ));
    }
}

// Volatility is a compiler effect, not an extra architectural encoding bit.
// These controls check bytes against the distinct volatile intent only. They
// neither establish ordering nor extend the ordinary native harness's scope.
fn volatile_inst(width: u16, load: bool, rt: u16, rn: u16, offset: i64, mem: bool) -> MachInst {
    let mut intent = inst(width, load, rt, rn, offset, mem);
    intent.opcode = if load {
        Op::VolatileLdrRI
    } else {
        Op::VolatileStrRI
    };
    intent
}

#[test]
fn volatile_fp_literal_anchors_and_all_single_bit_mutations() {
    let mut accepted = 0;
    let mut refused = 0;
    for (width, load, rt, rn, offset, expected) in ANCHORS {
        for mem in [false, true] {
            let intent = volatile_inst(width, load, rt, rn, offset, mem);
            assert_eq!(encode_instruction(&intent).unwrap(), expected);
            assert!(
                matches!(check(&intent, expected), DecodeCheckOutcome::Match),
                "{intent:?}"
            );
            accepted += 1;
            for bit in 0..32 {
                assert!(
                    matches!(
                        check(&intent, expected ^ (1 << bit)),
                        DecodeCheckOutcome::Mismatch(_)
                    ),
                    "{intent:?}, bit{bit}"
                );
                refused += 1;
            }
        }
    }
    assert_eq!((accepted, refused), (32, 1_024));
}

#[test]
fn volatile_fp_all_registers_and_address_layouts_at_boundaries() {
    let mut cases = 0;
    for width in [16, 32, 64, 128] {
        let scale = i64::from(width / 8);
        for load in [false, true] {
            for rt in 0..32 {
                for rn in 0..32 {
                    for offset in [-256, -1, 0, 1, 255, scale, 4095 * scale] {
                        for mem in [false, true] {
                            let intent = volatile_inst(width, load, rt, rn, offset, mem);
                            let expected = word(width, load, rt, rn, offset);
                            assert_eq!(
                                encode_instruction(&intent).unwrap(),
                                expected,
                                "{intent:?}"
                            );
                            assert!(
                                matches!(check(&intent, expected), DecodeCheckOutcome::Match),
                                "{intent:?}"
                            );
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 114_688);
}

#[test]
fn volatile_fp_every_canonical_immediate_field() {
    let mut cases = 0;
    for width in [16, 32, 64, 128] {
        let scale = i64::from(width / 8);
        for load in [false, true] {
            for offset in (0..4096)
                .map(|v| v * scale)
                .chain((-256..=255).filter(|v| *v < 0 || v % scale != 0))
            {
                for mem in [false, true] {
                    // Full Rt/Rn banks are covered above; this census pins real
                    // FPR31 and SP while exhausting every canonical immediate.
                    let intent = volatile_inst(width, load, 31, 31, offset, mem);
                    let expected = word(width, load, 31, 31, offset);
                    assert_eq!(encode_instruction(&intent).unwrap(), expected, "{intent:?}");
                    assert!(
                        matches!(check(&intent, expected), DecodeCheckOutcome::Match),
                        "{intent:?}"
                    );
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 72_768);
}

#[test]
fn volatile_fp_zero_offset_spellings_keep_real_fpr31() {
    let mut cases = 0;
    for width in [16, 32, 64, 128] {
        for load in [false, true] {
            for base in [
                Arg::PReg(regs::X0),
                Arg::PReg(regs::SP),
                Arg::Special(SpecialReg::SP),
            ] {
                let rn = if base == Arg::PReg(regs::X0) { 0 } else { 31 };
                for explicit in [false, true] {
                    let mut intent = volatile_inst(width, load, 31, rn, 0, false);
                    intent.operands = vec![transfer(width, 31), base.clone()];
                    if explicit {
                        intent.operands.push(Arg::Imm(0));
                    }
                    let expected = word(width, load, 31, rn, 0);
                    assert_eq!(encode_instruction(&intent).unwrap(), expected);
                    assert!(
                        matches!(check(&intent, expected), DecodeCheckOutcome::Match),
                        "{intent:?}"
                    );
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 48);
}

#[test]
fn volatile_fp_malformed_address_transfer_and_arity_refuse() {
    let mut cases = 0;
    for width in [16, 32, 64, 128] {
        for load in [false, true] {
            let good = volatile_inst(width, load, 0, 1, 0, false);
            let mut bad = Vec::new();
            for base in [
                regs::W0,
                regs::W1,
                regs::WSP,
                regs::XZR,
                regs::WZR,
                regs::V0,
                regs::V1,
                regs::D0,
                regs::D1,
                regs::S0,
                regs::S1,
                regs::H0,
                regs::H1,
                regs::B0,
                regs::B1,
                regs::NZCV,
                PReg::new(u16::MAX),
            ] {
                for address in [Arg::PReg(base), Arg::MemOp { base, offset: 0 }] {
                    // Matching low hardware fields prevent an incidental Rn
                    // mismatch from disguising missing bank validation.
                    bad.push((
                        MachInst::new(good.opcode, vec![transfer(width, 0), address]),
                        word(width, load, 0, u16::from(base.hw_enc()), 0),
                    ));
                }
            }
            for base in [
                Arg::Special(SpecialReg::XZR),
                Arg::Special(SpecialReg::WZR),
                Arg::Imm(0),
            ] {
                bad.push((
                    MachInst::new(good.opcode, vec![transfer(width, 0), base]),
                    word(width, load, 0, 31, 0),
                ));
            }
            bad.push((
                MachInst::new(good.opcode, vec![]),
                word(width, load, 0, 1, 0),
            ));
            bad.push((
                MachInst::new(good.opcode, vec![transfer(width, 0)]),
                word(width, load, 0, 1, 0),
            ));
            for extra in [Arg::Imm(0), Arg::PReg(regs::X1)] {
                for mem in [false, true] {
                    let mut intent = volatile_inst(width, load, 0, 1, 0, mem);
                    intent.operands.push(extra.clone());
                    bad.push((intent, word(width, load, 0, 1, 0)));
                }
            }
            let mut wrong_offset = good.clone();
            wrong_offset.operands[2] = Arg::PReg(regs::X0);
            bad.push((wrong_offset, word(width, load, 0, 1, 0)));
            for (intent, spoof) in bad {
                assert!(
                    encode_instruction(&intent).is_err(),
                    "encoder admitted {intent:?}"
                );
                assert!(
                    matches!(check(&intent, spoof), DecodeCheckOutcome::Mismatch(_)),
                    "checker admitted {intent:?}"
                );
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 352);

    // B is an unsupported FP transfer, not an ordinary GPR spelling. Other
    // nonscalar/invalid banks must not accidentally acquire the FP byte check.
    let mut transfer_cases = 0;
    for load in [false, true] {
        for rt in [regs::B0, regs::B1, regs::NZCV, PReg::new(u16::MAX)] {
            let mut intent = volatile_inst(128, load, 0, 1, 0, false);
            intent.operands[0] = Arg::PReg(rt);
            let b_register = rt == regs::B0 || rt == regs::B1;
            let spoof = (if b_register { 0x3d00_0000 } else { 0xf900_0000 })
                | (u32::from(load) << 22)
                | (1 << 5)
                | u32::from(rt.hw_enc());
            if b_register {
                assert!(
                    encode_instruction(&intent).is_err(),
                    "encoder admitted {intent:?}"
                );
            }
            // The legacy encoder's System/unknown GPR fallback is not repaired
            // here. Matching its low-field GPR word must still fail the decoder.
            assert!(
                matches!(check(&intent, spoof), DecodeCheckOutcome::Mismatch(_)),
                "checker admitted {intent:?}"
            );
            transfer_cases += 1;
        }
        for invalid in [
            Arg::Imm(0),
            Arg::VReg(regs::VReg::new(0, regs::RegClass::Fpr128)),
        ] {
            let mut intent = volatile_inst(128, load, 0, 1, 0, false);
            intent.operands[0] = invalid;
            assert!(
                encode_instruction(&intent).is_err(),
                "encoder admitted {intent:?}"
            );
            assert!(
                matches!(
                    check(&intent, word(128, load, 0, 1, 0)),
                    DecodeCheckOutcome::Mismatch(_)
                ),
                "checker admitted {intent:?}"
            );
            transfer_cases += 1;
        }
    }
    assert_eq!(transfer_cases, 12);
}

#[test]
fn volatile_fp_wrong_fields_offsets_and_holes_refuse() {
    let mut fields = 0;
    let mut offsets = 0;
    let mut holes = 0;
    for width in [16, 32, 64, 128] {
        let scale = i64::from(width / 8);
        for load in [false, true] {
            for mem in [false, true] {
                let intent = volatile_inst(width, load, 0, 1, 0, mem);
                let expected = word(width, load, 0, 1, 0);
                for wrong in [
                    word(width, !load, 0, 1, 0),
                    word(width, load, 1, 1, 0),
                    word(width, load, 0, 2, 0),
                    word(width, load, 0, 1, scale),
                    word(if width == 128 { 16 } else { width * 2 }, load, 0, 1, 0),
                    expected & !0x0100_0000,
                ] {
                    assert!(
                        matches!(check(&intent, wrong), DecodeCheckOutcome::Mismatch(_)),
                        "{intent:?}, {wrong:08x}"
                    );
                    fields += 1;
                }
                for offset in [
                    (1_i64 << 32) * scale,
                    ((1_i64 << 32) + 4095) * scale,
                    -257,
                    i64::MIN,
                    i64::MAX,
                    4096 * scale,
                ] {
                    let invalid = volatile_inst(width, load, 0, 1, offset, mem);
                    assert!(
                        encode_instruction(&invalid).is_err(),
                        "encoder truncated {invalid:?}"
                    );
                    assert!(
                        matches!(check(&invalid, expected), DecodeCheckOutcome::Mismatch(_)),
                        "checker admitted {invalid:?}"
                    );
                    offsets += 1;
                }
                for kind in [
                    FixupHoleKind::Branch,
                    FixupHoleKind::Call,
                    FixupHoleKind::GlobalRef,
                    FixupHoleKind::ExternRefGot,
                    FixupHoleKind::TlsTlv,
                    FixupHoleKind::ConstPool,
                ] {
                    for (offset_in_inst, width) in [(0, 4), (1, 2), (0, 0), (4, 8)] {
                        let hole = FixupHole {
                            offset_in_inst,
                            width,
                            kind,
                        };
                        assert!(
                            matches!(
                                A64DecodeCheck.check_one(
                                    &intent,
                                    &expected.to_le_bytes(),
                                    Some(&hole)
                                ),
                                DecodeCheckOutcome::Mismatch(_)
                            ),
                            "{intent:?}, {hole:?}"
                        );
                        holes += 1;
                    }
                }
            }
        }
    }
    assert_eq!((fields, offsets, holes), (96, 96, 384));
}

#[test]
fn volatile_gpr_and_scalar_writeback_have_explicit_decoder_contracts() {
    for load in [false, true] {
        for rt in [regs::W0, regs::X0, regs::WZR, regs::XZR] {
            let intent = MachInst::new(
                if load {
                    Op::VolatileLdrRI
                } else {
                    Op::VolatileStrRI
                },
                vec![Arg::PReg(rt), Arg::PReg(regs::X1), Arg::Imm(0)],
            );
            let encoded = encode_instruction(&intent).unwrap();
            assert!(
                matches!(check(&intent, encoded), DecodeCheckOutcome::Match),
                "{intent:?}"
            );
        }
    }
    for opcode in [Op::LdrRO, Op::StrRO] {
        // An RI-shaped address is not a valid register-offset intent.
        let mut intent = inst(128, true, 0, 1, 0, false);
        intent.opcode = opcode;
        assert!(
            matches!(
                check(&intent, word(128, true, 0, 1, 0)),
                DecodeCheckOutcome::Mismatch(_)
            ),
            "{intent:?}"
        );
        // Canonical S0,[X1,X2], LSL #0: independent literal RO words.
        let canonical = MachInst::new(
            opcode,
            vec![
                Arg::PReg(regs::S0),
                Arg::PReg(regs::X1),
                Arg::PReg(regs::X2),
            ],
        );
        let expected = if opcode == Op::LdrRO {
            0xbc62_6820
        } else {
            0xbc22_6820
        };
        assert!(matches!(
            check(&canonical, expected),
            DecodeCheckOutcome::Match
        ));
    }
    // The four scalar writeback opcodes own GPR transfers, not FP/Q. Their
    // strict decoder must refuse an FP intent instead of allowlisting it.
    for opcode in [
        Op::LdrPreIndex,
        Op::StrPreIndex,
        Op::LdrPostIndex,
        Op::StrPostIndex,
    ] {
        let mut intent = inst(128, true, 0, 1, 0, false);
        intent.opcode = opcode;
        assert!(
            matches!(
                check(&intent, word(128, true, 0, 1, 0)),
                DecodeCheckOutcome::Mismatch(_)
            ),
            "{intent:?}"
        );
    }
}

#[test]
fn volatile_fp_byte_lengths_and_actual_enforce_stream() {
    let mut lengths = 0;
    let mut streams = 0;
    for width in [16, 32, 64, 128] {
        for load in [false, true] {
            let intent = volatile_inst(width, load, 0, 1, 0, false);
            let expected = word(width, load, 0, 1, 0);
            for len in [0, 1, 2, 3, 5, 8] {
                let mut bytes = expected.to_le_bytes().to_vec();
                bytes.resize(len, 0);
                assert!(matches!(
                    A64DecodeCheck.check_one(&intent, &bytes, None),
                    DecodeCheckOutcome::Mismatch(_)
                ));
                lengths += 1;
            }
            let items = [DecodeCheckItem {
                start: 0,
                end: 4,
                intent,
                hole: None,
            }];
            run_decode_check(
                &A64DecodeCheck,
                &items,
                &expected.to_le_bytes(),
                DecodeCheckMode::Enforce,
            )
            .expect("valid volatile FP bytes must pass the actual stream gate");
            let error = run_decode_check(
                &A64DecodeCheck,
                &items,
                &(expected ^ (1 << 22)).to_le_bytes(),
                DecodeCheckMode::Enforce,
            )
            .expect_err(
                "wrong load/store direction must fail the actual stream gate, not be allowlisted",
            );
            assert!(error.message.contains(if load {
                "VolatileLdrRI"
            } else {
                "VolatileStrRI"
            }));
            assert!(error.message.contains("opc"), "wrong failure: {error}");
            streams += 1;
        }
    }
    assert_eq!((lengths, streams), (48, 8));
}

#[path = "common/fresh_dir.rs"]
mod fresh_dir;
