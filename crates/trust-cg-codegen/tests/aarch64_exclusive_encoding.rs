// Copyright 2026 Andrew Yates | Apache-2.0
//! Exact LDAXR/STLXR and baseline LL/SC exclusive/CLREX encoder boundary.
//! Arm DDI0602 (aarchmrs v2025-03), LDAXR pp469–470 / STLXR pp898–900:
//! https://documentation-service.arm.com/static/67e40f3398aa3c3b6eea6a85
//! GNU as 2.42 independently supplies the pinned words. The separate lift
//! decoder checks every register tuple; neither agreement nor native testing
//! is formal verification or an exclusive-monitor/progress proof.

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_ir::{
    inst::{AArch64Opcode as Op, MachInst},
    operand::MachOperand as Arg,
    regs::{self, PReg, SpecialReg},
};
use trust_cg_lift::disasm::aarch64::{
    ClearExclusive, DecodeError, Instruction, LoadStoreExclusive, LoadStoreExclusivePair, decode,
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

fn instruction(opcode: Op, operands: Vec<Arg>) -> MachInst {
    MachInst::new(opcode, operands)
}

fn gpr(width: u16, number: u16) -> Arg {
    Arg::PReg(if number == 31 {
        if width == 64 { regs::XZR } else { regs::WZR }
    } else {
        PReg::new(number + if width == 32 { 32 } else { 0 })
    })
}

#[test]
fn exclusive_assembler_words_and_all_register_tuples() {
    let goldens = [
        (Op::Ldaxr, vec![gpr(32, 0), gpr(64, 1)], 0x885ffc20),
        (Op::Ldaxr, vec![gpr(64, 2), gpr(64, 3)], 0xc85ffc62),
        (
            Op::Ldaxr,
            vec![gpr(32, 31), Arg::PReg(regs::SP)],
            0x885fffff,
        ),
        (
            Op::Ldaxr,
            vec![gpr(64, 31), Arg::PReg(regs::SP)],
            0xc85fffff,
        ),
        (Op::Ldaxr, vec![gpr(64, 0), gpr(64, 0)], 0xc85ffc00),
        (
            Op::Stlxr,
            vec![gpr(32, 0), gpr(32, 1), gpr(64, 2)],
            0x8800fc41,
        ),
        (
            Op::Stlxr,
            vec![gpr(32, 3), gpr(64, 4), gpr(64, 5)],
            0xc803fca4,
        ),
        // GNU as 2.42 emits the correct word, but spuriously warns about the
        // WZR/SP hardware-number match. Arm explicitly exempts base n==31.
        (
            Op::Stlxr,
            vec![gpr(32, 31), gpr(64, 1), Arg::PReg(regs::SP)],
            0xc81fffe1,
        ),
        (
            Op::Stlxr,
            vec![gpr(32, 0), gpr(64, 31), Arg::PReg(regs::SP)],
            0xc800ffff,
        ),
        (
            Op::Stlxr,
            vec![gpr(32, 0), gpr(32, 31), gpr(64, 1)],
            0x8800fc3f,
        ),
        // Data/base overlap is legal; only the status overlaps are forbidden.
        (
            Op::Stlxr,
            vec![gpr(32, 0), gpr(64, 1), gpr(64, 1)],
            0xc800fc21,
        ),
    ];
    for (opcode, operands, expected) in goldens {
        assert_eq!(
            encode_instruction(&instruction(opcode, operands.clone())).unwrap(),
            expected
        );
        // Both canonical public representations of SP and ZR must agree.
        let special = operands
            .into_iter()
            .map(|arg| match arg {
                Arg::PReg(p) if p == regs::SP => Arg::Special(SpecialReg::SP),
                Arg::PReg(p) if p == regs::XZR => Arg::Special(SpecialReg::XZR),
                Arg::PReg(p) if p == regs::WZR => Arg::Special(SpecialReg::WZR),
                other => other,
            })
            .collect();
        assert_eq!(
            encode_instruction(&instruction(opcode, special)).unwrap(),
            expected
        );
    }

    let mut valid = 0;
    let mut rejected = 0;
    for width in [32, 64] {
        for data in 0..32 {
            for base in 0..32 {
                let address = Arg::PReg(PReg::new(base)); // X0..X30, SP
                let load = instruction(Op::Ldaxr, vec![gpr(width, data), address.clone()]);
                let decoded = decode(encode_instruction(&load).unwrap()).unwrap();
                assert!(
                    matches!(decoded, Instruction::LoadStoreExclusiveAcquireRelease(fields)
                    if fields.load && fields.size == if width == 64 { 3 } else { 2 }
                        && fields.rs == 31 && fields.rt == data as u8 && fields.rn == base as u8)
                );
                valid += 1;
                for status in 0..32 {
                    let store = instruction(
                        Op::Stlxr,
                        vec![gpr(32, status), gpr(width, data), address.clone()],
                    );
                    if status == data || (status == base && base != 31) {
                        assert!(
                            encode_instruction(&store).is_err(),
                            "constrained-unpredictable tuple: {store:?}"
                        );
                        // Mutate an independent architectural encoding into
                        // the bad tuple; the separate decoder also refuses it.
                        let word = (if width == 64 { 0xc800fc00 } else { 0x8800fc00 })
                            | ((status as u32) << 16)
                            | ((base as u32) << 5)
                            | data as u32;
                        assert!(matches!(
                            decode(word),
                            Err(DecodeError::ConstrainedUnpredictable { .. })
                        ));
                        rejected += 1;
                    } else {
                        let decoded = decode(encode_instruction(&store).unwrap()).unwrap();
                        assert!(
                            matches!(decoded, Instruction::LoadStoreExclusiveAcquireRelease(fields)
                            if !fields.load && fields.size == if width == 64 { 3 } else { 2 }
                                && fields.rs == status as u8 && fields.rt == data as u8 && fields.rn == base as u8)
                        );
                        valid += 1;
                    }
                }
            }
        }
    }
    assert_eq!((valid, rejected), (63_614, 3_970));
}

#[test]
fn exclusive_wrong_width_bank_sp_zr_and_arity_are_rejected() {
    let invalid = [
        instruction(Op::Ldaxr, vec![Arg::PReg(regs::D0), gpr(64, 1)]),
        instruction(Op::Ldaxr, vec![gpr(64, 0), gpr(32, 1)]),
        instruction(Op::Ldaxr, vec![Arg::PReg(regs::SP), gpr(64, 1)]),
        instruction(Op::Ldaxr, vec![gpr(64, 0), gpr(64, 31)]),
        instruction(Op::Stlxr, vec![gpr(64, 0), gpr(64, 1), gpr(64, 2)]),
        instruction(Op::Stlxr, vec![gpr(32, 0), Arg::PReg(regs::D1), gpr(64, 2)]),
        instruction(Op::Stlxr, vec![gpr(32, 0), gpr(64, 1), gpr(32, 2)]),
        instruction(
            Op::Stlxr,
            vec![Arg::PReg(regs::WSP), gpr(64, 1), gpr(64, 2)],
        ),
        instruction(Op::Stlxr, vec![gpr(32, 0), Arg::PReg(regs::SP), gpr(64, 2)]),
        instruction(Op::Stlxr, vec![gpr(32, 0), gpr(64, 1), gpr(64, 31)]),
    ];
    let wrongly_accepted: Vec<_> = invalid
        .iter()
        .filter_map(|inst| {
            encode_instruction(inst)
                .ok()
                .map(|word| format!("{inst:?} -> {word:08x}"))
        })
        .collect();
    assert!(
        wrongly_accepted.is_empty(),
        "invalid roles were silently aliased:\n{}",
        wrongly_accepted.join("\n")
    );

    for opcode in [Op::Ldaxr, Op::Stlxr] {
        let valid = if opcode == Op::Ldaxr {
            vec![gpr(64, 0), gpr(64, 1)]
        } else {
            vec![gpr(32, 0), gpr(64, 1), gpr(64, 2)]
        };
        for length in 0..valid.len() {
            assert!(encode_instruction(&instruction(opcode, valid[..length].to_vec())).is_err());
        }
        for extra in [Arg::Imm(0), Arg::Imm(1), gpr(64, 3)] {
            let mut operands = valid.clone();
            operands.push(extra);
            assert!(encode_instruction(&instruction(opcode, operands)).is_err());
        }
        for index in 0..valid.len() {
            for bad in [
                Arg::Imm(0),
                Arg::PReg(regs::V0),
                Arg::PReg(regs::S0),
                Arg::PReg(regs::H0),
                Arg::PReg(regs::B0),
                Arg::PReg(regs::NZCV),
                Arg::PReg(PReg::new(u16::MAX)),
                Arg::Symbol("bad".into()),
                Arg::MemOp {
                    base: regs::X0,
                    offset: 0,
                },
                Arg::PReg(regs::WSP),
                Arg::Special(SpecialReg::XZR),
                Arg::Special(SpecialReg::WZR),
                Arg::Special(SpecialReg::SP),
            ] {
                // ZR is legal data; WZR is also legal status; SP legal base.
                let base = valid.len() - 1;
                if (index == base && bad == Arg::Special(SpecialReg::SP))
                    || (index != base
                        && (bad == Arg::Special(SpecialReg::WZR)
                            || (bad == Arg::Special(SpecialReg::XZR)
                                && !(opcode == Op::Stlxr && index == 0))))
                {
                    continue;
                }
                let mut operands = valid.clone();
                operands[index] = bad;
                assert!(
                    encode_instruction(&instruction(opcode, operands.clone())).is_err(),
                    "{opcode:?}: {operands:?}"
                );
            }
        }
    }
}

/// Baseline LL/SC exclusives emitted by the post-RA LL/SC expansion
/// (`trust_cg_codegen::llsc`). Pinned words come from LLVM's integrated
/// assembler (`clang -target aarch64-apple-darwin -c`, Apple clang 21), not
/// from this encoder; the separate lift decoder then checks every register
/// tuple of every new form. Encoding/decoding agreement is not an
/// exclusive-monitor, ordering or progress proof.
#[test]
fn baseline_llsc_exclusive_assembler_words_and_all_register_tuples() {
    let sp = || Arg::PReg(regs::SP);
    let goldens = [
        (Op::Ldxr, vec![gpr(32, 0), gpr(64, 1)], 0x885f7c20),
        (Op::Ldxr, vec![gpr(64, 2), gpr(64, 3)], 0xc85f7c62),
        (Op::Ldxr, vec![gpr(32, 30), sp()], 0x885f7ffe),
        (Op::Ldxrb, vec![gpr(32, 4), gpr(64, 5)], 0x085f7ca4),
        (Op::Ldxrh, vec![gpr(32, 6), gpr(64, 7)], 0x485f7ce6),
        (Op::Ldaxrb, vec![gpr(32, 8), gpr(64, 9)], 0x085ffd28),
        (Op::Ldaxrh, vec![gpr(32, 10), gpr(64, 11)], 0x485ffd6a),
        (Op::Ldaxrb, vec![gpr(32, 31), sp()], 0x085fffff),
        (
            Op::Stxr,
            vec![gpr(32, 0), gpr(32, 1), gpr(64, 2)],
            0x88007c41,
        ),
        (
            Op::Stxr,
            vec![gpr(32, 3), gpr(64, 4), gpr(64, 5)],
            0xc8037ca4,
        ),
        (Op::Stxr, vec![gpr(32, 6), gpr(64, 31), sp()], 0xc8067fff),
        (
            Op::Stxrb,
            vec![gpr(32, 7), gpr(32, 8), gpr(64, 9)],
            0x08077d28,
        ),
        (
            Op::Stxrh,
            vec![gpr(32, 10), gpr(32, 11), gpr(64, 12)],
            0x480a7d8b,
        ),
        (
            Op::Stlxrb,
            vec![gpr(32, 13), gpr(32, 14), gpr(64, 15)],
            0x080dfdee,
        ),
        (
            Op::Stlxrh,
            vec![gpr(32, 16), gpr(32, 17), gpr(64, 18)],
            0x4810fe51,
        ),
        (Op::Stlxrb, vec![gpr(32, 31), gpr(32, 1), sp()], 0x081fffe1),
        (
            Op::Stxrh,
            vec![gpr(32, 0), gpr(32, 31), gpr(64, 1)],
            0x48007c3f,
        ),
        // Data/base overlap is legal; only status overlaps are forbidden.
        (
            Op::Stxr,
            vec![gpr(32, 0), gpr(64, 1), gpr(64, 1)],
            0xc8007c21,
        ),
        (Op::Clrex, vec![], 0xd5033f5f),
    ];
    for (opcode, operands, expected) in goldens {
        assert_eq!(
            encode_instruction(&instruction(opcode, operands.clone())).unwrap(),
            expected,
            "{opcode:?} {operands:?}"
        );
    }
    assert_eq!(
        decode(0xd5033f5f),
        Ok(Instruction::ClearExclusive(ClearExclusive { crm: 15 }))
    );

    // (opcode, W/X data widths, size field, ordered bit)
    let loads = [
        (Op::Ldxr, &[32, 64][..], None, false),
        (Op::Ldxrb, &[32][..], Some(0u8), false),
        (Op::Ldxrh, &[32][..], Some(1), false),
        (Op::Ldaxrb, &[32][..], Some(0), true),
        (Op::Ldaxrh, &[32][..], Some(1), true),
    ];
    let stores = [
        (Op::Stxr, &[32, 64][..], None, false),
        (Op::Stxrb, &[32][..], Some(0u8), false),
        (Op::Stxrh, &[32][..], Some(1), false),
        (Op::Stlxrb, &[32][..], Some(0), true),
        (Op::Stlxrh, &[32][..], Some(1), true),
    ];
    let size_of = |fixed: Option<u8>, width: u16| fixed.unwrap_or(if width == 64 { 3 } else { 2 });
    let mut valid = 0;
    let mut rejected = 0;
    for (opcode, widths, fixed, ordered) in loads {
        for &width in widths {
            for data in 0..32 {
                for base in 0..32 {
                    let load =
                        instruction(opcode, vec![gpr(width, data), Arg::PReg(PReg::new(base))]);
                    let decoded = decode(encode_instruction(&load).unwrap()).unwrap();
                    assert_eq!(
                        decoded,
                        Instruction::LoadStoreExclusive(LoadStoreExclusive {
                            size: size_of(fixed, width),
                            load: true,
                            ordered,
                            rs: 31,
                            rn: base as u8,
                            rt: data as u8,
                        }),
                        "{load:?}"
                    );
                    valid += 1;
                }
            }
        }
    }
    for (opcode, widths, fixed, ordered) in stores {
        for &width in widths {
            for status in 0..32 {
                for data in 0..32 {
                    for base in 0..32 {
                        let store = instruction(
                            opcode,
                            vec![
                                gpr(32, status),
                                gpr(width, data),
                                Arg::PReg(PReg::new(base)),
                            ],
                        );
                        if status == data || (status == base && base != 31) {
                            assert!(encode_instruction(&store).is_err(), "{store:?}");
                            rejected += 1;
                            continue;
                        }
                        let decoded = decode(encode_instruction(&store).unwrap()).unwrap();
                        assert_eq!(
                            decoded,
                            Instruction::LoadStoreExclusive(LoadStoreExclusive {
                                size: size_of(fixed, width),
                                load: false,
                                ordered,
                                rs: status as u8,
                                rn: base as u8,
                                rt: data as u8,
                            }),
                            "{store:?}"
                        );
                        valid += 1;
                    }
                }
            }
        }
    }
    // Loads: 6 data widths x 32 x 32. Stores: 6 x 32^3 tuples, of which each
    // width forbids 32*32 status==data plus 31*32 status==base (base != SP)
    // tuples, minus the 31 counted twice (status==data==base != SP): 1985.
    assert_eq!(
        (valid, rejected),
        (6 * 1024 + 6 * (32_768 - 1_985), 6 * 1_985)
    );
}

/// 128-bit pair exclusives emitted by the LL/SC pair expansion. LLVM's
/// integrated assembler supplies the pinned words; the separate lift decoder
/// checks every register tuple, and the constrained-unpredictable overlaps
/// (load `Rt == Rt2`, store status equal to a data register or a non-SP
/// base) are refused by the encoder.
#[test]
fn llsc_pair_exclusive_assembler_words_and_all_register_tuples() {
    let sp = || Arg::PReg(regs::SP);
    let goldens = [
        (
            Op::Ldxp,
            vec![gpr(64, 0), gpr(64, 1), gpr(64, 2)],
            0xc87f0440,
        ),
        (
            Op::Ldaxp,
            vec![gpr(64, 3), gpr(64, 4), gpr(64, 5)],
            0xc87f90a3,
        ),
        (Op::Ldxp, vec![gpr(64, 30), gpr(64, 31), sp()], 0xc87f7ffe),
        (
            Op::Ldaxp,
            vec![gpr(64, 31), gpr(64, 29), gpr(64, 28)],
            0xc87ff79f,
        ),
        (
            Op::Stxp,
            vec![gpr(32, 0), gpr(64, 1), gpr(64, 2), gpr(64, 3)],
            0xc8200861,
        ),
        (
            Op::Stlxp,
            vec![gpr(32, 4), gpr(64, 5), gpr(64, 6), gpr(64, 7)],
            0xc82498e5,
        ),
        (
            Op::Stxp,
            vec![gpr(32, 8), gpr(64, 31), gpr(64, 9), sp()],
            0xc82827ff,
        ),
        (
            Op::Stlxp,
            vec![gpr(32, 31), gpr(64, 10), gpr(64, 11), gpr(64, 12)],
            0xc83fad8a,
        ),
        (
            Op::Stxp,
            vec![gpr(32, 13), gpr(64, 14), gpr(64, 14), gpr(64, 14)],
            0xc82d39ce,
        ),
    ];
    for (opcode, operands, expected) in goldens {
        assert_eq!(
            encode_instruction(&instruction(opcode, operands.clone())).unwrap(),
            expected,
            "{opcode:?} {operands:?}"
        );
    }
    let (mut valid, mut rejected) = (0u64, 0u64);
    for (opcode, ordered) in [(Op::Ldxp, false), (Op::Ldaxp, true)] {
        for rt in 0..32 {
            for rt2 in 0..32 {
                for base in 0..32 {
                    let load = instruction(
                        opcode,
                        vec![gpr(64, rt), gpr(64, rt2), Arg::PReg(PReg::new(base))],
                    );
                    if rt == rt2 {
                        assert!(encode_instruction(&load).is_err(), "{load:?}");
                        rejected += 1;
                        continue;
                    }
                    assert_eq!(
                        decode(encode_instruction(&load).unwrap()).unwrap(),
                        Instruction::LoadStoreExclusivePair(LoadStoreExclusivePair {
                            wide: true,
                            load: true,
                            ordered,
                            rs: 31,
                            rt2: rt2 as u8,
                            rn: base as u8,
                            rt: rt as u8,
                        }),
                        "{load:?}"
                    );
                    valid += 1;
                }
            }
        }
    }
    for (opcode, ordered) in [(Op::Stxp, false), (Op::Stlxp, true)] {
        for status in 0..32 {
            for rt in 0..32 {
                for rt2 in 0..32 {
                    for base in 0..32 {
                        let store = instruction(
                            opcode,
                            vec![
                                gpr(32, status),
                                gpr(64, rt),
                                gpr(64, rt2),
                                Arg::PReg(PReg::new(base)),
                            ],
                        );
                        if status == rt || status == rt2 || (status == base && base != 31) {
                            assert!(encode_instruction(&store).is_err(), "{store:?}");
                            rejected += 1;
                            continue;
                        }
                        assert_eq!(
                            decode(encode_instruction(&store).unwrap()).unwrap(),
                            Instruction::LoadStoreExclusivePair(LoadStoreExclusivePair {
                                wide: true,
                                load: false,
                                ordered,
                                rs: status as u8,
                                rt2: rt2 as u8,
                                rn: base as u8,
                                rt: rt as u8,
                            }),
                            "{store:?}"
                        );
                        valid += 1;
                    }
                }
            }
        }
    }
    // Loads: 2 x (32^3 - 32*32 duplicate destinations). Stores: per status,
    // 31*31 data pairs avoid it, and 31 bases (32 for the WZR status, whose
    // SP base is exempt) avoid it: 2 x 993 x 961.
    assert_eq!(valid, 2 * (32_768 - 1_024) + 2 * 993 * 961);
    assert_eq!(rejected, 2 * 1_024 + 2 * (1_048_576 - 993 * 961));

    // Wrong banks, widths and arity are refused, never masked into a word.
    let invalid = [
        instruction(Op::Ldxp, vec![gpr(32, 0), gpr(64, 1), gpr(64, 2)]),
        instruction(Op::Ldxp, vec![gpr(64, 0), gpr(32, 1), gpr(64, 2)]),
        instruction(Op::Ldxp, vec![gpr(64, 0), gpr(64, 1), gpr(32, 2)]),
        instruction(Op::Ldxp, vec![gpr(64, 0), gpr(64, 1), gpr(64, 31)]),
        instruction(Op::Ldaxp, vec![Arg::PReg(regs::D0), gpr(64, 1), gpr(64, 2)]),
        instruction(Op::Ldaxp, vec![gpr(64, 0), gpr(64, 1)]),
        instruction(
            Op::Stxp,
            vec![gpr(64, 0), gpr(64, 1), gpr(64, 2), gpr(64, 3)],
        ),
        instruction(
            Op::Stxp,
            vec![gpr(32, 0), gpr(32, 1), gpr(64, 2), gpr(64, 3)],
        ),
        instruction(
            Op::Stlxp,
            vec![gpr(32, 0), gpr(64, 1), gpr(64, 2), gpr(64, 3), Arg::Imm(0)],
        ),
        instruction(Op::Stlxp, vec![gpr(32, 0), gpr(64, 1), gpr(64, 2)]),
    ];
    for inst in invalid {
        assert!(encode_instruction(&inst).is_err(), "{inst:?}");
    }
}

#[test]
fn baseline_llsc_exclusive_wrong_bank_width_and_arity_are_rejected() {
    let invalid = [
        // Byte/halfword exclusives take W data only.
        instruction(Op::Ldxrb, vec![gpr(64, 0), gpr(64, 1)]),
        instruction(Op::Ldaxrh, vec![gpr(64, 0), gpr(64, 1)]),
        instruction(Op::Stxrb, vec![gpr(32, 0), gpr(64, 1), gpr(64, 2)]),
        instruction(Op::Stlxrh, vec![gpr(32, 0), gpr(64, 1), gpr(64, 2)]),
        // Status must be a W register; address must be X or SP.
        instruction(Op::Stxr, vec![gpr(64, 0), gpr(64, 1), gpr(64, 2)]),
        instruction(Op::Stxrh, vec![gpr(32, 0), gpr(32, 1), gpr(32, 2)]),
        instruction(Op::Ldxr, vec![gpr(64, 0), gpr(32, 1)]),
        instruction(Op::Ldxr, vec![gpr(64, 0), gpr(64, 31)]),
        // Wrong banks.
        instruction(Op::Ldxr, vec![Arg::PReg(regs::D0), gpr(64, 1)]),
        instruction(Op::Stxrb, vec![gpr(32, 0), Arg::PReg(regs::S1), gpr(64, 2)]),
        instruction(Op::Ldaxrb, vec![Arg::PReg(regs::SP), gpr(64, 1)]),
        // Arity.
        instruction(Op::Ldxrh, vec![gpr(32, 0)]),
        instruction(Op::Stxr, vec![gpr(32, 0), gpr(64, 1)]),
        instruction(
            Op::Stlxrb,
            vec![gpr(32, 0), gpr(32, 1), gpr(64, 2), Arg::Imm(0)],
        ),
        instruction(Op::Clrex, vec![Arg::Imm(15)]),
    ];
    let wrongly_accepted: Vec<_> = invalid
        .iter()
        .filter_map(|inst| {
            encode_instruction(inst)
                .ok()
                .map(|word| format!("{inst:?} -> {word:08x}"))
        })
        .collect();
    assert!(
        wrongly_accepted.is_empty(),
        "invalid exclusive roles were silently aliased:\n{}",
        wrongly_accepted.join("\n")
    );
    // The opaque LL/SC pseudos never encode.
    for opcode in [
        Op::LlscRmw8,
        Op::LlscRmw16,
        Op::LlscRmw32,
        Op::LlscRmw64,
        Op::LlscCmpSwap8,
        Op::LlscCmpSwap16,
        Op::LlscCmpSwap32,
        Op::LlscCmpSwap64,
        Op::LlscLoad128,
        Op::LlscStore128,
        Op::LlscRmw128,
        Op::LlscCmpSwap128,
    ] {
        assert!(matches!(
            encode_instruction(&instruction(opcode, vec![])),
            Err(trust_cg_codegen::aarch64::encode::EncodeError::PseudoInstruction(op)) if op == opcode
        ));
    }
}

#[test]
#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
fn native_existing_exclusive_words_success_and_monitor_failure() {
    use std::{fmt::Write, fs, process::Command};
    // These are direct encoder words in independently assembled leaf routines,
    // not LIR atomics or a newly admitted frontend/pipeline lowering. Correct
    // values in one thread do not prove the concurrent memory-order model.
    let mut assembly = String::from(".text\n");
    for width in [32, 64] {
        let load =
            encode_instruction(&instruction(Op::Ldaxr, vec![gpr(width, 2), gpr(64, 0)])).unwrap();
        let store = encode_instruction(&instruction(
            Op::Stlxr,
            vec![gpr(32, 3), gpr(width, 1), gpr(64, 0)],
        ))
        .unwrap();
        let bank = if width == 32 { "w" } else { "x" };
        writeln!(assembly, ".global cg_exchange{width}\n.type cg_exchange{width},%function\ncg_exchange{width}:\n1: .inst 0x{load:08x}\n.inst 0x{store:08x}\ncbnz w3,1b\nmov {bank}0,{bank}2\nret\n.size cg_exchange{width},.-cg_exchange{width}").unwrap();
        writeln!(assembly, ".global cg_failure{width}\n.type cg_failure{width},%function\ncg_failure{width}:\n.inst 0x{load:08x}\nclrex\n.inst 0x{store:08x}\nmov w0,w3\nret\n.size cg_failure{width},.-cg_failure{width}").unwrap();
    }
    assembly.push_str(".section .note.GNU-stack,\"\",%progbits\n");
    const DRIVER: &str = r#"
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
struct word32 { _Alignas(16) _Atomic uint32_t value; unsigned char guard[12]; };
struct word64 { _Alignas(16) _Atomic uint64_t value; unsigned char guard[8]; };
_Static_assert(sizeof(struct word32)==16 && sizeof(struct word64)==16,"guard layout");
extern uint32_t cg_exchange32(_Atomic uint32_t*,uint32_t);
extern uint64_t cg_exchange64(_Atomic uint64_t*,uint64_t);
extern uint64_t cg_failure32(_Atomic uint32_t*,uint32_t);
extern uint64_t cg_failure64(_Atomic uint64_t*,uint64_t);
static unsigned checks;
static int check(uint64_t actual,uint64_t expected,unsigned width,unsigned seed,const char*mode){
 if(actual!=expected){printf("FAIL width=%u seed=%u mode=%s actual=%016lx expected=%016lx\n",width,seed,mode,actual,expected);return 1;}checks++;return 0;
}
__attribute__((noinline)) static uint32_t c_exchange32(_Atomic uint32_t*p,uint32_t x){return atomic_exchange_explicit(p,x,memory_order_seq_cst);}
__attribute__((noinline)) static uint64_t c_exchange64(_Atomic uint64_t*p,uint64_t x){return atomic_exchange_explicit(p,x,memory_order_seq_cst);}
#define CASE(BITS,SEED,INITIAL,DESIRED) do { \
 struct word##BITS actual,control; \
 unsigned char guards[sizeof(actual.guard)];memset(guards,0xa7,sizeof(guards)); \
 atomic_init(&actual.value,(uint##BITS##_t)(INITIAL));atomic_init(&control.value,(uint##BITS##_t)(INITIAL)); \
 memcpy(actual.guard,guards,sizeof(guards));memcpy(control.guard,guards,sizeof(guards)); \
 uint##BITS##_t old=cg_exchange##BITS(&actual.value,(uint##BITS##_t)(DESIRED)); \
 uint##BITS##_t reference=c_exchange##BITS(&control.value,(uint##BITS##_t)(DESIRED)); \
 if(check(old,(uint##BITS##_t)(INITIAL),BITS,SEED,"CG old")||check(reference,(uint##BITS##_t)(INITIAL),BITS,SEED,"C old"))return 1; \
 if(check(atomic_load(&actual.value),(uint##BITS##_t)(DESIRED),BITS,SEED,"CG stored")||check(atomic_load(&control.value),(uint##BITS##_t)(DESIRED),BITS,SEED,"C stored"))return 2; \
 if(check(cg_failure##BITS(&actual.value,(uint##BITS##_t)~(DESIRED)),1,BITS,SEED,"cleared monitor status")||check(atomic_load(&actual.value),(uint##BITS##_t)(DESIRED),BITS,SEED,"failed store nonmutation"))return 3; \
 if(check(memcmp(actual.guard,guards,sizeof(guards)),0,BITS,SEED,"CG guards")||check(memcmp(control.guard,guards,sizeof(guards)),0,BITS,SEED,"C guards"))return 4; \
} while(0)
int main(void){
 uint64_t state=UINT64_C(0x8abced0198765432);
 for(unsigned seed=0;seed<64;seed++){
  uint64_t initial=seed<4?(uint64_t[]){0,UINT64_MAX,UINT64_C(0x8000000080000000),UINT64_C(0x7fffffff7fffffff)}[seed]:state;
  state=state*UINT64_C(6364136223846793005)+1;
  uint64_t desired=~state;
  CASE(32,seed,initial,desired);CASE(64,seed,initial,desired);
 }
 printf("PASS %u exclusive value/guard checks\n",checks);return 0;
}
"#;
    for opt in ["-O0", "-O2"] {
        let dir = fresh_dir::create("trust-cg-exclusive-native-");
        fs::write(dir.join("exclusive.S"), native_host::assembly(&assembly)).unwrap();
        fs::write(dir.join("driver.c"), DRIVER).unwrap();
        let binary = dir.join("driver");
        let link = process::command_output_with_timeout(
            Command::new("cc")
                .arg(opt)
                .arg("-march=armv8-a")
                .arg("-mno-outline-atomics")
                .arg(dir.join("exclusive.S"))
                .arg(dir.join("driver.c"))
                .arg("-o")
                .arg(&binary),
            process::codegen_link_timeout(),
        )
        .unwrap();
        assert!(
            !link.timed_out && link.output.status.success(),
            "{opt} files={dir:?}: {}",
            String::from_utf8_lossy(&link.output.stderr)
        );
        let run =
            process::run_executable_with_timeout(&binary, process::codegen_run_timeout()).unwrap();
        assert!(
            !run.timed_out && run.output.status.success(),
            "{opt} files={dir:?}: {} {}",
            String::from_utf8_lossy(&run.output.stdout),
            String::from_utf8_lossy(&run.output.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&run.output.stdout).trim(),
            "PASS 1024 exclusive value/guard checks",
            "files={dir:?}"
        );
        eprintln!(
            "{opt}: {}",
            String::from_utf8_lossy(&run.output.stdout).trim()
        );
        fs::remove_dir_all(&dir).unwrap();
    }
}
