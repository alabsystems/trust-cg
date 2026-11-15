// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Public single-word encoding on the consumer's unchanged stack budget.
//! Exact words and typed refusals are regression controls, not native proof.

use std::thread;

use trust_cg_codegen::aarch64::encode::{EncodeError, encode_instruction};
use trust_cg_ir::inst::{AArch64Opcode as Op, MachInst};
use trust_cg_ir::operand::MachOperand as Arg;
use trust_cg_ir::regs::{D0, D1, D2, PReg, SP, V0, V1, V2, W0, W1, X0, X1, X2};

const SMALL_STACK_BYTES: usize = 256 * 1024;

fn reg(register: PReg) -> Arg {
    Arg::PReg(register)
}

fn imm(value: i64) -> Arg {
    Arg::Imm(value)
}

fn inst(opcode: Op, operands: Vec<Arg>) -> MachInst {
    MachInst::new(opcode, operands)
}

#[test]
fn every_encoder_family_keeps_exact_words_on_256kib_stack() {
    thread::Builder::new()
        .name("aarch64-encoder-families-256kib".into())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(|| {
            // One independent exact-word control for every generated family.
            // These constants exercise the public dispatcher, not helpers or
            // a second encoder. No parent encode call warms any route.
            let cases = [
                (
                    inst(Op::AddRR, vec![reg(X0), reg(X1), reg(X2)]),
                    0x8b02_0020,
                ),
                (
                    inst(Op::AndRR, vec![reg(X0), reg(X1), reg(X2)]),
                    0x8a02_0020,
                ),
                (
                    inst(Op::LslRR, vec![reg(X0), reg(X1), reg(X2)]),
                    0x9ac2_2020,
                ),
                (inst(Op::CmpRR, vec![reg(X1), reg(X2)]), 0xeb02_003f),
                (inst(Op::MovR, vec![reg(X0), reg(X1)]), 0xaa01_03e0),
                (inst(Op::LdrRI, vec![reg(X0), reg(X1), imm(8)]), 0xf940_0420),
                (inst(Op::Ret, vec![]), 0xd65f_03c0),
                (inst(Op::Sxtw, vec![reg(X0), reg(X1)]), 0x9340_7c20),
                (inst(Op::Adrp, vec![reg(X0), imm(0)]), 0x9000_0000),
                (
                    inst(Op::FaddRR, vec![reg(D0), reg(D1), reg(D2)]),
                    0x1e62_2820,
                ),
                (
                    inst(Op::AddsRR, vec![reg(X0), reg(X1), reg(X2)]),
                    0xab02_0020,
                ),
                (inst(Op::Adc, vec![reg(X0), reg(X1), reg(X2)]), 0x9a02_0020),
                (
                    inst(Op::Csel, vec![reg(X0), reg(X1), reg(X2), imm(0)]),
                    0x9a82_0020,
                ),
                (
                    inst(Op::NeonSmaxV, vec![reg(V0), reg(V1), reg(V2), imm(5)]),
                    0x4ea2_6420,
                ),
                (inst(Op::Ldar, vec![reg(X0), reg(X1)]), 0xc8df_fc20),
                (inst(Op::Mrs, vec![reg(X0), imm(0xde82)]), 0xd53b_d040),
                (inst(Op::Brk, vec![]), 0xd420_0020),
                (
                    inst(Op::Ubfm, vec![reg(X0), reg(X1), imm(0), imm(31)]),
                    0xd340_7c20,
                ),
                (
                    inst(Op::LdrRO, vec![reg(X0), reg(X1), reg(X2)]),
                    0xf862_6820,
                ),
                (
                    inst(Op::LdrGot, vec![reg(X0), reg(X1), imm(0)]),
                    0xf940_0020,
                ),
                (
                    inst(Op::AndRI, vec![reg(X0), reg(X1), imm(0xff)]),
                    0x9240_1c20,
                ),
                (
                    inst(Op::BicRR, vec![reg(X0), reg(X1), reg(X2)]),
                    0x8a22_0020,
                ),
                (
                    inst(Op::Csinc, vec![reg(X0), reg(X1), reg(X2), imm(0)]),
                    0x9a82_0420,
                ),
                (inst(Op::Movn, vec![reg(X0), imm(0)]), 0x9280_0000),
                (
                    inst(Op::FmovImm, vec![reg(D0), Arg::FImm(1.0)]),
                    0x1e6e_1000,
                ),
                (inst(Op::MOVWrr, vec![reg(W0), reg(W1)]), 0x2a01_03e0),
            ];
            for (instruction, expected) in cases {
                assert_eq!(
                    encode_instruction(&instruction).unwrap(),
                    expected,
                    "{instruction:?}",
                );
            }
            // Both original guarded opcode arms retain their routing order.
            assert_eq!(
                encode_instruction(&inst(Op::SubsRR, vec![reg(X0), reg(SP), reg(X2)])).unwrap(),
                0xeb22_63e0,
            );
            assert_eq!(
                encode_instruction(&inst(Op::SubsRR, vec![reg(X0), reg(X1), reg(X2)])).unwrap(),
                0xeb02_0020,
            );
            assert_eq!(
                encode_instruction(&inst(Op::Brk, vec![imm(0x534c)])).unwrap(),
                0xd42a_6980,
            );
        })
        .expect("spawn bounded public encoder")
        .join()
        .expect("bounded public encoding must complete");
}

#[test]
fn every_encoder_family_keeps_typed_refusals_on_256kib_stack() {
    thread::Builder::new()
        .name("aarch64-encoder-refusals-256kib".into())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(|| {
            // Malformed shapes cross the same family boundaries as successes.
            // B's optional immediate and Ret's fixed encoding are controlled
            // instead by an explicit out-of-range branch, not missing operands.
            for opcode in [
                Op::AddRR,
                Op::AndRR,
                Op::LslRR,
                Op::CmpRR,
                Op::MovR,
                Op::LdrRI,
                Op::Sxtw,
                Op::Adrp,
                Op::FaddRR,
                Op::AddsRR,
                Op::Adc,
                Op::Csel,
                Op::NeonSmaxV,
                Op::Ldar,
                Op::Mrs,
                Op::Ubfm,
                Op::LdrRO,
                Op::LdrGot,
                Op::AndRI,
                Op::BicRR,
                Op::Csinc,
                Op::Movn,
                Op::FmovImm,
                Op::MOVWrr,
            ] {
                let instruction = inst(opcode, vec![]);
                let error = encode_instruction(&instruction).unwrap_err();
                assert!(
                    matches!(
                        error,
                        EncodeError::MissingOperand { .. } | EncodeError::InvalidOperand { .. }
                    ),
                    "{opcode:?} changed its operand-refusal class: {error:?}",
                );
            }
            for (opcode, operands, index) in [
                (Op::B, vec![imm(1_i64 << 25)], 0),
                (Op::Brk, vec![imm(-1)], 0),
                (Op::SubsRR, vec![reg(X0), reg(SP), reg(W1)], 2),
                (Op::Movn, vec![reg(X0), imm(0), imm(16)], 2),
                (Op::NeonSmaxV, vec![reg(V0), reg(V1), reg(V2), imm(7)], 3),
            ] {
                assert!(
                    matches!(
                        encode_instruction(&inst(opcode, operands)),
                        Err(EncodeError::InvalidOperand { opcode: actual, index: actual_index, .. })
                            if actual == opcode && actual_index == index
                    ),
                    "{opcode:?} must preserve its exact refusing operand",
                );
            }
            // Arity remains first for move-wide; compare and guarded SP forms
            // retain their original operand validation order as well.
            assert!(matches!(
                encode_instruction(&inst(Op::Movz, vec![reg(D0), imm(0), imm(0), imm(0)])),
                Err(EncodeError::InvalidOperand { index: 3, .. }),
            ));
            assert!(matches!(
                encode_instruction(&inst(Op::CmpRR, vec![reg(D0), reg(X1)])),
                Err(EncodeError::InvalidOperand { index: 0, .. }),
            ));
            for opcode in [Op::TrapBoundsCheckExact, Op::LlscRmw64, Op::LlscCmpSwap128] {
                assert!(matches!(
                    encode_instruction(&inst(opcode, vec![])),
                    Err(EncodeError::PseudoInstruction(actual)) if actual == opcode,
                ));
            }
            for opcode in [Op::AddTprelHi12, Op::LdrGottprel, Op::TlsDescCall] {
                assert!(matches!(
                    encode_instruction(&inst(opcode, vec![])),
                    Err(EncodeError::UnsupportedOpcode(actual)) if actual == opcode,
                ));
            }
        })
        .expect("spawn bounded refusal consumer")
        .join()
        .expect("bounded typed refusals must complete");
}
