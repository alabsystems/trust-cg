// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Ordinary intent and emitted-word consumers on an unchanged stack budget.
//! These exact regression controls add no decoded form or formal proof credit.

use std::thread;

use trust_cg_codegen::aarch64::decode_check::{A64_UNDECODED_FAMILY, A64DecodeCheck};
use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_codegen::decode_check::{
    AllowlistPolicy, DecodeCheck, DecodeCheckItem, DecodeCheckMode, DecodeCheckOutcome, FixupHole,
    FixupHoleKind, UNDECODED_EMISSION_REFUSAL_TAG, run_decode_check_with_allowlist_policy,
};
use trust_cg_ir::{AArch64Opcode as Op, MachInst, MachOperand, SpecialReg};
use trust_cg_verify::aarch64_value_decode_proofs::{
    A64Decision, A64Dest, A64Operand, A64RefusalClass, A64ValueCheckError, A64ValueForm,
    A64ValueVerdict, CAPTURED_A64_VALUE_WORDS, a64_value_intent, check_emitted_a64_value_word,
};

const SMALL_STACK_BYTES: usize = 256 * 1024;

// Pin the pre-split supported opcode census, not merely the current dispatcher.
const INTENT_OPCODES: [Op; 16] = [
    Op::MovR,
    Op::MOVWrr,
    Op::MOVXrr,
    Op::FmovFprFpr,
    Op::FmovFprGpr,
    Op::FmovGprFpr,
    Op::NeonOrrV,
    Op::Smull,
    Op::Bfm,
    Op::Rbit,
    Op::AddRIShift12,
    Op::Mrs,
    Op::FcvtHS,
    Op::FcvtHD,
    Op::FcvtSH,
    Op::FcvtDH,
];

fn on_small_stack(name: &str, run: impl FnOnce() + Send + 'static) {
    thread::Builder::new()
        .name(name.into())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(run)
        .expect("spawn ordinary verifier consumer")
        .join()
        .expect("ordinary verifier consumer completed");
}

fn inst(opcode: Op, operands: &[A64Operand]) -> MachInst {
    MachInst::new(opcode, operands.iter().map(|op| op.mach()).collect())
}

#[test]
fn every_original_intent_form_and_enc5_consumer_runs_on_256kib_stack() {
    on_small_stack("a64-value-intent-corpus-256kib", || {
        let mut opcodes = Vec::new();
        let mut forms = Vec::new();
        // All construction, expression destruction, encoding and verification
        // happen in this thread. There is no parent compiler call or warm-up.
        for captured in CAPTURED_A64_VALUE_WORDS {
            let instruction = captured.inst();
            let intent = a64_value_intent(&instruction).expect("captured intent");
            assert_eq!(intent.form, Some(captured.form), "{instruction:?}");
            let width = match intent.dest {
                A64Dest::Fpr(_) => 128,
                A64Dest::Gpr(_) | A64Dest::Sp | A64Dest::Discarded => 64,
                A64Dest::SystemRegister(_) => panic!("value corpus cannot write a system register"),
            };
            assert_eq!(intent.value.bv_width(), width, "{instruction:?}");
            let instance = matches!(
                captured.form,
                A64ValueForm::Smull
                    | A64ValueForm::AddLsl12W
                    | A64ValueForm::AddLsl12X
                    | A64ValueForm::FcvtSFromH
                    | A64ValueForm::FcvtDFromH
                    | A64ValueForm::FcvtHFromS
                    | A64ValueForm::FcvtHFromD
            );
            let expected = if instance {
                assert!(
                    matches!(intent.decision, A64Decision::InstanceOf { form, .. } if form == captured.form)
                );
                A64ValueVerdict::InstanceOf(captured.form)
            } else {
                assert_eq!(intent.decision, A64Decision::ExactRouting);
                A64ValueVerdict::Exact
            };
            assert_eq!(encode_instruction(&instruction).unwrap(), captured.word);
            assert_eq!(
                check_emitted_a64_value_word(&instruction, captured.word).unwrap(),
                expected,
                "{instruction:?}"
            );
            assert!(matches!(
                A64DecodeCheck.check_one(&instruction, &captured.word.to_le_bytes(), None),
                DecodeCheckOutcome::Match
            ));

            // Bit zero is always part of Rd/Rt: pin destination refutation
            // for every original captured word, including the SP destination.
            let wrong_word = captured.word ^ 1;
            assert!(
                matches!(
                    check_emitted_a64_value_word(&instruction, wrong_word),
                    Err(A64ValueCheckError::Refuted(error)) if error.class == A64RefusalClass::Destination
                ),
                "{instruction:?} = {wrong_word:#010x}"
            );
            assert!(matches!(
                A64DecodeCheck.check_one(&instruction, &wrong_word.to_le_bytes(), None),
                DecodeCheckOutcome::Mismatch(_)
            ));
            if !opcodes.contains(&instruction.opcode) {
                opcodes.push(instruction.opcode);
            }
            if !forms.contains(&captured.form) {
                forms.push(captured.form);
            }
        }
        assert_eq!(opcodes.len(), INTENT_OPCODES.len());
        assert!(INTENT_OPCODES.iter().all(|opcode| opcodes.contains(opcode)));
        assert_eq!(forms.len(), 30);
        assert_eq!(forms.len(), A64ValueForm::ALL.len());
        assert!(A64ValueForm::ALL.iter().all(|form| forms.contains(form)));
    });
}

#[test]
fn every_intent_family_preserves_refusal_precedence_on_256kib_stack() {
    on_small_stack("a64-value-intent-refusals-256kib", || {
        for opcode in INTENT_OPCODES {
            let expected = match opcode {
                Op::NeonOrrV => {
                    "ORR (vector) with 0 operands (expected 3, or 4 with a selector)".to_owned()
                }
                Op::Bfm => format!("{opcode:?} with 0 operands (expected 4)"),
                Op::Smull | Op::AddRIShift12 => {
                    format!("{opcode:?} with 0 operands (expected 3)")
                }
                _ => format!("{opcode:?} with 0 operands (expected 2)"),
            };
            assert_eq!(
                a64_value_intent(&MachInst::new(opcode, Vec::new())).unwrap_err(),
                A64ValueCheckError::OutOfModel(expected)
            );
        }
        for opcode in [Op::Ret, Op::AddRR, Op::NeonAndV] {
            assert_eq!(
                a64_value_intent(&MachInst::new(opcode, Vec::new())).unwrap_err(),
                A64ValueCheckError::OutOfModel(format!("{opcode:?} is not a decoded value opcode"))
            );
        }
        // Width refuses before SP/immediate checks, as in the original arm.
        let bad_bfm = inst(
            Op::Bfm,
            &[
                A64Operand::W(3),
                A64Operand::Sp,
                A64Operand::Imm(100),
                A64Operand::Imm(100),
            ],
        );
        assert_eq!(
            a64_value_intent(&bad_bfm).unwrap_err(),
            A64ValueCheckError::IllFormed("BFM register widths differ".into())
        );
        // The opcode's nominal width, not an X view, rejects SP in MOVWrr.
        let bad_typed = inst(Op::MOVWrr, &[A64Operand::X(3), A64Operand::Sp]);
        assert_eq!(
            a64_value_intent(&bad_typed).unwrap_err(),
            A64ValueCheckError::OutOfModel("MOVWrr naming WSP".into())
        );
        // ADD's ZR/SP identity check still precedes its immediate check.
        let bad_add = inst(
            Op::AddRIShift12,
            &[A64Operand::Xzr, A64Operand::X(7), A64Operand::Imm(4096)],
        );
        assert_eq!(
            a64_value_intent(&bad_add).unwrap_err(),
            A64ValueCheckError::IllFormed(
                "register 31 names SP in ADD (immediate); a zero register cannot be encoded".into()
            )
        );
        // Non-physical operands do not acquire an encoding/register identity.
        let bad_operand = MachInst::new(
            Op::MovR,
            vec![
                MachOperand::Special(SpecialReg::XZR),
                MachOperand::FImm(1.0),
            ],
        );
        assert_eq!(
            a64_value_intent(&bad_operand).unwrap_err(),
            A64ValueCheckError::OutOfModel("unmodeled operand FImm(1.0)".into())
        );
    });
}

#[test]
fn modeled_copy_shapes_keep_form_boundaries_and_exact_verdicts_on_256kib_stack() {
    on_small_stack("a64-value-intent-uncredited-256kib", || {
        let cases = [
            // A discarded write is decidable, not a new registered form.
            (
                inst(Op::MovR, &[A64Operand::Xzr, A64Operand::X(5)]),
                0xAA05_03FF,
            ),
            (
                inst(Op::FmovFprFpr, &[A64Operand::H(3), A64Operand::H(7)]),
                0x1EE0_40E3,
            ),
            // The unselected 8B ORR copies low bits and clears the upper half.
            (
                inst(
                    Op::NeonOrrV,
                    &[A64Operand::D(3), A64Operand::D(7), A64Operand::D(7)],
                ),
                0x0EA7_1CE3,
            ),
        ];
        for (instruction, word) in cases {
            let intent = a64_value_intent(&instruction).unwrap();
            assert_eq!(intent.form, None);
            assert_eq!(intent.decision, A64Decision::ExactRouting);
            assert_eq!(
                check_emitted_a64_value_word(&instruction, word).unwrap(),
                A64ValueVerdict::Exact
            );
        }
        // A W->X view copy reads at the destination's original width and
        // retains the original MovX form rather than losing its form binding.
        let widening = inst(Op::MovR, &[A64Operand::X(3), A64Operand::W(7)]);
        assert_eq!(
            a64_value_intent(&widening).unwrap().form,
            Some(A64ValueForm::MovX)
        );
        assert_eq!(
            check_emitted_a64_value_word(&widening, 0xAA07_03E3).unwrap(),
            A64ValueVerdict::Exact
        );
        let different_registers = inst(
            Op::NeonOrrV,
            &[A64Operand::Q(3), A64Operand::Q(7), A64Operand::Q(8)],
        );
        assert_eq!(
            a64_value_intent(&different_registers).unwrap_err(),
            A64ValueCheckError::OutOfModel(
                "ORR (vector) of two different registers is a bitwise OR, not a copy".into()
            )
        );
    });
}

#[test]
fn mandatory_bindings_and_structural_policy_stay_ordered_on_256kib_stack() {
    on_small_stack("a64-decode-stage-boundary-256kib", || {
        // Each word is pinned independently of the current encoder; each
        // corrupted word must fail at its original mandatory binding, before
        // the independently structural decoder's possible disagreement.
        let bound = [
            (
                inst(Op::MovR, &[A64Operand::X(3), A64Operand::X(7)]),
                0xAA07_03E3u32,
                "aarch64_value_decode_proofs rejected",
            ),
            (
                inst(Op::Movz, &[A64Operand::X(0), A64Operand::Imm(0x1234)]),
                0xD282_4680,
                "the instruction-derived obligation decodes",
            ),
            (
                inst(
                    Op::StpRI,
                    &[
                        A64Operand::X(0),
                        A64Operand::X(1),
                        A64Operand::Sp,
                        A64Operand::Imm(0),
                    ],
                ),
                0xA900_07E0,
                "the memory-effect obligations carry",
            ),
            (
                inst(
                    Op::NeonExtV,
                    &[
                        A64Operand::Q(0),
                        A64Operand::Q(1),
                        A64Operand::Q(2),
                        A64Operand::Imm(12),
                    ],
                ),
                0x6E02_6020,
                "the NEON lane-effect obligations carry",
            ),
            (
                inst(
                    Op::NeonAndV,
                    &[A64Operand::Q(0), A64Operand::Q(1), A64Operand::Q(2)],
                ),
                0x4E22_1C20,
                "does not encode the bound 16B intent",
            ),
        ];
        for (instruction, word, binding) in bound {
            assert_eq!(encode_instruction(&instruction).unwrap(), word);
            assert!(
                matches!(
                    A64DecodeCheck.check_one(&instruction, &word.to_le_bytes(), None),
                    DecodeCheckOutcome::Match
                ),
                "{instruction:?}"
            );
            match A64DecodeCheck.check_one(&instruction, &(word ^ 1).to_le_bytes(), None) {
                DecodeCheckOutcome::Mismatch(error) => {
                    assert!(
                        error.message.contains(binding),
                        "{instruction:?}: {}",
                        error.message
                    );
                }
                other => panic!("{instruction:?}: original binding did not refuse: {other:?}"),
            }
        }

        let ret = inst(Op::Ret, &[]);
        assert!(matches!(
            A64DecodeCheck.check_one(&ret, &0xD65F_03C0u32.to_le_bytes(), None),
            DecodeCheckOutcome::Match
        ));
        match A64DecodeCheck.check_one(&ret, &[0; 3], None) {
            DecodeCheckOutcome::Mismatch(error) => assert_eq!(
                error.message,
                "instruction byte range is 3 bytes; AArch64 instructions are exactly 4"
            ),
            other => panic!("bad byte length did not refuse: {other:?}"),
        }
        let fp = inst(Op::FmovFprFpr, &[A64Operand::D(3), A64Operand::D(7)]);
        let hole = FixupHole {
            offset_in_inst: 0,
            width: 4,
            kind: FixupHoleKind::GlobalRef,
        };
        match A64DecodeCheck.check_one(&fp, &0x1E60_40E3u32.to_le_bytes(), Some(&hole)) {
            DecodeCheckOutcome::Mismatch(error) => assert_eq!(
                error.message,
                "FmovFprFpr is an FP/SIMD word and cannot contain a relocation hole"
            ),
            other => panic!("FP relocation hole did not refuse: {other:?}"),
        }

        // Unsupported emissions retain a named structural allowlist verdict,
        // and proof-grade Refuse policy still rejects that same verdict.
        let retained = inst(Op::Retain, &[A64Operand::X(0)]);
        let bytes = 0xD503_201Fu32.to_le_bytes();
        assert!(matches!(
            A64DecodeCheck.check_one(&retained, &bytes, None),
            DecodeCheckOutcome::Allowlisted(reason) if reason == A64_UNDECODED_FAMILY
        ));
        let items = [DecodeCheckItem {
            start: 0,
            end: bytes.len(),
            intent: retained,
            hole: None,
        }];
        assert!(
            run_decode_check_with_allowlist_policy(
                &A64DecodeCheck,
                &items,
                &bytes,
                DecodeCheckMode::Enforce,
                AllowlistPolicy::Count
            )
            .is_ok()
        );
        let error = run_decode_check_with_allowlist_policy(
            &A64DecodeCheck,
            &items,
            &bytes,
            DecodeCheckMode::Enforce,
            AllowlistPolicy::Refuse,
        )
        .unwrap_err();
        assert!(error.message.contains(UNDECODED_EMISSION_REFUSAL_TAG));
        assert!(error.message.contains(A64_UNDECODED_FAMILY));
    });
}
