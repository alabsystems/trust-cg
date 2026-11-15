// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
use super::*;
use crate::source_bound_frame::source_bound_frame;
use trust_cg_ir::function::{Signature, Type};
use trust_cg_ir::regs::{PReg, W0, X0, X1, X19, X29, X30};
use trust_cg_ir::{InstFlags, MachFunction, MachInst};
use trust_cg_lower::function::{BasicBlock, Function};
use trust_cg_lower::instructions::{Instruction, Opcode, Value};

/// A checked framed leaf whose single body instruction is `opcode` over the
/// incoming arguments: the source-bound frame and arithmetic replay vehicle,
/// also used by the function-request authority transport tests.
pub(crate) fn fixture(bits: u32, opcode: M, operand: O) -> (Function, MachFunction) {
    let ty = if bits == 32 {
        trust_cg_lower::Type::I32
    } else {
        trust_cg_lower::Type::I64
    };
    let mt = if bits == 32 { Type::I32 } else { Type::I64 };
    let reg = |index: u16| O::PReg(PReg::new(index + if bits == 32 { 32 } else { 0 }));
    let mut source = Function::new(
        "arithmetic",
        trust_cg_lower::function::Signature {
            params: vec![ty.clone(); 2],
            returns: vec![ty.clone()],
        },
    );
    let mut instructions = Vec::new();
    let mut result = Value(0);
    let mut push = |opcode, args| {
        let result = Value(instructions.len() as u32 + 2);
        instructions.push(Instruction {
            opcode,
            args,
            results: vec![result],
        });
        result
    };
    if opcode == M::LslRI {
        let O::Imm(shift) = operand else {
            unreachable!()
        };
        for _ in 0..shift {
            result = push(Opcode::Iadd, vec![result, result]);
        }
    } else {
        let rhs = match &operand {
            O::PReg(r) => Value(u32::from(r.encoding() % 32)),
            O::Special(_) => push(
                Opcode::Iconst {
                    ty: ty.clone(),
                    imm: 0,
                },
                vec![],
            ),
            O::Imm(value) => push(
                Opcode::Iconst {
                    ty: ty.clone(),
                    imm: *value << if opcode == M::AddRIShift12 { 12 } else { 0 },
                },
                vec![],
            ),
            _ => unreachable!(),
        };
        result = push(
            if matches!(opcode, M::SubRR | M::SubRI) {
                Opcode::Isub
            } else {
                Opcode::Iadd
            },
            vec![Value(0), rhs],
        );
    }
    let params = vec![(Value(0), ty.clone()), (Value(1), ty.clone())];
    source.value_types.extend(params.iter().cloned());
    for instruction in &instructions {
        source
            .value_types
            .insert(instruction.results[0], ty.clone());
    }
    instructions.push(Instruction {
        opcode: Opcode::Return,
        args: vec![result],
        results: vec![],
    });
    source.blocks.insert(
        source.entry_block,
        BasicBlock {
            params,
            instructions,
            ..Default::default()
        },
    );
    let mut machine = MachFunction::new(
        source.name.clone(),
        Signature::new(vec![mt.clone(); 2], vec![mt]),
    );
    for (op, operands) in [
        (
            M::StpPreIndex,
            vec![
                O::PReg(X29),
                O::PReg(X30),
                O::Special(SpecialReg::SP),
                O::Imm(-16),
            ],
        ),
        (
            M::AddRI,
            vec![O::PReg(X29), O::Special(SpecialReg::SP), O::Imm(0)],
        ),
        (opcode, vec![reg(0), reg(0), operand]),
        (
            M::LdpPostIndex,
            vec![
                O::PReg(X29),
                O::PReg(X30),
                O::Special(SpecialReg::SP),
                O::Imm(16),
            ],
        ),
        (M::Ret, vec![O::PReg(X30)]),
    ] {
        let id = machine.push_inst(MachInst::new(op, operands));
        machine.append_inst(machine.entry, id);
    }
    (source, machine)
}

#[test]
fn checked_alu_covers_widths_aliases_immediates_and_shift_boundaries() {
    let mut cases = 0;
    for bits in [32, 64] {
        let reg = |index: u16| O::PReg(PReg::new(index + if bits == 32 { 32 } else { 0 }));
        let zero = O::Special(if bits == 32 {
            SpecialReg::WZR
        } else {
            SpecialReg::XZR
        });
        let mut shapes = Vec::new();
        for op in [M::AddRR, M::SubRR] {
            for rhs in [reg(0), reg(1), zero.clone()] {
                shapes.push((op, rhs));
            }
        }
        for op in [M::AddRI, M::SubRI, M::AddRIShift12] {
            for imm in [0, 1, 4095] {
                shapes.push((op, O::Imm(imm)));
            }
        }
        for shift in [0, 1, i64::from(bits - 1)] {
            shapes.push((M::LslRI, O::Imm(shift)));
        }
        for (op, rhs) in shapes {
            let (source, machine) = fixture(bits, op, rhs.clone());
            let frame = source_bound_frame(&source, &machine).expect("source/machine pair");
            let alu = SourceBoundAlu::bind(&frame, InstId(2)).expect("checked arithmetic");
            assert!(!alu.obligation().is_degenerate(), "{bits}/{op:?}/{rhs:?}");
            let expected_inputs = if rhs == reg(1) { 2 } else { 1 };
            assert_eq!(alu.obligation().inputs.len(), expected_inputs);
            assert!(
                alu.obligation()
                    .inputs
                    .iter()
                    .all(|(_, width)| *width == bits)
            );
            let query = crate::ay_bridge::generate_smt2_query_raw(
                alu.obligation(),
                &crate::ay_bridge::AYConfig::default(),
            );
            println!(
                "SOURCE_BOUND_ALU_SMT2={}",
                serde_json::to_string(&query).unwrap()
            );
            cases += 1;
        }
    }
    assert_eq!(cases, 36);
}

#[test]
fn checked_alu_requires_live_arithmetic_and_excludes_frame_envelope() {
    let (source, machine) = fixture(64, M::AddRR, O::PReg(X1));
    let frame = source_bound_frame(&source, &machine).unwrap();
    for id in [0, 1, 3, 4, 5, u32::MAX] {
        assert!(SourceBoundAlu::bind(&frame, InstId(id)).is_none());
    }
}

#[test]
fn checked_alu_refuses_changed_source_operands_width_cfg_and_hidden_effects() {
    let (source, machine) = fixture(64, M::SubRR, O::PReg(X1));
    assert!(source_bound_frame(&source, &machine).is_ok());
    for mutation in 0..10 {
        let mut wrong = machine.clone();
        match mutation {
            0 => wrong.insts[2].opcode = M::AddRR,
            1 => wrong.insts[2].operands[1] = O::PReg(X1),
            2 => wrong.insts[2].operands[2] = O::PReg(X0),
            3 => wrong.insts[2].operands[0] = O::PReg(W0),
            4 => wrong.insts[2].operands[1] = O::PReg(X19),
            5 => wrong.insts[2].operands[1] = O::Special(SpecialReg::SP),
            6 => wrong.insts[2].implicit_defs = &[X0],
            7 => wrong.insts[2].flags = InstFlags::HAS_SIDE_EFFECTS,
            8 => wrong.blocks[0].insts.insert(2, InstId(2)),
            _ => wrong.blocks[0].succs.push(wrong.entry),
        }
        assert!(
            source_bound_frame(&source, &wrong).is_err(),
            "machine mutation {mutation}"
        );
    }
    let mut wrong = source.clone();
    wrong
        .blocks
        .get_mut(&wrong.entry_block)
        .unwrap()
        .instructions[0]
        .opcode = Opcode::Iadd;
    assert!(source_bound_frame(&wrong, &machine).is_err());
    wrong = source.clone();
    wrong
        .blocks
        .get_mut(&wrong.entry_block)
        .unwrap()
        .instructions[0]
        .args
        .swap(0, 1);
    assert!(source_bound_frame(&wrong, &machine).is_err());
}

#[test]
fn checked_alu_refuses_reserved_immediates_and_shift_mutations() {
    for bits in [32, 64] {
        for op in [M::AddRI, M::SubRI, M::AddRIShift12, M::LslRI] {
            let (source, machine) = fixture(bits, op, O::Imm(1));
            assert!(source_bound_frame(&source, &machine).is_ok());
            for value in [-1, 0, 2, i64::from(bits), 4096, i64::MAX] {
                let mut wrong = machine.clone();
                wrong.insts[2].operands[2] = O::Imm(value);
                assert!(
                    source_bound_frame(&source, &wrong).is_err(),
                    "{bits}/{op:?}/{value}"
                );
            }
            let mut wrong = machine.clone();
            wrong.insts[2].operands[1] = O::Special(if bits == 32 {
                SpecialReg::WZR
            } else {
                SpecialReg::XZR
            });
            assert!(source_bound_frame(&source, &wrong).is_err());
        }
    }
}

#[test]
fn checked_alu_never_promotes_without_independent_replay() {
    use crate::VerificationStrength;
    use crate::function_verifier::InstructionVerificationResult;
    use crate::provenance_xcheck::ProvenanceXCheckMode;
    use crate::{FunctionVerifier, VerificationConfig};
    crate::env_lock::with_env_overrides(&[("TCG_REFINE_SOLVER", "0")], || {
        let (source, machine) = fixture(64, M::AddRR, O::PReg(X1));
        let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        let captured = verifier.verify_with_request(&machine, Some(&source), &request);
        assert!(captured.matches_aarch64_input(&machine, Some(&source)));
        assert!(!captured.report().emitted_opcode_inventory().is_promotable());
        assert!(!matches!(
            captured.report().instructions[2].result,
            InstructionVerificationResult::Verified {
                strength: VerificationStrength::Formal,
                ..
            }
        ));
        let mut wrong = machine.clone();
        wrong.insts[2].opcode = M::SubRR;
        assert!(!captured.matches_aarch64_input(&wrong, Some(&source)));
        let mut wrong_source = source.clone();
        wrong_source.name.push_str("_changed");
        assert!(!captured.matches_aarch64_input(&machine, Some(&wrong_source)));
        for mode in [
            ProvenanceXCheckMode::Off,
            ProvenanceXCheckMode::Warn,
            ProvenanceXCheckMode::Enforce,
        ] {
            let report = verifier.verify_with_lir_source_and_mode(&wrong, Some(&source), mode);
            if mode == ProvenanceXCheckMode::Enforce {
                // SUB for a source ADD inside a recognized frame is an
                // erroneous supported target, rejected by name.
                assert!(matches!(
                    &report.precondition_failure,
                    Some(
                        crate::FunctionVerificationPreconditionFailure::SourceBoundFrameMismatch(
                            crate::source_bound_frame::FrameBindingMismatch::Body(
                                crate::aarch64_affine_lowering::AffineLoweringError::ReturnMismatch
                            )
                        )
                    )
                ));
                assert!(report.has_failures() && report.instructions.is_empty());
                continue;
            }
            assert!(report.precondition_failure.is_none());
            assert!(!matches!(
                report.instructions[2].result,
                InstructionVerificationResult::Verified {
                    strength: VerificationStrength::Formal,
                    ..
                }
            ));
        }
    });
}
