// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
use super::*;
use crate::source_bound_frame::source_bound_frame;
use crate::verify::VerificationResult;
use trust_cg_ir::provenance::SourceInstId;
use trust_cg_ir::regs::PReg;
use trust_cg_ir::{MachFunction, MachInst};
use trust_cg_lower::Function;
use trust_cg_lower::instructions::{Instruction, Value};

fn dead_constant(
    bits: u32,
    value: u64,
    opcode: M,
    immediate: i64,
    shift: i64,
) -> (Function, MachFunction, InstId) {
    let (mut source, mut machine) =
        crate::source_bound_alu::tests::fixture(bits, M::SubRI, O::Imm(3));
    let ty = if bits == 32 { Type::I32 } else { Type::I64 };
    let constant = Instruction {
        opcode: Opcode::Iconst {
            ty: ty.clone(),
            imm: value as i64,
        },
        args: Vec::new(),
        results: vec![Value(90)],
    };
    let digest = SourceInstDigest::compute_debug(&constant.opcode, 0, 1);
    source
        .blocks
        .get_mut(&source.entry_block)
        .unwrap()
        .instructions
        .insert(2, constant);
    source.value_types.insert(Value(90), ty);
    let id = machine.push_inst(MachInst::new(
        opcode,
        vec![
            O::PReg(PReg::new(if bits == 32 { 33 } else { 1 })),
            O::Imm(immediate),
            O::Imm(shift),
        ],
    ));
    machine.blocks[0].insts.insert(2, id);
    machine.set_inst_lowering_provenance(
        id,
        LoweringProvenance::SourceInst {
            id: SourceInstId {
                block: source.entry_block.0,
                index: 2,
            },
            digest,
            trust_ir_inst: None,
        },
    );
    (source, machine, id)
}

#[test]
fn source_constants_bind_every_halfword_at_their_actual_width() {
    for bits in [32, 64] {
        let mask = if bits == 32 {
            u32::MAX as u64
        } else {
            u64::MAX
        };
        for opcode in [M::Movz, M::Movn] {
            for immediate in [0, 1, 3, 32768, 65535] {
                for shift in (0..bits).step_by(16) {
                    let shifted = (immediate as u64) << shift;
                    let value = if opcode == M::Movn {
                        !shifted & mask
                    } else {
                        shifted
                    };
                    let (source, machine, id) =
                        dead_constant(bits, value, opcode, immediate, i64::from(shift));
                    let frame =
                        source_bound_frame(&source, &machine).expect("checked dead constant frame");
                    let constant =
                        SourceBoundConstant::bind(&frame, id).expect("actual Iconst owner");
                    assert!(!constant.obligation().is_degenerate());
                    assert!(constant.obligation().inputs.is_empty());
                    assert!(matches!(
                        crate::lowering_proof::verify_by_evaluation(constant.obligation()),
                        VerificationResult::Valid
                    ));
                }
            }
        }
    }
}

#[test]
fn dead_constant_immediate_and_halfword_mutants_refute_the_source_value() {
    for bits in [32, 64] {
        for (immediate, shift) in [(4, 0), (3, 16)] {
            let (source, machine, id) = dead_constant(bits, 3, M::Movz, immediate, shift);
            // A return-only check cannot observe these wrong dead writes.
            let frame =
                source_bound_frame(&source, &machine).expect("dead write leaves return unchanged");
            let constant =
                SourceBoundConstant::bind(&frame, id).expect("a refutable constant owner");
            assert!(matches!(
                crate::lowering_proof::verify_by_evaluation(constant.obligation()),
                VerificationResult::Invalid { .. }
            ));
        }
    }
}

#[test]
fn constants_require_exact_iconst_coordinates_digest_and_width() {
    let (source, machine, id) = dead_constant(32, 3, M::Movz, 3, 0);
    for mutation in 0..7 {
        let mut wrong = machine.clone();
        let stamp = machine.inst_lowering_provenance(id);
        let LoweringProvenance::SourceInst {
            id: mut sid,
            mut digest,
            ..
        } = stamp
        else {
            unreachable!()
        };
        match mutation {
            0 => wrong.set_inst_lowering_provenance(id, LoweringProvenance::UNATTRIBUTED),
            1 => {
                sid.block += 99;
                wrong.set_inst_lowering_provenance(
                    id,
                    LoweringProvenance::SourceInst {
                        id: sid,
                        digest,
                        trust_ir_inst: None,
                    },
                );
            }
            2 => {
                sid.index = 99;
                wrong.set_inst_lowering_provenance(
                    id,
                    LoweringProvenance::SourceInst {
                        id: sid,
                        digest,
                        trust_ir_inst: None,
                    },
                );
            }
            3 => {
                digest.0 ^= 1;
                wrong.set_inst_lowering_provenance(
                    id,
                    LoweringProvenance::SourceInst {
                        id: sid,
                        digest,
                        trust_ir_inst: None,
                    },
                );
            }
            4 => {
                sid.index = 1; // Isub, with its correct digest: glue class exemption is insufficient.
                let inst = &source.blocks[&source.entry_block].instructions[1];
                digest = SourceInstDigest::compute_debug(
                    &inst.opcode,
                    inst.args.len(),
                    inst.results.len(),
                );
                wrong.set_inst_lowering_provenance(
                    id,
                    LoweringProvenance::SourceInst {
                        id: sid,
                        digest,
                        trust_ir_inst: None,
                    },
                );
            }
            5 => wrong.insts[id.0 as usize].operands[0] = O::PReg(PReg::new(1)), // X instead of source I32's W.
            _ => wrong.insts[id.0 as usize].operands[2] = O::Imm(32),
        }
        // Reserved move-wide encodings may already fail the outer gate.
        if let Ok(frame) = source_bound_frame(&source, &wrong) {
            assert!(
                SourceBoundConstant::bind(&frame, id).is_none(),
                "mutation {mutation}"
            );
        }
    }
}

#[test]
fn move_keep_expansions_need_a_sequence_owner() {
    let (source, mut machine, id) = dead_constant(64, 0x12340003, M::Movz, 3, 0);
    let keep = machine.push_inst(MachInst::new(
        M::Movk,
        vec![O::PReg(PReg::new(1)), O::Imm(0x1234), O::Imm(16)],
    ));
    machine.blocks[0].insts.insert(3, keep);
    machine.set_inst_lowering_provenance(keep, machine.inst_lowering_provenance(id));
    let frame = source_bound_frame(&source, &machine).expect("valid move-wide sequence");
    assert!(SourceBoundConstant::bind(&frame, id).is_none());
    assert!(SourceBoundConstant::bind(&frame, keep).is_none());
}

#[test]
fn ground_evaluation_cannot_replace_independent_replay() {
    crate::env_lock::with_env_overrides(&[("TCG_REFINE_SOLVER", "0")], || {
        let (source, machine, id) = dead_constant(64, 3, M::Movz, 3, 0);
        let verifier =
            crate::FunctionVerifier::with_config(crate::VerificationConfig::for_proof_promotion());
        let report = verifier.verify_with_lir_source_and_mode(
            &machine,
            Some(&source),
            crate::provenance_xcheck::ProvenanceXCheckMode::Enforce,
        );
        assert!(!report.emitted_opcode_inventory().is_promotable());
        assert!(!matches!(
            report
                .instructions
                .iter()
                .find(|row| row.inst_index == id.0 as usize)
                .unwrap()
                .result,
            crate::function_verifier::InstructionVerificationResult::Verified {
                strength: crate::VerificationStrength::Formal,
                ..
            }
        ));
    });
}
