// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! A pure Jump cycle has a control observable even though it never returns.
//! These tests use the production source-bound owner and request/replay route.

use trust_cg_ir::function::{MachBlock, Signature as MachineSignature};
use trust_cg_ir::{AArch64Opcode as M, BlockId, InstId, MachFunction, MachInst, MachOperand as O};
use trust_cg_lower::Function;
use trust_cg_lower::function::{BasicBlock, Signature};
use trust_cg_lower::instructions::{Block, Instruction, Opcode as L};
use trust_cg_verify::function_verifier::InstructionVerificationResult;
use trust_cg_verify::provenance_xcheck::ProvenanceXCheckMode;
use trust_cg_verify::source_bound_a64_body::{
    diagnostic_a64_body_obligation, source_admits_a64_body_owner, source_bound_a64_body,
};
use trust_cg_verify::{FunctionVerifier, VerificationConfig, VerificationStrength};

fn fixture(successors: &[u32], layout: &[u32]) -> (Function, MachFunction) {
    let mut source = Function::new(
        "pure_jump_loop",
        Signature {
            params: vec![],
            returns: vec![],
        },
    );
    let mut machine = MachFunction::new(source.name.clone(), MachineSignature::new(vec![], vec![]));
    machine.blocks.clear();
    machine.insts.clear();
    let mut positions = vec![0i64; successors.len()];
    for (position, block) in layout.iter().enumerate() {
        positions[*block as usize] = position as i64;
    }
    for (block, target) in successors.iter().copied().enumerate() {
        source.blocks.insert(
            Block(block as u32),
            BasicBlock {
                instructions: vec![Instruction {
                    opcode: L::Jump {
                        dest: Block(target),
                    },
                    args: vec![],
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        let id = InstId(machine.insts.len() as u32);
        machine.insts.push(MachInst::new(
            M::B,
            vec![O::Imm(positions[target as usize] - positions[block])],
        ));
        machine.blocks.push(MachBlock {
            insts: vec![id],
            preds: successors
                .iter()
                .enumerate()
                .filter_map(|(pred, dest)| (*dest == block as u32).then_some(BlockId(pred as u32)))
                .collect(),
            succs: vec![BlockId(target)],
            loop_depth: 0,
        });
    }
    source.block_order = (0..successors.len() as u32).map(Block).collect();
    machine.block_order = layout.iter().copied().map(BlockId).collect();
    (source, machine)
}

#[test]
fn pure_jump_cycle_constructs_a_nondegenerate_source_bound_transition() {
    for (successors, layout) in [
        (vec![0], vec![0]),
        (vec![1, 1], vec![0, 1]),
        (vec![1, 2, 0], vec![0, 2, 1]),
    ] {
        let (source, machine) = fixture(&successors, &layout);
        assert!(source_admits_a64_body_owner(&source));
        let owner = source_bound_a64_body(&source, &machine)
            .expect("the exact source Jump graph needs a transition theorem");
        assert!(!owner.obligation().is_degenerate());
        assert_eq!(owner.covered().len(), successors.len());
        assert!(owner.copies_and_constants().is_empty());
        for id in 0..successors.len() {
            assert!(owner.covers(InstId(id as u32)));
        }
    }
}

#[test]
fn evaluation_only_never_credits_the_loop() {
    let (source, machine) = fixture(&[1, 1], &[0, 1]);
    let report = FunctionVerifier::with_config(VerificationConfig::default())
        .verify_with_lir_source_and_mode(&machine, Some(&source), ProvenanceXCheckMode::Enforce);
    assert!(!report.emitted_opcode_inventory().is_promotable());
    assert!(report.instructions.iter().all(|row| !matches!(
        row.result,
        InstructionVerificationResult::Verified {
            strength: VerificationStrength::Formal,
            ..
        }
    )));
}

#[test]
fn rejected_pure_jump_machine_cannot_fall_through_to_skipped_pseudos() {
    let (source, original) = fixture(&[1, 1], &[0, 1]);
    for unsupported_metadata in [false, true] {
        let mut machine = original.clone();
        for instruction in &mut machine.insts {
            *instruction = MachInst::new(M::Nop, vec![]);
        }
        if unsupported_metadata {
            machine.stack_limit_overflow_block = Some(BlockId(1));
        }
        let report = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion())
            .verify_with_lir_source_and_mode(
                &machine,
                Some(&source),
                ProvenanceXCheckMode::Enforce,
            );
        assert!(report.precondition_failure.is_some(), "{report:?}");
        assert!(
            !report.emitted_opcode_inventory().is_promotable(),
            "a source-bound control mismatch cannot become an all-skipped report: {report:?}"
        );
    }
}

#[test]
fn wrong_source_target_and_decoded_displacement_are_refuted() {
    let (source, machine) = fixture(&[1, 2, 0], &[0, 2, 1]);
    for index in 0..machine.insts.len() {
        let mut wrong = machine.clone();
        let O::Imm(offset) = &mut wrong.insts[index].operands[0] else {
            unreachable!()
        };
        *offset += 1;
        assert!(
            source_bound_a64_body(&source, &wrong).is_err(),
            "branch {index}"
        );
        let obligation = diagnostic_a64_body_obligation(&source, &wrong)
            .expect("diagnostics retain the false step theorem without authority");
        assert!(matches!(
            trust_cg_verify::verify_by_evaluation(&obligation),
            trust_cg_verify::VerificationResult::Invalid { .. }
        ));
    }
    // Keep all three source blocks reachable, and make the machine's edge
    // metadata agree with the changed source. The old encoded displacement
    // must still be refused: metadata cannot certify another branch target.
    let mut different_source = source.clone();
    different_source
        .blocks
        .get_mut(&Block(2))
        .unwrap()
        .instructions[0]
        .opcode = L::Jump { dest: Block(1) };
    let mut old_word = machine.clone();
    old_word.blocks[2].succs = vec![BlockId(1)];
    old_word.blocks[0].preds.clear();
    old_word.blocks[1].preds.push(BlockId(2));
    assert!(source_admits_a64_body_owner(&different_source));
    assert!(source_bound_a64_body(&different_source, &old_word).is_err());
    let wrong = diagnostic_a64_body_obligation(&different_source, &old_word).unwrap();
    assert!(matches!(
        trust_cg_verify::verify_by_evaluation(&wrong),
        trust_cg_verify::VerificationResult::Invalid { .. }
    ));
}

#[test]
fn bounded_graph_admission_keeps_every_block_and_refuses_unreachable_work() {
    for count in [1, 16] {
        let successors: Vec<_> = (0..count).map(|index| (index + 1) % count).collect();
        let layout: Vec<_> = (0..count).collect();
        let (source, machine) = fixture(&successors, &layout);
        assert_eq!(
            source_bound_a64_body(&source, &machine)
                .unwrap()
                .covered()
                .len(),
            count as usize,
        );
    }
    let successors: Vec<_> = (0..17).map(|index| (index + 1) % 17).collect();
    let (source, machine) = fixture(&successors, &(0..17).collect::<Vec<_>>());
    assert!(!source_admits_a64_body_owner(&source));
    assert!(source_bound_a64_body(&source, &machine).is_err());
    let (mut source, machine) = fixture(&[1, 1], &[0, 1]);
    source.blocks.get_mut(&Block(0)).unwrap().instructions[0].opcode = L::Jump { dest: Block(0) };
    assert!(!source_admits_a64_body_owner(&source));
    assert!(source_bound_a64_body(&source, &machine).is_err());
}

#[test]
fn effects_foreign_entries_and_malformed_ownership_never_bind() {
    let (source, machine) = fixture(&[1, 1], &[0, 1]);
    for case in 0..10 {
        let mut wrong = machine.clone();
        match case {
            0 => wrong.insts[0].opcode = M::Bl,
            1 => wrong.insts[0].operands.push(O::Imm(0)),
            2 => wrong.blocks[0].insts.push(InstId(0)),
            3 => wrong.blocks[0].insts[0] = InstId(u32::MAX),
            4 => wrong.block_order.swap(0, 1),
            5 => wrong.blocks[0].succs.clear(),
            6 => wrong.blocks[1].preds.clear(),
            7 => wrong.name.push_str("_foreign"),
            8 => wrong
                .signature
                .params
                .push(trust_cg_ir::function::Type::I64),
            _ => wrong.insts[0].operands[0] = O::Block(BlockId(1)),
        }
        assert!(
            source_bound_a64_body(&source, &wrong).is_err(),
            "machine case {case}"
        );
    }
    for case in 0..5 {
        let mut wrong = source.clone();
        match case {
            0 => wrong.signature.params.push(trust_cg_lower::Type::I64),
            1 => wrong.signature.returns.push(trust_cg_lower::Type::I64),
            2 => wrong.blocks.get_mut(&Block(0)).unwrap().instructions[0].opcode = L::Return,
            3 => {
                wrong.blocks.get_mut(&Block(0)).unwrap().instructions[0].opcode =
                    L::Jump { dest: Block(9) }
            }
            _ => wrong.blocks.get_mut(&Block(0)).unwrap().instructions[0]
                .args
                .push(trust_cg_lower::instructions::Value(0)),
        }
        assert!(!source_admits_a64_body_owner(&wrong), "source case {case}");
        assert!(source_bound_a64_body(&wrong, &machine).is_err());
    }
}

#[test]
fn a_real_checked_proof_credits_only_the_exact_source_bound_loop() {
    if std::env::var("TRUST_CG_RUN_FORMAL_PROOF_TESTS").as_deref() != Ok("1") {
        eprintln!("SKIP: requires TRUST_CG_RUN_FORMAL_PROOF_TESTS=1 (AY and Clean)");
        return;
    }
    let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
    let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
    for (successors, layout) in [
        (vec![0], vec![0]),
        (vec![1, 1], vec![0, 1]),
        (vec![1, 2, 0], vec![0, 2, 1]),
    ] {
        let (source, machine) = fixture(&successors, &layout);
        let owner = source_bound_a64_body(&source, &machine).unwrap();
        println!(
            "PURE_JUMP_QUERY={}",
            serde_json::to_string(&trust_cg_verify::ay_bridge::generate_smt2_query_raw(
                owner.obligation(),
                &trust_cg_verify::ay_bridge::AYConfig::default(),
            ))
            .unwrap()
        );
        let (captured, exports) =
            verifier.verify_with_request_for_export(&machine, Some(&source), &request);
        eprintln!("pure-loop proof report: {:?}", captured.report());
        assert!(captured.matches_aarch64_input(&machine, Some(&source)));
        assert!(captured.report().emitted_opcode_inventory().is_promotable());
        assert_eq!(captured.report().instructions.len(), successors.len());
        assert_eq!(exports.len(), successors.len());
        for export in exports {
            assert_eq!(
                export.kind(),
                trust_cg_verify::SourceBoundObligationKind::A64Body
            );
            assert_eq!(export.obligation(), owner.obligation());
            assert!(export.matches_aarch64_input(&machine, Some(&source)));
        }
        assert!(
            captured
                .report()
                .instructions
                .iter()
                .all(|row| matches!(&row.result,
        InstructionVerificationResult::Verified {
            strength: VerificationStrength::Formal, degenerate: false, proof_name, ..
        } if proof_name.contains("pure-jump")))
        );
        let mut wrong = machine.clone();
        let O::Imm(offset) = &mut wrong.insts[0].operands[0] else {
            unreachable!()
        };
        *offset += 1;
        assert!(!captured.matches_aarch64_input(&wrong, Some(&source)));
        assert!(
            !verifier
                .verify_with_request(&wrong, Some(&source), &request)
                .report()
                .emitted_opcode_inventory()
                .is_promotable()
        );
        assert!(
            !verifier
                .verify_with_request(&machine, None, &request)
                .report()
                .emitted_opcode_inventory()
                .is_promotable()
        );
        let mut wrong_source = source.clone();
        wrong_source.name.push_str("_foreign");
        assert!(!captured.matches_aarch64_input(&machine, Some(&wrong_source)));
    }
}
