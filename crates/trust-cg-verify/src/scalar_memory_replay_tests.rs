// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Exact inventory/identity/policy controls for conditional scalar-memory
//! replay. No successful verdict is injected; finite evaluation is not proof,
//! caller permission, native publication or artifact/cache authority.

use super::*;
use crate::memory_proofs::encode_store_le;
use crate::read_only_target::ScalarMemoryTargetEndpoint;
use crate::read_only_target::scalar_memory_tests::{evaluate, expand_equations};
use crate::smt::{EvalEnv, SmtExpr as E, SmtSort};
use crate::source_bound_frame::bind_scalar_memory_source;
use trust_cg_ir::regs::{X0, X1, X2, X3, X30, XZR};
use trust_cg_ir::{AArch64Opcode as M, MachInst, MachOperand as O, Signature, Type};
use trust_ir::{
    Block, BlockId, CallingConv, Constant, Endianness, FuncId, FuncTy, Inst, InstrNode, Module,
    TargetInfo, Ty, ValueId,
};

fn node(instruction: Inst, result: Option<u32>) -> InstrNode {
    let mut node = InstrNode::new(instruction);
    node.results.extend(result.map(ValueId::new));
    node
}

fn original() -> Module {
    let mut module = Module::new("ordinary_scalar_replay_control");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr; 2],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = trust_ir::Function::new(
        FuncId::new(23),
        "ordinary_scalar_replay_control",
        signature,
        BlockId::new(0),
    );
    function.calling_conv = CallingConv::C;
    let mut entry = Block::new(BlockId::new(0));
    entry.params = vec![(ValueId::new(0), Ty::Ptr), (ValueId::new(1), Ty::Ptr)];
    entry.body = vec![
        node(
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(42),
            },
            Some(2),
        ),
        node(
            Inst::Store {
                ty: Ty::U64,
                ptr: ValueId::new(1),
                value: ValueId::new(2),
                volatile: false,
                align: Some(8),
            },
            None,
        ),
        node(
            Inst::Load {
                ty: Ty::U64,
                ptr: ValueId::new(0),
                volatile: false,
                align: Some(8),
            },
            Some(3),
        ),
        node(
            Inst::Return {
                values: vec![ValueId::new(3)],
            },
            None,
        ),
    ];
    function.blocks.push(entry);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn machine() -> MachFunction {
    let mut machine = MachFunction::new(
        "ordinary_scalar_replay_control".into(),
        Signature::new(vec![Type::I64; 2], vec![Type::I64]),
    );
    for instruction in [
        MachInst::new(M::Movz, vec![O::PReg(X2), O::Imm(42)]),
        MachInst::new(M::StrRI, vec![O::PReg(X2), O::PReg(X1), O::Imm(0)]),
        MachInst::new(M::LdrRI, vec![O::PReg(X0), O::PReg(X0), O::Imm(0)]),
    ] {
        let id = machine.push_inst(instruction);
        machine.append_inst(machine.entry, id);
    }
    append_return(&mut machine);
    machine
}

fn append_return(machine: &mut MachFunction) {
    let mut ret = MachInst::new(M::Ret, vec![O::PReg(X30)]);
    ret.implicit_uses = &[X0];
    let id = machine.push_inst(ret);
    machine.append_inst(machine.entry, id);
}

fn words() -> Vec<u32> {
    // Exact MOVZ X2,#42; STR X2,[X1]; LDR X0,[X0]; RET X30 words.
    // The final-word observer owns their independent decode; no encoder hint.
    vec![0xd280_0542, 0xf900_0022, 0xf940_0000, 0xd65f_03c0]
}

fn bytes(words: &[u32]) -> Vec<u8> {
    words.iter().flat_map(|word| word.to_le_bytes()).collect()
}

fn expected_ids(
    target_returns: usize,
    target_reads: usize,
    target_writes: usize,
) -> Vec<ScalarMemoryRelationId> {
    let mut ids = Vec::new();
    for (stage, returns, reads, writes) in [
        (ScalarMemoryRelationStage::CoreToLir, 1, 1, 1),
        (
            ScalarMemoryRelationStage::CoreToMachine,
            target_returns,
            target_reads,
            target_writes,
        ),
        (
            ScalarMemoryRelationStage::CoreToFinalBytes,
            target_returns,
            target_reads,
            target_writes,
        ),
    ] {
        for (kind, count) in [
            (ScalarMemoryRelationKind::Status, returns),
            (ScalarMemoryRelationKind::FinalMemory, returns),
            (ScalarMemoryRelationKind::Read, reads),
            (ScalarMemoryRelationKind::Write, writes),
        ] {
            ids.extend((0..count).map(|index| ScalarMemoryRelationId { stage, kind, index }));
        }
    }
    ids
}

fn request(mode: ProvenanceXCheckMode) -> FunctionVerificationRequest {
    FunctionVerificationRequest::capture(VerificationConfig::for_proof_promotion(), mode)
}

fn assert_not_run(report: &ScalarMemoryReplayReport<'_, '_>, why: &str) {
    assert!(report.certificate().is_none());
    assert_eq!(report.outcomes().len(), report.relations().len());
    for (outcome, part) in report.outcomes().iter().zip(report.relations().parts()) {
        assert_eq!(outcome.id(), part.id());
        assert!(!outcome.attempted());
        assert!(outcome.verdict().is_none());
        assert!(outcome.why().unwrap().contains(why));
    }
}

fn assert_recording_refusal(
    report: &ScalarMemoryReplayReport<'_, '_>,
    expected: &[ScalarMemoryRelationId],
) {
    assert!(
        report.refusal().is_none(),
        "the captured enforcing policy matches"
    );
    assert!(report.certificate().is_none());
    assert_eq!(report.outcomes().len(), expected.len());
    assert_eq!(report.outcomes()[0].id(), expected[0]);
    assert!(report.outcomes()[0].attempted());
    assert!(report.outcomes()[0].verdict().is_none());
    assert!(
        report.outcomes()[0]
            .why()
            .unwrap()
            .contains("tier-0 recorder")
    );
    for (outcome, id) in report.outcomes().iter().zip(expected).skip(1) {
        assert_eq!(outcome.id(), *id);
        assert!(!outcome.attempted());
        assert!(outcome.verdict().is_none());
        assert_eq!(
            outcome.why(),
            Some("not replayed: an earlier part has no Valid replay")
        );
    }
}

#[test]
fn scalar_inventory_preserves_original_identity_inputs_premises_and_exact_borrowed_queries() {
    let original = original();
    let original_debug = format!("{original:#?}");
    let lir = trust_cg_lower::translate_function_with_license(
        &original.functions[0],
        &original,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .0;
    let lir_debug = format!("{lir:#?}");
    let source = bind_scalar_memory_source(&original, 0, &lir).unwrap();
    let machine = machine();
    let machine_debug = format!("{machine:#?}");
    let code = bytes(&words());
    let relations = ScalarMemoryCompilerRelations::bind(&source, &machine, &code).unwrap();
    let ids = expected_ids(1, 1, 1);
    assert_eq!(relations.len(), 12);
    assert!(!relations.is_empty());
    assert_eq!(
        relations.parts().map(|part| part.id()).collect::<Vec<_>>(),
        ids
    );
    assert_eq!(
        relations
            .parts()
            .rev()
            .map(|part| part.id())
            .collect::<Vec<_>>(),
        ids.iter().rev().copied().collect::<Vec<_>>()
    );
    let mut mixed = relations.parts();
    assert_eq!(mixed.next().unwrap().id(), ids[0]);
    assert_eq!(mixed.next_back().unwrap().id(), ids[11]);
    assert_eq!(mixed.len(), 10);
    assert!(std::ptr::eq(relations.source(), &source));
    assert!(std::ptr::eq(relations.source().module(), &original));
    assert!(std::ptr::eq(
        relations.source().source(),
        &original.functions[0]
    ));
    assert!(std::ptr::eq(relations.source().lir(), &lir));
    assert!(std::ptr::eq(relations.machine(), &machine));
    assert!(std::ptr::eq(relations.final_bytes(), code.as_slice()));
    match relations.machine_queries().endpoint() {
        ScalarMemoryTargetEndpoint::Machine(actual) => assert!(std::ptr::eq(actual, &machine)),
        _ => panic!("actual machine endpoint retained"),
    }
    match relations.byte_queries().endpoint() {
        ScalarMemoryTargetEndpoint::FinalBytes(actual) => {
            assert!(std::ptr::eq(actual, code.as_slice()))
        }
        _ => panic!("actual final words retained"),
    }
    for part in relations.parts() {
        let id = part.id();
        let (expected, premises, inputs) = if id.stage == ScalarMemoryRelationStage::CoreToLir {
            let query = match id.kind {
                ScalarMemoryRelationKind::Status => source.status_obligation(),
                ScalarMemoryRelationKind::FinalMemory => source.memory_obligation(),
                ScalarMemoryRelationKind::Read => &source.read_obligations()[id.index],
                ScalarMemoryRelationKind::Write => &source.write_obligations()[id.index],
            };
            (
                query,
                source
                    .source_geometry()
                    .iter()
                    .chain(source.encoding_definitions())
                    .cloned()
                    .collect::<Vec<_>>(),
                &source.status_obligation().inputs,
            )
        } else {
            let target = if id.stage == ScalarMemoryRelationStage::CoreToMachine {
                relations.machine_queries()
            } else {
                relations.byte_queries()
            };
            let query = match id.kind {
                ScalarMemoryRelationKind::Status => &target.return_obligations()[id.index],
                ScalarMemoryRelationKind::FinalMemory => &target.memory_obligations()[id.index],
                ScalarMemoryRelationKind::Read => &target.read_obligations()[id.index],
                ScalarMemoryRelationKind::Write => &target.write_obligations()[id.index],
            };
            (
                query,
                source
                    .source_geometry()
                    .iter()
                    .chain(source.original_encoding_definitions())
                    .chain(target.encoding_definitions())
                    .cloned()
                    .collect::<Vec<_>>(),
                &target.return_obligations()[0].inputs,
            )
        };
        assert!(
            std::ptr::eq(part.obligation(), expected),
            "replay borrows the exact owned query"
        );
        assert_eq!(part.obligation().preconditions, premises);
        assert_eq!(&part.obligation().inputs, inputs);
        assert_eq!(
            inputs.iter().filter(|(name, _)| name == "observe").count(),
            1
        );
        assert!(inputs.contains(&("abi_x0".into(), 64)) && inputs.contains(&("abi_x1".into(), 64)));
        assert!(!inputs.iter().any(|(name, _)| name == "abi_x2"));
    }
    assert_eq!(format!("{original:#?}"), original_debug);
    assert_eq!(format!("{lir:#?}"), lir_debug);
    assert_eq!(format!("{machine:#?}"), machine_debug);
    assert_eq!(code, bytes(&words()));
}

#[test]
fn scalar_replay_off_warn_and_configuration_mismatch_never_attempt_or_mint() {
    let original = original();
    let lir = trust_cg_lower::translate_function_with_license(
        &original.functions[0],
        &original,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .0;
    let source = bind_scalar_memory_source(&original, 0, &lir).unwrap();
    let machine = machine();
    let code = bytes(&words());
    let relations = ScalarMemoryCompilerRelations::bind(&source, &machine, &code).unwrap();
    for mode in [ProvenanceXCheckMode::Off, ProvenanceXCheckMode::Warn] {
        let request = request(mode);
        let report = relations.replay(&request);
        assert!(std::ptr::eq(report.request(), &request));
        assert!(std::ptr::eq(report.relations(), &relations));
        assert_eq!(
            report.refusal(),
            Some(ScalarMemoryReplayRefusal::ProvenanceNotEnforced)
        );
        assert_not_run(&report, "Enforce");
    }
    let mut samples = VerificationConfig::for_proof_promotion();
    samples.sample_count += 1;
    let mut exhaustive = VerificationConfig::for_proof_promotion();
    exhaustive.exhaustive_threshold += 1;
    for config in [VerificationConfig::default(), samples, exhaustive] {
        let request = FunctionVerificationRequest::capture(config, ProvenanceXCheckMode::Enforce);
        let report = relations.replay(&request);
        assert_eq!(
            report.refusal(),
            Some(ScalarMemoryReplayRefusal::ProofPromotionConfigurationMismatch)
        );
        assert_not_run(&report, "proof-promotion");
    }
}

#[test]
fn scalar_authentic_recorder_refusal_retains_complete_unrun_inventory() {
    let original = original();
    let lir = trust_cg_lower::translate_function_with_license(
        &original.functions[0],
        &original,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .0;
    let source = bind_scalar_memory_source(&original, 0, &lir).unwrap();
    let machine = machine();
    let code = bytes(&words());
    let relations = ScalarMemoryCompilerRelations::bind(&source, &machine, &code).unwrap();
    // Existing request-local recording refusal, not a fake solver/verdict or
    // a process-wide environment change. No replay success is fabricated.
    let request = request(ProvenanceXCheckMode::Enforce).captured_while_recording();
    let report = relations.replay(&request);
    assert_recording_refusal(&report, &expected_ids(1, 1, 1));
    assert!(std::ptr::eq(report.request(), &request));
    assert!(std::ptr::eq(report.relations(), &relations));
    assert!(std::ptr::eq(report.relations().source(), &source));
    assert!(std::ptr::eq(report.relations().machine(), &machine));
    assert!(std::ptr::eq(
        report.relations().final_bytes(),
        code.as_slice()
    ));
}

#[test]
fn scalar_every_guarded_status_and_final_memory_row_is_inventory_required() {
    let original = original();
    let lir = trust_cg_lower::translate_function_with_license(
        &original.functions[0],
        &original,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .0;
    let source = bind_scalar_memory_source(&original, 0, &lir).unwrap();
    let mut machine = machine();
    let branch = machine.push_inst(MachInst::new(M::Cbz, vec![O::PReg(X0), O::Imm(2)]));
    machine.block_mut(machine.entry).insts.insert(3, branch);
    append_return(&mut machine);
    let mut words = words();
    words.insert(3, 0xb400_0040); // CBZ X0,+2 words, before both exact RETs.
    words.push(0xd65f_03c0);
    let code = bytes(&words);
    let relations = ScalarMemoryCompilerRelations::bind(&source, &machine, &code).unwrap();
    let ids = expected_ids(2, 1, 1);
    assert_eq!(relations.len(), 16);
    assert_eq!(
        relations.parts().map(|part| part.id()).collect::<Vec<_>>(),
        ids
    );
    for stage in [
        ScalarMemoryRelationStage::CoreToMachine,
        ScalarMemoryRelationStage::CoreToFinalBytes,
    ] {
        for kind in [
            ScalarMemoryRelationKind::Status,
            ScalarMemoryRelationKind::FinalMemory,
        ] {
            assert_eq!(
                relations
                    .parts()
                    .filter(|part| part.id().stage == stage && part.id().kind == kind)
                    .map(|part| part.id().index)
                    .collect::<Vec<_>>(),
                [0, 1]
            );
        }
    }
    let request = request(ProvenanceXCheckMode::Enforce).captured_while_recording();
    assert_recording_refusal(&relations.replay(&request), &ids);
}

#[test]
fn scalar_dead_read_and_write_restore_cannot_leave_the_replay_inventory() {
    let original = original();
    let lir = trust_cg_lower::translate_function_with_license(
        &original.functions[0],
        &original,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .0;
    let source = bind_scalar_memory_source(&original, 0, &lir).unwrap();
    let mut machine = machine();
    let mut additions = Vec::new();
    for instruction in [
        MachInst::new(M::LdrRI, vec![O::PReg(X3), O::PReg(X1), O::Imm(8)]),
        MachInst::new(M::StrRI, vec![O::PReg(XZR), O::PReg(X1), O::Imm(8)]),
        MachInst::new(M::StrRI, vec![O::PReg(X3), O::PReg(X1), O::Imm(8)]),
    ] {
        additions.push(machine.push_inst(instruction));
    }
    machine
        .block_mut(machine.entry)
        .insts
        .splice(3..3, additions);
    let mut words = words();
    words.splice(3..3, [0xf940_0423, 0xf900_043f, 0xf900_0423]);
    let code = bytes(&words);
    let relations = ScalarMemoryCompilerRelations::bind(&source, &machine, &code).unwrap();
    let ids = expected_ids(1, 2, 3);
    assert_eq!(relations.len(), 18);
    assert_eq!(
        relations.parts().map(|part| part.id()).collect::<Vec<_>>(),
        ids
    );
    let mut memory = E::const_array(SmtSort::BitVec(64), E::bv_const(0xa5, 8));
    for (address, value) in [(0x1000, 17), (0x2000, 29), (0x2008, 0x1122_3344_5566_7788)] {
        memory = encode_store_le(
            &memory,
            &E::bv_const(address, 64),
            &E::bv_const(value, 64),
            8,
        );
    }
    let mut env = EvalEnv::default();
    env.insert("abi_x0".into(), 0x1000);
    env.insert("abi_x1".into(), 0x2000);
    env.insert("observe".into(), 0x2008);
    for (stage, target) in [
        (
            ScalarMemoryRelationStage::CoreToMachine,
            relations.machine_queries(),
        ),
        (
            ScalarMemoryRelationStage::CoreToFinalBytes,
            relations.byte_queries(),
        ),
    ] {
        let mut equations = source.original_encoding_definitions().to_vec();
        equations.extend_from_slice(target.encoding_definitions());
        let substitutions = expand_equations(&equations, &memory);
        for part in relations.parts().filter(|part| part.id().stage == stage) {
            let query = part.obligation();
            assert!(
                query
                    .preconditions
                    .iter()
                    .all(|premise| evaluate(premise, &substitutions, &env).as_bool())
            );
            let holds = evaluate(&query.trust_ir_expr, &substitutions, &env)
                == evaluate(&query.aarch64_expr, &substitutions, &env);
            let expected = match part.id().kind {
                ScalarMemoryRelationKind::Status | ScalarMemoryRelationKind::FinalMemory => true,
                ScalarMemoryRelationKind::Read | ScalarMemoryRelationKind::Write => {
                    part.id().index == 0
                }
            };
            assert_eq!(
                holds,
                expected,
                "actual {stage:?} {:?} row{}",
                part.id().kind,
                part.id().index
            );
        }
    }
    let request = request(ProvenanceXCheckMode::Enforce).captured_while_recording();
    let report = relations.replay(&request);
    assert_recording_refusal(&report, &ids);
    assert!(
        report.certificate().is_none(),
        "finite counterexamples are not replay credit"
    );
}

#[test]
fn scalar_endpoint_identity_and_unsupported_bytes_are_target_refusals_not_source_skips() {
    let original = original();
    let lir = trust_cg_lower::translate_function_with_license(
        &original.functions[0],
        &original,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .0;
    let source = bind_scalar_memory_source(&original, 0, &lir).unwrap();
    let code = bytes(&words());
    let mut wrong = machine();
    wrong.name.push_str("_other");
    assert_eq!(
        ScalarMemoryCompilerRelations::bind(&source, &wrong, &code).err(),
        Some(ReadOnlyTargetError::Machine(
            "function identity/signature differs from original Core"
        ))
    );
    wrong = machine();
    wrong.signature.params.push(Type::I64);
    assert_eq!(
        ScalarMemoryCompilerRelations::bind(&source, &wrong, &code).err(),
        Some(ReadOnlyTargetError::Machine(
            "function identity/signature differs from original Core"
        ))
    );
    let machine = machine();
    for code in [vec![], vec![0], bytes(&[0xffff_ffff])] {
        assert!(matches!(
            ScalarMemoryCompilerRelations::bind(&source, &machine, &code),
            Err(ReadOnlyTargetError::Bytes(_))
        ));
    }
}
