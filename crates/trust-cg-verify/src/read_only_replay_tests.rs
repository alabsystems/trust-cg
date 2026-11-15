// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Inventory, identity, policy and actual-refusal controls. These tests never
//! synthesize a successful replay/certificate. Connected strict AY/Clean
//! acceptance uses the authentic compiler endpoints in the codegen tests.

use super::*;
use crate::memory_proofs::{encode_store_le, memory_sort, zeroed_memory};
use crate::smt::{EvalEnv, EvalResult, SmtExpr};
use crate::source_bound_frame::bind_read_only_source;
use std::convert::Infallible;
use trust_cg_ir::regs::{X0, X1, X2, X30};
use trust_cg_ir::{AArch64Opcode as M, MachInst, MachOperand as O, Signature, Type};
use trust_ir::{
    Block, BlockId, Endianness, FuncId, FuncTy, Inst, InstrNode, Module, TargetInfo, Ty, ValueId,
};

fn module() -> Module {
    let mut module = Module::new("read_only_replay_inventory_control");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = trust_ir::Function::new(
        FuncId::new(19),
        "read_only_replay_control",
        signature,
        BlockId::new(0),
    );
    let mut entry = Block::new(BlockId::new(0));
    entry.params = vec![(ValueId::new(0), Ty::Ptr)];
    let mut load = InstrNode::new(Inst::Load {
        ty: Ty::U64,
        ptr: ValueId::new(0),
        volatile: false,
        align: Some(8),
    });
    load.results = vec![ValueId::new(1)];
    entry.body = vec![
        load,
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }),
    ];
    function.blocks = vec![entry];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn machine(offset: i64) -> MachFunction {
    let mut function = MachFunction::new(
        "read_only_replay_control".into(),
        Signature {
            params: vec![Type::I64],
            returns: vec![Type::I64],
        },
    );
    let load = function.push_inst(MachInst::new(
        M::LdrRI,
        vec![O::PReg(X0), O::PReg(X0), O::Imm(offset)],
    ));
    function.append_inst(function.entry, load);
    let mut ret = MachInst::new(M::Ret, vec![O::PReg(X30)]);
    ret.implicit_uses = &[X0];
    let ret = function.push_inst(ret);
    function.append_inst(function.entry, ret);
    function
}

fn bytes(first: u32) -> Vec<u8> {
    [first, 0xd65f_03c0]
        .into_iter()
        .flat_map(u32::to_le_bytes)
        .collect()
}

fn ids() -> Vec<ReadOnlyRelationId> {
    [
        ReadOnlyRelationStage::CoreToLir,
        ReadOnlyRelationStage::CoreToMachine,
        ReadOnlyRelationStage::CoreToFinalBytes,
    ]
    .into_iter()
    .flat_map(|stage| {
        [ReadOnlyRelationKind::Return, ReadOnlyRelationKind::Load].map(|kind| ReadOnlyRelationId {
            stage,
            kind,
            index: 0,
        })
    })
    .collect()
}

fn request(mode: ProvenanceXCheckMode) -> FunctionVerificationRequest {
    FunctionVerificationRequest::capture(VerificationConfig::for_proof_promotion(), mode)
}

fn assert_not_run(report: &ReadOnlyReplayReport<'_, '_>, why: &str) {
    assert!(report.certificate().is_none());
    assert_eq!(report.outcomes().len(), report.relations().len());
    for (outcome, part) in report.outcomes().iter().zip(report.relations().parts()) {
        assert_eq!(outcome.id(), part.id());
        assert!(!outcome.attempted());
        assert!(outcome.verdict().is_none());
        assert!(outcome.why().unwrap().contains(why));
    }
}

#[test]
fn deterministic_complete_inventory_borrows_original_queries_and_actual_endpoints() {
    let original = module();
    let original_debug = format!("{original:#?}");
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &original.functions[0],
        &original,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    let lir_debug = format!("{lir:#?}");
    let source = bind_read_only_source(&original, 0, &lir).unwrap();
    let machine = machine(0);
    let machine_debug = format!("{machine:#?}");
    let code = bytes(0xf940_0000); // Actual LDR X0,[X0]; RET X30 control.
    let relations = ReadOnlyCompilerRelations::bind(&source, &machine, &code).unwrap();
    assert_eq!(relations.len(), 6);
    assert!(!relations.is_empty());
    assert_eq!(relations.parts().map(|p| p.id()).collect::<Vec<_>>(), ids());
    assert_eq!(
        relations.parts().rev().map(|p| p.id()).collect::<Vec<_>>(),
        ids().into_iter().rev().collect::<Vec<_>>()
    );
    assert!(std::ptr::eq(relations.source(), &source));
    assert!(std::ptr::eq(relations.source().module(), &original));
    assert!(std::ptr::eq(relations.source().lir(), &lir));
    assert!(std::ptr::eq(relations.machine(), &machine));
    assert!(std::ptr::eq(relations.final_bytes(), code.as_slice()));
    for part in relations.parts() {
        let expected = match (part.id().stage, part.id().kind) {
            (ReadOnlyRelationStage::CoreToLir, ReadOnlyRelationKind::Return) => {
                source.return_obligation()
            }
            (ReadOnlyRelationStage::CoreToLir, ReadOnlyRelationKind::Load) => {
                &source.load_obligations()[0]
            }
            (ReadOnlyRelationStage::CoreToMachine, ReadOnlyRelationKind::Return) => {
                &relations.machine_queries().return_obligations()[0]
            }
            (ReadOnlyRelationStage::CoreToMachine, ReadOnlyRelationKind::Load) => {
                &relations.machine_queries().load_obligations()[0]
            }
            (ReadOnlyRelationStage::CoreToFinalBytes, ReadOnlyRelationKind::Return) => {
                &relations.byte_queries().return_obligations()[0]
            }
            (ReadOnlyRelationStage::CoreToFinalBytes, ReadOnlyRelationKind::Load) => {
                &relations.byte_queries().load_obligations()[0]
            }
        };
        assert!(
            std::ptr::eq(part.obligation(), expected),
            "no query cloning/reconstruction at replay boundary"
        );
    }
    assert_eq!(format!("{original:#?}"), original_debug);
    assert_eq!(format!("{lir:#?}"), lir_debug);
    assert_eq!(format!("{machine:#?}"), machine_debug);
    assert_eq!(code, bytes(0xf940_0000));
}

#[test]
fn enforce_and_exact_proof_promotion_configuration_are_mandatory_before_replay() {
    let module = module();
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    let source = bind_read_only_source(&module, 0, &lir).unwrap();
    let machine = machine(0);
    let code = bytes(0xf940_0000);
    let relations = ReadOnlyCompilerRelations::bind(&source, &machine, &code).unwrap();
    for mode in [ProvenanceXCheckMode::Off, ProvenanceXCheckMode::Warn] {
        let request = request(mode);
        let report = relations.replay(&request);
        assert!(std::ptr::eq(report.request(), &request));
        assert!(std::ptr::eq(report.relations(), &relations));
        assert_eq!(
            report.refusal(),
            Some(ReadOnlyReplayRefusal::ProvenanceNotEnforced)
        );
        assert_not_run(&report, "Enforce");
    }
    let mut different_samples = VerificationConfig::for_proof_promotion();
    different_samples.sample_count += 1;
    let mut different_exhaustive = VerificationConfig::for_proof_promotion();
    different_exhaustive.exhaustive_threshold += 1;
    for config in [
        VerificationConfig::default(),
        different_samples,
        different_exhaustive,
    ] {
        let request = FunctionVerificationRequest::capture(config, ProvenanceXCheckMode::Enforce);
        let report = relations.replay(&request);
        assert_eq!(
            report.refusal(),
            Some(ReadOnlyReplayRefusal::ProofPromotionConfigurationMismatch)
        );
        assert_not_run(&report, "proof-promotion");
    }
}

#[test]
fn authentic_recording_refusal_stops_replay_and_retains_all_later_rows() {
    let module = module();
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    let source = bind_read_only_source(&module, 0, &lir).unwrap();
    let machine = machine(0);
    let code = bytes(0xf940_0000);
    let relations = ReadOnlyCompilerRelations::bind(&source, &machine, &code).unwrap();
    // This request-local existing control does not arm global recording or
    // alter the solver/tool identity. No synthetic Valid result is injected.
    let request = request(ProvenanceXCheckMode::Enforce).captured_while_recording();
    let report = relations.replay(&request);
    assert!(
        report.refusal().is_none(),
        "the requested strict policy itself matches"
    );
    assert!(report.certificate().is_none());
    assert_eq!(report.outcomes().len(), 6);
    assert!(report.outcomes()[0].attempted());
    assert!(report.outcomes()[0].verdict().is_none());
    assert!(
        report.outcomes()[0]
            .why()
            .unwrap()
            .contains("tier-0 recorder")
    );
    for (outcome, expected) in report.outcomes().iter().zip(ids()).skip(1) {
        assert_eq!(outcome.id(), expected);
        assert!(!outcome.attempted());
        assert!(outcome.verdict().is_none());
        assert_eq!(
            outcome.why(),
            Some("not replayed: an earlier part has no Valid replay")
        );
    }
    assert!(std::ptr::eq(report.request(), &request));
    assert!(std::ptr::eq(report.relations().machine(), &machine));
    assert!(std::ptr::eq(
        report.relations().final_bytes(),
        code.as_slice()
    ));
}

#[test]
fn source_machine_name_and_signature_cannot_be_substituted() {
    let module = module();
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    let source = bind_read_only_source(&module, 0, &lir).unwrap();
    let code = bytes(0xf940_0000);
    let mut wrong = machine(0);
    wrong.name = "same_shape_different_source".into();
    assert_eq!(
        ReadOnlyCompilerRelations::bind(&source, &wrong, &code).err(),
        Some(ReadOnlyTargetError::Machine(
            "function identity/signature differs from original Core"
        ))
    );
    wrong = machine(0);
    wrong.signature.params.push(Type::I64);
    assert_eq!(
        ReadOnlyCompilerRelations::bind(&source, &wrong, &code).err(),
        Some(ReadOnlyTargetError::Machine(
            "function identity/signature differs from original Core"
        ))
    );
}

#[test]
fn unsupported_final_words_are_a_target_error_not_a_source_coverage_skip() {
    let module = module();
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    let source = bind_read_only_source(&module, 0, &lir).unwrap();
    let machine = machine(0);
    for code in [vec![], vec![0], bytes(0xffff_ffff)] {
        assert!(matches!(
            ReadOnlyCompilerRelations::bind(&source, &machine, &code),
            Err(ReadOnlyTargetError::Bytes(_))
        ));
    }
}

#[test]
fn every_guarded_return_is_inventory_required_not_only_each_ret_word() {
    let module = module();
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    let source = bind_read_only_source(&module, 0, &lir).unwrap();
    let mut machine = machine(0);
    let branch = machine.push_inst(MachInst::new(M::Cbz, vec![O::PReg(X0), O::Imm(2)]));
    machine.block_mut(machine.entry).insts.insert(1, branch);
    let mut ret = MachInst::new(M::Ret, vec![O::PReg(X30)]);
    ret.implicit_uses = &[X0];
    let ret = machine.push_inst(ret);
    machine.append_inst(machine.entry, ret);
    // LDR X0,[X0]; CBZ X0,+2 words; RET X30; RET X30.
    let code: Vec<_> = [0xf940_0000u32, 0xb400_0040, 0xd65f_03c0, 0xd65f_03c0]
        .into_iter()
        .flat_map(u32::to_le_bytes)
        .collect();
    let relations = ReadOnlyCompilerRelations::bind(&source, &machine, &code).unwrap();
    assert_eq!(relations.len(), 8);
    for stage in [
        ReadOnlyRelationStage::CoreToMachine,
        ReadOnlyRelationStage::CoreToFinalBytes,
    ] {
        assert_eq!(
            relations
                .parts()
                .filter(|p| p.id().stage == stage && p.id().kind == ReadOnlyRelationKind::Return)
                .map(|p| p.id().index)
                .collect::<Vec<_>>(),
            [0, 1]
        );
    }
    let request = request(ProvenanceXCheckMode::Enforce).captured_while_recording();
    let report = relations.replay(&request);
    assert!(report.certificate().is_none());
    assert_eq!(report.outcomes().len(), relations.len());
    assert_eq!(
        report.outcomes().iter().map(|o| o.id()).collect::<Vec<_>>(),
        relations.parts().map(|p| p.id()).collect::<Vec<_>>()
    );
}

#[test]
fn discarded_extra_reads_cannot_disappear_from_the_relation_inventory() {
    let module = module();
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    let source = bind_read_only_source(&module, 0, &lir).unwrap();
    let mut machine = machine(0);
    let copy = machine.push_inst(MachInst::new(M::MOVXrr, vec![O::PReg(X2), O::PReg(X0)]));
    machine.block_mut(machine.entry).insts.insert(0, copy);
    let extra = machine.push_inst(MachInst::new(
        M::LdrRI,
        vec![O::PReg(X1), O::PReg(X2), O::Imm(8)],
    ));
    machine.block_mut(machine.entry).insts.insert(2, extra);
    // MOV X2,X0; LDR X0,[X0]; LDR X1,[X2,#8]; RET X30.
    let code: Vec<_> = [0xaa00_03e2u32, 0xf940_0000, 0xf940_0441, 0xd65f_03c0]
        .into_iter()
        .flat_map(u32::to_le_bytes)
        .collect();
    let relations = ReadOnlyCompilerRelations::bind(&source, &machine, &code).unwrap();
    assert_eq!(relations.len(), 8);
    assert_eq!(relations.machine_queries().reads().len(), 2);
    assert_eq!(relations.byte_queries().reads().len(), 2);
    let mut env = EvalEnv::default();
    env.insert("abi_x0".into(), 0x1000);
    let memory = encode_store_le(
        &zeroed_memory(),
        &SmtExpr::bv_const(0x1000, 64),
        &SmtExpr::bv_const(17, 64),
        8,
    );
    for stage in [
        ReadOnlyRelationStage::CoreToMachine,
        ReadOnlyRelationStage::CoreToFinalBytes,
    ] {
        let loads: Vec<_> = relations
            .parts()
            .filter(|p| p.id().stage == stage && p.id().kind == ReadOnlyRelationKind::Load)
            .collect();
        assert_eq!(loads.len(), 2);
        assert_eq!(loads[1].id().index, 1);
        assert_eq!(
            concrete(&loads[1].obligation().aarch64_expr, &memory, &env),
            EvalResult::Bool(false)
        );
        let returned = relations
            .parts()
            .find(|p| p.id().stage == stage && p.id().kind == ReadOnlyRelationKind::Return)
            .unwrap();
        assert_eq!(
            concrete(&returned.obligation().aarch64_expr, &memory, &env),
            EvalResult::Bool(true),
            "a true return equation cannot hide an extra potentially faulting read"
        );
    }
}

fn concrete(expr: &SmtExpr, memory: &SmtExpr, env: &EvalEnv) -> EvalResult {
    let rewritten = expr
        .try_rewrite_dag::<Infallible>(&mut |node| {
            Ok(matches!(node, SmtExpr::UF { name, args, ret_sort }
            if name == "entry_memory" && args.is_empty() && *ret_sort == memory_sort())
            .then(|| memory.clone()))
        })
        .unwrap()
        .unwrap_or_else(|| expr.clone());
    rewritten.try_eval(env).unwrap()
}

#[test]
fn legal_semantic_mutants_remain_pending_actual_queries_with_counterexamples() {
    let module = module();
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    let source = bind_read_only_source(&module, 0, &lir).unwrap();
    let mut env = EvalEnv::default();
    env.insert("abi_x0".into(), 0x1000);
    let mut memory = zeroed_memory();
    for (address, value) in [(0x1000, 17), (0x1008, 29)] {
        memory = encode_store_le(
            &memory,
            &SmtExpr::bv_const(address, 64),
            &SmtExpr::bv_const(value, 64),
            8,
        );
    }
    for (machine, code, bad_stage) in [
        (
            machine(8),
            bytes(0xf940_0000),
            ReadOnlyRelationStage::CoreToMachine,
        ),
        (
            machine(0),
            bytes(0xf940_0400),
            ReadOnlyRelationStage::CoreToFinalBytes,
        ),
    ] {
        let relations = ReadOnlyCompilerRelations::bind(&source, &machine, &code)
            .expect("legal wrong-address semantics must construct, not refuse structurally");
        assert_eq!(relations.parts().map(|p| p.id()).collect::<Vec<_>>(), ids());
        for part in relations.parts().filter(|p| p.id().stage == bad_stage) {
            assert_eq!(
                concrete(&part.obligation().aarch64_expr, &memory, &env),
                EvalResult::Bool(false),
                "actual {bad_stage:?} {:?} has an independent concrete counterexample",
                part.id().kind
            );
        }
        let request = request(ProvenanceXCheckMode::Enforce).captured_while_recording();
        let report = relations.replay(&request);
        assert!(
            report.certificate().is_none(),
            "concrete testing never manufactures replay proof"
        );
    }
}
