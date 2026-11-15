// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use trust_cg_lower::instructions::{Block, Opcode};
use trust_cg_lower::{Function, ProofContext};
use trust_cg_verify::aarch64_affine_lowering::{AffineLoweringError, TrustIrAffineLoweringError};
use trust_ir::{BinOp, BlockId, FuncId, FuncTy, Inst, InstrNode, Module, Ty, ValueId};

fn source(op: BinOp) -> (Module, Function, ProofContext) {
    let mut module = Module::new("affine_core_seam");
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = trust_ir::Function::new(
        FuncId::new(17),
        "affine_core_seam",
        signature,
        BlockId::new(5),
    );
    // Deliberately sparse identities: parameters bind by ordinal, not ValueId.
    let (a, b, result) = (ValueId::new(100), ValueId::new(300), ValueId::new(700));
    function.blocks.push(trust_ir::Block {
        id: function.entry,
        params: vec![(a, Ty::I64), (b, Ty::I64)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op,
                ty: Ty::I64,
                lhs: a,
                rhs: b,
            })
            .with_result(result),
            InstrNode::new(Inst::Return {
                values: vec![result],
            }),
        ],
    });
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    let (lir, proof_context) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .unwrap();
    (module, lir, proof_context)
}

fn pipeline() -> Pipeline {
    Pipeline::new(PipelineConfig {
        verify: false,
        ..PipelineConfig::for_target("aarch64-apple-darwin")
    })
}

#[test]
fn sealed_core_preparation_checks_raw_triple_without_promoting_final_machine() {
    let (module, input, proofs) = source(BinOp::Add);
    let (_, metrics) = pipeline()
        .prepare_function_with_metrics_for_sealed_core(&input, Some(&proofs), &module, 0)
        .expect("ordinary affine source prepares through existing Core pipeline");
    let Some(PreOptimizationAffineLowering::Checked(stats)) =
        metrics.pre_optimization_affine_lowering
    else {
        panic!("Core path must record the actual raw triple check");
    };
    assert_eq!(stats.trust_ir_instructions, 2);
    assert_eq!(stats.lowering.source_instructions, 2);
    assert_eq!(stats.lowering.machine_instructions, 5); // 2 ABI copies, ADD, return copy, RET.
    assert_eq!(stats.lowering.parameter_count, 2);
    // These counts mint no final JIT certificate. Later publication gates run.
}

#[test]
fn core_affine_gate_rejects_wrong_source_despite_plausible_provenance() {
    let (module, mut input, _) = source(BinOp::Add);
    let (selected, _) = pipeline()
        .run_isel_with_call_admission(&input, None, Aarch64DirectCallAdmission::SealedCore)
        .unwrap();
    let machine = selected.to_ir_func();
    input
        .blocks
        .get_mut(&input.entry_block)
        .unwrap()
        .instructions[0]
        .args
        .swap(0, 1);
    // Commutation is semantic equality, independent of nominal operand stamps.
    assert!(matches!(
        check_core_affine_lowering(&module, 0, &input, &machine),
        Ok(PreOptimizationAffineLowering::Checked(_))
    ));
    input
        .blocks
        .get_mut(&input.entry_block)
        .unwrap()
        .instructions[0]
        .opcode = Opcode::Isub;
    assert!(matches!(
        check_core_affine_lowering(&module, 0, &input, &machine),
        Err(PipelineError::AffineLoweringRejected {
            reason: TrustIrAffineLoweringError::TrustIrLirMismatch,
            ..
        })
    ));
}

#[test]
fn broader_core_source_is_explicitly_unchecked_not_promoted_by_affine_summary() {
    let (module, input, proofs) = source(BinOp::Mul);
    let (_, metrics) = pipeline()
        .prepare_function_with_metrics_for_sealed_core(&input, Some(&proofs), &module, 0)
        .unwrap();
    assert!(matches!(
        metrics.pre_optimization_affine_lowering,
        Some(PreOptimizationAffineLowering::UnsupportedSource { .. })
    ));
}

#[test]
fn supported_trust_ir_cannot_downgrade_through_unsupported_lir() {
    let (module, mut input, proofs) = source(BinOp::Add);
    input
        .blocks
        .get_mut(&input.entry_block)
        .unwrap()
        .instructions[0]
        .opcode = Opcode::Imul;
    assert!(matches!(
        pipeline().prepare_function_with_metrics_for_sealed_core(&input, Some(&proofs), &module, 0),
        Err(PipelineError::AffineLoweringRejected {
            reason: TrustIrAffineLoweringError::Lowering(AffineLoweringError::UnsupportedSource(_)),
            ..
        })
    ));
}

#[test]
fn core_preparation_rejects_correspondingly_mutated_lir_and_machine() {
    let (module, mut input, proofs) = source(BinOp::Add);
    input
        .blocks
        .get_mut(&input.entry_block)
        .unwrap()
        .instructions[0]
        .opcode = Opcode::Isub;
    // Actual selection now produces matching SUB, so a pair-only check passes.
    // The independent TrustIR endpoint must still reject the compilation.
    assert!(matches!(
        pipeline().prepare_function_with_metrics_for_sealed_core(&input, Some(&proofs), &module, 0),
        Err(PipelineError::AffineLoweringRejected {
            reason: TrustIrAffineLoweringError::TrustIrLirMismatch,
            ..
        })
    ));
}

#[test]
fn sealed_core_requires_module_owned_source_before_instruction_selection() {
    let (module, mut input, _) = source(BinOp::Add);
    // Invalid LIR ensures an accidentally reached selector cannot mask the
    // source precondition with an ordinary ISel refusal.
    input.entry_block = Block(u32::MAX);
    for context in [
        None,
        Some(PreparationTrustIrSource::Diagnostic(
            &module,
            &module.functions[0],
        )),
        Some(PreparationTrustIrSource::SealedCore(&module, usize::MAX)),
    ] {
        assert!(matches!(
            pipeline().prepare_function_with_metrics_and_provenance(
                &input,
                None,
                context,
                Aarch64DirectCallAdmission::SealedCore,
            ),
            Err(PipelineError::AffineLoweringRejected {
                reason: TrustIrAffineLoweringError::InvalidTrustIr(_),
                ..
            })
        ));
    }
}

#[test]
fn sealed_core_selects_module_ordinal_not_sparse_id_or_filtered_position() {
    let (mut module, input, proofs) = source(BinOp::Add);
    let declaration = trust_ir::Function::new(
        FuncId::new(900),
        "external_declaration",
        module.functions[0].ty,
        BlockId::new(0),
    );
    module.functions.insert(0, declaration);
    let (_, metrics) = pipeline()
        .prepare_function_with_metrics_for_sealed_core(&input, Some(&proofs), &module, 1)
        .expect("definition after a declaration is selected by its actual ordinal");
    assert!(matches!(
        metrics.pre_optimization_affine_lowering,
        Some(PreOptimizationAffineLowering::Checked(_))
    ));
    assert!(
        pipeline()
            .prepare_function_with_metrics_for_sealed_core(&input, Some(&proofs), &module, 17)
            .is_err()
    );
}

#[test]
fn sealed_core_rejects_mispaired_unsupported_source_before_coverage_skip() {
    let (mut module, input, proofs) = source(BinOp::Add);
    // A valid ordinal, but the wrong module-owned function. Its unsupported
    // body must not hide the source-name mismatch as an uncredited success.
    module.functions[0].name = "unrelated_declaration".into();
    module.functions[0].blocks.clear();
    assert!(matches!(
        pipeline().prepare_function_with_metrics_for_sealed_core(&input, Some(&proofs), &module, 0),
        Err(PipelineError::AffineLoweringRejected {
            reason: TrustIrAffineLoweringError::TrustIrLirMismatch,
            ..
        })
    ));
}

#[test]
fn sealed_core_rejects_same_name_declaration_before_coverage_skip() {
    let (mut module, input, proofs) = source(BinOp::Add);
    module.functions[0].blocks.clear();
    assert!(matches!(
        pipeline().prepare_function_with_metrics_for_sealed_core(&input, Some(&proofs), &module, 0),
        Err(PipelineError::AffineLoweringRejected {
            reason: TrustIrAffineLoweringError::InvalidTrustIr(_),
            ..
        })
    ));
}

#[test]
fn compatibility_path_does_not_inherit_core_check_cost_or_coverage_claim() {
    let (module, input, proofs) = source(BinOp::Add);
    let (_, metrics) = pipeline()
        .prepare_function_with_metrics(&input, Some(&proofs))
        .unwrap();
    assert_eq!(metrics.pre_optimization_affine_lowering, None);
    let (_, metrics) = pipeline()
        .prepare_function_with_metrics_and_trust_ir_module(
            &input,
            Some(&proofs),
            &module,
            &module.functions[0],
        )
        .unwrap();
    assert_eq!(metrics.pre_optimization_affine_lowering, None);
}

fn comparison_source(
    ty: Ty,
    op: trust_ir::ICmpOp,
    guard: bool,
) -> (Module, Function, ProofContext) {
    let mut module = Module::new("predicate_core_seam");
    let signature = module
        .add_func_type(FuncTy {
            params: vec![ty.clone(), ty.clone()],
            returns: vec![Ty::Bool],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = trust_ir::Function::new(
        FuncId::new(47),
        "predicate_core_seam",
        signature,
        BlockId::new(9),
    );
    let (a, b, result) = (ValueId::new(101), ValueId::new(303), ValueId::new(707));
    let mut compare = InstrNode::new(Inst::ICmp {
        op,
        ty: ty.clone(),
        lhs: a,
        rhs: b,
    })
    .with_result(result);
    if guard {
        compare.proofs.push(trust_ir::ProofAnnotation::InBounds);
    }
    function.blocks.push(trust_ir::Block {
        id: function.entry,
        params: vec![(a, ty.clone()), (b, ty)],
        body: vec![
            compare,
            InstrNode::new(Inst::Return {
                values: vec![result],
            }),
        ],
    });
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    let (lir, proofs) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .unwrap();
    (module, lir, proofs)
}

#[test]
fn sealed_core_integer_predicates_all_conditions_and_types_are_actually_checked() {
    use trust_ir::ICmpOp;
    let mut checked = 0;
    for ty in [Ty::I32, Ty::U32, Ty::I64, Ty::U64] {
        for op in [
            ICmpOp::Eq,
            ICmpOp::Ne,
            ICmpOp::Slt,
            ICmpOp::Sle,
            ICmpOp::Sgt,
            ICmpOp::Sge,
            ICmpOp::Ult,
            ICmpOp::Ule,
            ICmpOp::Ugt,
            ICmpOp::Uge,
        ] {
            let (module, input, proofs) = comparison_source(ty.clone(), op, false);
            let (_, metrics) = pipeline()
                .prepare_function_with_metrics_for_sealed_core(&input, Some(&proofs), &module, 0)
                .unwrap_or_else(|error| panic!("{ty:?}/{op:?}: {error}"));
            let Some(PreOptimizationAffineLowering::Checked(stats)) =
                metrics.pre_optimization_affine_lowering
            else {
                panic!("{ty:?}/{op:?} did not reach actual checked Core hook");
            };
            assert_eq!(stats.trust_ir_instructions, 2);
            assert_eq!(stats.lowering.source_instructions, 2);
            assert_eq!(stats.lowering.machine_instructions, 6);
            assert_eq!(stats.lowering.parameter_count, 2);
            checked += 1;
        }
    }
    assert_eq!(checked, 40);
}

#[test]
fn sealed_core_integer_selects_reach_existing_check_and_reject_changed_source() {
    for ty in [Ty::I32, Ty::I64] {
        let (mut module, _, _) = comparison_source(ty.clone(), trust_ir::ICmpOp::Slt, false);
        let signature = module
            .add_func_type(FuncTy {
                params: vec![ty.clone(); 2],
                returns: vec![ty.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let function = &mut module.functions[0];
        function.ty = signature;
        let a = function.blocks[0].params[0].0;
        let b = function.blocks[0].params[1].0;
        let cond = function.blocks[0].body[0].results[0];
        let result = ValueId::new(909);
        function.blocks[0].body.insert(
            1,
            InstrNode::new(Inst::Select {
                ty,
                cond,
                then_val: a,
                else_val: b,
            })
            .with_result(result),
        );
        function.blocks[0].body[2] = InstrNode::new(Inst::Return {
            values: vec![result],
        });
        let (input, proofs) = trust_cg_lower::translate_function_with_license(
            &module.functions[0],
            &module,
            &permit_unlicensed(),
        )
        .unwrap();
        let (_, metrics) = pipeline()
            .prepare_function_with_metrics_for_sealed_core(&input, Some(&proofs), &module, 0)
            .unwrap();
        let Some(PreOptimizationAffineLowering::Checked(stats)) =
            metrics.pre_optimization_affine_lowering
        else {
            panic!("integer select did not reach the existing raw source check");
        };
        assert_eq!(stats.trust_ir_instructions, 3);
        assert_eq!(stats.lowering.source_instructions, 3);
        if let Inst::Select {
            then_val, else_val, ..
        } = &mut module.functions[0].blocks[0].body[1].inst
        {
            std::mem::swap(then_val, else_val);
        }
        assert!(
            pipeline()
                .prepare_function_with_metrics_for_sealed_core(&input, Some(&proofs), &module, 0)
                .is_err()
        );
    }
}

#[test]
fn sealed_core_integer_predicate_guard_semantics_stay_visibly_unchecked() {
    let (module, input, proofs) = comparison_source(Ty::U64, trust_ir::ICmpOp::Ult, true);
    assert!(
        input
            .blocks
            .values()
            .flat_map(|block| &block.instructions)
            .any(|inst| matches!(inst.opcode, Opcode::GuardBoundsCheckDyn { .. })),
        "actual adapter must retain the dynamic bounds guard"
    );
    let (_, metrics) = pipeline()
        .prepare_function_with_metrics_for_sealed_core(&input, Some(&proofs), &module, 0)
        .expect("guarded source remains available through the existing guard-aware pipeline");
    assert!(matches!(metrics.pre_optimization_affine_lowering,
        Some(PreOptimizationAffineLowering::UnsupportedSource { reason })
        if reason.contains("InBounds comparison guard semantics")
    ));
}

#[test]
fn sealed_core_integer_predicate_correlated_lir_and_machine_corruption_is_hard_failure() {
    for ty in [Ty::I32, Ty::U32, Ty::I64, Ty::U64] {
        let (module, mut input, proofs) = comparison_source(ty, trust_ir::ICmpOp::Eq, false);
        input
            .blocks
            .get_mut(&input.entry_block)
            .unwrap()
            .instructions[0]
            .opcode = Opcode::Icmp {
            cond: trust_cg_lower::instructions::IntCC::NotEqual,
        };
        // Real selection follows the corrupted LIR. Only the independently
        // retained module-owned source prevents this correlated substitution.
        assert!(matches!(
            pipeline().prepare_function_with_metrics_for_sealed_core(
                &input,
                Some(&proofs),
                &module,
                0,
            ),
            Err(PipelineError::AffineLoweringRejected {
                reason: TrustIrAffineLoweringError::TrustIrLirMismatch,
                ..
            })
        ));
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its lowerings state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
