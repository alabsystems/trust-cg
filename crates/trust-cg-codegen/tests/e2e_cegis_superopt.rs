// trust-cg-codegen/tests/e2e_cegis_superopt.rs - CEGIS superopt pipeline wiring tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Regression coverage for issue #395: wire the CEGIS superopt pass into the
// pipeline and expose direct observability for integration tests.

use std::sync::atomic::{AtomicU64, Ordering};
use trust_cg_codegen::pipeline::{
    CegisPassStats, OptLevel, Pipeline, PipelineConfig, build_add_test_function,
};
use trust_cg_ir::{
    AArch64Opcode, MachFunction, MachInst, MachOperand, RegClass, Signature, Type as IrType, VReg,
};

use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, FuncId, FuncTy, Function as TrustIrFunction, Inst,
    InstrNode, Module as TrustIrModule, Ty, ValueId,
};

static CEGIS_PIPELINE_COUNTER: AtomicU64 = AtomicU64::new(0);

fn unique_test_triple() -> String {
    let id = CEGIS_PIPELINE_COUNTER.fetch_add(1, Ordering::Relaxed);
    // Use an explicit Apple Mach-O AArch64 triple so object emission satisfies the
    // post-merge fail-closed contract (bare `aarch64-unknown-unknown` triples are
    // rejected before Mach-O emission). The `-apple-` infix keeps the triple a
    // valid Mach-O target while the trailing suffix preserves a unique CEGIS
    // cache key per pipeline.
    format!(
        "aarch64-apple-darwin-cegis-test-{}-{}",
        std::process::id(),
        id
    )
}

fn make_cegis_pipeline() -> Pipeline {
    Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O0,
        cegis_superopt_budget_sec: Some(1),
        target_triple: unique_test_triple(),
        ..Default::default()
    })
}

#[cfg(feature = "verify")]
fn make_no_cegis_pipeline() -> Pipeline {
    Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O0,
        // Explicit Apple Mach-O triple: bare `aarch64-unknown-unknown` now fails
        // closed before object emission under the post-merge contract.
        target_triple: "aarch64-apple-darwin".to_string(),
        ..Default::default()
    })
}

fn build_add_trust_ir() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I32, Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "add32", ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I32), (ValueId::new(1), Ty::I32)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(func.clone());
    (func, module)
}

#[cfg(feature = "verify")]
fn scalar_type_for(class: RegClass) -> IrType {
    match class {
        RegClass::Gpr32 => IrType::I32,
        RegClass::Gpr64 => IrType::I64,
        other => panic!("unsupported CEGIS scalar class in test: {other:?}"),
    }
}

#[cfg(feature = "verify")]
fn alloc_vreg(func: &mut MachFunction, class: RegClass) -> VReg {
    VReg::new(func.alloc_vreg(), class)
}

#[cfg(feature = "verify")]
fn append_inst(func: &mut MachFunction, opcode: AArch64Opcode, operands: Vec<MachOperand>) {
    let id = func.push_inst(MachInst::new(opcode, operands));
    func.append_inst(func.entry, id);
}

#[cfg(feature = "verify")]
fn build_layer_a_mul_zero_func(name: &str, class: RegClass, optimized: bool) -> MachFunction {
    let mut func = MachFunction::new(
        name.to_string(),
        Signature::new(vec![], vec![scalar_type_for(class)]),
    );
    let v_zero = alloc_vreg(&mut func, class);
    let v_lhs = alloc_vreg(&mut func, class);
    let v_dst = alloc_vreg(&mut func, class);

    append_inst(
        &mut func,
        AArch64Opcode::Movz,
        vec![MachOperand::VReg(v_zero), MachOperand::Imm(0)],
    );
    append_inst(
        &mut func,
        AArch64Opcode::Movz,
        vec![MachOperand::VReg(v_lhs), MachOperand::Imm(7)],
    );
    if optimized {
        append_inst(
            &mut func,
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(v_dst), MachOperand::Imm(0)],
        );
    } else {
        append_inst(
            &mut func,
            AArch64Opcode::MulRR,
            vec![
                MachOperand::VReg(v_dst),
                MachOperand::VReg(v_lhs),
                MachOperand::VReg(v_zero),
            ],
        );
    }

    append_inst(
        &mut func,
        AArch64Opcode::Ret,
        vec![MachOperand::VReg(v_dst)],
    );
    func
}

#[cfg(feature = "verify")]
fn build_layer_b_movz_add_func(
    name: &str,
    class: RegClass,
    src_imm: i64,
    add_imm: i64,
    optimized: bool,
) -> MachFunction {
    let mut func = MachFunction::new(
        name.to_string(),
        Signature::new(vec![], vec![scalar_type_for(class)]),
    );
    let v_src = alloc_vreg(&mut func, class);
    let v_imm = alloc_vreg(&mut func, class);
    let v_dst = alloc_vreg(&mut func, class);

    append_inst(
        &mut func,
        AArch64Opcode::Movz,
        vec![MachOperand::VReg(v_src), MachOperand::Imm(src_imm)],
    );
    if optimized {
        append_inst(
            &mut func,
            AArch64Opcode::AddRI,
            vec![
                MachOperand::VReg(v_dst),
                MachOperand::VReg(v_src),
                MachOperand::Imm(add_imm),
            ],
        );
    } else {
        append_inst(
            &mut func,
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(v_imm), MachOperand::Imm(add_imm)],
        );
        append_inst(
            &mut func,
            AArch64Opcode::AddRR,
            vec![
                MachOperand::VReg(v_dst),
                MachOperand::VReg(v_src),
                MachOperand::VReg(v_imm),
            ],
        );
    }

    append_inst(
        &mut func,
        AArch64Opcode::Ret,
        vec![MachOperand::VReg(v_dst)],
    );
    func
}

#[cfg(feature = "verify")]
fn compile_ir_object(pipeline: &Pipeline, mut func: MachFunction) -> Vec<u8> {
    pipeline
        .compile_ir_function(&mut func)
        .expect("hand-crafted CEGIS codegen case should compile")
}

#[cfg(feature = "verify")]
fn assert_cegis_codegen_matches_hand_optimized(
    case_name: &str,
    source: MachFunction,
    hand_optimized: MachFunction,
    check_stats: fn(&CegisPassStats),
) {
    let mut probe = source.clone();
    let stats = make_cegis_pipeline()
        .run_cegis_superopt(&mut probe)
        .expect("CEGIS pass should run for the probe function");
    check_stats(&stats);
    assert!(
        stats.verified >= 1,
        "{case_name}: expected at least one proven rewrite, got {stats:?}"
    );

    let no_cegis = make_no_cegis_pipeline();
    let unoptimized_obj = compile_ir_object(&no_cegis, source.clone());
    let hand_optimized_obj = compile_ir_object(&no_cegis, hand_optimized);
    assert_ne!(
        unoptimized_obj, hand_optimized_obj,
        "{case_name}: disabled CEGIS output should differ from the hand-optimized baseline"
    );

    let cegis_obj = compile_ir_object(&make_cegis_pipeline(), source);
    assert_eq!(
        cegis_obj, hand_optimized_obj,
        "{case_name}: CEGIS-enabled codegen must match the hand-optimized object bytes"
    );
}

#[test]
fn test_cegis_flag_is_noop_when_disabled() {
    let pipeline = Pipeline::new(PipelineConfig::default());
    let mut func = build_add_test_function();

    assert!(pipeline.run_cegis_superopt(&mut func).is_none());
}

#[cfg(feature = "verify")]
#[test]
fn test_cegis_flag_runs_pass() {
    let pipeline = make_cegis_pipeline();
    let mut func = build_add_test_function();

    let stats = pipeline
        .run_cegis_superopt(&mut func)
        .expect("CEGIS pass should run when budget is enabled");

    assert_eq!(stats.functions_seen, 1);
    assert_eq!(stats.cache_misses, 1);
    assert_eq!(stats.cache_puts, 1);
}

#[cfg(feature = "verify")]
#[test]
fn test_cegis_cache_hit_on_repeat() {
    let pipeline = make_cegis_pipeline();

    let mut func1 = build_add_test_function();
    let first = pipeline
        .run_cegis_superopt(&mut func1)
        .expect("first CEGIS run should execute");
    assert_eq!(first.cache_misses, 1);
    assert_eq!(first.cache_puts, 1);

    let mut func2 = build_add_test_function();
    let second = pipeline
        .run_cegis_superopt(&mut func2)
        .expect("second CEGIS run should execute");
    assert_eq!(second.functions_seen, 1);
    assert_eq!(second.cache_hits, 1);
    assert_eq!(second.cache_misses, 0);
}

#[test]
fn test_full_pipeline_with_cegis_flag() {
    let pipeline = make_cegis_pipeline();
    let (trust_ir_func, module) = build_add_trust_ir();
    let (lir_func, _) = trust_cg_lower::translate_function(&trust_ir_func, &module)
        .expect("trust_ir add function should translate");

    let obj_bytes = pipeline
        .compile_function(&lir_func)
        .expect("full pipeline should compile with the CEGIS flag enabled");

    assert!(
        !obj_bytes.is_empty(),
        "pipeline should produce non-empty object bytes"
    );
}

#[cfg(feature = "verify")]
#[test]
fn test_cegis_codegen_layer_a_mul_zero_i32_matches_hand_movz() {
    let source = build_layer_a_mul_zero_func("cegis_layer_a_i32_codegen", RegClass::Gpr32, false);
    let hand_optimized =
        build_layer_a_mul_zero_func("cegis_layer_a_i32_codegen", RegClass::Gpr32, true);

    assert_cegis_codegen_matches_hand_optimized(
        "Layer A i32 MulRR-by-zero",
        source,
        hand_optimized,
        |stats| {
            assert!(
                stats.layer_a_committed >= 1,
                "Layer A i32 case should commit, got {stats:?}"
            );
            assert_eq!(stats.layer_b_committed, 0);
        },
    );
}

#[cfg(feature = "verify")]
#[test]
fn test_cegis_codegen_layer_b_movz_add_small_imm_matches_hand_addri() {
    let source = build_layer_b_movz_add_func(
        "cegis_layer_b_i32_imm7_codegen",
        RegClass::Gpr32,
        3,
        7,
        false,
    );
    let hand_optimized = build_layer_b_movz_add_func(
        "cegis_layer_b_i32_imm7_codegen",
        RegClass::Gpr32,
        3,
        7,
        true,
    );

    assert_cegis_codegen_matches_hand_optimized(
        "Layer B i32 Movz+AddRR imm7",
        source,
        hand_optimized,
        |stats| {
            assert!(
                stats.layer_b_committed >= 1,
                "Layer B imm7 case should commit, got {stats:?}"
            );
            assert_eq!(stats.layer_a_committed, 0);
        },
    );
}

#[cfg(feature = "verify")]
#[test]
fn test_cegis_codegen_layer_b_movz_add_max_imm12_matches_hand_addri() {
    let source = build_layer_b_movz_add_func(
        "cegis_layer_b_i32_imm4095_codegen",
        RegClass::Gpr32,
        11,
        4095,
        false,
    );
    let hand_optimized = build_layer_b_movz_add_func(
        "cegis_layer_b_i32_imm4095_codegen",
        RegClass::Gpr32,
        11,
        4095,
        true,
    );

    assert_cegis_codegen_matches_hand_optimized(
        "Layer B i32 Movz+AddRR imm4095",
        source,
        hand_optimized,
        |stats| {
            assert!(
                stats.layer_b_committed >= 1,
                "Layer B imm4095 case should commit, got {stats:?}"
            );
            assert_eq!(stats.layer_a_committed, 0);
        },
    );
}
