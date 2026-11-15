// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Actual AArch64 preparation/public JIT retains a layout observation, without
//! making U10 requests or treating resource metadata as proof authority.

use super::*;
use trust_cg_verify::aarch64_stack_limit::frame_depth;
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{Block, Function, Inst, InstrNode, Module, Ty};

fn module() -> Module {
    let mut module = Module::new("static_stack_frame_jit");
    let signature = module
        .add_func_type(FuncTy::unrecorded(vec![Ty::I64], vec![Ty::I64], false))
        .expect("synthetic test signature");
    let mut function = Function::new(FuncId(0), "stack_roundtrip", signature, BlockId(0));
    function.calling_conv = trust_ir::CallingConv::C;
    let mut block = Block::new(BlockId(0)).with_param(ValueId(0), Ty::I64);
    block.body = vec![
        InstrNode::new(Inst::Alloca {
            ty: Ty::I64,
            count: None,
            align: Some(16),
        })
        .with_result(ValueId(1)),
        InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: ValueId(1),
            value: ValueId(0),
            volatile: true,
            align: Some(8),
        }),
        InstrNode::new(Inst::Load {
            ty: Ty::I64,
            ptr: ValueId(1),
            volatile: true,
            align: Some(8),
        })
        .with_result(ValueId(2)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId(2)],
        }),
    ];
    function.blocks = vec![block];
    module.try_add_function(function).expect("test function");
    module
}

#[test]
fn static_stack_frame_public_aarch64_jit_executes_and_matches_independent_depth() {
    let module = module();
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let original = serde_json::to_value(&module).unwrap();
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    // O0 has no module inline/range rewrites. The independently prepared
    // graph is the exact original function/configuration the JIT consumes.
    config.opt_level = OptLevel::O0;
    // The fixture is hand-built and carries no codegen license (`body_gate:
    // None`), which trust-cg refuses by default (roadmap WS7.5, DG-73): the
    // compile states `Permit` explicitly.
    let compiler = Compiler::new(config)
        .with_codegen_license(crate::license_test_support::permit_unlicensed());
    let target_triple = compiler_target_triple(compiler.target_spec);
    let tls = if crate::pipeline::target_triple_uses_elf(&target_triple) {
        trust_cg_lower::TlsDialect::ElfLocalExec
    } else {
        trust_cg_lower::TlsDialect::MachOTlv
    };
    let (lowered, validation) =
        trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
            &module,
            guard_carrier_arch_for_target(Target::Aarch64),
            tls,
            &compiler.codegen_license,
        )
        .unwrap();
    validation.replay_exact_module_bindings(&lowered).unwrap();
    assert_eq!(lowered.len(), 1);
    let (input, proofs) = &lowered[0];
    let pipeline = compiler.build_pipeline(compiler.effective_aarch64_jit_isa_profile());
    let (checked, metrics) = pipeline
        .prepare_function_checked_with_trust_ir_module(
            input,
            Some(proofs),
            &module,
            &module.functions[0],
        )
        .unwrap();
    let (function, _check) = checked.into_parts();
    assert!(function.stack_limit.is_none());
    assert!(metrics.stack_limit_certificate.is_none());
    let report = metrics
        .static_stack_frame()
        .expect("real preparation layout");
    assert!(!report.has_dynamic_allocation);
    assert!(!report.uses_red_zone);
    assert!(report.static_frame_bytes >= 16);
    // A separate existing model visits this final function ONLY in the test.
    // Production reporting reads the retained layout and performs no CFG walk.
    assert_eq!(frame_depth(&function).unwrap(), report.static_frame_bytes);

    let result = compiler
        .compile_module_to_jit(&module, &HashMap::new())
        .unwrap();
    assert!(result.stack_limits.is_none());
    assert_eq!(result.per_function_metrics.len(), 1);
    let observed = &result.per_function_metrics[0];
    assert_eq!(observed.name, "stack_roundtrip");
    assert_eq!(observed.static_stack_frame, Some(report));
    assert!(observed.stack_limit.is_none());
    assert_eq!(serde_json::to_value(&module).unwrap(), original);
    type Roundtrip = extern "C" fn(i64) -> i64;
    // SAFETY: this complete canonical test module declares exactly C(i64)->i64;
    // the result keeps the executable owner alive throughout these calls. Raw
    // lookup here is the native test harness, not product install authority.
    let roundtrip = unsafe { result.buffer.get_fn_bound::<Roundtrip>("stack_roundtrip") }
        .expect("actual JIT symbol");
    for value in [i64::MIN, -239, 0, 239, i64::MAX] {
        assert_eq!(roundtrip.as_ref()(value), value);
    }
}
