// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! The historical canonical bounds fixture is now refused before a generic
//! trap can erase Rust panic semantics. This is not native execution evidence.

#![cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTy, Function, ICmpOp, Inst, InstrNode, Module, Ty,
    ValueId,
};

fn module(bound: u64) -> Module {
    let mut module = Module::new("canonical_runtime_bounds");
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::Ptr],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "checked_index", signature, BlockId::new(0));
    let v = ValueId::new;
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![(v(0), Ty::I64), (v(1), Ty::Ptr)];
    block.body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(i128::from(bound)),
        })
        .with_result(v(2)),
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Ult,
            ty: Ty::I64,
            lhs: v(0),
            rhs: v(2),
        })
        .with_result(v(3)),
        InstrNode::new(Inst::Assert {
            cond: v(3),
            kind: trust_ir::AssertKind::Unspecified,
            site: None,
        }),
        InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: v(1),
            value: v(0),
            volatile: false,
            align: Some(8),
        }),
        InstrNode::new(Inst::Return { values: vec![v(0)] }),
    ];
    function.blocks.push(block);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

#[test]
fn canonical_bounds_assert_is_refused_at_every_compiler_optimization() {
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        for bound in [0, 8, 4096, i32::MAX as u64] {
            let module = module(bound);
            assert!(trust_ir_build::validate_module(&module).is_empty());
            let compiler = Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level,
                    ..CompilerConfig::default()
                },
                TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap(),
            )
            .with_codegen_license(permit_unlicensed());
            let error = compiler.compile(&module).unwrap_err();
            assert!(
                error.to_string().contains("unspecified panic kind"),
                "{error}"
            );
            assert!(
                error.to_string().contains("require_assert_panic_kinds"),
                "{error}"
            );
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
