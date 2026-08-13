// trust-cg-codegen/tests/x86_64_constant_pool.rs - x86-64 constant pool regressions
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_codegen::x86_64::pipeline::X86RegAllocMode;
use trust_cg_codegen::x86_64::{X86OutputFormat, X86Pipeline, X86PipelineConfig};
use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_ir::x86_64_regs;
use trust_cg_lower::function::Signature;
use trust_cg_lower::instructions::Block;
use trust_cg_lower::types::Type;
use trust_cg_lower::x86_64_isel::{
    X86ISelConstPoolEntry, X86ISelFunction, X86ISelInst, X86ISelOperand,
};

#[cfg(target_arch = "x86_64")]
use std::collections::HashMap;

#[cfg(target_arch = "x86_64")]
use trust_cg_codegen::pipeline::OptLevel;
#[cfg(target_arch = "x86_64")]
use trust_cg_codegen::{Compiler, CompilerConfig};
#[cfg(target_arch = "x86_64")]
use trust_ir::{FCmpOp, Ty};
#[cfg(target_arch = "x86_64")]
use trust_ir_build::ModuleBuilder;

#[test]
fn x86_pipeline_keeps_f32_pos_zero_and_f64_neg_zero_distinct() {
    let sig = Signature {
        params: vec![],
        returns: vec![Type::F64],
    };
    let mut func = X86ISelFunction::new("mixed_zero_constants".to_string(), sig);
    let entry = Block(0);
    func.ensure_block(entry);

    func.const_pool_entries.push(X86ISelConstPoolEntry {
        data: 0.0_f32.to_le_bytes().to_vec(),
        align: 4,
    });
    func.const_pool_entries.push(X86ISelConstPoolEntry {
        data: (-0.0_f64).to_le_bytes().to_vec(),
        align: 8,
    });

    let f32_tmp = VReg::new(0, RegClass::Fpr32);
    let f64_ret = VReg::new(1, RegClass::Fpr64);
    func.next_vreg = 2;

    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::MovssRipRel,
            vec![
                X86ISelOperand::VReg(f32_tmp),
                X86ISelOperand::ConstPoolEntry(0),
            ],
        ),
    );
    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::MovsdRipRel,
            vec![
                X86ISelOperand::VReg(f64_ret),
                X86ISelOperand::ConstPoolEntry(1),
            ],
        ),
    );
    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::MovsdRR,
            vec![
                X86ISelOperand::PReg(x86_64_regs::XMM0),
                X86ISelOperand::VReg(f64_ret),
            ],
        ),
    );
    func.push_inst(entry, X86ISelInst::new(X86Opcode::Ret, vec![]));

    let pipeline = X86Pipeline::new(X86PipelineConfig {
        opt_level: trust_cg_opt::OptLevel::O0,
        output_format: X86OutputFormat::RawBytes,
        emit_frame: false,
        regalloc_mode: X86RegAllocMode::Simplified,
        ..X86PipelineConfig::default()
    });

    let (code, const_pool_data, call_fixups, global_ref_fixups) = pipeline
        .compile_function_with_fixups(&func)
        .expect("x86 constant-pool function should compile");

    assert!(!code.is_empty());
    assert!(call_fixups.is_empty());
    assert!(global_ref_fixups.is_empty());
    assert_eq!(const_pool_data.len(), 16);
    assert_eq!(&const_pool_data[0..4], &0.0_f32.to_le_bytes());
    assert_eq!(&const_pool_data[4..8], &[0, 0, 0, 0]);
    assert_eq!(&const_pool_data[8..16], &(-0.0_f64).to_le_bytes());
}

#[cfg(target_arch = "x86_64")]
fn mixed_zero_jit_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("x86_64_mixed_zero_constant_pool");
    let ty = mb.add_func_type(vec![], vec![Ty::F64]);
    let mut fb = mb.function("mixed_zero_runtime", ty);

    let entry = fb.create_block();
    let then_block = fb.create_block();
    let else_block = fb.create_block();

    fb.switch_to_block(entry);
    let f32_pos_zero = fb.fconst(Ty::F32, 0.0);
    let f32_pos_zero_again = fb.fconst(Ty::F32, 0.0);
    let is_zero = fb.fcmp(FCmpOp::OEq, Ty::F32, f32_pos_zero, f32_pos_zero_again);
    fb.condbr(is_zero, then_block, vec![], else_block, vec![]);

    fb.switch_to_block(then_block);
    let f64_neg_zero = fb.fconst(Ty::F64, -0.0);
    fb.ret(vec![f64_neg_zero]);

    fb.switch_to_block(else_block);
    let f64_neg_zero_else = fb.fconst(Ty::F64, -0.0);
    fb.ret(vec![f64_neg_zero_else]);

    fb.build();
    mb.build()
}

#[cfg(target_arch = "x86_64")]
#[test]
fn x86_host_jit_returns_f64_neg_zero_with_f32_pos_zero_in_same_pool() {
    let mut config = CompilerConfig::for_host_jit();
    config.opt_level = OptLevel::O0;
    let result = Compiler::new(config)
        .compile_module_to_jit(&mixed_zero_jit_module(), &HashMap::new())
        .expect("x86-64 host JIT should compile mixed zero constant-pool module");

    let mixed_zero_runtime: extern "C" fn() -> f64 = unsafe {
        result
            .buffer
            .get_fn_bound("mixed_zero_runtime")
            .expect("mixed_zero_runtime symbol")
            .into_inner()
    };

    assert_eq!(mixed_zero_runtime().to_bits(), (-0.0_f64).to_bits());
}
