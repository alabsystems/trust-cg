// trust-cg-codegen/tests/jit_windows_raw_x86_64.rs - Windows raw JIT boundary tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#![cfg(all(target_arch = "x86_64", target_os = "windows"))]

use std::collections::HashMap;

use trust_cg_codegen::Compiler;
use trust_cg_codegen::jit::{JitCompiler, JitConfig, JitError};
use trust_cg_ir::function::{MachFunction, Signature, Type};
use trust_cg_ir::inst::{AArch64Opcode, MachInst};
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::regs::X0;
use trust_ir::Ty;
use trust_ir_build::ModuleBuilder;

fn build_raw_return_const_named(name: &str) -> MachFunction {
    let sig = Signature::new(vec![], vec![Type::I64]);
    let mut func = MachFunction::new(name.to_string(), sig);
    let entry = func.entry;

    let mov = MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(X0), MachOperand::Imm(42)],
    );
    let mov_id = func.push_inst(mov);
    func.append_inst(entry, mov_id);

    let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
    let ret_id = func.push_inst(ret);
    func.append_inst(entry, ret_id);

    func
}

#[test]
fn windows_x64_raw_compile_raw_empty_input_rejects_without_unwind_error() {
    let jit = JitCompiler::new(JitConfig::default());
    let ext: HashMap<String, *const u8> = HashMap::new();

    match jit.compile_raw(&[], &ext) {
        Err(JitError::EmptyExecutableBuffer { function_count }) => {
            assert_eq!(function_count, 0);
        }
        Err(other) => panic!("expected EmptyExecutableBuffer, got {other:?}"),
        Ok(buffer) => panic!(
            "empty Windows x64 compile_raw input must not publish a buffer: symbols={}, allocated_size={}",
            buffer.symbol_count(),
            buffer.allocated_size()
        ),
    }
}

#[test]
fn windows_x64_raw_compile_raw_rejects_untagged_aarch64_machir() {
    let jit = JitCompiler::new(JitConfig::default());
    let ext: HashMap<String, *const u8> = HashMap::new();
    let result = jit.compile_raw(&[build_raw_return_const_named("raw_answer")], &ext);

    match result {
        Err(JitError::RawJitTargetMismatch {
            function,
            host_arch,
        }) => {
            assert_eq!(function, "raw_answer");
            assert_eq!(host_arch, "x86_64");
            let msg = JitError::RawJitTargetMismatch {
                function,
                host_arch,
            }
            .to_string();
            assert!(
                msg.contains("AArch64 MachFunction")
                    && msg.contains("host architecture is x86_64")
                    && msg.contains("typed Compiler/trust_ir JIT"),
                "raw target diagnostic should name the architecture mismatch and typed route: {msg}"
            );
        }
        Err(other) => panic!("expected RawJitTargetMismatch, got {other:?}"),
        Ok(buffer) => panic!(
            "raw Windows x64 compile_raw must not publish target-mismatched AArch64 MachIR: symbols={}, allocated_size={}",
            buffer.symbol_count(),
            buffer.allocated_size()
        ),
    }
}

#[test]
fn windows_x64_typed_compiler_jit_is_supported_route_for_non_empty_input() {
    let mut mb = ModuleBuilder::new("windows_raw_jit_contract_typed_route");
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("typed_answer", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let answer = fb.iconst(Ty::I64, 42);
    fb.ret(vec![answer]);
    fb.build();
    let module = mb.build();

    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Compiler::for_host().compile_module_to_jit should be the Windows typed JIT route");

    let typed_answer: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("typed_answer")
            .expect("typed_answer symbol should be published by the typed JIT")
            .into_inner()
    };

    assert_eq!(typed_answer(), 42);
}
