// x86-64 host-JIT profile-mode fail-closed coverage.

#![cfg(target_arch = "x86_64")]

use std::collections::HashMap;

use trust_cg_codegen::Compiler;
use trust_cg_codegen::compiler::CompileError;
use trust_cg_codegen::jit::{JitCompiler, JitConfig, JitError, ProfileHookMode};
use trust_cg_ir::types::BlockId;
use trust_ir::{FuncId, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

fn build_answer_module(module_name: &str, function_name: &str) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new(module_name);
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function(function_name, ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let answer = fb.iconst(Ty::I64, 42);
    fb.ret(vec![answer]);
    fb.build();
    mb.build()
}

fn build_linear_branchy_module(module_name: &str, function_name: &str) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new(module_name);
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function(function_name, ty);

    let entry = fb.create_block();
    let hop1 = fb.create_block();
    let hop2 = fb.create_block();
    let done = fb.create_block();

    fb.switch_to_block(entry);
    fb.br(hop1, vec![]);

    fb.switch_to_block(hop1);
    fb.br(hop2, vec![]);

    fb.switch_to_block(hop2);
    fb.br(done, vec![]);

    fb.switch_to_block(done);
    let answer = fb.iconst(Ty::I64, 42);
    fb.ret(vec![answer]);

    fb.build();
    mb.build()
}

fn build_constant_conditional_module(module_name: &str, function_name: &str) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new(module_name);
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function(function_name, ty);

    let entry = fb.create_block();
    let taken = fb.create_block();
    let skipped = fb.create_block();

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::I64, 0);
    let is_zero = fb.icmp(ICmpOp::Eq, Ty::I64, zero, zero);
    fb.condbr(is_zero, skipped, vec![], taken, vec![]);

    fb.switch_to_block(taken);
    let seven = fb.iconst(Ty::I64, 7);
    fb.ret(vec![seven]);

    fb.switch_to_block(skipped);
    let nine = fb.iconst(Ty::I64, 9);
    fb.ret(vec![nine]);

    fb.build();
    mb.build()
}

fn build_late_call_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("x86_64_host_jit_block_counts_late_call");
    let callee_ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut callee = mb.function("callee", callee_ty);
    let callee_entry = callee.create_block();
    callee.switch_to_block(callee_entry);
    let value = callee.iconst(Ty::I64, 55);
    callee.ret(vec![value]);
    callee.build();

    let caller_ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut caller = mb.function("caller", caller_ty);
    let entry = caller.create_block();
    let call_block = caller.create_block();
    caller.switch_to_block(entry);
    caller.br(call_block, vec![]);
    caller.switch_to_block(call_block);
    let called = caller.call(FuncId::new(0), vec![]);
    caller.ret(vec![called]);
    caller.build();

    mb.build()
}

fn build_late_f64_const_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("x86_64_host_jit_block_counts_late_const");
    let ty = mb.add_func_type(vec![], vec![Ty::F64]);
    let mut fb = mb.function("late_const", ty);
    let entry = fb.create_block();
    let body = fb.create_block();
    fb.switch_to_block(entry);
    fb.br(body, vec![]);
    fb.switch_to_block(body);
    let value = fb.fconst(Ty::F64, 3.5);
    fb.ret(vec![value]);
    fb.build();
    mb.build()
}

fn assert_profile_hooks_unsupported(mode: ProfileHookMode) {
    let module = build_answer_module("x86_64_host_jit_unsupported_profile", "answer");
    let err = Compiler::for_host()
        .compile_module_to_jit_with_profile_hooks(&module, &HashMap::new(), mode)
        .expect_err("x86-64 host JIT must reject unsupported profile hooks");

    match err {
        CompileError::Jit(JitError::ProfileHooksUnsupported) => {}
        other => panic!("expected ProfileHooksUnsupported for {mode:?}, got {other:?}"),
    }
}

#[test]
fn x86_64_raw_compile_raw_rejects_block_counts_profile_hooks() {
    let jit = JitCompiler::new(JitConfig {
        profile_hooks: ProfileHookMode::BlockCounts,
        ..JitConfig::default()
    });
    let ext: HashMap<String, *const u8> = HashMap::new();

    match jit.compile_raw(&[], &ext) {
        Err(JitError::ProfileHooksUnsupported) => {}
        Err(other) => panic!("expected raw compile_raw ProfileHooksUnsupported, got {other:?}"),
        Ok(_) => panic!("raw x86-64 compile_raw must reject BlockCounts profile hooks"),
    }
}

// Companion positive coverage below proves the typed Compiler/trust_ir JIT path
// supports x86-64 BlockCounts despite the raw compile_raw boundary above.
#[test]
fn x86_64_host_jit_accepts_block_counts_profile_hooks() {
    let module = build_linear_branchy_module("x86_64_host_jit_block_counts_profile", "linear");
    let result = Compiler::for_host()
        .compile_module_to_jit_with_profile_hooks(
            &module,
            &HashMap::new(),
            ProfileHookMode::BlockCounts,
        )
        .expect("x86-64 host JIT should support block counters");

    let branchy: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("linear")
            .expect("branchy symbol")
            .into_inner()
    };

    assert_eq!(branchy(), 42);
    assert_eq!(branchy(), 42);

    assert_eq!(result.buffer.block_count("linear", BlockId(0)), Some(2));
    assert_eq!(result.buffer.block_count("linear", BlockId(1)), Some(2));
    assert_eq!(result.buffer.block_count("linear", BlockId(2)), Some(2));
    assert_eq!(result.buffer.block_count("linear", BlockId(3)), Some(2));
    assert_eq!(result.buffer.entry_count("linear"), Some(2));

    let mut all = result.buffer.block_counts("linear");
    all.sort_by_key(|&(block, _)| block);
    assert_eq!(all, vec![(0, 2), (1, 2), (2, 2), (3, 2)]);
}

#[test]
fn x86_64_host_jit_block_counts_profile_hooks_count_conditional_targets() {
    let module = build_constant_conditional_module(
        "x86_64_host_jit_block_counts_conditional_profile",
        "selective",
    );
    let result = Compiler::for_host()
        .compile_module_to_jit_with_profile_hooks(
            &module,
            &HashMap::new(),
            ProfileHookMode::BlockCounts,
        )
        .expect("x86-64 host JIT should support conditional block counters");

    let selective: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("selective")
            .expect("selective symbol")
            .into_inner()
    };

    assert_eq!(selective(), 9);
    assert_eq!(selective(), 9);
    assert_eq!(selective(), 9);

    assert_eq!(result.buffer.block_count("selective", BlockId(0)), Some(3));
    assert_eq!(result.buffer.block_count("selective", BlockId(1)), Some(3));
    assert_eq!(result.buffer.block_count("selective", BlockId(2)), Some(0));
    assert_eq!(result.buffer.entry_count("selective"), Some(3));

    let mut all = result.buffer.block_counts("selective");
    all.sort_by_key(|&(block, _)| block);
    assert_eq!(all, vec![(0, 3), (1, 3), (2, 0)]);
}

#[test]
fn x86_64_host_jit_block_counts_preserve_late_call_fixup() {
    let module = build_late_call_module();
    let result = Compiler::for_host()
        .compile_module_to_jit_with_profile_hooks(
            &module,
            &HashMap::new(),
            ProfileHookMode::BlockCounts,
        )
        .expect("x86-64 host JIT should support block counters around calls");

    let caller: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("caller")
            .expect("caller symbol")
            .into_inner()
    };

    assert_eq!(caller(), 55);
    assert_eq!(result.buffer.block_count("caller", BlockId(0)), Some(1));
    assert_eq!(result.buffer.block_count("caller", BlockId(1)), Some(1));
    assert_eq!(result.buffer.block_count("callee", BlockId(0)), Some(1));
}

#[test]
fn x86_64_host_jit_block_counts_preserve_late_rip_const_pool_fixup() {
    let module = build_late_f64_const_module();
    let result = Compiler::for_host()
        .compile_module_to_jit_with_profile_hooks(
            &module,
            &HashMap::new(),
            ProfileHookMode::BlockCounts,
        )
        .expect("x86-64 host JIT should support block counters around const-pool loads");

    let late_const: extern "C" fn() -> f64 = unsafe {
        result
            .buffer
            .get_fn_bound("late_const")
            .expect("late_const symbol")
            .into_inner()
    };

    assert_eq!(late_const(), 3.5);
    assert_eq!(result.buffer.block_count("late_const", BlockId(0)), Some(1));
    assert_eq!(result.buffer.block_count("late_const", BlockId(1)), Some(1));
}

#[test]
fn x86_64_host_jit_rejects_block_counts_and_timing_profile_hooks() {
    assert_profile_hooks_unsupported(ProfileHookMode::BlockCountsAndTiming);
}

#[test]
fn x86_64_host_jit_rejects_call_counts_and_timing_profile_hooks() {
    assert_profile_hooks_unsupported(ProfileHookMode::CallCountsAndTiming);
}

#[test]
fn x86_64_host_jit_accepts_call_counts_profile_hooks() {
    let module = build_answer_module("x86_64_host_jit_call_counts_profile", "profiled_answer");
    let result = Compiler::for_host()
        .compile_module_to_jit_with_profile_hooks(
            &module,
            &HashMap::new(),
            ProfileHookMode::CallCounts,
        )
        .expect("x86-64 host JIT should support function-entry counters");

    let profiled_answer: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("profiled_answer")
            .expect("profiled_answer symbol")
            .into_inner()
    };

    assert_eq!(profiled_answer(), 42);
    assert_eq!(profiled_answer(), 42);
    assert_eq!(result.buffer.entry_count("profiled_answer"), Some(2));
}
