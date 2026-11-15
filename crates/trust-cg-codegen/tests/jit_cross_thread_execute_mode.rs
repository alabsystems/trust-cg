// Cross-thread execution of a JIT function pointer published on another
// thread. On Apple Silicon the caller thread must first enter MAP_JIT execute
// mode (`ensure_jit_execute_mode`); on Linux that call is a no-op and the
// control is plain cross-thread execution. Required-floor target: registered
// in scripts/check_linux_aarch64.py.
#![cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]

use std::collections::HashMap;
use std::sync::Arc;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::{Compiler, CompilerConfig, Target, ensure_jit_execute_mode};
use trust_ir::{BinOp, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY_NAME: &str = "request_1_1_cross_thread_execute_mode";
const CHILD_ENV: &str = "TRUST_CG_JIT_CROSS_THREAD_EXEC_CHILD";

fn build_smoke_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("jit_cross_thread_execute_mode");
    let entry_ty = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);

    {
        let mut fb = mb.function(ENTRY_NAME, entry_ty);
        let entry = fb.create_block();
        let input = fb.add_block_param(entry, Ty::U64);

        fb.switch_to_block(entry);
        let one = fb.iconst(Ty::U64, 1);
        let result = fb.binop(BinOp::Add, Ty::U64, input, one);
        fb.ret(vec![result]);
        fb.build();
    }

    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn compile_smoke_module() -> trust_cg_codegen::ExecutableBuffer {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = OptLevel::O3;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(&build_smoke_module(), &HashMap::new())
        .expect("compile smoke module")
        .buffer
}

fn run_child() {
    let buffer = Arc::new(compile_smoke_module());
    let entry: extern "C" fn(u64) -> u64 = unsafe {
        buffer
            .get_fn_bound(ENTRY_NAME)
            .expect("entry symbol should exist")
            .into_inner()
    };
    let keepalive = Arc::clone(&buffer);

    let joined = std::thread::spawn(move || {
        ensure_jit_execute_mode();
        let actual = entry(41);
        drop(keepalive);
        actual
    })
    .join()
    .expect("JIT caller thread should not panic");

    assert_eq!(joined, 42);
}

#[test]
fn jit_function_pointer_survives_cross_thread_execute_mode() {
    if std::env::var_os(CHILD_ENV).is_some() {
        run_child();
        return;
    }

    let current_exe = std::env::current_exe().expect("current test binary");
    let output = std::process::Command::new(current_exe)
        .arg("jit_function_pointer_survives_cross_thread_execute_mode")
        .arg("--exact")
        .arg("--nocapture")
        .env(CHILD_ENV, "1")
        .output()
        .expect("run cross-thread JIT child");

    assert!(
        output.status.success(),
        "cross-thread JIT child should execute after ensure_jit_execute_mode; status={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
