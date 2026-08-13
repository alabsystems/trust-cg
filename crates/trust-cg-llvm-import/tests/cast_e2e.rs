#![cfg(feature = "driver")]

// trust-cg-llvm-import / tests / cast_e2e.rs
//
// Regression coverage for WS2 imported integer cast chains.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus};
use std::time::{SystemTime, UNIX_EPOCH};

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_cg_llvm_import::import_text;

#[cfg(unix)]
use std::os::unix::process::ExitStatusExt;

const LL_CASTTEST_TRUNC_I8: &str = r#"
target triple = "arm64-apple-macosx26.0.0"

@.str = private unnamed_addr constant [4 x i8] c"%d\0A\00", align 1

define i32 @test(i32 noundef %0) {
  %2 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
  %3 = load i32, ptr %2, align 4
  %4 = trunc i32 %3 to i8
  %5 = zext i8 %4 to i32
  ret i32 %5
}

define i32 @main() {
  %1 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  %2 = call i32 @test(i32 noundef 123456)
  %3 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %2)
  ret i32 0
}

declare i32 @printf(ptr noundef, ...)
"#;

fn compile_to_aarch64_object(src: &str, module_name: &str) -> Vec<u8> {
    let module = import_text(src, module_name).expect("import");
    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        target: Target::Aarch64,
        emit_proofs: false,
        trace_level: CompilerTraceLevel::None,
        emit_debug: false,
        parallel: false,
        cegis_superopt_budget_sec: None,
        enable_fsym_trust_ir_preflight: false,
        enable_jit_fast_regalloc: false,
        jit_validation_mode_override: None,
        panic_unwind: false,
    });
    compiler
        .compile(&module)
        .unwrap_or_else(|e| panic!("compile `{module_name}` failed: {e}"))
        .object_code
}

fn unique_temp_dir(name: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time before unix epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "trust-cg-import-{name}-{}-{nanos}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).expect("create temp dir");
    dir
}

fn link_with_cc(obj_path: &Path, bin_path: &Path) {
    let output = Command::new("cc")
        .arg(obj_path)
        .arg("-o")
        .arg(bin_path)
        .output()
        .expect("run cc");
    assert!(
        output.status.success(),
        "cc failed with status {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn describe_status(status: ExitStatus) -> String {
    if let Some(code) = status.code() {
        return format!("exit {code}");
    }
    #[cfg(unix)]
    if let Some(signal) = status.signal() {
        return format!("signal {signal}");
    }
    "unknown status".to_string()
}

#[test]
fn ws2_casttest_trunc_i8_linked_binary_prints_64() {
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        eprintln!(
            "skipping: test requires aarch64-apple-darwin (host is {} / {})",
            std::env::consts::OS,
            std::env::consts::ARCH
        );
        return;
    }

    let object = compile_to_aarch64_object(LL_CASTTEST_TRUNC_I8, "ws2_casttest_trunc_i8");
    let dir = unique_temp_dir("casttest-trunc-i8");
    let obj_path = dir.join("casttest.o");
    let bin_path = dir.join("casttest");
    fs::write(&obj_path, object).expect("write object");
    link_with_cc(&obj_path, &bin_path);

    let output = Command::new(&bin_path).output().expect("run linked binary");
    assert!(
        output.status.success(),
        "linked binary failed with {}\nstdout:\n{}\nstderr:\n{}",
        describe_status(output.status),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout), "64\n");
}
