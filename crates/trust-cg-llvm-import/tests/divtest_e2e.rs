#![cfg(feature = "driver")]

// trust-cg-llvm-import / tests / divtest_e2e.rs
//
// Regression coverage for WS2 2002-05-19-DivTest.

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

const LL_DIVTEST: &str = r#"
target triple = "arm64-apple-macosx26.0.0"

@.str = private unnamed_addr constant [4 x i8] c"%d\0A\00", align 1

define void @testL(i64 noundef %0) {
  %2 = alloca i64, align 8
  store i64 %0, ptr %2, align 8
  %3 = load i64, ptr %2, align 8
  %4 = sdiv i64 %3, 16
  %5 = trunc i64 %4 to i32
  %6 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %5)
  %7 = load i64, ptr %2, align 8
  %8 = sdiv i64 %7, 70368744177664
  %9 = trunc i64 %8 to i32
  %10 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %9)
  ret void
}

declare i32 @printf(ptr noundef, ...)

define void @test(i32 noundef %0) {
  %2 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
  %3 = load i32, ptr %2, align 4
  %4 = sdiv i32 %3, 1
  %5 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %4)
  %6 = load i32, ptr %2, align 4
  %7 = sdiv i32 %6, 16
  %8 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %7)
  %9 = load i32, ptr %2, align 4
  %10 = sdiv i32 %9, 262144
  %11 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %10)
  %12 = load i32, ptr %2, align 4
  %13 = sdiv i32 %12, 1073741824
  %14 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %13)
  ret void
}

define i32 @main() {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i64, align 8
  store i32 0, ptr %1, align 4
  store i32 -1048576, ptr %2, align 4
  store i64 -9007199254740992, ptr %3, align 8
  %4 = load i32, ptr %2, align 4
  %5 = add nsw i32 %4, 32
  call void @test(i32 noundef %5)
  %6 = load i32, ptr %2, align 4
  %7 = add nsw i32 %6, 33
  call void @test(i32 noundef %7)
  %8 = load i64, ptr %3, align 8
  %9 = add nsw i64 %8, 64
  call void @testL(i64 noundef %9)
  %10 = load i64, ptr %3, align 8
  %11 = add nsw i64 %10, 65
  call void @testL(i64 noundef %11)
  ret i32 0
}
"#;

const EXPECTED_DIVTEST_STDOUT: &str = "\
-1048544
-65534
-3
0
-1048543
-65533
-3
0
4
-127
5
-127
";

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
fn ws2_divtest_linked_binary_matches_reference_output() {
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        eprintln!(
            "skipping: test requires aarch64-apple-darwin (host is {} / {})",
            std::env::consts::OS,
            std::env::consts::ARCH
        );
        return;
    }

    let object = compile_to_aarch64_object(LL_DIVTEST, "ws2_divtest");
    let dir = unique_temp_dir("divtest");
    let obj_path = dir.join("divtest.o");
    let bin_path = dir.join("divtest");
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
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        EXPECTED_DIVTEST_STDOUT
    );
}
