#![cfg(feature = "driver")]

// trust-cg-llvm-import / tests / bitreverse_intrinsics.rs
//
// Regression coverage for LLVM bitreverse intrinsics imported from clang IR.

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

const LL_BITREVERSE_INTRINSICS: &str = r#"
target triple = "arm64-apple-macosx26.0.0"

declare i32 @llvm.bitreverse.i32(i32)
declare i64 @llvm.bitreverse.i64(i64)

define i32 @main() {
entry:
  %a = call i32 @llvm.bitreverse.i32(i32 -2147483648)
  %b = call i64 @llvm.bitreverse.i64(i64 -9223372036854775808)
  %bt = trunc i64 %b to i32
  %sum = add i32 %a, %bt
  ret i32 %sum
}
"#;

const LL_HANDWRITTEN_REVERSEBITS: &str = r#"
target triple = "arm64-apple-macosx26.0.0"

define i32 @ReverseBits32(i32 %n) {
entry:
  %slot = alloca i32, align 4
  store i32 %n, ptr %slot, align 4
  %3 = load i32, ptr %slot, align 4
  %4 = lshr i32 %3, 1
  %5 = and i32 %4, 1431655765
  %6 = load i32, ptr %slot, align 4
  %7 = and i32 %6, 1431655765
  %8 = shl i32 %7, 1
  %9 = or i32 %5, %8
  store i32 %9, ptr %slot, align 4
  %10 = load i32, ptr %slot, align 4
  %11 = lshr i32 %10, 2
  %12 = and i32 %11, 858993459
  %13 = load i32, ptr %slot, align 4
  %14 = and i32 %13, 858993459
  %15 = shl i32 %14, 2
  %16 = or i32 %12, %15
  store i32 %16, ptr %slot, align 4
  %17 = load i32, ptr %slot, align 4
  %18 = lshr i32 %17, 4
  %19 = and i32 %18, 252645135
  %20 = load i32, ptr %slot, align 4
  %21 = and i32 %20, 252645135
  %22 = shl i32 %21, 4
  %23 = or i32 %19, %22
  store i32 %23, ptr %slot, align 4
  %24 = load i32, ptr %slot, align 4
  %25 = and i32 %24, -16777216
  %26 = lshr i32 %25, 24
  %27 = load i32, ptr %slot, align 4
  %28 = and i32 %27, 16711680
  %29 = lshr i32 %28, 8
  %30 = or i32 %26, %29
  %31 = load i32, ptr %slot, align 4
  %32 = and i32 %31, 65280
  %33 = shl i32 %32, 8
  %34 = or i32 %30, %33
  %35 = load i32, ptr %slot, align 4
  %36 = and i32 %35, 255
  %37 = shl i32 %36, 24
  %38 = or i32 %34, %37
  ret i32 %38
}

define i64 @ReverseBits64(i64 %n) {
entry:
  %slot = alloca i64, align 8
  store i64 %n, ptr %slot, align 8
  %3 = load i64, ptr %slot, align 8
  %4 = lshr i64 %3, 1
  %5 = and i64 %4, 6148914691236517205
  %6 = load i64, ptr %slot, align 8
  %7 = and i64 %6, 6148914691236517205
  %8 = shl i64 %7, 1
  %9 = or i64 %5, %8
  store i64 %9, ptr %slot, align 8
  %10 = load i64, ptr %slot, align 8
  %11 = lshr i64 %10, 2
  %12 = and i64 %11, 3689348814741910323
  %13 = load i64, ptr %slot, align 8
  %14 = and i64 %13, 3689348814741910323
  %15 = shl i64 %14, 2
  %16 = or i64 %12, %15
  store i64 %16, ptr %slot, align 8
  %17 = load i64, ptr %slot, align 8
  %18 = lshr i64 %17, 4
  %19 = and i64 %18, 1085102592571150095
  %20 = load i64, ptr %slot, align 8
  %21 = and i64 %20, 1085102592571150095
  %22 = shl i64 %21, 4
  %23 = or i64 %19, %22
  store i64 %23, ptr %slot, align 8
  %24 = load i64, ptr %slot, align 8
  %25 = and i64 %24, -72057594037927936
  %26 = lshr i64 %25, 56
  %27 = load i64, ptr %slot, align 8
  %28 = and i64 %27, 71776119061217280
  %29 = lshr i64 %28, 40
  %30 = or i64 %26, %29
  %31 = load i64, ptr %slot, align 8
  %32 = and i64 %31, 280375465082880
  %33 = lshr i64 %32, 24
  %34 = or i64 %30, %33
  %35 = load i64, ptr %slot, align 8
  %36 = and i64 %35, 1095216660480
  %37 = lshr i64 %36, 8
  %38 = or i64 %34, %37
  %39 = load i64, ptr %slot, align 8
  %40 = and i64 %39, 255
  %41 = shl i64 %40, 56
  %42 = or i64 %38, %41
  %43 = load i64, ptr %slot, align 8
  %44 = and i64 %43, 65280
  %45 = shl i64 %44, 40
  %46 = or i64 %42, %45
  %47 = load i64, ptr %slot, align 8
  %48 = and i64 %47, 16711680
  %49 = shl i64 %48, 24
  %50 = or i64 %46, %49
  %51 = load i64, ptr %slot, align 8
  %52 = and i64 %51, 4278190080
  %53 = shl i64 %52, 8
  %54 = or i64 %50, %53
  ret i64 %54
}

define i32 @main() {
entry:
  %a = call i32 @ReverseBits32(i32 -2147483648)
  %b = call i64 @ReverseBits64(i64 -9223372036854775808)
  %bt = trunc i64 %b to i32
  %sum = add i32 %a, %bt
  ret i32 %sum
}
"#;

const LL_REVERTBITS_CLANG_O0: &str = include_str!("fixtures/revertBits_clang_o0.ll");

fn handwritten_reversebits_with_default_ssp() -> String {
    let mut src = LL_HANDWRITTEN_REVERSEBITS
        .replace(
            "define i32 @ReverseBits32(i32 %n) {",
            "define i32 @ReverseBits32(i32 %n) #0 {",
        )
        .replace(
            "define i64 @ReverseBits64(i64 %n) {",
            "define i64 @ReverseBits64(i64 %n) #0 {",
        )
        .replace("define i32 @main() {", "define i32 @main() #0 {");
    src.push_str(
        r#"
attributes #0 = { noinline nounwind ssp uwtable "stack-protector-buffer-size"="8" }
"#,
    );
    src
}

fn compile_to_aarch64_object(src: &str, module_name: &str) -> Vec<u8> {
    compile_to_aarch64_object_with_opt(src, module_name, OptLevel::O0)
}

fn compile_to_aarch64_object_with_opt(
    src: &str,
    module_name: &str,
    opt_level: OptLevel,
) -> Vec<u8> {
    let module = import_text(src, module_name).expect("import");
    let compiler = Compiler::new(CompilerConfig {
        opt_level,
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

fn function_disasm<'a>(disasm: &'a str, symbol: &str) -> &'a str {
    let marker = format!("_{}:", symbol.to_lowercase());
    let start = disasm
        .find(&marker)
        .unwrap_or_else(|| panic!("missing disassembly for symbol `{symbol}`:\n{disasm}"));
    let rest = &disasm[start..];
    let search_from = marker.len();
    let end = rest[search_from..]
        .find("\n_")
        .map(|offset| search_from + offset)
        .unwrap_or(rest.len());
    &rest[..end]
}

fn assert_rbit_ret_shape(disasm: &str, symbol: &str, rbit: &str) {
    let body = function_disasm(disasm, symbol);
    assert!(
        body.contains(rbit),
        "{symbol} should emit `{rbit}` directly:\n{body}"
    );
    assert_eq!(
        body.matches("rbit\t").count(),
        1,
        "{symbol} should contain exactly one RBIT:\n{body}"
    );
    assert!(body.contains("ret"), "{symbol} should return:\n{body}");
    for forbidden in [
        "stp\t", "ldp\t", "sub\tsp", "add\tsp", "x29", "x27", "x28", "mov\tw0", "mov\tx0",
    ] {
        assert!(
            !body.contains(forbidden),
            "{symbol} should not contain frame/callee-save/copy pattern `{forbidden}`:\n{body}"
        );
    }
}

fn assert_no_stack_guard_undefined_symbols(obj_path: &Path) {
    let nm = Command::new("nm")
        .arg("-u")
        .arg(obj_path)
        .output()
        .expect("run nm");
    assert!(
        nm.status.success(),
        "nm failed with status {:?}\nstdout:\n{}\nstderr:\n{}",
        nm.status.code(),
        String::from_utf8_lossy(&nm.stdout),
        String::from_utf8_lossy(&nm.stderr)
    );
    let undefined = String::from_utf8_lossy(&nm.stdout);
    assert!(
        !undefined.contains("___stack_chk_guard") && !undefined.contains("___stack_chk_fail"),
        "default ssp bitreverse helpers should not emit stack guard symbols:\n{undefined}"
    );
}

#[test]
fn imported_revertbits_clang_o0_vectorizes_mixed_width_sub_loop() {
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        eprintln!(
            "skipping: test requires aarch64-apple-darwin (host is {} / {})",
            std::env::consts::OS,
            std::env::consts::ARCH
        );
        return;
    }

    let object = compile_to_aarch64_object_with_opt(
        LL_REVERTBITS_CLANG_O0,
        "revertbits_clang_o0",
        OptLevel::O2,
    );
    let dir = unique_temp_dir("revertbits-clang-o0");
    let obj_path = dir.join("revertbits_clang_o0.o");
    let bin_path = dir.join("revertbits_clang_o0");
    fs::write(&obj_path, object).expect("write object");

    let otool = Command::new("otool")
        .arg("-tv")
        .arg(&obj_path)
        .output()
        .expect("run otool");
    assert!(
        otool.status.success(),
        "otool failed with status {:?}\nstdout:\n{}\nstderr:\n{}",
        otool.status.code(),
        String::from_utf8_lossy(&otool.stdout),
        String::from_utf8_lossy(&otool.stderr)
    );
    let disasm = String::from_utf8_lossy(&otool.stdout).to_lowercase();
    let main = function_disasm(&disasm, "main");
    for expected in ["rev32.8b", "rbit.8b", "rev64.16b", "rbit.16b"] {
        assert!(
            main.contains(expected),
            "main should contain vectorized mixed-width bitreverse op `{expected}`:\n{main}"
        );
    }

    link_with_cc(&obj_path, &bin_path);
    let output = Command::new(&bin_path).output().expect("run linked binary");
    assert_eq!(
        output.status.code(),
        Some(0),
        "linked binary should exit cleanly, got {}\nstdout:\n{}\nstderr:\n{}",
        describe_status(output.status),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "0x12345678 -> 0x1e6a2c48\n0x123456789012345 -> 0xa2c48091e6a2c480\n"
    );
}

#[test]
fn bitreverse_intrinsics_link_and_run_without_external_symbols() {
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        eprintln!(
            "skipping: test requires aarch64-apple-darwin (host is {} / {})",
            std::env::consts::OS,
            std::env::consts::ARCH
        );
        return;
    }

    let object = compile_to_aarch64_object(LL_BITREVERSE_INTRINSICS, "bitreverse_intrinsics");
    let dir = unique_temp_dir("bitreverse");
    let obj_path = dir.join("bitreverse.o");
    let bin_path = dir.join("bitreverse");
    fs::write(&obj_path, object).expect("write object");

    let otool = Command::new("otool")
        .arg("-tv")
        .arg(&obj_path)
        .output()
        .expect("run otool");
    assert!(
        otool.status.success(),
        "otool failed with status {:?}\nstdout:\n{}\nstderr:\n{}",
        otool.status.code(),
        String::from_utf8_lossy(&otool.stdout),
        String::from_utf8_lossy(&otool.stderr)
    );
    let disasm = String::from_utf8_lossy(&otool.stdout).to_lowercase();
    assert!(
        disasm.contains("rbit\tw"),
        "i32 bitreverse should select RBIT W-form:\n{disasm}"
    );
    assert!(
        disasm.contains("rbit\tx"),
        "i64 bitreverse should select RBIT X-form:\n{disasm}"
    );

    let nm = Command::new("nm")
        .arg("-u")
        .arg(&obj_path)
        .output()
        .expect("run nm");
    assert!(
        nm.status.success(),
        "nm failed with status {:?}\nstdout:\n{}\nstderr:\n{}",
        nm.status.code(),
        String::from_utf8_lossy(&nm.stdout),
        String::from_utf8_lossy(&nm.stderr)
    );
    let undefined = String::from_utf8_lossy(&nm.stdout);
    assert!(
        !undefined.contains("llvm.bitreverse"),
        "bitreverse intrinsic was left as an unresolved symbol:\n{undefined}"
    );

    link_with_cc(&obj_path, &bin_path);
    let output = Command::new(&bin_path).output().expect("run linked binary");
    assert_eq!(
        output.status.code(),
        Some(2),
        "linked binary should return bitreverse32(msb)+bitreverse64(msb)=2, got {}\nstdout:\n{}\nstderr:\n{}",
        describe_status(output.status),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn handwritten_reversebits_helpers_emit_rbit() {
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        eprintln!(
            "skipping: test requires aarch64-apple-darwin (host is {} / {})",
            std::env::consts::OS,
            std::env::consts::ARCH
        );
        return;
    }

    let object = compile_to_aarch64_object(LL_HANDWRITTEN_REVERSEBITS, "handwritten_reversebits");
    let dir = unique_temp_dir("handwritten-reversebits");
    let obj_path = dir.join("handwritten_reversebits.o");
    let bin_path = dir.join("handwritten_reversebits");
    fs::write(&obj_path, object).expect("write object");

    let otool = Command::new("otool")
        .arg("-tv")
        .arg(&obj_path)
        .output()
        .expect("run otool");
    assert!(
        otool.status.success(),
        "otool failed with status {:?}\nstdout:\n{}\nstderr:\n{}",
        otool.status.code(),
        String::from_utf8_lossy(&otool.stdout),
        String::from_utf8_lossy(&otool.stderr)
    );
    let disasm = String::from_utf8_lossy(&otool.stdout).to_lowercase();
    let reverse32 = function_disasm(&disasm, "ReverseBits32");
    let reverse64 = function_disasm(&disasm, "ReverseBits64");
    assert!(
        reverse32.contains("rbit\tw"),
        "ReverseBits32 should select RBIT W-form:\n{reverse32}"
    );
    assert!(
        reverse64.contains("rbit\tx"),
        "ReverseBits64 should select RBIT X-form:\n{reverse64}"
    );

    link_with_cc(&obj_path, &bin_path);
    let output = Command::new(&bin_path).output().expect("run linked binary");
    assert_eq!(
        output.status.code(),
        Some(2),
        "linked binary should return ReverseBits32(msb)+ReverseBits64(msb)=2, got {}\nstdout:\n{}\nstderr:\n{}",
        describe_status(output.status),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn handwritten_reversebits_helpers_are_frameless_rbit_ret_at_o2() {
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        eprintln!(
            "skipping: test requires aarch64-apple-darwin (host is {} / {})",
            std::env::consts::OS,
            std::env::consts::ARCH
        );
        return;
    }

    let object = compile_to_aarch64_object_with_opt(
        LL_HANDWRITTEN_REVERSEBITS,
        "handwritten_reversebits_o2_shape",
        OptLevel::O2,
    );
    let dir = unique_temp_dir("handwritten-reversebits-o2-shape");
    let obj_path = dir.join("handwritten_reversebits_o2_shape.o");
    fs::write(&obj_path, object).expect("write object");

    let otool = Command::new("otool")
        .arg("-tv")
        .arg(&obj_path)
        .output()
        .expect("run otool");
    assert!(
        otool.status.success(),
        "otool failed with status {:?}\nstdout:\n{}\nstderr:\n{}",
        otool.status.code(),
        String::from_utf8_lossy(&otool.stdout),
        String::from_utf8_lossy(&otool.stderr)
    );
    let disasm = String::from_utf8_lossy(&otool.stdout).to_lowercase();

    assert_rbit_ret_shape(&disasm, "ReverseBits32", "rbit\tw0, w0");
    assert_rbit_ret_shape(&disasm, "ReverseBits64", "rbit\tx0, x0");
}

#[test]
fn default_ssp_handwritten_reversebits_helpers_are_frameless_rbit_ret_at_o2() {
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        eprintln!(
            "skipping: test requires aarch64-apple-darwin (host is {} / {})",
            std::env::consts::OS,
            std::env::consts::ARCH
        );
        return;
    }

    let src = handwritten_reversebits_with_default_ssp();
    let object = compile_to_aarch64_object_with_opt(
        &src,
        "handwritten_reversebits_default_ssp_o2_shape",
        OptLevel::O2,
    );
    let dir = unique_temp_dir("handwritten-reversebits-default-ssp-o2-shape");
    let obj_path = dir.join("handwritten_reversebits_default_ssp_o2_shape.o");
    fs::write(&obj_path, object).expect("write object");

    assert_no_stack_guard_undefined_symbols(&obj_path);

    let otool = Command::new("otool")
        .arg("-tv")
        .arg(&obj_path)
        .output()
        .expect("run otool");
    assert!(
        otool.status.success(),
        "otool failed with status {:?}\nstdout:\n{}\nstderr:\n{}",
        otool.status.code(),
        String::from_utf8_lossy(&otool.stdout),
        String::from_utf8_lossy(&otool.stderr)
    );
    let disasm = String::from_utf8_lossy(&otool.stdout).to_lowercase();

    assert_rbit_ret_shape(&disasm, "ReverseBits32", "rbit\tw0, w0");
    assert_rbit_ret_shape(&disasm, "ReverseBits64", "rbit\tx0, x0");
}
