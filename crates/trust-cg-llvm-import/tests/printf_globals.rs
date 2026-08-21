#![cfg(feature = "driver")]

// trust-cg-llvm-import / tests / printf_globals.rs
//
// Regression coverage for WS2 imported printf string globals.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus};
use std::time::{SystemTime, UNIX_EPOCH};

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::macho::linker::MachOParser;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_cg_llvm_import::import_text;

#[cfg(unix)]
use std::os::unix::process::ExitStatusExt;

/// These fixtures parse Mach-O structure (MachOParser sections/relocations),
/// so pin the aarch64-apple-darwin spec explicitly: `Compiler::new` derives
/// the object format from the HOST, which on Linux emits ELF and fails the
/// Mach-O parse. Mach-O byte emission is host-independent.
fn macho_compiler(config: CompilerConfig) -> Compiler {
    let spec = trust_cg_codegen::target::TargetSpec::parse("aarch64-apple-darwin")
        .expect("aarch64-apple-darwin parses");
    Compiler::new_for_target_spec(config, spec)
}

const LL_PRINTF_STRING_GLOBAL: &str = r#"
@.str = private unnamed_addr constant [4 x i8] c"%d\0A\00", align 1

declare i32 @printf(ptr noundef, ...)

define i32 @main() {
entry:
  %call = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef 7)
  ret i32 0
}
"#;

const LL_MUTABLE_BYTE_GLOBALS: &str = r#"
@main.flags = internal global [4 x i8] zeroinitializer, align 1
@main.bytes = internal global [4 x i8] [i8 1, i8 2, i8 3, i8 4], align 1

define i32 @main(i32 %idx) {
entry:
  %idx64 = sext i32 %idx to i64
  %p = getelementptr inbounds [4 x i8], ptr @main.flags, i64 0, i64 %idx64
  store i8 7, ptr %p, align 1
  ret i32 0
}
"#;

const LL_NOTTEST: &str = r#"
@.str = private unnamed_addr constant [26 x i8] c"Bitwise Not: %d %d %d %d\0A\00", align 1
@.str.1 = private unnamed_addr constant [32 x i8] c"Boolean Not: %d %d %d %d %d %d\0A\00", align 1

define void @testBitWiseNot(i32 noundef %0, i32 noundef %1, i32 noundef %2, i32 noundef %3) {
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  store i32 %0, ptr %5, align 4
  store i32 %1, ptr %6, align 4
  store i32 %2, ptr %7, align 4
  store i32 %3, ptr %8, align 4
  %9 = load i32, ptr %5, align 4
  %10 = xor i32 %9, -1
  %11 = load i32, ptr %6, align 4
  %12 = xor i32 %11, -1
  %13 = load i32, ptr %7, align 4
  %14 = xor i32 %13, -1
  %15 = load i32, ptr %8, align 4
  %16 = xor i32 %15, -1
  %17 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %10, i32 noundef %12, i32 noundef %14, i32 noundef %16)
  ret void
}

declare i32 @printf(ptr noundef, ...)

define void @testBooleanNot(i32 noundef %0, i32 noundef %1, i32 noundef %2, i32 noundef %3) {
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  store i32 %0, ptr %5, align 4
  store i32 %1, ptr %6, align 4
  store i32 %2, ptr %7, align 4
  store i32 %3, ptr %8, align 4
  %9 = load i32, ptr %5, align 4
  %10 = icmp sgt i32 %9, 0
  br i1 %10, label %11, label %14
11:
  %12 = load i32, ptr %6, align 4
  %13 = icmp sgt i32 %12, 0
  br label %14
14:
  %15 = phi i1 [ false, %4 ], [ %13, %11 ]
  %16 = xor i1 %15, true
  %17 = zext i1 %16 to i32
  %18 = load i32, ptr %5, align 4
  %19 = icmp sgt i32 %18, 0
  br i1 %19, label %20, label %23
20:
  %21 = load i32, ptr %7, align 4
  %22 = icmp sgt i32 %21, 0
  br label %23
23:
  %24 = phi i1 [ false, %14 ], [ %22, %20 ]
  %25 = xor i1 %24, true
  %26 = zext i1 %25 to i32
  %27 = load i32, ptr %5, align 4
  %28 = icmp sgt i32 %27, 0
  br i1 %28, label %29, label %32
29:
  %30 = load i32, ptr %8, align 4
  %31 = icmp sgt i32 %30, 0
  br label %32
32:
  %33 = phi i1 [ false, %23 ], [ %31, %29 ]
  %34 = xor i1 %33, true
  %35 = zext i1 %34 to i32
  %36 = load i32, ptr %6, align 4
  %37 = icmp sgt i32 %36, 0
  br i1 %37, label %38, label %41
38:
  %39 = load i32, ptr %7, align 4
  %40 = icmp sgt i32 %39, 0
  br label %41
41:
  %42 = phi i1 [ false, %32 ], [ %40, %38 ]
  %43 = xor i1 %42, true
  %44 = zext i1 %43 to i32
  %45 = load i32, ptr %6, align 4
  %46 = icmp sgt i32 %45, 0
  br i1 %46, label %47, label %50
47:
  %48 = load i32, ptr %8, align 4
  %49 = icmp sgt i32 %48, 0
  br label %50
50:
  %51 = phi i1 [ false, %41 ], [ %49, %47 ]
  %52 = xor i1 %51, true
  %53 = zext i1 %52 to i32
  %54 = load i32, ptr %7, align 4
  %55 = icmp sgt i32 %54, 0
  br i1 %55, label %56, label %59
56:
  %57 = load i32, ptr %8, align 4
  %58 = icmp sgt i32 %57, 0
  br label %59
59:
  %60 = phi i1 [ false, %50 ], [ %58, %56 ]
  %61 = xor i1 %60, true
  %62 = zext i1 %61 to i32
  %63 = call i32 (ptr, ...) @printf(ptr noundef @.str.1, i32 noundef %17, i32 noundef %26, i32 noundef %35, i32 noundef %44, i32 noundef %53, i32 noundef %62)
  ret void
}

define i32 @main() {
  call void @testBitWiseNot(i32 noundef 1, i32 noundef 2, i32 noundef -3, i32 noundef 5)
  call void @testBooleanNot(i32 noundef 1, i32 noundef 2, i32 noundef -3, i32 noundef 5)
  ret i32 0
}
"#;

fn compile_to_aarch64_object(src: &str, module_name: &str) -> Vec<u8> {
    let module = import_text(src, module_name).expect("import");
    let compiler = macho_compiler(CompilerConfig {
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
fn imported_printf_string_global_emits_const_data_and_relocation() {
    let module = import_text(LL_PRINTF_STRING_GLOBAL, "printf_string").expect("import");
    assert_eq!(module.globals[0].align, Some(1));
    let compiler = macho_compiler(CompilerConfig {
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
    let result = compiler.compile(&module).expect("compile");
    assert!(
        result
            .object_code
            .windows(4)
            .any(|window| window == b"%d\n\0"),
        "object should contain the imported format string"
    );

    let parsed = MachOParser::parse(&result.object_code).expect("parse Mach-O object");
    let const_data = parsed
        .sections
        .iter()
        .find(|section| section.segment == "__TEXT" && section.name == "__const")
        .expect("__TEXT,__const section");
    assert_eq!(const_data.data, b"%d\n\0");

    let string_symbol_idx = parsed
        .symbols
        .iter()
        .position(|symbol| symbol.name == "_.str")
        .expect("string global symbol");
    let const_section_ordinal = parsed
        .sections
        .iter()
        .position(|section| section.segment == "__TEXT" && section.name == "__const")
        .map(|index| (index + 1) as u8)
        .unwrap();
    assert_eq!(
        parsed.symbols[string_symbol_idx].section,
        const_section_ordinal
    );
    let text = parsed
        .sections
        .iter()
        .find(|section| section.name == "__text")
        .expect("__text section");
    assert!(
        text.relocations
            .iter()
            .any(|reloc| reloc.symbol_index as usize == string_symbol_idx),
        "text should relocate the GlobalRef ADRP/ADD pair against _.str; string_idx={string_symbol_idx}, relocs={:?}, symbols={:?}",
        text.relocations,
        parsed.symbols
    );
}

#[test]
fn imported_mutable_byte_globals_emit_writable_data_and_relocation() {
    let module = import_text(LL_MUTABLE_BYTE_GLOBALS, "mutable_byte_globals").expect("import");
    assert!(
        module.globals.iter().all(|global| global.mutable),
        "test globals should preserve LLVM `global` mutability"
    );
    assert!(
        module.globals.iter().all(|global| global.align == Some(1)),
        "explicit LLVM byte-global alignment must survive import"
    );

    let object = compile_to_aarch64_object(LL_MUTABLE_BYTE_GLOBALS, "mutable_byte_globals");
    let parsed = MachOParser::parse(&object).expect("parse Mach-O object");
    let data_section_idx = parsed
        .sections
        .iter()
        .position(|section| section.segment == "__DATA" && section.name == "__data")
        .expect("__DATA,__data section");
    let data = &parsed.sections[data_section_idx];
    assert_eq!(data.data, &[0, 0, 0, 0, 1, 2, 3, 4]);
    assert!(
        parsed
            .sections
            .iter()
            .all(|section| !(section.segment == "__TEXT" && section.name == "__cstring")),
        "mutable byte globals must not be emitted as __TEXT,__cstring"
    );

    let data_section_ordinal = (data_section_idx + 1) as u8;
    let flags_symbol_idx = parsed
        .symbols
        .iter()
        .position(|symbol| symbol.name == "_main.flags")
        .expect("_main.flags symbol");
    let bytes_symbol_idx = parsed
        .symbols
        .iter()
        .position(|symbol| symbol.name == "_main.bytes")
        .expect("_main.bytes symbol");
    let flags_symbol = &parsed.symbols[flags_symbol_idx];
    let bytes_symbol = &parsed.symbols[bytes_symbol_idx];
    assert_eq!(flags_symbol.section, data_section_ordinal);
    assert_eq!(flags_symbol.value, data.addr);
    assert_eq!(bytes_symbol.section, data_section_ordinal);
    assert_eq!(bytes_symbol.value, data.addr + 4);

    let text = parsed
        .sections
        .iter()
        .find(|section| section.segment == "__TEXT" && section.name == "__text")
        .expect("__TEXT,__text section");
    assert!(
        text.relocations
            .iter()
            .any(|reloc| reloc.symbol_index as usize == flags_symbol_idx),
        "text should relocate the GlobalRef ADRP/ADD pair against _main.flags; flags_idx={flags_symbol_idx}, relocs={:?}, symbols={:?}",
        text.relocations,
        parsed.symbols
    );
}

#[test]
fn imported_nottest_linked_binary_matches_clang_stdout() {
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        eprintln!(
            "skipping: test requires aarch64-apple-darwin (host is {} / {})",
            std::env::consts::OS,
            std::env::consts::ARCH
        );
        return;
    }

    let object = compile_to_aarch64_object(LL_NOTTEST, "ws2_nottest");
    let dir = unique_temp_dir("nottest");
    let obj_path = dir.join("nottest.o");
    let bin_path = dir.join("nottest");
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
        "Bitwise Not: -2 -3 2 -6\nBoolean Not: 0 1 0 1 0 1\n"
    );
}
