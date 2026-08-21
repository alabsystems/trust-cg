// E2E integration tests: trust_ir -> Trust Codegen pipeline -> Mach-O .o -> link -> run
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// These tests verify the complete compilation pipeline produces runnable
// AArch64 binaries on macOS (Apple Silicon). This is the most important
// milestone for Trust Codegen: proving it can generate real executables.

use std::fs;
use std::io::{ErrorKind, Write};
use std::process::{Command, Output};

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::pipeline::{self, OptLevel};

// trust_ir imports
use trust_ir::value::GlobalId;
use trust_ir::{BinOp, Global, ICmpOp, Inst, InstrNode, Linkage, TlsModel};
use trust_ir::{
    Block as TrustIrBlock, Constant, FuncTy, Function as TrustIrFunction, Module as TrustIrModule,
    Ty,
};
use trust_ir::{BlockId, FuncId, ValueId};

// =============================================================================
// Helper: write bytes to a temp file and return the path
// =============================================================================

/// These e2e fixtures assert Mach-O bytes (and, on macOS hosts, feed them to
/// otool/nm/ld). `Compiler::new` derives the object format from the HOST
/// (`TargetSpec::default_for_architecture`), which on a Linux host emits ELF
/// and fails every Mach-O assertion below — so pin the historical
/// aarch64-apple-darwin spec explicitly. Object emission is pure byte
/// generation and host-independent; the link-and-run tests keep their
/// existing macOS host gates.
fn macho_compiler(config: CompilerConfig) -> Compiler {
    let spec = trust_cg_codegen::target::TargetSpec::parse("aarch64-apple-darwin")
        .expect("aarch64-apple-darwin parses");
    Compiler::new_for_target_spec(config, spec)
}

fn write_temp_file(name: &str, suffix: &str, contents: &[u8]) -> std::path::PathBuf {
    let dir = std::env::temp_dir().join("trust_cg_e2e_tests");
    fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join(format!("{}{}", name, suffix));
    let mut f = fs::File::create(&path).expect("create temp file");
    f.write_all(contents).expect("write temp file");
    path
}

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

fn skip_host_tool_test(reason: impl std::fmt::Display) {
    eprintln!("SKIP: AArch64 Mach-O host integration test unavailable: {reason}");
}

fn output_text(output: &Output) -> String {
    format!(
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

fn tool_lacks_macho_support(output: &Output) -> bool {
    let text = output_text(output).to_lowercase();
    text.contains("file format not recognized")
        || text.contains("unknown file type")
        || text.contains("unsupported file format")
        || text.contains("unsupported object file")
        || text.contains("not a mach-o file")
}

fn run_otool(args: &[&str]) -> Option<String> {
    let output = match Command::new("otool").args(args).output() {
        Ok(output) => output,
        Err(err) if err.kind() == ErrorKind::NotFound => {
            skip_host_tool_test("otool is not installed");
            return None;
        }
        Err(err) => panic!("failed to run otool: {err}"),
    };
    assert!(
        output.status.success(),
        "otool failed: {}",
        output_text(&output)
    );
    Some(String::from_utf8_lossy(&output.stdout).to_string())
}

fn run_macho_nm(path: &std::path::Path) -> Option<String> {
    let output = match Command::new("nm").args([path.to_str().unwrap()]).output() {
        Ok(output) => output,
        Err(err) if err.kind() == ErrorKind::NotFound => {
            skip_host_tool_test("nm is not installed");
            return None;
        }
        Err(err) => panic!("failed to run nm: {err}"),
    };

    if output.status.success() {
        return Some(String::from_utf8_lossy(&output.stdout).to_string());
    }

    if tool_lacks_macho_support(&output) {
        skip_host_tool_test("nm cannot inspect the generated Mach-O object");
        return None;
    }

    panic!("nm failed: {}", output_text(&output));
}

// =============================================================================
// Helper: compile a trust_ir module through the Compiler API
// =============================================================================

/// Build a minimal trust_ir module: `fn add(a: i32, b: i32) -> i32 { a + b }`
fn build_trust_ir_add_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I32, Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_add_two", ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::I32), // param a
            (ValueId::new(1), Ty::I32), // param b
        ],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

/// Build a trust_ir module: `fn const_42() -> i32 { 42 }`
fn build_trust_ir_const_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_const_42", ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(42),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

/// Build a trust_ir module: `fn sub_vals(a: i64, b: i64) -> i64 { a - b }`
fn build_trust_ir_sub_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_sub_vals", ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Sub,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

// =============================================================================
// Test 1: Compiler API produces non-empty Mach-O from trust_ir module
// =============================================================================

#[test]
fn e2e_aarch64_trust_ir_module_to_object_code() {
    let module = build_trust_ir_add_module();
    let compiler = macho_compiler(CompilerConfig {
        opt_level: OptLevel::O0,
        trace_level: CompilerTraceLevel::Full,
        ..CompilerConfig::default()
    });

    let result = compiler
        .compile(&module)
        .expect("compilation should succeed");

    // Object code must be non-empty
    assert!(
        !result.object_code.is_empty(),
        "Compiler::compile() must produce non-empty Mach-O bytes"
    );

    // Metrics should reflect one function
    assert_eq!(result.metrics.function_count, 1);
    assert!(result.metrics.code_size_bytes > 0);

    // Trace should be populated (we asked for Full)
    let trace = result
        .trace
        .expect("trace should be present with Full level");
    assert!(!trace.entries.is_empty());

    eprintln!(
        "trust_ir->object: {} bytes, {} instructions, trace entries: {}",
        result.metrics.code_size_bytes,
        result.metrics.instruction_count,
        trace.entries.len()
    );
}

// =============================================================================
// Test 2: Mach-O file has valid magic number and structure
// =============================================================================

#[test]
fn e2e_aarch64_macho_magic_number() {
    let module = build_trust_ir_add_module();
    let compiler = macho_compiler(CompilerConfig::default());
    let result = compiler
        .compile(&module)
        .expect("compilation should succeed");
    let obj = &result.object_code;

    // Mach-O 64-bit magic: 0xFEEDFACF
    assert!(obj.len() >= 4, "object too small for Mach-O header");
    let magic = u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]);
    assert_eq!(
        magic, 0xFEED_FACF,
        "expected Mach-O 64-bit magic 0xFEEDFACF, got {:#010X}",
        magic
    );

    // CPU type for ARM64: 0x0100000C (CPU_TYPE_ARM64)
    let cputype = u32::from_le_bytes([obj[4], obj[5], obj[6], obj[7]]);
    assert_eq!(
        cputype, 0x0100_000C,
        "expected CPU_TYPE_ARM64 (0x0100000C), got {:#010X}",
        cputype
    );
}

// =============================================================================
// Test 3: Object file disassembles with otool (validates encoding)
// =============================================================================

#[test]
fn e2e_aarch64_otool_disassembly() {
    let module = build_trust_ir_add_module();
    let compiler = macho_compiler(CompilerConfig::default());
    let result = compiler
        .compile(&module)
        .expect("compilation should succeed");

    let obj_path = write_temp_file("add_two", ".o", &result.object_code);

    let Some(stdout) = run_otool(&["-tv", obj_path.to_str().unwrap()]) else {
        return;
    };

    // Should contain the function symbol
    assert!(
        stdout.contains("__add_two") || stdout.contains("_add_two"),
        "otool output should contain the function symbol. Got:\n{}",
        stdout
    );

    // Should contain AArch64 instructions (add, ret are expected)
    let has_instructions =
        stdout.contains("add") || stdout.contains("ret") || stdout.contains("mov");
    assert!(
        has_instructions,
        "otool output should show AArch64 instructions. Got:\n{}",
        stdout
    );

    eprintln!("otool disassembly:\n{}", stdout);
}

// =============================================================================
// Test 4: Link and run -- the big one
//
// We compile add_two(i32, i32) -> i32 via Trust Codegen, write a C main() that calls
// it, link them together, and verify the output.
// =============================================================================

#[test]
fn e2e_aarch64_link_and_run() {
    if !can_link_and_run_aarch64_macho() {
        skip_host_tool_test("link-and-run requires an aarch64-apple-darwin host");
        return;
    }

    let module = build_trust_ir_add_module();
    let compiler = macho_compiler(CompilerConfig {
        opt_level: OptLevel::O0,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(&module)
        .expect("compilation should succeed");

    let test_dir = std::env::temp_dir().join("trust_cg_e2e_tests");
    fs::create_dir_all(&test_dir).expect("create temp dir");

    let obj_path = test_dir.join("add_two.o");
    fs::write(&obj_path, &result.object_code).expect("write object file");

    // Write a C driver that calls our compiled function
    let driver_path = test_dir.join("driver_add.c");
    let driver_src = r#"
#include <stdio.h>

// Declare the function compiled by Trust Codegen
// Mach-O symbol: __add_two (C sees it as _add_two without extra underscore)
extern int _add_two(int a, int b);

int main() {
    int result = _add_two(30, 12);
    printf("%d\n", result);
    return (result == 42) ? 0 : 1;
}
"#;
    fs::write(&driver_path, driver_src).expect("write driver source");

    let binary_path = test_dir.join("test_add");

    // Compile and link: cc driver.c add_two.o -o test_add
    let link_output = Command::new("cc")
        .args([
            driver_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-o",
            binary_path.to_str().unwrap(),
        ])
        .output()
        .expect("cc should be available");

    let link_stderr = String::from_utf8_lossy(&link_output.stderr);
    if !link_output.status.success() {
        // If linking fails, fall back to verifying the .o with otool
        eprintln!(
            "Linking failed (may be expected if ABI is off): {}",
            link_stderr
        );

        // Verify the object at least disassembles
        let otool_out = Command::new("otool")
            .args(["-tv", obj_path.to_str().unwrap()])
            .output()
            .expect("otool");
        let otool_stdout = String::from_utf8_lossy(&otool_out.stdout);
        assert!(
            otool_out.status.success(),
            "otool should at least work on the .o"
        );
        eprintln!("Object disassembly (link failed):\n{}", otool_stdout);

        // Also check symbols
        let nm_out = Command::new("nm")
            .args([obj_path.to_str().unwrap()])
            .output()
            .expect("nm");
        let nm_stdout = String::from_utf8_lossy(&nm_out.stdout);
        eprintln!("Symbols:\n{}", nm_stdout);

        panic!(
            "Linking failed. This means the Mach-O structure or ABI is wrong.\n\
             Linker stderr: {}\n\
             Fix the pipeline to produce a linkable object.",
            link_stderr
        );
    }

    eprintln!("Link succeeded: {}", binary_path.display());

    // Run the binary
    let run_output = Command::new(binary_path.to_str().unwrap())
        .output()
        .expect("should be able to run the binary");

    let run_stdout = String::from_utf8_lossy(&run_output.stdout);
    let run_stderr = String::from_utf8_lossy(&run_output.stderr);

    eprintln!("Binary stdout: {}", run_stdout.trim());
    eprintln!("Binary stderr: {}", run_stderr);
    eprintln!("Exit code: {:?}", run_output.status.code());

    assert!(
        run_output.status.success(),
        "Binary should exit 0 (add(30, 12) == 42). Got exit code {:?}\nstdout: {}\nstderr: {}",
        run_output.status.code(),
        run_stdout,
        run_stderr
    );

    assert_eq!(run_stdout.trim(), "42", "Binary should print 42 (30 + 12)");
}

// =============================================================================
// Test 5: build_add_test_function() IR path (bypasses trust_ir adapter + ISel)
// =============================================================================

#[test]
fn e2e_aarch64_ir_function_compile() {
    let mut ir_func = pipeline::build_add_test_function();
    let compiler = macho_compiler(CompilerConfig::default());
    let result = compiler
        .compile_ir_function(&mut ir_func)
        .expect("compile_ir_function should succeed");

    assert!(!result.object_code.is_empty());
    assert!(result.metrics.code_size_bytes > 0);
    assert_eq!(result.metrics.function_count, 1);

    // Verify Mach-O magic
    let obj = &result.object_code;
    let magic = u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]);
    assert_eq!(magic, 0xFEED_FACF, "should be valid Mach-O");

    eprintln!(
        "IR path: {} bytes, {} estimated instructions",
        result.metrics.code_size_bytes, result.metrics.instruction_count
    );
}

// =============================================================================
// Test 6: IR path link-and-run with the pre-built add function
// =============================================================================

#[test]
fn e2e_aarch64_ir_link_and_run() {
    if !can_link_and_run_aarch64_macho() {
        skip_host_tool_test("link-and-run requires an aarch64-apple-darwin host");
        return;
    }

    let mut ir_func = pipeline::build_add_test_function();
    let compiler = macho_compiler(CompilerConfig {
        opt_level: OptLevel::O0,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile_ir_function(&mut ir_func)
        .expect("compile_ir_function should succeed");

    let test_dir = std::env::temp_dir().join("trust_cg_e2e_tests");
    fs::create_dir_all(&test_dir).expect("create temp dir");

    let obj_path = test_dir.join("ir_add.o");
    fs::write(&obj_path, &result.object_code).expect("write object file");

    // The IR build_add_test_function creates a function named "add",
    // which becomes symbol "_add" in Mach-O
    let driver_path = test_dir.join("driver_ir_add.c");
    let driver_src = r#"
#include <stdio.h>

extern int add(int a, int b);

int main() {
    int result = add(17, 25);
    printf("%d\n", result);
    return (result == 42) ? 0 : 1;
}
"#;
    fs::write(&driver_path, driver_src).expect("write driver source");

    let binary_path = test_dir.join("test_ir_add");

    let link_output = Command::new("cc")
        .args([
            driver_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-o",
            binary_path.to_str().unwrap(),
        ])
        .output()
        .expect("cc");

    let link_stderr = String::from_utf8_lossy(&link_output.stderr);
    if !link_output.status.success() {
        eprintln!("IR path linking failed: {}", link_stderr);

        let otool_out = Command::new("otool")
            .args(["-tv", obj_path.to_str().unwrap()])
            .output()
            .expect("otool");
        eprintln!(
            "Disassembly:\n{}",
            String::from_utf8_lossy(&otool_out.stdout)
        );

        let nm_out = Command::new("nm")
            .args([obj_path.to_str().unwrap()])
            .output()
            .expect("nm");
        eprintln!("Symbols:\n{}", String::from_utf8_lossy(&nm_out.stdout));

        panic!("IR path linking failed: {}", link_stderr);
    }

    let run_output = Command::new(binary_path.to_str().unwrap())
        .output()
        .expect("run binary");

    let stdout = String::from_utf8_lossy(&run_output.stdout);
    eprintln!("IR path binary stdout: {}", stdout.trim());

    assert!(
        run_output.status.success(),
        "IR add(17, 25) should produce 42 and exit 0. Got {:?}\n{}",
        run_output.status.code(),
        stdout
    );
    assert_eq!(stdout.trim(), "42");
}

// =============================================================================
// Test 7: trust_ir constant function through full pipeline
// =============================================================================

#[test]
fn e2e_aarch64_trust_ir_const_to_object() {
    let module = build_trust_ir_const_module();
    let compiler = macho_compiler(CompilerConfig::default());
    let result = compiler
        .compile(&module)
        .expect("const compilation should succeed");

    assert!(!result.object_code.is_empty());
    assert_eq!(result.metrics.function_count, 1);

    // Verify valid Mach-O
    let obj = &result.object_code;
    let magic = u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]);
    assert_eq!(magic, 0xFEED_FACF);

    eprintln!(
        "trust_ir const->object: {} bytes",
        result.metrics.code_size_bytes
    );
}

// =============================================================================
// Test 8: trust_ir subtraction (i64) through full pipeline
// =============================================================================

#[test]
fn e2e_aarch64_trust_ir_sub_to_object() {
    let module = build_trust_ir_sub_module();
    let compiler = macho_compiler(CompilerConfig::default());
    let result = compiler
        .compile(&module)
        .expect("sub compilation should succeed");

    assert!(!result.object_code.is_empty());
    assert_eq!(result.metrics.function_count, 1);

    // Verify valid Mach-O
    let obj = &result.object_code;
    let magic = u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]);
    assert_eq!(magic, 0xFEED_FACF);

    eprintln!(
        "trust_ir sub->object: {} bytes",
        result.metrics.code_size_bytes
    );
}

// =============================================================================
// Test 9: All optimization levels produce valid output
// =============================================================================

#[test]
fn e2e_aarch64_all_opt_levels() {
    let module = build_trust_ir_add_module();

    for opt in &[OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let compiler = macho_compiler(CompilerConfig {
            opt_level: *opt,
            ..CompilerConfig::default()
        });
        let result = compiler
            .compile(&module)
            .unwrap_or_else(|e| panic!("compilation at {:?} failed: {}", opt, e));

        assert!(
            !result.object_code.is_empty(),
            "{:?} produced empty object code",
            opt
        );

        let obj = &result.object_code;
        let magic = u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]);
        assert_eq!(magic, 0xFEED_FACF, "{:?} produced invalid Mach-O", opt);

        eprintln!(
            "  {:?}: {} bytes, {} instructions",
            opt, result.metrics.code_size_bytes, result.metrics.instruction_count
        );
    }
}

// =============================================================================
// Test 10: nm shows expected symbol
// =============================================================================

#[test]
fn e2e_aarch64_nm_symbol_check() {
    let module = build_trust_ir_add_module();
    let compiler = macho_compiler(CompilerConfig::default());
    let result = compiler
        .compile(&module)
        .expect("compilation should succeed");

    let obj_path = write_temp_file("nm_test", ".o", &result.object_code);

    let Some(stdout) = run_macho_nm(&obj_path) else {
        return;
    };

    // The function should appear as an external text symbol
    // nm format: "<addr> T __add_two" (with Mach-O double underscore)
    assert!(
        stdout.contains("__add_two"),
        "nm should show __add_two symbol. Got:\n{}",
        stdout
    );

    eprintln!("nm output:\n{}", stdout);
}

// =============================================================================
// Multi-block trust_ir builders and E2E tests
//
// These tests exercise control flow (branches, loops) through the FULL pipeline:
//   trust_ir -> adapter -> ISel -> opt -> regalloc -> frame -> encode -> Mach-O -> link -> run
//
// Part of #242 -- Multi-block E2E tests for control flow
// =============================================================================

// ---------------------------------------------------------------------------
// Helpers for multi-block link-and-run tests
// ---------------------------------------------------------------------------

fn make_test_dir(test_name: &str) -> std::path::PathBuf {
    let dir = std::env::temp_dir().join(format!("trust_cg_e2e_multiblock_{}", test_name));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");
    dir
}

fn compile_trust_ir_module_to_obj(module: &TrustIrModule) -> Vec<u8> {
    let compiler = macho_compiler(CompilerConfig {
        opt_level: OptLevel::O0,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(module)
        .expect("compilation should succeed");
    assert!(
        !result.object_code.is_empty(),
        "compiled object code must be non-empty"
    );
    result.object_code
}

fn link_and_run(
    test_name: &str,
    func_name: &str,
    obj_bytes: &[u8],
    driver_src: &str,
) -> Option<(i32, String)> {
    if !can_link_and_run_aarch64_macho() {
        skip_host_tool_test("link-and-run requires an aarch64-apple-darwin host");
        return None;
    }

    let dir = make_test_dir(test_name);
    let obj_path = dir.join(format!("{}.o", func_name));
    fs::write(&obj_path, obj_bytes).expect("write .o file");

    let driver_path = dir.join("driver.c");
    fs::write(&driver_path, driver_src).expect("write driver.c");

    let binary_path = dir.join(format!("test_{}", func_name));

    let link_output = Command::new("cc")
        .args([
            driver_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-o",
            binary_path.to_str().unwrap(),
        ])
        .output()
        .expect("cc should be available");

    if !link_output.status.success() {
        let stderr = String::from_utf8_lossy(&link_output.stderr);
        // Debug: show otool and nm output
        let otool_out = Command::new("otool")
            .args(["-tv", obj_path.to_str().unwrap()])
            .output()
            .ok();
        let nm_out = Command::new("nm")
            .args([obj_path.to_str().unwrap()])
            .output()
            .ok();

        let disasm = otool_out
            .map(|o| String::from_utf8_lossy(&o.stdout).to_string())
            .unwrap_or_default();
        let symbols = nm_out
            .map(|o| String::from_utf8_lossy(&o.stdout).to_string())
            .unwrap_or_default();

        panic!(
            "Linking failed for {}!\nstderr: {}\notool:\n{}\nnm:\n{}",
            func_name, stderr, disasm, symbols
        );
    }

    let run_output = Command::new(binary_path.to_str().unwrap())
        .output()
        .expect("should be able to run the binary");

    let stdout = String::from_utf8_lossy(&run_output.stdout).to_string();
    let exit_code = run_output.status.code().unwrap_or(-1);

    let _ = fs::remove_dir_all(&dir);

    Some((exit_code, stdout))
}

// ---------------------------------------------------------------------------
// Builder: max(a, b) -- conditional branch (if-then-else diamond)
//
// fn max_val(a: i64, b: i64) -> i64 {
//     if a > b { a } else { b }
// }
//
// bb0 (entry): cmp a > b, condbr -> bb1 (return a), bb2 (return b)
// bb1: return a
// bb2: return b
// ---------------------------------------------------------------------------

fn build_trust_ir_max_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");

    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_max_val", ft_id, BlockId::new(0));
    func.blocks = vec![
        // bb0 (entry): compare and branch
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![
                (ValueId::new(0), Ty::I64), // a
                (ValueId::new(1), Ty::I64), // b
            ],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sgt,
                    ty: Ty::I64,
                    lhs: ValueId::new(0), // a
                    rhs: ValueId::new(1), // b
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(2),
                    then_target: BlockId::new(1), // a > b => return a
                    then_args: vec![],
                    else_target: BlockId::new(2), // else return b
                    else_args: vec![],
                }),
            ],
        },
        // bb1: return a
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            })],
        },
        // bb2: return b
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            })],
        },
    ];
    module.add_function(func);
    module
}

// ---------------------------------------------------------------------------
// Builder: abs(x) -- comparison + conditional negate
//
// fn abs_val(x: i64) -> i64 {
//     if x < 0 { 0 - x } else { x }
// }
//
// bb0 (entry): const 0, cmp x < 0, condbr -> bb1 (negate), bb2 (return x)
// bb1: neg = 0 - x, return neg
// bb2: return x
// ---------------------------------------------------------------------------

fn build_trust_ir_abs_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");

    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_abs_val", ft_id, BlockId::new(0));
    func.blocks = vec![
        // bb0 (entry): compare x < 0
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)], // x
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Slt,
                    ty: Ty::I64,
                    lhs: ValueId::new(0), // x
                    rhs: ValueId::new(1), // 0
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(2),
                    then_target: BlockId::new(1), // negate
                    then_args: vec![],
                    else_target: BlockId::new(2), // return x
                    else_args: vec![],
                }),
            ],
        },
        // bb1: negate -- return 0 - x
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Sub,
                    ty: Ty::I64,
                    lhs: ValueId::new(1), // 0 from bb0
                    rhs: ValueId::new(0), // x from bb0
                })
                .with_result(ValueId::new(3)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(3)],
                }),
            ],
        },
        // bb2: return x
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            })],
        },
    ];
    module.add_function(func);
    module
}

// ---------------------------------------------------------------------------
// Builder: fibonacci(n) -- loop with accumulator and block parameters
//
// fn fibonacci(n: i64) -> i64 {
//     if n <= 1 { return n }
//     a = 0; b = 1; i = 2
//     loop { tmp = a + b; a = b; b = tmp; i += 1; if i > n: return b }
// }
//
// bb0 (entry): const 1, cmp n <= 1, condbr -> bb1 (ret n), bb2 (loop_init)
// bb1: return n
// bb2: a=0, b=1, i=2, br -> bb3
// bb3 (loop): params(a, b, i)
//   tmp = a + b, new_i = i + 1, cmp new_i <= n
//   condbr -> bb3(b, tmp, new_i), bb4(tmp)
// bb4 (exit): params(result), return result
// ---------------------------------------------------------------------------

fn build_trust_ir_fibonacci_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");

    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_fibonacci", ft_id, BlockId::new(0));
    func.blocks = vec![
        // bb0 (entry): check n <= 1
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)], // n
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    lhs: ValueId::new(0), // n
                    rhs: ValueId::new(1), // 1
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(2),
                    then_target: BlockId::new(1), // ret_n
                    then_args: vec![],
                    else_target: BlockId::new(2), // loop_init
                    else_args: vec![],
                }),
            ],
        },
        // bb1 (ret_n): return n
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            })],
        },
        // bb2 (loop_init): a=0, b=1, i=2, jump to loop
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(10)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(11)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(2),
                })
                .with_result(ValueId::new(12)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(3),
                    args: vec![ValueId::new(10), ValueId::new(11), ValueId::new(12)],
                }),
            ],
        },
        // bb3 (loop body): params(a, b, i)
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![
                (ValueId::new(20), Ty::I64), // a
                (ValueId::new(21), Ty::I64), // b
                (ValueId::new(22), Ty::I64), // i
            ],
            body: vec![
                // tmp = a + b
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(20), // a
                    rhs: ValueId::new(21), // b
                })
                .with_result(ValueId::new(23)),
                // new_i = i + 1
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(24)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(22), // i
                    rhs: ValueId::new(24), // 1
                })
                .with_result(ValueId::new(25)),
                // cmp new_i <= n
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    lhs: ValueId::new(25), // new_i
                    rhs: ValueId::new(0),  // n (from entry)
                })
                .with_result(ValueId::new(26)),
                // condbr: loop back or exit
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(26),
                    then_target: BlockId::new(3), // loop (b, tmp, new_i)
                    then_args: vec![ValueId::new(21), ValueId::new(23), ValueId::new(25)],
                    else_target: BlockId::new(4), // exit (tmp)
                    else_args: vec![ValueId::new(23)],
                }),
            ],
        },
        // bb4 (exit): return result
        TrustIrBlock {
            id: BlockId::new(4),
            params: vec![(ValueId::new(30), Ty::I64)],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(30)],
            })],
        },
    ];
    module.add_function(func);
    module
}

// ---------------------------------------------------------------------------
// Builder: sum_1_to_n(n) -- simple counting loop
//
// fn sum_1_to_n(n: i64) -> i64 {
//     sum = 0; i = 1
//     while i <= n { sum += i; i += 1 }
//     return sum
// }
//
// bb0 (entry): sum=0, i=1, br -> bb1
// bb1 (loop header): params(sum, i), cmp i <= n, condbr -> bb2 (body), bb3 (exit)
// bb2 (body): new_sum = sum + i, new_i = i + 1, br -> bb1(new_sum, new_i)
// bb3 (exit): return sum
// ---------------------------------------------------------------------------

fn build_trust_ir_sum_1_to_n_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");

    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_sum_1_to_n", ft_id, BlockId::new(0));
    func.blocks = vec![
        // bb0 (entry): init sum=0, i=1, jump to loop
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)], // n
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(1),
                    args: vec![ValueId::new(1), ValueId::new(2)],
                }),
            ],
        },
        // bb1 (loop header): params(sum, i), check i <= n
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![
                (ValueId::new(10), Ty::I64), // sum
                (ValueId::new(11), Ty::I64), // i
            ],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    lhs: ValueId::new(11), // i
                    rhs: ValueId::new(0),  // n
                })
                .with_result(ValueId::new(12)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(12),
                    then_target: BlockId::new(2), // body
                    then_args: vec![],
                    else_target: BlockId::new(3), // exit
                    else_args: vec![],
                }),
            ],
        },
        // bb2 (body): sum += i, i += 1, back to loop
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(10), // sum
                    rhs: ValueId::new(11), // i
                })
                .with_result(ValueId::new(20)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(21)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(11), // i
                    rhs: ValueId::new(21), // 1
                })
                .with_result(ValueId::new(22)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(1),
                    args: vec![ValueId::new(20), ValueId::new(22)],
                }),
            ],
        },
        // bb3 (exit): return sum
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(10)], // sum from bb1
            })],
        },
    ];
    module.add_function(func);
    module
}

// =============================================================================
// Test 11: max(a, b) -- conditional branch, compile to valid Mach-O
// =============================================================================

#[test]
fn e2e_aarch64_max_val_compile() {
    let module = build_trust_ir_max_module();
    let compiler = macho_compiler(CompilerConfig {
        opt_level: OptLevel::O0,
        trace_level: CompilerTraceLevel::Full,
        ..CompilerConfig::default()
    });

    let result = compiler
        .compile(&module)
        .expect("max_val compilation should succeed");

    assert!(
        !result.object_code.is_empty(),
        "max_val must produce non-empty object code"
    );
    assert_eq!(result.metrics.function_count, 1);

    // Valid Mach-O magic
    let obj = &result.object_code;
    let magic = u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]);
    assert_eq!(magic, 0xFEED_FACF, "must be valid Mach-O");

    eprintln!(
        "max_val: {} bytes, {} instructions",
        result.metrics.code_size_bytes, result.metrics.instruction_count
    );
}

// =============================================================================
// Test 12: max(a, b) -- link and run (if-then-else diamond CFG)
// =============================================================================

#[test]
fn e2e_aarch64_max_val_link_and_run() {
    let module = build_trust_ir_max_module();
    let obj_bytes = compile_trust_ir_module_to_obj(&module);

    let driver = r#"
#include <stdio.h>

extern long _max_val(long a, long b);

int main(void) {
    long r1 = _max_val(10, 20);
    long r2 = _max_val(20, 10);
    long r3 = _max_val(5, 5);
    long r4 = _max_val(-3, -7);
    long r5 = _max_val(-1, 1);
    printf("max(10,20)=%ld max(20,10)=%ld max(5,5)=%ld max(-3,-7)=%ld max(-1,1)=%ld\n",
           r1, r2, r3, r4, r5);
    if (r1 != 20) return 1;
    if (r2 != 20) return 2;
    if (r3 != 5)  return 3;
    if (r4 != -3) return 4;
    if (r5 != 1)  return 5;
    return 0;
}
"#;

    let Some((exit_code, stdout)) = link_and_run("max_val", "max_val", &obj_bytes, driver) else {
        return;
    };
    eprintln!("max_val link+run stdout: {}", stdout.trim());
    assert_eq!(
        exit_code, 0,
        "max_val link+run failed (exit {}). \
         1=max(10,20)!=20, 2=max(20,10)!=20, 3=max(5,5)!=5, 4=max(-3,-7)!=-3, 5=max(-1,1)!=1. \
         stdout: {}",
        exit_code, stdout
    );
}

// =============================================================================
// Test 13: abs(x) -- comparison + conditional negate, compile to valid Mach-O
// =============================================================================

#[test]
fn e2e_aarch64_abs_val_compile() {
    let module = build_trust_ir_abs_module();
    let compiler = macho_compiler(CompilerConfig {
        opt_level: OptLevel::O0,
        ..CompilerConfig::default()
    });

    let result = compiler
        .compile(&module)
        .expect("abs_val compilation should succeed");

    assert!(!result.object_code.is_empty());
    assert_eq!(result.metrics.function_count, 1);

    let obj = &result.object_code;
    let magic = u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]);
    assert_eq!(magic, 0xFEED_FACF);

    eprintln!(
        "abs_val: {} bytes, {} instructions",
        result.metrics.code_size_bytes, result.metrics.instruction_count
    );
}

// =============================================================================
// Test 14: abs(x) -- link and run
// =============================================================================

#[test]
fn e2e_aarch64_abs_val_link_and_run() {
    let module = build_trust_ir_abs_module();
    let obj_bytes = compile_trust_ir_module_to_obj(&module);

    let driver = r#"
#include <stdio.h>

extern long _abs_val(long x);

int main(void) {
    long r1 = _abs_val(42);
    long r2 = _abs_val(-42);
    long r3 = _abs_val(0);
    long r4 = _abs_val(-1);
    long r5 = _abs_val(1);
    long r6 = _abs_val(-9999);
    printf("abs(42)=%ld abs(-42)=%ld abs(0)=%ld abs(-1)=%ld abs(1)=%ld abs(-9999)=%ld\n",
           r1, r2, r3, r4, r5, r6);
    if (r1 != 42)   return 1;
    if (r2 != 42)   return 2;
    if (r3 != 0)    return 3;
    if (r4 != 1)    return 4;
    if (r5 != 1)    return 5;
    if (r6 != 9999) return 6;
    return 0;
}
"#;

    let Some((exit_code, stdout)) = link_and_run("abs_val", "abs_val", &obj_bytes, driver) else {
        return;
    };
    eprintln!("abs_val link+run stdout: {}", stdout.trim());
    assert_eq!(
        exit_code, 0,
        "abs_val link+run failed (exit {}). \
         1=abs(42)!=42, 2=abs(-42)!=42, 3=abs(0)!=0, 4=abs(-1)!=1, 5=abs(1)!=1, 6=abs(-9999)!=9999. \
         stdout: {}",
        exit_code, stdout
    );
}

// =============================================================================
// Test 15: fibonacci(n) -- loop with accumulator, compile to valid Mach-O
// =============================================================================

#[test]
fn e2e_aarch64_fibonacci_compile() {
    let module = build_trust_ir_fibonacci_module();
    let compiler = macho_compiler(CompilerConfig {
        opt_level: OptLevel::O0,
        trace_level: CompilerTraceLevel::Full,
        ..CompilerConfig::default()
    });

    let result = compiler
        .compile(&module)
        .expect("fibonacci compilation should succeed");

    assert!(!result.object_code.is_empty());
    assert_eq!(result.metrics.function_count, 1);

    let obj = &result.object_code;
    let magic = u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]);
    assert_eq!(magic, 0xFEED_FACF);

    // Multi-block function should produce more code than simple single-block
    assert!(
        result.metrics.code_size_bytes > 50,
        "fibonacci (5 blocks, loop) should produce substantial code, got {} bytes",
        result.metrics.code_size_bytes
    );

    let trace = result.trace.expect("trace should be present");
    eprintln!(
        "fibonacci: {} bytes, {} instructions, {} trace entries",
        result.metrics.code_size_bytes,
        result.metrics.instruction_count,
        trace.entries.len()
    );
}

// =============================================================================
// Test 16: fibonacci(n) -- link and run
// =============================================================================

#[test]
fn e2e_aarch64_fibonacci_link_and_run() {
    let module = build_trust_ir_fibonacci_module();
    let obj_bytes = compile_trust_ir_module_to_obj(&module);

    // Fibonacci sequence: 0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55
    let driver = r#"
#include <stdio.h>

extern long _fibonacci(long n);

int main(void) {
    long r0 = _fibonacci(0);   /* 0 */
    long r1 = _fibonacci(1);   /* 1 */
    long r2 = _fibonacci(2);   /* 1 */
    long r5 = _fibonacci(5);   /* 5 */
    long r10 = _fibonacci(10); /* 55 */
    long r20 = _fibonacci(20); /* 6765 */
    printf("fib(0)=%ld fib(1)=%ld fib(2)=%ld fib(5)=%ld fib(10)=%ld fib(20)=%ld\n",
           r0, r1, r2, r5, r10, r20);
    if (r0 != 0)    return 1;
    if (r1 != 1)    return 2;
    if (r2 != 1)    return 3;
    if (r5 != 5)    return 4;
    if (r10 != 55)  return 5;
    if (r20 != 6765) return 6;
    return 0;
}
"#;

    let Some((exit_code, stdout)) = link_and_run("fibonacci", "fibonacci", &obj_bytes, driver)
    else {
        return;
    };
    eprintln!("fibonacci link+run stdout: {}", stdout.trim());
    assert_eq!(
        exit_code, 0,
        "fibonacci link+run failed (exit {}). \
         1=fib(0)!=0, 2=fib(1)!=1, 3=fib(2)!=1, 4=fib(5)!=5, 5=fib(10)!=55, 6=fib(20)!=6765. \
         stdout: {}",
        exit_code, stdout
    );
}

// =============================================================================
// Test 17: sum_1_to_n(n) -- simple counting loop, compile to valid Mach-O
// =============================================================================

#[test]
fn e2e_aarch64_sum_1_to_n_compile() {
    let module = build_trust_ir_sum_1_to_n_module();
    let compiler = macho_compiler(CompilerConfig {
        opt_level: OptLevel::O0,
        ..CompilerConfig::default()
    });

    let result = compiler
        .compile(&module)
        .expect("sum_1_to_n compilation should succeed");

    assert!(!result.object_code.is_empty());
    assert_eq!(result.metrics.function_count, 1);

    let obj = &result.object_code;
    let magic = u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]);
    assert_eq!(magic, 0xFEED_FACF);

    eprintln!(
        "sum_1_to_n: {} bytes, {} instructions",
        result.metrics.code_size_bytes, result.metrics.instruction_count
    );
}

// =============================================================================
// Test 18: sum_1_to_n(n) -- link and run
// =============================================================================

#[test]
fn e2e_aarch64_sum_1_to_n_link_and_run() {
    let module = build_trust_ir_sum_1_to_n_module();
    let obj_bytes = compile_trust_ir_module_to_obj(&module);

    // sum(1..=n) = n*(n+1)/2
    let driver = r#"
#include <stdio.h>

extern long _sum_1_to_n(long n);

int main(void) {
    long r0  = _sum_1_to_n(0);    /* 0 */
    long r1  = _sum_1_to_n(1);    /* 1 */
    long r5  = _sum_1_to_n(5);    /* 15 */
    long r10 = _sum_1_to_n(10);   /* 55 */
    long r100 = _sum_1_to_n(100); /* 5050 */
    printf("sum(0)=%ld sum(1)=%ld sum(5)=%ld sum(10)=%ld sum(100)=%ld\n",
           r0, r1, r5, r10, r100);
    if (r0 != 0)     return 1;
    if (r1 != 1)     return 2;
    if (r5 != 15)    return 3;
    if (r10 != 55)   return 4;
    if (r100 != 5050) return 5;
    return 0;
}
"#;

    let Some((exit_code, stdout)) = link_and_run("sum_1_to_n", "sum_1_to_n", &obj_bytes, driver)
    else {
        return;
    };
    eprintln!("sum_1_to_n link+run stdout: {}", stdout.trim());
    assert_eq!(
        exit_code, 0,
        "sum_1_to_n link+run failed (exit {}). \
         1=sum(0)!=0, 2=sum(1)!=1, 3=sum(5)!=15, 4=sum(10)!=55, 5=sum(100)!=5050. \
         stdout: {}",
        exit_code, stdout
    );
}

// =============================================================================
// Test 19: multi-block functions at multiple optimization levels
// =============================================================================

#[test]
fn e2e_aarch64_multiblock_all_opt_levels() {
    // Verify that multi-block functions compile at all opt levels
    let modules: &[(&str, TrustIrModule)] = &[
        ("max_val", build_trust_ir_max_module()),
        ("abs_val", build_trust_ir_abs_module()),
        ("fibonacci", build_trust_ir_fibonacci_module()),
        ("sum_1_to_n", build_trust_ir_sum_1_to_n_module()),
    ];

    for (name, module) in modules {
        for opt in &[OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let compiler = macho_compiler(CompilerConfig {
                opt_level: *opt,
                ..CompilerConfig::default()
            });
            let result = compiler
                .compile(module)
                .unwrap_or_else(|e| panic!("{} at {:?} failed: {}", name, opt, e));

            assert!(
                !result.object_code.is_empty(),
                "{} at {:?} produced empty object code",
                name,
                opt
            );

            let obj = &result.object_code;
            let magic = u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]);
            assert_eq!(
                magic, 0xFEED_FACF,
                "{} at {:?} produced invalid Mach-O",
                name, opt
            );

            eprintln!(
                "  {} {:?}: {} bytes",
                name, opt, result.metrics.code_size_bytes
            );
        }
    }
}

// =============================================================================
// Cross-function call tests (BRANCH26 relocation)
//
// Part of #241 -- BL relocation for cross-function calls
// =============================================================================

// ---------------------------------------------------------------------------
// Builder: two functions where caller BLs to callee
//
// fn _callee(x: i32) -> i32 { x + 10 }
// fn _caller(x: i32) -> i32 { _callee(x) }
//
// The key: _caller uses a BL instruction with a Symbol operand targeting
// _callee. When compiled into one .o via compile_module(), this BL must
// get an ARM64_RELOC_BRANCH26 relocation so the linker patches the offset.
// ---------------------------------------------------------------------------

fn build_trust_ir_cross_call_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");

    // fn _callee(x: i32) -> i32 { x + 10 }
    let ft_id_1 = module.add_func_type(FuncTy {
        params: vec![Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut callee = TrustIrFunction::new(FuncId::new(0), "_callee", ft_id_1, BlockId::new(0));
    callee.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I32)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(10),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];

    // fn _caller(x: i32) -> i32 { _callee(x) }
    let ft_id_2 = module.add_func_type(FuncTy {
        params: vec![Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut caller = TrustIrFunction::new(FuncId::new(1), "_caller", ft_id_2, BlockId::new(0));
    caller.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I32)],
        body: vec![
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0), // calls _callee
                args: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];

    module.add_function(callee);
    module.add_function(caller);
    module
}

// =============================================================================
// Test 20: Cross-function call -- compile to valid Mach-O with both symbols
// =============================================================================

#[test]
fn e2e_aarch64_cross_call_compile() {
    let module = build_trust_ir_cross_call_module();
    let compiler = macho_compiler(CompilerConfig {
        opt_level: OptLevel::O0,
        trace_level: CompilerTraceLevel::Full,
        ..CompilerConfig::default()
    });

    let result = compiler
        .compile(&module)
        .expect("cross-call compilation should succeed");

    assert!(
        !result.object_code.is_empty(),
        "cross-call must produce non-empty object code"
    );
    // Module has 2 functions
    assert_eq!(result.metrics.function_count, 2);

    // Valid Mach-O magic
    let obj = &result.object_code;
    let magic = u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]);
    assert_eq!(magic, 0xFEED_FACF, "must be valid Mach-O");

    // Write to temp and verify both symbols are present via nm
    let obj_path = write_temp_file("cross_call", ".o", obj);
    let Some(nm_stdout) = run_macho_nm(&obj_path) else {
        return;
    };

    assert!(
        nm_stdout.contains("__callee"),
        "nm should show __callee symbol. Got:\n{}",
        nm_stdout
    );
    assert!(
        nm_stdout.contains("__caller"),
        "nm should show __caller symbol. Got:\n{}",
        nm_stdout
    );

    // Verify relocations via otool -r (should show BRANCH26)
    let Some(reloc_stdout) = run_otool(&["-r", obj_path.to_str().unwrap()]) else {
        return;
    };

    eprintln!("nm output:\n{}", nm_stdout);
    eprintln!("otool -r output:\n{}", reloc_stdout);
    eprintln!(
        "cross-call: {} bytes, {} functions",
        result.metrics.code_size_bytes, result.metrics.function_count
    );

    // The relocation output should contain a BRANCH26 entry for the BL.
    // otool -r shows ARM64_RELOC_BRANCH26 as type value "2" in numeric output.
    // Check for both the symbolic name and the numeric type.
    let has_branch26_reloc = reloc_stdout.contains("ARM64_RELOC_BRANCH26")
        || reloc_stdout.contains("BRANCH26")
        // otool -r numeric format: columns are
        //   address pcrel length extern type scattered symbolnum
        // For BRANCH26: pcrel=1, length=2, extern=1, type=2
        || (reloc_stdout.contains("Relocation information")
            && reloc_stdout.contains("1     2      1      2"));
    assert!(
        has_branch26_reloc,
        "otool -r should show ARM64_RELOC_BRANCH26 (type 2) for the cross-function BL. Got:\n{}",
        reloc_stdout
    );
}

// =============================================================================
// Test 21: Cross-function call -- link and run
//
// fn _callee(x: i32) -> i32 { x + 10 }
// fn _caller(x: i32) -> i32 { _callee(x) }
//
// C driver calls _caller(32), expects 42 (32 + 10).
// =============================================================================

#[test]
fn e2e_aarch64_cross_call_link_and_run() {
    let module = build_trust_ir_cross_call_module();
    let obj_bytes = compile_trust_ir_module_to_obj(&module);

    let driver = r#"
#include <stdio.h>

extern int _caller(int x);

int main(void) {
    int r1 = _caller(32);
    int r2 = _caller(0);
    int r3 = _caller(-10);
    printf("caller(32)=%d caller(0)=%d caller(-10)=%d\n", r1, r2, r3);
    if (r1 != 42) return 1;
    if (r2 != 10) return 2;
    if (r3 != 0) return 3;
    return 0;
}
"#;

    let Some((exit_code, stdout)) = link_and_run("cross_call", "cross_call", &obj_bytes, driver)
    else {
        return;
    };
    eprintln!("cross_call link+run stdout: {}", stdout.trim());
    assert_eq!(
        exit_code, 0,
        "cross_call link+run failed (exit {}). \
         1=caller(32)!=42, 2=caller(0)!=10, 3=caller(-10)!=0. \
         stdout: {}",
        exit_code, stdout
    );
}

// ---------------------------------------------------------------------------
// Builder: TY-shaped record build + cross-call through a pointer
//
// fn _tla_record_sum2(ptr: *const i64) -> i64 {
//     return ptr[0] + ptr[1];
// }
//
// fn _tla_record_build_then_sum2(a, b, c, d: i64) -> i64 {
//     count_slot = alloca i64
//     *count_slot = 4
//     count = *count_slot
//     record = alloca i64, count  // bounded dynamic-count path (#520)
//     record[0] = a; record[1] = b; record[2] = c; record[3] = d;
//     return _tla_record_sum2(record);
// }
//
// This is the smallest honest #519 TY slice:
// - multi-function module
// - aggregate-shaped temporary
// - direct inter-function call by symbol
// - exercises the bounded dynamic-count alloca escape hatch landed in #520
// ---------------------------------------------------------------------------

fn build_trust_ir_tla_record_cross_call_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");

    let sum_ft = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut callee =
        TrustIrFunction::new(FuncId::new(0), "_tla_record_sum2", sum_ft, BlockId::new(0));
    callee.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: ValueId::new(0),
                indices: vec![ValueId::new(1)],
                inbounds: false,
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(3),
                align: None,
                volatile: false,
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: ValueId::new(0),
                indices: vec![ValueId::new(2)],
                inbounds: false,
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(5),
                align: None,
                volatile: false,
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(4),
                rhs: ValueId::new(6),
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(7)],
            }),
        ],
    }];

    let build_ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64, Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut caller = TrustIrFunction::new(
        FuncId::new(1),
        "_tla_record_build_then_sum2",
        build_ft,
        BlockId::new(0),
    );
    caller.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::I64),
            (ValueId::new(1), Ty::I64),
            (ValueId::new(2), Ty::I64),
            (ValueId::new(3), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            })
            .with_result(ValueId::new(10)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(4),
            })
            .with_result(ValueId::new(11)),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: ValueId::new(10),
                value: ValueId::new(11),
                align: None,
                volatile: false,
            }),
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(10),
                align: None,
                volatile: false,
            })
            .with_result(ValueId::new(12)),
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: Some(ValueId::new(12)),
                align: None,
            })
            .with_result(ValueId::new(20)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(30)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(31)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(2),
            })
            .with_result(ValueId::new(32)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(3),
            })
            .with_result(ValueId::new(33)),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: ValueId::new(20),
                indices: vec![ValueId::new(30)],
                inbounds: false,
            })
            .with_result(ValueId::new(40)),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: ValueId::new(40),
                value: ValueId::new(0),
                align: None,
                volatile: false,
            }),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: ValueId::new(20),
                indices: vec![ValueId::new(31)],
                inbounds: false,
            })
            .with_result(ValueId::new(41)),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: ValueId::new(41),
                value: ValueId::new(1),
                align: None,
                volatile: false,
            }),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: ValueId::new(20),
                indices: vec![ValueId::new(32)],
                inbounds: false,
            })
            .with_result(ValueId::new(42)),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: ValueId::new(42),
                value: ValueId::new(2),
                align: None,
                volatile: false,
            }),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: ValueId::new(20),
                indices: vec![ValueId::new(33)],
                inbounds: false,
            })
            .with_result(ValueId::new(43)),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: ValueId::new(43),
                value: ValueId::new(3),
                align: None,
                volatile: false,
            }),
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![ValueId::new(20)],
            })
            .with_result(ValueId::new(50)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(50)],
            }),
        ],
    }];

    module.add_function(callee);
    module.add_function(caller);
    module
}

// =============================================================================
// Test 22: TY-shaped aggregate cross-call -- compile to valid Mach-O
// =============================================================================

#[test]
fn e2e_aarch64_tla_record_cross_call_compile() {
    let module = build_trust_ir_tla_record_cross_call_module();
    let compiler = macho_compiler(CompilerConfig {
        opt_level: OptLevel::O0,
        trace_level: CompilerTraceLevel::Full,
        ..CompilerConfig::default()
    });

    let result = compiler
        .compile(&module)
        .expect("tla record cross-call compilation should succeed");

    assert!(
        !result.object_code.is_empty(),
        "tla record cross-call must produce non-empty object code"
    );
    assert_eq!(result.metrics.function_count, 2);

    let obj = &result.object_code;
    let magic = u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]);
    assert_eq!(magic, 0xFEED_FACF, "must be valid Mach-O");

    let obj_path = write_temp_file("tla_record_cross_call", ".o", obj);
    let Some(nm_stdout) = run_macho_nm(&obj_path) else {
        return;
    };

    assert!(
        nm_stdout.contains("__tla_record_sum2"),
        "nm should show __tla_record_sum2 symbol. Got:\n{}",
        nm_stdout
    );
    assert!(
        nm_stdout.contains("__tla_record_build_then_sum2"),
        "nm should show __tla_record_build_then_sum2 symbol. Got:\n{}",
        nm_stdout
    );

    let Some(reloc_stdout) = run_otool(&["-r", obj_path.to_str().unwrap()]) else {
        return;
    };

    let has_branch26_reloc = reloc_stdout.contains("ARM64_RELOC_BRANCH26")
        || reloc_stdout.contains("BRANCH26")
        || (reloc_stdout.contains("Relocation information")
            && reloc_stdout.contains("1     2      1      2"));
    assert!(
        has_branch26_reloc,
        "otool -r should show ARM64_RELOC_BRANCH26 (type 2) for the record cross-call BL. Got:\n{}",
        reloc_stdout
    );
}

// =============================================================================
// Test 23: TY-shaped aggregate cross-call -- link and run
// =============================================================================

#[test]
fn e2e_aarch64_tla_record_cross_call_link_and_run() {
    let module = build_trust_ir_tla_record_cross_call_module();
    let obj_bytes = compile_trust_ir_module_to_obj(&module);

    let driver = r#"
#include <stdio.h>

extern long long _tla_record_build_then_sum2(long long a, long long b, long long c, long long d);

int main(void) {
    long long r1 = _tla_record_build_then_sum2(1, 2, 100, 200);
    long long r2 = _tla_record_build_then_sum2(40, 2, 7, 9);
    long long r3 = _tla_record_build_then_sum2(-5, 5, 0, 1);
    printf("record_sum2(1,2,100,200)=%lld record_sum2(40,2,7,9)=%lld record_sum2(-5,5,0,1)=%lld\n", r1, r2, r3);
    if (r1 != 3) return 1;
    if (r2 != 42) return 2;
    if (r3 != 0) return 3;
    return 0;
}
"#;

    let Some((exit_code, stdout)) = link_and_run(
        "tla_record_cross_call",
        "tla_record_cross_call",
        &obj_bytes,
        driver,
    ) else {
        return;
    };
    eprintln!("tla_record_cross_call link+run stdout: {}", stdout.trim());
    assert_eq!(
        exit_code, 0,
        "tla_record_cross_call link+run failed (exit {}). \
         1=first case failed, 2=second case failed, 3=third case failed. \
         stdout: {}",
        exit_code, stdout
    );
}

// =============================================================================
// Multi-block E2E tests adapted to the Operand model
//
// Part of #242 -- if/else, loop, nested conditional, factorial
// =============================================================================

// ---------------------------------------------------------------------------
// Builder: classify(x) -- 3-way if/else (sign classification)
//
// fn classify(x: i64) -> i64 {
//     if x < 0 { return -1 }
//     if x == 0 { return 0 }
//     return 1
// }
//
// bb0 (entry): cmp x < 0, condbr -> bb1 (neg), bb2 (check_zero)
// bb1 (neg): return -1
// bb2 (check_zero): cmp x == 0, condbr -> bb3 (zero), bb4 (pos)
// bb3 (zero): return 0
// bb4 (pos): return 1
// ---------------------------------------------------------------------------

fn build_trust_ir_classify_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");

    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_classify", ft_id, BlockId::new(0));
    func.blocks = vec![
        // bb0 (entry): check x < 0
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)], // x
            body: vec![
                // const 0 for comparison
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(1)),
                // cmp x < 0
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Slt,
                    ty: Ty::I64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2)),
                // if x < 0 -> bb1 (neg), else -> bb2 (check_zero)
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(2),
                    then_target: BlockId::new(1),
                    then_args: vec![],
                    else_target: BlockId::new(2),
                    else_args: vec![],
                }),
            ],
        },
        // bb1 (neg): return -1
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(-1),
                })
                .with_result(ValueId::new(10)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(10)],
                }),
            ],
        },
        // bb2 (check_zero): cmp x == 0
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::I64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1), // zero from bb0
                })
                .with_result(ValueId::new(20)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(20),
                    then_target: BlockId::new(3), // zero
                    then_args: vec![],
                    else_target: BlockId::new(4), // pos
                    else_args: vec![],
                }),
            ],
        },
        // bb3 (zero): return 0
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)], // reuse zero from bb0
            })],
        },
        // bb4 (pos): return 1
        TrustIrBlock {
            id: BlockId::new(4),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(30)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(30)],
                }),
            ],
        },
    ];
    module.add_function(func);
    module
}

// ---------------------------------------------------------------------------
// Builder: sum_to_n(n) -- loop with accumulator
//
// fn sum_to_n(n: i64) -> i64 {
//     let mut acc = 0;
//     let mut i = 1;
//     while i <= n { acc += i; i += 1; }
//     return acc;
// }
//
// bb0 (entry): acc=0, i=1, br -> bb1
// bb1 (loop header): params(acc, i), cmp i <= n, condbr -> bb2 (body), bb3 (exit)
// bb2 (body): new_acc = acc + i, new_i = i + 1, br -> bb1(new_acc, new_i)
// bb3 (exit): return acc
// ---------------------------------------------------------------------------

fn build_trust_ir_sum_to_n_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");

    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_sum_to_n", ft_id, BlockId::new(0));
    func.blocks = vec![
        // bb0 (entry): acc=0, i=1, jump to loop
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)], // n
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(1),
                    args: vec![ValueId::new(1), ValueId::new(2)],
                }),
            ],
        },
        // bb1 (loop header): params(acc, i), check i <= n
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![
                (ValueId::new(10), Ty::I64), // acc
                (ValueId::new(11), Ty::I64), // i
            ],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    lhs: ValueId::new(11), // i
                    rhs: ValueId::new(0),  // n
                })
                .with_result(ValueId::new(12)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(12),
                    then_target: BlockId::new(2), // body
                    then_args: vec![],
                    else_target: BlockId::new(3), // exit
                    else_args: vec![],
                }),
            ],
        },
        // bb2 (body): acc += i, i += 1, back to loop header
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                // new_acc = acc + i
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(10), // acc
                    rhs: ValueId::new(11), // i
                })
                .with_result(ValueId::new(20)),
                // new_i = i + 1
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(21)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(11), // i
                    rhs: ValueId::new(21), // 1
                })
                .with_result(ValueId::new(22)),
                // br -> bb1(new_acc, new_i)
                InstrNode::new(Inst::Br {
                    target: BlockId::new(1),
                    args: vec![ValueId::new(20), ValueId::new(22)],
                }),
            ],
        },
        // bb3 (exit): return acc
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(10)], // acc from bb1
            })],
        },
    ];
    module.add_function(func);
    module
}

// ---------------------------------------------------------------------------
// Builder: clamp(x, lo, hi) -- nested conditional (5+ blocks)
//
// fn clamp(x: i64, lo: i64, hi: i64) -> i64 {
//     if x < lo { return lo }
//     if x > hi { return hi }
//     return x
// }
//
// bb0 (entry): cmp x < lo, condbr -> bb1 (ret_lo), bb2 (check_hi)
// bb1 (ret_lo): return lo
// bb2 (check_hi): cmp x > hi, condbr -> bb3 (ret_hi), bb4 (ret_x)
// bb3 (ret_hi): return hi
// bb4 (ret_x): return x
// ---------------------------------------------------------------------------

fn build_trust_ir_clamp_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");

    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_clamp", ft_id, BlockId::new(0));
    func.blocks = vec![
        // bb0 (entry): cmp x < lo
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![
                (ValueId::new(0), Ty::I64), // x
                (ValueId::new(1), Ty::I64), // lo
                (ValueId::new(2), Ty::I64), // hi
            ],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Slt,
                    ty: Ty::I64,
                    lhs: ValueId::new(0), // x
                    rhs: ValueId::new(1), // lo
                })
                .with_result(ValueId::new(3)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(3),
                    then_target: BlockId::new(1), // ret_lo
                    then_args: vec![],
                    else_target: BlockId::new(2), // check_hi
                    else_args: vec![],
                }),
            ],
        },
        // bb1 (ret_lo): return lo
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)], // lo
            })],
        },
        // bb2 (check_hi): cmp x > hi
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sgt,
                    ty: Ty::I64,
                    lhs: ValueId::new(0), // x
                    rhs: ValueId::new(2), // hi
                })
                .with_result(ValueId::new(10)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(10),
                    then_target: BlockId::new(3), // ret_hi
                    then_args: vec![],
                    else_target: BlockId::new(4), // ret_x
                    else_args: vec![],
                }),
            ],
        },
        // bb3 (ret_hi): return hi
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)], // hi
            })],
        },
        // bb4 (ret_x): return x
        TrustIrBlock {
            id: BlockId::new(4),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)], // x
            })],
        },
    ];
    module.add_function(func);
    module
}

// ---------------------------------------------------------------------------
// Builder: factorial(n) -- loop with multiply
//
// fn factorial(n: i64) -> i64 {
//     if n <= 1 { return 1 }
//     let mut acc = 1;
//     let mut i = 2;
//     while i <= n { acc *= i; i += 1; }
//     return acc;
// }
//
// bb0 (entry): cmp n <= 1, condbr -> bb1 (ret_1), bb2 (loop_init)
// bb1 (ret_1): return 1
// bb2 (loop_init): acc=1, i=2, br -> bb3
// bb3 (loop): params(acc, i), cmp i <= n, condbr -> bb4 (body), bb5 (exit)
// bb4 (body): new_acc = acc * i, new_i = i + 1, br -> bb3(new_acc, new_i)
// bb5 (exit): return acc
// ---------------------------------------------------------------------------

fn build_trust_ir_factorial_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");

    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_factorial", ft_id, BlockId::new(0));
    func.blocks = vec![
        // bb0 (entry): check n <= 1
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)], // n
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    lhs: ValueId::new(0), // n
                    rhs: ValueId::new(1), // 1
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(2),
                    then_target: BlockId::new(1), // ret_1
                    then_args: vec![],
                    else_target: BlockId::new(2), // loop_init
                    else_args: vec![],
                }),
            ],
        },
        // bb1 (ret_1): return 1
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)], // const_1 from bb0
            })],
        },
        // bb2 (loop_init): acc=1, i=2, jump to loop
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(10)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(2),
                })
                .with_result(ValueId::new(11)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(3),
                    args: vec![ValueId::new(10), ValueId::new(11)],
                }),
            ],
        },
        // bb3 (loop header): params(acc, i), check i <= n
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![
                (ValueId::new(20), Ty::I64), // acc
                (ValueId::new(21), Ty::I64), // i
            ],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    lhs: ValueId::new(21), // i
                    rhs: ValueId::new(0),  // n
                })
                .with_result(ValueId::new(22)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(22),
                    then_target: BlockId::new(4), // body
                    then_args: vec![],
                    else_target: BlockId::new(5), // exit
                    else_args: vec![],
                }),
            ],
        },
        // bb4 (body): acc *= i, i += 1, back to loop header
        TrustIrBlock {
            id: BlockId::new(4),
            params: vec![],
            body: vec![
                // new_acc = acc * i
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Mul,
                    ty: Ty::I64,
                    lhs: ValueId::new(20), // acc
                    rhs: ValueId::new(21), // i
                })
                .with_result(ValueId::new(30)),
                // new_i = i + 1
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(31)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(21), // i
                    rhs: ValueId::new(31), // 1
                })
                .with_result(ValueId::new(32)),
                // br -> bb3(new_acc, new_i)
                InstrNode::new(Inst::Br {
                    target: BlockId::new(3),
                    args: vec![ValueId::new(30), ValueId::new(32)],
                }),
            ],
        },
        // bb5 (exit): return acc
        TrustIrBlock {
            id: BlockId::new(5),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(20)], // acc from bb3
            })],
        },
    ];
    module.add_function(func);
    module
}

// =============================================================================
// Test 22: classify(x) -- if/else 3-way branch, compile to valid Mach-O
// =============================================================================

#[test]
fn e2e_aarch64_classify_compile() {
    let module = build_trust_ir_classify_module();
    let compiler = macho_compiler(CompilerConfig {
        opt_level: OptLevel::O0,
        trace_level: CompilerTraceLevel::Full,
        ..CompilerConfig::default()
    });

    let result = compiler
        .compile(&module)
        .expect("classify compilation should succeed");

    assert!(
        !result.object_code.is_empty(),
        "classify must produce non-empty object code"
    );
    assert_eq!(result.metrics.function_count, 1);

    let obj = &result.object_code;
    let magic = u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]);
    assert_eq!(magic, 0xFEED_FACF, "must be valid Mach-O");

    eprintln!(
        "classify: {} bytes, {} instructions",
        result.metrics.code_size_bytes, result.metrics.instruction_count
    );
}

// =============================================================================
// Test 23: classify(x) -- link and run
// =============================================================================

#[test]
fn e2e_aarch64_classify_link_and_run() {
    let module = build_trust_ir_classify_module();
    let obj_bytes = compile_trust_ir_module_to_obj(&module);

    let driver = r#"
#include <stdio.h>

extern long _classify(long x);

int main(void) {
    long r1 = _classify(-100);
    long r2 = _classify(-1);
    long r3 = _classify(0);
    long r4 = _classify(1);
    long r5 = _classify(999);
    printf("classify(-100)=%ld classify(-1)=%ld classify(0)=%ld classify(1)=%ld classify(999)=%ld\n",
           r1, r2, r3, r4, r5);
    if (r1 != -1) return 1;
    if (r2 != -1) return 2;
    if (r3 != 0)  return 3;
    if (r4 != 1)  return 4;
    if (r5 != 1)  return 5;
    return 0;
}
"#;

    let Some((exit_code, stdout)) = link_and_run("classify", "classify", &obj_bytes, driver) else {
        return;
    };
    eprintln!("classify link+run stdout: {}", stdout.trim());
    assert_eq!(
        exit_code, 0,
        "classify link+run failed (exit {}). \
         1=classify(-100)!=-1, 2=classify(-1)!=-1, 3=classify(0)!=0, \
         4=classify(1)!=1, 5=classify(999)!=1. stdout: {}",
        exit_code, stdout
    );
}

// =============================================================================
// Test 24: sum_to_n(n) -- loop with accumulator, compile to valid Mach-O
// =============================================================================

#[test]
fn e2e_aarch64_sum_to_n_compile() {
    let module = build_trust_ir_sum_to_n_module();
    let compiler = macho_compiler(CompilerConfig {
        opt_level: OptLevel::O0,
        ..CompilerConfig::default()
    });

    let result = compiler
        .compile(&module)
        .expect("sum_to_n compilation should succeed");

    assert!(!result.object_code.is_empty());
    assert_eq!(result.metrics.function_count, 1);

    let obj = &result.object_code;
    let magic = u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]);
    assert_eq!(magic, 0xFEED_FACF);

    eprintln!(
        "sum_to_n: {} bytes, {} instructions",
        result.metrics.code_size_bytes, result.metrics.instruction_count
    );
}

// =============================================================================
// Test 25: sum_to_n(n) -- link and run
// =============================================================================

#[test]
fn e2e_aarch64_sum_to_n_link_and_run() {
    let module = build_trust_ir_sum_to_n_module();
    let obj_bytes = compile_trust_ir_module_to_obj(&module);

    // sum(1..=n) = n*(n+1)/2
    let driver = r#"
#include <stdio.h>

extern long _sum_to_n(long n);

int main(void) {
    long r0  = _sum_to_n(0);    /* 0 */
    long r1  = _sum_to_n(1);    /* 1 */
    long r5  = _sum_to_n(5);    /* 15 */
    long r10 = _sum_to_n(10);   /* 55 */
    long r100 = _sum_to_n(100); /* 5050 */
    printf("sum(0)=%ld sum(1)=%ld sum(5)=%ld sum(10)=%ld sum(100)=%ld\n",
           r0, r1, r5, r10, r100);
    if (r0 != 0)     return 1;
    if (r1 != 1)     return 2;
    if (r5 != 15)    return 3;
    if (r10 != 55)   return 4;
    if (r100 != 5050) return 5;
    return 0;
}
"#;

    let Some((exit_code, stdout)) = link_and_run("sum_to_n", "sum_to_n", &obj_bytes, driver) else {
        return;
    };
    eprintln!("sum_to_n link+run stdout: {}", stdout.trim());
    assert_eq!(
        exit_code, 0,
        "sum_to_n link+run failed (exit {}). \
         1=sum(0)!=0, 2=sum(1)!=1, 3=sum(5)!=15, 4=sum(10)!=55, 5=sum(100)!=5050. \
         stdout: {}",
        exit_code, stdout
    );
}

// =============================================================================
// Test 26: clamp(x, lo, hi) -- nested conditional (5 blocks), compile
// =============================================================================

#[test]
fn e2e_aarch64_clamp_compile() {
    let module = build_trust_ir_clamp_module();
    let compiler = macho_compiler(CompilerConfig {
        opt_level: OptLevel::O0,
        trace_level: CompilerTraceLevel::Full,
        ..CompilerConfig::default()
    });

    let result = compiler
        .compile(&module)
        .expect("clamp compilation should succeed");

    assert!(
        !result.object_code.is_empty(),
        "clamp must produce non-empty object code"
    );
    assert_eq!(result.metrics.function_count, 1);

    let obj = &result.object_code;
    let magic = u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]);
    assert_eq!(magic, 0xFEED_FACF, "must be valid Mach-O");

    eprintln!(
        "clamp: {} bytes, {} instructions",
        result.metrics.code_size_bytes, result.metrics.instruction_count
    );
}

// =============================================================================
// Test 27: clamp(x, lo, hi) -- link and run
// =============================================================================

#[test]
fn e2e_aarch64_clamp_link_and_run() {
    let module = build_trust_ir_clamp_module();
    let obj_bytes = compile_trust_ir_module_to_obj(&module);

    let driver = r#"
#include <stdio.h>

extern long _clamp(long x, long lo, long hi);

int main(void) {
    long r1 = _clamp(5, 0, 10);     /* 5 (in range) */
    long r2 = _clamp(-5, 0, 10);    /* 0 (below lo) */
    long r3 = _clamp(15, 0, 10);    /* 10 (above hi) */
    long r4 = _clamp(0, 0, 10);     /* 0 (at lo boundary) */
    long r5 = _clamp(10, 0, 10);    /* 10 (at hi boundary) */
    long r6 = _clamp(-100, -50, 50); /* -50 (below negative lo) */
    long r7 = _clamp(100, -50, 50);  /* 50 (above positive hi) */
    printf("clamp(5,0,10)=%ld clamp(-5,0,10)=%ld clamp(15,0,10)=%ld "
           "clamp(0,0,10)=%ld clamp(10,0,10)=%ld "
           "clamp(-100,-50,50)=%ld clamp(100,-50,50)=%ld\n",
           r1, r2, r3, r4, r5, r6, r7);
    if (r1 != 5)   return 1;
    if (r2 != 0)   return 2;
    if (r3 != 10)  return 3;
    if (r4 != 0)   return 4;
    if (r5 != 10)  return 5;
    if (r6 != -50) return 6;
    if (r7 != 50)  return 7;
    return 0;
}
"#;

    let Some((exit_code, stdout)) = link_and_run("clamp", "clamp", &obj_bytes, driver) else {
        return;
    };
    eprintln!("clamp link+run stdout: {}", stdout.trim());
    assert_eq!(
        exit_code, 0,
        "clamp link+run failed (exit {}). \
         1=clamp(5,0,10)!=5, 2=clamp(-5,0,10)!=0, 3=clamp(15,0,10)!=10, \
         4=clamp(0,0,10)!=0, 5=clamp(10,0,10)!=10, \
         6=clamp(-100,-50,50)!=-50, 7=clamp(100,-50,50)!=50. stdout: {}",
        exit_code, stdout
    );
}

// =============================================================================
// Test 28: factorial(n) -- loop with multiply, compile to valid Mach-O
// =============================================================================

#[test]
fn e2e_aarch64_factorial_compile() {
    let module = build_trust_ir_factorial_module();
    let compiler = macho_compiler(CompilerConfig {
        opt_level: OptLevel::O0,
        trace_level: CompilerTraceLevel::Full,
        ..CompilerConfig::default()
    });

    let result = compiler
        .compile(&module)
        .expect("factorial compilation should succeed");

    assert!(
        !result.object_code.is_empty(),
        "factorial must produce non-empty object code"
    );
    assert_eq!(result.metrics.function_count, 1);

    let obj = &result.object_code;
    let magic = u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]);
    assert_eq!(magic, 0xFEED_FACF, "must be valid Mach-O");

    // Multi-block function with loop should produce substantial code
    assert!(
        result.metrics.code_size_bytes > 50,
        "factorial (6 blocks, loop) should produce substantial code, got {} bytes",
        result.metrics.code_size_bytes
    );

    let trace = result.trace.expect("trace should be present");
    eprintln!(
        "factorial: {} bytes, {} instructions, {} trace entries",
        result.metrics.code_size_bytes,
        result.metrics.instruction_count,
        trace.entries.len()
    );
}

// =============================================================================
// Test 29: factorial(n) -- link and run
// =============================================================================

#[test]
fn e2e_aarch64_factorial_link_and_run() {
    let module = build_trust_ir_factorial_module();
    let obj_bytes = compile_trust_ir_module_to_obj(&module);

    // 0! = 1, 1! = 1, 5! = 120, 10! = 3628800, 12! = 479001600, 20! = 2432902008176640000
    let driver = r#"
#include <stdio.h>

extern long _factorial(long n);

int main(void) {
    long r0  = _factorial(0);   /* 1 */
    long r1  = _factorial(1);   /* 1 */
    long r5  = _factorial(5);   /* 120 */
    long r10 = _factorial(10);  /* 3628800 */
    long r12 = _factorial(12);  /* 479001600 */
    long r20 = _factorial(20);  /* 2432902008176640000 */
    printf("fact(0)=%ld fact(1)=%ld fact(5)=%ld fact(10)=%ld fact(12)=%ld fact(20)=%ld\n",
           r0, r1, r5, r10, r12, r20);
    if (r0 != 1)          return 1;
    if (r1 != 1)          return 2;
    if (r5 != 120)        return 3;
    if (r10 != 3628800)   return 4;
    if (r12 != 479001600) return 5;
    if (r20 != 2432902008176640000L) return 6;
    return 0;
}
"#;

    let Some((exit_code, stdout)) = link_and_run("factorial", "factorial", &obj_bytes, driver)
    else {
        return;
    };
    eprintln!("factorial link+run stdout: {}", stdout.trim());
    assert_eq!(
        exit_code, 0,
        "factorial link+run failed (exit {}). \
         1=fact(0)!=1, 2=fact(1)!=1, 3=fact(5)!=120, 4=fact(10)!=3628800, \
         5=fact(12)!=479001600, 6=fact(20)!=2432902008176640000. stdout: {}",
        exit_code, stdout
    );
}

// =============================================================================
// Test 30: new multi-block functions at all optimization levels
// =============================================================================

#[test]
fn e2e_aarch64_new_multiblock_all_opt_levels() {
    let modules: &[(&str, TrustIrModule)] = &[
        ("classify", build_trust_ir_classify_module()),
        ("sum_to_n", build_trust_ir_sum_to_n_module()),
        ("clamp", build_trust_ir_clamp_module()),
        ("factorial", build_trust_ir_factorial_module()),
    ];

    for (name, module) in modules {
        for opt in &[OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let compiler = macho_compiler(CompilerConfig {
                opt_level: *opt,
                ..CompilerConfig::default()
            });
            let result = compiler
                .compile(module)
                .unwrap_or_else(|e| panic!("{} at {:?} failed: {}", name, opt, e));

            assert!(
                !result.object_code.is_empty(),
                "{} at {:?} produced empty object code",
                name,
                opt
            );

            let obj = &result.object_code;
            let magic = u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]);
            assert_eq!(
                magic, 0xFEED_FACF,
                "{} at {:?} produced invalid Mach-O",
                name, opt
            );

            eprintln!(
                "  {} {:?}: {} bytes",
                name, opt, result.metrics.code_size_bytes
            );
        }
    }
}

// =============================================================================
// Darwin thread-local (TLV) access path: end-to-end
// =============================================================================
//
// Builds a hand-authored trust_ir module with a thread-local global and reader/
// mutator functions, compiles it through the full backend (adapter ->
// `Opcode::TlsRef` -> `select_tls_ref` TLV sequence -> Mach-O `__thread_data`/
// `__thread_vars` emission with `ARM64_RELOC_TLVP_LOAD_PAGE21`/`PAGEOFF12` +
// the descriptor's `__tlv_bootstrap`/init `ARM64_RELOC_UNSIGNED` relocations),
// links with `cc`, and RUNS under a watchdog timeout — asserting the read value
// is correct AND per-thread isolated (a write in one thread does not perturb
// another thread's copy). This is the live oracle for the TLV access path.

/// Build a trust_ir module:
/// ```c
/// _Thread_local int X = 0xABCD;
/// int read_x(void)      { return X; }
/// int bump_x(int delta) { X = X + delta; return X; }  // write through the TLV addr
/// ```
fn build_trust_ir_thread_local_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("tls_test");

    // `_Thread_local int X = 0xABCD;` — the 4-byte little-endian template
    // `CD AB 00 00` lives in `__thread_data`; the descriptor in `__thread_vars`.
    module.globals.push(Global {
        name: "X".to_string(),
        ty: Ty::I32,
        mutable: true,
        initializer: Some(Constant::Aggregate(vec![
            Constant::Int(0xCD),
            Constant::Int(0xAB),
            Constant::Int(0x00),
            Constant::Int(0x00),
        ])),
        linkage: Linkage::External,
        // Any dynamic model selects the Darwin TLV path on Mach-O; the backend
        // lowers it to `TlsModel::Tlv` during ISel.
        tls: Some(TlsModel::GeneralDynamic),
        align: None,
    });

    // int read_x(void) { return X; }
    let ft_read = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut read = TrustIrFunction::new(FuncId::new(0), "read_x", ft_read, BlockId::new(0));
    read.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::GlobalAddr {
                global: GlobalId::new(0),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Load {
                ty: Ty::I32,
                ptr: ValueId::new(0),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    module.add_function(read);

    // int bump_x(int delta) { X = X + delta; return X; }
    let ft_bump = module.add_func_type(FuncTy {
        params: vec![Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut bump = TrustIrFunction::new(FuncId::new(1), "bump_x", ft_bump, BlockId::new(0));
    bump.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I32)], // delta
        body: vec![
            InstrNode::new(Inst::GlobalAddr {
                global: GlobalId::new(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Load {
                ty: Ty::I32,
                ptr: ValueId::new(1),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: ValueId::new(2),
                rhs: ValueId::new(0),
            })
            .with_result(ValueId::new(3)),
            // A second, independent TLV access for the store address.
            InstrNode::new(Inst::GlobalAddr {
                global: GlobalId::new(0),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Store {
                ty: Ty::I32,
                ptr: ValueId::new(4),
                value: ValueId::new(3),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    module.add_function(bump);

    module
}

#[test]
fn e2e_aarch64_thread_local_read_is_correct_and_per_thread() {
    if !can_link_and_run_aarch64_macho() {
        skip_host_tool_test("TLV link-and-run requires an aarch64-apple-darwin host");
        return;
    }

    let module = build_trust_ir_thread_local_module();
    let compiler = macho_compiler(CompilerConfig {
        opt_level: OptLevel::O0,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(&module)
        .expect("thread-local module compilation should succeed");

    let test_dir = std::env::temp_dir().join("trust_cg_e2e_tests");
    fs::create_dir_all(&test_dir).expect("create temp dir");

    let obj_path = test_dir.join("tls_x.o");
    fs::write(&obj_path, &result.object_code).expect("write object file");

    // Structural sanity: the Darwin TLV sections + symbols must be present (the
    // descriptor `_X`, the init template `_X$tlv$init`, the dyld import
    // `__tlv_bootstrap`).
    if let Some(nm) = run_macho_nm(&obj_path) {
        assert!(nm.contains("_X"), "descriptor symbol _X missing:\n{nm}");
        assert!(
            nm.contains("_X$tlv$init"),
            "init-template symbol _X$tlv$init missing:\n{nm}"
        );
        assert!(
            nm.contains("__tlv_bootstrap"),
            "dyld thunk import __tlv_bootstrap missing:\n{nm}"
        );
    }

    let driver_path = test_dir.join("driver_tls.c");
    let driver_src = r#"
#include <stdio.h>
#include <pthread.h>

extern int read_x(void);
extern int bump_x(int);

static int worker_result;
static void *worker(void *arg) {
    (void)arg;
    // This thread mutates its OWN per-thread copy by +200 (two +100 bumps).
    bump_x(100);
    worker_result = bump_x(100);
    return NULL;
}

int main(void) {
    int v0 = read_x();      // expect init 0xABCD = 43981
    int vm = bump_x(1);     // main's copy -> 43982
    pthread_t t;
    pthread_create(&t, NULL, worker, NULL);
    pthread_join(t, NULL);
    int vm2 = read_x();     // main's copy must be unperturbed by the worker
    printf("%d %d %d %d\n", v0, vm, worker_result, vm2);
    int ok = (v0 == 43981) && (vm == 43982) && (worker_result == 44181) && (vm2 == 43982);
    return ok ? 0 : 1;
}
"#;
    fs::write(&driver_path, driver_src).expect("write driver source");

    let binary_path = test_dir.join("test_tls");
    let link_output = Command::new("cc")
        .args([
            driver_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-o",
            binary_path.to_str().unwrap(),
        ])
        .output()
        .expect("cc should be available");

    if !link_output.status.success() {
        panic!(
            "Linking the TLV object failed:\n{}",
            String::from_utf8_lossy(&link_output.stderr)
        );
    }

    // Run under a watchdog: a botched TLV descriptor / BLR would hang or crash.
    let run_output = Command::new("timeout")
        .args(["10", binary_path.to_str().unwrap()])
        .output()
        .or_else(|_| Command::new(binary_path.to_str().unwrap()).output())
        .expect("run the TLV binary");

    let run_stdout = String::from_utf8_lossy(&run_output.stdout);
    eprintln!("TLV binary stdout: {}", run_stdout.trim());
    eprintln!("TLV binary exit: {:?}", run_output.status.code());

    assert!(
        run_output.status.success(),
        "TLV binary must exit 0 (correct, per-thread reads/writes). stdout: {}\nstderr: {}",
        run_stdout,
        String::from_utf8_lossy(&run_output.stderr),
    );
    assert_eq!(
        run_stdout.trim(),
        "43981 43982 44181 43982",
        "thread-local read must be 0xABCD and per-thread isolated"
    );
}
