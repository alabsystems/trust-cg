#![allow(dead_code)]
// trust-cg-codegen/tests/common/x86_64_corpus.rs - Shared x86-64 oracle corpus & harness
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Shared infrastructure for the x86-64 correctness oracles (WS0 of
// docs/x86_64_completion_plan.md). This mirrors the AArch64 harnesses in
// `e2e_differential.rs` and `e2e_triple_oracle.rs`, but compiles trust_ir
// through Trust Codegen with `Target::X86_64` so the produced object is a
// real x86-64 Mach-O on this macOS host, links it with `cc -arch x86_64`,
// and compares against clang-compiled C equivalents (and, for the triple
// oracle, the trust_ir interpreter).
//
// The trust_ir module builders below are byte-for-byte the same shapes used
// by the AArch64 corpus, so x86-64 codegen is held to the identical contract.
// They live in `common/` so both `e2e_x86_64_differential.rs` and
// `e2e_x86_64_triple_oracle.rs` consume one copy.

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::interpreter::{InterpreterValue, interpret};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;

use trust_ir::{BinOp, ICmpOp, Inst, InstrNode};
use trust_ir::{
    Block as TrustIrBlock, Constant, FuncTy, Function as TrustIrFunction, Module as TrustIrModule,
    Ty,
};
use trust_ir::{BlockId, FuncId, ValueId};

use super::rosetta::{
    codegen_link_timeout, codegen_run_timeout, command_output_with_timeout, has_cc_x86_64_link_run,
    run_executable_with_timeout,
};

// =============================================================================
// Gating
// =============================================================================

/// Returns true if we are running on an x86-64 host.
pub fn is_x86_64() -> bool {
    cfg!(target_arch = "x86_64")
}

/// Returns true if `cc -arch x86_64` can compile, link, and run a binary on
/// this host (native x86-64, or a healthy Rosetta 2 aarch64 host).
pub fn can_link_run_x86_64() -> bool {
    has_cc_x86_64_link_run()
}

/// Combined gate used by every x86-64 oracle test. Returns true when the
/// test body should execute. Logs a skip reason and returns false otherwise.
pub fn x86_64_oracle_enabled(test_name: &str) -> bool {
    if !is_x86_64() {
        eprintln!("Skipping x86-64 oracle {test_name}: host is not x86-64");
        return false;
    }
    if !can_link_run_x86_64() {
        eprintln!("Skipping x86-64 oracle {test_name}: cc -arch x86_64 link/run unavailable");
        return false;
    }
    true
}

// =============================================================================
// Trust Codegen x86-64 object emission (AOT Mach-O on this host)
// =============================================================================

/// Compile a trust_ir module through Trust Codegen targeting x86-64, returning
/// raw object-code bytes. On macOS the host object format is Mach-O.
pub fn compile_trust_ir_module_x86_64(module: &TrustIrModule) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        target: Target::X86_64,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(module)
        .expect("Trust Codegen x86-64 compilation should succeed");
    assert!(
        !result.object_code.is_empty(),
        "Trust Codegen must produce non-empty x86-64 object code"
    );
    result.object_code
}

fn make_test_dir(test_name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("trust_cg_x86_64_oracle_{test_name}"));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("Failed to create test directory");
    dir
}

fn cleanup(dir: &Path) {
    let _ = fs::remove_dir_all(dir);
}

fn cc_link_x86_64(args: &[&str]) -> Result<(bool, String, String), String> {
    let mut cmd = Command::new("cc");
    cmd.arg("-arch").arg("x86_64");
    for a in args {
        cmd.arg(a);
    }
    let result = command_output_with_timeout(&mut cmd, codegen_link_timeout())
        .map_err(|e| format!("cc -arch x86_64 failed to spawn: {e}"))?;
    let stdout = String::from_utf8_lossy(&result.output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&result.output.stderr).to_string();
    if result.timed_out {
        return Err(format!(
            "cc -arch x86_64 timed out after {:?}: stdout={}, stderr={}",
            codegen_link_timeout(),
            stdout.trim(),
            stderr.trim()
        ));
    }
    Ok((result.output.status.success(), stdout, stderr))
}

fn run_x86_64_binary(binary: &Path) -> Result<(i32, String), String> {
    let result = run_executable_with_timeout(binary, codegen_run_timeout())
        .map_err(|e| format!("run x86-64 binary failed to spawn: {e}"))?;
    if result.timed_out {
        let stdout = String::from_utf8_lossy(&result.output.stdout).to_string();
        let stderr = String::from_utf8_lossy(&result.output.stderr).to_string();
        return Err(format!(
            "x86-64 binary {} timed out after {:?}: stdout={}, stderr={}",
            binary.display(),
            codegen_run_timeout(),
            stdout.trim(),
            stderr.trim()
        ));
    }
    let stdout = String::from_utf8_lossy(&result.output.stdout).to_string();
    let exit = result.output.status.code().unwrap_or(-1);
    Ok((exit, stdout))
}

// =============================================================================
// Differential harness: Trust Codegen (x86-64 Mach-O) vs clang
// =============================================================================

/// Run a differential test: compile the same function(s) through Trust Codegen
/// (x86-64) and clang (`cc -arch x86_64`), link each against the shared driver,
/// run both, and assert stdout and exit code match. clang is the golden oracle.
pub fn x86_64_differential_test(
    test_name: &str,
    trust_ir_module: &TrustIrModule,
    c_reference: &str,
    driver_src: &str,
) -> Result<(), String> {
    let dir = make_test_dir(test_name);

    // --- Step 1: Trust Codegen path (x86-64 Mach-O object) ---
    let trust_cg_obj_bytes = compile_trust_ir_module_x86_64(trust_ir_module);
    let trust_cg_obj_path = dir.join("trust_cg_func.o");
    fs::write(&trust_cg_obj_path, &trust_cg_obj_bytes)
        .map_err(|e| format!("write trust-cg .o: {e}"))?;

    // --- Step 2: Clang path (compile reference C to x86-64 object) ---
    let ref_c_path = dir.join("reference.c");
    fs::write(&ref_c_path, c_reference).map_err(|e| format!("write reference.c: {e}"))?;
    let clang_obj_path = dir.join("clang_func.o");
    let (ok, _o, e) = cc_link_x86_64(&[
        "-c",
        "-O0",
        "-o",
        clang_obj_path.to_str().unwrap(),
        ref_c_path.to_str().unwrap(),
    ])?;
    if !ok {
        cleanup(&dir);
        return Err(format!("cc -c reference.c failed: {e}"));
    }

    // --- Step 3: Shared driver ---
    let driver_path = dir.join("driver.c");
    fs::write(&driver_path, driver_src).map_err(|e| format!("write driver.c: {e}"))?;

    // --- Step 4: Link and run Trust Codegen version ---
    let trust_cg_binary = dir.join("test_trust_cg");
    let (ok, _o, e) = cc_link_x86_64(&[
        "-o",
        trust_cg_binary.to_str().unwrap(),
        driver_path.to_str().unwrap(),
        trust_cg_obj_path.to_str().unwrap(),
    ])?;
    if !ok {
        let nm = Command::new("nm")
            .arg(trust_cg_obj_path.to_str().unwrap())
            .output()
            .ok()
            .map(|o| String::from_utf8_lossy(&o.stdout).to_string())
            .unwrap_or_default();
        let otool = Command::new("otool")
            .args(["-tv", trust_cg_obj_path.to_str().unwrap()])
            .output()
            .ok()
            .map(|o| String::from_utf8_lossy(&o.stdout).to_string())
            .unwrap_or_default();
        cleanup(&dir);
        return Err(format!(
            "Linking Trust Codegen x86-64 binary failed!\nstderr: {e}\nnm:\n{nm}\notool:\n{otool}"
        ));
    }
    let (trust_cg_exit, trust_cg_stdout) = run_x86_64_binary(&trust_cg_binary)?;

    // --- Step 5: Link and run clang version ---
    let clang_binary = dir.join("test_clang");
    let (ok, _o, e) = cc_link_x86_64(&[
        "-o",
        clang_binary.to_str().unwrap(),
        driver_path.to_str().unwrap(),
        clang_obj_path.to_str().unwrap(),
    ])?;
    if !ok {
        cleanup(&dir);
        return Err(format!("Linking clang x86-64 binary failed: {e}"));
    }
    let (clang_exit, clang_stdout) = run_x86_64_binary(&clang_binary)?;

    // --- Step 6: Compare ---
    eprintln!("=== x86-64 differential: {test_name} ===");
    eprintln!("  Trust Codegen stdout: {}", trust_cg_stdout.trim());
    eprintln!("  Clang stdout:         {}", clang_stdout.trim());
    eprintln!("  Trust Codegen exit:   {trust_cg_exit}");
    eprintln!("  Clang exit:           {clang_exit}");

    if trust_cg_stdout != clang_stdout {
        let disasm = Command::new("otool")
            .args(["-tv", trust_cg_obj_path.to_str().unwrap()])
            .output()
            .ok()
            .map(|o| String::from_utf8_lossy(&o.stdout).to_string())
            .unwrap_or_default();
        cleanup(&dir);
        return Err(format!(
            "OUTPUT MISMATCH!\n  Trust Codegen: {}\n  Clang: {}\n  Trust Codegen disassembly:\n{}",
            trust_cg_stdout.trim(),
            clang_stdout.trim(),
            disasm
        ));
    }

    if trust_cg_exit != clang_exit {
        cleanup(&dir);
        return Err(format!(
            "EXIT CODE MISMATCH!\n  Trust Codegen: {trust_cg_exit}\n  Clang: {clang_exit}"
        ));
    }

    // Both must actually succeed (not just matching failures).
    if clang_exit != 0 {
        cleanup(&dir);
        return Err(format!(
            "Both binaries exited with non-zero code {clang_exit}. \
             The C reference itself has a bug or the driver is wrong."
        ));
    }

    cleanup(&dir);
    Ok(())
}

// =============================================================================
// Triple-oracle harness: interpreter vs Trust Codegen (x86-64) vs clang
// =============================================================================

/// A single triple-oracle case: function input(s) and the key used in stdout.
pub struct TripleOracleCase {
    /// Key used in the driver's printf (e.g., "fib(10)").
    pub key: String,
    /// Arguments to the function.
    pub args: Vec<i64>,
}

impl TripleOracleCase {
    pub fn new(key: &str, args: &[i64]) -> Self {
        Self {
            key: key.to_string(),
            args: args.to_vec(),
        }
    }
}

/// Parse "key=value" lines from stdout into a map of i64 results.
fn parse_results(stdout: &str) -> HashMap<String, i64> {
    let mut map = HashMap::new();
    for line in stdout.lines() {
        let line = line.trim();
        if let Some((key, val_str)) = line.split_once('=')
            && let Ok(val) = val_str.trim().parse::<i64>()
        {
            map.insert(key.trim().to_string(), val);
        }
    }
    map
}

/// Run the trust_ir interpreter for `func_name` with i64 args, returning i64.
fn interp_i64(module: &TrustIrModule, func_name: &str, args: &[i64]) -> i64 {
    let interp_args: Vec<InterpreterValue> = args
        .iter()
        .map(|&a| InterpreterValue::Int(a as i128))
        .collect();
    let result = interpret(module, func_name, &interp_args)
        .unwrap_or_else(|e| panic!("interpreter failed on {func_name}({args:?}): {e}"));
    assert_eq!(result.len(), 1, "expected single return value");
    result[0].as_int().expect("expected Int result") as i64
}

/// Three-way agreement: trust_ir interpreter, Trust Codegen (x86-64 Mach-O),
/// and clang must all return the same value for every case.
///
/// `c_source` is a single C file that defines the function under `#ifndef
/// EXTERN_ONLY` and declares it `extern` under `#ifdef EXTERN_ONLY`, plus a
/// `main` that prints `key=value` lines. The Trust Codegen path compiles the
/// driver with `-DEXTERN_ONLY` and links the Trust Codegen object; clang
/// compiles the whole file standalone.
pub fn x86_64_triple_oracle_test(
    test_name: &str,
    trust_ir_module: &TrustIrModule,
    func_name: &str,
    c_source: &str,
    cases: &[TripleOracleCase],
) -> Result<(), String> {
    let dir = make_test_dir(test_name);

    // --- Oracle 1: Interpreter ---
    let mut interp_results: HashMap<String, i64> = HashMap::new();
    for tc in cases {
        interp_results.insert(
            tc.key.clone(),
            interp_i64(trust_ir_module, func_name, &tc.args),
        );
    }
    eprintln!("=== x86-64 triple oracle: {test_name} ===");
    eprintln!("  Interpreter results:  {interp_results:?}");

    // --- Oracle 2: Trust Codegen compiled binary (x86-64 Mach-O) ---
    let trust_cg_obj_bytes = compile_trust_ir_module_x86_64(trust_ir_module);
    let trust_cg_obj_path = dir.join("trust_cg_func.o");
    fs::write(&trust_cg_obj_path, &trust_cg_obj_bytes)
        .map_err(|e| format!("write trust-cg .o: {e}"))?;

    let driver_path = dir.join("trust_cg_driver.c");
    fs::write(&driver_path, c_source).map_err(|e| format!("write trust_cg_driver.c: {e}"))?;

    let trust_cg_binary = dir.join("test_trust_cg");
    let (ok, _o, e) = cc_link_x86_64(&[
        "-DEXTERN_ONLY",
        "-O0",
        "-o",
        trust_cg_binary.to_str().unwrap(),
        driver_path.to_str().unwrap(),
        trust_cg_obj_path.to_str().unwrap(),
    ])?;
    if !ok {
        let nm = Command::new("nm")
            .arg(trust_cg_obj_path.to_str().unwrap())
            .output()
            .ok()
            .map(|o| String::from_utf8_lossy(&o.stdout).to_string())
            .unwrap_or_default();
        cleanup(&dir);
        return Err(format!(
            "Trust Codegen x86-64 link failed!\nstderr: {e}\nnm:\n{nm}"
        ));
    }
    let (trust_cg_exit, trust_cg_stdout) = run_x86_64_binary(&trust_cg_binary)?;
    if trust_cg_exit != 0 {
        cleanup(&dir);
        return Err(format!(
            "Trust Codegen x86-64 binary exited with code {trust_cg_exit}"
        ));
    }
    let trust_cg_results = parse_results(&trust_cg_stdout);
    eprintln!("  Trust Codegen results: {trust_cg_results:?}");

    // --- Oracle 3: clang standalone binary ---
    let ref_path = dir.join("clang_reference.c");
    fs::write(&ref_path, c_source).map_err(|e| format!("write clang_reference.c: {e}"))?;
    let clang_binary = dir.join("test_clang");
    let (ok, _o, e) = cc_link_x86_64(&[
        "-O0",
        "-o",
        clang_binary.to_str().unwrap(),
        ref_path.to_str().unwrap(),
    ])?;
    if !ok {
        cleanup(&dir);
        return Err(format!("clang x86-64 compile failed: {e}"));
    }
    let (clang_exit, clang_stdout) = run_x86_64_binary(&clang_binary)?;
    if clang_exit != 0 {
        cleanup(&dir);
        return Err(format!("clang x86-64 binary exited with code {clang_exit}"));
    }
    let clang_results = parse_results(&clang_stdout);
    eprintln!("  Clang results:         {clang_results:?}");

    // --- Compare all three ---
    let mut mismatches = Vec::new();
    for tc in cases {
        let interp_val = interp_results.get(&tc.key);
        let trust_cg_val = trust_cg_results.get(&tc.key);
        let clang_val = clang_results.get(&tc.key);
        match (interp_val, trust_cg_val, clang_val) {
            (Some(&i), Some(&l), Some(&c)) => {
                if i != l || i != c {
                    mismatches.push(format!(
                        "  {}: interp={i}, trust-cg={l}, clang={c}",
                        tc.key
                    ));
                }
            }
            _ => mismatches.push(format!(
                "  {}: MISSING -- interp={interp_val:?}, trust-cg={trust_cg_val:?}, clang={clang_val:?}",
                tc.key
            )),
        }
    }

    cleanup(&dir);
    if mismatches.is_empty() {
        eprintln!("  ALL THREE ORACLES AGREE");
        Ok(())
    } else {
        Err(format!(
            "TRIPLE ORACLE MISMATCH for {test_name}:\n{}",
            mismatches.join("\n")
        ))
    }
}

// =============================================================================
// trust_ir corpus builders (same shapes as the AArch64 corpus)
// =============================================================================

/// `int _add_two(int a, int b) { return a + b; }`
pub fn build_add_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I32, Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_add_two", ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I32), (ValueId::new(1), Ty::I32)],
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

/// `long _max_val(long a, long b) { return (a > b) ? a : b; }`
pub fn build_max_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_max_val", ft_id, BlockId::new(0));
    func.blocks = vec![
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sgt,
                    ty: Ty::I64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(2),
                    then_target: BlockId::new(1),
                    then_args: vec![],
                    else_target: BlockId::new(2),
                    else_args: vec![],
                }),
            ],
        },
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            })],
        },
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

/// `long _abs_val(long x) { return (x < 0) ? -x : x; }`
pub fn build_abs_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_abs_val", ft_id, BlockId::new(0));
    func.blocks = vec![
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Slt,
                    ty: Ty::I64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(2),
                    then_target: BlockId::new(1),
                    then_args: vec![],
                    else_target: BlockId::new(2),
                    else_args: vec![],
                }),
            ],
        },
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Sub,
                    ty: Ty::I64,
                    lhs: ValueId::new(1), // 0
                    rhs: ValueId::new(0), // x
                })
                .with_result(ValueId::new(3)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(3)],
                }),
            ],
        },
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

/// `long _sum_1_to_n(long n)` — loop accumulating 1..=n.
pub fn build_sum_1_to_n_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_sum_1_to_n", ft_id, BlockId::new(0));
    func.blocks = vec![
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)],
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
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![(ValueId::new(10), Ty::I64), (ValueId::new(11), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    lhs: ValueId::new(11),
                    rhs: ValueId::new(0),
                })
                .with_result(ValueId::new(12)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(12),
                    then_target: BlockId::new(2),
                    then_args: vec![],
                    else_target: BlockId::new(3),
                    else_args: vec![],
                }),
            ],
        },
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(10),
                    rhs: ValueId::new(11),
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
                    lhs: ValueId::new(11),
                    rhs: ValueId::new(21),
                })
                .with_result(ValueId::new(22)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(1),
                    args: vec![ValueId::new(20), ValueId::new(22)],
                }),
            ],
        },
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(10)],
            })],
        },
    ];
    module.add_function(func);
    module
}

/// `long _factorial(long n)` — iterative factorial.
pub fn build_factorial_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_factorial", ft_id, BlockId::new(0));
    func.blocks = vec![
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(2),
                    then_target: BlockId::new(1),
                    then_args: vec![],
                    else_target: BlockId::new(2),
                    else_args: vec![],
                }),
            ],
        },
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            })],
        },
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
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![(ValueId::new(20), Ty::I64), (ValueId::new(21), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    lhs: ValueId::new(21),
                    rhs: ValueId::new(0),
                })
                .with_result(ValueId::new(22)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(22),
                    then_target: BlockId::new(4),
                    then_args: vec![],
                    else_target: BlockId::new(5),
                    else_args: vec![],
                }),
            ],
        },
        TrustIrBlock {
            id: BlockId::new(4),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Mul,
                    ty: Ty::I64,
                    lhs: ValueId::new(20),
                    rhs: ValueId::new(21),
                })
                .with_result(ValueId::new(30)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(31)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(21),
                    rhs: ValueId::new(31),
                })
                .with_result(ValueId::new(32)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(3),
                    args: vec![ValueId::new(30), ValueId::new(32)],
                }),
            ],
        },
        TrustIrBlock {
            id: BlockId::new(5),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(20)],
            })],
        },
    ];
    module.add_function(func);
    module
}

/// `long _fibonacci(long n)` — iterative fibonacci.
pub fn build_fibonacci_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_fibonacci", ft_id, BlockId::new(0));
    func.blocks = vec![
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(2),
                    then_target: BlockId::new(1),
                    then_args: vec![],
                    else_target: BlockId::new(2),
                    else_args: vec![],
                }),
            ],
        },
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            })],
        },
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
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![
                (ValueId::new(20), Ty::I64),
                (ValueId::new(21), Ty::I64),
                (ValueId::new(22), Ty::I64),
            ],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(20),
                    rhs: ValueId::new(21),
                })
                .with_result(ValueId::new(23)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(24)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(22),
                    rhs: ValueId::new(24),
                })
                .with_result(ValueId::new(25)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    lhs: ValueId::new(25),
                    rhs: ValueId::new(0),
                })
                .with_result(ValueId::new(26)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(26),
                    then_target: BlockId::new(3),
                    then_args: vec![ValueId::new(21), ValueId::new(23), ValueId::new(25)],
                    else_target: BlockId::new(4),
                    else_args: vec![ValueId::new(23)],
                }),
            ],
        },
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

/// `long _gcd(long a, long b)` — Euclidean algorithm using SRem.
pub fn build_gcd_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_gcd", ft_id, BlockId::new(0));
    func.blocks = vec![
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
            body: vec![InstrNode::new(Inst::Br {
                target: BlockId::new(1),
                args: vec![ValueId::new(0), ValueId::new(1)],
            })],
        },
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![(ValueId::new(10), Ty::I64), (ValueId::new(11), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(12)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ne,
                    ty: Ty::I64,
                    lhs: ValueId::new(11),
                    rhs: ValueId::new(12),
                })
                .with_result(ValueId::new(13)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(13),
                    then_target: BlockId::new(2),
                    then_args: vec![],
                    else_target: BlockId::new(3),
                    else_args: vec![ValueId::new(10)],
                }),
            ],
        },
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::SRem,
                    ty: Ty::I64,
                    lhs: ValueId::new(10),
                    rhs: ValueId::new(11),
                })
                .with_result(ValueId::new(20)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(1),
                    args: vec![ValueId::new(11), ValueId::new(20)],
                }),
            ],
        },
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![(ValueId::new(30), Ty::I64)],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(30)],
            })],
        },
    ];
    module.add_function(func);
    module
}

/// `long _collatz_steps(long n)` — Collatz step count (uses SRem and SDiv).
pub fn build_collatz_steps_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_collatz_steps", ft_id, BlockId::new(0));
    func.blocks = vec![
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(2),
                    then_target: BlockId::new(5),
                    then_args: vec![],
                    else_target: BlockId::new(1),
                    else_args: vec![ValueId::new(0)],
                }),
            ],
        },
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![(ValueId::new(3), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(4)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(2),
                    args: vec![ValueId::new(3), ValueId::new(4)],
                }),
            ],
        },
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![(ValueId::new(5), Ty::I64), (ValueId::new(6), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(7)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ne,
                    ty: Ty::I64,
                    lhs: ValueId::new(5),
                    rhs: ValueId::new(7),
                })
                .with_result(ValueId::new(8)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(8),
                    then_target: BlockId::new(3),
                    then_args: vec![ValueId::new(5), ValueId::new(6)],
                    else_target: BlockId::new(6),
                    else_args: vec![ValueId::new(6)],
                }),
            ],
        },
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![(ValueId::new(9), Ty::I64), (ValueId::new(10), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(2),
                })
                .with_result(ValueId::new(11)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(12)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::SRem,
                    ty: Ty::I64,
                    lhs: ValueId::new(9),
                    rhs: ValueId::new(11),
                })
                .with_result(ValueId::new(13)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::I64,
                    lhs: ValueId::new(13),
                    rhs: ValueId::new(12),
                })
                .with_result(ValueId::new(14)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(14),
                    then_target: BlockId::new(4),
                    then_args: vec![ValueId::new(9), ValueId::new(10)],
                    else_target: BlockId::new(7),
                    else_args: vec![ValueId::new(9), ValueId::new(10)],
                }),
            ],
        },
        TrustIrBlock {
            id: BlockId::new(4),
            params: vec![(ValueId::new(15), Ty::I64), (ValueId::new(16), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(2),
                })
                .with_result(ValueId::new(17)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(18)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::SDiv,
                    ty: Ty::I64,
                    lhs: ValueId::new(15),
                    rhs: ValueId::new(17),
                })
                .with_result(ValueId::new(19)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(16),
                    rhs: ValueId::new(18),
                })
                .with_result(ValueId::new(20)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(2),
                    args: vec![ValueId::new(19), ValueId::new(20)],
                }),
            ],
        },
        TrustIrBlock {
            id: BlockId::new(5),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(21)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(21)],
                }),
            ],
        },
        TrustIrBlock {
            id: BlockId::new(6),
            params: vec![(ValueId::new(22), Ty::I64)],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(22)],
            })],
        },
        TrustIrBlock {
            id: BlockId::new(7),
            params: vec![(ValueId::new(23), Ty::I64), (ValueId::new(24), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(3),
                })
                .with_result(ValueId::new(25)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(26)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Mul,
                    ty: Ty::I64,
                    lhs: ValueId::new(23),
                    rhs: ValueId::new(25),
                })
                .with_result(ValueId::new(27)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(27),
                    rhs: ValueId::new(26),
                })
                .with_result(ValueId::new(28)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(24),
                    rhs: ValueId::new(26),
                })
                .with_result(ValueId::new(29)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(2),
                    args: vec![ValueId::new(28), ValueId::new(29)],
                }),
            ],
        },
    ];
    module.add_function(func);
    module
}

/// Recursive/chained calls: `_fact_helper(n, acc)` tail-recurses, and
/// `_fact_double(n) = _fact_helper(n, 1) * 2`. Exercises the call ABI and
/// recursion through Trust Codegen's x86-64 backend.
pub fn build_recursive_fact_double_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");

    let ft_id_0 = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut fact_helper =
        TrustIrFunction::new(FuncId::new(0), "_fact_helper", ft_id_0, BlockId::new(0));
    fact_helper.blocks = vec![
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(2),
                })
                .with_result(ValueId::new(3)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(3),
                    then_target: BlockId::new(1),
                    then_args: vec![ValueId::new(1)],
                    else_target: BlockId::new(2),
                    else_args: vec![ValueId::new(0), ValueId::new(1)],
                }),
            ],
        },
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![(ValueId::new(8), Ty::I64)],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(8)],
            })],
        },
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![(ValueId::new(9), Ty::I64), (ValueId::new(10), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(11)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Sub,
                    ty: Ty::I64,
                    lhs: ValueId::new(9),
                    rhs: ValueId::new(11),
                })
                .with_result(ValueId::new(12)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Mul,
                    ty: Ty::I64,
                    lhs: ValueId::new(10),
                    rhs: ValueId::new(9),
                })
                .with_result(ValueId::new(13)),
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(0),
                    args: vec![ValueId::new(12), ValueId::new(13)],
                })
                .with_result(ValueId::new(14)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(14)],
                }),
            ],
        },
    ];

    let ft_id_1 = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut fact_double =
        TrustIrFunction::new(FuncId::new(1), "_fact_double", ft_id_1, BlockId::new(0));
    fact_double.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![ValueId::new(0), ValueId::new(1)],
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(2),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: ValueId::new(2),
                rhs: ValueId::new(3),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(4)],
            }),
        ],
    }];

    module.add_function(fact_helper);
    module.add_function(fact_double);
    module
}

/// `long _ipow(long base, long exp)` — iterative integer power `base**exp`
/// (exp >= 0). Loop with running product. Exercises a two-input loop and Mul.
/// `int _deep_select_chain(int v0, int v1, int v2, int v3, int v4, int v5, int v6)`
///
/// A straight-line, single-block function that builds seven distinct boolean
/// predicates (six `SETcc` results plus one `AND`-derived flag) that are all
/// simultaneously live into a seven-deep `select`/CMOV chain. The earliest
/// predicate (`cached_drop`) has the longest live range: it is defined first
/// yet only consumed by the final `select`.
///
/// This is the exact shape of the SAT minimize keep/drop classifier and is a
/// permanent regression for the x86-64 register-allocator numbering bug where a
/// coalesced (copy-removed) stream desynchronized live-interval positions from
/// the splitter, causing the long-lived predicate's register to be reused by a
/// later `SETBE` without preservation. The final CMOV then tested the wrong
/// predicate byte and returned DROP(0) instead of KEEP(1).
pub fn build_deep_select_chain_module() -> TrustIrModule {
    fn v(id: u32) -> ValueId {
        ValueId::new(id)
    }
    fn const_i32(body: &mut Vec<InstrNode>, result: ValueId, value: i32) {
        body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(value.into()),
            })
            .with_result(result),
        );
    }
    fn icmp_i32(
        body: &mut Vec<InstrNode>,
        result: ValueId,
        op: ICmpOp,
        lhs: ValueId,
        rhs: ValueId,
    ) {
        body.push(
            InstrNode::new(Inst::ICmp {
                op,
                ty: Ty::I32,
                lhs,
                rhs,
            })
            .with_result(result),
        );
    }
    fn select_i32(
        body: &mut Vec<InstrNode>,
        result: ValueId,
        cond: ValueId,
        then_val: ValueId,
        else_val: ValueId,
    ) {
        body.push(
            InstrNode::new(Inst::Select {
                ty: Ty::I32,
                cond,
                then_val,
                else_val,
            })
            .with_result(result),
        );
    }
    fn binop_i32(
        body: &mut Vec<InstrNode>,
        result: ValueId,
        op: BinOp,
        lhs: ValueId,
        rhs: ValueId,
    ) {
        body.push(
            InstrNode::new(Inst::BinOp {
                op,
                ty: Ty::I32,
                lhs,
                rhs,
            })
            .with_result(result),
        );
    }

    const DROP: i32 = 0;
    const KEEP: i32 = 1;
    const CHECK: i32 = 2;
    const REMOVABLE: i32 = 0x02;
    const KEEPF: i32 = 0x08;
    const POISON: i32 = 0x04;
    const NO_REASON: i32 = -1;

    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I32; 7],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut body = Vec::new();

    let zero = v(7);
    let one = v(8);
    let two = v(9);
    let cached_drop_mask = v(10);
    let poison_mask = v(11);
    let no_reason = v(12);
    const_i32(&mut body, zero, DROP);
    const_i32(&mut body, one, KEEP);
    const_i32(&mut body, two, CHECK);
    const_i32(&mut body, cached_drop_mask, REMOVABLE | KEEPF);
    const_i32(&mut body, poison_mask, POISON);
    const_i32(&mut body, no_reason, NO_REASON);

    let mut next = 13;
    let cached_drop_bits = v(next);
    next += 1;
    binop_i32(
        &mut body,
        cached_drop_bits,
        BinOp::And,
        v(3),
        cached_drop_mask,
    );
    let cached_drop = v(next);
    next += 1;
    icmp_i32(&mut body, cached_drop, ICmpOp::Ne, cached_drop_bits, zero);

    let poison_bits = v(next);
    next += 1;
    binop_i32(&mut body, poison_bits, BinOp::And, v(3), poison_mask);
    let poison = v(next);
    next += 1;
    icmp_i32(&mut body, poison, ICmpOp::Ne, poison_bits, zero);

    let current_decision_level = v(next);
    next += 1;
    icmp_i32(&mut body, current_decision_level, ICmpOp::Eq, v(0), v(6));
    let decision_variable = v(next);
    next += 1;
    icmp_i32(&mut body, decision_variable, ICmpOp::Eq, v(2), no_reason);
    let single_seen = v(next);
    next += 1;
    icmp_i32(&mut body, single_seen, ICmpOp::Ult, v(4), two);
    let trail_abort = v(next);
    next += 1;
    icmp_i32(&mut body, trail_abort, ICmpOp::Ule, v(1), v(5));
    let level_zero = v(next);
    next += 1;
    icmp_i32(&mut body, level_zero, ICmpOp::Eq, v(0), zero);

    let trail_result = v(next);
    next += 1;
    select_i32(&mut body, trail_result, trail_abort, one, two);
    let seen_result = v(next);
    next += 1;
    select_i32(&mut body, seen_result, single_seen, one, trail_result);
    let decision_var_result = v(next);
    next += 1;
    select_i32(
        &mut body,
        decision_var_result,
        decision_variable,
        one,
        seen_result,
    );
    let current_level_result = v(next);
    next += 1;
    select_i32(
        &mut body,
        current_level_result,
        current_decision_level,
        one,
        decision_var_result,
    );
    let poison_result = v(next);
    next += 1;
    select_i32(&mut body, poison_result, poison, one, current_level_result);
    let cached_result = v(next);
    next += 1;
    select_i32(&mut body, cached_result, cached_drop, zero, poison_result);
    let result = v(next);
    select_i32(&mut body, result, level_zero, zero, cached_result);
    body.push(InstrNode::new(Inst::Return {
        values: vec![result],
    }));

    let mut func =
        TrustIrFunction::new(FuncId::new(0), "_deep_select_chain", ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: (0..7).map(|i| (v(i), Ty::I32)).collect(),
        body,
    }];
    module.add_function(func);
    module
}

pub fn build_ipow_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_ipow", ft_id, BlockId::new(0));
    func.blocks = vec![
        // bb0 (entry): result=1, i=0, br -> loop(result, i)
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)], // base, exp
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(2)), // result = 1
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(3)), // i = 0
                InstrNode::new(Inst::Br {
                    target: BlockId::new(1),
                    args: vec![ValueId::new(2), ValueId::new(3)],
                }),
            ],
        },
        // bb1 (loop header): params(result, i). while i < exp.
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![(ValueId::new(10), Ty::I64), (ValueId::new(11), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Slt,
                    ty: Ty::I64,
                    lhs: ValueId::new(11), // i
                    rhs: ValueId::new(1),  // exp
                })
                .with_result(ValueId::new(12)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(12),
                    then_target: BlockId::new(2),
                    then_args: vec![],
                    else_target: BlockId::new(3),
                    else_args: vec![],
                }),
            ],
        },
        // bb2 (body): result *= base; i += 1; br -> loop.
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Mul,
                    ty: Ty::I64,
                    lhs: ValueId::new(10), // result
                    rhs: ValueId::new(0),  // base
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
                    rhs: ValueId::new(21),
                })
                .with_result(ValueId::new(22)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(1),
                    args: vec![ValueId::new(20), ValueId::new(22)],
                }),
            ],
        },
        // bb3 (exit): return result.
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(10)],
            })],
        },
    ];
    module.add_function(func);
    module
}

// =============================================================================
// i128 (128-bit integer) corpus builders
//
// These exercise the x86-64 i128 register-pair lowering (arithmetic, compare,
// shifts) and the SysV i128 ABI (args in a consecutive GPR pair, return in
// RAX:RDX). They are the permanent regressions for the silent-miscompile fix
// where the x86-64 ISel previously lowered I128 as a single 64-bit register.
// =============================================================================

/// `__int128 f(__int128 a, __int128 b) { return a <binop> b; }`
pub fn build_i128_binop_module(name: &str, op: BinOp) -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I128, Ty::I128],
        returns: vec![Ty::I128],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), name, ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I128), (ValueId::new(1), Ty::I128)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op,
                ty: Ty::I128,
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

/// `long f(__int128 a, __int128 b) { return (a <cmp> b); }` — the bool result is
/// zero-extended to i64 so it can be returned in a single GPR.
pub fn build_i128_cmp_module(name: &str, op: ICmpOp) -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I128, Ty::I128],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), name, ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I128), (ValueId::new(1), Ty::I128)],
        body: vec![
            InstrNode::new(Inst::ICmp {
                op,
                ty: Ty::I128,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Cast {
                op: trust_ir::CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::I64,
                operand: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

/// `long f(long a, long b)` computing the HIGH 64 bits of the 128-bit signed
/// product `(__int128)a * (__int128)b`, i.e. `(long)(((__int128)a * b) >> 64)`.
///
/// This routes an i64-in / i64-out signature (so the i64-based triple-oracle
/// harness can drive it) through the full i128 lowering pipeline: two SExt
/// widenings to i128, an i128 multiply (cross terms), an i128 arithmetic
/// right-shift by 64 (the >= 64 boundary case), and a truncation back to i64.
pub fn build_i128_mulhi_i64_module(name: &str) -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), name, ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            // a128 = sext a to i128
            InstrNode::new(Inst::Cast {
                op: trust_ir::CastOp::SExt,
                src_ty: Ty::I64,
                dst_ty: Ty::I128,
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(2)),
            // b128 = sext b to i128
            InstrNode::new(Inst::Cast {
                op: trust_ir::CastOp::SExt,
                src_ty: Ty::I64,
                dst_ty: Ty::I128,
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(3)),
            // prod = a128 * b128 (i128)
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I128,
                lhs: ValueId::new(2),
                rhs: ValueId::new(3),
            })
            .with_result(ValueId::new(4)),
            // sh = 64 (i128)
            InstrNode::new(Inst::Const {
                ty: Ty::I128,
                value: trust_ir::Constant::Int(64),
            })
            .with_result(ValueId::new(5)),
            // hi = prod >>(arith) 64 (i128)
            InstrNode::new(Inst::BinOp {
                op: BinOp::AShr,
                ty: Ty::I128,
                lhs: ValueId::new(4),
                rhs: ValueId::new(5),
            })
            .with_result(ValueId::new(6)),
            // res = trunc hi to i64
            InstrNode::new(Inst::Cast {
                op: trust_ir::CastOp::Trunc,
                src_ty: Ty::I128,
                dst_ty: Ty::I64,
                operand: ValueId::new(6),
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(7)],
            }),
        ],
    }];
    module.add_function(func);
    module
}
