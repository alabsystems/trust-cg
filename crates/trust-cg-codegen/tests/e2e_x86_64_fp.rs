// trust-cg-codegen/tests/e2e_x86_64_fp.rs - x86-64 floating-point oracle
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Differential + triple-oracle testing of x86-64 floating-point lowering:
//   - f64 and f32 arithmetic chains (FAdd/FSub/FMul/FDiv)
//   - all FCmp predicates including NaN/unordered behaviour
//   - int<->float conversions (FcvtToInt = FPToSI, FcvtFromInt = SIToFP,
//     FPExt f32->f64, FPTrunc f64->f32)
//
// Value-returning FP functions print via C printf and are checked
// DIFFERENTIALLY (trust-cg vs clang, exact string match).
//
// Integer-returning FP functions (compare predicates, float->int conversions)
// are checked with the TRIPLE ORACLE (trust_ir interpreter / trust-cg / clang),
// since the interpreter models FCmp and Cast (FPToSI/SIToFP/FPExt/FPTrunc) and
// returns exact integers.
//
// Host: x86-64 macOS.

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::interpreter::{InterpreterValue, interpret};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, CastOp, Constant, FCmpOp, FuncId, FuncTy,
    Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, Ty, ValueId,
};

// =============================================================================
// Host gating + harness
// =============================================================================

fn x86_64_oracle_enabled() -> bool {
    if !cfg!(target_arch = "x86_64") {
        eprintln!("SKIP: x86-64 FP oracle requires an x86-64 host");
        return false;
    }
    if !has_cc() {
        eprintln!("SKIP: cc not available");
        return false;
    }
    true
}

fn has_cc() -> bool {
    Command::new("cc")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

fn make_test_dir(test_name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("trust_cg_x86_64_fp_{}", test_name));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");
    dir
}

fn cleanup(dir: &Path) {
    let _ = fs::remove_dir_all(dir);
}

fn compile_trust_ir_module_x86_64(module: &TrustIrModule) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        target: Target::X86_64,
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
    let result = compiler
        .compile(module)
        .expect("x86-64 trust-cg compilation should succeed");
    assert!(
        !result.object_code.is_empty(),
        "trust-cg must produce non-empty object code"
    );
    result.object_code
}

/// Differential: trust-cg vs clang, exact stdout string equality.
fn differential_test(
    test_name: &str,
    module: &TrustIrModule,
    c_source: &str,
) -> Result<(), String> {
    let dir = make_test_dir(test_name);

    let obj_bytes = compile_trust_ir_module_x86_64(module);
    let obj_path = dir.join("trust_cg.o");
    fs::write(&obj_path, &obj_bytes).map_err(|e| format!("write .o: {}", e))?;
    let driver_path = dir.join("driver.c");
    fs::write(&driver_path, c_source).map_err(|e| format!("write driver.c: {}", e))?;

    let trust_cg_bin = dir.join("test_trust_cg");
    let trust_cg_link = Command::new("cc")
        .args(if cfg!(target_os = "macos") {
            &["-arch", "x86_64"][..]
        } else {
            &[][..]
        })
        .args([
            "-DEXTERN_ONLY",
            "-O0",
            "-o",
            trust_cg_bin.to_str().unwrap(),
            driver_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
        ])
        .output()
        .map_err(|e| format!("trust-cg link: {}", e))?;
    if !trust_cg_link.status.success() {
        let stderr = String::from_utf8_lossy(&trust_cg_link.stderr);
        cleanup(&dir);
        return Err(format!("trust-cg link failed: {}", stderr));
    }

    let trust_cg_run = Command::new(&trust_cg_bin)
        .output()
        .map_err(|e| format!("run trust-cg binary: {}", e))?;
    let trust_cg_stdout = String::from_utf8_lossy(&trust_cg_run.stdout).to_string();
    let trust_cg_exit = trust_cg_run.status.code().unwrap_or(-1);

    let clang_bin = dir.join("test_clang");
    let clang_compile = Command::new("cc")
        .args(if cfg!(target_os = "macos") {
            &["-arch", "x86_64"][..]
        } else {
            &[][..]
        })
        .args([
            "-O0",
            "-o",
            clang_bin.to_str().unwrap(),
            driver_path.to_str().unwrap(),
        ])
        .output()
        .map_err(|e| format!("clang compile: {}", e))?;
    if !clang_compile.status.success() {
        let stderr = String::from_utf8_lossy(&clang_compile.stderr);
        cleanup(&dir);
        return Err(format!("clang reference compile failed: {}", stderr));
    }

    let clang_run = Command::new(&clang_bin)
        .output()
        .map_err(|e| format!("run clang binary: {}", e))?;
    let clang_stdout = String::from_utf8_lossy(&clang_run.stdout).to_string();
    let clang_exit = clang_run.status.code().unwrap_or(-1);

    eprintln!("=== x86-64 FP differential: {} ===", test_name);
    eprintln!("  trust-cg stdout: {}", trust_cg_stdout.trim());
    eprintln!("  clang    stdout: {}", clang_stdout.trim());

    if trust_cg_stdout != clang_stdout {
        let otool = Command::new("otool")
            .args(["-tv", obj_path.to_str().unwrap()])
            .output()
            .ok();
        let disasm = otool
            .map(|o| String::from_utf8_lossy(&o.stdout).to_string())
            .unwrap_or_default();
        cleanup(&dir);
        return Err(format!(
            "OUTPUT MISMATCH!\n  trust-cg: {}\n  clang:    {}\n  trust-cg disasm:\n{}",
            trust_cg_stdout.trim(),
            clang_stdout.trim(),
            disasm
        ));
    }
    if trust_cg_exit != clang_exit {
        cleanup(&dir);
        return Err(format!(
            "EXIT MISMATCH! trust-cg={} clang={}",
            trust_cg_exit, clang_exit
        ));
    }
    if clang_exit != 0 {
        cleanup(&dir);
        return Err(format!("both binaries exited non-zero ({})", clang_exit));
    }

    cleanup(&dir);
    Ok(())
}

/// Parse "key=value" integer lines from stdout.
fn parse_int_results(stdout: &str) -> HashMap<String, i64> {
    let mut m = HashMap::new();
    for line in stdout.lines() {
        if let Some((k, v)) = line.trim().split_once('=')
            && let Ok(n) = v.trim().parse::<i64>()
        {
            m.insert(k.trim().to_string(), n);
        }
    }
    m
}

/// A triple-oracle case for an INTEGER-returning function.
struct IntCase {
    key: String,
    /// Interpreter args (Int or Float) for this case.
    args: Vec<InterpreterValue>,
}

/// Triple-oracle harness for integer-returning FP functions: compares the
/// trust_ir interpreter, the trust-cg compiled binary, and clang.
///
/// `c_source` uses the `-DEXTERN_ONLY` split convention.
fn triple_oracle_int(
    test_name: &str,
    module: &TrustIrModule,
    func_name: &str,
    c_source: &str,
    cases: &[IntCase],
) -> Result<(), String> {
    let dir = make_test_dir(test_name);

    // Oracle 1: interpreter
    let mut interp: HashMap<String, i64> = HashMap::new();
    for c in cases {
        let r = interpret(module, func_name, &c.args)
            .map_err(|e| format!("interpreter failed on {}: {}", c.key, e))?;
        let v = r
            .first()
            .ok_or_else(|| format!("interpreter returned no value for {}", c.key))?
            .as_int()
            .map_err(|e| format!("interpreter result not int for {}: {}", c.key, e))?;
        interp.insert(c.key.clone(), v as i64);
    }

    // Oracle 2: trust-cg
    let obj_bytes = compile_trust_ir_module_x86_64(module);
    let obj_path = dir.join("trust_cg.o");
    fs::write(&obj_path, &obj_bytes).map_err(|e| format!("write .o: {}", e))?;
    let driver_path = dir.join("driver.c");
    fs::write(&driver_path, c_source).map_err(|e| format!("write driver.c: {}", e))?;

    let trust_cg_bin = dir.join("test_trust_cg");
    let trust_cg_link = Command::new("cc")
        .args(if cfg!(target_os = "macos") {
            &["-arch", "x86_64"][..]
        } else {
            &[][..]
        })
        .args([
            "-DEXTERN_ONLY",
            "-O0",
            "-o",
            trust_cg_bin.to_str().unwrap(),
            driver_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
        ])
        .output()
        .map_err(|e| format!("trust-cg link: {}", e))?;
    if !trust_cg_link.status.success() {
        let stderr = String::from_utf8_lossy(&trust_cg_link.stderr);
        cleanup(&dir);
        return Err(format!("trust-cg link failed: {}", stderr));
    }
    let trust_cg_run = Command::new(&trust_cg_bin)
        .output()
        .map_err(|e| format!("run trust-cg binary: {}", e))?;
    let trust_cg = parse_int_results(&String::from_utf8_lossy(&trust_cg_run.stdout));

    // Oracle 3: clang
    let clang_bin = dir.join("test_clang");
    let clang_compile = Command::new("cc")
        .args(if cfg!(target_os = "macos") {
            &["-arch", "x86_64"][..]
        } else {
            &[][..]
        })
        .args([
            "-O0",
            "-o",
            clang_bin.to_str().unwrap(),
            driver_path.to_str().unwrap(),
        ])
        .output()
        .map_err(|e| format!("clang compile: {}", e))?;
    if !clang_compile.status.success() {
        let stderr = String::from_utf8_lossy(&clang_compile.stderr);
        cleanup(&dir);
        return Err(format!("clang compile failed: {}", stderr));
    }
    let clang_run = Command::new(&clang_bin)
        .output()
        .map_err(|e| format!("run clang binary: {}", e))?;
    let clang = parse_int_results(&String::from_utf8_lossy(&clang_run.stdout));

    eprintln!("=== x86-64 FP triple oracle: {} ===", test_name);
    eprintln!("  interp:   {:?}", interp);
    eprintln!("  trust-cg: {:?}", trust_cg);
    eprintln!("  clang:    {:?}", clang);

    let mut mismatches = Vec::new();
    for c in cases {
        match (interp.get(&c.key), trust_cg.get(&c.key), clang.get(&c.key)) {
            (Some(&i), Some(&l), Some(&k)) => {
                if i != l || i != k {
                    mismatches.push(format!(
                        "  {}: interp={}, trust-cg={}, clang={}",
                        c.key, i, l, k
                    ));
                }
            }
            (i, l, k) => mismatches.push(format!(
                "  {}: MISSING interp={:?} trust-cg={:?} clang={:?}",
                c.key, i, l, k
            )),
        }
    }

    cleanup(&dir);
    if mismatches.is_empty() {
        eprintln!("  ALL THREE ORACLES AGREE");
        Ok(())
    } else {
        Err(format!(
            "TRIPLE ORACLE MISMATCH {}:\n{}",
            test_name,
            mismatches.join("\n")
        ))
    }
}

// =============================================================================
// trust_ir builders
// =============================================================================

/// `f64 _f64_chain(a, b, c, d) -> ((a + b) * c) - (d / b)`
fn build_f64_chain_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::F64; 4],
        returns: vec![Ty::F64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_f64_chain", ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::F64),
            (ValueId::new(1), Ty::F64),
            (ValueId::new(2), Ty::F64),
            (ValueId::new(3), Ty::F64),
        ],
        body: vec![
            // t0 = a + b
            InstrNode::new(Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::F64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(4)),
            // t1 = t0 * c
            InstrNode::new(Inst::BinOp {
                op: BinOp::FMul,
                ty: Ty::F64,
                lhs: ValueId::new(4),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(5)),
            // t2 = d / b
            InstrNode::new(Inst::BinOp {
                op: BinOp::FDiv,
                ty: Ty::F64,
                lhs: ValueId::new(3),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(6)),
            // t3 = t1 - t2
            InstrNode::new(Inst::BinOp {
                op: BinOp::FSub,
                ty: Ty::F64,
                lhs: ValueId::new(5),
                rhs: ValueId::new(6),
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

/// `f32 _f32_chain(a, b, c, d) -> ((a + b) * c) - (d / b)`
fn build_f32_chain_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::F32; 4],
        returns: vec![Ty::F32],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_f32_chain", ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::F32),
            (ValueId::new(1), Ty::F32),
            (ValueId::new(2), Ty::F32),
            (ValueId::new(3), Ty::F32),
        ],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::F32,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::FMul,
                ty: Ty::F32,
                lhs: ValueId::new(4),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::FDiv,
                ty: Ty::F32,
                lhs: ValueId::new(3),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::FSub,
                ty: Ty::F32,
                lhs: ValueId::new(5),
                rhs: ValueId::new(6),
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

/// `i64 _fcmp(a: f64, b: f64) -> (a PRED b) ? 1 : 0` for a given predicate.
fn build_fcmp_module(name: &str, pred: FCmpOp) -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::F64, Ty::F64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), name, ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::F64), (ValueId::new(1), Ty::F64)],
        body: vec![
            InstrNode::new(Inst::FCmp {
                op: pred,
                ty: Ty::F64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            // one / zero constants for select
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Select {
                ty: Ty::I64,
                cond: ValueId::new(2),
                then_val: ValueId::new(3),
                else_val: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(5)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

/// `i64 _fptosi(x: f64) -> (i64) x`  (truncation toward zero)
fn build_fptosi_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::F64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_fptosi", ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::F64)],
        body: vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::FPToSI,
                src_ty: Ty::F64,
                dst_ty: Ty::I64,
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

/// `f64 _sitofp(x: i64) -> (f64) x`
fn build_sitofp_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::F64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_sitofp", ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::SIToFP,
                src_ty: Ty::I64,
                dst_ty: Ty::F64,
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

/// `i64 _round_trip(x: f32) -> (i64)((f64)x)`  (FPExt f32->f64 then FPToSI)
fn build_fpext_fptosi_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::F32],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_fpext_fptosi", ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::F32)],
        body: vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::FPExt,
                src_ty: Ty::F32,
                dst_ty: Ty::F64,
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Cast {
                op: CastOp::FPToSI,
                src_ty: Ty::F64,
                dst_ty: Ty::I64,
                operand: ValueId::new(1),
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

/// `f32 _fptrunc(x: f64) -> (f32) x`  (FPTrunc, returned as f32)
fn build_fptrunc_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::F64],
        returns: vec![Ty::F32],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_fptrunc", ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::F64)],
        body: vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::FPTrunc,
                src_ty: Ty::F64,
                dst_ty: Ty::F32,
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

// =============================================================================
// Value-returning FP tests (differential vs clang)
// =============================================================================

#[test]
fn test_x86_64_fp_f64_chain() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_f64_chain_module();
    let c_source = r#"
#include <stdio.h>
#ifndef EXTERN_ONLY
double _f64_chain(double a, double b, double c, double d) {
    return ((a + b) * c) - (d / b);
}
#endif
#ifdef EXTERN_ONLY
extern double _f64_chain(double a, double b, double c, double d);
#endif
int main(void) {
    printf("c(1.5,2.0,3.0,8.0)=%.10f\n", _f64_chain(1.5, 2.0, 3.0, 8.0));
    printf("c(-1.25,0.5,4.0,2.0)=%.10f\n", _f64_chain(-1.25, 0.5, 4.0, 2.0));
    printf("c(100.0,4.0,0.25,16.0)=%.10f\n", _f64_chain(100.0, 4.0, 0.25, 16.0));
    printf("c(0.0,1.0,0.0,0.0)=%.10f\n", _f64_chain(0.0, 1.0, 0.0, 0.0));
    return 0;
}
"#;
    let r = differential_test("fp_f64_chain", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_fp_f32_chain() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_f32_chain_module();
    let c_source = r#"
#include <stdio.h>
#ifndef EXTERN_ONLY
float _f32_chain(float a, float b, float c, float d) {
    return ((a + b) * c) - (d / b);
}
#endif
#ifdef EXTERN_ONLY
extern float _f32_chain(float a, float b, float c, float d);
#endif
int main(void) {
    printf("c(1.5,2.0,3.0,8.0)=%.6f\n", _f32_chain(1.5f, 2.0f, 3.0f, 8.0f));
    printf("c(-1.25,0.5,4.0,2.0)=%.6f\n", _f32_chain(-1.25f, 0.5f, 4.0f, 2.0f));
    printf("c(100.0,4.0,0.25,16.0)=%.6f\n", _f32_chain(100.0f, 4.0f, 0.25f, 16.0f));
    printf("c(0.0,1.0,0.0,0.0)=%.6f\n", _f32_chain(0.0f, 1.0f, 0.0f, 0.0f));
    return 0;
}
"#;
    let r = differential_test("fp_f32_chain", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_fp_sitofp_value() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_sitofp_module();
    let c_source = r#"
#include <stdio.h>
#ifndef EXTERN_ONLY
double _sitofp(long x) { return (double) x; }
#endif
#ifdef EXTERN_ONLY
extern double _sitofp(long x);
#endif
int main(void) {
    printf("s(0)=%.10f\n", _sitofp(0));
    printf("s(42)=%.10f\n", _sitofp(42));
    printf("s(-7)=%.10f\n", _sitofp(-7));
    printf("s(1000000)=%.10f\n", _sitofp(1000000));
    printf("s(-123456789)=%.10f\n", _sitofp(-123456789));
    return 0;
}
"#;
    let r = differential_test("fp_sitofp_value", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_fp_fptrunc_value() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_fptrunc_module();
    let c_source = r#"
#include <stdio.h>
#ifndef EXTERN_ONLY
float _fptrunc(double x) { return (float) x; }
#endif
#ifdef EXTERN_ONLY
extern float _fptrunc(double x);
#endif
int main(void) {
    printf("t(1.5)=%.6f\n", _fptrunc(1.5));
    printf("t(3.14159265358979)=%.6f\n", _fptrunc(3.14159265358979));
    printf("t(-2.718281828)=%.6f\n", _fptrunc(-2.718281828));
    printf("t(1e20)=%.6e\n", (double) _fptrunc(1e20));
    return 0;
}
"#;
    let r = differential_test("fp_fptrunc_value", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

// =============================================================================
// Integer-returning FP tests (triple oracle: interp / trust-cg / clang)
// =============================================================================

/// Build the standard FCmp driver for predicate `c_pred` (a C boolean expr).
fn fcmp_driver(func: &str, c_pred: &str) -> String {
    format!(
        r#"
#include <stdio.h>
#ifndef EXTERN_ONLY
long {func}(double a, double b) {{ return ({c_pred}) ? 1 : 0; }}
#endif
#ifdef EXTERN_ONLY
extern long {func}(double a, double b);
#endif
int main(void) {{
    double nan = 0.0/0.0;
    printf("lt=%ld\n", {func}(1.0, 2.0));
    printf("eq=%ld\n", {func}(2.0, 2.0));
    printf("gt=%ld\n", {func}(3.0, 2.0));
    printf("neg=%ld\n", {func}(-1.0, -2.0));
    printf("nan_a=%ld\n", {func}(nan, 1.0));
    printf("nan_b=%ld\n", {func}(1.0, nan));
    printf("nan_both=%ld\n", {func}(nan, nan));
    return 0;
}}
"#
    )
}

fn fcmp_cases() -> Vec<IntCase> {
    let nan = f64::NAN;
    vec![
        IntCase {
            key: "lt".into(),
            args: vec![InterpreterValue::Float(1.0), InterpreterValue::Float(2.0)],
        },
        IntCase {
            key: "eq".into(),
            args: vec![InterpreterValue::Float(2.0), InterpreterValue::Float(2.0)],
        },
        IntCase {
            key: "gt".into(),
            args: vec![InterpreterValue::Float(3.0), InterpreterValue::Float(2.0)],
        },
        IntCase {
            key: "neg".into(),
            args: vec![InterpreterValue::Float(-1.0), InterpreterValue::Float(-2.0)],
        },
        IntCase {
            key: "nan_a".into(),
            args: vec![InterpreterValue::Float(nan), InterpreterValue::Float(1.0)],
        },
        IntCase {
            key: "nan_b".into(),
            args: vec![InterpreterValue::Float(1.0), InterpreterValue::Float(nan)],
        },
        IntCase {
            key: "nan_both".into(),
            args: vec![InterpreterValue::Float(nan), InterpreterValue::Float(nan)],
        },
    ]
}

#[test]
fn test_x86_64_fcmp_oeq() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_fcmp_module("_fcmp", FCmpOp::OEq);
    let r = triple_oracle_int(
        "fcmp_oeq",
        &module,
        "_fcmp",
        &fcmp_driver("_fcmp", "a == b"),
        &fcmp_cases(),
    );
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_fcmp_one() {
    if !x86_64_oracle_enabled() {
        return;
    }
    // ONE: ordered-and-not-equal => clang `!isunordered(a,b) && a != b`
    // (false when either operand is NaN).
    //
    // DIFFERENTIAL-ONLY (trust-cg vs clang). The triple oracle is NOT usable
    // for ONE because the trust_ir interpreter's `eval_fcmp` implements
    // `ONe => lhs != rhs`, and Rust's `f64 != f64` returns true when either
    // operand is NaN — so the interpreter reports ONE=1 for NaN operands,
    // disagreeing with correct IEEE-754 ordered-not-equal semantics. trust-cg
    // and clang both correctly produce 0 for NaN operands; the divergence is a
    // KNOWN interpreter quirk, not a backend miscompile. See report.
    let module = build_fcmp_module("_fcmp", FCmpOp::ONe);
    let r = differential_test(
        "fcmp_one",
        &module,
        &fcmp_driver("_fcmp", "!__builtin_isunordered(a, b) && a != b"),
    );
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_fcmp_olt() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_fcmp_module("_fcmp", FCmpOp::OLt);
    let r = triple_oracle_int(
        "fcmp_olt",
        &module,
        "_fcmp",
        &fcmp_driver("_fcmp", "a < b"),
        &fcmp_cases(),
    );
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_fcmp_ole() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_fcmp_module("_fcmp", FCmpOp::OLe);
    let r = triple_oracle_int(
        "fcmp_ole",
        &module,
        "_fcmp",
        &fcmp_driver("_fcmp", "a <= b"),
        &fcmp_cases(),
    );
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_fcmp_ogt() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_fcmp_module("_fcmp", FCmpOp::OGt);
    let r = triple_oracle_int(
        "fcmp_ogt",
        &module,
        "_fcmp",
        &fcmp_driver("_fcmp", "a > b"),
        &fcmp_cases(),
    );
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_fcmp_oge() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_fcmp_module("_fcmp", FCmpOp::OGe);
    let r = triple_oracle_int(
        "fcmp_oge",
        &module,
        "_fcmp",
        &fcmp_driver("_fcmp", "a >= b"),
        &fcmp_cases(),
    );
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_fcmp_une() {
    if !x86_64_oracle_enabled() {
        return;
    }
    // UNE: unordered or not equal => C `a != b` (true when unordered).
    let module = build_fcmp_module("_fcmp", FCmpOp::UNe);
    let r = triple_oracle_int(
        "fcmp_une",
        &module,
        "_fcmp",
        &fcmp_driver("_fcmp", "a != b"),
        &fcmp_cases(),
    );
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_fcmp_ueq() {
    if !x86_64_oracle_enabled() {
        return;
    }
    // UEQ: unordered or equal => C `isunordered(a,b) || a == b`.
    let module = build_fcmp_module("_fcmp", FCmpOp::UEq);
    let r = triple_oracle_int(
        "fcmp_ueq",
        &module,
        "_fcmp",
        &fcmp_driver("_fcmp", "__builtin_isunordered(a, b) || a == b"),
        &fcmp_cases(),
    );
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_fcmp_ult() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_fcmp_module("_fcmp", FCmpOp::ULt);
    let r = triple_oracle_int(
        "fcmp_ult",
        &module,
        "_fcmp",
        &fcmp_driver("_fcmp", "__builtin_isunordered(a, b) || a < b"),
        &fcmp_cases(),
    );
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_fcmp_ugt() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_fcmp_module("_fcmp", FCmpOp::UGt);
    let r = triple_oracle_int(
        "fcmp_ugt",
        &module,
        "_fcmp",
        &fcmp_driver("_fcmp", "__builtin_isunordered(a, b) || a > b"),
        &fcmp_cases(),
    );
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_fptosi_triple() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_fptosi_module();
    let c_source = r#"
#include <stdio.h>
#ifndef EXTERN_ONLY
long _fptosi(double x) { return (long) x; }
#endif
#ifdef EXTERN_ONLY
extern long _fptosi(double x);
#endif
int main(void) {
    printf("a=%ld\n", _fptosi(0.0));
    printf("b=%ld\n", _fptosi(42.9));
    printf("c=%ld\n", _fptosi(-42.9));
    printf("d=%ld\n", _fptosi(1000000.5));
    printf("e=%ld\n", _fptosi(-7.0));
    printf("f=%ld\n", _fptosi(2.99999));
    return 0;
}
"#;
    let cases = vec![
        IntCase {
            key: "a".into(),
            args: vec![InterpreterValue::Float(0.0)],
        },
        IntCase {
            key: "b".into(),
            args: vec![InterpreterValue::Float(42.9)],
        },
        IntCase {
            key: "c".into(),
            args: vec![InterpreterValue::Float(-42.9)],
        },
        IntCase {
            key: "d".into(),
            args: vec![InterpreterValue::Float(1000000.5)],
        },
        IntCase {
            key: "e".into(),
            args: vec![InterpreterValue::Float(-7.0)],
        },
        IntCase {
            key: "f".into(),
            args: vec![InterpreterValue::Float(2.99999)],
        },
    ];
    let r = triple_oracle_int("fptosi", &module, "_fptosi", c_source, &cases);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_fpext_fptosi_triple() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_fpext_fptosi_module();
    let c_source = r#"
#include <stdio.h>
#ifndef EXTERN_ONLY
long _fpext_fptosi(float x) { return (long)(double) x; }
#endif
#ifdef EXTERN_ONLY
extern long _fpext_fptosi(float x);
#endif
int main(void) {
    printf("a=%ld\n", _fpext_fptosi(0.0f));
    printf("b=%ld\n", _fpext_fptosi(42.5f));
    printf("c=%ld\n", _fpext_fptosi(-99.9f));
    printf("d=%ld\n", _fpext_fptosi(12345.0f));
    return 0;
}
"#;
    let cases = vec![
        IntCase {
            key: "a".into(),
            args: vec![InterpreterValue::Float(0.0)],
        },
        IntCase {
            key: "b".into(),
            args: vec![InterpreterValue::Float(42.5)],
        },
        IntCase {
            key: "c".into(),
            args: vec![InterpreterValue::Float(-99.9f32 as f64)],
        },
        IntCase {
            key: "d".into(),
            args: vec![InterpreterValue::Float(12345.0)],
        },
    ];
    let r = triple_oracle_int("fpext_fptosi", &module, "_fpext_fptosi", c_source, &cases);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}
