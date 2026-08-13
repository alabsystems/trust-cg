// trust-cg-codegen/tests/e2e_x86_64_recursion.rs - x86-64 recursion oracle
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Triple-oracle + differential testing of deep and mutual recursion on x86-64,
// stressing RSP 16-byte alignment and prologue/epilogue correctness across many
// nested frames:
//   - ackermann-lite (deeply nested self-recursion)
//   - even/odd (mutual recursion between two functions)
//   - recursive fibonacci (exponential call tree)
//
// These functions use only direct `Call`, `BinOp`, `ICmp`, `CondBr`, and
// `Const`, all of which the trust_ir interpreter models, so they are checked
// with the TRIPLE ORACLE (interpreter / trust-cg / clang). Host: x86-64 macOS.

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::interpreter::{InterpreterValue, interpret};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction,
    ICmpOp, Inst, InstrNode, Module as TrustIrModule, Ty, ValueId,
};

// =============================================================================
// Host gating + harness
// =============================================================================

fn x86_64_oracle_enabled() -> bool {
    if !cfg!(target_arch = "x86_64") {
        eprintln!("SKIP: x86-64 recursion oracle requires an x86-64 host");
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
    let dir = std::env::temp_dir().join(format!("trust_cg_x86_64_recursion_{}", test_name));
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

struct Case {
    key: String,
    args: Vec<i64>,
}

fn interp_i64(module: &TrustIrModule, func: &str, args: &[i64]) -> i64 {
    let interp_args: Vec<InterpreterValue> = args
        .iter()
        .map(|&a| InterpreterValue::Int(a as i128))
        .collect();
    let r = interpret(module, func, &interp_args)
        .unwrap_or_else(|e| panic!("interpreter failed on {}({:?}): {}", func, args, e));
    r.first()
        .expect("interpreter returned no value")
        .as_int()
        .expect("interpreter result not int") as i64
}

/// Triple oracle for an i64-returning function `func_name` driven by `c_source`
/// (using the `-DEXTERN_ONLY` split convention).
fn triple_oracle(
    test_name: &str,
    module: &TrustIrModule,
    func_name: &str,
    c_source: &str,
    cases: &[Case],
) -> Result<(), String> {
    let dir = make_test_dir(test_name);

    // Oracle 1: interpreter
    let mut interp: HashMap<String, i64> = HashMap::new();
    for c in cases {
        interp.insert(c.key.clone(), interp_i64(module, func_name, &c.args));
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
    if !trust_cg_run.status.success() {
        cleanup(&dir);
        return Err(format!(
            "trust-cg binary exited with {}",
            trust_cg_run.status.code().unwrap_or(-1)
        ));
    }
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
    if !clang_run.status.success() {
        cleanup(&dir);
        return Err(format!(
            "clang binary exited with {}",
            clang_run.status.code().unwrap_or(-1)
        ));
    }
    let clang = parse_int_results(&String::from_utf8_lossy(&clang_run.stdout));

    eprintln!("=== x86-64 recursion triple oracle: {} ===", test_name);
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

/// Build `fn _ackermann(m: i64, n: i64) -> i64` (classic Ackermann recursion).
///
///   ack(m, n) = n + 1                         if m == 0
///             = ack(m-1, 1)                   if n == 0
///             = ack(m-1, ack(m, n-1))         otherwise
///
/// Deeply nested self-recursion; stresses prologue/epilogue and RSP alignment
/// across many frames (a call with two formal args plus a nested-call return).
fn build_ackermann_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("ackermann_test");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let me = FuncId::new(0);
    let mut func = TrustIrFunction::new(me, "_ackermann", ft, BlockId::new(0));
    func.blocks = vec![
        // bb0: m, n. zero=0. if m == 0 -> bb1(base) else bb2
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::I64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(2),
                })
                .with_result(ValueId::new(3)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(3),
                    then_target: BlockId::new(1), // m == 0
                    then_args: vec![],
                    else_target: BlockId::new(2), // m != 0
                    else_args: vec![],
                }),
            ],
        },
        // bb1: return n + 1
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(4)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(1),
                    rhs: ValueId::new(4),
                })
                .with_result(ValueId::new(5)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(5)],
                }),
            ],
        },
        // bb2: m != 0. if n == 0 -> bb3 else bb4
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(6)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::I64,
                    lhs: ValueId::new(1),
                    rhs: ValueId::new(6),
                })
                .with_result(ValueId::new(7)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(7),
                    then_target: BlockId::new(3), // n == 0
                    then_args: vec![],
                    else_target: BlockId::new(4), // n != 0
                    else_args: vec![],
                }),
            ],
        },
        // bb3: n == 0 => return ack(m-1, 1)
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(8)),
                // m - 1
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Sub,
                    ty: Ty::I64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(8),
                })
                .with_result(ValueId::new(9)),
                // ack(m-1, 1)
                InstrNode::new(Inst::Call {
                    callee: me,
                    args: vec![ValueId::new(9), ValueId::new(8)],
                })
                .with_result(ValueId::new(10)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(10)],
                }),
            ],
        },
        // bb4: n != 0 => return ack(m-1, ack(m, n-1))
        TrustIrBlock {
            id: BlockId::new(4),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(11)),
                // n - 1
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Sub,
                    ty: Ty::I64,
                    lhs: ValueId::new(1),
                    rhs: ValueId::new(11),
                })
                .with_result(ValueId::new(12)),
                // inner = ack(m, n-1)
                InstrNode::new(Inst::Call {
                    callee: me,
                    args: vec![ValueId::new(0), ValueId::new(12)],
                })
                .with_result(ValueId::new(13)),
                // m - 1
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Sub,
                    ty: Ty::I64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(11),
                })
                .with_result(ValueId::new(14)),
                // ack(m-1, inner)
                InstrNode::new(Inst::Call {
                    callee: me,
                    args: vec![ValueId::new(14), ValueId::new(13)],
                })
                .with_result(ValueId::new(15)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(15)],
                }),
            ],
        },
    ];
    module.add_function(func);
    module
}

/// Build mutual recursion `_is_even` / `_is_odd` over non-negative n.
///
///   is_even(n) = 1            if n == 0
///              = is_odd(n-1)  otherwise
///   is_odd(n)  = 0            if n == 0
///              = is_even(n-1) otherwise
fn build_even_odd_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("even_odd_test");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let even_id = FuncId::new(0);
    let odd_id = FuncId::new(1);

    // Helper to build a parity function: base value when n==0, else call `other(n-1)`.
    let build = |id: FuncId, name: &str, base: i64, other: FuncId| {
        let mut f = TrustIrFunction::new(id, name, ft, BlockId::new(0));
        f.blocks = vec![
            // bb0: n. if n == 0 -> bb1(base) else bb2
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
                        op: ICmpOp::Eq,
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
            // bb1: return base
            TrustIrBlock {
                id: BlockId::new(1),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(base as i128),
                    })
                    .with_result(ValueId::new(3)),
                    InstrNode::new(Inst::Return {
                        values: vec![ValueId::new(3)],
                    }),
                ],
            },
            // bb2: return other(n-1)
            TrustIrBlock {
                id: BlockId::new(2),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(1),
                    })
                    .with_result(ValueId::new(4)),
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Sub,
                        ty: Ty::I64,
                        lhs: ValueId::new(0),
                        rhs: ValueId::new(4),
                    })
                    .with_result(ValueId::new(5)),
                    InstrNode::new(Inst::Call {
                        callee: other,
                        args: vec![ValueId::new(5)],
                    })
                    .with_result(ValueId::new(6)),
                    InstrNode::new(Inst::Return {
                        values: vec![ValueId::new(6)],
                    }),
                ],
            },
        ];
        f
    };

    module.add_function(build(even_id, "_is_even", 1, odd_id));
    module.add_function(build(odd_id, "_is_odd", 0, even_id));
    module
}

/// Build `fn _fib_rec(n: i64) -> i64` (naive recursive fibonacci).
///
///   fib(n) = n              if n < 2
///          = fib(n-1) + fib(n-2)
fn build_fib_rec_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("fib_rec_test");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let me = FuncId::new(0);
    let mut func = TrustIrFunction::new(me, "_fib_rec", ft, BlockId::new(0));
    func.blocks = vec![
        // bb0: n. two=2. if n < 2 -> bb1(return n) else bb2
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(2),
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
        // bb1: return n
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            })],
        },
        // bb2: return fib(n-1) + fib(n-2)
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(3)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(2),
                })
                .with_result(ValueId::new(4)),
                // n-1
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Sub,
                    ty: Ty::I64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(3),
                })
                .with_result(ValueId::new(5)),
                // n-2
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Sub,
                    ty: Ty::I64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(4),
                })
                .with_result(ValueId::new(6)),
                // fib(n-1)
                InstrNode::new(Inst::Call {
                    callee: me,
                    args: vec![ValueId::new(5)],
                })
                .with_result(ValueId::new(7)),
                // fib(n-2)
                InstrNode::new(Inst::Call {
                    callee: me,
                    args: vec![ValueId::new(6)],
                })
                .with_result(ValueId::new(8)),
                // sum
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(7),
                    rhs: ValueId::new(8),
                })
                .with_result(ValueId::new(9)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(9)],
                }),
            ],
        },
    ];
    module.add_function(func);
    module
}

// =============================================================================
// Tests
// =============================================================================

#[test]
fn test_x86_64_recursion_ackermann() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_ackermann_module();
    let c_source = r#"
#include <stdio.h>
#ifndef EXTERN_ONLY
long _ackermann(long m, long n) {
    if (m == 0) return n + 1;
    if (n == 0) return _ackermann(m - 1, 1);
    return _ackermann(m - 1, _ackermann(m, n - 1));
}
#endif
#ifdef EXTERN_ONLY
extern long _ackermann(long m, long n);
#endif
int main(void) {
    printf("a(0,0)=%ld\n", _ackermann(0, 0));
    printf("a(1,1)=%ld\n", _ackermann(1, 1));
    printf("a(2,2)=%ld\n", _ackermann(2, 2));
    printf("a(2,3)=%ld\n", _ackermann(2, 3));
    printf("a(3,3)=%ld\n", _ackermann(3, 3));
    printf("a(3,4)=%ld\n", _ackermann(3, 4));
    return 0;
}
"#;
    let cases = vec![
        Case {
            key: "a(0,0)".into(),
            args: vec![0, 0],
        },
        Case {
            key: "a(1,1)".into(),
            args: vec![1, 1],
        },
        Case {
            key: "a(2,2)".into(),
            args: vec![2, 2],
        },
        Case {
            key: "a(2,3)".into(),
            args: vec![2, 3],
        },
        Case {
            key: "a(3,3)".into(),
            args: vec![3, 3],
        },
        Case {
            key: "a(3,4)".into(),
            args: vec![3, 4],
        },
    ];
    let r = triple_oracle("ackermann", &module, "_ackermann", c_source, &cases);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_recursion_even_odd() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_even_odd_module();
    let c_source = r#"
#include <stdio.h>
#ifndef EXTERN_ONLY
long _is_odd(long n);
long _is_even(long n) { if (n == 0) return 1; return _is_odd(n - 1); }
long _is_odd(long n)  { if (n == 0) return 0; return _is_even(n - 1); }
#endif
#ifdef EXTERN_ONLY
extern long _is_even(long n);
#endif
int main(void) {
    printf("e(0)=%ld\n", _is_even(0));
    printf("e(1)=%ld\n", _is_even(1));
    printf("e(2)=%ld\n", _is_even(2));
    printf("e(7)=%ld\n", _is_even(7));
    printf("e(20)=%ld\n", _is_even(20));
    printf("e(101)=%ld\n", _is_even(101));
    return 0;
}
"#;
    let cases = vec![
        Case {
            key: "e(0)".into(),
            args: vec![0],
        },
        Case {
            key: "e(1)".into(),
            args: vec![1],
        },
        Case {
            key: "e(2)".into(),
            args: vec![2],
        },
        Case {
            key: "e(7)".into(),
            args: vec![7],
        },
        Case {
            key: "e(20)".into(),
            args: vec![20],
        },
        Case {
            key: "e(101)".into(),
            args: vec![101],
        },
    ];
    let r = triple_oracle("even_odd", &module, "_is_even", c_source, &cases);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_recursion_fib() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_fib_rec_module();
    let c_source = r#"
#include <stdio.h>
#ifndef EXTERN_ONLY
long _fib_rec(long n) {
    if (n < 2) return n;
    return _fib_rec(n - 1) + _fib_rec(n - 2);
}
#endif
#ifdef EXTERN_ONLY
extern long _fib_rec(long n);
#endif
int main(void) {
    printf("f(0)=%ld\n", _fib_rec(0));
    printf("f(1)=%ld\n", _fib_rec(1));
    printf("f(5)=%ld\n", _fib_rec(5));
    printf("f(10)=%ld\n", _fib_rec(10));
    printf("f(15)=%ld\n", _fib_rec(15));
    printf("f(22)=%ld\n", _fib_rec(22));
    return 0;
}
"#;
    // Capped at fib(22) so the trust_ir interpreter (1M-step fuel budget) does
    // not exhaust fuel on the naive O(phi^n) call tree; the trust-cg/clang
    // recursion itself is unaffected by this bound.
    let cases = vec![
        Case {
            key: "f(0)".into(),
            args: vec![0],
        },
        Case {
            key: "f(1)".into(),
            args: vec![1],
        },
        Case {
            key: "f(5)".into(),
            args: vec![5],
        },
        Case {
            key: "f(10)".into(),
            args: vec![10],
        },
        Case {
            key: "f(15)".into(),
            args: vec![15],
        },
        Case {
            key: "f(22)".into(),
            args: vec![22],
        },
    ];
    let r = triple_oracle("fib_rec", &module, "_fib_rec", c_source, &cases);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}
