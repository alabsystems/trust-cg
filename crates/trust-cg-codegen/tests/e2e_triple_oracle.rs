// trust-cg-codegen/tests/e2e_triple_oracle.rs - Triple oracle validation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Three-way differential testing: every function is evaluated by THREE
// independent truth sources and all three must agree:
//
//   1. trust_ir interpreter — evaluates IR directly, no codegen
//   2. Trust Codegen — our compiler: trust_ir -> ISel -> RegAlloc -> AArch64 -> Mach-O
//   3. clang — system C compiler, known correct
//
// If any oracle disagrees, the test fails with a detailed mismatch report.
//
// Architecture: AArch64 (Apple Silicon) only. Skipped on other targets.
//
// Part of #301 — Triple oracle test harness.

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::interpreter::{InterpreterValue, interpret};
use trust_cg_codegen::pipeline::OptLevel;

// trust_ir imports
use trust_ir::{BinOp, ICmpOp, Inst, InstrNode};
use trust_ir::{
    Block as TrustIrBlock, Constant, FuncTy, Function as TrustIrFunction, Module as TrustIrModule,
    Ty,
};
use trust_ir::{BlockId, FuncId, ValueId};

// =============================================================================
// Test infrastructure
// =============================================================================

/// Returns true if we are running on AArch64 (Apple Silicon).
fn is_aarch64() -> bool {
    cfg!(target_arch = "aarch64")
}

/// Returns true if the system C compiler is available.
fn has_cc() -> bool {
    Command::new("cc")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// Create a temporary directory for test artifacts.
fn make_test_dir(test_name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("trust_cg_triple_oracle_{}", test_name));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("Failed to create test directory");
    dir
}

/// Cleanup a test directory.
fn cleanup(dir: &Path) {
    let _ = fs::remove_dir_all(dir);
}

/// Compile a trust_ir module through the Trust Codegen pipeline, returning raw .o bytes.
fn compile_trust_ir_module(module: &TrustIrModule) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(module)
        .expect("Trust Codegen compilation should succeed");
    assert!(
        !result.object_code.is_empty(),
        "Trust Codegen must produce non-empty object code"
    );
    result.object_code
}

/// Parse "key=value" lines from stdout into a map.
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

/// Run the interpreter for a given function with i64 arguments, return i64 result.
fn interp_i64(module: &TrustIrModule, func_name: &str, args: &[i64]) -> i64 {
    let interp_args: Vec<InterpreterValue> = args
        .iter()
        .map(|&a| InterpreterValue::Int(a as i128))
        .collect();
    let result = interpret(module, func_name, &interp_args)
        .unwrap_or_else(|e| panic!("interpreter failed on {}({:?}): {}", func_name, args, e));
    assert_eq!(result.len(), 1, "expected single return value");
    result[0].as_int().expect("expected Int result") as i64
}

// =============================================================================
// Core triple oracle harness
// =============================================================================

/// A single test case: function input(s) and the key used in stdout.
struct TestCase {
    /// Key used in the driver's printf (e.g., "fib(10)")
    key: String,
    /// Arguments to the function
    args: Vec<i64>,
}

// =============================================================================
// trust_ir module builders
// =============================================================================

/// Build trust_ir for: `fn _fibonacci(n: i64) -> i64`
///
/// Iterative fibonacci:
///   bb0 (entry): if n <= 1 return n
///   bb1 (ret_n): return n
///   bb2 (loop_init): a=0, b=1, i=2, br -> bb3
///   bb3 (loop): a+b -> tmp, i+1 -> new_i, if new_i <= n continue else exit
///   bb4 (exit): return result
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
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
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
        // bb3 (loop): params(a, b, i)
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
                    lhs: ValueId::new(20),
                    rhs: ValueId::new(21),
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
                    lhs: ValueId::new(22),
                    rhs: ValueId::new(24),
                })
                .with_result(ValueId::new(25)),
                // cmp new_i <= n
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    lhs: ValueId::new(25),
                    rhs: ValueId::new(0), // n from entry
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

/// Build trust_ir for: `fn _gcd(a: i64, b: i64) -> i64`
///
/// Euclidean algorithm with SRem:
///   bb0 (entry): params a, b. Jump to bb1
///   bb1 (loop): params (a, b). b != 0? -> bb2 (body) or bb3 (exit with a)
///   bb2 (body): t = a % b, br -> bb1(b, t)
///   bb3 (exit): return a
fn build_trust_ir_gcd_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_gcd", ft_id, BlockId::new(0));
    func.blocks = vec![
        // bb0 (entry)
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![
                (ValueId::new(0), Ty::I64), // a
                (ValueId::new(1), Ty::I64), // b
            ],
            body: vec![InstrNode::new(Inst::Br {
                target: BlockId::new(1),
                args: vec![ValueId::new(0), ValueId::new(1)],
            })],
        },
        // bb1 (loop): params (a, b). Check b != 0.
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![
                (ValueId::new(10), Ty::I64), // a
                (ValueId::new(11), Ty::I64), // b
            ],
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
                    then_target: BlockId::new(2), // body
                    then_args: vec![],
                    else_target: BlockId::new(3), // exit
                    else_args: vec![ValueId::new(10)],
                }),
            ],
        },
        // bb2 (body): t = a % b, loop back
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
        // bb3 (exit): return a
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

/// Build trust_ir for: `fn _sum_1_to_n(n: i64) -> i64`
///
/// bb0 (entry): sum=0, i=1, br -> bb1
/// bb1 (loop): params(sum, i), cmp i <= n, condbr -> bb2 (body) or bb3 (exit)
/// bb2 (body): new_sum = sum + i, new_i = i + 1, br -> bb1
/// bb3 (exit): return sum
fn build_trust_ir_sum_1_to_n_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_sum_1_to_n", ft_id, BlockId::new(0));
    func.blocks = vec![
        // bb0 (entry): init sum=0, i=1
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
        // bb1 (loop): params(sum, i), check i <= n
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
                    lhs: ValueId::new(11),
                    rhs: ValueId::new(0),
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
        // bb2 (body): new_sum = sum + i, new_i = i + 1
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
        // bb3 (exit): return sum
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

/// Build trust_ir for: `fn _factorial(n: i64) -> i64`
///
/// Iterative factorial:
///   bb0: check n <= 1
///   bb1: return 1
///   bb2: loop init acc=1, i=2
///   bb3 (loop): params(acc, i), cmp i <= n, condbr -> bb4 (body) or bb5 (exit)
///   bb4: new_acc = acc * i, new_i = i + 1, br -> bb3
///   bb5: return acc
fn build_trust_ir_factorial_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_factorial", ft_id, BlockId::new(0));
    func.blocks = vec![
        // bb0: check n <= 1
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
        // bb1: return 1
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            })],
        },
        // bb2: loop init
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
        // bb3 (loop header): params(acc, i)
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
        // bb4 (loop body): acc * i, i + 1
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
        // bb5 (exit): return acc
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

/// Build trust_ir for: `fn _max_val(a: i64, b: i64) -> i64`
///
/// bb0: if a > b -> bb1 (ret a) else bb2 (ret b)
fn build_trust_ir_max_module() -> TrustIrModule {
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

/// Build trust_ir for: `fn _abs_val(x: i64) -> i64`
///
/// bb0: if x < 0 -> bb1 (ret 0-x) else bb2 (ret x)
fn build_trust_ir_abs_module() -> TrustIrModule {
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

// =============================================================================
// Test 1: fibonacci
//
// fib(0)=0, fib(1)=1, fib(2)=1, fib(5)=5, fib(10)=55, fib(15)=610, fib(20)=6765
// =============================================================================

#[test]
fn test_triple_oracle_fibonacci() {
    if !is_aarch64() || !has_cc() {
        eprintln!("Skipping triple oracle fibonacci: not AArch64 or cc not available");
        return;
    }

    let module = build_trust_ir_fibonacci_module();

    // The C driver includes BOTH the reference implementation AND the main().
    // When linked with Trust Codegen .o, the linker uses the Trust Codegen symbol (driver
    // declares extern). When compiled standalone, clang uses the C impl.
    //
    // For the Trust Codegen path: driver declares extern, links Trust Codegen .o
    // For the clang path: driver defines the function inline
    //
    // To handle both: the standalone clang version includes the implementation,
    // while the Trust Codegen driver declares it extern. We use a single C file that
    // works for both paths by using a weak attribute trick. Actually, simpler:
    // use #ifndef guards.
    //
    // Simplest approach: the C source includes the implementation AND main.
    // For the Trust Codegen path, the driver only has extern + main (no impl).
    // But we pass the same string to both... Let's use a different approach:
    // the C file has both the impl and main. For Trust Codegen, we compile only the
    // driver part. For clang, we compile the whole thing.
    //
    // Actually, the cleanest approach matching e2e_differential.rs: pass two
    // different C strings. But our harness uses one string. Let's restructure.
    //
    // New approach: For Trust Codegen, compile a driver-only .c that declares extern.
    // For clang, compile a complete .c with impl + main. Both produce the same
    // stdout format.

    let c_reference_and_driver = r#"
#include <stdio.h>

#ifndef EXTERN_ONLY
long _fibonacci(long n) {
    if (n <= 1) return n;
    long a = 0, b = 1;
    for (long i = 2; i <= n; i++) {
        long tmp = a + b;
        a = b;
        b = tmp;
    }
    return b;
}
#endif

#ifdef EXTERN_ONLY
extern long _fibonacci(long n);
#endif

int main(void) {
    printf("fib(0)=%ld\n", _fibonacci(0));
    printf("fib(1)=%ld\n", _fibonacci(1));
    printf("fib(2)=%ld\n", _fibonacci(2));
    printf("fib(5)=%ld\n", _fibonacci(5));
    printf("fib(10)=%ld\n", _fibonacci(10));
    printf("fib(15)=%ld\n", _fibonacci(15));
    printf("fib(20)=%ld\n", _fibonacci(20));
    return 0;
}
"#;

    let cases = vec![
        TestCase {
            key: "fib(0)".into(),
            args: vec![0],
        },
        TestCase {
            key: "fib(1)".into(),
            args: vec![1],
        },
        TestCase {
            key: "fib(2)".into(),
            args: vec![2],
        },
        TestCase {
            key: "fib(5)".into(),
            args: vec![5],
        },
        TestCase {
            key: "fib(10)".into(),
            args: vec![10],
        },
        TestCase {
            key: "fib(15)".into(),
            args: vec![15],
        },
        TestCase {
            key: "fib(20)".into(),
            args: vec![20],
        },
    ];

    let result = triple_oracle_test_split(
        "fibonacci",
        &module,
        "_fibonacci",
        c_reference_and_driver,
        &cases,
    );
    assert!(
        result.is_ok(),
        "Triple oracle fibonacci failed: {}",
        result.unwrap_err()
    );
}

// =============================================================================
// Test 2: gcd
//
// gcd(12,8)=4, gcd(100,75)=25, gcd(48,18)=6, gcd(17,13)=1, gcd(0,5)=5,
// gcd(7,0)=7, gcd(1000,1)=1
// =============================================================================

#[test]
fn test_triple_oracle_gcd() {
    if !is_aarch64() || !has_cc() {
        eprintln!("Skipping triple oracle gcd: not AArch64 or cc not available");
        return;
    }

    let module = build_trust_ir_gcd_module();

    let c_source = r#"
#include <stdio.h>

#ifndef EXTERN_ONLY
long _gcd(long a, long b) {
    while (b != 0) {
        long t = a % b;
        a = b;
        b = t;
    }
    return a;
}
#endif

#ifdef EXTERN_ONLY
extern long _gcd(long a, long b);
#endif

int main(void) {
    printf("gcd(12,8)=%ld\n", _gcd(12, 8));
    printf("gcd(100,75)=%ld\n", _gcd(100, 75));
    printf("gcd(48,18)=%ld\n", _gcd(48, 18));
    printf("gcd(17,13)=%ld\n", _gcd(17, 13));
    printf("gcd(0,5)=%ld\n", _gcd(0, 5));
    printf("gcd(7,0)=%ld\n", _gcd(7, 0));
    printf("gcd(1000,1)=%ld\n", _gcd(1000, 1));
    return 0;
}
"#;

    let cases = vec![
        TestCase {
            key: "gcd(12,8)".into(),
            args: vec![12, 8],
        },
        TestCase {
            key: "gcd(100,75)".into(),
            args: vec![100, 75],
        },
        TestCase {
            key: "gcd(48,18)".into(),
            args: vec![48, 18],
        },
        TestCase {
            key: "gcd(17,13)".into(),
            args: vec![17, 13],
        },
        TestCase {
            key: "gcd(0,5)".into(),
            args: vec![0, 5],
        },
        TestCase {
            key: "gcd(7,0)".into(),
            args: vec![7, 0],
        },
        TestCase {
            key: "gcd(1000,1)".into(),
            args: vec![1000, 1],
        },
    ];

    let result = triple_oracle_test_split("gcd", &module, "_gcd", c_source, &cases);
    assert!(
        result.is_ok(),
        "Triple oracle gcd failed: {}",
        result.unwrap_err()
    );
}

// =============================================================================
// Test 3: sum_1_to_n
//
// sum(0)=0, sum(1)=1, sum(5)=15, sum(10)=55, sum(100)=5050, sum(1000)=500500
// =============================================================================

#[test]
fn test_triple_oracle_sum_1_to_n() {
    if !is_aarch64() || !has_cc() {
        eprintln!("Skipping triple oracle sum_1_to_n: not AArch64 or cc not available");
        return;
    }

    let module = build_trust_ir_sum_1_to_n_module();

    let c_source = r#"
#include <stdio.h>

#ifndef EXTERN_ONLY
long _sum_1_to_n(long n) {
    long sum = 0;
    for (long i = 1; i <= n; i++) {
        sum += i;
    }
    return sum;
}
#endif

#ifdef EXTERN_ONLY
extern long _sum_1_to_n(long n);
#endif

int main(void) {
    printf("sum(0)=%ld\n", _sum_1_to_n(0));
    printf("sum(1)=%ld\n", _sum_1_to_n(1));
    printf("sum(5)=%ld\n", _sum_1_to_n(5));
    printf("sum(10)=%ld\n", _sum_1_to_n(10));
    printf("sum(100)=%ld\n", _sum_1_to_n(100));
    printf("sum(1000)=%ld\n", _sum_1_to_n(1000));
    return 0;
}
"#;

    let cases = vec![
        TestCase {
            key: "sum(0)".into(),
            args: vec![0],
        },
        TestCase {
            key: "sum(1)".into(),
            args: vec![1],
        },
        TestCase {
            key: "sum(5)".into(),
            args: vec![5],
        },
        TestCase {
            key: "sum(10)".into(),
            args: vec![10],
        },
        TestCase {
            key: "sum(100)".into(),
            args: vec![100],
        },
        TestCase {
            key: "sum(1000)".into(),
            args: vec![1000],
        },
    ];

    let result = triple_oracle_test_split("sum_1_to_n", &module, "_sum_1_to_n", c_source, &cases);
    assert!(
        result.is_ok(),
        "Triple oracle sum_1_to_n failed: {}",
        result.unwrap_err()
    );
}

// =============================================================================
// Test 4: factorial
//
// fact(0)=1, fact(1)=1, fact(5)=120, fact(10)=3628800, fact(12)=479001600,
// fact(20)=2432902008176640000
// =============================================================================

#[test]
fn test_triple_oracle_factorial() {
    if !is_aarch64() || !has_cc() {
        eprintln!("Skipping triple oracle factorial: not AArch64 or cc not available");
        return;
    }

    let module = build_trust_ir_factorial_module();

    let c_source = r#"
#include <stdio.h>

#ifndef EXTERN_ONLY
long _factorial(long n) {
    if (n <= 1) return 1;
    long acc = 1;
    for (long i = 2; i <= n; i++) {
        acc *= i;
    }
    return acc;
}
#endif

#ifdef EXTERN_ONLY
extern long _factorial(long n);
#endif

int main(void) {
    printf("fact(0)=%ld\n", _factorial(0));
    printf("fact(1)=%ld\n", _factorial(1));
    printf("fact(5)=%ld\n", _factorial(5));
    printf("fact(10)=%ld\n", _factorial(10));
    printf("fact(12)=%ld\n", _factorial(12));
    printf("fact(20)=%ld\n", _factorial(20));
    return 0;
}
"#;

    let cases = vec![
        TestCase {
            key: "fact(0)".into(),
            args: vec![0],
        },
        TestCase {
            key: "fact(1)".into(),
            args: vec![1],
        },
        TestCase {
            key: "fact(5)".into(),
            args: vec![5],
        },
        TestCase {
            key: "fact(10)".into(),
            args: vec![10],
        },
        TestCase {
            key: "fact(12)".into(),
            args: vec![12],
        },
        TestCase {
            key: "fact(20)".into(),
            args: vec![20],
        },
    ];

    let result = triple_oracle_test_split("factorial", &module, "_factorial", c_source, &cases);
    assert!(
        result.is_ok(),
        "Triple oracle factorial failed: {}",
        result.unwrap_err()
    );
}

// =============================================================================
// Test 5: max_val
//
// max(10,20)=20, max(20,10)=20, max(5,5)=5, max(-3,-7)=-3, max(-1,1)=1,
// max(0,0)=0, max(-1000000,1000000)=1000000
// =============================================================================

#[test]
fn test_triple_oracle_max() {
    if !is_aarch64() || !has_cc() {
        eprintln!("Skipping triple oracle max: not AArch64 or cc not available");
        return;
    }

    let module = build_trust_ir_max_module();

    let c_source = r#"
#include <stdio.h>

#ifndef EXTERN_ONLY
long _max_val(long a, long b) {
    return (a > b) ? a : b;
}
#endif

#ifdef EXTERN_ONLY
extern long _max_val(long a, long b);
#endif

int main(void) {
    printf("max(10,20)=%ld\n", _max_val(10, 20));
    printf("max(20,10)=%ld\n", _max_val(20, 10));
    printf("max(5,5)=%ld\n", _max_val(5, 5));
    printf("max(-3,-7)=%ld\n", _max_val(-3, -7));
    printf("max(-1,1)=%ld\n", _max_val(-1, 1));
    printf("max(0,0)=%ld\n", _max_val(0, 0));
    printf("max(-1000000,1000000)=%ld\n", _max_val(-1000000, 1000000));
    return 0;
}
"#;

    let cases = vec![
        TestCase {
            key: "max(10,20)".into(),
            args: vec![10, 20],
        },
        TestCase {
            key: "max(20,10)".into(),
            args: vec![20, 10],
        },
        TestCase {
            key: "max(5,5)".into(),
            args: vec![5, 5],
        },
        TestCase {
            key: "max(-3,-7)".into(),
            args: vec![-3, -7],
        },
        TestCase {
            key: "max(-1,1)".into(),
            args: vec![-1, 1],
        },
        TestCase {
            key: "max(0,0)".into(),
            args: vec![0, 0],
        },
        TestCase {
            key: "max(-1000000,1000000)".into(),
            args: vec![-1000000, 1000000],
        },
    ];

    let result = triple_oracle_test_split("max_val", &module, "_max_val", c_source, &cases);
    assert!(
        result.is_ok(),
        "Triple oracle max failed: {}",
        result.unwrap_err()
    );
}

// =============================================================================
// Test 6: abs_val
//
// abs(42)=42, abs(-42)=42, abs(0)=0, abs(-1)=1, abs(1)=1, abs(-9999)=9999
// =============================================================================

#[test]
fn test_triple_oracle_abs() {
    if !is_aarch64() || !has_cc() {
        eprintln!("Skipping triple oracle abs: not AArch64 or cc not available");
        return;
    }

    let module = build_trust_ir_abs_module();

    let c_source = r#"
#include <stdio.h>

#ifndef EXTERN_ONLY
long _abs_val(long x) {
    return (x < 0) ? (0 - x) : x;
}
#endif

#ifdef EXTERN_ONLY
extern long _abs_val(long x);
#endif

int main(void) {
    printf("abs(42)=%ld\n", _abs_val(42));
    printf("abs(-42)=%ld\n", _abs_val(-42));
    printf("abs(0)=%ld\n", _abs_val(0));
    printf("abs(-1)=%ld\n", _abs_val(-1));
    printf("abs(1)=%ld\n", _abs_val(1));
    printf("abs(-9999)=%ld\n", _abs_val(-9999));
    return 0;
}
"#;

    let cases = vec![
        TestCase {
            key: "abs(42)".into(),
            args: vec![42],
        },
        TestCase {
            key: "abs(-42)".into(),
            args: vec![-42],
        },
        TestCase {
            key: "abs(0)".into(),
            args: vec![0],
        },
        TestCase {
            key: "abs(-1)".into(),
            args: vec![-1],
        },
        TestCase {
            key: "abs(1)".into(),
            args: vec![1],
        },
        TestCase {
            key: "abs(-9999)".into(),
            args: vec![-9999],
        },
    ];

    let result = triple_oracle_test_split("abs_val", &module, "_abs_val", c_source, &cases);
    assert!(
        result.is_ok(),
        "Triple oracle abs failed: {}",
        result.unwrap_err()
    );
}

// =============================================================================
// Split triple oracle harness
//
// The C source uses #ifdef EXTERN_ONLY to control whether the function
// implementation is included. For the Trust Codegen path, we compile with
// -DEXTERN_ONLY so only the extern declaration + main is compiled, and the
// Trust Codegen .o provides the actual implementation. For the clang path, we compile
// without the define so the C implementation is included.
// =============================================================================

/// Run a triple oracle test using a single C source with #ifdef EXTERN_ONLY.
///
/// For Trust Codegen: `cc -DEXTERN_ONLY driver.c trust-cg.o -o test_trust-cg`
/// For clang: `cc reference.c -o test_clang`  (includes implementation)
fn triple_oracle_test_split(
    test_name: &str,
    trust_ir_module: &TrustIrModule,
    func_name: &str,
    c_source: &str,
    cases: &[TestCase],
) -> Result<(), String> {
    let dir = make_test_dir(test_name);

    // --- Oracle 1: Interpreter ---
    let mut interp_results: HashMap<String, i64> = HashMap::new();
    for tc in cases {
        let result = interp_i64(trust_ir_module, func_name, &tc.args);
        interp_results.insert(tc.key.clone(), result);
    }
    eprintln!("=== Triple oracle: {} ===", test_name);
    eprintln!("  Interpreter results: {:?}", interp_results);

    // --- Oracle 2: Trust Codegen compiled binary ---
    let trust_cg_obj_bytes = compile_trust_ir_module(trust_ir_module);
    let trust_cg_obj_path = dir.join("trust_cg_func.o");
    fs::write(&trust_cg_obj_path, &trust_cg_obj_bytes)
        .map_err(|e| format!("write trust-cg .o: {}", e))?;

    // Write driver C with EXTERN_ONLY
    let driver_path = dir.join("trust_cg_driver.c");
    fs::write(&driver_path, c_source).map_err(|e| format!("write trust_cg_driver.c: {}", e))?;

    let trust_cg_binary = dir.join("test_trust-cg");
    let trust_cg_link = Command::new("cc")
        .args([
            "-DEXTERN_ONLY",
            "-O0",
            "-o",
            trust_cg_binary.to_str().unwrap(),
            driver_path.to_str().unwrap(),
            trust_cg_obj_path.to_str().unwrap(),
        ])
        .output()
        .map_err(|e| format!("Trust Codegen compile/link: {}", e))?;

    if !trust_cg_link.status.success() {
        let stderr = String::from_utf8_lossy(&trust_cg_link.stderr);
        // Debug: show symbols
        let nm = Command::new("nm")
            .args([trust_cg_obj_path.to_str().unwrap()])
            .output()
            .ok();
        let nm_out = nm
            .map(|o| String::from_utf8_lossy(&o.stdout).to_string())
            .unwrap_or_default();
        return Err(format!(
            "Trust Codegen link failed!\nstderr: {}\nnm:\n{}",
            stderr, nm_out
        ));
    }

    let trust_cg_run = Command::new(&trust_cg_binary)
        .output()
        .map_err(|e| format!("run Trust Codegen binary: {}", e))?;
    if !trust_cg_run.status.success() {
        return Err(format!(
            "Trust Codegen binary exited with code {}",
            trust_cg_run.status.code().unwrap_or(-1)
        ));
    }
    let trust_cg_stdout = String::from_utf8_lossy(&trust_cg_run.stdout).to_string();
    let trust_cg_results = parse_results(&trust_cg_stdout);
    eprintln!("  Trust Codegen results:       {:?}", trust_cg_results);

    // --- Oracle 3: Clang compiled binary (standalone, includes impl) ---
    let ref_path = dir.join("clang_reference.c");
    fs::write(&ref_path, c_source).map_err(|e| format!("write clang_reference.c: {}", e))?;

    let clang_binary = dir.join("test_clang");
    let clang_compile = Command::new("cc")
        .args([
            "-O0",
            "-o",
            clang_binary.to_str().unwrap(),
            ref_path.to_str().unwrap(),
        ])
        .output()
        .map_err(|e| format!("clang compile: {}", e))?;

    if !clang_compile.status.success() {
        let stderr = String::from_utf8_lossy(&clang_compile.stderr);
        return Err(format!("clang compile failed: {}", stderr));
    }

    let clang_run = Command::new(&clang_binary)
        .output()
        .map_err(|e| format!("run clang binary: {}", e))?;
    if !clang_run.status.success() {
        return Err(format!(
            "clang binary exited with code {}",
            clang_run.status.code().unwrap_or(-1)
        ));
    }
    let clang_stdout = String::from_utf8_lossy(&clang_run.stdout).to_string();
    let clang_results = parse_results(&clang_stdout);
    eprintln!("  Clang results:       {:?}", clang_results);

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
                        "  {}: interp={}, trust-cg={}, clang={}",
                        tc.key, i, l, c
                    ));
                }
            }
            _ => {
                mismatches.push(format!(
                    "  {}: MISSING -- interp={:?}, trust-cg={:?}, clang={:?}",
                    tc.key, interp_val, trust_cg_val, clang_val
                ));
            }
        }
    }

    cleanup(&dir);

    if !mismatches.is_empty() {
        Err(format!(
            "TRIPLE ORACLE MISMATCH for {}:\n{}",
            test_name,
            mismatches.join("\n")
        ))
    } else {
        eprintln!("  ALL THREE ORACLES AGREE");
        Ok(())
    }
}
