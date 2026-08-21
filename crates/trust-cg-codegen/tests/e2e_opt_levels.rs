// trust-cg-codegen/tests/e2e_opt_levels.rs - Cross-optimization-level correctness tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// These tests verify that Trust Codegen-compiled functions produce CORRECT results at
// ALL optimization levels (O0, O1, O2, O3). For each test function, we compile
// through the full trust_ir pipeline at every opt level, link with a C driver, run,
// and verify the output matches known-good values.
//
// This catches optimization bugs where a pass corrupts semantics — the most
// dangerous class of compiler bugs because the binary "works" but computes
// wrong answers.
//
// Part of #301 — Multi-optimization-level correctness validation.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

mod common;

use common::rosetta::{codegen_run_timeout, run_executable_with_timeout};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_lower::Type as LirType;

use trust_ir::{BinOp, ICmpOp, Inst, InstrNode};
use trust_ir::{
    Block as TrustIrBlock, Constant, FieldDef, FuncTy, Function as TrustIrFunction,
    Module as TrustIrModule, StructDef, StructId, Ty,
};
use trust_ir::{BlockId, FuncId, ValueId};

// ---------------------------------------------------------------------------
// Host-native object support (GB10 re-baseline): these e2e tests emit objects
// the HOST toolchain links and runs, so emission, magic checks, PIE flags and
// disassembly must follow the host format — Mach-O on macOS, ELF elsewhere.
// ---------------------------------------------------------------------------

#[allow(dead_code)]
fn host_aarch64_triple() -> &'static str {
    if cfg!(target_os = "macos") {
        "aarch64-apple-darwin"
    } else {
        "aarch64-unknown-linux-gnu"
    }
}

#[allow(dead_code)]
fn host_no_pie_flag() -> &'static str {
    if cfg!(target_os = "macos") {
        "-Wl,-no_pie"
    } else {
        "-no-pie"
    }
}

#[allow(dead_code)]
fn host_object_magic_u32() -> u32 {
    if cfg!(target_os = "macos") {
        0xFEED_FACF
    } else {
        u32::from_le_bytes([0x7F, b'E', b'L', b'F'])
    }
}

#[allow(dead_code)]
fn assert_host_object_magic_bytes(obj_bytes: &[u8], context: &str) {
    assert!(obj_bytes.len() >= 4, "{context}: object too small");
    let expected = host_object_magic_u32().to_le_bytes();
    assert_eq!(
        &obj_bytes[0..4],
        &expected,
        "{context}: object magic must match the host-native format"
    );
}

// ---------------------------------------------------------------------------
// Test infrastructure
// ---------------------------------------------------------------------------

fn is_aarch64() -> bool {
    cfg!(target_arch = "aarch64")
}

fn has_cc() -> bool {
    Command::new("cc")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

fn make_test_dir(test_name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("trust_cg_opt_levels_{}", test_name));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("Failed to create test directory");
    dir
}

fn write_c_driver(dir: &Path, filename: &str, source: &str) -> PathBuf {
    let path = dir.join(filename);
    fs::write(&path, source).expect("Failed to write C driver");
    path
}

fn write_object_file(dir: &Path, filename: &str, bytes: &[u8]) -> PathBuf {
    let path = dir.join(filename);
    fs::write(&path, bytes).expect("Failed to write .o file");
    path
}

fn link_with_cc(dir: &Path, driver_c: &Path, obj: &Path, output_name: &str) -> PathBuf {
    let binary = dir.join(output_name);
    let result = Command::new("cc")
        .arg("-o")
        .arg(&binary)
        .arg(driver_c)
        .arg(obj)
        .arg(host_no_pie_flag())
        .output()
        .expect("Failed to run cc");

    if !result.status.success() {
        let stderr = String::from_utf8_lossy(&result.stderr);
        let stdout = String::from_utf8_lossy(&result.stdout);
        panic!(
            "Linking failed!\ncc stdout: {}\ncc stderr: {}\nDriver: {}\nObject: {}",
            stdout,
            stderr,
            driver_c.display(),
            obj.display()
        );
    }

    binary
}

fn run_binary_with_output(binary: &Path) -> (i32, String) {
    let timeout = codegen_run_timeout();
    let result =
        run_executable_with_timeout(binary, timeout).expect("Failed to run binary with timeout");
    let stdout = String::from_utf8_lossy(&result.output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&result.output.stderr);

    if result.timed_out {
        panic!(
            "Binary {} timed out after {:?} -- likely infinite loop in generated code; stdout={:?}, stderr={:?}",
            binary.display(),
            timeout,
            stdout,
            stderr
        );
    }

    (result.output.status.code().unwrap_or(-1), stdout)
}

fn cleanup(dir: &Path) {
    let _ = fs::remove_dir_all(dir);
}

// ---------------------------------------------------------------------------
// Helper: compile a trust_ir function through the full pipeline
// ---------------------------------------------------------------------------

fn compile_trust_ir_function(
    trust_ir_func: &TrustIrFunction,
    module: &TrustIrModule,
    opt_level: OptLevel,
) -> Result<Vec<u8>, String> {
    let (lir_func, _proof_ctx) = trust_cg_lower::translate_function(trust_ir_func, module)
        .map_err(|e| format!("adapter error: {}", e))?;
    compile_lir_function(&lir_func, opt_level)
}

fn compile_lir_function(
    lir_func: &trust_cg_lower::Function,
    opt_level: OptLevel,
) -> Result<Vec<u8>, String> {
    let config = PipelineConfig {
        target_triple: host_aarch64_triple().to_string(),
        opt_level,
        emit_debug: false,
        ..Default::default()
    };
    let pipeline = Pipeline::new(config);
    let obj_bytes = pipeline
        .compile_function(lir_func)
        .map_err(|e| format!("pipeline error: {}", e))?;

    Ok(obj_bytes)
}

/// All optimization levels to test.
const OPT_LEVELS: &[OptLevel] = &[OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn opt_level_name(opt: &OptLevel) -> &'static str {
    match opt {
        OptLevel::O0 => "O0",
        OptLevel::O1 => "O1",
        OptLevel::O2 => "O2",
        OptLevel::O3 => "O3",
    }
}

// ---------------------------------------------------------------------------
// trust_ir function builders (duplicated from e2e_full_pipeline.rs and
// e2e_differential.rs — integration tests are separate binaries)
// ---------------------------------------------------------------------------

/// Build trust_ir for: fn fibonacci(n: i64) -> i64
///
/// Iterative fibonacci with SSA block parameters.
fn build_fibonacci_trust_ir() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "fibonacci", ft_id, BlockId::new(0));
    func.blocks = vec![
        // bb0 (entry): check if n <= 1
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
                    then_target: BlockId::new(1),
                    then_args: vec![],
                    else_target: BlockId::new(2),
                    else_args: vec![],
                }),
            ],
        },
        // bb1 (ret_n): return n directly
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            })],
        },
        // bb2 (loop_init): setup a=0, b=1, i=2, jump to loop
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
        // bb3 (loop): loop body with block parameters
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
                    rhs: ValueId::new(0),
                })
                .with_result(ValueId::new(26)),
                // condbr: loop back or exit
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(26),
                    then_target: BlockId::new(3),
                    then_args: vec![ValueId::new(21), ValueId::new(23), ValueId::new(25)],
                    else_target: BlockId::new(4),
                    else_args: vec![ValueId::new(23)],
                }),
            ],
        },
        // bb4 (ret_b): return the result
        TrustIrBlock {
            id: BlockId::new(4),
            params: vec![(ValueId::new(30), Ty::I64)],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(30)],
            })],
        },
    ];
    module.add_function(func.clone());
    (func, module)
}

/// Build trust_ir for: fn gcd(a: i64, b: i64) -> i64
///
/// Euclidean algorithm using SRem.
fn build_gcd_trust_ir() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "gcd", ft_id, BlockId::new(0));
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
                    then_target: BlockId::new(2),
                    then_args: vec![],
                    else_target: BlockId::new(3),
                    else_args: vec![ValueId::new(10)],
                }),
            ],
        },
        // bb2 (body): t = a % b, loop back with (b, t)
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
        // bb3 (exit): return result
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![(ValueId::new(30), Ty::I64)],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(30)],
            })],
        },
    ];
    module.add_function(func.clone());
    (func, module)
}

/// Build trust_ir for: fn collatz_steps(n: i64) -> i64
///
/// Count steps to reach 1 in the Collatz sequence.
fn build_collatz_steps_trust_ir() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "collatz_steps", ft_id, BlockId::new(0));
    func.blocks = vec![
        // bb0 (entry): param n, jump to loop with (n, 0)
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(1),
                    args: vec![ValueId::new(0), ValueId::new(1)],
                }),
            ],
        },
        // bb1 (loop): params (n, steps). Check n != 1.
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![
                (ValueId::new(10), Ty::I64), // n
                (ValueId::new(11), Ty::I64), // steps
            ],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(12)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ne,
                    ty: Ty::I64,
                    lhs: ValueId::new(10),
                    rhs: ValueId::new(12),
                })
                .with_result(ValueId::new(13)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(13),
                    then_target: BlockId::new(2),
                    then_args: vec![],
                    else_target: BlockId::new(3),
                    else_args: vec![ValueId::new(11)],
                }),
            ],
        },
        // bb2 (check even/odd): n % 2 == 0?
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(2),
                })
                .with_result(ValueId::new(20)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::SRem,
                    ty: Ty::I64,
                    lhs: ValueId::new(10),
                    rhs: ValueId::new(20),
                })
                .with_result(ValueId::new(21)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(22)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::I64,
                    lhs: ValueId::new(21),
                    rhs: ValueId::new(22),
                })
                .with_result(ValueId::new(23)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(23),
                    then_target: BlockId::new(4), // even
                    then_args: vec![],
                    else_target: BlockId::new(5), // odd
                    else_args: vec![],
                }),
            ],
        },
        // bb3 (exit): return steps
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![(ValueId::new(30), Ty::I64)],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(30)],
            })],
        },
        // bb4 (even): new_n = n / 2, new_steps = steps + 1, br bb1
        TrustIrBlock {
            id: BlockId::new(4),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(2),
                })
                .with_result(ValueId::new(40)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::SDiv,
                    ty: Ty::I64,
                    lhs: ValueId::new(10),
                    rhs: ValueId::new(40),
                })
                .with_result(ValueId::new(41)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(42)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(11),
                    rhs: ValueId::new(42),
                })
                .with_result(ValueId::new(43)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(1),
                    args: vec![ValueId::new(41), ValueId::new(43)],
                }),
            ],
        },
        // bb5 (odd): tmp = n * 3, new_n = tmp + 1, new_steps = steps + 1, br bb1
        TrustIrBlock {
            id: BlockId::new(5),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(3),
                })
                .with_result(ValueId::new(50)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Mul,
                    ty: Ty::I64,
                    lhs: ValueId::new(10),
                    rhs: ValueId::new(50),
                })
                .with_result(ValueId::new(51)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(52)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(51),
                    rhs: ValueId::new(52),
                })
                .with_result(ValueId::new(53)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(54)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(11),
                    rhs: ValueId::new(54),
                })
                .with_result(ValueId::new(55)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(1),
                    args: vec![ValueId::new(53), ValueId::new(55)],
                }),
            ],
        },
    ];
    module.add_function(func.clone());
    (func, module)
}

/// Build trust_ir for: fn _factorial(n: i64) -> i64
///
/// Iterative factorial with multiply loop.
fn build_trust_ir_factorial() -> (TrustIrFunction, TrustIrModule) {
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
        // bb3: loop header
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
        // bb4: loop body
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
        // bb5: exit
        TrustIrBlock {
            id: BlockId::new(5),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(20)],
            })],
        },
    ];
    module.add_function(func.clone());
    (func, module)
}

/// Build trust_ir for: fn _sum_1_to_n(n: i64) -> i64
///
/// Sum from 1 to n using a counting loop.
fn build_trust_ir_sum_1_to_n() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_sum_1_to_n", ft_id, BlockId::new(0));
    func.blocks = vec![
        // bb0: init
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
        // bb1: loop header
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
                    then_target: BlockId::new(2),
                    then_args: vec![],
                    else_target: BlockId::new(3),
                    else_args: vec![],
                }),
            ],
        },
        // bb2: loop body
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
        // bb3: exit
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(10)],
            })],
        },
    ];
    module.add_function(func.clone());
    (func, module)
}

fn record_state_struct_def(id: StructId) -> StructDef {
    StructDef {
        id,
        name: "RecordState".to_string(),
        fields: vec![
            FieldDef {
                name: "pc".to_string(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "counter".to_string(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "owner".to_string(),
                ty: Ty::I64,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: Default::default(),
    }
}

fn build_record_state_probe_trust_ir(typed_state: bool) -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("typed_record_state_probe");
    let state_struct_id = StructId::new(0);
    let current_state_ty = if typed_state {
        module.structs = vec![record_state_struct_def(state_struct_id)];
        Ty::PtrConst(Box::new(Ty::Struct(state_struct_id)))
    } else {
        Ty::Ptr
    };
    let next_state_ty = if typed_state {
        Ty::PtrMut(Box::new(Ty::Struct(state_struct_id)))
    } else {
        Ty::Ptr
    };
    let params = vec![Ty::Ptr, current_state_ty, next_state_ty, Ty::I64];
    let ft_id = module.add_func_type(FuncTy {
        params: params.clone(),
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(
        FuncId::new(0),
        "typed_record_state_probe",
        ft_id,
        BlockId::new(0),
    );
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: params
            .into_iter()
            .enumerate()
            .map(|(idx, ty)| (ValueId::new(idx as u32), ty))
            .collect(),
        body: vec![InstrNode::new(Inst::Return {
            values: vec![ValueId::new(3)],
        })],
    }];
    module.add_function(func.clone());
    (func, module)
}

#[test]
fn typed_record_state_pointee_metadata_does_not_change_o0_o3_scalar_abi_output() {
    let (typed_func, typed_module) = build_record_state_probe_trust_ir(true);
    let (raw_func, raw_module) = build_record_state_probe_trust_ir(false);
    let (typed_lir, _typed_proofs) =
        trust_cg_lower::translate_function(&typed_func, &typed_module).unwrap();
    let (raw_lir, _raw_proofs) =
        trust_cg_lower::translate_function(&raw_func, &raw_module).unwrap();
    let record_state = LirType::Struct(vec![LirType::I64, LirType::I64, LirType::I64]);

    assert_eq!(
        typed_lir.signature.params,
        vec![LirType::I64, LirType::I64, LirType::I64, LirType::I64]
    );
    assert_eq!(typed_lir.signature.params, raw_lir.signature.params);
    assert!(raw_lir.param_pointee_types.is_empty());
    assert_eq!(typed_lir.param_pointee_types.len(), 2);
    assert_eq!(typed_lir.param_pointee_types[0].param_index, 1);
    assert_eq!(&typed_lir.param_pointee_types[0].pointee_ty, &record_state);
    assert_eq!(typed_lir.param_pointee_types[1].param_index, 2);
    assert_eq!(&typed_lir.param_pointee_types[1].pointee_ty, &record_state);

    for opt in OPT_LEVELS {
        let name = opt_level_name(opt);
        let typed_obj = compile_lir_function(&typed_lir, *opt)
            .unwrap_or_else(|e| panic!("typed record-state compile at {} failed: {}", name, e));
        let raw_obj = compile_lir_function(&raw_lir, *opt)
            .unwrap_or_else(|e| panic!("raw pointer compile at {} failed: {}", name, e));
        assert!(!typed_obj.is_empty(), "typed object at {} is empty", name);
        assert_eq!(
            typed_obj, raw_obj,
            "record-state pointee sidecar must not perturb scalar ABI object output at {}",
            name
        );
    }
}

// ===========================================================================
// Test: fibonacci at O0, O1, O2, O3
// ===========================================================================

/// Compiles fibonacci through the full trust_ir pipeline at every optimization
/// level, links, runs, and verifies correct results.
#[test]
fn test_opt_levels_fibonacci() {
    if !is_aarch64() || !has_cc() {
        eprintln!("Skipping e2e opt level test: not AArch64 or cc not available");
        return;
    }

    let (trust_ir_func, module) = build_fibonacci_trust_ir();

    let driver_src = r#"
#include <stdio.h>
extern long fibonacci(long n);
int main(void) {
    struct { long n; long expected; } tests[] = {
        {0, 0}, {1, 1}, {2, 1}, {3, 2}, {5, 5},
        {10, 55}, {15, 610}, {20, 6765},
    };
    int n_tests = sizeof(tests) / sizeof(tests[0]);
    for (int i = 0; i < n_tests; i++) {
        long result = fibonacci(tests[i].n);
        printf("fibonacci(%ld) = %ld (expected %ld) %s\n",
               tests[i].n, result, tests[i].expected,
               result == tests[i].expected ? "OK" : "FAIL");
        if (result != tests[i].expected) return i + 1;
    }
    printf("All %d fibonacci tests passed.\n", n_tests);
    return 0;
}
"#;

    for opt in OPT_LEVELS {
        let name = opt_level_name(opt);
        let dir = make_test_dir(&format!("fibonacci_{}", name));

        let obj_bytes = compile_trust_ir_function(&trust_ir_func, &module, *opt)
            .unwrap_or_else(|e| panic!("fibonacci compilation at {} failed: {}", name, e));

        let obj_path = write_object_file(&dir, "fibonacci.o", &obj_bytes);
        let driver_path = write_c_driver(&dir, "driver.c", driver_src);
        let binary = link_with_cc(&dir, &driver_path, &obj_path, "test_fib");

        let (exit_code, stdout) = run_binary_with_output(&binary);
        eprintln!("fibonacci @ {} stdout:\n{}", name, stdout);
        assert_eq!(
            exit_code, 0,
            "fibonacci FAILED at {} (test case {} 1-indexed). stdout:\n{}",
            name, exit_code, stdout
        );

        cleanup(&dir);
    }
}

// ===========================================================================
// Test: gcd at O0, O1, O2, O3
// ===========================================================================

/// Compiles gcd through the full trust_ir pipeline at every optimization level.
#[test]
fn test_opt_levels_gcd() {
    if !is_aarch64() || !has_cc() {
        eprintln!("Skipping e2e opt level test: not AArch64 or cc not available");
        return;
    }

    let (trust_ir_func, module) = build_gcd_trust_ir();

    let driver_src = r#"
#include <stdio.h>
extern long gcd(long a, long b);
int main(void) {
    struct { long a; long b; long expected; } tests[] = {
        {12, 8, 4}, {100, 75, 25}, {17, 13, 1},
        {0, 5, 5}, {7, 0, 7}, {1, 1, 1}, {48, 36, 12},
    };
    int n_tests = sizeof(tests) / sizeof(tests[0]);
    for (int i = 0; i < n_tests; i++) {
        long result = gcd(tests[i].a, tests[i].b);
        printf("gcd(%ld,%ld) = %ld (expected %ld) %s\n",
               tests[i].a, tests[i].b, result, tests[i].expected,
               result == tests[i].expected ? "OK" : "FAIL");
        if (result != tests[i].expected) return i + 1;
    }
    printf("All %d gcd tests passed.\n", n_tests);
    return 0;
}
"#;

    for opt in OPT_LEVELS {
        let name = opt_level_name(opt);
        let dir = make_test_dir(&format!("gcd_{}", name));

        let obj_bytes = compile_trust_ir_function(&trust_ir_func, &module, *opt)
            .unwrap_or_else(|e| panic!("gcd compilation at {} failed: {}", name, e));

        let obj_path = write_object_file(&dir, "gcd.o", &obj_bytes);
        let driver_path = write_c_driver(&dir, "driver.c", driver_src);
        let binary = link_with_cc(&dir, &driver_path, &obj_path, "test_gcd");

        let (exit_code, stdout) = run_binary_with_output(&binary);
        eprintln!("gcd @ {} stdout:\n{}", name, stdout);
        assert_eq!(
            exit_code, 0,
            "gcd FAILED at {} (test case {} 1-indexed). stdout:\n{}",
            name, exit_code, stdout
        );

        cleanup(&dir);
    }
}

// ===========================================================================
// Test: collatz_steps at O0, O1, O2, O3
// ===========================================================================

/// Compiles collatz_steps through the full trust_ir pipeline at every optimization
/// level. This is particularly important because the O2 infinite loop bug
/// (scheduler DAG cycles) was recently fixed — we must verify it stays fixed.
#[test]
fn test_opt_levels_collatz() {
    if !is_aarch64() || !has_cc() {
        eprintln!("Skipping e2e opt level test: not AArch64 or cc not available");
        return;
    }

    let (trust_ir_func, module) = build_collatz_steps_trust_ir();

    let driver_src = r#"
#include <stdio.h>
extern long collatz_steps(long n);
int main(void) {
    struct { long n; long expected; } tests[] = {
        {1, 0}, {2, 1}, {3, 7}, {6, 8}, {7, 16}, {27, 111},
    };
    int n_tests = sizeof(tests) / sizeof(tests[0]);
    for (int i = 0; i < n_tests; i++) {
        long result = collatz_steps(tests[i].n);
        printf("collatz(%ld) = %ld (expected %ld) %s\n",
               tests[i].n, result, tests[i].expected,
               result == tests[i].expected ? "OK" : "FAIL");
        if (result != tests[i].expected) return i + 1;
    }
    printf("All %d collatz tests passed.\n", n_tests);
    return 0;
}
"#;

    for opt in OPT_LEVELS {
        let name = opt_level_name(opt);
        let dir = make_test_dir(&format!("collatz_{}", name));

        let obj_bytes = compile_trust_ir_function(&trust_ir_func, &module, *opt)
            .unwrap_or_else(|e| panic!("collatz compilation at {} failed: {}", name, e));

        let obj_path = write_object_file(&dir, "collatz_steps.o", &obj_bytes);
        let driver_path = write_c_driver(&dir, "driver.c", driver_src);
        let binary = link_with_cc(&dir, &driver_path, &obj_path, "test_collatz");

        let (exit_code, stdout) = run_binary_with_output(&binary);
        eprintln!("collatz @ {} stdout:\n{}", name, stdout);
        assert_eq!(
            exit_code, 0,
            "collatz FAILED at {} (test case {} 1-indexed). stdout:\n{}",
            name, exit_code, stdout
        );

        cleanup(&dir);
    }
}

// ===========================================================================
// Test: factorial at O0, O1, O2, O3
// ===========================================================================

/// Compiles factorial through the full trust_ir pipeline at every optimization
/// level. Exercises multiply loops and accumulator patterns under optimization.
#[test]
fn test_opt_levels_factorial() {
    if !is_aarch64() || !has_cc() {
        eprintln!("Skipping e2e opt level test: not AArch64 or cc not available");
        return;
    }

    let (trust_ir_func, module) = build_trust_ir_factorial();

    let driver_src = r#"
#include <stdio.h>
extern long _factorial(long n);
int main(void) {
    struct { long n; long expected; } tests[] = {
        {0, 1}, {1, 1}, {2, 2}, {5, 120},
        {10, 3628800}, {12, 479001600}, {20, 2432902008176640000L},
    };
    int n_tests = sizeof(tests) / sizeof(tests[0]);
    for (int i = 0; i < n_tests; i++) {
        long result = _factorial(tests[i].n);
        printf("factorial(%ld) = %ld (expected %ld) %s\n",
               tests[i].n, result, tests[i].expected,
               result == tests[i].expected ? "OK" : "FAIL");
        if (result != tests[i].expected) return i + 1;
    }
    printf("All %d factorial tests passed.\n", n_tests);
    return 0;
}
"#;

    for opt in OPT_LEVELS {
        let name = opt_level_name(opt);
        let dir = make_test_dir(&format!("factorial_{}", name));

        let obj_bytes = compile_trust_ir_function(&trust_ir_func, &module, *opt)
            .unwrap_or_else(|e| panic!("factorial compilation at {} failed: {}", name, e));

        let obj_path = write_object_file(&dir, "factorial.o", &obj_bytes);
        let driver_path = write_c_driver(&dir, "driver.c", driver_src);
        let binary = link_with_cc(&dir, &driver_path, &obj_path, "test_factorial");

        let (exit_code, stdout) = run_binary_with_output(&binary);
        eprintln!("factorial @ {} stdout:\n{}", name, stdout);
        assert_eq!(
            exit_code, 0,
            "factorial FAILED at {} (test case {} 1-indexed). stdout:\n{}",
            name, exit_code, stdout
        );

        cleanup(&dir);
    }
}

// ===========================================================================
// Test: sum_1_to_n at O0, O1, O2, O3
// ===========================================================================

/// Compiles sum_1_to_n through the full trust_ir pipeline at every optimization
/// level. Verifiable via the closed-form formula n*(n+1)/2.
#[test]
fn test_opt_levels_sum_1_to_n() {
    if !is_aarch64() || !has_cc() {
        eprintln!("Skipping e2e opt level test: not AArch64 or cc not available");
        return;
    }

    let (trust_ir_func, module) = build_trust_ir_sum_1_to_n();

    let driver_src = r#"
#include <stdio.h>
extern long _sum_1_to_n(long n);
int main(void) {
    struct { long n; long expected; } tests[] = {
        {0, 0}, {1, 1}, {5, 15}, {10, 55},
        {100, 5050}, {1000, 500500},
    };
    int n_tests = sizeof(tests) / sizeof(tests[0]);
    for (int i = 0; i < n_tests; i++) {
        long result = _sum_1_to_n(tests[i].n);
        printf("sum_1_to_n(%ld) = %ld (expected %ld) %s\n",
               tests[i].n, result, tests[i].expected,
               result == tests[i].expected ? "OK" : "FAIL");
        if (result != tests[i].expected) return i + 1;
    }
    printf("All %d sum_1_to_n tests passed.\n", n_tests);
    return 0;
}
"#;

    for opt in OPT_LEVELS {
        let name = opt_level_name(opt);
        let dir = make_test_dir(&format!("sum_1_to_n_{}", name));

        let obj_bytes = compile_trust_ir_function(&trust_ir_func, &module, *opt)
            .unwrap_or_else(|e| panic!("sum_1_to_n compilation at {} failed: {}", name, e));

        let obj_path = write_object_file(&dir, "sum_1_to_n.o", &obj_bytes);
        let driver_path = write_c_driver(&dir, "driver.c", driver_src);
        let binary = link_with_cc(&dir, &driver_path, &obj_path, "test_sum");

        let (exit_code, stdout) = run_binary_with_output(&binary);
        eprintln!("sum_1_to_n @ {} stdout:\n{}", name, stdout);
        assert_eq!(
            exit_code, 0,
            "sum_1_to_n FAILED at {} (test case {} 1-indexed). stdout:\n{}",
            name, exit_code, stdout
        );

        cleanup(&dir);
    }
}
