// trust-cg-codegen/tests/e2e_x86_64_atomics.rs - x86-64 atomics differential oracle
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Differential testing of x86-64 atomic instructions (single-threaded value
// semantics) against clang's `_Atomic` / `__atomic_*` builtins:
//   - AtomicLoad / AtomicStore
//   - AtomicRMW (Add, Sub, And, Or, Xor, Xchg)
//   - CmpXchg
//   - Fence
//
// Each trust_ir function allocates a stack slot, performs the atomic op on it,
// and returns an i64 that captures the observable result (RMW return value
// and/or the final stored value). The clang reference implements the SAME
// observable computation with `__atomic_*` builtins so any divergence is a
// trust-cg miscompile.
//
// The trust_ir interpreter does NOT model memory or atomics (it returns
// Unsupported for Alloca/Load/Store/Atomic*), so these are DIFFERENTIAL-ONLY
// (trust-cg vs clang). Host: x86-64 macOS (cc + native run).

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    AtomicRMWOp, BinOp, Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy,
    Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, Ordering, Ty, ValueId,
};

// =============================================================================
// Host gating
// =============================================================================

/// x86-64 host with a working native C toolchain.
fn x86_64_oracle_enabled() -> bool {
    if !cfg!(target_arch = "x86_64") {
        eprintln!("SKIP: x86-64 atomics oracle requires an x86-64 host");
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
    let dir = std::env::temp_dir().join(format!("trust_cg_x86_64_atomics_{}", test_name));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");
    dir
}

fn cleanup(dir: &Path) {
    let _ = fs::remove_dir_all(dir);
}

/// Compile a trust_ir module to an x86-64 Mach-O object via the public Compiler.
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

// =============================================================================
// Differential harness: trust-cg vs clang
//
// `c_source` is a single C file that contains BOTH the reference impl AND the
// driver main(). Under `-DEXTERN_ONLY` the impl is excluded (driver links the
// trust-cg .o); without it, clang compiles the full reference standalone.
// =============================================================================

fn differential_test(
    test_name: &str,
    module: &TrustIrModule,
    c_source: &str,
) -> Result<(), String> {
    let dir = make_test_dir(test_name);

    // --- trust-cg path ---
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
        let nm = Command::new("nm")
            .arg(obj_path.to_str().unwrap())
            .output()
            .ok();
        let nm_out = nm
            .map(|o| String::from_utf8_lossy(&o.stdout).to_string())
            .unwrap_or_default();
        cleanup(&dir);
        return Err(format!("trust-cg link failed: {}\nnm:\n{}", stderr, nm_out));
    }

    let trust_cg_run = Command::new(&trust_cg_bin)
        .output()
        .map_err(|e| format!("run trust-cg binary: {}", e))?;
    let trust_cg_stdout = String::from_utf8_lossy(&trust_cg_run.stdout).to_string();
    let trust_cg_exit = trust_cg_run.status.code().unwrap_or(-1);

    // --- clang path (standalone reference, includes impl) ---
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

    eprintln!("=== x86-64 atomics differential: {} ===", test_name);
    eprintln!("  trust-cg stdout: {}", trust_cg_stdout.trim());
    eprintln!("  clang    stdout: {}", clang_stdout.trim());
    eprintln!(
        "  trust-cg exit={}  clang exit={}",
        trust_cg_exit, clang_exit
    );

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

// =============================================================================
// trust_ir builders
//
// Each builder allocates an i64 stack slot, stores `init`, performs the op, and
// returns an i64 capturing the observable result.
// =============================================================================

/// `i64 _atomic_load_store(i64 v) { _Atomic long s; store(s, v); return load(s); }`
fn build_atomic_load_store_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_atomic_load_store", ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            // slot = alloca i64
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: Some(8),
            })
            .with_result(ValueId::new(1)),
            // atomic store v -> slot (SeqCst)
            InstrNode::new(Inst::AtomicStore {
                ty: Ty::I64,
                ptr: ValueId::new(1),
                value: ValueId::new(0),
                ordering: Ordering::SeqCst,
            }),
            // r = atomic load slot (SeqCst)
            InstrNode::new(Inst::AtomicLoad {
                ty: Ty::I64,
                ptr: ValueId::new(1),
                ordering: Ordering::SeqCst,
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

/// Build an AtomicRMW module:
/// `i64 _NAME(i64 init, i64 operand) { slot=init; old=rmw(slot, operand); return old + load(slot); }`
///
/// Returning `old + final` makes the test sensitive to BOTH the returned old
/// value and the value actually written back.
fn build_atomic_rmw_module(name: &str, op: AtomicRMWOp) -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), name, ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: Some(8),
            })
            .with_result(ValueId::new(2)),
            // store init
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: ValueId::new(2),
                value: ValueId::new(0),
                volatile: false,
                align: Some(8),
            }),
            // old = rmw(slot, operand)
            InstrNode::new(Inst::AtomicRMW {
                op,
                ty: Ty::I64,
                ptr: ValueId::new(2),
                value: ValueId::new(1),
                ordering: Ordering::SeqCst,
            })
            .with_result(ValueId::new(3)),
            // final = load slot
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(2),
                volatile: false,
                align: Some(8),
            })
            .with_result(ValueId::new(4)),
            // r = old + final
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(3),
                rhs: ValueId::new(4),
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

/// `i64 _atomic_cmpxchg(i64 init, i64 expected, i64 desired)`:
///   slot=init; old = cmpxchg(slot, expected, desired); return old*1000 + load(slot)
/// Sensitive to both the returned previous value and whether the swap happened.
fn build_atomic_cmpxchg_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_atomic_cmpxchg", ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::I64), // init
            (ValueId::new(1), Ty::I64), // expected
            (ValueId::new(2), Ty::I64), // desired
        ],
        body: vec![
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: Some(8),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: ValueId::new(3),
                value: ValueId::new(0),
                volatile: false,
                align: Some(8),
            }),
            // old = cmpxchg(slot, expected, desired) -- result[0] is the previous value
            InstrNode::new(Inst::CmpXchg {
                ty: Ty::I64,
                ptr: ValueId::new(3),
                expected: ValueId::new(1),
                desired: ValueId::new(2),
                success: Ordering::SeqCst,
                failure: Ordering::SeqCst,
            })
            .with_result(ValueId::new(4)),
            // final = load slot
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(3),
                volatile: false,
                align: Some(8),
            })
            .with_result(ValueId::new(5)),
            // k = 1000
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1000),
            })
            .with_result(ValueId::new(6)),
            // old*1000
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: ValueId::new(4),
                rhs: ValueId::new(6),
            })
            .with_result(ValueId::new(7)),
            // + final
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(7),
                rhs: ValueId::new(5),
            })
            .with_result(ValueId::new(8)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(8)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

/// `i64 _atomic_fence(i64 a, i64 b)`:
///   slot=a; fence(SeqCst); store b; fence(SeqCst); return load(slot)
/// Exercises Fence emission around ordinary stores; observable value is `b`.
fn build_atomic_fence_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_atomic_fence", ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: Some(8),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::AtomicStore {
                ty: Ty::I64,
                ptr: ValueId::new(2),
                value: ValueId::new(0),
                ordering: Ordering::SeqCst,
            }),
            InstrNode::new(Inst::Fence {
                ordering: Ordering::SeqCst,
            }),
            InstrNode::new(Inst::AtomicStore {
                ty: Ty::I64,
                ptr: ValueId::new(2),
                value: ValueId::new(1),
                ordering: Ordering::SeqCst,
            }),
            InstrNode::new(Inst::Fence {
                ordering: Ordering::SeqCst,
            }),
            InstrNode::new(Inst::AtomicLoad {
                ty: Ty::I64,
                ptr: ValueId::new(2),
                ordering: Ordering::SeqCst,
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

// =============================================================================
// Tests
// =============================================================================

#[test]
fn test_x86_64_atomic_load_store() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_atomic_load_store_module();
    let c_source = r#"
#include <stdio.h>
#include <stdatomic.h>

#ifndef EXTERN_ONLY
long _atomic_load_store(long v) {
    _Atomic long s;
    atomic_store_explicit(&s, v, memory_order_seq_cst);
    return atomic_load_explicit(&s, memory_order_seq_cst);
}
#endif
#ifdef EXTERN_ONLY
extern long _atomic_load_store(long v);
#endif

int main(void) {
    printf("ls(0)=%ld\n", _atomic_load_store(0));
    printf("ls(1)=%ld\n", _atomic_load_store(1));
    printf("ls(-5)=%ld\n", _atomic_load_store(-5));
    printf("ls(123456789)=%ld\n", _atomic_load_store(123456789L));
    printf("ls(min)=%ld\n", _atomic_load_store((-9223372036854775807L - 1)));
    return 0;
}
"#;
    let r = differential_test("atomic_load_store", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_atomic_rmw_add() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_atomic_rmw_module("_atomic_rmw_add", AtomicRMWOp::Add);
    let c_source = r#"
#include <stdio.h>
#include <stdatomic.h>

#ifndef EXTERN_ONLY
long _atomic_rmw_add(long init, long operand) {
    _Atomic long s = init;
    long old = atomic_fetch_add_explicit(&s, operand, memory_order_seq_cst);
    long final = atomic_load_explicit(&s, memory_order_seq_cst);
    return old + final;
}
#endif
#ifdef EXTERN_ONLY
extern long _atomic_rmw_add(long init, long operand);
#endif

int main(void) {
    printf("add(10,5)=%ld\n", _atomic_rmw_add(10, 5));
    printf("add(0,0)=%ld\n", _atomic_rmw_add(0, 0));
    printf("add(-3,8)=%ld\n", _atomic_rmw_add(-3, 8));
    printf("add(100,-250)=%ld\n", _atomic_rmw_add(100, -250));
    return 0;
}
"#;
    let r = differential_test("atomic_rmw_add", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_atomic_rmw_sub() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_atomic_rmw_module("_atomic_rmw_sub", AtomicRMWOp::Sub);
    let c_source = r#"
#include <stdio.h>
#include <stdatomic.h>

#ifndef EXTERN_ONLY
long _atomic_rmw_sub(long init, long operand) {
    _Atomic long s = init;
    long old = atomic_fetch_sub_explicit(&s, operand, memory_order_seq_cst);
    long final = atomic_load_explicit(&s, memory_order_seq_cst);
    return old + final;
}
#endif
#ifdef EXTERN_ONLY
extern long _atomic_rmw_sub(long init, long operand);
#endif

int main(void) {
    printf("sub(10,5)=%ld\n", _atomic_rmw_sub(10, 5));
    printf("sub(0,7)=%ld\n", _atomic_rmw_sub(0, 7));
    printf("sub(-3,-8)=%ld\n", _atomic_rmw_sub(-3, -8));
    printf("sub(100,250)=%ld\n", _atomic_rmw_sub(100, 250));
    return 0;
}
"#;
    let r = differential_test("atomic_rmw_sub", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_atomic_rmw_and() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_atomic_rmw_module("_atomic_rmw_and", AtomicRMWOp::And);
    let c_source = r#"
#include <stdio.h>
#include <stdatomic.h>

#ifndef EXTERN_ONLY
long _atomic_rmw_and(long init, long operand) {
    _Atomic long s = init;
    long old = atomic_fetch_and_explicit(&s, operand, memory_order_seq_cst);
    long final = atomic_load_explicit(&s, memory_order_seq_cst);
    return old + final;
}
#endif
#ifdef EXTERN_ONLY
extern long _atomic_rmw_and(long init, long operand);
#endif

int main(void) {
    printf("and(0xff,0x0f)=%ld\n", _atomic_rmw_and(0xff, 0x0f));
    printf("and(-1,12345)=%ld\n", _atomic_rmw_and(-1, 12345));
    printf("and(0,999)=%ld\n", _atomic_rmw_and(0, 999));
    printf("and(0x7777,0x3333)=%ld\n", _atomic_rmw_and(0x7777, 0x3333));
    return 0;
}
"#;
    let r = differential_test("atomic_rmw_and", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_atomic_rmw_or() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_atomic_rmw_module("_atomic_rmw_or", AtomicRMWOp::Or);
    let c_source = r#"
#include <stdio.h>
#include <stdatomic.h>

#ifndef EXTERN_ONLY
long _atomic_rmw_or(long init, long operand) {
    _Atomic long s = init;
    long old = atomic_fetch_or_explicit(&s, operand, memory_order_seq_cst);
    long final = atomic_load_explicit(&s, memory_order_seq_cst);
    return old + final;
}
#endif
#ifdef EXTERN_ONLY
extern long _atomic_rmw_or(long init, long operand);
#endif

int main(void) {
    printf("or(0xf0,0x0f)=%ld\n", _atomic_rmw_or(0xf0, 0x0f));
    printf("or(0,0)=%ld\n", _atomic_rmw_or(0, 0));
    printf("or(0x1000,0x0001)=%ld\n", _atomic_rmw_or(0x1000, 0x0001));
    printf("or(-2,1)=%ld\n", _atomic_rmw_or(-2, 1));
    return 0;
}
"#;
    let r = differential_test("atomic_rmw_or", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_atomic_rmw_xor() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_atomic_rmw_module("_atomic_rmw_xor", AtomicRMWOp::Xor);
    let c_source = r#"
#include <stdio.h>
#include <stdatomic.h>

#ifndef EXTERN_ONLY
long _atomic_rmw_xor(long init, long operand) {
    _Atomic long s = init;
    long old = atomic_fetch_xor_explicit(&s, operand, memory_order_seq_cst);
    long final = atomic_load_explicit(&s, memory_order_seq_cst);
    return old + final;
}
#endif
#ifdef EXTERN_ONLY
extern long _atomic_rmw_xor(long init, long operand);
#endif

int main(void) {
    printf("xor(0xff,0x0f)=%ld\n", _atomic_rmw_xor(0xff, 0x0f));
    printf("xor(0,0xabcd)=%ld\n", _atomic_rmw_xor(0, 0xabcd));
    printf("xor(-1,-1)=%ld\n", _atomic_rmw_xor(-1, -1));
    printf("xor(0x5555,0x3333)=%ld\n", _atomic_rmw_xor(0x5555, 0x3333));
    return 0;
}
"#;
    let r = differential_test("atomic_rmw_xor", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_atomic_rmw_xchg() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_atomic_rmw_module("_atomic_rmw_xchg", AtomicRMWOp::Xchg);
    let c_source = r#"
#include <stdio.h>
#include <stdatomic.h>

#ifndef EXTERN_ONLY
long _atomic_rmw_xchg(long init, long operand) {
    _Atomic long s = init;
    long old = atomic_exchange_explicit(&s, operand, memory_order_seq_cst);
    long final = atomic_load_explicit(&s, memory_order_seq_cst);
    return old + final;
}
#endif
#ifdef EXTERN_ONLY
extern long _atomic_rmw_xchg(long init, long operand);
#endif

int main(void) {
    printf("xchg(10,5)=%ld\n", _atomic_rmw_xchg(10, 5));
    printf("xchg(0,0)=%ld\n", _atomic_rmw_xchg(0, 0));
    printf("xchg(-7,42)=%ld\n", _atomic_rmw_xchg(-7, 42));
    printf("xchg(999,-1)=%ld\n", _atomic_rmw_xchg(999, -1));
    return 0;
}
"#;
    let r = differential_test("atomic_rmw_xchg", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_atomic_cmpxchg() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_atomic_cmpxchg_module();
    let c_source = r#"
#include <stdio.h>
#include <stdatomic.h>

#ifndef EXTERN_ONLY
long _atomic_cmpxchg(long init, long expected, long desired) {
    _Atomic long s = init;
    long exp = expected;
    /* strong cmpxchg: on success writes desired; on failure writes the actual
       value into exp. The trust_ir CmpXchg result is the PREVIOUS value, which
       equals `init` here (the value the slot held before the attempt). */
    atomic_compare_exchange_strong_explicit(
        &s, &exp, desired, memory_order_seq_cst, memory_order_seq_cst);
    long old = init; /* previous value at the slot */
    long final = atomic_load_explicit(&s, memory_order_seq_cst);
    return old * 1000 + final;
}
#endif
#ifdef EXTERN_ONLY
extern long _atomic_cmpxchg(long init, long expected, long desired);
#endif

int main(void) {
    /* success: init==expected => swap to desired */
    printf("cx(5,5,9)=%ld\n", _atomic_cmpxchg(5, 5, 9));
    /* failure: init!=expected => slot unchanged */
    printf("cx(5,7,9)=%ld\n", _atomic_cmpxchg(5, 7, 9));
    printf("cx(0,0,42)=%ld\n", _atomic_cmpxchg(0, 0, 42));
    printf("cx(-1,-1,100)=%ld\n", _atomic_cmpxchg(-1, -1, 100));
    printf("cx(8,3,3)=%ld\n", _atomic_cmpxchg(8, 3, 3));
    return 0;
}
"#;
    let r = differential_test("atomic_cmpxchg", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_atomic_fence() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_atomic_fence_module();
    let c_source = r#"
#include <stdio.h>
#include <stdatomic.h>

#ifndef EXTERN_ONLY
long _atomic_fence(long a, long b) {
    _Atomic long s;
    atomic_store_explicit(&s, a, memory_order_seq_cst);
    atomic_thread_fence(memory_order_seq_cst);
    atomic_store_explicit(&s, b, memory_order_seq_cst);
    atomic_thread_fence(memory_order_seq_cst);
    return atomic_load_explicit(&s, memory_order_seq_cst);
}
#endif
#ifdef EXTERN_ONLY
extern long _atomic_fence(long a, long b);
#endif

int main(void) {
    printf("fence(1,2)=%ld\n", _atomic_fence(1, 2));
    printf("fence(0,0)=%ld\n", _atomic_fence(0, 0));
    printf("fence(-3,99)=%ld\n", _atomic_fence(-3, 99));
    printf("fence(7,7)=%ld\n", _atomic_fence(7, 7));
    return 0;
}
"#;
    let r = differential_test("atomic_fence", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}
