// trust-cg-codegen/tests/e2e_x86_64_checked_arith.rs - x86-64 checked-arithmetic oracle
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Differential testing of x86-64 overflow-checked arithmetic against clang's
// `__builtin_*_overflow` builtins. Covers all six checked ops:
//   - CheckedSadd / CheckedSsub / CheckedSmul  (signed, via Ty::I64)
//   - CheckedUadd / CheckedUsub / CheckedUmul  (unsigned, via Ty::U64)
//
// trust_ir `Inst::Overflow { op, ty, lhs, rhs }` produces TWO results:
//   results[0] = wrapped arithmetic value
//   results[1] = overflow flag (bool)
// Signedness is selected by the operand `ty` (I64 => signed checked op,
// U64 => unsigned checked op). On I64/U64 the adapter maps directly to the
// dedicated Checked{S,U}{add,sub,mul} LIR opcodes (adapter.rs translate_overflow).
//
// Each op is tested via TWO trust_ir functions sharing the same Overflow
// instruction: `_OP_v` returns the wrapped value; `_OP_o` returns the overflow
// bit. We assert BOTH the wrapped result AND the overflow bit against clang.
//
// This is DIFFERENTIAL-ONLY (trust-cg vs clang): the trust_ir interpreter's
// Overflow handler hardcodes the overflow flag to `false` (interpreter.rs), so
// it cannot serve as an oracle for the overflow bit. Host: x86-64 macOS.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    Block as TrustIrBlock, BlockId, CastOp, FuncId, FuncTy, Function as TrustIrFunction, Inst,
    InstrNode, Module as TrustIrModule, OverflowOp, Ty, ValueId,
};

// =============================================================================
// Host gating + harness
// =============================================================================

fn x86_64_oracle_enabled() -> bool {
    if !cfg!(target_arch = "x86_64") {
        eprintln!("SKIP: x86-64 checked-arith oracle requires an x86-64 host");
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
    let dir = std::env::temp_dir().join(format!("trust_cg_x86_64_checked_{}", test_name));
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
        return Err(format!("clang compile failed: {}", stderr));
    }
    let clang_run = Command::new(&clang_bin)
        .output()
        .map_err(|e| format!("run clang binary: {}", e))?;
    let clang_stdout = String::from_utf8_lossy(&clang_run.stdout).to_string();
    let clang_exit = clang_run.status.code().unwrap_or(-1);

    eprintln!("=== x86-64 checked-arith differential: {} ===", test_name);
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

// =============================================================================
// trust_ir builder
//
// One module with two functions for a given (op, ty):
//   _NAME_v(a, b) -> wrapped value (as i64)
//   _NAME_o(a, b) -> overflow bit (as i32)
// Both contain the same `Inst::Overflow { op, ty, .. }`.
//
// `op_ty` is the integer type used for the checked op (I64 signed / U64
// unsigned). The wrapped value is widened/extended back to i64 for return.
// =============================================================================

fn build_checked_module(name_v: &str, name_o: &str, op: OverflowOp, op_ty: Ty) -> TrustIrModule {
    let mut module = TrustIrModule::new("checked_test");

    // value-returning fn type: (op_ty, op_ty) -> op_ty
    let ft_v = module.add_func_type(FuncTy {
        params: vec![op_ty.clone(), op_ty.clone()],
        returns: vec![op_ty.clone()],
        is_vararg: false,
    });
    // overflow-bit fn type: (op_ty, op_ty) -> i32
    let ft_o = module.add_func_type(FuncTy {
        params: vec![op_ty.clone(), op_ty.clone()],
        returns: vec![Ty::I32],
        is_vararg: false,
    });

    // --- _NAME_v: return wrapped value ---
    let mut fv = TrustIrFunction::new(FuncId::new(0), name_v, ft_v, BlockId::new(0));
    fv.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), op_ty.clone()),
            (ValueId::new(1), op_ty.clone()),
        ],
        body: vec![
            // (wrapped, overflow) = op(a, b); only wrapped is returned
            InstrNode::new(Inst::Overflow {
                op,
                ty: op_ty.clone(),
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_results([ValueId::new(2), ValueId::new(3)]),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(fv);

    // --- _NAME_o: return overflow bit zero-extended to i32 ---
    let mut fo = TrustIrFunction::new(FuncId::new(1), name_o, ft_o, BlockId::new(0));
    fo.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), op_ty.clone()),
            (ValueId::new(1), op_ty.clone()),
        ],
        body: vec![
            InstrNode::new(Inst::Overflow {
                op,
                ty: op_ty.clone(),
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_results([ValueId::new(2), ValueId::new(3)]),
            // ovf_i32 = zext(overflow bit) to i32
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::I32,
                operand: ValueId::new(3),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(4)],
            }),
        ],
    }];
    module.add_function(fo);

    module
}

// =============================================================================
// Tests
// =============================================================================

#[test]
fn test_x86_64_checked_sadd() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_checked_module("_sadd_v", "_sadd_o", OverflowOp::AddOverflow, Ty::I64);
    let c_source = r#"
#include <stdio.h>
#include <limits.h>

#ifndef EXTERN_ONLY
long _sadd_v(long a, long b) { long r; __builtin_saddl_overflow(a, b, &r); return r; }
int  _sadd_o(long a, long b) { long r; return __builtin_saddl_overflow(a, b, &r) ? 1 : 0; }
#endif
#ifdef EXTERN_ONLY
extern long _sadd_v(long a, long b);
extern int  _sadd_o(long a, long b);
#endif

static void run(long a, long b) {
    printf("v(%ld,%ld)=%ld o=%d\n", a, b, _sadd_v(a, b), _sadd_o(a, b));
}
int main(void) {
    run(1, 2);
    run(-5, 3);
    run(LONG_MAX, 1);
    run(LONG_MIN, -1);
    run(LONG_MAX, LONG_MAX);
    run(LONG_MIN, LONG_MIN);
    run(0, 0);
    run(LONG_MAX, -1);
    return 0;
}
"#;
    let r = differential_test("checked_sadd", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_checked_ssub() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_checked_module("_ssub_v", "_ssub_o", OverflowOp::SubOverflow, Ty::I64);
    let c_source = r#"
#include <stdio.h>
#include <limits.h>

#ifndef EXTERN_ONLY
long _ssub_v(long a, long b) { long r; __builtin_ssubl_overflow(a, b, &r); return r; }
int  _ssub_o(long a, long b) { long r; return __builtin_ssubl_overflow(a, b, &r) ? 1 : 0; }
#endif
#ifdef EXTERN_ONLY
extern long _ssub_v(long a, long b);
extern int  _ssub_o(long a, long b);
#endif

static void run(long a, long b) {
    printf("v(%ld,%ld)=%ld o=%d\n", a, b, _ssub_v(a, b), _ssub_o(a, b));
}
int main(void) {
    run(5, 3);
    run(-5, 3);
    run(LONG_MIN, 1);
    run(LONG_MAX, -1);
    run(LONG_MIN, LONG_MAX);
    run(LONG_MAX, LONG_MIN);
    run(0, LONG_MIN);
    run(7, 7);
    return 0;
}
"#;
    let r = differential_test("checked_ssub", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_checked_smul() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_checked_module("_smul_v", "_smul_o", OverflowOp::MulOverflow, Ty::I64);
    let c_source = r#"
#include <stdio.h>
#include <limits.h>

#ifndef EXTERN_ONLY
long _smul_v(long a, long b) { long r; __builtin_smull_overflow(a, b, &r); return r; }
int  _smul_o(long a, long b) { long r; return __builtin_smull_overflow(a, b, &r) ? 1 : 0; }
#endif
#ifdef EXTERN_ONLY
extern long _smul_v(long a, long b);
extern int  _smul_o(long a, long b);
#endif

static void run(long a, long b) {
    printf("v(%ld,%ld)=%ld o=%d\n", a, b, _smul_v(a, b), _smul_o(a, b));
}
int main(void) {
    run(3, 4);
    run(-3, 4);
    run(LONG_MAX, 2);
    run(LONG_MIN, -1);
    run(LONG_MIN, 2);
    run(1L << 40, 1L << 40);
    run(0, LONG_MAX);
    run(-1, LONG_MIN);
    return 0;
}
"#;
    let r = differential_test("checked_smul", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_checked_uadd() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_checked_module("_uadd_v", "_uadd_o", OverflowOp::AddOverflow, Ty::U64);
    let c_source = r#"
#include <stdio.h>
#include <limits.h>

#ifndef EXTERN_ONLY
unsigned long _uadd_v(unsigned long a, unsigned long b) { unsigned long r; __builtin_uaddl_overflow(a, b, &r); return r; }
int           _uadd_o(unsigned long a, unsigned long b) { unsigned long r; return __builtin_uaddl_overflow(a, b, &r) ? 1 : 0; }
#endif
#ifdef EXTERN_ONLY
extern unsigned long _uadd_v(unsigned long a, unsigned long b);
extern int           _uadd_o(unsigned long a, unsigned long b);
#endif

static void run(unsigned long a, unsigned long b) {
    printf("v(%lu,%lu)=%lu o=%d\n", a, b, _uadd_v(a, b), _uadd_o(a, b));
}
int main(void) {
    run(1, 2);
    run(ULONG_MAX, 1);
    run(ULONG_MAX, ULONG_MAX);
    run(0, 0);
    run(ULONG_MAX - 5, 5);
    run(ULONG_MAX - 5, 6);
    return 0;
}
"#;
    let r = differential_test("checked_uadd", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_checked_usub() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_checked_module("_usub_v", "_usub_o", OverflowOp::SubOverflow, Ty::U64);
    let c_source = r#"
#include <stdio.h>
#include <limits.h>

#ifndef EXTERN_ONLY
unsigned long _usub_v(unsigned long a, unsigned long b) { unsigned long r; __builtin_usubl_overflow(a, b, &r); return r; }
int           _usub_o(unsigned long a, unsigned long b) { unsigned long r; return __builtin_usubl_overflow(a, b, &r) ? 1 : 0; }
#endif
#ifdef EXTERN_ONLY
extern unsigned long _usub_v(unsigned long a, unsigned long b);
extern int           _usub_o(unsigned long a, unsigned long b);
#endif

static void run(unsigned long a, unsigned long b) {
    printf("v(%lu,%lu)=%lu o=%d\n", a, b, _usub_v(a, b), _usub_o(a, b));
}
int main(void) {
    run(5, 3);
    run(3, 5);
    run(0, 1);
    run(ULONG_MAX, ULONG_MAX);
    run(0, ULONG_MAX);
    run(10, 10);
    return 0;
}
"#;
    let r = differential_test("checked_usub", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_checked_umul() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_checked_module("_umul_v", "_umul_o", OverflowOp::MulOverflow, Ty::U64);
    let c_source = r#"
#include <stdio.h>
#include <limits.h>

#ifndef EXTERN_ONLY
unsigned long _umul_v(unsigned long a, unsigned long b) { unsigned long r; __builtin_umull_overflow(a, b, &r); return r; }
int           _umul_o(unsigned long a, unsigned long b) { unsigned long r; return __builtin_umull_overflow(a, b, &r) ? 1 : 0; }
#endif
#ifdef EXTERN_ONLY
extern unsigned long _umul_v(unsigned long a, unsigned long b);
extern int           _umul_o(unsigned long a, unsigned long b);
#endif

static void run(unsigned long a, unsigned long b) {
    printf("v(%lu,%lu)=%lu o=%d\n", a, b, _umul_v(a, b), _umul_o(a, b));
}
int main(void) {
    run(3, 4);
    run(ULONG_MAX, 2);
    run(1UL << 32, 1UL << 32);
    run(1UL << 32, (1UL << 32) - 1);
    run(0, ULONG_MAX);
    run(ULONG_MAX, ULONG_MAX);
    run(1, ULONG_MAX);
    return 0;
}
"#;
    let r = differential_test("checked_umul", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}
