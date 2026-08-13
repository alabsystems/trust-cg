// trust-cg-codegen/tests/e2e_x86_64_indirect_calls.rs - x86-64 indirect-call oracle
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Differential testing of x86-64 `CallIndirect` (calls through a function
// pointer selected at runtime) against clang's function-pointer dispatch.
//
// The trust_ir module defines two leaf operations (`_add_op`, `_sub_op`),
// then a dispatcher (`_dispatch`) that picks one of their addresses with a
// `Select` over a selector argument and invokes it via `CallIndirect`. The C
// reference performs the same selection through a `long (*)(long,long)`
// function pointer.
//
// The trust_ir interpreter returns Unsupported for `CallIndirect`, so this is
// DIFFERENTIAL-ONLY (trust-cg vs clang). Host: x86-64 macOS.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    Block as TrustIrBlock, BlockId, CallingConv, Constant, FuncId, FuncTy,
    Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, Ty, ValueId,
};

// =============================================================================
// Host gating + harness (mirrors e2e_x86_64_atomics.rs)
// =============================================================================

fn x86_64_oracle_enabled() -> bool {
    if !cfg!(target_arch = "x86_64") {
        eprintln!("SKIP: x86-64 indirect-call oracle requires an x86-64 host");
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
    let dir = std::env::temp_dir().join(format!("trust_cg_x86_64_indirect_{}", test_name));
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

    eprintln!("=== x86-64 indirect-call differential: {} ===", test_name);
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
// Function pointers are supplied by the C driver as runtime arguments, so the
// trust-cg path never needs to relocate a function-symbol address (raw x86-64
// Mach-O emission does not support GlobalRef/FnDef relocation). This still
// exercises the full `CallIndirect` lowering: the callee is a register-held
// function pointer.
// =============================================================================

/// `fn _call_through(fp: ptr, a: i64, b: i64) -> i64 { fp(a, b) }`
///
/// A single indirect call through a function pointer passed in as the first
/// argument. The C driver chooses which function to pass.
fn build_call_through_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("indirect_test");

    // Callee signature (i64, i64) -> i64
    let binop_ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    // _call_through(ptr, i64, i64) -> i64
    let ct_ft = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    let mut func = TrustIrFunction::new(FuncId::new(0), "_call_through", ct_ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::Ptr), // fp
            (ValueId::new(1), Ty::I64), // a
            (ValueId::new(2), Ty::I64), // b
        ],
        body: vec![
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(0),
                sig: binop_ft,
                args: vec![ValueId::new(1), ValueId::new(2)],
                calling_conv: CallingConv::C,
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

/// `fn _dispatch(sel, fp0, fp1, a, b) -> (sel != 0 ? fp0 : fp1)(a, b)`
///
/// Runtime selection between two function pointers (passed in by the driver)
/// via `Select`, then a single `CallIndirect`. Exercises the selection +
/// indirect-call interaction without function-symbol relocation.
fn build_dispatch_select_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("indirect_test");

    let binop_ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    // _dispatch(i64 sel, ptr fp0, ptr fp1, i64 a, i64 b) -> i64
    let dispatch_ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::Ptr, Ty::Ptr, Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    let mut func = TrustIrFunction::new(FuncId::new(0), "_dispatch", dispatch_ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::I64), // sel
            (ValueId::new(1), Ty::Ptr), // fp0
            (ValueId::new(2), Ty::Ptr), // fp1
            (ValueId::new(3), Ty::I64), // a
            (ValueId::new(4), Ty::I64), // b
        ],
        body: vec![
            // zero = 0
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(5)),
            // cond = sel != 0
            InstrNode::new(Inst::ICmp {
                op: trust_ir::ICmpOp::Ne,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(5),
            })
            .with_result(ValueId::new(6)),
            // chosen = cond ? fp0 : fp1
            InstrNode::new(Inst::Select {
                ty: Ty::Ptr,
                cond: ValueId::new(6),
                then_val: ValueId::new(1),
                else_val: ValueId::new(2),
            })
            .with_result(ValueId::new(7)),
            // r = chosen(a, b)
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(7),
                sig: binop_ft,
                args: vec![ValueId::new(3), ValueId::new(4)],
                calling_conv: CallingConv::C,
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

// =============================================================================
// Tests
// =============================================================================

#[test]
fn test_x86_64_call_through_pointer() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_call_through_module();
    // The driver supplies the function pointer; both add and sub are exercised.
    let c_source = r#"
#include <stdio.h>

typedef long (*binop_t)(long, long);

static long add_op(long a, long b) { return a + b; }
static long sub_op(long a, long b) { return a - b; }
static long mul_op(long a, long b) { return a * b; }

#ifndef EXTERN_ONLY
long _call_through(binop_t fp, long a, long b) {
    return fp(a, b);
}
#endif
#ifdef EXTERN_ONLY
extern long _call_through(binop_t fp, long a, long b);
#endif

int main(void) {
    printf("add(10,3)=%ld\n", _call_through(&add_op, 10, 3));
    printf("sub(10,3)=%ld\n", _call_through(&sub_op, 10, 3));
    printf("mul(10,3)=%ld\n", _call_through(&mul_op, 10, 3));
    printf("add(-4,9)=%ld\n", _call_through(&add_op, -4, 9));
    printf("sub(0,0)=%ld\n", _call_through(&sub_op, 0, 0));
    printf("mul(-7,-6)=%ld\n", _call_through(&mul_op, -7, -6));
    return 0;
}
"#;
    let r = differential_test("call_through_pointer", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_dispatch_select() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_dispatch_select_module();
    let c_source = r#"
#include <stdio.h>

typedef long (*binop_t)(long, long);

static long add_op(long a, long b) { return a + b; }
static long sub_op(long a, long b) { return a - b; }

#ifndef EXTERN_ONLY
long _dispatch(long sel, binop_t fp0, binop_t fp1, long a, long b) {
    binop_t chosen = (sel != 0) ? fp0 : fp1;
    return chosen(a, b);
}
#endif
#ifdef EXTERN_ONLY
extern long _dispatch(long sel, binop_t fp0, binop_t fp1, long a, long b);
#endif

int main(void) {
    /* sel != 0 selects fp0 (add); sel == 0 selects fp1 (sub) */
    printf("d(1,10,3)=%ld\n", _dispatch(1, &add_op, &sub_op, 10, 3));
    printf("d(0,10,3)=%ld\n", _dispatch(0, &add_op, &sub_op, 10, 3));
    printf("d(5,-4,9)=%ld\n", _dispatch(5, &add_op, &sub_op, -4, 9));
    printf("d(0,-4,9)=%ld\n", _dispatch(0, &add_op, &sub_op, -4, 9));
    printf("d(-1,100,250)=%ld\n", _dispatch(-1, &add_op, &sub_op, 100, 250));
    printf("d(0,100,250)=%ld\n", _dispatch(0, &add_op, &sub_op, 100, 250));
    return 0;
}
"#;
    let r = differential_test("dispatch_select", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}
