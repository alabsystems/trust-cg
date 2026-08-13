// trust-cg-codegen/tests/e2e_scalar_if_alloca_soundness.rs
//
// Regression for the ty scalar-primed IF-THEN-ELSE soundness bug.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ty lowers a TLA+ action `x' = (IF x = 0 THEN 5 ELSE x)` to a diamond CFG
// whose two arms each `store` the selected value into a SHARED register-file
// `alloca` slot, with a single `load` from that slot in the merge block. This
// is the canonical mem-backed (non-block-param) phi shape produced by ty's
// next-state lowering.
//
// Where the soundness bug actually lived: it was NOT a trust-cg codegen bug.
// trust-cg compiles this exact diamond/alloca shape CORRECTLY at every opt
// level (this test proves it: scalar_if(0) == 5). The collapse was upstream,
// in ty's bytecode -> trust-ir lowering, which carried flow-INSENSITIVE
// per-register state-alias provenance across the IF merge and emitted `x' = x`
// (re-copying the OLD x slot) instead of the correct diamond above — so the
// model checker saw no successor distinct from the initial state and vacuously
// passed a violated invariant. That root cause is fixed in ty's `tla-ir`
// lowering (`invalidate_all_register_tracking_at_merge`).
//
// This test is the trust-cg-side guard for the corrected shape: it pins, end
// to end (compile -> link -> run), that once ty emits the correct mem-backed
// phi, trust-cg's lowering of a shared-alloca store-in-both-arms / load-in-
// merge diamond keeps the THEN value (5), never silently reverting to the
// ELSE / unchanged value.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{ICmpOp, Module as TrustIrModule, Ty};
use trust_ir_build::ModuleBuilder;

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
    let dir = std::env::temp_dir().join(format!("trust_cg_e2e_scalar_if_{}", test_name));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");
    dir
}

fn cleanup(dir: &Path) {
    let _ = fs::remove_dir_all(dir);
}

fn compile_module_at(module: &TrustIrModule, opt_level: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level,
        trace_level: CompilerTraceLevel::Full,
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

/// ty's compiled-action default is O1; test every level so a pass-specific
/// miscompile cannot hide behind the level the default happens to use.
const OPT_LEVELS: &[OptLevel] = &[OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn link_and_run(dir: &Path, obj_bytes: &[u8], obj_name: &str, driver_src: &str) -> (i32, String) {
    let obj_path = dir.join(format!("{}.o", obj_name));
    fs::write(&obj_path, obj_bytes).expect("write .o");

    let driver_path = dir.join("driver.c");
    fs::write(&driver_path, driver_src).expect("write driver.c");

    let binary_path = dir.join(format!("test_{}", obj_name));

    let link_out = Command::new("cc")
        .args([
            driver_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-o",
            binary_path.to_str().unwrap(),
        ])
        .output()
        .expect("cc should be available");
    assert!(
        link_out.status.success(),
        "linking failed: {}",
        String::from_utf8_lossy(&link_out.stderr)
    );

    let run_out = Command::new(binary_path.to_str().unwrap())
        .output()
        .expect("run binary");
    let stdout = String::from_utf8_lossy(&run_out.stdout).to_string();
    let exit_code = run_out.status.code().unwrap_or(-1);
    (exit_code, stdout)
}

// fn _scalar_if(x) -> i64 {
//     let r = alloca i64;          // shared register-file slot (the IF result)
//     if x == 0 { store r, 5 }     // THEN arm
//     else      { store r, x }     // ELSE arm
//     return load r;               // merge: mem-backed phi
// }
fn build_scalar_if_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("e2e_scalar_if_alloca");
    let ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("_scalar_if", ty);

    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I64);
    let bb_then = fb.create_block();
    let bb_else = fb.create_block();
    let bb_merge = fb.create_block();

    fb.switch_to_block(entry);
    // Allocate the shared result slot in the entry block (ty's register-file
    // alloca lives in the entry block, like a Cranelift/LLVM stack slot).
    let slot = fb.alloca(Ty::I64);
    let zero = fb.iconst(Ty::I64, 0);
    let cmp = fb.icmp(ICmpOp::Eq, Ty::I64, x, zero);
    // condbr: then when cond is TRUE (x == 0).
    fb.condbr(cmp, bb_then, vec![], bb_else, vec![]);

    fb.switch_to_block(bb_then);
    let five = fb.iconst(Ty::I64, 5);
    fb.store(Ty::I64, slot, five);
    fb.br(bb_merge, vec![]);

    fb.switch_to_block(bb_else);
    fb.store(Ty::I64, slot, x);
    fb.br(bb_merge, vec![]);

    fb.switch_to_block(bb_merge);
    let result = fb.load(Ty::I64, slot);
    fb.ret(vec![result]);

    fb.build();
    mb.build()
}

#[test]
fn e2e_scalar_if_alloca_then_value_survives() {
    if !is_aarch64() || !has_cc() {
        eprintln!("Skipping: not AArch64 or cc not available");
        return;
    }

    let module = build_scalar_if_module();

    // _scalar_if(0) must take the THEN arm and return 5; _scalar_if(7) takes
    // the ELSE arm and returns 7. The soundness bug returned 0 for input 0
    // (the ELSE/unchanged value), collapsing the state space.
    let driver = r#"
#include <stdio.h>

extern long _scalar_if(long x);

int main(void) {
    long r0 = _scalar_if(0);
    long r7 = _scalar_if(7);
    printf("scalar_if(0)=%ld scalar_if(7)=%ld\n", r0, r7);
    if (r0 != 5) return 1; /* THEN arm dropped -> soundness bug */
    if (r7 != 7) return 2; /* ELSE arm wrong */
    return 0;
}
"#;

    for &opt in OPT_LEVELS {
        let dir = make_test_dir(&format!("then_value_{:?}", opt));
        let obj_bytes = compile_module_at(&module, opt);
        let (exit_code, stdout) = link_and_run(&dir, &obj_bytes, "scalar_if", driver);
        eprintln!("scalar_if [{:?}] stdout: {}", opt, stdout.trim());
        assert_eq!(
            exit_code, 0,
            "scalar_if mem-backed-phi miscompile at {:?} (exit {}): \
             1=scalar_if(0)!=5 (THEN arm dropped, the soundness bug), \
             2=scalar_if(7)!=7. stdout: {}",
            opt, exit_code, stdout
        );
        cleanup(&dir);
    }
}

// The full ty next-state ABI shape: `fn(state_in*, state_out*)` where the
// function loads `x` from `state_in[0]`, runs the diamond-alloca IF, and stores
// the IF result into `state_out[0]`. This mirrors ty's compiled action exactly
// (LoadVar from state_in, StoreVar to state_out via GEP).
//
// fn _scalar_if_state(in: *const i64, out: *mut i64) {
//     let r = alloca i64;
//     let x = load in[0];
//     if x == 0 { store r, 5 } else { store r, x }
//     store out[0], load r;
// }
fn build_scalar_if_state_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("e2e_scalar_if_state");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr], vec![]);
    let mut fb = mb.function("_scalar_if_state", ty);

    let entry = fb.create_block();
    let state_in = fb.add_block_param(entry, Ty::Ptr);
    let state_out = fb.add_block_param(entry, Ty::Ptr);
    let bb_then = fb.create_block();
    let bb_else = fb.create_block();
    let bb_merge = fb.create_block();

    fb.switch_to_block(entry);
    let slot = fb.alloca(Ty::I64);
    let idx0 = fb.iconst(Ty::I64, 0);
    let in_ptr = fb.gep(Ty::I64, state_in, vec![idx0]);
    let x = fb.load(Ty::I64, in_ptr);
    let zero = fb.iconst(Ty::I64, 0);
    let cmp = fb.icmp(ICmpOp::Eq, Ty::I64, x, zero);
    fb.condbr(cmp, bb_then, vec![], bb_else, vec![]);

    fb.switch_to_block(bb_then);
    let five = fb.iconst(Ty::I64, 5);
    fb.store(Ty::I64, slot, five);
    fb.br(bb_merge, vec![]);

    fb.switch_to_block(bb_else);
    fb.store(Ty::I64, slot, x);
    fb.br(bb_merge, vec![]);

    fb.switch_to_block(bb_merge);
    let result = fb.load(Ty::I64, slot);
    let idx0b = fb.iconst(Ty::I64, 0);
    let out_ptr = fb.gep(Ty::I64, state_out, vec![idx0b]);
    fb.store(Ty::I64, out_ptr, result);
    fb.ret(vec![]);

    fb.build();
    mb.build()
}

#[test]
fn e2e_scalar_if_state_buffer_then_value_survives() {
    if !is_aarch64() || !has_cc() {
        eprintln!("Skipping: not AArch64 or cc not available");
        return;
    }

    let module = build_scalar_if_state_module();

    let driver = r#"
#include <stdio.h>

extern void _scalar_if_state(const long* in, long* out);

int main(void) {
    long in0[1] = {0};
    long out0[1] = {-1};
    _scalar_if_state(in0, out0);

    long in7[1] = {7};
    long out7[1] = {-1};
    _scalar_if_state(in7, out7);

    printf("state_if(0)=%ld state_if(7)=%ld\n", out0[0], out7[0]);
    if (out0[0] != 5) return 1; /* THEN arm dropped -> soundness bug */
    if (out7[0] != 7) return 2; /* ELSE arm wrong */
    return 0;
}
"#;

    for &opt in OPT_LEVELS {
        let dir = make_test_dir(&format!("state_buffer_{:?}", opt));
        let obj_bytes = compile_module_at(&module, opt);
        let (exit_code, stdout) = link_and_run(&dir, &obj_bytes, "scalar_if_state", driver);
        eprintln!("scalar_if_state [{:?}] stdout: {}", opt, stdout.trim());
        assert_eq!(
            exit_code, 0,
            "scalar_if_state mem-backed-phi miscompile at {:?} (exit {}): \
             1=state_if(0)!=5 (THEN arm dropped, the soundness bug), \
             2=state_if(7)!=7. stdout: {}",
            opt, exit_code, stdout
        );
        cleanup(&dir);
    }
}

// The byte-for-byte trust-ir module ty emits for the `IfScalar` action
// `x' = (IF x = 0 THEN 5 ELSE x) /\ f' = f`, captured from the ty native
// replay artifact (`TY_TRUST_CG_REPLAY_ARTIFACT_DIR`, stage
// `compile_module_native.pre_jit`, opt level O3). This is exactly the module
// `compile_module_native` hands to `translate_module`. Compiling it and
// running the action with `state_in[x]=0` must write `state_out[x]=5`.
//
// ABI: fn(out: ptr, state_in: ptr, state_out: ptr, len: i32). `x` lives at
// flat slot index 1 (an i32 GEP index); slot 0 is `f`. `out` is the JitCallOut.
const TY_IF_SCALAR_ACTION_TRUST_IR: &str = r#"; TrustIr text format v1
module "ty_if_scalar_action_replay"

functy.0 = (ptr, ptr, ptr, i32) -> ()

fn @ty_if_scalar_action(functy.0) {
bb0(%0: ptr, %1: ptr, %2: ptr, %3: i32):
    %4 = alloca i64
    %5 = alloca i64
    %6 = alloca i64
    %7 = alloca i64
    %8 = alloca i64
    %9 = alloca i64
    %10 = alloca i64
    %11 = alloca i64
    %12 = alloca i64
    %13 = alloca i64
    %14 = alloca i64
    %15 = alloca i64
    %16 = const i64 1
    store i64 %16, ptr %11
    %17 = const i32 1
    %18 = gep i64, ptr %1, %17
    %19 = load i64, ptr %18
    store i64 %19, ptr %5
    %20 = const i64 0
    store i64 %20, ptr %6
    %21 = load i64, ptr %5
    %22 = load i64, ptr %6
    %23 = icmp eq i64 %21, %22
    %24 = zext bool %23 to i64
    store i64 %24, ptr %7
    %25 = load i64, ptr %7
    %26 = const i64 0
    %27 = icmp ne i64 %25, %26
    condbr %27, bb1, bb2
bb1:
    %28 = const i64 5
    store i64 %28, ptr %9
    %29 = load i64, ptr %9
    store i64 %29, ptr %8
    br bb3
bb2:
    %30 = const i32 1
    %31 = gep i64, ptr %1, %30
    %32 = load i64, ptr %31
    store i64 %32, ptr %10
    %33 = load i64, ptr %10
    store i64 %33, ptr %8
    br bb3
bb3:
    %34 = load i64, ptr %8
    %35 = const i32 1
    %36 = gep i64, ptr %2, %35
    store i64 %34, ptr %36
    %37 = load i64, ptr %11
    store i64 %37, ptr %12
    %38 = load i64, ptr %12
    %39 = const i64 0
    %40 = icmp ne i64 %38, %39
    condbr %40, bb4, bb5
bb4:
    %41 = const i64 1
    store i64 %41, ptr %15
    %42 = const i32 0
    %43 = gep i64, ptr %1, %42
    %44 = load i64, ptr %43
    store i64 %44, ptr %14
    %45 = load i64, ptr %14
    %46 = const i32 0
    %47 = gep i64, ptr %2, %46
    store i64 %45, ptr %47
    %48 = load i64, ptr %15
    store i64 %48, ptr %12
    br bb5
bb5:
    %49 = load i64, ptr %12
    store i64 %49, ptr %4
    %50 = load i64, ptr %4
    %51 = const i64 0
    %52 = icmp ne i64 %50, %51
    %53 = zext bool %52 to i64
    %54 = const i64 0
    %55 = gep i8, ptr %0, %54
    %56 = const i8 0
    store i8 %56, ptr %55
    %57 = const i64 8
    %58 = gep i8, ptr %0, %57
    store i64 %53, ptr %58
    ret
}
"#;

#[test]
fn e2e_ty_if_scalar_action_replay_writes_then_value() {
    if !is_aarch64() || !has_cc() {
        eprintln!("Skipping: not AArch64 or cc not available");
        return;
    }

    let module = trust_ir::parser::parse_module(TY_IF_SCALAR_ACTION_TRUST_IR)
        .expect("ty replay module should parse");

    // JitCallOut is opaque to this test; the action only writes a status byte
    // at out[0] and an i64 at out[8]. A 16-byte zeroed scratch buffer covers it.
    let driver = r#"
#include <stdio.h>
#include <string.h>

extern void ty_if_scalar_action(void* out, const long* state_in, long* state_out, int len);

int main(void) {
    char out[64];

    /* x = state_in[1] = 0 (initial), f = state_in[0] = 0. */
    long in0[2]  = {0, 0};
    long out0[2] = {-1, -1};
    memset(out, 0, sizeof(out));
    ty_if_scalar_action(out, in0, out0, 2);

    /* x = state_in[1] = 7 (else arm). */
    long in7[2]  = {0, 7};
    long out7[2] = {-1, -1};
    memset(out, 0, sizeof(out));
    ty_if_scalar_action(out, in7, out7, 2);

    printf("ty_action x=0 -> x'=%ld ; x=7 -> x'=%ld\n", out0[1], out7[1]);
    if (out0[1] != 5) return 1; /* THEN arm dropped -> the ty soundness bug */
    if (out7[1] != 7) return 2; /* ELSE arm wrong */
    return 0;
}
"#;

    for &opt in OPT_LEVELS {
        let dir = make_test_dir(&format!("ty_replay_{:?}", opt));
        let obj_bytes = compile_module_at(&module, opt);
        let (exit_code, stdout) = link_and_run(&dir, &obj_bytes, "ty_if_action", driver);
        eprintln!("ty_if_action [{:?}] stdout: {}", opt, stdout.trim());
        assert_eq!(
            exit_code, 0,
            "ty IfScalar action miscompile at {:?} (exit {}): \
             1=x'(x=0)!=5 (THEN arm dropped, the soundness bug), \
             2=x'(x=7)!=7. stdout: {}",
            opt, exit_code, stdout
        );
        cleanup(&dir);
    }
}
