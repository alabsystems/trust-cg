// trust-cg-codegen/tests/e2e_x86_64_vector_fp.rs - x86-64 packed vector FP oracle
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Differential testing of x86-64 PACKED floating-point arithmetic lowering:
// `<4 x f32>` and `<2 x f64>` FAdd/FSub/FMul/FDiv lowered to the SSE/SSE2
// ADDPS/ADDPD instruction families. clang is the golden oracle.
//
// Two differential families are exercised:
//
//   * MEMORY FORM: each module loads two packed FP vectors from pointer
//     arguments, performs one packed FP op, and stores the result through an
//     output pointer. The C reference uses
//     `float __attribute__((vector_size(16)))` / `double vector_size(16)` and
//     the driver prints each result lane. trust-cg and clang must agree on the
//     printed lanes exactly. This directly exercises the real packed-FP machine
//     instructions end-to-end.
//
//   * PACK / ARITHMETIC / EXTRACT FORM: each module builds two packed FP
//     vectors from `Constant::Vector` literals, performs the packed FP op,
//     bitcasts the result to the matching integer vector, extracts one lane via
//     the (integer) vector dialect, and returns the lane's raw bit pattern as
//     an i64. trust-cg and clang must agree on the returned integer.
//
// ORACLE COUNT NOTE: a triple oracle (adding the trust_ir interpreter) is NOT
// used. The trust-cg-codegen crate's interpreter -- the one the x86-64 oracle
// corpus is wired to -- does not model packed vector values (vector constants
// evaluate to `Undef`; there is no `InterpreterValue::Vector`), so it cannot
// execute packed vector FP. These tests therefore stay differential (trust-cg
// vs clang). Per-lane semantic equivalence is independently established by the
// discharged SMT lowering proofs in `trust-cg-verify::all_x86_64_proofs`.
//
// Host: x86-64 macOS.

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::dialect::vector as vector_dialect;
use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, CastOp, Constant, FuncId, FuncTy,
    Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, Ty, ValueId,
};

// =============================================================================
// Host gating + harness
// =============================================================================

fn x86_64_oracle_enabled() -> bool {
    if !cfg!(target_arch = "x86_64") {
        eprintln!("SKIP: x86-64 packed-FP oracle requires an x86-64 host");
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
    let dir = std::env::temp_dir().join(format!("trust_cg_x86_64_vec_fp_{}", test_name));
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

    eprintln!("=== x86-64 packed-FP differential: {} ===", test_name);
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

/// Differential harness for integer-returning packed-FP functions: compares
/// the trust-cg compiled binary and clang on the function's i64 lane result.
///
/// NOTE ON ORACLE COUNT: a third (interpreter) oracle is intentionally omitted.
/// The trust-cg-codegen crate's interpreter (`trust_cg_codegen::interpreter`,
/// the one the x86-64 oracle corpus uses) does not model packed vector values
/// at all -- vector constants evaluate to `Undef` and there is no
/// `InterpreterValue::Vector` -- so it cannot execute packed-FP arithmetic. The
/// trust_ir interpreter does model packed vector FP, but the e2e corpus is
/// wired to the codegen interpreter, so these tests stay differential
/// (trust-cg vs clang), with clang as the golden oracle. The per-lane semantic
/// equivalence is independently established by the discharged SMT lowering
/// proofs (`all_x86_64_proofs`).
///
/// Each function takes no arguments (it builds its packed-FP inputs from
/// constants), performs the packed op, bitcasts to the matching integer vector,
/// and returns one lane's raw bit pattern as i64. `c_source` uses the
/// `-DEXTERN_ONLY` split convention.
fn differential_int(
    test_name: &str,
    module: &TrustIrModule,
    c_source: &str,
    key: &str,
) -> Result<(), String> {
    let dir = make_test_dir(test_name);

    // Oracle 1: trust-cg
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

    // Oracle 2: clang (golden)
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

    eprintln!("=== x86-64 packed-FP lane differential: {} ===", test_name);
    eprintln!("  trust-cg: {:?}", trust_cg);
    eprintln!("  clang:    {:?}", clang);

    let mut mismatches = Vec::new();
    match (trust_cg.get(key), clang.get(key)) {
        (Some(&l), Some(&k)) => {
            if l != k {
                mismatches.push(format!("  {}: trust-cg={}, clang={}", key, l, k));
            }
        }
        (l, k) => mismatches.push(format!("  {}: MISSING trust-cg={:?} clang={:?}", key, l, k)),
    }

    cleanup(&dir);
    if mismatches.is_empty() {
        eprintln!("  trust-cg AND clang AGREE");
        Ok(())
    } else {
        Err(format!(
            "DIFFERENTIAL MISMATCH {}:\n{}",
            test_name,
            mismatches.join("\n")
        ))
    }
}

// =============================================================================
// trust_ir builders -- differential (memory load/store) form
// =============================================================================

fn v4_f32() -> Ty {
    Ty::Vector(Box::new(Ty::F32), 4)
}

fn v2_f64() -> Ty {
    Ty::Vector(Box::new(Ty::F64), 2)
}

/// Build `void NAME(VEC* a, VEC* b, VEC* out) { *out = (*a) OP (*b); }` where
/// VEC is the packed FP vector type. Pointers are passed as i64 values.
fn build_packed_memform_module(name: &str, vec_ty: Ty, op: BinOp) -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::Ptr, Ty::Ptr],
        returns: vec![],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), name, ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::Ptr), // a
            (ValueId::new(1), Ty::Ptr), // b
            (ValueId::new(2), Ty::Ptr), // out
        ],
        body: vec![
            // va = *a
            InstrNode::new(Inst::Load {
                ty: vec_ty.clone(),
                ptr: ValueId::new(0),
                volatile: false,
                align: Some(16),
            })
            .with_result(ValueId::new(3)),
            // vb = *b
            InstrNode::new(Inst::Load {
                ty: vec_ty.clone(),
                ptr: ValueId::new(1),
                volatile: false,
                align: Some(16),
            })
            .with_result(ValueId::new(4)),
            // vr = va OP vb
            InstrNode::new(Inst::BinOp {
                op,
                ty: vec_ty.clone(),
                lhs: ValueId::new(3),
                rhs: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
            // *out = vr
            InstrNode::new(Inst::Store {
                ty: vec_ty.clone(),
                ptr: ValueId::new(2),
                value: ValueId::new(5),
                volatile: false,
                align: Some(16),
            }),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    module.add_function(func);
    module
}

// =============================================================================
// trust_ir builders -- triple-oracle (constant inputs, integer lane return)
// =============================================================================

/// Build `i64 NAME() { vr = consts_a OP consts_b; return (i64) bitcast(vr to
/// int-vector)[lane]; }`.
///
/// `vec_ty` is the packed FP vector type; `int_vec_ty` is the matching integer
/// vector (`<4 x i32>` for f32, `<2 x i64>` for f64); `int_lane_ty` is the
/// integer lane type (I32 / I64). The extracted integer lane is zero/sign
/// extended to i64 (for I32 we widen with ZExt to compare raw bit patterns).
#[allow(clippy::too_many_arguments)]
fn build_packed_const_lane_module(
    name: &str,
    vec_ty: Ty,
    int_vec_ty: Ty,
    int_lane_ty: Ty,
    op: BinOp,
    consts_a: Vec<f64>,
    consts_b: Vec<f64>,
    lane: u32,
) -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), name, ft, BlockId::new(0));

    let make_vec_const =
        |vals: &[f64]| Constant::Vector(vals.iter().map(|v| Constant::Float(*v)).collect());

    let mut body = Vec::new();
    let mut next = 0u32;
    let mut fresh = || {
        let v = ValueId::new(next);
        next += 1;
        v
    };

    let a = fresh();
    body.push(
        InstrNode::new(Inst::Const {
            ty: vec_ty.clone(),
            value: make_vec_const(&consts_a),
        })
        .with_result(a),
    );
    let b = fresh();
    body.push(
        InstrNode::new(Inst::Const {
            ty: vec_ty.clone(),
            value: make_vec_const(&consts_b),
        })
        .with_result(b),
    );
    let vr = fresh();
    body.push(
        InstrNode::new(Inst::BinOp {
            op,
            ty: vec_ty.clone(),
            lhs: a,
            rhs: b,
        })
        .with_result(vr),
    );
    // bitcast packed FP vector -> matching integer vector (bit-preserving).
    let ivr = fresh();
    body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::Bitcast,
            src_ty: vec_ty.clone(),
            dst_ty: int_vec_ty.clone(),
            operand: vr,
        })
        .with_result(ivr),
    );
    // extract integer lane via the vector dialect (integer lane extract).
    let lane_val = fresh();
    body.push(
        InstrNode::new(Inst::DialectOp(Box::new(vector_dialect::extract_lane(
            int_vec_ty.clone(),
            ivr,
            lane,
        ))))
        .with_result(lane_val),
    );
    // widen the lane bits to i64 (zero-extend so the raw bit pattern compares
    // equal across the three oracles).
    let ret = if int_lane_ty == Ty::I64 {
        lane_val
    } else {
        let z = fresh();
        body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: int_lane_ty.clone(),
                dst_ty: Ty::I64,
                operand: lane_val,
            })
            .with_result(z),
        );
        z
    };
    body.push(InstrNode::new(Inst::Return { values: vec![ret] }));

    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body,
    }];
    module.add_function(func);
    module
}

// =============================================================================
// Differential tests: <4 x f32>
// =============================================================================

fn v4f32_driver(func: &str, op_c: &str) -> String {
    format!(
        r#"
#include <stdio.h>
typedef float v4f __attribute__((vector_size(16)));
#ifdef EXTERN_ONLY
extern void {func}(const v4f* a, const v4f* b, v4f* out);
#else
void {func}(const v4f* a, const v4f* b, v4f* out) {{ *out = (*a) {op_c} (*b); }}
#endif
int main(void) {{
    v4f a = {{ 1.5f, -2.25f, 3.0f, 8.0f }};
    v4f b = {{ 0.5f,  4.0f,  3.0f, 2.0f }};
    v4f out;
    {func}(&a, &b, &out);
    printf("l0=%a\nl1=%a\nl2=%a\nl3=%a\n", (double)out[0], (double)out[1], (double)out[2], (double)out[3]);
    return 0;
}}
"#,
        func = func,
        op_c = op_c
    )
}

#[test]
fn v4f32_fadd_differential() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_packed_memform_module("_v4f32_add", v4_f32(), BinOp::FAdd);
    differential_test("v4f32_fadd", &module, &v4f32_driver("_v4f32_add", "+")).unwrap();
}

#[test]
fn v4f32_fsub_differential() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_packed_memform_module("_v4f32_sub", v4_f32(), BinOp::FSub);
    differential_test("v4f32_fsub", &module, &v4f32_driver("_v4f32_sub", "-")).unwrap();
}

#[test]
fn v4f32_fmul_differential() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_packed_memform_module("_v4f32_mul", v4_f32(), BinOp::FMul);
    differential_test("v4f32_fmul", &module, &v4f32_driver("_v4f32_mul", "*")).unwrap();
}

#[test]
fn v4f32_fdiv_differential() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_packed_memform_module("_v4f32_div", v4_f32(), BinOp::FDiv);
    differential_test("v4f32_fdiv", &module, &v4f32_driver("_v4f32_div", "/")).unwrap();
}

// =============================================================================
// Differential tests: <2 x f64>
// =============================================================================

fn v2f64_driver(func: &str, op_c: &str) -> String {
    format!(
        r#"
#include <stdio.h>
typedef double v2d __attribute__((vector_size(16)));
#ifdef EXTERN_ONLY
extern void {func}(const v2d* a, const v2d* b, v2d* out);
#else
void {func}(const v2d* a, const v2d* b, v2d* out) {{ *out = (*a) {op_c} (*b); }}
#endif
int main(void) {{
    v2d a = {{ 1.5, -2.25 }};
    v2d b = {{ 0.5,  4.0 }};
    v2d out;
    {func}(&a, &b, &out);
    printf("l0=%a\nl1=%a\n", out[0], out[1]);
    return 0;
}}
"#,
        func = func,
        op_c = op_c
    )
}

#[test]
fn v2f64_fadd_differential() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_packed_memform_module("_v2f64_add", v2_f64(), BinOp::FAdd);
    differential_test("v2f64_fadd", &module, &v2f64_driver("_v2f64_add", "+")).unwrap();
}

#[test]
fn v2f64_fsub_differential() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_packed_memform_module("_v2f64_sub", v2_f64(), BinOp::FSub);
    differential_test("v2f64_fsub", &module, &v2f64_driver("_v2f64_sub", "-")).unwrap();
}

#[test]
fn v2f64_fmul_differential() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_packed_memform_module("_v2f64_mul", v2_f64(), BinOp::FMul);
    differential_test("v2f64_fmul", &module, &v2f64_driver("_v2f64_mul", "*")).unwrap();
}

#[test]
fn v2f64_fdiv_differential() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_packed_memform_module("_v2f64_div", v2_f64(), BinOp::FDiv);
    differential_test("v2f64_fdiv", &module, &v2f64_driver("_v2f64_div", "/")).unwrap();
}

// =============================================================================
// Triple-oracle tests: pack lanes (via constants), arithmetic, extract one lane
// =============================================================================
//
// Each function performs the packed FP op on two constant vectors, bitcasts the
// result to the matching integer vector, and returns one lane's raw bit pattern
// as i64. The interpreter models packed vector FP + bitcast + integer lane
// extract, so all three oracles can be compared on exact bits.

/// `<4 x f32>` triple-oracle C reference: build the same constant vectors,
/// perform the op, and reinterpret the chosen lane's bits as a u32, printed as
/// a decimal integer matching the trust_ir ZExt-to-i64 result.
fn v4f32_lane_driver(func: &str, op_c: &str, key: &str, lane: usize) -> String {
    format!(
        r#"
#include <stdio.h>
#include <string.h>
#include <stdint.h>
typedef float v4f __attribute__((vector_size(16)));
#ifdef EXTERN_ONLY
extern long {func}(void);
#else
long {func}(void) {{
    v4f a = {{ 1.5f, -2.25f, 9.0f, 8.0f }};
    v4f b = {{ 0.5f,  4.0f,  3.0f, 2.0f }};
    v4f r = a {op_c} b;
    uint32_t bits;
    memcpy(&bits, ((const float*)&r) + {lane}, 4);
    return (long)(uint64_t)bits;
}}
#endif
int main(void) {{
    printf("{key}=%ld\n", {func}());
    return 0;
}}
"#,
        func = func,
        op_c = op_c,
        key = key,
        lane = lane
    )
}

/// `<2 x f64>` triple-oracle C reference.
fn v2f64_lane_driver(func: &str, op_c: &str, key: &str, lane: usize) -> String {
    format!(
        r#"
#include <stdio.h>
#include <string.h>
#include <stdint.h>
typedef double v2d __attribute__((vector_size(16)));
#ifdef EXTERN_ONLY
extern long {func}(void);
#else
long {func}(void) {{
    v2d a = {{ 1.5, -2.25 }};
    v2d b = {{ 0.5,  4.0 }};
    v2d r = a {op_c} b;
    uint64_t bits;
    memcpy(&bits, ((const double*)&r) + {lane}, 8);
    return (long)bits;
}}
#endif
int main(void) {{
    printf("{key}=%ld\n", {func}());
    return 0;
}}
"#,
        func = func,
        op_c = op_c,
        key = key,
        lane = lane
    )
}

#[test]
fn v4f32_pack_arith_extract_lane_differential() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let a = vec![1.5, -2.25, 9.0, 8.0];
    let b = vec![0.5, 4.0, 3.0, 2.0];
    // (op, c-operator, lane)
    let cases: &[(BinOp, &str, u32)] = &[
        (BinOp::FAdd, "+", 0),
        (BinOp::FSub, "-", 1),
        (BinOp::FMul, "*", 2),
        (BinOp::FDiv, "/", 3),
    ];
    for (op, op_c, lane) in cases {
        let func = format!("_v4f32_lane_{:?}_{}", op, lane).to_lowercase();
        let key = format!("v4f32_{:?}_l{}", op, lane).to_lowercase();
        let module = build_packed_const_lane_module(
            &func,
            v4_f32(),
            Ty::Vector(Box::new(Ty::I32), 4),
            Ty::I32,
            *op,
            a.clone(),
            b.clone(),
            *lane,
        );
        differential_int(
            &format!("v4f32_to_{}", func),
            &module,
            &v4f32_lane_driver(&func, op_c, &key, *lane as usize),
            &key,
        )
        .unwrap();
    }
}

#[test]
fn v2f64_pack_arith_extract_lane_differential() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let a = vec![1.5, -2.25];
    let b = vec![0.5, 4.0];
    let cases: &[(BinOp, &str, u32)] = &[
        (BinOp::FAdd, "+", 0),
        (BinOp::FSub, "-", 1),
        (BinOp::FMul, "*", 0),
        (BinOp::FDiv, "/", 1),
    ];
    for (op, op_c, lane) in cases {
        let func = format!("_v2f64_lane_{:?}_{}", op, lane).to_lowercase();
        let key = format!("v2f64_{:?}_l{}", op, lane).to_lowercase();
        let module = build_packed_const_lane_module(
            &func,
            v2_f64(),
            Ty::Vector(Box::new(Ty::I64), 2),
            Ty::I64,
            *op,
            a.clone(),
            b.clone(),
            *lane,
        );
        differential_int(
            &format!("v2f64_to_{}", func),
            &module,
            &v2f64_lane_driver(&func, op_c, &key, *lane as usize),
            &key,
        )
        .unwrap();
    }
}
