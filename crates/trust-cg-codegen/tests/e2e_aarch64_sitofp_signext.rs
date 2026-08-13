// trust-cg-codegen/tests/e2e_aarch64_sitofp_signext.rs
//
// Pinned refutation test for a P0 silent miscompile (fixed 2026-07-04):
// AArch64 `sitofp` (signed int -> float, Opcode::FcvtFromInt) from a
// narrower-than-64-bit source (i8/i16/i32) ZERO-extended the source instead of
// SIGN-extending it before SCVTF. Because SCVTF is encoded sf=1 (reads a 64-bit
// X source, encode.rs `ScvtfRR`), every NEGATIVE input was read as a huge
// positive value: `(-2i32) as f32` produced 4.29497e9 instead of -2.0. uitofp
// was correct (zero-extension is what unsigned wants) and i64 was correct (no
// extension). Fix: select_fcvt_from_int sign-extends i8/i16/i32 to 64 bits
// (SXTB/SXTH/SXTW) before SCVTF.
//
// This test compiles sitofp/uitofp from every integer width to f32/f64, links,
// and RUNS on aarch64-apple-darwin, diffing bit-exact against the C cast
// reference (clang/LLVM) with a battery of NEGATIVE inputs that reproduces the
// original bug. It fails closed (exit != 0) if the sign-extension regresses.
//
// NOTE (verifier gate): the per-instruction certs PASSED on the buggy code —
// translation validation proved SCVTF in isolation without witnessing that its
// source operand was zero- rather than sign-extended (the omission/dataflow
// direction, TV-3 territory). This runtime differential is the gate that
// actually catches the class; strengthening the isel dataflow validator to
// reject a mis-extended SCVTF source is a follow-up for the verify lane.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    Block as TrustIrBlock, CastOp, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

/// `fn name(x: src) -> dst { x as dst }` via a single int->float Cast.
fn build_itofp(func_id: u32, name: &str, module: &mut TrustIrModule, op: CastOp, src: Ty, dst: Ty) {
    let ft = module.add_func_type(FuncTy {
        params: vec![src.clone()],
        returns: vec![dst.clone()],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), src.clone())],
        body: vec![
            InstrNode::new(Inst::Cast {
                op,
                src_ty: src,
                dst_ty: dst,
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    module.add_function(f);
}

fn build_module() -> TrustIrModule {
    use CastOp::{SIToFP, UIToFP};
    let mut m = TrustIrModule::new("sitofp_signext");
    // Signed -> f32/f64 (the miscompiling family).
    build_itofp(0, "_s8_f32", &mut m, SIToFP, Ty::I8, Ty::F32);
    build_itofp(1, "_s16_f32", &mut m, SIToFP, Ty::I16, Ty::F32);
    build_itofp(2, "_s32_f32", &mut m, SIToFP, Ty::I32, Ty::F32);
    build_itofp(3, "_s64_f32", &mut m, SIToFP, Ty::I64, Ty::F32);
    build_itofp(4, "_s32_f64", &mut m, SIToFP, Ty::I32, Ty::F64);
    build_itofp(5, "_s16_f64", &mut m, SIToFP, Ty::I16, Ty::F64);
    // Unsigned -> f32/f64 (regression guard: must stay zero-extended/correct).
    build_itofp(6, "_u32_f32", &mut m, UIToFP, Ty::U32, Ty::F32);
    build_itofp(7, "_u32_f64", &mut m, UIToFP, Ty::U32, Ty::F64);
    build_itofp(8, "_u64_f64", &mut m, UIToFP, Ty::U64, Ty::F64);
    m
}

fn compile_to_obj_at(module: &TrustIrModule, opt_level: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(module)
        .expect("int->float casts must compile (proof/coverage gate included)");
    assert!(!result.object_code.is_empty());
    result.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
#include <string.h>

extern float  _s8_f32(int8_t);
extern float  _s16_f32(int16_t);
extern float  _s32_f32(int32_t);
extern float  _s64_f32(int64_t);
extern double _s32_f64(int32_t);
extern double _s16_f64(int16_t);
extern float  _u32_f32(uint32_t);
extern double _u32_f64(uint32_t);
extern double _u64_f64(uint64_t);

static int eqf(float a, float b){ return memcmp(&a,&b,4)==0; }
static int eqd(double a, double b){ return memcmp(&a,&b,8)==0; }

int main(void){
    /* the original bug: every negative signed source was miscompiled */
    int8_t  i8v[]  = { -1, -2, -128, 127, 0, 50 };
    int16_t i16v[] = { -1, -2, -30000, -32768, 32767, 0 };
    int32_t i32v[] = { -1, -2, -100, -2147483647-1, 2147483647, 0, 123456 };
    int64_t i64v[] = { -1, -2, -100, -9000000000LL, 9000000000LL, 0 };
    uint32_t u32v[]= { 0u, 2u, 4000000000u, 0xFFFFFFFFu, 100u };
    uint64_t u64v[]= { 0u, 2u, 18000000000000000000ULL, 100u };

    for (unsigned k=0;k<sizeof(i8v)/sizeof(i8v[0]);k++)
        if (!eqf(_s8_f32(i8v[k]), (float)i8v[k])) return 1;
    for (unsigned k=0;k<sizeof(i16v)/sizeof(i16v[0]);k++){
        if (!eqf(_s16_f32(i16v[k]), (float)i16v[k])) return 2;
        if (!eqd(_s16_f64(i16v[k]), (double)i16v[k])) return 3;
    }
    for (unsigned k=0;k<sizeof(i32v)/sizeof(i32v[0]);k++){
        if (!eqf(_s32_f32(i32v[k]), (float)i32v[k])) return 4;
        if (!eqd(_s32_f64(i32v[k]), (double)i32v[k])) return 5;
    }
    for (unsigned k=0;k<sizeof(i64v)/sizeof(i64v[0]);k++)
        if (!eqf(_s64_f32(i64v[k]), (float)i64v[k])) return 6;
    for (unsigned k=0;k<sizeof(u32v)/sizeof(u32v[0]);k++){
        if (!eqf(_u32_f32(u32v[k]), (float)u32v[k])) return 7;
        if (!eqd(_u32_f64(u32v[k]), (double)u32v[k])) return 8;
    }
    for (unsigned k=0;k<sizeof(u64v)/sizeof(u64v[0]);k++)
        if (!eqd(_u64_f64(u64v[k]), (double)u64v[k])) return 9;

    printf("sitofp/uitofp i8/i16/i32/i64 -> f32/f64 bit-exact vs clang (negatives included)\n");
    return 0;
}
"#;

fn link_run_exit_code(tag: &str, obj: &[u8], driver: &str) -> Option<i32> {
    if !can_link_and_run_aarch64_macho() {
        eprintln!("SKIP: link-and-run requires an aarch64-apple-darwin host");
        return None;
    }
    let dir = std::env::temp_dir().join(format!("trust_cg_{tag}_e2e"));
    let _ = fs::create_dir_all(&dir);
    let obj_path = dir.join(format!("{tag}.o"));
    let drv_path = dir.join("driver.c");
    let bin_path = dir.join(format!("{tag}_bin"));
    fs::write(&obj_path, obj).expect("write .o");
    fs::write(&drv_path, driver).expect("write driver");

    let link = Command::new("cc")
        .args([
            drv_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-o",
            bin_path.to_str().unwrap(),
        ])
        .output()
        .expect("cc available");
    assert!(
        link.status.success(),
        "link failed:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );

    let run = Command::new(bin_path.to_str().unwrap())
        .output()
        .expect("run binary");
    let code = run.status.code().unwrap_or(-1);
    let _ = fs::remove_dir_all(&dir);
    Some(code)
}

#[test]
fn e2e_aarch64_sitofp_sign_extends_negatives() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_to_obj_at(&module, opt);
        let Some(code) = link_run_exit_code("sitofp_signext", &obj, DRIVER) else {
            return;
        };
        assert_eq!(
            code, 0,
            "int->float cast runtime mismatch at {opt:?} (failing-case code {code}); \
             a nonzero code in 1..=6 means a SIGNED narrow source was not sign-extended",
        );
    }
}
