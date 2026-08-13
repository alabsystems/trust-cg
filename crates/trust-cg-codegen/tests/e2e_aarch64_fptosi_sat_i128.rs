// trust-cg-codegen/tests/e2e_aarch64_fptosi_sat_i128.rs
//
// Completeness: saturating float -> i128/u128 (`f as i128` / `f as u128` in
// Rust, LLVM `fptosi.sat` / `fptoui.sat`), previously fail-closed. Rust's `as`
// is saturating: NaN -> 0, out-of-range clamps to MIN/MAX, else round toward
// zero.
//
// There is no native 128-bit `fcvt`, so the lowering uses the raw `__fix*ti`
// libcall plus explicit float-compare bounds. The libcall alone is NOT a correct
// saturating cast:
//   * UNSIGNED: `__fixuns*ti` already clamps [0, 2^128) and maps negatives to 0;
//     only NaN (which it maps to UMAX) needs correcting to 0.
//   * SIGNED: `__fix*ti` computes the raw value for exponents < 128, so an `f` in
//     [2^127, 2^128) OVERFLOWS the signed range and wraps -- `__fixdfti(2^127)`
//     returns i128::MIN, not MAX. So the signed path bounds f >= 2^127 -> MAX and
//     f < -2^127 -> MIN explicitly, plus NaN -> 0.
//
// This test checks against an INDEPENDENT trunc-and-clamp oracle (not the
// libcall) over the whole magnitude range including the 2^127 / 2^128 boundary,
// at O0 and O2.
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

fn build_sat(id: u32, name: &str, m: &mut TrustIrModule, op: CastOp, src: Ty, dst: Ty) {
    let ft = m.add_func_type(FuncTy {
        params: vec![src.clone()],
        returns: vec![dst.clone()],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
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
    m.add_function(f);
}

fn build_module() -> TrustIrModule {
    use CastOp::{FPToSISat, FPToUISat};
    let mut m = TrustIrModule::new("fptosi_sat_i128");
    build_sat(0, "s_d128", &mut m, FPToSISat, Ty::F64, Ty::I128);
    build_sat(1, "u_d128", &mut m, FPToUISat, Ty::F64, Ty::U128);
    build_sat(2, "s_f128", &mut m, FPToSISat, Ty::F32, Ty::I128);
    build_sat(3, "u_f128", &mut m, FPToUISat, Ty::F32, Ty::U128);
    m
}

fn compile_at(module: &TrustIrModule, opt: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    });
    let r = compiler
        .compile(module)
        .expect("saturating i128 cast module must compile");
    assert!(!r.object_code.is_empty());
    r.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <math.h>
#include <float.h>
typedef __int128 i128; typedef unsigned __int128 u128;
extern i128 s_d128(double); extern u128 u_d128(double);
extern i128 s_f128(float);  extern u128 u_f128(float);

static i128 sref(double f){
    i128 MIN=(i128)1<<127, MAX=~MIN;
    if(f!=f) return 0;
    if(f >= 0x1p127) return MAX;
    if(f <  -0x1p127) return MIN;
    return (i128)f;
}
static u128 uref(double f){
    if(f!=f) return 0;
    if(f <= 0.0) return 0;
    if(f >= 0x1p128) return ~(u128)0;
    return (u128)f;
}

int main(void){
    double D[]={0,-0.0,1,-1,0.9,-0.9,3.7,-3.7,1e18,-1e18,1e30,-1e30,
                0x1p127,-0x1p127,nextafter(0x1p127,0),nextafter(-0x1p127,0),
                nextafter(0x1p127,INFINITY),0x1p128,-0x1p128,nextafter(0x1p128,0),
                1e40,-1e40,INFINITY,-INFINITY,NAN,DBL_MAX,-DBL_MAX,0x1p120,0x1p100,-0x1p100,42.0,-42.0};
    for(unsigned i=0;i<sizeof(D)/sizeof(D[0]);i++){
        double f=D[i];
        if(s_d128(f)!=sref(f)){printf("s_d128 f=%a\n",f);return 1;}
        if(u_d128(f)!=uref(f)){printf("u_d128 f=%a\n",f);return 2;}
    }
    float F[]={0,-0.0f,1,-1,3.7f,-3.7f,1e18f,-1e18f,0x1p127f,-0x1p127f,
               nextafterf(0x1p127f,0),nextafterf(0x1p127f,INFINITY),0x1p128f,-0x1p128f,
               1e30f,-1e30f,INFINITY,-INFINITY,NAN,FLT_MAX,-FLT_MAX,0x1p100f,42.0f,-42.0f};
    for(unsigned i=0;i<sizeof(F)/sizeof(F[0]);i++){
        float f=F[i]; double d=(double)f;
        if(s_f128(f)!=sref(d)){printf("s_f128 f=%a\n",(double)f);return 3;}
        if(u_f128(f)!=uref(d)){printf("u_f128 f=%a\n",(double)f);return 4;}
    }
    printf("saturating f32/f64 -> i128/u128 matches independent trunc-and-clamp oracle\n");
    return 0;
}
"#;

fn link_run(tag: &str, obj: &[u8]) -> Option<i32> {
    if !can_link_and_run_aarch64_macho() {
        eprintln!("SKIP: needs aarch64-apple-darwin");
        return None;
    }
    let dir = std::env::temp_dir().join(format!("trust_cg_{tag}_e2e"));
    let _ = fs::create_dir_all(&dir);
    let obj_path = dir.join(format!("{tag}.o"));
    let drv_path = dir.join("driver.c");
    let bin_path = dir.join(format!("{tag}_bin"));
    fs::write(&obj_path, obj).unwrap();
    fs::write(&drv_path, DRIVER).unwrap();
    let link = Command::new("cc")
        .args([
            drv_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-lm",
            "-o",
            bin_path.to_str().unwrap(),
        ])
        .output()
        .expect("cc");
    assert!(
        link.status.success(),
        "link:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let code = Command::new(bin_path.to_str().unwrap())
        .output()
        .unwrap()
        .status
        .code()
        .unwrap_or(-1);
    let _ = fs::remove_dir_all(&dir);
    Some(code)
}

#[test]
fn e2e_aarch64_fptosi_fptoui_sat_i128() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt);
        let Some(code) = link_run("fptosi_sat_i128", &obj) else {
            return;
        };
        assert_eq!(
            code, 0,
            "saturating i128 cast mismatch at {opt:?} (failing code {code})",
        );
    }
}
