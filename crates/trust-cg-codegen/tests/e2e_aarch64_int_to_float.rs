// trust-cg-codegen/tests/e2e_aarch64_int_to_float.rs
//
// Pinned refutation for a confirmed P0 miscompile of i128/u128 -> float
// (`sitofp`/`uitofp`, LLVM SIToFP/UIToFP). A 128-bit integer source was lowered
// to a native `SCVTF/UCVTF d0, x0`, which reads only the LOW 64 bits and
// silently drops the high half — so `x as f64` was wrong for every 128-bit
// value outside the i64/u64 range. Definitive failure: `(double)(u128)-1`
// (2^128 - 1) produced ~1.8e19 (just the low word) instead of ~3.4e38.
//
// Fix: route i128/u128 -> f32/f64 through the compiler-rt `__float*ti` libcalls
// (`__floattidf`/`__floattisf`/`__floatuntidf`/`__floatuntisf`), the exact
// reverse of the `__fix*ti` float->i128 path. The i128 is passed in the x0:x1
// register pair.
//
// This test pins i128/u128/i64/i32 -> f32/f64 bit-exact against clang over a
// value matrix that includes MIN/MAX, powers of two above 2^64, and the
// all-ones u128, at O0 and O2.
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

fn build_itof(id: u32, name: &str, m: &mut TrustIrModule, op: CastOp, src: Ty, dst: Ty) {
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
    use CastOp::{SIToFP, UIToFP};
    let mut m = TrustIrModule::new("int_to_float");
    build_itof(0, "s128_f64", &mut m, SIToFP, Ty::I128, Ty::F64);
    build_itof(1, "u128_f64", &mut m, UIToFP, Ty::U128, Ty::F64);
    build_itof(2, "s128_f32", &mut m, SIToFP, Ty::I128, Ty::F32);
    build_itof(3, "u128_f32", &mut m, UIToFP, Ty::U128, Ty::F32);
    build_itof(4, "s64_f64", &mut m, SIToFP, Ty::I64, Ty::F64);
    build_itof(5, "u64_f64", &mut m, UIToFP, Ty::U64, Ty::F64);
    build_itof(6, "s32_f64", &mut m, SIToFP, Ty::I32, Ty::F64);
    m
}

fn compile_at(module: &TrustIrModule, opt: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    });
    let r = compiler
        .compile(module)
        .expect("int->float module must compile");
    assert!(!r.object_code.is_empty());
    r.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
#include <string.h>
typedef __int128 i128; typedef unsigned __int128 u128;
extern double s128_f64(i128);  extern double u128_f64(u128);
extern float  s128_f32(i128);  extern float  u128_f32(u128);
extern double s64_f64(int64_t); extern double u64_f64(uint64_t);
extern double s32_f64(int32_t);
static int eqd(double a,double b){return memcmp(&a,&b,8)==0;}
static int eqf(float a,float b){return memcmp(&a,&b,4)==0;}
int main(void){
    i128 MIN=(i128)1<<127, MAX=~MIN;
    i128 V[]={0,1,-1,2,-2,MIN,MAX,MIN+1,MAX-1,(i128)1<<64,-((i128)1<<64),
              (i128)0x123456789abcdef,(i128)1<<100,-((i128)1<<100),(i128)1<<126,
              12345678901234567LL, ((i128)1<<80)+7};
    for(unsigned i=0;i<sizeof(V)/sizeof(V[0]);i++){
        i128 v=V[i]; u128 uv=(u128)v;
        if(!eqd(s128_f64(v), (double)v)){printf("s128_f64 #%u\n",i);return 1;}
        if(!eqf(s128_f32(v), (float)v)){printf("s128_f32 #%u\n",i);return 2;}
        if(!eqd(u128_f64(uv),(double)uv)){printf("u128_f64 #%u\n",i);return 3;}
        if(!eqf(u128_f32(uv),(float)uv)){printf("u128_f32 #%u\n",i);return 4;}
    }
    int64_t S64[]={0,-1,1,0x7fffffffffffffffLL,(int64_t)0x8000000000000000ULL,123456789012345LL};
    for(unsigned i=0;i<sizeof(S64)/sizeof(S64[0]);i++){
        if(!eqd(s64_f64(S64[i]),(double)S64[i])){printf("s64_f64 #%u\n",i);return 5;}
        if(!eqd(u64_f64((uint64_t)S64[i]),(double)(uint64_t)S64[i])){printf("u64_f64 #%u\n",i);return 6;}
    }
    int32_t S32[]={0,-1,1,2147483647,(int32_t)0x80000000u,-1000000};
    for(unsigned i=0;i<sizeof(S32)/sizeof(S32[0]);i++)
        if(!eqd(s32_f64(S32[i]),(double)S32[i])){printf("s32_f64 #%u\n",i);return 7;}
    printf("int->float (i128/u128/i64/u64/i32 -> f32/f64) bit-exact vs clang\n");
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
fn e2e_aarch64_int_to_float_incl_i128() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt);
        let Some(code) = link_run("int_to_float", &obj) else {
            return;
        };
        assert_eq!(
            code, 0,
            "int->float mismatch at {opt:?} (failing code {code})"
        );
    }
}
