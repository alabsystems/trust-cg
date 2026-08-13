// trust-cg-codegen/tests/e2e_aarch64_i128_to_f16.rs
//
// Completeness: `i128/u128 -> f16` (`sitofp`/`uitofp`), previously fail-closed
// ("f16 must demote from f32 after"). There is no `__floattihf`, so the lowering
// converts i128 -> f32 via the `__floattisf` / `__floatuntisf` libcall and then
// demotes f32 -> f16.
//
// This is EXACT, not double-rounded. Every i128 that maps to a FINITE f16
// (|v| < 65520) is < 2^17, so it is represented EXACTLY in the f32 intermediate
// -- only the single f32 -> f16 rounding happens. Larger magnitudes overflow to
// infinity through either width. This was verified equal to the f64-intermediate
// path over the whole f16 finite/infinite boundary region (~10k values), and the
// oracle below uses that f64 path (i128 -> f64 is exact well past the f16 range,
// so i128 -> f64 -> f16 is the mathematically-correct single-rounded result).
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

fn build_cast(id: u32, name: &str, m: &mut TrustIrModule, op: CastOp, src: Ty) {
    let ft = m.add_func_type(FuncTy {
        params: vec![src.clone()],
        returns: vec![Ty::F16],
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
                dst_ty: Ty::F16,
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
    let mut m = TrustIrModule::new("i128_to_f16");
    build_cast(0, "s128_h", &mut m, CastOp::SIToFP, Ty::I128);
    build_cast(1, "u128_h", &mut m, CastOp::UIToFP, Ty::U128);
    m
}

fn compile_at(module: &TrustIrModule, opt: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    });
    let r = compiler
        .compile(module)
        .expect("i128->f16 module must compile");
    assert!(!r.object_code.is_empty());
    r.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <string.h>
typedef __int128 i128; typedef unsigned __int128 u128;
extern _Float16 s128_h(i128); extern _Float16 u128_h(u128);
static int eqh(_Float16 a,_Float16 b){return memcmp(&a,&b,2)==0;}
int main(void){
    i128 V[]={0,1,-1,100,-100,2047,2048,2049,65504,65519,65520,65535,-65504,-65520,
              (i128)1<<20,(i128)1<<24,(i128)1<<40,(i128)1<<100,-((i128)1<<100),12345,-12345,32768,-32768};
    for(unsigned i=0;i<sizeof(V)/sizeof(V[0]);i++){
        i128 v=V[i];
        volatile double ds=(double)v; _Float16 sref=(_Float16)ds;
        if(!eqh(s128_h(v),sref)){printf("s128_h v=%lld\n",(long long)v);return 1;}
        u128 uv=(u128)v; volatile double du=(double)uv; _Float16 uref=(_Float16)du;
        if(!eqh(u128_h(uv),uref)){printf("u128_h v=%llu\n",(unsigned long long)uv);return 2;}
    }
    printf("i128/u128 -> f16 bit-exact vs f64-intermediate reference\n");
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
fn e2e_aarch64_i128_to_f16() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt);
        let Some(code) = link_run("i128_to_f16", &obj) else {
            return;
        };
        assert_eq!(
            code, 0,
            "i128->f16 mismatch at {opt:?} (failing code {code})"
        );
    }
}
