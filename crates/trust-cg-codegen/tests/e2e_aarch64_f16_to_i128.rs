// trust-cg-codegen/tests/e2e_aarch64_f16_to_i128.rs
//
// Completeness: `f16 -> i128/u128` (`fptosi`/`fptoui`), previously fail-closed
// ("f16 must widen first"). There is no `__fixhfti` in the shipped compiler-rt,
// so the lowering widens the f16 to f32 first — a LOSSLESS conversion (every
// f16 is exactly representable in f32) — and then uses the existing `__fixsfti`
// / `__fixunssfti` libcall. Because the widening rounds nothing, only the single
// f32 -> i128 truncation happens, so `f16 -> f32 -> i128` is bit-identical to a
// direct `f16 -> i128`. (The reverse, i128 -> f16, is deliberately NOT lowered
// this way: i128 -> f32 -> f16 would double-round.)
//
// The C oracle must widen through a `volatile float` too, both because
// `(i128)(_Float16)` needs the missing `__fixhfti` and because clang would
// otherwise refold `(i128)(float)h` back into that direct call.
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

fn build_cast(id: u32, name: &str, m: &mut TrustIrModule, op: CastOp, dst: Ty) {
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::F16],
        returns: vec![dst.clone()],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::F16)],
        body: vec![
            InstrNode::new(Inst::Cast {
                op,
                src_ty: Ty::F16,
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
    let mut m = TrustIrModule::new("f16_to_i128");
    build_cast(0, "h_s128", &mut m, CastOp::FPToSI, Ty::I128);
    build_cast(1, "h_u128", &mut m, CastOp::FPToUI, Ty::U128);
    m
}

fn compile_at(module: &TrustIrModule, opt: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    });
    let r = compiler
        .compile(module)
        .expect("f16->i128 module must compile");
    assert!(!r.object_code.is_empty());
    r.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
typedef __int128 i128; typedef unsigned __int128 u128;
extern i128 h_s128(_Float16); extern u128 h_u128(_Float16);
int main(void){
    float xs[]={0.0f,1.0f,-1.0f,3.7f,-3.7f,100.9f,-100.9f,65504.0f,-65504.0f,
                32768.0f,0.5f,-0.5f,255.9f,-256.1f};
    for(unsigned i=0;i<sizeof(xs)/sizeof(xs[0]);i++){
        _Float16 h=(_Float16)xs[i];
        volatile float f=(float)h;    /* exact widen; volatile blocks refold to __fixhfti */
        i128 sref=(i128)f; u128 uref=(u128)f;
        if(h_s128(h)!=sref){printf("h_s128 %g\n",xs[i]);return 1;}
        if(f>=0 && h_u128(h)!=uref){printf("h_u128 %g\n",xs[i]);return 2;}
    }
    printf("f16 -> i128/u128 bit-exact vs clang (widen-then-convert)\n");
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
fn e2e_aarch64_f16_to_i128() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt);
        let Some(code) = link_run("f16_to_i128", &obj) else {
            return;
        };
        assert_eq!(
            code, 0,
            "f16->i128 mismatch at {opt:?} (failing code {code})"
        );
    }
}
