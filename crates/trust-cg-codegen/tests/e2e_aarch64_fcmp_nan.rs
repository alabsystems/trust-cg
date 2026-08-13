// trust-cg-codegen/tests/e2e_aarch64_fcmp_nan.rs
//
// Pinned refutation for a confirmed P0 miscompile of `fcmp one` (ordered,
// not-equal / LLVM `FCmpOp::ONe`) on AArch64. `one` must be FALSE when either
// operand is NaN (it is an ORDERED predicate), but it was lowered to the plain
// `NE` condition code — and AArch64 FCMP sets Z=0 on an unordered result, so
// `NE` is TRUE for NaN. `one(x, NaN)` therefore wrongly returned 1.
//
// (x86 does not share this bug: UCOMISD sets ZF=1 on unordered, so `one`->NE is
// correct there. It is an AArch64-specific flag-semantics divergence.)
//
// Fix: `select_fcmp` lowers `one` as `MI || GT` (ordered-less OR ordered-
// greater) via two CSETs and an ORR — both conditions are false for NaN — the
// same two-condition shape already used for `ueq` (EQ || VS).
//
// This test evaluates all 12 IEEE compare predicates over an input set that
// includes NaN and signed zero, bit-exact against clang's own float compares
// at -O2.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    Block as TrustIrBlock, CastOp, FCmpOp, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

// `fn name(a: f64, b: f64) -> i32 { zext((a <pred> b) as bool) }`
fn build_fcmp(id: u32, name: &str, m: &mut TrustIrModule, pred: FCmpOp) {
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::F64, Ty::F64],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::F64), (ValueId::new(1), Ty::F64)],
        body: vec![
            InstrNode::new(Inst::FCmp {
                op: pred,
                ty: Ty::F64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::I32,
                operand: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    m.add_function(f);
}

fn build_module() -> TrustIrModule {
    use FCmpOp::*;
    let mut m = TrustIrModule::new("fcmp_nan");
    let preds = [
        (OEq, "fc_oeq"),
        (ONe, "fc_one"),
        (OLt, "fc_olt"),
        (OLe, "fc_ole"),
        (OGt, "fc_ogt"),
        (OGe, "fc_oge"),
        (UEq, "fc_ueq"),
        (UNe, "fc_une"),
        (ULt, "fc_ult"),
        (ULe, "fc_ule"),
        (UGt, "fc_ugt"),
        (UGe, "fc_uge"),
    ];
    for (i, (p, n)) in preds.iter().enumerate() {
        build_fcmp(i as u32, n, &mut m, *p);
    }
    m
}

fn compile_at(module: &TrustIrModule, opt: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    });
    let r = compiler.compile(module).expect("fcmp module must compile");
    assert!(!r.object_code.is_empty());
    r.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <math.h>
#define D(p) extern int p(double,double);
D(fc_oeq)D(fc_one)D(fc_olt)D(fc_ole)D(fc_ogt)D(fc_oge)
D(fc_ueq)D(fc_une)D(fc_ult)D(fc_ule)D(fc_ugt)D(fc_uge)
int main(void){
    double N=NAN, vals[]={0.0,-0.0,1.0,-1.0,2.5,N,1e308,-1e308};
    int n=sizeof(vals)/sizeof(vals[0]);
    for(int i=0;i<n;i++)for(int j=0;j<n;j++){
        double a=vals[i],b=vals[j]; int u=isnan(a)||isnan(b);
        if(fc_oeq(a,b)!=(a==b))          return 1;
        if(fc_one(a,b)!=(!u && a!=b))    return 2;   /* ordered ne */
        if(fc_olt(a,b)!=(a<b))           return 3;
        if(fc_ole(a,b)!=(a<=b))          return 4;
        if(fc_ogt(a,b)!=(a>b))           return 5;
        if(fc_oge(a,b)!=(a>=b))          return 6;
        if(fc_ueq(a,b)!=(u || a==b))     return 7;
        if(fc_une(a,b)!=(a!=b))          return 8;   /* unordered ne */
        if(fc_ult(a,b)!=(u || a<b))      return 9;
        if(fc_ule(a,b)!=(u || a<=b))     return 10;
        if(fc_ugt(a,b)!=(u || a>b))      return 11;
        if(fc_uge(a,b)!=(u || a>=b))     return 12;
    }
    printf("all 12 fcmp predicates NaN-aware bit-exact vs clang\n");
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
            "-O2",
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
fn e2e_aarch64_fcmp_all_predicates_nan_aware() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt);
        let Some(code) = link_run("fcmp_nan", &obj) else {
            return;
        };
        assert_eq!(
            code, 0,
            "fcmp predicate mismatch at {opt:?} (failing code {code})"
        );
    }
}
