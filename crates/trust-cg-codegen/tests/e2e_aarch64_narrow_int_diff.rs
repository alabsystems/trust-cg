// trust-cg-codegen/tests/e2e_aarch64_narrow_int_diff.rs
//
// End-to-end (compile -> link -> RUN on aarch64-apple-darwin) differential gate
// for narrow scalar integer ops (i8/i16), the extension-discipline-sensitive
// class where the sitofp P0 (commit 71f2e8e) lived: a narrow value in a wide
// register whose sign/zero extension must be handled correctly. Signed
// comparisons over negative operands, wrapping arithmetic, division, and
// arithmetic shifts each depend on the low bits being interpreted at the right
// width and signedness.
//
// Every op is diffed bit-exact against clang/LLVM over an operand grid that
// includes the sign boundaries (iN::MIN, -1, iN::MAX). It is a standing
// regression gate: a future extension-discipline slip fails it closed.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    BinOp, Block as TrustIrBlock, FuncTy, Function as TrustIrFunction, ICmpOp, Inst, InstrNode,
    Module as TrustIrModule, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

fn cmp_fn(id: u32, name: &str, m: &mut TrustIrModule, ty: Ty, op: ICmpOp) {
    let ft = m.add_func_type(FuncTy {
        params: vec![ty.clone(), ty.clone()],
        returns: vec![Ty::Bool],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), ty.clone()), (ValueId::new(1), ty.clone())],
        body: vec![
            InstrNode::new(Inst::ICmp {
                op,
                ty,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    m.add_function(f);
}

fn bin_fn(id: u32, name: &str, m: &mut TrustIrModule, ty: Ty, op: BinOp) {
    let ft = m.add_func_type(FuncTy {
        params: vec![ty.clone(), ty.clone()],
        returns: vec![ty.clone()],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), ty.clone()), (ValueId::new(1), ty.clone())],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op,
                ty,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    m.add_function(f);
}

fn build_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("narrow_int_diff");
    cmp_fn(0, "_slt8", &mut m, Ty::I8, ICmpOp::Slt);
    cmp_fn(1, "_sgt8", &mut m, Ty::I8, ICmpOp::Sgt);
    cmp_fn(2, "_sle16", &mut m, Ty::I16, ICmpOp::Sle);
    cmp_fn(3, "_ult8", &mut m, Ty::U8, ICmpOp::Ult);
    bin_fn(4, "_add8", &mut m, Ty::I8, BinOp::Add);
    bin_fn(5, "_sub8", &mut m, Ty::I8, BinOp::Sub);
    bin_fn(6, "_mul8", &mut m, Ty::I8, BinOp::Mul);
    bin_fn(7, "_sdiv8", &mut m, Ty::I8, BinOp::SDiv);
    bin_fn(8, "_ashr8", &mut m, Ty::I8, BinOp::AShr);
    bin_fn(9, "_add16", &mut m, Ty::I16, BinOp::Add);
    bin_fn(10, "_mul16", &mut m, Ty::I16, BinOp::Mul);
    m
}

fn compile_to_obj_at(module: &TrustIrModule, opt_level: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(module)
        .expect("narrow int ops must compile");
    assert!(!result.object_code.is_empty());
    result.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>

extern int _slt8(int8_t,int8_t);
extern int _sgt8(int8_t,int8_t);
extern int _sle16(int16_t,int16_t);
extern int _ult8(uint8_t,uint8_t);
extern int8_t _add8(int8_t,int8_t);
extern int8_t _sub8(int8_t,int8_t);
extern int8_t _mul8(int8_t,int8_t);
extern int8_t _sdiv8(int8_t,int8_t);
extern int8_t _ashr8(int8_t,int8_t);
extern int16_t _add16(int16_t,int16_t);
extern int16_t _mul16(int16_t,int16_t);

int main(void){
    int8_t v[] = { -128, -100, -1, 0, 1, 50, 100, 127, -50, 3 };
    unsigned n = sizeof(v)/sizeof(v[0]);
    for (unsigned i=0;i<n;i++) for (unsigned j=0;j<n;j++){
        int8_t a=v[i], b=v[j];
        if ((_slt8(a,b)!=0) != (a<b))  return 1;
        if ((_sgt8(a,b)!=0) != (a>b))  return 2;
        if ((int8_t)_add8(a,b) != (int8_t)(a+b)) return 3;
        if ((int8_t)_sub8(a,b) != (int8_t)(a-b)) return 4;
        if ((int8_t)_mul8(a,b) != (int8_t)(a*b)) return 5;
        if (b != 0 && !(a==-128 && b==-1))         /* skip INT_MIN/-1 (UB) */
            if ((int8_t)_sdiv8(a,b) != (int8_t)(a/b)) return 6;
        int sh = ((uint8_t)b) & 7;                  /* well-defined shift amount */
        if ((int8_t)_ashr8(a,(int8_t)sh) != (int8_t)(a>>sh)) return 7;
    }
    uint8_t u[] = { 0, 1, 100, 127, 128, 200, 255 };
    unsigned un = sizeof(u)/sizeof(u[0]);
    for (unsigned i=0;i<un;i++) for (unsigned j=0;j<un;j++)
        if ((_ult8(u[i],u[j])!=0) != (u[i]<u[j])) return 8;
    int16_t w[] = { -32768, -100, -1, 0, 1, 100, 32767 };
    unsigned wn = sizeof(w)/sizeof(w[0]);
    for (unsigned i=0;i<wn;i++) for (unsigned j=0;j<wn;j++){
        int16_t a=w[i], b=w[j];
        if ((_sle16(a,b)!=0) != (a<=b)) return 9;
        if ((int16_t)_add16(a,b) != (int16_t)(a+b)) return 10;
        if ((int16_t)_mul16(a,b) != (int16_t)(a*b)) return 11;
    }
    printf("narrow i8/i16 cmp/add/sub/mul/sdiv/ashr bit-exact vs clang (sign boundaries incl.)\n");
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
fn e2e_aarch64_narrow_int_matches_llvm() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_to_obj_at(&module, opt);
        let Some(code) = link_run_exit_code("narrow_int_diff", &obj, DRIVER) else {
            return;
        };
        assert_eq!(
            code, 0,
            "narrow int op runtime mismatch at {opt:?} (failing-case code {code})",
        );
    }
}
