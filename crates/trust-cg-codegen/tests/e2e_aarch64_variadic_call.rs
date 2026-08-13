// trust-cg-codegen/tests/e2e_aarch64_variadic_call.rs
//
// Completeness: variadic CALLS (caller side) via `Inst::Call` to a function
// whose `FuncTy` is `is_vararg`. This routes to the machine `CallVariadic`
// opcode and `select_variadic_call`, which must obey the *Apple* AArch64
// variadic ABI -- the sharpest divergence from stock AAPCS64:
//
//   * Fixed (named) parameters are classified normally (registers, then stack).
//   * EVERY variadic argument is passed on the STACK, 8-byte aligned, even when
//     integer/FP argument registers are still free. (Stock AAPCS64 would keep
//     filling x1.. / d0..; Apple does not.)
//   * A variadic `float` is promoted to `double` (8 bytes on the stack).
//
// If trust-cg wrongly kept variadic args in registers, the oracle -- a `vsum`
// summing helper compiled by clang, which reads varargs from the stack per the
// Apple ABI -- would read garbage and the totals would diverge. The whole point
// is that clang defines the callee and trust-cg emits the caller, so the two
// ABIs must agree bit-for-bit.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    Block as TrustIrBlock, Constant, FuncTy, Function as TrustIrFunction, Inst, InstrNode, Linkage,
    Module as TrustIrModule, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

// Declare an external variadic function `name(fixed...) -> ret, ...`.
// Bodyless + Linkage::External => collected into external_func_ids, its
// signature is used only to classify the call, no code is emitted for it.
fn declare_variadic(m: &mut TrustIrModule, id: u32, name: &str, fixed: Vec<Ty>, ret: Ty) -> FuncId {
    let ft = m.add_func_type(FuncTy {
        params: fixed,
        returns: vec![ret],
        is_vararg: true,
    });
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    f.linkage = Linkage::External;
    f.blocks = Vec::new(); // bodyless declaration
    let fid = f.id;
    m.add_function(f);
    fid
}

fn build_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("variadic_call");

    // extern int64_t vsum_i(int64_t count, ...);   // sums `count` int64 varargs
    let vsum_i = declare_variadic(&mut m, 0, "vsum_i", vec![Ty::I64], Ty::I64);
    // extern double  vsum_d(int64_t count, ...);   // sums `count` double varargs
    let vsum_d = declare_variadic(&mut m, 1, "vsum_d", vec![Ty::I64], Ty::F64);

    // int64_t drive_i(int64_t a, int64_t b, int64_t c, int64_t d, int64_t e) {
    //     return vsum_i(5, a, b, c, d, e);   // 5 int varargs -> all on stack
    // }
    let drive_i_sig = m.add_func_type(FuncTy {
        params: vec![Ty::I64; 5],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut drive_i = TrustIrFunction::new(FuncId::new(2), "drive_i", drive_i_sig, BlockId::new(0));
    drive_i.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: (0..5).map(|i| (ValueId::new(i), Ty::I64)).collect(),
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(5),
            })
            .with_result(ValueId::new(10)), // count
            InstrNode::new(Inst::Call {
                callee: vsum_i,
                args: vec![
                    ValueId::new(10),
                    ValueId::new(0),
                    ValueId::new(1),
                    ValueId::new(2),
                    ValueId::new(3),
                    ValueId::new(4),
                ],
            })
            .with_result(ValueId::new(11)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(11)],
            }),
        ],
    }];
    m.add_function(drive_i);

    // double drive_d(double a, double b, double c, double d) {
    //     return vsum_d(4, a, b, c, d);   // 4 double varargs -> all on stack
    // }
    let drive_d_sig = m.add_func_type(FuncTy {
        params: vec![Ty::F64; 4],
        returns: vec![Ty::F64],
        is_vararg: false,
    });
    let mut drive_d = TrustIrFunction::new(FuncId::new(3), "drive_d", drive_d_sig, BlockId::new(0));
    drive_d.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: (0..4).map(|i| (ValueId::new(i), Ty::F64)).collect(),
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(4),
            })
            .with_result(ValueId::new(10)), // count (fixed i64 -> x0)
            InstrNode::new(Inst::Call {
                callee: vsum_d,
                args: vec![
                    ValueId::new(10),
                    ValueId::new(0),
                    ValueId::new(1),
                    ValueId::new(2),
                    ValueId::new(3),
                ],
            })
            .with_result(ValueId::new(11)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(11)],
            }),
        ],
    }];
    m.add_function(drive_d);

    m
}

fn compile_at(module: &TrustIrModule, opt: OptLevel) -> Result<Vec<u8>, String> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    });
    compiler
        .compile(module)
        .map(|r| r.object_code)
        .map_err(|e| format!("{e:?}"))
}

// The oracle: clang-compiled variadic helpers that read varargs from the stack
// per the Apple ABI, plus a main that drives the trust-cg trampolines.
const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
#include <stdarg.h>
#include <math.h>

int64_t vsum_i(int64_t count, ...) {
    va_list ap; va_start(ap, count);
    int64_t s = 0;
    for (int64_t i = 0; i < count; i++) s += va_arg(ap, int64_t);
    va_end(ap);
    return s;
}
double vsum_d(int64_t count, ...) {
    va_list ap; va_start(ap, count);
    double s = 0;
    for (int64_t i = 0; i < count; i++) s += va_arg(ap, double);
    va_end(ap);
    return s;
}

extern int64_t drive_i(int64_t,int64_t,int64_t,int64_t,int64_t);
extern double  drive_d(double,double,double,double);

int main(void){
    if (drive_i(1,2,3,4,5) != 15)            { printf("drive_i a\n"); return 1; }
    if (drive_i(100,-50,7,-7,0) != 50)       { printf("drive_i b\n"); return 2; }
    if (drive_i(-1,-2,-3,-4,-5) != -15)      { printf("drive_i c\n"); return 3; }
    if (fabs(drive_d(1.5,2.25,0.25,4.0) - 8.0) > 1e-12)      { printf("drive_d a\n"); return 4; }
    if (fabs(drive_d(-1.0,0.5,-0.25,10.0) - 9.25) > 1e-12)   { printf("drive_d b\n"); return 5; }
    printf("variadic calls marshal all varargs on the stack (Apple ABI, bit-exact vs clang)\n");
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
fn e2e_aarch64_variadic_call_matches_clang() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt).expect("variadic-call module must compile");
        let Some(code) = link_run("variadic_call", &obj) else {
            return;
        };
        assert_eq!(code, 0, "variadic-call result mismatch at {opt:?}");
    }
}
