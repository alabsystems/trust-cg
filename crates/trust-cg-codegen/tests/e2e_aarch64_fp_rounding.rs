// trust-cg-codegen/tests/e2e_aarch64_fp_rounding.rs
//
// End-to-end (compile -> link -> RUN on aarch64-apple-darwin) coverage for scalar
// FP round-to-integral: floor / ceil / trunc on f32 and f64.
//
// These fail-closed on AArch64 ("x86-64-only via SSE4.1 ROUNDSD/ROUNDSS") until
// now. AArch64 has them as single 1-source FP instructions: FRINTM (floor,
// toward -inf), FRINTP (ceil, toward +inf), FRINTZ (trunc, toward zero). They are
// proven by the Ffloor/Fceil/Ftrunc_F{32,64} lowering proofs (fp.roundToIntegral
// RTN/RTP/RTZ), the AArch64 analogue of the x86 ROUNDSD/ROUNDSS proofs. Verified
// bit-exact against libm on real Apple Silicon.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    Block as TrustIrBlock, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, Ty, UnOp,
};
use trust_ir::{BlockId, FuncId, ValueId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

/// `fn name(x: T) -> T { op(x) }` for a scalar FP type T (F32 or F64).
fn build_fp_unop(func_id: u32, name: &str, module: &mut TrustIrModule, ty: Ty, op: UnOp) {
    let ft = module.add_func_type(FuncTy {
        params: vec![ty.clone()],
        returns: vec![ty.clone()],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), ty.clone())],
        body: vec![
            InstrNode::new(Inst::UnOp {
                op,
                ty,
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
    let mut module = TrustIrModule::new("fp_rounding");
    build_fp_unop(0, "_f64_floor", &mut module, Ty::F64, UnOp::FFloor);
    build_fp_unop(1, "_f64_ceil", &mut module, Ty::F64, UnOp::FCeil);
    build_fp_unop(2, "_f64_trunc", &mut module, Ty::F64, UnOp::FTrunc);
    build_fp_unop(3, "_f32_floor", &mut module, Ty::F32, UnOp::FFloor);
    build_fp_unop(4, "_f32_ceil", &mut module, Ty::F32, UnOp::FCeil);
    build_fp_unop(5, "_f32_trunc", &mut module, Ty::F32, UnOp::FTrunc);
    module
}

fn compile_to_obj_at(module: &TrustIrModule, opt_level: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(module)
        .expect("scalar FP round-to-integral must compile (proof/coverage gate included)");
    assert!(!result.object_code.is_empty());
    result.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

extern double _f64_floor(double x);
extern double _f64_ceil(double x);
extern double _f64_trunc(double x);
extern float  _f32_floor(float x);
extern float  _f32_ceil(float x);
extern float  _f32_trunc(float x);

static int eqd(double a, double b) { return memcmp(&a, &b, sizeof a) == 0; } /* bit-exact */
static int eqf(float a, float b)   { return memcmp(&a, &b, sizeof a) == 0; }

int main(void) {
    double dv[] = { 3.7, -3.7, 2.0, -2.5, 0.0, -0.0, 100.5, -100.5, 0.5, -0.5, 1e15 + 0.5 };
    for (unsigned i = 0; i < sizeof(dv)/sizeof(dv[0]); i++) {
        double x = dv[i];
        if (!eqd(_f64_floor(x), floor(x))) return 1;
        if (!eqd(_f64_ceil(x),  ceil(x)))  return 2;
        if (!eqd(_f64_trunc(x), trunc(x))) return 3;
    }
    float fv[] = { 3.7f, -3.7f, 2.0f, -2.5f, 0.0f, -0.0f, 100.5f, -100.5f, 0.5f, -0.5f };
    for (unsigned i = 0; i < sizeof(fv)/sizeof(fv[0]); i++) {
        float x = fv[i];
        if (!eqf(_f32_floor(x), floorf(x))) return 4;
        if (!eqf(_f32_ceil(x),  ceilf(x)))  return 5;
        if (!eqf(_f32_trunc(x), truncf(x))) return 6;
    }
    /* signed-zero specifics: floor(-0.0) = -0.0, ceil(0.0)=0.0, trunc(-0.0)=-0.0 */
    if (!eqd(_f64_floor(-0.0), -0.0)) return 7;
    if (!eqd(_f64_ceil(0.0),    0.0)) return 8;
    if (!eqd(_f64_trunc(-0.0), -0.0)) return 9;

    printf("scalar FP floor/ceil/trunc (f32/f64) bit-exact vs libm\n");
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
            "-lm",
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
fn e2e_aarch64_scalar_fp_floor_ceil_trunc() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_to_obj_at(&module, opt);
        let Some(code) = link_run_exit_code("fp_rounding", &obj, DRIVER) else {
            return;
        };
        assert_eq!(
            code, 0,
            "scalar FP round-to-integral runtime mismatch at {opt:?} (failing-case code {code})",
        );
    }
}
