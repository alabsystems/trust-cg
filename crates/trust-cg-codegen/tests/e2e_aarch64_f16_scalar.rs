// trust-cg-codegen/tests/e2e_aarch64_f16_scalar.rs
//
// End-to-end (compile -> link -> RUN on aarch64-apple-darwin) coverage for scalar
// binary16 (IEEE FP16 / ARMv8.2-FP16) arithmetic and unary ops.
//
// These fail-closed in the adapter's validate_scalar_binop_shape /
// validate_unop_shape gates until now (F32/F64 only). AArch64 with FEAT_FP16
// (present on all Apple Silicon) has these as native single-instruction ops on
// the H registers:
//   FADD/FSUB/FMUL/FDIV Hd,Hn,Hm ; FMINNM/FMAXNM Hd,Hn,Hm (min/max)
//   FNEG/FABS/FSQRT Hd,Hn         ; FRINTM/FRINTP/FRINTZ Hd,Hn (floor/ceil/trunc)
// FADD/FSUB/FMUL/FDIV are correctly rounded in binary16 (and F32 is exactly
// 2p+2 = 24 bits wide, so even a promote/compute/demote lowering rounds once),
// FMINNM/FMAXNM and the sign-bit / round-to-integral ops are exact, and FSQRT is
// correctly rounded — so each is a proven, single-rounding lowering. The verifier
// models binary16 via fp_bitmodel::F16; certs are ON here (default config).
//
// FRem over f16 lowers by promoting to f32, calling `fmodf`, and demoting (fmod
// is exact) — see adapter::tests::test_frem_f16_lowers_via_promoted_fmodf.
//
// Verified bit-exact against clang's native _Float16 ops and libm on real Apple
// Silicon (NaN-aware compare).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    BinOp, Block as TrustIrBlock, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, Ty, UnOp,
};
use trust_ir::{BlockId, FuncId, ValueId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

/// `fn name(a: f16, b: f16) -> f16 { op(a, b) }`.
fn build_fp_binop(func_id: u32, name: &str, module: &mut TrustIrModule, op: BinOp) {
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::F16, Ty::F16],
        returns: vec![Ty::F16],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::F16), (ValueId::new(1), Ty::F16)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op,
                ty: Ty::F16,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(f);
}

/// `fn name(x: f16) -> f16 { op(x) }`.
fn build_fp_unop(func_id: u32, name: &str, module: &mut TrustIrModule, op: UnOp) {
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::F16],
        returns: vec![Ty::F16],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::F16)],
        body: vec![
            InstrNode::new(Inst::UnOp {
                op,
                ty: Ty::F16,
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
    let mut module = TrustIrModule::new("f16_scalar");
    build_fp_binop(0, "_f16_add", &mut module, BinOp::FAdd);
    build_fp_binop(1, "_f16_sub", &mut module, BinOp::FSub);
    build_fp_binop(2, "_f16_mul", &mut module, BinOp::FMul);
    build_fp_binop(3, "_f16_div", &mut module, BinOp::FDiv);
    build_fp_binop(4, "_f16_min", &mut module, BinOp::FMin);
    build_fp_binop(5, "_f16_max", &mut module, BinOp::FMax);
    build_fp_binop(12, "_f16_rem", &mut module, BinOp::FRem);
    build_fp_unop(6, "_f16_neg", &mut module, UnOp::FNeg);
    build_fp_unop(7, "_f16_abs", &mut module, UnOp::FAbs);
    build_fp_unop(8, "_f16_sqrt", &mut module, UnOp::FSqrt);
    build_fp_unop(9, "_f16_floor", &mut module, UnOp::FFloor);
    build_fp_unop(10, "_f16_ceil", &mut module, UnOp::FCeil);
    build_fp_unop(11, "_f16_trunc", &mut module, UnOp::FTrunc);
    module
}

fn compile_to_obj_at(module: &TrustIrModule, opt_level: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(module)
        .expect("scalar f16 ops must compile (proof/coverage gate included)");
    assert!(!result.object_code.is_empty());
    result.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

extern _Float16 _f16_add(_Float16, _Float16);
extern _Float16 _f16_sub(_Float16, _Float16);
extern _Float16 _f16_mul(_Float16, _Float16);
extern _Float16 _f16_div(_Float16, _Float16);
extern _Float16 _f16_min(_Float16, _Float16);
extern _Float16 _f16_max(_Float16, _Float16);
extern _Float16 _f16_rem(_Float16, _Float16);
extern _Float16 _f16_neg(_Float16);
extern _Float16 _f16_abs(_Float16);
extern _Float16 _f16_sqrt(_Float16);
extern _Float16 _f16_floor(_Float16);
extern _Float16 _f16_ceil(_Float16);
extern _Float16 _f16_trunc(_Float16);

/* equal if both NaN, else bit-exact (captures signed zero) */
static int eqh(_Float16 a, _Float16 b) {
    int an = ((float)a != (float)a), bn = ((float)b != (float)b);
    if (an && bn) return 1;
    return memcmp(&a, &b, 2) == 0;
}

int main(void) {
    float xs[] = { 3.5f, -2.7f, 0.0f, -0.0f, 2.0f, 6.25f, 0.9f, -0.9f,
                   100.0f, 65504.0f, 0.33333f, -4.0f, 7.5f, 1.1f, 2.8f };
    unsigned n = sizeof(xs)/sizeof(xs[0]);
    for (unsigned i = 0; i < n; i++) {
        _Float16 a = (_Float16)xs[i];
        for (unsigned j = 0; j < n; j++) {
            _Float16 b = (_Float16)xs[j];
            if (!eqh(_f16_add(a,b), (_Float16)(a+b)))                 return 1;
            if (!eqh(_f16_sub(a,b), (_Float16)(a-b)))                 return 2;
            if (!eqh(_f16_mul(a,b), (_Float16)(a*b)))                 return 3;
            if (!eqh(_f16_div(a,b), (_Float16)(a/b)))                 return 4;
            if (!eqh(_f16_rem(a,b), (_Float16)fmodf((float)a,(float)b))) return 12;
            if (!eqh(_f16_min(a,b), (_Float16)fminf((float)a,(float)b))) return 5;
            if (!eqh(_f16_max(a,b), (_Float16)fmaxf((float)a,(float)b))) return 6;
        }
        if (!eqh(_f16_neg(a),   (_Float16)(-a)))                     return 7;
        if (!eqh(_f16_abs(a),   (_Float16)fabsf((float)a)))          return 8;
        if (!eqh(_f16_sqrt(a),  (_Float16)sqrtf((float)a)))          return 9;
        if (!eqh(_f16_floor(a), (_Float16)floorf((float)a)))         return 10;
        if (!eqh(_f16_ceil(a),  (_Float16)ceilf((float)a)))          return 11;
        if (!eqh(_f16_trunc(a), (_Float16)truncf((float)a)))         return 12;
    }
    /* signed-zero max/min specifics (0.0 and -0.0 are in xs above):
       FMAXNM(+0,-0)=+0, FMINNM(+0,-0)=-0 — matches fmaxf/fminf oracle. */
    printf("scalar f16 add/sub/mul/div/min/max + neg/abs/sqrt/floor/ceil/trunc bit-exact vs clang _Float16 / libm\n");
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
fn e2e_aarch64_scalar_f16_arith() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_to_obj_at(&module, opt);
        let Some(code) = link_run_exit_code("f16_scalar", &obj, DRIVER) else {
            return;
        };
        assert_eq!(
            code, 0,
            "scalar f16 op runtime mismatch at {opt:?} (failing-case code {code})",
        );
    }
}
