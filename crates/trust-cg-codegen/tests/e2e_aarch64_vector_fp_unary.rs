// trust-cg-codegen/tests/e2e_aarch64_vector_fp_unary.rs
//
// End-to-end (compile -> link -> RUN on aarch64-apple-darwin) coverage for packed
// FP negate/abs on <4 x f32> / <2 x f64>.
//
// The adapter previously fail-closed EVERY vector unary op. `Fneg`/`Fabs` need no
// new opcode: they are a bitwise sign-mask op over the V128 lanes, reusing the
// already-covered NEON EOR (Bxor) / BIC (BandNot):
//   Fneg(v) = v EOR sign_mask   (flip each lane's sign bit — correct IEEE
//                                negation, yields -0.0 from +0.0)
//   Fabs(v) = v BIC sign_mask   (clear each lane's sign bit)
// Verified bit-exact (incl. signed zero) by execution on real Apple Silicon.
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

/// `fn name(in: *const V, out: *mut V) { *out = op(*in); }`
fn build_vec_unop(func_id: u32, name: &str, module: &mut TrustIrModule, vec_ty: Ty, op: UnOp) {
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::Ptr],
        returns: vec![],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr), (ValueId::new(1), Ty::Ptr)],
        body: vec![
            InstrNode::new(Inst::Load {
                ty: vec_ty.clone(),
                ptr: ValueId::new(0),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::UnOp {
                op,
                ty: vec_ty.clone(),
                operand: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Store {
                ty: vec_ty,
                ptr: ValueId::new(1),
                value: ValueId::new(3),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    module.add_function(f);
}

fn build_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("vec_fp_unary");
    let v4f32 = Ty::Vector(Box::new(Ty::F32), 4);
    let v2f64 = Ty::Vector(Box::new(Ty::F64), 2);
    build_vec_unop(0, "_v4f32_fneg", &mut module, v4f32.clone(), UnOp::FNeg);
    build_vec_unop(1, "_v4f32_fabs", &mut module, v4f32, UnOp::FAbs);
    build_vec_unop(2, "_v2f64_fneg", &mut module, v2f64.clone(), UnOp::FNeg);
    build_vec_unop(3, "_v2f64_fabs", &mut module, v2f64, UnOp::FAbs);
    build_vec_unop(
        4,
        "_v4i32_neg",
        &mut module,
        Ty::Vector(Box::new(Ty::I32), 4),
        UnOp::Neg,
    );
    build_vec_unop(
        5,
        "_v2i64_neg",
        &mut module,
        Ty::Vector(Box::new(Ty::I64), 2),
        UnOp::Neg,
    );
    module
}

fn compile_to_obj_at(module: &TrustIrModule, opt_level: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(module)
        .expect("packed FP fneg/fabs must compile (coverage gate included)");
    assert!(!result.object_code.is_empty());
    result.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <string.h>
#include <stdint.h>

extern void _v4f32_fneg(const float *in, float *out);
extern void _v4f32_fabs(const float *in, float *out);
extern void _v2f64_fneg(const double *in, double *out);
extern void _v2f64_fabs(const double *in, double *out);
extern void _v4i32_neg(const int32_t *in, int32_t *out);
extern void _v2i64_neg(const int64_t *in, int64_t *out);

int main(void) {
    {
        float in[4]   = { 1.5f, -2.5f,  0.0f, -0.0f };
        float negE[4] = { -1.5f, 2.5f, -0.0f,  0.0f };  /* bit-exact, incl signed zero */
        float absE[4] = {  1.5f, 2.5f,  0.0f,  0.0f };
        float out[4];
        _v4f32_fneg(in, out);
        if (memcmp(out, negE, sizeof out) != 0) return 1;
        _v4f32_fabs(in, out);
        if (memcmp(out, absE, sizeof out) != 0) return 2;
    }
    {
        double in[2]   = { 3.25, -4.75 };
        double negE[2] = { -3.25, 4.75 };
        double absE[2] = { 3.25,  4.75 };
        double out[2];
        _v2f64_fneg(in, out);
        if (memcmp(out, negE, sizeof out) != 0) return 3;
        _v2f64_fabs(in, out);
        if (memcmp(out, absE, sizeof out) != 0) return 4;
    }
    {
        /* fneg(-0.0)=+0.0 and fabs(-0.0)=+0.0 -> all bits zero */
        float in[4] = { -0.0f, -0.0f, -0.0f, -0.0f };
        float out[4];
        _v4f32_fneg(in, out);
        for (int i = 0; i < 4; i++) { uint32_t b; memcpy(&b, &out[i], 4); if (b != 0) return 5; }
        _v4f32_fabs(in, out);
        for (int i = 0; i < 4; i++) { uint32_t b; memcpy(&b, &out[i], 4); if (b != 0) return 6; }
    }
    {
        /* packed integer negate = 0 - v, incl INT_MIN wrap */
        int32_t in[4] = { 1, -2, 0, -2147483647 - 1 };  /* last = INT32_MIN */
        int32_t E[4]  = { -1, 2, 0, -2147483647 - 1 };  /* -INT32_MIN wraps to itself */
        int32_t out[4];
        _v4i32_neg(in, out);
        if (memcmp(out, E, sizeof out) != 0) return 7;
    }
    {
        int64_t in[2] = { 5, -9 };
        int64_t E[2]  = { -5, 9 };
        int64_t out[2];
        _v2i64_neg(in, out);
        if (memcmp(out, E, sizeof out) != 0) return 8;
    }
    printf("packed FP fneg/fabs + int neg (v4f32/v2f64/v4i32/v2i64) correct\n");
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
fn e2e_aarch64_packed_fp_fneg_fabs() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_to_obj_at(&module, opt);
        let Some(code) = link_run_exit_code("vec_fp_unary", &obj, DRIVER) else {
            return;
        };
        assert_eq!(
            code, 0,
            "packed FP fneg/fabs runtime mismatch at {opt:?} (failing-case code {code})",
        );
    }
}
