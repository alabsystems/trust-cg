// trust-cg-codegen/tests/e2e_aarch64_fp_minmax.rs
//
// End-to-end (compile -> link -> RUN) coverage for scalar FP min/max
// (BinOp::FMin / FMax == Rust f{32,64}::min/max == IEEE minimumNumber/
// maximumNumber), which fail-closed on AArch64 before FMINNM/FMAXNM were wired.
// The on-host run is the GOLD-STANDARD evidence for the NaN/±0 semantics the SMT
// model only approximates: a lone NaN yields the NUMBER, and min(-0,+0) = -0.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    BinOp, Block as TrustIrBlock, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, Ty,
};
use trust_ir::{BlockId, FuncId, ValueId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

/// `fn name(a: E, b: E) -> E { a <op> b }` for FP element E and BinOp op.
fn build_fp_binop(func_id: u32, name: &str, module: &mut TrustIrModule, elem_ty: Ty, op: BinOp) {
    let ft = module.add_func_type(FuncTy {
        params: vec![elem_ty.clone(), elem_ty.clone()],
        returns: vec![elem_ty.clone()],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), elem_ty.clone()),
            (ValueId::new(1), elem_ty.clone()),
        ],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op,
                ty: elem_ty,
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

fn build_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("fp_minmax");
    build_fp_binop(0, "_f32_min", &mut module, Ty::F32, BinOp::FMin);
    build_fp_binop(1, "_f32_max", &mut module, Ty::F32, BinOp::FMax);
    build_fp_binop(2, "_f64_min", &mut module, Ty::F64, BinOp::FMin);
    build_fp_binop(3, "_f64_max", &mut module, Ty::F64, BinOp::FMax);
    module
}

fn compile_to_obj_at(module: &TrustIrModule, opt_level: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level,
        ..CompilerConfig::default()
    });
    let result = compiler.compile(module).expect("FP min/max must compile");
    assert!(!result.object_code.is_empty());
    result.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

extern float  _f32_min(float a, float b);
extern float  _f32_max(float a, float b);
extern double _f64_min(double a, double b);
extern double _f64_max(double a, double b);

static int eqf(float a, float b)   { return memcmp(&a, &b, sizeof a) == 0; }
static int eqd(double a, double b) { return memcmp(&a, &b, sizeof a) == 0; }

int main(void) {
    float  nanf = NAN, inf = INFINITY;
    double nand = NAN, infd = INFINITY;

    /* ---- f32::min ---- */
    if (_f32_min(3.0f, 5.0f) != 3.0f) return 1;
    if (_f32_min(5.0f, 3.0f) != 3.0f) return 2;
    /* lone NaN yields the NUMBER (minimumNumber), either operand position */
    if (_f32_min(nanf, 5.0f) != 5.0f) return 3;
    if (_f32_min(5.0f, nanf) != 5.0f) return 4;
    /* signed zero: min(-0,+0) == -0 (bit-exact) */
    if (!eqf(_f32_min(-0.0f, 0.0f), -0.0f)) return 5;
    if (!eqf(_f32_min(0.0f, -0.0f), -0.0f)) return 6;
    if (_f32_min(-inf, 0.0f) != -inf) return 7;

    /* ---- f32::max ---- */
    if (_f32_max(3.0f, 5.0f) != 5.0f) return 8;
    if (_f32_max(nanf, 5.0f) != 5.0f) return 9;
    if (_f32_max(5.0f, nanf) != 5.0f) return 10;
    if (!eqf(_f32_max(-0.0f, 0.0f), 0.0f)) return 11;
    if (_f32_max(inf, 0.0f) != inf) return 12;

    /* ---- f64::min / max ---- */
    if (_f64_min(3.0, 5.0) != 3.0) return 13;
    if (_f64_min(nand, 5.0) != 5.0) return 14;
    if (_f64_min(5.0, nand) != 5.0) return 15;
    if (!eqd(_f64_min(-0.0, 0.0), -0.0)) return 16;
    if (_f64_max(3.0, 5.0) != 5.0) return 17;
    if (_f64_max(nand, 5.0) != 5.0) return 18;
    if (!eqd(_f64_max(-0.0, 0.0), 0.0)) return 19;
    if (_f64_max(infd, 0.0) != infd) return 20;

    printf("scalar FP min/max (FMINNM/FMAXNM) correct: NaN-away, signed-zero, inf\n");
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
fn e2e_aarch64_fp_minmax() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_to_obj_at(&module, opt);
        let Some(code) = link_run_exit_code("fp_minmax", &obj, DRIVER) else {
            return;
        };
        assert_eq!(
            code, 0,
            "scalar FP min/max runtime mismatch at {opt:?} (failing-case code {code})",
        );
    }
}
