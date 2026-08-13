// trust-cg-codegen/tests/e2e_aarch64_fptosi_sat.rs
//
// End-to-end coverage for register-width (i64/u64) SATURATING float->int casts
// (Rust `f as i64`/`as isize`/`as u64`/`as usize`; LLVM fptosi.sat/fptoui.sat).
// AArch64 FCVTZS/FCVTZU are round-toward-zero, map NaN->0, and saturate at the
// i64/u64 range — which IS the destination range — so a register-width saturating
// cast lowers to the same instruction (and proof) as the raw cast. This test
// runs on M-series and checks the saturating edge cases (NaN, +/-inf, overflow,
// negative-to-unsigned) plus in-range values against the exact reference.
//
// Narrower destinations (i8/i16/i32) use an explicit destination-width clamp;
// the exhaustive and edge differential below checks that expansion end to end.
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

fn build_sat(func_id: u32, name: &str, m: &mut TrustIrModule, op: CastOp, src: Ty, dst: Ty) {
    let ft = m.add_func_type(FuncTy {
        params: vec![src.clone()],
        returns: vec![dst.clone()],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
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
    let mut m = TrustIrModule::new("fptosi_sat");
    build_sat(0, "_d_s64", &mut m, CastOp::FPToSISat, Ty::F64, Ty::I64);
    build_sat(1, "_d_u64", &mut m, CastOp::FPToUISat, Ty::F64, Ty::U64);
    build_sat(2, "_f_s64", &mut m, CastOp::FPToSISat, Ty::F32, Ty::I64);
    m
}

fn compile_ok(module: &TrustIrModule, opt: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    });
    let r = compiler
        .compile(module)
        .expect("register-width saturating casts must compile (certs included)");
    assert!(!r.object_code.is_empty());
    r.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
#include <math.h>

extern int64_t  _d_s64(double);
extern uint64_t _d_u64(double);
extern int64_t  _f_s64(float);

int main(void) {
    /* in-range: the C cast is a defined, exact oracle */
    double inr[] = { 0.0, 3.7, -3.7, -1.0, 1e15, -1e15, 9.2e18 };
    for (unsigned i=0;i<sizeof(inr)/sizeof(inr[0]);i++)
        if (_d_s64(inr[i]) != (int64_t)inr[i]) return 1;
    double inu[] = { 0.0, 3.7, 1e15, 1.8e19 };
    for (unsigned i=0;i<sizeof(inu)/sizeof(inu[0]);i++)
        if (_d_u64(inu[i]) != (uint64_t)inu[i]) return 2;

    /* saturating edge cases (C cast is UB here — manual oracle) */
    if (_d_s64(NAN)       != 0)         return 3;
    if (_d_u64(NAN)       != 0)         return 4;
    if (_d_s64(INFINITY)  != INT64_MAX) return 5;
    if (_d_s64(-INFINITY) != INT64_MIN) return 6;
    if (_d_s64(1e30)      != INT64_MAX) return 7;
    if (_d_s64(-1e30)     != INT64_MIN) return 8;
    if (_d_u64(1e30)      != UINT64_MAX) return 9;
    if (_d_u64(-5.0)      != 0)         return 10; /* negative -> 0 (unsigned) */
    if (_f_s64(1e30f)     != INT64_MAX) return 11;

    printf("register-width i64/u64 saturating float->int casts correct (NaN/inf/overflow/neg/in-range)\n");
    return 0;
}
"#;

fn link_run(tag: &str, obj: &[u8], driver: &str) -> Option<i32> {
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
    fs::write(&drv_path, driver).unwrap();
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
    let run = Command::new(bin_path.to_str().unwrap()).output().unwrap();
    let code = run.status.code().unwrap_or(-1);
    let _ = fs::remove_dir_all(&dir);
    Some(code)
}

#[test]
fn e2e_aarch64_register_width_saturating_casts() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_ok(&module, opt);
        let Some(code) = link_run("fptosi_sat", &obj, DRIVER) else {
            return;
        };
        assert_eq!(
            code, 0,
            "saturating cast mismatch at {opt:?} (case code {code})"
        );
    }
}

fn build_narrow_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("narrow_sat");
    build_sat(0, "_h_s8", &mut m, CastOp::FPToSISat, Ty::F16, Ty::I8);
    build_sat(1, "_h_u8", &mut m, CastOp::FPToUISat, Ty::F16, Ty::U8);
    build_sat(2, "_f_s32", &mut m, CastOp::FPToSISat, Ty::F32, Ty::I32);
    build_sat(3, "_f_u16", &mut m, CastOp::FPToUISat, Ty::F32, Ty::U16);
    m
}

const NARROW_DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
#include <math.h>
#include <string.h>

extern int8_t   _h_s8(_Float16);
extern uint8_t  _h_u8(_Float16);
extern int32_t  _f_s32(float);
extern uint16_t _f_u16(float);

static long clampl(long v, long lo, long hi){ return v<lo?lo:(v>hi?hi:v); }

int main(void) {
    /* EXHAUSTIVE: every f16 bit pattern -> i8 and u8 (NaN/inf/subnormal/
       boundary/out-of-range all covered). Reference = LLVM fptosi.sat.sat
       semantics: NaN->0, round-toward-zero, clamp to dest range. */
    for (unsigned u = 0; u < 65536; u++) {
        uint16_t b = (uint16_t)u; _Float16 h; memcpy(&h, &b, 2);
        float f = (float)h;
        int rs = isnan(f) ? 0 : (int)clampl((long)truncf(f), -128, 127);
        int ru = isnan(f) ? 0 : (f <= 0.0f ? 0 : (int)clampl((long)truncf(f), 0, 255));
        if (_h_s8(h) != (int8_t)rs)  return 1;
        if (_h_u8(h) != (uint8_t)ru) return 2;
    }
    /* f32 -> i32/u16 edge cases (C cast is UB out of range -> manual oracle) */
    float fs[] = { 0.0f, 3.7f, -3.7f, 1e10f, -1e10f, 2.2e9f, NAN, INFINITY,
                   -INFINITY, 60000.5f, -1.0f, 65535.9f };
    for (unsigned i = 0; i < sizeof(fs)/sizeof(fs[0]); i++) {
        float f = fs[i];
        int rs = isnan(f) ? 0 : (int)clampl((long)truncf(f), -2147483648L, 2147483647L);
        if (_f_s32(f) != rs) return 3;
        int ru = isnan(f) ? 0 : (f <= 0.0f ? 0 : (int)clampl((long)truncf(f), 0, 65535));
        if (_f_u16(f) != (uint16_t)ru) return 4;
    }
    printf("narrow saturating f16->i8/u8 EXHAUSTIVE (131072) + f32->i32/u16 edges correct\n");
    return 0;
}
"#;

#[test]
fn e2e_aarch64_narrow_saturating_casts_exhaustive() {
    // i8/i16/i32/u8/u16/u32 saturating casts: FCVTZS/FCVTZU to i64 (NaN->0,
    // i64-saturating) then a destination-width clamp then truncate.
    let module = build_narrow_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_ok(&module, opt);
        let Some(code) = link_run("narrow_sat", &obj, NARROW_DRIVER) else {
            return;
        };
        assert_eq!(
            code, 0,
            "narrow saturating cast mismatch at {opt:?} (case code {code})",
        );
    }
}
