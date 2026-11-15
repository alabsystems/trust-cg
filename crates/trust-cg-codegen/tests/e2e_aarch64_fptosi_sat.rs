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
use trust_cg_codegen::target::{AArch64IsaProfile, TargetSpec};

use trust_ir::{
    Block as TrustIrBlock, CastOp, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

#[path = "common/native_host.rs"]
mod native_host;

/// AArch64 Linux GNU (ELF) or macOS (Mach-O): `Compiler::new` derives the
/// host's object format and ABI, and the host `cc` links it.
fn can_link_and_run_aarch64_native() -> bool {
    native_host::NATIVE
}

fn build_sat(func_id: u32, name: &str, m: &mut TrustIrModule, op: CastOp, src: Ty, dst: Ty) {
    let ft = m
        .add_func_type(FuncTy {
            params: vec![src.clone()],
            returns: vec![dst.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
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
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
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
    })
    .with_codegen_license(permit_unlicensed());
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
    if !can_link_and_run_aarch64_native() {
        eprintln!("SKIP: needs an AArch64 Linux GNU or macOS host");
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
        .args(native_host::c_math_library_args())
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

/// The f16 sources need FEAT_FP16 (`FCVTZS/FCVTZU H`). Darwin's AOT target
/// contract admits it, so the production `Compiler` lane runs there; generic
/// Linux AOT refuses it by name (pinned below), so every native host also runs
/// the explicit-FP16 pipeline lane, the only admitted FP16 lane on Linux GNU.
/// A host CPU without FP16 is a failure, never a skip.
fn narrow_objects_at(module: &TrustIrModule, opt: OptLevel) -> Vec<(&'static str, Vec<u8>)> {
    let mut objects = Vec::new();
    if !native_host::LINUX_GNU {
        objects.push(("darwin-aot", compile_ok(module, opt)));
    }
    if native_host::NATIVE {
        assert!(
            AArch64IsaProfile::FP16.is_supported_by_host(),
            "the explicit FP16 native lane requires host FP16"
        );
        let object = native_host::compile_with_isa_profile(module, opt, AArch64IsaProfile::FP16)
            .unwrap_or_else(|error| panic!("explicit FP16 {opt:?}: {error}"));
        objects.push(("explicit-fp16", object));
    }
    objects
}

/// Generic Linux AOT keeps refusing f16 saturating conversions by name.
/// Object-level, so it runs on every host.
#[test]
fn generic_linux_aot_refuses_fp16_saturating_casts_by_name() {
    let error = Compiler::new_for_target_spec(
        CompilerConfig::default(),
        TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&build_narrow_module())
    .unwrap_err()
    .to_string();
    assert!(error.contains("FEAT_FP16 is not admitted"), "{error}");
}

#[test]
fn e2e_aarch64_narrow_saturating_casts_exhaustive() {
    // i8/i16/i32/u8/u16/u32 saturating casts: FCVTZS/FCVTZU to i64 (NaN->0,
    // i64-saturating) then a destination-width clamp then truncate.
    let module = build_narrow_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let objects = narrow_objects_at(&module, opt);
        if objects.is_empty() {
            eprintln!("SKIP: needs an AArch64 Linux GNU or macOS host");
            return;
        }
        for (lane, obj) in objects {
            let Some(code) = link_run(&format!("narrow_sat_{lane}"), &obj, NARROW_DRIVER) else {
                return;
            };
            assert_eq!(
                code, 0,
                "narrow saturating cast mismatch at {opt:?} via {lane} (case code {code})",
            );
        }
    }
}

/// The Linux GNU explicit-FP16 lane's object, checked at object level on every
/// host: the f16 saturating casts compile for the generic Linux triple.
#[test]
fn explicit_fp16_linux_saturating_cast_object_is_elf_aarch64() {
    for opt in [OptLevel::O0, OptLevel::O2] {
        let object = native_host::compile_with_isa_profile_for(
            "aarch64-unknown-linux-gnu",
            &build_narrow_module(),
            opt,
            AArch64IsaProfile::FP16,
        )
        .unwrap_or_else(|error| panic!("{opt:?}: {error}"));
        native_host::assert_elf_aarch64_object(&object);
        assert!(!native_host::text_words(&object).is_empty());
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
