// trust-cg-codegen/tests/e2e_aarch64_fp_to_int.rs
//
// End-to-end (compile -> link -> RUN on aarch64-apple-darwin) coverage for
// raw float->int truncation casts (Opcode::FcvtToInt / FcvtToUint, LLVM
// `fptosi`/`fptoui`), the reverse direction of e2e_aarch64_sitofp_signext.rs.
//
// The lowering is `FCVTZS/FCVTZU Xd, Sn/Dn` (round toward zero) then a
// width-narrowing move for the destination. Raw fptosi/fptoui is UB on
// out-of-range/NaN (Rust's saturating `as` is a distinct op, FPToSISat, which
// currently fails closed pending a destination-width clamp), so this test uses
// only IN-RANGE finite inputs where the C cast oracle is well defined. It pins
// bit-exact agreement with clang/LLVM over signed and unsigned destinations of
// every width, including negative sources (the sign-discipline class that the
// sitofp direction miscompiled).
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

fn build_fptoi(func_id: u32, name: &str, m: &mut TrustIrModule, op: CastOp, src: Ty, dst: Ty) {
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
    use CastOp::{FPToSI, FPToUI};
    let mut m = TrustIrModule::new("fp_to_int");
    build_fptoi(0, "_f32_s8", &mut m, FPToSI, Ty::F32, Ty::I8);
    build_fptoi(1, "_f32_s16", &mut m, FPToSI, Ty::F32, Ty::I16);
    build_fptoi(2, "_f32_s32", &mut m, FPToSI, Ty::F32, Ty::I32);
    build_fptoi(3, "_f32_s64", &mut m, FPToSI, Ty::F32, Ty::I64);
    build_fptoi(4, "_f64_s32", &mut m, FPToSI, Ty::F64, Ty::I32);
    build_fptoi(5, "_f64_s64", &mut m, FPToSI, Ty::F64, Ty::I64);
    build_fptoi(6, "_f32_u8", &mut m, FPToUI, Ty::F32, Ty::U8);
    build_fptoi(7, "_f32_u16", &mut m, FPToUI, Ty::F32, Ty::U16);
    build_fptoi(8, "_f32_u32", &mut m, FPToUI, Ty::F32, Ty::U32);
    build_fptoi(9, "_f64_u32", &mut m, FPToUI, Ty::F64, Ty::U32);
    build_fptoi(10, "_f64_u64", &mut m, FPToUI, Ty::F64, Ty::U64);
    // Float -> i128/u128 route through the __fix*ti compiler-rt libcalls
    // (FCVTZS/FCVTZU cannot target a 128-bit register).
    build_fptoi(11, "_f64_s128", &mut m, FPToSI, Ty::F64, Ty::I128);
    build_fptoi(12, "_f64_u128", &mut m, FPToUI, Ty::F64, Ty::U128);
    build_fptoi(13, "_f32_s128", &mut m, FPToSI, Ty::F32, Ty::I128);
    m
}

fn compile_to_obj_at(module: &TrustIrModule, opt_level: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(module)
        .expect("float->int casts must compile (proof/coverage gate included)");
    assert!(!result.object_code.is_empty());
    result.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>

extern int8_t  _f32_s8(float);
extern int16_t _f32_s16(float);
extern int32_t _f32_s32(float);
extern int64_t _f32_s64(float);
extern int32_t _f64_s32(double);
extern int64_t _f64_s64(double);
extern uint8_t  _f32_u8(float);
extern uint16_t _f32_u16(float);
extern uint32_t _f32_u32(float);
extern uint32_t _f64_u32(double);
extern uint64_t _f64_u64(double);
extern __int128 _f64_s128(double);
extern unsigned __int128 _f64_u128(double);
extern __int128 _f32_s128(float);

int main(void){
    /* float -> i128/u128 (in-range, via __fix*ti) */
    double d128[] = { 0.0, 3.7, -3.7, 1e18, -1e18, 1e30, -1e30, 1e10, 1.234e28 };
    for (unsigned k=0;k<sizeof(d128)/sizeof(d128[0]);k++) {
        if (_f64_s128(d128[k]) != (__int128)d128[k]) return 20;
        if (d128[k] >= 0.0 && _f64_u128(d128[k]) != (unsigned __int128)d128[k]) return 21;
    }
    float f128[] = { 0.0f, 3.7f, -3.7f, 1e18f, -1e18f, 1e10f };
    for (unsigned k=0;k<sizeof(f128)/sizeof(f128[0]);k++)
        if (_f32_s128(f128[k]) != (__int128)f128[k]) return 22;

    /* signed, in i8 range (truncate toward zero) */
    float s8v[] = { -128.0f, -100.9f, -1.5f, -0.0f, 0.0f, 1.9f, 100.9f, 127.0f };
    for (unsigned k=0;k<sizeof(s8v)/sizeof(s8v[0]);k++)
        if (_f32_s8(s8v[k]) != (int8_t)s8v[k]) return 1;
    float s16v[] = { -32768.0f, -100.9f, -1.5f, 0.0f, 1.9f, 32767.0f };
    for (unsigned k=0;k<sizeof(s16v)/sizeof(s16v[0]);k++)
        if (_f32_s16(s16v[k]) != (int16_t)s16v[k]) return 2;
    float s32v[] = { -2000000.9f, -100.9f, -1.5f, 0.0f, 1.9f, 2000000.9f };
    for (unsigned k=0;k<sizeof(s32v)/sizeof(s32v[0]);k++)
        if (_f32_s32(s32v[k]) != (int32_t)s32v[k]) return 3;
    for (unsigned k=0;k<sizeof(s32v)/sizeof(s32v[0]);k++)
        if (_f32_s64(s32v[k]) != (int64_t)s32v[k]) return 4;
    double d32v[] = { -2000000000.9, -100.9, -1.5, 0.0, 1.9, 2000000000.9 };
    for (unsigned k=0;k<sizeof(d32v)/sizeof(d32v[0]);k++)
        if (_f64_s32(d32v[k]) != (int32_t)d32v[k]) return 5;
    double d64v[] = { -9.0e15, -100.9, 0.0, 1.9, 9.0e15 };
    for (unsigned k=0;k<sizeof(d64v)/sizeof(d64v[0]);k++)
        if (_f64_s64(d64v[k]) != (int64_t)d64v[k]) return 6;

    /* unsigned, in range (non-negative) */
    float u8v[] = { 0.0f, 1.9f, 100.9f, 200.9f, 255.0f };
    for (unsigned k=0;k<sizeof(u8v)/sizeof(u8v[0]);k++)
        if (_f32_u8(u8v[k]) != (uint8_t)u8v[k]) return 7;
    float u16v[] = { 0.0f, 1.9f, 60000.9f, 65535.0f };
    for (unsigned k=0;k<sizeof(u16v)/sizeof(u16v[0]);k++)
        if (_f32_u16(u16v[k]) != (uint16_t)u16v[k]) return 8;
    float u32v[] = { 0.0f, 1.9f, 4000000.9f };
    for (unsigned k=0;k<sizeof(u32v)/sizeof(u32v[0]);k++)
        if (_f32_u32(u32v[k]) != (uint32_t)u32v[k]) return 9;
    double du32v[] = { 0.0, 1.9, 4000000000.9 };
    for (unsigned k=0;k<sizeof(du32v)/sizeof(du32v[0]);k++)
        if (_f64_u32(du32v[k]) != (uint32_t)du32v[k]) return 10;
    double du64v[] = { 0.0, 1.9, 9.0e18 };
    for (unsigned k=0;k<sizeof(du64v)/sizeof(du64v[0]);k++)
        if (_f64_u64(du64v[k]) != (uint64_t)du64v[k]) return 11;

    printf("raw fptosi/fptoui f32/f64 -> i8..i64/u8..u64 bit-exact vs clang (in-range)\n");
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
fn e2e_aarch64_fptosi_fptoui_in_range() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_to_obj_at(&module, opt);
        let Some(code) = link_run_exit_code("fp_to_int", &obj, DRIVER) else {
            return;
        };
        assert_eq!(
            code, 0,
            "float->int cast runtime mismatch at {opt:?} (failing-case code {code})",
        );
    }
}
