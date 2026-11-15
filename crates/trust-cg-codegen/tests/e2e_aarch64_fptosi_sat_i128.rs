// trust-cg-codegen/tests/e2e_aarch64_fptosi_sat_i128.rs
//
// Completeness: saturating float -> i128/u128 (`f as i128` / `f as u128` in
// Rust, LLVM `fptosi.sat` / `fptoui.sat`), previously fail-closed. Rust's `as`
// is saturating: NaN -> 0, out-of-range clamps to MIN/MAX, else round toward
// zero.
//
// Raw __fix*ti helpers do not promise saturation outside their input domain.
// The lowerer clamps those cases and passes a finite, in-range operand to
// the helper. This test checks f32/f64 casts against an independent C
// truncation-and-clamping oracle at O0-O3. GNU linker wrappers reject every
// out-of-domain helper argument, including NaNs and infinities.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

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

fn build_sat(id: u32, name: &str, m: &mut TrustIrModule, op: CastOp, src: Ty, dst: Ty) {
    let ft = m
        .add_func_type(FuncTy {
            params: vec![src.clone()],
            returns: vec![dst.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
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
    use CastOp::{FPToSISat, FPToUISat};
    let mut m = TrustIrModule::new("fptosi_sat_i128");
    build_sat(0, "s_d128", &mut m, FPToSISat, Ty::F64, Ty::I128);
    build_sat(1, "u_d128", &mut m, FPToUISat, Ty::F64, Ty::U128);
    build_sat(2, "s_f128", &mut m, FPToSISat, Ty::F32, Ty::I128);
    build_sat(3, "u_f128", &mut m, FPToUISat, Ty::F32, Ty::U128);
    m
}

fn compile_at(module: &TrustIrModule, opt: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    })
    .with_codegen_license(permit_unlicensed());
    let r = compiler
        .compile(module)
        .expect("saturating i128 cast module must compile");
    assert!(!r.object_code.is_empty());
    r.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <math.h>
#include <float.h>
#include <stdint.h>
#include <stdlib.h>
typedef __int128 i128; typedef unsigned __int128 u128;
extern i128 s_d128(double); extern u128 u_d128(double);
extern i128 s_f128(float);  extern u128 u_f128(float);

#ifdef TCG_WRAP_FIX_HELPERS
extern i128 __real___fixdfti(double); extern u128 __real___fixunsdfti(double);
extern i128 __real___fixsfti(float); extern u128 __real___fixunssfti(float);
static void check_helper(double f, int sign) {
    if (!(f >= (sign ? -0x1p127 : 0.0) && f < (sign ? 0x1p127 : 0x1p128))) {
        fprintf(stderr, "out-of-domain raw conversion: signed=%d value=%a\n", sign, f);
        abort();
    }
}
i128 __wrap___fixdfti(double f){check_helper(f,1);return __real___fixdfti(f);}
u128 __wrap___fixunsdfti(double f){check_helper(f,0);return __real___fixunsdfti(f);}
i128 __wrap___fixsfti(float f){check_helper(f,1);return __real___fixsfti(f);}
u128 __wrap___fixunssfti(float f){check_helper(f,0);return __real___fixunssfti(f);}
#endif

static i128 sref(double f){
    i128 MAX=(i128)(((u128)1<<127)-1), MIN=-MAX-1;
    if(f!=f) return 0;
    if(f >= 0x1p127) return MAX;
    if(f <  -0x1p127) return MIN;
    return (i128)f;
}
static u128 uref(double f){
    if(f!=f) return 0;
    if(f <= 0.0) return 0;
    if(f >= 0x1p128) return ~(u128)0;
    return (u128)f;
}

int main(void){
    double D[]={0,-0.0,1,-1,0.9,-0.9,3.7,-3.7,1e18,-1e18,1e30,-1e30,
                0x1p127,-0x1p127,nextafter(0x1p127,0),nextafter(-0x1p127,0),
                nextafter(0x1p127,INFINITY),0x1p128,-0x1p128,nextafter(0x1p128,0),
                1e40,-1e40,INFINITY,-INFINITY,NAN,DBL_MAX,-DBL_MAX,0x1p120,0x1p100,-0x1p100,42.0,-42.0};
    for(unsigned i=0;i<sizeof(D)/sizeof(D[0]);i++){
        double f=D[i];
        if(s_d128(f)!=sref(f)){printf("s_d128 f=%a\n",f);return 1;}
        if(u_d128(f)!=uref(f)){printf("u_d128 f=%a\n",f);return 2;}
    }
    float F[]={0,-0.0f,1,-1,3.7f,-3.7f,1e18f,-1e18f,0x1p127f,-0x1p127f,
               nextafterf(0x1p127f,0),nextafterf(0x1p127f,INFINITY),0x1p128f,-0x1p128f,
               1e30f,-1e30f,INFINITY,-INFINITY,NAN,FLT_MAX,-FLT_MAX,0x1p100f,42.0f,-42.0f};
    for(unsigned i=0;i<sizeof(F)/sizeof(F[0]);i++){
        float f=F[i]; double d=(double)f;
        if(s_f128(f)!=sref(d)){printf("s_f128 f=%a\n",(double)f);return 3;}
        if(u_f128(f)!=uref(d)){printf("u_f128 f=%a\n",(double)f);return 4;}
    }
    uint64_t seed=UINT64_C(0x72ec019d623481ab);
    for(unsigned i=0;i<1024;i++) {
        seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;
        union {uint64_t bits; double f;} d={.bits=seed};
        union {uint32_t bits; float f;} f={.bits=(uint32_t)(seed>>16)};
        if(s_d128(d.f)!=sref(d.f)||u_d128(d.f)!=uref(d.f)) {
            printf("random double bits=%016llx\n",(unsigned long long)seed);return 5;
        }
        if(s_f128(f.f)!=sref((double)f.f)||u_f128(f.f)!=uref((double)f.f)) {
            printf("random float bits=%08x\n",f.bits);return 6;
        }
    }
    printf("saturating f32/f64 -> i128/u128 matches independent trunc-and-clamp oracle\n");
    return 0;
}
"#;

fn link_run(tag: &str, obj: &[u8]) -> Option<i32> {
    if !can_link_and_run_aarch64_native() {
        eprintln!("SKIP: needs an AArch64 Linux GNU or macOS host");
        return None;
    }
    let dir = fresh_dir::create(&format!("trust_cg_{tag}_e2e-"));
    eprintln!("SAT_I128_NATIVE_DIR={}", dir.display());
    let obj_path = dir.join(format!("{tag}.o"));
    let drv_path = dir.join("driver.c");
    let bin_path = dir.join(format!("{tag}_bin"));
    fs::write(&obj_path, obj).unwrap();
    fs::write(&drv_path, DRIVER).unwrap();
    let link = Command::new("cc")
        .args([
            drv_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-lm",
            "-o",
            bin_path.to_str().unwrap(),
        ])
        .args(native_host::c_math_library_args())
        .args(if cfg!(target_os = "linux") {
            vec![
                "-DTCG_WRAP_FIX_HELPERS",
                "-Wl,--wrap=__fixdfti",
                "-Wl,--wrap=__fixunsdfti",
                "-Wl,--wrap=__fixsfti",
                "-Wl,--wrap=__fixunssfti",
            ]
        } else {
            vec![]
        })
        .output()
        .expect("cc");
    assert!(
        link.status.success(),
        "link:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let output = Command::new(bin_path.to_str().unwrap()).output().unwrap();
    eprintln!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let code = output.status.code().unwrap_or(-1);
    Some(code)
}

#[test]
fn e2e_aarch64_fptosi_fptoui_sat_i128() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let obj = compile_at(&module, opt);
        let Some(code) = link_run("fptosi_sat_i128", &obj) else {
            return;
        };
        assert_eq!(
            code, 0,
            "saturating i128 cast mismatch at {opt:?} (failing code {code})",
        );
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
