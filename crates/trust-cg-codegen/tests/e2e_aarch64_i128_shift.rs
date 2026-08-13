// trust-cg-codegen/tests/e2e_aarch64_i128_shift.rs
//
// Correctness: i128 scalar shifts (`Shl`, `LShr`, `AShr`). AArch64 has no
// 128-bit shift, so trust-cg lowers each to a register-pair decomposition
// (select_i128_shl / _lshr / _ashr in isel.rs) built from 64-bit shifts, a
// cross-half spill, and CSELs that special-case shift==0 and shift>=64. Those
// boundaries (0, 63, 64, 65, 127) are exactly where a wrong CSEL condition or a
// missing zero-guard silently corrupts a half -- invisible to a shape-only unit
// test but caught by sweeping every shift amount and diffing against clang's
// native `__int128` shifts. Also exercises i128 register-pair argument passing
// (x0:x1, x2:x3) since the operands and shift amount are all i128.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    BinOp, Block as TrustIrBlock, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

// fn name(x: i128, s: i128) -> i128 { x <op> s }
fn build_shift_fn(m: &mut TrustIrModule, id: u32, name: &str, op: BinOp) {
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::I128, Ty::I128],
        returns: vec![Ty::I128],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I128), (ValueId::new(1), Ty::I128)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op,
                ty: Ty::I128,
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
    let mut m = TrustIrModule::new("i128_shift");
    build_shift_fn(&mut m, 0, "shl128", BinOp::Shl);
    build_shift_fn(&mut m, 1, "lshr128", BinOp::LShr);
    build_shift_fn(&mut m, 2, "ashr128", BinOp::AShr);
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

const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
typedef unsigned __int128 u128;
typedef __int128 s128;
extern u128  shl128(u128, u128);
extern u128  lshr128(u128, u128);
extern s128  ashr128(s128, s128);

static void pr(const char* tag, unsigned s, u128 got, u128 exp){
    printf("%s s=%u got=%016llx:%016llx exp=%016llx:%016llx\n", tag, s,
        (unsigned long long)(got>>64),(unsigned long long)got,
        (unsigned long long)(exp>>64),(unsigned long long)exp);
}

int main(void){
    // Boundary + arbitrary values, including sign-bit-set for the arithmetic shift.
    u128 vals[] = {
        0, 1, (u128)(~(u128)0),
        (u128)1 << 63, (u128)1 << 64, (u128)1 << 127,
        ((u128)0xDEADBEEFCAFEBABEull << 64) | 0x0123456789ABCDEFull,
        ((u128)0x8000000000000001ull << 64) | 0xFEDCBA9876543210ull,
        (u128)0x00000000FFFFFFFFull,
    };
    unsigned nv = sizeof(vals)/sizeof(vals[0]);
    for(unsigned i=0;i<nv;i++){
        u128 v = vals[i];
        for(unsigned s=0;s<128;s++){
            u128 se = (u128)s;
            if(shl128(v,se) != (u128)(v << s)){ pr("shl",s,shl128(v,se),(u128)(v<<s)); return 1; }
            if(lshr128(v,se) != (u128)(v >> s)){ pr("lshr",s,lshr128(v,se),(u128)(v>>s)); return 2; }
            s128 sv = (s128)v;
            if(ashr128(sv,(s128)se) != (s128)(sv >> s)){ pr("ashr",s,(u128)ashr128(sv,(s128)se),(u128)(s128)(sv>>s)); return 3; }
        }
    }
    printf("i128 shifts (shl/lshr/ashr) bit-exact vs clang across all shift amounts 0..127\n");
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
    let out = Command::new(bin_path.to_str().unwrap()).output().unwrap();
    if !out.stdout.is_empty() {
        eprint!("{}", String::from_utf8_lossy(&out.stdout));
    }
    let code = out.status.code().unwrap_or(-1);
    let _ = fs::remove_dir_all(&dir);
    Some(code)
}

#[test]
fn e2e_aarch64_i128_shift_matches_clang() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt).expect("i128-shift module must compile");
        let Some(code) = link_run("i128_shift", &obj) else {
            return;
        };
        assert_eq!(code, 0, "i128-shift result mismatch at {opt:?}");
    }
}
