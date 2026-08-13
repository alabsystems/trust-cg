// trust-cg-codegen/tests/e2e_aarch64_ctpop.rs
//
// Completeness/correctness: `UnOp::CtPop` (population count). AArch64 has no
// direct GPR popcount, so trust-cg lowers it to a width-dependent SWAR
// bit-twiddling sequence (emit_ctpop_swar in isel.rs): mask to the logical
// width, then the classic shift/mask/add reduction with 0x55/0x33/0x0F/...
// constants scaled to the type. Those masks are exactly where an off-by-a-mask
// bug hides -- invisible to a shape-only unit test but caught by counting the
// bits of many patterns and diffing against clang's __builtin_popcount.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    Block as TrustIrBlock, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, Ty, UnOp, ValueId,
};
use trust_ir::{BlockId, FuncId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

// fn name(x: ty) -> ty { return ctpop(x) }
fn build_ctpop_fn(m: &mut TrustIrModule, id: u32, name: &str, ty: Ty) {
    let ft = m.add_func_type(FuncTy {
        params: vec![ty.clone()],
        returns: vec![ty.clone()],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), ty.clone())],
        body: vec![
            InstrNode::new(Inst::UnOp {
                op: UnOp::CtPop,
                ty,
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
    let mut m = TrustIrModule::new("ctpop");
    build_ctpop_fn(&mut m, 0, "pc8", Ty::I8);
    build_ctpop_fn(&mut m, 1, "pc16", Ty::I16);
    build_ctpop_fn(&mut m, 2, "pc32", Ty::I32);
    build_ctpop_fn(&mut m, 3, "pc64", Ty::I64);
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
extern int8_t  pc8(int8_t);
extern int16_t pc16(int16_t);
extern int32_t pc32(int32_t);
extern int64_t pc64(int64_t);

int main(void){
    // Exercise the SWAR masks: all-zero, all-one, alternating, nibble, single
    // bits, and a few arbitrary patterns, at each width.
    uint8_t p8[]  = {0x00,0xFF,0x55,0xAA,0x0F,0xF0,0x01,0x80,0x7F,0x3C,0x91};
    for(unsigned i=0;i<sizeof(p8)/sizeof(p8[0]);i++){
        int8_t x = (int8_t)p8[i];
        int expect = __builtin_popcount((unsigned)(uint8_t)x);
        if((int)pc8(x) != expect){ printf("pc8 %#x -> %d != %d\n",(unsigned)(uint8_t)x,(int)pc8(x),expect); return 1; }
    }
    uint16_t p16[] = {0x0000,0xFFFF,0x5555,0xAAAA,0x0F0F,0xF0F0,0x0001,0x8000,0x1234,0xBEEF};
    for(unsigned i=0;i<sizeof(p16)/sizeof(p16[0]);i++){
        int16_t x = (int16_t)p16[i];
        int expect = __builtin_popcount((unsigned)(uint16_t)x);
        if((int)pc16(x) != expect){ printf("pc16 %#x\n",(unsigned)(uint16_t)x); return 2; }
    }
    uint32_t p32[] = {0u,0xFFFFFFFFu,0x55555555u,0xAAAAAAAAu,0x0F0F0F0Fu,1u,0x80000000u,0xDEADBEEFu,0x12345678u};
    for(unsigned i=0;i<sizeof(p32)/sizeof(p32[0]);i++){
        int32_t x = (int32_t)p32[i];
        int expect = __builtin_popcount(p32[i]);
        if((int)pc32(x) != expect){ printf("pc32 %#x\n",p32[i]); return 3; }
    }
    uint64_t p64[] = {0ull,~0ull,0x5555555555555555ull,0xAAAAAAAAAAAAAAAAull,
                      0x0F0F0F0F0F0F0F0Full,1ull,0x8000000000000000ull,0xDEADBEEFCAFEBABEull};
    for(unsigned i=0;i<sizeof(p64)/sizeof(p64[0]);i++){
        int64_t x = (int64_t)p64[i];
        int expect = __builtin_popcountll(p64[i]);
        if((int)pc64(x) != expect){ printf("pc64 %#llx\n",(unsigned long long)p64[i]); return 4; }
    }
    printf("ctpop: SWAR popcount matches __builtin_popcount across widths and patterns\n");
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
fn e2e_aarch64_ctpop_matches_clang() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt).expect("ctpop module must compile");
        let Some(code) = link_run("ctpop", &obj) else {
            return;
        };
        assert_eq!(code, 0, "ctpop result mismatch at {opt:?}");
    }
}
