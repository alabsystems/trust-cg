// trust-cg-codegen/tests/e2e_aarch64_i128_icmp.rs
//
// Correctness: i128 integer comparisons (all ten `ICmpOp` predicates). AArch64
// compares 128-bit values as register pairs (select_i128_cmp): equality ANDs
// per-half CSETs, while the ordered predicates compare the high half and fall
// back to an unsigned low-half compare -- with the signed/unsigned distinction
// applied only to the high half. That split is exactly where a wrong condition
// code flips a result near a half boundary (e.g. hi equal, lo differing; or the
// signed/unsigned sign bit of the high half). Shape-only unit tests can't catch
// a swapped CC; sweeping ordered pairs of boundary values and diffing against
// clang's native __int128 comparisons does.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_ir::{
    Block as TrustIrBlock, CastOp, FuncTy, Function as TrustIrFunction, ICmpOp, Inst, InstrNode,
    Module as TrustIrModule, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

// fn name(a: i128, b: i128) -> i64 { (i64)(a <pred> b) }
fn build_cmp_fn(m: &mut TrustIrModule, id: u32, name: &str, op: ICmpOp) {
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::I128, Ty::I128],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I128), (ValueId::new(1), Ty::I128)],
        body: vec![
            InstrNode::new(Inst::ICmp {
                op,
                ty: Ty::I128,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::I64,
                operand: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    m.add_function(f);
}

fn build_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("i128_icmp");
    for (i, (name, op)) in [
        ("cmp_eq", ICmpOp::Eq),
        ("cmp_ne", ICmpOp::Ne),
        ("cmp_ult", ICmpOp::Ult),
        ("cmp_ule", ICmpOp::Ule),
        ("cmp_ugt", ICmpOp::Ugt),
        ("cmp_uge", ICmpOp::Uge),
        ("cmp_slt", ICmpOp::Slt),
        ("cmp_sle", ICmpOp::Sle),
        ("cmp_sgt", ICmpOp::Sgt),
        ("cmp_sge", ICmpOp::Sge),
    ]
    .into_iter()
    .enumerate()
    {
        build_cmp_fn(&mut m, i as u32, name, op);
    }
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
extern int64_t cmp_eq(u128,u128), cmp_ne(u128,u128);
extern int64_t cmp_ult(u128,u128), cmp_ule(u128,u128), cmp_ugt(u128,u128), cmp_uge(u128,u128);
extern int64_t cmp_slt(s128,s128), cmp_sle(s128,s128), cmp_sgt(s128,s128), cmp_sge(s128,s128);

int main(void){
    // Boundary values chosen to stress the hi/lo split and the signed/unsigned
    // high-half sign bit: equal-hi/differing-lo, differing-hi, sign boundaries.
    u128 V[] = {
        0, 1, 2,
        (u128)0xFFFFFFFFFFFFFFFFull,               // lo all ones, hi zero
        (u128)1 << 64,                             // hi = 1, lo = 0
        ((u128)1 << 64) | 1,                       // hi = 1, lo = 1
        (u128)1 << 127,                            // sign bit (INT128_MIN as signed)
        ((u128)1 << 127) | 1,
        (u128)(~(u128)0),                          // all ones (-1 signed, UINT128_MAX unsigned)
        ((u128)0x8000000000000000ull << 64),       // hi sign bit only
        ((u128)0x7FFFFFFFFFFFFFFFull << 64) | 0xFFFFFFFFFFFFFFFFull, // INT128_MAX
    };
    unsigned n = sizeof(V)/sizeof(V[0]);
    for(unsigned i=0;i<n;i++) for(unsigned j=0;j<n;j++){
        u128 a=V[i], b=V[j];
        s128 sa=(s128)a, sb=(s128)b;
        if(cmp_eq(a,b)  != (a==b))  { printf("eq %u %u\n",i,j);  return 1; }
        if(cmp_ne(a,b)  != (a!=b))  { printf("ne %u %u\n",i,j);  return 2; }
        if(cmp_ult(a,b) != (a<b))   { printf("ult %u %u\n",i,j); return 3; }
        if(cmp_ule(a,b) != (a<=b))  { printf("ule %u %u\n",i,j); return 4; }
        if(cmp_ugt(a,b) != (a>b))   { printf("ugt %u %u\n",i,j); return 5; }
        if(cmp_uge(a,b) != (a>=b))  { printf("uge %u %u\n",i,j); return 6; }
        if(cmp_slt(sa,sb) != (sa<sb))  { printf("slt %u %u\n",i,j); return 7; }
        if(cmp_sle(sa,sb) != (sa<=sb)) { printf("sle %u %u\n",i,j); return 8; }
        if(cmp_sgt(sa,sb) != (sa>sb))  { printf("sgt %u %u\n",i,j); return 9; }
        if(cmp_sge(sa,sb) != (sa>=sb)) { printf("sge %u %u\n",i,j); return 10; }
    }
    printf("i128 comparisons (all 10 predicates) bit-exact vs clang across boundary pairs\n");
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
fn e2e_aarch64_i128_icmp_matches_clang() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt).expect("i128-icmp module must compile");
        let Some(code) = link_run("i128_icmp", &obj) else {
            return;
        };
        assert_eq!(code, 0, "i128-icmp result mismatch at {opt:?}");
    }
}
