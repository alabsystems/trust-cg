// trust-cg-codegen/tests/e2e_aarch64_calling_conv.rs
//
// Completeness: non-C calling conventions. trust-cg previously fail-closed on
// every convention except C. On aarch64, `Fast` and `Cold` are LLVM
// optimization-hint conventions for which the C (AAPCS64) register ABI is always
// a valid lowering, and `Rust` uses the same AAPCS64 register sequence as C for
// scalars/pointers (aggregate *layout* is carried by StructRepr, not the
// convention). So those three now lower via the C ABI; `Swift` (self in x20,
// error in x21) genuinely differs and stays fail-closed.
//
// The register-passing part is checked by having clang -- which uses the C ABI
// -- call a trust-cg function declared with the Rust/Fast/Cold convention and
// diffing the result. If the convention did not match the C register ABI, the
// arguments/return would be read from the wrong registers.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    BinOp, Block as TrustIrBlock, CallingConv, FieldDef, FuncTy, Function as TrustIrFunction, Inst,
    InstrNode, Module as TrustIrModule, StructDef, StructId, StructRepr, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

// `fn name(a: i64, b: i64, c: i64) -> i64 { a*b + c }` with a given convention.
fn build_fn(m: &mut TrustIrModule, id: u32, name: &str, cc: CallingConv) {
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    f.calling_conv = cc;
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::I64),
            (ValueId::new(1), Ty::I64),
            (ValueId::new(2), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(3),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(4)],
            }),
        ],
    }];
    m.add_function(f);
}

fn build_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("calling_conv");
    build_fn(&mut m, 0, "cc_rust", CallingConv::Rust);
    build_fn(&mut m, 1, "cc_fast", CallingConv::Fast);
    build_fn(&mut m, 2, "cc_cold", CallingConv::Cold);
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
extern int64_t cc_rust(int64_t,int64_t,int64_t);
extern int64_t cc_fast(int64_t,int64_t,int64_t);
extern int64_t cc_cold(int64_t,int64_t,int64_t);
int main(void){
    struct { int64_t a,b,c; } T[] = {{3,5,7},{-2,10,4},{1000000,1000000,-5},{0,999,42},{-7,-8,100}};
    for(unsigned i=0;i<sizeof(T)/sizeof(T[0]);i++){
        int64_t ref=T[i].a*T[i].b+T[i].c;
        if(cc_rust(T[i].a,T[i].b,T[i].c)!=ref){printf("cc_rust #%u\n",i);return 1;}
        if(cc_fast(T[i].a,T[i].b,T[i].c)!=ref){printf("cc_fast #%u\n",i);return 2;}
        if(cc_cold(T[i].a,T[i].b,T[i].c)!=ref){printf("cc_cold #%u\n",i);return 3;}
    }
    printf("Rust/Fast/Cold conventions use the C register ABI (bit-exact vs clang)\n");
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
fn e2e_aarch64_c_compatible_conventions() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt).expect("Rust/Fast/Cold must compile");
        let Some(code) = link_run("calling_conv", &obj) else {
            return;
        };
        assert_eq!(code, 0, "C-compatible convention mismatch at {opt:?}");
    }
}

#[test]
fn swift_convention_with_aggregate_stays_fail_closed() {
    // The Swift scalar subset -- including i128/u128 -- is admitted (it lowers
    // identically to the C register ABI; verified in e2e_aarch64_swift_scalar.rs).
    // AGGREGATE params/returns within Swift's 4-component direct budget are now
    // also admitted via scalarization (verified bit-exact vs clang swiftcall in
    // e2e_aarch64_swift_aggregate.rs). What stays GENUINELY divergent -- and so
    // fail-closed -- is a swiftcc aggregate whose combined GPR-word + FP-field
    // count is >= 5: Swift passes it indirectly / returns it via sret, which the
    // scalarization subset does not cover. Here: a 40-byte {i64*5} struct param
    // + return (budget 5) must stay rejected rather than silently mislowered.
    let mut m = TrustIrModule::new("swift_cc_agg");
    m.structs.push(StructDef {
        id: StructId::new(0),
        name: "I64x5".to_string(),
        fields: (0..5)
            .map(|i| FieldDef {
                name: format!("f{i}"),
                ty: Ty::I64,
                offset: None,
            })
            .collect(),
        size: None,
        align: None,
        repr: StructRepr::C,
    });
    let agg = Ty::Struct(StructId::new(0));
    let ft = m.add_func_type(FuncTy {
        params: vec![agg.clone()],
        returns: vec![agg.clone()],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(0), "swifty_agg", ft, BlockId::new(0));
    f.calling_conv = CallingConv::Swift;
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), agg)],
        body: vec![InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        })],
    }];
    m.add_function(f);
    let err = compile_at(&m, OptLevel::O0)
        .expect_err("Swift with aggregate params/returns must fail closed, not compile");
    assert!(
        err.contains("Swift") || err.to_lowercase().contains("calling convention"),
        "unexpected error for aggregate Swift convention: {err}"
    );
}
