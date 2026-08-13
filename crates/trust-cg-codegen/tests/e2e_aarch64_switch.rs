// trust-cg-codegen/tests/e2e_aarch64_switch.rs
//
// Completeness: `Inst::Switch`. trust-cg picks between two lowering strategies
// (crates/trust-cg-lower/src/switch.rs):
//   * a DENSE jump table (PC-relative table indexed by the selector, then BR) --
//     the interesting path because it materializes a table address and does an
//     indirect branch through it; and
//   * a SPARSE linear scan (a chain of compare/branch) for scattered cases.
//
// Both are checked differentially against a clang-compiled `switch` oracle over
// the whole interesting input range (each case value, the boundaries just
// outside it, and default-hitting values). A wrong table base, a wrong index
// bias, or an off-by-one in the range check would send some selector to the
// wrong arm and diverge from clang.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    Block as TrustIrBlock, Constant, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, SwitchCase, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

// A block `bbN:` that just returns the i64 constant `k`. `vid` is a
// function-unique SSA id for the constant.
fn ret_const_block(bb: u32, vid: u32, k: i64) -> TrustIrBlock {
    TrustIrBlock {
        id: BlockId::new(bb),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(k as i128),
            })
            .with_result(ValueId::new(vid)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(vid)],
            }),
        ],
    }
}

// Build `fn name(x: i64) -> i64 { switch (x) { case k_i: return v_i; default: return dflt } }`.
// `arms` are (case_value, return_value); default block returns `dflt`.
fn build_switch_fn(m: &mut TrustIrModule, id: u32, name: &str, arms: &[(i64, i64)], dflt: i64) {
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));

    // Entry block 0 holds the Switch terminator. Case i -> block (i+1),
    // default -> block (arms.len()+1). SSA ids for the case constants start
    // at 100 to stay clear of the selector (%0).
    let default_bb = arms.len() as u32 + 1;
    let cases: Vec<SwitchCase> = arms
        .iter()
        .enumerate()
        .map(|(i, (cv, _))| SwitchCase {
            value: Constant::Int(*cv as i128),
            target: BlockId::new(i as u32 + 1),
            args: vec![],
        })
        .collect();

    let mut blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![InstrNode::new(Inst::Switch {
            value: ValueId::new(0),
            default: BlockId::new(default_bb),
            default_args: vec![],
            cases,
            exhaustive_enum_unreachable: false,
        })],
    }];
    for (i, (_, rv)) in arms.iter().enumerate() {
        blocks.push(ret_const_block(i as u32 + 1, 100 + i as u32, *rv));
    }
    blocks.push(ret_const_block(default_bb, 100 + arms.len() as u32, dflt));

    f.blocks = blocks;
    m.add_function(f);
}

fn build_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("switch");
    // Dense, contiguous 0..=5 -> jump table.
    build_switch_fn(
        &mut m,
        0,
        "dense_sw",
        &[(0, 100), (1, 111), (2, 122), (3, 133), (4, 144), (5, 155)],
        -1,
    );
    // Sparse, scattered (incl. a negative) -> linear scan / BST. Exercises the
    // emit_cmp constant-materialization fix (negative -7, wide 30000).
    build_switch_fn(
        &mut m,
        1,
        "sparse_sw",
        &[(-7, 40), (3, 10), (300, 20), (30000, 30)],
        0,
    );
    // Dense over a NEGATIVE range (-3..=3) -> jump table with a negative
    // min_val, exercising the normalize-SUB materialization fix.
    build_switch_fn(
        &mut m,
        2,
        "dense_neg_sw",
        &[
            (-3, 1000),
            (-2, 1001),
            (-1, 1002),
            (0, 1003),
            (1, 1004),
            (2, 1005),
            (3, 1006),
        ],
        -99,
    );
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
extern int64_t dense_sw(int64_t);
extern int64_t sparse_sw(int64_t);
extern int64_t dense_neg_sw(int64_t);

static int64_t dense_ref(int64_t x){
    switch(x){
        case 0: return 100; case 1: return 111; case 2: return 122;
        case 3: return 133; case 4: return 144; case 5: return 155;
        default: return -1;
    }
}
static int64_t sparse_ref(int64_t x){
    switch(x){
        case -7: return 40; case 3: return 10; case 300: return 20;
        case 30000: return 30; default: return 0;
    }
}
static int64_t dense_neg_ref(int64_t x){
    switch(x){
        case -3: return 1000; case -2: return 1001; case -1: return 1002;
        case 0: return 1003; case 1: return 1004; case 2: return 1005;
        case 3: return 1006; default: return -99;
    }
}

int main(void){
    // Every case value, the boundaries just outside the dense range, and
    // scattered default-hitting values.
    int64_t probes[] = {-100,-8,-7,-6,-4,-3,-2,-1,0,1,2,3,4,5,6,7,42,299,300,301,29999,30000,30001,1000000};
    for(unsigned i=0;i<sizeof(probes)/sizeof(probes[0]);i++){
        int64_t x = probes[i];
        if(dense_sw(x)     != dense_ref(x))     { printf("dense  x=%lld\n",(long long)x); return 1; }
        if(sparse_sw(x)    != sparse_ref(x))    { printf("sparse x=%lld\n",(long long)x); return 2; }
        if(dense_neg_sw(x) != dense_neg_ref(x)) { printf("dneg   x=%lld\n",(long long)x); return 3; }
    }
    printf("switch: dense (0-based & negative-min jump table) and sparse (linear/BST) match clang\n");
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
fn e2e_aarch64_switch_matches_clang() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt).expect("switch module must compile");
        let Some(code) = link_run("switch", &obj) else {
            return;
        };
        assert_eq!(code, 0, "switch result mismatch at {opt:?}");
    }
}
