// trust-cg-codegen/tests/e2e_aarch64_unit_return.rs
//
// End-to-end coverage for unit/void-returning functions (`fn ... -> ()`), which
// are ubiquitous in real Rust. A `()` (unit) or `!` (never) return type is a
// zero-sized value with no ABI return slot, so it is dropped from the machine
// signature (translate_signature / current_return_tys) and the function returns
// void — instead of fail-closing on `translate_type(Ty::Unit) == VoidValue`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    Block as TrustIrBlock, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

fn build_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("unit_return");

    // `fn store_it(p: *mut i64, v: i64) -> () { *p = v; }`
    let store_ft = m.add_func_type(FuncTy {
        params: vec![Ty::PtrMut(Box::new(Ty::I64)), Ty::I64],
        returns: vec![Ty::Unit], // unit return -> void
        is_vararg: false,
    });
    let mut store_it = TrustIrFunction::new(FuncId::new(0), "store_it", store_ft, BlockId::new(0));
    store_it.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::PtrMut(Box::new(Ty::I64))),
            (ValueId::new(1), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                value: ValueId::new(1),
                ptr: ValueId::new(0),
                align: None,
                volatile: false,
            }),
            // bare `ret` — no return value (void)
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    m.add_function(store_it);

    // `fn ignore(v: i64) -> () {}`
    let ign_ft = m.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::Unit],
        is_vararg: false,
    });
    let mut ignore = TrustIrFunction::new(FuncId::new(1), "ignore", ign_ft, BlockId::new(0));
    ignore.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![InstrNode::new(Inst::Return { values: vec![] })],
    }];
    m.add_function(ignore);
    m
}

fn compile_at(module: &TrustIrModule, opt: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    });
    let r = compiler
        .compile(module)
        .expect("unit/void-returning functions must compile");
    assert!(!r.object_code.is_empty());
    r.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
extern void store_it(int64_t* p, int64_t v);
extern void ignore(int64_t v);
int main(void) {
    int64_t x = 0;
    store_it(&x, 0x1234567890ABCDEFLL);
    ignore(99);
    if (x != 0x1234567890ABCDEFLL) return 1;
    printf("unit/void-returning functions run correctly\n");
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
fn e2e_aarch64_unit_returning_functions() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt);
        let Some(code) = link_run("unit_return", &obj) else {
            return;
        };
        assert_eq!(code, 0, "unit-return runtime failure at {opt:?}");
    }
}
