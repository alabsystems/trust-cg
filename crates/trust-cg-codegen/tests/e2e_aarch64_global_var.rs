// trust-cg-codegen/tests/e2e_aarch64_global_var.rs
//
// Completeness: module global variables. `Inst::GlobalAddr` lowers (via
// `Opcode::GlobalRef`) to the AArch64 direct addressing pair
//   ADRP Xd, sym@PAGE ; ADD Xd, Xd, sym@PAGEOFF
// and the object emitter must place the global's initializer in the right
// section (mutable -> __data, immutable -> __const) and emit the matching
// ARM64_RELOC_PAGE21 / PAGEOFF12 relocations.
//
// This is checked differentially by making clang -- which addresses the very
// same exported symbols with its own ADRP/ADD -- and trust-cg share the same
// memory: the driver reads/writes `g_counter` directly, and trust-cg reads,
// writes, and read-modify-writes it through GlobalAddr+Load/Store. If the
// relocation, the section placement, or the initializer were wrong, the two
// views of the symbol would disagree.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::value::GlobalId;
use trust_ir::{
    BinOp, Block as TrustIrBlock, Constant, FuncTy, Function as TrustIrFunction, Global, Inst,
    InstrNode, Linkage, Module as TrustIrModule, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

fn i64_load(ptr: ValueId, out: ValueId) -> InstrNode {
    InstrNode::new(Inst::Load {
        ty: Ty::I64,
        ptr,
        volatile: false,
        align: Some(8),
    })
    .with_result(out)
}

fn build_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("global_var");

    // int64_t g_counter = 100;            (mutable, exported -> __data)
    m.globals.push(Global {
        name: "g_counter".to_string(),
        ty: Ty::I64,
        mutable: true,
        initializer: Some(Constant::Int(100)),
        linkage: Linkage::External,
        tls: None,
        align: None,
    });
    // const int64_t g_ro = 42;            (immutable, exported -> __const)
    m.globals.push(Global {
        name: "g_ro".to_string(),
        ty: Ty::I64,
        mutable: false,
        initializer: Some(Constant::Int(42)),
        linkage: Linkage::External,
        tls: None,
        align: None,
    });
    // const double g_pi = 3.14159;        (immutable f64 -> __const, 8 IEEE bytes)
    m.globals.push(Global {
        name: "g_pi".to_string(),
        ty: Ty::F64,
        mutable: false,
        initializer: Some(Constant::Float(f64::from_bits(0x4009_21f9_f01b_866e))),
        linkage: Linkage::External,
        tls: None,
        align: None,
    });
    let g_counter = GlobalId::new(0);
    let g_ro = GlobalId::new(1);
    let g_pi = GlobalId::new(2);

    let ret_i64 = |m: &mut TrustIrModule| {
        m.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        })
    };

    // int64_t get_counter(void) { return g_counter; }
    let ft0 = ret_i64(&mut m);
    let mut get_counter = TrustIrFunction::new(FuncId::new(0), "get_counter", ft0, BlockId::new(0));
    get_counter.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::GlobalAddr { global: g_counter }).with_result(ValueId::new(0)),
            i64_load(ValueId::new(0), ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    m.add_function(get_counter);

    // int64_t get_ro(void) { return g_ro; }
    let ft1 = ret_i64(&mut m);
    let mut get_ro = TrustIrFunction::new(FuncId::new(1), "get_ro", ft1, BlockId::new(0));
    get_ro.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::GlobalAddr { global: g_ro }).with_result(ValueId::new(0)),
            i64_load(ValueId::new(0), ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    m.add_function(get_ro);

    // int64_t add_counter(int64_t x) { g_counter += x; return g_counter; }
    let ft2 = m.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut add_counter = TrustIrFunction::new(FuncId::new(2), "add_counter", ft2, BlockId::new(0));
    add_counter.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)], // x
        body: vec![
            InstrNode::new(Inst::GlobalAddr { global: g_counter }).with_result(ValueId::new(1)),
            i64_load(ValueId::new(1), ValueId::new(2)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(2),
                rhs: ValueId::new(0),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: ValueId::new(1),
                value: ValueId::new(3),
                volatile: false,
                align: Some(8),
            }),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    m.add_function(add_counter);

    // double get_pi(void) { return g_pi; }
    let ft3 = m.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::F64],
        is_vararg: false,
    });
    let mut get_pi = TrustIrFunction::new(FuncId::new(3), "get_pi", ft3, BlockId::new(0));
    get_pi.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::GlobalAddr { global: g_pi }).with_result(ValueId::new(0)),
            InstrNode::new(Inst::Load {
                ty: Ty::F64,
                ptr: ValueId::new(0),
                volatile: false,
                align: Some(8),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    m.add_function(get_pi);

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
#include <math.h>
extern int64_t g_counter;         // trust-cg-defined, mutable
extern const int64_t g_ro;        // trust-cg-defined, read-only
extern const double g_pi;         // trust-cg-defined f64, read-only
extern int64_t get_counter(void);
extern int64_t get_ro(void);
extern int64_t add_counter(int64_t);
extern double  get_pi(void);
int main(void){
    // trust-cg and clang must see the same initial values.
    if (get_counter() != 100) { printf("init counter\n"); return 1; }
    if (g_counter    != 100)  { printf("C view init\n");  return 2; }
    if (get_ro()     != 42)   { printf("ro\n");           return 3; }
    if (g_ro         != 42)   { printf("C view ro\n");    return 4; }
    // trust-cg writes; clang reads the same symbol.
    if (add_counter(5)  != 105) { printf("rmw a\n"); return 5; }
    if (g_counter       != 105) { printf("C sees rmw\n"); return 6; }
    // clang writes; trust-cg reads the same symbol.
    g_counter = 1000;
    if (get_counter() != 1000) { printf("read after C write\n"); return 7; }
    if (add_counter(-1) != 999) { printf("rmw b\n"); return 8; }
    if (g_counter       != 999) { printf("C sees rmw b\n"); return 9; }
    // f64 global: trust-cg's IEEE bytes must match the C view bit-for-bit.
    if (get_pi() != g_pi)          { printf("pi mismatch\n"); return 10; }
    if (fabs(g_pi - 3.14159) > 0)  { printf("pi bytes\n");    return 11; }
    printf("module globals: ADRP+ADD load/store/rmw + f64 init agree with clang on the same symbols\n");
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
fn e2e_aarch64_global_var_matches_clang() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt).expect("global-var module must compile");
        let Some(code) = link_run("global_var", &obj) else {
            return;
        };
        assert_eq!(code, 0, "global-var result mismatch at {opt:?}");
    }
}
