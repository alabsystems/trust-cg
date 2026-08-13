// trust-cg-codegen/tests/e2e_aarch64_vector_binop.rs
//
// End-to-end (compile -> link -> RUN) coverage for packed <2 x i64> bitwise
// AND/OR/XOR (audit A4) — these fail-closed while V4I32/V16I8 bitwise lowered.
// They reuse the covered NEON AND/ORR/EOR (lane-width-agnostic over the 128-bit
// register), so the fix is three adapter arms; verified bit-exact on hardware.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    BinOp, Block as TrustIrBlock, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, Ty,
};
use trust_ir::{BlockId, FuncId, ValueId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

/// `fn name(a: *const V, b: *const V, out: *mut V) { *out = op(*a, *b); }`
fn build_vec_binop(func_id: u32, name: &str, module: &mut TrustIrModule, vec_ty: Ty, op: BinOp) {
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::Ptr, Ty::Ptr],
        returns: vec![],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::Ptr),
            (ValueId::new(1), Ty::Ptr),
            (ValueId::new(2), Ty::Ptr),
        ],
        body: vec![
            InstrNode::new(Inst::Load {
                ty: vec_ty.clone(),
                ptr: ValueId::new(0),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Load {
                ty: vec_ty.clone(),
                ptr: ValueId::new(1),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::BinOp {
                op,
                ty: vec_ty.clone(),
                lhs: ValueId::new(3),
                rhs: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Store {
                ty: vec_ty,
                ptr: ValueId::new(2),
                value: ValueId::new(5),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    module.add_function(f);
}

fn build_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("vec_binop");
    let v2i64 = Ty::Vector(Box::new(Ty::I64), 2);
    build_vec_binop(0, "_v2i64_and", &mut module, v2i64.clone(), BinOp::And);
    build_vec_binop(1, "_v2i64_or", &mut module, v2i64.clone(), BinOp::Or);
    build_vec_binop(2, "_v2i64_xor", &mut module, v2i64, BinOp::Xor);
    module
}

fn compile_to_obj_at(module: &TrustIrModule, opt_level: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(module)
        .expect("v2i64 bitwise must compile");
    assert!(!result.object_code.is_empty());
    result.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>

extern void _v2i64_and(const uint64_t *a, const uint64_t *b, uint64_t *out);
extern void _v2i64_or (const uint64_t *a, const uint64_t *b, uint64_t *out);
extern void _v2i64_xor(const uint64_t *a, const uint64_t *b, uint64_t *out);

int main(void) {
    uint64_t a[2] = { 0xF0F0F0F0F0F0F0F0ULL, 0x0123456789ABCDEFULL };
    uint64_t b[2] = { 0xFF00FF00FF00FF00ULL, 0xFFFFFFFF00000000ULL };
    uint64_t o[2];

    _v2i64_and(a, b, o);
    if (o[0] != (a[0] & b[0]) || o[1] != (a[1] & b[1])) return 1;
    _v2i64_or(a, b, o);
    if (o[0] != (a[0] | b[0]) || o[1] != (a[1] | b[1])) return 2;
    _v2i64_xor(a, b, o);
    if (o[0] != (a[0] ^ b[0]) || o[1] != (a[1] ^ b[1])) return 3;

    printf("<2 x i64> bitwise and/or/xor correct\n");
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
fn e2e_aarch64_v2i64_bitwise() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_to_obj_at(&module, opt);
        let Some(code) = link_run_exit_code("vec_binop", &obj, DRIVER) else {
            return;
        };
        assert_eq!(
            code, 0,
            "<2 x i64> bitwise runtime mismatch at {opt:?} (failing-case code {code})",
        );
    }
}
