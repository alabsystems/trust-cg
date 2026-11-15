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

#[path = "common/native_host.rs"]
mod native_host;

/// AArch64 Linux GNU (ELF) or macOS (Mach-O): `Compiler::new` derives the
/// host's object format and ABI, and the host `cc` links it.
fn can_link_and_run_aarch64_native() -> bool {
    native_host::NATIVE
}

/// The two functions with `unit_return` as their return list and a bare
/// `ret`: `[]` is trust-ir's spelling of a `-> ()` function (the rustc bridge
/// drops a zero-sized return the same way, `trust_ir_ty_is_zero_sized`), and
/// the backend lowers it as void; `[()]` with a bare `ret` is
/// `ReturnArityMismatch` (a declared `()` must be returned as a value), which
/// since WS7.3 every ingestion entry refuses.
fn build_module() -> TrustIrModule {
    build_module_returning(vec![])
}

fn build_module_returning(unit_return: Vec<Ty>) -> TrustIrModule {
    let mut m = TrustIrModule::new("unit_return");

    // `fn store_it(p: *mut i64, v: i64) -> () { *p = v; }`
    let store_ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::PtrMut(Box::new(Ty::I64)), Ty::I64],
            returns: unit_return.clone(), // unit return -> void
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
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
    m.try_add_function(store_it)
        .expect("Module::try_add_function: test fixture");

    // `fn ignore(v: i64) -> () {}`
    let ign_ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: unit_return,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut ignore = TrustIrFunction::new(FuncId::new(1), "ignore", ign_ft, BlockId::new(0));
    ignore.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![InstrNode::new(Inst::Return { values: vec![] })],
    }];
    m.try_add_function(ignore)
        .expect("Module::try_add_function: test fixture");
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
    if !can_link_and_run_aarch64_native() {
        eprintln!("SKIP: needs an AArch64 Linux GNU or macOS host");
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
        .args(native_host::c_math_library_args())
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

/// The fixture is claim-less, so the compile states `Permit` (the LD-W7-1
/// rule): the default license policy refuses the claim-less body first, by its
/// own name, and would hide the structural finding this row pins. Under either
/// policy trust-ir's `ReturnArityMismatch` is a refusal; the default-policy
/// verdict is pinned by name too. Decision record LD-80.
#[test]
fn a_declared_unit_return_with_a_bare_ret_is_refused_at_ingestion() {
    let module = build_module_returning(vec![Ty::Unit]);
    let licensed = Compiler::new(CompilerConfig::default())
        .compile(&module)
        .expect_err("the default license refuses a claim-less body");
    assert!(
        matches!(
            &licensed,
            trust_cg_codegen::compiler::CompileError::Adapter(
                trust_cg_lower::AdapterError::UnlicensedBody { function }
            ) if function == "store_it"
        ),
        "{licensed}"
    );
    let error = Compiler::new(CompilerConfig::default())
        .with_codegen_license(permit_unlicensed())
        .compile(&module)
        .expect_err("a `()` return list with a bare `ret` is not valid trust-ir");
    assert!(
        matches!(
            &error,
            trust_cg_codegen::compiler::CompileError::InvalidTrustIr(refusal)
                if refusal.any(|finding| matches!(
                    finding,
                    trust_ir_build::ValidationError::ReturnArityMismatch { .. }
                ))
        ),
        "{error}"
    );
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

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
