// trust-cg-codegen/tests/e2e_aarch64_call_arg_signext.rs
//
// End-to-end refutation + regression gate for the CALL/ARGUMENT side of the
// Apple arm64 narrow-integer ABI (the mirror of the return-side P0 fixed in
// b711878). The Apple ABI requires the CALLER to sign/zero-extend a sub-word
// argument to 32 bits before a call; trust-cg's select_call moved narrow args
// with a plain register copy and no extension, so passing a COMPUTED narrow
// value (with non-canonical upper bits) to an LLVM-compiled callee miscompiled.
//
// This test builds `caller(a,b) = observe((i8)(a+b))` where `observe` is an
// EXTERNAL (clang-compiled) `int observe(signed char)` that returns its arg —
// clang, per the Apple ABI, reads the caller-extended value. With inputs where
// `(i8)(a+b)` is negative (e.g. 100+100 -> -56), a missing caller-side extension
// is observable as a wrong result. Runs on aarch64-apple-darwin.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    BinOp, Block as TrustIrBlock, FuncTy, Function as TrustIrFunction, Inst, InstrNode, Linkage,
    Module as TrustIrModule, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

fn build_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("call_arg_signext");

    // External declaration: `int observe(signed char)` — no body, provided by clang.
    let observe_ft = m.add_func_type(FuncTy {
        params: vec![Ty::I8],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut observe = TrustIrFunction::new(FuncId::new(0), "observe", observe_ft, BlockId::new(0));
    observe.blocks = vec![]; // declaration / import
    observe.linkage = Linkage::External;
    m.add_function(observe);

    // `caller(a: i8, b: i8) -> i32 { observe((i8)(a + b)) }`
    let caller_ft = m.add_func_type(FuncTy {
        params: vec![Ty::I8, Ty::I8],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut caller = TrustIrFunction::new(FuncId::new(1), "caller", caller_ft, BlockId::new(0));
    caller.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I8), (ValueId::new(1), Ty::I8)],
        body: vec![
            // %2 = a + b (i8, wraps; upper bits of the 32-bit reg are non-canonical)
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I8,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            // %3 = observe(%2)
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![ValueId::new(2)],
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    m.add_function(caller);
    m
}

fn compile_to_obj_at(module: &TrustIrModule, opt_level: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level,
        ..CompilerConfig::default()
    });
    let result = compiler.compile(module).expect("caller must compile");
    assert!(!result.object_code.is_empty());
    result.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>

/* clang-compiled callee: per the Apple arm64 ABI it may assume the caller
   sign-extended the signed-char argument, so it uses the incoming 32-bit reg
   directly. Returning it exposes any missing caller-side extension. */
int observe(signed char x) { return (int)x; }

extern int caller(signed char a, signed char b);

int main(void) {
    struct { signed char a, b; } cases[] = {
        {100, 100},   /* a+b = 200 -> (i8) -56 */
        {-100, -100}, /* -> (i8) 56 */
        {-1, -1},     /* -> -2 */
        {127, 1},     /* -> -128 */
        {50, 7},      /* -> 57 (canonical, must still match) */
        {-128, -1},   /* -> 127 */
    };
    for (unsigned i = 0; i < sizeof(cases)/sizeof(cases[0]); i++) {
        int got = caller(cases[i].a, cases[i].b);
        int ref = (int)(signed char)(cases[i].a + cases[i].b);
        if (got != ref) {
            printf("MISMATCH caller(%d,%d) = %d, expected %d\n",
                   cases[i].a, cases[i].b, got, ref);
            return 1;
        }
    }
    printf("caller-side narrow-arg extension bit-exact vs clang callee\n");
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

    // -O2 is essential: at -O0 clang RE-narrows a `signed char` parameter
    // (`sxtb w0,w0`), masking a missing caller-side extension. At -O2 clang
    // trusts the Apple ABI and uses the incoming register directly, so an
    // unextended argument is observable.
    let link = Command::new("cc")
        .args([
            "-O2",
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
fn e2e_aarch64_caller_extends_narrow_args() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_to_obj_at(&module, opt);
        let Some(code) = link_run_exit_code("call_arg_signext", &obj, DRIVER) else {
            return;
        };
        assert_eq!(
            code, 0,
            "caller-side narrow-arg extension mismatch at {opt:?} \
             (a computed i8 arg was passed to an extern callee unextended)",
        );
    }
}
