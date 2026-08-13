// trust-cg-codegen/tests/e2e_aarch64_indirect_call.rs
//
// Completeness: indirect calls (function pointers) via `Inst::CallIndirect`.
// This is a distinct code path from direct calls -- the callee is a runtime
// value (a `ptr`) rather than a symbol, so the backend must materialize the
// target address into a register and emit `BLR` instead of a `BL` to a fixup.
// It is also the path exercised by the non-C conventions enabled earlier, so
// pinning it guards both.
//
// The test is a native differential check on aarch64-apple-darwin: clang -- the
// oracle -- compiles a driver that passes real C function pointers (`dbl`,
// `neg`, `fma3`) into trust-cg-compiled trampolines `apply1`/`apply3`, which
// invoke them through `call_indirect`. If the address materialization, the
// BLR, or the argument marshalling were wrong, the result would diverge from
// the direct C call clang would have made.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    Block as TrustIrBlock, CallingConv, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

fn build_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("indirect_call");

    // Signature of the *target* being called through the pointer: (i64)->(i64).
    let callee1_sig = m.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    // apply1(fp: ptr, x: i64) -> i64 { return (*fp)(x) }
    let apply1_sig = m.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut apply1 = TrustIrFunction::new(FuncId::new(0), "apply1", apply1_sig, BlockId::new(0));
    apply1.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(0),
                sig: callee1_sig,
                args: vec![ValueId::new(1)],
                calling_conv: CallingConv::C,
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    m.add_function(apply1);

    // Signature of the 3-arg target: (i64,i64,i64)->(i64).
    let callee3_sig = m.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    // apply3(fp: ptr, a,b,c: i64) -> i64 { return (*fp)(a,b,c) }
    let apply3_sig = m.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::I64, Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut apply3 = TrustIrFunction::new(FuncId::new(1), "apply3", apply3_sig, BlockId::new(0));
    apply3.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::Ptr),
            (ValueId::new(1), Ty::I64),
            (ValueId::new(2), Ty::I64),
            (ValueId::new(3), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(0),
                sig: callee3_sig,
                args: vec![ValueId::new(1), ValueId::new(2), ValueId::new(3)],
                calling_conv: CallingConv::C,
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(4)],
            }),
        ],
    }];
    m.add_function(apply3);

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
extern int64_t apply1(int64_t (*)(int64_t), int64_t);
extern int64_t apply3(int64_t (*)(int64_t,int64_t,int64_t), int64_t,int64_t,int64_t);
static int64_t dbl(int64_t x){ return 2*x; }
static int64_t neg(int64_t x){ return -x; }
static int64_t fma3(int64_t a,int64_t b,int64_t c){ return a*b+c; }
int main(void){
    if(apply1(dbl,21)!=42){printf("apply1 dbl\n");return 1;}
    if(apply1(neg,7)!=-7){printf("apply1 neg\n");return 2;}
    if(apply1(dbl,-100)!=-200){printf("apply1 dbl neg\n");return 3;}
    if(apply3(fma3,3,5,7)!=22){printf("apply3\n");return 4;}
    if(apply3(fma3,-2,10,4)!=-16){printf("apply3 b\n");return 5;}
    if(apply3(fma3,0,999,42)!=42){printf("apply3 c\n");return 6;}
    printf("indirect calls (function pointers via call_indirect) bit-exact vs clang\n");
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
fn e2e_aarch64_indirect_call_matches_clang() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt).expect("indirect-call module must compile");
        let Some(code) = link_run("indirect_call", &obj) else {
            return;
        };
        assert_eq!(code, 0, "indirect-call result mismatch at {opt:?}");
    }
}
