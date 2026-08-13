// trust-cg-codegen/tests/e2e_aarch64_call_arg_ptr_theft.rs
//
// ADVERSARIAL REGRESSION PIN for the AArch64 call-argument-setup repair
// (`fixup_aarch64_call_arg_source_clobbers` and its siblings
// `aarch64_call_arg_implicit_preserves` / `classify_aarch64_call_arg_setup` in
// crates/trust-cg-codegen/src/pipeline.rs).
//
// THE SHAPE (reconstructed from the lldb trace on the def_eq/TY binaries):
// a call whose argument register is ALSO the destination of an in-region
// GEP/madd pointer that is *separately consumed* (dereferenced) before the
// call. After register allocation the allocator legitimately parks the pointer
// in the ABI argument register (x0), loads through it, and hands the same x0 to
// the callee. A historical `implicit_preserves` heuristic could "restore" x0's
// pre-region value right before the `blr`, overwriting the live pointer, so the
// callee dereferenced a scalar -> SIGSEGV / silent miscompile.
//
// This is a native differential: a C driver hands trust-cg-compiled `thief` a
// real array pointer. `thief` computes `p = &arr[i]`, reads `*p` (the separate
// consume), then calls `sink(p, *p + tag)` which STORES through `p` and returns
// the stored value. If x0 (the pointer) were clobbered with a stale scalar the
// store faults or lands at the wrong address, which both the return value and
// the post-call array contents detect. A genuine arg swap is pinned alongside
// so the fix for the theft vector may never silently break real serialization.
//
// The pass must be CORRECT or FAIL-CLOSED (a typed compile error), and may
// NEVER emit a wrong pointer. A crash / wrong result / wrong array is a P0.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    BinOp, Block as TrustIrBlock, CallingConv, FuncTy, Function as TrustIrFunction, Inst,
    InstrNode, Module as TrustIrModule, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

/// Two-function module exercising the "pointer both dereferenced and passed"
/// theft shape.
///
/// ```text
/// fn sink(p: ptr, tag: i64) -> i64 { *p = tag; return *p }
/// fn thief(base: ptr, i: i64, tag: i64) -> i64 {
///     p   = &base[i]      // GEP -> madd base + i*8; the call's x0 argument
///     old = *p            // SEPARATE consume of the same pointer
///     s   = old + tag
///     return sink(p, s)   // p passed as arg0, threaded through x0
/// }
/// ```
fn build_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("call_arg_ptr_theft");

    // fn sink(p: ptr, tag: i64) -> i64 { *p = tag; return *p }
    let sink_sig = m.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut sink = TrustIrFunction::new(FuncId::new(0), "sink", sink_sig, BlockId::new(0));
    sink.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: ValueId::new(0),
                value: ValueId::new(1),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(0),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    m.add_function(sink);

    // fn thief(base: ptr, i: i64, tag: i64) -> i64 { ... }
    let thief_sig = m.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut thief = TrustIrFunction::new(FuncId::new(1), "thief", thief_sig, BlockId::new(0));
    thief.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::Ptr), // base
            (ValueId::new(1), Ty::I64), // i
            (ValueId::new(2), Ty::I64), // tag
        ],
        body: vec![
            // p = &base[i]
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: ValueId::new(0),
                indices: vec![ValueId::new(1)],
                inbounds: true,
            })
            .with_result(ValueId::new(3)),
            // old = *p  (separate consume of the same pointer)
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(3),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(4)),
            // s = old + tag
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(4),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(5)),
            // r = sink(p, s)  — p is arg0 (x0) AND was just dereferenced above
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![ValueId::new(3), ValueId::new(5)],
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(6)],
            }),
        ],
    }];
    m.add_function(thief);

    m
}

/// Genuine argument-register swap through a NON-inlinable indirect call, so the
/// backend is forced to emit a real `x0 <- x1; x1 <- x0` parallel move (the
/// mutating source-clobber repair path). The callee target is a runtime
/// function pointer parked in x2, which keeps the swap from being folded away.
///
/// ```text
/// fn swap_caller(a: i64, b: i64, fp: ptr) -> i64 { return (*fp)(b, a) }
/// ```
/// With `fp` last, `a` lands in x0 and `b` in x1; calling `(*fp)(b, a)` needs
/// `b` in x0 and `a` in x1 — the exact `x0 <-> x1` swap. A botched serialization
/// (no scratch) collapses both to one value.
fn build_swap_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("call_arg_swap");

    // Signature of the target reached through the pointer: (i64,i64)->(i64).
    let callee_sig = m.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    let caller_sig = m.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64, Ty::Ptr],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut caller =
        TrustIrFunction::new(FuncId::new(0), "swap_caller", caller_sig, BlockId::new(0));
    caller.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::I64), // a -> x0
            (ValueId::new(1), Ty::I64), // b -> x1
            (ValueId::new(2), Ty::Ptr), // fp -> x2
        ],
        body: vec![
            // (*fp)(b, a) — forces b into x0 and a into x1: a real x0<->x1 swap.
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(2),
                sig: callee_sig,
                args: vec![ValueId::new(1), ValueId::new(0)],
                calling_conv: CallingConv::C,
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

const THEFT_DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
extern int64_t thief(int64_t *base, int64_t i, int64_t tag);
int main(void){
    int64_t arr[4] = {100, 200, 300, 400};
    // p = &arr[2]; old = 300; s = 305; sink(p,305): arr[2]=305, return 305.
    int64_t r = thief(arr, 2, 5);
    if (r != 305)        { printf("thief return %lld != 305\n", (long long)r); return 1; }
    if (arr[2] != 305)   { printf("arr[2] %lld != 305 (wrong store address)\n", (long long)arr[2]); return 2; }
    if (arr[0] != 100)   { printf("arr[0] clobbered: %lld\n", (long long)arr[0]); return 3; }
    if (arr[1] != 200)   { printf("arr[1] clobbered: %lld\n", (long long)arr[1]); return 4; }
    if (arr[3] != 400)   { printf("arr[3] clobbered: %lld\n", (long long)arr[3]); return 5; }
    // A second index to be sure the address is index-dependent, not fixed.
    int64_t r2 = thief(arr, 0, 1);   // old=100, s=101, arr[0]=101, ret 101
    if (r2 != 101)       { printf("thief#2 return %lld != 101\n", (long long)r2); return 6; }
    if (arr[0] != 101)   { printf("arr[0] %lld != 101\n", (long long)arr[0]); return 7; }
    printf("call-arg pointer-theft shape correct (pointer survived to the callee)\n");
    return 0;
}
"#;

const SWAP_DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
static int64_t sub_c(int64_t x, int64_t y){ return x - y; }
extern int64_t swap_caller(int64_t a, int64_t b, int64_t (*fp)(int64_t,int64_t));
int main(void){
    // swap_caller(10,3,sub_c) == sub_c(3,10) == -7. A botched swap yields 0 or 7.
    int64_t r = swap_caller(10, 3, sub_c);
    if (r != -7) { printf("swap_caller(10,3) = %lld != -7\n", (long long)r); return 1; }
    if (swap_caller(3, 10, sub_c) != 7) { printf("swap_caller(3,10) != 7\n"); return 2; }
    if (swap_caller(-5, 5, sub_c) != 10) { printf("swap_caller(-5,5) != 10\n"); return 3; }
    printf("genuine arg-register swap serializes correctly\n");
    return 0;
}
"#;

fn link_run(tag: &str, obj: &[u8], driver: &str) -> Option<i32> {
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
    fs::write(&drv_path, driver).unwrap();
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
fn call_arg_pointer_theft_pointer_survives_to_callee() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        // The repair pass must be CORRECT or FAIL-CLOSED, never a miscompile.
        match compile_at(&module, opt) {
            Ok(obj) => {
                let Some(code) = link_run("call_arg_ptr_theft", &obj, THEFT_DRIVER) else {
                    return;
                };
                assert_eq!(
                    code, 0,
                    "MISCOMPILE at {opt:?}: the call-arg pointer was clobbered before the call \
                     (stale scalar over a live pointer). Exit code {code} names the failed check.",
                );
            }
            Err(e) => {
                // Fail-closed is acceptable soundness-wise, but this program is
                // legitimate, so a rejection is a completeness regression to be
                // surfaced loudly rather than silently miscompiled.
                assert!(
                    e.contains("Aarch64CallArgRepair")
                        || e.contains("call argument")
                        || e.contains("ambiguous"),
                    "compile failed at {opt:?} with an UNEXPECTED error (not the fail-closed \
                     call-arg guard): {e}",
                );
                eprintln!(
                    "NOTE: pointer-theft shape FAIL-CLOSED at {opt:?} (sound, not a miscompile): {e}"
                );
            }
        }
    }
}

#[test]
fn genuine_arg_register_swap_serializes() {
    let module = build_swap_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt).expect("swap module must compile");
        let Some(code) = link_run("call_arg_swap", &obj, SWAP_DRIVER) else {
            return;
        };
        assert_eq!(
            code, 0,
            "genuine arg-register swap mis-serialized at {opt:?} (exit {code})",
        );
    }
}
