// trust-cg-codegen/tests/e2e_aarch64_atomics.rs
//
// Pinned refutation for TWO confirmed P0 miscompiles of LSE atomics that only
// appeared at -O2 (the -O0 pipeline was correct):
//
//   1. `atomicrmw` (LDADD/LDSET/SWP/...): the update value is operand 0 (a
//      pure USE) while the old-value DEF is operand 1 — the opposite of the
//      usual "operand 0 is the def" layout. AArch64 DCE assumed operand 0 was
//      the def, so it treated the update-value vreg as never-used and deleted
//      the copy materializing it. The atomic then read a stale/undefined
//      register: `atomicrmw add p, v` computed `*p + garbage` instead of
//      `*p + v`.
//
//   2. `cmpxchg` (CAS): the expected value is placed in the CAS Rs register,
//      which is a DEF-USE (expected in, loaded value out). The post-RA copy
//      coalescer scanned the def before the use within that one instruction and
//      concluded the `mov Rs, expected` copy was dead, deleting it — so the CAS
//      compared against an undefined register.
//
// Both are fixed and this test pins them bit-exact against C11 `<stdatomic.h>`
// on real Apple Silicon at O0 and O2. Single-threaded suffices to catch the
// value bug (the read-modify-write arithmetic and the compare-exchange logic).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_ir::{
    AtomicRMWOp, Block as TrustIrBlock, CastOp, FuncTy, Function as TrustIrFunction, Inst,
    InstrNode, Module as TrustIrModule, Ordering, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

// `fn name(p: *mut i64, v: i64) -> i64 { atomicrmw <op> seq_cst *p, v }`
// returns the OLD value.
fn build_rmw(id: u32, name: &str, m: &mut TrustIrModule, op: AtomicRMWOp) {
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::PtrMut(Box::new(Ty::I64)), Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::PtrMut(Box::new(Ty::I64))),
            (ValueId::new(1), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::AtomicRMW {
                op,
                ty: Ty::I64,
                ptr: ValueId::new(0),
                value: ValueId::new(1),
                ordering: Ordering::SeqCst,
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    m.add_function(f);
}

fn build_module() -> TrustIrModule {
    use AtomicRMWOp::*;
    let mut m = TrustIrModule::new("atomics");
    let ops = [
        (Add, "rmw_add"),
        (Sub, "rmw_sub"),
        (And, "rmw_and"),
        (Or, "rmw_or"),
        (Xor, "rmw_xor"),
        (Xchg, "rmw_xchg"),
        (Max, "rmw_max"),
        (Min, "rmw_min"),
        (UMax, "rmw_umax"),
        (UMin, "rmw_umin"),
    ];
    for (i, (op, name)) in ops.iter().enumerate() {
        build_rmw(i as u32, name, &mut m, *op);
    }

    // `fn cas_old(p, expected, desired) -> i64` returns the loaded value.
    let cas_ft = m.add_func_type(FuncTy {
        params: vec![Ty::PtrMut(Box::new(Ty::I64)), Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut cas_old = TrustIrFunction::new(FuncId::new(100), "cas_old", cas_ft, BlockId::new(0));
    cas_old.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::PtrMut(Box::new(Ty::I64))),
            (ValueId::new(1), Ty::I64),
            (ValueId::new(2), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::CmpXchg {
                ty: Ty::I64,
                ptr: ValueId::new(0),
                expected: ValueId::new(1),
                desired: ValueId::new(2),
                success: Ordering::SeqCst,
                failure: Ordering::SeqCst,
            })
            .with_results(vec![ValueId::new(3), ValueId::new(4)]),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    m.add_function(cas_old);

    // `fn cas_ok(p, expected, desired) -> i64` returns the success flag (0/1).
    let cas_ok_ft = m.add_func_type(FuncTy {
        params: vec![Ty::PtrMut(Box::new(Ty::I64)), Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut cas_ok = TrustIrFunction::new(FuncId::new(101), "cas_ok", cas_ok_ft, BlockId::new(0));
    cas_ok.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::PtrMut(Box::new(Ty::I64))),
            (ValueId::new(1), Ty::I64),
            (ValueId::new(2), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::CmpXchg {
                ty: Ty::I64,
                ptr: ValueId::new(0),
                expected: ValueId::new(1),
                desired: ValueId::new(2),
                success: Ordering::SeqCst,
                failure: Ordering::SeqCst,
            })
            .with_results(vec![ValueId::new(3), ValueId::new(4)]),
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::I64,
                operand: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(5)],
            }),
        ],
    }];
    m.add_function(cas_ok);
    m
}

fn compile_at(module: &TrustIrModule, opt: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    });
    let r = compiler
        .compile(module)
        .expect("atomics module must compile");
    assert!(!r.object_code.is_empty());
    r.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
#define D(op) extern int64_t rmw_##op(int64_t*,int64_t);
D(add)D(sub)D(and)D(or)D(xor)D(xchg)D(max)D(min)D(umax)D(umin)
extern int64_t cas_old(int64_t*,int64_t,int64_t);
extern int64_t cas_ok(int64_t*,int64_t,int64_t);
int main(void){
    int64_t A[]={0,5,-5,0x0f0f0f0f0f0f0f0fLL,-1,100,0x7fffffffffffffffLL};
    int64_t B[]={0,3,-3,(int64_t)0xf0f0f0f0f0f0f0f0ULL,1,-100,3};
    for(unsigned i=0;i<sizeof(A)/sizeof(A[0]);i++)for(unsigned j=0;j<sizeof(B)/sizeof(B[0]);j++){
        int64_t a=A[i],b=B[j],m,old;
        #define CHK(op, expr) m=a; old=rmw_##op(&m,b); if(old!=a){printf(#op" old\n");return 1;} { int64_t want=(expr); if(m!=want){printf(#op" mem got=%lld want=%lld\n",(long long)m,(long long)want);return 2;} }
        CHK(add, a+b) CHK(sub, a-b) CHK(and, a&b) CHK(or, a|b) CHK(xor, a^b) CHK(xchg, b)
        CHK(max, a>b?a:b) CHK(min, a<b?a:b)
        CHK(umax, (uint64_t)a>(uint64_t)b?a:b) CHK(umin, (uint64_t)a<(uint64_t)b?a:b)
        /* cmpxchg match: expected == current -> swaps, returns old */
        m=a; int64_t o=cas_old(&m,a,b); if(o!=a||m!=b){printf("cas match o=%lld m=%lld\n",(long long)o,(long long)m);return 3;}
        /* cmpxchg mismatch: expected != current -> no change, flag 0 */
        m=a; int64_t f=cas_ok(&m,a+1,b); if(f!=0||m!=a){printf("cas mismatch f=%lld m=%lld\n",(long long)f,(long long)m);return 4;}
        /* cmpxchg success: expected == current -> swaps, flag 1 */
        m=a; int64_t s=cas_ok(&m,a,b); if(s!=1||m!=b){printf("cas succ s=%lld m=%lld\n",(long long)s,(long long)m);return 5;}
    }
    printf("atomicrmw (10 ops) + cmpxchg value-correct vs C11 atomics\n");
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
            "-O2",
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
fn e2e_aarch64_atomicrmw_and_cmpxchg() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt);
        let Some(code) = link_run("atomics", &obj) else {
            return;
        };
        assert_eq!(
            code, 0,
            "atomic op mismatch at {opt:?} (failing code {code})"
        );
    }
}
