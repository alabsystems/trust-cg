// trust-cg-codegen/tests/e2e_aarch64_callee_saved_fpr.rs
//
// Pinned refutation for a confirmed P0 frame-lowering miscompile: a trust-cg
// function that holds an FP value in a callee-saved register (D8–D15) across a
// call did NOT save/restore that register, silently clobbering the caller's
// callee-saved FP state.
//
// The AArch64 AAPCS64 (and Apple arm64) ABI makes V8–V15 (the D8–D15 low-64
// aliases) callee-saved. The frame lowering DID detect the D8 use and build a
// callee-saved pair with `is_fpr = true` — but the pre-index (CSA-allocating)
// STP and post-index (CSA-deallocating) LDP encoders HARDCODED the integer
// pair form (`PairSize::X64, v=false`). So `stp d9, d8, [sp,#-N]!` was emitted
// as `stp x9, x8, [sp,#-N]!`: it saved two caller scratch GPRs and never
// touched D8, so the callee's own `fmov d8, d0` destroyed the caller's D8.
//
// Definitive failure signature before the fix (value pinned in D8 = 6.0):
//   held=6 ... *** MISCOMPILE: callee clobbered callee-saved d8 ***
//
// Fix: the pre/post-index LDP/STP encoders now derive (PairSize, V) from the
// operand register class (Gpr64 -> X64/v0, Fpr64 -> D64/v1) via
// `pair_index_size_v`, which fails CLOSED on any other class so an FPR pair can
// never again be silently encoded as a GPR pair. This test pins sentinels in
// ALL of D8–D15 across the call and verifies bit-exact preservation.
//
// The `live_fp` function computes `a + (a % b)`: the `%` lowers to an `fmod`
// libcall, and `a` is live across that call, forcing it into a callee-saved
// D-register (D8) — the reachable trigger.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    BinOp, Block as TrustIrBlock, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

fn build_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("callee_saved_fpr");

    // `fn live_fp(a: f64, b: f64) -> f64 { let r = a % b; a + r }`
    // `a` is live across the `fmod` libcall the `%` lowers to, so the allocator
    // must keep it in a callee-saved D-register across that call.
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::F64, Ty::F64],
        returns: vec![Ty::F64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(0), "live_fp", ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::F64), (ValueId::new(1), Ty::F64)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::FRem,
                ty: Ty::F64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::F64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    m.add_function(f);
    m
}

// A function that forces MANY int and float values live across an internal call,
// so the register allocator must park them in callee-saved X19–X28 and D8–D15
// simultaneously. This exercises the mixed GPR+FPR multi-pair frame: the pair
// offset arithmetic in the prologue/epilogue and the FP-vs-GPR encoding of every
// saved pair. `fn stress(i0..i7, f0..f7) -> i64` computes
//   (i0+..+i7) + trunc(f0)+..+trunc(f7) + trunc(f0 % f1)
// where the leading `f0 % f1` lowers to an `fmod` libcall (the call all the
// other values must survive).
fn build_stress_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("stress_callee_saved");
    const NI: u32 = 8;
    const NF: u32 = 8;

    let mut params: Vec<Ty> = (0..NI).map(|_| Ty::I64).collect();
    params.extend((0..NF).map(|_| Ty::F64));
    let ft = m.add_func_type(FuncTy {
        params: params.clone(),
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(0), "stress", ft, BlockId::new(0));

    let bb_params: Vec<(ValueId, Ty)> = params
        .iter()
        .enumerate()
        .map(|(i, t)| (ValueId::new(i as u32), t.clone()))
        .collect();

    let mut body = Vec::new();
    let mut next = 100u32;
    let mut fresh = || {
        let v = ValueId::new(next);
        next += 1;
        v
    };

    // fr = f0 % f1  (the internal call).
    let fr = fresh();
    body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::FRem,
            ty: Ty::F64,
            lhs: ValueId::new(NI),     // f0
            rhs: ValueId::new(NI + 1), // f1
        })
        .with_result(fr),
    );
    // fri = trunc(fr) as i64
    let fri = fresh();
    body.push(
        InstrNode::new(Inst::Cast {
            op: trust_ir::CastOp::FPToSI,
            src_ty: Ty::F64,
            dst_ty: Ty::I64,
            operand: fr,
        })
        .with_result(fri),
    );
    // trunc(f0)..trunc(f7) as i64 (uses the float params AFTER the call).
    let mut fints = Vec::new();
    for k in 0..NF {
        let x = fresh();
        body.push(
            InstrNode::new(Inst::Cast {
                op: trust_ir::CastOp::FPToSI,
                src_ty: Ty::F64,
                dst_ty: Ty::I64,
                operand: ValueId::new(NI + k),
            })
            .with_result(x),
        );
        fints.push(x);
    }
    // acc = i0 + i1 + .. + i7 + trunc(f0).. + fri
    let mut terms: Vec<ValueId> = (0..NI).map(ValueId::new).collect();
    terms.extend(fints);
    terms.push(fri);
    let mut cur = terms[0];
    for &t in &terms[1..] {
        let x = fresh();
        body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: cur,
                rhs: t,
            })
            .with_result(x),
        );
        cur = x;
    }
    body.push(InstrNode::new(Inst::Return { values: vec![cur] }));

    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: bb_params,
        body,
    }];
    m.add_function(f);
    m
}

fn compile_at(module: &TrustIrModule, opt: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    });
    let r = compiler
        .compile(module)
        .expect("callee-saved-FPR function must compile");
    assert!(!r.object_code.is_empty());
    r.object_code
}

// Pin distinct sentinels into every callee-saved FP register (D8–D15) before
// the call, and verify each survives it bit-exactly. Any register the callee
// clobbers without saving is caught. `+w` keeps the value in its bound V-reg
// and the empty-asm barrier defeats constant propagation across the call.
const DRIVER: &str = r#"
#include <stdio.h>
extern double live_fp(double, double);
int main(void) {
    register double r8  asm("d8")  = 8.5;
    register double r9  asm("d9")  = 9.5;
    register double r10 asm("d10") = 10.5;
    register double r11 asm("d11") = 11.5;
    register double r12 asm("d12") = 12.5;
    register double r13 asm("d13") = 13.5;
    register double r14 asm("d14") = 14.5;
    register double r15 asm("d15") = 15.5;
    asm volatile("" : "+w"(r8),"+w"(r9),"+w"(r10),"+w"(r11),
                      "+w"(r12),"+w"(r13),"+w"(r14),"+w"(r15));
    double result = live_fp(10.0, 3.0);   /* 10 % 3 = 1;  10 + 1 = 11 */
    asm volatile("" : "+w"(r8),"+w"(r9),"+w"(r10),"+w"(r11),
                      "+w"(r12),"+w"(r13),"+w"(r14),"+w"(r15));
    if (r8!=8.5||r9!=9.5||r10!=10.5||r11!=11.5||
        r12!=12.5||r13!=13.5||r14!=14.5||r15!=15.5) {
        printf("*** MISCOMPILE: callee clobbered a callee-saved D8-D15 reg ***\n");
        return 1;
    }
    if (result != 11.0) { printf("*** wrong result %g (want 11) ***\n", result); return 2; }
    printf("callee-saved D8-D15 preserved across trust-cg call; result=11\n");
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
fn e2e_aarch64_callee_saved_fpr_preserved() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt);
        let Some(code) = link_run("callee_saved_fpr", &obj) else {
            return;
        };
        assert_eq!(
            code, 0,
            "callee-saved FPR (D8-D15) not preserved across call at {opt:?} (code {code})",
        );
    }
}

// Mixed GPR+FPR callee-saved frame: pins sentinels in ALL of X19–X28 and D8–D15
// across a call that forces 8 int + 8 float values live simultaneously, and
// checks bit-exact preservation AND the numeric result against a C oracle. This
// exercises the multi-pair (9-pair) frame offset arithmetic and the FP-vs-GPR
// encoding of every saved pair together.
const STRESS_DRIVER: &str = r#"
#include <stdio.h>
#include <math.h>
#include <stdint.h>
extern int64_t stress(int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,
                      double,double,double,double,double,double,double,double);
static int64_t oracle(int64_t*I,double*F){
    int64_t s=0; for(int k=0;k<8;k++) s+=I[k];
    for(int k=0;k<8;k++) s+=(int64_t)F[k];   /* fptosi = trunc toward zero */
    s+=(int64_t)fmod(F[0],F[1]);
    return s;
}
int main(void){
    int64_t I[8]={ -5, 1000000000000LL, 7, -42, 999, -1, 123456789, 8 };
    double  F[8]={ 10.7, 3.0, -2.9, 100.5, -7.25, 65536.9, 0.0, -1e12 };
    register int64_t x19 asm("x19")=0x1919,x20 asm("x20")=0x2020,x21 asm("x21")=0x2121,
                     x22 asm("x22")=0x2222,x23 asm("x23")=0x2323,x24 asm("x24")=0x2424,
                     x25 asm("x25")=0x2525,x26 asm("x26")=0x2626,x27 asm("x27")=0x2727,x28 asm("x28")=0x2828;
    register double d8 asm("d8")=8.5,d9 asm("d9")=9.5,d10 asm("d10")=10.5,d11 asm("d11")=11.5,
                    d12 asm("d12")=12.5,d13 asm("d13")=13.5,d14 asm("d14")=14.5,d15 asm("d15")=15.5;
    asm volatile("":"+r"(x19),"+r"(x20),"+r"(x21),"+r"(x22),"+r"(x23),"+r"(x24),"+r"(x25),"+r"(x26),"+r"(x27),"+r"(x28),
                    "+w"(d8),"+w"(d9),"+w"(d10),"+w"(d11),"+w"(d12),"+w"(d13),"+w"(d14),"+w"(d15));
    int64_t got=stress(I[0],I[1],I[2],I[3],I[4],I[5],I[6],I[7],F[0],F[1],F[2],F[3],F[4],F[5],F[6],F[7]);
    asm volatile("":"+r"(x19),"+r"(x20),"+r"(x21),"+r"(x22),"+r"(x23),"+r"(x24),"+r"(x25),"+r"(x26),"+r"(x27),"+r"(x28),
                    "+w"(d8),"+w"(d9),"+w"(d10),"+w"(d11),"+w"(d12),"+w"(d13),"+w"(d14),"+w"(d15));
    int64_t ref=oracle(I,F);
    if(x19!=0x1919||x20!=0x2020||x21!=0x2121||x22!=0x2222||x23!=0x2323||x24!=0x2424||x25!=0x2525||x26!=0x2626||x27!=0x2727||x28!=0x2828){printf("*** GPR clobbered ***\n");return 1;}
    if(d8!=8.5||d9!=9.5||d10!=10.5||d11!=11.5||d12!=12.5||d13!=13.5||d14!=14.5||d15!=15.5){printf("*** FPR clobbered ***\n");return 1;}
    if(got!=ref){printf("*** result got=%lld ref=%lld ***\n",(long long)got,(long long)ref);return 2;}
    printf("mixed GPR+FPR callee-saved frame preserved; result matches oracle\n");
    return 0;
}
"#;

fn link_run_driver(tag: &str, obj: &[u8], driver: &str) -> Option<i32> {
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
            "-lm",
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
fn e2e_aarch64_mixed_callee_saved_frame_preserved() {
    let module = build_stress_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt);
        let Some(code) = link_run_driver("stress_callee_saved", &obj, STRESS_DRIVER) else {
            return;
        };
        assert_eq!(
            code, 0,
            "mixed GPR+FPR callee-saved frame failed at {opt:?} (code {code})",
        );
    }
}
