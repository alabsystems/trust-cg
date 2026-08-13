// trust-cg-codegen/tests/e2e_aarch64_stack_narrow_args.rs
//
// Pinned refutation for a confirmed P0 ABI miscompile: narrow (i8/i16/i32)
// integer arguments passed ON THE STACK (beyond X0-X7) were laid out with the
// standard AAPCS64 "one 8-byte slot per argument" rule, but the Apple arm64 ABI
// PACKS fixed stack arguments at their natural size and alignment.
//
// For `f(i64 x8, i8 a, i16 b, i32 c, i8 d)` the four stack args sit at byte
// offsets 0, 2, 4, 8 (natural packing) in clang's layout, NOT 0, 8, 16, 24.
// Both directions were wrong:
//   * Callee read the args from 8-byte-slot offsets -> garbage.
//   * Caller extended each narrow arg to i32 and stored it in a 4-byte slot
//     (offsets 0,4,8,12) with a full-word STR -> wrong offsets AND clobbered
//     neighbouring packed args.
//
// Ground truth (verified by disassembling clang -O2):
//   caller:  strb w,[sp] ; strh w,[sp,#2] ; str w,[sp,#4] ; strb w,[sp,#8]
//   callee:  ldrb ...,[fp,#..] ; ldrh ...,[fp,#..+2] ; ldr w ...,[..+4] ; ...
// i.e. natural width, natural packed offset, UNEXTENDED (the callee extends on
// load). This test pins BOTH directions bit-exactly against clang at -O2, where
// clang trusts the ABI and does not re-narrow.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    Block as TrustIrBlock, CastOp, Constant, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Linkage, Module as TrustIrModule, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

// Params: 8x i64 (fill X0-X7) then i8, i16, i32, i8 (these four spill to the
// stack). Both the callee (build_callee_module) and the caller
// (build_caller_module) use this exact signature.
fn stack_narrow_params() -> Vec<Ty> {
    vec![
        Ty::I64,
        Ty::I64,
        Ty::I64,
        Ty::I64,
        Ty::I64,
        Ty::I64,
        Ty::I64,
        Ty::I64,
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I8,
    ]
}

// ------------------------------------------------------------------------
// Direction A: trust-cg is the CALLEE reading narrow stack args.
// `nsum(...) -> i64` returns sext(a)+sext(b)+sext(c)+sext(d).
// ------------------------------------------------------------------------
fn build_callee_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("stack_narrow_callee");
    let ft = m.add_func_type(FuncTy {
        params: stack_narrow_params(),
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(0), "nsum", ft, BlockId::new(0));
    let params: Vec<(ValueId, Ty)> = stack_narrow_params()
        .into_iter()
        .enumerate()
        .map(|(i, t)| (ValueId::new(i as u32), t))
        .collect();
    // sext each narrow arg (values 8,9,10,11) to i64, then add them up.
    let mut body = Vec::new();
    let sext = |dst: u32, src: u32, from: Ty| {
        InstrNode::new(Inst::Cast {
            op: CastOp::SExt,
            src_ty: from,
            dst_ty: Ty::I64,
            operand: ValueId::new(src),
        })
        .with_result(ValueId::new(dst))
    };
    body.push(sext(20, 8, Ty::I8));
    body.push(sext(21, 9, Ty::I16));
    body.push(sext(22, 10, Ty::I32));
    body.push(sext(23, 11, Ty::I8));
    let add = |dst: u32, a: u32, b: u32| {
        InstrNode::new(Inst::BinOp {
            op: trust_ir::BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(a),
            rhs: ValueId::new(b),
        })
        .with_result(ValueId::new(dst))
    };
    body.push(add(24, 20, 21));
    body.push(add(25, 24, 22));
    body.push(add(26, 25, 23));
    body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(26)],
    }));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params,
        body,
    }];
    m.add_function(f);
    m
}

// ------------------------------------------------------------------------
// Direction B: trust-cg is the CALLER storing narrow stack args, calling an
// external clang `sink`. `caller(a: i8, b: i16, c: i32, d: i8) -> i64`
// calls `sink(0,0,0,0,0,0,0,0, a, b, c, d)`.
// ------------------------------------------------------------------------
fn build_caller_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("stack_narrow_caller");

    // External declaration of sink (provided by clang).
    let sink_ft = m.add_func_type(FuncTy {
        params: stack_narrow_params(),
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut sink = TrustIrFunction::new(FuncId::new(0), "sink", sink_ft, BlockId::new(0));
    sink.blocks = vec![]; // bodyless import
    sink.linkage = Linkage::External;
    m.add_function(sink);

    // caller(a: i8, b: i16, c: i32, d: i8) -> i64
    let caller_ft = m.add_func_type(FuncTy {
        params: vec![Ty::I8, Ty::I16, Ty::I32, Ty::I8],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut caller = TrustIrFunction::new(FuncId::new(1), "caller", caller_ft, BlockId::new(0));
    // params a=%0 b=%1 c=%2 d=%3 ; %4 = const i64 0 (the eight register fillers)
    let mut body = Vec::new();
    body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(0),
        })
        .with_result(ValueId::new(4)),
    );
    let zero = ValueId::new(4);
    body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![
                zero,
                zero,
                zero,
                zero,
                zero,
                zero,
                zero,
                zero,
                ValueId::new(0),
                ValueId::new(1),
                ValueId::new(2),
                ValueId::new(3),
            ],
        })
        .with_result(ValueId::new(5)),
    );
    body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(5)],
    }));
    caller.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::I8),
            (ValueId::new(1), Ty::I16),
            (ValueId::new(2), Ty::I32),
            (ValueId::new(3), Ty::I8),
        ],
        body,
    }];
    m.add_function(caller);
    m
}

fn compile_at(module: &TrustIrModule, opt: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    });
    let r = compiler
        .compile(module)
        .expect("narrow-stack-arg module must compile");
    assert!(!r.object_code.is_empty());
    r.object_code
}

const CALLEE_DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
extern int64_t nsum(int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,
                    int8_t,int16_t,int32_t,int8_t);
int main(void){
    struct { int8_t a; int16_t b; int32_t c; int8_t d; } C[] = {
        {-5,-3000,100000,-7}, {0,0,0,0}, {127,32767,2147483647,-128},
        {-128,-32768,-2147483647,127}, {1,2,3,4},
    };
    for (unsigned i=0;i<sizeof(C)/sizeof(C[0]);i++){
        int64_t got=nsum(0,0,0,0,0,0,0,0,C[i].a,C[i].b,C[i].c,C[i].d);
        int64_t ref=(int64_t)C[i].a+(int64_t)C[i].b+(int64_t)C[i].c+(int64_t)C[i].d;
        if(got!=ref){printf("callee MISMATCH #%u got=%lld ref=%lld\n",i,(long long)got,(long long)ref);return 1;}
    }
    printf("callee reads narrow stack args bit-exact vs clang\n");
    return 0;
}
"#;

const CALLER_DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
/* clang-compiled callee; -O2 trusts the ABI and reads the packed natural-width
   slots directly (ldrb/ldrh/ldr w at offsets 0,2,4,8). */
int64_t sink(int64_t x0,int64_t x1,int64_t x2,int64_t x3,int64_t x4,int64_t x5,
             int64_t x6,int64_t x7, int8_t a,int16_t b,int32_t c,int8_t d){
    (void)x0;(void)x1;(void)x2;(void)x3;(void)x4;(void)x5;(void)x6;(void)x7;
    return (int64_t)a + (int64_t)b + (int64_t)c + (int64_t)d;
}
extern int64_t caller(int8_t a,int16_t b,int32_t c,int8_t d);
int main(void){
    struct { int8_t a; int16_t b; int32_t c; int8_t d; } C[] = {
        {-5,-3000,100000,-7}, {0,0,0,0}, {127,32767,2147483647,-128},
        {-128,-32768,-2147483647,127}, {1,2,3,4},
    };
    for (unsigned i=0;i<sizeof(C)/sizeof(C[0]);i++){
        int64_t got=caller(C[i].a,C[i].b,C[i].c,C[i].d);
        int64_t ref=(int64_t)C[i].a+(int64_t)C[i].b+(int64_t)C[i].c+(int64_t)C[i].d;
        if(got!=ref){printf("caller MISMATCH #%u got=%lld ref=%lld\n",i,(long long)got,(long long)ref);return 1;}
    }
    printf("caller stores narrow stack args bit-exact vs clang\n");
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
    // -O2 is essential: at -O0 clang re-narrows narrow params, masking a layout
    // or extension bug.
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
fn e2e_aarch64_callee_reads_narrow_stack_args() {
    let module = build_callee_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt);
        let Some(code) = link_run("stack_narrow_callee", &obj, CALLEE_DRIVER) else {
            return;
        };
        assert_eq!(code, 0, "callee narrow-stack-arg read failed at {opt:?}");
    }
}

#[test]
fn e2e_aarch64_caller_stores_narrow_stack_args() {
    let module = build_caller_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt);
        let Some(code) = link_run("stack_narrow_caller", &obj, CALLER_DRIVER) else {
            return;
        };
        assert_eq!(code, 0, "caller narrow-stack-arg store failed at {opt:?}");
    }
}
