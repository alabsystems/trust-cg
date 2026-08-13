// a64_interp_fcmp_nan.rs — the on-host AArch64 CORRECTNESS harness for scalar
// floating-point compares, with the NaN / NZCV edge cases that RE-FIND and pin
// the owner-#10 `fcmp`-on-NaN miscompile.
//
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// # What this catches
//
// An AArch64 `FCMP` sets NZCV to `0b0011` (N=0 Z=0 C=1 V=1) when either operand
// is NaN. The ORDERED predicates (Rust `<`, `<=`, `>`, `>=`, `==`, and ordered
// `!=`) must all be FALSE for NaN. Most map to a single condition code that is
// already false for NaN (OLT→MI, OLE→LS, OGT→GT, OGE→GE, OEQ→EQ). The exception
// is ORDERED not-equal (`ONE`): it was lowered to the bare `NE` condition, which
// is ALSO true for NaN (Z=0), so `x != y` wrongly returned true when either
// operand was NaN. `ONE` is not a single AArch64 condition code — it is
// `NE && VC` (not-equal AND ordered) — so the fixed lowering materializes two
// CSETs and ANDs them.
//
// The `fcmp_nan_sweep` test compiles the REAL codegen for every FCmpOp and
// asserts the interpreted AArch64 result against the faithful `trust_ir`
// interpreter over a NaN-heavy operand grid. The `teeth_*` test hand-assembles
// the exact PRE-FIX buggy lowering (a single `CSET NE`) and confirms the harness
// reports its wrong NaN answer, then confirms the FIXED lowering is correct —
// proving the harness has teeth against the real defect.

mod common;
use common::a64_interp::A64Interp;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{
    Block as B, Constant, FCmpOp, FuncTy, Function as F, Inst, InstrNode, InterpretValue,
    InterpretValueKind, Interpreter, Module as M, Ty,
};
use trust_ir::{BlockId, FuncId, ValueId};

const FN: &str = "_c";
const SYM: &str = "__c";

/// `fn _c(a:f64,b:f64)->i32 { (a <op> b) as i32 }`
fn build_fcmp(op: FCmpOp) -> M {
    let mut m = M::new("fcmp");
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::F64, Ty::F64],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut f = F::new(FuncId::new(0), FN, ft, BlockId::new(0));
    f.blocks = vec![B {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::F64), (ValueId::new(1), Ty::F64)],
        body: vec![
            InstrNode::new(Inst::FCmp {
                op,
                ty: Ty::F64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Select {
                ty: Ty::I32,
                cond: ValueId::new(2),
                then_val: ValueId::new(3),
                else_val: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(5)],
            }),
        ],
    }];
    m.add_function(f);
    m
}

fn fp_arg(v: f64) -> InterpretValue {
    InterpretValue {
        ty: Ty::F64,
        kind: InterpretValueKind::FloatBits(v.to_bits()),
    }
}

/// Faithful `trust_ir::Interpreter` oracle for `_c(a, b)`.
fn oracle(m: &M, a: f64, b: f64) -> i32 {
    Interpreter::with_module(m)
        .execute_func(FuncId::new(0), [fp_arg(a), fp_arg(b)])
        .expect("oracle executes")
        .returns[0]
        .as_int()
        .expect("int result")
        .as_signed() as i32
}

fn compile(m: &M, opt: OptLevel) -> Vec<u8> {
    let c = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    });
    c.compile(m).expect("compile").object_code
}

/// Decode + interpret the emitted AArch64 `_c(a, b)` on this host.
fn a64(obj: &[u8], a: f64, b: f64) -> i32 {
    use common::a64_interp::{extract_text, symbol_addrs};
    let text = extract_text(obj);
    let addrs = symbol_addrs(obj);
    let entry = (*addrs.get(SYM).expect("_c symbol") - text.addr) as usize;
    let mut interp = A64Interp::new(text.bytes);
    interp.set_d(0, a);
    interp.set_d(1, b);
    interp.run(entry).expect("interpret _c") as u32 as i32
}

/// The NaN-heavy operand grid. Includes equal / less / greater / signed-zero /
/// infinities and every NaN placement.
fn grid() -> Vec<(f64, f64)> {
    let nan = f64::NAN;
    let inf = f64::INFINITY;
    vec![
        (1.0, 2.0),
        (2.0, 1.0),
        (1.5, 1.5),
        (-1.0, 0.0),
        (0.0, -1.0),
        (0.0, 0.0),
        (-0.0, 0.0),
        (inf, 1.0),
        (1.0, inf),
        (-inf, inf),
        (nan, 1.0),
        (1.0, nan),
        (nan, nan),
        (nan, inf),
    ]
}

fn all_ops() -> Vec<FCmpOp> {
    use FCmpOp::*;
    vec![OEq, ONe, OLt, OLe, OGt, OGe, UEq, UNe, ULt, ULe, UGt, UGe]
}

#[test]
fn fcmp_nan_sweep() {
    for op in all_ops() {
        let m = build_fcmp(op);
        for opt in [OptLevel::O0, OptLevel::O2] {
            let obj = compile(&m, opt);
            for (a, b) in grid() {
                let want = oracle(&m, a, b);
                let got = a64(&obj, a, b);
                assert_eq!(
                    got, want,
                    "AArch64 fcmp MISCOMPILE {op:?} at {opt:?}: _c({a}, {b}) = {got}, oracle {want}",
                );
            }
        }
    }
}

/// Focused assertion on the exact owner-#10 shape: ordered `!=` on a NaN operand
/// must be FALSE, and the emitted codegen must produce 0.
#[test]
fn ordered_ne_on_nan_is_false() {
    let m = build_fcmp(FCmpOp::ONe);
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile(&m, opt);
        assert_eq!(oracle(&m, f64::NAN, 1.0), 0, "ONE(NaN,1) is false");
        assert_eq!(
            a64(&obj, f64::NAN, 1.0),
            0,
            "codegen: ONE(NaN,1) must be 0 at {opt:?}"
        );
        assert_eq!(a64(&obj, 1.0, f64::NAN), 0, "codegen: ONE(1,NaN) must be 0");
        assert_eq!(a64(&obj, f64::NAN, f64::NAN), 0, "codegen: ONE(NaN,NaN)=0");
        // Non-NaN ordered `!=` still works.
        assert_eq!(a64(&obj, 1.0, 2.0), 1, "ONE(1,2)=1");
        assert_eq!(a64(&obj, 1.0, 1.0), 0, "ONE(1,1)=0");
    }
}

// ---------------------------------------------------------------------------
// TEETH: reproduce the pre-fix buggy lowering (single `CSET NE`) and confirm the
// harness reports its wrong NaN answer; confirm the fixed lowering is correct.
// ---------------------------------------------------------------------------

fn asm(words: &[u32]) -> Vec<u8> {
    words.iter().flat_map(|w| w.to_le_bytes()).collect()
}

// Fixed instruction words (verified against the leaf disassembler dump):
const FCMP_D0_D1: u32 = 0x1e61_2000; // FCMP D0, D1  (sets NZCV per FP compare)
const CSET_X0_NE: u32 = 0x9a9f_07e0; // CSET X0, NE  (CSINC X0,XZR,XZR, inv=EQ)
const CSET_X1_VC: u32 = 0x9a9f_67e1; // CSET X1, VC  (CSINC X1,XZR,XZR, inv=VS)
const AND_X0_X0_X1: u32 = 0x8a01_0000; // AND X0, X0, X1
const RET: u32 = 0xd65f_03c0; // RET

fn run_bytes(bytes: Vec<u8>, a: f64, b: f64) -> i32 {
    let mut interp = A64Interp::new(bytes);
    interp.set_d(0, a);
    interp.set_d(1, b);
    interp.run(0).expect("snippet runs") as u32 as i32
}

#[test]
fn teeth_ordered_ne_on_nan_bug_and_fix() {
    let m = build_fcmp(FCmpOp::ONe);
    let key_nan = oracle(&m, f64::NAN, 1.0); // = 0 (ordered != is false on NaN)
    let key_lt = oracle(&m, 1.0, 2.0); // = 1
    assert_eq!(key_nan, 0);
    assert_eq!(key_lt, 1);

    // PRE-FIX BUGGY lowering of ordered `!=`: a single `CSET NE`. NE tests Z=0,
    // and FCMP(NaN, x) sets Z=0, so this returns 1 for NaN — the miscompile.
    let buggy = asm(&[FCMP_D0_D1, CSET_X0_NE, RET]);
    assert_eq!(
        run_bytes(buggy.clone(), f64::NAN, 1.0),
        1,
        "the buggy single-CSET-NE lowering returns the WRONG NaN answer (1)"
    );
    // Off NaN the bug is invisible — it agrees with the oracle there.
    assert_eq!(run_bytes(buggy.clone(), 1.0, 2.0), key_lt);
    // TEETH: the harness DETECTS the miscompile (buggy NaN answer != oracle).
    assert_ne!(
        run_bytes(buggy, f64::NAN, 1.0),
        key_nan,
        "TEETH: the harness must flag the buggy fcmp-on-NaN lowering"
    );

    // FIXED lowering: NE && VC (not-equal AND ordered). VC tests V=0, and
    // FCMP(NaN,x) sets V=1, so VC=false → the AND is 0 for NaN. Correct.
    let fixed = asm(&[FCMP_D0_D1, CSET_X0_NE, CSET_X1_VC, AND_X0_X0_X1, RET]);
    assert_eq!(
        run_bytes(fixed.clone(), f64::NAN, 1.0),
        key_nan,
        "the fixed NE&&VC lowering is correct on NaN (0)"
    );
    assert_eq!(
        run_bytes(fixed, 1.0, 2.0),
        key_lt,
        "the fixed lowering is still correct off NaN (1)"
    );
}
