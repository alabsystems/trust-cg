// trust-cg-codegen/tests/e2e_x86_64_fp_across_call.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Permanent x86-64 regression for the "floating-point value live across a
// function call" pattern.
//
// In the System V AMD64 ABI ALL XMM registers (XMM0..XMM15) are caller-saved
// (volatile). A floating-point SSA value that is defined before a `call` and
// used after it therefore CANNOT remain in any XMM register across the call:
// the callee is permitted to clobber every XMM. The register allocator must
// either spill the live float to the stack across the call or otherwise keep
// it out of a clobbered register. (x86-64 SysV has NO callee-saved XMM, so a
// spill to the stack is the only sound option.)
//
// The pipeline marks all caller-saved XMM as implicit-defs on each `call`
// (crates/trust-cg-codegen/src/x86_64/pipeline.rs, `is_call()` branch feeding
// `x86_64_caller_saved_regs`). This test asserts the allocator HONORS that
// clobber set: it builds functions that receive/compute an f64 (and an f32),
// make one and two calls with the float live across, and compare the result
// against clang. A miscompile here means the post-call use read a clobbered
// XMM and the float differs from the reference.
//
// These tests gate on `x86_64_oracle_enabled` like the rest of the x86-64
// oracle suite, so they early-return cleanly on non-x86-64 hosts.

mod common;

use common::x86_64_corpus::{
    TripleOracleCase, x86_64_differential_test, x86_64_oracle_enabled, x86_64_triple_oracle_test,
};

use trust_ir::{BinOp, CastOp, Constant, FuncTy, Inst, InstrNode, Ty};
use trust_ir::{Block as TrustIrBlock, Function as TrustIrFunction, Module as TrustIrModule};
use trust_ir::{BlockId, FuncId, ValueId};

// ---------------------------------------------------------------------------
// Module builders
// ---------------------------------------------------------------------------

/// A trivial integer callee that the pipeline must treat as clobbering every
/// caller-saved XMM:
///
/// ```c
/// long _sink(long n) { return n + 1; }
/// ```
///
/// Even though its body touches no XMM, the call site adds all caller-saved
/// XMM as implicit-defs, which is exactly the interference the allocator must
/// honor for any float live across a call to it.
fn append_sink(module: &mut TrustIrModule, func_id: u32, name: &str) -> u32 {
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(f);
    func_id
}

/// `long _fp_one_call(long n, double x)`:
///
/// ```c
/// long _sink(long n);
/// long _fp_one_call(long n, double x) {
///     double y = x + 1.0;       // y live across the call (in an XMM)
///     long  s = _sink(n);       // clobbers every caller-saved XMM
///     double z = y * 2.0 + (double)s;  // reads y AFTER the call
///     return (long)z;
/// }
/// ```
///
/// `y` is defined before the call and used after it. If the allocator leaves
/// `y` in a caller-saved XMM across `_sink`, the post-call use reads garbage.
fn build_fp_one_call_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let sink = append_sink(&mut module, 0, "_sink");

    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::F64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(1), "_fp_one_call", ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::F64)],
        body: vec![
            // y = x + 1.0
            InstrNode::new(Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(1.0),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::F64,
                lhs: ValueId::new(1),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(3)), // y
            // s = _sink(n)  -- clobbers all caller-saved XMM
            InstrNode::new(Inst::Call {
                callee: FuncId::new(sink),
                args: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(4)), // s
            // sd = (double)s
            InstrNode::new(Inst::Cast {
                op: CastOp::SIToFP,
                src_ty: Ty::I64,
                dst_ty: Ty::F64,
                operand: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
            // y2 = y * 2.0  -- reads y AFTER the call
            InstrNode::new(Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(2.0),
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::FMul,
                ty: Ty::F64,
                lhs: ValueId::new(3),
                rhs: ValueId::new(6),
            })
            .with_result(ValueId::new(7)),
            // z = y2 + sd
            InstrNode::new(Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::F64,
                lhs: ValueId::new(7),
                rhs: ValueId::new(5),
            })
            .with_result(ValueId::new(8)),
            // return (long)z
            InstrNode::new(Inst::Cast {
                op: CastOp::FPToSI,
                src_ty: Ty::F64,
                dst_ty: Ty::I64,
                operand: ValueId::new(8),
            })
            .with_result(ValueId::new(9)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(9)],
            }),
        ],
    }];
    module.add_function(f);
    module
}

/// `long _fp_two_calls(long n, double x)`:
///
/// ```c
/// long _sink(long n);
/// long _fp_two_calls(long n, double x) {
///     double y = x + 1.0;            // y live across BOTH calls
///     long a = _sink(n);             // call #1 clobbers XMM
///     long b = _sink(a);             // call #2 clobbers XMM (y still live)
///     double z = y * 4.0 + (double)(a + b);   // reads y after both calls
///     return (long)z;
/// }
/// ```
///
/// The float `y` must survive two distinct call sites. This is the exact
/// "TWO calls where the float stays live in an XMM across the first call"
/// shape from the original bug report.
fn build_fp_two_calls_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let sink = append_sink(&mut module, 0, "_sink");

    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::F64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(1), "_fp_two_calls", ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::F64)],
        body: vec![
            // y = x + 1.0
            InstrNode::new(Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(1.0),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::F64,
                lhs: ValueId::new(1),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(3)), // y
            // a = _sink(n)  -- call #1
            InstrNode::new(Inst::Call {
                callee: FuncId::new(sink),
                args: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(4)), // a
            // b = _sink(a)  -- call #2; y still live across it
            InstrNode::new(Inst::Call {
                callee: FuncId::new(sink),
                args: vec![ValueId::new(4)],
            })
            .with_result(ValueId::new(5)), // b
            // ab = a + b
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(4),
                rhs: ValueId::new(5),
            })
            .with_result(ValueId::new(6)),
            // abd = (double)ab
            InstrNode::new(Inst::Cast {
                op: CastOp::SIToFP,
                src_ty: Ty::I64,
                dst_ty: Ty::F64,
                operand: ValueId::new(6),
            })
            .with_result(ValueId::new(7)),
            // y4 = y * 4.0  -- reads y AFTER both calls
            InstrNode::new(Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(4.0),
            })
            .with_result(ValueId::new(8)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::FMul,
                ty: Ty::F64,
                lhs: ValueId::new(3),
                rhs: ValueId::new(8),
            })
            .with_result(ValueId::new(9)),
            // z = y4 + abd
            InstrNode::new(Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::F64,
                lhs: ValueId::new(9),
                rhs: ValueId::new(7),
            })
            .with_result(ValueId::new(10)),
            InstrNode::new(Inst::Cast {
                op: CastOp::FPToSI,
                src_ty: Ty::F64,
                dst_ty: Ty::I64,
                operand: ValueId::new(10),
            })
            .with_result(ValueId::new(11)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(11)],
            }),
        ],
    }];
    module.add_function(f);
    module
}

/// `long _f32_across_call(long n, float x)` — the f32 variant of the one-call
/// pattern. Probes whether the 32-bit XMM class is handled the same way.
///
/// ```c
/// long _sink(long n);
/// long _f32_across_call(long n, float x) {
///     float y = x + 1.0f;            // y live across the call
///     long s = _sink(n);             // clobbers XMM
///     float z = y * 2.0f + (float)s; // reads y after the call
///     return (long)z;
/// }
/// ```
fn build_f32_across_call_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let sink = append_sink(&mut module, 0, "_sink");

    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::F32],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(1), "_f32_across_call", ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::F32)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::F32,
                value: Constant::Float(1.0),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::F32,
                lhs: ValueId::new(1),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(3)), // y
            InstrNode::new(Inst::Call {
                callee: FuncId::new(sink),
                args: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(4)), // s
            InstrNode::new(Inst::Cast {
                op: CastOp::SIToFP,
                src_ty: Ty::I64,
                dst_ty: Ty::F32,
                operand: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Const {
                ty: Ty::F32,
                value: Constant::Float(2.0),
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::FMul,
                ty: Ty::F32,
                lhs: ValueId::new(3),
                rhs: ValueId::new(6),
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::F32,
                lhs: ValueId::new(7),
                rhs: ValueId::new(5),
            })
            .with_result(ValueId::new(8)),
            InstrNode::new(Inst::Cast {
                op: CastOp::FPToSI,
                src_ty: Ty::F32,
                dst_ty: Ty::I64,
                operand: ValueId::new(8),
            })
            .with_result(ValueId::new(9)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(9)],
            }),
        ],
    }];
    module.add_function(f);
    module
}

// ---------------------------------------------------------------------------
// C references / drivers
// ---------------------------------------------------------------------------

// For the differential harness, the C *reference* defines the functions while
// the *driver* only declares them `extern` and runs them. They are linked
// separately (driver + trust-cg .o, driver + clang .o), so the function
// bodies must NOT live in the driver or the trust-cg link gets duplicates.

const ONE_CALL_REF_C: &str = r#"
long _sink(long n) { return n + 1; }
long _fp_one_call(long n, double x) {
    double y = x + 1.0;
    long s = _sink(n);
    double z = y * 2.0 + (double)s;
    return (long)z;
}
"#;

const ONE_CALL_DRIVER_C: &str = r#"
#include <stdio.h>
extern long _fp_one_call(long n, double x);
int main(void) {
    printf("one_call(3,2.5)=%ld\n", _fp_one_call(3, 2.5));
    printf("one_call(10,100.25)=%ld\n", _fp_one_call(10, 100.25));
    printf("one_call(-4,7.75)=%ld\n", _fp_one_call(-4, 7.75));
    return 0;
}
"#;

const TWO_CALLS_REF_C: &str = r#"
long _sink(long n) { return n + 1; }
long _fp_two_calls(long n, double x) {
    double y = x + 1.0;
    long a = _sink(n);
    long b = _sink(a);
    double z = y * 4.0 + (double)(a + b);
    return (long)z;
}
"#;

const TWO_CALLS_DRIVER_C: &str = r#"
#include <stdio.h>
extern long _fp_two_calls(long n, double x);
int main(void) {
    printf("two_calls(3,2.5)=%ld\n", _fp_two_calls(3, 2.5));
    printf("two_calls(10,100.25)=%ld\n", _fp_two_calls(10, 100.25));
    printf("two_calls(-4,7.75)=%ld\n", _fp_two_calls(-4, 7.75));
    return 0;
}
"#;

const F32_REF_C: &str = r#"
long _sink(long n) { return n + 1; }
long _f32_across_call(long n, float x) {
    float y = x + 1.0f;
    long s = _sink(n);
    float z = y * 2.0f + (float)s;
    return (long)z;
}
"#;

const F32_DRIVER_C: &str = r#"
#include <stdio.h>
extern long _f32_across_call(long n, float x);
int main(void) {
    printf("f32(3,2.5)=%ld\n", _f32_across_call(3, 2.5f));
    printf("f32(10,100.25)=%ld\n", _f32_across_call(10, 100.25f));
    printf("f32(-4,7.75)=%ld\n", _f32_across_call(-4, 7.75f));
    return 0;
}
"#;

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[test]
fn test_x86_64_fp_one_call_differential() {
    if !x86_64_oracle_enabled("fp_one_call_diff") {
        return;
    }
    let module = build_fp_one_call_module();
    x86_64_differential_test(
        "fp_one_call_diff",
        &module,
        ONE_CALL_REF_C,
        ONE_CALL_DRIVER_C,
    )
    .expect("f64 live across one call must match clang");
}

#[test]
fn test_x86_64_fp_two_calls_differential() {
    if !x86_64_oracle_enabled("fp_two_calls_diff") {
        return;
    }
    let module = build_fp_two_calls_module();
    x86_64_differential_test(
        "fp_two_calls_diff",
        &module,
        TWO_CALLS_REF_C,
        TWO_CALLS_DRIVER_C,
    )
    .expect("f64 live across two calls must match clang");
}

#[test]
fn test_x86_64_f32_across_call_differential() {
    if !x86_64_oracle_enabled("f32_across_call_diff") {
        return;
    }
    let module = build_f32_across_call_module();
    x86_64_differential_test("f32_across_call_diff", &module, F32_REF_C, F32_DRIVER_C)
        .expect("f32 live across a call must match clang");
}

// The triple-oracle variant additionally pins the trust_ir interpreter as a
// third independent truth source (interp == trust-cg == clang).
//
// The triple-oracle harness drives every function with i64-only arguments (it
// shares one set of inputs across the interpreter and the C driver). To keep a
// float live across calls while staying i64-in/i64-out, the function takes a
// single `long n`, converts it to a double internally, holds that double live
// across TWO calls, and returns an i64 derived from it.

/// `long _fp_int_io(long n)`:
///
/// ```c
/// long _sink2(long n);
/// long _fp_int_io(long n) {
///     double y = (double)n + 0.5;   // y live across both calls
///     long a = _sink2(n);           // call #1 clobbers all caller-saved XMM
///     long b = _sink2(a);           // call #2; y still live
///     double z = y * 2.0 + (double)(a + b);  // reads y after both calls
///     return (long)z;
/// }
/// ```
fn build_fp_int_io_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let sink = append_sink(&mut module, 0, "_sink2");

    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(1), "_fp_int_io", ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            // nd = (double)n
            InstrNode::new(Inst::Cast {
                op: CastOp::SIToFP,
                src_ty: Ty::I64,
                dst_ty: Ty::F64,
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
            // y = nd + 0.5
            InstrNode::new(Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(0.5),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::F64,
                lhs: ValueId::new(1),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(3)), // y
            // a = _sink2(n) -- call #1
            InstrNode::new(Inst::Call {
                callee: FuncId::new(sink),
                args: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(4)), // a
            // b = _sink2(a) -- call #2
            InstrNode::new(Inst::Call {
                callee: FuncId::new(sink),
                args: vec![ValueId::new(4)],
            })
            .with_result(ValueId::new(5)), // b
            // ab = a + b
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(4),
                rhs: ValueId::new(5),
            })
            .with_result(ValueId::new(6)),
            // abd = (double)ab
            InstrNode::new(Inst::Cast {
                op: CastOp::SIToFP,
                src_ty: Ty::I64,
                dst_ty: Ty::F64,
                operand: ValueId::new(6),
            })
            .with_result(ValueId::new(7)),
            // y2 = y * 2.0  -- reads y after both calls
            InstrNode::new(Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(2.0),
            })
            .with_result(ValueId::new(8)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::FMul,
                ty: Ty::F64,
                lhs: ValueId::new(3),
                rhs: ValueId::new(8),
            })
            .with_result(ValueId::new(9)),
            // z = y2 + abd
            InstrNode::new(Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::F64,
                lhs: ValueId::new(9),
                rhs: ValueId::new(7),
            })
            .with_result(ValueId::new(10)),
            InstrNode::new(Inst::Cast {
                op: CastOp::FPToSI,
                src_ty: Ty::F64,
                dst_ty: Ty::I64,
                operand: ValueId::new(10),
            })
            .with_result(ValueId::new(11)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(11)],
            }),
        ],
    }];
    module.add_function(f);
    module
}

const INT_IO_C: &str = r#"
#include <stdio.h>

#ifndef EXTERN_ONLY
long _sink2(long n) { return n + 1; }
long _fp_int_io(long n) {
    double y = (double)n + 0.5;
    long a = _sink2(n);
    long b = _sink2(a);
    double z = y * 2.0 + (double)(a + b);
    return (long)z;
}
#else
extern long _fp_int_io(long n);
#endif

int main(void) {
    printf("fp_int_io(0)=%ld\n", _fp_int_io(0));
    printf("fp_int_io(3)=%ld\n", _fp_int_io(3));
    printf("fp_int_io(7)=%ld\n", _fp_int_io(7));
    printf("fp_int_io(-5)=%ld\n", _fp_int_io(-5));
    printf("fp_int_io(100)=%ld\n", _fp_int_io(100));
    return 0;
}
"#;

#[test]
fn test_x86_64_fp_across_two_calls_triple_oracle() {
    if !x86_64_oracle_enabled("fp_int_io_triple") {
        return;
    }
    let module = build_fp_int_io_module();
    let cases = vec![
        TripleOracleCase::new("fp_int_io(0)", &[0]),
        TripleOracleCase::new("fp_int_io(3)", &[3]),
        TripleOracleCase::new("fp_int_io(7)", &[7]),
        TripleOracleCase::new("fp_int_io(-5)", &[-5]),
        TripleOracleCase::new("fp_int_io(100)", &[100]),
    ];
    x86_64_triple_oracle_test("fp_int_io_triple", &module, "_fp_int_io", INT_IO_C, &cases)
        .expect("f64 live across two calls: all three oracles must agree");
}
