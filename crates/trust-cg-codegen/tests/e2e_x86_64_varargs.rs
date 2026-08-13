// trust-cg-codegen/tests/e2e_x86_64_varargs.rs - x86-64 SysV varargs caller oracle
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Differential oracle for the System V AMD64 *variadic caller* ABI: a
// trust-cg-generated function calls a C variadic function (`CallVariadic`),
// and we compare the trust-cg-compiled program against an all-clang program
// calling the same C variadic function.
//
// Why this matters / what it proves:
//
//   The SysV AMD64 ABI requires that, before calling a variadic function, AL
//   holds the number of vector (XMM) registers used to pass arguments (0..8).
//   printf-family functions read AL to decide how many XMM registers to spill
//   into their register save area. If AL is wrong, a `double` vararg reads
//   garbage. These tests force a range of XMM counts (0, 1, 2) and integer
//   counts (including enough to spill onto the stack) and check the *observable
//   result* of the variadic callee, so an incorrect AL or a misplaced argument
//   is caught by value divergence vs. clang.
//
//   The trust-cg side passes the variadic arguments through exactly the same
//   GPR/XMM/overflow-stack classification as fixed arguments (which is the
//   correct SysV behavior: variadic integer args go in the GPR sequence, FP
//   args in the XMM sequence, overflow on the stack), and sets AL = total XMM
//   count. This is an ABI-placement property verified by differential
//   execution, not a new SMT lowering rule.
//
// The callee side of varargs (`va_start`/`va_arg`/`va_end` inside a function
// body) is intentionally NOT exercised here: trust-ir does not model those
// intrinsics (there is no VaStart/VaArg/VaEnd opcode), so a trust-cg function
// can never *consume* its own varargs. The variadic *callees* below are written
// in C (clang) on both link paths; only the *caller* is trust-cg-generated.
//
// Architecture: x86-64 host only (Mach-O AOT, `cc -arch x86_64`). On AArch64
// hosts these tests early-return. clang is the golden reference.

mod common;
use common::x86_64_corpus::{x86_64_differential_test, x86_64_oracle_enabled};

use trust_ir::{
    Block as TrustIrBlock, Constant, FuncTy, Function as TrustIrFunction, Inst, InstrNode, Linkage,
    Module as TrustIrModule, Ty,
};
use trust_ir::{BlockId, FuncId, ValueId};

// ---------------------------------------------------------------------------
// Builders
// ---------------------------------------------------------------------------

/// Declare a bodyless external variadic function so that calls to it lower to
/// `CallVariadic` (the adapter rewrites `Inst::Call` to `CallVariadic` when the
/// callee's `FuncTy.is_vararg` is true). `fixed_params` are the declared
/// non-variadic parameter types.
fn add_variadic_extern(
    module: &mut TrustIrModule,
    id: u32,
    name: &str,
    fixed_params: Vec<Ty>,
    returns: Vec<Ty>,
) -> FuncId {
    let ft_id = module.add_func_type(FuncTy {
        params: fixed_params,
        returns,
        is_vararg: true,
    });
    let mut decl = TrustIrFunction::new(FuncId::new(id), name, ft_id, BlockId::new(0));
    decl.blocks = vec![]; // bodyless declaration
    decl.linkage = Linkage::External;
    let fid = decl.id;
    module.add_function(decl);
    fid
}

/// Build `long _call_vsum_N(void)` that calls the C variadic
/// `long vsum(int n, ...)` with `n` `long` arguments `vals[0..n]` and returns
/// the result. This exercises integer varargs only (AL must be 0), including
/// counts that overflow the 6 integer arg registers onto the stack.
///
/// The C signature seen by the callee is `vsum(int n, long a0, long a1, ...)`.
fn build_call_vsum_module(func_name: &str, vals: &[i64]) -> TrustIrModule {
    let mut module = TrustIrModule::new("varargs_vsum");

    // extern long vsum(int n, ...);
    let vsum = add_variadic_extern(&mut module, 1, "vsum", vec![Ty::I32], vec![Ty::I64]);

    // long _call_vsum_N(void) { return vsum(N, vals[0], vals[1], ...); }
    let caller_ty = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut caller = TrustIrFunction::new(FuncId::new(0), func_name, caller_ty, BlockId::new(0));

    let mut body = Vec::new();
    let mut next_vid = 0u32;
    let mut alloc = || {
        let v = ValueId::new(next_vid);
        next_vid += 1;
        v
    };

    // n : i32 = vals.len()
    let n_v = alloc();
    body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(vals.len() as i128),
        })
        .with_result(n_v),
    );

    // each vararg long
    let mut call_args = vec![n_v];
    for &val in vals {
        let v = alloc();
        body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(val as i128),
            })
            .with_result(v),
        );
        call_args.push(v);
    }

    let result_v = alloc();
    body.push(
        InstrNode::new(Inst::Call {
            callee: vsum,
            args: call_args,
        })
        .with_result(result_v),
    );
    body.push(InstrNode::new(Inst::Return {
        values: vec![result_v],
    }));

    caller.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body,
    }];
    module.add_function(caller);
    module
}

/// Build `double _call_vmix_N(void)` that calls the C variadic
/// `double vmix(int n, ...)` with `n` `double` arguments and returns the sum.
/// This forces a NONZERO AL (one XMM register per double vararg, capped at 8),
/// which is exactly the SysV requirement that printf-family functions depend
/// on. Counts above 8 doubles additionally overflow onto the stack.
fn build_call_vmix_module(func_name: &str, vals: &[f64]) -> TrustIrModule {
    let mut module = TrustIrModule::new("varargs_vmix");

    // extern double vmix(int n, ...);
    let vmix = add_variadic_extern(&mut module, 1, "vmix", vec![Ty::I32], vec![Ty::F64]);

    let caller_ty = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::F64],
        is_vararg: false,
    });
    let mut caller = TrustIrFunction::new(FuncId::new(0), func_name, caller_ty, BlockId::new(0));

    let mut body = Vec::new();
    let mut next_vid = 0u32;
    let mut alloc = || {
        let v = ValueId::new(next_vid);
        next_vid += 1;
        v
    };

    let n_v = alloc();
    body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(vals.len() as i128),
        })
        .with_result(n_v),
    );

    let mut call_args = vec![n_v];
    for &val in vals {
        let v = alloc();
        body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(val),
            })
            .with_result(v),
        );
        call_args.push(v);
    }

    let result_v = alloc();
    body.push(
        InstrNode::new(Inst::Call {
            callee: vmix,
            args: call_args,
        })
        .with_result(result_v),
    );
    body.push(InstrNode::new(Inst::Return {
        values: vec![result_v],
    }));

    caller.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body,
    }];
    module.add_function(caller);
    module
}

/// Build `long _call_vmix2(void)` that calls `double vmix2(int n, ...)` with a
/// MIX of `long` (GPR) and `double` (XMM) variadic arguments, then truncates
/// the resulting double to a long. This is the key AL-correctness case: the
/// integer varargs consume the GPR sequence, the double varargs consume the
/// XMM sequence, and AL must equal the XMM count (not the total arg count).
///
/// We pass: n=4, then long 10, double 1.5, long 20, double 2.5  =>  AL must be 2.
fn build_call_vmix2_module(func_name: &str) -> TrustIrModule {
    let mut module = TrustIrModule::new("varargs_vmix2");

    // extern double vmix2(int n, ...);
    let vmix2 = add_variadic_extern(&mut module, 1, "vmix2", vec![Ty::I32], vec![Ty::F64]);

    let caller_ty = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut caller = TrustIrFunction::new(FuncId::new(0), func_name, caller_ty, BlockId::new(0));

    let v = |i: u32| ValueId::new(i);
    let body = vec![
        // n = 4
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(4),
        })
        .with_result(v(0)),
        // long 10
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(10),
        })
        .with_result(v(1)),
        // double 1.5
        InstrNode::new(Inst::Const {
            ty: Ty::F64,
            value: Constant::Float(1.5),
        })
        .with_result(v(2)),
        // long 20
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(20),
        })
        .with_result(v(3)),
        // double 2.5
        InstrNode::new(Inst::Const {
            ty: Ty::F64,
            value: Constant::Float(2.5),
        })
        .with_result(v(4)),
        // d = vmix2(4, 10L, 1.5, 20L, 2.5)
        InstrNode::new(Inst::Call {
            callee: vmix2,
            args: vec![v(0), v(1), v(2), v(3), v(4)],
        })
        .with_result(v(5)),
        // r = (long) d
        InstrNode::new(Inst::Cast {
            op: trust_ir::CastOp::FPToSI,
            src_ty: Ty::F64,
            dst_ty: Ty::I64,
            operand: v(5),
        })
        .with_result(v(6)),
        InstrNode::new(Inst::Return { values: vec![v(6)] }),
    ];

    caller.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body,
    }];
    module.add_function(caller);
    module
}

/// Build `long _call_snprintf(char *buf)` that calls libc `snprintf` with a
/// mix of integer and double conversions, returning the number of bytes that
/// would have been written. This exercises AL correctness against a *real* libc
/// variadic function (snprintf reads AL to spill XMM registers for `%f`).
///
/// `buf` is the function's only fixed parameter (a pointer passed in by the
/// driver); the format string is provided by the driver as a global the trust-cg
/// side does not need to synthesize — instead we have the C driver pass the
/// format pointer too, so trust-cg just forwards pointers + scalars.
///
/// Signature: `int _call_snprintf(char *buf, const char *fmt)`
///   returns snprintf(buf, 64, fmt, 42, 3.5, 7) as a long.
fn build_call_snprintf_module(func_name: &str) -> TrustIrModule {
    let mut module = TrustIrModule::new("varargs_snprintf");

    // extern int snprintf(char *restrict, size_t, const char *restrict, ...);
    let snprintf = add_variadic_extern(
        &mut module,
        1,
        "snprintf",
        vec![Ty::Ptr, Ty::I64, Ty::Ptr],
        vec![Ty::I32],
    );

    let caller_ty = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::Ptr],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut caller = TrustIrFunction::new(FuncId::new(0), func_name, caller_ty, BlockId::new(0));

    let v = |i: u32| ValueId::new(i);
    let body = vec![
        // size = 64
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(64),
        })
        .with_result(v(2)),
        // int 42
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(42),
        })
        .with_result(v(3)),
        // double 3.5
        InstrNode::new(Inst::Const {
            ty: Ty::F64,
            value: Constant::Float(3.5),
        })
        .with_result(v(4)),
        // int 7
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(7),
        })
        .with_result(v(5)),
        // ret = snprintf(buf, 64, fmt, 42, 3.5, 7)  -> AL must be 1
        InstrNode::new(Inst::Call {
            callee: snprintf,
            args: vec![v(0), v(2), v(1), v(3), v(4), v(5)],
        })
        .with_result(v(6)),
        // widen i32 result to i64 for return
        InstrNode::new(Inst::Cast {
            op: trust_ir::CastOp::SExt,
            src_ty: Ty::I32,
            dst_ty: Ty::I64,
            operand: v(6),
        })
        .with_result(v(7)),
        InstrNode::new(Inst::Return { values: vec![v(7)] }),
    ];

    caller.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        // params: buf (v0), fmt (v1)
        params: vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr)],
        body,
    }];
    module.add_function(caller);
    module
}

// ---------------------------------------------------------------------------
// Shared C: variadic callees defined in the driver (present on BOTH link paths)
// ---------------------------------------------------------------------------

/// Variadic callees, compiled identically into the driver on both the trust-cg
/// and the clang link paths so the only difference under test is who *calls*
/// them.
const VARARGS_CALLEES: &str = r#"
#include <stdarg.h>

/* sum n long varargs */
long vsum(int n, ...) {
    va_list ap;
    va_start(ap, n);
    long acc = 0;
    for (int i = 0; i < n; i++) {
        acc += va_arg(ap, long);
    }
    va_end(ap);
    return acc;
}

/* sum n double varargs (forces nonzero AL) */
double vmix(int n, ...) {
    va_list ap;
    va_start(ap, n);
    double acc = 0.0;
    for (int i = 0; i < n; i++) {
        acc += va_arg(ap, double);
    }
    va_end(ap);
    return acc;
}

/* alternating long/double varargs: n is the TOTAL number of varargs.
   reads long, double, long, double, ... summing into a double. */
double vmix2(int n, ...) {
    va_list ap;
    va_start(ap, n);
    double acc = 0.0;
    for (int i = 0; i < n; i++) {
        if ((i & 1) == 0) {
            acc += (double) va_arg(ap, long);
        } else {
            acc += va_arg(ap, double);
        }
    }
    va_end(ap);
    return acc;
}
"#;

// ---------------------------------------------------------------------------
// Tests: integer varargs (AL == 0), increasing counts incl. stack spill
// ---------------------------------------------------------------------------

fn run_vsum_case(test_name: &str, func_name: &str, vals: &[i64], driver_calls: &str) {
    if !x86_64_oracle_enabled(test_name) {
        return;
    }
    let module = build_call_vsum_module(func_name, vals);

    // c_reference: the C equivalent of the trust-cg-generated _call function.
    // It must NOT redefine the variadic callees — those live in the driver so
    // they are present (and identical) on both link paths. Here we only declare
    // `vsum` as extern.
    let mut args_c = String::new();
    for v in vals {
        args_c.push_str(&format!(", {}L", v));
    }
    let c_reference = format!(
        "extern long vsum(int n, ...);\n\
         long {func_name}(void) {{ return vsum({}{}); }}\n",
        vals.len(),
        args_c
    );

    // The driver carries the variadic callees so the trust-cg object (which
    // calls them as undefined externs) links against the same definitions clang
    // uses.
    let driver = format!(
        "#include <stdio.h>\n\
         {VARARGS_CALLEES}\n\
         extern long {func_name}(void);\n\
         int main(void) {{\n{driver_calls}    return 0;\n}}\n"
    );

    let result = x86_64_differential_test(test_name, &module, &c_reference, &driver);
    assert!(
        result.is_ok(),
        "{test_name} failed: {}",
        result.unwrap_err()
    );
}

#[test]
fn test_x86_64_varargs_vsum_zero_args() {
    // vsum(0) -> 0. AL == 0.
    run_vsum_case(
        "varargs_vsum_zero",
        "_call_vsum_zero",
        &[],
        "    printf(\"vsum0=%ld\\n\", _call_vsum_zero());\n",
    );
}

#[test]
fn test_x86_64_varargs_vsum_one_arg() {
    // vsum(1, 7) -> 7. AL == 0.
    run_vsum_case(
        "varargs_vsum_one",
        "_call_vsum_one",
        &[7],
        "    printf(\"vsum1=%ld\\n\", _call_vsum_one());\n",
    );
}

#[test]
fn test_x86_64_varargs_vsum_several_args() {
    // vsum(4, 1, 2, 3, 4) -> 10. All in GPRs (n + 4 = 5 GPR args). AL == 0.
    run_vsum_case(
        "varargs_vsum_several",
        "_call_vsum_several",
        &[1, 2, 3, 4],
        "    printf(\"vsumS=%ld\\n\", _call_vsum_several());\n",
    );
}

#[test]
fn test_x86_64_varargs_vsum_stack_spill() {
    // vsum(10, 1..10) -> 55. n + 10 = 11 integer args; only 6 GPRs exist
    // (RDI..R9), so 5 varargs spill to the overflow stack area. AL == 0.
    // This is the critical stack-placement case.
    run_vsum_case(
        "varargs_vsum_spill",
        "_call_vsum_spill",
        &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
        "    printf(\"vsumSP=%ld\\n\", _call_vsum_spill());\n",
    );
}

#[test]
fn test_x86_64_varargs_vsum_negative_and_large() {
    // Mix of negative and large magnitudes, also spilling to the stack.
    run_vsum_case(
        "varargs_vsum_neg",
        "_call_vsum_neg",
        &[
            -100,
            5_000_000_000,
            -7,
            0,
            42,
            1_000_000_007,
            -2_000_000_000,
            9,
        ],
        "    printf(\"vsumNEG=%ld\\n\", _call_vsum_neg());\n",
    );
}

// ---------------------------------------------------------------------------
// Tests: double varargs (AL > 0), increasing counts incl. XMM exhaustion
// ---------------------------------------------------------------------------

fn run_vmix_case(test_name: &str, func_name: &str, vals: &[f64], driver_calls: &str) {
    if !x86_64_oracle_enabled(test_name) {
        return;
    }
    let module = build_call_vmix_module(func_name, vals);

    let mut args_c = String::new();
    for v in vals {
        // Print with full precision so the C literal round-trips exactly.
        args_c.push_str(&format!(", {:?}", v));
    }
    let c_reference = format!(
        "extern double vmix(int n, ...);\n\
         double {func_name}(void) {{ return vmix({}{}); }}\n",
        vals.len(),
        args_c
    );

    let driver = format!(
        "#include <stdio.h>\n\
         {VARARGS_CALLEES}\n\
         extern double {func_name}(void);\n\
         int main(void) {{\n{driver_calls}    return 0;\n}}\n"
    );

    let result = x86_64_differential_test(test_name, &module, &c_reference, &driver);
    assert!(
        result.is_ok(),
        "{test_name} failed: {}",
        result.unwrap_err()
    );
}

#[test]
fn test_x86_64_varargs_vmix_one_double() {
    // vmix(1, 3.25) -> 3.25. AL == 1.
    run_vmix_case(
        "varargs_vmix_one",
        "_call_vmix_one",
        &[3.25],
        "    printf(\"vmix1=%.4f\\n\", _call_vmix_one());\n",
    );
}

#[test]
fn test_x86_64_varargs_vmix_several_doubles() {
    // vmix(3, 1.5, 2.25, 4.125) -> 7.875. AL == 3.
    run_vmix_case(
        "varargs_vmix_several",
        "_call_vmix_several",
        &[1.5, 2.25, 4.125],
        "    printf(\"vmixS=%.4f\\n\", _call_vmix_several());\n",
    );
}

#[test]
fn test_x86_64_varargs_vmix_xmm_spill() {
    // 10 double varargs: 8 XMM registers (XMM0..XMM7), then 2 spill to stack.
    // AL must saturate at 8 (number of XMM *registers* used, not args).
    run_vmix_case(
        "varargs_vmix_xmm_spill",
        "_call_vmix_xmm_spill",
        &[0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0, 4.5, 5.0],
        "    printf(\"vmixXS=%.4f\\n\", _call_vmix_xmm_spill());\n",
    );
}

// ---------------------------------------------------------------------------
// Test: mixed int + double varargs (the key AL-vs-total-count case)
// ---------------------------------------------------------------------------

#[test]
fn test_x86_64_varargs_vmix2_mixed_int_double() {
    if !x86_64_oracle_enabled("varargs_vmix2_mixed") {
        return;
    }
    let module = build_call_vmix2_module("_call_vmix2");

    // C equivalent: (long) vmix2(4, 10L, 1.5, 20L, 2.5) == 34.
    let c_reference = "extern double vmix2(int n, ...);\n\
         long _call_vmix2(void) { return (long) vmix2(4, 10L, 1.5, 20L, 2.5); }\n";

    let driver = format!(
        "#include <stdio.h>\n\
         {VARARGS_CALLEES}\n\
         extern long _call_vmix2(void);\n\
         int main(void) {{\n    printf(\"vmix2=%ld\\n\", _call_vmix2());\n    return 0;\n}}\n"
    );

    let result = x86_64_differential_test("varargs_vmix2_mixed", &module, c_reference, &driver);
    assert!(
        result.is_ok(),
        "varargs_vmix2_mixed failed: {}",
        result.unwrap_err()
    );
}

// ---------------------------------------------------------------------------
// Test: libc snprintf (real variadic function, AL correctness for %f)
// ---------------------------------------------------------------------------

#[test]
fn test_x86_64_varargs_snprintf_libc() {
    if !x86_64_oracle_enabled("varargs_snprintf") {
        return;
    }
    let module = build_call_snprintf_module("_call_snprintf");

    // C equivalent of the trust-cg function: forward buf+fmt to snprintf with a
    // %d %f %d argument set (AL must be 1 for the single double).
    let c_reference = r#"#include <stdio.h>
long _call_snprintf(char *buf, const char *fmt) {
    return (long) snprintf(buf, 64, fmt, 42, 3.5, 7);
}
"#;

    // The driver supplies the buffer and the format string, calls the trust-cg
    // function, then prints BOTH the returned byte count and the formatted
    // buffer contents. If AL were wrong, the %f field would format garbage and
    // the buffer text (and likely the length) would diverge from clang.
    let driver = r#"#include <stdio.h>
extern long _call_snprintf(char *buf, const char *fmt);
int main(void) {
    char buf[64];
    long n = _call_snprintf(buf, "i=%d f=%.3f j=%d");
    printf("snprintf_len=%ld\n", n);
    printf("snprintf_buf=%s\n", buf);
    return 0;
}
"#;

    let result = x86_64_differential_test("varargs_snprintf", &module, c_reference, driver);
    assert!(
        result.is_ok(),
        "varargs_snprintf failed: {}",
        result.unwrap_err()
    );
}
