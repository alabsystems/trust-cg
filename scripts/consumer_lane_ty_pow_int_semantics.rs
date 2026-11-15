// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Consumer-lane test target (ledger L13-P8), copied by
//! `scripts/check_darwin_consumers.py` into an exported TY tree as
//! `crates/tla-trust-cg/tests/trust_cg_lane_pow_int_semantics.rs`; it is never
//! part of a TY checkout.
//!
//! TY's own `pow_int_typed_native` test panics at its second case: it expects
//! `0^0 == 1`, while TY's PowInt lowering sends `0^0` to its TypeMismatch
//! runtime error on purpose ("TLC: 0^0 is undefined",
//! `crates/tla-ir/src/lower/arithmetic.rs`). Every later assertion of that test
//! therefore never runs. This target compiles the same certified predicate
//! (`state[0] ^ state[1] == state[2]`, helpers copied verbatim from TY's test
//! at the lane's pin) through trust-cg and checks TY's lowering semantics
//! natively: ordinary powers, `x^0`, `0^n`, the `i64::MIN` boundary, the u32
//! exponent domain, negative exponents, `0^0` and checked overflow.

#![cfg(feature = "native")]

use tla_jit_abi::{JitCallOut, JitRuntimeErrorKind, JitStatus};
use tla_tir::bytecode::{BytecodeFunction, Opcode};
use tla_trust_cg::{
    BatchJitOptions, TrustCgNativeCallableCompileTask, TrustCgNativeCallableExport,
    TrustCgNativeStatePredicateExport,
};

const SYMBOL: &str = "pow_int_typed_native_predicate";

fn compile_pow_predicate() -> TrustCgNativeStatePredicateExport {
    // The predicate evaluates state[0] ^ state[1] == state[2]. Keeping all
    // three operands in the input state exercises one compiled native loop
    // across success, exponent-domain, and overflow cases.
    let mut function = BytecodeFunction::new(SYMBOL.to_owned(), 0);
    function.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    function.emit(Opcode::LoadVar { rd: 1, var_idx: 1 });
    function.emit(Opcode::PowInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    function.emit(Opcode::LoadVar { rd: 3, var_idx: 2 });
    function.emit(Opcode::Eq {
        rd: 4,
        r1: 2,
        r2: 3,
    });
    function.emit(Opcode::Ret { rs: 4 });

    let certified = tla_ir::lower::lower_invariant_certified(
        &function,
        SYMBOL,
        tla_ir::lower::LoweringOptions::new(),
    )
    .expect("PowInt state predicate must lower with semantic ABI authority");
    let export = tla_trust_cg::compile_native_callable_export(
        TrustCgNativeCallableCompileTask::new(&certified, BatchJitOptions::default()),
    )
    .expect("lowering-certified PowInt predicate must compile natively");

    let TrustCgNativeCallableExport::StatePredicate(export) = export else {
        panic!("state-predicate certificate must publish only a state-predicate wrapper");
    };
    assert_eq!(export.symbol_name(), SYMBOL);
    export
}

fn evaluate(export: &TrustCgNativeStatePredicateExport, state: [i64; 3]) -> JitCallOut {
    // SAFETY: `export` remains live for the call. The exact cached address is
    // re-proved against its published symbol below, and execute mode is entered
    // immediately before invoking the state-predicate ABI with a valid slice.
    let function = unsafe { export.function() };
    export
        .library()
        .ensure_published_symbol_ptr(
            export.symbol_name(),
            function as *const () as *mut std::ffi::c_void,
        )
        .expect("typed PowInt pointer must remain the exact published symbol");

    let mut out = JitCallOut::default();
    tla_trust_cg::ensure_jit_execute_mode();
    // SAFETY: `state` contains the three i64 slots read by the certified
    // StatePredicateV1 entry, and `out` is valid for the duration of the call.
    unsafe { function(&mut out, state.as_ptr(), state.len() as u32) };
    out
}

#[test]
fn lane_pow_int_matches_ty_lowering_semantics_natively() {
    let export = compile_pow_predicate();
    let max_exponent = i64::from(u32::MAX);

    // The predicate holds: status Ok, value 1.
    for (state, label) in [
        ([2, 10, 1_024], "ordinary power"),
        ([3, 1, 3], "first power"),
        ([-3, 3, -27], "odd power of a negative base"),
        ([5, 0, 1], "nonzero base to the zero power"),
        ([-1, 0, 1], "negative base to the zero power"),
        ([0, 1, 0], "zero to the first power"),
        ([0, 2, 0], "zero to the second power"),
        ([2, 62, 1_i64 << 62], "largest positive power of two"),
        ([-2, 63, i64::MIN], "signed minimum boundary"),
        ([1, max_exponent, 1], "largest exponent in the u32 domain"),
        ([-1, max_exponent, -1], "odd largest exponent of minus one"),
    ] {
        let out = evaluate(&export, state);
        assert_eq!(out.status, JitStatus::Ok, "{label}: {out:?}");
        assert_eq!(out.value, 1, "{label} must satisfy the predicate: {out:?}");
    }

    // The predicate is evaluated, not assumed: a wrong expected value is false.
    let wrong = evaluate(&export, [2, 10, 1_023]);
    assert_eq!(
        wrong.status,
        JitStatus::Ok,
        "wrong expected value: {wrong:?}"
    );
    assert_eq!(wrong.value, 0, "2^10 == 1023 must be false: {wrong:?}");

    // TY's lowering: 0^0, a negative exponent and an exponent above the u32
    // domain are TypeMismatch runtime errors.
    for (state, label) in [
        ([0, 0, 1], "zero to the zero power"),
        ([0, 0, 0], "zero to the zero power, either expectation"),
        ([2, -1, 0], "negative exponent"),
        ([1, max_exponent + 1, 1], "exponent above the u32 domain"),
    ] {
        let out = evaluate(&export, state);
        assert_eq!(out.status, JitStatus::RuntimeError, "{label}: {out:?}");
        assert_eq!(
            out.err_kind,
            JitRuntimeErrorKind::TypeMismatch,
            "{label}: {out:?}"
        );
    }

    // A result outside i64 is a checked ArithmeticOverflow, never a wrapped value.
    for (state, label) in [
        ([2, 63, 0], "2^63"),
        ([-2, 64, 0], "(-2)^64"),
        ([3, 40, 0], "3^40"),
        ([i64::MAX, 2, 0], "i64::MAX squared"),
    ] {
        let out = evaluate(&export, state);
        assert_eq!(out.status, JitStatus::RuntimeError, "{label}: {out:?}");
        assert_eq!(
            out.err_kind,
            JitRuntimeErrorKind::ArithmeticOverflow,
            "{label}: {out:?}"
        );
    }
}
