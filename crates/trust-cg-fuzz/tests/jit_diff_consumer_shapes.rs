// trust-cg-fuzz/tests/jit_diff_consumer_shapes.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Part of #797.

// The jit_diff harness is unix-only (its per-invoke sandbox is a POSIX fork);
// mirror that gate here so the test compiles out cleanly on non-unix hosts
// rather than failing to resolve `trust_cg_fuzz::jit_diff`.
#![cfg(all(unix, any(target_arch = "aarch64", target_arch = "x86_64")))]

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_fuzz::jit_diff::{
    ConsumerJitOutcome, compile_and_run_consumer_shape, diff_consumer_shape_row,
    run_consumer_shape_oracle,
};
use trust_cg_fuzz::trust_ir_gen::gen_consumer_shape_module;

fn assert_consumer_row(module: &trust_ir::Module, row: [i64; 4]) {
    let expected = run_consumer_shape_oracle(&row);
    for opt in [OptLevel::O0, OptLevel::O2, OptLevel::O3] {
        let actual = compile_and_run_consumer_shape(module, opt, &row);
        match actual {
            ConsumerJitOutcome::Value(snapshot) => assert_eq!(
                snapshot, expected,
                "consumer row must match scalar oracle at {:?}",
                opt
            ),
            other => panic!("consumer row must JIT at {:?}, got {:?}", opt, other),
        }
    }
    assert!(
        diff_consumer_shape_row(module, &row).is_none(),
        "diff lane must accept matching row"
    );
}

#[test]
fn consumer_shape_jit_matches_scalar_status_oracle() {
    let module = gen_consumer_shape_module(797);

    assert_consumer_row(&module, [3, 4, 0, 7]);
    assert_consumer_row(&module, [-5, 9, 4, 7]);
    assert_consumer_row(&module, [11, -2, 5, 7]);
    assert_consumer_row(&module, [1, 2, 3, 6]);
}
