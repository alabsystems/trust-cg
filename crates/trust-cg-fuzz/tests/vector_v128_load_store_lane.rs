// trust-cg-fuzz/tests/vector_v128_load_store_lane.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Regression for DEFECT #7: a 128-bit vector (<2 x i64>, RegClass::Fpr128 /
// IR Type::V128) stored to an alloca'd slot and reloaded must round-trip
// correctly. Before the fix, select_load/select_store fell through a catch-all
// that emitted a scalar 64-bit LDR/STR, dropping the high 64 bits of the
// vector and returning the WRONG lane at O1/O2/O3.
//
// Harness: build a self-contained trust-ir module whose entry fn "fuzz_fn"
//   - takes two i64 params a, b
//   - packs them into a <2 x i64> (lane0 = a, lane1 = b)
//   - stores the vector to an alloca'd V128 slot
//   - loads it back
//   - extracts lane 0
//   - returns it as i64
// The correct result is `a` (the first param) for every input.
//
// O0 is the trusted reference. We assert O1/O2/O3 == O0 == a under both the
// fast and quality register allocators.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{Module as TrustIrModule, Ty};
use trust_ir_build::ModuleBuilder;
// The fixed-width vector shorthands moved to the marked demo module
// (trust-ir 93a418f "quarantine the SIMD/vector demo emitters").
use trust_ir_build::demo::VectorDemoExt;

/// Build a module with entry fn "fuzz_fn" that round-trips a <2 x i64> through
/// an alloca'd vector slot and returns lane 0 (which equals the first param).
fn build_v128_roundtrip_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("v128_load_store_lane");
    let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", ty);

    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I64);
    let b = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);

    // Build <2 x i64> { lane0 = a, lane1 = b }.
    let vec = fb
        .v2_i64_pack_lanes([a, b])
        .expect("v2_i64 pack_lanes builds");

    // Store the vector to an alloca'd 128-bit slot, then reload it.
    let slot = fb.alloca(Ty::v2_i64());
    fb.store(Ty::v2_i64(), slot, vec);
    let reloaded = fb.load(Ty::v2_i64(), slot);

    // Extract lane 0 — must equal `a`.
    let lane0 = fb
        .v2_i64_extract_lane(reloaded, 0)
        .expect("v2_i64 extract_lane 0 builds");

    fb.ret(vec![lane0]);
    fb.build();
    mb.build()
}

type FuzzFn = extern "C" fn(i64, i64) -> i64;

/// Compile `module`'s "fuzz_fn" at `opt` with the given allocator and run it on
/// `(a, b)`. Returns the i64 result.
fn compile_and_run(
    module: &TrustIrModule,
    opt: OptLevel,
    fast_regalloc: bool,
    a: i64,
    b: i64,
) -> i64 {
    let mut config = if fast_regalloc {
        CompilerConfig::jit_fast(Target::host())
    } else {
        let mut c = CompilerConfig::for_host_jit();
        c.enable_jit_fast_regalloc = false;
        c
    };
    config.opt_level = opt;

    let compiler = Compiler::new(config);
    let externs: HashMap<String, *const u8> = HashMap::new();
    let result = compiler
        .compile_module_to_jit(module, &externs)
        .unwrap_or_else(|e| {
            panic!(
                "compile fuzz_fn at {:?} (fast_regalloc={}) failed: {}",
                opt, fast_regalloc, e
            )
        });
    let f = unsafe {
        result
            .buffer
            .get_fn_bound::<FuzzFn>("fuzz_fn")
            .expect("fuzz_fn symbol present")
    }
    .into_inner();
    f(a, b)
}

#[test]
fn v128_load_store_returns_first_lane_all_opt_levels_both_allocators() {
    let module = build_v128_roundtrip_module();

    // Diverse inputs, including values whose high/low 64-bit halves differ so a
    // scalar 64-bit load that drops the high lane would still be caught by the
    // lane-0 read AND by comparing against O0.
    let rows: [(i64, i64); 6] = [
        (1, 2),
        (0x1122_3344_5566_7788, 0x99AA_BBCC_DDEE_FF00u64 as i64),
        (-1, 0),
        (0, -1),
        (i64::MIN, i64::MAX),
        (0x7FFF_FFFF_FFFF_FFFF, -42),
    ];

    for (a, b) in rows {
        // O0 is the trusted reference.
        let o0_fast = compile_and_run(&module, OptLevel::O0, true, a, b);
        let o0_quality = compile_and_run(&module, OptLevel::O0, false, a, b);

        // Hand-written reference: lane 0 of {a, b} is `a`.
        let reference = a;

        assert_eq!(
            o0_fast, reference,
            "O0 fast-regalloc fuzz_fn({a:#x}, {b:#x}) must return lane 0 == {a:#x}"
        );
        assert_eq!(
            o0_quality, reference,
            "O0 quality-regalloc fuzz_fn({a:#x}, {b:#x}) must return lane 0 == {a:#x}"
        );

        for opt in [OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let fast = compile_and_run(&module, opt, true, a, b);
            let quality = compile_and_run(&module, opt, false, a, b);

            assert_eq!(
                fast, o0_fast,
                "{opt:?} fast-regalloc fuzz_fn({a:#x}, {b:#x}) = {fast:#x} must match O0 = {o0_fast:#x}"
            );
            assert_eq!(
                quality, o0_quality,
                "{opt:?} quality-regalloc fuzz_fn({a:#x}, {b:#x}) = {quality:#x} must match O0 = {o0_quality:#x}"
            );
        }
    }
}
