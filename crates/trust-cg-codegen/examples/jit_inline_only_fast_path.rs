// trust-cg-codegen/examples/jit_inline_only_fast_path.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A runtime helper's fast path shipped as an inline-only
//! (`AvailableExternally`) body, compiled by `Compiler::compile_module_to_jit`
//! and run in a loop: the measurement fixture for
//! `docs/jit-inline-only-bodies.md`.
//!
//! `sum(table, n) = Σ_{i<n} read(table, i & 7)` where `read` is the runtime's
//! helper (a host function bound through the extern map): a bounds check
//! against `table[0]` and a load, else the out-of-line remainder `read_slow`.
//! The module carries `read`'s fast path as an inline-only body, so at O1+ the
//! JIT splices it into the loop and calls the host only for out-of-range
//! reads. Run it twice under `/usr/bin/time -l` — as is, and with
//! `TCG_NO_JIT_LIR_PREPARE=1` (every read calls the host definition) — and
//! compare the printed answers (they must be equal) and the instructions
//! retired:
//!
//! ```text
//! scripts/trust_cargo.sh build --release -p trust-cg-codegen --example jit_inline_only_fast_path
//! /usr/bin/time -l target/release/examples/jit_inline_only_fast_path 2 50000000
//! TCG_NO_JIT_LIR_PREPARE=1 /usr/bin/time -l target/release/examples/jit_inline_only_fast_path 2 50000000
//! ```
//!
//! Arguments: optimization level (0-3, default 2) and iteration count
//! (default 10,000,000).

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::{BinOp, ICmpOp, Linkage, Module, Ty};
use trust_ir_build::ModuleBuilder;

static DEFINITION_CALLS: AtomicU64 = AtomicU64::new(0);
static SLOW_CALLS: AtomicU64 = AtomicU64::new(0);

extern "C" fn host_read_slow(_table: *const i64, index: i64) -> i64 {
    SLOW_CALLS.fetch_add(1, Ordering::Relaxed);
    -1000 - index
}

extern "C" fn host_read(table: *const i64, index: i64) -> i64 {
    DEFINITION_CALLS.fetch_add(1, Ordering::Relaxed);
    // SAFETY: word 0 of the table is its length.
    let len = unsafe { *table };
    if (index as u64) < (len as u64) {
        // SAFETY: bounds-checked above.
        unsafe { *table.add(1 + index as usize) }
    } else {
        host_read_slow(table, index)
    }
}

fn module() -> Module {
    let mut mb = ModuleBuilder::new("jit_inline_only_fast_path");
    let read_ty = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
    let slow = mb.declare_function("read_slow", read_ty);
    let read = {
        let mut fb = mb.function("read", read_ty);
        fb.set_linkage(Linkage::AvailableExternally);
        let entry = fb.create_block();
        let table = fb.add_block_param(entry, Ty::Ptr);
        let index = fb.add_block_param(entry, Ty::I64);
        let fast = fb.create_block();
        let slow_block = fb.create_block();
        fb.switch_to_block(entry);
        let len = fb.load(Ty::I64, table);
        let in_range = fb.icmp(ICmpOp::Ult, Ty::I64, index, len);
        fb.condbr(in_range, fast, vec![], slow_block, vec![]);
        fb.switch_to_block(fast);
        let one = fb.iconst(Ty::I64, 1);
        let slot = fb.add(Ty::I64, index, one);
        let element = fb.gep(Ty::I64, table, vec![slot]);
        let value = fb.load(Ty::I64, element);
        fb.ret(vec![value]);
        fb.switch_to_block(slow_block);
        let rest = fb.call(slow, vec![table, index]);
        fb.ret(vec![rest]);
        fb.build()
    };
    {
        let mut fb = mb.function("sum", read_ty);
        let entry = fb.create_block();
        let table = fb.add_block_param(entry, Ty::Ptr);
        let n = fb.add_block_param(entry, Ty::I64);
        let header = fb.create_block();
        let i = fb.add_block_param(header, Ty::I64);
        let acc = fb.add_block_param(header, Ty::I64);
        let body = fb.create_block();
        let exit = fb.create_block();
        let result = fb.add_block_param(exit, Ty::I64);
        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::I64, 0);
        fb.br(header, vec![zero, zero]);
        fb.switch_to_block(header);
        let more = fb.icmp(ICmpOp::Ult, Ty::I64, i, n);
        fb.condbr(more, body, vec![], exit, vec![acc]);
        fb.switch_to_block(body);
        let seven = fb.iconst(Ty::I64, 7);
        let index = fb.binop(BinOp::And, Ty::I64, i, seven);
        let value = fb.call(read, vec![table, index]);
        let next_acc = fb.add(Ty::I64, acc, value);
        let one = fb.iconst(Ty::I64, 1);
        let next_i = fb.add(Ty::I64, i, one);
        fb.br(header, vec![next_i, next_acc]);
        fb.switch_to_block(exit);
        fb.ret(vec![result]);
        fb.build();
    }
    mb.build()
        .expect("ModuleBuilder::build: the example module")
}

fn main() {
    let mut args = std::env::args().skip(1);
    let opt_level = match args.next().as_deref() {
        Some("0") => OptLevel::O0,
        Some("1") => OptLevel::O1,
        Some("3") => OptLevel::O3,
        _ => OptLevel::O2,
    };
    let n: i64 = args
        .next()
        .and_then(|s| s.parse().ok())
        .unwrap_or(10_000_000);

    let mut config = CompilerConfig::jit_fast(Target::try_host().expect("an in-process JIT host"));
    config.opt_level = opt_level;
    let externs = HashMap::from([
        ("read".to_string(), host_read as *const u8),
        ("read_slow".to_string(), host_read_slow as *const u8),
    ]);
    let result = Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(&module(), &externs)
        .expect("compile_module_to_jit");
    let sum: extern "C" fn(*const i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("sum")
            .expect("sum symbol")
            .into_inner()
    };
    let table: [i64; 6] = [5, 10, 20, 30, 40, 50];
    let answer = sum(table.as_ptr(), n);

    // The reference, in closed form (so the process's instruction count is
    // the JIT'd loop's plus compile): the definition's own semantics over one
    // period of `i & 7`, times the full periods, plus the remainder.
    let read = |index: i64| {
        if index < table[0] {
            table[1 + index as usize]
        } else {
            -1000 - index
        }
    };
    let period: i64 = (0..8).map(read).sum();
    let expected = (n / 8) * period + (0..n % 8).map(read).sum::<i64>();
    assert_eq!(answer, expected, "inlined and called answers must agree");

    println!("opt_level={opt_level:?} n={n}");
    println!("answer={answer} (reference {expected})");
    println!(
        "definition_calls={} slow_calls={}",
        DEFINITION_CALLS.load(Ordering::Relaxed),
        SLOW_CALLS.load(Ordering::Relaxed)
    );
    println!(
        "spliced={:?} withheld={}",
        result
            .inline_only_bodies
            .spliced
            .iter()
            .map(|u| (u.name.as_str(), u.sites))
            .collect::<Vec<_>>(),
        result.inline_only_bodies.withheld.len()
    );
    for premise in result.inline_only_bodies.premises() {
        println!("premise: {premise}");
    }
}

/// The module it compiles is hand-built and carries no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). This example states `Permit` explicitly.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
