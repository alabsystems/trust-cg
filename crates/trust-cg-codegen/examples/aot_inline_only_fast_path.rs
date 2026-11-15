// trust-cg-codegen/examples/aot_inline_only_fast_path.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The object-file twin of `jit_inline_only_fast_path`: a runtime helper's
//! fast path shipped as an inline-only (`AvailableExternally`) body, compiled
//! by `Compiler::compile` (AOT) into an object that a C runtime defining the
//! helper is linked against. The measurement fixture for the AOT half of
//! `docs/jit-inline-only-bodies.md`.
//!
//! `sum(table, n) = Σ_{i<n} tcg_read(table, i & 7)` where `tcg_read` is the
//! runtime's helper (defined by the C file the object is linked with): a
//! bounds check against `table[0]` and a load, else the out-of-line remainder
//! `tcg_read_slow`. The module carries `tcg_read`'s fast path as an
//! inline-only body, so at O1+ the AOT inliner splices it into the loop and
//! the linked definition is called only by code the inliner did not reach.
//! Build the object twice — as is, and with `TCG_NO_INLINE_ONLY_BODIES=1`
//! (every read calls the linked definition) — link each with the same runtime
//! and compare the printed answers (they must be equal) and the instructions
//! retired:
//!
//! ```text
//! scripts/trust_cargo.sh run --release -p trust-cg-codegen \
//!     --example aot_inline_only_fast_path -- on.o 2
//! TCG_NO_INLINE_ONLY_BODIES=1 scripts/trust_cargo.sh run --release -p trust-cg-codegen \
//!     --example aot_inline_only_fast_path -- off.o 2
//! cc -O2 runtime.c on.o -o on && cc -O2 runtime.c off.o -o off
//! /usr/bin/time -l ./on 50000000; /usr/bin/time -l ./off 50000000
//! ```
//!
//! Arguments: the object path to write, the optimization level (0-3,
//! default 2) and the target triple (default: the host's). With `--runtime
//! PATH` it also writes the C runtime (the helper, its remainder, a `main`
//! that runs `sum` over `argv[1]` iterations and checks the answer against the
//! closed-form reference).

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{Target, TargetSpec};
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::{BinOp, Endianness, ICmpOp, Linkage, Module, StructPassingPolicy, TargetInfo, Ty};
use trust_ir_build::ModuleBuilder;

const RUNTIME: &str = r#"#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
static unsigned long long definition_calls, slow_calls;
int64_t tcg_read_slow(const int64_t *table, int64_t index) {
    (void)table;
    slow_calls++;
    return -1000 - index;
}
int64_t tcg_read(const int64_t *table, int64_t index) {
    definition_calls++;
    if ((uint64_t)index < (uint64_t)table[0]) return table[1 + index];
    return tcg_read_slow(table, index);
}
extern int64_t sum(const int64_t *table, int64_t n);
static int64_t reference_read(const int64_t *table, int64_t index) {
    return index < table[0] ? table[1 + index] : -1000 - index;
}
int main(int argc, char **argv) {
    static const int64_t table[6] = {5, 10, 20, 30, 40, 50};
    int64_t n = argc > 1 ? atoll(argv[1]) : 10000000;
    int64_t answer = sum(table, n);
    int64_t period = 0, rest = 0;
    for (int64_t i = 0; i < 8; i++) period += reference_read(table, i);
    for (int64_t i = 0; i < n % 8; i++) rest += reference_read(table, i);
    int64_t expected = (n / 8) * period + rest;
    printf("n=%lld answer=%lld reference=%lld definition_calls=%llu slow_calls=%llu\n",
           (long long)n, (long long)answer, (long long)expected, definition_calls, slow_calls);
    return answer == expected ? 0 : 1;
}
"#;

fn module(triple: &str) -> Module {
    let mut mb = ModuleBuilder::new("aot_inline_only_fast_path");
    let read_ty = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
    let slow = mb.declare_function("tcg_read_slow", read_ty);
    let read = {
        let mut fb = mb.function("tcg_read", read_ty);
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
    let mut module = mb
        .build()
        .expect("ModuleBuilder::build: the example module");
    module.target_info = Some(TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    });
    module
}

fn host_triple() -> &'static str {
    match (std::env::consts::ARCH, std::env::consts::OS) {
        ("aarch64", "macos") => "aarch64-apple-darwin",
        ("aarch64", _) => "aarch64-unknown-linux-gnu",
        ("x86_64", "macos") => "x86_64-apple-darwin",
        _ => "x86_64-unknown-linux-gnu",
    }
}

fn main() {
    let mut runtime_path = None;
    let mut positional = Vec::new();
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        if arg == "--runtime" {
            runtime_path = args.next();
        } else {
            positional.push(arg);
        }
    }
    let mut positional = positional.into_iter();
    let object_path = positional
        .next()
        .expect("usage: aot_inline_only_fast_path OUT.o [OPT] [TRIPLE] [--runtime PATH]");
    let opt_level = match positional.next().as_deref() {
        Some("0") => OptLevel::O0,
        Some("1") => OptLevel::O1,
        Some("3") => OptLevel::O3,
        _ => OptLevel::O2,
    };
    let triple = positional
        .next()
        .unwrap_or_else(|| host_triple().to_string());
    if let Some(path) = runtime_path {
        std::fs::write(&path, RUNTIME).expect("write the C runtime");
    }

    let config = CompilerConfig {
        opt_level,
        target: if triple.starts_with("x86_64") {
            Target::X86_64
        } else {
            Target::Aarch64
        },
        ..CompilerConfig::default()
    };
    let result =
        Compiler::new_for_target_spec(config, TargetSpec::parse(&triple).expect("target triple"))
            .with_codegen_license(permit_unlicensed())
            .compile(&module(&triple))
            .expect("compile");
    std::fs::write(&object_path, &result.object_code).expect("write the object");

    println!(
        "triple={triple} opt_level={opt_level:?} object={object_path} bytes={}",
        result.object_code.len()
    );
    println!(
        "spliced={:?} withheld={:?}",
        result
            .inline_only_bodies
            .spliced
            .iter()
            .map(|u| (u.name.as_str(), u.sites))
            .collect::<Vec<_>>(),
        result
            .inline_only_bodies
            .withheld
            .iter()
            .map(|w| (w.name.as_str(), w.reason.as_str()))
            .collect::<Vec<_>>()
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
