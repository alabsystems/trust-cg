// trust-cg-codegen/tests/ty_parent_loop_aot_x86_64.rs - loop-bearing TY BFS
// parent-loop kernels through the x86-64 AOT path, linked and executed.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// WHY THIS TARGET EXISTS. On x86-64 the TY parent-loop kernels
// (`ty_native_bfs_no_action_parent_loop`, `ty_bfs_minimal_o1_o3_summary`) are
// compiled only through the in-process JIT, whose proof-carrying publication
// gate refuses them before any generated code runs. The only TY code that
// executes on x86-64 is the straight-line `ty_bfs_minimal` kernel. This target
// drives the same two loop-bearing modules through `Compiler::compile`
// (lowering -> optimization -> regalloc -> encoding -> ELF), links each object
// with the host `cc` and executes it at O0-O3 against a Rust reference.
//
// EVIDENCE BOUNDARY. This is an executed differential test over a handful of
// inputs. It is not proof evidence, it does not go through the JIT
// publication gate, and it says nothing about that gate's refusals.
//
// The objects are left under `CARGO_TARGET_TMPDIR/ty_parent_loop_aot/` so a
// runtime or instruction-count measurement can link the same bytes.

#![cfg(all(target_arch = "x86_64", target_os = "linux"))]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{BinOp, ICmpOp, Ty, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

const NO_ACTION_ENTRY: &str = "ty_native_bfs_no_action_parent_loop";
const NO_ACTION_SEED: u64 = 7;
const NO_ACTION_PRIME: u64 = 131;

const MINIMAL_ENTRY: &str = "ty_bfs_minimal_o1_o3_summary";
const FINGERPRINT_SEED: u64 = 0x6d2b_79f5_aa17_6620;
const PARENT_DIGEST_SEED: u64 = 0x9e37_79b9_6620_0001;
const IDX_PRIME: u64 = 0x0000_0000_85eb_ca6b;
const GENERATED_PRIME: u64 = 0x0000_0100_0000_01b3;
const PARENT_DIGEST_PRIME: u64 = 0x0000_0000_c2b2_ae35;
const FINGERPRINT_PARENT_PRIME: u64 = 0xff51_afd7_ed55_8ccd;
const FINGERPRINT_PRIME: u64 = 0x0000_0001_65b1_e9dd;

/// Parent counts every kernel is executed on. Zero is the not-taken loop, one
/// the single trip, and 1000 runs the loop body enough to exercise any
/// unrolled or strength-reduced form with a remainder.
const PARENT_COUNTS: [u64; 6] = [0, 1, 2, 7, 64, 1000];

fn store_summary_slot(fb: &mut FunctionBuilder<'_>, out: ValueId, slot: u64, value: ValueId) {
    let slot = fb.iconst(Ty::U64, i128::from(slot));
    let ptr = fb.gep(Ty::U64, out, vec![slot]);
    fb.store(Ty::U64, ptr, value);
}

/// The module of `ty_native_bfs_no_action_parent_loop.rs`, with plain stores
/// for every summary slot (that file's `Aligned(16)` claim on slot 0 is about
/// the JIT certificate lane and is not made here).
fn build_no_action_parent_loop_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new(NO_ACTION_ENTRY);
    let entry_ty = mb.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::Ptr], vec![Ty::U64]);
    {
        let mut fb = mb.function(NO_ACTION_ENTRY, entry_ty);

        let entry = fb.create_block();
        let parents = fb.add_block_param(entry, Ty::Ptr);
        let parent_count = fb.add_block_param(entry, Ty::U64);
        let out = fb.add_block_param(entry, Ty::Ptr);

        let header = fb.create_block();
        let idx = fb.add_block_param(header, Ty::U64);
        let state_count = fb.add_block_param(header, Ty::U64);
        let generated = fb.add_block_param(header, Ty::U64);
        let last_parent = fb.add_block_param(header, Ty::U64);
        let fingerprint = fb.add_block_param(header, Ty::U64);
        let status = fb.add_block_param(header, Ty::U64);

        let body = fb.create_block();
        let done = fb.create_block();
        let done_state_count = fb.add_block_param(done, Ty::U64);
        let done_generated = fb.add_block_param(done, Ty::U64);
        let done_last_parent = fb.add_block_param(done, Ty::U64);
        let done_fingerprint = fb.add_block_param(done, Ty::U64);
        let done_status = fb.add_block_param(done, Ty::U64);

        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::U64, 0);
        let seed = fb.iconst(Ty::U64, i128::from(NO_ACTION_SEED));
        fb.br(header, vec![zero, zero, zero, zero, seed, zero]);

        fb.switch_to_block(header);
        let has_parent = fb.icmp(ICmpOp::Ult, Ty::U64, idx, parent_count);
        fb.condbr(
            has_parent,
            body,
            vec![],
            done,
            vec![state_count, generated, last_parent, fingerprint, status],
        );

        fb.switch_to_block(body);
        let parent_ptr = fb.gep(Ty::U64, parents, vec![idx]);
        let parent = fb.load(Ty::U64, parent_ptr);
        let one = fb.iconst(Ty::U64, 1);
        let next_idx = fb.binop(BinOp::Add, Ty::U64, idx, one);
        let next_state_count = fb.binop(BinOp::Add, Ty::U64, state_count, one);
        let mixed = fb.binop(BinOp::Xor, Ty::U64, fingerprint, parent);
        let prime = fb.iconst(Ty::U64, i128::from(NO_ACTION_PRIME));
        let mixed = fb.binop(BinOp::Mul, Ty::U64, mixed, prime);
        let next_fingerprint = fb.binop(BinOp::Add, Ty::U64, mixed, next_state_count);
        fb.br(
            header,
            vec![
                next_idx,
                next_state_count,
                generated,
                parent,
                next_fingerprint,
                status,
            ],
        );

        fb.switch_to_block(done);
        store_summary_slot(&mut fb, out, 0, done_state_count);
        store_summary_slot(&mut fb, out, 1, done_generated);
        store_summary_slot(&mut fb, out, 2, done_last_parent);
        store_summary_slot(&mut fb, out, 3, done_fingerprint);
        store_summary_slot(&mut fb, out, 4, done_status);
        fb.ret(vec![done_status]);

        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn no_action_reference(parents: &[u64]) -> [u64; 5] {
    let (mut state_count, mut last_parent, mut fingerprint) = (0u64, 0u64, NO_ACTION_SEED);
    for &parent in parents {
        state_count = state_count.wrapping_add(1);
        last_parent = parent;
        fingerprint = (fingerprint ^ parent)
            .wrapping_mul(NO_ACTION_PRIME)
            .wrapping_add(state_count);
    }
    [state_count, 0, last_parent, fingerprint, 0]
}

/// The module of `ty_bfs_minimal_o1_o3_summary.rs`.
fn build_minimal_parent_loop_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new(MINIMAL_ENTRY);
    let entry_ty = mb.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::Ptr], vec![Ty::U64]);
    {
        let mut fb = mb.function(MINIMAL_ENTRY, entry_ty);

        let entry = fb.create_block();
        let parents = fb.add_block_param(entry, Ty::Ptr);
        let parent_count = fb.add_block_param(entry, Ty::U64);
        let summary = fb.add_block_param(entry, Ty::Ptr);

        let header = fb.create_block();
        let idx = fb.add_block_param(header, Ty::U64);
        let state_count = fb.add_block_param(header, Ty::U64);
        let generated_count = fb.add_block_param(header, Ty::U64);
        let parent_digest = fb.add_block_param(header, Ty::U64);
        let fingerprint = fb.add_block_param(header, Ty::U64);
        let status = fb.add_block_param(header, Ty::U64);

        let body = fb.create_block();
        let done = fb.create_block();
        let done_state_count = fb.add_block_param(done, Ty::U64);
        let done_generated_count = fb.add_block_param(done, Ty::U64);
        let done_parent_digest = fb.add_block_param(done, Ty::U64);
        let done_fingerprint = fb.add_block_param(done, Ty::U64);
        let done_status = fb.add_block_param(done, Ty::U64);

        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::U64, 0);
        let fingerprint_seed = fb.iconst(Ty::U64, i128::from(FINGERPRINT_SEED));
        let parent_digest_seed = fb.iconst(Ty::U64, i128::from(PARENT_DIGEST_SEED));
        fb.br(
            header,
            vec![zero, zero, zero, parent_digest_seed, fingerprint_seed, zero],
        );

        fb.switch_to_block(header);
        let has_parent = fb.icmp(ICmpOp::Ult, Ty::U64, idx, parent_count);
        fb.condbr(
            has_parent,
            body,
            vec![],
            done,
            vec![
                state_count,
                generated_count,
                parent_digest,
                fingerprint,
                status,
            ],
        );

        fb.switch_to_block(body);
        let parent_ptr = fb.gep(Ty::U64, parents, vec![idx]);
        let parent = fb.load(Ty::U64, parent_ptr);
        let one = fb.iconst(Ty::U64, 1);
        let next_idx = fb.binop(BinOp::Add, Ty::U64, idx, one);
        let next_state_count = fb.binop(BinOp::Add, Ty::U64, state_count, one);
        let next_generated_count = fb.binop(BinOp::Add, Ty::U64, generated_count, one);

        let idx_prime = fb.iconst(Ty::U64, i128::from(IDX_PRIME));
        let idx_term = fb.binop(BinOp::Mul, Ty::U64, idx, idx_prime);
        let generated_prime = fb.iconst(Ty::U64, i128::from(GENERATED_PRIME));
        let generated_term = fb.binop(BinOp::Mul, Ty::U64, next_generated_count, generated_prime);
        let parent_mix = fb.binop(BinOp::Xor, Ty::U64, parent, idx_term);
        let parent_mix = fb.binop(BinOp::Xor, Ty::U64, parent_mix, generated_term);
        let parent_xor = fb.binop(BinOp::Xor, Ty::U64, parent_digest, parent_mix);
        let parent_digest_prime = fb.iconst(Ty::U64, i128::from(PARENT_DIGEST_PRIME));
        let parent_scaled = fb.binop(BinOp::Mul, Ty::U64, parent_xor, parent_digest_prime);
        let next_parent_digest = fb.binop(BinOp::Add, Ty::U64, parent_scaled, next_state_count);

        let fingerprint_parent_prime = fb.iconst(Ty::U64, i128::from(FINGERPRINT_PARENT_PRIME));
        let parent_fingerprint_term =
            fb.binop(BinOp::Mul, Ty::U64, parent, fingerprint_parent_prime);
        let fingerprint_xor = fb.binop(BinOp::Xor, Ty::U64, fingerprint, next_parent_digest);
        let fingerprint_with_parent = fb.binop(
            BinOp::Add,
            Ty::U64,
            fingerprint_xor,
            parent_fingerprint_term,
        );
        let fingerprint_with_idx = fb.binop(BinOp::Add, Ty::U64, fingerprint_with_parent, idx);
        let fingerprint_prime = fb.iconst(Ty::U64, i128::from(FINGERPRINT_PRIME));
        let fingerprint_scaled =
            fb.binop(BinOp::Mul, Ty::U64, fingerprint_with_idx, fingerprint_prime);
        let next_fingerprint = fb.binop(
            BinOp::Add,
            Ty::U64,
            fingerprint_scaled,
            next_generated_count,
        );

        let status_delta = fb.binop(BinOp::Sub, Ty::U64, next_generated_count, next_state_count);
        let next_status = fb.binop(BinOp::Add, Ty::U64, status, status_delta);

        fb.br(
            header,
            vec![
                next_idx,
                next_state_count,
                next_generated_count,
                next_parent_digest,
                next_fingerprint,
                next_status,
            ],
        );

        fb.switch_to_block(done);
        store_summary_slot(&mut fb, summary, 0, done_state_count);
        store_summary_slot(&mut fb, summary, 1, done_generated_count);
        store_summary_slot(&mut fb, summary, 2, done_parent_digest);
        store_summary_slot(&mut fb, summary, 3, done_fingerprint);
        store_summary_slot(&mut fb, summary, 4, done_status);
        fb.ret(vec![done_status]);

        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn minimal_reference(parents: &[u64]) -> [u64; 5] {
    let (mut state_count, mut generated_count) = (0u64, 0u64);
    let (mut parent_digest, mut fingerprint, mut status) =
        (PARENT_DIGEST_SEED, FINGERPRINT_SEED, 0u64);
    for (idx, &parent) in parents.iter().enumerate() {
        let idx = idx as u64;
        state_count = state_count.wrapping_add(1);
        generated_count = generated_count.wrapping_add(1);
        let parent_mix =
            parent ^ idx.wrapping_mul(IDX_PRIME) ^ generated_count.wrapping_mul(GENERATED_PRIME);
        parent_digest = (parent_digest ^ parent_mix)
            .wrapping_mul(PARENT_DIGEST_PRIME)
            .wrapping_add(state_count);
        fingerprint = (fingerprint ^ parent_digest)
            .wrapping_add(parent.wrapping_mul(FINGERPRINT_PARENT_PRIME))
            .wrapping_add(idx)
            .wrapping_mul(FINGERPRINT_PRIME)
            .wrapping_add(generated_count);
        status = status.wrapping_add(generated_count.wrapping_sub(state_count));
    }
    [
        state_count,
        generated_count,
        parent_digest,
        fingerprint,
        status,
    ]
}

/// The parent array both the C driver and the reference use: a splitmix64
/// stream, so the values exercise all 64 bits.
fn parent_stream(count: u64) -> Vec<u64> {
    let mut state = 0x243f_6a88_85a3_08d3u64;
    (0..count)
        .map(|_| {
            state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = state;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        })
        .collect()
}

/// `driver COUNT [REPS]` fills the same splitmix64 parent array, calls the
/// kernel REPS times (default 1) and prints the return value and the five
/// summary slots of the last call. REPS exists for runtime measurement.
fn c_driver(entry: &str) -> String {
    format!(
        r#"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

extern uint64_t {entry}(const uint64_t *parents, uint64_t count, uint64_t *out);

int main(int argc, char **argv) {{
    uint64_t count = argc > 1 ? strtoull(argv[1], 0, 10) : 0;
    uint64_t reps = argc > 2 ? strtoull(argv[2], 0, 10) : 1;
    uint64_t *parents = malloc((count + 1) * sizeof(uint64_t));
    uint64_t state = 0x243f6a8885a308d3ull;
    for (uint64_t i = 0; i < count; i++) {{
        state += 0x9e3779b97f4a7c15ull;
        uint64_t z = state;
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ull;
        z = (z ^ (z >> 27)) * 0x94d049bb133111ebull;
        parents[i] = z ^ (z >> 31);
    }}
    uint64_t slots[5];
    uint64_t ret = 0;
    for (uint64_t r = 0; r < reps; r++) {{
        for (int i = 0; i < 5; i++) slots[i] = ~0ull;
        ret = {entry}(parents, count, slots);
    }}
    printf("%llu %llu %llu %llu %llu %llu\n", (unsigned long long)ret,
           (unsigned long long)slots[0], (unsigned long long)slots[1],
           (unsigned long long)slots[2], (unsigned long long)slots[3],
           (unsigned long long)slots[4]);
    return 0;
}}
"#
    )
}

fn out_dir() -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("ty_parent_loop_aot");
    fs::create_dir_all(&dir).expect("create output dir");
    dir
}

fn opt_name(opt_level: OptLevel) -> &'static str {
    match opt_level {
        OptLevel::O0 => "O0",
        OptLevel::O1 => "O1",
        OptLevel::O2 => "O2",
        OptLevel::O3 => "O3",
    }
}

fn compile_object(module: &trust_ir::Module, opt_level: OptLevel) -> Vec<u8> {
    // As the TY ahead-of-time driver compiles: no proof certificates, and the
    // certificate-free allocation requested.
    let bytes = Compiler::new(CompilerConfig {
        opt_level,
        target: Target::X86_64,
        x86_certificate_free_allocation: true,
        ..CompilerConfig::default()
    })
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .unwrap_or_else(|err| panic!("{opt_level:?} AOT compile failed: {err:?}"))
    .object_code;
    assert_eq!(&bytes[..4], b"\x7fELF", "{opt_level:?}: not an ELF object");
    bytes
}

fn run_kernel(
    entry: &str,
    module: &trust_ir::Module,
    reference: fn(&[u64]) -> [u64; 5],
    opt_level: OptLevel,
) {
    let dir = out_dir();
    let stem = format!("{entry}_{}", opt_name(opt_level));
    let obj = dir.join(format!("{stem}.o"));
    fs::write(&obj, compile_object(module, opt_level)).expect("write object");
    let driver = dir.join(format!("{entry}_driver.c"));
    fs::write(&driver, c_driver(entry)).expect("write driver");
    let binary = dir.join(&stem);
    let link = Command::new("cc")
        .arg("-O1")
        .arg("-o")
        .arg(&binary)
        .arg(&driver)
        .arg(&obj)
        .arg("-no-pie")
        .output()
        .expect("the executed leg needs the host cc");
    assert!(
        link.status.success(),
        "{stem}: link failed: {}",
        String::from_utf8_lossy(&link.stderr)
    );

    for count in PARENT_COUNTS {
        let run = Command::new(&binary)
            .arg(count.to_string())
            .output()
            .expect("run kernel binary");
        assert!(run.status.success(), "{stem}: count={count} exited {run:?}");
        let slots = reference(&parent_stream(count));
        let expected = format!(
            "{} {} {} {} {} {}\n",
            slots[4], slots[0], slots[1], slots[2], slots[3], slots[4]
        );
        assert_eq!(
            String::from_utf8_lossy(&run.stdout),
            expected,
            "{stem}: summary diverged from the reference at count={count}"
        );
    }
}

const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

#[test]
fn no_action_parent_loop_aot_matches_reference_o0_o3() {
    let module = build_no_action_parent_loop_module();
    for opt_level in OPT_LEVELS {
        run_kernel(NO_ACTION_ENTRY, &module, no_action_reference, opt_level);
    }
}

#[test]
fn minimal_parent_loop_aot_matches_reference_o0_o3() {
    let module = build_minimal_parent_loop_module();
    for opt_level in OPT_LEVELS {
        run_kernel(MINIMAL_ENTRY, &module, minimal_reference, opt_level);
    }
}

/// These fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg refuses by default (roadmap WS7.5,
/// decision gate DG-73). The compiles state `Permit` explicitly.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
