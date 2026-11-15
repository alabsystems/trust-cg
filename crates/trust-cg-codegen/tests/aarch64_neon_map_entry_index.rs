// trust-cg-codegen - map loops whose induction does not start at index 0
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Map loops in the three shapes the NEON map vectorizer (`neon_map`)
//! recognizes, with the start index a parameter, run through the JIT at every
//! optimization level against a scalar Rust reference:
//!
//! * the bounds-checked chain: a test-first `while i <u N` map with a `u64`
//!   index entered at `1 << 32` (no scalar iteration runs);
//! * the rotated loop: a bottom-tested `a[i] += 5` over `i64` entered at a
//!   negative index;
//! * the native loop under runtime alias versioning: a test-first signed
//!   `dst[i] = src[i] + 1` over overlapping arrays entered at a negative index
//!   (a carried dependence).
//!
//! Each vector plan is exact only from a non-negative, i32-range start, so the
//! pass must leave these loops scalar. The cases are bounded executions on
//! the host, not a proof of the transform.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// Elements of the unsigned map's arrays.
const N: usize = 4096;

/// `i = start; while i <u N { a[i] = a[i]*k + b[i]; i += 1 }` over `i32`
/// elements with a `u64` index, with the in-body `i <u N` bounds check of a
/// safe-Rust array index.
fn unsigned_map_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("neon_map_entry_unsigned");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::I32, Ty::U64], vec![]);
    let mut fb = mb.function("unsigned_map", ty);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::Ptr);
    let b = fb.add_block_param(entry, Ty::Ptr);
    let k = fb.add_block_param(entry, Ty::I32);
    let start = fb.add_block_param(entry, Ty::U64);
    let head = fb.create_block();
    let i = fb.add_block_param(head, Ty::U64);
    let check = fb.create_block();
    let j = fb.add_block_param(check, Ty::U64);
    let body = fb.create_block();
    let exit = fb.create_block();
    let out_of_bounds = fb.create_block();

    fb.switch_to_block(entry);
    let n = fb.iconst(Ty::U64, N as i128);
    fb.br(head, vec![start]);

    fb.switch_to_block(head);
    let more = fb.icmp(ICmpOp::Ult, Ty::U64, i, n);
    fb.condbr(more, check, vec![i], exit, vec![]);

    // The array bounds check a safe-Rust index lowers to, on a copy of the
    // index as the bridge emits it.
    fb.switch_to_block(check);
    let pa0 = fb.gep(Ty::I32, a, vec![i]);
    let va0 = fb.load(Ty::I32, pa0);
    let in_bounds = fb.icmp(ICmpOp::Ult, Ty::U64, j, n);
    fb.condbr(in_bounds, body, vec![], out_of_bounds, vec![]);

    fb.switch_to_block(out_of_bounds);
    fb.ret(vec![]);

    fb.switch_to_block(body);
    let pb = fb.gep(Ty::I32, b, vec![i]);
    let vb = fb.load(Ty::I32, pb);
    let scaled = fb.binop(BinOp::Mul, Ty::I32, va0, k);
    let sum = fb.binop(BinOp::Add, Ty::I32, scaled, vb);
    fb.store(Ty::I32, pa0, sum);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.binop(BinOp::Add, Ty::U64, i, one);
    fb.br(head, vec![next]);

    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `if s < n { i = s; do { a[i] += 5; i += 1 } while i != n }` over `i64`.
fn rotated_bump_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("neon_map_entry_rotated");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::I64, Ty::I64], vec![]);
    let mut fb = mb.function("rotated_bump", ty);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::Ptr);
    let s = fb.add_block_param(entry, Ty::I64);
    let n = fb.add_block_param(entry, Ty::I64);
    let head = fb.create_block();
    let i = fb.add_block_param(head, Ty::I64);
    let exit = fb.create_block();

    fb.switch_to_block(entry);
    let nonempty = fb.icmp(ICmpOp::Slt, Ty::I64, s, n);
    fb.condbr(nonempty, head, vec![s], exit, vec![]);

    fb.switch_to_block(head);
    let p = fb.gep(Ty::I64, a, vec![i]);
    let v = fb.load(Ty::I64, p);
    let five = fb.iconst(Ty::I64, 5);
    let bumped = fb.binop(BinOp::Add, Ty::I64, v, five);
    fb.store(Ty::I64, p, bumped);
    let one = fb.iconst(Ty::I64, 1);
    let next = fb.binop(BinOp::Add, Ty::I64, i, one);
    let done = fb.icmp(ICmpOp::Eq, Ty::I64, next, n);
    fb.condbr(done, exit, vec![], head, vec![next]);

    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `i = s; while i < n { dst[i] = src[i] + 1; i += 1 }` over `i32` with a
/// signed `i32` index.
fn signed_copy_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("neon_map_entry_signed");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::I32, Ty::I32], vec![]);
    let mut fb = mb.function("signed_copy", ty);
    let entry = fb.create_block();
    let dst = fb.add_block_param(entry, Ty::Ptr);
    let src = fb.add_block_param(entry, Ty::Ptr);
    let s = fb.add_block_param(entry, Ty::I32);
    let n = fb.add_block_param(entry, Ty::I32);
    let head = fb.create_block();
    let i = fb.add_block_param(head, Ty::I32);
    let body = fb.create_block();
    let exit = fb.create_block();

    fb.switch_to_block(entry);
    fb.br(head, vec![s]);

    fb.switch_to_block(head);
    let more = fb.icmp(ICmpOp::Slt, Ty::I32, i, n);
    fb.condbr(more, body, vec![], exit, vec![]);

    fb.switch_to_block(body);
    let idx = fb.sext(Ty::I32, Ty::I64, i);
    let ps = fb.gep(Ty::I32, src, vec![idx]);
    let v = fb.load(Ty::I32, ps);
    let one32 = fb.iconst(Ty::I32, 1);
    let bumped = fb.binop(BinOp::Add, Ty::I32, v, one32);
    let pd = fb.gep(Ty::I32, dst, vec![idx]);
    fb.store(Ty::I32, pd, bumped);
    let next = fb.binop(BinOp::Add, Ty::I32, i, one32);
    fb.br(head, vec![next]);

    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn jit(module: &trust_ir::Module, opt_level: OptLevel) -> JitCompilationResult {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(module, &HashMap::new())
        .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"))
}

#[test]
fn an_unsigned_map_entered_past_i32_range_stores_nothing() {
    let module = unsigned_map_module();
    let b: Vec<i32> = (0..N as i32).map(|x| x * 3 - 7).collect();
    let mut wrong = Vec::new();
    for opt_level in LEVELS {
        let result = jit(&module, opt_level);
        // SAFETY: the trust-ir signature is (ptr, ptr, i32, u64) -> (); `a` and
        // `b` hold N elements, the scalar loop touches only indices below N,
        // and `result` outlives the call.
        let entry = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*mut i32, *const i32, i32, u64)>("unsigned_map")
        }
        .expect("entry symbol");
        for start in [0u64, 5, 1 << 32, (1 << 32) + 3] {
            let mut a: Vec<i32> = (0..N as i32).map(|x| x ^ 0x55).collect();
            let mut want = a.clone();
            let mut j = start;
            while j < N as u64 {
                let idx = j as usize;
                want[idx] = want[idx].wrapping_mul(3).wrapping_add(b[idx]);
                j += 1;
            }
            entry.as_ref()(a.as_mut_ptr(), b.as_ptr(), 3, start);
            if a != want {
                let first = (0..N).find(|&x| a[x] != want[x]).unwrap();
                wrong.push(format!(
                    "{opt_level:?} start={start:#x}: a[{first}] = {} (want {})",
                    a[first], want[first]
                ));
            }
        }
    }
    assert!(wrong.is_empty(), "\n  {}", wrong.join("\n  "));
}

#[test]
fn a_rotated_map_entered_at_a_negative_index_runs_every_iteration() {
    let module = rotated_bump_module();
    const PAD: usize = 16;
    let mut wrong = Vec::new();
    for opt_level in LEVELS {
        let result = jit(&module, opt_level);
        // SAFETY: the trust-ir signature is (ptr, i64, i64) -> (); `a` points
        // PAD elements into `buf`, every case keeps `[s, n)` inside `buf`, and
        // `result` outlives the call.
        let entry = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*mut i64, i64, i64)>("rotated_bump")
        }
        .expect("entry symbol");
        for (s, n) in [
            (0i64, 100i64),
            (-4, 100),
            (-4, 3),
            (-16, 0),
            (-9, 40),
            (3, 64),
        ] {
            let mut buf: Vec<i64> = (0..PAD as i64 + 128).map(|x| x * 11).collect();
            let mut want = buf.clone();
            for i in s..n {
                want[(PAD as i64 + i) as usize] += 5;
            }
            // SAFETY: PAD < buf.len().
            let a = unsafe { buf.as_mut_ptr().add(PAD) };
            entry.as_ref()(a, s, n);
            if buf != want {
                let first = (0..buf.len()).find(|&x| buf[x] != want[x]).unwrap();
                wrong.push(format!(
                    "{opt_level:?} s={s} n={n}: a[{}] = {} (want {})",
                    first as i64 - PAD as i64,
                    buf[first],
                    want[first]
                ));
            }
        }
    }
    assert!(wrong.is_empty(), "\n  {}", wrong.join("\n  "));
}

#[test]
fn an_overlapping_map_entered_at_a_negative_index_keeps_its_dependence() {
    let module = signed_copy_module();
    let mut wrong = Vec::new();
    for opt_level in LEVELS {
        let result = jit(&module, opt_level);
        // SAFETY: the trust-ir signature is (ptr, ptr, i32, i32) -> (); `dst`
        // and `src` point into the middle of `buf`, every case keeps
        // `[s, n)` (offset by 63 or 64) inside it, and `result` outlives the
        // call.
        let entry = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*mut i32, *const i32, i32, i32)>("signed_copy")
        }
        .expect("entry symbol");
        for (s, n) in [(0i32, 40i32), (-32, 0), (-40, -8), (-32, 20)] {
            let mut buf: Vec<i32> = (0..128).map(|x| x * 7 + 1).collect();
            let mut want = buf.clone();
            for i in s..n {
                want[(64 + i) as usize] = want[(63 + i) as usize].wrapping_add(1);
            }
            let base = buf.as_mut_ptr();
            // SAFETY: both offsets lie inside `buf`.
            let (dst, src) = unsafe { (base.add(64), base.add(63) as *const i32) };
            entry.as_ref()(dst, src, s, n);
            if buf != want {
                let first = (0..buf.len()).find(|&x| buf[x] != want[x]).unwrap();
                wrong.push(format!(
                    "{opt_level:?} s={s} n={n}: buf[{first}] = {} (want {})",
                    buf[first], want[first]
                ));
            }
        }
    }
    assert!(wrong.is_empty(), "\n  {}", wrong.join("\n  "));
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
