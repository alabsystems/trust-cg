// trust-cg-codegen - post-RA post-index formation: exit readers, late X16
// writers, size-scaled indexes, conditional IV steps
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Loops the post-RA post-index fold (`post_index_late`) must leave correct,
//! run through the JIT at every optimization level:
//!
//! * the loop EXIT reads the scaled index the fold deletes;
//! * the load scales its index by the access size (`ldr w, [a, x, lsl #2]`
//!   after `lsl x, k, #2`), so its stride is 16 bytes, not 4;
//! * the index advances only on a conditional arm, while a post-indexed
//!   pointer would advance on every iteration.
//!
//! The historical wide-bounds-guard fixture remains unchanged, but v52 source
//! Assert now refuses until faithful panic lowering exists. Its former X16
//! guard native execution credit is explicitly lost, not converted to Assume.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// `i = 0; loop { off = i << 2; if a[off] == 0 { return b[off]; } i += 1 }`,
/// with one `off` shared by the loop's load and the exit's load (byte GEPs).
fn exit_reader_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("post_index_late_exit_reader");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr], vec![Ty::I32]);
    let mut fb = mb.function("first_zero_pick", ty);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::Ptr);
    let b = fb.add_block_param(entry, Ty::Ptr);
    let head = fb.create_block();
    let i = fb.add_block_param(head, Ty::U64);
    let latch = fb.create_block();
    let exit = fb.create_block();

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    fb.br(head, vec![zero]);

    fb.switch_to_block(head);
    let two = fb.iconst(Ty::U64, 2);
    let off = fb.binop(BinOp::Shl, Ty::U64, i, two);
    let pa = fb.gep(Ty::I8, a, vec![off]);
    let va = fb.load(Ty::I32, pa);
    let zero32 = fb.iconst(Ty::I32, 0);
    let found = fb.icmp(ICmpOp::Eq, Ty::I32, va, zero32);
    fb.condbr(found, exit, vec![], latch, vec![]);

    fb.switch_to_block(latch);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.binop(BinOp::Add, Ty::U64, i, one);
    fb.br(head, vec![next]);

    fb.switch_to_block(exit);
    let pb = fb.gep(Ty::I8, b, vec![off]);
    let picked = fb.load(Ty::I32, pb);
    fb.ret(vec![picked]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `s = 0; i = 0; loop { assert!(i < 5000); v = a[i]; if v == 0 { return s }
/// s += v; i += 1 }`, the element address formed as a byte GEP of `i << 2`.
/// The bound exceeds the 12-bit `CMP` immediate, so the guard expands to
/// `MOVZ X16, #5000; CMP i, X16` inside the loop.
fn guarded_sum_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("post_index_late_guarded_sum");
    let ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I32]);
    let mut fb = mb.function("guarded_sum", ty);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::Ptr);
    let head = fb.create_block();
    let i = fb.add_block_param(head, Ty::U64);
    let s = fb.add_block_param(head, Ty::I32);
    let latch = fb.create_block();
    let exit = fb.create_block();

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    let zero32 = fb.iconst(Ty::I32, 0);
    fb.br(head, vec![zero, zero32]);

    fb.switch_to_block(head);
    let bound = fb.iconst(Ty::U64, 5000);
    let in_bounds = fb.icmp(ICmpOp::Ult, Ty::U64, i, bound);
    fb.assert(in_bounds);
    let two = fb.iconst(Ty::U64, 2);
    let off = fb.binop(BinOp::Shl, Ty::U64, i, two);
    let p = fb.gep(Ty::I8, a, vec![off]);
    let v = fb.load(Ty::I32, p);
    let zero_v = fb.iconst(Ty::I32, 0);
    let done = fb.icmp(ICmpOp::Eq, Ty::I32, v, zero_v);
    fb.condbr(done, exit, vec![], latch, vec![]);

    fb.switch_to_block(latch);
    let sum = fb.binop(BinOp::Add, Ty::I32, s, v);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.binop(BinOp::Add, Ty::U64, i, one);
    fb.br(head, vec![next, sum]);

    fb.switch_to_block(exit);
    fb.ret(vec![s]);
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
fn a_loop_exit_reading_the_shared_scaled_index_returns_the_reference() {
    let module = exit_reader_module();
    let a: [i32; 4] = [1, 1, 0, 1];
    let b: [i32; 4] = [10, 20, 30, 40];
    for opt_level in LEVELS {
        let result = jit(&module, opt_level);
        // SAFETY: the trust-ir signature is (ptr, ptr) -> i32; `a` holds a
        // zero at index 2, so every load stays inside `a` and `b`, and
        // `result` outlives the call.
        let entry = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*const i32, *const i32) -> i32>("first_zero_pick")
        }
        .expect("entry symbol");
        assert_eq!(entry.as_ref()(a.as_ptr(), b.as_ptr()), 30, "{opt_level:?}");
    }
}

#[test]
fn a_loop_with_a_source_bounds_assert_refuses_before_jit_installation() {
    let module = guarded_sum_module();
    for opt_level in LEVELS {
        let mut config = CompilerConfig::jit_fast(Target::Aarch64);
        config.opt_level = opt_level;
        let err = Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_err();
        assert!(err.to_string().contains("fn guarded_sum: bb1#2"), "{err}");
        assert!(err.to_string().contains("unspecified panic kind"), "{err}");
    }
}

/// `h = 0; k = 0; while k < n { if a[4k] > 0 { out[k] = k; h += 1 } k += 1 }
/// return h`, where `a[4k]` is an i32 GEP of `k << 2`: the index is scaled by
/// the element size, so the load addresses `a + 16k`.
fn scaled_index_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("post_index_late_scaled_index");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("count_every_fourth", ty);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::Ptr);
    let out = fb.add_block_param(entry, Ty::Ptr);
    let n = fb.add_block_param(entry, Ty::U64);
    let head = fb.create_block();
    let k = fb.add_block_param(head, Ty::U64);
    let h = fb.add_block_param(head, Ty::U64);
    let body = fb.create_block();
    let hit = fb.create_block();
    let latch = fb.create_block();
    let hh = fb.add_block_param(latch, Ty::U64);
    let exit = fb.create_block();

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    fb.br(head, vec![zero, zero]);

    fb.switch_to_block(head);
    let more = fb.icmp(ICmpOp::Ult, Ty::U64, k, n);
    fb.condbr(more, body, vec![], exit, vec![]);

    fb.switch_to_block(body);
    let two = fb.iconst(Ty::U64, 2);
    let s = fb.binop(BinOp::Shl, Ty::U64, k, two);
    let pa = fb.gep(Ty::I32, a, vec![s]);
    let v = fb.load(Ty::I32, pa);
    let zero32 = fb.iconst(Ty::I32, 0);
    let positive = fb.icmp(ICmpOp::Sgt, Ty::I32, v, zero32);
    fb.condbr(positive, hit, vec![], latch, vec![h]);

    fb.switch_to_block(hit);
    let q = fb.gep(Ty::U64, out, vec![k]);
    fb.store(Ty::U64, q, k);
    let one = fb.iconst(Ty::U64, 1);
    let h1 = fb.binop(BinOp::Add, Ty::U64, h, one);
    fb.br(latch, vec![h1]);

    fb.switch_to_block(latch);
    let one = fb.iconst(Ty::U64, 1);
    let k1 = fb.binop(BinOp::Add, Ty::U64, k, one);
    fb.br(head, vec![k1, hh]);

    fb.switch_to_block(exit);
    fb.ret(vec![h]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `h = 0; k = 0; j = 0; while j < n { if a[k] != 0 { out[h] = j; h += 1;
/// k += 1 } j += 1 } return h`, `a[k]` a byte GEP of `k << 2`: the index `k`
/// advances only on iterations that take the arm. Both arms branch straight
/// back to the header, so the arm is itself a back-edge source.
fn conditional_step_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("post_index_late_conditional_step");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("collect_hits", ty);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::Ptr);
    let out = fb.add_block_param(entry, Ty::Ptr);
    let n = fb.add_block_param(entry, Ty::U64);
    let head = fb.create_block();
    let j = fb.add_block_param(head, Ty::U64);
    let k = fb.add_block_param(head, Ty::U64);
    let h = fb.add_block_param(head, Ty::U64);
    let body = fb.create_block();
    let arm = fb.create_block();
    let exit = fb.create_block();

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    fb.br(head, vec![zero, zero, zero]);

    fb.switch_to_block(head);
    let more = fb.icmp(ICmpOp::Ult, Ty::U64, j, n);
    fb.condbr(more, body, vec![], exit, vec![]);

    fb.switch_to_block(body);
    let one = fb.iconst(Ty::U64, 1);
    let j1 = fb.binop(BinOp::Add, Ty::U64, j, one);
    let two = fb.iconst(Ty::U64, 2);
    let off = fb.binop(BinOp::Shl, Ty::U64, k, two);
    let pa = fb.gep(Ty::I8, a, vec![off]);
    let v = fb.load(Ty::I32, pa);
    let zero32 = fb.iconst(Ty::I32, 0);
    let nonzero = fb.icmp(ICmpOp::Ne, Ty::I32, v, zero32);
    fb.condbr(nonzero, arm, vec![], head, vec![j1, k, h]);

    fb.switch_to_block(arm);
    let q = fb.gep(Ty::U64, out, vec![h]);
    fb.store(Ty::U64, q, j);
    let one = fb.iconst(Ty::U64, 1);
    let h1 = fb.binop(BinOp::Add, Ty::U64, h, one);
    let k1 = fb.binop(BinOp::Add, Ty::U64, k, one);
    fb.br(head, vec![j1, k1, h1]);

    fb.switch_to_block(exit);
    fb.ret(vec![h]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

type Collect = extern "C" fn(*const i32, *mut u64, u64) -> u64;

#[test]
fn a_loop_reading_through_a_size_scaled_index_returns_the_reference() {
    let module = scaled_index_module();
    let mut a = [0i32; 16];
    for k in 0..4 {
        a[4 * k] = 1;
    }
    for opt_level in LEVELS {
        let result = jit(&module, opt_level);
        // SAFETY: the trust-ir signature is (ptr, ptr, u64) -> u64. With n = 4
        // the loop reads a[0], a[4], a[8], a[12] (or, miscompiled, a[0..4]),
        // all inside `a`, and writes out[0..4]; `result` outlives the call.
        let entry = unsafe { result.buffer.get_fn_bound::<Collect>("count_every_fourth") }
            .expect("entry symbol");
        let mut out = [0u64; 4];
        let hits = entry.as_ref()(a.as_ptr(), out.as_mut_ptr(), 4);
        assert_eq!((hits, out), (4, [0, 1, 2, 3]), "{opt_level:?}");
    }
}

#[test]
fn a_loop_whose_index_steps_on_a_conditional_arm_returns_the_reference() {
    let module = conditional_step_module();
    let a: [i32; 4] = [1, 0, 7, 9];
    for opt_level in LEVELS {
        let result = jit(&module, opt_level);
        // SAFETY: the trust-ir signature is (ptr, ptr, u64) -> u64. With n = 3
        // the loop reads at most a[0..3] and writes at most out[0..3], both
        // inside the arrays below; `result` outlives the call.
        let entry =
            unsafe { result.buffer.get_fn_bound::<Collect>("collect_hits") }.expect("entry symbol");
        let mut out = [u64::MAX; 3];
        let hits = entry.as_ref()(a.as_ptr(), out.as_mut_ptr(), 3);
        assert_eq!((hits, out), (1, [0, u64::MAX, u64::MAX]), "{opt_level:?}");
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
