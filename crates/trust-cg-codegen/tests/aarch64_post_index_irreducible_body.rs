// trust-cg-codegen - post-index formation on a loop whose body holds an
// irreducible cycle
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Loops whose body holds a TWO-ENTRY cycle `{arm, inner}`: the block before
//! it branches into both, and each branches to the other. Neither block
//! dominates the other, so the cycle has no dominator back-edge, `LoopAnalysis`
//! never reports it as a loop, and the enclosing loop looks innermost. `inner`
//! dominates the latch, so "dominated by the header and dominating every latch"
//! admits it as a block that runs once per iteration, yet it runs twice on
//! every iteration below.
//!
//! The post-index folds (`post_index_late` post-RA, `trust_cg_opt::post_index`
//! in the mid-end) advance their walking pointer once per LOAD and assume the
//! index IV advances once per iteration. Here either the IV steps twice per
//! load or the load runs twice per step, so a fold reads the wrong elements.
//! Every level runs through the JIT with both AArch64 allocator profiles and
//! must return the reference value.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// ```text
/// s = 0; i = 0; c = 0
/// head:  if c >= n return s
/// body:  v = a[i]  (byte GEP of i << 2); s += v
///        if v < 0 goto arm else goto inner
/// arm:   s += 1000; goto inner
/// inner: i += 1; if i is odd goto arm else goto latch
/// latch: c += 1; goto head
/// ```
///
/// Each iteration enters `inner` with an even `i` and leaves it with `i + 2`,
/// passing through `inner` twice, so the loop reads `a[0], a[2], a[4], ...`.
fn step_twice_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("post_index_irreducible_step_twice");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::U64], vec![Ty::I32]);
    let mut fb = mb.function("step_twice_sum", ty);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::Ptr);
    let n = fb.add_block_param(entry, Ty::U64);
    let head = fb.create_block();
    let i = fb.add_block_param(head, Ty::U64);
    let s = fb.add_block_param(head, Ty::I32);
    let c = fb.add_block_param(head, Ty::U64);
    let body = fb.create_block();
    let arm = fb.create_block();
    let arm_i = fb.add_block_param(arm, Ty::U64);
    let arm_s = fb.add_block_param(arm, Ty::I32);
    let inner = fb.create_block();
    let inner_i = fb.add_block_param(inner, Ty::U64);
    let inner_s = fb.add_block_param(inner, Ty::I32);
    let latch = fb.create_block();
    let exit = fb.create_block();
    let result = fb.add_block_param(exit, Ty::I32);

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    let zero32 = fb.iconst(Ty::I32, 0);
    fb.br(head, vec![zero, zero32, zero]);

    fb.switch_to_block(head);
    let more = fb.icmp(ICmpOp::Ult, Ty::U64, c, n);
    fb.condbr(more, body, vec![], exit, vec![s]);

    fb.switch_to_block(body);
    let two = fb.iconst(Ty::U64, 2);
    let off = fb.binop(BinOp::Shl, Ty::U64, i, two);
    let pa = fb.gep(Ty::I8, a, vec![off]);
    let v = fb.load(Ty::I32, pa);
    let s1 = fb.binop(BinOp::Add, Ty::I32, s, v);
    let zero32 = fb.iconst(Ty::I32, 0);
    let negative = fb.icmp(ICmpOp::Slt, Ty::I32, v, zero32);
    fb.condbr(negative, arm, vec![i, s1], inner, vec![i, s1]);

    fb.switch_to_block(arm);
    let bonus = fb.iconst(Ty::I32, 1000);
    let arm_s1 = fb.binop(BinOp::Add, Ty::I32, arm_s, bonus);
    fb.br(inner, vec![arm_i, arm_s1]);

    fb.switch_to_block(inner);
    let one = fb.iconst(Ty::U64, 1);
    let i1 = fb.binop(BinOp::Add, Ty::U64, inner_i, one);
    let parity = fb.binop(BinOp::And, Ty::U64, i1, one);
    let zero = fb.iconst(Ty::U64, 0);
    let odd = fb.icmp(ICmpOp::Ne, Ty::U64, parity, zero);
    fb.condbr(odd, arm, vec![i1, inner_s], latch, vec![]);

    fb.switch_to_block(latch);
    let one = fb.iconst(Ty::U64, 1);
    let c1 = fb.binop(BinOp::Add, Ty::U64, c, one);
    fb.br(head, vec![i1, inner_s, c1]);

    fb.switch_to_block(exit);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// [`step_twice_module`] in Rust.
fn step_twice_reference(a: &[i32], n: u64) -> i32 {
    let (mut i, mut s) = (0usize, 0i32);
    for _ in 0..n {
        let v = a[i];
        s = s.wrapping_add(v);
        let mut at_arm = v < 0;
        loop {
            if at_arm {
                s = s.wrapping_add(1000);
            }
            i += 1;
            if i & 1 == 0 {
                break;
            }
            at_arm = true;
        }
    }
    s
}

/// ```text
/// s = 0; i = 0
/// head:  if i >= n return s
/// body:  t = 0; if s is odd goto arm else goto inner
/// arm:   s += 1000; goto inner
/// inner: v = a[i]  (byte GEP of i << 2); s += v; t ^= 1
///        if t != 0 goto arm else goto latch
/// latch: i += 1; goto head
/// ```
///
/// `inner` toggles `t` from 0 to 1 and back, so it runs twice per iteration
/// while `i` steps once: the loop reads `a[0], a[0], a[1], a[1], ...`.
fn load_twice_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("post_index_irreducible_load_twice");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::U64], vec![Ty::I32]);
    let mut fb = mb.function("load_twice_sum", ty);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::Ptr);
    let n = fb.add_block_param(entry, Ty::U64);
    let head = fb.create_block();
    let i = fb.add_block_param(head, Ty::U64);
    let s = fb.add_block_param(head, Ty::I32);
    let body = fb.create_block();
    let arm = fb.create_block();
    let arm_s = fb.add_block_param(arm, Ty::I32);
    let arm_t = fb.add_block_param(arm, Ty::U64);
    let inner = fb.create_block();
    let inner_s = fb.add_block_param(inner, Ty::I32);
    let inner_t = fb.add_block_param(inner, Ty::U64);
    let latch = fb.create_block();
    let exit = fb.create_block();
    let result = fb.add_block_param(exit, Ty::I32);

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    let zero32 = fb.iconst(Ty::I32, 0);
    fb.br(head, vec![zero, zero32]);

    fb.switch_to_block(head);
    let more = fb.icmp(ICmpOp::Ult, Ty::U64, i, n);
    fb.condbr(more, body, vec![], exit, vec![s]);

    fb.switch_to_block(body);
    let one32 = fb.iconst(Ty::I32, 1);
    let parity = fb.binop(BinOp::And, Ty::I32, s, one32);
    let zero32 = fb.iconst(Ty::I32, 0);
    let odd = fb.icmp(ICmpOp::Ne, Ty::I32, parity, zero32);
    let zero = fb.iconst(Ty::U64, 0);
    fb.condbr(odd, arm, vec![s, zero], inner, vec![s, zero]);

    fb.switch_to_block(arm);
    let bonus = fb.iconst(Ty::I32, 1000);
    let arm_s1 = fb.binop(BinOp::Add, Ty::I32, arm_s, bonus);
    fb.br(inner, vec![arm_s1, arm_t]);

    fb.switch_to_block(inner);
    let two = fb.iconst(Ty::U64, 2);
    let off = fb.binop(BinOp::Shl, Ty::U64, i, two);
    let pa = fb.gep(Ty::I8, a, vec![off]);
    let v = fb.load(Ty::I32, pa);
    let s1 = fb.binop(BinOp::Add, Ty::I32, inner_s, v);
    let one = fb.iconst(Ty::U64, 1);
    let t1 = fb.binop(BinOp::Xor, Ty::U64, inner_t, one);
    let zero = fb.iconst(Ty::U64, 0);
    let again = fb.icmp(ICmpOp::Ne, Ty::U64, t1, zero);
    fb.condbr(again, arm, vec![s1, t1], latch, vec![]);

    fb.switch_to_block(latch);
    let one = fb.iconst(Ty::U64, 1);
    let i1 = fb.binop(BinOp::Add, Ty::U64, i, one);
    fb.br(head, vec![i1, s1]);

    fb.switch_to_block(exit);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// [`load_twice_module`] in Rust.
fn load_twice_reference(a: &[i32], n: u64) -> i32 {
    let mut s = 0i32;
    for &v in &a[..n as usize] {
        let mut at_arm = s & 1 != 0;
        let mut t = 0u64;
        loop {
            if at_arm {
                s = s.wrapping_add(1000);
            }
            s = s.wrapping_add(v);
            t ^= 1;
            if t == 0 {
                break;
            }
            at_arm = true;
        }
    }
    s
}

/// JIT-compile at `opt_level`. `jit_fast_regalloc` picks the allocator: the
/// JIT-latency profile (no coalescing), or the AOT LinearScan profile, whose
/// coalescing folds the IV's block-parameter copies into the in-place
/// `add x, x, #1` the post-RA fold looks for.
fn jit(
    module: &trust_ir::Module,
    opt_level: OptLevel,
    jit_fast_regalloc: bool,
) -> JitCompilationResult {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    config.enable_jit_fast_regalloc = jit_fast_regalloc;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(module, &HashMap::new())
        .unwrap_or_else(|error| {
            panic!("{opt_level:?} jit_fast_regalloc={jit_fast_regalloc}: {error}")
        })
}

type Sum = extern "C" fn(*const i32, u64) -> i32;

/// Distinct magnitudes with one negative entry, so reading any element other
/// than the reference's changes the sum.
const DATA: [i32; 12] = [
    1, 10, -100, 1_000, 10_000, 100_000, 1_000_000, 10_000_000, 3, 30, 300, 3_000,
];

#[test]
fn an_iv_stepped_twice_by_an_irreducible_cycle_returns_the_reference() {
    let module = step_twice_module();
    for jit_fast_regalloc in [true, false] {
        for opt_level in LEVELS {
            let result = jit(&module, opt_level, jit_fast_regalloc);
            // SAFETY: the trust-ir signature is (ptr, u64) -> i32. With n <= 6
            // the loop reads a[0], a[2], ..., a[2n - 2] (or, miscompiled,
            // a[0..n]), all inside DATA's 12 elements; `result` outlives the
            // call.
            let entry = unsafe { result.buffer.get_fn_bound::<Sum>("step_twice_sum") }
                .expect("entry symbol");
            for n in 0..=6u64 {
                assert_eq!(
                    entry.as_ref()(DATA.as_ptr(), n),
                    step_twice_reference(&DATA, n),
                    "{opt_level:?} jit_fast_regalloc={jit_fast_regalloc} n={n}"
                );
            }
        }
    }
}

#[test]
fn a_load_run_twice_by_an_irreducible_cycle_returns_the_reference() {
    let module = load_twice_module();
    for jit_fast_regalloc in [true, false] {
        for opt_level in LEVELS {
            let result = jit(&module, opt_level, jit_fast_regalloc);
            // SAFETY: the trust-ir signature is (ptr, u64) -> i32. With n <= 6
            // the loop reads a[0..n] (or, miscompiled, a[0..2n]), all inside
            // DATA's 12 elements; `result` outlives the call.
            let entry = unsafe { result.buffer.get_fn_bound::<Sum>("load_twice_sum") }
                .expect("entry symbol");
            for n in 0..=6u64 {
                assert_eq!(
                    entry.as_ref()(DATA.as_ptr(), n),
                    load_twice_reference(&DATA, n),
                    "{opt_level:?} jit_fast_regalloc={jit_fast_regalloc} n={n}"
                );
            }
        }
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
