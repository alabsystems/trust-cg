// trust-cg-codegen - loop load hoisting must not read above a load-acquire
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A loop that contains a load-acquire must keep reading its invariant plain
//! load inside the loop, at every optimization level:
//!
//! ```text
//! ready.store(1, Release);
//! i = 0;
//! loop {
//!     [a[i] = 7;]                         // alias-hoist kernels only
//!     while flag.load(Acquire) == 0 {}    // spin, then read
//!     v = *q;
//!     i += 1;
//!     if i >= n { break }
//! }
//! *out = v;
//! ```
//!
//! A publisher thread waits for `ready`, then writes `*q = 42` and releases
//! `flag`. Every read of `q` follows an acquire that saw `flag == 1`, which
//! synchronizes with that release, so the program is free of data races and
//! the read must return 42.
//!
//! Without the `a[i]` store the loop writes no memory, so the read of `q` is a
//! candidate for LICM's tier (a). With it, LICM cannot prove `*q` disjoint
//! from `a[i]`, and the candidate is the alias-versioned load hoist (O2/O3),
//! which versions the loop on a runtime disjointness check. Either hoist reads
//! `q` once, ahead of the loop, as if no in-loop instruction could change it.
//! That read runs before the acquire, sees `0`, and the loop reuses the stale
//! value (`out = 0`), so both must leave a loop that contains a load-acquire
//! alone.
//!
//! These are executions on this host, not a proof, and the failing direction
//! rests on timing: the publisher writes `q` 20 ms after it sees `*ready`, so
//! a read hoisted ahead of the loop (a few instructions after the `*ready`
//! store) sees 0 unless this thread is descheduled for that long in between.
//! A correct compile returns 42 whatever the timing: the acquire that sees
//! `flag == 1` synchronizes with the release that follows `*q = 42`.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering as AtomicOrdering};
use std::time::{Duration, Instant};

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ordering, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "read_after_acquire_in_loop";
const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
/// The value the publisher writes to `*q` before it releases `flag`.
const PUBLISHED: u64 = 42;

/// `(a, q, out, n, flag, ready)`.
type Kernel = extern "C" fn(*mut u64, *const u64, *mut u64, u64, *const u64, *mut u64);

/// Which loop-load hoist the kernel's loop is shaped for.
#[derive(Clone, Copy, Debug)]
enum Hoist {
    /// No memory write in the loop: LICM's tier (a).
    Licm,
    /// An indexed store `a[i] = 7` the load may alias: alias-versioned hoist.
    AliasHoist,
}

const KERNELS: [Hoist; 2] = [Hoist::Licm, Hoist::AliasHoist];

/// The loop in the module docs. The read of `q` is in the block that ends the
/// iteration and runs on every iteration, so both hoists see it as guaranteed
/// to execute.
fn build_module(hoist: Hoist) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_loop_load_hoist_acquire_order");
    let sig = mb.add_func_type(
        vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::U64, Ty::Ptr, Ty::Ptr],
        vec![],
    );
    let mut fb = mb.function(ENTRY, sig);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::Ptr);
    let q = fb.add_block_param(entry, Ty::Ptr);
    let out = fb.add_block_param(entry, Ty::Ptr);
    let n = fb.add_block_param(entry, Ty::U64);
    let flag = fb.add_block_param(entry, Ty::Ptr);
    let ready = fb.add_block_param(entry, Ty::Ptr);
    let header = fb.create_block();
    let i = fb.add_block_param(header, Ty::U64);
    let spin_block = fb.create_block();
    let tail = fb.create_block();
    let done = fb.create_block();
    let result = fb.add_block_param(done, Ty::U64);

    fb.switch_to_block(entry);
    let one = fb.iconst(Ty::U64, 1);
    fb.atomic_store(Ty::U64, ready, one, Ordering::Release);
    let zero = fb.iconst(Ty::U64, 0);
    fb.br(header, vec![zero]);

    // header: [a[i] = 7;] -> spin
    fb.switch_to_block(header);
    if let Hoist::AliasHoist = hoist {
        let slot = fb.gep(Ty::U64, a, vec![i]);
        let seven = fb.iconst(Ty::U64, 7);
        fb.store(Ty::U64, slot, seven);
    }
    fb.br(spin_block, vec![]);

    // spin: while flag.load(Acquire) == 0 {}
    fb.switch_to_block(spin_block);
    let seen = fb.atomic_load(Ty::U64, flag, Ordering::Acquire);
    let unset_value = fb.iconst(Ty::U64, 0);
    let unset = fb.icmp(ICmpOp::Eq, Ty::U64, seen, unset_value);
    fb.condbr(unset, spin_block, vec![], tail, vec![]);

    // tail: v = *q; [*out = v;] i += 1; if i >= n { break }
    fb.switch_to_block(tail);
    let value = fb.load(Ty::U64, q);
    if let Hoist::AliasHoist = hoist {
        // The second store keeps the read's value inside the loop body, which
        // alias-hoist requires (no body-internal value may be live-out).
        fb.store(Ty::U64, out, value);
    }
    let one = fb.iconst(Ty::U64, 1);
    let step = fb.binop(BinOp::Add, Ty::U64, i, one);
    let stop = fb.icmp(ICmpOp::Uge, Ty::U64, step, n);
    let carried = match hoist {
        Hoist::Licm => value,
        Hoist::AliasHoist => step,
    };
    fb.condbr(stop, done, vec![carried], header, vec![step]);

    fb.switch_to_block(done);
    if let Hoist::Licm = hoist {
        fb.store(Ty::U64, out, result);
    }
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn jit(hoist: Hoist, opt_level: OptLevel) -> JitCompilationResult {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(&build_module(hoist), &HashMap::new())
        .unwrap_or_else(|error| panic!("{hoist:?} {opt_level:?}: {error}"))
}

/// Run the kernel against a publisher thread and return `*out`.
fn run_against_publisher(result: &JitCompilationResult) -> u64 {
    let data = AtomicU64::new(0);
    let flag = AtomicU64::new(0);
    let ready = AtomicU64::new(0);
    let mut a = [0u64; 8];
    let mut out = u64::MAX;
    // SAFETY: the trust-ir signature is (ptr, ptr, ptr, u64, ptr, ptr) -> ()
    // and `result` outlives the call. The kernel stores to `ready`, to `out`
    // and (alias-hoist kernels) to `a[0]`, and reads
    // `q` and `flag`; every pointer names a live, aligned u64 of this frame.
    // The publisher always releases `flag` (after a bounded wait), so the
    // spin ends.
    let entry = unsafe { result.buffer.get_fn_bound::<Kernel>(ENTRY) }.expect("entry symbol");
    std::thread::scope(|scope| {
        scope.spawn(|| {
            let deadline = Instant::now() + Duration::from_secs(10);
            while ready.load(AtomicOrdering::Acquire) == 0 && Instant::now() < deadline {
                std::hint::spin_loop();
            }
            std::thread::sleep(Duration::from_millis(20));
            data.store(PUBLISHED, AtomicOrdering::Relaxed);
            flag.store(1, AtomicOrdering::Release);
        });
        entry.as_ref()(
            a.as_mut_ptr(),
            data.as_ptr(),
            &mut out,
            1,
            flag.as_ptr(),
            ready.as_ptr(),
        );
    });
    out
}

#[test]
fn a_read_after_an_in_loop_acquire_sees_the_published_value() {
    let mut failures = Vec::new();
    for hoist in KERNELS {
        for opt_level in LEVELS {
            let result = jit(hoist, opt_level);
            for trial in 0..3 {
                let out = run_against_publisher(&result);
                if out != PUBLISHED {
                    failures.push(format!(
                        "{hoist:?} {opt_level:?} trial {trial}: out = {out}"
                    ));
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "a read ordered after a load-acquire returned a value older than the release it \
         synchronizes with (want {PUBLISHED}):\n{}",
        failures.join("\n")
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
