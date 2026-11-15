// trust-cg-codegen/tests/jit_teardown_policy.rs - enforced JIT teardown policy
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Cross-thread execution and reclamation controls for the teardown policy an
// `ExecutableBuffer` enforces:
//
// - drop-during-execution: a worker thread is parked inside a host callback
//   called FROM JIT code, so its return address lies in the JIT text. The
//   owner drops the buffer while the worker is parked; the worker then returns
//   into that text. Without enforcement the drop unmaps the pages and the
//   return faults. With the default `RefCounted` policy the drop retires the
//   mapping and the worker's lease reclaims it after the call completes.
// - cross-thread leased execution continues after the owner drops the buffer.
// - `try_release` refuses (and returns the buffer) while leases are in flight.
// - `ProcessLifetime` retains the mapping: raw pointers keep working after
//   drop; release is refused.
// - downstream/unspecified policies and a lifetime downgrade are refused.
//
// Required-floor target: registered in scripts/check_linux_aarch64.py.

#![cfg(all(
    unix,
    any(target_arch = "x86_64", target_arch = "aarch64"),
    any(target_os = "macos", target_os = "linux")
))]

#[path = "common/pinned_target.rs"]
mod pinned_target;

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Barrier};
use std::time::{Duration, Instant};

use trust_cg_codegen::Compiler;
use trust_cg_codegen::compiler::CompilerConfig;
use trust_cg_codegen::jit::{
    ExecutableBuffer, JitError, JitReclamationState, ensure_jit_execute_mode,
    executable_buffer_teardown_counters,
};
use trust_cg_codegen::jit_contract::{ExecutableMemoryOwner, TeardownPolicy};
use trust_ir::{BinOp, Ty};
use trust_ir_build::ModuleBuilder;

/// Rendezvous shared between the test thread and the host callback.
struct Hold {
    entered: AtomicBool,
    release: AtomicBool,
    value: u64,
}

impl Hold {
    fn new(value: u64) -> Self {
        Self {
            entered: AtomicBool::new(false),
            release: AtomicBool::new(false),
            value,
        }
    }

    fn wait_entered(&self) {
        let deadline = Instant::now() + Duration::from_secs(60);
        while !self.entered.load(Ordering::SeqCst) {
            assert!(
                Instant::now() < deadline,
                "JIT code never reached the callback"
            );
            std::thread::yield_now();
        }
    }
}

/// Host callback invoked from JIT code: parks until released, then returns
/// into the JIT caller's remaining instructions.
extern "C" fn hold_in_callback(ctx: *const Hold) -> u64 {
    // SAFETY: the test passes a pointer to a `Hold` it keeps alive (Arc)
    // until the worker thread has joined.
    let hold = unsafe { &*ctx };
    hold.entered.store(true, Ordering::SeqCst);
    while !hold.release.load(Ordering::SeqCst) {
        std::thread::yield_now();
    }
    hold.value
}

/// `entry(ctx) = hold_in_callback(ctx) + 1`: the `+ 1` executes in JIT text
/// after the callback returns.
fn compile_hold_module(module_name: &str) -> ExecutableBuffer {
    let mut mb = ModuleBuilder::new_with_target_info(
        module_name,
        pinned_target::target_info(pinned_target::host_triple()),
    );
    let hold_ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
    let hold = mb.declare_function("hold_in_callback", hold_ty);
    let entry_ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
    {
        let mut fb = mb.function("entry", entry_ty);
        let block = fb.create_block();
        let ctx = fb.add_block_param(block, Ty::Ptr);
        fb.switch_to_block(block);
        let held = fb.call(hold, vec![ctx]);
        let one = fb.uconst(Ty::U64, 1);
        let result = fb.binop(BinOp::Add, Ty::U64, held, one);
        fb.ret(vec![result]);
        fb.build();
    }
    let externs = HashMap::from([("hold_in_callback".to_owned(), hold_in_callback as *const u8)]);
    Compiler::new(CompilerConfig::for_host_jit())
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(
            &mb.build().expect("ModuleBuilder::build: test fixture"),
            &externs,
        )
        .expect("host JIT compile must succeed")
        .buffer
}

/// `add_one(x) = x + 1`.
fn compile_add_one(module_name: &str) -> ExecutableBuffer {
    let mut mb = ModuleBuilder::new_with_target_info(
        module_name,
        pinned_target::target_info(pinned_target::host_triple()),
    );
    let ty = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("add_one", ty);
    let block = fb.create_block();
    let x = fb.add_block_param(block, Ty::U64);
    fb.switch_to_block(block);
    let one = fb.uconst(Ty::U64, 1);
    let result = fb.binop(BinOp::Add, Ty::U64, x, one);
    fb.ret(vec![result]);
    fb.build();
    Compiler::new(CompilerConfig::for_host_jit())
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(
            &mb.build().expect("ModuleBuilder::build: test fixture"),
            &HashMap::new(),
        )
        .expect("host JIT compile must succeed")
        .buffer
}

fn add_one_fn(ptr: *const u8) -> extern "C" fn(u64) -> u64 {
    // SAFETY: `ptr` is the `add_one(u64) -> u64` entry of a published buffer
    // whose mapping the caller keeps alive (lease or process lifetime).
    unsafe { std::mem::transmute::<*const u8, extern "C" fn(u64) -> u64>(ptr) }
}

#[test]
fn drop_during_execution_defers_reclamation_until_the_lease_drains() {
    let before = executable_buffer_teardown_counters();
    let buffer = compile_hold_module("teardown_drop_during_execution");
    assert_eq!(*buffer.teardown_policy(), TeardownPolicy::RefCounted);
    let probe = buffer.reclamation_probe();
    assert_eq!(probe.state(), JitReclamationState::Live);

    let leased = buffer.leased_symbol_ptr("entry").expect("leased entry");
    assert_eq!(buffer.in_flight_executions(), 1);
    let hold = Arc::new(Hold::new(41));
    let worker = {
        let hold = Arc::clone(&hold);
        std::thread::spawn(move || {
            leased.prepare_current_thread();
            // SAFETY: `entry(*const Hold) -> u64`; the lease keeps it mapped.
            let entry = unsafe {
                std::mem::transmute::<*const u8, extern "C" fn(*const Hold) -> u64>(leased.as_ptr())
            };
            let result = entry(Arc::as_ptr(&hold));
            drop(leased);
            result
        })
    };

    // The worker is now parked inside the callback with a return address in
    // the JIT text. Dropping the owner must neither block nor unmap it.
    hold.wait_entered();
    drop(buffer);
    assert_eq!(
        probe.state(),
        JitReclamationState::RetiredPendingExecutions { in_flight: 1 }
    );

    hold.release.store(true, Ordering::SeqCst);
    let result = worker
        .join()
        .expect("worker returned into retired JIT text without faulting");
    assert_eq!(result, 42, "the JIT tail after the callback must run");
    assert_eq!(probe.state(), JitReclamationState::Reclaimed);
    assert_eq!(probe.in_flight(), 0);

    let after = executable_buffer_teardown_counters();
    assert!(after.deferred_reclamations > before.deferred_reclamations);
    assert!(after.completed_deferred_reclamations > before.completed_deferred_reclamations);
}

#[test]
fn cross_thread_leased_execution_continues_after_the_owner_drops() {
    const THREADS: usize = 8;
    let buffer = compile_add_one("teardown_cross_thread");
    let probe = buffer.reclamation_probe();
    let leased = buffer.leased_symbol_ptr("add_one").expect("leased add_one");
    let started = Arc::new(Barrier::new(THREADS + 1));
    let owner_dropped = Arc::new(Barrier::new(THREADS + 1));

    let workers: Vec<_> = (0..THREADS)
        .map(|thread| {
            let leased = leased.clone();
            let started = Arc::clone(&started);
            let owner_dropped = Arc::clone(&owner_dropped);
            std::thread::spawn(move || {
                leased.prepare_current_thread();
                let f = add_one_fn(leased.as_ptr());
                let base = (thread as u64) << 32;
                started.wait();
                for i in 0..10_000u64 {
                    assert_eq!(f(base + i), base + i + 1);
                }
                owner_dropped.wait();
                // Executes strictly after the owning buffer was dropped.
                for i in 0..10_000u64 {
                    assert_eq!(f(base ^ i), (base ^ i) + 1);
                }
                drop(leased);
            })
        })
        .collect();
    drop(leased);
    assert_eq!(buffer.in_flight_executions(), THREADS);

    started.wait();
    drop(buffer);
    assert_eq!(
        probe.state(),
        JitReclamationState::RetiredPendingExecutions { in_flight: THREADS }
    );
    owner_dropped.wait();
    for worker in workers {
        worker
            .join()
            .expect("leased cross-thread execution after owner drop");
    }
    assert_eq!(probe.state(), JitReclamationState::Reclaimed);
}

#[test]
fn release_is_refused_while_executions_are_in_flight() {
    let buffer = compile_add_one("teardown_release_refused");
    let probe = buffer.reclamation_probe();
    let lease = buffer.execution_lease().expect("lease");
    let second = lease.clone();
    assert_eq!(buffer.in_flight_executions(), 2);

    let refusal = buffer
        .try_release()
        .expect_err("release must be refused while leases are in flight");
    assert!(
        matches!(
            refusal.error,
            JitError::ExecutableBufferInFlight { in_flight: 2, .. }
        ),
        "{:?}",
        refusal.error
    );
    let buffer = refusal.buffer;
    assert_eq!(probe.state(), JitReclamationState::Live);
    let f = add_one_fn(buffer.get_fn_ptr_bound("add_one").expect("symbol").as_ptr());
    assert_eq!(f(41), 42, "a refused release leaves the buffer executable");

    drop(lease);
    let refusal = buffer
        .try_release()
        .expect_err("one lease is still in flight");
    assert!(matches!(
        refusal.error,
        JitError::ExecutableBufferInFlight { in_flight: 1, .. }
    ));
    let buffer = refusal.buffer;
    drop(second);
    assert_eq!(buffer.in_flight_executions(), 0);
    buffer
        .try_release()
        .expect("release succeeds once no lease is in flight");
    assert_eq!(probe.state(), JitReclamationState::Reclaimed);
}

#[test]
fn process_lifetime_policy_keeps_raw_pointers_valid_after_drop() {
    let before = executable_buffer_teardown_counters();
    let mut buffer = compile_add_one("teardown_process_lifetime");
    buffer
        .set_teardown_policy(TeardownPolicy::ProcessLifetime)
        .expect("process lifetime is enforceable");
    let raw = buffer.get_fn_ptr_bound("add_one").expect("symbol").as_ptr() as usize;
    let probe = buffer.reclamation_probe();

    let refusal = buffer
        .try_release()
        .expect_err("a process-lifetime buffer is never released");
    assert!(matches!(
        refusal.error,
        JitError::ProcessLifetimeReleaseRefused { .. }
    ));
    drop(refusal.buffer);
    assert_eq!(
        probe.state(),
        JitReclamationState::RetainedForProcessLifetime
    );

    ensure_jit_execute_mode();
    assert_eq!(add_one_fn(raw as *const u8)(41), 42);
    let other_thread = std::thread::spawn(move || {
        ensure_jit_execute_mode();
        add_one_fn(raw as *const u8)(99)
    })
    .join()
    .expect("process-lifetime code runs on another thread after drop");
    assert_eq!(other_thread, 100);
    assert!(
        executable_buffer_teardown_counters().process_lifetime_retained
            > before.process_lifetime_retained
    );
}

#[test]
fn unenforceable_or_downgraded_teardown_policies_are_refused() {
    let mut buffer = compile_add_one("teardown_policy_refusals");
    assert_eq!(
        buffer.executable_memory_owner(),
        ExecutableMemoryOwner::TrustCg
    );
    buffer
        .set_teardown_policy(TeardownPolicy::RefCounted)
        .expect("re-selecting the default is accepted");

    for policy in [
        TeardownPolicy::Downstream("ty-runtime".to_owned()),
        TeardownPolicy::Unspecified,
    ] {
        let error = buffer
            .set_teardown_policy(policy.clone())
            .expect_err("Trust Codegen cannot enforce this policy");
        assert!(
            matches!(error, JitError::UnenforceableTeardownPolicy { .. }),
            "{policy:?}: {error:?}"
        );
        assert_eq!(*buffer.teardown_policy(), TeardownPolicy::RefCounted);
    }

    buffer
        .set_teardown_policy(TeardownPolicy::ProcessLifetime)
        .expect("strengthening to process lifetime is accepted");
    let error = buffer
        .set_teardown_policy(TeardownPolicy::RefCounted)
        .expect_err("process lifetime cannot be weakened");
    assert!(
        matches!(error, JitError::TeardownPolicyDowngradeRefused { .. }),
        "{error:?}"
    );
    assert_eq!(*buffer.teardown_policy(), TeardownPolicy::ProcessLifetime);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
