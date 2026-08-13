// trust-cg-codegen/tests/jit_runtime_hardening.rs - JIT-7 runtime hardening
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Integration coverage for the JIT-7 trusted-runtime-surface hardening:
//
// 1. LEAK / ownership: repeated compile → execute → drop cycles through the
//    production `compile_module_to_jit` path must not accumulate executable
//    mappings or address space (the accumulation failure mode documented in
//    docs/jit-parallel-race-2026-06-29.md). The mapping is RAII-owned from
//    mmap to publication and `ExecutableBuffer::drop` returns it.
// 2. RACE: concurrent compile/execute/drop across threads is safe — the JIT
//    engine holds no process-global mutable state, every mapping is
//    thread-isolated, and (on Apple Silicon) the MAP_JIT write/execute
//    toggle is per-thread and bracketed.
// 3. PUBLISH CHECK: every published buffer carries the SHA-256 of its
//    published image, verified against the sealed mapping before any
//    executable pointer can exist, and re-checkable at any time via
//    `verify_published_code_integrity`. (The corrupt-a-byte RED test lives
//    in `src/jit.rs`'s unit tests — it needs the `cfg(test)` fault-injection
//    hook inside the publish sequence.)
//
// Host notes: these tests are arch-generic and run on BOTH x86_64 and
// aarch64 hosts. On the x86 development host they execute the x86_64 JIT
// lane natively; their aarch64 (MAP_JIT / icache) executions are validated
// on the M-series lane.

#![cfg(all(unix, any(target_arch = "x86_64", target_arch = "aarch64")))]

use std::collections::HashMap;
use std::sync::Arc;

use trust_cg_codegen::Compiler;
use trust_cg_codegen::compiler::CompilerConfig;
use trust_ir::Ty;
use trust_ir_build::ModuleBuilder;

fn build_answer_module(module_name: &str, function_name: &str) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new(module_name);
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function(function_name, ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let answer = fb.iconst(Ty::I64, 42);
    fb.ret(vec![answer]);
    fb.build();
    mb.build()
}

fn compile_execute_drop(compiler: &Compiler, module_name: &str) {
    let module = build_answer_module(module_name, "answer");
    let result = compiler
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("host JIT compile must succeed");
    let f: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("answer")
            .expect("published symbol must resolve")
            .into_inner()
    };
    assert_eq!(f(), 42);
    // result (and its ExecutableBuffer mapping) drops here.
}

/// macOS-only address-space accounting via proc_pidinfo(PROC_PIDTASKINFO).
#[cfg(target_os = "macos")]
mod vm_stat {
    #[repr(C)]
    #[derive(Default, Clone, Copy)]
    pub struct ProcTaskInfo {
        pub pti_virtual_size: u64,
        pub pti_resident_size: u64,
        pti_total_user: u64,
        pti_total_system: u64,
        pti_threads_user: u64,
        pti_threads_system: u64,
        pti_policy: i32,
        pti_faults: i32,
        pti_pageins: i32,
        pti_cow_faults: i32,
        pti_messages_sent: i32,
        pti_messages_received: i32,
        pti_syscalls_mach: i32,
        pti_syscalls_unix: i32,
        pti_csw: i32,
        pti_threadnum: i32,
        pti_numrunning: i32,
        pti_priority: i32,
    }

    const PROC_PIDTASKINFO: i32 = 4;

    unsafe extern "C" {
        fn proc_pidinfo(
            pid: i32,
            flavor: i32,
            arg: u64,
            buffer: *mut core::ffi::c_void,
            buffersize: i32,
        ) -> i32;
        fn getpid() -> i32;
    }

    pub fn virtual_size() -> u64 {
        let mut info = ProcTaskInfo::default();
        let size = std::mem::size_of::<ProcTaskInfo>() as i32;
        let got = unsafe {
            proc_pidinfo(
                getpid(),
                PROC_PIDTASKINFO,
                0,
                (&mut info as *mut ProcTaskInfo).cast(),
                size,
            )
        };
        assert_eq!(got, size, "proc_pidinfo(PROC_PIDTASKINFO) failed");
        info.pti_virtual_size
    }
}

/// LEAK regression (JIT-7 item 1): repeated compile/execute/drop cycles keep
/// the process address space flat. A mapping leaked per cycle would grow the
/// virtual size by >= one page per cycle (>= 1.5 MiB @4K pages, >= 6 MiB
/// @16K pages, over 384 cycles) and trip the 1 MiB bound.
#[test]
fn jit_compile_execute_drop_cycles_do_not_accumulate_address_space() {
    let compiler = Compiler::new(CompilerConfig::for_host_jit());

    // Warmup: let allocator arenas, caches, and lazy runtime state settle.
    for i in 0..16 {
        compile_execute_drop(&compiler, &format!("jit7_warm_{i}"));
    }

    #[cfg(target_os = "macos")]
    let before = vm_stat::virtual_size();

    for i in 0..384 {
        compile_execute_drop(&compiler, &format!("jit7_cycle_{i}"));
    }

    #[cfg(target_os = "macos")]
    {
        let after = vm_stat::virtual_size();
        let delta = after.saturating_sub(before);
        assert!(
            delta < 1024 * 1024,
            "JIT compile/drop cycles leaked address space: virtual size grew by {delta} bytes \
             over 384 cycles (mapping accumulation — see docs/jit-parallel-race-2026-06-29.md)"
        );
    }
}

/// RACE smoke (JIT-7 item 2): concurrent compile/execute/drop across 8
/// threads. On Apple Silicon this exercises the per-thread MAP_JIT
/// write/execute toggling under contention (M-series lane validates that
/// half); on x86 it pins the mapping lifecycle and publish check under
/// concurrency. Any torn publish would fail closed via the bytes-hash check
/// rather than execute.
#[test]
fn jit_parallel_compile_execute_drop_smoke() {
    let threads: Vec<_> = (0..8)
        .map(|t| {
            std::thread::spawn(move || {
                let compiler = Compiler::new(CompilerConfig::for_host_jit());
                for i in 0..32 {
                    compile_execute_drop(&compiler, &format!("jit7_par_{t}_{i}"));
                }
            })
        })
        .collect();
    for handle in threads {
        handle.join().expect("parallel JIT thread must not crash");
    }
}

/// Cross-thread execution of one shared published buffer: lookup and call on
/// each thread (the lookup restores per-thread execute mode on MAP_JIT
/// hosts), while the owner keeps the buffer alive via Arc.
#[test]
fn jit_shared_buffer_cross_thread_execute() {
    let compiler = Compiler::new(CompilerConfig::for_host_jit());
    let module = build_answer_module("jit7_shared", "answer");
    let result = Arc::new(
        compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .expect("host JIT compile must succeed"),
    );

    let threads: Vec<_> = (0..8)
        .map(|_| {
            let result = Arc::clone(&result);
            std::thread::spawn(move || {
                let f: extern "C" fn() -> i64 = unsafe {
                    result
                        .buffer
                        .get_fn_bound("answer")
                        .expect("published symbol must resolve")
                        .into_inner()
                };
                for _ in 0..1000 {
                    assert_eq!(f(), 42);
                }
            })
        })
        .collect();
    for handle in threads {
        handle
            .join()
            .expect("cross-thread JIT execution must not crash");
    }
}

/// PUBLISH CHECK binding (JIT-7 item 3): every production-path buffer carries
/// a 64-hex-char SHA-256 of its published image, the integrity re-check
/// passes on the live mapping, and recompiling the identical module yields
/// the identical artifact hash (deterministic pipeline, no profile hooks).
#[test]
fn jit_published_buffer_is_hash_bound() {
    let compiler = Compiler::new(CompilerConfig::for_host_jit());
    let module = build_answer_module("jit7_hash_bound", "answer");

    let first = compiler
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("host JIT compile must succeed");
    let hash = first.buffer.published_image_sha256().to_owned();
    assert_eq!(hash.len(), 64, "publish hash must be a sha256 hex digest");
    assert!(hash.bytes().all(|b| b.is_ascii_hexdigit()));
    first
        .buffer
        .verify_published_code_integrity()
        .expect("live mapping must match its publish-time hash");

    let second = compiler
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("host JIT recompile must succeed");
    assert_eq!(
        second.buffer.published_image_sha256(),
        hash,
        "identical module + config must publish an identical artifact hash"
    );
}
