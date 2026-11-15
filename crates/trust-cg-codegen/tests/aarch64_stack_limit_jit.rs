// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! U10 prologue stack-limit check, executed (`docs/u10-prologue-stack-limit.md`).
//!
//! A recursive requester reads its limit `L` through its first parameter
//! (`Pointee { offset: 0 }`): deep recursion returns the overflow handler's
//! typed status instead of faulting, shallow calls are unaffected, two
//! threads with different `L` each stop at their own limit, a `Trap`
//! requester dies with SIGTRAP, and every compile carries the net's
//! certificate. These are executions on this host: tested, not proved.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_cg_lower::function::StackLimitSource;
use trust_cg_lower::stack_limit::{
    STACK_LIMIT_HANDLER_TAG, STACK_LIMIT_TRAP_TAG, encode_request_tag,
};

/// Set in the handler's status: the call overflowed. The low bits count the
/// frames that completed above the overflowing one.
const OVERFLOW: u64 = 1 << 63;

const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// `walk(ctx, n)`: `n` when the stack suffices, else
/// `OVERFLOW + frames that completed`. `ctx` points at the u64 limit.
fn walk_module(overflow_tags: &str, handler: bool) -> String {
    let request = encode_request_tag(0, StackLimitSource::Pointee { offset: 0 }).unwrap();
    let mut text = format!(
        "module \"u10_jit\"\n\nfuncty.0 = (ptr, u64) -> (u64)\n\n\
         fn @walk(functy.0) {{\n    ; #proof: custom({request}){overflow_tags}\n\
         bb0(%0: ptr, %1: u64):\n    %2 = const u64 0\n    %3 = icmp eq u64 %1, %2\n\
         \x20   condbr %3, bb1, bb2\nbb1:\n    ret %2\nbb2:\n    %4 = const u64 1\n\
         \x20   %5 = sub u64 %1, %4\n    %6 = call @func.0(%0, %5)\n    %7 = add u64 %6, %4\n\
         \x20   ret %7\n}}\n"
    );
    if handler {
        text.push_str(&format!(
            "\nfn @on_overflow(functy.0) {{\n    ; #proof: custom({STACK_LIMIT_HANDLER_TAG})\n\
             bb0(%0: ptr, %1: u64):\n    %2 = const u64 {OVERFLOW}\n    ret %2\n}}\n"
        ));
    }
    text
}

fn compile(text: &str, opt_level: OptLevel) -> JitCompilationResult {
    let module = trust_ir::parser::parse_module(text).expect("valid trust-ir text");
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(&module, &HashMap::new())
        .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"))
}

/// An address on the current thread's stack, a little above its SP.
#[inline(never)]
fn approximate_sp() -> u64 {
    let marker = 0u8;
    std::hint::black_box(&marker) as *const u8 as u64
}

type Walk = extern "C" fn(*const u64, u64) -> u64;

fn call_walk(result: &JitCompilationResult, limit: &u64, n: u64) -> u64 {
    // SAFETY: `walk`'s trust-ir signature is (ptr, u64) -> u64, `limit`
    // outlives the call, and `result` outlives the function pointer.
    let walk = unsafe { result.buffer.get_fn_bound::<Walk>("walk") }.expect("walk symbol");
    walk.as_ref()(limit, n)
}

#[test]
fn deep_recursion_returns_the_handler_status_and_shallow_calls_are_unaffected() {
    for opt_level in OPT_LEVELS {
        let result = compile(&walk_module("", true), opt_level);
        // No limit at all: an ordinary recursion.
        assert_eq!(call_walk(&result, &0, 1000), 1000, "{opt_level:?}");
        // 256 KiB below the caller: shallow recursion is unaffected...
        let limit = approximate_sp() - 256 * 1024;
        assert_eq!(call_walk(&result, &limit, 100), 100, "{opt_level:?}");
        // ...and a recursion far deeper than 256 KiB reports overflow
        // instead of running into the guard page.
        let status = call_walk(&result, &limit, 100_000_000);
        assert_ne!(status & OVERFLOW, 0, "{opt_level:?}: status {status:#x}");
        let completed = status & !OVERFLOW;
        assert!(
            completed > 100 && completed < 256 * 1024 / 16,
            "{opt_level:?}: {completed} frames completed within 256 KiB"
        );
        // A limit above the caller's SP overflows at the first frame.
        let above = approximate_sp() + 4096;
        assert_eq!(call_walk(&result, &above, 5), OVERFLOW, "{opt_level:?}");
    }
}

#[test]
fn every_compile_carries_the_stack_limit_certificate() {
    for opt_level in OPT_LEVELS {
        let result = compile(&walk_module("", true), opt_level);
        let walk = result
            .per_function_metrics
            .iter()
            .find(|metrics| metrics.name == "walk")
            .expect("walk metrics");
        let summary = walk
            .stack_limit
            .as_ref()
            .unwrap_or_else(|| panic!("{opt_level:?}: walk has no stack-limit summary"));
        assert!(summary.checked, "{opt_level:?}: {summary:?}");
        assert_eq!(summary.handler.as_deref(), Some("on_overflow"));
        assert!(
            summary.total >= summary.csa && summary.csa >= 16,
            "{summary:?}"
        );
        let handler = result
            .per_function_metrics
            .iter()
            .find(|metrics| metrics.name == "on_overflow")
            .expect("handler metrics");
        assert!(
            handler.stack_limit.is_none(),
            "the handler requests nothing"
        );
        let bound = &result
            .stack_limits
            .as_ref()
            .expect("a requesting module reports its bound")
            .bound;
        // walk only calls itself, a checked requester: R is its own
        // pre-check bytes or the handler's frame.
        assert!(bound.reserve.is_some(), "{bound:?}");
        assert!(
            bound.reserve.unwrap() >= u64::from(summary.csa),
            "{bound:?}"
        );
    }
}

#[test]
fn a_module_without_requests_reports_no_bound() {
    let text = "module \"plain\"\n\nfuncty.0 = (u64) -> (u64)\n\n\
                fn @id(functy.0) {\nbb0(%0: u64):\n    ret %0\n}\n";
    let result = compile(text, OptLevel::O2);
    assert!(result.stack_limits.is_none());
    assert!(
        result
            .per_function_metrics
            .iter()
            .all(|m| m.stack_limit.is_none())
    );
}

#[test]
fn two_threads_with_different_limits_each_stop_at_their_own() {
    let result = std::sync::Arc::new(compile(&walk_module("", true), OptLevel::O2));
    let run = |budget: u64| {
        let result = std::sync::Arc::clone(&result);
        std::thread::Builder::new()
            .stack_size(8 * 1024 * 1024)
            .spawn(move || {
                let limit = approximate_sp() - budget;
                call_walk(&result, &limit, 100_000_000)
            })
            .expect("spawn")
    };
    let small = run(64 * 1024);
    let large = run(1024 * 1024);
    let (small, large) = (small.join().unwrap(), large.join().unwrap());
    assert_ne!(small & OVERFLOW, 0);
    assert_ne!(large & OVERFLOW, 0);
    let (small, large) = (small & !OVERFLOW, large & !OVERFLOW);
    // Same frame size, sixteen times the budget.
    assert!(large > small * 8, "small {small}, large {large}");
}

#[test]
fn a_trap_requester_dies_with_sigtrap() {
    const CHILD: &str = "U10_STACK_LIMIT_TRAP_CHILD";
    if std::env::var_os(CHILD).is_some() {
        let tags = format!(", custom({STACK_LIMIT_TRAP_TAG})");
        let result = compile(&walk_module(&tags, false), OptLevel::O2);
        let limit = approximate_sp() - 64 * 1024;
        let status = call_walk(&result, &limit, 100_000_000);
        // Unreachable: the trap must have ended the process.
        eprintln!("trap requester returned {status:#x}");
        std::process::exit(0);
    }
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "a_trap_requester_dies_with_sigtrap",
            "--nocapture",
        ])
        .env(CHILD, "1")
        .output()
        .expect("spawn the child test");
    use std::os::unix::process::ExitStatusExt;
    assert_eq!(
        output.status.signal(),
        Some(libc_sigtrap()),
        "child status {:?}, stderr {}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
}

/// SIGTRAP on Darwin and Linux.
fn libc_sigtrap() -> i32 {
    5
}

#[test]
fn proof_grade_routes_refuse_the_request() {
    let module = trust_ir::parser::parse_module(&walk_module("", true)).unwrap();
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = OptLevel::O2;
    config.emit_proofs = true;
    let error = Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(&module, &HashMap::new())
        .expect_err("v1 is not proof-qualified");
    assert!(
        error.to_string().contains("StackLimitNotProofQualified"),
        "{error}"
    );
}

/// `deep(ctx, n, a2..a7, d0..d7, s1, out)`: eight X arguments, eight V
/// arguments and two stack arguments, recursing on `n` (not in tail
/// position, so no optimization turns it into a loop) with everything else
/// passed through unchanged. The handler stores a checksum of X7, V0, V7 and
/// the first stack argument through the second stack argument and returns
/// `OVERFLOW`: a corrupted register, or a moved SP, shows in the checksum.
fn many_args_module() -> String {
    let request = encode_request_tag(0, StackLimitSource::Pointee { offset: 0 }).unwrap();
    let params = "%0: ptr, %1: u64, %2: u64, %3: u64, %4: u64, %5: u64, %6: u64, %7: u64, \
                  %8: f64, %9: f64, %10: f64, %11: f64, %12: f64, %13: f64, %14: f64, %15: f64, \
                  %16: u64, %17: u64";
    let pass = "%0, %21, %2, %3, %4, %5, %6, %7, %8, %9, %10, %11, %12, %13, %14, %15, %16, %17";
    format!(
        "module \"u10_many\"\n\n\
         functy.0 = (ptr, u64, u64, u64, u64, u64, u64, u64, f64, f64, f64, f64, f64, f64, f64, f64, u64, u64) -> (u64)\n\n\
         fn @deep(functy.0) {{\n    ; #proof: custom({request})\nbb0({params}):\n\
         \x20   %18 = const u64 0\n    %19 = icmp eq u64 %1, %18\n    condbr %19, bb1, bb2\n\
         bb1:\n    ret %18\nbb2:\n    %20 = const u64 1\n    %21 = sub u64 %1, %20\n\
         \x20   %22 = call @func.0({pass})\n    %23 = add u64 %22, %20\n    ret %23\n}}\n\n\
         fn @deep_overflow(functy.0) {{\n    ; #proof: custom({STACK_LIMIT_HANDLER_TAG})\n\
         bb0({params}):\n    %18 = fptoui f64 %8 to u64\n    %19 = fptoui f64 %15 to u64\n\
         \x20   %20 = add u64 %7, %16\n    %21 = add u64 %20, %18\n    %22 = add u64 %21, %19\n\
         \x20   %23 = inttoptr u64 %17 to ptr\n    store u64 %22, ptr %23\n\
         \x20   %24 = const u64 {OVERFLOW}\n    ret %24\n}}\n"
    )
}

type Deep = extern "C" fn(
    *const u64,
    u64,
    u64,
    u64,
    u64,
    u64,
    u64,
    u64,
    f64,
    f64,
    f64,
    f64,
    f64,
    f64,
    f64,
    f64,
    u64,
    u64,
) -> u64;

#[test]
fn the_handler_sees_every_register_and_stack_argument() {
    for opt_level in OPT_LEVELS {
        let result = compile(&many_args_module(), opt_level);
        // SAFETY: the signature matches functy.0; `result`, `limit` and
        // `checksum` outlive the calls.
        let deep = unsafe { result.buffer.get_fn_bound::<Deep>("deep") }.expect("deep symbol");
        let checksum = std::cell::Cell::new(0u64);
        let call = |limit: &u64, n: u64| {
            deep.as_ref()(
                limit,
                n,
                2,
                3,
                4,
                5,
                6,
                700,
                1.0,
                2.0,
                3.0,
                4.0,
                5.0,
                6.0,
                7.0,
                8000.0,
                90_000,
                checksum.as_ptr() as u64,
            )
        };
        assert_eq!(call(&0, 50), 50, "{opt_level:?}: no limit");
        assert_eq!(checksum.get(), 0, "{opt_level:?}: no overflow, no handler");
        let limit = approximate_sp() - 128 * 1024;
        let status = call(&limit, 100_000_000);
        assert_ne!(status & OVERFLOW, 0, "{opt_level:?}: status {status:#x}");
        assert_eq!(
            checksum.get(),
            700 + 90_000 + 1 + 8000,
            "{opt_level:?}: the handler saw a corrupted argument"
        );
    }
}

/// An AOT compile served from the artifact cache reports the same
/// acknowledgment as the compile that stored it.
#[test]
fn a_cached_object_keeps_the_acknowledgment() {
    use trust_cg_codegen::{
        CompileArtifactCacheConfig, CompileArtifactCacheStatus, CompileArtifactDependencyIdentity,
        CompileArtifactProofPolicy,
    };
    let module = trust_ir::parser::parse_module(&walk_module("", true)).unwrap();
    let root = std::env::temp_dir().join(format!(
        "trust-cg-u10-cache-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    let compile = || {
        let config = CompilerConfig {
            opt_level: OptLevel::O2,
            ..CompilerConfig::default()
        };
        Compiler::new_for_target_spec(
            config,
            trust_cg_codegen::target::TargetSpec::parse("aarch64-apple-darwin").unwrap(),
        )
        .with_codegen_license(permit_unlicensed())
        .with_compile_artifact_cache(CompileArtifactCacheConfig::new(
            &root,
            CompileArtifactProofPolicy::Unchecked,
            CompileArtifactDependencyIdentity::new(
                "source-lock-sha256:trust-cg-u10-test",
                "source-lock-sha256:trust-ir-u10-test",
                "source-lock-sha256:ay-u10-test",
                "rustc:stage2-sha256:u10-test",
                "tcargo:sha256:u10-test",
                "trust",
            ),
        ))
        .compile(&module)
        .expect("AOT compile")
    };
    let stored = compile();
    let reused = compile();
    std::fs::remove_dir_all(&root).ok();
    assert_eq!(stored.object_code, reused.object_code);
    let stored_report = stored.stack_limits.expect("stored acknowledgment");
    let reused_report = reused.stack_limits.expect("reused acknowledgment");
    assert_eq!(stored_report, reused_report);
    assert!(
        stored_report
            .functions
            .iter()
            .any(|f| f.name == "walk" && f.checked)
    );
    // Reuse is disabled altogether under an ambient legacy control; the hit
    // is then absent by design, and the acknowledgment is still present.
    if trust_cg_codegen::artifact_reuse_permit().is_some() {
        assert!(
            reused
                .compile_artifact_cache_telemetry
                .iter()
                .any(|row| row.status == CompileArtifactCacheStatus::Hit),
            "{:?}",
            reused.compile_artifact_cache_telemetry
        );
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
