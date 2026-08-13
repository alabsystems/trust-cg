// trust-cg-fuzz - Differential fuzzing for Trust Codegen
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Differential fuzzing infrastructure for Trust Codegen. Three drivers live in
// `src/bin/*.rs`; shared helpers (PRNG, trust_ir generation, JSON run log
// schema) live here.
//
// Part of WS3 (differential fuzzing) in the "proving trust-cg replaces llvm"
// plan.  See issue referenced in commits.

pub mod prng;
pub mod runlog;
pub mod trust_ir_gen;

// P2: rustc/LLVM-oracle bridge differential harness CORE (outcome model, diff
// engine, ddmin reducer, seed corpus, BridgeCompiler trait). Pure std — the
// real two-compiler driver lives out-of-workspace in the bridge crate's tests
// (needs the nightly rustc-dev toolchain); this is the authoritative logic it
// mirrors, and is unit-tested in-workspace with a MockCompiler.
pub mod bridge_diff;

// Fork-based execution sandbox: runs each JIT-compiled function in a child
// process so a hardware trap (SIGFPE on idiv #DE / div-by-zero, SIGSEGV, ...)
// kills only the child and the campaign survives. Unix-only.
#[cfg(all(unix, any(target_arch = "aarch64", target_arch = "x86_64")))]
pub mod sandbox;

// JIT-differential-harness core (see src/bin/trust_ir_jit_diff.rs).
// The module is gated to unix aarch64 / x86_64: the JIT backend is host-specific
// and the per-invoke fork sandbox is POSIX-only. On other hosts the binary
// writes an "unavailable" RunLog.
#[cfg(all(unix, any(target_arch = "aarch64", target_arch = "x86_64")))]
pub mod jit_diff;
