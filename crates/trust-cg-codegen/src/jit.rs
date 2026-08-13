// trust-cg-codegen/jit.rs - In-memory JIT execution via raw syscalls
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! In-memory JIT compilation for Trust Codegen.
//!
//! Compiles IR functions directly to callable function pointers in memory,
//! bypassing Mach-O emission, the system linker, and all disk I/O.
//! Uses raw syscalls or VirtualAlloc for executable memory management, Apple
//! MAP_JIT thread-protection toggles on Apple Silicon, plus host-native
//! process-visible symbol fallback where available.
//!
//! # Pipeline
//!
//! Reuses existing phases 1-8 (ISel through AArch64 encoding), then:
//! 1. Lay out all functions contiguously in a buffer
//! 2. Resolve internal fixups (cross-function BL/B calls)
//! 3. Resolve external symbols via veneer trampolines
//! 4. Allocate executable memory, copy code, flush icache
//! 5. Return [`ExecutableBuffer`] with symbol→offset map
//!
//! # Thread-Local Storage (TLS)
//!
//! The JIT does not emit TLS intrinsics. Callers resolve thread-local
//! addresses in Rust and pass them to JIT-compiled code as pointer-typed
//! `extern "C"` arguments, and the JIT treats them as ordinary pointers.
//!
//! Safety invariants:
//! - The resolved pointer is only valid on the thread that resolved it.
//! - The JIT-compiled callee must be invoked on the same thread that resolved
//!   the address.
//! - If the thread exits, the pointer is dangling.
//! - Passing the pointer across threads is UB.
//!
//! Crates that need to surface a TLS pointer through a callback can use
//! `UnsafeCell<T>` with `.with()` to get a stable address for the closure's
//! duration. That address does not outlive the closure invocation's thread.
//!
//! ```rust
//! use std::cell::UnsafeCell;
//!
//! std::thread_local! {
//!     static SCRATCH: UnsafeCell<u64> = UnsafeCell::new(0);
//! }
//!
//! fn call_jit(f: extern "C" fn(*mut u8)) {
//!     SCRATCH.with(|cell| {
//!         let ptr = cell.get() as *mut u8; // valid on THIS thread only
//!         f(ptr);
//!     });
//! }
//! ```
//!
//! Option B, emitting `mrs TPIDR_EL0` for `#[thread_local]` statics, is a
//! future optimization tracked separately.
//!
//! # Supported hosts
//!
//! The JIT execution path (`mmap` + `mprotect` on Unix, `VirtualAlloc` +
//! `VirtualProtect` on Windows) is implemented for five `(target_arch,
//! target_os)` combinations:
//!
//! | target_arch | target_os | MAP_JIT | Page size | Status |
//! |---|---|---|---|---|
//! | `aarch64`   | `macos`   | yes     | 16 KiB    | primary development host |
//! | `aarch64`   | `linux`   | no      | 4 KiB     | supported (#346) |
//! | `x86_64`    | `macos`   | no      | 4 KiB     | supported |
//! | `x86_64`    | `linux`   | no      | 4 KiB     | supported (#346) |
//! | `x86_64`    | `windows` | n/a     | 4 KiB     | supported |
//!
//! Any other host rejects [`JitCompiler::compile_raw`] with
//! [`JitError::UnsupportedHost`] so non-JIT codegen, object emission, and
//! dispatcher tests can still compile on secondary hosts. Running-on-Linux
//! prerequisites: a kernel that permits `mprotect(..., PROT_EXEC)` on
//! anonymous mappings (any mainstream distribution kernel qualifies) and a
//! libc providing `dlsym` (glibc, musl, or equivalent). Windows hosts require
//! standard `kernel32` virtual-memory APIs. No Mach-O / ELF / COFF object-file
//! machinery is used by this path; code is written into anonymous executable
//! memory and invoked directly.
//!
//! On Windows x64, the supported in-process route is the typed
//! [`crate::Compiler`] JIT path, typically
//! `Compiler::for_host().compile_module_to_jit(...)`
//! ([`crate::Compiler::for_host`] followed by
//! [`crate::Compiler::compile_module_to_jit`]). That path registers dynamic
//! `RUNTIME_FUNCTION` / `UNWIND_INFO` tables with the Windows unwinder before
//! returning callable code. Raw [`JitCompiler::compile_raw`] input is untagged
//! AArch64 MachIR, so nonempty Windows x64 input fails even earlier with
//! [`JitError::RawJitTargetMismatch`].
//!
//! This repository does not provide a hosted Linux workflow; manual smoke
//! testing on a Linux host is the intended verification route.
//!
//! # Raw lookup vs product dispatch
//!
//! The raw lookup APIs on [`ExecutableBuffer`] are a low-level ABI
//! compatibility surface for wrapper internals, focused ABI regression tests,
//! fuzzing, and explicitly non-promoting/profile-only probes. They are not
//! the product dispatch contract for external `ay` or `ty` native
//! execution, and raw pointer lookup alone must not be cited as installable
//! product evidence.
//!
//! Product dispatch must validate a manifest-backed
//! [`SymbolLookupContract`] before native execution. Callers that own an
//! installed compile-service artifact must use
//! [`crate::compile_service::InstalledArtifact::get_contract_symbol_bound`].
//! A bare [`ExecutableBuffer`] has no compiler-derived signature or installed
//! artifact binding authority and therefore exposes no public product lookup.
//!
//! ```text
//! let typed = installed.get_contract_symbol_bound::<extern "C" fn(i64) -> i64>(
//!     &manifest,
//!     &contract,
//! )?;
//! let entry = unsafe {
//!     // SAFETY: the SymbolLookupContract and manifest were validated above.
//!     typed.into_fn()
//! };
//! ```
//!
//! # Calling convention for JIT-compiled symbols (low-level ABI contract)
//!
//! Low-level callers may convert a symbol pointer returned by
//! [`ExecutableBuffer::get_fn_ptr_bound`] / [`ExecutableBuffer::get_fn_bound`]
//! into an `extern "C" fn(...)` pointer whose signature matches the trust_ir
//! function type, and invoke it directly from Rust. No wrapper, trampoline,
//! stack-alignment shim, or shadow-stack management is required beyond what
//! the compiled function itself already performs in its prologue/epilogue.
//! For product `ay`/`ty` dispatch, this raw ABI compatibility is necessary
//! but not sufficient; the manifest-backed contract path above is required.
//!
//! This is a P0 low-level compatibility contract. Any silent change to this
//! contract (e.g. a future optimization that allocates across callee-saved
//! registers without saving them, or that deviates from the host ABI's
//! argument / return conventions) **must** be gated behind an opt-in and
//! documented here. Breaking it silently is a P0 regression.
//!
//! ## AArch64 (macOS and Linux): Apple DarwinPCS / AAPCS64
//!
//! Source of truth: [`trust_cg_lower::abi::AppleAArch64ABI`], with register
//! definitions in [`trust_cg_ir::aarch64_regs`] and
//! [`trust_cg_ir::regs`]. We implement Apple DarwinPCS, which is the
//! AAPCS64 base with Apple deltas (X18 reserved, frame pointer mandatory,
//! variadic arguments always on the stack, 16-byte SP alignment).
//!
//! Standard Linux aarch64 targets the same AAPCS64 base but with a
//! register-and-stack `va_list` layout. The fixed-argument contract
//! below is identical on both OSes, so `extern "C" fn` transmute is
//! sound on either host for non-variadic signatures. Variadic signatures
//! work today on Apple only (see "Deviations & gaps" below).
//!
//! - Integer / pointer / `bool` arguments:  `X0..=X7`, then stack.
//! - `i128` arguments:                      consecutive GPR pair
//!                                          `(X0,X1)`, `(X2,X3)`, …;
//!                                          overflow is 16-byte aligned
//!                                          on the stack.
//! - Floating-point `f32`/`f64` arguments:  `V0..=V7` (32-bit view
//!                                          `S0..=S7`, 64-bit view
//!                                          `D0..=D7`), then stack.
//! - `v128` / NEON arguments:               `V0..=V7`, then 16-byte
//!                                          aligned stack slots.
//! - Homogeneous Floating-point Aggregate
//!   (1–4 same-type `f32`/`f64` fields):    consecutive typed FPR
//!                                          sequence `S0..=S7` (F32 HFA)
//!                                          or `D0..=D7` (F64 HFA); all-
//!                                          or-nothing, falls back to the
//!                                          stack if the whole HFA cannot
//!                                          be placed.
//! - Small aggregate (≤ 8 bytes):           one GPR from `X0..=X7`.
//! - Medium aggregate (9–16 bytes):         caller places the value in
//!                                          memory and passes a pointer
//!                                          in the next free `X`.
//! - Large aggregate (> 16 bytes):          caller passes a pointer in
//!                                          the next free `X` (indirect).
//!
//! - Integer / pointer return:              `X0` (single), `(X0, X1)` for
//!                                          `i128`.
//! - FP / `v128` return:                    `V0`.
//! - HFA return (1–4 FP fields):            `S0..=S3` (F32) or
//!                                          `D0..=D3` (F64).
//! - Small aggregate return (≤ 8 bytes):    `X0`.
//! - Medium aggregate return (9–16 bytes):  `X0` + `X1` (record-pair).
//! - Struct return > 16 bytes (sret):       caller allocates the return
//!                                          buffer and passes its pointer
//!                                          in **`X8`** (not a hidden
//!                                          first `X0` argument). This
//!                                          matches AAPCS64 §6.9.
//!
//! - Callee-saved GPRs: `X19..=X28`, plus frame pointer `X29` (FP) and
//!   link register `X30` (LR). `X18` is reserved on Apple (platform
//!   register) and treated as call-clobbered.
//! - Callee-saved FPRs: `V8..=V15` (lower 64 bits only per AAPCS64; the
//!   upper half is call-clobbered).
//! - Call-clobbered GPRs: `X0..=X18`.
//! - Call-clobbered FPRs: `V0..=V7`, `V16..=V31`.
//! - Stack pointer: 16-byte aligned at every public entry and at every
//!   call site; enforced by the prologue (see `trust-cg-codegen/src/frame.rs`).
//!
//! ## x86-64 Unix (Linux and macOS): System V AMD64 ABI
//!
//! Source of truth: [`trust_cg_lower::x86_64_isel`] (formal-argument,
//! call, and return lowering), with register definitions in
//! [`trust_cg_ir::x86_64_regs`].
//!
//! - Integer / pointer arguments:           `RDI, RSI, RDX, RCX, R8, R9`,
//!                                          then stack at `[RBP+16]`,
//!                                          `[RBP+24]`, …
//! - FP `f32`/`f64` arguments:              `XMM0..=XMM7`, then stack.
//! - Variadic: `AL` holds the count of XMM argument registers used
//!   (0–8) at the call site, matching the System V requirement.
//!
//! - Integer / pointer return:              `RAX` (and `RDX` for the
//!                                          second integer return slot).
//! - FP return:                             `XMM0` (and `XMM1` for the
//!                                          second FP return slot).
//!
//! - Callee-saved GPRs: `RBX, RBP, R12, R13, R14, R15`.
//! - Caller-saved (clobbered) GPRs: `RAX, RCX, RDX, RSI, RDI, R8, R9,
//!   R10, R11` (plus the implicit RSP/RIP changes from CALL/RET).
//! - All XMM registers (`XMM0..=XMM15`) are caller-saved on System V
//!   (unlike Windows x64 where `XMM6..=XMM15` are callee-saved).
//! - Stack: 16-byte aligned at every call boundary.
//!
//! ## x86-64 Windows: Microsoft x64 ABI
//!
//! Source of truth: [`trust_cg_lower::x86_64_isel`] with
//! [`X86CallAbi::WindowsX64`](trust_cg_lower::x86_64_isel::X86CallAbi::WindowsX64).
//!
//! - Integer / pointer arguments:           `RCX, RDX, R8, R9` by argument
//!                                          position, then stack after the
//!                                          32-byte caller shadow area.
//! - FP `f32`/`f64` arguments:              `XMM0..=XMM3` by argument
//!                                          position, then stack.
//! - Variadic: FP values in the first four argument positions are duplicated
//!   into the matching integer register, matching the Microsoft x64 varargs
//!   rule.
//!
//! - Integer / pointer return:              `RAX` (and `RDX` for the
//!                                          second integer return slot).
//! - FP return:                             `XMM0` (and `XMM1` for the
//!                                          second FP return slot).
//! - Aggregate return > 8 bytes:            caller allocates the return
//!                                          buffer, passes it as a hidden
//!                                          first pointer in `RCX`, and the
//!                                          callee returns the same pointer in
//!                                          `RAX`.
//!
//! - Callee-saved GPRs: `RBX, RBP, RDI, RSI, R12, R13, R14, R15`.
//! - Callee-saved XMM registers: `XMM6..=XMM15`. The x86-64 pipeline may
//!   allocate them and emits 128-bit save/restore slots when it does.
//! - Stack: 16-byte aligned at every call boundary; callers reserve 32 bytes
//!   of shadow/home space for every call. There is no red zone.
//! - Unwind registration: [`crate::Compiler`] / trust_ir JIT registers Windows x64
//!   dynamic unwind tables for supported generated code. Windows callers with
//!   non-empty modules should use
//!   `Compiler::for_host().compile_module_to_jit(...)`
//!   ([`crate::Compiler::for_host`] followed by
//!   [`crate::Compiler::compile_module_to_jit`]) or
//!   [`crate::CompilerConfig::for_host_jit`] with the typed trust_ir/module JIT
//!   API. Raw [`JitCompiler::compile_raw`] currently fails closed on non-empty
//!   Windows x64 input that passes earlier raw validation because raw
//!   [`MachFunction`](trust_cg_ir::function::MachFunction) input does not include
//!   validated `RUNTIME_FUNCTION` / `UNWIND_INFO` metadata.
//!
//! ## x86-64 aggregate support boundary
//!
//! x86-64 currently has two JIT entry points with different aggregate
//! surfaces:
//!
//! - [`crate::Compiler`] / trust_ir JIT enters the typed x86-64 ISel path. It
//!   supports large aggregate returns by hidden pointer on both x86-64 ABIs,
//!   exact single integer-lane aggregate returns/formals/call-results/by-value
//!   arguments (`I8`/`I16`/`I32`/`I64`) in one integer register, exact SysV
//!   `Struct([I64, I64])` /
//!   `Array(I64, 2)` aggregate returns/call-results/formals/by-value call
//!   arguments in the integer register sequences, and exact SysV two-eightbyte
//!   scalar `I64`/`F64` aggregate combinations such as `Struct([F64, F64])`,
//!   `Array(F64, 2)`, `Struct([I64, F64])`, and `Struct([F64, I64])` in the
//!   ABI-selected GPR/XMM register sequences. Windows x64 exact
//!   `Struct([I64, I64])` / `Array(I64, 2)` formals and by-value call
//!   arguments by reference. Windows x64 aggregate returns/call-results larger
//!   than 8 bytes use hidden pointer return. The current Windows 9-16 byte
//!   executable coverage starts with `Struct([I64, I64])`; other >8-byte
//!   return/call-result shapes also route through hidden pointer return once
//!   they pass typed lowering. Shapes that are unsupported in their ABI
//!   position, including single-lane SSE aggregates and non-exact sub-`I64`
//!   multi-field integer by-value/formal aggregates, are rejected by
//!   `trust_cg_lower::x86_64_isel` before executable code is published.
//! - [`JitCompiler::compile_raw`] accepts already-selected, untagged AArch64
//!   [`MachFunction`] bodies. Nonempty x86-64 calls are rejected with
//!   [`JitError::RawJitTargetMismatch`]; raw callers must enter through the
//!   typed compiler path for architecture-specific lowering.
//!
//! Scalar and pointer signatures follow the active host ABI.
//!
//! ## What low-level "transmute is sound" means here
//!
//! An internal harness or legacy wrapper may write:
//!
//! ```text
//! let buf: trust_cg_codegen::ExecutableBuffer = /* from JitCompiler */;
//! let f: extern "C" fn(i64, i64) -> i64 =
//!     *unsafe { buf.get_fn_bound("add").expect("add") }.as_ref();
//! assert_eq!(f(3, 4), 7);
//! ```
//!
//! This is sound **iff** the trust_ir signature of `"add"` is `(i64, i64) -> i64`
//! and the host is one of the supported `(arch, os)` tuples. The
//! test suite in `crates/trust-cg-codegen/tests/jit_integration.rs` already
//! uses this exact pattern for over 20 integration tests (search for
//! `extern "C" fn` in that file); those tests act as the regression
//! guard on this contract. Any codegen change that breaks them is a
//! breaking ABI change.
//!
//! This raw form does not validate artifact identity, proof policy,
//! target/layout compatibility, or downstream invalidation state. Product
//! callers must enter through a compile-service
//! [`crate::compile_service::InstalledArtifact`] and its manifest-backed
//! [`crate::compile_service::InstalledArtifact::get_contract_symbol_bound`]
//! before converting to a callable function.
//!
//! The `get_fn` / `get_fn_bound` APIs `assert_eq!` that `size_of::<F>()
//! == size_of::<*const u8>()`, which gives a runtime check that `F` is
//! a pointer-sized type (i.e. a single function pointer, not a closure
//! or a wide pointer). The caller is still responsible for signature
//! compatibility.
//!
//! ## Deviations & gaps from the host C ABI
//!
//! As of today (2026-05-01) the only known gaps are in partial feature
//! coverage, **not** in ABI deviation. For every signature the backend
//! actually accepts, the emitted code matches the host C ABI.
//!
//! - **Variadic functions on non-Apple aarch64:** the `va_list` lowering
//!   in `trust-cg-lower/src/va_list.rs` implements the Apple DarwinPCS
//!   shape (`va_list` is a plain `char*` into the stack argument area),
//!   not the Linux AAPCS64 five-field struct. Non-variadic signatures
//!   are unaffected and remain ABI-compatible on Linux aarch64.
//! - **SIMD / `v128` return values** use `V0` (aarch64) / `XMM0` (x86-64)
//!   as a full vector register, not split across integer registers. This
//!   matches both host ABIs.
//! - **Struct return > 16 bytes (aarch64):** uses `X8` (sret), not a
//!   hidden first `X0` argument. This matches AAPCS64 §6.9.
//! - **x86-64 aggregate support boundary:** the typed [`crate::Compiler`]
//!   trust_ir JIT supports large aggregate returns via hidden sret, exact single
//!   integer-lane aggregate returns/formals/call-results/by-value arguments,
//!   SysV exact two-eightbyte scalar `I64`/`F64` aggregate lanes in the
//!   ABI-selected GPR/XMM register sequences, and Windows x64 9-16 byte
//!   aggregate returns/call-results via hidden sret. Windows x64 exact
//!   `Struct([I64, I64])` / `Array(I64, 2)` formals and by-value call
//!   arguments use the host ABI's by-reference passing. Other unsupported
//!   aggregate shapes fail closed in `trust_cg_lower::x86_64_isel`.
//!   [`JitCompiler::compile_raw`] accepts AArch64 `MachFunction` input only;
//!   nonempty calls on x86-64 fail with [`JitError::RawJitTargetMismatch`]
//!   before encoding. The typed [`crate::Compiler`] x86-64 JIT is the supported
//!   architecture-aware route.
//!
//! If you find a real deviation from the host C ABI while reading the
//! lowering or codegen code, that is a P0 bug — file an issue and
//! update this section in the same commit.
//!
//! # Profile counter & timing-cell lifetime (issues #478, #364, #494)
//!
//! When the JIT is configured with an implemented
//! [`ProfileHookMode`] above `None` — specifically
//! [`ProfileHookMode::CallCounts`], AArch64
//! [`ProfileHookMode::CallCountsAndTiming`],
//! [`ProfileHookMode::BlockCounts`] or
//! [`ProfileHookMode::BlockCountsAndTiming`] — the codegen phase emits
//! trampolines whose literal pools hold **raw `*const AtomicU64` pointers**
//! into per-function or per-block counter cells (and, under
//! `BlockCountsAndTiming`, a single buffer-wide `*mut TimingState`). The
//! pointees are `Box<AtomicU64>` / `Box<BlockTimingCell>` /
//! `Box<TimingState>` allocations owned by the [`ExecutableBuffer`].
//!
//! The raw [`JitCompiler::compile_raw`] profiling surface is AArch64-only for
//! nonempty input. The higher-level [`crate::Compiler`] trust_ir JIT path is
//! separate and supports x86-64 [`ProfileHookMode::BlockCounts`] through its
//! architecture-specific encoder.
//!
//! The lifetime invariant is:
//!
//! > **Every counter allocation, every timing-cell allocation, and the
//! > single timing state allocation must outlive the executable mapping
//! > they are referenced from.**
//!
//! This is guaranteed structurally, not by convention, because:
//!
//! 1. The `Box` allocations live in
//!    [`ExecutableBuffer::counters`] / `timing_cells` /
//!    `timing_state` — fields of the same buffer that owns the mmap'd
//!    `memory`.
//! 2. `Box<T>` pins its heap address: a counter's address is fixed from
//!    allocation to drop regardless of `HashMap` resize, insertion, or
//!    iteration. The trampoline's literal pool can therefore cache the
//!    address at compile time and read / write it indefinitely.
//! 3. `impl Drop for ExecutableBuffer` runs in the order:
//!    `munmap(memory)` first (user `Drop::drop`), then Rust-driven field
//!    drops in declaration order. Because `memory` is dropped before
//!    `counters` / `timing_cells` / `timing_state`, the executable code —
//!    which is the **only** holder of raw counter pointers — is unmapped
//!    strictly before any counter Box is dropped. There is therefore no
//!    window in which the trampoline can execute against a freed counter.
//!
//! The hazardous case is **not** counter-lifetime vs buffer-lifetime
//! (structural, as above) but **buffer-lifetime vs in-flight JIT call**:
//! if a caller drops the [`ExecutableBuffer`] while another thread is
//! inside a JIT-compiled function, the `munmap` invalidates the text
//! pages (and the embedded counter pointers) mid-call, producing the
//! same use-after-free hazard described for
//! [`ExecutableBuffer::get_fn_ptr`] / [`ExecutableBuffer::get_fn`]. The
//! mitigation is identical: prefer the lifetime-bound
//! [`ExecutableBuffer::get_fn_bound`] / [`ExecutableBuffer::get_fn_ptr_bound`]
//! APIs, or wrap the buffer in `Arc<ExecutableBuffer>` and only drop it
//! after every call has returned. See the `SAFETY` note on
//! [`ExecutableBuffer`]'s `Send`/`Sync` impls and issue #355 for the
//! legacy-API hazard, and #478 / #364 / #494 for the counter extensions.
//!
//! ## Cross-references
//!
//! - [`trust_cg_lower::abi::AppleAArch64ABI`] — aarch64 parameter/return classifier.
//! - [`trust_cg_lower::x86_64_isel`] — x86-64 formal arg / call / return lowering.
//! - `crates/trust-cg-codegen/src/frame.rs` — aarch64 prologue/epilogue,
//!   SP alignment, callee-saved area.
//! - `crates/trust-cg-codegen/tests/jit_integration.rs` — live regression
//!   tests that exercise `transmute` to `extern "C" fn` for scalar,
//!   call-through-host, and host-callback signatures.
//! - `crates/trust-cg-codegen/tests/jit_x86_64_aggregate_abi_fail_closed.rs`
//!   - x86-64 aggregate ABI support and fail-closed regression coverage.
//! - Sibling instruction / pattern work: `#429` (SMULH opcode + isel)
//!   and `#430` (recognize ADDS+B.VS idiom from trust_ir i128 overflow).
//! - Upstream tracker: `#431`.

use std::collections::HashMap;
use std::marker::PhantomData;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};
use thiserror::Error;

use crate::jit_contract::{
    ArtifactContractError, ArtifactManifestV1, SymbolLookupContract, TypedSymbol,
};
use crate::macho::fixup::{Fixup, FixupTarget};
#[cfg(target_arch = "aarch64")]
use crate::pipeline::encode_function_with_fixups_and_blocks;
use crate::pipeline::{
    DispatchVerifyMode, OptLevel, Pipeline, PipelineConfig, PipelineError,
    encode_function_with_fixups,
};
use trust_cg_ir::function::MachFunction as IrMachFunction;
#[cfg(target_arch = "aarch64")]
use trust_cg_ir::types::BlockId;

// ---------------------------------------------------------------------------
// Raw syscall interface for executable memory management.
// ---------------------------------------------------------------------------
mod sys {
    const PROT_READ: i32 = 1;
    const PROT_WRITE: i32 = 2;
    const PROT_EXEC: i32 = 4;
    pub(in crate::jit) const RW: i32 = PROT_READ | PROT_WRITE;
    pub(in crate::jit) const RX: i32 = PROT_READ | PROT_EXEC;

    /// W^X invariant (JIT-7): the only protections this module will ever
    /// request for a JIT mapping are `RW` (write phase) and `RX` (published
    /// phase). A protection value that is simultaneously writable and
    /// executable is a hard programming error, never a fallback.
    pub(in crate::jit) const fn prot_is_w_xor_x(prot: i32) -> bool {
        prot == RW || prot == RX
    }

    /// Assert the W^X discipline on every mmap/mprotect request. This is an
    /// always-on `assert!` (not `debug_assert!`): the protection arguments
    /// are compile-time constants at every call site, so the check is free
    /// in practice and fail-closed if a future call site regresses.
    #[track_caller]
    pub(in crate::jit) fn assert_w_xor_x(prot: i32) {
        assert!(
            prot_is_w_xor_x(prot),
            "W^X violation: requested JIT page protection {prot:#x} is neither RW ({RW:#x}) nor RX ({RX:#x}); \
             writable+executable mappings are forbidden"
        );
    }

    pub(crate) const fn host_supported() -> bool {
        cfg!(any(
            all(target_arch = "aarch64", target_os = "macos"),
            all(target_arch = "aarch64", target_os = "linux"),
            all(target_arch = "x86_64", target_os = "macos"),
            all(target_arch = "x86_64", target_os = "linux"),
            all(target_arch = "x86_64", target_os = "windows"),
        ))
    }

    // -- AArch64 macOS (Apple Silicon) -----------------------------------------
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    mod platform {
        // macOS Mach syscall numbers (via XNU sys/syscall.h)
        pub(super) const SYS_MMAP: u64 = 197;
        pub(super) const SYS_MUNMAP: u64 = 73;
        pub(super) const SYS_MPROTECT: u64 = 74;
        // MAP_PRIVATE | MAP_ANONYMOUS | MAP_JIT
        pub(super) const MAP_FLAGS: i32 = 0x0002 | 0x1000 | 0x0800;
        pub(super) const PAGE_SIZE: usize = 16384; // Apple Silicon
    }

    // -- AArch64 Linux ---------------------------------------------------------
    #[cfg(all(target_arch = "aarch64", target_os = "linux"))]
    mod platform {
        // Linux AArch64 syscall numbers
        pub(super) const SYS_MMAP: u64 = 222;
        pub(super) const SYS_MUNMAP: u64 = 215;
        pub(super) const SYS_MPROTECT: u64 = 226;
        pub(super) const MAP_FLAGS: i32 = 0x0002 | 0x0020; // MAP_PRIVATE | MAP_ANONYMOUS
        pub(super) const PAGE_SIZE: usize = 4096;
    }

    // -- x86-64 macOS ----------------------------------------------------------
    #[cfg(all(target_arch = "x86_64", target_os = "macos"))]
    mod platform {
        // macOS x86-64 syscall numbers use 0x2000000 prefix (BSD class).
        // Reference: XNU bsd/kern/syscalls.master
        pub(super) const SYS_MMAP: u64 = 0x2000000 + 197;
        pub(super) const SYS_MUNMAP: u64 = 0x2000000 + 73;
        pub(super) const SYS_MPROTECT: u64 = 0x2000000 + 74;
        // MAP_PRIVATE | MAP_ANONYMOUS (no MAP_JIT needed on x86-64)
        pub(super) const MAP_FLAGS: i32 = 0x0002 | 0x1000;
        pub(super) const PAGE_SIZE: usize = 4096; // x86-64 uses 4K pages
    }

    // -- x86-64 Linux ----------------------------------------------------------
    #[cfg(all(target_arch = "x86_64", target_os = "linux"))]
    mod platform {
        // Linux x86-64 syscall numbers (via asm/unistd_64.h)
        pub(super) const SYS_MMAP: u64 = 9;
        pub(super) const SYS_MUNMAP: u64 = 11;
        pub(super) const SYS_MPROTECT: u64 = 10;
        pub(super) const MAP_FLAGS: i32 = 0x0002 | 0x0020; // MAP_PRIVATE | MAP_ANONYMOUS
        pub(super) const PAGE_SIZE: usize = 4096;
    }

    // -- x86-64 Windows --------------------------------------------------------
    #[cfg(all(target_arch = "x86_64", target_os = "windows"))]
    #[allow(dead_code)]
    mod platform {
        pub(super) const SYS_MMAP: u64 = 0;
        pub(super) const SYS_MUNMAP: u64 = 0;
        pub(super) const SYS_MPROTECT: u64 = 0;
        pub(super) const MAP_FLAGS: i32 = 0;
        pub(super) const PAGE_SIZE: usize = 4096;
    }

    // -- Unsupported (arch, os) ------------------------------------------------
    // Keep non-JIT codegen buildable on secondary hosts. `compile_raw_inner`
    // returns `JitError::UnsupportedHost` before these constants can be used
    // for a real mapping, but the stubs below let the public crate type-check.
    #[cfg(not(any(
        all(target_arch = "aarch64", target_os = "macos"),
        all(target_arch = "aarch64", target_os = "linux"),
        all(target_arch = "x86_64", target_os = "macos"),
        all(target_arch = "x86_64", target_os = "linux"),
        all(target_arch = "x86_64", target_os = "windows"),
    )))]
    mod platform {
        pub(super) const SYS_MMAP: u64 = 0;
        pub(super) const SYS_MUNMAP: u64 = 0;
        pub(super) const SYS_MPROTECT: u64 = 0;
        pub(super) const MAP_FLAGS: i32 = 0;
        pub(super) const PAGE_SIZE: usize = 4096;
    }

    #[cfg_attr(all(target_arch = "x86_64", target_os = "windows"), allow(dead_code))]
    const SYS_MMAP: u64 = platform::SYS_MMAP;
    #[cfg_attr(all(target_arch = "x86_64", target_os = "windows"), allow(dead_code))]
    const SYS_MUNMAP: u64 = platform::SYS_MUNMAP;
    #[cfg_attr(all(target_arch = "x86_64", target_os = "windows"), allow(dead_code))]
    const SYS_MPROTECT: u64 = platform::SYS_MPROTECT;
    #[cfg_attr(all(target_arch = "x86_64", target_os = "windows"), allow(dead_code))]
    const MAP_FLAGS: i32 = platform::MAP_FLAGS;
    pub(in crate::jit) const PAGE_SIZE: usize = platform::PAGE_SIZE;

    // -- Syscall result type ---------------------------------------------------
    // macOS/XNU signals syscall errors via the carry flag (CPSR.C on AArch64,
    // CF on x86-64), NOT via a negative return value (that's the Linux
    // convention). When carry is set, x0/rax contains the positive errno.
    // We capture carry into `err` so callers can correctly distinguish
    // success from failure for all syscalls (not just mmap).
    #[cfg_attr(all(target_arch = "x86_64", target_os = "windows"), allow(dead_code))]
    struct SyscallResult {
        val: i64,
        /// 1 if carry flag was set (error), 0 otherwise.
        /// On Linux this is always 0 — we use the traditional negative-return
        /// check in `check_error`, so `err` is read only on macOS. The
        /// `#[allow(dead_code)]` is conditional on the Linux build where
        /// the field is dead; on macOS it is actively consumed and the
        /// allow has no effect. Keeping the field shape identical across
        /// platforms lets every syscall wrapper construct the same struct
        /// without cfg-gating every call site. (Issue #346.)
        #[cfg_attr(not(target_os = "macos"), allow(dead_code))]
        err: u64,
    }

    // -- AArch64 macOS raw syscall wrappers ------------------------------------
    // AArch64 ABI: syscall number in x16, args in x0-x5, return in x0.
    // Error convention: carry flag (CPSR.C) set on error, x0 = positive errno.
    // Instruction: svc #0x80, then cset to capture carry.
    //
    // CLOBBERS: XNU's arm64 return path writes retval[0] into x0 AND
    // retval[1] into x1 — x1 is NOT preserved across `svc #0x80` (observed:
    // the kernel zeroes it even for single-value syscalls like mmap). Every
    // argument register must therefore be declared `inout(...) => _` rather
    // than `in(...)`, or LLVM may reuse a stale pre-syscall value (this
    // corrupted MappedRegion.len when mmap's `len` arg in x1 read back as 0).
    // x2-x5 are preserved by the current kernel, but we clobber them too as
    // defense in depth against future kernel/ABI drift.

    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    unsafe fn syscall6(
        nr: u64,
        a0: u64,
        a1: u64,
        a2: u64,
        a3: u64,
        a4: u64,
        a5: u64,
    ) -> SyscallResult {
        let val: i64;
        let err: u64;
        // SAFETY (caller-upheld): `unsafe fn` contract delegates raw-syscall
        // responsibility (valid fd/addr/prot args) to the caller; the inline
        // `svc #0x80` itself only uses registers and sets the carry flag.
        unsafe {
            core::arch::asm!(
                "svc #0x80",
                "cset {err}, cs",
                err = out(reg) err,
                in("x16") nr,
                inout("x0") a0 => val,
                inout("x1") a1 => _,
                inout("x2") a2 => _,
                inout("x3") a3 => _,
                inout("x4") a4 => _,
                inout("x5") a5 => _,
                options(nostack),
            );
        }
        SyscallResult { val, err }
    }

    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    unsafe fn syscall3(nr: u64, a0: u64, a1: u64, a2: u64) -> SyscallResult {
        let val: i64;
        let err: u64;
        // SAFETY: see `syscall6` above — same caller contract applies.
        unsafe {
            core::arch::asm!(
                "svc #0x80",
                "cset {err}, cs",
                err = out(reg) err,
                in("x16") nr,
                inout("x0") a0 => val,
                inout("x1") a1 => _,
                inout("x2") a2 => _,
                options(nostack),
            );
        }
        SyscallResult { val, err }
    }

    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    unsafe fn syscall2(nr: u64, a0: u64, a1: u64) -> SyscallResult {
        let val: i64;
        let err: u64;
        // SAFETY: see `syscall6` above — same caller contract applies.
        unsafe {
            core::arch::asm!(
                "svc #0x80",
                "cset {err}, cs",
                err = out(reg) err,
                in("x16") nr,
                inout("x0") a0 => val,
                inout("x1") a1 => _,
                options(nostack),
            );
        }
        SyscallResult { val, err }
    }

    // -- AArch64 Linux raw syscall wrappers ------------------------------------
    // Linux AArch64: negative return = -errno. No carry flag convention.

    #[cfg(all(target_arch = "aarch64", target_os = "linux"))]
    unsafe fn syscall6(
        nr: u64,
        a0: u64,
        a1: u64,
        a2: u64,
        a3: u64,
        a4: u64,
        a5: u64,
    ) -> SyscallResult {
        let val: i64;
        // SAFETY: see macOS `syscall6` — same caller contract applies.
        unsafe {
            core::arch::asm!(
                "svc #0",
                in("x8") nr,
                inout("x0") a0 => val,
                in("x1") a1,
                in("x2") a2,
                in("x3") a3,
                in("x4") a4,
                in("x5") a5,
                options(nostack),
            );
        }
        SyscallResult { val, err: 0 }
    }

    #[cfg(all(target_arch = "aarch64", target_os = "linux"))]
    unsafe fn syscall3(nr: u64, a0: u64, a1: u64, a2: u64) -> SyscallResult {
        let val: i64;
        // SAFETY: see macOS `syscall6` — same caller contract applies.
        unsafe {
            core::arch::asm!(
                "svc #0",
                in("x8") nr,
                inout("x0") a0 => val,
                in("x1") a1,
                in("x2") a2,
                options(nostack),
            );
        }
        SyscallResult { val, err: 0 }
    }

    #[cfg(all(target_arch = "aarch64", target_os = "linux"))]
    unsafe fn syscall2(nr: u64, a0: u64, a1: u64) -> SyscallResult {
        let val: i64;
        // SAFETY: see macOS `syscall6` — same caller contract applies.
        unsafe {
            core::arch::asm!(
                "svc #0",
                in("x8") nr,
                inout("x0") a0 => val,
                in("x1") a1,
                options(nostack),
            );
        }
        SyscallResult { val, err: 0 }
    }

    // -- x86-64 macOS raw syscall wrappers -------------------------------------
    // x86-64 macOS: syscall number in rax, args in rdi/rsi/rdx/r10/r8/r9.
    // Return in rax. Clobbers rcx and r11.
    // Error convention: carry flag (CF) set on error, rax = positive errno.

    #[cfg(all(target_arch = "x86_64", target_os = "macos"))]
    unsafe fn syscall6(
        nr: u64,
        a0: u64,
        a1: u64,
        a2: u64,
        a3: u64,
        a4: u64,
        a5: u64,
    ) -> SyscallResult {
        let val: i64;
        let err: u64;
        // SAFETY: see aarch64 macOS `syscall6` — same caller contract applies.
        unsafe {
            core::arch::asm!(
                "syscall",
                "setc {err_byte}",
                "movzx {err}, {err_byte}",
                err_byte = out(reg_byte) _,
                err = out(reg) err,
                inout("rax") nr as i64 => val,
                in("rdi") a0,
                in("rsi") a1,
                in("rdx") a2,
                in("r10") a3,
                in("r8") a4,
                in("r9") a5,
                out("rcx") _,
                out("r11") _,
                options(nostack),
            );
        }
        SyscallResult { val, err }
    }

    #[cfg(all(target_arch = "x86_64", target_os = "macos"))]
    unsafe fn syscall3(nr: u64, a0: u64, a1: u64, a2: u64) -> SyscallResult {
        let val: i64;
        let err: u64;
        // SAFETY: see aarch64 macOS `syscall6` — same caller contract applies.
        unsafe {
            core::arch::asm!(
                "syscall",
                "setc {err_byte}",
                "movzx {err}, {err_byte}",
                err_byte = out(reg_byte) _,
                err = out(reg) err,
                inout("rax") nr as i64 => val,
                in("rdi") a0,
                in("rsi") a1,
                in("rdx") a2,
                out("rcx") _,
                out("r11") _,
                options(nostack),
            );
        }
        SyscallResult { val, err }
    }

    #[cfg(all(target_arch = "x86_64", target_os = "macos"))]
    unsafe fn syscall2(nr: u64, a0: u64, a1: u64) -> SyscallResult {
        let val: i64;
        let err: u64;
        // SAFETY: see aarch64 macOS `syscall6` — same caller contract applies.
        unsafe {
            core::arch::asm!(
                "syscall",
                "setc {err_byte}",
                "movzx {err}, {err_byte}",
                err_byte = out(reg_byte) _,
                err = out(reg) err,
                inout("rax") nr as i64 => val,
                in("rdi") a0,
                in("rsi") a1,
                out("rcx") _,
                out("r11") _,
                options(nostack),
            );
        }
        SyscallResult { val, err }
    }

    // -- x86-64 Linux raw syscall wrappers -------------------------------------
    // Linux x86-64: negative return = -errno. No carry flag convention.

    #[cfg(all(target_arch = "x86_64", target_os = "linux"))]
    unsafe fn syscall6(
        nr: u64,
        a0: u64,
        a1: u64,
        a2: u64,
        a3: u64,
        a4: u64,
        a5: u64,
    ) -> SyscallResult {
        let val: i64;
        // SAFETY: see aarch64 macOS `syscall6` — same caller contract applies.
        unsafe {
            core::arch::asm!(
                "syscall",
                inout("rax") nr as i64 => val,
                in("rdi") a0,
                in("rsi") a1,
                in("rdx") a2,
                in("r10") a3,
                in("r8") a4,
                in("r9") a5,
                out("rcx") _,
                out("r11") _,
                options(nostack),
            );
        }
        SyscallResult { val, err: 0 }
    }

    #[cfg(all(target_arch = "x86_64", target_os = "linux"))]
    unsafe fn syscall3(nr: u64, a0: u64, a1: u64, a2: u64) -> SyscallResult {
        let val: i64;
        // SAFETY: see aarch64 macOS `syscall6` — same caller contract applies.
        unsafe {
            core::arch::asm!(
                "syscall",
                inout("rax") nr as i64 => val,
                in("rdi") a0,
                in("rsi") a1,
                in("rdx") a2,
                out("rcx") _,
                out("r11") _,
                options(nostack),
            );
        }
        SyscallResult { val, err: 0 }
    }

    #[cfg(all(target_arch = "x86_64", target_os = "linux"))]
    unsafe fn syscall2(nr: u64, a0: u64, a1: u64) -> SyscallResult {
        let val: i64;
        // SAFETY: see aarch64 macOS `syscall6` — same caller contract applies.
        unsafe {
            core::arch::asm!(
                "syscall",
                inout("rax") nr as i64 => val,
                in("rdi") a0,
                in("rsi") a1,
                out("rcx") _,
                out("r11") _,
                options(nostack),
            );
        }
        SyscallResult { val, err: 0 }
    }

    #[cfg(not(any(
        all(target_arch = "aarch64", target_os = "macos"),
        all(target_arch = "aarch64", target_os = "linux"),
        all(target_arch = "x86_64", target_os = "macos"),
        all(target_arch = "x86_64", target_os = "linux"),
        all(target_arch = "x86_64", target_os = "windows"),
    )))]
    unsafe fn syscall6(
        _nr: u64,
        _a0: u64,
        _a1: u64,
        _a2: u64,
        _a3: u64,
        _a4: u64,
        _a5: u64,
    ) -> SyscallResult {
        SyscallResult { val: -1, err: 0 }
    }

    #[cfg(not(any(
        all(target_arch = "aarch64", target_os = "macos"),
        all(target_arch = "aarch64", target_os = "linux"),
        all(target_arch = "x86_64", target_os = "macos"),
        all(target_arch = "x86_64", target_os = "linux"),
        all(target_arch = "x86_64", target_os = "windows"),
    )))]
    unsafe fn syscall3(_nr: u64, _a0: u64, _a1: u64, _a2: u64) -> SyscallResult {
        SyscallResult { val: -1, err: 0 }
    }

    #[cfg(not(any(
        all(target_arch = "aarch64", target_os = "macos"),
        all(target_arch = "aarch64", target_os = "linux"),
        all(target_arch = "x86_64", target_os = "macos"),
        all(target_arch = "x86_64", target_os = "linux"),
        all(target_arch = "x86_64", target_os = "windows"),
    )))]
    unsafe fn syscall2(_nr: u64, _a0: u64, _a1: u64) -> SyscallResult {
        SyscallResult { val: -1, err: 0 }
    }

    /// Check a syscall result for error.
    ///
    /// On macOS, errors are signaled via carry flag (captured in `res.err`).
    /// When carry is set, `res.val` contains the positive errno.
    ///
    /// On Linux, errors are signaled via negative return value (-errno).
    /// `res.err` is always 0 on Linux.
    #[cfg_attr(all(target_arch = "x86_64", target_os = "windows"), allow(dead_code))]
    fn check_error(res: &SyscallResult) -> Option<std::io::Error> {
        #[cfg(target_os = "macos")]
        {
            if res.err != 0 {
                // macOS: carry set, val is the positive errno
                return Some(std::io::Error::from_raw_os_error(res.val as i32));
            }
        }
        #[cfg(target_os = "linux")]
        {
            if res.val < 0 {
                // Linux: negative return = -errno
                return Some(std::io::Error::from_raw_os_error((-res.val) as i32));
            }
        }
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            None
        }
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        {
            let _ = res;
            Some(std::io::Error::new(
                std::io::ErrorKind::Unsupported,
                "trust-cg-codegen JIT executable memory is supported on macos/linux only",
            ))
        }
    }

    #[cfg(all(target_arch = "x86_64", target_os = "windows"))]
    mod windows {
        use core::ffi::c_void;

        pub(super) const MEM_COMMIT: u32 = 0x1000;
        pub(super) const MEM_RESERVE: u32 = 0x2000;
        pub(super) const MEM_RELEASE: u32 = 0x8000;
        pub(super) const PAGE_READWRITE: u32 = 0x04;
        pub(super) const PAGE_EXECUTE_READ: u32 = 0x20;

        #[repr(C)]
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub(in crate::jit) struct RuntimeFunction {
            pub(in crate::jit) begin_address: u32,
            pub(in crate::jit) end_address: u32,
            pub(in crate::jit) unwind_info_address: u32,
        }

        #[link(name = "kernel32")]
        unsafe extern "system" {
            pub(super) fn VirtualAlloc(
                lp_address: *mut c_void,
                dw_size: usize,
                fl_allocation_type: u32,
                fl_protect: u32,
            ) -> *mut c_void;
            pub(super) fn VirtualFree(
                lp_address: *mut c_void,
                dw_size: usize,
                dw_free_type: u32,
            ) -> i32;
            pub(super) fn VirtualProtect(
                lp_address: *mut c_void,
                dw_size: usize,
                fl_new_protect: u32,
                lpfl_old_protect: *mut u32,
            ) -> i32;
            pub(super) fn GetCurrentProcess() -> *mut c_void;
            pub(super) fn FlushInstructionCache(
                h_process: *mut c_void,
                lp_base_address: *const c_void,
                dw_size: usize,
            ) -> i32;
            pub(super) fn RtlAddFunctionTable(
                function_table: *mut RuntimeFunction,
                entry_count: u32,
                base_address: u64,
            ) -> u8;
            pub(super) fn RtlDeleteFunctionTable(function_table: *mut RuntimeFunction) -> u8;
        }
    }

    #[cfg(all(target_arch = "x86_64", target_os = "windows"))]
    pub(in crate::jit) use windows::RuntimeFunction as WindowsRuntimeFunction;

    #[cfg(all(target_arch = "x86_64", target_os = "windows"))]
    fn windows_protection(prot: i32) -> u32 {
        // W^X: only the two sanctioned protection states exist. The previous
        // `_ => PAGE_READWRITE` fallback silently accepted bogus protection
        // requests; fail closed instead (JIT-7 hardening).
        match prot {
            RW => windows::PAGE_READWRITE,
            RX => windows::PAGE_EXECUTE_READ,
            other => {
                unreachable!("W^X violation: unsupported Windows JIT protection request {other:#x}")
            }
        }
    }

    #[cfg(all(target_arch = "x86_64", target_os = "windows"))]
    pub(in crate::jit) unsafe fn mmap(len: usize, prot: i32) -> Result<*mut u8, std::io::Error> {
        assert_w_xor_x(prot);
        let ptr = unsafe {
            windows::VirtualAlloc(
                std::ptr::null_mut(),
                len,
                windows::MEM_RESERVE | windows::MEM_COMMIT,
                windows_protection(prot),
            )
        };
        if ptr.is_null() {
            Err(std::io::Error::last_os_error())
        } else {
            Ok(ptr as *mut u8)
        }
    }

    #[cfg(all(target_arch = "x86_64", target_os = "windows"))]
    pub(in crate::jit) unsafe fn munmap(addr: *mut u8, _len: usize) {
        let _ = unsafe { windows::VirtualFree(addr.cast(), 0, windows::MEM_RELEASE) };
    }

    #[cfg(all(target_arch = "x86_64", target_os = "windows"))]
    pub(in crate::jit) unsafe fn mprotect(
        addr: *mut u8,
        len: usize,
        prot: i32,
    ) -> Result<(), std::io::Error> {
        assert_w_xor_x(prot);
        let mut old_protect = 0u32;
        let ok = unsafe {
            windows::VirtualProtect(addr.cast(), len, windows_protection(prot), &mut old_protect)
        };
        if ok == 0 {
            Err(std::io::Error::last_os_error())
        } else {
            Ok(())
        }
    }

    #[cfg(not(all(target_arch = "x86_64", target_os = "windows")))]
    pub(in crate::jit) unsafe fn mmap(len: usize, prot: i32) -> Result<*mut u8, std::io::Error> {
        assert_w_xor_x(prot);
        // SAFETY: this `unsafe fn` wraps the raw mmap syscall; caller is
        // responsible for using the returned page correctly (see `ExecutableBuffer`).
        let res = unsafe {
            syscall6(
                SYS_MMAP,
                0, // addr: NULL (kernel chooses)
                len as u64,
                prot as u64,
                MAP_FLAGS as u64,
                u64::MAX, // fd: -1
                0,        // offset: 0
            )
        };
        if let Some(e) = check_error(&res) {
            Err(e)
        } else {
            Ok(res.val as *mut u8)
        }
    }

    #[cfg(not(all(target_arch = "x86_64", target_os = "windows")))]
    pub(in crate::jit) unsafe fn munmap(addr: *mut u8, len: usize) {
        // SAFETY: caller guarantees `addr`/`len` match a prior `mmap`.
        let _ = unsafe { syscall2(SYS_MUNMAP, addr as u64, len as u64) };
    }

    #[cfg(not(all(target_arch = "x86_64", target_os = "windows")))]
    pub(in crate::jit) unsafe fn mprotect(
        addr: *mut u8,
        len: usize,
        prot: i32,
    ) -> Result<(), std::io::Error> {
        assert_w_xor_x(prot);
        // SAFETY: caller guarantees `addr`/`len` name a valid mapping.
        let res = unsafe { syscall3(SYS_MPROTECT, addr as u64, len as u64, prot as u64) };
        if let Some(e) = check_error(&res) {
            Err(e)
        } else {
            Ok(())
        }
    }

    // Apple Silicon MAP_JIT mappings have a per-thread write/execute toggle:
    // write-protection enabled means executable and not writable; disabled
    // means writable and not executable. mprotect(RX) alone does not flip that
    // thread-local state, so callers must bracket all code writes and publish
    // only after returning to execute mode.
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    unsafe extern "C" {
        fn pthread_jit_write_protect_np(enabled: i32);
        fn pthread_jit_write_protect_supported_np() -> i32;
    }

    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    pub(crate) fn jit_write_protect_supported() -> bool {
        // SAFETY: libSystem exposes this process-local feature probe; it has
        // no side effects and takes no arguments.
        unsafe { pthread_jit_write_protect_supported_np() != 0 }
    }

    #[cfg(not(all(target_arch = "aarch64", target_os = "macos")))]
    pub(crate) fn jit_write_protect_supported() -> bool {
        false
    }

    pub(crate) const fn uses_map_jit() -> bool {
        cfg!(all(target_arch = "aarch64", target_os = "macos"))
    }

    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    pub(crate) unsafe fn set_jit_write_protect(enabled: bool) {
        if jit_write_protect_supported() {
            // SAFETY: toggles the current thread's MAP_JIT permission mode.
            // The caller controls when writes and execution are permitted.
            unsafe { pthread_jit_write_protect_np(i32::from(enabled)) };
        }
    }

    #[cfg(not(all(target_arch = "aarch64", target_os = "macos")))]
    pub(crate) unsafe fn set_jit_write_protect(_enabled: bool) {}

    pub(crate) struct JitWriteGuard {
        active: bool,
    }

    impl JitWriteGuard {
        pub(crate) fn enter() -> Self {
            // SAFETY: this guard is only created while the current thread is
            // about to write freshly mmap'd JIT pages. Drop restores execute
            // mode before any function pointer can be called.
            unsafe { set_jit_write_protect(false) };
            Self { active: true }
        }
    }

    impl Drop for JitWriteGuard {
        fn drop(&mut self) {
            if self.active {
                // SAFETY: re-enables execute mode for MAP_JIT pages on the
                // current thread. Non-Apple-Silicon targets are no-ops.
                unsafe { set_jit_write_protect(true) };
                self.active = false;
            }
        }
    }

    pub(in crate::jit) unsafe fn flush_icache(addr: *mut u8, len: usize) {
        #[cfg(target_arch = "aarch64")]
        {
            // Walk cache lines and invalidate. Line size = 64 bytes on Apple Silicon.
            let mut p = addr as usize;
            let end = p + len;
            // SAFETY: caller supplies a valid [addr, addr+len) range for the
            // just-written executable mapping; DC/IC/DSB/ISB are side-effect
            // free beyond the cache/barrier semantics they document.
            unsafe {
                while p < end {
                    core::arch::asm!(
                        "dc cvau, {addr}",   // Clean data cache to point of unification
                        addr = in(reg) p,
                        options(nostack),
                    );
                    p += 64;
                }
                core::arch::asm!("dsb ish", options(nostack)); // Data sync barrier
                p = addr as usize;
                while p < end {
                    core::arch::asm!(
                        "ic ivau, {addr}",   // Invalidate instruction cache
                        addr = in(reg) p,
                        options(nostack),
                    );
                    p += 64;
                }
                core::arch::asm!("dsb ish", options(nostack));
                core::arch::asm!("isb", options(nostack)); // Instruction sync barrier
            }
        }
        #[cfg(all(target_arch = "x86_64", target_os = "windows"))]
        {
            // Windows documents this as the required publication step after
            // generating executable code in-process.
            let _ = unsafe {
                windows::FlushInstructionCache(windows::GetCurrentProcess(), addr.cast(), len)
            };
        }
        #[cfg(all(target_arch = "x86_64", not(target_os = "windows")))]
        {
            // x86-64 has coherent instruction and data caches.
            // No cache flush needed after writing code to executable memory.
            let _ = (addr, len);
        }
    }

    #[cfg(all(target_arch = "x86_64", target_os = "windows"))]
    pub(in crate::jit) unsafe fn rtl_add_function_table(
        function_table: *mut WindowsRuntimeFunction,
        entry_count: u32,
        base_address: u64,
    ) -> bool {
        unsafe { windows::RtlAddFunctionTable(function_table, entry_count, base_address) != 0 }
    }

    #[cfg(all(target_arch = "x86_64", target_os = "windows"))]
    pub(in crate::jit) unsafe fn rtl_delete_function_table(
        function_table: *mut WindowsRuntimeFunction,
    ) -> bool {
        unsafe { windows::RtlDeleteFunctionTable(function_table) != 0 }
    }

    pub(in crate::jit) fn page_align(len: usize) -> usize {
        (len + PAGE_SIZE - 1) & !(PAGE_SIZE - 1)
    }
}

/// Ensure the current thread is ready to execute JIT code.
///
/// On Apple Silicon macOS, `MAP_JIT` mappings use a per-thread
/// write/execute mode. This enables JIT write protection, which makes those
/// mappings executable and not writable for the current thread. On other
/// supported hosts this is a no-op.
#[inline]
pub fn ensure_jit_execute_mode() {
    // SAFETY: enabling JIT write protection does not dereference memory or
    // grant write access; it only restores the current thread's execute mode.
    unsafe { sys::set_jit_write_protect(true) };
}

/// Windows x64 unwind registration input for one JIT-published function.
///
/// Offsets are relative to the start of the executable allocation. `begin`
/// is the callable entry point and may include a stack-neutral profiling
/// prefix; `end` must be one-past the last executable instruction byte and
/// must exclude inline constant-pool data.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct WindowsJitUnwindFunction {
    pub(crate) name: String,
    pub(crate) begin_offset: u64,
    pub(crate) end_offset: u64,
    pub(crate) has_dynamic_stack_alloc: bool,
}

impl WindowsJitUnwindFunction {
    pub(crate) fn new(name: impl Into<String>, begin_offset: u64, end_offset: u64) -> Self {
        Self {
            name: name.into(),
            begin_offset,
            end_offset,
            has_dynamic_stack_alloc: false,
        }
    }

    pub(crate) fn with_dynamic_stack_alloc(mut self, has_dynamic_stack_alloc: bool) -> Self {
        self.has_dynamic_stack_alloc = has_dynamic_stack_alloc;
        self
    }
}

#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
#[derive(Default)]
struct WindowsJitUnwindRegistration {
    function_table: Vec<sys::WindowsRuntimeFunction>,
    registered: bool,
}

#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
impl WindowsJitUnwindRegistration {
    fn new(function_table: Vec<sys::WindowsRuntimeFunction>) -> Self {
        Self {
            function_table,
            registered: false,
        }
    }

    fn register(mut self, base_address: u64) -> Result<Self, JitError> {
        if self.function_table.is_empty() {
            return Ok(self);
        }
        let entry_count = u32::try_from(self.function_table.len()).map_err(|_| {
            JitError::WindowsUnwindUnsupported {
                function: "<module>".to_string(),
                reason: format!(
                    "function table has {} entries, which does not fit in DWORD",
                    self.function_table.len()
                ),
            }
        })?;
        let ok = unsafe {
            sys::rtl_add_function_table(self.function_table.as_mut_ptr(), entry_count, base_address)
        };
        if !ok {
            return Err(JitError::WindowsUnwindRegistrationFailed {
                function_count: self.function_table.len(),
            });
        }
        self.registered = true;
        Ok(self)
    }

    fn unregister(&mut self) {
        if self.registered {
            let _ = unsafe { sys::rtl_delete_function_table(self.function_table.as_mut_ptr()) };
            self.registered = false;
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
impl Drop for WindowsJitUnwindRegistration {
    fn drop(&mut self) {
        self.unregister();
    }
}

#[cfg(not(all(target_arch = "x86_64", target_os = "windows")))]
#[derive(Default)]
struct WindowsJitUnwindRegistration;

#[cfg(not(all(target_arch = "x86_64", target_os = "windows")))]
impl WindowsJitUnwindRegistration {
    fn register(self, _base_address: u64) -> Result<Self, JitError> {
        Ok(self)
    }

    fn unregister(&mut self) {}
}

#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
const UWOP_PUSH_NONVOL: u8 = 0;
#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
const UWOP_ALLOC_LARGE: u8 = 1;
#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
const UWOP_ALLOC_SMALL: u8 = 2;
#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
const UWOP_SET_FPREG: u8 = 3;
#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
const UWOP_SAVE_XMM128: u8 = 8;
#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
const X86_64_RBP_UNWIND_REGISTER: u8 = 5;

#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
#[derive(Debug, Clone, Copy)]
struct WindowsUnwindCode {
    code_offset: u8,
    unwind_op: u8,
    op_info: u8,
}

#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
impl WindowsUnwindCode {
    fn emit(self, out: &mut Vec<u8>) {
        out.push(self.code_offset);
        out.push((self.op_info << 4) | (self.unwind_op & 0x0f));
    }
}

#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
#[derive(Debug, Clone)]
struct WindowsUnwindEntry {
    code: WindowsUnwindCode,
    extra_words: Vec<u16>,
}

#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
impl WindowsUnwindEntry {
    fn new(code: WindowsUnwindCode) -> Self {
        Self {
            code,
            extra_words: Vec::new(),
        }
    }

    fn with_extra_word(mut self, word: u16) -> Self {
        self.extra_words.push(word);
        self
    }

    fn slot_count(&self) -> usize {
        1 + self.extra_words.len()
    }

    fn emit(&self, out: &mut Vec<u8>) {
        self.code.emit(out);
        for word in &self.extra_words {
            out.extend_from_slice(&word.to_le_bytes());
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
#[derive(Debug, Clone, Copy)]
struct WindowsXmmSave {
    reg: u8,
    len: usize,
    rbp_disp: i32,
}

#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
fn windows_x64_push_register(bytes: &[u8]) -> Option<(u8, usize)> {
    match bytes {
        [op @ 0x50..=0x57, ..] => Some((op - 0x50, 1)),
        [0x41, op @ 0x50..=0x57, ..] => Some((8 + (op - 0x50), 2)),
        _ => None,
    }
}

#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
fn windows_x64_nonvolatile_gpr(reg: u8) -> bool {
    matches!(reg, 3 | 5 | 6 | 7 | 12 | 13 | 14 | 15)
}

#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
fn windows_x64_neutral_counter_prefix_len(bytes: &[u8]) -> usize {
    // Windows x64 profile counters use R10, a volatile register, and do not
    // touch RSP. That makes the prefix safe to include in the unwind prologue
    // span while leaving no unwind op to encode for the prefix itself.
    const PREFIX_LEN: usize = 14;
    if bytes.len() >= PREFIX_LEN
        && bytes[0] == 0x49
        && bytes[1] == 0xBA
        && bytes[10..14] == [0xF0, 0x49, 0xFF, 0x02]
    {
        PREFIX_LEN
    } else {
        0
    }
}

#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
fn windows_x64_xmm_save(function: &str, bytes: &[u8]) -> Result<Option<WindowsXmmSave>, JitError> {
    let Some(0xF3) = bytes.first().copied() else {
        return Ok(None);
    };

    let mut cursor = 1usize;
    let rex = if matches!(bytes.get(cursor), Some(0x40..=0x4F)) {
        let rex = bytes[cursor];
        cursor += 1;
        rex
    } else {
        0
    };
    if bytes.get(cursor..cursor + 2) != Some(&[0x0F, 0x7F]) {
        // The scanner is positioned at the first byte after the generated
        // frame setup. A body MOVSS load also starts with F3 but is not an XMM
        // save and must not make otherwise valid unwind metadata fail closed.
        if bytes.get(cursor..cursor + 2) == Some(&[0x0F, 0x10]) {
            return Ok(None);
        }
        return Err(JitError::WindowsUnwindUnsupported {
            function: function.to_string(),
            reason: "unsupported XMM/non-GPR save pattern in Windows x64 prologue".to_string(),
        });
    }
    cursor += 2;

    let Some(modrm) = bytes.get(cursor).copied() else {
        return Err(JitError::WindowsUnwindUnsupported {
            function: function.to_string(),
            reason: "truncated XMM save in Windows x64 prologue".to_string(),
        });
    };
    cursor += 1;

    let reg = ((modrm >> 3) & 0x07) + if rex & 0x04 != 0 { 8 } else { 0 };
    let base = (modrm & 0x07) + if rex & 0x01 != 0 { 8 } else { 0 };
    let mode = modrm >> 6;
    if base != X86_64_RBP_UNWIND_REGISTER || mode == 0 || mode == 3 {
        return Err(JitError::WindowsUnwindUnsupported {
            function: function.to_string(),
            reason: "unsupported XMM save addressing in Windows x64 prologue".to_string(),
        });
    }
    if !(6..=15).contains(&reg) {
        return Err(JitError::WindowsUnwindUnsupported {
            function: function.to_string(),
            reason: format!("unsupported XMM save in Windows x64 prologue: register xmm{reg}"),
        });
    }

    let rbp_disp = match mode {
        1 => {
            let Some(disp) = bytes.get(cursor).copied() else {
                return Err(JitError::WindowsUnwindUnsupported {
                    function: function.to_string(),
                    reason: "truncated disp8 XMM save in Windows x64 prologue".to_string(),
                });
            };
            cursor += 1;
            i32::from(disp as i8)
        }
        2 => {
            let disp = bytes.get(cursor..cursor + 4).ok_or_else(|| {
                JitError::WindowsUnwindUnsupported {
                    function: function.to_string(),
                    reason: "truncated disp32 XMM save in Windows x64 prologue".to_string(),
                }
            })?;
            cursor += 4;
            i32::from_le_bytes([disp[0], disp[1], disp[2], disp[3]])
        }
        _ => unreachable!("unsupported XMM save mode rejected above"),
    };

    Ok(Some(WindowsXmmSave {
        reg,
        len: cursor,
        rbp_disp,
    }))
}

#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
fn windows_x64_stack_alloc(function: &str, bytes: &[u8]) -> Result<Option<(u32, usize)>, JitError> {
    if bytes.starts_with(&[0x48, 0x81, 0xEC]) {
        let frame_bytes = bytes
            .get(3..7)
            .ok_or_else(|| JitError::WindowsUnwindUnsupported {
                function: function.to_string(),
                reason: "truncated `sub rsp, imm32` in prologue".to_string(),
            })?;
        let frame_size = u32::from_le_bytes([
            frame_bytes[0],
            frame_bytes[1],
            frame_bytes[2],
            frame_bytes[3],
        ]);
        return Ok(Some((frame_size, 7)));
    }

    if bytes.starts_with(&[0x48, 0x83, 0xEC]) {
        let imm = bytes
            .get(3)
            .copied()
            .ok_or_else(|| JitError::WindowsUnwindUnsupported {
                function: function.to_string(),
                reason: "truncated `sub rsp, imm8` in prologue".to_string(),
            })?;
        let signed = i32::from(imm as i8);
        if signed <= 0 {
            return Err(JitError::WindowsUnwindUnsupported {
                function: function.to_string(),
                reason: format!(
                    "unsupported non-positive `sub rsp, imm8` stack allocation in Windows x64 prologue: {signed}"
                ),
            });
        }
        return Ok(Some((signed as u32, 4)));
    }

    Ok(None)
}

#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
fn build_windows_x64_unwind_info(
    function: &str,
    bytes: &[u8],
    has_dynamic_stack_alloc: bool,
) -> Result<Vec<u8>, JitError> {
    let prefix_len = windows_x64_neutral_counter_prefix_len(bytes);
    let prologue = bytes
        .get(prefix_len..)
        .ok_or_else(|| JitError::WindowsUnwindUnsupported {
            function: function.to_string(),
            reason: "function range ends before prologue".to_string(),
        })?;
    if prologue.len() < 4 || prologue[0..4] != [0x55, 0x48, 0x89, 0xE5] {
        return Err(JitError::WindowsUnwindUnsupported {
            function: function.to_string(),
            reason: "expected supported prologue `push rbp; mov rbp, rsp`".to_string(),
        });
    }

    let mut frame_size = 0u32;
    let mut cursor = 4usize;
    let mut gpr_save_slots = Vec::new();
    while let Some((reg, len)) = windows_x64_push_register(&prologue[cursor..]) {
        if !windows_x64_nonvolatile_gpr(reg) || reg == X86_64_RBP_UNWIND_REGISTER {
            return Err(JitError::WindowsUnwindUnsupported {
                function: function.to_string(),
                reason: format!("unsupported GPR push in Windows x64 prologue: register {reg}"),
            });
        }
        cursor += len;
        let code_offset =
            u8::try_from(prefix_len + cursor).map_err(|_| JitError::WindowsUnwindUnsupported {
                function: function.to_string(),
                reason: format!(
                    "unwind code offset {} does not fit in UNWIND_INFO",
                    prefix_len + cursor
                ),
            })?;
        gpr_save_slots.push(WindowsUnwindCode {
            code_offset,
            unwind_op: UWOP_PUSH_NONVOL,
            op_info: reg,
        });
    }

    let mut prolog_size = prefix_len + cursor;
    let mut frame_alloc_code_offset = None;
    let tail = &prologue[cursor..];
    if let Some((alloc_size, alloc_len)) = windows_x64_stack_alloc(function, tail)? {
        frame_size = alloc_size;
        cursor += alloc_len;
        prolog_size = prefix_len + cursor;
        frame_alloc_code_offset =
            Some(
                u8::try_from(prolog_size).map_err(|_| JitError::WindowsUnwindUnsupported {
                    function: function.to_string(),
                    reason: format!("prologue size {prolog_size} does not fit in UNWIND_INFO"),
                })?,
            );
    }

    let tail = &prologue[cursor..];
    if let Some((reg, _)) = windows_x64_push_register(tail) {
        return Err(JitError::WindowsUnwindUnsupported {
            function: function.to_string(),
            reason: format!(
                "unsupported GPR push after stack allocation in Windows x64 prologue: register {reg}"
            ),
        });
    }

    let final_rsp_from_rbp = i64::from(frame_size) + (gpr_save_slots.len() as i64 * 8);
    let mut xmm_save_slots = Vec::new();
    while let Some(save) = windows_x64_xmm_save(function, &prologue[cursor..])? {
        if has_dynamic_stack_alloc {
            return Err(JitError::WindowsUnwindUnsupported {
                function: function.to_string(),
                reason: "Windows x64 JIT unwind metadata does not yet support callee-saved XMM saves with dynamic stack allocation".to_string(),
            });
        }

        cursor += save.len;
        prolog_size = prefix_len + cursor;
        let code_offset =
            u8::try_from(prefix_len + cursor).map_err(|_| JitError::WindowsUnwindUnsupported {
                function: function.to_string(),
                reason: format!(
                    "unwind code offset {} does not fit in UNWIND_INFO",
                    prefix_len + cursor
                ),
            })?;
        let stack_offset = final_rsp_from_rbp + i64::from(save.rbp_disp);
        if stack_offset < 0 || stack_offset % 16 != 0 {
            return Err(JitError::WindowsUnwindUnsupported {
                function: function.to_string(),
                reason: format!(
                    "callee-saved XMM save for xmm{} has unsupported stack offset {stack_offset}",
                    save.reg
                ),
            });
        }
        let scaled_offset =
            u16::try_from(stack_offset / 16).map_err(|_| JitError::WindowsUnwindUnsupported {
                function: function.to_string(),
                reason: format!(
                    "callee-saved XMM save offset {stack_offset} exceeds supported UWOP_SAVE_XMM128 range"
                ),
            })?;
        xmm_save_slots.push(
            WindowsUnwindEntry::new(WindowsUnwindCode {
                code_offset,
                unwind_op: UWOP_SAVE_XMM128,
                op_info: save.reg,
            })
            .with_extra_word(scaled_offset),
        );
    }

    if frame_size % 8 != 0 {
        return Err(JitError::WindowsUnwindUnsupported {
            function: function.to_string(),
            reason: format!("frame allocation {frame_size} is not 8-byte aligned"),
        });
    }

    let prolog_size_u8 =
        u8::try_from(prolog_size).map_err(|_| JitError::WindowsUnwindUnsupported {
            function: function.to_string(),
            reason: format!("prologue size {prolog_size} does not fit in UNWIND_INFO"),
        })?;
    let code_offset = |offset: usize| -> Result<u8, JitError> {
        u8::try_from(prefix_len + offset).map_err(|_| JitError::WindowsUnwindUnsupported {
            function: function.to_string(),
            reason: format!(
                "unwind code offset {} does not fit in UNWIND_INFO",
                prefix_len + offset
            ),
        })
    };

    let mut entries = Vec::new();
    if frame_size > 0 {
        let alloc_code_offset = frame_alloc_code_offset.unwrap_or(prolog_size_u8);
        if frame_size <= 128 {
            entries.push(WindowsUnwindEntry::new(WindowsUnwindCode {
                code_offset: alloc_code_offset,
                unwind_op: UWOP_ALLOC_SMALL,
                op_info: ((frame_size - 8) / 8) as u8,
            }));
        } else if frame_size <= (512 * 1024 - 8) {
            entries.push(
                WindowsUnwindEntry::new(WindowsUnwindCode {
                    code_offset: alloc_code_offset,
                    unwind_op: UWOP_ALLOC_LARGE,
                    op_info: 0,
                })
                .with_extra_word((frame_size / 8) as u16),
            );
        } else {
            return Err(JitError::WindowsUnwindUnsupported {
                function: function.to_string(),
                reason: format!(
                    "frame allocation {frame_size} exceeds supported UWOP_ALLOC_LARGE short form"
                ),
            });
        }
    }

    entries.extend(xmm_save_slots);
    for slot in gpr_save_slots.iter().copied() {
        entries.push(WindowsUnwindEntry::new(slot));
    }
    let uses_frame_register = entries
        .iter()
        .all(|entry| entry.code.unwind_op != UWOP_SAVE_XMM128);
    if uses_frame_register {
        entries.push(WindowsUnwindEntry::new(WindowsUnwindCode {
            code_offset: code_offset(4)?,
            unwind_op: UWOP_SET_FPREG,
            op_info: 0,
        }));
    }
    entries.push(WindowsUnwindEntry::new(WindowsUnwindCode {
        code_offset: code_offset(1)?,
        unwind_op: UWOP_PUSH_NONVOL,
        op_info: X86_64_RBP_UNWIND_REGISTER,
    }));
    entries.sort_by(|left, right| right.code.code_offset.cmp(&left.code.code_offset));

    let count_of_codes = entries
        .iter()
        .map(WindowsUnwindEntry::slot_count)
        .sum::<usize>();
    let count_of_codes_u8 =
        u8::try_from(count_of_codes).map_err(|_| JitError::WindowsUnwindUnsupported {
            function: function.to_string(),
            reason: format!("too many Windows unwind code slots: {count_of_codes}"),
        })?;

    let mut out = Vec::new();
    out.push(1);
    out.push(prolog_size_u8);
    out.push(count_of_codes_u8);
    out.push(if uses_frame_register {
        X86_64_RBP_UNWIND_REGISTER
    } else {
        0
    });

    for entry in &entries {
        entry.emit(&mut out);
    }
    if count_of_codes % 2 != 0 {
        out.extend_from_slice(&[0, 0]);
    }
    while out.len() % 4 != 0 {
        out.push(0);
    }
    Ok(out)
}

#[cfg(all(target_arch = "x86_64", target_os = "windows"))]
fn prepare_windows_jit_unwind_registration(
    code: &mut Vec<u8>,
    functions: &[WindowsJitUnwindFunction],
) -> Result<WindowsJitUnwindRegistration, JitError> {
    if functions.is_empty() {
        return Ok(WindowsJitUnwindRegistration::default());
    }

    let executable_len = code.len();
    let mut table = Vec::with_capacity(functions.len());
    let mut sorted = functions.to_vec();
    sorted.sort_by_key(|function| function.begin_offset);

    while code.len() % 4 != 0 {
        code.push(0);
    }

    for function in sorted {
        let begin = usize::try_from(function.begin_offset).map_err(|_| {
            JitError::WindowsUnwindRangeInvalid {
                function: function.name.clone(),
                begin_offset: function.begin_offset,
                end_offset: function.end_offset,
                code_len: executable_len,
            }
        })?;
        let end = usize::try_from(function.end_offset).map_err(|_| {
            JitError::WindowsUnwindRangeInvalid {
                function: function.name.clone(),
                begin_offset: function.begin_offset,
                end_offset: function.end_offset,
                code_len: executable_len,
            }
        })?;
        if begin >= end || end > executable_len {
            return Err(JitError::WindowsUnwindRangeInvalid {
                function: function.name,
                begin_offset: function.begin_offset,
                end_offset: function.end_offset,
                code_len: executable_len,
            });
        }
        let begin_address =
            u32::try_from(begin).map_err(|_| JitError::WindowsUnwindRangeInvalid {
                function: function.name.clone(),
                begin_offset: function.begin_offset,
                end_offset: function.end_offset,
                code_len: executable_len,
            })?;
        let end_address = u32::try_from(end).map_err(|_| JitError::WindowsUnwindRangeInvalid {
            function: function.name.clone(),
            begin_offset: function.begin_offset,
            end_offset: function.end_offset,
            code_len: executable_len,
        })?;

        let unwind_info = build_windows_x64_unwind_info(
            &function.name,
            &code[begin..end],
            function.has_dynamic_stack_alloc,
        )?;
        let unwind_info_address =
            u32::try_from(code.len()).map_err(|_| JitError::WindowsUnwindUnsupported {
                function: function.name.clone(),
                reason: format!("UNWIND_INFO offset {} does not fit in u32", code.len()),
            })?;
        code.extend_from_slice(&unwind_info);
        while code.len() % 4 != 0 {
            code.push(0);
        }

        table.push(sys::WindowsRuntimeFunction {
            begin_address,
            end_address,
            unwind_info_address,
        });
    }

    Ok(WindowsJitUnwindRegistration::new(table))
}

#[cfg(not(all(target_arch = "x86_64", target_os = "windows")))]
fn prepare_windows_jit_unwind_registration(
    _code: &mut Vec<u8>,
    _functions: &[WindowsJitUnwindFunction],
) -> Result<WindowsJitUnwindRegistration, JitError> {
    Ok(WindowsJitUnwindRegistration)
}

// ---------------------------------------------------------------------------
// JIT-7 hardened publication: RAII mapping ownership + bytes-hash publish check
// ---------------------------------------------------------------------------

/// RAII ownership of the anonymous mapping backing a JIT publication.
///
/// Before JIT-7 the publish sequences owned their mapping as a raw pointer
/// and released it with ad-hoc `munmap` calls sprinkled over *some* error
/// paths — a `?`/panic between `mmap` and `ExecutableBuffer` construction on
/// any other path leaked the mapping, and mappings that accumulate across
/// compiles are exactly the failure mode documented in
/// `docs/jit-parallel-race-2026-06-29.md`. This type makes the ownership
/// structural: from `allocate_rw` until `into_published_parts`, every exit —
/// early `return`, `?`, or panic/unwind — unmaps via `Drop`.
///
/// It also encodes the W^X state machine in one place:
///
/// 1. `allocate_rw` — the mapping is born `RW` (readable+writable, never
///    executable).
/// 2. `seal_rx_and_verify` — exactly one `RW -> RX` flip, with the icache
///    flush issued *before* the flip (the architecturally-required order on
///    AArch64, see #357), followed by the fail-closed bytes-hash publish
///    check (below). Double-sealing is an `assert!` failure.
/// 3. `into_published_parts` — only a sealed (RX, hash-verified) mapping may
///    be released into an [`ExecutableBuffer`].
///
/// There is deliberately no way back from `RX` to `RW` on this type.
struct MappedRegion {
    ptr: *mut u8,
    len: usize,
    sealed_rx: bool,
}

#[cfg(test)]
thread_local! {
    /// Exact bytes currently owned by pre-publication `MappedRegion` values on
    /// this test thread. Unlike process virtual-size sampling, this cannot be
    /// perturbed by unrelated parallel tests, allocator arenas, or dyld.
    static MAPPED_REGION_OWNED_BYTES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn track_mapped_region_alloc(len: usize) {
    MAPPED_REGION_OWNED_BYTES.with(|bytes| bytes.set(bytes.get().saturating_add(len)));
}

#[cfg(not(test))]
fn track_mapped_region_alloc(_len: usize) {}

#[cfg(test)]
fn track_mapped_region_release(len: usize) {
    MAPPED_REGION_OWNED_BYTES.with(|bytes| {
        bytes.set(
            bytes
                .get()
                .checked_sub(len)
                .expect("MappedRegion ownership accounting underflow"),
        );
    });
}

#[cfg(not(test))]
fn track_mapped_region_release(_len: usize) {}

#[cfg(all(test, target_os = "macos"))]
fn mapped_region_owned_bytes_for_tests() -> usize {
    MAPPED_REGION_OWNED_BYTES.with(std::cell::Cell::get)
}

impl MappedRegion {
    /// mmap a fresh anonymous read+write (never executable) region.
    fn allocate_rw(len: usize) -> Result<Self, JitError> {
        // SAFETY: requesting a fresh anonymous RW mapping of `len` bytes;
        // ownership of the returned pages is held by `self` until either
        // `Drop` unmaps them or `into_published_parts` transfers them to an
        // `ExecutableBuffer`.
        let ptr = unsafe { sys::mmap(len, sys::RW).map_err(JitError::MemoryAlloc)? };
        track_mapped_region_alloc(len);
        Ok(Self {
            ptr,
            len,
            sealed_rx: false,
        })
    }

    fn as_mut_ptr(&self) -> *mut u8 {
        self.ptr
    }

    /// Flip the mapping `RW -> RX` and run the fail-closed bytes-hash publish
    /// check: re-read the first `expected_image.len()` bytes from the sealed
    /// mapping and require their SHA-256 to equal `expected_sha256` — the
    /// hash of the compiled artifact computed from the heap image *before*
    /// the copy. A mismatch means the written code is torn/corrupted (e.g. a
    /// racing writer or a wild store during the write window) and returns
    /// [`JitError::PublishedBytesHashMismatch`]; the mapping is then unmapped
    /// by `Drop` and no executable pointer can ever be produced from it.
    ///
    /// The icache flush is issued while the pages are still writable, before
    /// the protection flip — the ARM ARM ordering (`dc cvau`/`dsb`/`ic ivau`/
    /// `dsb`/`isb` on a readable page); see the discussion at the former
    /// inline site (#357). On x86 the flush is a no-op (coherent I/D caches).
    fn seal_rx_and_verify(
        &mut self,
        expected_image_len: usize,
        expected_sha256: &str,
    ) -> Result<(), JitError> {
        assert!(
            !self.sealed_rx,
            "W^X discipline violation: seal_rx_and_verify called twice on the same mapping"
        );
        assert!(
            expected_image_len <= self.len,
            "published image length {} exceeds mapping length {}",
            expected_image_len,
            self.len
        );
        unsafe {
            // SAFETY: `ptr`/`len` name the live mapping owned by `self`; the
            // flush walks only the just-written image bytes and the RW->RX
            // flip covers the whole allocation.
            sys::flush_icache(self.ptr, expected_image_len);
            sys::mprotect(self.ptr, self.len, sys::RX).map_err(JitError::MemoryProtect)?;
        }
        self.sealed_rx = true;

        // Publish check (JIT-7, always on): hash the bytes that will actually
        // execute, as read back from the sealed mapping.
        // SAFETY: the mapping is RX (readable) and `expected_image_len <= len`.
        let published = unsafe { std::slice::from_raw_parts(self.ptr, expected_image_len) };
        let actual_sha256 = crate::jit_diagnostics::sha256_hex(published);
        if actual_sha256 != expected_sha256 {
            return Err(JitError::PublishedBytesHashMismatch {
                expected_sha256: expected_sha256.to_owned(),
                actual_sha256,
                published_len: expected_image_len,
            });
        }
        Ok(())
    }

    /// Transfer ownership of the sealed pages to the caller (the
    /// [`ExecutableBuffer`] constructor). Publication of an unsealed —
    /// writable or unverified — mapping is a hard error.
    fn into_published_parts(self) -> (*mut u8, usize) {
        assert!(
            self.sealed_rx,
            "W^X discipline violation: attempted to publish a mapping that was never sealed RX \
             + hash-verified"
        );
        let parts = (self.ptr, self.len);
        track_mapped_region_release(self.len);
        std::mem::forget(self);
        parts
    }
}

impl Drop for MappedRegion {
    fn drop(&mut self) {
        if !self.ptr.is_null() {
            // SAFETY: `ptr`/`len` are the exact extent returned by `mmap` in
            // `allocate_rw`, still owned by this value (ownership transfer
            // defuses `Drop` via `mem::forget`).
            unsafe { sys::munmap(self.ptr, self.len) };
            track_mapped_region_release(self.len);
        }
    }
}

/// Write an 8-byte little-endian-native literal into the *heap* image at
/// `offset`, failing closed if the slot does not lie entirely inside
/// `image[..code_len]` (the raw code region). This replaces the former
/// direct `write_u64_literal_unaligned` stores into the live mapping so the
/// heap image stays the single source of truth for the publish-check hash.
fn write_u64_literal_in_image(
    image: &mut [u8],
    code_len: usize,
    offset: usize,
    value: u64,
) -> Result<(), JitError> {
    let end = offset.checked_add(8).filter(|&end| end <= code_len);
    if end.is_none() {
        return Err(JitError::ProfilePatchOutOfBounds {
            patch_offset: offset,
            code_len,
        });
    }
    assert!(code_len <= image.len());
    // SAFETY: `offset + 8 <= code_len <= image.len()` was just checked; the
    // store semantics (native-endian unaligned u64) are identical to the
    // former direct-into-mapping writes.
    unsafe { write_u64_literal_unaligned(image.as_mut_ptr(), offset, value) };
    Ok(())
}

/// Test-only fault injection for the publish check: when set, the publish
/// sequences XOR-flip one byte of the *mapping* (not the heap image) at the
/// given offset after the copy and before sealing, simulating a torn/racy
/// write. The negative test locks in that such corruption can never publish.
#[cfg(test)]
mod publish_test_hooks {
    use std::cell::Cell;

    thread_local! {
        pub(super) static CORRUPT_PUBLISHED_BYTE_AT: Cell<Option<usize>> =
            const { Cell::new(None) };
    }

    pub(super) fn corrupt_published_byte_if_requested(memory: *mut u8, image_len: usize) {
        if let Some(offset) = CORRUPT_PUBLISHED_BYTE_AT.with(|slot| slot.take())
            && offset < image_len
        {
            // SAFETY: test-only; `offset < image_len` and the mapping is
            // still in its RW write window.
            unsafe {
                let p = memory.add(offset);
                p.write(p.read() ^ 0xa5);
            }
        }
    }
}

#[cfg(test)]
use publish_test_hooks::corrupt_published_byte_if_requested;

#[cfg(not(test))]
#[inline(always)]
fn corrupt_published_byte_if_requested(_memory: *mut u8, _image_len: usize) {}

/// Publish already-encoded native code as an [`ExecutableBuffer`].
///
/// Target-specific JIT frontends that do their own lowering/linking use this
/// to share the same executable-memory and lifetime-bound lookup machinery as
/// [`JitCompiler::compile_raw`]. When profiling trampolines were pre-emitted,
/// `counter_patch_sites` are offsets into `code` where an 8-byte counter
/// pointer immediate/literal must be patched after the copy into writable
/// executable memory.
pub(crate) fn publish_raw_executable_buffer_with_profile_data(
    code: &[u8],
    canonical_symbols: Vec<String>,
    symbol_offsets: HashMap<String, u64>,
    function_ranges: Vec<(String, std::ops::Range<u64>)>,
    counters: HashMap<String, Box<AtomicU64>>,
    counter_patch_sites: Vec<(usize, *const AtomicU64)>,
    windows_unwind_functions: Vec<WindowsJitUnwindFunction>,
) -> Result<ExecutableBuffer, JitError> {
    if !sys::host_supported() {
        return Err(JitError::UnsupportedHost {
            arch: std::env::consts::ARCH,
            os: std::env::consts::OS,
        });
    }

    if code.is_empty() {
        return Err(JitError::EmptyExecutableBuffer {
            function_count: canonical_symbols.len(),
        });
    }

    let code_len = code.len();
    let mut published_code = code.to_vec();
    let windows_unwind =
        prepare_windows_jit_unwind_registration(&mut published_code, &windows_unwind_functions)?;

    #[cfg(debug_assertions)]
    {
        use std::collections::HashSet;
        let valid: HashSet<usize> = counters
            .values()
            .map(|counter| counter.as_ref() as *const AtomicU64 as usize)
            .collect();
        for (patch_offset, counter_ptr) in &counter_patch_sites {
            debug_assert!(
                !counter_ptr.is_null(),
                "counter patch site at offset {} has null counter pointer",
                patch_offset
            );
            debug_assert!(
                valid.contains(&(*counter_ptr as usize)),
                "counter patch site at offset {} points outside ExecutableBuffer-owned counters",
                patch_offset
            );
        }
    }

    // Apply all counter-literal patches to the HEAP image before the copy
    // (single-writer discipline, JIT-7): the mapping receives exactly one
    // bulk write, and the heap image is the artifact the publish check
    // hashes. The bounds check is now fail-closed on release builds too
    // (previously a debug_assert next to a raw mapping store).
    for (patch_offset, counter_ptr) in &counter_patch_sites {
        write_u64_literal_in_image(
            &mut published_code,
            code_len,
            *patch_offset,
            *counter_ptr as u64,
        )?;
    }

    let published_len = published_code.len();
    let expected_sha256 = crate::jit_diagnostics::sha256_hex(&published_code);
    let alloc_size = sys::page_align(published_len);
    let mut region = MappedRegion::allocate_rw(alloc_size)?;
    let jit_write_guard = sys::JitWriteGuard::enter();
    unsafe {
        // SAFETY: `region` owns a writable allocation of `alloc_size >=
        // published_len` bytes; `published_code` is heap memory distinct from
        // the fresh mapping.
        std::ptr::copy_nonoverlapping(published_code.as_ptr(), region.as_mut_ptr(), published_len);
    }
    corrupt_published_byte_if_requested(region.as_mut_ptr(), published_len);
    region.seal_rx_and_verify(published_len, &expected_sha256)?;
    drop(jit_write_guard);

    // On registration failure `region`'s Drop unmaps — no manual munmap.
    let windows_unwind = windows_unwind.register(region.as_mut_ptr() as u64)?;

    let (memory, alloc_size) = region.into_published_parts();
    let allocation_cookie =
        executable_buffer_allocation_cookie(memory, alloc_size, code_len, published_len);
    Ok(ExecutableBuffer {
        memory,
        len: alloc_size,
        len_shadow: alloc_size,
        allocation_cookie,
        code_len,
        published_len,
        published_image_sha256: expected_sha256,
        publication: JitPublicationContract::published_rx(),
        windows_unwind,
        function_ranges,
        symbol_offsets,
        canonical_symbols,
        counters,
        timing_cells: HashMap::new(),
        timing_state: None,
        certificates: HashMap::new(),
        proof_optimization_certificates: Vec::new(),
    })
}

/// Publish previously-encoded native code from a serialized payload as a
/// fresh [`ExecutableBuffer`].
///
/// This is the public re-publication entry point used by on-disk JIT buffer
/// caches: a caller persists `code` plus the symbol metadata to disk, and on
/// a subsequent process load this function re-establishes an RX mapping and
/// a working `get_fn_ptr_bound` table without re-running ISel / regalloc /
/// encoding.
///
/// The replay path is restricted to profile-free buffers (no
/// `counters` / `counter_patch_sites` / `timing_cells` / `timing_state`):
/// those structures carry raw heap pointers baked into the code at the
/// originating process's address space, so they cannot be re-used after a
/// process boundary. Buffers compiled via
/// [`CompilerConfig::for_host_jit`](crate::CompilerConfig::for_host_jit)
/// without explicit profile-hook configuration satisfy this restriction,
/// which is the case for every BCP / parent-loop kernel in
/// `trust-cg-jit-matrix`.
///
/// Windows x64 unwind metadata is also out of scope here: the caller is
/// expected to provide raw code only, and the function passes an empty
/// `windows_unwind_functions` list to the inner publisher. Replay on
/// Windows therefore requires the buffer to have been produced without
/// unwind-info patching (which is the case for the BCP kernels).
pub fn publish_serialized_buffer(
    code: &[u8],
    canonical_symbols: Vec<String>,
    symbol_offsets: HashMap<String, u64>,
    function_ranges: Vec<(String, std::ops::Range<u64>)>,
) -> Result<ExecutableBuffer, JitError> {
    // No profile counters: the empty `counters` map paired with the empty
    // `counter_patch_sites` list short-circuits the patch loop inside
    // `publish_raw_executable_buffer_with_profile_data` so no
    // address-bound writes are performed against the freshly-mapped pages.
    let counters: HashMap<String, Box<AtomicU64>> = HashMap::new();
    let counter_patch_sites: Vec<(usize, *const AtomicU64)> = Vec::new();
    let windows_unwind_functions: Vec<WindowsJitUnwindFunction> = Vec::new();
    publish_raw_executable_buffer_with_profile_data(
        code,
        canonical_symbols,
        symbol_offsets,
        function_ranges,
        counters,
        counter_patch_sites,
        windows_unwind_functions,
    )
}

// ---------------------------------------------------------------------------
// Process symbol resolution — dlsym(RTLD_DEFAULT, name)
// ---------------------------------------------------------------------------
// `dlsym(RTLD_DEFAULT, ...)` is thread-safe per POSIX. For symbols in the main
// binary, the returned pointer is stable for the lifetime of the process.
// Callers must still ensure the resolved symbol's ABI matches the generated
// callsite ABI before invoking it.
#[cfg(unix)]
mod dl {
    use std::os::raw::{c_char, c_int, c_void};

    // RTLD_DEFAULT is an opaque pseudo-handle. Values differ per platform.
    #[cfg(target_os = "macos")]
    pub(super) const RTLD_DEFAULT: *mut c_void = -2isize as *mut c_void;

    #[cfg(target_os = "linux")]
    pub(super) const RTLD_DEFAULT: *mut c_void = std::ptr::null_mut();

    unsafe extern "C" {
        pub(super) fn dlsym(handle: *mut c_void, symbol: *const c_char) -> *mut c_void;
        pub(super) fn dlerror() -> *const c_char;
    }

    // Suppress unused warning where target_os is neither macos nor linux.
    #[allow(dead_code)]
    fn _unused() {
        let _: c_int = 0;
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

#[derive(Debug, Error)]
#[non_exhaustive]
pub enum JitError {
    #[error("pipeline error: {0}")]
    Pipeline(#[from] PipelineError),

    #[error("unresolved symbol: {0}")]
    UnresolvedSymbol(String),

    #[error(
        "JIT executable memory is unsupported on host {arch}-{os}; supported hosts are aarch64/x86_64 on macos/linux and x86_64 on windows"
    )]
    UnsupportedHost {
        arch: &'static str,
        os: &'static str,
    },

    #[error("memory allocation failed: {0}")]
    MemoryAlloc(std::io::Error),

    #[error("memory protection failed: {0}")]
    MemoryProtect(std::io::Error),

    #[error(
        "raw JIT exception handling is unsupported for `{function}`: compile_raw publishes code without registering its LSDA/personality/unwind-frame sidecar"
    )]
    RawJitEhUnsupported { function: String },

    #[error(
        "raw JIT target mismatch for `{function}`: JitCompiler::compile_raw consumes AArch64 MachFunction instructions, but the host architecture is {host_arch}; use the typed Compiler/trust_ir JIT path for architecture-specific lowering"
    )]
    RawJitTargetMismatch {
        function: String,
        host_arch: &'static str,
    },

    #[error("Windows x64 JIT unwind metadata for `{function}` is unsupported: {reason}")]
    WindowsUnwindUnsupported { function: String, reason: String },

    #[error(
        "Windows x64 JIT unwind range for `{function}` is invalid: {begin_offset:#x}..{end_offset:#x} with code length {code_len}"
    )]
    WindowsUnwindRangeInvalid {
        function: String,
        begin_offset: u64,
        end_offset: u64,
        code_len: usize,
    },

    #[error(
        "Windows x64 JIT unwind registration failed for {function_count} function table entrie(s)"
    )]
    WindowsUnwindRegistrationFailed { function_count: usize },

    #[error("JIT compilation produced no executable code for {function_count} function(s)")]
    EmptyExecutableBuffer { function_count: usize },

    #[error(
        "JIT executable buffer is not published RX: buffer {buffer_base:#x}..{buffer_end:#x} (code_len={code_len}, allocation_len={allocation_len})"
    )]
    UnpublishedExecutableBuffer {
        buffer_base: u64,
        buffer_end: u64,
        code_len: usize,
        allocation_len: usize,
    },

    #[error(
        "JIT executable buffer has invalid extent: code range {buffer_base:#x}..{code_end:#x}, allocation range {buffer_base:#x}..{allocation_end:#x} (code_len={code_len}, allocation_len={allocation_len})"
    )]
    InvalidExecutableBufferExtent {
        buffer_base: u64,
        code_end: u64,
        allocation_end: u64,
        code_len: usize,
        allocation_len: usize,
    },

    #[error("null JIT function pointer for `{symbol}`")]
    NullFunctionPointer { symbol: String },

    #[error(
        "JIT pointer ownership mismatch for `{context}`: pointer {pointer:#x} is outside buffer code range {buffer_base:#x}..{buffer_end:#x} (code_len={code_len}, allocation_len={allocation_len})"
    )]
    JitPointerOwnershipMismatch {
        context: String,
        pointer: u64,
        buffer_base: u64,
        buffer_end: u64,
        code_len: usize,
        allocation_len: usize,
    },

    #[error(
        "JIT function pointer for `{symbol}` targets offset {actual_offset:#x}, expected symbol offset {expected_offset:#x} (pointer {pointer:#x}, buffer_base {buffer_base:#x})"
    )]
    FunctionPointerSymbolMismatch {
        symbol: String,
        pointer: u64,
        buffer_base: u64,
        actual_offset: u64,
        expected_offset: u64,
    },

    #[error("branch out of range: offset {offset} to {target} (distance {distance})")]
    BranchOutOfRange {
        offset: u32,
        target: u64,
        distance: i64,
    },

    #[error(
        "veneer for `{symbol}` at {veneer_offset} is out of BL range from call site {offset} \
         (distance {distance}, max +-128MiB)"
    )]
    VeneerOutOfRange {
        symbol: String,
        offset: u32,
        veneer_offset: u64,
        distance: i64,
    },

    #[error("fixup offset {offset} out of bounds (code length {code_len})")]
    FixupOutOfBounds { offset: u32, code_len: usize },

    #[error(
        "duplicate JIT symbol: `{0}` (primary name or `_`-prefixed alias collides with a previously compiled function)"
    )]
    DuplicateSymbol(String),

    #[error("profile hooks are only supported on aarch64 and x86-64 hosts")]
    ProfileHooksUnsupported,

    #[error("block profile patch site for `{function}` block {block_id} has no allocated counter")]
    MissingBlockProfileCounter { function: String, block_id: u32 },

    #[error(
        "block timing patch site for `{function}` block {block_id} has no allocated timing cell"
    )]
    MissingBlockTimingCell { function: String, block_id: u32 },

    #[error(
        "profile hook mode `{mode:?}` is a reserved #396 Phase 2 variant; \
         trampoline emission is not yet implemented. See \
         designs/2026-04-18-pgo-workflow.md and use \
         `ProfileHookMode::CallCounts` for the current Phase 1 surface."
    )]
    ProfileHookModeUnimplemented { mode: ProfileHookMode },

    #[error(
        "fail-closed: refusing to publish JIT executable buffer — the bytes read back from the \
         sealed RX mapping hash to {actual_sha256} but the compiled artifact hashes to \
         {expected_sha256} ({published_len} bytes); the written code is torn or corrupted and \
         must never execute (JIT-7 publish check)"
    )]
    PublishedBytesHashMismatch {
        expected_sha256: String,
        actual_sha256: String,
        published_len: usize,
    },

    #[error(
        "fail-closed: profile literal patch at offset {patch_offset} (+8 bytes) is outside the \
         raw code region of length {code_len}; refusing to publish a buffer whose patch would \
         scribble past the encoded code (JIT-7 publish check)"
    )]
    ProfilePatchOutOfBounds {
        patch_offset: usize,
        code_len: usize,
    },
}

/// Maximum absolute distance for an AArch64 B/BL imm26 branch: +-128 MiB.
/// The imm26 field encodes a signed 26-bit word offset, so the reachable
/// range is [-(1 << 27), (1 << 27)) bytes from the branch instruction.
#[cfg(target_arch = "aarch64")]
const AARCH64_BRANCH26_MAX: i64 = 1 << 27;

/// Check whether an AArch64 B/BL `imm26` branch at `offset` can reach `target`.
/// Returns true if the signed distance fits in [-128 MiB, +128 MiB).
#[cfg(target_arch = "aarch64")]
fn branch26_in_range(offset: u32, target: u64) -> (bool, i64) {
    let distance = target as i64 - offset as i64;
    let in_range = (-AARCH64_BRANCH26_MAX..AARCH64_BRANCH26_MAX).contains(&distance);
    (in_range, distance)
}

/// Pre-validate that every veneer trampoline is within AArch64 BL reach of
/// the call site that will patch into it.
///
/// `ext_patches` is the per-fixup list of `(bl_offset, veneer_offset, symbol)`
/// triples collected during veneer emission in
/// [`JitCompiler::compile_raw`]. This function performs the range check in
/// isolation so that (a) the check is exercised by unit tests without
/// emitting >128 MiB of real code, and (b) the validation pass in
/// `compile_raw` is a single well-named call rather than an inline loop.
///
/// On AArch64 this enforces the imm26 range `[-2^27, +2^27)` bytes.
/// On non-AArch64 hosts the check is a no-op (BL range is a property of the
/// target ISA — on macOS-x86_64 JIT hosts the veneer code would not run
/// anyway, and the BL imm26 limit does not apply).
///
/// Returns `Err(JitError::VeneerOutOfRange)` on the first unreachable pair.
/// The `_code_len` parameter is accepted (and unused) so the signature can
/// grow a bounds-check or island-aware variant later without breaking callers.
#[cfg_attr(not(target_arch = "aarch64"), allow(dead_code))]
fn validate_veneer_ranges(
    ext_patches: &[(u32, u64, String)],
    _code_len: usize,
) -> Result<(), JitError> {
    #[cfg(target_arch = "aarch64")]
    for (fx_off, veneer_off, sym) in ext_patches {
        let (ok, distance) = branch26_in_range(*fx_off, *veneer_off);
        if !ok {
            return Err(JitError::VeneerOutOfRange {
                symbol: sym.clone(),
                offset: *fx_off,
                veneer_offset: *veneer_off,
                distance,
            });
        }
    }
    // Suppress unused-variable warning on non-aarch64 hosts where the loop
    // is compiled out entirely.
    #[cfg(not(target_arch = "aarch64"))]
    let _ = ext_patches;
    Ok(())
}

/// Entry-hook mode for JIT-compiled functions.
///
/// # Granularity levels (#396 PGO workflow)
///
/// Variants are ordered roughly by granularity. `None` disables all hooks
/// (the zero-overhead default). `CallCounts` is the portable function-entry
/// counter mode. `CallCountsAndTiming` is implemented only where the backend
/// has a real timing trampoline; on x86-64 it currently returns
/// [`JitError::ProfileHooksUnsupported`] instead of silently collecting
/// count-only data.
///
/// For the raw MachIR JIT surface, `BlockCounts` and `BlockCountsAndTiming`
/// are implemented by the AArch64 block-trampoline path and rejected with
/// [`JitError::ProfileHooksUnsupported`] on x86-64 until equivalent raw x86-64
/// block splicing exists. The higher-level [`crate::Compiler`] trust_ir JIT path
/// has its own x86-64 `BlockCounts` injection used by `trust-cg --profile-generate`;
/// that compiler path does not change the fail-closed behavior of
/// [`JitCompiler::compile_raw`]. `EdgeCounts`, `BlockFrequency`, and
/// `LoopHeads` remain reserved API variants; [`JitCompiler::compile_raw`]
/// rejects them with [`JitError::ProfileHookModeUnimplemented`] until their
/// trampoline work lands. See `designs/2026-04-18-pgo-workflow.md`.
///
/// # Public Entry-Counter API (#478)
///
/// The stable, ergonomic name for the function-entry slice is
/// [`JitConfig::emit_entry_counters`] plus
/// [`ExecutableBuffer::entry_count`],
/// [`ExecutableBuffer::reset_entry_count`], and
/// [`ExecutableBuffer::entry_counts`]. `ProfileHookMode` remains the
/// lower-level knob for callers that need to choose a specific profiling
/// mode directly.
///
/// See also [`trust_cg_opt::pgo::inject`] for the MachIR-level block-counter
/// injection pass that already exists (Phase 1 landed in #396).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProfileHookMode {
    /// No profiling hooks. Zero overhead. The default.
    None,
    /// One counter per function, incremented at the trampoline entry.
    CallCounts,
    /// `CallCounts` plus wall-time timing around the function body.
    ///
    /// Unsupported on x86-64 until that backend records timing data. The
    /// x86-64 JIT must reject this mode with
    /// [`JitError::ProfileHooksUnsupported`], not treat it as
    /// [`ProfileHookMode::CallCounts`].
    CallCountsAndTiming,
    // ----- Phase 2 (#396) — API reserved, trampoline TODO ------------------
    /// One counter per basic block, incremented at block prologue.
    ///
    /// Implemented for raw AArch64 JIT block trampolines and for the
    /// higher-level x86-64 trust_ir compiler JIT path used by CLI
    /// `--profile-generate`. Raw x86-64 [`JitCompiler::compile_raw`] requests
    /// still reject this mode with [`JitError::ProfileHooksUnsupported`].
    BlockCounts,
    /// `BlockCounts` plus per-block wall-time timing.
    ///
    /// TODO(#396 Phase 2): as `BlockCounts`, plus timing probes on every
    /// block prologue and epilogue. Beware: per-block timing can dwarf
    /// the work being measured; emit only when the caller has explicitly
    /// asked for timing.
    BlockCountsAndTiming,
    /// One counter per CFG edge, incremented on the edge itself (after
    /// critical-edge splitting).
    ///
    /// TODO(#396 Phase 3): strictly more information than `BlockCounts`
    /// but doubles counter count. Requires a critical-edge-split
    /// pre-pass so each edge has a unique landing block; otherwise
    /// multi-predecessor blocks double-count. See LLVM's
    /// `llvm/lib/Transforms/IPO/PGOInstrumentation.cpp` for prior art.
    EdgeCounts,
    /// Derived per-block frequency (no new counters; computed from
    /// `BlockCounts` or `EdgeCounts` via Kirchhoff balance at profile
    /// read time).
    ///
    /// TODO(#396 Phase 2): this is the *consumer*-facing mode —
    /// requesting `BlockFrequency` from the JIT should be equivalent to
    /// requesting `BlockCounts` and having the reader derive
    /// frequencies. Added here so the `JitConfig` API matches what
    /// `ProfileUse` consumers (inline budget, unroll, block layout)
    /// ultimately want to see.
    BlockFrequency,
    /// Only loop-head blocks get counters. Captures iteration counts
    /// without per-block overhead.
    ///
    /// TODO(#396 Phase 2): implemented as a filter on top of
    /// `BlockCounts`: the instrumentation step queries the loop
    /// analysis (`trust_cg_opt::loops`) and only emits counter increments
    /// at loop headers.
    LoopHeads,
}

/// Snapshot of per-function profile data exposed by [`ExecutableBuffer`].
///
/// This type currently exposes call counts only. A buffer compiled with
/// [`ProfileHookMode::CallCountsAndTiming`] must have a backend timing
/// implementation before it can produce this snapshot; x86-64 rejects that
/// mode with [`JitError::ProfileHooksUnsupported`] rather than returning a
/// count-only [`ProfileStats`] value.
#[derive(Debug, Clone, Copy, Default)]
pub struct ProfileStats {
    pub call_count: u64,
}

/// Returns `true` if `mode` is a granularity level for which per-function
/// counter slots must be allocated and the function-entry trampoline
/// emitted.
///
/// This helper classifies storage/trampoline shape only; it is not a support
/// predicate. x86-64 still rejects [`ProfileHookMode::CallCountsAndTiming`]
/// before code emission because that backend has no timing trampoline and must
/// fail closed instead of falling back to count-only data. The newer
/// block/edge/frequency modes (#396 Phase 2) return `false` here — they are
/// accepted by the API but not yet reached from `compile_raw`;
/// [`JitCompiler::compile_raw`] rejects them with
/// [`JitError::ProfileHookModeUnimplemented`] until the trampoline work lands.
fn profile_hooks_enable_counters(mode: ProfileHookMode) -> bool {
    matches!(
        mode,
        ProfileHookMode::CallCounts | ProfileHookMode::CallCountsAndTiming
    )
}

/// Returns `true` if `mode` allocates one counter per basic block and
/// emits a trampoline at the start of every block (not just the function
/// entry). Landed for [`ProfileHookMode::BlockCounts`] under #364; the
/// companion [`ProfileHookMode::BlockCountsAndTiming`] variant is handled
/// by [`profile_hooks_enable_block_timing`] and goes through a larger
/// trampoline that additionally captures a `CNTVCT_EL0` timestamp.
fn profile_hooks_enable_block_counters(mode: ProfileHookMode) -> bool {
    matches!(mode, ProfileHookMode::BlockCounts)
}

/// Returns `true` if `mode` is [`ProfileHookMode::BlockCountsAndTiming`]
/// — one `{count, total_cycles}` cell per basic block, plus a shared
/// `{prev_ts, prev_accum_ptr}` timing-state struct. The larger trampoline
/// captures `CNTVCT_EL0` on every block entry and attributes the cycles
/// between consecutive block entries to the previously-entered block.
///
/// Implemented on AArch64 only (#364 Phase 3). The x86-64 port is a
/// follow-up; on non-AArch64 hosts this mode returns
/// [`JitError::ProfileHooksUnsupported`].
fn profile_hooks_enable_block_timing(mode: ProfileHookMode) -> bool {
    matches!(mode, ProfileHookMode::BlockCountsAndTiming)
}

/// Returns `true` when a mode cannot select both the function-entry counter
/// trampoline and either block-entry trampoline family.
fn profile_hooks_counter_classifiers_are_disjoint(mode: ProfileHookMode) -> bool {
    let enables_function_entry_counter = profile_hooks_enable_counters(mode);
    let enables_block_entry_counter =
        profile_hooks_enable_block_counters(mode) || profile_hooks_enable_block_timing(mode);

    !(enables_function_entry_counter && enables_block_entry_counter)
}

/// Returns `true` if `mode` is a #396 Phase 2 variant whose trampoline
/// work is still TODO. Kept in one place so the early-return in
/// `compile_raw` and the error-message test stay in sync.
fn profile_hooks_is_phase2_stub(mode: ProfileHookMode) -> bool {
    // NOTE: `BlockCountsAndTiming` is intentionally NOT in this list —
    // it is implemented by `splice_block_trampolines_with_timing_aarch64`
    // (#364 Phase 3).
    matches!(
        mode,
        ProfileHookMode::EdgeCounts | ProfileHookMode::BlockFrequency | ProfileHookMode::LoopHeads
    )
}

/// Configuration for [`JitCompiler`].
///
/// # Dispatch verification default (#375)
///
/// The `verify_dispatch` field is propagated into the underlying
/// [`PipelineConfig`] and defaults to [`DispatchVerifyMode::ErrorOnFailure`].
/// Any code path that invokes the Pipeline's dispatch verifier — for example
/// [`Pipeline::generate_and_verify_dispatch`] or
/// [`Pipeline::verify_dispatch_plan`] — will therefore return
/// [`PipelineError::DispatchVerificationFailed`] on a failing plan rather
/// than silently substituting a CPU-only fallback. A verification failure must
/// not be indistinguishable from success on a proof-required path, so silent
/// fallback (the previous default) is not the default behavior.
///
/// Note on current reach: [`JitCompiler::compile_raw`] does not itself
/// invoke the dispatch verifier yet — the verifier is only reached via the
/// pipeline APIs mentioned above. The default still matters because callers
/// that share a [`Pipeline`] via the JIT (including future heterogeneous-
/// aware JIT entry points) inherit this policy from `JitConfig`.
///
/// Callers that explicitly want the legacy silent-fallback behaviour (for
/// example, best-effort heterogeneous dispatch on graphs where a CPU
/// fallback is always acceptable) can opt in with:
///
/// ```
/// use trust_cg_codegen::{JitConfig, DispatchVerifyMode};
/// let cfg = JitConfig {
///     verify_dispatch: DispatchVerifyMode::FallbackOnFailure,
///     ..JitConfig::default()
/// };
/// ```
///
/// Set `verify_dispatch` to [`DispatchVerifyMode::Off`] to skip dispatch
/// verification entirely. Off bypasses the correctness check — prefer
/// `FallbackOnFailure` if the intent is "soft failure" rather than "no
/// check at all". The default remains `ErrorOnFailure` so failures are
/// never silently swallowed.
#[derive(Debug, Clone)]
pub struct JitConfig {
    /// Optimization level for the underlying pipeline.
    pub opt_level: OptLevel,
    /// Whether to run function-level verification after optimization.
    ///
    /// This is a separate gate from `verify_dispatch`: it controls
    /// instruction-level verification of the lowered/optimized IR, not the
    /// heterogeneous dispatch plan.
    pub verify: bool,
    /// Policy for handling dispatch-plan verification failures.
    ///
    /// Defaults to [`DispatchVerifyMode::ErrorOnFailure`] so that
    /// verification failures surface as [`JitError::Pipeline`] rather than
    /// being silently replaced by a CPU-only fallback (see #375).
    pub verify_dispatch: DispatchVerifyMode,
    /// Optional per-function profiling hooks inserted at JIT entry.
    pub profile_hooks: ProfileHookMode,
    /// Convenience flag equivalent to `profile_hooks = ProfileHookMode::CallCounts`.
    ///
    /// When `true`, the JIT emits one atomic `u64` counter per function,
    /// incremented at function entry, readable via
    /// [`ExecutableBuffer::entry_count`]. This is the public name for the
    /// function-entry slice of #364 (see issue #478).
    ///
    /// If `profile_hooks` is also set to anything other than `None`, that
    /// explicit setting wins. Use `emit_entry_counters` as the ergonomic
    /// default; reach for `profile_hooks` for finer control.
    pub emit_entry_counters: bool,
    /// JIT-5: whether function verification may be satisfied from the
    /// content-addressed certificate cache (warm-hit fast path).
    ///
    /// Only meaningful when `verify` is true. `CachedVerified` sets this true
    /// (a cache miss still re-verifies — never skips); `AlwaysVerify` sets it
    /// false so every compile re-discharges. Default `true` so the common
    /// verifying path is warm-fast; the fail-closed guarantee is unaffected
    /// either way because the cache is bytes-bound.
    pub cache_certificates: bool,
}

impl Default for JitConfig {
    fn default() -> Self {
        Self {
            opt_level: OptLevel::O2,
            verify: false,
            // #375: Default to ErrorOnFailure so dispatch-verification
            // failures are not silently swallowed. Callers that want the
            // previous silent-fallback behaviour must opt in explicitly.
            verify_dispatch: DispatchVerifyMode::ErrorOnFailure,
            profile_hooks: ProfileHookMode::None,
            emit_entry_counters: false,
            cache_certificates: true,
        }
    }
}

/// Look up a symbol in the current process's symbol table.
///
/// This is a raw external-symbol resolver used by the low-level JIT path
/// when patching call veneers. It is not a product dispatch or install
/// evidence API; product callers must bind callable entrypoints through a
/// manifest-backed [`SymbolLookupContract`].
///
/// Uses `dlsym(RTLD_DEFAULT, ...)` on Unix. This finds any symbol visible in
/// the current process, including `#[no_mangle] pub extern "C"` functions
/// defined in the calling binary.
///
/// Returns `None` if the symbol is not found, or if the name contains an
/// interior NUL byte (which is invalid for a C string).
///
/// # Safety
/// The returned pointer is only valid as long as the symbol exists in the
/// process. For dynamically loaded libraries this means until the library
/// is unloaded. For symbols in the main binary, the pointer is valid for
/// the lifetime of the process.
#[cfg(unix)]
pub fn lookup_process_symbol(name: &str) -> Option<*const u8> {
    let c_name = std::ffi::CString::new(name).ok()?;
    // SAFETY: Clearing dlerror state before dlsym is the documented way to
    // distinguish a NULL symbol value from a lookup failure.
    unsafe {
        dl::dlerror();
    }
    // SAFETY: `dl::RTLD_DEFAULT` is the documented pseudo-handle for the
    // current process symbol table. `c_name.as_ptr()` is a valid NUL-terminated
    // string for the duration of this call, and dlsym does not retain it.
    let ptr = unsafe { dl::dlsym(dl::RTLD_DEFAULT, c_name.as_ptr()) };
    if ptr.is_null() {
        None
    } else {
        Some(ptr as *const u8)
    }
}

#[cfg(windows)]
mod win_process_symbols {
    use core::ffi::{c_char, c_void};

    #[link(name = "kernel32")]
    unsafe extern "system" {
        fn GetCurrentProcess() -> *mut c_void;
        fn GetModuleHandleW(lp_module_name: *const u16) -> *mut c_void;
        fn GetProcAddress(h_module: *mut c_void, lp_proc_name: *const c_char) -> *mut c_void;
        fn K32EnumProcessModules(
            h_process: *mut c_void,
            lph_module: *mut *mut c_void,
            cb: u32,
            lpcb_needed: *mut u32,
        ) -> i32;
    }

    pub(super) fn lookup(c_name: &std::ffi::CStr) -> Option<*const u8> {
        unsafe {
            let main_module = GetModuleHandleW(std::ptr::null());
            if !main_module.is_null() {
                let ptr = GetProcAddress(main_module, c_name.as_ptr());
                if !ptr.is_null() {
                    return Some(ptr.cast());
                }
            }

            let process = GetCurrentProcess();
            let mut modules = [std::ptr::null_mut(); 1024];
            let mut needed = 0u32;
            let byte_len = std::mem::size_of_val(&modules) as u32;
            if K32EnumProcessModules(process, modules.as_mut_ptr(), byte_len, &mut needed) == 0 {
                return None;
            }

            let count = ((needed as usize) / std::mem::size_of::<*mut c_void>()).min(modules.len());
            for &module in modules.iter().take(count) {
                if module.is_null() {
                    continue;
                }
                let ptr = GetProcAddress(module, c_name.as_ptr());
                if !ptr.is_null() {
                    return Some(ptr.cast());
                }
            }
        }

        None
    }
}

#[cfg(windows)]
pub fn lookup_process_symbol(name: &str) -> Option<*const u8> {
    let c_name = std::ffi::CString::new(name).ok()?;
    win_process_symbols::lookup(&c_name)
}

#[cfg(not(any(unix, windows)))]
pub fn lookup_process_symbol(_name: &str) -> Option<*const u8> {
    None
}

fn resolve_extern(name: &str, extern_symbols: &HashMap<String, *const u8>) -> Option<*const u8> {
    if let Some(&ptr) = extern_symbols.get(name) {
        return Some(ptr);
    }
    if let Some(ptr) = lookup_process_symbol(name) {
        return Some(ptr);
    }
    #[cfg(target_os = "macos")]
    if let Some(stripped) = name.strip_prefix('_')
        && let Some(ptr) = lookup_process_symbol(stripped)
    {
        return Some(ptr);
    }
    None
}

fn has_explicit_extern(name: &str, extern_symbols: &HashMap<String, *const u8>) -> bool {
    extern_symbols.contains_key(name)
}

#[cfg(feature = "verify")]
fn jit_lowering_target() -> &'static str {
    if cfg!(target_arch = "aarch64") {
        "aarch64"
    } else if cfg!(target_arch = "x86_64") {
        "x86_64"
    } else {
        std::env::consts::ARCH
    }
}

#[cfg(feature = "verify")]
fn jit_lowering_compiler_config_bytes(
    config: &PipelineConfig,
    profile_hooks: ProfileHookMode,
) -> Vec<u8> {
    format!(
        concat!(
            "trust-cg.jit.compiler_config.v1\n",
            "target={}\n",
            "opt_level={:?}\n",
            "verify={}\n",
            "verify_dispatch={:?}\n",
            "profile_hooks={:?}\n",
            "emit_debug={}\n",
            "cegis_superopt_budget_sec={:?}\n",
            "target_triple={}\n"
        ),
        jit_lowering_target(),
        config.opt_level,
        config.verify,
        config.verify_dispatch,
        profile_hooks,
        config.emit_debug,
        config.cegis_superopt_budget_sec,
        config.target_triple,
    )
    .into_bytes()
}

pub struct JitCompiler {
    /// Pipeline constructed from the caller-supplied [`JitConfig`]. Held for
    /// forward compatibility: `compile_raw` does not currently invoke the
    /// pipeline, but the config (notably `verify_dispatch`, see #375) must
    /// be preserved so future heterogeneous-aware JIT entry points inherit
    /// the caller's policy. Also reached from unit tests via the
    /// `#[cfg(test)] pipeline()` accessor.
    #[allow(dead_code)]
    pipeline: Pipeline,
    profile_hooks: ProfileHookMode,
    /// JIT-5: whether the verify branch may satisfy the obligation from the
    /// content-addressed certificate cache. Mirrors
    /// [`JitConfig::cache_certificates`]; kept on the compiler (not
    /// `PipelineConfig`) so the low-level pipeline stays untouched.
    // Read only in the verifying cert branch (feature = "verify").
    #[cfg_attr(not(feature = "verify"), allow(dead_code))]
    cache_certificates: bool,
}

impl JitCompiler {
    pub fn new(config: JitConfig) -> Self {
        let profile_hooks =
            if config.profile_hooks == ProfileHookMode::None && config.emit_entry_counters {
                ProfileHookMode::CallCounts
            } else {
                config.profile_hooks
            };
        Self {
            pipeline: Pipeline::new(PipelineConfig {
                opt_level: config.opt_level,
                emit_debug: false,
                // #375: Propagate caller-visible dispatch-verification policy
                // instead of hard-coding FallbackOnFailure. The JitConfig
                // default is ErrorOnFailure so failures surface as errors.
                verify_dispatch: config.verify_dispatch,
                verify: config.verify,
                // CEGIS superopt is not scheduled by the JIT path; the
                // budget knob is only wired into the batch compiler (AOT).
                cegis_superopt_budget_sec: None,
                target_triple: String::new(),
                enable_fsym_trust_ir_preflight: false,
                // The legacy raw-MachFunction JitCompiler defaults to the
                // full quality regalloc. The latency-tuned profile is
                // currently wired through CompilerConfig::for_host_jit
                // (the typed trust_ir/module JIT API).
                enable_jit_fast_regalloc: false,
                // Full quality regalloc => keep CSE/GVN (remat is available).
                skip_cse_gvn: false,
                // Raw JIT callers preserve the process-level compatibility
                // controls unless they prepare IR through an explicitly
                // configured Pipeline first.
                disabled_passes_override: None,
                contains4_scanner_batch_rewrite_override: None,
            }),
            profile_hooks,
            cache_certificates: config.cache_certificates,
        }
    }

    /// Report what proof evidence this JIT compiler's configuration actually
    /// produces, and what it relies on rather than checks.
    ///
    /// The fast JIT route returns a bare [`ExecutableBuffer`], which carries no
    /// evidence field of its own, so a consumer had no way to tell a compile
    /// where lowering proofs ran from one where nothing ran. This accessor
    /// makes the negative case readable: a compiler built with `verify: false`
    /// and [`crate::pipeline::DispatchVerifyMode::Off`] reports
    /// [`crate::jit_contract::ProofEvidenceVerdict::MissingEvidence`] at
    /// [`crate::jit_contract::EvidenceStrength::NotRun`], together with the
    /// assumptions that compile is resting on.
    ///
    /// Reporting only: calling this runs no verifier and changes no behaviour.
    pub fn proof_evidence(&self) -> crate::jit_contract::ProofEvidenceSummary {
        self.pipeline.proof_evidence()
    }

    /// Returns a reference to the underlying compilation pipeline.
    ///
    /// Test-only accessor (`#[cfg(test)]`) used by the dispatch-verification
    /// default regression tests (#375) to reach
    /// [`Pipeline::generate_and_verify_dispatch`] without adding a
    /// permanent public API surface. Not part of the supported JIT API.
    #[cfg(test)]
    pub(crate) fn pipeline(&self) -> &Pipeline {
        &self.pipeline
    }

    /// Compile post-regalloc IR functions to executable memory.
    ///
    /// `extern_symbols` maps mangled names (e.g., `"_helper"`) to host addresses.
    ///
    /// # Symbol uniqueness
    ///
    /// Every function's primary name and its `_`-prefixed Mach-O alias must
    /// be unique across the entire `functions` slice. A duplicate in either
    /// slot — e.g., two functions named `"foo"`, or one `"foo"` and one
    /// `"_foo"` (whose primary key collides with the first's alias) —
    /// returns [`JitError::DuplicateSymbol`] instead of silently
    /// overwriting the earlier function's offset (#374).
    ///
    /// Direct named calls resolve canonical function names as internal. If a
    /// target matches only a generated `_name` alias, external symbol
    /// resolution takes precedence and the alias is used only as a
    /// compatibility fallback.
    ///
    /// Nonempty raw input is currently AArch64-only: `MachFunction` does not
    /// carry an architecture tag, while this legacy encoder interprets its
    /// opcodes as AArch64. Other hosts fail closed before encoding; use the
    /// typed [`crate::Compiler`] JIT for x86-64.
    pub fn compile_raw(
        &self,
        functions: &[IrMachFunction],
        extern_symbols: &HashMap<String, *const u8>,
    ) -> Result<ExecutableBuffer, JitError> {
        self.compile_raw_inner(functions, extern_symbols, |_func, _duration| {})
    }

    /// Internal variant of [`Self::compile_raw`] that also reports
    /// per-function encoding durations to the caller.
    pub(crate) fn compile_raw_with_encoding_metrics(
        &self,
        functions: &[IrMachFunction],
        extern_symbols: &HashMap<String, *const u8>,
    ) -> Result<(ExecutableBuffer, HashMap<String, Duration>), JitError> {
        let mut encoding_timings = HashMap::with_capacity(functions.len());
        let buffer = self.compile_raw_inner(functions, extern_symbols, |func, duration| {
            encoding_timings.insert(func.name.clone(), duration);
        })?;
        Ok((buffer, encoding_timings))
    }

    fn compile_raw_inner<F>(
        &self,
        functions: &[IrMachFunction],
        extern_symbols: &HashMap<String, *const u8>,
        mut record_encoding: F,
    ) -> Result<ExecutableBuffer, JitError>
    where
        F: FnMut(&IrMachFunction, Duration),
    {
        if let Some(func) = functions.iter().find(|func| func.eh_metadata.has_eh_info()) {
            return Err(JitError::RawJitEhUnsupported {
                function: func.name.clone(),
            });
        }

        if !functions.is_empty() && !cfg!(target_arch = "aarch64") {
            return Err(JitError::RawJitTargetMismatch {
                function: functions[0].name.clone(),
                host_arch: std::env::consts::ARCH,
            });
        }

        if !sys::host_supported() {
            return Err(JitError::UnsupportedHost {
                arch: std::env::consts::ARCH,
                os: std::env::consts::OS,
            });
        }

        // #396 Phase 2: block/edge/frequency/loop-head modes are API
        // reserved but the trampoline emitter has not been extended
        // yet. Reject early so the caller gets a clear diagnostic
        // instead of silently producing unhooked code.
        if profile_hooks_is_phase2_stub(self.profile_hooks) {
            return Err(JitError::ProfileHookModeUnimplemented {
                mode: self.profile_hooks,
            });
        }
        // x86-64 has an entry counter trampoline, but not the timing
        // instrumentation required by `CallCountsAndTiming`. Reject this mode
        // explicitly so it cannot be mistaken for supported count-only
        // profiling.
        #[cfg(target_arch = "x86_64")]
        if self.profile_hooks == ProfileHookMode::CallCountsAndTiming {
            return Err(JitError::ProfileHooksUnsupported);
        }
        let mut code = Vec::with_capacity(functions.len() * 128);
        let mut fixups: Vec<Fixup> = Vec::new();
        // Canonical internal function definitions only. Named fixups use this
        // map to decide whether a direct target is definitely internal.
        let mut func_offsets: HashMap<String, u64> = HashMap::new();
        // Alias-aware lookup table handed to ExecutableBuffer and used as the
        // fallback for legacy internal `_name` call compatibility.
        let mut symbol_offsets: HashMap<String, u64> = HashMap::new();
        let mut counters: HashMap<String, Box<AtomicU64>> = HashMap::new();
        // Per-block `{count, total_cycles}` cells, populated only under
        // `ProfileHookMode::BlockCountsAndTiming` (#364 Phase 3). Otherwise
        // left empty and handed off to the `ExecutableBuffer` as-is.
        #[cfg(target_arch = "aarch64")]
        let mut timing_cells: HashMap<String, Box<BlockTimingCell>> = HashMap::new();
        #[cfg(not(target_arch = "aarch64"))]
        let timing_cells: HashMap<String, Box<BlockTimingCell>> = HashMap::new();
        // Per-buffer `TimingState`. `Some` iff `BlockCountsAndTiming` is
        // enabled for this compile. Allocated upfront (before the first
        // trampoline is emitted) so the trampolines' literal-pool patches
        // can bake in a stable address.
        let mut timing_state: Option<Box<TimingState>> = None;
        // Canonical (user-provided) function names in insertion order. This is
        // the authoritative symbol list — `symbol_offsets` contains additional
        // alias keys (`"_foo"` for Mach-O dlsym compatibility), which are
        // lookup conveniences rather than independent symbols. (Fix #360.)
        let mut canonical_symbols: Vec<String> = Vec::with_capacity(functions.len());
        let profile_counters_enabled = profile_hooks_enable_counters(self.profile_hooks);
        let profile_block_counters_enabled =
            profile_hooks_enable_block_counters(self.profile_hooks);
        let profile_block_timing_enabled = profile_hooks_enable_block_timing(self.profile_hooks);
        debug_assert!(
            profile_hooks_counter_classifiers_are_disjoint(self.profile_hooks),
            "profile hook mode {:?} must not emit both function-entry and block-entry counters",
            self.profile_hooks
        );

        if profile_counters_enabled && !cfg!(any(target_arch = "aarch64", target_arch = "x86_64")) {
            return Err(JitError::ProfileHooksUnsupported);
        }

        // Raw JitCompiler BlockCounts is implemented on AArch64 only. The
        // higher-level Compiler trust_ir JIT has an x86-64 counter-injection path
        // for CLI profile-generate, but this raw MachIR splice surface still
        // fails closed until x86-64 raw block splicing/repatching exists.
        if profile_block_counters_enabled && !cfg!(target_arch = "aarch64") {
            return Err(JitError::ProfileHooksUnsupported);
        }

        // #364 Phase 3 BlockCountsAndTiming is likewise AArch64-only in the
        // initial landing — the timing trampoline uses the `MRS CNTVCT_EL0`
        // virtual-counter system register. An x86-64 port (using `RDTSC`)
        // is tracked as a follow-up.
        if profile_block_timing_enabled && !cfg!(target_arch = "aarch64") {
            return Err(JitError::ProfileHooksUnsupported);
        }

        // Allocate the single per-buffer `TimingState` upfront so the
        // trampolines' literal slots can capture a stable address.
        if profile_block_timing_enabled {
            timing_state = Some(Box::new(TimingState {
                prev_ts: AtomicU64::new(0),
                prev_accum_ptr: AtomicU64::new(0),
            }));
        }

        let mut counter_patch_sites: Vec<(usize, *const AtomicU64)> =
            Vec::with_capacity(functions.len());
        // Per-buffer `&TimingState` patch sites. Populated only under
        // `BlockCountsAndTiming`; drained after the code buffer is mapped.
        #[cfg(target_arch = "aarch64")]
        let mut tstate_patch_sites: Vec<usize> = Vec::new();
        #[cfg(not(target_arch = "aarch64"))]
        let tstate_patch_sites: Vec<usize> = Vec::new();

        // Per-function byte ranges in the code buffer. Used by the proof
        // certificate path (issue #348) to tell callers which bytes each
        // certified function occupies. Populated regardless of whether
        // verification is enabled; certificate construction itself is
        // gated on `self.pipeline` config below.
        let mut func_ranges: Vec<(String, std::ops::Range<u64>)> =
            Vec::with_capacity(functions.len());

        // Encode all functions into a contiguous buffer.
        for func in functions {
            let start = code.len() as u64;
            let mut body_start = start;
            if symbol_offsets.contains_key(func.name.as_str()) {
                return Err(JitError::DuplicateSymbol(func.name.clone()));
            }

            // Insert the underscore-prefixed alias so Mach-O-style lookups
            // (`"_foo"`) resolve to the same offset. If the canonical name
            // already begins with `_` this happens to produce `"__foo"`,
            // which is harmless: it is never consulted by `symbols()` or
            // `symbol_count()` because those iterate `canonical_symbols`.
            //
            // The "Mach-O-style" naming here refers to a caller convention
            // (the leading underscore C symbols get under darwin), not to an
            // object-file format. On Linux hosts (#346) this alias is a
            // dormant extra key in the lookup map unless a caller explicitly
            // asks for the `_`-prefixed form, so leaving it in place keeps
            // the JIT's public symbol API identical across macOS and Linux.
            let alias = format!("_{}", func.name);
            if symbol_offsets.contains_key(alias.as_str()) {
                return Err(JitError::DuplicateSymbol(alias));
            }
            canonical_symbols.push(func.name.clone());
            func_offsets.insert(func.name.clone(), start);
            symbol_offsets.insert(func.name.clone(), start);
            symbol_offsets.insert(alias, start);

            if profile_counters_enabled {
                let counter = Box::new(AtomicU64::new(0));
                let counter_ptr = counter.as_ref() as *const AtomicU64;
                counters.insert(func.name.clone(), counter);
                if cfg!(target_arch = "aarch64") {
                    #[cfg(target_arch = "aarch64")]
                    {
                        let literal_slot_offset = emit_profile_trampoline_aarch64(&mut code);
                        counter_patch_sites.push((literal_slot_offset, counter_ptr));
                    }
                } else if cfg!(target_arch = "x86_64") {
                    #[cfg(target_arch = "x86_64")]
                    {
                        let imm64_offset = emit_profile_trampoline_x86_64(&mut code);
                        counter_patch_sites.push((imm64_offset, counter_ptr));
                    }
                } else {
                    return Err(JitError::ProfileHooksUnsupported);
                }
                body_start = code.len() as u64;
            }

            let encode_start = Instant::now();
            let (bytes, fxs) = if profile_block_counters_enabled {
                // #364 BlockCounts path (AArch64-only at present).
                //
                // 1. Encode the function normally and capture per-block byte
                //    offsets so we can splice in a trampoline at the start
                //    of every block.
                // 2. Allocate one `AtomicU64` per basic block, keyed as
                //    `"{func.name}::block{block_id.0}"`. The entry block's
                //    counter doubles as the function-entry counter and is
                //    re-exposed under `func.name` via a read-side alias on
                //    `ExecutableBuffer::get_profile` / `entry_count`.
                // 3. Run `splice_block_trampolines_aarch64`, which returns
                //    the spliced bytes plus the list of
                //    `(block_id, literal_slot_offset_within_spliced_bytes)`
                //    patch sites. Fixup offsets are shifted in-place so
                //    external symbol fixups still index the correct branch
                //    instruction.
                // 4. Register each patch site against `counter_patch_sites`
                //    so the late-binding code that writes counter pointers
                //    into the mmap'd buffer picks them up uniformly with
                //    the per-function trampolines.
                #[cfg(target_arch = "aarch64")]
                {
                    let (body_bytes, mut block_fixups, block_byte_offsets) =
                        encode_function_with_fixups_and_blocks(func)?;
                    record_encoding(func, encode_start.elapsed());

                    // Allocate per-block counters.
                    let mut block_counter_ptrs: HashMap<BlockId, *const AtomicU64> =
                        HashMap::with_capacity(func.block_order.len());
                    for &bid in func.block_order.iter() {
                        let key = format!("{}::block{}", func.name, bid.0);
                        if counters.contains_key(&key) {
                            return Err(JitError::DuplicateSymbol(key));
                        }
                        let counter = Box::new(AtomicU64::new(0));
                        let counter_ptr = counter.as_ref() as *const AtomicU64;
                        block_counter_ptrs.insert(bid, counter_ptr);
                        counters.insert(key, counter);
                    }

                    let (spliced, tramp_sites) = splice_block_trampolines_aarch64(
                        func,
                        &body_bytes,
                        &block_byte_offsets,
                        block_fixups.as_mut_slice(),
                    )?;

                    // Register patch sites: translate each
                    // (block_id, literal_slot_offset_within_spliced) into
                    // (buffer_absolute_offset, counter_ptr).
                    let func_base = code.len();
                    register_block_counter_patch_sites(
                        &func.name,
                        &block_counter_ptrs,
                        &tramp_sites,
                        func_base,
                        &mut counter_patch_sites,
                    )?;

                    // The first block's trampoline IS the function entry
                    // point, so body_start must point at the start of the
                    // spliced region (not past it). The per-function
                    // trampoline emitted above when `profile_counters_enabled`
                    // is mutually exclusive with BlockCounts, so body_start
                    // is still `start` here.
                    debug_assert!(!profile_counters_enabled);
                    (spliced, block_fixups)
                }
                #[cfg(not(target_arch = "aarch64"))]
                {
                    // Unreachable: guarded by the top-of-function arch
                    // check. Included so this branch type-checks on all
                    // architectures.
                    unreachable!("profile_block_counters_enabled implies target_arch = aarch64")
                }
            } else if profile_block_timing_enabled {
                // #364 Phase 3 BlockCountsAndTiming path (AArch64-only).
                //
                // Mirrors the plain-counter path above but:
                // - Allocates one `BlockTimingCell {count, total_cycles}`
                //   per basic block instead of a single counter.
                // - Calls `splice_block_trampolines_with_timing_aarch64`,
                //   which emits 108-byte timing trampolines and returns
                //   two patch-site offsets per block (counter literal and
                //   `TimingState` literal).
                // - Pushes each (counter_ptr) site onto
                //   `counter_patch_sites` and each (tstate) site onto
                //   `tstate_patch_sites`; both lists are drained after
                //   the mmap is written, identical in shape to the plain
                //   counter path.
                #[cfg(target_arch = "aarch64")]
                {
                    let (body_bytes, mut block_fixups, block_byte_offsets) =
                        encode_function_with_fixups_and_blocks(func)?;
                    record_encoding(func, encode_start.elapsed());

                    // Allocate per-block timing cells. Capture raw pointers
                    // to the `count` field — the trampoline increments
                    // `count` at offset 0 of the cell, so the LDR/ADD/STR
                    // targets the cell's start address directly.
                    let mut block_cell_ptrs: HashMap<BlockId, *const AtomicU64> =
                        HashMap::with_capacity(func.block_order.len());
                    for &bid in func.block_order.iter() {
                        let key = format!("{}::block{}", func.name, bid.0);
                        if counters.contains_key(&key) || timing_cells.contains_key(&key) {
                            return Err(JitError::DuplicateSymbol(key));
                        }
                        let cell = Box::new(BlockTimingCell {
                            count: AtomicU64::new(0),
                            total_cycles: AtomicU64::new(0),
                        });
                        // `&cell.count` sits at offset 0 of a `#[repr(C)]`
                        // BlockTimingCell, so its address equals the cell's
                        // address. The trampoline writes `total_cycles` at
                        // cell + 8 via an explicit `ADD X11, X16, #8`.
                        let cell_ptr = &cell.count as *const AtomicU64;
                        block_cell_ptrs.insert(bid, cell_ptr);
                        timing_cells.insert(key, cell);
                    }

                    let (spliced, tramp_sites) = splice_block_trampolines_with_timing_aarch64(
                        func,
                        &body_bytes,
                        &block_byte_offsets,
                        block_fixups.as_mut_slice(),
                    )?;

                    // Register patch sites for both the counter-cell literal
                    // and the timing-state literal of each block.
                    let func_base = code.len();
                    register_block_timing_patch_sites(
                        &func.name,
                        &block_cell_ptrs,
                        &tramp_sites,
                        func_base,
                        &mut counter_patch_sites,
                        &mut tstate_patch_sites,
                    )?;

                    debug_assert!(!profile_counters_enabled);
                    (spliced, block_fixups)
                }
                #[cfg(not(target_arch = "aarch64"))]
                {
                    unreachable!("profile_block_timing_enabled implies target_arch = aarch64")
                }
            } else {
                let (bytes, fxs) = encode_function_with_fixups(func)?;
                record_encoding(func, encode_start.elapsed());
                (bytes, fxs)
            };
            for fx in fxs.iter() {
                let mut adjusted = fx.clone();
                adjusted.offset += body_start as u32;
                fixups.push(adjusted);
            }
            code.extend_from_slice(&bytes);
            let end = code.len() as u64;
            // When profile hooks are enabled the callable entry point starts
            // at the trampoline, so the certified range must cover the full
            // compiled region from trampoline start through body end.
            func_ranges.push((func.name.clone(), start..end));
        }

        // Resolve internal fixups.
        for fixup in &fixups {
            let addr = match &fixup.target {
                FixupTarget::NamedSymbol(name) => {
                    if has_explicit_extern(name, extern_symbols) {
                        continue;
                    } else if let Some(&off) = func_offsets.get(name) {
                        off
                    } else if resolve_extern(name, extern_symbols).is_some() {
                        continue;
                    } else if let Some(&off) = symbol_offsets.get(name) {
                        off
                    } else {
                        return Err(JitError::UnresolvedSymbol(name.clone()));
                    }
                }
                FixupTarget::Symbol(idx) => {
                    let name = functions
                        .get(*idx as usize)
                        .map(|f| &f.name)
                        .ok_or_else(|| JitError::UnresolvedSymbol(format!("index {}", idx)))?;
                    *func_offsets.get(name.as_str()).unwrap()
                }
                _ => continue,
            };
            patch_fixup(&mut code, fixup.offset, addr)?;
        }

        // Build veneer trampolines for external calls and patch their BL sites.
        //
        // Fix #362: single-pass over fixups — no intermediate clone+Vec+double
        // iteration. `HashMap::entry` dedups veneers in O(1) per fixup while
        // preserving deterministic, first-seen emission order (driven by the
        // deterministic order of `fixups`).
        //
        // Fix #345: on AArch64, BL has +-128 MiB reach. Veneers are appended
        // after all function code; if the module is large, a BL at the start
        // of the buffer may not be able to reach a veneer at the end. We
        // pre-validate each external BL's distance to its veneer and return a
        // typed `VeneerOutOfRange` error instead of letting `patch_branch26`
        // emit a corrupt instruction or surface the generic `BranchOutOfRange`.
        let mut veneers: HashMap<String, u64> = HashMap::new();
        // Deferred patches: (fixup_offset, veneer_offset, symbol_name). We
        // cannot patch while still emitting veneers because emitting grows
        // `code`, and each veneer's final offset is only known at emission
        // time. Collecting the (site, veneer) pairs in one pass lets us patch
        // after all veneers are laid out.
        let mut ext_patches: Vec<(u32, u64, String)> = Vec::new();
        for fixup in &fixups {
            let name = match &fixup.target {
                FixupTarget::NamedSymbol(n)
                    if has_explicit_extern(n, extern_symbols)
                        || (!func_offsets.contains_key(n)
                            && resolve_extern(n, extern_symbols).is_some()) =>
                {
                    n
                }
                _ => continue,
            };
            let veneer_off = *veneers.entry(name.clone()).or_insert_with(|| {
                let pos = code.len() as u64;
                emit_veneer_stub(&mut code);
                pos
            });
            ext_patches.push((fixup.offset, veneer_off, name.clone()));
        }

        // Pre-validate BL reachability for every external fixup before we
        // start mutating the instruction stream. Patching is all-or-nothing:
        // if any BL is out of range we bail out with a descriptive error
        // rather than leaving the buffer half-patched. The check is factored
        // out into `validate_veneer_ranges` so #345 can be regression-tested
        // without emitting >128 MiB of real code.
        validate_veneer_ranges(&ext_patches, code.len())?;

        for (fx_off, veneer_off, _sym) in &ext_patches {
            patch_fixup(&mut code, *fx_off, *veneer_off)?;
        }

        // Zero-byte JIT artifacts are not executable artifacts. Reject before
        // mmap so empty inputs cannot publish an RX buffer or appear in replay
        // metadata as a zero-length native mapping.
        if code.is_empty() {
            return Err(JitError::EmptyExecutableBuffer {
                function_count: functions.len(),
            });
        }

        // JIT-7 publication discipline: all literal patches (profile counters,
        // timing state, veneer target addresses) are applied to a HEAP image
        // first; the mapping then receives exactly one bulk write and is
        // sealed RW->RX with a fail-closed bytes-hash publish check. `code`
        // itself stays unpatched so the proof-certificate path below keeps
        // hashing the deterministic pre-patch machine code exactly as before.
        let mut published_image = code.clone();
        let image_len = published_image.len();

        // Lifetime-invariant check (#494): each baked-in counter pointer
        // MUST point into a `Box` that this function is about to transfer
        // ownership of to the returned `ExecutableBuffer`. Otherwise the
        // trampoline would dereference freed memory the moment this
        // function returns. Build a debug-only set of valid Box addresses
        // (`counters` + `timing_cells.count` fields) and verify every
        // patch site lands in it.
        #[cfg(debug_assertions)]
        {
            use std::collections::HashSet;
            let mut valid: HashSet<usize> =
                HashSet::with_capacity(counters.len() + timing_cells.len());
            for counter in counters.values() {
                valid.insert(counter.as_ref() as *const AtomicU64 as usize);
            }
            for cell in timing_cells.values() {
                // The `count` field is the one referenced by per-block
                // trampolines under `BlockCounts` and the counter slot of
                // `BlockCountsAndTiming`. `total_cycles` is addressed via
                // `TimingState::prev_accum_ptr` (stored at runtime, not at
                // compile time), so it is NOT a patch-site target.
                valid.insert(&cell.count as *const AtomicU64 as usize);
            }
            for (patch_offset, counter_ptr) in &counter_patch_sites {
                debug_assert!(
                    !counter_ptr.is_null(),
                    "counter patch site at offset {} has null counter pointer",
                    patch_offset
                );
                debug_assert!(
                    valid.contains(&(*counter_ptr as usize)),
                    "counter patch site at offset {} points outside the \
                     ExecutableBuffer-owned counter/timing_cell boxes \
                     (counter_ptr = {:p}); would dangle on return (see #494)",
                    patch_offset,
                    *counter_ptr
                );
            }
        }

        for (patch_offset, counter_ptr) in &counter_patch_sites {
            // `patch_offset` points at the 8-byte immediate / literal slot
            // inside a trampoline within the heap image, and `counter_ptr`
            // points at the owned `AtomicU64` backing that trampoline. The
            // debug_assert above verifies that `counter_ptr` lands in a `Box`
            // being transferred into the returned `ExecutableBuffer` (#494
            // invariant). Out-of-bounds slots fail closed.
            write_u64_literal_in_image(
                &mut published_image,
                image_len,
                *patch_offset,
                *counter_ptr as u64,
            )?;
        }

        // Patch the `&TimingState` literal slot in every
        // `BlockCountsAndTiming` trampoline. The `timing_state` allocation
        // is owned by the `ExecutableBuffer` so the baked-in pointer stays
        // valid for the lifetime of the executable mapping.
        if let Some(tstate) = timing_state.as_ref() {
            let tstate_ptr = &**tstate as *const TimingState as u64;
            for patch_offset in &tstate_patch_sites {
                write_u64_literal_in_image(
                    &mut published_image,
                    image_len,
                    *patch_offset,
                    tstate_ptr,
                )?;
            }
        } else {
            debug_assert!(
                tstate_patch_sites.is_empty(),
                "tstate patch sites registered without an allocated TimingState"
            );
        }

        // Resolve every veneer's external target BEFORE any mapping exists:
        // an unresolved symbol now fails closed with nothing to unmap.
        // `veneer_off` was produced from `code.len()` during veneer emission
        // and `veneer_addr_offset()` lands on the embedded 64-bit address
        // slot within that veneer stub (instruction-aligned, not necessarily
        // 8-byte aligned — the image writer handles that).
        for (name, &veneer_off) in &veneers {
            let ext_addr = resolve_extern(name, extern_symbols)
                .ok_or_else(|| JitError::UnresolvedSymbol(name.clone()))?;
            write_u64_literal_in_image(
                &mut published_image,
                image_len,
                veneer_off as usize + veneer_addr_offset(),
                ext_addr as u64,
            )?;
        }

        // Allocate RW memory, bulk-copy the fully-patched image, then seal
        // RW->RX with the fail-closed bytes-hash publish check. On Apple
        // Silicon, `JitWriteGuard` additionally switches the current thread's
        // MAP_JIT pages into write mode and restores execute mode before the
        // returned `ExecutableBuffer` exposes function pointers. `MappedRegion`
        // owns the pages: every error path from here on unmaps via Drop.
        let expected_sha256 = crate::jit_diagnostics::sha256_hex(&published_image);
        let alloc_size = sys::page_align(image_len);
        let mut region = MappedRegion::allocate_rw(alloc_size)?;
        let jit_write_guard = sys::JitWriteGuard::enter();
        unsafe {
            // SAFETY: `region` owns a writable allocation of `alloc_size >=
            // image_len` bytes; `published_image` is heap memory distinct
            // from the fresh mapping.
            std::ptr::copy_nonoverlapping(published_image.as_ptr(), region.as_mut_ptr(), image_len);
        }
        corrupt_published_byte_if_requested(region.as_mut_ptr(), image_len);
        // Seal: icache flush (while still RW — ARM ARM ordering, #357), the
        // single RW->RX flip, then the read-back hash verification.
        region.seal_rx_and_verify(image_len, &expected_sha256)?;
        drop(jit_write_guard);
        // NOTE: `region` intentionally stays alive across the certificate
        // block below — a panic inside `verify_function` unwinds through
        // `region`'s Drop and unmaps instead of leaking the mapping.

        // Proof-certificate path (issue #348).
        //
        // When `JitConfig::verify` is set we run trust-cg-verify's
        // `verify_function` for each compiled function and attach a
        // `JitCertificate` (containing the full `CertificateChain` plus
        // coarse trust_ir provenance) to the `ExecutableBuffer`. Callers such
        // as ty can then ask `buffer.certificate(name)` to prove that
        // the JIT'd machine code was verified against its trust_ir input. The
        // recorded byte range already includes any prepended profile
        // trampoline so the certificate covers the full callable region.
        //
        // When `verify` is off, `certificates` stays empty and the
        // `ExecutableBuffer::certificate` accessor returns `None`, keeping
        // the fast-path cost of JIT compilation unchanged.
        #[cfg(feature = "verify")]
        let certificates: HashMap<String, crate::jit_cert::JitCertificate> =
            if self.pipeline.config.verify {
                let compiler_config_bytes =
                    jit_lowering_compiler_config_bytes(&self.pipeline.config, self.profile_hooks);
                // JIT-5: consult the process-global content-addressed
                // certificate cache. The AArch64 JitCertificate path has the
                // emitted machine bytes available at verify time, so the cache
                // key folds those exact bytes with the config fingerprint — a
                // warm hit reuses the verdict WITHOUT re-running
                // `verify_function` (no solver spawn), rebound to this buffer's
                // range. A miss verifies and populates. Nothing here can turn an
                // unverified function into a verified one.
                let cache = crate::jit_cert::JitCertCache::global();
                let use_cache = self.cache_certificates && cache.is_enabled();
                let mut certs = HashMap::with_capacity(functions.len());
                for (func, (_name, range)) in functions.iter().zip(func_ranges.iter()) {
                    let machine_code_bytes = &code[range.start as usize..range.end as usize];
                    let key = crate::jit_cert::JitCertCacheKey::new(
                        machine_code_bytes,
                        &compiler_config_bytes,
                    );
                    let cached = if use_cache { cache.peek(&key) } else { None };
                    let cert = match cached {
                        Some(v) if v.aarch64_cert.is_some() => {
                            cache.record_hit();
                            v.aarch64_cert
                                .expect("peeked aarch64_cert present")
                                .rebound(range.clone())
                        }
                        _ => {
                            if use_cache {
                                cache.record_miss();
                            }
                            let report = crate::jit_cert::run_on_proof_verifier_stack(
                                "trust-cg-jit-proof-verifier",
                                || trust_cg_verify::verify_function(func),
                            );
                            let fresh = crate::jit_cert::JitCertificate::from_report(
                                func,
                                &report,
                                range.clone(),
                                jit_lowering_target(),
                                machine_code_bytes,
                                &compiler_config_bytes,
                            );
                            if use_cache {
                                cache.store(
                                    key,
                                    crate::jit_cert::CachedFunctionVerdict {
                                        verified: fresh.is_verified(),
                                        emitted_bytes_sha256: crate::jit_diagnostics::sha256_hex(
                                            machine_code_bytes,
                                        ),
                                        x86_proof_certs: Vec::new(),
                                        aarch64_cert: Some(fresh.clone()),
                                    },
                                );
                            }
                            fresh
                        }
                    };
                    certs.insert(func.name.clone(), cert);
                }
                certs
            } else {
                HashMap::new()
            };

        #[cfg(not(feature = "verify"))]
        let certificates: HashMap<String, crate::jit_cert::JitCertificate> = HashMap::new();

        let (memory, alloc_size) = region.into_published_parts();
        let allocation_cookie =
            executable_buffer_allocation_cookie(memory, alloc_size, code.len(), code.len());
        let buffer = ExecutableBuffer {
            memory,
            len: alloc_size,
            len_shadow: alloc_size,
            allocation_cookie,
            code_len: code.len(),
            published_len: code.len(),
            published_image_sha256: expected_sha256,
            publication: JitPublicationContract::published_rx(),
            windows_unwind: WindowsJitUnwindRegistration,
            function_ranges: func_ranges,
            symbol_offsets,
            canonical_symbols,
            counters,
            timing_cells,
            timing_state,
            certificates,
            proof_optimization_certificates: Vec::new(),
        };
        debug_assert_eq!(buffer.allocation_len_opaque(), alloc_size);
        debug_assert_eq!(buffer.allocation_len_from_published_len(), alloc_size);
        debug_assert_eq!(buffer.allocation_cookie_opaque(), allocation_cookie);
        Ok(buffer)
    }
}

/// Publication state for an executable JIT mapping.
///
/// The mapping's VM permissions are process-wide, but Apple Silicon `MAP_JIT`
/// also has a per-thread write/execute toggle. A callable lookup can happen on
/// a different thread from compilation, so the buffer records enough
/// publication state to restore execute mode for the current lookup thread.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct JitPublicationContract {
    /// The mapping was allocated with `MAP_JIT`.
    pub map_jit: bool,
    /// The host reports support for pthread JIT write-protect toggling.
    pub write_protect_supported: bool,
    /// The mapping reached the published read-execute state.
    pub published_rx: bool,
}

impl JitPublicationContract {
    fn current_platform(published_rx: bool) -> Self {
        Self {
            map_jit: sys::uses_map_jit(),
            write_protect_supported: sys::jit_write_protect_supported(),
            published_rx,
        }
    }

    fn published_rx() -> Self {
        Self::current_platform(true)
    }

    #[cfg(test)]
    fn unpublished_for_tests() -> Self {
        Self::current_platform(false)
    }
}

/// Structured evidence that a cached raw JIT symbol pointer is owned by a
/// published executable buffer and exactly matches the requested symbol.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JitSymbolPublicationProof {
    pub symbol: String,
    pub pointer: u64,
    pub buffer_base: u64,
    pub buffer_end: u64,
    pub code_len: usize,
    pub published_len: usize,
    pub allocation_len: usize,
    pub expected_symbol_offset: u64,
    pub actual_ptr_offset: u64,
    pub exact_symbol_match: bool,
    pub publication_contract: JitPublicationContract,
    pub mprotect_rx_ok: bool,
    pub execute_mode_reasserted: bool,
    pub first_code_bytes: Option<Vec<u8>>,
}

/// A typed JIT function pointer tied to the lifetime of the owning
/// [`ExecutableBuffer`]. Cannot outlive the buffer by construction.
///
/// This is the lifetime-safe form of the raw lookup surface. It does not
/// validate artifact identity, target/layout compatibility, proof policy, or
/// downstream invalidation state. Product `ay`/`ty` dispatch must use
/// [`crate::compile_service::InstalledArtifact::get_contract_symbol_bound`]
/// instead; a bare executable buffer is not artifact/signature authority.
///
/// ```compile_fail
/// use trust_cg_codegen::jit::{JitCompiler, JitConfig};
/// use std::collections::HashMap;
///
/// let jit = JitCompiler::new(JitConfig::default());
/// let ext: HashMap<String, *const u8> = HashMap::new();
/// let buf = jit.compile_raw(&[], &ext).unwrap();
/// let func = unsafe { buf.get_fn_bound::<extern "C" fn()>("foo") };
/// drop(buf);
/// let _ = func;
/// ```
#[derive(Copy, Clone)]
pub struct JitFn<'a, F: Copy> {
    inner: F,
    _marker: PhantomData<&'a ExecutableBuffer>,
}

impl<'a, F: Copy> JitFn<'a, F> {
    /// Returns the underlying `F`. Still safe because `F` itself is
    /// typically an `extern "C" fn(...)` — which is `Copy + 'static` —
    /// so the lifetime exists only on the wrapper. Callers that leak
    /// the inner `F` past the buffer's lifetime re-enter the unsafe
    /// world. Prefer `as_ref` / keep the `JitFn` wrapper in scope.
    pub fn into_inner(self) -> F {
        self.inner
    }
}

impl<F: Copy> AsRef<F> for JitFn<'_, F> {
    /// Returns a reference to the underlying `F` without consuming the
    /// lifetime guard. This is the recommended way to use a `JitFn`.
    fn as_ref(&self) -> &F {
        &self.inner
    }
}

/// A raw code pointer tied to the lifetime of the owning buffer.
///
/// This is a low-level escape hatch for wrappers and tests that need the raw
/// address. It is not sufficient for product dispatch unless a
/// manifest-backed [`SymbolLookupContract`] has already guarded the lookup.
///
/// ```compile_fail
/// use trust_cg_codegen::jit::{JitCompiler, JitConfig};
/// use std::collections::HashMap;
///
/// let jit = JitCompiler::new(JitConfig::default());
/// let ext: HashMap<String, *const u8> = HashMap::new();
/// let buf = jit.compile_raw(&[], &ext).unwrap();
/// let ptr = buf.get_fn_ptr_bound("foo");
/// drop(buf);
/// let _ = ptr;
/// ```
#[derive(Copy, Clone)]
pub struct JitPtr<'a> {
    ptr: *const u8,
    _marker: PhantomData<&'a ExecutableBuffer>,
}

impl<'a> JitPtr<'a> {
    pub fn as_ptr(self) -> *const u8 {
        self.ptr
    }
}

/// Per-basic-block `{count, total_cycles}` cell used by
/// [`ProfileHookMode::BlockCountsAndTiming`] (#364 Phase 3).
///
/// The AArch64 timing trampoline emits LDR/ADD/STR against the `count`
/// field at offset 0 and against the `total_cycles` field at offset 8, so
/// the layout is `#[repr(C)]`-pinned and must NOT be reordered. Both
/// fields are accessed with relaxed atomics from the trampoline, matching
/// the Rust-side `Ordering::Relaxed` used by the reader accessors.
///
/// # Lifetime invariant (#494)
///
/// Each `BlockTimingCell` is allocated as `Box<BlockTimingCell>` and
/// stored in [`ExecutableBuffer::timing_cells`]. The AArch64 timing
/// trampoline bakes the cell's `Box`-pinned heap address into its
/// literal pool, so the cell **must outlive the executable mapping**
/// it is referenced from. This is guaranteed structurally: `Drop` for
/// [`ExecutableBuffer`] unmaps `memory` before Rust drops the owning
/// `HashMap` (field declaration order). See the module-level
/// "Profile counter & timing-cell lifetime" section for the full
/// contract. Related: #478 (per-function counter path),
/// #364 (block-level extension), #494 (this lifetime documentation).
#[repr(C)]
pub(crate) struct BlockTimingCell {
    /// Block entry count. Incremented on every entry by the trampoline.
    /// Equivalent to the single counter used by
    /// [`ProfileHookMode::BlockCounts`].
    pub(crate) count: AtomicU64,
    /// Accumulated cycles spent in this block, measured as the sum of
    /// `(next_block_entry_ts - this_block_entry_ts)` deltas attributed
    /// back to this cell by subsequent block-entry trampolines. See
    /// [`TimingState`] for the attribution machinery.
    pub(crate) total_cycles: AtomicU64,
}

/// Shared cross-block attribution state for
/// [`ProfileHookMode::BlockCountsAndTiming`] (#364 Phase 3).
///
/// One instance per [`ExecutableBuffer`]. On each block entry the
/// trampoline:
/// 1. Reads `prev_ts`. If zero (first block ever entered under this
///    buffer), the attribution step is skipped.
/// 2. Otherwise computes `delta = now - prev_ts` and accumulates it into
///    the [`BlockTimingCell::total_cycles`] field pointed to by
///    `prev_accum_ptr`.
/// 3. Writes `prev_ts = now` and `prev_accum_ptr = &cell.total_cycles`
///    for the current block.
///
/// The layout is `#[repr(C)]` because the trampoline accesses `prev_ts`
/// at offset 0 and `prev_accum_ptr` at offset 8 via fixed LDR/STR
/// immediates.
///
/// **Concurrency limitation (documented, intentional for Phase 3):** the
/// state is a single buffer-wide pair, accessed with relaxed atomics. On
/// a single thread this gives the intended per-block total cycle
/// attribution. With multiple threads calling into the same buffer
/// concurrently, the attribution races — a thread's block may be charged
/// for another thread's cycles. The `count` field is still correct; only
/// `total_cycles` is racy. A per-thread `TimingState` is a straightforward
/// follow-up (pthread_self keying or TLS slot), filed as a gap in the
/// issue comment for #364 Phase 3.
///
/// # Lifetime invariant (#494)
///
/// The `TimingState` is allocated as `Box<TimingState>` once per buffer
/// and stored in [`ExecutableBuffer::timing_state`]. Every timing
/// trampoline in the buffer bakes its heap address into its literal
/// pool, so the `TimingState` **must outlive the executable mapping**.
/// The guarantee is structural, not convention: `Drop` for
/// [`ExecutableBuffer`] unmaps `memory` before Rust drops
/// `timing_state`, so the trampolines cannot execute against a freed
/// allocation. See the module-level "Profile counter & timing-cell
/// lifetime" section for the full contract. Related: #364, #494.
#[repr(C)]
pub(crate) struct TimingState {
    /// Timestamp (`CNTVCT_EL0`) captured at the last block entry, or 0
    /// if no block has been entered yet under this buffer.
    pub(crate) prev_ts: AtomicU64,
    /// Raw pointer to the `total_cycles` field of the
    /// [`BlockTimingCell`] for the previously-entered block, or 0 if
    /// none. Stored as `u64` so the trampoline can load it directly with
    /// an `LDR`. Cast back to `*mut AtomicU64` only inside the buffer
    /// while the mapping is alive.
    pub(crate) prev_accum_ptr: AtomicU64,
}

/// Executable memory buffer containing compiled native functions.
///
/// The generated code remains valid only while this buffer is alive. Prefer
/// [`Self::get_fn_bound`] and [`Self::get_fn_ptr_bound`], which tie returned
/// handles to `&self` so they cannot outlive the mapping. The legacy
/// [`Self::get_fn`] and [`Self::get_fn_ptr`] APIs return raw values with no
/// lifetime tracking, so callers must keep the buffer alive for the full
/// duration of any outstanding function pointer or code pointer.
///
/// The raw lookup family is intentionally low-level. Product callers that
/// install or invoke `ay`/`ty` native artifacts must use
/// [`crate::compile_service::InstalledArtifact::get_contract_symbol_bound`]
/// so the manifest is bound to compiler-derived signatures and the live
/// installed payload before native execution. A bare buffer has no public
/// product typed-lookup surface.
///
/// ```compile_fail
/// use trust_cg_codegen::jit::ExecutableBuffer;
/// use trust_cg_codegen::jit_contract::{ArtifactManifestV1, SymbolLookupContract};
///
/// fn bypass_uninstalled_buffer<'a>(
///     buffer: &'a ExecutableBuffer,
///     manifest: &'a ArtifactManifestV1,
///     contract: &SymbolLookupContract,
/// ) {
///     // Product contract lookup is intentionally not public on a bare buffer.
///     let _ = buffer.get_contract_symbol_bound::<extern "C" fn()>(manifest, contract);
/// }
/// ```
///
/// # Field drop order (profile counter lifetime — #494)
///
/// `memory` is declared first, so it is unmapped (via `Drop for
/// ExecutableBuffer`, which calls `munmap`) strictly before any of the
/// heap-allocated counter / timing-cell / timing-state fields are
/// dropped. The AArch64 profile trampolines bake the counters'
/// `Box`-pinned addresses into the code buffer's literal pool, so the
/// trampolines cannot execute against a freed counter after `munmap`:
/// the text page containing the literal is gone first. Reordering these
/// fields WOULD INTRODUCE A USE-AFTER-FREE WINDOW during buffer
/// teardown — do not reorder.
///
/// See the module-level "Profile counter & timing-cell lifetime"
/// section for the full contract. Related: #478, #364, #494.
#[repr(C)]
pub struct ExecutableBuffer {
    // NOTE (#494): `memory` MUST remain the first field so `Drop` unmaps
    // it before the counter / timing boxes are dropped. See the struct-
    // level doc comment above for the full ordering argument.
    memory: *mut u8,
    len: usize,
    // Redundant construction-time allocation extent for #734. Full-release
    // downstream LTO observed `len == 0` after `compile_raw` even though the
    // mmap and code copy used a nonzero extent. Keep a private duplicate plus
    // a pointer/code/extent cookie so publication and Drop can recover only
    // when the duplicate still proves the original mapping layout.
    len_shadow: usize,
    allocation_cookie: usize,
    code_len: usize,
    published_len: usize,
    /// SHA-256 (lowercase hex) of the full published image — the exact
    /// `published_len` bytes written into the mapping and re-verified by the
    /// JIT-7 publish check before this buffer could be constructed. This is
    /// the bytes-hash that certificate caches (JIT-6) bind against. Empty
    /// only for test-fabricated buffers that never went through a publish
    /// sequence; [`Self::verify_published_code_integrity`] fails closed on
    /// an empty hash.
    published_image_sha256: String,
    publication: JitPublicationContract,
    windows_unwind: WindowsJitUnwindRegistration,
    function_ranges: Vec<(String, std::ops::Range<u64>)>,
    /// Symbol → offset lookup table. Contains both canonical function names
    /// (as supplied by the caller) and Mach-O-style `_name` aliases pointing
    /// to the same offset. This map is a lookup convenience for
    /// `get_fn_ptr` / `get_fn_bound`; it is NOT the canonical symbol list.
    /// Use `canonical_symbols` (via `symbols()` / `symbol_count()`) for the
    /// authoritative, de-duplicated symbol view (fix #360).
    symbol_offsets: HashMap<String, u64>,
    /// Canonical, user-provided function names in insertion order. One entry
    /// per compiled function. Distinct from `symbol_offsets` which also holds
    /// underscore-prefixed aliases.
    canonical_symbols: Vec<String>,
    /// Per-function profiling counters keyed by canonical name.
    ///
    /// Under [`ProfileHookMode::BlockCounts`] / `BlockCountsAndTiming` this
    /// map ALSO carries per-block counters keyed as
    /// `"{func_name}::block{block_id.0}"` (issue #364). Reader accessors
    /// [`Self::get_profile`] / [`Self::entry_count`] fall back to the
    /// entry-block alias when the per-function key is absent.
    ///
    /// # Lifetime invariant (#478, #494)
    ///
    /// The code buffer bakes raw `*const AtomicU64` pointers — the
    /// `Box`-pinned heap addresses returned by
    /// `Box::as_ref() as *const AtomicU64` — into any emitted entry /
    /// block trampolines. The buffer owns the `Box` allocations for the
    /// full lifetime of the executable mapping: `Drop` for
    /// [`ExecutableBuffer`] unmaps `memory` before Rust drops this map
    /// (declared after `memory`), so the trampolines cannot execute
    /// against a freed counter. See the module-level "Profile counter
    /// & timing-cell lifetime" section for the full contract.
    counters: HashMap<String, Box<AtomicU64>>,
    /// Per-basic-block `{count, total_cycles}` cells keyed as
    /// `"{func_name}::block{block_id.0}"`. Populated only when the buffer
    /// was compiled with [`ProfileHookMode::BlockCountsAndTiming`]
    /// (#364 Phase 3). The AArch64 timing trampoline bakes a raw pointer
    /// to each cell into the code buffer.
    ///
    /// # Lifetime invariant (#494)
    ///
    /// These allocations MUST outlive the executable mapping — which they
    /// do, since the `ExecutableBuffer` owns both and `memory` is dropped
    /// first by `Drop for ExecutableBuffer` (field declaration order). See
    /// the module-level "Profile counter & timing-cell lifetime" section
    /// for the full contract.
    timing_cells: HashMap<String, Box<BlockTimingCell>>,
    /// Buffer-wide cross-block timing attribution state. `Some` iff the
    /// buffer was compiled with [`ProfileHookMode::BlockCountsAndTiming`].
    /// The single allocation is addressed by every timing trampoline in
    /// the buffer, so lifetime-tying it to the buffer is mandatory — see
    /// [`TimingState`] for the invariant it maintains.
    ///
    /// # Lifetime invariant (#494)
    ///
    /// The trampolines bake `&*timing_state` as a raw pointer into their
    /// literal pools. The allocation MUST outlive the executable mapping.
    /// This is guaranteed structurally: `Drop for ExecutableBuffer`
    /// unmaps `memory` before Rust drops this field (declared after
    /// `memory`). See the module-level "Profile counter & timing-cell
    /// lifetime" section for the full contract.
    ///
    /// `dead_code` is allowed because the field's purpose is purely
    /// ownership: the live reference to this allocation is the raw `u64`
    /// pointer baked into every timing trampoline's literal pool at
    /// `compile_raw_inner` time. Rust cannot see that use, and adding a
    /// token reader would misrepresent the invariant (`TimingState` is
    /// mutated only by emitted machine code, never by Rust code).
    #[allow(dead_code)]
    timing_state: Option<Box<TimingState>>,
    /// Per-function proof certificates (issue #348).
    ///
    /// Populated when `JitConfig::verify` is true at compile time. Callers
    /// such as ty can query a specific function via
    /// [`ExecutableBuffer::certificate`], iterate all attached certificates
    /// via [`ExecutableBuffer::certificates`], or check the verify-all-
    /// functions invariant via [`ExecutableBuffer::all_verified`].
    ///
    /// When verification is disabled (runtime flag cleared or `verify`
    /// feature off), this map stays empty.
    certificates: HashMap<String, crate::jit_cert::JitCertificate>,
    /// Proof-optimization certificate citations emitted while preparing this
    /// executable buffer.
    proof_optimization_certificates: Vec<crate::pipeline::ProofOptimizationCertificateCitation>,
}

fn executable_buffer_allocation_cookie(
    memory: *mut u8,
    allocation_len: usize,
    code_len: usize,
    published_len: usize,
) -> usize {
    let mut x = (memory as usize as u64)
        ^ (allocation_len as u64).rotate_left(17)
        ^ (code_len as u64).rotate_left(29)
        ^ (published_len as u64).rotate_left(41)
        ^ 0x9e37_79b9_7f4a_7c15_u64;
    x ^= x >> 33;
    x = x.wrapping_mul(0xff51_afd7_ed55_8ccd_u64);
    x ^= x >> 33;
    x = x.wrapping_mul(0xc4ce_b9fe_1a85_ec53_u64);
    x ^= x >> 33;
    #[cfg(target_pointer_width = "64")]
    let cookie = x as usize;
    #[cfg(target_pointer_width = "32")]
    let cookie = (x as usize) ^ ((x >> 32) as usize);
    if cookie == 0 { 1 } else { cookie }
}

/*
SAFETY: After construction the mapped code buffer is immutable executable
memory, so transferring or sharing `ExecutableBuffer` itself across threads
does not create data races.

Issue #355 exposed a separate lifetime hazard: the legacy `get_fn_ptr` and
`get_fn` APIs return raw function pointers with no lifetime tie to `&self`.
That means safe-ish code can move those pointers to other threads and drop the
buffer while a call is still outstanding, causing use-after-free when `Drop`
unmaps the executable pages.

The lifetime-bound `get_fn_ptr_bound` / `get_fn_bound` APIs close that gap for
new code by making outstanding pointers borrow the buffer. Callers who use the
legacy raw APIs across threads are responsible for synchronizing buffer
lifetime with all outstanding pointers, for example by keeping the buffer alive
in an `Arc<ExecutableBuffer>` for the full duration of any call and only
dropping it after all threads have returned.
*/
unsafe impl Send for ExecutableBuffer {}
unsafe impl Sync for ExecutableBuffer {}

impl std::fmt::Debug for ExecutableBuffer {
    /// Metadata-only Debug (no code bytes, no raw pointer contents): enough
    /// for test diagnostics and replay logs without dumping executable
    /// memory.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ExecutableBuffer")
            .field("code_len", &self.code_len)
            .field("published_len", &self.published_len)
            .field("allocation_len", &self.len)
            .field("published_image_sha256", &self.published_image_sha256)
            .field("publication", &self.publication)
            .field("symbol_count", &self.canonical_symbols.len())
            .finish_non_exhaustive()
    }
}

impl ExecutableBuffer {
    #[inline(never)]
    fn allocation_len_primary_opaque(&self) -> usize {
        // Volatile read prevents whole-program release LTO from replacing the
        // field load with a stale scalar when the buffer crosses crate
        // boundaries (#734). This is diagnostic/control metadata, not a data
        // race synchronization primitive.
        std::hint::black_box(unsafe { std::ptr::addr_of!(self.len).read_volatile() })
    }

    #[inline(never)]
    fn allocation_len_shadow_opaque(&self) -> usize {
        std::hint::black_box(unsafe { std::ptr::addr_of!(self.len_shadow).read_volatile() })
    }

    #[inline(never)]
    fn allocation_cookie_opaque(&self) -> usize {
        std::hint::black_box(unsafe { std::ptr::addr_of!(self.allocation_cookie).read_volatile() })
    }

    fn allocation_len_from_published_len(&self) -> usize {
        if self.memory.is_null() || self.code_len == 0 || self.published_len == 0 {
            0
        } else {
            sys::page_align(self.published_len)
        }
    }

    fn allocation_len_shape_is_valid(&self, allocation_len: usize) -> bool {
        let derived_allocation_len = self.allocation_len_from_published_len();
        !self.memory.is_null()
            && allocation_len != 0
            && self.code_len != 0
            && self.code_len <= allocation_len
            && self.code_len <= self.published_len
            && self.published_len <= allocation_len
            && allocation_len >= derived_allocation_len
            && allocation_len.is_multiple_of(sys::PAGE_SIZE)
    }

    fn allocation_len_candidate_is_valid(&self, allocation_len: usize, cookie: usize) -> bool {
        self.allocation_len_shape_is_valid(allocation_len)
            && cookie
                == executable_buffer_allocation_cookie(
                    self.memory,
                    allocation_len,
                    self.code_len,
                    self.published_len,
                )
    }

    fn validated_allocation_len_from_parts(
        &self,
        primary: usize,
        shadow: usize,
        cookie: usize,
    ) -> Option<usize> {
        if primary == shadow && self.allocation_len_candidate_is_valid(primary, cookie) {
            return Some(primary);
        }
        if primary == 0 && self.allocation_len_candidate_is_valid(shadow, cookie) {
            return Some(shadow);
        }
        None
    }

    fn allocation_len_opaque(&self) -> usize {
        let primary = self.allocation_len_primary_opaque();
        let shadow = self.allocation_len_shadow_opaque();
        let cookie = self.allocation_cookie_opaque();
        if let Some(allocation_len) =
            self.validated_allocation_len_from_parts(primary, shadow, cookie)
        {
            return allocation_len;
        }

        let derived_allocation_len = self.allocation_len_from_published_len();
        if primary == 0 && derived_allocation_len != 0 {
            return derived_allocation_len;
        }

        if self.allocation_len_shape_is_valid(primary) {
            0
        } else {
            primary
        }
    }

    fn allocation_len_for_unmap(&self) -> usize {
        let primary = self.allocation_len_primary_opaque();
        let shadow = self.allocation_len_shadow_opaque();
        let cookie = self.allocation_cookie_opaque();
        if let Some(allocation_len) =
            self.validated_allocation_len_from_parts(primary, shadow, cookie)
        {
            return allocation_len;
        }
        if primary == 0 {
            return self.allocation_len_from_published_len();
        }
        0
    }

    /// Return the publication state recorded when this buffer was created.
    pub fn publication_contract(&self) -> JitPublicationContract {
        self.publication
    }

    /// SHA-256 (lowercase hex) of the published image, computed from the
    /// compiled artifact and re-verified against the sealed RX mapping by
    /// the always-on JIT-7 publish check. Empty only for test-fabricated
    /// buffers that never went through a publish sequence.
    pub fn published_image_sha256(&self) -> &str {
        &self.published_image_sha256
    }

    /// Re-run the bytes-hash integrity check against the live mapping: hash
    /// the `published_len` bytes currently in the mapping and require them to
    /// equal the publish-time hash. Fails closed (never a warning) on any
    /// mismatch — including a buffer that carries no publish-time hash.
    ///
    /// Callers that are about to hand out an executable pointer long after
    /// publication (e.g. cached-buffer replay, JIT-6 certificate attachment)
    /// can use this to prove the bytes they vouch for are the bytes that
    /// will execute.
    pub fn verify_published_code_integrity(&self) -> Result<(), JitError> {
        if self.memory.is_null() || self.published_len == 0 {
            return Err(JitError::PublishedBytesHashMismatch {
                expected_sha256: self.published_image_sha256.clone(),
                actual_sha256: "<no published mapping>".to_string(),
                published_len: self.published_len,
            });
        }
        // SAFETY: `memory` is the live mapping owned by this buffer and
        // `published_len` bytes were initialized at publication time.
        let live = unsafe { std::slice::from_raw_parts(self.memory, self.published_len) };
        let actual_sha256 = crate::jit_diagnostics::sha256_hex(live);
        if self.published_image_sha256.is_empty() || actual_sha256 != self.published_image_sha256 {
            return Err(JitError::PublishedBytesHashMismatch {
                expected_sha256: self.published_image_sha256.clone(),
                actual_sha256,
                published_len: self.published_len,
            });
        }
        Ok(())
    }

    /// Ensure this thread can execute the published mapping before a callable
    /// pointer escapes lookup.
    pub fn ensure_current_thread_execute_mode(&self) {
        if self.publication.map_jit && self.publication.published_rx {
            ensure_jit_execute_mode();
        }
    }

    /// Reassert that the published buffer is executable for this process and
    /// current thread before invoking a cached raw function pointer.
    pub fn ensure_published_executable(&self) -> Result<(), JitError> {
        self.reassert_published_executable().map(|_| ())
    }

    fn reassert_published_executable(&self) -> Result<(bool, bool), JitError> {
        let buffer_base = self.memory as u64;
        let code_len = u64::try_from(self.code_len).unwrap_or(u64::MAX);
        let allocation_len_usize = self.allocation_len_opaque();
        let allocation_len = u64::try_from(allocation_len_usize).unwrap_or(u64::MAX);
        if self.memory.is_null()
            || allocation_len_usize == 0
            || self.code_len == 0
            || self.code_len > self.published_len
            || self.code_len > allocation_len_usize
            || self.published_len > allocation_len_usize
        {
            return Err(JitError::InvalidExecutableBufferExtent {
                buffer_base,
                code_end: buffer_base.saturating_add(code_len),
                allocation_end: buffer_base.saturating_add(allocation_len),
                code_len: self.code_len,
                allocation_len: allocation_len_usize,
            });
        }

        if !self.publication.published_rx {
            return Err(JitError::UnpublishedExecutableBuffer {
                buffer_base,
                buffer_end: buffer_base.saturating_add(code_len),
                code_len: self.code_len,
                allocation_len: allocation_len_usize,
            });
        }

        unsafe {
            sys::mprotect(self.memory, allocation_len_usize, sys::RX)
                .map_err(JitError::MemoryProtect)?;
        }
        let execute_mode_reasserted = self.publication.map_jit && self.publication.published_rx;
        self.ensure_current_thread_execute_mode();
        Ok((true, execute_mode_reasserted))
    }

    fn checked_code_offset_for_ptr(
        &self,
        ptr: *const u8,
        context: impl Into<String>,
    ) -> Result<u64, JitError> {
        let pointer = ptr as u64;
        let buffer_base = self.memory as u64;
        let code_len = u64::try_from(self.code_len).unwrap_or(u64::MAX);
        let buffer_end = buffer_base.saturating_add(code_len);
        self.code_offset_for_host_pc(pointer)
            .ok_or_else(|| JitError::JitPointerOwnershipMismatch {
                context: context.into(),
                pointer,
                buffer_base,
                buffer_end,
                code_len: self.code_len,
                allocation_len: self.allocation_len_opaque(),
            })
    }

    /// Reassert executable publication for a cached raw pointer after proving
    /// that the pointer belongs to this buffer's initialized code range.
    ///
    /// Downstream runtimes that cache raw function pointers must use this
    /// guard when they still have the owning [`ExecutableBuffer`] available.
    /// A plain buffer-level publish can accidentally publish the wrong owner;
    /// this form fails closed with range diagnostics before the unsafe call.
    pub fn ensure_published_executable_for_ptr(
        &self,
        ptr: *const u8,
        context: impl Into<String>,
    ) -> Result<u64, JitError> {
        let code_offset = self.checked_code_offset_for_ptr(ptr, context)?;
        self.ensure_published_executable()?;
        Ok(code_offset)
    }

    /// Reassert executable publication for a cached raw symbol pointer after
    /// proving the pointer belongs to this buffer and exactly matches the
    /// named symbol's entry offset.
    pub fn ensure_published_symbol_ptr<'a>(
        &'a self,
        symbol: &str,
        ptr: *const u8,
    ) -> Result<JitPtr<'a>, JitError> {
        self.diagnose_published_symbol_ptr(symbol, ptr)?;
        Ok(JitPtr {
            ptr,
            _marker: PhantomData,
        })
    }

    /// Return structured publication evidence for a cached raw symbol pointer.
    ///
    /// This performs the same null, owner, exact-symbol, and executable
    /// publication checks as [`Self::ensure_published_symbol_ptr`], but returns
    /// the buffer and publication state that downstream crash/replay artifacts
    /// can attach before making an unsafe raw call.
    pub fn diagnose_published_symbol_ptr(
        &self,
        symbol: &str,
        ptr: *const u8,
    ) -> Result<JitSymbolPublicationProof, JitError> {
        if ptr.is_null() {
            return Err(JitError::NullFunctionPointer {
                symbol: symbol.to_owned(),
            });
        }
        let expected_offset = *self
            .symbol_offsets
            .get(symbol)
            .ok_or_else(|| JitError::UnresolvedSymbol(symbol.to_owned()))?;
        let actual_offset =
            self.checked_code_offset_for_ptr(ptr, format!("symbol `{symbol}` cached pointer"))?;
        if actual_offset != expected_offset {
            return Err(JitError::FunctionPointerSymbolMismatch {
                symbol: symbol.to_owned(),
                pointer: ptr as u64,
                buffer_base: self.memory as u64,
                actual_offset,
                expected_offset,
            });
        }

        let (mprotect_rx_ok, execute_mode_reasserted) = self.reassert_published_executable()?;
        let first_code_bytes = if (actual_offset as usize) < self.code_len {
            let available = self.code_len - actual_offset as usize;
            let len = available.min(16);
            Some(unsafe {
                std::slice::from_raw_parts(self.memory.add(actual_offset as usize), len).to_vec()
            })
        } else {
            None
        };
        let buffer_base = self.memory as u64;
        let code_len = u64::try_from(self.code_len).unwrap_or(u64::MAX);
        Ok(JitSymbolPublicationProof {
            symbol: symbol.to_owned(),
            pointer: ptr as u64,
            buffer_base,
            buffer_end: buffer_base.saturating_add(code_len),
            code_len: self.code_len,
            published_len: self.published_len,
            allocation_len: self.allocation_len_opaque(),
            expected_symbol_offset: expected_offset,
            actual_ptr_offset: actual_offset,
            exact_symbol_match: true,
            publication_contract: self.publication,
            mprotect_rx_ok,
            execute_mode_reasserted,
            first_code_bytes,
        })
    }

    /// Lifetime-bound version of [`Self::get_fn_ptr`]. The returned
    /// [`JitPtr`] cannot outlive `self`, eliminating the use-after-free
    /// risk when the buffer is dropped while a pointer is held.
    ///
    /// This is still raw lookup. Use it only for low-level wrappers, tests,
    /// fuzzing, or explicitly non-product/profile-only probes. Product
    /// dispatch must use an installed artifact's contract-bound lookup.
    pub fn get_fn_ptr_bound<'a>(&'a self, name: &str) -> Option<JitPtr<'a>> {
        let off = *self.symbol_offsets.get(name)?;
        let off = usize::try_from(off).ok()?;
        if off >= self.code_len {
            return None;
        }
        self.ensure_current_thread_execute_mode();
        Some(JitPtr {
            ptr: unsafe { self.memory.add(off) as *const u8 },
            _marker: PhantomData,
        })
    }

    /// Internal primitive used only after the compile-service installed
    /// artifact has validated its compiler-derived signature and live payload
    /// binding.
    ///
    /// A caller-supplied manifest and signature are not authority on their own,
    /// so this method is deliberately crate-private. The only public product
    /// typed-lookup boundary is
    /// [`crate::compile_service::InstalledArtifact::get_contract_symbol_bound`].
    pub(crate) fn get_contract_symbol_bound<'a, F: Copy>(
        &'a self,
        manifest: &'a ArtifactManifestV1,
        contract: &SymbolLookupContract,
    ) -> Result<TypedSymbol<'a, F>, ArtifactContractError> {
        let ptr = self
            .get_fn_ptr_bound(&contract.symbol)
            .map(JitPtr::as_ptr)
            .unwrap_or(std::ptr::null());
        manifest.typed_symbol(contract, ptr)
    }

    #[deprecated = "use get_fn_ptr_bound for low-level lifetime-bound lookup, or InstalledArtifact::get_contract_symbol_bound for product dispatch"]
    pub fn get_fn_ptr(&self, name: &str) -> Option<*const u8> {
        self.get_fn_ptr_bound(name).map(JitPtr::as_ptr)
    }

    /// Lifetime-bound version of [`Self::get_fn`]. The returned
    /// [`JitFn`] cannot outlive `self`.
    ///
    /// This API checks only the Rust function-pointer size and the buffer
    /// lifetime. It remains a low-level ABI compatibility surface; product
    /// dispatch must use
    /// [`crate::compile_service::InstalledArtifact::get_contract_symbol_bound`]
    /// so compiler-derived signature and installed-payload bindings validate
    /// the callable first.
    ///
    /// # Safety
    /// `F` must match the compiled function's ABI and be pointer-sized.
    pub unsafe fn get_fn_bound<'a, F: Copy>(&'a self, name: &str) -> Option<JitFn<'a, F>> {
        assert_eq!(
            std::mem::size_of::<F>(),
            std::mem::size_of::<*const u8>(),
            "get_fn_bound<F>: F must be pointer-sized (expected {} bytes, got {} bytes)",
            std::mem::size_of::<*const u8>(),
            std::mem::size_of::<F>(),
        );
        self.get_fn_ptr_bound(name).map(|ptr| {
            let raw = ptr.as_ptr();
            // SAFETY: caller asserts `F` is ABI-compatible with the compiled
            // function pointer (documented on `unsafe fn get_fn_bound`), and
            // the above size assertion pins `F` to pointer width.
            JitFn {
                inner: unsafe { std::mem::transmute_copy(&raw) },
                _marker: PhantomData,
            }
        })
    }

    #[deprecated = "use get_fn_bound for low-level lifetime-bound lookup, or InstalledArtifact::get_contract_symbol_bound for product dispatch"]
    /// # Safety
    /// Caller must ensure `F` matches the compiled function's ABI. Product
    /// callers must not use this legacy raw lookup as installable native
    /// dispatch evidence; use an installed artifact's contract-bound lookup
    /// instead.
    ///
    /// # Panics
    /// Panics if `size_of::<F>() != size_of::<*const u8>()` (F must be pointer-sized).
    pub unsafe fn get_fn<F>(&self, name: &str) -> Option<F> {
        assert_eq!(
            std::mem::size_of::<F>(),
            std::mem::size_of::<*const u8>(),
            "get_fn<F>: F must be pointer-sized (expected {} bytes, got {} bytes)",
            std::mem::size_of::<*const u8>(),
            std::mem::size_of::<F>(),
        );
        self.get_fn_ptr_bound(name).map(|ptr| {
            let raw = ptr.as_ptr();
            // SAFETY: caller asserts `F` is ABI-compatible with the compiled
            // function pointer (documented on `unsafe fn get_fn`), and the
            // above size assertion pins `F` to pointer width.
            unsafe { std::mem::transmute_copy(&raw) }
        })
    }

    pub fn allocated_size(&self) -> usize {
        self.allocation_len_opaque()
    }

    /// Borrow the raw executable code prefix of this buffer.
    ///
    /// The slice covers exactly `code_len` bytes starting at the mapped base
    /// address; any target metadata appended after the code (e.g. Windows
    /// unwind tables) is intentionally omitted so the bytes correspond to
    /// what the encoder produced. The returned reference borrows the buffer
    /// and must not outlive it.
    ///
    /// This accessor exists for callers that need to persist the JIT'd code
    /// to disk and replay it via [`publish_serialized_buffer`]; it is the
    /// public counterpart of the internal `code_bytes` helper.
    pub fn code_slice(&self) -> &[u8] {
        self.code_bytes()
    }

    /// Number of bytes of executable code copied into the mapped buffer.
    ///
    /// Equivalent to `self.code_slice().len()`.
    pub fn code_len(&self) -> usize {
        self.code_len
    }

    /// Borrow the full symbol-offset table, including any underscore-prefixed
    /// Mach-O aliases. The map's values are byte offsets from the buffer
    /// base. Use [`Self::symbols`] for the canonical, alias-free view.
    pub fn symbol_offsets(&self) -> &HashMap<String, u64> {
        &self.symbol_offsets
    }

    /// Borrow the canonical function name list in insertion order.
    pub fn canonical_symbols(&self) -> &[String] {
        &self.canonical_symbols
    }

    /// Borrow the per-function `(name, code_byte_range)` ranges captured at
    /// JIT layout time.
    pub fn function_ranges(&self) -> &[(String, std::ops::Range<u64>)] {
        &self.function_ranges
    }

    /// Attach proof-optimization certificate citations captured by the
    /// codegen preparation pipeline.
    pub fn attach_proof_optimization_certificates(
        &mut self,
        certificates: Vec<crate::pipeline::ProofOptimizationCertificateCitation>,
    ) {
        self.proof_optimization_certificates = certificates;
    }

    /// Proof-optimization certificate citations attached to this buffer.
    pub fn proof_optimization_certificates(
        &self,
    ) -> &[crate::pipeline::ProofOptimizationCertificateCitation] {
        &self.proof_optimization_certificates
    }

    /// Return replay metadata for this executable buffer using the exact
    /// compiled code length and function byte ranges captured at JIT layout
    /// time.
    pub fn replay_report_metadata(&self) -> crate::jit_diagnostics::JitReplayReportMetadata {
        use crate::jit_diagnostics::{
            JitCodeRange, JitPcMapEntry, JitReplayReportMetadata, JitSymbolLabel, sha256_hex,
        };

        let mut report = JitReplayReportMetadata::new(self.code_len as u64);
        report.entry_symbol = self.canonical_symbols.first().cloned();
        let native_payload_sha256 = format!("sha256:{}", sha256_hex(self.code_bytes()));
        let live_identity_bytes = self.live_replay_identity_bytes();
        let live_identity_sha256 = format!("sha256:{}", sha256_hex(&live_identity_bytes));
        report.artifact_id = Some(format!("trust-cg-jit-live:{live_identity_sha256}"));
        report
            .properties
            .insert("native_payload_sha256".to_string(), native_payload_sha256);
        report.properties.insert(
            "artifact_manifest_checksum".to_string(),
            crate::jit_contract::ArtifactChecksum::for_bytes(&live_identity_bytes).to_string(),
        );
        report
            .properties
            .insert("source_fingerprint".to_string(), live_identity_sha256);
        report.properties.insert(
            "source_identity_kind".to_string(),
            "jit_live_symbol_layout".to_string(),
        );
        report.proof_optimization_certificates = self.proof_optimization_certificates.clone();

        for (name, range) in &self.function_ranges {
            let generated_alias = format!("_{}", name);
            let aliases = if self.symbol_offsets.get(generated_alias.as_str()) == Some(&range.start)
            {
                vec![generated_alias]
            } else {
                Vec::new()
            };

            report
                .pc_map
                .push(JitPcMapEntry::new(range.start, name.clone(), 0));
            report.symbols.push(
                JitSymbolLabel::new(name.clone(), JitCodeRange::new(range.start, range.end))
                    .with_aliases(aliases),
            );
        }

        report
    }

    /// Build an issue-ready crash packet from this live executable buffer's
    /// replay metadata.
    pub fn crash_report_metadata(
        &self,
        kind: crate::jit_diagnostics::JitCrashKind,
        stage: impl Into<String>,
        host_pc: Option<u64>,
        code_offset: Option<u64>,
    ) -> crate::jit_diagnostics::JitCrashReportMetadata {
        use crate::jit_diagnostics::{JitCrashLocation, JitTrapStatusBlock};

        let stage = stage.into();
        let mut replay = self.replay_report_metadata();
        let location = JitCrashLocation::resolve(&replay, host_pc, code_offset);
        let mut status = JitTrapStatusBlock::new(0, kind.status_kind(), stage.clone());
        if let Some(pc_offset) = code_offset {
            status = status.with_pc_offset(pc_offset);
        }
        if let Some(symbol) = location.symbol.as_deref() {
            status = status.with_symbol(symbol);
        }
        replay.statuses.push(status);

        crate::jit_diagnostics::JitCrashReportMetadata::new(kind, "jit-runtime", stage, replay)
            .with_location(host_pc, code_offset)
    }

    /// Resolve a native program counter into this executable buffer's code
    /// offset when the PC points inside the live mapping.
    pub fn code_offset_for_host_pc(&self, host_pc: u64) -> Option<u64> {
        let base = self.memory as u64;
        let code_len = u64::try_from(self.code_len).ok()?;
        let end = base.checked_add(code_len)?;
        if (base..end).contains(&host_pc) {
            Some(host_pc - base)
        } else {
            None
        }
    }

    fn code_bytes(&self) -> &[u8] {
        // SAFETY: `memory` points to a live RX mapping owned by this buffer,
        // and `code_len` is the executable-code prefix copied into that
        // mapping. Target metadata appended after it is intentionally omitted.
        unsafe { std::slice::from_raw_parts(self.memory as *const u8, self.code_len) }
    }

    fn live_replay_identity_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(b"trust-cg.codegen.jit.live_replay_identity.v1\0");
        bytes.extend_from_slice(&(self.code_len as u64).to_le_bytes());
        bytes.extend_from_slice(self.code_bytes());

        let mut ranges = self.function_ranges.clone();
        ranges.sort_by(|left, right| {
            (left.1.start, left.1.end, left.0.as_str()).cmp(&(
                right.1.start,
                right.1.end,
                right.0.as_str(),
            ))
        });
        bytes.extend_from_slice(&(ranges.len() as u64).to_le_bytes());
        for (name, range) in ranges {
            bytes.extend_from_slice(&(name.len() as u64).to_le_bytes());
            bytes.extend_from_slice(name.as_bytes());
            bytes.extend_from_slice(&range.start.to_le_bytes());
            bytes.extend_from_slice(&range.end.to_le_bytes());
        }

        bytes.extend_from_slice(&(self.canonical_symbols.len() as u64).to_le_bytes());
        for name in &self.canonical_symbols {
            bytes.extend_from_slice(&(name.len() as u64).to_le_bytes());
            bytes.extend_from_slice(name.as_bytes());
        }

        bytes
    }

    /// Number of distinct functions compiled into this buffer.
    ///
    /// Fix #360: previously computed as `symbol_offsets.len() / 2`, which
    /// relied on the fragile invariant that every canonical name had exactly
    /// one `_`-prefixed alias. That assumption broke for user names already
    /// starting with `_` and for any external mutation of `symbol_offsets`.
    /// Now returns the exact length of the canonical symbol list, which is
    /// populated once per compiled function.
    pub fn symbol_count(&self) -> usize {
        self.canonical_symbols.len()
    }

    /// Iterate canonical function names paired with their offset in the code
    /// buffer. Yields each compiled function exactly once, using the
    /// user-provided name (never the Mach-O `_`-prefixed alias).
    ///
    /// Fix #360: previous implementation filtered `symbol_offsets` by
    /// `!starts_with('_')`, which silently hid functions whose canonical
    /// name already began with `_`. Iterating the canonical list is both
    /// correct and O(n) without a hash probe per item.
    pub fn symbols(&self) -> impl Iterator<Item = (&str, u64)> {
        self.canonical_symbols.iter().map(move |name| {
            // Safety: every canonical name is inserted into `symbol_offsets`
            // at construction time. If this unwrap ever fires we have a
            // construction-time bug, not a user-input bug.
            let off = *self
                .symbol_offsets
                .get(name.as_str())
                .expect("canonical symbol missing from symbol_offsets");
            (name.as_str(), off)
        })
    }

    pub fn get_profile(&self, name: &str) -> Option<ProfileStats> {
        // #364 read-side alias: when BlockCounts (or BlockCountsAndTiming)
        // is enabled the per-function entry counter is NOT stored under
        // `name`; instead the entry block counter under `{name}::block0`
        // serves both purposes. Fall back to that alias so the stable
        // `get_profile(name)` API keeps working regardless of which
        // profile mode compiled the function.
        if let Some(counter) = self.counters.get(name) {
            return Some(ProfileStats {
                call_count: counter.load(Ordering::Relaxed),
            });
        }
        let alias = format!("{}::block0", name);
        if let Some(counter) = self.counters.get(&alias) {
            return Some(ProfileStats {
                call_count: counter.load(Ordering::Relaxed),
            });
        }
        // Phase 3 (BlockCountsAndTiming): the entry counter lives inside
        // the TimingCell, not the `counters` map.
        self.timing_cells.get(&alias).map(|cell| ProfileStats {
            call_count: cell.count.load(Ordering::Relaxed),
        })
    }

    /// Returns the function-entry counter for `name`, or `None` if `name`
    /// was not compiled with entry counters enabled.
    ///
    /// Equivalent to `self.get_profile(name).map(|s| s.call_count)`; provided
    /// as the stable public API per issue #478.
    pub fn entry_count(&self, name: &str) -> Option<u64> {
        self.get_profile(name).map(|stats| stats.call_count)
    }

    /// Snapshot function-entry JIT counters into a `.profdata` document.
    ///
    /// This is the lightweight runtime dump surface for call-count canaries:
    /// callers compile with [`ProfileHookMode::CallCounts`], execute a
    /// bounded input window, then persist the captured counts with the full
    /// PGO profile key for the compile request. `ProfileHookMode::BlockCounts`
    /// callers should prefer [`Self::block_profdata_with_key`] so the profile
    /// keeps all block-level hotness, not just entry counts.
    ///
    /// Each function-entry counter is mirrored into block id 0 so existing
    /// profile-use hotness consumers can classify the entry block without a
    /// separate schema path. Functions compiled without direct entry counters
    /// are omitted.
    pub fn entry_profdata_with_key(
        &self,
        profile_key: &trust_cg_opt::CacheKey,
    ) -> trust_cg_opt::pgo::ProfData {
        let mut profile = trust_cg_opt::pgo::ProfData::new_with_key(profile_key);

        for name in &self.canonical_symbols {
            let Some(counter) = self.counters.get(name) else {
                continue;
            };
            let count = counter.load(Ordering::Relaxed);

            let mut function = trust_cg_opt::pgo::FunctionProfile::new(name.as_str());
            function.call_count = count;
            function.blocks = vec![trust_cg_opt::pgo::BlockProfile::new(0, count)];
            profile.functions.push(function);
        }

        profile
    }

    /// Snapshot function-entry JIT counters using a legacy module-hash-only
    /// default key. New profile-generate callers should use
    /// [`Self::entry_profdata_with_key`].
    pub fn entry_profdata(&self, module_hash: u128) -> trust_cg_opt::pgo::ProfData {
        let profile_key =
            trust_cg_opt::CacheKey::new(module_hash, 0, String::new(), String::new(), Vec::new());
        self.entry_profdata_with_key(&profile_key)
    }

    /// Write [`Self::entry_profdata`] to `path` and return the captured
    /// profile document.
    pub fn write_entry_profdata(
        &self,
        module_hash: u128,
        path: &std::path::Path,
    ) -> Result<trust_cg_opt::pgo::ProfData, trust_cg_opt::pgo::ProfDataError> {
        let profile = self.entry_profdata(module_hash);
        trust_cg_opt::pgo::write_to_path(&profile, path)?;
        Ok(profile)
    }

    /// Write [`Self::entry_profdata_with_key`] to `path` and return the
    /// captured profile document.
    pub fn write_entry_profdata_with_key(
        &self,
        profile_key: &trust_cg_opt::CacheKey,
        path: &std::path::Path,
    ) -> Result<trust_cg_opt::pgo::ProfData, trust_cg_opt::pgo::ProfDataError> {
        let profile = self.entry_profdata_with_key(profile_key);
        trust_cg_opt::pgo::write_to_path(&profile, path)?;
        Ok(profile)
    }

    /// Returns the per-basic-block counter value for the given function and
    /// block id, or `None` if `name` was not compiled with
    /// [`ProfileHookMode::BlockCounts`] / [`ProfileHookMode::BlockCountsAndTiming`]
    /// or `block_id` is not a valid block of that function.
    ///
    /// The key format (`"{name}::block{block_id.0}"`) is the stable public
    /// API introduced for issue #364. Prover harnesses and ty callers
    /// should use this accessor rather than reaching into `counters`-style
    /// internals.
    ///
    /// Under [`ProfileHookMode::BlockCountsAndTiming`] the same count value
    /// is available; this accessor looks in both the plain-counter and the
    /// timing-cell tables so the read-side API is uniform across modes.
    pub fn block_count(&self, name: &str, block_id: trust_cg_ir::types::BlockId) -> Option<u64> {
        let key = format!("{}::block{}", name, block_id.0);
        if let Some(counter) = self.counters.get(&key) {
            return Some(counter.load(Ordering::Relaxed));
        }
        self.timing_cells
            .get(&key)
            .map(|cell| cell.count.load(Ordering::Relaxed))
    }

    /// Iterate `(block_id_value, count)` pairs for every block-level counter
    /// registered under `name`. Yields nothing if `name` was not compiled
    /// with [`ProfileHookMode::BlockCounts`] or
    /// [`ProfileHookMode::BlockCountsAndTiming`].
    ///
    /// Returned in an unspecified order. Callers that need deterministic
    /// ordering should collect + sort by the first tuple element.
    pub fn block_counts(&self, name: &str) -> Vec<(u32, u64)> {
        let prefix = format!("{}::block", name);
        let from_counters = self.counters.iter().filter_map(|(key, counter)| {
            let rest = key.strip_prefix(&prefix)?;
            let bid: u32 = rest.parse().ok()?;
            Some((bid, counter.load(Ordering::Relaxed)))
        });
        let from_timing = self.timing_cells.iter().filter_map(|(key, cell)| {
            let rest = key.strip_prefix(&prefix)?;
            let bid: u32 = rest.parse().ok()?;
            Some((bid, cell.count.load(Ordering::Relaxed)))
        });
        from_counters.chain(from_timing).collect()
    }

    /// Snapshot all JIT block counters into a `.profdata` document.
    ///
    /// This is the runtime dump surface for JIT canary runs: callers compile
    /// with [`ProfileHookMode::BlockCounts`] or
    /// [`ProfileHookMode::BlockCountsAndTiming`], execute representative
    /// inputs, then call this method with the full PGO profile key for the
    /// compile request. Consumers such as ty can write the result and feed
    /// it back to `trust-cg --profile-use` for a profile-generate/profile-use
    /// round trip.
    ///
    /// Functions compiled without block counters are omitted.
    pub fn block_profdata_with_key(
        &self,
        profile_key: &trust_cg_opt::CacheKey,
    ) -> trust_cg_opt::pgo::ProfData {
        let mut profile = trust_cg_opt::pgo::ProfData::new_with_key(profile_key);

        for name in &self.canonical_symbols {
            let mut counts = self.block_counts(name);
            if counts.is_empty() {
                continue;
            }

            counts.sort_by_key(|(block_id, _)| *block_id);

            let mut function = trust_cg_opt::pgo::FunctionProfile::new(name.as_str());
            function.blocks = counts
                .into_iter()
                .map(|(block_id, hits)| trust_cg_opt::pgo::BlockProfile::new(block_id, hits))
                .collect();
            function.call_count = function.block_hits(0);
            profile.functions.push(function);
        }

        profile
    }

    /// Snapshot all JIT block counters using a legacy module-hash-only
    /// default key. New profile-generate callers should use
    /// [`Self::block_profdata_with_key`].
    pub fn block_profdata(&self, module_hash: u128) -> trust_cg_opt::pgo::ProfData {
        let profile_key =
            trust_cg_opt::CacheKey::new(module_hash, 0, String::new(), String::new(), Vec::new());
        self.block_profdata_with_key(&profile_key)
    }

    /// Write [`Self::block_profdata`] to `path` and return the captured
    /// profile document.
    pub fn write_block_profdata(
        &self,
        module_hash: u128,
        path: &std::path::Path,
    ) -> Result<trust_cg_opt::pgo::ProfData, trust_cg_opt::pgo::ProfDataError> {
        let profile = self.block_profdata(module_hash);
        trust_cg_opt::pgo::write_to_path(&profile, path)?;
        Ok(profile)
    }

    /// Write [`Self::block_profdata_with_key`] to `path` and return the
    /// captured profile document.
    pub fn write_block_profdata_with_key(
        &self,
        profile_key: &trust_cg_opt::CacheKey,
        path: &std::path::Path,
    ) -> Result<trust_cg_opt::pgo::ProfData, trust_cg_opt::pgo::ProfDataError> {
        let profile = self.block_profdata_with_key(profile_key);
        trust_cg_opt::pgo::write_to_path(&profile, path)?;
        Ok(profile)
    }

    /// Returns `(count, total_cycles)` for the given function's basic
    /// block, or `None` if `name` was not compiled with
    /// [`ProfileHookMode::BlockCountsAndTiming`] (#364 Phase 3) or
    /// `block_id` is not a valid block of that function.
    ///
    /// `total_cycles` is the accumulated `CNTVCT_EL0` delta between this
    /// block's entry and the next block's entry (on any thread, since the
    /// attribution state is buffer-wide). See [`TimingState`] for the
    /// attribution semantics. The first block entered under a buffer
    /// contributes 0 cycles because there is no preceding entry to
    /// attribute from.
    pub fn block_timing(
        &self,
        name: &str,
        block_id: trust_cg_ir::types::BlockId,
    ) -> Option<(u64, u64)> {
        let key = format!("{}::block{}", name, block_id.0);
        self.timing_cells.get(&key).map(|cell| {
            (
                cell.count.load(Ordering::Relaxed),
                cell.total_cycles.load(Ordering::Relaxed),
            )
        })
    }

    /// Iterate `(block_id_value, count, total_cycles)` tuples for every
    /// timing cell registered under `name`. Yields nothing if `name` was
    /// not compiled with [`ProfileHookMode::BlockCountsAndTiming`].
    ///
    /// Returned in an unspecified order. Callers that need deterministic
    /// ordering should collect + sort by the first tuple element.
    pub fn block_timings(&self, name: &str) -> Vec<(u32, u64, u64)> {
        let prefix = format!("{}::block", name);
        self.timing_cells
            .iter()
            .filter_map(|(key, cell)| {
                let rest = key.strip_prefix(&prefix)?;
                let bid: u32 = rest.parse().ok()?;
                Some((
                    bid,
                    cell.count.load(Ordering::Relaxed),
                    cell.total_cycles.load(Ordering::Relaxed),
                ))
            })
            .collect()
    }

    /// Reset the call counter for `name` to 0. Returns `true` if `name` was a
    /// profiled function (counter existed), `false` otherwise. Callers that
    /// need the pre-reset count should call `get_profile` first — the reset
    /// itself is destructive and does not return the old value.
    ///
    /// Uses `Ordering::Relaxed` to match the trampoline increment side. Safe
    /// to call while the function is executing on other threads; the observed
    /// counter on those threads may miss increments that happen across the
    /// reset boundary, which is the documented relaxed-atomic behaviour.
    pub fn reset_profile(&self, name: &str) -> bool {
        if let Some(counter) = self.counters.get(name) {
            counter.store(0, Ordering::Relaxed);
            true
        } else {
            false
        }
    }

    /// Reset the entry counter for `name` to zero. Returns `true` iff `name`
    /// had a counter. Equivalent to [`Self::reset_profile`] and kept separate
    /// so the #478 public API is self-contained.
    pub fn reset_entry_count(&self, name: &str) -> bool {
        self.reset_profile(name)
    }

    /// Reset every profiled function's counter to 0. Returns the number of
    /// counters that were reset.
    pub fn reset_all_profiles(&self) -> usize {
        for counter in self.counters.values() {
            counter.store(0, Ordering::Relaxed);
        }
        self.counters.len()
    }

    pub fn profiles(&self) -> impl Iterator<Item = (&str, ProfileStats)> + '_ {
        self.counters.iter().map(|(name, counter)| {
            (
                name.as_str(),
                ProfileStats {
                    call_count: counter.load(Ordering::Relaxed),
                },
            )
        })
    }

    /// Snapshot every `(name, count)` pair. Produces an owned `Vec` so callers
    /// can drop the buffer's borrow between samples.
    pub fn entry_counts(&self) -> Vec<(String, u64)> {
        self.canonical_symbols
            .iter()
            .filter_map(|name| {
                self.counters
                    .get(name)
                    .map(|counter| (name.clone(), counter.load(Ordering::Relaxed)))
            })
            .collect()
    }

    // --- Proof certificates (issue #348) -------------------------------------

    /// Return the proof certificate for the named function, if one was
    /// generated. A certificate is generated only when
    /// [`crate::jit::JitConfig::verify`] was true at compile time and the
    /// `verify` feature is enabled in the build.
    ///
    /// Callers such as ty use this to assert that a JIT'd function has
    /// been formally checked against its trust_ir input. Example:
    ///
    /// ```no_run
    /// # use trust_cg_codegen::jit::{JitCompiler, JitConfig};
    /// # use std::collections::HashMap;
    /// let jit = JitCompiler::new(JitConfig { verify: true, ..Default::default() });
    /// # let functions = vec![];
    /// let buf = jit.compile_raw(&functions, &HashMap::new()).unwrap();
    /// if let Some(cert) = buf.certificate("add") {
    ///     assert!(cert.is_verified());
    ///     assert!(cert.replay_check());
    /// }
    /// ```
    pub fn certificate(&self, name: &str) -> Option<&crate::jit_cert::JitCertificate> {
        self.certificates.get(name)
    }

    /// Iterate over every `(function_name, certificate)` pair attached to
    /// this buffer. Empty when verification was disabled.
    pub fn certificates(&self) -> impl Iterator<Item = (&str, &crate::jit_cert::JitCertificate)> {
        self.certificates.iter().map(|(k, v)| (k.as_str(), v))
    }

    /// Returns true iff every attached certificate reports
    /// [`crate::jit_cert::JitCertificate::is_verified`]. Returns `true`
    /// vacuously when there are no certificates (e.g. verification off).
    pub fn all_verified(&self) -> bool {
        self.certificates.values().all(|c| c.is_verified())
    }

    /// Export every attached certificate as a single JSON object mapping
    /// function name → certificate JSON. Intended for cross-system proof
    /// composition (see `designs/2026-04-16-proof-certificate-chain.md`).
    pub fn export_proofs(&self) -> String {
        let mut out = String::from("{\n  \"functions\": {");
        for (i, (name, cert)) in self.certificates.iter().enumerate() {
            if i > 0 {
                out.push(',');
            }
            out.push_str(&format!(
                "\n    \"{}\": ",
                crate::jit_cert::escape_for_export(name)
            ));
            out.push_str(&cert.to_json());
        }
        out.push_str("\n  }");

        #[cfg(feature = "verify")]
        {
            let lowering_entries: Vec<(&str, String, String)> = self
                .certificates
                .iter()
                .filter_map(|(name, cert)| {
                    let lowering = cert.lowering_certificate()?;
                    let lowering_json = lowering
                        .to_json()
                        .expect("lowering certificate JSON serialization must succeed");
                    let trust_json = lowering
                        .to_trust_proof_cert_json()
                        .expect("trust-proof-cert JSON serialization must succeed");
                    Some((name.as_str(), lowering_json, trust_json))
                })
                .collect();

            if !lowering_entries.is_empty() {
                out.push_str(",\n  \"lowering_certificates\": {");
                for (i, (name, lowering_json, _)) in lowering_entries.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    out.push_str(&format!(
                        "\n    \"{}\": ",
                        crate::jit_cert::escape_for_export(name)
                    ));
                    out.push_str(lowering_json);
                }
                out.push_str("\n  },\n  \"trust_proof_certificates\": {");
                for (i, (name, _, trust_json)) in lowering_entries.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    out.push_str(&format!(
                        "\n    \"{}\": ",
                        crate::jit_cert::escape_for_export(name)
                    ));
                    out.push_str(trust_json);
                }
                out.push_str("\n  }");
            }
        }

        out.push_str("\n}");
        out
    }
}

impl Drop for ExecutableBuffer {
    fn drop(&mut self) {
        // ORDER MATTERS (#494): `munmap` must run BEFORE the counter /
        // timing-cell / timing-state boxes are dropped. This runs first
        // (`Drop::drop` is invoked before the compiler-generated field
        // drops), and the counter/timing fields are declared AFTER
        // `memory` in `ExecutableBuffer` so they drop after this returns.
        //
        // Consequence: once `munmap` returns, any in-flight JIT call is
        // already a use-after-free on the text pages themselves — there
        // is no window in which the trampoline can observe a freed
        // counter while the text is still mapped. See the module-level
        // "Profile counter & timing-cell lifetime" section.
        if !self.memory.is_null() {
            // Unregister the Windows unwind table unconditionally: the table
            // itself lives in an owned Vec, so deregistration is safe even
            // when the mapping extent below cannot be validated. (Previously
            // the bail-out path skipped this too.)
            self.windows_unwind.unregister();
            let allocation_len = self.allocation_len_for_unmap();
            if allocation_len == 0 {
                // #734 fail-closed bail-out: the recorded allocation extent
                // is inconsistent and unmapping a guessed extent could tear
                // down unrelated mappings — leaking is the sound choice, but
                // it must never be SILENT (the accumulation failure mode of
                // docs/jit-parallel-race-2026-06-29.md). Count it so tests
                // and diagnostics can observe the leak.
                UNMAP_BAILOUT_LEAKS.fetch_add(1, Ordering::Relaxed);
                return;
            }
            unsafe {
                sys::munmap(self.memory, allocation_len);
            }
        }
    }
}

/// Process-wide count of `ExecutableBuffer` drops that had to LEAK their
/// mapping because the recorded allocation extent failed the #734
/// shadow/cookie validation. Nonzero values mean executable mappings are
/// accumulating; healthy processes stay at 0 forever.
static UNMAP_BAILOUT_LEAKS: AtomicU64 = AtomicU64::new(0);

/// Number of executable mappings leaked by fail-closed `Drop` bail-outs in
/// this process. See [`ExecutableBuffer`]'s Drop for the bail-out rationale.
pub fn executable_buffer_unmap_bailout_count() -> u64 {
    UNMAP_BAILOUT_LEAKS.load(Ordering::Relaxed)
}

unsafe fn write_u64_literal_unaligned(base: *mut u8, offset: usize, value: u64) {
    // AArch64 literal slots can sit at 4-byte instruction-aligned offsets such
    // as 20, 92, or 100. They are valid byte ranges but not guaranteed to be
    // aligned for a `u64` store.
    unsafe {
        std::ptr::write_unaligned(base.add(offset) as *mut u64, value);
    }
}

// ---------------------------------------------------------------------------
// Architecture-specific fixup patching and veneer stubs
// ---------------------------------------------------------------------------

/// Patch a branch/call fixup at `offset` to reach `target`.
/// Dispatches to the appropriate architecture-specific implementation.
#[cfg(target_arch = "aarch64")]
fn patch_fixup(code: &mut [u8], offset: u32, target: u64) -> Result<(), JitError> {
    patch_branch26(code, offset, target)
}

#[cfg(target_arch = "x86_64")]
fn patch_fixup(code: &mut [u8], offset: u32, target: u64) -> Result<(), JitError> {
    patch_rel32(code, offset, target)
}

/// Emit a veneer trampoline stub that loads a 64-bit address and jumps to it.
/// The absolute address slot is filled in later.
#[cfg(target_arch = "aarch64")]
fn emit_veneer_stub(code: &mut Vec<u8>) {
    // LDR X16, [PC, #8] (0x58000050) ; BR X16 (0xD61F0200) ; .quad <addr>
    // Total: 16 bytes
    code.extend_from_slice(&0x5800_0050u32.to_le_bytes());
    code.extend_from_slice(&0xD61F_0200u32.to_le_bytes());
    code.extend_from_slice(&[0u8; 8]);
}

#[cfg(target_arch = "aarch64")]
fn emit_profile_trampoline_aarch64(code: &mut Vec<u8>) -> usize {
    let literal_slot_offset = code.len() + 28;
    // Block-count trampolines run at arbitrary internal block entries after
    // register allocation, so preserve IP0/IP1 instead of treating them as
    // ABI scratch only valid at function boundaries.
    code.extend_from_slice(&0xA9BF_47F0u32.to_le_bytes()); // STP X16, X17, [SP, #-16]!
    code.extend_from_slice(&0x5800_00D0u32.to_le_bytes()); // LDR X16, [PC, #24]
    code.extend_from_slice(&0xF940_0211u32.to_le_bytes());
    code.extend_from_slice(&0x9100_0631u32.to_le_bytes());
    code.extend_from_slice(&0xF900_0211u32.to_le_bytes());
    code.extend_from_slice(&0xA8C1_47F0u32.to_le_bytes()); // LDP X16, X17, [SP], #16
    code.extend_from_slice(&0x1400_0003u32.to_le_bytes());
    code.extend_from_slice(&[0u8; 8]);
    literal_slot_offset
}

/// Size in bytes of the AArch64 profile trampoline emitted by
/// [`emit_profile_trampoline_aarch64`]. Kept as a named constant so the
/// block-splicing logic and the byte-layout unit test stay in sync.
#[cfg(target_arch = "aarch64")]
const AARCH64_PROFILE_TRAMPOLINE_BYTES: usize = 36;

/// Size in bytes of the AArch64 `BlockCountsAndTiming` trampoline
/// emitted by [`emit_profile_trampoline_with_timing_aarch64`]
/// (issue #364, Phase 3).
///
/// Layout (byte offsets within a single trampoline):
///
/// ```text
///   0  STP X9,  X10, [SP, #-16]!      ; save caller-saved temps
///   4  STP X11, X12, [SP, #-16]!      ;
///   8  STP X16, X17, [SP, #-16]!      ; save IP0/IP1 too
///  12  LDR X16, [PC, #lit_counter]    ; X16 = &BlockTimingCell
///  16  LDR X17, [X16]                 ; count++
///  20  ADD X17, X17, #1               ;
///  24  STR X17, [X16]                 ;
///  28  MRS X17, CNTVCT_EL0            ; X17 = now
///  32  ADD X11, X16, #8               ; X11 = &cell.total_cycles
///  36  LDR X9,  [PC, #lit_tstate]     ; X9 = &TimingState
///  40  LDR X10, [X9]                  ; X10 = prev_ts
///  44  CBZ X10, skip_attrib           ; +24 → off 68
///  48    SUB X12, X17, X10            ; X12 = now - prev_ts
///  52    LDR X16, [X9, #8]            ; X16 = prev_accum_ptr
///  56    LDR X10, [X16]               ; X10 = *prev_accum
///  60    ADD X10, X10, X12            ; X10 += delta
///  64    STR X10, [X16]               ; *prev_accum = X10
///  68  skip_attrib: STR X17, [X9]     ; prev_ts = now
///  72  STR X11, [X9, #8]              ; prev_accum_ptr = &cell.total_cycles
///  76  LDP X11, X12, [SP], #16
///  80  LDP X9,  X10, [SP], #16
///  84  LDP X16, X17, [SP], #16
///  88  B   over_literals              ; +20 → off 108
///  92  .quad lit_counter              ; patched to &BlockTimingCell
/// 100  .quad lit_tstate               ; patched to &TimingState
/// 108  (end; block body follows)
/// ```
///
/// The scratch-saving prologue uses `{X9, X10, X11, X12, X16, X17}` and
/// leaves `{X0..X8}` untouched so argument registers are preserved across
/// every block entry, including the entry block (which doubles as the
/// function entry). `X16`/`X17` are IP0/IP1, but block-entry trampolines
/// run after register allocation at arbitrary internal labels, so they
/// are preserved just like the other temporaries. `X18` (Darwin platform
/// register) is intentionally NEVER touched.
///
/// The literal pool lives inside the trampoline so each block's
/// trampoline has its own two literals (counter cell pointer and
/// timing-state pointer) — no cross-trampoline reference chains to
/// complicate re-patching when trampolines are spliced in.
#[cfg(target_arch = "aarch64")]
const AARCH64_PROFILE_TRAMPOLINE_TIMING_BYTES: usize = 108;

/// Emit the AArch64 `BlockCountsAndTiming` trampoline into `code`.
/// Returns `(counter_cell_literal_offset, timing_state_literal_offset)`
/// — both absolute offsets into `code` at the time of return, suitable
/// for pushing onto the compile_raw patch-site lists.
///
/// See [`AARCH64_PROFILE_TRAMPOLINE_TIMING_BYTES`] for the full byte
/// layout, register plan, and ABI notes.
#[cfg(target_arch = "aarch64")]
fn emit_profile_trampoline_with_timing_aarch64(code: &mut Vec<u8>) -> (usize, usize) {
    let start = code.len();
    // Prolog: save every temporary the attribution body clobbers. These
    // trampolines run at arbitrary block entries after register allocation.
    code.extend_from_slice(&0xA9BF_2BE9u32.to_le_bytes()); // STP X9, X10, [SP, #-16]!
    code.extend_from_slice(&0xA9BF_33EBu32.to_le_bytes()); // STP X11, X12, [SP, #-16]!
    code.extend_from_slice(&0xA9BF_47F0u32.to_le_bytes()); // STP X16, X17, [SP, #-16]!

    // --- count increment ---
    // LDR X16, [PC, #80] → literal at offset +80 from this instruction
    // (instr at start+12, literal at start+92, delta = 80).
    code.extend_from_slice(&0x5800_0290u32.to_le_bytes()); // LDR X16, [PC, #80]
    code.extend_from_slice(&0xF940_0211u32.to_le_bytes()); // LDR X17, [X16]
    code.extend_from_slice(&0x9100_0631u32.to_le_bytes()); // ADD X17, X17, #1
    code.extend_from_slice(&0xF900_0211u32.to_le_bytes()); // STR X17, [X16]

    // --- timing capture + cross-block attribution ---
    code.extend_from_slice(&0xD53B_E051u32.to_le_bytes()); // MRS X17, CNTVCT_EL0
    code.extend_from_slice(&0x9100_220Bu32.to_le_bytes()); // ADD X11, X16, #8
    // LDR X9, [PC, #64] → literal at offset +64 from this instruction
    // (instr at start+36, literal at start+100, delta = 64).
    code.extend_from_slice(&0x5800_0209u32.to_le_bytes()); // LDR X9, [PC, #64]
    code.extend_from_slice(&0xF940_012Au32.to_le_bytes()); // LDR X10, [X9]
    code.extend_from_slice(&0xB400_00CAu32.to_le_bytes()); // CBZ X10, +24 (skip_attrib)
    code.extend_from_slice(&0xCB0A_022Cu32.to_le_bytes()); // SUB X12, X17, X10
    code.extend_from_slice(&0xF940_0530u32.to_le_bytes()); // LDR X16, [X9, #8]
    code.extend_from_slice(&0xF940_020Au32.to_le_bytes()); // LDR X10, [X16]
    code.extend_from_slice(&0x8B0C_014Au32.to_le_bytes()); // ADD X10, X10, X12
    code.extend_from_slice(&0xF900_020Au32.to_le_bytes()); // STR X10, [X16]
    // skip_attrib:
    code.extend_from_slice(&0xF900_0131u32.to_le_bytes()); // STR X17, [X9]      ; prev_ts = now
    code.extend_from_slice(&0xF900_052Bu32.to_le_bytes()); // STR X11, [X9, #8]  ; prev_accum = &cell.cycles

    // --- epilogue: restore X9, X10, X11, X12, X16, X17 ---
    code.extend_from_slice(&0xA8C1_33EBu32.to_le_bytes()); // LDP X11, X12, [SP], #16
    code.extend_from_slice(&0xA8C1_2BE9u32.to_le_bytes()); // LDP X9, X10,  [SP], #16
    code.extend_from_slice(&0xA8C1_47F0u32.to_le_bytes()); // LDP X16, X17, [SP], #16

    // --- branch over the 16-byte literal pool into the block body ---
    code.extend_from_slice(&0x1400_0005u32.to_le_bytes()); // B +20 (over 16B literals + 4B padding-past-self)

    // Literal pool (patched by compile_raw_inner):
    let lit_counter_offset = code.len();
    code.extend_from_slice(&[0u8; 8]); // .quad <&BlockTimingCell>
    let lit_tstate_offset = code.len();
    code.extend_from_slice(&[0u8; 8]); // .quad <&TimingState>

    debug_assert_eq!(code.len() - start, AARCH64_PROFILE_TRAMPOLINE_TIMING_BYTES);
    debug_assert_eq!(lit_counter_offset - start, 92);
    debug_assert_eq!(lit_tstate_offset - start, 100);

    (lit_counter_offset, lit_tstate_offset)
}

/// Size in bytes of the x86-64 profile trampoline emitted by
/// [`emit_profile_trampoline_x86_64`].
#[cfg(target_arch = "x86_64")]
const X86_64_PROFILE_TRAMPOLINE_BYTES: usize = 16;

#[cfg(target_arch = "aarch64")]
fn block_splice_encoding_error(message: impl Into<String>) -> JitError {
    JitError::Pipeline(PipelineError::Encoding(message.into()))
}

#[cfg(target_arch = "aarch64")]
fn register_block_counter_patch_sites(
    function: &str,
    block_counter_ptrs: &HashMap<BlockId, *const AtomicU64>,
    tramp_sites: &[(BlockId, usize)],
    func_base: usize,
    counter_patch_sites: &mut Vec<(usize, *const AtomicU64)>,
) -> Result<(), JitError> {
    let mut resolved = Vec::with_capacity(tramp_sites.len());
    for &(bid, slot_off) in tramp_sites {
        let ptr = block_counter_ptrs.get(&bid).copied().ok_or_else(|| {
            JitError::MissingBlockProfileCounter {
                function: function.to_owned(),
                block_id: bid.0,
            }
        })?;
        resolved.push((func_base + slot_off, ptr));
    }
    counter_patch_sites.extend(resolved);
    Ok(())
}

#[cfg(target_arch = "aarch64")]
fn register_block_timing_patch_sites(
    function: &str,
    block_cell_ptrs: &HashMap<BlockId, *const AtomicU64>,
    tramp_sites: &[(BlockId, usize, usize)],
    func_base: usize,
    counter_patch_sites: &mut Vec<(usize, *const AtomicU64)>,
    tstate_patch_sites: &mut Vec<usize>,
) -> Result<(), JitError> {
    let mut resolved_counters = Vec::with_capacity(tramp_sites.len());
    let mut resolved_tstates = Vec::with_capacity(tramp_sites.len());
    for &(bid, counter_off, tstate_off) in tramp_sites {
        let ptr =
            block_cell_ptrs
                .get(&bid)
                .copied()
                .ok_or_else(|| JitError::MissingBlockTimingCell {
                    function: function.to_owned(),
                    block_id: bid.0,
                })?;
        resolved_counters.push((func_base + counter_off, ptr));
        resolved_tstates.push(func_base + tstate_off);
    }
    counter_patch_sites.extend(resolved_counters);
    tstate_patch_sites.extend(resolved_tstates);
    Ok(())
}

#[cfg(target_arch = "aarch64")]
fn block_splice_byte_offset(
    prefix: &str,
    block_byte_offsets: &HashMap<BlockId, u32>,
    bid: BlockId,
    purpose: &str,
) -> Result<usize, JitError> {
    block_byte_offsets
        .get(&bid)
        .copied()
        .map(|offset| offset as usize)
        .ok_or_else(|| {
            block_splice_encoding_error(format!(
                "{prefix}: block {bid:?} missing byte offset while {purpose}"
            ))
        })
}

#[cfg(target_arch = "aarch64")]
fn block_splice_layout_index(
    prefix: &str,
    block_layout_idx: &HashMap<BlockId, usize>,
    bid: BlockId,
    purpose: &str,
) -> Result<usize, JitError> {
    block_layout_idx.get(&bid).copied().ok_or_else(|| {
        block_splice_encoding_error(format!(
            "{prefix}: block {bid:?} missing layout index while {purpose}"
        ))
    })
}

#[cfg(target_arch = "aarch64")]
fn block_splice_trampoline_start(
    prefix: &str,
    block_new_trampoline_start: &HashMap<BlockId, usize>,
    bid: BlockId,
    role: &str,
) -> Result<usize, JitError> {
    block_new_trampoline_start
        .get(&bid)
        .copied()
        .ok_or_else(|| {
            block_splice_encoding_error(format!(
                "{prefix}: {role} {bid:?} has no post-splice offset"
            ))
        })
}

#[cfg(target_arch = "aarch64")]
fn validate_block_splice_body_range(
    prefix: &str,
    bid: BlockId,
    start: usize,
    end: usize,
    body_len: usize,
) -> Result<(), JitError> {
    if start > end || end > body_len {
        return Err(block_splice_encoding_error(format!(
            "{prefix}: block {bid:?} byte range {start}..{end} is outside body length {body_len}"
        )));
    }
    Ok(())
}

/// Splice an AArch64 profile trampoline in front of every basic block of
/// an already-encoded function body.
///
/// Design (issue #364, `ProfileHookMode::BlockCounts`):
/// - The entry block's trampoline doubles as the function-entry trampoline,
///   so a block-profiled function does not need a separate function-entry
///   increment — counting the entry block already counts the call.
/// - Each block gets its own counter, keyed externally by
///   `format!("{}::block{}", func.name, block_id.0)` so the canonical
///   function-entry APIs (`get_profile(name)`) continue to work for the
///   whole function via `block0`.
/// - Intra-function PC-relative branches (`B`, `B.cond`, `CBZ`, `CBNZ`,
///   `TBZ`, `TBNZ`) are re-patched so their displacements still land on
///   the intended target block's new location. After splicing, branch
///   targets that were block starts now point at the *trampoline* for
///   that block, which is exactly what we want — the counter has to fire
///   every time control reaches the block, including on back-edges.
/// - Jump tables (issue #490): `encode_function_with_fixups_and_blocks`
///   appends one 32-bit-entry table per ADR-with-`JumpTableIndex` operand
///   after the function body. The ADR's imm21 was patched to `(table -
///   adr)`, and each entry was written as `(target_block - table_base)`.
///   After splicing, all three terms shift by different amounts, so the
///   splice must (a) strip the original jump-table tail, (b) re-patch
///   each ADR imm21 against the new layout, and (c) regenerate each
///   table entry against post-splice block positions. See issue #490.
/// - The trampoline size (`AARCH64_PROFILE_TRAMPOLINE_BYTES` = 36 bytes) is a
///   multiple of 4, so all branch encodings remain 4-byte-aligned.
///
/// Returns the spliced bytes and the list of `(block_id,
/// literal_slot_offset)` patch sites within the spliced bytes.
/// `fixups` is modified in place: each fixup's `offset` is shifted by the
/// cumulative trampoline bytes preceding the fixup's original byte
/// position, so external fixups still index the correct branch
/// instruction in the spliced output.
#[cfg(target_arch = "aarch64")]
fn splice_block_trampolines_aarch64(
    func: &IrMachFunction,
    body_bytes: &[u8],
    block_byte_offsets: &HashMap<BlockId, u32>,
    fixups: &mut [Fixup],
) -> Result<(Vec<u8>, Vec<(BlockId, usize)>), JitError> {
    use trust_cg_ir::inst::AArch64Opcode;

    const PREFIX: &str = "block-splice";
    let tramp = AARCH64_PROFILE_TRAMPOLINE_BYTES;

    // Block layout order and per-block shift amounts. Block at layout
    // position `k` (0-indexed) has `(k+1)*tramp` bytes of trampoline
    // inserted at-or-before its first original byte: one trampoline each
    // for block_order[0..=k].
    let mut block_layout_idx: HashMap<BlockId, usize> = HashMap::new();
    for (idx, &bid) in func.block_order.iter().enumerate() {
        block_layout_idx.insert(bid, idx);
    }

    // Compute the new (post-splice) byte offset of each block's trampoline
    // start.
    let mut block_new_trampoline_start: HashMap<BlockId, usize> = HashMap::new();
    for (k, &bid) in func.block_order.iter().enumerate() {
        let orig = block_splice_byte_offset(
            PREFIX,
            block_byte_offsets,
            bid,
            "computing trampoline start",
        )?;
        let tramp_start = orig + k * tramp;
        block_new_trampoline_start.insert(bid, tramp_start);
    }

    // Collect ADR-for-jump-table sites (issue #490). We must replay the
    // exact walk used by `encode_function_with_fixups_and_blocks` so the
    // ordering (and therefore which appended table a given ADR points at)
    // matches the encoder. Each entry records:
    //   - `orig_adr_byte`: byte offset in `body_bytes` of the 4-byte ADR
    //   - `source_layout_idx`: layout position of the containing block
    //   - `jt_idx`: index into `func.jump_tables`
    // Also compute `insts_end_in_body` = the byte offset in `body_bytes`
    // that separates instruction bytes from the appended jump-table tail.
    // Since the encoder writes exactly 4 bytes per non-pseudo instruction,
    // this equals (start of last block) + 4 * non_pseudo_count(last
    // block).
    let mut jt_adr_sites: Vec<(usize, usize, u32)> = Vec::new();
    for (layout_idx, &bid) in func.block_order.iter().enumerate() {
        let block = func.block(bid);
        let mut cur_byte = block_splice_byte_offset(
            PREFIX,
            block_byte_offsets,
            bid,
            "collecting jump-table ADR sites",
        )?;
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            if inst.is_pseudo() {
                continue;
            }
            if inst.opcode == AArch64Opcode::Adr
                && let Some(jt_idx) = inst.operands.get(1).and_then(|op| op.as_jump_table_index())
            {
                jt_adr_sites.push((cur_byte, layout_idx, jt_idx));
            }
            cur_byte += 4;
        }
    }
    let insts_end_in_body = {
        let last_bid = *func.block_order.last().ok_or_else(|| {
            JitError::Pipeline(PipelineError::Encoding(
                "block-splice: empty block_order".to_string(),
            ))
        })?;
        let last_block = func.block(last_bid);
        let last_non_pseudo = last_block
            .insts
            .iter()
            .filter(|&&id| !func.inst(id).is_pseudo())
            .count();
        block_splice_byte_offset(
            PREFIX,
            block_byte_offsets,
            last_bid,
            "computing instruction body end",
        )? + last_non_pseudo * 4
    };
    if insts_end_in_body > body_bytes.len() {
        return Err(JitError::Pipeline(PipelineError::Encoding(format!(
            "block-splice: computed insts_end_in_body {} exceeds body_bytes.len() {}",
            insts_end_in_body,
            body_bytes.len()
        ))));
    }
    // Sanity: if no ADR->jump-table sites were found, the jump-table tail
    // must be empty. If it's non-empty without any ADR pointing at it, we
    // cannot safely reconstruct the tail, so bail out explicitly rather
    // than silently dropping bytes.
    if jt_adr_sites.is_empty() && insts_end_in_body < body_bytes.len() {
        return Err(JitError::Pipeline(PipelineError::Encoding(format!(
            "block-splice: body_bytes has {} bytes of unexpected tail past instruction end \
             without any Adr(JumpTableIndex) site",
            body_bytes.len() - insts_end_in_body
        ))));
    }
    // Range-check every referenced jt_idx BEFORE we start writing `out`.
    for &(_, _, jt_idx) in &jt_adr_sites {
        if (jt_idx as usize) >= func.jump_tables.len() {
            return Err(JitError::Pipeline(PipelineError::Encoding(format!(
                "block-splice: Adr references jump table index {} but func has only {} tables",
                jt_idx,
                func.jump_tables.len()
            ))));
        }
    }

    // Build the spliced output by walking blocks in layout order,
    // inserting one trampoline then the original block bytes.
    let mut out = Vec::with_capacity(body_bytes.len() + func.block_order.len() * tramp);
    let mut tramp_sites: Vec<(BlockId, usize)> = Vec::with_capacity(func.block_order.len());

    for (k, &bid) in func.block_order.iter().enumerate() {
        let block_orig_start =
            block_splice_byte_offset(PREFIX, block_byte_offsets, bid, "copying block bytes")?;
        let block_orig_end = if k + 1 < func.block_order.len() {
            block_splice_byte_offset(
                PREFIX,
                block_byte_offsets,
                func.block_order[k + 1],
                "copying block bytes",
            )?
        } else {
            // Last block: stop at the end of instruction bytes so the
            // appended jump-table tail is NOT copied into the spliced
            // output. The tables are regenerated below against the
            // post-splice layout. (issue #490)
            insts_end_in_body
        };
        validate_block_splice_body_range(
            PREFIX,
            bid,
            block_orig_start,
            block_orig_end,
            body_bytes.len(),
        )?;
        // Emit trampoline for this block.
        let literal_slot_offset = emit_profile_trampoline_aarch64(&mut out);
        tramp_sites.push((bid, literal_slot_offset));
        // Sanity: the trampoline just emitted begins at the computed
        // post-splice offset.
        let expected_tramp_start =
            block_splice_trampoline_start(PREFIX, &block_new_trampoline_start, bid, "block")?;
        debug_assert_eq!(out.len() - tramp, expected_tramp_start);
        // Append the block's original bytes.
        out.extend_from_slice(&body_bytes[block_orig_start..block_orig_end]);
    }

    // Re-patch intra-function PC-relative branches so displacements still
    // resolve to the intended target block. We iterate instructions in
    // original layout order so we can compute the original byte offset of
    // each branch instruction.
    for &bid in &func.block_order {
        let block = func.block(bid);
        let mut orig_inst_byte = block_splice_byte_offset(
            PREFIX,
            block_byte_offsets,
            bid,
            "re-patching intra-function branches",
        )?;
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            if inst.is_pseudo() {
                continue;
            }
            let opcode = inst.opcode;
            let is_branch_with_symbol = matches!(
                opcode,
                AArch64Opcode::B | AArch64Opcode::TailCall | AArch64Opcode::Bl | AArch64Opcode::BL
            ) && inst.operands.first().is_some_and(|op| op.is_symbol());

            // Intra-function PC-relative branches we need to re-patch. BL
            // with a symbol target is NOT re-patched here — that's an
            // external fixup resolved later.
            let is_intra_branch = matches!(
                opcode,
                AArch64Opcode::B
                    | AArch64Opcode::TailCall
                    | AArch64Opcode::BCond
                    | AArch64Opcode::Cbz
                    | AArch64Opcode::Cbnz
                    | AArch64Opcode::Tbz
                    | AArch64Opcode::Tbnz
            ) && !is_branch_with_symbol;

            if is_intra_branch {
                // Locate the new source byte in `out`.
                let source_layout_idx = block_splice_layout_index(
                    PREFIX,
                    &block_layout_idx,
                    bid,
                    "re-patching branch source",
                )?;
                let new_source = orig_inst_byte + (source_layout_idx + 1) * tramp;
                if new_source + 4 > out.len() {
                    return Err(block_splice_encoding_error(format!(
                        "{PREFIX}: branch source at post-splice offset {new_source} exceeds out buffer length {}",
                        out.len()
                    )));
                }

                // Decode the existing 4-byte instruction from `out`, get
                // its original (baked-in) imm field, compute the original
                // target byte offset, find the target block, and re-encode
                // with the shifted displacement.
                let existing = u32::from_le_bytes([
                    out[new_source],
                    out[new_source + 1],
                    out[new_source + 2],
                    out[new_source + 3],
                ]);

                let (imm_bits, imm_shift, imm_mask, sign_bits) = match opcode {
                    AArch64Opcode::B
                    | AArch64Opcode::TailCall
                    | AArch64Opcode::Bl
                    | AArch64Opcode::BL => (26u32, 0u32, 0x03FF_FFFFu32, 25u32),
                    AArch64Opcode::BCond | AArch64Opcode::Cbz | AArch64Opcode::Cbnz => {
                        (19, 5, 0x0007_FFFF, 18)
                    }
                    AArch64Opcode::Tbz | AArch64Opcode::Tbnz => (14, 5, 0x0000_3FFF, 13),
                    _ => unreachable!(),
                };
                let raw_imm = (existing >> imm_shift) & imm_mask;
                // Sign-extend from `imm_bits` bits.
                let sign = (raw_imm >> sign_bits) & 1;
                let signed_imm = if sign == 1 {
                    (raw_imm as i64) | !((1i64 << imm_bits) - 1)
                } else {
                    raw_imm as i64
                };
                let original_target_byte = (orig_inst_byte as i64) + signed_imm * 4;
                if original_target_byte < 0 {
                    return Err(JitError::Pipeline(PipelineError::Encoding(format!(
                        "block-splice: negative original branch target {}",
                        original_target_byte
                    ))));
                }
                let original_target_byte = original_target_byte as u32;

                // Look up which block starts at `original_target_byte`.
                // By the resolve_branches invariant, every intra-function
                // branch's target is a block start.
                let target_bid = block_byte_offsets
                    .iter()
                    .find(|&(_, &bo)| bo == original_target_byte)
                    .map(|(bid, _)| *bid)
                    .ok_or_else(|| {
                        JitError::Pipeline(PipelineError::Encoding(format!(
                            "block-splice: branch at original byte {} targets {} which is not a block start",
                            orig_inst_byte, original_target_byte
                        )))
                    })?;
                let new_target = block_splice_trampoline_start(
                    PREFIX,
                    &block_new_trampoline_start,
                    target_bid,
                    "branch target",
                )?;

                // Compute new byte-distance and encode.
                let new_dist_bytes = new_target as i64 - new_source as i64;
                if new_dist_bytes % 4 != 0 {
                    return Err(JitError::Pipeline(PipelineError::Encoding(format!(
                        "block-splice: non-4-byte-aligned branch distance {}",
                        new_dist_bytes
                    ))));
                }
                let new_inst_units = new_dist_bytes / 4;
                // Range-check.
                let range = 1i64 << (imm_bits - 1);
                if new_inst_units < -range || new_inst_units >= range {
                    return Err(JitError::Pipeline(PipelineError::Encoding(format!(
                        "block-splice: branch displacement {} out of {}-bit range after \
                         trampoline insertion",
                        new_inst_units, imm_bits
                    ))));
                }
                let new_imm = (new_inst_units as u32) & imm_mask;
                let cleared = existing & !(imm_mask << imm_shift);
                let rewritten = cleared | (new_imm << imm_shift);
                out[new_source..new_source + 4].copy_from_slice(&rewritten.to_le_bytes());
            }

            orig_inst_byte += 4;
        }
    }

    // Shift external fixups: each fixup's `offset` pointed into the
    // original `body_bytes`. In the new `out` it must shift by
    // `(source_layout_idx + 1) * tramp` where `source_layout_idx` is the
    // layout position of the block containing the fixup.
    let mut layout_starts: Vec<(usize, usize)> = Vec::with_capacity(func.block_order.len());
    for (idx, &bid) in func.block_order.iter().enumerate() {
        layout_starts.push((
            block_splice_byte_offset(PREFIX, block_byte_offsets, bid, "shifting external fixups")?,
            idx,
        ));
    }
    layout_starts.sort_by_key(|&(off, _)| off);

    for fx in fixups.iter_mut() {
        let off = fx.offset as usize;
        // Find the largest layout_start.0 <= off; that defines which block
        // contains this fixup.
        let mut layout_idx = 0usize;
        for (start, idx) in layout_starts.iter() {
            if *start <= off {
                layout_idx = *idx;
            } else {
                break;
            }
        }
        let shift = (layout_idx + 1) * tramp;
        fx.offset = (off + shift) as u32;
    }

    // Regenerate jump tables against the post-splice layout (issue #490).
    //
    // Replay the pipeline.rs emission walk: for each ADR->jump-table site
    // (in the same deterministic order the encoder used), append one
    // table's worth of bytes at the current end of `out`, then re-patch
    // the ADR's imm21 to point at that new table base.
    //
    // Each table entry is a 32-bit signed delta
    // `(target_block_new_offset - new_table_base)` where
    // `target_block_new_offset` is the post-splice start of the TARGET
    // BLOCK'S TRAMPOLINE. Landing on the trampoline (not the first real
    // instruction) matches the convention used for regular branch
    // re-patching so every jump-table-dispatched case increments the
    // target block's counter.
    for (orig_adr_byte, source_layout_idx, jt_idx) in jt_adr_sites {
        let new_adr = orig_adr_byte + (source_layout_idx + 1) * tramp;
        if new_adr + 4 > out.len() {
            return Err(JitError::Pipeline(PipelineError::Encoding(format!(
                "block-splice: ADR site at post-splice offset {} exceeds out buffer length {}",
                new_adr,
                out.len()
            ))));
        }

        let new_table_base = out.len();
        let pc_relative = new_table_base as i64 - new_adr as i64;
        if !(-(1i64 << 20)..(1i64 << 20)).contains(&pc_relative) {
            return Err(JitError::Pipeline(PipelineError::Encoding(format!(
                "block-splice: ADR->jump-table offset {} does not fit in imm21",
                pc_relative
            ))));
        }

        // Re-encode the ADR, preserving Rd from the placeholder bits[4:0].
        let placeholder_word = u32::from_le_bytes([
            out[new_adr],
            out[new_adr + 1],
            out[new_adr + 2],
            out[new_adr + 3],
        ]);
        let rd = (placeholder_word & 0x1F) as u8;
        let patched = crate::aarch64::encoding_mem::encode_adr(pc_relative as i32, rd)
            .map_err(|e| JitError::Pipeline(PipelineError::Encoding(e.to_string())))?;
        out[new_adr..new_adr + 4].copy_from_slice(&patched.to_le_bytes());

        // Append one table copy. (If two ADRs share the same jt_idx the
        // pipeline emits two separate tables; we mirror that exactly.)
        let jt = &func.jump_tables[jt_idx as usize];
        for target in &jt.targets {
            let new_target = block_splice_trampoline_start(
                PREFIX,
                &block_new_trampoline_start,
                *target,
                "jump-table target",
            )?;
            let entry: i32 = (new_target as i64 - new_table_base as i64) as i32;
            out.extend_from_slice(&entry.to_le_bytes());
        }
    }

    Ok((out, tramp_sites))
}

/// Splice an AArch64 `BlockCountsAndTiming` trampoline in front of every
/// basic block of an already-encoded function body (issue #364, Phase 3).
///
/// This is the timing-aware sibling of [`splice_block_trampolines_aarch64`].
/// It follows the same re-patching discipline for intra-function PC-relative
/// branches but:
/// - Emits 108-byte [`emit_profile_trampoline_with_timing_aarch64`] trampolines
///   instead of 28-byte plain-counter ones.
/// - Returns two patch-site offsets per block: one for the
///   `&BlockTimingCell` literal and one for the `&TimingState` literal.
///
/// The trampoline size is a multiple of 4, so branch encoding alignment
/// remains valid. The 14-bit range of `TBZ/TBNZ` allows roughly
/// `(2^13 * 4) / 108 ≈ 303` blocks per function before displacement
/// overflow; that is large enough for any human-written function and is
/// documented as a Phase 3 limitation in #364.
///
/// Jump-table handling mirrors [`splice_block_trampolines_aarch64`]: the
/// original post-body jump-table tail is stripped, ADR immediates are
/// re-patched against the post-timing-splice layout, and table entries are
/// regenerated to land on target block trampolines.
///
/// Returns the spliced bytes and a list of
/// `(block_id, counter_literal_offset, tstate_literal_offset)` patch sites
/// pointing into the spliced bytes. `fixups` is shifted in place.
#[cfg(target_arch = "aarch64")]
fn splice_block_trampolines_with_timing_aarch64(
    func: &IrMachFunction,
    body_bytes: &[u8],
    block_byte_offsets: &HashMap<BlockId, u32>,
    fixups: &mut [Fixup],
) -> Result<(Vec<u8>, Vec<(BlockId, usize, usize)>), JitError> {
    use trust_cg_ir::inst::AArch64Opcode;

    const PREFIX: &str = "timing-block-splice";
    let tramp = AARCH64_PROFILE_TRAMPOLINE_TIMING_BYTES;

    // Block layout order and per-block shift amounts.
    let mut block_layout_idx: HashMap<BlockId, usize> = HashMap::new();
    for (idx, &bid) in func.block_order.iter().enumerate() {
        block_layout_idx.insert(bid, idx);
    }

    // Compute the new (post-splice) byte offset of each block's trampoline
    // start.
    let mut block_new_trampoline_start: HashMap<BlockId, usize> = HashMap::new();
    for (k, &bid) in func.block_order.iter().enumerate() {
        let orig = block_splice_byte_offset(
            PREFIX,
            block_byte_offsets,
            bid,
            "computing trampoline start",
        )?;
        let tramp_start = orig + k * tramp;
        block_new_trampoline_start.insert(bid, tramp_start);
    }

    // Collect ADR-for-jump-table sites and identify where the instruction
    // body ends before any appended jump-table tail. This intentionally
    // mirrors the plain BlockCounts splicer; only the trampoline size differs.
    let mut jt_adr_sites: Vec<(usize, usize, u32)> = Vec::new();
    for (layout_idx, &bid) in func.block_order.iter().enumerate() {
        let block = func.block(bid);
        let mut cur_byte = block_splice_byte_offset(
            PREFIX,
            block_byte_offsets,
            bid,
            "collecting jump-table ADR sites",
        )?;
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            if inst.is_pseudo() {
                continue;
            }
            if inst.opcode == AArch64Opcode::Adr
                && let Some(jt_idx) = inst.operands.get(1).and_then(|op| op.as_jump_table_index())
            {
                jt_adr_sites.push((cur_byte, layout_idx, jt_idx));
            }
            cur_byte += 4;
        }
    }
    let insts_end_in_body = {
        let last_bid = *func.block_order.last().ok_or_else(|| {
            JitError::Pipeline(PipelineError::Encoding(
                "timing-block-splice: empty block_order".to_string(),
            ))
        })?;
        let last_block = func.block(last_bid);
        let last_non_pseudo = last_block
            .insts
            .iter()
            .filter(|&&id| !func.inst(id).is_pseudo())
            .count();
        block_splice_byte_offset(
            PREFIX,
            block_byte_offsets,
            last_bid,
            "computing instruction body end",
        )? + last_non_pseudo * 4
    };
    if insts_end_in_body > body_bytes.len() {
        return Err(JitError::Pipeline(PipelineError::Encoding(format!(
            "timing-block-splice: computed insts_end_in_body {} exceeds body_bytes.len() {}",
            insts_end_in_body,
            body_bytes.len()
        ))));
    }
    if jt_adr_sites.is_empty() && insts_end_in_body < body_bytes.len() {
        return Err(JitError::Pipeline(PipelineError::Encoding(format!(
            "timing-block-splice: body_bytes has {} bytes of unexpected tail past instruction end \
             without any Adr(JumpTableIndex) site",
            body_bytes.len() - insts_end_in_body
        ))));
    }
    for &(_, _, jt_idx) in &jt_adr_sites {
        if (jt_idx as usize) >= func.jump_tables.len() {
            return Err(JitError::Pipeline(PipelineError::Encoding(format!(
                "timing-block-splice: Adr references jump table index {} but func has only {} tables",
                jt_idx,
                func.jump_tables.len()
            ))));
        }
    }

    // Build spliced output.
    let mut out = Vec::with_capacity(body_bytes.len() + func.block_order.len() * tramp);
    let mut tramp_sites: Vec<(BlockId, usize, usize)> = Vec::with_capacity(func.block_order.len());

    for (k, &bid) in func.block_order.iter().enumerate() {
        let block_orig_start =
            block_splice_byte_offset(PREFIX, block_byte_offsets, bid, "copying block bytes")?;
        let block_orig_end = if k + 1 < func.block_order.len() {
            block_splice_byte_offset(
                PREFIX,
                block_byte_offsets,
                func.block_order[k + 1],
                "copying block bytes",
            )?
        } else {
            insts_end_in_body
        };
        validate_block_splice_body_range(
            PREFIX,
            bid,
            block_orig_start,
            block_orig_end,
            body_bytes.len(),
        )?;
        let (lit_counter_offset, lit_tstate_offset) =
            emit_profile_trampoline_with_timing_aarch64(&mut out);
        tramp_sites.push((bid, lit_counter_offset, lit_tstate_offset));
        let expected_tramp_start =
            block_splice_trampoline_start(PREFIX, &block_new_trampoline_start, bid, "block")?;
        debug_assert_eq!(out.len() - tramp, expected_tramp_start);
        out.extend_from_slice(&body_bytes[block_orig_start..block_orig_end]);
    }

    // Re-patch intra-function PC-relative branches so displacements still
    // resolve to the intended target block. Identical logic to the
    // plain-counter splicer; only the `tramp` constant differs.
    for &bid in &func.block_order {
        let block = func.block(bid);
        let mut orig_inst_byte = block_splice_byte_offset(
            PREFIX,
            block_byte_offsets,
            bid,
            "re-patching intra-function branches",
        )?;
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            if inst.is_pseudo() {
                continue;
            }
            let opcode = inst.opcode;
            let is_branch_with_symbol = matches!(
                opcode,
                AArch64Opcode::B | AArch64Opcode::TailCall | AArch64Opcode::Bl | AArch64Opcode::BL
            ) && inst.operands.first().is_some_and(|op| op.is_symbol());

            let is_intra_branch = matches!(
                opcode,
                AArch64Opcode::B
                    | AArch64Opcode::TailCall
                    | AArch64Opcode::BCond
                    | AArch64Opcode::Cbz
                    | AArch64Opcode::Cbnz
                    | AArch64Opcode::Tbz
                    | AArch64Opcode::Tbnz
            ) && !is_branch_with_symbol;

            if is_intra_branch {
                let source_layout_idx = block_splice_layout_index(
                    PREFIX,
                    &block_layout_idx,
                    bid,
                    "re-patching branch source",
                )?;
                let new_source = orig_inst_byte + (source_layout_idx + 1) * tramp;
                if new_source + 4 > out.len() {
                    return Err(block_splice_encoding_error(format!(
                        "{PREFIX}: branch source at post-splice offset {new_source} exceeds out buffer length {}",
                        out.len()
                    )));
                }

                let existing = u32::from_le_bytes([
                    out[new_source],
                    out[new_source + 1],
                    out[new_source + 2],
                    out[new_source + 3],
                ]);

                let (imm_bits, imm_shift, imm_mask, sign_bits) = match opcode {
                    AArch64Opcode::B
                    | AArch64Opcode::TailCall
                    | AArch64Opcode::Bl
                    | AArch64Opcode::BL => (26u32, 0u32, 0x03FF_FFFFu32, 25u32),
                    AArch64Opcode::BCond | AArch64Opcode::Cbz | AArch64Opcode::Cbnz => {
                        (19, 5, 0x0007_FFFF, 18)
                    }
                    AArch64Opcode::Tbz | AArch64Opcode::Tbnz => (14, 5, 0x0000_3FFF, 13),
                    _ => unreachable!(),
                };
                let raw_imm = (existing >> imm_shift) & imm_mask;
                let sign = (raw_imm >> sign_bits) & 1;
                let signed_imm = if sign == 1 {
                    (raw_imm as i64) | !((1i64 << imm_bits) - 1)
                } else {
                    raw_imm as i64
                };
                let original_target_byte = (orig_inst_byte as i64) + signed_imm * 4;
                if original_target_byte < 0 {
                    return Err(JitError::Pipeline(PipelineError::Encoding(format!(
                        "timing-block-splice: negative original branch target {}",
                        original_target_byte
                    ))));
                }
                let original_target_byte = original_target_byte as u32;

                let target_bid = block_byte_offsets
                    .iter()
                    .find(|&(_, &bo)| bo == original_target_byte)
                    .map(|(bid, _)| *bid)
                    .ok_or_else(|| {
                        JitError::Pipeline(PipelineError::Encoding(format!(
                            "timing-block-splice: branch at original byte {} targets {} which is not a block start",
                            orig_inst_byte, original_target_byte
                        )))
                    })?;
                let new_target = block_splice_trampoline_start(
                    PREFIX,
                    &block_new_trampoline_start,
                    target_bid,
                    "branch target",
                )?;

                let new_dist_bytes = new_target as i64 - new_source as i64;
                if new_dist_bytes % 4 != 0 {
                    return Err(JitError::Pipeline(PipelineError::Encoding(format!(
                        "timing-block-splice: non-4-byte-aligned branch distance {}",
                        new_dist_bytes
                    ))));
                }
                let new_inst_units = new_dist_bytes / 4;
                let range = 1i64 << (imm_bits - 1);
                if new_inst_units < -range || new_inst_units >= range {
                    return Err(JitError::Pipeline(PipelineError::Encoding(format!(
                        "timing-block-splice: branch displacement {} out of {}-bit range after \
                         trampoline insertion (block count × 108-byte trampolines too large)",
                        new_inst_units, imm_bits
                    ))));
                }
                let new_imm = (new_inst_units as u32) & imm_mask;
                let cleared = existing & !(imm_mask << imm_shift);
                let rewritten = cleared | (new_imm << imm_shift);
                out[new_source..new_source + 4].copy_from_slice(&rewritten.to_le_bytes());
            }

            orig_inst_byte += 4;
        }
    }

    // Shift external fixups.
    let mut layout_starts: Vec<(usize, usize)> = Vec::with_capacity(func.block_order.len());
    for (idx, &bid) in func.block_order.iter().enumerate() {
        layout_starts.push((
            block_splice_byte_offset(PREFIX, block_byte_offsets, bid, "shifting external fixups")?,
            idx,
        ));
    }
    layout_starts.sort_by_key(|&(off, _)| off);

    for fx in fixups.iter_mut() {
        let off = fx.offset as usize;
        let mut layout_idx = 0usize;
        for (start, idx) in layout_starts.iter() {
            if *start <= off {
                layout_idx = *idx;
            } else {
                break;
            }
        }
        let shift = (layout_idx + 1) * tramp;
        fx.offset = (off + shift) as u32;
    }

    // Regenerate jump tables against the post-timing-splice layout. Entries
    // target the start of each destination block's timing trampoline so both
    // the counter and cycle attribution fire on indirect dispatch.
    for (orig_adr_byte, source_layout_idx, jt_idx) in jt_adr_sites {
        let new_adr = orig_adr_byte + (source_layout_idx + 1) * tramp;
        if new_adr + 4 > out.len() {
            return Err(JitError::Pipeline(PipelineError::Encoding(format!(
                "timing-block-splice: ADR site at post-splice offset {} exceeds out buffer length {}",
                new_adr,
                out.len()
            ))));
        }

        let new_table_base = out.len();
        let pc_relative = new_table_base as i64 - new_adr as i64;
        if !(-(1i64 << 20)..(1i64 << 20)).contains(&pc_relative) {
            return Err(JitError::Pipeline(PipelineError::Encoding(format!(
                "timing-block-splice: ADR->jump-table offset {} does not fit in imm21",
                pc_relative
            ))));
        }

        let placeholder_word = u32::from_le_bytes([
            out[new_adr],
            out[new_adr + 1],
            out[new_adr + 2],
            out[new_adr + 3],
        ]);
        let rd = (placeholder_word & 0x1F) as u8;
        let patched = crate::aarch64::encoding_mem::encode_adr(pc_relative as i32, rd)
            .map_err(|e| JitError::Pipeline(PipelineError::Encoding(e.to_string())))?;
        out[new_adr..new_adr + 4].copy_from_slice(&patched.to_le_bytes());

        let jt = &func.jump_tables[jt_idx as usize];
        for target in &jt.targets {
            let new_target = block_splice_trampoline_start(
                PREFIX,
                &block_new_trampoline_start,
                *target,
                "jump-table target",
            )?;
            let entry: i32 = (new_target as i64 - new_table_base as i64) as i32;
            out.extend_from_slice(&entry.to_le_bytes());
        }
    }

    Ok((out, tramp_sites))
}

#[cfg(target_arch = "x86_64")]
fn emit_profile_trampoline_x86_64(code: &mut Vec<u8>) -> usize {
    // Function-entry atomic counter trampoline for x86-64 (#478).
    //
    // Byte layout (16 bytes total):
    //   50              push rax                 ; 1 byte — preserve caller's RAX
    //   48 B8 ii ii ii ii ii ii ii ii
    //                   movabs rax, imm64        ; 10 bytes — heap counter ptr
    //   F0 48 FF 00     lock incq qword ptr [rax]; 4 bytes — atomic increment
    //   58              pop rax                  ; 1 byte — restore caller's RAX
    //
    // RAX must be preserved: the System V AMD64 ABI uses RAX at call sites
    // to pass the number of vector (XMM) registers used when calling
    // variadic functions. Clobbering RAX at function entry would corrupt
    // that convention, so the trampoline wraps the increment in a
    // `push rax` / `pop rax` pair. The sequence is self-balanced (one push,
    // one pop) and preserves stack alignment across the trampoline.
    //
    // Returns the byte offset (within the trampoline's start-of-code slice)
    // of the 8-byte `imm64` field; callers patch it with the live heap
    // counter pointer once the code buffer is mapped.
    let start = code.len();
    code.extend_from_slice(&[0x50]);
    code.extend_from_slice(&[0x48, 0xB8]);
    let imm64_offset = code.len();
    code.extend_from_slice(&[0u8; 8]);
    code.extend_from_slice(&[0xF0, 0x48, 0xFF, 0x00]);
    code.extend_from_slice(&[0x58]);
    debug_assert_eq!(code.len() - start, X86_64_PROFILE_TRAMPOLINE_BYTES);
    imm64_offset
}

#[cfg(target_arch = "x86_64")]
fn emit_veneer_stub(code: &mut Vec<u8>) {
    // JMP [RIP+0]: FF 25 00 00 00 00 ; .quad <addr>
    // Total: 14 bytes. Pad to 16 for alignment.
    code.extend_from_slice(&[0xFF, 0x25, 0x00, 0x00, 0x00, 0x00]); // JMP [RIP+0]
    code.extend_from_slice(&[0u8; 8]); // .quad addr
    code.extend_from_slice(&[0xCC, 0xCC]); // INT3 padding
}

/// Byte offset from veneer start to the embedded absolute address slot.
#[cfg(target_arch = "aarch64")]
const fn veneer_addr_offset() -> usize {
    8 // LDR(4) + BR(4), then 8-byte address
}

#[cfg(target_arch = "x86_64")]
const fn veneer_addr_offset() -> usize {
    6 // FF 25 00 00 00 00 (6 bytes), then 8-byte address
}

/// Patch an AArch64 Branch26 fixup (B/BL instruction, imm26 field).
#[cfg(target_arch = "aarch64")]
fn patch_branch26(code: &mut [u8], offset: u32, target: u64) -> Result<(), JitError> {
    let off = offset as usize;
    if off + 4 > code.len() {
        return Err(JitError::FixupOutOfBounds {
            offset,
            code_len: code.len(),
        });
    }
    let distance = target as i64 - offset as i64;
    if !(-AARCH64_BRANCH26_MAX..AARCH64_BRANCH26_MAX).contains(&distance) {
        return Err(JitError::BranchOutOfRange {
            offset,
            target,
            distance,
        });
    }
    let imm26 = ((distance >> 2) & 0x03FF_FFFF) as u32;
    let existing = u32::from_le_bytes([code[off], code[off + 1], code[off + 2], code[off + 3]]);
    code[off..off + 4].copy_from_slice(&((existing & 0xFC00_0000) | imm26).to_le_bytes());
    Ok(())
}

/// Patch an x86-64 rel32 fixup (CALL/JMP instruction, 4-byte displacement).
///
/// The `offset` is the byte position of the start of the CALL/JMP instruction.
/// For CALL (E8 xx xx xx xx), the displacement is at offset+1 and is relative
/// to the end of the instruction (offset+5). For JMP (E9), same layout.
/// For Jcc (0F 8x xx xx xx xx), displacement at offset+2, end at offset+6.
#[cfg(target_arch = "x86_64")]
fn patch_rel32(code: &mut [u8], offset: u32, target: u64) -> Result<(), JitError> {
    let off = offset as usize;
    // Jcc needs 6 bytes; CALL/JMP need 5. Check the max to avoid OOB panic.
    if off + 6 > code.len() {
        return Err(JitError::FixupOutOfBounds {
            offset,
            code_len: code.len(),
        });
    }
    // Determine instruction length from the opcode to locate the displacement.
    let (disp_off, inst_end) = match code[off] {
        0xE8 | 0xE9 => (off + 1, off + 5), // CALL rel32 / JMP rel32
        0x0F => (off + 2, off + 6),        // Jcc rel32 (0F 80+cc)
        _ => (off + 1, off + 5),           // Default: 5-byte near call/jmp
    };
    let distance = target as i64 - inst_end as i64;
    if distance < i32::MIN as i64 || distance > i32::MAX as i64 {
        return Err(JitError::BranchOutOfRange {
            offset,
            target,
            distance,
        });
    }
    code[disp_off..disp_off + 4].copy_from_slice(&(distance as i32).to_le_bytes());
    Ok(())
}

#[cfg(test)]
mod tests {
    // Test module intentionally exercises the deprecated `get_fn` /
    // `get_fn_ptr` APIs (issue #355) alongside the new bound versions.
    #![allow(deprecated)]
    use super::*;
    use crate::jit_contract::{
        AbiDescriptor, AbiValue, AbiValueKind, ArtifactChecksum, ArtifactContractError,
        ArtifactManifestV1, ArtifactSymbol, Endianness, InvalidationKey, JitArtifactKind,
        LayoutManifest, ProofPolicy, SymbolLookupContract, SymbolSignature, SymbolVisibility,
        TargetDescriptor, TargetOperatingSystem,
    };
    use crate::target::Target;
    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    use trust_cg_ir::function::{MachFunction, Signature, Type};
    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    use trust_cg_ir::inst::{AArch64Opcode, MachInst};
    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    use trust_cg_ir::operand::MachOperand;
    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    use trust_cg_ir::regs::X0;

    // Also compiled on x86_64: test_x86_compile_raw_rejects_untagged_aarch64_machir
    // feeds this AArch64-tagged function to the x86 JIT to check rejection.
    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    fn build_return_const_named(name: &str) -> MachFunction {
        let sig = Signature::new(vec![], vec![Type::I64]);
        let mut func = MachFunction::new(name.to_string(), sig);
        let entry = func.entry;

        let mov = MachInst::new(
            AArch64Opcode::Movz,
            vec![MachOperand::PReg(X0), MachOperand::Imm(42)],
        );
        let mov_id = func.push_inst(mov);
        func.append_inst(entry, mov_id);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let ret_id = func.push_inst(ret);
        func.append_inst(entry, ret_id);

        func
    }

    #[cfg(target_arch = "aarch64")]
    fn build_zero_instruction_named(name: &str) -> MachFunction {
        MachFunction::new(name.to_string(), Signature::new(vec![], vec![]))
    }

    #[cfg(target_arch = "aarch64")]
    fn assert_encoding_error_contains<T>(result: Result<T, JitError>, needle: &str) {
        match result {
            Err(JitError::Pipeline(PipelineError::Encoding(message))) => {
                assert!(
                    message.contains(needle),
                    "expected encoding error containing {needle:?}, got {message:?}"
                );
            }
            Err(other) => panic!("expected PipelineError::Encoding, got {other:?}"),
            Ok(_) => panic!("expected PipelineError::Encoding containing {needle:?}, got Ok"),
        }
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_block_profile_patch_registration_missing_cells_return_jit_errors() {
        let mut counter_patch_sites = Vec::new();
        let err = register_block_counter_patch_sites(
            "profiled",
            &HashMap::new(),
            &[(BlockId(7), 20)],
            128,
            &mut counter_patch_sites,
        )
        .expect_err("missing block counter must return a typed JIT error");
        match err {
            JitError::MissingBlockProfileCounter { function, block_id } => {
                assert_eq!(function, "profiled");
                assert_eq!(block_id, 7);
            }
            other => panic!("expected MissingBlockProfileCounter, got {other:?}"),
        }
        assert!(counter_patch_sites.is_empty());

        let mut counter_patch_sites = Vec::new();
        let mut tstate_patch_sites = Vec::new();
        let err = register_block_timing_patch_sites(
            "timed",
            &HashMap::new(),
            &[(BlockId(9), 92, 100)],
            256,
            &mut counter_patch_sites,
            &mut tstate_patch_sites,
        )
        .expect_err("missing block timing cell must return a typed JIT error");
        match err {
            JitError::MissingBlockTimingCell { function, block_id } => {
                assert_eq!(function, "timed");
                assert_eq!(block_id, 9);
            }
            other => panic!("expected MissingBlockTimingCell, got {other:?}"),
        }
        assert!(counter_patch_sites.is_empty());
        assert!(tstate_patch_sites.is_empty());
    }

    #[cfg(target_arch = "aarch64")]
    fn build_branch_to_unordered_block() -> (MachFunction, HashMap<BlockId, u32>, Vec<u8>) {
        let sig = Signature::new(vec![], vec![]);
        let mut func = MachFunction::new("bad_splice".to_string(), sig);
        let entry = func.entry;
        let target = func.create_block();

        let branch = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(target)]);
        let branch_id = func.push_inst(branch);
        func.append_inst(entry, branch_id);

        func.block_order = vec![entry];
        let offsets = HashMap::from([(entry, 0), (target, 4)]);
        let body = (0x1400_0001u32).to_le_bytes().to_vec();
        (func, offsets, body)
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_block_splice_missing_byte_offset_returns_encoding_error() {
        let func = build_return_const_named("missing_offset");
        let offsets = HashMap::new();
        let mut fixups = Vec::new();

        assert_encoding_error_contains(
            splice_block_trampolines_aarch64(&func, &[], &offsets, fixups.as_mut_slice()),
            "missing byte offset",
        );

        assert_encoding_error_contains(
            splice_block_trampolines_with_timing_aarch64(
                &func,
                &[],
                &offsets,
                fixups.as_mut_slice(),
            ),
            "missing byte offset",
        );
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_block_splice_missing_target_layout_returns_encoding_error() {
        let (func, offsets, body) = build_branch_to_unordered_block();

        let mut fixups = Vec::new();
        assert_encoding_error_contains(
            splice_block_trampolines_aarch64(&func, &body, &offsets, fixups.as_mut_slice()),
            "branch target BlockId(1) has no post-splice offset",
        );

        let mut fixups = Vec::new();
        assert_encoding_error_contains(
            splice_block_trampolines_with_timing_aarch64(
                &func,
                &body,
                &offsets,
                fixups.as_mut_slice(),
            ),
            "branch target BlockId(1) has no post-splice offset",
        );
    }

    // -- AArch64 patch tests ---------------------------------------------------

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_patch_branch26_forward() {
        let mut code = vec![0; 20];
        code[0..4].copy_from_slice(&0x9400_0000u32.to_le_bytes());
        patch_branch26(&mut code, 0, 16).unwrap();
        let patched = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
        assert_eq!(patched, 0x9400_0004);
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_patch_branch26_backward() {
        let mut code = vec![0; 20];
        code[8..12].copy_from_slice(&0x1400_0000u32.to_le_bytes());
        patch_branch26(&mut code, 8, 0).unwrap();
        let patched = u32::from_le_bytes([code[8], code[9], code[10], code[11]]);
        assert_eq!(patched, 0x1400_0000 | ((-2i32 as u32) & 0x03FF_FFFF));
    }

    // -- x86-64 patch tests ----------------------------------------------------

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn test_patch_rel32_call_forward() {
        // CALL rel32 at offset 0, target at offset 20.
        // Instruction is 5 bytes (E8 + 4-byte disp), so disp = 20 - 5 = 15.
        let mut code = vec![0u8; 32];
        code[0] = 0xE8; // CALL opcode
        patch_rel32(&mut code, 0, 20).unwrap();
        let disp = i32::from_le_bytes([code[1], code[2], code[3], code[4]]);
        assert_eq!(disp, 15);
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn test_patch_rel32_jmp_backward() {
        // JMP rel32 at offset 10, target at offset 0.
        // Instruction is 5 bytes, so disp = 0 - 15 = -15.
        let mut code = vec![0u8; 32];
        code[10] = 0xE9; // JMP opcode
        patch_rel32(&mut code, 10, 0).unwrap();
        let disp = i32::from_le_bytes([code[11], code[12], code[13], code[14]]);
        assert_eq!(disp, -15);
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn test_patch_rel32_jcc() {
        // Jcc rel32 at offset 0, target at offset 20.
        // Instruction is 6 bytes (0F 8x + 4-byte disp), so disp = 20 - 6 = 14.
        let mut code = vec![0u8; 32];
        code[0] = 0x0F;
        code[1] = 0x84; // JE rel32
        patch_rel32(&mut code, 0, 20).unwrap();
        let disp = i32::from_le_bytes([code[2], code[3], code[4], code[5]]);
        assert_eq!(disp, 14);
    }

    // -- Architecture-independent tests ----------------------------------------

    #[test]
    fn test_raw_mmap_roundtrip() {
        unsafe {
            let size = sys::page_align(1);
            let ptr = sys::mmap(size, sys::RW).expect("mmap failed");
            *ptr = 42;
            assert_eq!(*ptr, 42);
            sys::munmap(ptr, size);
        }
    }

    #[test]
    fn test_page_align() {
        assert_eq!(sys::page_align(0), 0);
        assert_eq!(sys::page_align(1), sys::PAGE_SIZE);
        assert_eq!(sys::page_align(sys::PAGE_SIZE), sys::PAGE_SIZE);
        assert_eq!(sys::page_align(sys::PAGE_SIZE + 1), sys::PAGE_SIZE * 2);
    }

    #[test]
    fn test_veneer_addr_offset() {
        #[cfg(target_arch = "aarch64")]
        assert_eq!(veneer_addr_offset(), 8);
        #[cfg(target_arch = "x86_64")]
        assert_eq!(veneer_addr_offset(), 6);
    }

    #[test]
    fn test_emit_veneer_stub_size() {
        let mut code = Vec::new();
        emit_veneer_stub(&mut code);
        // Both architectures: 16 bytes (AArch64: 4+4+8, x86-64: 6+8+2)
        assert_eq!(code.len(), 16);
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_aarch64_profile_literal_patch_offsets_use_unaligned_writes() {
        let mut entry_counter = Vec::new();
        let entry_counter_off = emit_profile_trampoline_aarch64(&mut entry_counter);
        assert_eq!(entry_counter.len(), AARCH64_PROFILE_TRAMPOLINE_BYTES);
        assert_eq!(entry_counter_off, 28);

        let mut timing = Vec::new();
        let (timing_counter_off, timing_state_off) =
            emit_profile_trampoline_with_timing_aarch64(&mut timing);
        assert_eq!(timing.len(), AARCH64_PROFILE_TRAMPOLINE_TIMING_BYTES);
        let timing_word = |offset: usize| {
            u32::from_le_bytes([
                timing[offset],
                timing[offset + 1],
                timing[offset + 2],
                timing[offset + 3],
            ])
        };
        assert_eq!(timing_word(8), 0xA9BF_47F0, "save X16/X17");
        assert_eq!(timing_word(12), 0x5800_0290, "counter literal load");
        assert_eq!(timing_word(36), 0x5800_0209, "timing-state literal load");
        assert_eq!(timing_word(84), 0xA8C1_47F0, "restore X16/X17");
        assert_eq!(timing_word(88), 0x1400_0005, "branch over literals");
        assert_eq!(timing_counter_off, 92);
        assert_eq!(timing_state_off, 100);

        let mut scratch = [0u8; AARCH64_PROFILE_TRAMPOLINE_TIMING_BYTES];
        for (offset, value) in [
            (entry_counter_off, 0x0102_0304_0506_0708),
            (timing_counter_off, 0x1112_1314_1516_1718),
            (timing_state_off, 0x2122_2324_2526_2728),
        ] {
            assert_ne!(
                offset % std::mem::align_of::<u64>(),
                0,
                "regression requires an unaligned AArch64 literal slot"
            );
            unsafe {
                write_u64_literal_unaligned(scratch.as_mut_ptr(), offset, value);
            }
            assert_eq!(
                &scratch[offset..offset + std::mem::size_of::<u64>()],
                &value.to_le_bytes()
            );
        }
    }

    #[test]
    fn test_profile_hook_mode_default_is_none() {
        assert_eq!(JitConfig::default().profile_hooks, ProfileHookMode::None);
        assert!(
            !JitConfig::default().emit_entry_counters,
            "entry counters must remain opt-in"
        );
    }

    #[test]
    fn test_emit_entry_counters_upgrades_profile_hooks_when_none() {
        let jit = JitCompiler::new(JitConfig {
            emit_entry_counters: true,
            ..JitConfig::default()
        });
        assert_eq!(jit.profile_hooks, ProfileHookMode::CallCounts);
    }

    #[test]
    fn test_explicit_profile_hooks_win_over_emit_entry_counters() {
        let jit = JitCompiler::new(JitConfig {
            profile_hooks: ProfileHookMode::CallCountsAndTiming,
            emit_entry_counters: true,
            ..JitConfig::default()
        });
        assert_eq!(jit.profile_hooks, ProfileHookMode::CallCountsAndTiming);
    }

    #[test]
    fn test_profile_hook_mode_phase2_stubs_classified() {
        // #396 Phase 2: these variants are API-reserved but not
        // implemented in the trampoline emitter. They must all be
        // classified as stubs so compile_raw rejects them with a clear
        // diagnostic rather than silently producing unhooked code.
        //
        // BlockCounts was demoted out of the stub set in #364 Phase 2
        // and BlockCountsAndTiming was demoted in #364 Phase 3 — both
        // now have real trampoline landings exercised by
        // `tests/jit_block_counters.rs` and
        // `tests/jit_block_counters_and_timing.rs`.
        for mode in [
            ProfileHookMode::EdgeCounts,
            ProfileHookMode::BlockFrequency,
            ProfileHookMode::LoopHeads,
        ] {
            assert!(
                profile_hooks_is_phase2_stub(mode),
                "mode {:?} must be classified as a Phase 2 stub",
                mode
            );
            assert!(
                !profile_hooks_enable_counters(mode),
                "mode {:?} must NOT claim to enable function-entry counters \
                 until Phase 2 trampoline lands",
                mode
            );
        }
        // And verify the currently-implemented modes are NOT classified
        // as stubs (so the early-reject does not fire on the happy path).
        for mode in [
            ProfileHookMode::None,
            ProfileHookMode::CallCounts,
            ProfileHookMode::CallCountsAndTiming,
            ProfileHookMode::BlockCounts,
            ProfileHookMode::BlockCountsAndTiming,
        ] {
            assert!(
                !profile_hooks_is_phase2_stub(mode),
                "mode {:?} must NOT be classified as a Phase 2 stub",
                mode
            );
        }
    }

    #[test]
    fn test_profile_hook_mode_block_counts_enables_block_counters() {
        // #364: BlockCounts is the one mode that turns on
        // `profile_hooks_enable_block_counters`. All other modes must
        // remain false here so the BlockCounts-specific splice path is
        // only taken for that exact variant.
        assert!(profile_hooks_enable_block_counters(
            ProfileHookMode::BlockCounts
        ));
        for mode in [
            ProfileHookMode::None,
            ProfileHookMode::CallCounts,
            ProfileHookMode::CallCountsAndTiming,
            ProfileHookMode::BlockCountsAndTiming,
            ProfileHookMode::EdgeCounts,
            ProfileHookMode::BlockFrequency,
            ProfileHookMode::LoopHeads,
        ] {
            assert!(
                !profile_hooks_enable_block_counters(mode),
                "mode {:?} must NOT enable per-block counters",
                mode
            );
        }
    }

    #[test]
    fn test_profile_hook_counter_classifiers_are_disjoint() {
        // #496: a mode must never select both the per-function entry
        // trampoline and a block-entry trampoline family. Otherwise the
        // entry block would increment twice.
        for mode in [
            ProfileHookMode::None,
            ProfileHookMode::CallCounts,
            ProfileHookMode::CallCountsAndTiming,
            ProfileHookMode::BlockCounts,
            ProfileHookMode::BlockCountsAndTiming,
            ProfileHookMode::EdgeCounts,
            ProfileHookMode::BlockFrequency,
            ProfileHookMode::LoopHeads,
        ] {
            assert!(
                profile_hooks_counter_classifiers_are_disjoint(mode),
                "mode {:?} must not enable overlapping counter classifiers",
                mode
            );
        }
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_profile_hook_mode_remaining_stubs_rejected() {
        // The still-stubbed Phase 2 variants must continue to return
        // `ProfileHookModeUnimplemented` — not silently succeed, not
        // return `ProfileHooksUnsupported` (which is specifically the
        // wrong-architecture error).
        //
        // BlockCountsAndTiming moved out of this list in #364 Phase 3
        // once its timing-aware trampoline landed; see
        // `tests/jit_block_counters_and_timing.rs` for happy-path
        // coverage.
        for mode in [
            ProfileHookMode::EdgeCounts,
            ProfileHookMode::BlockFrequency,
            ProfileHookMode::LoopHeads,
        ] {
            let jit = JitCompiler::new(JitConfig {
                profile_hooks: mode,
                ..JitConfig::default()
            });
            let ext: HashMap<String, *const u8> = HashMap::new();
            match jit.compile_raw(&[], &ext) {
                Err(JitError::ProfileHookModeUnimplemented { mode: got }) => {
                    assert_eq!(got, mode);
                }
                Err(other) => panic!(
                    "expected ProfileHookModeUnimplemented for {:?}, got error {:?}",
                    mode, other
                ),
                Ok(_) => panic!(
                    "expected ProfileHookModeUnimplemented for {:?}, got Ok(ExecutableBuffer)",
                    mode
                ),
            }
        }
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn test_x86_compile_raw_rejects_call_counts_and_timing() {
        let jit = JitCompiler::new(JitConfig {
            profile_hooks: ProfileHookMode::CallCountsAndTiming,
            ..JitConfig::default()
        });
        let ext: HashMap<String, *const u8> = HashMap::new();

        match jit.compile_raw(&[], &ext) {
            Err(JitError::ProfileHooksUnsupported) => {}
            Err(other) => panic!("expected ProfileHooksUnsupported, got {other:?}"),
            Ok(_) => panic!("x86-64 CallCountsAndTiming must not silently omit timing data"),
        }
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn test_x86_compile_raw_rejects_untagged_aarch64_machir() {
        let jit = JitCompiler::new(JitConfig::default());
        let ext: HashMap<String, *const u8> = HashMap::new();

        match jit.compile_raw(&[build_return_const_named("raw_answer")], &ext) {
            Err(JitError::RawJitTargetMismatch {
                function,
                host_arch,
            }) => {
                assert_eq!(function, "raw_answer");
                assert_eq!(host_arch, "x86_64");
            }
            Err(other) => panic!("expected RawJitTargetMismatch, got {other:?}"),
            Ok(_) => panic!("x86-64 raw AArch64 MachIR must not publish executable code"),
        }
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_compile_raw_rejects_empty_function_list_before_mmap() {
        let jit = JitCompiler::new(JitConfig::default());
        let ext: HashMap<String, *const u8> = HashMap::new();

        match jit.compile_raw(&[], &ext) {
            Err(JitError::EmptyExecutableBuffer { function_count }) => {
                assert_eq!(function_count, 0);
            }
            Err(other) => panic!("expected EmptyExecutableBuffer, got {other:?}"),
            Ok(buf) => panic!(
                "empty compile_raw input must not publish executable buffer: allocated_size={}",
                buf.allocated_size()
            ),
        }
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_compile_raw_rejects_zero_instruction_function_before_mmap() {
        let jit = JitCompiler::new(JitConfig::default());
        let ext: HashMap<String, *const u8> = HashMap::new();

        match jit.compile_raw(&[build_zero_instruction_named("empty")], &ext) {
            Err(JitError::EmptyExecutableBuffer { function_count }) => {
                assert_eq!(function_count, 1);
            }
            Err(other) => panic!("expected EmptyExecutableBuffer, got {other:?}"),
            Ok(buf) => panic!(
                "zero-instruction function must not publish executable buffer: allocated_size={}",
                buf.allocated_size()
            ),
        }
    }

    #[cfg(all(target_arch = "x86_64", target_os = "windows"))]
    #[test]
    fn windows_jit_unwind_info_encodes_supported_rbp_frames() {
        let no_alloc =
            build_windows_x64_unwind_info("no_alloc", &[0x55, 0x48, 0x89, 0xE5, 0xC3], false)
                .expect("supported RBP frame should encode");
        assert_eq!(
            no_alloc,
            vec![0x01, 0x04, 0x02, 0x05, 0x04, 0x03, 0x01, 0x50]
        );

        let mut with_prefix = vec![0x49, 0xBA];
        with_prefix.extend_from_slice(&[0u8; 8]);
        with_prefix.extend_from_slice(&[
            0xF0, 0x49, 0xFF, 0x02, 0x55, 0x48, 0x89, 0xE5, 0x48, 0x81, 0xEC, 0x20, 0x00, 0x00,
            0x00, 0xC3,
        ]);
        let encoded = build_windows_x64_unwind_info("prefixed", &with_prefix, false)
            .expect("stack-neutral profile prefix should encode");
        assert_eq!(
            encoded,
            vec![
                0x01, 0x19, 0x03, 0x05, 0x19, 0x32, 0x12, 0x03, 0x0F, 0x50, 0x00, 0x00,
            ]
        );

        let with_imm8_alloc = build_windows_x64_unwind_info(
            "imm8_alloc",
            &[0x55, 0x48, 0x89, 0xE5, 0x48, 0x83, 0xEC, 0x20, 0xC3],
            false,
        )
        .expect("short-form stack allocation should encode");
        assert_eq!(
            with_imm8_alloc,
            vec![
                0x01, 0x08, 0x03, 0x05, 0x08, 0x32, 0x04, 0x03, 0x01, 0x50, 0x00, 0x00,
            ]
        );

        let with_gprs = build_windows_x64_unwind_info(
            "gprs",
            &[
                0x55, 0x48, 0x89, 0xE5, 0x53, 0x41, 0x54, 0x48, 0x81, 0xEC, 0x20, 0x00, 0x00, 0x00,
                0xC3,
            ],
            false,
        )
        .expect("callee-saved GPR pushes should encode");
        assert_eq!(
            with_gprs,
            vec![
                0x01, 0x0E, 0x05, 0x05, 0x0E, 0x32, 0x07, 0xC0, 0x05, 0x30, 0x04, 0x03, 0x01, 0x50,
                0x00, 0x00,
            ]
        );

        let with_xmms = build_windows_x64_unwind_info(
            "xmms",
            &[
                0x55, 0x48, 0x89, 0xE5, 0x48, 0x81, 0xEC, 0x20, 0x00, 0x00, 0x00, 0xF3, 0x0F, 0x7F,
                0x75, 0xF0, 0xF3, 0x44, 0x0F, 0x7F, 0x7D, 0xE0, 0xC3,
            ],
            false,
        )
        .expect("static callee-saved XMM saves should encode");
        assert_eq!(
            with_xmms,
            vec![
                0x01, 0x16, 0x06, 0x00, 0x16, 0xF8, 0x00, 0x00, 0x10, 0x68, 0x01, 0x00, 0x0B, 0x32,
                0x01, 0x50,
            ]
        );

        let with_movss_body = build_windows_x64_unwind_info(
            "movss_body",
            &[
                0x55, 0x48, 0x89, 0xE5, 0x48, 0x81, 0xEC, 0x20, 0x00, 0x00, 0x00, 0xF3, 0x0F, 0x10,
                0x05, 0x00, 0x00, 0x00, 0x00, 0xC3,
            ],
            false,
        )
        .expect("body MOVSS after the prologue should not be parsed as an XMM save");
        assert_eq!(
            with_movss_body,
            vec![
                0x01, 0x0B, 0x03, 0x05, 0x0B, 0x32, 0x04, 0x03, 0x01, 0x50, 0x00, 0x00,
            ]
        );
    }

    #[cfg(all(target_arch = "x86_64", target_os = "windows"))]
    fn expect_windows_unwind_unsupported(
        code: &[u8],
        has_dynamic_stack_alloc: bool,
        reason_fragment: &str,
    ) {
        match build_windows_x64_unwind_info("bad", code, has_dynamic_stack_alloc) {
            Err(JitError::WindowsUnwindUnsupported { function, reason }) => {
                assert_eq!(function, "bad");
                assert!(
                    reason.contains(reason_fragment),
                    "expected reason containing {reason_fragment:?}, got {reason:?}"
                );
            }
            Err(other) => panic!("expected WindowsUnwindUnsupported, got {other:?}"),
            Ok(encoded) => panic!("unsupported Windows unwind prologue encoded as {encoded:?}"),
        }
    }

    #[cfg(all(target_arch = "x86_64", target_os = "windows"))]
    #[test]
    fn windows_jit_unwind_rejects_unsupported_prologue_shapes() {
        expect_windows_unwind_unsupported(&[0xC3], false, "expected supported prologue");
        expect_windows_unwind_unsupported(
            &[0x55, 0x48, 0x89, 0xE5, 0x48, 0x83, 0xEC],
            false,
            "truncated `sub rsp, imm8`",
        );
        expect_windows_unwind_unsupported(
            &[0x55, 0x48, 0x89, 0xE5, 0x50, 0xC3],
            false,
            "unsupported GPR push",
        );
        expect_windows_unwind_unsupported(
            &[
                0x55, 0x48, 0x89, 0xE5, 0x48, 0x81, 0xEC, 0x20, 0x00, 0x00, 0x00, 0xF3, 0x0F, 0x7F,
                0x6D, 0xF0, 0xC3,
            ],
            false,
            "unsupported XMM save",
        );
        expect_windows_unwind_unsupported(
            &[
                0x55, 0x48, 0x89, 0xE5, 0x48, 0x81, 0xEC, 0x20, 0x00, 0x00, 0x00, 0xF3, 0x44, 0x0F,
                0x7F, 0x7D, 0xE0, 0xC3,
            ],
            true,
            "dynamic stack allocation",
        );
    }

    #[cfg(all(target_arch = "x86_64", target_os = "windows"))]
    fn expect_windows_unwind_publish_rejects(
        code: &[u8],
        has_dynamic_stack_alloc: bool,
        reason_fragment: &str,
    ) {
        let mut symbol_offsets = HashMap::new();
        symbol_offsets.insert("bad".to_string(), 0);
        let result = publish_raw_executable_buffer_with_profile_data(
            code,
            vec!["bad".to_string()],
            symbol_offsets,
            vec![("bad".to_string(), 0..code.len() as u64)],
            HashMap::new(),
            Vec::new(),
            vec![
                WindowsJitUnwindFunction::new("bad", 0, code.len() as u64)
                    .with_dynamic_stack_alloc(has_dynamic_stack_alloc),
            ],
        );

        match result {
            Err(JitError::WindowsUnwindUnsupported { function, reason }) => {
                assert_eq!(function, "bad");
                assert!(
                    reason.contains(reason_fragment),
                    "unexpected reason: {reason}"
                );
            }
            Err(other) => panic!("expected WindowsUnwindUnsupported, got {other:?}"),
            Ok(buf) => panic!(
                "unsupported Windows unwind prologue must fail before publishing: allocated_size={}",
                buf.allocated_size()
            ),
        }
    }

    #[cfg(all(target_arch = "x86_64", target_os = "windows"))]
    #[test]
    fn windows_jit_unwind_rejects_unsupported_prologue_before_publish() {
        expect_windows_unwind_publish_rejects(&[0xC3], false, "expected supported prologue");
        expect_windows_unwind_publish_rejects(
            &[0x55, 0x48, 0x89, 0xE5, 0x48, 0x83, 0xEC],
            false,
            "truncated `sub rsp, imm8`",
        );
        expect_windows_unwind_publish_rejects(
            &[
                0x55, 0x48, 0x89, 0xE5, 0x48, 0x81, 0xEC, 0x20, 0x00, 0x00, 0x00, 0xF3, 0x44, 0x0F,
                0x7F, 0x7D, 0xE0, 0xC3,
            ],
            true,
            "dynamic stack allocation",
        );
    }

    #[cfg(all(target_arch = "x86_64", target_os = "windows"))]
    #[test]
    fn windows_jit_unwind_xdata_stays_outside_code_boundary() {
        let code = [0x55, 0x48, 0x89, 0xE5, 0x5D, 0xC3];
        let mut symbol_offsets = HashMap::new();
        symbol_offsets.insert("framed".to_string(), 0);
        let buf = publish_raw_executable_buffer_with_profile_data(
            &code,
            vec!["framed".to_string()],
            symbol_offsets,
            vec![("framed".to_string(), 0..code.len() as u64)],
            HashMap::new(),
            Vec::new(),
            vec![WindowsJitUnwindFunction::new(
                "framed",
                0,
                code.len() as u64,
            )],
        )
        .expect("supported Windows unwind metadata should publish");

        assert_eq!(buf.code_len, code.len());
        assert!(buf.published_len > buf.code_len);
        assert_eq!(buf.allocated_size(), sys::page_align(buf.published_len));
        assert!(buf.code_offset_for_host_pc(buf.memory as u64).is_some());
        assert_eq!(
            buf.code_offset_for_host_pc((buf.memory as u64) + buf.code_len as u64),
            None,
            "appended UNWIND_INFO bytes must not be classified as executable code"
        );
        assert_eq!(buf.code_bytes(), &code);
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_profile_trampoline_byte_layout() {
        let mut code = Vec::new();
        let literal_slot_offset = emit_profile_trampoline_aarch64(&mut code);

        assert_eq!(literal_slot_offset, 28);
        assert_eq!(code.len(), 36);
        assert_eq!(
            u32::from_le_bytes([code[0], code[1], code[2], code[3]]),
            0xA9BF_47F0
        );
        assert_eq!(
            u32::from_le_bytes([code[4], code[5], code[6], code[7]]),
            0x5800_00D0
        );
        assert_eq!(
            u32::from_le_bytes([code[8], code[9], code[10], code[11]]),
            0xF940_0211
        );
        assert_eq!(
            u32::from_le_bytes([code[12], code[13], code[14], code[15]]),
            0x9100_0631
        );
        assert_eq!(
            u32::from_le_bytes([code[16], code[17], code[18], code[19]]),
            0xF900_0211
        );
        assert_eq!(
            u32::from_le_bytes([code[20], code[21], code[22], code[23]]),
            0xA8C1_47F0
        );
        assert_eq!(
            u32::from_le_bytes([code[24], code[25], code[26], code[27]]),
            0x1400_0003
        );
        assert_eq!(&code[28..36], &[0u8; 8]);
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn test_profile_trampoline_x86_64_byte_layout() {
        // x86-64 entry-counter trampoline (see emit_profile_trampoline_x86_64).
        //
        //   offset 0  : 50                     push rax
        //   offset 1..=2  : 48 B8              movabs rax, imm64 opcode
        //   offset 3..=10 : imm64 placeholder  (patched to heap counter addr)
        //   offset 11..=14: F0 48 FF 00        lock incq qword ptr [rax]
        //   offset 15 : 58                     pop rax
        let mut code = Vec::new();
        let imm64_offset = emit_profile_trampoline_x86_64(&mut code);

        assert_eq!(imm64_offset, 3, "imm64 slot follows push rax + REX/mov");
        assert_eq!(code.len(), 16, "trampoline must be exactly 16 bytes");
        assert_eq!(code[0], 0x50, "push rax");
        assert_eq!(&code[1..3], &[0x48, 0xB8], "movabs rax, imm64 opcode");
        assert_eq!(&code[3..11], &[0u8; 8], "imm64 starts zeroed until patch");
        assert_eq!(
            &code[11..15],
            &[0xF0, 0x48, 0xFF, 0x00],
            "lock incq qword ptr [rax]"
        );
        assert_eq!(code[15], 0x58, "pop rax");
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_profile_hooks_none_has_no_trampoline() {
        let func = build_return_const_named("f");
        let (bytes, fixups) = encode_function_with_fixups(&func).expect("encode should succeed");
        assert!(
            fixups.is_empty(),
            "return-const fixture should encode without fixups"
        );

        let jit = JitCompiler::new(JitConfig::default());
        let ext: HashMap<String, *const u8> = HashMap::new();
        let buf = jit
            .compile_raw(&[func], &ext)
            .expect("compile_raw should succeed");

        let ptr = buf
            .get_fn_ptr_bound("f")
            .expect("function pointer should exist")
            .as_ptr();
        let actual = unsafe { std::slice::from_raw_parts(ptr, bytes.len()) };
        assert_eq!(actual, bytes.as_slice());
        assert!(buf.get_profile("f").is_none());
        assert_eq!(buf.profiles().count(), 0);
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_jit_call_counter_increments() {
        let jit = JitCompiler::new(JitConfig {
            profile_hooks: ProfileHookMode::CallCounts,
            ..JitConfig::default()
        });
        let ext: HashMap<String, *const u8> = HashMap::new();
        let buf = jit
            .compile_raw(&[build_return_const_named("f")], &ext)
            .expect("compile_raw should succeed");

        let f: extern "C" fn() -> u64 = unsafe {
            buf.get_fn_bound("f")
                .expect("typed function pointer should exist")
                .into_inner()
        };
        for _ in 0..100 {
            assert_eq!(f(), 42);
        }

        let stats = buf.get_profile("f").expect("profile should exist");
        assert_eq!(stats.call_count, 100);

        let collected: Vec<(&str, ProfileStats)> = buf.profiles().collect();
        assert_eq!(collected.len(), 1);
        assert_eq!(collected[0].0, "f");
        assert_eq!(collected[0].1.call_count, 100);
    }

    #[cfg(unix)]
    #[test]
    fn test_lookup_process_symbol_libc_malloc() {
        // malloc is in libSystem on macOS, libc.so.6 on Linux — always resolvable
        // in any Rust binary since the allocator links libc.
        let ptr = lookup_process_symbol("malloc");
        assert!(
            ptr.is_some(),
            "malloc should be resolvable via dlsym(RTLD_DEFAULT)"
        );
        assert!(!ptr.unwrap().is_null());
    }

    #[cfg(unix)]
    #[test]
    fn test_lookup_process_symbol_missing_returns_none() {
        let ptr = lookup_process_symbol("definitely_not_a_real_symbol_qwertyuiop_12345");
        assert!(ptr.is_none());
    }

    #[cfg(unix)]
    #[test]
    fn test_lookup_process_symbol_interior_nul_returns_none() {
        // CString::new rejects interior NULs.
        let ptr = lookup_process_symbol("mal\0loc");
        assert!(ptr.is_none());
    }

    #[cfg(windows)]
    #[test]
    fn test_lookup_process_symbol_windows_kernel32() {
        let ptr = lookup_process_symbol("GetCurrentProcessId");
        assert!(
            ptr.is_some(),
            "GetCurrentProcessId should be resolvable from loaded Windows modules"
        );
    }

    #[cfg(windows)]
    #[test]
    fn test_lookup_process_symbol_windows_missing_returns_none() {
        let ptr = lookup_process_symbol("definitely_not_a_real_symbol_qwertyuiop_12345");
        assert!(ptr.is_none());
    }

    #[cfg(windows)]
    #[test]
    fn test_lookup_process_symbol_windows_interior_nul_returns_none() {
        let ptr = lookup_process_symbol("Get\0CurrentProcessId");
        assert!(ptr.is_none());
    }

    #[cfg(unix)]
    #[test]
    fn test_extern_symbols_preferred_over_dlsym() {
        // If caller supplies an explicit pointer for "malloc", compile_raw's
        // resolution must use the supplied pointer rather than dlsym'd one.
        // We test the helper directly since building a full compile_raw test
        // here would be heavy; use `resolve_extern` helper.
        let mut map: HashMap<String, *const u8> = HashMap::new();
        let fake_ptr: *const u8 = 0xdead_beef_usize as *const u8;
        map.insert("malloc".to_string(), fake_ptr);
        let resolved = resolve_extern("malloc", &map);
        assert_eq!(
            resolved,
            Some(fake_ptr),
            "extern_symbols must override dlsym"
        );
    }

    #[test]
    fn test_ensure_jit_execute_mode_is_callable() {
        ensure_jit_execute_mode();
    }

    #[test]
    fn test_mprotect_rw_then_rx() {
        unsafe {
            let size = sys::page_align(64);
            let ptr = sys::mmap(size, sys::RW).expect("mmap failed");
            // Write a pattern
            for i in 0..64 {
                *ptr.add(i) = i as u8;
            }
            // Switch to RX
            sys::mprotect(ptr, size, sys::RX).expect("mprotect failed");
            // Verify data is still readable
            assert_eq!(*ptr, 0);
            assert_eq!(*ptr.add(63), 63);
            sys::munmap(ptr, size);
        }
    }

    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    #[test]
    fn test_map_jit_execute_mode_denies_writes_after_publish() {
        const CHILD_ENV: &str = "TRUST_CG_MAP_JIT_WRITE_PROTECT_CHILD";
        const WRITE_SUCCEEDED_EXIT: i32 = 77;

        if std::env::var_os(CHILD_ENV).is_some() {
            unsafe {
                let size = sys::page_align(64);
                let ptr = sys::mmap(size, sys::RW).expect("mmap failed");
                let jit_write_guard = sys::JitWriteGuard::enter();
                std::ptr::write_volatile(ptr, 0x2a);
                sys::mprotect(ptr, size, sys::RX).expect("mprotect failed");
                drop(jit_write_guard);

                // This must fault when pthread JIT write protection is active:
                // after publishing, the current thread may execute MAP_JIT
                // pages but may not write them.
                std::ptr::write_volatile(ptr, 0x7f);
                sys::munmap(ptr, size);
            }
            std::process::exit(WRITE_SUCCEEDED_EXIT);
        }

        if !sys::jit_write_protect_supported() {
            return;
        }

        let current_exe = std::env::current_exe().expect("current test binary");
        let output = std::process::Command::new(current_exe)
            .arg("test_map_jit_execute_mode_denies_writes_after_publish")
            .arg("--nocapture")
            .env(CHILD_ENV, "1")
            .output()
            .expect("run MAP_JIT write-protect child");

        use std::os::unix::process::ExitStatusExt;

        let signal = output.status.signal();
        assert!(
            matches!(signal, Some(10 | 11)),
            "child should die with SIGBUS/SIGSEGV after writing a published MAP_JIT page; \
             status={:?}, signal={:?}, stdout:\n{}\nstderr:\n{}",
            output.status,
            signal,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    #[test]
    fn test_callable_lookup_restores_current_thread_execute_mode() {
        const CHILD_ENV: &str = "TRUST_CG_MAP_JIT_LOOKUP_EXEC_MODE_CHILD";

        if std::env::var_os(CHILD_ENV).is_some() {
            if !sys::jit_write_protect_supported() {
                return;
            }

            let jit = JitCompiler::new(JitConfig::default());
            let ext: HashMap<String, *const u8> = HashMap::new();
            let buf = jit
                .compile_raw(&[build_return_const_named("f")], &ext)
                .expect("compile_raw should publish executable code");
            assert_eq!(
                buf.publication_contract(),
                JitPublicationContract {
                    map_jit: true,
                    write_protect_supported: true,
                    published_rx: true,
                }
            );

            unsafe {
                // Put this thread back into MAP_JIT write mode. Lookup must
                // restore execute mode before handing back the callable.
                sys::set_jit_write_protect(false);
            }
            let bound_f: extern "C" fn() -> u64 = unsafe {
                buf.get_fn_bound("f")
                    .expect("typed function pointer should exist")
                    .into_inner()
            };
            assert_eq!(bound_f(), 42);

            unsafe {
                sys::set_jit_write_protect(false);
            }
            let legacy_f: extern "C" fn() -> u64 = unsafe {
                buf.get_fn("f")
                    .expect("legacy typed function pointer should exist")
            };
            assert_eq!(legacy_f(), 42);

            let signature = contract_void_to_i64_signature();
            let manifest = manifest_with_contract_symbol_and_signature("f", signature.clone());
            let contract = symbol_lookup_contract_for_with_signature(&manifest, "f", signature);

            unsafe {
                sys::set_jit_write_protect(false);
            }
            let contract_f: extern "C" fn() -> u64 = unsafe {
                buf.get_contract_symbol_bound::<extern "C" fn() -> u64>(&manifest, &contract)
                    .expect("contract symbol should bind")
                    .into_fn()
            };
            assert_eq!(contract_f(), 42);

            // `compile_raw` has no compiler-derived v2 installed-payload
            // binding, so this MAP_JIT mechanism test must remain on the
            // documented direct-JIT/profile-only bridge. Product contract
            // lookup is intentionally unavailable for this artifact.
            let replay = buf.replay_report_metadata();
            let installed =
                crate::compile_service::InstalledArtifact::from_executable_buffer_replay_metadata(
                    std::sync::Arc::new(buf),
                    crate::compile_service::CompileGeneration::new(1),
                    replay,
                );
            assert_eq!(
                installed.metadata.disposition,
                crate::compile_service::ArtifactInstallDisposition::ProfileOnly,
            );

            unsafe {
                sys::set_jit_write_protect(false);
            }
            let installed_ptr = installed
                .entrypoint_ptr("f")
                .expect("installed raw entrypoint pointer should exist");
            let installed_raw = installed_ptr.as_ptr();
            let installed_ptr_f: extern "C" fn() -> u64 =
                unsafe { std::mem::transmute_copy(&installed_raw) };
            assert_eq!(installed_ptr_f(), 42);

            unsafe {
                sys::set_jit_write_protect(false);
            }
            let installed_entry_f: extern "C" fn() -> u64 = unsafe {
                installed
                    .entrypoint("f")
                    .expect("installed typed entrypoint should exist")
                    .into_inner()
            };
            assert_eq!(installed_entry_f(), 42);

            unsafe {
                sys::set_jit_write_protect(true);
            }
            return;
        }

        if !sys::jit_write_protect_supported() {
            return;
        }

        let current_exe = std::env::current_exe().expect("current test binary");
        let output = std::process::Command::new(current_exe)
            .arg("jit::tests::test_callable_lookup_restores_current_thread_execute_mode")
            .arg("--exact")
            .arg("--nocapture")
            .env(CHILD_ENV, "1")
            .output()
            .expect("run MAP_JIT lookup execute-mode child");

        assert!(
            output.status.success(),
            "child should execute after lookup restores MAP_JIT execute mode; status={:?}\nstdout:\n{}\nstderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
    }

    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    #[test]
    fn test_ensure_published_executable_recovers_after_rw_protection_drift() {
        const CHILD_ENV: &str = "TRUST_CG_MAP_JIT_REASSERT_RX_CHILD";

        if std::env::var_os(CHILD_ENV).is_some() {
            if !sys::jit_write_protect_supported() {
                return;
            }

            let jit = JitCompiler::new(JitConfig::default());
            let ext: HashMap<String, *const u8> = HashMap::new();
            let buf = jit
                .compile_raw(&[build_return_const_named("f")], &ext)
                .expect("compile_raw should publish executable code");
            let f: extern "C" fn() -> u64 = unsafe {
                buf.get_fn_bound("f")
                    .expect("typed function pointer should exist")
                    .into_inner()
            };

            unsafe {
                sys::mprotect(buf.memory, buf.len, sys::RW)
                    .expect("force published buffer back to RW for drift probe");
                sys::set_jit_write_protect(false);
            }

            buf.ensure_published_executable()
                .expect("published buffer should reassert RX protection");
            assert_eq!(f(), 42);
            return;
        }

        if !sys::jit_write_protect_supported() {
            return;
        }

        let current_exe = std::env::current_exe().expect("current test binary");
        let output = std::process::Command::new(current_exe)
            .arg("jit::tests::test_ensure_published_executable_recovers_after_rw_protection_drift")
            .arg("--exact")
            .arg("--nocapture")
            .env(CHILD_ENV, "1")
            .output()
            .expect("run MAP_JIT reassert-RX child");

        assert!(
            output.status.success(),
            "child should execute after reasserting RX protection; status={:?}\nstdout:\n{}\nstderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
    }

    #[test]
    fn test_ensure_published_executable_rejects_unpublished_buffer() {
        let buf = make_buf_with_symbols(&["f"]);
        let err = match buf.ensure_published_executable() {
            Ok(_) => panic!("unpublished buffer must not be treated as executable"),
            Err(err) => err,
        };
        match err {
            JitError::UnpublishedExecutableBuffer {
                buffer_base,
                buffer_end,
                code_len,
                allocation_len,
            } => {
                assert_eq!(buffer_base, buf.memory as u64);
                assert_eq!(
                    buffer_end,
                    (buf.memory as u64).saturating_add(buf.code_len as u64)
                );
                assert_eq!(code_len, buf.code_len);
                assert_eq!(allocation_len, buf.len);
            }
            other => panic!("expected unpublished executable buffer, got {other:?}"),
        }
    }

    #[test]
    fn test_exact_pointer_owner_mismatch_rejects_before_publication() {
        let owner_a = make_buf_with_symbols(&["f"]);
        let owner_b = make_buf_with_symbols(&["f"]);
        let ptr = owner_a
            .get_fn_ptr_bound("f")
            .expect("owner A symbol should exist")
            .as_ptr();

        let err = match owner_b.ensure_published_symbol_ptr("f", ptr) {
            Ok(_) => panic!("wrong owner must reject the cached pointer"),
            Err(err) => err,
        };
        match err {
            JitError::JitPointerOwnershipMismatch {
                context,
                pointer,
                buffer_base,
                code_len,
                allocation_len,
                ..
            } => {
                assert!(context.contains("symbol `f`"));
                assert_eq!(pointer, ptr as u64);
                assert_eq!(buffer_base, owner_b.memory as u64);
                assert_eq!(code_len, owner_b.code_len);
                assert_eq!(allocation_len, owner_b.len);
            }
            other => panic!("expected pointer ownership mismatch, got {other:?}"),
        }
    }

    #[test]
    fn test_exact_pointer_symbol_mismatch_rejects_before_publication() {
        let buf = make_buf_with_symbols(&["f", "g"]);
        let ptr = buf
            .get_fn_ptr_bound("g")
            .expect("g symbol should exist")
            .as_ptr();

        let err = match buf.ensure_published_symbol_ptr("f", ptr) {
            Ok(_) => panic!("wrong symbol must reject the cached pointer"),
            Err(err) => err,
        };
        match err {
            JitError::FunctionPointerSymbolMismatch {
                symbol,
                pointer,
                buffer_base,
                actual_offset,
                expected_offset,
            } => {
                assert_eq!(symbol, "f");
                assert_eq!(pointer, ptr as u64);
                assert_eq!(buffer_base, buf.memory as u64);
                assert_eq!(actual_offset, 4);
                assert_eq!(expected_offset, 0);
            }
            other => panic!("expected symbol mismatch, got {other:?}"),
        }
    }

    #[test]
    fn test_exact_pointer_null_rejects_before_publication() {
        let buf = make_buf_with_symbols(&["f"]);
        let err = match buf.ensure_published_symbol_ptr("f", std::ptr::null()) {
            Ok(_) => panic!("null cached pointer must reject"),
            Err(err) => err,
        };
        match err {
            JitError::NullFunctionPointer { symbol } => assert_eq!(symbol, "f"),
            other => panic!("expected null function pointer, got {other:?}"),
        }
    }

    #[test]
    fn test_publication_proof_null_rejects_before_publication() {
        let buf = make_buf_with_symbols(&["f"]);
        let err = match buf.diagnose_published_symbol_ptr("f", std::ptr::null()) {
            Ok(proof) => panic!("null cached pointer must not produce proof: {proof:?}"),
            Err(err) => err,
        };
        match err {
            JitError::NullFunctionPointer { symbol } => assert_eq!(symbol, "f"),
            other => panic!("expected null function pointer, got {other:?}"),
        }
    }

    #[test]
    fn test_exact_pointer_rejects_unpublished_buffer() {
        let buf = make_buf_with_symbols(&["f"]);
        let ptr = buf
            .get_fn_ptr_bound("f")
            .expect("f symbol should exist")
            .as_ptr();

        let err = match buf.ensure_published_symbol_ptr("f", ptr) {
            Ok(_) => panic!("exact cached pointer must not publish an unpublished buffer"),
            Err(err) => err,
        };
        match err {
            JitError::UnpublishedExecutableBuffer {
                buffer_base,
                buffer_end,
                code_len,
                allocation_len,
            } => {
                assert_eq!(buffer_base, buf.memory as u64);
                assert_eq!(
                    buffer_end,
                    (buf.memory as u64).saturating_add(buf.code_len as u64)
                );
                assert_eq!(code_len, buf.code_len);
                assert_eq!(allocation_len, buf.len);
            }
            other => panic!("expected unpublished executable buffer, got {other:?}"),
        }
    }

    #[test]
    fn test_publication_proof_reports_exact_symbol_pointer() {
        let mut buf = make_buf_with_symbols(&["f", "g"]);
        buf.publication = JitPublicationContract::published_rx();
        let ptr = buf
            .get_fn_ptr_bound("g")
            .expect("g symbol should exist")
            .as_ptr();

        let proof = buf
            .diagnose_published_symbol_ptr("g", ptr)
            .expect("published exact symbol pointer should produce proof");

        assert_eq!(proof.symbol, "g");
        assert_eq!(proof.pointer, ptr as u64);
        assert_eq!(proof.buffer_base, buf.memory as u64);
        assert_eq!(
            proof.buffer_end,
            (buf.memory as u64).saturating_add(buf.code_len as u64)
        );
        assert_eq!(proof.code_len, buf.code_len);
        assert_eq!(proof.published_len, buf.published_len);
        assert_eq!(proof.allocation_len, buf.len);
        assert_eq!(proof.expected_symbol_offset, 4);
        assert_eq!(proof.actual_ptr_offset, 4);
        assert!(proof.exact_symbol_match);
        assert_eq!(proof.publication_contract, buf.publication_contract());
        assert!(proof.mprotect_rx_ok);
        assert_eq!(
            proof.execute_mode_reasserted,
            buf.publication_contract().map_jit && buf.publication_contract().published_rx
        );
        assert_eq!(proof.first_code_bytes.as_deref(), Some(&[0, 0, 0, 0][..]));
    }

    #[test]
    fn test_publication_proof_recovers_zero_primary_allocation_len_from_shadow() {
        let mut buf = make_buf_with_symbols(&["f"]);
        let mapped_len = buf.len;
        buf.publication = JitPublicationContract::published_rx();
        buf.len = 0;
        let ptr = buf
            .get_fn_ptr_bound("f")
            .expect("f symbol should exist")
            .as_ptr();

        let proof = buf
            .diagnose_published_symbol_ptr("f", ptr)
            .expect("valid shadow extent should recover zero primary len");

        assert_eq!(buf.allocated_size(), mapped_len);
        assert_eq!(proof.allocation_len, mapped_len);
        assert_eq!(
            proof.buffer_end,
            (buf.memory as u64).saturating_add(buf.code_len as u64)
        );
    }

    #[test]
    fn test_publication_proof_recovers_zero_len_metadata_from_published_len() {
        let mut buf = make_buf_with_symbols(&["f"]);
        let mapped_len = buf.len;
        let mapped_shadow = buf.len_shadow;
        let mapped_cookie = buf.allocation_cookie;
        buf.publication = JitPublicationContract::published_rx();
        buf.len = 0;
        buf.len_shadow = 0;
        buf.allocation_cookie = 0;
        let ptr = buf
            .get_fn_ptr_bound("f")
            .expect("f symbol should exist")
            .as_ptr();

        let proof = buf
            .diagnose_published_symbol_ptr("f", ptr)
            .expect("published_len-derived extent should recover zero length metadata");

        assert_eq!(buf.allocated_size(), mapped_len);
        assert_eq!(proof.allocation_len, mapped_len);
        assert_eq!(proof.published_len, buf.published_len);

        buf.len = mapped_len;
        buf.len_shadow = mapped_shadow;
        buf.allocation_cookie = mapped_cookie;
    }

    #[test]
    fn test_publication_proof_rejects_allocation_cookie_mismatch() {
        let mut buf = make_buf_with_symbols(&["f"]);
        let mapped_cookie = buf.allocation_cookie;
        buf.publication = JitPublicationContract::published_rx();
        buf.allocation_cookie = 0;
        let ptr = buf
            .get_fn_ptr_bound("f")
            .expect("f symbol should exist")
            .as_ptr();

        let err = match buf.diagnose_published_symbol_ptr("f", ptr) {
            Ok(proof) => panic!("cookie mismatch must not produce proof: {proof:?}"),
            Err(err) => err,
        };
        match err {
            JitError::InvalidExecutableBufferExtent {
                buffer_base,
                code_end,
                allocation_end,
                code_len,
                allocation_len,
            } => {
                assert_eq!(buffer_base, buf.memory as u64);
                assert_eq!(
                    code_end,
                    (buf.memory as u64).saturating_add(buf.code_len as u64)
                );
                assert_eq!(allocation_end, buf.memory as u64);
                assert_eq!(code_len, buf.code_len);
                assert_eq!(allocation_len, 0);
            }
            other => panic!("expected invalid executable extent, got {other:?}"),
        }

        buf.allocation_cookie = mapped_cookie;
    }

    #[test]
    fn test_publication_proof_rejects_zero_allocation_len() {
        let mut buf = make_buf_with_symbols(&["f"]);
        let mapped_len = buf.len;
        let mapped_shadow = buf.len_shadow;
        let mapped_code_len = buf.code_len;
        buf.publication = JitPublicationContract::published_rx();
        buf.len = 0;
        buf.len_shadow = 0;
        buf.code_len = 0;

        let err = match buf.ensure_published_executable() {
            Ok(_) => panic!("zero-length executable extent must not publish"),
            Err(err) => err,
        };
        match err {
            JitError::InvalidExecutableBufferExtent {
                buffer_base,
                code_end,
                allocation_end,
                code_len,
                allocation_len,
            } => {
                assert_eq!(buffer_base, buf.memory as u64);
                assert_eq!(code_end, buf.memory as u64);
                assert_eq!(allocation_end, buf.memory as u64);
                assert_eq!(code_len, 0);
                assert_eq!(allocation_len, 0);
            }
            other => panic!("expected invalid executable extent, got {other:?}"),
        }

        buf.len = mapped_len;
        buf.len_shadow = mapped_shadow;
        buf.code_len = mapped_code_len;
    }

    #[test]
    fn test_publication_proof_rejects_code_len_beyond_allocation_len() {
        let mut buf = make_buf_with_symbols(&["f", "g"]);
        let mapped_len = buf.len;
        buf.publication = JitPublicationContract::published_rx();
        buf.len = buf.code_len - 1;
        let ptr = buf
            .get_fn_ptr_bound("f")
            .expect("f symbol should exist")
            .as_ptr();

        let err = match buf.diagnose_published_symbol_ptr("f", ptr) {
            Ok(proof) => panic!("oversized code extent must not produce proof: {proof:?}"),
            Err(err) => err,
        };
        match err {
            JitError::InvalidExecutableBufferExtent {
                buffer_base,
                code_end,
                allocation_end,
                code_len,
                allocation_len,
            } => {
                assert_eq!(buffer_base, buf.memory as u64);
                assert_eq!(
                    code_end,
                    (buf.memory as u64).saturating_add(buf.code_len as u64)
                );
                assert_eq!(
                    allocation_end,
                    (buf.memory as u64).saturating_add(buf.len as u64)
                );
                assert_eq!(code_len, buf.code_len);
                assert_eq!(allocation_len, buf.len);
            }
            other => panic!("expected invalid executable extent, got {other:?}"),
        }

        buf.len = mapped_len;
    }

    #[test]
    fn test_publication_proof_rejects_published_len_before_code_len() {
        let mut buf = make_buf_with_symbols(&["f", "g"]);
        let mapped_published_len = buf.published_len;
        buf.publication = JitPublicationContract::published_rx();
        buf.published_len = buf.code_len - 1;
        let ptr = buf
            .get_fn_ptr_bound("f")
            .expect("f symbol should still be inside code_len")
            .as_ptr();

        let err = match buf.diagnose_published_symbol_ptr("f", ptr) {
            Ok(proof) => panic!("published_len < code_len must not produce proof: {proof:?}"),
            Err(err) => err,
        };
        match err {
            JitError::InvalidExecutableBufferExtent { code_len, .. } => {
                assert_eq!(code_len, buf.code_len);
            }
            other => panic!("expected invalid executable extent, got {other:?}"),
        }

        buf.published_len = mapped_published_len;
    }

    #[test]
    fn test_publication_proof_rejects_published_len_beyond_allocation_len() {
        let mut buf = make_buf_with_symbols(&["f", "g"]);
        let mapped_published_len = buf.published_len;
        buf.publication = JitPublicationContract::published_rx();
        buf.published_len = buf.len + 1;
        let ptr = buf
            .get_fn_ptr_bound("f")
            .expect("f symbol should still be inside code_len")
            .as_ptr();

        let err = match buf.diagnose_published_symbol_ptr("f", ptr) {
            Ok(proof) => panic!("published_len > allocation_len must not produce proof: {proof:?}"),
            Err(err) => err,
        };
        match err {
            JitError::InvalidExecutableBufferExtent { allocation_len, .. } => {
                assert_eq!(allocation_len, buf.len);
            }
            other => panic!("expected invalid executable extent, got {other:?}"),
        }

        buf.published_len = mapped_published_len;
    }

    #[test]
    fn test_get_fn_ptr_bound_rejects_symbol_offset_at_code_boundary() {
        let mut buf = make_buf_with_symbols(&["f"]);
        buf.symbol_offsets
            .insert("xdata".to_string(), buf.code_len as u64);

        assert!(
            buf.get_fn_ptr_bound("xdata").is_none(),
            "raw symbol lookup must not return pointers into metadata after code_len"
        );
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_compile_raw_publication_proof_reports_nonzero_allocation_len() {
        let jit = JitCompiler::new(JitConfig::default());
        let ext: HashMap<String, *const u8> = HashMap::new();
        let buf = jit
            .compile_raw(&[build_return_const_named("f")], &ext)
            .expect("compile_raw should publish executable code");
        let ptr = buf
            .get_fn_ptr_bound("f")
            .expect("f symbol should exist")
            .as_ptr();

        let proof = buf
            .diagnose_published_symbol_ptr("f", ptr)
            .expect("real compiled buffer should produce publication proof");
        assert!(proof.code_len > 0);
        assert!(proof.allocation_len > 0);
        assert!(proof.allocation_len >= proof.code_len);
        assert_eq!(proof.allocation_len, buf.allocated_size());
    }

    #[test]
    fn test_publication_proof_wrong_symbol_rejects_before_publication() {
        let mut buf = make_buf_with_symbols(&["f", "g"]);
        buf.publication = JitPublicationContract::published_rx();
        let ptr = buf
            .get_fn_ptr_bound("g")
            .expect("g symbol should exist")
            .as_ptr();

        let err = match buf.diagnose_published_symbol_ptr("f", ptr) {
            Ok(proof) => panic!("wrong symbol must not produce proof: {proof:?}"),
            Err(err) => err,
        };
        match err {
            JitError::FunctionPointerSymbolMismatch {
                symbol,
                pointer,
                buffer_base,
                actual_offset,
                expected_offset,
            } => {
                assert_eq!(symbol, "f");
                assert_eq!(pointer, ptr as u64);
                assert_eq!(buffer_base, buf.memory as u64);
                assert_eq!(actual_offset, 4);
                assert_eq!(expected_offset, 0);
            }
            other => panic!("expected symbol mismatch, got {other:?}"),
        }
    }

    #[test]
    fn test_publication_proof_wrong_owner_rejects_before_publication() {
        let mut owner_a = make_buf_with_symbols(&["f"]);
        owner_a.publication = JitPublicationContract::published_rx();
        let mut owner_b = make_buf_with_symbols(&["f"]);
        owner_b.publication = JitPublicationContract::published_rx();
        let ptr = owner_a
            .get_fn_ptr_bound("f")
            .expect("owner A symbol should exist")
            .as_ptr();

        let err = match owner_b.diagnose_published_symbol_ptr("f", ptr) {
            Ok(proof) => panic!("wrong owner must not produce proof: {proof:?}"),
            Err(err) => err,
        };
        match err {
            JitError::JitPointerOwnershipMismatch {
                context,
                pointer,
                buffer_base,
                code_len,
                allocation_len,
                ..
            } => {
                assert!(context.contains("symbol `f`"));
                assert_eq!(pointer, ptr as u64);
                assert_eq!(buffer_base, owner_b.memory as u64);
                assert_eq!(code_len, owner_b.code_len);
                assert_eq!(allocation_len, owner_b.len);
            }
            other => panic!("expected pointer ownership mismatch, got {other:?}"),
        }
    }

    #[test]
    fn test_publication_proof_unpublished_buffer_rejects_after_pointer_checks() {
        let buf = make_buf_with_symbols(&["f"]);
        let ptr = buf
            .get_fn_ptr_bound("f")
            .expect("f symbol should exist")
            .as_ptr();

        let err = match buf.diagnose_published_symbol_ptr("f", ptr) {
            Ok(proof) => panic!("unpublished buffer must not produce proof: {proof:?}"),
            Err(err) => err,
        };
        match err {
            JitError::UnpublishedExecutableBuffer {
                buffer_base,
                buffer_end,
                code_len,
                allocation_len,
            } => {
                assert_eq!(buffer_base, buf.memory as u64);
                assert_eq!(
                    buffer_end,
                    (buf.memory as u64).saturating_add(buf.code_len as u64)
                );
                assert_eq!(code_len, buf.code_len);
                assert_eq!(allocation_len, buf.len);
            }
            other => panic!("expected unpublished executable buffer, got {other:?}"),
        }
    }

    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    #[test]
    fn test_exact_pointer_owner_recovers_after_rw_write_mode_drift() {
        const CHILD_ENV: &str = "TRUST_CG_MAP_JIT_EXACT_PTR_REASSERT_CHILD";

        if std::env::var_os(CHILD_ENV).is_some() {
            if !sys::jit_write_protect_supported() {
                return;
            }

            let jit = JitCompiler::new(JitConfig::default());
            let ext: HashMap<String, *const u8> = HashMap::new();
            let buf = jit
                .compile_raw(&[build_return_const_named("f")], &ext)
                .expect("compile_raw should publish executable code");
            let raw = buf
                .get_fn_ptr_bound("f")
                .expect("raw function pointer should exist")
                .as_ptr();
            assert_eq!(buf.code_offset_for_host_pc(raw as u64), Some(0));

            unsafe {
                sys::mprotect(buf.memory, buf.len, sys::RW)
                    .expect("force published buffer back to RW for exact pointer drift probe");
                sys::set_jit_write_protect(false);
            }

            let checked = buf
                .ensure_published_symbol_ptr("f", raw)
                .expect("exact cached pointer should reassert RX protection");
            let checked_raw = checked.as_ptr();
            let f: extern "C" fn() -> u64 = unsafe { std::mem::transmute_copy(&checked_raw) };
            assert_eq!(f(), 42);
            return;
        }

        if !sys::jit_write_protect_supported() {
            return;
        }

        let current_exe = std::env::current_exe().expect("current test binary");
        let output = std::process::Command::new(current_exe)
            .arg("jit::tests::test_exact_pointer_owner_recovers_after_rw_write_mode_drift")
            .arg("--exact")
            .arg("--nocapture")
            .env(CHILD_ENV, "1")
            .output()
            .expect("run MAP_JIT exact-pointer reassert child");

        assert!(
            output.status.success(),
            "child should execute after exact-pointer publication reasserts RX; status={:?}\nstdout:\n{}\nstderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
    }

    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    #[test]
    fn test_exact_pointer_owner_recovers_when_multiple_buffers_drift_to_rw() {
        const CHILD_ENV: &str = "TRUST_CG_MAP_JIT_MULTI_BUFFER_EXACT_PTR_REASSERT_CHILD";

        if std::env::var_os(CHILD_ENV).is_some() {
            if !sys::jit_write_protect_supported() {
                return;
            }

            let jit = JitCompiler::new(JitConfig::default());
            let ext: HashMap<String, *const u8> = HashMap::new();
            let buffers = vec![
                jit.compile_raw(&[build_return_const_named("f")], &ext)
                    .expect("compile first buffer"),
                jit.compile_raw(&[build_return_const_named("f")], &ext)
                    .expect("compile owner buffer"),
                jit.compile_raw(&[build_return_const_named("f")], &ext)
                    .expect("compile third buffer"),
            ];
            let owner = &buffers[1];
            let raw = owner
                .get_fn_ptr_bound("f")
                .expect("raw function pointer should exist")
                .as_ptr();
            assert_eq!(owner.code_offset_for_host_pc(raw as u64), Some(0));
            assert!(buffers[0].code_offset_for_host_pc(raw as u64).is_none());
            assert!(buffers[2].code_offset_for_host_pc(raw as u64).is_none());

            unsafe {
                for buf in &buffers {
                    sys::mprotect(buf.memory, buf.len, sys::RW)
                        .expect("force published buffer back to RW for multi-buffer drift probe");
                }
                sys::set_jit_write_protect(false);
            }

            let checked = owner
                .ensure_published_symbol_ptr("f", raw)
                .expect("exact cached owner pointer should reassert RX protection");
            let checked_raw = checked.as_ptr();
            let f: extern "C" fn() -> u64 = unsafe { std::mem::transmute_copy(&checked_raw) };
            assert_eq!(f(), 42);
            return;
        }

        if !sys::jit_write_protect_supported() {
            return;
        }

        let current_exe = std::env::current_exe().expect("current test binary");
        let output = std::process::Command::new(current_exe)
            .arg("jit::tests::test_exact_pointer_owner_recovers_when_multiple_buffers_drift_to_rw")
            .arg("--exact")
            .arg("--nocapture")
            .env(CHILD_ENV, "1")
            .output()
            .expect("run MAP_JIT multi-buffer exact-pointer reassert child");

        assert!(
            output.status.success(),
            "child should execute after exact-pointer publication reasserts the owner among multiple RW buffers; status={:?}\nstdout:\n{}\nstderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
    }

    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    #[test]
    fn test_installed_artifact_exact_pointer_recovers_after_rw_write_mode_drift() {
        const CHILD_ENV: &str = "TRUST_CG_MAP_JIT_INSTALLED_EXACT_PTR_REASSERT_CHILD";

        if std::env::var_os(CHILD_ENV).is_some() {
            if !sys::jit_write_protect_supported() {
                return;
            }

            let jit = JitCompiler::new(JitConfig::default());
            let ext: HashMap<String, *const u8> = HashMap::new();
            let buf = jit
                .compile_raw(&[build_return_const_named("f")], &ext)
                .expect("compile_raw should publish executable code");
            let install_metadata = crate::compile_service::CompiledArtifact::metadata_only(
                "jit-installed-exact-pointer",
                crate::compile_service::CompileGeneration::new(1),
            )
            .install;
            let installed = crate::compile_service::InstalledArtifact::new(
                std::sync::Arc::new(buf),
                install_metadata,
            );
            let raw = installed
                .entrypoint_ptr("f")
                .expect("installed raw entrypoint should exist")
                .as_ptr();

            unsafe {
                sys::mprotect(installed.buffer.memory, installed.buffer.len, sys::RW)
                    .expect("force installed buffer back to RW for exact pointer drift probe");
                sys::set_jit_write_protect(false);
            }

            let checked = installed
                .ensure_published_entrypoint_ptr("f", raw)
                .expect("installed exact cached pointer should reassert RX protection");
            let checked_raw = checked.as_ptr();
            let f: extern "C" fn() -> u64 = unsafe { std::mem::transmute_copy(&checked_raw) };
            assert_eq!(f(), 42);
            return;
        }

        if !sys::jit_write_protect_supported() {
            return;
        }

        let current_exe = std::env::current_exe().expect("current test binary");
        let output = std::process::Command::new(current_exe)
            .arg("jit::tests::test_installed_artifact_exact_pointer_recovers_after_rw_write_mode_drift")
            .arg("--exact")
            .arg("--nocapture")
            .env(CHILD_ENV, "1")
            .output()
            .expect("run MAP_JIT installed exact-pointer reassert child");

        assert!(
            output.status.success(),
            "child should execute after installed exact-pointer publication reasserts RX; status={:?}\nstdout:\n{}\nstderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
    }

    // -- Issue #353: veneer patching with missing extern symbols ----------------

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_patch_branch26_oob_offset_returns_error() {
        let mut code = vec![0u8; 4];
        // offset 4 means code[4..8] which is out of bounds for a 4-byte buffer
        let result = patch_branch26(&mut code, 4, 0);
        assert!(matches!(
            result,
            Err(JitError::FixupOutOfBounds {
                offset: 4,
                code_len: 4
            })
        ));
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn test_patch_rel32_oob_offset_returns_error() {
        let mut code = vec![0xE8, 0, 0, 0, 0]; // 5-byte CALL
        // offset 2 means we need code[2..8] which is out of bounds
        let result = patch_rel32(&mut code, 2, 100);
        assert!(matches!(
            result,
            Err(JitError::FixupOutOfBounds {
                offset: 2,
                code_len: 5
            })
        ));
    }

    // -- Issue #352: get_fn transmute_copy size check --------------------------

    #[test]
    fn test_get_fn_size_mismatch_panics() {
        // Create a minimal ExecutableBuffer with a known symbol
        let size = sys::page_align(16);
        let memory = unsafe { sys::mmap(size, sys::RW).expect("mmap failed") };
        let mut symbol_offsets = HashMap::new();
        symbol_offsets.insert("test".to_string(), 0u64);
        let buf = ExecutableBuffer {
            memory,
            len: size,
            len_shadow: size,
            allocation_cookie: executable_buffer_allocation_cookie(memory, size, 16, 16),
            code_len: 16,
            published_len: 16,
            published_image_sha256: String::new(),
            publication: JitPublicationContract::unpublished_for_tests(),
            windows_unwind: WindowsJitUnwindRegistration,
            function_ranges: vec![("test".to_string(), 0..16)],
            symbol_offsets,
            canonical_symbols: vec!["test".to_string()],
            counters: HashMap::new(),
            timing_cells: HashMap::new(),
            timing_state: None,
            certificates: HashMap::new(),
            proof_optimization_certificates: Vec::new(),
        };
        // [u8; 16] is 16 bytes, not pointer-sized (8 bytes) — should panic
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
            buf.get_fn::<[u8; 16]>("test")
        }));
        assert!(result.is_err(), "get_fn should panic on size mismatch");
        // Prevent Drop from double-freeing since we need to clean up manually
        std::mem::forget(buf);
        unsafe {
            sys::munmap(memory, size);
        }
    }

    #[test]
    fn test_get_fn_pointer_sized_ok() {
        let size = sys::page_align(16);
        let memory = unsafe { sys::mmap(size, sys::RW).expect("mmap failed") };
        let mut symbol_offsets = HashMap::new();
        symbol_offsets.insert("test".to_string(), 0u64);
        let buf = ExecutableBuffer {
            memory,
            len: size,
            len_shadow: size,
            allocation_cookie: executable_buffer_allocation_cookie(memory, size, 16, 16),
            code_len: 16,
            published_len: 16,
            published_image_sha256: String::new(),
            publication: JitPublicationContract::unpublished_for_tests(),
            windows_unwind: WindowsJitUnwindRegistration,
            function_ranges: vec![("test".to_string(), 0..16)],
            symbol_offsets,
            canonical_symbols: vec!["test".to_string()],
            counters: HashMap::new(),
            timing_cells: HashMap::new(),
            timing_state: None,
            certificates: HashMap::new(),
            proof_optimization_certificates: Vec::new(),
        };
        // fn() is pointer-sized — should not panic
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
            buf.get_fn::<fn()>("test")
        }));
        assert!(
            result.is_ok(),
            "get_fn should succeed for pointer-sized types"
        );
        std::mem::forget(buf);
        unsafe {
            sys::munmap(memory, size);
        }
    }

    // -- Issue #345: BL range validation for veneer trampolines ----------------

    /// `branch26_in_range` accepts distances strictly inside +-128 MiB and
    /// rejects anything at or beyond the asymmetric limit [-2^27, +2^27).
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_branch26_in_range_boundaries() {
        // Exactly +128 MiB is the first out-of-range value (imm26 is a signed
        // 26-bit word offset => max byte distance is (1 << 27) - 4).
        let (ok, _) = branch26_in_range(0, AARCH64_BRANCH26_MAX as u64);
        assert!(!ok, "distance of +128 MiB must be out of range");

        // One instruction under the limit is fine.
        let (ok, _) = branch26_in_range(0, (AARCH64_BRANCH26_MAX - 4) as u64);
        assert!(ok, "distance of +128 MiB - 4 must be in range");

        // Zero is trivially in range.
        let (ok, dist) = branch26_in_range(100, 100);
        assert!(ok);
        assert_eq!(dist, 0);
    }

    /// `patch_branch26` must refuse to encode an out-of-range BL instead of
    /// silently truncating the imm26 field.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_patch_branch26_out_of_range_returns_error() {
        // Build a 4-byte BL so the fixup offset itself is in bounds; the
        // target is what overflows +-128 MiB. We cannot actually allocate
        // 128 MiB of code in a test, but `patch_branch26` only inspects the
        // arithmetic distance — any (offset, target) pair whose delta
        // exceeds the limit exercises the error path.
        let mut code = vec![0u8; 4];
        code[0..4].copy_from_slice(&0x9400_0000u32.to_le_bytes());
        let target = AARCH64_BRANCH26_MAX as u64; // exactly +128 MiB, first invalid
        let result = patch_branch26(&mut code, 0, target);
        match result {
            Err(JitError::BranchOutOfRange {
                offset,
                target: t,
                distance,
            }) => {
                assert_eq!(offset, 0);
                assert_eq!(t, target);
                assert_eq!(distance, AARCH64_BRANCH26_MAX);
            }
            other => panic!("expected BranchOutOfRange, got {:?}", other),
        }
        // The instruction must be unchanged — no partial/corrupt encoding.
        let still = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
        assert_eq!(still, 0x9400_0000);
    }

    /// Construct a `VeneerOutOfRange` error and confirm the diagnostic
    /// message names the symbol, distance, and 128 MiB limit so operators
    /// can tell veneer-distance problems apart from generic branch range
    /// failures (e.g., a cross-function BL that was never reachable).
    #[test]
    fn test_veneer_out_of_range_error_message() {
        let err = JitError::VeneerOutOfRange {
            symbol: "_host_helper".to_string(),
            offset: 0,
            veneer_offset: 256 * 1024 * 1024,
            distance: 256 * 1024 * 1024,
        };
        let msg = format!("{}", err);
        assert!(msg.contains("_host_helper"), "message: {msg}");
        assert!(msg.contains("128MiB"), "message: {msg}");
    }

    /// Drive `validate_veneer_ranges` — the production seam used by
    /// `compile_raw` — with a synthetic `(fixup, veneer)` pair whose distance
    /// is just past the AArch64 imm26 limit. This is the end-to-end regression
    /// for #345: it proves the compile_raw validation path actually returns
    /// `VeneerOutOfRange` rather than falling through to `patch_branch26` and
    /// emitting a silently-truncated BL.
    ///
    /// We cannot allocate >128 MiB of real code in a unit test, so we pass
    /// hand-built offsets directly. On non-aarch64 hosts the validator is a
    /// no-op by design — the imm26 range is an AArch64-specific constraint —
    /// so the test is gated to aarch64.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_validate_veneer_ranges_detects_out_of_range_patch() {
        // BL at offset 0; veneer pretends to live at exactly +128 MiB.
        // +128 MiB is the first out-of-range byte distance (imm26 encodes
        // a signed 26-bit word offset, so the reachable byte range is
        // `[-2^27, +2^27)`).
        let ext_patches = vec![(
            0u32,
            AARCH64_BRANCH26_MAX as u64,
            "_host_helper".to_string(),
        )];
        // `code_len` is only advisory for future island-aware variants;
        // the current validator looks only at the (fixup, veneer) arithmetic.
        let err = validate_veneer_ranges(&ext_patches, AARCH64_BRANCH26_MAX as usize + 16)
            .expect_err("validator must reject out-of-range veneer");
        match err {
            JitError::VeneerOutOfRange {
                symbol,
                offset,
                veneer_offset,
                distance,
            } => {
                assert_eq!(symbol, "_host_helper");
                assert_eq!(offset, 0);
                assert_eq!(veneer_offset, AARCH64_BRANCH26_MAX as u64);
                assert_eq!(distance, AARCH64_BRANCH26_MAX);
            }
            other => panic!("expected VeneerOutOfRange, got {:?}", other),
        }
    }

    /// A veneer exactly 4 bytes inside the +-128 MiB limit must be accepted —
    /// this locks in the asymmetric `[-2^27, +2^27)` boundary and protects
    /// against future off-by-one regressions (e.g., someone flipping `>=` to
    /// `>` or rewriting the limit as `1 << 27 - 1`).
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_validate_veneer_ranges_accepts_boundary_minus_four() {
        let ext_patches = vec![(
            0u32,
            (AARCH64_BRANCH26_MAX - 4) as u64,
            "_host_helper".to_string(),
        )];
        validate_veneer_ranges(&ext_patches, (AARCH64_BRANCH26_MAX + 16) as usize)
            .expect("exact-limit-minus-one-instruction must be in range");
    }

    /// When multiple veneer patches are in play, the validator must fail on
    /// the *first* out-of-range entry and name that specific symbol. This
    /// guarantees the error message points at the actual distance problem
    /// rather than whichever fixup happened to be last in the list.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_validate_veneer_ranges_reports_first_failing_symbol() {
        let ext_patches = vec![
            (0u32, 16u64, "_near".to_string()), // trivially in range
            (0u32, AARCH64_BRANCH26_MAX as u64, "_far".to_string()), // the culprit
            (
                0u32,
                (AARCH64_BRANCH26_MAX * 2) as u64,
                "_further".to_string(),
            ), // also bad, but must not be reported first
        ];
        let err = validate_veneer_ranges(&ext_patches, 0)
            .expect_err("validator must reject when any veneer is out of range");
        match err {
            JitError::VeneerOutOfRange { symbol, .. } => {
                assert_eq!(
                    symbol, "_far",
                    "validator must report the first failing symbol"
                );
            }
            other => panic!("expected VeneerOutOfRange, got {:?}", other),
        }
    }

    // -- Issue #360: symbol_count / symbols robustness -------------------------

    /// Build a minimal `ExecutableBuffer` whose `symbol_offsets` map mirrors
    /// what `compile_raw` produces: one canonical entry per function plus one
    /// Mach-O-style `_name` alias pointing at the same offset. Tests don't
    /// want to run the full codegen pipeline, so we fabricate the map
    /// directly and verify the counting / iteration contracts.
    fn make_buf_with_symbols(names: &[&str]) -> ExecutableBuffer {
        let size = sys::page_align(16);
        let memory = unsafe { sys::mmap(size, sys::RW).expect("mmap failed") };
        let mut symbol_offsets: HashMap<String, u64> = HashMap::new();
        let mut canonical_symbols = Vec::with_capacity(names.len());
        let mut function_ranges = Vec::with_capacity(names.len());
        for (i, n) in names.iter().enumerate() {
            let off = i as u64 * 4;
            canonical_symbols.push((*n).to_string());
            function_ranges.push(((*n).to_string(), off..off + 4));
            symbol_offsets.insert((*n).to_string(), off);
            symbol_offsets.insert(format!("_{}", n), off);
        }
        ExecutableBuffer {
            memory,
            len: size,
            len_shadow: size,
            allocation_cookie: executable_buffer_allocation_cookie(
                memory,
                size,
                names.len() * 4,
                names.len() * 4,
            ),
            code_len: names.len() * 4,
            published_len: names.len() * 4,
            published_image_sha256: String::new(),
            publication: JitPublicationContract::unpublished_for_tests(),
            windows_unwind: WindowsJitUnwindRegistration,
            function_ranges,
            symbol_offsets,
            canonical_symbols,
            counters: HashMap::new(),
            timing_cells: HashMap::new(),
            timing_state: None,
            certificates: HashMap::new(),
            proof_optimization_certificates: Vec::new(),
        }
    }

    fn contract_i64_to_i64_signature() -> SymbolSignature {
        SymbolSignature::extern_c(
            vec![AbiValue::new(AbiValueKind::I64)],
            vec![AbiValue::new(AbiValueKind::I64)],
        )
    }

    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    fn contract_void_to_i64_signature() -> SymbolSignature {
        SymbolSignature::extern_c(Vec::new(), vec![AbiValue::new(AbiValueKind::I64)])
    }

    fn contract_i32_to_i64_signature() -> SymbolSignature {
        SymbolSignature::extern_c(
            vec![AbiValue::new(AbiValueKind::I32)],
            vec![AbiValue::new(AbiValueKind::I64)],
        )
    }

    fn manifest_with_contract_symbol(symbol: &str) -> ArtifactManifestV1 {
        manifest_with_contract_symbol_and_signature(symbol, contract_i64_to_i64_signature())
    }

    fn manifest_with_contract_symbol_and_signature(
        symbol: &str,
        signature: SymbolSignature,
    ) -> ArtifactManifestV1 {
        let target =
            TargetDescriptor::for_trust_cg_target(Target::Aarch64, TargetOperatingSystem::Macos)
                .with_cpu("apple-m")
                .with_features(["fp", "simd"]);
        let abi = AbiDescriptor::for_trust_cg_target(Target::Aarch64);
        let layout = LayoutManifest::lp64(Endianness::Little, 16);
        let proof_policy = ProofPolicy::disabled();
        let invalidation = InvalidationKey::new(
            "source:jit-unit",
            "compiler:jit-unit",
            target.checksum(),
            abi.checksum(),
            layout.checksum(),
            proof_policy.checksum(),
            1,
        );
        let mut manifest = ArtifactManifestV1::new(
            "jit-unit-artifact",
            JitArtifactKind::ExecutableMemory,
            target,
            abi,
            layout,
            invalidation,
            proof_policy,
        );
        manifest.symbols.push(ArtifactSymbol {
            name: symbol.to_owned(),
            visibility: SymbolVisibility::Exported,
            signature,
            offset_bytes: Some(0),
            checksum: None,
        });
        manifest
    }

    fn symbol_lookup_contract_for(
        manifest: &ArtifactManifestV1,
        symbol: &str,
    ) -> SymbolLookupContract {
        symbol_lookup_contract_for_with_signature(manifest, symbol, contract_i64_to_i64_signature())
    }

    fn symbol_lookup_contract_for_with_signature(
        manifest: &ArtifactManifestV1,
        symbol: &str,
        signature: SymbolSignature,
    ) -> SymbolLookupContract {
        SymbolLookupContract::new(
            symbol,
            signature,
            manifest.target.checksum(),
            manifest.abi.checksum(),
            manifest.layout.checksum(),
        )
        .with_invalidation_checksum(manifest.invalidation.checksum())
        .with_manifest_checksum(manifest.checksum())
    }

    #[test]
    fn test_executable_buffer_contract_symbol_bound() {
        type EntryFn = extern "C" fn(i64) -> i64;

        let buf = make_buf_with_symbols(&["entry"]);
        let manifest = manifest_with_contract_symbol("entry");
        let contract = symbol_lookup_contract_for(&manifest, "entry");

        let typed = buf
            .get_contract_symbol_bound::<EntryFn>(&manifest, &contract)
            .expect("valid executable-buffer symbol and manifest contract should bind");
        assert_eq!(typed.symbol(), "entry");
        assert_eq!(typed.signature(), &contract_i64_to_i64_signature());
        assert_eq!(typed.artifact_checksum(), manifest.checksum());
        assert_eq!(typed.as_ptr(), buf.memory as *const u8);

        let mut wrong_abi = contract.clone();
        wrong_abi.abi_checksum = ArtifactChecksum::new(contract.abi_checksum.get() ^ 1);
        let err = buf
            .get_contract_symbol_bound::<EntryFn>(&manifest, &wrong_abi)
            .expect_err("ABI checksum mismatch must reject the typed symbol");
        match err {
            ArtifactContractError::ChecksumMismatch { component, .. } => {
                assert_eq!(component, "abi");
            }
            other => panic!("expected ABI checksum mismatch, got {other:?}"),
        }

        let mut wrong_signature = contract.clone();
        wrong_signature.signature = contract_i32_to_i64_signature();
        let err = buf
            .get_contract_symbol_bound::<extern "C" fn(i32) -> i64>(&manifest, &wrong_signature)
            .expect_err("signature mismatch must reject the typed symbol");
        match err {
            ArtifactContractError::SignatureMismatch { symbol, .. } => {
                assert_eq!(symbol, "entry");
            }
            other => panic!("expected signature mismatch, got {other:?}"),
        }

        let missing_buf_symbol = make_buf_with_symbols(&["other"]);
        let err = missing_buf_symbol
            .get_contract_symbol_bound::<EntryFn>(&manifest, &contract)
            .expect_err("missing executable-buffer symbol must surface as null pointer");
        match err {
            ArtifactContractError::NullSymbolPointer { symbol } => {
                assert_eq!(symbol, "entry");
            }
            other => panic!("expected null symbol pointer, got {other:?}"),
        }
    }

    /// Plain names without any underscore prefix must count and enumerate
    /// correctly. This is the common "user function" case.
    #[test]
    fn test_symbol_count_plain_names() {
        let buf = make_buf_with_symbols(&["foo", "bar", "baz"]);
        assert_eq!(buf.symbol_count(), 3);
        let names: Vec<&str> = buf.symbols().map(|(n, _)| n).collect();
        assert!(names.contains(&"foo"));
        assert!(names.contains(&"bar"));
        assert!(names.contains(&"baz"));
        assert_eq!(names.len(), 3);
    }

    /// Mixed plain and `_`-prefixed names: `symbol_count` must still equal
    /// the number of functions, and `symbols()` must yield every canonical
    /// name (including the `_foo` one) exactly once. The old `/ 2` hack
    /// happened to get the count right here but the `starts_with('_')`
    /// filter hid `_priv`.
    #[test]
    fn test_symbol_count_mixed_underscore_prefix() {
        let buf = make_buf_with_symbols(&["foo", "_priv", "bar"]);
        assert_eq!(
            buf.symbol_count(),
            3,
            "symbol_count must not depend on `_name` alias parity"
        );
        let names: Vec<&str> = buf.symbols().map(|(n, _)| n).collect();
        assert!(names.contains(&"foo"));
        assert!(
            names.contains(&"_priv"),
            "symbols() must expose canonical names starting with '_', \
             not silently filter them out"
        );
        assert!(names.contains(&"bar"));
        assert_eq!(names.len(), 3);
    }

    /// All user names start with `_`. Before the fix this case produced a
    /// correct count by coincidence but `symbols()` returned an empty
    /// iterator, hiding every function from callers.
    #[test]
    fn test_symbol_count_all_underscore_prefix() {
        let buf = make_buf_with_symbols(&["_foo", "_bar"]);
        assert_eq!(buf.symbol_count(), 2);
        let names: Vec<&str> = buf.symbols().map(|(n, _)| n).collect();
        assert_eq!(names.len(), 2, "all-underscore names must not be hidden");
        assert!(names.contains(&"_foo"));
        assert!(names.contains(&"_bar"));
    }

    /// `symbols()` must return each function exactly once, even though the
    /// underlying `symbol_offsets` map holds two entries per function
    /// (canonical + `_`-prefixed alias). This is the invariant the old
    /// `/ 2` hack tried — and sometimes failed — to express.
    #[test]
    fn test_symbols_deduplicates_aliases() {
        let buf = make_buf_with_symbols(&["foo", "bar"]);
        let collected: Vec<(&str, u64)> = buf.symbols().collect();
        assert_eq!(collected.len(), 2);
        // Each canonical name should appear once and map to the same offset
        // as its alias in `symbol_offsets`.
        for (name, off) in collected {
            assert_eq!(buf.symbol_offsets.get(name).copied(), Some(off));
            assert_eq!(
                buf.symbol_offsets.get(&format!("_{}", name)).copied(),
                Some(off),
                "alias `_{name}` must resolve to the same offset"
            );
        }
    }

    /// Empty buffer edge case: both accessors should be safe and empty.
    #[test]
    fn test_symbol_count_empty() {
        let buf = make_buf_with_symbols(&[]);
        assert_eq!(buf.symbol_count(), 0);
        assert_eq!(buf.symbols().count(), 0);
    }

    // -- JitConfig dispatch-verification defaults (#375) -----------------------

    /// Tests for the #375 change: `JitConfig::default().verify_dispatch` is
    /// `DispatchVerifyMode::ErrorOnFailure`, the field is caller-visible, and
    /// the value propagates into the underlying `Pipeline`. Uses the
    /// `pub(crate) #[cfg(test)] pipeline()` accessor so tests can reach
    /// `Pipeline::generate_and_verify_dispatch` without exposing a permanent
    /// public API surface.
    mod dispatch_verify_defaults {
        use super::*;
        use crate::pipeline::PipelineError;
        use std::collections::HashMap;
        use trust_cg_ir::cost_model::CostModelGen;
        use trust_cg_lower::compute_graph::{
            ComputeCost, ComputeGraph, ComputeNode, ComputeNodeId, DataEdge, NodeKind,
            TargetRecommendation,
        };
        use trust_cg_lower::target_analysis::ComputeTarget;

        fn make_graph(nodes: Vec<ComputeNode>, edges: Vec<DataEdge>) -> ComputeGraph {
            let mut graph = ComputeGraph::new_with_profitability(CostModelGen::M1);
            graph.nodes = nodes;
            graph.edges = edges;
            graph
        }

        /// A deliberately broken graph: the single node only permits GPU, so
        /// the dispatch verifier cannot construct a safe CPU fallback. This
        /// mirrors `bad_fallback_graph` in `pipeline.rs` tests.
        fn bad_fallback_graph() -> (ComputeGraph, Vec<TargetRecommendation>) {
            let mut gpu_costs = HashMap::new();
            gpu_costs.insert(
                ComputeTarget::Gpu,
                ComputeCost {
                    latency_cycles: 5,
                    throughput_ops_per_kcycle: 100_000,
                },
            );

            let node = ComputeNode {
                id: ComputeNodeId(0),
                instructions: vec![],
                costs: gpu_costs,
                legal_targets: vec![ComputeTarget::Gpu], // No CPU fallback.
                kind: NodeKind::DataParallel,
                data_size_bytes: 4096,
                produced_values: vec![],
                consumed_values: vec![],
                dominant_op: "ADD".to_string(),
                target_legality: None,
                matmul_shape: None,
            };

            let graph = make_graph(vec![node], vec![]);

            let recs = vec![TargetRecommendation {
                node_id: ComputeNodeId(0),
                recommended_target: ComputeTarget::Gpu,
                legal_targets: vec![ComputeTarget::Gpu],
                reason: "GPU only".to_string(),
                parallel_reduction_legal: false,
            }];

            (graph, recs)
        }

        /// AC 2: `JitConfig::default()` selects `ErrorOnFailure`.
        #[test]
        fn default_verify_dispatch_is_error_on_failure() {
            let cfg = JitConfig::default();
            assert_eq!(
                cfg.verify_dispatch,
                DispatchVerifyMode::ErrorOnFailure,
                "JitConfig default must be ErrorOnFailure (#375) so \
                 dispatch-verification failures surface as errors."
            );
        }

        /// AC 1: The `verify_dispatch` field is public and settable.
        #[test]
        fn verify_dispatch_field_is_settable() {
            let cfg = JitConfig {
                verify_dispatch: DispatchVerifyMode::FallbackOnFailure,
                ..JitConfig::default()
            };
            assert_eq!(cfg.verify_dispatch, DispatchVerifyMode::FallbackOnFailure);

            let cfg_off = JitConfig {
                verify_dispatch: DispatchVerifyMode::Off,
                ..JitConfig::default()
            };
            assert_eq!(cfg_off.verify_dispatch, DispatchVerifyMode::Off);
        }

        /// AC 3: Default `JitCompiler` propagates `ErrorOnFailure` into the
        /// underlying pipeline, so a dispatch-failing graph yields
        /// `PipelineError::DispatchVerificationFailed` rather than a silent
        /// CPU-only fallback. Uses the `#[cfg(test)] pipeline()` accessor.
        #[test]
        fn default_jit_propagates_error_mode_into_pipeline() {
            let jit = JitCompiler::new(JitConfig::default());
            let (graph, recs) = bad_fallback_graph();

            let result = jit.pipeline().generate_and_verify_dispatch(&graph, &recs);

            match result {
                Ok(_) => panic!(
                    "Default JitConfig must surface dispatch-verification \
                     failures as errors (#375); bad_fallback_graph should \
                     not pass."
                ),
                Err(PipelineError::DispatchVerificationFailed {
                    violations,
                    summary,
                    report,
                }) => {
                    assert!(violations > 0, "expected at least one violation");
                    assert!(!summary.is_empty(), "expected non-empty summary");
                    assert!(
                        !report.cpu_fallback_ok,
                        "expected the report to flag the missing CPU fallback"
                    );
                }
                Err(other) => {
                    panic!("expected DispatchVerificationFailed, got {other:?}")
                }
            }
        }

        /// Opt-in `FallbackOnFailure` preserves legacy silent-fallback
        /// behaviour end-to-end through the JIT-owned pipeline.
        #[test]
        fn opt_in_fallback_mode_preserves_silent_fallback() {
            let jit = JitCompiler::new(JitConfig {
                verify_dispatch: DispatchVerifyMode::FallbackOnFailure,
                ..JitConfig::default()
            });
            let (graph, recs) = bad_fallback_graph();

            let result = jit.pipeline().generate_and_verify_dispatch(&graph, &recs);
            assert!(
                result.is_ok(),
                "FallbackOnFailure must not surface an error, got {:?}",
                result.err()
            );
        }

        /// `Off` mode bypasses the verifier entirely.
        #[test]
        fn off_mode_skips_verification() {
            let jit = JitCompiler::new(JitConfig {
                verify_dispatch: DispatchVerifyMode::Off,
                ..JitConfig::default()
            });
            let (graph, recs) = bad_fallback_graph();

            let result = jit.pipeline().generate_and_verify_dispatch(&graph, &recs);
            assert!(
                result.is_ok(),
                "Off must not surface an error, got {:?}",
                result.err()
            );
        }
    }

    // =======================================================================
    // JIT-7 runtime hardening: bytes-hash publish check, W^X invariant,
    // RAII mapping ownership, and Drop-bailout leak accounting.
    //
    // These tests are host-arch generic (they run on x86_64 AND aarch64).
    // The aarch64 executions of the code-running assertions are validated on
    // the M-series lane; on this x86 development host they execute natively
    // for x86_64.
    // =======================================================================

    /// Tiny host-native `fn() -> i64 { 42 }` image for publish tests.
    #[cfg(unix)]
    fn jit7_sample_code() -> Vec<u8> {
        #[cfg(target_arch = "x86_64")]
        {
            // mov eax, 42 ; ret
            vec![0xb8, 0x2a, 0x00, 0x00, 0x00, 0xc3]
        }
        #[cfg(target_arch = "aarch64")]
        {
            // movz x0, #42 ; ret
            let mut v = Vec::new();
            v.extend_from_slice(&0xD280_0540u32.to_le_bytes());
            v.extend_from_slice(&0xD65F_03C0u32.to_le_bytes());
            v
        }
        #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
        {
            vec![0u8; 8]
        }
    }

    #[cfg(unix)]
    fn jit7_publish_sample(symbol: &str) -> Result<ExecutableBuffer, JitError> {
        let code = jit7_sample_code();
        let mut symbol_offsets = HashMap::new();
        symbol_offsets.insert(symbol.to_string(), 0u64);
        publish_serialized_buffer(
            &code,
            vec![symbol.to_string()],
            symbol_offsets,
            vec![(symbol.to_string(), 0..code.len() as u64)],
        )
    }

    /// Happy path: the published buffer's hash accessor is bound to the
    /// compiled artifact bytes, the integrity re-check passes, and the code
    /// executes correctly. (aarch64 execution: M-series lane.)
    #[cfg(unix)]
    #[test]
    fn jit7_publish_check_hash_bound_happy_path() {
        if !sys::host_supported() {
            return;
        }
        let code = jit7_sample_code();
        let buf = jit7_publish_sample("f").expect("publish must succeed");
        assert_eq!(
            buf.published_image_sha256(),
            crate::jit_diagnostics::sha256_hex(&code),
            "published_image_sha256 must equal the compiled artifact hash"
        );
        buf.verify_published_code_integrity()
            .expect("fresh published buffer must pass the integrity re-check");
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        {
            let f: extern "C" fn() -> i64 = unsafe {
                buf.get_fn_bound("f")
                    .expect("published symbol must resolve")
                    .into_inner()
            };
            assert_eq!(f(), 42);
        }
    }

    /// THE locked red test (roadmap JIT-7 done-criterion): a single byte
    /// corrupted between the mapping write and the seal must make the
    /// publish FAIL CLOSED with `PublishedBytesHashMismatch` — corrupted
    /// bytes can never surface as an executable pointer.
    #[cfg(unix)]
    #[test]
    fn jit7_publish_check_detects_corrupted_byte_fails_closed() {
        if !sys::host_supported() {
            return;
        }
        publish_test_hooks::CORRUPT_PUBLISHED_BYTE_AT.with(|slot| slot.set(Some(1)));
        let err = jit7_publish_sample("f").expect_err("corrupted publish must fail closed");
        match err {
            JitError::PublishedBytesHashMismatch {
                expected_sha256,
                actual_sha256,
                published_len,
            } => {
                assert_ne!(expected_sha256, actual_sha256);
                assert_eq!(published_len, jit7_sample_code().len());
            }
            other => panic!("expected PublishedBytesHashMismatch, got {other:?}"),
        }
        // The hook is consumed by the failed publish; the next publish is
        // clean and must succeed — the failure path leaves no poisoned state.
        let buf = jit7_publish_sample("f").expect("subsequent clean publish must succeed");
        buf.verify_published_code_integrity()
            .expect("clean buffer verifies");
    }

    /// W^X: the only sanctioned protection states are RW and RX.
    #[test]
    fn jit7_wx_protection_values_are_exclusive() {
        assert!(sys::prot_is_w_xor_x(sys::RW));
        assert!(sys::prot_is_w_xor_x(sys::RX));
        assert!(
            !sys::prot_is_w_xor_x(sys::RW | sys::RX),
            "a simultaneously writable+executable protection must never validate"
        );
    }

    /// W^X: requesting a writable+executable mapping is a hard assertion
    /// failure before any syscall is issued.
    #[cfg(unix)]
    #[test]
    #[should_panic(expected = "W^X violation")]
    fn jit7_wx_mmap_rejects_writable_executable() {
        let _ = unsafe { sys::mmap(sys::PAGE_SIZE, sys::RW | sys::RX) };
    }

    /// W^X: flipping an existing mapping to writable+executable is equally
    /// rejected.
    #[cfg(unix)]
    #[test]
    #[should_panic(expected = "W^X violation")]
    fn jit7_wx_mprotect_rejects_writable_executable() {
        unsafe {
            let size = sys::page_align(16);
            let ptr = sys::mmap(size, sys::RW).expect("mmap failed");
            let result = sys::mprotect(ptr, size, sys::RW | sys::RX);
            // Only reached if the W^X assert regressed; clean up then fail.
            let _ = result;
            sys::munmap(ptr, size);
        }
    }

    /// W^X state machine: an unsealed (still-writable) mapping can never be
    /// released into an `ExecutableBuffer`.
    #[cfg(unix)]
    #[test]
    #[should_panic(expected = "never sealed RX")]
    fn jit7_unsealed_mapping_cannot_publish() {
        if !sys::host_supported() {
            // Keep the should_panic contract meaningful on unsupported hosts.
            panic!("never sealed RX (host unsupported — vacuous)");
        }
        let region = MappedRegion::allocate_rw(sys::page_align(16)).expect("mmap failed");
        let _ = region.into_published_parts();
    }

    /// W^X state machine: the RW->RX flip happens exactly once.
    #[cfg(unix)]
    #[test]
    #[should_panic(expected = "seal_rx_and_verify called twice")]
    fn jit7_double_seal_panics() {
        if !sys::host_supported() {
            panic!("seal_rx_and_verify called twice (host unsupported — vacuous)");
        }
        let mut region = MappedRegion::allocate_rw(sys::page_align(16)).expect("mmap failed");
        // Fresh anonymous pages are zero-filled, so the expected hash is the
        // hash of 16 zero bytes.
        let expected = crate::jit_diagnostics::sha256_hex(&[0u8; 16]);
        region
            .seal_rx_and_verify(16, &expected)
            .expect("first seal of a zero image must verify");
        let _ = region.seal_rx_and_verify(16, &expected);
    }

    /// Sealing against a wrong expected hash fails closed (and the region's
    /// Drop reclaims the mapping — covered by the accounting test below).
    #[cfg(unix)]
    #[test]
    fn jit7_seal_with_wrong_expected_hash_fails_closed() {
        if !sys::host_supported() {
            return;
        }
        let mut region = MappedRegion::allocate_rw(sys::page_align(16)).expect("mmap failed");
        let err = region
            .seal_rx_and_verify(16, "not-a-real-hash")
            .expect_err("hash mismatch must fail closed");
        assert!(matches!(err, JitError::PublishedBytesHashMismatch { .. }));
    }

    /// A fail-closed Drop bail-out (#734 inconsistent extent) must be
    /// COUNTED, never silent: leaked executable mappings are the documented
    /// accumulation failure mode (docs/jit-parallel-race-2026-06-29.md).
    #[cfg(unix)]
    #[test]
    fn jit7_drop_bailout_is_counted_not_silent() {
        let size = sys::page_align(16);
        let memory = unsafe { sys::mmap(size, sys::RW).expect("mmap failed") };
        let before = executable_buffer_unmap_bailout_count();
        let buf = ExecutableBuffer {
            memory,
            len: size,
            // Shadow disagrees with primary and the cookie validates
            // neither: allocation_len_for_unmap() returns 0 -> bail-out.
            len_shadow: size + sys::PAGE_SIZE,
            allocation_cookie: 0xdead,
            code_len: 16,
            published_len: 16,
            published_image_sha256: String::new(),
            publication: JitPublicationContract::unpublished_for_tests(),
            windows_unwind: WindowsJitUnwindRegistration,
            function_ranges: Vec::new(),
            symbol_offsets: HashMap::new(),
            canonical_symbols: Vec::new(),
            counters: HashMap::new(),
            timing_cells: HashMap::new(),
            timing_state: None,
            certificates: HashMap::new(),
            proof_optimization_certificates: Vec::new(),
        };
        drop(buf);
        assert!(
            executable_buffer_unmap_bailout_count() > before,
            "a Drop bail-out must increment the leak counter"
        );
        // The bail-out deliberately leaked `memory`; reclaim it manually so
        // the test process stays clean.
        unsafe { sys::munmap(memory, size) };
    }

    /// A buffer with no publish-time hash must FAIL the integrity re-check
    /// (fail-closed), never vacuously pass.
    #[cfg(unix)]
    #[test]
    fn jit7_integrity_recheck_fails_closed_without_publish_hash() {
        let buf = make_buf_with_symbols(&["f"]);
        assert!(
            matches!(
                buf.verify_published_code_integrity(),
                Err(JitError::PublishedBytesHashMismatch { .. })
            ),
            "a hash-less buffer must not pass the integrity re-check"
        );
    }

    /// Repeated FAILED publishes must release every byte owned by the RAII
    /// `MappedRegion` on every fail-closed path. Thread-local ownership
    /// accounting makes the assertion exact and immune to unrelated parallel
    /// tests growing process VM arenas.
    #[cfg(target_os = "macos")]
    #[test]
    fn jit7_failed_publishes_do_not_accumulate_mappings() {
        if !sys::host_supported() {
            return;
        }

        let corrupt_publish_must_fail = || {
            publish_test_hooks::CORRUPT_PUBLISHED_BYTE_AT.with(|slot| slot.set(Some(0)));
            match jit7_publish_sample("f") {
                Err(JitError::PublishedBytesHashMismatch { .. }) => {}
                Err(other) => {
                    panic!("corrupted publish must fail with the hash check, got {other:?}")
                }
                Ok(_) => panic!("corrupted publish must fail closed, but it published"),
            }
        };

        let before = mapped_region_owned_bytes_for_tests();
        for _ in 0..128 {
            corrupt_publish_must_fail();
            assert_eq!(
                mapped_region_owned_bytes_for_tests(),
                before,
                "a failed publish retained MappedRegion ownership"
            );
        }
    }
}
