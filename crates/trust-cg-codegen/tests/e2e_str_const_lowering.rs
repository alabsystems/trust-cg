//! R3 STAGE 1 — &'static str CONSTANT LOWERING (thread R3-A): the first stage
//! of the string-gap program pinned by round 1's T3 probes. Gap (1) — a
//! `&'static str` fat-pointer CONSTANT as a call arg / fat-local initializer
//! ("call arg constant of non-scalar type ref" / "fat-pointer dst from
//! unmodelable rvalue") — is now LOWERED by the trust-ir frontend change on
//! branch `r3-str-lowering` (worktree diff against trust-ir 9e4f5d2,
//! frontend/src/mir_lower.rs only), and this file proves the machine code
//! trust-cg JITs from those modules executes IDENTICALLY to native Rust.
//!
//! THE LOWERING (documented at `str_const_bytes` in mir_lower.rs): each
//! DISTINCT literal is materialized ONCE per function in the ENTRY block as
//!   * an IMMORTAL heap byte image (`heap_alloc(I8, len, align 1, RustHeap)` +
//!     one byte Store per literal byte) — heap, never freed, so escaping
//!     references (returned literals!) stay valid like `&'static` rodata;
//!     the same `__rust_alloc` trust boundary as the landed Arc::new lowering;
//!   * a 16-byte (ptr,len) FAT-PAIR SLOT ([Ptr at +0, U64 len at +8]) whose
//!     address is the AggByRef call-arg value — exactly the convention a
//!     lowered callee models its own fat `&str` param with.
//!     WHY NOT MODULE GLOBALS: trust-ir + the OBJECT path support rodata globals
//!     (`Global`/`GlobalAddr`, e2e_aarch64_read_global.rs), but the in-process JIT
//!     that runs every verification round-trip resolves ONLY Branch26 code fixups
//!     (`jit.rs::patch_fixup` = `patch_branch26`); an ADRP/Page21 DATA relocation
//!     is unresolvable there today. BACKEND NEXT-STEP (owner item): teach the JIT
//!     data relocations, then move literals to true module globals.
//!
//! MODELED BOUNDARIES (each also documented in the slice + the frontend
//! change):
//!   * ADDRESS IDENTITY / ALLOCATION COUNT: native puts a literal in rodata
//!     (one stable address, zero allocations); the lowering allocates one
//!     leaked image per (function, literal) per invocation. Bytes + length are
//!     exact; a program comparing literal ADDRESSES or counting allocator
//!     traffic would diverge — nothing verified does either.
//!   * `String::from` / `String::len` (std, not crate-local) lower to extern
//!     decls; this file binds FAITHFUL host shims that call the REAL std fns
//!     through the module's synthesized ABI (sret-String + pair-ptr; thin
//!     &String -> u64). The from-shim also CAPTURES the &str it received so
//!     the test asserts the exact bytes that crossed the extern boundary.
//!   * The String local's drop is not emitted (landed RUNG-8b
//!     purely-deallocating-drop model: the String leaks; return values
//!     unaffected).
//!
//! Slice (verbatim, with regen instructions):
//!   tests/slices/str_const_lowering_slice.rs
//! Each embedded module below was emitted from it with the r3-str-lowering
//! frontend (validate_module = 0 error(s), re-parse OK for ALL FIVE — no
//! const-shift divergence class in these bodies) and is asserted 0-error again
//! at test time. NO-DRIFT: the frontend change re-emits
//! slices/clean_expr_whnf_slice.rs BYTE-IDENTICAL to _baseline_whnf.tir
//! (115588 bytes) and clean_decl_universe_slice.rs / trust_logimm_slice.rs
//! byte-identical to their landed embedded consts.
//!
//! REC-NAME DE-MODELING STATUS (the T3 prize): still BLOCKED for full
//! in-module construction, but stage 1 moved the frontier. The production
//! path is `Name::from_string(&format!("{name}.rec"))` (name.rs:557/576):
//! `format!` stays gap (4), and `from_string_uncached`'s split('.') fold
//! stays gap (3) (str::Bytes/Split element types), with `acc.str(part)`
//! needing in-module str-byte access (gap (2) beyond the as_bytes-sret shape
//! verified here) for the KaniHasher word. STAGE-2 NEXT STEP: lower the
//! remaining &str->bytes deref rvalue class + str-iterator element types;
//! then `from_string_uncached("Tree.rec")` UNROLLED over literal parts
//! (anon().str("Tree").str("rec")) runs in-module with only the Arc<str>
//! allocation shimmed, and the mutual-recursor slice's pre-interned RecPair
//! table can be replaced by in-module literal Name construction.
//!
//! REGEN (per module):
//!   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//!   cd <r3-str worktree>/frontend && env -u RUSTUP_TOOLCHAIN \
//!     RUSTC=$S/bin/rustc \
//!     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//!     $S/bin/cargo run --bin trust_ir_mir -- \
//!     ../../trust-cg/crates/trust-cg-codegen/tests/slices/str_const_lowering_slice.rs \
//!     --crate-type=lib --mir-emit-closure <root> <out.tir>
//!
//! HANG SAFETY: every JIT compile+execute runs inside a WATCHDOG WORKER
//! THREAD; the main thread bounds the wait with recv_timeout and PANICS with
//! the stalled step's name instead of hanging the suite (the JIT buffer moves
//! into — and on a hang is leaked with — the worker, so a hung thread never
//! executes freed machine code).
//!
//! COVERAGE NOTE: gated to aarch64 (the JIT target); on any other host this
//! file compiles to ZERO tests. Run tests ONE AT A TIME
//! (`-- --exact <name> --test-threads=1`): the JIT engine is not thread-safe
//! at suite scale (see jit-parallel-race-2026-06-29.md).

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::sync::Mutex;
use std::sync::mpsc;
use std::time::Duration;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

// ── shared harness ──────────────────────────────────────────────────────────

/// Parse, VALIDATE (must be 0 errors — all five modules emitted clean), and
/// JIT one embedded module; returns the buffer (keep it alive while calling
/// fn pointers bound from it).
fn jit_module(
    text: &str,
    what: &str,
    externs: &HashMap<String, *const u8>,
) -> trust_cg_codegen::jit::ExecutableBuffer {
    let module = trust_ir::parser::parse_module(text)
        .unwrap_or_else(|e| panic!("MIR-emitted `{what}` trust-ir text must parse: {e:?}"));
    let errs = trust_ir_build::validate_module(&module);
    assert!(
        errs.is_empty(),
        "MIR-emitted `{what}` must validate clean (emitted with 0 errors): {errs:?}"
    );
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .compile_module_to_jit(&module, externs)
        .unwrap_or_else(|e| panic!("trust-cg JIT compile of MIR-emitted `{what}` failed: {e:?}"))
        .buffer
}

fn bind(buffer: &trust_cg_codegen::jit::ExecutableBuffer, sym: &str) -> *const u8 {
    buffer
        .get_fn_ptr_bound(sym)
        .unwrap_or_else(|| panic!("JIT symbol `{sym}` not found"))
        .as_ptr()
}

/// The module-side fat pair layout: [data ptr at +0, byte length at +8] — the
/// exact lane discipline of the frontend's 16-byte fat slots and sret returns.
#[repr(C)]
#[derive(Clone, Copy)]
struct FatPair {
    ptr: *const u8,
    len: u64,
}

/// The Rust-heap allocator every module's `heap_alloc rust_heap` lowers to
/// (`__rust_alloc(size, align)`), forwarding to the system allocator — the
/// same shim the landed heap_alloc round-trips bind.
extern "C" fn shim_rust_alloc(size: usize, align: usize) -> *mut u8 {
    unsafe {
        let layout = std::alloc::Layout::from_size_align(size, align).expect("valid layout");
        std::alloc::alloc(layout)
    }
}

fn base_externs() -> HashMap<String, *const u8> {
    let mut e: HashMap<String, *const u8> = HashMap::new();
    e.insert("__rust_alloc".to_string(), shim_rust_alloc as *const u8);
    e
}

/// Run `f` (JIT compile + execute + read-back) on a WATCHDOG worker thread;
/// panic loudly if it does not complete within the bound. The worker owns the
/// JIT buffer; a hung worker is leaked, never freed-under-execution.
fn run_with_watchdog<T: Send + 'static>(what: &str, f: impl FnOnce() -> T + Send + 'static) -> T {
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(f());
    });
    match rx.recv_timeout(Duration::from_secs(180)) {
        Ok(v) => v,
        Err(_) => panic!("WATCHDOG: `{what}` did not complete within 180s (JIT hang?)"),
    }
}

// ── native oracles (verbatim transcriptions of the slice's crate-local fns) ─

fn native_ident_str(s: &str) -> &str {
    s
}

fn native_pick_str<'a>(a: &'a str, b: &'a str, which: u64) -> &'a str {
    if which == 0 { a } else { b }
}

fn native_from_len() -> u64 {
    let s = String::from("Tree.rec");
    s.len() as u64
}

// ═══════════════════════════════════════════════════════════════════════════
// Embedded MIR-closure emits (verbatim r3-str-lowering frontend output)
// ═══════════════════════════════════════════════════════════════════════════

/// VERBATIM `--mir-emit-closure str_const_ident_root` emit of
/// tests/slices/str_const_lowering_slice.rs (r3-str-lowering frontend).
/// Emit reported: 1619 bytes; 2 closure members (root + ident_str);
/// validate_module = 0 error(s); re-parse OK.
const IDENT_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::str_const_ident_root"
target "aarch64-apple-darwin" 8 little
file 0 "str_const_lowering_slice.rs"

functy.0 = (ptr) -> ()

functy.1 = (ptr, ptr) -> ()

fn @str_const_ident_root(functy.0) {
bb0(%0: ptr):
    %1 = alloca (i64, i64), align 8
    %2 = const i64 8
    %3 = heap_alloc rust_heap i8, %2, align 1
    %4 = const u8 84
    store u8 %4, ptr %3
    %5 = const i64 1
    %6 = gep i8, ptr %3, %5
    %7 = const u8 114
    store u8 %7, ptr %6
    %8 = const i64 2
    %9 = gep i8, ptr %3, %8
    %10 = const u8 101
    store u8 %10, ptr %9
    %11 = const i64 3
    %12 = gep i8, ptr %3, %11
    %13 = const u8 101
    store u8 %13, ptr %12
    %14 = const i64 4
    %15 = gep i8, ptr %3, %14
    %16 = const u8 46
    store u8 %16, ptr %15
    %17 = const i64 5
    %18 = gep i8, ptr %3, %17
    %19 = const u8 114
    store u8 %19, ptr %18
    %20 = const i64 6
    %21 = gep i8, ptr %3, %20
    %22 = const u8 101
    store u8 %22, ptr %21
    %23 = const i64 7
    %24 = gep i8, ptr %3, %23
    %25 = const u8 99
    store u8 %25, ptr %24
    %26 = alloca (i64, i64), align 8
    store ptr %3, ptr %26
    %27 = const i64 8
    %28 = gep i8, ptr %26, %27
    %29 = const u64 8
    store u64 %29, ptr %28
    store ptr %3, ptr %1
    %30 = const i64 8
    %31 = gep i8, ptr %1, %30
    %32 = const u64 8
    store u64 %32, ptr %31
    call @func.1(%0, %1)
    br bb1
bb1:
    ret
}

fn @ident_str(functy.1) {
bb0(%0: ptr, %1: ptr):
    %2 = load i64, ptr %1
    store i64 %2, ptr %0
    %3 = const i64 8
    %4 = gep i8, ptr %1, %3
    %5 = const i64 8
    %6 = gep i8, ptr %0, %5
    %7 = load i64, ptr %4
    store i64 %7, ptr %6
    ret
}"#;

/// VERBATIM `--mir-emit-closure str_const_pick_root` emit (same slice/
/// frontend). Emit reported: 3362 bytes; 2 closure members (root + pick_str);
/// validate_module = 0 error(s); re-parse OK. TWO distinct literals ("Tree.rec"
/// image + "Forest.rec" image) materialized in the root's entry block.
const PICK_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::str_const_pick_root"
target "aarch64-apple-darwin" 8 little
file 0 "str_const_lowering_slice.rs"

functy.0 = (ptr, u64) -> ()

functy.1 = (ptr, ptr, ptr, u64) -> ()

fn @str_const_pick_root(functy.0) {
bb0(%0: ptr, %1: u64):
    %2 = alloca (i64, i64), align 8
    %3 = alloca (i64, i64), align 8
    %4 = const i64 8
    %5 = heap_alloc rust_heap i8, %4, align 1
    %6 = const u8 84
    store u8 %6, ptr %5
    %7 = const i64 1
    %8 = gep i8, ptr %5, %7
    %9 = const u8 114
    store u8 %9, ptr %8
    %10 = const i64 2
    %11 = gep i8, ptr %5, %10
    %12 = const u8 101
    store u8 %12, ptr %11
    %13 = const i64 3
    %14 = gep i8, ptr %5, %13
    %15 = const u8 101
    store u8 %15, ptr %14
    %16 = const i64 4
    %17 = gep i8, ptr %5, %16
    %18 = const u8 46
    store u8 %18, ptr %17
    %19 = const i64 5
    %20 = gep i8, ptr %5, %19
    %21 = const u8 114
    store u8 %21, ptr %20
    %22 = const i64 6
    %23 = gep i8, ptr %5, %22
    %24 = const u8 101
    store u8 %24, ptr %23
    %25 = const i64 7
    %26 = gep i8, ptr %5, %25
    %27 = const u8 99
    store u8 %27, ptr %26
    %28 = alloca (i64, i64), align 8
    store ptr %5, ptr %28
    %29 = const i64 8
    %30 = gep i8, ptr %28, %29
    %31 = const u64 8
    store u64 %31, ptr %30
    %32 = const i64 10
    %33 = heap_alloc rust_heap i8, %32, align 1
    %34 = const u8 70
    store u8 %34, ptr %33
    %35 = const i64 1
    %36 = gep i8, ptr %33, %35
    %37 = const u8 111
    store u8 %37, ptr %36
    %38 = const i64 2
    %39 = gep i8, ptr %33, %38
    %40 = const u8 114
    store u8 %40, ptr %39
    %41 = const i64 3
    %42 = gep i8, ptr %33, %41
    %43 = const u8 101
    store u8 %43, ptr %42
    %44 = const i64 4
    %45 = gep i8, ptr %33, %44
    %46 = const u8 115
    store u8 %46, ptr %45
    %47 = const i64 5
    %48 = gep i8, ptr %33, %47
    %49 = const u8 116
    store u8 %49, ptr %48
    %50 = const i64 6
    %51 = gep i8, ptr %33, %50
    %52 = const u8 46
    store u8 %52, ptr %51
    %53 = const i64 7
    %54 = gep i8, ptr %33, %53
    %55 = const u8 114
    store u8 %55, ptr %54
    %56 = const i64 8
    %57 = gep i8, ptr %33, %56
    %58 = const u8 101
    store u8 %58, ptr %57
    %59 = const i64 9
    %60 = gep i8, ptr %33, %59
    %61 = const u8 99
    store u8 %61, ptr %60
    %62 = alloca (i64, i64), align 8
    store ptr %33, ptr %62
    %63 = const i64 8
    %64 = gep i8, ptr %62, %63
    %65 = const u64 10
    store u64 %65, ptr %64
    store ptr %5, ptr %2
    %66 = const i64 8
    %67 = gep i8, ptr %2, %66
    %68 = const u64 8
    store u64 %68, ptr %67
    store ptr %33, ptr %3
    %69 = const i64 8
    %70 = gep i8, ptr %3, %69
    %71 = const u64 10
    store u64 %71, ptr %70
    call @func.1(%0, %2, %3, %1)
    br bb1
bb1:
    ret
}

fn @pick_str(functy.1) {
bb0(%0: ptr, %1: ptr, %2: ptr, %3: u64):
    %4 = const u64 0
    %5 = icmp eq u64 %3, %4
    condbr %5, bb1, bb2
bb1:
    %6 = load i64, ptr %1
    store i64 %6, ptr %0
    %7 = const i64 8
    %8 = gep i8, ptr %1, %7
    %9 = const i64 8
    %10 = gep i8, ptr %0, %9
    %11 = load i64, ptr %8
    store i64 %11, ptr %10
    br bb3
bb2:
    %12 = load i64, ptr %2
    store i64 %12, ptr %0
    %13 = const i64 8
    %14 = gep i8, ptr %2, %13
    %15 = const i64 8
    %16 = gep i8, ptr %0, %15
    %17 = load i64, ptr %14
    store i64 %17, ptr %16
    br bb3
bb3:
    ret
}"#;

/// VERBATIM `--mir-emit-closure str_const_local_root` emit (same slice/
/// frontend). Emit reported: 1721 bytes; 2 closure members; validate_module =
/// 0 error(s); re-parse OK. Exercises the fat-LOCAL `Use(Constant)` assign arm
/// (`let s: &str = "Quot.lift"`), then the ordinary fat PLACE call arg.
const LOCAL_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::str_const_local_root"
target "aarch64-apple-darwin" 8 little
file 0 "str_const_lowering_slice.rs"

functy.0 = (ptr) -> ()

functy.1 = (ptr, ptr) -> ()

fn @str_const_local_root(functy.0) {
bb0(%0: ptr):
    %1 = alloca (i64, i64), align 8
    %2 = const i64 9
    %3 = heap_alloc rust_heap i8, %2, align 1
    %4 = const u8 81
    store u8 %4, ptr %3
    %5 = const i64 1
    %6 = gep i8, ptr %3, %5
    %7 = const u8 117
    store u8 %7, ptr %6
    %8 = const i64 2
    %9 = gep i8, ptr %3, %8
    %10 = const u8 111
    store u8 %10, ptr %9
    %11 = const i64 3
    %12 = gep i8, ptr %3, %11
    %13 = const u8 116
    store u8 %13, ptr %12
    %14 = const i64 4
    %15 = gep i8, ptr %3, %14
    %16 = const u8 46
    store u8 %16, ptr %15
    %17 = const i64 5
    %18 = gep i8, ptr %3, %17
    %19 = const u8 108
    store u8 %19, ptr %18
    %20 = const i64 6
    %21 = gep i8, ptr %3, %20
    %22 = const u8 105
    store u8 %22, ptr %21
    %23 = const i64 7
    %24 = gep i8, ptr %3, %23
    %25 = const u8 102
    store u8 %25, ptr %24
    %26 = const i64 8
    %27 = gep i8, ptr %3, %26
    %28 = const u8 116
    store u8 %28, ptr %27
    %29 = alloca (i64, i64), align 8
    store ptr %3, ptr %29
    %30 = const i64 8
    %31 = gep i8, ptr %29, %30
    %32 = const u64 9
    store u64 %32, ptr %31
    store ptr %3, ptr %1
    %33 = const i64 8
    %34 = gep i8, ptr %1, %33
    %35 = const u64 9
    store u64 %35, ptr %34
    call @func.1(%0, %1)
    br bb1
bb1:
    ret
}

fn @ident_str(functy.1) {
bb0(%0: ptr, %1: ptr):
    %2 = load i64, ptr %1
    store i64 %2, ptr %0
    %3 = const i64 8
    %4 = gep i8, ptr %1, %3
    %5 = const i64 8
    %6 = gep i8, ptr %0, %5
    %7 = load i64, ptr %4
    store i64 %7, ptr %6
    ret
}"#;

/// VERBATIM `--mir-emit-closure str_const_from_len_root` emit (same slice/
/// frontend) — the original T3 probe (1) shape (`String::from("Tree.rec")`
/// -> len; probe preserved at <dev-scratch>/t3-mutual/probe_string_e.rs
/// emits IDENTICALLY modulo crate-name mangling). Emit reported: 1618 bytes;
/// 1 closure member + 2 extern decls (`String::from`, `String::len`);
/// validate_module = 0 error(s); re-parse OK.
const FROM_LEN_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::str_const_from_len_root"
target "aarch64-apple-darwin" 8 little
file 0 "str_const_lowering_slice.rs"

functy.0 = (ptr, ptr) -> ()

functy.1 = (ptr) -> (u64)

functy.2 = () -> (u64)

fn @_RNvXsK_NtCskTzINo8ZBH9_5alloc6stringNtB5_6StringINtNtCs2EYQwhfuABO_4core7convert4FromReE4fromCs3P47iBr1uFy_24str_const_lowering_slice(functy.0) {
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc6stringNtB2_6String3lenCs3P47iBr1uFy_24str_const_lowering_slice(functy.1) {
}

fn @str_const_from_len_root(functy.2) {
bb0:
    %2 = alloca (i64, i64, i64), align 8
    %3 = const i64 8
    %4 = heap_alloc rust_heap i8, %3, align 1
    %5 = const u8 84
    store u8 %5, ptr %4
    %6 = const i64 1
    %7 = gep i8, ptr %4, %6
    %8 = const u8 114
    store u8 %8, ptr %7
    %9 = const i64 2
    %10 = gep i8, ptr %4, %9
    %11 = const u8 101
    store u8 %11, ptr %10
    %12 = const i64 3
    %13 = gep i8, ptr %4, %12
    %14 = const u8 101
    store u8 %14, ptr %13
    %15 = const i64 4
    %16 = gep i8, ptr %4, %15
    %17 = const u8 46
    store u8 %17, ptr %16
    %18 = const i64 5
    %19 = gep i8, ptr %4, %18
    %20 = const u8 114
    store u8 %20, ptr %19
    %21 = const i64 6
    %22 = gep i8, ptr %4, %21
    %23 = const u8 101
    store u8 %23, ptr %22
    %24 = const i64 7
    %25 = gep i8, ptr %4, %24
    %26 = const u8 99
    store u8 %26, ptr %25
    %27 = alloca (i64, i64), align 8
    store ptr %4, ptr %27
    %28 = const i64 8
    %29 = gep i8, ptr %27, %28
    %30 = const u64 8
    store u64 %30, ptr %29
    call @func.0(%2, %27)
    br bb1
bb1:
    %31 = call @func.1(%2)
    br bb2(%31)
bb2(%0: u64):
    br bb3(%0)
bb3(%1: u64):
    ret %1
}"#;

// ═══════════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════════

/// Root (a): `ident_str("Tree.rec")` — the literal crosses as an AggByRef pair
/// into an IN-MODULE fat-param callee and returns through the fat sret. The
/// harness reads the returned (ptr,len) and compares the pointed-to BYTES —
/// verifying the heap image's exact contents, the pair's length lane, and the
/// fat plumbing end-to-end. The image is immortal heap, so the read after
/// return is sound (this is the escape shape stack rodata would dangle on).
#[test]
fn str_const_ident_native_eq_jit() {
    let (jit_bytes, jit_len) = run_with_watchdog("ident_root JIT", || {
        let buffer = jit_module(IDENT_TRUST_IR, "str_const_ident_root", &base_externs());
        let f: extern "C" fn(*mut FatPair) =
            unsafe { std::mem::transmute(bind(&buffer, "str_const_ident_root")) };
        let mut out = FatPair {
            ptr: std::ptr::null(),
            len: 0,
        };
        f(&mut out);
        assert!(!out.ptr.is_null(), "JIT returned a NULL data pointer");
        let bytes = unsafe { std::slice::from_raw_parts(out.ptr, out.len as usize) }.to_vec();
        (bytes, out.len)
    });

    let native = native_ident_str("Tree.rec");
    assert_eq!(
        jit_len,
        native.len() as u64,
        "returned length lane != native"
    );
    assert_eq!(
        jit_bytes.as_slice(),
        native.as_bytes(),
        "returned bytes != native \"Tree.rec\""
    );

    // NEGATIVE CONTROLS (armed): a wrong-BYTE expectation and a wrong-LENGTH
    // expectation must both DISAGREE with the JIT result — the comparisons
    // above are sensitive to every byte and to the metadata lane.
    assert_ne!(
        jit_bytes.as_slice(),
        b"Tree.reX".as_slice(),
        "negative control must FAIL: a corrupted last byte should disagree with the JIT"
    );
    assert_ne!(
        jit_len, 7,
        "negative control must FAIL: a wrong length should disagree with the JIT"
    );
}

/// Root (b): `pick_str("Tree.rec", "Forest.rec", which)` — TWO distinct
/// literals materialized in one entry block, runtime-branch-selected, swept
/// over which ∈ {0, 1, 2, 99} against the native oracle.
#[test]
fn str_const_pick_native_eq_jit() {
    let results = run_with_watchdog("pick_root JIT sweep", || {
        let buffer = jit_module(PICK_TRUST_IR, "str_const_pick_root", &base_externs());
        let f: extern "C" fn(*mut FatPair, u64) =
            unsafe { std::mem::transmute(bind(&buffer, "str_const_pick_root")) };
        let mut out_rows: Vec<(u64, Vec<u8>, u64)> = Vec::new();
        for which in [0u64, 1, 2, 99] {
            let mut out = FatPair {
                ptr: std::ptr::null(),
                len: 0,
            };
            f(&mut out, which);
            assert!(!out.ptr.is_null(), "JIT returned NULL for which={which}");
            let bytes = unsafe { std::slice::from_raw_parts(out.ptr, out.len as usize) }.to_vec();
            out_rows.push((which, bytes, out.len));
        }
        out_rows
    });

    for (which, jit_bytes, jit_len) in &results {
        let native = native_pick_str("Tree.rec", "Forest.rec", *which);
        assert_eq!(
            *jit_len,
            native.len() as u64,
            "which={which}: returned length lane != native"
        );
        assert_eq!(
            jit_bytes.as_slice(),
            native.as_bytes(),
            "which={which}: returned bytes != native"
        );
    }

    // NEGATIVE CONTROL (armed): the CROSSED expectation — which=0 must NOT
    // match "Forest.rec" — proves the branch actually selects between the two
    // materialized images (a lowering that collapsed them would pass the
    // positive checks for one arm only).
    let (_, w0_bytes, _) = &results[0];
    assert_ne!(
        w0_bytes.as_slice(),
        b"Forest.rec".as_slice(),
        "negative control must FAIL: which=0 returning the OTHER literal should disagree"
    );
}

/// Root (c): `let s: &str = "Quot.lift"; ident_str(s)` — the literal lands in
/// a fat LOCAL first (the `Use(Constant)` fat-destination assign arm), then
/// flows to the in-module callee as an ordinary fat PLACE arg.
#[test]
fn str_const_local_native_eq_jit() {
    let (jit_bytes, jit_len) = run_with_watchdog("local_root JIT", || {
        let buffer = jit_module(LOCAL_TRUST_IR, "str_const_local_root", &base_externs());
        let f: extern "C" fn(*mut FatPair) =
            unsafe { std::mem::transmute(bind(&buffer, "str_const_local_root")) };
        let mut out = FatPair {
            ptr: std::ptr::null(),
            len: 0,
        };
        f(&mut out);
        assert!(!out.ptr.is_null(), "JIT returned a NULL data pointer");
        let bytes = unsafe { std::slice::from_raw_parts(out.ptr, out.len as usize) }.to_vec();
        (bytes, out.len)
    });

    let native = native_ident_str("Quot.lift");
    assert_eq!(
        jit_len,
        native.len() as u64,
        "returned length lane != native"
    );
    assert_eq!(
        jit_bytes.as_slice(),
        native.as_bytes(),
        "returned bytes != native \"Quot.lift\""
    );

    // NEGATIVE CONTROL (armed): a same-length single-byte corruption must
    // disagree.
    assert_ne!(
        jit_bytes.as_slice(),
        b"Quot.lifT".as_slice(),
        "negative control must FAIL: a corrupted byte should disagree with the JIT"
    );
}

/// The bytes the `String::from` SHIM observed crossing the extern boundary —
/// captured so the test can assert the exact literal content arrived (not just
/// the final length). Reset per test run; guarded because the shim is
/// `extern "C"` with no other channel back.
static FROM_SHIM_SAW: Mutex<Option<String>> = Mutex::new(None);

/// FAITHFUL host shim for the module's `String::from` extern
/// (synthesized ABI: sret `*mut String` + `*const FatPair`): reconstructs the
/// `&str` from the pair, CAPTURES it, and calls the REAL `String::from`,
/// writing the result through the sret pointer — byte layout of the sret slot
/// is the module's 24-byte (i64,i64,i64) String alloca = native String.
extern "C" fn shim_string_from(sret: *mut String, pair: *const FatPair) {
    unsafe {
        let p = *pair;
        let s = std::str::from_utf8(std::slice::from_raw_parts(p.ptr, p.len as usize))
            .expect("shim received non-UTF8 bytes — a corrupted literal image");
        *FROM_SHIM_SAW.lock().unwrap() = Some(s.to_string());
        std::ptr::write(sret, String::from(s));
    }
}

/// FAITHFUL host shim for the module's `String::len` extern (thin `&String` ->
/// u64): calls the real len.
extern "C" fn shim_string_len(s: *const String) -> u64 {
    unsafe { (&*s).len() as u64 }
}

/// Root (d): the ORIGINAL T3 probe (1) shape — `String::from("Tree.rec")` ->
/// `s.len()`. The literal's (ptr,len) pair crosses the extern boundary into
/// the REAL `String::from` (which copies the image bytes into a heap String);
/// the test asserts native == JIT on the length AND that the exact bytes
/// "Tree.rec" arrived at the shim.
#[test]
fn str_const_from_len_native_eq_jit() {
    *FROM_SHIM_SAW.lock().unwrap() = None;

    let jit = run_with_watchdog("from_len_root JIT", || {
        let mut externs = base_externs();
        // Extern symbol names read verbatim from the emitted module (v0
        // mangling; instantiating crate = the slice crate).
        externs.insert(
            "_RNvXsK_NtCskTzINo8ZBH9_5alloc6stringNtB5_6StringINtNtCs2EYQwhfuABO_4core7convert4FromReE4fromCs3P47iBr1uFy_24str_const_lowering_slice".to_string(),
            shim_string_from as *const u8,
        );
        externs.insert(
            "_RNvMNtCskTzINo8ZBH9_5alloc6stringNtB2_6String3lenCs3P47iBr1uFy_24str_const_lowering_slice".to_string(),
            shim_string_len as *const u8,
        );
        let buffer = jit_module(FROM_LEN_TRUST_IR, "str_const_from_len_root", &externs);
        let f: extern "C" fn() -> u64 =
            unsafe { std::mem::transmute(bind(&buffer, "str_const_from_len_root")) };
        f()
    });

    let native = native_from_len();
    assert_eq!(
        jit, native,
        "String::from(\"Tree.rec\").len(): native != JIT"
    );

    let saw = FROM_SHIM_SAW.lock().unwrap().clone();
    assert_eq!(
        saw.as_deref(),
        Some("Tree.rec"),
        "the String::from shim must observe the EXACT literal bytes crossing the extern boundary"
    );

    // NEGATIVE CONTROL (armed): a corrupted oracle must disagree.
    assert_ne!(
        jit,
        native + 1,
        "negative control must FAIL: an off-by-one length oracle should disagree with the JIT"
    );
}

/// VERBATIM `--mir-emit-closure str_const_hash_root` emit (same slice/
/// frontend) — the T3 PROBE A2 shape (String::new + push_str x2 + as_bytes +
/// index-loop byte hash). Before R3 stage 1 this whole body failed at the
/// push_str CONST ARGS (gap (1)); now the hash loop — PtrMetadata bounds
/// checks, slice indexing through the as_bytes sret pair, the wrapping-arith
/// calls — lowers with the std fns as externs. Emit reported: 3774 bytes;
/// 1 closure member + 5 extern decls; validate_module = 0 error(s);
/// re-parse OK. (Gap (2) FELL OUT NATURALLY for this String->as_bytes shape:
/// the fat RETURN crosses as an sret pair; the standalone `&str`->bytes deref
/// rvalue class remains open.)
const HASH_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::str_const_hash_root"
target "aarch64-apple-darwin" 8 little
file 0 "str_const_lowering_slice.rs"

functy.0 = (ptr) -> ()

functy.1 = (ptr, ptr) -> ()

functy.2 = (ptr, ptr) -> ()

functy.3 = (u64, u64) -> (u64)

functy.4 = (u64, u64) -> (u64)

functy.5 = () -> (u64)

fn @_RNvMNtCskTzINo8ZBH9_5alloc6stringNtB2_6String3newCs3P47iBr1uFy_24str_const_lowering_slice(functy.0) {
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc6stringNtB2_6String8push_strCs3P47iBr1uFy_24str_const_lowering_slice(functy.1) {
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc6stringNtB2_6String8as_bytesCs3P47iBr1uFy_24str_const_lowering_slice(functy.2) {
}

fn @_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_mul(functy.3) {
}

fn @_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_add(functy.4) {
}

fn @str_const_hash_root(functy.5) {
bb0:
    %14 = alloca (i64, i64, i64), align 8
    %15 = alloca (i64, i64), align 8
    %16 = alloca (i64, i64), align 8
    %17 = alloca (i64, i64), align 8
    %18 = alloca (i64, i64), align 8
    %19 = const i64 4
    %20 = heap_alloc rust_heap i8, %19, align 1
    %21 = const u8 84
    store u8 %21, ptr %20
    %22 = const i64 1
    %23 = gep i8, ptr %20, %22
    %24 = const u8 114
    store u8 %24, ptr %23
    %25 = const i64 2
    %26 = gep i8, ptr %20, %25
    %27 = const u8 101
    store u8 %27, ptr %26
    %28 = const i64 3
    %29 = gep i8, ptr %20, %28
    %30 = const u8 101
    store u8 %30, ptr %29
    %31 = alloca (i64, i64), align 8
    store ptr %20, ptr %31
    %32 = const i64 8
    %33 = gep i8, ptr %31, %32
    %34 = const u64 4
    store u64 %34, ptr %33
    %35 = const i64 4
    %36 = heap_alloc rust_heap i8, %35, align 1
    %37 = const u8 46
    store u8 %37, ptr %36
    %38 = const i64 1
    %39 = gep i8, ptr %36, %38
    %40 = const u8 114
    store u8 %40, ptr %39
    %41 = const i64 2
    %42 = gep i8, ptr %36, %41
    %43 = const u8 101
    store u8 %43, ptr %42
    %44 = const i64 3
    %45 = gep i8, ptr %36, %44
    %46 = const u8 99
    store u8 %46, ptr %45
    %47 = alloca (i64, i64), align 8
    store ptr %36, ptr %47
    %48 = const i64 8
    %49 = gep i8, ptr %47, %48
    %50 = const u64 4
    store u64 %50, ptr %49
    call @func.0(%14)
    br bb1
bb1:
    store ptr %20, ptr %15
    %51 = const i64 8
    %52 = gep i8, ptr %15, %51
    %53 = const u64 4
    store u64 %53, ptr %52
    call @func.1(%14, %15)
    br bb2
bb2:
    store ptr %36, ptr %16
    %54 = const i64 8
    %55 = gep i8, ptr %16, %54
    %56 = const u64 4
    store u64 %56, ptr %55
    call @func.1(%14, %16)
    br bb3
bb3:
    call @func.2(%17, %14)
    br bb4
bb4:
    %57 = const u64 0
    %58 = const u64 0
    br bb5(%57, %58)
bb5(%0: u64, %1: u64):
    %59 = const i64 8
    %60 = gep i8, ptr %17, %59
    %61 = load u64, ptr %60
    %62 = icmp ult u64 %1, %61
    condbr %62, bb6(%0, %1), bb11(%0)
bb6(%2: u64, %3: u64):
    %63 = const u64 31
    %64 = call @func.3(%2, %63)
    br bb7(%3, %64)
bb7(%4: u64, %5: u64):
    %65 = const i64 8
    %66 = gep i8, ptr %17, %65
    %67 = load u64, ptr %66
    %68 = icmp ult u64 %4, %67
    condbr %68, bb8(%4, %5, %4), bb13
bb8(%6: u64, %7: u64, %8: u64):
    %69 = load ptr, ptr %17
    %70 = gep u8, ptr %69, %8
    %71 = load u8, ptr %70
    %72 = zext u8 %71 to u64
    %73 = call @func.4(%7, %72)
    br bb9(%6, %73)
bb9(%9: u64, %10: u64):
    %74 = const u64 1
    %75, %76 = add.overflow u64 %9, %74
    store u64 %75, ptr %18
    %77 = const i64 8
    %78 = gep i8, ptr %18, %77
    store bool %76, ptr %78
    %79 = const i64 8
    %80 = gep i8, ptr %18, %79
    %81 = load bool, ptr %80
    %82 = const bool false
    %83 = icmp eq bool %81, %82
    condbr %83, bb10(%10), bb13
bb10(%11: u64):
    %84 = load u64, ptr %18
    br bb5(%11, %84)
bb11(%12: u64):
    br bb12(%12)
bb12(%13: u64):
    ret %13
bb13:
    unreachable
}"#;

// ── faithful host shims for the hash root's std externs ────────────────────

extern "C" fn shim_string_new(sret: *mut String) {
    unsafe {
        std::ptr::write(sret, String::new());
    }
}

extern "C" fn shim_push_str(s: *mut String, pair: *const FatPair) {
    unsafe {
        let p = *pair;
        let part = std::str::from_utf8(std::slice::from_raw_parts(p.ptr, p.len as usize))
            .expect("push_str shim received non-UTF8 bytes — a corrupted literal image");
        (&mut *s).push_str(part);
    }
}

extern "C" fn shim_as_bytes(sret: *mut FatPair, s: *const String) {
    unsafe {
        let b = (&*s).as_bytes();
        *sret = FatPair {
            ptr: b.as_ptr(),
            len: b.len() as u64,
        };
    }
}

extern "C" fn shim_wrapping_mul(a: u64, b: u64) -> u64 {
    a.wrapping_mul(b)
}

extern "C" fn shim_wrapping_add(a: u64, b: u64) -> u64 {
    a.wrapping_add(b)
}

/// Native oracle for root (e) — the probe A2 body verbatim.
fn native_hash() -> u64 {
    let mut s = String::new();
    s.push_str("Tree");
    s.push_str(".rec");
    let bytes = s.as_bytes();
    let mut h = 0u64;
    let mut i = 0usize;
    while i < bytes.len() {
        h = h.wrapping_mul(31).wrapping_add(bytes[i] as u64);
        i += 1;
    }
    h
}

/// Root (e): the T3 probe A2 shape — BOTH literals cross as pair args into the
/// real `push_str` (host shim building a real String), then the byte-hash loop
/// runs IN-MODULE over the as_bytes pair: the JIT machine code performs the
/// bounds checks, the indexing loads, and the 31x+b folds via the wrapping
/// shims. native == JIT on the final hash — sensitive to every literal byte,
/// their ORDER (push_str x2 concatenation), and the length.
#[test]
fn str_const_hash_native_eq_jit() {
    let jit = run_with_watchdog("hash_root JIT", || {
        let mut externs = base_externs();
        externs.insert(
            "_RNvMNtCskTzINo8ZBH9_5alloc6stringNtB2_6String3newCs3P47iBr1uFy_24str_const_lowering_slice".to_string(),
            shim_string_new as *const u8,
        );
        externs.insert(
            "_RNvMNtCskTzINo8ZBH9_5alloc6stringNtB2_6String8push_strCs3P47iBr1uFy_24str_const_lowering_slice".to_string(),
            shim_push_str as *const u8,
        );
        externs.insert(
            "_RNvMNtCskTzINo8ZBH9_5alloc6stringNtB2_6String8as_bytesCs3P47iBr1uFy_24str_const_lowering_slice".to_string(),
            shim_as_bytes as *const u8,
        );
        externs.insert(
            "_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_mul".to_string(),
            shim_wrapping_mul as *const u8,
        );
        externs.insert(
            "_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_add".to_string(),
            shim_wrapping_add as *const u8,
        );
        let buffer = jit_module(HASH_TRUST_IR, "str_const_hash_root", &externs);
        let f: extern "C" fn() -> u64 =
            unsafe { std::mem::transmute(bind(&buffer, "str_const_hash_root")) };
        f()
    });

    let native = native_hash();
    assert_eq!(jit, native, "probe-A2 byte hash: native != JIT");

    // NEGATIVE CONTROLS (armed): the hash of a single-byte-corrupted string and
    // the hash of the two parts pushed in the REVERSED order must both disagree
    // — the equality above is sensitive to every byte and to concatenation
    // order.
    let corrupted = "Tree.reX"
        .bytes()
        .fold(0u64, |h, b| h.wrapping_mul(31).wrapping_add(b as u64));
    assert_ne!(
        jit, corrupted,
        "negative control must FAIL: a corrupted-byte hash should disagree with the JIT"
    );
    let reversed = ".recTree"
        .bytes()
        .fold(0u64, |h, b| h.wrapping_mul(31).wrapping_add(b as u64));
    assert_ne!(
        jit, reversed,
        "negative control must FAIL: a reversed-concatenation hash should disagree with the JIT"
    );
}
