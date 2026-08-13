//! FOLD_CAST CLUSTER STATUS (round-2 re-probe, 2026-07-02), after the switch/BST
//! block-id namespace collision fix addressed the first two regressions.
//!
//! The 2026-06-29 investigation recorded three fold_cast symptoms. Re-probed
//! here, the verdicts are:
//!
//!   (1) i128-from-halves ISel error — STILL BROKEN at trust-cg 9d3dfa6:
//!       `Pipeline(ISel("value Value(45) not defined before use"))` (was
//!       Value(36) on 2026-06-29) when the entry rebuilds an i128 from two u64
//!       halves (`shl u128 ..,64` + `or` + `bitcast`) and extracts with
//!       `lshr u128 ..,64`. Now lowered + verified native==JIT:
//!       `fold_cast_halves_full_sweep_native_eq_jit`.
//!   (2) JIT HANG on the `<Option<i128> as Try>::branch` sret shim (`val?`) —
//!       FIXED: the byte-for-byte production body (`val?` / `then_some` /
//!       `bit_width_with(64)?`) lowered through the Try/FromResidual/then_some
//!       shims now runs the FULL 3570-row differential native == JIT, no hang.
//!       PROMOTED: `fold_cast_verbatim_try_full_sweep_native_eq_jit`.
//!   (3) ZExt(Some(7))->None miscompile (bad i128 `icmp sge`) + Trunc-arm hang
//!       in the desugared extern-free form — BOTH FIXED: full 3570-row
//!       differential native == JIT including the exact 2026-06-29 witnesses.
//!       PROMOTED: `fold_cast_desugared_full_sweep_native_eq_jit`.
//!
//! Net: `fold_cast` (the CAST arm of trust-ir's allocation-bounds const-folder
//! — a genuine soundness predicate: a wrong Trunc fold under/over-estimates an
//! allocation count = an out-of-bounds access) is now VERIFIED native == JIT
//! over its full modeled input domain, in both the desugared and the verbatim
//! `?`-sugar lowering. The one remaining gap is the SCAFFOLDING-ABI ISel limit
//! (1), which never touches the verified body and is pinned.
//!
//! The verified fn: `fold_cast` (trust-ir/crates/trust-ir/src/alloc_bound.rs:270).
//! Transcription re-verified current against production sources on 2026-07-02:
//! `fold_cast` (alloc_bound.rs:270-290), `Ty` + `bit_width`/`bit_width_with`
//! (ty.rs:55-131/153/185), `CastOp` (inst.rs:105-123).
//!
//! Slices (verbatim transcriptions; modeled boundaries documented inline; all
//! DURABLE in tests/slices/, and each embedded module below regenerates
//! BYTE-IDENTICALLY from them — re-checked 2026-07-02):
//!   * `tests/slices/trust_fold_cast_slice.rs` — the desugared, extern-free
//!     form (documented provably-equivalent rewrites of `?`/`then_some`;
//!     POD-by-reference i128 ABI). Pre-existing, unchanged.
//!   * `tests/slices/trust_fold_cast_halves_slice.rs` — same verified body;
//!     the wrapper rebuilds the i128 from two u64 halves + `>> 64` extraction
//!     (the exact symptom-1 shape). NEW.
//!   * `tests/slices/trust_fold_cast_try_slice.rs` — the 100% byte-for-byte
//!     production body (`val?` / `(v >= 0).then_some(v)` /
//!     `dst_ty.bit_width_with(64)?`), lowering through the `Try::branch` /
//!     `FromResidual` / `then_some` empty-bodied shims (the symptom-2 shape).
//!     NEW.
//!
//! REGEN (per module):
//!   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//!   cd $HOME/trust-ir/frontend && env -u RUSTUP_TOOLCHAIN RUSTC=$S/bin/rustc \
//!     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//!     $S/bin/cargo run --bin trust_ir_mir -- <slice.rs> --crate-type=lib \
//!     --mir-emit-closure <root> <out.tir>
//!   roots: fold_cast_entry / fold_cast_entry_halves / fold_cast_entry_try
//!
//! MODELED BOUNDARIES (each also documented in the slices):
//!   * `?` / `then_some` / `u32::checked_mul` lower to EMPTY-BODIED imports
//!     (the known Option-Try/core-combinator frontend gap): the try-variant
//!     test binds FAITHFUL host shims for them (layouts read off the emitted
//!     module and documented at the shims below); `checked_mul` is reachable
//!     only via `Ty::Vector` dst types, which the tag menu does not build.
//!   * The desugared slice's rewrites of `?`/`then_some` are the literal
//!     definitional desugarings, documented in the slice; the try-variant
//!     slice removes even that (byte-for-byte production body), so the two
//!     modules TOGETHER close the transcription gap.
//!   * `src_ty` is dead in the production body (kept in the signature); the
//!     harness passes a fixed `Ty::I64` placeholder.
//!
//! HANG SAFETY: symptom (2)/(3) included JIT hangs, so EVERY JIT execution in
//! this file runs inside a WATCHDOG WORKER THREAD that streams each sweep row
//! back over a channel: the JIT buffer moves into (and on a hang is leaked
//! with) the worker, so a hung thread never executes freed machine code, and
//! the main thread bounds every wait with `recv_timeout` — a hang panics with
//! the exact input that stopped progressing instead of stalling the suite.
//!
//! COVERAGE NOTE: gated to aarch64 (the JIT target). Run ONE test per process
//! (`-- --exact <name> --test-threads=1`): the JIT engine is not thread-safe
//! at suite scale (see jit-parallel-race-2026-06-29.md).

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::sync::mpsc;
use std::time::Duration;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

// ── shared harness ──────────────────────────────────────────────────────────

/// Parse + JIT one embedded module with bound host externs; return the buffer
/// (keep it alive while calling fn pointers bound from it).
fn jit_module_with(
    text: &str,
    what: &str,
    externs: &HashMap<String, *const u8>,
) -> trust_cg_codegen::jit::ExecutableBuffer {
    let module = trust_ir::parser::parse_module(text)
        .unwrap_or_else(|e| panic!("MIR-emitted `{what}` trust-ir text must parse: {e:?}"));
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

// ── the NATIVE ORACLE: `fold_cast` + its type menu, transcribed VERBATIM from
//    production (alloc_bound.rs:270-290; ty.rs; inst.rs — re-checked current
//    2026-07-02). Same transcription as tests/slices/trust_fold_cast_slice.rs.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NStructId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NTyId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NFatPtrKind {
    Slice(NTyId),
    Str,
    TraitObject { trait_id: u32 },
}

/// The `Ty` menu the differential feeds (`dst_ty_for_tag` below only builds
/// scalar/pointer/Unit/Struct dst types, so the oracle enum carries exactly
/// the constructors those need; `bit_width`/`bit_width_with` are VERBATIM).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NTy {
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
    U128,
    F16,
    F32,
    F64,
    Bool,
    Vector(Box<NTy>, u32),
    Ptr,
    FatPtr(NFatPtrKind),
    Unit,
    Struct(NStructId),
}

impl NTy {
    /// ty.rs:153-175, VERBATIM.
    pub fn bit_width(&self) -> Option<u32> {
        match self {
            NTy::Bool => Some(1),
            NTy::I8 | NTy::U8 => Some(8),
            NTy::I16 | NTy::U16 => Some(16),
            NTy::I32 | NTy::U32 => Some(32),
            NTy::I64 | NTy::U64 => Some(64),
            NTy::I128 | NTy::U128 => Some(128),
            NTy::F16 => Some(16),
            NTy::F32 => Some(32),
            NTy::F64 => Some(64),
            NTy::Vector(elem, lanes) => elem.bit_width().and_then(|bits| bits.checked_mul(*lanes)),
            NTy::Ptr | NTy::FatPtr(_) => None,
            _ => None,
        }
    }

    /// ty.rs:185-196, VERBATIM.
    pub fn bit_width_with(&self, pointer_bits: u32) -> Option<u32> {
        match self {
            NTy::Ptr => Some(pointer_bits),
            NTy::FatPtr(_) => pointer_bits.checked_mul(2),
            NTy::Vector(elem, lanes) => elem
                .bit_width_with(pointer_bits)
                .and_then(|bits| bits.checked_mul(*lanes)),
            _ => self.bit_width(),
        }
    }
}

/// inst.rs:105-123, VERBATIM variant set & order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NCastOp {
    Trunc,
    ZExt,
    SExt,
    FPTrunc,
    FPExt,
    FPToUI,
    FPToSI,
    UIToFP,
    SIToFP,
    PtrToInt,
    IntToPtr,
    PtrToPtr,
    Bitcast,
    Transmute,
    ReifyFnPointer,
}

/// alloc_bound.rs:276-290, VERBATIM (the production body, `?`/`then_some`
/// form) — THE NATIVE ORACLE.
fn fold_cast_native(op: NCastOp, _src_ty: &NTy, dst_ty: &NTy, val: Option<i128>) -> Option<i128> {
    let v = val?;
    match op {
        NCastOp::SExt | NCastOp::Bitcast => Some(v),
        NCastOp::ZExt => (v >= 0).then_some(v),
        NCastOp::Trunc => {
            let bits = dst_ty.bit_width_with(64)?;
            if bits == 0 || bits > 127 {
                return None;
            }
            let mask = (1i128 << bits) - 1;
            Some(v & mask)
        }
        _ => None,
    }
}

/// Mirrors the slices' `cast_op_for_tag` exactly (covers every fold_cast arm).
fn cast_op_for_tag_native(tag: u32) -> NCastOp {
    match tag {
        0 => NCastOp::Trunc,
        1 => NCastOp::ZExt,
        2 => NCastOp::SExt,
        3 => NCastOp::FPTrunc,
        4 => NCastOp::FPExt,
        5 => NCastOp::FPToUI,
        6 => NCastOp::FPToSI,
        7 => NCastOp::UIToFP,
        8 => NCastOp::SIToFP,
        9 => NCastOp::PtrToInt,
        10 => NCastOp::IntToPtr,
        11 => NCastOp::PtrToPtr,
        12 => NCastOp::Bitcast,
        13 => NCastOp::Transmute,
        _ => NCastOp::ReifyFnPointer,
    }
}

/// Mirrors the slices' `dst_ty_for_tag` exactly: all scalar widths (128 hits
/// the `bits > 127` guard), Bool (1), Ptr (64), Unit + Struct (`bit_width_with`
/// -> None -> the `?` short-circuits).
fn dst_ty_for_tag_native(tag: u32) -> NTy {
    match tag {
        0 => NTy::I8,
        1 => NTy::I16,
        2 => NTy::I32,
        3 => NTy::I64,
        4 => NTy::I128,
        5 => NTy::U8,
        6 => NTy::U16,
        7 => NTy::U32,
        8 => NTy::U64,
        9 => NTy::U128,
        10 => NTy::Bool,
        11 => NTy::Ptr,
        12 => NTy::Unit,
        _ => NTy::Struct(NStructId(0)),
    }
}

/// The swept `Option<i128>` value menu: None + boundary/sign/width probes,
/// including the exact 2026-06-29 witnesses (`Some(7)` for ZExt, `0x1FF` for
/// Trunc-to-8).
fn value_menu() -> Vec<Option<i128>> {
    vec![
        None,
        Some(0),
        Some(1),
        Some(7),
        Some(-1),
        Some(-7),
        Some(255),
        Some(256),
        Some(0x1FF),
        Some(i128::MAX),
        Some(i128::MIN),
        Some(i128::MIN + 1),
        Some(u64::MAX as i128),
        Some(-(u64::MAX as i128)),
        Some(1i128 << 64),
        Some(-(1i128 << 64)),
        Some(0x0123_4567_89AB_CDEF_0123_4567_89AB_CDEFu128 as i128),
    ]
}

/// Plain-old-data view of `Option<i128>` (no niche) — the slices' ABI struct.
#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct OptI128POD {
    pub present: u64,
    pub value: i128,
}

type FoldCastEntryFn = unsafe extern "C" fn(u32, u32, *const OptI128POD, *mut OptI128POD);
type FoldCastHalvesFn = unsafe extern "C" fn(u32, u32, u64, u64, u64, *mut u64, *mut u64, *mut u64);

/// Sweep result row: (op_tag, dst_tag, val, jit_present, jit_value).
type SweepRow = (u32, u32, Option<i128>, u64, i128);

const WATCHDOG_SECS: u64 = 120;

// ── EMBEDDED MODULES (verbatim emits, validate_module = 0, re-parse OK) ─────

/// The DESUGARED module (slice: tests/slices/trust_fold_cast_slice.rs,
/// root `fold_cast_entry`; re-emitted 2026-07-02, 23492 bytes, 10 closure
/// members, validate_module = 0, re-parse OK; semantically identical to the
/// 2026-06-29 emit — the only diff is the crate-hash suffix in mangled
/// names). Its ONLY imports are the 3 empty-bodied `u32::checked_mul`
/// monomorphizations (unreachable on this file's dst menu; bound faithfully).
const FOLD_CAST_DESUGARED_IR: &str = r#"; TrustIr text format v1
module "mir::closure::fold_cast_entry"

functy.0 = (u32, u32, ptr, ptr) -> ()

functy.1 = (ptr, u32) -> ()

functy.2 = (ptr, u32) -> ()

functy.3 = (ptr, u8, ptr, ptr, ptr) -> ()

functy.4 = (ptr, u32, u32) -> ()

functy.5 = (ptr, ptr, u32) -> ()

functy.6 = (ptr, ptr) -> ()

functy.7 = (ptr, ptr, ptr) -> ()

functy.8 = (ptr, ptr, ptr) -> ()

functy.9 = (ptr, u32, u32) -> ()

functy.10 = (ptr, ptr, u32) -> ()

functy.11 = (ptr, u32, u32) -> ()

functy.12 = (ptr, ptr, u32) -> ()

fn @fold_cast_entry(functy.0) {
bb0(%0: u32, %1: u32, %2: ptr, %3: ptr):
    %20 = alloca (i128, i128), align 16
    %21 = alloca i8, align 1
    %22 = alloca (i64, i64, i64), align 8
    %23 = alloca (i64, i64, i64), align 8
    %24 = alloca (i128, i128), align 16
    %25 = alloca (i128, i128), align 16
    %26 = load u64, ptr %2
    %27 = const u64 0
    %28 = icmp ne u64 %26, %27
    condbr %28, bb1(%0, %1, %2, %3), bb2(%0, %1, %3)
bb1(%4: u32, %5: u32, %6: ptr, %7: ptr):
    %29 = const i64 16
    %30 = gep i8, ptr %6, %29
    %31 = load i128, ptr %30
    %32 = const i64 16
    %33 = gep i8, ptr %20, %32
    store i128 %31, ptr %33
    %34 = const i128 1
    store i128 %34, ptr %20
    br bb3(%4, %5, %7)
bb2(%8: u32, %9: u32, %10: ptr):
    %35 = const i128 0
    store i128 %35, ptr %20
    br bb3(%8, %9, %10)
bb3(%11: u32, %12: u32, %13: ptr):
    call @func.1(%21, %11)
    br bb4(%12, %13)
bb4(%14: u32, %15: ptr):
    call @func.2(%22, %14)
    br bb5(%15)
bb5(%16: ptr):
    %36 = const i64 -9223372036854775805
    store i64 %36, ptr %23
    %37 = load i128, ptr %20
    store i128 %37, ptr %25
    %38 = const i64 16
    %39 = gep i8, ptr %20, %38
    %40 = const i64 16
    %41 = gep i8, ptr %25, %40
    %42 = load i128, ptr %39
    store i128 %42, ptr %41
    %43 = load u8, ptr %21
    call @func.3(%24, %43, %23, %22, %25)
    br bb6(%16)
bb6(%17: ptr):
    %44 = load i128, ptr %24
    %45 = trunc i128 %44 to i64
    switch %45 [ 0: bb8(%17) 1: bb9(%17) default: bb7 ]
bb7:
    unreachable
bb8(%18: ptr):
    %46 = const u64 0
    store u64 %46, ptr %18
    %47 = const i128 0
    %48 = const i64 16
    %49 = gep i8, ptr %18, %48
    store i128 %47, ptr %49
    br bb10
bb9(%19: ptr):
    %50 = const i64 16
    %51 = gep i8, ptr %24, %50
    %52 = load i128, ptr %51
    %53 = const u64 1
    store u64 %53, ptr %19
    %54 = const i64 16
    %55 = gep i8, ptr %19, %54
    store i128 %52, ptr %55
    br bb10
bb10:
    br bb11
bb11:
    br bb12
bb12:
    ret
}

fn @cast_op_for_tag(functy.1) {
bb0(%0: ptr, %1: u32):
    switch %1 [ 0: bb15 1: bb14 2: bb13 3: bb12 4: bb11 5: bb10 6: bb9 7: bb8 8: bb7 9: bb6 10: bb5 11: bb4 12: bb3 13: bb2 default: bb1 ]
bb1:
    %2 = const i8 14
    store i8 %2, ptr %0
    br bb16
bb2:
    %3 = const i8 13
    store i8 %3, ptr %0
    br bb16
bb3:
    %4 = const i8 12
    store i8 %4, ptr %0
    br bb16
bb4:
    %5 = const i8 11
    store i8 %5, ptr %0
    br bb16
bb5:
    %6 = const i8 10
    store i8 %6, ptr %0
    br bb16
bb6:
    %7 = const i8 9
    store i8 %7, ptr %0
    br bb16
bb7:
    %8 = const i8 8
    store i8 %8, ptr %0
    br bb16
bb8:
    %9 = const i8 7
    store i8 %9, ptr %0
    br bb16
bb9:
    %10 = const i8 6
    store i8 %10, ptr %0
    br bb16
bb10:
    %11 = const i8 5
    store i8 %11, ptr %0
    br bb16
bb11:
    %12 = const i8 4
    store i8 %12, ptr %0
    br bb16
bb12:
    %13 = const i8 3
    store i8 %13, ptr %0
    br bb16
bb13:
    %14 = const i8 2
    store i8 %14, ptr %0
    br bb16
bb14:
    %15 = const i8 1
    store i8 %15, ptr %0
    br bb16
bb15:
    %16 = const i8 0
    store i8 %16, ptr %0
    br bb16
bb16:
    ret
}

fn @dst_ty_for_tag(functy.2) {
bb0(%0: ptr, %1: u32):
    %2 = alloca i32, align 4
    switch %1 [ 0: bb14 1: bb13 2: bb12 3: bb11 4: bb10 5: bb9 6: bb8 7: bb7 8: bb6 9: bb5 10: bb4 11: bb3 12: bb2 default: bb1 ]
bb1:
    %3 = const u32 0
    store u32 %3, ptr %2
    %4 = const i64 8
    %5 = gep i8, ptr %0, %4
    %6 = load i32, ptr %2
    store i32 %6, ptr %5
    %7 = const i64 -9223372036854775789
    store i64 %7, ptr %0
    br bb15
bb2:
    %8 = const i64 -9223372036854775791
    store i64 %8, ptr %0
    br bb15
bb3:
    %9 = const i64 -9223372036854775793
    store i64 %9, ptr %0
    br bb15
bb4:
    %10 = const i64 -9223372036854775795
    store i64 %10, ptr %0
    br bb15
bb5:
    %11 = const i64 -9223372036854775799
    store i64 %11, ptr %0
    br bb15
bb6:
    %12 = const i64 -9223372036854775800
    store i64 %12, ptr %0
    br bb15
bb7:
    %13 = const i64 -9223372036854775801
    store i64 %13, ptr %0
    br bb15
bb8:
    %14 = const i64 -9223372036854775802
    store i64 %14, ptr %0
    br bb15
bb9:
    %15 = const i64 -9223372036854775803
    store i64 %15, ptr %0
    br bb15
bb10:
    %16 = const i64 -9223372036854775804
    store i64 %16, ptr %0
    br bb15
bb11:
    %17 = const i64 -9223372036854775805
    store i64 %17, ptr %0
    br bb15
bb12:
    %18 = const i64 -9223372036854775806
    store i64 %18, ptr %0
    br bb15
bb13:
    %19 = const i64 -9223372036854775807
    store i64 %19, ptr %0
    br bb15
bb14:
    %20 = const i64 -9223372036854775808
    store i64 %20, ptr %0
    br bb15
bb15:
    ret
}

fn @fold_cast(functy.3) {
bb0(%0: ptr, %1: u8, %2: ptr, %3: ptr, %4: ptr):
    %20 = alloca i8, align 1
    %21 = alloca (i32, i32), align 4
    %22 = alloca (i128, i128), align 16
    store u8 %1, ptr %20
    %23 = load i128, ptr %4
    %24 = trunc i128 %23 to i64
    switch %24 [ 0: bb2 1: bb3(%3) default: bb1 ]
bb1:
    unreachable
bb2:
    %25 = const i128 0
    store i128 %25, ptr %0
    br bb18
bb3(%5: ptr):
    %26 = const i64 16
    %27 = gep i8, ptr %4, %26
    %28 = load i128, ptr %27
    %29 = load i8, ptr %20
    %30 = sext i8 %29 to i64
    switch %30 [ 0: bb5(%5, %28) 1: bb6(%28) 2: bb7(%28) 12: bb7(%28) default: bb4 ]
bb4:
    %31 = const i128 0
    store i128 %31, ptr %0
    br bb18
bb5(%6: ptr, %7: i128):
    %32 = const u32 64
    call @func.5(%21, %6, %32)
    br bb10(%7)
bb6(%8: i128):
    %33 = const i128 0
    %34 = icmp sge i128 %8, %33
    condbr %34, bb8(%8), bb9
bb7(%9: i128):
    %35 = const i64 16
    %36 = gep i8, ptr %0, %35
    store i128 %9, ptr %36
    %37 = const i128 1
    store i128 %37, ptr %0
    br bb18
bb8(%10: i128):
    %38 = const i64 16
    %39 = gep i8, ptr %0, %38
    store i128 %10, ptr %39
    %40 = const i128 1
    store i128 %40, ptr %0
    br bb18
bb9:
    %41 = const i128 0
    store i128 %41, ptr %0
    br bb18
bb10(%11: i128):
    %42 = load i32, ptr %21
    %43 = sext i32 %42 to i64
    switch %43 [ 0: bb11 1: bb12(%11) default: bb1 ]
bb11:
    %44 = const i128 0
    store i128 %44, ptr %0
    br bb18
bb12(%12: i128):
    %45 = const i64 4
    %46 = gep i8, ptr %21, %45
    %47 = load u32, ptr %46
    %48 = const u32 0
    %49 = icmp eq u32 %47, %48
    condbr %49, bb15, bb13(%12, %47)
bb13(%13: i128, %14: u32):
    %50 = const u32 127
    %51 = icmp ugt u32 %14, %50
    condbr %51, bb15, bb14(%13, %14)
bb14(%15: i128, %16: u32):
    %52 = const u32 128
    %53 = icmp ult u32 %16, %52
    condbr %53, bb16(%15, %16), bb19
bb15:
    %54 = const i128 0
    store i128 %54, ptr %0
    br bb18
bb16(%17: i128, %18: u32):
    %55 = const i128 1
    %56 = zext u32 %18 to i128
    %57 = shl i128 %55, %56
    %58 = const i128 1
    %59, %60 = sub.overflow i128 %57, %58
    store i128 %59, ptr %22
    %61 = const i64 16
    %62 = gep i8, ptr %22, %61
    store bool %60, ptr %62
    %63 = const i64 16
    %64 = gep i8, ptr %22, %63
    %65 = load bool, ptr %64
    %66 = const bool false
    %67 = icmp eq bool %65, %66
    condbr %67, bb17(%17), bb19
bb17(%19: i128):
    %68 = load i128, ptr %22
    %69 = and i128 %19, %68
    %70 = const i64 16
    %71 = gep i8, ptr %0, %70
    store i128 %69, ptr %71
    %72 = const i128 1
    store i128 %72, ptr %0
    br bb18
bb18:
    ret
bb19:
    unreachable
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm11checked_mulCs34Q1zAXKtMq_21trust_fold_cast_slice(functy.4) {
}

fn @Ty__bit_width_with(functy.5) {
bb0(%0: ptr, %1: ptr, %2: u32):
    %8 = alloca i64, align 8
    %9 = alloca i64, align 8
    %10 = alloca (i32, i32), align 4
    %11 = alloca i64, align 8
    %12 = alloca i64, align 8
    %13 = alloca i64, align 8
    store ptr %1, ptr %8
    %14 = load ptr, ptr %8
    %15 = load i64, ptr %14
    %16 = const i64 21
    %17 = const i64 -9223372036854775808
    %18 = icmp eq i64 %15, %17
    %19 = const i64 0
    %20 = select i64 %18, %19, %16
    %21 = const i64 -9223372036854775807
    %22 = icmp eq i64 %15, %21
    %23 = const i64 1
    %24 = select i64 %22, %23, %20
    %25 = const i64 -9223372036854775806
    %26 = icmp eq i64 %15, %25
    %27 = const i64 2
    %28 = select i64 %26, %27, %24
    %29 = const i64 -9223372036854775805
    %30 = icmp eq i64 %15, %29
    %31 = const i64 3
    %32 = select i64 %30, %31, %28
    %33 = const i64 -9223372036854775804
    %34 = icmp eq i64 %15, %33
    %35 = const i64 4
    %36 = select i64 %34, %35, %32
    %37 = const i64 -9223372036854775803
    %38 = icmp eq i64 %15, %37
    %39 = const i64 5
    %40 = select i64 %38, %39, %36
    %41 = const i64 -9223372036854775802
    %42 = icmp eq i64 %15, %41
    %43 = const i64 6
    %44 = select i64 %42, %43, %40
    %45 = const i64 -9223372036854775801
    %46 = icmp eq i64 %15, %45
    %47 = const i64 7
    %48 = select i64 %46, %47, %44
    %49 = const i64 -9223372036854775800
    %50 = icmp eq i64 %15, %49
    %51 = const i64 8
    %52 = select i64 %50, %51, %48
    %53 = const i64 -9223372036854775799
    %54 = icmp eq i64 %15, %53
    %55 = const i64 9
    %56 = select i64 %54, %55, %52
    %57 = const i64 -9223372036854775798
    %58 = icmp eq i64 %15, %57
    %59 = const i64 10
    %60 = select i64 %58, %59, %56
    %61 = const i64 -9223372036854775797
    %62 = icmp eq i64 %15, %61
    %63 = const i64 11
    %64 = select i64 %62, %63, %60
    %65 = const i64 -9223372036854775796
    %66 = icmp eq i64 %15, %65
    %67 = const i64 12
    %68 = select i64 %66, %67, %64
    %69 = const i64 -9223372036854775795
    %70 = icmp eq i64 %15, %69
    %71 = const i64 13
    %72 = select i64 %70, %71, %68
    %73 = const i64 -9223372036854775794
    %74 = icmp eq i64 %15, %73
    %75 = const i64 14
    %76 = select i64 %74, %75, %72
    %77 = const i64 -9223372036854775793
    %78 = icmp eq i64 %15, %77
    %79 = const i64 15
    %80 = select i64 %78, %79, %76
    %81 = const i64 -9223372036854775792
    %82 = icmp eq i64 %15, %81
    %83 = const i64 16
    %84 = select i64 %82, %83, %80
    %85 = const i64 -9223372036854775791
    %86 = icmp eq i64 %15, %85
    %87 = const i64 17
    %88 = select i64 %86, %87, %84
    %89 = const i64 -9223372036854775790
    %90 = icmp eq i64 %15, %89
    %91 = const i64 18
    %92 = select i64 %90, %91, %88
    %93 = const i64 -9223372036854775789
    %94 = icmp eq i64 %15, %93
    %95 = const i64 19
    %96 = select i64 %94, %95, %92
    %97 = const i64 -9223372036854775788
    %98 = icmp eq i64 %15, %97
    %99 = const i64 20
    %100 = select i64 %98, %99, %96
    %101 = const i64 -9223372036854775786
    %102 = icmp eq i64 %15, %101
    %103 = const i64 22
    %104 = select i64 %102, %103, %100
    %105 = const i64 -9223372036854775785
    %106 = icmp eq i64 %15, %105
    %107 = const i64 23
    %108 = select i64 %106, %107, %104
    %109 = const i64 -9223372036854775784
    %110 = icmp eq i64 %15, %109
    %111 = const i64 24
    %112 = select i64 %110, %111, %108
    %113 = const i64 -9223372036854775783
    %114 = icmp eq i64 %15, %113
    %115 = const i64 25
    %116 = select i64 %114, %115, %112
    %117 = const i64 -9223372036854775782
    %118 = icmp eq i64 %15, %117
    %119 = const i64 26
    %120 = select i64 %118, %119, %116
    %121 = const i64 -9223372036854775781
    %122 = icmp eq i64 %15, %121
    %123 = const i64 27
    %124 = select i64 %122, %123, %120
    %125 = const i64 -9223372036854775780
    %126 = icmp eq i64 %15, %125
    %127 = const i64 28
    %128 = select i64 %126, %127, %124
    %129 = const i64 -9223372036854775779
    %130 = icmp eq i64 %15, %129
    %131 = const i64 29
    %132 = select i64 %130, %131, %128
    %133 = const i64 -9223372036854775778
    %134 = icmp eq i64 %15, %133
    %135 = const i64 30
    %136 = select i64 %134, %135, %132
    %137 = const i64 -9223372036854775777
    %138 = icmp eq i64 %15, %137
    %139 = const i64 31
    %140 = select i64 %138, %139, %136
    %141 = const i64 -9223372036854775776
    %142 = icmp eq i64 %15, %141
    %143 = const i64 32
    %144 = select i64 %142, %143, %140
    switch %144 [ 14: bb2(%2) 15: bb4(%2) 16: bb3(%2) 24: bb4(%2) 25: bb4(%2) 26: bb4(%2) 27: bb4(%2) 28: bb4(%2) default: bb1 ]
bb1:
    %145 = load ptr, ptr %8
    call @func.6(%0, %145)
    br bb6
bb2(%3: u32):
    %146 = load ptr, ptr %8
    %147 = const i64 8
    %148 = gep i8, ptr %146, %147
    %149 = load ptr, ptr %8
    %150 = const i64 16
    %151 = gep i8, ptr %149, %150
    store ptr %151, ptr %9
    %152 = load i64, ptr %148
    store i64 %152, ptr %12
    %153 = load ptr, ptr %12
    store ptr %153, ptr %13
    %154 = load ptr, ptr %13
    %155 = ptrtoint ptr %154 to u64
    %156 = const u64 8
    %157 = const u64 1
    %158 = sub u64 %156, %157
    %159 = and u64 %155, %158
    %160 = const u64 0
    %161 = icmp eq u64 %159, %160
    condbr %161, bb7(%3), bb9
bb3(%4: u32):
    %162 = const u32 2
    call @func.4(%0, %4, %162)
    br bb6
bb4(%5: u32):
    %163 = const i64 4
    %164 = gep i8, ptr %0, %163
    store u32 %5, ptr %164
    %165 = const i32 1
    store i32 %165, ptr %0
    br bb6
bb5:
    store ptr %9, ptr %11
    call @func.7(%0, %10, %11)
    br bb6
bb6:
    ret
bb7(%6: u32):
    %166 = load ptr, ptr %13
    %167 = ptrtoint ptr %166 to u64
    %168 = const u64 0
    %169 = icmp eq u64 %167, %168
    %170 = const bool true
    %171 = const bool false
    %172 = select bool %169, %170, %171
    %173 = const bool false
    %174 = icmp eq bool %172, %173
    condbr %174, bb8(%6), bb9
bb8(%7: u32):
    %175 = load ptr, ptr %13
    call @func.5(%10, %175, %7)
    br bb5
bb9:
    unreachable
}

fn @Ty__bit_width(functy.6) {
bb0(%0: ptr, %1: ptr):
    %2 = alloca i64, align 8
    %3 = alloca i64, align 8
    %4 = alloca (i32, i32), align 4
    %5 = alloca i64, align 8
    %6 = alloca i64, align 8
    %7 = alloca i64, align 8
    store ptr %1, ptr %2
    %8 = load ptr, ptr %2
    %9 = load i64, ptr %8
    %10 = const i64 21
    %11 = const i64 -9223372036854775808
    %12 = icmp eq i64 %9, %11
    %13 = const i64 0
    %14 = select i64 %12, %13, %10
    %15 = const i64 -9223372036854775807
    %16 = icmp eq i64 %9, %15
    %17 = const i64 1
    %18 = select i64 %16, %17, %14
    %19 = const i64 -9223372036854775806
    %20 = icmp eq i64 %9, %19
    %21 = const i64 2
    %22 = select i64 %20, %21, %18
    %23 = const i64 -9223372036854775805
    %24 = icmp eq i64 %9, %23
    %25 = const i64 3
    %26 = select i64 %24, %25, %22
    %27 = const i64 -9223372036854775804
    %28 = icmp eq i64 %9, %27
    %29 = const i64 4
    %30 = select i64 %28, %29, %26
    %31 = const i64 -9223372036854775803
    %32 = icmp eq i64 %9, %31
    %33 = const i64 5
    %34 = select i64 %32, %33, %30
    %35 = const i64 -9223372036854775802
    %36 = icmp eq i64 %9, %35
    %37 = const i64 6
    %38 = select i64 %36, %37, %34
    %39 = const i64 -9223372036854775801
    %40 = icmp eq i64 %9, %39
    %41 = const i64 7
    %42 = select i64 %40, %41, %38
    %43 = const i64 -9223372036854775800
    %44 = icmp eq i64 %9, %43
    %45 = const i64 8
    %46 = select i64 %44, %45, %42
    %47 = const i64 -9223372036854775799
    %48 = icmp eq i64 %9, %47
    %49 = const i64 9
    %50 = select i64 %48, %49, %46
    %51 = const i64 -9223372036854775798
    %52 = icmp eq i64 %9, %51
    %53 = const i64 10
    %54 = select i64 %52, %53, %50
    %55 = const i64 -9223372036854775797
    %56 = icmp eq i64 %9, %55
    %57 = const i64 11
    %58 = select i64 %56, %57, %54
    %59 = const i64 -9223372036854775796
    %60 = icmp eq i64 %9, %59
    %61 = const i64 12
    %62 = select i64 %60, %61, %58
    %63 = const i64 -9223372036854775795
    %64 = icmp eq i64 %9, %63
    %65 = const i64 13
    %66 = select i64 %64, %65, %62
    %67 = const i64 -9223372036854775794
    %68 = icmp eq i64 %9, %67
    %69 = const i64 14
    %70 = select i64 %68, %69, %66
    %71 = const i64 -9223372036854775793
    %72 = icmp eq i64 %9, %71
    %73 = const i64 15
    %74 = select i64 %72, %73, %70
    %75 = const i64 -9223372036854775792
    %76 = icmp eq i64 %9, %75
    %77 = const i64 16
    %78 = select i64 %76, %77, %74
    %79 = const i64 -9223372036854775791
    %80 = icmp eq i64 %9, %79
    %81 = const i64 17
    %82 = select i64 %80, %81, %78
    %83 = const i64 -9223372036854775790
    %84 = icmp eq i64 %9, %83
    %85 = const i64 18
    %86 = select i64 %84, %85, %82
    %87 = const i64 -9223372036854775789
    %88 = icmp eq i64 %9, %87
    %89 = const i64 19
    %90 = select i64 %88, %89, %86
    %91 = const i64 -9223372036854775788
    %92 = icmp eq i64 %9, %91
    %93 = const i64 20
    %94 = select i64 %92, %93, %90
    %95 = const i64 -9223372036854775786
    %96 = icmp eq i64 %9, %95
    %97 = const i64 22
    %98 = select i64 %96, %97, %94
    %99 = const i64 -9223372036854775785
    %100 = icmp eq i64 %9, %99
    %101 = const i64 23
    %102 = select i64 %100, %101, %98
    %103 = const i64 -9223372036854775784
    %104 = icmp eq i64 %9, %103
    %105 = const i64 24
    %106 = select i64 %104, %105, %102
    %107 = const i64 -9223372036854775783
    %108 = icmp eq i64 %9, %107
    %109 = const i64 25
    %110 = select i64 %108, %109, %106
    %111 = const i64 -9223372036854775782
    %112 = icmp eq i64 %9, %111
    %113 = const i64 26
    %114 = select i64 %112, %113, %110
    %115 = const i64 -9223372036854775781
    %116 = icmp eq i64 %9, %115
    %117 = const i64 27
    %118 = select i64 %116, %117, %114
    %119 = const i64 -9223372036854775780
    %120 = icmp eq i64 %9, %119
    %121 = const i64 28
    %122 = select i64 %120, %121, %118
    %123 = const i64 -9223372036854775779
    %124 = icmp eq i64 %9, %123
    %125 = const i64 29
    %126 = select i64 %124, %125, %122
    %127 = const i64 -9223372036854775778
    %128 = icmp eq i64 %9, %127
    %129 = const i64 30
    %130 = select i64 %128, %129, %126
    %131 = const i64 -9223372036854775777
    %132 = icmp eq i64 %9, %131
    %133 = const i64 31
    %134 = select i64 %132, %133, %130
    %135 = const i64 -9223372036854775776
    %136 = icmp eq i64 %9, %135
    %137 = const i64 32
    %138 = select i64 %136, %137, %134
    switch %138 [ 0: bb11 1: bb10 2: bb9 3: bb8 4: bb7 5: bb11 6: bb10 7: bb9 8: bb8 9: bb7 10: bb6 11: bb5 12: bb4 13: bb12 14: bb3 15: bb2 16: bb2 24: bb2 25: bb2 26: bb2 27: bb2 28: bb2 default: bb1 ]
bb1:
    %139 = const i32 0
    store i32 %139, ptr %0
    br bb14
bb2:
    %140 = const i32 0
    store i32 %140, ptr %0
    br bb14
bb3:
    %141 = load ptr, ptr %2
    %142 = const i64 8
    %143 = gep i8, ptr %141, %142
    %144 = load ptr, ptr %2
    %145 = const i64 16
    %146 = gep i8, ptr %144, %145
    store ptr %146, ptr %3
    %147 = load i64, ptr %143
    store i64 %147, ptr %6
    %148 = load ptr, ptr %6
    store ptr %148, ptr %7
    %149 = load ptr, ptr %7
    %150 = ptrtoint ptr %149 to u64
    %151 = const u64 8
    %152 = const u64 1
    %153 = sub u64 %151, %152
    %154 = and u64 %150, %153
    %155 = const u64 0
    %156 = icmp eq u64 %154, %155
    condbr %156, bb15, bb17
bb4:
    %157 = const u32 64
    %158 = const i64 4
    %159 = gep i8, ptr %0, %158
    store u32 %157, ptr %159
    %160 = const i32 1
    store i32 %160, ptr %0
    br bb14
bb5:
    %161 = const u32 32
    %162 = const i64 4
    %163 = gep i8, ptr %0, %162
    store u32 %161, ptr %163
    %164 = const i32 1
    store i32 %164, ptr %0
    br bb14
bb6:
    %165 = const u32 16
    %166 = const i64 4
    %167 = gep i8, ptr %0, %166
    store u32 %165, ptr %167
    %168 = const i32 1
    store i32 %168, ptr %0
    br bb14
bb7:
    %169 = const u32 128
    %170 = const i64 4
    %171 = gep i8, ptr %0, %170
    store u32 %169, ptr %171
    %172 = const i32 1
    store i32 %172, ptr %0
    br bb14
bb8:
    %173 = const u32 64
    %174 = const i64 4
    %175 = gep i8, ptr %0, %174
    store u32 %173, ptr %175
    %176 = const i32 1
    store i32 %176, ptr %0
    br bb14
bb9:
    %177 = const u32 32
    %178 = const i64 4
    %179 = gep i8, ptr %0, %178
    store u32 %177, ptr %179
    %180 = const i32 1
    store i32 %180, ptr %0
    br bb14
bb10:
    %181 = const u32 16
    %182 = const i64 4
    %183 = gep i8, ptr %0, %182
    store u32 %181, ptr %183
    %184 = const i32 1
    store i32 %184, ptr %0
    br bb14
bb11:
    %185 = const u32 8
    %186 = const i64 4
    %187 = gep i8, ptr %0, %186
    store u32 %185, ptr %187
    %188 = const i32 1
    store i32 %188, ptr %0
    br bb14
bb12:
    %189 = const u32 1
    %190 = const i64 4
    %191 = gep i8, ptr %0, %190
    store u32 %189, ptr %191
    %192 = const i32 1
    store i32 %192, ptr %0
    br bb14
bb13:
    store ptr %3, ptr %5
    call @func.8(%0, %4, %5)
    br bb14
bb14:
    ret
bb15:
    %193 = load ptr, ptr %7
    %194 = ptrtoint ptr %193 to u64
    %195 = const u64 0
    %196 = icmp eq u64 %194, %195
    %197 = const bool true
    %198 = const bool false
    %199 = select bool %196, %197, %198
    %200 = const bool false
    %201 = icmp eq bool %199, %200
    condbr %201, bb16, bb17
bb16:
    %202 = load ptr, ptr %7
    call @func.6(%4, %202)
    br bb13
bb17:
    unreachable
}

fn @std__option__Option___T___and_then__monoebbfde013e54d81c(functy.7) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %3 = alloca i64, align 8
    %4 = alloca i32, align 4
    %5 = load i32, ptr %1
    %6 = sext i32 %5 to i64
    switch %6 [ 0: bb2 1: bb3 default: bb1 ]
bb1:
    unreachable
bb2:
    %7 = const i32 0
    store i32 %7, ptr %0
    br bb5
bb3:
    %8 = const i64 4
    %9 = gep i8, ptr %1, %8
    %10 = load u32, ptr %9
    %11 = load i64, ptr %2
    store i64 %11, ptr %3
    store u32 %10, ptr %4
    %12 = load u32, ptr %4
    call @func.10(%0, %3, %12)
    br bb4
bb4:
    br bb5
bb5:
    ret
}

fn @std__option__Option___T___and_then__monoaef14581b8a512cf(functy.8) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %3 = alloca i64, align 8
    %4 = alloca i32, align 4
    %5 = load i32, ptr %1
    %6 = sext i32 %5 to i64
    switch %6 [ 0: bb2 1: bb3 default: bb1 ]
bb1:
    unreachable
bb2:
    %7 = const i32 0
    store i32 %7, ptr %0
    br bb5
bb3:
    %8 = const i64 4
    %9 = gep i8, ptr %1, %8
    %10 = load u32, ptr %9
    %11 = load i64, ptr %2
    store i64 %11, ptr %3
    store u32 %10, ptr %4
    %12 = load u32, ptr %4
    call @func.12(%0, %3, %12)
    br bb4
bb4:
    br bb5
bb5:
    ret
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm11checked_mulCs34Q1zAXKtMq_21trust_fold_cast_slice(functy.9) {
}

fn @Ty__bit_width_with___closure_0_(functy.10) {
bb0(%0: ptr, %1: ptr, %2: u32):
    %3 = load ptr, ptr %1
    %4 = load ptr, ptr %3
    %5 = load u32, ptr %4
    call @func.9(%0, %2, %5)
    br bb1
bb1:
    ret
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm11checked_mulCs34Q1zAXKtMq_21trust_fold_cast_slice(functy.11) {
}

fn @Ty__bit_width___closure_0_(functy.12) {
bb0(%0: ptr, %1: ptr, %2: u32):
    %3 = load ptr, ptr %1
    %4 = load ptr, ptr %3
    %5 = load u32, ptr %4
    call @func.11(%0, %2, %5)
    br bb1
bb1:
    ret
}
"#;

/// The HALVES-ABI module (symptom-1 probe shape: i128 rebuilt from two u64
/// halves + `>> 64` result extraction; root `fold_cast_entry_halves`;
/// emitted 2026-07-02, 24542 bytes, validate_module = 0, re-parse OK).
const FOLD_CAST_HALVES_IR: &str = r#"; TrustIr text format v1
module "mir::closure::fold_cast_entry_halves"

functy.0 = (u32, u32, u64, u64, u64, ptr, ptr, ptr) -> ()

functy.1 = (ptr, u32) -> ()

functy.2 = (ptr, u32) -> ()

functy.3 = (ptr, u8, ptr, ptr, ptr) -> ()

functy.4 = (ptr, u32, u32) -> ()

functy.5 = (ptr, ptr, u32) -> ()

functy.6 = (ptr, ptr) -> ()

functy.7 = (ptr, ptr, ptr) -> ()

functy.8 = (ptr, ptr, ptr) -> ()

functy.9 = (ptr, u32, u32) -> ()

functy.10 = (ptr, ptr, u32) -> ()

functy.11 = (ptr, u32, u32) -> ()

functy.12 = (ptr, ptr, u32) -> ()

fn @fold_cast_entry_halves(functy.0) {
bb0(%0: u32, %1: u32, %2: u64, %3: u64, %4: u64, %5: ptr, %6: ptr, %7: ptr):
    %50 = alloca (i128, i128), align 16
    %51 = alloca i8, align 1
    %52 = alloca (i64, i64, i64), align 8
    %53 = alloca (i64, i64, i64), align 8
    %54 = alloca (i128, i128), align 16
    %55 = alloca (i128, i128), align 16
    %56 = const u64 0
    %57 = icmp ne u64 %2, %56
    condbr %57, bb1(%0, %1, %3, %4, %5, %6, %7), bb3(%0, %1, %5, %6, %7)
bb1(%8: u32, %9: u32, %10: u64, %11: u64, %12: ptr, %13: ptr, %14: ptr):
    %58 = zext u64 %11 to u128
    %59 = const i32 64
    %60 = bitcast i32 %59 to u32
    %61 = const u32 128
    %62 = icmp ult u32 %60, %61
    condbr %62, bb2(%8, %9, %10, %12, %13, %14, %58), bb15
bb2(%15: u32, %16: u32, %17: u64, %18: ptr, %19: ptr, %20: ptr, %21: u128):
    %63 = const i32 64
    %64 = zext i32 %63 to u128
    %65 = shl u128 %21, %64
    %66 = zext u64 %17 to u128
    %67 = or u128 %65, %66
    %68 = bitcast u128 %67 to i128
    %69 = const i64 16
    %70 = gep i8, ptr %50, %69
    store i128 %68, ptr %70
    %71 = const i128 1
    store i128 %71, ptr %50
    br bb4(%15, %16, %18, %19, %20)
bb3(%22: u32, %23: u32, %24: ptr, %25: ptr, %26: ptr):
    %72 = const i128 0
    store i128 %72, ptr %50
    br bb4(%22, %23, %24, %25, %26)
bb4(%27: u32, %28: u32, %29: ptr, %30: ptr, %31: ptr):
    call @func.1(%51, %27)
    br bb5(%28, %29, %30, %31)
bb5(%32: u32, %33: ptr, %34: ptr, %35: ptr):
    call @func.2(%52, %32)
    br bb6(%33, %34, %35)
bb6(%36: ptr, %37: ptr, %38: ptr):
    %73 = const i64 -9223372036854775805
    store i64 %73, ptr %53
    %74 = load i128, ptr %50
    store i128 %74, ptr %55
    %75 = const i64 16
    %76 = gep i8, ptr %50, %75
    %77 = const i64 16
    %78 = gep i8, ptr %55, %77
    %79 = load i128, ptr %76
    store i128 %79, ptr %78
    %80 = load u8, ptr %51
    call @func.3(%54, %80, %53, %52, %55)
    br bb7(%36, %37, %38)
bb7(%39: ptr, %40: ptr, %41: ptr):
    %81 = load i128, ptr %54
    %82 = trunc i128 %81 to i64
    switch %82 [ 0: bb9(%39, %40, %41) 1: bb10(%39, %40, %41) default: bb8 ]
bb8:
    unreachable
bb9(%42: ptr, %43: ptr, %44: ptr):
    %83 = const u64 0
    store u64 %83, ptr %42
    %84 = const u64 0
    store u64 %84, ptr %43
    %85 = const u64 0
    store u64 %85, ptr %44
    br bb12
bb10(%45: ptr, %46: ptr, %47: ptr):
    %86 = const i64 16
    %87 = gep i8, ptr %54, %86
    %88 = load i128, ptr %87
    %89 = const u64 1
    store u64 %89, ptr %45
    %90 = bitcast i128 %88 to u128
    %91 = trunc u128 %90 to u64
    store u64 %91, ptr %46
    %92 = const i32 64
    %93 = bitcast i32 %92 to u32
    %94 = const u32 128
    %95 = icmp ult u32 %93, %94
    condbr %95, bb11(%47, %90), bb15
bb11(%48: ptr, %49: u128):
    %96 = const i32 64
    %97 = zext i32 %96 to u128
    %98 = lshr u128 %49, %97
    %99 = trunc u128 %98 to u64
    store u64 %99, ptr %48
    br bb12
bb12:
    br bb13
bb13:
    br bb14
bb14:
    ret
bb15:
    unreachable
}

fn @cast_op_for_tag(functy.1) {
bb0(%0: ptr, %1: u32):
    switch %1 [ 0: bb15 1: bb14 2: bb13 3: bb12 4: bb11 5: bb10 6: bb9 7: bb8 8: bb7 9: bb6 10: bb5 11: bb4 12: bb3 13: bb2 default: bb1 ]
bb1:
    %2 = const i8 14
    store i8 %2, ptr %0
    br bb16
bb2:
    %3 = const i8 13
    store i8 %3, ptr %0
    br bb16
bb3:
    %4 = const i8 12
    store i8 %4, ptr %0
    br bb16
bb4:
    %5 = const i8 11
    store i8 %5, ptr %0
    br bb16
bb5:
    %6 = const i8 10
    store i8 %6, ptr %0
    br bb16
bb6:
    %7 = const i8 9
    store i8 %7, ptr %0
    br bb16
bb7:
    %8 = const i8 8
    store i8 %8, ptr %0
    br bb16
bb8:
    %9 = const i8 7
    store i8 %9, ptr %0
    br bb16
bb9:
    %10 = const i8 6
    store i8 %10, ptr %0
    br bb16
bb10:
    %11 = const i8 5
    store i8 %11, ptr %0
    br bb16
bb11:
    %12 = const i8 4
    store i8 %12, ptr %0
    br bb16
bb12:
    %13 = const i8 3
    store i8 %13, ptr %0
    br bb16
bb13:
    %14 = const i8 2
    store i8 %14, ptr %0
    br bb16
bb14:
    %15 = const i8 1
    store i8 %15, ptr %0
    br bb16
bb15:
    %16 = const i8 0
    store i8 %16, ptr %0
    br bb16
bb16:
    ret
}

fn @dst_ty_for_tag(functy.2) {
bb0(%0: ptr, %1: u32):
    %2 = alloca i32, align 4
    switch %1 [ 0: bb14 1: bb13 2: bb12 3: bb11 4: bb10 5: bb9 6: bb8 7: bb7 8: bb6 9: bb5 10: bb4 11: bb3 12: bb2 default: bb1 ]
bb1:
    %3 = const u32 0
    store u32 %3, ptr %2
    %4 = const i64 8
    %5 = gep i8, ptr %0, %4
    %6 = load i32, ptr %2
    store i32 %6, ptr %5
    %7 = const i64 -9223372036854775789
    store i64 %7, ptr %0
    br bb15
bb2:
    %8 = const i64 -9223372036854775791
    store i64 %8, ptr %0
    br bb15
bb3:
    %9 = const i64 -9223372036854775793
    store i64 %9, ptr %0
    br bb15
bb4:
    %10 = const i64 -9223372036854775795
    store i64 %10, ptr %0
    br bb15
bb5:
    %11 = const i64 -9223372036854775799
    store i64 %11, ptr %0
    br bb15
bb6:
    %12 = const i64 -9223372036854775800
    store i64 %12, ptr %0
    br bb15
bb7:
    %13 = const i64 -9223372036854775801
    store i64 %13, ptr %0
    br bb15
bb8:
    %14 = const i64 -9223372036854775802
    store i64 %14, ptr %0
    br bb15
bb9:
    %15 = const i64 -9223372036854775803
    store i64 %15, ptr %0
    br bb15
bb10:
    %16 = const i64 -9223372036854775804
    store i64 %16, ptr %0
    br bb15
bb11:
    %17 = const i64 -9223372036854775805
    store i64 %17, ptr %0
    br bb15
bb12:
    %18 = const i64 -9223372036854775806
    store i64 %18, ptr %0
    br bb15
bb13:
    %19 = const i64 -9223372036854775807
    store i64 %19, ptr %0
    br bb15
bb14:
    %20 = const i64 -9223372036854775808
    store i64 %20, ptr %0
    br bb15
bb15:
    ret
}

fn @fold_cast(functy.3) {
bb0(%0: ptr, %1: u8, %2: ptr, %3: ptr, %4: ptr):
    %20 = alloca i8, align 1
    %21 = alloca (i32, i32), align 4
    %22 = alloca (i128, i128), align 16
    store u8 %1, ptr %20
    %23 = load i128, ptr %4
    %24 = trunc i128 %23 to i64
    switch %24 [ 0: bb2 1: bb3(%3) default: bb1 ]
bb1:
    unreachable
bb2:
    %25 = const i128 0
    store i128 %25, ptr %0
    br bb18
bb3(%5: ptr):
    %26 = const i64 16
    %27 = gep i8, ptr %4, %26
    %28 = load i128, ptr %27
    %29 = load i8, ptr %20
    %30 = sext i8 %29 to i64
    switch %30 [ 0: bb5(%5, %28) 1: bb6(%28) 2: bb7(%28) 12: bb7(%28) default: bb4 ]
bb4:
    %31 = const i128 0
    store i128 %31, ptr %0
    br bb18
bb5(%6: ptr, %7: i128):
    %32 = const u32 64
    call @func.5(%21, %6, %32)
    br bb10(%7)
bb6(%8: i128):
    %33 = const i128 0
    %34 = icmp sge i128 %8, %33
    condbr %34, bb8(%8), bb9
bb7(%9: i128):
    %35 = const i64 16
    %36 = gep i8, ptr %0, %35
    store i128 %9, ptr %36
    %37 = const i128 1
    store i128 %37, ptr %0
    br bb18
bb8(%10: i128):
    %38 = const i64 16
    %39 = gep i8, ptr %0, %38
    store i128 %10, ptr %39
    %40 = const i128 1
    store i128 %40, ptr %0
    br bb18
bb9:
    %41 = const i128 0
    store i128 %41, ptr %0
    br bb18
bb10(%11: i128):
    %42 = load i32, ptr %21
    %43 = sext i32 %42 to i64
    switch %43 [ 0: bb11 1: bb12(%11) default: bb1 ]
bb11:
    %44 = const i128 0
    store i128 %44, ptr %0
    br bb18
bb12(%12: i128):
    %45 = const i64 4
    %46 = gep i8, ptr %21, %45
    %47 = load u32, ptr %46
    %48 = const u32 0
    %49 = icmp eq u32 %47, %48
    condbr %49, bb15, bb13(%12, %47)
bb13(%13: i128, %14: u32):
    %50 = const u32 127
    %51 = icmp ugt u32 %14, %50
    condbr %51, bb15, bb14(%13, %14)
bb14(%15: i128, %16: u32):
    %52 = const u32 128
    %53 = icmp ult u32 %16, %52
    condbr %53, bb16(%15, %16), bb19
bb15:
    %54 = const i128 0
    store i128 %54, ptr %0
    br bb18
bb16(%17: i128, %18: u32):
    %55 = const i128 1
    %56 = zext u32 %18 to i128
    %57 = shl i128 %55, %56
    %58 = const i128 1
    %59, %60 = sub.overflow i128 %57, %58
    store i128 %59, ptr %22
    %61 = const i64 16
    %62 = gep i8, ptr %22, %61
    store bool %60, ptr %62
    %63 = const i64 16
    %64 = gep i8, ptr %22, %63
    %65 = load bool, ptr %64
    %66 = const bool false
    %67 = icmp eq bool %65, %66
    condbr %67, bb17(%17), bb19
bb17(%19: i128):
    %68 = load i128, ptr %22
    %69 = and i128 %19, %68
    %70 = const i64 16
    %71 = gep i8, ptr %0, %70
    store i128 %69, ptr %71
    %72 = const i128 1
    store i128 %72, ptr %0
    br bb18
bb18:
    ret
bb19:
    unreachable
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm11checked_mulCsg65pCKkzay5_28trust_fold_cast_halves_slice(functy.4) {
}

fn @Ty__bit_width_with(functy.5) {
bb0(%0: ptr, %1: ptr, %2: u32):
    %8 = alloca i64, align 8
    %9 = alloca i64, align 8
    %10 = alloca (i32, i32), align 4
    %11 = alloca i64, align 8
    %12 = alloca i64, align 8
    %13 = alloca i64, align 8
    store ptr %1, ptr %8
    %14 = load ptr, ptr %8
    %15 = load i64, ptr %14
    %16 = const i64 21
    %17 = const i64 -9223372036854775808
    %18 = icmp eq i64 %15, %17
    %19 = const i64 0
    %20 = select i64 %18, %19, %16
    %21 = const i64 -9223372036854775807
    %22 = icmp eq i64 %15, %21
    %23 = const i64 1
    %24 = select i64 %22, %23, %20
    %25 = const i64 -9223372036854775806
    %26 = icmp eq i64 %15, %25
    %27 = const i64 2
    %28 = select i64 %26, %27, %24
    %29 = const i64 -9223372036854775805
    %30 = icmp eq i64 %15, %29
    %31 = const i64 3
    %32 = select i64 %30, %31, %28
    %33 = const i64 -9223372036854775804
    %34 = icmp eq i64 %15, %33
    %35 = const i64 4
    %36 = select i64 %34, %35, %32
    %37 = const i64 -9223372036854775803
    %38 = icmp eq i64 %15, %37
    %39 = const i64 5
    %40 = select i64 %38, %39, %36
    %41 = const i64 -9223372036854775802
    %42 = icmp eq i64 %15, %41
    %43 = const i64 6
    %44 = select i64 %42, %43, %40
    %45 = const i64 -9223372036854775801
    %46 = icmp eq i64 %15, %45
    %47 = const i64 7
    %48 = select i64 %46, %47, %44
    %49 = const i64 -9223372036854775800
    %50 = icmp eq i64 %15, %49
    %51 = const i64 8
    %52 = select i64 %50, %51, %48
    %53 = const i64 -9223372036854775799
    %54 = icmp eq i64 %15, %53
    %55 = const i64 9
    %56 = select i64 %54, %55, %52
    %57 = const i64 -9223372036854775798
    %58 = icmp eq i64 %15, %57
    %59 = const i64 10
    %60 = select i64 %58, %59, %56
    %61 = const i64 -9223372036854775797
    %62 = icmp eq i64 %15, %61
    %63 = const i64 11
    %64 = select i64 %62, %63, %60
    %65 = const i64 -9223372036854775796
    %66 = icmp eq i64 %15, %65
    %67 = const i64 12
    %68 = select i64 %66, %67, %64
    %69 = const i64 -9223372036854775795
    %70 = icmp eq i64 %15, %69
    %71 = const i64 13
    %72 = select i64 %70, %71, %68
    %73 = const i64 -9223372036854775794
    %74 = icmp eq i64 %15, %73
    %75 = const i64 14
    %76 = select i64 %74, %75, %72
    %77 = const i64 -9223372036854775793
    %78 = icmp eq i64 %15, %77
    %79 = const i64 15
    %80 = select i64 %78, %79, %76
    %81 = const i64 -9223372036854775792
    %82 = icmp eq i64 %15, %81
    %83 = const i64 16
    %84 = select i64 %82, %83, %80
    %85 = const i64 -9223372036854775791
    %86 = icmp eq i64 %15, %85
    %87 = const i64 17
    %88 = select i64 %86, %87, %84
    %89 = const i64 -9223372036854775790
    %90 = icmp eq i64 %15, %89
    %91 = const i64 18
    %92 = select i64 %90, %91, %88
    %93 = const i64 -9223372036854775789
    %94 = icmp eq i64 %15, %93
    %95 = const i64 19
    %96 = select i64 %94, %95, %92
    %97 = const i64 -9223372036854775788
    %98 = icmp eq i64 %15, %97
    %99 = const i64 20
    %100 = select i64 %98, %99, %96
    %101 = const i64 -9223372036854775786
    %102 = icmp eq i64 %15, %101
    %103 = const i64 22
    %104 = select i64 %102, %103, %100
    %105 = const i64 -9223372036854775785
    %106 = icmp eq i64 %15, %105
    %107 = const i64 23
    %108 = select i64 %106, %107, %104
    %109 = const i64 -9223372036854775784
    %110 = icmp eq i64 %15, %109
    %111 = const i64 24
    %112 = select i64 %110, %111, %108
    %113 = const i64 -9223372036854775783
    %114 = icmp eq i64 %15, %113
    %115 = const i64 25
    %116 = select i64 %114, %115, %112
    %117 = const i64 -9223372036854775782
    %118 = icmp eq i64 %15, %117
    %119 = const i64 26
    %120 = select i64 %118, %119, %116
    %121 = const i64 -9223372036854775781
    %122 = icmp eq i64 %15, %121
    %123 = const i64 27
    %124 = select i64 %122, %123, %120
    %125 = const i64 -9223372036854775780
    %126 = icmp eq i64 %15, %125
    %127 = const i64 28
    %128 = select i64 %126, %127, %124
    %129 = const i64 -9223372036854775779
    %130 = icmp eq i64 %15, %129
    %131 = const i64 29
    %132 = select i64 %130, %131, %128
    %133 = const i64 -9223372036854775778
    %134 = icmp eq i64 %15, %133
    %135 = const i64 30
    %136 = select i64 %134, %135, %132
    %137 = const i64 -9223372036854775777
    %138 = icmp eq i64 %15, %137
    %139 = const i64 31
    %140 = select i64 %138, %139, %136
    %141 = const i64 -9223372036854775776
    %142 = icmp eq i64 %15, %141
    %143 = const i64 32
    %144 = select i64 %142, %143, %140
    switch %144 [ 14: bb2(%2) 15: bb4(%2) 16: bb3(%2) 24: bb4(%2) 25: bb4(%2) 26: bb4(%2) 27: bb4(%2) 28: bb4(%2) default: bb1 ]
bb1:
    %145 = load ptr, ptr %8
    call @func.6(%0, %145)
    br bb6
bb2(%3: u32):
    %146 = load ptr, ptr %8
    %147 = const i64 8
    %148 = gep i8, ptr %146, %147
    %149 = load ptr, ptr %8
    %150 = const i64 16
    %151 = gep i8, ptr %149, %150
    store ptr %151, ptr %9
    %152 = load i64, ptr %148
    store i64 %152, ptr %12
    %153 = load ptr, ptr %12
    store ptr %153, ptr %13
    %154 = load ptr, ptr %13
    %155 = ptrtoint ptr %154 to u64
    %156 = const u64 8
    %157 = const u64 1
    %158 = sub u64 %156, %157
    %159 = and u64 %155, %158
    %160 = const u64 0
    %161 = icmp eq u64 %159, %160
    condbr %161, bb7(%3), bb9
bb3(%4: u32):
    %162 = const u32 2
    call @func.4(%0, %4, %162)
    br bb6
bb4(%5: u32):
    %163 = const i64 4
    %164 = gep i8, ptr %0, %163
    store u32 %5, ptr %164
    %165 = const i32 1
    store i32 %165, ptr %0
    br bb6
bb5:
    store ptr %9, ptr %11
    call @func.7(%0, %10, %11)
    br bb6
bb6:
    ret
bb7(%6: u32):
    %166 = load ptr, ptr %13
    %167 = ptrtoint ptr %166 to u64
    %168 = const u64 0
    %169 = icmp eq u64 %167, %168
    %170 = const bool true
    %171 = const bool false
    %172 = select bool %169, %170, %171
    %173 = const bool false
    %174 = icmp eq bool %172, %173
    condbr %174, bb8(%6), bb9
bb8(%7: u32):
    %175 = load ptr, ptr %13
    call @func.5(%10, %175, %7)
    br bb5
bb9:
    unreachable
}

fn @Ty__bit_width(functy.6) {
bb0(%0: ptr, %1: ptr):
    %2 = alloca i64, align 8
    %3 = alloca i64, align 8
    %4 = alloca (i32, i32), align 4
    %5 = alloca i64, align 8
    %6 = alloca i64, align 8
    %7 = alloca i64, align 8
    store ptr %1, ptr %2
    %8 = load ptr, ptr %2
    %9 = load i64, ptr %8
    %10 = const i64 21
    %11 = const i64 -9223372036854775808
    %12 = icmp eq i64 %9, %11
    %13 = const i64 0
    %14 = select i64 %12, %13, %10
    %15 = const i64 -9223372036854775807
    %16 = icmp eq i64 %9, %15
    %17 = const i64 1
    %18 = select i64 %16, %17, %14
    %19 = const i64 -9223372036854775806
    %20 = icmp eq i64 %9, %19
    %21 = const i64 2
    %22 = select i64 %20, %21, %18
    %23 = const i64 -9223372036854775805
    %24 = icmp eq i64 %9, %23
    %25 = const i64 3
    %26 = select i64 %24, %25, %22
    %27 = const i64 -9223372036854775804
    %28 = icmp eq i64 %9, %27
    %29 = const i64 4
    %30 = select i64 %28, %29, %26
    %31 = const i64 -9223372036854775803
    %32 = icmp eq i64 %9, %31
    %33 = const i64 5
    %34 = select i64 %32, %33, %30
    %35 = const i64 -9223372036854775802
    %36 = icmp eq i64 %9, %35
    %37 = const i64 6
    %38 = select i64 %36, %37, %34
    %39 = const i64 -9223372036854775801
    %40 = icmp eq i64 %9, %39
    %41 = const i64 7
    %42 = select i64 %40, %41, %38
    %43 = const i64 -9223372036854775800
    %44 = icmp eq i64 %9, %43
    %45 = const i64 8
    %46 = select i64 %44, %45, %42
    %47 = const i64 -9223372036854775799
    %48 = icmp eq i64 %9, %47
    %49 = const i64 9
    %50 = select i64 %48, %49, %46
    %51 = const i64 -9223372036854775798
    %52 = icmp eq i64 %9, %51
    %53 = const i64 10
    %54 = select i64 %52, %53, %50
    %55 = const i64 -9223372036854775797
    %56 = icmp eq i64 %9, %55
    %57 = const i64 11
    %58 = select i64 %56, %57, %54
    %59 = const i64 -9223372036854775796
    %60 = icmp eq i64 %9, %59
    %61 = const i64 12
    %62 = select i64 %60, %61, %58
    %63 = const i64 -9223372036854775795
    %64 = icmp eq i64 %9, %63
    %65 = const i64 13
    %66 = select i64 %64, %65, %62
    %67 = const i64 -9223372036854775794
    %68 = icmp eq i64 %9, %67
    %69 = const i64 14
    %70 = select i64 %68, %69, %66
    %71 = const i64 -9223372036854775793
    %72 = icmp eq i64 %9, %71
    %73 = const i64 15
    %74 = select i64 %72, %73, %70
    %75 = const i64 -9223372036854775792
    %76 = icmp eq i64 %9, %75
    %77 = const i64 16
    %78 = select i64 %76, %77, %74
    %79 = const i64 -9223372036854775791
    %80 = icmp eq i64 %9, %79
    %81 = const i64 17
    %82 = select i64 %80, %81, %78
    %83 = const i64 -9223372036854775790
    %84 = icmp eq i64 %9, %83
    %85 = const i64 18
    %86 = select i64 %84, %85, %82
    %87 = const i64 -9223372036854775789
    %88 = icmp eq i64 %9, %87
    %89 = const i64 19
    %90 = select i64 %88, %89, %86
    %91 = const i64 -9223372036854775788
    %92 = icmp eq i64 %9, %91
    %93 = const i64 20
    %94 = select i64 %92, %93, %90
    %95 = const i64 -9223372036854775786
    %96 = icmp eq i64 %9, %95
    %97 = const i64 22
    %98 = select i64 %96, %97, %94
    %99 = const i64 -9223372036854775785
    %100 = icmp eq i64 %9, %99
    %101 = const i64 23
    %102 = select i64 %100, %101, %98
    %103 = const i64 -9223372036854775784
    %104 = icmp eq i64 %9, %103
    %105 = const i64 24
    %106 = select i64 %104, %105, %102
    %107 = const i64 -9223372036854775783
    %108 = icmp eq i64 %9, %107
    %109 = const i64 25
    %110 = select i64 %108, %109, %106
    %111 = const i64 -9223372036854775782
    %112 = icmp eq i64 %9, %111
    %113 = const i64 26
    %114 = select i64 %112, %113, %110
    %115 = const i64 -9223372036854775781
    %116 = icmp eq i64 %9, %115
    %117 = const i64 27
    %118 = select i64 %116, %117, %114
    %119 = const i64 -9223372036854775780
    %120 = icmp eq i64 %9, %119
    %121 = const i64 28
    %122 = select i64 %120, %121, %118
    %123 = const i64 -9223372036854775779
    %124 = icmp eq i64 %9, %123
    %125 = const i64 29
    %126 = select i64 %124, %125, %122
    %127 = const i64 -9223372036854775778
    %128 = icmp eq i64 %9, %127
    %129 = const i64 30
    %130 = select i64 %128, %129, %126
    %131 = const i64 -9223372036854775777
    %132 = icmp eq i64 %9, %131
    %133 = const i64 31
    %134 = select i64 %132, %133, %130
    %135 = const i64 -9223372036854775776
    %136 = icmp eq i64 %9, %135
    %137 = const i64 32
    %138 = select i64 %136, %137, %134
    switch %138 [ 0: bb11 1: bb10 2: bb9 3: bb8 4: bb7 5: bb11 6: bb10 7: bb9 8: bb8 9: bb7 10: bb6 11: bb5 12: bb4 13: bb12 14: bb3 15: bb2 16: bb2 24: bb2 25: bb2 26: bb2 27: bb2 28: bb2 default: bb1 ]
bb1:
    %139 = const i32 0
    store i32 %139, ptr %0
    br bb14
bb2:
    %140 = const i32 0
    store i32 %140, ptr %0
    br bb14
bb3:
    %141 = load ptr, ptr %2
    %142 = const i64 8
    %143 = gep i8, ptr %141, %142
    %144 = load ptr, ptr %2
    %145 = const i64 16
    %146 = gep i8, ptr %144, %145
    store ptr %146, ptr %3
    %147 = load i64, ptr %143
    store i64 %147, ptr %6
    %148 = load ptr, ptr %6
    store ptr %148, ptr %7
    %149 = load ptr, ptr %7
    %150 = ptrtoint ptr %149 to u64
    %151 = const u64 8
    %152 = const u64 1
    %153 = sub u64 %151, %152
    %154 = and u64 %150, %153
    %155 = const u64 0
    %156 = icmp eq u64 %154, %155
    condbr %156, bb15, bb17
bb4:
    %157 = const u32 64
    %158 = const i64 4
    %159 = gep i8, ptr %0, %158
    store u32 %157, ptr %159
    %160 = const i32 1
    store i32 %160, ptr %0
    br bb14
bb5:
    %161 = const u32 32
    %162 = const i64 4
    %163 = gep i8, ptr %0, %162
    store u32 %161, ptr %163
    %164 = const i32 1
    store i32 %164, ptr %0
    br bb14
bb6:
    %165 = const u32 16
    %166 = const i64 4
    %167 = gep i8, ptr %0, %166
    store u32 %165, ptr %167
    %168 = const i32 1
    store i32 %168, ptr %0
    br bb14
bb7:
    %169 = const u32 128
    %170 = const i64 4
    %171 = gep i8, ptr %0, %170
    store u32 %169, ptr %171
    %172 = const i32 1
    store i32 %172, ptr %0
    br bb14
bb8:
    %173 = const u32 64
    %174 = const i64 4
    %175 = gep i8, ptr %0, %174
    store u32 %173, ptr %175
    %176 = const i32 1
    store i32 %176, ptr %0
    br bb14
bb9:
    %177 = const u32 32
    %178 = const i64 4
    %179 = gep i8, ptr %0, %178
    store u32 %177, ptr %179
    %180 = const i32 1
    store i32 %180, ptr %0
    br bb14
bb10:
    %181 = const u32 16
    %182 = const i64 4
    %183 = gep i8, ptr %0, %182
    store u32 %181, ptr %183
    %184 = const i32 1
    store i32 %184, ptr %0
    br bb14
bb11:
    %185 = const u32 8
    %186 = const i64 4
    %187 = gep i8, ptr %0, %186
    store u32 %185, ptr %187
    %188 = const i32 1
    store i32 %188, ptr %0
    br bb14
bb12:
    %189 = const u32 1
    %190 = const i64 4
    %191 = gep i8, ptr %0, %190
    store u32 %189, ptr %191
    %192 = const i32 1
    store i32 %192, ptr %0
    br bb14
bb13:
    store ptr %3, ptr %5
    call @func.8(%0, %4, %5)
    br bb14
bb14:
    ret
bb15:
    %193 = load ptr, ptr %7
    %194 = ptrtoint ptr %193 to u64
    %195 = const u64 0
    %196 = icmp eq u64 %194, %195
    %197 = const bool true
    %198 = const bool false
    %199 = select bool %196, %197, %198
    %200 = const bool false
    %201 = icmp eq bool %199, %200
    condbr %201, bb16, bb17
bb16:
    %202 = load ptr, ptr %7
    call @func.6(%4, %202)
    br bb13
bb17:
    unreachable
}

fn @std__option__Option___T___and_then__monofee3f10092efc55a(functy.7) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %3 = alloca i64, align 8
    %4 = alloca i32, align 4
    %5 = load i32, ptr %1
    %6 = sext i32 %5 to i64
    switch %6 [ 0: bb2 1: bb3 default: bb1 ]
bb1:
    unreachable
bb2:
    %7 = const i32 0
    store i32 %7, ptr %0
    br bb5
bb3:
    %8 = const i64 4
    %9 = gep i8, ptr %1, %8
    %10 = load u32, ptr %9
    %11 = load i64, ptr %2
    store i64 %11, ptr %3
    store u32 %10, ptr %4
    %12 = load u32, ptr %4
    call @func.10(%0, %3, %12)
    br bb4
bb4:
    br bb5
bb5:
    ret
}

fn @std__option__Option___T___and_then__mono9d0e2b10d4da2997(functy.8) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %3 = alloca i64, align 8
    %4 = alloca i32, align 4
    %5 = load i32, ptr %1
    %6 = sext i32 %5 to i64
    switch %6 [ 0: bb2 1: bb3 default: bb1 ]
bb1:
    unreachable
bb2:
    %7 = const i32 0
    store i32 %7, ptr %0
    br bb5
bb3:
    %8 = const i64 4
    %9 = gep i8, ptr %1, %8
    %10 = load u32, ptr %9
    %11 = load i64, ptr %2
    store i64 %11, ptr %3
    store u32 %10, ptr %4
    %12 = load u32, ptr %4
    call @func.12(%0, %3, %12)
    br bb4
bb4:
    br bb5
bb5:
    ret
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm11checked_mulCsg65pCKkzay5_28trust_fold_cast_halves_slice(functy.9) {
}

fn @Ty__bit_width_with___closure_0_(functy.10) {
bb0(%0: ptr, %1: ptr, %2: u32):
    %3 = load ptr, ptr %1
    %4 = load ptr, ptr %3
    %5 = load u32, ptr %4
    call @func.9(%0, %2, %5)
    br bb1
bb1:
    ret
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm11checked_mulCsg65pCKkzay5_28trust_fold_cast_halves_slice(functy.11) {
}

fn @Ty__bit_width___closure_0_(functy.12) {
bb0(%0: ptr, %1: ptr, %2: u32):
    %3 = load ptr, ptr %1
    %4 = load ptr, ptr %3
    %5 = load u32, ptr %4
    call @func.11(%0, %2, %5)
    br bb1
bb1:
    ret
}
"#;

/// The VERBATIM-`?` module (symptom-2 probe shape: the byte-for-byte
/// production body lowering through the `Try::branch`/`FromResidual`/
/// `then_some` empty-bodied shims; root `fold_cast_entry_try`; emitted
/// 2026-07-02, 24163 bytes, validate_module = 0, re-parse OK).
const FOLD_CAST_TRY_IR: &str = r#"; TrustIr text format v1
module "mir::closure::fold_cast_entry_try"

functy.0 = (u32, u32, ptr, ptr) -> ()

functy.1 = (ptr, u32) -> ()

functy.2 = (ptr, u32) -> ()

functy.3 = (ptr, ptr) -> ()

functy.4 = (ptr) -> ()

functy.5 = (ptr, bool, i128) -> ()

functy.6 = (ptr, ptr) -> ()

functy.7 = (ptr, u8, ptr, ptr, ptr) -> ()

functy.8 = (ptr, u32, u32) -> ()

functy.9 = (ptr, ptr, u32) -> ()

functy.10 = (ptr, ptr) -> ()

functy.11 = (ptr, ptr, ptr) -> ()

functy.12 = (ptr, ptr, ptr) -> ()

functy.13 = (ptr, u32, u32) -> ()

functy.14 = (ptr, ptr, u32) -> ()

functy.15 = (ptr, u32, u32) -> ()

functy.16 = (ptr, ptr, u32) -> ()

fn @fold_cast_entry_try(functy.0) {
bb0(%0: u32, %1: u32, %2: ptr, %3: ptr):
    %20 = alloca (i128, i128), align 16
    %21 = alloca i8, align 1
    %22 = alloca (i64, i64, i64), align 8
    %23 = alloca (i64, i64, i64), align 8
    %24 = alloca (i128, i128), align 16
    %25 = alloca (i128, i128), align 16
    %26 = load u64, ptr %2
    %27 = const u64 0
    %28 = icmp ne u64 %26, %27
    condbr %28, bb1(%0, %1, %2, %3), bb2(%0, %1, %3)
bb1(%4: u32, %5: u32, %6: ptr, %7: ptr):
    %29 = const i64 16
    %30 = gep i8, ptr %6, %29
    %31 = load i128, ptr %30
    %32 = const i64 16
    %33 = gep i8, ptr %20, %32
    store i128 %31, ptr %33
    %34 = const i128 1
    store i128 %34, ptr %20
    br bb3(%4, %5, %7)
bb2(%8: u32, %9: u32, %10: ptr):
    %35 = const i128 0
    store i128 %35, ptr %20
    br bb3(%8, %9, %10)
bb3(%11: u32, %12: u32, %13: ptr):
    call @func.1(%21, %11)
    br bb4(%12, %13)
bb4(%14: u32, %15: ptr):
    call @func.2(%22, %14)
    br bb5(%15)
bb5(%16: ptr):
    %36 = const i64 -9223372036854775805
    store i64 %36, ptr %23
    %37 = load i128, ptr %20
    store i128 %37, ptr %25
    %38 = const i64 16
    %39 = gep i8, ptr %20, %38
    %40 = const i64 16
    %41 = gep i8, ptr %25, %40
    %42 = load i128, ptr %39
    store i128 %42, ptr %41
    %43 = load u8, ptr %21
    call @func.7(%24, %43, %23, %22, %25)
    br bb6(%16)
bb6(%17: ptr):
    %44 = load i128, ptr %24
    %45 = trunc i128 %44 to i64
    switch %45 [ 0: bb8(%17) 1: bb9(%17) default: bb7 ]
bb7:
    unreachable
bb8(%18: ptr):
    %46 = const u64 0
    store u64 %46, ptr %18
    %47 = const i128 0
    %48 = const i64 16
    %49 = gep i8, ptr %18, %48
    store i128 %47, ptr %49
    br bb10
bb9(%19: ptr):
    %50 = const i64 16
    %51 = gep i8, ptr %24, %50
    %52 = load i128, ptr %51
    %53 = const u64 1
    store u64 %53, ptr %19
    %54 = const i64 16
    %55 = gep i8, ptr %19, %54
    store i128 %52, ptr %55
    br bb10
bb10:
    br bb11
bb11:
    br bb12
bb12:
    ret
}

fn @cast_op_for_tag(functy.1) {
bb0(%0: ptr, %1: u32):
    switch %1 [ 0: bb15 1: bb14 2: bb13 3: bb12 4: bb11 5: bb10 6: bb9 7: bb8 8: bb7 9: bb6 10: bb5 11: bb4 12: bb3 13: bb2 default: bb1 ]
bb1:
    %2 = const i8 14
    store i8 %2, ptr %0
    br bb16
bb2:
    %3 = const i8 13
    store i8 %3, ptr %0
    br bb16
bb3:
    %4 = const i8 12
    store i8 %4, ptr %0
    br bb16
bb4:
    %5 = const i8 11
    store i8 %5, ptr %0
    br bb16
bb5:
    %6 = const i8 10
    store i8 %6, ptr %0
    br bb16
bb6:
    %7 = const i8 9
    store i8 %7, ptr %0
    br bb16
bb7:
    %8 = const i8 8
    store i8 %8, ptr %0
    br bb16
bb8:
    %9 = const i8 7
    store i8 %9, ptr %0
    br bb16
bb9:
    %10 = const i8 6
    store i8 %10, ptr %0
    br bb16
bb10:
    %11 = const i8 5
    store i8 %11, ptr %0
    br bb16
bb11:
    %12 = const i8 4
    store i8 %12, ptr %0
    br bb16
bb12:
    %13 = const i8 3
    store i8 %13, ptr %0
    br bb16
bb13:
    %14 = const i8 2
    store i8 %14, ptr %0
    br bb16
bb14:
    %15 = const i8 1
    store i8 %15, ptr %0
    br bb16
bb15:
    %16 = const i8 0
    store i8 %16, ptr %0
    br bb16
bb16:
    ret
}

fn @dst_ty_for_tag(functy.2) {
bb0(%0: ptr, %1: u32):
    %2 = alloca i32, align 4
    switch %1 [ 0: bb14 1: bb13 2: bb12 3: bb11 4: bb10 5: bb9 6: bb8 7: bb7 8: bb6 9: bb5 10: bb4 11: bb3 12: bb2 default: bb1 ]
bb1:
    %3 = const u32 0
    store u32 %3, ptr %2
    %4 = const i64 8
    %5 = gep i8, ptr %0, %4
    %6 = load i32, ptr %2
    store i32 %6, ptr %5
    %7 = const i64 -9223372036854775789
    store i64 %7, ptr %0
    br bb15
bb2:
    %8 = const i64 -9223372036854775791
    store i64 %8, ptr %0
    br bb15
bb3:
    %9 = const i64 -9223372036854775793
    store i64 %9, ptr %0
    br bb15
bb4:
    %10 = const i64 -9223372036854775795
    store i64 %10, ptr %0
    br bb15
bb5:
    %11 = const i64 -9223372036854775799
    store i64 %11, ptr %0
    br bb15
bb6:
    %12 = const i64 -9223372036854775800
    store i64 %12, ptr %0
    br bb15
bb7:
    %13 = const i64 -9223372036854775801
    store i64 %13, ptr %0
    br bb15
bb8:
    %14 = const i64 -9223372036854775802
    store i64 %14, ptr %0
    br bb15
bb9:
    %15 = const i64 -9223372036854775803
    store i64 %15, ptr %0
    br bb15
bb10:
    %16 = const i64 -9223372036854775804
    store i64 %16, ptr %0
    br bb15
bb11:
    %17 = const i64 -9223372036854775805
    store i64 %17, ptr %0
    br bb15
bb12:
    %18 = const i64 -9223372036854775806
    store i64 %18, ptr %0
    br bb15
bb13:
    %19 = const i64 -9223372036854775807
    store i64 %19, ptr %0
    br bb15
bb14:
    %20 = const i64 -9223372036854775808
    store i64 %20, ptr %0
    br bb15
bb15:
    ret
}

fn @_RNvXsJ_NtCs2EYQwhfuABO_4core6optionINtB5_6OptionnENtNtNtB7_3ops9try_trait3Try6branchCs8ad5MLNZt89_25trust_fold_cast_try_slice(functy.3) {
}

fn @_RNvXsK_NtCs2EYQwhfuABO_4core6optionINtB5_6OptionnEINtNtNtB7_3ops9try_trait12FromResidualIBy_NtNtB7_7convert10InfallibleEE13from_residualCs8ad5MLNZt89_25trust_fold_cast_try_slice(functy.4) {
}

fn @_RINvMNtCs2EYQwhfuABO_4core4boolb9then_somenECs8ad5MLNZt89_25trust_fold_cast_try_slice(functy.5) {
}

fn @_RNvXsJ_NtCs2EYQwhfuABO_4core6optionINtB5_6OptionmENtNtNtB7_3ops9try_trait3Try6branchCs8ad5MLNZt89_25trust_fold_cast_try_slice(functy.6) {
}

fn @fold_cast(functy.7) {
bb0(%0: ptr, %1: u8, %2: ptr, %3: ptr, %4: ptr):
    %21 = alloca i8, align 1
    %22 = alloca (i128, i128), align 16
    %23 = alloca (i32, i32), align 4
    %24 = alloca (i32, i32), align 4
    %25 = alloca (i128, i128), align 16
    store u8 %1, ptr %21
    call @func.3(%22, %4)
    br bb1(%3)
bb1(%5: ptr):
    %26 = load i128, ptr %22
    %27 = trunc i128 %26 to i64
    switch %27 [ 0: bb3(%5) 1: bb4 default: bb2 ]
bb2:
    unreachable
bb3(%6: ptr):
    %28 = const i64 16
    %29 = gep i8, ptr %22, %28
    %30 = load i128, ptr %29
    %31 = load i8, ptr %21
    %32 = sext i8 %31 to i64
    switch %32 [ 0: bb6(%6, %30) 1: bb7(%30) 2: bb8(%30) 12: bb8(%30) default: bb5 ]
bb4:
    call @func.4(%0)
    br bb18
bb5:
    %33 = const i128 0
    store i128 %33, ptr %0
    br bb18
bb6(%7: ptr, %8: i128):
    %34 = const u32 64
    call @func.9(%24, %7, %34)
    br bb9(%8)
bb7(%9: i128):
    %35 = const i128 0
    %36 = icmp sge i128 %9, %35
    call @func.5(%0, %36, %9)
    br bb18
bb8(%10: i128):
    %37 = const i64 16
    %38 = gep i8, ptr %0, %37
    store i128 %10, ptr %38
    %39 = const i128 1
    store i128 %39, ptr %0
    br bb18
bb9(%11: i128):
    call @func.6(%23, %24)
    br bb10(%11)
bb10(%12: i128):
    %40 = load i32, ptr %23
    %41 = sext i32 %40 to i64
    switch %41 [ 0: bb11(%12) 1: bb12 default: bb2 ]
bb11(%13: i128):
    %42 = const i64 4
    %43 = gep i8, ptr %23, %42
    %44 = load u32, ptr %43
    %45 = const u32 0
    %46 = icmp eq u32 %44, %45
    condbr %46, bb15, bb13(%13, %44)
bb12:
    call @func.4(%0)
    br bb18
bb13(%14: i128, %15: u32):
    %47 = const u32 127
    %48 = icmp ugt u32 %15, %47
    condbr %48, bb15, bb14(%14, %15)
bb14(%16: i128, %17: u32):
    %49 = const u32 128
    %50 = icmp ult u32 %17, %49
    condbr %50, bb16(%16, %17), bb19
bb15:
    %51 = const i128 0
    store i128 %51, ptr %0
    br bb18
bb16(%18: i128, %19: u32):
    %52 = const i128 1
    %53 = zext u32 %19 to i128
    %54 = shl i128 %52, %53
    %55 = const i128 1
    %56, %57 = sub.overflow i128 %54, %55
    store i128 %56, ptr %25
    %58 = const i64 16
    %59 = gep i8, ptr %25, %58
    store bool %57, ptr %59
    %60 = const i64 16
    %61 = gep i8, ptr %25, %60
    %62 = load bool, ptr %61
    %63 = const bool false
    %64 = icmp eq bool %62, %63
    condbr %64, bb17(%18), bb19
bb17(%20: i128):
    %65 = load i128, ptr %25
    %66 = and i128 %20, %65
    %67 = const i64 16
    %68 = gep i8, ptr %0, %67
    store i128 %66, ptr %68
    %69 = const i128 1
    store i128 %69, ptr %0
    br bb18
bb18:
    ret
bb19:
    unreachable
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm11checked_mulCs8ad5MLNZt89_25trust_fold_cast_try_slice(functy.8) {
}

fn @Ty__bit_width_with(functy.9) {
bb0(%0: ptr, %1: ptr, %2: u32):
    %8 = alloca i64, align 8
    %9 = alloca i64, align 8
    %10 = alloca (i32, i32), align 4
    %11 = alloca i64, align 8
    %12 = alloca i64, align 8
    %13 = alloca i64, align 8
    store ptr %1, ptr %8
    %14 = load ptr, ptr %8
    %15 = load i64, ptr %14
    %16 = const i64 21
    %17 = const i64 -9223372036854775808
    %18 = icmp eq i64 %15, %17
    %19 = const i64 0
    %20 = select i64 %18, %19, %16
    %21 = const i64 -9223372036854775807
    %22 = icmp eq i64 %15, %21
    %23 = const i64 1
    %24 = select i64 %22, %23, %20
    %25 = const i64 -9223372036854775806
    %26 = icmp eq i64 %15, %25
    %27 = const i64 2
    %28 = select i64 %26, %27, %24
    %29 = const i64 -9223372036854775805
    %30 = icmp eq i64 %15, %29
    %31 = const i64 3
    %32 = select i64 %30, %31, %28
    %33 = const i64 -9223372036854775804
    %34 = icmp eq i64 %15, %33
    %35 = const i64 4
    %36 = select i64 %34, %35, %32
    %37 = const i64 -9223372036854775803
    %38 = icmp eq i64 %15, %37
    %39 = const i64 5
    %40 = select i64 %38, %39, %36
    %41 = const i64 -9223372036854775802
    %42 = icmp eq i64 %15, %41
    %43 = const i64 6
    %44 = select i64 %42, %43, %40
    %45 = const i64 -9223372036854775801
    %46 = icmp eq i64 %15, %45
    %47 = const i64 7
    %48 = select i64 %46, %47, %44
    %49 = const i64 -9223372036854775800
    %50 = icmp eq i64 %15, %49
    %51 = const i64 8
    %52 = select i64 %50, %51, %48
    %53 = const i64 -9223372036854775799
    %54 = icmp eq i64 %15, %53
    %55 = const i64 9
    %56 = select i64 %54, %55, %52
    %57 = const i64 -9223372036854775798
    %58 = icmp eq i64 %15, %57
    %59 = const i64 10
    %60 = select i64 %58, %59, %56
    %61 = const i64 -9223372036854775797
    %62 = icmp eq i64 %15, %61
    %63 = const i64 11
    %64 = select i64 %62, %63, %60
    %65 = const i64 -9223372036854775796
    %66 = icmp eq i64 %15, %65
    %67 = const i64 12
    %68 = select i64 %66, %67, %64
    %69 = const i64 -9223372036854775795
    %70 = icmp eq i64 %15, %69
    %71 = const i64 13
    %72 = select i64 %70, %71, %68
    %73 = const i64 -9223372036854775794
    %74 = icmp eq i64 %15, %73
    %75 = const i64 14
    %76 = select i64 %74, %75, %72
    %77 = const i64 -9223372036854775793
    %78 = icmp eq i64 %15, %77
    %79 = const i64 15
    %80 = select i64 %78, %79, %76
    %81 = const i64 -9223372036854775792
    %82 = icmp eq i64 %15, %81
    %83 = const i64 16
    %84 = select i64 %82, %83, %80
    %85 = const i64 -9223372036854775791
    %86 = icmp eq i64 %15, %85
    %87 = const i64 17
    %88 = select i64 %86, %87, %84
    %89 = const i64 -9223372036854775790
    %90 = icmp eq i64 %15, %89
    %91 = const i64 18
    %92 = select i64 %90, %91, %88
    %93 = const i64 -9223372036854775789
    %94 = icmp eq i64 %15, %93
    %95 = const i64 19
    %96 = select i64 %94, %95, %92
    %97 = const i64 -9223372036854775788
    %98 = icmp eq i64 %15, %97
    %99 = const i64 20
    %100 = select i64 %98, %99, %96
    %101 = const i64 -9223372036854775786
    %102 = icmp eq i64 %15, %101
    %103 = const i64 22
    %104 = select i64 %102, %103, %100
    %105 = const i64 -9223372036854775785
    %106 = icmp eq i64 %15, %105
    %107 = const i64 23
    %108 = select i64 %106, %107, %104
    %109 = const i64 -9223372036854775784
    %110 = icmp eq i64 %15, %109
    %111 = const i64 24
    %112 = select i64 %110, %111, %108
    %113 = const i64 -9223372036854775783
    %114 = icmp eq i64 %15, %113
    %115 = const i64 25
    %116 = select i64 %114, %115, %112
    %117 = const i64 -9223372036854775782
    %118 = icmp eq i64 %15, %117
    %119 = const i64 26
    %120 = select i64 %118, %119, %116
    %121 = const i64 -9223372036854775781
    %122 = icmp eq i64 %15, %121
    %123 = const i64 27
    %124 = select i64 %122, %123, %120
    %125 = const i64 -9223372036854775780
    %126 = icmp eq i64 %15, %125
    %127 = const i64 28
    %128 = select i64 %126, %127, %124
    %129 = const i64 -9223372036854775779
    %130 = icmp eq i64 %15, %129
    %131 = const i64 29
    %132 = select i64 %130, %131, %128
    %133 = const i64 -9223372036854775778
    %134 = icmp eq i64 %15, %133
    %135 = const i64 30
    %136 = select i64 %134, %135, %132
    %137 = const i64 -9223372036854775777
    %138 = icmp eq i64 %15, %137
    %139 = const i64 31
    %140 = select i64 %138, %139, %136
    %141 = const i64 -9223372036854775776
    %142 = icmp eq i64 %15, %141
    %143 = const i64 32
    %144 = select i64 %142, %143, %140
    switch %144 [ 14: bb2(%2) 15: bb4(%2) 16: bb3(%2) 24: bb4(%2) 25: bb4(%2) 26: bb4(%2) 27: bb4(%2) 28: bb4(%2) default: bb1 ]
bb1:
    %145 = load ptr, ptr %8
    call @func.10(%0, %145)
    br bb6
bb2(%3: u32):
    %146 = load ptr, ptr %8
    %147 = const i64 8
    %148 = gep i8, ptr %146, %147
    %149 = load ptr, ptr %8
    %150 = const i64 16
    %151 = gep i8, ptr %149, %150
    store ptr %151, ptr %9
    %152 = load i64, ptr %148
    store i64 %152, ptr %12
    %153 = load ptr, ptr %12
    store ptr %153, ptr %13
    %154 = load ptr, ptr %13
    %155 = ptrtoint ptr %154 to u64
    %156 = const u64 8
    %157 = const u64 1
    %158 = sub u64 %156, %157
    %159 = and u64 %155, %158
    %160 = const u64 0
    %161 = icmp eq u64 %159, %160
    condbr %161, bb7(%3), bb9
bb3(%4: u32):
    %162 = const u32 2
    call @func.8(%0, %4, %162)
    br bb6
bb4(%5: u32):
    %163 = const i64 4
    %164 = gep i8, ptr %0, %163
    store u32 %5, ptr %164
    %165 = const i32 1
    store i32 %165, ptr %0
    br bb6
bb5:
    store ptr %9, ptr %11
    call @func.11(%0, %10, %11)
    br bb6
bb6:
    ret
bb7(%6: u32):
    %166 = load ptr, ptr %13
    %167 = ptrtoint ptr %166 to u64
    %168 = const u64 0
    %169 = icmp eq u64 %167, %168
    %170 = const bool true
    %171 = const bool false
    %172 = select bool %169, %170, %171
    %173 = const bool false
    %174 = icmp eq bool %172, %173
    condbr %174, bb8(%6), bb9
bb8(%7: u32):
    %175 = load ptr, ptr %13
    call @func.9(%10, %175, %7)
    br bb5
bb9:
    unreachable
}

fn @Ty__bit_width(functy.10) {
bb0(%0: ptr, %1: ptr):
    %2 = alloca i64, align 8
    %3 = alloca i64, align 8
    %4 = alloca (i32, i32), align 4
    %5 = alloca i64, align 8
    %6 = alloca i64, align 8
    %7 = alloca i64, align 8
    store ptr %1, ptr %2
    %8 = load ptr, ptr %2
    %9 = load i64, ptr %8
    %10 = const i64 21
    %11 = const i64 -9223372036854775808
    %12 = icmp eq i64 %9, %11
    %13 = const i64 0
    %14 = select i64 %12, %13, %10
    %15 = const i64 -9223372036854775807
    %16 = icmp eq i64 %9, %15
    %17 = const i64 1
    %18 = select i64 %16, %17, %14
    %19 = const i64 -9223372036854775806
    %20 = icmp eq i64 %9, %19
    %21 = const i64 2
    %22 = select i64 %20, %21, %18
    %23 = const i64 -9223372036854775805
    %24 = icmp eq i64 %9, %23
    %25 = const i64 3
    %26 = select i64 %24, %25, %22
    %27 = const i64 -9223372036854775804
    %28 = icmp eq i64 %9, %27
    %29 = const i64 4
    %30 = select i64 %28, %29, %26
    %31 = const i64 -9223372036854775803
    %32 = icmp eq i64 %9, %31
    %33 = const i64 5
    %34 = select i64 %32, %33, %30
    %35 = const i64 -9223372036854775802
    %36 = icmp eq i64 %9, %35
    %37 = const i64 6
    %38 = select i64 %36, %37, %34
    %39 = const i64 -9223372036854775801
    %40 = icmp eq i64 %9, %39
    %41 = const i64 7
    %42 = select i64 %40, %41, %38
    %43 = const i64 -9223372036854775800
    %44 = icmp eq i64 %9, %43
    %45 = const i64 8
    %46 = select i64 %44, %45, %42
    %47 = const i64 -9223372036854775799
    %48 = icmp eq i64 %9, %47
    %49 = const i64 9
    %50 = select i64 %48, %49, %46
    %51 = const i64 -9223372036854775798
    %52 = icmp eq i64 %9, %51
    %53 = const i64 10
    %54 = select i64 %52, %53, %50
    %55 = const i64 -9223372036854775797
    %56 = icmp eq i64 %9, %55
    %57 = const i64 11
    %58 = select i64 %56, %57, %54
    %59 = const i64 -9223372036854775796
    %60 = icmp eq i64 %9, %59
    %61 = const i64 12
    %62 = select i64 %60, %61, %58
    %63 = const i64 -9223372036854775795
    %64 = icmp eq i64 %9, %63
    %65 = const i64 13
    %66 = select i64 %64, %65, %62
    %67 = const i64 -9223372036854775794
    %68 = icmp eq i64 %9, %67
    %69 = const i64 14
    %70 = select i64 %68, %69, %66
    %71 = const i64 -9223372036854775793
    %72 = icmp eq i64 %9, %71
    %73 = const i64 15
    %74 = select i64 %72, %73, %70
    %75 = const i64 -9223372036854775792
    %76 = icmp eq i64 %9, %75
    %77 = const i64 16
    %78 = select i64 %76, %77, %74
    %79 = const i64 -9223372036854775791
    %80 = icmp eq i64 %9, %79
    %81 = const i64 17
    %82 = select i64 %80, %81, %78
    %83 = const i64 -9223372036854775790
    %84 = icmp eq i64 %9, %83
    %85 = const i64 18
    %86 = select i64 %84, %85, %82
    %87 = const i64 -9223372036854775789
    %88 = icmp eq i64 %9, %87
    %89 = const i64 19
    %90 = select i64 %88, %89, %86
    %91 = const i64 -9223372036854775788
    %92 = icmp eq i64 %9, %91
    %93 = const i64 20
    %94 = select i64 %92, %93, %90
    %95 = const i64 -9223372036854775786
    %96 = icmp eq i64 %9, %95
    %97 = const i64 22
    %98 = select i64 %96, %97, %94
    %99 = const i64 -9223372036854775785
    %100 = icmp eq i64 %9, %99
    %101 = const i64 23
    %102 = select i64 %100, %101, %98
    %103 = const i64 -9223372036854775784
    %104 = icmp eq i64 %9, %103
    %105 = const i64 24
    %106 = select i64 %104, %105, %102
    %107 = const i64 -9223372036854775783
    %108 = icmp eq i64 %9, %107
    %109 = const i64 25
    %110 = select i64 %108, %109, %106
    %111 = const i64 -9223372036854775782
    %112 = icmp eq i64 %9, %111
    %113 = const i64 26
    %114 = select i64 %112, %113, %110
    %115 = const i64 -9223372036854775781
    %116 = icmp eq i64 %9, %115
    %117 = const i64 27
    %118 = select i64 %116, %117, %114
    %119 = const i64 -9223372036854775780
    %120 = icmp eq i64 %9, %119
    %121 = const i64 28
    %122 = select i64 %120, %121, %118
    %123 = const i64 -9223372036854775779
    %124 = icmp eq i64 %9, %123
    %125 = const i64 29
    %126 = select i64 %124, %125, %122
    %127 = const i64 -9223372036854775778
    %128 = icmp eq i64 %9, %127
    %129 = const i64 30
    %130 = select i64 %128, %129, %126
    %131 = const i64 -9223372036854775777
    %132 = icmp eq i64 %9, %131
    %133 = const i64 31
    %134 = select i64 %132, %133, %130
    %135 = const i64 -9223372036854775776
    %136 = icmp eq i64 %9, %135
    %137 = const i64 32
    %138 = select i64 %136, %137, %134
    switch %138 [ 0: bb11 1: bb10 2: bb9 3: bb8 4: bb7 5: bb11 6: bb10 7: bb9 8: bb8 9: bb7 10: bb6 11: bb5 12: bb4 13: bb12 14: bb3 15: bb2 16: bb2 24: bb2 25: bb2 26: bb2 27: bb2 28: bb2 default: bb1 ]
bb1:
    %139 = const i32 0
    store i32 %139, ptr %0
    br bb14
bb2:
    %140 = const i32 0
    store i32 %140, ptr %0
    br bb14
bb3:
    %141 = load ptr, ptr %2
    %142 = const i64 8
    %143 = gep i8, ptr %141, %142
    %144 = load ptr, ptr %2
    %145 = const i64 16
    %146 = gep i8, ptr %144, %145
    store ptr %146, ptr %3
    %147 = load i64, ptr %143
    store i64 %147, ptr %6
    %148 = load ptr, ptr %6
    store ptr %148, ptr %7
    %149 = load ptr, ptr %7
    %150 = ptrtoint ptr %149 to u64
    %151 = const u64 8
    %152 = const u64 1
    %153 = sub u64 %151, %152
    %154 = and u64 %150, %153
    %155 = const u64 0
    %156 = icmp eq u64 %154, %155
    condbr %156, bb15, bb17
bb4:
    %157 = const u32 64
    %158 = const i64 4
    %159 = gep i8, ptr %0, %158
    store u32 %157, ptr %159
    %160 = const i32 1
    store i32 %160, ptr %0
    br bb14
bb5:
    %161 = const u32 32
    %162 = const i64 4
    %163 = gep i8, ptr %0, %162
    store u32 %161, ptr %163
    %164 = const i32 1
    store i32 %164, ptr %0
    br bb14
bb6:
    %165 = const u32 16
    %166 = const i64 4
    %167 = gep i8, ptr %0, %166
    store u32 %165, ptr %167
    %168 = const i32 1
    store i32 %168, ptr %0
    br bb14
bb7:
    %169 = const u32 128
    %170 = const i64 4
    %171 = gep i8, ptr %0, %170
    store u32 %169, ptr %171
    %172 = const i32 1
    store i32 %172, ptr %0
    br bb14
bb8:
    %173 = const u32 64
    %174 = const i64 4
    %175 = gep i8, ptr %0, %174
    store u32 %173, ptr %175
    %176 = const i32 1
    store i32 %176, ptr %0
    br bb14
bb9:
    %177 = const u32 32
    %178 = const i64 4
    %179 = gep i8, ptr %0, %178
    store u32 %177, ptr %179
    %180 = const i32 1
    store i32 %180, ptr %0
    br bb14
bb10:
    %181 = const u32 16
    %182 = const i64 4
    %183 = gep i8, ptr %0, %182
    store u32 %181, ptr %183
    %184 = const i32 1
    store i32 %184, ptr %0
    br bb14
bb11:
    %185 = const u32 8
    %186 = const i64 4
    %187 = gep i8, ptr %0, %186
    store u32 %185, ptr %187
    %188 = const i32 1
    store i32 %188, ptr %0
    br bb14
bb12:
    %189 = const u32 1
    %190 = const i64 4
    %191 = gep i8, ptr %0, %190
    store u32 %189, ptr %191
    %192 = const i32 1
    store i32 %192, ptr %0
    br bb14
bb13:
    store ptr %3, ptr %5
    call @func.12(%0, %4, %5)
    br bb14
bb14:
    ret
bb15:
    %193 = load ptr, ptr %7
    %194 = ptrtoint ptr %193 to u64
    %195 = const u64 0
    %196 = icmp eq u64 %194, %195
    %197 = const bool true
    %198 = const bool false
    %199 = select bool %196, %197, %198
    %200 = const bool false
    %201 = icmp eq bool %199, %200
    condbr %201, bb16, bb17
bb16:
    %202 = load ptr, ptr %7
    call @func.10(%4, %202)
    br bb13
bb17:
    unreachable
}

fn @std__option__Option___T___and_then__mono3b23d5c2024a40ab(functy.11) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %3 = alloca i64, align 8
    %4 = alloca i32, align 4
    %5 = load i32, ptr %1
    %6 = sext i32 %5 to i64
    switch %6 [ 0: bb2 1: bb3 default: bb1 ]
bb1:
    unreachable
bb2:
    %7 = const i32 0
    store i32 %7, ptr %0
    br bb5
bb3:
    %8 = const i64 4
    %9 = gep i8, ptr %1, %8
    %10 = load u32, ptr %9
    %11 = load i64, ptr %2
    store i64 %11, ptr %3
    store u32 %10, ptr %4
    %12 = load u32, ptr %4
    call @func.14(%0, %3, %12)
    br bb4
bb4:
    br bb5
bb5:
    ret
}

fn @std__option__Option___T___and_then__monoe6192165786a0ec9(functy.12) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %3 = alloca i64, align 8
    %4 = alloca i32, align 4
    %5 = load i32, ptr %1
    %6 = sext i32 %5 to i64
    switch %6 [ 0: bb2 1: bb3 default: bb1 ]
bb1:
    unreachable
bb2:
    %7 = const i32 0
    store i32 %7, ptr %0
    br bb5
bb3:
    %8 = const i64 4
    %9 = gep i8, ptr %1, %8
    %10 = load u32, ptr %9
    %11 = load i64, ptr %2
    store i64 %11, ptr %3
    store u32 %10, ptr %4
    %12 = load u32, ptr %4
    call @func.16(%0, %3, %12)
    br bb4
bb4:
    br bb5
bb5:
    ret
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm11checked_mulCs8ad5MLNZt89_25trust_fold_cast_try_slice(functy.13) {
}

fn @Ty__bit_width_with___closure_0_(functy.14) {
bb0(%0: ptr, %1: ptr, %2: u32):
    %3 = load ptr, ptr %1
    %4 = load ptr, ptr %3
    %5 = load u32, ptr %4
    call @func.13(%0, %2, %5)
    br bb1
bb1:
    ret
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm11checked_mulCs8ad5MLNZt89_25trust_fold_cast_try_slice(functy.15) {
}

fn @Ty__bit_width___closure_0_(functy.16) {
bb0(%0: ptr, %1: ptr, %2: u32):
    %3 = load ptr, ptr %1
    %4 = load ptr, ptr %3
    %5 = load u32, ptr %4
    call @func.15(%0, %2, %5)
    br bb1
bb1:
    ret
}
"#;

// ── host shims for the try-variant's empty-bodied imports ───────────────────
//
// The frontend lowers `?` / `then_some` to 0-block fns (the known
// Option-Try shim gap — round-2 doc); the JIT resolves them from the externs
// map. Layouts read off the emitted module:
//   Option<i128>                       = { tag: i128 @0 (0=None,1=Some), value: i128 @16 }
//   ControlFlow<Option<Infallible>,i128> = { tag: i128 @0 (0=Continue,1=Break), payload: i128 @16 }
//   Option<u32>                        = { tag: i32 @0 (0=None,1=Some), value: u32 @4 }
//   ControlFlow<Option<Infallible>,u32>  = { tag: i32 @0 (0=Continue,1=Break), payload: u32 @4 }

#[repr(C, align(16))]
struct Pair128 {
    tag: i128,
    payload: i128,
}

#[repr(C)]
struct Pair32 {
    tag: i32,
    payload: u32,
}

unsafe extern "C" fn shim_try_branch_i128(out: *mut Pair128, opt: *const Pair128) {
    unsafe {
        if (*opt).tag == 1 {
            (*out).tag = 0; // Continue
            (*out).payload = (*opt).payload;
        } else {
            (*out).tag = 1; // Break(None residual)
            (*out).payload = 0;
        }
    }
}

unsafe extern "C" fn shim_from_residual_i128(out: *mut Pair128) {
    unsafe {
        (*out).tag = 0; // Option<i128>::None
        (*out).payload = 0;
    }
}

unsafe extern "C" fn shim_then_some_i128(out: *mut Pair128, b: bool, v: i128) {
    unsafe {
        if b {
            (*out).tag = 1;
            (*out).payload = v;
        } else {
            (*out).tag = 0;
            (*out).payload = 0;
        }
    }
}

unsafe extern "C" fn shim_try_branch_u32(out: *mut Pair32, opt: *const Pair32) {
    unsafe {
        if (*opt).tag == 1 {
            (*out).tag = 0; // Continue
            (*out).payload = (*opt).payload;
        } else {
            (*out).tag = 1; // Break(None residual)
            (*out).payload = 0;
        }
    }
}

/// `u32::checked_mul` — the ONE true leaf of `Ty::bit_width{,_with}` (lives in
/// the Vector arm, never reached by this file's dst menu, but the JIT resolves
/// all imports eagerly). Faithful host semantics.
/// Option<u32> out = { tag: i32 @0 (0=None,1=Some), value: u32 @4 }.
unsafe extern "C" fn shim_checked_mul_u32(out: *mut Pair32, a: u32, b: u32) {
    unsafe {
        match a.checked_mul(b) {
            Some(v) => {
                (*out).tag = 1;
                (*out).payload = v;
            }
            None => {
                (*out).tag = 0;
                (*out).payload = 0;
            }
        }
    }
}

// NOTE: the crate-hash suffix in these mangled names is derived from the
// slice's file path — regenerating a slice from a different directory changes
// the suffix (update the constants alongside the embedded IR).
const EXT_CHECKED_MUL_DESUGARED: &str =
    "_RNvMs6_NtCs2EYQwhfuABO_4core3numm11checked_mulCs34Q1zAXKtMq_21trust_fold_cast_slice";
const EXT_CHECKED_MUL_HALVES: &str =
    "_RNvMs6_NtCs2EYQwhfuABO_4core3numm11checked_mulCsg65pCKkzay5_28trust_fold_cast_halves_slice";
const EXT_CHECKED_MUL_TRY: &str =
    "_RNvMs6_NtCs2EYQwhfuABO_4core3numm11checked_mulCs8ad5MLNZt89_25trust_fold_cast_try_slice";

const EXT_TRY_BRANCH_I128: &str = "_RNvXsJ_NtCs2EYQwhfuABO_4core6optionINtB5_6OptionnENtNtNtB7_3ops9try_trait3Try6branchCs8ad5MLNZt89_25trust_fold_cast_try_slice";
const EXT_FROM_RESIDUAL_I128: &str = "_RNvXsK_NtCs2EYQwhfuABO_4core6optionINtB5_6OptionnEINtNtNtB7_3ops9try_trait12FromResidualIBy_NtNtB7_7convert10InfallibleEE13from_residualCs8ad5MLNZt89_25trust_fold_cast_try_slice";
const EXT_THEN_SOME_I128: &str =
    "_RINvMNtCs2EYQwhfuABO_4core4boolb9then_somenECs8ad5MLNZt89_25trust_fold_cast_try_slice";
const EXT_TRY_BRANCH_U32: &str = "_RNvXsJ_NtCs2EYQwhfuABO_4core6optionINtB5_6OptionmENtNtNtB7_3ops9try_trait3Try6branchCs8ad5MLNZt89_25trust_fold_cast_try_slice";

/// Extern bindings as Send-able (symbol, address) pairs — fn addresses cross
/// into the watchdog worker thread as `usize` (raw pointers are not `Send`).
fn try_variant_externs() -> Vec<(&'static str, usize)> {
    vec![
        (
            EXT_TRY_BRANCH_I128,
            shim_try_branch_i128 as *const () as usize,
        ),
        (
            EXT_FROM_RESIDUAL_I128,
            shim_from_residual_i128 as *const () as usize,
        ),
        (
            EXT_THEN_SOME_I128,
            shim_then_some_i128 as *const () as usize,
        ),
        (
            EXT_TRY_BRANCH_U32,
            shim_try_branch_u32 as *const () as usize,
        ),
        (
            EXT_CHECKED_MUL_TRY,
            shim_checked_mul_u32 as *const () as usize,
        ),
    ]
}

fn externs_map(pairs: &[(&'static str, usize)]) -> HashMap<String, *const u8> {
    pairs
        .iter()
        .map(|&(name, addr)| (name.to_string(), addr as *const u8))
        .collect()
}

// ── sweep helpers ────────────────────────────────────────────────────────────

/// Run the FULL (op × dst × val) sweep against one POD-ABI entry inside the
/// watchdog thread, streaming each row back so a hang identifies its input.
fn sweep_pod_entry(
    ir: &'static str,
    what: &'static str,
    root: &'static str,
    externs: Vec<(&'static str, usize)>,
) -> Vec<SweepRow> {
    let (tx, rx) = mpsc::channel::<SweepRow>();
    // The buffer is created and used ENTIRELY inside the worker thread; on a
    // hang it is leaked with the thread (hang safety — see file header).
    std::thread::spawn(move || {
        let buffer = jit_module_with(ir, what, &externs_map(&externs));
        // SAFETY: machine code for functy.0 = (u32, u32, ptr, ptr) -> ().
        let f: FoldCastEntryFn = unsafe { std::mem::transmute(bind(&buffer, root)) };
        for op_tag in 0..=14u32 {
            for dst_tag in 0..=13u32 {
                for &val in &value_menu() {
                    let vin = OptI128POD {
                        present: u64::from(val.is_some()),
                        value: val.unwrap_or(0),
                    };
                    let mut vout = OptI128POD {
                        present: 0xDEAD,
                        value: -1,
                    };
                    unsafe { f(op_tag, dst_tag, &vin, &mut vout) };
                    if tx
                        .send((op_tag, dst_tag, val, vout.present, vout.value))
                        .is_err()
                    {
                        return;
                    }
                }
            }
        }
    });

    let expected = 15 * 14 * value_menu().len();
    let mut rows = Vec::with_capacity(expected);
    let mut last: Option<(u32, u32, Option<i128>)> = None;
    for _ in 0..expected {
        match rx.recv_timeout(Duration::from_secs(WATCHDOG_SECS)) {
            Ok(row) => {
                last = Some((row.0, row.1, row.2));
                rows.push(row);
            }
            Err(_) => panic!(
                "JIT `{what}` HUNG (watchdog {WATCHDOG_SECS}s): no progress after {last:?} \
                 ({} of {expected} rows) — the 2026-06-29 hang class is BACK; re-pin it",
                rows.len()
            ),
        }
    }
    rows
}

/// Assert every sweep row agrees with the native oracle.
fn assert_rows_match_native(rows: &[SweepRow], what: &str) {
    for &(op_tag, dst_tag, val, jit_present, jit_value) in rows {
        let native = fold_cast_native(
            cast_op_for_tag_native(op_tag),
            &NTy::I64,
            &dst_ty_for_tag_native(dst_tag),
            val,
        );
        let jit = (jit_present != 0).then_some(jit_value);
        assert_eq!(
            native,
            jit,
            "{what}: JIT disagrees with native at op_tag={op_tag} \
             ({:?}), dst_tag={dst_tag} ({:?}), val={val:?}: native={native:?} jit={jit:?}",
            cast_op_for_tag_native(op_tag),
            dst_ty_for_tag_native(dst_tag),
        );
    }
}

// ── SYMPTOM (3): the desugared, extern-free module ──────────────────────────

/// Full-domain differential on the desugared module: every CastOp × every
/// dst_ty × the value menu, native == JIT (covers the 2026-06-29 ZExt
/// miscompile witness `ZExt(Some(7))` and the hanging Trunc arm).
#[test]
fn fold_cast_desugared_full_sweep_native_eq_jit() {
    let rows = sweep_pod_entry(
        FOLD_CAST_DESUGARED_IR,
        "fold_cast (desugared)",
        "fold_cast_entry",
        vec![(
            EXT_CHECKED_MUL_DESUGARED,
            shim_checked_mul_u32 as *const () as usize,
        )],
    );
    assert_eq!(rows.len(), 15 * 14 * value_menu().len());
    assert_rows_match_native(&rows, "fold_cast desugared");

    // Ground-truth spot checks (independent of both implementations):
    let find = |op: u32, dst: u32, val: Option<i128>| {
        rows.iter()
            .find(|r| r.0 == op && r.1 == dst && r.2 == val)
            .map(|r| (r.3 != 0).then_some(r.4))
            .unwrap()
    };
    assert_eq!(
        find(1, 0, Some(7)),
        Some(7),
        "ZExt(Some(7)) — the 2026-06-29 witness"
    );
    assert_eq!(find(1, 0, Some(-7)), None, "ZExt of negative must not fold");
    assert_eq!(find(0, 0, Some(0x1FF)), Some(0xFF), "Trunc-to-i8 masks");
    assert_eq!(
        find(0, 4, Some(-1)),
        None,
        "Trunc-to-i128 hits the bits>127 guard"
    );
    assert_eq!(
        find(0, 11, Some(1i128 << 64)),
        Some(0),
        "Trunc-to-Ptr masks to 64 bits"
    );
    assert_eq!(
        find(0, 12, Some(7)),
        None,
        "Trunc-to-Unit: bit_width None short-circuits"
    );
    assert_eq!(
        find(2, 4, Some(i128::MIN)),
        Some(i128::MIN),
        "SExt passes through"
    );
    assert_eq!(find(3, 0, Some(1)), None, "FPTrunc is not folded");

    // NEGATIVE CONTROL: a corrupted oracle (ZExt drops non-negative values —
    // the exact 2026-06-29 miscompile behavior) must DISAGREE with the JIT,
    // proving the differential discriminates.
    fn fold_cast_corrupt(op: NCastOp, dst: &NTy, val: Option<i128>) -> Option<i128> {
        match op {
            NCastOp::ZExt => None, // bug: ZExt(Some(7)) -> None
            _ => fold_cast_native(op, &NTy::I64, dst, val),
        }
    }
    let jit_zext7 = find(1, 0, Some(7));
    assert_ne!(
        fold_cast_corrupt(NCastOp::ZExt, &dst_ty_for_tag_native(0), Some(7)),
        jit_zext7,
        "negative control must FAIL: the ZExt-dropping oracle should disagree with the JIT"
    );
}

// ── SYMPTOM (1): the halves-ABI module — STILL BROKEN, PINNED ───────────────

/// PINNED trust-cg ISel LIMIT (symptom 1, REPRODUCED at trust-cg 9d3dfa6):
/// the entry that rebuilds an i128 from two u64 halves
/// (`zext`/`shl u128 ..., 64`/`or`/`bitcast u128->i128`) and extracts the
/// result with `lshr u128 ..., 64` still CANNOT be lowered —
/// `Pipeline(ISel("value Value(45) not defined before use"))`, the same
/// i128 high-half register-pair binding class as 2026-06-29 (then
/// `Value(36)`) and as the pinned `edge_bounds` limit.
///
/// Scope note (what makes this pin PRECISE): the desugared module above
/// contains plain i128 loads/stores, `shl i128` by a dynamic amount,
/// `sub.overflow i128`, and `icmp sge i128` — and compiles AND runs
/// correctly. The gap is specifically the u128/i128 HALF-SPLITTING
/// arithmetic shape, not i128 support generally.
///
/// This test FAILS the day trust-cg learns to lower it: on successful
/// compile it runs the full differential sweep (hang-guarded) and reports
/// the native==JIT outcome, then panics demanding promotion.
#[test]
fn fold_cast_halves_full_sweep_native_eq_jit() {
    let module = trust_ir::parser::parse_module(FOLD_CAST_HALVES_IR)
        .expect("MIR-emitted `fold_cast_entry_halves` trust-ir must parse (frontend is fine)");
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    let halves_externs = vec![(
        EXT_CHECKED_MUL_HALVES,
        shim_checked_mul_u32 as *const () as usize,
    )];
    let result =
        Compiler::new(config).compile_module_to_jit(&module, &externs_map(&halves_externs));
    match result {
        Err(e) => panic!(
            "REGRESSION: trust-cg can no longer lower the fold_cast i128-from-halves entry \
             (was verified native==JIT): {e:?}"
        ),
        Ok(_) => {
            // trust-cg compiles the halves ABI. Run the full differential
            // (hang-guarded), comparing the JIT output against the native
            // oracle over the entire modeled input domain.
            let (tx, rx) = mpsc::channel::<SweepRow>();
            std::thread::spawn(move || {
                let buffer = jit_module_with(
                    FOLD_CAST_HALVES_IR,
                    "fold_cast (halves ABI)",
                    &externs_map(&halves_externs),
                );
                // SAFETY: machine code for functy.0 = (u32,u32,u64,u64,u64,ptr,ptr,ptr) -> ().
                let f: FoldCastHalvesFn =
                    unsafe { std::mem::transmute(bind(&buffer, "fold_cast_entry_halves")) };
                for op_tag in 0..=14u32 {
                    for dst_tag in 0..=13u32 {
                        for &val in &value_menu() {
                            let (present, lo, hi) = match val {
                                Some(v) => (1u64, v as u64, ((v as u128) >> 64) as u64),
                                None => (0u64, 0, 0),
                            };
                            let (mut op, mut olo, mut ohi) = (0xDEADu64, 0u64, 0u64);
                            unsafe {
                                f(
                                    op_tag, dst_tag, present, lo, hi, &mut op, &mut olo, &mut ohi,
                                )
                            };
                            let value = (((ohi as u128) << 64) | olo as u128) as i128;
                            if tx.send((op_tag, dst_tag, val, op, value)).is_err() {
                                return;
                            }
                        }
                    }
                }
            });
            let expected = 15 * 14 * value_menu().len();
            let mut rows = Vec::with_capacity(expected);
            let mut hung_after: Option<(u32, u32, Option<i128>)> = None;
            for _ in 0..expected {
                match rx.recv_timeout(Duration::from_secs(WATCHDOG_SECS)) {
                    Ok(row) => {
                        hung_after = Some((row.0, row.1, row.2));
                        rows.push(row);
                    }
                    Err(_) => break,
                }
            }
            if rows.len() < expected {
                panic!(
                    "PINNED FINDING CHANGED SHAPE: trust-cg now COMPILES the i128-from-halves                      entry but the JIT HUNG after {hung_after:?} ({} of {expected} rows) —                      re-pin with the new failure mode",
                    rows.len()
                );
            }
            assert_rows_match_native(&rows, "fold_cast halves-ABI (full sweep)");
        }
    }
}

// ── SYMPTOM (2): the verbatim-`?` module through the Try shims ──────────────

/// The byte-for-byte production body (`val?` / `then_some` /
/// `bit_width_with(64)?`) lowered through the empty-bodied
/// `Try::branch`/`FromResidual`/`then_some` imports, bound to host shims —
/// the exact surface whose sret consumption looped forever on 2026-06-29.
/// Full sweep, hang-guarded.
#[test]
fn fold_cast_verbatim_try_full_sweep_native_eq_jit() {
    let rows = sweep_pod_entry(
        FOLD_CAST_TRY_IR,
        "fold_cast (verbatim-? Try shims)",
        "fold_cast_entry_try",
        try_variant_externs(),
    );
    assert_eq!(rows.len(), 15 * 14 * value_menu().len());
    assert_rows_match_native(&rows, "fold_cast verbatim-?");

    // The exact 2026-06-29 hang trigger: ANY input reaching `val?` with
    // Some(_) called the branch shim once and then looped. Re-assert the two
    // canonical witnesses.
    let find = |op: u32, dst: u32, val: Option<i128>| {
        rows.iter()
            .find(|r| r.0 == op && r.1 == dst && r.2 == val)
            .map(|r| (r.3 != 0).then_some(r.4))
            .unwrap()
    };
    assert_eq!(
        find(0, 0, Some(0x1FF)),
        Some(0xFF),
        "Trunc through BOTH `?`s"
    );
    assert_eq!(
        find(1, 0, Some(7)),
        Some(7),
        "ZExt through the then_some shim"
    );
    assert_eq!(
        find(12, 13, None),
        None,
        "None short-circuits via FromResidual"
    );

    // NEGATIVE CONTROL: a shim-level corruption oracle — a `then_some` that
    // inverts its condition — must disagree with the JIT.
    fn then_some_inverted(b: bool, v: i128) -> Option<i128> {
        (!b).then_some(v)
    }
    assert_ne!(
        then_some_inverted(7 >= 0, 7),
        find(1, 0, Some(7)),
        "negative control must FAIL: the inverted then_some oracle should disagree with the JIT"
    );
}
