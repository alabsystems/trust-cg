//! T3 — MUTUAL RECURSOR PATH: native == JIT differential over the clean-kernel
//! mutual-inductive recursor construction (Rust -> MIR -> trust-ir -> trust-cg ->
//! machine code), on real mutual families (Even/Odd; Tree/Forest with a parameter).
//!
//! WHAT IS VERIFIED (per output, deep-structural AND ExprMeta-word bit-identical at
//! every node):
//!   * `build_recursor_type` on the MUTUAL arm (num_motives = 2): motives for ALL
//!     block types, minor premises for ALL constructors across the block (built by
//!     the verified `build_minor_premise_type`, now with conclusion_motive_idx > 0
//!     and cross-type IH motives via `field_motive_index`), the mutual de-Bruijn
//!     lift arithmetic, and `infer_implicit`.
//!   * `build_recursor_rule_rhs` taking the `all_types.len() > 1` MUTUAL branch:
//!     the IH names the recursor OF THE TYPE THE FIELD RETURNS TO (Forest.rec
//!     inside Tree.rec's rule; Even.rec inside Odd.rec's — Lean 4 inductive.cpp:738),
//!     with the GLOBAL minor index (minor_idx_offset + local idx).
//!   * The in-module CtorInfo derivation from REAL constructor Pi-telescopes:
//!     `compute_ctor_infos` / `get_recursive_field_flags` /
//!     `field_is_eliminably_recursive` / `get_constructor_field_types` /
//!     `get_constructor_return_indices` (mutual: a field is recursive iff its
//!     return head is ANY block type).
//!   * The `build_recursor` assembly (inductive_recursor.rs:66) + the
//!     `minor_idx_offset` computation (inductive_builder.rs:322), transcribed
//!     verbatim into `build_mutual_recursor_part`.
//!
//! GROUND-TRUTH ANCHORS (not just native==JIT self-consistency): the expected
//! Even.rec TYPE and the expected Odd.rec succ_even rule RHS are HAND-BUILT in this
//! file from Lean's documented mutual-recursor shape (the Even/Odd example in
//! clean's inductive_recursor_types.rs doc comment) and asserted deep-equal to the
//! JIT outputs.
//!
//! THE MODELED BOUNDARY (the T3 boundary, documented): the mutual path's
//! `Name::from_string(&format!("{name}.rec"))` (string formatting + interning) is
//! modeled as a caller-provided PRE-INTERNED table `&[RecPair{ind, rec}]` looked up
//! by slice scan (`rec_name_of`), the established env-boundary pattern. The
//! frontend gaps forcing this are probe-pinned (see the T3 report /
//! dev-scratch/t3-mutual/probe_string_*.rs):
//!   * `String::from("lit")`      -> "call arg constant of non-scalar type ref"
//!   * `String` -> `&[u8]` deref  -> "fat-pointer dst from unmodelable rvalue"
//!   * `str::bytes()` iterator    -> "next inline: iterator has no element type arg"
//!   * `format!("{x}.rec")`       -> "constant value not a single scalar"
//!     (the format_args! pieces constant)
//!     The table lookup's miss-fallback is provably dead on the verified path: a field
//!     is only flagged recursive when its return head is a block inductive, and the
//!     table covers exactly the block. A NEGATIVE CONTROL feeds a deliberately swapped
//!     table through the JIT and asserts the wrong recursor name comes out (and equals
//!     the native mirror under the same bogus table) — the table genuinely flows
//!     through the machine code.
//!
//! Other boundaries (see the slice header): HashSet -> slice scan (exact membership
//! semantics), SmallVec -> Vec, prop-only/fresh-univ-name modeled as inputs
//! (elim_only_universe_zero is separately verified), RecursorVal metadata (is_k
//! etc.) not built, ctor_path_data -> None (non-HIT families), Name/Level modeled
//! leaves as in every prior kernel slice.
//!
//! Fixture: MIR-emitted closure of `build_mutual_rec_root` from
//! dev-scratch/t3-mutual/clean_mutual_recursor_slice.rs —
//! EMIT-CLOSURE-OK: 431151 bytes; 86 closure members; validate_module = 0 errors;
//! re-parse OK. Regenerate:
//!   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//!   cd $HOME/trust-ir/frontend && env -u RUSTUP_TOOLCHAIN RUSTC=$S/bin/rustc \
//!     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//!     $S/bin/cargo run --bin trust_ir_mir -- <dev-scratch>/t3-mutual/clean_mutual_recursor_slice.rs \
//!     --crate-type=lib --mir-emit-closure build_mutual_rec_root <out.tir>
//!
//! Run this file's test ALONE (JIT accumulation — see jit-parallel-race-2026-06-29.md):
//!   cargo test -p trust-cg-codegen --test e2e_mutual_recursor -- --test-threads=1

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

/// VERBATIM MIR-emitted trust-ir closure of `build_mutual_rec_root` (see module docs).
const MX_MUTUAL_REC_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::build_mutual_rec_root"

functy.0 = (ptr, ptr, u64) -> ()

functy.1 = (ptr, ptr, u64) -> ()

functy.2 = (ptr, ptr) -> ()

functy.3 = (ptr, ptr, u64) -> ()

functy.4 = (ptr, ptr) -> ()

functy.5 = (ptr) -> ()

functy.6 = (ptr, u32) -> ()

functy.7 = (ptr, ptr) -> ()

functy.8 = (ptr) -> ()

functy.9 = (ptr) -> (u64)

functy.10 = (ptr, u64) -> (ptr)

functy.11 = (ptr, ptr) -> ()

functy.12 = (ptr, ptr) -> (bool)

functy.13 = (ptr) -> (u64)

functy.14 = (u32, u32) -> (u32)

functy.15 = (ptr, ptr) -> ()

functy.16 = (ptr, ptr) -> ()

functy.17 = (ptr, ptr) -> ()

functy.18 = (ptr, ptr, u32, ptr, ptr, ptr, ptr, u64, u64) -> ()

functy.19 = (ptr, ptr) -> (bool)

functy.20 = (ptr, ptr) -> (bool)

functy.21 = (ptr, ptr, ptr, ptr) -> ()

functy.22 = (ptr) -> (u64)

functy.23 = (ptr, u64) -> ()

functy.24 = (ptr, u64) -> (ptr)

functy.25 = (u32, u32) -> (u32)

functy.26 = (ptr, ptr) -> ()

functy.27 = (ptr, ptr, ptr, u32) -> ()

functy.28 = (ptr, ptr) -> ()

functy.29 = (ptr, ptr) -> ()

functy.30 = (ptr, ptr) -> ()

functy.31 = (u32, u32) -> (u32)

functy.32 = (ptr) -> (u32)

functy.33 = (ptr, u64) -> ()

functy.34 = (u32, u32) -> (u32)

functy.35 = (ptr) -> (u64)

functy.36 = (ptr, u64) -> (ptr)

functy.37 = (ptr, ptr) -> ()

functy.38 = (ptr, ptr) -> (bool)

functy.39 = (ptr) -> ()

functy.40 = (ptr, ptr) -> ()

functy.41 = (ptr, ptr) -> ()

functy.42 = (ptr, ptr) -> ()

functy.43 = (ptr) -> (u64)

functy.44 = (ptr, u64) -> (ptr)

functy.45 = (ptr) -> (u64)

functy.46 = (ptr, u64) -> (ptr)

functy.47 = (ptr, ptr, ptr, u32, u32, ptr, ptr, ptr, ptr) -> ()

functy.48 = (ptr) -> ()

functy.49 = (ptr, ptr) -> ()

functy.50 = (ptr, ptr, u64) -> ()

functy.51 = (ptr, ptr) -> ()

functy.52 = (ptr) -> (u64)

functy.53 = (ptr, u64) -> (ptr)

functy.54 = (ptr) -> ()

functy.55 = (ptr) -> (u64)

functy.56 = (ptr, u64) -> (ptr)

functy.57 = (ptr) -> ()

functy.58 = (ptr, ptr) -> ()

functy.59 = (ptr, ptr, ptr, u32, u32, u32, u32, ptr, ptr, u64, u64, ptr, ptr, ptr) -> ()

functy.60 = (ptr) -> ()

functy.61 = (ptr, bool) -> ()

functy.62 = (ptr, ptr, ptr, u32) -> ()

functy.63 = (ptr) -> ()

functy.64 = (ptr, ptr) -> ()

functy.65 = (ptr, ptr, u32) -> ()

functy.66 = (ptr) -> ()

functy.67 = (ptr, ptr) -> ()

functy.68 = (ptr) -> (u64)

functy.69 = (ptr, u64) -> (ptr)

functy.70 = (ptr, ptr, u32) -> ()

functy.71 = (ptr, ptr) -> ()

functy.72 = (ptr) -> ()

functy.73 = (ptr, ptr) -> ()

functy.74 = (ptr, ptr, ptr) -> ()

functy.75 = (ptr) -> ()

functy.76 = (ptr, ptr) -> ()

functy.77 = (ptr, ptr, u32) -> ()

functy.78 = (ptr, ptr) -> ()

functy.79 = (ptr, ptr, u32, u32) -> ()

functy.80 = (ptr, ptr) -> ()

functy.81 = (ptr, ptr) -> ()

functy.82 = (ptr, ptr) -> ()

functy.83 = (ptr, u32) -> ()

functy.84 = (ptr, ptr, ptr) -> ()

functy.85 = (ptr) -> ()

functy.86 = (ptr, ptr, ptr, ptr) -> ()

functy.87 = (ptr) -> (u64)

functy.88 = (ptr, u64) -> (ptr)

functy.89 = (ptr, ptr) -> (bool)

functy.90 = (ptr, ptr) -> (u64)

functy.91 = (ptr, ptr, ptr) -> ()

functy.92 = (ptr) -> ()

functy.93 = (ptr, ptr) -> ()

functy.94 = (ptr, ptr, u64) -> ()

functy.95 = (ptr) -> (u64)

functy.96 = (ptr, u64) -> (ptr)

functy.97 = (ptr) -> ()

functy.98 = (ptr) -> (u64)

functy.99 = (ptr, u64) -> (ptr)

functy.100 = (ptr, ptr, ptr, u32, ptr, ptr, u32, ptr, ptr, u64, u64, ptr) -> ()

functy.101 = (ptr, u64) -> ()

functy.102 = (ptr, u32) -> (u32)

functy.103 = (u64) -> (u32)

functy.104 = (ptr, ptr, u32, u32) -> ()

functy.105 = (ptr, ptr, u32, u32) -> ()

functy.106 = (ptr, ptr, u32) -> ()

functy.107 = (ptr) -> ()

functy.108 = (ptr, ptr, bool) -> ()

functy.109 = (ptr) -> (u64)

functy.110 = (ptr) -> (ptr)

functy.111 = (ptr) -> (ptr)

functy.112 = (ptr, u32, ptr) -> ()

functy.113 = (ptr, ptr, u64, u64, u64, u64, u64, u64) -> ()

functy.114 = (ptr) -> ()

functy.115 = (ptr, ptr) -> ()

functy.116 = (ptr, ptr) -> ()

functy.117 = (ptr, ptr, ptr, ptr) -> ()

functy.118 = (ptr, ptr) -> ()

functy.119 = (ptr, ptr) -> (bool)

functy.120 = (ptr) -> (ptr)

functy.121 = (ptr, ptr) -> ()

functy.122 = (ptr, ptr) -> ()

functy.123 = (ptr, ptr) -> ()

functy.124 = (ptr, ptr) -> ()

functy.125 = (u32, u32) -> (u32)

functy.126 = (ptr) -> (u64)

functy.127 = (ptr, u64) -> (ptr)

functy.128 = (u32, u32) -> (u32)

functy.129 = (ptr, ptr) -> ()

functy.130 = (ptr, ptr, ptr, u64) -> ()

functy.131 = (ptr, ptr) -> (bool)

functy.132 = (ptr, ptr) -> (u64)

functy.133 = (ptr, ptr, u64, u64, u64, u64) -> ()

functy.134 = (ptr, ptr, u32, u32) -> ()

functy.135 = (ptr, ptr, u32, bool) -> ()

functy.136 = (ptr, ptr) -> (bool)

functy.137 = (ptr, ptr) -> (bool)

functy.138 = (ptr, ptr) -> ()

functy.139 = (ptr, ptr) -> ()

functy.140 = (ptr, ptr) -> ()

functy.141 = (ptr) -> (u64)

functy.142 = (u64, u64) -> (u64)

functy.143 = (u64, u64) -> (u64)

functy.144 = (ptr) -> (u64)

functy.145 = (ptr) -> (u64)

functy.146 = (u32, u32) -> (u32)

functy.147 = (ptr, u32, u32, u32, bool, bool, bool, bool) -> ()

functy.148 = (ptr, ptr) -> ()

functy.149 = (u8, u8) -> (u8)

functy.150 = (u32, u32) -> (u32)

functy.151 = (u32, u32) -> (u32)

functy.152 = (ptr, u64, u64) -> ()

functy.153 = (u8, u8) -> (u8)

functy.154 = (u32, u32) -> (u32)

functy.155 = (u32, u32) -> (u32)

functy.156 = (u32, u32) -> (u32)

functy.157 = (ptr, u64, u64, u64) -> ()

functy.158 = (ptr) -> (bool)

functy.159 = (ptr) -> (bool)

functy.160 = (u8, u8) -> (u8)

functy.161 = (u32, u32) -> (u32)

functy.162 = (u32, u32) -> (u32)

functy.163 = (u32, u32) -> (u32)

functy.164 = (ptr, u64, u64, u64) -> ()

functy.165 = (u64) -> (u8)

functy.166 = (u64) -> (u32)

functy.167 = (u64) -> (u32)

functy.168 = (u64) -> (bool)

functy.169 = (u64) -> (bool)

functy.170 = (u64) -> (bool)

functy.171 = (u64) -> (bool)

functy.172 = (ptr) -> (u32)

functy.173 = (u32, u32) -> (u32)

functy.174 = (u32, u32) -> (u32)

functy.175 = (ptr, u32, bool) -> (bool)

functy.176 = (ptr, u8, u8) -> ()

functy.177 = (ptr) -> ()

functy.178 = (ptr, ptr) -> ()

functy.179 = (ptr, ptr) -> ()

functy.180 = (ptr, ptr) -> ()

functy.181 = (ptr, ptr) -> ()

functy.182 = (ptr) -> (u64)

functy.183 = (ptr, ptr) -> ()

functy.184 = (ptr, ptr) -> ()

functy.185 = (ptr, ptr) -> ()

functy.186 = (ptr, ptr) -> ()

functy.187 = (ptr, ptr) -> ()

functy.188 = (ptr, u32) -> (bool)

functy.189 = (ptr, u32, u32) -> (bool)

functy.190 = (ptr, u32, u32) -> (bool)

functy.191 = (ptr, u32, u32) -> ()

functy.192 = (u32, u32, u32) -> (bool)

fn @_RINvNtNtCs2EYQwhfuABO_4core5slice3raw14from_raw_partsNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4NameEBR_(functy.0) {
}

fn @_RINvNtNtCs2EYQwhfuABO_4core5slice3raw14from_raw_partsNtCs6RT0DENTjyC_27clean_mutual_recursor_slice7RecPairEBR_(functy.1) {
}

fn @_RINvNtCs2EYQwhfuABO_4core3ptr5writeNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprEBz_(functy.2) {
}

fn @_RINvNtNtCs2EYQwhfuABO_4core5slice3raw14from_raw_partsNtCs6RT0DENTjyC_27clean_mutual_recursor_slice13InductiveTypeEBR_(functy.3) {
}

fn @build_mutual_rec_root(functy.4) {
bb0(%0: ptr, %1: ptr):
    %19 = alloca i64, align 8
    %20 = alloca (i64, i64), align 8
    %21 = alloca (i64, i64), align 8
    %22 = alloca (i64, i64), align 8
    %23 = alloca (i64, i64), align 8
    %24 = alloca i32, align 4
    %25 = alloca i64, align 8
    %26 = alloca (i64, i64, i64, i64, i64), align 8
    %27 = alloca i64, align 8
    store ptr %1, ptr %19
    %28 = load ptr, ptr %19
    %29 = ptrtoint ptr %28 to u64
    %30 = const u64 8
    %31 = const u64 1
    %32 = sub u64 %30, %31
    %33 = and u64 %29, %32
    %34 = const u64 0
    %35 = icmp eq u64 %33, %34
    condbr %35, bb10(%0), bb12
bb1(%2: ptr, %3: ptr):
    %36 = const i64 32
    %37 = gep i8, ptr %3, %36
    %38 = load ptr, ptr %37
    %39 = const i64 40
    %40 = gep i8, ptr %3, %39
    %41 = load u64, ptr %40
    call @func.0(%21, %38, %41)
    br bb2(%2, %3)
bb2(%4: ptr, %5: ptr):
    %42 = const i64 48
    %43 = gep i8, ptr %5, %42
    %44 = load ptr, ptr %43
    %45 = const i64 56
    %46 = gep i8, ptr %5, %45
    %47 = load u64, ptr %46
    call @func.0(%22, %44, %47)
    br bb3(%4, %5)
bb3(%6: ptr, %7: ptr):
    %48 = const i64 64
    %49 = gep i8, ptr %7, %48
    %50 = load ptr, ptr %49
    %51 = const i64 72
    %52 = gep i8, ptr %7, %51
    %53 = load u64, ptr %52
    call @func.1(%23, %50, %53)
    br bb4(%6, %7)
bb4(%8: ptr, %9: ptr):
    %54 = const u32 7
    store u32 %54, ptr %24
    %55 = const i64 4
    %56 = gep i8, ptr %9, %55
    %57 = load u32, ptr %56
    %58 = const u32 0
    %59 = icmp ne u32 %57, %58
    condbr %59, bb5(%8, %9), bb6(%8, %9)
bb5(%10: ptr, %11: ptr):
    store ptr %24, ptr %25
    br bb7(%10, %11)
bb6(%12: ptr, %13: ptr):
    %60 = const i64 0
    store i64 %60, ptr %25
    br bb7(%12, %13)
bb7(%14: ptr, %15: ptr):
    %61 = load u32, ptr %15
    %62 = load i64, ptr %25
    store i64 %62, ptr %27
    %63 = const i64 8
    %64 = gep i8, ptr %15, %63
    %65 = load u32, ptr %64
    %66 = zext u32 %65 to u64
    %67 = const i64 12
    %68 = gep i8, ptr %15, %67
    %69 = load u32, ptr %68
    %70 = zext u32 %69 to u64
    call @func.18(%26, %20, %61, %27, %21, %22, %23, %66, %70)
    br bb8(%14)
bb8(%16: ptr):
    call @func.2(%16, %26)
    br bb9
bb9:
    ret
bb10(%17: ptr):
    %71 = load ptr, ptr %19
    %72 = ptrtoint ptr %71 to u64
    %73 = const u64 0
    %74 = icmp eq u64 %72, %73
    %75 = const bool true
    %76 = const bool false
    %77 = select bool %74, %75, %76
    %78 = const bool false
    %79 = icmp eq bool %77, %78
    condbr %79, bb11(%17), bb12
bb11(%18: ptr):
    %80 = load ptr, ptr %19
    %81 = const i64 16
    %82 = gep i8, ptr %80, %81
    %83 = load ptr, ptr %82
    %84 = const i64 24
    %85 = gep i8, ptr %80, %84
    %86 = load u64, ptr %85
    call @func.3(%20, %83, %86)
    br bb1(%18, %80)
bb12:
    unreachable
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4NameE3newBE_(functy.5) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4NameE4pushBH_(functy.6) {
}

fn @_RNvXs7_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4NameENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefBH_(functy.7) {
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice8CtorInfoE3newBE_(functy.8) {
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice8CtorInfoE3lenBG_(functy.9) {
}

fn @_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice8CtorInfoEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_(functy.10) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice8CtorInfoE4pushBH_(functy.11) {
}

fn @_RNvYNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4NameNtNtCs2EYQwhfuABO_4core3cmp9PartialEq2neB4_(functy.12) {
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4CtorE3lenBG_(functy.13) {
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm14saturating_sub(functy.14) {
}

fn @_RNvXs7_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice8CtorInfoENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefBH_(functy.15) {
}

fn @_RNvXs7_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecbENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefCs6RT0DENTjyC_27clean_mutual_recursor_slice(functy.16) {
}

fn @_RNvXs7_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefBH_(functy.17) {
}

fn @build_mutual_recursor_part(functy.18) {
bb0(%0: ptr, %1: ptr, %2: u32, %3: ptr, %4: ptr, %5: ptr, %6: ptr, %7: u64, %8: u64):
    %264 = alloca (i64, i64, i64), align 8
    %265 = alloca i32, align 4
    %266 = alloca (i64, i64), align 8
    %267 = alloca i32, align 4
    %268 = alloca (i64, i64), align 8
    %269 = alloca i64, align 8
    %270 = alloca i32, align 4
    %271 = alloca (i64, i64, i64), align 8
    %272 = alloca (i64, i64), align 8
    %273 = alloca (i64, i64, i64), align 8
    %274 = alloca (i64, i64, i64), align 8
    %275 = alloca (i64, i64), align 8
    %276 = alloca (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64), align 8
    %277 = alloca (i64, i64), align 8
    %278 = alloca (i64, i64), align 8
    %279 = alloca (i64, i64), align 8
    %280 = alloca (i64, i64), align 8
    %281 = alloca (i64, i64, i64, i64, i64), align 8
    %282 = alloca (i64, i64), align 8
    %283 = alloca (i64, i64), align 8
    %284 = alloca i64, align 8
    %285 = alloca (i64, i64), align 8
    %286 = alloca (i64, i64), align 8
    %287 = alloca (i64, i64), align 8
    call @func.5(%264)
    br bb1(%2, %7, %8)
bb1(%9: u32, %10: u64, %11: u64):
    %288 = const u64 0
    br bb2(%9, %10, %11, %288)
bb2(%12: u32, %13: u64, %14: u64, %15: u64):
    %289 = const i64 8
    %290 = gep i8, ptr %1, %289
    %291 = load u64, ptr %290
    %292 = icmp ult u64 %15, %291
    condbr %292, bb3(%12, %13, %14, %15), bb7(%12, %13, %14)
bb3(%16: u32, %17: u64, %18: u64, %19: u64):
    %293 = const i64 8
    %294 = gep i8, ptr %1, %293
    %295 = load u64, ptr %294
    %296 = icmp ult u64 %19, %295
    condbr %296, bb4(%16, %17, %18, %19, %264, %19), bb69
bb4(%20: u32, %21: u64, %22: u64, %23: u64, %24: ptr, %25: u64):
    %297 = load ptr, ptr %1
    %298 = const u64 72
    %299 = mul u64 %25, %298
    %300 = gep i8, ptr %297, %299
    %301 = const i64 64
    %302 = gep i8, ptr %300, %301
    %303 = load i32, ptr %302
    store i32 %303, ptr %265
    %304 = load u32, ptr %265
    call @func.6(%24, %304)
    br bb5(%20, %21, %22, %23)
bb5(%26: u32, %27: u64, %28: u64, %29: u64):
    %305 = const u64 1
    %306, %307 = add.overflow u64 %29, %305
    store u64 %306, ptr %266
    %308 = const i64 8
    %309 = gep i8, ptr %266, %308
    store bool %307, ptr %309
    %310 = const i64 8
    %311 = gep i8, ptr %266, %310
    %312 = load bool, ptr %311
    %313 = const bool false
    %314 = icmp eq bool %312, %313
    condbr %314, bb6(%26, %27, %28), bb69
bb6(%30: u32, %31: u64, %32: u64):
    %315 = load u64, ptr %266
    br bb2(%30, %31, %32, %315)
bb7(%33: u32, %34: u64, %35: u64):
    %316 = const i64 8
    %317 = gep i8, ptr %1, %316
    %318 = load u64, ptr %317
    %319 = icmp ult u64 %34, %318
    condbr %319, bb8(%33, %34, %35), bb69
bb8(%36: u32, %37: u64, %38: u64):
    %320 = load ptr, ptr %1
    %321 = const u64 72
    %322 = mul u64 %37, %321
    %323 = gep i8, ptr %320, %322
    %324 = const i64 64
    %325 = gep i8, ptr %323, %324
    %326 = load i32, ptr %325
    store i32 %326, ptr %267
    %327 = const u64 0
    %328 = const u64 0
    br bb9(%36, %38, %327, %328)
bb9(%39: u32, %40: u64, %41: u64, %42: u64):
    %329 = const i64 8
    %330 = gep i8, ptr %1, %329
    %331 = load u64, ptr %330
    %332 = icmp ult u64 %42, %331
    condbr %332, bb10(%39, %40, %41, %42), bb16(%39, %40, %41)
bb10(%43: u32, %44: u64, %45: u64, %46: u64):
    %333 = const i64 8
    %334 = gep i8, ptr %1, %333
    %335 = load u64, ptr %334
    %336 = icmp ult u64 %46, %335
    condbr %336, bb11(%43, %44, %45, %46, %46), bb69
bb11(%47: u32, %48: u64, %49: u64, %50: u64, %51: u64):
    %337 = load ptr, ptr %1
    %338 = const u64 72
    %339 = mul u64 %51, %338
    %340 = gep i8, ptr %337, %339
    %341 = const i64 64
    %342 = gep i8, ptr %340, %341
    %343 = call @func.19(%342, %267)
    br bb12(%47, %48, %49, %50, %343)
bb12(%52: u32, %53: u64, %54: u64, %55: u64, %56: bool):
    condbr %56, bb13(%52, %53, %55), bb14(%52, %53, %54, %55)
bb13(%57: u32, %58: u64, %59: u64):
    br bb16(%57, %58, %59)
bb14(%60: u32, %61: u64, %62: u64, %63: u64):
    %344 = const u64 1
    %345, %346 = add.overflow u64 %63, %344
    store u64 %345, ptr %268
    %347 = const i64 8
    %348 = gep i8, ptr %268, %347
    store bool %346, ptr %348
    %349 = const i64 8
    %350 = gep i8, ptr %268, %349
    %351 = load bool, ptr %350
    %352 = const bool false
    %353 = icmp eq bool %351, %352
    condbr %353, bb15(%60, %61, %62), bb69
bb15(%64: u32, %65: u64, %66: u64):
    %354 = load u64, ptr %268
    br bb9(%64, %65, %66, %354)
bb16(%67: u32, %68: u64, %69: u64):
    %355 = const i64 8
    %356 = gep i8, ptr %1, %355
    %357 = load u64, ptr %356
    %358 = icmp ult u64 %69, %357
    condbr %358, bb17(%67, %68, %69), bb69
bb17(%70: u32, %71: u64, %72: u64):
    %359 = load ptr, ptr %1
    %360 = const u64 72
    %361 = mul u64 %72, %360
    %362 = gep i8, ptr %359, %361
    store ptr %362, ptr %269
    call @func.21(%270, %267, %6, %267)
    br bb18(%70, %71)
bb18(%73: u32, %74: u64):
    call @func.7(%272, %264)
    br bb19(%73, %74)
bb19(%75: u32, %76: u64):
    %363 = load ptr, ptr %269
    call @func.27(%271, %363, %272, %75)
    br bb20(%75, %76)
bb20(%77: u32, %78: u64):
    call @func.8(%273)
    br bb21(%77, %78)
bb21(%79: u32, %80: u64):
    %364 = const u64 0
    br bb22(%79, %80, %364)
bb22(%81: u32, %82: u64, %83: u64):
    %365 = const i64 8
    %366 = gep i8, ptr %1, %365
    %367 = load u64, ptr %366
    %368 = icmp ult u64 %83, %367
    condbr %368, bb23(%81, %82, %83), bb36(%81, %82)
bb23(%84: u32, %85: u64, %86: u64):
    %369 = const i64 8
    %370 = gep i8, ptr %1, %369
    %371 = load u64, ptr %370
    %372 = icmp ult u64 %86, %371
    condbr %372, bb24(%84, %85, %86, %86), bb69
bb24(%87: u32, %88: u64, %89: u64, %90: u64):
    %373 = load ptr, ptr %1
    %374 = const u64 72
    %375 = mul u64 %90, %374
    %376 = gep i8, ptr %373, %375
    call @func.7(%275, %264)
    br bb25(%87, %88, %89, %376)
bb25(%91: u32, %92: u64, %93: u64, %94: ptr):
    call @func.27(%274, %94, %275, %91)
    br bb26(%91, %92, %93)
bb26(%95: u32, %96: u64, %97: u64):
    %377 = const u64 0
    br bb27(%95, %96, %97, %377)
bb27(%98: u32, %99: u64, %100: u64, %101: u64):
    %378 = call @func.9(%274)
    br bb28(%98, %99, %100, %101, %101, %378)
bb28(%102: u32, %103: u64, %104: u64, %105: u64, %106: u64, %107: u64):
    %379 = icmp ult u64 %106, %107
    condbr %379, bb29(%102, %103, %104, %105), bb34(%102, %103, %104)
bb29(%108: u32, %109: u64, %110: u64, %111: u64):
    %380 = call @func.10(%274, %111)
    br bb30(%108, %109, %110, %111, %273, %380)
bb30(%112: u32, %113: u64, %114: u64, %115: u64, %116: ptr, %117: ptr):
    call @func.30(%276, %117)
    br bb31(%112, %113, %114, %115, %116)
bb31(%118: u32, %119: u64, %120: u64, %121: u64, %122: ptr):
    call @func.11(%122, %276)
    br bb32(%118, %119, %120, %121)
bb32(%123: u32, %124: u64, %125: u64, %126: u64):
    %381 = const u64 1
    %382, %383 = add.overflow u64 %126, %381
    store u64 %382, ptr %277
    %384 = const i64 8
    %385 = gep i8, ptr %277, %384
    store bool %383, ptr %385
    %386 = const i64 8
    %387 = gep i8, ptr %277, %386
    %388 = load bool, ptr %387
    %389 = const bool false
    %390 = icmp eq bool %388, %389
    condbr %390, bb33(%123, %124, %125), bb69
bb33(%127: u32, %128: u64, %129: u64):
    %391 = load u64, ptr %277
    br bb27(%127, %128, %129, %391)
bb34(%130: u32, %131: u64, %132: u64):
    %392 = const u64 1
    %393, %394 = add.overflow u64 %132, %392
    store u64 %393, ptr %278
    %395 = const i64 8
    %396 = gep i8, ptr %278, %395
    store bool %394, ptr %396
    %397 = const i64 8
    %398 = gep i8, ptr %278, %397
    %399 = load bool, ptr %398
    %400 = const bool false
    %401 = icmp eq bool %399, %400
    condbr %401, bb35(%130, %131), bb69
bb35(%133: u32, %134: u64):
    %402 = load u64, ptr %278
    br bb22(%133, %134, %402)
bb36(%135: u32, %136: u64):
    %403 = const u64 0
    %404 = const u64 0
    br bb37(%135, %136, %403, %404)
bb37(%137: u32, %138: u64, %139: u64, %140: u64):
    %405 = const i64 8
    %406 = gep i8, ptr %1, %405
    %407 = load u64, ptr %406
    %408 = icmp ult u64 %140, %407
    condbr %408, bb38(%137, %138, %139, %140), bb46(%137, %138, %139)
bb38(%141: u32, %142: u64, %143: u64, %144: u64):
    %409 = const i64 8
    %410 = gep i8, ptr %1, %409
    %411 = load u64, ptr %410
    %412 = icmp ult u64 %144, %411
    condbr %412, bb39(%141, %142, %143, %144, %144), bb69
bb39(%145: u32, %146: u64, %147: u64, %148: u64, %149: u64):
    %413 = load ptr, ptr %1
    %414 = const u64 72
    %415 = mul u64 %149, %414
    %416 = gep i8, ptr %413, %415
    %417 = const i64 64
    %418 = gep i8, ptr %416, %417
    %419 = load ptr, ptr %269
    %420 = const i64 64
    %421 = gep i8, ptr %419, %420
    %422 = call @func.12(%418, %421)
    br bb40(%145, %146, %147, %148, %422)
bb40(%150: u32, %151: u64, %152: u64, %153: u64, %154: bool):
    condbr %154, bb41(%150, %151, %152, %153), bb46(%150, %151, %152)
bb41(%155: u32, %156: u64, %157: u64, %158: u64):
    %423 = const i64 8
    %424 = gep i8, ptr %1, %423
    %425 = load u64, ptr %424
    %426 = icmp ult u64 %158, %425
    condbr %426, bb42(%155, %156, %157, %158, %158), bb69
bb42(%159: u32, %160: u64, %161: u64, %162: u64, %163: u64):
    %427 = load ptr, ptr %1
    %428 = const u64 72
    %429 = mul u64 %163, %428
    %430 = gep i8, ptr %427, %429
    %431 = call @func.13(%430)
    br bb43(%159, %160, %161, %162, %431)
bb43(%164: u32, %165: u64, %166: u64, %167: u64, %168: u64):
    %432, %433 = add.overflow u64 %166, %168
    store u64 %432, ptr %279
    %434 = const i64 8
    %435 = gep i8, ptr %279, %434
    store bool %433, ptr %435
    %436 = const i64 8
    %437 = gep i8, ptr %279, %436
    %438 = load bool, ptr %437
    %439 = const bool false
    %440 = icmp eq bool %438, %439
    condbr %440, bb44(%164, %165, %167), bb69
bb44(%169: u32, %170: u64, %171: u64):
    %441 = load u64, ptr %279
    %442 = const u64 1
    %443, %444 = add.overflow u64 %171, %442
    store u64 %443, ptr %280
    %445 = const i64 8
    %446 = gep i8, ptr %280, %445
    store bool %444, ptr %446
    %447 = const i64 8
    %448 = gep i8, ptr %280, %447
    %449 = load bool, ptr %448
    %450 = const bool false
    %451 = icmp eq bool %449, %450
    condbr %451, bb45(%169, %170, %441), bb69
bb45(%172: u32, %173: u64, %174: u64):
    %452 = load u64, ptr %280
    br bb37(%172, %173, %174, %452)
bb46(%175: u32, %176: u64, %177: u64):
    %453 = load ptr, ptr %269
    %454 = const i64 24
    %455 = gep i8, ptr %453, %454
    %456 = call @func.32(%455)
    br bb47(%175, %176, %177, %456)
bb47(%178: u32, %179: u64, %180: u64, %181: u32):
    %457 = call @func.14(%181, %178)
    br bb48(%178, %179, %180, %457)
bb48(%182: u32, %183: u64, %184: u64, %185: u32):
    %458 = const i64 8
    %459 = gep i8, ptr %1, %458
    %460 = load u64, ptr %459
    %461 = trunc u64 %460 to u32
    %462 = call @func.9(%273)
    br bb49(%182, %183, %184, %185, %461, %462)
bb49(%186: u32, %187: u64, %188: u64, %189: u32, %190: u32, %191: u64):
    %463 = load ptr, ptr %269
    %464 = const i64 24
    %465 = gep i8, ptr %463, %464
    call @func.15(%282, %273)
    br bb50(%186, %187, %188, %189, %190, %191, %267, %465)
bb50(%192: u32, %193: u64, %194: u64, %195: u32, %196: u32, %197: u64, %198: ptr, %199: ptr):
    call @func.47(%281, %198, %199, %192, %195, %3, %4, %282, %1)
    br bb51(%192, %193, %194, %195, %196, %197)
bb51(%200: u32, %201: u64, %202: u64, %203: u32, %204: u32, %205: u64):
    %466 = const u64 0
    %467 = icmp eq u64 %201, %466
    condbr %467, bb52, bb53(%200, %201, %202, %203, %204, %205)
bb52:
    %468 = load i64, ptr %281
    store i64 %468, ptr %0
    %469 = const i64 8
    %470 = gep i8, ptr %281, %469
    %471 = const i64 8
    %472 = gep i8, ptr %0, %471
    %473 = load i64, ptr %470
    store i64 %473, ptr %472
    %474 = const i64 16
    %475 = gep i8, ptr %281, %474
    %476 = const i64 16
    %477 = gep i8, ptr %0, %476
    %478 = load i64, ptr %475
    store i64 %478, ptr %477
    %479 = const i64 24
    %480 = gep i8, ptr %281, %479
    %481 = const i64 24
    %482 = gep i8, ptr %0, %481
    %483 = load i64, ptr %480
    store i64 %483, ptr %482
    %484 = const i64 32
    %485 = gep i8, ptr %281, %484
    %486 = const i64 32
    %487 = gep i8, ptr %0, %486
    %488 = load i64, ptr %485
    store i64 %488, ptr %487
    br bb66
bb53(%206: u32, %207: u64, %208: u64, %209: u32, %210: u32, %211: u64):
    %489 = const u64 1
    %490, %491 = sub.overflow u64 %207, %489
    store u64 %490, ptr %283
    %492 = const i64 8
    %493 = gep i8, ptr %283, %492
    store bool %491, ptr %493
    %494 = const i64 8
    %495 = gep i8, ptr %283, %494
    %496 = load bool, ptr %495
    %497 = const bool false
    %498 = icmp eq bool %496, %497
    condbr %498, bb54(%206, %208, %209, %210, %211), bb69
bb54(%212: u32, %213: u64, %214: u32, %215: u32, %216: u64):
    %499 = load u64, ptr %283
    %500 = call @func.9(%271)
    br bb55(%212, %213, %214, %215, %216, %499, %499, %500)
bb55(%217: u32, %218: u64, %219: u32, %220: u32, %221: u64, %222: u64, %223: u64, %224: u64):
    %501 = icmp uge u64 %223, %224
    condbr %501, bb56(%217, %218, %219, %220, %221), bb57(%217, %218, %219, %220, %221, %222)
bb56(%225: u32, %226: u64, %227: u32, %228: u32, %229: u64):
    %502 = const u64 0
    br bb57(%225, %226, %227, %228, %229, %502)
bb57(%230: u32, %231: u64, %232: u32, %233: u32, %234: u64, %235: u64):
    %503 = call @func.10(%271, %235)
    store ptr %503, ptr %284
    br bb58(%230, %231, %232, %233, %234, %235)
bb58(%236: u32, %237: u64, %238: u32, %239: u32, %240: u64, %241: u64):
    %504 = load ptr, ptr %284
    %505 = const i64 76
    %506 = gep i8, ptr %504, %505
    %507 = load u32, ptr %506
    %508 = load ptr, ptr %284
    call @func.16(%285, %508)
    br bb59(%236, %237, %238, %239, %240, %241, %270, %507)
bb59(%242: u32, %243: u64, %244: u32, %245: u32, %246: u64, %247: u64, %248: ptr, %249: u32):
    %509 = load ptr, ptr %284
    %510 = const i64 24
    %511 = gep i8, ptr %509, %510
    call @func.17(%286, %511)
    br bb60(%242, %243, %244, %245, %246, %247, %248, %249)
bb60(%250: u32, %251: u64, %252: u32, %253: u32, %254: u64, %255: u64, %256: ptr, %257: u32):
    %512, %513 = add.overflow u64 %251, %255
    store u64 %512, ptr %287
    %514 = const i64 8
    %515 = gep i8, ptr %287, %514
    store bool %513, ptr %515
    %516 = const i64 8
    %517 = gep i8, ptr %287, %516
    %518 = load bool, ptr %517
    %519 = const bool false
    %520 = icmp eq bool %518, %519
    condbr %520, bb61(%250, %252, %253, %254, %256, %257), bb69
bb61(%258: u32, %259: u32, %260: u32, %261: u64, %262: ptr, %263: u32):
    %521 = load u64, ptr %287
    call @func.59(%0, %262, %5, %258, %260, %259, %263, %285, %286, %261, %521, %281, %1, %6)
    br bb62
bb62:
    br bb63
bb63:
    br bb64
bb64:
    br bb65
bb65:
    br bb68
bb66:
    br bb67
bb67:
    br bb68
bb68:
    ret
bb69:
    unreachable
}

fn @_Name_as_std__cmp__PartialEq___eq(functy.19) {
bb0(%0: ptr, %1: ptr):
    %2 = load u32, ptr %0
    %3 = load u32, ptr %1
    %4 = icmp eq u32 %2, %3
    ret %4
}

fn @_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4NameNtB7_9PartialEq2eqBF_(functy.20) {
}

fn @rec_name_of(functy.21) {
bb0(%0: ptr, %1: ptr, %2: ptr, %3: ptr):
    %20 = alloca i64, align 8
    %21 = alloca i64, align 8
    %22 = alloca (i64, i64), align 8
    store ptr %1, ptr %20
    %23 = const u64 0
    br bb1(%3, %23)
bb1(%4: ptr, %5: u64):
    %24 = const i64 8
    %25 = gep i8, ptr %2, %24
    %26 = load u64, ptr %25
    %27 = icmp ult u64 %5, %26
    condbr %27, bb2(%4, %5), bb9(%4)
bb2(%6: ptr, %7: u64):
    %28 = const i64 8
    %29 = gep i8, ptr %2, %28
    %30 = load u64, ptr %29
    %31 = icmp ult u64 %7, %30
    condbr %31, bb3(%6, %7, %7), bb11
bb3(%8: ptr, %9: u64, %10: u64):
    %32 = load ptr, ptr %2
    %33 = const u64 8
    %34 = mul u64 %10, %33
    %35 = gep i8, ptr %32, %34
    store ptr %35, ptr %21
    %36 = call @func.20(%21, %20)
    br bb4(%8, %9, %36)
bb4(%11: ptr, %12: u64, %13: bool):
    condbr %13, bb5(%12), bb7(%11, %12)
bb5(%14: u64):
    %37 = const i64 8
    %38 = gep i8, ptr %2, %37
    %39 = load u64, ptr %38
    %40 = icmp ult u64 %14, %39
    condbr %40, bb6(%14), bb11
bb6(%15: u64):
    %41 = load ptr, ptr %2
    %42 = const u64 8
    %43 = mul u64 %15, %42
    %44 = gep i8, ptr %41, %43
    %45 = const i64 4
    %46 = gep i8, ptr %44, %45
    %47 = load i32, ptr %46
    store i32 %47, ptr %0
    br bb10
bb7(%16: ptr, %17: u64):
    %48 = const u64 1
    %49, %50 = add.overflow u64 %17, %48
    store u64 %49, ptr %22
    %51 = const i64 8
    %52 = gep i8, ptr %22, %51
    store bool %50, ptr %52
    %53 = const i64 8
    %54 = gep i8, ptr %22, %53
    %55 = load bool, ptr %54
    %56 = const bool false
    %57 = icmp eq bool %55, %56
    condbr %57, bb8(%16), bb11
bb8(%18: ptr):
    %58 = load u64, ptr %22
    br bb1(%18, %58)
bb9(%19: ptr):
    %59 = load i32, ptr %19
    store i32 %59, ptr %0
    br bb10
bb10:
    ret
bb11:
    unreachable
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4CtorE3lenBG_(functy.22) {
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice8CtorInfoE13with_capacityBE_(functy.23) {
}

fn @_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4CtorEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_(functy.24) {
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm14saturating_sub(functy.25) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice8CtorInfoE4pushBH_(functy.26) {
}

fn @compute_ctor_infos(functy.27) {
bb0(%0: ptr, %1: ptr, %2: ptr, %3: u32):
    %35 = alloca i64, align 8
    %36 = alloca (i64, i64, i64), align 8
    %37 = alloca i64, align 8
    %38 = alloca (i64, i64, i64), align 8
    %39 = alloca (i64, i64, i64), align 8
    %40 = alloca (i64, i64, i64), align 8
    %41 = alloca (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64), align 8
    %42 = alloca i32, align 4
    %43 = alloca (i64, i64, i64), align 8
    %44 = alloca (i64, i64, i64), align 8
    %45 = alloca (i64, i64), align 8
    store ptr %1, ptr %35
    %46 = const bool false
    %47 = const bool false
    %48 = load ptr, ptr %35
    %49 = call @func.22(%48)
    br bb1(%3, %49)
bb1(%4: u32, %5: u64):
    call @func.23(%36, %5)
    br bb2(%4)
bb2(%6: u32):
    %50 = const u64 0
    br bb3(%6, %50)
bb3(%7: u32, %8: u64):
    %51 = load ptr, ptr %35
    %52 = call @func.22(%51)
    br bb4(%7, %8, %8, %52)
bb4(%9: u32, %10: u64, %11: u64, %12: u64):
    %53 = icmp ult u64 %11, %12
    condbr %53, bb5(%9, %10), bb14
bb5(%13: u32, %14: u64):
    %54 = load ptr, ptr %35
    %55 = call @func.24(%54, %14)
    store ptr %55, ptr %37
    br bb6(%13, %14)
bb6(%15: u32, %16: u64):
    %56 = load ptr, ptr %37
    %57 = call @func.32(%56)
    br bb7(%15, %16, %57)
bb7(%17: u32, %18: u64, %19: u32):
    %58 = call @func.25(%19, %17)
    br bb8(%17, %18, %58)
bb8(%20: u32, %21: u64, %22: u32):
    %59 = load ptr, ptr %37
    call @func.62(%38, %59, %2, %20)
    br bb9(%20, %21, %22)
bb9(%23: u32, %24: u64, %25: u32):
    %60 = const bool true
    %61 = load ptr, ptr %37
    call @func.65(%39, %61, %23)
    br bb10(%23, %24, %25)
bb10(%26: u32, %27: u64, %28: u32):
    %62 = const bool true
    %63 = load ptr, ptr %37
    call @func.70(%40, %63, %26)
    br bb11(%26, %27, %28)
bb11(%29: u32, %30: u64, %31: u32):
    %64 = load ptr, ptr %37
    %65 = const i64 40
    %66 = gep i8, ptr %64, %65
    %67 = load i32, ptr %66
    store i32 %67, ptr %42
    %68 = const bool false
    %69 = load i64, ptr %38
    store i64 %69, ptr %43
    %70 = const i64 8
    %71 = gep i8, ptr %38, %70
    %72 = const i64 8
    %73 = gep i8, ptr %43, %72
    %74 = load i64, ptr %71
    store i64 %74, ptr %73
    %75 = const i64 16
    %76 = gep i8, ptr %38, %75
    %77 = const i64 16
    %78 = gep i8, ptr %43, %77
    %79 = load i64, ptr %76
    store i64 %79, ptr %78
    %80 = const bool false
    %81 = load i64, ptr %39
    store i64 %81, ptr %44
    %82 = const i64 8
    %83 = gep i8, ptr %39, %82
    %84 = const i64 8
    %85 = gep i8, ptr %44, %84
    %86 = load i64, ptr %83
    store i64 %86, ptr %85
    %87 = const i64 16
    %88 = gep i8, ptr %39, %87
    %89 = const i64 16
    %90 = gep i8, ptr %44, %89
    %91 = load i64, ptr %88
    store i64 %91, ptr %90
    %92 = const i64 72
    %93 = gep i8, ptr %41, %92
    %94 = load i32, ptr %42
    store i32 %94, ptr %93
    %95 = const i64 76
    %96 = gep i8, ptr %41, %95
    store u32 %31, ptr %96
    %97 = load i64, ptr %43
    store i64 %97, ptr %41
    %98 = const i64 8
    %99 = gep i8, ptr %43, %98
    %100 = const i64 8
    %101 = gep i8, ptr %41, %100
    %102 = load i64, ptr %99
    store i64 %102, ptr %101
    %103 = const i64 16
    %104 = gep i8, ptr %43, %103
    %105 = const i64 16
    %106 = gep i8, ptr %41, %105
    %107 = load i64, ptr %104
    store i64 %107, ptr %106
    %108 = const i64 24
    %109 = gep i8, ptr %41, %108
    %110 = load i64, ptr %44
    store i64 %110, ptr %109
    %111 = const i64 8
    %112 = gep i8, ptr %44, %111
    %113 = const i64 8
    %114 = gep i8, ptr %109, %113
    %115 = load i64, ptr %112
    store i64 %115, ptr %114
    %116 = const i64 16
    %117 = gep i8, ptr %44, %116
    %118 = const i64 16
    %119 = gep i8, ptr %109, %118
    %120 = load i64, ptr %117
    store i64 %120, ptr %119
    %121 = const i64 48
    %122 = gep i8, ptr %41, %121
    %123 = load i64, ptr %40
    store i64 %123, ptr %122
    %124 = const i64 8
    %125 = gep i8, ptr %40, %124
    %126 = const i64 8
    %127 = gep i8, ptr %122, %126
    %128 = load i64, ptr %125
    store i64 %128, ptr %127
    %129 = const i64 16
    %130 = gep i8, ptr %40, %129
    %131 = const i64 16
    %132 = gep i8, ptr %122, %131
    %133 = load i64, ptr %130
    store i64 %133, ptr %132
    call @func.26(%36, %41)
    br bb12(%29, %30)
bb12(%32: u32, %33: u64):
    %134 = const u64 1
    %135, %136 = add.overflow u64 %33, %134
    store u64 %135, ptr %45
    %137 = const i64 8
    %138 = gep i8, ptr %45, %137
    store bool %136, ptr %138
    %139 = const i64 8
    %140 = gep i8, ptr %45, %139
    %141 = load bool, ptr %140
    %142 = const bool false
    %143 = icmp eq bool %141, %142
    condbr %143, bb13(%32), bb15
bb13(%34: u32):
    %144 = load u64, ptr %45
    %145 = const bool false
    %146 = const bool false
    br bb3(%34, %144)
bb14:
    %147 = load i64, ptr %36
    store i64 %147, ptr %0
    %148 = const i64 8
    %149 = gep i8, ptr %36, %148
    %150 = const i64 8
    %151 = gep i8, ptr %0, %150
    %152 = load i64, ptr %149
    store i64 %152, ptr %151
    %153 = const i64 16
    %154 = gep i8, ptr %36, %153
    %155 = const i64 16
    %156 = gep i8, ptr %0, %155
    %157 = load i64, ptr %154
    store i64 %157, ptr %156
    ret
bb15:
    unreachable
}

fn @_RNvXsa_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecbENtNtCs2EYQwhfuABO_4core5clone5Clone5cloneCs6RT0DENTjyC_27clean_mutual_recursor_slice(functy.28) {
}

fn @_RNvXsa_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprENtNtCs2EYQwhfuABO_4core5clone5Clone5cloneBH_(functy.29) {
}

fn @_CtorInfo_as_std__clone__Clone___clone(functy.30) {
bb0(%0: ptr, %1: ptr):
    %5 = alloca i64, align 8
    %6 = alloca i32, align 4
    %7 = alloca (i64, i64, i64), align 8
    %8 = alloca (i64, i64, i64), align 8
    %9 = alloca (i64, i64, i64), align 8
    store ptr %1, ptr %5
    %10 = load ptr, ptr %5
    %11 = const i64 72
    %12 = gep i8, ptr %10, %11
    call @func.71(%6, %12)
    br bb1
bb1:
    %13 = load ptr, ptr %5
    %14 = const i64 76
    %15 = gep i8, ptr %13, %14
    %16 = load u32, ptr %15
    %17 = load ptr, ptr %5
    call @func.28(%7, %17)
    br bb2(%16)
bb2(%2: u32):
    %18 = load ptr, ptr %5
    %19 = const i64 24
    %20 = gep i8, ptr %18, %19
    call @func.29(%8, %20)
    br bb3(%2)
bb3(%3: u32):
    %21 = load ptr, ptr %5
    %22 = const i64 48
    %23 = gep i8, ptr %21, %22
    call @func.29(%9, %23)
    br bb4(%3)
bb4(%4: u32):
    %24 = const i64 72
    %25 = gep i8, ptr %0, %24
    %26 = load i32, ptr %6
    store i32 %26, ptr %25
    %27 = const i64 76
    %28 = gep i8, ptr %0, %27
    store u32 %4, ptr %28
    %29 = load i64, ptr %7
    store i64 %29, ptr %0
    %30 = const i64 8
    %31 = gep i8, ptr %7, %30
    %32 = const i64 8
    %33 = gep i8, ptr %0, %32
    %34 = load i64, ptr %31
    store i64 %34, ptr %33
    %35 = const i64 16
    %36 = gep i8, ptr %7, %35
    %37 = const i64 16
    %38 = gep i8, ptr %0, %37
    %39 = load i64, ptr %36
    store i64 %39, ptr %38
    %40 = const i64 24
    %41 = gep i8, ptr %0, %40
    %42 = load i64, ptr %8
    store i64 %42, ptr %41
    %43 = const i64 8
    %44 = gep i8, ptr %8, %43
    %45 = const i64 8
    %46 = gep i8, ptr %41, %45
    %47 = load i64, ptr %44
    store i64 %47, ptr %46
    %48 = const i64 16
    %49 = gep i8, ptr %8, %48
    %50 = const i64 16
    %51 = gep i8, ptr %41, %50
    %52 = load i64, ptr %49
    store i64 %52, ptr %51
    %53 = const i64 48
    %54 = gep i8, ptr %0, %53
    %55 = load i64, ptr %9
    store i64 %55, ptr %54
    %56 = const i64 8
    %57 = gep i8, ptr %9, %56
    %58 = const i64 8
    %59 = gep i8, ptr %54, %58
    %60 = load i64, ptr %57
    store i64 %60, ptr %59
    %61 = const i64 16
    %62 = gep i8, ptr %9, %61
    %63 = const i64 16
    %64 = gep i8, ptr %54, %63
    %65 = load i64, ptr %62
    store i64 %65, ptr %64
    ret
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm14saturating_add(functy.31) {
}

fn @count_pi_args(functy.32) {
bb0(%0: ptr):
    %8 = alloca i64, align 8
    %9 = alloca i64, align 8
    %10 = const u32 0
    store ptr %0, ptr %8
    br bb1(%10)
bb1(%1: u32):
    %11 = load ptr, ptr %8
    store ptr %11, ptr %9
    %12 = load ptr, ptr %9
    %13 = load i8, ptr %12
    %14 = sext i8 %13 to i64
    switch %14 [ 6: bb2(%1) default: bb5(%1) ]
bb2(%2: u32):
    %15 = load ptr, ptr %9
    %16 = const i64 16
    %17 = gep i8, ptr %15, %16
    %18 = const u32 1
    %19 = call @func.31(%2, %18)
    br bb3(%17, %19)
bb3(%3: ptr, %4: u32):
    %20 = load ptr, ptr %3
    %21 = const i64 16
    %22 = gep i8, ptr %20, %21
    br bb4(%4, %22)
bb4(%5: u32, %6: ptr):
    store ptr %6, ptr %8
    br bb1(%5)
bb5(%7: u32):
    ret %7
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprE13with_capacityBE_(functy.33) {
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm14saturating_sub(functy.34) {
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecTNtCs6RT0DENTjyC_27clean_mutual_recursor_slice10BinderDataNtBH_4ExprEE3lenBH_(functy.35) {
}

fn @_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecTNtCs6RT0DENTjyC_27clean_mutual_recursor_slice10BinderDataNtBI_4ExprEEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBI_(functy.36) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprE4pushBH_(functy.37) {
}

fn @_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4NameNtB7_9PartialEq2eqBF_(functy.38) {
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecTNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprbEE3newBF_(functy.39) {
}

fn @_RNvXs7_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecbENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefCs6RT0DENTjyC_27clean_mutual_recursor_slice(functy.40) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecTNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprbEE4pushBI_(functy.41) {
}

fn @_RNvXs7_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefBH_(functy.42) {
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecTNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprbEE3lenBH_(functy.43) {
}

fn @_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecTNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprbEEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBI_(functy.44) {
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprE3lenBG_(functy.45) {
}

fn @_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_(functy.46) {
}

fn @build_recursor_type(functy.47) {
bb0(%0: ptr, %1: ptr, %2: ptr, %3: u32, %4: u32, %5: ptr, %6: ptr, %7: ptr, %8: ptr):
    %467 = alloca i64, align 8
    %468 = alloca i32, align 4
    %469 = alloca i32, align 4
    %470 = alloca (i64, i64), align 8
    %471 = alloca i32, align 4
    %472 = alloca (i64, i64, i64, i64, i64), align 8
    %473 = alloca (i64, i64, i64), align 8
    %474 = alloca (i64, i64, i64, i64, i64), align 8
    %475 = alloca i64, align 8
    %476 = alloca (i64, i64, i64, i64, i64), align 8
    %477 = alloca (i32, i32), align 4
    %478 = alloca (i64, i64, i64), align 8
    %479 = alloca (i64, i64, i64), align 8
    %480 = alloca (i64, i64, i64), align 8
    %481 = alloca i64, align 8
    %482 = alloca (i64, i64, i64, i64, i64), align 8
    %483 = alloca (i64, i64, i64), align 8
    %484 = alloca (i64, i64, i64, i64, i64), align 8
    %485 = alloca (i64, i64, i64, i64), align 8
    %486 = alloca (i64, i64), align 8
    %487 = alloca (i64, i64, i64, i64, i64), align 8
    %488 = alloca (i32, i32), align 4
    %489 = alloca (i32, i32), align 4
    %490 = alloca (i32, i32), align 4
    %491 = alloca (i64, i64, i64, i64, i64), align 8
    %492 = alloca (i64, i64, i64, i64, i64), align 8
    %493 = alloca (i64, i64, i64, i64, i64), align 8
    %494 = alloca (i32, i32), align 4
    %495 = alloca (i32, i32), align 4
    %496 = alloca (i32, i32), align 4
    %497 = alloca (i64, i64, i64, i64, i64), align 8
    %498 = alloca (i64, i64, i64, i64, i64), align 8
    %499 = alloca (i64, i64, i64, i64, i64), align 8
    %500 = alloca (i32, i32), align 4
    %501 = alloca (i64, i64, i64, i64, i64), align 8
    %502 = alloca (i8, i8), align 1
    %503 = alloca (i64, i64, i64, i64, i64), align 8
    %504 = alloca (i64, i64, i64, i64, i64), align 8
    %505 = alloca (i64, i64), align 8
    %506 = alloca i64, align 8
    %507 = alloca (i64, i64, i64, i64, i64), align 8
    %508 = alloca (i8, i8), align 1
    %509 = alloca (i64, i64, i64, i64, i64), align 8
    %510 = alloca (i64, i64, i64, i64, i64), align 8
    %511 = alloca (i64, i64, i64, i64, i64), align 8
    %512 = alloca (i64, i64), align 8
    %513 = alloca (i64, i64), align 8
    %514 = alloca i64, align 8
    %515 = alloca (i64, i64), align 8
    %516 = alloca (i64, i64), align 8
    %517 = alloca (i64, i64, i64), align 8
    %518 = alloca i64, align 8
    %519 = alloca (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64), align 8
    %520 = alloca (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64), align 8
    %521 = alloca (i64, i64, i64, i64, i64, i64), align 8
    %522 = alloca (i64, i64, i64, i64, i64), align 8
    %523 = alloca (i64, i64, i64, i64, i64), align 8
    %524 = alloca (i64, i64), align 8
    %525 = alloca (i64, i64), align 8
    %526 = alloca (i64, i64), align 8
    %527 = alloca (i64, i64, i64, i64, i64, i64), align 8
    %528 = alloca (i64, i64), align 8
    %529 = alloca (i64, i64), align 8
    %530 = alloca (i64, i64), align 8
    %531 = alloca (i64, i64), align 8
    %532 = alloca (i64, i64), align 8
    %533 = alloca (i64, i64), align 8
    %534 = alloca (i64, i64, i64, i64, i64), align 8
    %535 = alloca (i64, i64), align 8
    %536 = alloca (i64, i64, i64, i64, i64), align 8
    %537 = alloca (i64, i64, i64, i64, i64), align 8
    %538 = alloca (i64, i64, i64, i64, i64), align 8
    %539 = alloca (i32, i32), align 4
    %540 = alloca (i64, i64, i64, i64, i64), align 8
    %541 = alloca (i64, i64, i64, i64, i64), align 8
    %542 = alloca (i64, i64, i64, i64, i64), align 8
    %543 = alloca (i64, i64, i64, i64, i64), align 8
    %544 = alloca (i32, i32), align 4
    %545 = alloca (i32, i32), align 4
    %546 = alloca (i32, i32), align 4
    %547 = alloca (i64, i64, i64, i64, i64), align 8
    %548 = alloca (i8, i8), align 1
    %549 = alloca (i64, i64, i64, i64, i64), align 8
    %550 = alloca (i64, i64, i64, i64, i64), align 8
    %551 = alloca (i64, i64), align 8
    %552 = alloca (i64, i64), align 8
    %553 = alloca i64, align 8
    %554 = alloca (i64, i64, i64, i64, i64), align 8
    %555 = alloca (i64, i64, i64, i64, i64), align 8
    %556 = alloca (i8, i8), align 1
    %557 = alloca (i64, i64, i64, i64, i64), align 8
    %558 = alloca (i64, i64, i64, i64, i64), align 8
    %559 = alloca (i64, i64), align 8
    %560 = alloca i64, align 8
    %561 = alloca (i64, i64, i64, i64, i64), align 8
    %562 = alloca (i64, i64, i64, i64, i64), align 8
    %563 = alloca (i8, i8), align 1
    %564 = alloca (i64, i64, i64, i64, i64), align 8
    %565 = alloca (i64, i64, i64, i64, i64), align 8
    %566 = alloca (i64, i64), align 8
    %567 = alloca (i64, i64, i64, i64, i64), align 8
    %568 = alloca (i64, i64, i64, i64, i64), align 8
    %569 = alloca (i8, i8), align 1
    %570 = alloca (i64, i64, i64, i64, i64), align 8
    %571 = alloca (i64, i64, i64, i64, i64), align 8
    %572 = alloca (i64, i64), align 8
    %573 = alloca i64, align 8
    %574 = alloca (i64, i64, i64, i64, i64), align 8
    %575 = alloca (i8, i8), align 1
    %576 = alloca (i64, i64, i64, i64, i64), align 8
    %577 = alloca (i64, i64, i64, i64, i64), align 8
    %578 = alloca (i64, i64, i64, i64, i64), align 8
    store ptr %1, ptr %467
    store u32 %3, ptr %468
    store u32 %4, ptr %469
    %579 = const bool false
    %580 = const bool false
    %581 = const bool false
    %582 = const bool false
    %583 = const bool false
    %584 = const bool false
    %585 = const bool false
    %586 = const bool false
    %587 = const bool false
    %588 = const bool false
    %589 = load i64, ptr %5
    %590 = const i64 0
    %591 = icmp eq i64 %589, %590
    %592 = const i64 0
    %593 = const i64 1
    %594 = select i64 %591, %592, %593
    switch %594 [ 0: bb2(%2) 1: bb3(%2) default: bb1 ]
bb1:
    unreachable
bb2(%9: ptr):
    %595 = const i32 0
    store i32 %595, ptr %470
    br bb4(%9)
bb3(%10: ptr):
    %596 = load ptr, ptr %5
    %597 = load i32, ptr %596
    store i32 %597, ptr %471
    %598 = const i64 4
    %599 = gep i8, ptr %470, %598
    %600 = load i32, ptr %471
    store i32 %600, ptr %599
    %601 = const i32 2
    store i32 %601, ptr %470
    br bb4(%10)
bb4(%11: ptr):
    %602 = load ptr, ptr %467
    call @func.74(%472, %602, %6)
    br bb5(%11)
bb5(%12: ptr):
    %603 = const i64 8
    %604 = gep i8, ptr %8, %603
    %605 = load u64, ptr %604
    %606 = load u32, ptr %468
    call @func.77(%473, %12, %606)
    br bb6(%12, %605)
bb6(%13: ptr, %14: u64):
    call @func.78(%474, %13)
    br bb7(%14)
bb7(%15: u64):
    %607 = const u32 0
    br bb8(%15, %607)
bb8(%16: u64, %17: u32):
    %608 = load u32, ptr %468
    %609 = icmp ult u32 %17, %608
    condbr %609, bb9(%16, %17), bb16(%16)
bb9(%18: u64, %19: u32):
    store ptr %474, ptr %475
    %610 = load ptr, ptr %475
    %611 = load i8, ptr %610
    %612 = sext i8 %611 to i64
    switch %612 [ 6: bb10(%18, %19) default: bb14(%18, %19) ]
bb10(%20: u64, %21: u32):
    %613 = load ptr, ptr %475
    %614 = const i64 16
    %615 = gep i8, ptr %613, %614
    %616 = load ptr, ptr %615
    %617 = const i64 16
    %618 = gep i8, ptr %616, %617
    br bb11(%20, %21, %618)
bb11(%22: u64, %23: u32, %24: ptr):
    call @func.78(%476, %24)
    br bb12(%22, %23)
bb12(%25: u64, %26: u32):
    br bb13(%25, %26)
bb13(%27: u64, %28: u32):
    %619 = load i64, ptr %476
    store i64 %619, ptr %474
    %620 = const i64 8
    %621 = gep i8, ptr %476, %620
    %622 = const i64 8
    %623 = gep i8, ptr %474, %622
    %624 = load i64, ptr %621
    store i64 %624, ptr %623
    %625 = const i64 16
    %626 = gep i8, ptr %476, %625
    %627 = const i64 16
    %628 = gep i8, ptr %474, %627
    %629 = load i64, ptr %626
    store i64 %629, ptr %628
    %630 = const i64 24
    %631 = gep i8, ptr %476, %630
    %632 = const i64 24
    %633 = gep i8, ptr %474, %632
    %634 = load i64, ptr %631
    store i64 %634, ptr %633
    %635 = const i64 32
    %636 = gep i8, ptr %476, %635
    %637 = const i64 32
    %638 = gep i8, ptr %474, %637
    %639 = load i64, ptr %636
    store i64 %639, ptr %638
    br bb14(%27, %28)
bb14(%29: u64, %30: u32):
    %640 = const u32 1
    %641, %642 = add.overflow u32 %30, %640
    store u32 %641, ptr %477
    %643 = const i64 4
    %644 = gep i8, ptr %477, %643
    store bool %642, ptr %644
    %645 = const i64 4
    %646 = gep i8, ptr %477, %645
    %647 = load bool, ptr %646
    %648 = const bool false
    %649 = icmp eq bool %647, %648
    condbr %649, bb15(%29), bb171
bb15(%31: u64):
    %650 = load u32, ptr %477
    br bb8(%31, %650)
bb16(%32: u64):
    %651 = load u32, ptr %469
    call @func.77(%478, %474, %651)
    br bb17(%32)
bb17(%33: u64):
    %652 = const i64 8
    %653 = gep i8, ptr %7, %652
    %654 = load u64, ptr %653
    store ptr %472, ptr %479
    %655 = const i64 8
    %656 = gep i8, ptr %479, %655
    store ptr %468, ptr %656
    %657 = const i64 16
    %658 = gep i8, ptr %479, %657
    store ptr %469, ptr %658
    call @func.33(%480, %33)
    br bb18(%33, %654)
bb18(%34: u64, %35: u64):
    %659 = const u64 0
    br bb19(%34, %35, %659)
bb19(%36: u64, %37: u64, %38: u64):
    %660 = const i64 8
    %661 = gep i8, ptr %8, %660
    %662 = load u64, ptr %661
    %663 = icmp ult u64 %38, %662
    condbr %663, bb20(%36, %37, %38), bb58(%36, %37)
bb20(%39: u64, %40: u64, %41: u64):
    %664 = const i64 8
    %665 = gep i8, ptr %8, %664
    %666 = load u64, ptr %665
    %667 = icmp ult u64 %41, %666
    condbr %667, bb21(%39, %40, %41, %41), bb171
bb21(%42: u64, %43: u64, %44: u64, %45: u64):
    %668 = load ptr, ptr %8
    %669 = const u64 72
    %670 = mul u64 %45, %669
    %671 = gep i8, ptr %668, %670
    store ptr %671, ptr %481
    %672 = load ptr, ptr %481
    %673 = const i64 64
    %674 = gep i8, ptr %672, %673
    call @func.74(%482, %674, %6)
    br bb22(%42, %43, %44)
bb22(%46: u64, %47: u64, %48: u64):
    %675 = load ptr, ptr %481
    %676 = const i64 24
    %677 = gep i8, ptr %675, %676
    %678 = call @func.32(%677)
    br bb23(%46, %47, %48, %678)
bb23(%49: u64, %50: u64, %51: u64, %52: u32):
    %679 = load u32, ptr %468
    %680 = call @func.34(%52, %679)
    br bb24(%49, %50, %51, %680)
bb24(%53: u64, %54: u64, %55: u64, %56: u32):
    %681 = load ptr, ptr %481
    %682 = const i64 24
    %683 = gep i8, ptr %681, %682
    %684 = load u32, ptr %468
    call @func.79(%483, %683, %684, %56)
    br bb25(%53, %54, %55, %56)
bb25(%57: u64, %58: u64, %59: u64, %60: u32):
    call @func.81(%486, %470)
    br bb26(%57, %58, %59, %60)
bb26(%61: u64, %62: u64, %63: u64, %64: u32):
    %685 = const i64 8
    %686 = gep i8, ptr %485, %685
    %687 = load i64, ptr %486
    store i64 %687, ptr %686
    %688 = const i64 8
    %689 = gep i8, ptr %486, %688
    %690 = const i64 8
    %691 = gep i8, ptr %686, %690
    %692 = load i64, ptr %689
    store i64 %692, ptr %691
    %693 = const i8 2
    store i8 %693, ptr %485
    call @func.82(%484, %485)
    br bb27(%61, %62, %63, %64)
bb27(%65: u64, %66: u64, %67: u64, %68: u32):
    %694 = const bool true
    call @func.78(%487, %482)
    br bb28(%65, %66, %67, %68)
bb28(%69: u64, %70: u64, %71: u64, %72: u32):
    %695 = const bool true
    %696 = const u32 0
    br bb29(%69, %70, %71, %72, %696)
bb29(%73: u64, %74: u64, %75: u64, %76: u32, %77: u32):
    %697 = load u32, ptr %468
    %698 = icmp ult u32 %77, %697
    condbr %698, bb30(%73, %74, %75, %76, %77), bb37(%73, %74, %75, %76)
bb30(%78: u64, %79: u64, %80: u64, %81: u32, %82: u32):
    %699 = load u32, ptr %468
    %700 = const u32 1
    %701, %702 = sub.overflow u32 %699, %700
    store u32 %701, ptr %488
    %703 = const i64 4
    %704 = gep i8, ptr %488, %703
    store bool %702, ptr %704
    %705 = const i64 4
    %706 = gep i8, ptr %488, %705
    %707 = load bool, ptr %706
    %708 = const bool false
    %709 = icmp eq bool %707, %708
    condbr %709, bb31(%78, %79, %80, %81, %82), bb171
bb31(%83: u64, %84: u64, %85: u64, %86: u32, %87: u32):
    %710 = load u32, ptr %488
    %711, %712 = sub.overflow u32 %710, %87
    store u32 %711, ptr %489
    %713 = const i64 4
    %714 = gep i8, ptr %489, %713
    store bool %712, ptr %714
    %715 = const i64 4
    %716 = gep i8, ptr %489, %715
    %717 = load bool, ptr %716
    %718 = const bool false
    %719 = icmp eq bool %717, %718
    condbr %719, bb32(%83, %84, %85, %86, %87), bb171
bb32(%88: u64, %89: u64, %90: u64, %91: u32, %92: u32):
    %720 = load u32, ptr %489
    %721, %722 = add.overflow u32 %91, %720
    store u32 %721, ptr %490
    %723 = const i64 4
    %724 = gep i8, ptr %490, %723
    store bool %722, ptr %724
    %725 = const i64 4
    %726 = gep i8, ptr %490, %725
    %727 = load bool, ptr %726
    %728 = const bool false
    %729 = icmp eq bool %727, %728
    condbr %729, bb33(%88, %89, %90, %91, %92), bb171
bb33(%93: u64, %94: u64, %95: u64, %96: u32, %97: u32):
    %730 = load u32, ptr %490
    %731 = const bool false
    %732 = const bool true
    %733 = load i64, ptr %487
    store i64 %733, ptr %492
    %734 = const i64 8
    %735 = gep i8, ptr %487, %734
    %736 = const i64 8
    %737 = gep i8, ptr %492, %736
    %738 = load i64, ptr %735
    store i64 %738, ptr %737
    %739 = const i64 16
    %740 = gep i8, ptr %487, %739
    %741 = const i64 16
    %742 = gep i8, ptr %492, %741
    %743 = load i64, ptr %740
    store i64 %743, ptr %742
    %744 = const i64 24
    %745 = gep i8, ptr %487, %744
    %746 = const i64 24
    %747 = gep i8, ptr %492, %746
    %748 = load i64, ptr %745
    store i64 %748, ptr %747
    %749 = const i64 32
    %750 = gep i8, ptr %487, %749
    %751 = const i64 32
    %752 = gep i8, ptr %492, %751
    %753 = load i64, ptr %750
    store i64 %753, ptr %752
    call @func.83(%493, %730)
    br bb34(%93, %94, %95, %96, %97)
bb34(%98: u64, %99: u64, %100: u64, %101: u32, %102: u32):
    %754 = const bool false
    call @func.84(%491, %492, %493)
    br bb35(%98, %99, %100, %101, %102)
bb35(%103: u64, %104: u64, %105: u64, %106: u32, %107: u32):
    %755 = const bool false
    %756 = const bool true
    %757 = load i64, ptr %491
    store i64 %757, ptr %487
    %758 = const i64 8
    %759 = gep i8, ptr %491, %758
    %760 = const i64 8
    %761 = gep i8, ptr %487, %760
    %762 = load i64, ptr %759
    store i64 %762, ptr %761
    %763 = const i64 16
    %764 = gep i8, ptr %491, %763
    %765 = const i64 16
    %766 = gep i8, ptr %487, %765
    %767 = load i64, ptr %764
    store i64 %767, ptr %766
    %768 = const i64 24
    %769 = gep i8, ptr %491, %768
    %770 = const i64 24
    %771 = gep i8, ptr %487, %770
    %772 = load i64, ptr %769
    store i64 %772, ptr %771
    %773 = const i64 32
    %774 = gep i8, ptr %491, %773
    %775 = const i64 32
    %776 = gep i8, ptr %487, %775
    %777 = load i64, ptr %774
    store i64 %777, ptr %776
    %778 = const u32 1
    %779, %780 = add.overflow u32 %107, %778
    store u32 %779, ptr %494
    %781 = const i64 4
    %782 = gep i8, ptr %494, %781
    store bool %780, ptr %782
    %783 = const i64 4
    %784 = gep i8, ptr %494, %783
    %785 = load bool, ptr %784
    %786 = const bool false
    %787 = icmp eq bool %785, %786
    condbr %787, bb36(%103, %104, %105, %106), bb171
bb36(%108: u64, %109: u64, %110: u64, %111: u32):
    %788 = load u32, ptr %494
    br bb29(%108, %109, %110, %111, %788)
bb37(%112: u64, %113: u64, %114: u64, %115: u32):
    %789 = const u32 0
    br bb38(%112, %113, %114, %115, %789)
bb38(%116: u64, %117: u64, %118: u64, %119: u32, %120: u32):
    %790 = icmp ult u32 %120, %119
    condbr %790, bb39(%116, %117, %118, %119, %120), bb45(%116, %117, %118)
bb39(%121: u64, %122: u64, %123: u64, %124: u32, %125: u32):
    %791 = const u32 1
    %792, %793 = sub.overflow u32 %124, %791
    store u32 %792, ptr %495
    %794 = const i64 4
    %795 = gep i8, ptr %495, %794
    store bool %793, ptr %795
    %796 = const i64 4
    %797 = gep i8, ptr %495, %796
    %798 = load bool, ptr %797
    %799 = const bool false
    %800 = icmp eq bool %798, %799
    condbr %800, bb40(%121, %122, %123, %124, %125), bb171
bb40(%126: u64, %127: u64, %128: u64, %129: u32, %130: u32):
    %801 = load u32, ptr %495
    %802, %803 = sub.overflow u32 %801, %130
    store u32 %802, ptr %496
    %804 = const i64 4
    %805 = gep i8, ptr %496, %804
    store bool %803, ptr %805
    %806 = const i64 4
    %807 = gep i8, ptr %496, %806
    %808 = load bool, ptr %807
    %809 = const bool false
    %810 = icmp eq bool %808, %809
    condbr %810, bb41(%126, %127, %128, %129, %130), bb171
bb41(%131: u64, %132: u64, %133: u64, %134: u32, %135: u32):
    %811 = load u32, ptr %496
    %812 = const bool false
    %813 = const bool true
    %814 = load i64, ptr %487
    store i64 %814, ptr %498
    %815 = const i64 8
    %816 = gep i8, ptr %487, %815
    %817 = const i64 8
    %818 = gep i8, ptr %498, %817
    %819 = load i64, ptr %816
    store i64 %819, ptr %818
    %820 = const i64 16
    %821 = gep i8, ptr %487, %820
    %822 = const i64 16
    %823 = gep i8, ptr %498, %822
    %824 = load i64, ptr %821
    store i64 %824, ptr %823
    %825 = const i64 24
    %826 = gep i8, ptr %487, %825
    %827 = const i64 24
    %828 = gep i8, ptr %498, %827
    %829 = load i64, ptr %826
    store i64 %829, ptr %828
    %830 = const i64 32
    %831 = gep i8, ptr %487, %830
    %832 = const i64 32
    %833 = gep i8, ptr %498, %832
    %834 = load i64, ptr %831
    store i64 %834, ptr %833
    call @func.83(%499, %811)
    br bb42(%131, %132, %133, %134, %135)
bb42(%136: u64, %137: u64, %138: u64, %139: u32, %140: u32):
    %835 = const bool false
    call @func.84(%497, %498, %499)
    br bb43(%136, %137, %138, %139, %140)
bb43(%141: u64, %142: u64, %143: u64, %144: u32, %145: u32):
    %836 = const bool false
    %837 = const bool true
    %838 = load i64, ptr %497
    store i64 %838, ptr %487
    %839 = const i64 8
    %840 = gep i8, ptr %497, %839
    %841 = const i64 8
    %842 = gep i8, ptr %487, %841
    %843 = load i64, ptr %840
    store i64 %843, ptr %842
    %844 = const i64 16
    %845 = gep i8, ptr %497, %844
    %846 = const i64 16
    %847 = gep i8, ptr %487, %846
    %848 = load i64, ptr %845
    store i64 %848, ptr %847
    %849 = const i64 24
    %850 = gep i8, ptr %497, %849
    %851 = const i64 24
    %852 = gep i8, ptr %487, %851
    %853 = load i64, ptr %850
    store i64 %853, ptr %852
    %854 = const i64 32
    %855 = gep i8, ptr %497, %854
    %856 = const i64 32
    %857 = gep i8, ptr %487, %856
    %858 = load i64, ptr %855
    store i64 %858, ptr %857
    %859 = const u32 1
    %860, %861 = add.overflow u32 %145, %859
    store u32 %860, ptr %500
    %862 = const i64 4
    %863 = gep i8, ptr %500, %862
    store bool %861, ptr %863
    %864 = const i64 4
    %865 = gep i8, ptr %500, %864
    %866 = load bool, ptr %865
    %867 = const bool false
    %868 = icmp eq bool %866, %867
    condbr %868, bb44(%141, %142, %143, %144), bb171
bb44(%146: u64, %147: u64, %148: u64, %149: u32):
    %869 = load u32, ptr %500
    br bb38(%146, %147, %148, %149, %869)
bb45(%150: u64, %151: u64, %152: u64):
    call @func.85(%502)
    br bb46(%150, %151, %152)
bb46(%153: u64, %154: u64, %155: u64):
    %870 = const bool false
    %871 = load i64, ptr %487
    store i64 %871, ptr %503
    %872 = const i64 8
    %873 = gep i8, ptr %487, %872
    %874 = const i64 8
    %875 = gep i8, ptr %503, %874
    %876 = load i64, ptr %873
    store i64 %876, ptr %875
    %877 = const i64 16
    %878 = gep i8, ptr %487, %877
    %879 = const i64 16
    %880 = gep i8, ptr %503, %879
    %881 = load i64, ptr %878
    store i64 %881, ptr %880
    %882 = const i64 24
    %883 = gep i8, ptr %487, %882
    %884 = const i64 24
    %885 = gep i8, ptr %503, %884
    %886 = load i64, ptr %883
    store i64 %886, ptr %885
    %887 = const i64 32
    %888 = gep i8, ptr %487, %887
    %889 = const i64 32
    %890 = gep i8, ptr %503, %889
    %891 = load i64, ptr %888
    store i64 %891, ptr %890
    %892 = const bool false
    %893 = load i64, ptr %484
    store i64 %893, ptr %504
    %894 = const i64 8
    %895 = gep i8, ptr %484, %894
    %896 = const i64 8
    %897 = gep i8, ptr %504, %896
    %898 = load i64, ptr %895
    store i64 %898, ptr %897
    %899 = const i64 16
    %900 = gep i8, ptr %484, %899
    %901 = const i64 16
    %902 = gep i8, ptr %504, %901
    %903 = load i64, ptr %900
    store i64 %903, ptr %902
    %904 = const i64 24
    %905 = gep i8, ptr %484, %904
    %906 = const i64 24
    %907 = gep i8, ptr %504, %906
    %908 = load i64, ptr %905
    store i64 %908, ptr %907
    %909 = const i64 32
    %910 = gep i8, ptr %484, %909
    %911 = const i64 32
    %912 = gep i8, ptr %504, %911
    %913 = load i64, ptr %910
    store i64 %913, ptr %912
    call @func.86(%501, %502, %503, %504)
    br bb47(%153, %154, %155)
bb47(%156: u64, %157: u64, %158: u64):
    %914 = const bool true
    %915 = load i64, ptr %501
    store i64 %915, ptr %484
    %916 = const i64 8
    %917 = gep i8, ptr %501, %916
    %918 = const i64 8
    %919 = gep i8, ptr %484, %918
    %920 = load i64, ptr %917
    store i64 %920, ptr %919
    %921 = const i64 16
    %922 = gep i8, ptr %501, %921
    %923 = const i64 16
    %924 = gep i8, ptr %484, %923
    %925 = load i64, ptr %922
    store i64 %925, ptr %924
    %926 = const i64 24
    %927 = gep i8, ptr %501, %926
    %928 = const i64 24
    %929 = gep i8, ptr %484, %928
    %930 = load i64, ptr %927
    store i64 %930, ptr %929
    %931 = const i64 32
    %932 = gep i8, ptr %501, %931
    %933 = const i64 32
    %934 = gep i8, ptr %484, %933
    %935 = load i64, ptr %932
    store i64 %935, ptr %934
    %936 = call @func.35(%483)
    br bb163(%156, %157, %158, %936)
bb48(%159: u64, %160: u64, %161: u64, %162: u64):
    %937 = const u64 0
    %938 = icmp ugt u64 %162, %937
    condbr %938, bb49(%159, %160, %161, %162), bb54(%159, %160, %161)
bb49(%163: u64, %164: u64, %165: u64, %166: u64):
    %939 = const u64 1
    %940, %941 = sub.overflow u64 %166, %939
    store u64 %940, ptr %505
    %942 = const i64 8
    %943 = gep i8, ptr %505, %942
    store bool %941, ptr %943
    %944 = const i64 8
    %945 = gep i8, ptr %505, %944
    %946 = load bool, ptr %945
    %947 = const bool false
    %948 = icmp eq bool %946, %947
    condbr %948, bb50(%163, %164, %165), bb171
bb50(%167: u64, %168: u64, %169: u64):
    %949 = load u64, ptr %505
    %950 = call @func.36(%483, %949)
    store ptr %950, ptr %506
    br bb51(%167, %168, %169, %949)
bb51(%170: u64, %171: u64, %172: u64, %173: u64):
    %951 = load ptr, ptr %506
    %952 = load ptr, ptr %506
    %953 = const i64 8
    %954 = gep i8, ptr %952, %953
    %955 = load i8, ptr %951
    store i8 %955, ptr %508
    %956 = const i64 1
    %957 = gep i8, ptr %951, %956
    %958 = const i64 1
    %959 = gep i8, ptr %508, %958
    %960 = load i8, ptr %957
    store i8 %960, ptr %959
    call @func.78(%509, %954)
    br bb52(%170, %171, %172, %173)
bb52(%174: u64, %175: u64, %176: u64, %177: u64):
    %961 = const bool false
    %962 = load i64, ptr %484
    store i64 %962, ptr %510
    %963 = const i64 8
    %964 = gep i8, ptr %484, %963
    %965 = const i64 8
    %966 = gep i8, ptr %510, %965
    %967 = load i64, ptr %964
    store i64 %967, ptr %966
    %968 = const i64 16
    %969 = gep i8, ptr %484, %968
    %970 = const i64 16
    %971 = gep i8, ptr %510, %970
    %972 = load i64, ptr %969
    store i64 %972, ptr %971
    %973 = const i64 24
    %974 = gep i8, ptr %484, %973
    %975 = const i64 24
    %976 = gep i8, ptr %510, %975
    %977 = load i64, ptr %974
    store i64 %977, ptr %976
    %978 = const i64 32
    %979 = gep i8, ptr %484, %978
    %980 = const i64 32
    %981 = gep i8, ptr %510, %980
    %982 = load i64, ptr %979
    store i64 %982, ptr %981
    call @func.86(%507, %508, %509, %510)
    br bb53(%174, %175, %176, %177)
bb53(%178: u64, %179: u64, %180: u64, %181: u64):
    %983 = const bool true
    %984 = load i64, ptr %507
    store i64 %984, ptr %484
    %985 = const i64 8
    %986 = gep i8, ptr %507, %985
    %987 = const i64 8
    %988 = gep i8, ptr %484, %987
    %989 = load i64, ptr %986
    store i64 %989, ptr %988
    %990 = const i64 16
    %991 = gep i8, ptr %507, %990
    %992 = const i64 16
    %993 = gep i8, ptr %484, %992
    %994 = load i64, ptr %991
    store i64 %994, ptr %993
    %995 = const i64 24
    %996 = gep i8, ptr %507, %995
    %997 = const i64 24
    %998 = gep i8, ptr %484, %997
    %999 = load i64, ptr %996
    store i64 %999, ptr %998
    %1000 = const i64 32
    %1001 = gep i8, ptr %507, %1000
    %1002 = const i64 32
    %1003 = gep i8, ptr %484, %1002
    %1004 = load i64, ptr %1001
    store i64 %1004, ptr %1003
    br bb48(%178, %179, %180, %181)
bb54(%182: u64, %183: u64, %184: u64):
    %1005 = const bool false
    %1006 = load i64, ptr %484
    store i64 %1006, ptr %511
    %1007 = const i64 8
    %1008 = gep i8, ptr %484, %1007
    %1009 = const i64 8
    %1010 = gep i8, ptr %511, %1009
    %1011 = load i64, ptr %1008
    store i64 %1011, ptr %1010
    %1012 = const i64 16
    %1013 = gep i8, ptr %484, %1012
    %1014 = const i64 16
    %1015 = gep i8, ptr %511, %1014
    %1016 = load i64, ptr %1013
    store i64 %1016, ptr %1015
    %1017 = const i64 24
    %1018 = gep i8, ptr %484, %1017
    %1019 = const i64 24
    %1020 = gep i8, ptr %511, %1019
    %1021 = load i64, ptr %1018
    store i64 %1021, ptr %1020
    %1022 = const i64 32
    %1023 = gep i8, ptr %484, %1022
    %1024 = const i64 32
    %1025 = gep i8, ptr %511, %1024
    %1026 = load i64, ptr %1023
    store i64 %1026, ptr %1025
    call @func.37(%480, %511)
    br bb55(%182, %183, %184)
bb55(%185: u64, %186: u64, %187: u64):
    %1027 = const u64 1
    %1028, %1029 = add.overflow u64 %187, %1027
    store u64 %1028, ptr %512
    %1030 = const i64 8
    %1031 = gep i8, ptr %512, %1030
    store bool %1029, ptr %1031
    %1032 = const i64 8
    %1033 = gep i8, ptr %512, %1032
    %1034 = load bool, ptr %1033
    %1035 = const bool false
    %1036 = icmp eq bool %1034, %1035
    condbr %1036, bb56(%185, %186), bb171
bb56(%188: u64, %189: u64):
    %1037 = load u64, ptr %512
    %1038 = const bool false
    %1039 = const bool false
    br bb57(%188, %189, %1037)
bb57(%190: u64, %191: u64, %192: u64):
    br bb19(%190, %191, %192)
bb58(%193: u64, %194: u64):
    %1040 = const i64 0
    store i64 %1040, ptr %513
    %1041 = const u64 0
    br bb59(%193, %194, %1041)
bb59(%195: u64, %196: u64, %197: u64):
    %1042 = const i64 8
    %1043 = gep i8, ptr %8, %1042
    %1044 = load u64, ptr %1043
    %1045 = icmp ult u64 %197, %1044
    condbr %1045, bb60(%195, %196, %197), bb66(%195, %196)
bb60(%198: u64, %199: u64, %200: u64):
    %1046 = const i64 8
    %1047 = gep i8, ptr %8, %1046
    %1048 = load u64, ptr %1047
    %1049 = icmp ult u64 %200, %1048
    condbr %1049, bb61(%198, %199, %200, %200), bb171
bb61(%201: u64, %202: u64, %203: u64, %204: u64):
    %1050 = load ptr, ptr %8
    %1051 = const u64 72
    %1052 = mul u64 %204, %1051
    %1053 = gep i8, ptr %1050, %1052
    %1054 = const i64 64
    %1055 = gep i8, ptr %1053, %1054
    store ptr %1055, ptr %514
    %1056 = call @func.38(%514, %467)
    br bb62(%201, %202, %203, %1056)
bb62(%205: u64, %206: u64, %207: u64, %208: bool):
    condbr %208, bb63(%205, %206, %207), bb64(%205, %206, %207)
bb63(%209: u64, %210: u64, %211: u64):
    %1057 = const i64 8
    %1058 = gep i8, ptr %515, %1057
    store u64 %211, ptr %1058
    %1059 = const i64 1
    store i64 %1059, ptr %515
    %1060 = load i64, ptr %515
    store i64 %1060, ptr %513
    %1061 = const i64 8
    %1062 = gep i8, ptr %515, %1061
    %1063 = const i64 8
    %1064 = gep i8, ptr %513, %1063
    %1065 = load i64, ptr %1062
    store i64 %1065, ptr %1064
    br bb66(%209, %210)
bb64(%212: u64, %213: u64, %214: u64):
    %1066 = const u64 1
    %1067, %1068 = add.overflow u64 %214, %1066
    store u64 %1067, ptr %516
    %1069 = const i64 8
    %1070 = gep i8, ptr %516, %1069
    store bool %1068, ptr %1070
    %1071 = const i64 8
    %1072 = gep i8, ptr %516, %1071
    %1073 = load bool, ptr %1072
    %1074 = const bool false
    %1075 = icmp eq bool %1073, %1074
    condbr %1075, bb65(%212, %213), bb171
bb65(%215: u64, %216: u64):
    %1076 = load u64, ptr %516
    br bb59(%215, %216, %1076)
bb66(%217: u64, %218: u64):
    %1077 = load i64, ptr %513
    switch %1077 [ 0: bb67(%217, %218) 1: bb68(%217, %218) default: bb1 ]
bb67(%219: u64, %220: u64):
    %1078 = const u64 0
    br bb69(%219, %220, %1078)
bb68(%221: u64, %222: u64):
    %1079 = const i64 8
    %1080 = gep i8, ptr %513, %1079
    %1081 = load u64, ptr %1080
    br bb69(%221, %222, %1081)
bb69(%223: u64, %224: u64, %225: u64):
    call @func.39(%517)
    br bb70(%223, %224, %225)
bb70(%226: u64, %227: u64, %228: u64):
    %1082 = const u64 0
    br bb71(%226, %227, %228, %1082)
bb71(%229: u64, %230: u64, %231: u64, %232: u64):
    %1083 = const i64 8
    %1084 = gep i8, ptr %7, %1083
    %1085 = load u64, ptr %1084
    %1086 = icmp ult u64 %232, %1085
    condbr %1086, bb72(%229, %230, %231, %232), bb85(%229, %230, %231)
bb72(%233: u64, %234: u64, %235: u64, %236: u64):
    %1087 = const i64 8
    %1088 = gep i8, ptr %7, %1087
    %1089 = load u64, ptr %1088
    %1090 = icmp ult u64 %236, %1089
    condbr %1090, bb73(%233, %234, %235, %236, %236), bb171
bb73(%237: u64, %238: u64, %239: u64, %240: u64, %241: u64):
    %1091 = load ptr, ptr %7
    %1092 = const u64 80
    %1093 = mul u64 %241, %1092
    %1094 = gep i8, ptr %1091, %1093
    store ptr %1094, ptr %518
    %1095 = load ptr, ptr %518
    %1096 = const i64 72
    %1097 = gep i8, ptr %1095, %1096
    %1098 = load ptr, ptr %518
    %1099 = const i64 76
    %1100 = gep i8, ptr %1098, %1099
    %1101 = load u32, ptr %1100
    %1102 = load ptr, ptr %518
    %1103 = load ptr, ptr %518
    %1104 = const i64 24
    %1105 = gep i8, ptr %1103, %1104
    %1106 = load ptr, ptr %518
    %1107 = const i64 48
    %1108 = gep i8, ptr %1106, %1107
    %1109 = call @func.90(%1097, %8)
    br bb74(%237, %238, %239, %240, %1097, %1101, %1102, %1105, %1108, %1109)
bb74(%242: u64, %243: u64, %244: u64, %245: u64, %246: ptr, %247: u32, %248: ptr, %249: ptr, %250: ptr, %251: u64):
    call @func.91(%519, %246, %8)
    br bb75(%242, %243, %244, %245, %246, %247, %248, %249, %250, %251)
bb75(%252: u64, %253: u64, %254: u64, %255: u64, %256: ptr, %257: u32, %258: ptr, %259: ptr, %260: ptr, %261: u64):
    %1110 = load i8, ptr %519
    %1111 = const i8 10
    %1112 = icmp eq i8 %1110, %1111
    %1113 = const i64 0
    %1114 = const i64 1
    %1115 = select i64 %1112, %1113, %1114
    switch %1115 [ 0: bb76(%252, %253, %254, %255, %256, %257, %258, %259, %260, %261) 1: bb77(%252, %253, %254, %255) default: bb1 ]
bb76(%262: u64, %263: u64, %264: u64, %265: u64, %266: ptr, %267: u32, %268: ptr, %269: ptr, %270: ptr, %271: u64):
    call @func.40(%524, %268)
    br bb80(%262, %263, %264, %265, %266, %267, %269, %270, %271)
bb77(%272: u64, %273: u64, %274: u64, %275: u64):
    %1116 = load i64, ptr %519
    store i64 %1116, ptr %520
    %1117 = const i64 8
    %1118 = gep i8, ptr %519, %1117
    %1119 = const i64 8
    %1120 = gep i8, ptr %520, %1119
    %1121 = load i64, ptr %1118
    store i64 %1121, ptr %1120
    %1122 = const i64 16
    %1123 = gep i8, ptr %519, %1122
    %1124 = const i64 16
    %1125 = gep i8, ptr %520, %1124
    %1126 = load i64, ptr %1123
    store i64 %1126, ptr %1125
    %1127 = const i64 24
    %1128 = gep i8, ptr %519, %1127
    %1129 = const i64 24
    %1130 = gep i8, ptr %520, %1129
    %1131 = load i64, ptr %1128
    store i64 %1131, ptr %1130
    %1132 = const i64 32
    %1133 = gep i8, ptr %519, %1132
    %1134 = const i64 32
    %1135 = gep i8, ptr %520, %1134
    %1136 = load i64, ptr %1133
    store i64 %1136, ptr %1135
    %1137 = const i64 40
    %1138 = gep i8, ptr %519, %1137
    %1139 = const i64 40
    %1140 = gep i8, ptr %520, %1139
    %1141 = load i64, ptr %1138
    store i64 %1141, ptr %1140
    %1142 = const i64 48
    %1143 = gep i8, ptr %519, %1142
    %1144 = const i64 48
    %1145 = gep i8, ptr %520, %1144
    %1146 = load i64, ptr %1143
    store i64 %1146, ptr %1145
    %1147 = const i64 56
    %1148 = gep i8, ptr %519, %1147
    %1149 = const i64 56
    %1150 = gep i8, ptr %520, %1149
    %1151 = load i64, ptr %1148
    store i64 %1151, ptr %1150
    %1152 = const i64 64
    %1153 = gep i8, ptr %519, %1152
    %1154 = const i64 64
    %1155 = gep i8, ptr %520, %1154
    %1156 = load i64, ptr %1153
    store i64 %1156, ptr %1155
    %1157 = const i64 72
    %1158 = gep i8, ptr %519, %1157
    %1159 = const i64 72
    %1160 = gep i8, ptr %520, %1159
    %1161 = load i64, ptr %1158
    store i64 %1161, ptr %1160
    %1162 = const u32 0
    call @func.83(%522, %1162)
    br bb78(%272, %273, %274, %275, %517)
bb78(%276: u64, %277: u64, %278: u64, %279: u64, %280: ptr):
    %1163 = load i64, ptr %522
    store i64 %1163, ptr %521
    %1164 = const i64 8
    %1165 = gep i8, ptr %522, %1164
    %1166 = const i64 8
    %1167 = gep i8, ptr %521, %1166
    %1168 = load i64, ptr %1165
    store i64 %1168, ptr %1167
    %1169 = const i64 16
    %1170 = gep i8, ptr %522, %1169
    %1171 = const i64 16
    %1172 = gep i8, ptr %521, %1171
    %1173 = load i64, ptr %1170
    store i64 %1173, ptr %1172
    %1174 = const i64 24
    %1175 = gep i8, ptr %522, %1174
    %1176 = const i64 24
    %1177 = gep i8, ptr %521, %1176
    %1178 = load i64, ptr %1175
    store i64 %1178, ptr %1177
    %1179 = const i64 32
    %1180 = gep i8, ptr %522, %1179
    %1181 = const i64 32
    %1182 = gep i8, ptr %521, %1181
    %1183 = load i64, ptr %1180
    store i64 %1183, ptr %1182
    %1184 = const bool true
    %1185 = const i64 40
    %1186 = gep i8, ptr %521, %1185
    store bool %1184, ptr %1186
    call @func.41(%280, %521)
    br bb79(%276, %277, %278, %279)
bb79(%281: u64, %282: u64, %283: u64, %284: u64):
    br bb162(%281, %282, %283, %284)
bb80(%285: u64, %286: u64, %287: u64, %288: u64, %289: ptr, %290: u32, %291: ptr, %292: ptr, %293: u64):
    call @func.42(%525, %291)
    br bb81(%285, %286, %287, %288, %289, %290, %292, %293)
bb81(%294: u64, %295: u64, %296: u64, %297: u64, %298: ptr, %299: u32, %300: ptr, %301: u64):
    call @func.42(%526, %300)
    br bb82(%294, %295, %296, %297, %298, %299, %301)
bb82(%302: u64, %303: u64, %304: u64, %305: u64, %306: ptr, %307: u32, %308: u64):
    %1187 = load ptr, ptr %467
    %1188 = load u32, ptr %468
    call @func.100(%523, %1187, %306, %307, %524, %525, %1188, %6, %526, %302, %308, %8)
    br bb83(%302, %303, %304, %305)
bb83(%309: u64, %310: u64, %311: u64, %312: u64):
    %1189 = load i64, ptr %523
    store i64 %1189, ptr %527
    %1190 = const i64 8
    %1191 = gep i8, ptr %523, %1190
    %1192 = const i64 8
    %1193 = gep i8, ptr %527, %1192
    %1194 = load i64, ptr %1191
    store i64 %1194, ptr %1193
    %1195 = const i64 16
    %1196 = gep i8, ptr %523, %1195
    %1197 = const i64 16
    %1198 = gep i8, ptr %527, %1197
    %1199 = load i64, ptr %1196
    store i64 %1199, ptr %1198
    %1200 = const i64 24
    %1201 = gep i8, ptr %523, %1200
    %1202 = const i64 24
    %1203 = gep i8, ptr %527, %1202
    %1204 = load i64, ptr %1201
    store i64 %1204, ptr %1203
    %1205 = const i64 32
    %1206 = gep i8, ptr %523, %1205
    %1207 = const i64 32
    %1208 = gep i8, ptr %527, %1207
    %1209 = load i64, ptr %1206
    store i64 %1209, ptr %1208
    %1210 = const bool false
    %1211 = const i64 40
    %1212 = gep i8, ptr %527, %1211
    store bool %1210, ptr %1212
    call @func.41(%517, %527)
    br bb164(%309, %310, %311, %312)
bb84(%313: u64, %314: u64, %315: u64):
    %1213 = load u64, ptr %528
    br bb71(%313, %314, %315, %1213)
bb85(%316: u64, %317: u64, %318: u64):
    %1214 = load u32, ptr %469
    %1215 = zext u32 %1214 to u64
    %1216, %1217 = add.overflow u64 %317, %1215
    store u64 %1216, ptr %529
    %1218 = const i64 8
    %1219 = gep i8, ptr %529, %1218
    store bool %1217, ptr %1219
    %1220 = const i64 8
    %1221 = gep i8, ptr %529, %1220
    %1222 = load bool, ptr %1221
    %1223 = const bool false
    %1224 = icmp eq bool %1222, %1223
    condbr %1224, bb86(%316, %317, %318), bb171
bb86(%319: u64, %320: u64, %321: u64):
    %1225 = load u64, ptr %529
    %1226 = const u64 1
    %1227, %1228 = add.overflow u64 %1225, %1226
    store u64 %1227, ptr %530
    %1229 = const i64 8
    %1230 = gep i8, ptr %530, %1229
    store bool %1228, ptr %1230
    %1231 = const i64 8
    %1232 = gep i8, ptr %530, %1231
    %1233 = load bool, ptr %1232
    %1234 = const bool false
    %1235 = icmp eq bool %1233, %1234
    condbr %1235, bb87(%319, %320, %321), bb171
bb87(%322: u64, %323: u64, %324: u64):
    %1236 = load u64, ptr %530
    %1237 = const u64 1
    %1238, %1239 = sub.overflow u64 %322, %1237
    store u64 %1238, ptr %531
    %1240 = const i64 8
    %1241 = gep i8, ptr %531, %1240
    store bool %1239, ptr %1241
    %1242 = const i64 8
    %1243 = gep i8, ptr %531, %1242
    %1244 = load bool, ptr %1243
    %1245 = const bool false
    %1246 = icmp eq bool %1244, %1245
    condbr %1246, bb88(%322, %323, %324, %1236), bb171
bb88(%325: u64, %326: u64, %327: u64, %328: u64):
    %1247 = load u64, ptr %531
    %1248, %1249 = sub.overflow u64 %1247, %327
    store u64 %1248, ptr %532
    %1250 = const i64 8
    %1251 = gep i8, ptr %532, %1250
    store bool %1249, ptr %1251
    %1252 = const i64 8
    %1253 = gep i8, ptr %532, %1252
    %1254 = load bool, ptr %1253
    %1255 = const bool false
    %1256 = icmp eq bool %1254, %1255
    condbr %1256, bb89(%325, %326, %328), bb171
bb89(%329: u64, %330: u64, %331: u64):
    %1257 = load u64, ptr %532
    %1258, %1259 = add.overflow u64 %331, %1257
    store u64 %1258, ptr %533
    %1260 = const i64 8
    %1261 = gep i8, ptr %533, %1260
    store bool %1259, ptr %1261
    %1262 = const i64 8
    %1263 = gep i8, ptr %533, %1262
    %1264 = load bool, ptr %1263
    %1265 = const bool false
    %1266 = icmp eq bool %1264, %1265
    condbr %1266, bb90(%329, %330), bb171
bb90(%332: u64, %333: u64):
    %1267 = load u64, ptr %533
    %1268 = call @func.103(%1267)
    br bb91(%332, %333, %1268)
bb91(%334: u64, %335: u64, %336: u32):
    call @func.83(%534, %336)
    br bb92(%334, %335)
bb92(%337: u64, %338: u64):
    %1269 = const bool true
    %1270 = const u32 0
    br bb93(%337, %338, %1270)
bb93(%339: u64, %340: u64, %341: u32):
    %1271 = load u32, ptr %469
    %1272 = icmp ult u32 %341, %1271
    condbr %1272, bb94(%339, %340, %341), bb100(%339, %340)
bb94(%342: u64, %343: u64, %344: u32):
    %1273 = load u32, ptr %469
    %1274 = zext u32 %1273 to u64
    %1275 = zext u32 %344 to u64
    %1276, %1277 = sub.overflow u64 %1274, %1275
    store u64 %1276, ptr %535
    %1278 = const i64 8
    %1279 = gep i8, ptr %535, %1278
    store bool %1277, ptr %1279
    %1280 = const i64 8
    %1281 = gep i8, ptr %535, %1280
    %1282 = load bool, ptr %1281
    %1283 = const bool false
    %1284 = icmp eq bool %1282, %1283
    condbr %1284, bb95(%342, %343, %344), bb171
bb95(%345: u64, %346: u64, %347: u32):
    %1285 = load u64, ptr %535
    %1286 = call @func.103(%1285)
    br bb96(%345, %346, %347, %1286)
bb96(%348: u64, %349: u64, %350: u32, %351: u32):
    %1287 = const bool false
    %1288 = const bool true
    %1289 = load i64, ptr %534
    store i64 %1289, ptr %537
    %1290 = const i64 8
    %1291 = gep i8, ptr %534, %1290
    %1292 = const i64 8
    %1293 = gep i8, ptr %537, %1292
    %1294 = load i64, ptr %1291
    store i64 %1294, ptr %1293
    %1295 = const i64 16
    %1296 = gep i8, ptr %534, %1295
    %1297 = const i64 16
    %1298 = gep i8, ptr %537, %1297
    %1299 = load i64, ptr %1296
    store i64 %1299, ptr %1298
    %1300 = const i64 24
    %1301 = gep i8, ptr %534, %1300
    %1302 = const i64 24
    %1303 = gep i8, ptr %537, %1302
    %1304 = load i64, ptr %1301
    store i64 %1304, ptr %1303
    %1305 = const i64 32
    %1306 = gep i8, ptr %534, %1305
    %1307 = const i64 32
    %1308 = gep i8, ptr %537, %1307
    %1309 = load i64, ptr %1306
    store i64 %1309, ptr %1308
    call @func.83(%538, %351)
    br bb97(%348, %349, %350)
bb97(%352: u64, %353: u64, %354: u32):
    %1310 = const bool false
    call @func.84(%536, %537, %538)
    br bb98(%352, %353, %354)
bb98(%355: u64, %356: u64, %357: u32):
    %1311 = const bool false
    %1312 = const bool true
    %1313 = load i64, ptr %536
    store i64 %1313, ptr %534
    %1314 = const i64 8
    %1315 = gep i8, ptr %536, %1314
    %1316 = const i64 8
    %1317 = gep i8, ptr %534, %1316
    %1318 = load i64, ptr %1315
    store i64 %1318, ptr %1317
    %1319 = const i64 16
    %1320 = gep i8, ptr %536, %1319
    %1321 = const i64 16
    %1322 = gep i8, ptr %534, %1321
    %1323 = load i64, ptr %1320
    store i64 %1323, ptr %1322
    %1324 = const i64 24
    %1325 = gep i8, ptr %536, %1324
    %1326 = const i64 24
    %1327 = gep i8, ptr %534, %1326
    %1328 = load i64, ptr %1325
    store i64 %1328, ptr %1327
    %1329 = const i64 32
    %1330 = gep i8, ptr %536, %1329
    %1331 = const i64 32
    %1332 = gep i8, ptr %534, %1331
    %1333 = load i64, ptr %1330
    store i64 %1333, ptr %1332
    %1334 = const u32 1
    %1335, %1336 = add.overflow u32 %357, %1334
    store u32 %1335, ptr %539
    %1337 = const i64 4
    %1338 = gep i8, ptr %539, %1337
    store bool %1336, ptr %1338
    %1339 = const i64 4
    %1340 = gep i8, ptr %539, %1339
    %1341 = load bool, ptr %1340
    %1342 = const bool false
    %1343 = icmp eq bool %1341, %1342
    condbr %1343, bb99(%355, %356), bb171
bb99(%358: u64, %359: u64):
    %1344 = load u32, ptr %539
    br bb93(%358, %359, %1344)
bb100(%360: u64, %361: u64):
    %1345 = const bool false
    %1346 = const bool true
    %1347 = load i64, ptr %534
    store i64 %1347, ptr %541
    %1348 = const i64 8
    %1349 = gep i8, ptr %534, %1348
    %1350 = const i64 8
    %1351 = gep i8, ptr %541, %1350
    %1352 = load i64, ptr %1349
    store i64 %1352, ptr %1351
    %1353 = const i64 16
    %1354 = gep i8, ptr %534, %1353
    %1355 = const i64 16
    %1356 = gep i8, ptr %541, %1355
    %1357 = load i64, ptr %1354
    store i64 %1357, ptr %1356
    %1358 = const i64 24
    %1359 = gep i8, ptr %534, %1358
    %1360 = const i64 24
    %1361 = gep i8, ptr %541, %1360
    %1362 = load i64, ptr %1359
    store i64 %1362, ptr %1361
    %1363 = const i64 32
    %1364 = gep i8, ptr %534, %1363
    %1365 = const i64 32
    %1366 = gep i8, ptr %541, %1365
    %1367 = load i64, ptr %1364
    store i64 %1367, ptr %1366
    %1368 = const u32 0
    call @func.83(%542, %1368)
    br bb101(%360, %361)
bb101(%362: u64, %363: u64):
    %1369 = const bool false
    call @func.84(%540, %541, %542)
    br bb102(%362, %363)
bb102(%364: u64, %365: u64):
    %1370 = const bool false
    %1371 = const bool true
    %1372 = load i64, ptr %540
    store i64 %1372, ptr %534
    %1373 = const i64 8
    %1374 = gep i8, ptr %540, %1373
    %1375 = const i64 8
    %1376 = gep i8, ptr %534, %1375
    %1377 = load i64, ptr %1374
    store i64 %1377, ptr %1376
    %1378 = const i64 16
    %1379 = gep i8, ptr %540, %1378
    %1380 = const i64 16
    %1381 = gep i8, ptr %534, %1380
    %1382 = load i64, ptr %1379
    store i64 %1382, ptr %1381
    %1383 = const i64 24
    %1384 = gep i8, ptr %540, %1383
    %1385 = const i64 24
    %1386 = gep i8, ptr %534, %1385
    %1387 = load i64, ptr %1384
    store i64 %1387, ptr %1386
    %1388 = const i64 32
    %1389 = gep i8, ptr %540, %1388
    %1390 = const i64 32
    %1391 = gep i8, ptr %534, %1390
    %1392 = load i64, ptr %1389
    store i64 %1392, ptr %1391
    %1393 = trunc u64 %365 to u32
    %1394 = load u32, ptr %469
    %1395, %1396 = add.overflow u32 %1394, %1393
    store u32 %1395, ptr %545
    %1397 = const i64 4
    %1398 = gep i8, ptr %545, %1397
    store bool %1396, ptr %1398
    %1399 = const i64 4
    %1400 = gep i8, ptr %545, %1399
    %1401 = load bool, ptr %1400
    %1402 = const bool false
    %1403 = icmp eq bool %1401, %1402
    condbr %1403, bb103(%364, %365, %479), bb171
bb103(%366: u64, %367: u64, %368: ptr):
    %1404 = load u32, ptr %545
    %1405 = trunc u64 %366 to u32
    %1406, %1407 = add.overflow u32 %1404, %1405
    store u32 %1406, ptr %546
    %1408 = const i64 4
    %1409 = gep i8, ptr %546, %1408
    store bool %1407, ptr %1409
    %1410 = const i64 4
    %1411 = gep i8, ptr %546, %1410
    %1412 = load bool, ptr %1411
    %1413 = const bool false
    %1414 = icmp eq bool %1412, %1413
    condbr %1414, bb104(%366, %367, %368), bb171
bb104(%369: u64, %370: u64, %371: ptr):
    %1415 = load u32, ptr %546
    store u32 %1415, ptr %544
    %1416 = const u32 0
    %1417 = const i64 4
    %1418 = gep i8, ptr %544, %1417
    store u32 %1416, ptr %1418
    %1419 = load u32, ptr %544
    %1420 = const i64 4
    %1421 = gep i8, ptr %544, %1420
    %1422 = load u32, ptr %1421
    call @func.104(%543, %371, %1419, %1422)
    br bb105(%369, %370)
bb105(%372: u64, %373: u64):
    %1423 = const bool true
    call @func.85(%548)
    br bb106(%372, %373)
bb106(%374: u64, %375: u64):
    %1424 = const bool false
    %1425 = load i64, ptr %543
    store i64 %1425, ptr %549
    %1426 = const i64 8
    %1427 = gep i8, ptr %543, %1426
    %1428 = const i64 8
    %1429 = gep i8, ptr %549, %1428
    %1430 = load i64, ptr %1427
    store i64 %1430, ptr %1429
    %1431 = const i64 16
    %1432 = gep i8, ptr %543, %1431
    %1433 = const i64 16
    %1434 = gep i8, ptr %549, %1433
    %1435 = load i64, ptr %1432
    store i64 %1435, ptr %1434
    %1436 = const i64 24
    %1437 = gep i8, ptr %543, %1436
    %1438 = const i64 24
    %1439 = gep i8, ptr %549, %1438
    %1440 = load i64, ptr %1437
    store i64 %1440, ptr %1439
    %1441 = const i64 32
    %1442 = gep i8, ptr %543, %1441
    %1443 = const i64 32
    %1444 = gep i8, ptr %549, %1443
    %1445 = load i64, ptr %1442
    store i64 %1445, ptr %1444
    %1446 = const bool false
    %1447 = load i64, ptr %534
    store i64 %1447, ptr %550
    %1448 = const i64 8
    %1449 = gep i8, ptr %534, %1448
    %1450 = const i64 8
    %1451 = gep i8, ptr %550, %1450
    %1452 = load i64, ptr %1449
    store i64 %1452, ptr %1451
    %1453 = const i64 16
    %1454 = gep i8, ptr %534, %1453
    %1455 = const i64 16
    %1456 = gep i8, ptr %550, %1455
    %1457 = load i64, ptr %1454
    store i64 %1457, ptr %1456
    %1458 = const i64 24
    %1459 = gep i8, ptr %534, %1458
    %1460 = const i64 24
    %1461 = gep i8, ptr %550, %1460
    %1462 = load i64, ptr %1459
    store i64 %1462, ptr %1461
    %1463 = const i64 32
    %1464 = gep i8, ptr %534, %1463
    %1465 = const i64 32
    %1466 = gep i8, ptr %550, %1465
    %1467 = load i64, ptr %1464
    store i64 %1467, ptr %1466
    call @func.86(%547, %548, %549, %550)
    br bb107(%374, %375)
bb107(%376: u64, %377: u64):
    %1468 = const bool true
    %1469 = load i64, ptr %547
    store i64 %1469, ptr %534
    %1470 = const i64 8
    %1471 = gep i8, ptr %547, %1470
    %1472 = const i64 8
    %1473 = gep i8, ptr %534, %1472
    %1474 = load i64, ptr %1471
    store i64 %1474, ptr %1473
    %1475 = const i64 16
    %1476 = gep i8, ptr %547, %1475
    %1477 = const i64 16
    %1478 = gep i8, ptr %534, %1477
    %1479 = load i64, ptr %1476
    store i64 %1479, ptr %1478
    %1480 = const i64 24
    %1481 = gep i8, ptr %547, %1480
    %1482 = const i64 24
    %1483 = gep i8, ptr %534, %1482
    %1484 = load i64, ptr %1481
    store i64 %1484, ptr %1483
    %1485 = const i64 32
    %1486 = gep i8, ptr %547, %1485
    %1487 = const i64 32
    %1488 = gep i8, ptr %534, %1487
    %1489 = load i64, ptr %1486
    store i64 %1489, ptr %1488
    %1490, %1491 = add.overflow u64 %377, %376
    store u64 %1490, ptr %551
    %1492 = const i64 8
    %1493 = gep i8, ptr %551, %1492
    store bool %1491, ptr %1493
    %1494 = const i64 8
    %1495 = gep i8, ptr %551, %1494
    %1496 = load bool, ptr %1495
    %1497 = const bool false
    %1498 = icmp eq bool %1496, %1497
    condbr %1498, bb108, bb171
bb108:
    %1499 = load u64, ptr %551
    %1500 = call @func.103(%1499)
    br bb109(%1500)
bb109(%378: u32):
    %1501 = call @func.35(%478)
    br bb165(%378, %1501)
bb110(%379: u32, %380: u64):
    %1502 = const u64 0
    %1503 = icmp ugt u64 %380, %1502
    condbr %1503, bb111(%379, %380), bb118
bb111(%381: u32, %382: u64):
    %1504 = const u64 1
    %1505, %1506 = sub.overflow u64 %382, %1504
    store u64 %1505, ptr %552
    %1507 = const i64 8
    %1508 = gep i8, ptr %552, %1507
    store bool %1506, ptr %1508
    %1509 = const i64 8
    %1510 = gep i8, ptr %552, %1509
    %1511 = load bool, ptr %1510
    %1512 = const bool false
    %1513 = icmp eq bool %1511, %1512
    condbr %1513, bb112(%381), bb171
bb112(%383: u32):
    %1514 = load u64, ptr %552
    %1515 = call @func.36(%478, %1514)
    store ptr %1515, ptr %553
    br bb113(%383, %1514, %1514)
bb113(%384: u32, %385: u64, %386: u64):
    %1516 = load ptr, ptr %553
    %1517 = load ptr, ptr %553
    %1518 = const i64 8
    %1519 = gep i8, ptr %1517, %1518
    %1520 = const u32 0
    %1521 = icmp ugt u32 %384, %1520
    condbr %1521, bb114(%384, %385, %386, %1516, %1519), bb115(%384, %385, %1516, %1519)
bb114(%387: u32, %388: u64, %389: u64, %390: ptr, %391: ptr):
    %1522 = trunc u64 %389 to u32
    call @func.105(%554, %391, %1522, %387)
    br bb166(%387, %388, %390)
bb115(%392: u32, %393: u64, %394: ptr, %395: ptr):
    call @func.78(%554, %395)
    br bb167(%392, %393, %394)
bb116(%396: u32, %397: u64, %398: ptr):
    %1523 = load i8, ptr %398
    store i8 %1523, ptr %556
    %1524 = const i64 1
    %1525 = gep i8, ptr %398, %1524
    %1526 = const i64 1
    %1527 = gep i8, ptr %556, %1526
    %1528 = load i8, ptr %1525
    store i8 %1528, ptr %1527
    %1529 = load i64, ptr %554
    store i64 %1529, ptr %557
    %1530 = const i64 8
    %1531 = gep i8, ptr %554, %1530
    %1532 = const i64 8
    %1533 = gep i8, ptr %557, %1532
    %1534 = load i64, ptr %1531
    store i64 %1534, ptr %1533
    %1535 = const i64 16
    %1536 = gep i8, ptr %554, %1535
    %1537 = const i64 16
    %1538 = gep i8, ptr %557, %1537
    %1539 = load i64, ptr %1536
    store i64 %1539, ptr %1538
    %1540 = const i64 24
    %1541 = gep i8, ptr %554, %1540
    %1542 = const i64 24
    %1543 = gep i8, ptr %557, %1542
    %1544 = load i64, ptr %1541
    store i64 %1544, ptr %1543
    %1545 = const i64 32
    %1546 = gep i8, ptr %554, %1545
    %1547 = const i64 32
    %1548 = gep i8, ptr %557, %1547
    %1549 = load i64, ptr %1546
    store i64 %1549, ptr %1548
    %1550 = const bool false
    %1551 = load i64, ptr %534
    store i64 %1551, ptr %558
    %1552 = const i64 8
    %1553 = gep i8, ptr %534, %1552
    %1554 = const i64 8
    %1555 = gep i8, ptr %558, %1554
    %1556 = load i64, ptr %1553
    store i64 %1556, ptr %1555
    %1557 = const i64 16
    %1558 = gep i8, ptr %534, %1557
    %1559 = const i64 16
    %1560 = gep i8, ptr %558, %1559
    %1561 = load i64, ptr %1558
    store i64 %1561, ptr %1560
    %1562 = const i64 24
    %1563 = gep i8, ptr %534, %1562
    %1564 = const i64 24
    %1565 = gep i8, ptr %558, %1564
    %1566 = load i64, ptr %1563
    store i64 %1566, ptr %1565
    %1567 = const i64 32
    %1568 = gep i8, ptr %534, %1567
    %1569 = const i64 32
    %1570 = gep i8, ptr %558, %1569
    %1571 = load i64, ptr %1568
    store i64 %1571, ptr %1570
    call @func.86(%555, %556, %557, %558)
    br bb117(%396, %397)
bb117(%399: u32, %400: u64):
    %1572 = const bool true
    %1573 = load i64, ptr %555
    store i64 %1573, ptr %534
    %1574 = const i64 8
    %1575 = gep i8, ptr %555, %1574
    %1576 = const i64 8
    %1577 = gep i8, ptr %534, %1576
    %1578 = load i64, ptr %1575
    store i64 %1578, ptr %1577
    %1579 = const i64 16
    %1580 = gep i8, ptr %555, %1579
    %1581 = const i64 16
    %1582 = gep i8, ptr %534, %1581
    %1583 = load i64, ptr %1580
    store i64 %1583, ptr %1582
    %1584 = const i64 24
    %1585 = gep i8, ptr %555, %1584
    %1586 = const i64 24
    %1587 = gep i8, ptr %534, %1586
    %1588 = load i64, ptr %1585
    store i64 %1588, ptr %1587
    %1589 = const i64 32
    %1590 = gep i8, ptr %555, %1589
    %1591 = const i64 32
    %1592 = gep i8, ptr %534, %1591
    %1593 = load i64, ptr %1590
    store i64 %1593, ptr %1592
    br bb110(%399, %400)
bb118:
    %1594 = call @func.43(%517)
    br bb168(%1594)
bb119(%401: u64):
    %1595 = const u64 0
    %1596 = icmp ugt u64 %401, %1595
    condbr %1596, bb120(%401), bb132
bb120(%402: u64):
    %1597 = const u64 1
    %1598, %1599 = sub.overflow u64 %402, %1597
    store u64 %1598, ptr %559
    %1600 = const i64 8
    %1601 = gep i8, ptr %559, %1600
    store bool %1599, ptr %1601
    %1602 = const i64 8
    %1603 = gep i8, ptr %559, %1602
    %1604 = load bool, ptr %1603
    %1605 = const bool false
    %1606 = icmp eq bool %1604, %1605
    condbr %1606, bb121, bb171
bb121:
    %1607 = load u64, ptr %559
    %1608 = call @func.44(%517, %1607)
    store ptr %1608, ptr %560
    br bb122(%1607, %1607)
bb122(%403: u64, %404: u64):
    %1609 = load ptr, ptr %560
    %1610 = load ptr, ptr %560
    %1611 = const i64 40
    %1612 = gep i8, ptr %1610, %1611
    %1613 = load bool, ptr %1612
    condbr %1613, bb124(%403, %1609), bb123(%403, %404, %1609)
bb123(%405: u64, %406: u64, %407: ptr):
    %1614 = const u64 0
    %1615 = icmp eq u64 %406, %1614
    condbr %1615, bb124(%405, %407), bb126(%405, %406, %407)
bb124(%408: u64, %409: ptr):
    call @func.78(%561, %409)
    br bb125(%408)
bb125(%410: u64):
    %1616 = const bool true
    br bb129(%410)
bb126(%411: u64, %412: u64, %413: ptr):
    %1617 = call @func.103(%412)
    br bb127(%411, %413, %1617)
bb127(%414: u64, %415: ptr, %416: u32):
    call @func.106(%561, %415, %416)
    br bb128(%414)
bb128(%417: u64):
    %1618 = const bool true
    br bb129(%417)
bb129(%418: u64):
    call @func.85(%563)
    br bb130(%418)
bb130(%419: u64):
    %1619 = const bool false
    %1620 = load i64, ptr %561
    store i64 %1620, ptr %564
    %1621 = const i64 8
    %1622 = gep i8, ptr %561, %1621
    %1623 = const i64 8
    %1624 = gep i8, ptr %564, %1623
    %1625 = load i64, ptr %1622
    store i64 %1625, ptr %1624
    %1626 = const i64 16
    %1627 = gep i8, ptr %561, %1626
    %1628 = const i64 16
    %1629 = gep i8, ptr %564, %1628
    %1630 = load i64, ptr %1627
    store i64 %1630, ptr %1629
    %1631 = const i64 24
    %1632 = gep i8, ptr %561, %1631
    %1633 = const i64 24
    %1634 = gep i8, ptr %564, %1633
    %1635 = load i64, ptr %1632
    store i64 %1635, ptr %1634
    %1636 = const i64 32
    %1637 = gep i8, ptr %561, %1636
    %1638 = const i64 32
    %1639 = gep i8, ptr %564, %1638
    %1640 = load i64, ptr %1637
    store i64 %1640, ptr %1639
    %1641 = const bool false
    %1642 = load i64, ptr %534
    store i64 %1642, ptr %565
    %1643 = const i64 8
    %1644 = gep i8, ptr %534, %1643
    %1645 = const i64 8
    %1646 = gep i8, ptr %565, %1645
    %1647 = load i64, ptr %1644
    store i64 %1647, ptr %1646
    %1648 = const i64 16
    %1649 = gep i8, ptr %534, %1648
    %1650 = const i64 16
    %1651 = gep i8, ptr %565, %1650
    %1652 = load i64, ptr %1649
    store i64 %1652, ptr %1651
    %1653 = const i64 24
    %1654 = gep i8, ptr %534, %1653
    %1655 = const i64 24
    %1656 = gep i8, ptr %565, %1655
    %1657 = load i64, ptr %1654
    store i64 %1657, ptr %1656
    %1658 = const i64 32
    %1659 = gep i8, ptr %534, %1658
    %1660 = const i64 32
    %1661 = gep i8, ptr %565, %1660
    %1662 = load i64, ptr %1659
    store i64 %1662, ptr %1661
    call @func.86(%562, %563, %564, %565)
    br bb131(%419)
bb131(%420: u64):
    %1663 = const bool true
    %1664 = load i64, ptr %562
    store i64 %1664, ptr %534
    %1665 = const i64 8
    %1666 = gep i8, ptr %562, %1665
    %1667 = const i64 8
    %1668 = gep i8, ptr %534, %1667
    %1669 = load i64, ptr %1666
    store i64 %1669, ptr %1668
    %1670 = const i64 16
    %1671 = gep i8, ptr %562, %1670
    %1672 = const i64 16
    %1673 = gep i8, ptr %534, %1672
    %1674 = load i64, ptr %1671
    store i64 %1674, ptr %1673
    %1675 = const i64 24
    %1676 = gep i8, ptr %562, %1675
    %1677 = const i64 24
    %1678 = gep i8, ptr %534, %1677
    %1679 = load i64, ptr %1676
    store i64 %1679, ptr %1678
    %1680 = const i64 32
    %1681 = gep i8, ptr %562, %1680
    %1682 = const i64 32
    %1683 = gep i8, ptr %534, %1682
    %1684 = load i64, ptr %1681
    store i64 %1684, ptr %1683
    %1685 = const bool false
    br bb119(%420)
bb132:
    %1686 = call @func.45(%480)
    br bb169(%1686)
bb133(%421: u64):
    %1687 = const u64 0
    %1688 = icmp ugt u64 %421, %1687
    condbr %1688, bb134(%421), bb145
bb134(%422: u64):
    %1689 = const u64 1
    %1690, %1691 = sub.overflow u64 %422, %1689
    store u64 %1690, ptr %566
    %1692 = const i64 8
    %1693 = gep i8, ptr %566, %1692
    store bool %1691, ptr %1693
    %1694 = const i64 8
    %1695 = gep i8, ptr %566, %1694
    %1696 = load bool, ptr %1695
    %1697 = const bool false
    %1698 = icmp eq bool %1696, %1697
    condbr %1698, bb135, bb171
bb135:
    %1699 = load u64, ptr %566
    %1700 = call @func.46(%480, %1699)
    br bb136(%1699, %1699, %1700)
bb136(%423: u64, %424: u64, %425: ptr):
    %1701 = const u64 0
    %1702 = icmp ugt u64 %424, %1701
    condbr %1702, bb137(%423, %424, %425), bb140(%423, %425)
bb137(%426: u64, %427: u64, %428: ptr):
    %1703 = call @func.103(%427)
    br bb138(%426, %428, %1703)
bb138(%429: u64, %430: ptr, %431: u32):
    call @func.106(%567, %430, %431)
    br bb139(%429)
bb139(%432: u64):
    %1704 = const bool true
    br bb142(%432)
bb140(%433: u64, %434: ptr):
    call @func.78(%567, %434)
    br bb141(%433)
bb141(%435: u64):
    %1705 = const bool true
    br bb142(%435)
bb142(%436: u64):
    call @func.107(%569)
    br bb143(%436)
bb143(%437: u64):
    %1706 = const bool false
    %1707 = load i64, ptr %567
    store i64 %1707, ptr %570
    %1708 = const i64 8
    %1709 = gep i8, ptr %567, %1708
    %1710 = const i64 8
    %1711 = gep i8, ptr %570, %1710
    %1712 = load i64, ptr %1709
    store i64 %1712, ptr %1711
    %1713 = const i64 16
    %1714 = gep i8, ptr %567, %1713
    %1715 = const i64 16
    %1716 = gep i8, ptr %570, %1715
    %1717 = load i64, ptr %1714
    store i64 %1717, ptr %1716
    %1718 = const i64 24
    %1719 = gep i8, ptr %567, %1718
    %1720 = const i64 24
    %1721 = gep i8, ptr %570, %1720
    %1722 = load i64, ptr %1719
    store i64 %1722, ptr %1721
    %1723 = const i64 32
    %1724 = gep i8, ptr %567, %1723
    %1725 = const i64 32
    %1726 = gep i8, ptr %570, %1725
    %1727 = load i64, ptr %1724
    store i64 %1727, ptr %1726
    %1728 = const bool false
    %1729 = load i64, ptr %534
    store i64 %1729, ptr %571
    %1730 = const i64 8
    %1731 = gep i8, ptr %534, %1730
    %1732 = const i64 8
    %1733 = gep i8, ptr %571, %1732
    %1734 = load i64, ptr %1731
    store i64 %1734, ptr %1733
    %1735 = const i64 16
    %1736 = gep i8, ptr %534, %1735
    %1737 = const i64 16
    %1738 = gep i8, ptr %571, %1737
    %1739 = load i64, ptr %1736
    store i64 %1739, ptr %1738
    %1740 = const i64 24
    %1741 = gep i8, ptr %534, %1740
    %1742 = const i64 24
    %1743 = gep i8, ptr %571, %1742
    %1744 = load i64, ptr %1741
    store i64 %1744, ptr %1743
    %1745 = const i64 32
    %1746 = gep i8, ptr %534, %1745
    %1747 = const i64 32
    %1748 = gep i8, ptr %571, %1747
    %1749 = load i64, ptr %1746
    store i64 %1749, ptr %1748
    call @func.86(%568, %569, %570, %571)
    br bb144(%437)
bb144(%438: u64):
    %1750 = const bool true
    %1751 = load i64, ptr %568
    store i64 %1751, ptr %534
    %1752 = const i64 8
    %1753 = gep i8, ptr %568, %1752
    %1754 = const i64 8
    %1755 = gep i8, ptr %534, %1754
    %1756 = load i64, ptr %1753
    store i64 %1756, ptr %1755
    %1757 = const i64 16
    %1758 = gep i8, ptr %568, %1757
    %1759 = const i64 16
    %1760 = gep i8, ptr %534, %1759
    %1761 = load i64, ptr %1758
    store i64 %1761, ptr %1760
    %1762 = const i64 24
    %1763 = gep i8, ptr %568, %1762
    %1764 = const i64 24
    %1765 = gep i8, ptr %534, %1764
    %1766 = load i64, ptr %1763
    store i64 %1766, ptr %1765
    %1767 = const i64 32
    %1768 = gep i8, ptr %568, %1767
    %1769 = const i64 32
    %1770 = gep i8, ptr %534, %1769
    %1771 = load i64, ptr %1768
    store i64 %1771, ptr %1770
    %1772 = const bool false
    br bb133(%438)
bb145:
    %1773 = call @func.35(%473)
    br bb170(%1773)
bb146(%439: u64):
    %1774 = const u64 0
    %1775 = icmp ugt u64 %439, %1774
    condbr %1775, bb147(%439), bb152
bb147(%440: u64):
    %1776 = const u64 1
    %1777, %1778 = sub.overflow u64 %440, %1776
    store u64 %1777, ptr %572
    %1779 = const i64 8
    %1780 = gep i8, ptr %572, %1779
    store bool %1778, ptr %1780
    %1781 = const i64 8
    %1782 = gep i8, ptr %572, %1781
    %1783 = load bool, ptr %1782
    %1784 = const bool false
    %1785 = icmp eq bool %1783, %1784
    condbr %1785, bb148, bb171
bb148:
    %1786 = load u64, ptr %572
    %1787 = call @func.36(%473, %1786)
    store ptr %1787, ptr %573
    br bb149(%1786)
bb149(%441: u64):
    %1788 = load ptr, ptr %573
    %1789 = load ptr, ptr %573
    %1790 = const i64 8
    %1791 = gep i8, ptr %1789, %1790
    %1792 = load i8, ptr %1788
    store i8 %1792, ptr %575
    %1793 = const i64 1
    %1794 = gep i8, ptr %1788, %1793
    %1795 = const i64 1
    %1796 = gep i8, ptr %575, %1795
    %1797 = load i8, ptr %1794
    store i8 %1797, ptr %1796
    call @func.78(%576, %1791)
    br bb150(%441)
bb150(%442: u64):
    %1798 = const bool false
    %1799 = load i64, ptr %534
    store i64 %1799, ptr %577
    %1800 = const i64 8
    %1801 = gep i8, ptr %534, %1800
    %1802 = const i64 8
    %1803 = gep i8, ptr %577, %1802
    %1804 = load i64, ptr %1801
    store i64 %1804, ptr %1803
    %1805 = const i64 16
    %1806 = gep i8, ptr %534, %1805
    %1807 = const i64 16
    %1808 = gep i8, ptr %577, %1807
    %1809 = load i64, ptr %1806
    store i64 %1809, ptr %1808
    %1810 = const i64 24
    %1811 = gep i8, ptr %534, %1810
    %1812 = const i64 24
    %1813 = gep i8, ptr %577, %1812
    %1814 = load i64, ptr %1811
    store i64 %1814, ptr %1813
    %1815 = const i64 32
    %1816 = gep i8, ptr %534, %1815
    %1817 = const i64 32
    %1818 = gep i8, ptr %577, %1817
    %1819 = load i64, ptr %1816
    store i64 %1819, ptr %1818
    call @func.86(%574, %575, %576, %577)
    br bb151(%442)
bb151(%443: u64):
    %1820 = const bool true
    %1821 = load i64, ptr %574
    store i64 %1821, ptr %534
    %1822 = const i64 8
    %1823 = gep i8, ptr %574, %1822
    %1824 = const i64 8
    %1825 = gep i8, ptr %534, %1824
    %1826 = load i64, ptr %1823
    store i64 %1826, ptr %1825
    %1827 = const i64 16
    %1828 = gep i8, ptr %574, %1827
    %1829 = const i64 16
    %1830 = gep i8, ptr %534, %1829
    %1831 = load i64, ptr %1828
    store i64 %1831, ptr %1830
    %1832 = const i64 24
    %1833 = gep i8, ptr %574, %1832
    %1834 = const i64 24
    %1835 = gep i8, ptr %534, %1834
    %1836 = load i64, ptr %1833
    store i64 %1836, ptr %1835
    %1837 = const i64 32
    %1838 = gep i8, ptr %574, %1837
    %1839 = const i64 32
    %1840 = gep i8, ptr %534, %1839
    %1841 = load i64, ptr %1838
    store i64 %1841, ptr %1840
    br bb146(%443)
bb152:
    %1842 = const bool true
    call @func.108(%578, %534, %1842)
    br bb153
bb153:
    br bb154
bb154:
    %1843 = const bool true
    %1844 = load i64, ptr %578
    store i64 %1844, ptr %534
    %1845 = const i64 8
    %1846 = gep i8, ptr %578, %1845
    %1847 = const i64 8
    %1848 = gep i8, ptr %534, %1847
    %1849 = load i64, ptr %1846
    store i64 %1849, ptr %1848
    %1850 = const i64 16
    %1851 = gep i8, ptr %578, %1850
    %1852 = const i64 16
    %1853 = gep i8, ptr %534, %1852
    %1854 = load i64, ptr %1851
    store i64 %1854, ptr %1853
    %1855 = const i64 24
    %1856 = gep i8, ptr %578, %1855
    %1857 = const i64 24
    %1858 = gep i8, ptr %534, %1857
    %1859 = load i64, ptr %1856
    store i64 %1859, ptr %1858
    %1860 = const i64 32
    %1861 = gep i8, ptr %578, %1860
    %1862 = const i64 32
    %1863 = gep i8, ptr %534, %1862
    %1864 = load i64, ptr %1861
    store i64 %1864, ptr %1863
    %1865 = const bool false
    %1866 = load i64, ptr %534
    store i64 %1866, ptr %0
    %1867 = const i64 8
    %1868 = gep i8, ptr %534, %1867
    %1869 = const i64 8
    %1870 = gep i8, ptr %0, %1869
    %1871 = load i64, ptr %1868
    store i64 %1871, ptr %1870
    %1872 = const i64 16
    %1873 = gep i8, ptr %534, %1872
    %1874 = const i64 16
    %1875 = gep i8, ptr %0, %1874
    %1876 = load i64, ptr %1873
    store i64 %1876, ptr %1875
    %1877 = const i64 24
    %1878 = gep i8, ptr %534, %1877
    %1879 = const i64 24
    %1880 = gep i8, ptr %0, %1879
    %1881 = load i64, ptr %1878
    store i64 %1881, ptr %1880
    %1882 = const i64 32
    %1883 = gep i8, ptr %534, %1882
    %1884 = const i64 32
    %1885 = gep i8, ptr %0, %1884
    %1886 = load i64, ptr %1883
    store i64 %1886, ptr %1885
    %1887 = const bool false
    %1888 = const bool false
    br bb155
bb155:
    br bb156
bb156:
    br bb157
bb157:
    br bb158
bb158:
    br bb159
bb159:
    br bb160
bb160:
    br bb161
bb161:
    ret
bb162(%444: u64, %445: u64, %446: u64, %447: u64):
    %1889 = const u64 1
    %1890, %1891 = add.overflow u64 %447, %1889
    store u64 %1890, ptr %528
    %1892 = const i64 8
    %1893 = gep i8, ptr %528, %1892
    store bool %1891, ptr %1893
    %1894 = const i64 8
    %1895 = gep i8, ptr %528, %1894
    %1896 = load bool, ptr %1895
    %1897 = const bool false
    %1898 = icmp eq bool %1896, %1897
    condbr %1898, bb84(%444, %445, %446), bb171
bb163(%448: u64, %449: u64, %450: u64, %451: u64):
    br bb48(%448, %449, %450, %451)
bb164(%452: u64, %453: u64, %454: u64, %455: u64):
    br bb162(%452, %453, %454, %455)
bb165(%456: u32, %457: u64):
    br bb110(%456, %457)
bb166(%458: u32, %459: u64, %460: ptr):
    br bb116(%458, %459, %460)
bb167(%461: u32, %462: u64, %463: ptr):
    br bb116(%461, %462, %463)
bb168(%464: u64):
    br bb119(%464)
bb169(%465: u64):
    br bb133(%465)
bb170(%466: u64):
    br bb146(%466)
bb171:
    unreachable
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice5LevelE3newBE_(functy.48) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice5LevelE4pushBH_(functy.49) {
}

fn @_RINvMNtCs2EYQwhfuABO_4core5sliceSNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4Expr3getjEBx_(functy.50) {
}

fn @_RNvXsa_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice5LevelENtNtCs2EYQwhfuABO_4core5clone5Clone5cloneBH_(functy.51) {
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprE3lenBG_(functy.52) {
}

fn @_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_(functy.53) {
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecTNtCs6RT0DENTjyC_27clean_mutual_recursor_slice10BinderDataNtBF_4ExprEE3newBF_(functy.54) {
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecTNtCs6RT0DENTjyC_27clean_mutual_recursor_slice10BinderDataNtBH_4ExprEE3lenBH_(functy.55) {
}

fn @_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecTNtCs6RT0DENTjyC_27clean_mutual_recursor_slice10BinderDataNtBI_4ExprEEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBI_(functy.56) {
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprE3newBE_(functy.57) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprE4pushBH_(functy.58) {
}

fn @build_recursor_rule_rhs(functy.59) {
bb0(%0: ptr, %1: ptr, %2: ptr, %3: u32, %4: u32, %5: u32, %6: u32, %7: ptr, %8: ptr, %9: u64, %10: u64, %11: ptr, %12: ptr, %13: ptr):
    %1714 = alloca (i64, i64), align 8
    %1715 = alloca (i64, i64), align 8
    %1716 = alloca (i64, i64), align 8
    %1717 = alloca (i64, i64), align 8
    %1718 = alloca (i64, i64), align 8
    %1719 = alloca (i64, i64), align 8
    %1720 = alloca (i64, i64, i64, i64, i64), align 8
    %1721 = alloca (i64, i64), align 8
    %1722 = alloca (i64, i64), align 8
    %1723 = alloca (i64, i64, i64, i64, i64), align 8
    %1724 = alloca (i64, i64, i64, i64, i64), align 8
    %1725 = alloca (i64, i64, i64, i64, i64), align 8
    %1726 = alloca (i64, i64), align 8
    %1727 = alloca (i64, i64, i64), align 8
    %1728 = alloca (i64, i64), align 8
    %1729 = alloca i32, align 4
    %1730 = alloca (i64, i64), align 8
    %1731 = alloca i64, align 8
    %1732 = alloca i32, align 4
    %1733 = alloca i64, align 8
    %1734 = alloca i64, align 8
    %1735 = alloca i64, align 8
    %1736 = alloca (i64, i64, i64, i64, i64), align 8
    %1737 = alloca i32, align 4
    %1738 = alloca (i64, i64, i64), align 8
    %1739 = alloca (i64, i64), align 8
    %1740 = alloca (i64, i64), align 8
    %1741 = alloca (i64, i64), align 8
    %1742 = alloca (i64, i64, i64, i64, i64), align 8
    %1743 = alloca (i64, i64, i64, i64, i64), align 8
    %1744 = alloca (i64, i64, i64, i64, i64), align 8
    %1745 = alloca (i64, i64), align 8
    %1746 = alloca (i64, i64), align 8
    %1747 = alloca (i64, i64), align 8
    %1748 = alloca (i64, i64), align 8
    %1749 = alloca (i64, i64), align 8
    %1750 = alloca (i64, i64), align 8
    %1751 = alloca (i64, i64, i64, i64, i64), align 8
    %1752 = alloca (i64, i64, i64, i64, i64), align 8
    %1753 = alloca (i64, i64, i64, i64, i64), align 8
    %1754 = alloca (i64, i64), align 8
    %1755 = alloca (i64, i64), align 8
    %1756 = alloca (i64, i64), align 8
    %1757 = alloca (i64, i64), align 8
    %1758 = alloca (i64, i64), align 8
    %1759 = alloca (i64, i64, i64, i64, i64), align 8
    %1760 = alloca (i64, i64, i64, i64, i64), align 8
    %1761 = alloca (i64, i64, i64, i64, i64), align 8
    %1762 = alloca (i64, i64), align 8
    %1763 = alloca i64, align 8
    %1764 = alloca (i64, i64, i64), align 8
    %1765 = alloca (i64, i64, i64, i64, i64), align 8
    %1766 = alloca (i64, i64, i64, i64, i64), align 8
    %1767 = alloca (i64, i64, i64, i64, i64), align 8
    %1768 = alloca (i64, i64), align 8
    %1769 = alloca (i64, i64, i64, i64, i64), align 8
    %1770 = alloca (i64, i64), align 8
    %1771 = alloca (i64, i64), align 8
    %1772 = alloca (i64, i64), align 8
    %1773 = alloca (i64, i64), align 8
    %1774 = alloca (i64, i64, i64, i64, i64), align 8
    %1775 = alloca (i64, i64, i64, i64, i64), align 8
    %1776 = alloca (i64, i64, i64, i64, i64), align 8
    %1777 = alloca (i64, i64, i64, i64, i64), align 8
    %1778 = alloca (i64, i64, i64, i64, i64), align 8
    %1779 = alloca (i64, i64, i64, i64, i64), align 8
    %1780 = alloca (i64, i64, i64), align 8
    %1781 = alloca i64, align 8
    %1782 = alloca (i64, i64), align 8
    %1783 = alloca i64, align 8
    %1784 = alloca (i64, i64, i64, i64, i64), align 8
    %1785 = alloca (i64, i64, i64, i64, i64), align 8
    %1786 = alloca (i8, i8), align 1
    %1787 = alloca (i64, i64, i64, i64, i64), align 8
    %1788 = alloca (i64, i64, i64, i64, i64), align 8
    %1789 = alloca (i64, i64, i64, i64, i64), align 8
    %1790 = alloca (i64, i64, i64, i64, i64), align 8
    %1791 = alloca (i64, i64), align 8
    %1792 = alloca (i64, i64, i64, i64, i64), align 8
    %1793 = alloca (i64, i64), align 8
    %1794 = alloca (i64, i64, i64, i64, i64), align 8
    %1795 = alloca (i64, i64, i64), align 8
    %1796 = alloca i64, align 8
    %1797 = alloca (i64, i64, i64, i64, i64), align 8
    %1798 = alloca (i64, i64, i64, i64, i64), align 8
    %1799 = alloca (i64, i64, i64, i64, i64), align 8
    %1800 = alloca (i64, i64), align 8
    %1801 = alloca (i64, i64, i64), align 8
    %1802 = alloca i64, align 8
    %1803 = alloca (i64, i64, i64, i64, i64), align 8
    %1804 = alloca (i64, i64, i64, i64, i64), align 8
    %1805 = alloca (i64, i64, i64, i64, i64), align 8
    %1806 = alloca (i64, i64), align 8
    %1807 = alloca (i64, i64, i64), align 8
    %1808 = alloca i64, align 8
    %1809 = alloca (i64, i64, i64, i64, i64), align 8
    %1810 = alloca (i64, i64, i64, i64, i64), align 8
    %1811 = alloca (i64, i64, i64, i64, i64), align 8
    %1812 = alloca (i64, i64), align 8
    %1813 = alloca (i64, i64, i64, i64, i64), align 8
    %1814 = alloca (i64, i64), align 8
    %1815 = alloca (i64, i64), align 8
    %1816 = alloca (i64, i64, i64, i64, i64), align 8
    %1817 = alloca i64, align 8
    %1818 = alloca (i64, i64, i64, i64, i64), align 8
    %1819 = alloca (i8, i8), align 1
    %1820 = alloca (i64, i64, i64, i64, i64), align 8
    %1821 = alloca (i64, i64, i64, i64, i64), align 8
    %1822 = alloca (i64, i64), align 8
    %1823 = alloca (i64, i64, i64, i64, i64), align 8
    %1824 = alloca (i8, i8), align 1
    %1825 = alloca (i64, i64, i64, i64, i64), align 8
    %1826 = alloca (i64, i64, i64, i64, i64), align 8
    %1827 = alloca (i64, i64), align 8
    %1828 = alloca (i64, i64, i64, i64, i64), align 8
    %1829 = alloca (i8, i8), align 1
    %1830 = alloca (i64, i64, i64, i64, i64), align 8
    %1831 = alloca (i64, i64, i64, i64, i64), align 8
    %1832 = alloca (i64, i64), align 8
    %1833 = alloca (i64, i64, i64, i64, i64), align 8
    %1834 = alloca (i8, i8), align 1
    %1835 = alloca (i64, i64, i64, i64, i64), align 8
    %1836 = alloca (i64, i64, i64, i64, i64), align 8
    %1837 = const bool false
    %1838 = const bool false
    %1839 = const bool false
    %1840 = const bool false
    %1841 = const bool false
    %1842 = const bool false
    %1843 = const bool false
    %1844 = const bool false
    %1845 = const bool false
    %1846 = const bool false
    %1847 = zext u32 %6 to u64
    %1848 = zext u32 %3 to u64
    %1849 = zext u32 %4 to u64
    %1850, %1851 = add.overflow u64 %1848, %1849
    store u64 %1850, ptr %1714
    %1852 = const i64 8
    %1853 = gep i8, ptr %1714, %1852
    store bool %1851, ptr %1853
    %1854 = const i64 8
    %1855 = gep i8, ptr %1714, %1854
    %1856 = load bool, ptr %1855
    %1857 = const bool false
    %1858 = icmp eq bool %1856, %1857
    condbr %1858, bb1(%1, %3, %5, %9, %10, %11, %1847, %1848, %1849), bb226
bb1(%14: ptr, %15: u32, %16: u32, %17: u64, %18: u64, %19: ptr, %20: u64, %21: u64, %22: u64):
    %1859 = load u64, ptr %1714
    %1860, %1861 = add.overflow u64 %1859, %17
    store u64 %1860, ptr %1715
    %1862 = const i64 8
    %1863 = gep i8, ptr %1715, %1862
    store bool %1861, ptr %1863
    %1864 = const i64 8
    %1865 = gep i8, ptr %1715, %1864
    %1866 = load bool, ptr %1865
    %1867 = const bool false
    %1868 = icmp eq bool %1866, %1867
    condbr %1868, bb2(%14, %15, %16, %17, %18, %19, %20, %21, %22), bb226
bb2(%23: ptr, %24: u32, %25: u32, %26: u64, %27: u64, %28: ptr, %29: u64, %30: u64, %31: u64):
    %1869 = load u64, ptr %1715
    %1870, %1871 = add.overflow u64 %1869, %29
    store u64 %1870, ptr %1716
    %1872 = const i64 8
    %1873 = gep i8, ptr %1716, %1872
    store bool %1871, ptr %1873
    %1874 = const i64 8
    %1875 = gep i8, ptr %1716, %1874
    %1876 = load bool, ptr %1875
    %1877 = const bool false
    %1878 = icmp eq bool %1876, %1877
    condbr %1878, bb3(%23, %24, %25, %26, %27, %28, %29, %30, %31), bb226
bb3(%32: ptr, %33: u32, %34: u32, %35: u64, %36: u64, %37: ptr, %38: u64, %39: u64, %40: u64):
    %1879 = load u64, ptr %1716
    %1880, %1881 = add.overflow u64 %38, %35
    store u64 %1880, ptr %1717
    %1882 = const i64 8
    %1883 = gep i8, ptr %1717, %1882
    store bool %1881, ptr %1883
    %1884 = const i64 8
    %1885 = gep i8, ptr %1717, %1884
    %1886 = load bool, ptr %1885
    %1887 = const bool false
    %1888 = icmp eq bool %1886, %1887
    condbr %1888, bb4(%32, %33, %34, %35, %36, %37, %38, %39, %40, %1879), bb226
bb4(%41: ptr, %42: u32, %43: u32, %44: u64, %45: u64, %46: ptr, %47: u64, %48: u64, %49: u64, %50: u64):
    %1889 = load u64, ptr %1717
    %1890 = const u64 1
    %1891, %1892 = sub.overflow u64 %1889, %1890
    store u64 %1891, ptr %1718
    %1893 = const i64 8
    %1894 = gep i8, ptr %1718, %1893
    store bool %1892, ptr %1894
    %1895 = const i64 8
    %1896 = gep i8, ptr %1718, %1895
    %1897 = load bool, ptr %1896
    %1898 = const bool false
    %1899 = icmp eq bool %1897, %1898
    condbr %1899, bb5(%41, %42, %43, %44, %45, %46, %47, %48, %49, %50), bb226
bb5(%51: ptr, %52: u32, %53: u32, %54: u64, %55: u64, %56: ptr, %57: u64, %58: u64, %59: u64, %60: u64):
    %1900 = load u64, ptr %1718
    %1901, %1902 = sub.overflow u64 %1900, %55
    store u64 %1901, ptr %1719
    %1903 = const i64 8
    %1904 = gep i8, ptr %1719, %1903
    store bool %1902, ptr %1904
    %1905 = const i64 8
    %1906 = gep i8, ptr %1719, %1905
    %1907 = load bool, ptr %1906
    %1908 = const bool false
    %1909 = icmp eq bool %1907, %1908
    condbr %1909, bb6(%51, %52, %53, %54, %56, %57, %58, %59, %60), bb226
bb6(%61: ptr, %62: u32, %63: u32, %64: u64, %65: ptr, %66: u64, %67: u64, %68: u64, %69: u64):
    %1910 = load u64, ptr %1719
    %1911 = call @func.103(%1910)
    br bb7(%61, %62, %63, %64, %65, %66, %67, %68, %69, %1911)
bb7(%70: ptr, %71: u32, %72: u32, %73: u64, %74: ptr, %75: u64, %76: u64, %77: u64, %78: u64, %79: u32):
    %1912 = const bool true
    call @func.83(%1720, %79)
    br bb8(%70, %71, %72, %73, %74, %75, %76, %77, %78)
bb8(%80: ptr, %81: u32, %82: u32, %83: u64, %84: ptr, %85: u64, %86: u64, %87: u64, %88: u64):
    %1913 = const u64 0
    br bb9(%80, %81, %82, %83, %84, %85, %86, %87, %88, %1913)
bb9(%89: ptr, %90: u32, %91: u32, %92: u64, %93: ptr, %94: u64, %95: u64, %96: u64, %97: u64, %98: u64):
    %1914 = icmp ult u64 %98, %94
    condbr %1914, bb10(%89, %90, %91, %92, %93, %94, %95, %96, %97, %98), bb17(%89, %90, %91, %92, %93, %94, %95, %96, %97)
bb10(%99: ptr, %100: u32, %101: u32, %102: u64, %103: ptr, %104: u64, %105: u64, %106: u64, %107: u64, %108: u64):
    %1915 = const u64 1
    %1916, %1917 = sub.overflow u64 %104, %1915
    store u64 %1916, ptr %1721
    %1918 = const i64 8
    %1919 = gep i8, ptr %1721, %1918
    store bool %1917, ptr %1919
    %1920 = const i64 8
    %1921 = gep i8, ptr %1721, %1920
    %1922 = load bool, ptr %1921
    %1923 = const bool false
    %1924 = icmp eq bool %1922, %1923
    condbr %1924, bb11(%99, %100, %101, %102, %103, %104, %105, %106, %107, %108), bb226
bb11(%109: ptr, %110: u32, %111: u32, %112: u64, %113: ptr, %114: u64, %115: u64, %116: u64, %117: u64, %118: u64):
    %1925 = load u64, ptr %1721
    %1926, %1927 = sub.overflow u64 %1925, %118
    store u64 %1926, ptr %1722
    %1928 = const i64 8
    %1929 = gep i8, ptr %1722, %1928
    store bool %1927, ptr %1929
    %1930 = const i64 8
    %1931 = gep i8, ptr %1722, %1930
    %1932 = load bool, ptr %1931
    %1933 = const bool false
    %1934 = icmp eq bool %1932, %1933
    condbr %1934, bb12(%109, %110, %111, %112, %113, %114, %115, %116, %117, %118), bb226
bb12(%119: ptr, %120: u32, %121: u32, %122: u64, %123: ptr, %124: u64, %125: u64, %126: u64, %127: u64, %128: u64):
    %1935 = load u64, ptr %1722
    %1936 = call @func.103(%1935)
    br bb13(%119, %120, %121, %122, %123, %124, %125, %126, %127, %128, %1936)
bb13(%129: ptr, %130: u32, %131: u32, %132: u64, %133: ptr, %134: u64, %135: u64, %136: u64, %137: u64, %138: u64, %139: u32):
    %1937 = const bool false
    %1938 = const bool true
    %1939 = load i64, ptr %1720
    store i64 %1939, ptr %1724
    %1940 = const i64 8
    %1941 = gep i8, ptr %1720, %1940
    %1942 = const i64 8
    %1943 = gep i8, ptr %1724, %1942
    %1944 = load i64, ptr %1941
    store i64 %1944, ptr %1943
    %1945 = const i64 16
    %1946 = gep i8, ptr %1720, %1945
    %1947 = const i64 16
    %1948 = gep i8, ptr %1724, %1947
    %1949 = load i64, ptr %1946
    store i64 %1949, ptr %1948
    %1950 = const i64 24
    %1951 = gep i8, ptr %1720, %1950
    %1952 = const i64 24
    %1953 = gep i8, ptr %1724, %1952
    %1954 = load i64, ptr %1951
    store i64 %1954, ptr %1953
    %1955 = const i64 32
    %1956 = gep i8, ptr %1720, %1955
    %1957 = const i64 32
    %1958 = gep i8, ptr %1724, %1957
    %1959 = load i64, ptr %1956
    store i64 %1959, ptr %1958
    call @func.83(%1725, %139)
    br bb14(%129, %130, %131, %132, %133, %134, %135, %136, %137, %138)
bb14(%140: ptr, %141: u32, %142: u32, %143: u64, %144: ptr, %145: u64, %146: u64, %147: u64, %148: u64, %149: u64):
    %1960 = const bool false
    call @func.84(%1723, %1724, %1725)
    br bb15(%140, %141, %142, %143, %144, %145, %146, %147, %148, %149)
bb15(%150: ptr, %151: u32, %152: u32, %153: u64, %154: ptr, %155: u64, %156: u64, %157: u64, %158: u64, %159: u64):
    %1961 = const bool false
    %1962 = const bool true
    %1963 = load i64, ptr %1723
    store i64 %1963, ptr %1720
    %1964 = const i64 8
    %1965 = gep i8, ptr %1723, %1964
    %1966 = const i64 8
    %1967 = gep i8, ptr %1720, %1966
    %1968 = load i64, ptr %1965
    store i64 %1968, ptr %1967
    %1969 = const i64 16
    %1970 = gep i8, ptr %1723, %1969
    %1971 = const i64 16
    %1972 = gep i8, ptr %1720, %1971
    %1973 = load i64, ptr %1970
    store i64 %1973, ptr %1972
    %1974 = const i64 24
    %1975 = gep i8, ptr %1723, %1974
    %1976 = const i64 24
    %1977 = gep i8, ptr %1720, %1976
    %1978 = load i64, ptr %1975
    store i64 %1978, ptr %1977
    %1979 = const i64 32
    %1980 = gep i8, ptr %1723, %1979
    %1981 = const i64 32
    %1982 = gep i8, ptr %1720, %1981
    %1983 = load i64, ptr %1980
    store i64 %1983, ptr %1982
    %1984 = const u64 1
    %1985, %1986 = add.overflow u64 %159, %1984
    store u64 %1985, ptr %1726
    %1987 = const i64 8
    %1988 = gep i8, ptr %1726, %1987
    store bool %1986, ptr %1988
    %1989 = const i64 8
    %1990 = gep i8, ptr %1726, %1989
    %1991 = load bool, ptr %1990
    %1992 = const bool false
    %1993 = icmp eq bool %1991, %1992
    condbr %1993, bb16(%150, %151, %152, %153, %154, %155, %156, %157, %158), bb226
bb16(%160: ptr, %161: u32, %162: u32, %163: u64, %164: ptr, %165: u64, %166: u64, %167: u64, %168: u64):
    %1994 = load u64, ptr %1726
    br bb9(%160, %161, %162, %163, %164, %165, %166, %167, %168, %1994)
bb17(%169: ptr, %170: u32, %171: u32, %172: u64, %173: ptr, %174: u64, %175: u64, %176: u64, %177: u64):
    call @func.48(%1727)
    br bb18(%169, %170, %171, %172, %173, %174, %175, %176, %177)
bb18(%178: ptr, %179: u32, %180: u32, %181: u64, %182: ptr, %183: u64, %184: u64, %185: u64, %186: u64):
    %1995 = const u64 0
    br bb19(%178, %179, %180, %181, %182, %183, %184, %185, %186, %1995)
bb19(%187: ptr, %188: u32, %189: u32, %190: u64, %191: ptr, %192: u64, %193: u64, %194: u64, %195: u64, %196: u64):
    %1996 = const i64 8
    %1997 = gep i8, ptr %2, %1996
    %1998 = load u64, ptr %1997
    %1999 = icmp ult u64 %196, %1998
    condbr %1999, bb20(%187, %188, %189, %190, %191, %192, %193, %194, %195, %196), bb24(%187, %188, %189, %190, %191, %192, %193, %194, %195)
bb20(%197: ptr, %198: u32, %199: u32, %200: u64, %201: ptr, %202: u64, %203: u64, %204: u64, %205: u64, %206: u64):
    %2000 = const i64 8
    %2001 = gep i8, ptr %2, %2000
    %2002 = load u64, ptr %2001
    %2003 = icmp ult u64 %206, %2002
    condbr %2003, bb21(%197, %198, %199, %200, %201, %202, %203, %204, %205, %206, %1727, %206), bb226
bb21(%207: ptr, %208: u32, %209: u32, %210: u64, %211: ptr, %212: u64, %213: u64, %214: u64, %215: u64, %216: u64, %217: ptr, %218: u64):
    %2004 = load ptr, ptr %2
    %2005 = const u64 4
    %2006 = mul u64 %218, %2005
    %2007 = gep i8, ptr %2004, %2006
    %2008 = load i32, ptr %2007
    store i32 %2008, ptr %1729
    %2009 = const i64 4
    %2010 = gep i8, ptr %1728, %2009
    %2011 = load i32, ptr %1729
    store i32 %2011, ptr %2010
    %2012 = const i32 2
    store i32 %2012, ptr %1728
    call @func.49(%217, %1728)
    br bb22(%207, %208, %209, %210, %211, %212, %213, %214, %215, %216)
bb22(%219: ptr, %220: u32, %221: u32, %222: u64, %223: ptr, %224: u64, %225: u64, %226: u64, %227: u64, %228: u64):
    %2013 = const u64 1
    %2014, %2015 = add.overflow u64 %228, %2013
    store u64 %2014, ptr %1730
    %2016 = const i64 8
    %2017 = gep i8, ptr %1730, %2016
    store bool %2015, ptr %2017
    %2018 = const i64 8
    %2019 = gep i8, ptr %1730, %2018
    %2020 = load bool, ptr %2019
    %2021 = const bool false
    %2022 = icmp eq bool %2020, %2021
    condbr %2022, bb23(%219, %220, %221, %222, %223, %224, %225, %226, %227), bb226
bb23(%229: ptr, %230: u32, %231: u32, %232: u64, %233: ptr, %234: u64, %235: u64, %236: u64, %237: u64):
    %2023 = load u64, ptr %1730
    br bb19(%229, %230, %231, %232, %233, %234, %235, %236, %237, %2023)
bb24(%238: ptr, %239: u32, %240: u32, %241: u64, %242: ptr, %243: u64, %244: u64, %245: u64, %246: u64):
    %2024 = const u64 0
    br bb25(%238, %239, %240, %241, %242, %243, %244, %245, %246, %2024)
bb25(%247: ptr, %248: u32, %249: u32, %250: u64, %251: ptr, %252: u64, %253: u64, %254: u64, %255: u64, %256: u64):
    %2025 = const i64 8
    %2026 = gep i8, ptr %7, %2025
    %2027 = load u64, ptr %2026
    %2028 = icmp ult u64 %256, %2027
    condbr %2028, bb26(%247, %248, %249, %250, %251, %252, %253, %254, %255, %256), bb120(%250, %251, %252, %253, %254)
bb26(%257: ptr, %258: u32, %259: u32, %260: u64, %261: ptr, %262: u64, %263: u64, %264: u64, %265: u64, %266: u64):
    %2029 = const i64 8
    %2030 = gep i8, ptr %7, %2029
    %2031 = load u64, ptr %2030
    %2032 = icmp ult u64 %266, %2031
    condbr %2032, bb27(%257, %258, %259, %260, %261, %262, %263, %264, %265, %266, %266), bb226
bb27(%267: ptr, %268: u32, %269: u32, %270: u64, %271: ptr, %272: u64, %273: u64, %274: u64, %275: u64, %276: u64, %277: u64):
    %2033 = load ptr, ptr %7
    %2034 = gep bool, ptr %2033, %277
    %2035 = load bool, ptr %2034
    condbr %2035, bb28(%267, %268, %269, %270, %271, %272, %273, %274, %275, %276), bb118(%267, %268, %269, %270, %271, %272, %273, %274, %275, %276)
bb28(%278: ptr, %279: u32, %280: u32, %281: u64, %282: ptr, %283: u64, %284: u64, %285: u64, %286: u64, %287: u64):
    call @func.50(%1731, %8, %287)
    br bb29(%278, %279, %280, %281, %282, %283, %284, %285, %286, %287)
bb29(%288: ptr, %289: u32, %290: u32, %291: u64, %292: ptr, %293: u64, %294: u64, %295: u64, %296: u64, %297: u64):
    %2036 = load i64, ptr %1731
    %2037 = const i64 0
    %2038 = icmp eq i64 %2036, %2037
    %2039 = const i64 0
    %2040 = const i64 1
    %2041 = select i64 %2038, %2039, %2040
    switch %2041 [ 0: bb31(%288, %289, %290, %291, %292, %293, %294, %295, %296, %297) 1: bb32(%288, %289, %290, %291, %292, %293, %294, %295, %296, %297) default: bb30 ]
bb30:
    unreachable
bb31(%298: ptr, %299: u32, %300: u32, %301: u64, %302: ptr, %303: u64, %304: u64, %305: u64, %306: u64, %307: u64):
    %2042 = const u64 0
    br bb33(%298, %299, %300, %301, %302, %303, %304, %305, %306, %307, %2042)
bb32(%308: ptr, %309: u32, %310: u32, %311: u64, %312: ptr, %313: u64, %314: u64, %315: u64, %316: u64, %317: u64):
    %2043 = load ptr, ptr %1731
    %2044 = call @func.109(%2043)
    br bb215(%308, %309, %310, %311, %312, %313, %314, %315, %316, %317, %2044)
bb33(%318: ptr, %319: u32, %320: u32, %321: u64, %322: ptr, %323: u64, %324: u64, %325: u64, %326: u64, %327: u64, %328: u64):
    %2045 = const i64 8
    %2046 = gep i8, ptr %12, %2045
    %2047 = load u64, ptr %2046
    %2048 = const u64 1
    %2049 = icmp ugt u64 %2047, %2048
    condbr %2049, bb34(%318, %319, %320, %321, %322, %323, %324, %325, %326, %327, %328, %328), bb42(%318, %319, %320, %321, %322, %323, %324, %325, %326, %327, %328, %328)
bb34(%329: ptr, %330: u32, %331: u32, %332: u64, %333: ptr, %334: u64, %335: u64, %336: u64, %337: u64, %338: u64, %339: u64, %340: u64):
    call @func.50(%1733, %8, %338)
    br bb35(%329, %330, %331, %332, %333, %334, %335, %336, %337, %338, %339, %340)
bb35(%341: ptr, %342: u32, %343: u32, %344: u64, %345: ptr, %346: u64, %347: u64, %348: u64, %349: u64, %350: u64, %351: u64, %352: u64):
    %2050 = load i64, ptr %1733
    %2051 = const i64 0
    %2052 = icmp eq i64 %2050, %2051
    %2053 = const i64 0
    %2054 = const i64 1
    %2055 = select i64 %2052, %2053, %2054
    switch %2055 [ 0: bb36(%341, %342, %343, %344, %345, %346, %347, %348, %349, %350, %351, %352) 1: bb37(%341, %342, %343, %344, %345, %346, %347, %348, %349, %350, %351, %352) default: bb30 ]
bb36(%353: ptr, %354: u32, %355: u32, %356: u64, %357: ptr, %358: u64, %359: u64, %360: u64, %361: u64, %362: u64, %363: u64, %364: u64):
    %2056 = load i32, ptr %353
    store i32 %2056, ptr %1732
    br bb43(%353, %354, %355, %356, %357, %358, %359, %360, %361, %362, %363, %364)
bb37(%365: ptr, %366: u32, %367: u32, %368: u64, %369: ptr, %370: u64, %371: u64, %372: u64, %373: u64, %374: u64, %375: u64, %376: u64):
    %2057 = load ptr, ptr %1733
    %2058 = call @func.110(%2057)
    br bb38(%365, %366, %367, %368, %369, %370, %371, %372, %373, %374, %375, %376, %2058)
bb38(%377: ptr, %378: u32, %379: u32, %380: u64, %381: ptr, %382: u64, %383: u64, %384: u64, %385: u64, %386: u64, %387: u64, %388: u64, %389: ptr):
    %2059 = call @func.111(%389)
    store ptr %2059, ptr %1734
    br bb39(%377, %378, %379, %380, %381, %382, %383, %384, %385, %386, %387, %388)
bb39(%390: ptr, %391: u32, %392: u32, %393: u64, %394: ptr, %395: u64, %396: u64, %397: u64, %398: u64, %399: u64, %400: u64, %401: u64):
    %2060 = load ptr, ptr %1734
    store ptr %2060, ptr %1735
    %2061 = load ptr, ptr %1735
    %2062 = load i8, ptr %2061
    %2063 = sext i8 %2062 to i64
    switch %2063 [ 3: bb41(%390, %391, %392, %393, %394, %395, %396, %397, %398, %399, %400, %401) default: bb40(%390, %391, %392, %393, %394, %395, %396, %397, %398, %399, %400, %401) ]
bb40(%402: ptr, %403: u32, %404: u32, %405: u64, %406: ptr, %407: u64, %408: u64, %409: u64, %410: u64, %411: u64, %412: u64, %413: u64):
    %2064 = load i32, ptr %402
    store i32 %2064, ptr %1732
    br bb43(%402, %403, %404, %405, %406, %407, %408, %409, %410, %411, %412, %413)
bb41(%414: ptr, %415: u32, %416: u32, %417: u64, %418: ptr, %419: u64, %420: u64, %421: u64, %422: u64, %423: u64, %424: u64, %425: u64):
    %2065 = load ptr, ptr %1735
    %2066 = const i64 4
    %2067 = gep i8, ptr %2065, %2066
    call @func.21(%1732, %2067, %13, %414)
    br bb216(%414, %415, %416, %417, %418, %419, %420, %421, %422, %423, %424, %425)
bb42(%426: ptr, %427: u32, %428: u32, %429: u64, %430: ptr, %431: u64, %432: u64, %433: u64, %434: u64, %435: u64, %436: u64, %437: u64):
    %2068 = load i32, ptr %426
    store i32 %2068, ptr %1732
    br bb43(%426, %427, %428, %429, %430, %431, %432, %433, %434, %435, %436, %437)
bb43(%438: ptr, %439: u32, %440: u32, %441: u64, %442: ptr, %443: u64, %444: u64, %445: u64, %446: u64, %447: u64, %448: u64, %449: u64):
    %2069 = load i32, ptr %1732
    store i32 %2069, ptr %1737
    call @func.51(%1738, %1727)
    br bb44(%438, %439, %440, %441, %442, %443, %444, %445, %446, %447, %448, %449)
bb44(%450: ptr, %451: u32, %452: u32, %453: u64, %454: ptr, %455: u64, %456: u64, %457: u64, %458: u64, %459: u64, %460: u64, %461: u64):
    %2070 = load u32, ptr %1737
    call @func.112(%1736, %2070, %1738)
    br bb45(%450, %451, %452, %453, %454, %455, %456, %457, %458, %459, %460, %461)
bb45(%462: ptr, %463: u32, %464: u32, %465: u64, %466: ptr, %467: u64, %468: u64, %469: u64, %470: u64, %471: u64, %472: u64, %473: u64):
    %2071 = const bool true
    %2072 = const u64 0
    br bb46(%462, %463, %464, %465, %466, %467, %468, %469, %470, %471, %472, %473, %2072)
bb46(%474: ptr, %475: u32, %476: u32, %477: u64, %478: ptr, %479: u64, %480: u64, %481: u64, %482: u64, %483: u64, %484: u64, %485: u64, %486: u64):
    %2073 = icmp ult u64 %486, %480
    condbr %2073, bb47(%474, %475, %476, %477, %478, %479, %480, %481, %482, %483, %484, %485, %486), bb55(%474, %475, %476, %477, %478, %479, %480, %481, %482, %483, %484, %485)
bb47(%487: ptr, %488: u32, %489: u32, %490: u64, %491: ptr, %492: u64, %493: u64, %494: u64, %495: u64, %496: u64, %497: u64, %498: u64, %499: u64):
    %2074 = const u64 1
    %2075, %2076 = sub.overflow u64 %495, %2074
    store u64 %2075, ptr %1739
    %2077 = const i64 8
    %2078 = gep i8, ptr %1739, %2077
    store bool %2076, ptr %2078
    %2079 = const i64 8
    %2080 = gep i8, ptr %1739, %2079
    %2081 = load bool, ptr %2080
    %2082 = const bool false
    %2083 = icmp eq bool %2081, %2082
    condbr %2083, bb48(%487, %488, %489, %490, %491, %492, %493, %494, %495, %496, %497, %498, %499), bb226
bb48(%500: ptr, %501: u32, %502: u32, %503: u64, %504: ptr, %505: u64, %506: u64, %507: u64, %508: u64, %509: u64, %510: u64, %511: u64, %512: u64):
    %2084 = load u64, ptr %1739
    %2085, %2086 = sub.overflow u64 %2084, %512
    store u64 %2085, ptr %1740
    %2087 = const i64 8
    %2088 = gep i8, ptr %1740, %2087
    store bool %2086, ptr %2088
    %2089 = const i64 8
    %2090 = gep i8, ptr %1740, %2089
    %2091 = load bool, ptr %2090
    %2092 = const bool false
    %2093 = icmp eq bool %2091, %2092
    condbr %2093, bb49(%500, %501, %502, %503, %504, %505, %506, %507, %508, %509, %510, %511, %512), bb226
bb49(%513: ptr, %514: u32, %515: u32, %516: u64, %517: ptr, %518: u64, %519: u64, %520: u64, %521: u64, %522: u64, %523: u64, %524: u64, %525: u64):
    %2094 = load u64, ptr %1740
    %2095, %2096 = add.overflow u64 %2094, %524
    store u64 %2095, ptr %1741
    %2097 = const i64 8
    %2098 = gep i8, ptr %1741, %2097
    store bool %2096, ptr %2098
    %2099 = const i64 8
    %2100 = gep i8, ptr %1741, %2099
    %2101 = load bool, ptr %2100
    %2102 = const bool false
    %2103 = icmp eq bool %2101, %2102
    condbr %2103, bb50(%513, %514, %515, %516, %517, %518, %519, %520, %521, %522, %523, %524, %525), bb226
bb50(%526: ptr, %527: u32, %528: u32, %529: u64, %530: ptr, %531: u64, %532: u64, %533: u64, %534: u64, %535: u64, %536: u64, %537: u64, %538: u64):
    %2104 = load u64, ptr %1741
    %2105 = call @func.103(%2104)
    br bb51(%526, %527, %528, %529, %530, %531, %532, %533, %534, %535, %536, %537, %538, %2105)
bb51(%539: ptr, %540: u32, %541: u32, %542: u64, %543: ptr, %544: u64, %545: u64, %546: u64, %547: u64, %548: u64, %549: u64, %550: u64, %551: u64, %552: u32):
    %2106 = const bool false
    %2107 = const bool true
    %2108 = load i64, ptr %1736
    store i64 %2108, ptr %1743
    %2109 = const i64 8
    %2110 = gep i8, ptr %1736, %2109
    %2111 = const i64 8
    %2112 = gep i8, ptr %1743, %2111
    %2113 = load i64, ptr %2110
    store i64 %2113, ptr %2112
    %2114 = const i64 16
    %2115 = gep i8, ptr %1736, %2114
    %2116 = const i64 16
    %2117 = gep i8, ptr %1743, %2116
    %2118 = load i64, ptr %2115
    store i64 %2118, ptr %2117
    %2119 = const i64 24
    %2120 = gep i8, ptr %1736, %2119
    %2121 = const i64 24
    %2122 = gep i8, ptr %1743, %2121
    %2123 = load i64, ptr %2120
    store i64 %2123, ptr %2122
    %2124 = const i64 32
    %2125 = gep i8, ptr %1736, %2124
    %2126 = const i64 32
    %2127 = gep i8, ptr %1743, %2126
    %2128 = load i64, ptr %2125
    store i64 %2128, ptr %2127
    call @func.83(%1744, %552)
    br bb52(%539, %540, %541, %542, %543, %544, %545, %546, %547, %548, %549, %550, %551)
bb52(%553: ptr, %554: u32, %555: u32, %556: u64, %557: ptr, %558: u64, %559: u64, %560: u64, %561: u64, %562: u64, %563: u64, %564: u64, %565: u64):
    %2129 = const bool false
    call @func.84(%1742, %1743, %1744)
    br bb53(%553, %554, %555, %556, %557, %558, %559, %560, %561, %562, %563, %564, %565)
bb53(%566: ptr, %567: u32, %568: u32, %569: u64, %570: ptr, %571: u64, %572: u64, %573: u64, %574: u64, %575: u64, %576: u64, %577: u64, %578: u64):
    %2130 = const bool false
    %2131 = const bool true
    %2132 = load i64, ptr %1742
    store i64 %2132, ptr %1736
    %2133 = const i64 8
    %2134 = gep i8, ptr %1742, %2133
    %2135 = const i64 8
    %2136 = gep i8, ptr %1736, %2135
    %2137 = load i64, ptr %2134
    store i64 %2137, ptr %2136
    %2138 = const i64 16
    %2139 = gep i8, ptr %1742, %2138
    %2140 = const i64 16
    %2141 = gep i8, ptr %1736, %2140
    %2142 = load i64, ptr %2139
    store i64 %2142, ptr %2141
    %2143 = const i64 24
    %2144 = gep i8, ptr %1742, %2143
    %2145 = const i64 24
    %2146 = gep i8, ptr %1736, %2145
    %2147 = load i64, ptr %2144
    store i64 %2147, ptr %2146
    %2148 = const i64 32
    %2149 = gep i8, ptr %1742, %2148
    %2150 = const i64 32
    %2151 = gep i8, ptr %1736, %2150
    %2152 = load i64, ptr %2149
    store i64 %2152, ptr %2151
    %2153 = const u64 1
    %2154, %2155 = add.overflow u64 %578, %2153
    store u64 %2154, ptr %1745
    %2156 = const i64 8
    %2157 = gep i8, ptr %1745, %2156
    store bool %2155, ptr %2157
    %2158 = const i64 8
    %2159 = gep i8, ptr %1745, %2158
    %2160 = load bool, ptr %2159
    %2161 = const bool false
    %2162 = icmp eq bool %2160, %2161
    condbr %2162, bb54(%566, %567, %568, %569, %570, %571, %572, %573, %574, %575, %576, %577), bb226
bb54(%579: ptr, %580: u32, %581: u32, %582: u64, %583: ptr, %584: u64, %585: u64, %586: u64, %587: u64, %588: u64, %589: u64, %590: u64):
    %2163 = load u64, ptr %1745
    br bb46(%579, %580, %581, %582, %583, %584, %585, %586, %587, %588, %589, %590, %2163)
bb55(%591: ptr, %592: u32, %593: u32, %594: u64, %595: ptr, %596: u64, %597: u64, %598: u64, %599: u64, %600: u64, %601: u64, %602: u64):
    %2164 = const u64 0
    br bb56(%591, %592, %593, %594, %595, %596, %597, %598, %599, %600, %601, %602, %2164)
bb56(%603: ptr, %604: u32, %605: u32, %606: u64, %607: ptr, %608: u64, %609: u64, %610: u64, %611: u64, %612: u64, %613: u64, %614: u64, %615: u64):
    %2165 = icmp ult u64 %615, %610
    condbr %2165, bb57(%603, %604, %605, %606, %607, %608, %609, %610, %611, %612, %613, %614, %615), bb67(%603, %604, %605, %606, %607, %608, %609, %610, %611, %612, %613, %614)
bb57(%616: ptr, %617: u32, %618: u32, %619: u64, %620: ptr, %621: u64, %622: u64, %623: u64, %624: u64, %625: u64, %626: u64, %627: u64, %628: u64):
    %2166, %2167 = add.overflow u64 %621, %619
    store u64 %2166, ptr %1746
    %2168 = const i64 8
    %2169 = gep i8, ptr %1746, %2168
    store bool %2167, ptr %2169
    %2170 = const i64 8
    %2171 = gep i8, ptr %1746, %2170
    %2172 = load bool, ptr %2171
    %2173 = const bool false
    %2174 = icmp eq bool %2172, %2173
    condbr %2174, bb58(%616, %617, %618, %619, %620, %621, %622, %623, %624, %625, %626, %627, %628), bb226
bb58(%629: ptr, %630: u32, %631: u32, %632: u64, %633: ptr, %634: u64, %635: u64, %636: u64, %637: u64, %638: u64, %639: u64, %640: u64, %641: u64):
    %2175 = load u64, ptr %1746
    %2176, %2177 = add.overflow u64 %2175, %636
    store u64 %2176, ptr %1747
    %2178 = const i64 8
    %2179 = gep i8, ptr %1747, %2178
    store bool %2177, ptr %2179
    %2180 = const i64 8
    %2181 = gep i8, ptr %1747, %2180
    %2182 = load bool, ptr %2181
    %2183 = const bool false
    %2184 = icmp eq bool %2182, %2183
    condbr %2184, bb59(%629, %630, %631, %632, %633, %634, %635, %636, %637, %638, %639, %640, %641), bb226
bb59(%642: ptr, %643: u32, %644: u32, %645: u64, %646: ptr, %647: u64, %648: u64, %649: u64, %650: u64, %651: u64, %652: u64, %653: u64, %654: u64):
    %2185 = load u64, ptr %1747
    %2186 = const u64 1
    %2187, %2188 = sub.overflow u64 %2185, %2186
    store u64 %2187, ptr %1748
    %2189 = const i64 8
    %2190 = gep i8, ptr %1748, %2189
    store bool %2188, ptr %2190
    %2191 = const i64 8
    %2192 = gep i8, ptr %1748, %2191
    %2193 = load bool, ptr %2192
    %2194 = const bool false
    %2195 = icmp eq bool %2193, %2194
    condbr %2195, bb60(%642, %643, %644, %645, %646, %647, %648, %649, %650, %651, %652, %653, %654), bb226
bb60(%655: ptr, %656: u32, %657: u32, %658: u64, %659: ptr, %660: u64, %661: u64, %662: u64, %663: u64, %664: u64, %665: u64, %666: u64, %667: u64):
    %2196 = load u64, ptr %1748
    %2197, %2198 = sub.overflow u64 %2196, %667
    store u64 %2197, ptr %1749
    %2199 = const i64 8
    %2200 = gep i8, ptr %1749, %2199
    store bool %2198, ptr %2200
    %2201 = const i64 8
    %2202 = gep i8, ptr %1749, %2201
    %2203 = load bool, ptr %2202
    %2204 = const bool false
    %2205 = icmp eq bool %2203, %2204
    condbr %2205, bb61(%655, %656, %657, %658, %659, %660, %661, %662, %663, %664, %665, %666, %667), bb226
bb61(%668: ptr, %669: u32, %670: u32, %671: u64, %672: ptr, %673: u64, %674: u64, %675: u64, %676: u64, %677: u64, %678: u64, %679: u64, %680: u64):
    %2206 = load u64, ptr %1749
    %2207, %2208 = add.overflow u64 %2206, %679
    store u64 %2207, ptr %1750
    %2209 = const i64 8
    %2210 = gep i8, ptr %1750, %2209
    store bool %2208, ptr %2210
    %2211 = const i64 8
    %2212 = gep i8, ptr %1750, %2211
    %2213 = load bool, ptr %2212
    %2214 = const bool false
    %2215 = icmp eq bool %2213, %2214
    condbr %2215, bb62(%668, %669, %670, %671, %672, %673, %674, %675, %676, %677, %678, %679, %680), bb226
bb62(%681: ptr, %682: u32, %683: u32, %684: u64, %685: ptr, %686: u64, %687: u64, %688: u64, %689: u64, %690: u64, %691: u64, %692: u64, %693: u64):
    %2216 = load u64, ptr %1750
    %2217 = call @func.103(%2216)
    br bb63(%681, %682, %683, %684, %685, %686, %687, %688, %689, %690, %691, %692, %693, %2217)
bb63(%694: ptr, %695: u32, %696: u32, %697: u64, %698: ptr, %699: u64, %700: u64, %701: u64, %702: u64, %703: u64, %704: u64, %705: u64, %706: u64, %707: u32):
    %2218 = const bool false
    %2219 = const bool true
    %2220 = load i64, ptr %1736
    store i64 %2220, ptr %1752
    %2221 = const i64 8
    %2222 = gep i8, ptr %1736, %2221
    %2223 = const i64 8
    %2224 = gep i8, ptr %1752, %2223
    %2225 = load i64, ptr %2222
    store i64 %2225, ptr %2224
    %2226 = const i64 16
    %2227 = gep i8, ptr %1736, %2226
    %2228 = const i64 16
    %2229 = gep i8, ptr %1752, %2228
    %2230 = load i64, ptr %2227
    store i64 %2230, ptr %2229
    %2231 = const i64 24
    %2232 = gep i8, ptr %1736, %2231
    %2233 = const i64 24
    %2234 = gep i8, ptr %1752, %2233
    %2235 = load i64, ptr %2232
    store i64 %2235, ptr %2234
    %2236 = const i64 32
    %2237 = gep i8, ptr %1736, %2236
    %2238 = const i64 32
    %2239 = gep i8, ptr %1752, %2238
    %2240 = load i64, ptr %2237
    store i64 %2240, ptr %2239
    call @func.83(%1753, %707)
    br bb64(%694, %695, %696, %697, %698, %699, %700, %701, %702, %703, %704, %705, %706)
bb64(%708: ptr, %709: u32, %710: u32, %711: u64, %712: ptr, %713: u64, %714: u64, %715: u64, %716: u64, %717: u64, %718: u64, %719: u64, %720: u64):
    %2241 = const bool false
    call @func.84(%1751, %1752, %1753)
    br bb65(%708, %709, %710, %711, %712, %713, %714, %715, %716, %717, %718, %719, %720)
bb65(%721: ptr, %722: u32, %723: u32, %724: u64, %725: ptr, %726: u64, %727: u64, %728: u64, %729: u64, %730: u64, %731: u64, %732: u64, %733: u64):
    %2242 = const bool false
    %2243 = const bool true
    %2244 = load i64, ptr %1751
    store i64 %2244, ptr %1736
    %2245 = const i64 8
    %2246 = gep i8, ptr %1751, %2245
    %2247 = const i64 8
    %2248 = gep i8, ptr %1736, %2247
    %2249 = load i64, ptr %2246
    store i64 %2249, ptr %2248
    %2250 = const i64 16
    %2251 = gep i8, ptr %1751, %2250
    %2252 = const i64 16
    %2253 = gep i8, ptr %1736, %2252
    %2254 = load i64, ptr %2251
    store i64 %2254, ptr %2253
    %2255 = const i64 24
    %2256 = gep i8, ptr %1751, %2255
    %2257 = const i64 24
    %2258 = gep i8, ptr %1736, %2257
    %2259 = load i64, ptr %2256
    store i64 %2259, ptr %2258
    %2260 = const i64 32
    %2261 = gep i8, ptr %1751, %2260
    %2262 = const i64 32
    %2263 = gep i8, ptr %1736, %2262
    %2264 = load i64, ptr %2261
    store i64 %2264, ptr %2263
    %2265 = const u64 1
    %2266, %2267 = add.overflow u64 %733, %2265
    store u64 %2266, ptr %1754
    %2268 = const i64 8
    %2269 = gep i8, ptr %1754, %2268
    store bool %2267, ptr %2269
    %2270 = const i64 8
    %2271 = gep i8, ptr %1754, %2270
    %2272 = load bool, ptr %2271
    %2273 = const bool false
    %2274 = icmp eq bool %2272, %2273
    condbr %2274, bb66(%721, %722, %723, %724, %725, %726, %727, %728, %729, %730, %731, %732), bb226
bb66(%734: ptr, %735: u32, %736: u32, %737: u64, %738: ptr, %739: u64, %740: u64, %741: u64, %742: u64, %743: u64, %744: u64, %745: u64):
    %2275 = load u64, ptr %1754
    br bb56(%734, %735, %736, %737, %738, %739, %740, %741, %742, %743, %744, %745, %2275)
bb67(%746: ptr, %747: u32, %748: u32, %749: u64, %750: ptr, %751: u64, %752: u64, %753: u64, %754: u64, %755: u64, %756: u64, %757: u64):
    %2276 = const u64 0
    br bb68(%746, %747, %748, %749, %750, %751, %752, %753, %754, %755, %756, %757, %2276)
bb68(%758: ptr, %759: u32, %760: u32, %761: u64, %762: ptr, %763: u64, %764: u64, %765: u64, %766: u64, %767: u64, %768: u64, %769: u64, %770: u64):
    %2277 = icmp ult u64 %770, %761
    condbr %2277, bb69(%758, %759, %760, %761, %762, %763, %764, %765, %766, %767, %768, %769, %770), bb78(%758, %759, %760, %761, %762, %763, %764, %765, %766, %767, %768, %769)
bb69(%771: ptr, %772: u32, %773: u32, %774: u64, %775: ptr, %776: u64, %777: u64, %778: u64, %779: u64, %780: u64, %781: u64, %782: u64, %783: u64):
    %2278, %2279 = add.overflow u64 %776, %774
    store u64 %2278, ptr %1755
    %2280 = const i64 8
    %2281 = gep i8, ptr %1755, %2280
    store bool %2279, ptr %2281
    %2282 = const i64 8
    %2283 = gep i8, ptr %1755, %2282
    %2284 = load bool, ptr %2283
    %2285 = const bool false
    %2286 = icmp eq bool %2284, %2285
    condbr %2286, bb70(%771, %772, %773, %774, %775, %776, %777, %778, %779, %780, %781, %782, %783), bb226
bb70(%784: ptr, %785: u32, %786: u32, %787: u64, %788: ptr, %789: u64, %790: u64, %791: u64, %792: u64, %793: u64, %794: u64, %795: u64, %796: u64):
    %2287 = load u64, ptr %1755
    %2288 = const u64 1
    %2289, %2290 = sub.overflow u64 %2287, %2288
    store u64 %2289, ptr %1756
    %2291 = const i64 8
    %2292 = gep i8, ptr %1756, %2291
    store bool %2290, ptr %2292
    %2293 = const i64 8
    %2294 = gep i8, ptr %1756, %2293
    %2295 = load bool, ptr %2294
    %2296 = const bool false
    %2297 = icmp eq bool %2295, %2296
    condbr %2297, bb71(%784, %785, %786, %787, %788, %789, %790, %791, %792, %793, %794, %795, %796), bb226
bb71(%797: ptr, %798: u32, %799: u32, %800: u64, %801: ptr, %802: u64, %803: u64, %804: u64, %805: u64, %806: u64, %807: u64, %808: u64, %809: u64):
    %2298 = load u64, ptr %1756
    %2299, %2300 = sub.overflow u64 %2298, %809
    store u64 %2299, ptr %1757
    %2301 = const i64 8
    %2302 = gep i8, ptr %1757, %2301
    store bool %2300, ptr %2302
    %2303 = const i64 8
    %2304 = gep i8, ptr %1757, %2303
    %2305 = load bool, ptr %2304
    %2306 = const bool false
    %2307 = icmp eq bool %2305, %2306
    condbr %2307, bb72(%797, %798, %799, %800, %801, %802, %803, %804, %805, %806, %807, %808, %809), bb226
bb72(%810: ptr, %811: u32, %812: u32, %813: u64, %814: ptr, %815: u64, %816: u64, %817: u64, %818: u64, %819: u64, %820: u64, %821: u64, %822: u64):
    %2308 = load u64, ptr %1757
    %2309, %2310 = add.overflow u64 %2308, %821
    store u64 %2309, ptr %1758
    %2311 = const i64 8
    %2312 = gep i8, ptr %1758, %2311
    store bool %2310, ptr %2312
    %2313 = const i64 8
    %2314 = gep i8, ptr %1758, %2313
    %2315 = load bool, ptr %2314
    %2316 = const bool false
    %2317 = icmp eq bool %2315, %2316
    condbr %2317, bb73(%810, %811, %812, %813, %814, %815, %816, %817, %818, %819, %820, %821, %822), bb226
bb73(%823: ptr, %824: u32, %825: u32, %826: u64, %827: ptr, %828: u64, %829: u64, %830: u64, %831: u64, %832: u64, %833: u64, %834: u64, %835: u64):
    %2318 = load u64, ptr %1758
    %2319 = call @func.103(%2318)
    br bb74(%823, %824, %825, %826, %827, %828, %829, %830, %831, %832, %833, %834, %835, %2319)
bb74(%836: ptr, %837: u32, %838: u32, %839: u64, %840: ptr, %841: u64, %842: u64, %843: u64, %844: u64, %845: u64, %846: u64, %847: u64, %848: u64, %849: u32):
    %2320 = const bool false
    %2321 = const bool true
    %2322 = load i64, ptr %1736
    store i64 %2322, ptr %1760
    %2323 = const i64 8
    %2324 = gep i8, ptr %1736, %2323
    %2325 = const i64 8
    %2326 = gep i8, ptr %1760, %2325
    %2327 = load i64, ptr %2324
    store i64 %2327, ptr %2326
    %2328 = const i64 16
    %2329 = gep i8, ptr %1736, %2328
    %2330 = const i64 16
    %2331 = gep i8, ptr %1760, %2330
    %2332 = load i64, ptr %2329
    store i64 %2332, ptr %2331
    %2333 = const i64 24
    %2334 = gep i8, ptr %1736, %2333
    %2335 = const i64 24
    %2336 = gep i8, ptr %1760, %2335
    %2337 = load i64, ptr %2334
    store i64 %2337, ptr %2336
    %2338 = const i64 32
    %2339 = gep i8, ptr %1736, %2338
    %2340 = const i64 32
    %2341 = gep i8, ptr %1760, %2340
    %2342 = load i64, ptr %2339
    store i64 %2342, ptr %2341
    call @func.83(%1761, %849)
    br bb75(%836, %837, %838, %839, %840, %841, %842, %843, %844, %845, %846, %847, %848)
bb75(%850: ptr, %851: u32, %852: u32, %853: u64, %854: ptr, %855: u64, %856: u64, %857: u64, %858: u64, %859: u64, %860: u64, %861: u64, %862: u64):
    %2343 = const bool false
    call @func.84(%1759, %1760, %1761)
    br bb76(%850, %851, %852, %853, %854, %855, %856, %857, %858, %859, %860, %861, %862)
bb76(%863: ptr, %864: u32, %865: u32, %866: u64, %867: ptr, %868: u64, %869: u64, %870: u64, %871: u64, %872: u64, %873: u64, %874: u64, %875: u64):
    %2344 = const bool false
    %2345 = const bool true
    %2346 = load i64, ptr %1759
    store i64 %2346, ptr %1736
    %2347 = const i64 8
    %2348 = gep i8, ptr %1759, %2347
    %2349 = const i64 8
    %2350 = gep i8, ptr %1736, %2349
    %2351 = load i64, ptr %2348
    store i64 %2351, ptr %2350
    %2352 = const i64 16
    %2353 = gep i8, ptr %1759, %2352
    %2354 = const i64 16
    %2355 = gep i8, ptr %1736, %2354
    %2356 = load i64, ptr %2353
    store i64 %2356, ptr %2355
    %2357 = const i64 24
    %2358 = gep i8, ptr %1759, %2357
    %2359 = const i64 24
    %2360 = gep i8, ptr %1736, %2359
    %2361 = load i64, ptr %2358
    store i64 %2361, ptr %2360
    %2362 = const i64 32
    %2363 = gep i8, ptr %1759, %2362
    %2364 = const i64 32
    %2365 = gep i8, ptr %1736, %2364
    %2366 = load i64, ptr %2363
    store i64 %2366, ptr %2365
    %2367 = const u64 1
    %2368, %2369 = add.overflow u64 %875, %2367
    store u64 %2368, ptr %1762
    %2370 = const i64 8
    %2371 = gep i8, ptr %1762, %2370
    store bool %2369, ptr %2371
    %2372 = const i64 8
    %2373 = gep i8, ptr %1762, %2372
    %2374 = load bool, ptr %2373
    %2375 = const bool false
    %2376 = icmp eq bool %2374, %2375
    condbr %2376, bb77(%863, %864, %865, %866, %867, %868, %869, %870, %871, %872, %873, %874), bb226
bb77(%876: ptr, %877: u32, %878: u32, %879: u64, %880: ptr, %881: u64, %882: u64, %883: u64, %884: u64, %885: u64, %886: u64, %887: u64):
    %2377 = load u64, ptr %1762
    br bb68(%876, %877, %878, %879, %880, %881, %882, %883, %884, %885, %886, %887, %2377)
bb78(%888: ptr, %889: u32, %890: u32, %891: u64, %892: ptr, %893: u64, %894: u64, %895: u64, %896: u64, %897: u64, %898: u64, %899: u64):
    %2378 = const u32 0
    %2379 = icmp ugt u32 %890, %2378
    condbr %2379, bb79(%888, %889, %890, %891, %892, %893, %894, %895, %896, %897, %898, %899), bb91(%888, %889, %890, %891, %892, %893, %894, %895, %896, %897, %898, %899)
bb79(%900: ptr, %901: u32, %902: u32, %903: u64, %904: ptr, %905: u64, %906: u64, %907: u64, %908: u64, %909: u64, %910: u64, %911: u64):
    call @func.50(%1763, %8, %909)
    br bb80(%900, %901, %902, %903, %904, %905, %906, %907, %908, %909, %910, %911)
bb80(%912: ptr, %913: u32, %914: u32, %915: u64, %916: ptr, %917: u64, %918: u64, %919: u64, %920: u64, %921: u64, %922: u64, %923: u64):
    %2380 = load i64, ptr %1763
    %2381 = const i64 0
    %2382 = icmp eq i64 %2380, %2381
    %2383 = const i64 0
    %2384 = const i64 1
    %2385 = select i64 %2382, %2383, %2384
    switch %2385 [ 1: bb81(%912, %913, %914, %915, %916, %917, %918, %919, %920, %921, %922, %923) 0: bb91(%912, %913, %914, %915, %916, %917, %918, %919, %920, %921, %922, %923) default: bb30 ]
bb81(%924: ptr, %925: u32, %926: u32, %927: u64, %928: ptr, %929: u64, %930: u64, %931: u64, %932: u64, %933: u64, %934: u64, %935: u64):
    %2386 = load ptr, ptr %1763
    call @func.70(%1764, %2386, %925)
    br bb82(%924, %925, %926, %927, %928, %929, %930, %931, %932, %933, %934, %935)
bb82(%936: ptr, %937: u32, %938: u32, %939: u64, %940: ptr, %941: u64, %942: u64, %943: u64, %944: u64, %945: u64, %946: u64, %947: u64):
    %2387 = const u64 0
    br bb83(%936, %937, %938, %939, %940, %941, %942, %943, %944, %945, %946, %947, %2387)
bb83(%948: ptr, %949: u32, %950: u32, %951: u64, %952: ptr, %953: u64, %954: u64, %955: u64, %956: u64, %957: u64, %958: u64, %959: u64, %960: u64):
    %2388 = call @func.52(%1764)
    br bb84(%948, %949, %950, %951, %952, %953, %954, %955, %956, %957, %958, %959, %960, %960, %2388)
bb84(%961: ptr, %962: u32, %963: u32, %964: u64, %965: ptr, %966: u64, %967: u64, %968: u64, %969: u64, %970: u64, %971: u64, %972: u64, %973: u64, %974: u64, %975: u64):
    %2389 = icmp ult u64 %974, %975
    condbr %2389, bb85(%961, %962, %963, %964, %965, %966, %967, %968, %969, %970, %971, %972, %973), bb90(%961, %962, %963, %964, %965, %966, %967, %968, %969, %970, %971, %972)
bb85(%976: ptr, %977: u32, %978: u32, %979: u64, %980: ptr, %981: u64, %982: u64, %983: u64, %984: u64, %985: u64, %986: u64, %987: u64, %988: u64):
    %2390 = call @func.53(%1764, %988)
    br bb86(%976, %977, %978, %979, %980, %981, %982, %983, %984, %985, %986, %987, %988, %2390)
bb86(%989: ptr, %990: u32, %991: u32, %992: u64, %993: ptr, %994: u64, %995: u64, %996: u64, %997: u64, %998: u64, %999: u64, %1000: u64, %1001: u64, %1002: ptr):
    call @func.113(%1765, %1002, %998, %995, %994, %992, %996, %999)
    br bb87(%989, %990, %991, %992, %993, %994, %995, %996, %997, %998, %999, %1000, %1001)
bb87(%1003: ptr, %1004: u32, %1005: u32, %1006: u64, %1007: ptr, %1008: u64, %1009: u64, %1010: u64, %1011: u64, %1012: u64, %1013: u64, %1014: u64, %1015: u64):
    %2391 = const bool false
    %2392 = load i64, ptr %1736
    store i64 %2392, ptr %1767
    %2393 = const i64 8
    %2394 = gep i8, ptr %1736, %2393
    %2395 = const i64 8
    %2396 = gep i8, ptr %1767, %2395
    %2397 = load i64, ptr %2394
    store i64 %2397, ptr %2396
    %2398 = const i64 16
    %2399 = gep i8, ptr %1736, %2398
    %2400 = const i64 16
    %2401 = gep i8, ptr %1767, %2400
    %2402 = load i64, ptr %2399
    store i64 %2402, ptr %2401
    %2403 = const i64 24
    %2404 = gep i8, ptr %1736, %2403
    %2405 = const i64 24
    %2406 = gep i8, ptr %1767, %2405
    %2407 = load i64, ptr %2404
    store i64 %2407, ptr %2406
    %2408 = const i64 32
    %2409 = gep i8, ptr %1736, %2408
    %2410 = const i64 32
    %2411 = gep i8, ptr %1767, %2410
    %2412 = load i64, ptr %2409
    store i64 %2412, ptr %2411
    call @func.84(%1766, %1767, %1765)
    br bb88(%1003, %1004, %1005, %1006, %1007, %1008, %1009, %1010, %1011, %1012, %1013, %1014, %1015)
bb88(%1016: ptr, %1017: u32, %1018: u32, %1019: u64, %1020: ptr, %1021: u64, %1022: u64, %1023: u64, %1024: u64, %1025: u64, %1026: u64, %1027: u64, %1028: u64):
    %2413 = const bool true
    %2414 = load i64, ptr %1766
    store i64 %2414, ptr %1736
    %2415 = const i64 8
    %2416 = gep i8, ptr %1766, %2415
    %2417 = const i64 8
    %2418 = gep i8, ptr %1736, %2417
    %2419 = load i64, ptr %2416
    store i64 %2419, ptr %2418
    %2420 = const i64 16
    %2421 = gep i8, ptr %1766, %2420
    %2422 = const i64 16
    %2423 = gep i8, ptr %1736, %2422
    %2424 = load i64, ptr %2421
    store i64 %2424, ptr %2423
    %2425 = const i64 24
    %2426 = gep i8, ptr %1766, %2425
    %2427 = const i64 24
    %2428 = gep i8, ptr %1736, %2427
    %2429 = load i64, ptr %2426
    store i64 %2429, ptr %2428
    %2430 = const i64 32
    %2431 = gep i8, ptr %1766, %2430
    %2432 = const i64 32
    %2433 = gep i8, ptr %1736, %2432
    %2434 = load i64, ptr %2431
    store i64 %2434, ptr %2433
    %2435 = const u64 1
    %2436, %2437 = add.overflow u64 %1028, %2435
    store u64 %2436, ptr %1768
    %2438 = const i64 8
    %2439 = gep i8, ptr %1768, %2438
    store bool %2437, ptr %2439
    %2440 = const i64 8
    %2441 = gep i8, ptr %1768, %2440
    %2442 = load bool, ptr %2441
    %2443 = const bool false
    %2444 = icmp eq bool %2442, %2443
    condbr %2444, bb89(%1016, %1017, %1018, %1019, %1020, %1021, %1022, %1023, %1024, %1025, %1026, %1027), bb226
bb89(%1029: ptr, %1030: u32, %1031: u32, %1032: u64, %1033: ptr, %1034: u64, %1035: u64, %1036: u64, %1037: u64, %1038: u64, %1039: u64, %1040: u64):
    %2445 = load u64, ptr %1768
    br bb83(%1029, %1030, %1031, %1032, %1033, %1034, %1035, %1036, %1037, %1038, %1039, %1040, %2445)
bb90(%1041: ptr, %1042: u32, %1043: u32, %1044: u64, %1045: ptr, %1046: u64, %1047: u64, %1048: u64, %1049: u64, %1050: u64, %1051: u64, %1052: u64):
    br bb91(%1041, %1042, %1043, %1044, %1045, %1046, %1047, %1048, %1049, %1050, %1051, %1052)
bb91(%1053: ptr, %1054: u32, %1055: u32, %1056: u64, %1057: ptr, %1058: u64, %1059: u64, %1060: u64, %1061: u64, %1062: u64, %1063: u64, %1064: u64):
    %2446 = const u64 1
    %2447, %2448 = sub.overflow u64 %1058, %2446
    store u64 %2447, ptr %1770
    %2449 = const i64 8
    %2450 = gep i8, ptr %1770, %2449
    store bool %2448, ptr %2450
    %2451 = const i64 8
    %2452 = gep i8, ptr %1770, %2451
    %2453 = load bool, ptr %2452
    %2454 = const bool false
    %2455 = icmp eq bool %2453, %2454
    condbr %2455, bb92(%1053, %1054, %1055, %1056, %1057, %1058, %1059, %1060, %1061, %1062, %1063, %1064), bb226
bb92(%1065: ptr, %1066: u32, %1067: u32, %1068: u64, %1069: ptr, %1070: u64, %1071: u64, %1072: u64, %1073: u64, %1074: u64, %1075: u64, %1076: u64):
    %2456 = load u64, ptr %1770
    %2457, %2458 = sub.overflow u64 %2456, %1074
    store u64 %2457, ptr %1771
    %2459 = const i64 8
    %2460 = gep i8, ptr %1771, %2459
    store bool %2458, ptr %2460
    %2461 = const i64 8
    %2462 = gep i8, ptr %1771, %2461
    %2463 = load bool, ptr %2462
    %2464 = const bool false
    %2465 = icmp eq bool %2463, %2464
    condbr %2465, bb93(%1065, %1066, %1067, %1068, %1069, %1070, %1071, %1072, %1073, %1074, %1075, %1076), bb226
bb93(%1077: ptr, %1078: u32, %1079: u32, %1080: u64, %1081: ptr, %1082: u64, %1083: u64, %1084: u64, %1085: u64, %1086: u64, %1087: u64, %1088: u64):
    %2466 = load u64, ptr %1771
    %2467, %2468 = add.overflow u64 %2466, %1088
    store u64 %2467, ptr %1772
    %2469 = const i64 8
    %2470 = gep i8, ptr %1772, %2469
    store bool %2468, ptr %2470
    %2471 = const i64 8
    %2472 = gep i8, ptr %1772, %2471
    %2473 = load bool, ptr %2472
    %2474 = const bool false
    %2475 = icmp eq bool %2473, %2474
    condbr %2475, bb94(%1077, %1078, %1079, %1080, %1081, %1082, %1083, %1084, %1085, %1086, %1087), bb226
bb94(%1089: ptr, %1090: u32, %1091: u32, %1092: u64, %1093: ptr, %1094: u64, %1095: u64, %1096: u64, %1097: u64, %1098: u64, %1099: u64):
    %2476 = load u64, ptr %1772
    %2477 = call @func.103(%2476)
    br bb95(%1089, %1090, %1091, %1092, %1093, %1094, %1095, %1096, %1097, %1098, %1099, %2477)
bb95(%1100: ptr, %1101: u32, %1102: u32, %1103: u64, %1104: ptr, %1105: u64, %1106: u64, %1107: u64, %1108: u64, %1109: u64, %1110: u64, %1111: u32):
    call @func.83(%1769, %1111)
    br bb96(%1100, %1101, %1102, %1103, %1104, %1105, %1106, %1107, %1108, %1109, %1110)
bb96(%1112: ptr, %1113: u32, %1114: u32, %1115: u64, %1116: ptr, %1117: u64, %1118: u64, %1119: u64, %1120: u64, %1121: u64, %1122: u64):
    %2478 = const bool true
    br bb97(%1112, %1113, %1114, %1115, %1116, %1117, %1118, %1119, %1120, %1121, %1122)
bb97(%1123: ptr, %1124: u32, %1125: u32, %1126: u64, %1127: ptr, %1128: u64, %1129: u64, %1130: u64, %1131: u64, %1132: u64, %1133: u64):
    %2479 = const u64 0
    %2480 = icmp ugt u64 %1133, %2479
    condbr %2480, bb98(%1123, %1124, %1125, %1126, %1127, %1128, %1129, %1130, %1131, %1132, %1133), bb103(%1123, %1124, %1125, %1126, %1127, %1128, %1129, %1130, %1131, %1132)
bb98(%1134: ptr, %1135: u32, %1136: u32, %1137: u64, %1138: ptr, %1139: u64, %1140: u64, %1141: u64, %1142: u64, %1143: u64, %1144: u64):
    %2481 = const u64 1
    %2482, %2483 = sub.overflow u64 %1144, %2481
    store u64 %2482, ptr %1773
    %2484 = const i64 8
    %2485 = gep i8, ptr %1773, %2484
    store bool %2483, ptr %2485
    %2486 = const i64 8
    %2487 = gep i8, ptr %1773, %2486
    %2488 = load bool, ptr %2487
    %2489 = const bool false
    %2490 = icmp eq bool %2488, %2489
    condbr %2490, bb99(%1134, %1135, %1136, %1137, %1138, %1139, %1140, %1141, %1142, %1143), bb226
bb99(%1145: ptr, %1146: u32, %1147: u32, %1148: u64, %1149: ptr, %1150: u64, %1151: u64, %1152: u64, %1153: u64, %1154: u64):
    %2491 = load u64, ptr %1773
    %2492 = const bool false
    %2493 = const bool true
    %2494 = load i64, ptr %1769
    store i64 %2494, ptr %1775
    %2495 = const i64 8
    %2496 = gep i8, ptr %1769, %2495
    %2497 = const i64 8
    %2498 = gep i8, ptr %1775, %2497
    %2499 = load i64, ptr %2496
    store i64 %2499, ptr %2498
    %2500 = const i64 16
    %2501 = gep i8, ptr %1769, %2500
    %2502 = const i64 16
    %2503 = gep i8, ptr %1775, %2502
    %2504 = load i64, ptr %2501
    store i64 %2504, ptr %2503
    %2505 = const i64 24
    %2506 = gep i8, ptr %1769, %2505
    %2507 = const i64 24
    %2508 = gep i8, ptr %1775, %2507
    %2509 = load i64, ptr %2506
    store i64 %2509, ptr %2508
    %2510 = const i64 32
    %2511 = gep i8, ptr %1769, %2510
    %2512 = const i64 32
    %2513 = gep i8, ptr %1775, %2512
    %2514 = load i64, ptr %2511
    store i64 %2514, ptr %2513
    %2515 = call @func.103(%2491)
    br bb100(%1145, %1146, %1147, %1148, %1149, %1150, %1151, %1152, %1153, %1154, %2491, %2515)
bb100(%1155: ptr, %1156: u32, %1157: u32, %1158: u64, %1159: ptr, %1160: u64, %1161: u64, %1162: u64, %1163: u64, %1164: u64, %1165: u64, %1166: u32):
    call @func.83(%1776, %1166)
    br bb101(%1155, %1156, %1157, %1158, %1159, %1160, %1161, %1162, %1163, %1164, %1165)
bb101(%1167: ptr, %1168: u32, %1169: u32, %1170: u64, %1171: ptr, %1172: u64, %1173: u64, %1174: u64, %1175: u64, %1176: u64, %1177: u64):
    %2516 = const bool false
    call @func.84(%1774, %1775, %1776)
    br bb102(%1167, %1168, %1169, %1170, %1171, %1172, %1173, %1174, %1175, %1176, %1177)
bb102(%1178: ptr, %1179: u32, %1180: u32, %1181: u64, %1182: ptr, %1183: u64, %1184: u64, %1185: u64, %1186: u64, %1187: u64, %1188: u64):
    %2517 = const bool false
    %2518 = const bool true
    %2519 = load i64, ptr %1774
    store i64 %2519, ptr %1769
    %2520 = const i64 8
    %2521 = gep i8, ptr %1774, %2520
    %2522 = const i64 8
    %2523 = gep i8, ptr %1769, %2522
    %2524 = load i64, ptr %2521
    store i64 %2524, ptr %2523
    %2525 = const i64 16
    %2526 = gep i8, ptr %1774, %2525
    %2527 = const i64 16
    %2528 = gep i8, ptr %1769, %2527
    %2529 = load i64, ptr %2526
    store i64 %2529, ptr %2528
    %2530 = const i64 24
    %2531 = gep i8, ptr %1774, %2530
    %2532 = const i64 24
    %2533 = gep i8, ptr %1769, %2532
    %2534 = load i64, ptr %2531
    store i64 %2534, ptr %2533
    %2535 = const i64 32
    %2536 = gep i8, ptr %1774, %2535
    %2537 = const i64 32
    %2538 = gep i8, ptr %1769, %2537
    %2539 = load i64, ptr %2536
    store i64 %2539, ptr %2538
    br bb97(%1178, %1179, %1180, %1181, %1182, %1183, %1184, %1185, %1186, %1187, %1188)
bb103(%1189: ptr, %1190: u32, %1191: u32, %1192: u64, %1193: ptr, %1194: u64, %1195: u64, %1196: u64, %1197: u64, %1198: u64):
    %2540 = const bool false
    %2541 = load i64, ptr %1736
    store i64 %2541, ptr %1778
    %2542 = const i64 8
    %2543 = gep i8, ptr %1736, %2542
    %2544 = const i64 8
    %2545 = gep i8, ptr %1778, %2544
    %2546 = load i64, ptr %2543
    store i64 %2546, ptr %2545
    %2547 = const i64 16
    %2548 = gep i8, ptr %1736, %2547
    %2549 = const i64 16
    %2550 = gep i8, ptr %1778, %2549
    %2551 = load i64, ptr %2548
    store i64 %2551, ptr %2550
    %2552 = const i64 24
    %2553 = gep i8, ptr %1736, %2552
    %2554 = const i64 24
    %2555 = gep i8, ptr %1778, %2554
    %2556 = load i64, ptr %2553
    store i64 %2556, ptr %2555
    %2557 = const i64 32
    %2558 = gep i8, ptr %1736, %2557
    %2559 = const i64 32
    %2560 = gep i8, ptr %1778, %2559
    %2561 = load i64, ptr %2558
    store i64 %2561, ptr %2560
    %2562 = const bool false
    %2563 = load i64, ptr %1769
    store i64 %2563, ptr %1779
    %2564 = const i64 8
    %2565 = gep i8, ptr %1769, %2564
    %2566 = const i64 8
    %2567 = gep i8, ptr %1779, %2566
    %2568 = load i64, ptr %2565
    store i64 %2568, ptr %2567
    %2569 = const i64 16
    %2570 = gep i8, ptr %1769, %2569
    %2571 = const i64 16
    %2572 = gep i8, ptr %1779, %2571
    %2573 = load i64, ptr %2570
    store i64 %2573, ptr %2572
    %2574 = const i64 24
    %2575 = gep i8, ptr %1769, %2574
    %2576 = const i64 24
    %2577 = gep i8, ptr %1779, %2576
    %2578 = load i64, ptr %2575
    store i64 %2578, ptr %2577
    %2579 = const i64 32
    %2580 = gep i8, ptr %1769, %2579
    %2581 = const i64 32
    %2582 = gep i8, ptr %1779, %2581
    %2583 = load i64, ptr %2580
    store i64 %2583, ptr %2582
    call @func.84(%1777, %1778, %1779)
    br bb104(%1189, %1190, %1191, %1192, %1193, %1194, %1195, %1196, %1197, %1198)
bb104(%1199: ptr, %1200: u32, %1201: u32, %1202: u64, %1203: ptr, %1204: u64, %1205: u64, %1206: u64, %1207: u64, %1208: u64):
    %2584 = const bool true
    %2585 = load i64, ptr %1777
    store i64 %2585, ptr %1736
    %2586 = const i64 8
    %2587 = gep i8, ptr %1777, %2586
    %2588 = const i64 8
    %2589 = gep i8, ptr %1736, %2588
    %2590 = load i64, ptr %2587
    store i64 %2590, ptr %2589
    %2591 = const i64 16
    %2592 = gep i8, ptr %1777, %2591
    %2593 = const i64 16
    %2594 = gep i8, ptr %1736, %2593
    %2595 = load i64, ptr %2592
    store i64 %2595, ptr %2594
    %2596 = const i64 24
    %2597 = gep i8, ptr %1777, %2596
    %2598 = const i64 24
    %2599 = gep i8, ptr %1736, %2598
    %2600 = load i64, ptr %2597
    store i64 %2600, ptr %2599
    %2601 = const i64 32
    %2602 = gep i8, ptr %1777, %2601
    %2603 = const i64 32
    %2604 = gep i8, ptr %1736, %2603
    %2605 = load i64, ptr %2602
    store i64 %2605, ptr %2604
    call @func.50(%1781, %8, %1208)
    br bb105(%1199, %1200, %1201, %1202, %1203, %1204, %1205, %1206, %1207, %1208)
bb105(%1209: ptr, %1210: u32, %1211: u32, %1212: u64, %1213: ptr, %1214: u64, %1215: u64, %1216: u64, %1217: u64, %1218: u64):
    %2606 = load i64, ptr %1781
    %2607 = const i64 0
    %2608 = icmp eq i64 %2606, %2607
    %2609 = const i64 0
    %2610 = const i64 1
    %2611 = select i64 %2608, %2609, %2610
    switch %2611 [ 0: bb106(%1209, %1210, %1211, %1212, %1213, %1214, %1215, %1216, %1217, %1218) 1: bb107(%1209, %1210, %1211, %1212, %1213, %1214, %1215, %1216, %1217, %1218) default: bb30 ]
bb106(%1219: ptr, %1220: u32, %1221: u32, %1222: u64, %1223: ptr, %1224: u64, %1225: u64, %1226: u64, %1227: u64, %1228: u64):
    call @func.54(%1780)
    br bb217(%1219, %1220, %1221, %1222, %1223, %1224, %1225, %1226, %1227, %1228)
bb107(%1229: ptr, %1230: u32, %1231: u32, %1232: u64, %1233: ptr, %1234: u64, %1235: u64, %1236: u64, %1237: u64, %1238: u64):
    %2612 = load ptr, ptr %1781
    call @func.116(%1780, %2612)
    br bb218(%1229, %1230, %1231, %1232, %1233, %1234, %1235, %1236, %1237, %1238)
bb108(%1239: ptr, %1240: u32, %1241: u32, %1242: u64, %1243: ptr, %1244: u64, %1245: u64, %1246: u64, %1247: u64, %1248: u64):
    %2613 = call @func.55(%1780)
    br bb219(%1239, %1240, %1241, %1242, %1243, %1244, %1245, %1246, %1247, %1248, %2613)
bb109(%1249: ptr, %1250: u32, %1251: u32, %1252: u64, %1253: ptr, %1254: u64, %1255: u64, %1256: u64, %1257: u64, %1258: u64, %1259: u64):
    %2614 = const u64 0
    %2615 = icmp ugt u64 %1259, %2614
    condbr %2615, bb110(%1249, %1250, %1251, %1252, %1253, %1254, %1255, %1256, %1257, %1258, %1259), bb115(%1249, %1250, %1251, %1252, %1253, %1254, %1255, %1256, %1257, %1258)
bb110(%1260: ptr, %1261: u32, %1262: u32, %1263: u64, %1264: ptr, %1265: u64, %1266: u64, %1267: u64, %1268: u64, %1269: u64, %1270: u64):
    %2616 = const u64 1
    %2617, %2618 = sub.overflow u64 %1270, %2616
    store u64 %2617, ptr %1782
    %2619 = const i64 8
    %2620 = gep i8, ptr %1782, %2619
    store bool %2618, ptr %2620
    %2621 = const i64 8
    %2622 = gep i8, ptr %1782, %2621
    %2623 = load bool, ptr %2622
    %2624 = const bool false
    %2625 = icmp eq bool %2623, %2624
    condbr %2625, bb111(%1260, %1261, %1262, %1263, %1264, %1265, %1266, %1267, %1268, %1269), bb226
bb111(%1271: ptr, %1272: u32, %1273: u32, %1274: u64, %1275: ptr, %1276: u64, %1277: u64, %1278: u64, %1279: u64, %1280: u64):
    %2626 = load u64, ptr %1782
    %2627 = call @func.56(%1780, %2626)
    store ptr %2627, ptr %1783
    br bb112(%1271, %1272, %1273, %1274, %1275, %1276, %1277, %1278, %1279, %1280, %2626, %2626)
bb112(%1281: ptr, %1282: u32, %1283: u32, %1284: u64, %1285: ptr, %1286: u64, %1287: u64, %1288: u64, %1289: u64, %1290: u64, %1291: u64, %1292: u64):
    %2628 = load ptr, ptr %1783
    %2629 = load ptr, ptr %1783
    %2630 = const i64 8
    %2631 = gep i8, ptr %2629, %2630
    call @func.113(%1784, %2631, %1290, %1287, %1286, %1284, %1288, %1292)
    br bb113(%1281, %1282, %1283, %1284, %1285, %1286, %1287, %1288, %1289, %1290, %1291, %2628)
bb113(%1293: ptr, %1294: u32, %1295: u32, %1296: u64, %1297: ptr, %1298: u64, %1299: u64, %1300: u64, %1301: u64, %1302: u64, %1303: u64, %1304: ptr):
    %2632 = load i8, ptr %1304
    store i8 %2632, ptr %1786
    %2633 = const i64 1
    %2634 = gep i8, ptr %1304, %2633
    %2635 = const i64 1
    %2636 = gep i8, ptr %1786, %2635
    %2637 = load i8, ptr %2634
    store i8 %2637, ptr %2636
    %2638 = const bool false
    %2639 = load i64, ptr %1736
    store i64 %2639, ptr %1787
    %2640 = const i64 8
    %2641 = gep i8, ptr %1736, %2640
    %2642 = const i64 8
    %2643 = gep i8, ptr %1787, %2642
    %2644 = load i64, ptr %2641
    store i64 %2644, ptr %2643
    %2645 = const i64 16
    %2646 = gep i8, ptr %1736, %2645
    %2647 = const i64 16
    %2648 = gep i8, ptr %1787, %2647
    %2649 = load i64, ptr %2646
    store i64 %2649, ptr %2648
    %2650 = const i64 24
    %2651 = gep i8, ptr %1736, %2650
    %2652 = const i64 24
    %2653 = gep i8, ptr %1787, %2652
    %2654 = load i64, ptr %2651
    store i64 %2654, ptr %2653
    %2655 = const i64 32
    %2656 = gep i8, ptr %1736, %2655
    %2657 = const i64 32
    %2658 = gep i8, ptr %1787, %2657
    %2659 = load i64, ptr %2656
    store i64 %2659, ptr %2658
    call @func.117(%1785, %1786, %1784, %1787)
    br bb114(%1293, %1294, %1295, %1296, %1297, %1298, %1299, %1300, %1301, %1302, %1303)
bb114(%1305: ptr, %1306: u32, %1307: u32, %1308: u64, %1309: ptr, %1310: u64, %1311: u64, %1312: u64, %1313: u64, %1314: u64, %1315: u64):
    %2660 = const bool true
    %2661 = load i64, ptr %1785
    store i64 %2661, ptr %1736
    %2662 = const i64 8
    %2663 = gep i8, ptr %1785, %2662
    %2664 = const i64 8
    %2665 = gep i8, ptr %1736, %2664
    %2666 = load i64, ptr %2663
    store i64 %2666, ptr %2665
    %2667 = const i64 16
    %2668 = gep i8, ptr %1785, %2667
    %2669 = const i64 16
    %2670 = gep i8, ptr %1736, %2669
    %2671 = load i64, ptr %2668
    store i64 %2671, ptr %2670
    %2672 = const i64 24
    %2673 = gep i8, ptr %1785, %2672
    %2674 = const i64 24
    %2675 = gep i8, ptr %1736, %2674
    %2676 = load i64, ptr %2673
    store i64 %2676, ptr %2675
    %2677 = const i64 32
    %2678 = gep i8, ptr %1785, %2677
    %2679 = const i64 32
    %2680 = gep i8, ptr %1736, %2679
    %2681 = load i64, ptr %2678
    store i64 %2681, ptr %2680
    br bb109(%1305, %1306, %1307, %1308, %1309, %1310, %1311, %1312, %1313, %1314, %1315)
bb115(%1316: ptr, %1317: u32, %1318: u32, %1319: u64, %1320: ptr, %1321: u64, %1322: u64, %1323: u64, %1324: u64, %1325: u64):
    %2682 = const bool false
    %2683 = load i64, ptr %1720
    store i64 %2683, ptr %1789
    %2684 = const i64 8
    %2685 = gep i8, ptr %1720, %2684
    %2686 = const i64 8
    %2687 = gep i8, ptr %1789, %2686
    %2688 = load i64, ptr %2685
    store i64 %2688, ptr %2687
    %2689 = const i64 16
    %2690 = gep i8, ptr %1720, %2689
    %2691 = const i64 16
    %2692 = gep i8, ptr %1789, %2691
    %2693 = load i64, ptr %2690
    store i64 %2693, ptr %2692
    %2694 = const i64 24
    %2695 = gep i8, ptr %1720, %2694
    %2696 = const i64 24
    %2697 = gep i8, ptr %1789, %2696
    %2698 = load i64, ptr %2695
    store i64 %2698, ptr %2697
    %2699 = const i64 32
    %2700 = gep i8, ptr %1720, %2699
    %2701 = const i64 32
    %2702 = gep i8, ptr %1789, %2701
    %2703 = load i64, ptr %2700
    store i64 %2703, ptr %2702
    %2704 = const bool false
    %2705 = load i64, ptr %1736
    store i64 %2705, ptr %1790
    %2706 = const i64 8
    %2707 = gep i8, ptr %1736, %2706
    %2708 = const i64 8
    %2709 = gep i8, ptr %1790, %2708
    %2710 = load i64, ptr %2707
    store i64 %2710, ptr %2709
    %2711 = const i64 16
    %2712 = gep i8, ptr %1736, %2711
    %2713 = const i64 16
    %2714 = gep i8, ptr %1790, %2713
    %2715 = load i64, ptr %2712
    store i64 %2715, ptr %2714
    %2716 = const i64 24
    %2717 = gep i8, ptr %1736, %2716
    %2718 = const i64 24
    %2719 = gep i8, ptr %1790, %2718
    %2720 = load i64, ptr %2717
    store i64 %2720, ptr %2719
    %2721 = const i64 32
    %2722 = gep i8, ptr %1736, %2721
    %2723 = const i64 32
    %2724 = gep i8, ptr %1790, %2723
    %2725 = load i64, ptr %2722
    store i64 %2725, ptr %2724
    call @func.84(%1788, %1789, %1790)
    br bb116(%1316, %1317, %1318, %1319, %1320, %1321, %1322, %1323, %1324, %1325)
bb116(%1326: ptr, %1327: u32, %1328: u32, %1329: u64, %1330: ptr, %1331: u64, %1332: u64, %1333: u64, %1334: u64, %1335: u64):
    %2726 = const bool true
    %2727 = load i64, ptr %1788
    store i64 %2727, ptr %1720
    %2728 = const i64 8
    %2729 = gep i8, ptr %1788, %2728
    %2730 = const i64 8
    %2731 = gep i8, ptr %1720, %2730
    %2732 = load i64, ptr %2729
    store i64 %2732, ptr %2731
    %2733 = const i64 16
    %2734 = gep i8, ptr %1788, %2733
    %2735 = const i64 16
    %2736 = gep i8, ptr %1720, %2735
    %2737 = load i64, ptr %2734
    store i64 %2737, ptr %2736
    %2738 = const i64 24
    %2739 = gep i8, ptr %1788, %2738
    %2740 = const i64 24
    %2741 = gep i8, ptr %1720, %2740
    %2742 = load i64, ptr %2739
    store i64 %2742, ptr %2741
    %2743 = const i64 32
    %2744 = gep i8, ptr %1788, %2743
    %2745 = const i64 32
    %2746 = gep i8, ptr %1720, %2745
    %2747 = load i64, ptr %2744
    store i64 %2747, ptr %2746
    br bb117(%1326, %1327, %1328, %1329, %1330, %1331, %1332, %1333, %1334, %1335)
bb117(%1336: ptr, %1337: u32, %1338: u32, %1339: u64, %1340: ptr, %1341: u64, %1342: u64, %1343: u64, %1344: u64, %1345: u64):
    %2748 = const bool false
    %2749 = const bool false
    br bb118(%1336, %1337, %1338, %1339, %1340, %1341, %1342, %1343, %1344, %1345)
bb118(%1346: ptr, %1347: u32, %1348: u32, %1349: u64, %1350: ptr, %1351: u64, %1352: u64, %1353: u64, %1354: u64, %1355: u64):
    %2750 = const u64 1
    %2751, %2752 = add.overflow u64 %1355, %2750
    store u64 %2751, ptr %1791
    %2753 = const i64 8
    %2754 = gep i8, ptr %1791, %2753
    store bool %2752, ptr %2754
    %2755 = const i64 8
    %2756 = gep i8, ptr %1791, %2755
    %2757 = load bool, ptr %2756
    %2758 = const bool false
    %2759 = icmp eq bool %2757, %2758
    condbr %2759, bb119(%1346, %1347, %1348, %1349, %1350, %1351, %1352, %1353, %1354), bb226
bb119(%1356: ptr, %1357: u32, %1358: u32, %1359: u64, %1360: ptr, %1361: u64, %1362: u64, %1363: u64, %1364: u64):
    %2760 = load u64, ptr %1791
    br bb25(%1356, %1357, %1358, %1359, %1360, %1361, %1362, %1363, %1364, %2760)
bb120(%1365: u64, %1366: ptr, %1367: u64, %1368: u64, %1369: u64):
    %2761 = const i32 0
    store i32 %2761, ptr %1793
    call @func.118(%1792, %1793)
    br bb121(%1365, %1366, %1367, %1368, %1369)
bb121(%1370: u64, %1371: ptr, %1372: u64, %1373: u64, %1374: u64):
    call @func.78(%1794, %1371)
    br bb122(%1370, %1372, %1373, %1374)
bb122(%1375: u64, %1376: u64, %1377: u64, %1378: u64):
    call @func.57(%1795)
    br bb123(%1375, %1376, %1377, %1378)
bb123(%1379: u64, %1380: u64, %1381: u64, %1382: u64):
    %2762 = const u64 0
    br bb124(%1379, %1380, %1381, %1382, %2762)
bb124(%1383: u64, %1384: u64, %1385: u64, %1386: u64, %1387: u64):
    %2763 = icmp ult u64 %1387, %1385
    condbr %2763, bb125(%1383, %1384, %1385, %1386, %1387), bb137(%1383, %1384, %1386)
bb125(%1388: u64, %1389: u64, %1390: u64, %1391: u64, %1392: u64):
    store ptr %1794, ptr %1796
    %2764 = load ptr, ptr %1796
    %2765 = load i8, ptr %2764
    %2766 = sext i8 %2765 to i64
    switch %2766 [ 6: bb127(%1388, %1389, %1390, %1391, %1392) default: bb126(%1388, %1389, %1390, %1391, %1392) ]
bb126(%1393: u64, %1394: u64, %1395: u64, %1396: u64, %1397: u64):
    call @func.78(%1799, %1792)
    br bb134(%1393, %1394, %1395, %1396, %1397, %1795)
bb127(%1398: u64, %1399: u64, %1400: u64, %1401: u64, %1402: u64):
    %2767 = load ptr, ptr %1796
    %2768 = const i64 8
    %2769 = gep i8, ptr %2767, %2768
    %2770 = load ptr, ptr %1796
    %2771 = const i64 16
    %2772 = gep i8, ptr %2770, %2771
    %2773 = load ptr, ptr %2769
    %2774 = const i64 16
    %2775 = gep i8, ptr %2773, %2774
    br bb128(%1398, %1399, %1400, %1401, %1402, %2772, %1795, %2775)
bb128(%1403: u64, %1404: u64, %1405: u64, %1406: u64, %1407: u64, %1408: ptr, %1409: ptr, %1410: ptr):
    call @func.78(%1797, %1410)
    br bb129(%1403, %1404, %1405, %1406, %1407, %1408, %1409)
bb129(%1411: u64, %1412: u64, %1413: u64, %1414: u64, %1415: u64, %1416: ptr, %1417: ptr):
    call @func.58(%1417, %1797)
    br bb130(%1411, %1412, %1413, %1414, %1415, %1416)
bb130(%1418: u64, %1419: u64, %1420: u64, %1421: u64, %1422: u64, %1423: ptr):
    %2776 = load ptr, ptr %1423
    %2777 = const i64 16
    %2778 = gep i8, ptr %2776, %2777
    br bb131(%1418, %1419, %1420, %1421, %1422, %2778)
bb131(%1424: u64, %1425: u64, %1426: u64, %1427: u64, %1428: u64, %1429: ptr):
    call @func.78(%1798, %1429)
    br bb132(%1424, %1425, %1426, %1427, %1428)
bb132(%1430: u64, %1431: u64, %1432: u64, %1433: u64, %1434: u64):
    br bb133(%1430, %1431, %1432, %1433, %1434)
bb133(%1435: u64, %1436: u64, %1437: u64, %1438: u64, %1439: u64):
    %2779 = load i64, ptr %1798
    store i64 %2779, ptr %1794
    %2780 = const i64 8
    %2781 = gep i8, ptr %1798, %2780
    %2782 = const i64 8
    %2783 = gep i8, ptr %1794, %2782
    %2784 = load i64, ptr %2781
    store i64 %2784, ptr %2783
    %2785 = const i64 16
    %2786 = gep i8, ptr %1798, %2785
    %2787 = const i64 16
    %2788 = gep i8, ptr %1794, %2787
    %2789 = load i64, ptr %2786
    store i64 %2789, ptr %2788
    %2790 = const i64 24
    %2791 = gep i8, ptr %1798, %2790
    %2792 = const i64 24
    %2793 = gep i8, ptr %1794, %2792
    %2794 = load i64, ptr %2791
    store i64 %2794, ptr %2793
    %2795 = const i64 32
    %2796 = gep i8, ptr %1798, %2795
    %2797 = const i64 32
    %2798 = gep i8, ptr %1794, %2797
    %2799 = load i64, ptr %2796
    store i64 %2799, ptr %2798
    br bb135(%1435, %1436, %1437, %1438, %1439)
bb134(%1440: u64, %1441: u64, %1442: u64, %1443: u64, %1444: u64, %1445: ptr):
    call @func.58(%1445, %1799)
    br bb220(%1440, %1441, %1442, %1443, %1444)
bb135(%1446: u64, %1447: u64, %1448: u64, %1449: u64, %1450: u64):
    %2800 = const u64 1
    %2801, %2802 = add.overflow u64 %1450, %2800
    store u64 %2801, ptr %1800
    %2803 = const i64 8
    %2804 = gep i8, ptr %1800, %2803
    store bool %2802, ptr %2804
    %2805 = const i64 8
    %2806 = gep i8, ptr %1800, %2805
    %2807 = load bool, ptr %2806
    %2808 = const bool false
    %2809 = icmp eq bool %2807, %2808
    condbr %2809, bb136(%1446, %1447, %1448, %1449), bb226
bb136(%1451: u64, %1452: u64, %1453: u64, %1454: u64):
    %2810 = load u64, ptr %1800
    br bb124(%1451, %1452, %1453, %1454, %2810)
bb137(%1455: u64, %1456: u64, %1457: u64):
    call @func.57(%1801)
    br bb138(%1455, %1456, %1457)
bb138(%1458: u64, %1459: u64, %1460: u64):
    %2811 = const u64 0
    br bb139(%1458, %1459, %1460, %2811)
bb139(%1461: u64, %1462: u64, %1463: u64, %1464: u64):
    %2812 = icmp ult u64 %1464, %1463
    condbr %2812, bb140(%1461, %1462, %1463, %1464), bb152(%1461, %1462, %1463)
bb140(%1465: u64, %1466: u64, %1467: u64, %1468: u64):
    store ptr %1794, ptr %1802
    %2813 = load ptr, ptr %1802
    %2814 = load i8, ptr %2813
    %2815 = sext i8 %2814 to i64
    switch %2815 [ 6: bb142(%1465, %1466, %1467, %1468) default: bb141(%1465, %1466, %1467, %1468) ]
bb141(%1469: u64, %1470: u64, %1471: u64, %1472: u64):
    call @func.78(%1805, %1792)
    br bb149(%1469, %1470, %1471, %1472, %1801)
bb142(%1473: u64, %1474: u64, %1475: u64, %1476: u64):
    %2816 = load ptr, ptr %1802
    %2817 = const i64 8
    %2818 = gep i8, ptr %2816, %2817
    %2819 = load ptr, ptr %1802
    %2820 = const i64 16
    %2821 = gep i8, ptr %2819, %2820
    %2822 = load ptr, ptr %2818
    %2823 = const i64 16
    %2824 = gep i8, ptr %2822, %2823
    br bb143(%1473, %1474, %1475, %1476, %2821, %1801, %2824)
bb143(%1477: u64, %1478: u64, %1479: u64, %1480: u64, %1481: ptr, %1482: ptr, %1483: ptr):
    call @func.78(%1803, %1483)
    br bb144(%1477, %1478, %1479, %1480, %1481, %1482)
bb144(%1484: u64, %1485: u64, %1486: u64, %1487: u64, %1488: ptr, %1489: ptr):
    call @func.58(%1489, %1803)
    br bb145(%1484, %1485, %1486, %1487, %1488)
bb145(%1490: u64, %1491: u64, %1492: u64, %1493: u64, %1494: ptr):
    %2825 = load ptr, ptr %1494
    %2826 = const i64 16
    %2827 = gep i8, ptr %2825, %2826
    br bb146(%1490, %1491, %1492, %1493, %2827)
bb146(%1495: u64, %1496: u64, %1497: u64, %1498: u64, %1499: ptr):
    call @func.78(%1804, %1499)
    br bb147(%1495, %1496, %1497, %1498)
bb147(%1500: u64, %1501: u64, %1502: u64, %1503: u64):
    br bb148(%1500, %1501, %1502, %1503)
bb148(%1504: u64, %1505: u64, %1506: u64, %1507: u64):
    %2828 = load i64, ptr %1804
    store i64 %2828, ptr %1794
    %2829 = const i64 8
    %2830 = gep i8, ptr %1804, %2829
    %2831 = const i64 8
    %2832 = gep i8, ptr %1794, %2831
    %2833 = load i64, ptr %2830
    store i64 %2833, ptr %2832
    %2834 = const i64 16
    %2835 = gep i8, ptr %1804, %2834
    %2836 = const i64 16
    %2837 = gep i8, ptr %1794, %2836
    %2838 = load i64, ptr %2835
    store i64 %2838, ptr %2837
    %2839 = const i64 24
    %2840 = gep i8, ptr %1804, %2839
    %2841 = const i64 24
    %2842 = gep i8, ptr %1794, %2841
    %2843 = load i64, ptr %2840
    store i64 %2843, ptr %2842
    %2844 = const i64 32
    %2845 = gep i8, ptr %1804, %2844
    %2846 = const i64 32
    %2847 = gep i8, ptr %1794, %2846
    %2848 = load i64, ptr %2845
    store i64 %2848, ptr %2847
    br bb150(%1504, %1505, %1506, %1507)
bb149(%1508: u64, %1509: u64, %1510: u64, %1511: u64, %1512: ptr):
    call @func.58(%1512, %1805)
    br bb221(%1508, %1509, %1510, %1511)
bb150(%1513: u64, %1514: u64, %1515: u64, %1516: u64):
    %2849 = const u64 1
    %2850, %2851 = add.overflow u64 %1516, %2849
    store u64 %2850, ptr %1806
    %2852 = const i64 8
    %2853 = gep i8, ptr %1806, %2852
    store bool %2851, ptr %2853
    %2854 = const i64 8
    %2855 = gep i8, ptr %1806, %2854
    %2856 = load bool, ptr %2855
    %2857 = const bool false
    %2858 = icmp eq bool %2856, %2857
    condbr %2858, bb151(%1513, %1514, %1515), bb226
bb151(%1517: u64, %1518: u64, %1519: u64):
    %2859 = load u64, ptr %1806
    br bb139(%1517, %1518, %1519, %2859)
bb152(%1520: u64, %1521: u64, %1522: u64):
    call @func.57(%1807)
    br bb153(%1520, %1521, %1522)
bb153(%1523: u64, %1524: u64, %1525: u64):
    %2860 = const u64 0
    br bb154(%1523, %1524, %1525, %2860)
bb154(%1526: u64, %1527: u64, %1528: u64, %1529: u64):
    %2861 = icmp ult u64 %1529, %1526
    condbr %2861, bb155(%1526, %1527, %1528, %1529), bb167(%1526, %1527, %1528)
bb155(%1530: u64, %1531: u64, %1532: u64, %1533: u64):
    store ptr %1794, ptr %1808
    %2862 = load ptr, ptr %1808
    %2863 = load i8, ptr %2862
    %2864 = sext i8 %2863 to i64
    switch %2864 [ 6: bb157(%1530, %1531, %1532, %1533) default: bb156(%1530, %1531, %1532, %1533) ]
bb156(%1534: u64, %1535: u64, %1536: u64, %1537: u64):
    call @func.78(%1811, %1792)
    br bb164(%1534, %1535, %1536, %1537, %1807)
bb157(%1538: u64, %1539: u64, %1540: u64, %1541: u64):
    %2865 = load ptr, ptr %1808
    %2866 = const i64 8
    %2867 = gep i8, ptr %2865, %2866
    %2868 = load ptr, ptr %1808
    %2869 = const i64 16
    %2870 = gep i8, ptr %2868, %2869
    %2871 = load ptr, ptr %2867
    %2872 = const i64 16
    %2873 = gep i8, ptr %2871, %2872
    br bb158(%1538, %1539, %1540, %1541, %2870, %1807, %2873)
bb158(%1542: u64, %1543: u64, %1544: u64, %1545: u64, %1546: ptr, %1547: ptr, %1548: ptr):
    call @func.78(%1809, %1548)
    br bb159(%1542, %1543, %1544, %1545, %1546, %1547)
bb159(%1549: u64, %1550: u64, %1551: u64, %1552: u64, %1553: ptr, %1554: ptr):
    call @func.58(%1554, %1809)
    br bb160(%1549, %1550, %1551, %1552, %1553)
bb160(%1555: u64, %1556: u64, %1557: u64, %1558: u64, %1559: ptr):
    %2874 = load ptr, ptr %1559
    %2875 = const i64 16
    %2876 = gep i8, ptr %2874, %2875
    br bb161(%1555, %1556, %1557, %1558, %2876)
bb161(%1560: u64, %1561: u64, %1562: u64, %1563: u64, %1564: ptr):
    call @func.78(%1810, %1564)
    br bb162(%1560, %1561, %1562, %1563)
bb162(%1565: u64, %1566: u64, %1567: u64, %1568: u64):
    br bb163(%1565, %1566, %1567, %1568)
bb163(%1569: u64, %1570: u64, %1571: u64, %1572: u64):
    %2877 = load i64, ptr %1810
    store i64 %2877, ptr %1794
    %2878 = const i64 8
    %2879 = gep i8, ptr %1810, %2878
    %2880 = const i64 8
    %2881 = gep i8, ptr %1794, %2880
    %2882 = load i64, ptr %2879
    store i64 %2882, ptr %2881
    %2883 = const i64 16
    %2884 = gep i8, ptr %1810, %2883
    %2885 = const i64 16
    %2886 = gep i8, ptr %1794, %2885
    %2887 = load i64, ptr %2884
    store i64 %2887, ptr %2886
    %2888 = const i64 24
    %2889 = gep i8, ptr %1810, %2888
    %2890 = const i64 24
    %2891 = gep i8, ptr %1794, %2890
    %2892 = load i64, ptr %2889
    store i64 %2892, ptr %2891
    %2893 = const i64 32
    %2894 = gep i8, ptr %1810, %2893
    %2895 = const i64 32
    %2896 = gep i8, ptr %1794, %2895
    %2897 = load i64, ptr %2894
    store i64 %2897, ptr %2896
    br bb165(%1569, %1570, %1571, %1572)
bb164(%1573: u64, %1574: u64, %1575: u64, %1576: u64, %1577: ptr):
    call @func.58(%1577, %1811)
    br bb222(%1573, %1574, %1575, %1576)
bb165(%1578: u64, %1579: u64, %1580: u64, %1581: u64):
    %2898 = const u64 1
    %2899, %2900 = add.overflow u64 %1581, %2898
    store u64 %2899, ptr %1812
    %2901 = const i64 8
    %2902 = gep i8, ptr %1812, %2901
    store bool %2900, ptr %2902
    %2903 = const i64 8
    %2904 = gep i8, ptr %1812, %2903
    %2905 = load bool, ptr %2904
    %2906 = const bool false
    %2907 = icmp eq bool %2905, %2906
    condbr %2907, bb166(%1578, %1579, %1580), bb226
bb166(%1582: u64, %1583: u64, %1584: u64):
    %2908 = load u64, ptr %1812
    br bb154(%1582, %1583, %1584, %2908)
bb167(%1585: u64, %1586: u64, %1587: u64):
    %2909 = const bool false
    %2910 = const bool true
    %2911 = load i64, ptr %1720
    store i64 %2911, ptr %1813
    %2912 = const i64 8
    %2913 = gep i8, ptr %1720, %2912
    %2914 = const i64 8
    %2915 = gep i8, ptr %1813, %2914
    %2916 = load i64, ptr %2913
    store i64 %2916, ptr %2915
    %2917 = const i64 16
    %2918 = gep i8, ptr %1720, %2917
    %2919 = const i64 16
    %2920 = gep i8, ptr %1813, %2919
    %2921 = load i64, ptr %2918
    store i64 %2921, ptr %2920
    %2922 = const i64 24
    %2923 = gep i8, ptr %1720, %2922
    %2924 = const i64 24
    %2925 = gep i8, ptr %1813, %2924
    %2926 = load i64, ptr %2923
    store i64 %2926, ptr %2925
    %2927 = const i64 32
    %2928 = gep i8, ptr %1720, %2927
    %2929 = const i64 32
    %2930 = gep i8, ptr %1813, %2929
    %2931 = load i64, ptr %2928
    store i64 %2931, ptr %2930
    %2932, %2933 = add.overflow u64 %1587, %1585
    store u64 %2932, ptr %1814
    %2934 = const i64 8
    %2935 = gep i8, ptr %1814, %2934
    store bool %2933, ptr %2935
    %2936 = const i64 8
    %2937 = gep i8, ptr %1814, %2936
    %2938 = load bool, ptr %2937
    %2939 = const bool false
    %2940 = icmp eq bool %2938, %2939
    condbr %2940, bb168(%1586), bb226
bb168(%1588: u64):
    %2941 = load u64, ptr %1814
    %2942 = call @func.103(%2941)
    br bb169(%1588, %2942)
bb169(%1589: u64, %1590: u32):
    br bb170(%1590, %1589)
bb170(%1591: u32, %1592: u64):
    %2943 = const u64 0
    %2944 = icmp ugt u64 %1592, %2943
    condbr %2944, bb171(%1591, %1592), bb184
bb171(%1593: u32, %1594: u64):
    %2945 = const u64 1
    %2946, %2947 = sub.overflow u64 %1594, %2945
    store u64 %2946, ptr %1815
    %2948 = const i64 8
    %2949 = gep i8, ptr %1815, %2948
    store bool %2947, ptr %2949
    %2950 = const i64 8
    %2951 = gep i8, ptr %1815, %2950
    %2952 = load bool, ptr %2951
    %2953 = const bool false
    %2954 = icmp eq bool %2952, %2953
    condbr %2954, bb172(%1593), bb226
bb172(%1595: u32):
    %2955 = load u64, ptr %1815
    call @func.50(%1817, %8, %2955)
    br bb173(%1595, %2955, %2955)
bb173(%1596: u32, %1597: u64, %1598: u64):
    %2956 = load i64, ptr %1817
    %2957 = const i64 0
    %2958 = icmp eq i64 %2956, %2957
    %2959 = const i64 0
    %2960 = const i64 1
    %2961 = select i64 %2958, %2959, %2960
    switch %2961 [ 0: bb174(%1596, %1597) 1: bb175(%1596, %1597, %1598) default: bb30 ]
bb174(%1599: u32, %1600: u64):
    call @func.78(%1816, %1792)
    br bb180(%1599, %1600)
bb175(%1601: u32, %1602: u64, %1603: u64):
    %2962 = load ptr, ptr %1817
    %2963 = const u32 0
    %2964 = icmp ugt u32 %1601, %2963
    condbr %2964, bb176(%1601, %1602, %1603, %2962), bb178(%1601, %1602, %2962)
bb176(%1604: u32, %1605: u64, %1606: u64, %1607: ptr):
    %2965 = trunc u64 %1606 to u32
    call @func.105(%1816, %1607, %2965, %1604)
    br bb177(%1604, %1605)
bb177(%1608: u32, %1609: u64):
    %2966 = const bool true
    br bb181(%1608, %1609)
bb178(%1610: u32, %1611: u64, %1612: ptr):
    call @func.78(%1816, %1612)
    br bb179(%1610, %1611)
bb179(%1613: u32, %1614: u64):
    %2967 = const bool true
    br bb181(%1613, %1614)
bb180(%1615: u32, %1616: u64):
    %2968 = const bool true
    br bb181(%1615, %1616)
bb181(%1617: u32, %1618: u64):
    call @func.85(%1819)
    br bb182(%1617, %1618)
bb182(%1619: u32, %1620: u64):
    %2969 = const bool false
    %2970 = load i64, ptr %1816
    store i64 %2970, ptr %1820
    %2971 = const i64 8
    %2972 = gep i8, ptr %1816, %2971
    %2973 = const i64 8
    %2974 = gep i8, ptr %1820, %2973
    %2975 = load i64, ptr %2972
    store i64 %2975, ptr %2974
    %2976 = const i64 16
    %2977 = gep i8, ptr %1816, %2976
    %2978 = const i64 16
    %2979 = gep i8, ptr %1820, %2978
    %2980 = load i64, ptr %2977
    store i64 %2980, ptr %2979
    %2981 = const i64 24
    %2982 = gep i8, ptr %1816, %2981
    %2983 = const i64 24
    %2984 = gep i8, ptr %1820, %2983
    %2985 = load i64, ptr %2982
    store i64 %2985, ptr %2984
    %2986 = const i64 32
    %2987 = gep i8, ptr %1816, %2986
    %2988 = const i64 32
    %2989 = gep i8, ptr %1820, %2988
    %2990 = load i64, ptr %2987
    store i64 %2990, ptr %2989
    %2991 = const bool false
    %2992 = load i64, ptr %1813
    store i64 %2992, ptr %1821
    %2993 = const i64 8
    %2994 = gep i8, ptr %1813, %2993
    %2995 = const i64 8
    %2996 = gep i8, ptr %1821, %2995
    %2997 = load i64, ptr %2994
    store i64 %2997, ptr %2996
    %2998 = const i64 16
    %2999 = gep i8, ptr %1813, %2998
    %3000 = const i64 16
    %3001 = gep i8, ptr %1821, %3000
    %3002 = load i64, ptr %2999
    store i64 %3002, ptr %3001
    %3003 = const i64 24
    %3004 = gep i8, ptr %1813, %3003
    %3005 = const i64 24
    %3006 = gep i8, ptr %1821, %3005
    %3007 = load i64, ptr %3004
    store i64 %3007, ptr %3006
    %3008 = const i64 32
    %3009 = gep i8, ptr %1813, %3008
    %3010 = const i64 32
    %3011 = gep i8, ptr %1821, %3010
    %3012 = load i64, ptr %3009
    store i64 %3012, ptr %3011
    call @func.117(%1818, %1819, %1820, %1821)
    br bb183(%1619, %1620)
bb183(%1621: u32, %1622: u64):
    %3013 = const bool true
    %3014 = load i64, ptr %1818
    store i64 %3014, ptr %1813
    %3015 = const i64 8
    %3016 = gep i8, ptr %1818, %3015
    %3017 = const i64 8
    %3018 = gep i8, ptr %1813, %3017
    %3019 = load i64, ptr %3016
    store i64 %3019, ptr %3018
    %3020 = const i64 16
    %3021 = gep i8, ptr %1818, %3020
    %3022 = const i64 16
    %3023 = gep i8, ptr %1813, %3022
    %3024 = load i64, ptr %3021
    store i64 %3024, ptr %3023
    %3025 = const i64 24
    %3026 = gep i8, ptr %1818, %3025
    %3027 = const i64 24
    %3028 = gep i8, ptr %1813, %3027
    %3029 = load i64, ptr %3026
    store i64 %3029, ptr %3028
    %3030 = const i64 32
    %3031 = gep i8, ptr %1818, %3030
    %3032 = const i64 32
    %3033 = gep i8, ptr %1813, %3032
    %3034 = load i64, ptr %3031
    store i64 %3034, ptr %3033
    %3035 = const bool false
    br bb170(%1621, %1622)
bb184:
    %3036 = call @func.52(%1807)
    br bb223(%3036)
bb185(%1623: u64):
    %3037 = const u64 0
    %3038 = icmp ugt u64 %1623, %3037
    condbr %3038, bb186(%1623), bb192
bb186(%1624: u64):
    %3039 = const u64 1
    %3040, %3041 = sub.overflow u64 %1624, %3039
    store u64 %3040, ptr %1822
    %3042 = const i64 8
    %3043 = gep i8, ptr %1822, %3042
    store bool %3041, ptr %3043
    %3044 = const i64 8
    %3045 = gep i8, ptr %1822, %3044
    %3046 = load bool, ptr %3045
    %3047 = const bool false
    %3048 = icmp eq bool %3046, %3047
    condbr %3048, bb187, bb226
bb187:
    %3049 = load u64, ptr %1822
    call @func.85(%1824)
    br bb188(%3049)
bb188(%1625: u64):
    %3050 = call @func.53(%1807, %1625)
    br bb189(%1625, %3050)
bb189(%1626: u64, %1627: ptr):
    call @func.78(%1825, %1627)
    br bb190(%1626)
bb190(%1628: u64):
    %3051 = const bool false
    %3052 = load i64, ptr %1813
    store i64 %3052, ptr %1826
    %3053 = const i64 8
    %3054 = gep i8, ptr %1813, %3053
    %3055 = const i64 8
    %3056 = gep i8, ptr %1826, %3055
    %3057 = load i64, ptr %3054
    store i64 %3057, ptr %3056
    %3058 = const i64 16
    %3059 = gep i8, ptr %1813, %3058
    %3060 = const i64 16
    %3061 = gep i8, ptr %1826, %3060
    %3062 = load i64, ptr %3059
    store i64 %3062, ptr %3061
    %3063 = const i64 24
    %3064 = gep i8, ptr %1813, %3063
    %3065 = const i64 24
    %3066 = gep i8, ptr %1826, %3065
    %3067 = load i64, ptr %3064
    store i64 %3067, ptr %3066
    %3068 = const i64 32
    %3069 = gep i8, ptr %1813, %3068
    %3070 = const i64 32
    %3071 = gep i8, ptr %1826, %3070
    %3072 = load i64, ptr %3069
    store i64 %3072, ptr %3071
    call @func.117(%1823, %1824, %1825, %1826)
    br bb191(%1628)
bb191(%1629: u64):
    %3073 = const bool true
    %3074 = load i64, ptr %1823
    store i64 %3074, ptr %1813
    %3075 = const i64 8
    %3076 = gep i8, ptr %1823, %3075
    %3077 = const i64 8
    %3078 = gep i8, ptr %1813, %3077
    %3079 = load i64, ptr %3076
    store i64 %3079, ptr %3078
    %3080 = const i64 16
    %3081 = gep i8, ptr %1823, %3080
    %3082 = const i64 16
    %3083 = gep i8, ptr %1813, %3082
    %3084 = load i64, ptr %3081
    store i64 %3084, ptr %3083
    %3085 = const i64 24
    %3086 = gep i8, ptr %1823, %3085
    %3087 = const i64 24
    %3088 = gep i8, ptr %1813, %3087
    %3089 = load i64, ptr %3086
    store i64 %3089, ptr %3088
    %3090 = const i64 32
    %3091 = gep i8, ptr %1823, %3090
    %3092 = const i64 32
    %3093 = gep i8, ptr %1813, %3092
    %3094 = load i64, ptr %3091
    store i64 %3094, ptr %3093
    br bb185(%1629)
bb192:
    %3095 = call @func.52(%1801)
    br bb224(%3095)
bb193(%1630: u64):
    %3096 = const u64 0
    %3097 = icmp ugt u64 %1630, %3096
    condbr %3097, bb194(%1630), bb200
bb194(%1631: u64):
    %3098 = const u64 1
    %3099, %3100 = sub.overflow u64 %1631, %3098
    store u64 %3099, ptr %1827
    %3101 = const i64 8
    %3102 = gep i8, ptr %1827, %3101
    store bool %3100, ptr %3102
    %3103 = const i64 8
    %3104 = gep i8, ptr %1827, %3103
    %3105 = load bool, ptr %3104
    %3106 = const bool false
    %3107 = icmp eq bool %3105, %3106
    condbr %3107, bb195, bb226
bb195:
    %3108 = load u64, ptr %1827
    call @func.85(%1829)
    br bb196(%3108)
bb196(%1632: u64):
    %3109 = call @func.53(%1801, %1632)
    br bb197(%1632, %3109)
bb197(%1633: u64, %1634: ptr):
    call @func.78(%1830, %1634)
    br bb198(%1633)
bb198(%1635: u64):
    %3110 = const bool false
    %3111 = load i64, ptr %1813
    store i64 %3111, ptr %1831
    %3112 = const i64 8
    %3113 = gep i8, ptr %1813, %3112
    %3114 = const i64 8
    %3115 = gep i8, ptr %1831, %3114
    %3116 = load i64, ptr %3113
    store i64 %3116, ptr %3115
    %3117 = const i64 16
    %3118 = gep i8, ptr %1813, %3117
    %3119 = const i64 16
    %3120 = gep i8, ptr %1831, %3119
    %3121 = load i64, ptr %3118
    store i64 %3121, ptr %3120
    %3122 = const i64 24
    %3123 = gep i8, ptr %1813, %3122
    %3124 = const i64 24
    %3125 = gep i8, ptr %1831, %3124
    %3126 = load i64, ptr %3123
    store i64 %3126, ptr %3125
    %3127 = const i64 32
    %3128 = gep i8, ptr %1813, %3127
    %3129 = const i64 32
    %3130 = gep i8, ptr %1831, %3129
    %3131 = load i64, ptr %3128
    store i64 %3131, ptr %3130
    call @func.117(%1828, %1829, %1830, %1831)
    br bb199(%1635)
bb199(%1636: u64):
    %3132 = const bool true
    %3133 = load i64, ptr %1828
    store i64 %3133, ptr %1813
    %3134 = const i64 8
    %3135 = gep i8, ptr %1828, %3134
    %3136 = const i64 8
    %3137 = gep i8, ptr %1813, %3136
    %3138 = load i64, ptr %3135
    store i64 %3138, ptr %3137
    %3139 = const i64 16
    %3140 = gep i8, ptr %1828, %3139
    %3141 = const i64 16
    %3142 = gep i8, ptr %1813, %3141
    %3143 = load i64, ptr %3140
    store i64 %3143, ptr %3142
    %3144 = const i64 24
    %3145 = gep i8, ptr %1828, %3144
    %3146 = const i64 24
    %3147 = gep i8, ptr %1813, %3146
    %3148 = load i64, ptr %3145
    store i64 %3148, ptr %3147
    %3149 = const i64 32
    %3150 = gep i8, ptr %1828, %3149
    %3151 = const i64 32
    %3152 = gep i8, ptr %1813, %3151
    %3153 = load i64, ptr %3150
    store i64 %3153, ptr %3152
    br bb193(%1636)
bb200:
    %3154 = call @func.52(%1795)
    br bb225(%3154)
bb201(%1637: u64):
    %3155 = const u64 0
    %3156 = icmp ugt u64 %1637, %3155
    condbr %3156, bb202(%1637), bb208
bb202(%1638: u64):
    %3157 = const u64 1
    %3158, %3159 = sub.overflow u64 %1638, %3157
    store u64 %3158, ptr %1832
    %3160 = const i64 8
    %3161 = gep i8, ptr %1832, %3160
    store bool %3159, ptr %3161
    %3162 = const i64 8
    %3163 = gep i8, ptr %1832, %3162
    %3164 = load bool, ptr %3163
    %3165 = const bool false
    %3166 = icmp eq bool %3164, %3165
    condbr %3166, bb203, bb226
bb203:
    %3167 = load u64, ptr %1832
    call @func.85(%1834)
    br bb204(%3167)
bb204(%1639: u64):
    %3168 = call @func.53(%1795, %1639)
    br bb205(%1639, %3168)
bb205(%1640: u64, %1641: ptr):
    call @func.78(%1835, %1641)
    br bb206(%1640)
bb206(%1642: u64):
    %3169 = const bool false
    %3170 = load i64, ptr %1813
    store i64 %3170, ptr %1836
    %3171 = const i64 8
    %3172 = gep i8, ptr %1813, %3171
    %3173 = const i64 8
    %3174 = gep i8, ptr %1836, %3173
    %3175 = load i64, ptr %3172
    store i64 %3175, ptr %3174
    %3176 = const i64 16
    %3177 = gep i8, ptr %1813, %3176
    %3178 = const i64 16
    %3179 = gep i8, ptr %1836, %3178
    %3180 = load i64, ptr %3177
    store i64 %3180, ptr %3179
    %3181 = const i64 24
    %3182 = gep i8, ptr %1813, %3181
    %3183 = const i64 24
    %3184 = gep i8, ptr %1836, %3183
    %3185 = load i64, ptr %3182
    store i64 %3185, ptr %3184
    %3186 = const i64 32
    %3187 = gep i8, ptr %1813, %3186
    %3188 = const i64 32
    %3189 = gep i8, ptr %1836, %3188
    %3190 = load i64, ptr %3187
    store i64 %3190, ptr %3189
    call @func.117(%1833, %1834, %1835, %1836)
    br bb207(%1642)
bb207(%1643: u64):
    %3191 = const bool true
    %3192 = load i64, ptr %1833
    store i64 %3192, ptr %1813
    %3193 = const i64 8
    %3194 = gep i8, ptr %1833, %3193
    %3195 = const i64 8
    %3196 = gep i8, ptr %1813, %3195
    %3197 = load i64, ptr %3194
    store i64 %3197, ptr %3196
    %3198 = const i64 16
    %3199 = gep i8, ptr %1833, %3198
    %3200 = const i64 16
    %3201 = gep i8, ptr %1813, %3200
    %3202 = load i64, ptr %3199
    store i64 %3202, ptr %3201
    %3203 = const i64 24
    %3204 = gep i8, ptr %1833, %3203
    %3205 = const i64 24
    %3206 = gep i8, ptr %1813, %3205
    %3207 = load i64, ptr %3204
    store i64 %3207, ptr %3206
    %3208 = const i64 32
    %3209 = gep i8, ptr %1833, %3208
    %3210 = const i64 32
    %3211 = gep i8, ptr %1813, %3210
    %3212 = load i64, ptr %3209
    store i64 %3212, ptr %3211
    br bb201(%1643)
bb208:
    %3213 = const bool false
    %3214 = load i64, ptr %1813
    store i64 %3214, ptr %0
    %3215 = const i64 8
    %3216 = gep i8, ptr %1813, %3215
    %3217 = const i64 8
    %3218 = gep i8, ptr %0, %3217
    %3219 = load i64, ptr %3216
    store i64 %3219, ptr %3218
    %3220 = const i64 16
    %3221 = gep i8, ptr %1813, %3220
    %3222 = const i64 16
    %3223 = gep i8, ptr %0, %3222
    %3224 = load i64, ptr %3221
    store i64 %3224, ptr %3223
    %3225 = const i64 24
    %3226 = gep i8, ptr %1813, %3225
    %3227 = const i64 24
    %3228 = gep i8, ptr %0, %3227
    %3229 = load i64, ptr %3226
    store i64 %3229, ptr %3228
    %3230 = const i64 32
    %3231 = gep i8, ptr %1813, %3230
    %3232 = const i64 32
    %3233 = gep i8, ptr %0, %3232
    %3234 = load i64, ptr %3231
    store i64 %3234, ptr %3233
    %3235 = const bool false
    br bb209
bb209:
    br bb210
bb210:
    br bb211
bb211:
    br bb212
bb212:
    br bb213
bb213:
    br bb214
bb214:
    %3236 = const bool false
    ret
bb215(%1644: ptr, %1645: u32, %1646: u32, %1647: u64, %1648: ptr, %1649: u64, %1650: u64, %1651: u64, %1652: u64, %1653: u64, %1654: u64):
    br bb33(%1644, %1645, %1646, %1647, %1648, %1649, %1650, %1651, %1652, %1653, %1654)
bb216(%1655: ptr, %1656: u32, %1657: u32, %1658: u64, %1659: ptr, %1660: u64, %1661: u64, %1662: u64, %1663: u64, %1664: u64, %1665: u64, %1666: u64):
    br bb43(%1655, %1656, %1657, %1658, %1659, %1660, %1661, %1662, %1663, %1664, %1665, %1666)
bb217(%1667: ptr, %1668: u32, %1669: u32, %1670: u64, %1671: ptr, %1672: u64, %1673: u64, %1674: u64, %1675: u64, %1676: u64):
    br bb108(%1667, %1668, %1669, %1670, %1671, %1672, %1673, %1674, %1675, %1676)
bb218(%1677: ptr, %1678: u32, %1679: u32, %1680: u64, %1681: ptr, %1682: u64, %1683: u64, %1684: u64, %1685: u64, %1686: u64):
    br bb108(%1677, %1678, %1679, %1680, %1681, %1682, %1683, %1684, %1685, %1686)
bb219(%1687: ptr, %1688: u32, %1689: u32, %1690: u64, %1691: ptr, %1692: u64, %1693: u64, %1694: u64, %1695: u64, %1696: u64, %1697: u64):
    br bb109(%1687, %1688, %1689, %1690, %1691, %1692, %1693, %1694, %1695, %1696, %1697)
bb220(%1698: u64, %1699: u64, %1700: u64, %1701: u64, %1702: u64):
    br bb135(%1698, %1699, %1700, %1701, %1702)
bb221(%1703: u64, %1704: u64, %1705: u64, %1706: u64):
    br bb150(%1703, %1704, %1705, %1706)
bb222(%1707: u64, %1708: u64, %1709: u64, %1710: u64):
    br bb165(%1707, %1708, %1709, %1710)
bb223(%1711: u64):
    br bb185(%1711)
bb224(%1712: u64):
    br bb193(%1712)
bb225(%1713: u64):
    br bb201(%1713)
bb226:
    unreachable
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecbE3newCs6RT0DENTjyC_27clean_mutual_recursor_slice(functy.60) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecbE4pushCs6RT0DENTjyC_27clean_mutual_recursor_slice(functy.61) {
}

fn @get_recursive_field_flags(functy.62) {
bb0(%0: ptr, %1: ptr, %2: ptr, %3: u32):
    %39 = alloca (i64, i64, i64), align 8
    %40 = alloca (i64, i64, i64, i64, i64), align 8
    %41 = alloca i64, align 8
    %42 = alloca (i64, i64, i64, i64, i64), align 8
    %43 = alloca (i32, i32), align 4
    %44 = const bool false
    %45 = const bool true
    call @func.60(%39)
    br bb1(%1, %3)
bb1(%4: ptr, %5: u32):
    call @func.78(%40, %4)
    br bb2(%5)
bb2(%6: u32):
    %46 = const u32 0
    br bb3(%6, %46)
bb3(%7: u32, %8: u32):
    store ptr %40, ptr %41
    %47 = load ptr, ptr %41
    %48 = load i8, ptr %47
    %49 = sext i8 %48 to i64
    switch %49 [ 6: bb4(%7, %8) default: bb13 ]
bb4(%9: u32, %10: u32):
    %50 = load ptr, ptr %41
    %51 = const i64 8
    %52 = gep i8, ptr %50, %51
    %53 = load ptr, ptr %41
    %54 = const i64 16
    %55 = gep i8, ptr %53, %54
    %56 = icmp uge u32 %10, %9
    condbr %56, bb5(%9, %10, %52, %55), bb8(%9, %10, %55)
bb5(%11: u32, %12: u32, %13: ptr, %14: ptr):
    %57 = load ptr, ptr %13
    %58 = const i64 16
    %59 = gep i8, ptr %57, %58
    br bb6(%11, %12, %14, %39, %59)
bb6(%15: u32, %16: u32, %17: ptr, %18: ptr, %19: ptr):
    %60 = call @func.119(%19, %2)
    br bb7(%15, %16, %17, %18, %60)
bb7(%20: u32, %21: u32, %22: ptr, %23: ptr, %24: bool):
    call @func.61(%23, %24)
    br bb15(%20, %21, %22)
bb8(%25: u32, %26: u32, %27: ptr):
    %61 = load ptr, ptr %27
    %62 = const i64 16
    %63 = gep i8, ptr %61, %62
    br bb9(%25, %26, %63)
bb9(%28: u32, %29: u32, %30: ptr):
    call @func.78(%42, %30)
    br bb10(%28, %29)
bb10(%31: u32, %32: u32):
    br bb11(%31, %32)
bb11(%33: u32, %34: u32):
    %64 = load i64, ptr %42
    store i64 %64, ptr %40
    %65 = const i64 8
    %66 = gep i8, ptr %42, %65
    %67 = const i64 8
    %68 = gep i8, ptr %40, %67
    %69 = load i64, ptr %66
    store i64 %69, ptr %68
    %70 = const i64 16
    %71 = gep i8, ptr %42, %70
    %72 = const i64 16
    %73 = gep i8, ptr %40, %72
    %74 = load i64, ptr %71
    store i64 %74, ptr %73
    %75 = const i64 24
    %76 = gep i8, ptr %42, %75
    %77 = const i64 24
    %78 = gep i8, ptr %40, %77
    %79 = load i64, ptr %76
    store i64 %79, ptr %78
    %80 = const i64 32
    %81 = gep i8, ptr %42, %80
    %82 = const i64 32
    %83 = gep i8, ptr %40, %82
    %84 = load i64, ptr %81
    store i64 %84, ptr %83
    %85 = const u32 1
    %86, %87 = add.overflow u32 %34, %85
    store u32 %86, ptr %43
    %88 = const i64 4
    %89 = gep i8, ptr %43, %88
    store bool %87, ptr %89
    %90 = const i64 4
    %91 = gep i8, ptr %43, %90
    %92 = load bool, ptr %91
    %93 = const bool false
    %94 = icmp eq bool %92, %93
    condbr %94, bb12(%33), bb16
bb12(%35: u32):
    %95 = load u32, ptr %43
    br bb3(%35, %95)
bb13:
    %96 = const bool false
    %97 = load i64, ptr %39
    store i64 %97, ptr %0
    %98 = const i64 8
    %99 = gep i8, ptr %39, %98
    %100 = const i64 8
    %101 = gep i8, ptr %0, %100
    %102 = load i64, ptr %99
    store i64 %102, ptr %101
    %103 = const i64 16
    %104 = gep i8, ptr %39, %103
    %105 = const i64 16
    %106 = gep i8, ptr %0, %105
    %107 = load i64, ptr %104
    store i64 %107, ptr %106
    br bb14
bb14:
    %108 = const bool false
    ret
bb15(%36: u32, %37: u32, %38: ptr):
    br bb8(%36, %37, %38)
bb16:
    unreachable
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprE3newBE_(functy.63) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprE4pushBH_(functy.64) {
}

fn @get_constructor_field_types(functy.65) {
bb0(%0: ptr, %1: ptr, %2: u32):
    %42 = alloca (i64, i64, i64), align 8
    %43 = alloca (i64, i64, i64, i64, i64), align 8
    %44 = alloca i64, align 8
    %45 = alloca (i64, i64, i64, i64, i64), align 8
    %46 = alloca (i64, i64, i64, i64, i64), align 8
    %47 = alloca (i32, i32), align 4
    %48 = const bool false
    %49 = const bool true
    call @func.63(%42)
    br bb1(%1, %2)
bb1(%3: ptr, %4: u32):
    call @func.78(%43, %3)
    br bb2(%4)
bb2(%5: u32):
    %50 = const u32 0
    br bb3(%5, %50)
bb3(%6: u32, %7: u32):
    store ptr %43, ptr %44
    %51 = load ptr, ptr %44
    %52 = load i8, ptr %51
    %53 = sext i8 %52 to i64
    switch %53 [ 6: bb4(%6, %7) default: bb14 ]
bb4(%8: u32, %9: u32):
    %54 = load ptr, ptr %44
    %55 = const i64 8
    %56 = gep i8, ptr %54, %55
    %57 = load ptr, ptr %44
    %58 = const i64 16
    %59 = gep i8, ptr %57, %58
    %60 = icmp uge u32 %9, %8
    condbr %60, bb5(%8, %9, %56, %59), bb9(%8, %9, %59)
bb5(%10: u32, %11: u32, %12: ptr, %13: ptr):
    %61 = load ptr, ptr %12
    %62 = const i64 16
    %63 = gep i8, ptr %61, %62
    br bb6(%10, %11, %13, %42, %63)
bb6(%14: u32, %15: u32, %16: ptr, %17: ptr, %18: ptr):
    %64 = call @func.120(%18)
    br bb7(%14, %15, %16, %17, %64)
bb7(%19: u32, %20: u32, %21: ptr, %22: ptr, %23: ptr):
    call @func.78(%45, %23)
    br bb8(%19, %20, %21, %22)
bb8(%24: u32, %25: u32, %26: ptr, %27: ptr):
    call @func.64(%27, %45)
    br bb16(%24, %25, %26)
bb9(%28: u32, %29: u32, %30: ptr):
    %65 = load ptr, ptr %30
    %66 = const i64 16
    %67 = gep i8, ptr %65, %66
    br bb10(%28, %29, %67)
bb10(%31: u32, %32: u32, %33: ptr):
    call @func.78(%46, %33)
    br bb11(%31, %32)
bb11(%34: u32, %35: u32):
    br bb12(%34, %35)
bb12(%36: u32, %37: u32):
    %68 = load i64, ptr %46
    store i64 %68, ptr %43
    %69 = const i64 8
    %70 = gep i8, ptr %46, %69
    %71 = const i64 8
    %72 = gep i8, ptr %43, %71
    %73 = load i64, ptr %70
    store i64 %73, ptr %72
    %74 = const i64 16
    %75 = gep i8, ptr %46, %74
    %76 = const i64 16
    %77 = gep i8, ptr %43, %76
    %78 = load i64, ptr %75
    store i64 %78, ptr %77
    %79 = const i64 24
    %80 = gep i8, ptr %46, %79
    %81 = const i64 24
    %82 = gep i8, ptr %43, %81
    %83 = load i64, ptr %80
    store i64 %83, ptr %82
    %84 = const i64 32
    %85 = gep i8, ptr %46, %84
    %86 = const i64 32
    %87 = gep i8, ptr %43, %86
    %88 = load i64, ptr %85
    store i64 %88, ptr %87
    %89 = const u32 1
    %90, %91 = add.overflow u32 %37, %89
    store u32 %90, ptr %47
    %92 = const i64 4
    %93 = gep i8, ptr %47, %92
    store bool %91, ptr %93
    %94 = const i64 4
    %95 = gep i8, ptr %47, %94
    %96 = load bool, ptr %95
    %97 = const bool false
    %98 = icmp eq bool %96, %97
    condbr %98, bb13(%36), bb17
bb13(%38: u32):
    %99 = load u32, ptr %47
    br bb3(%38, %99)
bb14:
    %100 = const bool false
    %101 = load i64, ptr %42
    store i64 %101, ptr %0
    %102 = const i64 8
    %103 = gep i8, ptr %42, %102
    %104 = const i64 8
    %105 = gep i8, ptr %0, %104
    %106 = load i64, ptr %103
    store i64 %106, ptr %105
    %107 = const i64 16
    %108 = gep i8, ptr %42, %107
    %109 = const i64 16
    %110 = gep i8, ptr %0, %109
    %111 = load i64, ptr %108
    store i64 %111, ptr %110
    br bb15
bb15:
    %112 = const bool false
    ret
bb16(%39: u32, %40: u32, %41: ptr):
    br bb9(%39, %40, %41)
bb17:
    unreachable
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprE3newBE_(functy.66) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprE4pushBH_(functy.67) {
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprE3lenBG_(functy.68) {
}

fn @_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_(functy.69) {
}

fn @get_constructor_return_indices(functy.70) {
bb0(%0: ptr, %1: ptr, %2: u32):
    %67 = alloca (i64, i64, i64, i64, i64), align 8
    %68 = alloca i64, align 8
    %69 = alloca (i64, i64, i64, i64, i64), align 8
    %70 = alloca (i64, i64, i64), align 8
    %71 = alloca i64, align 8
    %72 = alloca (i64, i64, i64, i64, i64), align 8
    %73 = alloca (i64, i64, i64, i64, i64), align 8
    %74 = alloca (i64, i64, i64), align 8
    %75 = alloca (i64, i64, i64, i64, i64), align 8
    %76 = alloca (i64, i64), align 8
    %77 = alloca (i64, i64), align 8
    %78 = alloca (i64, i64), align 8
    call @func.78(%67, %1)
    br bb1(%2)
bb1(%3: u32):
    store ptr %67, ptr %68
    %79 = load ptr, ptr %68
    %80 = load i8, ptr %79
    %81 = sext i8 %80 to i64
    switch %81 [ 6: bb2(%3) default: bb6(%3) ]
bb2(%4: u32):
    %82 = load ptr, ptr %68
    %83 = const i64 16
    %84 = gep i8, ptr %82, %83
    %85 = load ptr, ptr %84
    %86 = const i64 16
    %87 = gep i8, ptr %85, %86
    br bb3(%4, %87)
bb3(%5: u32, %6: ptr):
    call @func.78(%69, %6)
    br bb4(%5)
bb4(%7: u32):
    br bb5(%7)
bb5(%8: u32):
    %88 = load i64, ptr %69
    store i64 %88, ptr %67
    %89 = const i64 8
    %90 = gep i8, ptr %69, %89
    %91 = const i64 8
    %92 = gep i8, ptr %67, %91
    %93 = load i64, ptr %90
    store i64 %93, ptr %92
    %94 = const i64 16
    %95 = gep i8, ptr %69, %94
    %96 = const i64 16
    %97 = gep i8, ptr %67, %96
    %98 = load i64, ptr %95
    store i64 %98, ptr %97
    %99 = const i64 24
    %100 = gep i8, ptr %69, %99
    %101 = const i64 24
    %102 = gep i8, ptr %67, %101
    %103 = load i64, ptr %100
    store i64 %103, ptr %102
    %104 = const i64 32
    %105 = gep i8, ptr %69, %104
    %106 = const i64 32
    %107 = gep i8, ptr %67, %106
    %108 = load i64, ptr %105
    store i64 %108, ptr %107
    br bb1(%8)
bb6(%9: u32):
    call @func.66(%70)
    br bb30(%9)
bb7(%10: u32):
    store ptr %67, ptr %71
    %109 = load ptr, ptr %71
    %110 = load i8, ptr %109
    %111 = sext i8 %110 to i64
    switch %111 [ 4: bb8(%10) default: bb15(%10) ]
bb8(%11: u32):
    %112 = load ptr, ptr %71
    %113 = const i64 8
    %114 = gep i8, ptr %112, %113
    %115 = load ptr, ptr %71
    %116 = const i64 16
    %117 = gep i8, ptr %115, %116
    %118 = load ptr, ptr %117
    %119 = const i64 16
    %120 = gep i8, ptr %118, %119
    br bb9(%11, %114, %70, %120)
bb9(%12: u32, %13: ptr, %14: ptr, %15: ptr):
    call @func.78(%72, %15)
    br bb10(%12, %13, %14)
bb10(%16: u32, %17: ptr, %18: ptr):
    call @func.67(%18, %72)
    br bb11(%16, %17)
bb11(%19: u32, %20: ptr):
    %121 = load ptr, ptr %20
    %122 = const i64 16
    %123 = gep i8, ptr %121, %122
    br bb12(%19, %123)
bb12(%21: u32, %22: ptr):
    call @func.78(%73, %22)
    br bb13(%21)
bb13(%23: u32):
    br bb14(%23)
bb14(%24: u32):
    %124 = load i64, ptr %73
    store i64 %124, ptr %67
    %125 = const i64 8
    %126 = gep i8, ptr %73, %125
    %127 = const i64 8
    %128 = gep i8, ptr %67, %127
    %129 = load i64, ptr %126
    store i64 %129, ptr %128
    %130 = const i64 16
    %131 = gep i8, ptr %73, %130
    %132 = const i64 16
    %133 = gep i8, ptr %67, %132
    %134 = load i64, ptr %131
    store i64 %134, ptr %133
    %135 = const i64 24
    %136 = gep i8, ptr %73, %135
    %137 = const i64 24
    %138 = gep i8, ptr %67, %137
    %139 = load i64, ptr %136
    store i64 %139, ptr %138
    %140 = const i64 32
    %141 = gep i8, ptr %73, %140
    %142 = const i64 32
    %143 = gep i8, ptr %67, %142
    %144 = load i64, ptr %141
    store i64 %144, ptr %143
    br bb7(%24)
bb15(%25: u32):
    %145 = zext u32 %25 to u64
    %146 = call @func.68(%70)
    br bb16(%145, %146)
bb16(%26: u64, %27: u64):
    call @func.66(%74)
    br bb17(%26, %27)
bb17(%28: u64, %29: u64):
    %147 = const u64 0
    br bb18(%28, %29, %147)
bb18(%30: u64, %31: u64, %32: u64):
    %148 = icmp ult u64 %32, %31
    condbr %148, bb19(%30, %31, %32), bb27
bb19(%33: u64, %34: u64, %35: u64):
    %149 = icmp uge u64 %35, %33
    condbr %149, bb20(%33, %34, %35), bb25(%33, %34, %35)
bb20(%36: u64, %37: u64, %38: u64):
    %150 = const u64 1
    %151, %152 = sub.overflow u64 %37, %150
    store u64 %151, ptr %76
    %153 = const i64 8
    %154 = gep i8, ptr %76, %153
    store bool %152, ptr %154
    %155 = const i64 8
    %156 = gep i8, ptr %76, %155
    %157 = load bool, ptr %156
    %158 = const bool false
    %159 = icmp eq bool %157, %158
    condbr %159, bb21(%36, %37, %38, %74, %70), bb32
bb21(%39: u64, %40: u64, %41: u64, %42: ptr, %43: ptr):
    %160 = load u64, ptr %76
    %161, %162 = sub.overflow u64 %160, %41
    store u64 %161, ptr %77
    %163 = const i64 8
    %164 = gep i8, ptr %77, %163
    store bool %162, ptr %164
    %165 = const i64 8
    %166 = gep i8, ptr %77, %165
    %167 = load bool, ptr %166
    %168 = const bool false
    %169 = icmp eq bool %167, %168
    condbr %169, bb22(%39, %40, %41, %42, %43), bb32
bb22(%44: u64, %45: u64, %46: u64, %47: ptr, %48: ptr):
    %170 = load u64, ptr %77
    %171 = call @func.69(%48, %170)
    br bb23(%44, %45, %46, %47, %171)
bb23(%49: u64, %50: u64, %51: u64, %52: ptr, %53: ptr):
    call @func.78(%75, %53)
    br bb24(%49, %50, %51, %52)
bb24(%54: u64, %55: u64, %56: u64, %57: ptr):
    call @func.67(%57, %75)
    br bb31(%54, %55, %56)
bb25(%58: u64, %59: u64, %60: u64):
    %172 = const u64 1
    %173, %174 = add.overflow u64 %60, %172
    store u64 %173, ptr %78
    %175 = const i64 8
    %176 = gep i8, ptr %78, %175
    store bool %174, ptr %176
    %177 = const i64 8
    %178 = gep i8, ptr %78, %177
    %179 = load bool, ptr %178
    %180 = const bool false
    %181 = icmp eq bool %179, %180
    condbr %181, bb26(%58, %59), bb32
bb26(%61: u64, %62: u64):
    %182 = load u64, ptr %78
    br bb18(%61, %62, %182)
bb27:
    %183 = load i64, ptr %74
    store i64 %183, ptr %0
    %184 = const i64 8
    %185 = gep i8, ptr %74, %184
    %186 = const i64 8
    %187 = gep i8, ptr %0, %186
    %188 = load i64, ptr %185
    store i64 %188, ptr %187
    %189 = const i64 16
    %190 = gep i8, ptr %74, %189
    %191 = const i64 16
    %192 = gep i8, ptr %0, %191
    %193 = load i64, ptr %190
    store i64 %193, ptr %192
    br bb28
bb28:
    br bb29
bb29:
    ret
bb30(%63: u32):
    br bb7(%63)
bb31(%64: u64, %65: u64, %66: u64):
    br bb25(%64, %65, %66)
bb32:
    unreachable
}

fn @_Name_as_std__clone__Clone___clone(functy.71) {
bb0(%0: ptr, %1: ptr):
    %2 = load i32, ptr %1
    store i32 %2, ptr %0
    ret
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice5LevelE3newBE_(functy.72) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice5LevelE4pushBH_(functy.73) {
}

fn @ind_const_with_levels(functy.74) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %16 = alloca (i64, i64, i64), align 8
    %17 = alloca (i64, i64), align 8
    %18 = alloca i32, align 4
    %19 = alloca (i64, i64), align 8
    %20 = alloca i32, align 4
    %21 = alloca (i64, i64, i64), align 8
    %22 = const bool false
    %23 = const bool true
    call @func.72(%16)
    br bb1(%1)
bb1(%3: ptr):
    %24 = const u64 0
    br bb2(%3, %24)
bb2(%4: ptr, %5: u64):
    %25 = const i64 8
    %26 = gep i8, ptr %2, %25
    %27 = load u64, ptr %26
    %28 = icmp ult u64 %5, %27
    condbr %28, bb3(%4, %5), bb7(%4)
bb3(%6: ptr, %7: u64):
    %29 = const i64 8
    %30 = gep i8, ptr %2, %29
    %31 = load u64, ptr %30
    %32 = icmp ult u64 %7, %31
    condbr %32, bb4(%6, %7, %16, %7), bb9
bb4(%8: ptr, %9: u64, %10: ptr, %11: u64):
    %33 = load ptr, ptr %2
    %34 = const u64 4
    %35 = mul u64 %11, %34
    %36 = gep i8, ptr %33, %35
    %37 = load i32, ptr %36
    store i32 %37, ptr %18
    %38 = const i64 4
    %39 = gep i8, ptr %17, %38
    %40 = load i32, ptr %18
    store i32 %40, ptr %39
    %41 = const i32 2
    store i32 %41, ptr %17
    call @func.73(%10, %17)
    br bb5(%8, %9)
bb5(%12: ptr, %13: u64):
    %42 = const u64 1
    %43, %44 = add.overflow u64 %13, %42
    store u64 %43, ptr %19
    %45 = const i64 8
    %46 = gep i8, ptr %19, %45
    store bool %44, ptr %46
    %47 = const i64 8
    %48 = gep i8, ptr %19, %47
    %49 = load bool, ptr %48
    %50 = const bool false
    %51 = icmp eq bool %49, %50
    condbr %51, bb6(%12), bb9
bb6(%14: ptr):
    %52 = load u64, ptr %19
    br bb2(%14, %52)
bb7(%15: ptr):
    %53 = load i32, ptr %15
    store i32 %53, ptr %20
    %54 = const bool false
    %55 = load i64, ptr %16
    store i64 %55, ptr %21
    %56 = const i64 8
    %57 = gep i8, ptr %16, %56
    %58 = const i64 8
    %59 = gep i8, ptr %21, %58
    %60 = load i64, ptr %57
    store i64 %60, ptr %59
    %61 = const i64 16
    %62 = gep i8, ptr %16, %61
    %63 = const i64 16
    %64 = gep i8, ptr %21, %63
    %65 = load i64, ptr %62
    store i64 %65, ptr %64
    %66 = load u32, ptr %20
    call @func.112(%0, %66, %21)
    br bb8
bb8:
    %67 = const bool false
    ret
bb9:
    unreachable
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecTNtCs6RT0DENTjyC_27clean_mutual_recursor_slice10BinderDataNtBF_4ExprEE3newBF_(functy.75) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecTNtCs6RT0DENTjyC_27clean_mutual_recursor_slice10BinderDataNtBI_4ExprEE4pushBI_(functy.76) {
}

fn @collect_pi_binders(functy.77) {
bb0(%0: ptr, %1: ptr, %2: u32):
    %37 = alloca (i64, i64, i64), align 8
    %38 = alloca (i64, i64, i64, i64, i64), align 8
    %39 = alloca i64, align 8
    %40 = alloca (i64, i64, i64, i64, i64, i64), align 8
    %41 = alloca (i8, i8), align 1
    %42 = alloca (i64, i64, i64, i64, i64), align 8
    %43 = alloca (i64, i64, i64, i64, i64), align 8
    %44 = alloca (i32, i32), align 4
    %45 = const bool false
    %46 = const bool true
    call @func.75(%37)
    br bb1(%1, %2)
bb1(%3: ptr, %4: u32):
    call @func.78(%38, %3)
    br bb2(%4)
bb2(%5: u32):
    %47 = const u32 0
    br bb3(%5, %47)
bb3(%6: u32, %7: u32):
    %48 = icmp ult u32 %7, %6
    condbr %48, bb4(%6, %7), bb14
bb4(%8: u32, %9: u32):
    store ptr %38, ptr %39
    %49 = load ptr, ptr %39
    %50 = load i8, ptr %49
    %51 = sext i8 %50 to i64
    switch %51 [ 6: bb5(%8, %9) default: bb14 ]
bb5(%10: u32, %11: u32):
    %52 = load ptr, ptr %39
    %53 = const i64 1
    %54 = gep i8, ptr %52, %53
    %55 = load ptr, ptr %39
    %56 = const i64 8
    %57 = gep i8, ptr %55, %56
    %58 = load ptr, ptr %39
    %59 = const i64 16
    %60 = gep i8, ptr %58, %59
    %61 = load i8, ptr %54
    store i8 %61, ptr %41
    %62 = const i64 1
    %63 = gep i8, ptr %54, %62
    %64 = const i64 1
    %65 = gep i8, ptr %41, %64
    %66 = load i8, ptr %63
    store i8 %66, ptr %65
    %67 = load ptr, ptr %57
    %68 = const i64 16
    %69 = gep i8, ptr %67, %68
    br bb6(%10, %11, %60, %37, %69)
bb6(%12: u32, %13: u32, %14: ptr, %15: ptr, %16: ptr):
    %70 = call @func.120(%16)
    br bb7(%12, %13, %14, %15, %70)
bb7(%17: u32, %18: u32, %19: ptr, %20: ptr, %21: ptr):
    call @func.78(%42, %21)
    br bb8(%17, %18, %19, %20)
bb8(%22: u32, %23: u32, %24: ptr, %25: ptr):
    %71 = load i8, ptr %41
    store i8 %71, ptr %40
    %72 = const i64 1
    %73 = gep i8, ptr %41, %72
    %74 = const i64 1
    %75 = gep i8, ptr %40, %74
    %76 = load i8, ptr %73
    store i8 %76, ptr %75
    %77 = const i64 8
    %78 = gep i8, ptr %40, %77
    %79 = load i64, ptr %42
    store i64 %79, ptr %78
    %80 = const i64 8
    %81 = gep i8, ptr %42, %80
    %82 = const i64 8
    %83 = gep i8, ptr %78, %82
    %84 = load i64, ptr %81
    store i64 %84, ptr %83
    %85 = const i64 16
    %86 = gep i8, ptr %42, %85
    %87 = const i64 16
    %88 = gep i8, ptr %78, %87
    %89 = load i64, ptr %86
    store i64 %89, ptr %88
    %90 = const i64 24
    %91 = gep i8, ptr %42, %90
    %92 = const i64 24
    %93 = gep i8, ptr %78, %92
    %94 = load i64, ptr %91
    store i64 %94, ptr %93
    %95 = const i64 32
    %96 = gep i8, ptr %42, %95
    %97 = const i64 32
    %98 = gep i8, ptr %78, %97
    %99 = load i64, ptr %96
    store i64 %99, ptr %98
    call @func.76(%25, %40)
    br bb9(%22, %23, %24)
bb9(%26: u32, %27: u32, %28: ptr):
    %100 = load ptr, ptr %28
    %101 = const i64 16
    %102 = gep i8, ptr %100, %101
    br bb10(%26, %27, %102)
bb10(%29: u32, %30: u32, %31: ptr):
    call @func.78(%43, %31)
    br bb11(%29, %30)
bb11(%32: u32, %33: u32):
    br bb12(%32, %33)
bb12(%34: u32, %35: u32):
    %103 = load i64, ptr %43
    store i64 %103, ptr %38
    %104 = const i64 8
    %105 = gep i8, ptr %43, %104
    %106 = const i64 8
    %107 = gep i8, ptr %38, %106
    %108 = load i64, ptr %105
    store i64 %108, ptr %107
    %109 = const i64 16
    %110 = gep i8, ptr %43, %109
    %111 = const i64 16
    %112 = gep i8, ptr %38, %111
    %113 = load i64, ptr %110
    store i64 %113, ptr %112
    %114 = const i64 24
    %115 = gep i8, ptr %43, %114
    %116 = const i64 24
    %117 = gep i8, ptr %38, %116
    %118 = load i64, ptr %115
    store i64 %118, ptr %117
    %119 = const i64 32
    %120 = gep i8, ptr %43, %119
    %121 = const i64 32
    %122 = gep i8, ptr %38, %121
    %123 = load i64, ptr %120
    store i64 %123, ptr %122
    %124 = const u32 1
    %125, %126 = add.overflow u32 %35, %124
    store u32 %125, ptr %44
    %127 = const i64 4
    %128 = gep i8, ptr %44, %127
    store bool %126, ptr %128
    %129 = const i64 4
    %130 = gep i8, ptr %44, %129
    %131 = load bool, ptr %130
    %132 = const bool false
    %133 = icmp eq bool %131, %132
    condbr %133, bb13(%34), bb16
bb13(%36: u32):
    %134 = load u32, ptr %44
    br bb3(%36, %134)
bb14:
    %135 = const bool false
    %136 = load i64, ptr %37
    store i64 %136, ptr %0
    %137 = const i64 8
    %138 = gep i8, ptr %37, %137
    %139 = const i64 8
    %140 = gep i8, ptr %0, %139
    %141 = load i64, ptr %138
    store i64 %141, ptr %140
    %142 = const i64 16
    %143 = gep i8, ptr %37, %142
    %144 = const i64 16
    %145 = gep i8, ptr %0, %144
    %146 = load i64, ptr %143
    store i64 %146, ptr %145
    br bb15
bb15:
    %147 = const bool false
    ret
bb16:
    unreachable
}

fn @_Expr_as_std__clone__Clone___clone(functy.78) {
bb0(%0: ptr, %1: ptr):
    %2 = alloca i64, align 8
    %3 = alloca (i64, i64, i64, i64), align 8
    %4 = alloca i64, align 8
    store ptr %1, ptr %2
    %5 = load ptr, ptr %2
    call @func.123(%3, %5)
    br bb1
bb1:
    %6 = load ptr, ptr %2
    %7 = const i64 32
    %8 = gep i8, ptr %6, %7
    call @func.124(%4, %8)
    br bb2
bb2:
    %9 = load i64, ptr %3
    store i64 %9, ptr %0
    %10 = const i64 8
    %11 = gep i8, ptr %3, %10
    %12 = const i64 8
    %13 = gep i8, ptr %0, %12
    %14 = load i64, ptr %11
    store i64 %14, ptr %13
    %15 = const i64 16
    %16 = gep i8, ptr %3, %15
    %17 = const i64 16
    %18 = gep i8, ptr %0, %17
    %19 = load i64, ptr %16
    store i64 %19, ptr %18
    %20 = const i64 24
    %21 = gep i8, ptr %3, %20
    %22 = const i64 24
    %23 = gep i8, ptr %0, %22
    %24 = load i64, ptr %21
    store i64 %24, ptr %23
    %25 = const i64 32
    %26 = gep i8, ptr %0, %25
    %27 = load i64, ptr %4
    store i64 %27, ptr %26
    ret
}

fn @collect_pi_binders_after_skip(functy.79) {
bb0(%0: ptr, %1: ptr, %2: u32, %3: u32):
    %31 = alloca (i64, i64, i64, i64, i64), align 8
    %32 = alloca i64, align 8
    %33 = alloca (i64, i64, i64, i64, i64), align 8
    %34 = alloca (i32, i32), align 4
    call @func.78(%31, %1)
    br bb1(%2, %3)
bb1(%4: u32, %5: u32):
    %35 = const u32 0
    br bb2(%4, %5, %35)
bb2(%6: u32, %7: u32, %8: u32):
    %36 = icmp ult u32 %8, %6
    condbr %36, bb3(%6, %7, %8), bb10(%7)
bb3(%9: u32, %10: u32, %11: u32):
    store ptr %31, ptr %32
    %37 = load ptr, ptr %32
    %38 = load i8, ptr %37
    %39 = sext i8 %38 to i64
    switch %39 [ 6: bb4(%9, %10, %11) default: bb8(%9, %10, %11) ]
bb4(%12: u32, %13: u32, %14: u32):
    %40 = load ptr, ptr %32
    %41 = const i64 16
    %42 = gep i8, ptr %40, %41
    %43 = load ptr, ptr %42
    %44 = const i64 16
    %45 = gep i8, ptr %43, %44
    br bb5(%12, %13, %14, %45)
bb5(%15: u32, %16: u32, %17: u32, %18: ptr):
    call @func.78(%33, %18)
    br bb6(%15, %16, %17)
bb6(%19: u32, %20: u32, %21: u32):
    br bb7(%19, %20, %21)
bb7(%22: u32, %23: u32, %24: u32):
    %46 = load i64, ptr %33
    store i64 %46, ptr %31
    %47 = const i64 8
    %48 = gep i8, ptr %33, %47
    %49 = const i64 8
    %50 = gep i8, ptr %31, %49
    %51 = load i64, ptr %48
    store i64 %51, ptr %50
    %52 = const i64 16
    %53 = gep i8, ptr %33, %52
    %54 = const i64 16
    %55 = gep i8, ptr %31, %54
    %56 = load i64, ptr %53
    store i64 %56, ptr %55
    %57 = const i64 24
    %58 = gep i8, ptr %33, %57
    %59 = const i64 24
    %60 = gep i8, ptr %31, %59
    %61 = load i64, ptr %58
    store i64 %61, ptr %60
    %62 = const i64 32
    %63 = gep i8, ptr %33, %62
    %64 = const i64 32
    %65 = gep i8, ptr %31, %64
    %66 = load i64, ptr %63
    store i64 %66, ptr %65
    br bb8(%22, %23, %24)
bb8(%25: u32, %26: u32, %27: u32):
    %67 = const u32 1
    %68, %69 = add.overflow u32 %27, %67
    store u32 %68, ptr %34
    %70 = const i64 4
    %71 = gep i8, ptr %34, %70
    store bool %69, ptr %71
    %72 = const i64 4
    %73 = gep i8, ptr %34, %72
    %74 = load bool, ptr %73
    %75 = const bool false
    %76 = icmp eq bool %74, %75
    condbr %76, bb9(%25, %26), bb13
bb9(%28: u32, %29: u32):
    %77 = load u32, ptr %34
    br bb2(%28, %29, %77)
bb10(%30: u32):
    call @func.77(%0, %31, %30)
    br bb11
bb11:
    br bb12
bb12:
    ret
bb13:
    unreachable
}

fn @_RNvXsd_NtCskTzINo8ZBH9_5alloc5boxedINtB5_3BoxNtCs6RT0DENTjyC_27clean_mutual_recursor_slice5LevelENtNtCs2EYQwhfuABO_4core5clone5Clone5cloneBJ_(functy.80) {
}

fn @_Level_as_std__clone__Clone___clone(functy.81) {
bb0(%0: ptr, %1: ptr):
    %2 = alloca i64, align 8
    %3 = alloca i64, align 8
    %4 = alloca i32, align 4
    store ptr %1, ptr %2
    %5 = load ptr, ptr %2
    %6 = load i32, ptr %5
    %7 = sext i32 %6 to i64
    switch %7 [ 0: bb4 1: bb3 2: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %8 = load ptr, ptr %2
    %9 = const i64 4
    %10 = gep i8, ptr %8, %9
    call @func.71(%4, %10)
    br bb6
bb3:
    %11 = load ptr, ptr %2
    %12 = const i64 8
    %13 = gep i8, ptr %11, %12
    call @func.80(%3, %13)
    br bb5
bb4:
    %14 = const i32 0
    store i32 %14, ptr %0
    br bb7
bb5:
    %15 = load ptr, ptr %3
    %16 = const i64 8
    %17 = gep i8, ptr %0, %16
    store ptr %15, ptr %17
    %18 = const i32 1
    store i32 %18, ptr %0
    br bb7
bb6:
    %19 = const i64 4
    %20 = gep i8, ptr %0, %19
    %21 = load i32, ptr %4
    store i32 %21, ptr %20
    %22 = const i32 2
    store i32 %22, ptr %0
    br bb7
bb7:
    ret
}

fn @Expr__from_kind(functy.82) {
bb0(%0: ptr, %1: ptr):
    %2 = alloca i64, align 8
    %3 = alloca (i64, i64, i64, i64), align 8
    call @func.129(%2, %1)
    br bb1
bb1:
    %4 = load i64, ptr %1
    store i64 %4, ptr %3
    %5 = const i64 8
    %6 = gep i8, ptr %1, %5
    %7 = const i64 8
    %8 = gep i8, ptr %3, %7
    %9 = load i64, ptr %6
    store i64 %9, ptr %8
    %10 = const i64 16
    %11 = gep i8, ptr %1, %10
    %12 = const i64 16
    %13 = gep i8, ptr %3, %12
    %14 = load i64, ptr %11
    store i64 %14, ptr %13
    %15 = const i64 24
    %16 = gep i8, ptr %1, %15
    %17 = const i64 24
    %18 = gep i8, ptr %3, %17
    %19 = load i64, ptr %16
    store i64 %19, ptr %18
    %20 = load i64, ptr %3
    store i64 %20, ptr %0
    %21 = const i64 8
    %22 = gep i8, ptr %3, %21
    %23 = const i64 8
    %24 = gep i8, ptr %0, %23
    %25 = load i64, ptr %22
    store i64 %25, ptr %24
    %26 = const i64 16
    %27 = gep i8, ptr %3, %26
    %28 = const i64 16
    %29 = gep i8, ptr %0, %28
    %30 = load i64, ptr %27
    store i64 %30, ptr %29
    %31 = const i64 24
    %32 = gep i8, ptr %3, %31
    %33 = const i64 24
    %34 = gep i8, ptr %0, %33
    %35 = load i64, ptr %32
    store i64 %35, ptr %34
    %36 = const i64 32
    %37 = gep i8, ptr %0, %36
    %38 = load i64, ptr %2
    store i64 %38, ptr %37
    ret
}

fn @Expr__bvar(functy.83) {
bb0(%0: ptr, %1: u32):
    %2 = alloca (i64, i64, i64, i64), align 8
    %3 = const i64 4
    %4 = gep i8, ptr %2, %3
    store u32 %1, ptr %4
    %5 = const i8 0
    store i8 %5, ptr %2
    call @func.82(%0, %2)
    br bb1
bb1:
    ret
}

fn @Expr__app(functy.84) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %3 = alloca (i64, i64, i64, i64), align 8
    %4 = alloca i64, align 8
    %5 = alloca i64, align 8
    %6 = alloca (i64, i64, i64, i64, i64), align 8
    %7 = const bool false
    %8 = const bool true
    %9 = const i64 56
    %10 = heap_alloc rust_heap i8, %9, align 8
    %11 = const u64 1
    store u64 %11, ptr %10
    %12 = const i64 8
    %13 = gep i8, ptr %10, %12
    %14 = const u64 1
    store u64 %14, ptr %13
    %15 = const i64 16
    %16 = gep i8, ptr %10, %15
    %17 = load i64, ptr %1
    store i64 %17, ptr %16
    %18 = const i64 8
    %19 = gep i8, ptr %1, %18
    %20 = const i64 8
    %21 = gep i8, ptr %16, %20
    %22 = load i64, ptr %19
    store i64 %22, ptr %21
    %23 = const i64 16
    %24 = gep i8, ptr %1, %23
    %25 = const i64 16
    %26 = gep i8, ptr %16, %25
    %27 = load i64, ptr %24
    store i64 %27, ptr %26
    %28 = const i64 24
    %29 = gep i8, ptr %1, %28
    %30 = const i64 24
    %31 = gep i8, ptr %16, %30
    %32 = load i64, ptr %29
    store i64 %32, ptr %31
    %33 = const i64 32
    %34 = gep i8, ptr %1, %33
    %35 = const i64 32
    %36 = gep i8, ptr %16, %35
    %37 = load i64, ptr %34
    store i64 %37, ptr %36
    store ptr %10, ptr %4
    br bb1
bb1:
    %38 = const bool false
    %39 = load i64, ptr %2
    store i64 %39, ptr %6
    %40 = const i64 8
    %41 = gep i8, ptr %2, %40
    %42 = const i64 8
    %43 = gep i8, ptr %6, %42
    %44 = load i64, ptr %41
    store i64 %44, ptr %43
    %45 = const i64 16
    %46 = gep i8, ptr %2, %45
    %47 = const i64 16
    %48 = gep i8, ptr %6, %47
    %49 = load i64, ptr %46
    store i64 %49, ptr %48
    %50 = const i64 24
    %51 = gep i8, ptr %2, %50
    %52 = const i64 24
    %53 = gep i8, ptr %6, %52
    %54 = load i64, ptr %51
    store i64 %54, ptr %53
    %55 = const i64 32
    %56 = gep i8, ptr %2, %55
    %57 = const i64 32
    %58 = gep i8, ptr %6, %57
    %59 = load i64, ptr %56
    store i64 %59, ptr %58
    %60 = const i64 56
    %61 = heap_alloc rust_heap i8, %60, align 8
    %62 = const u64 1
    store u64 %62, ptr %61
    %63 = const i64 8
    %64 = gep i8, ptr %61, %63
    %65 = const u64 1
    store u64 %65, ptr %64
    %66 = const i64 16
    %67 = gep i8, ptr %61, %66
    %68 = load i64, ptr %6
    store i64 %68, ptr %67
    %69 = const i64 8
    %70 = gep i8, ptr %6, %69
    %71 = const i64 8
    %72 = gep i8, ptr %67, %71
    %73 = load i64, ptr %70
    store i64 %73, ptr %72
    %74 = const i64 16
    %75 = gep i8, ptr %6, %74
    %76 = const i64 16
    %77 = gep i8, ptr %67, %76
    %78 = load i64, ptr %75
    store i64 %78, ptr %77
    %79 = const i64 24
    %80 = gep i8, ptr %6, %79
    %81 = const i64 24
    %82 = gep i8, ptr %67, %81
    %83 = load i64, ptr %80
    store i64 %83, ptr %82
    %84 = const i64 32
    %85 = gep i8, ptr %6, %84
    %86 = const i64 32
    %87 = gep i8, ptr %67, %86
    %88 = load i64, ptr %85
    store i64 %88, ptr %87
    store ptr %61, ptr %5
    br bb2
bb2:
    %89 = load ptr, ptr %4
    %90 = const i64 8
    %91 = gep i8, ptr %3, %90
    store ptr %89, ptr %91
    %92 = load ptr, ptr %5
    %93 = const i64 16
    %94 = gep i8, ptr %3, %93
    store ptr %92, ptr %94
    %95 = const i8 4
    store i8 %95, ptr %3
    call @func.82(%0, %3)
    br bb3
bb3:
    ret
}

fn @bi_default(functy.85) {
bb0(%0: ptr):
    %1 = const u8 0
    store u8 %1, ptr %0
    %2 = const u8 0
    %3 = const i64 1
    %4 = gep i8, ptr %0, %3
    store u8 %2, ptr %4
    ret
}

fn @Expr__pi(functy.86) {
bb0(%0: ptr, %1: ptr, %2: ptr, %3: ptr):
    %4 = alloca (i64, i64, i64, i64), align 8
    %5 = alloca i64, align 8
    %6 = alloca i64, align 8
    %7 = alloca (i64, i64, i64, i64, i64), align 8
    %8 = const bool false
    %9 = const bool true
    %10 = const i64 56
    %11 = heap_alloc rust_heap i8, %10, align 8
    %12 = const u64 1
    store u64 %12, ptr %11
    %13 = const i64 8
    %14 = gep i8, ptr %11, %13
    %15 = const u64 1
    store u64 %15, ptr %14
    %16 = const i64 16
    %17 = gep i8, ptr %11, %16
    %18 = load i64, ptr %2
    store i64 %18, ptr %17
    %19 = const i64 8
    %20 = gep i8, ptr %2, %19
    %21 = const i64 8
    %22 = gep i8, ptr %17, %21
    %23 = load i64, ptr %20
    store i64 %23, ptr %22
    %24 = const i64 16
    %25 = gep i8, ptr %2, %24
    %26 = const i64 16
    %27 = gep i8, ptr %17, %26
    %28 = load i64, ptr %25
    store i64 %28, ptr %27
    %29 = const i64 24
    %30 = gep i8, ptr %2, %29
    %31 = const i64 24
    %32 = gep i8, ptr %17, %31
    %33 = load i64, ptr %30
    store i64 %33, ptr %32
    %34 = const i64 32
    %35 = gep i8, ptr %2, %34
    %36 = const i64 32
    %37 = gep i8, ptr %17, %36
    %38 = load i64, ptr %35
    store i64 %38, ptr %37
    store ptr %11, ptr %5
    br bb1
bb1:
    %39 = const bool false
    %40 = load i64, ptr %3
    store i64 %40, ptr %7
    %41 = const i64 8
    %42 = gep i8, ptr %3, %41
    %43 = const i64 8
    %44 = gep i8, ptr %7, %43
    %45 = load i64, ptr %42
    store i64 %45, ptr %44
    %46 = const i64 16
    %47 = gep i8, ptr %3, %46
    %48 = const i64 16
    %49 = gep i8, ptr %7, %48
    %50 = load i64, ptr %47
    store i64 %50, ptr %49
    %51 = const i64 24
    %52 = gep i8, ptr %3, %51
    %53 = const i64 24
    %54 = gep i8, ptr %7, %53
    %55 = load i64, ptr %52
    store i64 %55, ptr %54
    %56 = const i64 32
    %57 = gep i8, ptr %3, %56
    %58 = const i64 32
    %59 = gep i8, ptr %7, %58
    %60 = load i64, ptr %57
    store i64 %60, ptr %59
    %61 = const i64 56
    %62 = heap_alloc rust_heap i8, %61, align 8
    %63 = const u64 1
    store u64 %63, ptr %62
    %64 = const i64 8
    %65 = gep i8, ptr %62, %64
    %66 = const u64 1
    store u64 %66, ptr %65
    %67 = const i64 16
    %68 = gep i8, ptr %62, %67
    %69 = load i64, ptr %7
    store i64 %69, ptr %68
    %70 = const i64 8
    %71 = gep i8, ptr %7, %70
    %72 = const i64 8
    %73 = gep i8, ptr %68, %72
    %74 = load i64, ptr %71
    store i64 %74, ptr %73
    %75 = const i64 16
    %76 = gep i8, ptr %7, %75
    %77 = const i64 16
    %78 = gep i8, ptr %68, %77
    %79 = load i64, ptr %76
    store i64 %79, ptr %78
    %80 = const i64 24
    %81 = gep i8, ptr %7, %80
    %82 = const i64 24
    %83 = gep i8, ptr %68, %82
    %84 = load i64, ptr %81
    store i64 %84, ptr %83
    %85 = const i64 32
    %86 = gep i8, ptr %7, %85
    %87 = const i64 32
    %88 = gep i8, ptr %68, %87
    %89 = load i64, ptr %86
    store i64 %89, ptr %88
    store ptr %62, ptr %6
    br bb2
bb2:
    %90 = const i64 1
    %91 = gep i8, ptr %4, %90
    %92 = load i8, ptr %1
    store i8 %92, ptr %91
    %93 = const i64 1
    %94 = gep i8, ptr %1, %93
    %95 = const i64 1
    %96 = gep i8, ptr %91, %95
    %97 = load i8, ptr %94
    store i8 %97, ptr %96
    %98 = load ptr, ptr %5
    %99 = const i64 8
    %100 = gep i8, ptr %4, %99
    store ptr %98, ptr %100
    %101 = load ptr, ptr %6
    %102 = const i64 16
    %103 = gep i8, ptr %4, %102
    store ptr %101, ptr %103
    %104 = const i8 6
    store i8 %104, ptr %4
    call @func.82(%0, %4)
    br bb3
bb3:
    ret
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4CtorE3lenBG_(functy.87) {
}

fn @_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4CtorEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_(functy.88) {
}

fn @_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4NameNtB7_9PartialEq2eqBF_(functy.89) {
}

fn @ctor_motive_index(functy.90) {
bb0(%0: ptr, %1: ptr):
    %30 = alloca i64, align 8
    %31 = alloca i64, align 8
    %32 = alloca i64, align 8
    %33 = alloca (i64, i64), align 8
    %34 = alloca (i64, i64), align 8
    store ptr %0, ptr %30
    %35 = const u64 0
    br bb1(%35)
bb1(%2: u64):
    %36 = const i64 8
    %37 = gep i8, ptr %1, %36
    %38 = load u64, ptr %37
    %39 = icmp ult u64 %2, %38
    condbr %39, bb2(%2), bb15
bb2(%3: u64):
    %40 = const u64 0
    br bb3(%3, %40)
bb3(%4: u64, %5: u64):
    %41 = const i64 8
    %42 = gep i8, ptr %1, %41
    %43 = load u64, ptr %42
    %44 = icmp ult u64 %4, %43
    condbr %44, bb4(%4, %5, %5, %4), bb17
bb4(%6: u64, %7: u64, %8: u64, %9: u64):
    %45 = load ptr, ptr %1
    %46 = const u64 72
    %47 = mul u64 %9, %46
    %48 = gep i8, ptr %45, %47
    %49 = call @func.87(%48)
    br bb5(%6, %7, %8, %49)
bb5(%10: u64, %11: u64, %12: u64, %13: u64):
    %50 = icmp ult u64 %12, %13
    condbr %50, bb6(%10, %11), bb13(%10)
bb6(%14: u64, %15: u64):
    %51 = const i64 8
    %52 = gep i8, ptr %1, %51
    %53 = load u64, ptr %52
    %54 = icmp ult u64 %14, %53
    condbr %54, bb7(%14, %15, %14), bb17
bb7(%16: u64, %17: u64, %18: u64):
    %55 = load ptr, ptr %1
    %56 = const u64 72
    %57 = mul u64 %18, %56
    %58 = gep i8, ptr %55, %57
    %59 = call @func.88(%58, %17)
    store ptr %59, ptr %32
    br bb8(%16, %17)
bb8(%19: u64, %20: u64):
    %60 = load ptr, ptr %32
    %61 = const i64 40
    %62 = gep i8, ptr %60, %61
    store ptr %62, ptr %31
    %63 = call @func.89(%31, %30)
    br bb9(%19, %20, %63)
bb9(%21: u64, %22: u64, %23: bool):
    condbr %23, bb10(%21), bb11(%21, %22)
bb10(%24: u64):
    br bb16(%24)
bb11(%25: u64, %26: u64):
    %64 = const u64 1
    %65, %66 = add.overflow u64 %26, %64
    store u64 %65, ptr %33
    %67 = const i64 8
    %68 = gep i8, ptr %33, %67
    store bool %66, ptr %68
    %69 = const i64 8
    %70 = gep i8, ptr %33, %69
    %71 = load bool, ptr %70
    %72 = const bool false
    %73 = icmp eq bool %71, %72
    condbr %73, bb12(%25), bb17
bb12(%27: u64):
    %74 = load u64, ptr %33
    br bb3(%27, %74)
bb13(%28: u64):
    %75 = const u64 1
    %76, %77 = add.overflow u64 %28, %75
    store u64 %76, ptr %34
    %78 = const i64 8
    %79 = gep i8, ptr %34, %78
    store bool %77, ptr %79
    %80 = const i64 8
    %81 = gep i8, ptr %34, %80
    %82 = load bool, ptr %81
    %83 = const bool false
    %84 = icmp eq bool %82, %83
    condbr %84, bb14, bb17
bb14:
    %85 = load u64, ptr %34
    br bb1(%85)
bb15:
    %86 = const u64 0
    br bb16(%86)
bb16(%29: u64):
    ret %29
bb17:
    unreachable
}

fn @ctor_path_data(functy.91) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %3 = const i8 10
    store i8 %3, ptr %0
    ret
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice5LevelE3newBE_(functy.92) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice5LevelE4pushBH_(functy.93) {
}

fn @_RINvMNtCs2EYQwhfuABO_4core5sliceSNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4Expr3getjEBx_(functy.94) {
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprE3lenBG_(functy.95) {
}

fn @_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_(functy.96) {
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecTNtCs6RT0DENTjyC_27clean_mutual_recursor_slice10BinderDataNtBF_4ExprEE3newBF_(functy.97) {
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecTNtCs6RT0DENTjyC_27clean_mutual_recursor_slice10BinderDataNtBH_4ExprEE3lenBH_(functy.98) {
}

fn @_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecTNtCs6RT0DENTjyC_27clean_mutual_recursor_slice10BinderDataNtBI_4ExprEEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBI_(functy.99) {
}

fn @build_minor_premise_type(functy.100) {
bb0(%0: ptr, %1: ptr, %2: ptr, %3: u32, %4: ptr, %5: ptr, %6: u32, %7: ptr, %8: ptr, %9: u64, %10: u64, %11: ptr):
    %1011 = alloca i64, align 8
    %1012 = alloca (i64, i64), align 8
    %1013 = alloca (i64, i64), align 8
    %1014 = alloca i64, align 8
    %1015 = alloca (i64, i64), align 8
    %1016 = alloca (i64, i64), align 8
    %1017 = alloca (i64, i64), align 8
    %1018 = alloca (i64, i64), align 8
    %1019 = alloca (i64, i64), align 8
    %1020 = alloca (i64, i64, i64), align 8
    %1021 = alloca (i64, i64), align 8
    %1022 = alloca i32, align 4
    %1023 = alloca (i64, i64), align 8
    %1024 = alloca (i64, i64, i64, i64, i64), align 8
    %1025 = alloca i32, align 4
    %1026 = alloca (i64, i64, i64), align 8
    %1027 = alloca (i64, i64), align 8
    %1028 = alloca (i64, i64), align 8
    %1029 = alloca (i64, i64), align 8
    %1030 = alloca (i64, i64), align 8
    %1031 = alloca (i64, i64), align 8
    %1032 = alloca (i64, i64, i64, i64, i64), align 8
    %1033 = alloca (i64, i64, i64, i64, i64), align 8
    %1034 = alloca (i64, i64, i64, i64, i64), align 8
    %1035 = alloca (i32, i32), align 4
    %1036 = alloca (i64, i64), align 8
    %1037 = alloca (i64, i64), align 8
    %1038 = alloca (i64, i64), align 8
    %1039 = alloca (i64, i64, i64, i64, i64), align 8
    %1040 = alloca (i64, i64, i64, i64, i64), align 8
    %1041 = alloca (i64, i64, i64, i64, i64), align 8
    %1042 = alloca (i64, i64), align 8
    %1043 = alloca (i64, i64, i64, i64, i64), align 8
    %1044 = alloca (i64, i64, i64, i64, i64), align 8
    %1045 = alloca (i64, i64, i64, i64, i64, i64), align 8
    %1046 = alloca (i64, i64, i64, i64, i64), align 8
    %1047 = alloca (i64, i64, i64, i64, i64), align 8
    %1048 = alloca (i64, i64, i64, i64, i64), align 8
    %1049 = alloca (i64, i64), align 8
    %1050 = alloca (i64, i64, i64, i64, i64), align 8
    %1051 = alloca (i64, i64, i64, i64, i64), align 8
    %1052 = alloca (i64, i64, i64, i64, i64), align 8
    %1053 = alloca (i64, i64), align 8
    %1054 = alloca (i64, i64), align 8
    %1055 = alloca (i64, i64), align 8
    %1056 = alloca (i64, i64), align 8
    %1057 = alloca (i64, i64), align 8
    %1058 = alloca (i64, i64), align 8
    %1059 = alloca i64, align 8
    %1060 = alloca (i64, i64), align 8
    %1061 = alloca (i64, i64), align 8
    %1062 = alloca (i64, i64), align 8
    %1063 = alloca (i64, i64), align 8
    %1064 = alloca i64, align 8
    %1065 = alloca (i64, i64), align 8
    %1066 = alloca (i64, i64), align 8
    %1067 = alloca (i64, i64, i64, i64, i64), align 8
    %1068 = alloca (i64, i64, i64, i64, i64), align 8
    %1069 = alloca i64, align 8
    %1070 = alloca (i64, i64, i64), align 8
    %1071 = alloca (i64, i64, i64, i64, i64), align 8
    %1072 = alloca (i64, i64, i64, i64, i64), align 8
    %1073 = alloca (i64, i64, i64, i64, i64), align 8
    %1074 = alloca (i64, i64), align 8
    %1075 = alloca (i64, i64, i64, i64, i64), align 8
    %1076 = alloca (i64, i64), align 8
    %1077 = alloca (i64, i64, i64, i64, i64), align 8
    %1078 = alloca (i64, i64, i64, i64, i64), align 8
    %1079 = alloca (i64, i64, i64, i64, i64), align 8
    %1080 = alloca (i64, i64, i64, i64, i64), align 8
    %1081 = alloca (i64, i64, i64, i64, i64), align 8
    %1082 = alloca (i64, i64, i64, i64, i64), align 8
    %1083 = alloca (i64, i64, i64), align 8
    %1084 = alloca i64, align 8
    %1085 = alloca (i64, i64), align 8
    %1086 = alloca i64, align 8
    %1087 = alloca (i64, i64, i64, i64, i64), align 8
    %1088 = alloca (i64, i64, i64, i64, i64), align 8
    %1089 = alloca (i8, i8), align 1
    %1090 = alloca (i64, i64, i64, i64, i64), align 8
    %1091 = alloca (i64, i64, i64, i64, i64), align 8
    %1092 = alloca (i8, i8), align 1
    %1093 = alloca (i64, i64, i64, i64, i64), align 8
    %1094 = alloca (i64, i64, i64, i64, i64), align 8
    %1095 = alloca (i64, i64), align 8
    %1096 = alloca (i64, i64), align 8
    %1097 = alloca (i64, i64, i64, i64, i64), align 8
    %1098 = alloca i64, align 8
    %1099 = alloca (i64, i64, i64, i64, i64), align 8
    %1100 = alloca (i64, i64, i64, i64, i64), align 8
    %1101 = alloca (i8, i8), align 1
    %1102 = alloca (i64, i64, i64, i64, i64), align 8
    %1103 = alloca (i64, i64, i64, i64, i64), align 8
    store u64 %9, ptr %1011
    %1104 = const bool false
    %1105 = const bool false
    %1106 = const bool false
    %1107 = const bool false
    %1108 = const bool false
    %1109 = const bool false
    %1110 = const bool false
    %1111 = const bool false
    %1112 = const bool false
    %1113 = const u64 0
    %1114 = const u64 0
    br bb1(%1, %2, %3, %6, %10, %1113, %1114)
bb1(%12: ptr, %13: ptr, %14: u32, %15: u32, %16: u64, %17: u64, %18: u64):
    %1115 = const i64 8
    %1116 = gep i8, ptr %4, %1115
    %1117 = load u64, ptr %1116
    %1118 = icmp ult u64 %18, %1117
    condbr %1118, bb2(%12, %13, %14, %15, %16, %17, %18), bb8(%12, %13, %14, %15, %16, %17)
bb2(%19: ptr, %20: ptr, %21: u32, %22: u32, %23: u64, %24: u64, %25: u64):
    %1119 = const i64 8
    %1120 = gep i8, ptr %4, %1119
    %1121 = load u64, ptr %1120
    %1122 = icmp ult u64 %25, %1121
    condbr %1122, bb3(%19, %20, %21, %22, %23, %24, %25, %25), bb143
bb3(%26: ptr, %27: ptr, %28: u32, %29: u32, %30: u64, %31: u64, %32: u64, %33: u64):
    %1123 = load ptr, ptr %4
    %1124 = gep bool, ptr %1123, %33
    %1125 = load bool, ptr %1124
    condbr %1125, bb4(%26, %27, %28, %29, %30, %31, %32), bb6(%26, %27, %28, %29, %30, %31, %32)
bb4(%34: ptr, %35: ptr, %36: u32, %37: u32, %38: u64, %39: u64, %40: u64):
    %1126 = const u64 1
    %1127, %1128 = add.overflow u64 %39, %1126
    store u64 %1127, ptr %1012
    %1129 = const i64 8
    %1130 = gep i8, ptr %1012, %1129
    store bool %1128, ptr %1130
    %1131 = const i64 8
    %1132 = gep i8, ptr %1012, %1131
    %1133 = load bool, ptr %1132
    %1134 = const bool false
    %1135 = icmp eq bool %1133, %1134
    condbr %1135, bb5(%34, %35, %36, %37, %38, %40), bb143
bb5(%41: ptr, %42: ptr, %43: u32, %44: u32, %45: u64, %46: u64):
    %1136 = load u64, ptr %1012
    br bb6(%41, %42, %43, %44, %45, %1136, %46)
bb6(%47: ptr, %48: ptr, %49: u32, %50: u32, %51: u64, %52: u64, %53: u64):
    %1137 = const u64 1
    %1138, %1139 = add.overflow u64 %53, %1137
    store u64 %1138, ptr %1013
    %1140 = const i64 8
    %1141 = gep i8, ptr %1013, %1140
    store bool %1139, ptr %1141
    %1142 = const i64 8
    %1143 = gep i8, ptr %1013, %1142
    %1144 = load bool, ptr %1143
    %1145 = const bool false
    %1146 = icmp eq bool %1144, %1145
    condbr %1146, bb7(%47, %48, %49, %50, %51, %52), bb143
bb7(%54: ptr, %55: ptr, %56: u32, %57: u32, %58: u64, %59: u64):
    %1147 = load u64, ptr %1013
    br bb1(%54, %55, %56, %57, %58, %59, %1147)
bb8(%60: ptr, %61: ptr, %62: u32, %63: u32, %64: u64, %65: u64):
    %1148 = zext u32 %62 to u64
    store u64 %1148, ptr %1014
    %1149 = load u64, ptr %1014
    %1150, %1151 = add.overflow u64 %1149, %65
    store u64 %1150, ptr %1015
    %1152 = const i64 8
    %1153 = gep i8, ptr %1015, %1152
    store bool %1151, ptr %1153
    %1154 = const i64 8
    %1155 = gep i8, ptr %1015, %1154
    %1156 = load bool, ptr %1155
    %1157 = const bool false
    %1158 = icmp eq bool %1156, %1157
    condbr %1158, bb9(%60, %61, %63, %64, %65), bb143
bb9(%66: ptr, %67: ptr, %68: u32, %69: u64, %70: u64):
    %1159 = load u64, ptr %1015
    %1160 = load u64, ptr %1011
    %1161 = const u64 1
    %1162, %1163 = sub.overflow u64 %1160, %1161
    store u64 %1162, ptr %1016
    %1164 = const i64 8
    %1165 = gep i8, ptr %1016, %1164
    store bool %1163, ptr %1165
    %1166 = const i64 8
    %1167 = gep i8, ptr %1016, %1166
    %1168 = load bool, ptr %1167
    %1169 = const bool false
    %1170 = icmp eq bool %1168, %1169
    condbr %1170, bb10(%66, %67, %68, %69, %70, %1159), bb143
bb10(%71: ptr, %72: ptr, %73: u32, %74: u64, %75: u64, %76: u64):
    %1171 = load u64, ptr %1016
    %1172, %1173 = sub.overflow u64 %1171, %74
    store u64 %1172, ptr %1017
    %1174 = const i64 8
    %1175 = gep i8, ptr %1017, %1174
    store bool %1173, ptr %1175
    %1176 = const i64 8
    %1177 = gep i8, ptr %1017, %1176
    %1178 = load bool, ptr %1177
    %1179 = const bool false
    %1180 = icmp eq bool %1178, %1179
    condbr %1180, bb11(%71, %72, %73, %74, %75, %76), bb143
bb11(%77: ptr, %78: ptr, %79: u32, %80: u64, %81: u64, %82: u64):
    %1181 = load u64, ptr %1017
    %1182, %1183 = add.overflow u64 %82, %1181
    store u64 %1182, ptr %1018
    %1184 = const i64 8
    %1185 = gep i8, ptr %1018, %1184
    store bool %1183, ptr %1185
    %1186 = const i64 8
    %1187 = gep i8, ptr %1018, %1186
    %1188 = load bool, ptr %1187
    %1189 = const bool false
    %1190 = icmp eq bool %1188, %1189
    condbr %1190, bb12(%77, %78, %79, %80, %81), bb143
bb12(%83: ptr, %84: ptr, %85: u32, %86: u64, %87: u64):
    %1191 = load u64, ptr %1018
    store ptr %1014, ptr %1019
    %1192 = const i64 8
    %1193 = gep i8, ptr %1019, %1192
    store ptr %1011, ptr %1193
    %1194 = const bool true
    call @func.92(%1020)
    br bb13(%83, %84, %85, %86, %87, %1191)
bb13(%88: ptr, %89: ptr, %90: u32, %91: u64, %92: u64, %93: u64):
    %1195 = const u64 0
    br bb14(%88, %89, %90, %91, %92, %93, %1195)
bb14(%94: ptr, %95: ptr, %96: u32, %97: u64, %98: u64, %99: u64, %100: u64):
    %1196 = const i64 8
    %1197 = gep i8, ptr %7, %1196
    %1198 = load u64, ptr %1197
    %1199 = icmp ult u64 %100, %1198
    condbr %1199, bb15(%94, %95, %96, %97, %98, %99, %100), bb19(%94, %95, %96, %97, %98, %99)
bb15(%101: ptr, %102: ptr, %103: u32, %104: u64, %105: u64, %106: u64, %107: u64):
    %1200 = const i64 8
    %1201 = gep i8, ptr %7, %1200
    %1202 = load u64, ptr %1201
    %1203 = icmp ult u64 %107, %1202
    condbr %1203, bb16(%101, %102, %103, %104, %105, %106, %107, %1020, %107), bb143
bb16(%108: ptr, %109: ptr, %110: u32, %111: u64, %112: u64, %113: u64, %114: u64, %115: ptr, %116: u64):
    %1204 = load ptr, ptr %7
    %1205 = const u64 4
    %1206 = mul u64 %116, %1205
    %1207 = gep i8, ptr %1204, %1206
    %1208 = load i32, ptr %1207
    store i32 %1208, ptr %1022
    %1209 = const i64 4
    %1210 = gep i8, ptr %1021, %1209
    %1211 = load i32, ptr %1022
    store i32 %1211, ptr %1210
    %1212 = const i32 2
    store i32 %1212, ptr %1021
    call @func.93(%115, %1021)
    br bb17(%108, %109, %110, %111, %112, %113, %114)
bb17(%117: ptr, %118: ptr, %119: u32, %120: u64, %121: u64, %122: u64, %123: u64):
    %1213 = const u64 1
    %1214, %1215 = add.overflow u64 %123, %1213
    store u64 %1214, ptr %1023
    %1216 = const i64 8
    %1217 = gep i8, ptr %1023, %1216
    store bool %1215, ptr %1217
    %1218 = const i64 8
    %1219 = gep i8, ptr %1023, %1218
    %1220 = load bool, ptr %1219
    %1221 = const bool false
    %1222 = icmp eq bool %1220, %1221
    condbr %1222, bb18(%117, %118, %119, %120, %121, %122), bb143
bb18(%124: ptr, %125: ptr, %126: u32, %127: u64, %128: u64, %129: u64):
    %1223 = load u64, ptr %1023
    br bb14(%124, %125, %126, %127, %128, %129, %1223)
bb19(%130: ptr, %131: ptr, %132: u32, %133: u64, %134: u64, %135: u64):
    %1224 = load i32, ptr %131
    store i32 %1224, ptr %1025
    %1225 = const bool false
    %1226 = load i64, ptr %1020
    store i64 %1226, ptr %1026
    %1227 = const i64 8
    %1228 = gep i8, ptr %1020, %1227
    %1229 = const i64 8
    %1230 = gep i8, ptr %1026, %1229
    %1231 = load i64, ptr %1228
    store i64 %1231, ptr %1230
    %1232 = const i64 16
    %1233 = gep i8, ptr %1020, %1232
    %1234 = const i64 16
    %1235 = gep i8, ptr %1026, %1234
    %1236 = load i64, ptr %1233
    store i64 %1236, ptr %1235
    %1237 = load u32, ptr %1025
    call @func.112(%1024, %1237, %1026)
    br bb20(%130, %132, %133, %134, %135)
bb20(%136: ptr, %137: u32, %138: u64, %139: u64, %140: u64):
    %1238 = const bool true
    %1239 = const u32 0
    br bb21(%136, %137, %138, %139, %140, %1239)
bb21(%141: ptr, %142: u32, %143: u64, %144: u64, %145: u64, %146: u32):
    %1240 = icmp ult u32 %146, %142
    condbr %1240, bb22(%141, %142, %143, %144, %145, %146), bb32(%141, %142, %143, %144, %145)
bb22(%147: ptr, %148: u32, %149: u64, %150: u64, %151: u64, %152: u32):
    %1241 = load u64, ptr %1014
    %1242, %1243 = add.overflow u64 %1241, %150
    store u64 %1242, ptr %1027
    %1244 = const i64 8
    %1245 = gep i8, ptr %1027, %1244
    store bool %1243, ptr %1245
    %1246 = const i64 8
    %1247 = gep i8, ptr %1027, %1246
    %1248 = load bool, ptr %1247
    %1249 = const bool false
    %1250 = icmp eq bool %1248, %1249
    condbr %1250, bb23(%147, %148, %149, %150, %151, %152), bb143
bb23(%153: ptr, %154: u32, %155: u64, %156: u64, %157: u64, %158: u32):
    %1251 = load u64, ptr %1027
    %1252 = load u64, ptr %1011
    %1253, %1254 = add.overflow u64 %1251, %1252
    store u64 %1253, ptr %1028
    %1255 = const i64 8
    %1256 = gep i8, ptr %1028, %1255
    store bool %1254, ptr %1256
    %1257 = const i64 8
    %1258 = gep i8, ptr %1028, %1257
    %1259 = load bool, ptr %1258
    %1260 = const bool false
    %1261 = icmp eq bool %1259, %1260
    condbr %1261, bb24(%153, %154, %155, %156, %157, %158), bb143
bb24(%159: ptr, %160: u32, %161: u64, %162: u64, %163: u64, %164: u32):
    %1262 = load u64, ptr %1028
    %1263 = zext u32 %160 to u64
    %1264 = const u64 1
    %1265, %1266 = sub.overflow u64 %1263, %1264
    store u64 %1265, ptr %1029
    %1267 = const i64 8
    %1268 = gep i8, ptr %1029, %1267
    store bool %1266, ptr %1268
    %1269 = const i64 8
    %1270 = gep i8, ptr %1029, %1269
    %1271 = load bool, ptr %1270
    %1272 = const bool false
    %1273 = icmp eq bool %1271, %1272
    condbr %1273, bb25(%159, %160, %161, %162, %163, %164, %1262), bb143
bb25(%165: ptr, %166: u32, %167: u64, %168: u64, %169: u64, %170: u32, %171: u64):
    %1274 = load u64, ptr %1029
    %1275 = zext u32 %170 to u64
    %1276, %1277 = sub.overflow u64 %1274, %1275
    store u64 %1276, ptr %1030
    %1278 = const i64 8
    %1279 = gep i8, ptr %1030, %1278
    store bool %1277, ptr %1279
    %1280 = const i64 8
    %1281 = gep i8, ptr %1030, %1280
    %1282 = load bool, ptr %1281
    %1283 = const bool false
    %1284 = icmp eq bool %1282, %1283
    condbr %1284, bb26(%165, %166, %167, %168, %169, %170, %171), bb143
bb26(%172: ptr, %173: u32, %174: u64, %175: u64, %176: u64, %177: u32, %178: u64):
    %1285 = load u64, ptr %1030
    %1286, %1287 = add.overflow u64 %178, %1285
    store u64 %1286, ptr %1031
    %1288 = const i64 8
    %1289 = gep i8, ptr %1031, %1288
    store bool %1287, ptr %1289
    %1290 = const i64 8
    %1291 = gep i8, ptr %1031, %1290
    %1292 = load bool, ptr %1291
    %1293 = const bool false
    %1294 = icmp eq bool %1292, %1293
    condbr %1294, bb27(%172, %173, %174, %175, %176, %177), bb143
bb27(%179: ptr, %180: u32, %181: u64, %182: u64, %183: u64, %184: u32):
    %1295 = load u64, ptr %1031
    %1296 = const bool false
    %1297 = const bool true
    %1298 = load i64, ptr %1024
    store i64 %1298, ptr %1033
    %1299 = const i64 8
    %1300 = gep i8, ptr %1024, %1299
    %1301 = const i64 8
    %1302 = gep i8, ptr %1033, %1301
    %1303 = load i64, ptr %1300
    store i64 %1303, ptr %1302
    %1304 = const i64 16
    %1305 = gep i8, ptr %1024, %1304
    %1306 = const i64 16
    %1307 = gep i8, ptr %1033, %1306
    %1308 = load i64, ptr %1305
    store i64 %1308, ptr %1307
    %1309 = const i64 24
    %1310 = gep i8, ptr %1024, %1309
    %1311 = const i64 24
    %1312 = gep i8, ptr %1033, %1311
    %1313 = load i64, ptr %1310
    store i64 %1313, ptr %1312
    %1314 = const i64 32
    %1315 = gep i8, ptr %1024, %1314
    %1316 = const i64 32
    %1317 = gep i8, ptr %1033, %1316
    %1318 = load i64, ptr %1315
    store i64 %1318, ptr %1317
    %1319 = call @func.103(%1295)
    br bb28(%179, %180, %181, %182, %183, %184, %1319)
bb28(%185: ptr, %186: u32, %187: u64, %188: u64, %189: u64, %190: u32, %191: u32):
    call @func.83(%1034, %191)
    br bb29(%185, %186, %187, %188, %189, %190)
bb29(%192: ptr, %193: u32, %194: u64, %195: u64, %196: u64, %197: u32):
    %1320 = const bool false
    call @func.84(%1032, %1033, %1034)
    br bb30(%192, %193, %194, %195, %196, %197)
bb30(%198: ptr, %199: u32, %200: u64, %201: u64, %202: u64, %203: u32):
    %1321 = const bool false
    %1322 = const bool true
    %1323 = load i64, ptr %1032
    store i64 %1323, ptr %1024
    %1324 = const i64 8
    %1325 = gep i8, ptr %1032, %1324
    %1326 = const i64 8
    %1327 = gep i8, ptr %1024, %1326
    %1328 = load i64, ptr %1325
    store i64 %1328, ptr %1327
    %1329 = const i64 16
    %1330 = gep i8, ptr %1032, %1329
    %1331 = const i64 16
    %1332 = gep i8, ptr %1024, %1331
    %1333 = load i64, ptr %1330
    store i64 %1333, ptr %1332
    %1334 = const i64 24
    %1335 = gep i8, ptr %1032, %1334
    %1336 = const i64 24
    %1337 = gep i8, ptr %1024, %1336
    %1338 = load i64, ptr %1335
    store i64 %1338, ptr %1337
    %1339 = const i64 32
    %1340 = gep i8, ptr %1032, %1339
    %1341 = const i64 32
    %1342 = gep i8, ptr %1024, %1341
    %1343 = load i64, ptr %1340
    store i64 %1343, ptr %1342
    %1344 = const u32 1
    %1345, %1346 = add.overflow u32 %203, %1344
    store u32 %1345, ptr %1035
    %1347 = const i64 4
    %1348 = gep i8, ptr %1035, %1347
    store bool %1346, ptr %1348
    %1349 = const i64 4
    %1350 = gep i8, ptr %1035, %1349
    %1351 = load bool, ptr %1350
    %1352 = const bool false
    %1353 = icmp eq bool %1351, %1352
    condbr %1353, bb31(%198, %199, %200, %201, %202), bb143
bb31(%204: ptr, %205: u32, %206: u64, %207: u64, %208: u64):
    %1354 = load u32, ptr %1035
    br bb21(%204, %205, %206, %207, %208, %1354)
bb32(%209: ptr, %210: u32, %211: u64, %212: u64, %213: u64):
    %1355 = const u64 0
    br bb33(%209, %210, %211, %212, %213, %1355)
bb33(%214: ptr, %215: u32, %216: u64, %217: u64, %218: u64, %219: u64):
    %1356 = load u64, ptr %1014
    %1357 = icmp ult u64 %219, %1356
    condbr %1357, bb34(%214, %215, %216, %217, %218, %219), bb42(%214, %215, %216, %217, %218)
bb34(%220: ptr, %221: u32, %222: u64, %223: u64, %224: u64, %225: u64):
    %1358 = load u64, ptr %1014
    %1359 = const u64 1
    %1360, %1361 = sub.overflow u64 %1358, %1359
    store u64 %1360, ptr %1036
    %1362 = const i64 8
    %1363 = gep i8, ptr %1036, %1362
    store bool %1361, ptr %1363
    %1364 = const i64 8
    %1365 = gep i8, ptr %1036, %1364
    %1366 = load bool, ptr %1365
    %1367 = const bool false
    %1368 = icmp eq bool %1366, %1367
    condbr %1368, bb35(%220, %221, %222, %223, %224, %225), bb143
bb35(%226: ptr, %227: u32, %228: u64, %229: u64, %230: u64, %231: u64):
    %1369 = load u64, ptr %1036
    %1370, %1371 = sub.overflow u64 %1369, %231
    store u64 %1370, ptr %1037
    %1372 = const i64 8
    %1373 = gep i8, ptr %1037, %1372
    store bool %1371, ptr %1373
    %1374 = const i64 8
    %1375 = gep i8, ptr %1037, %1374
    %1376 = load bool, ptr %1375
    %1377 = const bool false
    %1378 = icmp eq bool %1376, %1377
    condbr %1378, bb36(%226, %227, %228, %229, %230, %231), bb143
bb36(%232: ptr, %233: u32, %234: u64, %235: u64, %236: u64, %237: u64):
    %1379 = load u64, ptr %1037
    %1380, %1381 = add.overflow u64 %1379, %235
    store u64 %1380, ptr %1038
    %1382 = const i64 8
    %1383 = gep i8, ptr %1038, %1382
    store bool %1381, ptr %1383
    %1384 = const i64 8
    %1385 = gep i8, ptr %1038, %1384
    %1386 = load bool, ptr %1385
    %1387 = const bool false
    %1388 = icmp eq bool %1386, %1387
    condbr %1388, bb37(%232, %233, %234, %235, %236, %237), bb143
bb37(%238: ptr, %239: u32, %240: u64, %241: u64, %242: u64, %243: u64):
    %1389 = load u64, ptr %1038
    %1390 = const bool false
    %1391 = const bool true
    %1392 = load i64, ptr %1024
    store i64 %1392, ptr %1040
    %1393 = const i64 8
    %1394 = gep i8, ptr %1024, %1393
    %1395 = const i64 8
    %1396 = gep i8, ptr %1040, %1395
    %1397 = load i64, ptr %1394
    store i64 %1397, ptr %1396
    %1398 = const i64 16
    %1399 = gep i8, ptr %1024, %1398
    %1400 = const i64 16
    %1401 = gep i8, ptr %1040, %1400
    %1402 = load i64, ptr %1399
    store i64 %1402, ptr %1401
    %1403 = const i64 24
    %1404 = gep i8, ptr %1024, %1403
    %1405 = const i64 24
    %1406 = gep i8, ptr %1040, %1405
    %1407 = load i64, ptr %1404
    store i64 %1407, ptr %1406
    %1408 = const i64 32
    %1409 = gep i8, ptr %1024, %1408
    %1410 = const i64 32
    %1411 = gep i8, ptr %1040, %1410
    %1412 = load i64, ptr %1409
    store i64 %1412, ptr %1411
    %1413 = call @func.103(%1389)
    br bb38(%238, %239, %240, %241, %242, %243, %1413)
bb38(%244: ptr, %245: u32, %246: u64, %247: u64, %248: u64, %249: u64, %250: u32):
    call @func.83(%1041, %250)
    br bb39(%244, %245, %246, %247, %248, %249)
bb39(%251: ptr, %252: u32, %253: u64, %254: u64, %255: u64, %256: u64):
    %1414 = const bool false
    call @func.84(%1039, %1040, %1041)
    br bb40(%251, %252, %253, %254, %255, %256)
bb40(%257: ptr, %258: u32, %259: u64, %260: u64, %261: u64, %262: u64):
    %1415 = const bool false
    %1416 = const bool true
    %1417 = load i64, ptr %1039
    store i64 %1417, ptr %1024
    %1418 = const i64 8
    %1419 = gep i8, ptr %1039, %1418
    %1420 = const i64 8
    %1421 = gep i8, ptr %1024, %1420
    %1422 = load i64, ptr %1419
    store i64 %1422, ptr %1421
    %1423 = const i64 16
    %1424 = gep i8, ptr %1039, %1423
    %1425 = const i64 16
    %1426 = gep i8, ptr %1024, %1425
    %1427 = load i64, ptr %1424
    store i64 %1427, ptr %1426
    %1428 = const i64 24
    %1429 = gep i8, ptr %1039, %1428
    %1430 = const i64 24
    %1431 = gep i8, ptr %1024, %1430
    %1432 = load i64, ptr %1429
    store i64 %1432, ptr %1431
    %1433 = const i64 32
    %1434 = gep i8, ptr %1039, %1433
    %1435 = const i64 32
    %1436 = gep i8, ptr %1024, %1435
    %1437 = load i64, ptr %1434
    store i64 %1437, ptr %1436
    %1438 = const u64 1
    %1439, %1440 = add.overflow u64 %262, %1438
    store u64 %1439, ptr %1042
    %1441 = const i64 8
    %1442 = gep i8, ptr %1042, %1441
    store bool %1440, ptr %1442
    %1443 = const i64 8
    %1444 = gep i8, ptr %1042, %1443
    %1445 = load bool, ptr %1444
    %1446 = const bool false
    %1447 = icmp eq bool %1445, %1446
    condbr %1447, bb41(%257, %258, %259, %260, %261), bb143
bb41(%263: ptr, %264: u32, %265: u64, %266: u64, %267: u64):
    %1448 = load u64, ptr %1042
    br bb33(%263, %264, %265, %266, %267, %1448)
bb42(%268: ptr, %269: u32, %270: u64, %271: u64, %272: u64):
    %1449 = call @func.103(%272)
    br bb43(%268, %269, %270, %271, %1449)
bb43(%273: ptr, %274: u32, %275: u64, %276: u64, %277: u32):
    call @func.83(%1043, %277)
    br bb44(%273, %274, %275, %276)
bb44(%278: ptr, %279: u32, %280: u64, %281: u64):
    %1450 = const bool true
    %1451 = const u64 0
    br bb45(%278, %279, %280, %281, %1451)
bb45(%282: ptr, %283: u32, %284: u64, %285: u64, %286: u64):
    %1452 = const i64 8
    %1453 = gep i8, ptr %8, %1452
    %1454 = load u64, ptr %1453
    %1455 = icmp ult u64 %286, %1454
    condbr %1455, bb46(%282, %283, %284, %285, %286), bb52(%282, %283, %284, %285)
bb46(%287: ptr, %288: u32, %289: u64, %290: u64, %291: u64):
    %1456 = const i64 8
    %1457 = gep i8, ptr %8, %1456
    %1458 = load u64, ptr %1457
    %1459 = icmp ult u64 %291, %1458
    condbr %1459, bb47(%287, %288, %289, %290, %291, %1019, %291), bb143
bb47(%292: ptr, %293: u32, %294: u64, %295: u64, %296: u64, %297: ptr, %298: u64):
    %1460 = load ptr, ptr %8
    %1461 = const u64 40
    %1462 = mul u64 %298, %1461
    %1463 = gep i8, ptr %1460, %1462
    call @func.78(%1046, %1463)
    br bb48(%292, %293, %294, %295, %296, %297)
bb48(%299: ptr, %300: u32, %301: u64, %302: u64, %303: u64, %304: ptr):
    %1464 = load i64, ptr %1046
    store i64 %1464, ptr %1045
    %1465 = const i64 8
    %1466 = gep i8, ptr %1046, %1465
    %1467 = const i64 8
    %1468 = gep i8, ptr %1045, %1467
    %1469 = load i64, ptr %1466
    store i64 %1469, ptr %1468
    %1470 = const i64 16
    %1471 = gep i8, ptr %1046, %1470
    %1472 = const i64 16
    %1473 = gep i8, ptr %1045, %1472
    %1474 = load i64, ptr %1471
    store i64 %1474, ptr %1473
    %1475 = const i64 24
    %1476 = gep i8, ptr %1046, %1475
    %1477 = const i64 24
    %1478 = gep i8, ptr %1045, %1477
    %1479 = load i64, ptr %1476
    store i64 %1479, ptr %1478
    %1480 = const i64 32
    %1481 = gep i8, ptr %1046, %1480
    %1482 = const i64 32
    %1483 = gep i8, ptr %1045, %1482
    %1484 = load i64, ptr %1481
    store i64 %1484, ptr %1483
    %1485 = const i64 40
    %1486 = gep i8, ptr %1045, %1485
    store u64 %302, ptr %1486
    %1487 = const i64 40
    %1488 = gep i8, ptr %1045, %1487
    %1489 = load u64, ptr %1488
    call @func.130(%1044, %304, %1045, %1489)
    br bb49(%299, %300, %301, %302, %303)
bb49(%305: ptr, %306: u32, %307: u64, %308: u64, %309: u64):
    %1490 = const bool false
    %1491 = load i64, ptr %1043
    store i64 %1491, ptr %1048
    %1492 = const i64 8
    %1493 = gep i8, ptr %1043, %1492
    %1494 = const i64 8
    %1495 = gep i8, ptr %1048, %1494
    %1496 = load i64, ptr %1493
    store i64 %1496, ptr %1495
    %1497 = const i64 16
    %1498 = gep i8, ptr %1043, %1497
    %1499 = const i64 16
    %1500 = gep i8, ptr %1048, %1499
    %1501 = load i64, ptr %1498
    store i64 %1501, ptr %1500
    %1502 = const i64 24
    %1503 = gep i8, ptr %1043, %1502
    %1504 = const i64 24
    %1505 = gep i8, ptr %1048, %1504
    %1506 = load i64, ptr %1503
    store i64 %1506, ptr %1505
    %1507 = const i64 32
    %1508 = gep i8, ptr %1043, %1507
    %1509 = const i64 32
    %1510 = gep i8, ptr %1048, %1509
    %1511 = load i64, ptr %1508
    store i64 %1511, ptr %1510
    call @func.84(%1047, %1048, %1044)
    br bb50(%305, %306, %307, %308, %309)
bb50(%310: ptr, %311: u32, %312: u64, %313: u64, %314: u64):
    %1512 = const bool true
    %1513 = load i64, ptr %1047
    store i64 %1513, ptr %1043
    %1514 = const i64 8
    %1515 = gep i8, ptr %1047, %1514
    %1516 = const i64 8
    %1517 = gep i8, ptr %1043, %1516
    %1518 = load i64, ptr %1515
    store i64 %1518, ptr %1517
    %1519 = const i64 16
    %1520 = gep i8, ptr %1047, %1519
    %1521 = const i64 16
    %1522 = gep i8, ptr %1043, %1521
    %1523 = load i64, ptr %1520
    store i64 %1523, ptr %1522
    %1524 = const i64 24
    %1525 = gep i8, ptr %1047, %1524
    %1526 = const i64 24
    %1527 = gep i8, ptr %1043, %1526
    %1528 = load i64, ptr %1525
    store i64 %1528, ptr %1527
    %1529 = const i64 32
    %1530 = gep i8, ptr %1047, %1529
    %1531 = const i64 32
    %1532 = gep i8, ptr %1043, %1531
    %1533 = load i64, ptr %1530
    store i64 %1533, ptr %1532
    %1534 = const u64 1
    %1535, %1536 = add.overflow u64 %314, %1534
    store u64 %1535, ptr %1049
    %1537 = const i64 8
    %1538 = gep i8, ptr %1049, %1537
    store bool %1536, ptr %1538
    %1539 = const i64 8
    %1540 = gep i8, ptr %1049, %1539
    %1541 = load bool, ptr %1540
    %1542 = const bool false
    %1543 = icmp eq bool %1541, %1542
    condbr %1543, bb51(%310, %311, %312, %313), bb143
bb51(%315: ptr, %316: u32, %317: u64, %318: u64):
    %1544 = load u64, ptr %1049
    br bb45(%315, %316, %317, %318, %1544)
bb52(%319: ptr, %320: u32, %321: u64, %322: u64):
    %1545 = const bool false
    %1546 = load i64, ptr %1043
    store i64 %1546, ptr %1051
    %1547 = const i64 8
    %1548 = gep i8, ptr %1043, %1547
    %1549 = const i64 8
    %1550 = gep i8, ptr %1051, %1549
    %1551 = load i64, ptr %1548
    store i64 %1551, ptr %1550
    %1552 = const i64 16
    %1553 = gep i8, ptr %1043, %1552
    %1554 = const i64 16
    %1555 = gep i8, ptr %1051, %1554
    %1556 = load i64, ptr %1553
    store i64 %1556, ptr %1555
    %1557 = const i64 24
    %1558 = gep i8, ptr %1043, %1557
    %1559 = const i64 24
    %1560 = gep i8, ptr %1051, %1559
    %1561 = load i64, ptr %1558
    store i64 %1561, ptr %1560
    %1562 = const i64 32
    %1563 = gep i8, ptr %1043, %1562
    %1564 = const i64 32
    %1565 = gep i8, ptr %1051, %1564
    %1566 = load i64, ptr %1563
    store i64 %1566, ptr %1565
    %1567 = const bool false
    %1568 = load i64, ptr %1024
    store i64 %1568, ptr %1052
    %1569 = const i64 8
    %1570 = gep i8, ptr %1024, %1569
    %1571 = const i64 8
    %1572 = gep i8, ptr %1052, %1571
    %1573 = load i64, ptr %1570
    store i64 %1573, ptr %1572
    %1574 = const i64 16
    %1575 = gep i8, ptr %1024, %1574
    %1576 = const i64 16
    %1577 = gep i8, ptr %1052, %1576
    %1578 = load i64, ptr %1575
    store i64 %1578, ptr %1577
    %1579 = const i64 24
    %1580 = gep i8, ptr %1024, %1579
    %1581 = const i64 24
    %1582 = gep i8, ptr %1052, %1581
    %1583 = load i64, ptr %1580
    store i64 %1583, ptr %1582
    %1584 = const i64 32
    %1585 = gep i8, ptr %1024, %1584
    %1586 = const i64 32
    %1587 = gep i8, ptr %1052, %1586
    %1588 = load i64, ptr %1585
    store i64 %1588, ptr %1587
    call @func.84(%1050, %1051, %1052)
    br bb53(%319, %320, %321, %322)
bb53(%323: ptr, %324: u32, %325: u64, %326: u64):
    %1589 = const bool true
    %1590 = load i64, ptr %1050
    store i64 %1590, ptr %1043
    %1591 = const i64 8
    %1592 = gep i8, ptr %1050, %1591
    %1593 = const i64 8
    %1594 = gep i8, ptr %1043, %1593
    %1595 = load i64, ptr %1592
    store i64 %1595, ptr %1594
    %1596 = const i64 16
    %1597 = gep i8, ptr %1050, %1596
    %1598 = const i64 16
    %1599 = gep i8, ptr %1043, %1598
    %1600 = load i64, ptr %1597
    store i64 %1600, ptr %1599
    %1601 = const i64 24
    %1602 = gep i8, ptr %1050, %1601
    %1603 = const i64 24
    %1604 = gep i8, ptr %1043, %1603
    %1605 = load i64, ptr %1602
    store i64 %1605, ptr %1604
    %1606 = const i64 32
    %1607 = gep i8, ptr %1050, %1606
    %1608 = const i64 32
    %1609 = gep i8, ptr %1043, %1608
    %1610 = load i64, ptr %1607
    store i64 %1610, ptr %1609
    %1611 = const u64 0
    %1612 = const i64 8
    %1613 = gep i8, ptr %4, %1612
    %1614 = load u64, ptr %1613
    br bb54(%323, %324, %325, %326, %1611, %1614)
bb54(%327: ptr, %328: u32, %329: u64, %330: u64, %331: u64, %332: u64):
    %1615 = const u64 0
    %1616 = icmp ugt u64 %332, %1615
    condbr %1616, bb55(%327, %328, %329, %330, %331, %332), bb121(%327)
bb55(%333: ptr, %334: u32, %335: u64, %336: u64, %337: u64, %338: u64):
    %1617 = const u64 1
    %1618, %1619 = sub.overflow u64 %338, %1617
    store u64 %1618, ptr %1053
    %1620 = const i64 8
    %1621 = gep i8, ptr %1053, %1620
    store bool %1619, ptr %1621
    %1622 = const i64 8
    %1623 = gep i8, ptr %1053, %1622
    %1624 = load bool, ptr %1623
    %1625 = const bool false
    %1626 = icmp eq bool %1624, %1625
    condbr %1626, bb56(%333, %334, %335, %336, %337), bb143
bb56(%339: ptr, %340: u32, %341: u64, %342: u64, %343: u64):
    %1627 = load u64, ptr %1053
    %1628 = const i64 8
    %1629 = gep i8, ptr %4, %1628
    %1630 = load u64, ptr %1629
    %1631 = icmp ult u64 %1627, %1630
    condbr %1631, bb57(%339, %340, %341, %342, %343, %1627, %1627), bb143
bb57(%344: ptr, %345: u32, %346: u64, %347: u64, %348: u64, %349: u64, %350: u64):
    %1632 = load ptr, ptr %4
    %1633 = gep bool, ptr %1632, %350
    %1634 = load bool, ptr %1633
    condbr %1634, bb58(%344, %345, %346, %347, %348, %349, %350), bb54(%344, %345, %346, %347, %348, %349)
bb58(%351: ptr, %352: u32, %353: u64, %354: u64, %355: u64, %356: u64, %357: u64):
    %1635 = const u64 1
    %1636, %1637 = sub.overflow u64 %354, %1635
    store u64 %1636, ptr %1054
    %1638 = const i64 8
    %1639 = gep i8, ptr %1054, %1638
    store bool %1637, ptr %1639
    %1640 = const i64 8
    %1641 = gep i8, ptr %1054, %1640
    %1642 = load bool, ptr %1641
    %1643 = const bool false
    %1644 = icmp eq bool %1642, %1643
    condbr %1644, bb59(%351, %352, %353, %354, %355, %356, %357), bb143
bb59(%358: ptr, %359: u32, %360: u64, %361: u64, %362: u64, %363: u64, %364: u64):
    %1645 = load u64, ptr %1054
    %1646, %1647 = sub.overflow u64 %1645, %362
    store u64 %1646, ptr %1055
    %1648 = const i64 8
    %1649 = gep i8, ptr %1055, %1648
    store bool %1647, ptr %1649
    %1650 = const i64 8
    %1651 = gep i8, ptr %1055, %1650
    %1652 = load bool, ptr %1651
    %1653 = const bool false
    %1654 = icmp eq bool %1652, %1653
    condbr %1654, bb60(%358, %359, %360, %361, %362, %363, %364), bb143
bb60(%365: ptr, %366: u32, %367: u64, %368: u64, %369: u64, %370: u64, %371: u64):
    %1655 = load u64, ptr %1055
    %1656 = load u64, ptr %1014
    %1657 = const u64 1
    %1658, %1659 = sub.overflow u64 %1656, %1657
    store u64 %1658, ptr %1056
    %1660 = const i64 8
    %1661 = gep i8, ptr %1056, %1660
    store bool %1659, ptr %1661
    %1662 = const i64 8
    %1663 = gep i8, ptr %1056, %1662
    %1664 = load bool, ptr %1663
    %1665 = const bool false
    %1666 = icmp eq bool %1664, %1665
    condbr %1666, bb61(%365, %366, %367, %368, %369, %370, %371, %1655), bb143
bb61(%372: ptr, %373: u32, %374: u64, %375: u64, %376: u64, %377: u64, %378: u64, %379: u64):
    %1667 = load u64, ptr %1056
    %1668, %1669 = sub.overflow u64 %1667, %378
    store u64 %1668, ptr %1057
    %1670 = const i64 8
    %1671 = gep i8, ptr %1057, %1670
    store bool %1669, ptr %1671
    %1672 = const i64 8
    %1673 = gep i8, ptr %1057, %1672
    %1674 = load bool, ptr %1673
    %1675 = const bool false
    %1676 = icmp eq bool %1674, %1675
    condbr %1676, bb62(%372, %373, %374, %375, %376, %377, %378, %379), bb143
bb62(%380: ptr, %381: u32, %382: u64, %383: u64, %384: u64, %385: u64, %386: u64, %387: u64):
    %1677 = load u64, ptr %1057
    %1678, %1679 = add.overflow u64 %1677, %387
    store u64 %1678, ptr %1058
    %1680 = const i64 8
    %1681 = gep i8, ptr %1058, %1680
    store bool %1679, ptr %1681
    %1682 = const i64 8
    %1683 = gep i8, ptr %1058, %1682
    %1684 = load bool, ptr %1683
    %1685 = const bool false
    %1686 = icmp eq bool %1684, %1685
    condbr %1686, bb63(%380, %381, %382, %383, %384, %385, %386, %387), bb143
bb63(%388: ptr, %389: u32, %390: u64, %391: u64, %392: u64, %393: u64, %394: u64, %395: u64):
    %1687 = load u64, ptr %1058
    call @func.94(%1059, %5, %394)
    br bb64(%388, %389, %390, %391, %392, %393, %394, %395, %1687)
bb64(%396: ptr, %397: u32, %398: u64, %399: u64, %400: u64, %401: u64, %402: u64, %403: u64, %404: u64):
    %1688 = load i64, ptr %1059
    %1689 = const i64 0
    %1690 = icmp eq i64 %1688, %1689
    %1691 = const i64 0
    %1692 = const i64 1
    %1693 = select i64 %1690, %1691, %1692
    switch %1693 [ 0: bb66(%396, %397, %398, %399, %400, %401, %402, %403, %404) 1: bb67(%396, %397, %398, %399, %400, %401, %402, %403, %404) default: bb65 ]
bb65:
    unreachable
bb66(%405: ptr, %406: u32, %407: u64, %408: u64, %409: u64, %410: u64, %411: u64, %412: u64, %413: u64):
    br bb68(%405, %406, %407, %408, %409, %410, %411, %412, %413, %407)
bb67(%414: ptr, %415: u32, %416: u64, %417: u64, %418: u64, %419: u64, %420: u64, %421: u64, %422: u64):
    %1694 = load ptr, ptr %1059
    %1695 = call @func.132(%1694, %11)
    br bb134(%414, %415, %416, %417, %418, %419, %420, %421, %422, %1695)
bb68(%423: ptr, %424: u32, %425: u64, %426: u64, %427: u64, %428: u64, %429: u64, %430: u64, %431: u64, %432: u64):
    %1696 = load u64, ptr %1014
    %1697, %1698 = add.overflow u64 %1696, %430
    store u64 %1697, ptr %1060
    %1699 = const i64 8
    %1700 = gep i8, ptr %1060, %1699
    store bool %1698, ptr %1700
    %1701 = const i64 8
    %1702 = gep i8, ptr %1060, %1701
    %1703 = load bool, ptr %1702
    %1704 = const bool false
    %1705 = icmp eq bool %1703, %1704
    condbr %1705, bb69(%423, %424, %425, %426, %427, %428, %429, %430, %431, %432), bb143
bb69(%433: ptr, %434: u32, %435: u64, %436: u64, %437: u64, %438: u64, %439: u64, %440: u64, %441: u64, %442: u64):
    %1706 = load u64, ptr %1060
    %1707 = load u64, ptr %1011
    %1708 = const u64 1
    %1709, %1710 = sub.overflow u64 %1707, %1708
    store u64 %1709, ptr %1061
    %1711 = const i64 8
    %1712 = gep i8, ptr %1061, %1711
    store bool %1710, ptr %1712
    %1713 = const i64 8
    %1714 = gep i8, ptr %1061, %1713
    %1715 = load bool, ptr %1714
    %1716 = const bool false
    %1717 = icmp eq bool %1715, %1716
    condbr %1717, bb70(%433, %434, %435, %436, %437, %438, %439, %440, %441, %442, %1706), bb143
bb70(%443: ptr, %444: u32, %445: u64, %446: u64, %447: u64, %448: u64, %449: u64, %450: u64, %451: u64, %452: u64, %453: u64):
    %1718 = load u64, ptr %1061
    %1719, %1720 = sub.overflow u64 %1718, %452
    store u64 %1719, ptr %1062
    %1721 = const i64 8
    %1722 = gep i8, ptr %1062, %1721
    store bool %1720, ptr %1722
    %1723 = const i64 8
    %1724 = gep i8, ptr %1062, %1723
    %1725 = load bool, ptr %1724
    %1726 = const bool false
    %1727 = icmp eq bool %1725, %1726
    condbr %1727, bb71(%443, %444, %445, %446, %447, %448, %449, %450, %451, %453), bb143
bb71(%454: ptr, %455: u32, %456: u64, %457: u64, %458: u64, %459: u64, %460: u64, %461: u64, %462: u64, %463: u64):
    %1728 = load u64, ptr %1062
    %1729, %1730 = add.overflow u64 %463, %1728
    store u64 %1729, ptr %1063
    %1731 = const i64 8
    %1732 = gep i8, ptr %1063, %1731
    store bool %1730, ptr %1732
    %1733 = const i64 8
    %1734 = gep i8, ptr %1063, %1733
    %1735 = load bool, ptr %1734
    %1736 = const bool false
    %1737 = icmp eq bool %1735, %1736
    condbr %1737, bb72(%454, %455, %456, %457, %458, %459, %460, %461, %462), bb143
bb72(%464: ptr, %465: u32, %466: u64, %467: u64, %468: u64, %469: u64, %470: u64, %471: u64, %472: u64):
    %1738 = load u64, ptr %1063
    call @func.94(%1064, %5, %470)
    br bb73(%464, %465, %466, %467, %468, %469, %470, %471, %472, %1738)
bb73(%473: ptr, %474: u32, %475: u64, %476: u64, %477: u64, %478: u64, %479: u64, %480: u64, %481: u64, %482: u64):
    %1739 = load i64, ptr %1064
    %1740 = const i64 0
    %1741 = icmp eq i64 %1739, %1740
    %1742 = const i64 0
    %1743 = const i64 1
    %1744 = select i64 %1741, %1742, %1743
    switch %1744 [ 0: bb74(%473, %474, %475, %476, %477, %478, %479, %480, %481, %482) 1: bb75(%473, %474, %475, %476, %477, %478, %479, %480, %481, %482) default: bb65 ]
bb74(%483: ptr, %484: u32, %485: u64, %486: u64, %487: u64, %488: u64, %489: u64, %490: u64, %491: u64, %492: u64):
    %1745 = const u64 0
    br bb76(%483, %484, %485, %486, %487, %488, %489, %490, %491, %492, %1745)
bb75(%493: ptr, %494: u32, %495: u64, %496: u64, %497: u64, %498: u64, %499: u64, %500: u64, %501: u64, %502: u64):
    %1746 = load ptr, ptr %1064
    %1747 = call @func.109(%1746)
    br bb135(%493, %494, %495, %496, %497, %498, %499, %500, %501, %502, %1747)
bb76(%503: ptr, %504: u32, %505: u64, %506: u64, %507: u64, %508: u64, %509: u64, %510: u64, %511: u64, %512: u64, %513: u64):
    %1748, %1749 = add.overflow u64 %512, %513
    store u64 %1748, ptr %1065
    %1750 = const i64 8
    %1751 = gep i8, ptr %1065, %1750
    store bool %1749, ptr %1751
    %1752 = const i64 8
    %1753 = gep i8, ptr %1065, %1752
    %1754 = load bool, ptr %1753
    %1755 = const bool false
    %1756 = icmp eq bool %1754, %1755
    condbr %1756, bb77(%503, %504, %505, %506, %507, %508, %509, %510, %511, %513), bb143
bb77(%514: ptr, %515: u32, %516: u64, %517: u64, %518: u64, %519: u64, %520: u64, %521: u64, %522: u64, %523: u64):
    %1757 = load u64, ptr %1065
    %1758, %1759 = add.overflow u64 %522, %523
    store u64 %1758, ptr %1066
    %1760 = const i64 8
    %1761 = gep i8, ptr %1066, %1760
    store bool %1759, ptr %1761
    %1762 = const i64 8
    %1763 = gep i8, ptr %1066, %1762
    %1764 = load bool, ptr %1763
    %1765 = const bool false
    %1766 = icmp eq bool %1764, %1765
    condbr %1766, bb78(%514, %515, %516, %517, %518, %519, %520, %521, %523, %1757), bb143
bb78(%524: ptr, %525: u32, %526: u64, %527: u64, %528: u64, %529: u64, %530: u64, %531: u64, %532: u64, %533: u64):
    %1767 = load u64, ptr %1066
    %1768 = call @func.103(%533)
    br bb79(%524, %525, %526, %527, %528, %529, %530, %531, %532, %1767, %1768)
bb79(%534: ptr, %535: u32, %536: u64, %537: u64, %538: u64, %539: u64, %540: u64, %541: u64, %542: u64, %543: u64, %544: u32):
    call @func.83(%1067, %544)
    br bb80(%534, %535, %536, %537, %538, %539, %540, %541, %542, %543)
bb80(%545: ptr, %546: u32, %547: u64, %548: u64, %549: u64, %550: u64, %551: u64, %552: u64, %553: u64, %554: u64):
    %1769 = const bool true
    call @func.94(%1069, %5, %551)
    br bb81(%545, %546, %547, %548, %549, %550, %551, %552, %553, %554)
bb81(%555: ptr, %556: u32, %557: u64, %558: u64, %559: u64, %560: u64, %561: u64, %562: u64, %563: u64, %564: u64):
    %1770 = load i64, ptr %1069
    %1771 = const i64 0
    %1772 = icmp eq i64 %1770, %1771
    %1773 = const i64 0
    %1774 = const i64 1
    %1775 = select i64 %1772, %1773, %1774
    switch %1775 [ 0: bb82(%555, %556, %557, %558, %559, %560, %561, %562, %563, %564) 1: bb83(%555, %556, %557, %558, %559, %560, %561, %562, %563, %564) default: bb65 ]
bb82(%565: ptr, %566: u32, %567: u64, %568: u64, %569: u64, %570: u64, %571: u64, %572: u64, %573: u64, %574: u64):
    call @func.74(%1068, %565, %7)
    br bb136(%565, %566, %567, %568, %569, %570, %571, %572, %573, %574)
bb83(%575: ptr, %576: u32, %577: u64, %578: u64, %579: u64, %580: u64, %581: u64, %582: u64, %583: u64, %584: u64):
    %1776 = load ptr, ptr %1069
    call @func.78(%1068, %1776)
    br bb137(%575, %576, %577, %578, %579, %580, %581, %582, %583, %584)
bb84(%585: ptr, %586: u32, %587: u64, %588: u64, %589: u64, %590: u64, %591: u64, %592: u64, %593: u64, %594: u64):
    call @func.70(%1070, %1068, %586)
    br bb85(%585, %586, %587, %588, %589, %590, %591, %592, %593, %594)
bb85(%595: ptr, %596: u32, %597: u64, %598: u64, %599: u64, %600: u64, %601: u64, %602: u64, %603: u64, %604: u64):
    %1777 = const u64 0
    br bb86(%595, %596, %597, %598, %599, %600, %601, %602, %603, %604, %1777)
bb86(%605: ptr, %606: u32, %607: u64, %608: u64, %609: u64, %610: u64, %611: u64, %612: u64, %613: u64, %614: u64, %615: u64):
    %1778 = call @func.95(%1070)
    br bb87(%605, %606, %607, %608, %609, %610, %611, %612, %613, %614, %615, %615, %1778)
bb87(%616: ptr, %617: u32, %618: u64, %619: u64, %620: u64, %621: u64, %622: u64, %623: u64, %624: u64, %625: u64, %626: u64, %627: u64, %628: u64):
    %1779 = icmp ult u64 %627, %628
    condbr %1779, bb88(%616, %617, %618, %619, %620, %621, %622, %623, %624, %625, %626), bb93(%616, %617, %618, %619, %620, %621, %622, %623, %624, %625)
bb88(%629: ptr, %630: u32, %631: u64, %632: u64, %633: u64, %634: u64, %635: u64, %636: u64, %637: u64, %638: u64, %639: u64):
    %1780 = call @func.96(%1070, %639)
    br bb89(%629, %630, %631, %632, %633, %634, %635, %636, %637, %638, %639, %1780)
bb89(%640: ptr, %641: u32, %642: u64, %643: u64, %644: u64, %645: u64, %646: u64, %647: u64, %648: u64, %649: u64, %650: u64, %651: ptr):
    %1781 = load u64, ptr %1014
    call @func.133(%1071, %651, %646, %1781, %647, %648)
    br bb90(%640, %641, %642, %643, %644, %645, %646, %647, %648, %649, %650)
bb90(%652: ptr, %653: u32, %654: u64, %655: u64, %656: u64, %657: u64, %658: u64, %659: u64, %660: u64, %661: u64, %662: u64):
    %1782 = const bool false
    %1783 = load i64, ptr %1067
    store i64 %1783, ptr %1073
    %1784 = const i64 8
    %1785 = gep i8, ptr %1067, %1784
    %1786 = const i64 8
    %1787 = gep i8, ptr %1073, %1786
    %1788 = load i64, ptr %1785
    store i64 %1788, ptr %1787
    %1789 = const i64 16
    %1790 = gep i8, ptr %1067, %1789
    %1791 = const i64 16
    %1792 = gep i8, ptr %1073, %1791
    %1793 = load i64, ptr %1790
    store i64 %1793, ptr %1792
    %1794 = const i64 24
    %1795 = gep i8, ptr %1067, %1794
    %1796 = const i64 24
    %1797 = gep i8, ptr %1073, %1796
    %1798 = load i64, ptr %1795
    store i64 %1798, ptr %1797
    %1799 = const i64 32
    %1800 = gep i8, ptr %1067, %1799
    %1801 = const i64 32
    %1802 = gep i8, ptr %1073, %1801
    %1803 = load i64, ptr %1800
    store i64 %1803, ptr %1802
    call @func.84(%1072, %1073, %1071)
    br bb91(%652, %653, %654, %655, %656, %657, %658, %659, %660, %661, %662)
bb91(%663: ptr, %664: u32, %665: u64, %666: u64, %667: u64, %668: u64, %669: u64, %670: u64, %671: u64, %672: u64, %673: u64):
    %1804 = const bool true
    %1805 = load i64, ptr %1072
    store i64 %1805, ptr %1067
    %1806 = const i64 8
    %1807 = gep i8, ptr %1072, %1806
    %1808 = const i64 8
    %1809 = gep i8, ptr %1067, %1808
    %1810 = load i64, ptr %1807
    store i64 %1810, ptr %1809
    %1811 = const i64 16
    %1812 = gep i8, ptr %1072, %1811
    %1813 = const i64 16
    %1814 = gep i8, ptr %1067, %1813
    %1815 = load i64, ptr %1812
    store i64 %1815, ptr %1814
    %1816 = const i64 24
    %1817 = gep i8, ptr %1072, %1816
    %1818 = const i64 24
    %1819 = gep i8, ptr %1067, %1818
    %1820 = load i64, ptr %1817
    store i64 %1820, ptr %1819
    %1821 = const i64 32
    %1822 = gep i8, ptr %1072, %1821
    %1823 = const i64 32
    %1824 = gep i8, ptr %1067, %1823
    %1825 = load i64, ptr %1822
    store i64 %1825, ptr %1824
    %1826 = const u64 1
    %1827, %1828 = add.overflow u64 %673, %1826
    store u64 %1827, ptr %1074
    %1829 = const i64 8
    %1830 = gep i8, ptr %1074, %1829
    store bool %1828, ptr %1830
    %1831 = const i64 8
    %1832 = gep i8, ptr %1074, %1831
    %1833 = load bool, ptr %1832
    %1834 = const bool false
    %1835 = icmp eq bool %1833, %1834
    condbr %1835, bb92(%663, %664, %665, %666, %667, %668, %669, %670, %671, %672), bb143
bb92(%674: ptr, %675: u32, %676: u64, %677: u64, %678: u64, %679: u64, %680: u64, %681: u64, %682: u64, %683: u64):
    %1836 = load u64, ptr %1074
    br bb86(%674, %675, %676, %677, %678, %679, %680, %681, %682, %683, %1836)
bb93(%684: ptr, %685: u32, %686: u64, %687: u64, %688: u64, %689: u64, %690: u64, %691: u64, %692: u64, %693: u64):
    %1837 = call @func.103(%693)
    br bb94(%684, %685, %686, %687, %688, %689, %690, %691, %692, %1837)
bb94(%694: ptr, %695: u32, %696: u64, %697: u64, %698: u64, %699: u64, %700: u64, %701: u64, %702: u64, %703: u32):
    call @func.83(%1075, %703)
    br bb95(%694, %695, %696, %697, %698, %699, %700, %701, %702)
bb95(%704: ptr, %705: u32, %706: u64, %707: u64, %708: u64, %709: u64, %710: u64, %711: u64, %712: u64):
    %1838 = const bool true
    br bb96(%704, %705, %706, %707, %708, %709, %710, %711, %712)
bb96(%713: ptr, %714: u32, %715: u64, %716: u64, %717: u64, %718: u64, %719: u64, %720: u64, %721: u64):
    %1839 = const u64 0
    %1840 = icmp ugt u64 %721, %1839
    condbr %1840, bb97(%713, %714, %715, %716, %717, %718, %719, %720, %721), bb102(%713, %714, %715, %716, %717, %718, %719, %720)
bb97(%722: ptr, %723: u32, %724: u64, %725: u64, %726: u64, %727: u64, %728: u64, %729: u64, %730: u64):
    %1841 = const u64 1
    %1842, %1843 = sub.overflow u64 %730, %1841
    store u64 %1842, ptr %1076
    %1844 = const i64 8
    %1845 = gep i8, ptr %1076, %1844
    store bool %1843, ptr %1845
    %1846 = const i64 8
    %1847 = gep i8, ptr %1076, %1846
    %1848 = load bool, ptr %1847
    %1849 = const bool false
    %1850 = icmp eq bool %1848, %1849
    condbr %1850, bb98(%722, %723, %724, %725, %726, %727, %728, %729), bb143
bb98(%731: ptr, %732: u32, %733: u64, %734: u64, %735: u64, %736: u64, %737: u64, %738: u64):
    %1851 = load u64, ptr %1076
    %1852 = const bool false
    %1853 = const bool true
    %1854 = load i64, ptr %1075
    store i64 %1854, ptr %1078
    %1855 = const i64 8
    %1856 = gep i8, ptr %1075, %1855
    %1857 = const i64 8
    %1858 = gep i8, ptr %1078, %1857
    %1859 = load i64, ptr %1856
    store i64 %1859, ptr %1858
    %1860 = const i64 16
    %1861 = gep i8, ptr %1075, %1860
    %1862 = const i64 16
    %1863 = gep i8, ptr %1078, %1862
    %1864 = load i64, ptr %1861
    store i64 %1864, ptr %1863
    %1865 = const i64 24
    %1866 = gep i8, ptr %1075, %1865
    %1867 = const i64 24
    %1868 = gep i8, ptr %1078, %1867
    %1869 = load i64, ptr %1866
    store i64 %1869, ptr %1868
    %1870 = const i64 32
    %1871 = gep i8, ptr %1075, %1870
    %1872 = const i64 32
    %1873 = gep i8, ptr %1078, %1872
    %1874 = load i64, ptr %1871
    store i64 %1874, ptr %1873
    %1875 = call @func.103(%1851)
    br bb99(%731, %732, %733, %734, %735, %736, %737, %738, %1851, %1875)
bb99(%739: ptr, %740: u32, %741: u64, %742: u64, %743: u64, %744: u64, %745: u64, %746: u64, %747: u64, %748: u32):
    call @func.83(%1079, %748)
    br bb100(%739, %740, %741, %742, %743, %744, %745, %746, %747)
bb100(%749: ptr, %750: u32, %751: u64, %752: u64, %753: u64, %754: u64, %755: u64, %756: u64, %757: u64):
    %1876 = const bool false
    call @func.84(%1077, %1078, %1079)
    br bb101(%749, %750, %751, %752, %753, %754, %755, %756, %757)
bb101(%758: ptr, %759: u32, %760: u64, %761: u64, %762: u64, %763: u64, %764: u64, %765: u64, %766: u64):
    %1877 = const bool false
    %1878 = const bool true
    %1879 = load i64, ptr %1077
    store i64 %1879, ptr %1075
    %1880 = const i64 8
    %1881 = gep i8, ptr %1077, %1880
    %1882 = const i64 8
    %1883 = gep i8, ptr %1075, %1882
    %1884 = load i64, ptr %1881
    store i64 %1884, ptr %1883
    %1885 = const i64 16
    %1886 = gep i8, ptr %1077, %1885
    %1887 = const i64 16
    %1888 = gep i8, ptr %1075, %1887
    %1889 = load i64, ptr %1886
    store i64 %1889, ptr %1888
    %1890 = const i64 24
    %1891 = gep i8, ptr %1077, %1890
    %1892 = const i64 24
    %1893 = gep i8, ptr %1075, %1892
    %1894 = load i64, ptr %1891
    store i64 %1894, ptr %1893
    %1895 = const i64 32
    %1896 = gep i8, ptr %1077, %1895
    %1897 = const i64 32
    %1898 = gep i8, ptr %1075, %1897
    %1899 = load i64, ptr %1896
    store i64 %1899, ptr %1898
    br bb96(%758, %759, %760, %761, %762, %763, %764, %765, %766)
bb102(%767: ptr, %768: u32, %769: u64, %770: u64, %771: u64, %772: u64, %773: u64, %774: u64):
    %1900 = const bool false
    %1901 = load i64, ptr %1067
    store i64 %1901, ptr %1081
    %1902 = const i64 8
    %1903 = gep i8, ptr %1067, %1902
    %1904 = const i64 8
    %1905 = gep i8, ptr %1081, %1904
    %1906 = load i64, ptr %1903
    store i64 %1906, ptr %1905
    %1907 = const i64 16
    %1908 = gep i8, ptr %1067, %1907
    %1909 = const i64 16
    %1910 = gep i8, ptr %1081, %1909
    %1911 = load i64, ptr %1908
    store i64 %1911, ptr %1910
    %1912 = const i64 24
    %1913 = gep i8, ptr %1067, %1912
    %1914 = const i64 24
    %1915 = gep i8, ptr %1081, %1914
    %1916 = load i64, ptr %1913
    store i64 %1916, ptr %1915
    %1917 = const i64 32
    %1918 = gep i8, ptr %1067, %1917
    %1919 = const i64 32
    %1920 = gep i8, ptr %1081, %1919
    %1921 = load i64, ptr %1918
    store i64 %1921, ptr %1920
    %1922 = const bool false
    %1923 = load i64, ptr %1075
    store i64 %1923, ptr %1082
    %1924 = const i64 8
    %1925 = gep i8, ptr %1075, %1924
    %1926 = const i64 8
    %1927 = gep i8, ptr %1082, %1926
    %1928 = load i64, ptr %1925
    store i64 %1928, ptr %1927
    %1929 = const i64 16
    %1930 = gep i8, ptr %1075, %1929
    %1931 = const i64 16
    %1932 = gep i8, ptr %1082, %1931
    %1933 = load i64, ptr %1930
    store i64 %1933, ptr %1932
    %1934 = const i64 24
    %1935 = gep i8, ptr %1075, %1934
    %1936 = const i64 24
    %1937 = gep i8, ptr %1082, %1936
    %1938 = load i64, ptr %1935
    store i64 %1938, ptr %1937
    %1939 = const i64 32
    %1940 = gep i8, ptr %1075, %1939
    %1941 = const i64 32
    %1942 = gep i8, ptr %1082, %1941
    %1943 = load i64, ptr %1940
    store i64 %1943, ptr %1942
    call @func.84(%1080, %1081, %1082)
    br bb103(%767, %768, %769, %770, %771, %772, %773, %774)
bb103(%775: ptr, %776: u32, %777: u64, %778: u64, %779: u64, %780: u64, %781: u64, %782: u64):
    %1944 = const bool true
    %1945 = load i64, ptr %1080
    store i64 %1945, ptr %1067
    %1946 = const i64 8
    %1947 = gep i8, ptr %1080, %1946
    %1948 = const i64 8
    %1949 = gep i8, ptr %1067, %1948
    %1950 = load i64, ptr %1947
    store i64 %1950, ptr %1949
    %1951 = const i64 16
    %1952 = gep i8, ptr %1080, %1951
    %1953 = const i64 16
    %1954 = gep i8, ptr %1067, %1953
    %1955 = load i64, ptr %1952
    store i64 %1955, ptr %1954
    %1956 = const i64 24
    %1957 = gep i8, ptr %1080, %1956
    %1958 = const i64 24
    %1959 = gep i8, ptr %1067, %1958
    %1960 = load i64, ptr %1957
    store i64 %1960, ptr %1959
    %1961 = const i64 32
    %1962 = gep i8, ptr %1080, %1961
    %1963 = const i64 32
    %1964 = gep i8, ptr %1067, %1963
    %1965 = load i64, ptr %1962
    store i64 %1965, ptr %1964
    call @func.94(%1084, %5, %781)
    br bb104(%775, %776, %777, %778, %779, %780, %781, %782)
bb104(%783: ptr, %784: u32, %785: u64, %786: u64, %787: u64, %788: u64, %789: u64, %790: u64):
    %1966 = load i64, ptr %1084
    %1967 = const i64 0
    %1968 = icmp eq i64 %1966, %1967
    %1969 = const i64 0
    %1970 = const i64 1
    %1971 = select i64 %1968, %1969, %1970
    switch %1971 [ 0: bb105(%783, %784, %785, %786, %787, %788, %789, %790) 1: bb106(%783, %784, %785, %786, %787, %788, %789, %790) default: bb65 ]
bb105(%791: ptr, %792: u32, %793: u64, %794: u64, %795: u64, %796: u64, %797: u64, %798: u64):
    call @func.97(%1083)
    br bb138(%791, %792, %793, %794, %795, %796, %797, %798)
bb106(%799: ptr, %800: u32, %801: u64, %802: u64, %803: u64, %804: u64, %805: u64, %806: u64):
    %1972 = load ptr, ptr %1084
    call @func.116(%1083, %1972)
    br bb139(%799, %800, %801, %802, %803, %804, %805, %806)
bb107(%807: ptr, %808: u32, %809: u64, %810: u64, %811: u64, %812: u64, %813: u64, %814: u64):
    %1973 = call @func.98(%1083)
    br bb140(%807, %808, %809, %810, %811, %812, %813, %814, %1973)
bb108(%815: ptr, %816: u32, %817: u64, %818: u64, %819: u64, %820: u64, %821: u64, %822: u64, %823: u64):
    %1974 = const u64 0
    %1975 = icmp ugt u64 %823, %1974
    condbr %1975, bb109(%815, %816, %817, %818, %819, %820, %821, %822, %823), bb114(%815, %816, %817, %818, %819, %820)
bb109(%824: ptr, %825: u32, %826: u64, %827: u64, %828: u64, %829: u64, %830: u64, %831: u64, %832: u64):
    %1976 = const u64 1
    %1977, %1978 = sub.overflow u64 %832, %1976
    store u64 %1977, ptr %1085
    %1979 = const i64 8
    %1980 = gep i8, ptr %1085, %1979
    store bool %1978, ptr %1980
    %1981 = const i64 8
    %1982 = gep i8, ptr %1085, %1981
    %1983 = load bool, ptr %1982
    %1984 = const bool false
    %1985 = icmp eq bool %1983, %1984
    condbr %1985, bb110(%824, %825, %826, %827, %828, %829, %830, %831), bb143
bb110(%833: ptr, %834: u32, %835: u64, %836: u64, %837: u64, %838: u64, %839: u64, %840: u64):
    %1986 = load u64, ptr %1085
    %1987 = call @func.99(%1083, %1986)
    store ptr %1987, ptr %1086
    br bb111(%833, %834, %835, %836, %837, %838, %839, %840, %1986, %1986)
bb111(%841: ptr, %842: u32, %843: u64, %844: u64, %845: u64, %846: u64, %847: u64, %848: u64, %849: u64, %850: u64):
    %1988 = load ptr, ptr %1086
    %1989 = load ptr, ptr %1086
    %1990 = const i64 8
    %1991 = gep i8, ptr %1989, %1990
    %1992 = load u64, ptr %1014
    call @func.133(%1087, %1991, %847, %1992, %848, %850)
    br bb112(%841, %842, %843, %844, %845, %846, %847, %848, %849, %1988)
bb112(%851: ptr, %852: u32, %853: u64, %854: u64, %855: u64, %856: u64, %857: u64, %858: u64, %859: u64, %860: ptr):
    %1993 = load i8, ptr %860
    store i8 %1993, ptr %1089
    %1994 = const i64 1
    %1995 = gep i8, ptr %860, %1994
    %1996 = const i64 1
    %1997 = gep i8, ptr %1089, %1996
    %1998 = load i8, ptr %1995
    store i8 %1998, ptr %1997
    %1999 = const bool false
    %2000 = load i64, ptr %1067
    store i64 %2000, ptr %1090
    %2001 = const i64 8
    %2002 = gep i8, ptr %1067, %2001
    %2003 = const i64 8
    %2004 = gep i8, ptr %1090, %2003
    %2005 = load i64, ptr %2002
    store i64 %2005, ptr %2004
    %2006 = const i64 16
    %2007 = gep i8, ptr %1067, %2006
    %2008 = const i64 16
    %2009 = gep i8, ptr %1090, %2008
    %2010 = load i64, ptr %2007
    store i64 %2010, ptr %2009
    %2011 = const i64 24
    %2012 = gep i8, ptr %1067, %2011
    %2013 = const i64 24
    %2014 = gep i8, ptr %1090, %2013
    %2015 = load i64, ptr %2012
    store i64 %2015, ptr %2014
    %2016 = const i64 32
    %2017 = gep i8, ptr %1067, %2016
    %2018 = const i64 32
    %2019 = gep i8, ptr %1090, %2018
    %2020 = load i64, ptr %2017
    store i64 %2020, ptr %2019
    call @func.86(%1088, %1089, %1087, %1090)
    br bb113(%851, %852, %853, %854, %855, %856, %857, %858, %859)
bb113(%861: ptr, %862: u32, %863: u64, %864: u64, %865: u64, %866: u64, %867: u64, %868: u64, %869: u64):
    %2021 = const bool true
    %2022 = load i64, ptr %1088
    store i64 %2022, ptr %1067
    %2023 = const i64 8
    %2024 = gep i8, ptr %1088, %2023
    %2025 = const i64 8
    %2026 = gep i8, ptr %1067, %2025
    %2027 = load i64, ptr %2024
    store i64 %2027, ptr %2026
    %2028 = const i64 16
    %2029 = gep i8, ptr %1088, %2028
    %2030 = const i64 16
    %2031 = gep i8, ptr %1067, %2030
    %2032 = load i64, ptr %2029
    store i64 %2032, ptr %2031
    %2033 = const i64 24
    %2034 = gep i8, ptr %1088, %2033
    %2035 = const i64 24
    %2036 = gep i8, ptr %1067, %2035
    %2037 = load i64, ptr %2034
    store i64 %2037, ptr %2036
    %2038 = const i64 32
    %2039 = gep i8, ptr %1088, %2038
    %2040 = const i64 32
    %2041 = gep i8, ptr %1067, %2040
    %2042 = load i64, ptr %2039
    store i64 %2042, ptr %2041
    br bb108(%861, %862, %863, %864, %865, %866, %867, %868, %869)
bb114(%870: ptr, %871: u32, %872: u64, %873: u64, %874: u64, %875: u64):
    call @func.85(%1092)
    br bb115(%870, %871, %872, %873, %874, %875)
bb115(%876: ptr, %877: u32, %878: u64, %879: u64, %880: u64, %881: u64):
    %2043 = const bool false
    %2044 = load i64, ptr %1067
    store i64 %2044, ptr %1093
    %2045 = const i64 8
    %2046 = gep i8, ptr %1067, %2045
    %2047 = const i64 8
    %2048 = gep i8, ptr %1093, %2047
    %2049 = load i64, ptr %2046
    store i64 %2049, ptr %2048
    %2050 = const i64 16
    %2051 = gep i8, ptr %1067, %2050
    %2052 = const i64 16
    %2053 = gep i8, ptr %1093, %2052
    %2054 = load i64, ptr %2051
    store i64 %2054, ptr %2053
    %2055 = const i64 24
    %2056 = gep i8, ptr %1067, %2055
    %2057 = const i64 24
    %2058 = gep i8, ptr %1093, %2057
    %2059 = load i64, ptr %2056
    store i64 %2059, ptr %2058
    %2060 = const i64 32
    %2061 = gep i8, ptr %1067, %2060
    %2062 = const i64 32
    %2063 = gep i8, ptr %1093, %2062
    %2064 = load i64, ptr %2061
    store i64 %2064, ptr %2063
    %2065 = const bool false
    %2066 = load i64, ptr %1043
    store i64 %2066, ptr %1094
    %2067 = const i64 8
    %2068 = gep i8, ptr %1043, %2067
    %2069 = const i64 8
    %2070 = gep i8, ptr %1094, %2069
    %2071 = load i64, ptr %2068
    store i64 %2071, ptr %2070
    %2072 = const i64 16
    %2073 = gep i8, ptr %1043, %2072
    %2074 = const i64 16
    %2075 = gep i8, ptr %1094, %2074
    %2076 = load i64, ptr %2073
    store i64 %2076, ptr %2075
    %2077 = const i64 24
    %2078 = gep i8, ptr %1043, %2077
    %2079 = const i64 24
    %2080 = gep i8, ptr %1094, %2079
    %2081 = load i64, ptr %2078
    store i64 %2081, ptr %2080
    %2082 = const i64 32
    %2083 = gep i8, ptr %1043, %2082
    %2084 = const i64 32
    %2085 = gep i8, ptr %1094, %2084
    %2086 = load i64, ptr %2083
    store i64 %2086, ptr %2085
    call @func.86(%1091, %1092, %1093, %1094)
    br bb116(%876, %877, %878, %879, %880, %881)
bb116(%882: ptr, %883: u32, %884: u64, %885: u64, %886: u64, %887: u64):
    %2087 = const bool true
    %2088 = load i64, ptr %1091
    store i64 %2088, ptr %1043
    %2089 = const i64 8
    %2090 = gep i8, ptr %1091, %2089
    %2091 = const i64 8
    %2092 = gep i8, ptr %1043, %2091
    %2093 = load i64, ptr %2090
    store i64 %2093, ptr %2092
    %2094 = const i64 16
    %2095 = gep i8, ptr %1091, %2094
    %2096 = const i64 16
    %2097 = gep i8, ptr %1043, %2096
    %2098 = load i64, ptr %2095
    store i64 %2098, ptr %2097
    %2099 = const i64 24
    %2100 = gep i8, ptr %1091, %2099
    %2101 = const i64 24
    %2102 = gep i8, ptr %1043, %2101
    %2103 = load i64, ptr %2100
    store i64 %2103, ptr %2102
    %2104 = const i64 32
    %2105 = gep i8, ptr %1091, %2104
    %2106 = const i64 32
    %2107 = gep i8, ptr %1043, %2106
    %2108 = load i64, ptr %2105
    store i64 %2108, ptr %2107
    %2109 = const u64 1
    %2110, %2111 = add.overflow u64 %886, %2109
    store u64 %2110, ptr %1095
    %2112 = const i64 8
    %2113 = gep i8, ptr %1095, %2112
    store bool %2111, ptr %2113
    %2114 = const i64 8
    %2115 = gep i8, ptr %1095, %2114
    %2116 = load bool, ptr %2115
    %2117 = const bool false
    %2118 = icmp eq bool %2116, %2117
    condbr %2118, bb117(%882, %883, %884, %885, %887), bb143
bb117(%888: ptr, %889: u32, %890: u64, %891: u64, %892: u64):
    %2119 = load u64, ptr %1095
    br bb118(%888, %889, %890, %891, %2119, %892)
bb118(%893: ptr, %894: u32, %895: u64, %896: u64, %897: u64, %898: u64):
    %2120 = const bool false
    br bb119(%893, %894, %895, %896, %897, %898)
bb119(%899: ptr, %900: u32, %901: u64, %902: u64, %903: u64, %904: u64):
    br bb120(%899, %900, %901, %902, %903, %904)
bb120(%905: ptr, %906: u32, %907: u64, %908: u64, %909: u64, %910: u64):
    %2121 = const bool false
    br bb54(%905, %906, %907, %908, %909, %910)
bb121(%911: ptr):
    %2122 = load u64, ptr %1014
    br bb122(%911, %2122)
bb122(%912: ptr, %913: u64):
    %2123 = const u64 0
    %2124 = icmp ugt u64 %913, %2123
    condbr %2124, bb123(%912, %913), bb133
bb123(%914: ptr, %915: u64):
    %2125 = const u64 1
    %2126, %2127 = sub.overflow u64 %915, %2125
    store u64 %2126, ptr %1096
    %2128 = const i64 8
    %2129 = gep i8, ptr %1096, %2128
    store bool %2127, ptr %2129
    %2130 = const i64 8
    %2131 = gep i8, ptr %1096, %2130
    %2132 = load bool, ptr %2131
    %2133 = const bool false
    %2134 = icmp eq bool %2132, %2133
    condbr %2134, bb124(%914), bb143
bb124(%916: ptr):
    %2135 = load u64, ptr %1096
    call @func.94(%1098, %5, %2135)
    br bb125(%916, %2135, %2135)
bb125(%917: ptr, %918: u64, %919: u64):
    %2136 = load i64, ptr %1098
    %2137 = const i64 0
    %2138 = icmp eq i64 %2136, %2137
    %2139 = const i64 0
    %2140 = const i64 1
    %2141 = select i64 %2138, %2139, %2140
    switch %2141 [ 0: bb126(%917, %918, %919) 1: bb127(%917, %918, %919) default: bb65 ]
bb126(%920: ptr, %921: u64, %922: u64):
    call @func.74(%1097, %920, %7)
    br bb141(%920, %921, %922)
bb127(%923: ptr, %924: u64, %925: u64):
    %2142 = load ptr, ptr %1098
    call @func.78(%1097, %2142)
    br bb142(%923, %924, %925)
bb128(%926: ptr, %927: u64, %928: u64):
    %2143 = call @func.103(%928)
    br bb129(%926, %927, %1097, %2143)
bb129(%929: ptr, %930: u64, %931: ptr, %932: u32):
    %2144 = load u64, ptr %1011
    %2145 = trunc u64 %2144 to u32
    call @func.105(%1099, %931, %932, %2145)
    br bb130(%929, %930)
bb130(%933: ptr, %934: u64):
    %2146 = const bool true
    call @func.85(%1101)
    br bb131(%933, %934)
bb131(%935: ptr, %936: u64):
    %2147 = const bool false
    %2148 = load i64, ptr %1099
    store i64 %2148, ptr %1102
    %2149 = const i64 8
    %2150 = gep i8, ptr %1099, %2149
    %2151 = const i64 8
    %2152 = gep i8, ptr %1102, %2151
    %2153 = load i64, ptr %2150
    store i64 %2153, ptr %2152
    %2154 = const i64 16
    %2155 = gep i8, ptr %1099, %2154
    %2156 = const i64 16
    %2157 = gep i8, ptr %1102, %2156
    %2158 = load i64, ptr %2155
    store i64 %2158, ptr %2157
    %2159 = const i64 24
    %2160 = gep i8, ptr %1099, %2159
    %2161 = const i64 24
    %2162 = gep i8, ptr %1102, %2161
    %2163 = load i64, ptr %2160
    store i64 %2163, ptr %2162
    %2164 = const i64 32
    %2165 = gep i8, ptr %1099, %2164
    %2166 = const i64 32
    %2167 = gep i8, ptr %1102, %2166
    %2168 = load i64, ptr %2165
    store i64 %2168, ptr %2167
    %2169 = const bool false
    %2170 = load i64, ptr %1043
    store i64 %2170, ptr %1103
    %2171 = const i64 8
    %2172 = gep i8, ptr %1043, %2171
    %2173 = const i64 8
    %2174 = gep i8, ptr %1103, %2173
    %2175 = load i64, ptr %2172
    store i64 %2175, ptr %2174
    %2176 = const i64 16
    %2177 = gep i8, ptr %1043, %2176
    %2178 = const i64 16
    %2179 = gep i8, ptr %1103, %2178
    %2180 = load i64, ptr %2177
    store i64 %2180, ptr %2179
    %2181 = const i64 24
    %2182 = gep i8, ptr %1043, %2181
    %2183 = const i64 24
    %2184 = gep i8, ptr %1103, %2183
    %2185 = load i64, ptr %2182
    store i64 %2185, ptr %2184
    %2186 = const i64 32
    %2187 = gep i8, ptr %1043, %2186
    %2188 = const i64 32
    %2189 = gep i8, ptr %1103, %2188
    %2190 = load i64, ptr %2187
    store i64 %2190, ptr %2189
    call @func.86(%1100, %1101, %1102, %1103)
    br bb132(%935, %936)
bb132(%937: ptr, %938: u64):
    %2191 = const bool true
    %2192 = load i64, ptr %1100
    store i64 %2192, ptr %1043
    %2193 = const i64 8
    %2194 = gep i8, ptr %1100, %2193
    %2195 = const i64 8
    %2196 = gep i8, ptr %1043, %2195
    %2197 = load i64, ptr %2194
    store i64 %2197, ptr %2196
    %2198 = const i64 16
    %2199 = gep i8, ptr %1100, %2198
    %2200 = const i64 16
    %2201 = gep i8, ptr %1043, %2200
    %2202 = load i64, ptr %2199
    store i64 %2202, ptr %2201
    %2203 = const i64 24
    %2204 = gep i8, ptr %1100, %2203
    %2205 = const i64 24
    %2206 = gep i8, ptr %1043, %2205
    %2207 = load i64, ptr %2204
    store i64 %2207, ptr %2206
    %2208 = const i64 32
    %2209 = gep i8, ptr %1100, %2208
    %2210 = const i64 32
    %2211 = gep i8, ptr %1043, %2210
    %2212 = load i64, ptr %2209
    store i64 %2212, ptr %2211
    %2213 = const bool false
    br bb122(%937, %938)
bb133:
    %2214 = const bool false
    %2215 = load i64, ptr %1043
    store i64 %2215, ptr %0
    %2216 = const i64 8
    %2217 = gep i8, ptr %1043, %2216
    %2218 = const i64 8
    %2219 = gep i8, ptr %0, %2218
    %2220 = load i64, ptr %2217
    store i64 %2220, ptr %2219
    %2221 = const i64 16
    %2222 = gep i8, ptr %1043, %2221
    %2223 = const i64 16
    %2224 = gep i8, ptr %0, %2223
    %2225 = load i64, ptr %2222
    store i64 %2225, ptr %2224
    %2226 = const i64 24
    %2227 = gep i8, ptr %1043, %2226
    %2228 = const i64 24
    %2229 = gep i8, ptr %0, %2228
    %2230 = load i64, ptr %2227
    store i64 %2230, ptr %2229
    %2231 = const i64 32
    %2232 = gep i8, ptr %1043, %2231
    %2233 = const i64 32
    %2234 = gep i8, ptr %0, %2233
    %2235 = load i64, ptr %2232
    store i64 %2235, ptr %2234
    %2236 = const bool false
    %2237 = const bool false
    %2238 = const bool false
    ret
bb134(%939: ptr, %940: u32, %941: u64, %942: u64, %943: u64, %944: u64, %945: u64, %946: u64, %947: u64, %948: u64):
    br bb68(%939, %940, %941, %942, %943, %944, %945, %946, %947, %948)
bb135(%949: ptr, %950: u32, %951: u64, %952: u64, %953: u64, %954: u64, %955: u64, %956: u64, %957: u64, %958: u64, %959: u64):
    br bb76(%949, %950, %951, %952, %953, %954, %955, %956, %957, %958, %959)
bb136(%960: ptr, %961: u32, %962: u64, %963: u64, %964: u64, %965: u64, %966: u64, %967: u64, %968: u64, %969: u64):
    br bb84(%960, %961, %962, %963, %964, %965, %966, %967, %968, %969)
bb137(%970: ptr, %971: u32, %972: u64, %973: u64, %974: u64, %975: u64, %976: u64, %977: u64, %978: u64, %979: u64):
    br bb84(%970, %971, %972, %973, %974, %975, %976, %977, %978, %979)
bb138(%980: ptr, %981: u32, %982: u64, %983: u64, %984: u64, %985: u64, %986: u64, %987: u64):
    br bb107(%980, %981, %982, %983, %984, %985, %986, %987)
bb139(%988: ptr, %989: u32, %990: u64, %991: u64, %992: u64, %993: u64, %994: u64, %995: u64):
    br bb107(%988, %989, %990, %991, %992, %993, %994, %995)
bb140(%996: ptr, %997: u32, %998: u64, %999: u64, %1000: u64, %1001: u64, %1002: u64, %1003: u64, %1004: u64):
    br bb108(%996, %997, %998, %999, %1000, %1001, %1002, %1003, %1004)
bb141(%1005: ptr, %1006: u64, %1007: u64):
    br bb128(%1005, %1006, %1007)
bb142(%1008: ptr, %1009: u64, %1010: u64):
    br bb128(%1008, %1009, %1010)
bb143:
    unreachable
}

fn @_RNvXs0_NtNtNtCs2EYQwhfuABO_4core7convert3num18ptr_try_from_implsmINtB9_7TryFromjE8try_fromCs6RT0DENTjyC_27clean_mutual_recursor_slice(functy.101) {
}

fn @_RNvMNtCs2EYQwhfuABO_4core6resultINtB2_6ResultmNtNtNtB4_3num5error15TryFromIntErrorE9unwrap_orCs6RT0DENTjyC_27clean_mutual_recursor_slice(functy.102) {
}

fn @usize_to_u32(functy.103) {
bb0(%0: u64):
    %2 = alloca (i32, i32), align 4
    call @func.101(%2, %0)
    br bb1
bb1:
    %3 = const u32 4294967295
    %4 = call @func.102(%2, %3)
    br bb2(%4)
bb2(%1: u32):
    ret %1
}

fn @build_recursor_type___closure_0_(functy.104) {
bb0(%0: ptr, %1: ptr, %2: u32, %3: u32):
    %63 = alloca (i64, i64, i64, i64, i64), align 8
    %64 = alloca (i32, i32), align 4
    %65 = alloca (i32, i32), align 4
    %66 = alloca (i32, i32), align 4
    %67 = alloca (i64, i64, i64, i64, i64), align 8
    %68 = alloca (i64, i64, i64, i64, i64), align 8
    %69 = alloca (i64, i64, i64, i64, i64), align 8
    %70 = alloca (i32, i32), align 4
    %71 = alloca (i32, i32), align 4
    %72 = alloca (i32, i32), align 4
    %73 = alloca (i32, i32), align 4
    %74 = alloca (i64, i64, i64, i64, i64), align 8
    %75 = alloca (i64, i64, i64, i64, i64), align 8
    %76 = alloca (i64, i64, i64, i64, i64), align 8
    %77 = alloca (i32, i32), align 4
    %78 = const bool false
    %79 = const bool false
    %80 = const bool false
    %81 = load ptr, ptr %1
    %82 = const bool true
    call @func.78(%63, %81)
    br bb1(%1, %2, %3)
bb1(%4: ptr, %5: u32, %6: u32):
    %83 = const u32 0
    br bb2(%4, %5, %6, %83)
bb2(%7: ptr, %8: u32, %9: u32, %10: u32):
    %84 = const i64 8
    %85 = gep i8, ptr %7, %84
    %86 = load ptr, ptr %85
    %87 = load u32, ptr %86
    %88 = icmp ult u32 %10, %87
    condbr %88, bb3(%7, %8, %9, %10), bb10(%7, %9)
bb3(%11: ptr, %12: u32, %13: u32, %14: u32):
    %89 = const i64 8
    %90 = gep i8, ptr %11, %89
    %91 = load ptr, ptr %90
    %92 = load u32, ptr %91
    %93 = const u32 1
    %94, %95 = sub.overflow u32 %92, %93
    store u32 %94, ptr %64
    %96 = const i64 4
    %97 = gep i8, ptr %64, %96
    store bool %95, ptr %97
    %98 = const i64 4
    %99 = gep i8, ptr %64, %98
    %100 = load bool, ptr %99
    %101 = const bool false
    %102 = icmp eq bool %100, %101
    condbr %102, bb4(%11, %12, %13, %14), bb20
bb4(%15: ptr, %16: u32, %17: u32, %18: u32):
    %103 = load u32, ptr %64
    %104, %105 = sub.overflow u32 %103, %18
    store u32 %104, ptr %65
    %106 = const i64 4
    %107 = gep i8, ptr %65, %106
    store bool %105, ptr %107
    %108 = const i64 4
    %109 = gep i8, ptr %65, %108
    %110 = load bool, ptr %109
    %111 = const bool false
    %112 = icmp eq bool %110, %111
    condbr %112, bb5(%15, %16, %17, %18), bb20
bb5(%19: ptr, %20: u32, %21: u32, %22: u32):
    %113 = load u32, ptr %65
    %114, %115 = add.overflow u32 %20, %113
    store u32 %114, ptr %66
    %116 = const i64 4
    %117 = gep i8, ptr %66, %116
    store bool %115, ptr %117
    %118 = const i64 4
    %119 = gep i8, ptr %66, %118
    %120 = load bool, ptr %119
    %121 = const bool false
    %122 = icmp eq bool %120, %121
    condbr %122, bb6(%19, %20, %21, %22), bb20
bb6(%23: ptr, %24: u32, %25: u32, %26: u32):
    %123 = load u32, ptr %66
    %124 = const bool false
    %125 = const bool true
    %126 = load i64, ptr %63
    store i64 %126, ptr %68
    %127 = const i64 8
    %128 = gep i8, ptr %63, %127
    %129 = const i64 8
    %130 = gep i8, ptr %68, %129
    %131 = load i64, ptr %128
    store i64 %131, ptr %130
    %132 = const i64 16
    %133 = gep i8, ptr %63, %132
    %134 = const i64 16
    %135 = gep i8, ptr %68, %134
    %136 = load i64, ptr %133
    store i64 %136, ptr %135
    %137 = const i64 24
    %138 = gep i8, ptr %63, %137
    %139 = const i64 24
    %140 = gep i8, ptr %68, %139
    %141 = load i64, ptr %138
    store i64 %141, ptr %140
    %142 = const i64 32
    %143 = gep i8, ptr %63, %142
    %144 = const i64 32
    %145 = gep i8, ptr %68, %144
    %146 = load i64, ptr %143
    store i64 %146, ptr %145
    call @func.83(%69, %123)
    br bb7(%23, %24, %25, %26)
bb7(%27: ptr, %28: u32, %29: u32, %30: u32):
    %147 = const bool false
    call @func.84(%67, %68, %69)
    br bb8(%27, %28, %29, %30)
bb8(%31: ptr, %32: u32, %33: u32, %34: u32):
    %148 = const bool false
    %149 = const bool true
    %150 = load i64, ptr %67
    store i64 %150, ptr %63
    %151 = const i64 8
    %152 = gep i8, ptr %67, %151
    %153 = const i64 8
    %154 = gep i8, ptr %63, %153
    %155 = load i64, ptr %152
    store i64 %155, ptr %154
    %156 = const i64 16
    %157 = gep i8, ptr %67, %156
    %158 = const i64 16
    %159 = gep i8, ptr %63, %158
    %160 = load i64, ptr %157
    store i64 %160, ptr %159
    %161 = const i64 24
    %162 = gep i8, ptr %67, %161
    %163 = const i64 24
    %164 = gep i8, ptr %63, %163
    %165 = load i64, ptr %162
    store i64 %165, ptr %164
    %166 = const i64 32
    %167 = gep i8, ptr %67, %166
    %168 = const i64 32
    %169 = gep i8, ptr %63, %168
    %170 = load i64, ptr %167
    store i64 %170, ptr %169
    %171 = const u32 1
    %172, %173 = add.overflow u32 %34, %171
    store u32 %172, ptr %70
    %174 = const i64 4
    %175 = gep i8, ptr %70, %174
    store bool %173, ptr %175
    %176 = const i64 4
    %177 = gep i8, ptr %70, %176
    %178 = load bool, ptr %177
    %179 = const bool false
    %180 = icmp eq bool %178, %179
    condbr %180, bb9(%31, %32, %33), bb20
bb9(%35: ptr, %36: u32, %37: u32):
    %181 = load u32, ptr %70
    br bb2(%35, %36, %37, %181)
bb10(%38: ptr, %39: u32):
    %182 = const u32 0
    br bb11(%38, %39, %182)
bb11(%40: ptr, %41: u32, %42: u32):
    %183 = const i64 16
    %184 = gep i8, ptr %40, %183
    %185 = load ptr, ptr %184
    %186 = load u32, ptr %185
    %187 = icmp ult u32 %42, %186
    condbr %187, bb12(%40, %41, %42), bb19
bb12(%43: ptr, %44: u32, %45: u32):
    %188 = const i64 16
    %189 = gep i8, ptr %43, %188
    %190 = load ptr, ptr %189
    %191 = load u32, ptr %190
    %192 = const u32 1
    %193, %194 = sub.overflow u32 %191, %192
    store u32 %193, ptr %71
    %195 = const i64 4
    %196 = gep i8, ptr %71, %195
    store bool %194, ptr %196
    %197 = const i64 4
    %198 = gep i8, ptr %71, %197
    %199 = load bool, ptr %198
    %200 = const bool false
    %201 = icmp eq bool %199, %200
    condbr %201, bb13(%43, %44, %45), bb20
bb13(%46: ptr, %47: u32, %48: u32):
    %202 = load u32, ptr %71
    %203, %204 = sub.overflow u32 %202, %48
    store u32 %203, ptr %72
    %205 = const i64 4
    %206 = gep i8, ptr %72, %205
    store bool %204, ptr %206
    %207 = const i64 4
    %208 = gep i8, ptr %72, %207
    %209 = load bool, ptr %208
    %210 = const bool false
    %211 = icmp eq bool %209, %210
    condbr %211, bb14(%46, %47, %48), bb20
bb14(%49: ptr, %50: u32, %51: u32):
    %212 = load u32, ptr %72
    %213, %214 = add.overflow u32 %50, %212
    store u32 %213, ptr %73
    %215 = const i64 4
    %216 = gep i8, ptr %73, %215
    store bool %214, ptr %216
    %217 = const i64 4
    %218 = gep i8, ptr %73, %217
    %219 = load bool, ptr %218
    %220 = const bool false
    %221 = icmp eq bool %219, %220
    condbr %221, bb15(%49, %50, %51), bb20
bb15(%52: ptr, %53: u32, %54: u32):
    %222 = load u32, ptr %73
    %223 = const bool false
    %224 = const bool true
    %225 = load i64, ptr %63
    store i64 %225, ptr %75
    %226 = const i64 8
    %227 = gep i8, ptr %63, %226
    %228 = const i64 8
    %229 = gep i8, ptr %75, %228
    %230 = load i64, ptr %227
    store i64 %230, ptr %229
    %231 = const i64 16
    %232 = gep i8, ptr %63, %231
    %233 = const i64 16
    %234 = gep i8, ptr %75, %233
    %235 = load i64, ptr %232
    store i64 %235, ptr %234
    %236 = const i64 24
    %237 = gep i8, ptr %63, %236
    %238 = const i64 24
    %239 = gep i8, ptr %75, %238
    %240 = load i64, ptr %237
    store i64 %240, ptr %239
    %241 = const i64 32
    %242 = gep i8, ptr %63, %241
    %243 = const i64 32
    %244 = gep i8, ptr %75, %243
    %245 = load i64, ptr %242
    store i64 %245, ptr %244
    call @func.83(%76, %222)
    br bb16(%52, %53, %54)
bb16(%55: ptr, %56: u32, %57: u32):
    %246 = const bool false
    call @func.84(%74, %75, %76)
    br bb17(%55, %56, %57)
bb17(%58: ptr, %59: u32, %60: u32):
    %247 = const bool false
    %248 = const bool true
    %249 = load i64, ptr %74
    store i64 %249, ptr %63
    %250 = const i64 8
    %251 = gep i8, ptr %74, %250
    %252 = const i64 8
    %253 = gep i8, ptr %63, %252
    %254 = load i64, ptr %251
    store i64 %254, ptr %253
    %255 = const i64 16
    %256 = gep i8, ptr %74, %255
    %257 = const i64 16
    %258 = gep i8, ptr %63, %257
    %259 = load i64, ptr %256
    store i64 %259, ptr %258
    %260 = const i64 24
    %261 = gep i8, ptr %74, %260
    %262 = const i64 24
    %263 = gep i8, ptr %63, %262
    %264 = load i64, ptr %261
    store i64 %264, ptr %263
    %265 = const i64 32
    %266 = gep i8, ptr %74, %265
    %267 = const i64 32
    %268 = gep i8, ptr %63, %267
    %269 = load i64, ptr %266
    store i64 %269, ptr %268
    %270 = const u32 1
    %271, %272 = add.overflow u32 %60, %270
    store u32 %271, ptr %77
    %273 = const i64 4
    %274 = gep i8, ptr %77, %273
    store bool %272, ptr %274
    %275 = const i64 4
    %276 = gep i8, ptr %77, %275
    %277 = load bool, ptr %276
    %278 = const bool false
    %279 = icmp eq bool %277, %278
    condbr %279, bb18(%58, %59), bb20
bb18(%61: ptr, %62: u32):
    %280 = load u32, ptr %77
    br bb11(%61, %62, %280)
bb19:
    %281 = const bool false
    %282 = load i64, ptr %63
    store i64 %282, ptr %0
    %283 = const i64 8
    %284 = gep i8, ptr %63, %283
    %285 = const i64 8
    %286 = gep i8, ptr %0, %285
    %287 = load i64, ptr %284
    store i64 %287, ptr %286
    %288 = const i64 16
    %289 = gep i8, ptr %63, %288
    %290 = const i64 16
    %291 = gep i8, ptr %0, %290
    %292 = load i64, ptr %289
    store i64 %292, ptr %291
    %293 = const i64 24
    %294 = gep i8, ptr %63, %293
    %295 = const i64 24
    %296 = gep i8, ptr %0, %295
    %297 = load i64, ptr %294
    store i64 %297, ptr %296
    %298 = const i64 32
    %299 = gep i8, ptr %63, %298
    %300 = const i64 32
    %301 = gep i8, ptr %0, %300
    %302 = load i64, ptr %299
    store i64 %302, ptr %301
    %303 = const bool false
    ret
bb20:
    unreachable
}

fn @Expr__lift_from(functy.105) {
bb0(%0: ptr, %1: ptr, %2: u32, %3: u32):
    call @func.134(%0, %1, %2, %3)
    br bb1
bb1:
    ret
}

fn @Expr__lift(functy.106) {
bb0(%0: ptr, %1: ptr, %2: u32):
    %3 = const u32 0
    call @func.134(%0, %1, %3, %2)
    br bb1
bb1:
    ret
}

fn @bi_implicit(functy.107) {
bb0(%0: ptr):
    %1 = const u8 1
    store u8 %1, ptr %0
    %2 = const u8 0
    %3 = const i64 1
    %4 = gep i8, ptr %0, %3
    store u8 %2, ptr %4
    ret
}

fn @Expr__infer_implicit(functy.108) {
bb0(%0: ptr, %1: ptr, %2: bool):
    %3 = const u32 4294967295
    call @func.135(%0, %1, %3, %2)
    br bb1
bb1:
    ret
}

fn @count_pi_binders(functy.109) {
bb0(%0: ptr):
    %7 = alloca i64, align 8
    %8 = alloca i64, align 8
    %9 = alloca (i64, i64), align 8
    %10 = const u64 0
    store ptr %0, ptr %7
    br bb1(%10)
bb1(%1: u64):
    %11 = load ptr, ptr %7
    store ptr %11, ptr %8
    %12 = load ptr, ptr %8
    %13 = load i8, ptr %12
    %14 = sext i8 %13 to i64
    switch %14 [ 6: bb2(%1) default: bb5(%1) ]
bb2(%2: u64):
    %15 = load ptr, ptr %8
    %16 = const i64 16
    %17 = gep i8, ptr %15, %16
    %18 = const u64 1
    %19, %20 = add.overflow u64 %2, %18
    store u64 %19, ptr %9
    %21 = const i64 8
    %22 = gep i8, ptr %9, %21
    store bool %20, ptr %22
    %23 = const i64 8
    %24 = gep i8, ptr %9, %23
    %25 = load bool, ptr %24
    %26 = const bool false
    %27 = icmp eq bool %25, %26
    condbr %27, bb3(%17), bb6
bb3(%3: ptr):
    %28 = load u64, ptr %9
    %29 = load ptr, ptr %3
    %30 = const i64 16
    %31 = gep i8, ptr %29, %30
    br bb4(%28, %31)
bb4(%4: u64, %5: ptr):
    store ptr %5, ptr %7
    br bb1(%4)
bb5(%6: u64):
    ret %6
bb6:
    unreachable
}

fn @get_return_type(functy.110) {
bb0(%0: ptr):
    %2 = alloca i64, align 8
    %3 = alloca i64, align 8
    store ptr %0, ptr %2
    br bb1
bb1:
    %4 = load ptr, ptr %2
    store ptr %4, ptr %3
    %5 = load ptr, ptr %3
    %6 = load i8, ptr %5
    %7 = sext i8 %6 to i64
    switch %7 [ 6: bb2 default: bb4 ]
bb2:
    %8 = load ptr, ptr %3
    %9 = const i64 16
    %10 = gep i8, ptr %8, %9
    %11 = load ptr, ptr %10
    %12 = const i64 16
    %13 = gep i8, ptr %11, %12
    br bb3(%13)
bb3(%1: ptr):
    store ptr %1, ptr %2
    br bb1
bb4:
    %14 = load ptr, ptr %2
    ret %14
}

fn @Expr__get_app_fn(functy.111) {
bb0(%0: ptr):
    %2 = alloca i64, align 8
    %3 = alloca i64, align 8
    store ptr %0, ptr %2
    br bb1
bb1:
    %4 = load ptr, ptr %2
    store ptr %4, ptr %3
    %5 = load ptr, ptr %3
    %6 = load i8, ptr %5
    %7 = sext i8 %6 to i64
    switch %7 [ 4: bb2 default: bb4 ]
bb2:
    %8 = load ptr, ptr %3
    %9 = const i64 8
    %10 = gep i8, ptr %8, %9
    %11 = load ptr, ptr %10
    %12 = const i64 16
    %13 = gep i8, ptr %11, %12
    br bb3(%13)
bb3(%1: ptr):
    store ptr %1, ptr %2
    br bb1
bb4:
    %14 = load ptr, ptr %2
    ret %14
}

fn @Expr__const_(functy.112) {
bb0(%0: ptr, %1: u32, %2: ptr):
    %3 = alloca i32, align 4
    %4 = alloca (i64, i64, i64, i64), align 8
    store u32 %1, ptr %3
    %5 = const i64 4
    %6 = gep i8, ptr %4, %5
    %7 = load i32, ptr %3
    store i32 %7, ptr %6
    %8 = const i64 8
    %9 = gep i8, ptr %4, %8
    %10 = load i64, ptr %2
    store i64 %10, ptr %9
    %11 = const i64 8
    %12 = gep i8, ptr %2, %11
    %13 = const i64 8
    %14 = gep i8, ptr %9, %13
    %15 = load i64, ptr %12
    store i64 %15, ptr %14
    %16 = const i64 16
    %17 = gep i8, ptr %2, %16
    %18 = const i64 16
    %19 = gep i8, ptr %9, %18
    %20 = load i64, ptr %17
    store i64 %20, ptr %19
    %21 = const i8 3
    store i8 %21, ptr %4
    call @func.82(%0, %4)
    br bb1
bb1:
    ret
}

fn @remap_residual_index_bvars(functy.113) {
bb0(%0: ptr, %1: ptr, %2: u64, %3: u64, %4: u64, %5: u64, %6: u64, %7: u64):
    %107 = alloca i64, align 8
    %108 = alloca i64, align 8
    %109 = alloca (i64, i64), align 8
    %110 = alloca (i64, i64), align 8
    %111 = alloca (i64, i64), align 8
    %112 = alloca (i64, i64), align 8
    %113 = alloca (i64, i64), align 8
    %114 = alloca (i64, i64), align 8
    %115 = alloca (i64, i64), align 8
    %116 = alloca (i64, i64), align 8
    %117 = alloca (i64, i64), align 8
    %118 = alloca (i64, i64), align 8
    %119 = alloca (i64, i64), align 8
    %120 = alloca (i64, i64), align 8
    %121 = alloca (i64, i64), align 8
    %122 = alloca (i64, i64), align 8
    %123 = alloca (i64, i64), align 8
    %124 = alloca (i64, i64, i64, i64, i64), align 8
    %125 = alloca (i64, i64, i64, i64, i64), align 8
    %126 = alloca (i64, i64, i64, i64, i64), align 8
    store ptr %1, ptr %107
    %127 = const bool false
    %128 = load ptr, ptr %107
    store ptr %128, ptr %108
    %129 = load ptr, ptr %108
    %130 = load i8, ptr %129
    %131 = sext i8 %130 to i64
    switch %131 [ 0: bb3(%2, %3, %4, %5, %6, %7) 4: bb2(%2, %3, %4, %5, %6, %7) default: bb1 ]
bb1:
    %132 = load ptr, ptr %107
    call @func.78(%0, %132)
    br bb30
bb2(%8: u64, %9: u64, %10: u64, %11: u64, %12: u64, %13: u64):
    %133 = load ptr, ptr %108
    %134 = const i64 8
    %135 = gep i8, ptr %133, %134
    %136 = load ptr, ptr %108
    %137 = const i64 16
    %138 = gep i8, ptr %136, %137
    %139 = load ptr, ptr %135
    %140 = const i64 16
    %141 = gep i8, ptr %139, %140
    br bb25(%8, %9, %10, %11, %12, %13, %138, %141)
bb3(%14: u64, %15: u64, %16: u64, %17: u64, %18: u64, %19: u64):
    %142 = load ptr, ptr %108
    %143 = const i64 4
    %144 = gep i8, ptr %142, %143
    %145 = load u32, ptr %144
    %146 = zext u32 %145 to u64
    %147 = icmp ult u64 %146, %19
    condbr %147, bb4(%146), bb5(%14, %15, %16, %17, %18, %19, %146)
bb4(%20: u64):
    br bb23(%20)
bb5(%21: u64, %22: u64, %23: u64, %24: u64, %25: u64, %26: u64, %27: u64):
    %148, %149 = sub.overflow u64 %27, %26
    store u64 %148, ptr %109
    %150 = const i64 8
    %151 = gep i8, ptr %109, %150
    store bool %149, ptr %151
    %152 = const i64 8
    %153 = gep i8, ptr %109, %152
    %154 = load bool, ptr %153
    %155 = const bool false
    %156 = icmp eq bool %154, %155
    condbr %156, bb6(%21, %22, %23, %24, %25, %26), bb31
bb6(%28: u64, %29: u64, %30: u64, %31: u64, %32: u64, %33: u64):
    %157 = load u64, ptr %109
    %158 = icmp ult u64 %157, %28
    condbr %158, bb7(%28, %30, %33, %157), bb13(%28, %29, %30, %31, %32, %33, %157)
bb7(%34: u64, %35: u64, %36: u64, %37: u64):
    %159 = const u64 1
    %160, %161 = sub.overflow u64 %34, %159
    store u64 %160, ptr %110
    %162 = const i64 8
    %163 = gep i8, ptr %110, %162
    store bool %161, ptr %163
    %164 = const i64 8
    %165 = gep i8, ptr %110, %164
    %166 = load bool, ptr %165
    %167 = const bool false
    %168 = icmp eq bool %166, %167
    condbr %168, bb8(%35, %36, %37), bb31
bb8(%38: u64, %39: u64, %40: u64):
    %169 = load u64, ptr %110
    %170, %171 = sub.overflow u64 %169, %40
    store u64 %170, ptr %111
    %172 = const i64 8
    %173 = gep i8, ptr %111, %172
    store bool %171, ptr %173
    %174 = const i64 8
    %175 = gep i8, ptr %111, %174
    %176 = load bool, ptr %175
    %177 = const bool false
    %178 = icmp eq bool %176, %177
    condbr %178, bb9(%38, %39), bb31
bb9(%41: u64, %42: u64):
    %179 = load u64, ptr %111
    %180 = const u64 1
    %181, %182 = sub.overflow u64 %41, %180
    store u64 %181, ptr %112
    %183 = const i64 8
    %184 = gep i8, ptr %112, %183
    store bool %182, ptr %184
    %185 = const i64 8
    %186 = gep i8, ptr %112, %185
    %187 = load bool, ptr %186
    %188 = const bool false
    %189 = icmp eq bool %187, %188
    condbr %189, bb10(%42, %179), bb31
bb10(%43: u64, %44: u64):
    %190 = load u64, ptr %112
    %191, %192 = sub.overflow u64 %190, %44
    store u64 %191, ptr %113
    %193 = const i64 8
    %194 = gep i8, ptr %113, %193
    store bool %192, ptr %194
    %195 = const i64 8
    %196 = gep i8, ptr %113, %195
    %197 = load bool, ptr %196
    %198 = const bool false
    %199 = icmp eq bool %197, %198
    condbr %199, bb11(%43), bb31
bb11(%45: u64):
    %200 = load u64, ptr %113
    %201, %202 = add.overflow u64 %200, %45
    store u64 %201, ptr %114
    %203 = const i64 8
    %204 = gep i8, ptr %114, %203
    store bool %202, ptr %204
    %205 = const i64 8
    %206 = gep i8, ptr %114, %205
    %207 = load bool, ptr %206
    %208 = const bool false
    %209 = icmp eq bool %207, %208
    condbr %209, bb12, bb31
bb12:
    %210 = load u64, ptr %114
    br bb23(%210)
bb13(%46: u64, %47: u64, %48: u64, %49: u64, %50: u64, %51: u64, %52: u64):
    %211 = const u64 1
    %212, %213 = sub.overflow u64 %47, %211
    store u64 %212, ptr %115
    %214 = const i64 8
    %215 = gep i8, ptr %115, %214
    store bool %213, ptr %215
    %216 = const i64 8
    %217 = gep i8, ptr %115, %216
    %218 = load bool, ptr %217
    %219 = const bool false
    %220 = icmp eq bool %218, %219
    condbr %220, bb14(%46, %47, %48, %49, %50, %51, %52), bb31
bb14(%53: u64, %54: u64, %55: u64, %56: u64, %57: u64, %58: u64, %59: u64):
    %221 = load u64, ptr %115
    %222, %223 = sub.overflow u64 %59, %53
    store u64 %222, ptr %116
    %224 = const i64 8
    %225 = gep i8, ptr %116, %224
    store bool %223, ptr %225
    %226 = const i64 8
    %227 = gep i8, ptr %116, %226
    %228 = load bool, ptr %227
    %229 = const bool false
    %230 = icmp eq bool %228, %229
    condbr %230, bb15(%54, %55, %56, %57, %58, %221), bb31
bb15(%60: u64, %61: u64, %62: u64, %63: u64, %64: u64, %65: u64):
    %231 = load u64, ptr %116
    %232, %233 = sub.overflow u64 %65, %231
    store u64 %232, ptr %117
    %234 = const i64 8
    %235 = gep i8, ptr %117, %234
    store bool %233, ptr %235
    %236 = const i64 8
    %237 = gep i8, ptr %117, %236
    %238 = load bool, ptr %237
    %239 = const bool false
    %240 = icmp eq bool %238, %239
    condbr %240, bb16(%60, %61, %62, %63, %64), bb31
bb16(%66: u64, %67: u64, %68: u64, %69: u64, %70: u64):
    %241 = load u64, ptr %117
    %242, %243 = add.overflow u64 %67, %68
    store u64 %242, ptr %118
    %244 = const i64 8
    %245 = gep i8, ptr %118, %244
    store bool %243, ptr %245
    %246 = const i64 8
    %247 = gep i8, ptr %118, %246
    %248 = load bool, ptr %247
    %249 = const bool false
    %250 = icmp eq bool %248, %249
    condbr %250, bb17(%66, %69, %70, %241), bb31
bb17(%71: u64, %72: u64, %73: u64, %74: u64):
    %251 = load u64, ptr %118
    %252, %253 = add.overflow u64 %251, %72
    store u64 %252, ptr %119
    %254 = const i64 8
    %255 = gep i8, ptr %119, %254
    store bool %253, ptr %255
    %256 = const i64 8
    %257 = gep i8, ptr %119, %256
    %258 = load bool, ptr %257
    %259 = const bool false
    %260 = icmp eq bool %258, %259
    condbr %260, bb18(%71, %73, %74), bb31
bb18(%75: u64, %76: u64, %77: u64):
    %261 = load u64, ptr %119
    %262, %263 = add.overflow u64 %261, %75
    store u64 %262, ptr %120
    %264 = const i64 8
    %265 = gep i8, ptr %120, %264
    store bool %263, ptr %265
    %266 = const i64 8
    %267 = gep i8, ptr %120, %266
    %268 = load bool, ptr %267
    %269 = const bool false
    %270 = icmp eq bool %268, %269
    condbr %270, bb19(%76, %77), bb31
bb19(%78: u64, %79: u64):
    %271 = load u64, ptr %120
    %272 = const u64 1
    %273, %274 = sub.overflow u64 %271, %272
    store u64 %273, ptr %121
    %275 = const i64 8
    %276 = gep i8, ptr %121, %275
    store bool %274, ptr %276
    %277 = const i64 8
    %278 = gep i8, ptr %121, %277
    %279 = load bool, ptr %278
    %280 = const bool false
    %281 = icmp eq bool %279, %280
    condbr %281, bb20(%78, %79), bb31
bb20(%80: u64, %81: u64):
    %282 = load u64, ptr %121
    %283, %284 = sub.overflow u64 %282, %81
    store u64 %283, ptr %122
    %285 = const i64 8
    %286 = gep i8, ptr %122, %285
    store bool %284, ptr %286
    %287 = const i64 8
    %288 = gep i8, ptr %122, %287
    %289 = load bool, ptr %288
    %290 = const bool false
    %291 = icmp eq bool %289, %290
    condbr %291, bb21(%80), bb31
bb21(%82: u64):
    %292 = load u64, ptr %122
    %293, %294 = add.overflow u64 %292, %82
    store u64 %293, ptr %123
    %295 = const i64 8
    %296 = gep i8, ptr %123, %295
    store bool %294, ptr %296
    %297 = const i64 8
    %298 = gep i8, ptr %123, %297
    %299 = load bool, ptr %298
    %300 = const bool false
    %301 = icmp eq bool %299, %300
    condbr %301, bb22, bb31
bb22:
    %302 = load u64, ptr %123
    br bb23(%302)
bb23(%83: u64):
    %303 = call @func.103(%83)
    br bb24(%303)
bb24(%84: u32):
    call @func.83(%0, %84)
    br bb30
bb25(%85: u64, %86: u64, %87: u64, %88: u64, %89: u64, %90: u64, %91: ptr, %92: ptr):
    %304 = const bool true
    call @func.113(%124, %92, %85, %86, %87, %88, %89, %90)
    br bb26(%85, %86, %87, %88, %89, %90, %91)
bb26(%93: u64, %94: u64, %95: u64, %96: u64, %97: u64, %98: u64, %99: ptr):
    %305 = load ptr, ptr %99
    %306 = const i64 16
    %307 = gep i8, ptr %305, %306
    br bb27(%93, %94, %95, %96, %97, %98, %307)
bb27(%100: u64, %101: u64, %102: u64, %103: u64, %104: u64, %105: u64, %106: ptr):
    call @func.113(%125, %106, %100, %101, %102, %103, %104, %105)
    br bb28
bb28:
    %308 = const bool false
    %309 = load i64, ptr %124
    store i64 %309, ptr %126
    %310 = const i64 8
    %311 = gep i8, ptr %124, %310
    %312 = const i64 8
    %313 = gep i8, ptr %126, %312
    %314 = load i64, ptr %311
    store i64 %314, ptr %313
    %315 = const i64 16
    %316 = gep i8, ptr %124, %315
    %317 = const i64 16
    %318 = gep i8, ptr %126, %317
    %319 = load i64, ptr %316
    store i64 %319, ptr %318
    %320 = const i64 24
    %321 = gep i8, ptr %124, %320
    %322 = const i64 24
    %323 = gep i8, ptr %126, %322
    %324 = load i64, ptr %321
    store i64 %324, ptr %323
    %325 = const i64 32
    %326 = gep i8, ptr %124, %325
    %327 = const i64 32
    %328 = gep i8, ptr %126, %327
    %329 = load i64, ptr %326
    store i64 %329, ptr %328
    call @func.84(%0, %126, %125)
    br bb29
bb29:
    %330 = const bool false
    br bb30
bb30:
    ret
bb31:
    unreachable
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecTNtCs6RT0DENTjyC_27clean_mutual_recursor_slice10BinderDataNtBF_4ExprEE3newBF_(functy.114) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecTNtCs6RT0DENTjyC_27clean_mutual_recursor_slice10BinderDataNtBI_4ExprEE4pushBI_(functy.115) {
}

fn @collect_pi_domains(functy.116) {
bb0(%0: ptr, %1: ptr):
    %10 = alloca (i64, i64, i64), align 8
    %11 = alloca i64, align 8
    %12 = alloca i64, align 8
    %13 = alloca (i64, i64, i64, i64, i64, i64), align 8
    %14 = alloca (i8, i8), align 1
    %15 = alloca (i64, i64, i64, i64, i64), align 8
    call @func.114(%10)
    br bb1(%1)
bb1(%2: ptr):
    store ptr %2, ptr %11
    br bb2
bb2:
    %16 = load ptr, ptr %11
    store ptr %16, ptr %12
    %17 = load ptr, ptr %12
    %18 = load i8, ptr %17
    %19 = sext i8 %18 to i64
    switch %19 [ 6: bb3 default: bb8 ]
bb3:
    %20 = load ptr, ptr %12
    %21 = const i64 1
    %22 = gep i8, ptr %20, %21
    %23 = load ptr, ptr %12
    %24 = const i64 8
    %25 = gep i8, ptr %23, %24
    %26 = load ptr, ptr %12
    %27 = const i64 16
    %28 = gep i8, ptr %26, %27
    %29 = load i8, ptr %22
    store i8 %29, ptr %14
    %30 = const i64 1
    %31 = gep i8, ptr %22, %30
    %32 = const i64 1
    %33 = gep i8, ptr %14, %32
    %34 = load i8, ptr %31
    store i8 %34, ptr %33
    %35 = load ptr, ptr %25
    %36 = const i64 16
    %37 = gep i8, ptr %35, %36
    br bb4(%28, %10, %37)
bb4(%3: ptr, %4: ptr, %5: ptr):
    call @func.78(%15, %5)
    br bb5(%3, %4)
bb5(%6: ptr, %7: ptr):
    %38 = load i8, ptr %14
    store i8 %38, ptr %13
    %39 = const i64 1
    %40 = gep i8, ptr %14, %39
    %41 = const i64 1
    %42 = gep i8, ptr %13, %41
    %43 = load i8, ptr %40
    store i8 %43, ptr %42
    %44 = const i64 8
    %45 = gep i8, ptr %13, %44
    %46 = load i64, ptr %15
    store i64 %46, ptr %45
    %47 = const i64 8
    %48 = gep i8, ptr %15, %47
    %49 = const i64 8
    %50 = gep i8, ptr %45, %49
    %51 = load i64, ptr %48
    store i64 %51, ptr %50
    %52 = const i64 16
    %53 = gep i8, ptr %15, %52
    %54 = const i64 16
    %55 = gep i8, ptr %45, %54
    %56 = load i64, ptr %53
    store i64 %56, ptr %55
    %57 = const i64 24
    %58 = gep i8, ptr %15, %57
    %59 = const i64 24
    %60 = gep i8, ptr %45, %59
    %61 = load i64, ptr %58
    store i64 %61, ptr %60
    %62 = const i64 32
    %63 = gep i8, ptr %15, %62
    %64 = const i64 32
    %65 = gep i8, ptr %45, %64
    %66 = load i64, ptr %63
    store i64 %66, ptr %65
    call @func.115(%7, %13)
    br bb6(%6)
bb6(%8: ptr):
    %67 = load ptr, ptr %8
    %68 = const i64 16
    %69 = gep i8, ptr %67, %68
    br bb7(%69)
bb7(%9: ptr):
    store ptr %9, ptr %11
    br bb2
bb8:
    %70 = load i64, ptr %10
    store i64 %70, ptr %0
    %71 = const i64 8
    %72 = gep i8, ptr %10, %71
    %73 = const i64 8
    %74 = gep i8, ptr %0, %73
    %75 = load i64, ptr %72
    store i64 %75, ptr %74
    %76 = const i64 16
    %77 = gep i8, ptr %10, %76
    %78 = const i64 16
    %79 = gep i8, ptr %0, %78
    %80 = load i64, ptr %77
    store i64 %80, ptr %79
    ret
}

fn @Expr__lam(functy.117) {
bb0(%0: ptr, %1: ptr, %2: ptr, %3: ptr):
    %4 = alloca (i64, i64, i64, i64), align 8
    %5 = alloca i64, align 8
    %6 = alloca i64, align 8
    %7 = alloca (i64, i64, i64, i64, i64), align 8
    %8 = const bool false
    %9 = const bool true
    %10 = const i64 56
    %11 = heap_alloc rust_heap i8, %10, align 8
    %12 = const u64 1
    store u64 %12, ptr %11
    %13 = const i64 8
    %14 = gep i8, ptr %11, %13
    %15 = const u64 1
    store u64 %15, ptr %14
    %16 = const i64 16
    %17 = gep i8, ptr %11, %16
    %18 = load i64, ptr %2
    store i64 %18, ptr %17
    %19 = const i64 8
    %20 = gep i8, ptr %2, %19
    %21 = const i64 8
    %22 = gep i8, ptr %17, %21
    %23 = load i64, ptr %20
    store i64 %23, ptr %22
    %24 = const i64 16
    %25 = gep i8, ptr %2, %24
    %26 = const i64 16
    %27 = gep i8, ptr %17, %26
    %28 = load i64, ptr %25
    store i64 %28, ptr %27
    %29 = const i64 24
    %30 = gep i8, ptr %2, %29
    %31 = const i64 24
    %32 = gep i8, ptr %17, %31
    %33 = load i64, ptr %30
    store i64 %33, ptr %32
    %34 = const i64 32
    %35 = gep i8, ptr %2, %34
    %36 = const i64 32
    %37 = gep i8, ptr %17, %36
    %38 = load i64, ptr %35
    store i64 %38, ptr %37
    store ptr %11, ptr %5
    br bb1
bb1:
    %39 = const bool false
    %40 = load i64, ptr %3
    store i64 %40, ptr %7
    %41 = const i64 8
    %42 = gep i8, ptr %3, %41
    %43 = const i64 8
    %44 = gep i8, ptr %7, %43
    %45 = load i64, ptr %42
    store i64 %45, ptr %44
    %46 = const i64 16
    %47 = gep i8, ptr %3, %46
    %48 = const i64 16
    %49 = gep i8, ptr %7, %48
    %50 = load i64, ptr %47
    store i64 %50, ptr %49
    %51 = const i64 24
    %52 = gep i8, ptr %3, %51
    %53 = const i64 24
    %54 = gep i8, ptr %7, %53
    %55 = load i64, ptr %52
    store i64 %55, ptr %54
    %56 = const i64 32
    %57 = gep i8, ptr %3, %56
    %58 = const i64 32
    %59 = gep i8, ptr %7, %58
    %60 = load i64, ptr %57
    store i64 %60, ptr %59
    %61 = const i64 56
    %62 = heap_alloc rust_heap i8, %61, align 8
    %63 = const u64 1
    store u64 %63, ptr %62
    %64 = const i64 8
    %65 = gep i8, ptr %62, %64
    %66 = const u64 1
    store u64 %66, ptr %65
    %67 = const i64 16
    %68 = gep i8, ptr %62, %67
    %69 = load i64, ptr %7
    store i64 %69, ptr %68
    %70 = const i64 8
    %71 = gep i8, ptr %7, %70
    %72 = const i64 8
    %73 = gep i8, ptr %68, %72
    %74 = load i64, ptr %71
    store i64 %74, ptr %73
    %75 = const i64 16
    %76 = gep i8, ptr %7, %75
    %77 = const i64 16
    %78 = gep i8, ptr %68, %77
    %79 = load i64, ptr %76
    store i64 %79, ptr %78
    %80 = const i64 24
    %81 = gep i8, ptr %7, %80
    %82 = const i64 24
    %83 = gep i8, ptr %68, %82
    %84 = load i64, ptr %81
    store i64 %84, ptr %83
    %85 = const i64 32
    %86 = gep i8, ptr %7, %85
    %87 = const i64 32
    %88 = gep i8, ptr %68, %87
    %89 = load i64, ptr %86
    store i64 %89, ptr %88
    store ptr %62, ptr %6
    br bb2
bb2:
    %90 = const i64 1
    %91 = gep i8, ptr %4, %90
    %92 = load i8, ptr %1
    store i8 %92, ptr %91
    %93 = const i64 1
    %94 = gep i8, ptr %1, %93
    %95 = const i64 1
    %96 = gep i8, ptr %91, %95
    %97 = load i8, ptr %94
    store i8 %97, ptr %96
    %98 = load ptr, ptr %5
    %99 = const i64 8
    %100 = gep i8, ptr %4, %99
    store ptr %98, ptr %100
    %101 = load ptr, ptr %6
    %102 = const i64 16
    %103 = gep i8, ptr %4, %102
    store ptr %101, ptr %103
    %104 = const i8 5
    store i8 %104, ptr %4
    call @func.82(%0, %4)
    br bb3
bb3:
    ret
}

fn @Expr__sort(functy.118) {
bb0(%0: ptr, %1: ptr):
    %2 = alloca (i64, i64, i64, i64), align 8
    %3 = const i64 8
    %4 = gep i8, ptr %2, %3
    %5 = load i64, ptr %1
    store i64 %5, ptr %4
    %6 = const i64 8
    %7 = gep i8, ptr %1, %6
    %8 = const i64 8
    %9 = gep i8, ptr %4, %8
    %10 = load i64, ptr %7
    store i64 %10, ptr %9
    %11 = const i8 2
    store i8 %11, ptr %2
    call @func.82(%0, %2)
    br bb1
bb1:
    ret
}

fn @field_is_eliminably_recursive(functy.119) {
bb0(%0: ptr, %1: ptr):
    %4 = alloca i64, align 8
    %5 = alloca i64, align 8
    %6 = call @func.110(%0)
    br bb1(%6)
bb1(%2: ptr):
    %7 = call @func.111(%2)
    store ptr %7, ptr %4
    br bb2
bb2:
    %8 = load ptr, ptr %4
    store ptr %8, ptr %5
    %9 = load ptr, ptr %5
    %10 = load i8, ptr %9
    %11 = sext i8 %10 to i64
    switch %11 [ 3: bb4 default: bb3 ]
bb3:
    %12 = const bool false
    br bb5(%12)
bb4:
    %13 = load ptr, ptr %5
    %14 = const i64 4
    %15 = gep i8, ptr %13, %14
    %16 = call @func.137(%15, %1)
    br bb5(%16)
bb5(%3: bool):
    ret %3
}

fn @consume_type_annotations(functy.120) {
bb0(%0: ptr):
    ret %0
}

fn @_RNvXsu_NtCskTzINo8ZBH9_5alloc4syncINtB5_3ArcNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4ExprENtNtCs2EYQwhfuABO_4core5clone5Clone5cloneBI_(functy.121) {
}

fn @_RNvXsa_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice5LevelENtNtCs2EYQwhfuABO_4core5clone5Clone5cloneBH_(functy.122) {
}

fn @_ExprKind_as_std__clone__Clone___clone(functy.123) {
bb0(%0: ptr, %1: ptr):
    %23 = alloca i64, align 8
    %24 = alloca i64, align 8
    %25 = alloca (i64, i64), align 8
    %26 = alloca i32, align 4
    %27 = alloca (i64, i64, i64), align 8
    %28 = alloca i64, align 8
    %29 = alloca i64, align 8
    %30 = alloca (i8, i8), align 1
    %31 = alloca i64, align 8
    %32 = alloca i64, align 8
    %33 = alloca (i8, i8), align 1
    %34 = alloca i64, align 8
    %35 = alloca i64, align 8
    %36 = alloca i32, align 4
    %37 = alloca i64, align 8
    %38 = alloca i64, align 8
    %39 = alloca i64, align 8
    %40 = alloca (i64, i64), align 8
    %41 = alloca i32, align 4
    %42 = alloca i64, align 8
    store ptr %1, ptr %23
    %43 = load ptr, ptr %23
    %44 = load i8, ptr %43
    %45 = sext i8 %44 to i64
    switch %45 [ 0: bb11 1: bb10 2: bb9 3: bb8 4: bb7 5: bb6 6: bb5 7: bb4 8: bb3 9: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %46 = load ptr, ptr %23
    %47 = const i64 4
    %48 = gep i8, ptr %46, %47
    %49 = load ptr, ptr %23
    %50 = const i64 8
    %51 = gep i8, ptr %49, %50
    %52 = load ptr, ptr %23
    %53 = const i64 16
    %54 = gep i8, ptr %52, %53
    call @func.71(%41, %48)
    br bb29(%51, %54)
bb3:
    %55 = load ptr, ptr %23
    %56 = const i64 8
    %57 = gep i8, ptr %55, %56
    call @func.138(%40, %57)
    br bb28
bb4:
    %58 = load ptr, ptr %23
    %59 = const i64 4
    %60 = gep i8, ptr %58, %59
    %61 = load ptr, ptr %23
    %62 = const i64 8
    %63 = gep i8, ptr %61, %62
    %64 = load ptr, ptr %23
    %65 = const i64 16
    %66 = gep i8, ptr %64, %65
    %67 = load ptr, ptr %23
    %68 = const i64 24
    %69 = gep i8, ptr %67, %68
    %70 = load ptr, ptr %23
    %71 = const i64 1
    %72 = gep i8, ptr %70, %71
    call @func.71(%36, %60)
    br bb24(%63, %66, %69, %72)
bb5:
    %73 = load ptr, ptr %23
    %74 = const i64 1
    %75 = gep i8, ptr %73, %74
    %76 = load ptr, ptr %23
    %77 = const i64 8
    %78 = gep i8, ptr %76, %77
    %79 = load ptr, ptr %23
    %80 = const i64 16
    %81 = gep i8, ptr %79, %80
    call @func.139(%33, %75)
    br bb21(%78, %81)
bb6:
    %82 = load ptr, ptr %23
    %83 = const i64 1
    %84 = gep i8, ptr %82, %83
    %85 = load ptr, ptr %23
    %86 = const i64 8
    %87 = gep i8, ptr %85, %86
    %88 = load ptr, ptr %23
    %89 = const i64 16
    %90 = gep i8, ptr %88, %89
    call @func.139(%30, %84)
    br bb18(%87, %90)
bb7:
    %91 = load ptr, ptr %23
    %92 = const i64 8
    %93 = gep i8, ptr %91, %92
    %94 = load ptr, ptr %23
    %95 = const i64 16
    %96 = gep i8, ptr %94, %95
    call @func.121(%28, %93)
    br bb16(%96)
bb8:
    %97 = load ptr, ptr %23
    %98 = const i64 4
    %99 = gep i8, ptr %97, %98
    %100 = load ptr, ptr %23
    %101 = const i64 8
    %102 = gep i8, ptr %100, %101
    call @func.71(%26, %99)
    br bb14(%102)
bb9:
    %103 = load ptr, ptr %23
    %104 = const i64 8
    %105 = gep i8, ptr %103, %104
    call @func.81(%25, %105)
    br bb13
bb10:
    %106 = load ptr, ptr %23
    %107 = const i64 8
    %108 = gep i8, ptr %106, %107
    call @func.140(%24, %108)
    br bb12
bb11:
    %109 = load ptr, ptr %23
    %110 = const i64 4
    %111 = gep i8, ptr %109, %110
    %112 = load u32, ptr %111
    %113 = const i64 4
    %114 = gep i8, ptr %0, %113
    store u32 %112, ptr %114
    %115 = const i8 0
    store i8 %115, ptr %0
    br bb31
bb12:
    %116 = const i64 8
    %117 = gep i8, ptr %0, %116
    %118 = load i64, ptr %24
    store i64 %118, ptr %117
    %119 = const i8 1
    store i8 %119, ptr %0
    br bb31
bb13:
    %120 = const i64 8
    %121 = gep i8, ptr %0, %120
    %122 = load i64, ptr %25
    store i64 %122, ptr %121
    %123 = const i64 8
    %124 = gep i8, ptr %25, %123
    %125 = const i64 8
    %126 = gep i8, ptr %121, %125
    %127 = load i64, ptr %124
    store i64 %127, ptr %126
    %128 = const i8 2
    store i8 %128, ptr %0
    br bb31
bb14(%2: ptr):
    call @func.122(%27, %2)
    br bb15
bb15:
    %129 = const i64 4
    %130 = gep i8, ptr %0, %129
    %131 = load i32, ptr %26
    store i32 %131, ptr %130
    %132 = const i64 8
    %133 = gep i8, ptr %0, %132
    %134 = load i64, ptr %27
    store i64 %134, ptr %133
    %135 = const i64 8
    %136 = gep i8, ptr %27, %135
    %137 = const i64 8
    %138 = gep i8, ptr %133, %137
    %139 = load i64, ptr %136
    store i64 %139, ptr %138
    %140 = const i64 16
    %141 = gep i8, ptr %27, %140
    %142 = const i64 16
    %143 = gep i8, ptr %133, %142
    %144 = load i64, ptr %141
    store i64 %144, ptr %143
    %145 = const i8 3
    store i8 %145, ptr %0
    br bb31
bb16(%3: ptr):
    call @func.121(%29, %3)
    br bb17
bb17:
    %146 = load ptr, ptr %28
    %147 = const i64 8
    %148 = gep i8, ptr %0, %147
    store ptr %146, ptr %148
    %149 = load ptr, ptr %29
    %150 = const i64 16
    %151 = gep i8, ptr %0, %150
    store ptr %149, ptr %151
    %152 = const i8 4
    store i8 %152, ptr %0
    br bb31
bb18(%4: ptr, %5: ptr):
    call @func.121(%31, %4)
    br bb19(%5)
bb19(%6: ptr):
    call @func.121(%32, %6)
    br bb20
bb20:
    %153 = const i64 1
    %154 = gep i8, ptr %0, %153
    %155 = load i8, ptr %30
    store i8 %155, ptr %154
    %156 = const i64 1
    %157 = gep i8, ptr %30, %156
    %158 = const i64 1
    %159 = gep i8, ptr %154, %158
    %160 = load i8, ptr %157
    store i8 %160, ptr %159
    %161 = load ptr, ptr %31
    %162 = const i64 8
    %163 = gep i8, ptr %0, %162
    store ptr %161, ptr %163
    %164 = load ptr, ptr %32
    %165 = const i64 16
    %166 = gep i8, ptr %0, %165
    store ptr %164, ptr %166
    %167 = const i8 5
    store i8 %167, ptr %0
    br bb31
bb21(%7: ptr, %8: ptr):
    call @func.121(%34, %7)
    br bb22(%8)
bb22(%9: ptr):
    call @func.121(%35, %9)
    br bb23
bb23:
    %168 = const i64 1
    %169 = gep i8, ptr %0, %168
    %170 = load i8, ptr %33
    store i8 %170, ptr %169
    %171 = const i64 1
    %172 = gep i8, ptr %33, %171
    %173 = const i64 1
    %174 = gep i8, ptr %169, %173
    %175 = load i8, ptr %172
    store i8 %175, ptr %174
    %176 = load ptr, ptr %34
    %177 = const i64 8
    %178 = gep i8, ptr %0, %177
    store ptr %176, ptr %178
    %179 = load ptr, ptr %35
    %180 = const i64 16
    %181 = gep i8, ptr %0, %180
    store ptr %179, ptr %181
    %182 = const i8 6
    store i8 %182, ptr %0
    br bb31
bb24(%10: ptr, %11: ptr, %12: ptr, %13: ptr):
    call @func.121(%37, %10)
    br bb25(%11, %12, %13)
bb25(%14: ptr, %15: ptr, %16: ptr):
    call @func.121(%38, %14)
    br bb26(%15, %16)
bb26(%17: ptr, %18: ptr):
    call @func.121(%39, %17)
    br bb27(%18)
bb27(%19: ptr):
    %183 = load bool, ptr %19
    %184 = const i64 4
    %185 = gep i8, ptr %0, %184
    %186 = load i32, ptr %36
    store i32 %186, ptr %185
    %187 = load ptr, ptr %37
    %188 = const i64 8
    %189 = gep i8, ptr %0, %188
    store ptr %187, ptr %189
    %190 = load ptr, ptr %38
    %191 = const i64 16
    %192 = gep i8, ptr %0, %191
    store ptr %190, ptr %192
    %193 = load ptr, ptr %39
    %194 = const i64 24
    %195 = gep i8, ptr %0, %194
    store ptr %193, ptr %195
    %196 = const i64 1
    %197 = gep i8, ptr %0, %196
    store bool %183, ptr %197
    %198 = const i8 7
    store i8 %198, ptr %0
    br bb31
bb28:
    %199 = const i64 8
    %200 = gep i8, ptr %0, %199
    %201 = load i64, ptr %40
    store i64 %201, ptr %200
    %202 = const i64 8
    %203 = gep i8, ptr %40, %202
    %204 = const i64 8
    %205 = gep i8, ptr %200, %204
    %206 = load i64, ptr %203
    store i64 %206, ptr %205
    %207 = const i8 8
    store i8 %207, ptr %0
    br bb31
bb29(%20: ptr, %21: ptr):
    %208 = load u32, ptr %20
    call @func.121(%42, %21)
    br bb30(%208)
bb30(%22: u32):
    %209 = const i64 4
    %210 = gep i8, ptr %0, %209
    %211 = load i32, ptr %41
    store i32 %211, ptr %210
    %212 = const i64 8
    %213 = gep i8, ptr %0, %212
    store u32 %22, ptr %213
    %214 = load ptr, ptr %42
    %215 = const i64 16
    %216 = gep i8, ptr %0, %215
    store ptr %214, ptr %216
    %217 = const i8 9
    store i8 %217, ptr %0
    br bb31
bb31:
    ret
}

fn @_ExprMeta_as_std__clone__Clone___clone(functy.124) {
bb0(%0: ptr, %1: ptr):
    %2 = load i64, ptr %1
    store i64 %2, ptr %0
    ret
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm14saturating_add(functy.125) {
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice5LevelE3lenBG_(functy.126) {
}

fn @_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6RT0DENTjyC_27clean_mutual_recursor_slice5LevelEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_(functy.127) {
}

fn @_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3minCs6RT0DENTjyC_27clean_mutual_recursor_slice(functy.128) {
}

fn @ExprKind__compute_meta(functy.129) {
bb0(%0: ptr, %1: ptr):
    %136 = alloca i64, align 8
    %137 = alloca i64, align 8
    %138 = alloca i64, align 8
    %139 = alloca i64, align 8
    %140 = alloca i64, align 8
    %141 = alloca i64, align 8
    %142 = alloca i64, align 8
    %143 = alloca (i64, i64), align 8
    %144 = alloca i64, align 8
    %145 = alloca i64, align 8
    %146 = alloca i64, align 8
    %147 = alloca i64, align 8
    %148 = alloca (i32, i32), align 4
    store ptr %1, ptr %136
    %149 = load ptr, ptr %136
    %150 = load i8, ptr %149
    %151 = sext i8 %150 to i64
    switch %151 [ 0: bb11 1: bb5 2: bb7 3: bb6 4: bb10 5: bb9 6: bb8 7: bb4 8: bb3 9: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %152 = load ptr, ptr %136
    %153 = const i64 4
    %154 = gep i8, ptr %152, %153
    %155 = load ptr, ptr %136
    %156 = const i64 8
    %157 = gep i8, ptr %155, %156
    %158 = load ptr, ptr %136
    %159 = const i64 16
    %160 = gep i8, ptr %158, %159
    %161 = load ptr, ptr %160
    %162 = const i64 16
    %163 = gep i8, ptr %161, %162
    br bb50(%154, %157, %163)
bb3:
    %164 = load ptr, ptr %136
    %165 = const i64 8
    %166 = gep i8, ptr %164, %165
    %167 = call @func.141(%166)
    br bb48(%167)
bb4:
    %168 = load ptr, ptr %136
    %169 = const i64 8
    %170 = gep i8, ptr %168, %169
    %171 = load ptr, ptr %136
    %172 = const i64 16
    %173 = gep i8, ptr %171, %172
    %174 = load ptr, ptr %136
    %175 = const i64 24
    %176 = gep i8, ptr %174, %175
    %177 = load ptr, ptr %170
    %178 = const i64 16
    %179 = gep i8, ptr %177, %178
    br bb42(%173, %176, %179)
bb5:
    %180 = load ptr, ptr %136
    %181 = const i64 8
    %182 = gep i8, ptr %180, %181
    %183 = load u64, ptr %182
    %184 = const u64 13
    %185 = call @func.143(%184, %183)
    br bb41(%185)
bb6:
    %186 = load ptr, ptr %136
    %187 = const i64 4
    %188 = gep i8, ptr %186, %187
    %189 = load ptr, ptr %136
    %190 = const i64 8
    %191 = gep i8, ptr %189, %190
    %192 = call @func.144(%188)
    br bb30(%191, %192)
bb7:
    %193 = load ptr, ptr %136
    %194 = const i64 8
    %195 = gep i8, ptr %193, %194
    %196 = call @func.145(%195)
    br bb26(%195, %196)
bb8:
    %197 = load ptr, ptr %136
    %198 = const i64 1
    %199 = gep i8, ptr %197, %198
    %200 = load ptr, ptr %136
    %201 = const i64 8
    %202 = gep i8, ptr %200, %201
    %203 = load ptr, ptr %136
    %204 = const i64 16
    %205 = gep i8, ptr %203, %204
    %206 = load ptr, ptr %202
    %207 = const i64 16
    %208 = gep i8, ptr %206, %207
    br bb22(%205, %208)
bb9:
    %209 = load ptr, ptr %136
    %210 = const i64 1
    %211 = gep i8, ptr %209, %210
    %212 = load ptr, ptr %136
    %213 = const i64 8
    %214 = gep i8, ptr %212, %213
    %215 = load ptr, ptr %136
    %216 = const i64 16
    %217 = gep i8, ptr %215, %216
    %218 = load ptr, ptr %214
    %219 = const i64 16
    %220 = gep i8, ptr %218, %219
    br bb18(%217, %220)
bb10:
    %221 = load ptr, ptr %136
    %222 = const i64 8
    %223 = gep i8, ptr %221, %222
    %224 = load ptr, ptr %136
    %225 = const i64 16
    %226 = gep i8, ptr %224, %225
    %227 = load ptr, ptr %223
    %228 = const i64 16
    %229 = gep i8, ptr %227, %228
    br bb14(%226, %229)
bb11:
    %230 = load ptr, ptr %136
    %231 = const i64 4
    %232 = gep i8, ptr %230, %231
    %233 = load u32, ptr %232
    %234 = zext u32 %233 to u64
    %235 = const u64 7
    %236 = call @func.143(%235, %234)
    br bb12(%232, %236)
bb12(%2: ptr, %3: u64):
    %237 = trunc u64 %3 to u32
    %238 = load u32, ptr %2
    %239 = const u32 1
    %240 = call @func.125(%238, %239)
    br bb13(%237, %240)
bb13(%4: u32, %5: u32):
    %241 = const u32 0
    %242 = const bool false
    %243 = const bool false
    %244 = const bool false
    %245 = const bool false
    call @func.147(%0, %4, %5, %241, %242, %243, %244, %245)
    br bb65
bb14(%6: ptr, %7: ptr):
    call @func.148(%137, %7)
    br bb15(%6)
bb15(%8: ptr):
    %246 = load ptr, ptr %8
    %247 = const i64 16
    %248 = gep i8, ptr %246, %247
    br bb16(%248)
bb16(%9: ptr):
    call @func.148(%138, %9)
    br bb17
bb17:
    %249 = load u64, ptr %137
    %250 = load u64, ptr %138
    call @func.152(%0, %249, %250)
    br bb65
bb18(%10: ptr, %11: ptr):
    call @func.148(%139, %11)
    br bb19(%10)
bb19(%12: ptr):
    %251 = load ptr, ptr %12
    %252 = const i64 16
    %253 = gep i8, ptr %251, %252
    br bb20(%253)
bb20(%13: ptr):
    call @func.148(%140, %13)
    br bb21
bb21:
    %254 = load u64, ptr %139
    %255 = load u64, ptr %140
    %256 = const u64 0
    call @func.157(%0, %254, %255, %256)
    br bb65
bb22(%14: ptr, %15: ptr):
    call @func.148(%141, %15)
    br bb23(%14)
bb23(%16: ptr):
    %257 = load ptr, ptr %16
    %258 = const i64 16
    %259 = gep i8, ptr %257, %258
    br bb24(%259)
bb24(%17: ptr):
    call @func.148(%142, %17)
    br bb25
bb25:
    %260 = load u64, ptr %141
    %261 = load u64, ptr %142
    %262 = const u64 1
    call @func.157(%0, %260, %261, %262)
    br bb65
bb26(%18: ptr, %19: u64):
    %263 = const u64 11
    %264 = call @func.143(%263, %19)
    br bb27(%18, %264)
bb27(%20: ptr, %21: u64):
    %265 = trunc u64 %21 to u32
    %266 = call @func.158(%20)
    br bb28(%20, %265, %266)
bb28(%22: ptr, %23: u32, %24: bool):
    %267 = call @func.159(%22)
    br bb29(%23, %24, %267)
bb29(%25: u32, %26: bool, %27: bool):
    %268 = const u32 0
    %269 = const u32 0
    %270 = const bool false
    %271 = const bool false
    call @func.147(%0, %25, %268, %269, %270, %271, %26, %27)
    br bb65
bb30(%28: ptr, %29: u64):
    %272 = const bool false
    %273 = const u64 0
    br bb31(%28, %29, %272, %273)
bb31(%30: ptr, %31: u64, %32: bool, %33: u64):
    %274 = call @func.126(%30)
    br bb32(%30, %31, %32, %33, %33, %274)
bb32(%34: ptr, %35: u64, %36: bool, %37: u64, %38: u64, %39: u64):
    %275 = icmp ult u64 %38, %39
    condbr %275, bb33(%34, %35, %36, %37), bb39(%35, %36)
bb33(%40: ptr, %41: u64, %42: bool, %43: u64):
    %276 = call @func.127(%40, %43)
    br bb34(%40, %41, %42, %43, %276)
bb34(%44: ptr, %45: u64, %46: bool, %47: u64, %48: ptr):
    %277 = call @func.159(%48)
    br bb35(%44, %45, %46, %47, %277)
bb35(%49: ptr, %50: u64, %51: bool, %52: u64, %53: bool):
    condbr %53, bb36(%49, %50, %52), bb37(%49, %50, %51, %52)
bb36(%54: ptr, %55: u64, %56: u64):
    %278 = const bool true
    br bb37(%54, %55, %278, %56)
bb37(%57: ptr, %58: u64, %59: bool, %60: u64):
    %279 = const u64 1
    %280, %281 = add.overflow u64 %60, %279
    store u64 %280, ptr %143
    %282 = const i64 8
    %283 = gep i8, ptr %143, %282
    store bool %281, ptr %283
    %284 = const i64 8
    %285 = gep i8, ptr %143, %284
    %286 = load bool, ptr %285
    %287 = const bool false
    %288 = icmp eq bool %286, %287
    condbr %288, bb38(%57, %58, %59), bb66
bb38(%61: ptr, %62: u64, %63: bool):
    %289 = load u64, ptr %143
    br bb31(%61, %62, %63, %289)
bb39(%64: u64, %65: bool):
    %290 = const u64 5
    %291 = call @func.143(%290, %64)
    br bb40(%65, %291)
bb40(%66: bool, %67: u64):
    %292 = trunc u64 %67 to u32
    %293 = const u32 0
    %294 = const u32 0
    %295 = const bool false
    %296 = const bool false
    %297 = const bool false
    call @func.147(%0, %292, %293, %294, %295, %296, %297, %66)
    br bb65
bb41(%68: u64):
    %298 = trunc u64 %68 to u32
    %299 = const u32 0
    %300 = const u32 0
    %301 = const bool true
    %302 = const bool false
    %303 = const bool false
    %304 = const bool false
    call @func.147(%0, %298, %299, %300, %301, %302, %303, %304)
    br bb65
bb42(%69: ptr, %70: ptr, %71: ptr):
    call @func.148(%144, %71)
    br bb43(%69, %70)
bb43(%72: ptr, %73: ptr):
    %305 = load ptr, ptr %72
    %306 = const i64 16
    %307 = gep i8, ptr %305, %306
    br bb44(%73, %307)
bb44(%74: ptr, %75: ptr):
    call @func.148(%145, %75)
    br bb45(%74)
bb45(%76: ptr):
    %308 = load ptr, ptr %76
    %309 = const i64 16
    %310 = gep i8, ptr %308, %309
    br bb46(%310)
bb46(%77: ptr):
    call @func.148(%146, %77)
    br bb47
bb47:
    %311 = load u64, ptr %144
    %312 = load u64, ptr %145
    %313 = load u64, ptr %146
    call @func.164(%0, %311, %312, %313)
    br bb65
bb48(%78: u64):
    %314 = const u64 3
    %315 = call @func.143(%314, %78)
    br bb49(%315)
bb49(%79: u64):
    %316 = trunc u64 %79 to u32
    %317 = const u32 0
    %318 = const u32 0
    %319 = const bool false
    %320 = const bool false
    %321 = const bool false
    %322 = const bool false
    call @func.147(%0, %316, %317, %318, %319, %320, %321, %322)
    br bb65
bb50(%80: ptr, %81: ptr, %82: ptr):
    call @func.148(%147, %82)
    br bb51(%80, %81)
bb51(%83: ptr, %84: ptr):
    %323 = load u64, ptr %147
    %324 = call @func.165(%323)
    br bb52(%83, %84, %324)
bb52(%85: ptr, %86: ptr, %87: u8):
    %325 = zext u8 %87 to u32
    %326 = const u32 1
    %327, %328 = add.overflow u32 %325, %326
    store u32 %327, ptr %148
    %329 = const i64 4
    %330 = gep i8, ptr %148, %329
    store bool %328, ptr %330
    %331 = const i64 4
    %332 = gep i8, ptr %148, %331
    %333 = load bool, ptr %332
    %334 = const bool false
    %335 = icmp eq bool %333, %334
    condbr %335, bb53(%85, %86), bb66
bb53(%88: ptr, %89: ptr):
    %336 = load u32, ptr %148
    %337 = const u32 255
    %338 = call @func.128(%336, %337)
    br bb54(%88, %89, %338)
bb54(%90: ptr, %91: ptr, %92: u32):
    %339 = zext u32 %92 to u64
    %340 = call @func.144(%90)
    br bb55(%91, %92, %339, %340)
bb55(%93: ptr, %94: u32, %95: u64, %96: u64):
    %341 = load u32, ptr %93
    %342 = zext u32 %341 to u64
    %343 = load u64, ptr %147
    %344 = call @func.166(%343)
    br bb56(%94, %95, %96, %342, %344)
bb56(%97: u32, %98: u64, %99: u64, %100: u64, %101: u32):
    %345 = zext u32 %101 to u64
    %346 = call @func.143(%100, %345)
    br bb57(%97, %98, %99, %346)
bb57(%102: u32, %103: u64, %104: u64, %105: u64):
    %347 = call @func.143(%104, %105)
    br bb58(%102, %103, %347)
bb58(%106: u32, %107: u64, %108: u64):
    %348 = call @func.143(%107, %108)
    br bb59(%106, %348)
bb59(%109: u32, %110: u64):
    %349 = trunc u64 %110 to u32
    %350 = load u64, ptr %147
    %351 = call @func.167(%350)
    br bb60(%109, %349, %351)
bb60(%111: u32, %112: u32, %113: u32):
    %352 = load u64, ptr %147
    %353 = call @func.168(%352)
    br bb61(%111, %112, %113, %353)
bb61(%114: u32, %115: u32, %116: u32, %117: bool):
    %354 = load u64, ptr %147
    %355 = call @func.169(%354)
    br bb62(%114, %115, %116, %117, %355)
bb62(%118: u32, %119: u32, %120: u32, %121: bool, %122: bool):
    %356 = load u64, ptr %147
    %357 = call @func.170(%356)
    br bb63(%118, %119, %120, %121, %122, %357)
bb63(%123: u32, %124: u32, %125: u32, %126: bool, %127: bool, %128: bool):
    %358 = load u64, ptr %147
    %359 = call @func.171(%358)
    br bb64(%123, %124, %125, %126, %127, %128, %359)
bb64(%129: u32, %130: u32, %131: u32, %132: bool, %133: bool, %134: bool, %135: bool):
    call @func.147(%0, %130, %131, %129, %132, %133, %134, %135)
    br bb65
bb65:
    ret
bb66:
    unreachable
}

fn @build_minor_premise_type___closure_0_(functy.130) {
bb0(%0: ptr, %1: ptr, %2: ptr, %3: u64):
    %15 = alloca (i64, i64, i64, i64, i64), align 8
    %16 = alloca (i64, i64, i64, i64, i64), align 8
    %17 = alloca (i64, i64), align 8
    %18 = call @func.103(%3)
    br bb1(%1, %3, %2, %18)
bb1(%4: ptr, %5: u64, %6: ptr, %7: u32):
    call @func.106(%15, %6, %7)
    br bb2(%4, %5)
bb2(%8: ptr, %9: u64):
    %19 = load ptr, ptr %8
    %20 = load u64, ptr %19
    %21, %22 = add.overflow u64 %9, %20
    store u64 %21, ptr %17
    %23 = const i64 8
    %24 = gep i8, ptr %17, %23
    store bool %22, ptr %24
    %25 = const i64 8
    %26 = gep i8, ptr %17, %25
    %27 = load bool, ptr %26
    %28 = const bool false
    %29 = icmp eq bool %27, %28
    condbr %29, bb3(%8, %15), bb8
bb3(%10: ptr, %11: ptr):
    %30 = load u64, ptr %17
    %31 = call @func.103(%30)
    br bb4(%10, %11, %31)
bb4(%12: ptr, %13: ptr, %14: u32):
    %32 = const i64 8
    %33 = gep i8, ptr %12, %32
    %34 = load ptr, ptr %33
    %35 = load u64, ptr %34
    %36 = trunc u64 %35 to u32
    call @func.105(%16, %13, %14, %36)
    br bb5
bb5:
    br bb6
bb6:
    %37 = load i64, ptr %16
    store i64 %37, ptr %15
    %38 = const i64 8
    %39 = gep i8, ptr %16, %38
    %40 = const i64 8
    %41 = gep i8, ptr %15, %40
    %42 = load i64, ptr %39
    store i64 %42, ptr %41
    %43 = const i64 16
    %44 = gep i8, ptr %16, %43
    %45 = const i64 16
    %46 = gep i8, ptr %15, %45
    %47 = load i64, ptr %44
    store i64 %47, ptr %46
    %48 = const i64 24
    %49 = gep i8, ptr %16, %48
    %50 = const i64 24
    %51 = gep i8, ptr %15, %50
    %52 = load i64, ptr %49
    store i64 %52, ptr %51
    %53 = const i64 32
    %54 = gep i8, ptr %16, %53
    %55 = const i64 32
    %56 = gep i8, ptr %15, %55
    %57 = load i64, ptr %54
    store i64 %57, ptr %56
    %58 = load i64, ptr %15
    store i64 %58, ptr %0
    %59 = const i64 8
    %60 = gep i8, ptr %15, %59
    %61 = const i64 8
    %62 = gep i8, ptr %0, %61
    %63 = load i64, ptr %60
    store i64 %63, ptr %62
    %64 = const i64 16
    %65 = gep i8, ptr %15, %64
    %66 = const i64 16
    %67 = gep i8, ptr %0, %66
    %68 = load i64, ptr %65
    store i64 %68, ptr %67
    %69 = const i64 24
    %70 = gep i8, ptr %15, %69
    %71 = const i64 24
    %72 = gep i8, ptr %0, %71
    %73 = load i64, ptr %70
    store i64 %73, ptr %72
    %74 = const i64 32
    %75 = gep i8, ptr %15, %74
    %76 = const i64 32
    %77 = gep i8, ptr %0, %76
    %78 = load i64, ptr %75
    store i64 %78, ptr %77
    br bb7
bb7:
    ret
bb8:
    unreachable
}

fn @_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4NameNtB7_9PartialEq2eqBF_(functy.131) {
}

fn @field_motive_index(functy.132) {
bb0(%0: ptr, %1: ptr):
    %12 = alloca i64, align 8
    %13 = alloca i64, align 8
    %14 = alloca i64, align 8
    %15 = alloca i64, align 8
    %16 = alloca (i64, i64), align 8
    %17 = call @func.110(%0)
    br bb1(%17)
bb1(%2: ptr):
    %18 = call @func.111(%2)
    store ptr %18, ptr %12
    br bb2
bb2:
    %19 = load ptr, ptr %12
    store ptr %19, ptr %13
    %20 = load ptr, ptr %13
    %21 = load i8, ptr %20
    %22 = sext i8 %21 to i64
    switch %22 [ 3: bb3 default: bb11 ]
bb3:
    %23 = load ptr, ptr %13
    %24 = const i64 4
    %25 = gep i8, ptr %23, %24
    store ptr %25, ptr %14
    %26 = const u64 0
    br bb4(%26)
bb4(%3: u64):
    %27 = const i64 8
    %28 = gep i8, ptr %1, %27
    %29 = load u64, ptr %28
    %30 = icmp ult u64 %3, %29
    condbr %30, bb5(%3), bb11
bb5(%4: u64):
    %31 = const i64 8
    %32 = gep i8, ptr %1, %31
    %33 = load u64, ptr %32
    %34 = icmp ult u64 %4, %33
    condbr %34, bb6(%4, %4), bb13
bb6(%5: u64, %6: u64):
    %35 = load ptr, ptr %1
    %36 = const u64 72
    %37 = mul u64 %6, %36
    %38 = gep i8, ptr %35, %37
    %39 = const i64 64
    %40 = gep i8, ptr %38, %39
    store ptr %40, ptr %15
    %41 = call @func.131(%15, %14)
    br bb7(%5, %41)
bb7(%7: u64, %8: bool):
    condbr %8, bb8(%7), bb9(%7)
bb8(%9: u64):
    br bb12(%9)
bb9(%10: u64):
    %42 = const u64 1
    %43, %44 = add.overflow u64 %10, %42
    store u64 %43, ptr %16
    %45 = const i64 8
    %46 = gep i8, ptr %16, %45
    store bool %44, ptr %46
    %47 = const i64 8
    %48 = gep i8, ptr %16, %47
    %49 = load bool, ptr %48
    %50 = const bool false
    %51 = icmp eq bool %49, %50
    condbr %51, bb10, bb13
bb10:
    %52 = load u64, ptr %16
    br bb4(%52)
bb11:
    %53 = const u64 0
    br bb12(%53)
bb12(%11: u64):
    ret %11
bb13:
    unreachable
}

fn @remap_residual_index_bvars_for_minor(functy.133) {
bb0(%0: ptr, %1: ptr, %2: u64, %3: u64, %4: u64, %5: u64):
    %72 = alloca i64, align 8
    %73 = alloca i64, align 8
    %74 = alloca (i64, i64), align 8
    %75 = alloca (i64, i64), align 8
    %76 = alloca (i64, i64), align 8
    %77 = alloca (i64, i64), align 8
    %78 = alloca (i64, i64), align 8
    %79 = alloca (i64, i64), align 8
    %80 = alloca (i64, i64), align 8
    %81 = alloca (i64, i64), align 8
    %82 = alloca (i64, i64), align 8
    %83 = alloca (i64, i64), align 8
    %84 = alloca (i64, i64), align 8
    %85 = alloca (i64, i64), align 8
    %86 = alloca (i64, i64, i64, i64, i64), align 8
    %87 = alloca (i64, i64, i64, i64, i64), align 8
    %88 = alloca (i64, i64, i64, i64, i64), align 8
    store ptr %1, ptr %72
    %89 = const bool false
    %90 = load ptr, ptr %72
    store ptr %90, ptr %73
    %91 = load ptr, ptr %73
    %92 = load i8, ptr %91
    %93 = sext i8 %92 to i64
    switch %93 [ 0: bb3(%2, %3, %4, %5) 4: bb2(%2, %3, %4, %5) default: bb1 ]
bb1:
    %94 = load ptr, ptr %72
    call @func.78(%0, %94)
    br bb27
bb2(%6: u64, %7: u64, %8: u64, %9: u64):
    %95 = load ptr, ptr %73
    %96 = const i64 8
    %97 = gep i8, ptr %95, %96
    %98 = load ptr, ptr %73
    %99 = const i64 16
    %100 = gep i8, ptr %98, %99
    %101 = load ptr, ptr %97
    %102 = const i64 16
    %103 = gep i8, ptr %101, %102
    br bb22(%6, %7, %8, %9, %100, %103)
bb3(%10: u64, %11: u64, %12: u64, %13: u64):
    %104 = load ptr, ptr %73
    %105 = const i64 4
    %106 = gep i8, ptr %104, %105
    %107 = load u32, ptr %106
    %108 = zext u32 %107 to u64
    %109 = icmp ult u64 %108, %13
    condbr %109, bb4(%108), bb5(%10, %11, %12, %13, %108)
bb4(%14: u64):
    br bb20(%14)
bb5(%15: u64, %16: u64, %17: u64, %18: u64, %19: u64):
    %110, %111 = sub.overflow u64 %19, %18
    store u64 %110, ptr %74
    %112 = const i64 8
    %113 = gep i8, ptr %74, %112
    store bool %111, ptr %113
    %114 = const i64 8
    %115 = gep i8, ptr %74, %114
    %116 = load bool, ptr %115
    %117 = const bool false
    %118 = icmp eq bool %116, %117
    condbr %118, bb6(%15, %16, %17, %18), bb28
bb6(%20: u64, %21: u64, %22: u64, %23: u64):
    %119 = load u64, ptr %74
    %120 = icmp ult u64 %119, %20
    condbr %120, bb7(%20, %21, %22, %23, %119), bb14(%20, %21, %22, %23, %119)
bb7(%24: u64, %25: u64, %26: u64, %27: u64, %28: u64):
    %121 = const u64 1
    %122, %123 = sub.overflow u64 %24, %121
    store u64 %122, ptr %75
    %124 = const i64 8
    %125 = gep i8, ptr %75, %124
    store bool %123, ptr %125
    %126 = const i64 8
    %127 = gep i8, ptr %75, %126
    %128 = load bool, ptr %127
    %129 = const bool false
    %130 = icmp eq bool %128, %129
    condbr %130, bb8(%25, %26, %27, %28), bb28
bb8(%29: u64, %30: u64, %31: u64, %32: u64):
    %131 = load u64, ptr %75
    %132, %133 = sub.overflow u64 %131, %32
    store u64 %132, ptr %76
    %134 = const i64 8
    %135 = gep i8, ptr %76, %134
    store bool %133, ptr %135
    %136 = const i64 8
    %137 = gep i8, ptr %76, %136
    %138 = load bool, ptr %137
    %139 = const bool false
    %140 = icmp eq bool %138, %139
    condbr %140, bb9(%29, %30, %31), bb28
bb9(%33: u64, %34: u64, %35: u64):
    %141 = load u64, ptr %76
    %142, %143 = add.overflow u64 %34, %33
    store u64 %142, ptr %77
    %144 = const i64 8
    %145 = gep i8, ptr %77, %144
    store bool %143, ptr %145
    %146 = const i64 8
    %147 = gep i8, ptr %77, %146
    %148 = load bool, ptr %147
    %149 = const bool false
    %150 = icmp eq bool %148, %149
    condbr %150, bb10(%35, %141), bb28
bb10(%36: u64, %37: u64):
    %151 = load u64, ptr %77
    %152 = const u64 1
    %153, %154 = sub.overflow u64 %151, %152
    store u64 %153, ptr %78
    %155 = const i64 8
    %156 = gep i8, ptr %78, %155
    store bool %154, ptr %156
    %157 = const i64 8
    %158 = gep i8, ptr %78, %157
    %159 = load bool, ptr %158
    %160 = const bool false
    %161 = icmp eq bool %159, %160
    condbr %161, bb11(%36, %37), bb28
bb11(%38: u64, %39: u64):
    %162 = load u64, ptr %78
    %163, %164 = sub.overflow u64 %162, %39
    store u64 %163, ptr %79
    %165 = const i64 8
    %166 = gep i8, ptr %79, %165
    store bool %164, ptr %166
    %167 = const i64 8
    %168 = gep i8, ptr %79, %167
    %169 = load bool, ptr %168
    %170 = const bool false
    %171 = icmp eq bool %169, %170
    condbr %171, bb12(%38), bb28
bb12(%40: u64):
    %172 = load u64, ptr %79
    %173, %174 = add.overflow u64 %172, %40
    store u64 %173, ptr %80
    %175 = const i64 8
    %176 = gep i8, ptr %80, %175
    store bool %174, ptr %176
    %177 = const i64 8
    %178 = gep i8, ptr %80, %177
    %179 = load bool, ptr %178
    %180 = const bool false
    %181 = icmp eq bool %179, %180
    condbr %181, bb13, bb28
bb13:
    %182 = load u64, ptr %80
    br bb20(%182)
bb14(%41: u64, %42: u64, %43: u64, %44: u64, %45: u64):
    %183, %184 = sub.overflow u64 %45, %41
    store u64 %183, ptr %81
    %185 = const i64 8
    %186 = gep i8, ptr %81, %185
    store bool %184, ptr %186
    %187 = const i64 8
    %188 = gep i8, ptr %81, %187
    %189 = load bool, ptr %188
    %190 = const bool false
    %191 = icmp eq bool %189, %190
    condbr %191, bb15(%42, %43, %44), bb28
bb15(%46: u64, %47: u64, %48: u64):
    %192 = load u64, ptr %81
    %193, %194 = add.overflow u64 %47, %46
    store u64 %193, ptr %82
    %195 = const i64 8
    %196 = gep i8, ptr %82, %195
    store bool %194, ptr %196
    %197 = const i64 8
    %198 = gep i8, ptr %82, %197
    %199 = load bool, ptr %198
    %200 = const bool false
    %201 = icmp eq bool %199, %200
    condbr %201, bb16(%48, %192), bb28
bb16(%49: u64, %50: u64):
    %202 = load u64, ptr %82
    %203 = const u64 1
    %204, %205 = add.overflow u64 %202, %203
    store u64 %204, ptr %83
    %206 = const i64 8
    %207 = gep i8, ptr %83, %206
    store bool %205, ptr %207
    %208 = const i64 8
    %209 = gep i8, ptr %83, %208
    %210 = load bool, ptr %209
    %211 = const bool false
    %212 = icmp eq bool %210, %211
    condbr %212, bb17(%49, %50), bb28
bb17(%51: u64, %52: u64):
    %213 = load u64, ptr %83
    %214, %215 = add.overflow u64 %213, %52
    store u64 %214, ptr %84
    %216 = const i64 8
    %217 = gep i8, ptr %84, %216
    store bool %215, ptr %217
    %218 = const i64 8
    %219 = gep i8, ptr %84, %218
    %220 = load bool, ptr %219
    %221 = const bool false
    %222 = icmp eq bool %220, %221
    condbr %222, bb18(%51), bb28
bb18(%53: u64):
    %223 = load u64, ptr %84
    %224, %225 = add.overflow u64 %223, %53
    store u64 %224, ptr %85
    %226 = const i64 8
    %227 = gep i8, ptr %85, %226
    store bool %225, ptr %227
    %228 = const i64 8
    %229 = gep i8, ptr %85, %228
    %230 = load bool, ptr %229
    %231 = const bool false
    %232 = icmp eq bool %230, %231
    condbr %232, bb19, bb28
bb19:
    %233 = load u64, ptr %85
    br bb20(%233)
bb20(%54: u64):
    %234 = call @func.103(%54)
    br bb21(%234)
bb21(%55: u32):
    call @func.83(%0, %55)
    br bb27
bb22(%56: u64, %57: u64, %58: u64, %59: u64, %60: ptr, %61: ptr):
    %235 = const bool true
    call @func.133(%86, %61, %56, %57, %58, %59)
    br bb23(%56, %57, %58, %59, %60)
bb23(%62: u64, %63: u64, %64: u64, %65: u64, %66: ptr):
    %236 = load ptr, ptr %66
    %237 = const i64 16
    %238 = gep i8, ptr %236, %237
    br bb24(%62, %63, %64, %65, %238)
bb24(%67: u64, %68: u64, %69: u64, %70: u64, %71: ptr):
    call @func.133(%87, %71, %67, %68, %69, %70)
    br bb25
bb25:
    %239 = const bool false
    %240 = load i64, ptr %86
    store i64 %240, ptr %88
    %241 = const i64 8
    %242 = gep i8, ptr %86, %241
    %243 = const i64 8
    %244 = gep i8, ptr %88, %243
    %245 = load i64, ptr %242
    store i64 %245, ptr %244
    %246 = const i64 16
    %247 = gep i8, ptr %86, %246
    %248 = const i64 16
    %249 = gep i8, ptr %88, %248
    %250 = load i64, ptr %247
    store i64 %250, ptr %249
    %251 = const i64 24
    %252 = gep i8, ptr %86, %251
    %253 = const i64 24
    %254 = gep i8, ptr %88, %253
    %255 = load i64, ptr %252
    store i64 %255, ptr %254
    %256 = const i64 32
    %257 = gep i8, ptr %86, %256
    %258 = const i64 32
    %259 = gep i8, ptr %88, %258
    %260 = load i64, ptr %257
    store i64 %260, ptr %259
    call @func.84(%0, %88, %87)
    br bb26
bb26:
    %261 = const bool false
    br bb27
bb27:
    ret
bb28:
    unreachable
}

fn @Expr__lift_at(functy.134) {
bb0(%0: ptr, %1: ptr, %2: u32, %3: u32):
    %58 = alloca i64, align 8
    %59 = alloca i64, align 8
    %60 = alloca (i64, i64, i64, i64, i64), align 8
    %61 = alloca (i64, i64, i64, i64, i64), align 8
    %62 = alloca (i8, i8), align 1
    %63 = alloca (i64, i64, i64, i64, i64), align 8
    %64 = alloca (i64, i64, i64, i64, i64), align 8
    %65 = alloca (i8, i8), align 1
    %66 = alloca (i64, i64, i64, i64, i64), align 8
    %67 = alloca (i64, i64, i64, i64, i64), align 8
    store ptr %1, ptr %58
    %68 = const bool false
    %69 = const bool false
    %70 = const bool false
    %71 = const u32 0
    %72 = icmp eq u32 %3, %71
    condbr %72, bb1, bb2(%2, %3)
bb1:
    %73 = load ptr, ptr %58
    call @func.78(%0, %73)
    br bb31
bb2(%4: u32, %5: u32):
    %74 = load ptr, ptr %58
    %75 = call @func.172(%74)
    br bb3(%4, %5, %75)
bb3(%6: u32, %7: u32, %8: u32):
    %76 = icmp uge u32 %6, %8
    condbr %76, bb4, bb5(%6, %7)
bb4:
    %77 = load ptr, ptr %58
    call @func.78(%0, %77)
    br bb31
bb5(%9: u32, %10: u32):
    %78 = load ptr, ptr %58
    store ptr %78, ptr %59
    %79 = load ptr, ptr %59
    %80 = load i8, ptr %79
    %81 = sext i8 %80 to i64
    switch %81 [ 0: bb10(%9, %10) 4: bb9(%9, %10) 5: bb8(%9, %10) 6: bb7(%9, %10) default: bb6 ]
bb6:
    %82 = load ptr, ptr %58
    call @func.78(%0, %82)
    br bb31
bb7(%11: u32, %12: u32):
    %83 = load ptr, ptr %59
    %84 = const i64 1
    %85 = gep i8, ptr %83, %84
    %86 = load ptr, ptr %59
    %87 = const i64 8
    %88 = gep i8, ptr %86, %87
    %89 = load ptr, ptr %59
    %90 = const i64 16
    %91 = gep i8, ptr %89, %90
    %92 = load i8, ptr %85
    store i8 %92, ptr %65
    %93 = const i64 1
    %94 = gep i8, ptr %85, %93
    %95 = const i64 1
    %96 = gep i8, ptr %65, %95
    %97 = load i8, ptr %94
    store i8 %97, ptr %96
    %98 = load ptr, ptr %88
    %99 = const i64 16
    %100 = gep i8, ptr %98, %99
    br bb25(%11, %12, %91, %100)
bb8(%13: u32, %14: u32):
    %101 = load ptr, ptr %59
    %102 = const i64 1
    %103 = gep i8, ptr %101, %102
    %104 = load ptr, ptr %59
    %105 = const i64 8
    %106 = gep i8, ptr %104, %105
    %107 = load ptr, ptr %59
    %108 = const i64 16
    %109 = gep i8, ptr %107, %108
    %110 = load i8, ptr %103
    store i8 %110, ptr %62
    %111 = const i64 1
    %112 = gep i8, ptr %103, %111
    %113 = const i64 1
    %114 = gep i8, ptr %62, %113
    %115 = load i8, ptr %112
    store i8 %115, ptr %114
    %116 = load ptr, ptr %106
    %117 = const i64 16
    %118 = gep i8, ptr %116, %117
    br bb19(%13, %14, %109, %118)
bb9(%15: u32, %16: u32):
    %119 = load ptr, ptr %59
    %120 = const i64 8
    %121 = gep i8, ptr %119, %120
    %122 = load ptr, ptr %59
    %123 = const i64 16
    %124 = gep i8, ptr %122, %123
    %125 = load ptr, ptr %121
    %126 = const i64 16
    %127 = gep i8, ptr %125, %126
    br bb14(%15, %16, %124, %127)
bb10(%17: u32, %18: u32):
    %128 = load ptr, ptr %59
    %129 = const i64 4
    %130 = gep i8, ptr %128, %129
    %131 = load u32, ptr %130
    %132 = icmp uge u32 %131, %17
    condbr %132, bb11(%18, %130), bb13
bb11(%19: u32, %20: ptr):
    %133 = load u32, ptr %20
    %134 = call @func.174(%133, %19)
    br bb12(%134)
bb12(%21: u32):
    call @func.83(%0, %21)
    br bb31
bb13:
    %135 = load ptr, ptr %58
    call @func.78(%0, %135)
    br bb31
bb14(%22: u32, %23: u32, %24: ptr, %25: ptr):
    %136 = const bool true
    call @func.134(%60, %25, %22, %23)
    br bb15(%22, %23, %24)
bb15(%26: u32, %27: u32, %28: ptr):
    %137 = load ptr, ptr %28
    %138 = const i64 16
    %139 = gep i8, ptr %137, %138
    br bb16(%26, %27, %139)
bb16(%29: u32, %30: u32, %31: ptr):
    call @func.134(%61, %31, %29, %30)
    br bb17
bb17:
    %140 = const bool false
    call @func.84(%0, %60, %61)
    br bb18
bb18:
    %141 = const bool false
    br bb31
bb19(%32: u32, %33: u32, %34: ptr, %35: ptr):
    %142 = const bool true
    call @func.134(%63, %35, %32, %33)
    br bb20(%32, %33, %34)
bb20(%36: u32, %37: u32, %38: ptr):
    %143 = load ptr, ptr %38
    %144 = const i64 16
    %145 = gep i8, ptr %143, %144
    br bb21(%36, %37, %145)
bb21(%39: u32, %40: u32, %41: ptr):
    %146 = const u32 1
    %147 = call @func.174(%39, %146)
    br bb22(%40, %41, %147)
bb22(%42: u32, %43: ptr, %44: u32):
    call @func.134(%64, %43, %44, %42)
    br bb23
bb23:
    %148 = const bool false
    call @func.117(%0, %62, %63, %64)
    br bb24
bb24:
    %149 = const bool false
    br bb31
bb25(%45: u32, %46: u32, %47: ptr, %48: ptr):
    %150 = const bool true
    call @func.134(%66, %48, %45, %46)
    br bb26(%45, %46, %47)
bb26(%49: u32, %50: u32, %51: ptr):
    %151 = load ptr, ptr %51
    %152 = const i64 16
    %153 = gep i8, ptr %151, %152
    br bb27(%49, %50, %153)
bb27(%52: u32, %53: u32, %54: ptr):
    %154 = const u32 1
    %155 = call @func.174(%52, %154)
    br bb28(%53, %54, %155)
bb28(%55: u32, %56: ptr, %57: u32):
    call @func.134(%67, %56, %57, %55)
    br bb29
bb29:
    %156 = const bool false
    call @func.86(%0, %65, %66, %67)
    br bb30
bb30:
    %157 = const bool false
    br bb31
bb31:
    ret
}

fn @Expr__infer_implicit_n(functy.135) {
bb0(%0: ptr, %1: ptr, %2: u32, %3: bool):
    %36 = alloca i64, align 8
    %37 = alloca i64, align 8
    %38 = alloca (i64, i64, i64, i64, i64), align 8
    %39 = alloca (i32, i32), align 4
    %40 = alloca (i8, i8), align 1
    %41 = alloca (i64, i64, i64, i64, i64), align 8
    %42 = alloca (i64, i64, i64, i64, i64), align 8
    %43 = alloca (i8, i8), align 1
    %44 = alloca (i64, i64, i64, i64, i64), align 8
    %45 = alloca (i64, i64, i64, i64, i64), align 8
    %46 = alloca (i8, i8), align 1
    %47 = alloca (i64, i64, i64, i64, i64), align 8
    %48 = alloca (i64, i64, i64, i64, i64), align 8
    store ptr %1, ptr %36
    %49 = const bool false
    %50 = const u32 0
    %51 = icmp eq u32 %2, %50
    condbr %51, bb1, bb2(%2, %3)
bb1:
    %52 = load ptr, ptr %36
    call @func.78(%0, %52)
    br bb21
bb2(%4: u32, %5: bool):
    %53 = load ptr, ptr %36
    store ptr %53, ptr %37
    %54 = load ptr, ptr %37
    %55 = load i8, ptr %54
    %56 = sext i8 %55 to i64
    switch %56 [ 6: bb4(%4, %5) default: bb3 ]
bb3:
    %57 = load ptr, ptr %36
    call @func.78(%0, %57)
    br bb21
bb4(%6: u32, %7: bool):
    %58 = load ptr, ptr %37
    %59 = const i64 1
    %60 = gep i8, ptr %58, %59
    %61 = load ptr, ptr %37
    %62 = const i64 8
    %63 = gep i8, ptr %61, %62
    %64 = load ptr, ptr %37
    %65 = const i64 16
    %66 = gep i8, ptr %64, %65
    %67 = load ptr, ptr %66
    %68 = const i64 16
    %69 = gep i8, ptr %67, %68
    br bb5(%6, %7, %60, %63, %69)
bb5(%8: u32, %9: bool, %10: ptr, %11: ptr, %12: ptr):
    %70 = const u32 1
    %71, %72 = sub.overflow u32 %8, %70
    store u32 %71, ptr %39
    %73 = const i64 4
    %74 = gep i8, ptr %39, %73
    store bool %72, ptr %74
    %75 = const i64 4
    %76 = gep i8, ptr %39, %75
    %77 = load bool, ptr %76
    %78 = const bool false
    %79 = icmp eq bool %77, %78
    condbr %79, bb6(%9, %10, %11, %12), bb25
bb6(%13: bool, %14: ptr, %15: ptr, %16: ptr):
    %80 = load u32, ptr %39
    %81 = const bool true
    call @func.135(%38, %16, %80, %13)
    br bb7(%13, %14, %15)
bb7(%17: bool, %18: ptr, %19: ptr):
    %82 = load u8, ptr %18
    %83 = const u8 0
    %84 = icmp ne u8 %82, %83
    condbr %84, bb8(%18, %19), bb11(%17, %18, %19)
bb8(%20: ptr, %21: ptr):
    %85 = load i8, ptr %20
    store i8 %85, ptr %40
    %86 = const i64 1
    %87 = gep i8, ptr %20, %86
    %88 = const i64 1
    %89 = gep i8, ptr %40, %88
    %90 = load i8, ptr %87
    store i8 %90, ptr %89
    %91 = load ptr, ptr %21
    %92 = const i64 16
    %93 = gep i8, ptr %91, %92
    br bb9(%93)
bb9(%22: ptr):
    call @func.78(%41, %22)
    br bb10
bb10:
    %94 = const bool false
    %95 = load i64, ptr %38
    store i64 %95, ptr %42
    %96 = const i64 8
    %97 = gep i8, ptr %38, %96
    %98 = const i64 8
    %99 = gep i8, ptr %42, %98
    %100 = load i64, ptr %97
    store i64 %100, ptr %99
    %101 = const i64 16
    %102 = gep i8, ptr %38, %101
    %103 = const i64 16
    %104 = gep i8, ptr %42, %103
    %105 = load i64, ptr %102
    store i64 %105, ptr %104
    %106 = const i64 24
    %107 = gep i8, ptr %38, %106
    %108 = const i64 24
    %109 = gep i8, ptr %42, %108
    %110 = load i64, ptr %107
    store i64 %110, ptr %109
    %111 = const i64 32
    %112 = gep i8, ptr %38, %111
    %113 = const i64 32
    %114 = gep i8, ptr %42, %113
    %115 = load i64, ptr %112
    store i64 %115, ptr %114
    call @func.86(%0, %40, %41, %42)
    br bb22
bb11(%23: bool, %24: ptr, %25: ptr):
    %116 = const u32 0
    %117 = call @func.175(%38, %116, %23)
    br bb12(%24, %25, %117)
bb12(%26: ptr, %27: ptr, %28: bool):
    condbr %28, bb13(%26, %27), bb17(%26, %27)
bb13(%29: ptr, %30: ptr):
    %118 = const i64 1
    %119 = gep i8, ptr %29, %118
    %120 = load u8, ptr %119
    %121 = const u8 1
    call @func.176(%43, %121, %120)
    br bb14(%30)
bb14(%31: ptr):
    %122 = load ptr, ptr %31
    %123 = const i64 16
    %124 = gep i8, ptr %122, %123
    br bb15(%124)
bb15(%32: ptr):
    call @func.78(%44, %32)
    br bb16
bb16:
    %125 = const bool false
    %126 = load i64, ptr %38
    store i64 %126, ptr %45
    %127 = const i64 8
    %128 = gep i8, ptr %38, %127
    %129 = const i64 8
    %130 = gep i8, ptr %45, %129
    %131 = load i64, ptr %128
    store i64 %131, ptr %130
    %132 = const i64 16
    %133 = gep i8, ptr %38, %132
    %134 = const i64 16
    %135 = gep i8, ptr %45, %134
    %136 = load i64, ptr %133
    store i64 %136, ptr %135
    %137 = const i64 24
    %138 = gep i8, ptr %38, %137
    %139 = const i64 24
    %140 = gep i8, ptr %45, %139
    %141 = load i64, ptr %138
    store i64 %141, ptr %140
    %142 = const i64 32
    %143 = gep i8, ptr %38, %142
    %144 = const i64 32
    %145 = gep i8, ptr %45, %144
    %146 = load i64, ptr %143
    store i64 %146, ptr %145
    call @func.86(%0, %43, %44, %45)
    br bb23
bb17(%33: ptr, %34: ptr):
    %147 = load i8, ptr %33
    store i8 %147, ptr %46
    %148 = const i64 1
    %149 = gep i8, ptr %33, %148
    %150 = const i64 1
    %151 = gep i8, ptr %46, %150
    %152 = load i8, ptr %149
    store i8 %152, ptr %151
    %153 = load ptr, ptr %34
    %154 = const i64 16
    %155 = gep i8, ptr %153, %154
    br bb18(%155)
bb18(%35: ptr):
    call @func.78(%47, %35)
    br bb19
bb19:
    %156 = const bool false
    %157 = load i64, ptr %38
    store i64 %157, ptr %48
    %158 = const i64 8
    %159 = gep i8, ptr %38, %158
    %160 = const i64 8
    %161 = gep i8, ptr %48, %160
    %162 = load i64, ptr %159
    store i64 %162, ptr %161
    %163 = const i64 16
    %164 = gep i8, ptr %38, %163
    %165 = const i64 16
    %166 = gep i8, ptr %48, %165
    %167 = load i64, ptr %164
    store i64 %167, ptr %166
    %168 = const i64 24
    %169 = gep i8, ptr %38, %168
    %170 = const i64 24
    %171 = gep i8, ptr %48, %170
    %172 = load i64, ptr %169
    store i64 %172, ptr %171
    %173 = const i64 32
    %174 = gep i8, ptr %38, %173
    %175 = const i64 32
    %176 = gep i8, ptr %48, %175
    %177 = load i64, ptr %174
    store i64 %177, ptr %176
    call @func.86(%0, %46, %47, %48)
    br bb24
bb20:
    %178 = const bool false
    br bb21
bb21:
    ret
bb22:
    br bb20
bb23:
    br bb20
bb24:
    br bb20
bb25:
    unreachable
}

fn @_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCs6RT0DENTjyC_27clean_mutual_recursor_slice4NameNtB7_9PartialEq2eqBF_(functy.136) {
}

fn @name_in_set(functy.137) {
bb0(%0: ptr, %1: ptr):
    %10 = alloca i64, align 8
    %11 = alloca i64, align 8
    %12 = alloca (i64, i64), align 8
    store ptr %0, ptr %10
    %13 = const u64 0
    br bb1(%13)
bb1(%2: u64):
    %14 = const i64 8
    %15 = gep i8, ptr %1, %14
    %16 = load u64, ptr %15
    %17 = icmp ult u64 %2, %16
    condbr %17, bb2(%2), bb8
bb2(%3: u64):
    %18 = const i64 8
    %19 = gep i8, ptr %1, %18
    %20 = load u64, ptr %19
    %21 = icmp ult u64 %3, %20
    condbr %21, bb3(%3, %3), bb10
bb3(%4: u64, %5: u64):
    %22 = load ptr, ptr %1
    %23 = const u64 4
    %24 = mul u64 %5, %23
    %25 = gep i8, ptr %22, %24
    store ptr %25, ptr %11
    %26 = call @func.136(%11, %10)
    br bb4(%4, %26)
bb4(%6: u64, %7: bool):
    condbr %7, bb5, bb6(%6)
bb5:
    %27 = const bool true
    br bb9(%27)
bb6(%8: u64):
    %28 = const u64 1
    %29, %30 = add.overflow u64 %8, %28
    store u64 %29, ptr %12
    %31 = const i64 8
    %32 = gep i8, ptr %12, %31
    store bool %30, ptr %32
    %33 = const i64 8
    %34 = gep i8, ptr %12, %33
    %35 = load bool, ptr %34
    %36 = const bool false
    %37 = icmp eq bool %35, %36
    condbr %37, bb7, bb10
bb7:
    %38 = load u64, ptr %12
    br bb1(%38)
bb8:
    %39 = const bool false
    br bb9(%39)
bb9(%9: bool):
    ret %9
bb10:
    unreachable
}

fn @_Literal_as_std__clone__Clone___clone(functy.138) {
bb0(%0: ptr, %1: ptr):
    %2 = alloca i64, align 8
    store ptr %1, ptr %2
    %3 = load ptr, ptr %2
    %4 = load i32, ptr %3
    %5 = sext i32 %4 to i64
    switch %5 [ 0: bb3 1: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %6 = load ptr, ptr %2
    %7 = const i64 4
    %8 = gep i8, ptr %6, %7
    %9 = load u32, ptr %8
    %10 = const i64 4
    %11 = gep i8, ptr %0, %10
    store u32 %9, ptr %11
    %12 = const i32 1
    store i32 %12, ptr %0
    br bb4
bb3:
    %13 = load ptr, ptr %2
    %14 = const i64 8
    %15 = gep i8, ptr %13, %14
    %16 = load u64, ptr %15
    %17 = const i64 8
    %18 = gep i8, ptr %0, %17
    store u64 %16, ptr %18
    %19 = const i32 0
    store i32 %19, ptr %0
    br bb4
bb4:
    ret
}

fn @_BinderData_as_std__clone__Clone___clone(functy.139) {
bb0(%0: ptr, %1: ptr):
    %2 = load i8, ptr %1
    store i8 %2, ptr %0
    %3 = const i64 1
    %4 = gep i8, ptr %1, %3
    %5 = const i64 1
    %6 = gep i8, ptr %0, %5
    %7 = load i8, ptr %4
    store i8 %7, ptr %6
    ret
}

fn @_FVarId_as_std__clone__Clone___clone(functy.140) {
bb0(%0: ptr, %1: ptr):
    %2 = load i64, ptr %1
    store i64 %2, ptr %0
    ret
}

fn @hash_lit(functy.141) {
bb0(%0: ptr):
    %3 = alloca i64, align 8
    call @func.177(%3)
    br bb1(%0)
bb1(%1: ptr):
    call @func.181(%1, %3)
    br bb2
bb2:
    %4 = call @func.182(%3)
    br bb3(%4)
bb3(%2: u64):
    ret %2
}

fn @_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_mul(functy.142) {
}

fn @mix_hash(functy.143) {
bb0(%0: u64, %1: u64):
    %8 = const u64 14313749767032793493
    %9 = call @func.142(%1, %8)
    br bb1(%0, %9)
bb1(%2: u64, %3: u64):
    %10 = const u32 47
    %11 = const u32 64
    %12 = icmp ult u32 %10, %11
    condbr %12, bb2(%2, %3, %3), bb4
bb2(%4: u64, %5: u64, %6: u64):
    %13 = const u32 47
    %14 = zext u32 %13 to u64
    %15 = lshr u64 %6, %14
    %16 = xor u64 %5, %15
    %17 = const u64 14313749767032793493
    %18 = xor u64 %16, %17
    %19 = xor u64 %4, %18
    %20 = const u64 14313749767032793493
    %21 = call @func.142(%19, %20)
    br bb3(%21)
bb3(%7: u64):
    ret %7
bb4:
    unreachable
}

fn @hash_name(functy.144) {
bb0(%0: ptr):
    %3 = alloca i64, align 8
    call @func.177(%3)
    br bb1(%0)
bb1(%1: ptr):
    call @func.184(%1, %3)
    br bb2
bb2:
    %4 = call @func.182(%3)
    br bb3(%4)
bb3(%2: u64):
    ret %2
}

fn @hash_level(functy.145) {
bb0(%0: ptr):
    %3 = alloca i64, align 8
    call @func.177(%3)
    br bb1(%0)
bb1(%1: ptr):
    call @func.187(%1, %3)
    br bb2
bb2:
    %4 = call @func.182(%3)
    br bb3(%4)
bb3(%2: u64):
    ret %2
}

fn @_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3minCs6RT0DENTjyC_27clean_mutual_recursor_slice(functy.146) {
}

fn @ExprMeta__pack(functy.147) {
bb0(%0: ptr, %1: u32, %2: u32, %3: u32, %4: bool, %5: bool, %6: bool, %7: bool):
    %42 = const u32 255
    %43 = call @func.146(%3, %42)
    br bb1(%1, %2, %4, %5, %6, %7, %43)
bb1(%8: u32, %9: u32, %10: bool, %11: bool, %12: bool, %13: bool, %14: u32):
    %44 = zext u32 %8 to u64
    %45 = zext u32 %14 to u64
    %46 = const u32 32
    %47 = const u32 64
    %48 = icmp ult u32 %46, %47
    condbr %48, bb2(%9, %10, %11, %12, %13, %44, %45), bb8
bb2(%15: u32, %16: bool, %17: bool, %18: bool, %19: bool, %20: u64, %21: u64):
    %49 = const u32 32
    %50 = zext u32 %49 to u64
    %51 = shl u64 %21, %50
    %52 = or u64 %20, %51
    %53 = const u64 1
    %54 = const u64 0
    %55 = select u64 %16, %53, %54
    %56 = const u32 40
    %57 = const u32 64
    %58 = icmp ult u32 %56, %57
    condbr %58, bb3(%15, %17, %18, %19, %52, %55), bb8
bb3(%22: u32, %23: bool, %24: bool, %25: bool, %26: u64, %27: u64):
    %59 = const u32 40
    %60 = zext u32 %59 to u64
    %61 = shl u64 %27, %60
    %62 = or u64 %26, %61
    %63 = const u64 1
    %64 = const u64 0
    %65 = select u64 %23, %63, %64
    %66 = const u32 41
    %67 = const u32 64
    %68 = icmp ult u32 %66, %67
    condbr %68, bb4(%22, %24, %25, %62, %65), bb8
bb4(%28: u32, %29: bool, %30: bool, %31: u64, %32: u64):
    %69 = const u32 41
    %70 = zext u32 %69 to u64
    %71 = shl u64 %32, %70
    %72 = or u64 %31, %71
    %73 = const u64 1
    %74 = const u64 0
    %75 = select u64 %29, %73, %74
    %76 = const u32 42
    %77 = const u32 64
    %78 = icmp ult u32 %76, %77
    condbr %78, bb5(%28, %30, %72, %75), bb8
bb5(%33: u32, %34: bool, %35: u64, %36: u64):
    %79 = const u32 42
    %80 = zext u32 %79 to u64
    %81 = shl u64 %36, %80
    %82 = or u64 %35, %81
    %83 = const u64 1
    %84 = const u64 0
    %85 = select u64 %34, %83, %84
    %86 = const u32 43
    %87 = const u32 64
    %88 = icmp ult u32 %86, %87
    condbr %88, bb6(%33, %82, %85), bb8
bb6(%37: u32, %38: u64, %39: u64):
    %89 = const u32 43
    %90 = zext u32 %89 to u64
    %91 = shl u64 %39, %90
    %92 = or u64 %38, %91
    %93 = zext u32 %37 to u64
    %94 = const u32 44
    %95 = const u32 64
    %96 = icmp ult u32 %94, %95
    condbr %96, bb7(%92, %93), bb8
bb7(%40: u64, %41: u64):
    %97 = const u32 44
    %98 = zext u32 %97 to u64
    %99 = shl u64 %41, %98
    %100 = or u64 %40, %99
    store u64 %100, ptr %0
    ret
bb8:
    unreachable
}

fn @Expr__meta(functy.148) {
bb0(%0: ptr, %1: ptr):
    %2 = const i64 32
    %3 = gep i8, ptr %1, %2
    %4 = load i64, ptr %3
    store i64 %4, ptr %0
    ret
}

fn @_RNvYhNtNtCs2EYQwhfuABO_4core3cmp3Ord3maxCs6RT0DENTjyC_27clean_mutual_recursor_slice(functy.149) {
}

fn @_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3minCs6RT0DENTjyC_27clean_mutual_recursor_slice(functy.150) {
}

fn @_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3maxCs6RT0DENTjyC_27clean_mutual_recursor_slice(functy.151) {
}

fn @ExprMeta__mk_app_meta(functy.152) {
bb0(%0: ptr, %1: u64, %2: u64):
    %28 = alloca i64, align 8
    %29 = alloca i64, align 8
    %30 = alloca (i32, i32), align 4
    store u64 %1, ptr %28
    store u64 %2, ptr %29
    %31 = load u64, ptr %28
    %32 = call @func.165(%31)
    br bb1(%32)
bb1(%3: u8):
    %33 = load u64, ptr %29
    %34 = call @func.165(%33)
    br bb2(%3, %34)
bb2(%4: u8, %5: u8):
    %35 = call @func.149(%4, %5)
    br bb3(%35)
bb3(%6: u8):
    %36 = zext u8 %6 to u32
    %37 = const u32 1
    %38, %39 = add.overflow u32 %36, %37
    store u32 %38, ptr %30
    %40 = const i64 4
    %41 = gep i8, ptr %30, %40
    store bool %39, ptr %41
    %42 = const i64 4
    %43 = gep i8, ptr %30, %42
    %44 = load bool, ptr %43
    %45 = const bool false
    %46 = icmp eq bool %44, %45
    condbr %46, bb4, bb13
bb4:
    %47 = load u32, ptr %30
    %48 = const u32 255
    %49 = call @func.150(%47, %48)
    br bb5(%49)
bb5(%7: u32):
    %50 = load u64, ptr %28
    %51 = call @func.167(%50)
    br bb6(%7, %51)
bb6(%8: u32, %9: u32):
    %52 = load u64, ptr %29
    %53 = call @func.167(%52)
    br bb7(%8, %9, %53)
bb7(%10: u32, %11: u32, %12: u32):
    %54 = call @func.151(%11, %12)
    br bb8(%10, %54)
bb8(%13: u32, %14: u32):
    %55 = load u64, ptr %28
    %56 = load u64, ptr %29
    %57 = call @func.143(%55, %56)
    br bb9(%13, %14, %57)
bb9(%15: u32, %16: u32, %17: u64):
    %58 = trunc u64 %17 to u32
    %59 = load u64, ptr %28
    %60 = load u64, ptr %29
    %61 = or u64 %59, %60
    %62 = const u32 40
    %63 = const u32 64
    %64 = icmp ult u32 %62, %63
    condbr %64, bb10(%15, %16, %58, %61), bb13
bb10(%18: u32, %19: u32, %20: u32, %21: u64):
    %65 = const u64 15
    %66 = const u32 40
    %67 = zext u32 %66 to u64
    %68 = shl u64 %65, %67
    %69 = and u64 %21, %68
    %70 = zext u32 %20 to u64
    %71 = zext u32 %18 to u64
    %72 = const u32 32
    %73 = const u32 64
    %74 = icmp ult u32 %72, %73
    condbr %74, bb11(%19, %69, %70, %71), bb13
bb11(%22: u32, %23: u64, %24: u64, %25: u64):
    %75 = const u32 32
    %76 = zext u32 %75 to u64
    %77 = shl u64 %25, %76
    %78 = or u64 %24, %77
    %79 = or u64 %78, %23
    %80 = zext u32 %22 to u64
    %81 = const u32 44
    %82 = const u32 64
    %83 = icmp ult u32 %81, %82
    condbr %83, bb12(%79, %80), bb13
bb12(%26: u64, %27: u64):
    %84 = const u32 44
    %85 = zext u32 %84 to u64
    %86 = shl u64 %27, %85
    %87 = or u64 %26, %86
    store u64 %87, ptr %0
    ret
bb13:
    unreachable
}

fn @_RNvYhNtNtCs2EYQwhfuABO_4core3cmp3Ord3maxCs6RT0DENTjyC_27clean_mutual_recursor_slice(functy.153) {
}

fn @_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3minCs6RT0DENTjyC_27clean_mutual_recursor_slice(functy.154) {
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm14saturating_sub(functy.155) {
}

fn @_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3maxCs6RT0DENTjyC_27clean_mutual_recursor_slice(functy.156) {
}

fn @ExprMeta__mk_binder_meta(functy.157) {
bb0(%0: ptr, %1: u64, %2: u64, %3: u64):
    %130 = alloca i64, align 8
    %131 = alloca i64, align 8
    %132 = alloca (i32, i32), align 4
    store u64 %1, ptr %130
    store u64 %2, ptr %131
    %133 = load u64, ptr %130
    %134 = call @func.165(%133)
    br bb1(%3, %134)
bb1(%4: u64, %5: u8):
    %135 = load u64, ptr %131
    %136 = call @func.165(%135)
    br bb2(%4, %5, %136)
bb2(%6: u64, %7: u8, %8: u8):
    %137 = call @func.153(%7, %8)
    br bb3(%6, %137)
bb3(%9: u64, %10: u8):
    %138 = zext u8 %10 to u32
    %139 = const u32 1
    %140, %141 = add.overflow u32 %138, %139
    store u32 %140, ptr %132
    %142 = const i64 4
    %143 = gep i8, ptr %132, %142
    store bool %141, ptr %143
    %144 = const i64 4
    %145 = gep i8, ptr %132, %144
    %146 = load bool, ptr %145
    %147 = const bool false
    %148 = icmp eq bool %146, %147
    condbr %148, bb4(%9), bb32
bb4(%11: u64):
    %149 = load u32, ptr %132
    %150 = const u32 255
    %151 = call @func.154(%149, %150)
    br bb5(%11, %151)
bb5(%12: u64, %13: u32):
    %152 = load u64, ptr %131
    %153 = call @func.167(%152)
    br bb6(%12, %13, %153)
bb6(%14: u64, %15: u32, %16: u32):
    %154 = const u32 1
    %155 = call @func.155(%16, %154)
    br bb7(%14, %15, %155)
bb7(%17: u64, %18: u32, %19: u32):
    %156 = load u64, ptr %130
    %157 = call @func.167(%156)
    br bb8(%17, %18, %19, %157)
bb8(%20: u64, %21: u32, %22: u32, %23: u32):
    %158 = call @func.156(%23, %22)
    br bb9(%20, %21, %158)
bb9(%24: u64, %25: u32, %26: u32):
    %159 = zext u32 %25 to u64
    %160 = load u64, ptr %130
    %161 = call @func.166(%160)
    br bb10(%24, %25, %26, %159, %161)
bb10(%27: u64, %28: u32, %29: u32, %30: u64, %31: u32):
    %162 = zext u32 %31 to u64
    %163 = load u64, ptr %131
    %164 = call @func.166(%163)
    br bb11(%27, %28, %29, %30, %162, %164)
bb11(%32: u64, %33: u32, %34: u32, %35: u64, %36: u64, %37: u32):
    %165 = zext u32 %37 to u64
    %166 = call @func.143(%165, %32)
    br bb12(%33, %34, %35, %36, %166)
bb12(%38: u32, %39: u32, %40: u64, %41: u64, %42: u64):
    %167 = call @func.143(%41, %42)
    br bb13(%38, %39, %40, %167)
bb13(%43: u32, %44: u32, %45: u64, %46: u64):
    %168 = call @func.143(%45, %46)
    br bb14(%43, %44, %168)
bb14(%47: u32, %48: u32, %49: u64):
    %169 = trunc u64 %49 to u32
    %170 = load u64, ptr %130
    %171 = call @func.168(%170)
    br bb15(%47, %48, %169, %171)
bb15(%50: u32, %51: u32, %52: u32, %53: bool):
    condbr %53, bb16(%50, %51, %52), bb17(%50, %51, %52)
bb16(%54: u32, %55: u32, %56: u32):
    %172 = const bool true
    br bb18(%54, %55, %56, %172)
bb17(%57: u32, %58: u32, %59: u32):
    %173 = load u64, ptr %131
    %174 = call @func.168(%173)
    br bb18(%57, %58, %59, %174)
bb18(%60: u32, %61: u32, %62: u32, %63: bool):
    %175 = load u64, ptr %130
    %176 = call @func.169(%175)
    br bb19(%60, %61, %62, %63, %176)
bb19(%64: u32, %65: u32, %66: u32, %67: bool, %68: bool):
    condbr %68, bb20(%64, %65, %66, %67), bb21(%64, %65, %66, %67)
bb20(%69: u32, %70: u32, %71: u32, %72: bool):
    %177 = const bool true
    br bb22(%69, %70, %71, %72, %177)
bb21(%73: u32, %74: u32, %75: u32, %76: bool):
    %178 = load u64, ptr %131
    %179 = call @func.169(%178)
    br bb22(%73, %74, %75, %76, %179)
bb22(%77: u32, %78: u32, %79: u32, %80: bool, %81: bool):
    %180 = load u64, ptr %130
    %181 = call @func.170(%180)
    br bb23(%77, %78, %79, %80, %81, %181)
bb23(%82: u32, %83: u32, %84: u32, %85: bool, %86: bool, %87: bool):
    condbr %87, bb24(%82, %83, %84, %85, %86), bb25(%82, %83, %84, %85, %86)
bb24(%88: u32, %89: u32, %90: u32, %91: bool, %92: bool):
    %182 = const bool true
    br bb26(%88, %89, %90, %91, %92, %182)
bb25(%93: u32, %94: u32, %95: u32, %96: bool, %97: bool):
    %183 = load u64, ptr %131
    %184 = call @func.170(%183)
    br bb26(%93, %94, %95, %96, %97, %184)
bb26(%98: u32, %99: u32, %100: u32, %101: bool, %102: bool, %103: bool):
    %185 = load u64, ptr %130
    %186 = call @func.171(%185)
    br bb27(%98, %99, %100, %101, %102, %103, %186)
bb27(%104: u32, %105: u32, %106: u32, %107: bool, %108: bool, %109: bool, %110: bool):
    condbr %110, bb28(%104, %105, %106, %107, %108, %109), bb29(%104, %105, %106, %107, %108, %109)
bb28(%111: u32, %112: u32, %113: u32, %114: bool, %115: bool, %116: bool):
    %187 = const bool true
    br bb30(%111, %112, %113, %114, %115, %116, %187)
bb29(%117: u32, %118: u32, %119: u32, %120: bool, %121: bool, %122: bool):
    %188 = load u64, ptr %131
    %189 = call @func.171(%188)
    br bb30(%117, %118, %119, %120, %121, %122, %189)
bb30(%123: u32, %124: u32, %125: u32, %126: bool, %127: bool, %128: bool, %129: bool):
    call @func.147(%0, %125, %124, %123, %126, %127, %128, %129)
    br bb31
bb31:
    ret
bb32:
    unreachable
}

fn @level_has_mvar(functy.158) {
bb0(%0: ptr):
    %1 = const bool false
    ret %1
}

fn @Level__has_params(functy.159) {
bb0(%0: ptr):
    %2 = alloca i64, align 8
    %3 = alloca i64, align 8
    %4 = alloca i64, align 8
    store ptr %0, ptr %2
    %5 = load ptr, ptr %2
    %6 = load i32, ptr %5
    %7 = sext i32 %6 to i64
    switch %7 [ 0: bb4 1: bb3 2: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %8 = const bool true
    br bb5(%8)
bb3:
    %9 = load ptr, ptr %2
    %10 = const i64 8
    %11 = gep i8, ptr %9, %10
    %12 = load i64, ptr %11
    store i64 %12, ptr %3
    %13 = load ptr, ptr %3
    store ptr %13, ptr %4
    %14 = load ptr, ptr %4
    %15 = ptrtoint ptr %14 to u64
    %16 = const u64 8
    %17 = const u64 1
    %18 = sub u64 %16, %17
    %19 = and u64 %15, %18
    %20 = const u64 0
    %21 = icmp eq u64 %19, %20
    condbr %21, bb6, bb8
bb4:
    %22 = const bool false
    br bb5(%22)
bb5(%1: bool):
    ret %1
bb6:
    %23 = load ptr, ptr %4
    %24 = ptrtoint ptr %23 to u64
    %25 = const u64 0
    %26 = icmp eq u64 %24, %25
    %27 = const bool true
    %28 = const bool false
    %29 = select bool %26, %27, %28
    %30 = const bool false
    %31 = icmp eq bool %29, %30
    condbr %31, bb7, bb8
bb7:
    %32 = load ptr, ptr %4
    %33 = call @func.159(%32)
    br bb5(%33)
bb8:
    unreachable
}

fn @_RNvYhNtNtCs2EYQwhfuABO_4core3cmp3Ord3maxCs6RT0DENTjyC_27clean_mutual_recursor_slice(functy.160) {
}

fn @_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3minCs6RT0DENTjyC_27clean_mutual_recursor_slice(functy.161) {
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm14saturating_sub(functy.162) {
}

fn @_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3maxCs6RT0DENTjyC_27clean_mutual_recursor_slice(functy.163) {
}

fn @ExprMeta__mk_let_meta(functy.164) {
bb0(%0: ptr, %1: u64, %2: u64, %3: u64):
    %175 = alloca i64, align 8
    %176 = alloca i64, align 8
    %177 = alloca i64, align 8
    %178 = alloca (i32, i32), align 4
    store u64 %1, ptr %175
    store u64 %2, ptr %176
    store u64 %3, ptr %177
    %179 = load u64, ptr %175
    %180 = call @func.165(%179)
    br bb1(%180)
bb1(%4: u8):
    %181 = load u64, ptr %176
    %182 = call @func.165(%181)
    br bb2(%4, %182)
bb2(%5: u8, %6: u8):
    %183 = call @func.160(%5, %6)
    br bb3(%183)
bb3(%7: u8):
    %184 = load u64, ptr %177
    %185 = call @func.165(%184)
    br bb4(%7, %185)
bb4(%8: u8, %9: u8):
    %186 = call @func.160(%8, %9)
    br bb5(%186)
bb5(%10: u8):
    %187 = zext u8 %10 to u32
    %188 = const u32 1
    %189, %190 = add.overflow u32 %187, %188
    store u32 %189, ptr %178
    %191 = const i64 4
    %192 = gep i8, ptr %178, %191
    store bool %190, ptr %192
    %193 = const i64 4
    %194 = gep i8, ptr %178, %193
    %195 = load bool, ptr %194
    %196 = const bool false
    %197 = icmp eq bool %195, %196
    condbr %197, bb6, bb45
bb6:
    %198 = load u32, ptr %178
    %199 = const u32 255
    %200 = call @func.161(%198, %199)
    br bb7(%200)
bb7(%11: u32):
    %201 = load u64, ptr %177
    %202 = call @func.167(%201)
    br bb8(%11, %202)
bb8(%12: u32, %13: u32):
    %203 = const u32 1
    %204 = call @func.162(%13, %203)
    br bb9(%12, %204)
bb9(%14: u32, %15: u32):
    %205 = load u64, ptr %175
    %206 = call @func.167(%205)
    br bb10(%14, %15, %206)
bb10(%16: u32, %17: u32, %18: u32):
    %207 = load u64, ptr %176
    %208 = call @func.167(%207)
    br bb11(%16, %17, %18, %208)
bb11(%19: u32, %20: u32, %21: u32, %22: u32):
    %209 = call @func.163(%21, %22)
    br bb12(%19, %20, %209)
bb12(%23: u32, %24: u32, %25: u32):
    %210 = call @func.163(%25, %24)
    br bb13(%23, %210)
bb13(%26: u32, %27: u32):
    %211 = zext u32 %26 to u64
    %212 = load u64, ptr %175
    %213 = call @func.166(%212)
    br bb14(%26, %27, %211, %213)
bb14(%28: u32, %29: u32, %30: u64, %31: u32):
    %214 = zext u32 %31 to u64
    %215 = load u64, ptr %176
    %216 = call @func.166(%215)
    br bb15(%28, %29, %30, %214, %216)
bb15(%32: u32, %33: u32, %34: u64, %35: u64, %36: u32):
    %217 = zext u32 %36 to u64
    %218 = load u64, ptr %177
    %219 = call @func.166(%218)
    br bb16(%32, %33, %34, %35, %217, %219)
bb16(%37: u32, %38: u32, %39: u64, %40: u64, %41: u64, %42: u32):
    %220 = zext u32 %42 to u64
    %221 = call @func.143(%41, %220)
    br bb17(%37, %38, %39, %40, %221)
bb17(%43: u32, %44: u32, %45: u64, %46: u64, %47: u64):
    %222 = call @func.143(%46, %47)
    br bb18(%43, %44, %45, %222)
bb18(%48: u32, %49: u32, %50: u64, %51: u64):
    %223 = call @func.143(%50, %51)
    br bb19(%48, %49, %223)
bb19(%52: u32, %53: u32, %54: u64):
    %224 = trunc u64 %54 to u32
    %225 = load u64, ptr %175
    %226 = call @func.168(%225)
    br bb20(%52, %53, %224, %226)
bb20(%55: u32, %56: u32, %57: u32, %58: bool):
    condbr %58, bb23(%55, %56, %57), bb21(%55, %56, %57)
bb21(%59: u32, %60: u32, %61: u32):
    %227 = load u64, ptr %176
    %228 = call @func.168(%227)
    br bb22(%59, %60, %61, %228)
bb22(%62: u32, %63: u32, %64: u32, %65: bool):
    condbr %65, bb23(%62, %63, %64), bb24(%62, %63, %64)
bb23(%66: u32, %67: u32, %68: u32):
    %229 = const bool true
    br bb25(%66, %67, %68, %229)
bb24(%69: u32, %70: u32, %71: u32):
    %230 = load u64, ptr %177
    %231 = call @func.168(%230)
    br bb25(%69, %70, %71, %231)
bb25(%72: u32, %73: u32, %74: u32, %75: bool):
    %232 = load u64, ptr %175
    %233 = call @func.169(%232)
    br bb26(%72, %73, %74, %75, %233)
bb26(%76: u32, %77: u32, %78: u32, %79: bool, %80: bool):
    condbr %80, bb29(%76, %77, %78, %79), bb27(%76, %77, %78, %79)
bb27(%81: u32, %82: u32, %83: u32, %84: bool):
    %234 = load u64, ptr %176
    %235 = call @func.169(%234)
    br bb28(%81, %82, %83, %84, %235)
bb28(%85: u32, %86: u32, %87: u32, %88: bool, %89: bool):
    condbr %89, bb29(%85, %86, %87, %88), bb30(%85, %86, %87, %88)
bb29(%90: u32, %91: u32, %92: u32, %93: bool):
    %236 = const bool true
    br bb31(%90, %91, %92, %93, %236)
bb30(%94: u32, %95: u32, %96: u32, %97: bool):
    %237 = load u64, ptr %177
    %238 = call @func.169(%237)
    br bb31(%94, %95, %96, %97, %238)
bb31(%98: u32, %99: u32, %100: u32, %101: bool, %102: bool):
    %239 = load u64, ptr %175
    %240 = call @func.170(%239)
    br bb32(%98, %99, %100, %101, %102, %240)
bb32(%103: u32, %104: u32, %105: u32, %106: bool, %107: bool, %108: bool):
    condbr %108, bb35(%103, %104, %105, %106, %107), bb33(%103, %104, %105, %106, %107)
bb33(%109: u32, %110: u32, %111: u32, %112: bool, %113: bool):
    %241 = load u64, ptr %176
    %242 = call @func.170(%241)
    br bb34(%109, %110, %111, %112, %113, %242)
bb34(%114: u32, %115: u32, %116: u32, %117: bool, %118: bool, %119: bool):
    condbr %119, bb35(%114, %115, %116, %117, %118), bb36(%114, %115, %116, %117, %118)
bb35(%120: u32, %121: u32, %122: u32, %123: bool, %124: bool):
    %243 = const bool true
    br bb37(%120, %121, %122, %123, %124, %243)
bb36(%125: u32, %126: u32, %127: u32, %128: bool, %129: bool):
    %244 = load u64, ptr %177
    %245 = call @func.170(%244)
    br bb37(%125, %126, %127, %128, %129, %245)
bb37(%130: u32, %131: u32, %132: u32, %133: bool, %134: bool, %135: bool):
    %246 = load u64, ptr %175
    %247 = call @func.171(%246)
    br bb38(%130, %131, %132, %133, %134, %135, %247)
bb38(%136: u32, %137: u32, %138: u32, %139: bool, %140: bool, %141: bool, %142: bool):
    condbr %142, bb41(%136, %137, %138, %139, %140, %141), bb39(%136, %137, %138, %139, %140, %141)
bb39(%143: u32, %144: u32, %145: u32, %146: bool, %147: bool, %148: bool):
    %248 = load u64, ptr %176
    %249 = call @func.171(%248)
    br bb40(%143, %144, %145, %146, %147, %148, %249)
bb40(%149: u32, %150: u32, %151: u32, %152: bool, %153: bool, %154: bool, %155: bool):
    condbr %155, bb41(%149, %150, %151, %152, %153, %154), bb42(%149, %150, %151, %152, %153, %154)
bb41(%156: u32, %157: u32, %158: u32, %159: bool, %160: bool, %161: bool):
    %250 = const bool true
    br bb43(%156, %157, %158, %159, %160, %161, %250)
bb42(%162: u32, %163: u32, %164: u32, %165: bool, %166: bool, %167: bool):
    %251 = load u64, ptr %177
    %252 = call @func.171(%251)
    br bb43(%162, %163, %164, %165, %166, %167, %252)
bb43(%168: u32, %169: u32, %170: u32, %171: bool, %172: bool, %173: bool, %174: bool):
    call @func.147(%0, %170, %169, %168, %171, %172, %173, %174)
    br bb44
bb44:
    ret
bb45:
    unreachable
}

fn @ExprMeta__approx_depth(functy.165) {
bb0(%0: u64):
    %2 = alloca i64, align 8
    store u64 %0, ptr %2
    %3 = load u64, ptr %2
    %4 = const u32 32
    %5 = const u32 64
    %6 = icmp ult u32 %4, %5
    condbr %6, bb1(%3), bb2
bb1(%1: u64):
    %7 = const u32 32
    %8 = zext u32 %7 to u64
    %9 = lshr u64 %1, %8
    %10 = const u64 255
    %11 = and u64 %9, %10
    %12 = trunc u64 %11 to u8
    ret %12
bb2:
    unreachable
}

fn @ExprMeta__hash(functy.166) {
bb0(%0: u64):
    %1 = alloca i64, align 8
    store u64 %0, ptr %1
    %2 = load u64, ptr %1
    %3 = const u64 4294967295
    %4 = and u64 %2, %3
    %5 = trunc u64 %4 to u32
    ret %5
}

fn @ExprMeta__loose_bvar_range(functy.167) {
bb0(%0: u64):
    %2 = alloca i64, align 8
    store u64 %0, ptr %2
    %3 = load u64, ptr %2
    %4 = const u32 44
    %5 = const u32 64
    %6 = icmp ult u32 %4, %5
    condbr %6, bb1(%3), bb2
bb1(%1: u64):
    %7 = const u32 44
    %8 = zext u32 %7 to u64
    %9 = lshr u64 %1, %8
    %10 = trunc u64 %9 to u32
    ret %10
bb2:
    unreachable
}

fn @ExprMeta__has_fvar(functy.168) {
bb0(%0: u64):
    %2 = alloca i64, align 8
    store u64 %0, ptr %2
    %3 = load u64, ptr %2
    %4 = const u32 40
    %5 = const u32 64
    %6 = icmp ult u32 %4, %5
    condbr %6, bb1(%3), bb2
bb1(%1: u64):
    %7 = const u32 40
    %8 = zext u32 %7 to u64
    %9 = lshr u64 %1, %8
    %10 = const u64 1
    %11 = and u64 %9, %10
    %12 = const u64 1
    %13 = icmp eq u64 %11, %12
    ret %13
bb2:
    unreachable
}

fn @ExprMeta__has_expr_mvar(functy.169) {
bb0(%0: u64):
    %2 = alloca i64, align 8
    store u64 %0, ptr %2
    %3 = load u64, ptr %2
    %4 = const u32 41
    %5 = const u32 64
    %6 = icmp ult u32 %4, %5
    condbr %6, bb1(%3), bb2
bb1(%1: u64):
    %7 = const u32 41
    %8 = zext u32 %7 to u64
    %9 = lshr u64 %1, %8
    %10 = const u64 1
    %11 = and u64 %9, %10
    %12 = const u64 1
    %13 = icmp eq u64 %11, %12
    ret %13
bb2:
    unreachable
}

fn @ExprMeta__has_level_mvar(functy.170) {
bb0(%0: u64):
    %2 = alloca i64, align 8
    store u64 %0, ptr %2
    %3 = load u64, ptr %2
    %4 = const u32 42
    %5 = const u32 64
    %6 = icmp ult u32 %4, %5
    condbr %6, bb1(%3), bb2
bb1(%1: u64):
    %7 = const u32 42
    %8 = zext u32 %7 to u64
    %9 = lshr u64 %1, %8
    %10 = const u64 1
    %11 = and u64 %9, %10
    %12 = const u64 1
    %13 = icmp eq u64 %11, %12
    ret %13
bb2:
    unreachable
}

fn @ExprMeta__has_level_param(functy.171) {
bb0(%0: u64):
    %2 = alloca i64, align 8
    store u64 %0, ptr %2
    %3 = load u64, ptr %2
    %4 = const u32 43
    %5 = const u32 64
    %6 = icmp ult u32 %4, %5
    condbr %6, bb1(%3), bb2
bb1(%1: u64):
    %7 = const u32 43
    %8 = zext u32 %7 to u64
    %9 = lshr u64 %1, %8
    %10 = const u64 1
    %11 = and u64 %9, %10
    %12 = const u64 1
    %13 = icmp eq u64 %11, %12
    ret %13
bb2:
    unreachable
}

fn @Expr__loose_bvar_range(functy.172) {
bb0(%0: ptr):
    %2 = alloca i64, align 8
    %3 = const i64 32
    %4 = gep i8, ptr %0, %3
    %5 = load i64, ptr %4
    store i64 %5, ptr %2
    %6 = load u64, ptr %2
    %7 = call @func.167(%6)
    br bb1(%7)
bb1(%1: u32):
    ret %1
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm14saturating_add(functy.173) {
}

fn @checked_add_u32(functy.174) {
bb0(%0: u32, %1: u32):
    %3 = call @func.173(%0, %1)
    br bb1(%3)
bb1(%2: u32):
    ret %2
}

fn @has_loose_bvars_in_domain(functy.175) {
bb0(%0: ptr, %1: u32, %2: bool):
    %42 = alloca i64, align 8
    %43 = alloca i64, align 8
    %44 = alloca (i32, i32), align 4
    store ptr %0, ptr %42
    %45 = load ptr, ptr %42
    store ptr %45, ptr %43
    %46 = load ptr, ptr %43
    %47 = load i8, ptr %46
    %48 = sext i8 %47 to i64
    switch %48 [ 6: bb2(%1, %2) default: bb1(%1, %2) ]
bb1(%3: u32, %4: bool):
    condbr %4, bb15, bb14(%3)
bb2(%5: u32, %6: bool):
    %49 = load ptr, ptr %43
    %50 = const i64 1
    %51 = gep i8, ptr %49, %50
    %52 = load ptr, ptr %43
    %53 = const i64 8
    %54 = gep i8, ptr %52, %53
    %55 = load ptr, ptr %43
    %56 = const i64 16
    %57 = gep i8, ptr %55, %56
    %58 = load ptr, ptr %54
    %59 = const i64 16
    %60 = gep i8, ptr %58, %59
    br bb3(%5, %6, %51, %57, %60)
bb3(%7: u32, %8: bool, %9: ptr, %10: ptr, %11: ptr):
    %61 = call @func.188(%11, %7)
    br bb4(%7, %8, %9, %10, %61)
bb4(%12: u32, %13: bool, %14: ptr, %15: ptr, %16: bool):
    condbr %16, bb5(%12, %13, %14, %15), bb11(%12, %13, %15)
bb5(%17: u32, %18: bool, %19: ptr, %20: ptr):
    %62 = load u8, ptr %19
    %63 = const u8 0
    %64 = icmp eq u8 %62, %63
    condbr %64, bb6, bb7(%17, %18, %20)
bb6:
    %65 = const bool true
    br bb16(%65)
bb7(%21: u32, %22: bool, %23: ptr):
    %66 = load ptr, ptr %23
    %67 = const i64 16
    %68 = gep i8, ptr %66, %67
    br bb8(%21, %22, %23, %68)
bb8(%24: u32, %25: bool, %26: ptr, %27: ptr):
    %69 = const u32 0
    %70 = call @func.175(%27, %69, %25)
    br bb9(%24, %25, %26, %70)
bb9(%28: u32, %29: bool, %30: ptr, %31: bool):
    condbr %31, bb10, bb11(%28, %29, %30)
bb10:
    %71 = const bool true
    br bb16(%71)
bb11(%32: u32, %33: bool, %34: ptr):
    %72 = load ptr, ptr %34
    %73 = const i64 16
    %74 = gep i8, ptr %72, %73
    br bb12(%32, %33, %74)
bb12(%35: u32, %36: bool, %37: ptr):
    %75 = const u32 1
    %76, %77 = add.overflow u32 %35, %75
    store u32 %76, ptr %44
    %78 = const i64 4
    %79 = gep i8, ptr %44, %78
    store bool %77, ptr %79
    %80 = const i64 4
    %81 = gep i8, ptr %44, %80
    %82 = load bool, ptr %81
    %83 = const bool false
    %84 = icmp eq bool %82, %83
    condbr %84, bb13(%36, %37), bb17
bb13(%38: bool, %39: ptr):
    %85 = load u32, ptr %44
    %86 = call @func.175(%39, %85, %38)
    br bb16(%86)
bb14(%40: u32):
    %87 = load ptr, ptr %42
    %88 = call @func.188(%87, %40)
    br bb16(%88)
bb15:
    %89 = const bool false
    br bb16(%89)
bb16(%41: bool):
    ret %41
bb17:
    unreachable
}

fn @BinderData__new(functy.176) {
bb0(%0: ptr, %1: u8, %2: u8):
    store u8 %1, ptr %0
    %3 = const i64 1
    %4 = gep i8, ptr %0, %3
    store u8 %2, ptr %4
    ret
}

fn @KaniHasher__new(functy.177) {
bb0(%0: ptr):
    %1 = const u64 0
    store u64 %1, ptr %0
    ret
}

fn @_RINvXsg_NtNtCs2EYQwhfuABO_4core4hash5implsiNtB8_4Hash4hashNtCs6RT0DENTjyC_27clean_mutual_recursor_slice10KaniHasherEBW_(functy.178) {
}

fn @_RINvXs9_NtNtCs2EYQwhfuABO_4core4hash5implsmNtB8_4Hash4hashNtCs6RT0DENTjyC_27clean_mutual_recursor_slice10KaniHasherEBW_(functy.179) {
}

fn @_RINvXsa_NtNtCs2EYQwhfuABO_4core4hash5implsyNtB8_4Hash4hashNtCs6RT0DENTjyC_27clean_mutual_recursor_slice10KaniHasherEBW_(functy.180) {
}

fn @_Literal_as_std__hash__Hash___hash(functy.181) {
bb0(%0: ptr, %1: ptr):
    %5 = alloca i64, align 8
    %6 = alloca i64, align 8
    store ptr %0, ptr %5
    %7 = load ptr, ptr %5
    %8 = load i32, ptr %7
    %9 = sext i32 %8 to i64
    store i64 %9, ptr %6
    call @func.178(%6, %1)
    br bb1(%1)
bb1(%2: ptr):
    %10 = load ptr, ptr %5
    %11 = load i32, ptr %10
    %12 = sext i32 %11 to i64
    switch %12 [ 0: bb4(%2) 1: bb3(%2) default: bb2 ]
bb2:
    unreachable
bb3(%3: ptr):
    %13 = load ptr, ptr %5
    %14 = const i64 4
    %15 = gep i8, ptr %13, %14
    call @func.179(%15, %3)
    br bb5
bb4(%4: ptr):
    %16 = load ptr, ptr %5
    %17 = const i64 8
    %18 = gep i8, ptr %16, %17
    call @func.180(%18, %4)
    br bb5
bb5:
    ret
}

fn @_KaniHasher_as_std__hash__Hasher___finish(functy.182) {
bb0(%0: ptr):
    %1 = load u64, ptr %0
    ret %1
}

fn @_RINvXs9_NtNtCs2EYQwhfuABO_4core4hash5implsmNtB8_4Hash4hashNtCs6RT0DENTjyC_27clean_mutual_recursor_slice10KaniHasherEBW_(functy.183) {
}

fn @_Name_as_std__hash__Hash___hash(functy.184) {
bb0(%0: ptr, %1: ptr):
    %2 = alloca i64, align 8
    store ptr %0, ptr %2
    %3 = load ptr, ptr %2
    call @func.183(%3, %1)
    br bb1
bb1:
    ret
}

fn @_RINvXsg_NtNtCs2EYQwhfuABO_4core4hash5implsiNtB8_4Hash4hashNtCs6RT0DENTjyC_27clean_mutual_recursor_slice10KaniHasherEBW_(functy.185) {
}

fn @_RINvXsk_NtCskTzINo8ZBH9_5alloc5boxedINtB6_3BoxNtCs6RT0DENTjyC_27clean_mutual_recursor_slice5LevelENtNtCs2EYQwhfuABO_4core4hash4Hash4hashNtBK_10KaniHasherEBK_(functy.186) {
}

fn @_Level_as_std__hash__Hash___hash(functy.187) {
bb0(%0: ptr, %1: ptr):
    %5 = alloca i64, align 8
    %6 = alloca i64, align 8
    store ptr %0, ptr %5
    %7 = load ptr, ptr %5
    %8 = load i32, ptr %7
    %9 = sext i32 %8 to i64
    store i64 %9, ptr %6
    call @func.185(%6, %1)
    br bb1(%1)
bb1(%2: ptr):
    %10 = load ptr, ptr %5
    %11 = load i32, ptr %10
    %12 = sext i32 %11 to i64
    switch %12 [ 1: bb3(%2) 2: bb2(%2) 0: bb4 default: bb5 ]
bb2(%3: ptr):
    %13 = load ptr, ptr %5
    %14 = const i64 4
    %15 = gep i8, ptr %13, %14
    call @func.184(%15, %3)
    br bb4
bb3(%4: ptr):
    %16 = load ptr, ptr %5
    %17 = const i64 8
    %18 = gep i8, ptr %16, %17
    call @func.186(%18, %4)
    br bb4
bb4:
    ret
bb5:
    unreachable
}

fn @Expr__has_loose_bvar(functy.188) {
bb0(%0: ptr, %1: u32):
    %5 = alloca (i32, i32), align 4
    %6 = const u32 1
    %7, %8 = add.overflow u32 %1, %6
    store u32 %7, ptr %5
    %9 = const i64 4
    %10 = gep i8, ptr %5, %9
    store bool %8, ptr %10
    %11 = const i64 4
    %12 = gep i8, ptr %5, %11
    %13 = load bool, ptr %12
    %14 = const bool false
    %15 = icmp eq bool %13, %14
    condbr %15, bb1(%0, %1), bb3
bb1(%2: ptr, %3: u32):
    %16 = load u32, ptr %5
    %17 = call @func.189(%2, %3, %16)
    br bb2(%17)
bb2(%4: bool):
    ret %4
bb3:
    unreachable
}

fn @Expr__has_loose_bvar_in_range(functy.189) {
bb0(%0: ptr, %1: u32, %2: u32):
    %4 = call @func.190(%0, %1, %2)
    br bb1(%4)
bb1(%3: bool):
    ret %3
}

fn @Expr__has_loose_bvar_in_range_impl(functy.190) {
bb0(%0: ptr, %1: u32, %2: u32):
    %121 = alloca i64, align 8
    %122 = alloca i64, align 8
    %123 = alloca (i32, i32, i32), align 4
    %124 = alloca (i32, i32, i32), align 4
    store ptr %0, ptr %121
    %125 = const u32 4294967295
    %126 = icmp ne u32 %2, %125
    condbr %126, bb1(%1, %2), bb3(%1, %2)
bb1(%3: u32, %4: u32):
    %127 = icmp uge u32 %3, %4
    condbr %127, bb2, bb3(%3, %4)
bb2:
    %128 = const bool false
    br bb43(%128)
bb3(%5: u32, %6: u32):
    %129 = load ptr, ptr %121
    %130 = call @func.172(%129)
    br bb4(%5, %6, %130)
bb4(%7: u32, %8: u32, %9: u32):
    %131 = icmp ule u32 %9, %7
    condbr %131, bb5, bb6(%7, %8)
bb5:
    %132 = const bool false
    br bb43(%132)
bb6(%10: u32, %11: u32):
    %133 = load ptr, ptr %121
    store ptr %133, ptr %122
    %134 = load ptr, ptr %122
    %135 = load i8, ptr %134
    %136 = sext i8 %135 to i64
    switch %136 [ 0: bb14(%10, %11) 1: bb13 2: bb13 3: bb13 4: bb12(%10, %11) 5: bb11(%10, %11) 6: bb10(%10, %11) 7: bb9(%10, %11) 8: bb13 9: bb8(%10, %11) default: bb7 ]
bb7:
    unreachable
bb8(%12: u32, %13: u32):
    %137 = load ptr, ptr %122
    %138 = const i64 16
    %139 = gep i8, ptr %137, %138
    %140 = load ptr, ptr %139
    %141 = const i64 16
    %142 = gep i8, ptr %140, %141
    br bb42(%12, %13, %142)
bb9(%14: u32, %15: u32):
    %143 = load ptr, ptr %122
    %144 = const i64 8
    %145 = gep i8, ptr %143, %144
    %146 = load ptr, ptr %122
    %147 = const i64 16
    %148 = gep i8, ptr %146, %147
    %149 = load ptr, ptr %122
    %150 = const i64 24
    %151 = gep i8, ptr %149, %150
    call @func.191(%124, %14, %15)
    br bb30(%14, %15, %145, %148, %151)
bb10(%16: u32, %17: u32):
    %152 = load ptr, ptr %122
    %153 = const i64 8
    %154 = gep i8, ptr %152, %153
    %155 = load ptr, ptr %122
    %156 = const i64 16
    %157 = gep i8, ptr %155, %156
    br bb20(%16, %17, %154, %157)
bb11(%18: u32, %19: u32):
    %158 = load ptr, ptr %122
    %159 = const i64 8
    %160 = gep i8, ptr %158, %159
    %161 = load ptr, ptr %122
    %162 = const i64 16
    %163 = gep i8, ptr %161, %162
    br bb20(%18, %19, %160, %163)
bb12(%20: u32, %21: u32):
    %164 = load ptr, ptr %122
    %165 = const i64 8
    %166 = gep i8, ptr %164, %165
    %167 = load ptr, ptr %122
    %168 = const i64 16
    %169 = gep i8, ptr %167, %168
    %170 = load ptr, ptr %166
    %171 = const i64 16
    %172 = gep i8, ptr %170, %171
    br bb15(%20, %21, %169, %172)
bb13:
    %173 = const bool false
    br bb43(%173)
bb14(%22: u32, %23: u32):
    %174 = load ptr, ptr %122
    %175 = const i64 4
    %176 = gep i8, ptr %174, %175
    %177 = load u32, ptr %176
    %178 = call @func.192(%177, %22, %23)
    br bb43(%178)
bb15(%24: u32, %25: u32, %26: ptr, %27: ptr):
    %179 = call @func.189(%27, %24, %25)
    br bb16(%24, %25, %26, %179)
bb16(%28: u32, %29: u32, %30: ptr, %31: bool):
    condbr %31, bb17, bb18(%28, %29, %30)
bb17:
    %180 = const bool true
    br bb43(%180)
bb18(%32: u32, %33: u32, %34: ptr):
    %181 = load ptr, ptr %34
    %182 = const i64 16
    %183 = gep i8, ptr %181, %182
    br bb19(%32, %33, %183)
bb19(%35: u32, %36: u32, %37: ptr):
    %184 = call @func.189(%37, %35, %36)
    br bb43(%184)
bb20(%38: u32, %39: u32, %40: ptr, %41: ptr):
    call @func.191(%123, %38, %39)
    br bb21(%38, %39, %40, %41)
bb21(%42: u32, %43: u32, %44: ptr, %45: ptr):
    %185 = load i32, ptr %123
    %186 = sext i32 %185 to i64
    switch %186 [ 0: bb22(%42, %43, %44) 1: bb23(%42, %43, %44, %45) default: bb7 ]
bb22(%46: u32, %47: u32, %48: ptr):
    %187 = const bool false
    br bb25(%46, %47, %48, %187)
bb23(%49: u32, %50: u32, %51: ptr, %52: ptr):
    %188 = const i64 4
    %189 = gep i8, ptr %123, %188
    %190 = load u32, ptr %189
    %191 = const i64 8
    %192 = gep i8, ptr %123, %191
    %193 = load u32, ptr %192
    %194 = load ptr, ptr %52
    %195 = const i64 16
    %196 = gep i8, ptr %194, %195
    br bb24(%49, %50, %51, %190, %193, %196)
bb24(%53: u32, %54: u32, %55: ptr, %56: u32, %57: u32, %58: ptr):
    %197 = call @func.189(%58, %56, %57)
    br bb25(%53, %54, %55, %197)
bb25(%59: u32, %60: u32, %61: ptr, %62: bool):
    %198 = load ptr, ptr %61
    %199 = const i64 16
    %200 = gep i8, ptr %198, %199
    br bb26(%59, %60, %62, %200)
bb26(%63: u32, %64: u32, %65: bool, %66: ptr):
    %201 = call @func.189(%66, %63, %64)
    br bb27(%65, %201)
bb27(%67: bool, %68: bool):
    condbr %68, bb28, bb29(%67)
bb28:
    %202 = const bool true
    br bb43(%202)
bb29(%69: bool):
    br bb43(%69)
bb30(%70: u32, %71: u32, %72: ptr, %73: ptr, %74: ptr):
    %203 = load i32, ptr %124
    %204 = sext i32 %203 to i64
    switch %204 [ 0: bb31(%70, %71, %72, %73) 1: bb32(%70, %71, %72, %73, %74) default: bb7 ]
bb31(%75: u32, %76: u32, %77: ptr, %78: ptr):
    %205 = const bool false
    br bb34(%75, %76, %77, %78, %205)
bb32(%79: u32, %80: u32, %81: ptr, %82: ptr, %83: ptr):
    %206 = const i64 4
    %207 = gep i8, ptr %124, %206
    %208 = load u32, ptr %207
    %209 = const i64 8
    %210 = gep i8, ptr %124, %209
    %211 = load u32, ptr %210
    %212 = load ptr, ptr %83
    %213 = const i64 16
    %214 = gep i8, ptr %212, %213
    br bb33(%79, %80, %81, %82, %208, %211, %214)
bb33(%84: u32, %85: u32, %86: ptr, %87: ptr, %88: u32, %89: u32, %90: ptr):
    %215 = call @func.189(%90, %88, %89)
    br bb34(%84, %85, %86, %87, %215)
bb34(%91: u32, %92: u32, %93: ptr, %94: ptr, %95: bool):
    %216 = load ptr, ptr %93
    %217 = const i64 16
    %218 = gep i8, ptr %216, %217
    br bb35(%91, %92, %94, %95, %218)
bb35(%96: u32, %97: u32, %98: ptr, %99: bool, %100: ptr):
    %219 = call @func.189(%100, %96, %97)
    br bb36(%96, %97, %98, %99, %219)
bb36(%101: u32, %102: u32, %103: ptr, %104: bool, %105: bool):
    condbr %105, bb40, bb37(%101, %102, %103, %104)
bb37(%106: u32, %107: u32, %108: ptr, %109: bool):
    %220 = load ptr, ptr %108
    %221 = const i64 16
    %222 = gep i8, ptr %220, %221
    br bb38(%106, %107, %109, %222)
bb38(%110: u32, %111: u32, %112: bool, %113: ptr):
    %223 = call @func.189(%113, %110, %111)
    br bb39(%112, %223)
bb39(%114: bool, %115: bool):
    condbr %115, bb40, bb41(%114)
bb40:
    %224 = const bool true
    br bb43(%224)
bb41(%116: bool):
    br bb43(%116)
bb42(%117: u32, %118: u32, %119: ptr):
    %225 = call @func.189(%119, %117, %118)
    br bb43(%225)
bb43(%120: bool):
    ret %120
}

fn @shift_bvar_range(functy.191) {
bb0(%0: ptr, %1: u32, %2: u32):
    %16 = alloca (i32, i32), align 4
    %17 = const u32 4294967295
    %18 = icmp ne u32 %2, %17
    condbr %18, bb1(%1, %2), bb3(%1, %2)
bb1(%3: u32, %4: u32):
    %19 = icmp uge u32 %3, %4
    condbr %19, bb2, bb3(%3, %4)
bb2:
    %20 = const i32 0
    store i32 %20, ptr %0
    br bb10
bb3(%5: u32, %6: u32):
    %21 = const u32 4294967295
    %22 = icmp eq u32 %5, %21
    condbr %22, bb4, bb5(%5, %6)
bb4:
    %23 = const i32 0
    store i32 %23, ptr %0
    br bb10
bb5(%7: u32, %8: u32):
    %24 = const u32 1
    %25 = call @func.174(%7, %24)
    br bb6(%8, %25)
bb6(%9: u32, %10: u32):
    %26 = const u32 4294967295
    %27 = icmp eq u32 %9, %26
    condbr %27, bb7(%10), bb8(%9, %10)
bb7(%11: u32):
    %28 = const u32 4294967295
    br bb9(%11, %28)
bb8(%12: u32, %13: u32):
    %29 = const u32 1
    %30 = call @func.174(%12, %29)
    br bb9(%13, %30)
bb9(%14: u32, %15: u32):
    store u32 %14, ptr %16
    %31 = const i64 4
    %32 = gep i8, ptr %16, %31
    store u32 %15, ptr %32
    %33 = const i64 4
    %34 = gep i8, ptr %0, %33
    %35 = load i32, ptr %16
    store i32 %35, ptr %34
    %36 = const i64 4
    %37 = gep i8, ptr %16, %36
    %38 = const i64 4
    %39 = gep i8, ptr %34, %38
    %40 = load i32, ptr %37
    store i32 %40, ptr %39
    %41 = const i32 1
    store i32 %41, ptr %0
    br bb10
bb10:
    ret
}

fn @bvar_in_range(functy.192) {
bb0(%0: u32, %1: u32, %2: u32):
    %11 = const u32 4294967295
    %12 = icmp eq u32 %2, %11
    condbr %12, bb1(%0, %1), bb2(%0, %1, %2)
bb1(%3: u32, %4: u32):
    %13 = icmp uge u32 %3, %4
    br bb5(%13)
bb2(%5: u32, %6: u32, %7: u32):
    %14 = icmp uge u32 %5, %6
    condbr %14, bb3(%5, %7), bb4
bb3(%8: u32, %9: u32):
    %15 = icmp ult u32 %8, %9
    br bb5(%15)
bb4:
    %16 = const bool false
    br bb5(%16)
bb5(%10: bool):
    ret %10
}
"#;

// ════════════════════════════════════════════════════════════════════════════
// Native mirror — the slice source itself, compiled natively in this test crate
// (byte-identical logic; the strongest possible oracle for the differential).
// Only transforms: inner attrs -> mod attrs, #[no_mangle] stripped, main() cut,
// bi_default/bi_implicit/deep_eq/root_part made pub.
// ════════════════════════════════════════════════════════════════════════════
#[allow(dead_code)]
#[allow(clippy::all)]
#[allow(unused_variables)]
pub mod mx {

    #[allow(unused_imports)]
    use std::convert::TryFrom;
    use std::hash::{Hash, Hasher};
    use std::sync::Arc; // pre-2021 prelude (the MIR driver's edition) needs the explicit import

    // ════════════════════════════════════════════════════════════════════════════
    // Modeled leaf payloads (Name/Level/Literal/FVarId/BinderData). VERBATIM the
    // verified construction slice.
    // ════════════════════════════════════════════════════════════════════════════

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct Name(pub u32);

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct FVarId(pub u64);

    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    pub enum Level {
        Zero,
        Succ(Box<Level>),
        Param(Name),
    }

    impl Level {
        fn has_params(&self) -> bool {
            match self {
                Level::Zero => false,
                Level::Succ(l) => l.has_params(),
                Level::Param(_) => true,
            }
        }
    }

    type LevelVec = Vec<Level>;

    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    pub enum Literal {
        Nat(u64),
        Str(u32),
    }

    // BinderInfo::Default / Implicit modeled as the real `bd.info` byte (Default=0,
    // Implicit=1). infer_implicit only ever compares against Default and constructs
    // Implicit, so the two-variant model is faithful.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct BinderData {
        pub info: u8,
        pub mult: u8,
    }

    impl BinderData {
        // VERBATIM `BinderData::new(info, mult)` (expr/types.rs:131).
        #[inline]
        fn new(info: u8, mult: u8) -> Self {
            BinderData { info, mult }
        }
    }

    // BinderInfo::Default / Implicit -> the scalar BinderData the real constructor stores.
    // Built as RUNTIME locals (NOT `const` items): the real `Expr::pi(BinderInfo::Default,..)`
    // passes a freshly-`Into`-converted `BinderData`, and the frontend lowers a struct-adt
    // only as a runtime aggregate. These `#[inline]` fns return the same scalar pair as
    // `BinderInfo::Default.into()` / `::Implicit.into()`.
    #[inline]
    pub fn bi_default() -> BinderData {
        BinderData { info: 0, mult: 0 }
    }
    #[inline]
    pub fn bi_implicit() -> BinderData {
        BinderData { info: 1, mult: 0 }
    }
    // `BinderInfo::Default` used as a comparison value in infer_implicit / has_loose_bvars_in_domain.
    const INFO_DEFAULT: u8 = 0;

    // ════════════════════════════════════════════════════════════════════════════
    // meta.rs — VERBATIM mix_hash / KaniHasher / hash_to_u64 / level_has_mvar.
    // ════════════════════════════════════════════════════════════════════════════

    #[inline]
    pub(crate) fn mix_hash(h: u64, k: u64) -> u64 {
        const M: u64 = 0xc6a4_a793_5bd1_e995;
        const R: u32 = 47;
        let mut k = k.wrapping_mul(M);
        k ^= k >> R;
        k ^= M;
        let mut h = h ^ k;
        h = h.wrapping_mul(M);
        h
    }

    pub(crate) struct KaniHasher {
        state: u64,
    }

    impl KaniHasher {
        pub(crate) fn new() -> Self {
            KaniHasher { state: 0 }
        }
    }

    impl Hasher for KaniHasher {
        fn finish(&self) -> u64 {
            self.state
        }
        fn write(&mut self, bytes: &[u8]) {
            for &b in bytes {
                self.state = self.state.wrapping_mul(31).wrapping_add(b as u64);
            }
        }
        fn write_u8(&mut self, i: u8) {
            self.state ^= i as u64;
            self.state = self.state.wrapping_mul(0x517cc1b727220a95);
        }
        fn write_u16(&mut self, i: u16) {
            self.state ^= i as u64;
            self.state = self.state.wrapping_mul(0x517cc1b727220a95);
        }
        fn write_u32(&mut self, i: u32) {
            self.state ^= i as u64;
            self.state = self.state.wrapping_mul(0x517cc1b727220a95);
        }
        fn write_u64(&mut self, i: u64) {
            self.state ^= i;
            self.state = self.state.wrapping_mul(0x517cc1b727220a95);
        }
        fn write_u128(&mut self, i: u128) {
            self.write_u64(i as u64);
            self.write_u64((i >> 64) as u64);
        }
        fn write_usize(&mut self, i: usize) {
            self.write_u64(i as u64);
        }
    }

    #[inline]
    pub(crate) fn hash_to_u64<T: Hash>(value: &T) -> u64 {
        let mut hasher = KaniHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }

    #[inline]
    pub(crate) fn hash_name(value: &Name) -> u64 {
        let mut hasher = KaniHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }

    #[inline]
    pub(crate) fn hash_level(value: &Level) -> u64 {
        let mut hasher = KaniHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }

    #[inline]
    pub(crate) fn hash_lit(value: &Literal) -> u64 {
        let mut hasher = KaniHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }

    #[inline]
    pub(crate) fn level_has_mvar(_level: &Level) -> bool {
        false
    }

    // ════════════════════════════════════════════════════════════════════════════
    // meta.rs — VERBATIM ExprMeta (bit-packed u64) + pack + accessors + mk_*_meta.
    // ════════════════════════════════════════════════════════════════════════════

    #[derive(Clone, Copy, Debug)]
    pub(crate) struct ExprMeta(u64);

    impl ExprMeta {
        const HASH_MASK: u64 = 0xFFFF_FFFF;
        const DEPTH_SHIFT: u32 = 32;
        const DEPTH_MASK: u64 = 0xFF;
        const HAS_FVAR_BIT: u32 = 40;
        const HAS_EXPR_MVAR_BIT: u32 = 41;
        const HAS_LEVEL_MVAR_BIT: u32 = 42;
        const HAS_LEVEL_PARAM_BIT: u32 = 43;
        const BVAR_RANGE_SHIFT: u32 = 44;
        pub(crate) const MAX_DEPTH: u32 = 255;
        pub(crate) const MAX_BVAR_RANGE: u32 = 1_048_575;

        #[inline]
        pub fn pack(
            hash: u32,
            loose_bvar_range: u32,
            approx_depth: u32,
            has_fvar: bool,
            has_expr_mvar: bool,
            has_level_mvar: bool,
            has_level_param: bool,
        ) -> Self {
            let depth = approx_depth.min(Self::MAX_DEPTH);
            let range = loose_bvar_range;
            let bits = (hash as u64)
                | ((depth as u64) << Self::DEPTH_SHIFT)
                | ((has_fvar as u64) << Self::HAS_FVAR_BIT)
                | ((has_expr_mvar as u64) << Self::HAS_EXPR_MVAR_BIT)
                | ((has_level_mvar as u64) << Self::HAS_LEVEL_MVAR_BIT)
                | ((has_level_param as u64) << Self::HAS_LEVEL_PARAM_BIT)
                | ((range as u64) << Self::BVAR_RANGE_SHIFT);
            ExprMeta(bits)
        }

        #[inline]
        pub fn raw(self) -> u64 {
            self.0
        }
        #[inline]
        pub fn hash(self) -> u32 {
            (self.0 & Self::HASH_MASK) as u32
        }
        #[inline]
        pub fn approx_depth(self) -> u8 {
            ((self.0 >> Self::DEPTH_SHIFT) & Self::DEPTH_MASK) as u8
        }
        #[inline]
        pub fn has_fvar(self) -> bool {
            (self.0 >> Self::HAS_FVAR_BIT) & 1 == 1
        }
        #[inline]
        pub fn has_expr_mvar(self) -> bool {
            (self.0 >> Self::HAS_EXPR_MVAR_BIT) & 1 == 1
        }
        #[inline]
        pub fn has_level_mvar(self) -> bool {
            (self.0 >> Self::HAS_LEVEL_MVAR_BIT) & 1 == 1
        }
        #[inline]
        pub fn has_level_param(self) -> bool {
            (self.0 >> Self::HAS_LEVEL_PARAM_BIT) & 1 == 1
        }
        #[inline]
        pub fn loose_bvar_range(self) -> u32 {
            (self.0 >> Self::BVAR_RANGE_SHIFT) as u32
        }

        #[inline]
        pub fn mk_app_meta(f: ExprMeta, a: ExprMeta) -> ExprMeta {
            let depth = (f.approx_depth().max(a.approx_depth()) as u32 + 1).min(Self::MAX_DEPTH);
            let range = f.loose_bvar_range().max(a.loose_bvar_range());
            let h = mix_hash(f.0, a.0) as u32;
            let flags = (f.0 | a.0) & (0xF_u64 << Self::HAS_FVAR_BIT);
            let bits = (h as u64)
                | ((depth as u64) << Self::DEPTH_SHIFT)
                | flags
                | ((range as u64) << Self::BVAR_RANGE_SHIFT);
            ExprMeta(bits)
        }

        #[inline]
        pub fn mk_binder_meta(ty: ExprMeta, body: ExprMeta, extra_hash: u64) -> ExprMeta {
            let depth =
                (ty.approx_depth().max(body.approx_depth()) as u32 + 1).min(Self::MAX_DEPTH);
            let body_range = body.loose_bvar_range().saturating_sub(1);
            let range = ty.loose_bvar_range().max(body_range);
            let h = mix_hash(
                depth as u64,
                mix_hash(ty.hash() as u64, mix_hash(body.hash() as u64, extra_hash)),
            ) as u32;
            ExprMeta::pack(
                h,
                range,
                depth,
                ty.has_fvar() || body.has_fvar(),
                ty.has_expr_mvar() || body.has_expr_mvar(),
                ty.has_level_mvar() || body.has_level_mvar(),
                ty.has_level_param() || body.has_level_param(),
            )
        }

        #[inline]
        pub fn mk_let_meta(ty: ExprMeta, val: ExprMeta, body: ExprMeta) -> ExprMeta {
            let depth = (ty
                .approx_depth()
                .max(val.approx_depth())
                .max(body.approx_depth()) as u32
                + 1)
            .min(Self::MAX_DEPTH);
            let body_range = body.loose_bvar_range().saturating_sub(1);
            let range = ty
                .loose_bvar_range()
                .max(val.loose_bvar_range())
                .max(body_range);
            let h = mix_hash(
                depth as u64,
                mix_hash(
                    ty.hash() as u64,
                    mix_hash(val.hash() as u64, body.hash() as u64),
                ),
            ) as u32;
            ExprMeta::pack(
                h,
                range,
                depth,
                ty.has_fvar() || val.has_fvar() || body.has_fvar(),
                ty.has_expr_mvar() || val.has_expr_mvar() || body.has_expr_mvar(),
                ty.has_level_mvar() || val.has_level_mvar() || body.has_level_mvar(),
                ty.has_level_param() || val.has_level_param() || body.has_level_param(),
            )
        }

        #[inline]
        pub fn mk_wrapper_meta(inner: ExprMeta, extra_hash: u64) -> ExprMeta {
            let depth = (inner.approx_depth() as u32 + 1).min(Self::MAX_DEPTH);
            let h = mix_hash(depth as u64, mix_hash(inner.hash() as u64, extra_hash)) as u32;
            ExprMeta::pack(
                h,
                inner.loose_bvar_range(),
                depth,
                inner.has_fvar(),
                inner.has_expr_mvar(),
                inner.has_level_mvar(),
                inner.has_level_param(),
            )
        }
    }

    // ════════════════════════════════════════════════════════════════════════════
    // kind.rs — VERBATIM ExprKind + cfg(kani) compute_meta.
    // ════════════════════════════════════════════════════════════════════════════

    #[derive(Clone, Debug)]
    pub enum ExprKind {
        BVar(u32),
        FVar(FVarId),
        Sort(Level),
        Const(Name, LevelVec),
        App(Arc<Expr>, Arc<Expr>),
        Lam(BinderData, Arc<Expr>, Arc<Expr>),
        Pi(BinderData, Arc<Expr>, Arc<Expr>),
        Let(Name, Arc<Expr>, Arc<Expr>, Arc<Expr>, bool),
        Lit(Literal),
        Proj(Name, u32, Arc<Expr>),
    }

    impl ExprKind {
        pub(crate) fn compute_meta(&self) -> ExprMeta {
            match self {
                // ── CONSTRUCTION ARMS (reached by build_recursor_type) — VERBATIM ──
                ExprKind::BVar(idx) => ExprMeta::pack(
                    mix_hash(7, *idx as u64) as u32,
                    idx.saturating_add(1),
                    0,
                    false,
                    false,
                    false,
                    false,
                ),
                ExprKind::App(f, a) => ExprMeta::mk_app_meta(f.meta(), a.meta()),
                ExprKind::Lam(_bi, ty, body) => ExprMeta::mk_binder_meta(ty.meta(), body.meta(), 0),
                ExprKind::Pi(_bi, ty, body) => ExprMeta::mk_binder_meta(ty.meta(), body.meta(), 1),
                ExprKind::Sort(lvl) => ExprMeta::pack(
                    mix_hash(11, hash_level(lvl)) as u32,
                    0,
                    0,
                    false,
                    false,
                    level_has_mvar(lvl),
                    lvl.has_params(),
                ),
                ExprKind::Const(name, _levels) => {
                    let name_hash = hash_name(name);
                    // VERBATIM the real `levels.iter().any(|l| l.has_params())` — lowered to
                    // the equivalent explicit loop. True iff any level is a Param; keeps the
                    // has_level_param meta bit faithful for the Const(I/ctor, [Param(u)..]) nodes.
                    let mut has_param = false;
                    {
                        let mut _li = 0usize;
                        while _li < _levels.len() {
                            if _levels[_li].has_params() {
                                has_param = true;
                            }
                            _li += 1;
                        }
                    }
                    ExprMeta::pack(
                        mix_hash(5, name_hash) as u32,
                        0,
                        0,
                        false,
                        false,
                        false,
                        has_param,
                    )
                }
                // ── LEAF ARMS (off this fn's construction path) — payload hash MODELED ──
                ExprKind::FVar(id) => {
                    ExprMeta::pack(mix_hash(13, id.0) as u32, 0, 0, true, false, false, false)
                }
                ExprKind::Let(_, ty, val, body, _) => {
                    ExprMeta::mk_let_meta(ty.meta(), val.meta(), body.meta())
                }
                ExprKind::Lit(lit) => ExprMeta::pack(
                    mix_hash(3, hash_lit(lit)) as u32,
                    0,
                    0,
                    false,
                    false,
                    false,
                    false,
                ),
                ExprKind::Proj(name, idx, expr) => {
                    let inner = expr.meta();
                    let depth = (inner.approx_depth() as u32 + 1).min(255);
                    let h = mix_hash(
                        depth as u64,
                        mix_hash(hash_name(name), mix_hash(*idx as u64, inner.hash() as u64)),
                    ) as u32;
                    ExprMeta::pack(
                        h,
                        inner.loose_bvar_range(),
                        depth,
                        inner.has_fvar(),
                        inner.has_expr_mvar(),
                        inner.has_level_mvar(),
                        inner.has_level_param(),
                    )
                }
            }
        }
    }

    // ════════════════════════════════════════════════════════════════════════════
    // mod.rs — VERBATIM Expr{kind,meta} + from_kind + accessors + constructors.
    // ════════════════════════════════════════════════════════════════════════════

    #[derive(Clone, Debug)]
    pub struct Expr {
        pub(crate) kind: ExprKind,
        pub(crate) meta: ExprMeta,
    }

    impl Expr {
        #[inline]
        pub fn from_kind(kind: ExprKind) -> Self {
            let meta = kind.compute_meta();
            Expr { kind, meta }
        }
        #[inline]
        pub(crate) fn meta(&self) -> ExprMeta {
            self.meta
        }
        #[inline]
        pub fn kind(&self) -> &ExprKind {
            &self.kind
        }
        #[inline]
        pub fn loose_bvar_range(&self) -> u32 {
            self.meta.loose_bvar_range()
        }

        // ── VERBATIM constructors (each builds via from_kind, Arc::new children). ──
        pub fn bvar(idx: u32) -> Self {
            Expr::from_kind(ExprKind::BVar(idx))
        }
        pub fn const_(name: Name, levels: LevelVec) -> Self {
            Expr::from_kind(ExprKind::Const(name, levels))
        }
        pub fn sort(level: Level) -> Self {
            Expr::from_kind(ExprKind::Sort(level))
        }
        pub fn app(func: Expr, arg: Expr) -> Self {
            Expr::from_kind(ExprKind::App(Arc::new(func), Arc::new(arg)))
        }
        pub fn lam(bd: BinderData, ty: Expr, body: Expr) -> Self {
            Expr::from_kind(ExprKind::Lam(bd, Arc::new(ty), Arc::new(body)))
        }
        pub fn pi(bd: BinderData, ty: Expr, body: Expr) -> Self {
            Expr::from_kind(ExprKind::Pi(bd, Arc::new(ty), Arc::new(body)))
        }
    }

    // ════════════════════════════════════════════════════════════════════════════
    // subst.rs / expr::mod.rs — VERBATIM de-Bruijn READS: lift_at (WRITE lift) +
    // has_loose_bvar_in_range (the meta-guarded loose-bvar READ driving infer_implicit).
    // ════════════════════════════════════════════════════════════════════════════

    #[inline]
    pub(crate) fn checked_add_u32(a: u32, b: u32) -> u32 {
        a.saturating_add(b)
    }

    // VERBATIM `bvar_in_range` (expr/mod.rs:94).
    pub(crate) fn bvar_in_range(idx: u32, start: u32, end: u32) -> bool {
        if end == u32::MAX {
            idx >= start
        } else {
            idx >= start && idx < end
        }
    }

    // VERBATIM `shift_bvar_range` (expr/mod.rs:114). `checked_add_u32` -> saturating_add.
    pub(crate) fn shift_bvar_range(start: u32, end: u32) -> Option<(u32, u32)> {
        if end != u32::MAX && start >= end {
            return None;
        }
        if start == u32::MAX {
            return None;
        }
        let next_start = checked_add_u32(start, 1);
        let next_end = if end == u32::MAX {
            u32::MAX
        } else {
            checked_add_u32(end, 1)
        };
        Some((next_start, next_end))
    }

    impl Expr {
        pub fn lift_at(&self, start: u32, amount: u32) -> Expr {
            if amount == 0 {
                return self.clone();
            }
            if start >= self.loose_bvar_range() {
                return self.clone();
            }
            match &self.kind {
                ExprKind::BVar(idx) => {
                    if *idx >= start {
                        Expr::bvar(checked_add_u32(*idx, amount))
                    } else {
                        self.clone()
                    }
                }
                ExprKind::App(f, a) => {
                    Expr::app(f.lift_at(start, amount), a.lift_at(start, amount))
                }
                ExprKind::Lam(bd, ty, body) => Expr::lam(
                    *bd,
                    ty.lift_at(start, amount),
                    body.lift_at(checked_add_u32(start, 1), amount),
                ),
                ExprKind::Pi(bd, ty, body) => Expr::pi(
                    *bd,
                    ty.lift_at(start, amount),
                    body.lift_at(checked_add_u32(start, 1), amount),
                ),
                _ => self.clone(),
            }
        }

        // VERBATIM `Expr::lift` (subst.rs:495).
        pub fn lift(&self, amount: u32) -> Expr {
            self.lift_at(0, amount)
        }
        // VERBATIM `Expr::lift_from` (subst.rs:511).
        pub fn lift_from(&self, start: u32, amount: u32) -> Expr {
            self.lift_at(start, amount)
        }

        // VERBATIM `Expr::get_app_fn` (expr/constructors.rs:256) — the VERIFIED App-spine
        // head walk (reused by field_motive_index).
        pub fn get_app_fn(&self) -> &Expr {
            let mut current = self;
            while let ExprKind::App(f, _) = &current.kind {
                current = f;
            }
            current
        }

        // VERBATIM `Expr::has_loose_bvar` (subst.rs:547).
        pub fn has_loose_bvar(&self, idx: u32) -> bool {
            self.has_loose_bvar_in_range(idx, idx + 1)
        }

        // VERBATIM `Expr::has_loose_bvar_in_range` (subst.rs:595) — the real wraps
        // `has_loose_bvar_in_range_impl` in `stack_safe(||..)` (a maybe_grow that is a
        // no-op on these small trees); dropped, calling the impl directly.
        pub fn has_loose_bvar_in_range(&self, start: u32, end: u32) -> bool {
            self.has_loose_bvar_in_range_impl(start, end)
        }

        // VERBATIM `has_loose_bvar_in_range_impl` (subst.rs:601). Only the modeled ExprKind
        // arms are present (the CubicalPath/MData/SProp/Squash/... arms are unconstructible
        // in this slice; the `_ => false` on leaves matches the real FVar/Sort/Const/Lit).
        fn has_loose_bvar_in_range_impl(&self, start: u32, end: u32) -> bool {
            if end != u32::MAX && start >= end {
                return false;
            }
            // O(1) metadata guard: all loose BVar indices are < loose_bvar_range(),
            // so if loose_bvar_range() <= start, no BVars exist in [start, end).
            if self.loose_bvar_range() <= start {
                return false;
            }
            match &self.kind {
                ExprKind::BVar(idx) => bvar_in_range(*idx, start, end),
                ExprKind::FVar(_)
                | ExprKind::Sort(_)
                | ExprKind::Const(_, _)
                | ExprKind::Lit(_) => false,
                ExprKind::App(f, a) => {
                    f.has_loose_bvar_in_range(start, end) || a.has_loose_bvar_in_range(start, end)
                }
                ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                    let body_has_loose = match shift_bvar_range(start, end) {
                        Some((next_start, next_end)) => {
                            body.has_loose_bvar_in_range(next_start, next_end)
                        }
                        None => false,
                    };
                    ty.has_loose_bvar_in_range(start, end) || body_has_loose
                }
                ExprKind::Let(_, ty, val, body, _) => {
                    let body_has_loose = match shift_bvar_range(start, end) {
                        Some((next_start, next_end)) => {
                            body.has_loose_bvar_in_range(next_start, next_end)
                        }
                        None => false,
                    };
                    ty.has_loose_bvar_in_range(start, end)
                        || val.has_loose_bvar_in_range(start, end)
                        || body_has_loose
                }
                ExprKind::Proj(_, _, e) => e.has_loose_bvar_in_range(start, end),
            }
        }

        // VERBATIM `infer_implicit` (subst.rs:560) — strict-mode wrapper over infer_implicit_n.
        pub fn infer_implicit(&self, strict: bool) -> Expr {
            self.infer_implicit_n(u32::MAX, strict)
        }

        // VERBATIM `infer_implicit_n` (subst.rs:567). `bd.info != BinderInfo::Default`
        // -> `bd.info != INFO_DEFAULT`; `BinderData::new(BinderInfo::Implicit, bd.mult)`
        // -> `BinderData::new(1, bd.mult)`.
        pub fn infer_implicit_n(&self, num_params: u32, strict: bool) -> Expr {
            if num_params == 0 {
                return self.clone();
            }
            match &self.kind {
                ExprKind::Pi(bd, domain, body) => {
                    let new_body = body.infer_implicit_n(num_params - 1, strict);
                    if bd.info != INFO_DEFAULT {
                        // Already non-explicit — keep as-is, just update body
                        Expr::pi(*bd, (**domain).clone(), new_body)
                    } else if has_loose_bvars_in_domain(&new_body, 0, strict) {
                        // BVar 0 appears in a subsequent domain — mark implicit
                        Expr::pi(BinderData::new(1, bd.mult), (**domain).clone(), new_body)
                    } else {
                        Expr::pi(*bd, (**domain).clone(), new_body)
                    }
                }
                _ => self.clone(),
            }
        }
    }

    // VERBATIM `has_loose_bvars_in_domain` (expr/mod.rs:140). `bd.info == BinderInfo::Default`
    // -> `bd.info == INFO_DEFAULT`.
    pub(crate) fn has_loose_bvars_in_domain(b: &Expr, vidx: u32, strict: bool) -> bool {
        match &b.kind {
            ExprKind::Pi(bd, domain, body) => {
                if domain.has_loose_bvar(vidx) {
                    if bd.info == INFO_DEFAULT {
                        // vidx appears in an explicit argument's domain
                        return true;
                    } else if has_loose_bvars_in_domain(body, 0, strict) {
                        // Transitivity
                        return true;
                    }
                }
                has_loose_bvars_in_domain(body, vidx + 1, strict)
            }
            _ => {
                if !strict {
                    b.has_loose_bvar(vidx)
                } else {
                    false
                }
            }
        }
    }

    // ════════════════════════════════════════════════════════════════════════════
    // MODELED InductiveType — the struct build_recursor_type reads via `all_types`:
    //   .name (ctor_motive_index / this_motive_idx / field_motive_index),
    //   .type_ (count_pi_args / collect_pi_binders_after_skip for the motive-type builder),
    //   .constructors (ctor_path_data — HIT check, modeled to return None).
    // ════════════════════════════════════════════════════════════════════════════

    #[derive(Clone, Debug)]
    pub struct Ctor {
        pub name: Name,
        pub type_: Expr,
    }

    #[derive(Clone, Debug)]
    pub struct InductiveType {
        pub name: Name,
        pub type_: Expr,
        pub constructors: Vec<Ctor>,
    }

    // VERBATIM `ind_const_with_levels` (inductive_fixed_indices.rs:266).
    pub(crate) fn ind_const_with_levels(name: &Name, level_params: &[Name]) -> Expr {
        // VERBATIM `level_params.iter().map(|p| Level::param(p.clone())).collect()` —
        // lowered to the equivalent push loop (identical: one Level::Param per param).
        let mut levels: Vec<Level> = Vec::new();
        {
            let mut _i = 0usize;
            while _i < level_params.len() {
                levels.push(Level::Param(level_params[_i]));
                _i += 1;
            }
        }
        Expr::const_(*name, levels)
    }

    // VERBATIM `get_return_type` (inductive/mod.rs:650) — walk past the Pi telescope.
    pub(crate) fn get_return_type(expr: &Expr) -> &Expr {
        let mut current = expr;
        while let ExprKind::Pi(_, _, body) = &current.kind {
            current = body;
        }
        current
    }

    // ════════════════════════════════════════════════════════════════════════════
    // The Environment-method PILLARS transcribed as free fns over the modeled types.
    // ════════════════════════════════════════════════════════════════════════════

    #[inline]
    fn usize_to_u32(value: usize) -> u32 {
        u32::try_from(value).unwrap_or(u32::MAX)
    }

    // VERBATIM `count_pi_args` (inductive/mod.rs:608).
    pub(crate) fn count_pi_args(expr: &Expr) -> u32 {
        let mut count = 0u32;
        let mut current = expr;
        while let ExprKind::Pi(_, _, body) = &current.kind {
            count = count.saturating_add(1);
            current = body;
        }
        count
    }

    // MODELED `consume_type_annotations` (inductive/mod.rs:676). The real fn peels
    // optParam/autoParam (arity-2) and outParam/semiOutParam (arity-1) wrapper Consts by
    // comparing `name.to_string()` to those literals. No synthetic domain in this slice uses
    // a reserved wrapper Name, so the scan is a faithful no-op returning its input unchanged.
    // (Const-name interning `to_string` is off this fn's construction/lift/read path.)
    pub(crate) fn consume_type_annotations(expr: &Expr) -> &Expr {
        expr
    }

    // VERBATIM `field_motive_index` (inductive_recursor_types.rs:45).
    pub(crate) fn field_motive_index(field_ty: &Expr, all_types: &[InductiveType]) -> usize {
        let ret_ty = get_return_type(field_ty);
        let head = ret_ty.get_app_fn();
        if let ExprKind::Const(name, _) = &head.kind {
            // VERBATIM `for (idx, ind_type) in all_types.iter().enumerate()` — index loop.
            let mut idx = 0usize;
            while idx < all_types.len() {
                if &all_types[idx].name == name {
                    return idx;
                }
                idx += 1;
            }
        }
        0
    }

    // VERBATIM `ctor_motive_index` (inductive_recursor_types.rs:28).
    pub(crate) fn ctor_motive_index(ctor_name: &Name, all_types: &[InductiveType]) -> usize {
        // VERBATIM `for (idx, ind_type) in all_types.iter().enumerate()` — index loops.
        let mut idx = 0usize;
        while idx < all_types.len() {
            let mut ci = 0usize;
            while ci < all_types[idx].constructors.len() {
                if &all_types[idx].constructors[ci].name == ctor_name {
                    return idx;
                }
                ci += 1;
            }
            idx += 1;
        }
        0
    }

    // MODELED `ctor_path_data` (inductive_recursor_minor.rs:175). The real fn returns
    // `Some((left,right))` ONLY when a ctor's return type is `ExprKind::CubicalPath{..}`
    // (a HIT path ctor). The modeled ExprKind has NO CubicalPath variant and every test
    // inductive is non-HIT, so this ALWAYS returns None — the is_path / path-minor branch
    // is provably dead on every verified case.
    pub(crate) fn ctor_path_data(
        _ctor_name: &Name,
        _all_types: &[InductiveType],
    ) -> Option<(Expr, Expr)> {
        None
    }

    // VERBATIM `count_pi_binders` (inductive_recursor_rules.rs:24).
    pub(crate) fn count_pi_binders(expr: &Expr) -> usize {
        let mut count = 0;
        let mut current = expr;
        while let ExprKind::Pi(_, _, body) = &current.kind {
            count += 1;
            current = body;
        }
        count
    }

    // VERBATIM `collect_pi_domains` (inductive_recursor_rules.rs:39).
    pub(crate) fn collect_pi_domains(expr: &Expr) -> Vec<(BinderData, Expr)> {
        let mut domains = Vec::new();
        let mut current = expr;
        while let ExprKind::Pi(bi, domain, body) = &current.kind {
            domains.push((*bi, (**domain).clone()));
            current = body;
        }
        domains
    }

    // VERBATIM `collect_pi_binders` (inductive_recursor.rs:988). The real collects through
    // `consume_type_annotations(domain)` (modeled no-op).
    pub(crate) fn collect_pi_binders(ty: &Expr, count: u32) -> Vec<(BinderData, Expr)> {
        let mut result = Vec::new();
        let mut current = ty.clone();
        let mut collected = 0u32;
        while collected < count {
            if let ExprKind::Pi(bi, domain, codomain) = &current.kind {
                result.push((*bi, consume_type_annotations(domain).clone()));
                current = (**codomain).clone();
                collected += 1;
            } else {
                break;
            }
        }
        result
    }

    // VERBATIM `collect_pi_binders_after_skip` (inductive_recursor_types.rs:510).
    pub(crate) fn collect_pi_binders_after_skip(
        ty: &Expr,
        skip: u32,
        count: u32,
    ) -> Vec<(BinderData, Expr)> {
        let mut current = ty.clone();
        {
            let mut _s = 0u32;
            while _s < skip {
                if let ExprKind::Pi(_, _, body) = &current.kind {
                    current = (**body).clone();
                }
                _s += 1;
            }
        }
        collect_pi_binders(&current, count)
    }

    // VERBATIM `get_constructor_return_indices` (inductive_recursor.rs:951).
    pub(crate) fn get_constructor_return_indices(ctor_ty: &Expr, num_params: u32) -> Vec<Expr> {
        let mut current = ctor_ty.clone();
        while let ExprKind::Pi(_, _, codomain) = &current.kind {
            current = (**codomain).clone();
        }
        let mut args: Vec<Expr> = Vec::new();
        while let ExprKind::App(f, a) = &current.kind {
            args.push((**a).clone());
            current = (**f).clone();
        }
        // args collected rightmost-first; VERBATIM `args.reverse()` then
        // `.into_iter().skip(num_params).collect()` — single forward emit over the reversed
        // (source-order) indices, skipping the first num_params.
        let np = num_params as usize;
        let n = args.len();
        let mut out: Vec<Expr> = Vec::new();
        {
            let mut s = 0usize;
            while s < n {
                if s >= np {
                    out.push(args[n - 1 - s].clone());
                }
                s += 1;
            }
        }
        out
    }

    // VERBATIM `remap_residual_index_bvars_for_minor` (inductive_recursor_rules.rs:94).
    pub(crate) fn remap_residual_index_bvars_for_minor(
        expr: &Expr,
        field_idx: usize,
        nf: usize,
        ih_offset: usize,
        n_pis: usize,
    ) -> Expr {
        match &expr.kind {
            ExprKind::BVar(k) => {
                let k = *k as usize;
                let new_k = if k < n_pis {
                    k
                } else {
                    let ctor_k = k - n_pis;
                    if ctor_k < field_idx {
                        let field_j = field_idx - 1 - ctor_k;
                        ih_offset + nf - 1 - field_j + n_pis
                    } else {
                        let param_j = ctor_k - field_idx;
                        ih_offset + nf + 1 + param_j + n_pis
                    }
                };
                Expr::bvar(usize_to_u32(new_k))
            }
            ExprKind::App(f, a) => {
                let f2 = remap_residual_index_bvars_for_minor(f, field_idx, nf, ih_offset, n_pis);
                let a2 = remap_residual_index_bvars_for_minor(a, field_idx, nf, ih_offset, n_pis);
                Expr::app(f2, a2)
            }
            _ => expr.clone(),
        }
    }

    // ════════════════════════════════════════════════════════════════════════════
    // VERIFIED PILLAR — `build_minor_premise_type`, VERBATIM from
    // inductive_recursor_minor.rs:33 (already native==JIT verified). Reused here as the
    // per-ctor minor-premise slot filler; `BinderInfo::Default` -> `bi_default()`.
    // ════════════════════════════════════════════════════════════════════════════

    #[allow(clippy::too_many_arguments)]
    pub fn build_minor_premise_type(
        ind_name: &Name,
        ctor_name: &Name,
        num_fields: u32,
        recursive_flags: &[bool],
        field_types: &[Expr],
        num_params: u32,
        ind_level_params: &[Name],
        ctor_indices: &[Expr],
        num_motives: usize,
        conclusion_motive_idx: usize,
        all_types: &[InductiveType],
    ) -> Expr {
        // VERBATIM `recursive_flags.iter().filter(|&&b| b).count()` — explicit count loop.
        let mut num_ihs: usize = 0;
        {
            let mut _ci = 0usize;
            while _ci < recursive_flags.len() {
                if recursive_flags[_ci] {
                    num_ihs += 1;
                }
                _ci += 1;
            }
        }
        let num_fields = num_fields as usize;

        let conclusion_motive_bvar =
            num_fields + num_ihs + (num_motives - 1 - conclusion_motive_idx);

        let adjust_index_expr = |expr: Expr, ih_offset: usize| -> Expr {
            let mut adjusted = expr.lift(usize_to_u32(ih_offset));
            adjusted = adjusted.lift_from(usize_to_u32(ih_offset + num_fields), num_motives as u32);
            adjusted
        };

        // VERBATIM `ind_level_params.iter().map(|p| Level::param(p.clone())).collect()`.
        let mut ctor_levels: Vec<Level> = Vec::new();
        {
            let mut _pi = 0usize;
            while _pi < ind_level_params.len() {
                ctor_levels.push(Level::Param(ind_level_params[_pi]));
                _pi += 1;
            }
        }
        let mut ctor_app = Expr::const_(*ctor_name, ctor_levels);
        {
            let mut i: u32 = 0;
            while i < num_params {
                let param_depth =
                    num_fields + num_ihs + num_motives + (num_params as usize - 1 - i as usize);
                ctor_app = Expr::app(ctor_app, Expr::bvar(usize_to_u32(param_depth)));
                i += 1;
            }
        }
        {
            let mut i: usize = 0;
            while i < num_fields {
                let field_depth = (num_fields - 1 - i) + num_ihs;
                ctor_app = Expr::app(ctor_app, Expr::bvar(usize_to_u32(field_depth)));
                i += 1;
            }
        }

        let mut result = Expr::bvar(usize_to_u32(conclusion_motive_bvar));
        {
            let mut _ii = 0usize;
            while _ii < ctor_indices.len() {
                let adjusted = adjust_index_expr(ctor_indices[_ii].clone(), num_ihs);
                result = Expr::app(result, adjusted);
                _ii += 1;
            }
        }
        result = Expr::app(result, ctor_app);

        let mut ih_offset = 0usize;
        let mut _ri = recursive_flags.len();
        while _ri > 0 {
            _ri -= 1;
            let i = _ri;
            let is_recursive = recursive_flags[i];
            if is_recursive {
                let ihs_above = num_ihs - 1 - ih_offset;
                let field_depth = (num_fields - 1 - i) + ihs_above;

                let ih_motive_idx = match field_types.get(i) {
                    Some(ft) => field_motive_index(ft, all_types),
                    None => conclusion_motive_idx,
                };
                let motive_at_ih = num_fields + ihs_above + (num_motives - 1 - ih_motive_idx);

                let n_pis = match field_types.get(i) {
                    Some(ft) => count_pi_binders(ft),
                    None => 0,
                };

                let ih_motive = motive_at_ih + n_pis;
                let ih_field_depth = field_depth + n_pis;

                let mut ih_type = Expr::bvar(usize_to_u32(ih_motive));

                let field_ty = match field_types.get(i) {
                    Some(ft) => ft.clone(),
                    None => ind_const_with_levels(ind_name, ind_level_params),
                };
                let field_indices = get_constructor_return_indices(&field_ty, num_params);
                {
                    let mut _fi = 0usize;
                    while _fi < field_indices.len() {
                        let remapped = remap_residual_index_bvars_for_minor(
                            &field_indices[_fi],
                            i,
                            num_fields,
                            ihs_above,
                            n_pis,
                        );
                        ih_type = Expr::app(ih_type, remapped);
                        _fi += 1;
                    }
                }

                let mut major = Expr::bvar(usize_to_u32(ih_field_depth));
                {
                    let mut _k = n_pis;
                    while _k > 0 {
                        _k -= 1;
                        major = Expr::app(major, Expr::bvar(usize_to_u32(_k)));
                    }
                }
                ih_type = Expr::app(ih_type, major);

                let pi_domains = match field_types.get(i) {
                    Some(ft) => collect_pi_domains(ft),
                    None => Vec::new(),
                };
                {
                    let mut _pd = pi_domains.len();
                    while _pd > 0 {
                        _pd -= 1;
                        let k = _pd;
                        let (bi, domain) = &pi_domains[k];
                        let remapped = remap_residual_index_bvars_for_minor(
                            domain, i, num_fields, ihs_above, k,
                        );
                        ih_type = Expr::pi(*bi, remapped, ih_type);
                    }
                }

                result = Expr::pi(bi_default(), ih_type, result);
                ih_offset += 1;
            }
        }

        {
            let mut _fb = num_fields;
            while _fb > 0 {
                _fb -= 1;
                let i = _fb;
                let field_ty = match field_types.get(i) {
                    Some(ft) => ft.clone(),
                    None => ind_const_with_levels(ind_name, ind_level_params),
                };
                let lifted_field_ty = field_ty.lift_from(usize_to_u32(i), num_motives as u32);
                result = Expr::pi(bi_default(), lifted_field_ty, result);
            }
        }

        result
    }

    // ════════════════════════════════════════════════════════════════════════════
    // THE SOUNDNESS-CRITICAL FN — `build_recursor_type`, VERBATIM from
    // inductive_recursor_types.rs:89. `&self` (Environment) is dropped: on this path it is
    // used ONLY to reach the associated helper fns (`self.collect_pi_binders`,
    // `self.collect_pi_binders_after_skip`, `self.build_minor_premise_type`), all transcribed
    // above. The `build_ind_app` closure is preserved verbatim.
    // `BinderInfo::Default`/`::Implicit` -> `bi_default()`/`bi_implicit()`.
    //
    // A CtorInfo is `(ctor_name, num_fields, recursive_flags, field_types, return_indices)`.
    // ════════════════════════════════════════════════════════════════════════════

    #[derive(Clone, Debug)]
    pub struct CtorInfo {
        pub name: Name,
        pub num_fields: u32,
        pub recursive_flags: Vec<bool>,
        pub field_types: Vec<Expr>,
        pub return_indices: Vec<Expr>,
    }

    #[allow(clippy::too_many_arguments)]
    pub fn build_recursor_type(
        ind_name: &Name,
        ind_type: &Expr,
        num_params: u32,
        num_indices: u32,
        motive_univ_name: Option<&Name>,
        ind_level_params: &[Name],
        ctor_infos: &[CtorInfo],
        all_types: &[InductiveType],
    ) -> Expr {
        // Prop-only elimination: motive targets Sort 0 (Prop). Large elimination: Sort u.
        // VERBATIM `match motive_univ_name { Some(name) => Level::param(name.clone()),
        //   None => Level::zero() }`.
        let motive_univ = match motive_univ_name {
            Some(name) => Level::Param(*name),
            None => Level::Zero,
        };
        let ind_const = ind_const_with_levels(ind_name, ind_level_params);

        let num_motives = all_types.len();

        // Collect parameter and index binders from the inductive type.
        let param_binders = collect_pi_binders(ind_type, num_params);
        let mut current = ind_type.clone();
        {
            let mut _p = 0u32;
            while _p < num_params {
                if let ExprKind::Pi(_, _, body) = &current.kind {
                    current = (**body).clone();
                }
                _p += 1;
            }
        }
        let index_binders = collect_pi_binders(&current, num_indices);
        let num_minors = ctor_infos.len();

        // Helper to build Ind applied to params and indices at given depths (VERBATIM closure).
        let build_ind_app = |param_offset: u32, index_offset: u32| -> Expr {
            let mut ind_app = ind_const.clone();
            {
                let mut i: u32 = 0;
                while i < num_params {
                    let idx = param_offset + (num_params - 1 - i);
                    ind_app = Expr::app(ind_app, Expr::bvar(idx));
                    i += 1;
                }
            }
            {
                let mut i: u32 = 0;
                while i < num_indices {
                    let idx = index_offset + (num_indices - 1 - i);
                    ind_app = Expr::app(ind_app, Expr::bvar(idx));
                    i += 1;
                }
            }
            ind_app
        };

        // Build motive types for ALL types in the mutual block.
        // Each motive: Π indices_i, Π (major : Type_i indices_i), Sort u.
        let mut motive_types: Vec<Expr> = Vec::with_capacity(num_motives);
        {
            let mut _t = 0usize;
            while _t < all_types.len() {
                let t = &all_types[_t];
                let t_const = ind_const_with_levels(&t.name, ind_level_params);
                let t_type_arity = count_pi_args(&t.type_);
                let t_num_indices = t_type_arity.saturating_sub(num_params);
                let t_index_binders =
                    collect_pi_binders_after_skip(&t.type_, num_params, t_num_indices);

                let mut mtype = Expr::from_kind(ExprKind::Sort(motive_univ.clone()));
                // major type: Type_i params indices
                let mut major_ty_for_motive = t_const.clone();
                {
                    let mut i: u32 = 0;
                    while i < num_params {
                        let idx = t_num_indices + (num_params - 1 - i);
                        major_ty_for_motive = Expr::app(major_ty_for_motive, Expr::bvar(idx));
                        i += 1;
                    }
                }
                {
                    let mut i: u32 = 0;
                    while i < t_num_indices {
                        let idx = t_num_indices - 1 - i;
                        major_ty_for_motive = Expr::app(major_ty_for_motive, Expr::bvar(idx));
                        i += 1;
                    }
                }
                mtype = Expr::pi(bi_default(), major_ty_for_motive, mtype);
                // Add the index binders, outermost (idx_0) last. Each I_i placed UNCHANGED
                // (see the real comment: the standalone-motive and inductive-telescope
                // contexts are identical; a previous over-shift was the multi-index bug).
                // VERBATIM `for (binder_info, index_ty) in t_index_binders.iter().rev()`.
                {
                    let mut _ib = t_index_binders.len();
                    while _ib > 0 {
                        _ib -= 1;
                        let (binder_info, index_ty) = &t_index_binders[_ib];
                        mtype = Expr::pi(*binder_info, index_ty.clone(), mtype);
                    }
                }
                motive_types.push(mtype);
                _t += 1;
            }
        }

        // Determine which motive index corresponds to ind_name.
        // VERBATIM `all_types.iter().position(|t| &t.name == ind_name).unwrap_or(0)`.
        let this_motive_idx = {
            let mut found: Option<usize> = None;
            let mut _i = 0usize;
            while _i < all_types.len() {
                if &all_types[_i].name == ind_name {
                    found = Some(_i);
                    break;
                }
                _i += 1;
            }
            match found {
                Some(v) => v,
                None => 0,
            }
        };

        // Build minor premise types. Each entry is (type, is_path).
        let mut minor_types: Vec<(Expr, bool)> = Vec::new();
        {
            let mut minor_self_idx = 0usize;
            while minor_self_idx < ctor_infos.len() {
                let ci = &ctor_infos[minor_self_idx];
                let ctor_name = &ci.name;
                let num_fields = ci.num_fields;
                let recursive_flags = &ci.recursive_flags;
                let field_types = &ci.field_types;
                let return_indices = &ci.return_indices;

                let ctor_motive_idx = ctor_motive_index(ctor_name, all_types);
                match ctor_path_data(ctor_name, all_types) {
                    Some(_lr) => {
                        // Provably dead on every non-HIT test case (ctor_path_data == None).
                        // Path-minor construction is NOT modeled; unreachable here.
                        minor_types.push((Expr::bvar(0), true));
                    }
                    None => {
                        let minor_ty = build_minor_premise_type(
                            ind_name,
                            ctor_name,
                            num_fields,
                            recursive_flags,
                            field_types,
                            num_params,
                            ind_level_params,
                            return_indices,
                            num_motives,
                            ctor_motive_idx,
                            all_types,
                        );
                        minor_types.push((minor_ty, false));
                    }
                }
                minor_self_idx += 1;
            }
        }

        // Build the full rec type from inside out:
        // params → motives → minors → indices → major → motive_i indices major
        let this_motive_bvar = usize_to_u32(
            num_minors + num_indices as usize + 1 + (num_motives - 1 - this_motive_idx),
        );
        let mut result_ty = Expr::bvar(this_motive_bvar);
        {
            let mut i: u32 = 0;
            while i < num_indices {
                let idx = usize_to_u32(num_indices as usize - i as usize);
                result_ty = Expr::app(result_ty, Expr::bvar(idx));
                i += 1;
            }
        }
        result_ty = Expr::app(result_ty, Expr::bvar(0)); // major

        // Add major premise: (t : Ind params indices) → result.
        let major_ty = build_ind_app(num_indices + num_minors as u32 + num_motives as u32, 0);
        result_ty = Expr::pi(bi_default(), major_ty, result_ty);

        // Add index binders. Param-referencing BVars shifted by (num_minors + num_motives).
        // VERBATIM `for (i, (binder_info, index_ty)) in index_binders.iter().enumerate().rev()`.
        let extra = usize_to_u32(num_minors + num_motives);
        {
            let mut _ix = index_binders.len();
            while _ix > 0 {
                _ix -= 1;
                let i = _ix;
                let (binder_info, index_ty) = &index_binders[i];
                let lifted_index_ty = if extra > 0 {
                    index_ty.lift_from(i as u32, extra)
                } else {
                    index_ty.clone()
                };
                result_ty = Expr::pi(*binder_info, lifted_index_ty, result_ty);
            }
        }

        // Add minor premises (reverse order). Each minor's BVars reference the motives; a
        // non-path minor at index i is lifted by i. Path minors (dead here) skip the lift.
        // VERBATIM `for (i, (minor_ty, is_path)) in minor_types.iter().enumerate().rev()`.
        {
            let mut _m = minor_types.len();
            while _m > 0 {
                _m -= 1;
                let i = _m;
                let (minor_ty, is_path) = &minor_types[i];
                let lifted_minor_ty = if *is_path || i == 0 {
                    minor_ty.clone()
                } else {
                    minor_ty.lift(usize_to_u32(i))
                };
                result_ty = Expr::pi(bi_default(), lifted_minor_ty, result_ty);
            }
        }

        // Add motives (innermost motive last). Motive_i lifted by i.
        // VERBATIM `for (i, mtype) in motive_types.iter().enumerate().rev()`.
        {
            let mut _mo = motive_types.len();
            while _mo > 0 {
                _mo -= 1;
                let i = _mo;
                let mtype = &motive_types[i];
                let lifted_mtype = if i > 0 {
                    mtype.lift(usize_to_u32(i))
                } else {
                    mtype.clone()
                };
                result_ty = Expr::pi(bi_implicit(), lifted_mtype, result_ty);
            }
        }

        // Add parameters (outermost).
        // VERBATIM `for (_i, (binder_info, param_ty)) in param_binders.iter().enumerate().rev()`.
        {
            let mut _pb = param_binders.len();
            while _pb > 0 {
                _pb -= 1;
                let (binder_info, param_ty) = &param_binders[_pb];
                result_ty = Expr::pi(*binder_info, param_ty.clone(), result_ty);
            }
        }

        // infer_implicit: mark explicit binders Implicit when their bvar appears in a
        // subsequent Pi domain (strict). Ref: lean4-ref/src/kernel/inductive.cpp:767.
        result_ty = result_ty.infer_implicit(true);

        result_ty
    }

    // ════════════════════════════════════════════════════════════════════════════
    // VERBATIM `remap_residual_index_bvars` (inductive_recursor_rules.rs:51) — the
    // NON-minor variant (distinct arithmetic from _for_minor), used by the rule RHS.
    // ════════════════════════════════════════════════════════════════════════════

    pub(crate) fn remap_residual_index_bvars(
        expr: &Expr,
        field_idx: usize,
        np: usize,
        nf: usize,
        n_minors: usize,
        nm: usize,
        n_pis: usize,
    ) -> Expr {
        match &expr.kind {
            ExprKind::BVar(k) => {
                let k = *k as usize;
                let new_k = if k < n_pis {
                    k
                } else {
                    let ctor_k = k - n_pis;
                    if ctor_k < field_idx {
                        let field_j = field_idx - 1 - ctor_k;
                        nf - 1 - field_j + n_pis
                    } else {
                        let param_j = np - 1 - (ctor_k - field_idx);
                        nf + n_minors + nm + np - 1 - param_j + n_pis
                    }
                };
                Expr::bvar(usize_to_u32(new_k))
            }
            ExprKind::App(f, a) => {
                let f2 = remap_residual_index_bvars(f, field_idx, np, nf, n_minors, nm, n_pis);
                let a2 = remap_residual_index_bvars(a, field_idx, np, nf, n_minors, nm, n_pis);
                Expr::app(f2, a2)
            }
            _ => expr.clone(),
        }
    }

    // ════════════════════════════════════════════════════════════════════════════
    // THE INTERNING BOUNDARY (MODELED) — `Name::from_string(&format!("{name}.rec"))`.
    // The real path formats the hierarchical Name via core::fmt and re-interns the
    // dotted string (split('.') / parse::<u64> / Arc<str> — see name.rs:557). The
    // frontend cannot lower that machinery (probe-pinned: &str constants as call args,
    // String deref fat pointers, str::Bytes element types, format_args! pieces), so
    // the map `head-name -> rec-name` is passed in PRE-INTERNED as `&[RecPair]` and
    // looked up by the established slice-scan pattern. The fallback (return *fallback)
    // is PROVABLY DEAD on the verified path: a field is only flagged recursive when
    // its return head is a block inductive (get_recursive_field_flags below), and the
    // harness table covers exactly the block's types.
    // ════════════════════════════════════════════════════════════════════════════

    #[derive(Clone, Copy, Debug)]
    #[repr(C)]
    pub struct RecPair {
        pub ind: Name,
        pub rec: Name,
    }

    pub(crate) fn rec_name_of(head: &Name, rec_pairs: &[RecPair], fallback: &Name) -> Name {
        let mut i = 0usize;
        while i < rec_pairs.len() {
            if &rec_pairs[i].ind == head {
                return rec_pairs[i].rec;
            }
            i += 1;
        }
        *fallback
    }

    // ════════════════════════════════════════════════════════════════════════════
    // THE SOUNDNESS-CRITICAL FN — `build_recursor_rule_rhs`, VERBATIM from
    // inductive_recursor_rules.rs:148, INCLUDING the `all_types.len() > 1` MUTUAL
    // branch (get_return_type + get_app_fn head walk + `{head}.rec` derivation, the
    // latter through the modeled pre-interned table). `&self` dropped (used only to
    // reach get_constructor_return_indices, transcribed as a free fn).
    // `BinderInfo::Default` -> bi_default(); SmallVec -> Vec (modeled, see header).
    // ════════════════════════════════════════════════════════════════════════════

    #[allow(clippy::too_many_arguments)]
    pub fn build_recursor_rule_rhs(
        rec_name: &Name,
        rec_level_params: &[Name],
        num_params: u32,
        num_motives: u32,
        num_indices: u32,
        num_fields: u32,
        recursive_flags: &[bool],
        field_types: &[Expr],
        num_ctors: usize,
        ctor_idx: usize,
        eliminator_type: &Expr,
        all_types: &[InductiveType],
        rec_pairs: &[RecPair],
    ) -> Expr {
        let nf = num_fields as usize;
        let np = num_params as usize;
        let nm = num_motives as usize;
        let n_minors = num_ctors; // num_minors == num_ctors for standard rec
        let total_binders = np + nm + n_minors + nf;

        // minor for ctor_idx (minors go minor_0 outermost .. minor_{n-1} innermost).
        let minor_bvar = usize_to_u32(nf + n_minors - 1 - ctor_idx);
        let mut body = Expr::bvar(minor_bvar);

        // Apply all fields to minor: minor field_0 .. field_{nf-1}.
        // VERBATIM `for i in 0..nf` — ascending while loop.
        {
            let mut i: usize = 0;
            while i < nf {
                let field_bvar = usize_to_u32(nf - 1 - i);
                body = Expr::app(body, Expr::bvar(field_bvar));
                i += 1;
            }
        }

        // rec_levels = rec_level_params.iter().map(|n| Level::param(n.clone())).collect()
        // VERBATIM — explicit push loop (SmallVec -> Vec, modeled).
        let mut rec_levels: Vec<Level> = Vec::new();
        {
            let mut _li = 0usize;
            while _li < rec_level_params.len() {
                rec_levels.push(Level::Param(rec_level_params[_li]));
                _li += 1;
            }
        }

        // Apply IH for each recursive field.
        // VERBATIM `for (i, &is_recursive) in recursive_flags.iter().enumerate()`.
        {
            let mut i: usize = 0;
            while i < recursive_flags.len() {
                let is_recursive = recursive_flags[i];
                if is_recursive {
                    let n_pis = match field_types.get(i) {
                        Some(ft) => count_pi_binders(ft),
                        None => 0,
                    };
                    let shift = n_pis;

                    // THE MUTUAL BRANCH — VERBATIM control flow: for a mutual block the
                    // IH names the recursor of the type the field RETURNS TO
                    // (Lean 4 inductive.cpp:738); the `Name::from_string(format!("{name}.rec"))`
                    // step is the modeled table lookup (see rec_name_of).
                    let ih_rec_name = if all_types.len() > 1 {
                        match field_types.get(i) {
                            Some(field_ty) => {
                                let ret_ty = get_return_type(field_ty);
                                let head = ret_ty.get_app_fn();
                                match &head.kind {
                                    ExprKind::Const(name, _) => {
                                        rec_name_of(name, rec_pairs, rec_name)
                                    }
                                    _ => *rec_name,
                                }
                            }
                            None => *rec_name,
                        }
                    } else {
                        *rec_name
                    };

                    // ih = ih_rec@{levels} params motives minors [indices] (field xs)
                    let mut ih = Expr::const_(ih_rec_name, rec_levels.clone());

                    // Apply params (outermost group). VERBATIM `for j in 0..np`.
                    {
                        let mut j: usize = 0;
                        while j < np {
                            let param_bvar = usize_to_u32(total_binders - 1 - j + shift);
                            ih = Expr::app(ih, Expr::bvar(param_bvar));
                            j += 1;
                        }
                    }
                    // Apply motives.
                    {
                        let mut j: usize = 0;
                        while j < nm {
                            let motive_bvar = usize_to_u32(nf + n_minors + nm - 1 - j + shift);
                            ih = Expr::app(ih, Expr::bvar(motive_bvar));
                            j += 1;
                        }
                    }
                    // Apply minors.
                    {
                        let mut j: usize = 0;
                        while j < n_minors {
                            let minor_bvar_idx = usize_to_u32(nf + n_minors - 1 - j + shift);
                            ih = Expr::app(ih, Expr::bvar(minor_bvar_idx));
                            j += 1;
                        }
                    }

                    // Apply index arguments for indexed inductives.
                    if num_indices > 0 {
                        if let Some(field_ty) = field_types.get(i) {
                            let indices = get_constructor_return_indices(field_ty, num_params);
                            {
                                let mut _ix = 0usize;
                                while _ix < indices.len() {
                                    let remapped = remap_residual_index_bvars(
                                        &indices[_ix],
                                        i,
                                        np,
                                        nf,
                                        n_minors,
                                        nm,
                                        n_pis,
                                    );
                                    ih = Expr::app(ih, remapped);
                                    _ix += 1;
                                }
                            }
                        }
                    }

                    // Apply the recursive field as major premise.
                    let mut major = Expr::bvar(usize_to_u32(nf - 1 - i + shift));
                    // VERBATIM `for k in (0..n_pis).rev()` — descending while loop.
                    {
                        let mut _k = n_pis;
                        while _k > 0 {
                            _k -= 1;
                            major = Expr::app(major, Expr::bvar(usize_to_u32(_k)));
                        }
                    }
                    ih = Expr::app(ih, major);

                    // Wrap IH in lambda binders for Pi-bound variables (reflexive fields).
                    let pi_domains = match field_types.get(i) {
                        Some(ft) => collect_pi_domains(ft),
                        None => Vec::new(),
                    };
                    // VERBATIM `for (k, (bi, domain)) in pi_domains.iter().enumerate().rev()`.
                    {
                        let mut _pd = pi_domains.len();
                        while _pd > 0 {
                            _pd -= 1;
                            let k = _pd;
                            let (bi, domain) = &pi_domains[k];
                            let remapped =
                                remap_residual_index_bvars(domain, i, np, nf, n_minors, nm, k);
                            ih = Expr::lam(*bi, remapped, ih);
                        }
                    }

                    body = Expr::app(body, ih);
                }
                i += 1;
            }
        }

        // Extract actual domain types from the eliminator type's Pi binders:
        // Π params. Π motives. Π minors. Π rest...
        let dummy_ty = Expr::sort(Level::Zero);
        let mut elim_cursor = eliminator_type.clone();
        let mut param_domain_types: Vec<Expr> = Vec::new();
        {
            let mut _p = 0usize;
            while _p < np {
                match &elim_cursor.kind {
                    ExprKind::Pi(_, domain, body) => {
                        param_domain_types.push((**domain).clone());
                        elim_cursor = (**body).clone();
                    }
                    _ => {
                        param_domain_types.push(dummy_ty.clone());
                    }
                }
                _p += 1;
            }
        }
        let mut motive_domain_types: Vec<Expr> = Vec::new();
        {
            let mut _m = 0usize;
            while _m < nm {
                match &elim_cursor.kind {
                    ExprKind::Pi(_, domain, body) => {
                        motive_domain_types.push((**domain).clone());
                        elim_cursor = (**body).clone();
                    }
                    _ => {
                        motive_domain_types.push(dummy_ty.clone());
                    }
                }
                _m += 1;
            }
        }
        let mut minor_domain_types: Vec<Expr> = Vec::new();
        {
            let mut _mn = 0usize;
            while _mn < n_minors {
                match &elim_cursor.kind {
                    ExprKind::Pi(_, domain, body) => {
                        minor_domain_types.push((**domain).clone());
                        elim_cursor = (**body).clone();
                    }
                    _ => {
                        minor_domain_types.push(dummy_ty.clone());
                    }
                }
                _mn += 1;
            }
        }

        // Wrap body in λ params. λ motives. λ minors. λ fields. body
        let mut result = body;

        // Fields (innermost) — lift field types by (nm + n_minors) at depth i.
        let lift_amount = usize_to_u32(nm + n_minors);
        // VERBATIM `for i in (0..nf).rev()` — descending while loop.
        {
            let mut _fi = nf;
            while _fi > 0 {
                _fi -= 1;
                let i = _fi;
                let field_ty = match field_types.get(i) {
                    Some(ft) => {
                        if lift_amount > 0 {
                            ft.lift_from(i as u32, lift_amount)
                        } else {
                            ft.clone()
                        }
                    }
                    None => dummy_ty.clone(),
                };
                result = Expr::lam(bi_default(), field_ty, result);
            }
        }
        // Minors (innermost minor first wrapping outward).
        {
            let mut _mi = minor_domain_types.len();
            while _mi > 0 {
                _mi -= 1;
                result = Expr::lam(bi_default(), minor_domain_types[_mi].clone(), result);
            }
        }
        // Motives.
        {
            let mut _mo = motive_domain_types.len();
            while _mo > 0 {
                _mo -= 1;
                result = Expr::lam(bi_default(), motive_domain_types[_mo].clone(), result);
            }
        }
        // Params (innermost param first wrapping outward).
        {
            let mut _pa = param_domain_types.len();
            while _pa > 0 {
                _pa -= 1;
                result = Expr::lam(bi_default(), param_domain_types[_pa].clone(), result);
            }
        }

        result
    }

    // ════════════════════════════════════════════════════════════════════════════
    // NEW IN-MODULE — the CtorInfo derivation from REAL ctor Pi-telescopes.
    // VERBATIM from inductive_recursor.rs; `HashSet<&Name>` -> Vec<Name> + scan
    // (pure membership semantics — exact model), `self` dropped.
    // ════════════════════════════════════════════════════════════════════════════

    // Modeled `ind_name_set.contains(name)` — linear scan over the block's names.
    pub(crate) fn name_in_set(name: &Name, ind_name_set: &[Name]) -> bool {
        let mut i = 0usize;
        while i < ind_name_set.len() {
            if &ind_name_set[i] == name {
                return true;
            }
            i += 1;
        }
        false
    }

    // VERBATIM `field_is_eliminably_recursive` (inductive_recursor.rs:902): a field is
    // *eliminably* recursive iff, after stripping leading Pi binders, the HEAD of its
    // return type is one of the block inductives.
    pub(crate) fn field_is_eliminably_recursive(field_ty: &Expr, ind_name_set: &[Name]) -> bool {
        let ret_ty = get_return_type(field_ty);
        let head = ret_ty.get_app_fn();
        // VERBATIM `matches!(&head.kind, ExprKind::Const(name, _) if ind_name_set.contains(name))`.
        match &head.kind {
            ExprKind::Const(name, _) => name_in_set(name, ind_name_set),
            _ => false,
        }
    }

    // VERBATIM `get_recursive_field_flags` (inductive_recursor.rs:877). For mutual
    // inductives, a field is recursive if it (eliminably) mentions ANY type in the block.
    pub(crate) fn get_recursive_field_flags(
        ctor_ty: &Expr,
        ind_name_set: &[Name],
        num_params: u32,
    ) -> Vec<bool> {
        let mut flags = Vec::new();
        let mut current = ctor_ty.clone();
        let mut arg_count = 0u32;

        while let ExprKind::Pi(_, domain, codomain) = &current.kind {
            if arg_count >= num_params {
                flags.push(field_is_eliminably_recursive(domain, ind_name_set));
            }
            current = (**codomain).clone();
            arg_count += 1;
        }
        flags
    }

    // VERBATIM `get_constructor_field_types` (inductive_recursor.rs:915) — field types
    // after skipping parameters, through consume_type_annotations (modeled no-op).
    pub(crate) fn get_constructor_field_types(ctor_ty: &Expr, num_params: u32) -> Vec<Expr> {
        let mut types = Vec::new();
        let mut current = ctor_ty.clone();
        let mut arg_count = 0u32;

        while let ExprKind::Pi(_, domain, codomain) = &current.kind {
            if arg_count >= num_params {
                types.push(consume_type_annotations(domain).clone());
            }
            current = (**codomain).clone();
            arg_count += 1;
        }
        types
    }

    // VERBATIM `compute_ctor_infos` (inductive_recursor.rs:34). The `decl` is passed as
    // its two read fields (types via `all_types`, num_params); ind_name_set is built by
    // the caller ONCE per block (`decl.types.iter().map(|t| &t.name).collect()` — push
    // loop) and threaded through, preserving the once-per-block construction.
    pub(crate) fn compute_ctor_infos(
        ind_type: &InductiveType,
        ind_name_set: &[Name],
        num_params: u32,
    ) -> Vec<CtorInfo> {
        let mut ctor_infos: Vec<CtorInfo> = Vec::with_capacity(ind_type.constructors.len());
        // VERBATIM `for ctor in &ind_type.constructors` — index loop.
        {
            let mut _c = 0usize;
            while _c < ind_type.constructors.len() {
                let ctor = &ind_type.constructors[_c];
                let ctor_arity = count_pi_args(&ctor.type_);
                let num_fields = ctor_arity.saturating_sub(num_params);
                let recursive_flags =
                    get_recursive_field_flags(&ctor.type_, ind_name_set, num_params);
                let field_types = get_constructor_field_types(&ctor.type_, num_params);
                let return_indices = get_constructor_return_indices(&ctor.type_, num_params);
                ctor_infos.push(CtorInfo {
                    name: ctor.name,
                    num_fields,
                    recursive_flags,
                    field_types,
                    return_indices,
                });
                _c += 1;
            }
        }
        ctor_infos
    }

    // ════════════════════════════════════════════════════════════════════════════
    // NEW IN-MODULE — the MUTUAL RECURSOR ASSEMBLY, VERBATIM the non-HIT path of
    // `build_recursor` (inductive_recursor.rs:66) + the `minor_idx_offset`
    // computation from its caller (inductive_builder.rs:322). Produces, for the
    // block's type `which`: the full recursor TYPE (sel == 0) or the iota-rule RHS
    // of that type's ctor j (sel == 1 + j). prop_only/fresh_univ_name are modeled
    // out as inputs (see header); RecursorVal metadata (is_k etc.) is not built.
    // ════════════════════════════════════════════════════════════════════════════

    #[allow(clippy::too_many_arguments)]
    pub fn build_mutual_recursor_part(
        all_types: &[InductiveType],
        num_params: u32,
        motive_univ_name: Option<&Name>,
        ind_level_params: &[Name],
        rec_level_params: &[Name],
        rec_pairs: &[RecPair],
        which: usize,
        sel: usize,
    ) -> Expr {
        // ind_name_set: `decl.types.iter().map(|t| &t.name).collect()` — push loop.
        let mut ind_name_set: Vec<Name> = Vec::new();
        {
            let mut _i = 0usize;
            while _i < all_types.len() {
                ind_name_set.push(all_types[_i].name);
                _i += 1;
            }
        }

        // VERBATIM `decl.types.iter().find(|t| &t.name == ind_name)` — the root passes
        // `which` as an index, so ind_name = all_types[which].name and the find loop
        // resolves it back (preserving the real find-by-name control flow).
        let ind_name = all_types[which].name;
        let mut ind_type_idx = 0usize;
        {
            let mut _i = 0usize;
            while _i < all_types.len() {
                if all_types[_i].name == ind_name {
                    ind_type_idx = _i;
                    break;
                }
                _i += 1;
            }
        }
        let ind_type = &all_types[ind_type_idx];

        // MODELED `Name::from_string(&format!("{ind_name}.rec"))` — table lookup.
        let rec_name = rec_name_of(&ind_name, rec_pairs, &ind_name);

        // `ctor_infos` for THIS type; `all_ctor_infos` via flat_map over ALL types
        // (VERBATIM inductive_builder.rs:314 — nested push loops).
        let ctor_infos = compute_ctor_infos(ind_type, &ind_name_set, num_params);
        let mut all_ctor_infos: Vec<CtorInfo> = Vec::new();
        {
            let mut _t = 0usize;
            while _t < all_types.len() {
                let infos_t = compute_ctor_infos(&all_types[_t], &ind_name_set, num_params);
                let mut _j = 0usize;
                while _j < infos_t.len() {
                    all_ctor_infos.push(infos_t[_j].clone());
                    _j += 1;
                }
                _t += 1;
            }
        }

        // VERBATIM minor_idx_offset (inductive_builder.rs:322):
        // `decl.types.iter().take_while(|t| t.name != ind_type.name).map(|t| t.constructors.len()).sum()`.
        let mut minor_idx_offset: usize = 0;
        {
            let mut _t = 0usize;
            while _t < all_types.len() {
                if all_types[_t].name != ind_type.name {
                    minor_idx_offset += all_types[_t].constructors.len();
                } else {
                    break;
                }
                _t += 1;
            }
        }

        // VERBATIM build_recursor's core (inductive_recursor.rs:101-120).
        let type_arity = count_pi_args(&ind_type.type_);
        let num_indices = type_arity.saturating_sub(num_params);
        let num_motives = all_types.len() as u32;
        let total_minors = all_ctor_infos.len();

        let rec_ty = build_recursor_type(
            &ind_name,
            &ind_type.type_,
            num_params,
            num_indices,
            motive_univ_name,
            ind_level_params,
            &all_ctor_infos,
            all_types,
        );

        if sel == 0 {
            return rec_ty;
        }

        // VERBATIM the rules construction (inductive_recursor.rs:126-153): rules for
        // THIS type's constructors only, minor index globally offset. `sel - 1`
        // selects the local ctor idx (harness contract: 1 <= sel <= ctor_infos.len()).
        let mut idx = sel - 1;
        if idx >= ctor_infos.len() {
            idx = 0; // harness contract violation guard — never taken by the tests
        }
        let ci = &ctor_infos[idx];
        build_recursor_rule_rhs(
            &rec_name,
            rec_level_params,
            num_params,
            num_motives,
            num_indices,
            ci.num_fields,
            &ci.recursive_flags,
            &ci.field_types,
            total_minors,
            minor_idx_offset + idx,
            &rec_ty,
            all_types,
            rec_pairs,
        )
    }

    // ════════════════════════════════════════════════════════════════════════════
    // MONO ROOT (#[no_mangle]) — the single closure-free root the emitter picks with
    // `--mir-emit-closure build_mutual_rec_root`. Receives the mutual block as REAL
    // InductiveType values (name + type_ + ctor {name, type_} Pi-telescopes — the
    // CtorInfo derivation runs IN-MODULE), the pre-interned rec-name table, and the
    // (which, sel) selector; writes the resulting Expr through the sret pointer.
    // ════════════════════════════════════════════════════════════════════════════

    #[repr(C)]
    pub struct MutualRecArgs {
        pub num_params: u32,
        pub motive_univ_is_some: u32, // 1 => Some(ULEVEL) (large elim); 0 => None (Prop-only)
        pub which: u32,               // block type index to build the recursor for
        pub sel: u32,                 // 0 => rec TYPE; 1 + j => rule RHS of local ctor j
        pub all_types_ptr: *const InductiveType,
        pub all_types_len: usize,
        pub ind_level_params_ptr: *const Name,
        pub ind_level_params_len: usize,
        pub rec_level_params_ptr: *const Name,
        pub rec_level_params_len: usize,
        pub rec_pairs_ptr: *const RecPair,
        pub rec_pairs_len: usize,
    }

    pub const ULEVEL: u32 = 7; // the fresh motive universe level-param name `u` (modeled)

    pub extern "C" fn build_mutual_rec_root(out: *mut Expr, args: *const MutualRecArgs) {
        let a: &MutualRecArgs = unsafe { &*args };
        let all_types: &[InductiveType] =
            unsafe { std::slice::from_raw_parts(a.all_types_ptr, a.all_types_len) };
        let ind_level_params: &[Name] =
            unsafe { std::slice::from_raw_parts(a.ind_level_params_ptr, a.ind_level_params_len) };
        let rec_level_params: &[Name] =
            unsafe { std::slice::from_raw_parts(a.rec_level_params_ptr, a.rec_level_params_len) };
        let rec_pairs: &[RecPair] =
            unsafe { std::slice::from_raw_parts(a.rec_pairs_ptr, a.rec_pairs_len) };

        let ulevel = Name(ULEVEL);
        let motive_univ_name: Option<&Name> = if a.motive_univ_is_some != 0 {
            Some(&ulevel)
        } else {
            None
        };

        let result = build_mutual_recursor_part(
            all_types,
            a.num_params,
            motive_univ_name,
            ind_level_params,
            rec_level_params,
            rec_pairs,
            a.which as usize,
            a.sel as usize,
        );

        unsafe {
            std::ptr::write(out, result);
        }
    }

    // ── Caller-side input builders (standalone harness + mirrored by the native test).
    //    NOT part of the emitted root; they may use full Rust. ──

    pub const EVEN: u32 = 1;
    pub const ODD: u32 = 2;
    pub const TREE: u32 = 11;
    pub const FOREST: u32 = 12;
    pub const EVEN_REC: u32 = 101;
    pub const ODD_REC: u32 = 102;
    pub const TREE_REC: u32 = 111;
    pub const FOREST_REC: u32 = 112;
    pub const C_EVEN_ZERO: u32 = 201;
    pub const C_EVEN_SUCC_ODD: u32 = 202;
    pub const C_ODD_SUCC_EVEN: u32 = 203;
    pub const C_TREE_NODE: u32 = 211;
    pub const C_FOREST_NIL: u32 = 212;
    pub const C_FOREST_CONS: u32 = 213;
    pub const VLEVEL: u32 = 8; // the inductive's own level param `v` (Tree/Forest)

    // Even/Odd: 0 params, 0 indices, monomorphic (Type 1 formers).
    //   Even.zero : Even ; Even.succ_odd : Π(_:Odd). Even ; Odd.succ_even : Π(_:Even). Odd
    pub fn family_even_odd() -> Vec<InductiveType> {
        let type1 = Expr::sort(Level::Succ(Box::new(Level::Zero)));
        let e = Expr::const_(Name(EVEN), Vec::new());
        let o = Expr::const_(Name(ODD), Vec::new());
        vec![
            InductiveType {
                name: Name(EVEN),
                type_: type1.clone(),
                constructors: vec![
                    Ctor {
                        name: Name(C_EVEN_ZERO),
                        type_: e.clone(),
                    },
                    Ctor {
                        name: Name(C_EVEN_SUCC_ODD),
                        type_: Expr::pi(bi_default(), o.clone(), e.clone()),
                    },
                ],
            },
            InductiveType {
                name: Name(ODD),
                type_: type1,
                constructors: vec![Ctor {
                    name: Name(C_ODD_SUCC_EVEN),
                    type_: Expr::pi(bi_default(), e, o),
                }],
            },
        ]
    }

    // Tree/Forest: 1 param (A : Sort v), 0 indices.
    //   Tree.node    : Π(A:Sort v)(a:A)(f:Forest A). Tree A
    //   Forest.nil   : Π(A:Sort v). Forest A
    //   Forest.cons  : Π(A:Sort v)(t:Tree A)(f:Forest A). Forest A
    pub fn family_tree_forest() -> Vec<InductiveType> {
        let sort_v = Expr::sort(Level::Param(Name(VLEVEL)));
        let tree = |a: Expr| {
            Expr::app(
                Expr::const_(Name(TREE), vec![Level::Param(Name(VLEVEL))]),
                a,
            )
        };
        let forest = |a: Expr| {
            Expr::app(
                Expr::const_(Name(FOREST), vec![Level::Param(Name(VLEVEL))]),
                a,
            )
        };
        // former: Π(A:Sort v). Sort v
        let former = Expr::pi(
            bi_default(),
            sort_v.clone(),
            Expr::sort(Level::Param(Name(VLEVEL))),
        );
        // Tree.node : Π(A:Sort v). Π(a:#0). Π(f:Forest #1). Tree #2
        let node_ty = Expr::pi(
            bi_default(),
            sort_v.clone(),
            Expr::pi(
                bi_default(),
                Expr::bvar(0),
                Expr::pi(bi_default(), forest(Expr::bvar(1)), tree(Expr::bvar(2))),
            ),
        );
        // Forest.nil : Π(A:Sort v). Forest #0
        let nil_ty = Expr::pi(bi_default(), sort_v.clone(), forest(Expr::bvar(0)));
        // Forest.cons : Π(A:Sort v). Π(t:Tree #0). Π(f:Forest #1). Forest #2
        let cons_ty = Expr::pi(
            bi_default(),
            sort_v,
            Expr::pi(
                bi_default(),
                tree(Expr::bvar(0)),
                Expr::pi(bi_default(), forest(Expr::bvar(1)), forest(Expr::bvar(2))),
            ),
        );
        vec![
            InductiveType {
                name: Name(TREE),
                type_: former.clone(),
                constructors: vec![Ctor {
                    name: Name(C_TREE_NODE),
                    type_: node_ty,
                }],
            },
            InductiveType {
                name: Name(FOREST),
                type_: former,
                constructors: vec![
                    Ctor {
                        name: Name(C_FOREST_NIL),
                        type_: nil_ty,
                    },
                    Ctor {
                        name: Name(C_FOREST_CONS),
                        type_: cons_ty,
                    },
                ],
            },
        ]
    }

    pub fn rec_pairs_even_odd() -> Vec<RecPair> {
        vec![
            RecPair {
                ind: Name(EVEN),
                rec: Name(EVEN_REC),
            },
            RecPair {
                ind: Name(ODD),
                rec: Name(ODD_REC),
            },
        ]
    }

    pub fn rec_pairs_tree_forest() -> Vec<RecPair> {
        vec![
            RecPair {
                ind: Name(TREE),
                rec: Name(TREE_REC),
            },
            RecPair {
                ind: Name(FOREST),
                rec: Name(FOREST_REC),
            },
        ]
    }

    pub fn deep_eq(a: &Expr, b: &Expr) -> bool {
        if a.meta.raw() != b.meta.raw() {
            return false;
        }
        match (&a.kind, &b.kind) {
            (ExprKind::BVar(x), ExprKind::BVar(y)) => x == y,
            (ExprKind::FVar(x), ExprKind::FVar(y)) => x == y,
            (ExprKind::Sort(x), ExprKind::Sort(y)) => x == y,
            (ExprKind::Const(n1, l1), ExprKind::Const(n2, l2)) => n1 == n2 && l1 == l2,
            (ExprKind::Lit(x), ExprKind::Lit(y)) => x == y,
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => deep_eq(f1, f2) && deep_eq(a1, a2),
            (ExprKind::Lam(b1, t1, y1), ExprKind::Lam(b2, t2, y2)) => {
                b1 == b2 && deep_eq(t1, t2) && deep_eq(y1, y2)
            }
            (ExprKind::Pi(b1, t1, y1), ExprKind::Pi(b2, t2, y2)) => {
                b1 == b2 && deep_eq(t1, t2) && deep_eq(y1, y2)
            }
            _ => false,
        }
    }

    // Via-root: build the args struct + drive the FFI root.
    pub fn root_part(
        all_types: &[InductiveType],
        num_params: u32,
        ind_level_params: &[Name],
        rec_level_params: &[Name],
        rec_pairs: &[RecPair],
        which: u32,
        sel: u32,
    ) -> Expr {
        let args = MutualRecArgs {
            num_params,
            motive_univ_is_some: 1,
            which,
            sel,
            all_types_ptr: all_types.as_ptr(),
            all_types_len: all_types.len(),
            ind_level_params_ptr: ind_level_params.as_ptr(),
            ind_level_params_len: ind_level_params.len(),
            rec_level_params_ptr: rec_level_params.as_ptr(),
            rec_level_params_len: rec_level_params.len(),
            rec_pairs_ptr: rec_pairs.as_ptr(),
            rec_pairs_len: rec_pairs.len(),
        };
        let mut slot = std::mem::MaybeUninit::<Expr>::uninit();
        unsafe {
            build_mutual_rec_root(slot.as_mut_ptr(), &args as *const MutualRecArgs);
            slot.assume_init()
        }
    }
}

use mx::{Expr, ExprKind, InductiveType, Level, MutualRecArgs, Name, RecPair};

// ════════════════════════════════════════════════════════════════════════════
// mx_shim_* leaf intrinsics (faithful native bodies the JIT binds by mangled
// symbol; layout-driven over the SAME mx types the mirror uses). The Arc/Vec ops
// LEAK (no matching dealloc) — accepted, same model as all prior kernel rungs.
// ════════════════════════════════════════════════════════════════════════════

extern "C" fn mx_shim_rust_alloc(size: usize, align: usize) -> *mut u8 {
    unsafe {
        let layout = std::alloc::Layout::from_size_align(size, align).expect("valid layout");
        std::alloc::alloc(layout)
    }
}
extern "C" fn mx_shim_sat_add(a: u32, b: u32) -> u32 {
    a.saturating_add(b)
}
extern "C" fn mx_shim_sat_sub(a: u32, b: u32) -> u32 {
    a.saturating_sub(b)
}
extern "C" fn mx_shim_wrap_mul(a: u64, b: u64) -> u64 {
    a.wrapping_mul(b)
}
extern "C" fn mx_shim_max_u8(a: u8, b: u8) -> u8 {
    a.max(b)
}
extern "C" fn mx_shim_max_u32(a: u32, b: u32) -> u32 {
    a.max(b)
}
extern "C" fn mx_shim_min_u32(a: u32, b: u32) -> u32 {
    a.min(b)
}
// <&Name as PartialEq>::eq — ref-ref (core::cmp::impls R).
extern "C" fn mx_shim_name_eq(a: *const *const Name, b: *const *const Name) -> bool {
    unsafe { (**a).0 == (**b).0 }
}
// <Name as PartialEq>::ne — (&self, &other).
extern "C" fn mx_shim_name_ne(a: *const Name, b: *const Name) -> bool {
    unsafe { (*a).0 != (*b).0 }
}
// usize_to_u32 = u32::try_from(v).unwrap_or(MAX): Result<u32,TryFromIntError> via sret.
extern "C" fn mx_shim_try_from_u32(sret: *mut Result<u32, std::num::TryFromIntError>, v: u64) {
    unsafe {
        std::ptr::write(sret, u32::try_from(v));
    }
}
extern "C" fn mx_shim_result_unwrap_or(
    res: *const Result<u32, std::num::TryFromIntError>,
    default: u32,
) -> u32 {
    unsafe { (*res).unwrap_or(default) }
}
// std::slice::from_raw_parts<T>(data, len) -> &[T] (fat pointer via sret).
extern "C" fn mx_shim_from_raw_parts(sret: *mut (*const u8, usize), data: *const u8, len: u64) {
    unsafe {
        std::ptr::write(sret, (data, len as usize));
    }
}
// std::ptr::write::<Expr>(dst, val) — val passed by pointer.
extern "C" fn mx_shim_ptr_write_expr(dst: *mut Expr, val: *const Expr) {
    unsafe {
        std::ptr::write(dst, std::ptr::read(val));
    }
}
// slice::<Expr>::get(idx) -> Option<&Expr> (niche-encoded; None = null). slice_ref is a
// POINTER to the fat pointer.
extern "C" fn mx_shim_slice_expr_get(
    sret: *mut Option<&Expr>,
    slice_ref: *const (*const Expr, usize),
    idx: u64,
) {
    unsafe {
        let (data, len) = *slice_ref;
        if (idx as usize) < len {
            std::ptr::write(sret, Some(&*data.add(idx as usize)));
        } else {
            std::ptr::write(sret, None);
        }
    }
}
// KaniHasher leaf writes (xor + wrapping_mul MAGIC — the slice's write_uN semantics).
const MX_KANI_MAGIC: u64 = 0x517cc1b727220a95;
extern "C" fn mx_shim_hash_u32(value: *const u32, state: *mut u64) {
    unsafe {
        let v = *value as u64;
        let s = (*state) ^ v;
        *state = s.wrapping_mul(MX_KANI_MAGIC);
    }
}
// <isize as Hash>::hash — derived-enum discriminant writes (write_isize -> write_u64).
extern "C" fn mx_shim_hash_isize(value: *const i64, state: *mut u64) {
    unsafe {
        let v = *value as u64;
        let s = (*state) ^ v;
        *state = s.wrapping_mul(MX_KANI_MAGIC);
    }
}
// <u64 as Hash>::hash — OFF-path (only FVarId(u64) payloads hash through this; no FVar
// is constructed on the recursor path). Trap loudly if ever reached.
extern "C" fn mx_shim_hash_unreached(_a: *const u8, _b: *const u8) {
    unreachable!("KaniHasher u64 Hash leaf reached on the mutual-recursor path (FVar payload?)");
}
// <Box<Level> as Hash>::hash — deref + derived Level hash through KaniHasher semantics.
struct MxShimKani {
    state: u64,
}
impl std::hash::Hasher for MxShimKani {
    fn finish(&self) -> u64 {
        self.state
    }
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.state = self.state.wrapping_mul(31).wrapping_add(b as u64);
        }
    }
    fn write_u8(&mut self, i: u8) {
        self.state ^= i as u64;
        self.state = self.state.wrapping_mul(MX_KANI_MAGIC);
    }
    fn write_u16(&mut self, i: u16) {
        self.state ^= i as u64;
        self.state = self.state.wrapping_mul(MX_KANI_MAGIC);
    }
    fn write_u32(&mut self, i: u32) {
        self.state ^= i as u64;
        self.state = self.state.wrapping_mul(MX_KANI_MAGIC);
    }
    fn write_u64(&mut self, i: u64) {
        self.state ^= i;
        self.state = self.state.wrapping_mul(MX_KANI_MAGIC);
    }
    fn write_u128(&mut self, i: u128) {
        self.write_u64(i as u64);
        self.write_u64((i >> 64) as u64);
    }
    fn write_usize(&mut self, i: usize) {
        self.write_u64(i as u64);
    }
}
extern "C" fn mx_shim_hash_box_level(boxptr: *const Box<Level>, state: *mut u64) {
    use std::hash::{Hash, Hasher};
    unsafe {
        let mut h = MxShimKani { state: *state };
        (**boxptr).hash(&mut h);
        *state = h.finish();
    }
}

// Vec<T> ops per element type (new / with_capacity / push / len / index / deref / clone).
macro_rules! mx_vec_shims {
    ($new:ident, $push:ident, $len:ident, $index:ident, $deref:ident, $clone:ident, $ty:ty) => {
        #[allow(dead_code)]
        extern "C" fn $new(sret: *mut Vec<$ty>) {
            unsafe {
                std::ptr::write(sret, Vec::new());
            }
        }
        #[allow(dead_code)]
        extern "C" fn $push(vec: *mut Vec<$ty>, value: *const $ty) {
            unsafe {
                let v = std::ptr::read(value);
                (*vec).push(v);
            }
        }
        #[allow(dead_code)]
        extern "C" fn $len(vec: *const Vec<$ty>) -> u64 {
            unsafe { (*vec).len() as u64 }
        }
        #[allow(dead_code)]
        extern "C" fn $index(vec: *const Vec<$ty>, idx: u64) -> *const $ty {
            unsafe {
                let s: &[$ty] = (*vec).as_slice();
                assert!((idx as usize) < s.len(), "vec index oob");
                s.as_ptr().add(idx as usize)
            }
        }
        #[allow(dead_code)]
        extern "C" fn $deref(sret: *mut (*const $ty, usize), vec: *const Vec<$ty>) {
            unsafe {
                let s: &[$ty] = (*vec).as_slice();
                std::ptr::write(sret, (s.as_ptr(), s.len()));
            }
        }
        #[allow(dead_code)]
        extern "C" fn $clone(sret: *mut Vec<$ty>, this: *const Vec<$ty>) {
            unsafe {
                std::ptr::write(sret, (*this).clone());
            }
        }
    };
}
mx_vec_shims!(
    mxv_expr_new,
    mxv_expr_push,
    mxv_expr_len,
    mxv_expr_index,
    mxv_expr_deref,
    mxv_expr_clone,
    Expr
);
mx_vec_shims!(
    mxv_lvl_new,
    mxv_lvl_push,
    mxv_lvl_len,
    mxv_lvl_index,
    mxv_lvl_deref,
    mxv_lvl_clone,
    Level
);
mx_vec_shims!(
    mxv_name_new,
    mxv_name_push,
    mxv_name_len,
    mxv_name_index,
    mxv_name_deref,
    mxv_name_clone,
    Name
);
mx_vec_shims!(
    mxv_ci_new,
    mxv_ci_push,
    mxv_ci_len,
    mxv_ci_index,
    mxv_ci_deref,
    mxv_ci_clone,
    mx::CtorInfo
);
mx_vec_shims!(
    mxv_ctor_new,
    mxv_ctor_push,
    mxv_ctor_len,
    mxv_ctor_index,
    mxv_ctor_deref,
    mxv_ctor_clone,
    mx::Ctor
);
mx_vec_shims!(
    mxv_bool_new,
    mxv_bool_push,
    mxv_bool_len,
    mxv_bool_index,
    mxv_bool_deref,
    mxv_bool_clone,
    bool
);
mx_vec_shims!(
    mxv_bdexpr_new,
    mxv_bdexpr_push,
    mxv_bdexpr_len,
    mxv_bdexpr_index,
    mxv_bdexpr_deref,
    mxv_bdexpr_clone,
    (mx::BinderData, Expr)
);
mx_vec_shims!(
    mxv_exprbool_new,
    mxv_exprbool_push,
    mxv_exprbool_len,
    mxv_exprbool_index,
    mxv_exprbool_deref,
    mxv_exprbool_clone,
    (Expr, bool)
);
// BY-VALUE pushes (scalar element ABIs — functy (ptr, bool) / (ptr, u32)):
extern "C" fn mxv_bool_push_val(vec: *mut Vec<bool>, value: bool) {
    unsafe {
        (*vec).push(value);
    }
}
extern "C" fn mxv_name_push_val(vec: *mut Vec<Name>, value: u32) {
    unsafe {
        (*vec).push(Name(value));
    }
}
extern "C" fn mxv_expr_with_capacity(sret: *mut Vec<Expr>, _cap: u64) {
    unsafe {
        std::ptr::write(sret, Vec::new());
    }
}
extern "C" fn mxv_ci_with_capacity(sret: *mut Vec<mx::CtorInfo>, _cap: u64) {
    unsafe {
        std::ptr::write(sret, Vec::new());
    }
}
extern "C" fn mx_shim_arc_clone(
    sret: *mut std::sync::Arc<Expr>,
    this: *const std::sync::Arc<Expr>,
) {
    unsafe {
        std::ptr::write(sret, std::sync::Arc::clone(&*this));
    }
}
extern "C" fn mx_shim_box_lvl_clone(sret: *mut Box<Level>, this: *const Box<Level>) {
    unsafe {
        std::ptr::write(sret, (*this).clone());
    }
}

type MutualRootFn = extern "C" fn(*mut Expr, *const MutualRecArgs);

fn mx_externs() -> HashMap<String, *const u8> {
    let c = "Cs6RT0DENTjyC_27clean_mutual_recursor_slice"; // the slice crate's v0 tag (crate-name-derived; load-bearing)
    let mut e: HashMap<String, *const u8> = HashMap::new();
    let mut ins = |k: String, v: *const u8| {
        e.insert(k, v);
    };
    ins("__rust_alloc".into(), mx_shim_rust_alloc as *const u8);
    ins(
        format!("_RINvMNtCs2EYQwhfuABO_4core5sliceSNt{c}4Expr3getjEBx_"),
        mx_shim_slice_expr_get as *const u8,
    );
    ins(
        format!("_RINvNtCs2EYQwhfuABO_4core3ptr5writeNt{c}4ExprEBz_"),
        mx_shim_ptr_write_expr as *const u8,
    );
    ins(
        format!("_RINvNtNtCs2EYQwhfuABO_4core5slice3raw14from_raw_partsNt{c}13InductiveTypeEBR_"),
        mx_shim_from_raw_parts as *const u8,
    );
    ins(
        format!("_RINvNtNtCs2EYQwhfuABO_4core5slice3raw14from_raw_partsNt{c}4NameEBR_"),
        mx_shim_from_raw_parts as *const u8,
    );
    ins(
        format!("_RINvNtNtCs2EYQwhfuABO_4core5slice3raw14from_raw_partsNt{c}7RecPairEBR_"),
        mx_shim_from_raw_parts as *const u8,
    );
    ins(
        format!("_RINvXs9_NtNtCs2EYQwhfuABO_4core4hash5implsmNtB8_4Hash4hashNt{c}10KaniHasherEBW_"),
        mx_shim_hash_u32 as *const u8,
    );
    ins(
        format!("_RINvXsa_NtNtCs2EYQwhfuABO_4core4hash5implsyNtB8_4Hash4hashNt{c}10KaniHasherEBW_"),
        mx_shim_hash_unreached as *const u8,
    );
    ins(
        format!("_RINvXsg_NtNtCs2EYQwhfuABO_4core4hash5implsiNtB8_4Hash4hashNt{c}10KaniHasherEBW_"),
        mx_shim_hash_isize as *const u8,
    );
    ins(
        format!(
            "_RINvXsk_NtCskTzINo8ZBH9_5alloc5boxedINtB6_3BoxNt{c}5LevelENtNtCs2EYQwhfuABO_4core4hash4Hash4hashNtBK_10KaniHasherEBK_"
        ),
        mx_shim_hash_box_level as *const u8,
    );
    ins(
        format!(
            "_RNvMNtCs2EYQwhfuABO_4core6resultINtB2_6ResultmNtNtNtB4_3num5error15TryFromIntErrorE9unwrap_or{c}"
        ),
        mx_shim_result_unwrap_or as *const u8,
    );
    ins(
        format!(
            "_RNvXs0_NtNtNtCs2EYQwhfuABO_4core7convert3num18ptr_try_from_implsmINtB9_7TryFromjE8try_from{c}"
        ),
        mx_shim_try_from_u32 as *const u8,
    );
    // Vec::new / with_capacity
    ins(
        format!("_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecbE3new{c}"),
        mxv_bool_new as *const u8,
    );
    ins(
        format!("_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNt{c}4ExprE13with_capacityBE_"),
        mxv_expr_with_capacity as *const u8,
    );
    ins(
        format!("_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNt{c}4ExprE3newBE_"),
        mxv_expr_new as *const u8,
    );
    ins(
        format!("_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNt{c}4NameE3newBE_"),
        mxv_name_new as *const u8,
    );
    ins(
        format!("_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNt{c}5LevelE3newBE_"),
        mxv_lvl_new as *const u8,
    );
    ins(
        format!("_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNt{c}8CtorInfoE13with_capacityBE_"),
        mxv_ci_with_capacity as *const u8,
    );
    ins(
        format!("_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNt{c}8CtorInfoE3newBE_"),
        mxv_ci_new as *const u8,
    );
    ins(
        format!("_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecTNt{c}10BinderDataNtBF_4ExprEE3newBF_"),
        mxv_bdexpr_new as *const u8,
    );
    ins(
        format!("_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecTNt{c}4ExprbEE3newBF_"),
        mxv_exprbool_new as *const u8,
    );
    // Vec::push
    ins(
        format!("_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecbE4push{c}"),
        mxv_bool_push_val as *const u8,
    );
    ins(
        format!("_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNt{c}4ExprE4pushBH_"),
        mxv_expr_push as *const u8,
    );
    ins(
        format!("_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNt{c}4NameE4pushBH_"),
        mxv_name_push_val as *const u8,
    );
    ins(
        format!("_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNt{c}5LevelE4pushBH_"),
        mxv_lvl_push as *const u8,
    );
    ins(
        format!("_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNt{c}8CtorInfoE4pushBH_"),
        mxv_ci_push as *const u8,
    );
    ins(
        format!(
            "_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecTNt{c}10BinderDataNtBI_4ExprEE4pushBI_"
        ),
        mxv_bdexpr_push as *const u8,
    );
    ins(
        format!("_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecTNt{c}4ExprbEE4pushBI_"),
        mxv_exprbool_push as *const u8,
    );
    // Vec::len
    ins(
        format!("_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNt{c}4CtorE3lenBG_"),
        mxv_ctor_len as *const u8,
    );
    ins(
        format!("_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNt{c}4ExprE3lenBG_"),
        mxv_expr_len as *const u8,
    );
    ins(
        format!("_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNt{c}5LevelE3lenBG_"),
        mxv_lvl_len as *const u8,
    );
    ins(
        format!("_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNt{c}8CtorInfoE3lenBG_"),
        mxv_ci_len as *const u8,
    );
    ins(
        format!("_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecTNt{c}10BinderDataNtBH_4ExprEE3lenBH_"),
        mxv_bdexpr_len as *const u8,
    );
    ins(
        format!("_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecTNt{c}4ExprbEE3lenBH_"),
        mxv_exprbool_len as *const u8,
    );
    // Vec Index
    ins(
        format!(
            "_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNt{c}4CtorEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_"
        ),
        mxv_ctor_index as *const u8,
    );
    ins(
        format!(
            "_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNt{c}4ExprEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_"
        ),
        mxv_expr_index as *const u8,
    );
    ins(
        format!(
            "_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNt{c}5LevelEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_"
        ),
        mxv_lvl_index as *const u8,
    );
    ins(
        format!(
            "_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNt{c}8CtorInfoEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_"
        ),
        mxv_ci_index as *const u8,
    );
    ins(
        format!(
            "_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecTNt{c}10BinderDataNtBI_4ExprEEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBI_"
        ),
        mxv_bdexpr_index as *const u8,
    );
    ins(
        format!(
            "_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecTNt{c}4ExprbEEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBI_"
        ),
        mxv_exprbool_index as *const u8,
    );
    // Vec Deref
    ins(
        format!(
            "_RNvXs7_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecbENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5deref{c}"
        ),
        mxv_bool_deref as *const u8,
    );
    ins(
        format!(
            "_RNvXs7_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNt{c}4ExprENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefBH_"
        ),
        mxv_expr_deref as *const u8,
    );
    ins(
        format!(
            "_RNvXs7_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNt{c}4NameENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefBH_"
        ),
        mxv_name_deref as *const u8,
    );
    ins(
        format!(
            "_RNvXs7_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNt{c}8CtorInfoENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefBH_"
        ),
        mxv_ci_deref as *const u8,
    );
    // Vec Clone
    ins(
        format!(
            "_RNvXsa_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecbENtNtCs2EYQwhfuABO_4core5clone5Clone5clone{c}"
        ),
        mxv_bool_clone as *const u8,
    );
    ins(
        format!(
            "_RNvXsa_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNt{c}4ExprENtNtCs2EYQwhfuABO_4core5clone5Clone5cloneBH_"
        ),
        mxv_expr_clone as *const u8,
    );
    ins(
        format!(
            "_RNvXsa_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNt{c}5LevelENtNtCs2EYQwhfuABO_4core5clone5Clone5cloneBH_"
        ),
        mxv_lvl_clone as *const u8,
    );
    // Arc / Box clones
    ins(
        format!(
            "_RNvXsu_NtCskTzINo8ZBH9_5alloc4syncINtB5_3ArcNt{c}4ExprENtNtCs2EYQwhfuABO_4core5clone5Clone5cloneBI_"
        ),
        mx_shim_arc_clone as *const u8,
    );
    ins(
        format!(
            "_RNvXsd_NtCskTzINo8ZBH9_5alloc5boxedINtB5_3BoxNt{c}5LevelENtNtCs2EYQwhfuABO_4core5clone5Clone5cloneBJ_"
        ),
        mx_shim_box_lvl_clone as *const u8,
    );
    // Name eq/ne
    ins(
        format!("_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNt{c}4NameNtB7_9PartialEq2eqBF_"),
        mx_shim_name_eq as *const u8,
    );
    ins(
        format!("_RNvYNt{c}4NameNtNtCs2EYQwhfuABO_4core3cmp9PartialEq2neB4_"),
        mx_shim_name_ne as *const u8,
    );
    // num / cmp leaves
    ins(
        "_RNvMs6_NtCs2EYQwhfuABO_4core3numm14saturating_add".into(),
        mx_shim_sat_add as *const u8,
    );
    ins(
        "_RNvMs6_NtCs2EYQwhfuABO_4core3numm14saturating_sub".into(),
        mx_shim_sat_sub as *const u8,
    );
    ins(
        "_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_mul".into(),
        mx_shim_wrap_mul as *const u8,
    );
    ins(
        format!("_RNvYhNtNtCs2EYQwhfuABO_4core3cmp3Ord3max{c}"),
        mx_shim_max_u8 as *const u8,
    );
    ins(
        format!("_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3max{c}"),
        mx_shim_max_u32 as *const u8,
    );
    ins(
        format!("_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3min{c}"),
        mx_shim_min_u32 as *const u8,
    );
    e
}

// Drive the JIT root over host-built inputs.
#[allow(clippy::too_many_arguments)]
fn jit_part(
    f: MutualRootFn,
    all_types: &[InductiveType],
    num_params: u32,
    motive_univ_is_some: u32,
    ilp: &[Name],
    rlp: &[Name],
    pairs: &[RecPair],
    which: u32,
    sel: u32,
) -> Expr {
    let args = MutualRecArgs {
        num_params,
        motive_univ_is_some,
        which,
        sel,
        all_types_ptr: all_types.as_ptr(),
        all_types_len: all_types.len(),
        ind_level_params_ptr: ilp.as_ptr(),
        ind_level_params_len: ilp.len(),
        rec_level_params_ptr: rlp.as_ptr(),
        rec_level_params_len: rlp.len(),
        rec_pairs_ptr: pairs.as_ptr(),
        rec_pairs_len: pairs.len(),
    };
    let mut slot = std::mem::MaybeUninit::<Expr>::uninit();
    unsafe {
        f(slot.as_mut_ptr(), &args as *const MutualRecArgs);
        slot.assume_init()
    }
}

// Native oracle (the mirror slice compiled in this crate).
#[allow(clippy::too_many_arguments)]
fn native_part(
    all_types: &[InductiveType],
    num_params: u32,
    motive_univ_is_some: u32,
    ilp: &[Name],
    rlp: &[Name],
    pairs: &[RecPair],
    which: u32,
    sel: u32,
) -> Expr {
    let ulevel = Name(mx::ULEVEL);
    let motive: Option<&Name> = if motive_univ_is_some != 0 {
        Some(&ulevel)
    } else {
        None
    };
    mx::build_mutual_recursor_part(
        all_types,
        num_params,
        motive,
        ilp,
        rlp,
        pairs,
        which as usize,
        sel as usize,
    )
}

// App-spine head of an Expr (test-side walker for the IH-head ground-truth check).
fn spine_head(e: &Expr) -> &Expr {
    let mut cur = e;
    while let ExprKind::App(f, _) = &cur.kind {
        cur = f;
    }
    cur
}

// Strip all leading lambdas.
fn strip_lams(e: &Expr) -> &Expr {
    let mut cur = e;
    while let ExprKind::Lam(_, _, body) = &cur.kind {
        cur = body;
    }
    cur
}

#[test]
fn mir_mutual_recursor_even_odd_tree_forest_roundtrip() {
    let module = trust_ir::parser::parse_module(MX_MUTUAL_REC_TRUST_IR)
        .expect("MIR-emitted mutual-recursor closure trust-ir text must parse");

    // The full mutual engine must be genuinely IN-MODULE (real bodies, not stubs).
    let bodied = |sym: &str| {
        module
            .functions
            .iter()
            .find(|f| f.name == sym)
            .map(|f| !f.blocks.is_empty())
            .unwrap_or(false)
    };
    assert!(
        bodied("build_mutual_rec_root"),
        "mono root must be in-module"
    );
    assert!(
        bodied("build_mutual_recursor_part"),
        "the build_recursor assembly must be in-module"
    );
    assert!(
        bodied("build_recursor_type"),
        "recursor-type builder must be in-module"
    );
    assert!(
        bodied("build_minor_premise_type"),
        "minor-premise builder must be in-module"
    );
    assert!(
        bodied("build_recursor_rule_rhs"),
        "iota-rule RHS builder must be in-module"
    );
    assert!(
        bodied("compute_ctor_infos"),
        "CtorInfo derivation must be in-module"
    );
    assert!(
        bodied("get_recursive_field_flags") && bodied("field_is_eliminably_recursive"),
        "the mutual recursive-field detection must be in-module"
    );
    assert!(
        bodied("get_constructor_field_types") && bodied("get_constructor_return_indices"),
        "the ctor telescope readers must be in-module"
    );
    assert!(
        bodied("rec_name_of") && bodied("name_in_set"),
        "the modeled interning-table lookup must be in-module"
    );
    assert!(
        bodied("remap_residual_index_bvars") && bodied("remap_residual_index_bvars_for_minor"),
        "both BVar remap variants must be in-module"
    );
    assert!(
        bodied("ctor_motive_index") && bodied("field_motive_index"),
        "the motive selectors must be in-module"
    );
    assert!(
        bodied("Expr__from_kind") && bodied("ExprKind__compute_meta") && bodied("mix_hash"),
        "the verified construction core must be in-module"
    );
    assert!(
        bodied("Expr__infer_implicit") && bodied("Expr__lift_at"),
        "infer_implicit + the de-Bruijn lift must be in-module"
    );
    assert!(
        MX_MUTUAL_REC_TRUST_IR.contains("heap_alloc rust_heap"),
        "Arc::new children must lower to heap_alloc (not stubbed)"
    );
    assert!(
        MX_MUTUAL_REC_TRUST_IR.contains("14313749767032793493"),
        "mix_hash MurmurHash constant must be lowered"
    );

    let externs = mx_externs();
    let buffer = Compiler::new(CompilerConfig::jit_fast(Target::Aarch64))
        .compile_module_to_jit(&module, &externs)
        .expect("trust-cg JIT compile of the mutual-recursor closure failed")
        .buffer;
    let raw = buffer
        .get_fn_ptr_bound("build_mutual_rec_root")
        .expect("JIT symbol `build_mutual_rec_root` not found")
        .as_ptr();
    let f: MutualRootFn = unsafe { std::mem::transmute(raw) };

    // ── the two real mutual families ──
    let eo = mx::family_even_odd();
    let eo_pairs = mx::rec_pairs_even_odd();
    let eo_ilp: Vec<Name> = Vec::new();
    let eo_rlp = vec![Name(mx::ULEVEL)];

    let tf = mx::family_tree_forest();
    let tf_pairs = mx::rec_pairs_tree_forest();
    let tf_ilp = vec![Name(mx::VLEVEL)];
    let tf_rlp = vec![Name(mx::ULEVEL), Name(mx::VLEVEL)];

    // ── native == JIT over every output of both recursors of both blocks ──
    // (deep-structural AND meta-word bit-identical at every node via mx::deep_eq).
    let eo_sels: [(u32, u32, &str); 5] = [
        (0, 0, "Even.rec TYPE"),
        (0, 1, "Even.rec rule[zero]"),
        (0, 2, "Even.rec rule[succ_odd]"),
        (1, 0, "Odd.rec TYPE"),
        (1, 1, "Odd.rec rule[succ_even]"),
    ];
    for (which, sel, label) in &eo_sels {
        let native = native_part(&eo, 0, 1, &eo_ilp, &eo_rlp, &eo_pairs, *which, *sel);
        let jit = jit_part(f, &eo, 0, 1, &eo_ilp, &eo_rlp, &eo_pairs, *which, *sel);
        assert!(
            mx::deep_eq(&native, &jit),
            "MUTUAL Even/Odd `{label}`: JIT disagrees with native\n  native = {native:?}\n  jit = {jit:?}"
        );
        assert_eq!(
            native.meta.raw(),
            jit.meta.raw(),
            "meta word disagrees on `{label}`"
        );
    }
    let tf_sels: [(u32, u32, &str); 5] = [
        (0, 0, "Tree.rec TYPE"),
        (0, 1, "Tree.rec rule[node]"),
        (1, 0, "Forest.rec TYPE"),
        (1, 1, "Forest.rec rule[nil]"),
        (1, 2, "Forest.rec rule[cons]"),
    ];
    for (which, sel, label) in &tf_sels {
        let native = native_part(&tf, 1, 1, &tf_ilp, &tf_rlp, &tf_pairs, *which, *sel);
        let jit = jit_part(f, &tf, 1, 1, &tf_ilp, &tf_rlp, &tf_pairs, *which, *sel);
        assert!(
            mx::deep_eq(&native, &jit),
            "MUTUAL Tree/Forest `{label}`: JIT disagrees with native\n  native = {native:?}\n  jit = {jit:?}"
        );
        assert_eq!(
            native.meta.raw(),
            jit.meta.raw(),
            "meta word disagrees on `{label}`"
        );
    }

    // ── GROUND TRUTH 1: the JIT-built Even.rec TYPE equals the HAND-BUILT term from
    //    Lean's documented Even/Odd shape (inductive_recursor_types.rs doc comment):
    //      Even.rec : {m1 : Even -> Sort u} -> {m2 : Odd -> Sort u} ->
    //                 (m1 Even.zero) ->
    //                 ((o : Odd) -> m2 o -> m1 (Even.succ_odd o)) ->
    //                 ((e : Even) -> m1 e -> m2 (Odd.succ_even e)) ->
    //                 (t : Even) -> m1 t
    //    hand-lowered to de Bruijn (independent of ALL builder code). ──
    let d = mx::bi_default();
    let imp = mx::bi_implicit();
    let u = Level::Param(Name(mx::ULEVEL));
    let even = Expr::const_(Name(mx::EVEN), vec![]);
    let odd = Expr::const_(Name(mx::ODD), vec![]);
    let zero = Expr::const_(Name(mx::C_EVEN_ZERO), vec![]);
    let succ_odd = Expr::const_(Name(mx::C_EVEN_SUCC_ODD), vec![]);
    let succ_even = Expr::const_(Name(mx::C_ODD_SUCC_EVEN), vec![]);
    let m1_ty = Expr::pi(d, even.clone(), Expr::sort(u.clone()));
    let m2_ty = Expr::pi(d, odd.clone(), Expr::sort(u.clone()));
    // minor domains AS THEY APPEAR in the rec telescope (post per-minor lift):
    let n0_ty = Expr::app(Expr::bvar(1), zero.clone());
    let n1_ty = Expr::pi(
        d,
        odd.clone(),
        Expr::pi(
            d,
            Expr::app(Expr::bvar(2), Expr::bvar(0)),
            Expr::app(Expr::bvar(4), Expr::app(succ_odd.clone(), Expr::bvar(1))),
        ),
    );
    let n2_ty = Expr::pi(
        d,
        even.clone(),
        Expr::pi(
            d,
            Expr::app(Expr::bvar(4), Expr::bvar(0)),
            Expr::app(Expr::bvar(4), Expr::app(succ_even.clone(), Expr::bvar(1))),
        ),
    );
    let expected_even_rec_ty = Expr::pi(
        imp,
        m1_ty.clone(),
        Expr::pi(
            imp,
            m2_ty.clone(),
            Expr::pi(
                d,
                n0_ty.clone(),
                Expr::pi(
                    d,
                    n1_ty.clone(),
                    Expr::pi(
                        d,
                        n2_ty.clone(),
                        Expr::pi(d, even.clone(), Expr::app(Expr::bvar(5), Expr::bvar(0))),
                    ),
                ),
            ),
        ),
    );
    let jit_even_rec_ty = jit_part(f, &eo, 0, 1, &eo_ilp, &eo_rlp, &eo_pairs, 0, 0);
    assert!(
        mx::deep_eq(&expected_even_rec_ty, &jit_even_rec_ty),
        "GROUND TRUTH: JIT Even.rec TYPE != hand-built Lean-documented shape\n  expected = {expected_even_rec_ty:?}\n  jit = {jit_even_rec_ty:?}"
    );

    // ── GROUND TRUTH 2: the JIT-built Odd.rec rule[succ_even] RHS equals the
    //    HAND-BUILT iota RHS — the CROSS-RECURSOR IH is Even.rec (the mutual essence):
    //      \ m1 m2 n0 n1 n2 (e : Even). n2 e (Even.rec@{u} m1 m2 n0 n1 n2 e)
    //    (minor selector = GLOBAL index 2 = minor_idx_offset(Even's 2 ctors) + 0). ──
    let even_rec_c = Expr::const_(Name(mx::EVEN_REC), vec![Level::Param(Name(mx::ULEVEL))]);
    let ih = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(even_rec_c.clone(), Expr::bvar(5)), Expr::bvar(4)),
                    Expr::bvar(3),
                ),
                Expr::bvar(2),
            ),
            Expr::bvar(1),
        ),
        Expr::bvar(0),
    );
    let body_correct = Expr::app(Expr::app(Expr::bvar(1), Expr::bvar(0)), ih.clone());
    let wrap_rhs = |body: Expr| {
        Expr::lam(
            d,
            m1_ty.clone(),
            Expr::lam(
                d,
                m2_ty.clone(),
                Expr::lam(
                    d,
                    n0_ty.clone(),
                    Expr::lam(
                        d,
                        n1_ty.clone(),
                        Expr::lam(d, n2_ty.clone(), Expr::lam(d, even.clone(), body)),
                    ),
                ),
            ),
        )
    };
    let expected_odd_rule = wrap_rhs(body_correct);
    let jit_odd_rule = jit_part(f, &eo, 0, 1, &eo_ilp, &eo_rlp, &eo_pairs, 1, 1);
    assert!(
        mx::deep_eq(&expected_odd_rule, &jit_odd_rule),
        "GROUND TRUTH: JIT Odd.rec rule[succ_even] != hand-built iota RHS (cross-recursor IH)\n  expected = {expected_odd_rule:?}\n  jit = {jit_odd_rule:?}"
    );

    // ── GROUND TRUTH 3 (parametric block): in Tree.rec rule[node], the IH head must
    //    be Forest.rec with levels [u, v] (the sibling recursor). ──
    let jit_tree_node_rule = jit_part(f, &tf, 1, 1, &tf_ilp, &tf_rlp, &tf_pairs, 0, 1);
    let body = strip_lams(&jit_tree_node_rule);
    // body = App(App(App(minor, a), f_field), ih) — the LAST applied arg is the IH.
    let ih_arg = match &body.kind {
        ExprKind::App(_, a) => a,
        other => panic!("Tree.node rule body is not an application: {other:?}"),
    };
    match &spine_head(ih_arg).kind {
        ExprKind::Const(name, levels) => {
            assert_eq!(
                name.0,
                mx::FOREST_REC,
                "MUTUAL IH must name the SIBLING recursor Forest.rec (got Name({}))",
                name.0
            );
            assert_eq!(
                levels,
                &vec![
                    Level::Param(Name(mx::ULEVEL)),
                    Level::Param(Name(mx::VLEVEL))
                ],
                "IH recursor levels must be [u, v]"
            );
        }
        other => panic!("Tree.node IH head is not a Const: {other:?}"),
    }

    // ── NEGATIVE CONTROL A (fail-loud; arm by corrupting the expectation): a
    //    hand-built RHS whose IH names the WRONG recursor (Odd.rec instead of
    //    Even.rec) must NOT deep-eq the JIT output. If the differential ever went
    //    soft (deep_eq degenerating, or the builder ignoring the table), this
    //    assert panics. ──
    let odd_rec_c = Expr::const_(Name(mx::ODD_REC), vec![Level::Param(Name(mx::ULEVEL))]);
    let ih_wrong = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(odd_rec_c, Expr::bvar(5)), Expr::bvar(4)),
                    Expr::bvar(3),
                ),
                Expr::bvar(2),
            ),
            Expr::bvar(1),
        ),
        Expr::bvar(0),
    );
    let expected_wrong_ih = wrap_rhs(Expr::app(Expr::app(Expr::bvar(1), Expr::bvar(0)), ih_wrong));
    assert!(
        !mx::deep_eq(&expected_wrong_ih, &jit_odd_rule),
        "NEGATIVE CONTROL: a wrong-recursor IH must NOT match the JIT output"
    );

    // ── NEGATIVE CONTROL B (fail-loud): a hand-built RHS with the WRONG minor
    //    selector (local idx without minor_idx_offset: BVar(3) = n0 instead of
    //    BVar(1) = n2) must NOT deep-eq the JIT output. ──
    let body_wrong_minor = Expr::app(Expr::app(Expr::bvar(3), Expr::bvar(0)), ih.clone());
    let expected_wrong_minor = wrap_rhs(body_wrong_minor);
    assert!(
        !mx::deep_eq(&expected_wrong_minor, &jit_odd_rule),
        "NEGATIVE CONTROL: dropping minor_idx_offset must NOT match the JIT output"
    );

    // ── NEGATIVE CONTROL C (the modeled boundary, exercised through MACHINE CODE):
    //    a deliberately SWAPPED pre-interned table (Even -> Odd.rec, Odd -> Even.rec)
    //    fed to the JIT must produce exactly the wrong-recursor RHS (equal to the
    //    hand-built wrong-IH term AND to the native mirror under the same bogus
    //    table), and must differ from the correct output. Proves the interning
    //    table genuinely flows through the JIT-compiled rec_name_of. ──
    let bogus_pairs = vec![
        RecPair {
            ind: Name(mx::EVEN),
            rec: Name(mx::ODD_REC),
        },
        RecPair {
            ind: Name(mx::ODD),
            rec: Name(mx::EVEN_REC),
        },
    ];
    let jit_bogus = jit_part(f, &eo, 0, 1, &eo_ilp, &eo_rlp, &bogus_pairs, 1, 1);
    let native_bogus = native_part(&eo, 0, 1, &eo_ilp, &eo_rlp, &bogus_pairs, 1, 1);
    assert!(
        mx::deep_eq(&jit_bogus, &native_bogus),
        "bogus-table run must still agree native == JIT (differential sharpness)"
    );
    assert!(
        mx::deep_eq(&jit_bogus, &expected_wrong_ih),
        "bogus table must produce exactly the hand-built wrong-recursor RHS"
    );
    assert!(
        !mx::deep_eq(&jit_bogus, &jit_odd_rule),
        "bogus table output must differ from the correct output"
    );

    drop(buffer);
}
