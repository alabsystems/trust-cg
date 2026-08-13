//! T1 UNIVERSE INTEGRATION — the universal decl gate over the FULL production Level.
//!
//! End-to-end: the real clean-kernel decl-add gate (`Environment::check_decl_readonly`,
//! env/decl_add.rs:229) — §2 duplicate-level-params, §3 no-mvar/no-fvar, §4 level-param
//! closure, §5 infer_sort, §6 theorem-is-Prop, §7 check_type — compiled through Trust
//! (Rust -> MIR -> trust-ir -> trust-cg JIT) and executed IDENTICALLY to native Rust
//! over genuinely universe-POLYMORPHIC declarations.
//!
//! What this adds over the previously-verified `mir_real_expr_full_decl_check_roundtrip`:
//! that rung ran the gate over a simplified {Zero,Succ,Param} Level model with structural
//! level equality and a modeled imax. HERE the gate runs over the FULL production
//! `Level` {Zero, Succ, Max, IMax, Param}, with the ALREADY-VERIFIED
//! `Level::is_def_eq`/`normalize` universe-unification machinery wired in as def_eq's
//! `level_eq` — exactly the real kernel wiring (cert/expr_eq.rs:34) — and with the FULL
//! smart-constructor `imax` in infer_type's Pi rule and infer_sort. The differential
//! exercises: the imax(_,0)=0 edge, the imax(_,Succ..)=Max collapse, a REAL IMax node
//! produced by inference (IMax(succ u, u)), Max commutativity + Succ-offset distribution
//! + flatten/sort/dedup-same-base normalization inside §7's def_eq, and the §4
//! level-param closure walk through Max/IMax level trees.
//!
//! The embedded module below is the byte-verbatim `--mir-emit-closure check_decl_readonly`
//! output of the slice (a verbatim transcription of the kernel code; modeled boundaries
//! documented inline there and mirrored in this file's oracle):
//!   <dev-scratch>/t1-universe/clean_decl_universe_slice.rs
//! REGEN:
//!   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//!   cd $HOME/trust-ir/frontend && env -u RUSTUP_TOOLCHAIN RUSTC=$S/bin/rustc \
//!     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//!     $S/bin/cargo run --bin trust_ir_mir -- clean_decl_universe_slice.rs \
//!     --crate-type=lib --mir-emit-closure check_decl_readonly decl_universe.tir
//!
//! Oracle: native Rust (the mirror below, byte-equivalent to the slice) == JIT machine
//! code, over real heap inputs. Error payloads are compared deeply: universe payloads
//! (`TheoremTypeNotProp.sort`) structurally by deref'ing the Arc children the JIT built;
//! type-mismatch payloads (`TypeMismatch.expected/inferred`) node-by-node with the
//! recomputed ExprMeta word BIT-IDENTICAL at every node (which routes through the full
//! Level hash chain: mem::discriminant + Arc<Level> child hashing).
//!
//! NEGATIVE CONTROLS (fail-loud, self-arming — they run on every execution):
//!   NC1 an always-accept gate stub must DISAGREE with native on the wrong-universe
//!       definition (a soft differential would pass it — the assert panics).
//!   NC2 a deliberately-WRONG universe expectation (sort = Zero, and the arg-swapped
//!       IMax) must be REJECTED by the structural level comparator against the
//!       JIT-built sort (a comparator gone vacuous-true panics here).
//!   NC3 a meta-word-corrupted copy of the §7 mismatch payload (meta ^= 1) must be
//!       REJECTED by deep_eq (proves the bit-identity check actually reads meta).
//!
//! COVERAGE NOTE: gated to aarch64 (the JIT target). Run per-test:
//!   cargo test -p trust-cg-codegen --test e2e_universe_integration -- \
//!     --exact mir_decl_gate_full_universe_roundtrip --test-threads=1

#![cfg(target_arch = "aarch64")]
#![allow(dead_code)]
#![allow(clippy::all)]

#[cfg(kernel_fixture_layout_unknown)]
compile_error!(
    "kernel JIT fixtures require exact Rust 1.95.0, Rust 1.97.1, or the certified Trust compiler"
);

use std::collections::HashMap;
use std::sync::Arc;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

/// VERBATIM `--mir-emit-closure check_decl_readonly` emit of
/// clean_decl_universe_slice.rs (crate hash CshhXhIKvfvMU_). 211 functions: the
/// gate + infer_sort/check_type + the full infer_type/whnf/def_eq pillars + the
/// COMPLETE production-Level universe machinery (normalize/is_geq/imax/...),
/// extern only for true leaves (Vec/Arc/Result-Try/hash primitive shims below).
const MIR_DECL_UNIVERSE_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::Verifier::<'env>::check_decl_readonly"

functy.0 = (ptr) -> (u64)

functy.1 = (ptr, u64) -> (ptr)

functy.2 = (ptr, ptr) -> ()

functy.3 = (ptr, ptr, ptr) -> ()

functy.4 = (ptr, ptr) -> (bool)

functy.5 = (ptr) -> (bool)

functy.6 = (ptr) -> (bool)

functy.7 = (ptr) -> (bool)

functy.8 = (ptr, ptr) -> ()

functy.9 = (ptr) -> (u64)

functy.10 = (ptr, u64) -> (ptr)

functy.11 = (ptr, ptr) -> ()

functy.12 = (ptr, ptr, ptr) -> ()

functy.13 = (ptr) -> ()

functy.14 = (ptr, ptr, ptr) -> ()

functy.15 = (ptr) -> (bool)

functy.16 = (ptr, ptr) -> ()

functy.17 = (ptr, ptr) -> ()

functy.18 = (ptr, ptr, ptr, ptr) -> ()

functy.19 = (u64) -> (bool)

functy.20 = (u64) -> (bool)

functy.21 = (u64) -> (bool)

functy.22 = (ptr) -> (ptr)

functy.23 = (ptr, ptr) -> ()

functy.24 = (ptr, ptr) -> ()

functy.25 = (ptr, ptr, ptr) -> ()

functy.26 = (ptr, ptr) -> ()

functy.27 = (ptr, ptr) -> ()

functy.28 = (ptr, ptr) -> ()

functy.29 = (ptr) -> (ptr)

functy.30 = (ptr, ptr) -> ()

functy.31 = (ptr, ptr) -> ()

functy.32 = (ptr, ptr, ptr, u32, ptr) -> ()

functy.33 = (ptr) -> ()

functy.34 = (ptr, ptr, ptr) -> ()

functy.35 = (ptr, ptr, ptr) -> (bool)

functy.36 = (ptr, ptr) -> ()

functy.37 = (ptr) -> (u64)

functy.38 = (ptr, u64) -> (ptr)

functy.39 = (u32, u32) -> (u32)

functy.40 = (ptr, ptr) -> ()

functy.41 = (ptr, ptr) -> ()

functy.42 = (ptr) -> (ptr)

functy.43 = (ptr, ptr) -> ()

functy.44 = (ptr, ptr) -> ()

functy.45 = (ptr, ptr, ptr, ptr) -> ()

functy.46 = (ptr, ptr, ptr) -> ()

functy.47 = (ptr, ptr) -> ()

functy.48 = (ptr, ptr) -> ()

functy.49 = (ptr, ptr, ptr) -> ()

functy.50 = (ptr, ptr) -> (bool)

functy.51 = (ptr, ptr) -> (bool)

functy.52 = (ptr, ptr) -> (bool)

functy.53 = (ptr, ptr) -> (bool)

functy.54 = (ptr, ptr) -> ()

functy.55 = (ptr, ptr, ptr) -> (bool)

functy.56 = (ptr, ptr) -> ()

functy.57 = (ptr, ptr) -> ()

functy.58 = (ptr, ptr) -> ()

functy.59 = (ptr, ptr) -> ()

functy.60 = (ptr, ptr, ptr) -> ()

functy.61 = (ptr, ptr) -> ()

functy.62 = (ptr, ptr) -> ()

functy.63 = (u32, u32) -> (u32)

functy.64 = (ptr, ptr, u32, u32) -> ()

functy.65 = (ptr, ptr, ptr) -> ()

functy.66 = (ptr, ptr, ptr, ptr) -> ()

functy.67 = (ptr) -> ()

functy.68 = (ptr, u32) -> ()

functy.69 = (ptr, ptr) -> ()

functy.70 = (ptr, ptr, ptr) -> ()

functy.71 = (ptr, ptr) -> ()

functy.72 = (ptr) -> (bool)

functy.73 = (ptr, ptr, ptr) -> ()

functy.74 = (ptr) -> ()

functy.75 = (ptr, ptr) -> ()

functy.76 = (ptr, ptr) -> (bool)

functy.77 = (ptr, ptr) -> ()

functy.78 = (ptr, ptr) -> (bool)

functy.79 = (ptr, ptr) -> ()

functy.80 = (u64) -> (u64)

functy.81 = (ptr, ptr) -> (bool)

functy.82 = (ptr, ptr) -> (bool)

functy.83 = (ptr, ptr) -> (bool)

functy.84 = (ptr, ptr) -> (bool)

functy.85 = (ptr, ptr) -> ()

functy.86 = (ptr, ptr, ptr) -> (bool)

functy.87 = (ptr, ptr, ptr) -> (bool)

functy.88 = (ptr, ptr, ptr) -> (bool)

functy.89 = (ptr, ptr, ptr) -> (bool)

functy.90 = (ptr, ptr, ptr) -> (bool)

functy.91 = (ptr, ptr) -> ()

functy.92 = (ptr, ptr) -> ()

functy.93 = (ptr, ptr) -> ()

functy.94 = (ptr, ptr) -> ()

functy.95 = (ptr, ptr, ptr) -> ()

functy.96 = (ptr, ptr) -> ()

functy.97 = (ptr) -> (u32)

functy.98 = (ptr, u32) -> ()

functy.99 = (ptr, ptr, ptr) -> ()

functy.100 = (ptr, ptr, ptr, ptr) -> ()

functy.101 = (u32, u32) -> (u32)

functy.102 = (u32, u32) -> (u32)

functy.103 = (ptr, ptr, ptr, u32) -> ()

functy.104 = (ptr, ptr, ptr) -> ()

functy.105 = (ptr, ptr, ptr) -> ()

functy.106 = (ptr) -> (u64)

functy.107 = (ptr, u64) -> (ptr)

functy.108 = (ptr, ptr, ptr, u32, ptr) -> ()

functy.109 = (ptr, ptr) -> (bool)

functy.110 = (ptr, ptr) -> (bool)

functy.111 = (ptr, ptr, u32, u32) -> ()

functy.112 = (u32, u32) -> (u32)

functy.113 = (u32, u32) -> (u32)

functy.114 = (ptr, ptr) -> ()

functy.115 = (u64) -> (u32)

functy.116 = (ptr, u32, ptr, ptr, ptr, bool) -> ()

functy.117 = (ptr, u32, u32, ptr) -> ()

functy.118 = (ptr) -> (ptr)

functy.119 = (ptr, ptr) -> ()

functy.120 = (ptr, ptr, ptr) -> ()

functy.121 = (ptr) -> ()

functy.122 = (ptr) -> (ptr)

functy.123 = (ptr, ptr) -> ()

functy.124 = (ptr, ptr) -> ()

functy.125 = (ptr) -> ()

functy.126 = (ptr, ptr) -> ()

functy.127 = (ptr, ptr) -> ()

functy.128 = (ptr) -> (u64)

functy.129 = (ptr) -> (u64)

functy.130 = (ptr) -> (u64)

functy.131 = (u64, u64) -> (u64)

functy.132 = (u64, u64) -> (u64)

functy.133 = (u32, u32) -> (u32)

functy.134 = (ptr, u32, u32, u32, bool, bool, bool, bool) -> ()

functy.135 = (ptr, ptr) -> ()

functy.136 = (u8, u8) -> (u8)

functy.137 = (u32, u32) -> (u32)

functy.138 = (u32, u32) -> (u32)

functy.139 = (ptr, u64, u64) -> ()

functy.140 = (u8, u8) -> (u8)

functy.141 = (u32, u32) -> (u32)

functy.142 = (u32, u32) -> (u32)

functy.143 = (u32, u32) -> (u32)

functy.144 = (ptr, u64, u64, u64) -> ()

functy.145 = (ptr) -> (bool)

functy.146 = (ptr) -> (bool)

functy.147 = (u8, u8) -> (u8)

functy.148 = (u32, u32) -> (u32)

functy.149 = (u32, u32) -> (u32)

functy.150 = (u32, u32) -> (u32)

functy.151 = (ptr, u64, u64, u64) -> ()

functy.152 = (u64) -> (u8)

functy.153 = (u64) -> (u32)

functy.154 = (u64) -> (bool)

functy.155 = (u32, u32) -> (u32)

functy.156 = (ptr, u64, u64) -> ()

functy.157 = (ptr, ptr) -> ()

functy.158 = (ptr) -> ()

functy.159 = (ptr, ptr) -> ()

functy.160 = (ptr, ptr) -> ()

functy.161 = (ptr, ptr) -> ()

functy.162 = (ptr, ptr) -> ()

functy.163 = (ptr) -> (u64)

functy.164 = (ptr, ptr) -> ()

functy.165 = (ptr, ptr) -> ()

functy.166 = (ptr, ptr) -> ()

functy.167 = (ptr, ptr) -> ()

functy.168 = (ptr, ptr) -> ()

functy.169 = (ptr, ptr) -> ()

functy.170 = (u32, u32) -> (u32)

functy.171 = (ptr, ptr) -> ()

functy.172 = (ptr) -> ()

functy.173 = (ptr) -> (u64)

functy.174 = (ptr, u64) -> (ptr)

functy.175 = (ptr, ptr) -> ()

functy.176 = (ptr, u64, u64) -> ()

functy.177 = (ptr, ptr) -> ()

functy.178 = (ptr, u64) -> (ptr)

functy.179 = (ptr) -> (bool)

functy.180 = (ptr, ptr, u32) -> ()

functy.181 = (ptr, ptr, u32) -> ()

functy.182 = (ptr, ptr) -> ()

functy.183 = (ptr, ptr) -> ()

functy.184 = (ptr, ptr) -> ()

functy.185 = (ptr, ptr) -> ()

functy.186 = (ptr, ptr) -> (bool)

functy.187 = (ptr, ptr) -> (bool)

functy.188 = (ptr, ptr) -> (bool)

functy.189 = (ptr, ptr) -> (bool)

functy.190 = (ptr, ptr) -> (bool)

functy.191 = (ptr) -> ()

functy.192 = (ptr, ptr) -> ()

functy.193 = (ptr, ptr) -> (bool)

functy.194 = (ptr, ptr) -> ()

functy.195 = (ptr, ptr) -> ()

functy.196 = (ptr, ptr) -> ()

functy.197 = (ptr) -> ()

functy.198 = (ptr) -> (u64)

functy.199 = (ptr, u64) -> (ptr)

functy.200 = (ptr, ptr) -> ()

functy.201 = (ptr, ptr) -> ()

functy.202 = (ptr, ptr) -> ()

functy.203 = (ptr) -> (u8)

functy.204 = (ptr) -> (bool)

functy.205 = (ptr, ptr) -> ()

functy.206 = (ptr, ptr) -> (bool)

functy.207 = (ptr, ptr) -> ()

functy.208 = (ptr, ptr) -> (bool)

functy.209 = (ptr, ptr) -> (bool)

functy.210 = (ptr, ptr) -> (bool)

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4NameE3lenBG_(functy.0) {
}

fn @_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4NameEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_(functy.1) {
}

fn @_RNvXs7_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4NameENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefBH_(functy.2) {
}

fn @Verifier____env___check_decl_readonly(functy.3) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %321 = alloca i64, align 8
    %322 = alloca i64, align 8
    %323 = alloca (i64, i64, i64, i64, i64), align 8
    %324 = alloca i64, align 8
    %325 = alloca i64, align 8
    %326 = alloca i64, align 8
    %327 = alloca i64, align 8
    %328 = alloca (i64, i64, i64, i64), align 8
    %329 = alloca i32, align 4
    %330 = alloca i32, align 4
    %331 = alloca (i64, i64), align 8
    %332 = alloca (i64, i64), align 8
    %333 = alloca (i64, i64, i64, i64), align 8
    %334 = alloca i32, align 4
    %335 = alloca (i64, i64, i64, i64), align 8
    %336 = alloca i32, align 4
    %337 = alloca (i64, i64, i64, i64), align 8
    %338 = alloca i32, align 4
    %339 = alloca (i64, i64, i64, i64), align 8
    %340 = alloca i32, align 4
    %341 = alloca (i32, i32), align 4
    %342 = alloca (i64, i64), align 8
    %343 = alloca i32, align 4
    %344 = alloca (i64, i64, i64, i64), align 8
    %345 = alloca i32, align 4
    %346 = alloca (i32, i32), align 4
    %347 = alloca (i64, i64), align 8
    %348 = alloca i32, align 4
    %349 = alloca (i64, i64, i64, i64), align 8
    %350 = alloca i32, align 4
    %351 = alloca (i64, i64, i64), align 8
    %352 = alloca (i64, i64, i64, i64), align 8
    %353 = alloca (i64, i64, i64), align 8
    %354 = alloca (i64, i64, i64), align 8
    %355 = alloca (i64, i64, i64, i64), align 8
    %356 = alloca i32, align 4
    %357 = alloca (i64, i64, i64, i64), align 8
    %358 = alloca i32, align 4
    %359 = alloca (i64, i64, i64), align 8
    %360 = alloca (i64, i64, i64), align 8
    %361 = alloca (i64, i64, i64), align 8
    %362 = alloca (i64, i64, i64, i64), align 8
    %363 = alloca i32, align 4
    store ptr %2, ptr %321
    %364 = const bool false
    %365 = load ptr, ptr %321
    %366 = load i8, ptr %365
    %367 = sext i8 %366 to i64
    switch %367 [ 0: bb5(%1) 1: bb4(%1) 2: bb3(%1) 3: bb2(%1) default: bb1 ]
bb1:
    unreachable
bb2(%3: ptr):
    %368 = load ptr, ptr %321
    %369 = const i64 4
    %370 = gep i8, ptr %368, %369
    %371 = load ptr, ptr %321
    %372 = const i64 24
    %373 = gep i8, ptr %371, %372
    %374 = load ptr, ptr %321
    %375 = const i64 8
    %376 = gep i8, ptr %374, %375
    %377 = load ptr, ptr %321
    %378 = const i64 16
    %379 = gep i8, ptr %377, %378
    store ptr %379, ptr %327
    store ptr %370, ptr %323
    %380 = const i64 8
    %381 = gep i8, ptr %323, %380
    store ptr %373, ptr %381
    %382 = const i64 16
    %383 = gep i8, ptr %323, %382
    store ptr %376, ptr %383
    %384 = load ptr, ptr %327
    %385 = const i64 24
    %386 = gep i8, ptr %323, %385
    store ptr %384, ptr %386
    %387 = const bool false
    %388 = const i64 32
    %389 = gep i8, ptr %323, %388
    store bool %387, ptr %389
    br bb6(%3)
bb3(%4: ptr):
    %390 = load ptr, ptr %321
    %391 = const i64 4
    %392 = gep i8, ptr %390, %391
    %393 = load ptr, ptr %321
    %394 = const i64 24
    %395 = gep i8, ptr %393, %394
    %396 = load ptr, ptr %321
    %397 = const i64 8
    %398 = gep i8, ptr %396, %397
    %399 = load ptr, ptr %321
    %400 = const i64 16
    %401 = gep i8, ptr %399, %400
    store ptr %401, ptr %326
    store ptr %392, ptr %323
    %402 = const i64 8
    %403 = gep i8, ptr %323, %402
    store ptr %395, ptr %403
    %404 = const i64 16
    %405 = gep i8, ptr %323, %404
    store ptr %398, ptr %405
    %406 = load ptr, ptr %326
    %407 = const i64 24
    %408 = gep i8, ptr %323, %407
    store ptr %406, ptr %408
    %409 = const bool true
    %410 = const i64 32
    %411 = gep i8, ptr %323, %410
    store bool %409, ptr %411
    br bb6(%4)
bb4(%5: ptr):
    %412 = load ptr, ptr %321
    %413 = const i64 4
    %414 = gep i8, ptr %412, %413
    %415 = load ptr, ptr %321
    %416 = const i64 16
    %417 = gep i8, ptr %415, %416
    %418 = load ptr, ptr %321
    %419 = const i64 8
    %420 = gep i8, ptr %418, %419
    %421 = const i64 0
    store i64 %421, ptr %325
    store ptr %414, ptr %323
    %422 = const i64 8
    %423 = gep i8, ptr %323, %422
    store ptr %417, ptr %423
    %424 = const i64 16
    %425 = gep i8, ptr %323, %424
    store ptr %420, ptr %425
    %426 = load ptr, ptr %325
    %427 = const i64 24
    %428 = gep i8, ptr %323, %427
    store ptr %426, ptr %428
    %429 = const bool false
    %430 = const i64 32
    %431 = gep i8, ptr %323, %430
    store bool %429, ptr %431
    br bb6(%5)
bb5(%6: ptr):
    %432 = load ptr, ptr %321
    %433 = const i64 4
    %434 = gep i8, ptr %432, %433
    %435 = load ptr, ptr %321
    %436 = const i64 24
    %437 = gep i8, ptr %435, %436
    %438 = load ptr, ptr %321
    %439 = const i64 8
    %440 = gep i8, ptr %438, %439
    %441 = load ptr, ptr %321
    %442 = const i64 16
    %443 = gep i8, ptr %441, %442
    store ptr %443, ptr %324
    store ptr %434, ptr %323
    %444 = const i64 8
    %445 = gep i8, ptr %323, %444
    store ptr %437, ptr %445
    %446 = const i64 16
    %447 = gep i8, ptr %323, %446
    store ptr %440, ptr %447
    %448 = load ptr, ptr %324
    %449 = const i64 24
    %450 = gep i8, ptr %323, %449
    store ptr %448, ptr %450
    %451 = const bool false
    %452 = const i64 32
    %453 = gep i8, ptr %323, %452
    store bool %451, ptr %453
    br bb6(%6)
bb6(%7: ptr):
    %454 = load ptr, ptr %323
    %455 = const i64 8
    %456 = gep i8, ptr %323, %455
    %457 = load ptr, ptr %456
    %458 = const i64 16
    %459 = gep i8, ptr %323, %458
    %460 = load ptr, ptr %459
    %461 = const i64 24
    %462 = gep i8, ptr %323, %461
    %463 = load i64, ptr %462
    store i64 %463, ptr %322
    %464 = const i64 32
    %465 = gep i8, ptr %323, %464
    %466 = load bool, ptr %465
    %467 = call @func.0(%457)
    br bb7(%7, %454, %457, %460, %466, %467)
bb7(%8: ptr, %9: ptr, %10: ptr, %11: ptr, %12: bool, %13: u64):
    %468 = const u64 0
    br bb8(%8, %9, %10, %11, %12, %13, %468)
bb8(%14: ptr, %15: ptr, %16: ptr, %17: ptr, %18: bool, %19: u64, %20: u64):
    %469 = icmp ult u64 %20, %19
    condbr %469, bb9(%14, %15, %16, %17, %18, %19, %20), bb21(%14, %15, %16, %17, %18)
bb9(%21: ptr, %22: ptr, %23: ptr, %24: ptr, %25: bool, %26: u64, %27: u64):
    %470 = const u64 0
    br bb10(%21, %22, %23, %24, %25, %26, %27, %470)
bb10(%28: ptr, %29: ptr, %30: ptr, %31: ptr, %32: bool, %33: u64, %34: u64, %35: u64):
    %471 = icmp ult u64 %35, %34
    condbr %471, bb11(%28, %29, %30, %31, %32, %33, %34, %35), bb19(%28, %29, %30, %31, %32, %33, %34)
bb11(%36: ptr, %37: ptr, %38: ptr, %39: ptr, %40: bool, %41: u64, %42: u64, %43: u64):
    %472 = call @func.1(%38, %43)
    br bb12(%36, %37, %38, %39, %40, %41, %42, %43, %472)
bb12(%44: ptr, %45: ptr, %46: ptr, %47: ptr, %48: bool, %49: u64, %50: u64, %51: u64, %52: ptr):
    %473 = call @func.1(%46, %50)
    br bb13(%44, %45, %46, %47, %48, %49, %50, %51, %52, %473)
bb13(%53: ptr, %54: ptr, %55: ptr, %56: ptr, %57: bool, %58: u64, %59: u64, %60: u64, %61: ptr, %62: ptr):
    %474 = call @func.4(%61, %62)
    br bb14(%53, %54, %55, %56, %57, %58, %59, %60, %474)
bb14(%63: ptr, %64: ptr, %65: ptr, %66: ptr, %67: bool, %68: u64, %69: u64, %70: u64, %71: bool):
    condbr %71, bb15(%64, %65, %69), bb17(%63, %64, %65, %66, %67, %68, %69, %70)
bb15(%72: ptr, %73: ptr, %74: u64):
    %475 = load i32, ptr %72
    store i32 %475, ptr %329
    %476 = call @func.1(%73, %74)
    br bb16(%476)
bb16(%75: ptr):
    %477 = load i32, ptr %75
    store i32 %477, ptr %330
    %478 = const i64 4
    %479 = gep i8, ptr %328, %478
    %480 = load i32, ptr %329
    store i32 %480, ptr %479
    %481 = const i64 8
    %482 = gep i8, ptr %328, %481
    %483 = load i32, ptr %330
    store i32 %483, ptr %482
    %484 = const i32 1
    store i32 %484, ptr %328
    %485 = load i64, ptr %328
    store i64 %485, ptr %0
    %486 = const i64 8
    %487 = gep i8, ptr %328, %486
    %488 = const i64 8
    %489 = gep i8, ptr %0, %488
    %490 = load i64, ptr %487
    store i64 %490, ptr %489
    %491 = const i64 16
    %492 = gep i8, ptr %328, %491
    %493 = const i64 16
    %494 = gep i8, ptr %0, %493
    %495 = load i64, ptr %492
    store i64 %495, ptr %494
    %496 = const i64 24
    %497 = gep i8, ptr %328, %496
    %498 = const i64 24
    %499 = gep i8, ptr %0, %498
    %500 = load i64, ptr %497
    store i64 %500, ptr %499
    br bb72
bb17(%76: ptr, %77: ptr, %78: ptr, %79: ptr, %80: bool, %81: u64, %82: u64, %83: u64):
    %501 = const u64 1
    %502, %503 = add.overflow u64 %83, %501
    store u64 %502, ptr %331
    %504 = const i64 8
    %505 = gep i8, ptr %331, %504
    store bool %503, ptr %505
    %506 = const i64 8
    %507 = gep i8, ptr %331, %506
    %508 = load bool, ptr %507
    %509 = const bool false
    %510 = icmp eq bool %508, %509
    condbr %510, bb18(%76, %77, %78, %79, %80, %81, %82), bb75
bb18(%84: ptr, %85: ptr, %86: ptr, %87: ptr, %88: bool, %89: u64, %90: u64):
    %511 = load u64, ptr %331
    br bb10(%84, %85, %86, %87, %88, %89, %90, %511)
bb19(%91: ptr, %92: ptr, %93: ptr, %94: ptr, %95: bool, %96: u64, %97: u64):
    %512 = const u64 1
    %513, %514 = add.overflow u64 %97, %512
    store u64 %513, ptr %332
    %515 = const i64 8
    %516 = gep i8, ptr %332, %515
    store bool %514, ptr %516
    %517 = const i64 8
    %518 = gep i8, ptr %332, %517
    %519 = load bool, ptr %518
    %520 = const bool false
    %521 = icmp eq bool %519, %520
    condbr %521, bb20(%91, %92, %93, %94, %95, %96), bb75
bb20(%98: ptr, %99: ptr, %100: ptr, %101: ptr, %102: bool, %103: u64):
    %522 = load u64, ptr %332
    br bb8(%98, %99, %100, %101, %102, %103, %522)
bb21(%104: ptr, %105: ptr, %106: ptr, %107: ptr, %108: bool):
    %523 = load ptr, ptr %107
    %524 = const i64 16
    %525 = gep i8, ptr %523, %524
    br bb22(%104, %105, %106, %107, %108, %525)
bb22(%109: ptr, %110: ptr, %111: ptr, %112: ptr, %113: bool, %114: ptr):
    %526 = call @func.5(%114)
    br bb23(%109, %110, %111, %112, %113, %526)
bb23(%115: ptr, %116: ptr, %117: ptr, %118: ptr, %119: bool, %120: bool):
    condbr %120, bb27(%116), bb24(%115, %116, %117, %118, %119)
bb24(%121: ptr, %122: ptr, %123: ptr, %124: ptr, %125: bool):
    %527 = load ptr, ptr %124
    %528 = const i64 16
    %529 = gep i8, ptr %527, %528
    br bb25(%121, %122, %123, %124, %125, %529)
bb25(%126: ptr, %127: ptr, %128: ptr, %129: ptr, %130: bool, %131: ptr):
    %530 = call @func.6(%131)
    br bb26(%126, %127, %128, %129, %130, %530)
bb26(%132: ptr, %133: ptr, %134: ptr, %135: ptr, %136: bool, %137: bool):
    condbr %137, bb27(%133), bb28(%132, %133, %134, %135, %136)
bb27(%138: ptr):
    %531 = load i32, ptr %138
    store i32 %531, ptr %334
    %532 = const i64 4
    %533 = gep i8, ptr %333, %532
    %534 = load i32, ptr %334
    store i32 %534, ptr %533
    %535 = const i32 4
    store i32 %535, ptr %333
    %536 = load i64, ptr %333
    store i64 %536, ptr %0
    %537 = const i64 8
    %538 = gep i8, ptr %333, %537
    %539 = const i64 8
    %540 = gep i8, ptr %0, %539
    %541 = load i64, ptr %538
    store i64 %541, ptr %540
    %542 = const i64 16
    %543 = gep i8, ptr %333, %542
    %544 = const i64 16
    %545 = gep i8, ptr %0, %544
    %546 = load i64, ptr %543
    store i64 %546, ptr %545
    %547 = const i64 24
    %548 = gep i8, ptr %333, %547
    %549 = const i64 24
    %550 = gep i8, ptr %0, %549
    %551 = load i64, ptr %548
    store i64 %551, ptr %550
    br bb72
bb28(%139: ptr, %140: ptr, %141: ptr, %142: ptr, %143: bool):
    %552 = load ptr, ptr %142
    %553 = const i64 16
    %554 = gep i8, ptr %552, %553
    br bb29(%139, %140, %141, %142, %143, %554)
bb29(%144: ptr, %145: ptr, %146: ptr, %147: ptr, %148: bool, %149: ptr):
    %555 = call @func.7(%149)
    br bb30(%144, %145, %146, %147, %148, %555)
bb30(%150: ptr, %151: ptr, %152: ptr, %153: ptr, %154: bool, %155: bool):
    condbr %155, bb31(%151), bb32(%150, %151, %152, %153, %154)
bb31(%156: ptr):
    %556 = load i32, ptr %156
    store i32 %556, ptr %336
    %557 = const i64 4
    %558 = gep i8, ptr %335, %557
    %559 = load i32, ptr %336
    store i32 %559, ptr %558
    %560 = const i32 3
    store i32 %560, ptr %335
    %561 = load i64, ptr %335
    store i64 %561, ptr %0
    %562 = const i64 8
    %563 = gep i8, ptr %335, %562
    %564 = const i64 8
    %565 = gep i8, ptr %0, %564
    %566 = load i64, ptr %563
    store i64 %566, ptr %565
    %567 = const i64 16
    %568 = gep i8, ptr %335, %567
    %569 = const i64 16
    %570 = gep i8, ptr %0, %569
    %571 = load i64, ptr %568
    store i64 %571, ptr %570
    %572 = const i64 24
    %573 = gep i8, ptr %335, %572
    %574 = const i64 24
    %575 = gep i8, ptr %0, %574
    %576 = load i64, ptr %573
    store i64 %576, ptr %575
    br bb72
bb32(%157: ptr, %158: ptr, %159: ptr, %160: ptr, %161: bool):
    %577 = load i64, ptr %322
    %578 = const i64 0
    %579 = icmp eq i64 %577, %578
    %580 = const i64 0
    %581 = const i64 1
    %582 = select i64 %579, %580, %581
    switch %582 [ 1: bb33(%157, %158, %159, %160, %161) 0: bb44(%157, %158, %159, %160, %161) default: bb1 ]
bb33(%162: ptr, %163: ptr, %164: ptr, %165: ptr, %166: bool):
    %583 = load ptr, ptr %322
    %584 = load ptr, ptr %583
    %585 = const i64 16
    %586 = gep i8, ptr %584, %585
    br bb34(%162, %163, %164, %165, %166, %583, %586)
bb34(%167: ptr, %168: ptr, %169: ptr, %170: ptr, %171: bool, %172: ptr, %173: ptr):
    %587 = call @func.5(%173)
    br bb35(%167, %168, %169, %170, %171, %172, %587)
bb35(%174: ptr, %175: ptr, %176: ptr, %177: ptr, %178: bool, %179: ptr, %180: bool):
    condbr %180, bb39(%175), bb36(%174, %175, %176, %177, %178, %179)
bb36(%181: ptr, %182: ptr, %183: ptr, %184: ptr, %185: bool, %186: ptr):
    %588 = load ptr, ptr %186
    %589 = const i64 16
    %590 = gep i8, ptr %588, %589
    br bb37(%181, %182, %183, %184, %185, %186, %590)
bb37(%187: ptr, %188: ptr, %189: ptr, %190: ptr, %191: bool, %192: ptr, %193: ptr):
    %591 = call @func.6(%193)
    br bb38(%187, %188, %189, %190, %191, %192, %591)
bb38(%194: ptr, %195: ptr, %196: ptr, %197: ptr, %198: bool, %199: ptr, %200: bool):
    condbr %200, bb39(%195), bb40(%194, %195, %196, %197, %198, %199)
bb39(%201: ptr):
    %592 = load i32, ptr %201
    store i32 %592, ptr %338
    %593 = const i64 4
    %594 = gep i8, ptr %337, %593
    %595 = load i32, ptr %338
    store i32 %595, ptr %594
    %596 = const i32 4
    store i32 %596, ptr %337
    %597 = load i64, ptr %337
    store i64 %597, ptr %0
    %598 = const i64 8
    %599 = gep i8, ptr %337, %598
    %600 = const i64 8
    %601 = gep i8, ptr %0, %600
    %602 = load i64, ptr %599
    store i64 %602, ptr %601
    %603 = const i64 16
    %604 = gep i8, ptr %337, %603
    %605 = const i64 16
    %606 = gep i8, ptr %0, %605
    %607 = load i64, ptr %604
    store i64 %607, ptr %606
    %608 = const i64 24
    %609 = gep i8, ptr %337, %608
    %610 = const i64 24
    %611 = gep i8, ptr %0, %610
    %612 = load i64, ptr %609
    store i64 %612, ptr %611
    br bb72
bb40(%202: ptr, %203: ptr, %204: ptr, %205: ptr, %206: bool, %207: ptr):
    %613 = load ptr, ptr %207
    %614 = const i64 16
    %615 = gep i8, ptr %613, %614
    br bb41(%202, %203, %204, %205, %206, %615)
bb41(%208: ptr, %209: ptr, %210: ptr, %211: ptr, %212: bool, %213: ptr):
    %616 = call @func.7(%213)
    br bb42(%208, %209, %210, %211, %212, %616)
bb42(%214: ptr, %215: ptr, %216: ptr, %217: ptr, %218: bool, %219: bool):
    condbr %219, bb43(%215), bb44(%214, %215, %216, %217, %218)
bb43(%220: ptr):
    %617 = load i32, ptr %220
    store i32 %617, ptr %340
    %618 = const i64 4
    %619 = gep i8, ptr %339, %618
    %620 = load i32, ptr %340
    store i32 %620, ptr %619
    %621 = const i32 3
    store i32 %621, ptr %339
    %622 = load i64, ptr %339
    store i64 %622, ptr %0
    %623 = const i64 8
    %624 = gep i8, ptr %339, %623
    %625 = const i64 8
    %626 = gep i8, ptr %0, %625
    %627 = load i64, ptr %624
    store i64 %627, ptr %626
    %628 = const i64 16
    %629 = gep i8, ptr %339, %628
    %630 = const i64 16
    %631 = gep i8, ptr %0, %630
    %632 = load i64, ptr %629
    store i64 %632, ptr %631
    %633 = const i64 24
    %634 = gep i8, ptr %339, %633
    %635 = const i64 24
    %636 = gep i8, ptr %0, %635
    %637 = load i64, ptr %634
    store i64 %637, ptr %636
    br bb72
bb44(%221: ptr, %222: ptr, %223: ptr, %224: ptr, %225: bool):
    %638 = load ptr, ptr %224
    %639 = const i64 16
    %640 = gep i8, ptr %638, %639
    br bb45(%221, %222, %223, %224, %225, %640)
bb45(%226: ptr, %227: ptr, %228: ptr, %229: ptr, %230: bool, %231: ptr):
    call @func.2(%342, %228)
    br bb46(%226, %227, %228, %229, %230, %231)
bb46(%232: ptr, %233: ptr, %234: ptr, %235: ptr, %236: bool, %237: ptr):
    call @func.12(%341, %237, %342)
    br bb47(%232, %233, %234, %235, %236)
bb47(%238: ptr, %239: ptr, %240: ptr, %241: ptr, %242: bool):
    %641 = load i32, ptr %341
    %642 = sext i32 %641 to i64
    switch %642 [ 1: bb48(%239) 0: bb49(%238, %239, %240, %241, %242) default: bb1 ]
bb48(%243: ptr):
    %643 = const i64 4
    %644 = gep i8, ptr %341, %643
    %645 = load i32, ptr %644
    store i32 %645, ptr %343
    %646 = load i32, ptr %243
    store i32 %646, ptr %345
    %647 = const i64 4
    %648 = gep i8, ptr %344, %647
    %649 = load i32, ptr %345
    store i32 %649, ptr %648
    %650 = const i64 8
    %651 = gep i8, ptr %344, %650
    %652 = load i32, ptr %343
    store i32 %652, ptr %651
    %653 = const i32 5
    store i32 %653, ptr %344
    %654 = load i64, ptr %344
    store i64 %654, ptr %0
    %655 = const i64 8
    %656 = gep i8, ptr %344, %655
    %657 = const i64 8
    %658 = gep i8, ptr %0, %657
    %659 = load i64, ptr %656
    store i64 %659, ptr %658
    %660 = const i64 16
    %661 = gep i8, ptr %344, %660
    %662 = const i64 16
    %663 = gep i8, ptr %0, %662
    %664 = load i64, ptr %661
    store i64 %664, ptr %663
    %665 = const i64 24
    %666 = gep i8, ptr %344, %665
    %667 = const i64 24
    %668 = gep i8, ptr %0, %667
    %669 = load i64, ptr %666
    store i64 %669, ptr %668
    br bb72
bb49(%244: ptr, %245: ptr, %246: ptr, %247: ptr, %248: bool):
    %670 = load i64, ptr %322
    %671 = const i64 0
    %672 = icmp eq i64 %670, %671
    %673 = const i64 0
    %674 = const i64 1
    %675 = select i64 %672, %673, %674
    switch %675 [ 1: bb50(%244, %245, %246, %247, %248) 0: bb55(%244, %245, %247, %248) default: bb1 ]
bb50(%249: ptr, %250: ptr, %251: ptr, %252: ptr, %253: bool):
    %676 = load ptr, ptr %322
    %677 = load ptr, ptr %676
    %678 = const i64 16
    %679 = gep i8, ptr %677, %678
    br bb51(%249, %250, %251, %252, %253, %679)
bb51(%254: ptr, %255: ptr, %256: ptr, %257: ptr, %258: bool, %259: ptr):
    call @func.2(%347, %256)
    br bb52(%254, %255, %257, %258, %259)
bb52(%260: ptr, %261: ptr, %262: ptr, %263: bool, %264: ptr):
    call @func.12(%346, %264, %347)
    br bb53(%260, %261, %262, %263)
bb53(%265: ptr, %266: ptr, %267: ptr, %268: bool):
    %680 = load i32, ptr %346
    %681 = sext i32 %680 to i64
    switch %681 [ 1: bb54(%266) 0: bb55(%265, %266, %267, %268) default: bb1 ]
bb54(%269: ptr):
    %682 = const i64 4
    %683 = gep i8, ptr %346, %682
    %684 = load i32, ptr %683
    store i32 %684, ptr %348
    %685 = load i32, ptr %269
    store i32 %685, ptr %350
    %686 = const i64 4
    %687 = gep i8, ptr %349, %686
    %688 = load i32, ptr %350
    store i32 %688, ptr %687
    %689 = const i64 8
    %690 = gep i8, ptr %349, %689
    %691 = load i32, ptr %348
    store i32 %691, ptr %690
    %692 = const i32 5
    store i32 %692, ptr %349
    %693 = load i64, ptr %349
    store i64 %693, ptr %0
    %694 = const i64 8
    %695 = gep i8, ptr %349, %694
    %696 = const i64 8
    %697 = gep i8, ptr %0, %696
    %698 = load i64, ptr %695
    store i64 %698, ptr %697
    %699 = const i64 16
    %700 = gep i8, ptr %349, %699
    %701 = const i64 16
    %702 = gep i8, ptr %0, %701
    %703 = load i64, ptr %700
    store i64 %703, ptr %702
    %704 = const i64 24
    %705 = gep i8, ptr %349, %704
    %706 = const i64 24
    %707 = gep i8, ptr %0, %706
    %708 = load i64, ptr %705
    store i64 %708, ptr %707
    br bb72
bb55(%270: ptr, %271: ptr, %272: ptr, %273: bool):
    %709 = load ptr, ptr %272
    %710 = const i64 16
    %711 = gep i8, ptr %709, %710
    br bb56(%270, %271, %272, %273, %711)
bb56(%274: ptr, %275: ptr, %276: ptr, %277: bool, %278: ptr):
    call @func.14(%352, %274, %278)
    br bb57(%274, %275, %276, %277)
bb57(%279: ptr, %280: ptr, %281: ptr, %282: bool):
    %712 = load i64, ptr %352
    switch %712 [ 0: bb59(%279, %280, %281, %282) 1: bb58(%280) default: bb1 ]
bb58(%283: ptr):
    %713 = const i64 8
    %714 = gep i8, ptr %352, %713
    %715 = load i64, ptr %714
    store i64 %715, ptr %354
    %716 = const i64 8
    %717 = gep i8, ptr %714, %716
    %718 = const i64 8
    %719 = gep i8, ptr %354, %718
    %720 = load i64, ptr %717
    store i64 %720, ptr %719
    %721 = const i64 16
    %722 = gep i8, ptr %714, %721
    %723 = const i64 16
    %724 = gep i8, ptr %354, %723
    %725 = load i64, ptr %722
    store i64 %725, ptr %724
    %726 = load i32, ptr %283
    store i32 %726, ptr %356
    %727 = const i64 4
    %728 = gep i8, ptr %355, %727
    %729 = load i32, ptr %356
    store i32 %729, ptr %728
    %730 = const i64 8
    %731 = gep i8, ptr %355, %730
    %732 = load i64, ptr %354
    store i64 %732, ptr %731
    %733 = const i64 8
    %734 = gep i8, ptr %354, %733
    %735 = const i64 8
    %736 = gep i8, ptr %731, %735
    %737 = load i64, ptr %734
    store i64 %737, ptr %736
    %738 = const i64 16
    %739 = gep i8, ptr %354, %738
    %740 = const i64 16
    %741 = gep i8, ptr %731, %740
    %742 = load i64, ptr %739
    store i64 %742, ptr %741
    %743 = const i32 0
    store i32 %743, ptr %355
    %744 = load i64, ptr %355
    store i64 %744, ptr %0
    %745 = const i64 8
    %746 = gep i8, ptr %355, %745
    %747 = const i64 8
    %748 = gep i8, ptr %0, %747
    %749 = load i64, ptr %746
    store i64 %749, ptr %748
    %750 = const i64 16
    %751 = gep i8, ptr %355, %750
    %752 = const i64 16
    %753 = gep i8, ptr %0, %752
    %754 = load i64, ptr %751
    store i64 %754, ptr %753
    %755 = const i64 24
    %756 = gep i8, ptr %355, %755
    %757 = const i64 24
    %758 = gep i8, ptr %0, %757
    %759 = load i64, ptr %756
    store i64 %759, ptr %758
    br bb71
bb59(%284: ptr, %285: ptr, %286: ptr, %287: bool):
    %760 = const i64 8
    %761 = gep i8, ptr %352, %760
    %762 = load i64, ptr %761
    store i64 %762, ptr %353
    %763 = const i64 8
    %764 = gep i8, ptr %761, %763
    %765 = const i64 8
    %766 = gep i8, ptr %353, %765
    %767 = load i64, ptr %764
    store i64 %767, ptr %766
    %768 = const i64 16
    %769 = gep i8, ptr %761, %768
    %770 = const i64 16
    %771 = gep i8, ptr %353, %770
    %772 = load i64, ptr %769
    store i64 %772, ptr %771
    %773 = const bool true
    %774 = load i64, ptr %353
    store i64 %774, ptr %351
    %775 = const i64 8
    %776 = gep i8, ptr %353, %775
    %777 = const i64 8
    %778 = gep i8, ptr %351, %777
    %779 = load i64, ptr %776
    store i64 %779, ptr %778
    %780 = const i64 16
    %781 = gep i8, ptr %353, %780
    %782 = const i64 16
    %783 = gep i8, ptr %351, %782
    %784 = load i64, ptr %781
    store i64 %784, ptr %783
    condbr %287, bb60(%284, %285, %286, %773), bb63(%284, %285, %286, %773)
bb60(%288: ptr, %289: ptr, %290: ptr, %291: bool):
    %785 = call @func.15(%351)
    br bb61(%288, %289, %290, %785, %291)
bb61(%292: ptr, %293: ptr, %294: ptr, %295: bool, %296: bool):
    condbr %295, bb63(%292, %293, %294, %296), bb62(%293)
bb62(%297: ptr):
    %786 = load i32, ptr %297
    store i32 %786, ptr %358
    %787 = const bool false
    %788 = load i64, ptr %351
    store i64 %788, ptr %359
    %789 = const i64 8
    %790 = gep i8, ptr %351, %789
    %791 = const i64 8
    %792 = gep i8, ptr %359, %791
    %793 = load i64, ptr %790
    store i64 %793, ptr %792
    %794 = const i64 16
    %795 = gep i8, ptr %351, %794
    %796 = const i64 16
    %797 = gep i8, ptr %359, %796
    %798 = load i64, ptr %795
    store i64 %798, ptr %797
    %799 = const i64 4
    %800 = gep i8, ptr %357, %799
    %801 = load i32, ptr %358
    store i32 %801, ptr %800
    %802 = const i64 8
    %803 = gep i8, ptr %357, %802
    %804 = load i64, ptr %359
    store i64 %804, ptr %803
    %805 = const i64 8
    %806 = gep i8, ptr %359, %805
    %807 = const i64 8
    %808 = gep i8, ptr %803, %807
    %809 = load i64, ptr %806
    store i64 %809, ptr %808
    %810 = const i64 16
    %811 = gep i8, ptr %359, %810
    %812 = const i64 16
    %813 = gep i8, ptr %803, %812
    %814 = load i64, ptr %811
    store i64 %814, ptr %813
    %815 = const i32 2
    store i32 %815, ptr %357
    %816 = load i64, ptr %357
    store i64 %816, ptr %0
    %817 = const i64 8
    %818 = gep i8, ptr %357, %817
    %819 = const i64 8
    %820 = gep i8, ptr %0, %819
    %821 = load i64, ptr %818
    store i64 %821, ptr %820
    %822 = const i64 16
    %823 = gep i8, ptr %357, %822
    %824 = const i64 16
    %825 = gep i8, ptr %0, %824
    %826 = load i64, ptr %823
    store i64 %826, ptr %825
    %827 = const i64 24
    %828 = gep i8, ptr %357, %827
    %829 = const i64 24
    %830 = gep i8, ptr %0, %829
    %831 = load i64, ptr %828
    store i64 %831, ptr %830
    br bb74(%787)
bb63(%298: ptr, %299: ptr, %300: ptr, %301: bool):
    %832 = load i64, ptr %322
    %833 = const i64 0
    %834 = icmp eq i64 %832, %833
    %835 = const i64 0
    %836 = const i64 1
    %837 = select i64 %834, %835, %836
    switch %837 [ 1: bb64(%298, %299, %300, %301) 0: bb69 default: bb1 ]
bb64(%302: ptr, %303: ptr, %304: ptr, %305: bool):
    %838 = load ptr, ptr %322
    %839 = load ptr, ptr %838
    %840 = const i64 16
    %841 = gep i8, ptr %839, %840
    br bb65(%302, %303, %304, %841, %305)
bb65(%306: ptr, %307: ptr, %308: ptr, %309: ptr, %310: bool):
    %842 = load ptr, ptr %308
    %843 = const i64 16
    %844 = gep i8, ptr %842, %843
    br bb66(%306, %307, %309, %844, %310)
bb66(%311: ptr, %312: ptr, %313: ptr, %314: ptr, %315: bool):
    call @func.18(%360, %311, %313, %314)
    br bb67(%312, %315)
bb67(%316: ptr, %317: bool):
    %845 = load i32, ptr %360
    %846 = const i32 7
    %847 = icmp eq i32 %845, %846
    %848 = const i64 0
    %849 = const i64 1
    %850 = select i64 %847, %848, %849
    switch %850 [ 0: bb69 1: bb68(%316, %317) default: bb1 ]
bb68(%318: ptr, %319: bool):
    %851 = load i64, ptr %360
    store i64 %851, ptr %361
    %852 = const i64 8
    %853 = gep i8, ptr %360, %852
    %854 = const i64 8
    %855 = gep i8, ptr %361, %854
    %856 = load i64, ptr %853
    store i64 %856, ptr %855
    %857 = const i64 16
    %858 = gep i8, ptr %360, %857
    %859 = const i64 16
    %860 = gep i8, ptr %361, %859
    %861 = load i64, ptr %858
    store i64 %861, ptr %860
    %862 = load i32, ptr %318
    store i32 %862, ptr %363
    %863 = const i64 4
    %864 = gep i8, ptr %362, %863
    %865 = load i32, ptr %363
    store i32 %865, ptr %864
    %866 = const i64 8
    %867 = gep i8, ptr %362, %866
    %868 = load i64, ptr %361
    store i64 %868, ptr %867
    %869 = const i64 8
    %870 = gep i8, ptr %361, %869
    %871 = const i64 8
    %872 = gep i8, ptr %867, %871
    %873 = load i64, ptr %870
    store i64 %873, ptr %872
    %874 = const i64 16
    %875 = gep i8, ptr %361, %874
    %876 = const i64 16
    %877 = gep i8, ptr %867, %876
    %878 = load i64, ptr %875
    store i64 %878, ptr %877
    %879 = const i32 0
    store i32 %879, ptr %362
    %880 = load i64, ptr %362
    store i64 %880, ptr %0
    %881 = const i64 8
    %882 = gep i8, ptr %362, %881
    %883 = const i64 8
    %884 = gep i8, ptr %0, %883
    %885 = load i64, ptr %882
    store i64 %885, ptr %884
    %886 = const i64 16
    %887 = gep i8, ptr %362, %886
    %888 = const i64 16
    %889 = gep i8, ptr %0, %888
    %890 = load i64, ptr %887
    store i64 %890, ptr %889
    %891 = const i64 24
    %892 = gep i8, ptr %362, %891
    %893 = const i64 24
    %894 = gep i8, ptr %0, %893
    %895 = load i64, ptr %892
    store i64 %895, ptr %894
    br bb74(%319)
bb69:
    %896 = const i32 6
    store i32 %896, ptr %0
    br bb70
bb70:
    %897 = const bool false
    br bb72
bb71:
    %898 = const bool false
    br bb72
bb72:
    ret
bb73:
    br bb71
bb74(%320: bool):
    condbr %320, bb73, bb71
bb75:
    unreachable
}

fn @_Name_as_std__cmp__PartialEq___eq(functy.4) {
bb0(%0: ptr, %1: ptr):
    %2 = load u32, ptr %0
    %3 = load u32, ptr %1
    %4 = icmp eq u32 %2, %3
    ret %4
}

fn @Expr__has_expr_mvar_quick(functy.5) {
bb0(%0: ptr):
    %2 = alloca i64, align 8
    %3 = const i64 32
    %4 = gep i8, ptr %0, %3
    %5 = load i64, ptr %4
    store i64 %5, ptr %2
    %6 = load u64, ptr %2
    %7 = call @func.19(%6)
    br bb1(%7)
bb1(%1: bool):
    ret %1
}

fn @Expr__has_level_mvar_quick(functy.6) {
bb0(%0: ptr):
    %2 = alloca i64, align 8
    %3 = const i64 32
    %4 = gep i8, ptr %0, %3
    %5 = load i64, ptr %4
    store i64 %5, ptr %2
    %6 = load u64, ptr %2
    %7 = call @func.20(%6)
    br bb1(%7)
bb1(%1: bool):
    ret %1
}

fn @Expr__has_fvar_quick(functy.7) {
bb0(%0: ptr):
    %2 = alloca i64, align 8
    %3 = const i64 32
    %4 = gep i8, ptr %0, %3
    %5 = load i64, ptr %4
    store i64 %5, ptr %2
    %6 = load u64, ptr %2
    %7 = call @func.21(%6)
    br bb1(%7)
bb1(%1: bool):
    ret %1
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecRNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprE3popBH_(functy.8) {
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE3lenBG_(functy.9) {
}

fn @_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_(functy.10) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecRNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprE4pushBI_(functy.11) {
}

fn @find_undef_level_param(functy.12) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %53 = alloca (i64, i64, i64), align 8
    %54 = alloca i64, align 8
    %55 = alloca i64, align 8
    %56 = alloca i64, align 8
    %57 = alloca (i32, i32), align 4
    %58 = alloca i32, align 4
    %59 = alloca (i32, i32), align 4
    %60 = alloca i32, align 4
    %61 = alloca (i64, i64), align 8
    %62 = const i64 8
    %63 = heap_alloc rust_heap i8, %62, align 8
    store ptr %63, ptr %54
    br bb1(%1)
bb1(%3: ptr):
    %64 = load ptr, ptr %54
    %65 = ptrtoint ptr %64 to u64
    %66 = const u64 8
    %67 = const u64 1
    %68 = sub u64 %66, %67
    %69 = and u64 %65, %68
    %70 = const u64 0
    %71 = icmp eq u64 %69, %70
    condbr %71, bb42(%3, %64), bb48
bb2:
    call @func.8(%55, %53)
    br bb3
bb3:
    %72 = load i64, ptr %55
    %73 = const i64 0
    %74 = icmp eq i64 %72, %73
    %75 = const i64 0
    %76 = const i64 1
    %77 = select i64 %74, %75, %76
    switch %77 [ 1: bb4 0: bb39 default: bb6 ]
bb4:
    %78 = load ptr, ptr %55
    %79 = call @func.22(%78)
    store ptr %79, ptr %56
    br bb5
bb5:
    %80 = load ptr, ptr %56
    %81 = load i8, ptr %80
    %82 = sext i8 %81 to i64
    switch %82 [ 0: bb2 1: bb2 2: bb14 3: bb13 4: bb12 5: bb11 6: bb10 7: bb9 8: bb2 9: bb8 10: bb7 default: bb6 ]
bb6:
    unreachable
bb7:
    %83 = load ptr, ptr %56
    %84 = const i64 8
    %85 = gep i8, ptr %83, %84
    br bb37(%85)
bb8:
    %86 = load ptr, ptr %56
    %87 = const i64 16
    %88 = gep i8, ptr %86, %87
    br bb37(%88)
bb9:
    %89 = load ptr, ptr %56
    %90 = const i64 8
    %91 = gep i8, ptr %89, %90
    %92 = load ptr, ptr %56
    %93 = const i64 16
    %94 = gep i8, ptr %92, %93
    %95 = load ptr, ptr %56
    %96 = const i64 24
    %97 = gep i8, ptr %95, %96
    %98 = load ptr, ptr %97
    %99 = const i64 16
    %100 = gep i8, ptr %98, %99
    br bb32(%91, %94, %53, %100)
bb10:
    %101 = load ptr, ptr %56
    %102 = const i64 8
    %103 = gep i8, ptr %101, %102
    %104 = load ptr, ptr %56
    %105 = const i64 16
    %106 = gep i8, ptr %104, %105
    br bb28(%103, %106)
bb11:
    %107 = load ptr, ptr %56
    %108 = const i64 8
    %109 = gep i8, ptr %107, %108
    %110 = load ptr, ptr %56
    %111 = const i64 16
    %112 = gep i8, ptr %110, %111
    br bb28(%109, %112)
bb12:
    %113 = load ptr, ptr %56
    %114 = const i64 8
    %115 = gep i8, ptr %113, %114
    %116 = load ptr, ptr %56
    %117 = const i64 16
    %118 = gep i8, ptr %116, %117
    %119 = load ptr, ptr %118
    %120 = const i64 16
    %121 = gep i8, ptr %119, %120
    br bb25(%115, %53, %121)
bb13:
    %122 = load ptr, ptr %56
    %123 = const i64 8
    %124 = gep i8, ptr %122, %123
    %125 = const u64 0
    br bb17(%124, %125)
bb14:
    %126 = load ptr, ptr %56
    %127 = const i64 8
    %128 = gep i8, ptr %126, %127
    call @func.25(%57, %128, %2)
    br bb15
bb15:
    %129 = load i32, ptr %57
    %130 = sext i32 %129 to i64
    switch %130 [ 1: bb16 0: bb2 default: bb6 ]
bb16:
    %131 = const i64 4
    %132 = gep i8, ptr %57, %131
    %133 = load i32, ptr %132
    store i32 %133, ptr %58
    %134 = const i64 4
    %135 = gep i8, ptr %0, %134
    %136 = load i32, ptr %58
    store i32 %136, ptr %135
    %137 = const i32 1
    store i32 %137, ptr %0
    br bb40
bb17(%4: ptr, %5: u64):
    %138 = call @func.9(%4)
    br bb18(%4, %5, %5, %138)
bb18(%6: ptr, %7: u64, %8: u64, %9: u64):
    %139 = icmp ult u64 %8, %9
    condbr %139, bb19(%6, %7), bb2
bb19(%10: ptr, %11: u64):
    %140 = call @func.10(%10, %11)
    br bb20(%10, %11, %140)
bb20(%12: ptr, %13: u64, %14: ptr):
    call @func.25(%59, %14, %2)
    br bb21(%12, %13)
bb21(%15: ptr, %16: u64):
    %141 = load i32, ptr %59
    %142 = sext i32 %141 to i64
    switch %142 [ 1: bb22 0: bb23(%15, %16) default: bb6 ]
bb22:
    %143 = const i64 4
    %144 = gep i8, ptr %59, %143
    %145 = load i32, ptr %144
    store i32 %145, ptr %60
    %146 = const i64 4
    %147 = gep i8, ptr %0, %146
    %148 = load i32, ptr %60
    store i32 %148, ptr %147
    %149 = const i32 1
    store i32 %149, ptr %0
    br bb40
bb23(%17: ptr, %18: u64):
    %150 = const u64 1
    %151, %152 = add.overflow u64 %18, %150
    store u64 %151, ptr %61
    %153 = const i64 8
    %154 = gep i8, ptr %61, %153
    store bool %152, ptr %154
    %155 = const i64 8
    %156 = gep i8, ptr %61, %155
    %157 = load bool, ptr %156
    %158 = const bool false
    %159 = icmp eq bool %157, %158
    condbr %159, bb24(%17), bb48
bb24(%19: ptr):
    %160 = load u64, ptr %61
    br bb17(%19, %160)
bb25(%20: ptr, %21: ptr, %22: ptr):
    call @func.11(%21, %22)
    br bb26(%20)
bb26(%23: ptr):
    %161 = load ptr, ptr %23
    %162 = const i64 16
    %163 = gep i8, ptr %161, %162
    br bb27(%53, %163)
bb27(%24: ptr, %25: ptr):
    call @func.11(%24, %25)
    br bb44
bb28(%26: ptr, %27: ptr):
    %164 = load ptr, ptr %27
    %165 = const i64 16
    %166 = gep i8, ptr %164, %165
    br bb29(%26, %53, %166)
bb29(%28: ptr, %29: ptr, %30: ptr):
    call @func.11(%29, %30)
    br bb30(%28)
bb30(%31: ptr):
    %167 = load ptr, ptr %31
    %168 = const i64 16
    %169 = gep i8, ptr %167, %168
    br bb31(%53, %169)
bb31(%32: ptr, %33: ptr):
    call @func.11(%32, %33)
    br bb45
bb32(%34: ptr, %35: ptr, %36: ptr, %37: ptr):
    call @func.11(%36, %37)
    br bb33(%34, %35)
bb33(%38: ptr, %39: ptr):
    %170 = load ptr, ptr %39
    %171 = const i64 16
    %172 = gep i8, ptr %170, %171
    br bb34(%38, %53, %172)
bb34(%40: ptr, %41: ptr, %42: ptr):
    call @func.11(%41, %42)
    br bb35(%40)
bb35(%43: ptr):
    %173 = load ptr, ptr %43
    %174 = const i64 16
    %175 = gep i8, ptr %173, %174
    br bb36(%53, %175)
bb36(%44: ptr, %45: ptr):
    call @func.11(%44, %45)
    br bb46
bb37(%46: ptr):
    %176 = load ptr, ptr %46
    %177 = const i64 16
    %178 = gep i8, ptr %176, %177
    br bb38(%53, %178)
bb38(%47: ptr, %48: ptr):
    call @func.11(%47, %48)
    br bb47
bb39:
    %179 = const i32 0
    store i32 %179, ptr %0
    br bb41
bb40:
    br bb41
bb41:
    ret
bb42(%49: ptr, %50: ptr):
    %180 = ptrtoint ptr %50 to u64
    %181 = const u64 8
    %182 = const u64 0
    %183 = icmp ne u64 %181, %182
    %184 = const u64 0
    %185 = icmp eq u64 %180, %184
    %186 = const bool false
    %187 = select bool %185, %183, %186
    %188 = const bool false
    %189 = icmp eq bool %187, %188
    condbr %189, bb43(%49, %50), bb48
bb43(%51: ptr, %52: ptr):
    store ptr %51, ptr %52
    %190 = load ptr, ptr %54
    %191 = const i64 8
    %192 = gep i8, ptr %53, %191
    store ptr %190, ptr %192
    %193 = const i64 1
    store i64 %193, ptr %53
    %194 = const i64 1
    %195 = const i64 16
    %196 = gep i8, ptr %53, %195
    store i64 %194, ptr %196
    br bb2
bb44:
    br bb2
bb45:
    br bb2
bb46:
    br bb2
bb47:
    br bb2
bb48:
    unreachable
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprE3newBE_(functy.13) {
}

fn @Verifier____env___infer_sort(functy.14) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %5 = alloca (i64, i64, i64), align 8
    call @func.13(%5)
    br bb1(%1, %2)
bb1(%3: ptr, %4: ptr):
    %6 = const u32 0
    call @func.32(%0, %3, %4, %6, %5)
    br bb2
bb2:
    br bb3
bb3:
    ret
}

fn @Level__is_zero(functy.15) {
bb0(%0: ptr):
    %9 = alloca i64, align 8
    store ptr %0, ptr %9
    %10 = load ptr, ptr %9
    %11 = load i32, ptr %10
    %12 = sext i32 %11 to i64
    switch %12 [ 0: bb5 1: bb4 2: bb3 3: bb2 4: bb4 default: bb1 ]
bb1:
    unreachable
bb2:
    %13 = load ptr, ptr %9
    %14 = const i64 16
    %15 = gep i8, ptr %13, %14
    %16 = load ptr, ptr %15
    %17 = const i64 16
    %18 = gep i8, ptr %16, %17
    br bb11(%18)
bb3:
    %19 = load ptr, ptr %9
    %20 = const i64 8
    %21 = gep i8, ptr %19, %20
    %22 = load ptr, ptr %9
    %23 = const i64 16
    %24 = gep i8, ptr %22, %23
    %25 = load ptr, ptr %21
    %26 = const i64 16
    %27 = gep i8, ptr %25, %26
    br bb6(%24, %27)
bb4:
    %28 = const bool false
    br bb12(%28)
bb5:
    %29 = const bool true
    br bb12(%29)
bb6(%1: ptr, %2: ptr):
    %30 = call @func.15(%2)
    br bb7(%1, %30)
bb7(%3: ptr, %4: bool):
    condbr %4, bb8(%3), bb9
bb8(%5: ptr):
    %31 = load ptr, ptr %5
    %32 = const i64 16
    %33 = gep i8, ptr %31, %32
    br bb10(%33)
bb9:
    %34 = const bool false
    br bb12(%34)
bb10(%6: ptr):
    %35 = call @func.15(%6)
    br bb12(%35)
bb11(%7: ptr):
    %36 = call @func.15(%7)
    br bb12(%36)
bb12(%8: bool):
    ret %8
}

fn @_RNvXsp_NtCs2EYQwhfuABO_4core6resultINtB5_6ResultNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprNtBM_9TypeErrorENtNtNtB7_3ops9try_trait3Try6branchBM_(functy.16) {
}

fn @_RNvXsq_NtCs2EYQwhfuABO_4core6resultINtB5_6ResultuNtCshhXhIKvfvMU_25clean_decl_universe_slice9TypeErrorEINtNtNtB7_3ops9try_trait12FromResidualIBy_NtNtB7_7convert10InfallibleBL_EE13from_residualBN_(functy.17) {
}

fn @Verifier____env___check_type(functy.18) {
bb0(%0: ptr, %1: ptr, %2: ptr, %3: ptr):
    %17 = alloca (i64, i64, i64, i64, i64), align 8
    %18 = alloca (i64, i64, i64, i64, i64), align 8
    %19 = alloca (i64, i64, i64, i64, i64), align 8
    %20 = alloca (i64, i64, i64), align 8
    %21 = alloca (i64, i64, i64, i64, i64), align 8
    %22 = alloca (i64, i64, i64), align 8
    %23 = alloca i64, align 8
    %24 = alloca (i64, i64, i64, i64, i64), align 8
    %25 = alloca i64, align 8
    %26 = alloca (i64, i64, i64, i64, i64), align 8
    %27 = const bool false
    call @func.34(%19, %1, %2)
    br bb1(%1, %3)
bb1(%4: ptr, %5: ptr):
    call @func.16(%18, %19)
    br bb2(%4, %5)
bb2(%6: ptr, %7: ptr):
    %28 = load i8, ptr %18
    %29 = const i8 11
    %30 = icmp eq i8 %28, %29
    %31 = const i64 1
    %32 = const i64 0
    %33 = select i64 %30, %31, %32
    switch %33 [ 0: bb4(%6, %7) 1: bb5 default: bb3 ]
bb3:
    unreachable
bb4(%8: ptr, %9: ptr):
    %34 = load i64, ptr %18
    store i64 %34, ptr %21
    %35 = const i64 8
    %36 = gep i8, ptr %18, %35
    %37 = const i64 8
    %38 = gep i8, ptr %21, %37
    %39 = load i64, ptr %36
    store i64 %39, ptr %38
    %40 = const i64 16
    %41 = gep i8, ptr %18, %40
    %42 = const i64 16
    %43 = gep i8, ptr %21, %42
    %44 = load i64, ptr %41
    store i64 %44, ptr %43
    %45 = const i64 24
    %46 = gep i8, ptr %18, %45
    %47 = const i64 24
    %48 = gep i8, ptr %21, %47
    %49 = load i64, ptr %46
    store i64 %49, ptr %48
    %50 = const i64 32
    %51 = gep i8, ptr %18, %50
    %52 = const i64 32
    %53 = gep i8, ptr %21, %52
    %54 = load i64, ptr %51
    store i64 %54, ptr %53
    %55 = const bool true
    %56 = load i64, ptr %21
    store i64 %56, ptr %17
    %57 = const i64 8
    %58 = gep i8, ptr %21, %57
    %59 = const i64 8
    %60 = gep i8, ptr %17, %59
    %61 = load i64, ptr %58
    store i64 %61, ptr %60
    %62 = const i64 16
    %63 = gep i8, ptr %21, %62
    %64 = const i64 16
    %65 = gep i8, ptr %17, %64
    %66 = load i64, ptr %63
    store i64 %66, ptr %65
    %67 = const i64 24
    %68 = gep i8, ptr %21, %67
    %69 = const i64 24
    %70 = gep i8, ptr %17, %69
    %71 = load i64, ptr %68
    store i64 %71, ptr %70
    %72 = const i64 32
    %73 = gep i8, ptr %21, %72
    %74 = const i64 32
    %75 = gep i8, ptr %17, %74
    %76 = load i64, ptr %73
    store i64 %76, ptr %75
    %77 = call @func.35(%8, %17, %9)
    br bb7(%9, %77, %55)
bb5:
    %78 = const i64 8
    %79 = gep i8, ptr %18, %78
    %80 = load i64, ptr %79
    store i64 %80, ptr %20
    %81 = const i64 8
    %82 = gep i8, ptr %79, %81
    %83 = const i64 8
    %84 = gep i8, ptr %20, %83
    %85 = load i64, ptr %82
    store i64 %85, ptr %84
    %86 = const i64 16
    %87 = gep i8, ptr %79, %86
    %88 = const i64 16
    %89 = gep i8, ptr %20, %88
    %90 = load i64, ptr %87
    store i64 %90, ptr %89
    call @func.17(%0, %20)
    br bb6
bb6:
    %91 = const bool false
    br bb15
bb7(%10: ptr, %11: bool, %12: bool):
    condbr %11, bb8(%12), bb9(%10)
bb8(%13: bool):
    %92 = const i32 7
    store i32 %92, ptr %0
    br bb13(%13)
bb9(%14: ptr):
    call @func.36(%24, %14)
    br bb10
bb10:
    %93 = const i64 56
    %94 = heap_alloc rust_heap i8, %93, align 8
    %95 = const u64 1
    store u64 %95, ptr %94
    %96 = const i64 8
    %97 = gep i8, ptr %94, %96
    %98 = const u64 1
    store u64 %98, ptr %97
    %99 = const i64 16
    %100 = gep i8, ptr %94, %99
    %101 = load i64, ptr %24
    store i64 %101, ptr %100
    %102 = const i64 8
    %103 = gep i8, ptr %24, %102
    %104 = const i64 8
    %105 = gep i8, ptr %100, %104
    %106 = load i64, ptr %103
    store i64 %106, ptr %105
    %107 = const i64 16
    %108 = gep i8, ptr %24, %107
    %109 = const i64 16
    %110 = gep i8, ptr %100, %109
    %111 = load i64, ptr %108
    store i64 %111, ptr %110
    %112 = const i64 24
    %113 = gep i8, ptr %24, %112
    %114 = const i64 24
    %115 = gep i8, ptr %100, %114
    %116 = load i64, ptr %113
    store i64 %116, ptr %115
    %117 = const i64 32
    %118 = gep i8, ptr %24, %117
    %119 = const i64 32
    %120 = gep i8, ptr %100, %119
    %121 = load i64, ptr %118
    store i64 %121, ptr %120
    store ptr %94, ptr %23
    br bb11
bb11:
    %122 = const bool false
    %123 = load i64, ptr %17
    store i64 %123, ptr %26
    %124 = const i64 8
    %125 = gep i8, ptr %17, %124
    %126 = const i64 8
    %127 = gep i8, ptr %26, %126
    %128 = load i64, ptr %125
    store i64 %128, ptr %127
    %129 = const i64 16
    %130 = gep i8, ptr %17, %129
    %131 = const i64 16
    %132 = gep i8, ptr %26, %131
    %133 = load i64, ptr %130
    store i64 %133, ptr %132
    %134 = const i64 24
    %135 = gep i8, ptr %17, %134
    %136 = const i64 24
    %137 = gep i8, ptr %26, %136
    %138 = load i64, ptr %135
    store i64 %138, ptr %137
    %139 = const i64 32
    %140 = gep i8, ptr %17, %139
    %141 = const i64 32
    %142 = gep i8, ptr %26, %141
    %143 = load i64, ptr %140
    store i64 %143, ptr %142
    %144 = const i64 56
    %145 = heap_alloc rust_heap i8, %144, align 8
    %146 = const u64 1
    store u64 %146, ptr %145
    %147 = const i64 8
    %148 = gep i8, ptr %145, %147
    %149 = const u64 1
    store u64 %149, ptr %148
    %150 = const i64 16
    %151 = gep i8, ptr %145, %150
    %152 = load i64, ptr %26
    store i64 %152, ptr %151
    %153 = const i64 8
    %154 = gep i8, ptr %26, %153
    %155 = const i64 8
    %156 = gep i8, ptr %151, %155
    %157 = load i64, ptr %154
    store i64 %157, ptr %156
    %158 = const i64 16
    %159 = gep i8, ptr %26, %158
    %160 = const i64 16
    %161 = gep i8, ptr %151, %160
    %162 = load i64, ptr %159
    store i64 %162, ptr %161
    %163 = const i64 24
    %164 = gep i8, ptr %26, %163
    %165 = const i64 24
    %166 = gep i8, ptr %151, %165
    %167 = load i64, ptr %164
    store i64 %167, ptr %166
    %168 = const i64 32
    %169 = gep i8, ptr %26, %168
    %170 = const i64 32
    %171 = gep i8, ptr %151, %170
    %172 = load i64, ptr %169
    store i64 %172, ptr %171
    store ptr %145, ptr %25
    br bb12(%122)
bb12(%15: bool):
    %173 = load ptr, ptr %23
    %174 = const i64 8
    %175 = gep i8, ptr %22, %174
    store ptr %173, ptr %175
    %176 = load ptr, ptr %25
    %177 = const i64 16
    %178 = gep i8, ptr %22, %177
    store ptr %176, ptr %178
    %179 = const i32 2
    store i32 %179, ptr %22
    %180 = load i64, ptr %22
    store i64 %180, ptr %0
    %181 = const i64 8
    %182 = gep i8, ptr %22, %181
    %183 = const i64 8
    %184 = gep i8, ptr %0, %183
    %185 = load i64, ptr %182
    store i64 %185, ptr %184
    %186 = const i64 16
    %187 = gep i8, ptr %22, %186
    %188 = const i64 16
    %189 = gep i8, ptr %0, %188
    %190 = load i64, ptr %187
    store i64 %190, ptr %189
    br bb13(%15)
bb13(%16: bool):
    condbr %16, bb16, bb14
bb14:
    %191 = const bool false
    br bb15
bb15:
    ret
bb16:
    br bb14
}

fn @ExprMeta__has_expr_mvar(functy.19) {
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

fn @ExprMeta__has_level_mvar(functy.20) {
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

fn @ExprMeta__has_fvar(functy.21) {
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

fn @Expr__kind(functy.22) {
bb0(%0: ptr):
    %1 = alloca i64, align 8
    store ptr %0, ptr %1
    %2 = load ptr, ptr %1
    ret %2
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecRNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE3popBH_(functy.23) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecRNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE4pushBI_(functy.24) {
}

fn @find_undef_level_param_in_level(functy.25) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %41 = alloca (i64, i64, i64), align 8
    %42 = alloca i64, align 8
    %43 = alloca i64, align 8
    %44 = alloca i64, align 8
    %45 = alloca (i64, i64), align 8
    %46 = alloca i32, align 4
    %47 = const i64 8
    %48 = heap_alloc rust_heap i8, %47, align 8
    store ptr %48, ptr %42
    br bb1(%1)
bb1(%3: ptr):
    %49 = load ptr, ptr %42
    %50 = ptrtoint ptr %49 to u64
    %51 = const u64 8
    %52 = const u64 1
    %53 = sub u64 %51, %52
    %54 = and u64 %50, %53
    %55 = const u64 0
    %56 = icmp eq u64 %54, %55
    condbr %56, bb26(%3, %49), bb30
bb2:
    call @func.23(%43, %41)
    br bb3
bb3:
    %57 = load i64, ptr %43
    %58 = const i64 0
    %59 = icmp eq i64 %57, %58
    %60 = const i64 0
    %61 = const i64 1
    %62 = select i64 %59, %60, %61
    switch %62 [ 1: bb4 0: bb24 default: bb5 ]
bb4:
    %63 = load ptr, ptr %43
    store ptr %63, ptr %44
    %64 = load ptr, ptr %44
    %65 = load i32, ptr %64
    %66 = sext i32 %65 to i64
    switch %66 [ 0: bb2 1: bb8 2: bb7 3: bb6 4: bb9 default: bb5 ]
bb5:
    unreachable
bb6:
    %67 = load ptr, ptr %44
    %68 = const i64 8
    %69 = gep i8, ptr %67, %68
    %70 = load ptr, ptr %44
    %71 = const i64 16
    %72 = gep i8, ptr %70, %71
    br bb20(%69, %72)
bb7:
    %73 = load ptr, ptr %44
    %74 = const i64 8
    %75 = gep i8, ptr %73, %74
    %76 = load ptr, ptr %44
    %77 = const i64 16
    %78 = gep i8, ptr %76, %77
    br bb20(%75, %78)
bb8:
    %79 = load ptr, ptr %44
    %80 = const i64 8
    %81 = gep i8, ptr %79, %80
    %82 = load ptr, ptr %81
    %83 = const i64 16
    %84 = gep i8, ptr %82, %83
    br bb19(%41, %84)
bb9:
    %85 = load ptr, ptr %44
    %86 = const i64 4
    %87 = gep i8, ptr %85, %86
    %88 = const bool false
    %89 = const u64 0
    br bb10(%87, %88, %89)
bb10(%4: ptr, %5: bool, %6: u64):
    %90 = const i64 8
    %91 = gep i8, ptr %2, %90
    %92 = load u64, ptr %91
    %93 = icmp ult u64 %6, %92
    condbr %93, bb11(%4, %5, %6), bb17(%4, %5)
bb11(%7: ptr, %8: bool, %9: u64):
    %94 = const i64 8
    %95 = gep i8, ptr %2, %94
    %96 = load u64, ptr %95
    %97 = icmp ult u64 %9, %96
    condbr %97, bb12(%7, %8, %9, %9), bb30
bb12(%10: ptr, %11: bool, %12: u64, %13: u64):
    %98 = load ptr, ptr %2
    %99 = const u64 4
    %100 = mul u64 %13, %99
    %101 = gep i8, ptr %98, %100
    %102 = call @func.4(%101, %10)
    br bb13(%10, %11, %12, %102)
bb13(%14: ptr, %15: bool, %16: u64, %17: bool):
    condbr %17, bb14(%14), bb15(%14, %15, %16)
bb14(%18: ptr):
    %103 = const bool true
    br bb17(%18, %103)
bb15(%19: ptr, %20: bool, %21: u64):
    %104 = const u64 1
    %105, %106 = add.overflow u64 %21, %104
    store u64 %105, ptr %45
    %107 = const i64 8
    %108 = gep i8, ptr %45, %107
    store bool %106, ptr %108
    %109 = const i64 8
    %110 = gep i8, ptr %45, %109
    %111 = load bool, ptr %110
    %112 = const bool false
    %113 = icmp eq bool %111, %112
    condbr %113, bb16(%19, %20), bb30
bb16(%22: ptr, %23: bool):
    %114 = load u64, ptr %45
    br bb10(%22, %23, %114)
bb17(%24: ptr, %25: bool):
    condbr %25, bb2, bb18(%24)
bb18(%26: ptr):
    %115 = load i32, ptr %26
    store i32 %115, ptr %46
    %116 = const i64 4
    %117 = gep i8, ptr %0, %116
    %118 = load i32, ptr %46
    store i32 %118, ptr %117
    %119 = const i32 1
    store i32 %119, ptr %0
    br bb25
bb19(%27: ptr, %28: ptr):
    call @func.24(%27, %28)
    br bb28
bb20(%29: ptr, %30: ptr):
    %120 = load ptr, ptr %30
    %121 = const i64 16
    %122 = gep i8, ptr %120, %121
    br bb21(%29, %41, %122)
bb21(%31: ptr, %32: ptr, %33: ptr):
    call @func.24(%32, %33)
    br bb22(%31)
bb22(%34: ptr):
    %123 = load ptr, ptr %34
    %124 = const i64 16
    %125 = gep i8, ptr %123, %124
    br bb23(%41, %125)
bb23(%35: ptr, %36: ptr):
    call @func.24(%35, %36)
    br bb29
bb24:
    %126 = const i32 0
    store i32 %126, ptr %0
    br bb25
bb25:
    ret
bb26(%37: ptr, %38: ptr):
    %127 = ptrtoint ptr %38 to u64
    %128 = const u64 8
    %129 = const u64 0
    %130 = icmp ne u64 %128, %129
    %131 = const u64 0
    %132 = icmp eq u64 %127, %131
    %133 = const bool false
    %134 = select bool %132, %130, %133
    %135 = const bool false
    %136 = icmp eq bool %134, %135
    condbr %136, bb27(%37, %38), bb30
bb27(%39: ptr, %40: ptr):
    store ptr %39, ptr %40
    %137 = load ptr, ptr %42
    %138 = const i64 8
    %139 = gep i8, ptr %41, %138
    store ptr %137, ptr %139
    %140 = const i64 1
    store i64 %140, ptr %41
    %141 = const i64 1
    %142 = const i64 16
    %143 = gep i8, ptr %41, %142
    store i64 %141, ptr %143
    br bb2
bb28:
    br bb2
bb29:
    br bb2
bb30:
    unreachable
}

fn @_RNvXsp_NtCs2EYQwhfuABO_4core6resultINtB5_6ResultNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprNtBM_9TypeErrorENtNtNtB7_3ops9try_trait3Try6branchBM_(functy.26) {
}

fn @_RNvXsq_NtCs2EYQwhfuABO_4core6resultINtB5_6ResultNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelNtBM_9TypeErrorEINtNtNtB7_3ops9try_trait12FromResidualIBy_NtNtB7_7convert10InfallibleB1x_EE13from_residualBM_(functy.27) {
}

fn @_RNvXsp_NtCs2EYQwhfuABO_4core6resultINtB5_6ResultNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelNtBM_9TypeErrorENtNtNtB7_3ops9try_trait3Try6branchBM_(functy.28) {
}

fn @_RNvXs1j_NtCskTzINo8ZBH9_5alloc4syncINtB6_3ArcNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprEINtNtCs2EYQwhfuABO_4core7convert5AsRefBH_E6as_refBJ_(functy.29) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprE4pushBH_(functy.30) {
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprE3popBG_(functy.31) {
}

fn @Verifier____env___infer_sort_inner(functy.32) {
bb0(%0: ptr, %1: ptr, %2: ptr, %3: u32, %4: ptr):
    %98 = alloca (i64, i64, i64, i64, i64), align 8
    %99 = alloca (i64, i64, i64, i64, i64), align 8
    %100 = alloca (i64, i64, i64, i64, i64), align 8
    %101 = alloca (i64, i64, i64), align 8
    %102 = alloca (i64, i64, i64, i64, i64), align 8
    %103 = alloca (i64, i64, i64, i64, i64), align 8
    %104 = alloca i64, align 8
    %105 = alloca (i64, i64, i64), align 8
    %106 = alloca (i64, i64, i64), align 8
    %107 = alloca (i64, i64, i64), align 8
    %108 = alloca (i64, i64, i64, i64), align 8
    %109 = alloca (i64, i64, i64, i64), align 8
    %110 = alloca (i32, i32), align 4
    %111 = alloca (i64, i64, i64), align 8
    %112 = alloca (i64, i64, i64), align 8
    %113 = alloca (i64, i64, i64, i64, i64), align 8
    %114 = alloca (i64, i64, i64, i64), align 8
    %115 = alloca (i32, i32), align 4
    %116 = alloca (i64, i64, i64, i64, i64), align 8
    %117 = alloca (i64, i64, i64), align 8
    %118 = alloca (i64, i64, i64, i64), align 8
    %119 = alloca (i64, i64, i64, i64), align 8
    %120 = alloca (i64, i64, i64), align 8
    %121 = alloca (i64, i64, i64), align 8
    %122 = alloca (i64, i64, i64), align 8
    %123 = alloca (i64, i64, i64), align 8
    %124 = alloca (i64, i64, i64), align 8
    %125 = alloca (i64, i64, i64), align 8
    %126 = alloca i64, align 8
    %127 = alloca (i64, i64, i64, i64, i64), align 8
    %128 = const bool false
    %129 = const bool false
    %130 = const bool false
    %131 = const bool false
    call @func.45(%100, %1, %2, %4)
    br bb1(%1, %3, %4)
bb1(%5: ptr, %6: u32, %7: ptr):
    call @func.26(%99, %100)
    br bb2(%5, %6, %7)
bb2(%8: ptr, %9: u32, %10: ptr):
    %132 = load i8, ptr %99
    %133 = const i8 11
    %134 = icmp eq i8 %132, %133
    %135 = const i64 1
    %136 = const i64 0
    %137 = select i64 %134, %135, %136
    switch %137 [ 0: bb4(%8, %9, %10) 1: bb5 default: bb3 ]
bb3:
    unreachable
bb4(%11: ptr, %12: u32, %13: ptr):
    %138 = load i64, ptr %99
    store i64 %138, ptr %102
    %139 = const i64 8
    %140 = gep i8, ptr %99, %139
    %141 = const i64 8
    %142 = gep i8, ptr %102, %141
    %143 = load i64, ptr %140
    store i64 %143, ptr %142
    %144 = const i64 16
    %145 = gep i8, ptr %99, %144
    %146 = const i64 16
    %147 = gep i8, ptr %102, %146
    %148 = load i64, ptr %145
    store i64 %148, ptr %147
    %149 = const i64 24
    %150 = gep i8, ptr %99, %149
    %151 = const i64 24
    %152 = gep i8, ptr %102, %151
    %153 = load i64, ptr %150
    store i64 %153, ptr %152
    %154 = const i64 32
    %155 = gep i8, ptr %99, %154
    %156 = const i64 32
    %157 = gep i8, ptr %102, %156
    %158 = load i64, ptr %155
    store i64 %158, ptr %157
    %159 = const bool true
    %160 = load i64, ptr %102
    store i64 %160, ptr %98
    %161 = const i64 8
    %162 = gep i8, ptr %102, %161
    %163 = const i64 8
    %164 = gep i8, ptr %98, %163
    %165 = load i64, ptr %162
    store i64 %165, ptr %164
    %166 = const i64 16
    %167 = gep i8, ptr %102, %166
    %168 = const i64 16
    %169 = gep i8, ptr %98, %168
    %170 = load i64, ptr %167
    store i64 %170, ptr %169
    %171 = const i64 24
    %172 = gep i8, ptr %102, %171
    %173 = const i64 24
    %174 = gep i8, ptr %98, %173
    %175 = load i64, ptr %172
    store i64 %175, ptr %174
    %176 = const i64 32
    %177 = gep i8, ptr %102, %176
    %178 = const i64 32
    %179 = gep i8, ptr %98, %178
    %180 = load i64, ptr %177
    store i64 %180, ptr %179
    call @func.46(%103, %11, %98)
    br bb7(%11, %12, %13, %159)
bb5:
    %181 = const i64 8
    %182 = gep i8, ptr %99, %181
    %183 = load i64, ptr %182
    store i64 %183, ptr %101
    %184 = const i64 8
    %185 = gep i8, ptr %182, %184
    %186 = const i64 8
    %187 = gep i8, ptr %101, %186
    %188 = load i64, ptr %185
    store i64 %188, ptr %187
    %189 = const i64 16
    %190 = gep i8, ptr %182, %189
    %191 = const i64 16
    %192 = gep i8, ptr %101, %191
    %193 = load i64, ptr %190
    store i64 %193, ptr %192
    call @func.27(%0, %101)
    br bb6
bb6:
    %194 = const bool false
    br bb41
bb7(%14: ptr, %15: u32, %16: ptr, %17: bool):
    store ptr %103, ptr %104
    %195 = load ptr, ptr %104
    %196 = load i8, ptr %195
    %197 = sext i8 %196 to i64
    switch %197 [ 2: bb10(%17) 6: bb9(%14, %15, %16, %17) default: bb8 ]
bb8:
    %198 = const bool false
    %199 = load i64, ptr %98
    store i64 %199, ptr %127
    %200 = const i64 8
    %201 = gep i8, ptr %98, %200
    %202 = const i64 8
    %203 = gep i8, ptr %127, %202
    %204 = load i64, ptr %201
    store i64 %204, ptr %203
    %205 = const i64 16
    %206 = gep i8, ptr %98, %205
    %207 = const i64 16
    %208 = gep i8, ptr %127, %207
    %209 = load i64, ptr %206
    store i64 %209, ptr %208
    %210 = const i64 24
    %211 = gep i8, ptr %98, %210
    %212 = const i64 24
    %213 = gep i8, ptr %127, %212
    %214 = load i64, ptr %211
    store i64 %214, ptr %213
    %215 = const i64 32
    %216 = gep i8, ptr %98, %215
    %217 = const i64 32
    %218 = gep i8, ptr %127, %217
    %219 = load i64, ptr %216
    store i64 %219, ptr %218
    %220 = const i64 56
    %221 = heap_alloc rust_heap i8, %220, align 8
    %222 = const u64 1
    store u64 %222, ptr %221
    %223 = const i64 8
    %224 = gep i8, ptr %221, %223
    %225 = const u64 1
    store u64 %225, ptr %224
    %226 = const i64 16
    %227 = gep i8, ptr %221, %226
    %228 = load i64, ptr %127
    store i64 %228, ptr %227
    %229 = const i64 8
    %230 = gep i8, ptr %127, %229
    %231 = const i64 8
    %232 = gep i8, ptr %227, %231
    %233 = load i64, ptr %230
    store i64 %233, ptr %232
    %234 = const i64 16
    %235 = gep i8, ptr %127, %234
    %236 = const i64 16
    %237 = gep i8, ptr %227, %236
    %238 = load i64, ptr %235
    store i64 %238, ptr %237
    %239 = const i64 24
    %240 = gep i8, ptr %127, %239
    %241 = const i64 24
    %242 = gep i8, ptr %227, %241
    %243 = load i64, ptr %240
    store i64 %243, ptr %242
    %244 = const i64 32
    %245 = gep i8, ptr %127, %244
    %246 = const i64 32
    %247 = gep i8, ptr %227, %246
    %248 = load i64, ptr %245
    store i64 %248, ptr %247
    store ptr %221, ptr %126
    br bb33(%198)
bb9(%18: ptr, %19: u32, %20: ptr, %21: bool):
    %249 = load ptr, ptr %104
    %250 = const i64 1
    %251 = gep i8, ptr %249, %250
    %252 = load ptr, ptr %104
    %253 = const i64 8
    %254 = gep i8, ptr %252, %253
    %255 = load ptr, ptr %104
    %256 = const i64 16
    %257 = gep i8, ptr %255, %256
    %258 = const u32 64
    %259 = icmp uge u32 %19, %258
    condbr %259, bb12(%19), bb13(%18, %19, %20, %254, %257, %21)
bb10(%22: bool):
    %260 = load ptr, ptr %104
    %261 = const i64 8
    %262 = gep i8, ptr %260, %261
    call @func.48(%105, %262)
    br bb11(%22)
bb11(%23: bool):
    %263 = const i64 8
    %264 = gep i8, ptr %0, %263
    %265 = load i64, ptr %105
    store i64 %265, ptr %264
    %266 = const i64 8
    %267 = gep i8, ptr %105, %266
    %268 = const i64 8
    %269 = gep i8, ptr %264, %268
    %270 = load i64, ptr %267
    store i64 %270, ptr %269
    %271 = const i64 16
    %272 = gep i8, ptr %105, %271
    %273 = const i64 16
    %274 = gep i8, ptr %264, %273
    %275 = load i64, ptr %272
    store i64 %275, ptr %274
    %276 = const i64 0
    store i64 %276, ptr %0
    br bb34(%23)
bb12(%24: u32):
    %277 = const i64 4
    %278 = gep i8, ptr %106, %277
    store u32 %24, ptr %278
    %279 = const i32 5
    store i32 %279, ptr %106
    %280 = const i64 8
    %281 = gep i8, ptr %0, %280
    %282 = load i64, ptr %106
    store i64 %282, ptr %281
    %283 = const i64 8
    %284 = gep i8, ptr %106, %283
    %285 = const i64 8
    %286 = gep i8, ptr %281, %285
    %287 = load i64, ptr %284
    store i64 %287, ptr %286
    %288 = const i64 16
    %289 = gep i8, ptr %106, %288
    %290 = const i64 16
    %291 = gep i8, ptr %281, %290
    %292 = load i64, ptr %289
    store i64 %292, ptr %291
    %293 = const i64 1
    store i64 %293, ptr %0
    br bb38
bb13(%25: ptr, %26: u32, %27: ptr, %28: ptr, %29: ptr, %30: bool):
    %294 = load ptr, ptr %28
    %295 = const i64 16
    %296 = gep i8, ptr %294, %295
    br bb14(%25, %26, %27, %28, %29, %296, %30)
bb14(%31: ptr, %32: u32, %33: ptr, %34: ptr, %35: ptr, %36: ptr, %37: bool):
    %297 = const u32 1
    %298, %299 = add.overflow u32 %32, %297
    store u32 %298, ptr %110
    %300 = const i64 4
    %301 = gep i8, ptr %110, %300
    store bool %299, ptr %301
    %302 = const i64 4
    %303 = gep i8, ptr %110, %302
    %304 = load bool, ptr %303
    %305 = const bool false
    %306 = icmp eq bool %304, %305
    condbr %306, bb15(%31, %32, %33, %34, %35, %36, %37), bb44
bb15(%38: ptr, %39: u32, %40: ptr, %41: ptr, %42: ptr, %43: ptr, %44: bool):
    %307 = load u32, ptr %110
    call @func.32(%109, %38, %43, %307, %40)
    br bb16(%38, %39, %40, %41, %42, %44)
bb16(%45: ptr, %46: u32, %47: ptr, %48: ptr, %49: ptr, %50: bool):
    call @func.28(%108, %109)
    br bb17(%45, %46, %47, %48, %49, %50)
bb17(%51: ptr, %52: u32, %53: ptr, %54: ptr, %55: ptr, %56: bool):
    %308 = load i64, ptr %108
    switch %308 [ 0: bb18(%51, %52, %53, %54, %55, %56) 1: bb19 default: bb3 ]
bb18(%57: ptr, %58: u32, %59: ptr, %60: ptr, %61: ptr, %62: bool):
    %309 = const i64 8
    %310 = gep i8, ptr %108, %309
    %311 = load i64, ptr %310
    store i64 %311, ptr %112
    %312 = const i64 8
    %313 = gep i8, ptr %310, %312
    %314 = const i64 8
    %315 = gep i8, ptr %112, %314
    %316 = load i64, ptr %313
    store i64 %316, ptr %315
    %317 = const i64 16
    %318 = gep i8, ptr %310, %317
    %319 = const i64 16
    %320 = gep i8, ptr %112, %319
    %321 = load i64, ptr %318
    store i64 %321, ptr %320
    %322 = const bool true
    %323 = load i64, ptr %112
    store i64 %323, ptr %107
    %324 = const i64 8
    %325 = gep i8, ptr %112, %324
    %326 = const i64 8
    %327 = gep i8, ptr %107, %326
    %328 = load i64, ptr %325
    store i64 %328, ptr %327
    %329 = const i64 16
    %330 = gep i8, ptr %112, %329
    %331 = const i64 16
    %332 = gep i8, ptr %107, %331
    %333 = load i64, ptr %330
    store i64 %333, ptr %332
    %334 = call @func.29(%60)
    br bb20(%57, %58, %59, %61, %334, %62)
bb19:
    %335 = const i64 8
    %336 = gep i8, ptr %108, %335
    %337 = load i64, ptr %336
    store i64 %337, ptr %111
    %338 = const i64 8
    %339 = gep i8, ptr %336, %338
    %340 = const i64 8
    %341 = gep i8, ptr %111, %340
    %342 = load i64, ptr %339
    store i64 %342, ptr %341
    %343 = const i64 16
    %344 = gep i8, ptr %336, %343
    %345 = const i64 16
    %346 = gep i8, ptr %111, %345
    %347 = load i64, ptr %344
    store i64 %347, ptr %346
    call @func.27(%0, %111)
    br bb43
bb20(%63: ptr, %64: u32, %65: ptr, %66: ptr, %67: ptr, %68: bool):
    call @func.36(%113, %67)
    br bb21(%63, %64, %65, %66, %68)
bb21(%69: ptr, %70: u32, %71: ptr, %72: ptr, %73: bool):
    call @func.30(%71, %113)
    br bb22(%69, %70, %71, %72, %73)
bb22(%74: ptr, %75: u32, %76: ptr, %77: ptr, %78: bool):
    %348 = load ptr, ptr %77
    %349 = const i64 16
    %350 = gep i8, ptr %348, %349
    br bb23(%74, %75, %76, %350, %78)
bb23(%79: ptr, %80: u32, %81: ptr, %82: ptr, %83: bool):
    %351 = const u32 1
    %352, %353 = add.overflow u32 %80, %351
    store u32 %352, ptr %115
    %354 = const i64 4
    %355 = gep i8, ptr %115, %354
    store bool %353, ptr %355
    %356 = const i64 4
    %357 = gep i8, ptr %115, %356
    %358 = load bool, ptr %357
    %359 = const bool false
    %360 = icmp eq bool %358, %359
    condbr %360, bb24(%79, %81, %82, %83), bb44
bb24(%84: ptr, %85: ptr, %86: ptr, %87: bool):
    %361 = load u32, ptr %115
    call @func.32(%114, %84, %86, %361, %85)
    br bb25(%85, %87)
bb25(%88: ptr, %89: bool):
    %362 = const bool true
    call @func.31(%116, %88)
    br bb26(%89)
bb26(%90: bool):
    br bb27(%90)
bb27(%91: bool):
    %363 = const bool false
    %364 = load i64, ptr %114
    store i64 %364, ptr %119
    %365 = const i64 8
    %366 = gep i8, ptr %114, %365
    %367 = const i64 8
    %368 = gep i8, ptr %119, %367
    %369 = load i64, ptr %366
    store i64 %369, ptr %368
    %370 = const i64 16
    %371 = gep i8, ptr %114, %370
    %372 = const i64 16
    %373 = gep i8, ptr %119, %372
    %374 = load i64, ptr %371
    store i64 %374, ptr %373
    %375 = const i64 24
    %376 = gep i8, ptr %114, %375
    %377 = const i64 24
    %378 = gep i8, ptr %119, %377
    %379 = load i64, ptr %376
    store i64 %379, ptr %378
    call @func.28(%118, %119)
    br bb28(%91)
bb28(%92: bool):
    %380 = load i64, ptr %118
    switch %380 [ 0: bb29(%92) 1: bb30 default: bb3 ]
bb29(%93: bool):
    %381 = const i64 8
    %382 = gep i8, ptr %118, %381
    %383 = load i64, ptr %382
    store i64 %383, ptr %121
    %384 = const i64 8
    %385 = gep i8, ptr %382, %384
    %386 = const i64 8
    %387 = gep i8, ptr %121, %386
    %388 = load i64, ptr %385
    store i64 %388, ptr %387
    %389 = const i64 16
    %390 = gep i8, ptr %382, %389
    %391 = const i64 16
    %392 = gep i8, ptr %121, %391
    %393 = load i64, ptr %390
    store i64 %393, ptr %392
    %394 = const bool true
    %395 = load i64, ptr %121
    store i64 %395, ptr %117
    %396 = const i64 8
    %397 = gep i8, ptr %121, %396
    %398 = const i64 8
    %399 = gep i8, ptr %117, %398
    %400 = load i64, ptr %397
    store i64 %400, ptr %399
    %401 = const i64 16
    %402 = gep i8, ptr %121, %401
    %403 = const i64 16
    %404 = gep i8, ptr %117, %403
    %405 = load i64, ptr %402
    store i64 %405, ptr %404
    %406 = const bool false
    %407 = load i64, ptr %107
    store i64 %407, ptr %123
    %408 = const i64 8
    %409 = gep i8, ptr %107, %408
    %410 = const i64 8
    %411 = gep i8, ptr %123, %410
    %412 = load i64, ptr %409
    store i64 %412, ptr %411
    %413 = const i64 16
    %414 = gep i8, ptr %107, %413
    %415 = const i64 16
    %416 = gep i8, ptr %123, %415
    %417 = load i64, ptr %414
    store i64 %417, ptr %416
    %418 = const bool false
    %419 = load i64, ptr %117
    store i64 %419, ptr %124
    %420 = const i64 8
    %421 = gep i8, ptr %117, %420
    %422 = const i64 8
    %423 = gep i8, ptr %124, %422
    %424 = load i64, ptr %421
    store i64 %424, ptr %423
    %425 = const i64 16
    %426 = gep i8, ptr %117, %425
    %427 = const i64 16
    %428 = gep i8, ptr %124, %427
    %429 = load i64, ptr %426
    store i64 %429, ptr %428
    call @func.49(%122, %123, %124)
    br bb32(%93)
bb30:
    %430 = const i64 8
    %431 = gep i8, ptr %118, %430
    %432 = load i64, ptr %431
    store i64 %432, ptr %120
    %433 = const i64 8
    %434 = gep i8, ptr %431, %433
    %435 = const i64 8
    %436 = gep i8, ptr %120, %435
    %437 = load i64, ptr %434
    store i64 %437, ptr %436
    %438 = const i64 16
    %439 = gep i8, ptr %431, %438
    %440 = const i64 16
    %441 = gep i8, ptr %120, %440
    %442 = load i64, ptr %439
    store i64 %442, ptr %441
    call @func.27(%0, %120)
    br bb31
bb31:
    %443 = const bool false
    %444 = const bool false
    br bb37
bb32(%94: bool):
    %445 = const i64 8
    %446 = gep i8, ptr %0, %445
    %447 = load i64, ptr %122
    store i64 %447, ptr %446
    %448 = const i64 8
    %449 = gep i8, ptr %122, %448
    %450 = const i64 8
    %451 = gep i8, ptr %446, %450
    %452 = load i64, ptr %449
    store i64 %452, ptr %451
    %453 = const i64 16
    %454 = gep i8, ptr %122, %453
    %455 = const i64 16
    %456 = gep i8, ptr %446, %455
    %457 = load i64, ptr %454
    store i64 %457, ptr %456
    %458 = const i64 0
    store i64 %458, ptr %0
    %459 = const bool false
    %460 = const bool false
    %461 = const bool false
    br bb34(%94)
bb33(%95: bool):
    %462 = load ptr, ptr %126
    %463 = const i64 8
    %464 = gep i8, ptr %125, %463
    store ptr %462, ptr %464
    %465 = const i32 4
    store i32 %465, ptr %125
    %466 = const i64 8
    %467 = gep i8, ptr %0, %466
    %468 = load i64, ptr %125
    store i64 %468, ptr %467
    %469 = const i64 8
    %470 = gep i8, ptr %125, %469
    %471 = const i64 8
    %472 = gep i8, ptr %467, %471
    %473 = load i64, ptr %470
    store i64 %473, ptr %472
    %474 = const i64 16
    %475 = gep i8, ptr %125, %474
    %476 = const i64 16
    %477 = gep i8, ptr %467, %476
    %478 = load i64, ptr %475
    store i64 %478, ptr %477
    %479 = const i64 1
    store i64 %479, ptr %0
    br bb34(%95)
bb34(%96: bool):
    br bb35(%96)
bb35(%97: bool):
    condbr %97, bb42, bb36
bb36:
    %480 = const bool false
    br bb41
bb37:
    %481 = const bool false
    br bb38
bb38:
    br bb39
bb39:
    br bb40
bb40:
    %482 = const bool false
    br bb41
bb41:
    ret
bb42:
    br bb36
bb43:
    br bb37
bb44:
    unreachable
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprE3newBE_(functy.33) {
}

fn @Verifier____env___infer_type(functy.34) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %5 = alloca (i64, i64, i64), align 8
    call @func.33(%5)
    br bb1(%1, %2)
bb1(%3: ptr, %4: ptr):
    call @func.45(%0, %3, %4, %5)
    br bb2
bb2:
    br bb3
bb3:
    ret
}

fn @Verifier____env___is_def_eq(functy.35) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %4 = call @func.55(%0, %1, %2)
    br bb1(%4)
bb1(%3: bool):
    ret %3
}

fn @_Expr_as_std__clone__Clone___clone(functy.36) {
bb0(%0: ptr, %1: ptr):
    %2 = alloca i64, align 8
    %3 = alloca (i64, i64, i64, i64), align 8
    %4 = alloca i64, align 8
    store ptr %1, ptr %2
    %5 = load ptr, ptr %2
    call @func.58(%3, %5)
    br bb1
bb1:
    %6 = load ptr, ptr %2
    %7 = const i64 32
    %8 = gep i8, ptr %6, %7
    call @func.59(%4, %8)
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

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprE3lenBG_(functy.37) {
}

fn @_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_(functy.38) {
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm14saturating_add(functy.39) {
}

fn @_RNvXsp_NtCs2EYQwhfuABO_4core6resultINtB5_6ResultNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprNtBM_9TypeErrorENtNtNtB7_3ops9try_trait3Try6branchBM_(functy.40) {
}

fn @_RNvXsq_NtCs2EYQwhfuABO_4core6resultINtB5_6ResultNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprNtBM_9TypeErrorEINtNtNtB7_3ops9try_trait12FromResidualIBy_NtNtB7_7convert10InfallibleB1w_EE13from_residualBM_(functy.41) {
}

fn @_RNvXs1j_NtCskTzINo8ZBH9_5alloc4syncINtB6_3ArcNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprEINtNtCs2EYQwhfuABO_4core7convert5AsRefBH_E6as_refBJ_(functy.42) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprE4pushBH_(functy.43) {
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprE3popBG_(functy.44) {
}

fn @Verifier____env___infer_type_core(functy.45) {
bb0(%0: ptr, %1: ptr, %2: ptr, %3: ptr):
    %341 = alloca i64, align 8
    %342 = alloca i64, align 8
    %343 = alloca i64, align 8
    %344 = alloca (i64, i64, i64, i64, i64), align 8
    %345 = alloca (i64, i64, i64), align 8
    %346 = alloca (i64, i64, i64), align 8
    %347 = alloca (i64, i64, i64), align 8
    %348 = alloca (i64, i64), align 8
    %349 = alloca (i64, i64), align 8
    %350 = alloca (i64, i64, i64, i64, i64), align 8
    %351 = alloca (i64, i64, i64, i64, i64), align 8
    %352 = alloca (i64, i64, i64, i64, i64), align 8
    %353 = alloca (i64, i64, i64, i64, i64), align 8
    %354 = alloca (i64, i64, i64), align 8
    %355 = alloca i32, align 4
    %356 = alloca (i64, i64, i64, i64, i64), align 8
    %357 = alloca (i64, i64, i64, i64, i64), align 8
    %358 = alloca (i64, i64, i64, i64, i64), align 8
    %359 = alloca (i64, i64, i64), align 8
    %360 = alloca (i64, i64, i64, i64, i64), align 8
    %361 = alloca (i64, i64, i64, i64, i64), align 8
    %362 = alloca i64, align 8
    %363 = alloca (i64, i64, i64, i64, i64), align 8
    %364 = alloca (i64, i64, i64, i64, i64), align 8
    %365 = alloca (i64, i64, i64, i64, i64), align 8
    %366 = alloca (i64, i64, i64), align 8
    %367 = alloca (i64, i64, i64, i64, i64), align 8
    %368 = alloca (i64, i64, i64), align 8
    %369 = alloca i64, align 8
    %370 = alloca (i64, i64, i64, i64, i64), align 8
    %371 = alloca i64, align 8
    %372 = alloca (i64, i64, i64, i64, i64), align 8
    %373 = alloca (i64, i64, i64, i64, i64), align 8
    %374 = alloca (i64, i64, i64), align 8
    %375 = alloca i64, align 8
    %376 = alloca (i64, i64, i64, i64, i64), align 8
    %377 = alloca (i64, i64, i64, i64, i64), align 8
    %378 = alloca (i64, i64, i64, i64, i64), align 8
    %379 = alloca (i64, i64, i64, i64, i64), align 8
    %380 = alloca (i64, i64, i64), align 8
    %381 = alloca (i64, i64, i64, i64, i64), align 8
    %382 = alloca (i64, i64, i64, i64, i64), align 8
    %383 = alloca (i64, i64, i64), align 8
    %384 = alloca i64, align 8
    %385 = alloca (i64, i64, i64, i64, i64), align 8
    %386 = alloca (i64, i64, i64, i64, i64), align 8
    %387 = alloca (i64, i64, i64, i64, i64), align 8
    %388 = alloca (i64, i64, i64, i64, i64), align 8
    %389 = alloca (i64, i64, i64, i64, i64), align 8
    %390 = alloca (i64, i64, i64, i64, i64), align 8
    %391 = alloca (i64, i64, i64, i64, i64), align 8
    %392 = alloca (i64, i64, i64), align 8
    %393 = alloca (i64, i64, i64, i64, i64), align 8
    %394 = alloca (i64, i64, i64, i64, i64), align 8
    %395 = alloca (i8, i8), align 1
    %396 = alloca (i64, i64, i64, i64, i64), align 8
    %397 = alloca (i64, i64, i64, i64, i64), align 8
    %398 = alloca (i64, i64, i64, i64, i64), align 8
    %399 = alloca (i64, i64, i64, i64, i64), align 8
    %400 = alloca (i64, i64, i64, i64, i64), align 8
    %401 = alloca (i64, i64, i64), align 8
    %402 = alloca (i64, i64, i64, i64, i64), align 8
    %403 = alloca (i64, i64, i64, i64, i64), align 8
    %404 = alloca (i64, i64, i64), align 8
    %405 = alloca i64, align 8
    %406 = alloca (i64, i64, i64), align 8
    %407 = alloca i64, align 8
    %408 = alloca (i64, i64, i64, i64, i64), align 8
    %409 = alloca (i64, i64, i64, i64, i64), align 8
    %410 = alloca (i64, i64, i64, i64, i64), align 8
    %411 = alloca (i64, i64, i64, i64, i64), align 8
    %412 = alloca (i64, i64, i64, i64, i64), align 8
    %413 = alloca (i64, i64, i64, i64, i64), align 8
    %414 = alloca (i64, i64, i64, i64, i64), align 8
    %415 = alloca (i64, i64, i64), align 8
    %416 = alloca (i64, i64, i64, i64, i64), align 8
    %417 = alloca (i64, i64, i64, i64, i64), align 8
    %418 = alloca (i64, i64, i64), align 8
    %419 = alloca i64, align 8
    %420 = alloca (i64, i64, i64), align 8
    %421 = alloca i64, align 8
    %422 = alloca (i64, i64, i64, i64, i64), align 8
    %423 = alloca (i64, i64, i64, i64, i64), align 8
    %424 = alloca (i64, i64, i64), align 8
    %425 = alloca (i64, i64, i64), align 8
    %426 = alloca (i64, i64, i64, i64, i64), align 8
    %427 = alloca (i64, i64, i64, i64, i64), align 8
    %428 = alloca (i64, i64, i64, i64, i64), align 8
    %429 = alloca (i64, i64, i64), align 8
    %430 = alloca (i64, i64, i64, i64, i64), align 8
    %431 = alloca (i64, i64, i64, i64, i64), align 8
    %432 = alloca (i64, i64, i64), align 8
    %433 = alloca i64, align 8
    %434 = alloca (i64, i64, i64, i64, i64), align 8
    %435 = alloca (i64, i64, i64, i64, i64), align 8
    %436 = alloca (i64, i64, i64, i64, i64), align 8
    %437 = alloca (i64, i64, i64, i64, i64), align 8
    %438 = alloca (i64, i64, i64), align 8
    %439 = alloca (i64, i64, i64, i64, i64), align 8
    %440 = alloca (i64, i64, i64), align 8
    %441 = alloca i64, align 8
    %442 = alloca (i64, i64, i64, i64, i64), align 8
    %443 = alloca i64, align 8
    %444 = alloca (i64, i64, i64, i64, i64), align 8
    %445 = alloca (i64, i64, i64, i64, i64), align 8
    %446 = alloca (i64, i64, i64, i64, i64), align 8
    %447 = alloca (i64, i64, i64, i64, i64), align 8
    %448 = alloca (i64, i64, i64, i64, i64), align 8
    %449 = alloca (i64, i64, i64, i64, i64), align 8
    %450 = alloca (i64, i64, i64, i64, i64), align 8
    %451 = alloca (i64, i64, i64), align 8
    %452 = alloca (i64, i64, i64, i64, i64), align 8
    %453 = alloca (i64, i64, i64, i64, i64), align 8
    %454 = alloca (i64, i64, i64, i64, i64), align 8
    %455 = alloca i32, align 4
    %456 = alloca i32, align 4
    %457 = alloca (i64, i64, i64), align 8
    store ptr %2, ptr %341
    store ptr %3, ptr %342
    %458 = const bool false
    %459 = const bool false
    %460 = const bool false
    %461 = const bool false
    %462 = const bool false
    %463 = const bool false
    %464 = const bool false
    %465 = const bool false
    %466 = const bool false
    %467 = const bool false
    %468 = const bool false
    %469 = const bool false
    %470 = load ptr, ptr %341
    store ptr %470, ptr %343
    %471 = load ptr, ptr %343
    %472 = load i8, ptr %471
    %473 = sext i8 %472 to i64
    switch %473 [ 0: bb9 2: bb10 3: bb8(%1) 4: bb7(%1) 5: bb6(%1) 6: bb5(%1) 7: bb4(%1) 8: bb3 10: bb2(%1) default: bb1 ]
bb1:
    %474 = const i32 6
    store i32 %474, ptr %457
    %475 = const i64 8
    %476 = gep i8, ptr %0, %475
    %477 = load i64, ptr %457
    store i64 %477, ptr %476
    %478 = const i64 8
    %479 = gep i8, ptr %457, %478
    %480 = const i64 8
    %481 = gep i8, ptr %476, %480
    %482 = load i64, ptr %479
    store i64 %482, ptr %481
    %483 = const i64 16
    %484 = gep i8, ptr %457, %483
    %485 = const i64 16
    %486 = gep i8, ptr %476, %485
    %487 = load i64, ptr %484
    store i64 %487, ptr %486
    %488 = const i8 11
    store i8 %488, ptr %0
    br bb171
bb2(%4: ptr):
    %489 = load ptr, ptr %343
    %490 = const i64 8
    %491 = gep i8, ptr %489, %490
    %492 = load ptr, ptr %491
    %493 = const i64 16
    %494 = gep i8, ptr %492, %493
    br bb155(%4, %494)
bb3:
    %495 = load ptr, ptr %343
    %496 = const i64 8
    %497 = gep i8, ptr %495, %496
    %498 = load i32, ptr %497
    %499 = sext i32 %498 to i64
    switch %499 [ 0: bb153 1: bb152 default: bb24 ]
bb4(%5: ptr):
    %500 = load ptr, ptr %343
    %501 = const i64 4
    %502 = gep i8, ptr %500, %501
    %503 = load ptr, ptr %343
    %504 = const i64 8
    %505 = gep i8, ptr %503, %504
    %506 = load ptr, ptr %343
    %507 = const i64 16
    %508 = gep i8, ptr %506, %507
    %509 = load ptr, ptr %343
    %510 = const i64 24
    %511 = gep i8, ptr %509, %510
    %512 = load ptr, ptr %343
    %513 = const i64 1
    %514 = gep i8, ptr %512, %513
    %515 = load ptr, ptr %505
    %516 = const i64 16
    %517 = gep i8, ptr %515, %516
    br bb113(%5, %505, %508, %511, %517)
bb5(%6: ptr):
    %518 = load ptr, ptr %343
    %519 = const i64 1
    %520 = gep i8, ptr %518, %519
    %521 = load ptr, ptr %343
    %522 = const i64 8
    %523 = gep i8, ptr %521, %522
    %524 = load ptr, ptr %343
    %525 = const i64 16
    %526 = gep i8, ptr %524, %525
    %527 = load ptr, ptr %523
    %528 = const i64 16
    %529 = gep i8, ptr %527, %528
    br bb82(%6, %523, %526, %529)
bb6(%7: ptr):
    %530 = load ptr, ptr %343
    %531 = const i64 1
    %532 = gep i8, ptr %530, %531
    %533 = load ptr, ptr %343
    %534 = const i64 8
    %535 = gep i8, ptr %533, %534
    %536 = load ptr, ptr %343
    %537 = const i64 16
    %538 = gep i8, ptr %536, %537
    %539 = load ptr, ptr %535
    %540 = const i64 16
    %541 = gep i8, ptr %539, %540
    br bb57(%7, %532, %535, %538, %541)
bb7(%8: ptr):
    %542 = load ptr, ptr %343
    %543 = const i64 8
    %544 = gep i8, ptr %542, %543
    %545 = load ptr, ptr %343
    %546 = const i64 16
    %547 = gep i8, ptr %545, %546
    %548 = load ptr, ptr %544
    %549 = const i64 16
    %550 = gep i8, ptr %548, %549
    br bb27(%8, %547, %550)
bb8(%9: ptr):
    %551 = load ptr, ptr %343
    %552 = const i64 4
    %553 = gep i8, ptr %551, %552
    %554 = load ptr, ptr %343
    %555 = const i64 8
    %556 = gep i8, ptr %554, %555
    call @func.60(%352, %9, %553)
    br bb23(%553)
bb9:
    %557 = load ptr, ptr %343
    %558 = const i64 4
    %559 = gep i8, ptr %557, %558
    %560 = load ptr, ptr %342
    %561 = call @func.37(%560)
    br bb14(%559, %561)
bb10:
    %562 = load ptr, ptr %343
    %563 = const i64 8
    %564 = gep i8, ptr %562, %563
    call @func.48(%346, %564)
    br bb11
bb11:
    call @func.61(%345, %346)
    br bb12
bb12:
    call @func.62(%344, %345)
    br bb13
bb13:
    %565 = load i64, ptr %344
    store i64 %565, ptr %0
    %566 = const i64 8
    %567 = gep i8, ptr %344, %566
    %568 = const i64 8
    %569 = gep i8, ptr %0, %568
    %570 = load i64, ptr %567
    store i64 %570, ptr %569
    %571 = const i64 16
    %572 = gep i8, ptr %344, %571
    %573 = const i64 16
    %574 = gep i8, ptr %0, %573
    %575 = load i64, ptr %572
    store i64 %575, ptr %574
    %576 = const i64 24
    %577 = gep i8, ptr %344, %576
    %578 = const i64 24
    %579 = gep i8, ptr %0, %578
    %580 = load i64, ptr %577
    store i64 %580, ptr %579
    %581 = const i64 32
    %582 = gep i8, ptr %344, %581
    %583 = const i64 32
    %584 = gep i8, ptr %0, %583
    %585 = load i64, ptr %582
    store i64 %585, ptr %584
    br bb171
bb14(%10: ptr, %11: u64):
    %586 = load u32, ptr %10
    %587 = zext u32 %586 to u64
    %588 = icmp uge u64 %587, %11
    condbr %588, bb15(%10), bb16(%10, %11)
bb15(%12: ptr):
    %589 = load u32, ptr %12
    %590 = const i64 4
    %591 = gep i8, ptr %347, %590
    store u32 %589, ptr %591
    %592 = const i32 0
    store i32 %592, ptr %347
    %593 = const i64 8
    %594 = gep i8, ptr %0, %593
    %595 = load i64, ptr %347
    store i64 %595, ptr %594
    %596 = const i64 8
    %597 = gep i8, ptr %347, %596
    %598 = const i64 8
    %599 = gep i8, ptr %594, %598
    %600 = load i64, ptr %597
    store i64 %600, ptr %599
    %601 = const i64 16
    %602 = gep i8, ptr %347, %601
    %603 = const i64 16
    %604 = gep i8, ptr %594, %603
    %605 = load i64, ptr %602
    store i64 %605, ptr %604
    %606 = const i8 11
    store i8 %606, ptr %0
    br bb171
bb16(%13: ptr, %14: u64):
    %607 = const u64 1
    %608, %609 = sub.overflow u64 %14, %607
    store u64 %608, ptr %348
    %610 = const i64 8
    %611 = gep i8, ptr %348, %610
    store bool %609, ptr %611
    %612 = const i64 8
    %613 = gep i8, ptr %348, %612
    %614 = load bool, ptr %613
    %615 = const bool false
    %616 = icmp eq bool %614, %615
    condbr %616, bb17(%13), bb180
bb17(%15: ptr):
    %617 = load u64, ptr %348
    %618 = load u32, ptr %15
    %619 = zext u32 %618 to u64
    %620, %621 = sub.overflow u64 %617, %619
    store u64 %620, ptr %349
    %622 = const i64 8
    %623 = gep i8, ptr %349, %622
    store bool %621, ptr %623
    %624 = const i64 8
    %625 = gep i8, ptr %349, %624
    %626 = load bool, ptr %625
    %627 = const bool false
    %628 = icmp eq bool %626, %627
    condbr %628, bb18(%15), bb180
bb18(%16: ptr):
    %629 = load u64, ptr %349
    %630 = load ptr, ptr %342
    %631 = call @func.38(%630, %629)
    br bb19(%16, %631)
bb19(%17: ptr, %18: ptr):
    call @func.36(%350, %18)
    br bb20(%17)
bb20(%19: ptr):
    %632 = load u32, ptr %19
    %633 = const u32 1
    %634 = call @func.39(%632, %633)
    br bb21(%350, %634)
bb21(%20: ptr, %21: u32):
    %635 = const u32 0
    call @func.64(%351, %20, %635, %21)
    br bb22
bb22:
    %636 = load i64, ptr %351
    store i64 %636, ptr %0
    %637 = const i64 8
    %638 = gep i8, ptr %351, %637
    %639 = const i64 8
    %640 = gep i8, ptr %0, %639
    %641 = load i64, ptr %638
    store i64 %641, ptr %640
    %642 = const i64 16
    %643 = gep i8, ptr %351, %642
    %644 = const i64 16
    %645 = gep i8, ptr %0, %644
    %646 = load i64, ptr %643
    store i64 %646, ptr %645
    %647 = const i64 24
    %648 = gep i8, ptr %351, %647
    %649 = const i64 24
    %650 = gep i8, ptr %0, %649
    %651 = load i64, ptr %648
    store i64 %651, ptr %650
    %652 = const i64 32
    %653 = gep i8, ptr %351, %652
    %654 = const i64 32
    %655 = gep i8, ptr %0, %654
    %656 = load i64, ptr %653
    store i64 %656, ptr %655
    br bb171
bb23(%22: ptr):
    %657 = load i8, ptr %352
    %658 = const i8 11
    %659 = icmp eq i8 %657, %658
    %660 = const i64 0
    %661 = const i64 1
    %662 = select i64 %659, %660, %661
    switch %662 [ 0: bb25(%22) 1: bb26 default: bb24 ]
bb24:
    unreachable
bb25(%23: ptr):
    %663 = load i32, ptr %23
    store i32 %663, ptr %355
    %664 = const i64 4
    %665 = gep i8, ptr %354, %664
    %666 = load i32, ptr %355
    store i32 %666, ptr %665
    %667 = const i32 1
    store i32 %667, ptr %354
    %668 = const i64 8
    %669 = gep i8, ptr %0, %668
    %670 = load i64, ptr %354
    store i64 %670, ptr %669
    %671 = const i64 8
    %672 = gep i8, ptr %354, %671
    %673 = const i64 8
    %674 = gep i8, ptr %669, %673
    %675 = load i64, ptr %672
    store i64 %675, ptr %674
    %676 = const i64 16
    %677 = gep i8, ptr %354, %676
    %678 = const i64 16
    %679 = gep i8, ptr %669, %678
    %680 = load i64, ptr %677
    store i64 %680, ptr %679
    %681 = const i8 11
    store i8 %681, ptr %0
    br bb171
bb26:
    %682 = load i64, ptr %352
    store i64 %682, ptr %353
    %683 = const i64 8
    %684 = gep i8, ptr %352, %683
    %685 = const i64 8
    %686 = gep i8, ptr %353, %685
    %687 = load i64, ptr %684
    store i64 %687, ptr %686
    %688 = const i64 16
    %689 = gep i8, ptr %352, %688
    %690 = const i64 16
    %691 = gep i8, ptr %353, %690
    %692 = load i64, ptr %689
    store i64 %692, ptr %691
    %693 = const i64 24
    %694 = gep i8, ptr %352, %693
    %695 = const i64 24
    %696 = gep i8, ptr %353, %695
    %697 = load i64, ptr %694
    store i64 %697, ptr %696
    %698 = const i64 32
    %699 = gep i8, ptr %352, %698
    %700 = const i64 32
    %701 = gep i8, ptr %353, %700
    %702 = load i64, ptr %699
    store i64 %702, ptr %701
    %703 = load i64, ptr %353
    store i64 %703, ptr %0
    %704 = const i64 8
    %705 = gep i8, ptr %353, %704
    %706 = const i64 8
    %707 = gep i8, ptr %0, %706
    %708 = load i64, ptr %705
    store i64 %708, ptr %707
    %709 = const i64 16
    %710 = gep i8, ptr %353, %709
    %711 = const i64 16
    %712 = gep i8, ptr %0, %711
    %713 = load i64, ptr %710
    store i64 %713, ptr %712
    %714 = const i64 24
    %715 = gep i8, ptr %353, %714
    %716 = const i64 24
    %717 = gep i8, ptr %0, %716
    %718 = load i64, ptr %715
    store i64 %718, ptr %717
    %719 = const i64 32
    %720 = gep i8, ptr %353, %719
    %721 = const i64 32
    %722 = gep i8, ptr %0, %721
    %723 = load i64, ptr %720
    store i64 %723, ptr %722
    br bb171
bb27(%24: ptr, %25: ptr, %26: ptr):
    %724 = load ptr, ptr %342
    call @func.45(%358, %24, %26, %724)
    br bb28(%24, %25)
bb28(%27: ptr, %28: ptr):
    call @func.40(%357, %358)
    br bb29(%27, %28)
bb29(%29: ptr, %30: ptr):
    %725 = load i8, ptr %357
    %726 = const i8 11
    %727 = icmp eq i8 %725, %726
    %728 = const i64 1
    %729 = const i64 0
    %730 = select i64 %727, %728, %729
    switch %730 [ 0: bb30(%29, %30) 1: bb31 default: bb24 ]
bb30(%31: ptr, %32: ptr):
    %731 = load i64, ptr %357
    store i64 %731, ptr %360
    %732 = const i64 8
    %733 = gep i8, ptr %357, %732
    %734 = const i64 8
    %735 = gep i8, ptr %360, %734
    %736 = load i64, ptr %733
    store i64 %736, ptr %735
    %737 = const i64 16
    %738 = gep i8, ptr %357, %737
    %739 = const i64 16
    %740 = gep i8, ptr %360, %739
    %741 = load i64, ptr %738
    store i64 %741, ptr %740
    %742 = const i64 24
    %743 = gep i8, ptr %357, %742
    %744 = const i64 24
    %745 = gep i8, ptr %360, %744
    %746 = load i64, ptr %743
    store i64 %746, ptr %745
    %747 = const i64 32
    %748 = gep i8, ptr %357, %747
    %749 = const i64 32
    %750 = gep i8, ptr %360, %749
    %751 = load i64, ptr %748
    store i64 %751, ptr %750
    %752 = const bool true
    %753 = load i64, ptr %360
    store i64 %753, ptr %356
    %754 = const i64 8
    %755 = gep i8, ptr %360, %754
    %756 = const i64 8
    %757 = gep i8, ptr %356, %756
    %758 = load i64, ptr %755
    store i64 %758, ptr %757
    %759 = const i64 16
    %760 = gep i8, ptr %360, %759
    %761 = const i64 16
    %762 = gep i8, ptr %356, %761
    %763 = load i64, ptr %760
    store i64 %763, ptr %762
    %764 = const i64 24
    %765 = gep i8, ptr %360, %764
    %766 = const i64 24
    %767 = gep i8, ptr %356, %766
    %768 = load i64, ptr %765
    store i64 %768, ptr %767
    %769 = const i64 32
    %770 = gep i8, ptr %360, %769
    %771 = const i64 32
    %772 = gep i8, ptr %356, %771
    %773 = load i64, ptr %770
    store i64 %773, ptr %772
    call @func.46(%361, %31, %356)
    br bb33(%31, %32, %752)
bb31:
    %774 = const i64 8
    %775 = gep i8, ptr %357, %774
    %776 = load i64, ptr %775
    store i64 %776, ptr %359
    %777 = const i64 8
    %778 = gep i8, ptr %775, %777
    %779 = const i64 8
    %780 = gep i8, ptr %359, %779
    %781 = load i64, ptr %778
    store i64 %781, ptr %780
    %782 = const i64 16
    %783 = gep i8, ptr %775, %782
    %784 = const i64 16
    %785 = gep i8, ptr %359, %784
    %786 = load i64, ptr %783
    store i64 %786, ptr %785
    call @func.41(%0, %359)
    br bb32
bb32:
    %787 = const bool false
    br bb171
bb33(%33: ptr, %34: ptr, %35: bool):
    store ptr %361, ptr %362
    %788 = load ptr, ptr %362
    %789 = load i8, ptr %788
    %790 = sext i8 %789 to i64
    switch %790 [ 6: bb35(%33, %34, %35) default: bb34 ]
bb34:
    %791 = const bool false
    %792 = load i64, ptr %356
    store i64 %792, ptr %376
    %793 = const i64 8
    %794 = gep i8, ptr %356, %793
    %795 = const i64 8
    %796 = gep i8, ptr %376, %795
    %797 = load i64, ptr %794
    store i64 %797, ptr %796
    %798 = const i64 16
    %799 = gep i8, ptr %356, %798
    %800 = const i64 16
    %801 = gep i8, ptr %376, %800
    %802 = load i64, ptr %799
    store i64 %802, ptr %801
    %803 = const i64 24
    %804 = gep i8, ptr %356, %803
    %805 = const i64 24
    %806 = gep i8, ptr %376, %805
    %807 = load i64, ptr %804
    store i64 %807, ptr %806
    %808 = const i64 32
    %809 = gep i8, ptr %356, %808
    %810 = const i64 32
    %811 = gep i8, ptr %376, %810
    %812 = load i64, ptr %809
    store i64 %812, ptr %811
    %813 = const i64 56
    %814 = heap_alloc rust_heap i8, %813, align 8
    %815 = const u64 1
    store u64 %815, ptr %814
    %816 = const i64 8
    %817 = gep i8, ptr %814, %816
    %818 = const u64 1
    store u64 %818, ptr %817
    %819 = const i64 16
    %820 = gep i8, ptr %814, %819
    %821 = load i64, ptr %376
    store i64 %821, ptr %820
    %822 = const i64 8
    %823 = gep i8, ptr %376, %822
    %824 = const i64 8
    %825 = gep i8, ptr %820, %824
    %826 = load i64, ptr %823
    store i64 %826, ptr %825
    %827 = const i64 16
    %828 = gep i8, ptr %376, %827
    %829 = const i64 16
    %830 = gep i8, ptr %820, %829
    %831 = load i64, ptr %828
    store i64 %831, ptr %830
    %832 = const i64 24
    %833 = gep i8, ptr %376, %832
    %834 = const i64 24
    %835 = gep i8, ptr %820, %834
    %836 = load i64, ptr %833
    store i64 %836, ptr %835
    %837 = const i64 32
    %838 = gep i8, ptr %376, %837
    %839 = const i64 32
    %840 = gep i8, ptr %820, %839
    %841 = load i64, ptr %838
    store i64 %841, ptr %840
    store ptr %814, ptr %375
    br bb53(%791)
bb35(%36: ptr, %37: ptr, %38: bool):
    %842 = load ptr, ptr %362
    %843 = const i64 8
    %844 = gep i8, ptr %842, %843
    %845 = load ptr, ptr %362
    %846 = const i64 16
    %847 = gep i8, ptr %845, %846
    %848 = load ptr, ptr %37
    %849 = const i64 16
    %850 = gep i8, ptr %848, %849
    br bb36(%36, %37, %844, %847, %850, %38)
bb36(%39: ptr, %40: ptr, %41: ptr, %42: ptr, %43: ptr, %44: bool):
    %851 = load ptr, ptr %342
    call @func.45(%365, %39, %43, %851)
    br bb37(%39, %40, %41, %42, %44)
bb37(%45: ptr, %46: ptr, %47: ptr, %48: ptr, %49: bool):
    call @func.40(%364, %365)
    br bb38(%45, %46, %47, %48, %49)
bb38(%50: ptr, %51: ptr, %52: ptr, %53: ptr, %54: bool):
    %852 = load i8, ptr %364
    %853 = const i8 11
    %854 = icmp eq i8 %852, %853
    %855 = const i64 1
    %856 = const i64 0
    %857 = select i64 %854, %855, %856
    switch %857 [ 0: bb39(%50, %51, %52, %53, %54) 1: bb40 default: bb24 ]
bb39(%55: ptr, %56: ptr, %57: ptr, %58: ptr, %59: bool):
    %858 = load i64, ptr %364
    store i64 %858, ptr %367
    %859 = const i64 8
    %860 = gep i8, ptr %364, %859
    %861 = const i64 8
    %862 = gep i8, ptr %367, %861
    %863 = load i64, ptr %860
    store i64 %863, ptr %862
    %864 = const i64 16
    %865 = gep i8, ptr %364, %864
    %866 = const i64 16
    %867 = gep i8, ptr %367, %866
    %868 = load i64, ptr %865
    store i64 %868, ptr %867
    %869 = const i64 24
    %870 = gep i8, ptr %364, %869
    %871 = const i64 24
    %872 = gep i8, ptr %367, %871
    %873 = load i64, ptr %870
    store i64 %873, ptr %872
    %874 = const i64 32
    %875 = gep i8, ptr %364, %874
    %876 = const i64 32
    %877 = gep i8, ptr %367, %876
    %878 = load i64, ptr %875
    store i64 %878, ptr %877
    %879 = const bool true
    %880 = load i64, ptr %367
    store i64 %880, ptr %363
    %881 = const i64 8
    %882 = gep i8, ptr %367, %881
    %883 = const i64 8
    %884 = gep i8, ptr %363, %883
    %885 = load i64, ptr %882
    store i64 %885, ptr %884
    %886 = const i64 16
    %887 = gep i8, ptr %367, %886
    %888 = const i64 16
    %889 = gep i8, ptr %363, %888
    %890 = load i64, ptr %887
    store i64 %890, ptr %889
    %891 = const i64 24
    %892 = gep i8, ptr %367, %891
    %893 = const i64 24
    %894 = gep i8, ptr %363, %893
    %895 = load i64, ptr %892
    store i64 %895, ptr %894
    %896 = const i64 32
    %897 = gep i8, ptr %367, %896
    %898 = const i64 32
    %899 = gep i8, ptr %363, %898
    %900 = load i64, ptr %897
    store i64 %900, ptr %899
    %901 = load ptr, ptr %57
    %902 = const i64 16
    %903 = gep i8, ptr %901, %902
    br bb41(%55, %56, %57, %58, %363, %903, %59)
bb40:
    %904 = const i64 8
    %905 = gep i8, ptr %364, %904
    %906 = load i64, ptr %905
    store i64 %906, ptr %366
    %907 = const i64 8
    %908 = gep i8, ptr %905, %907
    %909 = const i64 8
    %910 = gep i8, ptr %366, %909
    %911 = load i64, ptr %908
    store i64 %911, ptr %910
    %912 = const i64 16
    %913 = gep i8, ptr %905, %912
    %914 = const i64 16
    %915 = gep i8, ptr %366, %914
    %916 = load i64, ptr %913
    store i64 %916, ptr %915
    call @func.41(%0, %366)
    br bb177
bb41(%60: ptr, %61: ptr, %62: ptr, %63: ptr, %64: ptr, %65: ptr, %66: bool):
    %917 = call @func.35(%60, %64, %65)
    br bb42(%61, %62, %63, %917, %66)
bb42(%67: ptr, %68: ptr, %69: ptr, %70: bool, %71: bool):
    condbr %70, bb43(%67, %69, %71), bb44(%68)
bb43(%72: ptr, %73: ptr, %74: bool):
    %918 = load ptr, ptr %73
    %919 = const i64 16
    %920 = gep i8, ptr %918, %919
    br bb49(%72, %920, %74)
bb44(%75: ptr):
    %921 = call @func.42(%75)
    br bb45(%921)
bb45(%76: ptr):
    call @func.36(%370, %76)
    br bb46
bb46:
    %922 = const i64 56
    %923 = heap_alloc rust_heap i8, %922, align 8
    %924 = const u64 1
    store u64 %924, ptr %923
    %925 = const i64 8
    %926 = gep i8, ptr %923, %925
    %927 = const u64 1
    store u64 %927, ptr %926
    %928 = const i64 16
    %929 = gep i8, ptr %923, %928
    %930 = load i64, ptr %370
    store i64 %930, ptr %929
    %931 = const i64 8
    %932 = gep i8, ptr %370, %931
    %933 = const i64 8
    %934 = gep i8, ptr %929, %933
    %935 = load i64, ptr %932
    store i64 %935, ptr %934
    %936 = const i64 16
    %937 = gep i8, ptr %370, %936
    %938 = const i64 16
    %939 = gep i8, ptr %929, %938
    %940 = load i64, ptr %937
    store i64 %940, ptr %939
    %941 = const i64 24
    %942 = gep i8, ptr %370, %941
    %943 = const i64 24
    %944 = gep i8, ptr %929, %943
    %945 = load i64, ptr %942
    store i64 %945, ptr %944
    %946 = const i64 32
    %947 = gep i8, ptr %370, %946
    %948 = const i64 32
    %949 = gep i8, ptr %929, %948
    %950 = load i64, ptr %947
    store i64 %950, ptr %949
    store ptr %923, ptr %369
    br bb47
bb47:
    %951 = const bool false
    %952 = load i64, ptr %363
    store i64 %952, ptr %372
    %953 = const i64 8
    %954 = gep i8, ptr %363, %953
    %955 = const i64 8
    %956 = gep i8, ptr %372, %955
    %957 = load i64, ptr %954
    store i64 %957, ptr %956
    %958 = const i64 16
    %959 = gep i8, ptr %363, %958
    %960 = const i64 16
    %961 = gep i8, ptr %372, %960
    %962 = load i64, ptr %959
    store i64 %962, ptr %961
    %963 = const i64 24
    %964 = gep i8, ptr %363, %963
    %965 = const i64 24
    %966 = gep i8, ptr %372, %965
    %967 = load i64, ptr %964
    store i64 %967, ptr %966
    %968 = const i64 32
    %969 = gep i8, ptr %363, %968
    %970 = const i64 32
    %971 = gep i8, ptr %372, %970
    %972 = load i64, ptr %969
    store i64 %972, ptr %971
    %973 = const i64 56
    %974 = heap_alloc rust_heap i8, %973, align 8
    %975 = const u64 1
    store u64 %975, ptr %974
    %976 = const i64 8
    %977 = gep i8, ptr %974, %976
    %978 = const u64 1
    store u64 %978, ptr %977
    %979 = const i64 16
    %980 = gep i8, ptr %974, %979
    %981 = load i64, ptr %372
    store i64 %981, ptr %980
    %982 = const i64 8
    %983 = gep i8, ptr %372, %982
    %984 = const i64 8
    %985 = gep i8, ptr %980, %984
    %986 = load i64, ptr %983
    store i64 %986, ptr %985
    %987 = const i64 16
    %988 = gep i8, ptr %372, %987
    %989 = const i64 16
    %990 = gep i8, ptr %980, %989
    %991 = load i64, ptr %988
    store i64 %991, ptr %990
    %992 = const i64 24
    %993 = gep i8, ptr %372, %992
    %994 = const i64 24
    %995 = gep i8, ptr %980, %994
    %996 = load i64, ptr %993
    store i64 %996, ptr %995
    %997 = const i64 32
    %998 = gep i8, ptr %372, %997
    %999 = const i64 32
    %1000 = gep i8, ptr %980, %999
    %1001 = load i64, ptr %998
    store i64 %1001, ptr %1000
    store ptr %974, ptr %371
    br bb48
bb48:
    %1002 = load ptr, ptr %369
    %1003 = const i64 8
    %1004 = gep i8, ptr %368, %1003
    store ptr %1002, ptr %1004
    %1005 = load ptr, ptr %371
    %1006 = const i64 16
    %1007 = gep i8, ptr %368, %1006
    store ptr %1005, ptr %1007
    %1008 = const i32 2
    store i32 %1008, ptr %368
    %1009 = const i64 8
    %1010 = gep i8, ptr %0, %1009
    %1011 = load i64, ptr %368
    store i64 %1011, ptr %1010
    %1012 = const i64 8
    %1013 = gep i8, ptr %368, %1012
    %1014 = const i64 8
    %1015 = gep i8, ptr %1010, %1014
    %1016 = load i64, ptr %1013
    store i64 %1016, ptr %1015
    %1017 = const i64 16
    %1018 = gep i8, ptr %368, %1017
    %1019 = const i64 16
    %1020 = gep i8, ptr %1010, %1019
    %1021 = load i64, ptr %1018
    store i64 %1021, ptr %1020
    %1022 = const i8 11
    store i8 %1022, ptr %0
    br bb168
bb49(%77: ptr, %78: ptr, %79: bool):
    %1023 = load ptr, ptr %77
    %1024 = const i64 16
    %1025 = gep i8, ptr %1023, %1024
    br bb50(%78, %1025, %79)
bb50(%80: ptr, %81: ptr, %82: bool):
    call @func.65(%373, %80, %81)
    br bb51(%82)
bb51(%83: bool):
    %1026 = load i64, ptr %373
    store i64 %1026, ptr %0
    %1027 = const i64 8
    %1028 = gep i8, ptr %373, %1027
    %1029 = const i64 8
    %1030 = gep i8, ptr %0, %1029
    %1031 = load i64, ptr %1028
    store i64 %1031, ptr %1030
    %1032 = const i64 16
    %1033 = gep i8, ptr %373, %1032
    %1034 = const i64 16
    %1035 = gep i8, ptr %0, %1034
    %1036 = load i64, ptr %1033
    store i64 %1036, ptr %1035
    %1037 = const i64 24
    %1038 = gep i8, ptr %373, %1037
    %1039 = const i64 24
    %1040 = gep i8, ptr %0, %1039
    %1041 = load i64, ptr %1038
    store i64 %1041, ptr %1040
    %1042 = const i64 32
    %1043 = gep i8, ptr %373, %1042
    %1044 = const i64 32
    %1045 = gep i8, ptr %0, %1044
    %1046 = load i64, ptr %1043
    store i64 %1046, ptr %1045
    br bb52(%83)
bb52(%84: bool):
    %1047 = const bool false
    br bb54(%84)
bb53(%85: bool):
    %1048 = load ptr, ptr %375
    %1049 = const i64 8
    %1050 = gep i8, ptr %374, %1049
    store ptr %1048, ptr %1050
    %1051 = const i32 3
    store i32 %1051, ptr %374
    %1052 = const i64 8
    %1053 = gep i8, ptr %0, %1052
    %1054 = load i64, ptr %374
    store i64 %1054, ptr %1053
    %1055 = const i64 8
    %1056 = gep i8, ptr %374, %1055
    %1057 = const i64 8
    %1058 = gep i8, ptr %1053, %1057
    %1059 = load i64, ptr %1056
    store i64 %1059, ptr %1058
    %1060 = const i64 16
    %1061 = gep i8, ptr %374, %1060
    %1062 = const i64 16
    %1063 = gep i8, ptr %1053, %1062
    %1064 = load i64, ptr %1061
    store i64 %1064, ptr %1063
    %1065 = const i8 11
    store i8 %1065, ptr %0
    br bb54(%85)
bb54(%86: bool):
    br bb55(%86)
bb55(%87: bool):
    condbr %87, bb172, bb56
bb56:
    %1066 = const bool false
    br bb171
bb57(%88: ptr, %89: ptr, %90: ptr, %91: ptr, %92: ptr):
    %1067 = load ptr, ptr %342
    call @func.45(%379, %88, %92, %1067)
    br bb58(%88, %89, %90, %91)
bb58(%93: ptr, %94: ptr, %95: ptr, %96: ptr):
    call @func.40(%378, %379)
    br bb59(%93, %94, %95, %96)
bb59(%97: ptr, %98: ptr, %99: ptr, %100: ptr):
    %1068 = load i8, ptr %378
    %1069 = const i8 11
    %1070 = icmp eq i8 %1068, %1069
    %1071 = const i64 1
    %1072 = const i64 0
    %1073 = select i64 %1070, %1071, %1072
    switch %1073 [ 0: bb60(%97, %98, %99, %100) 1: bb61 default: bb24 ]
bb60(%101: ptr, %102: ptr, %103: ptr, %104: ptr):
    %1074 = load i64, ptr %378
    store i64 %1074, ptr %381
    %1075 = const i64 8
    %1076 = gep i8, ptr %378, %1075
    %1077 = const i64 8
    %1078 = gep i8, ptr %381, %1077
    %1079 = load i64, ptr %1076
    store i64 %1079, ptr %1078
    %1080 = const i64 16
    %1081 = gep i8, ptr %378, %1080
    %1082 = const i64 16
    %1083 = gep i8, ptr %381, %1082
    %1084 = load i64, ptr %1081
    store i64 %1084, ptr %1083
    %1085 = const i64 24
    %1086 = gep i8, ptr %378, %1085
    %1087 = const i64 24
    %1088 = gep i8, ptr %381, %1087
    %1089 = load i64, ptr %1086
    store i64 %1089, ptr %1088
    %1090 = const i64 32
    %1091 = gep i8, ptr %378, %1090
    %1092 = const i64 32
    %1093 = gep i8, ptr %381, %1092
    %1094 = load i64, ptr %1091
    store i64 %1094, ptr %1093
    %1095 = const bool true
    %1096 = load i64, ptr %381
    store i64 %1096, ptr %377
    %1097 = const i64 8
    %1098 = gep i8, ptr %381, %1097
    %1099 = const i64 8
    %1100 = gep i8, ptr %377, %1099
    %1101 = load i64, ptr %1098
    store i64 %1101, ptr %1100
    %1102 = const i64 16
    %1103 = gep i8, ptr %381, %1102
    %1104 = const i64 16
    %1105 = gep i8, ptr %377, %1104
    %1106 = load i64, ptr %1103
    store i64 %1106, ptr %1105
    %1107 = const i64 24
    %1108 = gep i8, ptr %381, %1107
    %1109 = const i64 24
    %1110 = gep i8, ptr %377, %1109
    %1111 = load i64, ptr %1108
    store i64 %1111, ptr %1110
    %1112 = const i64 32
    %1113 = gep i8, ptr %381, %1112
    %1114 = const i64 32
    %1115 = gep i8, ptr %377, %1114
    %1116 = load i64, ptr %1113
    store i64 %1116, ptr %1115
    call @func.46(%382, %101, %377)
    br bb62(%101, %102, %103, %104, %1095)
bb61:
    %1117 = const i64 8
    %1118 = gep i8, ptr %378, %1117
    %1119 = load i64, ptr %1118
    store i64 %1119, ptr %380
    %1120 = const i64 8
    %1121 = gep i8, ptr %1118, %1120
    %1122 = const i64 8
    %1123 = gep i8, ptr %380, %1122
    %1124 = load i64, ptr %1121
    store i64 %1124, ptr %1123
    %1125 = const i64 16
    %1126 = gep i8, ptr %1118, %1125
    %1127 = const i64 16
    %1128 = gep i8, ptr %380, %1127
    %1129 = load i64, ptr %1126
    store i64 %1129, ptr %1128
    call @func.41(%0, %380)
    br bb167
bb62(%105: ptr, %106: ptr, %107: ptr, %108: ptr, %109: bool):
    %1130 = load i8, ptr %382
    %1131 = sext i8 %1130 to i64
    switch %1131 [ 2: bb64(%105, %106, %107, %108, %109) default: bb63 ]
bb63:
    %1132 = const bool false
    %1133 = load i64, ptr %377
    store i64 %1133, ptr %385
    %1134 = const i64 8
    %1135 = gep i8, ptr %377, %1134
    %1136 = const i64 8
    %1137 = gep i8, ptr %385, %1136
    %1138 = load i64, ptr %1135
    store i64 %1138, ptr %1137
    %1139 = const i64 16
    %1140 = gep i8, ptr %377, %1139
    %1141 = const i64 16
    %1142 = gep i8, ptr %385, %1141
    %1143 = load i64, ptr %1140
    store i64 %1143, ptr %1142
    %1144 = const i64 24
    %1145 = gep i8, ptr %377, %1144
    %1146 = const i64 24
    %1147 = gep i8, ptr %385, %1146
    %1148 = load i64, ptr %1145
    store i64 %1148, ptr %1147
    %1149 = const i64 32
    %1150 = gep i8, ptr %377, %1149
    %1151 = const i64 32
    %1152 = gep i8, ptr %385, %1151
    %1153 = load i64, ptr %1150
    store i64 %1153, ptr %1152
    %1154 = const i64 56
    %1155 = heap_alloc rust_heap i8, %1154, align 8
    %1156 = const u64 1
    store u64 %1156, ptr %1155
    %1157 = const i64 8
    %1158 = gep i8, ptr %1155, %1157
    %1159 = const u64 1
    store u64 %1159, ptr %1158
    %1160 = const i64 16
    %1161 = gep i8, ptr %1155, %1160
    %1162 = load i64, ptr %385
    store i64 %1162, ptr %1161
    %1163 = const i64 8
    %1164 = gep i8, ptr %385, %1163
    %1165 = const i64 8
    %1166 = gep i8, ptr %1161, %1165
    %1167 = load i64, ptr %1164
    store i64 %1167, ptr %1166
    %1168 = const i64 16
    %1169 = gep i8, ptr %385, %1168
    %1170 = const i64 16
    %1171 = gep i8, ptr %1161, %1170
    %1172 = load i64, ptr %1169
    store i64 %1172, ptr %1171
    %1173 = const i64 24
    %1174 = gep i8, ptr %385, %1173
    %1175 = const i64 24
    %1176 = gep i8, ptr %1161, %1175
    %1177 = load i64, ptr %1174
    store i64 %1177, ptr %1176
    %1178 = const i64 32
    %1179 = gep i8, ptr %385, %1178
    %1180 = const i64 32
    %1181 = gep i8, ptr %1161, %1180
    %1182 = load i64, ptr %1179
    store i64 %1182, ptr %1181
    store ptr %1155, ptr %384
    br bb65(%1132)
bb64(%110: ptr, %111: ptr, %112: ptr, %113: ptr, %114: bool):
    %1183 = call @func.42(%112)
    br bb66(%110, %111, %112, %113, %1183, %114)
bb65(%115: bool):
    %1184 = load ptr, ptr %384
    %1185 = const i64 8
    %1186 = gep i8, ptr %383, %1185
    store ptr %1184, ptr %1186
    %1187 = const i32 4
    store i32 %1187, ptr %383
    %1188 = const i64 8
    %1189 = gep i8, ptr %0, %1188
    %1190 = load i64, ptr %383
    store i64 %1190, ptr %1189
    %1191 = const i64 8
    %1192 = gep i8, ptr %383, %1191
    %1193 = const i64 8
    %1194 = gep i8, ptr %1189, %1193
    %1195 = load i64, ptr %1192
    store i64 %1195, ptr %1194
    %1196 = const i64 16
    %1197 = gep i8, ptr %383, %1196
    %1198 = const i64 16
    %1199 = gep i8, ptr %1189, %1198
    %1200 = load i64, ptr %1197
    store i64 %1200, ptr %1199
    %1201 = const i8 11
    store i8 %1201, ptr %0
    br bb165(%115)
bb66(%116: ptr, %117: ptr, %118: ptr, %119: ptr, %120: ptr, %121: bool):
    call @func.36(%386, %120)
    br bb67(%116, %117, %118, %119, %121)
bb67(%122: ptr, %123: ptr, %124: ptr, %125: ptr, %126: bool):
    %1202 = load ptr, ptr %342
    call @func.43(%1202, %386)
    br bb68(%122, %123, %124, %125, %126)
bb68(%127: ptr, %128: ptr, %129: ptr, %130: ptr, %131: bool):
    %1203 = load ptr, ptr %130
    %1204 = const i64 16
    %1205 = gep i8, ptr %1203, %1204
    br bb69(%127, %128, %129, %1205, %131)
bb69(%132: ptr, %133: ptr, %134: ptr, %135: ptr, %136: bool):
    %1206 = load ptr, ptr %342
    call @func.45(%387, %132, %135, %1206)
    br bb70(%133, %134, %136)
bb70(%137: ptr, %138: ptr, %139: bool):
    %1207 = const bool true
    %1208 = load ptr, ptr %342
    call @func.44(%388, %1208)
    br bb71(%137, %138, %139)
bb71(%140: ptr, %141: ptr, %142: bool):
    br bb72(%140, %141, %142)
bb72(%143: ptr, %144: ptr, %145: bool):
    %1209 = const bool false
    %1210 = load i64, ptr %387
    store i64 %1210, ptr %391
    %1211 = const i64 8
    %1212 = gep i8, ptr %387, %1211
    %1213 = const i64 8
    %1214 = gep i8, ptr %391, %1213
    %1215 = load i64, ptr %1212
    store i64 %1215, ptr %1214
    %1216 = const i64 16
    %1217 = gep i8, ptr %387, %1216
    %1218 = const i64 16
    %1219 = gep i8, ptr %391, %1218
    %1220 = load i64, ptr %1217
    store i64 %1220, ptr %1219
    %1221 = const i64 24
    %1222 = gep i8, ptr %387, %1221
    %1223 = const i64 24
    %1224 = gep i8, ptr %391, %1223
    %1225 = load i64, ptr %1222
    store i64 %1225, ptr %1224
    %1226 = const i64 32
    %1227 = gep i8, ptr %387, %1226
    %1228 = const i64 32
    %1229 = gep i8, ptr %391, %1228
    %1230 = load i64, ptr %1227
    store i64 %1230, ptr %1229
    call @func.40(%390, %391)
    br bb73(%143, %144, %145)
bb73(%146: ptr, %147: ptr, %148: bool):
    %1231 = load i8, ptr %390
    %1232 = const i8 11
    %1233 = icmp eq i8 %1231, %1232
    %1234 = const i64 1
    %1235 = const i64 0
    %1236 = select i64 %1233, %1234, %1235
    switch %1236 [ 0: bb74(%146, %147) 1: bb75(%148) default: bb24 ]
bb74(%149: ptr, %150: ptr):
    %1237 = load i64, ptr %390
    store i64 %1237, ptr %393
    %1238 = const i64 8
    %1239 = gep i8, ptr %390, %1238
    %1240 = const i64 8
    %1241 = gep i8, ptr %393, %1240
    %1242 = load i64, ptr %1239
    store i64 %1242, ptr %1241
    %1243 = const i64 16
    %1244 = gep i8, ptr %390, %1243
    %1245 = const i64 16
    %1246 = gep i8, ptr %393, %1245
    %1247 = load i64, ptr %1244
    store i64 %1247, ptr %1246
    %1248 = const i64 24
    %1249 = gep i8, ptr %390, %1248
    %1250 = const i64 24
    %1251 = gep i8, ptr %393, %1250
    %1252 = load i64, ptr %1249
    store i64 %1252, ptr %1251
    %1253 = const i64 32
    %1254 = gep i8, ptr %390, %1253
    %1255 = const i64 32
    %1256 = gep i8, ptr %393, %1255
    %1257 = load i64, ptr %1254
    store i64 %1257, ptr %1256
    %1258 = const bool true
    %1259 = load i64, ptr %393
    store i64 %1259, ptr %389
    %1260 = const i64 8
    %1261 = gep i8, ptr %393, %1260
    %1262 = const i64 8
    %1263 = gep i8, ptr %389, %1262
    %1264 = load i64, ptr %1261
    store i64 %1264, ptr %1263
    %1265 = const i64 16
    %1266 = gep i8, ptr %393, %1265
    %1267 = const i64 16
    %1268 = gep i8, ptr %389, %1267
    %1269 = load i64, ptr %1266
    store i64 %1269, ptr %1268
    %1270 = const i64 24
    %1271 = gep i8, ptr %393, %1270
    %1272 = const i64 24
    %1273 = gep i8, ptr %389, %1272
    %1274 = load i64, ptr %1271
    store i64 %1274, ptr %1273
    %1275 = const i64 32
    %1276 = gep i8, ptr %393, %1275
    %1277 = const i64 32
    %1278 = gep i8, ptr %389, %1277
    %1279 = load i64, ptr %1276
    store i64 %1279, ptr %1278
    %1280 = load i8, ptr %149
    store i8 %1280, ptr %395
    %1281 = const i64 1
    %1282 = gep i8, ptr %149, %1281
    %1283 = const i64 1
    %1284 = gep i8, ptr %395, %1283
    %1285 = load i8, ptr %1282
    store i8 %1285, ptr %1284
    %1286 = call @func.42(%150)
    br bb77(%1286)
bb75(%151: bool):
    %1287 = const i64 8
    %1288 = gep i8, ptr %390, %1287
    %1289 = load i64, ptr %1288
    store i64 %1289, ptr %392
    %1290 = const i64 8
    %1291 = gep i8, ptr %1288, %1290
    %1292 = const i64 8
    %1293 = gep i8, ptr %392, %1292
    %1294 = load i64, ptr %1291
    store i64 %1294, ptr %1293
    %1295 = const i64 16
    %1296 = gep i8, ptr %1288, %1295
    %1297 = const i64 16
    %1298 = gep i8, ptr %392, %1297
    %1299 = load i64, ptr %1296
    store i64 %1299, ptr %1298
    call @func.41(%0, %392)
    br bb76(%151)
bb76(%152: bool):
    %1300 = const bool false
    %1301 = const bool false
    br bb165(%152)
bb77(%153: ptr):
    call @func.36(%396, %153)
    br bb78
bb78:
    %1302 = const bool false
    %1303 = load i64, ptr %389
    store i64 %1303, ptr %397
    %1304 = const i64 8
    %1305 = gep i8, ptr %389, %1304
    %1306 = const i64 8
    %1307 = gep i8, ptr %397, %1306
    %1308 = load i64, ptr %1305
    store i64 %1308, ptr %1307
    %1309 = const i64 16
    %1310 = gep i8, ptr %389, %1309
    %1311 = const i64 16
    %1312 = gep i8, ptr %397, %1311
    %1313 = load i64, ptr %1310
    store i64 %1313, ptr %1312
    %1314 = const i64 24
    %1315 = gep i8, ptr %389, %1314
    %1316 = const i64 24
    %1317 = gep i8, ptr %397, %1316
    %1318 = load i64, ptr %1315
    store i64 %1318, ptr %1317
    %1319 = const i64 32
    %1320 = gep i8, ptr %389, %1319
    %1321 = const i64 32
    %1322 = gep i8, ptr %397, %1321
    %1323 = load i64, ptr %1320
    store i64 %1323, ptr %1322
    call @func.66(%394, %395, %396, %397)
    br bb79
bb79:
    %1324 = load i64, ptr %394
    store i64 %1324, ptr %0
    %1325 = const i64 8
    %1326 = gep i8, ptr %394, %1325
    %1327 = const i64 8
    %1328 = gep i8, ptr %0, %1327
    %1329 = load i64, ptr %1326
    store i64 %1329, ptr %1328
    %1330 = const i64 16
    %1331 = gep i8, ptr %394, %1330
    %1332 = const i64 16
    %1333 = gep i8, ptr %0, %1332
    %1334 = load i64, ptr %1331
    store i64 %1334, ptr %1333
    %1335 = const i64 24
    %1336 = gep i8, ptr %394, %1335
    %1337 = const i64 24
    %1338 = gep i8, ptr %0, %1337
    %1339 = load i64, ptr %1336
    store i64 %1339, ptr %1338
    %1340 = const i64 32
    %1341 = gep i8, ptr %394, %1340
    %1342 = const i64 32
    %1343 = gep i8, ptr %0, %1342
    %1344 = load i64, ptr %1341
    store i64 %1344, ptr %1343
    %1345 = const bool false
    %1346 = const bool false
    br bb80
bb80:
    br bb81
bb81:
    %1347 = const bool false
    br bb171
bb82(%154: ptr, %155: ptr, %156: ptr, %157: ptr):
    %1348 = load ptr, ptr %342
    call @func.45(%400, %154, %157, %1348)
    br bb83(%154, %155, %156)
bb83(%158: ptr, %159: ptr, %160: ptr):
    call @func.40(%399, %400)
    br bb84(%158, %159, %160)
bb84(%161: ptr, %162: ptr, %163: ptr):
    %1349 = load i8, ptr %399
    %1350 = const i8 11
    %1351 = icmp eq i8 %1349, %1350
    %1352 = const i64 1
    %1353 = const i64 0
    %1354 = select i64 %1351, %1352, %1353
    switch %1354 [ 0: bb85(%161, %162, %163) 1: bb86 default: bb24 ]
bb85(%164: ptr, %165: ptr, %166: ptr):
    %1355 = load i64, ptr %399
    store i64 %1355, ptr %402
    %1356 = const i64 8
    %1357 = gep i8, ptr %399, %1356
    %1358 = const i64 8
    %1359 = gep i8, ptr %402, %1358
    %1360 = load i64, ptr %1357
    store i64 %1360, ptr %1359
    %1361 = const i64 16
    %1362 = gep i8, ptr %399, %1361
    %1363 = const i64 16
    %1364 = gep i8, ptr %402, %1363
    %1365 = load i64, ptr %1362
    store i64 %1365, ptr %1364
    %1366 = const i64 24
    %1367 = gep i8, ptr %399, %1366
    %1368 = const i64 24
    %1369 = gep i8, ptr %402, %1368
    %1370 = load i64, ptr %1367
    store i64 %1370, ptr %1369
    %1371 = const i64 32
    %1372 = gep i8, ptr %399, %1371
    %1373 = const i64 32
    %1374 = gep i8, ptr %402, %1373
    %1375 = load i64, ptr %1372
    store i64 %1375, ptr %1374
    %1376 = const bool true
    %1377 = load i64, ptr %402
    store i64 %1377, ptr %398
    %1378 = const i64 8
    %1379 = gep i8, ptr %402, %1378
    %1380 = const i64 8
    %1381 = gep i8, ptr %398, %1380
    %1382 = load i64, ptr %1379
    store i64 %1382, ptr %1381
    %1383 = const i64 16
    %1384 = gep i8, ptr %402, %1383
    %1385 = const i64 16
    %1386 = gep i8, ptr %398, %1385
    %1387 = load i64, ptr %1384
    store i64 %1387, ptr %1386
    %1388 = const i64 24
    %1389 = gep i8, ptr %402, %1388
    %1390 = const i64 24
    %1391 = gep i8, ptr %398, %1390
    %1392 = load i64, ptr %1389
    store i64 %1392, ptr %1391
    %1393 = const i64 32
    %1394 = gep i8, ptr %402, %1393
    %1395 = const i64 32
    %1396 = gep i8, ptr %398, %1395
    %1397 = load i64, ptr %1394
    store i64 %1397, ptr %1396
    call @func.46(%403, %164, %398)
    br bb87(%164, %165, %166, %1376)
bb86:
    %1398 = const i64 8
    %1399 = gep i8, ptr %399, %1398
    %1400 = load i64, ptr %1399
    store i64 %1400, ptr %401
    %1401 = const i64 8
    %1402 = gep i8, ptr %1399, %1401
    %1403 = const i64 8
    %1404 = gep i8, ptr %401, %1403
    %1405 = load i64, ptr %1402
    store i64 %1405, ptr %1404
    %1406 = const i64 16
    %1407 = gep i8, ptr %1399, %1406
    %1408 = const i64 16
    %1409 = gep i8, ptr %401, %1408
    %1410 = load i64, ptr %1407
    store i64 %1410, ptr %1409
    call @func.41(%0, %401)
    br bb164
bb87(%167: ptr, %168: ptr, %169: ptr, %170: bool):
    store ptr %403, ptr %405
    %1411 = load ptr, ptr %405
    %1412 = load i8, ptr %1411
    %1413 = sext i8 %1412 to i64
    switch %1413 [ 2: bb89(%167, %168, %169, %170) default: bb88 ]
bb88:
    %1414 = const bool false
    %1415 = load i64, ptr %398
    store i64 %1415, ptr %408
    %1416 = const i64 8
    %1417 = gep i8, ptr %398, %1416
    %1418 = const i64 8
    %1419 = gep i8, ptr %408, %1418
    %1420 = load i64, ptr %1417
    store i64 %1420, ptr %1419
    %1421 = const i64 16
    %1422 = gep i8, ptr %398, %1421
    %1423 = const i64 16
    %1424 = gep i8, ptr %408, %1423
    %1425 = load i64, ptr %1422
    store i64 %1425, ptr %1424
    %1426 = const i64 24
    %1427 = gep i8, ptr %398, %1426
    %1428 = const i64 24
    %1429 = gep i8, ptr %408, %1428
    %1430 = load i64, ptr %1427
    store i64 %1430, ptr %1429
    %1431 = const i64 32
    %1432 = gep i8, ptr %398, %1431
    %1433 = const i64 32
    %1434 = gep i8, ptr %408, %1433
    %1435 = load i64, ptr %1432
    store i64 %1435, ptr %1434
    %1436 = const i64 56
    %1437 = heap_alloc rust_heap i8, %1436, align 8
    %1438 = const u64 1
    store u64 %1438, ptr %1437
    %1439 = const i64 8
    %1440 = gep i8, ptr %1437, %1439
    %1441 = const u64 1
    store u64 %1441, ptr %1440
    %1442 = const i64 16
    %1443 = gep i8, ptr %1437, %1442
    %1444 = load i64, ptr %408
    store i64 %1444, ptr %1443
    %1445 = const i64 8
    %1446 = gep i8, ptr %408, %1445
    %1447 = const i64 8
    %1448 = gep i8, ptr %1443, %1447
    %1449 = load i64, ptr %1446
    store i64 %1449, ptr %1448
    %1450 = const i64 16
    %1451 = gep i8, ptr %408, %1450
    %1452 = const i64 16
    %1453 = gep i8, ptr %1443, %1452
    %1454 = load i64, ptr %1451
    store i64 %1454, ptr %1453
    %1455 = const i64 24
    %1456 = gep i8, ptr %408, %1455
    %1457 = const i64 24
    %1458 = gep i8, ptr %1443, %1457
    %1459 = load i64, ptr %1456
    store i64 %1459, ptr %1458
    %1460 = const i64 32
    %1461 = gep i8, ptr %408, %1460
    %1462 = const i64 32
    %1463 = gep i8, ptr %1443, %1462
    %1464 = load i64, ptr %1461
    store i64 %1464, ptr %1463
    store ptr %1437, ptr %407
    br bb91(%1414)
bb89(%171: ptr, %172: ptr, %173: ptr, %174: bool):
    %1465 = load ptr, ptr %405
    %1466 = const i64 8
    %1467 = gep i8, ptr %1465, %1466
    call @func.48(%404, %1467)
    br bb90(%171, %172, %173, %174)
bb90(%175: ptr, %176: ptr, %177: ptr, %178: bool):
    %1468 = const bool true
    %1469 = call @func.42(%176)
    br bb92(%175, %177, %1469, %178)
bb91(%179: bool):
    %1470 = load ptr, ptr %407
    %1471 = const i64 8
    %1472 = gep i8, ptr %406, %1471
    store ptr %1470, ptr %1472
    %1473 = const i32 4
    store i32 %1473, ptr %406
    %1474 = const i64 8
    %1475 = gep i8, ptr %0, %1474
    %1476 = load i64, ptr %406
    store i64 %1476, ptr %1475
    %1477 = const i64 8
    %1478 = gep i8, ptr %406, %1477
    %1479 = const i64 8
    %1480 = gep i8, ptr %1475, %1479
    %1481 = load i64, ptr %1478
    store i64 %1481, ptr %1480
    %1482 = const i64 16
    %1483 = gep i8, ptr %406, %1482
    %1484 = const i64 16
    %1485 = gep i8, ptr %1475, %1484
    %1486 = load i64, ptr %1483
    store i64 %1486, ptr %1485
    %1487 = const i8 11
    store i8 %1487, ptr %0
    br bb162(%179)
bb92(%180: ptr, %181: ptr, %182: ptr, %183: bool):
    call @func.36(%409, %182)
    br bb93(%180, %181, %183)
bb93(%184: ptr, %185: ptr, %186: bool):
    %1488 = load ptr, ptr %342
    call @func.43(%1488, %409)
    br bb94(%184, %185, %186)
bb94(%187: ptr, %188: ptr, %189: bool):
    %1489 = load ptr, ptr %188
    %1490 = const i64 16
    %1491 = gep i8, ptr %1489, %1490
    br bb95(%187, %1491, %189)
bb95(%190: ptr, %191: ptr, %192: bool):
    %1492 = load ptr, ptr %342
    call @func.45(%410, %190, %191, %1492)
    br bb96(%190, %192)
bb96(%193: ptr, %194: bool):
    %1493 = const bool true
    %1494 = load ptr, ptr %342
    call @func.44(%411, %1494)
    br bb97(%193, %194)
bb97(%195: ptr, %196: bool):
    br bb98(%195, %196)
bb98(%197: ptr, %198: bool):
    %1495 = const bool false
    %1496 = load i64, ptr %410
    store i64 %1496, ptr %414
    %1497 = const i64 8
    %1498 = gep i8, ptr %410, %1497
    %1499 = const i64 8
    %1500 = gep i8, ptr %414, %1499
    %1501 = load i64, ptr %1498
    store i64 %1501, ptr %1500
    %1502 = const i64 16
    %1503 = gep i8, ptr %410, %1502
    %1504 = const i64 16
    %1505 = gep i8, ptr %414, %1504
    %1506 = load i64, ptr %1503
    store i64 %1506, ptr %1505
    %1507 = const i64 24
    %1508 = gep i8, ptr %410, %1507
    %1509 = const i64 24
    %1510 = gep i8, ptr %414, %1509
    %1511 = load i64, ptr %1508
    store i64 %1511, ptr %1510
    %1512 = const i64 32
    %1513 = gep i8, ptr %410, %1512
    %1514 = const i64 32
    %1515 = gep i8, ptr %414, %1514
    %1516 = load i64, ptr %1513
    store i64 %1516, ptr %1515
    call @func.40(%413, %414)
    br bb99(%197, %198)
bb99(%199: ptr, %200: bool):
    %1517 = load i8, ptr %413
    %1518 = const i8 11
    %1519 = icmp eq i8 %1517, %1518
    %1520 = const i64 1
    %1521 = const i64 0
    %1522 = select i64 %1519, %1520, %1521
    switch %1522 [ 0: bb100(%199, %200) 1: bb101(%200) default: bb24 ]
bb100(%201: ptr, %202: bool):
    %1523 = load i64, ptr %413
    store i64 %1523, ptr %416
    %1524 = const i64 8
    %1525 = gep i8, ptr %413, %1524
    %1526 = const i64 8
    %1527 = gep i8, ptr %416, %1526
    %1528 = load i64, ptr %1525
    store i64 %1528, ptr %1527
    %1529 = const i64 16
    %1530 = gep i8, ptr %413, %1529
    %1531 = const i64 16
    %1532 = gep i8, ptr %416, %1531
    %1533 = load i64, ptr %1530
    store i64 %1533, ptr %1532
    %1534 = const i64 24
    %1535 = gep i8, ptr %413, %1534
    %1536 = const i64 24
    %1537 = gep i8, ptr %416, %1536
    %1538 = load i64, ptr %1535
    store i64 %1538, ptr %1537
    %1539 = const i64 32
    %1540 = gep i8, ptr %413, %1539
    %1541 = const i64 32
    %1542 = gep i8, ptr %416, %1541
    %1543 = load i64, ptr %1540
    store i64 %1543, ptr %1542
    %1544 = const bool true
    %1545 = load i64, ptr %416
    store i64 %1545, ptr %412
    %1546 = const i64 8
    %1547 = gep i8, ptr %416, %1546
    %1548 = const i64 8
    %1549 = gep i8, ptr %412, %1548
    %1550 = load i64, ptr %1547
    store i64 %1550, ptr %1549
    %1551 = const i64 16
    %1552 = gep i8, ptr %416, %1551
    %1553 = const i64 16
    %1554 = gep i8, ptr %412, %1553
    %1555 = load i64, ptr %1552
    store i64 %1555, ptr %1554
    %1556 = const i64 24
    %1557 = gep i8, ptr %416, %1556
    %1558 = const i64 24
    %1559 = gep i8, ptr %412, %1558
    %1560 = load i64, ptr %1557
    store i64 %1560, ptr %1559
    %1561 = const i64 32
    %1562 = gep i8, ptr %416, %1561
    %1563 = const i64 32
    %1564 = gep i8, ptr %412, %1563
    %1565 = load i64, ptr %1562
    store i64 %1565, ptr %1564
    call @func.46(%417, %201, %412)
    br bb102(%202)
bb101(%203: bool):
    %1566 = const i64 8
    %1567 = gep i8, ptr %413, %1566
    %1568 = load i64, ptr %1567
    store i64 %1568, ptr %415
    %1569 = const i64 8
    %1570 = gep i8, ptr %1567, %1569
    %1571 = const i64 8
    %1572 = gep i8, ptr %415, %1571
    %1573 = load i64, ptr %1570
    store i64 %1573, ptr %1572
    %1574 = const i64 16
    %1575 = gep i8, ptr %1567, %1574
    %1576 = const i64 16
    %1577 = gep i8, ptr %415, %1576
    %1578 = load i64, ptr %1575
    store i64 %1578, ptr %1577
    call @func.41(%0, %415)
    br bb178(%203)
bb102(%204: bool):
    store ptr %417, ptr %419
    %1579 = load ptr, ptr %419
    %1580 = load i8, ptr %1579
    %1581 = sext i8 %1580 to i64
    switch %1581 [ 2: bb104 default: bb103(%204) ]
bb103(%205: bool):
    %1582 = const bool false
    %1583 = load i64, ptr %412
    store i64 %1583, ptr %422
    %1584 = const i64 8
    %1585 = gep i8, ptr %412, %1584
    %1586 = const i64 8
    %1587 = gep i8, ptr %422, %1586
    %1588 = load i64, ptr %1585
    store i64 %1588, ptr %1587
    %1589 = const i64 16
    %1590 = gep i8, ptr %412, %1589
    %1591 = const i64 16
    %1592 = gep i8, ptr %422, %1591
    %1593 = load i64, ptr %1590
    store i64 %1593, ptr %1592
    %1594 = const i64 24
    %1595 = gep i8, ptr %412, %1594
    %1596 = const i64 24
    %1597 = gep i8, ptr %422, %1596
    %1598 = load i64, ptr %1595
    store i64 %1598, ptr %1597
    %1599 = const i64 32
    %1600 = gep i8, ptr %412, %1599
    %1601 = const i64 32
    %1602 = gep i8, ptr %422, %1601
    %1603 = load i64, ptr %1600
    store i64 %1603, ptr %1602
    %1604 = const i64 56
    %1605 = heap_alloc rust_heap i8, %1604, align 8
    %1606 = const u64 1
    store u64 %1606, ptr %1605
    %1607 = const i64 8
    %1608 = gep i8, ptr %1605, %1607
    %1609 = const u64 1
    store u64 %1609, ptr %1608
    %1610 = const i64 16
    %1611 = gep i8, ptr %1605, %1610
    %1612 = load i64, ptr %422
    store i64 %1612, ptr %1611
    %1613 = const i64 8
    %1614 = gep i8, ptr %422, %1613
    %1615 = const i64 8
    %1616 = gep i8, ptr %1611, %1615
    %1617 = load i64, ptr %1614
    store i64 %1617, ptr %1616
    %1618 = const i64 16
    %1619 = gep i8, ptr %422, %1618
    %1620 = const i64 16
    %1621 = gep i8, ptr %1611, %1620
    %1622 = load i64, ptr %1619
    store i64 %1622, ptr %1621
    %1623 = const i64 24
    %1624 = gep i8, ptr %422, %1623
    %1625 = const i64 24
    %1626 = gep i8, ptr %1611, %1625
    %1627 = load i64, ptr %1624
    store i64 %1627, ptr %1626
    %1628 = const i64 32
    %1629 = gep i8, ptr %422, %1628
    %1630 = const i64 32
    %1631 = gep i8, ptr %1611, %1630
    %1632 = load i64, ptr %1629
    store i64 %1632, ptr %1631
    store ptr %1605, ptr %421
    br bb106(%205)
bb104:
    %1633 = load ptr, ptr %419
    %1634 = const i64 8
    %1635 = gep i8, ptr %1633, %1634
    call @func.48(%418, %1635)
    br bb105
bb105:
    %1636 = const bool false
    %1637 = load i64, ptr %404
    store i64 %1637, ptr %425
    %1638 = const i64 8
    %1639 = gep i8, ptr %404, %1638
    %1640 = const i64 8
    %1641 = gep i8, ptr %425, %1640
    %1642 = load i64, ptr %1639
    store i64 %1642, ptr %1641
    %1643 = const i64 16
    %1644 = gep i8, ptr %404, %1643
    %1645 = const i64 16
    %1646 = gep i8, ptr %425, %1645
    %1647 = load i64, ptr %1644
    store i64 %1647, ptr %1646
    call @func.49(%424, %425, %418)
    br bb107
bb106(%206: bool):
    %1648 = load ptr, ptr %421
    %1649 = const i64 8
    %1650 = gep i8, ptr %420, %1649
    store ptr %1648, ptr %1650
    %1651 = const i32 4
    store i32 %1651, ptr %420
    %1652 = const i64 8
    %1653 = gep i8, ptr %0, %1652
    %1654 = load i64, ptr %420
    store i64 %1654, ptr %1653
    %1655 = const i64 8
    %1656 = gep i8, ptr %420, %1655
    %1657 = const i64 8
    %1658 = gep i8, ptr %1653, %1657
    %1659 = load i64, ptr %1656
    store i64 %1659, ptr %1658
    %1660 = const i64 16
    %1661 = gep i8, ptr %420, %1660
    %1662 = const i64 16
    %1663 = gep i8, ptr %1653, %1662
    %1664 = load i64, ptr %1661
    store i64 %1664, ptr %1663
    %1665 = const i8 11
    store i8 %1665, ptr %0
    br bb161(%206)
bb107:
    call @func.62(%423, %424)
    br bb108
bb108:
    %1666 = load i64, ptr %423
    store i64 %1666, ptr %0
    %1667 = const i64 8
    %1668 = gep i8, ptr %423, %1667
    %1669 = const i64 8
    %1670 = gep i8, ptr %0, %1669
    %1671 = load i64, ptr %1668
    store i64 %1671, ptr %1670
    %1672 = const i64 16
    %1673 = gep i8, ptr %423, %1672
    %1674 = const i64 16
    %1675 = gep i8, ptr %0, %1674
    %1676 = load i64, ptr %1673
    store i64 %1676, ptr %1675
    %1677 = const i64 24
    %1678 = gep i8, ptr %423, %1677
    %1679 = const i64 24
    %1680 = gep i8, ptr %0, %1679
    %1681 = load i64, ptr %1678
    store i64 %1681, ptr %1680
    %1682 = const i64 32
    %1683 = gep i8, ptr %423, %1682
    %1684 = const i64 32
    %1685 = gep i8, ptr %0, %1684
    %1686 = load i64, ptr %1683
    store i64 %1686, ptr %1685
    br bb109
bb109:
    br bb110
bb110:
    %1687 = const bool false
    %1688 = const bool false
    %1689 = const bool false
    br bb111
bb111:
    br bb112
bb112:
    %1690 = const bool false
    br bb171
bb113(%207: ptr, %208: ptr, %209: ptr, %210: ptr, %211: ptr):
    %1691 = load ptr, ptr %342
    call @func.45(%428, %207, %211, %1691)
    br bb114(%207, %208, %209, %210)
bb114(%212: ptr, %213: ptr, %214: ptr, %215: ptr):
    call @func.40(%427, %428)
    br bb115(%212, %213, %214, %215)
bb115(%216: ptr, %217: ptr, %218: ptr, %219: ptr):
    %1692 = load i8, ptr %427
    %1693 = const i8 11
    %1694 = icmp eq i8 %1692, %1693
    %1695 = const i64 1
    %1696 = const i64 0
    %1697 = select i64 %1694, %1695, %1696
    switch %1697 [ 0: bb116(%216, %217, %218, %219) 1: bb117 default: bb24 ]
bb116(%220: ptr, %221: ptr, %222: ptr, %223: ptr):
    %1698 = load i64, ptr %427
    store i64 %1698, ptr %430
    %1699 = const i64 8
    %1700 = gep i8, ptr %427, %1699
    %1701 = const i64 8
    %1702 = gep i8, ptr %430, %1701
    %1703 = load i64, ptr %1700
    store i64 %1703, ptr %1702
    %1704 = const i64 16
    %1705 = gep i8, ptr %427, %1704
    %1706 = const i64 16
    %1707 = gep i8, ptr %430, %1706
    %1708 = load i64, ptr %1705
    store i64 %1708, ptr %1707
    %1709 = const i64 24
    %1710 = gep i8, ptr %427, %1709
    %1711 = const i64 24
    %1712 = gep i8, ptr %430, %1711
    %1713 = load i64, ptr %1710
    store i64 %1713, ptr %1712
    %1714 = const i64 32
    %1715 = gep i8, ptr %427, %1714
    %1716 = const i64 32
    %1717 = gep i8, ptr %430, %1716
    %1718 = load i64, ptr %1715
    store i64 %1718, ptr %1717
    %1719 = const bool true
    %1720 = load i64, ptr %430
    store i64 %1720, ptr %426
    %1721 = const i64 8
    %1722 = gep i8, ptr %430, %1721
    %1723 = const i64 8
    %1724 = gep i8, ptr %426, %1723
    %1725 = load i64, ptr %1722
    store i64 %1725, ptr %1724
    %1726 = const i64 16
    %1727 = gep i8, ptr %430, %1726
    %1728 = const i64 16
    %1729 = gep i8, ptr %426, %1728
    %1730 = load i64, ptr %1727
    store i64 %1730, ptr %1729
    %1731 = const i64 24
    %1732 = gep i8, ptr %430, %1731
    %1733 = const i64 24
    %1734 = gep i8, ptr %426, %1733
    %1735 = load i64, ptr %1732
    store i64 %1735, ptr %1734
    %1736 = const i64 32
    %1737 = gep i8, ptr %430, %1736
    %1738 = const i64 32
    %1739 = gep i8, ptr %426, %1738
    %1740 = load i64, ptr %1737
    store i64 %1740, ptr %1739
    call @func.46(%431, %220, %426)
    br bb118(%220, %221, %222, %223, %1719)
bb117:
    %1741 = const i64 8
    %1742 = gep i8, ptr %427, %1741
    %1743 = load i64, ptr %1742
    store i64 %1743, ptr %429
    %1744 = const i64 8
    %1745 = gep i8, ptr %1742, %1744
    %1746 = const i64 8
    %1747 = gep i8, ptr %429, %1746
    %1748 = load i64, ptr %1745
    store i64 %1748, ptr %1747
    %1749 = const i64 16
    %1750 = gep i8, ptr %1742, %1749
    %1751 = const i64 16
    %1752 = gep i8, ptr %429, %1751
    %1753 = load i64, ptr %1750
    store i64 %1753, ptr %1752
    call @func.41(%0, %429)
    br bb160
bb118(%224: ptr, %225: ptr, %226: ptr, %227: ptr, %228: bool):
    %1754 = load i8, ptr %431
    %1755 = sext i8 %1754 to i64
    switch %1755 [ 2: bb120(%224, %225, %226, %227, %228) default: bb119 ]
bb119:
    %1756 = const bool false
    %1757 = load i64, ptr %426
    store i64 %1757, ptr %434
    %1758 = const i64 8
    %1759 = gep i8, ptr %426, %1758
    %1760 = const i64 8
    %1761 = gep i8, ptr %434, %1760
    %1762 = load i64, ptr %1759
    store i64 %1762, ptr %1761
    %1763 = const i64 16
    %1764 = gep i8, ptr %426, %1763
    %1765 = const i64 16
    %1766 = gep i8, ptr %434, %1765
    %1767 = load i64, ptr %1764
    store i64 %1767, ptr %1766
    %1768 = const i64 24
    %1769 = gep i8, ptr %426, %1768
    %1770 = const i64 24
    %1771 = gep i8, ptr %434, %1770
    %1772 = load i64, ptr %1769
    store i64 %1772, ptr %1771
    %1773 = const i64 32
    %1774 = gep i8, ptr %426, %1773
    %1775 = const i64 32
    %1776 = gep i8, ptr %434, %1775
    %1777 = load i64, ptr %1774
    store i64 %1777, ptr %1776
    %1778 = const i64 56
    %1779 = heap_alloc rust_heap i8, %1778, align 8
    %1780 = const u64 1
    store u64 %1780, ptr %1779
    %1781 = const i64 8
    %1782 = gep i8, ptr %1779, %1781
    %1783 = const u64 1
    store u64 %1783, ptr %1782
    %1784 = const i64 16
    %1785 = gep i8, ptr %1779, %1784
    %1786 = load i64, ptr %434
    store i64 %1786, ptr %1785
    %1787 = const i64 8
    %1788 = gep i8, ptr %434, %1787
    %1789 = const i64 8
    %1790 = gep i8, ptr %1785, %1789
    %1791 = load i64, ptr %1788
    store i64 %1791, ptr %1790
    %1792 = const i64 16
    %1793 = gep i8, ptr %434, %1792
    %1794 = const i64 16
    %1795 = gep i8, ptr %1785, %1794
    %1796 = load i64, ptr %1793
    store i64 %1796, ptr %1795
    %1797 = const i64 24
    %1798 = gep i8, ptr %434, %1797
    %1799 = const i64 24
    %1800 = gep i8, ptr %1785, %1799
    %1801 = load i64, ptr %1798
    store i64 %1801, ptr %1800
    %1802 = const i64 32
    %1803 = gep i8, ptr %434, %1802
    %1804 = const i64 32
    %1805 = gep i8, ptr %1785, %1804
    %1806 = load i64, ptr %1803
    store i64 %1806, ptr %1805
    store ptr %1779, ptr %433
    br bb121(%1756)
bb120(%229: ptr, %230: ptr, %231: ptr, %232: ptr, %233: bool):
    %1807 = load ptr, ptr %231
    %1808 = const i64 16
    %1809 = gep i8, ptr %1807, %1808
    br bb122(%229, %230, %231, %232, %1809, %233)
bb121(%234: bool):
    %1810 = load ptr, ptr %433
    %1811 = const i64 8
    %1812 = gep i8, ptr %432, %1811
    store ptr %1810, ptr %1812
    %1813 = const i32 4
    store i32 %1813, ptr %432
    %1814 = const i64 8
    %1815 = gep i8, ptr %0, %1814
    %1816 = load i64, ptr %432
    store i64 %1816, ptr %1815
    %1817 = const i64 8
    %1818 = gep i8, ptr %432, %1817
    %1819 = const i64 8
    %1820 = gep i8, ptr %1815, %1819
    %1821 = load i64, ptr %1818
    store i64 %1821, ptr %1820
    %1822 = const i64 16
    %1823 = gep i8, ptr %432, %1822
    %1824 = const i64 16
    %1825 = gep i8, ptr %1815, %1824
    %1826 = load i64, ptr %1823
    store i64 %1826, ptr %1825
    %1827 = const i8 11
    store i8 %1827, ptr %0
    br bb158(%234)
bb122(%235: ptr, %236: ptr, %237: ptr, %238: ptr, %239: ptr, %240: bool):
    %1828 = load ptr, ptr %342
    call @func.45(%437, %235, %239, %1828)
    br bb123(%235, %236, %237, %238, %240)
bb123(%241: ptr, %242: ptr, %243: ptr, %244: ptr, %245: bool):
    call @func.40(%436, %437)
    br bb124(%241, %242, %243, %244, %245)
bb124(%246: ptr, %247: ptr, %248: ptr, %249: ptr, %250: bool):
    %1829 = load i8, ptr %436
    %1830 = const i8 11
    %1831 = icmp eq i8 %1829, %1830
    %1832 = const i64 1
    %1833 = const i64 0
    %1834 = select i64 %1831, %1832, %1833
    switch %1834 [ 0: bb125(%246, %247, %248, %249, %250) 1: bb126(%250) default: bb24 ]
bb125(%251: ptr, %252: ptr, %253: ptr, %254: ptr, %255: bool):
    %1835 = load i64, ptr %436
    store i64 %1835, ptr %439
    %1836 = const i64 8
    %1837 = gep i8, ptr %436, %1836
    %1838 = const i64 8
    %1839 = gep i8, ptr %439, %1838
    %1840 = load i64, ptr %1837
    store i64 %1840, ptr %1839
    %1841 = const i64 16
    %1842 = gep i8, ptr %436, %1841
    %1843 = const i64 16
    %1844 = gep i8, ptr %439, %1843
    %1845 = load i64, ptr %1842
    store i64 %1845, ptr %1844
    %1846 = const i64 24
    %1847 = gep i8, ptr %436, %1846
    %1848 = const i64 24
    %1849 = gep i8, ptr %439, %1848
    %1850 = load i64, ptr %1847
    store i64 %1850, ptr %1849
    %1851 = const i64 32
    %1852 = gep i8, ptr %436, %1851
    %1853 = const i64 32
    %1854 = gep i8, ptr %439, %1853
    %1855 = load i64, ptr %1852
    store i64 %1855, ptr %1854
    %1856 = const bool true
    %1857 = load i64, ptr %439
    store i64 %1857, ptr %435
    %1858 = const i64 8
    %1859 = gep i8, ptr %439, %1858
    %1860 = const i64 8
    %1861 = gep i8, ptr %435, %1860
    %1862 = load i64, ptr %1859
    store i64 %1862, ptr %1861
    %1863 = const i64 16
    %1864 = gep i8, ptr %439, %1863
    %1865 = const i64 16
    %1866 = gep i8, ptr %435, %1865
    %1867 = load i64, ptr %1864
    store i64 %1867, ptr %1866
    %1868 = const i64 24
    %1869 = gep i8, ptr %439, %1868
    %1870 = const i64 24
    %1871 = gep i8, ptr %435, %1870
    %1872 = load i64, ptr %1869
    store i64 %1872, ptr %1871
    %1873 = const i64 32
    %1874 = gep i8, ptr %439, %1873
    %1875 = const i64 32
    %1876 = gep i8, ptr %435, %1875
    %1877 = load i64, ptr %1874
    store i64 %1877, ptr %1876
    %1878 = load ptr, ptr %252
    %1879 = const i64 16
    %1880 = gep i8, ptr %1878, %1879
    br bb127(%251, %252, %253, %254, %435, %1880, %1856, %255)
bb126(%256: bool):
    %1881 = const i64 8
    %1882 = gep i8, ptr %436, %1881
    %1883 = load i64, ptr %1882
    store i64 %1883, ptr %438
    %1884 = const i64 8
    %1885 = gep i8, ptr %1882, %1884
    %1886 = const i64 8
    %1887 = gep i8, ptr %438, %1886
    %1888 = load i64, ptr %1885
    store i64 %1888, ptr %1887
    %1889 = const i64 16
    %1890 = gep i8, ptr %1882, %1889
    %1891 = const i64 16
    %1892 = gep i8, ptr %438, %1891
    %1893 = load i64, ptr %1890
    store i64 %1893, ptr %1892
    call @func.41(%0, %438)
    br bb179(%256)
bb127(%257: ptr, %258: ptr, %259: ptr, %260: ptr, %261: ptr, %262: ptr, %263: bool, %264: bool):
    %1894 = call @func.35(%257, %261, %262)
    br bb128(%257, %258, %259, %260, %1894, %263, %264)
bb128(%265: ptr, %266: ptr, %267: ptr, %268: ptr, %269: bool, %270: bool, %271: bool):
    condbr %269, bb129(%265, %266, %267, %268, %270, %271), bb130(%266, %271)
bb129(%272: ptr, %273: ptr, %274: ptr, %275: ptr, %276: bool, %277: bool):
    %1895 = call @func.42(%273)
    br bb135(%272, %274, %275, %1895, %276, %277)
bb130(%278: ptr, %279: bool):
    %1896 = call @func.42(%278)
    br bb131(%1896, %279)
bb131(%280: ptr, %281: bool):
    call @func.36(%442, %280)
    br bb132(%281)
bb132(%282: bool):
    %1897 = const i64 56
    %1898 = heap_alloc rust_heap i8, %1897, align 8
    %1899 = const u64 1
    store u64 %1899, ptr %1898
    %1900 = const i64 8
    %1901 = gep i8, ptr %1898, %1900
    %1902 = const u64 1
    store u64 %1902, ptr %1901
    %1903 = const i64 16
    %1904 = gep i8, ptr %1898, %1903
    %1905 = load i64, ptr %442
    store i64 %1905, ptr %1904
    %1906 = const i64 8
    %1907 = gep i8, ptr %442, %1906
    %1908 = const i64 8
    %1909 = gep i8, ptr %1904, %1908
    %1910 = load i64, ptr %1907
    store i64 %1910, ptr %1909
    %1911 = const i64 16
    %1912 = gep i8, ptr %442, %1911
    %1913 = const i64 16
    %1914 = gep i8, ptr %1904, %1913
    %1915 = load i64, ptr %1912
    store i64 %1915, ptr %1914
    %1916 = const i64 24
    %1917 = gep i8, ptr %442, %1916
    %1918 = const i64 24
    %1919 = gep i8, ptr %1904, %1918
    %1920 = load i64, ptr %1917
    store i64 %1920, ptr %1919
    %1921 = const i64 32
    %1922 = gep i8, ptr %442, %1921
    %1923 = const i64 32
    %1924 = gep i8, ptr %1904, %1923
    %1925 = load i64, ptr %1922
    store i64 %1925, ptr %1924
    store ptr %1898, ptr %441
    br bb133(%282)
bb133(%283: bool):
    %1926 = const bool false
    %1927 = load i64, ptr %435
    store i64 %1927, ptr %444
    %1928 = const i64 8
    %1929 = gep i8, ptr %435, %1928
    %1930 = const i64 8
    %1931 = gep i8, ptr %444, %1930
    %1932 = load i64, ptr %1929
    store i64 %1932, ptr %1931
    %1933 = const i64 16
    %1934 = gep i8, ptr %435, %1933
    %1935 = const i64 16
    %1936 = gep i8, ptr %444, %1935
    %1937 = load i64, ptr %1934
    store i64 %1937, ptr %1936
    %1938 = const i64 24
    %1939 = gep i8, ptr %435, %1938
    %1940 = const i64 24
    %1941 = gep i8, ptr %444, %1940
    %1942 = load i64, ptr %1939
    store i64 %1942, ptr %1941
    %1943 = const i64 32
    %1944 = gep i8, ptr %435, %1943
    %1945 = const i64 32
    %1946 = gep i8, ptr %444, %1945
    %1947 = load i64, ptr %1944
    store i64 %1947, ptr %1946
    %1948 = const i64 56
    %1949 = heap_alloc rust_heap i8, %1948, align 8
    %1950 = const u64 1
    store u64 %1950, ptr %1949
    %1951 = const i64 8
    %1952 = gep i8, ptr %1949, %1951
    %1953 = const u64 1
    store u64 %1953, ptr %1952
    %1954 = const i64 16
    %1955 = gep i8, ptr %1949, %1954
    %1956 = load i64, ptr %444
    store i64 %1956, ptr %1955
    %1957 = const i64 8
    %1958 = gep i8, ptr %444, %1957
    %1959 = const i64 8
    %1960 = gep i8, ptr %1955, %1959
    %1961 = load i64, ptr %1958
    store i64 %1961, ptr %1960
    %1962 = const i64 16
    %1963 = gep i8, ptr %444, %1962
    %1964 = const i64 16
    %1965 = gep i8, ptr %1955, %1964
    %1966 = load i64, ptr %1963
    store i64 %1966, ptr %1965
    %1967 = const i64 24
    %1968 = gep i8, ptr %444, %1967
    %1969 = const i64 24
    %1970 = gep i8, ptr %1955, %1969
    %1971 = load i64, ptr %1968
    store i64 %1971, ptr %1970
    %1972 = const i64 32
    %1973 = gep i8, ptr %444, %1972
    %1974 = const i64 32
    %1975 = gep i8, ptr %1955, %1974
    %1976 = load i64, ptr %1973
    store i64 %1976, ptr %1975
    store ptr %1949, ptr %443
    br bb134(%1926, %283)
bb134(%284: bool, %285: bool):
    %1977 = load ptr, ptr %441
    %1978 = const i64 8
    %1979 = gep i8, ptr %440, %1978
    store ptr %1977, ptr %1979
    %1980 = load ptr, ptr %443
    %1981 = const i64 16
    %1982 = gep i8, ptr %440, %1981
    store ptr %1980, ptr %1982
    %1983 = const i32 2
    store i32 %1983, ptr %440
    %1984 = const i64 8
    %1985 = gep i8, ptr %0, %1984
    %1986 = load i64, ptr %440
    store i64 %1986, ptr %1985
    %1987 = const i64 8
    %1988 = gep i8, ptr %440, %1987
    %1989 = const i64 8
    %1990 = gep i8, ptr %1985, %1989
    %1991 = load i64, ptr %1988
    store i64 %1991, ptr %1990
    %1992 = const i64 16
    %1993 = gep i8, ptr %440, %1992
    %1994 = const i64 16
    %1995 = gep i8, ptr %1985, %1994
    %1996 = load i64, ptr %1993
    store i64 %1996, ptr %1995
    %1997 = const i8 11
    store i8 %1997, ptr %0
    br bb156(%284, %285)
bb135(%286: ptr, %287: ptr, %288: ptr, %289: ptr, %290: bool, %291: bool):
    call @func.36(%445, %289)
    br bb136(%286, %287, %288, %290, %291)
bb136(%292: ptr, %293: ptr, %294: ptr, %295: bool, %296: bool):
    %1998 = load ptr, ptr %342
    call @func.43(%1998, %445)
    br bb137(%292, %293, %294, %295, %296)
bb137(%297: ptr, %298: ptr, %299: ptr, %300: bool, %301: bool):
    %1999 = load ptr, ptr %299
    %2000 = const i64 16
    %2001 = gep i8, ptr %1999, %2000
    br bb138(%297, %298, %2001, %300, %301)
bb138(%302: ptr, %303: ptr, %304: ptr, %305: bool, %306: bool):
    %2002 = load ptr, ptr %342
    call @func.45(%446, %302, %304, %2002)
    br bb139(%303, %305, %306)
bb139(%307: ptr, %308: bool, %309: bool):
    %2003 = const bool true
    %2004 = load ptr, ptr %342
    call @func.44(%447, %2004)
    br bb140(%307, %308, %309)
bb140(%310: ptr, %311: bool, %312: bool):
    br bb141(%310, %311, %312)
bb141(%313: ptr, %314: bool, %315: bool):
    %2005 = const bool false
    %2006 = load i64, ptr %446
    store i64 %2006, ptr %450
    %2007 = const i64 8
    %2008 = gep i8, ptr %446, %2007
    %2009 = const i64 8
    %2010 = gep i8, ptr %450, %2009
    %2011 = load i64, ptr %2008
    store i64 %2011, ptr %2010
    %2012 = const i64 16
    %2013 = gep i8, ptr %446, %2012
    %2014 = const i64 16
    %2015 = gep i8, ptr %450, %2014
    %2016 = load i64, ptr %2013
    store i64 %2016, ptr %2015
    %2017 = const i64 24
    %2018 = gep i8, ptr %446, %2017
    %2019 = const i64 24
    %2020 = gep i8, ptr %450, %2019
    %2021 = load i64, ptr %2018
    store i64 %2021, ptr %2020
    %2022 = const i64 32
    %2023 = gep i8, ptr %446, %2022
    %2024 = const i64 32
    %2025 = gep i8, ptr %450, %2024
    %2026 = load i64, ptr %2023
    store i64 %2026, ptr %2025
    call @func.40(%449, %450)
    br bb142(%313, %314, %315)
bb142(%316: ptr, %317: bool, %318: bool):
    %2027 = load i8, ptr %449
    %2028 = const i8 11
    %2029 = icmp eq i8 %2027, %2028
    %2030 = const i64 1
    %2031 = const i64 0
    %2032 = select i64 %2029, %2030, %2031
    switch %2032 [ 0: bb143(%316) 1: bb144(%317, %318) default: bb24 ]
bb143(%319: ptr):
    %2033 = load i64, ptr %449
    store i64 %2033, ptr %452
    %2034 = const i64 8
    %2035 = gep i8, ptr %449, %2034
    %2036 = const i64 8
    %2037 = gep i8, ptr %452, %2036
    %2038 = load i64, ptr %2035
    store i64 %2038, ptr %2037
    %2039 = const i64 16
    %2040 = gep i8, ptr %449, %2039
    %2041 = const i64 16
    %2042 = gep i8, ptr %452, %2041
    %2043 = load i64, ptr %2040
    store i64 %2043, ptr %2042
    %2044 = const i64 24
    %2045 = gep i8, ptr %449, %2044
    %2046 = const i64 24
    %2047 = gep i8, ptr %452, %2046
    %2048 = load i64, ptr %2045
    store i64 %2048, ptr %2047
    %2049 = const i64 32
    %2050 = gep i8, ptr %449, %2049
    %2051 = const i64 32
    %2052 = gep i8, ptr %452, %2051
    %2053 = load i64, ptr %2050
    store i64 %2053, ptr %2052
    %2054 = load i64, ptr %452
    store i64 %2054, ptr %448
    %2055 = const i64 8
    %2056 = gep i8, ptr %452, %2055
    %2057 = const i64 8
    %2058 = gep i8, ptr %448, %2057
    %2059 = load i64, ptr %2056
    store i64 %2059, ptr %2058
    %2060 = const i64 16
    %2061 = gep i8, ptr %452, %2060
    %2062 = const i64 16
    %2063 = gep i8, ptr %448, %2062
    %2064 = load i64, ptr %2061
    store i64 %2064, ptr %2063
    %2065 = const i64 24
    %2066 = gep i8, ptr %452, %2065
    %2067 = const i64 24
    %2068 = gep i8, ptr %448, %2067
    %2069 = load i64, ptr %2066
    store i64 %2069, ptr %2068
    %2070 = const i64 32
    %2071 = gep i8, ptr %452, %2070
    %2072 = const i64 32
    %2073 = gep i8, ptr %448, %2072
    %2074 = load i64, ptr %2071
    store i64 %2074, ptr %2073
    %2075 = load ptr, ptr %319
    %2076 = const i64 16
    %2077 = gep i8, ptr %2075, %2076
    br bb146(%448, %2077)
bb144(%320: bool, %321: bool):
    %2078 = const i64 8
    %2079 = gep i8, ptr %449, %2078
    %2080 = load i64, ptr %2079
    store i64 %2080, ptr %451
    %2081 = const i64 8
    %2082 = gep i8, ptr %2079, %2081
    %2083 = const i64 8
    %2084 = gep i8, ptr %451, %2083
    %2085 = load i64, ptr %2082
    store i64 %2085, ptr %2084
    %2086 = const i64 16
    %2087 = gep i8, ptr %2079, %2086
    %2088 = const i64 16
    %2089 = gep i8, ptr %451, %2088
    %2090 = load i64, ptr %2087
    store i64 %2090, ptr %2089
    call @func.41(%0, %451)
    br bb145(%320, %321)
bb145(%322: bool, %323: bool):
    %2091 = const bool false
    br bb156(%322, %323)
bb146(%324: ptr, %325: ptr):
    call @func.65(%453, %324, %325)
    br bb147
bb147:
    %2092 = load i64, ptr %453
    store i64 %2092, ptr %0
    %2093 = const i64 8
    %2094 = gep i8, ptr %453, %2093
    %2095 = const i64 8
    %2096 = gep i8, ptr %0, %2095
    %2097 = load i64, ptr %2094
    store i64 %2097, ptr %2096
    %2098 = const i64 16
    %2099 = gep i8, ptr %453, %2098
    %2100 = const i64 16
    %2101 = gep i8, ptr %0, %2100
    %2102 = load i64, ptr %2099
    store i64 %2102, ptr %2101
    %2103 = const i64 24
    %2104 = gep i8, ptr %453, %2103
    %2105 = const i64 24
    %2106 = gep i8, ptr %0, %2105
    %2107 = load i64, ptr %2104
    store i64 %2107, ptr %2106
    %2108 = const i64 32
    %2109 = gep i8, ptr %453, %2108
    %2110 = const i64 32
    %2111 = gep i8, ptr %0, %2110
    %2112 = load i64, ptr %2109
    store i64 %2112, ptr %2111
    br bb148
bb148:
    %2113 = const bool false
    br bb149
bb149:
    %2114 = const bool false
    br bb150
bb150:
    br bb151
bb151:
    %2115 = const bool false
    br bb171
bb152:
    %2116 = const u32 4294901762
    store u32 %2116, ptr %456
    %2117 = load u32, ptr %456
    call @func.68(%454, %2117)
    br bb154
bb153:
    %2118 = const u32 4294901761
    store u32 %2118, ptr %455
    %2119 = load u32, ptr %455
    call @func.68(%454, %2119)
    br bb154
bb154:
    %2120 = load i64, ptr %454
    store i64 %2120, ptr %0
    %2121 = const i64 8
    %2122 = gep i8, ptr %454, %2121
    %2123 = const i64 8
    %2124 = gep i8, ptr %0, %2123
    %2125 = load i64, ptr %2122
    store i64 %2125, ptr %2124
    %2126 = const i64 16
    %2127 = gep i8, ptr %454, %2126
    %2128 = const i64 16
    %2129 = gep i8, ptr %0, %2128
    %2130 = load i64, ptr %2127
    store i64 %2130, ptr %2129
    %2131 = const i64 24
    %2132 = gep i8, ptr %454, %2131
    %2133 = const i64 24
    %2134 = gep i8, ptr %0, %2133
    %2135 = load i64, ptr %2132
    store i64 %2135, ptr %2134
    %2136 = const i64 32
    %2137 = gep i8, ptr %454, %2136
    %2138 = const i64 32
    %2139 = gep i8, ptr %0, %2138
    %2140 = load i64, ptr %2137
    store i64 %2140, ptr %2139
    br bb171
bb155(%326: ptr, %327: ptr):
    %2141 = load ptr, ptr %342
    call @func.45(%0, %326, %327, %2141)
    br bb171
bb156(%328: bool, %329: bool):
    condbr %328, bb173(%329), bb157(%329)
bb157(%330: bool):
    %2142 = const bool false
    br bb158(%330)
bb158(%331: bool):
    br bb159(%331)
bb159(%332: bool):
    condbr %332, bb174, bb160
bb160:
    %2143 = const bool false
    br bb171
bb161(%333: bool):
    %2144 = const bool false
    %2145 = const bool false
    br bb162(%333)
bb162(%334: bool):
    %2146 = const bool false
    br bb163(%334)
bb163(%335: bool):
    condbr %335, bb175, bb164
bb164:
    %2147 = const bool false
    br bb171
bb165(%336: bool):
    br bb166(%336)
bb166(%337: bool):
    condbr %337, bb176, bb167
bb167:
    %2148 = const bool false
    br bb171
bb168:
    %2149 = const bool false
    br bb169
bb169:
    br bb170
bb170:
    %2150 = const bool false
    br bb171
bb171:
    ret
bb172:
    br bb56
bb173(%338: bool):
    br bb157(%338)
bb174:
    br bb160
bb175:
    br bb164
bb176:
    br bb167
bb177:
    br bb168
bb178(%339: bool):
    br bb161(%339)
bb179(%340: bool):
    br bb157(%340)
bb180:
    unreachable
}

fn @Verifier____env___whnf_impl(functy.46) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    call @func.70(%0, %1, %2)
    br bb1
bb1:
    ret
}

fn @_RNvXsu_NtCskTzINo8ZBH9_5alloc4syncINtB5_3ArcNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelENtNtCs2EYQwhfuABO_4core5clone5Clone5cloneBI_(functy.47) {
}

fn @_Level_as_std__clone__Clone___clone(functy.48) {
bb0(%0: ptr, %1: ptr):
    %4 = alloca i64, align 8
    %5 = alloca i64, align 8
    %6 = alloca i64, align 8
    %7 = alloca i64, align 8
    %8 = alloca i64, align 8
    %9 = alloca i64, align 8
    %10 = alloca i32, align 4
    store ptr %1, ptr %4
    %11 = load ptr, ptr %4
    %12 = load i32, ptr %11
    %13 = sext i32 %12 to i64
    switch %13 [ 0: bb6 1: bb5 2: bb4 3: bb3 4: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %14 = load ptr, ptr %4
    %15 = const i64 4
    %16 = gep i8, ptr %14, %15
    call @func.71(%10, %16)
    br bb12
bb3:
    %17 = load ptr, ptr %4
    %18 = const i64 8
    %19 = gep i8, ptr %17, %18
    %20 = load ptr, ptr %4
    %21 = const i64 16
    %22 = gep i8, ptr %20, %21
    call @func.47(%8, %19)
    br bb10(%22)
bb4:
    %23 = load ptr, ptr %4
    %24 = const i64 8
    %25 = gep i8, ptr %23, %24
    %26 = load ptr, ptr %4
    %27 = const i64 16
    %28 = gep i8, ptr %26, %27
    call @func.47(%6, %25)
    br bb8(%28)
bb5:
    %29 = load ptr, ptr %4
    %30 = const i64 8
    %31 = gep i8, ptr %29, %30
    call @func.47(%5, %31)
    br bb7
bb6:
    %32 = const i32 0
    store i32 %32, ptr %0
    br bb13
bb7:
    %33 = load ptr, ptr %5
    %34 = const i64 8
    %35 = gep i8, ptr %0, %34
    store ptr %33, ptr %35
    %36 = const i32 1
    store i32 %36, ptr %0
    br bb13
bb8(%2: ptr):
    call @func.47(%7, %2)
    br bb9
bb9:
    %37 = load ptr, ptr %6
    %38 = const i64 8
    %39 = gep i8, ptr %0, %38
    store ptr %37, ptr %39
    %40 = load ptr, ptr %7
    %41 = const i64 16
    %42 = gep i8, ptr %0, %41
    store ptr %40, ptr %42
    %43 = const i32 2
    store i32 %43, ptr %0
    br bb13
bb10(%3: ptr):
    call @func.47(%9, %3)
    br bb11
bb11:
    %44 = load ptr, ptr %8
    %45 = const i64 8
    %46 = gep i8, ptr %0, %45
    store ptr %44, ptr %46
    %47 = load ptr, ptr %9
    %48 = const i64 16
    %49 = gep i8, ptr %0, %48
    store ptr %47, ptr %49
    %50 = const i32 3
    store i32 %50, ptr %0
    br bb13
bb12:
    %51 = const i64 4
    %52 = gep i8, ptr %0, %51
    %53 = load i32, ptr %10
    store i32 %53, ptr %52
    %54 = const i32 4
    store i32 %54, ptr %0
    br bb13
bb13:
    ret
}

fn @Level__imax(functy.49) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %43 = alloca (i64, i64, i64), align 8
    %44 = alloca (i64, i64, i64), align 8
    %45 = alloca (i64, i64, i64), align 8
    %46 = alloca (i64, i64, i64), align 8
    %47 = alloca i64, align 8
    %48 = alloca (i64, i64, i64), align 8
    %49 = alloca i64, align 8
    %50 = alloca (i64, i64, i64), align 8
    %51 = const bool false
    %52 = const bool false
    %53 = const bool true
    %54 = const bool true
    %55 = call @func.15(%2)
    br bb1(%55, %54, %53)
bb1(%3: bool, %4: bool, %5: bool):
    condbr %3, bb2(%4, %5), bb3(%4, %5)
bb2(%6: bool, %7: bool):
    %56 = const i32 0
    store i32 %56, ptr %0
    br bb25(%6, %7)
bb3(%8: bool, %9: bool):
    %57 = call @func.72(%2)
    br bb4(%57, %8, %9)
bb4(%10: bool, %11: bool, %12: bool):
    condbr %10, bb5, bb6(%11, %12)
bb5:
    %58 = const bool false
    %59 = load i64, ptr %1
    store i64 %59, ptr %43
    %60 = const i64 8
    %61 = gep i8, ptr %1, %60
    %62 = const i64 8
    %63 = gep i8, ptr %43, %62
    %64 = load i64, ptr %61
    store i64 %64, ptr %63
    %65 = const i64 16
    %66 = gep i8, ptr %1, %65
    %67 = const i64 16
    %68 = gep i8, ptr %43, %67
    %69 = load i64, ptr %66
    store i64 %69, ptr %68
    %70 = const bool false
    %71 = load i64, ptr %2
    store i64 %71, ptr %44
    %72 = const i64 8
    %73 = gep i8, ptr %2, %72
    %74 = const i64 8
    %75 = gep i8, ptr %44, %74
    %76 = load i64, ptr %73
    store i64 %76, ptr %75
    %77 = const i64 16
    %78 = gep i8, ptr %2, %77
    %79 = const i64 16
    %80 = gep i8, ptr %44, %79
    %81 = load i64, ptr %78
    store i64 %81, ptr %80
    call @func.73(%0, %43, %44)
    br bb27(%70, %58)
bb6(%13: bool, %14: bool):
    %82 = call @func.15(%1)
    br bb7(%82, %13, %14)
bb7(%15: bool, %16: bool, %17: bool):
    condbr %15, bb8(%17), bb9(%16, %17)
bb8(%18: bool):
    %83 = const bool false
    %84 = load i64, ptr %2
    store i64 %84, ptr %0
    %85 = const i64 8
    %86 = gep i8, ptr %2, %85
    %87 = const i64 8
    %88 = gep i8, ptr %0, %87
    %89 = load i64, ptr %86
    store i64 %89, ptr %88
    %90 = const i64 16
    %91 = gep i8, ptr %2, %90
    %92 = const i64 16
    %93 = gep i8, ptr %0, %92
    %94 = load i64, ptr %91
    store i64 %94, ptr %93
    br bb25(%83, %18)
bb9(%19: bool, %20: bool):
    call @func.74(%46)
    br bb10(%1, %19, %20)
bb10(%21: ptr, %22: bool, %23: bool):
    call @func.61(%45, %46)
    br bb11(%21, %22, %23)
bb11(%24: ptr, %25: bool, %26: bool):
    %95 = call @func.78(%24, %45)
    br bb12(%95, %25, %26)
bb12(%27: bool, %28: bool, %29: bool):
    condbr %27, bb13(%29), bb15(%28)
bb13(%30: bool):
    br bb14(%30)
bb14(%31: bool):
    %96 = const bool false
    %97 = load i64, ptr %2
    store i64 %97, ptr %0
    %98 = const i64 8
    %99 = gep i8, ptr %2, %98
    %100 = const i64 8
    %101 = gep i8, ptr %0, %100
    %102 = load i64, ptr %99
    store i64 %102, ptr %101
    %103 = const i64 16
    %104 = gep i8, ptr %2, %103
    %105 = const i64 16
    %106 = gep i8, ptr %0, %105
    %107 = load i64, ptr %104
    store i64 %107, ptr %106
    br bb25(%96, %31)
bb15(%32: bool):
    br bb16(%32)
bb16(%33: bool):
    %108 = call @func.78(%1, %2)
    br bb17(%108, %33)
bb17(%34: bool, %35: bool):
    condbr %34, bb18(%35), bb19
bb18(%36: bool):
    %109 = const bool false
    %110 = load i64, ptr %1
    store i64 %110, ptr %0
    %111 = const i64 8
    %112 = gep i8, ptr %1, %111
    %113 = const i64 8
    %114 = gep i8, ptr %0, %113
    %115 = load i64, ptr %112
    store i64 %115, ptr %114
    %116 = const i64 16
    %117 = gep i8, ptr %1, %116
    %118 = const i64 16
    %119 = gep i8, ptr %0, %118
    %120 = load i64, ptr %117
    store i64 %120, ptr %119
    br bb25(%36, %109)
bb19:
    %121 = const bool false
    %122 = load i64, ptr %1
    store i64 %122, ptr %48
    %123 = const i64 8
    %124 = gep i8, ptr %1, %123
    %125 = const i64 8
    %126 = gep i8, ptr %48, %125
    %127 = load i64, ptr %124
    store i64 %127, ptr %126
    %128 = const i64 16
    %129 = gep i8, ptr %1, %128
    %130 = const i64 16
    %131 = gep i8, ptr %48, %130
    %132 = load i64, ptr %129
    store i64 %132, ptr %131
    call @func.79(%47, %48)
    br bb20
bb20:
    %133 = const bool false
    %134 = load i64, ptr %2
    store i64 %134, ptr %50
    %135 = const i64 8
    %136 = gep i8, ptr %2, %135
    %137 = const i64 8
    %138 = gep i8, ptr %50, %137
    %139 = load i64, ptr %136
    store i64 %139, ptr %138
    %140 = const i64 16
    %141 = gep i8, ptr %2, %140
    %142 = const i64 16
    %143 = gep i8, ptr %50, %142
    %144 = load i64, ptr %141
    store i64 %144, ptr %143
    call @func.79(%49, %50)
    br bb21
bb21:
    %145 = load ptr, ptr %47
    %146 = const i64 8
    %147 = gep i8, ptr %0, %146
    store ptr %145, ptr %147
    %148 = load ptr, ptr %49
    %149 = const i64 16
    %150 = gep i8, ptr %0, %149
    store ptr %148, ptr %150
    %151 = const i32 3
    store i32 %151, ptr %0
    br bb23
bb22(%37: bool):
    condbr %37, bb26, bb23
bb23:
    ret
bb24(%38: bool):
    br bb22(%38)
bb25(%39: bool, %40: bool):
    condbr %39, bb24(%40), bb22(%40)
bb26:
    br bb23
bb27(%41: bool, %42: bool):
    br bb25(%41, %42)
}

fn @_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCshhXhIKvfvMU_25clean_decl_universe_slice4NameNtB7_9PartialEq2eqBF_(functy.50) {
}

fn @_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCshhXhIKvfvMU_25clean_decl_universe_slice7LiteralNtB7_9PartialEq2eqBF_(functy.51) {
}

fn @_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCshhXhIKvfvMU_25clean_decl_universe_slice6FVarIdNtB7_9PartialEq2eqBF_(functy.52) {
}

fn @_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRmNtB7_9PartialEq2eqCshhXhIKvfvMU_25clean_decl_universe_slice(functy.53) {
}

fn @_RNvXs7_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefBH_(functy.54) {
}

fn @Verifier____env___def_eq_inner(functy.55) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %206 = alloca (i64, i64, i64, i64, i64), align 8
    %207 = alloca (i64, i64, i64, i64, i64), align 8
    %208 = alloca i64, align 8
    %209 = alloca i64, align 8
    %210 = alloca (i64, i64), align 8
    %211 = alloca i64, align 8
    %212 = alloca i64, align 8
    %213 = alloca i64, align 8
    %214 = alloca i64, align 8
    %215 = alloca i64, align 8
    %216 = alloca i64, align 8
    %217 = alloca (i64, i64), align 8
    %218 = alloca (i64, i64), align 8
    %219 = alloca i64, align 8
    %220 = alloca i64, align 8
    %221 = alloca i64, align 8
    %222 = alloca i64, align 8
    %223 = alloca i64, align 8
    %224 = alloca i64, align 8
    %225 = alloca i64, align 8
    %226 = alloca i64, align 8
    %227 = alloca i64, align 8
    %228 = alloca i64, align 8
    %229 = alloca i64, align 8
    %230 = alloca i64, align 8
    %231 = alloca i64, align 8
    %232 = alloca i64, align 8
    %233 = alloca i64, align 8
    %234 = alloca i64, align 8
    %235 = alloca i64, align 8
    %236 = alloca i64, align 8
    %237 = alloca i64, align 8
    %238 = alloca i64, align 8
    %239 = alloca i64, align 8
    %240 = alloca i64, align 8
    %241 = alloca i64, align 8
    %242 = alloca i64, align 8
    %243 = alloca i64, align 8
    %244 = alloca i64, align 8
    %245 = alloca i64, align 8
    %246 = alloca i64, align 8
    %247 = alloca i64, align 8
    %248 = alloca i64, align 8
    %249 = alloca i64, align 8
    %250 = alloca i64, align 8
    %251 = alloca i64, align 8
    %252 = alloca i64, align 8
    %253 = alloca i64, align 8
    %254 = alloca i64, align 8
    %255 = alloca i64, align 8
    %256 = alloca i64, align 8
    %257 = alloca i64, align 8
    %258 = alloca i64, align 8
    %259 = alloca i64, align 8
    %260 = alloca i64, align 8
    %261 = alloca i64, align 8
    %262 = alloca i64, align 8
    %263 = alloca i64, align 8
    %264 = alloca i64, align 8
    %265 = alloca i64, align 8
    %266 = alloca i64, align 8
    call @func.46(%206, %0, %1)
    br bb1(%0, %2)
bb1(%3: ptr, %4: ptr):
    call @func.46(%207, %3, %4)
    br bb2(%3)
bb2(%5: ptr):
    %267 = const i64 32
    %268 = gep i8, ptr %206, %267
    %269 = load i64, ptr %268
    store i64 %269, ptr %208
    %270 = load u64, ptr %208
    %271 = call @func.80(%270)
    br bb3(%5, %271)
bb3(%6: ptr, %7: u64):
    %272 = const i64 32
    %273 = gep i8, ptr %207, %272
    %274 = load i64, ptr %273
    store i64 %274, ptr %209
    %275 = load u64, ptr %209
    %276 = call @func.80(%275)
    br bb4(%6, %7, %276)
bb4(%8: ptr, %9: u64, %10: u64):
    %277 = icmp eq u64 %9, %10
    condbr %277, bb5(%8), bb8(%8)
bb5(%11: ptr):
    %278 = call @func.86(%11, %206, %207)
    br bb6(%11, %278)
bb6(%12: ptr, %13: bool):
    condbr %13, bb7, bb8(%12)
bb7:
    %279 = const bool true
    br bb77(%279)
bb8(%14: ptr):
    store ptr %206, ptr %210
    %280 = const i64 8
    %281 = gep i8, ptr %210, %280
    store ptr %207, ptr %281
    %282 = load ptr, ptr %210
    %283 = load i8, ptr %282
    %284 = sext i8 %283 to i64
    switch %284 [ 0: bb10(%14) 1: bb11(%14) 2: bb12(%14) 3: bb13(%14) 4: bb14(%14) 5: bb15(%14) 6: bb16(%14) 7: bb17(%14) 8: bb18(%14) 9: bb19(%14) 10: bb20(%14) default: bb80 ]
bb9(%15: ptr):
    %285 = const bool false
    br bb72(%15, %285)
bb10(%16: ptr):
    %286 = const i64 8
    %287 = gep i8, ptr %210, %286
    %288 = load ptr, ptr %287
    %289 = load i8, ptr %288
    %290 = sext i8 %289 to i64
    switch %290 [ 0: bb31(%16) default: bb9(%16) ]
bb11(%17: ptr):
    %291 = const i64 8
    %292 = gep i8, ptr %210, %291
    %293 = load ptr, ptr %292
    %294 = load i8, ptr %293
    %295 = sext i8 %294 to i64
    switch %295 [ 1: bb30(%17) default: bb9(%17) ]
bb12(%18: ptr):
    %296 = const i64 8
    %297 = gep i8, ptr %210, %296
    %298 = load ptr, ptr %297
    %299 = load i8, ptr %298
    %300 = sext i8 %299 to i64
    switch %300 [ 2: bb29(%18) default: bb9(%18) ]
bb13(%19: ptr):
    %301 = const i64 8
    %302 = gep i8, ptr %210, %301
    %303 = load ptr, ptr %302
    %304 = load i8, ptr %303
    %305 = sext i8 %304 to i64
    switch %305 [ 3: bb28(%19) default: bb9(%19) ]
bb14(%20: ptr):
    %306 = const i64 8
    %307 = gep i8, ptr %210, %306
    %308 = load ptr, ptr %307
    %309 = load i8, ptr %308
    %310 = sext i8 %309 to i64
    switch %310 [ 4: bb27(%20) default: bb9(%20) ]
bb15(%21: ptr):
    %311 = const i64 8
    %312 = gep i8, ptr %210, %311
    %313 = load ptr, ptr %312
    %314 = load i8, ptr %313
    %315 = sext i8 %314 to i64
    switch %315 [ 5: bb26(%21) default: bb9(%21) ]
bb16(%22: ptr):
    %316 = const i64 8
    %317 = gep i8, ptr %210, %316
    %318 = load ptr, ptr %317
    %319 = load i8, ptr %318
    %320 = sext i8 %319 to i64
    switch %320 [ 6: bb25(%22) default: bb9(%22) ]
bb17(%23: ptr):
    %321 = const i64 8
    %322 = gep i8, ptr %210, %321
    %323 = load ptr, ptr %322
    %324 = load i8, ptr %323
    %325 = sext i8 %324 to i64
    switch %325 [ 7: bb24(%23) default: bb9(%23) ]
bb18(%24: ptr):
    %326 = const i64 8
    %327 = gep i8, ptr %210, %326
    %328 = load ptr, ptr %327
    %329 = load i8, ptr %328
    %330 = sext i8 %329 to i64
    switch %330 [ 8: bb23(%24) default: bb9(%24) ]
bb19(%25: ptr):
    %331 = const i64 8
    %332 = gep i8, ptr %210, %331
    %333 = load ptr, ptr %332
    %334 = load i8, ptr %333
    %335 = sext i8 %334 to i64
    switch %335 [ 9: bb22(%25) default: bb9(%25) ]
bb20(%26: ptr):
    %336 = const i64 8
    %337 = gep i8, ptr %210, %336
    %338 = load ptr, ptr %337
    %339 = load i8, ptr %338
    %340 = sext i8 %339 to i64
    switch %340 [ 10: bb21(%26) default: bb9(%26) ]
bb21(%27: ptr):
    %341 = load ptr, ptr %210
    store ptr %341, ptr %225
    %342 = load ptr, ptr %225
    %343 = const i64 8
    %344 = gep i8, ptr %342, %343
    %345 = const i64 8
    %346 = gep i8, ptr %210, %345
    %347 = load ptr, ptr %346
    store ptr %347, ptr %226
    %348 = load ptr, ptr %226
    %349 = const i64 8
    %350 = gep i8, ptr %348, %349
    %351 = load ptr, ptr %344
    %352 = const i64 16
    %353 = gep i8, ptr %351, %352
    br bb70(%27, %350, %353)
bb22(%28: ptr):
    %354 = load ptr, ptr %210
    store ptr %354, ptr %227
    %355 = load ptr, ptr %227
    %356 = const i64 4
    %357 = gep i8, ptr %355, %356
    store ptr %357, ptr %221
    %358 = load ptr, ptr %210
    store ptr %358, ptr %228
    %359 = load ptr, ptr %228
    %360 = const i64 8
    %361 = gep i8, ptr %359, %360
    store ptr %361, ptr %222
    %362 = load ptr, ptr %210
    store ptr %362, ptr %229
    %363 = load ptr, ptr %229
    %364 = const i64 16
    %365 = gep i8, ptr %363, %364
    %366 = const i64 8
    %367 = gep i8, ptr %210, %366
    %368 = load ptr, ptr %367
    store ptr %368, ptr %230
    %369 = load ptr, ptr %230
    %370 = const i64 4
    %371 = gep i8, ptr %369, %370
    store ptr %371, ptr %223
    %372 = const i64 8
    %373 = gep i8, ptr %210, %372
    %374 = load ptr, ptr %373
    store ptr %374, ptr %231
    %375 = load ptr, ptr %231
    %376 = const i64 8
    %377 = gep i8, ptr %375, %376
    store ptr %377, ptr %224
    %378 = const i64 8
    %379 = gep i8, ptr %210, %378
    %380 = load ptr, ptr %379
    store ptr %380, ptr %232
    %381 = load ptr, ptr %232
    %382 = const i64 16
    %383 = gep i8, ptr %381, %382
    %384 = call @func.50(%221, %223)
    br bb63(%28, %365, %383, %384)
bb23(%29: ptr):
    %385 = load ptr, ptr %210
    store ptr %385, ptr %233
    %386 = load ptr, ptr %233
    %387 = const i64 8
    %388 = gep i8, ptr %386, %387
    store ptr %388, ptr %219
    %389 = const i64 8
    %390 = gep i8, ptr %210, %389
    %391 = load ptr, ptr %390
    store ptr %391, ptr %234
    %392 = load ptr, ptr %234
    %393 = const i64 8
    %394 = gep i8, ptr %392, %393
    store ptr %394, ptr %220
    %395 = call @func.51(%219, %220)
    br bb81(%29, %395)
bb24(%30: ptr):
    %396 = load ptr, ptr %210
    store ptr %396, ptr %235
    %397 = load ptr, ptr %235
    %398 = const i64 8
    %399 = gep i8, ptr %397, %398
    %400 = load ptr, ptr %210
    store ptr %400, ptr %236
    %401 = load ptr, ptr %236
    %402 = const i64 16
    %403 = gep i8, ptr %401, %402
    %404 = load ptr, ptr %210
    store ptr %404, ptr %237
    %405 = load ptr, ptr %237
    %406 = const i64 24
    %407 = gep i8, ptr %405, %406
    %408 = const i64 8
    %409 = gep i8, ptr %210, %408
    %410 = load ptr, ptr %409
    store ptr %410, ptr %238
    %411 = load ptr, ptr %238
    %412 = const i64 8
    %413 = gep i8, ptr %411, %412
    %414 = const i64 8
    %415 = gep i8, ptr %210, %414
    %416 = load ptr, ptr %415
    store ptr %416, ptr %239
    %417 = load ptr, ptr %239
    %418 = const i64 16
    %419 = gep i8, ptr %417, %418
    %420 = const i64 8
    %421 = gep i8, ptr %210, %420
    %422 = load ptr, ptr %421
    store ptr %422, ptr %240
    %423 = load ptr, ptr %240
    %424 = const i64 24
    %425 = gep i8, ptr %423, %424
    %426 = load ptr, ptr %399
    %427 = const i64 16
    %428 = gep i8, ptr %426, %427
    br bb52(%30, %403, %407, %413, %419, %425, %428)
bb25(%31: ptr):
    %429 = load ptr, ptr %210
    store ptr %429, ptr %241
    %430 = load ptr, ptr %241
    %431 = const i64 1
    %432 = gep i8, ptr %430, %431
    %433 = load ptr, ptr %210
    store ptr %433, ptr %242
    %434 = load ptr, ptr %242
    %435 = const i64 8
    %436 = gep i8, ptr %434, %435
    %437 = load ptr, ptr %210
    store ptr %437, ptr %243
    %438 = load ptr, ptr %243
    %439 = const i64 16
    %440 = gep i8, ptr %438, %439
    %441 = const i64 8
    %442 = gep i8, ptr %210, %441
    %443 = load ptr, ptr %442
    store ptr %443, ptr %244
    %444 = load ptr, ptr %244
    %445 = const i64 1
    %446 = gep i8, ptr %444, %445
    %447 = const i64 8
    %448 = gep i8, ptr %210, %447
    %449 = load ptr, ptr %448
    store ptr %449, ptr %245
    %450 = load ptr, ptr %245
    %451 = const i64 8
    %452 = gep i8, ptr %450, %451
    %453 = const i64 8
    %454 = gep i8, ptr %210, %453
    %455 = load ptr, ptr %454
    store ptr %455, ptr %246
    %456 = load ptr, ptr %246
    %457 = const i64 16
    %458 = gep i8, ptr %456, %457
    br bb44(%31, %436, %440, %452, %458)
bb26(%32: ptr):
    %459 = load ptr, ptr %210
    store ptr %459, ptr %247
    %460 = load ptr, ptr %247
    %461 = const i64 1
    %462 = gep i8, ptr %460, %461
    %463 = load ptr, ptr %210
    store ptr %463, ptr %248
    %464 = load ptr, ptr %248
    %465 = const i64 8
    %466 = gep i8, ptr %464, %465
    %467 = load ptr, ptr %210
    store ptr %467, ptr %249
    %468 = load ptr, ptr %249
    %469 = const i64 16
    %470 = gep i8, ptr %468, %469
    %471 = const i64 8
    %472 = gep i8, ptr %210, %471
    %473 = load ptr, ptr %472
    store ptr %473, ptr %250
    %474 = load ptr, ptr %250
    %475 = const i64 1
    %476 = gep i8, ptr %474, %475
    %477 = const i64 8
    %478 = gep i8, ptr %210, %477
    %479 = load ptr, ptr %478
    store ptr %479, ptr %251
    %480 = load ptr, ptr %251
    %481 = const i64 8
    %482 = gep i8, ptr %480, %481
    %483 = const i64 8
    %484 = gep i8, ptr %210, %483
    %485 = load ptr, ptr %484
    store ptr %485, ptr %252
    %486 = load ptr, ptr %252
    %487 = const i64 16
    %488 = gep i8, ptr %486, %487
    br bb44(%32, %466, %470, %482, %488)
bb27(%33: ptr):
    %489 = load ptr, ptr %210
    store ptr %489, ptr %253
    %490 = load ptr, ptr %253
    %491 = const i64 8
    %492 = gep i8, ptr %490, %491
    %493 = load ptr, ptr %210
    store ptr %493, ptr %254
    %494 = load ptr, ptr %254
    %495 = const i64 16
    %496 = gep i8, ptr %494, %495
    %497 = const i64 8
    %498 = gep i8, ptr %210, %497
    %499 = load ptr, ptr %498
    store ptr %499, ptr %255
    %500 = load ptr, ptr %255
    %501 = const i64 8
    %502 = gep i8, ptr %500, %501
    %503 = const i64 8
    %504 = gep i8, ptr %210, %503
    %505 = load ptr, ptr %504
    store ptr %505, ptr %256
    %506 = load ptr, ptr %256
    %507 = const i64 16
    %508 = gep i8, ptr %506, %507
    %509 = load ptr, ptr %492
    %510 = const i64 16
    %511 = gep i8, ptr %509, %510
    br bb37(%33, %496, %502, %508, %511)
bb28(%34: ptr):
    %512 = load ptr, ptr %210
    store ptr %512, ptr %257
    %513 = load ptr, ptr %257
    %514 = const i64 4
    %515 = gep i8, ptr %513, %514
    store ptr %515, ptr %215
    %516 = load ptr, ptr %210
    store ptr %516, ptr %258
    %517 = load ptr, ptr %258
    %518 = const i64 8
    %519 = gep i8, ptr %517, %518
    %520 = const i64 8
    %521 = gep i8, ptr %210, %520
    %522 = load ptr, ptr %521
    store ptr %522, ptr %259
    %523 = load ptr, ptr %259
    %524 = const i64 4
    %525 = gep i8, ptr %523, %524
    store ptr %525, ptr %216
    %526 = const i64 8
    %527 = gep i8, ptr %210, %526
    %528 = load ptr, ptr %527
    store ptr %528, ptr %260
    %529 = load ptr, ptr %260
    %530 = const i64 8
    %531 = gep i8, ptr %529, %530
    %532 = call @func.50(%215, %216)
    br bb32(%34, %519, %531, %532)
bb29(%35: ptr):
    %533 = load ptr, ptr %210
    store ptr %533, ptr %261
    %534 = load ptr, ptr %261
    %535 = const i64 8
    %536 = gep i8, ptr %534, %535
    %537 = const i64 8
    %538 = gep i8, ptr %210, %537
    %539 = load ptr, ptr %538
    store ptr %539, ptr %262
    %540 = load ptr, ptr %262
    %541 = const i64 8
    %542 = gep i8, ptr %540, %541
    %543 = call @func.87(%35, %536, %542)
    br bb82(%35, %543)
bb30(%36: ptr):
    %544 = load ptr, ptr %210
    store ptr %544, ptr %263
    %545 = load ptr, ptr %263
    %546 = const i64 8
    %547 = gep i8, ptr %545, %546
    store ptr %547, ptr %213
    %548 = const i64 8
    %549 = gep i8, ptr %210, %548
    %550 = load ptr, ptr %549
    store ptr %550, ptr %264
    %551 = load ptr, ptr %264
    %552 = const i64 8
    %553 = gep i8, ptr %551, %552
    store ptr %553, ptr %214
    %554 = call @func.52(%213, %214)
    br bb83(%36, %554)
bb31(%37: ptr):
    %555 = load ptr, ptr %210
    store ptr %555, ptr %265
    %556 = load ptr, ptr %265
    %557 = const i64 4
    %558 = gep i8, ptr %556, %557
    store ptr %558, ptr %211
    %559 = const i64 8
    %560 = gep i8, ptr %210, %559
    %561 = load ptr, ptr %560
    store ptr %561, ptr %266
    %562 = load ptr, ptr %266
    %563 = const i64 4
    %564 = gep i8, ptr %562, %563
    store ptr %564, ptr %212
    %565 = call @func.53(%211, %212)
    br bb84(%37, %565)
bb32(%38: ptr, %39: ptr, %40: ptr, %41: bool):
    condbr %41, bb33(%38, %39, %40), bb34(%38)
bb33(%42: ptr, %43: ptr, %44: ptr):
    call @func.54(%217, %43)
    br bb35(%42, %44)
bb34(%45: ptr):
    %566 = const bool false
    br bb72(%45, %566)
bb35(%46: ptr, %47: ptr):
    call @func.54(%218, %47)
    br bb36(%46)
bb36(%48: ptr):
    %567 = call @func.88(%48, %217, %218)
    br bb85(%48, %567)
bb37(%49: ptr, %50: ptr, %51: ptr, %52: ptr, %53: ptr):
    %568 = load ptr, ptr %51
    %569 = const i64 16
    %570 = gep i8, ptr %568, %569
    br bb38(%49, %50, %52, %53, %570)
bb38(%54: ptr, %55: ptr, %56: ptr, %57: ptr, %58: ptr):
    %571 = call @func.89(%54, %57, %58)
    br bb39(%54, %55, %56, %571)
bb39(%59: ptr, %60: ptr, %61: ptr, %62: bool):
    condbr %62, bb40(%59, %60, %61), bb41(%59)
bb40(%63: ptr, %64: ptr, %65: ptr):
    %572 = load ptr, ptr %64
    %573 = const i64 16
    %574 = gep i8, ptr %572, %573
    br bb42(%63, %65, %574)
bb41(%66: ptr):
    %575 = const bool false
    br bb72(%66, %575)
bb42(%67: ptr, %68: ptr, %69: ptr):
    %576 = load ptr, ptr %68
    %577 = const i64 16
    %578 = gep i8, ptr %576, %577
    br bb43(%67, %69, %578)
bb43(%70: ptr, %71: ptr, %72: ptr):
    %579 = call @func.89(%70, %71, %72)
    br bb86(%70, %579)
bb44(%73: ptr, %74: ptr, %75: ptr, %76: ptr, %77: ptr):
    %580 = load ptr, ptr %74
    %581 = const i64 16
    %582 = gep i8, ptr %580, %581
    br bb45(%73, %75, %76, %77, %582)
bb45(%78: ptr, %79: ptr, %80: ptr, %81: ptr, %82: ptr):
    %583 = load ptr, ptr %80
    %584 = const i64 16
    %585 = gep i8, ptr %583, %584
    br bb46(%78, %79, %81, %82, %585)
bb46(%83: ptr, %84: ptr, %85: ptr, %86: ptr, %87: ptr):
    %586 = call @func.89(%83, %86, %87)
    br bb47(%83, %84, %85, %586)
bb47(%88: ptr, %89: ptr, %90: ptr, %91: bool):
    condbr %91, bb48(%88, %89, %90), bb49(%88)
bb48(%92: ptr, %93: ptr, %94: ptr):
    %587 = load ptr, ptr %93
    %588 = const i64 16
    %589 = gep i8, ptr %587, %588
    br bb50(%92, %94, %589)
bb49(%95: ptr):
    %590 = const bool false
    br bb72(%95, %590)
bb50(%96: ptr, %97: ptr, %98: ptr):
    %591 = load ptr, ptr %97
    %592 = const i64 16
    %593 = gep i8, ptr %591, %592
    br bb51(%96, %98, %593)
bb51(%99: ptr, %100: ptr, %101: ptr):
    %594 = call @func.89(%99, %100, %101)
    br bb87(%99, %594)
bb52(%102: ptr, %103: ptr, %104: ptr, %105: ptr, %106: ptr, %107: ptr, %108: ptr):
    %595 = load ptr, ptr %105
    %596 = const i64 16
    %597 = gep i8, ptr %595, %596
    br bb53(%102, %103, %104, %106, %107, %108, %597)
bb53(%109: ptr, %110: ptr, %111: ptr, %112: ptr, %113: ptr, %114: ptr, %115: ptr):
    %598 = call @func.89(%109, %114, %115)
    br bb54(%109, %110, %111, %112, %113, %598)
bb54(%116: ptr, %117: ptr, %118: ptr, %119: ptr, %120: ptr, %121: bool):
    condbr %121, bb55(%116, %117, %118, %119, %120), bb60(%116)
bb55(%122: ptr, %123: ptr, %124: ptr, %125: ptr, %126: ptr):
    %599 = load ptr, ptr %123
    %600 = const i64 16
    %601 = gep i8, ptr %599, %600
    br bb56(%122, %124, %125, %126, %601)
bb56(%127: ptr, %128: ptr, %129: ptr, %130: ptr, %131: ptr):
    %602 = load ptr, ptr %129
    %603 = const i64 16
    %604 = gep i8, ptr %602, %603
    br bb57(%127, %128, %130, %131, %604)
bb57(%132: ptr, %133: ptr, %134: ptr, %135: ptr, %136: ptr):
    %605 = call @func.89(%132, %135, %136)
    br bb58(%132, %133, %134, %605)
bb58(%137: ptr, %138: ptr, %139: ptr, %140: bool):
    condbr %140, bb59(%137, %138, %139), bb60(%137)
bb59(%141: ptr, %142: ptr, %143: ptr):
    %606 = load ptr, ptr %142
    %607 = const i64 16
    %608 = gep i8, ptr %606, %607
    br bb61(%141, %143, %608)
bb60(%144: ptr):
    %609 = const bool false
    br bb72(%144, %609)
bb61(%145: ptr, %146: ptr, %147: ptr):
    %610 = load ptr, ptr %146
    %611 = const i64 16
    %612 = gep i8, ptr %610, %611
    br bb62(%145, %147, %612)
bb62(%148: ptr, %149: ptr, %150: ptr):
    %613 = call @func.89(%148, %149, %150)
    br bb88(%148, %613)
bb63(%151: ptr, %152: ptr, %153: ptr, %154: bool):
    condbr %154, bb64(%151, %152, %153), bb67(%151)
bb64(%155: ptr, %156: ptr, %157: ptr):
    %614 = call @func.53(%222, %224)
    br bb65(%155, %156, %157, %614)
bb65(%158: ptr, %159: ptr, %160: ptr, %161: bool):
    condbr %161, bb66(%158, %159, %160), bb67(%158)
bb66(%162: ptr, %163: ptr, %164: ptr):
    %615 = load ptr, ptr %163
    %616 = const i64 16
    %617 = gep i8, ptr %615, %616
    br bb68(%162, %164, %617)
bb67(%165: ptr):
    %618 = const bool false
    br bb72(%165, %618)
bb68(%166: ptr, %167: ptr, %168: ptr):
    %619 = load ptr, ptr %167
    %620 = const i64 16
    %621 = gep i8, ptr %619, %620
    br bb69(%166, %168, %621)
bb69(%169: ptr, %170: ptr, %171: ptr):
    %622 = call @func.89(%169, %170, %171)
    br bb89(%169, %622)
bb70(%172: ptr, %173: ptr, %174: ptr):
    %623 = load ptr, ptr %173
    %624 = const i64 16
    %625 = gep i8, ptr %623, %624
    br bb71(%172, %174, %625)
bb71(%175: ptr, %176: ptr, %177: ptr):
    %626 = call @func.89(%175, %176, %177)
    br bb90(%175, %626)
bb72(%178: ptr, %179: bool):
    condbr %179, bb73, bb74(%178)
bb73:
    %627 = const bool true
    br bb77(%627)
bb74(%180: ptr):
    %628 = call @func.90(%180, %206, %207)
    br bb75(%628)
bb75(%181: bool):
    br bb76(%181)
bb76(%182: bool):
    br bb79(%182)
bb77(%183: bool):
    br bb78(%183)
bb78(%184: bool):
    br bb79(%184)
bb79(%185: bool):
    ret %185
bb80:
    unreachable
bb81(%186: ptr, %187: bool):
    br bb72(%186, %187)
bb82(%188: ptr, %189: bool):
    br bb72(%188, %189)
bb83(%190: ptr, %191: bool):
    br bb72(%190, %191)
bb84(%192: ptr, %193: bool):
    br bb72(%192, %193)
bb85(%194: ptr, %195: bool):
    br bb72(%194, %195)
bb86(%196: ptr, %197: bool):
    br bb72(%196, %197)
bb87(%198: ptr, %199: bool):
    br bb72(%198, %199)
bb88(%200: ptr, %201: bool):
    br bb72(%200, %201)
bb89(%202: ptr, %203: bool):
    br bb72(%202, %203)
bb90(%204: ptr, %205: bool):
    br bb72(%204, %205)
}

fn @_RNvXsu_NtCskTzINo8ZBH9_5alloc4syncINtB5_3ArcNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprENtNtCs2EYQwhfuABO_4core5clone5Clone5cloneBI_(functy.56) {
}

fn @_RNvXsa_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelENtNtCs2EYQwhfuABO_4core5clone5Clone5cloneBH_(functy.57) {
}

fn @_ExprKind_as_std__clone__Clone___clone(functy.58) {
bb0(%0: ptr, %1: ptr):
    %24 = alloca i64, align 8
    %25 = alloca i64, align 8
    %26 = alloca (i64, i64, i64), align 8
    %27 = alloca i32, align 4
    %28 = alloca (i64, i64, i64), align 8
    %29 = alloca i64, align 8
    %30 = alloca i64, align 8
    %31 = alloca (i8, i8), align 1
    %32 = alloca i64, align 8
    %33 = alloca i64, align 8
    %34 = alloca (i8, i8), align 1
    %35 = alloca i64, align 8
    %36 = alloca i64, align 8
    %37 = alloca i32, align 4
    %38 = alloca i64, align 8
    %39 = alloca i64, align 8
    %40 = alloca i64, align 8
    %41 = alloca (i64, i64), align 8
    %42 = alloca i32, align 4
    %43 = alloca i64, align 8
    %44 = alloca i64, align 8
    store ptr %1, ptr %24
    %45 = load ptr, ptr %24
    %46 = load i8, ptr %45
    %47 = sext i8 %46 to i64
    switch %47 [ 0: bb12 1: bb11 2: bb10 3: bb9 4: bb8 5: bb7 6: bb6 7: bb5 8: bb4 9: bb3 10: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %48 = load ptr, ptr %24
    %49 = const i64 4
    %50 = gep i8, ptr %48, %49
    %51 = load ptr, ptr %24
    %52 = const i64 8
    %53 = gep i8, ptr %51, %52
    %54 = load u32, ptr %50
    call @func.56(%44, %53)
    br bb32(%54)
bb3:
    %55 = load ptr, ptr %24
    %56 = const i64 4
    %57 = gep i8, ptr %55, %56
    %58 = load ptr, ptr %24
    %59 = const i64 8
    %60 = gep i8, ptr %58, %59
    %61 = load ptr, ptr %24
    %62 = const i64 16
    %63 = gep i8, ptr %61, %62
    call @func.71(%42, %57)
    br bb30(%60, %63)
bb4:
    %64 = load ptr, ptr %24
    %65 = const i64 8
    %66 = gep i8, ptr %64, %65
    call @func.91(%41, %66)
    br bb29
bb5:
    %67 = load ptr, ptr %24
    %68 = const i64 4
    %69 = gep i8, ptr %67, %68
    %70 = load ptr, ptr %24
    %71 = const i64 8
    %72 = gep i8, ptr %70, %71
    %73 = load ptr, ptr %24
    %74 = const i64 16
    %75 = gep i8, ptr %73, %74
    %76 = load ptr, ptr %24
    %77 = const i64 24
    %78 = gep i8, ptr %76, %77
    %79 = load ptr, ptr %24
    %80 = const i64 1
    %81 = gep i8, ptr %79, %80
    call @func.71(%37, %69)
    br bb25(%72, %75, %78, %81)
bb6:
    %82 = load ptr, ptr %24
    %83 = const i64 1
    %84 = gep i8, ptr %82, %83
    %85 = load ptr, ptr %24
    %86 = const i64 8
    %87 = gep i8, ptr %85, %86
    %88 = load ptr, ptr %24
    %89 = const i64 16
    %90 = gep i8, ptr %88, %89
    call @func.92(%34, %84)
    br bb22(%87, %90)
bb7:
    %91 = load ptr, ptr %24
    %92 = const i64 1
    %93 = gep i8, ptr %91, %92
    %94 = load ptr, ptr %24
    %95 = const i64 8
    %96 = gep i8, ptr %94, %95
    %97 = load ptr, ptr %24
    %98 = const i64 16
    %99 = gep i8, ptr %97, %98
    call @func.92(%31, %93)
    br bb19(%96, %99)
bb8:
    %100 = load ptr, ptr %24
    %101 = const i64 8
    %102 = gep i8, ptr %100, %101
    %103 = load ptr, ptr %24
    %104 = const i64 16
    %105 = gep i8, ptr %103, %104
    call @func.56(%29, %102)
    br bb17(%105)
bb9:
    %106 = load ptr, ptr %24
    %107 = const i64 4
    %108 = gep i8, ptr %106, %107
    %109 = load ptr, ptr %24
    %110 = const i64 8
    %111 = gep i8, ptr %109, %110
    call @func.71(%27, %108)
    br bb15(%111)
bb10:
    %112 = load ptr, ptr %24
    %113 = const i64 8
    %114 = gep i8, ptr %112, %113
    call @func.48(%26, %114)
    br bb14
bb11:
    %115 = load ptr, ptr %24
    %116 = const i64 8
    %117 = gep i8, ptr %115, %116
    call @func.93(%25, %117)
    br bb13
bb12:
    %118 = load ptr, ptr %24
    %119 = const i64 4
    %120 = gep i8, ptr %118, %119
    %121 = load u32, ptr %120
    %122 = const i64 4
    %123 = gep i8, ptr %0, %122
    store u32 %121, ptr %123
    %124 = const i8 0
    store i8 %124, ptr %0
    br bb33
bb13:
    %125 = const i64 8
    %126 = gep i8, ptr %0, %125
    %127 = load i64, ptr %25
    store i64 %127, ptr %126
    %128 = const i8 1
    store i8 %128, ptr %0
    br bb33
bb14:
    %129 = const i64 8
    %130 = gep i8, ptr %0, %129
    %131 = load i64, ptr %26
    store i64 %131, ptr %130
    %132 = const i64 8
    %133 = gep i8, ptr %26, %132
    %134 = const i64 8
    %135 = gep i8, ptr %130, %134
    %136 = load i64, ptr %133
    store i64 %136, ptr %135
    %137 = const i64 16
    %138 = gep i8, ptr %26, %137
    %139 = const i64 16
    %140 = gep i8, ptr %130, %139
    %141 = load i64, ptr %138
    store i64 %141, ptr %140
    %142 = const i8 2
    store i8 %142, ptr %0
    br bb33
bb15(%2: ptr):
    call @func.57(%28, %2)
    br bb16
bb16:
    %143 = const i64 4
    %144 = gep i8, ptr %0, %143
    %145 = load i32, ptr %27
    store i32 %145, ptr %144
    %146 = const i64 8
    %147 = gep i8, ptr %0, %146
    %148 = load i64, ptr %28
    store i64 %148, ptr %147
    %149 = const i64 8
    %150 = gep i8, ptr %28, %149
    %151 = const i64 8
    %152 = gep i8, ptr %147, %151
    %153 = load i64, ptr %150
    store i64 %153, ptr %152
    %154 = const i64 16
    %155 = gep i8, ptr %28, %154
    %156 = const i64 16
    %157 = gep i8, ptr %147, %156
    %158 = load i64, ptr %155
    store i64 %158, ptr %157
    %159 = const i8 3
    store i8 %159, ptr %0
    br bb33
bb17(%3: ptr):
    call @func.56(%30, %3)
    br bb18
bb18:
    %160 = load ptr, ptr %29
    %161 = const i64 8
    %162 = gep i8, ptr %0, %161
    store ptr %160, ptr %162
    %163 = load ptr, ptr %30
    %164 = const i64 16
    %165 = gep i8, ptr %0, %164
    store ptr %163, ptr %165
    %166 = const i8 4
    store i8 %166, ptr %0
    br bb33
bb19(%4: ptr, %5: ptr):
    call @func.56(%32, %4)
    br bb20(%5)
bb20(%6: ptr):
    call @func.56(%33, %6)
    br bb21
bb21:
    %167 = const i64 1
    %168 = gep i8, ptr %0, %167
    %169 = load i8, ptr %31
    store i8 %169, ptr %168
    %170 = const i64 1
    %171 = gep i8, ptr %31, %170
    %172 = const i64 1
    %173 = gep i8, ptr %168, %172
    %174 = load i8, ptr %171
    store i8 %174, ptr %173
    %175 = load ptr, ptr %32
    %176 = const i64 8
    %177 = gep i8, ptr %0, %176
    store ptr %175, ptr %177
    %178 = load ptr, ptr %33
    %179 = const i64 16
    %180 = gep i8, ptr %0, %179
    store ptr %178, ptr %180
    %181 = const i8 5
    store i8 %181, ptr %0
    br bb33
bb22(%7: ptr, %8: ptr):
    call @func.56(%35, %7)
    br bb23(%8)
bb23(%9: ptr):
    call @func.56(%36, %9)
    br bb24
bb24:
    %182 = const i64 1
    %183 = gep i8, ptr %0, %182
    %184 = load i8, ptr %34
    store i8 %184, ptr %183
    %185 = const i64 1
    %186 = gep i8, ptr %34, %185
    %187 = const i64 1
    %188 = gep i8, ptr %183, %187
    %189 = load i8, ptr %186
    store i8 %189, ptr %188
    %190 = load ptr, ptr %35
    %191 = const i64 8
    %192 = gep i8, ptr %0, %191
    store ptr %190, ptr %192
    %193 = load ptr, ptr %36
    %194 = const i64 16
    %195 = gep i8, ptr %0, %194
    store ptr %193, ptr %195
    %196 = const i8 6
    store i8 %196, ptr %0
    br bb33
bb25(%10: ptr, %11: ptr, %12: ptr, %13: ptr):
    call @func.56(%38, %10)
    br bb26(%11, %12, %13)
bb26(%14: ptr, %15: ptr, %16: ptr):
    call @func.56(%39, %14)
    br bb27(%15, %16)
bb27(%17: ptr, %18: ptr):
    call @func.56(%40, %17)
    br bb28(%18)
bb28(%19: ptr):
    %197 = load bool, ptr %19
    %198 = const i64 4
    %199 = gep i8, ptr %0, %198
    %200 = load i32, ptr %37
    store i32 %200, ptr %199
    %201 = load ptr, ptr %38
    %202 = const i64 8
    %203 = gep i8, ptr %0, %202
    store ptr %201, ptr %203
    %204 = load ptr, ptr %39
    %205 = const i64 16
    %206 = gep i8, ptr %0, %205
    store ptr %204, ptr %206
    %207 = load ptr, ptr %40
    %208 = const i64 24
    %209 = gep i8, ptr %0, %208
    store ptr %207, ptr %209
    %210 = const i64 1
    %211 = gep i8, ptr %0, %210
    store bool %197, ptr %211
    %212 = const i8 7
    store i8 %212, ptr %0
    br bb33
bb29:
    %213 = const i64 8
    %214 = gep i8, ptr %0, %213
    %215 = load i64, ptr %41
    store i64 %215, ptr %214
    %216 = const i64 8
    %217 = gep i8, ptr %41, %216
    %218 = const i64 8
    %219 = gep i8, ptr %214, %218
    %220 = load i64, ptr %217
    store i64 %220, ptr %219
    %221 = const i8 8
    store i8 %221, ptr %0
    br bb33
bb30(%20: ptr, %21: ptr):
    %222 = load u32, ptr %20
    call @func.56(%43, %21)
    br bb31(%222)
bb31(%22: u32):
    %223 = const i64 4
    %224 = gep i8, ptr %0, %223
    %225 = load i32, ptr %42
    store i32 %225, ptr %224
    %226 = const i64 8
    %227 = gep i8, ptr %0, %226
    store u32 %22, ptr %227
    %228 = load ptr, ptr %43
    %229 = const i64 16
    %230 = gep i8, ptr %0, %229
    store ptr %228, ptr %230
    %231 = const i8 9
    store i8 %231, ptr %0
    br bb33
bb32(%23: u32):
    %232 = const i64 4
    %233 = gep i8, ptr %0, %232
    store u32 %23, ptr %233
    %234 = load ptr, ptr %44
    %235 = const i64 8
    %236 = gep i8, ptr %0, %235
    store ptr %234, ptr %236
    %237 = const i8 10
    store i8 %237, ptr %0
    br bb33
bb33:
    ret
}

fn @_ExprMeta_as_std__clone__Clone___clone(functy.59) {
bb0(%0: ptr, %1: ptr):
    %2 = load i64, ptr %1
    store i64 %2, ptr %0
    ret
}

fn @Verifier____env___const_type(functy.60) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %5 = alloca (i64, i64, i64, i64, i64), align 8
    %6 = alloca (i64, i64, i64, i64, i64), align 8
    %7 = alloca (i64, i64, i64, i64, i64), align 8
    %8 = alloca (i64, i64, i64, i64, i64), align 8
    call @func.95(%5, %1, %2)
    br bb1(%1)
bb1(%3: ptr):
    %9 = load i8, ptr %5
    %10 = const i8 11
    %11 = icmp eq i8 %9, %10
    %12 = const i64 0
    %13 = const i64 1
    %14 = select i64 %11, %12, %13
    switch %14 [ 0: bb3 1: bb4(%3) default: bb2 ]
bb2:
    unreachable
bb3:
    %15 = const i8 11
    store i8 %15, ptr %0
    br bb11
bb4(%4: ptr):
    %16 = load i64, ptr %5
    store i64 %16, ptr %6
    %17 = const i64 8
    %18 = gep i8, ptr %5, %17
    %19 = const i64 8
    %20 = gep i8, ptr %6, %19
    %21 = load i64, ptr %18
    store i64 %21, ptr %20
    %22 = const i64 16
    %23 = gep i8, ptr %5, %22
    %24 = const i64 16
    %25 = gep i8, ptr %6, %24
    %26 = load i64, ptr %23
    store i64 %26, ptr %25
    %27 = const i64 24
    %28 = gep i8, ptr %5, %27
    %29 = const i64 24
    %30 = gep i8, ptr %6, %29
    %31 = load i64, ptr %28
    store i64 %31, ptr %30
    %32 = const i64 32
    %33 = gep i8, ptr %5, %32
    %34 = const i64 32
    %35 = gep i8, ptr %6, %34
    %36 = load i64, ptr %33
    store i64 %36, ptr %35
    call @func.34(%7, %4, %6)
    br bb5
bb5:
    %37 = load i8, ptr %7
    %38 = const i8 11
    %39 = icmp eq i8 %37, %38
    %40 = const i64 1
    %41 = const i64 0
    %42 = select i64 %39, %40, %41
    switch %42 [ 0: bb7 1: bb6 default: bb2 ]
bb6:
    %43 = const i8 11
    store i8 %43, ptr %0
    br bb10
bb7:
    %44 = load i64, ptr %7
    store i64 %44, ptr %8
    %45 = const i64 8
    %46 = gep i8, ptr %7, %45
    %47 = const i64 8
    %48 = gep i8, ptr %8, %47
    %49 = load i64, ptr %46
    store i64 %49, ptr %48
    %50 = const i64 16
    %51 = gep i8, ptr %7, %50
    %52 = const i64 16
    %53 = gep i8, ptr %8, %52
    %54 = load i64, ptr %51
    store i64 %54, ptr %53
    %55 = const i64 24
    %56 = gep i8, ptr %7, %55
    %57 = const i64 24
    %58 = gep i8, ptr %8, %57
    %59 = load i64, ptr %56
    store i64 %59, ptr %58
    %60 = const i64 32
    %61 = gep i8, ptr %7, %60
    %62 = const i64 32
    %63 = gep i8, ptr %8, %62
    %64 = load i64, ptr %61
    store i64 %64, ptr %63
    %65 = load i64, ptr %8
    store i64 %65, ptr %0
    %66 = const i64 8
    %67 = gep i8, ptr %8, %66
    %68 = const i64 8
    %69 = gep i8, ptr %0, %68
    %70 = load i64, ptr %67
    store i64 %70, ptr %69
    %71 = const i64 16
    %72 = gep i8, ptr %8, %71
    %73 = const i64 16
    %74 = gep i8, ptr %0, %73
    %75 = load i64, ptr %72
    store i64 %75, ptr %74
    %76 = const i64 24
    %77 = gep i8, ptr %8, %76
    %78 = const i64 24
    %79 = gep i8, ptr %0, %78
    %80 = load i64, ptr %77
    store i64 %80, ptr %79
    %81 = const i64 32
    %82 = gep i8, ptr %8, %81
    %83 = const i64 32
    %84 = gep i8, ptr %0, %83
    %85 = load i64, ptr %82
    store i64 %85, ptr %84
    br bb10
bb8:
    br bb11
bb9:
    br bb8
bb10:
    %86 = load i8, ptr %7
    %87 = const i8 11
    %88 = icmp eq i8 %86, %87
    %89 = const i64 1
    %90 = const i64 0
    %91 = select i64 %88, %89, %90
    switch %91 [ 0: bb8 1: bb9 default: bb2 ]
bb11:
    ret
}

fn @Level__succ(functy.61) {
bb0(%0: ptr, %1: ptr):
    %2 = alloca i64, align 8
    call @func.79(%2, %1)
    br bb1
bb1:
    %3 = load ptr, ptr %2
    %4 = const i64 8
    %5 = gep i8, ptr %0, %4
    store ptr %3, ptr %5
    %6 = const i32 1
    store i32 %6, ptr %0
    ret
}

fn @Expr__sort(functy.62) {
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
    %11 = const i64 16
    %12 = gep i8, ptr %1, %11
    %13 = const i64 16
    %14 = gep i8, ptr %4, %13
    %15 = load i64, ptr %12
    store i64 %15, ptr %14
    %16 = const i8 2
    store i8 %16, ptr %2
    call @func.96(%0, %2)
    br bb1
bb1:
    ret
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm14saturating_add(functy.63) {
}

fn @Expr__lift_at(functy.64) {
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
    call @func.36(%0, %73)
    br bb31
bb2(%4: u32, %5: u32):
    %74 = load ptr, ptr %58
    %75 = call @func.97(%74)
    br bb3(%4, %5, %75)
bb3(%6: u32, %7: u32, %8: u32):
    %76 = icmp uge u32 %6, %8
    condbr %76, bb4, bb5(%6, %7)
bb4:
    %77 = load ptr, ptr %58
    call @func.36(%0, %77)
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
    call @func.36(%0, %82)
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
    %134 = call @func.63(%133, %19)
    br bb12(%134)
bb12(%21: u32):
    call @func.98(%0, %21)
    br bb31
bb13:
    %135 = load ptr, ptr %58
    call @func.36(%0, %135)
    br bb31
bb14(%22: u32, %23: u32, %24: ptr, %25: ptr):
    %136 = const bool true
    call @func.64(%60, %25, %22, %23)
    br bb15(%22, %23, %24)
bb15(%26: u32, %27: u32, %28: ptr):
    %137 = load ptr, ptr %28
    %138 = const i64 16
    %139 = gep i8, ptr %137, %138
    br bb16(%26, %27, %139)
bb16(%29: u32, %30: u32, %31: ptr):
    call @func.64(%61, %31, %29, %30)
    br bb17
bb17:
    %140 = const bool false
    call @func.99(%0, %60, %61)
    br bb18
bb18:
    %141 = const bool false
    br bb31
bb19(%32: u32, %33: u32, %34: ptr, %35: ptr):
    %142 = const bool true
    call @func.64(%63, %35, %32, %33)
    br bb20(%32, %33, %34)
bb20(%36: u32, %37: u32, %38: ptr):
    %143 = load ptr, ptr %38
    %144 = const i64 16
    %145 = gep i8, ptr %143, %144
    br bb21(%36, %37, %145)
bb21(%39: u32, %40: u32, %41: ptr):
    %146 = const u32 1
    %147 = call @func.63(%39, %146)
    br bb22(%40, %41, %147)
bb22(%42: u32, %43: ptr, %44: u32):
    call @func.64(%64, %43, %44, %42)
    br bb23
bb23:
    %148 = const bool false
    call @func.100(%0, %62, %63, %64)
    br bb24
bb24:
    %149 = const bool false
    br bb31
bb25(%45: u32, %46: u32, %47: ptr, %48: ptr):
    %150 = const bool true
    call @func.64(%66, %48, %45, %46)
    br bb26(%45, %46, %47)
bb26(%49: u32, %50: u32, %51: ptr):
    %151 = load ptr, ptr %51
    %152 = const i64 16
    %153 = gep i8, ptr %151, %152
    br bb27(%49, %50, %153)
bb27(%52: u32, %53: u32, %54: ptr):
    %154 = const u32 1
    %155 = call @func.63(%52, %154)
    br bb28(%53, %54, %155)
bb28(%55: u32, %56: ptr, %57: u32):
    call @func.64(%67, %56, %57, %55)
    br bb29
bb29:
    %156 = const bool false
    call @func.66(%0, %65, %66, %67)
    br bb30
bb30:
    %157 = const bool false
    br bb31
bb31:
    ret
}

fn @Expr__instantiate(functy.65) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %3 = const u32 0
    call @func.103(%0, %1, %2, %3)
    br bb1
bb1:
    ret
}

fn @Expr__pi(functy.66) {
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
    call @func.96(%0, %4)
    br bb3
bb3:
    ret
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE3newBE_(functy.67) {
}

fn @Expr__cnst(functy.68) {
bb0(%0: ptr, %1: u32):
    %2 = alloca i32, align 4
    %3 = alloca (i64, i64, i64, i64), align 8
    %4 = alloca (i64, i64, i64), align 8
    store u32 %1, ptr %2
    call @func.67(%4)
    br bb1
bb1:
    %5 = const i64 4
    %6 = gep i8, ptr %3, %5
    %7 = load i32, ptr %2
    store i32 %7, ptr %6
    %8 = const i64 8
    %9 = gep i8, ptr %3, %8
    %10 = load i64, ptr %4
    store i64 %10, ptr %9
    %11 = const i64 8
    %12 = gep i8, ptr %4, %11
    %13 = const i64 8
    %14 = gep i8, ptr %9, %13
    %15 = load i64, ptr %12
    store i64 %15, ptr %14
    %16 = const i64 16
    %17 = gep i8, ptr %4, %16
    %18 = const i64 16
    %19 = gep i8, ptr %9, %18
    %20 = load i64, ptr %17
    store i64 %20, ptr %19
    %21 = const i8 3
    store i8 %21, ptr %3
    call @func.96(%0, %3)
    br bb2
bb2:
    ret
}

fn @_RNvXsu_NtCskTzINo8ZBH9_5alloc4syncINtB5_3ArcNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprENtNtCs2EYQwhfuABO_4core5clone5Clone5cloneBI_(functy.69) {
}

fn @Verifier____env___whnf_inner(functy.70) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %62 = alloca i64, align 8
    %63 = alloca i64, align 8
    %64 = alloca (i64, i64, i64, i64, i64), align 8
    %65 = alloca i64, align 8
    %66 = alloca (i64, i64, i64, i64, i64), align 8
    %67 = alloca (i64, i64, i64, i64, i64), align 8
    %68 = alloca (i64, i64, i64, i64), align 8
    %69 = alloca i64, align 8
    %70 = alloca (i64, i64, i64, i64, i64), align 8
    %71 = alloca i64, align 8
    %72 = alloca (i64, i64, i64, i64, i64), align 8
    %73 = alloca (i64, i64, i64, i64, i64), align 8
    %74 = alloca (i64, i64, i64, i64, i64), align 8
    %75 = alloca (i64, i64, i64, i64, i64), align 8
    %76 = alloca (i64, i64, i64, i64, i64), align 8
    %77 = alloca (i64, i64, i64, i64, i64), align 8
    %78 = alloca (i64, i64, i64, i64, i64), align 8
    store ptr %2, ptr %62
    %79 = const bool false
    %80 = load ptr, ptr %62
    store ptr %80, ptr %63
    %81 = load ptr, ptr %63
    %82 = load i8, ptr %81
    %83 = sext i8 %82 to i64
    switch %83 [ 3: bb4(%1) 4: bb6(%1) 7: bb5(%1) 9: bb3(%1) 10: bb2(%1) default: bb1 ]
bb1:
    %84 = load ptr, ptr %62
    call @func.36(%0, %84)
    br bb40
bb2(%3: ptr):
    %85 = load ptr, ptr %63
    %86 = const i64 8
    %87 = gep i8, ptr %85, %86
    %88 = load ptr, ptr %87
    %89 = const i64 16
    %90 = gep i8, ptr %88, %89
    br bb37(%3, %90)
bb3(%4: ptr):
    %91 = load ptr, ptr %63
    %92 = const i64 4
    %93 = gep i8, ptr %91, %92
    %94 = load ptr, ptr %63
    %95 = const i64 8
    %96 = gep i8, ptr %94, %95
    %97 = load ptr, ptr %63
    %98 = const i64 16
    %99 = gep i8, ptr %97, %98
    %100 = load u32, ptr %96
    %101 = load ptr, ptr %99
    %102 = const i64 16
    %103 = gep i8, ptr %101, %102
    br bb36(%4, %93, %100, %103)
bb4(%5: ptr):
    %104 = load ptr, ptr %63
    %105 = const i64 4
    %106 = gep i8, ptr %104, %105
    %107 = load ptr, ptr %63
    %108 = const i64 8
    %109 = gep i8, ptr %107, %108
    call @func.95(%77, %5, %106)
    br bb31(%5)
bb5(%6: ptr):
    %110 = load ptr, ptr %63
    %111 = const i64 16
    %112 = gep i8, ptr %110, %111
    %113 = load ptr, ptr %63
    %114 = const i64 24
    %115 = gep i8, ptr %113, %114
    %116 = load ptr, ptr %115
    %117 = const i64 16
    %118 = gep i8, ptr %116, %117
    br bb27(%6, %112, %118)
bb6(%7: ptr):
    %119 = load ptr, ptr %63
    %120 = const i64 8
    %121 = gep i8, ptr %119, %120
    %122 = load ptr, ptr %63
    %123 = const i64 16
    %124 = gep i8, ptr %122, %123
    %125 = load ptr, ptr %121
    %126 = const i64 16
    %127 = gep i8, ptr %125, %126
    br bb7(%7, %124, %127)
bb7(%8: ptr, %9: ptr, %10: ptr):
    %128 = const bool true
    call @func.46(%64, %8, %10)
    br bb8(%8, %9, %128)
bb8(%11: ptr, %12: ptr, %13: bool):
    store ptr %64, ptr %65
    %129 = load ptr, ptr %65
    %130 = load i8, ptr %129
    %131 = sext i8 %130 to i64
    switch %131 [ 5: bb10(%11, %12, %13) default: bb9(%11, %12) ]
bb9(%14: ptr, %15: ptr):
    %132 = const bool false
    %133 = load i64, ptr %64
    store i64 %133, ptr %70
    %134 = const i64 8
    %135 = gep i8, ptr %64, %134
    %136 = const i64 8
    %137 = gep i8, ptr %70, %136
    %138 = load i64, ptr %135
    store i64 %138, ptr %137
    %139 = const i64 16
    %140 = gep i8, ptr %64, %139
    %141 = const i64 16
    %142 = gep i8, ptr %70, %141
    %143 = load i64, ptr %140
    store i64 %143, ptr %142
    %144 = const i64 24
    %145 = gep i8, ptr %64, %144
    %146 = const i64 24
    %147 = gep i8, ptr %70, %146
    %148 = load i64, ptr %145
    store i64 %148, ptr %147
    %149 = const i64 32
    %150 = gep i8, ptr %64, %149
    %151 = const i64 32
    %152 = gep i8, ptr %70, %151
    %153 = load i64, ptr %150
    store i64 %153, ptr %152
    %154 = const i64 56
    %155 = heap_alloc rust_heap i8, %154, align 8
    %156 = const u64 1
    store u64 %156, ptr %155
    %157 = const i64 8
    %158 = gep i8, ptr %155, %157
    %159 = const u64 1
    store u64 %159, ptr %158
    %160 = const i64 16
    %161 = gep i8, ptr %155, %160
    %162 = load i64, ptr %70
    store i64 %162, ptr %161
    %163 = const i64 8
    %164 = gep i8, ptr %70, %163
    %165 = const i64 8
    %166 = gep i8, ptr %161, %165
    %167 = load i64, ptr %164
    store i64 %167, ptr %166
    %168 = const i64 16
    %169 = gep i8, ptr %70, %168
    %170 = const i64 16
    %171 = gep i8, ptr %161, %170
    %172 = load i64, ptr %169
    store i64 %172, ptr %171
    %173 = const i64 24
    %174 = gep i8, ptr %70, %173
    %175 = const i64 24
    %176 = gep i8, ptr %161, %175
    %177 = load i64, ptr %174
    store i64 %177, ptr %176
    %178 = const i64 32
    %179 = gep i8, ptr %70, %178
    %180 = const i64 32
    %181 = gep i8, ptr %161, %180
    %182 = load i64, ptr %179
    store i64 %182, ptr %181
    store ptr %155, ptr %69
    br bb15(%14, %15, %132)
bb10(%16: ptr, %17: ptr, %18: bool):
    %183 = load ptr, ptr %65
    %184 = const i64 16
    %185 = gep i8, ptr %183, %184
    %186 = load ptr, ptr %185
    %187 = const i64 16
    %188 = gep i8, ptr %186, %187
    br bb11(%16, %17, %188, %18)
bb11(%19: ptr, %20: ptr, %21: ptr, %22: bool):
    %189 = load ptr, ptr %20
    %190 = const i64 16
    %191 = gep i8, ptr %189, %190
    br bb12(%19, %21, %191, %22)
bb12(%23: ptr, %24: ptr, %25: ptr, %26: bool):
    call @func.65(%66, %24, %25)
    br bb13(%23, %26)
bb13(%27: ptr, %28: bool):
    call @func.46(%0, %27, %66)
    br bb14(%28)
bb14(%29: bool):
    br bb42(%29)
bb15(%30: ptr, %31: ptr, %32: bool):
    call @func.69(%71, %31)
    br bb16(%30, %32)
bb16(%33: ptr, %34: bool):
    %192 = load ptr, ptr %69
    %193 = const i64 8
    %194 = gep i8, ptr %68, %193
    store ptr %192, ptr %194
    %195 = load ptr, ptr %71
    %196 = const i64 16
    %197 = gep i8, ptr %68, %196
    store ptr %195, ptr %197
    %198 = const i8 4
    store i8 %198, ptr %68
    call @func.96(%67, %68)
    br bb17(%33, %34)
bb17(%35: ptr, %36: bool):
    call @func.104(%72, %35, %67)
    br bb18(%35, %36)
bb18(%37: ptr, %38: bool):
    %199 = load i8, ptr %72
    %200 = const i8 11
    %201 = icmp eq i8 %199, %200
    %202 = const i64 0
    %203 = const i64 1
    %204 = select i64 %201, %202, %203
    switch %204 [ 1: bb19(%37) 0: bb21(%37, %38) default: bb32 ]
bb19(%39: ptr):
    %205 = load i64, ptr %72
    store i64 %205, ptr %73
    %206 = const i64 8
    %207 = gep i8, ptr %72, %206
    %208 = const i64 8
    %209 = gep i8, ptr %73, %208
    %210 = load i64, ptr %207
    store i64 %210, ptr %209
    %211 = const i64 16
    %212 = gep i8, ptr %72, %211
    %213 = const i64 16
    %214 = gep i8, ptr %73, %213
    %215 = load i64, ptr %212
    store i64 %215, ptr %214
    %216 = const i64 24
    %217 = gep i8, ptr %72, %216
    %218 = const i64 24
    %219 = gep i8, ptr %73, %218
    %220 = load i64, ptr %217
    store i64 %220, ptr %219
    %221 = const i64 32
    %222 = gep i8, ptr %72, %221
    %223 = const i64 32
    %224 = gep i8, ptr %73, %223
    %225 = load i64, ptr %222
    store i64 %225, ptr %224
    call @func.46(%0, %39, %73)
    br bb20
bb20:
    br bb38
bb21(%40: ptr, %41: bool):
    call @func.105(%74, %40, %67)
    br bb22(%40, %41)
bb22(%42: ptr, %43: bool):
    %226 = load i8, ptr %74
    %227 = const i8 11
    %228 = icmp eq i8 %226, %227
    %229 = const i64 0
    %230 = const i64 1
    %231 = select i64 %228, %229, %230
    switch %231 [ 1: bb23(%42) 0: bb25(%43) default: bb32 ]
bb23(%44: ptr):
    %232 = load i64, ptr %74
    store i64 %232, ptr %75
    %233 = const i64 8
    %234 = gep i8, ptr %74, %233
    %235 = const i64 8
    %236 = gep i8, ptr %75, %235
    %237 = load i64, ptr %234
    store i64 %237, ptr %236
    %238 = const i64 16
    %239 = gep i8, ptr %74, %238
    %240 = const i64 16
    %241 = gep i8, ptr %75, %240
    %242 = load i64, ptr %239
    store i64 %242, ptr %241
    %243 = const i64 24
    %244 = gep i8, ptr %74, %243
    %245 = const i64 24
    %246 = gep i8, ptr %75, %245
    %247 = load i64, ptr %244
    store i64 %247, ptr %246
    %248 = const i64 32
    %249 = gep i8, ptr %74, %248
    %250 = const i64 32
    %251 = gep i8, ptr %75, %250
    %252 = load i64, ptr %249
    store i64 %252, ptr %251
    call @func.46(%0, %44, %75)
    br bb24
bb24:
    br bb38
bb25(%45: bool):
    %253 = load i64, ptr %67
    store i64 %253, ptr %0
    %254 = const i64 8
    %255 = gep i8, ptr %67, %254
    %256 = const i64 8
    %257 = gep i8, ptr %0, %256
    %258 = load i64, ptr %255
    store i64 %258, ptr %257
    %259 = const i64 16
    %260 = gep i8, ptr %67, %259
    %261 = const i64 16
    %262 = gep i8, ptr %0, %261
    %263 = load i64, ptr %260
    store i64 %263, ptr %262
    %264 = const i64 24
    %265 = gep i8, ptr %67, %264
    %266 = const i64 24
    %267 = gep i8, ptr %0, %266
    %268 = load i64, ptr %265
    store i64 %268, ptr %267
    %269 = const i64 32
    %270 = gep i8, ptr %67, %269
    %271 = const i64 32
    %272 = gep i8, ptr %0, %271
    %273 = load i64, ptr %270
    store i64 %273, ptr %272
    br bb42(%45)
bb26:
    %274 = const bool false
    br bb40
bb27(%46: ptr, %47: ptr, %48: ptr):
    %275 = load ptr, ptr %47
    %276 = const i64 16
    %277 = gep i8, ptr %275, %276
    br bb28(%46, %48, %277)
bb28(%49: ptr, %50: ptr, %51: ptr):
    call @func.65(%76, %50, %51)
    br bb29(%49)
bb29(%52: ptr):
    call @func.46(%0, %52, %76)
    br bb30
bb30:
    br bb40
bb31(%53: ptr):
    %278 = load i8, ptr %77
    %279 = const i8 11
    %280 = icmp eq i8 %278, %279
    %281 = const i64 0
    %282 = const i64 1
    %283 = select i64 %280, %281, %282
    switch %283 [ 0: bb33 1: bb34(%53) default: bb32 ]
bb32:
    unreachable
bb33:
    %284 = load ptr, ptr %62
    call @func.36(%0, %284)
    br bb40
bb34(%54: ptr):
    %285 = load i64, ptr %77
    store i64 %285, ptr %78
    %286 = const i64 8
    %287 = gep i8, ptr %77, %286
    %288 = const i64 8
    %289 = gep i8, ptr %78, %288
    %290 = load i64, ptr %287
    store i64 %290, ptr %289
    %291 = const i64 16
    %292 = gep i8, ptr %77, %291
    %293 = const i64 16
    %294 = gep i8, ptr %78, %293
    %295 = load i64, ptr %292
    store i64 %295, ptr %294
    %296 = const i64 24
    %297 = gep i8, ptr %77, %296
    %298 = const i64 24
    %299 = gep i8, ptr %78, %298
    %300 = load i64, ptr %297
    store i64 %300, ptr %299
    %301 = const i64 32
    %302 = gep i8, ptr %77, %301
    %303 = const i64 32
    %304 = gep i8, ptr %78, %303
    %305 = load i64, ptr %302
    store i64 %305, ptr %304
    call @func.46(%0, %54, %78)
    br bb35
bb35:
    br bb40
bb36(%55: ptr, %56: ptr, %57: u32, %58: ptr):
    call @func.108(%0, %55, %56, %57, %58)
    br bb40
bb37(%59: ptr, %60: ptr):
    call @func.46(%0, %59, %60)
    br bb40
bb38:
    br bb39
bb39:
    %306 = const bool false
    br bb40
bb40:
    ret
bb41:
    br bb26
bb42(%61: bool):
    condbr %61, bb41, bb26
}

fn @_Name_as_std__clone__Clone___clone(functy.71) {
bb0(%0: ptr, %1: ptr):
    %2 = load i32, ptr %1
    store i32 %2, ptr %0
    ret
}

fn @Level__is_nonzero(functy.72) {
bb0(%0: ptr):
    %9 = alloca i64, align 8
    store ptr %0, ptr %9
    %10 = load ptr, ptr %9
    %11 = load i32, ptr %10
    %12 = sext i32 %11 to i64
    switch %12 [ 0: bb5 1: bb4 2: bb3 3: bb2 4: bb5 default: bb1 ]
bb1:
    unreachable
bb2:
    %13 = load ptr, ptr %9
    %14 = const i64 16
    %15 = gep i8, ptr %13, %14
    %16 = load ptr, ptr %15
    %17 = const i64 16
    %18 = gep i8, ptr %16, %17
    br bb11(%18)
bb3:
    %19 = load ptr, ptr %9
    %20 = const i64 8
    %21 = gep i8, ptr %19, %20
    %22 = load ptr, ptr %9
    %23 = const i64 16
    %24 = gep i8, ptr %22, %23
    %25 = load ptr, ptr %21
    %26 = const i64 16
    %27 = gep i8, ptr %25, %26
    br bb6(%24, %27)
bb4:
    %28 = const bool true
    br bb12(%28)
bb5:
    %29 = const bool false
    br bb12(%29)
bb6(%1: ptr, %2: ptr):
    %30 = call @func.72(%2)
    br bb7(%1, %30)
bb7(%3: ptr, %4: bool):
    condbr %4, bb8, bb9(%3)
bb8:
    %31 = const bool true
    br bb12(%31)
bb9(%5: ptr):
    %32 = load ptr, ptr %5
    %33 = const i64 16
    %34 = gep i8, ptr %32, %33
    br bb10(%34)
bb10(%6: ptr):
    %35 = call @func.72(%6)
    br bb12(%35)
bb11(%7: ptr):
    %36 = call @func.72(%7)
    br bb12(%36)
bb12(%8: bool):
    ret %8
}

fn @Level__max(functy.73) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %21 = alloca i64, align 8
    %22 = alloca (i64, i64, i64), align 8
    %23 = alloca i64, align 8
    %24 = alloca (i64, i64, i64), align 8
    %25 = const bool false
    %26 = const bool false
    %27 = const bool true
    %28 = const bool true
    %29 = call @func.78(%1, %2)
    br bb1(%29, %28, %27)
bb1(%3: bool, %4: bool, %5: bool):
    condbr %3, bb2(%4), bb3(%4, %5)
bb2(%6: bool):
    %30 = const bool false
    %31 = load i64, ptr %1
    store i64 %31, ptr %0
    %32 = const i64 8
    %33 = gep i8, ptr %1, %32
    %34 = const i64 8
    %35 = gep i8, ptr %0, %34
    %36 = load i64, ptr %33
    store i64 %36, ptr %35
    %37 = const i64 16
    %38 = gep i8, ptr %1, %37
    %39 = const i64 16
    %40 = gep i8, ptr %0, %39
    %41 = load i64, ptr %38
    store i64 %41, ptr %40
    br bb15(%6, %30)
bb3(%7: bool, %8: bool):
    %42 = call @func.15(%1)
    br bb4(%42, %7, %8)
bb4(%9: bool, %10: bool, %11: bool):
    condbr %9, bb5(%11), bb6(%10)
bb5(%12: bool):
    %43 = const bool false
    %44 = load i64, ptr %2
    store i64 %44, ptr %0
    %45 = const i64 8
    %46 = gep i8, ptr %2, %45
    %47 = const i64 8
    %48 = gep i8, ptr %0, %47
    %49 = load i64, ptr %46
    store i64 %49, ptr %48
    %50 = const i64 16
    %51 = gep i8, ptr %2, %50
    %52 = const i64 16
    %53 = gep i8, ptr %0, %52
    %54 = load i64, ptr %51
    store i64 %54, ptr %53
    br bb15(%43, %12)
bb6(%13: bool):
    %55 = call @func.15(%2)
    br bb7(%55, %13)
bb7(%14: bool, %15: bool):
    condbr %14, bb8(%15), bb9
bb8(%16: bool):
    %56 = const bool false
    %57 = load i64, ptr %1
    store i64 %57, ptr %0
    %58 = const i64 8
    %59 = gep i8, ptr %1, %58
    %60 = const i64 8
    %61 = gep i8, ptr %0, %60
    %62 = load i64, ptr %59
    store i64 %62, ptr %61
    %63 = const i64 16
    %64 = gep i8, ptr %1, %63
    %65 = const i64 16
    %66 = gep i8, ptr %0, %65
    %67 = load i64, ptr %64
    store i64 %67, ptr %66
    br bb15(%16, %56)
bb9:
    %68 = const bool false
    %69 = load i64, ptr %1
    store i64 %69, ptr %22
    %70 = const i64 8
    %71 = gep i8, ptr %1, %70
    %72 = const i64 8
    %73 = gep i8, ptr %22, %72
    %74 = load i64, ptr %71
    store i64 %74, ptr %73
    %75 = const i64 16
    %76 = gep i8, ptr %1, %75
    %77 = const i64 16
    %78 = gep i8, ptr %22, %77
    %79 = load i64, ptr %76
    store i64 %79, ptr %78
    call @func.79(%21, %22)
    br bb10
bb10:
    %80 = const bool false
    %81 = load i64, ptr %2
    store i64 %81, ptr %24
    %82 = const i64 8
    %83 = gep i8, ptr %2, %82
    %84 = const i64 8
    %85 = gep i8, ptr %24, %84
    %86 = load i64, ptr %83
    store i64 %86, ptr %85
    %87 = const i64 16
    %88 = gep i8, ptr %2, %87
    %89 = const i64 16
    %90 = gep i8, ptr %24, %89
    %91 = load i64, ptr %88
    store i64 %91, ptr %90
    call @func.79(%23, %24)
    br bb11
bb11:
    %92 = load ptr, ptr %21
    %93 = const i64 8
    %94 = gep i8, ptr %0, %93
    store ptr %92, ptr %94
    %95 = load ptr, ptr %23
    %96 = const i64 16
    %97 = gep i8, ptr %0, %96
    store ptr %95, ptr %97
    %98 = const i32 2
    store i32 %98, ptr %0
    br bb13
bb12(%17: bool):
    condbr %17, bb16, bb13
bb13:
    ret
bb14(%18: bool):
    br bb12(%18)
bb15(%19: bool, %20: bool):
    condbr %19, bb14(%20), bb12(%20)
bb16:
    br bb13
}

fn @Level__zero(functy.74) {
bb0(%0: ptr):
    %1 = const i32 0
    store i32 %1, ptr %0
    ret
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecTRNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelBF_EE3popBI_(functy.75) {
}

fn @_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCshhXhIKvfvMU_25clean_decl_universe_slice4NameNtB7_9PartialEq2neBF_(functy.76) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecTRNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelBG_EE4pushBJ_(functy.77) {
}

fn @_Level_as_std__cmp__PartialEq___eq(functy.78) {
bb0(%0: ptr, %1: ptr):
    %37 = alloca (i64, i64, i64), align 8
    %38 = alloca i64, align 8
    %39 = alloca (i64, i64), align 8
    %40 = alloca (i64, i64), align 8
    %41 = alloca (i64, i64), align 8
    %42 = alloca (i64, i64), align 8
    %43 = alloca (i64, i64), align 8
    %44 = alloca (i64, i64), align 8
    %45 = alloca i64, align 8
    %46 = alloca i64, align 8
    %47 = alloca i64, align 8
    %48 = alloca i64, align 8
    %49 = alloca i64, align 8
    %50 = alloca i64, align 8
    %51 = alloca i64, align 8
    %52 = alloca i64, align 8
    %53 = alloca i64, align 8
    %54 = alloca i64, align 8
    %55 = alloca i64, align 8
    %56 = alloca i64, align 8
    %57 = alloca i64, align 8
    %58 = alloca i64, align 8
    %59 = const i64 16
    %60 = heap_alloc rust_heap i8, %59, align 8
    store ptr %60, ptr %38
    br bb1(%0, %1)
bb1(%2: ptr, %3: ptr):
    store ptr %2, ptr %39
    %61 = const i64 8
    %62 = gep i8, ptr %39, %61
    store ptr %3, ptr %62
    %63 = load ptr, ptr %38
    %64 = ptrtoint ptr %63 to u64
    %65 = const u64 8
    %66 = const u64 1
    %67 = sub u64 %65, %66
    %68 = and u64 %64, %67
    %69 = const u64 0
    %70 = icmp eq u64 %68, %69
    condbr %70, bb28(%63), bb33
bb2:
    call @func.75(%40, %37)
    br bb3
bb3:
    %71 = load i64, ptr %40
    %72 = const i64 0
    %73 = icmp eq i64 %71, %72
    %74 = const i64 0
    %75 = const i64 1
    %76 = select i64 %73, %74, %75
    switch %76 [ 1: bb4 0: bb25 default: bb30 ]
bb4:
    %77 = load ptr, ptr %40
    %78 = const i64 8
    %79 = gep i8, ptr %40, %78
    %80 = load ptr, ptr %79
    store ptr %77, ptr %41
    %81 = const i64 8
    %82 = gep i8, ptr %41, %81
    store ptr %80, ptr %82
    %83 = load ptr, ptr %41
    %84 = load i32, ptr %83
    %85 = sext i32 %84 to i64
    switch %85 [ 0: bb6 1: bb7 2: bb8 3: bb9 4: bb10 default: bb30 ]
bb5:
    %86 = const bool false
    br bb26(%86)
bb6:
    %87 = const i64 8
    %88 = gep i8, ptr %41, %87
    %89 = load ptr, ptr %88
    %90 = load i32, ptr %89
    %91 = sext i32 %90 to i64
    switch %91 [ 0: bb2 default: bb5 ]
bb7:
    %92 = const i64 8
    %93 = gep i8, ptr %41, %92
    %94 = load ptr, ptr %93
    %95 = load i32, ptr %94
    %96 = sext i32 %95 to i64
    switch %96 [ 1: bb14 default: bb5 ]
bb8:
    %97 = const i64 8
    %98 = gep i8, ptr %41, %97
    %99 = load ptr, ptr %98
    %100 = load i32, ptr %99
    %101 = sext i32 %100 to i64
    switch %101 [ 2: bb13 default: bb5 ]
bb9:
    %102 = const i64 8
    %103 = gep i8, ptr %41, %102
    %104 = load ptr, ptr %103
    %105 = load i32, ptr %104
    %106 = sext i32 %105 to i64
    switch %106 [ 3: bb12 default: bb5 ]
bb10:
    %107 = const i64 8
    %108 = gep i8, ptr %41, %107
    %109 = load ptr, ptr %108
    %110 = load i32, ptr %109
    %111 = sext i32 %110 to i64
    switch %111 [ 4: bb11 default: bb5 ]
bb11:
    %112 = load ptr, ptr %41
    store ptr %112, ptr %47
    %113 = load ptr, ptr %47
    %114 = const i64 4
    %115 = gep i8, ptr %113, %114
    store ptr %115, ptr %45
    %116 = const i64 8
    %117 = gep i8, ptr %41, %116
    %118 = load ptr, ptr %117
    store ptr %118, ptr %48
    %119 = load ptr, ptr %48
    %120 = const i64 4
    %121 = gep i8, ptr %119, %120
    store ptr %121, ptr %46
    %122 = call @func.76(%45, %46)
    br bb23(%122)
bb12:
    %123 = load ptr, ptr %41
    store ptr %123, ptr %49
    %124 = load ptr, ptr %49
    %125 = const i64 8
    %126 = gep i8, ptr %124, %125
    %127 = load ptr, ptr %41
    store ptr %127, ptr %50
    %128 = load ptr, ptr %50
    %129 = const i64 16
    %130 = gep i8, ptr %128, %129
    %131 = const i64 8
    %132 = gep i8, ptr %41, %131
    %133 = load ptr, ptr %132
    store ptr %133, ptr %51
    %134 = load ptr, ptr %51
    %135 = const i64 8
    %136 = gep i8, ptr %134, %135
    %137 = const i64 8
    %138 = gep i8, ptr %41, %137
    %139 = load ptr, ptr %138
    store ptr %139, ptr %52
    %140 = load ptr, ptr %52
    %141 = const i64 16
    %142 = gep i8, ptr %140, %141
    br bb17(%126, %130, %136, %142)
bb13:
    %143 = load ptr, ptr %41
    store ptr %143, ptr %53
    %144 = load ptr, ptr %53
    %145 = const i64 8
    %146 = gep i8, ptr %144, %145
    %147 = load ptr, ptr %41
    store ptr %147, ptr %54
    %148 = load ptr, ptr %54
    %149 = const i64 16
    %150 = gep i8, ptr %148, %149
    %151 = const i64 8
    %152 = gep i8, ptr %41, %151
    %153 = load ptr, ptr %152
    store ptr %153, ptr %55
    %154 = load ptr, ptr %55
    %155 = const i64 8
    %156 = gep i8, ptr %154, %155
    %157 = const i64 8
    %158 = gep i8, ptr %41, %157
    %159 = load ptr, ptr %158
    store ptr %159, ptr %56
    %160 = load ptr, ptr %56
    %161 = const i64 16
    %162 = gep i8, ptr %160, %161
    br bb17(%146, %150, %156, %162)
bb14:
    %163 = load ptr, ptr %41
    store ptr %163, ptr %57
    %164 = load ptr, ptr %57
    %165 = const i64 8
    %166 = gep i8, ptr %164, %165
    %167 = const i64 8
    %168 = gep i8, ptr %41, %167
    %169 = load ptr, ptr %168
    store ptr %169, ptr %58
    %170 = load ptr, ptr %58
    %171 = const i64 8
    %172 = gep i8, ptr %170, %171
    %173 = load ptr, ptr %166
    %174 = const i64 16
    %175 = gep i8, ptr %173, %174
    br bb15(%172, %37, %175)
bb15(%4: ptr, %5: ptr, %6: ptr):
    %176 = load ptr, ptr %4
    %177 = const i64 16
    %178 = gep i8, ptr %176, %177
    br bb16(%5, %6, %178)
bb16(%7: ptr, %8: ptr, %9: ptr):
    store ptr %8, ptr %42
    %179 = const i64 8
    %180 = gep i8, ptr %42, %179
    store ptr %9, ptr %180
    call @func.77(%7, %42)
    br bb31
bb17(%10: ptr, %11: ptr, %12: ptr, %13: ptr):
    %181 = load ptr, ptr %10
    %182 = const i64 16
    %183 = gep i8, ptr %181, %182
    br bb18(%11, %12, %13, %37, %183)
bb18(%14: ptr, %15: ptr, %16: ptr, %17: ptr, %18: ptr):
    %184 = load ptr, ptr %15
    %185 = const i64 16
    %186 = gep i8, ptr %184, %185
    br bb19(%14, %16, %17, %18, %186)
bb19(%19: ptr, %20: ptr, %21: ptr, %22: ptr, %23: ptr):
    store ptr %22, ptr %43
    %187 = const i64 8
    %188 = gep i8, ptr %43, %187
    store ptr %23, ptr %188
    call @func.77(%21, %43)
    br bb20(%19, %20)
bb20(%24: ptr, %25: ptr):
    %189 = load ptr, ptr %24
    %190 = const i64 16
    %191 = gep i8, ptr %189, %190
    br bb21(%25, %37, %191)
bb21(%26: ptr, %27: ptr, %28: ptr):
    %192 = load ptr, ptr %26
    %193 = const i64 16
    %194 = gep i8, ptr %192, %193
    br bb22(%27, %28, %194)
bb22(%29: ptr, %30: ptr, %31: ptr):
    store ptr %30, ptr %44
    %195 = const i64 8
    %196 = gep i8, ptr %44, %195
    store ptr %31, ptr %196
    call @func.77(%29, %44)
    br bb32
bb23(%32: bool):
    condbr %32, bb24, bb2
bb24:
    %197 = const bool false
    br bb26(%197)
bb25:
    %198 = const bool true
    br bb27(%198)
bb26(%33: bool):
    br bb27(%33)
bb27(%34: bool):
    ret %34
bb28(%35: ptr):
    %199 = ptrtoint ptr %35 to u64
    %200 = const u64 16
    %201 = const u64 0
    %202 = icmp ne u64 %200, %201
    %203 = const u64 0
    %204 = icmp eq u64 %199, %203
    %205 = const bool false
    %206 = select bool %204, %202, %205
    %207 = const bool false
    %208 = icmp eq bool %206, %207
    condbr %208, bb29(%35), bb33
bb29(%36: ptr):
    %209 = load i64, ptr %39
    store i64 %209, ptr %36
    %210 = const i64 8
    %211 = gep i8, ptr %39, %210
    %212 = const i64 8
    %213 = gep i8, ptr %36, %212
    %214 = load i64, ptr %211
    store i64 %214, ptr %213
    %215 = load ptr, ptr %38
    %216 = const i64 8
    %217 = gep i8, ptr %37, %216
    store ptr %215, ptr %217
    %218 = const i64 1
    store i64 %218, ptr %37
    %219 = const i64 1
    %220 = const i64 16
    %221 = gep i8, ptr %37, %220
    store i64 %219, ptr %221
    br bb2
bb30:
    unreachable
bb31:
    br bb2
bb32:
    br bb2
bb33:
    unreachable
}

fn @level_arc(functy.79) {
bb0(%0: ptr, %1: ptr):
    %2 = const i64 40
    %3 = heap_alloc rust_heap i8, %2, align 8
    %4 = const u64 1
    store u64 %4, ptr %3
    %5 = const i64 8
    %6 = gep i8, ptr %3, %5
    %7 = const u64 1
    store u64 %7, ptr %6
    %8 = const i64 16
    %9 = gep i8, ptr %3, %8
    %10 = load i64, ptr %1
    store i64 %10, ptr %9
    %11 = const i64 8
    %12 = gep i8, ptr %1, %11
    %13 = const i64 8
    %14 = gep i8, ptr %9, %13
    %15 = load i64, ptr %12
    store i64 %15, ptr %14
    %16 = const i64 16
    %17 = gep i8, ptr %1, %16
    %18 = const i64 16
    %19 = gep i8, ptr %9, %18
    %20 = load i64, ptr %17
    store i64 %20, ptr %19
    store ptr %3, ptr %0
    br bb1
bb1:
    ret
}

fn @ExprMeta__raw(functy.80) {
bb0(%0: u64):
    %1 = alloca i64, align 8
    store u64 %0, ptr %1
    %2 = load u64, ptr %1
    ret %2
}

fn @_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCshhXhIKvfvMU_25clean_decl_universe_slice4NameNtB7_9PartialEq2eqBF_(functy.81) {
}

fn @_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCshhXhIKvfvMU_25clean_decl_universe_slice7LiteralNtB7_9PartialEq2eqBF_(functy.82) {
}

fn @_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCshhXhIKvfvMU_25clean_decl_universe_slice6FVarIdNtB7_9PartialEq2eqBF_(functy.83) {
}

fn @_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRmNtB7_9PartialEq2eqCshhXhIKvfvMU_25clean_decl_universe_slice(functy.84) {
}

fn @_RNvXs7_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefBH_(functy.85) {
}

fn @Verifier____env___structural_eq(functy.86) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %155 = alloca i64, align 8
    %156 = alloca i64, align 8
    %157 = alloca (i64, i64), align 8
    %158 = alloca i64, align 8
    %159 = alloca i64, align 8
    %160 = alloca i64, align 8
    %161 = alloca i64, align 8
    %162 = alloca i64, align 8
    %163 = alloca i64, align 8
    %164 = alloca (i64, i64), align 8
    %165 = alloca (i64, i64), align 8
    %166 = alloca i64, align 8
    %167 = alloca i64, align 8
    %168 = alloca i64, align 8
    %169 = alloca i64, align 8
    %170 = alloca i64, align 8
    %171 = alloca i64, align 8
    %172 = alloca i64, align 8
    %173 = alloca i64, align 8
    %174 = alloca i64, align 8
    %175 = alloca i64, align 8
    %176 = alloca i64, align 8
    %177 = alloca i64, align 8
    %178 = alloca i64, align 8
    %179 = alloca i64, align 8
    %180 = alloca i64, align 8
    %181 = alloca i64, align 8
    %182 = alloca i64, align 8
    %183 = alloca i64, align 8
    %184 = alloca i64, align 8
    %185 = alloca i64, align 8
    %186 = alloca i64, align 8
    %187 = alloca i64, align 8
    %188 = alloca i64, align 8
    %189 = alloca i64, align 8
    %190 = alloca i64, align 8
    %191 = alloca i64, align 8
    %192 = alloca i64, align 8
    %193 = alloca i64, align 8
    %194 = alloca i64, align 8
    %195 = alloca i64, align 8
    %196 = alloca i64, align 8
    %197 = alloca i64, align 8
    %198 = alloca i64, align 8
    %199 = alloca i64, align 8
    %200 = alloca i64, align 8
    %201 = alloca i64, align 8
    %202 = alloca i64, align 8
    %203 = alloca i64, align 8
    %204 = alloca i64, align 8
    %205 = alloca i64, align 8
    %206 = alloca i64, align 8
    %207 = alloca i64, align 8
    %208 = alloca i64, align 8
    %209 = alloca i64, align 8
    %210 = alloca i64, align 8
    %211 = alloca i64, align 8
    %212 = alloca i64, align 8
    %213 = alloca i64, align 8
    store ptr %1, ptr %155
    store ptr %2, ptr %156
    %214 = load ptr, ptr %155
    %215 = load ptr, ptr %156
    store ptr %214, ptr %157
    %216 = const i64 8
    %217 = gep i8, ptr %157, %216
    store ptr %215, ptr %217
    %218 = load ptr, ptr %157
    %219 = load i8, ptr %218
    %220 = sext i8 %219 to i64
    switch %220 [ 0: bb2 1: bb3 2: bb4(%0) 3: bb5(%0) 4: bb6(%0) 5: bb7(%0) 6: bb8(%0) 7: bb9(%0) 8: bb10 9: bb11(%0) 10: bb12(%0) default: bb65 ]
bb1:
    %221 = const bool false
    br bb64(%221)
bb2:
    %222 = const i64 8
    %223 = gep i8, ptr %157, %222
    %224 = load ptr, ptr %223
    %225 = load i8, ptr %224
    %226 = sext i8 %225 to i64
    switch %226 [ 0: bb23 default: bb1 ]
bb3:
    %227 = const i64 8
    %228 = gep i8, ptr %157, %227
    %229 = load ptr, ptr %228
    %230 = load i8, ptr %229
    %231 = sext i8 %230 to i64
    switch %231 [ 1: bb22 default: bb1 ]
bb4(%3: ptr):
    %232 = const i64 8
    %233 = gep i8, ptr %157, %232
    %234 = load ptr, ptr %233
    %235 = load i8, ptr %234
    %236 = sext i8 %235 to i64
    switch %236 [ 2: bb21(%3) default: bb1 ]
bb5(%4: ptr):
    %237 = const i64 8
    %238 = gep i8, ptr %157, %237
    %239 = load ptr, ptr %238
    %240 = load i8, ptr %239
    %241 = sext i8 %240 to i64
    switch %241 [ 3: bb20(%4) default: bb1 ]
bb6(%5: ptr):
    %242 = const i64 8
    %243 = gep i8, ptr %157, %242
    %244 = load ptr, ptr %243
    %245 = load i8, ptr %244
    %246 = sext i8 %245 to i64
    switch %246 [ 4: bb19(%5) default: bb1 ]
bb7(%6: ptr):
    %247 = const i64 8
    %248 = gep i8, ptr %157, %247
    %249 = load ptr, ptr %248
    %250 = load i8, ptr %249
    %251 = sext i8 %250 to i64
    switch %251 [ 5: bb18(%6) default: bb1 ]
bb8(%7: ptr):
    %252 = const i64 8
    %253 = gep i8, ptr %157, %252
    %254 = load ptr, ptr %253
    %255 = load i8, ptr %254
    %256 = sext i8 %255 to i64
    switch %256 [ 6: bb17(%7) default: bb1 ]
bb9(%8: ptr):
    %257 = const i64 8
    %258 = gep i8, ptr %157, %257
    %259 = load ptr, ptr %258
    %260 = load i8, ptr %259
    %261 = sext i8 %260 to i64
    switch %261 [ 7: bb16(%8) default: bb1 ]
bb10:
    %262 = const i64 8
    %263 = gep i8, ptr %157, %262
    %264 = load ptr, ptr %263
    %265 = load i8, ptr %264
    %266 = sext i8 %265 to i64
    switch %266 [ 8: bb15 default: bb1 ]
bb11(%9: ptr):
    %267 = const i64 8
    %268 = gep i8, ptr %157, %267
    %269 = load ptr, ptr %268
    %270 = load i8, ptr %269
    %271 = sext i8 %270 to i64
    switch %271 [ 9: bb14(%9) default: bb1 ]
bb12(%10: ptr):
    %272 = const i64 8
    %273 = gep i8, ptr %157, %272
    %274 = load ptr, ptr %273
    %275 = load i8, ptr %274
    %276 = sext i8 %275 to i64
    switch %276 [ 10: bb13(%10) default: bb1 ]
bb13(%11: ptr):
    %277 = load ptr, ptr %157
    store ptr %277, ptr %172
    %278 = load ptr, ptr %172
    %279 = const i64 8
    %280 = gep i8, ptr %278, %279
    %281 = const i64 8
    %282 = gep i8, ptr %157, %281
    %283 = load ptr, ptr %282
    store ptr %283, ptr %173
    %284 = load ptr, ptr %173
    %285 = const i64 8
    %286 = gep i8, ptr %284, %285
    %287 = load ptr, ptr %280
    %288 = const i64 16
    %289 = gep i8, ptr %287, %288
    br bb62(%11, %286, %289)
bb14(%12: ptr):
    %290 = load ptr, ptr %157
    store ptr %290, ptr %174
    %291 = load ptr, ptr %174
    %292 = const i64 4
    %293 = gep i8, ptr %291, %292
    store ptr %293, ptr %168
    %294 = load ptr, ptr %157
    store ptr %294, ptr %175
    %295 = load ptr, ptr %175
    %296 = const i64 8
    %297 = gep i8, ptr %295, %296
    store ptr %297, ptr %169
    %298 = load ptr, ptr %157
    store ptr %298, ptr %176
    %299 = load ptr, ptr %176
    %300 = const i64 16
    %301 = gep i8, ptr %299, %300
    %302 = const i64 8
    %303 = gep i8, ptr %157, %302
    %304 = load ptr, ptr %303
    store ptr %304, ptr %177
    %305 = load ptr, ptr %177
    %306 = const i64 4
    %307 = gep i8, ptr %305, %306
    store ptr %307, ptr %170
    %308 = const i64 8
    %309 = gep i8, ptr %157, %308
    %310 = load ptr, ptr %309
    store ptr %310, ptr %178
    %311 = load ptr, ptr %178
    %312 = const i64 8
    %313 = gep i8, ptr %311, %312
    store ptr %313, ptr %171
    %314 = const i64 8
    %315 = gep i8, ptr %157, %314
    %316 = load ptr, ptr %315
    store ptr %316, ptr %179
    %317 = load ptr, ptr %179
    %318 = const i64 16
    %319 = gep i8, ptr %317, %318
    %320 = call @func.81(%168, %170)
    br bb55(%12, %301, %319, %320)
bb15:
    %321 = load ptr, ptr %157
    store ptr %321, ptr %180
    %322 = load ptr, ptr %180
    %323 = const i64 8
    %324 = gep i8, ptr %322, %323
    store ptr %324, ptr %166
    %325 = const i64 8
    %326 = gep i8, ptr %157, %325
    %327 = load ptr, ptr %326
    store ptr %327, ptr %181
    %328 = load ptr, ptr %181
    %329 = const i64 8
    %330 = gep i8, ptr %328, %329
    store ptr %330, ptr %167
    %331 = call @func.82(%166, %167)
    br bb64(%331)
bb16(%13: ptr):
    %332 = load ptr, ptr %157
    store ptr %332, ptr %182
    %333 = load ptr, ptr %182
    %334 = const i64 8
    %335 = gep i8, ptr %333, %334
    %336 = load ptr, ptr %157
    store ptr %336, ptr %183
    %337 = load ptr, ptr %183
    %338 = const i64 16
    %339 = gep i8, ptr %337, %338
    %340 = load ptr, ptr %157
    store ptr %340, ptr %184
    %341 = load ptr, ptr %184
    %342 = const i64 24
    %343 = gep i8, ptr %341, %342
    %344 = const i64 8
    %345 = gep i8, ptr %157, %344
    %346 = load ptr, ptr %345
    store ptr %346, ptr %185
    %347 = load ptr, ptr %185
    %348 = const i64 8
    %349 = gep i8, ptr %347, %348
    %350 = const i64 8
    %351 = gep i8, ptr %157, %350
    %352 = load ptr, ptr %351
    store ptr %352, ptr %186
    %353 = load ptr, ptr %186
    %354 = const i64 16
    %355 = gep i8, ptr %353, %354
    %356 = const i64 8
    %357 = gep i8, ptr %157, %356
    %358 = load ptr, ptr %357
    store ptr %358, ptr %187
    %359 = load ptr, ptr %187
    %360 = const i64 24
    %361 = gep i8, ptr %359, %360
    %362 = load ptr, ptr %335
    %363 = const i64 16
    %364 = gep i8, ptr %362, %363
    br bb44(%13, %339, %343, %349, %355, %361, %364)
bb17(%14: ptr):
    %365 = load ptr, ptr %157
    store ptr %365, ptr %188
    %366 = load ptr, ptr %188
    %367 = const i64 1
    %368 = gep i8, ptr %366, %367
    %369 = load ptr, ptr %157
    store ptr %369, ptr %189
    %370 = load ptr, ptr %189
    %371 = const i64 8
    %372 = gep i8, ptr %370, %371
    %373 = load ptr, ptr %157
    store ptr %373, ptr %190
    %374 = load ptr, ptr %190
    %375 = const i64 16
    %376 = gep i8, ptr %374, %375
    %377 = const i64 8
    %378 = gep i8, ptr %157, %377
    %379 = load ptr, ptr %378
    store ptr %379, ptr %191
    %380 = load ptr, ptr %191
    %381 = const i64 1
    %382 = gep i8, ptr %380, %381
    %383 = const i64 8
    %384 = gep i8, ptr %157, %383
    %385 = load ptr, ptr %384
    store ptr %385, ptr %192
    %386 = load ptr, ptr %192
    %387 = const i64 8
    %388 = gep i8, ptr %386, %387
    %389 = const i64 8
    %390 = gep i8, ptr %157, %389
    %391 = load ptr, ptr %390
    store ptr %391, ptr %193
    %392 = load ptr, ptr %193
    %393 = const i64 16
    %394 = gep i8, ptr %392, %393
    br bb36(%14, %372, %376, %388, %394)
bb18(%15: ptr):
    %395 = load ptr, ptr %157
    store ptr %395, ptr %194
    %396 = load ptr, ptr %194
    %397 = const i64 1
    %398 = gep i8, ptr %396, %397
    %399 = load ptr, ptr %157
    store ptr %399, ptr %195
    %400 = load ptr, ptr %195
    %401 = const i64 8
    %402 = gep i8, ptr %400, %401
    %403 = load ptr, ptr %157
    store ptr %403, ptr %196
    %404 = load ptr, ptr %196
    %405 = const i64 16
    %406 = gep i8, ptr %404, %405
    %407 = const i64 8
    %408 = gep i8, ptr %157, %407
    %409 = load ptr, ptr %408
    store ptr %409, ptr %197
    %410 = load ptr, ptr %197
    %411 = const i64 1
    %412 = gep i8, ptr %410, %411
    %413 = const i64 8
    %414 = gep i8, ptr %157, %413
    %415 = load ptr, ptr %414
    store ptr %415, ptr %198
    %416 = load ptr, ptr %198
    %417 = const i64 8
    %418 = gep i8, ptr %416, %417
    %419 = const i64 8
    %420 = gep i8, ptr %157, %419
    %421 = load ptr, ptr %420
    store ptr %421, ptr %199
    %422 = load ptr, ptr %199
    %423 = const i64 16
    %424 = gep i8, ptr %422, %423
    br bb36(%15, %402, %406, %418, %424)
bb19(%16: ptr):
    %425 = load ptr, ptr %157
    store ptr %425, ptr %200
    %426 = load ptr, ptr %200
    %427 = const i64 8
    %428 = gep i8, ptr %426, %427
    %429 = load ptr, ptr %157
    store ptr %429, ptr %201
    %430 = load ptr, ptr %201
    %431 = const i64 16
    %432 = gep i8, ptr %430, %431
    %433 = const i64 8
    %434 = gep i8, ptr %157, %433
    %435 = load ptr, ptr %434
    store ptr %435, ptr %202
    %436 = load ptr, ptr %202
    %437 = const i64 8
    %438 = gep i8, ptr %436, %437
    %439 = const i64 8
    %440 = gep i8, ptr %157, %439
    %441 = load ptr, ptr %440
    store ptr %441, ptr %203
    %442 = load ptr, ptr %203
    %443 = const i64 16
    %444 = gep i8, ptr %442, %443
    %445 = load ptr, ptr %428
    %446 = const i64 16
    %447 = gep i8, ptr %445, %446
    br bb29(%16, %432, %438, %444, %447)
bb20(%17: ptr):
    %448 = load ptr, ptr %157
    store ptr %448, ptr %204
    %449 = load ptr, ptr %204
    %450 = const i64 4
    %451 = gep i8, ptr %449, %450
    store ptr %451, ptr %162
    %452 = load ptr, ptr %157
    store ptr %452, ptr %205
    %453 = load ptr, ptr %205
    %454 = const i64 8
    %455 = gep i8, ptr %453, %454
    %456 = const i64 8
    %457 = gep i8, ptr %157, %456
    %458 = load ptr, ptr %457
    store ptr %458, ptr %206
    %459 = load ptr, ptr %206
    %460 = const i64 4
    %461 = gep i8, ptr %459, %460
    store ptr %461, ptr %163
    %462 = const i64 8
    %463 = gep i8, ptr %157, %462
    %464 = load ptr, ptr %463
    store ptr %464, ptr %207
    %465 = load ptr, ptr %207
    %466 = const i64 8
    %467 = gep i8, ptr %465, %466
    %468 = call @func.81(%162, %163)
    br bb24(%17, %455, %467, %468)
bb21(%18: ptr):
    %469 = load ptr, ptr %157
    store ptr %469, ptr %208
    %470 = load ptr, ptr %208
    %471 = const i64 8
    %472 = gep i8, ptr %470, %471
    %473 = const i64 8
    %474 = gep i8, ptr %157, %473
    %475 = load ptr, ptr %474
    store ptr %475, ptr %209
    %476 = load ptr, ptr %209
    %477 = const i64 8
    %478 = gep i8, ptr %476, %477
    %479 = call @func.87(%18, %472, %478)
    br bb64(%479)
bb22:
    %480 = load ptr, ptr %157
    store ptr %480, ptr %210
    %481 = load ptr, ptr %210
    %482 = const i64 8
    %483 = gep i8, ptr %481, %482
    store ptr %483, ptr %160
    %484 = const i64 8
    %485 = gep i8, ptr %157, %484
    %486 = load ptr, ptr %485
    store ptr %486, ptr %211
    %487 = load ptr, ptr %211
    %488 = const i64 8
    %489 = gep i8, ptr %487, %488
    store ptr %489, ptr %161
    %490 = call @func.83(%160, %161)
    br bb64(%490)
bb23:
    %491 = load ptr, ptr %157
    store ptr %491, ptr %212
    %492 = load ptr, ptr %212
    %493 = const i64 4
    %494 = gep i8, ptr %492, %493
    store ptr %494, ptr %158
    %495 = const i64 8
    %496 = gep i8, ptr %157, %495
    %497 = load ptr, ptr %496
    store ptr %497, ptr %213
    %498 = load ptr, ptr %213
    %499 = const i64 4
    %500 = gep i8, ptr %498, %499
    store ptr %500, ptr %159
    %501 = call @func.84(%158, %159)
    br bb64(%501)
bb24(%19: ptr, %20: ptr, %21: ptr, %22: bool):
    condbr %22, bb25(%19, %20, %21), bb26
bb25(%23: ptr, %24: ptr, %25: ptr):
    call @func.85(%164, %24)
    br bb27(%23, %25)
bb26:
    %502 = const bool false
    br bb64(%502)
bb27(%26: ptr, %27: ptr):
    call @func.85(%165, %27)
    br bb28(%26)
bb28(%28: ptr):
    %503 = call @func.88(%28, %164, %165)
    br bb64(%503)
bb29(%29: ptr, %30: ptr, %31: ptr, %32: ptr, %33: ptr):
    %504 = load ptr, ptr %31
    %505 = const i64 16
    %506 = gep i8, ptr %504, %505
    br bb30(%29, %30, %32, %33, %506)
bb30(%34: ptr, %35: ptr, %36: ptr, %37: ptr, %38: ptr):
    %507 = call @func.86(%34, %37, %38)
    br bb31(%34, %35, %36, %507)
bb31(%39: ptr, %40: ptr, %41: ptr, %42: bool):
    condbr %42, bb32(%39, %40, %41), bb33
bb32(%43: ptr, %44: ptr, %45: ptr):
    %508 = load ptr, ptr %44
    %509 = const i64 16
    %510 = gep i8, ptr %508, %509
    br bb34(%43, %45, %510)
bb33:
    %511 = const bool false
    br bb64(%511)
bb34(%46: ptr, %47: ptr, %48: ptr):
    %512 = load ptr, ptr %47
    %513 = const i64 16
    %514 = gep i8, ptr %512, %513
    br bb35(%46, %48, %514)
bb35(%49: ptr, %50: ptr, %51: ptr):
    %515 = call @func.86(%49, %50, %51)
    br bb64(%515)
bb36(%52: ptr, %53: ptr, %54: ptr, %55: ptr, %56: ptr):
    %516 = load ptr, ptr %53
    %517 = const i64 16
    %518 = gep i8, ptr %516, %517
    br bb37(%52, %54, %55, %56, %518)
bb37(%57: ptr, %58: ptr, %59: ptr, %60: ptr, %61: ptr):
    %519 = load ptr, ptr %59
    %520 = const i64 16
    %521 = gep i8, ptr %519, %520
    br bb38(%57, %58, %60, %61, %521)
bb38(%62: ptr, %63: ptr, %64: ptr, %65: ptr, %66: ptr):
    %522 = call @func.86(%62, %65, %66)
    br bb39(%62, %63, %64, %522)
bb39(%67: ptr, %68: ptr, %69: ptr, %70: bool):
    condbr %70, bb40(%67, %68, %69), bb41
bb40(%71: ptr, %72: ptr, %73: ptr):
    %523 = load ptr, ptr %72
    %524 = const i64 16
    %525 = gep i8, ptr %523, %524
    br bb42(%71, %73, %525)
bb41:
    %526 = const bool false
    br bb64(%526)
bb42(%74: ptr, %75: ptr, %76: ptr):
    %527 = load ptr, ptr %75
    %528 = const i64 16
    %529 = gep i8, ptr %527, %528
    br bb43(%74, %76, %529)
bb43(%77: ptr, %78: ptr, %79: ptr):
    %530 = call @func.86(%77, %78, %79)
    br bb64(%530)
bb44(%80: ptr, %81: ptr, %82: ptr, %83: ptr, %84: ptr, %85: ptr, %86: ptr):
    %531 = load ptr, ptr %83
    %532 = const i64 16
    %533 = gep i8, ptr %531, %532
    br bb45(%80, %81, %82, %84, %85, %86, %533)
bb45(%87: ptr, %88: ptr, %89: ptr, %90: ptr, %91: ptr, %92: ptr, %93: ptr):
    %534 = call @func.86(%87, %92, %93)
    br bb46(%87, %88, %89, %90, %91, %534)
bb46(%94: ptr, %95: ptr, %96: ptr, %97: ptr, %98: ptr, %99: bool):
    condbr %99, bb47(%94, %95, %96, %97, %98), bb52
bb47(%100: ptr, %101: ptr, %102: ptr, %103: ptr, %104: ptr):
    %535 = load ptr, ptr %101
    %536 = const i64 16
    %537 = gep i8, ptr %535, %536
    br bb48(%100, %102, %103, %104, %537)
bb48(%105: ptr, %106: ptr, %107: ptr, %108: ptr, %109: ptr):
    %538 = load ptr, ptr %107
    %539 = const i64 16
    %540 = gep i8, ptr %538, %539
    br bb49(%105, %106, %108, %109, %540)
bb49(%110: ptr, %111: ptr, %112: ptr, %113: ptr, %114: ptr):
    %541 = call @func.86(%110, %113, %114)
    br bb50(%110, %111, %112, %541)
bb50(%115: ptr, %116: ptr, %117: ptr, %118: bool):
    condbr %118, bb51(%115, %116, %117), bb52
bb51(%119: ptr, %120: ptr, %121: ptr):
    %542 = load ptr, ptr %120
    %543 = const i64 16
    %544 = gep i8, ptr %542, %543
    br bb53(%119, %121, %544)
bb52:
    %545 = const bool false
    br bb64(%545)
bb53(%122: ptr, %123: ptr, %124: ptr):
    %546 = load ptr, ptr %123
    %547 = const i64 16
    %548 = gep i8, ptr %546, %547
    br bb54(%122, %124, %548)
bb54(%125: ptr, %126: ptr, %127: ptr):
    %549 = call @func.86(%125, %126, %127)
    br bb64(%549)
bb55(%128: ptr, %129: ptr, %130: ptr, %131: bool):
    condbr %131, bb56(%128, %129, %130), bb59
bb56(%132: ptr, %133: ptr, %134: ptr):
    %550 = call @func.84(%169, %171)
    br bb57(%132, %133, %134, %550)
bb57(%135: ptr, %136: ptr, %137: ptr, %138: bool):
    condbr %138, bb58(%135, %136, %137), bb59
bb58(%139: ptr, %140: ptr, %141: ptr):
    %551 = load ptr, ptr %140
    %552 = const i64 16
    %553 = gep i8, ptr %551, %552
    br bb60(%139, %141, %553)
bb59:
    %554 = const bool false
    br bb64(%554)
bb60(%142: ptr, %143: ptr, %144: ptr):
    %555 = load ptr, ptr %143
    %556 = const i64 16
    %557 = gep i8, ptr %555, %556
    br bb61(%142, %144, %557)
bb61(%145: ptr, %146: ptr, %147: ptr):
    %558 = call @func.86(%145, %146, %147)
    br bb64(%558)
bb62(%148: ptr, %149: ptr, %150: ptr):
    %559 = load ptr, ptr %149
    %560 = const i64 16
    %561 = gep i8, ptr %559, %560
    br bb63(%148, %150, %561)
bb63(%151: ptr, %152: ptr, %153: ptr):
    %562 = call @func.86(%151, %152, %153)
    br bb64(%562)
bb64(%154: bool):
    ret %154
bb65:
    unreachable
}

fn @Verifier____env___level_eq(functy.87) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %4 = call @func.110(%1, %2)
    br bb1(%4)
bb1(%3: bool):
    ret %3
}

fn @Verifier____env___level_vec_eq(functy.88) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %29 = alloca (i64, i64), align 8
    %30 = const i64 8
    %31 = gep i8, ptr %1, %30
    %32 = load u64, ptr %31
    %33 = const i64 8
    %34 = gep i8, ptr %2, %33
    %35 = load u64, ptr %34
    %36 = icmp ne u64 %32, %35
    condbr %36, bb1, bb2(%0)
bb1:
    %37 = const bool false
    br bb12(%37)
bb2(%3: ptr):
    %38 = const u64 0
    %39 = const i64 8
    %40 = gep i8, ptr %1, %39
    %41 = load u64, ptr %40
    br bb3(%3, %38, %41)
bb3(%4: ptr, %5: u64, %6: u64):
    %42 = icmp ult u64 %5, %6
    condbr %42, bb4(%4, %5, %6), bb11
bb4(%7: ptr, %8: u64, %9: u64):
    %43 = const i64 8
    %44 = gep i8, ptr %1, %43
    %45 = load u64, ptr %44
    %46 = icmp ult u64 %8, %45
    condbr %46, bb5(%7, %8, %9, %8), bb13
bb5(%10: ptr, %11: u64, %12: u64, %13: u64):
    %47 = load ptr, ptr %1
    %48 = const u64 24
    %49 = mul u64 %13, %48
    %50 = gep i8, ptr %47, %49
    %51 = const i64 8
    %52 = gep i8, ptr %2, %51
    %53 = load u64, ptr %52
    %54 = icmp ult u64 %11, %53
    condbr %54, bb6(%10, %11, %12, %50, %11), bb13
bb6(%14: ptr, %15: u64, %16: u64, %17: ptr, %18: u64):
    %55 = load ptr, ptr %2
    %56 = const u64 24
    %57 = mul u64 %18, %56
    %58 = gep i8, ptr %55, %57
    %59 = call @func.87(%14, %17, %58)
    br bb7(%14, %15, %16, %59)
bb7(%19: ptr, %20: u64, %21: u64, %22: bool):
    condbr %22, bb8(%19, %20, %21), bb9
bb8(%23: ptr, %24: u64, %25: u64):
    %60 = const u64 1
    %61, %62 = add.overflow u64 %24, %60
    store u64 %61, ptr %29
    %63 = const i64 8
    %64 = gep i8, ptr %29, %63
    store bool %62, ptr %64
    %65 = const i64 8
    %66 = gep i8, ptr %29, %65
    %67 = load bool, ptr %66
    %68 = const bool false
    %69 = icmp eq bool %67, %68
    condbr %69, bb10(%23, %25), bb13
bb9:
    %70 = const bool false
    br bb12(%70)
bb10(%26: ptr, %27: u64):
    %71 = load u64, ptr %29
    br bb3(%26, %71, %27)
bb11:
    %72 = const bool true
    br bb12(%72)
bb12(%28: bool):
    ret %28
bb13:
    unreachable
}

fn @Verifier____env___def_eq_impl(functy.89) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %4 = call @func.55(%0, %1, %2)
    br bb1(%4)
bb1(%3: bool):
    ret %3
}

fn @Verifier____env___try_eta_expansion(functy.90) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %25 = alloca i64, align 8
    %26 = alloca i64, align 8
    %27 = alloca (i64, i64), align 8
    %28 = alloca (i64, i64, i64, i64, i64), align 8
    %29 = alloca (i64, i64, i64, i64, i64), align 8
    %30 = alloca (i64, i64, i64, i64, i64), align 8
    %31 = alloca (i64, i64, i64, i64, i64), align 8
    %32 = alloca (i64, i64, i64, i64, i64), align 8
    %33 = alloca (i64, i64, i64, i64, i64), align 8
    %34 = alloca (i64, i64, i64, i64, i64), align 8
    %35 = alloca (i64, i64, i64, i64, i64), align 8
    %36 = alloca i64, align 8
    %37 = alloca i64, align 8
    %38 = alloca i64, align 8
    %39 = alloca i64, align 8
    store ptr %1, ptr %25
    store ptr %2, ptr %26
    %40 = const bool false
    %41 = const bool false
    %42 = load ptr, ptr %25
    %43 = load ptr, ptr %26
    store ptr %42, ptr %27
    %44 = const i64 8
    %45 = gep i8, ptr %27, %44
    store ptr %43, ptr %45
    %46 = load ptr, ptr %27
    %47 = load i8, ptr %46
    %48 = sext i8 %47 to i64
    switch %48 [ 5: bb4(%0) default: bb1(%0) ]
bb1(%3: ptr):
    %49 = const i64 8
    %50 = gep i8, ptr %27, %49
    %51 = load ptr, ptr %50
    %52 = load i8, ptr %51
    %53 = sext i8 %52 to i64
    switch %53 [ 5: bb3(%3) default: bb2 ]
bb2:
    %54 = const bool false
    br bb15(%54)
bb3(%4: ptr):
    %55 = const i64 8
    %56 = gep i8, ptr %27, %55
    %57 = load ptr, ptr %56
    store ptr %57, ptr %36
    %58 = load ptr, ptr %36
    %59 = const i64 8
    %60 = gep i8, ptr %58, %59
    %61 = const i64 8
    %62 = gep i8, ptr %27, %61
    %63 = load ptr, ptr %62
    store ptr %63, ptr %37
    %64 = load ptr, ptr %37
    %65 = const i64 16
    %66 = gep i8, ptr %64, %65
    %67 = load ptr, ptr %25
    %68 = const u32 0
    %69 = const u32 1
    call @func.111(%32, %67, %68, %69)
    br bb10(%4, %66)
bb4(%5: ptr):
    %70 = load ptr, ptr %27
    store ptr %70, ptr %38
    %71 = load ptr, ptr %38
    %72 = const i64 8
    %73 = gep i8, ptr %71, %72
    %74 = load ptr, ptr %27
    store ptr %74, ptr %39
    %75 = load ptr, ptr %39
    %76 = const i64 16
    %77 = gep i8, ptr %75, %76
    %78 = load ptr, ptr %26
    %79 = const u32 0
    %80 = const u32 1
    call @func.111(%28, %78, %79, %80)
    br bb5(%5, %77)
bb5(%6: ptr, %7: ptr):
    %81 = const bool true
    %82 = load i64, ptr %28
    store i64 %82, ptr %30
    %83 = const i64 8
    %84 = gep i8, ptr %28, %83
    %85 = const i64 8
    %86 = gep i8, ptr %30, %85
    %87 = load i64, ptr %84
    store i64 %87, ptr %86
    %88 = const i64 16
    %89 = gep i8, ptr %28, %88
    %90 = const i64 16
    %91 = gep i8, ptr %30, %90
    %92 = load i64, ptr %89
    store i64 %92, ptr %91
    %93 = const i64 24
    %94 = gep i8, ptr %28, %93
    %95 = const i64 24
    %96 = gep i8, ptr %30, %95
    %97 = load i64, ptr %94
    store i64 %97, ptr %96
    %98 = const i64 32
    %99 = gep i8, ptr %28, %98
    %100 = const i64 32
    %101 = gep i8, ptr %30, %100
    %102 = load i64, ptr %99
    store i64 %102, ptr %101
    %103 = const u32 0
    call @func.98(%31, %103)
    br bb6(%6, %7)
bb6(%8: ptr, %9: ptr):
    %104 = const bool false
    call @func.99(%29, %30, %31)
    br bb7(%8, %9)
bb7(%10: ptr, %11: ptr):
    %105 = const bool false
    %106 = load ptr, ptr %11
    %107 = const i64 16
    %108 = gep i8, ptr %106, %107
    br bb8(%10, %108)
bb8(%12: ptr, %13: ptr):
    %109 = call @func.89(%12, %13, %29)
    br bb9(%109)
bb9(%14: bool):
    br bb15(%14)
bb10(%15: ptr, %16: ptr):
    %110 = const bool true
    %111 = load i64, ptr %32
    store i64 %111, ptr %34
    %112 = const i64 8
    %113 = gep i8, ptr %32, %112
    %114 = const i64 8
    %115 = gep i8, ptr %34, %114
    %116 = load i64, ptr %113
    store i64 %116, ptr %115
    %117 = const i64 16
    %118 = gep i8, ptr %32, %117
    %119 = const i64 16
    %120 = gep i8, ptr %34, %119
    %121 = load i64, ptr %118
    store i64 %121, ptr %120
    %122 = const i64 24
    %123 = gep i8, ptr %32, %122
    %124 = const i64 24
    %125 = gep i8, ptr %34, %124
    %126 = load i64, ptr %123
    store i64 %126, ptr %125
    %127 = const i64 32
    %128 = gep i8, ptr %32, %127
    %129 = const i64 32
    %130 = gep i8, ptr %34, %129
    %131 = load i64, ptr %128
    store i64 %131, ptr %130
    %132 = const u32 0
    call @func.98(%35, %132)
    br bb11(%15, %16)
bb11(%17: ptr, %18: ptr):
    %133 = const bool false
    call @func.99(%33, %34, %35)
    br bb12(%17, %18)
bb12(%19: ptr, %20: ptr):
    %134 = const bool false
    %135 = load ptr, ptr %20
    %136 = const i64 16
    %137 = gep i8, ptr %135, %136
    br bb13(%19, %137)
bb13(%21: ptr, %22: ptr):
    %138 = call @func.89(%21, %22, %33)
    br bb14(%138)
bb14(%23: bool):
    br bb15(%23)
bb15(%24: bool):
    ret %24
}

fn @_Literal_as_std__clone__Clone___clone(functy.91) {
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

fn @_BinderData_as_std__clone__Clone___clone(functy.92) {
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

fn @_FVarId_as_std__clone__Clone___clone(functy.93) {
bb0(%0: ptr, %1: ptr):
    %2 = load i64, ptr %1
    store i64 %2, ptr %0
    ret
}

fn @_RNvXs4_NtCs2EYQwhfuABO_4core6optionINtB5_6OptionNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprENtNtB7_5clone5Clone5cloneBM_(functy.94) {
}

fn @Verifier____env___unfold_const(functy.95) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %28 = alloca i64, align 8
    %29 = alloca (i64, i64), align 8
    %30 = alloca (i64, i64), align 8
    %31 = alloca (i64, i64), align 8
    %32 = alloca (i64, i64), align 8
    %33 = alloca (i64, i64), align 8
    %34 = const u64 0
    %35 = load i64, ptr %1
    store i64 %35, ptr %31
    %36 = const i64 8
    %37 = gep i8, ptr %1, %36
    %38 = const i64 8
    %39 = gep i8, ptr %31, %38
    %40 = load i64, ptr %37
    store i64 %40, ptr %39
    %41 = const i64 8
    %42 = gep i8, ptr %31, %41
    %43 = load u64, ptr %42
    br bb1(%1, %2, %34, %43)
bb1(%3: ptr, %4: ptr, %5: u64, %6: u64):
    %44 = icmp ult u64 %5, %6
    condbr %44, bb2(%3, %4, %5, %6), bb8
bb2(%7: ptr, %8: ptr, %9: u64, %10: u64):
    %45 = load i64, ptr %7
    store i64 %45, ptr %32
    %46 = const i64 8
    %47 = gep i8, ptr %7, %46
    %48 = const i64 8
    %49 = gep i8, ptr %32, %48
    %50 = load i64, ptr %47
    store i64 %50, ptr %49
    %51 = load i64, ptr %32
    store i64 %51, ptr %29
    %52 = const i64 8
    %53 = gep i8, ptr %32, %52
    %54 = const i64 8
    %55 = gep i8, ptr %29, %54
    %56 = load i64, ptr %53
    store i64 %56, ptr %55
    %57 = const i64 8
    %58 = gep i8, ptr %29, %57
    %59 = load u64, ptr %58
    %60 = icmp ult u64 %9, %59
    condbr %60, bb3(%7, %8, %9, %10, %9), bb10
bb3(%11: ptr, %12: ptr, %13: u64, %14: u64, %15: u64):
    %61 = load i64, ptr %11
    store i64 %61, ptr %33
    %62 = const i64 8
    %63 = gep i8, ptr %11, %62
    %64 = const i64 8
    %65 = gep i8, ptr %33, %64
    %66 = load i64, ptr %63
    store i64 %66, ptr %65
    %67 = load ptr, ptr %33
    %68 = const u64 48
    %69 = mul u64 %15, %68
    %70 = gep i8, ptr %67, %69
    store ptr %70, ptr %28
    %71 = load ptr, ptr %28
    %72 = call @func.4(%71, %12)
    br bb4(%11, %12, %13, %14, %72)
bb4(%16: ptr, %17: ptr, %18: u64, %19: u64, %20: bool):
    condbr %20, bb5, bb6(%16, %17, %18, %19)
bb5:
    %73 = load ptr, ptr %28
    %74 = const i64 8
    %75 = gep i8, ptr %73, %74
    call @func.94(%0, %75)
    br bb9
bb6(%21: ptr, %22: ptr, %23: u64, %24: u64):
    %76 = const u64 1
    %77, %78 = add.overflow u64 %23, %76
    store u64 %77, ptr %30
    %79 = const i64 8
    %80 = gep i8, ptr %30, %79
    store bool %78, ptr %80
    %81 = const i64 8
    %82 = gep i8, ptr %30, %81
    %83 = load bool, ptr %82
    %84 = const bool false
    %85 = icmp eq bool %83, %84
    condbr %85, bb7(%21, %22, %24), bb10
bb7(%25: ptr, %26: ptr, %27: u64):
    %86 = load u64, ptr %30
    br bb1(%25, %26, %86, %27)
bb8:
    %87 = const i8 11
    store i8 %87, ptr %0
    br bb9
bb9:
    ret
bb10:
    unreachable
}

fn @Expr__from_kind(functy.96) {
bb0(%0: ptr, %1: ptr):
    %2 = alloca i64, align 8
    %3 = alloca (i64, i64, i64, i64), align 8
    call @func.114(%2, %1)
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

fn @Expr__loose_bvar_range(functy.97) {
bb0(%0: ptr):
    %2 = alloca i64, align 8
    %3 = const i64 32
    %4 = gep i8, ptr %0, %3
    %5 = load i64, ptr %4
    store i64 %5, ptr %2
    %6 = load u64, ptr %2
    %7 = call @func.115(%6)
    br bb1(%7)
bb1(%1: u32):
    ret %1
}

fn @Expr__bvar(functy.98) {
bb0(%0: ptr, %1: u32):
    %2 = alloca (i64, i64, i64, i64), align 8
    %3 = const i64 4
    %4 = gep i8, ptr %2, %3
    store u32 %1, ptr %4
    %5 = const i8 0
    store i8 %5, ptr %2
    call @func.96(%0, %2)
    br bb1
bb1:
    ret
}

fn @Expr__app(functy.99) {
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
    call @func.96(%0, %3)
    br bb3
bb3:
    ret
}

fn @Expr__lam(functy.100) {
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
    call @func.96(%0, %4)
    br bb3
bb3:
    ret
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm14saturating_sub(functy.101) {
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm14saturating_add(functy.102) {
}

fn @Expr__instantiate_at(functy.103) {
bb0(%0: ptr, %1: ptr, %2: ptr, %3: u32):
    %97 = alloca i64, align 8
    %98 = alloca i64, align 8
    %99 = alloca (i64, i64, i64, i64, i64), align 8
    %100 = alloca (i64, i64, i64, i64, i64), align 8
    %101 = alloca (i8, i8), align 1
    %102 = alloca (i64, i64, i64, i64, i64), align 8
    %103 = alloca (i64, i64, i64, i64, i64), align 8
    %104 = alloca (i8, i8), align 1
    %105 = alloca (i64, i64, i64, i64, i64), align 8
    %106 = alloca (i64, i64, i64, i64, i64), align 8
    %107 = alloca i32, align 4
    %108 = alloca (i64, i64, i64, i64, i64), align 8
    %109 = alloca (i64, i64, i64, i64, i64), align 8
    %110 = alloca (i64, i64, i64, i64, i64), align 8
    %111 = alloca i32, align 4
    %112 = alloca (i64, i64, i64, i64, i64), align 8
    store ptr %1, ptr %97
    %113 = const bool false
    %114 = const bool false
    %115 = const bool false
    %116 = const bool false
    %117 = const bool false
    %118 = load ptr, ptr %97
    %119 = call @func.97(%118)
    br bb1(%2, %3, %119)
bb1(%4: ptr, %5: u32, %6: u32):
    %120 = icmp uge u32 %5, %6
    condbr %120, bb2, bb3(%4, %5)
bb2:
    %121 = load ptr, ptr %97
    call @func.36(%0, %121)
    br bb43
bb3(%7: ptr, %8: u32):
    %122 = load ptr, ptr %97
    store ptr %122, ptr %98
    %123 = load ptr, ptr %98
    %124 = load i8, ptr %123
    %125 = sext i8 %124 to i64
    switch %125 [ 0: bb10(%7, %8) 4: bb9(%7, %8) 5: bb8(%7, %8) 6: bb7(%7, %8) 7: bb6(%7, %8) 9: bb5(%7, %8) default: bb4 ]
bb4:
    %126 = load ptr, ptr %97
    call @func.36(%0, %126)
    br bb43
bb5(%9: ptr, %10: u32):
    %127 = load ptr, ptr %98
    %128 = const i64 4
    %129 = gep i8, ptr %127, %128
    %130 = load ptr, ptr %98
    %131 = const i64 8
    %132 = gep i8, ptr %130, %131
    %133 = load ptr, ptr %98
    %134 = const i64 16
    %135 = gep i8, ptr %133, %134
    %136 = load i32, ptr %129
    store i32 %136, ptr %111
    %137 = load u32, ptr %132
    %138 = load ptr, ptr %135
    %139 = const i64 16
    %140 = gep i8, ptr %138, %139
    br bb41(%9, %10, %137, %140)
bb6(%11: ptr, %12: u32):
    %141 = load ptr, ptr %98
    %142 = const i64 4
    %143 = gep i8, ptr %141, %142
    %144 = load ptr, ptr %98
    %145 = const i64 8
    %146 = gep i8, ptr %144, %145
    %147 = load ptr, ptr %98
    %148 = const i64 16
    %149 = gep i8, ptr %147, %148
    %150 = load ptr, ptr %98
    %151 = const i64 24
    %152 = gep i8, ptr %150, %151
    %153 = load ptr, ptr %98
    %154 = const i64 1
    %155 = gep i8, ptr %153, %154
    %156 = load i32, ptr %143
    store i32 %156, ptr %107
    %157 = load ptr, ptr %146
    %158 = const i64 16
    %159 = gep i8, ptr %157, %158
    br bb33(%11, %12, %149, %152, %155, %159)
bb7(%13: ptr, %14: u32):
    %160 = load ptr, ptr %98
    %161 = const i64 1
    %162 = gep i8, ptr %160, %161
    %163 = load ptr, ptr %98
    %164 = const i64 8
    %165 = gep i8, ptr %163, %164
    %166 = load ptr, ptr %98
    %167 = const i64 16
    %168 = gep i8, ptr %166, %167
    %169 = load i8, ptr %162
    store i8 %169, ptr %104
    %170 = const i64 1
    %171 = gep i8, ptr %162, %170
    %172 = const i64 1
    %173 = gep i8, ptr %104, %172
    %174 = load i8, ptr %171
    store i8 %174, ptr %173
    %175 = load ptr, ptr %165
    %176 = const i64 16
    %177 = gep i8, ptr %175, %176
    br bb27(%13, %14, %168, %177)
bb8(%15: ptr, %16: u32):
    %178 = load ptr, ptr %98
    %179 = const i64 1
    %180 = gep i8, ptr %178, %179
    %181 = load ptr, ptr %98
    %182 = const i64 8
    %183 = gep i8, ptr %181, %182
    %184 = load ptr, ptr %98
    %185 = const i64 16
    %186 = gep i8, ptr %184, %185
    %187 = load i8, ptr %180
    store i8 %187, ptr %101
    %188 = const i64 1
    %189 = gep i8, ptr %180, %188
    %190 = const i64 1
    %191 = gep i8, ptr %101, %190
    %192 = load i8, ptr %189
    store i8 %192, ptr %191
    %193 = load ptr, ptr %183
    %194 = const i64 16
    %195 = gep i8, ptr %193, %194
    br bb21(%15, %16, %186, %195)
bb9(%17: ptr, %18: u32):
    %196 = load ptr, ptr %98
    %197 = const i64 8
    %198 = gep i8, ptr %196, %197
    %199 = load ptr, ptr %98
    %200 = const i64 16
    %201 = gep i8, ptr %199, %200
    %202 = load ptr, ptr %198
    %203 = const i64 16
    %204 = gep i8, ptr %202, %203
    br bb16(%17, %18, %201, %204)
bb10(%19: ptr, %20: u32):
    %205 = load ptr, ptr %98
    %206 = const i64 4
    %207 = gep i8, ptr %205, %206
    %208 = load u32, ptr %207
    %209 = icmp eq u32 %208, %20
    condbr %209, bb11(%19, %20), bb12(%20, %207)
bb11(%21: ptr, %22: u32):
    %210 = const u32 0
    call @func.64(%0, %21, %210, %22)
    br bb43
bb12(%23: u32, %24: ptr):
    %211 = load u32, ptr %24
    %212 = icmp ugt u32 %211, %23
    condbr %212, bb13(%24), bb15
bb13(%25: ptr):
    %213 = load u32, ptr %25
    %214 = const u32 1
    %215 = call @func.101(%213, %214)
    br bb14(%215)
bb14(%26: u32):
    call @func.98(%0, %26)
    br bb43
bb15:
    %216 = load ptr, ptr %97
    call @func.36(%0, %216)
    br bb43
bb16(%27: ptr, %28: u32, %29: ptr, %30: ptr):
    %217 = const bool true
    call @func.103(%99, %30, %27, %28)
    br bb17(%27, %28, %29)
bb17(%31: ptr, %32: u32, %33: ptr):
    %218 = load ptr, ptr %33
    %219 = const i64 16
    %220 = gep i8, ptr %218, %219
    br bb18(%31, %32, %220)
bb18(%34: ptr, %35: u32, %36: ptr):
    call @func.103(%100, %36, %34, %35)
    br bb19
bb19:
    %221 = const bool false
    call @func.99(%0, %99, %100)
    br bb20
bb20:
    %222 = const bool false
    br bb43
bb21(%37: ptr, %38: u32, %39: ptr, %40: ptr):
    %223 = const bool true
    call @func.103(%102, %40, %37, %38)
    br bb22(%37, %38, %39)
bb22(%41: ptr, %42: u32, %43: ptr):
    %224 = load ptr, ptr %43
    %225 = const i64 16
    %226 = gep i8, ptr %224, %225
    br bb23(%41, %42, %226)
bb23(%44: ptr, %45: u32, %46: ptr):
    %227 = const u32 1
    %228 = call @func.102(%45, %227)
    br bb24(%44, %46, %228)
bb24(%47: ptr, %48: ptr, %49: u32):
    call @func.103(%103, %48, %47, %49)
    br bb25
bb25:
    %229 = const bool false
    call @func.100(%0, %101, %102, %103)
    br bb26
bb26:
    %230 = const bool false
    br bb43
bb27(%50: ptr, %51: u32, %52: ptr, %53: ptr):
    %231 = const bool true
    call @func.103(%105, %53, %50, %51)
    br bb28(%50, %51, %52)
bb28(%54: ptr, %55: u32, %56: ptr):
    %232 = load ptr, ptr %56
    %233 = const i64 16
    %234 = gep i8, ptr %232, %233
    br bb29(%54, %55, %234)
bb29(%57: ptr, %58: u32, %59: ptr):
    %235 = const u32 1
    %236 = call @func.102(%58, %235)
    br bb30(%57, %59, %236)
bb30(%60: ptr, %61: ptr, %62: u32):
    call @func.103(%106, %61, %60, %62)
    br bb31
bb31:
    %237 = const bool false
    call @func.66(%0, %104, %105, %106)
    br bb32
bb32:
    %238 = const bool false
    br bb43
bb33(%63: ptr, %64: u32, %65: ptr, %66: ptr, %67: ptr, %68: ptr):
    %239 = const bool true
    call @func.103(%108, %68, %63, %64)
    br bb34(%63, %64, %65, %66, %67)
bb34(%69: ptr, %70: u32, %71: ptr, %72: ptr, %73: ptr):
    %240 = load ptr, ptr %71
    %241 = const i64 16
    %242 = gep i8, ptr %240, %241
    br bb35(%69, %70, %72, %73, %242)
bb35(%74: ptr, %75: u32, %76: ptr, %77: ptr, %78: ptr):
    call @func.103(%109, %78, %74, %75)
    br bb36(%74, %75, %76, %77)
bb36(%79: ptr, %80: u32, %81: ptr, %82: ptr):
    %243 = const bool true
    %244 = load ptr, ptr %81
    %245 = const i64 16
    %246 = gep i8, ptr %244, %245
    br bb37(%79, %80, %82, %246)
bb37(%83: ptr, %84: u32, %85: ptr, %86: ptr):
    %247 = const u32 1
    %248 = call @func.102(%84, %247)
    br bb38(%83, %85, %86, %248)
bb38(%87: ptr, %88: ptr, %89: ptr, %90: u32):
    call @func.103(%110, %89, %87, %90)
    br bb39(%88)
bb39(%91: ptr):
    %249 = load bool, ptr %91
    %250 = const bool false
    %251 = const bool false
    %252 = load u32, ptr %107
    call @func.116(%0, %252, %108, %109, %110, %249)
    br bb40
bb40:
    %253 = const bool false
    %254 = const bool false
    br bb43
bb41(%92: ptr, %93: u32, %94: u32, %95: ptr):
    call @func.103(%112, %95, %92, %93)
    br bb42(%94)
bb42(%96: u32):
    %255 = load u32, ptr %111
    call @func.117(%0, %255, %96, %112)
    br bb43
bb43:
    ret
}

fn @Verifier____env___try_iota_reduction(functy.104) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %3 = const i8 11
    store i8 %3, ptr %0
    ret
}

fn @Verifier____env___try_quot_reduction(functy.105) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %3 = const i8 11
    store i8 %3, ptr %0
    ret
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprE3lenBG_(functy.106) {
}

fn @_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_(functy.107) {
}

fn @Verifier____env___reduce_proj(functy.108) {
bb0(%0: ptr, %1: ptr, %2: ptr, %3: u32, %4: ptr):
    %41 = alloca (i64, i64, i64, i64, i64), align 8
    %42 = alloca (i64, i64, i64, i64, i64), align 8
    %43 = alloca i64, align 8
    %44 = alloca (i32, i32), align 4
    %45 = alloca (i64, i64, i64), align 8
    %46 = alloca (i64, i64), align 8
    %47 = alloca (i64, i64, i64, i64), align 8
    %48 = alloca i32, align 4
    %49 = alloca i64, align 8
    %50 = alloca (i64, i64, i64, i64, i64), align 8
    %51 = const bool false
    %52 = const bool true
    call @func.46(%41, %1, %4)
    br bb1(%1, %2, %3)
bb1(%5: ptr, %6: ptr, %7: u32):
    call @func.119(%42, %41)
    br bb2(%5, %6, %7)
bb2(%8: ptr, %9: ptr, %10: u32):
    store ptr %42, ptr %43
    %53 = load ptr, ptr %43
    %54 = load i8, ptr %53
    %55 = sext i8 %54 to i64
    switch %55 [ 3: bb3(%8, %9, %10) default: bb13(%9, %10) ]
bb3(%11: ptr, %12: ptr, %13: u32):
    %56 = load ptr, ptr %43
    %57 = const i64 4
    %58 = gep i8, ptr %56, %57
    call @func.120(%44, %11, %58)
    br bb4(%11, %12, %13)
bb4(%14: ptr, %15: ptr, %16: u32):
    %59 = load i32, ptr %44
    %60 = sext i32 %59 to i64
    switch %60 [ 1: bb5(%14, %15, %16) 0: bb13(%15, %16) default: bb21 ]
bb5(%17: ptr, %18: ptr, %19: u32):
    %61 = const i64 4
    %62 = gep i8, ptr %44, %61
    %63 = load u32, ptr %62
    call @func.126(%45, %41)
    br bb6(%17, %18, %19, %63)
bb6(%20: ptr, %21: ptr, %22: u32, %23: u32):
    %64 = zext u32 %23 to u64
    %65 = zext u32 %22 to u64
    %66, %67 = add.overflow u64 %64, %65
    store u64 %66, ptr %46
    %68 = const i64 8
    %69 = gep i8, ptr %46, %68
    store bool %67, ptr %69
    %70 = const i64 8
    %71 = gep i8, ptr %46, %70
    %72 = load bool, ptr %71
    %73 = const bool false
    %74 = icmp eq bool %72, %73
    condbr %74, bb7(%20, %21, %22), bb22
bb7(%24: ptr, %25: ptr, %26: u32):
    %75 = load u64, ptr %46
    %76 = call @func.106(%45)
    br bb8(%24, %25, %26, %75, %76)
bb8(%27: ptr, %28: ptr, %29: u32, %30: u64, %31: u64):
    %77 = icmp ult u64 %30, %31
    condbr %77, bb9(%27, %30), bb12(%28, %29)
bb9(%32: ptr, %33: u64):
    %78 = call @func.107(%45, %33)
    br bb10(%32, %78)
bb10(%34: ptr, %35: ptr):
    call @func.46(%0, %34, %35)
    br bb11
bb11:
    br bb17
bb12(%36: ptr, %37: u32):
    br bb13(%36, %37)
bb13(%38: ptr, %39: u32):
    %79 = load i32, ptr %38
    store i32 %79, ptr %48
    %80 = const bool false
    %81 = load i64, ptr %41
    store i64 %81, ptr %50
    %82 = const i64 8
    %83 = gep i8, ptr %41, %82
    %84 = const i64 8
    %85 = gep i8, ptr %50, %84
    %86 = load i64, ptr %83
    store i64 %86, ptr %85
    %87 = const i64 16
    %88 = gep i8, ptr %41, %87
    %89 = const i64 16
    %90 = gep i8, ptr %50, %89
    %91 = load i64, ptr %88
    store i64 %91, ptr %90
    %92 = const i64 24
    %93 = gep i8, ptr %41, %92
    %94 = const i64 24
    %95 = gep i8, ptr %50, %94
    %96 = load i64, ptr %93
    store i64 %96, ptr %95
    %97 = const i64 32
    %98 = gep i8, ptr %41, %97
    %99 = const i64 32
    %100 = gep i8, ptr %50, %99
    %101 = load i64, ptr %98
    store i64 %101, ptr %100
    %102 = const i64 56
    %103 = heap_alloc rust_heap i8, %102, align 8
    %104 = const u64 1
    store u64 %104, ptr %103
    %105 = const i64 8
    %106 = gep i8, ptr %103, %105
    %107 = const u64 1
    store u64 %107, ptr %106
    %108 = const i64 16
    %109 = gep i8, ptr %103, %108
    %110 = load i64, ptr %50
    store i64 %110, ptr %109
    %111 = const i64 8
    %112 = gep i8, ptr %50, %111
    %113 = const i64 8
    %114 = gep i8, ptr %109, %113
    %115 = load i64, ptr %112
    store i64 %115, ptr %114
    %116 = const i64 16
    %117 = gep i8, ptr %50, %116
    %118 = const i64 16
    %119 = gep i8, ptr %109, %118
    %120 = load i64, ptr %117
    store i64 %120, ptr %119
    %121 = const i64 24
    %122 = gep i8, ptr %50, %121
    %123 = const i64 24
    %124 = gep i8, ptr %109, %123
    %125 = load i64, ptr %122
    store i64 %125, ptr %124
    %126 = const i64 32
    %127 = gep i8, ptr %50, %126
    %128 = const i64 32
    %129 = gep i8, ptr %109, %128
    %130 = load i64, ptr %127
    store i64 %130, ptr %129
    store ptr %103, ptr %49
    br bb14(%39)
bb14(%40: u32):
    %131 = const i64 4
    %132 = gep i8, ptr %47, %131
    %133 = load i32, ptr %48
    store i32 %133, ptr %132
    %134 = const i64 8
    %135 = gep i8, ptr %47, %134
    store u32 %40, ptr %135
    %136 = load ptr, ptr %49
    %137 = const i64 16
    %138 = gep i8, ptr %47, %137
    store ptr %136, ptr %138
    %139 = const i8 9
    store i8 %139, ptr %47
    call @func.96(%0, %47)
    br bb15
bb15:
    br bb16
bb16:
    %140 = const bool false
    br bb20
bb17:
    br bb18
bb18:
    br bb19
bb19:
    %141 = const bool false
    br bb20
bb20:
    ret
bb21:
    unreachable
bb22:
    unreachable
}

fn @_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelNtB7_9PartialEq2eqBF_(functy.109) {
}

fn @Level__is_def_eq(functy.110) {
bb0(%0: ptr, %1: ptr):
    %7 = alloca i64, align 8
    %8 = alloca i64, align 8
    %9 = alloca (i64, i64, i64), align 8
    %10 = alloca (i64, i64, i64), align 8
    store ptr %0, ptr %7
    store ptr %1, ptr %8
    %11 = call @func.109(%7, %8)
    br bb1(%11)
bb1(%2: bool):
    condbr %2, bb2, bb3
bb2:
    %12 = const bool true
    br bb8(%12)
bb3:
    %13 = load ptr, ptr %7
    call @func.127(%9, %13)
    br bb4
bb4:
    %14 = load ptr, ptr %8
    call @func.127(%10, %14)
    br bb5(%9)
bb5(%3: ptr):
    %15 = call @func.78(%3, %10)
    br bb6(%15)
bb6(%4: bool):
    br bb7(%4)
bb7(%5: bool):
    br bb8(%5)
bb8(%6: bool):
    ret %6
}

fn @Expr__lift_from(functy.111) {
bb0(%0: ptr, %1: ptr, %2: u32, %3: u32):
    call @func.64(%0, %1, %2, %3)
    br bb1
bb1:
    ret
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm14saturating_add(functy.112) {
}

fn @_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3minCshhXhIKvfvMU_25clean_decl_universe_slice(functy.113) {
}

fn @ExprKind__compute_meta(functy.114) {
bb0(%0: ptr, %1: ptr):
    %99 = alloca i64, align 8
    %100 = alloca i64, align 8
    %101 = alloca i64, align 8
    %102 = alloca i64, align 8
    %103 = alloca i64, align 8
    %104 = alloca i64, align 8
    %105 = alloca i64, align 8
    %106 = alloca i64, align 8
    %107 = alloca i64, align 8
    %108 = alloca i64, align 8
    %109 = alloca i64, align 8
    %110 = alloca (i32, i32), align 4
    %111 = alloca i64, align 8
    store ptr %1, ptr %99
    %112 = load ptr, ptr %99
    %113 = load i8, ptr %112
    %114 = sext i8 %113 to i64
    switch %114 [ 0: bb12 1: bb8 2: bb7 3: bb6 4: bb11 5: bb10 6: bb9 7: bb5 8: bb4 9: bb3 10: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %115 = load ptr, ptr %99
    %116 = const i64 8
    %117 = gep i8, ptr %115, %116
    %118 = load ptr, ptr %117
    %119 = const i64 16
    %120 = gep i8, ptr %118, %119
    br bb57(%120)
bb3:
    %121 = load ptr, ptr %99
    %122 = const i64 4
    %123 = gep i8, ptr %121, %122
    %124 = load ptr, ptr %99
    %125 = const i64 8
    %126 = gep i8, ptr %124, %125
    %127 = load ptr, ptr %99
    %128 = const i64 16
    %129 = gep i8, ptr %127, %128
    %130 = load ptr, ptr %129
    %131 = const i64 16
    %132 = gep i8, ptr %130, %131
    br bb42(%123, %126, %132)
bb4:
    %133 = load ptr, ptr %99
    %134 = const i64 8
    %135 = gep i8, ptr %133, %134
    %136 = call @func.128(%135)
    br bb40(%136)
bb5:
    %137 = load ptr, ptr %99
    %138 = const i64 8
    %139 = gep i8, ptr %137, %138
    %140 = load ptr, ptr %99
    %141 = const i64 16
    %142 = gep i8, ptr %140, %141
    %143 = load ptr, ptr %99
    %144 = const i64 24
    %145 = gep i8, ptr %143, %144
    %146 = load ptr, ptr %139
    %147 = const i64 16
    %148 = gep i8, ptr %146, %147
    br bb34(%142, %145, %148)
bb6:
    %149 = load ptr, ptr %99
    %150 = const i64 4
    %151 = gep i8, ptr %149, %150
    %152 = load ptr, ptr %99
    %153 = const i64 8
    %154 = gep i8, ptr %152, %153
    %155 = call @func.129(%151)
    br bb32(%155)
bb7:
    %156 = load ptr, ptr %99
    %157 = const i64 8
    %158 = gep i8, ptr %156, %157
    %159 = call @func.130(%158)
    br bb28(%158, %159)
bb8:
    %160 = load ptr, ptr %99
    %161 = const i64 8
    %162 = gep i8, ptr %160, %161
    %163 = load u64, ptr %162
    %164 = const u64 13
    %165 = call @func.132(%164, %163)
    br bb27(%165)
bb9:
    %166 = load ptr, ptr %99
    %167 = const i64 1
    %168 = gep i8, ptr %166, %167
    %169 = load ptr, ptr %99
    %170 = const i64 8
    %171 = gep i8, ptr %169, %170
    %172 = load ptr, ptr %99
    %173 = const i64 16
    %174 = gep i8, ptr %172, %173
    %175 = load ptr, ptr %171
    %176 = const i64 16
    %177 = gep i8, ptr %175, %176
    br bb23(%174, %177)
bb10:
    %178 = load ptr, ptr %99
    %179 = const i64 1
    %180 = gep i8, ptr %178, %179
    %181 = load ptr, ptr %99
    %182 = const i64 8
    %183 = gep i8, ptr %181, %182
    %184 = load ptr, ptr %99
    %185 = const i64 16
    %186 = gep i8, ptr %184, %185
    %187 = load ptr, ptr %183
    %188 = const i64 16
    %189 = gep i8, ptr %187, %188
    br bb19(%186, %189)
bb11:
    %190 = load ptr, ptr %99
    %191 = const i64 8
    %192 = gep i8, ptr %190, %191
    %193 = load ptr, ptr %99
    %194 = const i64 16
    %195 = gep i8, ptr %193, %194
    %196 = load ptr, ptr %192
    %197 = const i64 16
    %198 = gep i8, ptr %196, %197
    br bb15(%195, %198)
bb12:
    %199 = load ptr, ptr %99
    %200 = const i64 4
    %201 = gep i8, ptr %199, %200
    %202 = load u32, ptr %201
    %203 = zext u32 %202 to u64
    %204 = const u64 7
    %205 = call @func.132(%204, %203)
    br bb13(%201, %205)
bb13(%2: ptr, %3: u64):
    %206 = trunc u64 %3 to u32
    %207 = load u32, ptr %2
    %208 = const u32 1
    %209 = call @func.112(%207, %208)
    br bb14(%206, %209)
bb14(%4: u32, %5: u32):
    %210 = const u32 0
    %211 = const bool false
    %212 = const bool false
    %213 = const bool false
    %214 = const bool false
    call @func.134(%0, %4, %5, %210, %211, %212, %213, %214)
    br bb59
bb15(%6: ptr, %7: ptr):
    call @func.135(%100, %7)
    br bb16(%6)
bb16(%8: ptr):
    %215 = load ptr, ptr %8
    %216 = const i64 16
    %217 = gep i8, ptr %215, %216
    br bb17(%217)
bb17(%9: ptr):
    call @func.135(%101, %9)
    br bb18
bb18:
    %218 = load u64, ptr %100
    %219 = load u64, ptr %101
    call @func.139(%0, %218, %219)
    br bb59
bb19(%10: ptr, %11: ptr):
    call @func.135(%102, %11)
    br bb20(%10)
bb20(%12: ptr):
    %220 = load ptr, ptr %12
    %221 = const i64 16
    %222 = gep i8, ptr %220, %221
    br bb21(%222)
bb21(%13: ptr):
    call @func.135(%103, %13)
    br bb22
bb22:
    %223 = load u64, ptr %102
    %224 = load u64, ptr %103
    %225 = const u64 0
    call @func.144(%0, %223, %224, %225)
    br bb59
bb23(%14: ptr, %15: ptr):
    call @func.135(%104, %15)
    br bb24(%14)
bb24(%16: ptr):
    %226 = load ptr, ptr %16
    %227 = const i64 16
    %228 = gep i8, ptr %226, %227
    br bb25(%228)
bb25(%17: ptr):
    call @func.135(%105, %17)
    br bb26
bb26:
    %229 = load u64, ptr %104
    %230 = load u64, ptr %105
    %231 = const u64 1
    call @func.144(%0, %229, %230, %231)
    br bb59
bb27(%18: u64):
    %232 = trunc u64 %18 to u32
    %233 = const u32 0
    %234 = const u32 0
    %235 = const bool true
    %236 = const bool false
    %237 = const bool false
    %238 = const bool false
    call @func.134(%0, %232, %233, %234, %235, %236, %237, %238)
    br bb59
bb28(%19: ptr, %20: u64):
    %239 = const u64 11
    %240 = call @func.132(%239, %20)
    br bb29(%19, %240)
bb29(%21: ptr, %22: u64):
    %241 = trunc u64 %22 to u32
    %242 = call @func.145(%21)
    br bb30(%21, %241, %242)
bb30(%23: ptr, %24: u32, %25: bool):
    %243 = call @func.146(%23)
    br bb31(%24, %25, %243)
bb31(%26: u32, %27: bool, %28: bool):
    %244 = const u32 0
    %245 = const u32 0
    %246 = const bool false
    %247 = const bool false
    call @func.134(%0, %26, %244, %245, %246, %247, %27, %28)
    br bb59
bb32(%29: u64):
    %248 = const u64 5
    %249 = call @func.132(%248, %29)
    br bb33(%249)
bb33(%30: u64):
    %250 = trunc u64 %30 to u32
    %251 = const u32 0
    %252 = const u32 0
    %253 = const bool false
    %254 = const bool false
    %255 = const bool false
    %256 = const bool false
    call @func.134(%0, %250, %251, %252, %253, %254, %255, %256)
    br bb59
bb34(%31: ptr, %32: ptr, %33: ptr):
    call @func.135(%106, %33)
    br bb35(%31, %32)
bb35(%34: ptr, %35: ptr):
    %257 = load ptr, ptr %34
    %258 = const i64 16
    %259 = gep i8, ptr %257, %258
    br bb36(%35, %259)
bb36(%36: ptr, %37: ptr):
    call @func.135(%107, %37)
    br bb37(%36)
bb37(%38: ptr):
    %260 = load ptr, ptr %38
    %261 = const i64 16
    %262 = gep i8, ptr %260, %261
    br bb38(%262)
bb38(%39: ptr):
    call @func.135(%108, %39)
    br bb39
bb39:
    %263 = load u64, ptr %106
    %264 = load u64, ptr %107
    %265 = load u64, ptr %108
    call @func.151(%0, %263, %264, %265)
    br bb59
bb40(%40: u64):
    %266 = const u64 3
    %267 = call @func.132(%266, %40)
    br bb41(%267)
bb41(%41: u64):
    %268 = trunc u64 %41 to u32
    %269 = const u32 0
    %270 = const u32 0
    %271 = const bool false
    %272 = const bool false
    %273 = const bool false
    %274 = const bool false
    call @func.134(%0, %268, %269, %270, %271, %272, %273, %274)
    br bb59
bb42(%42: ptr, %43: ptr, %44: ptr):
    call @func.135(%109, %44)
    br bb43(%42, %43)
bb43(%45: ptr, %46: ptr):
    %275 = load u64, ptr %109
    %276 = call @func.152(%275)
    br bb44(%45, %46, %276)
bb44(%47: ptr, %48: ptr, %49: u8):
    %277 = zext u8 %49 to u32
    %278 = const u32 1
    %279, %280 = add.overflow u32 %277, %278
    store u32 %279, ptr %110
    %281 = const i64 4
    %282 = gep i8, ptr %110, %281
    store bool %280, ptr %282
    %283 = const i64 4
    %284 = gep i8, ptr %110, %283
    %285 = load bool, ptr %284
    %286 = const bool false
    %287 = icmp eq bool %285, %286
    condbr %287, bb45(%47, %48), bb60
bb45(%50: ptr, %51: ptr):
    %288 = load u32, ptr %110
    %289 = const u32 255
    %290 = call @func.113(%288, %289)
    br bb46(%50, %51, %290)
bb46(%52: ptr, %53: ptr, %54: u32):
    %291 = zext u32 %54 to u64
    %292 = call @func.129(%52)
    br bb47(%53, %54, %291, %292)
bb47(%55: ptr, %56: u32, %57: u64, %58: u64):
    %293 = load u32, ptr %55
    %294 = zext u32 %293 to u64
    %295 = load u64, ptr %109
    %296 = call @func.153(%295)
    br bb48(%56, %57, %58, %294, %296)
bb48(%59: u32, %60: u64, %61: u64, %62: u64, %63: u32):
    %297 = zext u32 %63 to u64
    %298 = call @func.132(%62, %297)
    br bb49(%59, %60, %61, %298)
bb49(%64: u32, %65: u64, %66: u64, %67: u64):
    %299 = call @func.132(%66, %67)
    br bb50(%64, %65, %299)
bb50(%68: u32, %69: u64, %70: u64):
    %300 = call @func.132(%69, %70)
    br bb51(%68, %300)
bb51(%71: u32, %72: u64):
    %301 = trunc u64 %72 to u32
    %302 = load u64, ptr %109
    %303 = call @func.115(%302)
    br bb52(%71, %301, %303)
bb52(%73: u32, %74: u32, %75: u32):
    %304 = load u64, ptr %109
    %305 = call @func.21(%304)
    br bb53(%73, %74, %75, %305)
bb53(%76: u32, %77: u32, %78: u32, %79: bool):
    %306 = load u64, ptr %109
    %307 = call @func.19(%306)
    br bb54(%76, %77, %78, %79, %307)
bb54(%80: u32, %81: u32, %82: u32, %83: bool, %84: bool):
    %308 = load u64, ptr %109
    %309 = call @func.20(%308)
    br bb55(%80, %81, %82, %83, %84, %309)
bb55(%85: u32, %86: u32, %87: u32, %88: bool, %89: bool, %90: bool):
    %310 = load u64, ptr %109
    %311 = call @func.154(%310)
    br bb56(%85, %86, %87, %88, %89, %90, %311)
bb56(%91: u32, %92: u32, %93: u32, %94: bool, %95: bool, %96: bool, %97: bool):
    call @func.134(%0, %92, %93, %91, %94, %95, %96, %97)
    br bb59
bb57(%98: ptr):
    call @func.135(%111, %98)
    br bb58
bb58:
    %312 = load u64, ptr %111
    %313 = const u64 0
    call @func.156(%0, %312, %313)
    br bb59
bb59:
    ret
bb60:
    unreachable
}

fn @ExprMeta__loose_bvar_range(functy.115) {
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

fn @Expr__lett(functy.116) {
bb0(%0: ptr, %1: u32, %2: ptr, %3: ptr, %4: ptr, %5: bool):
    %9 = alloca i32, align 4
    %10 = alloca (i64, i64, i64, i64), align 8
    %11 = alloca i64, align 8
    %12 = alloca i64, align 8
    %13 = alloca (i64, i64, i64, i64, i64), align 8
    %14 = alloca i64, align 8
    %15 = alloca (i64, i64, i64, i64, i64), align 8
    store u32 %1, ptr %9
    %16 = const bool false
    %17 = const bool false
    %18 = const bool true
    %19 = const bool true
    %20 = const i64 56
    %21 = heap_alloc rust_heap i8, %20, align 8
    %22 = const u64 1
    store u64 %22, ptr %21
    %23 = const i64 8
    %24 = gep i8, ptr %21, %23
    %25 = const u64 1
    store u64 %25, ptr %24
    %26 = const i64 16
    %27 = gep i8, ptr %21, %26
    %28 = load i64, ptr %2
    store i64 %28, ptr %27
    %29 = const i64 8
    %30 = gep i8, ptr %2, %29
    %31 = const i64 8
    %32 = gep i8, ptr %27, %31
    %33 = load i64, ptr %30
    store i64 %33, ptr %32
    %34 = const i64 16
    %35 = gep i8, ptr %2, %34
    %36 = const i64 16
    %37 = gep i8, ptr %27, %36
    %38 = load i64, ptr %35
    store i64 %38, ptr %37
    %39 = const i64 24
    %40 = gep i8, ptr %2, %39
    %41 = const i64 24
    %42 = gep i8, ptr %27, %41
    %43 = load i64, ptr %40
    store i64 %43, ptr %42
    %44 = const i64 32
    %45 = gep i8, ptr %2, %44
    %46 = const i64 32
    %47 = gep i8, ptr %27, %46
    %48 = load i64, ptr %45
    store i64 %48, ptr %47
    store ptr %21, ptr %11
    br bb1(%5)
bb1(%6: bool):
    %49 = const bool false
    %50 = load i64, ptr %3
    store i64 %50, ptr %13
    %51 = const i64 8
    %52 = gep i8, ptr %3, %51
    %53 = const i64 8
    %54 = gep i8, ptr %13, %53
    %55 = load i64, ptr %52
    store i64 %55, ptr %54
    %56 = const i64 16
    %57 = gep i8, ptr %3, %56
    %58 = const i64 16
    %59 = gep i8, ptr %13, %58
    %60 = load i64, ptr %57
    store i64 %60, ptr %59
    %61 = const i64 24
    %62 = gep i8, ptr %3, %61
    %63 = const i64 24
    %64 = gep i8, ptr %13, %63
    %65 = load i64, ptr %62
    store i64 %65, ptr %64
    %66 = const i64 32
    %67 = gep i8, ptr %3, %66
    %68 = const i64 32
    %69 = gep i8, ptr %13, %68
    %70 = load i64, ptr %67
    store i64 %70, ptr %69
    %71 = const i64 56
    %72 = heap_alloc rust_heap i8, %71, align 8
    %73 = const u64 1
    store u64 %73, ptr %72
    %74 = const i64 8
    %75 = gep i8, ptr %72, %74
    %76 = const u64 1
    store u64 %76, ptr %75
    %77 = const i64 16
    %78 = gep i8, ptr %72, %77
    %79 = load i64, ptr %13
    store i64 %79, ptr %78
    %80 = const i64 8
    %81 = gep i8, ptr %13, %80
    %82 = const i64 8
    %83 = gep i8, ptr %78, %82
    %84 = load i64, ptr %81
    store i64 %84, ptr %83
    %85 = const i64 16
    %86 = gep i8, ptr %13, %85
    %87 = const i64 16
    %88 = gep i8, ptr %78, %87
    %89 = load i64, ptr %86
    store i64 %89, ptr %88
    %90 = const i64 24
    %91 = gep i8, ptr %13, %90
    %92 = const i64 24
    %93 = gep i8, ptr %78, %92
    %94 = load i64, ptr %91
    store i64 %94, ptr %93
    %95 = const i64 32
    %96 = gep i8, ptr %13, %95
    %97 = const i64 32
    %98 = gep i8, ptr %78, %97
    %99 = load i64, ptr %96
    store i64 %99, ptr %98
    store ptr %72, ptr %12
    br bb2(%6)
bb2(%7: bool):
    %100 = const bool false
    %101 = load i64, ptr %4
    store i64 %101, ptr %15
    %102 = const i64 8
    %103 = gep i8, ptr %4, %102
    %104 = const i64 8
    %105 = gep i8, ptr %15, %104
    %106 = load i64, ptr %103
    store i64 %106, ptr %105
    %107 = const i64 16
    %108 = gep i8, ptr %4, %107
    %109 = const i64 16
    %110 = gep i8, ptr %15, %109
    %111 = load i64, ptr %108
    store i64 %111, ptr %110
    %112 = const i64 24
    %113 = gep i8, ptr %4, %112
    %114 = const i64 24
    %115 = gep i8, ptr %15, %114
    %116 = load i64, ptr %113
    store i64 %116, ptr %115
    %117 = const i64 32
    %118 = gep i8, ptr %4, %117
    %119 = const i64 32
    %120 = gep i8, ptr %15, %119
    %121 = load i64, ptr %118
    store i64 %121, ptr %120
    %122 = const i64 56
    %123 = heap_alloc rust_heap i8, %122, align 8
    %124 = const u64 1
    store u64 %124, ptr %123
    %125 = const i64 8
    %126 = gep i8, ptr %123, %125
    %127 = const u64 1
    store u64 %127, ptr %126
    %128 = const i64 16
    %129 = gep i8, ptr %123, %128
    %130 = load i64, ptr %15
    store i64 %130, ptr %129
    %131 = const i64 8
    %132 = gep i8, ptr %15, %131
    %133 = const i64 8
    %134 = gep i8, ptr %129, %133
    %135 = load i64, ptr %132
    store i64 %135, ptr %134
    %136 = const i64 16
    %137 = gep i8, ptr %15, %136
    %138 = const i64 16
    %139 = gep i8, ptr %129, %138
    %140 = load i64, ptr %137
    store i64 %140, ptr %139
    %141 = const i64 24
    %142 = gep i8, ptr %15, %141
    %143 = const i64 24
    %144 = gep i8, ptr %129, %143
    %145 = load i64, ptr %142
    store i64 %145, ptr %144
    %146 = const i64 32
    %147 = gep i8, ptr %15, %146
    %148 = const i64 32
    %149 = gep i8, ptr %129, %148
    %150 = load i64, ptr %147
    store i64 %150, ptr %149
    store ptr %123, ptr %14
    br bb3(%7)
bb3(%8: bool):
    %151 = const i64 4
    %152 = gep i8, ptr %10, %151
    %153 = load i32, ptr %9
    store i32 %153, ptr %152
    %154 = load ptr, ptr %11
    %155 = const i64 8
    %156 = gep i8, ptr %10, %155
    store ptr %154, ptr %156
    %157 = load ptr, ptr %12
    %158 = const i64 16
    %159 = gep i8, ptr %10, %158
    store ptr %157, ptr %159
    %160 = load ptr, ptr %14
    %161 = const i64 24
    %162 = gep i8, ptr %10, %161
    store ptr %160, ptr %162
    %163 = const i64 1
    %164 = gep i8, ptr %10, %163
    store bool %8, ptr %164
    %165 = const i8 7
    store i8 %165, ptr %10
    call @func.96(%0, %10)
    br bb4
bb4:
    ret
}

fn @Expr__proj(functy.117) {
bb0(%0: ptr, %1: u32, %2: u32, %3: ptr):
    %5 = alloca i32, align 4
    %6 = alloca (i64, i64, i64, i64), align 8
    %7 = alloca i64, align 8
    store u32 %1, ptr %5
    %8 = const i64 56
    %9 = heap_alloc rust_heap i8, %8, align 8
    %10 = const u64 1
    store u64 %10, ptr %9
    %11 = const i64 8
    %12 = gep i8, ptr %9, %11
    %13 = const u64 1
    store u64 %13, ptr %12
    %14 = const i64 16
    %15 = gep i8, ptr %9, %14
    %16 = load i64, ptr %3
    store i64 %16, ptr %15
    %17 = const i64 8
    %18 = gep i8, ptr %3, %17
    %19 = const i64 8
    %20 = gep i8, ptr %15, %19
    %21 = load i64, ptr %18
    store i64 %21, ptr %20
    %22 = const i64 16
    %23 = gep i8, ptr %3, %22
    %24 = const i64 16
    %25 = gep i8, ptr %15, %24
    %26 = load i64, ptr %23
    store i64 %26, ptr %25
    %27 = const i64 24
    %28 = gep i8, ptr %3, %27
    %29 = const i64 24
    %30 = gep i8, ptr %15, %29
    %31 = load i64, ptr %28
    store i64 %31, ptr %30
    %32 = const i64 32
    %33 = gep i8, ptr %3, %32
    %34 = const i64 32
    %35 = gep i8, ptr %15, %34
    %36 = load i64, ptr %33
    store i64 %36, ptr %35
    store ptr %9, ptr %7
    br bb1(%2)
bb1(%4: u32):
    %37 = const i64 4
    %38 = gep i8, ptr %6, %37
    %39 = load i32, ptr %5
    store i32 %39, ptr %38
    %40 = const i64 8
    %41 = gep i8, ptr %6, %40
    store u32 %4, ptr %41
    %42 = load ptr, ptr %7
    %43 = const i64 16
    %44 = gep i8, ptr %6, %43
    store ptr %42, ptr %44
    %45 = const i8 9
    store i8 %45, ptr %6
    call @func.96(%0, %6)
    br bb2
bb2:
    ret
}

fn @_RNvXs1j_NtCskTzINo8ZBH9_5alloc4syncINtB6_3ArcNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprEINtNtCs2EYQwhfuABO_4core7convert5AsRefBH_E6as_refBJ_(functy.118) {
}

fn @Expr__get_app_fn(functy.119) {
bb0(%0: ptr, %1: ptr):
    %3 = alloca (i64, i64, i64, i64, i64), align 8
    %4 = alloca (i64, i64, i64, i64, i64), align 8
    %5 = alloca i64, align 8
    call @func.36(%3, %1)
    br bb1
bb1:
    store ptr %3, ptr %5
    %6 = load ptr, ptr %5
    %7 = load i8, ptr %6
    %8 = sext i8 %7 to i64
    switch %8 [ 4: bb3 default: bb2 ]
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
    %26 = gep i8, ptr %3, %25
    %27 = const i64 32
    %28 = gep i8, ptr %0, %27
    %29 = load i64, ptr %26
    store i64 %29, ptr %28
    ret
bb3:
    %30 = load ptr, ptr %5
    %31 = const i64 8
    %32 = gep i8, ptr %30, %31
    %33 = call @func.118(%32)
    br bb4(%33)
bb4(%2: ptr):
    call @func.36(%4, %2)
    br bb5
bb5:
    br bb6
bb6:
    %34 = load i64, ptr %4
    store i64 %34, ptr %3
    %35 = const i64 8
    %36 = gep i8, ptr %4, %35
    %37 = const i64 8
    %38 = gep i8, ptr %3, %37
    %39 = load i64, ptr %36
    store i64 %39, ptr %38
    %40 = const i64 16
    %41 = gep i8, ptr %4, %40
    %42 = const i64 16
    %43 = gep i8, ptr %3, %42
    %44 = load i64, ptr %41
    store i64 %44, ptr %43
    %45 = const i64 24
    %46 = gep i8, ptr %4, %45
    %47 = const i64 24
    %48 = gep i8, ptr %3, %47
    %49 = load i64, ptr %46
    store i64 %49, ptr %48
    %50 = const i64 32
    %51 = gep i8, ptr %4, %50
    %52 = const i64 32
    %53 = gep i8, ptr %3, %52
    %54 = load i64, ptr %51
    store i64 %54, ptr %53
    br bb1
}

fn @Verifier____env___get_constructor_num_params(functy.120) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %28 = alloca i64, align 8
    %29 = alloca (i64, i64), align 8
    %30 = alloca (i64, i64), align 8
    %31 = alloca (i64, i64), align 8
    %32 = alloca (i64, i64), align 8
    %33 = alloca (i64, i64), align 8
    %34 = const u64 0
    %35 = const i64 16
    %36 = gep i8, ptr %1, %35
    %37 = load i64, ptr %36
    store i64 %37, ptr %31
    %38 = const i64 8
    %39 = gep i8, ptr %36, %38
    %40 = const i64 8
    %41 = gep i8, ptr %31, %40
    %42 = load i64, ptr %39
    store i64 %42, ptr %41
    %43 = const i64 8
    %44 = gep i8, ptr %31, %43
    %45 = load u64, ptr %44
    br bb1(%1, %2, %34, %45)
bb1(%3: ptr, %4: ptr, %5: u64, %6: u64):
    %46 = icmp ult u64 %5, %6
    condbr %46, bb2(%3, %4, %5, %6), bb8
bb2(%7: ptr, %8: ptr, %9: u64, %10: u64):
    %47 = const i64 16
    %48 = gep i8, ptr %7, %47
    %49 = load i64, ptr %48
    store i64 %49, ptr %32
    %50 = const i64 8
    %51 = gep i8, ptr %48, %50
    %52 = const i64 8
    %53 = gep i8, ptr %32, %52
    %54 = load i64, ptr %51
    store i64 %54, ptr %53
    %55 = load i64, ptr %32
    store i64 %55, ptr %29
    %56 = const i64 8
    %57 = gep i8, ptr %32, %56
    %58 = const i64 8
    %59 = gep i8, ptr %29, %58
    %60 = load i64, ptr %57
    store i64 %60, ptr %59
    %61 = const i64 8
    %62 = gep i8, ptr %29, %61
    %63 = load u64, ptr %62
    %64 = icmp ult u64 %9, %63
    condbr %64, bb3(%7, %8, %9, %10, %9), bb10
bb3(%11: ptr, %12: ptr, %13: u64, %14: u64, %15: u64):
    %65 = const i64 16
    %66 = gep i8, ptr %11, %65
    %67 = load i64, ptr %66
    store i64 %67, ptr %33
    %68 = const i64 8
    %69 = gep i8, ptr %66, %68
    %70 = const i64 8
    %71 = gep i8, ptr %33, %70
    %72 = load i64, ptr %69
    store i64 %72, ptr %71
    %73 = load ptr, ptr %33
    %74 = const u64 8
    %75 = mul u64 %15, %74
    %76 = gep i8, ptr %73, %75
    store ptr %76, ptr %28
    %77 = load ptr, ptr %28
    %78 = call @func.4(%77, %12)
    br bb4(%11, %12, %13, %14, %78)
bb4(%16: ptr, %17: ptr, %18: u64, %19: u64, %20: bool):
    condbr %20, bb5, bb6(%16, %17, %18, %19)
bb5:
    %79 = load ptr, ptr %28
    %80 = const i64 4
    %81 = gep i8, ptr %79, %80
    %82 = load u32, ptr %81
    %83 = const i64 4
    %84 = gep i8, ptr %0, %83
    store u32 %82, ptr %84
    %85 = const i32 1
    store i32 %85, ptr %0
    br bb9
bb6(%21: ptr, %22: ptr, %23: u64, %24: u64):
    %86 = const u64 1
    %87, %88 = add.overflow u64 %23, %86
    store u64 %87, ptr %30
    %89 = const i64 8
    %90 = gep i8, ptr %30, %89
    store bool %88, ptr %90
    %91 = const i64 8
    %92 = gep i8, ptr %30, %91
    %93 = load bool, ptr %92
    %94 = const bool false
    %95 = icmp eq bool %93, %94
    condbr %95, bb7(%21, %22, %24), bb10
bb7(%25: ptr, %26: ptr, %27: u64):
    %96 = load u64, ptr %30
    br bb1(%25, %26, %96, %27)
bb8:
    %97 = const i32 0
    store i32 %97, ptr %0
    br bb9
bb9:
    ret
bb10:
    unreachable
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprE3newBE_(functy.121) {
}

fn @_RNvXs1j_NtCskTzINo8ZBH9_5alloc4syncINtB6_3ArcNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprEINtNtCs2EYQwhfuABO_4core7convert5AsRefBH_E6as_refBJ_(functy.122) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprE4pushBH_(functy.123) {
}

fn @_RNvXs8_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprENtNtNtCs2EYQwhfuABO_4core3ops5deref8DerefMut9deref_mutBH_(functy.124) {
}

fn @_RNvMNtCs2EYQwhfuABO_4core5sliceSNtCshhXhIKvfvMU_25clean_decl_universe_slice4Expr7reverseBw_(functy.125) {
}

fn @Expr__get_app_args(functy.126) {
bb0(%0: ptr, %1: ptr):
    %10 = alloca (i64, i64, i64), align 8
    %11 = alloca (i64, i64, i64, i64, i64), align 8
    %12 = alloca i64, align 8
    %13 = alloca (i64, i64, i64, i64, i64), align 8
    %14 = alloca (i64, i64, i64, i64, i64), align 8
    %15 = alloca (i64, i64), align 8
    %16 = const bool false
    %17 = const bool true
    call @func.121(%10)
    br bb1(%1)
bb1(%2: ptr):
    call @func.36(%11, %2)
    br bb14
bb2:
    store ptr %11, ptr %12
    %18 = load ptr, ptr %12
    %19 = load i8, ptr %18
    %20 = sext i8 %19 to i64
    switch %20 [ 4: bb3 default: bb10 ]
bb3:
    %21 = load ptr, ptr %12
    %22 = const i64 8
    %23 = gep i8, ptr %21, %22
    %24 = load ptr, ptr %12
    %25 = const i64 16
    %26 = gep i8, ptr %24, %25
    %27 = call @func.122(%26)
    br bb4(%23, %10, %27)
bb4(%3: ptr, %4: ptr, %5: ptr):
    call @func.36(%13, %5)
    br bb5(%3, %4)
bb5(%6: ptr, %7: ptr):
    call @func.123(%7, %13)
    br bb6(%6)
bb6(%8: ptr):
    %28 = call @func.122(%8)
    br bb7(%28)
bb7(%9: ptr):
    call @func.36(%14, %9)
    br bb8
bb8:
    br bb9
bb9:
    %29 = load i64, ptr %14
    store i64 %29, ptr %11
    %30 = const i64 8
    %31 = gep i8, ptr %14, %30
    %32 = const i64 8
    %33 = gep i8, ptr %11, %32
    %34 = load i64, ptr %31
    store i64 %34, ptr %33
    %35 = const i64 16
    %36 = gep i8, ptr %14, %35
    %37 = const i64 16
    %38 = gep i8, ptr %11, %37
    %39 = load i64, ptr %36
    store i64 %39, ptr %38
    %40 = const i64 24
    %41 = gep i8, ptr %14, %40
    %42 = const i64 24
    %43 = gep i8, ptr %11, %42
    %44 = load i64, ptr %41
    store i64 %44, ptr %43
    %45 = const i64 32
    %46 = gep i8, ptr %14, %45
    %47 = const i64 32
    %48 = gep i8, ptr %11, %47
    %49 = load i64, ptr %46
    store i64 %49, ptr %48
    br bb2
bb10:
    call @func.124(%15, %10)
    br bb11
bb11:
    call @func.125(%15)
    br bb12
bb12:
    %50 = const bool false
    %51 = load i64, ptr %10
    store i64 %51, ptr %0
    %52 = const i64 8
    %53 = gep i8, ptr %10, %52
    %54 = const i64 8
    %55 = gep i8, ptr %0, %54
    %56 = load i64, ptr %53
    store i64 %56, ptr %55
    %57 = const i64 16
    %58 = gep i8, ptr %10, %57
    %59 = const i64 16
    %60 = gep i8, ptr %0, %59
    %61 = load i64, ptr %58
    store i64 %61, ptr %60
    br bb13
bb13:
    %62 = const bool false
    ret
bb14:
    br bb2
}

fn @Level__normalize(functy.127) {
bb0(%0: ptr, %1: ptr):
    call @func.157(%0, %1)
    br bb1
bb1:
    ret
}

fn @hash_lit(functy.128) {
bb0(%0: ptr):
    %3 = alloca i64, align 8
    call @func.158(%3)
    br bb1(%0)
bb1(%1: ptr):
    call @func.162(%1, %3)
    br bb2
bb2:
    %4 = call @func.163(%3)
    br bb3(%4)
bb3(%2: u64):
    ret %2
}

fn @hash_name(functy.129) {
bb0(%0: ptr):
    %3 = alloca i64, align 8
    call @func.158(%3)
    br bb1(%0)
bb1(%1: ptr):
    call @func.165(%1, %3)
    br bb2
bb2:
    %4 = call @func.163(%3)
    br bb3(%4)
bb3(%2: u64):
    ret %2
}

fn @hash_level(functy.130) {
bb0(%0: ptr):
    %3 = alloca i64, align 8
    call @func.158(%3)
    br bb1(%0)
bb1(%1: ptr):
    call @func.169(%1, %3)
    br bb2
bb2:
    %4 = call @func.163(%3)
    br bb3(%4)
bb3(%2: u64):
    ret %2
}

fn @_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_mul(functy.131) {
}

fn @mix_hash(functy.132) {
bb0(%0: u64, %1: u64):
    %8 = const u64 14313749767032793493
    %9 = call @func.131(%1, %8)
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
    %21 = call @func.131(%19, %20)
    br bb3(%21)
bb3(%7: u64):
    ret %7
bb4:
    unreachable
}

fn @_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3minCshhXhIKvfvMU_25clean_decl_universe_slice(functy.133) {
}

fn @ExprMeta__pack(functy.134) {
bb0(%0: ptr, %1: u32, %2: u32, %3: u32, %4: bool, %5: bool, %6: bool, %7: bool):
    %42 = const u32 255
    %43 = call @func.133(%3, %42)
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

fn @Expr__meta(functy.135) {
bb0(%0: ptr, %1: ptr):
    %2 = const i64 32
    %3 = gep i8, ptr %1, %2
    %4 = load i64, ptr %3
    store i64 %4, ptr %0
    ret
}

fn @_RNvYhNtNtCs2EYQwhfuABO_4core3cmp3Ord3maxCshhXhIKvfvMU_25clean_decl_universe_slice(functy.136) {
}

fn @_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3minCshhXhIKvfvMU_25clean_decl_universe_slice(functy.137) {
}

fn @_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3maxCshhXhIKvfvMU_25clean_decl_universe_slice(functy.138) {
}

fn @ExprMeta__mk_app_meta(functy.139) {
bb0(%0: ptr, %1: u64, %2: u64):
    %28 = alloca i64, align 8
    %29 = alloca i64, align 8
    %30 = alloca (i32, i32), align 4
    store u64 %1, ptr %28
    store u64 %2, ptr %29
    %31 = load u64, ptr %28
    %32 = call @func.152(%31)
    br bb1(%32)
bb1(%3: u8):
    %33 = load u64, ptr %29
    %34 = call @func.152(%33)
    br bb2(%3, %34)
bb2(%4: u8, %5: u8):
    %35 = call @func.136(%4, %5)
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
    %49 = call @func.137(%47, %48)
    br bb5(%49)
bb5(%7: u32):
    %50 = load u64, ptr %28
    %51 = call @func.115(%50)
    br bb6(%7, %51)
bb6(%8: u32, %9: u32):
    %52 = load u64, ptr %29
    %53 = call @func.115(%52)
    br bb7(%8, %9, %53)
bb7(%10: u32, %11: u32, %12: u32):
    %54 = call @func.138(%11, %12)
    br bb8(%10, %54)
bb8(%13: u32, %14: u32):
    %55 = load u64, ptr %28
    %56 = load u64, ptr %29
    %57 = call @func.132(%55, %56)
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

fn @_RNvYhNtNtCs2EYQwhfuABO_4core3cmp3Ord3maxCshhXhIKvfvMU_25clean_decl_universe_slice(functy.140) {
}

fn @_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3minCshhXhIKvfvMU_25clean_decl_universe_slice(functy.141) {
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm14saturating_sub(functy.142) {
}

fn @_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3maxCshhXhIKvfvMU_25clean_decl_universe_slice(functy.143) {
}

fn @ExprMeta__mk_binder_meta(functy.144) {
bb0(%0: ptr, %1: u64, %2: u64, %3: u64):
    %130 = alloca i64, align 8
    %131 = alloca i64, align 8
    %132 = alloca (i32, i32), align 4
    store u64 %1, ptr %130
    store u64 %2, ptr %131
    %133 = load u64, ptr %130
    %134 = call @func.152(%133)
    br bb1(%3, %134)
bb1(%4: u64, %5: u8):
    %135 = load u64, ptr %131
    %136 = call @func.152(%135)
    br bb2(%4, %5, %136)
bb2(%6: u64, %7: u8, %8: u8):
    %137 = call @func.140(%7, %8)
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
    %151 = call @func.141(%149, %150)
    br bb5(%11, %151)
bb5(%12: u64, %13: u32):
    %152 = load u64, ptr %131
    %153 = call @func.115(%152)
    br bb6(%12, %13, %153)
bb6(%14: u64, %15: u32, %16: u32):
    %154 = const u32 1
    %155 = call @func.142(%16, %154)
    br bb7(%14, %15, %155)
bb7(%17: u64, %18: u32, %19: u32):
    %156 = load u64, ptr %130
    %157 = call @func.115(%156)
    br bb8(%17, %18, %19, %157)
bb8(%20: u64, %21: u32, %22: u32, %23: u32):
    %158 = call @func.143(%23, %22)
    br bb9(%20, %21, %158)
bb9(%24: u64, %25: u32, %26: u32):
    %159 = zext u32 %25 to u64
    %160 = load u64, ptr %130
    %161 = call @func.153(%160)
    br bb10(%24, %25, %26, %159, %161)
bb10(%27: u64, %28: u32, %29: u32, %30: u64, %31: u32):
    %162 = zext u32 %31 to u64
    %163 = load u64, ptr %131
    %164 = call @func.153(%163)
    br bb11(%27, %28, %29, %30, %162, %164)
bb11(%32: u64, %33: u32, %34: u32, %35: u64, %36: u64, %37: u32):
    %165 = zext u32 %37 to u64
    %166 = call @func.132(%165, %32)
    br bb12(%33, %34, %35, %36, %166)
bb12(%38: u32, %39: u32, %40: u64, %41: u64, %42: u64):
    %167 = call @func.132(%41, %42)
    br bb13(%38, %39, %40, %167)
bb13(%43: u32, %44: u32, %45: u64, %46: u64):
    %168 = call @func.132(%45, %46)
    br bb14(%43, %44, %168)
bb14(%47: u32, %48: u32, %49: u64):
    %169 = trunc u64 %49 to u32
    %170 = load u64, ptr %130
    %171 = call @func.21(%170)
    br bb15(%47, %48, %169, %171)
bb15(%50: u32, %51: u32, %52: u32, %53: bool):
    condbr %53, bb16(%50, %51, %52), bb17(%50, %51, %52)
bb16(%54: u32, %55: u32, %56: u32):
    %172 = const bool true
    br bb18(%54, %55, %56, %172)
bb17(%57: u32, %58: u32, %59: u32):
    %173 = load u64, ptr %131
    %174 = call @func.21(%173)
    br bb18(%57, %58, %59, %174)
bb18(%60: u32, %61: u32, %62: u32, %63: bool):
    %175 = load u64, ptr %130
    %176 = call @func.19(%175)
    br bb19(%60, %61, %62, %63, %176)
bb19(%64: u32, %65: u32, %66: u32, %67: bool, %68: bool):
    condbr %68, bb20(%64, %65, %66, %67), bb21(%64, %65, %66, %67)
bb20(%69: u32, %70: u32, %71: u32, %72: bool):
    %177 = const bool true
    br bb22(%69, %70, %71, %72, %177)
bb21(%73: u32, %74: u32, %75: u32, %76: bool):
    %178 = load u64, ptr %131
    %179 = call @func.19(%178)
    br bb22(%73, %74, %75, %76, %179)
bb22(%77: u32, %78: u32, %79: u32, %80: bool, %81: bool):
    %180 = load u64, ptr %130
    %181 = call @func.20(%180)
    br bb23(%77, %78, %79, %80, %81, %181)
bb23(%82: u32, %83: u32, %84: u32, %85: bool, %86: bool, %87: bool):
    condbr %87, bb24(%82, %83, %84, %85, %86), bb25(%82, %83, %84, %85, %86)
bb24(%88: u32, %89: u32, %90: u32, %91: bool, %92: bool):
    %182 = const bool true
    br bb26(%88, %89, %90, %91, %92, %182)
bb25(%93: u32, %94: u32, %95: u32, %96: bool, %97: bool):
    %183 = load u64, ptr %131
    %184 = call @func.20(%183)
    br bb26(%93, %94, %95, %96, %97, %184)
bb26(%98: u32, %99: u32, %100: u32, %101: bool, %102: bool, %103: bool):
    %185 = load u64, ptr %130
    %186 = call @func.154(%185)
    br bb27(%98, %99, %100, %101, %102, %103, %186)
bb27(%104: u32, %105: u32, %106: u32, %107: bool, %108: bool, %109: bool, %110: bool):
    condbr %110, bb28(%104, %105, %106, %107, %108, %109), bb29(%104, %105, %106, %107, %108, %109)
bb28(%111: u32, %112: u32, %113: u32, %114: bool, %115: bool, %116: bool):
    %187 = const bool true
    br bb30(%111, %112, %113, %114, %115, %116, %187)
bb29(%117: u32, %118: u32, %119: u32, %120: bool, %121: bool, %122: bool):
    %188 = load u64, ptr %131
    %189 = call @func.154(%188)
    br bb30(%117, %118, %119, %120, %121, %122, %189)
bb30(%123: u32, %124: u32, %125: u32, %126: bool, %127: bool, %128: bool, %129: bool):
    call @func.134(%0, %125, %124, %123, %126, %127, %128, %129)
    br bb31
bb31:
    ret
bb32:
    unreachable
}

fn @level_has_mvar(functy.145) {
bb0(%0: ptr):
    %1 = const bool false
    ret %1
}

fn @Level__has_params(functy.146) {
bb0(%0: ptr):
    %11 = alloca i64, align 8
    store ptr %0, ptr %11
    %12 = load ptr, ptr %11
    %13 = load i32, ptr %12
    %14 = sext i32 %13 to i64
    switch %14 [ 0: bb6 1: bb5 2: bb4 3: bb3 4: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %15 = const bool true
    br bb14(%15)
bb3:
    %16 = load ptr, ptr %11
    %17 = const i64 8
    %18 = gep i8, ptr %16, %17
    %19 = load ptr, ptr %11
    %20 = const i64 16
    %21 = gep i8, ptr %19, %20
    br bb8(%18, %21)
bb4:
    %22 = load ptr, ptr %11
    %23 = const i64 8
    %24 = gep i8, ptr %22, %23
    %25 = load ptr, ptr %11
    %26 = const i64 16
    %27 = gep i8, ptr %25, %26
    br bb8(%24, %27)
bb5:
    %28 = load ptr, ptr %11
    %29 = const i64 8
    %30 = gep i8, ptr %28, %29
    %31 = load ptr, ptr %30
    %32 = const i64 16
    %33 = gep i8, ptr %31, %32
    br bb7(%33)
bb6:
    %34 = const bool false
    br bb14(%34)
bb7(%1: ptr):
    %35 = call @func.146(%1)
    br bb14(%35)
bb8(%2: ptr, %3: ptr):
    %36 = load ptr, ptr %2
    %37 = const i64 16
    %38 = gep i8, ptr %36, %37
    br bb9(%3, %38)
bb9(%4: ptr, %5: ptr):
    %39 = call @func.146(%5)
    br bb10(%4, %39)
bb10(%6: ptr, %7: bool):
    condbr %7, bb11, bb12(%6)
bb11:
    %40 = const bool true
    br bb14(%40)
bb12(%8: ptr):
    %41 = load ptr, ptr %8
    %42 = const i64 16
    %43 = gep i8, ptr %41, %42
    br bb13(%43)
bb13(%9: ptr):
    %44 = call @func.146(%9)
    br bb14(%44)
bb14(%10: bool):
    ret %10
}

fn @_RNvYhNtNtCs2EYQwhfuABO_4core3cmp3Ord3maxCshhXhIKvfvMU_25clean_decl_universe_slice(functy.147) {
}

fn @_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3minCshhXhIKvfvMU_25clean_decl_universe_slice(functy.148) {
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm14saturating_sub(functy.149) {
}

fn @_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3maxCshhXhIKvfvMU_25clean_decl_universe_slice(functy.150) {
}

fn @ExprMeta__mk_let_meta(functy.151) {
bb0(%0: ptr, %1: u64, %2: u64, %3: u64):
    %175 = alloca i64, align 8
    %176 = alloca i64, align 8
    %177 = alloca i64, align 8
    %178 = alloca (i32, i32), align 4
    store u64 %1, ptr %175
    store u64 %2, ptr %176
    store u64 %3, ptr %177
    %179 = load u64, ptr %175
    %180 = call @func.152(%179)
    br bb1(%180)
bb1(%4: u8):
    %181 = load u64, ptr %176
    %182 = call @func.152(%181)
    br bb2(%4, %182)
bb2(%5: u8, %6: u8):
    %183 = call @func.147(%5, %6)
    br bb3(%183)
bb3(%7: u8):
    %184 = load u64, ptr %177
    %185 = call @func.152(%184)
    br bb4(%7, %185)
bb4(%8: u8, %9: u8):
    %186 = call @func.147(%8, %9)
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
    %200 = call @func.148(%198, %199)
    br bb7(%200)
bb7(%11: u32):
    %201 = load u64, ptr %177
    %202 = call @func.115(%201)
    br bb8(%11, %202)
bb8(%12: u32, %13: u32):
    %203 = const u32 1
    %204 = call @func.149(%13, %203)
    br bb9(%12, %204)
bb9(%14: u32, %15: u32):
    %205 = load u64, ptr %175
    %206 = call @func.115(%205)
    br bb10(%14, %15, %206)
bb10(%16: u32, %17: u32, %18: u32):
    %207 = load u64, ptr %176
    %208 = call @func.115(%207)
    br bb11(%16, %17, %18, %208)
bb11(%19: u32, %20: u32, %21: u32, %22: u32):
    %209 = call @func.150(%21, %22)
    br bb12(%19, %20, %209)
bb12(%23: u32, %24: u32, %25: u32):
    %210 = call @func.150(%25, %24)
    br bb13(%23, %210)
bb13(%26: u32, %27: u32):
    %211 = zext u32 %26 to u64
    %212 = load u64, ptr %175
    %213 = call @func.153(%212)
    br bb14(%26, %27, %211, %213)
bb14(%28: u32, %29: u32, %30: u64, %31: u32):
    %214 = zext u32 %31 to u64
    %215 = load u64, ptr %176
    %216 = call @func.153(%215)
    br bb15(%28, %29, %30, %214, %216)
bb15(%32: u32, %33: u32, %34: u64, %35: u64, %36: u32):
    %217 = zext u32 %36 to u64
    %218 = load u64, ptr %177
    %219 = call @func.153(%218)
    br bb16(%32, %33, %34, %35, %217, %219)
bb16(%37: u32, %38: u32, %39: u64, %40: u64, %41: u64, %42: u32):
    %220 = zext u32 %42 to u64
    %221 = call @func.132(%41, %220)
    br bb17(%37, %38, %39, %40, %221)
bb17(%43: u32, %44: u32, %45: u64, %46: u64, %47: u64):
    %222 = call @func.132(%46, %47)
    br bb18(%43, %44, %45, %222)
bb18(%48: u32, %49: u32, %50: u64, %51: u64):
    %223 = call @func.132(%50, %51)
    br bb19(%48, %49, %223)
bb19(%52: u32, %53: u32, %54: u64):
    %224 = trunc u64 %54 to u32
    %225 = load u64, ptr %175
    %226 = call @func.21(%225)
    br bb20(%52, %53, %224, %226)
bb20(%55: u32, %56: u32, %57: u32, %58: bool):
    condbr %58, bb23(%55, %56, %57), bb21(%55, %56, %57)
bb21(%59: u32, %60: u32, %61: u32):
    %227 = load u64, ptr %176
    %228 = call @func.21(%227)
    br bb22(%59, %60, %61, %228)
bb22(%62: u32, %63: u32, %64: u32, %65: bool):
    condbr %65, bb23(%62, %63, %64), bb24(%62, %63, %64)
bb23(%66: u32, %67: u32, %68: u32):
    %229 = const bool true
    br bb25(%66, %67, %68, %229)
bb24(%69: u32, %70: u32, %71: u32):
    %230 = load u64, ptr %177
    %231 = call @func.21(%230)
    br bb25(%69, %70, %71, %231)
bb25(%72: u32, %73: u32, %74: u32, %75: bool):
    %232 = load u64, ptr %175
    %233 = call @func.19(%232)
    br bb26(%72, %73, %74, %75, %233)
bb26(%76: u32, %77: u32, %78: u32, %79: bool, %80: bool):
    condbr %80, bb29(%76, %77, %78, %79), bb27(%76, %77, %78, %79)
bb27(%81: u32, %82: u32, %83: u32, %84: bool):
    %234 = load u64, ptr %176
    %235 = call @func.19(%234)
    br bb28(%81, %82, %83, %84, %235)
bb28(%85: u32, %86: u32, %87: u32, %88: bool, %89: bool):
    condbr %89, bb29(%85, %86, %87, %88), bb30(%85, %86, %87, %88)
bb29(%90: u32, %91: u32, %92: u32, %93: bool):
    %236 = const bool true
    br bb31(%90, %91, %92, %93, %236)
bb30(%94: u32, %95: u32, %96: u32, %97: bool):
    %237 = load u64, ptr %177
    %238 = call @func.19(%237)
    br bb31(%94, %95, %96, %97, %238)
bb31(%98: u32, %99: u32, %100: u32, %101: bool, %102: bool):
    %239 = load u64, ptr %175
    %240 = call @func.20(%239)
    br bb32(%98, %99, %100, %101, %102, %240)
bb32(%103: u32, %104: u32, %105: u32, %106: bool, %107: bool, %108: bool):
    condbr %108, bb35(%103, %104, %105, %106, %107), bb33(%103, %104, %105, %106, %107)
bb33(%109: u32, %110: u32, %111: u32, %112: bool, %113: bool):
    %241 = load u64, ptr %176
    %242 = call @func.20(%241)
    br bb34(%109, %110, %111, %112, %113, %242)
bb34(%114: u32, %115: u32, %116: u32, %117: bool, %118: bool, %119: bool):
    condbr %119, bb35(%114, %115, %116, %117, %118), bb36(%114, %115, %116, %117, %118)
bb35(%120: u32, %121: u32, %122: u32, %123: bool, %124: bool):
    %243 = const bool true
    br bb37(%120, %121, %122, %123, %124, %243)
bb36(%125: u32, %126: u32, %127: u32, %128: bool, %129: bool):
    %244 = load u64, ptr %177
    %245 = call @func.20(%244)
    br bb37(%125, %126, %127, %128, %129, %245)
bb37(%130: u32, %131: u32, %132: u32, %133: bool, %134: bool, %135: bool):
    %246 = load u64, ptr %175
    %247 = call @func.154(%246)
    br bb38(%130, %131, %132, %133, %134, %135, %247)
bb38(%136: u32, %137: u32, %138: u32, %139: bool, %140: bool, %141: bool, %142: bool):
    condbr %142, bb41(%136, %137, %138, %139, %140, %141), bb39(%136, %137, %138, %139, %140, %141)
bb39(%143: u32, %144: u32, %145: u32, %146: bool, %147: bool, %148: bool):
    %248 = load u64, ptr %176
    %249 = call @func.154(%248)
    br bb40(%143, %144, %145, %146, %147, %148, %249)
bb40(%149: u32, %150: u32, %151: u32, %152: bool, %153: bool, %154: bool, %155: bool):
    condbr %155, bb41(%149, %150, %151, %152, %153, %154), bb42(%149, %150, %151, %152, %153, %154)
bb41(%156: u32, %157: u32, %158: u32, %159: bool, %160: bool, %161: bool):
    %250 = const bool true
    br bb43(%156, %157, %158, %159, %160, %161, %250)
bb42(%162: u32, %163: u32, %164: u32, %165: bool, %166: bool, %167: bool):
    %251 = load u64, ptr %177
    %252 = call @func.154(%251)
    br bb43(%162, %163, %164, %165, %166, %167, %252)
bb43(%168: u32, %169: u32, %170: u32, %171: bool, %172: bool, %173: bool, %174: bool):
    call @func.134(%0, %170, %169, %168, %171, %172, %173, %174)
    br bb44
bb44:
    ret
bb45:
    unreachable
}

fn @ExprMeta__approx_depth(functy.152) {
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

fn @ExprMeta__hash(functy.153) {
bb0(%0: u64):
    %1 = alloca i64, align 8
    store u64 %0, ptr %1
    %2 = load u64, ptr %1
    %3 = const u64 4294967295
    %4 = and u64 %2, %3
    %5 = trunc u64 %4 to u32
    ret %5
}

fn @ExprMeta__has_level_param(functy.154) {
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

fn @_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3minCshhXhIKvfvMU_25clean_decl_universe_slice(functy.155) {
}

fn @ExprMeta__mk_wrapper_meta(functy.156) {
bb0(%0: ptr, %1: u64, %2: u64):
    %42 = alloca i64, align 8
    %43 = alloca (i32, i32), align 4
    store u64 %1, ptr %42
    %44 = load u64, ptr %42
    %45 = call @func.152(%44)
    br bb1(%2, %45)
bb1(%3: u64, %4: u8):
    %46 = zext u8 %4 to u32
    %47 = const u32 1
    %48, %49 = add.overflow u32 %46, %47
    store u32 %48, ptr %43
    %50 = const i64 4
    %51 = gep i8, ptr %43, %50
    store bool %49, ptr %51
    %52 = const i64 4
    %53 = gep i8, ptr %43, %52
    %54 = load bool, ptr %53
    %55 = const bool false
    %56 = icmp eq bool %54, %55
    condbr %56, bb2(%3), bb13
bb2(%5: u64):
    %57 = load u32, ptr %43
    %58 = const u32 255
    %59 = call @func.155(%57, %58)
    br bb3(%5, %59)
bb3(%6: u64, %7: u32):
    %60 = zext u32 %7 to u64
    %61 = load u64, ptr %42
    %62 = call @func.153(%61)
    br bb4(%6, %7, %60, %62)
bb4(%8: u64, %9: u32, %10: u64, %11: u32):
    %63 = zext u32 %11 to u64
    %64 = call @func.132(%63, %8)
    br bb5(%9, %10, %64)
bb5(%12: u32, %13: u64, %14: u64):
    %65 = call @func.132(%13, %14)
    br bb6(%12, %65)
bb6(%15: u32, %16: u64):
    %66 = trunc u64 %16 to u32
    %67 = load u64, ptr %42
    %68 = call @func.115(%67)
    br bb7(%15, %66, %68)
bb7(%17: u32, %18: u32, %19: u32):
    %69 = load u64, ptr %42
    %70 = call @func.21(%69)
    br bb8(%17, %18, %19, %70)
bb8(%20: u32, %21: u32, %22: u32, %23: bool):
    %71 = load u64, ptr %42
    %72 = call @func.19(%71)
    br bb9(%20, %21, %22, %23, %72)
bb9(%24: u32, %25: u32, %26: u32, %27: bool, %28: bool):
    %73 = load u64, ptr %42
    %74 = call @func.20(%73)
    br bb10(%24, %25, %26, %27, %28, %74)
bb10(%29: u32, %30: u32, %31: u32, %32: bool, %33: bool, %34: bool):
    %75 = load u64, ptr %42
    %76 = call @func.154(%75)
    br bb11(%29, %30, %31, %32, %33, %34, %76)
bb11(%35: u32, %36: u32, %37: u32, %38: bool, %39: bool, %40: bool, %41: bool):
    call @func.134(%0, %36, %37, %35, %38, %39, %40, %41)
    br bb12
bb12:
    ret
bb13:
    unreachable
}

fn @Level__normalize_impl(functy.157) {
bb0(%0: ptr, %1: ptr):
    %31 = alloca i64, align 8
    %32 = alloca (i64, i64), align 8
    %33 = alloca (i64, i64, i64), align 8
    %34 = alloca i32, align 4
    %35 = alloca (i64, i64, i64), align 8
    %36 = alloca (i64, i64, i64), align 8
    %37 = alloca (i32, i32), align 4
    %38 = alloca (i64, i64, i64), align 8
    %39 = alloca (i64, i64, i64), align 8
    %40 = alloca (i64, i64, i64), align 8
    %41 = alloca (i64, i64, i64), align 8
    %42 = alloca (i64, i64, i64), align 8
    %43 = const bool false
    %44 = const bool false
    call @func.171(%32, %1)
    br bb1
bb1:
    %45 = load ptr, ptr %32
    store ptr %45, ptr %31
    %46 = const i64 8
    %47 = gep i8, ptr %32, %46
    %48 = load u32, ptr %47
    %49 = load ptr, ptr %31
    %50 = load i32, ptr %49
    %51 = sext i32 %50 to i64
    switch %51 [ 0: bb6(%48) 1: bb5 2: bb3(%48) 3: bb4(%48) 4: bb6(%48) default: bb2 ]
bb2:
    unreachable
bb3(%2: u32):
    %52 = load ptr, ptr %31
    call @func.180(%0, %52, %2)
    br bb30
bb4(%3: u32):
    %53 = load ptr, ptr %31
    %54 = const i64 8
    %55 = gep i8, ptr %53, %54
    %56 = load ptr, ptr %31
    %57 = const i64 16
    %58 = gep i8, ptr %56, %57
    %59 = load ptr, ptr %55
    %60 = const i64 16
    %61 = gep i8, ptr %59, %60
    br bb16(%3, %58, %61)
bb5:
    %62 = load ptr, ptr %31
    call @func.48(%0, %62)
    br bb30
bb6(%4: u32):
    %63 = load ptr, ptr %31
    %64 = load i32, ptr %63
    %65 = sext i32 %64 to i64
    switch %65 [ 0: bb9(%4) 4: bb8(%4) default: bb7(%4) ]
bb7(%5: u32):
    %66 = const bool true
    %67 = const i32 0
    store i32 %67, ptr %33
    br bb10(%5)
bb8(%6: u32):
    %68 = load ptr, ptr %31
    %69 = const i64 4
    %70 = gep i8, ptr %68, %69
    %71 = load i32, ptr %70
    store i32 %71, ptr %34
    %72 = const bool true
    %73 = const i64 4
    %74 = gep i8, ptr %33, %73
    %75 = load i32, ptr %34
    store i32 %75, ptr %74
    %76 = const i32 4
    store i32 %76, ptr %33
    br bb10(%6)
bb9(%7: u32):
    %77 = const bool true
    %78 = const i32 0
    store i32 %78, ptr %33
    br bb10(%7)
bb10(%8: u32):
    %79 = const u32 0
    br bb11(%8, %79)
bb11(%9: u32, %10: u32):
    %80 = icmp ult u32 %10, %9
    condbr %80, bb12(%9, %10), bb15
bb12(%11: u32, %12: u32):
    %81 = const bool false
    %82 = load i64, ptr %33
    store i64 %82, ptr %36
    %83 = const i64 8
    %84 = gep i8, ptr %33, %83
    %85 = const i64 8
    %86 = gep i8, ptr %36, %85
    %87 = load i64, ptr %84
    store i64 %87, ptr %86
    %88 = const i64 16
    %89 = gep i8, ptr %33, %88
    %90 = const i64 16
    %91 = gep i8, ptr %36, %90
    %92 = load i64, ptr %89
    store i64 %92, ptr %91
    call @func.61(%35, %36)
    br bb13(%11, %12)
bb13(%13: u32, %14: u32):
    %93 = const bool true
    %94 = load i64, ptr %35
    store i64 %94, ptr %33
    %95 = const i64 8
    %96 = gep i8, ptr %35, %95
    %97 = const i64 8
    %98 = gep i8, ptr %33, %97
    %99 = load i64, ptr %96
    store i64 %99, ptr %98
    %100 = const i64 16
    %101 = gep i8, ptr %35, %100
    %102 = const i64 16
    %103 = gep i8, ptr %33, %102
    %104 = load i64, ptr %101
    store i64 %104, ptr %103
    %105 = const u32 1
    %106, %107 = add.overflow u32 %14, %105
    store u32 %106, ptr %37
    %108 = const i64 4
    %109 = gep i8, ptr %37, %108
    store bool %107, ptr %109
    %110 = const i64 4
    %111 = gep i8, ptr %37, %110
    %112 = load bool, ptr %111
    %113 = const bool false
    %114 = icmp eq bool %112, %113
    condbr %114, bb14(%13), bb32
bb14(%15: u32):
    %115 = load u32, ptr %37
    br bb11(%15, %115)
bb15:
    %116 = const bool false
    %117 = load i64, ptr %33
    store i64 %117, ptr %0
    %118 = const i64 8
    %119 = gep i8, ptr %33, %118
    %120 = const i64 8
    %121 = gep i8, ptr %0, %120
    %122 = load i64, ptr %119
    store i64 %122, ptr %121
    %123 = const i64 16
    %124 = gep i8, ptr %33, %123
    %125 = const i64 16
    %126 = gep i8, ptr %0, %125
    %127 = load i64, ptr %124
    store i64 %127, ptr %126
    %128 = const bool false
    br bb30
bb16(%16: u32, %17: ptr, %18: ptr):
    %129 = const bool true
    call @func.157(%38, %18)
    br bb17(%16, %17)
bb17(%19: u32, %20: ptr):
    %130 = load ptr, ptr %20
    %131 = const i64 16
    %132 = gep i8, ptr %130, %131
    br bb18(%19, %132)
bb18(%21: u32, %22: ptr):
    call @func.157(%39, %22)
    br bb19(%21)
bb19(%23: u32):
    %133 = const bool false
    %134 = load i64, ptr %38
    store i64 %134, ptr %41
    %135 = const i64 8
    %136 = gep i8, ptr %38, %135
    %137 = const i64 8
    %138 = gep i8, ptr %41, %137
    %139 = load i64, ptr %136
    store i64 %139, ptr %138
    %140 = const i64 16
    %141 = gep i8, ptr %38, %140
    %142 = const i64 16
    %143 = gep i8, ptr %41, %142
    %144 = load i64, ptr %141
    store i64 %144, ptr %143
    call @func.49(%40, %41, %39)
    br bb20(%23)
bb20(%24: u32):
    %145 = load i32, ptr %40
    %146 = sext i32 %145 to i64
    switch %146 [ 2: bb22(%24) default: bb21(%24) ]
bb21(%25: u32):
    %147 = const bool false
    br bb23(%25, %147)
bb22(%26: u32):
    %148 = const bool true
    br bb23(%26, %148)
bb23(%27: u32, %28: bool):
    condbr %28, bb24(%27), bb27(%27)
bb24(%29: u32):
    call @func.181(%42, %40, %29)
    br bb25
bb25:
    call @func.157(%0, %42)
    br bb26
bb26:
    br bb28
bb27(%30: u32):
    call @func.181(%0, %40, %30)
    br bb31
bb28:
    br bb29
bb29:
    %149 = const bool false
    br bb30
bb30:
    ret
bb31:
    br bb28
bb32:
    unreachable
}

fn @KaniHasher__new(functy.158) {
bb0(%0: ptr):
    %1 = const u64 0
    store u64 %1, ptr %0
    ret
}

fn @_RINvXsg_NtNtCs2EYQwhfuABO_4core4hash5implsiNtB8_4Hash4hashNtCshhXhIKvfvMU_25clean_decl_universe_slice10KaniHasherEBW_(functy.159) {
}

fn @_RINvXs9_NtNtCs2EYQwhfuABO_4core4hash5implsmNtB8_4Hash4hashNtCshhXhIKvfvMU_25clean_decl_universe_slice10KaniHasherEBW_(functy.160) {
}

fn @_RINvXsa_NtNtCs2EYQwhfuABO_4core4hash5implsyNtB8_4Hash4hashNtCshhXhIKvfvMU_25clean_decl_universe_slice10KaniHasherEBW_(functy.161) {
}

fn @_Literal_as_std__hash__Hash___hash(functy.162) {
bb0(%0: ptr, %1: ptr):
    %5 = alloca i64, align 8
    %6 = alloca i64, align 8
    store ptr %0, ptr %5
    %7 = load ptr, ptr %5
    %8 = load i32, ptr %7
    %9 = sext i32 %8 to i64
    store i64 %9, ptr %6
    call @func.159(%6, %1)
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
    call @func.160(%15, %3)
    br bb5
bb4(%4: ptr):
    %16 = load ptr, ptr %5
    %17 = const i64 8
    %18 = gep i8, ptr %16, %17
    call @func.161(%18, %4)
    br bb5
bb5:
    ret
}

fn @_KaniHasher_as_std__hash__Hasher___finish(functy.163) {
bb0(%0: ptr):
    %1 = load u64, ptr %0
    ret %1
}

fn @_RINvXs9_NtNtCs2EYQwhfuABO_4core4hash5implsmNtB8_4Hash4hashNtCshhXhIKvfvMU_25clean_decl_universe_slice10KaniHasherEBW_(functy.164) {
}

fn @_Name_as_std__hash__Hash___hash(functy.165) {
bb0(%0: ptr, %1: ptr):
    %2 = alloca i64, align 8
    store ptr %0, ptr %2
    %3 = load ptr, ptr %2
    call @func.164(%3, %1)
    br bb1
bb1:
    ret
}

fn @_RINvNtCs2EYQwhfuABO_4core3mem12discriminantNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelEBH_(functy.166) {
}

fn @_RINvXs3_NtCs2EYQwhfuABO_4core3memINtB6_12DiscriminantNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelENtNtB8_4hash4Hash4hashNtBR_10KaniHasherEBR_(functy.167) {
}

fn @_RINvXs12_NtCskTzINo8ZBH9_5alloc4syncINtB7_3ArcNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelENtNtCs2EYQwhfuABO_4core4hash4Hash4hashNtBK_10KaniHasherEBK_(functy.168) {
}

fn @_Level_as_std__hash__Hash___hash(functy.169) {
bb0(%0: ptr, %1: ptr):
    %13 = alloca i64, align 8
    %14 = alloca i64, align 8
    store ptr %0, ptr %13
    %15 = load ptr, ptr %13
    call @func.166(%14, %15)
    br bb1(%1)
bb1(%2: ptr):
    call @func.167(%14, %2)
    br bb2(%2)
bb2(%3: ptr):
    %16 = load ptr, ptr %13
    %17 = load i32, ptr %16
    %18 = sext i32 %17 to i64
    switch %18 [ 0: bb10 1: bb7(%3) 2: bb6(%3) 3: bb5(%3) 4: bb4(%3) default: bb3 ]
bb3:
    unreachable
bb4(%4: ptr):
    %19 = load ptr, ptr %13
    %20 = const i64 4
    %21 = gep i8, ptr %19, %20
    call @func.165(%21, %4)
    br bb10
bb5(%5: ptr):
    %22 = load ptr, ptr %13
    %23 = const i64 8
    %24 = gep i8, ptr %22, %23
    %25 = load ptr, ptr %13
    %26 = const i64 16
    %27 = gep i8, ptr %25, %26
    br bb8(%5, %24, %27)
bb6(%6: ptr):
    %28 = load ptr, ptr %13
    %29 = const i64 8
    %30 = gep i8, ptr %28, %29
    %31 = load ptr, ptr %13
    %32 = const i64 16
    %33 = gep i8, ptr %31, %32
    br bb8(%6, %30, %33)
bb7(%7: ptr):
    %34 = load ptr, ptr %13
    %35 = const i64 8
    %36 = gep i8, ptr %34, %35
    call @func.168(%36, %7)
    br bb10
bb8(%8: ptr, %9: ptr, %10: ptr):
    call @func.168(%9, %8)
    br bb9(%8, %10)
bb9(%11: ptr, %12: ptr):
    call @func.168(%12, %11)
    br bb10
bb10:
    ret
}

fn @_RNvMs6_NtCs2EYQwhfuABO_4core3numm14saturating_add(functy.170) {
}

fn @Level__get_offset(functy.171) {
bb0(%0: ptr, %1: ptr):
    %9 = alloca i64, align 8
    store ptr %1, ptr %9
    %10 = const u32 0
    br bb1(%10)
bb1(%2: u32):
    %11 = load ptr, ptr %9
    %12 = load i32, ptr %11
    %13 = sext i32 %12 to i64
    switch %13 [ 1: bb2(%2) default: bb5(%2) ]
bb2(%3: u32):
    %14 = load ptr, ptr %9
    %15 = const i64 8
    %16 = gep i8, ptr %14, %15
    %17 = const u32 1
    %18 = call @func.170(%3, %17)
    br bb3(%16, %18)
bb3(%4: ptr, %5: u32):
    %19 = load ptr, ptr %4
    %20 = const i64 16
    %21 = gep i8, ptr %19, %20
    br bb4(%5, %21)
bb4(%6: u32, %7: ptr):
    store ptr %7, ptr %9
    br bb1(%6)
bb5(%8: u32):
    %22 = load ptr, ptr %9
    store ptr %22, ptr %0
    %23 = const i64 8
    %24 = gep i8, ptr %0, %23
    store u32 %8, ptr %24
    ret
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE3newBE_(functy.172) {
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE3lenBG_(functy.173) {
}

fn @_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_(functy.174) {
}

fn @_RNvXs8_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelENtNtNtCs2EYQwhfuABO_4core3ops5deref8DerefMut9deref_mutBH_(functy.175) {
}

fn @_RNvMNtCs2EYQwhfuABO_4core5sliceSNtCshhXhIKvfvMU_25clean_decl_universe_slice5Level4swapBw_(functy.176) {
}

fn @_RNvXs7_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefBH_(functy.177) {
}

fn @_RNvXsd_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelEINtNtNtCs2EYQwhfuABO_4core3ops5index8IndexMutjE9index_mutBH_(functy.178) {
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE8is_emptyBG_(functy.179) {
}

fn @Level__normalize_max(functy.180) {
bb0(%0: ptr, %1: ptr, %2: u32):
    %101 = alloca (i64, i64, i64), align 8
    %102 = alloca (i64, i64, i64), align 8
    %103 = alloca (i64, i64, i64), align 8
    %104 = alloca (i64, i64), align 8
    %105 = alloca (i64, i64), align 8
    %106 = alloca (i64, i64), align 8
    %107 = alloca (i64, i64), align 8
    %108 = alloca (i64, i64), align 8
    %109 = alloca (i64, i64), align 8
    %110 = alloca (i64, i64, i64), align 8
    %111 = alloca (i64, i64), align 8
    %112 = alloca (i64, i64, i64), align 8
    %113 = alloca (i64, i64), align 8
    %114 = alloca (i64, i64, i64), align 8
    %115 = alloca (i64, i64), align 8
    %116 = alloca (i64, i64), align 8
    %117 = const bool false
    call @func.172(%101)
    br bb1(%1, %2)
bb1(%3: ptr, %4: u32):
    call @func.185(%3, %101)
    br bb2(%4)
bb2(%5: u32):
    call @func.172(%102)
    br bb3(%5)
bb3(%6: u32):
    %118 = const u64 0
    br bb4(%6, %118)
bb4(%7: u32, %8: u64):
    %119 = call @func.173(%101)
    br bb5(%7, %8, %8, %119)
bb5(%9: u32, %10: u64, %11: u64, %12: u64):
    %120 = icmp ult u64 %11, %12
    condbr %120, bb6(%9, %10), bb11(%9)
bb6(%13: u32, %14: u64):
    %121 = call @func.174(%101, %14)
    br bb7(%13, %14, %121)
bb7(%15: u32, %16: u64, %17: ptr):
    call @func.157(%103, %17)
    br bb8(%15, %16)
bb8(%18: u32, %19: u64):
    call @func.185(%103, %102)
    br bb9(%18, %19)
bb9(%20: u32, %21: u64):
    %122 = const u64 1
    %123, %124 = add.overflow u64 %21, %122
    store u64 %123, ptr %104
    %125 = const i64 8
    %126 = gep i8, ptr %104, %125
    store bool %124, ptr %126
    %127 = const i64 8
    %128 = gep i8, ptr %104, %127
    %129 = load bool, ptr %128
    %130 = const bool false
    %131 = icmp eq bool %129, %130
    condbr %131, bb10(%20), bb53
bb10(%22: u32):
    %132 = load u64, ptr %104
    br bb4(%22, %132)
bb11(%23: u32):
    %133 = const u64 1
    br bb12(%23, %133)
bb12(%24: u32, %25: u64):
    %134 = call @func.173(%102)
    br bb13(%24, %25, %25, %134)
bb13(%26: u32, %27: u64, %28: u64, %29: u64):
    %135 = icmp ult u64 %28, %29
    condbr %135, bb14(%26, %27), bb28(%26)
bb14(%30: u32, %31: u64):
    br bb15(%30, %31, %31)
bb15(%32: u32, %33: u64, %34: u64):
    %136 = const u64 0
    %137 = icmp ugt u64 %34, %136
    condbr %137, bb16(%32, %33, %34), bb26(%32, %33)
bb16(%35: u32, %36: u64, %37: u64):
    %138 = call @func.174(%102, %37)
    br bb17(%35, %36, %37, %138)
bb17(%38: u32, %39: u64, %40: u64, %41: ptr):
    %139 = const u64 1
    %140, %141 = sub.overflow u64 %40, %139
    store u64 %140, ptr %105
    %142 = const i64 8
    %143 = gep i8, ptr %105, %142
    store bool %141, ptr %143
    %144 = const i64 8
    %145 = gep i8, ptr %105, %144
    %146 = load bool, ptr %145
    %147 = const bool false
    %148 = icmp eq bool %146, %147
    condbr %148, bb18(%38, %39, %40, %41, %102), bb53
bb18(%42: u32, %43: u64, %44: u64, %45: ptr, %46: ptr):
    %149 = load u64, ptr %105
    %150 = call @func.174(%46, %149)
    br bb19(%42, %43, %44, %45, %150)
bb19(%47: u32, %48: u64, %49: u64, %50: ptr, %51: ptr):
    %151 = call @func.190(%50, %51)
    br bb20(%47, %48, %49, %151)
bb20(%52: u32, %53: u64, %54: u64, %55: bool):
    condbr %55, bb21(%52, %53, %54), bb26(%52, %53)
bb21(%56: u32, %57: u64, %58: u64):
    call @func.175(%106, %102)
    br bb22(%56, %57, %58)
bb22(%59: u32, %60: u64, %61: u64):
    %152 = const u64 1
    %153, %154 = sub.overflow u64 %61, %152
    store u64 %153, ptr %107
    %155 = const i64 8
    %156 = gep i8, ptr %107, %155
    store bool %154, ptr %156
    %157 = const i64 8
    %158 = gep i8, ptr %107, %157
    %159 = load bool, ptr %158
    %160 = const bool false
    %161 = icmp eq bool %159, %160
    condbr %161, bb23(%59, %60, %61, %61), bb53
bb23(%62: u32, %63: u64, %64: u64, %65: u64):
    %162 = load u64, ptr %107
    call @func.176(%106, %65, %162)
    br bb24(%62, %63, %64)
bb24(%66: u32, %67: u64, %68: u64):
    %163 = const u64 1
    %164, %165 = sub.overflow u64 %68, %163
    store u64 %164, ptr %108
    %166 = const i64 8
    %167 = gep i8, ptr %108, %166
    store bool %165, ptr %167
    %168 = const i64 8
    %169 = gep i8, ptr %108, %168
    %170 = load bool, ptr %169
    %171 = const bool false
    %172 = icmp eq bool %170, %171
    condbr %172, bb25(%66, %67), bb53
bb25(%69: u32, %70: u64):
    %173 = load u64, ptr %108
    br bb15(%69, %70, %173)
bb26(%71: u32, %72: u64):
    %174 = const u64 1
    %175, %176 = add.overflow u64 %72, %174
    store u64 %175, ptr %109
    %177 = const i64 8
    %178 = gep i8, ptr %109, %177
    store bool %176, ptr %178
    %179 = const i64 8
    %180 = gep i8, ptr %109, %179
    %181 = load bool, ptr %180
    %182 = const bool false
    %183 = icmp eq bool %181, %182
    condbr %183, bb27(%71), bb53
bb27(%73: u32):
    %184 = load u64, ptr %109
    br bb12(%73, %184)
bb28(%74: u32):
    call @func.177(%111, %102)
    br bb29(%74)
bb29(%75: u32):
    call @func.195(%110, %111)
    br bb30(%75)
bb30(%76: u32):
    call @func.177(%113, %110)
    br bb31(%76)
bb31(%77: u32):
    call @func.201(%112, %113)
    br bb32(%77)
bb32(%78: u32):
    %185 = const u32 0
    %186 = icmp ugt u32 %78, %185
    condbr %186, bb33(%78), bb42
bb33(%79: u32):
    %187 = const u64 0
    br bb34(%79, %187)
bb34(%80: u32, %81: u64):
    %188 = call @func.173(%112)
    br bb35(%80, %81, %81, %188)
bb35(%82: u32, %83: u64, %84: u64, %85: u64):
    %189 = icmp ult u64 %84, %85
    condbr %189, bb36(%82, %83), bb42
bb36(%86: u32, %87: u64):
    %190 = call @func.174(%112, %87)
    br bb37(%86, %87, %190)
bb37(%88: u32, %89: u64, %90: ptr):
    call @func.181(%114, %90, %88)
    br bb38(%88, %89)
bb38(%91: u32, %92: u64):
    %191 = const bool true
    %192 = call @func.178(%112, %92)
    br bb39(%91, %92, %192)
bb39(%93: u32, %94: u64, %95: ptr):
    br bb40(%93, %94, %95)
bb40(%96: u32, %97: u64, %98: ptr):
    %193 = const bool false
    %194 = load i64, ptr %114
    store i64 %194, ptr %98
    %195 = const i64 8
    %196 = gep i8, ptr %114, %195
    %197 = const i64 8
    %198 = gep i8, ptr %98, %197
    %199 = load i64, ptr %196
    store i64 %199, ptr %198
    %200 = const i64 16
    %201 = gep i8, ptr %114, %200
    %202 = const i64 16
    %203 = gep i8, ptr %98, %202
    %204 = load i64, ptr %201
    store i64 %204, ptr %203
    %205 = const bool false
    %206 = const u64 1
    %207, %208 = add.overflow u64 %97, %206
    store u64 %207, ptr %115
    %209 = const i64 8
    %210 = gep i8, ptr %115, %209
    store bool %208, ptr %210
    %211 = const i64 8
    %212 = gep i8, ptr %115, %211
    %213 = load bool, ptr %212
    %214 = const bool false
    %215 = icmp eq bool %213, %214
    condbr %215, bb41(%96), bb53
bb41(%99: u32):
    %216 = load u64, ptr %115
    br bb34(%99, %216)
bb42:
    %217 = call @func.179(%112)
    br bb43(%217)
bb43(%100: bool):
    condbr %100, bb44, bb45
bb44:
    %218 = const i32 0
    store i32 %218, ptr %0
    br bb47
bb45:
    call @func.177(%116, %112)
    br bb46
bb46:
    call @func.202(%0, %116)
    br bb52
bb47:
    br bb48
bb48:
    br bb49
bb49:
    br bb50
bb50:
    br bb51
bb51:
    ret
bb52:
    br bb47
bb53:
    unreachable
}

fn @Level__add_offset(functy.181) {
bb0(%0: ptr, %1: ptr, %2: u32):
    %11 = alloca (i64, i64, i64), align 8
    %12 = alloca (i64, i64, i64), align 8
    %13 = alloca (i64, i64, i64), align 8
    %14 = alloca (i32, i32), align 4
    %15 = const bool false
    %16 = const bool true
    call @func.48(%11, %1)
    br bb1(%2)
bb1(%3: u32):
    %17 = const u32 0
    br bb2(%3, %17)
bb2(%4: u32, %5: u32):
    %18 = icmp ult u32 %5, %4
    condbr %18, bb3(%4, %5), bb6
bb3(%6: u32, %7: u32):
    %19 = const bool false
    %20 = load i64, ptr %11
    store i64 %20, ptr %13
    %21 = const i64 8
    %22 = gep i8, ptr %11, %21
    %23 = const i64 8
    %24 = gep i8, ptr %13, %23
    %25 = load i64, ptr %22
    store i64 %25, ptr %24
    %26 = const i64 16
    %27 = gep i8, ptr %11, %26
    %28 = const i64 16
    %29 = gep i8, ptr %13, %28
    %30 = load i64, ptr %27
    store i64 %30, ptr %29
    call @func.61(%12, %13)
    br bb4(%6, %7)
bb4(%8: u32, %9: u32):
    %31 = const bool true
    %32 = load i64, ptr %12
    store i64 %32, ptr %11
    %33 = const i64 8
    %34 = gep i8, ptr %12, %33
    %35 = const i64 8
    %36 = gep i8, ptr %11, %35
    %37 = load i64, ptr %34
    store i64 %37, ptr %36
    %38 = const i64 16
    %39 = gep i8, ptr %12, %38
    %40 = const i64 16
    %41 = gep i8, ptr %11, %40
    %42 = load i64, ptr %39
    store i64 %42, ptr %41
    %43 = const u32 1
    %44, %45 = add.overflow u32 %9, %43
    store u32 %44, ptr %14
    %46 = const i64 4
    %47 = gep i8, ptr %14, %46
    store bool %45, ptr %47
    %48 = const i64 4
    %49 = gep i8, ptr %14, %48
    %50 = load bool, ptr %49
    %51 = const bool false
    %52 = icmp eq bool %50, %51
    condbr %52, bb5(%8), bb7
bb5(%10: u32):
    %53 = load u32, ptr %14
    br bb2(%10, %53)
bb6:
    %54 = const bool false
    %55 = load i64, ptr %11
    store i64 %55, ptr %0
    %56 = const i64 8
    %57 = gep i8, ptr %11, %56
    %58 = const i64 8
    %59 = gep i8, ptr %0, %58
    %60 = load i64, ptr %57
    store i64 %60, ptr %59
    %61 = const i64 16
    %62 = gep i8, ptr %11, %61
    %63 = const i64 16
    %64 = gep i8, ptr %0, %63
    %65 = load i64, ptr %62
    store i64 %65, ptr %64
    %66 = const bool false
    ret
bb7:
    unreachable
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecRNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE3popBH_(functy.182) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecRNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE4pushBI_(functy.183) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE4pushBH_(functy.184) {
}

fn @Level__push_max_args(functy.185) {
bb0(%0: ptr, %1: ptr):
    %27 = alloca (i64, i64, i64), align 8
    %28 = alloca i64, align 8
    %29 = alloca i64, align 8
    %30 = alloca i64, align 8
    %31 = alloca (i64, i64, i64), align 8
    %32 = const i64 8
    %33 = heap_alloc rust_heap i8, %32, align 8
    store ptr %33, ptr %28
    br bb1(%0, %1)
bb1(%2: ptr, %3: ptr):
    %34 = load ptr, ptr %28
    %35 = ptrtoint ptr %34 to u64
    %36 = const u64 8
    %37 = const u64 1
    %38 = sub u64 %36, %37
    %39 = and u64 %35, %38
    %40 = const u64 0
    %41 = icmp eq u64 %39, %40
    condbr %41, bb13(%2, %3, %34), bb18
bb2(%4: ptr):
    call @func.182(%29, %27)
    br bb3(%4)
bb3(%5: ptr):
    %42 = load i64, ptr %29
    %43 = const i64 0
    %44 = icmp eq i64 %42, %43
    %45 = const i64 0
    %46 = const i64 1
    %47 = select i64 %44, %45, %46
    switch %47 [ 1: bb4(%5) 0: bb11 default: bb15 ]
bb4(%6: ptr):
    %48 = load ptr, ptr %29
    store ptr %48, ptr %30
    %49 = load ptr, ptr %30
    %50 = load i32, ptr %49
    %51 = sext i32 %50 to i64
    switch %51 [ 2: bb6(%6) default: bb5(%6) ]
bb5(%7: ptr):
    %52 = load ptr, ptr %30
    call @func.48(%31, %52)
    br bb10(%7)
bb6(%8: ptr):
    %53 = load ptr, ptr %30
    %54 = const i64 8
    %55 = gep i8, ptr %53, %54
    %56 = load ptr, ptr %30
    %57 = const i64 16
    %58 = gep i8, ptr %56, %57
    %59 = load ptr, ptr %58
    %60 = const i64 16
    %61 = gep i8, ptr %59, %60
    br bb7(%8, %55, %27, %61)
bb7(%9: ptr, %10: ptr, %11: ptr, %12: ptr):
    call @func.183(%11, %12)
    br bb8(%9, %10)
bb8(%13: ptr, %14: ptr):
    %62 = load ptr, ptr %14
    %63 = const i64 16
    %64 = gep i8, ptr %62, %63
    br bb9(%13, %27, %64)
bb9(%15: ptr, %16: ptr, %17: ptr):
    call @func.183(%16, %17)
    br bb16(%15)
bb10(%18: ptr):
    call @func.184(%18, %31)
    br bb17(%18)
bb11:
    br bb12
bb12:
    ret
bb13(%19: ptr, %20: ptr, %21: ptr):
    %65 = ptrtoint ptr %21 to u64
    %66 = const u64 8
    %67 = const u64 0
    %68 = icmp ne u64 %66, %67
    %69 = const u64 0
    %70 = icmp eq u64 %65, %69
    %71 = const bool false
    %72 = select bool %70, %68, %71
    %73 = const bool false
    %74 = icmp eq bool %72, %73
    condbr %74, bb14(%19, %20, %21), bb18
bb14(%22: ptr, %23: ptr, %24: ptr):
    store ptr %22, ptr %24
    %75 = load ptr, ptr %28
    %76 = const i64 8
    %77 = gep i8, ptr %27, %76
    store ptr %75, ptr %77
    %78 = const i64 1
    store i64 %78, ptr %27
    %79 = const i64 1
    %80 = const i64 16
    %81 = gep i8, ptr %27, %80
    store i64 %79, ptr %81
    br bb2(%23)
bb15:
    unreachable
bb16(%25: ptr):
    br bb2(%25)
bb17(%26: ptr):
    br bb2(%26)
bb18:
    unreachable
}

fn @_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelNtB7_9PartialEq2eqBF_(functy.186) {
}

fn @_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelNtB7_9PartialEq2neBF_(functy.187) {
}

fn @_RNvXs8_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCshhXhIKvfvMU_25clean_decl_universe_slice4NameNtB7_10PartialOrd2ltBF_(functy.188) {
}

fn @_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRINtNtCskTzINo8ZBH9_5alloc4sync3ArcNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelENtB7_9PartialEq2neB1d_(functy.189) {
}

fn @Level__is_norm_lt(functy.190) {
bb0(%0: ptr, %1: ptr):
    %28 = alloca i64, align 8
    %29 = alloca i64, align 8
    %30 = alloca i64, align 8
    %31 = alloca (i64, i64), align 8
    %32 = alloca i64, align 8
    %33 = alloca (i64, i64), align 8
    %34 = alloca (i64, i64), align 8
    %35 = alloca i64, align 8
    %36 = alloca i64, align 8
    %37 = alloca i64, align 8
    %38 = alloca i64, align 8
    %39 = alloca i64, align 8
    %40 = alloca i64, align 8
    %41 = alloca i64, align 8
    %42 = alloca i64, align 8
    %43 = alloca i64, align 8
    %44 = alloca i64, align 8
    %45 = alloca i64, align 8
    %46 = alloca i64, align 8
    %47 = alloca i64, align 8
    %48 = alloca i64, align 8
    store ptr %0, ptr %28
    store ptr %1, ptr %29
    br bb1
bb1:
    %49 = call @func.186(%28, %29)
    br bb2(%49)
bb2(%2: bool):
    condbr %2, bb3, bb4
bb3:
    %50 = const bool false
    br bb31(%50)
bb4:
    %51 = load ptr, ptr %28
    call @func.171(%31, %51)
    br bb5
bb5:
    %52 = load ptr, ptr %31
    store ptr %52, ptr %30
    %53 = const i64 8
    %54 = gep i8, ptr %31, %53
    %55 = load u32, ptr %54
    %56 = load ptr, ptr %29
    call @func.171(%33, %56)
    br bb6(%55)
bb6(%3: u32):
    %57 = load ptr, ptr %33
    store ptr %57, ptr %32
    %58 = const i64 8
    %59 = gep i8, ptr %33, %58
    %60 = load u32, ptr %59
    %61 = call @func.187(%30, %32)
    br bb7(%3, %60, %61)
bb7(%4: u32, %5: u32, %6: bool):
    condbr %6, bb8, bb30(%4, %5)
bb8:
    %62 = load ptr, ptr %30
    %63 = call @func.203(%62)
    br bb9(%63)
bb9(%7: u8):
    %64 = load ptr, ptr %32
    %65 = call @func.203(%64)
    br bb10(%7, %65)
bb10(%8: u8, %9: u8):
    %66 = icmp ne u8 %8, %9
    condbr %66, bb11, bb14
bb11:
    %67 = load ptr, ptr %30
    %68 = call @func.203(%67)
    br bb12(%68)
bb12(%10: u8):
    %69 = load ptr, ptr %32
    %70 = call @func.203(%69)
    br bb13(%10, %70)
bb13(%11: u8, %12: u8):
    %71 = icmp ult u8 %11, %12
    br bb31(%71)
bb14:
    %72 = load ptr, ptr %30
    store ptr %72, ptr %34
    %73 = load ptr, ptr %32
    %74 = const i64 8
    %75 = gep i8, ptr %34, %74
    store ptr %73, ptr %75
    %76 = load ptr, ptr %34
    %77 = load i32, ptr %76
    %78 = sext i32 %77 to i64
    switch %78 [ 2: bb17 3: bb18 4: bb16 default: bb15 ]
bb15:
    %79 = const bool false
    br bb31(%79)
bb16:
    %80 = const i64 8
    %81 = gep i8, ptr %34, %80
    %82 = load ptr, ptr %81
    %83 = load i32, ptr %82
    %84 = sext i32 %83 to i64
    switch %84 [ 4: bb21 default: bb15 ]
bb17:
    %85 = const i64 8
    %86 = gep i8, ptr %34, %85
    %87 = load ptr, ptr %86
    %88 = load i32, ptr %87
    %89 = sext i32 %88 to i64
    switch %89 [ 2: bb20 default: bb15 ]
bb18:
    %90 = const i64 8
    %91 = gep i8, ptr %34, %90
    %92 = load ptr, ptr %91
    %93 = load i32, ptr %92
    %94 = sext i32 %93 to i64
    switch %94 [ 3: bb19 default: bb15 ]
bb19:
    %95 = load ptr, ptr %34
    store ptr %95, ptr %39
    %96 = load ptr, ptr %39
    %97 = const i64 8
    %98 = gep i8, ptr %96, %97
    store ptr %98, ptr %37
    %99 = load ptr, ptr %34
    store ptr %99, ptr %40
    %100 = load ptr, ptr %40
    %101 = const i64 16
    %102 = gep i8, ptr %100, %101
    %103 = const i64 8
    %104 = gep i8, ptr %34, %103
    %105 = load ptr, ptr %104
    store ptr %105, ptr %41
    %106 = load ptr, ptr %41
    %107 = const i64 8
    %108 = gep i8, ptr %106, %107
    store ptr %108, ptr %38
    %109 = const i64 8
    %110 = gep i8, ptr %34, %109
    %111 = load ptr, ptr %110
    store ptr %111, ptr %42
    %112 = load ptr, ptr %42
    %113 = const i64 16
    %114 = gep i8, ptr %112, %113
    br bb22(%102, %114)
bb20:
    %115 = load ptr, ptr %34
    store ptr %115, ptr %43
    %116 = load ptr, ptr %43
    %117 = const i64 8
    %118 = gep i8, ptr %116, %117
    store ptr %118, ptr %37
    %119 = load ptr, ptr %34
    store ptr %119, ptr %44
    %120 = load ptr, ptr %44
    %121 = const i64 16
    %122 = gep i8, ptr %120, %121
    %123 = const i64 8
    %124 = gep i8, ptr %34, %123
    %125 = load ptr, ptr %124
    store ptr %125, ptr %45
    %126 = load ptr, ptr %45
    %127 = const i64 8
    %128 = gep i8, ptr %126, %127
    store ptr %128, ptr %38
    %129 = const i64 8
    %130 = gep i8, ptr %34, %129
    %131 = load ptr, ptr %130
    store ptr %131, ptr %46
    %132 = load ptr, ptr %46
    %133 = const i64 16
    %134 = gep i8, ptr %132, %133
    br bb22(%122, %134)
bb21:
    %135 = load ptr, ptr %34
    store ptr %135, ptr %47
    %136 = load ptr, ptr %47
    %137 = const i64 4
    %138 = gep i8, ptr %136, %137
    store ptr %138, ptr %35
    %139 = const i64 8
    %140 = gep i8, ptr %34, %139
    %141 = load ptr, ptr %140
    store ptr %141, ptr %48
    %142 = load ptr, ptr %48
    %143 = const i64 4
    %144 = gep i8, ptr %142, %143
    store ptr %144, ptr %36
    %145 = call @func.188(%35, %36)
    br bb31(%145)
bb22(%13: ptr, %14: ptr):
    %146 = call @func.189(%37, %38)
    br bb23(%13, %14, %146)
bb23(%15: ptr, %16: ptr, %17: bool):
    condbr %17, bb24, bb27(%15, %16)
bb24:
    %147 = load ptr, ptr %37
    %148 = load ptr, ptr %147
    %149 = const i64 16
    %150 = gep i8, ptr %148, %149
    br bb25(%150)
bb25(%18: ptr):
    store ptr %18, ptr %28
    %151 = load ptr, ptr %38
    %152 = load ptr, ptr %151
    %153 = const i64 16
    %154 = gep i8, ptr %152, %153
    br bb26(%154)
bb26(%19: ptr):
    store ptr %19, ptr %29
    br bb1
bb27(%20: ptr, %21: ptr):
    %155 = load ptr, ptr %20
    %156 = const i64 16
    %157 = gep i8, ptr %155, %156
    br bb28(%21, %157)
bb28(%22: ptr, %23: ptr):
    store ptr %23, ptr %28
    %158 = load ptr, ptr %22
    %159 = const i64 16
    %160 = gep i8, ptr %158, %159
    br bb29(%160)
bb29(%24: ptr):
    store ptr %24, ptr %29
    br bb1
bb30(%25: u32, %26: u32):
    %161 = icmp ult u32 %25, %26
    br bb31(%161)
bb31(%27: bool):
    ret %27
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE3newBE_(functy.191) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE4pushBH_(functy.192) {
}

fn @_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelNtB7_9PartialEq2eqBF_(functy.193) {
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE3popBG_(functy.194) {
}

fn @Level__dedup_max_args(functy.195) {
bb0(%0: ptr, %1: ptr):
    %78 = alloca (i64, i64, i64), align 8
    %79 = alloca (i64, i64), align 8
    %80 = alloca (i64, i64), align 8
    %81 = alloca (i64, i64), align 8
    %82 = alloca (i64, i64), align 8
    %83 = alloca (i64, i64), align 8
    %84 = alloca (i64, i64), align 8
    %85 = alloca (i64, i64), align 8
    %86 = alloca (i64, i64), align 8
    %87 = alloca (i64, i64, i64), align 8
    %88 = alloca (i64, i64), align 8
    %89 = alloca (i64, i64), align 8
    %90 = alloca (i64, i64), align 8
    %91 = alloca (i64, i64, i64), align 8
    %92 = alloca (i64, i64, i64), align 8
    %93 = alloca (i64, i64, i64), align 8
    %94 = alloca (i64, i64), align 8
    call @func.191(%78)
    br bb1
bb1:
    %95 = const u64 0
    %96 = const i64 8
    %97 = gep i8, ptr %1, %96
    %98 = load u64, ptr %97
    %99 = icmp ult u64 %95, %98
    condbr %99, bb2(%95, %95), bb52
bb2(%2: u64, %3: u64):
    %100 = load ptr, ptr %1
    %101 = const u64 24
    %102 = mul u64 %3, %101
    %103 = gep i8, ptr %100, %102
    %104 = call @func.204(%103)
    br bb3(%2, %104)
bb3(%4: u64, %5: bool):
    condbr %5, bb4(%4), bb25(%4)
bb4(%6: u64):
    %105 = const u64 1
    %106, %107 = add.overflow u64 %6, %105
    store u64 %106, ptr %79
    %108 = const i64 8
    %109 = gep i8, ptr %79, %108
    store bool %107, ptr %109
    %110 = const i64 8
    %111 = gep i8, ptr %79, %110
    %112 = load bool, ptr %111
    %113 = const bool false
    %114 = icmp eq bool %112, %113
    condbr %114, bb5(%6), bb52
bb5(%7: u64):
    %115 = load u64, ptr %79
    %116 = const i64 8
    %117 = gep i8, ptr %1, %116
    %118 = load u64, ptr %117
    %119 = icmp ult u64 %115, %118
    condbr %119, bb6(%7), bb12(%7)
bb6(%8: u64):
    %120 = const u64 1
    %121, %122 = add.overflow u64 %8, %120
    store u64 %121, ptr %80
    %123 = const i64 8
    %124 = gep i8, ptr %80, %123
    store bool %122, ptr %124
    %125 = const i64 8
    %126 = gep i8, ptr %80, %125
    %127 = load bool, ptr %126
    %128 = const bool false
    %129 = icmp eq bool %127, %128
    condbr %129, bb7(%8), bb52
bb7(%9: u64):
    %130 = load u64, ptr %80
    %131 = const i64 8
    %132 = gep i8, ptr %1, %131
    %133 = load u64, ptr %132
    %134 = icmp ult u64 %130, %133
    condbr %134, bb8(%9, %130), bb52
bb8(%10: u64, %11: u64):
    %135 = load ptr, ptr %1
    %136 = const u64 24
    %137 = mul u64 %11, %136
    %138 = gep i8, ptr %135, %137
    %139 = call @func.204(%138)
    br bb9(%10, %139)
bb9(%12: u64, %13: bool):
    condbr %13, bb10(%12), bb12(%12)
bb10(%14: u64):
    %140 = const u64 1
    %141, %142 = add.overflow u64 %14, %140
    store u64 %141, ptr %81
    %143 = const i64 8
    %144 = gep i8, ptr %81, %143
    store bool %142, ptr %144
    %145 = const i64 8
    %146 = gep i8, ptr %81, %145
    %147 = load bool, ptr %146
    %148 = const bool false
    %149 = icmp eq bool %147, %148
    condbr %149, bb11, bb52
bb11:
    %150 = load u64, ptr %81
    br bb4(%150)
bb12(%15: u64):
    %151 = const i64 8
    %152 = gep i8, ptr %1, %151
    %153 = load u64, ptr %152
    %154 = icmp ult u64 %15, %153
    condbr %154, bb13(%15, %15), bb52
bb13(%16: u64, %17: u64):
    %155 = load ptr, ptr %1
    %156 = const u64 24
    %157 = mul u64 %17, %156
    %158 = gep i8, ptr %155, %157
    call @func.171(%82, %158)
    br bb14(%16)
bb14(%18: u64):
    %159 = const i64 8
    %160 = gep i8, ptr %82, %159
    %161 = load u32, ptr %160
    %162 = const u64 1
    %163, %164 = add.overflow u64 %18, %162
    store u64 %163, ptr %83
    %165 = const i64 8
    %166 = gep i8, ptr %83, %165
    store bool %164, ptr %166
    %167 = const i64 8
    %168 = gep i8, ptr %83, %167
    %169 = load bool, ptr %168
    %170 = const bool false
    %171 = icmp eq bool %169, %170
    condbr %171, bb15(%18, %161), bb52
bb15(%19: u64, %20: u32):
    %172 = load u64, ptr %83
    br bb16(%19, %20, %172)
bb16(%21: u64, %22: u32, %23: u64):
    %173 = const i64 8
    %174 = gep i8, ptr %1, %173
    %175 = load u64, ptr %174
    %176 = icmp ult u64 %23, %175
    condbr %176, bb17(%21, %22, %23), bb22(%21, %23)
bb17(%24: u64, %25: u32, %26: u64):
    %177 = const i64 8
    %178 = gep i8, ptr %1, %177
    %179 = load u64, ptr %178
    %180 = icmp ult u64 %26, %179
    condbr %180, bb18(%24, %25, %26, %26), bb52
bb18(%27: u64, %28: u32, %29: u64, %30: u64):
    %181 = load ptr, ptr %1
    %182 = const u64 24
    %183 = mul u64 %30, %182
    %184 = gep i8, ptr %181, %183
    call @func.171(%84, %184)
    br bb19(%27, %28, %29)
bb19(%31: u64, %32: u32, %33: u64):
    %185 = const i64 8
    %186 = gep i8, ptr %84, %185
    %187 = load u32, ptr %186
    %188 = icmp uge u32 %187, %32
    condbr %188, bb22(%31, %33), bb20(%31, %32, %33)
bb20(%34: u64, %35: u32, %36: u64):
    %189 = const u64 1
    %190, %191 = add.overflow u64 %36, %189
    store u64 %190, ptr %85
    %192 = const i64 8
    %193 = gep i8, ptr %85, %192
    store bool %191, ptr %193
    %194 = const i64 8
    %195 = gep i8, ptr %85, %194
    %196 = load bool, ptr %195
    %197 = const bool false
    %198 = icmp eq bool %196, %197
    condbr %198, bb21(%34, %35), bb52
bb21(%37: u64, %38: u32):
    %199 = load u64, ptr %85
    br bb16(%37, %38, %199)
bb22(%39: u64, %40: u64):
    %200 = const i64 8
    %201 = gep i8, ptr %1, %200
    %202 = load u64, ptr %201
    %203 = icmp ult u64 %40, %202
    condbr %203, bb23(%39), bb25(%39)
bb23(%41: u64):
    %204 = const u64 1
    %205, %206 = add.overflow u64 %41, %204
    store u64 %205, ptr %86
    %207 = const i64 8
    %208 = gep i8, ptr %86, %207
    store bool %206, ptr %208
    %209 = const i64 8
    %210 = gep i8, ptr %86, %209
    %211 = load bool, ptr %210
    %212 = const bool false
    %213 = icmp eq bool %211, %212
    condbr %213, bb24, bb52
bb24:
    %214 = load u64, ptr %86
    br bb25(%214)
bb25(%42: u64):
    %215 = const i64 8
    %216 = gep i8, ptr %1, %215
    %217 = load u64, ptr %216
    %218 = icmp ult u64 %42, %217
    condbr %218, bb26(%42), bb49
bb26(%43: u64):
    %219 = const i64 8
    %220 = gep i8, ptr %1, %219
    %221 = load u64, ptr %220
    %222 = icmp ult u64 %43, %221
    condbr %222, bb27(%43, %78, %43), bb52
bb27(%44: u64, %45: ptr, %46: u64):
    %223 = load ptr, ptr %1
    %224 = const u64 24
    %225 = mul u64 %46, %224
    %226 = gep i8, ptr %223, %225
    call @func.48(%87, %226)
    br bb28(%44, %45)
bb28(%47: u64, %48: ptr):
    call @func.192(%48, %87)
    br bb29(%47)
bb29(%49: u64):
    %227 = const i64 8
    %228 = gep i8, ptr %1, %227
    %229 = load u64, ptr %228
    %230 = icmp ult u64 %49, %229
    condbr %230, bb30(%49, %49), bb52
bb30(%50: u64, %51: u64):
    %231 = load ptr, ptr %1
    %232 = const u64 24
    %233 = mul u64 %51, %232
    %234 = gep i8, ptr %231, %233
    call @func.171(%88, %234)
    br bb31(%50)
bb31(%52: u64):
    %235 = const u64 1
    %236, %237 = add.overflow u64 %52, %235
    store u64 %236, ptr %89
    %238 = const i64 8
    %239 = gep i8, ptr %89, %238
    store bool %237, ptr %239
    %240 = const i64 8
    %241 = gep i8, ptr %89, %240
    %242 = load bool, ptr %241
    %243 = const bool false
    %244 = icmp eq bool %242, %243
    condbr %244, bb32, bb52
bb32:
    %245 = load u64, ptr %89
    br bb33(%245)
bb33(%53: u64):
    %246 = const i64 8
    %247 = gep i8, ptr %1, %246
    %248 = load u64, ptr %247
    %249 = icmp ult u64 %53, %248
    condbr %249, bb34(%53), bb49
bb34(%54: u64):
    %250 = const i64 8
    %251 = gep i8, ptr %1, %250
    %252 = load u64, ptr %251
    %253 = icmp ult u64 %54, %252
    condbr %253, bb35(%54, %54), bb52
bb35(%55: u64, %56: u64):
    %254 = load ptr, ptr %1
    %255 = const u64 24
    %256 = mul u64 %56, %255
    %257 = gep i8, ptr %254, %256
    call @func.171(%90, %257)
    br bb36(%55)
bb36(%57: u64):
    %258 = call @func.193(%88, %90)
    br bb37(%57, %258)
bb37(%58: u64, %59: bool):
    condbr %59, bb38(%58), bb44(%58)
bb38(%60: u64):
    %259 = const i64 8
    %260 = gep i8, ptr %88, %259
    %261 = load u32, ptr %260
    %262 = const i64 8
    %263 = gep i8, ptr %90, %262
    %264 = load u32, ptr %263
    %265 = icmp ult u32 %261, %264
    condbr %265, bb39(%60), bb47(%60)
bb39(%61: u64):
    %266 = load i64, ptr %90
    store i64 %266, ptr %88
    %267 = const i64 8
    %268 = gep i8, ptr %90, %267
    %269 = const i64 8
    %270 = gep i8, ptr %88, %269
    %271 = load i64, ptr %268
    store i64 %271, ptr %270
    call @func.194(%91, %78)
    br bb40(%61)
bb40(%62: u64):
    br bb41(%62)
bb41(%63: u64):
    %272 = const i64 8
    %273 = gep i8, ptr %1, %272
    %274 = load u64, ptr %273
    %275 = icmp ult u64 %63, %274
    condbr %275, bb42(%63, %78, %63), bb52
bb42(%64: u64, %65: ptr, %66: u64):
    %276 = load ptr, ptr %1
    %277 = const u64 24
    %278 = mul u64 %66, %277
    %279 = gep i8, ptr %276, %278
    call @func.48(%92, %279)
    br bb43(%64, %65)
bb43(%67: u64, %68: ptr):
    call @func.192(%68, %92)
    br bb50(%67)
bb44(%69: u64):
    %280 = load i64, ptr %90
    store i64 %280, ptr %88
    %281 = const i64 8
    %282 = gep i8, ptr %90, %281
    %283 = const i64 8
    %284 = gep i8, ptr %88, %283
    %285 = load i64, ptr %282
    store i64 %285, ptr %284
    %286 = const i64 8
    %287 = gep i8, ptr %1, %286
    %288 = load u64, ptr %287
    %289 = icmp ult u64 %69, %288
    condbr %289, bb45(%69, %78, %69), bb52
bb45(%70: u64, %71: ptr, %72: u64):
    %290 = load ptr, ptr %1
    %291 = const u64 24
    %292 = mul u64 %72, %291
    %293 = gep i8, ptr %290, %292
    call @func.48(%93, %293)
    br bb46(%70, %71)
bb46(%73: u64, %74: ptr):
    call @func.192(%74, %93)
    br bb51(%73)
bb47(%75: u64):
    %294 = const u64 1
    %295, %296 = add.overflow u64 %75, %294
    store u64 %295, ptr %94
    %297 = const i64 8
    %298 = gep i8, ptr %94, %297
    store bool %296, ptr %298
    %299 = const i64 8
    %300 = gep i8, ptr %94, %299
    %301 = load bool, ptr %300
    %302 = const bool false
    %303 = icmp eq bool %301, %302
    condbr %303, bb48, bb52
bb48:
    %304 = load u64, ptr %94
    br bb33(%304)
bb49:
    %305 = load i64, ptr %78
    store i64 %305, ptr %0
    %306 = const i64 8
    %307 = gep i8, ptr %78, %306
    %308 = const i64 8
    %309 = gep i8, ptr %0, %308
    %310 = load i64, ptr %307
    store i64 %310, ptr %309
    %311 = const i64 16
    %312 = gep i8, ptr %78, %311
    %313 = const i64 16
    %314 = gep i8, ptr %0, %313
    %315 = load i64, ptr %312
    store i64 %315, ptr %314
    ret
bb50(%76: u64):
    br bb47(%76)
bb51(%77: u64):
    br bb47(%77)
bb52:
    unreachable
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc5sliceSNtCshhXhIKvfvMU_25clean_decl_universe_slice5Level6to_vecBx_(functy.196) {
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE3newBE_(functy.197) {
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE3lenBG_(functy.198) {
}

fn @_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_(functy.199) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE4pushBH_(functy.200) {
}

fn @Level__subsume_max_args(functy.201) {
bb0(%0: ptr, %1: ptr):
    %219 = alloca (i64, i64), align 8
    %220 = alloca (i64, i64), align 8
    %221 = alloca (i64, i64, i64), align 8
    %222 = alloca (i64, i64), align 8
    %223 = alloca (i64, i64), align 8
    %224 = alloca (i64, i64), align 8
    %225 = alloca (i64, i64), align 8
    %226 = alloca (i64, i64), align 8
    %227 = alloca (i64, i64), align 8
    %228 = alloca (i64, i64), align 8
    %229 = alloca (i64, i64), align 8
    %230 = alloca (i64, i64, i64), align 8
    %231 = alloca (i64, i64), align 8
    %232 = const i64 8
    %233 = gep i8, ptr %1, %232
    %234 = load u64, ptr %233
    %235 = const u64 1
    %236 = icmp ule u64 %234, %235
    condbr %236, bb1, bb2
bb1:
    call @func.196(%0, %1)
    br bb66
bb2:
    %237 = const bool false
    %238 = const u64 0
    br bb3(%237, %238)
bb3(%2: bool, %3: u64):
    %239 = const i64 8
    %240 = gep i8, ptr %1, %239
    %241 = load u64, ptr %240
    %242 = icmp ult u64 %3, %241
    condbr %242, bb4(%2, %3), bb13(%2)
bb4(%4: bool, %5: u64):
    %243 = const i64 8
    %244 = gep i8, ptr %1, %243
    %245 = load u64, ptr %244
    %246 = icmp ult u64 %5, %245
    condbr %246, bb5(%4, %5, %5), bb67
bb5(%6: bool, %7: u64, %8: u64):
    %247 = load ptr, ptr %1
    %248 = const u64 24
    %249 = mul u64 %8, %248
    %250 = gep i8, ptr %247, %249
    call @func.171(%219, %250)
    br bb6(%6, %7)
bb6(%9: bool, %10: u64):
    %251 = load ptr, ptr %219
    %252 = load i32, ptr %251
    %253 = sext i32 %252 to i64
    switch %253 [ 2: bb8(%9, %10) 3: bb8(%9, %10) default: bb7(%9, %10) ]
bb7(%11: bool, %12: u64):
    %254 = const bool false
    br bb9(%11, %12, %254)
bb8(%13: bool, %14: u64):
    %255 = const bool true
    br bb9(%13, %14, %255)
bb9(%15: bool, %16: u64, %17: bool):
    condbr %17, bb10, bb11(%15, %16)
bb10:
    %256 = const bool true
    br bb13(%256)
bb11(%18: bool, %19: u64):
    %257 = const u64 1
    %258, %259 = add.overflow u64 %19, %257
    store u64 %258, ptr %220
    %260 = const i64 8
    %261 = gep i8, ptr %220, %260
    store bool %259, ptr %261
    %262 = const i64 8
    %263 = gep i8, ptr %220, %262
    %264 = load bool, ptr %263
    %265 = const bool false
    %266 = icmp eq bool %264, %265
    condbr %266, bb12(%18), bb67
bb12(%20: bool):
    %267 = load u64, ptr %220
    br bb3(%20, %267)
bb13(%21: bool):
    condbr %21, bb15, bb14
bb14:
    call @func.196(%0, %1)
    br bb66
bb15:
    call @func.197(%221)
    br bb16
bb16:
    %268 = const u64 0
    br bb17(%268)
bb17(%22: u64):
    %269 = const i64 8
    %270 = gep i8, ptr %1, %269
    %271 = load u64, ptr %270
    %272 = icmp ult u64 %22, %271
    condbr %272, bb18(%22), bb65
bb18(%23: u64):
    %273 = const i64 8
    %274 = gep i8, ptr %1, %273
    %275 = load u64, ptr %274
    %276 = icmp ult u64 %23, %275
    condbr %276, bb19(%23, %23), bb67
bb19(%24: u64, %25: u64):
    %277 = load ptr, ptr %1
    %278 = const u64 24
    %279 = mul u64 %25, %278
    %280 = gep i8, ptr %277, %279
    call @func.171(%222, %280)
    br bb20(%24, %280)
bb20(%26: u64, %27: ptr):
    %281 = load ptr, ptr %222
    %282 = load i32, ptr %281
    %283 = sext i32 %282 to i64
    switch %283 [ 2: bb22(%26, %27) 3: bb22(%26, %27) default: bb21(%26, %27) ]
bb21(%28: u64, %29: ptr):
    %284 = const bool false
    br bb23(%28, %29, %284)
bb22(%30: u64, %31: ptr):
    %285 = const bool true
    br bb23(%30, %31, %285)
bb23(%32: u64, %33: ptr, %34: bool):
    %286 = const bool false
    %287 = const u64 0
    br bb24(%32, %33, %34, %286, %287)
bb24(%35: u64, %36: ptr, %37: bool, %38: bool, %39: u64):
    %288 = call @func.198(%221)
    br bb25(%35, %36, %37, %38, %39, %39, %288)
bb25(%40: u64, %41: ptr, %42: bool, %43: bool, %44: u64, %45: u64, %46: u64):
    %289 = icmp ult u64 %45, %46
    condbr %289, bb26(%40, %41, %42, %43, %44), bb38(%40, %41, %42, %43)
bb26(%47: u64, %48: ptr, %49: bool, %50: bool, %51: u64):
    %290 = call @func.199(%221, %51)
    br bb27(%47, %48, %49, %50, %51, %290)
bb27(%52: u64, %53: ptr, %54: bool, %55: bool, %56: u64, %57: ptr):
    call @func.171(%223, %57)
    br bb28(%52, %53, %54, %55, %56, %57)
bb28(%58: u64, %59: ptr, %60: bool, %61: bool, %62: u64, %63: ptr):
    %291 = load ptr, ptr %223
    %292 = load i32, ptr %291
    %293 = sext i32 %292 to i64
    switch %293 [ 2: bb30(%58, %59, %60, %61, %62, %63) 3: bb30(%58, %59, %60, %61, %62, %63) default: bb29(%58, %59, %60, %61, %62, %63) ]
bb29(%64: u64, %65: ptr, %66: bool, %67: bool, %68: u64, %69: ptr):
    %294 = const bool false
    br bb31(%64, %65, %66, %67, %68, %69, %294)
bb30(%70: u64, %71: ptr, %72: bool, %73: bool, %74: u64, %75: ptr):
    %295 = const bool true
    br bb31(%70, %71, %72, %73, %74, %75, %295)
bb31(%76: u64, %77: ptr, %78: bool, %79: bool, %80: u64, %81: ptr, %82: bool):
    condbr %78, bb33(%76, %77, %78, %79, %80, %81), bb32(%76, %77, %78, %79, %80, %81, %82)
bb32(%83: u64, %84: ptr, %85: bool, %86: bool, %87: u64, %88: ptr, %89: bool):
    condbr %89, bb33(%83, %84, %85, %86, %87, %88), bb36(%83, %84, %85, %86, %87)
bb33(%90: u64, %91: ptr, %92: bool, %93: bool, %94: u64, %95: ptr):
    %296 = call @func.208(%95, %91)
    br bb34(%90, %91, %92, %93, %94, %296)
bb34(%96: u64, %97: ptr, %98: bool, %99: bool, %100: u64, %101: bool):
    condbr %101, bb35(%96, %97, %98), bb36(%96, %97, %98, %99, %100)
bb35(%102: u64, %103: ptr, %104: bool):
    %297 = const bool true
    br bb38(%102, %103, %104, %297)
bb36(%105: u64, %106: ptr, %107: bool, %108: bool, %109: u64):
    %298 = const u64 1
    %299, %300 = add.overflow u64 %109, %298
    store u64 %299, ptr %224
    %301 = const i64 8
    %302 = gep i8, ptr %224, %301
    store bool %300, ptr %302
    %303 = const i64 8
    %304 = gep i8, ptr %224, %303
    %305 = load bool, ptr %304
    %306 = const bool false
    %307 = icmp eq bool %305, %306
    condbr %307, bb37(%105, %106, %107, %108), bb67
bb37(%110: u64, %111: ptr, %112: bool, %113: bool):
    %308 = load u64, ptr %224
    br bb24(%110, %111, %112, %113, %308)
bb38(%114: u64, %115: ptr, %116: bool, %117: bool):
    condbr %117, bb39(%114), bb41(%114, %115, %116)
bb39(%118: u64):
    %309 = const u64 1
    %310, %311 = add.overflow u64 %118, %309
    store u64 %310, ptr %225
    %312 = const i64 8
    %313 = gep i8, ptr %225, %312
    store bool %311, ptr %313
    %314 = const i64 8
    %315 = gep i8, ptr %225, %314
    %316 = load bool, ptr %315
    %317 = const bool false
    %318 = icmp eq bool %316, %317
    condbr %318, bb40, bb67
bb40:
    %319 = load u64, ptr %225
    br bb17(%319)
bb41(%119: u64, %120: ptr, %121: bool):
    %320 = const bool false
    %321 = const u64 1
    %322, %323 = add.overflow u64 %119, %321
    store u64 %322, ptr %226
    %324 = const i64 8
    %325 = gep i8, ptr %226, %324
    store bool %323, ptr %325
    %326 = const i64 8
    %327 = gep i8, ptr %226, %326
    %328 = load bool, ptr %327
    %329 = const bool false
    %330 = icmp eq bool %328, %329
    condbr %330, bb42(%119, %120, %121, %320), bb67
bb42(%122: u64, %123: ptr, %124: bool, %125: bool):
    %331 = load u64, ptr %226
    br bb43(%122, %123, %124, %125, %331)
bb43(%126: u64, %127: ptr, %128: bool, %129: bool, %130: u64):
    %332 = const i64 8
    %333 = gep i8, ptr %1, %332
    %334 = load u64, ptr %333
    %335 = icmp ult u64 %130, %334
    condbr %335, bb44(%126, %127, %128, %129, %130), bb58(%126, %127, %129)
bb44(%131: u64, %132: ptr, %133: bool, %134: bool, %135: u64):
    %336 = const i64 8
    %337 = gep i8, ptr %1, %336
    %338 = load u64, ptr %337
    %339 = icmp ult u64 %135, %338
    condbr %339, bb45(%131, %132, %133, %134, %135, %135), bb67
bb45(%136: u64, %137: ptr, %138: bool, %139: bool, %140: u64, %141: u64):
    %340 = load ptr, ptr %1
    %341 = const u64 24
    %342 = mul u64 %141, %341
    %343 = gep i8, ptr %340, %342
    call @func.171(%227, %343)
    br bb46(%136, %137, %138, %139, %140, %343)
bb46(%142: u64, %143: ptr, %144: bool, %145: bool, %146: u64, %147: ptr):
    %344 = load ptr, ptr %227
    %345 = load i32, ptr %344
    %346 = sext i32 %345 to i64
    switch %346 [ 2: bb48(%142, %143, %144, %145, %146, %147) 3: bb48(%142, %143, %144, %145, %146, %147) default: bb47(%142, %143, %144, %145, %146, %147) ]
bb47(%148: u64, %149: ptr, %150: bool, %151: bool, %152: u64, %153: ptr):
    %347 = const bool false
    br bb49(%148, %149, %150, %151, %152, %153, %347)
bb48(%154: u64, %155: ptr, %156: bool, %157: bool, %158: u64, %159: ptr):
    %348 = const bool true
    br bb49(%154, %155, %156, %157, %158, %159, %348)
bb49(%160: u64, %161: ptr, %162: bool, %163: bool, %164: u64, %165: ptr, %166: bool):
    condbr %162, bb51(%160, %161, %162, %163, %164, %165), bb50(%160, %161, %162, %163, %164, %165, %166)
bb50(%167: u64, %168: ptr, %169: bool, %170: bool, %171: u64, %172: ptr, %173: bool):
    condbr %173, bb51(%167, %168, %169, %170, %171, %172), bb56(%167, %168, %169, %170, %171)
bb51(%174: u64, %175: ptr, %176: bool, %177: bool, %178: u64, %179: ptr):
    %349 = call @func.208(%179, %175)
    br bb52(%174, %175, %176, %177, %178, %179, %349)
bb52(%180: u64, %181: ptr, %182: bool, %183: bool, %184: u64, %185: ptr, %186: bool):
    condbr %186, bb53(%180, %181, %182, %183, %184, %185), bb56(%180, %181, %182, %183, %184)
bb53(%187: u64, %188: ptr, %189: bool, %190: bool, %191: u64, %192: ptr):
    %350 = call @func.208(%188, %192)
    br bb54(%187, %188, %189, %190, %191, %350)
bb54(%193: u64, %194: ptr, %195: bool, %196: bool, %197: u64, %198: bool):
    condbr %198, bb56(%193, %194, %195, %196, %197), bb55(%193, %194)
bb55(%199: u64, %200: ptr):
    %351 = const bool true
    br bb58(%199, %200, %351)
bb56(%201: u64, %202: ptr, %203: bool, %204: bool, %205: u64):
    %352 = const u64 1
    %353, %354 = add.overflow u64 %205, %352
    store u64 %353, ptr %228
    %355 = const i64 8
    %356 = gep i8, ptr %228, %355
    store bool %354, ptr %356
    %357 = const i64 8
    %358 = gep i8, ptr %228, %357
    %359 = load bool, ptr %358
    %360 = const bool false
    %361 = icmp eq bool %359, %360
    condbr %361, bb57(%201, %202, %203, %204), bb67
bb57(%206: u64, %207: ptr, %208: bool, %209: bool):
    %362 = load u64, ptr %228
    br bb43(%206, %207, %208, %209, %362)
bb58(%210: u64, %211: ptr, %212: bool):
    condbr %212, bb59(%210), bb61(%210, %211)
bb59(%213: u64):
    %363 = const u64 1
    %364, %365 = add.overflow u64 %213, %363
    store u64 %364, ptr %229
    %366 = const i64 8
    %367 = gep i8, ptr %229, %366
    store bool %365, ptr %367
    %368 = const i64 8
    %369 = gep i8, ptr %229, %368
    %370 = load bool, ptr %369
    %371 = const bool false
    %372 = icmp eq bool %370, %371
    condbr %372, bb60, bb67
bb60:
    %373 = load u64, ptr %229
    br bb17(%373)
bb61(%214: u64, %215: ptr):
    call @func.48(%230, %215)
    br bb62(%214, %221)
bb62(%216: u64, %217: ptr):
    call @func.200(%217, %230)
    br bb63(%216)
bb63(%218: u64):
    %374 = const u64 1
    %375, %376 = add.overflow u64 %218, %374
    store u64 %375, ptr %231
    %377 = const i64 8
    %378 = gep i8, ptr %231, %377
    store bool %376, ptr %378
    %379 = const i64 8
    %380 = gep i8, ptr %231, %379
    %381 = load bool, ptr %380
    %382 = const bool false
    %383 = icmp eq bool %381, %382
    condbr %383, bb64, bb67
bb64:
    %384 = load u64, ptr %231
    br bb17(%384)
bb65:
    %385 = load i64, ptr %221
    store i64 %385, ptr %0
    %386 = const i64 8
    %387 = gep i8, ptr %221, %386
    %388 = const i64 8
    %389 = gep i8, ptr %0, %388
    %390 = load i64, ptr %387
    store i64 %390, ptr %389
    %391 = const i64 16
    %392 = gep i8, ptr %221, %391
    %393 = const i64 16
    %394 = gep i8, ptr %0, %393
    %395 = load i64, ptr %392
    store i64 %395, ptr %394
    br bb66
bb66:
    ret
bb67:
    unreachable
}

fn @Level__mk_max_from_args(functy.202) {
bb0(%0: ptr, %1: ptr):
    %12 = alloca (i64, i64, i64), align 8
    %13 = alloca i64, align 8
    %14 = alloca (i64, i64, i64), align 8
    %15 = alloca (i64, i64), align 8
    %16 = alloca i64, align 8
    %17 = alloca (i64, i64, i64), align 8
    %18 = alloca (i64, i64), align 8
    %19 = alloca (i64, i64), align 8
    %20 = alloca (i64, i64), align 8
    %21 = alloca (i64, i64, i64), align 8
    %22 = alloca i64, align 8
    %23 = alloca (i64, i64, i64), align 8
    %24 = alloca i64, align 8
    %25 = alloca (i64, i64, i64), align 8
    %26 = const bool false
    %27 = const i64 8
    %28 = gep i8, ptr %1, %27
    %29 = load u64, ptr %28
    %30 = const u64 1
    %31 = icmp eq u64 %29, %30
    condbr %31, bb1, bb3
bb1:
    %32 = const u64 0
    %33 = const i64 8
    %34 = gep i8, ptr %1, %33
    %35 = load u64, ptr %34
    %36 = icmp ult u64 %32, %35
    condbr %36, bb2(%32), bb22
bb2(%2: u64):
    %37 = load ptr, ptr %1
    %38 = const u64 24
    %39 = mul u64 %2, %38
    %40 = gep i8, ptr %37, %39
    call @func.48(%0, %40)
    br bb21
bb3:
    %41 = const i64 8
    %42 = gep i8, ptr %1, %41
    %43 = load u64, ptr %42
    %44 = const u64 2
    %45, %46 = sub.overflow u64 %43, %44
    store u64 %45, ptr %15
    %47 = const i64 8
    %48 = gep i8, ptr %15, %47
    store bool %46, ptr %48
    %49 = const i64 8
    %50 = gep i8, ptr %15, %49
    %51 = load bool, ptr %50
    %52 = const bool false
    %53 = icmp eq bool %51, %52
    condbr %53, bb4, bb22
bb4:
    %54 = load u64, ptr %15
    %55 = const i64 8
    %56 = gep i8, ptr %1, %55
    %57 = load u64, ptr %56
    %58 = icmp ult u64 %54, %57
    condbr %58, bb5(%54), bb22
bb5(%3: u64):
    %59 = load ptr, ptr %1
    %60 = const u64 24
    %61 = mul u64 %3, %60
    %62 = gep i8, ptr %59, %61
    call @func.48(%14, %62)
    br bb6
bb6:
    call @func.79(%13, %14)
    br bb7
bb7:
    %63 = const i64 8
    %64 = gep i8, ptr %1, %63
    %65 = load u64, ptr %64
    %66 = const u64 1
    %67, %68 = sub.overflow u64 %65, %66
    store u64 %67, ptr %18
    %69 = const i64 8
    %70 = gep i8, ptr %18, %69
    store bool %68, ptr %70
    %71 = const i64 8
    %72 = gep i8, ptr %18, %71
    %73 = load bool, ptr %72
    %74 = const bool false
    %75 = icmp eq bool %73, %74
    condbr %75, bb8, bb22
bb8:
    %76 = load u64, ptr %18
    %77 = const i64 8
    %78 = gep i8, ptr %1, %77
    %79 = load u64, ptr %78
    %80 = icmp ult u64 %76, %79
    condbr %80, bb9(%76), bb22
bb9(%4: u64):
    %81 = load ptr, ptr %1
    %82 = const u64 24
    %83 = mul u64 %4, %82
    %84 = gep i8, ptr %81, %83
    call @func.48(%17, %84)
    br bb10
bb10:
    call @func.79(%16, %17)
    br bb11
bb11:
    %85 = const bool true
    %86 = load ptr, ptr %13
    %87 = const i64 8
    %88 = gep i8, ptr %12, %87
    store ptr %86, ptr %88
    %89 = load ptr, ptr %16
    %90 = const i64 16
    %91 = gep i8, ptr %12, %90
    store ptr %89, ptr %91
    %92 = const i32 2
    store i32 %92, ptr %12
    %93 = const i64 8
    %94 = gep i8, ptr %1, %93
    %95 = load u64, ptr %94
    %96 = const u64 2
    %97, %98 = sub.overflow u64 %95, %96
    store u64 %97, ptr %19
    %99 = const i64 8
    %100 = gep i8, ptr %19, %99
    store bool %98, ptr %100
    %101 = const i64 8
    %102 = gep i8, ptr %19, %101
    %103 = load bool, ptr %102
    %104 = const bool false
    %105 = icmp eq bool %103, %104
    condbr %105, bb12, bb22
bb12:
    %106 = load u64, ptr %19
    br bb13(%106)
bb13(%5: u64):
    %107 = const u64 0
    %108 = icmp ugt u64 %5, %107
    condbr %108, bb14(%5), bb20
bb14(%6: u64):
    %109 = const u64 1
    %110, %111 = sub.overflow u64 %6, %109
    store u64 %110, ptr %20
    %112 = const i64 8
    %113 = gep i8, ptr %20, %112
    store bool %111, ptr %113
    %114 = const i64 8
    %115 = gep i8, ptr %20, %114
    %116 = load bool, ptr %115
    %117 = const bool false
    %118 = icmp eq bool %116, %117
    condbr %118, bb15, bb22
bb15:
    %119 = load u64, ptr %20
    %120 = const i64 8
    %121 = gep i8, ptr %1, %120
    %122 = load u64, ptr %121
    %123 = icmp ult u64 %119, %122
    condbr %123, bb16(%119, %119), bb22
bb16(%7: u64, %8: u64):
    %124 = load ptr, ptr %1
    %125 = const u64 24
    %126 = mul u64 %8, %125
    %127 = gep i8, ptr %124, %126
    call @func.48(%23, %127)
    br bb17(%7)
bb17(%9: u64):
    call @func.79(%22, %23)
    br bb18(%9)
bb18(%10: u64):
    %128 = const bool false
    %129 = load i64, ptr %12
    store i64 %129, ptr %25
    %130 = const i64 8
    %131 = gep i8, ptr %12, %130
    %132 = const i64 8
    %133 = gep i8, ptr %25, %132
    %134 = load i64, ptr %131
    store i64 %134, ptr %133
    %135 = const i64 16
    %136 = gep i8, ptr %12, %135
    %137 = const i64 16
    %138 = gep i8, ptr %25, %137
    %139 = load i64, ptr %136
    store i64 %139, ptr %138
    call @func.79(%24, %25)
    br bb19(%10)
bb19(%11: u64):
    %140 = load ptr, ptr %22
    %141 = const i64 8
    %142 = gep i8, ptr %21, %141
    store ptr %140, ptr %142
    %143 = load ptr, ptr %24
    %144 = const i64 16
    %145 = gep i8, ptr %21, %144
    store ptr %143, ptr %145
    %146 = const i32 2
    store i32 %146, ptr %21
    %147 = const bool true
    %148 = load i64, ptr %21
    store i64 %148, ptr %12
    %149 = const i64 8
    %150 = gep i8, ptr %21, %149
    %151 = const i64 8
    %152 = gep i8, ptr %12, %151
    %153 = load i64, ptr %150
    store i64 %153, ptr %152
    %154 = const i64 16
    %155 = gep i8, ptr %21, %154
    %156 = const i64 16
    %157 = gep i8, ptr %12, %156
    %158 = load i64, ptr %155
    store i64 %158, ptr %157
    br bb13(%11)
bb20:
    %159 = const bool false
    %160 = load i64, ptr %12
    store i64 %160, ptr %0
    %161 = const i64 8
    %162 = gep i8, ptr %12, %161
    %163 = const i64 8
    %164 = gep i8, ptr %0, %163
    %165 = load i64, ptr %162
    store i64 %165, ptr %164
    %166 = const i64 16
    %167 = gep i8, ptr %12, %166
    %168 = const i64 16
    %169 = gep i8, ptr %0, %168
    %170 = load i64, ptr %167
    store i64 %170, ptr %169
    %171 = const bool false
    br bb21
bb21:
    ret
bb22:
    unreachable
}

fn @Level__kind_ord(functy.203) {
bb0(%0: ptr):
    %2 = load i32, ptr %0
    %3 = sext i32 %2 to i64
    switch %3 [ 0: bb6 1: bb5 2: bb4 3: bb3 4: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %4 = const u8 4
    br bb7(%4)
bb3:
    %5 = const u8 3
    br bb7(%5)
bb4:
    %6 = const u8 2
    br bb7(%6)
bb5:
    %7 = const u8 1
    br bb7(%7)
bb6:
    %8 = const u8 0
    br bb7(%8)
bb7(%1: u8):
    ret %1
}

fn @Level__is_explicit(functy.204) {
bb0(%0: ptr):
    %2 = alloca (i64, i64), align 8
    call @func.171(%2, %0)
    br bb1
bb1:
    %3 = load ptr, ptr %2
    %4 = load i32, ptr %3
    %5 = sext i32 %4 to i64
    switch %5 [ 0: bb3 default: bb2 ]
bb2:
    %6 = const bool false
    br bb4(%6)
bb3:
    %7 = const bool true
    br bb4(%7)
bb4(%1: bool):
    ret %1
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecTRNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelBF_EE3popBI_(functy.205) {
}

fn @_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelNtB7_9PartialEq2eqBF_(functy.206) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecTRNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelBG_EE4pushBJ_(functy.207) {
}

fn @Level__is_geq_core(functy.208) {
bb0(%0: ptr, %1: ptr):
    %53 = alloca (i64, i64, i64), align 8
    %54 = alloca i64, align 8
    %55 = alloca (i64, i64), align 8
    %56 = alloca (i64, i64), align 8
    %57 = alloca i64, align 8
    %58 = alloca i64, align 8
    %59 = alloca i64, align 8
    %60 = alloca (i64, i64), align 8
    %61 = alloca (i64, i64), align 8
    %62 = alloca (i64, i64), align 8
    %63 = alloca (i64, i64), align 8
    %64 = alloca (i64, i64), align 8
    %65 = alloca (i64, i64), align 8
    %66 = alloca i64, align 8
    %67 = alloca (i64, i64), align 8
    %68 = alloca (i64, i64), align 8
    %69 = const i64 16
    %70 = heap_alloc rust_heap i8, %69, align 8
    store ptr %70, ptr %54
    br bb1(%0, %1)
bb1(%2: ptr, %3: ptr):
    store ptr %2, ptr %55
    %71 = const i64 8
    %72 = gep i8, ptr %55, %71
    store ptr %3, ptr %72
    %73 = load ptr, ptr %54
    %74 = ptrtoint ptr %73 to u64
    %75 = const u64 8
    %76 = const u64 1
    %77 = sub u64 %75, %76
    %78 = and u64 %74, %77
    %79 = const u64 0
    %80 = icmp eq u64 %78, %79
    condbr %80, bb47(%73), bb54
bb2:
    call @func.205(%56, %53)
    br bb3
bb3:
    %81 = load i64, ptr %56
    %82 = const i64 0
    %83 = icmp eq i64 %81, %82
    %84 = const i64 0
    %85 = const i64 1
    %86 = select i64 %83, %84, %85
    switch %86 [ 1: bb4 0: bb44 default: bb49 ]
bb4:
    %87 = load ptr, ptr %56
    store ptr %87, ptr %57
    %88 = const i64 8
    %89 = gep i8, ptr %56, %88
    %90 = load ptr, ptr %89
    store ptr %90, ptr %58
    %91 = call @func.206(%57, %58)
    br bb5(%91)
bb5(%4: bool):
    condbr %4, bb2, bb6
bb6:
    %92 = load ptr, ptr %58
    %93 = call @func.15(%92)
    br bb7(%93)
bb7(%5: bool):
    condbr %5, bb2, bb8
bb8:
    %94 = load ptr, ptr %57
    call @func.171(%60, %94)
    br bb9
bb9:
    %95 = load ptr, ptr %60
    store ptr %95, ptr %59
    %96 = const i64 8
    %97 = gep i8, ptr %60, %96
    %98 = load u32, ptr %97
    %99 = const u32 0
    %100 = icmp ugt u32 %98, %99
    condbr %100, bb10(%98), bb12(%98)
bb10(%6: u32):
    %101 = load ptr, ptr %59
    %102 = load ptr, ptr %58
    %103 = call @func.78(%101, %102)
    br bb11(%6, %103)
bb11(%7: u32, %8: bool):
    condbr %8, bb2, bb12(%7)
bb12(%9: u32):
    %104 = load ptr, ptr %58
    %105 = load i32, ptr %104
    %106 = sext i32 %105 to i64
    switch %106 [ 2: bb14 default: bb13(%9) ]
bb13(%10: u32):
    %107 = load ptr, ptr %57
    %108 = load i32, ptr %107
    %109 = sext i32 %108 to i64
    switch %109 [ 2: bb19 default: bb18(%10) ]
bb14:
    %110 = load ptr, ptr %58
    %111 = const i64 8
    %112 = gep i8, ptr %110, %111
    %113 = load ptr, ptr %58
    %114 = const i64 16
    %115 = gep i8, ptr %113, %114
    %116 = load ptr, ptr %112
    %117 = const i64 16
    %118 = gep i8, ptr %116, %117
    br bb15(%115, %53, %118)
bb15(%11: ptr, %12: ptr, %13: ptr):
    %119 = load ptr, ptr %57
    store ptr %119, ptr %61
    %120 = const i64 8
    %121 = gep i8, ptr %61, %120
    store ptr %13, ptr %121
    call @func.207(%12, %61)
    br bb16(%11)
bb16(%14: ptr):
    %122 = load ptr, ptr %14
    %123 = const i64 16
    %124 = gep i8, ptr %122, %123
    br bb17(%53, %124)
bb17(%15: ptr, %16: ptr):
    %125 = load ptr, ptr %57
    store ptr %125, ptr %62
    %126 = const i64 8
    %127 = gep i8, ptr %62, %126
    store ptr %16, ptr %127
    call @func.207(%15, %62)
    br bb50
bb18(%17: u32):
    %128 = load ptr, ptr %58
    %129 = load i32, ptr %128
    %130 = sext i32 %129 to i64
    switch %130 [ 3: bb27 default: bb26(%17) ]
bb19:
    %131 = load ptr, ptr %57
    %132 = const i64 8
    %133 = gep i8, ptr %131, %132
    %134 = load ptr, ptr %57
    %135 = const i64 16
    %136 = gep i8, ptr %134, %135
    %137 = load ptr, ptr %133
    %138 = const i64 16
    %139 = gep i8, ptr %137, %138
    br bb20(%136, %139)
bb20(%18: ptr, %19: ptr):
    %140 = load ptr, ptr %58
    %141 = call @func.210(%19, %140)
    br bb21(%18, %141)
bb21(%20: ptr, %21: bool):
    condbr %21, bb2, bb22(%20)
bb22(%22: ptr):
    %142 = load ptr, ptr %22
    %143 = const i64 16
    %144 = gep i8, ptr %142, %143
    br bb23(%144)
bb23(%23: ptr):
    %145 = load ptr, ptr %58
    %146 = call @func.210(%23, %145)
    br bb24(%146)
bb24(%24: bool):
    condbr %24, bb2, bb25
bb25:
    %147 = const bool false
    br bb45(%147)
bb26(%25: u32):
    %148 = load ptr, ptr %57
    %149 = load i32, ptr %148
    %150 = sext i32 %149 to i64
    switch %150 [ 3: bb32 default: bb31(%25) ]
bb27:
    %151 = load ptr, ptr %58
    %152 = const i64 8
    %153 = gep i8, ptr %151, %152
    %154 = load ptr, ptr %58
    %155 = const i64 16
    %156 = gep i8, ptr %154, %155
    %157 = load ptr, ptr %153
    %158 = const i64 16
    %159 = gep i8, ptr %157, %158
    br bb28(%156, %53, %159)
bb28(%26: ptr, %27: ptr, %28: ptr):
    %160 = load ptr, ptr %57
    store ptr %160, ptr %63
    %161 = const i64 8
    %162 = gep i8, ptr %63, %161
    store ptr %28, ptr %162
    call @func.207(%27, %63)
    br bb29(%26)
bb29(%29: ptr):
    %163 = load ptr, ptr %29
    %164 = const i64 16
    %165 = gep i8, ptr %163, %164
    br bb30(%53, %165)
bb30(%30: ptr, %31: ptr):
    %166 = load ptr, ptr %57
    store ptr %166, ptr %64
    %167 = const i64 8
    %168 = gep i8, ptr %64, %167
    store ptr %31, ptr %168
    call @func.207(%30, %64)
    br bb51
bb31(%32: u32):
    %169 = load ptr, ptr %58
    call @func.171(%67, %169)
    br bb34(%32)
bb32:
    %170 = load ptr, ptr %57
    %171 = const i64 16
    %172 = gep i8, ptr %170, %171
    %173 = load ptr, ptr %172
    %174 = const i64 16
    %175 = gep i8, ptr %173, %174
    br bb33(%53, %175)
bb33(%33: ptr, %34: ptr):
    store ptr %34, ptr %65
    %176 = load ptr, ptr %58
    %177 = const i64 8
    %178 = gep i8, ptr %65, %177
    store ptr %176, ptr %178
    call @func.207(%33, %65)
    br bb52
bb34(%35: u32):
    %179 = load ptr, ptr %67
    store ptr %179, ptr %66
    %180 = const i64 8
    %181 = gep i8, ptr %67, %180
    %182 = load u32, ptr %181
    %183 = call @func.206(%59, %66)
    br bb35(%35, %182, %183)
bb35(%36: u32, %37: u32, %38: bool):
    condbr %38, bb38(%36, %37), bb36(%36, %37)
bb36(%39: u32, %40: u32):
    %184 = load ptr, ptr %66
    %185 = call @func.15(%184)
    br bb37(%39, %40, %185)
bb37(%41: u32, %42: u32, %43: bool):
    condbr %43, bb38(%41, %42), bb40(%41, %42)
bb38(%44: u32, %45: u32):
    %186 = icmp uge u32 %44, %45
    condbr %186, bb2, bb39
bb39:
    %187 = const bool false
    br bb45(%187)
bb40(%46: u32, %47: u32):
    %188 = icmp eq u32 %46, %47
    condbr %188, bb41(%46), bb43
bb41(%48: u32):
    %189 = const u32 0
    %190 = icmp ugt u32 %48, %189
    condbr %190, bb42, bb43
bb42:
    %191 = load ptr, ptr %59
    store ptr %191, ptr %68
    %192 = load ptr, ptr %66
    %193 = const i64 8
    %194 = gep i8, ptr %68, %193
    store ptr %192, ptr %194
    call @func.207(%53, %68)
    br bb53
bb43:
    %195 = const bool false
    br bb45(%195)
bb44:
    %196 = const bool true
    br bb46(%196)
bb45(%49: bool):
    br bb46(%49)
bb46(%50: bool):
    ret %50
bb47(%51: ptr):
    %197 = ptrtoint ptr %51 to u64
    %198 = const u64 16
    %199 = const u64 0
    %200 = icmp ne u64 %198, %199
    %201 = const u64 0
    %202 = icmp eq u64 %197, %201
    %203 = const bool false
    %204 = select bool %202, %200, %203
    %205 = const bool false
    %206 = icmp eq bool %204, %205
    condbr %206, bb48(%51), bb54
bb48(%52: ptr):
    %207 = load i64, ptr %55
    store i64 %207, ptr %52
    %208 = const i64 8
    %209 = gep i8, ptr %55, %208
    %210 = const i64 8
    %211 = gep i8, ptr %52, %210
    %212 = load i64, ptr %209
    store i64 %212, ptr %211
    %213 = load ptr, ptr %54
    %214 = const i64 8
    %215 = gep i8, ptr %53, %214
    store ptr %213, ptr %215
    %216 = const i64 1
    store i64 %216, ptr %53
    %217 = const i64 1
    %218 = const i64 16
    %219 = gep i8, ptr %53, %218
    store i64 %217, ptr %219
    br bb2
bb49:
    unreachable
bb50:
    br bb2
bb51:
    br bb2
bb52:
    br bb2
bb53:
    br bb2
bb54:
    unreachable
}

fn @_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelNtB7_9PartialEq2eqBF_(functy.209) {
}

fn @Level__is_geq_leaf(functy.210) {
bb0(%0: ptr, %1: ptr):
    %20 = alloca i64, align 8
    %21 = alloca i64, align 8
    %22 = alloca i64, align 8
    %23 = alloca (i64, i64), align 8
    %24 = alloca i64, align 8
    %25 = alloca (i64, i64), align 8
    store ptr %0, ptr %20
    store ptr %1, ptr %21
    %26 = call @func.209(%20, %21)
    br bb1(%26)
bb1(%2: bool):
    condbr %2, bb4, bb2
bb2:
    %27 = load ptr, ptr %21
    %28 = call @func.15(%27)
    br bb3(%28)
bb3(%3: bool):
    condbr %3, bb4, bb5
bb4:
    %29 = const bool true
    br bb17(%29)
bb5:
    %30 = load ptr, ptr %20
    call @func.171(%23, %30)
    br bb6
bb6:
    %31 = load ptr, ptr %23
    store ptr %31, ptr %22
    %32 = const i64 8
    %33 = gep i8, ptr %23, %32
    %34 = load u32, ptr %33
    %35 = const u32 0
    %36 = icmp ugt u32 %34, %35
    condbr %36, bb7(%34), bb10(%34)
bb7(%4: u32):
    %37 = load ptr, ptr %22
    %38 = load ptr, ptr %21
    %39 = call @func.78(%37, %38)
    br bb8(%4, %39)
bb8(%5: u32, %6: bool):
    condbr %6, bb9, bb10(%5)
bb9:
    %40 = const bool true
    br bb17(%40)
bb10(%7: u32):
    %41 = load ptr, ptr %21
    call @func.171(%25, %41)
    br bb11(%7)
bb11(%8: u32):
    %42 = load ptr, ptr %25
    store ptr %42, ptr %24
    %43 = const i64 8
    %44 = gep i8, ptr %25, %43
    %45 = load u32, ptr %44
    %46 = call @func.209(%22, %24)
    br bb12(%8, %45, %46)
bb12(%9: u32, %10: u32, %11: bool):
    condbr %11, bb15(%9, %10), bb13(%9, %10)
bb13(%12: u32, %13: u32):
    %47 = load ptr, ptr %24
    %48 = call @func.15(%47)
    br bb14(%12, %13, %48)
bb14(%14: u32, %15: u32, %16: bool):
    condbr %16, bb15(%14, %15), bb16
bb15(%17: u32, %18: u32):
    %49 = icmp uge u32 %17, %18
    br bb17(%49)
bb16:
    %50 = const bool false
    br bb17(%50)
bb17(%19: bool):
    ret %19
}
"#;

// Two frozen snapshots of the `--mir-emit-closure check_decl_readonly` output,
// selected by exact fixture-compiler identity (see build.rs):
//   * Rust 1.95 (the `MIR_DECL_UNIVERSE_TRUST_IR` inline const above) — baked by
//     the fixtures' 1.95 generation toolchain: that build's repr(Rust) niche/discriminant
//     layout, and the older sret ABI `(sret, this) -> ()` for the Arc<Expr>/Arc<Level>
//     clones and the Vec<&Expr>/Vec<&Level> pops.
//   * Rust 1.97 (`clean_decl_universe.trust.tir`) — re-emitted by the current self-hosted
//     frontend (prerelease rustc-master layout). Only four pointer-sized leaves drifted
//     ABI to register-return `(this) -> ptr`: Arc<Expr>::clone, Arc<Level>::clone,
//     Vec<&Expr>::pop, Vec<&Level>::pop (each pairs with its cfg-selected shim below).
//     Re-emit: the REGEN command in the slice header, adding
//     `-C panic=abort -C overflow-checks=off -C debug-assertions=off` — matching the
//     frozen generation profile (abort-style `call`s; no bounds-check/track_caller
//     Location threading; no unwind landing pads). The only other delta is drop_glue
//     leaves + drifted v0-mangling disambiguators, both absorbed by `norm_extern`.
// Both certified fixture lanes run the test; nothing is ignored.
#[cfg(kernel_fixture_layout_matches)]
const TIR: &str = MIR_DECL_UNIVERSE_TRUST_IR;
#[cfg(not(kernel_fixture_layout_matches))]
const TIR: &str = include_str!("clean_decl_universe.trust.tir");

// ════════════════════════════════════════════════════════════════════════════
// NATIVE ORACLE — byte-equivalent mirror of clean_decl_universe_slice.rs (the
// verbatim kernel transcription; see the slice for the source-line provenance
// and the modeled-boundary notes B1..B10).
// ════════════════════════════════════════════════════════════════════════════

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FVarId(pub u64);

pub type LevelArc = Arc<Level>;

#[inline(always)]
fn level_arc(l: Level) -> LevelArc {
    Arc::new(l)
}

#[derive(Clone, Debug)]
pub enum Level {
    Zero,
    Succ(LevelArc),
    Max(LevelArc, LevelArc),
    IMax(LevelArc, LevelArc),
    Param(Name),
}

impl PartialEq for Level {
    fn eq(&self, other: &Self) -> bool {
        let mut stack: Vec<(&Level, &Level)> = vec![(self, other)];
        while let Some((a, b)) = stack.pop() {
            match (a, b) {
                (Level::Zero, Level::Zero) => {}
                (Level::Succ(la), Level::Succ(lb)) => {
                    stack.push((la, lb));
                }
                (Level::Max(la1, la2), Level::Max(lb1, lb2))
                | (Level::IMax(la1, la2), Level::IMax(lb1, lb2)) => {
                    stack.push((la1, lb1));
                    stack.push((la2, lb2));
                }
                (Level::Param(na), Level::Param(nb)) => {
                    if na != nb {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
    }
}

impl Eq for Level {}

impl std::hash::Hash for Level {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Level::Zero => {}
            Level::Succ(l) => l.hash(state),
            Level::Max(l, r) | Level::IMax(l, r) => {
                l.hash(state);
                r.hash(state);
            }
            Level::Param(n) => n.hash(state),
        }
    }
}

impl Level {
    pub fn zero() -> Self {
        Level::Zero
    }
    pub fn succ(l: Level) -> Self {
        Level::Succ(level_arc(l))
    }
    pub fn max(l1: Level, l2: Level) -> Self {
        if l1 == l2 {
            return l1;
        }
        if l1.is_zero() {
            return l2;
        }
        if l2.is_zero() {
            return l1;
        }
        Level::Max(level_arc(l1), level_arc(l2))
    }
    pub fn imax(l1: Level, l2: Level) -> Self {
        if l2.is_zero() {
            return Level::Zero;
        }
        if l2.is_nonzero() {
            return Level::max(l1, l2);
        }
        if l1.is_zero() {
            return l2;
        }
        if l1 == Level::succ(Level::zero()) {
            return l2;
        }
        if l1 == l2 {
            return l1;
        }
        Level::IMax(level_arc(l1), level_arc(l2))
    }
    pub fn param(name: Name) -> Self {
        Level::Param(name)
    }
    pub fn is_zero(&self) -> bool {
        match self {
            Level::Zero => true,
            Level::Succ(_) | Level::Param(_) => false,
            Level::Max(l1, l2) => l1.is_zero() && l2.is_zero(),
            Level::IMax(_, l2) => l2.is_zero(),
        }
    }
    fn is_nonzero(&self) -> bool {
        match self {
            Level::Zero | Level::Param(_) => false,
            Level::Succ(_) => true,
            Level::Max(l1, l2) => l1.is_nonzero() || l2.is_nonzero(),
            Level::IMax(_, l2) => l2.is_nonzero(),
        }
    }
    pub fn has_params(&self) -> bool {
        match self {
            Level::Zero => false,
            Level::Succ(l) => l.has_params(),
            Level::Max(l1, l2) | Level::IMax(l1, l2) => l1.has_params() || l2.has_params(),
            Level::Param(_) => true,
        }
    }
    fn get_offset(&self) -> (&Level, u32) {
        let mut current = self;
        let mut offset = 0u32;
        while let Level::Succ(inner) = current {
            offset = offset.saturating_add(1);
            current = inner;
        }
        (current, offset)
    }
    fn add_offset(&self, n: u32) -> Level {
        let mut result = self.clone();
        let mut c = 0u32;
        while c < n {
            result = Level::succ(result);
            c += 1;
        }
        result
    }
    pub fn normalize(&self) -> Level {
        self.normalize_impl()
    }
    fn kind_ord(&self) -> u8 {
        match self {
            Level::Zero => 0,
            Level::Succ(_) => 1,
            Level::Max(_, _) => 2,
            Level::IMax(_, _) => 3,
            Level::Param(_) => 4,
        }
    }
    fn is_norm_lt(a: &Level, b: &Level) -> bool {
        let mut a = a;
        let mut b = b;
        loop {
            if a == b {
                return false;
            }
            let (base1, off1) = a.get_offset();
            let (base2, off2) = b.get_offset();
            if base1 != base2 {
                if base1.kind_ord() != base2.kind_ord() {
                    return base1.kind_ord() < base2.kind_ord();
                }
                match (base1, base2) {
                    (Level::Param(n1), Level::Param(n2)) => return n1 < n2,
                    (Level::Max(a1, b1), Level::Max(a2, b2))
                    | (Level::IMax(a1, b1), Level::IMax(a2, b2)) => {
                        if a1 != a2 {
                            a = a1;
                            b = a2;
                            continue;
                        } else {
                            a = b1;
                            b = b2;
                            continue;
                        }
                    }
                    _ => return false,
                }
            } else {
                return off1 < off2;
            }
        }
    }
    fn push_max_args(l: &Level, buf: &mut Vec<Level>) {
        let mut stack: Vec<&Level> = vec![l];
        while let Some(current) = stack.pop() {
            match current {
                Level::Max(a, b) => {
                    stack.push(b);
                    stack.push(a);
                }
                _ => buf.push(current.clone()),
            }
        }
    }
    fn mk_max_from_args(args: &[Level]) -> Level {
        if args.len() == 1 {
            return args[0].clone();
        }
        let mut r = Level::Max(
            level_arc(args[args.len() - 2].clone()),
            level_arc(args[args.len() - 1].clone()),
        );
        let mut i = args.len() - 2;
        while i > 0 {
            i -= 1;
            r = Level::Max(level_arc(args[i].clone()), level_arc(r));
        }
        r
    }
    fn is_explicit(&self) -> bool {
        matches!(self.get_offset().0, Level::Zero)
    }
    fn normalize_impl(&self) -> Level {
        let (base, outer_offset) = self.get_offset();
        match base {
            Level::Zero | Level::Param(_) => {
                let mut result = match base {
                    Level::Zero => Level::Zero,
                    Level::Param(n) => Level::Param(*n),
                    _ => Level::Zero,
                };
                let mut c = 0u32;
                while c < outer_offset {
                    result = Level::succ(result);
                    c += 1;
                }
                result
            }
            Level::Succ(_) => base.clone(),
            Level::IMax(l1, l2) => {
                let l1_norm = l1.normalize_impl();
                let l2_norm = l2.normalize_impl();
                let result = Level::imax(l1_norm, l2_norm);
                if matches!(result, Level::Max(_, _)) {
                    result.add_offset(outer_offset).normalize_impl()
                } else {
                    result.add_offset(outer_offset)
                }
            }
            Level::Max(_, _) => Self::normalize_max(base, outer_offset),
        }
    }
    fn normalize_max(base: &Level, outer_offset: u32) -> Level {
        let mut todo = Vec::new();
        Self::push_max_args(base, &mut todo);
        let mut args = Vec::new();
        let mut ti = 0;
        while ti < todo.len() {
            let normed = todo[ti].normalize_impl();
            Self::push_max_args(&normed, &mut args);
            ti += 1;
        }
        let mut i = 1;
        while i < args.len() {
            let mut j = i;
            while j > 0 && Self::is_norm_lt(&args[j], &args[j - 1]) {
                args.swap(j, j - 1);
                j -= 1;
            }
            i += 1;
        }
        let deduped = Self::dedup_max_args(&args);
        let mut rargs = Self::subsume_max_args(&deduped);
        if outer_offset > 0 {
            let mut k = 0;
            while k < rargs.len() {
                rargs[k] = rargs[k].add_offset(outer_offset);
                k += 1;
            }
        }
        if rargs.is_empty() {
            Level::Zero
        } else {
            Self::mk_max_from_args(&rargs)
        }
    }
    fn subsume_max_args(args: &[Level]) -> Vec<Level> {
        if args.len() <= 1 {
            return args.to_vec();
        }
        let mut any_composite = false;
        {
            let mut c = 0;
            while c < args.len() {
                if matches!(args[c].get_offset().0, Level::Max(_, _) | Level::IMax(_, _)) {
                    any_composite = true;
                    break;
                }
                c += 1;
            }
        }
        if !any_composite {
            return args.to_vec();
        }
        let mut kept: Vec<Level> = Vec::new();
        let mut i = 0;
        while i < args.len() {
            let x = &args[i];
            let x_composite = matches!(x.get_offset().0, Level::Max(_, _) | Level::IMax(_, _));
            let mut dominated_by_kept = false;
            {
                let mut ky = 0;
                while ky < kept.len() {
                    let y = &kept[ky];
                    let y_composite =
                        matches!(y.get_offset().0, Level::Max(_, _) | Level::IMax(_, _));
                    if (x_composite || y_composite) && Self::is_geq_core(y, x) {
                        dominated_by_kept = true;
                        break;
                    }
                    ky += 1;
                }
            }
            if dominated_by_kept {
                i += 1;
                continue;
            }
            let mut dominated_by_later_strict = false;
            {
                let mut ly = i + 1;
                while ly < args.len() {
                    let y = &args[ly];
                    let y_composite =
                        matches!(y.get_offset().0, Level::Max(_, _) | Level::IMax(_, _));
                    if (x_composite || y_composite)
                        && Self::is_geq_core(y, x)
                        && !Self::is_geq_core(x, y)
                    {
                        dominated_by_later_strict = true;
                        break;
                    }
                    ly += 1;
                }
            }
            if dominated_by_later_strict {
                i += 1;
                continue;
            }
            kept.push(x.clone());
            i += 1;
        }
        kept
    }
    fn dedup_max_args(args: &[Level]) -> Vec<Level> {
        let mut rargs: Vec<Level> = Vec::new();
        let mut i = 0;
        if args[i].is_explicit() {
            while i + 1 < args.len() && args[i + 1].is_explicit() {
                i += 1;
            }
            let k = args[i].get_offset().1;
            let mut j = i + 1;
            while j < args.len() {
                if args[j].get_offset().1 >= k {
                    break;
                }
                j += 1;
            }
            if j < args.len() {
                i += 1;
            }
        }
        if i < args.len() {
            rargs.push(args[i].clone());
            let mut prev_offset = args[i].get_offset();
            i += 1;
            while i < args.len() {
                let curr_offset = args[i].get_offset();
                if prev_offset.0 == curr_offset.0 {
                    if prev_offset.1 < curr_offset.1 {
                        prev_offset = curr_offset;
                        rargs.pop();
                        rargs.push(args[i].clone());
                    }
                } else {
                    prev_offset = curr_offset;
                    rargs.push(args[i].clone());
                }
                i += 1;
            }
        }
        rargs
    }
    fn is_geq(l1: &Level, l2: &Level) -> bool {
        let n1 = l1.normalize();
        let n2 = l2.normalize();
        Self::is_geq_core(&n1, &n2)
    }
    fn is_geq_core(l1: &Level, l2: &Level) -> bool {
        let mut worklist: Vec<(&Level, &Level)> = vec![(l1, l2)];
        while let Some((l1, l2)) = worklist.pop() {
            if l1 == l2 || l2.is_zero() {
                continue;
            }
            let (base1, offset1) = l1.get_offset();
            if offset1 > 0 && *base1 == *l2 {
                continue;
            }
            if let Level::Max(a, b) = l2 {
                worklist.push((l1, a));
                worklist.push((l1, b));
                continue;
            }
            if let Level::Max(a, b) = l1 {
                if Self::is_geq_leaf(a, l2) || Self::is_geq_leaf(b, l2) {
                    continue;
                }
                return false;
            }
            if let Level::IMax(a, b) = l2 {
                worklist.push((l1, a));
                worklist.push((l1, b));
                continue;
            }
            if let Level::IMax(_, b) = l1 {
                worklist.push((b, l2));
                continue;
            }
            let (base2, offset2) = l2.get_offset();
            if base1 == base2 || base2.is_zero() {
                if offset1 >= offset2 {
                    continue;
                }
                return false;
            }
            if offset1 == offset2 && offset1 > 0 {
                worklist.push((base1, base2));
                continue;
            }
            return false;
        }
        true
    }
    fn is_geq_leaf(l1: &Level, l2: &Level) -> bool {
        if l1 == l2 || l2.is_zero() {
            return true;
        }
        let (base1, offset1) = l1.get_offset();
        if offset1 > 0 && *base1 == *l2 {
            return true;
        }
        let (base2, offset2) = l2.get_offset();
        (base1 == base2 || base2.is_zero()) && offset1 >= offset2
    }
    pub fn is_def_eq(l1: &Level, l2: &Level) -> bool {
        if l1 == l2 {
            return true;
        }
        l1.normalize() == l2.normalize()
    }
}

pub type LevelVec = Vec<Level>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Literal {
    Nat(u64),
    Str(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BinderData {
    pub info: u8,
    pub mult: u8,
}

#[inline]
fn mix_hash(h: u64, k: u64) -> u64 {
    const M: u64 = 0xc6a4_a793_5bd1_e995;
    const R: u32 = 47;
    let mut k = k.wrapping_mul(M);
    k ^= k >> R;
    k ^= M;
    let mut h = h ^ k;
    h = h.wrapping_mul(M);
    h
}

pub struct KaniHasher {
    state: u64,
}
impl KaniHasher {
    fn new() -> Self {
        KaniHasher { state: 0 }
    }
}
impl std::hash::Hasher for KaniHasher {
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
fn hash_name(value: &Name) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}
#[inline]
fn hash_level(value: &Level) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}
#[inline]
fn hash_lit(value: &Literal) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[inline]
fn level_has_mvar(_l: &Level) -> bool {
    false
}

#[derive(Clone, Copy, Debug)]
pub struct ExprMeta(u64);

impl ExprMeta {
    const HASH_MASK: u64 = 0xFFFF_FFFF;
    const DEPTH_SHIFT: u32 = 32;
    const DEPTH_MASK: u64 = 0xFF;
    const HAS_FVAR_BIT: u32 = 40;
    const HAS_EXPR_MVAR_BIT: u32 = 41;
    const HAS_LEVEL_MVAR_BIT: u32 = 42;
    const HAS_LEVEL_PARAM_BIT: u32 = 43;
    const BVAR_RANGE_SHIFT: u32 = 44;
    const MAX_DEPTH: u32 = 255;
    const MAX_BVAR_RANGE: u32 = 1_048_575;

    fn pack(
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
    fn raw(self) -> u64 {
        self.0
    }
    fn hash(self) -> u32 {
        (self.0 & Self::HASH_MASK) as u32
    }
    fn approx_depth(self) -> u8 {
        ((self.0 >> Self::DEPTH_SHIFT) & Self::DEPTH_MASK) as u8
    }
    fn has_fvar(self) -> bool {
        (self.0 >> Self::HAS_FVAR_BIT) & 1 == 1
    }
    fn has_expr_mvar(self) -> bool {
        (self.0 >> Self::HAS_EXPR_MVAR_BIT) & 1 == 1
    }
    fn has_level_mvar(self) -> bool {
        (self.0 >> Self::HAS_LEVEL_MVAR_BIT) & 1 == 1
    }
    fn has_level_param(self) -> bool {
        (self.0 >> Self::HAS_LEVEL_PARAM_BIT) & 1 == 1
    }
    fn loose_bvar_range(self) -> u32 {
        (self.0 >> Self::BVAR_RANGE_SHIFT) as u32
    }

    fn mk_app_meta(f: ExprMeta, a: ExprMeta) -> ExprMeta {
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
    fn mk_binder_meta(ty: ExprMeta, body: ExprMeta, extra_hash: u64) -> ExprMeta {
        let depth = (ty.approx_depth().max(body.approx_depth()) as u32 + 1).min(Self::MAX_DEPTH);
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
    fn mk_let_meta(ty: ExprMeta, val: ExprMeta, body: ExprMeta) -> ExprMeta {
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
    fn mk_wrapper_meta(inner: ExprMeta, extra_hash: u64) -> ExprMeta {
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
    MData(u32, Arc<Expr>),
}

impl ExprKind {
    fn compute_meta(&self) -> ExprMeta {
        match self {
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
            ExprKind::FVar(id) => {
                ExprMeta::pack(mix_hash(13, id.0) as u32, 0, 0, true, false, false, false)
            }
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
                ExprMeta::pack(
                    mix_hash(5, name_hash) as u32,
                    0,
                    0,
                    false,
                    false,
                    false,
                    false,
                )
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
            ExprKind::MData(_, expr) => ExprMeta::mk_wrapper_meta(expr.meta(), 0),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Expr {
    kind: ExprKind,
    meta: ExprMeta,
}

impl Expr {
    fn from_kind(kind: ExprKind) -> Self {
        let meta = kind.compute_meta();
        Expr { kind, meta }
    }
    fn meta(&self) -> ExprMeta {
        self.meta
    }
    fn kind(&self) -> &ExprKind {
        &self.kind
    }
    fn loose_bvar_range(&self) -> u32 {
        self.meta.loose_bvar_range()
    }
    fn has_fvar_quick(&self) -> bool {
        self.meta.has_fvar()
    }
    fn has_expr_mvar_quick(&self) -> bool {
        self.meta.has_expr_mvar()
    }
    fn has_level_mvar_quick(&self) -> bool {
        self.meta.has_level_mvar()
    }
    fn bvar(idx: u32) -> Self {
        Expr::from_kind(ExprKind::BVar(idx))
    }
    fn cnst(name: Name) -> Self {
        Expr::from_kind(ExprKind::Const(name, vec![]))
    }
    fn sort0() -> Self {
        Expr::from_kind(ExprKind::Sort(Level::Zero))
    }
    fn sort(l: Level) -> Self {
        Expr::from_kind(ExprKind::Sort(l))
    }
    fn nat(n: u64) -> Self {
        Expr::from_kind(ExprKind::Lit(Literal::Nat(n)))
    }
    fn app(func: Expr, arg: Expr) -> Self {
        Expr::from_kind(ExprKind::App(Arc::new(func), Arc::new(arg)))
    }
    fn lam(bd: BinderData, ty: Expr, body: Expr) -> Self {
        Expr::from_kind(ExprKind::Lam(bd, Arc::new(ty), Arc::new(body)))
    }
    fn pi(bd: BinderData, ty: Expr, body: Expr) -> Self {
        Expr::from_kind(ExprKind::Pi(bd, Arc::new(ty), Arc::new(body)))
    }
    fn lett(name: Name, ty: Expr, val: Expr, body: Expr, nondep: bool) -> Self {
        Expr::from_kind(ExprKind::Let(
            name,
            Arc::new(ty),
            Arc::new(val),
            Arc::new(body),
            nondep,
        ))
    }
    fn proj(name: Name, idx: u32, e: Expr) -> Self {
        Expr::from_kind(ExprKind::Proj(name, idx, Arc::new(e)))
    }
    fn mdata(tag: u32, e: Expr) -> Self {
        Expr::from_kind(ExprKind::MData(tag, Arc::new(e)))
    }

    fn lift_at(&self, start: u32, amount: u32) -> Expr {
        if amount == 0 {
            return self.clone();
        }
        if start >= self.loose_bvar_range() {
            return self.clone();
        }
        match &self.kind {
            ExprKind::BVar(idx) => {
                if *idx >= start {
                    Expr::bvar(idx.saturating_add(amount))
                } else {
                    self.clone()
                }
            }
            ExprKind::App(f, a) => Expr::app(f.lift_at(start, amount), a.lift_at(start, amount)),
            ExprKind::Lam(bd, ty, body) => Expr::lam(
                *bd,
                ty.lift_at(start, amount),
                body.lift_at(start.saturating_add(1), amount),
            ),
            ExprKind::Pi(bd, ty, body) => Expr::pi(
                *bd,
                ty.lift_at(start, amount),
                body.lift_at(start.saturating_add(1), amount),
            ),
            _ => self.clone(),
        }
    }
    fn lift_from(&self, start: u32, amount: u32) -> Expr {
        self.lift_at(start, amount)
    }
    fn instantiate(&self, val: &Expr) -> Expr {
        self.instantiate_at(val, 0)
    }
    fn instantiate_at(&self, val: &Expr, depth: u32) -> Expr {
        if depth >= self.loose_bvar_range() {
            return self.clone();
        }
        match &self.kind {
            ExprKind::BVar(idx) => {
                if *idx == depth {
                    val.lift_at(0, depth)
                } else if *idx > depth {
                    Expr::bvar(idx.saturating_sub(1))
                } else {
                    self.clone()
                }
            }
            ExprKind::App(f, a) => {
                Expr::app(f.instantiate_at(val, depth), a.instantiate_at(val, depth))
            }
            ExprKind::Lam(bd, ty, body) => Expr::lam(
                *bd,
                ty.instantiate_at(val, depth),
                body.instantiate_at(val, depth.saturating_add(1)),
            ),
            ExprKind::Pi(bd, ty, body) => Expr::pi(
                *bd,
                ty.instantiate_at(val, depth),
                body.instantiate_at(val, depth.saturating_add(1)),
            ),
            ExprKind::Let(name, ty, val_e, body, nondep) => Expr::lett(
                *name,
                ty.instantiate_at(val, depth),
                val_e.instantiate_at(val, depth),
                body.instantiate_at(val, depth.saturating_add(1)),
                *nondep,
            ),
            ExprKind::Proj(name, idx, e) => Expr::proj(*name, *idx, e.instantiate_at(val, depth)),
            _ => self.clone(),
        }
    }
    fn get_app_fn(&self) -> Expr {
        let mut current = self.clone();
        loop {
            let next = match &current.kind {
                ExprKind::App(f, _) => f.as_ref().clone(),
                _ => return current,
            };
            current = next;
        }
    }
    fn get_app_args(&self) -> Vec<Expr> {
        let mut args: Vec<Expr> = Vec::new();
        let mut current = self.clone();
        while let ExprKind::App(f, a) = &current.kind {
            args.push(a.as_ref().clone());
            let next = f.as_ref().clone();
            current = next;
        }
        args.reverse();
        args
    }
}

pub struct Verifier<'env> {
    env: &'env [(Name, Option<Expr>)],
    ctors: &'env [(Name, u32)],
}

#[derive(Clone, Debug)]
pub enum TypeError {
    UnboundVariable(u32),
    UnknownConst(Name),
    TypeMismatch {
        expected: Arc<Expr>,
        inferred: Arc<Expr>,
    },
    NotAPi {
        ty: Arc<Expr>,
    },
    ExpectedSort {
        ty: Arc<Expr>,
    },
    SortDepthExceeded {
        depth: u32,
    },
    Unsupported,
}

impl<'env> Verifier<'env> {
    fn unfold_const(&self, name: &Name) -> Option<Expr> {
        let mut i: usize = 0;
        let n = self.env.len();
        while i < n {
            let entry = &self.env[i];
            if entry.0 == *name {
                return entry.1.clone();
            }
            i += 1;
        }
        None
    }
    fn get_constructor_num_params(&self, name: &Name) -> Option<u32> {
        let mut i: usize = 0;
        let n = self.ctors.len();
        while i < n {
            let entry = &self.ctors[i];
            if entry.0 == *name {
                return Some(entry.1);
            }
            i += 1;
        }
        None
    }
    fn const_type(&self, name: &Name) -> Option<Expr> {
        match self.unfold_const(name) {
            Some(val) => match self.infer_type(&val) {
                Ok(ty) => Some(ty),
                Err(_) => None,
            },
            None => None,
        }
    }
    fn try_iota_reduction(&self, _e: &Expr) -> Option<Expr> {
        None
    }
    fn try_quot_reduction(&self, _e: &Expr) -> Option<Expr> {
        None
    }

    fn whnf_impl(&self, e: &Expr) -> Expr {
        self.whnf_inner(e)
    }
    fn whnf_inner(&self, e: &Expr) -> Expr {
        match &e.kind {
            ExprKind::App(f, a) => {
                let f_whnf = self.whnf_impl(f);
                match &f_whnf.kind {
                    ExprKind::Lam(_, _, body) => {
                        let reduced = body.instantiate(a);
                        self.whnf_impl(&reduced)
                    }
                    _ => {
                        let app = Expr::from_kind(ExprKind::App(Arc::new(f_whnf), a.clone()));
                        if let Some(reduced) = self.try_iota_reduction(&app) {
                            return self.whnf_impl(&reduced);
                        }
                        if let Some(reduced) = self.try_quot_reduction(&app) {
                            return self.whnf_impl(&reduced);
                        }
                        app
                    }
                }
            }
            ExprKind::Let(_, _, val, body, _) => {
                let reduced = body.instantiate(val);
                self.whnf_impl(&reduced)
            }
            ExprKind::Const(name, _levels) => match self.unfold_const(name) {
                Some(val) => self.whnf_impl(&val),
                None => e.clone(),
            },
            ExprKind::Proj(struct_name, idx, expr) => self.reduce_proj(struct_name, *idx, expr),
            ExprKind::MData(_, inner) => self.whnf_impl(inner),
            _ => e.clone(),
        }
    }
    fn reduce_proj(&self, struct_name: &Name, idx: u32, expr: &Expr) -> Expr {
        let expr_whnf = self.whnf_impl(expr);
        let head = expr_whnf.get_app_fn();
        if let ExprKind::Const(ctor_name, _) = &head.kind {
            if let Some(num_params) = self.get_constructor_num_params(ctor_name) {
                let args = expr_whnf.get_app_args();
                let field_idx = num_params as usize + idx as usize;
                if field_idx < args.len() {
                    return self.whnf_impl(&args[field_idx]);
                }
            }
        }
        Expr::from_kind(ExprKind::Proj(*struct_name, idx, Arc::new(expr_whnf)))
    }

    fn level_eq(&self, l1: &Level, l2: &Level) -> bool {
        Level::is_def_eq(l1, l2)
    }
    fn level_vec_eq(&self, ls1: &[Level], ls2: &[Level]) -> bool {
        if ls1.len() != ls2.len() {
            return false;
        }
        let mut i: usize = 0;
        let n = ls1.len();
        while i < n {
            if !self.level_eq(&ls1[i], &ls2[i]) {
                return false;
            }
            i += 1;
        }
        true
    }
    fn structural_eq(&self, a: &Expr, b: &Expr) -> bool {
        match (&a.kind, &b.kind) {
            (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
            (ExprKind::FVar(i), ExprKind::FVar(j)) => i == j,
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => self.level_eq(l1, l2),
            (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => {
                n1 == n2 && self.level_vec_eq(ls1, ls2)
            }
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                self.structural_eq(f1, f2) && self.structural_eq(a1, a2)
            }
            (ExprKind::Lam(_b1, ty1, b1), ExprKind::Lam(_b2, ty2, b2))
            | (ExprKind::Pi(_b1, ty1, b1), ExprKind::Pi(_b2, ty2, b2)) => {
                self.structural_eq(ty1, ty2) && self.structural_eq(b1, b2)
            }
            (ExprKind::Let(_, ty1, v1, b1, _), ExprKind::Let(_, ty2, v2, b2, _)) => {
                self.structural_eq(ty1, ty2)
                    && self.structural_eq(v1, v2)
                    && self.structural_eq(b1, b2)
            }
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
                n1 == n2 && i1 == i2 && self.structural_eq(e1, e2)
            }
            (ExprKind::MData(_, in1), ExprKind::MData(_, in2)) => self.structural_eq(in1, in2),
            _ => false,
        }
    }
    fn is_def_eq(&self, a: &Expr, b: &Expr) -> bool {
        self.def_eq_inner(a, b)
    }
    fn def_eq_impl(&self, a: &Expr, b: &Expr) -> bool {
        self.def_eq_inner(a, b)
    }
    fn def_eq_inner(&self, a: &Expr, b: &Expr) -> bool {
        let a_whnf = self.whnf_impl(a);
        let b_whnf = self.whnf_impl(b);
        if a_whnf.meta.raw() == b_whnf.meta.raw() && self.structural_eq(&a_whnf, &b_whnf) {
            return true;
        }
        let matched = match (&a_whnf.kind, &b_whnf.kind) {
            (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
            (ExprKind::FVar(i), ExprKind::FVar(j)) => i == j,
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => self.level_eq(l1, l2),
            (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => {
                n1 == n2 && self.level_vec_eq(ls1, ls2)
            }
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                self.def_eq_impl(f1, f2) && self.def_eq_impl(a1, a2)
            }
            (ExprKind::Lam(_b1, ty1, b1), ExprKind::Lam(_b2, ty2, b2))
            | (ExprKind::Pi(_b1, ty1, b1), ExprKind::Pi(_b2, ty2, b2)) => {
                self.def_eq_impl(ty1, ty2) && self.def_eq_impl(b1, b2)
            }
            (ExprKind::Let(_, ty1, v1, b1, _), ExprKind::Let(_, ty2, v2, b2, _)) => {
                self.def_eq_impl(ty1, ty2) && self.def_eq_impl(v1, v2) && self.def_eq_impl(b1, b2)
            }
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
                n1 == n2 && i1 == i2 && self.def_eq_impl(e1, e2)
            }
            (ExprKind::MData(_, in1), ExprKind::MData(_, in2)) => self.def_eq_impl(in1, in2),
            _ => false,
        };
        if matched {
            return true;
        }
        self.try_eta_expansion(&a_whnf, &b_whnf)
    }
    fn try_eta_expansion(&self, a: &Expr, b: &Expr) -> bool {
        match (&a.kind, &b.kind) {
            (ExprKind::Lam(_, _ty, body), _) => {
                let other_lifted = b.lift_from(0, 1);
                let other_applied = Expr::app(other_lifted, Expr::bvar(0));
                self.def_eq_impl(body, &other_applied)
            }
            (_, ExprKind::Lam(_, _ty, body)) => {
                let other_lifted = a.lift_from(0, 1);
                let other_applied = Expr::app(other_lifted, Expr::bvar(0));
                self.def_eq_impl(body, &other_applied)
            }
            _ => false,
        }
    }

    fn infer_type(&self, e: &Expr) -> Result<Expr, TypeError> {
        let mut ctx: Vec<Expr> = Vec::new();
        self.infer_type_core(e, &mut ctx)
    }

    fn infer_type_core(&self, e: &Expr, ctx: &mut Vec<Expr>) -> Result<Expr, TypeError> {
        match &e.kind {
            ExprKind::Sort(l) => Ok(Expr::sort(Level::succ(l.clone()))),
            ExprKind::BVar(idx) => {
                let depth = ctx.len();
                if (*idx as usize) >= depth {
                    return Err(TypeError::UnboundVariable(*idx));
                }
                let pos = depth - 1 - (*idx as usize);
                let raw = ctx[pos].clone();
                Ok(raw.lift_at(0, idx.saturating_add(1)))
            }
            ExprKind::Const(name, _levels) => match self.const_type(name) {
                Some(ty) => Ok(ty),
                None => Err(TypeError::UnknownConst(*name)),
            },
            ExprKind::App(f, a) => {
                let f_type = self.infer_type_core(f, ctx)?;
                let f_type_whnf = self.whnf_impl(&f_type);
                match &f_type_whnf.kind {
                    ExprKind::Pi(_, expected_arg_type, result_type) => {
                        let arg_type = self.infer_type_core(a, ctx)?;
                        if !self.is_def_eq(&arg_type, expected_arg_type) {
                            return Err(TypeError::TypeMismatch {
                                expected: Arc::new(expected_arg_type.as_ref().clone()),
                                inferred: Arc::new(arg_type),
                            });
                        }
                        Ok(result_type.instantiate(a))
                    }
                    _ => Err(TypeError::NotAPi {
                        ty: Arc::new(f_type),
                    }),
                }
            }
            ExprKind::Lam(bi, arg_type, body) => {
                let arg_sort = self.infer_type_core(arg_type, ctx)?;
                let arg_sort_whnf = self.whnf_impl(&arg_sort);
                match &arg_sort_whnf.kind {
                    ExprKind::Sort(_) => {}
                    _ => {
                        return Err(TypeError::ExpectedSort {
                            ty: Arc::new(arg_sort),
                        });
                    }
                }
                ctx.push(arg_type.as_ref().clone());
                let body_type = self.infer_type_core(body, ctx);
                ctx.pop();
                let body_type = body_type?;
                Ok(Expr::pi(*bi, arg_type.as_ref().clone(), body_type))
            }
            ExprKind::Pi(_bi, arg_type, body) => {
                let arg_sort = self.infer_type_core(arg_type, ctx)?;
                let arg_sort_whnf = self.whnf_impl(&arg_sort);
                let l1 = match &arg_sort_whnf.kind {
                    ExprKind::Sort(l) => l.clone(),
                    _ => {
                        return Err(TypeError::ExpectedSort {
                            ty: Arc::new(arg_sort),
                        });
                    }
                };
                ctx.push(arg_type.as_ref().clone());
                let body_sort = self.infer_type_core(body, ctx);
                ctx.pop();
                let body_sort = body_sort?;
                let body_sort_whnf = self.whnf_impl(&body_sort);
                let l2 = match &body_sort_whnf.kind {
                    ExprKind::Sort(l) => l.clone(),
                    _ => {
                        return Err(TypeError::ExpectedSort {
                            ty: Arc::new(body_sort),
                        });
                    }
                };
                Ok(Expr::sort(Level::imax(l1, l2)))
            }
            ExprKind::Let(_name, ty, val, body, _nondep) => {
                let ty_sort = self.infer_type_core(ty, ctx)?;
                let ty_sort_whnf = self.whnf_impl(&ty_sort);
                match &ty_sort_whnf.kind {
                    ExprKind::Sort(_) => {}
                    _ => {
                        return Err(TypeError::ExpectedSort {
                            ty: Arc::new(ty_sort),
                        });
                    }
                }
                let val_type = self.infer_type_core(val, ctx)?;
                if !self.is_def_eq(&val_type, ty) {
                    return Err(TypeError::TypeMismatch {
                        expected: Arc::new(ty.as_ref().clone()),
                        inferred: Arc::new(val_type),
                    });
                }
                ctx.push(ty.as_ref().clone());
                let body_type = self.infer_type_core(body, ctx);
                ctx.pop();
                let body_type = body_type?;
                Ok(body_type.instantiate(val))
            }
            ExprKind::Lit(lit) => Ok(match lit {
                Literal::Nat(_) => Expr::cnst(Name(0xFFFF_0001)),
                Literal::Str(_) => Expr::cnst(Name(0xFFFF_0002)),
            }),
            ExprKind::MData(_, inner) => self.infer_type_core(inner, ctx),
            _ => Err(TypeError::Unsupported),
        }
    }

    const INFER_SORT_MAX_DEPTH: u32 = 64;

    fn infer_sort(&self, e: &Expr) -> Result<Level, TypeError> {
        let mut ctx: Vec<Expr> = Vec::new();
        self.infer_sort_inner(e, 0, &mut ctx)
    }

    fn infer_sort_inner(
        &self,
        e: &Expr,
        depth: u32,
        ctx: &mut Vec<Expr>,
    ) -> Result<Level, TypeError> {
        let ty = self.infer_type_core(e, ctx)?;
        let ty_whnf = self.whnf_impl(&ty);
        match &ty_whnf.kind {
            ExprKind::Sort(l) => Ok(l.clone()),
            ExprKind::Pi(_bd, arg_type, body) => {
                if depth >= Self::INFER_SORT_MAX_DEPTH {
                    return Err(TypeError::SortDepthExceeded { depth });
                }
                let arg_level = self.infer_sort_inner(arg_type, depth + 1, ctx)?;
                ctx.push(arg_type.as_ref().clone());
                let body_level_result = self.infer_sort_inner(body, depth + 1, ctx);
                ctx.pop();
                let body_level = body_level_result?;
                Ok(Level::imax(arg_level, body_level))
            }
            _ => Err(TypeError::ExpectedSort { ty: Arc::new(ty) }),
        }
    }

    fn check_type(&self, e: &Expr, expected: &Expr) -> Result<(), TypeError> {
        let inferred = self.infer_type(e)?;
        if self.is_def_eq(&inferred, expected) {
            Ok(())
        } else {
            Err(TypeError::TypeMismatch {
                expected: Arc::new(expected.clone()),
                inferred: Arc::new(inferred),
            })
        }
    }
}

#[derive(Clone, Debug)]
pub enum Declaration {
    Definition {
        name: Name,
        level_params: Vec<Name>,
        type_: Arc<Expr>,
        value: Arc<Expr>,
        is_reducible: bool,
    },
    Axiom {
        name: Name,
        level_params: Vec<Name>,
        type_: Arc<Expr>,
    },
    Theorem {
        name: Name,
        level_params: Vec<Name>,
        type_: Arc<Expr>,
        value: Arc<Expr>,
    },
    Opaque {
        name: Name,
        level_params: Vec<Name>,
        type_: Arc<Expr>,
        value: Arc<Expr>,
    },
}

#[derive(Clone, Debug)]
pub enum EnvError {
    TypeCheckFailed { name: Name, source: TypeError },
    DuplicateLevelParam { name: Name, param: Name },
    TheoremTypeNotProp { name: Name, sort: Level },
    ContainsFreeVar { name: Name },
    ContainsMetavar { name: Name },
    UndefinedLevelParam { name: Name, param: Name },
}

fn find_undef_level_param_in_level(l: &Level, allowed: &[Name]) -> Option<Name> {
    let mut level_stack: Vec<&Level> = vec![l];
    while let Some(curr) = level_stack.pop() {
        match curr {
            Level::Zero => {}
            Level::Param(n) => {
                let mut found = false;
                let mut k: usize = 0;
                while k < allowed.len() {
                    if allowed[k] == *n {
                        found = true;
                        break;
                    }
                    k += 1;
                }
                if !found {
                    return Some(*n);
                }
            }
            Level::Succ(inner) => level_stack.push(inner),
            Level::Max(a, b) | Level::IMax(a, b) => {
                level_stack.push(b);
                level_stack.push(a);
            }
        }
    }
    None
}

fn find_undef_level_param(e: &Expr, allowed: &[Name]) -> Option<Name> {
    let mut expr_stack: Vec<&Expr> = vec![e];
    while let Some(curr) = expr_stack.pop() {
        match curr.kind() {
            ExprKind::Sort(l) => {
                if let Some(undef) = find_undef_level_param_in_level(l, allowed) {
                    return Some(undef);
                }
            }
            ExprKind::Const(_, levels) => {
                let mut li: usize = 0;
                while li < levels.len() {
                    if let Some(undef) = find_undef_level_param_in_level(&levels[li], allowed) {
                        return Some(undef);
                    }
                    li += 1;
                }
            }
            ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Lit(_) => {}
            ExprKind::App(f, a) => {
                expr_stack.push(a);
                expr_stack.push(f);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                expr_stack.push(body);
                expr_stack.push(ty);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                expr_stack.push(body);
                expr_stack.push(val);
                expr_stack.push(ty);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
                expr_stack.push(inner);
            }
        }
    }
    None
}

impl<'env> Verifier<'env> {
    pub fn check_decl_readonly(&self, decl: &Declaration) -> Result<(), EnvError> {
        let (name, level_params, type_, opt_value, is_theorem): (
            &Name,
            &Vec<Name>,
            &Arc<Expr>,
            Option<&Arc<Expr>>,
            bool,
        ) = match decl {
            Declaration::Definition {
                name,
                level_params,
                type_,
                value,
                ..
            } => (name, level_params, type_, Some(value), false),
            Declaration::Axiom {
                name,
                level_params,
                type_,
            } => (name, level_params, type_, None, false),
            Declaration::Theorem {
                name,
                level_params,
                type_,
                value,
            } => (name, level_params, type_, Some(value), true),
            Declaration::Opaque {
                name,
                level_params,
                type_,
                value,
            } => (name, level_params, type_, Some(value), false),
        };

        {
            let n = level_params.len();
            let mut i: usize = 0;
            while i < n {
                let mut j: usize = 0;
                while j < i {
                    if level_params[j] == level_params[i] {
                        return Err(EnvError::DuplicateLevelParam {
                            name: *name,
                            param: level_params[i],
                        });
                    }
                    j += 1;
                }
                i += 1;
            }
        }

        if type_.has_expr_mvar_quick() || type_.has_level_mvar_quick() {
            return Err(EnvError::ContainsMetavar { name: *name });
        }
        if type_.has_fvar_quick() {
            return Err(EnvError::ContainsFreeVar { name: *name });
        }
        if let Some(value) = opt_value {
            if value.has_expr_mvar_quick() || value.has_level_mvar_quick() {
                return Err(EnvError::ContainsMetavar { name: *name });
            }
            if value.has_fvar_quick() {
                return Err(EnvError::ContainsFreeVar { name: *name });
            }
        }

        if let Some(undef) = find_undef_level_param(type_, level_params) {
            return Err(EnvError::UndefinedLevelParam {
                name: *name,
                param: undef,
            });
        }
        if let Some(value) = opt_value {
            if let Some(undef) = find_undef_level_param(value, level_params) {
                return Err(EnvError::UndefinedLevelParam {
                    name: *name,
                    param: undef,
                });
            }
        }

        let sort = match self.infer_sort(type_) {
            Ok(s) => s,
            Err(e) => {
                return Err(EnvError::TypeCheckFailed {
                    name: *name,
                    source: e,
                });
            }
        };

        if is_theorem && !sort.is_zero() {
            return Err(EnvError::TheoremTypeNotProp { name: *name, sort });
        }

        if let Some(value) = opt_value {
            match self.check_type(value, type_) {
                Ok(()) => {}
                Err(e) => {
                    return Err(EnvError::TypeCheckFailed {
                        name: *name,
                        source: e,
                    });
                }
            }
        }

        Ok(())
    }
}

// ════════════════════════════════════════════════════════════════════════════
// EXTERN SHIMS (prefix du_shim_) — faithful native leaves bound by mangled
// symbol. Arc/Vec allocations LEAK (no matching dealloc registered on the hot
// path) — accepted for this one-shot JIT verification, same as prior rungs.
// ════════════════════════════════════════════════════════════════════════════

extern "C" fn du_shim_rust_alloc(size: usize, align: usize) -> *mut u8 {
    unsafe {
        let layout = std::alloc::Layout::from_size_align(size, align).expect("valid layout");
        std::alloc::alloc(layout)
    }
}
extern "C" fn du_shim_rust_dealloc(ptr: *mut u8, size: usize, align: usize) {
    unsafe {
        let layout = std::alloc::Layout::from_size_align(size, align).expect("valid layout");
        std::alloc::dealloc(ptr, layout);
    }
}
extern "C" fn du_shim_rust_realloc(
    ptr: *mut u8,
    size: usize,
    align: usize,
    new_size: usize,
) -> *mut u8 {
    unsafe {
        let layout = std::alloc::Layout::from_size_align(size, align).expect("valid layout");
        std::alloc::realloc(ptr, layout, new_size)
    }
}

// num / cmp primitives.
extern "C" fn du_shim_sat_add(a: u32, b: u32) -> u32 {
    a.saturating_add(b)
}
extern "C" fn du_shim_sat_sub(a: u32, b: u32) -> u32 {
    a.saturating_sub(b)
}
extern "C" fn du_shim_wrap_mul(a: u64, b: u64) -> u64 {
    a.wrapping_mul(b)
}
extern "C" fn du_shim_max_u8(a: u8, b: u8) -> u8 {
    a.max(b)
}
extern "C" fn du_shim_max_u32(a: u32, b: u32) -> u32 {
    a.max(b)
}
extern "C" fn du_shim_min_u32(a: u32, b: u32) -> u32 {
    a.min(b)
}

// ── Arc leaves ──
// Arc<T>::clone drifted ABI across the generation toolchains. Stable fixture: the
// older frontend emitted the sret form `(sret, this) -> ()`. Trust fixture: the
// current frontend emits register-return `(this) -> ptr` — Arc<T> is pointer-sized
// (8 B = NonNull<ArcInner>), so the AArch64 ABI returns it in x0, not via an sret
// out-pointer. The raw Arc value is the ArcInner base (= data_ptr - 16, matching the
// +16 in du_shim_arc_expr_as_ref); `into_raw` keeps the strong count this clone just
// incremented. The shim ABI must match whichever `.tir` is compiled.
#[cfg(kernel_fixture_layout_matches)]
extern "C" fn du_shim_arc_expr_clone(sret: *mut Arc<Expr>, this: *const Arc<Expr>) {
    unsafe {
        std::ptr::write(sret, Arc::clone(&*this));
    }
}
#[cfg(not(kernel_fixture_layout_matches))]
extern "C" fn du_shim_arc_expr_clone(this: *const Arc<Expr>) -> *const Expr {
    unsafe {
        let data = Arc::into_raw(Arc::clone(&*this)) as *const u8;
        data.sub(16) as *const Expr
    }
}
#[cfg(kernel_fixture_layout_matches)]
extern "C" fn du_shim_arc_lvl_clone(sret: *mut Arc<Level>, this: *const Arc<Level>) {
    unsafe {
        std::ptr::write(sret, Arc::clone(&*this));
    }
}
#[cfg(not(kernel_fixture_layout_matches))]
extern "C" fn du_shim_arc_lvl_clone(this: *const Arc<Level>) -> *const Level {
    unsafe {
        let data = Arc::into_raw(Arc::clone(&*this)) as *const u8;
        data.sub(16) as *const Level
    }
}
// <Arc<Expr> as AsRef<Expr>>::as_ref -> &Expr (ArcInner data @ +16).
extern "C" fn du_shim_arc_expr_as_ref(arc_ref: *const *const u8) -> *const Expr {
    unsafe { (*arc_ref).add(16) as *const Expr }
}
// <&Arc<Level> as PartialEq>::ne — compare pointee Levels (iterative eq).
extern "C" fn du_shim_arc_lvl_ne(a: *const Arc<Level>, b: *const Arc<Level>) -> bool {
    unsafe { !(*(*a) == *(*b)) }
}

// ── clones ──
extern "C" fn du_shim_opt_expr_clone(sret: *mut Option<Expr>, this: *const Option<Expr>) {
    unsafe {
        std::ptr::write(sret, (*this).clone());
    }
}
extern "C" fn du_shim_vec_lvl_clone(sret: *mut Vec<Level>, this: *const Vec<Level>) {
    unsafe {
        std::ptr::write(sret, (*this).clone());
    }
}

// ── Vec<Expr> ops ──
extern "C" fn du_shim_vec_expr_new(sret: *mut Vec<Expr>) {
    unsafe {
        std::ptr::write(sret, Vec::new());
    }
}
extern "C" fn du_shim_vec_expr_len(v: *const Vec<Expr>) -> u64 {
    unsafe { (*v).len() as u64 }
}
extern "C" fn du_shim_vec_expr_index(v: *const Vec<Expr>, idx: u64) -> *const Expr {
    unsafe {
        let s: &[Expr] = (*v).as_slice();
        assert!((idx as usize) < s.len(), "vec_expr_index oob");
        s.as_ptr().add(idx as usize)
    }
}
extern "C" fn du_shim_vec_expr_push(v: *mut Vec<Expr>, val: *const Expr) {
    unsafe {
        (*v).push(std::ptr::read(val));
    }
}
extern "C" fn du_shim_vec_expr_pop(sret: *mut Option<Expr>, v: *mut Vec<Expr>) {
    unsafe {
        std::ptr::write(sret, (*v).pop());
    }
}
extern "C" fn du_shim_vec_expr_deref_mut(sret: *mut (*mut Expr, usize), v: *mut Vec<Expr>) {
    unsafe {
        let s: &mut [Expr] = (*v).as_mut_slice();
        std::ptr::write(sret, (s.as_mut_ptr(), s.len()));
    }
}
extern "C" fn du_shim_expr_slice_reverse(slice_ref: *const (*mut Expr, usize)) {
    unsafe {
        let (ptr, len) = *slice_ref;
        let s: &mut [Expr] = std::slice::from_raw_parts_mut(ptr, len);
        s.reverse();
    }
}

// ── Vec<&Expr> ops (find_undef_level_param stack; element is &Expr, niche 8B) ──
extern "C" fn du_shim_vec_expr_ref_push(v: *mut Vec<&'static Expr>, val: *const Expr) {
    unsafe {
        (*v).push(&*val);
    }
}
// pop drifted ABI: `Option<&Expr>` is niche-optimized to a single pointer (null =
// None), so it is pointer-sized. Stable fixture: older frontend emitted sret
// `(sret, v) -> ()`. Trust fixture: register-return `(v) -> ptr` (returned in x0).
#[cfg(kernel_fixture_layout_matches)]
extern "C" fn du_shim_vec_expr_ref_pop(
    sret: *mut Option<&'static Expr>,
    v: *mut Vec<&'static Expr>,
) {
    unsafe {
        std::ptr::write(sret, (*v).pop());
    }
}
#[cfg(not(kernel_fixture_layout_matches))]
extern "C" fn du_shim_vec_expr_ref_pop(v: *mut Vec<&'static Expr>) -> *const Expr {
    unsafe {
        match (*v).pop() {
            Some(r) => r as *const Expr,
            None => std::ptr::null(),
        }
    }
}

// ── Vec<Name> ops (level_params) ──
extern "C" fn du_shim_vec_name_len(v: *const Vec<Name>) -> u64 {
    unsafe { (*v).len() as u64 }
}
extern "C" fn du_shim_vec_name_index(v: *const Vec<Name>, idx: u64) -> *const Name {
    unsafe {
        let s: &[Name] = (*v).as_slice();
        assert!((idx as usize) < s.len(), "vec_name_index oob");
        s.as_ptr().add(idx as usize)
    }
}
extern "C" fn du_shim_vec_name_deref(sret: *mut (*const Name, usize), v: *const Vec<Name>) {
    unsafe {
        let s: &[Name] = (*v).as_slice();
        std::ptr::write(sret, (s.as_ptr(), s.len()));
    }
}

// ── Vec<Level> ops (normalize machinery) ──
extern "C" fn du_shim_vec_lvl_new(sret: *mut Vec<Level>) {
    unsafe {
        std::ptr::write(sret, Vec::new());
    }
}
extern "C" fn du_shim_vec_lvl_len(v: *const Vec<Level>) -> u64 {
    unsafe { (*v).len() as u64 }
}
extern "C" fn du_shim_vec_lvl_index(v: *const Vec<Level>, idx: u64) -> *const Level {
    unsafe {
        let s: &[Level] = (*v).as_slice();
        assert!((idx as usize) < s.len(), "vec_lvl_index oob");
        s.as_ptr().add(idx as usize)
    }
}
extern "C" fn du_shim_vec_lvl_index_mut(v: *mut Vec<Level>, idx: u64) -> *mut Level {
    unsafe {
        let s: &mut [Level] = (*v).as_mut_slice();
        assert!((idx as usize) < s.len(), "vec_lvl_index_mut oob");
        s.as_mut_ptr().add(idx as usize)
    }
}
extern "C" fn du_shim_vec_lvl_deref(sret: *mut (*const Level, usize), v: *const Vec<Level>) {
    unsafe {
        let s: &[Level] = (*v).as_slice();
        std::ptr::write(sret, (s.as_ptr(), s.len()));
    }
}
extern "C" fn du_shim_vec_lvl_deref_mut(sret: *mut (*mut Level, usize), v: *mut Vec<Level>) {
    unsafe {
        let s: &mut [Level] = (*v).as_mut_slice();
        std::ptr::write(sret, (s.as_mut_ptr(), s.len()));
    }
}
extern "C" fn du_shim_vec_lvl_is_empty(v: *const Vec<Level>) -> bool {
    unsafe { (*v).is_empty() }
}
extern "C" fn du_shim_vec_lvl_push(v: *mut Vec<Level>, val: *const Level) {
    unsafe {
        (*v).push(std::ptr::read(val));
    }
}
extern "C" fn du_shim_vec_lvl_pop(sret: *mut Option<Level>, v: *mut Vec<Level>) {
    unsafe {
        std::ptr::write(sret, (*v).pop());
    }
}
extern "C" fn du_shim_lvl_slice_swap(fat: *const (*mut Level, usize), i: u64, j: u64) {
    unsafe {
        let (data, _len) = *fat;
        std::ptr::swap(data.add(i as usize), data.add(j as usize));
    }
}
extern "C" fn du_shim_lvl_slice_to_vec(sret: *mut Vec<Level>, src: *const (*const Level, usize)) {
    unsafe {
        let (p, n) = *src;
        let s = std::slice::from_raw_parts(p, n);
        std::ptr::write(sret, s.to_vec());
    }
}

// ── Vec<&Level> / Vec<(&Level,&Level)> ops (push_max_args / eq / is_geq_core
//    worklists; niche-optimized reference elements, per the verified level rung) ──
extern "C" fn du_shim_vec_lvl_ref_push(v: *mut Vec<&'static Level>, val: *const Level) {
    unsafe {
        (*v).push(&*val);
    }
}
// Same niche-pointer pop drift as du_shim_vec_expr_ref_pop (Option<&Level>).
#[cfg(kernel_fixture_layout_matches)]
extern "C" fn du_shim_vec_lvl_ref_pop(
    sret: *mut Option<&'static Level>,
    v: *mut Vec<&'static Level>,
) {
    unsafe {
        std::ptr::write(sret, (*v).pop());
    }
}
#[cfg(not(kernel_fixture_layout_matches))]
extern "C" fn du_shim_vec_lvl_ref_pop(v: *mut Vec<&'static Level>) -> *const Level {
    unsafe {
        match (*v).pop() {
            Some(r) => r as *const Level,
            None => std::ptr::null(),
        }
    }
}
extern "C" fn du_shim_vec_lvl_pair_push(
    v: *mut Vec<(&'static Level, &'static Level)>,
    val: *const (&'static Level, &'static Level),
) {
    unsafe {
        (*v).push(std::ptr::read(val));
    }
}
extern "C" fn du_shim_vec_lvl_pair_pop(
    sret: *mut Option<(&'static Level, &'static Level)>,
    v: *mut Vec<(&'static Level, &'static Level)>,
) {
    unsafe {
        std::ptr::write(sret, (*v).pop());
    }
}

// ── `?` operator leaves: real std Try/FromResidual semantics, retyped ──
extern "C" fn du_shim_result_expr_branch(
    sret: *mut std::ops::ControlFlow<Result<std::convert::Infallible, TypeError>, Expr>,
    this: *const Result<Expr, TypeError>,
) {
    unsafe {
        let cf = match std::ptr::read(this) {
            Ok(v) => std::ops::ControlFlow::Continue(v),
            Err(e) => std::ops::ControlFlow::Break(Err(e)),
        };
        std::ptr::write(sret, cf);
    }
}
extern "C" fn du_shim_result_expr_from_residual(
    sret: *mut Result<Expr, TypeError>,
    residual: *const Result<std::convert::Infallible, TypeError>,
) {
    unsafe {
        let err = match std::ptr::read(residual) {
            Ok(_) => unreachable!("Infallible residual"),
            Err(e) => e,
        };
        std::ptr::write(sret, Err(err));
    }
}
extern "C" fn du_shim_result_lvl_branch(
    sret: *mut std::ops::ControlFlow<Result<std::convert::Infallible, TypeError>, Level>,
    this: *const Result<Level, TypeError>,
) {
    unsafe {
        let cf = match std::ptr::read(this) {
            Ok(v) => std::ops::ControlFlow::Continue(v),
            Err(e) => std::ops::ControlFlow::Break(Err(e)),
        };
        std::ptr::write(sret, cf);
    }
}
extern "C" fn du_shim_result_lvl_from_residual(
    sret: *mut Result<Level, TypeError>,
    residual: *const Result<std::convert::Infallible, TypeError>,
) {
    unsafe {
        let err = match std::ptr::read(residual) {
            Ok(_) => unreachable!("Infallible residual"),
            Err(e) => e,
        };
        std::ptr::write(sret, Err(err));
    }
}
extern "C" fn du_shim_result_unit_from_residual(
    sret: *mut Result<(), TypeError>,
    residual: *const Result<std::convert::Infallible, TypeError>,
) {
    unsafe {
        let err = match std::ptr::read(residual) {
            Ok(_) => unreachable!("Infallible residual"),
            Err(e) => e,
        };
        std::ptr::write(sret, Err(err));
    }
}

// ── ref-to-ref PartialEq/PartialOrd wrappers (`core::cmp::impls`, double-ptr
//    receiver convention per the verified rungs) ──
extern "C" fn du_shim_name_ref_eq(a: *const *const Name, b: *const *const Name) -> bool {
    unsafe { (**a).0 == (**b).0 }
}
extern "C" fn du_shim_name_ref_ne(a: *const *const Name, b: *const *const Name) -> bool {
    unsafe { (**a).0 != (**b).0 }
}
extern "C" fn du_shim_name_ref_lt(a: *const *const Name, b: *const *const Name) -> bool {
    unsafe { (**a).0 < (**b).0 }
}
extern "C" fn du_shim_lvl_ref_eq(a: *const *const Level, b: *const *const Level) -> bool {
    unsafe { (**a) == (**b) }
}
extern "C" fn du_shim_lvl_ref_ne(a: *const *const Level, b: *const *const Level) -> bool {
    unsafe { (**a) != (**b) }
}
extern "C" fn du_shim_lit_ref_eq(a: *const *const Literal, b: *const *const Literal) -> bool {
    unsafe { (**a) == (**b) }
}
extern "C" fn du_shim_fvarid_ref_eq(a: *const *const FVarId, b: *const *const FVarId) -> bool {
    unsafe { (**a) == (**b) }
}
extern "C" fn du_shim_u32_ref_eq(a: *const *const u32, b: *const *const u32) -> bool {
    unsafe { (**a) == (**b) }
}

// ── KaniHasher hash leaves. KaniHasher is a single u64 state word; each shim
//    replays the exact KaniHasher write path natively. ──
const DU_KANI_MAGIC: u64 = 0x517cc1b727220a95;
extern "C" fn du_shim_hash_u32(value: *const u32, state: *mut u64) {
    unsafe {
        let i = *value as u64;
        let s = (*state) ^ i;
        *state = s.wrapping_mul(DU_KANI_MAGIC);
    }
}
extern "C" fn du_shim_hash_u64(value: *const u64, state: *mut u64) {
    unsafe {
        let i = *value;
        let s = (*state) ^ i;
        *state = s.wrapping_mul(DU_KANI_MAGIC);
    }
}
// <isize as Hash>::hash -> write_isize -> write_usize -> KaniHasher write_u64.
extern "C" fn du_shim_hash_isize(value: *const isize, state: *mut u64) {
    unsafe {
        let i = *value as u64;
        let s = (*state) ^ i;
        *state = s.wrapping_mul(DU_KANI_MAGIC);
    }
}
// core::mem::discriminant::<Level> — sret Discriminant<Level> (8 bytes).
extern "C" fn du_shim_discriminant_level(
    sret: *mut std::mem::Discriminant<Level>,
    this: *const Level,
) {
    unsafe {
        std::ptr::write(sret, std::mem::discriminant(&*this));
    }
}
// <Discriminant<Level> as Hash>::hash — replay core's impl through KaniHasher.
extern "C" fn du_shim_hash_discriminant_level(
    value: *const std::mem::Discriminant<Level>,
    state: *mut u64,
) {
    use std::hash::{Hash, Hasher};
    unsafe {
        let mut h = KaniHasher { state: *state };
        (*value).hash(&mut h);
        *state = h.finish();
    }
}
// <Arc<Level> as Hash>::hash == <Level as Hash>::hash(&**arc) — replay the full
// native Level hash (discriminant + children) seeded with the current state.
extern "C" fn du_shim_hash_arc_level(arcptr: *const Arc<Level>, state: *mut u64) {
    use std::hash::{Hash, Hasher};
    unsafe {
        let lvl: &Level = &*(*arcptr);
        let mut h = KaniHasher { state: *state };
        lvl.hash(&mut h);
        *state = h.finish();
    }
}

// ════════════════════════════════════════════════════════════════════════════
// COMPARATORS (independent of the code under test — plain tree walks).
// ════════════════════════════════════════════════════════════════════════════

/// Structural (tree-identical) Level comparison — deref's the Arc children the
/// JIT built. NOT the is_def_eq under test.
fn level_structural_eq(a: &Level, b: &Level) -> bool {
    match (a, b) {
        (Level::Zero, Level::Zero) => true,
        (Level::Succ(x), Level::Succ(y)) => level_structural_eq(x, y),
        (Level::Max(a1, b1), Level::Max(a2, b2)) => {
            level_structural_eq(a1, a2) && level_structural_eq(b1, b2)
        }
        (Level::IMax(a1, b1), Level::IMax(a2, b2)) => {
            level_structural_eq(a1, a2) && level_structural_eq(b1, b2)
        }
        (Level::Param(n1), Level::Param(n2)) => n1 == n2,
        _ => false,
    }
}

/// Deep structural equality with the ExprMeta word BIT-IDENTICAL at every node.
fn deep_eq(a: &Expr, b: &Expr) -> bool {
    if a.meta.raw() != b.meta.raw() {
        return false;
    }
    match (&a.kind, &b.kind) {
        (ExprKind::BVar(x), ExprKind::BVar(y)) => x == y,
        (ExprKind::FVar(x), ExprKind::FVar(y)) => x == y,
        (ExprKind::Lit(x), ExprKind::Lit(y)) => x == y,
        (ExprKind::Sort(x), ExprKind::Sort(y)) => level_structural_eq(x, y),
        (ExprKind::Const(n1, l1), ExprKind::Const(n2, l2)) => {
            n1 == n2
                && l1.len() == l2.len()
                && l1
                    .iter()
                    .zip(l2.iter())
                    .all(|(x, y)| level_structural_eq(x, y))
        }
        (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => deep_eq(f1, f2) && deep_eq(a1, a2),
        (ExprKind::Lam(b1, t1, y1), ExprKind::Lam(b2, t2, y2)) => {
            b1 == b2 && deep_eq(t1, t2) && deep_eq(y1, y2)
        }
        (ExprKind::Pi(b1, t1, y1), ExprKind::Pi(b2, t2, y2)) => {
            b1 == b2 && deep_eq(t1, t2) && deep_eq(y1, y2)
        }
        (ExprKind::Let(n1, t1, v1, y1, d1), ExprKind::Let(n2, t2, v2, y2, d2)) => {
            n1 == n2 && deep_eq(t1, t2) && deep_eq(v1, v2) && deep_eq(y1, y2) && d1 == d2
        }
        (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
            n1 == n2 && i1 == i2 && deep_eq(e1, e2)
        }
        (ExprKind::MData(m1, e1), ExprKind::MData(m2, e2)) => m1 == m2 && deep_eq(e1, e2),
        _ => false,
    }
}

fn type_error_disc(e: &TypeError) -> u8 {
    match e {
        TypeError::UnboundVariable(_) => 0,
        TypeError::UnknownConst(_) => 1,
        TypeError::TypeMismatch { .. } => 2,
        TypeError::NotAPi { .. } => 3,
        TypeError::ExpectedSort { .. } => 4,
        TypeError::SortDepthExceeded { .. } => 5,
        TypeError::Unsupported => 6,
    }
}

fn env_error_disc(e: &EnvError) -> u8 {
    match e {
        EnvError::TypeCheckFailed { .. } => 0,
        EnvError::DuplicateLevelParam { .. } => 1,
        EnvError::TheoremTypeNotProp { .. } => 2,
        EnvError::ContainsFreeVar { .. } => 3,
        EnvError::ContainsMetavar { .. } => 4,
        EnvError::UndefinedLevelParam { .. } => 5,
    }
}

/// Payload-deep agreement between two gate errors: variant + names + params +
/// (for TheoremTypeNotProp) the STRUCTURAL universe payload + (for
/// TypeCheckFailed) the TypeError variant, with TypeMismatch expr payloads
/// deep-compared meta-bit-identically.
fn env_error_agrees(n: &EnvError, j: &EnvError) -> bool {
    match (n, j) {
        (
            EnvError::TypeCheckFailed {
                name: n1,
                source: s1,
            },
            EnvError::TypeCheckFailed {
                name: n2,
                source: s2,
            },
        ) => {
            n1 == n2
                && type_error_disc(s1) == type_error_disc(s2)
                && match (s1, s2) {
                    (
                        TypeError::TypeMismatch {
                            expected: e1,
                            inferred: i1,
                        },
                        TypeError::TypeMismatch {
                            expected: e2,
                            inferred: i2,
                        },
                    ) => deep_eq(e1, e2) && deep_eq(i1, i2),
                    _ => true,
                }
        }
        (
            EnvError::DuplicateLevelParam {
                name: n1,
                param: p1,
            },
            EnvError::DuplicateLevelParam {
                name: n2,
                param: p2,
            },
        ) => n1 == n2 && p1 == p2,
        (
            EnvError::TheoremTypeNotProp { name: n1, sort: s1 },
            EnvError::TheoremTypeNotProp { name: n2, sort: s2 },
        ) => n1 == n2 && level_structural_eq(s1, s2),
        (EnvError::ContainsFreeVar { name: n1 }, EnvError::ContainsFreeVar { name: n2 }) => {
            n1 == n2
        }
        (EnvError::ContainsMetavar { name: n1 }, EnvError::ContainsMetavar { name: n2 }) => {
            n1 == n2
        }
        (
            EnvError::UndefinedLevelParam {
                name: n1,
                param: p1,
            },
            EnvError::UndefinedLevelParam {
                name: n2,
                param: p2,
            },
        ) => n1 == n2 && p1 == p2,
        _ => false,
    }
}

// ABI of the MIR-emitted check_decl_readonly: (sret Result<(),EnvError>, &self, &decl).
type DeclCheckFn = extern "C" fn(*mut Result<(), EnvError>, *const Verifier, *const Declaration);

fn build_externs() -> HashMap<String, *const u8> {
    let mut externs: HashMap<String, *const u8> = HashMap::new();
    let mut ins = |sym: &str, f: *const u8| {
        externs.insert(sym.to_string(), f);
    };
    // allocator hooks (heap_alloc rust_heap).
    ins("__rust_alloc", du_shim_rust_alloc as *const u8);
    ins("__rust_dealloc", du_shim_rust_dealloc as *const u8);
    ins("__rust_realloc", du_shim_rust_realloc as *const u8);
    // num / cmp.
    ins(
        "_RNvMs6_NtCs2EYQwhfuABO_4core3numm14saturating_add",
        du_shim_sat_add as *const u8,
    );
    ins(
        "_RNvMs6_NtCs2EYQwhfuABO_4core3numm14saturating_sub",
        du_shim_sat_sub as *const u8,
    );
    ins(
        "_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_mul",
        du_shim_wrap_mul as *const u8,
    );
    ins(
        "_RNvYhNtNtCs2EYQwhfuABO_4core3cmp3Ord3maxCshhXhIKvfvMU_25clean_decl_universe_slice",
        du_shim_max_u8 as *const u8,
    );
    ins(
        "_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3maxCshhXhIKvfvMU_25clean_decl_universe_slice",
        du_shim_max_u32 as *const u8,
    );
    ins(
        "_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3minCshhXhIKvfvMU_25clean_decl_universe_slice",
        du_shim_min_u32 as *const u8,
    );
    // Arc.
    ins(
        "_RNvXsu_NtCskTzINo8ZBH9_5alloc4syncINtB5_3ArcNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprENtNtCs2EYQwhfuABO_4core5clone5Clone5cloneBI_",
        du_shim_arc_expr_clone as *const u8,
    );
    ins(
        "_RNvXsu_NtCskTzINo8ZBH9_5alloc4syncINtB5_3ArcNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelENtNtCs2EYQwhfuABO_4core5clone5Clone5cloneBI_",
        du_shim_arc_lvl_clone as *const u8,
    );
    ins(
        "_RNvXs1j_NtCskTzINo8ZBH9_5alloc4syncINtB6_3ArcNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprEINtNtCs2EYQwhfuABO_4core7convert5AsRefBH_E6as_refBJ_",
        du_shim_arc_expr_as_ref as *const u8,
    );
    ins(
        "_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRINtNtCskTzINo8ZBH9_5alloc4sync3ArcNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelENtB7_9PartialEq2neB1d_",
        du_shim_arc_lvl_ne as *const u8,
    );
    // clones.
    ins(
        "_RNvXs4_NtCs2EYQwhfuABO_4core6optionINtB5_6OptionNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprENtNtB7_5clone5Clone5cloneBM_",
        du_shim_opt_expr_clone as *const u8,
    );
    ins(
        "_RNvXsa_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelENtNtCs2EYQwhfuABO_4core5clone5Clone5cloneBH_",
        du_shim_vec_lvl_clone as *const u8,
    );
    // Vec<Expr>.
    ins(
        "_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprE3newBE_",
        du_shim_vec_expr_new as *const u8,
    );
    ins(
        "_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprE3lenBG_",
        du_shim_vec_expr_len as *const u8,
    );
    ins(
        "_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_",
        du_shim_vec_expr_index as *const u8,
    );
    ins(
        "_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprE4pushBH_",
        du_shim_vec_expr_push as *const u8,
    );
    ins(
        "_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprE3popBG_",
        du_shim_vec_expr_pop as *const u8,
    );
    ins(
        "_RNvXs8_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprENtNtNtCs2EYQwhfuABO_4core3ops5deref8DerefMut9deref_mutBH_",
        du_shim_vec_expr_deref_mut as *const u8,
    );
    ins(
        "_RNvMNtCs2EYQwhfuABO_4core5sliceSNtCshhXhIKvfvMU_25clean_decl_universe_slice4Expr7reverseBw_",
        du_shim_expr_slice_reverse as *const u8,
    );
    // Vec<&Expr>.
    ins(
        "_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecRNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprE4pushBI_",
        du_shim_vec_expr_ref_push as *const u8,
    );
    ins(
        "_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecRNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprE3popBH_",
        du_shim_vec_expr_ref_pop as *const u8,
    );
    // Vec<Name>.
    ins(
        "_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4NameE3lenBG_",
        du_shim_vec_name_len as *const u8,
    );
    ins(
        "_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4NameEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_",
        du_shim_vec_name_index as *const u8,
    );
    ins(
        "_RNvXs7_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice4NameENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefBH_",
        du_shim_vec_name_deref as *const u8,
    );
    // Vec<Level>.
    ins(
        "_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE3newBE_",
        du_shim_vec_lvl_new as *const u8,
    );
    ins(
        "_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE3lenBG_",
        du_shim_vec_lvl_len as *const u8,
    );
    ins(
        "_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_",
        du_shim_vec_lvl_index as *const u8,
    );
    ins(
        "_RNvXsd_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelEINtNtNtCs2EYQwhfuABO_4core3ops5index8IndexMutjE9index_mutBH_",
        du_shim_vec_lvl_index_mut as *const u8,
    );
    ins(
        "_RNvXs7_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefBH_",
        du_shim_vec_lvl_deref as *const u8,
    );
    ins(
        "_RNvXs8_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelENtNtNtCs2EYQwhfuABO_4core3ops5deref8DerefMut9deref_mutBH_",
        du_shim_vec_lvl_deref_mut as *const u8,
    );
    ins(
        "_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE8is_emptyBG_",
        du_shim_vec_lvl_is_empty as *const u8,
    );
    ins(
        "_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE4pushBH_",
        du_shim_vec_lvl_push as *const u8,
    );
    ins(
        "_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE3popBG_",
        du_shim_vec_lvl_pop as *const u8,
    );
    ins(
        "_RNvMNtCs2EYQwhfuABO_4core5sliceSNtCshhXhIKvfvMU_25clean_decl_universe_slice5Level4swapBw_",
        du_shim_lvl_slice_swap as *const u8,
    );
    ins(
        "_RNvMNtCskTzINo8ZBH9_5alloc5sliceSNtCshhXhIKvfvMU_25clean_decl_universe_slice5Level6to_vecBx_",
        du_shim_lvl_slice_to_vec as *const u8,
    );
    // Vec<&Level> / Vec<(&Level,&Level)>.
    ins(
        "_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecRNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE4pushBI_",
        du_shim_vec_lvl_ref_push as *const u8,
    );
    ins(
        "_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecRNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelE3popBH_",
        du_shim_vec_lvl_ref_pop as *const u8,
    );
    ins(
        "_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecTRNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelBG_EE4pushBJ_",
        du_shim_vec_lvl_pair_push as *const u8,
    );
    ins(
        "_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecTRNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelBF_EE3popBI_",
        du_shim_vec_lvl_pair_pop as *const u8,
    );
    // Result Try / FromResidual.
    ins(
        "_RNvXsp_NtCs2EYQwhfuABO_4core6resultINtB5_6ResultNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprNtBM_9TypeErrorENtNtNtB7_3ops9try_trait3Try6branchBM_",
        du_shim_result_expr_branch as *const u8,
    );
    ins(
        "_RNvXsq_NtCs2EYQwhfuABO_4core6resultINtB5_6ResultNtCshhXhIKvfvMU_25clean_decl_universe_slice4ExprNtBM_9TypeErrorEINtNtNtB7_3ops9try_trait12FromResidualIBy_NtNtB7_7convert10InfallibleB1w_EE13from_residualBM_",
        du_shim_result_expr_from_residual as *const u8,
    );
    ins(
        "_RNvXsp_NtCs2EYQwhfuABO_4core6resultINtB5_6ResultNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelNtBM_9TypeErrorENtNtNtB7_3ops9try_trait3Try6branchBM_",
        du_shim_result_lvl_branch as *const u8,
    );
    ins(
        "_RNvXsq_NtCs2EYQwhfuABO_4core6resultINtB5_6ResultNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelNtBM_9TypeErrorEINtNtNtB7_3ops9try_trait12FromResidualIBy_NtNtB7_7convert10InfallibleB1x_EE13from_residualBM_",
        du_shim_result_lvl_from_residual as *const u8,
    );
    ins(
        "_RNvXsq_NtCs2EYQwhfuABO_4core6resultINtB5_6ResultuNtCshhXhIKvfvMU_25clean_decl_universe_slice9TypeErrorEINtNtNtB7_3ops9try_trait12FromResidualIBy_NtNtB7_7convert10InfallibleBL_EE13from_residualBN_",
        du_shim_result_unit_from_residual as *const u8,
    );
    // ref-to-ref cmp wrappers.
    ins(
        "_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCshhXhIKvfvMU_25clean_decl_universe_slice4NameNtB7_9PartialEq2eqBF_",
        du_shim_name_ref_eq as *const u8,
    );
    ins(
        "_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCshhXhIKvfvMU_25clean_decl_universe_slice4NameNtB7_9PartialEq2neBF_",
        du_shim_name_ref_ne as *const u8,
    );
    ins(
        "_RNvXs8_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCshhXhIKvfvMU_25clean_decl_universe_slice4NameNtB7_10PartialOrd2ltBF_",
        du_shim_name_ref_lt as *const u8,
    );
    ins(
        "_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelNtB7_9PartialEq2eqBF_",
        du_shim_lvl_ref_eq as *const u8,
    );
    ins(
        "_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelNtB7_9PartialEq2neBF_",
        du_shim_lvl_ref_ne as *const u8,
    );
    ins(
        "_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCshhXhIKvfvMU_25clean_decl_universe_slice7LiteralNtB7_9PartialEq2eqBF_",
        du_shim_lit_ref_eq as *const u8,
    );
    ins(
        "_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRNtCshhXhIKvfvMU_25clean_decl_universe_slice6FVarIdNtB7_9PartialEq2eqBF_",
        du_shim_fvarid_ref_eq as *const u8,
    );
    ins(
        "_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRmNtB7_9PartialEq2eqCshhXhIKvfvMU_25clean_decl_universe_slice",
        du_shim_u32_ref_eq as *const u8,
    );
    // hash leaves.
    ins(
        "_RINvXs9_NtNtCs2EYQwhfuABO_4core4hash5implsmNtB8_4Hash4hashNtCshhXhIKvfvMU_25clean_decl_universe_slice10KaniHasherEBW_",
        du_shim_hash_u32 as *const u8,
    );
    ins(
        "_RINvXsa_NtNtCs2EYQwhfuABO_4core4hash5implsyNtB8_4Hash4hashNtCshhXhIKvfvMU_25clean_decl_universe_slice10KaniHasherEBW_",
        du_shim_hash_u64 as *const u8,
    );
    ins(
        "_RINvXsg_NtNtCs2EYQwhfuABO_4core4hash5implsiNtB8_4Hash4hashNtCshhXhIKvfvMU_25clean_decl_universe_slice10KaniHasherEBW_",
        du_shim_hash_isize as *const u8,
    );
    ins(
        "_RINvNtCs2EYQwhfuABO_4core3mem12discriminantNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelEBH_",
        du_shim_discriminant_level as *const u8,
    );
    ins(
        "_RINvXs3_NtCs2EYQwhfuABO_4core3memINtB6_12DiscriminantNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelENtNtB8_4hash4Hash4hashNtBR_10KaniHasherEBR_",
        du_shim_hash_discriminant_level as *const u8,
    );
    ins(
        "_RINvXs12_NtCskTzINo8ZBH9_5alloc4syncINtB7_3ArcNtCshhXhIKvfvMU_25clean_decl_universe_slice5LevelENtNtCs2EYQwhfuABO_4core4hash4Hash4hashNtBK_10KaniHasherEBK_",
        du_shim_hash_arc_level as *const u8,
    );
    externs
}

// drop_glue / eh-personality leaves resolve to a no-op: the shims deliberately LEAK
// (per the header note), so nothing needs to be freed on the one-shot JIT path.
extern "C" fn du_shim_noop_drop() {}
// A panic leaf firing would be a genuine divergence (out-of-bounds / double-panic);
// abort loudly rather than silently mis-execute.
extern "C" fn du_shim_abort() {
    std::process::abort();
}

// Normalize a Rust v0-mangled symbol so drifting disambiguators (the `Cs<base62>_`
// crate-disambiguator and `s<base62>_` impl-disambiguators, plus backref tokens) are
// neutralized while every length-prefixed <count><identifier> run is copied VERBATIM
// (read the count, copy exactly that many bytes). A misparse panics loudly — never a
// silent wrong-bind. The frozen shim table keys are frozen-toolchain-mangled; the
// trust re-emit drifted only these disambiguators, so both lanes bind by the SAME
// normalized name.
fn norm_extern(name: &str) -> String {
    let b = name.as_bytes();
    let mut i = 0usize;
    let mut out = String::new();
    while i < b.len() {
        let c = b[i];
        if c.is_ascii_digit() {
            // length-prefixed identifier <decimaldigits><identifier>: copy verbatim.
            let mut j = i;
            let mut n: usize = 0;
            while j < b.len() && b[j].is_ascii_digit() {
                n = n
                    .checked_mul(10)
                    .and_then(|x| x.checked_add((b[j] - b'0') as usize))
                    .unwrap_or_else(|| panic!("norm_extern length overflow in `{name}`"));
                j += 1;
            }
            let end = j
                .checked_add(n)
                .filter(|&e| e <= b.len())
                .unwrap_or_else(|| {
                    panic!("norm_extern misparse: identifier length {n} at {i} overruns `{name}`")
                });
            out.push_str(&name[i..end]);
            i = end;
        } else if c == b'B' {
            // backref B<base62>_ : copy verbatim (never a length prefix).
            let mut j = i + 1;
            while j < b.len() && b[j].is_ascii_alphanumeric() {
                j += 1;
            }
            if j < b.len() && b[j] == b'_' {
                j += 1;
            }
            out.push_str(&name[i..j]);
            i = j;
        } else if c == b's' {
            // possible disambiguator s<base62>_ : strip if it closes with `_`.
            let mut j = i + 1;
            while j < b.len() && b[j].is_ascii_alphanumeric() {
                j += 1;
            }
            if j < b.len() && b[j] == b'_' {
                i = j + 1; // drop the whole s...._ token
            } else {
                out.push('s');
                i += 1;
            }
        } else {
            out.push(c as char);
            i += 1;
        }
    }
    out
}

// Resolve every empty-body (extern) function in the module to a shim pointer by
// normalized name, mapping drop_glue/eh-personality -> no-op and panic -> abort.
// Panics loudly on any unbound extern or normalized-name collision — never a silent
// wrong-bind. Returns a table keyed by the module's EXACT extern names.
fn resolve_externs(
    module: &trust_ir::Module,
    ext: &HashMap<String, *const u8>,
) -> HashMap<String, *const u8> {
    // Normalized index of the shim table.
    let mut norm_index: HashMap<String, *const u8> = HashMap::new();
    for (k, &v) in ext {
        let nk = norm_extern(k);
        if let Some(&prev) = norm_index.get(&nk) {
            assert!(
                prev == v,
                "norm_extern shim collision: `{k}` -> `{nk}` maps to two pointers"
            );
        }
        norm_index.insert(nk, v);
    }
    // Seed with the raw shim table so exact runtime symbols (e.g. __rust_alloc) and any
    // already-exact mangled names stay bound; overlay robust bindings below.
    let mut resolved: HashMap<String, *const u8> = ext.clone();
    for f in &module.functions {
        if !f.blocks.is_empty() {
            continue;
        }
        let name = f.name.as_str();
        let ptr: *const u8 = if name.contains("drop_glue") || name.contains("rust_eh_personality") {
            du_shim_noop_drop as *const u8
        } else if name.contains("panic") {
            du_shim_abort as *const u8
        } else {
            let nn = norm_extern(name);
            *norm_index.get(&nn).unwrap_or_else(|| {
                panic!("unbound extern `{name}` (normalized `{nn}`) in decl-universe module")
            })
        };
        resolved.insert(f.name.clone(), ptr);
    }
    resolved
}

#[test]
fn mir_decl_gate_full_universe_roundtrip() {
    let module = trust_ir::parser::parse_module(TIR).expect(
        "MIR-emitted `check_decl_readonly` (full-universe decl gate) trust-ir text must parse",
    );

    // ── CONFIRM the full gate call graph is genuinely IN-MODULE, including the
    //    COMPLETE production-Level universe machinery. ──
    let bodied = |sym: &str| {
        module
            .functions
            .iter()
            .find(|f| f.name == sym)
            .map(|f| !f.blocks.is_empty())
            .unwrap_or(false)
    };
    for sym in [
        "Verifier____env___check_decl_readonly",
        "Verifier____env___infer_sort",
        "Verifier____env___infer_sort_inner",
        "Verifier____env___check_type",
        "Verifier____env___infer_type",
        "Verifier____env___infer_type_core",
        "Verifier____env___whnf_impl",
        "Verifier____env___whnf_inner",
        "Verifier____env___is_def_eq",
        "Verifier____env___def_eq_inner",
        "Verifier____env___structural_eq",
        "Verifier____env___level_eq",
        "Expr__instantiate",
        "Expr__lift_at",
        "find_undef_level_param",
        "find_undef_level_param_in_level",
        // the full-universe pillar, in-module:
        "Level__is_def_eq",
        "Level__normalize",
        "Level__normalize_impl",
        "Level__normalize_max",
        "Level__push_max_args",
        "Level__is_norm_lt",
        "Level__dedup_max_args",
        "Level__subsume_max_args",
        "Level__mk_max_from_args",
        "Level__is_geq_core",
        "Level__is_geq_leaf",
        "Level__imax",
        "Level__max",
        "Level__succ",
        "Level__is_zero",
        "Level__is_nonzero",
        "Level__has_params",
        "Level__get_offset",
        "Level__add_offset",
        "_Level_as_std__cmp__PartialEq___eq",
        "_Level_as_std__hash__Hash___hash",
    ] {
        assert!(bodied(sym), "`{sym}` must be lowered in-module (bodied)");
    }

    // ── CONFIRM the composition edges are RUNNING (not bypassed), by IR text:
    //    gate -> §4 find_undef_level_param (@func.12) + §5 infer_sort (@func.14)
    //         -> §6 Level::is_zero (@func.15) + §7 check_type (@func.18);
    //    level_eq -> Level::is_def_eq (@func.110)  [THE UNIVERSE INTEGRATION];
    //    infer_sort_inner -> infer_type_core (@func.45) + whnf_impl (@func.46)
    //                      + Level::imax (@func.49). ──
    let body_of = |sym: &str| -> &str {
        let start = TIR
            .find(&format!("fn @{sym}("))
            .unwrap_or_else(|| panic!("`{sym}` header present in IR text"));
        let after = &TIR[start + 1..];
        let end = after
            .find("\nfn @")
            .map(|i| start + 1 + i)
            .unwrap_or(TIR.len());
        &TIR[start..end]
    };
    // `@func.N` numbering is fixture-specific (the trust re-emit renumbers), so resolve
    // each callee's index from the module's declaration order — the same order @func.N
    // indexes into — rather than pinning the frozen numbers.
    let func_idx = |sym: &str| -> usize {
        module
            .functions
            .iter()
            .position(|f| f.name == sym)
            .unwrap_or_else(|| panic!("`{sym}` not present in module"))
    };
    let calls = |caller: &str, callee: &str| -> bool {
        body_of(caller).contains(&format!("@func.{}(", func_idx(callee)))
    };
    assert!(
        calls(
            "Verifier____env___check_decl_readonly",
            "find_undef_level_param"
        ),
        "gate must Call find_undef_level_param (§4 RUNNING)"
    );
    assert!(
        calls(
            "Verifier____env___check_decl_readonly",
            "Verifier____env___infer_sort"
        ),
        "gate must Call infer_sort (§5 RUNNING)"
    );
    assert!(
        calls("Verifier____env___check_decl_readonly", "Level__is_zero"),
        "gate must Call Level::is_zero (§6 RUNNING)"
    );
    assert!(
        calls(
            "Verifier____env___check_decl_readonly",
            "Verifier____env___check_type"
        ),
        "gate must Call check_type (§7 RUNNING)"
    );
    assert!(
        calls("Verifier____env___level_eq", "Level__is_def_eq"),
        "level_eq must Call Level__is_def_eq — the FULL universe unification wired into def_eq"
    );
    assert!(
        calls(
            "Verifier____env___infer_sort_inner",
            "Verifier____env___infer_type_core"
        ),
        "infer_sort_inner must Call infer_type_core"
    );
    assert!(
        calls(
            "Verifier____env___infer_sort_inner",
            "Verifier____env___whnf_impl"
        ),
        "infer_sort_inner must Call whnf_impl"
    );
    assert!(
        calls("Verifier____env___infer_sort_inner", "Level__imax"),
        "infer_sort_inner must Call Level::imax (FULL imax)"
    );

    let externs = build_externs();
    let resolved = resolve_externs(&module, &externs);
    let buffer = Compiler::new(CompilerConfig::jit_fast(Target::Aarch64))
        .compile_module_to_jit(&module, &resolved)
        .expect("trust-cg JIT compile of MIR-emitted full-universe `check_decl_readonly` failed")
        .buffer;
    let raw = buffer
        .get_fn_ptr_bound("Verifier____env___check_decl_readonly")
        .expect("JIT symbol `Verifier____env___check_decl_readonly` not found")
        .as_ptr();
    let gate_fn: DeclCheckFn = unsafe { std::mem::transmute(raw) };

    // ── Inputs: genuinely universe-POLYMORPHIC declarations over params {u, v}. ──
    let bd = BinderData { info: 0, mult: 2 };
    let u = Name(1);
    let v = Name(2);
    let pu = || Level::Param(Name(1));
    let pv = || Level::Param(Name(2));
    // RAW (non-simplifying) level constructors so normalize does the work.
    let rmax = |a: Level, b: Level| Level::Max(Arc::new(a), Arc::new(b));
    let rimax = |a: Level, b: Level| Level::IMax(Arc::new(a), Arc::new(b));
    let rsucc = |a: Level| Level::Succ(Arc::new(a));
    let arc = |e: Expr| Arc::new(e);
    let s0 = || Expr::sort0();
    let sortl = |l: Level| Expr::sort(l);
    let bv = |i: u32| Expr::bvar(i);
    let pi = |t: Expr, b: Expr| Expr::pi(bd, t, b);
    let lam = |t: Expr, b: Expr| Expr::lam(bd, t, b);

    // Modeled env: Const(101) := λ(Sort0).#0 (so Const(101)'s type is Pi(Sort0,Sort0) —
    // drives infer_sort's Pi-recursion arm through the env unfold).
    let env: Vec<(Name, Option<Expr>)> = vec![(Name(101), Some(lam(s0(), bv(0))))];
    let ctors: Vec<(Name, u32)> = vec![];
    let verifier = Verifier {
        env: &env,
        ctors: &ctors,
    };

    // The Prop tower: T0 = ∀(α:Sort0). α → α  : Sort(imax(1, imax(0,0))) = Sort 0.
    let prop_ty = || pi(s0(), pi(bv(0), bv(1)));
    let prop_proof = || lam(s0(), lam(bv(0), bv(0)));
    // The polymorphic tower: Tu = ∀(α:Sort u). α → α : Sort(IMax(succ u, u)) — a REAL IMax.
    let poly_ty = || pi(sortl(pu()), pi(bv(0), bv(1)));
    let poly_proof = || lam(sortl(pu()), lam(bv(0), bv(0)));
    // Pi with body at Succ level: ∀(α:Sort u). ∀(x:α). Sort v — drives imax(_,Succ..)=Max
    // then the flatten/sort/DEDUP-SAME-BASE normalization in §7.
    let maxy_val = || pi(sortl(pu()), pi(bv(0), sortl(pv())));

    let cases: Vec<(Declaration, &str)> = vec![
        // 1 ACCEPT: poly axiom at Sort(max u v) — §5 over a Max level.
        (
            Declaration::Axiom {
                name: Name(10),
                level_params: vec![u, v],
                type_: arc(sortl(rmax(pu(), pv()))),
            },
            "ACCEPT axiom ax.{u,v} : Sort(max u v)",
        ),
        // 2 REJECT §6 (poly): theorem at Sort(max u v) — sort = Succ(Max(u,v)), not Prop.
        //   The JIT BUILDS the Succ(Max) sort payload (compared structurally below).
        (
            Declaration::Theorem {
                name: Name(11),
                level_params: vec![u, v],
                type_: arc(sortl(rmax(pu(), pv()))),
                value: arc(s0()),
            },
            "REJECT §6 thm.{u,v} : Sort(max u v)  [sort=succ(max u v) not Prop]",
        ),
        // 3 REJECT §4: level_params {u} but the type mentions v NESTED inside Max(u, IMax(v,u)).
        (
            Declaration::Axiom {
                name: Name(12),
                level_params: vec![u],
                type_: arc(sortl(rmax(pu(), rimax(pv(), pu())))),
            },
            "REJECT §4 ax.{u} : Sort(max u (imax v u))  [undef param v inside IMax]",
        ),
        // 4 REJECT §2: duplicate level param u.
        (
            Declaration::Axiom {
                name: Name(13),
                level_params: vec![u, v, u],
                type_: arc(sortl(rmax(pu(), pv()))),
            },
            "REJECT §2 ax.{u,v,u}  [duplicate param u]",
        ),
        // 5 ACCEPT (theorem): the imax(_,0)=0 EDGE — T0 : Sort 0 (is_theorem gate passes)
        //   and §7 def_eq(Pi-tower, Pi-tower).
        (
            Declaration::Theorem {
                name: Name(14),
                level_params: vec![],
                type_: arc(prop_ty()),
                value: arc(prop_proof()),
            },
            "ACCEPT thm : (∀α:Prop. α→α) := λλ#0  [imax(_,0)=0 edge; theorem-is-Prop OK]",
        ),
        // 6 REJECT §6 (poly, REAL IMax): Tu's sort is IMax(succ u, u) — not zero.
        //   The JIT BUILDS the IMax node via the full smart-imax (compared structurally below).
        (
            Declaration::Theorem {
                name: Name(15),
                level_params: vec![u],
                type_: arc(poly_ty()),
                value: arc(poly_proof()),
            },
            "REJECT §6 thm.{u} : (∀α:Sort u. α→α)  [sort=IMax(succ u, u) not Prop]",
        ),
        // 7 ACCEPT §7 Max COMMUTATIVITY: declared Sort(succ(max v u)) vs inferred
        //   Sort(succ(max u v)) — equal only through normalize (flatten+sort+offset).
        (
            Declaration::Definition {
                name: Name(16),
                level_params: vec![u, v],
                type_: arc(sortl(rsucc(rmax(pv(), pu())))),
                value: arc(sortl(rmax(pu(), pv()))),
                is_reducible: false,
            },
            "ACCEPT def.{u,v} : Sort(succ(max v u)) := Sort(max u v)  [§7 via Max commutativity normalization]",
        ),
        // 8 ACCEPT §7 DEDUP-SAME-BASE: value's sort Max(succ u, Max(u, succ v))
        //   normalizes to Max(succ u, succ v) == declared. Also exercises the
        //   imax(_,Succ..)=Max collapse inside inference.
        (
            Declaration::Definition {
                name: Name(17),
                level_params: vec![u, v],
                type_: arc(sortl(rmax(rsucc(pu()), rsucc(pv())))),
                value: arc(maxy_val()),
                is_reducible: false,
            },
            "ACCEPT def.{u,v} : Sort(max (succ u) (succ v)) := ∀α:Sort u.∀x:α.Sort v  [imax->Max collapse + dedup-same-base]",
        ),
        // 9 REJECT §7 WRONG UNIVERSE: declared Sort(max u v) vs inferred Sort(succ(max v u))
        //   — normalize distinguishes the offsets -> TypeMismatch. Payload exprs
        //   (the JIT-BUILT inferred type) deep-compared meta-bit-identically below.
        (
            Declaration::Definition {
                name: Name(18),
                level_params: vec![u, v],
                type_: arc(sortl(rmax(pu(), pv()))),
                value: arc(sortl(rmax(pv(), pu()))),
                is_reducible: false,
            },
            "REJECT §7 def.{u,v} : Sort(max u v) := Sort(max v u)  [inferred succ(max) != max — wrong universe]",
        ),
        // 10 REJECT §5: declared type is not a type (Nat literal).
        (
            Declaration::Axiom {
                name: Name(19),
                level_params: vec![],
                type_: arc(Expr::nat(7)),
            },
            "REJECT §5 ax : Nat(7)  [ExpectedSort]",
        ),
        // 11 REJECT §3: type contains an FVar (meta quick-bit path).
        (
            Declaration::Axiom {
                name: Name(20),
                level_params: vec![],
                type_: arc(Expr::from_kind(ExprKind::FVar(FVarId(5)))),
            },
            "REJECT §3 ax : FVar(5)  [ContainsFreeVar]",
        ),
        // 12 ACCEPT: Opaque (value-bearing, non-theorem) at a poly type.
        (
            Declaration::Opaque {
                name: Name(21),
                level_params: vec![u],
                type_: arc(sortl(rsucc(pu()))),
                value: arc(sortl(pu())),
            },
            "ACCEPT opaque.{u} : Sort(succ u) := Sort(u)",
        ),
        // 13 ACCEPT: type is a Const — env unfold + infer_sort's Pi-recursion arm.
        (
            Declaration::Axiom {
                name: Name(22),
                level_params: vec![],
                type_: arc(Expr::cnst(Name(101))),
            },
            "ACCEPT ax : Const(101)  [infer_sort Pi-arm through env unfold]",
        ),
        // 14 REJECT §4 in the VALUE: value mentions u, params only {v}.
        (
            Declaration::Definition {
                name: Name(23),
                level_params: vec![v],
                type_: arc(sortl(rsucc(pv()))),
                value: arc(sortl(pu())),
                is_reducible: false,
            },
            "REJECT §4 def.{v} := Sort(u)  [undef param u in value]",
        ),
    ];

    let run_jit = |decl: &Declaration| -> Result<(), EnvError> {
        let mut out = std::mem::MaybeUninit::<Result<(), EnvError>>::uninit();
        let vp: *const Verifier = &verifier as *const Verifier;
        let dp: *const Declaration = decl as *const Declaration;
        unsafe {
            gate_fn(out.as_mut_ptr(), vp, dp);
            out.assume_init()
        }
    };

    let mut accepts = 0usize;
    let mut rejects = 0usize;
    for (decl, label) in &cases {
        let native = verifier.check_decl_readonly(decl);
        let jit = run_jit(decl);
        match (&native, &jit) {
            (Ok(()), Ok(())) => accepts += 1,
            (Err(ne), Err(je)) => {
                assert!(
                    env_error_agrees(ne, je),
                    "decl gate JIT disagrees with native on `{label}` (both Err, payloads differ):\n  native = {ne:?}\n  jit    = {je:?}"
                );
                rejects += 1;
            }
            _ => panic!(
                "decl gate JIT vs native ACCEPT/REJECT disagreement on `{label}`:\n  native = {native:?}\n  jit    = {jit:?}"
            ),
        }
    }
    assert_eq!(
        accepts, 6,
        "expected exactly 6 ACCEPTs (cases 1,5,7,8,12,13)"
    );
    assert_eq!(
        rejects, 8,
        "expected exactly 8 REJECTs (cases 2,3,4,6,9,10,11,14)"
    );

    // ── PINNED payload checks: the JIT-BUILT universe payloads, deref'd. ──
    // Case 6: sort must be EXACTLY IMax(Succ(Param u), Param u) — a real IMax node
    // constructed by the JIT's full smart-imax, compared node-by-node.
    let expected_imax = rimax(rsucc(pu()), pu());
    let jit6 = run_jit(&cases[5].0);
    let jit6_sort = match &jit6 {
        Err(EnvError::TheoremTypeNotProp { sort, .. }) => sort.clone(),
        other => panic!("case 6 must be TheoremTypeNotProp, got {other:?}"),
    };
    assert!(
        level_structural_eq(&jit6_sort, &expected_imax),
        "case 6: JIT-built sort payload must be IMax(succ u, u); got {jit6_sort:?}"
    );
    let native6 = verifier.check_decl_readonly(&cases[5].0);
    let native6_sort = match &native6 {
        Err(EnvError::TheoremTypeNotProp { sort, .. }) => sort.clone(),
        other => panic!("case 6 native must be TheoremTypeNotProp, got {other:?}"),
    };
    assert!(
        level_structural_eq(&native6_sort, &expected_imax),
        "case 6 native sort must match the pinned IMax"
    );
    // Case 2: sort must be Succ(Max(u,v)).
    let jit2 = run_jit(&cases[1].0);
    match &jit2 {
        Err(EnvError::TheoremTypeNotProp { sort, .. }) => {
            assert!(
                level_structural_eq(sort, &rsucc(rmax(pu(), pv()))),
                "case 2: JIT-built sort payload must be succ(max u v); got {sort:?}"
            );
        }
        other => panic!("case 2 must be TheoremTypeNotProp, got {other:?}"),
    }
    // Case 9: the TypeMismatch payloads (expected = declared type clone; inferred =
    // the JIT-CONSTRUCTED Sort(succ(max v u))) must deep-agree with native with the
    // ExprMeta word BIT-IDENTICAL at every node (routes through the full Level hash
    // chain: discriminant + Arc<Level> child hashing).
    let native9 = verifier.check_decl_readonly(&cases[8].0);
    let jit9 = run_jit(&cases[8].0);
    let (n_exp, n_inf) = match &native9 {
        Err(EnvError::TypeCheckFailed {
            source: TypeError::TypeMismatch { expected, inferred },
            ..
        }) => (expected.clone(), inferred.clone()),
        other => panic!("case 9 native must be TypeMismatch, got {other:?}"),
    };
    let (j_exp, j_inf) = match &jit9 {
        Err(EnvError::TypeCheckFailed {
            source: TypeError::TypeMismatch { expected, inferred },
            ..
        }) => (expected.clone(), inferred.clone()),
        other => panic!("case 9 JIT must be TypeMismatch, got {other:?}"),
    };
    assert!(
        deep_eq(&n_exp, &j_exp),
        "case 9: expected-type payload must be meta-bit-identical native == JIT"
    );
    assert!(
        deep_eq(&n_inf, &j_inf),
        "case 9: JIT-CONSTRUCTED inferred-type payload must be meta-bit-identical native == JIT"
    );
    assert!(
        matches!(&j_inf.kind, ExprKind::Sort(Level::Succ(_))),
        "case 9: the JIT-built inferred type must be Sort(succ(..)) — the wrong-universe witness"
    );

    // ── NC1 (fail-loud): an always-accept gate must DISAGREE with native on the
    //    wrong-universe definition — proves the differential catches a gate that
    //    admits the unsound decl. ──
    assert!(
        native9.is_err(),
        "control: native gate MUST reject the wrong-universe definition"
    );
    let always_accept = |_d: &Declaration| -> Result<(), EnvError> { Ok(()) };
    let bogus = always_accept(&cases[8].0);
    assert_ne!(
        native9.is_ok(),
        bogus.is_ok(),
        "NEGATIVE CONTROL FAILED: an always-accept gate agreed with native on the wrong-universe decl — the differential is vacuous"
    );

    // ── NC2 (fail-loud): deliberately-WRONG universe expectations must be REJECTED
    //    by the structural comparator against the JIT-built sort. ──
    assert!(
        !level_structural_eq(&jit6_sort, &Level::Zero),
        "NEGATIVE CONTROL FAILED: comparator equated IMax(succ u, u) with Zero — the universe check is vacuous"
    );
    assert!(
        !level_structural_eq(&jit6_sort, &rimax(pu(), rsucc(pu()))),
        "NEGATIVE CONTROL FAILED: comparator equated IMax(succ u, u) with the arg-SWAPPED IMax(u, succ u)"
    );

    // ── NC3 (fail-loud): a meta-word-corrupted copy of the case-9 payload must be
    //    REJECTED by deep_eq — proves the bit-identity check actually reads meta. ──
    let corrupted = Expr {
        kind: n_inf.kind.clone(),
        meta: ExprMeta(n_inf.meta.raw() ^ 1),
    };
    assert!(
        !deep_eq(&corrupted, &j_inf),
        "NEGATIVE CONTROL FAILED: deep_eq accepted a meta-corrupted expr — the meta-bit-identity check is vacuous"
    );

    drop(buffer);
}
