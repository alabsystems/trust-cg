//! TRUST-SELF ROUND 3 (thread R2-B): verifying MORE OF TRUST ITSELF —
//! trust-cg's remaining AArch64 word builders + the LDR/STR/LDP/STP
//! ADDRESSING-MODE encoders — through the full pipeline Rust -> MIR ->
//! trust-ir (stage1 `trust_ir_mir --mir-emit-closure`) -> trust-cg JIT ->
//! machine code, asserting native Rust == JIT over swept real inputs. These
//! are the functions that assemble every branch, every return, every
//! load/store and every prologue/epilogue pair trust-cg emits: a wrong field
//! shift here is a wrong instruction in every compiled program (including
//! the JIT running this test).
//!
//! New verified functions in this file (18):
//!   * the remaining WORD BUILDERS (encoding.rs): `encode_extract` (EXTR/ROR),
//!     `encode_bit_reverse` (RBIT), `encode_uncond_branch` (B/BL),
//!     `encode_branch_reg` (BR/BLR/RET), `encode_load_store_ui`
//!     (LDR/STR scaled unsigned offset), `encode_load_store_pair` (LDP/STP)
//!   * the ADDRESSING-MODE cluster (encoding_mem.rs):
//!     `encode_ldr_str_unsigned_offset`, `encode_ldr_str_pre_index`,
//!     `encode_ldr_str_post_index`, `encode_ldr_str_register`,
//!     `encode_ldp_stp` (+ its 3 mode wrappers `encode_ldp_stp_offset`,
//!     `encode_ldp_stp_pre_index`, `encode_ldp_stp_post_index`),
//!     `encode_ldrsw_register`, and the validators `check_imm12`,
//!     `check_imm9`, `check_imm7` (exhaustive over their FULL input domains;
//!     `check_reg` re-verified exhaustively over all 65536 (reg,max) pairs)
//!
//! Slices (verbatim transcriptions, modeled boundaries documented inline):
//!   tests/slices/trust_encwords2_slice.rs
//!   tests/slices/trust_memaddr_slice.rs
//! (working copies also in <dev-scratch>/r2-trust3/)
//!
//! REGEN (per module):
//!   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//!   cd $HOME/trust-ir/frontend && env -u RUSTUP_TOOLCHAIN RUSTC=$S/bin/rustc \
//!     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//!     $S/bin/cargo run --bin trust_ir_mir -- <slice.rs> --crate-type=lib \
//!     --mir-emit-closure <fn> <out.tir>
//!
//! MODELED BOUNDARIES (each also documented at the affected fixture below and
//! in the slice files; all inherited from round 2's pinned frontend limits —
//! NO new boundary was needed for this batch):
//!   * `debug_assert!` guards are STRIPPED from the encoding.rs word-builder
//!     slices — release-mode semantics (trust-cg ships with debug-assertions
//!     off). PINNED FRONTEND LIMIT (round 2): a body containing
//!     `debug_assert!` fails to lower ("call arg constant of non-scalar type
//!     ref" — the expanded `core::panicking::panic("...")` call's &str
//!     constant; MIR Assert TERMINATORS lower fine, explicit panic CALLS do
//!     not). Verified domain = the encoder contract domain (in-range fields).
//!   * encoding_mem.rs encoders: `?` rewritten as explicit match — PINNED
//!     FRONTEND LIMIT (round 2): `?` on Result lowers to EMPTY-bodied
//!     `<Result as Try>::branch` / `FromResidual::from_residual` externs.
//!     Oracles are the REAL production pub fns (verbatim `?` form).
//!   * `check_imm9` / `check_imm7`: `(-256..=255).contains(&value)` /
//!     `(-64..=63).contains(&value)` rewritten as explicit comparisons
//!     (RangeInclusive::contains does not lower — known frontend limit).
//!     Checked EXHAUSTIVELY over the full i16 / i8 domains against
//!     verbatim-`contains` oracles + the production encoders' error paths.
//!   * `EncodeError` thiserror derive dropped in the slice (generates only
//!     Display/Error impls, not in any call graph here; layout unchanged).
//!
//! BACKEND-VALIDATOR NOTE (same documented class as round 2, nothing new):
//! every module here that shifts by a CONSTANT amount carries
//! `validate_module` BinOpTypeMismatch errors — the MIR lowering spells
//! constant shift amounts as `const i32` against a u32/u64 lhs, which
//! trust-ir's validator rejects while trust-cg codegen consumes the
//! constant's bit pattern correctly (proven by every differential in this
//! file). Per-module counts are exactly 2 x (number of constant-amount
//! shifts) — the whole reported error set is this one class.
//!
//! COVERAGE NOTE: gated to aarch64 (the JIT target); on any other host this
//! file compiles to ZERO tests. Run tests ONE AT A TIME
//! (`-- --exact <name> --test-threads=1`): the JIT engine's LLVM context is
//! not thread-safe at suite scale (see jit-parallel-race-2026-06-29.md).

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::Target;
use trust_cg_codegen::aarch64::encoding as prod_encoding;
use trust_cg_codegen::aarch64::encoding_mem as prod_encoding_mem;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

use prod_encoding_mem::{LoadStoreOp, LoadStoreSize, PairMode, PairOp, PairSize, RegExtend};

// ── shared harness ──────────────────────────────────────────────────────────

/// Parse + JIT one embedded module; return the buffer (keep it alive while
/// calling fn pointers bound from it).
fn jit_module(text: &str, what: &str) -> trust_cg_codegen::jit::ExecutableBuffer {
    let module = trust_ir::parser::parse_module(text)
        .unwrap_or_else(|e| panic!("MIR-emitted `{what}` trust-ir text must parse: {e:?}"));
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .compile_module_to_jit(&module, &HashMap::new())
        .unwrap_or_else(|e| panic!("trust-cg JIT compile of MIR-emitted `{what}` failed: {e:?}"))
        .buffer
}

fn bind(buffer: &trust_cg_codegen::jit::ExecutableBuffer, sym: &str) -> *const u8 {
    buffer
        .get_fn_ptr_bound(sym)
        .unwrap_or_else(|| panic!("JIT symbol `{sym}` not found"))
        .as_ptr()
}

// ═══════════════════════════════════════════════════════════════════════════
// Embedded MIR-closure emits — encoding.rs word builders (round 3)
// ═══════════════════════════════════════════════════════════════════════════

/// VERBATIM MIR-closure emit of the production `encode_extract` (encoding.rs;
/// debug_assert! guards stripped in the slice = release-mode semantics — see
/// the module-header MODELED BOUNDARIES). Emit reported: 2000 bytes; 1 closure
/// member; validate_module = 12 error(s), ALL the documented
/// const-shift-amount spelling divergence (2 per constant shift x 6 shifts);
/// re-parse OK. Slice: tests/slices/trust_encwords2_slice.rs.
/// Regen: trust_ir_mir trust_encwords2_slice.rs --crate-type=lib
///   --mir-emit-closure encode_extract <out.tir>
const EXTRACT_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_extract"

functy.0 = (u32, u32, u32, u32, u32, u32) -> (u32)

fn @encode_extract(functy.0) {
bb0(%0: u32, %1: u32, %2: u32, %3: u32, %4: u32, %5: u32):
    %36 = const i32 31
    %37 = bitcast i32 %36 to u32
    %38 = const u32 32
    %39 = icmp ult u32 %37, %38
    condbr %39, bb1(%0, %1, %2, %3, %4, %5), bb7
bb1(%6: u32, %7: u32, %8: u32, %9: u32, %10: u32, %11: u32):
    %40 = const i32 31
    %41 = shl u32 %6, %40
    %42 = const i32 23
    %43 = bitcast i32 %42 to u32
    %44 = const u32 32
    %45 = icmp ult u32 %43, %44
    condbr %45, bb2(%7, %8, %9, %10, %11, %41), bb7
bb2(%12: u32, %13: u32, %14: u32, %15: u32, %16: u32, %17: u32):
    %46 = const u32 39
    %47 = const i32 23
    %48 = shl u32 %46, %47
    %49 = or u32 %17, %48
    %50 = const i32 22
    %51 = bitcast i32 %50 to u32
    %52 = const u32 32
    %53 = icmp ult u32 %51, %52
    condbr %53, bb3(%12, %13, %14, %15, %16, %49), bb7
bb3(%18: u32, %19: u32, %20: u32, %21: u32, %22: u32, %23: u32):
    %54 = const i32 22
    %55 = shl u32 %18, %54
    %56 = or u32 %23, %55
    %57 = const i32 16
    %58 = bitcast i32 %57 to u32
    %59 = const u32 32
    %60 = icmp ult u32 %58, %59
    condbr %60, bb4(%19, %20, %21, %22, %56), bb7
bb4(%24: u32, %25: u32, %26: u32, %27: u32, %28: u32):
    %61 = const i32 16
    %62 = shl u32 %24, %61
    %63 = or u32 %28, %62
    %64 = const i32 10
    %65 = bitcast i32 %64 to u32
    %66 = const u32 32
    %67 = icmp ult u32 %65, %66
    condbr %67, bb5(%25, %26, %27, %63), bb7
bb5(%29: u32, %30: u32, %31: u32, %32: u32):
    %68 = const i32 10
    %69 = shl u32 %29, %68
    %70 = or u32 %32, %69
    %71 = const i32 5
    %72 = bitcast i32 %71 to u32
    %73 = const u32 32
    %74 = icmp ult u32 %72, %73
    condbr %74, bb6(%30, %31, %70), bb7
bb6(%33: u32, %34: u32, %35: u32):
    %75 = const i32 5
    %76 = shl u32 %33, %75
    %77 = or u32 %35, %76
    %78 = or u32 %77, %34
    ret %78
bb7:
    unreachable
}
"#;

/// VERBATIM MIR-closure emit of the production `encode_bit_reverse`
/// (encoding.rs; debug_asserts stripped = release semantics). Emit reported:
/// 998 bytes; 1 closure member; validate_module = 6 error(s) (2 x 3 constant
/// shifts, the documented class); re-parse OK.
/// Slice: tests/slices/trust_encwords2_slice.rs.
/// Regen: trust_ir_mir trust_encwords2_slice.rs --crate-type=lib
///   --mir-emit-closure encode_bit_reverse <out.tir>
const BIT_REVERSE_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_bit_reverse"

functy.0 = (u32, u32, u32) -> (u32)

fn @encode_bit_reverse(functy.0) {
bb0(%0: u32, %1: u32, %2: u32):
    %12 = const i32 31
    %13 = bitcast i32 %12 to u32
    %14 = const u32 32
    %15 = icmp ult u32 %13, %14
    condbr %15, bb1(%0, %1, %2), bb4
bb1(%3: u32, %4: u32, %5: u32):
    %16 = const i32 31
    %17 = shl u32 %3, %16
    %18 = const i32 21
    %19 = bitcast i32 %18 to u32
    %20 = const u32 32
    %21 = icmp ult u32 %19, %20
    condbr %21, bb2(%4, %5, %17), bb4
bb2(%6: u32, %7: u32, %8: u32):
    %22 = const u32 726
    %23 = const i32 21
    %24 = shl u32 %22, %23
    %25 = or u32 %8, %24
    %26 = const i32 5
    %27 = bitcast i32 %26 to u32
    %28 = const u32 32
    %29 = icmp ult u32 %27, %28
    condbr %29, bb3(%6, %7, %25), bb4
bb3(%9: u32, %10: u32, %11: u32):
    %30 = const i32 5
    %31 = shl u32 %9, %30
    %32 = or u32 %11, %31
    %33 = or u32 %32, %10
    ret %33
bb4:
    unreachable
}
"#;

/// VERBATIM MIR-closure emit of the production `encode_uncond_branch`
/// (encoding.rs; debug_asserts stripped = release semantics). Emit reported:
/// 695 bytes; 1 closure member; validate_module = 4 error(s) (2 x 2 constant
/// shifts, the documented class); re-parse OK.
/// Slice: tests/slices/trust_encwords2_slice.rs.
/// Regen: trust_ir_mir trust_encwords2_slice.rs --crate-type=lib
///   --mir-emit-closure encode_uncond_branch <out.tir>
const UNCOND_BRANCH_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_uncond_branch"

functy.0 = (u32, u32) -> (u32)

fn @encode_uncond_branch(functy.0) {
bb0(%0: u32, %1: u32):
    %6 = const i32 31
    %7 = bitcast i32 %6 to u32
    %8 = const u32 32
    %9 = icmp ult u32 %7, %8
    condbr %9, bb1(%0, %1), bb3
bb1(%2: u32, %3: u32):
    %10 = const i32 31
    %11 = shl u32 %2, %10
    %12 = const i32 26
    %13 = bitcast i32 %12 to u32
    %14 = const u32 32
    %15 = icmp ult u32 %13, %14
    condbr %15, bb2(%3, %11), bb3
bb2(%4: u32, %5: u32):
    %16 = const u32 5
    %17 = const i32 26
    %18 = shl u32 %16, %17
    %19 = or u32 %5, %18
    %20 = or u32 %19, %4
    ret %20
bb3:
    unreachable
}
"#;

/// VERBATIM MIR-closure emit of the production `encode_branch_reg`
/// (encoding.rs; debug_asserts stripped = release semantics). Emit reported:
/// 1195 bytes; 1 closure member; validate_module = 8 error(s) (2 x 4 constant
/// shifts, the documented class); re-parse OK.
/// Slice: tests/slices/trust_encwords2_slice.rs.
/// Regen: trust_ir_mir trust_encwords2_slice.rs --crate-type=lib
///   --mir-emit-closure encode_branch_reg <out.tir>
const BRANCH_REG_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_branch_reg"

functy.0 = (u32, u32) -> (u32)

fn @encode_branch_reg(functy.0) {
bb0(%0: u32, %1: u32):
    %11 = const i32 25
    %12 = bitcast i32 %11 to u32
    %13 = const u32 32
    %14 = icmp ult u32 %12, %13
    condbr %14, bb1(%0, %1), bb5
bb1(%2: u32, %3: u32):
    %15 = const u32 107
    %16 = const i32 25
    %17 = shl u32 %15, %16
    %18 = const i32 21
    %19 = bitcast i32 %18 to u32
    %20 = const u32 32
    %21 = icmp ult u32 %19, %20
    condbr %21, bb2(%2, %3, %17), bb5
bb2(%4: u32, %5: u32, %6: u32):
    %22 = const i32 21
    %23 = shl u32 %4, %22
    %24 = or u32 %6, %23
    %25 = const i32 16
    %26 = bitcast i32 %25 to u32
    %27 = const u32 32
    %28 = icmp ult u32 %26, %27
    condbr %28, bb3(%5, %24), bb5
bb3(%7: u32, %8: u32):
    %29 = const u32 31
    %30 = const i32 16
    %31 = shl u32 %29, %30
    %32 = or u32 %8, %31
    %33 = const i32 5
    %34 = bitcast i32 %33 to u32
    %35 = const u32 32
    %36 = icmp ult u32 %34, %35
    condbr %36, bb4(%7, %32), bb5
bb4(%9: u32, %10: u32):
    %37 = const i32 5
    %38 = shl u32 %9, %37
    %39 = or u32 %10, %38
    ret %39
bb5:
    unreachable
}
"#;

/// VERBATIM MIR-closure emit of the production `encode_load_store_ui`
/// (encoding.rs; debug_asserts stripped = release semantics). Emit reported:
/// 2325 bytes; 1 closure member; validate_module = 14 error(s) (2 x 7
/// constant shifts, the documented class); re-parse OK.
/// Slice: tests/slices/trust_encwords2_slice.rs.
/// Regen: trust_ir_mir trust_encwords2_slice.rs --crate-type=lib
///   --mir-emit-closure encode_load_store_ui <out.tir>
const LDST_UI_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_load_store_ui"

functy.0 = (u32, u32, u32, u32, u32, u32) -> (u32)

fn @encode_load_store_ui(functy.0) {
bb0(%0: u32, %1: u32, %2: u32, %3: u32, %4: u32, %5: u32):
    %41 = const i32 30
    %42 = bitcast i32 %41 to u32
    %43 = const u32 32
    %44 = icmp ult u32 %42, %43
    condbr %44, bb1(%0, %1, %2, %3, %4, %5), bb8
bb1(%6: u32, %7: u32, %8: u32, %9: u32, %10: u32, %11: u32):
    %45 = const i32 30
    %46 = shl u32 %6, %45
    %47 = const i32 27
    %48 = bitcast i32 %47 to u32
    %49 = const u32 32
    %50 = icmp ult u32 %48, %49
    condbr %50, bb2(%7, %8, %9, %10, %11, %46), bb8
bb2(%12: u32, %13: u32, %14: u32, %15: u32, %16: u32, %17: u32):
    %51 = const u32 7
    %52 = const i32 27
    %53 = shl u32 %51, %52
    %54 = or u32 %17, %53
    %55 = const i32 26
    %56 = bitcast i32 %55 to u32
    %57 = const u32 32
    %58 = icmp ult u32 %56, %57
    condbr %58, bb3(%12, %13, %14, %15, %16, %54), bb8
bb3(%18: u32, %19: u32, %20: u32, %21: u32, %22: u32, %23: u32):
    %59 = const i32 26
    %60 = shl u32 %18, %59
    %61 = or u32 %23, %60
    %62 = const i32 24
    %63 = bitcast i32 %62 to u32
    %64 = const u32 32
    %65 = icmp ult u32 %63, %64
    condbr %65, bb4(%19, %20, %21, %22, %61), bb8
bb4(%24: u32, %25: u32, %26: u32, %27: u32, %28: u32):
    %66 = const u32 1
    %67 = const i32 24
    %68 = shl u32 %66, %67
    %69 = or u32 %28, %68
    %70 = const i32 22
    %71 = bitcast i32 %70 to u32
    %72 = const u32 32
    %73 = icmp ult u32 %71, %72
    condbr %73, bb5(%24, %25, %26, %27, %69), bb8
bb5(%29: u32, %30: u32, %31: u32, %32: u32, %33: u32):
    %74 = const i32 22
    %75 = shl u32 %29, %74
    %76 = or u32 %33, %75
    %77 = const i32 10
    %78 = bitcast i32 %77 to u32
    %79 = const u32 32
    %80 = icmp ult u32 %78, %79
    condbr %80, bb6(%30, %31, %32, %76), bb8
bb6(%34: u32, %35: u32, %36: u32, %37: u32):
    %81 = const i32 10
    %82 = shl u32 %34, %81
    %83 = or u32 %37, %82
    %84 = const i32 5
    %85 = bitcast i32 %84 to u32
    %86 = const u32 32
    %87 = icmp ult u32 %85, %86
    condbr %87, bb7(%35, %36, %83), bb8
bb7(%38: u32, %39: u32, %40: u32):
    %88 = const i32 5
    %89 = shl u32 %38, %88
    %90 = or u32 %40, %89
    %91 = or u32 %90, %39
    ret %91
bb8:
    unreachable
}
"#;

/// VERBATIM MIR-closure emit of the production `encode_load_store_pair`
/// (encoding.rs; debug_asserts stripped = release semantics). Emit reported:
/// 2731 bytes; 1 closure member; validate_module = 16 error(s) (2 x 8
/// constant shifts, the documented class); re-parse OK.
/// Slice: tests/slices/trust_encwords2_slice.rs.
/// Regen: trust_ir_mir trust_encwords2_slice.rs --crate-type=lib
///   --mir-emit-closure encode_load_store_pair <out.tir>
const LDST_PAIR_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_load_store_pair"

functy.0 = (u32, u32, u32, u32, u32, u32, u32) -> (u32)

fn @encode_load_store_pair(functy.0) {
bb0(%0: u32, %1: u32, %2: u32, %3: u32, %4: u32, %5: u32, %6: u32):
    %52 = const i32 30
    %53 = bitcast i32 %52 to u32
    %54 = const u32 32
    %55 = icmp ult u32 %53, %54
    condbr %55, bb1(%0, %1, %2, %3, %4, %5, %6), bb9
bb1(%7: u32, %8: u32, %9: u32, %10: u32, %11: u32, %12: u32, %13: u32):
    %56 = const i32 30
    %57 = shl u32 %7, %56
    %58 = const i32 27
    %59 = bitcast i32 %58 to u32
    %60 = const u32 32
    %61 = icmp ult u32 %59, %60
    condbr %61, bb2(%8, %9, %10, %11, %12, %13, %57), bb9
bb2(%14: u32, %15: u32, %16: u32, %17: u32, %18: u32, %19: u32, %20: u32):
    %62 = const u32 5
    %63 = const i32 27
    %64 = shl u32 %62, %63
    %65 = or u32 %20, %64
    %66 = const i32 26
    %67 = bitcast i32 %66 to u32
    %68 = const u32 32
    %69 = icmp ult u32 %67, %68
    condbr %69, bb3(%14, %15, %16, %17, %18, %19, %65), bb9
bb3(%21: u32, %22: u32, %23: u32, %24: u32, %25: u32, %26: u32, %27: u32):
    %70 = const i32 26
    %71 = shl u32 %21, %70
    %72 = or u32 %27, %71
    %73 = const i32 23
    %74 = bitcast i32 %73 to u32
    %75 = const u32 32
    %76 = icmp ult u32 %74, %75
    condbr %76, bb4(%22, %23, %24, %25, %26, %72), bb9
bb4(%28: u32, %29: u32, %30: u32, %31: u32, %32: u32, %33: u32):
    %77 = const u32 2
    %78 = const i32 23
    %79 = shl u32 %77, %78
    %80 = or u32 %33, %79
    %81 = const i32 22
    %82 = bitcast i32 %81 to u32
    %83 = const u32 32
    %84 = icmp ult u32 %82, %83
    condbr %84, bb5(%28, %29, %30, %31, %32, %80), bb9
bb5(%34: u32, %35: u32, %36: u32, %37: u32, %38: u32, %39: u32):
    %85 = const i32 22
    %86 = shl u32 %34, %85
    %87 = or u32 %39, %86
    %88 = const i32 15
    %89 = bitcast i32 %88 to u32
    %90 = const u32 32
    %91 = icmp ult u32 %89, %90
    condbr %91, bb6(%35, %36, %37, %38, %87), bb9
bb6(%40: u32, %41: u32, %42: u32, %43: u32, %44: u32):
    %92 = const i32 15
    %93 = shl u32 %40, %92
    %94 = or u32 %44, %93
    %95 = const i32 10
    %96 = bitcast i32 %95 to u32
    %97 = const u32 32
    %98 = icmp ult u32 %96, %97
    condbr %98, bb7(%41, %42, %43, %94), bb9
bb7(%45: u32, %46: u32, %47: u32, %48: u32):
    %99 = const i32 10
    %100 = shl u32 %45, %99
    %101 = or u32 %48, %100
    %102 = const i32 5
    %103 = bitcast i32 %102 to u32
    %104 = const u32 32
    %105 = icmp ult u32 %103, %104
    condbr %105, bb8(%46, %47, %101), bb9
bb8(%49: u32, %50: u32, %51: u32):
    %106 = const i32 5
    %107 = shl u32 %49, %106
    %108 = or u32 %51, %107
    %109 = or u32 %108, %50
    ret %109
bb9:
    unreachable
}
"#;

// ═══════════════════════════════════════════════════════════════════════════
// Embedded MIR-closure emits — encoding_mem.rs addressing modes
// ═══════════════════════════════════════════════════════════════════════════

/// VERBATIM MIR-closure emit of the production `encode_ldr_str_unsigned_offset`
/// + `check_reg` + `check_imm12` (encoding_mem.rs; `?` -> explicit match in
///   the slice — pinned frontend limit, see module-header MODELED BOUNDARIES).
///   Emit reported: 7220 bytes; 3 closure member(s); validate_module = 14
///   error(s) (all the const-shift spelling class); re-parse OK. NO externs.
///   Slice: tests/slices/trust_memaddr_slice.rs.
///   Regen: trust_ir_mir trust_memaddr_slice.rs --crate-type=lib
///   --mir-emit-closure encode_ldr_str_unsigned_offset <out.tir>
const LDR_STR_UNSIGNED_OFFSET_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_ldr_str_unsigned_offset"

functy.0 = (ptr, u8, bool, u8, u16, u8, u8) -> ()

functy.1 = (ptr, u8, u8) -> ()

functy.2 = (ptr, u16) -> ()

fn @encode_ldr_str_unsigned_offset(functy.0) {
bb0(%0: ptr, %1: u8, %2: bool, %3: u8, %4: u16, %5: u8, %6: u8):
    %63 = alloca i8, align 1
    %64 = alloca i8, align 1
    %65 = alloca (i32, i32), align 4
    %66 = alloca (i32, i32), align 4
    %67 = alloca (i32, i32), align 4
    %68 = alloca (i32, i32), align 4
    %69 = alloca (i32, i32), align 4
    %70 = alloca (i32, i32), align 4
    store u8 %1, ptr %63
    store u8 %3, ptr %64
    %71 = const u8 31
    call @func.1(%65, %5, %71)
    br bb1(%2, %4, %5, %6)
bb1(%7: bool, %8: u16, %9: u8, %10: u8):
    %72 = load i8, ptr %65
    %73 = const i8 6
    %74 = icmp eq i8 %72, %73
    %75 = const i64 0
    %76 = const i64 1
    %77 = select i64 %74, %75, %76
    switch %77 [ 0: bb3(%7, %8, %9, %10) 1: bb4 default: bb2 ]
bb2:
    unreachable
bb3(%11: bool, %12: u16, %13: u8, %14: u8):
    %78 = const u8 31
    call @func.1(%67, %14, %78)
    br bb5(%11, %12, %13, %14)
bb4:
    %79 = load i32, ptr %65
    store i32 %79, ptr %66
    %80 = const i64 4
    %81 = gep i8, ptr %65, %80
    %82 = const i64 4
    %83 = gep i8, ptr %66, %82
    %84 = load i32, ptr %81
    store i32 %84, ptr %83
    %85 = load i32, ptr %66
    store i32 %85, ptr %0
    %86 = const i64 4
    %87 = gep i8, ptr %66, %86
    %88 = const i64 4
    %89 = gep i8, ptr %0, %88
    %90 = load i32, ptr %87
    store i32 %90, ptr %89
    br bb18
bb5(%15: bool, %16: u16, %17: u8, %18: u8):
    %91 = load i8, ptr %67
    %92 = const i8 6
    %93 = icmp eq i8 %91, %92
    %94 = const i64 0
    %95 = const i64 1
    %96 = select i64 %93, %94, %95
    switch %96 [ 0: bb6(%15, %16, %17, %18) 1: bb7 default: bb2 ]
bb6(%19: bool, %20: u16, %21: u8, %22: u8):
    call @func.2(%69, %20)
    br bb8(%19, %20, %21, %22)
bb7:
    %97 = load i32, ptr %67
    store i32 %97, ptr %68
    %98 = const i64 4
    %99 = gep i8, ptr %67, %98
    %100 = const i64 4
    %101 = gep i8, ptr %68, %100
    %102 = load i32, ptr %99
    store i32 %102, ptr %101
    %103 = load i32, ptr %68
    store i32 %103, ptr %0
    %104 = const i64 4
    %105 = gep i8, ptr %68, %104
    %106 = const i64 4
    %107 = gep i8, ptr %0, %106
    %108 = load i32, ptr %105
    store i32 %108, ptr %107
    br bb18
bb8(%23: bool, %24: u16, %25: u8, %26: u8):
    %109 = load i8, ptr %69
    %110 = const i8 6
    %111 = icmp eq i8 %109, %110
    %112 = const i64 0
    %113 = const i64 1
    %114 = select i64 %111, %112, %113
    switch %114 [ 0: bb9(%23, %24, %25, %26) 1: bb10 default: bb2 ]
bb9(%27: bool, %28: u16, %29: u8, %30: u8):
    %115 = const u32 0
    %116 = load i8, ptr %63
    %117 = sext i8 %116 to i64
    %118 = trunc i64 %117 to u32
    %119 = const i32 30
    %120 = bitcast i32 %119 to u32
    %121 = const u32 32
    %122 = icmp ult u32 %120, %121
    condbr %122, bb11(%27, %28, %29, %30, %115, %118), bb19
bb10:
    %123 = load i32, ptr %69
    store i32 %123, ptr %70
    %124 = const i64 4
    %125 = gep i8, ptr %69, %124
    %126 = const i64 4
    %127 = gep i8, ptr %70, %126
    %128 = load i32, ptr %125
    store i32 %128, ptr %127
    %129 = load i32, ptr %70
    store i32 %129, ptr %0
    %130 = const i64 4
    %131 = gep i8, ptr %70, %130
    %132 = const i64 4
    %133 = gep i8, ptr %0, %132
    %134 = load i32, ptr %131
    store i32 %134, ptr %133
    br bb18
bb11(%31: bool, %32: u16, %33: u8, %34: u8, %35: u32, %36: u32):
    %135 = const i32 30
    %136 = shl u32 %36, %135
    %137 = or u32 %35, %136
    %138 = const i32 27
    %139 = bitcast i32 %138 to u32
    %140 = const u32 32
    %141 = icmp ult u32 %139, %140
    condbr %141, bb12(%31, %32, %33, %34, %137), bb19
bb12(%37: bool, %38: u16, %39: u8, %40: u8, %41: u32):
    %142 = const u32 7
    %143 = const i32 27
    %144 = shl u32 %142, %143
    %145 = or u32 %41, %144
    %146 = const u32 1
    %147 = const u32 0
    %148 = select u32 %37, %146, %147
    %149 = const i32 26
    %150 = bitcast i32 %149 to u32
    %151 = const u32 32
    %152 = icmp ult u32 %150, %151
    condbr %152, bb13(%38, %39, %40, %145, %148), bb19
bb13(%42: u16, %43: u8, %44: u8, %45: u32, %46: u32):
    %153 = const i32 26
    %154 = shl u32 %46, %153
    %155 = or u32 %45, %154
    %156 = const i32 24
    %157 = bitcast i32 %156 to u32
    %158 = const u32 32
    %159 = icmp ult u32 %157, %158
    condbr %159, bb14(%42, %43, %44, %155), bb19
bb14(%47: u16, %48: u8, %49: u8, %50: u32):
    %160 = const u32 1
    %161 = const i32 24
    %162 = shl u32 %160, %161
    %163 = or u32 %50, %162
    %164 = load i8, ptr %64
    %165 = sext i8 %164 to i64
    %166 = trunc i64 %165 to u32
    %167 = const i32 22
    %168 = bitcast i32 %167 to u32
    %169 = const u32 32
    %170 = icmp ult u32 %168, %169
    condbr %170, bb15(%47, %48, %49, %163, %166), bb19
bb15(%51: u16, %52: u8, %53: u8, %54: u32, %55: u32):
    %171 = const i32 22
    %172 = shl u32 %55, %171
    %173 = or u32 %54, %172
    %174 = zext u16 %51 to u32
    %175 = const i32 10
    %176 = bitcast i32 %175 to u32
    %177 = const u32 32
    %178 = icmp ult u32 %176, %177
    condbr %178, bb16(%52, %53, %173, %174), bb19
bb16(%56: u8, %57: u8, %58: u32, %59: u32):
    %179 = const i32 10
    %180 = shl u32 %59, %179
    %181 = or u32 %58, %180
    %182 = zext u8 %56 to u32
    %183 = const i32 5
    %184 = bitcast i32 %183 to u32
    %185 = const u32 32
    %186 = icmp ult u32 %184, %185
    condbr %186, bb17(%57, %181, %182), bb19
bb17(%60: u8, %61: u32, %62: u32):
    %187 = const i32 5
    %188 = shl u32 %62, %187
    %189 = or u32 %61, %188
    %190 = zext u8 %60 to u32
    %191 = or u32 %189, %190
    %192 = const i64 4
    %193 = gep i8, ptr %0, %192
    store u32 %191, ptr %193
    %194 = const i8 6
    store i8 %194, ptr %0
    br bb18
bb18:
    ret
bb19:
    unreachable
}

fn @check_reg(functy.1) {
bb0(%0: ptr, %1: u8, %2: u8):
    %5 = alloca (i32, i32), align 4
    %6 = icmp ugt u8 %1, %2
    condbr %6, bb1(%1, %2), bb2
bb1(%3: u8, %4: u8):
    %7 = const i64 1
    %8 = gep i8, ptr %5, %7
    store u8 %3, ptr %8
    %9 = const i64 2
    %10 = gep i8, ptr %5, %9
    store u8 %4, ptr %10
    %11 = const i8 0
    store i8 %11, ptr %5
    %12 = load i32, ptr %5
    store i32 %12, ptr %0
    %13 = const i64 4
    %14 = gep i8, ptr %5, %13
    %15 = const i64 4
    %16 = gep i8, ptr %0, %15
    %17 = load i32, ptr %14
    store i32 %17, ptr %16
    br bb3
bb2:
    %18 = const i8 6
    store i8 %18, ptr %0
    br bb3
bb3:
    ret
}

fn @check_imm12(functy.2) {
bb0(%0: ptr, %1: u16):
    %3 = alloca (i32, i32), align 4
    %4 = const u16 4095
    %5 = icmp ugt u16 %1, %4
    condbr %5, bb1(%1), bb2
bb1(%2: u16):
    %6 = const i64 2
    %7 = gep i8, ptr %3, %6
    store u16 %2, ptr %7
    %8 = const i8 1
    store i8 %8, ptr %3
    %9 = load i32, ptr %3
    store i32 %9, ptr %0
    %10 = const i64 4
    %11 = gep i8, ptr %3, %10
    %12 = const i64 4
    %13 = gep i8, ptr %0, %12
    %14 = load i32, ptr %11
    store i32 %14, ptr %13
    br bb3
bb2:
    %15 = const i8 6
    store i8 %15, ptr %0
    br bb3
bb3:
    ret
}
"#;

/// VERBATIM MIR-closure emit of the production `encode_ldr_str_pre_index`
/// + `check_reg` + `check_imm9` (encoding_mem.rs; `?` -> match and
///   RangeInclusive::contains -> explicit comparisons in check_imm9 — pinned
///   frontend limits). Emit reported: 7384 bytes; 3 closure member(s);
///   validate_module = 14 error(s) (const-shift class); re-parse OK.
///   Slice: tests/slices/trust_memaddr_slice.rs.
///   Regen: trust_ir_mir trust_memaddr_slice.rs --crate-type=lib
///   --mir-emit-closure encode_ldr_str_pre_index <out.tir>
const LDR_STR_PRE_INDEX_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_ldr_str_pre_index"

functy.0 = (ptr, u8, bool, u8, i16, u8, u8) -> ()

functy.1 = (ptr, u8, u8) -> ()

functy.2 = (ptr, i16) -> ()

fn @encode_ldr_str_pre_index(functy.0) {
bb0(%0: ptr, %1: u8, %2: bool, %3: u8, %4: i16, %5: u8, %6: u8):
    %62 = alloca i8, align 1
    %63 = alloca i8, align 1
    %64 = alloca (i32, i32), align 4
    %65 = alloca (i32, i32), align 4
    %66 = alloca (i32, i32), align 4
    %67 = alloca (i32, i32), align 4
    %68 = alloca (i32, i32), align 4
    %69 = alloca (i32, i32), align 4
    store u8 %1, ptr %62
    store u8 %3, ptr %63
    %70 = const u8 31
    call @func.1(%64, %5, %70)
    br bb1(%2, %4, %5, %6)
bb1(%7: bool, %8: i16, %9: u8, %10: u8):
    %71 = load i8, ptr %64
    %72 = const i8 6
    %73 = icmp eq i8 %71, %72
    %74 = const i64 0
    %75 = const i64 1
    %76 = select i64 %73, %74, %75
    switch %76 [ 0: bb3(%7, %8, %9, %10) 1: bb4 default: bb2 ]
bb2:
    unreachable
bb3(%11: bool, %12: i16, %13: u8, %14: u8):
    %77 = const u8 31
    call @func.1(%66, %14, %77)
    br bb5(%11, %12, %13, %14)
bb4:
    %78 = load i32, ptr %64
    store i32 %78, ptr %65
    %79 = const i64 4
    %80 = gep i8, ptr %64, %79
    %81 = const i64 4
    %82 = gep i8, ptr %65, %81
    %83 = load i32, ptr %80
    store i32 %83, ptr %82
    %84 = load i32, ptr %65
    store i32 %84, ptr %0
    %85 = const i64 4
    %86 = gep i8, ptr %65, %85
    %87 = const i64 4
    %88 = gep i8, ptr %0, %87
    %89 = load i32, ptr %86
    store i32 %89, ptr %88
    br bb18
bb5(%15: bool, %16: i16, %17: u8, %18: u8):
    %90 = load i8, ptr %66
    %91 = const i8 6
    %92 = icmp eq i8 %90, %91
    %93 = const i64 0
    %94 = const i64 1
    %95 = select i64 %92, %93, %94
    switch %95 [ 0: bb6(%15, %16, %17, %18) 1: bb7 default: bb2 ]
bb6(%19: bool, %20: i16, %21: u8, %22: u8):
    call @func.2(%68, %20)
    br bb8(%19, %20, %21, %22)
bb7:
    %96 = load i32, ptr %66
    store i32 %96, ptr %67
    %97 = const i64 4
    %98 = gep i8, ptr %66, %97
    %99 = const i64 4
    %100 = gep i8, ptr %67, %99
    %101 = load i32, ptr %98
    store i32 %101, ptr %100
    %102 = load i32, ptr %67
    store i32 %102, ptr %0
    %103 = const i64 4
    %104 = gep i8, ptr %67, %103
    %105 = const i64 4
    %106 = gep i8, ptr %0, %105
    %107 = load i32, ptr %104
    store i32 %107, ptr %106
    br bb18
bb8(%23: bool, %24: i16, %25: u8, %26: u8):
    %108 = load i8, ptr %68
    %109 = const i8 6
    %110 = icmp eq i8 %108, %109
    %111 = const i64 0
    %112 = const i64 1
    %113 = select i64 %110, %111, %112
    switch %113 [ 0: bb9(%23, %24, %25, %26) 1: bb10 default: bb2 ]
bb9(%27: bool, %28: i16, %29: u8, %30: u8):
    %114 = bitcast i16 %28 to u16
    %115 = const u16 511
    %116 = and u16 %114, %115
    %117 = zext u16 %116 to u32
    %118 = const u32 0
    %119 = load i8, ptr %62
    %120 = sext i8 %119 to i64
    %121 = trunc i64 %120 to u32
    %122 = const i32 30
    %123 = bitcast i32 %122 to u32
    %124 = const u32 32
    %125 = icmp ult u32 %123, %124
    condbr %125, bb11(%27, %29, %30, %117, %118, %121), bb19
bb10:
    %126 = load i32, ptr %68
    store i32 %126, ptr %69
    %127 = const i64 4
    %128 = gep i8, ptr %68, %127
    %129 = const i64 4
    %130 = gep i8, ptr %69, %129
    %131 = load i32, ptr %128
    store i32 %131, ptr %130
    %132 = load i32, ptr %69
    store i32 %132, ptr %0
    %133 = const i64 4
    %134 = gep i8, ptr %69, %133
    %135 = const i64 4
    %136 = gep i8, ptr %0, %135
    %137 = load i32, ptr %134
    store i32 %137, ptr %136
    br bb18
bb11(%31: bool, %32: u8, %33: u8, %34: u32, %35: u32, %36: u32):
    %138 = const i32 30
    %139 = shl u32 %36, %138
    %140 = or u32 %35, %139
    %141 = const i32 27
    %142 = bitcast i32 %141 to u32
    %143 = const u32 32
    %144 = icmp ult u32 %142, %143
    condbr %144, bb12(%31, %32, %33, %34, %140), bb19
bb12(%37: bool, %38: u8, %39: u8, %40: u32, %41: u32):
    %145 = const u32 7
    %146 = const i32 27
    %147 = shl u32 %145, %146
    %148 = or u32 %41, %147
    %149 = const u32 1
    %150 = const u32 0
    %151 = select u32 %37, %149, %150
    %152 = const i32 26
    %153 = bitcast i32 %152 to u32
    %154 = const u32 32
    %155 = icmp ult u32 %153, %154
    condbr %155, bb13(%38, %39, %40, %148, %151), bb19
bb13(%42: u8, %43: u8, %44: u32, %45: u32, %46: u32):
    %156 = const i32 26
    %157 = shl u32 %46, %156
    %158 = or u32 %45, %157
    %159 = load i8, ptr %63
    %160 = sext i8 %159 to i64
    %161 = trunc i64 %160 to u32
    %162 = const i32 22
    %163 = bitcast i32 %162 to u32
    %164 = const u32 32
    %165 = icmp ult u32 %163, %164
    condbr %165, bb14(%42, %43, %44, %158, %161), bb19
bb14(%47: u8, %48: u8, %49: u32, %50: u32, %51: u32):
    %166 = const i32 22
    %167 = shl u32 %51, %166
    %168 = or u32 %50, %167
    %169 = const i32 12
    %170 = bitcast i32 %169 to u32
    %171 = const u32 32
    %172 = icmp ult u32 %170, %171
    condbr %172, bb15(%47, %48, %49, %168), bb19
bb15(%52: u8, %53: u8, %54: u32, %55: u32):
    %173 = const i32 12
    %174 = shl u32 %54, %173
    %175 = or u32 %55, %174
    %176 = const i32 10
    %177 = bitcast i32 %176 to u32
    %178 = const u32 32
    %179 = icmp ult u32 %177, %178
    condbr %179, bb16(%52, %53, %175), bb19
bb16(%56: u8, %57: u8, %58: u32):
    %180 = const u32 3
    %181 = const i32 10
    %182 = shl u32 %180, %181
    %183 = or u32 %58, %182
    %184 = zext u8 %56 to u32
    %185 = const i32 5
    %186 = bitcast i32 %185 to u32
    %187 = const u32 32
    %188 = icmp ult u32 %186, %187
    condbr %188, bb17(%57, %183, %184), bb19
bb17(%59: u8, %60: u32, %61: u32):
    %189 = const i32 5
    %190 = shl u32 %61, %189
    %191 = or u32 %60, %190
    %192 = zext u8 %59 to u32
    %193 = or u32 %191, %192
    %194 = const i64 4
    %195 = gep i8, ptr %0, %194
    store u32 %193, ptr %195
    %196 = const i8 6
    store i8 %196, ptr %0
    br bb18
bb18:
    ret
bb19:
    unreachable
}

fn @check_reg(functy.1) {
bb0(%0: ptr, %1: u8, %2: u8):
    %5 = alloca (i32, i32), align 4
    %6 = icmp ugt u8 %1, %2
    condbr %6, bb1(%1, %2), bb2
bb1(%3: u8, %4: u8):
    %7 = const i64 1
    %8 = gep i8, ptr %5, %7
    store u8 %3, ptr %8
    %9 = const i64 2
    %10 = gep i8, ptr %5, %9
    store u8 %4, ptr %10
    %11 = const i8 0
    store i8 %11, ptr %5
    %12 = load i32, ptr %5
    store i32 %12, ptr %0
    %13 = const i64 4
    %14 = gep i8, ptr %5, %13
    %15 = const i64 4
    %16 = gep i8, ptr %0, %15
    %17 = load i32, ptr %14
    store i32 %17, ptr %16
    br bb3
bb2:
    %18 = const i8 6
    store i8 %18, ptr %0
    br bb3
bb3:
    ret
}

fn @check_imm9(functy.2) {
bb0(%0: ptr, %1: i16):
    %4 = alloca (i32, i32), align 4
    %5 = const i16 -256
    %6 = icmp slt i16 %1, %5
    condbr %6, bb2(%1), bb1(%1)
bb1(%2: i16):
    %7 = const i16 255
    %8 = icmp sgt i16 %2, %7
    condbr %8, bb2(%2), bb3
bb2(%3: i16):
    %9 = const i64 2
    %10 = gep i8, ptr %4, %9
    store i16 %3, ptr %10
    %11 = const i8 2
    store i8 %11, ptr %4
    %12 = load i32, ptr %4
    store i32 %12, ptr %0
    %13 = const i64 4
    %14 = gep i8, ptr %4, %13
    %15 = const i64 4
    %16 = gep i8, ptr %0, %15
    %17 = load i32, ptr %14
    store i32 %17, ptr %16
    br bb4
bb3:
    %18 = const i8 6
    store i8 %18, ptr %0
    br bb4
bb4:
    ret
}
"#;

/// VERBATIM MIR-closure emit of the production `encode_ldr_str_post_index`
/// + `check_reg` + `check_imm9` (encoding_mem.rs; same modeled rewrites as
///   pre-index). Emit reported: 7386 bytes; 3 closure member(s);
///   validate_module = 14 error(s) (const-shift class); re-parse OK.
///   Slice: tests/slices/trust_memaddr_slice.rs.
///   Regen: trust_ir_mir trust_memaddr_slice.rs --crate-type=lib
///   --mir-emit-closure encode_ldr_str_post_index <out.tir>
const LDR_STR_POST_INDEX_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_ldr_str_post_index"

functy.0 = (ptr, u8, bool, u8, i16, u8, u8) -> ()

functy.1 = (ptr, u8, u8) -> ()

functy.2 = (ptr, i16) -> ()

fn @encode_ldr_str_post_index(functy.0) {
bb0(%0: ptr, %1: u8, %2: bool, %3: u8, %4: i16, %5: u8, %6: u8):
    %62 = alloca i8, align 1
    %63 = alloca i8, align 1
    %64 = alloca (i32, i32), align 4
    %65 = alloca (i32, i32), align 4
    %66 = alloca (i32, i32), align 4
    %67 = alloca (i32, i32), align 4
    %68 = alloca (i32, i32), align 4
    %69 = alloca (i32, i32), align 4
    store u8 %1, ptr %62
    store u8 %3, ptr %63
    %70 = const u8 31
    call @func.1(%64, %5, %70)
    br bb1(%2, %4, %5, %6)
bb1(%7: bool, %8: i16, %9: u8, %10: u8):
    %71 = load i8, ptr %64
    %72 = const i8 6
    %73 = icmp eq i8 %71, %72
    %74 = const i64 0
    %75 = const i64 1
    %76 = select i64 %73, %74, %75
    switch %76 [ 0: bb3(%7, %8, %9, %10) 1: bb4 default: bb2 ]
bb2:
    unreachable
bb3(%11: bool, %12: i16, %13: u8, %14: u8):
    %77 = const u8 31
    call @func.1(%66, %14, %77)
    br bb5(%11, %12, %13, %14)
bb4:
    %78 = load i32, ptr %64
    store i32 %78, ptr %65
    %79 = const i64 4
    %80 = gep i8, ptr %64, %79
    %81 = const i64 4
    %82 = gep i8, ptr %65, %81
    %83 = load i32, ptr %80
    store i32 %83, ptr %82
    %84 = load i32, ptr %65
    store i32 %84, ptr %0
    %85 = const i64 4
    %86 = gep i8, ptr %65, %85
    %87 = const i64 4
    %88 = gep i8, ptr %0, %87
    %89 = load i32, ptr %86
    store i32 %89, ptr %88
    br bb18
bb5(%15: bool, %16: i16, %17: u8, %18: u8):
    %90 = load i8, ptr %66
    %91 = const i8 6
    %92 = icmp eq i8 %90, %91
    %93 = const i64 0
    %94 = const i64 1
    %95 = select i64 %92, %93, %94
    switch %95 [ 0: bb6(%15, %16, %17, %18) 1: bb7 default: bb2 ]
bb6(%19: bool, %20: i16, %21: u8, %22: u8):
    call @func.2(%68, %20)
    br bb8(%19, %20, %21, %22)
bb7:
    %96 = load i32, ptr %66
    store i32 %96, ptr %67
    %97 = const i64 4
    %98 = gep i8, ptr %66, %97
    %99 = const i64 4
    %100 = gep i8, ptr %67, %99
    %101 = load i32, ptr %98
    store i32 %101, ptr %100
    %102 = load i32, ptr %67
    store i32 %102, ptr %0
    %103 = const i64 4
    %104 = gep i8, ptr %67, %103
    %105 = const i64 4
    %106 = gep i8, ptr %0, %105
    %107 = load i32, ptr %104
    store i32 %107, ptr %106
    br bb18
bb8(%23: bool, %24: i16, %25: u8, %26: u8):
    %108 = load i8, ptr %68
    %109 = const i8 6
    %110 = icmp eq i8 %108, %109
    %111 = const i64 0
    %112 = const i64 1
    %113 = select i64 %110, %111, %112
    switch %113 [ 0: bb9(%23, %24, %25, %26) 1: bb10 default: bb2 ]
bb9(%27: bool, %28: i16, %29: u8, %30: u8):
    %114 = bitcast i16 %28 to u16
    %115 = const u16 511
    %116 = and u16 %114, %115
    %117 = zext u16 %116 to u32
    %118 = const u32 0
    %119 = load i8, ptr %62
    %120 = sext i8 %119 to i64
    %121 = trunc i64 %120 to u32
    %122 = const i32 30
    %123 = bitcast i32 %122 to u32
    %124 = const u32 32
    %125 = icmp ult u32 %123, %124
    condbr %125, bb11(%27, %29, %30, %117, %118, %121), bb19
bb10:
    %126 = load i32, ptr %68
    store i32 %126, ptr %69
    %127 = const i64 4
    %128 = gep i8, ptr %68, %127
    %129 = const i64 4
    %130 = gep i8, ptr %69, %129
    %131 = load i32, ptr %128
    store i32 %131, ptr %130
    %132 = load i32, ptr %69
    store i32 %132, ptr %0
    %133 = const i64 4
    %134 = gep i8, ptr %69, %133
    %135 = const i64 4
    %136 = gep i8, ptr %0, %135
    %137 = load i32, ptr %134
    store i32 %137, ptr %136
    br bb18
bb11(%31: bool, %32: u8, %33: u8, %34: u32, %35: u32, %36: u32):
    %138 = const i32 30
    %139 = shl u32 %36, %138
    %140 = or u32 %35, %139
    %141 = const i32 27
    %142 = bitcast i32 %141 to u32
    %143 = const u32 32
    %144 = icmp ult u32 %142, %143
    condbr %144, bb12(%31, %32, %33, %34, %140), bb19
bb12(%37: bool, %38: u8, %39: u8, %40: u32, %41: u32):
    %145 = const u32 7
    %146 = const i32 27
    %147 = shl u32 %145, %146
    %148 = or u32 %41, %147
    %149 = const u32 1
    %150 = const u32 0
    %151 = select u32 %37, %149, %150
    %152 = const i32 26
    %153 = bitcast i32 %152 to u32
    %154 = const u32 32
    %155 = icmp ult u32 %153, %154
    condbr %155, bb13(%38, %39, %40, %148, %151), bb19
bb13(%42: u8, %43: u8, %44: u32, %45: u32, %46: u32):
    %156 = const i32 26
    %157 = shl u32 %46, %156
    %158 = or u32 %45, %157
    %159 = load i8, ptr %63
    %160 = sext i8 %159 to i64
    %161 = trunc i64 %160 to u32
    %162 = const i32 22
    %163 = bitcast i32 %162 to u32
    %164 = const u32 32
    %165 = icmp ult u32 %163, %164
    condbr %165, bb14(%42, %43, %44, %158, %161), bb19
bb14(%47: u8, %48: u8, %49: u32, %50: u32, %51: u32):
    %166 = const i32 22
    %167 = shl u32 %51, %166
    %168 = or u32 %50, %167
    %169 = const i32 12
    %170 = bitcast i32 %169 to u32
    %171 = const u32 32
    %172 = icmp ult u32 %170, %171
    condbr %172, bb15(%47, %48, %49, %168), bb19
bb15(%52: u8, %53: u8, %54: u32, %55: u32):
    %173 = const i32 12
    %174 = shl u32 %54, %173
    %175 = or u32 %55, %174
    %176 = const i32 10
    %177 = bitcast i32 %176 to u32
    %178 = const u32 32
    %179 = icmp ult u32 %177, %178
    condbr %179, bb16(%52, %53, %175), bb19
bb16(%56: u8, %57: u8, %58: u32):
    %180 = const u32 1
    %181 = const i32 10
    %182 = shl u32 %180, %181
    %183 = or u32 %58, %182
    %184 = zext u8 %56 to u32
    %185 = const i32 5
    %186 = bitcast i32 %185 to u32
    %187 = const u32 32
    %188 = icmp ult u32 %186, %187
    condbr %188, bb17(%57, %183, %184), bb19
bb17(%59: u8, %60: u32, %61: u32):
    %189 = const i32 5
    %190 = shl u32 %61, %189
    %191 = or u32 %60, %190
    %192 = zext u8 %59 to u32
    %193 = or u32 %191, %192
    %194 = const i64 4
    %195 = gep i8, ptr %0, %194
    store u32 %193, ptr %195
    %196 = const i8 6
    store i8 %196, ptr %0
    br bb18
bb18:
    ret
bb19:
    unreachable
}

fn @check_reg(functy.1) {
bb0(%0: ptr, %1: u8, %2: u8):
    %5 = alloca (i32, i32), align 4
    %6 = icmp ugt u8 %1, %2
    condbr %6, bb1(%1, %2), bb2
bb1(%3: u8, %4: u8):
    %7 = const i64 1
    %8 = gep i8, ptr %5, %7
    store u8 %3, ptr %8
    %9 = const i64 2
    %10 = gep i8, ptr %5, %9
    store u8 %4, ptr %10
    %11 = const i8 0
    store i8 %11, ptr %5
    %12 = load i32, ptr %5
    store i32 %12, ptr %0
    %13 = const i64 4
    %14 = gep i8, ptr %5, %13
    %15 = const i64 4
    %16 = gep i8, ptr %0, %15
    %17 = load i32, ptr %14
    store i32 %17, ptr %16
    br bb3
bb2:
    %18 = const i8 6
    store i8 %18, ptr %0
    br bb3
bb3:
    ret
}

fn @check_imm9(functy.2) {
bb0(%0: ptr, %1: i16):
    %4 = alloca (i32, i32), align 4
    %5 = const i16 -256
    %6 = icmp slt i16 %1, %5
    condbr %6, bb2(%1), bb1(%1)
bb1(%2: i16):
    %7 = const i16 255
    %8 = icmp sgt i16 %2, %7
    condbr %8, bb2(%2), bb3
bb2(%3: i16):
    %9 = const i64 2
    %10 = gep i8, ptr %4, %9
    store i16 %3, ptr %10
    %11 = const i8 2
    store i8 %11, ptr %4
    %12 = load i32, ptr %4
    store i32 %12, ptr %0
    %13 = const i64 4
    %14 = gep i8, ptr %4, %13
    %15 = const i64 4
    %16 = gep i8, ptr %0, %15
    %17 = load i32, ptr %14
    store i32 %17, ptr %16
    br bb4
bb3:
    %18 = const i8 6
    store i8 %18, ptr %0
    br bb4
bb4:
    ret
}
"#;

/// VERBATIM MIR-closure emit of the production `encode_ldr_str_register`
/// + `check_reg` (encoding_mem.rs; `?` -> match). Emit reported: 8003 bytes;
///   2 closure member(s); validate_module = 20 error(s) (const-shift class);
///   re-parse OK. Operand enums (LoadStoreSize/LoadStoreOp/RegExtend) pass as
///   their u8 tags per the frontend's faithful scalar-tag enum ABI.
///   Slice: tests/slices/trust_memaddr_slice.rs.
///   Regen: trust_ir_mir trust_memaddr_slice.rs --crate-type=lib
///   --mir-emit-closure encode_ldr_str_register <out.tir>
const LDR_STR_REGISTER_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_ldr_str_register"

functy.0 = (ptr, u8, bool, u8, u8, u8, bool, u8, u8) -> ()

functy.1 = (ptr, u8, u8) -> ()

fn @encode_ldr_str_register(functy.0) {
bb0(%0: ptr, %1: u8, %2: bool, %3: u8, %4: u8, %5: u8, %6: bool, %7: u8, %8: u8):
    %89 = alloca i8, align 1
    %90 = alloca i8, align 1
    %91 = alloca i8, align 1
    %92 = alloca (i32, i32), align 4
    %93 = alloca (i32, i32), align 4
    %94 = alloca (i32, i32), align 4
    %95 = alloca (i32, i32), align 4
    %96 = alloca (i32, i32), align 4
    %97 = alloca (i32, i32), align 4
    store u8 %1, ptr %89
    store u8 %3, ptr %90
    store u8 %5, ptr %91
    %98 = const u8 31
    call @func.1(%92, %4, %98)
    br bb1(%2, %4, %6, %7, %8)
bb1(%9: bool, %10: u8, %11: bool, %12: u8, %13: u8):
    %99 = load i8, ptr %92
    %100 = const i8 6
    %101 = icmp eq i8 %99, %100
    %102 = const i64 0
    %103 = const i64 1
    %104 = select i64 %101, %102, %103
    switch %104 [ 0: bb3(%9, %10, %11, %12, %13) 1: bb4 default: bb2 ]
bb2:
    unreachable
bb3(%14: bool, %15: u8, %16: bool, %17: u8, %18: u8):
    %105 = const u8 31
    call @func.1(%94, %17, %105)
    br bb5(%14, %15, %16, %17, %18)
bb4:
    %106 = load i32, ptr %92
    store i32 %106, ptr %93
    %107 = const i64 4
    %108 = gep i8, ptr %92, %107
    %109 = const i64 4
    %110 = gep i8, ptr %93, %109
    %111 = load i32, ptr %108
    store i32 %111, ptr %110
    %112 = load i32, ptr %93
    store i32 %112, ptr %0
    %113 = const i64 4
    %114 = gep i8, ptr %93, %113
    %115 = const i64 4
    %116 = gep i8, ptr %0, %115
    %117 = load i32, ptr %114
    store i32 %117, ptr %116
    br bb21
bb5(%19: bool, %20: u8, %21: bool, %22: u8, %23: u8):
    %118 = load i8, ptr %94
    %119 = const i8 6
    %120 = icmp eq i8 %118, %119
    %121 = const i64 0
    %122 = const i64 1
    %123 = select i64 %120, %121, %122
    switch %123 [ 0: bb6(%19, %20, %21, %22, %23) 1: bb7 default: bb2 ]
bb6(%24: bool, %25: u8, %26: bool, %27: u8, %28: u8):
    %124 = const u8 31
    call @func.1(%96, %28, %124)
    br bb8(%24, %25, %26, %27, %28)
bb7:
    %125 = load i32, ptr %94
    store i32 %125, ptr %95
    %126 = const i64 4
    %127 = gep i8, ptr %94, %126
    %128 = const i64 4
    %129 = gep i8, ptr %95, %128
    %130 = load i32, ptr %127
    store i32 %130, ptr %129
    %131 = load i32, ptr %95
    store i32 %131, ptr %0
    %132 = const i64 4
    %133 = gep i8, ptr %95, %132
    %134 = const i64 4
    %135 = gep i8, ptr %0, %134
    %136 = load i32, ptr %133
    store i32 %136, ptr %135
    br bb21
bb8(%29: bool, %30: u8, %31: bool, %32: u8, %33: u8):
    %137 = load i8, ptr %96
    %138 = const i8 6
    %139 = icmp eq i8 %137, %138
    %140 = const i64 0
    %141 = const i64 1
    %142 = select i64 %139, %140, %141
    switch %142 [ 0: bb9(%29, %30, %31, %32, %33) 1: bb10 default: bb2 ]
bb9(%34: bool, %35: u8, %36: bool, %37: u8, %38: u8):
    %143 = const u32 0
    %144 = load i8, ptr %89
    %145 = sext i8 %144 to i64
    %146 = trunc i64 %145 to u32
    %147 = const i32 30
    %148 = bitcast i32 %147 to u32
    %149 = const u32 32
    %150 = icmp ult u32 %148, %149
    condbr %150, bb11(%34, %35, %36, %37, %38, %143, %146), bb22
bb10:
    %151 = load i32, ptr %96
    store i32 %151, ptr %97
    %152 = const i64 4
    %153 = gep i8, ptr %96, %152
    %154 = const i64 4
    %155 = gep i8, ptr %97, %154
    %156 = load i32, ptr %153
    store i32 %156, ptr %155
    %157 = load i32, ptr %97
    store i32 %157, ptr %0
    %158 = const i64 4
    %159 = gep i8, ptr %97, %158
    %160 = const i64 4
    %161 = gep i8, ptr %0, %160
    %162 = load i32, ptr %159
    store i32 %162, ptr %161
    br bb21
bb11(%39: bool, %40: u8, %41: bool, %42: u8, %43: u8, %44: u32, %45: u32):
    %163 = const i32 30
    %164 = shl u32 %45, %163
    %165 = or u32 %44, %164
    %166 = const i32 27
    %167 = bitcast i32 %166 to u32
    %168 = const u32 32
    %169 = icmp ult u32 %167, %168
    condbr %169, bb12(%39, %40, %41, %42, %43, %165), bb22
bb12(%46: bool, %47: u8, %48: bool, %49: u8, %50: u8, %51: u32):
    %170 = const u32 7
    %171 = const i32 27
    %172 = shl u32 %170, %171
    %173 = or u32 %51, %172
    %174 = const u32 1
    %175 = const u32 0
    %176 = select u32 %46, %174, %175
    %177 = const i32 26
    %178 = bitcast i32 %177 to u32
    %179 = const u32 32
    %180 = icmp ult u32 %178, %179
    condbr %180, bb13(%47, %48, %49, %50, %173, %176), bb22
bb13(%52: u8, %53: bool, %54: u8, %55: u8, %56: u32, %57: u32):
    %181 = const i32 26
    %182 = shl u32 %57, %181
    %183 = or u32 %56, %182
    %184 = load i8, ptr %90
    %185 = sext i8 %184 to i64
    %186 = trunc i64 %185 to u32
    %187 = const i32 22
    %188 = bitcast i32 %187 to u32
    %189 = const u32 32
    %190 = icmp ult u32 %188, %189
    condbr %190, bb14(%52, %53, %54, %55, %183, %186), bb22
bb14(%58: u8, %59: bool, %60: u8, %61: u8, %62: u32, %63: u32):
    %191 = const i32 22
    %192 = shl u32 %63, %191
    %193 = or u32 %62, %192
    %194 = const i32 21
    %195 = bitcast i32 %194 to u32
    %196 = const u32 32
    %197 = icmp ult u32 %195, %196
    condbr %197, bb15(%58, %59, %60, %61, %193), bb22
bb15(%64: u8, %65: bool, %66: u8, %67: u8, %68: u32):
    %198 = const u32 1
    %199 = const i32 21
    %200 = shl u32 %198, %199
    %201 = or u32 %68, %200
    %202 = zext u8 %64 to u32
    %203 = const i32 16
    %204 = bitcast i32 %203 to u32
    %205 = const u32 32
    %206 = icmp ult u32 %204, %205
    condbr %206, bb16(%65, %66, %67, %201, %202), bb22
bb16(%69: bool, %70: u8, %71: u8, %72: u32, %73: u32):
    %207 = const i32 16
    %208 = shl u32 %73, %207
    %209 = or u32 %72, %208
    %210 = load i8, ptr %91
    %211 = sext i8 %210 to i64
    %212 = trunc i64 %211 to u32
    %213 = const i32 13
    %214 = bitcast i32 %213 to u32
    %215 = const u32 32
    %216 = icmp ult u32 %214, %215
    condbr %216, bb17(%69, %70, %71, %209, %212), bb22
bb17(%74: bool, %75: u8, %76: u8, %77: u32, %78: u32):
    %217 = const i32 13
    %218 = shl u32 %78, %217
    %219 = or u32 %77, %218
    %220 = const u32 1
    %221 = const u32 0
    %222 = select u32 %74, %220, %221
    %223 = const i32 12
    %224 = bitcast i32 %223 to u32
    %225 = const u32 32
    %226 = icmp ult u32 %224, %225
    condbr %226, bb18(%75, %76, %219, %222), bb22
bb18(%79: u8, %80: u8, %81: u32, %82: u32):
    %227 = const i32 12
    %228 = shl u32 %82, %227
    %229 = or u32 %81, %228
    %230 = const i32 10
    %231 = bitcast i32 %230 to u32
    %232 = const u32 32
    %233 = icmp ult u32 %231, %232
    condbr %233, bb19(%79, %80, %229), bb22
bb19(%83: u8, %84: u8, %85: u32):
    %234 = const u32 2
    %235 = const i32 10
    %236 = shl u32 %234, %235
    %237 = or u32 %85, %236
    %238 = zext u8 %83 to u32
    %239 = const i32 5
    %240 = bitcast i32 %239 to u32
    %241 = const u32 32
    %242 = icmp ult u32 %240, %241
    condbr %242, bb20(%84, %237, %238), bb22
bb20(%86: u8, %87: u32, %88: u32):
    %243 = const i32 5
    %244 = shl u32 %88, %243
    %245 = or u32 %87, %244
    %246 = zext u8 %86 to u32
    %247 = or u32 %245, %246
    %248 = const i64 4
    %249 = gep i8, ptr %0, %248
    store u32 %247, ptr %249
    %250 = const i8 6
    store i8 %250, ptr %0
    br bb21
bb21:
    ret
bb22:
    unreachable
}

fn @check_reg(functy.1) {
bb0(%0: ptr, %1: u8, %2: u8):
    %5 = alloca (i32, i32), align 4
    %6 = icmp ugt u8 %1, %2
    condbr %6, bb1(%1, %2), bb2
bb1(%3: u8, %4: u8):
    %7 = const i64 1
    %8 = gep i8, ptr %5, %7
    store u8 %3, ptr %8
    %9 = const i64 2
    %10 = gep i8, ptr %5, %9
    store u8 %4, ptr %10
    %11 = const i8 0
    store i8 %11, ptr %5
    %12 = load i32, ptr %5
    store i32 %12, ptr %0
    %13 = const i64 4
    %14 = gep i8, ptr %5, %13
    %15 = const i64 4
    %16 = gep i8, ptr %0, %15
    %17 = load i32, ptr %14
    store i32 %17, ptr %16
    br bb3
bb2:
    %18 = const i8 6
    store i8 %18, ptr %0
    br bb3
bb3:
    ret
}
"#;

/// VERBATIM MIR-closure emit of the production `encode_ldrsw_register`
/// + `check_reg` (encoding_mem.rs; `?` -> match). Emit reported: 6629 bytes;
///   2 closure member(s); validate_module = 18 error(s) (const-shift class);
///   re-parse OK. Slice: tests/slices/trust_memaddr_slice.rs.
///   Regen: trust_ir_mir trust_memaddr_slice.rs --crate-type=lib
///   --mir-emit-closure encode_ldrsw_register <out.tir>
const LDRSW_REGISTER_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_ldrsw_register"

functy.0 = (ptr, u8, u8, u8) -> ()

functy.1 = (ptr, u8, u8) -> ()

fn @encode_ldrsw_register(functy.0) {
bb0(%0: ptr, %1: u8, %2: u8, %3: u8):
    %54 = alloca (i32, i32), align 4
    %55 = alloca (i32, i32), align 4
    %56 = alloca (i32, i32), align 4
    %57 = alloca (i32, i32), align 4
    %58 = alloca (i32, i32), align 4
    %59 = alloca (i32, i32), align 4
    %60 = const u8 31
    call @func.1(%54, %1, %60)
    br bb1(%1, %2, %3)
bb1(%4: u8, %5: u8, %6: u8):
    %61 = load i8, ptr %54
    %62 = const i8 6
    %63 = icmp eq i8 %61, %62
    %64 = const i64 0
    %65 = const i64 1
    %66 = select i64 %63, %64, %65
    switch %66 [ 0: bb3(%4, %5, %6) 1: bb4 default: bb2 ]
bb2:
    unreachable
bb3(%7: u8, %8: u8, %9: u8):
    %67 = const u8 31
    call @func.1(%56, %8, %67)
    br bb5(%7, %8, %9)
bb4:
    %68 = load i32, ptr %54
    store i32 %68, ptr %55
    %69 = const i64 4
    %70 = gep i8, ptr %54, %69
    %71 = const i64 4
    %72 = gep i8, ptr %55, %71
    %73 = load i32, ptr %70
    store i32 %73, ptr %72
    %74 = load i32, ptr %55
    store i32 %74, ptr %0
    %75 = const i64 4
    %76 = gep i8, ptr %55, %75
    %77 = const i64 4
    %78 = gep i8, ptr %0, %77
    %79 = load i32, ptr %76
    store i32 %79, ptr %78
    br bb20
bb5(%10: u8, %11: u8, %12: u8):
    %80 = load i8, ptr %56
    %81 = const i8 6
    %82 = icmp eq i8 %80, %81
    %83 = const i64 0
    %84 = const i64 1
    %85 = select i64 %82, %83, %84
    switch %85 [ 0: bb6(%10, %11, %12) 1: bb7 default: bb2 ]
bb6(%13: u8, %14: u8, %15: u8):
    %86 = const u8 31
    call @func.1(%58, %15, %86)
    br bb8(%13, %14, %15)
bb7:
    %87 = load i32, ptr %56
    store i32 %87, ptr %57
    %88 = const i64 4
    %89 = gep i8, ptr %56, %88
    %90 = const i64 4
    %91 = gep i8, ptr %57, %90
    %92 = load i32, ptr %89
    store i32 %92, ptr %91
    %93 = load i32, ptr %57
    store i32 %93, ptr %0
    %94 = const i64 4
    %95 = gep i8, ptr %57, %94
    %96 = const i64 4
    %97 = gep i8, ptr %0, %96
    %98 = load i32, ptr %95
    store i32 %98, ptr %97
    br bb20
bb8(%16: u8, %17: u8, %18: u8):
    %99 = load i8, ptr %58
    %100 = const i8 6
    %101 = icmp eq i8 %99, %100
    %102 = const i64 0
    %103 = const i64 1
    %104 = select i64 %101, %102, %103
    switch %104 [ 0: bb9(%16, %17, %18) 1: bb10 default: bb2 ]
bb9(%19: u8, %20: u8, %21: u8):
    %105 = const u32 0
    %106 = const i32 30
    %107 = bitcast i32 %106 to u32
    %108 = const u32 32
    %109 = icmp ult u32 %107, %108
    condbr %109, bb11(%19, %20, %21, %105), bb21
bb10:
    %110 = load i32, ptr %58
    store i32 %110, ptr %59
    %111 = const i64 4
    %112 = gep i8, ptr %58, %111
    %113 = const i64 4
    %114 = gep i8, ptr %59, %113
    %115 = load i32, ptr %112
    store i32 %115, ptr %114
    %116 = load i32, ptr %59
    store i32 %116, ptr %0
    %117 = const i64 4
    %118 = gep i8, ptr %59, %117
    %119 = const i64 4
    %120 = gep i8, ptr %0, %119
    %121 = load i32, ptr %118
    store i32 %121, ptr %120
    br bb20
bb11(%22: u8, %23: u8, %24: u8, %25: u32):
    %122 = const u32 2
    %123 = const i32 30
    %124 = shl u32 %122, %123
    %125 = or u32 %25, %124
    %126 = const i32 27
    %127 = bitcast i32 %126 to u32
    %128 = const u32 32
    %129 = icmp ult u32 %127, %128
    condbr %129, bb12(%22, %23, %24, %125), bb21
bb12(%26: u8, %27: u8, %28: u8, %29: u32):
    %130 = const u32 7
    %131 = const i32 27
    %132 = shl u32 %130, %131
    %133 = or u32 %29, %132
    %134 = const i32 22
    %135 = bitcast i32 %134 to u32
    %136 = const u32 32
    %137 = icmp ult u32 %135, %136
    condbr %137, bb13(%26, %27, %28, %133), bb21
bb13(%30: u8, %31: u8, %32: u8, %33: u32):
    %138 = const u32 2
    %139 = const i32 22
    %140 = shl u32 %138, %139
    %141 = or u32 %33, %140
    %142 = const i32 21
    %143 = bitcast i32 %142 to u32
    %144 = const u32 32
    %145 = icmp ult u32 %143, %144
    condbr %145, bb14(%30, %31, %32, %141), bb21
bb14(%34: u8, %35: u8, %36: u8, %37: u32):
    %146 = const u32 1
    %147 = const i32 21
    %148 = shl u32 %146, %147
    %149 = or u32 %37, %148
    %150 = zext u8 %34 to u32
    %151 = const i32 16
    %152 = bitcast i32 %151 to u32
    %153 = const u32 32
    %154 = icmp ult u32 %152, %153
    condbr %154, bb15(%35, %36, %149, %150), bb21
bb15(%38: u8, %39: u8, %40: u32, %41: u32):
    %155 = const i32 16
    %156 = shl u32 %41, %155
    %157 = or u32 %40, %156
    %158 = const i32 13
    %159 = bitcast i32 %158 to u32
    %160 = const u32 32
    %161 = icmp ult u32 %159, %160
    condbr %161, bb16(%38, %39, %157), bb21
bb16(%42: u8, %43: u8, %44: u32):
    %162 = const u32 3
    %163 = const i32 13
    %164 = shl u32 %162, %163
    %165 = or u32 %44, %164
    %166 = const i32 12
    %167 = bitcast i32 %166 to u32
    %168 = const u32 32
    %169 = icmp ult u32 %167, %168
    condbr %169, bb17(%42, %43, %165), bb21
bb17(%45: u8, %46: u8, %47: u32):
    %170 = const u32 1
    %171 = const i32 12
    %172 = shl u32 %170, %171
    %173 = or u32 %47, %172
    %174 = const i32 10
    %175 = bitcast i32 %174 to u32
    %176 = const u32 32
    %177 = icmp ult u32 %175, %176
    condbr %177, bb18(%45, %46, %173), bb21
bb18(%48: u8, %49: u8, %50: u32):
    %178 = const u32 2
    %179 = const i32 10
    %180 = shl u32 %178, %179
    %181 = or u32 %50, %180
    %182 = zext u8 %48 to u32
    %183 = const i32 5
    %184 = bitcast i32 %183 to u32
    %185 = const u32 32
    %186 = icmp ult u32 %184, %185
    condbr %186, bb19(%49, %181, %182), bb21
bb19(%51: u8, %52: u32, %53: u32):
    %187 = const i32 5
    %188 = shl u32 %53, %187
    %189 = or u32 %52, %188
    %190 = zext u8 %51 to u32
    %191 = or u32 %189, %190
    %192 = const i64 4
    %193 = gep i8, ptr %0, %192
    store u32 %191, ptr %193
    %194 = const i8 6
    store i8 %194, ptr %0
    br bb20
bb20:
    ret
bb21:
    unreachable
}

fn @check_reg(functy.1) {
bb0(%0: ptr, %1: u8, %2: u8):
    %5 = alloca (i32, i32), align 4
    %6 = icmp ugt u8 %1, %2
    condbr %6, bb1(%1, %2), bb2
bb1(%3: u8, %4: u8):
    %7 = const i64 1
    %8 = gep i8, ptr %5, %7
    store u8 %3, ptr %8
    %9 = const i64 2
    %10 = gep i8, ptr %5, %9
    store u8 %4, ptr %10
    %11 = const i8 0
    store i8 %11, ptr %5
    %12 = load i32, ptr %5
    store i32 %12, ptr %0
    %13 = const i64 4
    %14 = gep i8, ptr %5, %13
    %15 = const i64 4
    %16 = gep i8, ptr %0, %15
    %17 = load i32, ptr %14
    store i32 %17, ptr %16
    br bb3
bb2:
    %18 = const i8 6
    store i8 %18, ptr %0
    br bb3
bb3:
    ret
}
"#;

/// VERBATIM MIR-closure emit of the production `encode_ldp_stp_offset`
/// wrapper + the underlying `encode_ldp_stp` + `check_reg` + `check_imm7`
/// (encoding_mem.rs; `?` -> match; check_imm7 contains -> comparisons). Emit
/// reported: 9586 bytes; 4 closure member(s); validate_module = 16 error(s)
/// (const-shift class); re-parse OK. The bare `encode_ldp_stp` is IN-MODULE
/// and driven directly as a standalone JIT symbol over ALL THREE PairModes.
/// Slice: tests/slices/trust_memaddr_slice.rs.
/// Regen: trust_ir_mir trust_memaddr_slice.rs --crate-type=lib
///   --mir-emit-closure encode_ldp_stp_offset <out.tir>
const LDP_STP_OFFSET_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_ldp_stp_offset"

functy.0 = (ptr, u8, bool, u8, i8, u8, u8, u8) -> ()

functy.1 = (ptr, u8, bool, u8, u8, i8, u8, u8, u8) -> ()

functy.2 = (ptr, u8, u8) -> ()

functy.3 = (ptr, i8) -> ()

fn @encode_ldp_stp_offset(functy.0) {
bb0(%0: ptr, %1: u8, %2: bool, %3: u8, %4: i8, %5: u8, %6: u8, %7: u8):
    %8 = alloca i8, align 1
    %9 = alloca i8, align 1
    %10 = alloca i8, align 1
    store u8 %1, ptr %8
    store u8 %3, ptr %9
    %11 = const i8 2
    store i8 %11, ptr %10
    %12 = load u8, ptr %8
    %13 = load u8, ptr %9
    %14 = load u8, ptr %10
    call @func.1(%0, %12, %2, %13, %14, %4, %5, %6, %7)
    br bb1
bb1:
    ret
}

fn @encode_ldp_stp(functy.1) {
bb0(%0: ptr, %1: u8, %2: bool, %3: u8, %4: u8, %5: i8, %6: u8, %7: u8, %8: u8):
    %92 = alloca i8, align 1
    %93 = alloca i8, align 1
    %94 = alloca i8, align 1
    %95 = alloca (i32, i32), align 4
    %96 = alloca (i32, i32), align 4
    %97 = alloca (i32, i32), align 4
    %98 = alloca (i32, i32), align 4
    %99 = alloca (i32, i32), align 4
    %100 = alloca (i32, i32), align 4
    %101 = alloca (i32, i32), align 4
    %102 = alloca (i32, i32), align 4
    store u8 %1, ptr %92
    store u8 %3, ptr %93
    store u8 %4, ptr %94
    %103 = const u8 31
    call @func.2(%95, %8, %103)
    br bb1(%2, %5, %6, %7, %8)
bb1(%9: bool, %10: i8, %11: u8, %12: u8, %13: u8):
    %104 = load i8, ptr %95
    %105 = const i8 6
    %106 = icmp eq i8 %104, %105
    %107 = const i64 0
    %108 = const i64 1
    %109 = select i64 %106, %107, %108
    switch %109 [ 0: bb3(%9, %10, %11, %12, %13) 1: bb4 default: bb2 ]
bb2:
    unreachable
bb3(%14: bool, %15: i8, %16: u8, %17: u8, %18: u8):
    %110 = const u8 31
    call @func.2(%97, %16, %110)
    br bb5(%14, %15, %16, %17, %18)
bb4:
    %111 = load i32, ptr %95
    store i32 %111, ptr %96
    %112 = const i64 4
    %113 = gep i8, ptr %95, %112
    %114 = const i64 4
    %115 = gep i8, ptr %96, %114
    %116 = load i32, ptr %113
    store i32 %116, ptr %115
    %117 = load i32, ptr %96
    store i32 %117, ptr %0
    %118 = const i64 4
    %119 = gep i8, ptr %96, %118
    %120 = const i64 4
    %121 = gep i8, ptr %0, %120
    %122 = load i32, ptr %119
    store i32 %122, ptr %121
    br bb22
bb5(%19: bool, %20: i8, %21: u8, %22: u8, %23: u8):
    %123 = load i8, ptr %97
    %124 = const i8 6
    %125 = icmp eq i8 %123, %124
    %126 = const i64 0
    %127 = const i64 1
    %128 = select i64 %125, %126, %127
    switch %128 [ 0: bb6(%19, %20, %21, %22, %23) 1: bb7 default: bb2 ]
bb6(%24: bool, %25: i8, %26: u8, %27: u8, %28: u8):
    %129 = const u8 31
    call @func.2(%99, %27, %129)
    br bb8(%24, %25, %26, %27, %28)
bb7:
    %130 = load i32, ptr %97
    store i32 %130, ptr %98
    %131 = const i64 4
    %132 = gep i8, ptr %97, %131
    %133 = const i64 4
    %134 = gep i8, ptr %98, %133
    %135 = load i32, ptr %132
    store i32 %135, ptr %134
    %136 = load i32, ptr %98
    store i32 %136, ptr %0
    %137 = const i64 4
    %138 = gep i8, ptr %98, %137
    %139 = const i64 4
    %140 = gep i8, ptr %0, %139
    %141 = load i32, ptr %138
    store i32 %141, ptr %140
    br bb22
bb8(%29: bool, %30: i8, %31: u8, %32: u8, %33: u8):
    %142 = load i8, ptr %99
    %143 = const i8 6
    %144 = icmp eq i8 %142, %143
    %145 = const i64 0
    %146 = const i64 1
    %147 = select i64 %144, %145, %146
    switch %147 [ 0: bb9(%29, %30, %31, %32, %33) 1: bb10 default: bb2 ]
bb9(%34: bool, %35: i8, %36: u8, %37: u8, %38: u8):
    call @func.3(%101, %35)
    br bb11(%34, %35, %36, %37, %38)
bb10:
    %148 = load i32, ptr %99
    store i32 %148, ptr %100
    %149 = const i64 4
    %150 = gep i8, ptr %99, %149
    %151 = const i64 4
    %152 = gep i8, ptr %100, %151
    %153 = load i32, ptr %150
    store i32 %153, ptr %152
    %154 = load i32, ptr %100
    store i32 %154, ptr %0
    %155 = const i64 4
    %156 = gep i8, ptr %100, %155
    %157 = const i64 4
    %158 = gep i8, ptr %0, %157
    %159 = load i32, ptr %156
    store i32 %159, ptr %158
    br bb22
bb11(%39: bool, %40: i8, %41: u8, %42: u8, %43: u8):
    %160 = load i8, ptr %101
    %161 = const i8 6
    %162 = icmp eq i8 %160, %161
    %163 = const i64 0
    %164 = const i64 1
    %165 = select i64 %162, %163, %164
    switch %165 [ 0: bb12(%39, %40, %41, %42, %43) 1: bb13 default: bb2 ]
bb12(%44: bool, %45: i8, %46: u8, %47: u8, %48: u8):
    %166 = bitcast i8 %45 to u8
    %167 = const u8 127
    %168 = and u8 %166, %167
    %169 = zext u8 %168 to u32
    %170 = const u32 0
    %171 = load i8, ptr %92
    %172 = sext i8 %171 to i64
    %173 = trunc i64 %172 to u32
    %174 = const i32 30
    %175 = bitcast i32 %174 to u32
    %176 = const u32 32
    %177 = icmp ult u32 %175, %176
    condbr %177, bb14(%44, %46, %47, %48, %169, %170, %173), bb23
bb13:
    %178 = load i32, ptr %101
    store i32 %178, ptr %102
    %179 = const i64 4
    %180 = gep i8, ptr %101, %179
    %181 = const i64 4
    %182 = gep i8, ptr %102, %181
    %183 = load i32, ptr %180
    store i32 %183, ptr %182
    %184 = load i32, ptr %102
    store i32 %184, ptr %0
    %185 = const i64 4
    %186 = gep i8, ptr %102, %185
    %187 = const i64 4
    %188 = gep i8, ptr %0, %187
    %189 = load i32, ptr %186
    store i32 %189, ptr %188
    br bb22
bb14(%49: bool, %50: u8, %51: u8, %52: u8, %53: u32, %54: u32, %55: u32):
    %190 = const i32 30
    %191 = shl u32 %55, %190
    %192 = or u32 %54, %191
    %193 = const i32 27
    %194 = bitcast i32 %193 to u32
    %195 = const u32 32
    %196 = icmp ult u32 %194, %195
    condbr %196, bb15(%49, %50, %51, %52, %53, %192), bb23
bb15(%56: bool, %57: u8, %58: u8, %59: u8, %60: u32, %61: u32):
    %197 = const u32 5
    %198 = const i32 27
    %199 = shl u32 %197, %198
    %200 = or u32 %61, %199
    %201 = const u32 1
    %202 = const u32 0
    %203 = select u32 %56, %201, %202
    %204 = const i32 26
    %205 = bitcast i32 %204 to u32
    %206 = const u32 32
    %207 = icmp ult u32 %205, %206
    condbr %207, bb16(%57, %58, %59, %60, %200, %203), bb23
bb16(%62: u8, %63: u8, %64: u8, %65: u32, %66: u32, %67: u32):
    %208 = const i32 26
    %209 = shl u32 %67, %208
    %210 = or u32 %66, %209
    %211 = load i8, ptr %94
    %212 = sext i8 %211 to i64
    %213 = trunc i64 %212 to u32
    %214 = const i32 23
    %215 = bitcast i32 %214 to u32
    %216 = const u32 32
    %217 = icmp ult u32 %215, %216
    condbr %217, bb17(%62, %63, %64, %65, %210, %213), bb23
bb17(%68: u8, %69: u8, %70: u8, %71: u32, %72: u32, %73: u32):
    %218 = const i32 23
    %219 = shl u32 %73, %218
    %220 = or u32 %72, %219
    %221 = load i8, ptr %93
    %222 = sext i8 %221 to i64
    %223 = trunc i64 %222 to u32
    %224 = const i32 22
    %225 = bitcast i32 %224 to u32
    %226 = const u32 32
    %227 = icmp ult u32 %225, %226
    condbr %227, bb18(%68, %69, %70, %71, %220, %223), bb23
bb18(%74: u8, %75: u8, %76: u8, %77: u32, %78: u32, %79: u32):
    %228 = const i32 22
    %229 = shl u32 %79, %228
    %230 = or u32 %78, %229
    %231 = const i32 15
    %232 = bitcast i32 %231 to u32
    %233 = const u32 32
    %234 = icmp ult u32 %232, %233
    condbr %234, bb19(%74, %75, %76, %77, %230), bb23
bb19(%80: u8, %81: u8, %82: u8, %83: u32, %84: u32):
    %235 = const i32 15
    %236 = shl u32 %83, %235
    %237 = or u32 %84, %236
    %238 = zext u8 %80 to u32
    %239 = const i32 10
    %240 = bitcast i32 %239 to u32
    %241 = const u32 32
    %242 = icmp ult u32 %240, %241
    condbr %242, bb20(%81, %82, %237, %238), bb23
bb20(%85: u8, %86: u8, %87: u32, %88: u32):
    %243 = const i32 10
    %244 = shl u32 %88, %243
    %245 = or u32 %87, %244
    %246 = zext u8 %85 to u32
    %247 = const i32 5
    %248 = bitcast i32 %247 to u32
    %249 = const u32 32
    %250 = icmp ult u32 %248, %249
    condbr %250, bb21(%86, %245, %246), bb23
bb21(%89: u8, %90: u32, %91: u32):
    %251 = const i32 5
    %252 = shl u32 %91, %251
    %253 = or u32 %90, %252
    %254 = zext u8 %89 to u32
    %255 = or u32 %253, %254
    %256 = const i64 4
    %257 = gep i8, ptr %0, %256
    store u32 %255, ptr %257
    %258 = const i8 6
    store i8 %258, ptr %0
    br bb22
bb22:
    ret
bb23:
    unreachable
}

fn @check_reg(functy.2) {
bb0(%0: ptr, %1: u8, %2: u8):
    %5 = alloca (i32, i32), align 4
    %6 = icmp ugt u8 %1, %2
    condbr %6, bb1(%1, %2), bb2
bb1(%3: u8, %4: u8):
    %7 = const i64 1
    %8 = gep i8, ptr %5, %7
    store u8 %3, ptr %8
    %9 = const i64 2
    %10 = gep i8, ptr %5, %9
    store u8 %4, ptr %10
    %11 = const i8 0
    store i8 %11, ptr %5
    %12 = load i32, ptr %5
    store i32 %12, ptr %0
    %13 = const i64 4
    %14 = gep i8, ptr %5, %13
    %15 = const i64 4
    %16 = gep i8, ptr %0, %15
    %17 = load i32, ptr %14
    store i32 %17, ptr %16
    br bb3
bb2:
    %18 = const i8 6
    store i8 %18, ptr %0
    br bb3
bb3:
    ret
}

fn @check_imm7(functy.3) {
bb0(%0: ptr, %1: i8):
    %4 = alloca (i32, i32), align 4
    %5 = const i8 -64
    %6 = icmp slt i8 %1, %5
    condbr %6, bb2(%1), bb1(%1)
bb1(%2: i8):
    %7 = const i8 63
    %8 = icmp sgt i8 %2, %7
    condbr %8, bb2(%2), bb3
bb2(%3: i8):
    %9 = const i64 1
    %10 = gep i8, ptr %4, %9
    store i8 %3, ptr %10
    %11 = const i8 3
    store i8 %11, ptr %4
    %12 = load i32, ptr %4
    store i32 %12, ptr %0
    %13 = const i64 4
    %14 = gep i8, ptr %4, %13
    %15 = const i64 4
    %16 = gep i8, ptr %0, %15
    %17 = load i32, ptr %14
    store i32 %17, ptr %16
    br bb4
bb3:
    %18 = const i8 6
    store i8 %18, ptr %0
    br bb4
bb4:
    ret
}
"#;

/// VERBATIM MIR-closure emit of the production `encode_ldp_stp_pre_index`
/// wrapper + `encode_ldp_stp` + `check_reg` + `check_imm7`. Emit reported:
/// 9592 bytes; 4 closure member(s); validate_module = 16 error(s)
/// (const-shift class); re-parse OK.
/// Slice: tests/slices/trust_memaddr_slice.rs.
/// Regen: trust_ir_mir trust_memaddr_slice.rs --crate-type=lib
///   --mir-emit-closure encode_ldp_stp_pre_index <out.tir>
const LDP_STP_PRE_INDEX_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_ldp_stp_pre_index"

functy.0 = (ptr, u8, bool, u8, i8, u8, u8, u8) -> ()

functy.1 = (ptr, u8, bool, u8, u8, i8, u8, u8, u8) -> ()

functy.2 = (ptr, u8, u8) -> ()

functy.3 = (ptr, i8) -> ()

fn @encode_ldp_stp_pre_index(functy.0) {
bb0(%0: ptr, %1: u8, %2: bool, %3: u8, %4: i8, %5: u8, %6: u8, %7: u8):
    %8 = alloca i8, align 1
    %9 = alloca i8, align 1
    %10 = alloca i8, align 1
    store u8 %1, ptr %8
    store u8 %3, ptr %9
    %11 = const i8 3
    store i8 %11, ptr %10
    %12 = load u8, ptr %8
    %13 = load u8, ptr %9
    %14 = load u8, ptr %10
    call @func.1(%0, %12, %2, %13, %14, %4, %5, %6, %7)
    br bb1
bb1:
    ret
}

fn @encode_ldp_stp(functy.1) {
bb0(%0: ptr, %1: u8, %2: bool, %3: u8, %4: u8, %5: i8, %6: u8, %7: u8, %8: u8):
    %92 = alloca i8, align 1
    %93 = alloca i8, align 1
    %94 = alloca i8, align 1
    %95 = alloca (i32, i32), align 4
    %96 = alloca (i32, i32), align 4
    %97 = alloca (i32, i32), align 4
    %98 = alloca (i32, i32), align 4
    %99 = alloca (i32, i32), align 4
    %100 = alloca (i32, i32), align 4
    %101 = alloca (i32, i32), align 4
    %102 = alloca (i32, i32), align 4
    store u8 %1, ptr %92
    store u8 %3, ptr %93
    store u8 %4, ptr %94
    %103 = const u8 31
    call @func.2(%95, %8, %103)
    br bb1(%2, %5, %6, %7, %8)
bb1(%9: bool, %10: i8, %11: u8, %12: u8, %13: u8):
    %104 = load i8, ptr %95
    %105 = const i8 6
    %106 = icmp eq i8 %104, %105
    %107 = const i64 0
    %108 = const i64 1
    %109 = select i64 %106, %107, %108
    switch %109 [ 0: bb3(%9, %10, %11, %12, %13) 1: bb4 default: bb2 ]
bb2:
    unreachable
bb3(%14: bool, %15: i8, %16: u8, %17: u8, %18: u8):
    %110 = const u8 31
    call @func.2(%97, %16, %110)
    br bb5(%14, %15, %16, %17, %18)
bb4:
    %111 = load i32, ptr %95
    store i32 %111, ptr %96
    %112 = const i64 4
    %113 = gep i8, ptr %95, %112
    %114 = const i64 4
    %115 = gep i8, ptr %96, %114
    %116 = load i32, ptr %113
    store i32 %116, ptr %115
    %117 = load i32, ptr %96
    store i32 %117, ptr %0
    %118 = const i64 4
    %119 = gep i8, ptr %96, %118
    %120 = const i64 4
    %121 = gep i8, ptr %0, %120
    %122 = load i32, ptr %119
    store i32 %122, ptr %121
    br bb22
bb5(%19: bool, %20: i8, %21: u8, %22: u8, %23: u8):
    %123 = load i8, ptr %97
    %124 = const i8 6
    %125 = icmp eq i8 %123, %124
    %126 = const i64 0
    %127 = const i64 1
    %128 = select i64 %125, %126, %127
    switch %128 [ 0: bb6(%19, %20, %21, %22, %23) 1: bb7 default: bb2 ]
bb6(%24: bool, %25: i8, %26: u8, %27: u8, %28: u8):
    %129 = const u8 31
    call @func.2(%99, %27, %129)
    br bb8(%24, %25, %26, %27, %28)
bb7:
    %130 = load i32, ptr %97
    store i32 %130, ptr %98
    %131 = const i64 4
    %132 = gep i8, ptr %97, %131
    %133 = const i64 4
    %134 = gep i8, ptr %98, %133
    %135 = load i32, ptr %132
    store i32 %135, ptr %134
    %136 = load i32, ptr %98
    store i32 %136, ptr %0
    %137 = const i64 4
    %138 = gep i8, ptr %98, %137
    %139 = const i64 4
    %140 = gep i8, ptr %0, %139
    %141 = load i32, ptr %138
    store i32 %141, ptr %140
    br bb22
bb8(%29: bool, %30: i8, %31: u8, %32: u8, %33: u8):
    %142 = load i8, ptr %99
    %143 = const i8 6
    %144 = icmp eq i8 %142, %143
    %145 = const i64 0
    %146 = const i64 1
    %147 = select i64 %144, %145, %146
    switch %147 [ 0: bb9(%29, %30, %31, %32, %33) 1: bb10 default: bb2 ]
bb9(%34: bool, %35: i8, %36: u8, %37: u8, %38: u8):
    call @func.3(%101, %35)
    br bb11(%34, %35, %36, %37, %38)
bb10:
    %148 = load i32, ptr %99
    store i32 %148, ptr %100
    %149 = const i64 4
    %150 = gep i8, ptr %99, %149
    %151 = const i64 4
    %152 = gep i8, ptr %100, %151
    %153 = load i32, ptr %150
    store i32 %153, ptr %152
    %154 = load i32, ptr %100
    store i32 %154, ptr %0
    %155 = const i64 4
    %156 = gep i8, ptr %100, %155
    %157 = const i64 4
    %158 = gep i8, ptr %0, %157
    %159 = load i32, ptr %156
    store i32 %159, ptr %158
    br bb22
bb11(%39: bool, %40: i8, %41: u8, %42: u8, %43: u8):
    %160 = load i8, ptr %101
    %161 = const i8 6
    %162 = icmp eq i8 %160, %161
    %163 = const i64 0
    %164 = const i64 1
    %165 = select i64 %162, %163, %164
    switch %165 [ 0: bb12(%39, %40, %41, %42, %43) 1: bb13 default: bb2 ]
bb12(%44: bool, %45: i8, %46: u8, %47: u8, %48: u8):
    %166 = bitcast i8 %45 to u8
    %167 = const u8 127
    %168 = and u8 %166, %167
    %169 = zext u8 %168 to u32
    %170 = const u32 0
    %171 = load i8, ptr %92
    %172 = sext i8 %171 to i64
    %173 = trunc i64 %172 to u32
    %174 = const i32 30
    %175 = bitcast i32 %174 to u32
    %176 = const u32 32
    %177 = icmp ult u32 %175, %176
    condbr %177, bb14(%44, %46, %47, %48, %169, %170, %173), bb23
bb13:
    %178 = load i32, ptr %101
    store i32 %178, ptr %102
    %179 = const i64 4
    %180 = gep i8, ptr %101, %179
    %181 = const i64 4
    %182 = gep i8, ptr %102, %181
    %183 = load i32, ptr %180
    store i32 %183, ptr %182
    %184 = load i32, ptr %102
    store i32 %184, ptr %0
    %185 = const i64 4
    %186 = gep i8, ptr %102, %185
    %187 = const i64 4
    %188 = gep i8, ptr %0, %187
    %189 = load i32, ptr %186
    store i32 %189, ptr %188
    br bb22
bb14(%49: bool, %50: u8, %51: u8, %52: u8, %53: u32, %54: u32, %55: u32):
    %190 = const i32 30
    %191 = shl u32 %55, %190
    %192 = or u32 %54, %191
    %193 = const i32 27
    %194 = bitcast i32 %193 to u32
    %195 = const u32 32
    %196 = icmp ult u32 %194, %195
    condbr %196, bb15(%49, %50, %51, %52, %53, %192), bb23
bb15(%56: bool, %57: u8, %58: u8, %59: u8, %60: u32, %61: u32):
    %197 = const u32 5
    %198 = const i32 27
    %199 = shl u32 %197, %198
    %200 = or u32 %61, %199
    %201 = const u32 1
    %202 = const u32 0
    %203 = select u32 %56, %201, %202
    %204 = const i32 26
    %205 = bitcast i32 %204 to u32
    %206 = const u32 32
    %207 = icmp ult u32 %205, %206
    condbr %207, bb16(%57, %58, %59, %60, %200, %203), bb23
bb16(%62: u8, %63: u8, %64: u8, %65: u32, %66: u32, %67: u32):
    %208 = const i32 26
    %209 = shl u32 %67, %208
    %210 = or u32 %66, %209
    %211 = load i8, ptr %94
    %212 = sext i8 %211 to i64
    %213 = trunc i64 %212 to u32
    %214 = const i32 23
    %215 = bitcast i32 %214 to u32
    %216 = const u32 32
    %217 = icmp ult u32 %215, %216
    condbr %217, bb17(%62, %63, %64, %65, %210, %213), bb23
bb17(%68: u8, %69: u8, %70: u8, %71: u32, %72: u32, %73: u32):
    %218 = const i32 23
    %219 = shl u32 %73, %218
    %220 = or u32 %72, %219
    %221 = load i8, ptr %93
    %222 = sext i8 %221 to i64
    %223 = trunc i64 %222 to u32
    %224 = const i32 22
    %225 = bitcast i32 %224 to u32
    %226 = const u32 32
    %227 = icmp ult u32 %225, %226
    condbr %227, bb18(%68, %69, %70, %71, %220, %223), bb23
bb18(%74: u8, %75: u8, %76: u8, %77: u32, %78: u32, %79: u32):
    %228 = const i32 22
    %229 = shl u32 %79, %228
    %230 = or u32 %78, %229
    %231 = const i32 15
    %232 = bitcast i32 %231 to u32
    %233 = const u32 32
    %234 = icmp ult u32 %232, %233
    condbr %234, bb19(%74, %75, %76, %77, %230), bb23
bb19(%80: u8, %81: u8, %82: u8, %83: u32, %84: u32):
    %235 = const i32 15
    %236 = shl u32 %83, %235
    %237 = or u32 %84, %236
    %238 = zext u8 %80 to u32
    %239 = const i32 10
    %240 = bitcast i32 %239 to u32
    %241 = const u32 32
    %242 = icmp ult u32 %240, %241
    condbr %242, bb20(%81, %82, %237, %238), bb23
bb20(%85: u8, %86: u8, %87: u32, %88: u32):
    %243 = const i32 10
    %244 = shl u32 %88, %243
    %245 = or u32 %87, %244
    %246 = zext u8 %85 to u32
    %247 = const i32 5
    %248 = bitcast i32 %247 to u32
    %249 = const u32 32
    %250 = icmp ult u32 %248, %249
    condbr %250, bb21(%86, %245, %246), bb23
bb21(%89: u8, %90: u32, %91: u32):
    %251 = const i32 5
    %252 = shl u32 %91, %251
    %253 = or u32 %90, %252
    %254 = zext u8 %89 to u32
    %255 = or u32 %253, %254
    %256 = const i64 4
    %257 = gep i8, ptr %0, %256
    store u32 %255, ptr %257
    %258 = const i8 6
    store i8 %258, ptr %0
    br bb22
bb22:
    ret
bb23:
    unreachable
}

fn @check_reg(functy.2) {
bb0(%0: ptr, %1: u8, %2: u8):
    %5 = alloca (i32, i32), align 4
    %6 = icmp ugt u8 %1, %2
    condbr %6, bb1(%1, %2), bb2
bb1(%3: u8, %4: u8):
    %7 = const i64 1
    %8 = gep i8, ptr %5, %7
    store u8 %3, ptr %8
    %9 = const i64 2
    %10 = gep i8, ptr %5, %9
    store u8 %4, ptr %10
    %11 = const i8 0
    store i8 %11, ptr %5
    %12 = load i32, ptr %5
    store i32 %12, ptr %0
    %13 = const i64 4
    %14 = gep i8, ptr %5, %13
    %15 = const i64 4
    %16 = gep i8, ptr %0, %15
    %17 = load i32, ptr %14
    store i32 %17, ptr %16
    br bb3
bb2:
    %18 = const i8 6
    store i8 %18, ptr %0
    br bb3
bb3:
    ret
}

fn @check_imm7(functy.3) {
bb0(%0: ptr, %1: i8):
    %4 = alloca (i32, i32), align 4
    %5 = const i8 -64
    %6 = icmp slt i8 %1, %5
    condbr %6, bb2(%1), bb1(%1)
bb1(%2: i8):
    %7 = const i8 63
    %8 = icmp sgt i8 %2, %7
    condbr %8, bb2(%2), bb3
bb2(%3: i8):
    %9 = const i64 1
    %10 = gep i8, ptr %4, %9
    store i8 %3, ptr %10
    %11 = const i8 3
    store i8 %11, ptr %4
    %12 = load i32, ptr %4
    store i32 %12, ptr %0
    %13 = const i64 4
    %14 = gep i8, ptr %4, %13
    %15 = const i64 4
    %16 = gep i8, ptr %0, %15
    %17 = load i32, ptr %14
    store i32 %17, ptr %16
    br bb4
bb3:
    %18 = const i8 6
    store i8 %18, ptr %0
    br bb4
bb4:
    ret
}
"#;

/// VERBATIM MIR-closure emit of the production `encode_ldp_stp_post_index`
/// wrapper + `encode_ldp_stp` + `check_reg` + `check_imm7`. Emit reported:
/// 9594 bytes; 4 closure member(s); validate_module = 16 error(s)
/// (const-shift class); re-parse OK.
/// Slice: tests/slices/trust_memaddr_slice.rs.
/// Regen: trust_ir_mir trust_memaddr_slice.rs --crate-type=lib
///   --mir-emit-closure encode_ldp_stp_post_index <out.tir>
const LDP_STP_POST_INDEX_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_ldp_stp_post_index"

functy.0 = (ptr, u8, bool, u8, i8, u8, u8, u8) -> ()

functy.1 = (ptr, u8, bool, u8, u8, i8, u8, u8, u8) -> ()

functy.2 = (ptr, u8, u8) -> ()

functy.3 = (ptr, i8) -> ()

fn @encode_ldp_stp_post_index(functy.0) {
bb0(%0: ptr, %1: u8, %2: bool, %3: u8, %4: i8, %5: u8, %6: u8, %7: u8):
    %8 = alloca i8, align 1
    %9 = alloca i8, align 1
    %10 = alloca i8, align 1
    store u8 %1, ptr %8
    store u8 %3, ptr %9
    %11 = const i8 1
    store i8 %11, ptr %10
    %12 = load u8, ptr %8
    %13 = load u8, ptr %9
    %14 = load u8, ptr %10
    call @func.1(%0, %12, %2, %13, %14, %4, %5, %6, %7)
    br bb1
bb1:
    ret
}

fn @encode_ldp_stp(functy.1) {
bb0(%0: ptr, %1: u8, %2: bool, %3: u8, %4: u8, %5: i8, %6: u8, %7: u8, %8: u8):
    %92 = alloca i8, align 1
    %93 = alloca i8, align 1
    %94 = alloca i8, align 1
    %95 = alloca (i32, i32), align 4
    %96 = alloca (i32, i32), align 4
    %97 = alloca (i32, i32), align 4
    %98 = alloca (i32, i32), align 4
    %99 = alloca (i32, i32), align 4
    %100 = alloca (i32, i32), align 4
    %101 = alloca (i32, i32), align 4
    %102 = alloca (i32, i32), align 4
    store u8 %1, ptr %92
    store u8 %3, ptr %93
    store u8 %4, ptr %94
    %103 = const u8 31
    call @func.2(%95, %8, %103)
    br bb1(%2, %5, %6, %7, %8)
bb1(%9: bool, %10: i8, %11: u8, %12: u8, %13: u8):
    %104 = load i8, ptr %95
    %105 = const i8 6
    %106 = icmp eq i8 %104, %105
    %107 = const i64 0
    %108 = const i64 1
    %109 = select i64 %106, %107, %108
    switch %109 [ 0: bb3(%9, %10, %11, %12, %13) 1: bb4 default: bb2 ]
bb2:
    unreachable
bb3(%14: bool, %15: i8, %16: u8, %17: u8, %18: u8):
    %110 = const u8 31
    call @func.2(%97, %16, %110)
    br bb5(%14, %15, %16, %17, %18)
bb4:
    %111 = load i32, ptr %95
    store i32 %111, ptr %96
    %112 = const i64 4
    %113 = gep i8, ptr %95, %112
    %114 = const i64 4
    %115 = gep i8, ptr %96, %114
    %116 = load i32, ptr %113
    store i32 %116, ptr %115
    %117 = load i32, ptr %96
    store i32 %117, ptr %0
    %118 = const i64 4
    %119 = gep i8, ptr %96, %118
    %120 = const i64 4
    %121 = gep i8, ptr %0, %120
    %122 = load i32, ptr %119
    store i32 %122, ptr %121
    br bb22
bb5(%19: bool, %20: i8, %21: u8, %22: u8, %23: u8):
    %123 = load i8, ptr %97
    %124 = const i8 6
    %125 = icmp eq i8 %123, %124
    %126 = const i64 0
    %127 = const i64 1
    %128 = select i64 %125, %126, %127
    switch %128 [ 0: bb6(%19, %20, %21, %22, %23) 1: bb7 default: bb2 ]
bb6(%24: bool, %25: i8, %26: u8, %27: u8, %28: u8):
    %129 = const u8 31
    call @func.2(%99, %27, %129)
    br bb8(%24, %25, %26, %27, %28)
bb7:
    %130 = load i32, ptr %97
    store i32 %130, ptr %98
    %131 = const i64 4
    %132 = gep i8, ptr %97, %131
    %133 = const i64 4
    %134 = gep i8, ptr %98, %133
    %135 = load i32, ptr %132
    store i32 %135, ptr %134
    %136 = load i32, ptr %98
    store i32 %136, ptr %0
    %137 = const i64 4
    %138 = gep i8, ptr %98, %137
    %139 = const i64 4
    %140 = gep i8, ptr %0, %139
    %141 = load i32, ptr %138
    store i32 %141, ptr %140
    br bb22
bb8(%29: bool, %30: i8, %31: u8, %32: u8, %33: u8):
    %142 = load i8, ptr %99
    %143 = const i8 6
    %144 = icmp eq i8 %142, %143
    %145 = const i64 0
    %146 = const i64 1
    %147 = select i64 %144, %145, %146
    switch %147 [ 0: bb9(%29, %30, %31, %32, %33) 1: bb10 default: bb2 ]
bb9(%34: bool, %35: i8, %36: u8, %37: u8, %38: u8):
    call @func.3(%101, %35)
    br bb11(%34, %35, %36, %37, %38)
bb10:
    %148 = load i32, ptr %99
    store i32 %148, ptr %100
    %149 = const i64 4
    %150 = gep i8, ptr %99, %149
    %151 = const i64 4
    %152 = gep i8, ptr %100, %151
    %153 = load i32, ptr %150
    store i32 %153, ptr %152
    %154 = load i32, ptr %100
    store i32 %154, ptr %0
    %155 = const i64 4
    %156 = gep i8, ptr %100, %155
    %157 = const i64 4
    %158 = gep i8, ptr %0, %157
    %159 = load i32, ptr %156
    store i32 %159, ptr %158
    br bb22
bb11(%39: bool, %40: i8, %41: u8, %42: u8, %43: u8):
    %160 = load i8, ptr %101
    %161 = const i8 6
    %162 = icmp eq i8 %160, %161
    %163 = const i64 0
    %164 = const i64 1
    %165 = select i64 %162, %163, %164
    switch %165 [ 0: bb12(%39, %40, %41, %42, %43) 1: bb13 default: bb2 ]
bb12(%44: bool, %45: i8, %46: u8, %47: u8, %48: u8):
    %166 = bitcast i8 %45 to u8
    %167 = const u8 127
    %168 = and u8 %166, %167
    %169 = zext u8 %168 to u32
    %170 = const u32 0
    %171 = load i8, ptr %92
    %172 = sext i8 %171 to i64
    %173 = trunc i64 %172 to u32
    %174 = const i32 30
    %175 = bitcast i32 %174 to u32
    %176 = const u32 32
    %177 = icmp ult u32 %175, %176
    condbr %177, bb14(%44, %46, %47, %48, %169, %170, %173), bb23
bb13:
    %178 = load i32, ptr %101
    store i32 %178, ptr %102
    %179 = const i64 4
    %180 = gep i8, ptr %101, %179
    %181 = const i64 4
    %182 = gep i8, ptr %102, %181
    %183 = load i32, ptr %180
    store i32 %183, ptr %182
    %184 = load i32, ptr %102
    store i32 %184, ptr %0
    %185 = const i64 4
    %186 = gep i8, ptr %102, %185
    %187 = const i64 4
    %188 = gep i8, ptr %0, %187
    %189 = load i32, ptr %186
    store i32 %189, ptr %188
    br bb22
bb14(%49: bool, %50: u8, %51: u8, %52: u8, %53: u32, %54: u32, %55: u32):
    %190 = const i32 30
    %191 = shl u32 %55, %190
    %192 = or u32 %54, %191
    %193 = const i32 27
    %194 = bitcast i32 %193 to u32
    %195 = const u32 32
    %196 = icmp ult u32 %194, %195
    condbr %196, bb15(%49, %50, %51, %52, %53, %192), bb23
bb15(%56: bool, %57: u8, %58: u8, %59: u8, %60: u32, %61: u32):
    %197 = const u32 5
    %198 = const i32 27
    %199 = shl u32 %197, %198
    %200 = or u32 %61, %199
    %201 = const u32 1
    %202 = const u32 0
    %203 = select u32 %56, %201, %202
    %204 = const i32 26
    %205 = bitcast i32 %204 to u32
    %206 = const u32 32
    %207 = icmp ult u32 %205, %206
    condbr %207, bb16(%57, %58, %59, %60, %200, %203), bb23
bb16(%62: u8, %63: u8, %64: u8, %65: u32, %66: u32, %67: u32):
    %208 = const i32 26
    %209 = shl u32 %67, %208
    %210 = or u32 %66, %209
    %211 = load i8, ptr %94
    %212 = sext i8 %211 to i64
    %213 = trunc i64 %212 to u32
    %214 = const i32 23
    %215 = bitcast i32 %214 to u32
    %216 = const u32 32
    %217 = icmp ult u32 %215, %216
    condbr %217, bb17(%62, %63, %64, %65, %210, %213), bb23
bb17(%68: u8, %69: u8, %70: u8, %71: u32, %72: u32, %73: u32):
    %218 = const i32 23
    %219 = shl u32 %73, %218
    %220 = or u32 %72, %219
    %221 = load i8, ptr %93
    %222 = sext i8 %221 to i64
    %223 = trunc i64 %222 to u32
    %224 = const i32 22
    %225 = bitcast i32 %224 to u32
    %226 = const u32 32
    %227 = icmp ult u32 %225, %226
    condbr %227, bb18(%68, %69, %70, %71, %220, %223), bb23
bb18(%74: u8, %75: u8, %76: u8, %77: u32, %78: u32, %79: u32):
    %228 = const i32 22
    %229 = shl u32 %79, %228
    %230 = or u32 %78, %229
    %231 = const i32 15
    %232 = bitcast i32 %231 to u32
    %233 = const u32 32
    %234 = icmp ult u32 %232, %233
    condbr %234, bb19(%74, %75, %76, %77, %230), bb23
bb19(%80: u8, %81: u8, %82: u8, %83: u32, %84: u32):
    %235 = const i32 15
    %236 = shl u32 %83, %235
    %237 = or u32 %84, %236
    %238 = zext u8 %80 to u32
    %239 = const i32 10
    %240 = bitcast i32 %239 to u32
    %241 = const u32 32
    %242 = icmp ult u32 %240, %241
    condbr %242, bb20(%81, %82, %237, %238), bb23
bb20(%85: u8, %86: u8, %87: u32, %88: u32):
    %243 = const i32 10
    %244 = shl u32 %88, %243
    %245 = or u32 %87, %244
    %246 = zext u8 %85 to u32
    %247 = const i32 5
    %248 = bitcast i32 %247 to u32
    %249 = const u32 32
    %250 = icmp ult u32 %248, %249
    condbr %250, bb21(%86, %245, %246), bb23
bb21(%89: u8, %90: u32, %91: u32):
    %251 = const i32 5
    %252 = shl u32 %91, %251
    %253 = or u32 %90, %252
    %254 = zext u8 %89 to u32
    %255 = or u32 %253, %254
    %256 = const i64 4
    %257 = gep i8, ptr %0, %256
    store u32 %255, ptr %257
    %258 = const i8 6
    store i8 %258, ptr %0
    br bb22
bb22:
    ret
bb23:
    unreachable
}

fn @check_reg(functy.2) {
bb0(%0: ptr, %1: u8, %2: u8):
    %5 = alloca (i32, i32), align 4
    %6 = icmp ugt u8 %1, %2
    condbr %6, bb1(%1, %2), bb2
bb1(%3: u8, %4: u8):
    %7 = const i64 1
    %8 = gep i8, ptr %5, %7
    store u8 %3, ptr %8
    %9 = const i64 2
    %10 = gep i8, ptr %5, %9
    store u8 %4, ptr %10
    %11 = const i8 0
    store i8 %11, ptr %5
    %12 = load i32, ptr %5
    store i32 %12, ptr %0
    %13 = const i64 4
    %14 = gep i8, ptr %5, %13
    %15 = const i64 4
    %16 = gep i8, ptr %0, %15
    %17 = load i32, ptr %14
    store i32 %17, ptr %16
    br bb3
bb2:
    %18 = const i8 6
    store i8 %18, ptr %0
    br bb3
bb3:
    ret
}

fn @check_imm7(functy.3) {
bb0(%0: ptr, %1: i8):
    %4 = alloca (i32, i32), align 4
    %5 = const i8 -64
    %6 = icmp slt i8 %1, %5
    condbr %6, bb2(%1), bb1(%1)
bb1(%2: i8):
    %7 = const i8 63
    %8 = icmp sgt i8 %2, %7
    condbr %8, bb2(%2), bb3
bb2(%3: i8):
    %9 = const i64 1
    %10 = gep i8, ptr %4, %9
    store i8 %3, ptr %10
    %11 = const i8 3
    store i8 %11, ptr %4
    %12 = load i32, ptr %4
    store i32 %12, ptr %0
    %13 = const i64 4
    %14 = gep i8, ptr %4, %13
    %15 = const i64 4
    %16 = gep i8, ptr %0, %15
    %17 = load i32, ptr %14
    store i32 %17, ptr %16
    br bb4
bb3:
    %18 = const i8 6
    store i8 %18, ptr %0
    br bb4
bb4:
    ret
}
"#;

// ═══════════════════════════════════════════════════════════════════════════
// The WORD BUILDERS (encoding.rs) — oracle: the REAL production pub fns
// ═══════════════════════════════════════════════════════════════════════════

type Enc2Fn = extern "C" fn(u32, u32) -> u32;
type Enc3Fn = extern "C" fn(u32, u32, u32) -> u32;
type Enc6Fn = extern "C" fn(u32, u32, u32, u32, u32, u32) -> u32;
type Enc7Fn = extern "C" fn(u32, u32, u32, u32, u32, u32, u32) -> u32;

const REGS: [u32; 6] = [0, 1, 2, 15, 30, 31];

/// TRUST-SELF round 3: `encode_extract` (EXTR — `ROR Rd, Rn, #sh` is
/// `EXTR Rd, Rn, Rn, #sh`, the rotate ISel emits) — native (the REAL
/// production fn) == JIT over the full in-contract field product.
#[test]
fn trust_self3_encode_extract_roundtrip() {
    let buffer = jit_module(EXTRACT_TRUST_IR, "encode_extract");
    // SAFETY: machine code for `(u32 x6) -> u32` per functy.0.
    let f: Enc6Fn = unsafe { std::mem::transmute(bind(&buffer, "encode_extract")) };

    let mut pass = 0usize;
    for sf in [0u32, 1] {
        for n in [0u32, 1] {
            for &rm in &REGS {
                for &imms in &[0u32, 1, 4, 31, 32, 63] {
                    for &rn in &REGS {
                        let rd = (rm + rn + imms) % 32;
                        let native = prod_encoding::encode_extract(sf, n, rm, imms, rn, rd);
                        let jit = f(sf, n, rm, imms, rn, rd);
                        assert_eq!(
                            native, jit,
                            "TRUST-SELF encode_extract JIT disagrees: sf={sf} n={n} rm={rm} \
                             imms={imms} rn={rn} rd={rd}: native={native:#010X} jit={jit:#010X}"
                        );
                        pass += 1;
                    }
                }
            }
        }
    }
    assert_eq!(pass, 2 * 2 * 6 * 6 * 6);
    // Ground truth: ROR X0, X1, #4 == EXTR X0, X1, X1, #4 = 0x93C11020
    // (sf=1 N=1 rm=1 imms=4 rn=1 rd=0 — the encode.rs:1209 ROR form).
    assert_eq!(f(1, 1, 1, 4, 1, 0), 0x93C11020, "ROR X0, X1, #4");

    // NEGATIVE CONTROL: an oracle with N misplaced at bit 21 must disagree.
    fn extract_corrupt(sf: u32, n: u32, rm: u32, imms: u32, rn: u32, rd: u32) -> u32 {
        (sf << 31) | (0b100111 << 23) | (n << 21) | (rm << 16) | (imms << 10) | (rn << 5) | rd
    }
    assert_ne!(
        extract_corrupt(1, 1, 1, 4, 1, 0),
        f(1, 1, 1, 4, 1, 0),
        "negative control must FAIL: N-at-bit-21 oracle should disagree with the JIT"
    );

    drop(buffer);
}

/// TRUST-SELF round 3: `encode_bit_reverse` (RBIT) — native (REAL production
/// fn) == JIT over the full in-contract product (sf x rn x rd).
#[test]
fn trust_self3_encode_bit_reverse_roundtrip() {
    let buffer = jit_module(BIT_REVERSE_TRUST_IR, "encode_bit_reverse");
    // SAFETY: machine code for `(u32 x3) -> u32` per functy.0.
    let f: Enc3Fn = unsafe { std::mem::transmute(bind(&buffer, "encode_bit_reverse")) };

    let mut pass = 0usize;
    for sf in [0u32, 1] {
        for rn in 0..=31u32 {
            for rd in 0..=31u32 {
                let native = prod_encoding::encode_bit_reverse(sf, rn, rd);
                let jit = f(sf, rn, rd);
                assert_eq!(
                    native, jit,
                    "TRUST-SELF encode_bit_reverse JIT disagrees: sf={sf} rn={rn} rd={rd}: \
                     native={native:#010X} jit={jit:#010X}"
                );
                pass += 1;
            }
        }
    }
    assert_eq!(pass, 2 * 32 * 32);
    // Ground truths (the aarch64_encoding.rs integration tests' pinned words).
    assert_eq!(f(0, 1, 0), 0x5AC0_0020, "RBIT W0, W1");
    assert_eq!(f(1, 3, 2), 0xDAC0_0062, "RBIT X2, X3");

    // NEGATIVE CONTROL: the opcode field shifted to bit 20 must disagree.
    assert_ne!(
        (1u32 << 31) | (0b1011010110u32 << 20) | (3 << 5) | 2,
        f(1, 3, 2),
        "negative control must FAIL: mis-shifted opcode field should disagree with the JIT"
    );

    drop(buffer);
}

/// TRUST-SELF round 3: `encode_uncond_branch` (B / BL — every direct call and
/// every unconditional jump trust-cg emits) — native (REAL production fn) ==
/// JIT over the imm26 edges for both ops.
#[test]
fn trust_self3_encode_uncond_branch_roundtrip() {
    let buffer = jit_module(UNCOND_BRANCH_TRUST_IR, "encode_uncond_branch");
    // SAFETY: machine code for `(u32, u32) -> u32` per functy.0.
    let f: Enc2Fn = unsafe { std::mem::transmute(bind(&buffer, "encode_uncond_branch")) };

    let mut pass = 0usize;
    for op in [0u32, 1] {
        for &imm26 in &[
            0u32, 1, 2, 0x3FF, 0x2000000, 0x2AAAAAA, 0x3FFFFFE, 0x3FFFFFF,
        ] {
            let native = prod_encoding::encode_uncond_branch(op, imm26);
            let jit = f(op, imm26);
            assert_eq!(
                native, jit,
                "TRUST-SELF encode_uncond_branch JIT disagrees: op={op} imm26={imm26:#x}: \
                 native={native:#010X} jit={jit:#010X}"
            );
            pass += 1;
        }
    }
    assert_eq!(pass, 2 * 8);
    // Ground truths: B <+8> = 0x14000002; BL <+8> = 0x94000002.
    assert_eq!(f(0, 2), 0x14000002, "B <+8>");
    assert_eq!(f(1, 2), 0x94000002, "BL <+8>");

    // NEGATIVE CONTROL: op at bit 30 (colliding with the 00101 opcode field)
    // must disagree with BL.
    assert_ne!(
        (1u32 << 30) | (0b00101 << 26) | 2,
        f(1, 2),
        "negative control must FAIL: op-at-bit-30 word should disagree with the JIT"
    );

    drop(buffer);
}

/// TRUST-SELF round 3: `encode_branch_reg` (BR / BLR / RET — every indirect
/// call and every function return) — native (REAL production fn) == JIT over
/// the full opc x rn product.
#[test]
fn trust_self3_encode_branch_reg_roundtrip() {
    let buffer = jit_module(BRANCH_REG_TRUST_IR, "encode_branch_reg");
    // SAFETY: machine code for `(u32, u32) -> u32` per functy.0.
    let f: Enc2Fn = unsafe { std::mem::transmute(bind(&buffer, "encode_branch_reg")) };

    let mut pass = 0usize;
    for opc in 0..=15u32 {
        for rn in 0..=31u32 {
            let native = prod_encoding::encode_branch_reg(opc, rn);
            let jit = f(opc, rn);
            assert_eq!(
                native, jit,
                "TRUST-SELF encode_branch_reg JIT disagrees: opc={opc} rn={rn}: \
                 native={native:#010X} jit={jit:#010X}"
            );
            pass += 1;
        }
    }
    assert_eq!(pass, 16 * 32);
    // Ground truths (production unit tests' pinned words).
    assert_eq!(f(0, 30), 0xD61F03C0, "BR X30");
    assert_eq!(f(1, 0), 0xD63F0000, "BLR X0");
    assert_eq!(f(2, 30), 0xD65F03C0, "RET X30");

    // NEGATIVE CONTROL: an oracle that forgets the Rm=11111 field (bits
    // 20:16) must disagree with RET.
    fn branch_reg_corrupt(opc: u32, rn: u32) -> u32 {
        (0b1101011 << 25) | (opc << 21) | (rn << 5) // bug: no 0b11111 << 16
    }
    assert_ne!(
        branch_reg_corrupt(2, 30),
        f(2, 30),
        "negative control must FAIL: missing-Rm-field oracle should disagree with the JIT"
    );

    drop(buffer);
}

/// TRUST-SELF round 3: `encode_load_store_ui` (LDR/STR scaled unsigned offset
/// — the workhorse addressing mode of every stack slot and field access) —
/// native (REAL production fn) == JIT over the full in-contract product.
#[test]
fn trust_self3_encode_load_store_ui_roundtrip() {
    let buffer = jit_module(LDST_UI_TRUST_IR, "encode_load_store_ui");
    // SAFETY: machine code for `(u32 x6) -> u32` per functy.0.
    let f: Enc6Fn = unsafe { std::mem::transmute(bind(&buffer, "encode_load_store_ui")) };

    let mut pass = 0usize;
    for size in 0..=3u32 {
        for v in [0u32, 1] {
            for opc in 0..=3u32 {
                for &imm12 in &[0u32, 1, 42, 0x7FF, 0xFFE, 0xFFF] {
                    for &rn in &REGS {
                        let rt = (size + opc + imm12 + rn) % 32;
                        let native =
                            prod_encoding::encode_load_store_ui(size, v, opc, imm12, rn, rt);
                        let jit = f(size, v, opc, imm12, rn, rt);
                        assert_eq!(
                            native, jit,
                            "TRUST-SELF encode_load_store_ui JIT disagrees: size={size} v={v} \
                             opc={opc} imm12={imm12:#x} rn={rn} rt={rt}: native={native:#010X} \
                             jit={jit:#010X}"
                        );
                        pass += 1;
                    }
                }
            }
        }
    }
    assert_eq!(pass, 4 * 2 * 4 * 6 * 6);
    // Ground truths (production unit tests' pinned words).
    assert_eq!(f(3, 0, 1, 1, 1, 0), 0xF9400420, "LDR X0, [X1, #8]");
    assert_eq!(f(3, 0, 0, 0, 1, 0), 0xF9000020, "STR X0, [X1]");
    assert_eq!(f(2, 0, 1, 0, 1, 0), 0xB9400020, "LDR W0, [X1]");

    // NEGATIVE CONTROL: imm12 at the unscaled field offset (<<12) must
    // disagree.
    assert_ne!(
        (3u32 << 30) | (0b111 << 27) | (0b01 << 24) | (1 << 22) | (1 << 12) | (1 << 5),
        f(3, 0, 1, 1, 1, 0),
        "negative control must FAIL: imm12-at-bit-12 word should disagree with the JIT"
    );

    drop(buffer);
}

/// TRUST-SELF round 3: `encode_load_store_pair` (LDP/STP — every
/// prologue/epilogue callee-save pair) — native (REAL production fn) == JIT
/// over the full in-contract product incl. the already-masked imm7 domain.
#[test]
fn trust_self3_encode_load_store_pair_roundtrip() {
    let buffer = jit_module(LDST_PAIR_TRUST_IR, "encode_load_store_pair");
    // SAFETY: machine code for `(u32 x7) -> u32` per functy.0.
    let f: Enc7Fn = unsafe { std::mem::transmute(bind(&buffer, "encode_load_store_pair")) };

    let mut pass = 0usize;
    for opc in 0..=3u32 {
        for v in [0u32, 1] {
            for l in [0u32, 1] {
                for &imm7 in &[0u32, 1, 2, 0x3F, 0x40, 0x7C, 0x7F] {
                    for &rt2 in &REGS {
                        for &rn in &REGS {
                            let rt = (opc + imm7 + rt2 + rn) % 32;
                            let native =
                                prod_encoding::encode_load_store_pair(opc, v, l, imm7, rt2, rn, rt);
                            let jit = f(opc, v, l, imm7, rt2, rn, rt);
                            assert_eq!(
                                native, jit,
                                "TRUST-SELF encode_load_store_pair JIT disagrees: opc={opc} \
                                 v={v} l={l} imm7={imm7:#x} rt2={rt2} rn={rn} rt={rt}: \
                                 native={native:#010X} jit={jit:#010X}"
                            );
                            pass += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(pass, 4 * 2 * 2 * 7 * 6 * 6);
    // Ground truths (production unit tests' pinned words).
    assert_eq!(f(2, 0, 0, 2, 1, 31, 0), 0xA90107E0, "STP X0, X1, [SP, #16]");
    assert_eq!(f(2, 0, 1, 0, 1, 31, 0), 0xA94007E0, "LDP X0, X1, [SP]");

    // NEGATIVE CONTROL: L misplaced at bit 23 (inside the 010 mode field)
    // must disagree with LDP.
    fn pair_corrupt(opc: u32, v: u32, l: u32, imm7: u32, rt2: u32, rn: u32, rt: u32) -> u32 {
        (opc << 30)
            | (0b101 << 27)
            | (v << 26)
            | (0b010 << 23)
            | (l << 23) // bug: L at 23, not 22
            | (imm7 << 15)
            | (rt2 << 10)
            | (rn << 5)
            | rt
    }
    assert_ne!(
        pair_corrupt(2, 0, 1, 0, 1, 31, 0),
        f(2, 0, 1, 0, 1, 31, 0),
        "negative control must FAIL: L-at-bit-23 oracle should disagree with the JIT"
    );

    drop(buffer);
}

// ═══════════════════════════════════════════════════════════════════════════
// The ADDRESSING-MODE cluster (encoding_mem.rs) — Result<u32, EncodeError>
// ═══════════════════════════════════════════════════════════════════════════

/// Canonical view of a JIT/native `Result<u32, EncodeError>` outcome. The JIT
/// side is decoded from the out-buffer bytes at the offsets/tags the EMITTED
/// IR itself bakes in (tag i8 @0: 0=RegisterOutOfRange{reg@1,max@2},
/// 1=Imm12OutOfRange{value:u16@2}, 2=Imm9OutOfRange{value:i16@2},
/// 3=Imm7OutOfRange{value:i8@1}, 6=Ok(u32@4) — Ok occupies the niche after
/// EncodeError's 6 variants); the native side is canonicalized by `match`, so
/// no layout assumption is made about the host-compiled enum.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum MemOut {
    Ok(u32),
    ErrReg { reg: u8, max: u8 },
    ErrImm12 { value: u16 },
    ErrImm9 { value: i16 },
    ErrImm7 { value: i8 },
    Other(u8),
}

#[repr(C, align(8))]
struct RawOut {
    bytes: [u8; 8],
}

const OUT_POISON: u8 = 0xDE;

impl RawOut {
    fn poisoned() -> Self {
        RawOut {
            bytes: [OUT_POISON; 8],
        }
    }
}

fn decode_jit_mem(out: &RawOut) -> MemOut {
    let b = &out.bytes;
    match b[0] {
        6 => MemOut::Ok(u32::from_le_bytes([b[4], b[5], b[6], b[7]])),
        0 => MemOut::ErrReg {
            reg: b[1],
            max: b[2],
        },
        1 => MemOut::ErrImm12 {
            value: u16::from_le_bytes([b[2], b[3]]),
        },
        2 => MemOut::ErrImm9 {
            value: i16::from_le_bytes([b[2], b[3]]),
        },
        3 => MemOut::ErrImm7 { value: b[1] as i8 },
        t => MemOut::Other(t),
    }
}

fn canon_native_mem(r: Result<u32, prod_encoding_mem::EncodeError>) -> MemOut {
    match r {
        Ok(w) => MemOut::Ok(w),
        Err(prod_encoding_mem::EncodeError::RegisterOutOfRange { reg, max }) => {
            MemOut::ErrReg { reg, max }
        }
        Err(prod_encoding_mem::EncodeError::Imm12OutOfRange { value }) => {
            MemOut::ErrImm12 { value }
        }
        Err(prod_encoding_mem::EncodeError::Imm9OutOfRange { value }) => MemOut::ErrImm9 { value },
        Err(prod_encoding_mem::EncodeError::Imm7OutOfRange { value }) => MemOut::ErrImm7 { value },
        Err(other) => panic!("unexpected native error variant: {other:?}"),
    }
}

/// Decode a JIT `Result<(), EncodeError>` (unit Ok: tag-only) for the
/// standalone validator drives.
fn decode_jit_unit(out: &RawOut) -> MemOut {
    let b = &out.bytes;
    match b[0] {
        6 => MemOut::Ok(0),
        0 => MemOut::ErrReg {
            reg: b[1],
            max: b[2],
        },
        1 => MemOut::ErrImm12 {
            value: u16::from_le_bytes([b[2], b[3]]),
        },
        2 => MemOut::ErrImm9 {
            value: i16::from_le_bytes([b[2], b[3]]),
        },
        3 => MemOut::ErrImm7 { value: b[1] as i8 },
        t => MemOut::Other(t),
    }
}

// JIT signatures per the emitted functy declarations (Result through the
// out-pointer; operand enums as their u8 tags; bool as bool).
type UnsOffFn = extern "C" fn(*mut RawOut, u8, bool, u8, u16, u8, u8);
type PrePostFn = extern "C" fn(*mut RawOut, u8, bool, u8, i16, u8, u8);
type RegOffFn = extern "C" fn(*mut RawOut, u8, bool, u8, u8, u8, bool, u8, u8);
type LdpWrapFn = extern "C" fn(*mut RawOut, u8, bool, u8, i8, u8, u8, u8);
type LdpFn = extern "C" fn(*mut RawOut, u8, bool, u8, u8, i8, u8, u8, u8);
type LdrswFn = extern "C" fn(*mut RawOut, u8, u8, u8);
type CheckRegFn = extern "C" fn(*mut RawOut, u8, u8);
type CheckImm12Fn = extern "C" fn(*mut RawOut, u16);
type CheckImm9Fn = extern "C" fn(*mut RawOut, i16);
type CheckImm7Fn = extern "C" fn(*mut RawOut, i8);

const SIZES: [LoadStoreSize; 4] = [
    LoadStoreSize::Byte,
    LoadStoreSize::Half,
    LoadStoreSize::Word,
    LoadStoreSize::Double,
];
const LSOPS: [LoadStoreOp; 2] = [LoadStoreOp::Store, LoadStoreOp::Load];
const EXTENDS: [RegExtend; 4] = [
    RegExtend::Uxtw,
    RegExtend::Lsl,
    RegExtend::Sxtw,
    RegExtend::Sxtx,
];
const PAIR_SIZES: [PairSize; 2] = [PairSize::W32, PairSize::X64];
const PAIR_OPS: [PairOp; 2] = [PairOp::StorePair, PairOp::LoadPair];
const PAIR_MODES: [PairMode; 3] = [
    PairMode::PostIndex,
    PairMode::SignedOffset,
    PairMode::PreIndex,
];

const REGS8: [u8; 6] = [0, 1, 2, 15, 30, 31];
const BAD_REGS8: [u8; 4] = [32, 63, 200, 255];

/// TRUST-SELF round 3: `encode_ldr_str_unsigned_offset` (the scaled-offset
/// LDR/STR every stack access routes through) + `check_imm12` — native (REAL
/// production fns) == JIT across Ok / ErrReg / ErrImm12 paths, `check_imm12`
/// then EXHAUSTIVE over all 65536 u16 inputs.
#[test]
fn trust_self3_encode_ldr_str_unsigned_offset_roundtrip() {
    let buffer = jit_module(
        LDR_STR_UNSIGNED_OFFSET_TRUST_IR,
        "encode_ldr_str_unsigned_offset",
    );
    // SAFETY: machine code for `(ptr, u8, bool, u8, u16, u8, u8) -> ()` per
    // functy.0 (Result through the out-pointer).
    let f: UnsOffFn =
        unsafe { std::mem::transmute(bind(&buffer, "encode_ldr_str_unsigned_offset")) };

    let mut pass = 0usize;
    let (mut ok_seen, mut err_reg_seen, mut err_imm_seen) = (0usize, 0usize, 0usize);
    for &size in &SIZES {
        for v in [false, true] {
            for &op in &LSOPS {
                for &imm12 in &[0u16, 1, 42, 2047, 4095, 4096, 0x7FFF, 0xFFFF] {
                    for &rn in REGS8.iter().chain(&BAD_REGS8) {
                        let rt = (rn ^ (imm12 as u8)) % 32;
                        let native =
                            canon_native_mem(prod_encoding_mem::encode_ldr_str_unsigned_offset(
                                size, v, op, imm12, rn, rt,
                            ));
                        let mut out = RawOut::poisoned();
                        f(
                            &mut out as *mut RawOut,
                            size as u8,
                            v,
                            op as u8,
                            imm12,
                            rn,
                            rt,
                        );
                        assert_ne!(
                            out.bytes[0], OUT_POISON,
                            "JIT must write the Result tag (poison survived) at imm12={imm12} rn={rn}"
                        );
                        let jit = decode_jit_mem(&out);
                        assert_eq!(
                            native, jit,
                            "TRUST-SELF encode_ldr_str_unsigned_offset JIT disagrees at \
                             size={size:?} v={v} op={op:?} imm12={imm12} rn={rn} rt={rt}: \
                             native={native:?} jit={jit:?}"
                        );
                        match jit {
                            MemOut::Ok(_) => ok_seen += 1,
                            MemOut::ErrReg { .. } => err_reg_seen += 1,
                            MemOut::ErrImm12 { .. } => err_imm_seen += 1,
                            other => panic!("unexpected outcome {other:?}"),
                        }
                        pass += 1;
                    }
                }
            }
        }
    }
    assert_eq!(pass, 4 * 2 * 2 * 8 * 10);
    assert!(
        ok_seen > 0 && err_reg_seen > 0 && err_imm_seen > 0,
        "sweep must exercise Ok ({ok_seen}), ErrReg ({err_reg_seen}), ErrImm12 ({err_imm_seen})"
    );

    // Ground truth (production unit test): LDR W3, [X5, #64] -> imm12=16.
    let mut out = RawOut::poisoned();
    f(
        &mut out as *mut RawOut,
        LoadStoreSize::Word as u8,
        false,
        LoadStoreOp::Load as u8,
        16,
        5,
        3,
    );
    assert_eq!(
        decode_jit_mem(&out),
        MemOut::Ok(0xB940_40A3),
        "LDR W3, [X5, #64]"
    );

    // Precedence differentials: production checks rn, then rt, then imm12.
    let mut out = RawOut::poisoned();
    f(
        &mut out as *mut RawOut,
        LoadStoreSize::Double as u8,
        false,
        LoadStoreOp::Load as u8,
        9999,
        40,
        50,
    );
    assert_eq!(
        decode_jit_mem(&out),
        MemOut::ErrReg { reg: 40, max: 31 },
        "rn must be checked before rt and imm12 in the JIT, as in production"
    );
    let mut out = RawOut::poisoned();
    f(
        &mut out as *mut RawOut,
        LoadStoreSize::Double as u8,
        false,
        LoadStoreOp::Load as u8,
        9999,
        3,
        50,
    );
    assert_eq!(
        decode_jit_mem(&out),
        MemOut::ErrReg { reg: 50, max: 31 },
        "rt must be checked before imm12 in the JIT, as in production"
    );

    // Standalone EXHAUSTIVE differential for the in-module check_imm12 over
    // its ENTIRE u16 domain. Oracle: VERBATIM check_imm12 semantics
    // (encoding_mem.rs:118-124; private fn, transcribed): value > 4095 -> Err.
    // SAFETY: machine code for `(ptr, u16) -> ()` per functy.2.
    let fi: CheckImm12Fn = unsafe { std::mem::transmute(bind(&buffer, "check_imm12")) };
    for value in 0..=u16::MAX {
        let mut out = RawOut::poisoned();
        fi(&mut out as *mut RawOut, value);
        let native = if value > 4095 {
            MemOut::ErrImm12 { value }
        } else {
            MemOut::Ok(0)
        };
        assert_eq!(
            native,
            decode_jit_unit(&out),
            "TRUST-SELF check_imm12 JIT disagrees at value={value}"
        );
    }

    // NEGATIVE CONTROL: an off-by-one oracle (rejects at >= 4095) must
    // DISAGREE with the JIT at exactly 4095.
    let mut out = RawOut::poisoned();
    fi(&mut out as *mut RawOut, 4095);
    let corrupt = MemOut::ErrImm12 { value: 4095 }; // what a >=4095 oracle claims
    assert_ne!(
        corrupt,
        decode_jit_unit(&out),
        "negative control must FAIL: off-by-one imm12 oracle should disagree with the JIT"
    );
    assert_eq!(decode_jit_unit(&out), MemOut::Ok(0), "4095 is in range");

    drop(buffer);
}

/// Shared driver for the pre-index / post-index LDR/STR modules: full
/// (size, v, op) product x the imm9 boundary span x reg edge cases against
/// the REAL production fn, then `check_imm9` EXHAUSTIVE over all 65536 i16
/// inputs, then the mode-marker negative control (pre 0b11 vs post 0b01 —
/// each module must disagree with the OTHER mode's production word).
fn run_prepost_roundtrip(
    module_text: &str,
    root_sym: &str,
    native: fn(
        LoadStoreSize,
        bool,
        LoadStoreOp,
        i16,
        u8,
        u8,
    ) -> Result<u32, prod_encoding_mem::EncodeError>,
    other_mode_native: fn(
        LoadStoreSize,
        bool,
        LoadStoreOp,
        i16,
        u8,
        u8,
    ) -> Result<u32, prod_encoding_mem::EncodeError>,
) {
    let buffer = jit_module(module_text, root_sym);
    // SAFETY: machine code for `(ptr, u8, bool, u8, i16, u8, u8) -> ()` per
    // functy.0 (Result through the out-pointer).
    let f: PrePostFn = unsafe { std::mem::transmute(bind(&buffer, root_sym)) };

    let run = |size: LoadStoreSize, v: bool, op: LoadStoreOp, imm9: i16, rn: u8, rt: u8| {
        let mut out = RawOut::poisoned();
        f(
            &mut out as *mut RawOut,
            size as u8,
            v,
            op as u8,
            imm9,
            rn,
            rt,
        );
        assert_ne!(
            out.bytes[0], OUT_POISON,
            "JIT must write the Result tag (poison survived) at imm9={imm9} rn={rn} rt={rt}"
        );
        decode_jit_mem(&out)
    };

    let mut pass = 0usize;
    let (mut ok_seen, mut err_reg_seen, mut err_imm_seen) = (0usize, 0usize, 0usize);
    for &size in &SIZES {
        for v in [false, true] {
            for &op in &LSOPS {
                for imm9 in -260..=259i16 {
                    let rn = (imm9.unsigned_abs() % 32) as u8;
                    let rt = ((imm9.unsigned_abs() >> 5) % 32) as u8;
                    let native_out = canon_native_mem(native(size, v, op, imm9, rn, rt));
                    let jit = run(size, v, op, imm9, rn, rt);
                    assert_eq!(
                        native_out, jit,
                        "TRUST-SELF {root_sym} JIT disagrees at size={size:?} v={v} op={op:?} \
                         imm9={imm9} rn={rn} rt={rt}: native={native_out:?} jit={jit:?}"
                    );
                    match jit {
                        MemOut::Ok(_) => ok_seen += 1,
                        MemOut::ErrReg { .. } => err_reg_seen += 1,
                        MemOut::ErrImm9 { .. } => err_imm_seen += 1,
                        other => panic!("unexpected outcome {other:?}"),
                    }
                    pass += 1;
                }
            }
        }
    }
    assert_eq!(pass, 4 * 2 * 2 * 520);
    // i16 extremes + bad regs (rn checked before rt, both before imm9).
    for &(imm9, rn, rt) in &[
        (i16::MIN, 0u8, 0u8),
        (i16::MAX, 31, 31),
        (-256, 31, 30),
        (255, 30, 31),
        (0, 40, 0),
        (0, 0, 200),
        (300, 99, 88),
    ] {
        let native_out = canon_native_mem(native(
            LoadStoreSize::Double,
            false,
            LoadStoreOp::Load,
            imm9,
            rn,
            rt,
        ));
        let jit = run(
            LoadStoreSize::Double,
            false,
            LoadStoreOp::Load,
            imm9,
            rn,
            rt,
        );
        assert_eq!(
            native_out, jit,
            "TRUST-SELF {root_sym} JIT disagrees at edge imm9={imm9} rn={rn} rt={rt}"
        );
        match jit {
            MemOut::Ok(_) => ok_seen += 1,
            MemOut::ErrReg { .. } => err_reg_seen += 1,
            MemOut::ErrImm9 { .. } => err_imm_seen += 1,
            other => panic!("unexpected outcome {other:?}"),
        }
    }
    assert!(
        ok_seen > 0 && err_reg_seen > 0 && err_imm_seen > 0,
        "sweep must exercise Ok ({ok_seen}), ErrReg ({err_reg_seen}), ErrImm9 ({err_imm_seen})"
    );
    // Precedence: rn before rt.
    assert_eq!(
        run(LoadStoreSize::Double, false, LoadStoreOp::Load, 400, 99, 88),
        MemOut::ErrReg { reg: 99, max: 31 },
        "rn must be checked before rt and imm9 in the JIT, as in production"
    );

    // Standalone EXHAUSTIVE differential for the in-module check_imm9 over
    // its ENTIRE i16 domain. Oracle: VERBATIM check_imm9 semantics
    // (encoding_mem.rs:126-132; private fn, transcribed with the verbatim
    // RangeInclusive::contains): !(-256..=255).contains(&value) -> Err.
    // SAFETY: machine code for `(ptr, i16) -> ()` per functy.2.
    let fi: CheckImm9Fn = unsafe { std::mem::transmute(bind(&buffer, "check_imm9")) };
    for value in i16::MIN..=i16::MAX {
        let mut out = RawOut::poisoned();
        fi(&mut out as *mut RawOut, value);
        let native = if !(-256..=255).contains(&value) {
            MemOut::ErrImm9 { value }
        } else {
            MemOut::Ok(0)
        };
        assert_eq!(
            native,
            decode_jit_unit(&out),
            "TRUST-SELF check_imm9 JIT disagrees at value={value}"
        );
    }

    // NEGATIVE CONTROL (mode marker): the OTHER addressing mode's production
    // word must DISAGREE with this module's JIT on an in-range input (pre
    // writes 0b11 at bits 11:10, post writes 0b01 — a swapped-marker encoder
    // is exactly this corruption).
    let jit = run(LoadStoreSize::Double, false, LoadStoreOp::Store, -16, 31, 2);
    let other = canon_native_mem(other_mode_native(
        LoadStoreSize::Double,
        false,
        LoadStoreOp::Store,
        -16,
        31,
        2,
    ));
    assert_ne!(
        other, jit,
        "negative control must FAIL: the other mode's marker word should disagree with the JIT"
    );

    drop(buffer);
}

/// TRUST-SELF round 3: `encode_ldr_str_pre_index` (writeback-before
/// addressing) + `check_imm9` (exhaustive i16) — native == JIT across
/// Ok / ErrReg / ErrImm9, plus the production pinned word and the
/// swapped-mode-marker negative control.
#[test]
fn trust_self3_encode_ldr_str_pre_index_roundtrip() {
    run_prepost_roundtrip(
        LDR_STR_PRE_INDEX_TRUST_IR,
        "encode_ldr_str_pre_index",
        prod_encoding_mem::encode_ldr_str_pre_index,
        prod_encoding_mem::encode_ldr_str_post_index,
    );

    // Ground truth (production unit test): STR X2, [SP, #-16]!.
    let buffer = jit_module(LDR_STR_PRE_INDEX_TRUST_IR, "encode_ldr_str_pre_index");
    let f: PrePostFn = unsafe { std::mem::transmute(bind(&buffer, "encode_ldr_str_pre_index")) };
    let mut out = RawOut::poisoned();
    f(
        &mut out as *mut RawOut,
        LoadStoreSize::Double as u8,
        false,
        LoadStoreOp::Store as u8,
        -16,
        31,
        2,
    );
    assert_eq!(
        decode_jit_mem(&out),
        MemOut::Ok(0xF81F_0FE2),
        "STR X2, [SP, #-16]!"
    );
    drop(buffer);
}

/// TRUST-SELF round 3: `encode_ldr_str_post_index` (writeback-after
/// addressing) — same full differential as pre-index, opposite mode marker.
#[test]
fn trust_self3_encode_ldr_str_post_index_roundtrip() {
    run_prepost_roundtrip(
        LDR_STR_POST_INDEX_TRUST_IR,
        "encode_ldr_str_post_index",
        prod_encoding_mem::encode_ldr_str_post_index,
        prod_encoding_mem::encode_ldr_str_pre_index,
    );

    // Ground truth (production unit test): LDR X30, [SP], #16.
    let buffer = jit_module(LDR_STR_POST_INDEX_TRUST_IR, "encode_ldr_str_post_index");
    let f: PrePostFn = unsafe { std::mem::transmute(bind(&buffer, "encode_ldr_str_post_index")) };
    let mut out = RawOut::poisoned();
    f(
        &mut out as *mut RawOut,
        LoadStoreSize::Double as u8,
        false,
        LoadStoreOp::Load as u8,
        16,
        31,
        30,
    );
    assert_eq!(
        decode_jit_mem(&out),
        MemOut::Ok(0xF841_07FE),
        "LDR X30, [SP], #16"
    );
    drop(buffer);
}

/// TRUST-SELF round 3: `encode_ldr_str_register` (register-offset addressing
/// — every computed-index load/store) — native (REAL production fn) == JIT
/// over the full size x v x op x rm x extend x shift x rn product (4608
/// in-contract words) + all three ErrReg positions in precedence order.
#[test]
fn trust_self3_encode_ldr_str_register_roundtrip() {
    let buffer = jit_module(LDR_STR_REGISTER_TRUST_IR, "encode_ldr_str_register");
    // SAFETY: machine code for `(ptr, u8, bool, u8, u8, u8, bool, u8, u8) -> ()`
    // per functy.0 (Result through the out-pointer).
    let f: RegOffFn = unsafe { std::mem::transmute(bind(&buffer, "encode_ldr_str_register")) };

    let run = |size: LoadStoreSize,
               v: bool,
               op: LoadStoreOp,
               rm: u8,
               extend: RegExtend,
               shift: bool,
               rn: u8,
               rt: u8| {
        let mut out = RawOut::poisoned();
        f(
            &mut out as *mut RawOut,
            size as u8,
            v,
            op as u8,
            rm,
            extend as u8,
            shift,
            rn,
            rt,
        );
        assert_ne!(out.bytes[0], OUT_POISON, "JIT must write the Result tag");
        decode_jit_mem(&out)
    };

    let mut pass = 0usize;
    for &size in &SIZES {
        for v in [false, true] {
            for &op in &LSOPS {
                for &rm in &REGS8 {
                    for &extend in &EXTENDS {
                        for shift in [false, true] {
                            for &rn in &REGS8 {
                                let rt = (rm ^ rn) % 32;
                                let native =
                                    canon_native_mem(prod_encoding_mem::encode_ldr_str_register(
                                        size, v, op, rm, extend, shift, rn, rt,
                                    ));
                                let jit = run(size, v, op, rm, extend, shift, rn, rt);
                                assert_eq!(
                                    native, jit,
                                    "TRUST-SELF encode_ldr_str_register JIT disagrees at \
                                     size={size:?} v={v} op={op:?} rm={rm} extend={extend:?} \
                                     shift={shift} rn={rn} rt={rt}: native={native:?} jit={jit:?}"
                                );
                                pass += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(pass, 4 * 2 * 2 * 6 * 4 * 2 * 6);

    // Ground truths (production unit tests): LDR X7, [X6, X4, LSL #3] and
    // STR W0, [X1, W2, SXTW].
    assert_eq!(
        run(
            LoadStoreSize::Double,
            false,
            LoadStoreOp::Load,
            4,
            RegExtend::Lsl,
            true,
            6,
            7
        ),
        MemOut::Ok(0xF864_78C7),
        "LDR X7, [X6, X4, LSL #3]"
    );
    assert_eq!(
        run(
            LoadStoreSize::Word,
            false,
            LoadStoreOp::Store,
            2,
            RegExtend::Sxtw,
            false,
            1,
            0
        ),
        MemOut::Ok(0xB822_C820),
        "STR W0, [X1, W2, SXTW]"
    );

    // All three ErrReg positions, in production precedence order (rm, rn, rt)
    // — each differentially against the production fn AND pinned.
    for &(rm, rn, rt, want) in &[
        (77u8, 88u8, 99u8, MemOut::ErrReg { reg: 77, max: 31 }),
        (4, 88, 99, MemOut::ErrReg { reg: 88, max: 31 }),
        (4, 6, 99, MemOut::ErrReg { reg: 99, max: 31 }),
    ] {
        let native = canon_native_mem(prod_encoding_mem::encode_ldr_str_register(
            LoadStoreSize::Double,
            false,
            LoadStoreOp::Load,
            rm,
            RegExtend::Lsl,
            true,
            rn,
            rt,
        ));
        let jit = run(
            LoadStoreSize::Double,
            false,
            LoadStoreOp::Load,
            rm,
            RegExtend::Lsl,
            true,
            rn,
            rt,
        );
        assert_eq!(native, jit, "error precedence at rm={rm} rn={rn} rt={rt}");
        assert_eq!(jit, want, "pinned precedence at rm={rm} rn={rn} rt={rt}");
    }

    // NEGATIVE CONTROL: an oracle that forgets the S (shift) bit must
    // disagree with the JIT when shift=true.
    fn regoff_corrupt(size: u32, v: u32, op: u32, rm: u32, extend: u32, rn: u32, rt: u32) -> u32 {
        (size << 30)
            | (0b111 << 27)
            | (v << 26)
            | (op << 22)
            | (1 << 21)
            | (rm << 16)
            | (extend << 13)
            // bug: S bit dropped
            | (0b10 << 10)
            | (rn << 5)
            | rt
    }
    assert_ne!(
        MemOut::Ok(regoff_corrupt(3, 0, 1, 4, 0b011, 6, 7)),
        run(
            LoadStoreSize::Double,
            false,
            LoadStoreOp::Load,
            4,
            RegExtend::Lsl,
            true,
            6,
            7
        ),
        "negative control must FAIL: S-bit-forgetting oracle should disagree with the JIT"
    );

    drop(buffer);
}

/// TRUST-SELF round 3: `encode_ldrsw_register` (the sign-extending word load
/// behind every i32-indexed access) — native (REAL production fn) == JIT
/// EXHAUSTIVELY over rm x rn x rt in 0..=33 cubed (39304 calls: the entire
/// valid domain plus the first out-of-range band in every position) + far
/// out-of-range probes.
#[test]
fn trust_self3_encode_ldrsw_register_roundtrip() {
    let buffer = jit_module(LDRSW_REGISTER_TRUST_IR, "encode_ldrsw_register");
    // SAFETY: machine code for `(ptr, u8, u8, u8) -> ()` per functy.0.
    let f: LdrswFn = unsafe { std::mem::transmute(bind(&buffer, "encode_ldrsw_register")) };

    let run = |rm: u8, rn: u8, rt: u8| {
        let mut out = RawOut::poisoned();
        f(&mut out as *mut RawOut, rm, rn, rt);
        assert_ne!(out.bytes[0], OUT_POISON, "JIT must write the Result tag");
        decode_jit_mem(&out)
    };

    let mut pass = 0usize;
    let (mut ok_seen, mut err_seen) = (0usize, 0usize);
    for rm in 0..=33u8 {
        for rn in 0..=33u8 {
            for rt in 0..=33u8 {
                let native = canon_native_mem(prod_encoding_mem::encode_ldrsw_register(rm, rn, rt));
                let jit = run(rm, rn, rt);
                assert_eq!(
                    native, jit,
                    "TRUST-SELF encode_ldrsw_register JIT disagrees at rm={rm} rn={rn} rt={rt}: \
                     native={native:?} jit={jit:?}"
                );
                match jit {
                    MemOut::Ok(_) => ok_seen += 1,
                    MemOut::ErrReg { .. } => err_seen += 1,
                    other => panic!("unexpected outcome {other:?}"),
                }
                pass += 1;
            }
        }
    }
    assert_eq!(pass, 34 * 34 * 34);
    assert_eq!(ok_seen, 32 * 32 * 32, "the whole valid domain must encode");
    assert_eq!(err_seen, 34 * 34 * 34 - 32 * 32 * 32);
    // Far out-of-range + precedence (rm before rn before rt).
    assert_eq!(run(255, 255, 255), MemOut::ErrReg { reg: 255, max: 31 });
    assert_eq!(run(0, 200, 200), MemOut::ErrReg { reg: 200, max: 31 });

    // Ground truth (ARM ARM): LDRSW X0, [X1, X2, LSL #2] = 0xB8A27820.
    assert_eq!(
        run(2, 1, 0),
        MemOut::Ok(0xB8A2_7820),
        "LDRSW X0, [X1, X2, LSL #2]"
    );

    // NEGATIVE CONTROL: an oracle that forgets S=1 (the LSL #2 scale bit)
    // must disagree with the JIT.
    let corrupt = 0xB8A2_7820u32 & !(1 << 12);
    assert_ne!(
        MemOut::Ok(corrupt),
        run(2, 1, 0),
        "negative control must FAIL: scale-bit-forgetting oracle should disagree with the JIT"
    );

    drop(buffer);
}

/// Shared driver for one LDP/STP wrapper module: full pair_size x v x pair_op
/// x FULL i8 imm7 span x reg spread against the REAL production wrapper,
/// exercising Ok / ErrReg / ErrImm7.
type NativePairEncoder =
    fn(PairSize, bool, PairOp, i8, u8, u8, u8) -> Result<u32, prod_encoding_mem::EncodeError>;

fn run_ldp_wrapper_roundtrip(module_text: &str, root_sym: &str, native: NativePairEncoder) {
    let buffer = jit_module(module_text, root_sym);
    // SAFETY: machine code for `(ptr, u8, bool, u8, i8, u8, u8, u8) -> ()` per
    // functy.0 (Result through the out-pointer).
    let f: LdpWrapFn = unsafe { std::mem::transmute(bind(&buffer, root_sym)) };

    let mut pass = 0usize;
    let (mut ok_seen, mut err_imm_seen) = (0usize, 0usize);
    for &pair_size in &PAIR_SIZES {
        for v in [false, true] {
            for &pair_op in &PAIR_OPS {
                for imm7 in i8::MIN..=i8::MAX {
                    let rt2 = (imm7.unsigned_abs()) % 32;
                    let rn = (imm7.unsigned_abs().wrapping_mul(7)) % 32;
                    let rt = (imm7.unsigned_abs() >> 2) % 32;
                    let native_out =
                        canon_native_mem(native(pair_size, v, pair_op, imm7, rt2, rn, rt));
                    let mut out = RawOut::poisoned();
                    f(
                        &mut out as *mut RawOut,
                        pair_size as u8,
                        v,
                        pair_op as u8,
                        imm7,
                        rt2,
                        rn,
                        rt,
                    );
                    assert_ne!(out.bytes[0], OUT_POISON, "JIT must write the Result tag");
                    let jit = decode_jit_mem(&out);
                    assert_eq!(
                        native_out, jit,
                        "TRUST-SELF {root_sym} JIT disagrees at pair_size={pair_size:?} v={v} \
                         pair_op={pair_op:?} imm7={imm7} rt2={rt2} rn={rn} rt={rt}: \
                         native={native_out:?} jit={jit:?}"
                    );
                    match jit {
                        MemOut::Ok(_) => ok_seen += 1,
                        MemOut::ErrImm7 { .. } => err_imm_seen += 1,
                        other => panic!("unexpected outcome {other:?}"),
                    }
                    pass += 1;
                }
            }
        }
    }
    assert_eq!(pass, 2 * 2 * 2 * 256);
    // Bad-reg probes (the ErrReg path — unreachable from the in-range reg
    // spread above, so exercised + PINNED here, each also differentially
    // against the production fn): production checks rt FIRST, then rt2, then
    // rn, then imm7.
    let probe = |imm7: i8, rt2: u8, rn: u8, rt: u8| {
        let native_out = canon_native_mem(native(
            PairSize::X64,
            false,
            PairOp::LoadPair,
            imm7,
            rt2,
            rn,
            rt,
        ));
        let mut out = RawOut::poisoned();
        f(
            &mut out as *mut RawOut,
            PairSize::X64 as u8,
            false,
            PairOp::LoadPair as u8,
            imm7,
            rt2,
            rn,
            rt,
        );
        let jit = decode_jit_mem(&out);
        assert_eq!(
            native_out, jit,
            "{root_sym} reg-probe at rt2={rt2} rn={rn} rt={rt}"
        );
        jit
    };
    assert_eq!(
        probe(-100, 88, 77, 99),
        MemOut::ErrReg { reg: 99, max: 31 },
        "rt must be checked FIRST in the JIT, as in production"
    );
    assert_eq!(probe(-100, 88, 77, 0), MemOut::ErrReg { reg: 88, max: 31 });
    assert_eq!(probe(-100, 1, 77, 0), MemOut::ErrReg { reg: 77, max: 31 });
    assert_eq!(probe(-100, 1, 31, 0), MemOut::ErrImm7 { value: -100 });
    assert!(
        ok_seen > 0 && err_imm_seen > 0,
        "sweep must exercise Ok ({ok_seen}) and ErrImm7 ({err_imm_seen})"
    );

    drop(buffer);
}

/// TRUST-SELF round 3: `encode_ldp_stp_offset` (signed-offset LDP/STP) + the
/// underlying `encode_ldp_stp` driven DIRECTLY over ALL THREE PairModes + the
/// validators `check_imm7` (exhaustive i8) and `check_reg` (exhaustive
/// 256x256) — native (REAL production fns) == JIT.
#[test]
fn trust_self3_encode_ldp_stp_offset_roundtrip() {
    run_ldp_wrapper_roundtrip(
        LDP_STP_OFFSET_TRUST_IR,
        "encode_ldp_stp_offset",
        prod_encoding_mem::encode_ldp_stp_offset,
    );

    let buffer = jit_module(LDP_STP_OFFSET_TRUST_IR, "encode_ldp_stp_offset");

    // Ground truth (production unit test): LDP X9, X10, [SP, #-64] (imm7=-8).
    let fw: LdpWrapFn = unsafe { std::mem::transmute(bind(&buffer, "encode_ldp_stp_offset")) };
    let mut out = RawOut::poisoned();
    fw(
        &mut out as *mut RawOut,
        PairSize::X64 as u8,
        false,
        PairOp::LoadPair as u8,
        -8,
        10,
        31,
        9,
    );
    assert_eq!(
        decode_jit_mem(&out),
        MemOut::Ok(0xA97C_2BE9),
        "LDP X9, X10, [SP, #-64]"
    );

    // Drive the IN-MODULE `encode_ldp_stp` DIRECTLY over ALL THREE PairModes
    // (the wrapper only ever passes SignedOffset; this covers the full mode
    // arg domain of the underlying encoder against the production fn).
    // SAFETY: machine code for `(ptr, u8, bool, u8, u8, i8, u8, u8, u8) -> ()`
    // per functy.1.
    let fm: LdpFn = unsafe { std::mem::transmute(bind(&buffer, "encode_ldp_stp")) };
    let mut pass = 0usize;
    for &pair_size in &PAIR_SIZES {
        for v in [false, true] {
            for &pair_op in &PAIR_OPS {
                for &mode in &PAIR_MODES {
                    for &imm7 in &[-64i8, -8, -2, -1, 0, 1, 2, 63, -65, 64, i8::MIN, i8::MAX] {
                        for &rt2 in &[0u8, 1, 30, 31] {
                            let (rn, rt) = (31u8, (rt2 + 9) % 32);
                            let native = canon_native_mem(prod_encoding_mem::encode_ldp_stp(
                                pair_size, v, pair_op, mode, imm7, rt2, rn, rt,
                            ));
                            let mut out = RawOut::poisoned();
                            fm(
                                &mut out as *mut RawOut,
                                pair_size as u8,
                                v,
                                pair_op as u8,
                                mode as u8,
                                imm7,
                                rt2,
                                rn,
                                rt,
                            );
                            assert_ne!(out.bytes[0], OUT_POISON, "JIT must write the Result tag");
                            let jit = decode_jit_mem(&out);
                            assert_eq!(
                                native, jit,
                                "TRUST-SELF encode_ldp_stp (direct) JIT disagrees at \
                                 pair_size={pair_size:?} v={v} pair_op={pair_op:?} mode={mode:?} \
                                 imm7={imm7} rt2={rt2} rn={rn} rt={rt}: native={native:?} \
                                 jit={jit:?}"
                            );
                            pass += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(pass, 2 * 2 * 2 * 3 * 12 * 4);

    // Standalone EXHAUSTIVE differential for the in-module check_imm7 over
    // its ENTIRE i8 domain. Oracle: VERBATIM check_imm7 semantics
    // (encoding_mem.rs:134-140; private fn, transcribed with the verbatim
    // RangeInclusive::contains): !(-64..=63).contains(&value) -> Err.
    // SAFETY: machine code for `(ptr, i8) -> ()` per functy.3.
    let fi: CheckImm7Fn = unsafe { std::mem::transmute(bind(&buffer, "check_imm7")) };
    for value in i8::MIN..=i8::MAX {
        let mut out = RawOut::poisoned();
        fi(&mut out as *mut RawOut, value);
        let native = if !(-64..=63).contains(&value) {
            MemOut::ErrImm7 { value }
        } else {
            MemOut::Ok(0)
        };
        assert_eq!(
            native,
            decode_jit_unit(&out),
            "TRUST-SELF check_imm7 JIT disagrees at value={value}"
        );
    }

    // Standalone EXHAUSTIVE differential for the in-module check_reg over
    // ALL 65536 (reg, max) pairs. Oracle: VERBATIM check_reg semantics
    // (encoding_mem.rs:110-116): reg > max -> Err (round 2 verified this fn
    // at 3 max values; this closes the full domain).
    // SAFETY: machine code for `(ptr, u8, u8) -> ()` per functy.2.
    let fr: CheckRegFn = unsafe { std::mem::transmute(bind(&buffer, "check_reg")) };
    for reg in 0..=u8::MAX {
        for max in 0..=u8::MAX {
            let mut out = RawOut::poisoned();
            fr(&mut out as *mut RawOut, reg, max);
            let native = if reg > max {
                MemOut::ErrReg { reg, max }
            } else {
                MemOut::Ok(0)
            };
            assert_eq!(
                native,
                decode_jit_unit(&out),
                "TRUST-SELF check_reg JIT disagrees at reg={reg} max={max}"
            );
        }
    }

    // NEGATIVE CONTROL: an off-by-one check_imm7 oracle (rejects at >= 63)
    // must DISAGREE with the JIT at exactly 63.
    let mut out = RawOut::poisoned();
    fi(&mut out as *mut RawOut, 63);
    assert_ne!(
        MemOut::ErrImm7 { value: 63 },
        decode_jit_unit(&out),
        "negative control must FAIL: off-by-one imm7 oracle should disagree with the JIT"
    );
    assert_eq!(decode_jit_unit(&out), MemOut::Ok(0), "63 is in range");

    // NEGATIVE CONTROL (mode): a wrong-mode oracle (PreIndex word for the
    // SignedOffset wrapper) must disagree with the wrapper's JIT.
    let mut out = RawOut::poisoned();
    fw(
        &mut out as *mut RawOut,
        PairSize::X64 as u8,
        false,
        PairOp::LoadPair as u8,
        -8,
        10,
        31,
        9,
    );
    let wrong_mode = canon_native_mem(prod_encoding_mem::encode_ldp_stp(
        PairSize::X64,
        false,
        PairOp::LoadPair,
        PairMode::PreIndex,
        -8,
        10,
        31,
        9,
    ));
    assert_ne!(
        wrong_mode,
        decode_jit_mem(&out),
        "negative control must FAIL: a PreIndex-mode oracle should disagree with the \
         SignedOffset wrapper's JIT"
    );

    drop(buffer);
}

/// TRUST-SELF round 3: `encode_ldp_stp_pre_index` (writeback pair — the
/// prologue STP form) — full wrapper differential + production pinned word.
#[test]
fn trust_self3_encode_ldp_stp_pre_index_roundtrip() {
    run_ldp_wrapper_roundtrip(
        LDP_STP_PRE_INDEX_TRUST_IR,
        "encode_ldp_stp_pre_index",
        prod_encoding_mem::encode_ldp_stp_pre_index,
    );

    // Ground truth (production unit test): STP X29, X30, [SP, #-16]!.
    let buffer = jit_module(LDP_STP_PRE_INDEX_TRUST_IR, "encode_ldp_stp_pre_index");
    let f: LdpWrapFn = unsafe { std::mem::transmute(bind(&buffer, "encode_ldp_stp_pre_index")) };
    let mut out = RawOut::poisoned();
    f(
        &mut out as *mut RawOut,
        PairSize::X64 as u8,
        false,
        PairOp::StorePair as u8,
        -2,
        30,
        31,
        29,
    );
    assert_eq!(
        decode_jit_mem(&out),
        MemOut::Ok(0xA9BF_7BFD),
        "STP X29, X30, [SP, #-16]!"
    );

    // NEGATIVE CONTROL (mode): the SignedOffset word must disagree.
    let wrong_mode = canon_native_mem(prod_encoding_mem::encode_ldp_stp_offset(
        PairSize::X64,
        false,
        PairOp::StorePair,
        -2,
        30,
        31,
        29,
    ));
    assert_ne!(
        wrong_mode,
        decode_jit_mem(&out),
        "negative control must FAIL: a SignedOffset-mode oracle should disagree with the \
         PreIndex wrapper's JIT"
    );
    drop(buffer);
}

/// TRUST-SELF round 3: `encode_ldp_stp_post_index` (writeback pair — the
/// epilogue LDP form) — full wrapper differential + production pinned word.
#[test]
fn trust_self3_encode_ldp_stp_post_index_roundtrip() {
    run_ldp_wrapper_roundtrip(
        LDP_STP_POST_INDEX_TRUST_IR,
        "encode_ldp_stp_post_index",
        prod_encoding_mem::encode_ldp_stp_post_index,
    );

    // Ground truth (production unit test): LDP X29, X30, [SP], #16.
    let buffer = jit_module(LDP_STP_POST_INDEX_TRUST_IR, "encode_ldp_stp_post_index");
    let f: LdpWrapFn = unsafe { std::mem::transmute(bind(&buffer, "encode_ldp_stp_post_index")) };
    let mut out = RawOut::poisoned();
    f(
        &mut out as *mut RawOut,
        PairSize::X64 as u8,
        false,
        PairOp::LoadPair as u8,
        2,
        30,
        31,
        29,
    );
    assert_eq!(
        decode_jit_mem(&out),
        MemOut::Ok(0xA8C1_7BFD),
        "LDP X29, X30, [SP], #16"
    );

    // NEGATIVE CONTROL (mode): the PreIndex word must disagree.
    let wrong_mode = canon_native_mem(prod_encoding_mem::encode_ldp_stp_pre_index(
        PairSize::X64,
        false,
        PairOp::LoadPair,
        2,
        30,
        31,
        29,
    ));
    assert_ne!(
        wrong_mode,
        decode_jit_mem(&out),
        "negative control must FAIL: a PreIndex-mode oracle should disagree with the \
         PostIndex wrapper's JIT"
    );
    drop(buffer);
}
