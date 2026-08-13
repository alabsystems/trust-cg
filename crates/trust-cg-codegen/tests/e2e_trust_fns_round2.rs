//! TRUST-SELF ROUND 2 (thread T4): verifying MORE OF TRUST ITSELF —
//! trust-cg's own AArch64 INSTRUCTION ENCODERS — through the full pipeline
//! Rust -> MIR -> trust-ir (stage1 `trust_ir_mir --mir-emit-closure`) ->
//! trust-cg JIT -> machine code, asserting native Rust == JIT over swept
//! real inputs. These are the functions that assemble the very machine words
//! trust-cg emits: a wrong field shift here is a wrong instruction in every
//! compiled program (including the JIT running this test).
//!
//! New verified functions in this file (15):
//!   * the LOGICAL-IMMEDIATE cluster (encode.rs): `low_mask`,
//!     `rotate_right_within`, `replicate_logical_element`,
//!     `encode_logical_imm_fields` (the AArch64 bitmask-immediate search —
//!     exhaustively swept over ALL 5334 encodable 64-bit + 1302 encodable
//!     32-bit immediates, plus non-encodable probes, cross-checked against
//!     the production `encode_instruction` AndRI path)
//!   * the WORD BUILDERS (encoding.rs): `encode_add_sub_shifted_reg`,
//!     `encode_logical_shifted_reg`, `encode_add_sub_imm`,
//!     `encode_move_wide` (incl. the #387/#447 defensive masking),
//!     `encode_cond_branch`, `encode_cmp_branch`, `encode_load_store_unscaled`
//!   * the PC-RELATIVE cluster (encoding_mem.rs): `encode_adrp`, `encode_adr`,
//!     `check_reg`, `check_imm21` (Result<_, EncodeError> enum returns,
//!     error paths differentially exercised)
//!
//! Slices (verbatim transcriptions, modeled boundaries documented inline):
//!   <dev-scratch>/t4-trust/trust_logimm_slice.rs
//!   <dev-scratch>/t4-trust/trust_encwords_slice.rs
//!   <dev-scratch>/t4-trust/trust_adrp_slice.rs
//!
//! REGEN (per module):
//!   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//!   cd $HOME/trust-ir/frontend && env -u RUSTUP_TOOLCHAIN RUSTC=$S/bin/rustc \
//!     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//!     $S/bin/cargo run --bin trust_ir_mir -- <slice.rs> --crate-type=lib \
//!     --mir-emit-closure <fn> <out.tir>
//!
//! MODELED BOUNDARIES (each also documented at the affected fixture below and
//! in the slice files):
//!   * `debug_assert!` guards are STRIPPED from the encoding.rs word-builder
//!     slices — release-mode semantics (trust-cg ships with debug-assertions
//!     off). PINNED FRONTEND LIMIT: a body containing `debug_assert!` fails
//!     to lower ("call arg constant of non-scalar type ref" — the expanded
//!     `core::panicking::panic("...")` call's &str constant; MIR Assert
//!     TERMINATORS lower fine, explicit panic CALLS do not). Verified domain
//!     = the encoder contract domain (in-range fields).
//!   * `encode_logical_imm_fields`: diagnostic-only error payload modeled as
//!     `Err(())` (production: `EncodeError::InvalidOperand` with a `format!`
//!     string; the `opcode`/`index` params exist only for that diagnostic);
//!     const-slice iteration `&[2,4,8,16,32(,64)]` rewritten as a doubling
//!     while-loop (identical sequence for register_width ∈ {32,64});
//!     `for x in a..b` rewritten as while-loops and `u32::from(bool)` as an
//!     `as` cast (Range::into_iter/next and From::from lower to EMPTY extern
//!     bodies — pinned frontend limit). Every rewrite is differentially
//!     checked against the verbatim-form native oracle transcribed here.
//!   * `encode_adrp`/`encode_adr`: `?` rewritten as explicit match — PINNED
//!     FRONTEND LIMIT: `?` on Result lowers to EMPTY-bodied
//!     `<Result as Try>::branch` / `FromResidual::from_residual` externs (the
//!     Result-flavored sibling of the known Option-Try shim gap). Oracle is
//!     the REAL production `encoding_mem::encode_adrp`/`encode_adr` (verbatim
//!     `?` form).
//!   * `check_imm21`: `(-1_048_576..=1_048_575).contains(&value)` rewritten
//!     as explicit comparisons (RangeInclusive::contains does not lower —
//!     known frontend limit). Oracle: real production via encode_adrp/adr.
//!
//! BACKEND-VALIDATOR FINDING (documented, same family as the type_max
//! u128::MAX spelling divergence): every module here that shifts by a
//! CONSTANT amount carries `validate_module` BinOpTypeMismatch errors — the
//! MIR lowering spells constant shift amounts as `const i32` against a
//! u32/u64 lhs (`shl u32 %x, (const i32 24)`), which trust-ir's validator
//! rejects as a type mismatch, while trust-cg codegen consumes the constant's
//! bit pattern correctly (proven by every differential in this file. The
//! validator and the lowering disagree on the spelling; neither miscompiles).
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

/// VERBATIM MIR-closure emit of the LOGICAL-IMMEDIATE cluster (5 in-module fns:
/// the packing root + `encode_logical_imm_fields` + `low_mask` +
/// `rotate_right_within` + `replicate_logical_element`). Emit reported:
///   EMIT-CLOSURE-OK encode_logical_imm_fields_packed: 10954 bytes; 5 closure
///   member(s); validate_module = 4 error(s); re-parse OK
/// The 4 validator errors are ALL the documented const-shift-amount spelling
/// divergence (`shl u32 %x, (const i32 1)` for `element_width << 1` /
/// `<<= 1` — lowering spells constant shift amounts as i32; the validator wants
/// matching signedness; codegen consumes the bit pattern correctly, which this
/// file's differentials prove). Slice: t4-trust/trust_logimm_slice.rs (modeled
/// boundaries: diagnostic-only error payload -> Err(()); const-slice iteration ->
/// doubling while; Range for-loops -> while; u32::from -> as-cast; ALL
/// differentially checked against the verbatim-form native oracle below).
/// Regen: trust_ir_mir trust_logimm_slice.rs --crate-type=lib
///   --mir-emit-closure encode_logical_imm_fields_packed <out.tir>
const LOGIMM_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_logical_imm_fields_packed"

functy.0 = (i64, u32) -> (u64)

functy.1 = (ptr, i64, u32) -> ()

functy.2 = (u32) -> (u64)

functy.3 = (u64, u32, u32) -> (u64)

functy.4 = (u64, u32, u32) -> (u64)

fn @encode_logical_imm_fields_packed(functy.0) {
bb0(%0: i64, %1: u32):
    %13 = alloca (i32, i32, i32, i32), align 4
    call @func.1(%13, %0, %1)
    br bb1
bb1:
    %14 = load i32, ptr %13
    %15 = sext i32 %14 to i64
    switch %15 [ 0: bb4 1: bb3 default: bb2 ]
bb2:
    unreachable
bb3:
    %16 = const u64 0
    br bb8(%16)
bb4:
    %17 = const i64 4
    %18 = gep i8, ptr %13, %17
    %19 = load u32, ptr %18
    %20 = const i64 8
    %21 = gep i8, ptr %13, %20
    %22 = load u32, ptr %21
    %23 = const i64 12
    %24 = gep i8, ptr %13, %23
    %25 = load u32, ptr %24
    %26 = const i32 63
    %27 = bitcast i32 %26 to u32
    %28 = const u32 64
    %29 = icmp ult u32 %27, %28
    condbr %29, bb5(%19, %22, %25), bb9
bb5(%2: u32, %3: u32, %4: u32):
    %30 = const u64 1
    %31 = const i32 63
    %32 = zext i32 %31 to u64
    %33 = shl u64 %30, %32
    %34 = zext u32 %2 to u64
    %35 = const i32 12
    %36 = bitcast i32 %35 to u32
    %37 = const u32 64
    %38 = icmp ult u32 %36, %37
    condbr %38, bb6(%3, %4, %33, %34), bb9
bb6(%5: u32, %6: u32, %7: u64, %8: u64):
    %39 = const i32 12
    %40 = zext i32 %39 to u64
    %41 = shl u64 %8, %40
    %42 = or u64 %7, %41
    %43 = zext u32 %5 to u64
    %44 = const i32 6
    %45 = bitcast i32 %44 to u32
    %46 = const u32 64
    %47 = icmp ult u32 %45, %46
    condbr %47, bb7(%6, %42, %43), bb9
bb7(%9: u32, %10: u64, %11: u64):
    %48 = const i32 6
    %49 = zext i32 %48 to u64
    %50 = shl u64 %11, %49
    %51 = or u64 %10, %50
    %52 = zext u32 %9 to u64
    %53 = or u64 %51, %52
    br bb8(%53)
bb8(%12: u64):
    ret %12
bb9:
    unreachable
}

fn @encode_logical_imm_fields(functy.1) {
bb0(%0: ptr, %1: i64, %2: u32):
    %93 = alloca (i32, i32), align 4
    %94 = alloca (i32, i32), align 4
    %95 = alloca (i32, i32, i32), align 4
    %96 = alloca (i32, i32), align 4
    %97 = alloca (i32, i32), align 4
    %98 = call @func.2(%2)
    br bb1(%1, %2, %98)
bb1(%3: i64, %4: u32, %5: u64):
    %99 = bitcast i64 %3 to u64
    %100 = and u64 %99, %5
    %101 = const u64 0
    %102 = icmp eq u64 %100, %101
    condbr %102, bb3, bb2(%4, %5, %100)
bb2(%6: u32, %7: u64, %8: u64):
    %103 = icmp eq u64 %8, %7
    condbr %103, bb3, bb4(%6, %8)
bb3:
    %104 = const i32 1
    store i32 %104, ptr %0
    br bb25
bb4(%9: u32, %10: u64):
    %105 = const u32 2
    br bb5(%9, %10, %105)
bb5(%11: u32, %12: u64, %13: u32):
    %106 = icmp ule u32 %13, %11
    condbr %106, bb6(%11, %12, %13), bb24
bb6(%14: u32, %15: u64, %16: u32):
    %107 = const u32 1
    br bb7(%14, %15, %16, %107)
bb7(%17: u32, %18: u64, %19: u32, %20: u32):
    %108 = icmp ult u32 %20, %19
    condbr %108, bb8(%17, %18, %19, %20), bb22(%17, %18, %19)
bb8(%21: u32, %22: u64, %23: u32, %24: u32):
    %109 = call @func.2(%24)
    br bb9(%21, %22, %23, %24, %109)
bb9(%25: u32, %26: u64, %27: u32, %28: u32, %29: u64):
    %110 = const u32 0
    br bb10(%25, %26, %27, %28, %29, %110)
bb10(%30: u32, %31: u64, %32: u32, %33: u32, %34: u64, %35: u32):
    %111 = icmp ult u32 %35, %32
    condbr %111, bb11(%30, %31, %32, %33, %34, %35), bb20(%30, %31, %32, %33)
bb11(%36: u32, %37: u64, %38: u32, %39: u32, %40: u64, %41: u32):
    %112 = call @func.3(%40, %41, %38)
    br bb12(%36, %37, %38, %39, %40, %41, %112)
bb12(%42: u32, %43: u64, %44: u32, %45: u32, %46: u64, %47: u32, %48: u64):
    %113 = call @func.4(%48, %44, %42)
    br bb13(%42, %43, %44, %45, %46, %47, %113)
bb13(%49: u32, %50: u64, %51: u32, %52: u32, %53: u64, %54: u32, %55: u64):
    %114 = icmp eq u64 %55, %50
    condbr %114, bb14(%51, %52, %54), bb18(%49, %50, %51, %52, %53, %54)
bb14(%56: u32, %57: u32, %58: u32):
    %115 = const u32 64
    %116 = icmp eq u32 %56, %115
    %117 = const u32 1
    %118 = const u32 0
    %119 = select u32 %116, %117, %118
    %120 = const u32 63
    %121 = and u32 %58, %120
    %122 = const i32 1
    %123 = bitcast i32 %122 to u32
    %124 = const u32 32
    %125 = icmp ult u32 %123, %124
    condbr %125, bb15(%57, %119, %121, %56), bb26
bb15(%59: u32, %60: u32, %61: u32, %62: u32):
    %126 = const i32 1
    %127 = shl u32 %62, %126
    %128 = const u32 1
    %129, %130 = sub.overflow u32 %127, %128
    store u32 %129, ptr %93
    %131 = const i64 4
    %132 = gep i8, ptr %93, %131
    store bool %130, ptr %132
    %133 = const i64 4
    %134 = gep i8, ptr %93, %133
    %135 = load bool, ptr %134
    %136 = const bool false
    %137 = icmp eq bool %135, %136
    condbr %137, bb16(%59, %60, %61), bb26
bb16(%63: u32, %64: u32, %65: u32):
    %138 = load u32, ptr %93
    %139 = not u32 %138
    %140 = const u32 63
    %141 = and u32 %139, %140
    %142 = const u32 1
    %143, %144 = sub.overflow u32 %63, %142
    store u32 %143, ptr %94
    %145 = const i64 4
    %146 = gep i8, ptr %94, %145
    store bool %144, ptr %146
    %147 = const i64 4
    %148 = gep i8, ptr %94, %147
    %149 = load bool, ptr %148
    %150 = const bool false
    %151 = icmp eq bool %149, %150
    condbr %151, bb17(%64, %65, %141), bb26
bb17(%66: u32, %67: u32, %68: u32):
    %152 = load u32, ptr %94
    %153 = or u32 %68, %152
    store u32 %66, ptr %95
    %154 = const i64 4
    %155 = gep i8, ptr %95, %154
    store u32 %67, ptr %155
    %156 = const i64 8
    %157 = gep i8, ptr %95, %156
    store u32 %153, ptr %157
    %158 = const i64 4
    %159 = gep i8, ptr %0, %158
    %160 = load i32, ptr %95
    store i32 %160, ptr %159
    %161 = const i64 4
    %162 = gep i8, ptr %95, %161
    %163 = const i64 4
    %164 = gep i8, ptr %159, %163
    %165 = load i32, ptr %162
    store i32 %165, ptr %164
    %166 = const i64 8
    %167 = gep i8, ptr %95, %166
    %168 = const i64 8
    %169 = gep i8, ptr %159, %168
    %170 = load i32, ptr %167
    store i32 %170, ptr %169
    %171 = const i32 0
    store i32 %171, ptr %0
    br bb25
bb18(%69: u32, %70: u64, %71: u32, %72: u32, %73: u64, %74: u32):
    %172 = const u32 1
    %173, %174 = add.overflow u32 %74, %172
    store u32 %173, ptr %96
    %175 = const i64 4
    %176 = gep i8, ptr %96, %175
    store bool %174, ptr %176
    %177 = const i64 4
    %178 = gep i8, ptr %96, %177
    %179 = load bool, ptr %178
    %180 = const bool false
    %181 = icmp eq bool %179, %180
    condbr %181, bb19(%69, %70, %71, %72, %73), bb26
bb19(%75: u32, %76: u64, %77: u32, %78: u32, %79: u64):
    %182 = load u32, ptr %96
    br bb10(%75, %76, %77, %78, %79, %182)
bb20(%80: u32, %81: u64, %82: u32, %83: u32):
    %183 = const u32 1
    %184, %185 = add.overflow u32 %83, %183
    store u32 %184, ptr %97
    %186 = const i64 4
    %187 = gep i8, ptr %97, %186
    store bool %185, ptr %187
    %188 = const i64 4
    %189 = gep i8, ptr %97, %188
    %190 = load bool, ptr %189
    %191 = const bool false
    %192 = icmp eq bool %190, %191
    condbr %192, bb21(%80, %81, %82), bb26
bb21(%84: u32, %85: u64, %86: u32):
    %193 = load u32, ptr %97
    br bb7(%84, %85, %86, %193)
bb22(%87: u32, %88: u64, %89: u32):
    %194 = const i32 1
    %195 = bitcast i32 %194 to u32
    %196 = const u32 32
    %197 = icmp ult u32 %195, %196
    condbr %197, bb23(%87, %88, %89), bb26
bb23(%90: u32, %91: u64, %92: u32):
    %198 = const i32 1
    %199 = shl u32 %92, %198
    br bb5(%90, %91, %199)
bb24:
    %200 = const i32 1
    store i32 %200, ptr %0
    br bb25
bb25:
    ret
bb26:
    unreachable
}

fn @low_mask(functy.2) {
bb0(%0: u32):
    %4 = alloca (i64, i64), align 8
    %5 = const u32 64
    %6 = icmp eq u32 %0, %5
    condbr %6, bb1, bb2(%0)
bb1:
    %7 = const u64 18446744073709551615
    br bb5(%7)
bb2(%1: u32):
    %8 = const u32 64
    %9 = icmp ult u32 %1, %8
    condbr %9, bb3(%1), bb6
bb3(%2: u32):
    %10 = const u64 1
    %11 = zext u32 %2 to u64
    %12 = shl u64 %10, %11
    %13 = const u64 1
    %14, %15 = sub.overflow u64 %12, %13
    store u64 %14, ptr %4
    %16 = const i64 8
    %17 = gep i8, ptr %4, %16
    store bool %15, ptr %17
    %18 = const i64 8
    %19 = gep i8, ptr %4, %18
    %20 = load bool, ptr %19
    %21 = const bool false
    %22 = icmp eq bool %20, %21
    condbr %22, bb4, bb6
bb4:
    %23 = load u64, ptr %4
    br bb5(%23)
bb5(%3: u64):
    ret %3
bb6:
    unreachable
}

fn @rotate_right_within(functy.3) {
bb0(%0: u64, %1: u32, %2: u32):
    %24 = alloca (i32, i32), align 4
    %25 = call @func.2(%2)
    br bb1(%0, %1, %2, %25)
bb1(%3: u64, %4: u32, %5: u32, %6: u64):
    %26 = and u64 %3, %6
    %27 = const u32 0
    %28 = icmp eq u32 %4, %27
    condbr %28, bb2(%26), bb3(%4, %5, %6, %26)
bb2(%7: u64):
    br bb7(%7)
bb3(%8: u32, %9: u32, %10: u64, %11: u64):
    %29 = const u32 64
    %30 = icmp ult u32 %8, %29
    condbr %30, bb4(%8, %9, %10, %11), bb8
bb4(%12: u32, %13: u32, %14: u64, %15: u64):
    %31 = zext u32 %12 to u64
    %32 = lshr u64 %15, %31
    %33, %34 = sub.overflow u32 %13, %12
    store u32 %33, ptr %24
    %35 = const i64 4
    %36 = gep i8, ptr %24, %35
    store bool %34, ptr %36
    %37 = const i64 4
    %38 = gep i8, ptr %24, %37
    %39 = load bool, ptr %38
    %40 = const bool false
    %41 = icmp eq bool %39, %40
    condbr %41, bb5(%14, %15, %32), bb8
bb5(%16: u64, %17: u64, %18: u64):
    %42 = load u32, ptr %24
    %43 = const u32 64
    %44 = icmp ult u32 %42, %43
    condbr %44, bb6(%16, %17, %18, %42), bb8
bb6(%19: u64, %20: u64, %21: u64, %22: u32):
    %45 = zext u32 %22 to u64
    %46 = shl u64 %20, %45
    %47 = or u64 %21, %46
    %48 = and u64 %47, %19
    br bb7(%48)
bb7(%23: u64):
    ret %23
bb8:
    unreachable
}

fn @replicate_logical_element(functy.4) {
bb0(%0: u64, %1: u32, %2: u32):
    %27 = alloca (i32, i32), align 4
    %28 = const u64 0
    %29 = const u32 0
    br bb1(%0, %1, %2, %28, %29)
bb1(%3: u64, %4: u32, %5: u32, %6: u64, %7: u32):
    %30 = icmp ult u32 %7, %5
    condbr %30, bb2(%3, %4, %5, %6, %7), bb5(%5, %6)
bb2(%8: u64, %9: u32, %10: u32, %11: u64, %12: u32):
    %31 = const u32 64
    %32 = icmp ult u32 %12, %31
    condbr %32, bb3(%8, %9, %10, %11, %12, %12), bb7
bb3(%13: u64, %14: u32, %15: u32, %16: u64, %17: u32, %18: u32):
    %33 = zext u32 %18 to u64
    %34 = shl u64 %13, %33
    %35 = or u64 %16, %34
    %36, %37 = add.overflow u32 %17, %14
    store u32 %36, ptr %27
    %38 = const i64 4
    %39 = gep i8, ptr %27, %38
    store bool %37, ptr %39
    %40 = const i64 4
    %41 = gep i8, ptr %27, %40
    %42 = load bool, ptr %41
    %43 = const bool false
    %44 = icmp eq bool %42, %43
    condbr %44, bb4(%13, %14, %15, %35), bb7
bb4(%19: u64, %20: u32, %21: u32, %22: u64):
    %45 = load u32, ptr %27
    br bb1(%19, %20, %21, %22, %45)
bb5(%23: u32, %24: u64):
    %46 = call @func.2(%23)
    br bb6(%24, %46)
bb6(%25: u64, %26: u64):
    %47 = and u64 %25, %26
    ret %47
bb7:
    unreachable
}
"#;

/// VERBATIM MIR-closure emit of the production `encode_add_sub_shifted_reg`
/// (encoding.rs; debug_assert! guards stripped in the slice = release-mode
/// semantics — see the module-header MODELED BOUNDARIES). Emit reported:
/// 1 closure member; validate_module = 16 error(s), ALL the documented
/// const-shift-amount spelling divergence (const i32 shift amounts against u32
/// lhs) + the inlined shift-width checks' bitcasts; re-parse OK.
/// Slice: t4-trust/trust_encwords_slice.rs.
/// Regen: trust_ir_mir trust_encwords_slice.rs --crate-type=lib
///   --mir-emit-closure encode_add_sub_shifted_reg <out.tir>
const ENC_ADD_SUB_SHIFTED_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_add_sub_shifted_reg"

functy.0 = (u32, u32, u32, u32, u32, u32, u32, u32) -> (u32)

fn @encode_add_sub_shifted_reg(functy.0) {
bb0(%0: u32, %1: u32, %2: u32, %3: u32, %4: u32, %5: u32, %6: u32, %7: u32):
    %55 = const i32 31
    %56 = bitcast i32 %55 to u32
    %57 = const u32 32
    %58 = icmp ult u32 %56, %57
    condbr %58, bb1(%0, %1, %2, %3, %4, %5, %6, %7), bb9
bb1(%8: u32, %9: u32, %10: u32, %11: u32, %12: u32, %13: u32, %14: u32, %15: u32):
    %59 = const i32 31
    %60 = shl u32 %8, %59
    %61 = const i32 30
    %62 = bitcast i32 %61 to u32
    %63 = const u32 32
    %64 = icmp ult u32 %62, %63
    condbr %64, bb2(%9, %10, %11, %12, %13, %14, %15, %60), bb9
bb2(%16: u32, %17: u32, %18: u32, %19: u32, %20: u32, %21: u32, %22: u32, %23: u32):
    %65 = const i32 30
    %66 = shl u32 %16, %65
    %67 = or u32 %23, %66
    %68 = const i32 29
    %69 = bitcast i32 %68 to u32
    %70 = const u32 32
    %71 = icmp ult u32 %69, %70
    condbr %71, bb3(%17, %18, %19, %20, %21, %22, %67), bb9
bb3(%24: u32, %25: u32, %26: u32, %27: u32, %28: u32, %29: u32, %30: u32):
    %72 = const i32 29
    %73 = shl u32 %24, %72
    %74 = or u32 %30, %73
    %75 = const i32 24
    %76 = bitcast i32 %75 to u32
    %77 = const u32 32
    %78 = icmp ult u32 %76, %77
    condbr %78, bb4(%25, %26, %27, %28, %29, %74), bb9
bb4(%31: u32, %32: u32, %33: u32, %34: u32, %35: u32, %36: u32):
    %79 = const u32 11
    %80 = const i32 24
    %81 = shl u32 %79, %80
    %82 = or u32 %36, %81
    %83 = const i32 22
    %84 = bitcast i32 %83 to u32
    %85 = const u32 32
    %86 = icmp ult u32 %84, %85
    condbr %86, bb5(%31, %32, %33, %34, %35, %82), bb9
bb5(%37: u32, %38: u32, %39: u32, %40: u32, %41: u32, %42: u32):
    %87 = const i32 22
    %88 = shl u32 %37, %87
    %89 = or u32 %42, %88
    %90 = const i32 16
    %91 = bitcast i32 %90 to u32
    %92 = const u32 32
    %93 = icmp ult u32 %91, %92
    condbr %93, bb6(%38, %39, %40, %41, %89), bb9
bb6(%43: u32, %44: u32, %45: u32, %46: u32, %47: u32):
    %94 = const i32 16
    %95 = shl u32 %43, %94
    %96 = or u32 %47, %95
    %97 = const i32 10
    %98 = bitcast i32 %97 to u32
    %99 = const u32 32
    %100 = icmp ult u32 %98, %99
    condbr %100, bb7(%44, %45, %46, %96), bb9
bb7(%48: u32, %49: u32, %50: u32, %51: u32):
    %101 = const i32 10
    %102 = shl u32 %48, %101
    %103 = or u32 %51, %102
    %104 = const i32 5
    %105 = bitcast i32 %104 to u32
    %106 = const u32 32
    %107 = icmp ult u32 %105, %106
    condbr %107, bb8(%49, %50, %103), bb9
bb8(%52: u32, %53: u32, %54: u32):
    %108 = const i32 5
    %109 = shl u32 %52, %108
    %110 = or u32 %54, %109
    %111 = or u32 %110, %53
    ret %111
bb9:
    unreachable
}
"#;

/// VERBATIM MIR-closure emit of the production `encode_logical_shifted_reg`
/// (encoding.rs; debug_assert! guards stripped in the slice = release-mode
/// semantics — see the module-header MODELED BOUNDARIES). Emit reported:
/// 1 closure member; validate_module = 16 error(s), ALL the documented
/// const-shift-amount spelling divergence (const i32 shift amounts against u32
/// lhs) + the inlined shift-width checks' bitcasts; re-parse OK.
/// Slice: t4-trust/trust_encwords_slice.rs.
/// Regen: trust_ir_mir trust_encwords_slice.rs --crate-type=lib
///   --mir-emit-closure encode_logical_shifted_reg <out.tir>
const ENC_LOGICAL_SHIFTED_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_logical_shifted_reg"

functy.0 = (u32, u32, u32, u32, u32, u32, u32, u32) -> (u32)

fn @encode_logical_shifted_reg(functy.0) {
bb0(%0: u32, %1: u32, %2: u32, %3: u32, %4: u32, %5: u32, %6: u32, %7: u32):
    %56 = const i32 31
    %57 = bitcast i32 %56 to u32
    %58 = const u32 32
    %59 = icmp ult u32 %57, %58
    condbr %59, bb1(%0, %1, %2, %3, %4, %5, %6, %7), bb9
bb1(%8: u32, %9: u32, %10: u32, %11: u32, %12: u32, %13: u32, %14: u32, %15: u32):
    %60 = const i32 31
    %61 = shl u32 %8, %60
    %62 = const i32 29
    %63 = bitcast i32 %62 to u32
    %64 = const u32 32
    %65 = icmp ult u32 %63, %64
    condbr %65, bb2(%9, %10, %11, %12, %13, %14, %15, %61), bb9
bb2(%16: u32, %17: u32, %18: u32, %19: u32, %20: u32, %21: u32, %22: u32, %23: u32):
    %66 = const i32 29
    %67 = shl u32 %16, %66
    %68 = or u32 %23, %67
    %69 = const i32 24
    %70 = bitcast i32 %69 to u32
    %71 = const u32 32
    %72 = icmp ult u32 %70, %71
    condbr %72, bb3(%17, %18, %19, %20, %21, %22, %68), bb9
bb3(%24: u32, %25: u32, %26: u32, %27: u32, %28: u32, %29: u32, %30: u32):
    %73 = const u32 10
    %74 = const i32 24
    %75 = shl u32 %73, %74
    %76 = or u32 %30, %75
    %77 = const i32 22
    %78 = bitcast i32 %77 to u32
    %79 = const u32 32
    %80 = icmp ult u32 %78, %79
    condbr %80, bb4(%24, %25, %26, %27, %28, %29, %76), bb9
bb4(%31: u32, %32: u32, %33: u32, %34: u32, %35: u32, %36: u32, %37: u32):
    %81 = const i32 22
    %82 = shl u32 %31, %81
    %83 = or u32 %37, %82
    %84 = const i32 21
    %85 = bitcast i32 %84 to u32
    %86 = const u32 32
    %87 = icmp ult u32 %85, %86
    condbr %87, bb5(%32, %33, %34, %35, %36, %83), bb9
bb5(%38: u32, %39: u32, %40: u32, %41: u32, %42: u32, %43: u32):
    %88 = const i32 21
    %89 = shl u32 %38, %88
    %90 = or u32 %43, %89
    %91 = const i32 16
    %92 = bitcast i32 %91 to u32
    %93 = const u32 32
    %94 = icmp ult u32 %92, %93
    condbr %94, bb6(%39, %40, %41, %42, %90), bb9
bb6(%44: u32, %45: u32, %46: u32, %47: u32, %48: u32):
    %95 = const i32 16
    %96 = shl u32 %44, %95
    %97 = or u32 %48, %96
    %98 = const i32 10
    %99 = bitcast i32 %98 to u32
    %100 = const u32 32
    %101 = icmp ult u32 %99, %100
    condbr %101, bb7(%45, %46, %47, %97), bb9
bb7(%49: u32, %50: u32, %51: u32, %52: u32):
    %102 = const i32 10
    %103 = shl u32 %49, %102
    %104 = or u32 %52, %103
    %105 = const i32 5
    %106 = bitcast i32 %105 to u32
    %107 = const u32 32
    %108 = icmp ult u32 %106, %107
    condbr %108, bb8(%50, %51, %104), bb9
bb8(%53: u32, %54: u32, %55: u32):
    %109 = const i32 5
    %110 = shl u32 %53, %109
    %111 = or u32 %55, %110
    %112 = or u32 %111, %54
    ret %112
bb9:
    unreachable
}
"#;

/// VERBATIM MIR-closure emit of the production `encode_add_sub_imm`
/// (encoding.rs; debug_assert! guards stripped in the slice = release-mode
/// semantics — see the module-header MODELED BOUNDARIES). Emit reported:
/// 1 closure member; validate_module = 14 error(s), ALL the documented
/// const-shift-amount spelling divergence (const i32 shift amounts against u32
/// lhs) + the inlined shift-width checks' bitcasts; re-parse OK.
/// Slice: t4-trust/trust_encwords_slice.rs.
/// Regen: trust_ir_mir trust_encwords_slice.rs --crate-type=lib
///   --mir-emit-closure encode_add_sub_imm <out.tir>
const ENC_ADD_SUB_IMM_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_add_sub_imm"

functy.0 = (u32, u32, u32, u32, u32, u32, u32) -> (u32)

fn @encode_add_sub_imm(functy.0) {
bb0(%0: u32, %1: u32, %2: u32, %3: u32, %4: u32, %5: u32, %6: u32):
    %44 = const i32 31
    %45 = bitcast i32 %44 to u32
    %46 = const u32 32
    %47 = icmp ult u32 %45, %46
    condbr %47, bb1(%0, %1, %2, %3, %4, %5, %6), bb8
bb1(%7: u32, %8: u32, %9: u32, %10: u32, %11: u32, %12: u32, %13: u32):
    %48 = const i32 31
    %49 = shl u32 %7, %48
    %50 = const i32 30
    %51 = bitcast i32 %50 to u32
    %52 = const u32 32
    %53 = icmp ult u32 %51, %52
    condbr %53, bb2(%8, %9, %10, %11, %12, %13, %49), bb8
bb2(%14: u32, %15: u32, %16: u32, %17: u32, %18: u32, %19: u32, %20: u32):
    %54 = const i32 30
    %55 = shl u32 %14, %54
    %56 = or u32 %20, %55
    %57 = const i32 29
    %58 = bitcast i32 %57 to u32
    %59 = const u32 32
    %60 = icmp ult u32 %58, %59
    condbr %60, bb3(%15, %16, %17, %18, %19, %56), bb8
bb3(%21: u32, %22: u32, %23: u32, %24: u32, %25: u32, %26: u32):
    %61 = const i32 29
    %62 = shl u32 %21, %61
    %63 = or u32 %26, %62
    %64 = const i32 23
    %65 = bitcast i32 %64 to u32
    %66 = const u32 32
    %67 = icmp ult u32 %65, %66
    condbr %67, bb4(%22, %23, %24, %25, %63), bb8
bb4(%27: u32, %28: u32, %29: u32, %30: u32, %31: u32):
    %68 = const u32 34
    %69 = const i32 23
    %70 = shl u32 %68, %69
    %71 = or u32 %31, %70
    %72 = const i32 22
    %73 = bitcast i32 %72 to u32
    %74 = const u32 32
    %75 = icmp ult u32 %73, %74
    condbr %75, bb5(%27, %28, %29, %30, %71), bb8
bb5(%32: u32, %33: u32, %34: u32, %35: u32, %36: u32):
    %76 = const i32 22
    %77 = shl u32 %32, %76
    %78 = or u32 %36, %77
    %79 = const i32 10
    %80 = bitcast i32 %79 to u32
    %81 = const u32 32
    %82 = icmp ult u32 %80, %81
    condbr %82, bb6(%33, %34, %35, %78), bb8
bb6(%37: u32, %38: u32, %39: u32, %40: u32):
    %83 = const i32 10
    %84 = shl u32 %37, %83
    %85 = or u32 %40, %84
    %86 = const i32 5
    %87 = bitcast i32 %86 to u32
    %88 = const u32 32
    %89 = icmp ult u32 %87, %88
    condbr %89, bb7(%38, %39, %85), bb8
bb7(%41: u32, %42: u32, %43: u32):
    %90 = const i32 5
    %91 = shl u32 %41, %90
    %92 = or u32 %43, %91
    %93 = or u32 %92, %42
    ret %93
bb8:
    unreachable
}
"#;

/// VERBATIM MIR-closure emit of the production `encode_move_wide`
/// (encoding.rs; debug_assert! guards stripped in the slice = release-mode
/// semantics — see the module-header MODELED BOUNDARIES). Emit reported:
/// 1 closure member; validate_module = 10 error(s), ALL the documented
/// const-shift-amount spelling divergence (const i32 shift amounts against u32
/// lhs) + the inlined shift-width checks' bitcasts; re-parse OK.
/// Slice: t4-trust/trust_encwords_slice.rs.
/// Regen: trust_ir_mir trust_encwords_slice.rs --crate-type=lib
///   --mir-emit-closure encode_move_wide <out.tir>
const ENC_MOVE_WIDE_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_move_wide"

functy.0 = (u32, u32, u32, u32, u32) -> (u32)

fn @encode_move_wide(functy.0) {
bb0(%0: u32, %1: u32, %2: u32, %3: u32, %4: u32):
    %26 = const u32 3
    %27 = and u32 %2, %26
    %28 = const u32 65535
    %29 = and u32 %3, %28
    %30 = const u32 31
    %31 = and u32 %4, %30
    %32 = const i32 31
    %33 = bitcast i32 %32 to u32
    %34 = const u32 32
    %35 = icmp ult u32 %33, %34
    condbr %35, bb1(%0, %1, %27, %29, %31), bb6
bb1(%5: u32, %6: u32, %7: u32, %8: u32, %9: u32):
    %36 = const i32 31
    %37 = shl u32 %5, %36
    %38 = const i32 29
    %39 = bitcast i32 %38 to u32
    %40 = const u32 32
    %41 = icmp ult u32 %39, %40
    condbr %41, bb2(%6, %7, %8, %9, %37), bb6
bb2(%10: u32, %11: u32, %12: u32, %13: u32, %14: u32):
    %42 = const i32 29
    %43 = shl u32 %10, %42
    %44 = or u32 %14, %43
    %45 = const i32 23
    %46 = bitcast i32 %45 to u32
    %47 = const u32 32
    %48 = icmp ult u32 %46, %47
    condbr %48, bb3(%11, %12, %13, %44), bb6
bb3(%15: u32, %16: u32, %17: u32, %18: u32):
    %49 = const u32 37
    %50 = const i32 23
    %51 = shl u32 %49, %50
    %52 = or u32 %18, %51
    %53 = const i32 21
    %54 = bitcast i32 %53 to u32
    %55 = const u32 32
    %56 = icmp ult u32 %54, %55
    condbr %56, bb4(%15, %16, %17, %52), bb6
bb4(%19: u32, %20: u32, %21: u32, %22: u32):
    %57 = const i32 21
    %58 = shl u32 %19, %57
    %59 = or u32 %22, %58
    %60 = const i32 5
    %61 = bitcast i32 %60 to u32
    %62 = const u32 32
    %63 = icmp ult u32 %61, %62
    condbr %63, bb5(%20, %21, %59), bb6
bb5(%23: u32, %24: u32, %25: u32):
    %64 = const i32 5
    %65 = shl u32 %23, %64
    %66 = or u32 %25, %65
    %67 = or u32 %66, %24
    ret %67
bb6:
    unreachable
}
"#;

/// VERBATIM MIR-closure emit of the production `encode_cond_branch`
/// (encoding.rs; debug_assert! guards stripped in the slice = release-mode
/// semantics — see the module-header MODELED BOUNDARIES). Emit reported:
/// 1 closure member; validate_module = 4 error(s), ALL the documented
/// const-shift-amount spelling divergence (const i32 shift amounts against u32
/// lhs) + the inlined shift-width checks' bitcasts; re-parse OK.
/// Slice: t4-trust/trust_encwords_slice.rs.
/// Regen: trust_ir_mir trust_encwords_slice.rs --crate-type=lib
///   --mir-emit-closure encode_cond_branch <out.tir>
const ENC_COND_BRANCH_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_cond_branch"

functy.0 = (u32, u32) -> (u32)

fn @encode_cond_branch(functy.0) {
bb0(%0: u32, %1: u32):
    %7 = const i32 24
    %8 = bitcast i32 %7 to u32
    %9 = const u32 32
    %10 = icmp ult u32 %8, %9
    condbr %10, bb1(%0, %1), bb3
bb1(%2: u32, %3: u32):
    %11 = const u32 84
    %12 = const i32 24
    %13 = shl u32 %11, %12
    %14 = const i32 5
    %15 = bitcast i32 %14 to u32
    %16 = const u32 32
    %17 = icmp ult u32 %15, %16
    condbr %17, bb2(%2, %3, %13), bb3
bb2(%4: u32, %5: u32, %6: u32):
    %18 = const i32 5
    %19 = shl u32 %4, %18
    %20 = or u32 %6, %19
    %21 = or u32 %20, %5
    ret %21
bb3:
    unreachable
}
"#;

/// VERBATIM MIR-closure emit of the production `encode_cmp_branch`
/// (encoding.rs; debug_assert! guards stripped in the slice = release-mode
/// semantics — see the module-header MODELED BOUNDARIES). Emit reported:
/// 1 closure member; validate_module = 8 error(s), ALL the documented
/// const-shift-amount spelling divergence (const i32 shift amounts against u32
/// lhs) + the inlined shift-width checks' bitcasts; re-parse OK.
/// Slice: t4-trust/trust_encwords_slice.rs.
/// Regen: trust_ir_mir trust_encwords_slice.rs --crate-type=lib
///   --mir-emit-closure encode_cmp_branch <out.tir>
const ENC_CMP_BRANCH_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_cmp_branch"

functy.0 = (u32, u32, u32, u32) -> (u32)

fn @encode_cmp_branch(functy.0) {
bb0(%0: u32, %1: u32, %2: u32, %3: u32):
    %19 = const i32 31
    %20 = bitcast i32 %19 to u32
    %21 = const u32 32
    %22 = icmp ult u32 %20, %21
    condbr %22, bb1(%0, %1, %2, %3), bb5
bb1(%4: u32, %5: u32, %6: u32, %7: u32):
    %23 = const i32 31
    %24 = shl u32 %4, %23
    %25 = const i32 25
    %26 = bitcast i32 %25 to u32
    %27 = const u32 32
    %28 = icmp ult u32 %26, %27
    condbr %28, bb2(%5, %6, %7, %24), bb5
bb2(%8: u32, %9: u32, %10: u32, %11: u32):
    %29 = const u32 26
    %30 = const i32 25
    %31 = shl u32 %29, %30
    %32 = or u32 %11, %31
    %33 = const i32 24
    %34 = bitcast i32 %33 to u32
    %35 = const u32 32
    %36 = icmp ult u32 %34, %35
    condbr %36, bb3(%8, %9, %10, %32), bb5
bb3(%12: u32, %13: u32, %14: u32, %15: u32):
    %37 = const i32 24
    %38 = shl u32 %12, %37
    %39 = or u32 %15, %38
    %40 = const i32 5
    %41 = bitcast i32 %40 to u32
    %42 = const u32 32
    %43 = icmp ult u32 %41, %42
    condbr %43, bb4(%13, %14, %39), bb5
bb4(%16: u32, %17: u32, %18: u32):
    %44 = const i32 5
    %45 = shl u32 %16, %44
    %46 = or u32 %18, %45
    %47 = or u32 %46, %17
    ret %47
bb5:
    unreachable
}
"#;

/// VERBATIM MIR-closure emit of the production `encode_load_store_unscaled`
/// (encoding.rs; debug_assert! guards stripped in the slice = release-mode
/// semantics — see the module-header MODELED BOUNDARIES). Emit reported:
/// 1 closure member; validate_module = 12 error(s), ALL the documented
/// const-shift-amount spelling divergence (const i32 shift amounts against u32
/// lhs) + the inlined shift-width checks' bitcasts; re-parse OK.
/// Slice: t4-trust/trust_encwords_slice.rs.
/// Regen: trust_ir_mir trust_encwords_slice.rs --crate-type=lib
///   --mir-emit-closure encode_load_store_unscaled <out.tir>
const ENC_LDST_UNSCALED_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_load_store_unscaled"

functy.0 = (u32, u32, u32, i32, u32, u32) -> (u32)

fn @encode_load_store_unscaled(functy.0) {
bb0(%0: u32, %1: u32, %2: u32, %3: i32, %4: u32, %5: u32):
    %36 = bitcast i32 %3 to u32
    %37 = const u32 511
    %38 = and u32 %36, %37
    %39 = const i32 30
    %40 = bitcast i32 %39 to u32
    %41 = const u32 32
    %42 = icmp ult u32 %40, %41
    condbr %42, bb1(%0, %1, %2, %4, %5, %38), bb7
bb1(%6: u32, %7: u32, %8: u32, %9: u32, %10: u32, %11: u32):
    %43 = const i32 30
    %44 = shl u32 %6, %43
    %45 = const i32 27
    %46 = bitcast i32 %45 to u32
    %47 = const u32 32
    %48 = icmp ult u32 %46, %47
    condbr %48, bb2(%7, %8, %9, %10, %11, %44), bb7
bb2(%12: u32, %13: u32, %14: u32, %15: u32, %16: u32, %17: u32):
    %49 = const u32 7
    %50 = const i32 27
    %51 = shl u32 %49, %50
    %52 = or u32 %17, %51
    %53 = const i32 26
    %54 = bitcast i32 %53 to u32
    %55 = const u32 32
    %56 = icmp ult u32 %54, %55
    condbr %56, bb3(%12, %13, %14, %15, %16, %52), bb7
bb3(%18: u32, %19: u32, %20: u32, %21: u32, %22: u32, %23: u32):
    %57 = const i32 26
    %58 = shl u32 %18, %57
    %59 = or u32 %23, %58
    %60 = const i32 22
    %61 = bitcast i32 %60 to u32
    %62 = const u32 32
    %63 = icmp ult u32 %61, %62
    condbr %63, bb4(%19, %20, %21, %22, %59), bb7
bb4(%24: u32, %25: u32, %26: u32, %27: u32, %28: u32):
    %64 = const i32 22
    %65 = shl u32 %24, %64
    %66 = or u32 %28, %65
    %67 = const i32 12
    %68 = bitcast i32 %67 to u32
    %69 = const u32 32
    %70 = icmp ult u32 %68, %69
    condbr %70, bb5(%25, %26, %27, %66), bb7
bb5(%29: u32, %30: u32, %31: u32, %32: u32):
    %71 = const i32 12
    %72 = shl u32 %31, %71
    %73 = or u32 %32, %72
    %74 = const i32 5
    %75 = bitcast i32 %74 to u32
    %76 = const u32 32
    %77 = icmp ult u32 %75, %76
    condbr %77, bb6(%29, %30, %73), bb7
bb6(%33: u32, %34: u32, %35: u32):
    %78 = const i32 5
    %79 = shl u32 %33, %78
    %80 = or u32 %35, %79
    %81 = or u32 %80, %34
    ret %81
bb7:
    unreachable
}
"#;

/// VERBATIM MIR-closure emit of the production `encode_adrp` + `check_reg` +
/// `check_imm21` (encoding_mem.rs; `?` -> explicit match and
/// RangeInclusive::contains -> explicit comparisons in the slice — pinned
/// frontend limits, see the module-header MODELED BOUNDARIES). Emit reported:
///   EMIT-CLOSURE-OK encode_adrp: 5066 bytes; 3 closure member(s);
///   validate_module = 10 error(s) (all the const-shift spelling class);
///   re-parse OK. NO empty-bodied externs (verified).
/// Slice: t4-trust/trust_adrp_slice.rs.
/// Regen: trust_ir_mir trust_adrp_slice.rs --crate-type=lib
///   --mir-emit-closure encode_adrp <out.tir>
const ENC_ADRP_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_adrp"

functy.0 = (ptr, i32, u8) -> ()

functy.1 = (ptr, u8, u8) -> ()

functy.2 = (ptr, i32) -> ()

fn @encode_adrp(functy.0) {
bb0(%0: ptr, %1: i32, %2: u8):
    %28 = alloca (i32, i32), align 4
    %29 = alloca (i32, i32), align 4
    %30 = alloca (i32, i32), align 4
    %31 = alloca (i32, i32), align 4
    %32 = const u8 31
    call @func.1(%28, %2, %32)
    br bb1(%1, %2)
bb1(%3: i32, %4: u8):
    %33 = load i8, ptr %28
    %34 = const i8 6
    %35 = icmp eq i8 %33, %34
    %36 = const i64 0
    %37 = const i64 1
    %38 = select i64 %35, %36, %37
    switch %38 [ 0: bb3(%3, %4) 1: bb4 default: bb2 ]
bb2:
    unreachable
bb3(%5: i32, %6: u8):
    call @func.2(%30, %5)
    br bb5(%5, %6)
bb4:
    %39 = load i32, ptr %28
    store i32 %39, ptr %29
    %40 = const i64 4
    %41 = gep i8, ptr %28, %40
    %42 = const i64 4
    %43 = gep i8, ptr %29, %42
    %44 = load i32, ptr %41
    store i32 %44, ptr %43
    %45 = load i32, ptr %29
    store i32 %45, ptr %0
    %46 = const i64 4
    %47 = gep i8, ptr %29, %46
    %48 = const i64 4
    %49 = gep i8, ptr %0, %48
    %50 = load i32, ptr %47
    store i32 %50, ptr %49
    br bb13
bb5(%7: i32, %8: u8):
    %51 = load i8, ptr %30
    %52 = const i8 6
    %53 = icmp eq i8 %51, %52
    %54 = const i64 0
    %55 = const i64 1
    %56 = select i64 %53, %54, %55
    switch %56 [ 0: bb6(%7, %8) 1: bb7 default: bb2 ]
bb6(%9: i32, %10: u8):
    %57 = bitcast i32 %9 to u32
    %58 = const u32 2097151
    %59 = and u32 %57, %58
    %60 = const u32 3
    %61 = and u32 %59, %60
    %62 = const i32 2
    %63 = bitcast i32 %62 to u32
    %64 = const u32 32
    %65 = icmp ult u32 %63, %64
    condbr %65, bb8(%10, %59, %61), bb14
bb7:
    %66 = load i32, ptr %30
    store i32 %66, ptr %31
    %67 = const i64 4
    %68 = gep i8, ptr %30, %67
    %69 = const i64 4
    %70 = gep i8, ptr %31, %69
    %71 = load i32, ptr %68
    store i32 %71, ptr %70
    %72 = load i32, ptr %31
    store i32 %72, ptr %0
    %73 = const i64 4
    %74 = gep i8, ptr %31, %73
    %75 = const i64 4
    %76 = gep i8, ptr %0, %75
    %77 = load i32, ptr %74
    store i32 %77, ptr %76
    br bb13
bb8(%11: u8, %12: u32, %13: u32):
    %78 = const i32 2
    %79 = lshr u32 %12, %78
    %80 = const u32 0
    %81 = const i32 31
    %82 = bitcast i32 %81 to u32
    %83 = const u32 32
    %84 = icmp ult u32 %82, %83
    condbr %84, bb9(%11, %13, %79, %80), bb14
bb9(%14: u8, %15: u32, %16: u32, %17: u32):
    %85 = const u32 1
    %86 = const i32 31
    %87 = shl u32 %85, %86
    %88 = or u32 %17, %87
    %89 = const i32 29
    %90 = bitcast i32 %89 to u32
    %91 = const u32 32
    %92 = icmp ult u32 %90, %91
    condbr %92, bb10(%14, %15, %16, %88), bb14
bb10(%18: u8, %19: u32, %20: u32, %21: u32):
    %93 = const i32 29
    %94 = shl u32 %19, %93
    %95 = or u32 %21, %94
    %96 = const i32 24
    %97 = bitcast i32 %96 to u32
    %98 = const u32 32
    %99 = icmp ult u32 %97, %98
    condbr %99, bb11(%18, %20, %95), bb14
bb11(%22: u8, %23: u32, %24: u32):
    %100 = const u32 16
    %101 = const i32 24
    %102 = shl u32 %100, %101
    %103 = or u32 %24, %102
    %104 = const i32 5
    %105 = bitcast i32 %104 to u32
    %106 = const u32 32
    %107 = icmp ult u32 %105, %106
    condbr %107, bb12(%22, %23, %103), bb14
bb12(%25: u8, %26: u32, %27: u32):
    %108 = const i32 5
    %109 = shl u32 %26, %108
    %110 = or u32 %27, %109
    %111 = zext u8 %25 to u32
    %112 = or u32 %110, %111
    %113 = const i64 4
    %114 = gep i8, ptr %0, %113
    store u32 %112, ptr %114
    %115 = const i8 6
    store i8 %115, ptr %0
    br bb13
bb13:
    ret
bb14:
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

fn @check_imm21(functy.2) {
bb0(%0: ptr, %1: i32):
    %4 = alloca (i32, i32), align 4
    %5 = const i32 -1048576
    %6 = icmp slt i32 %1, %5
    condbr %6, bb2(%1), bb1(%1)
bb1(%2: i32):
    %7 = const i32 1048575
    %8 = icmp sgt i32 %2, %7
    condbr %8, bb2(%2), bb3
bb2(%3: i32):
    %9 = const i64 4
    %10 = gep i8, ptr %4, %9
    store i32 %3, ptr %10
    %11 = const i8 4
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

/// VERBATIM MIR-closure emit of the production `encode_adr` + `check_reg` +
/// `check_imm21` (see ENC_ADRP_TRUST_IR notes; same slice, root encode_adr).
/// Emit reported: 4739 bytes; 3 closure member(s); validate_module = 8 error(s)
/// (const-shift spelling class); re-parse OK.
const ENC_ADR_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::encode_adr"

functy.0 = (ptr, i32, u8) -> ()

functy.1 = (ptr, u8, u8) -> ()

functy.2 = (ptr, i32) -> ()

fn @encode_adr(functy.0) {
bb0(%0: ptr, %1: i32, %2: u8):
    %24 = alloca (i32, i32), align 4
    %25 = alloca (i32, i32), align 4
    %26 = alloca (i32, i32), align 4
    %27 = alloca (i32, i32), align 4
    %28 = const u8 31
    call @func.1(%24, %2, %28)
    br bb1(%1, %2)
bb1(%3: i32, %4: u8):
    %29 = load i8, ptr %24
    %30 = const i8 6
    %31 = icmp eq i8 %29, %30
    %32 = const i64 0
    %33 = const i64 1
    %34 = select i64 %31, %32, %33
    switch %34 [ 0: bb3(%3, %4) 1: bb4 default: bb2 ]
bb2:
    unreachable
bb3(%5: i32, %6: u8):
    call @func.2(%26, %5)
    br bb5(%5, %6)
bb4:
    %35 = load i32, ptr %24
    store i32 %35, ptr %25
    %36 = const i64 4
    %37 = gep i8, ptr %24, %36
    %38 = const i64 4
    %39 = gep i8, ptr %25, %38
    %40 = load i32, ptr %37
    store i32 %40, ptr %39
    %41 = load i32, ptr %25
    store i32 %41, ptr %0
    %42 = const i64 4
    %43 = gep i8, ptr %25, %42
    %44 = const i64 4
    %45 = gep i8, ptr %0, %44
    %46 = load i32, ptr %43
    store i32 %46, ptr %45
    br bb12
bb5(%7: i32, %8: u8):
    %47 = load i8, ptr %26
    %48 = const i8 6
    %49 = icmp eq i8 %47, %48
    %50 = const i64 0
    %51 = const i64 1
    %52 = select i64 %49, %50, %51
    switch %52 [ 0: bb6(%7, %8) 1: bb7 default: bb2 ]
bb6(%9: i32, %10: u8):
    %53 = bitcast i32 %9 to u32
    %54 = const u32 2097151
    %55 = and u32 %53, %54
    %56 = const u32 3
    %57 = and u32 %55, %56
    %58 = const i32 2
    %59 = bitcast i32 %58 to u32
    %60 = const u32 32
    %61 = icmp ult u32 %59, %60
    condbr %61, bb8(%10, %55, %57), bb13
bb7:
    %62 = load i32, ptr %26
    store i32 %62, ptr %27
    %63 = const i64 4
    %64 = gep i8, ptr %26, %63
    %65 = const i64 4
    %66 = gep i8, ptr %27, %65
    %67 = load i32, ptr %64
    store i32 %67, ptr %66
    %68 = load i32, ptr %27
    store i32 %68, ptr %0
    %69 = const i64 4
    %70 = gep i8, ptr %27, %69
    %71 = const i64 4
    %72 = gep i8, ptr %0, %71
    %73 = load i32, ptr %70
    store i32 %73, ptr %72
    br bb12
bb8(%11: u8, %12: u32, %13: u32):
    %74 = const i32 2
    %75 = lshr u32 %12, %74
    %76 = const u32 0
    %77 = const i32 29
    %78 = bitcast i32 %77 to u32
    %79 = const u32 32
    %80 = icmp ult u32 %78, %79
    condbr %80, bb9(%11, %13, %75, %76), bb13
bb9(%14: u8, %15: u32, %16: u32, %17: u32):
    %81 = const i32 29
    %82 = shl u32 %15, %81
    %83 = or u32 %17, %82
    %84 = const i32 24
    %85 = bitcast i32 %84 to u32
    %86 = const u32 32
    %87 = icmp ult u32 %85, %86
    condbr %87, bb10(%14, %16, %83), bb13
bb10(%18: u8, %19: u32, %20: u32):
    %88 = const u32 16
    %89 = const i32 24
    %90 = shl u32 %88, %89
    %91 = or u32 %20, %90
    %92 = const i32 5
    %93 = bitcast i32 %92 to u32
    %94 = const u32 32
    %95 = icmp ult u32 %93, %94
    condbr %95, bb11(%18, %19, %91), bb13
bb11(%21: u8, %22: u32, %23: u32):
    %96 = const i32 5
    %97 = shl u32 %22, %96
    %98 = or u32 %23, %97
    %99 = zext u8 %21 to u32
    %100 = or u32 %98, %99
    %101 = const i64 4
    %102 = gep i8, ptr %0, %101
    store u32 %100, ptr %102
    %103 = const i8 6
    store i8 %103, ptr %0
    br bb12
bb12:
    ret
bb13:
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

fn @check_imm21(functy.2) {
bb0(%0: ptr, %1: i32):
    %4 = alloca (i32, i32), align 4
    %5 = const i32 -1048576
    %6 = icmp slt i32 %1, %5
    condbr %6, bb2(%1), bb1(%1)
bb1(%2: i32):
    %7 = const i32 1048575
    %8 = icmp sgt i32 %2, %7
    condbr %8, bb2(%2), bb3
bb2(%3: i32):
    %9 = const i64 4
    %10 = gep i8, ptr %4, %9
    store i32 %3, ptr %10
    %11 = const i8 4
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
// The LOGICAL-IMMEDIATE cluster (encode.rs:152-224)
// ═══════════════════════════════════════════════════════════════════════════
//
// Native oracles for the PRIVATE encode.rs helpers, transcribed VERBATIM from
// production (const-slice + `for` + `u32::from` forms — deliberately kept in
// the ORIGINAL spelling so the differential also checks the slice's documented
// loop rewrites). Compare against
// $HOME/trust-cg/crates/trust-cg-codegen/src/aarch64/encode.rs:152-224.

/// VERBATIM `low_mask` (encode.rs:152-158).
fn low_mask_native(bits: u32) -> u64 {
    if bits == 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    }
}

/// VERBATIM `rotate_right_within` (encode.rs:160-168).
fn rotate_right_within_native(value: u64, rot: u32, width: u32) -> u64 {
    let mask = low_mask_native(width);
    let value = value & mask;
    if rot == 0 {
        value
    } else {
        ((value >> rot) | (value << (width - rot))) & mask
    }
}

/// VERBATIM `replicate_logical_element` (encode.rs:170-178).
fn replicate_logical_element_native(pattern: u64, element_width: u32, register_width: u32) -> u64 {
    let mut out = 0;
    let mut shift = 0;
    while shift < register_width {
        out |= pattern << shift;
        shift += element_width;
    }
    out & low_mask_native(register_width)
}

/// VERBATIM `encode_logical_imm_fields` (encode.rs:180-224) — the ORIGINAL
/// const-slice + `for`-loop + `u32::from` spelling — with only the
/// diagnostic-only error payload modeled as `Err(())` (production builds an
/// `EncodeError::InvalidOperand { opcode, index, desc: format!(..) }`; the
/// `opcode`/`index` params exist solely for that diagnostic).
fn encode_logical_imm_fields_native(raw: i64, register_width: u32) -> Result<(u32, u32, u32), ()> {
    let register_mask = low_mask_native(register_width);
    let raw_mask = (raw as u64) & register_mask;
    if raw_mask == 0 || raw_mask == register_mask {
        return Err(());
    }

    let element_widths: &[u32] = if register_width == 64 {
        &[2, 4, 8, 16, 32, 64]
    } else {
        &[2, 4, 8, 16, 32]
    };

    for &element_width in element_widths {
        for ones_len in 1..element_width {
            let ones = low_mask_native(ones_len);
            for rotation in 0..element_width {
                let element = rotate_right_within_native(ones, rotation, element_width);
                let candidate =
                    replicate_logical_element_native(element, element_width, register_width);
                if candidate == raw_mask {
                    let n = u32::from(element_width == 64);
                    let immr = rotation & 0x3f;
                    let imms_prefix = (!((element_width << 1) - 1)) & 0x3f;
                    let imms = imms_prefix | (ones_len - 1);
                    return Ok((n, immr, imms));
                }
            }
        }
    }

    Err(())
}

/// The packing used by the slice's `#[no_mangle]` root: injective on outcomes
/// (any Ok has bit 63 set; Err is exactly 0).
fn pack_logimm(r: Result<(u32, u32, u32), ()>) -> u64 {
    match r {
        Ok((n, immr, imms)) => {
            (1u64 << 63) | ((n as u64) << 12) | ((immr as u64) << 6) | (imms as u64)
        }
        Err(()) => 0,
    }
}

type LowMaskFn = extern "C" fn(u32) -> u64;
type RotateFn = extern "C" fn(u64, u32, u32) -> u64;
type ReplicateFn = extern "C" fn(u64, u32, u32) -> u64;
type LogImmPackedFn = extern "C" fn(i64, u32) -> u64;

/// TRUST-SELF round 2: `low_mask` — the mask primitive under every logical-
/// immediate decision trust-cg makes — native == JIT over its full production
/// domain (bits 0..=64, incl. the `bits == 64` all-ones arm and the 0-bit
/// empty mask).
#[test]
fn trust_self2_logimm_low_mask_roundtrip() {
    let buffer = jit_module(LOGIMM_TRUST_IR, "logical-imm cluster");
    // SAFETY: machine code for `(u32) -> u64` per the module's functy.2.
    let f: LowMaskFn = unsafe { std::mem::transmute(bind(&buffer, "low_mask")) };

    let mut pass = 0usize;
    for bits in 0..=64u32 {
        let native = low_mask_native(bits);
        let jit = f(bits);
        assert_eq!(
            native, jit,
            "TRUST-SELF low_mask JIT disagrees with native at bits={bits}: \
             native={native:#x} jit={jit:#x}"
        );
        pass += 1;
    }
    assert_eq!(pass, 65, "all low_mask inputs must agree native == JIT");
    // Ground truth spot checks (ARM ARM semantics: ones(bits)).
    assert_eq!(f(64), u64::MAX, "low_mask(64) must be all-ones");
    assert_eq!(f(0), 0, "low_mask(0) must be empty");
    assert_eq!(f(7), 0x7F);

    // NEGATIVE CONTROL: a corrupted oracle that returns 0 for the 64-bit arm
    // must DISAGREE with the JIT — proving the differential discriminates.
    fn low_mask_corrupt(bits: u32) -> u64 {
        if bits == 64 { 0 } else { low_mask_native(bits) } // bug: should be MAX
    }
    assert_ne!(
        low_mask_corrupt(64),
        f(64),
        "negative control must FAIL: corrupted low_mask should disagree with the JIT"
    );

    drop(buffer);
}

/// TRUST-SELF round 2: `rotate_right_within` — the element rotation of the
/// bitmask-immediate search — native == JIT over every (width, rot) pair in
/// the production domain and a battery of bit patterns.
#[test]
fn trust_self2_logimm_rotate_right_within_roundtrip() {
    let buffer = jit_module(LOGIMM_TRUST_IR, "logical-imm cluster");
    // SAFETY: machine code for `(u64, u32, u32) -> u64` per functy.3.
    let f: RotateFn = unsafe { std::mem::transmute(bind(&buffer, "rotate_right_within")) };

    let patterns: &[u64] = &[
        0,
        1,
        0b11,
        0xFF,
        0x1FF,
        0xAAAA_AAAA_AAAA_AAAA,
        0x5555_5555_5555_5555,
        0x8000_0000_0000_0001,
        0xDEAD_BEEF_CAFE_F00D,
        u64::MAX,
    ];
    let mut pass = 0usize;
    for &width in &[2u32, 4, 8, 16, 32, 64] {
        for rot in 0..width {
            for &value in patterns {
                let native = rotate_right_within_native(value, rot, width);
                let jit = f(value, rot, width);
                assert_eq!(
                    native, jit,
                    "TRUST-SELF rotate_right_within JIT disagrees with native at \
                     value={value:#x} rot={rot} width={width}: native={native:#x} jit={jit:#x}"
                );
                pass += 1;
            }
        }
    }
    assert_eq!(pass, (2 + 4 + 8 + 16 + 32 + 64) * patterns.len());
    // Ground truth: rotating 0b0011 right by 1 within width 4 = 0b1001.
    assert_eq!(f(0b0011, 1, 4), 0b1001);

    // NEGATIVE CONTROL: corrupted oracle that ignores the rotation.
    fn rotate_corrupt(value: u64, _rot: u32, width: u32) -> u64 {
        value & low_mask_native(width) // bug: no rotation
    }
    assert_ne!(
        rotate_corrupt(0b0011, 1, 4),
        f(0b0011, 1, 4),
        "negative control must FAIL: rotation-dropping oracle should disagree with the JIT"
    );

    drop(buffer);
}

/// TRUST-SELF round 2: `replicate_logical_element` — the element replication
/// of the bitmask-immediate search — native == JIT over every
/// (element_width, register_width) production pair and a pattern battery.
#[test]
fn trust_self2_logimm_replicate_element_roundtrip() {
    let buffer = jit_module(LOGIMM_TRUST_IR, "logical-imm cluster");
    // SAFETY: machine code for `(u64, u32, u32) -> u64` per functy.4.
    let f: ReplicateFn = unsafe { std::mem::transmute(bind(&buffer, "replicate_logical_element")) };

    let patterns: &[u64] = &[0, 1, 0b10, 0b11, 0b101, 0xF, 0xFF, 0x8001, 0xFFFF_FFFF];
    let mut pass = 0usize;
    for &rw in &[32u32, 64] {
        for &ew in &[2u32, 4, 8, 16, 32, 64] {
            if ew > rw {
                continue; // production only replicates elements <= register width
            }
            for &pattern in patterns {
                let native = replicate_logical_element_native(pattern, ew, rw);
                let jit = f(pattern, ew, rw);
                assert_eq!(
                    native, jit,
                    "TRUST-SELF replicate_logical_element JIT disagrees with native at \
                     pattern={pattern:#x} ew={ew} rw={rw}: native={native:#x} jit={jit:#x}"
                );
                pass += 1;
            }
        }
    }
    assert_eq!(pass, (5 + 6) * patterns.len());
    // Ground truth: replicating 0b01 across width-2 elements = alternating bits.
    assert_eq!(f(0b01, 2, 64), 0x5555_5555_5555_5555);
    assert_eq!(f(0b01, 2, 32), 0x5555_5555);

    // NEGATIVE CONTROL: corrupted oracle that replicates only once.
    fn replicate_corrupt(pattern: u64, _ew: u32, rw: u32) -> u64 {
        pattern & low_mask_native(rw) // bug: single element, no replication
    }
    assert_ne!(
        replicate_corrupt(0b01, 2, 64),
        f(0b01, 2, 64),
        "negative control must FAIL: replication-dropping oracle should disagree with the JIT"
    );

    drop(buffer);
}

/// TRUST-SELF round 2 — the capstone of the cluster: the AArch64
/// BITMASK-IMMEDIATE encoder `encode_logical_imm_fields`, native == JIT over
/// EVERY encodable logical immediate (all 5334 64-bit + all 1302 32-bit
/// rotated-replicated-ones patterns), non-encodable probes (0, all-ones,
/// 4096 LCG values, i64 edges), CROSS-CHECKED against the production
/// `encode_instruction` AndRI path for sampled values. A wrong (N, immr,
/// imms) triple here silently changes the mask of a logical instruction in
/// every program trust-cg compiles.
///
/// The JIT root is the slice's packing adapter (bit63 | n<<12 | immr<<6 |
/// imms; Err = 0), which CALLS the in-module `encode_logical_imm_fields` ->
/// `low_mask`/`rotate_right_within`/`replicate_logical_element` as real JIT'd
/// bodies, so the whole cluster executes as machine code on every probe.
#[test]
fn trust_self2_encode_logical_imm_fields_roundtrip() {
    let buffer = jit_module(LOGIMM_TRUST_IR, "logical-imm cluster");
    // SAFETY: machine code for `(i64, u32) -> u64` per functy.0.
    let f: LogImmPackedFn =
        unsafe { std::mem::transmute(bind(&buffer, "encode_logical_imm_fields_packed")) };

    let check = |raw: i64, rw: u32, what: &str| {
        let native = pack_logimm(encode_logical_imm_fields_native(raw, rw));
        let jit = f(raw, rw);
        assert_eq!(
            native, jit,
            "TRUST-SELF encode_logical_imm_fields JIT disagrees with native on {what} \
             (raw={raw:#x} rw={rw}): native={native:#x} jit={jit:#x}"
        );
        jit
    };

    // (a) EVERY encodable logical immediate, both register widths.
    let mut encodable64: Vec<u64> = Vec::new();
    let mut total = 0usize;
    for &rw in &[64u32, 32] {
        for &ew in &[2u32, 4, 8, 16, 32, 64] {
            if ew > rw {
                continue;
            }
            for ones_len in 1..ew {
                for rotation in 0..ew {
                    let element =
                        rotate_right_within_native(low_mask_native(ones_len), rotation, ew);
                    let value = replicate_logical_element_native(element, ew, rw);
                    let jit = check(value as i64, rw, "an encodable immediate");
                    assert_ne!(
                        jit, 0,
                        "every generated rotated-replicated-ones value must be encodable \
                         (value={value:#x} rw={rw})"
                    );
                    if rw == 64 {
                        encodable64.push(value);
                    }
                    total += 1;
                }
            }
        }
    }
    assert_eq!(encodable64.len(), 5334, "the 64-bit encodable universe");
    assert_eq!(
        total,
        5334 + 1302,
        "the full encodable universe (64 + 32 bit)"
    );

    // (b) Non-encodable + edge probes.
    for &(raw, rw) in &[
        (0i64, 64u32),
        (-1, 64),
        (0, 32),
        (-1, 32),
        (0xFFFF_FFFF, 32), // all-ones under the 32-bit mask
        (i64::MIN, 64),
        (i64::MAX, 64),
        (1, 64),
        (0x0123_4567_89AB_CDEF, 64),
        (0xDEAD_BEEFu32 as i64, 32),
    ] {
        check(raw, rw, "an edge probe");
    }
    assert_eq!(f(0, 64), 0, "0 must be non-encodable (Err)");
    assert_eq!(f(-1, 64), 0, "all-ones must be non-encodable (Err)");

    // (c) 4096 deterministic LCG probes (mostly non-encodable), both widths.
    let mut x = 0x9E37_79B9_7F4A_7C15u64;
    for _ in 0..4096 {
        x = x
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        check(x as i64, 64, "an LCG probe");
        check((x as u32) as i64, 32, "an LCG probe (32)");
    }

    // (d) CROSS-CHECK against the REAL production path: every 97th encodable
    // 64-bit value (+ known landmarks) through the pub `encode_instruction`
    // AndRI 3-operand form, which calls the production
    // `encode_logical_imm_fields` internally. Field extraction per the
    // BaseLogicalImm layout: N=bit22, immr=21:16, imms=15:10.
    use trust_cg_ir::aarch64_regs::{X0, X1};
    use trust_cg_ir::inst::{AArch64Opcode, MachInst};
    use trust_cg_ir::operand::MachOperand;
    let mut crosschecked = 0usize;
    for value in encodable64.iter().copied().step_by(97).chain([
        0xFFu64,
        0x5555_5555_5555_5555,
        0xFFFF_FFFF_0000_0000,
    ]) {
        let inst = MachInst::new(
            AArch64Opcode::AndRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(value as i64),
            ],
        );
        let word = trust_cg_codegen::aarch64::encode::encode_instruction(&inst)
            .expect("production encode_instruction must encode a known-encodable AndRI");
        let (n, immr, imms) = ((word >> 22) & 1, (word >> 16) & 0x3F, (word >> 10) & 0x3F);
        let prod_packed = (1u64 << 63) | ((n as u64) << 12) | ((immr as u64) << 6) | (imms as u64);
        let jit = f(value as i64, 64);
        assert_eq!(
            prod_packed, jit,
            "JIT fields disagree with the PRODUCTION encode_instruction AndRI fields \
             for value={value:#x}: prod={prod_packed:#x} jit={jit:#x}"
        );
        crosschecked += 1;
    }
    assert!(
        crosschecked >= 55,
        "production cross-check must cover a real sample"
    );
    // ...and the production path must agree on NON-encodability too.
    let bad = MachInst::new(
        AArch64Opcode::AndRI,
        vec![
            MachOperand::PReg(X0),
            MachOperand::PReg(X1),
            MachOperand::Imm(0x0123_4567_89AB_CDEF),
        ],
    );
    assert!(
        trust_cg_codegen::aarch64::encode::encode_instruction(&bad).is_err(),
        "production must reject the non-encodable probe"
    );
    assert_eq!(f(0x0123_4567_89AB_CDEF, 64), 0, "JIT must reject it too");

    // NEGATIVE CONTROL: a corrupted oracle with an off-by-one immr must
    // DISAGREE with the JIT on a rotated pattern (0xFF00000000000003 is
    // ones_len=10 rotated by 6 within ew=64 -> immr=6).
    fn logimm_corrupt(raw: i64, rw: u32) -> u64 {
        match encode_logical_imm_fields_native(raw, rw) {
            Ok((n, immr, imms)) => pack_logimm(Ok((n, immr + 1, imms))), // bug
            Err(()) => 0,
        }
    }
    let rot_probe = 0xFF00_0000_0000_0003u64 as i64;
    assert_ne!(f(rot_probe, 64), 0, "the rotation probe must be encodable");
    assert_ne!(
        logimm_corrupt(rot_probe, 64),
        f(rot_probe, 64),
        "negative control must FAIL: off-by-one immr oracle should disagree with the JIT"
    );

    drop(buffer);
}

// ═══════════════════════════════════════════════════════════════════════════
// The WORD BUILDERS (encoding.rs) — oracle: the REAL production pub fns
// ═══════════════════════════════════════════════════════════════════════════

type Enc8Fn = extern "C" fn(u32, u32, u32, u32, u32, u32, u32, u32) -> u32;
type Enc7Fn = extern "C" fn(u32, u32, u32, u32, u32, u32, u32) -> u32;
type Enc6iFn = extern "C" fn(u32, u32, u32, i32, u32, u32) -> u32;
type Enc5Fn = extern "C" fn(u32, u32, u32, u32, u32) -> u32;
type Enc4Fn = extern "C" fn(u32, u32, u32, u32) -> u32;
type Enc2Fn = extern "C" fn(u32, u32) -> u32;

const REGS: [u32; 6] = [0, 1, 2, 15, 30, 31];

/// TRUST-SELF round 2: `encode_add_sub_shifted_reg` (ADD/SUB/ADDS/SUBS
/// shifted-register) — native (the REAL production fn) == JIT over the full
/// in-contract field product (20736 words), incl. the ARM-ARM ground truths
/// the production unit tests pin (ADD X0,X1,X2 = 0x8B020020).
#[test]
fn trust_self2_encode_add_sub_shifted_reg_roundtrip() {
    let buffer = jit_module(ENC_ADD_SUB_SHIFTED_TRUST_IR, "encode_add_sub_shifted_reg");
    // SAFETY: machine code for `(u32 x8) -> u32` per functy.0.
    let f: Enc8Fn = unsafe { std::mem::transmute(bind(&buffer, "encode_add_sub_shifted_reg")) };

    let mut pass = 0usize;
    for sf in [0u32, 1] {
        for op in [0u32, 1] {
            for s in [0u32, 1] {
                for shift in [0u32, 1, 2] {
                    for &rm in &REGS {
                        for &imm6 in &[0u32, 1, 31, 63] {
                            for &rn in &REGS {
                                let rd = (rm + rn + imm6) % 32; // deterministic spread
                                let native = prod_encoding::encode_add_sub_shifted_reg(
                                    sf, op, s, shift, rm, imm6, rn, rd,
                                );
                                let jit = f(sf, op, s, shift, rm, imm6, rn, rd);
                                assert_eq!(
                                    native, jit,
                                    "TRUST-SELF encode_add_sub_shifted_reg JIT disagrees: \
                                     sf={sf} op={op} s={s} shift={shift} rm={rm} imm6={imm6} \
                                     rn={rn} rd={rd}: native={native:#010X} jit={jit:#010X}"
                                );
                                pass += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(pass, 2 * 2 * 2 * 3 * 6 * 4 * 6);
    // ARM ARM ground truth (the production unit tests' pinned words).
    assert_eq!(f(1, 0, 0, 0, 2, 0, 1, 0), 0x8B020020, "ADD X0, X1, X2");
    assert_eq!(f(0, 1, 0, 0, 5, 0, 4, 3), 0x4B050083, "SUB W3, W4, W5");

    // NEGATIVE CONTROL: an oracle with the `op` bit misplaced (bit 29 instead
    // of 30) must disagree with the JIT on SUB.
    assert_ne!(
        0x8B020020u32 | (1 << 29),
        f(1, 1, 0, 0, 2, 0, 1, 0),
        "negative control must FAIL: misplaced-op-bit word should disagree with the JIT"
    );

    drop(buffer);
}

/// TRUST-SELF round 2: `encode_logical_shifted_reg` (AND/ORR/EOR/BIC/... reg)
/// — native (REAL production fn) == JIT over the full in-contract product.
#[test]
fn trust_self2_encode_logical_shifted_reg_roundtrip() {
    let buffer = jit_module(ENC_LOGICAL_SHIFTED_TRUST_IR, "encode_logical_shifted_reg");
    // SAFETY: machine code for `(u32 x8) -> u32` per functy.0.
    let f: Enc8Fn = unsafe { std::mem::transmute(bind(&buffer, "encode_logical_shifted_reg")) };

    let mut pass = 0usize;
    for sf in [0u32, 1] {
        for opc in 0..=3u32 {
            for shift in 0..=3u32 {
                for n in [0u32, 1] {
                    for &rm in &REGS {
                        for &imm6 in &[0u32, 33, 63] {
                            for &rn in &REGS {
                                let rd = (rm ^ rn ^ imm6) % 32;
                                let native = prod_encoding::encode_logical_shifted_reg(
                                    sf, opc, shift, n, rm, imm6, rn, rd,
                                );
                                let jit = f(sf, opc, shift, n, rm, imm6, rn, rd);
                                assert_eq!(
                                    native, jit,
                                    "TRUST-SELF encode_logical_shifted_reg JIT disagrees: \
                                     sf={sf} opc={opc} shift={shift} n={n} rm={rm} imm6={imm6} \
                                     rn={rn} rd={rd}: native={native:#010X} jit={jit:#010X}"
                                );
                                pass += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(pass, 2 * 4 * 4 * 2 * 6 * 3 * 6);
    // Ground truth: ORR X0, XZR, X2 (MOV alias): sf=1 opc=01 -> 0xAA0203E0.
    assert_eq!(f(1, 1, 0, 0, 2, 0, 31, 0), 0xAA0203E0, "ORR X0, XZR, X2");

    // NEGATIVE CONTROL: opc misencoded at bit 30 must disagree.
    assert_ne!(
        f(1, 0, 0, 0, 2, 0, 31, 0) | (1 << 30),
        f(1, 1, 0, 0, 2, 0, 31, 0),
        "negative control must FAIL: mis-shifted opc should disagree with the JIT"
    );

    drop(buffer);
}

/// TRUST-SELF round 2: `encode_add_sub_imm` (ADD/SUB immediate — the
/// stack-adjust workhorse) — native (REAL production fn) == JIT.
#[test]
fn trust_self2_encode_add_sub_imm_roundtrip() {
    let buffer = jit_module(ENC_ADD_SUB_IMM_TRUST_IR, "encode_add_sub_imm");
    // SAFETY: machine code for `(u32 x7) -> u32` per functy.0.
    let f: Enc7Fn = unsafe { std::mem::transmute(bind(&buffer, "encode_add_sub_imm")) };

    let mut pass = 0usize;
    for sf in [0u32, 1] {
        for op in [0u32, 1] {
            for s in [0u32, 1] {
                for sh in [0u32, 1] {
                    for &imm12 in &[0u32, 1, 42, 0x7FF, 0xFFF] {
                        for &rn in &REGS {
                            let rd = (rn + imm12) % 32;
                            let native =
                                prod_encoding::encode_add_sub_imm(sf, op, s, sh, imm12, rn, rd);
                            let jit = f(sf, op, s, sh, imm12, rn, rd);
                            assert_eq!(
                                native, jit,
                                "TRUST-SELF encode_add_sub_imm JIT disagrees: sf={sf} op={op} \
                                 s={s} sh={sh} imm12={imm12} rn={rn} rd={rd}: \
                                 native={native:#010X} jit={jit:#010X}"
                            );
                            pass += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(pass, 2 * 2 * 2 * 2 * 5 * 6);
    // Ground truth: ADD X0, X1, #42 = 0x9100A820.
    assert_eq!(f(1, 0, 0, 0, 42, 1, 0), 0x9100A820, "ADD X0, X1, #42");

    // NEGATIVE CONTROL: imm12 shifted to the wrong field offset must disagree.
    assert_ne!(
        f(1, 0, 0, 0, 0, 1, 0) | (42 << 12),
        f(1, 0, 0, 0, 42, 1, 0),
        "negative control must FAIL: mis-shifted imm12 should disagree with the JIT"
    );

    drop(buffer);
}

/// TRUST-SELF round 2: `encode_move_wide` (MOVN/MOVZ/MOVK — every constant
/// materialization) — native (REAL production fn) == JIT, INCLUDING the
/// #387/#447 defensive out-of-range masking of hw/imm16 (attacker-shaped
/// inputs the encoder must mask rather than trap on).
#[test]
fn trust_self2_encode_move_wide_roundtrip() {
    let buffer = jit_module(ENC_MOVE_WIDE_TRUST_IR, "encode_move_wide");
    // SAFETY: machine code for `(u32 x5) -> u32` per functy.0.
    let f: Enc5Fn = unsafe { std::mem::transmute(bind(&buffer, "encode_move_wide")) };

    let mut pass = 0usize;
    for sf in [0u32, 1] {
        for opc in [0u32, 2, 3] {
            // hw INTENTIONALLY sweeps OUT of range (4..): the defensive
            // masking path (#447) is production semantics we must match.
            for &hw in &[0u32, 1, 2, 3, 4, 5, 6, 7, 8, 11, 0x4000_0003] {
                for &imm16 in &[0u32, 1, 0x8000, 0xBEEF, 0xFFFF, 0x1_0000, 0xDEAD_0000] {
                    for &rd in &REGS {
                        let native = prod_encoding::encode_move_wide(sf, opc, hw, imm16, rd);
                        let jit = f(sf, opc, hw, imm16, rd);
                        assert_eq!(
                            native, jit,
                            "TRUST-SELF encode_move_wide JIT disagrees: sf={sf} opc={opc} \
                             hw={hw} imm16={imm16:#x} rd={rd}: native={native:#010X} \
                             jit={jit:#010X}"
                        );
                        pass += 1;
                    }
                }
            }
        }
    }
    assert_eq!(pass, 2 * 3 * 11 * 7 * 6);
    // Ground truth: MOVZ X0, #0xBEEF = sf=1 opc=10 -> 0xD297DDE0.
    assert_eq!(f(1, 2, 0, 0xBEEF, 0), 0xD297DDE0, "MOVZ X0, #0xBEEF");
    // The defensive mask: hw=5 must encode exactly like hw=1 (5 & 0b11).
    assert_eq!(f(1, 2, 5, 7, 3), f(1, 2, 1, 7, 3), "hw defensive masking");

    // NEGATIVE CONTROL: an oracle without the defensive hw mask (raw shift)
    // must disagree with the JIT for hw=8. (NOTE, found while arming this
    // control: hw in 4..=7 unmasked spills ONLY into bit 23, which the
    // 0b100101<<23 move-wide opcode field already sets, so an unmasked-hw
    // encoder is indistinguishable there by construction; hw=8 spills into
    // bit 24, which is clear, and genuinely discriminates.)
    fn move_wide_corrupt(sf: u32, opc: u32, hw: u32, imm16: u32, rd: u32) -> u32 {
        // bug: no `hw & 0b11` mask
        (sf << 31) | (opc << 29) | (0b100101 << 23) | (hw << 21) | ((imm16 & 0xFFFF) << 5) | rd
    }
    assert_ne!(
        move_wide_corrupt(1, 2, 8, 7, 3),
        f(1, 2, 8, 7, 3),
        "negative control must FAIL: unmasked-hw oracle should disagree with the JIT"
    );
    assert_eq!(f(1, 2, 8, 7, 3), f(1, 2, 0, 7, 3), "hw=8 must mask to 0");

    drop(buffer);
}

/// TRUST-SELF round 2: `encode_cond_branch` (B.cond — every compiled `if`) —
/// native (REAL production fn) == JIT over all 16 condition codes and the
/// imm19 edges.
#[test]
fn trust_self2_encode_cond_branch_roundtrip() {
    let buffer = jit_module(ENC_COND_BRANCH_TRUST_IR, "encode_cond_branch");
    // SAFETY: machine code for `(u32, u32) -> u32` per functy.0.
    let f: Enc2Fn = unsafe { std::mem::transmute(bind(&buffer, "encode_cond_branch")) };

    let mut pass = 0usize;
    for &imm19 in &[0u32, 1, 2, 0x3FF, 0x4_0000, 0x7FFFF] {
        for cond in 0..=15u32 {
            let native = prod_encoding::encode_cond_branch(imm19, cond);
            let jit = f(imm19, cond);
            assert_eq!(
                native, jit,
                "TRUST-SELF encode_cond_branch JIT disagrees: imm19={imm19:#x} cond={cond}: \
                 native={native:#010X} jit={jit:#010X}"
            );
            pass += 1;
        }
    }
    assert_eq!(pass, 6 * 16);
    // Ground truth: B.NE +16 bytes (imm19=4, cond=NE=1) = 0x54000081.
    assert_eq!(f(4, 1), 0x54000081, "B.NE #+16");

    // NEGATIVE CONTROL: cond written into bit 4 (the o1 field) must disagree.
    assert_ne!(
        (0b01010100u32 << 24) | (4 << 5) | (1 << 4),
        f(4, 1),
        "negative control must FAIL: cond-in-o1 word should disagree with the JIT"
    );

    drop(buffer);
}

/// TRUST-SELF round 2: `encode_cmp_branch` (CBZ/CBNZ — every compiled
/// null/zero check branch) — native (REAL production fn) == JIT.
#[test]
fn trust_self2_encode_cmp_branch_roundtrip() {
    let buffer = jit_module(ENC_CMP_BRANCH_TRUST_IR, "encode_cmp_branch");
    // SAFETY: machine code for `(u32 x4) -> u32` per functy.0.
    let f: Enc4Fn = unsafe { std::mem::transmute(bind(&buffer, "encode_cmp_branch")) };

    let mut pass = 0usize;
    for sf in [0u32, 1] {
        for op in [0u32, 1] {
            for &imm19 in &[0u32, 1, 4, 0x3FFF, 0x7FFFF] {
                for &rt in &REGS {
                    let native = prod_encoding::encode_cmp_branch(sf, op, imm19, rt);
                    let jit = f(sf, op, imm19, rt);
                    assert_eq!(
                        native, jit,
                        "TRUST-SELF encode_cmp_branch JIT disagrees: sf={sf} op={op} \
                         imm19={imm19:#x} rt={rt}: native={native:#010X} jit={jit:#010X}"
                    );
                    pass += 1;
                }
            }
        }
    }
    assert_eq!(pass, 2 * 2 * 5 * 6);
    // Ground truth: CBZ X3, #+16 (sf=1 op=0 imm19=4 rt=3) = 0xB4000083.
    assert_eq!(f(1, 0, 4, 3), 0xB4000083, "CBZ X3, #+16");

    // NEGATIVE CONTROL: op misplaced at bit 25 must disagree with CBNZ.
    assert_ne!(
        f(1, 0, 4, 3) | (1 << 25),
        f(1, 1, 4, 3),
        "negative control must FAIL: misplaced-op word should disagree with the JIT"
    );

    drop(buffer);
}

/// TRUST-SELF round 2: `encode_load_store_unscaled` (LDUR/STUR — the
/// signed-offset memory access) — native (REAL production fn) == JIT over the
/// FULL signed imm9 domain including the negative-offset masking into the
/// 9-bit field (the sign-handling is the interesting bit surface here).
#[test]
fn trust_self2_encode_load_store_unscaled_roundtrip() {
    let buffer = jit_module(ENC_LDST_UNSCALED_TRUST_IR, "encode_load_store_unscaled");
    // SAFETY: machine code for `(u32, u32, u32, i32, u32, u32) -> u32` per functy.0.
    let f: Enc6iFn = unsafe { std::mem::transmute(bind(&buffer, "encode_load_store_unscaled")) };

    let mut pass = 0usize;
    for size in 0..=3u32 {
        for v in [0u32, 1] {
            for opc in 0..=3u32 {
                for imm9 in -256..=255i32 {
                    let (rn, rt) = ((imm9.unsigned_abs()) % 32, (size + opc) % 32);
                    let native =
                        prod_encoding::encode_load_store_unscaled(size, v, opc, imm9, rn, rt);
                    let jit = f(size, v, opc, imm9, rn, rt);
                    assert_eq!(
                        native, jit,
                        "TRUST-SELF encode_load_store_unscaled JIT disagrees: size={size} \
                         v={v} opc={opc} imm9={imm9} rn={rn} rt={rt}: native={native:#010X} \
                         jit={jit:#010X}"
                    );
                    pass += 1;
                }
            }
        }
    }
    assert_eq!(pass, 4 * 2 * 4 * 512);
    // Ground truth: LDUR X0, [X29, #-8] (size=3 v=0 opc=1 imm9=-8 rn=29) =
    // size<<30 | 0b111<<27 | 1<<22 | (0x1F8)<<12 | 29<<5 | 0 = 0xF85F83A0.
    assert_eq!(f(3, 0, 1, -8, 29, 0), 0xF85F83A0, "LDUR X0, [X29, #-8]");

    // NEGATIVE CONTROL: an oracle that forgets the 9-bit mask on negative
    // offsets (sign bits smear over opc/size) must disagree with the JIT.
    fn ldst_corrupt(size: u32, v: u32, opc: u32, imm9: i32, rn: u32, rt: u32) -> u32 {
        (size << 30)
            | (0b111 << 27)
            | (v << 26)
            | (opc << 22)
            | ((imm9 as u32) << 12) // bug: no & 0x1FF
            | (rn << 5)
            | rt
    }
    assert_ne!(
        ldst_corrupt(3, 0, 1, -8, 29, 0),
        f(3, 0, 1, -8, 29, 0),
        "negative control must FAIL: unmasked-imm9 oracle should disagree with the JIT"
    );

    drop(buffer);
}

// ═══════════════════════════════════════════════════════════════════════════
// The PC-RELATIVE cluster (encoding_mem.rs) — Result<u32, EncodeError> returns
// ═══════════════════════════════════════════════════════════════════════════

/// Canonical view of a JIT/native `Result<u32, EncodeError>` outcome. The JIT
/// side is decoded from the out-buffer bytes at the offsets/tags the EMITTED
/// IR itself bakes in (tag i8 @0: 0=RegisterOutOfRange{reg@1,max@2},
/// 4=Imm21OutOfRange{value:i32@4}, 6=Ok(u32@4) — Ok occupies the niche after
/// EncodeError's 6 variants); the native side is canonicalized by `match`, so
/// no layout assumption is made about the host-compiled enum.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum PcRelOut {
    Ok(u32),
    ErrReg { reg: u8, max: u8 },
    ErrImm21 { value: i32 },
    Other(u8),
}

#[repr(C, align(8))]
struct RawOut {
    bytes: [u8; 8],
}

const OUT_POISON: u8 = 0xDE;

fn decode_jit_pcrel(out: &RawOut) -> PcRelOut {
    let b = &out.bytes;
    match b[0] {
        6 => PcRelOut::Ok(u32::from_le_bytes([b[4], b[5], b[6], b[7]])),
        0 => PcRelOut::ErrReg {
            reg: b[1],
            max: b[2],
        },
        4 => PcRelOut::ErrImm21 {
            value: i32::from_le_bytes([b[4], b[5], b[6], b[7]]),
        },
        t => PcRelOut::Other(t),
    }
}

fn canon_native_pcrel(r: Result<u32, prod_encoding_mem::EncodeError>) -> PcRelOut {
    match r {
        Ok(w) => PcRelOut::Ok(w),
        Err(prod_encoding_mem::EncodeError::RegisterOutOfRange { reg, max }) => {
            PcRelOut::ErrReg { reg, max }
        }
        Err(prod_encoding_mem::EncodeError::Imm21OutOfRange { value }) => {
            PcRelOut::ErrImm21 { value }
        }
        Err(other) => panic!("unexpected native error variant: {other:?}"),
    }
}

type PcRelFn = extern "C" fn(*mut RawOut, i32, u8);
type CheckRegFn = extern "C" fn(*mut RawOut, u8, u8);
type CheckImm21Fn = extern "C" fn(*mut RawOut, i32);

const IMM21_CASES: [i32; 13] = [
    i32::MIN,
    -1_048_577,
    -1_048_576,
    -524_288,
    -1,
    0,
    1,
    4,
    0x15_5555,
    524_287,
    1_048_575,
    1_048_576,
    i32::MAX,
];
const RD_CASES: [u8; 9] = [0, 1, 15, 29, 30, 31, 32, 63, 255];

/// Drive one PC-relative encoder module (`encode_adrp` or `encode_adr`)
/// through the full imm21 x rd edge product against the REAL production fn,
/// exercising Ok, ErrReg, and ErrImm21 paths (which transit the in-module
/// JIT'd `check_reg` + `check_imm21` bodies), then drive `check_reg` /
/// `check_imm21` DIRECTLY as standalone JIT symbols.
fn run_pcrel_roundtrip(
    module_text: &str,
    root_sym: &str,
    native: fn(i32, u8) -> Result<u32, prod_encoding_mem::EncodeError>,
) {
    let buffer = jit_module(module_text, root_sym);
    // SAFETY: machine code for `(ptr, i32, u8) -> ()` per functy.0 (Result
    // returned through the out-pointer).
    let f: PcRelFn = unsafe { std::mem::transmute(bind(&buffer, root_sym)) };

    let mut pass = 0usize;
    let mut ok_seen = 0usize;
    let mut err_reg_seen = 0usize;
    let mut err_imm_seen = 0usize;
    for &imm21 in &IMM21_CASES {
        for &rd in &RD_CASES {
            let native_out = canon_native_pcrel(native(imm21, rd));
            let mut out = RawOut {
                bytes: [OUT_POISON; 8],
            };
            f(&mut out as *mut RawOut, imm21, rd);
            assert_ne!(
                out.bytes[0], OUT_POISON,
                "JIT must write the Result tag (poison survived) for imm21={imm21} rd={rd}"
            );
            let jit_out = decode_jit_pcrel(&out);
            assert_eq!(
                native_out, jit_out,
                "TRUST-SELF {root_sym} JIT disagrees with the production fn at \
                 imm21={imm21} rd={rd}: native={native_out:?} jit={jit_out:?}"
            );
            match jit_out {
                PcRelOut::Ok(_) => ok_seen += 1,
                PcRelOut::ErrReg { .. } => err_reg_seen += 1,
                PcRelOut::ErrImm21 { .. } => err_imm_seen += 1,
                PcRelOut::Other(t) => panic!("undecodable JIT tag {t}"),
            }
            pass += 1;
        }
    }
    assert_eq!(pass, IMM21_CASES.len() * RD_CASES.len());
    assert!(
        ok_seen > 0 && err_reg_seen > 0 && err_imm_seen > 0,
        "the sweep must exercise Ok ({ok_seen}), ErrReg ({err_reg_seen}) and \
         ErrImm21 ({err_imm_seen}) paths"
    );

    // Precedence differential: BOTH out of range -> production checks the
    // register FIRST (check_reg before check_imm21); the JIT must agree.
    let mut out = RawOut {
        bytes: [OUT_POISON; 8],
    };
    f(&mut out as *mut RawOut, i32::MAX, 200);
    assert_eq!(
        decode_jit_pcrel(&out),
        PcRelOut::ErrReg { reg: 200, max: 31 },
        "check_reg must take precedence over check_imm21 in the JIT, as in production"
    );

    // Direct standalone differentials for the in-module validators.
    // SAFETY: machine code for `(ptr, u8, u8) -> ()` / `(ptr, i32) -> ()` per
    // functy.1 / functy.2 (Result<(), EncodeError> through the out-pointer).
    let fr: CheckRegFn = unsafe { std::mem::transmute(bind(&buffer, "check_reg")) };
    let fi: CheckImm21Fn = unsafe { std::mem::transmute(bind(&buffer, "check_imm21")) };
    for reg in 0..=255u8 {
        for &max in &[0u8, 30, 31] {
            let mut out = RawOut {
                bytes: [OUT_POISON; 8],
            };
            fr(&mut out as *mut RawOut, reg, max);
            // Oracle: VERBATIM check_reg semantics (encoding_mem.rs:110-116;
            // private fn, transcribed): reg > max -> RegisterOutOfRange.
            let native_out = if reg > max {
                PcRelOut::ErrReg { reg, max }
            } else {
                PcRelOut::Ok(0) // unit Ok: tag-only
            };
            let jit_out = match out.bytes[0] {
                6 => PcRelOut::Ok(0),
                0 => PcRelOut::ErrReg {
                    reg: out.bytes[1],
                    max: out.bytes[2],
                },
                t => PcRelOut::Other(t),
            };
            assert_eq!(
                native_out, jit_out,
                "TRUST-SELF check_reg JIT disagrees at reg={reg} max={max}"
            );
        }
    }
    for &value in &IMM21_CASES {
        let mut out = RawOut {
            bytes: [OUT_POISON; 8],
        };
        fi(&mut out as *mut RawOut, value);
        // Oracle: VERBATIM check_imm21 semantics (encoding_mem.rs:142-148).
        let native_out = if !(-1_048_576..=1_048_575).contains(&value) {
            PcRelOut::ErrImm21 { value }
        } else {
            PcRelOut::Ok(0)
        };
        let jit_out = match out.bytes[0] {
            6 => PcRelOut::Ok(0),
            4 => PcRelOut::ErrImm21 {
                value: i32::from_le_bytes([out.bytes[4], out.bytes[5], out.bytes[6], out.bytes[7]]),
            },
            t => PcRelOut::Other(t),
        };
        assert_eq!(
            native_out, jit_out,
            "TRUST-SELF check_imm21 JIT disagrees at value={value}"
        );
    }

    // NEGATIVE CONTROL: an oracle that accepts rd=32 (off-by-one contract)
    // must DISAGREE with the JIT, which returns ErrReg.
    let mut out = RawOut {
        bytes: [OUT_POISON; 8],
    };
    f(&mut out as *mut RawOut, 0, 32);
    let corrupt_expectation = PcRelOut::Ok(match native(0, 0) {
        Ok(w) => w | 32, // what a bounds-forgetting encoder would produce
        Err(_) => unreachable!("imm21=0 rd=0 must encode"),
    });
    assert_ne!(
        corrupt_expectation,
        decode_jit_pcrel(&out),
        "negative control must FAIL: an rd=32-accepting oracle should disagree with the JIT"
    );
    assert_eq!(
        decode_jit_pcrel(&out),
        PcRelOut::ErrReg { reg: 32, max: 31 },
        "the JIT must reject rd=32 exactly as production does"
    );

    drop(buffer);
}

/// TRUST-SELF round 2: `encode_adrp` (the page-address encoder behind every
/// global/const-pool access trust-cg emits) + its `check_reg`/`check_imm21`
/// validators — native (REAL production fns) == JIT across Ok and both error
/// paths, plus the immlo/immhi bit-split ground truth.
#[test]
fn trust_self2_encode_adrp_roundtrip() {
    run_pcrel_roundtrip(
        ENC_ADRP_TRUST_IR,
        "encode_adrp",
        prod_encoding_mem::encode_adrp,
    );

    // Ground truth for the immlo/immhi split (independent of both compilers):
    // ADRP X0, #page+1: imm21=1 -> immlo=1 immhi=0 ->
    // 1<<31 | 1<<29 | 0b10000<<24 = 0xB0000000.
    let buffer = jit_module(ENC_ADRP_TRUST_IR, "encode_adrp");
    let f: PcRelFn = unsafe { std::mem::transmute(bind(&buffer, "encode_adrp")) };
    let mut out = RawOut {
        bytes: [OUT_POISON; 8],
    };
    f(&mut out as *mut RawOut, 1, 0);
    assert_eq!(
        decode_jit_pcrel(&out),
        PcRelOut::Ok(0xB000_0000),
        "ADRP X0, imm21=1"
    );
    // imm21=-1 -> bits=0x1FFFFF -> immlo=3, immhi=0x7FFFF.
    let mut out = RawOut {
        bytes: [OUT_POISON; 8],
    };
    f(&mut out as *mut RawOut, -1, 3);
    assert_eq!(
        decode_jit_pcrel(&out),
        PcRelOut::Ok(0x8000_0000 | (3 << 29) | (0b10000 << 24) | (0x7FFFF << 5) | 3),
        "ADRP X3, imm21=-1 (sign-masked split)"
    );
    drop(buffer);
}

/// TRUST-SELF round 2: `encode_adr` (op=0 sibling: byte- rather than
/// page-granular PC-relative address) — same full differential as ADRP.
#[test]
fn trust_self2_encode_adr_roundtrip() {
    run_pcrel_roundtrip(
        ENC_ADR_TRUST_IR,
        "encode_adr",
        prod_encoding_mem::encode_adr,
    );

    // Ground truth: ADR bit 31 must be CLEAR (the only difference from ADRP).
    let buffer = jit_module(ENC_ADR_TRUST_IR, "encode_adr");
    let f: PcRelFn = unsafe { std::mem::transmute(bind(&buffer, "encode_adr")) };
    let mut out = RawOut {
        bytes: [OUT_POISON; 8],
    };
    f(&mut out as *mut RawOut, 1, 0);
    assert_eq!(
        decode_jit_pcrel(&out),
        PcRelOut::Ok(0x3000_0000),
        "ADR X0, imm21=1"
    );
    drop(buffer);
}
