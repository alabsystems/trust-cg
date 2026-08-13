// trust-cg-ir - WebAssembly opcode definitions
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: WebAssembly Core Specification, Release 2.0 (Draft) — the binary
//            opcode table (§5.4 Instructions).

//! WebAssembly instruction opcode enum (the emittable universe of the trust-cg
//! wasm backend).
//!
//! Mirrors [`crate::RiscVOpcode`] / `AArch64Opcode` / `X86Opcode` so the coverage
//! gate ([`trust_cg_verify::coverage_gate`]) can enumerate and classify the wasm
//! backend the SAME way it does the register backends. Unlike the register ISAs,
//! wasm is a STACK MACHINE: an instruction consumes its operands from the value
//! stack rather than from named registers. The opcode itself, however, fixes the
//! VALUE FUNCTION exactly — `i32.add` (0x6a) always computes `(a+b) mod 2^32` of
//! the top two stack operands — so the opcode is the unit the gate audits, and a
//! WRONG opcode byte (e.g. `i32.sub` 0x6b for an intended add) genuinely refutes
//! the lowering. The stack-operand wiring is modeled in the verifier
//! (`wasm_function_verifier::reconstruct_alu_obligation`).
//!
//! The backend (`trust-cg-codegen/src/wasm/{lower,encode}.rs`) emits raw `u8`
//! opcode bytes via the `op::` constants; this typed enum is the verification
//! mirror of that table. Each variant carries its canonical binary opcode byte
//! ([`WasmOpcode::opcode_byte`]) so the verifier can DECODE the real emitted byte
//! through `wasm_semantics::decode_int_binop` (and the comparison / FP decoders)
//! and reconstruct the machine side from it. Multi-byte (0xfc-prefixed) ops carry
//! the prefix byte; their sub-index is recorded in the doc only (those ops are
//! not in the value-equivalence reconstruction set — see the classifier).
//!
//! GROUPING (load-bearing for the wildcard-free classifier `classify_wasm`):
//!
//!   * SCALAR VALUE OPS — integer ALU/compare, FP arith/compare/unary, width
//!     casts. These have a per-instruction trust-ir<->wasm value-equivalence and
//!     are RECONSTRUCTED by the wasm function verifier (the value-equivalence
//!     denominator).
//!   * STRUCTURAL — control flow (block/loop/if/br/br_table/return), memory
//!     (load/store), locals/globals (local.get/set/tee, global.get/set),
//!     calls (call/call_indirect), and the stack housekeeping (drop, const, end,
//!     nop, unreachable). These carry no per-instruction value-equivalence (their
//!     correctness is the relooper / memory-model / call-ABI argument), so the
//!     classifier puts them OUT of the value-equivalence denominator.
//!   * SIMD / v128 — SPLIT: the lane-wise VALUE ops (i32x4.add/mul, f32x4.add/mul)
//!     ARE now reconstructed lane-wise by the verifier
//!     (wasm_semantics::decode_simd_lane_op + encode_i32x4_add/mul /
//!     encode_f32x4_add_lane/mul_lane) and discharge Valid, so they are IN the
//!     value-equivalence denominator. The STRUCTURAL forms (v128.load/store/const)
//!     mirror the scalar load/store/const family and carry no per-instruction
//!     value equivalence, so they stay OUT of the denominator.

// ---------------------------------------------------------------------------
// WasmOpcode
// ---------------------------------------------------------------------------

/// WebAssembly instruction opcodes the trust-cg wasm backend can emit.
///
/// Enumerates the EMITTABLE universe (the value ops the lowerer selects, the
/// structural forms the relooper / memory / call paths emit, plus the v128/SIMD
/// surface that is reserved-but-deferred). Each variant maps to a canonical
/// binary opcode byte via [`Self::opcode_byte`]; the value-op subset is decoded
/// back through `wasm_semantics` by the verifier for operand reconstruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum WasmOpcode {
    // =====================================================================
    // Integer ALU (i32 / i64) — RECONSTRUCTABLE value ops
    // =====================================================================
    /// `i32.add` (0x6a) / `i64.add` (0x7c) — `(a + b) mod 2^N`.
    I32Add,
    I64Add,
    /// `i32.sub` (0x6b) / `i64.sub` (0x7d).
    I32Sub,
    I64Sub,
    /// `i32.mul` (0x6c) / `i64.mul` (0x7e).
    I32Mul,
    I64Mul,
    /// `i32.div_s` (0x6d) / `i64.div_s` (0x7f) — traps on 0 and INT_MIN/-1.
    I32DivS,
    I64DivS,
    /// `i32.div_u` (0x6e) / `i64.div_u` (0x80) — traps on 0.
    I32DivU,
    I64DivU,
    /// `i32.rem_s` (0x6f) / `i64.rem_s` (0x81) — traps on 0.
    I32RemS,
    I64RemS,
    /// `i32.rem_u` (0x70) / `i64.rem_u` (0x82) — traps on 0.
    I32RemU,
    I64RemU,
    /// `i32.and` (0x71) / `i64.and` (0x83).
    I32And,
    I64And,
    /// `i32.or` (0x72) / `i64.or` (0x84).
    I32Or,
    I64Or,
    /// `i32.xor` (0x73) / `i64.xor` (0x85).
    I32Xor,
    I64Xor,
    /// `i32.shl` (0x74) / `i64.shl` (0x86) — amount masked mod N.
    I32Shl,
    I64Shl,
    /// `i32.shr_s` (0x75) / `i64.shr_s` (0x87) — arithmetic right, masked mod N.
    I32ShrS,
    I64ShrS,
    /// `i32.shr_u` (0x76) / `i64.shr_u` (0x88) — logical right, masked mod N.
    I32ShrU,
    I64ShrU,
    /// `i32.popcnt` (0x69) / `i64.popcnt` (0x7b) — population count.
    I32Popcnt,
    I64Popcnt,

    // =====================================================================
    // Integer comparisons (operand i32 / i64; result i32 0/1) — RECONSTRUCTABLE
    // =====================================================================
    /// `i32.eq` (0x46) / `i64.eq` (0x51).
    I32Eq,
    I64Eq,
    /// `i32.ne` (0x47) / `i64.ne` (0x52).
    I32Ne,
    I64Ne,
    /// `i32.lt_s` (0x48) / `i64.lt_s` (0x53).
    I32LtS,
    I64LtS,
    /// `i32.lt_u` (0x49) / `i64.lt_u` (0x54).
    I32LtU,
    I64LtU,
    /// `i32.gt_s` (0x4a) / `i64.gt_s` (0x55).
    I32GtS,
    I64GtS,
    /// `i32.gt_u` (0x4b) / `i64.gt_u` (0x56).
    I32GtU,
    I64GtU,
    /// `i32.le_s` (0x4c) / `i64.le_s` (0x57).
    I32LeS,
    I64LeS,
    /// `i32.le_u` (0x4d) / `i64.le_u` (0x58).
    I32LeU,
    I64LeU,
    /// `i32.ge_s` (0x4e) / `i64.ge_s` (0x59).
    I32GeS,
    I64GeS,
    /// `i32.ge_u` (0x4f) / `i64.ge_u` (0x5a).
    I32GeU,
    I64GeU,

    // =====================================================================
    // Floating-point arithmetic (f32 / f64) — RECONSTRUCTABLE value ops
    // =====================================================================
    /// `f32.add` (0x92) / `f64.add` (0xa0).
    F32Add,
    F64Add,
    /// `f32.sub` (0x93) / `f64.sub` (0xa1).
    F32Sub,
    F64Sub,
    /// `f32.mul` (0x94) / `f64.mul` (0xa2).
    F32Mul,
    F64Mul,
    /// `f32.div` (0x95) / `f64.div` (0xa3).
    F32Div,
    F64Div,
    /// `f32.min` (0x96) / `f64.min` (0xa4) — IEEE-ish minimum (NaN-propagating).
    F32Min,
    F64Min,
    /// `f32.max` (0x97) / `f64.max` (0xa5).
    F32Max,
    F64Max,

    // =====================================================================
    // Floating-point comparisons (operand f32 / f64; result i32 0/1) — RECON
    // =====================================================================
    /// `f32.eq` (0x5b) / `f64.eq` (0x61).
    F32Eq,
    F64Eq,
    /// `f32.ne` (0x5c) / `f64.ne` (0x62).
    F32Ne,
    F64Ne,
    /// `f32.lt` (0x5d) / `f64.lt` (0x63).
    F32Lt,
    F64Lt,
    /// `f32.gt` (0x5e) / `f64.gt` (0x64).
    F32Gt,
    F64Gt,
    /// `f32.le` (0x5f) / `f64.le` (0x65).
    F32Le,
    F64Le,
    /// `f32.ge` (0x60) / `f64.ge` (0x66).
    F32Ge,
    F64Ge,

    // =====================================================================
    // Floating-point unary value ops (f32 / f64) — RECONSTRUCTABLE
    // =====================================================================
    /// `f32.abs` (0x8b) / `f64.abs` (0x99).
    F32Abs,
    F64Abs,
    /// `f32.neg` (0x8c) / `f64.neg` (0x9a).
    F32Neg,
    F64Neg,
    /// `f32.sqrt` (0x91) / `f64.sqrt` (0x9f).
    F32Sqrt,
    F64Sqrt,
    /// `f32.ceil` (0x8d) / `f64.ceil` (0x9b).
    F32Ceil,
    F64Ceil,
    /// `f32.floor` (0x8e) / `f64.floor` (0x9c).
    F32Floor,
    F64Floor,
    /// `f32.trunc` (0x8f) / `f64.trunc` (0x9d).
    F32Trunc,
    F64Trunc,

    // =====================================================================
    // Width / format casts — RECONSTRUCTABLE value ops (integer casts) +
    // RECONSTRUCTABLE FP-format casts; the float<->int conversions are NOT in
    // the integer/FP value-equivalence set (see classifier).
    // =====================================================================
    /// `i32.wrap_i64` (0xa7) — low 32 bits.
    I32WrapI64,
    /// `i64.extend_i32_s` (0xac) — sign-extend i32 -> i64.
    I64ExtendI32S,
    /// `i64.extend_i32_u` (0xad) — zero-extend i32 -> i64.
    I64ExtendI32U,
    /// `f32.demote_f64` (0xb6) — narrow f64 -> f32 (rounds).
    F32DemoteF64,
    /// `f64.promote_f32` (0xbb) — widen f32 -> f64 (exact).
    F64PromoteF32,

    // ---- Float <-> int conversions (NOT scalar-value-equivalence; structural) ----
    /// `f32.convert_i32_s` (0xb2) / `_u` (0xb3) / `i64` (0xb4 / 0xb5).
    F32ConvertI32S,
    F32ConvertI32U,
    F32ConvertI64S,
    F32ConvertI64U,
    /// `f64.convert_i32_s` (0xb7) / `_u` (0xb8) / `i64` (0xb9 / 0xba).
    F64ConvertI32S,
    F64ConvertI32U,
    F64ConvertI64S,
    F64ConvertI64U,
    /// Reinterpret (bitcast): `i32.reinterpret_f32` (0xbc) etc.
    I32ReinterpretF32,
    I64ReinterpretF64,
    F32ReinterpretI32,
    F64ReinterpretI64,
    /// Saturating float->int (0xfc prefix + index): `i32.trunc_sat_f32_s` etc.
    /// Carries the 0xfc prefix byte; the sub-index distinguishes the 8 forms.
    I32TruncSatF32S,
    I32TruncSatF32U,
    I32TruncSatF64S,
    I32TruncSatF64U,
    I64TruncSatF32S,
    I64TruncSatF32U,
    I64TruncSatF64S,
    I64TruncSatF64U,

    // =====================================================================
    // Constants — STRUCTURAL (value materialization, not a binary value op)
    // =====================================================================
    /// `i32.const` (0x41) / `i64.const` (0x42) — push an immediate.
    I32Const,
    I64Const,

    // =====================================================================
    // Locals / globals — STRUCTURAL
    // =====================================================================
    /// `local.get` (0x20).
    LocalGet,
    /// `local.set` (0x21).
    LocalSet,
    /// `local.tee` (0x22).
    LocalTee,
    /// `global.get` (0x23).
    GlobalGet,
    /// `global.set` (0x24).
    GlobalSet,

    // =====================================================================
    // Linear memory load / store — STRUCTURAL (memory-model family)
    // =====================================================================
    /// `i32.load` (0x28).
    I32Load,
    /// `i64.load` (0x29).
    I64Load,
    /// `i32.store` (0x36).
    I32Store,
    /// `i64.store` (0x37).
    I64Store,

    // =====================================================================
    // Structured control flow — STRUCTURAL (relooper / CFG family)
    // =====================================================================
    /// `unreachable` (0x00) — trap.
    Unreachable,
    /// `nop` (0x01).
    Nop,
    /// `block` (0x02).
    Block,
    /// `loop` (0x03).
    Loop,
    /// `if` (0x04).
    If,
    /// `else` (0x05).
    Else,
    /// `end` (0x0b).
    End,
    /// `br` (0x0c).
    Br,
    /// `br_if` (0x0d).
    BrIf,
    /// `br_table` (0x0e).
    BrTable,
    /// `return` (0x0f).
    Return,
    /// `drop` (0x1a).
    Drop,

    // =====================================================================
    // Calls — STRUCTURAL (call-ABI family)
    // =====================================================================
    /// `call` (0x10).
    Call,
    /// `call_indirect` (0x11).
    CallIndirect,

    // =====================================================================
    // SIMD / v128 — MIXED. The lane-wise VALUE ops (i32x4.add/mul, f32x4.add/mul)
    // are now reconstructed lane-wise and discharge Valid (see is_simd doc below);
    // the STRUCTURAL forms (v128.load/store/const) carry no value equivalence.
    // All carry the 0xfd SIMD prefix byte; the sub-index distinguishes forms.
    // =====================================================================
    /// `v128.load` (0xfd 0x00) — representative SIMD load.
    V128Load,
    /// `v128.store` (0xfd 0x0b) — representative SIMD store.
    V128Store,
    /// `v128.const` (0xfd 0x0c).
    V128Const,
    /// `i32x4.add` (0xfd 0xae) — representative lane-wise integer SIMD add.
    I32x4Add,
    /// `i32x4.mul` (0xfd 0xb5) — representative lane-wise integer SIMD mul.
    I32x4Mul,
    /// `f32x4.add` (0xfd 0xe4) — representative lane-wise FP SIMD add.
    F32x4Add,
    /// `f32x4.mul` (0xfd 0xe6) — representative lane-wise FP SIMD mul.
    F32x4Mul,
}

impl WasmOpcode {
    /// The canonical PRIMARY binary opcode byte for this instruction.
    ///
    /// For single-byte instructions this is the whole encoding. For the
    /// 0xfc-prefixed saturating-conversion ops and the 0xfd-prefixed SIMD ops,
    /// this returns the PREFIX byte (0xfc / 0xfd); their sub-index is documented
    /// on the variant and is not part of the value-equivalence reconstruction
    /// set. This is the byte the verifier feeds to `wasm_semantics`' decoders to
    /// rebuild the machine side from the REAL emitted opcode.
    pub fn opcode_byte(self) -> u8 {
        use WasmOpcode::*;
        match self {
            // Integer ALU
            I32Add => 0x6a,
            I64Add => 0x7c,
            I32Sub => 0x6b,
            I64Sub => 0x7d,
            I32Mul => 0x6c,
            I64Mul => 0x7e,
            I32DivS => 0x6d,
            I64DivS => 0x7f,
            I32DivU => 0x6e,
            I64DivU => 0x80,
            I32RemS => 0x6f,
            I64RemS => 0x81,
            I32RemU => 0x70,
            I64RemU => 0x82,
            I32And => 0x71,
            I64And => 0x83,
            I32Or => 0x72,
            I64Or => 0x84,
            I32Xor => 0x73,
            I64Xor => 0x85,
            I32Shl => 0x74,
            I64Shl => 0x86,
            I32ShrS => 0x75,
            I64ShrS => 0x87,
            I32ShrU => 0x76,
            I64ShrU => 0x88,
            I32Popcnt => 0x69,
            I64Popcnt => 0x7b,
            // Integer comparisons
            I32Eq => 0x46,
            I64Eq => 0x51,
            I32Ne => 0x47,
            I64Ne => 0x52,
            I32LtS => 0x48,
            I64LtS => 0x53,
            I32LtU => 0x49,
            I64LtU => 0x54,
            I32GtS => 0x4a,
            I64GtS => 0x55,
            I32GtU => 0x4b,
            I64GtU => 0x56,
            I32LeS => 0x4c,
            I64LeS => 0x57,
            I32LeU => 0x4d,
            I64LeU => 0x58,
            I32GeS => 0x4e,
            I64GeS => 0x59,
            I32GeU => 0x4f,
            I64GeU => 0x5a,
            // FP arithmetic
            F32Add => 0x92,
            F64Add => 0xa0,
            F32Sub => 0x93,
            F64Sub => 0xa1,
            F32Mul => 0x94,
            F64Mul => 0xa2,
            F32Div => 0x95,
            F64Div => 0xa3,
            F32Min => 0x96,
            F64Min => 0xa4,
            F32Max => 0x97,
            F64Max => 0xa5,
            // FP comparisons
            F32Eq => 0x5b,
            F64Eq => 0x61,
            F32Ne => 0x5c,
            F64Ne => 0x62,
            F32Lt => 0x5d,
            F64Lt => 0x63,
            F32Gt => 0x5e,
            F64Gt => 0x64,
            F32Le => 0x5f,
            F64Le => 0x65,
            F32Ge => 0x60,
            F64Ge => 0x66,
            // FP unary
            F32Abs => 0x8b,
            F64Abs => 0x99,
            F32Neg => 0x8c,
            F64Neg => 0x9a,
            F32Sqrt => 0x91,
            F64Sqrt => 0x9f,
            F32Ceil => 0x8d,
            F64Ceil => 0x9b,
            F32Floor => 0x8e,
            F64Floor => 0x9c,
            F32Trunc => 0x8f,
            F64Trunc => 0x9d,
            // Casts
            I32WrapI64 => 0xa7,
            I64ExtendI32S => 0xac,
            I64ExtendI32U => 0xad,
            F32DemoteF64 => 0xb6,
            F64PromoteF32 => 0xbb,
            F32ConvertI32S => 0xb2,
            F32ConvertI32U => 0xb3,
            F32ConvertI64S => 0xb4,
            F32ConvertI64U => 0xb5,
            F64ConvertI32S => 0xb7,
            F64ConvertI32U => 0xb8,
            F64ConvertI64S => 0xb9,
            F64ConvertI64U => 0xba,
            I32ReinterpretF32 => 0xbc,
            I64ReinterpretF64 => 0xbd,
            F32ReinterpretI32 => 0xbe,
            F64ReinterpretI64 => 0xbf,
            // 0xfc-prefixed saturating conversions: PREFIX byte.
            I32TruncSatF32S | I32TruncSatF32U | I32TruncSatF64S | I32TruncSatF64U
            | I64TruncSatF32S | I64TruncSatF32U | I64TruncSatF64S | I64TruncSatF64U => 0xfc,
            // Constants
            I32Const => 0x41,
            I64Const => 0x42,
            // Locals / globals
            LocalGet => 0x20,
            LocalSet => 0x21,
            LocalTee => 0x22,
            GlobalGet => 0x23,
            GlobalSet => 0x24,
            // Memory
            I32Load => 0x28,
            I64Load => 0x29,
            I32Store => 0x36,
            I64Store => 0x37,
            // Control flow
            Unreachable => 0x00,
            Nop => 0x01,
            Block => 0x02,
            Loop => 0x03,
            If => 0x04,
            Else => 0x05,
            End => 0x0b,
            Br => 0x0c,
            BrIf => 0x0d,
            BrTable => 0x0e,
            Return => 0x0f,
            Drop => 0x1a,
            // Calls
            Call => 0x10,
            CallIndirect => 0x11,
            // SIMD / v128: 0xfd PREFIX byte.
            V128Load | V128Store | V128Const | I32x4Add | I32x4Mul | F32x4Add | F32x4Mul => 0xfd,
        }
    }

    /// The 0xfc-prefix SUB-INDEX (the LEB128 immediate following the 0xfc prefix)
    /// for the saturating float->int conversions, per the wasm spec. `None` for
    /// every non-0xfc-prefixed opcode.
    ///
    /// Together with `opcode_byte()` (the 0xfc prefix) this is the COMPLETE machine
    /// encoding of a `trunc_sat` instruction, so the verifier can reconstruct the
    /// machine side from the real (prefix, sub-index) pair — and a wrong sub-index
    /// (e.g. the unsigned form where the signed was intended) decodes to a different
    /// conversion ⇒ REFUTE.
    pub fn trunc_sat_sub_opcode(self) -> Option<u32> {
        use WasmOpcode::*;
        Some(match self {
            I32TruncSatF32S => 0,
            I32TruncSatF32U => 1,
            I32TruncSatF64S => 2,
            I32TruncSatF64U => 3,
            I64TruncSatF32S => 4,
            I64TruncSatF32U => 5,
            I64TruncSatF64S => 6,
            I64TruncSatF64U => 7,
            _ => return None,
        })
    }

    /// The 0xfd-prefix SUB-OPCODE (the LEB128 immediate following the 0xfd SIMD
    /// prefix) per the wasm SIMD spec. `None` for every non-0xfd-prefixed opcode.
    ///
    /// Together with `opcode_byte()` (the 0xfd prefix) this is the COMPLETE machine
    /// encoding of a v128 instruction, so the verifier can reconstruct the machine
    /// side from the real (prefix, sub-opcode) pair — and decode the LANE op +
    /// arrangement from the sub-opcode. A WRONG sub-opcode (e.g. `i32x4.mul` 0xb5
    /// where `i32x4.add` 0xae was intended, or `f32x4.mul` for `i32x4.mul`) decodes
    /// to a different lane operation / lane width ⇒ REFUTE.
    ///
    /// Reference: WebAssembly SIMD proposal — the `0xfd` opcode table.
    pub fn simd_sub_opcode(self) -> Option<u32> {
        use WasmOpcode::*;
        Some(match self {
            V128Load => 0x00,
            V128Store => 0x0b,
            V128Const => 0x0c,
            I32x4Add => 0xae,
            I32x4Mul => 0xb5,
            F32x4Add => 0xe4,
            F32x4Mul => 0xe6,
            _ => return None,
        })
    }

    /// True for a SIMD / v128 instruction (the 0xfd-prefixed surface).
    ///
    /// The lane-wise SIMD VALUE ops (`i32x4.add/mul`, `f32x4.add/mul`) are now
    /// RECONSTRUCTED lane-wise by the verifier; the v128 memory/materialization
    /// forms (`v128.load/store/const`) are STRUCTURAL (mirroring the scalar
    /// load/store/const family) — see `classify_wasm`.
    pub fn is_simd(self) -> bool {
        use WasmOpcode::*;
        matches!(
            self,
            V128Load | V128Store | V128Const | I32x4Add | I32x4Mul | F32x4Add | F32x4Mul
        )
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// The current `WasmOpcode` release baseline, in declaration order. The
    /// coverage-gate test independently parses this enum declaration to enforce
    /// `ALL_WASM_OPCODES` completeness; this local count is only a drift pin.
    fn all_opcodes() -> Vec<WasmOpcode> {
        use WasmOpcode::*;
        vec![
            I32Add,
            I64Add,
            I32Sub,
            I64Sub,
            I32Mul,
            I64Mul,
            I32DivS,
            I64DivS,
            I32DivU,
            I64DivU,
            I32RemS,
            I64RemS,
            I32RemU,
            I64RemU,
            I32And,
            I64And,
            I32Or,
            I64Or,
            I32Xor,
            I64Xor,
            I32Shl,
            I64Shl,
            I32ShrS,
            I64ShrS,
            I32ShrU,
            I64ShrU,
            I32Popcnt,
            I64Popcnt,
            I32Eq,
            I64Eq,
            I32Ne,
            I64Ne,
            I32LtS,
            I64LtS,
            I32LtU,
            I64LtU,
            I32GtS,
            I64GtS,
            I32GtU,
            I64GtU,
            I32LeS,
            I64LeS,
            I32LeU,
            I64LeU,
            I32GeS,
            I64GeS,
            I32GeU,
            I64GeU,
            F32Add,
            F64Add,
            F32Sub,
            F64Sub,
            F32Mul,
            F64Mul,
            F32Div,
            F64Div,
            F32Min,
            F64Min,
            F32Max,
            F64Max,
            F32Eq,
            F64Eq,
            F32Ne,
            F64Ne,
            F32Lt,
            F64Lt,
            F32Gt,
            F64Gt,
            F32Le,
            F64Le,
            F32Ge,
            F64Ge,
            F32Abs,
            F64Abs,
            F32Neg,
            F64Neg,
            F32Sqrt,
            F64Sqrt,
            F32Ceil,
            F64Ceil,
            F32Floor,
            F64Floor,
            F32Trunc,
            F64Trunc,
            I32WrapI64,
            I64ExtendI32S,
            I64ExtendI32U,
            F32DemoteF64,
            F64PromoteF32,
            F32ConvertI32S,
            F32ConvertI32U,
            F32ConvertI64S,
            F32ConvertI64U,
            F64ConvertI32S,
            F64ConvertI32U,
            F64ConvertI64S,
            F64ConvertI64U,
            I32ReinterpretF32,
            I64ReinterpretF64,
            F32ReinterpretI32,
            F64ReinterpretI64,
            I32TruncSatF32S,
            I32TruncSatF32U,
            I32TruncSatF64S,
            I32TruncSatF64U,
            I64TruncSatF32S,
            I64TruncSatF32U,
            I64TruncSatF64S,
            I64TruncSatF64U,
            I32Const,
            I64Const,
            LocalGet,
            LocalSet,
            LocalTee,
            GlobalGet,
            GlobalSet,
            I32Load,
            I64Load,
            I32Store,
            I64Store,
            Unreachable,
            Nop,
            Block,
            Loop,
            If,
            Else,
            End,
            Br,
            BrIf,
            BrTable,
            Return,
            Drop,
            Call,
            CallIndirect,
            V128Load,
            V128Store,
            V128Const,
            I32x4Add,
            I32x4Mul,
            F32x4Add,
            F32x4Mul,
        ]
    }

    #[test]
    fn opcode_count() {
        assert_eq!(all_opcodes().len(), 141);
    }

    #[test]
    fn opcode_bytes_are_unique_within_single_byte_ops() {
        // The single-byte (non-prefixed) opcodes must all have distinct bytes —
        // a collision would mean two value ops share an encoding (a real bug).
        let mut seen = std::collections::HashMap::new();
        for op in all_opcodes() {
            if op.is_simd() {
                continue; // 0xfd prefix shared by all SIMD; sub-index distinguishes.
            }
            // The 8 saturating-conversion ops share the 0xfc prefix; skip those.
            if op.opcode_byte() == 0xfc {
                continue;
            }
            if let Some(prev) = seen.insert(op.opcode_byte(), op) {
                panic!(
                    "opcode byte 0x{:02x} shared by {prev:?} and {op:?}",
                    op.opcode_byte()
                );
            }
        }
    }

    #[test]
    fn simd_ops_carry_the_fd_prefix() {
        for op in all_opcodes() {
            if op.is_simd() {
                assert_eq!(
                    op.opcode_byte(),
                    0xfd,
                    "{op:?} must carry the 0xfd SIMD prefix"
                );
            }
        }
    }
}
