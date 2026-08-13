// trust-cg-lower/instructions.rs - LIR instruction set
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Instruction definitions for Trust Codegen Low-level IR.

use crate::types::Type;
use serde::{Deserialize, Serialize};
use trust_cg_ir::TlsModel;

/// A value reference in the IR.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Value(pub u32);

/// A basic block reference.
/// `Ord`/`PartialOrd` are derived so block sets can live in a `BTreeSet` and
/// iterate in a DETERMINISTIC order. `HashSet<Block>` iteration order depends on
/// Rust's per-process `RandomState` seed, which made the x86 vectorizer emit
/// different (but equally valid) code for the same input on different runs — see
/// the loop-body sets in `x86_vectorize.rs`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Block(pub u32);

/// LIR opcodes.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Opcode {
    // Constants
    Iconst {
        ty: Type,
        imm: i64,
    },
    /// Materialize a full 128-bit integer constant as two explicit 64-bit
    /// halves.
    ///
    /// The single-immediate [`Opcode::Iconst`] carries one `i64` and derives the
    /// i128 high half as that immediate's sign extension, so it can only express
    /// i128/u128 values that fit in `i64::MIN..=i64::MAX`. Wide constants (whose
    /// high 64 bits are NOT the sign extension of the low 64 bits) need both
    /// halves supplied independently.
    ///
    /// Semantics: the result is the I128 value
    /// `((hi as u128) << 64) | (lo as u128)`, where `lo`/`hi` are the raw 64-bit
    /// bit patterns of the two halves (carried as `i64` because LIR immediates
    /// are `i64`). The result type is always [`Type::I128`]; there is no `ty`
    /// field. ISel lowers this to two independent 64-bit immediate moves into the
    /// low/high registers of the i128 GPR pair — each move is the already-proven
    /// `MovRI` (x86) / `Movz`+`Movk` (AArch64) primitive, so no new
    /// per-instruction proof obligation is introduced.
    Iconst128 {
        lo: i64,
        hi: i64,
    },
    Fconst {
        ty: Type,
        imm: f64,
    },

    /// Register-to-register copy (move) pseudo-instruction.
    ///
    /// `args[0]` is the source value; `results[0]` is the destination. The
    /// instruction has no other semantic effect — it is equivalent to
    /// `dst = src`. This exists at the LIR level to model block-argument
    /// passing, trust_ir `Inst::Copy`, borrow lowering, and similar "value
    /// renaming" patterns without piggybacking on `Iadd`.
    ///
    /// ISel lowers this to `MovR` on AArch64 and `MovRR` on x86-64.
    ///
    /// History: previously single-argument `Iadd` was used as an implicit
    /// COPY pseudo, which made SMT verification harder (add vs copy
    /// semantics) and forced both ISels to re-detect copies via
    /// `Opcode::Iadd if inst.args.len() == 1`. See #417 for the fix.
    Copy,
    // Arithmetic
    Iadd,
    Isub,
    Imul,
    Udiv,
    Sdiv,
    Urem,
    Srem,
    /// Proof-only divide-by-zero guard.
    ///
    /// `args[0]` is the divisor. The instruction has no results. The adapter
    /// emits this only when the source trust_ir division/remainder node carries
    /// `ProofAnnotation::DivNonZero`, giving downstream proof-consuming passes
    /// an exact guard/check instruction to eliminate without changing
    /// unproved division semantics.
    GuardDivZero {
        /// Sentinel: the trust-ir proof obligation id (from a `ProofAnnotation::ProofRef`) that
        /// discharges this exact div-by-zero check, if the producer supplied one. Absent an explicit
        /// `ProofRef`, the adapter SYNTHESIZES a `Discharged` obligation FROM the `DivNonZero` proof
        /// itself (DivNonZero IS the upstream safety proof, exactly as `NotNull` is for `GuardNull`).
        /// `None` => no bound obligation, so the Certified-Elimination Kernel keeps the guard
        /// (fail-safe). Threaded onto the AArch64 `TrapDivZeroIfZero` carrier so the kernel-gated
        /// proof pass can authorize elimination against the discharged-evidence table.
        obligation: Option<u64>,
    },
    /// Proof-only null-pointer guard.
    ///
    /// `args[0]` is the pointer. The instruction has no results. The adapter
    /// emits this only when a source trust_ir memory node carries
    /// `ProofAnnotation::NotNull`, giving downstream proof-consuming passes an
    /// exact runtime guard to eliminate without treating unrelated null traps as
    /// NotNull consumers.
    GuardNull {
        /// Sentinel: the trust-ir proof obligation id (from a `ProofAnnotation::ProofRef`) that
        /// discharges this exact null check, if the producer supplied one. Absent an explicit
        /// `ProofRef`, the adapter SYNTHESIZES a `Discharged` obligation FROM the `NotNull` proof
        /// itself (NotNull IS the upstream safety proof, exactly as `InBounds` is for
        /// `GuardBoundsCheck`). `None` => no bound obligation, so the Certified-Elimination Kernel
        /// keeps the guard (fail-safe). Threaded onto the AArch64 `TrapNullIfZero` carrier so the
        /// kernel-gated proof pass can authorize elimination against the discharged-evidence table.
        obligation: Option<u64>,
    },
    /// Proof-only shift-amount range guard.
    ///
    /// `args[0]` is the shift amount and `bitwidth` is the exact scalar
    /// integer width for the shift. The adapter emits this only when the
    /// source trust_ir shift node carries `ProofAnnotation::ShiftInRange`, giving
    /// downstream proof-consuming passes an exact guard/check instruction to
    /// eliminate without inferring safety from the MIR shape alone.
    GuardShiftRange {
        bitwidth: u16,
        /// Sentinel: the trust-ir proof obligation id (from a `ProofAnnotation::ProofRef`) that
        /// discharges this exact shift-range check, if the producer supplied one. Absent an explicit
        /// `ProofRef`, the adapter SYNTHESIZES a `Discharged` obligation FROM the `ShiftInRange` proof
        /// itself (ShiftInRange IS the upstream safety proof, exactly as `InBounds` is for
        /// `GuardBoundsCheck`). `None` => no bound obligation, so the Certified-Elimination Kernel
        /// keeps the guard (fail-safe). Threaded onto the AArch64 `TrapShiftRangeIfOOB` carrier so the
        /// kernel-gated proof pass can authorize elimination against the discharged-evidence table.
        obligation: Option<u64>,
    },
    /// Proof-only arithmetic-overflow guard with self-contained operand identity.
    ///
    /// `args[0]` is the left operand and `args[1]` is the right operand of the
    /// arithmetic op whose overflow is being checked; the instruction has NO
    /// results — the VALUE is produced by a SEPARATE plain ADD/SUB. `op_tag`
    /// packs the op-kind (signed/unsigned × add/sub) and operand width (see
    /// [`trust_cg_ir::pack_overflow_tag`]). ISel lowers this to a self-contained
    /// `AArch64Opcode::TrapOverflowExact lhs, rhs, Imm(op_tag)` carrier, the
    /// OVERFLOW analogue of [`Self::GuardBoundsCheck`]/[`Self::GuardShiftRange`].
    ///
    /// Unlike the legacy entangled overflow path (where one `ADDS/SUBS` did double
    /// duty as both the value op AND the NZCV overflow check, consumed by
    /// `apply_no_overflow`), this DECOUPLES the value from the check: a KEPT
    /// carrier RE-DERIVES the overflow flags from its own `[lhs, rhs]`. The
    /// `op_tag` participates in the carrier fingerprint, so a wrong-op or
    /// wrong-width overflow proof cannot discharge it.
    GuardOverflow {
        /// Packed `(op_kind, width)` for the checked arithmetic (see
        /// [`trust_cg_ir::pack_overflow_tag`]). Threaded into the carrier's third
        /// operand so it participates in the operand fingerprint.
        op_tag: i64,
        /// Sentinel: the trust-ir proof obligation id that discharges this exact
        /// overflow check. Absent an explicit `ProofRef`, the adapter SYNTHESIZES a
        /// `Discharged` obligation FROM the genuine overflow proof
        /// (`NoOverflow`/`NoSignedOverflow`/`NoUnsignedOverflow` IS the upstream
        /// safety proof, exactly as `InBounds` is for `GuardBoundsCheck`). `None`
        /// => no bound obligation, so the Certified-Elimination Kernel keeps the
        /// guard (fail-safe). Threaded onto the `TrapOverflowExact` carrier so the
        /// kernel-gated proof pass can authorize elimination against the
        /// discharged-evidence table.
        obligation: Option<u64>,
    },
    /// Proof-only array bounds guard with exact source identity.
    ///
    /// `args[0]` is the base value, `args[1]` is the index value, and `bound`
    /// is the exact known element count from trust_ir type metadata. The adapter
    /// emits this only when the source trust_ir node carries `InBounds` and the
    /// bound is known exactly, giving downstream proof-consuming passes a
    /// proof-only carrier that does not consume legacy CMP+TrapBoundsCheck
    /// shapes.
    /// Proof-only bounds guard with a DYNAMIC (register) bound.
    ///
    /// Sibling of [`Self::GuardBoundsCheck`] for the case its `bound: u64` field
    /// cannot express: a heap slice or `Vec` whose length is only known at
    /// runtime, e.g. `while k < v.len() { .. v[k] .. }`.
    ///
    /// `args[0]` is the base, `args[1]` the index, and `args[2]` the LENGTH.
    /// Lowers to the same `TrapBoundsCheckExact` carrier, but with a register in
    /// the bound slot — which `expand_trap_bounds_check_exact` already lowers to
    /// `CmpRR` rather than `CmpRI`.
    ///
    /// Introduced as a separate variant rather than by widening
    /// `GuardBoundsCheck::bound`, because that field is matched at 65 sites and
    /// every one of them is correct for the constant case. A new variant leaves
    /// them untouched and makes the dynamic path opt-in.
    GuardBoundsCheckDyn {
        /// Same meaning as [`Self::GuardBoundsCheck::obligation`]: the trust-ir
        /// obligation id discharging this check, or `None` => keep the guard
        /// (fail-safe).
        obligation: Option<u64>,
    },
    GuardBoundsCheck {
        bound: u64,
        /// Sentinel: the trust-ir proof obligation id (from a `ProofAnnotation::ProofRef`) that
        /// discharges this exact bounds check, if the producer supplied one. `None` => no bound
        /// obligation, so the Certified-Elimination Kernel keeps the guard (fail-safe). Threaded
        /// onto the AArch64 `TrapBoundsCheckExact` carrier so the kernel-gated proof pass can
        /// authorize elimination against the discharged-evidence table.
        obligation: Option<u64>,
    },
    /// Runtime assertion guard.
    ///
    /// `args[0]` is the assertion condition. Execution continues when the
    /// condition is non-zero and traps when it is zero. This is not proof-only:
    /// dropping it would silently ignore a source `trust_ir::Inst::Assert`.
    Assert,
    Ineg, // Integer negate: result = -operand

    // Bitwise unary
    Bnot,  // Bitwise NOT: result = ~operand
    CtPop, // Population count: result = number of set bits in operand

    // Floating-point unary
    Fneg,   // Floating-point negate: result = -operand
    Fabs,   // Floating-point absolute value: result = |operand|
    Fsqrt,  // Floating-point square root: result = sqrt(operand)
    Ffloor, // Float round-to-integral toward -inf: result = floor(operand)
    Fceil,  // Float round-to-integral toward +inf: result = ceil(operand)
    Ftrunc, // Float round-to-integral toward zero: result = trunc(operand)

    // Shift operations
    Ishl, // Logical shift left
    Ushr, // Logical shift right (unsigned)
    Sshr, // Arithmetic shift right (signed)

    // Logical operations
    Band,    // Bitwise AND
    Bor,     // Bitwise OR
    Bxor,    // Bitwise XOR
    BandNot, // Bitwise AND-NOT (BIC)
    BorNot,  // Bitwise OR-NOT (ORN)

    // Extensions
    Sextend {
        from_ty: Type,
        to_ty: Type,
    }, // Sign-extend
    Uextend {
        from_ty: Type,
        to_ty: Type,
    }, // Zero-extend

    // Bitfield operations
    ExtractBits {
        lsb: u8,
        width: u8,
    }, // Unsigned bitfield extract (UBFM)
    SextractBits {
        lsb: u8,
        width: u8,
    }, // Signed bitfield extract (SBFM)
    InsertBits {
        lsb: u8,
        width: u8,
    }, // Bitfield insert (BFM)
    /// Compact a canonical `<4 x i32>` lane mask into an `i32` bitmask.
    ///
    /// `args[0]` is a V128 value whose i32 lanes are all-zero or all-ones
    /// mask lanes. `results[0]` is I32 with bits 0..3 set from lanes 0..3 and
    /// all upper bits cleared.
    V4I32MaskExtract,
    /// Compact a canonical `<16 x i8>` lane mask into an `i32` bitmask.
    ///
    /// `args[0]` is a V128 value whose i8 lanes are all-zero or all-ones
    /// mask lanes. `results[0]` is I32 with bits 0..15 set from lanes 0..15
    /// and all upper bits cleared.
    V16I8MaskExtract,
    /// Compact a canonical `<8 x i16>` lane mask into an `i32` bitmask.
    ///
    /// `args[0]` is a V128 value whose i16 lanes are all-zero or all-ones
    /// mask lanes. `results[0]` is I32 with bits 0..7 set from lanes 0..7 and
    /// all upper bits cleared.
    V8I16MaskExtract,
    /// Compact a canonical `<2 x i64>` lane mask into scalar low bits.
    ///
    /// `args[0]` is a V128 value whose i64 lanes are all-zero or all-ones
    /// mask lanes. This also covers the Trust Codegen x86 physical representation of
    /// `<2 x bool>` v2i64 compare masks. `results[0]` is `result_ty` I32 or
    /// I64 with bits 0..1 set from lanes 0..1 and all upper bits cleared.
    V2I64MaskExtract {
        result_ty: Type,
    },
    /// Materialize an all-zero `<4 x i32>` V128 value.
    ///
    /// `results[0]` is V128. x86-64 lowers this to PXOR or folds it into a
    /// zero-base lane insertion.
    V4I32Zero,
    /// Materialize an all-zero `<2 x i64>` V128 value.
    ///
    /// `results[0]` is V128. x86-64 lowers this to PXOR or folds it into a
    /// zero-base lane insertion.
    V2I64Zero,
    /// Pack four scalar i32 values into a single `<4 x i32>` V128 value.
    ///
    /// `args[0..4]` are I32 lane values. `args[0]` becomes lane 0, the low
    /// dword; `args[3]` becomes lane 3, the high dword. `results[0]` is V128.
    V4I32PackLanes,
    /// Pack two scalar i64 values into a single `<2 x i64>` V128 value.
    ///
    /// `args[0..2]` are I64 lane values. `args[0]` becomes lane 0, the low
    /// qword; `args[1]` becomes lane 1, the high qword. `results[0]` is V128.
    V2I64PackLanes,
    /// Pack sixteen scalar i8 values into a single `<16 x i8>` V128 value.
    ///
    /// `args[0..16]` are I8 lane values. `args[0]` becomes byte lane 0, the
    /// low byte; `args[15]` becomes byte lane 15, the high byte. `results[0]`
    /// is V128.
    V16I8PackLanes,
    /// Pack eight scalar i16 values into a single `<8 x i16>` V128 value.
    ///
    /// `args[0..8]` are I16 lane values. `args[0]` becomes halfword lane 0,
    /// the low halfword; `args[7]` becomes halfword lane 7, the high halfword.
    /// `results[0]` is V128.
    V8I16PackLanes,
    /// Pack eight scalar i8 values into a single `<8 x i8>` V64 (D-register)
    /// value.
    ///
    /// `args[0..8]` are I8 lane values. `args[0]` becomes byte lane 0, the low
    /// byte; `args[7]` becomes byte lane 7. `results[0]` is V64 (Fpr64). When
    /// every lane is the SAME value (a splat, e.g. hashbrown's `simd_splat`
    /// control-byte broadcast) AArch64 lowers this to a single NEON `dup.8b`;
    /// otherwise a `dup.8b` of lane 0 followed by `ins` of the remaining lanes.
    V8I8PackLanes,
    /// Add two `<2 x i64>` V128 values lane-wise with wrapping i64 semantics.
    ///
    /// `args[0]` and `args[1]` are V128 values known to be typed `<2 x i64>`.
    /// `results[0]` is V128. x86-64 lowers this to SSE2 PADDQ.
    V2I64Add,
    /// Subtract two `<2 x i64>` V128 values lane-wise with wrapping i64 semantics.
    ///
    /// `args[0]` and `args[1]` are V128 values known to be typed `<2 x i64>`.
    /// `results[0]` is V128. x86-64 lowers this to SSE2 PSUBQ.
    V2I64Sub,
    /// Multiply two `<2 x i64>` V128 values lane-wise with wrapping i64 semantics.
    ///
    /// `args[0]` and `args[1]` are V128 values known to be typed `<2 x i64>`.
    /// `results[0]` is V128. Baseline x86-64 and AArch64 lower this through
    /// scalar lane extraction, scalar 64-bit multiply, and vector repacking.
    V2I64Mul,
    /// Add two `<4 x i32>` V128 values lane-wise with wrapping i32 semantics.
    ///
    /// `args[0]` and `args[1]` are V128 values known to be typed `<4 x i32>`.
    /// `results[0]` is V128. x86-64 lowers this to SSE2 PADDD and AArch64
    /// lowers this to NEON ADD.4S.
    V4I32Add,
    /// Subtract two `<4 x i32>` V128 values lane-wise with wrapping i32 semantics.
    ///
    /// `args[0]` and `args[1]` are V128 values known to be typed `<4 x i32>`.
    /// `results[0]` is V128. x86-64 lowers this to SSE2 PSUBD and AArch64
    /// lowers this to NEON SUB.4S.
    V4I32Sub,
    /// Multiply two `<4 x i32>` V128 values lane-wise with wrapping i32 semantics.
    ///
    /// `args[0]` and `args[1]` are V128 values known to be typed `<4 x i32>`.
    /// `results[0]` is V128. x86-64 lowers this to a baseline SSE2 PMULUDQ
    /// shuffle sequence unless SSE4.1 PMULLD is explicitly enabled by the
    /// pipeline; AArch64 lowers this to NEON MUL.4S.
    V4I32Mul,
    /// Add two `<16 x i8>` V128 values lane-wise with wrapping i8 semantics.
    ///
    /// `args[0]` and `args[1]` are V128 values known to be typed `<16 x i8>`.
    /// `results[0]` is V128. x86-64 lowers this to SSE2 PADDB.
    V16I8Add,
    /// Subtract two `<16 x i8>` V128 values lane-wise with wrapping i8 semantics.
    ///
    /// `args[0]` and `args[1]` are V128 values known to be typed `<16 x i8>`.
    /// `results[0]` is V128. x86-64 lowers this to SSE2 PSUBB.
    V16I8Sub,
    /// Multiply two `<16 x i8>` V128 values lane-wise with wrapping i8 semantics.
    ///
    /// `args[0]` and `args[1]` are V128 values known to be typed `<16 x i8>`.
    /// `results[0]` is V128. x86-64 lowers this to an SSE2 unpack/PMULLW/pack
    /// sequence and AArch64 lowers this to NEON MUL.16B.
    V16I8Mul,
    /// Add two `<8 x i16>` V128 values lane-wise with wrapping i16 semantics.
    ///
    /// `args[0]` and `args[1]` are V128 values known to be typed `<8 x i16>`.
    /// `results[0]` is V128. x86-64 lowers this to SSE2 PADDW.
    V8I16Add,
    /// Subtract two `<8 x i16>` V128 values lane-wise with wrapping i16 semantics.
    ///
    /// `args[0]` and `args[1]` are V128 values known to be typed `<8 x i16>`.
    /// `results[0]` is V128. x86-64 lowers this to SSE2 PSUBW.
    V8I16Sub,
    /// Multiply two `<8 x i16>` V128 values lane-wise with wrapping i16 semantics.
    ///
    /// `args[0]` and `args[1]` are V128 values known to be typed `<8 x i16>`.
    /// `results[0]` is V128. x86-64 lowers this to SSE2 PMULLW and AArch64
    /// lowers this to NEON MUL.8H.
    V8I16Mul,
    /// Compare two `<16 x i8>` V128 values lane-wise and produce canonical masks.
    ///
    /// `args[0]` and `args[1]` are V128 values known to be typed `<16 x i8>`.
    /// `results[0]` is V128 with each i8 lane either all-zero or all-ones.
    /// x86-64 lowers this to SSE2 PCMPEQB/PCMPGTB sequences, using sign-bit
    /// bias for unsigned predicates. AArch64 lowers this to NEON
    /// CMEQ/CMGT/CMGE/CMHI/CMHS sequences.
    V16I8Icmp {
        cond: IntCC,
    },
    /// Compare two `<8 x i16>` V128 values lane-wise and produce canonical masks.
    ///
    /// `args[0]` and `args[1]` are V128 values known to be typed `<8 x i16>`.
    /// `results[0]` is V128 with each i16 lane either all-zero or all-ones.
    /// x86-64 lowers this to SSE2 PCMPEQW/PCMPGTW sequences, using sign-bit
    /// bias for unsigned predicates. AArch64 lowers this to NEON
    /// CMEQ/CMGT/CMGE/CMHI/CMHS sequences.
    V8I16Icmp {
        cond: IntCC,
    },
    /// Compare two `<4 x i32>` V128 values lane-wise and produce canonical masks.
    ///
    /// `args[0]` and `args[1]` are V128 values known to be typed `<4 x i32>`.
    /// `results[0]` is V128 with each i32 lane either all-zero or all-ones.
    /// x86-64 lowers this to SSE2 PCMPEQD/PCMPGTD sequences, using a sign-bit
    /// bias for unsigned predicates. AArch64 lowers this to NEON
    /// CMEQ/CMGT/CMGE/CMHI/CMHS sequences.
    V4I32Icmp {
        cond: IntCC,
    },
    /// Compare two `<2 x i64>` V128 values lane-wise and produce canonical masks.
    ///
    /// `args[0]` and `args[1]` are V128 values known to be typed `<2 x i64>`.
    /// `results[0]` is V128 with each i64 lane either all-zero or all-ones.
    /// x86-64 lowers this to SSE4.1/SSE4.2 PCMPEQQ/PCMPGTQ sequences, using
    /// sign-bit bias for unsigned predicates. AArch64 lowers this to NEON
    /// CMEQ/CMGT/CMGE/CMHI/CMHS sequences.
    V2I64Icmp {
        cond: IntCC,
    },
    /// Compare two `<8 x i8>` V64 (D-register) values lane-wise, producing
    /// canonical per-byte masks (all-zero / all-ones).
    ///
    /// `args[0]` and `args[1]` are V64 values known to be typed `<8 x i8>`.
    /// `results[0]` is V64 with each i8 lane either 0x00 or 0xFF. AArch64
    /// lowers this to NEON CMEQ/CMGT/CMGE/CMHI/CMHS with the `.8b` arrangement
    /// (D registers). This backs hashbrown's NEON group-scan control-byte
    /// compares (`vceq_u8`/`vcgez_s8`/`vcltz_s8`). No x86-64 lowering (the
    /// 64-bit D-register form is AArch64-only; x86 fails closed).
    V8I8Icmp {
        cond: IntCC,
    },
    /// Extract one scalar i32 lane from a `<4 x i32>` V128 value.
    ///
    /// `args[0]` is V128. `lane` must be in 0..=3. `results[0]` is I32.
    V4I32ExtractLane {
        lane: u8,
    },
    /// Insert one scalar i32 lane into a `<4 x i32>` V128 value.
    ///
    /// `args[0]` is the original V128 vector, `args[1]` is the I32 lane
    /// value. `lane` must be in 0..=3. `results[0]` is V128.
    V4I32InsertLane {
        lane: u8,
    },
    /// Extract one scalar i64 lane from a `<2 x i64>` V128 value.
    ///
    /// `args[0]` is V128. `lane` must be in 0..=1. `results[0]` is I64.
    V2I64ExtractLane {
        lane: u8,
    },
    /// Insert one scalar i64 lane into a `<2 x i64>` V128 value.
    ///
    /// `args[0]` is the original V128 vector, `args[1]` is the I64 lane
    /// value. `lane` must be in 0..=1. `results[0]` is V128.
    V2I64InsertLane {
        lane: u8,
    },
    /// Extract one scalar i8 lane from a `<16 x i8>` V128 value.
    ///
    /// `args[0]` is V128. `lane` must be in 0..=15. `results[0]` is I8.
    V16I8ExtractLane {
        lane: u8,
    },
    /// Insert one scalar i8 lane into a `<16 x i8>` V128 value.
    ///
    /// `args[0]` is the original V128 vector, `args[1]` is the I8 lane
    /// value. `lane` must be in 0..=15. `results[0]` is V128.
    V16I8InsertLane {
        lane: u8,
    },
    /// Extract one scalar i16 lane from a `<8 x i16>` V128 value.
    ///
    /// `args[0]` is V128. `lane` must be in 0..=7. `results[0]` is I16.
    V8I16ExtractLane {
        lane: u8,
    },
    /// Insert one scalar i16 lane into a `<8 x i16>` V128 value.
    ///
    /// `args[0]` is the original V128 vector, `args[1]` is the I16 lane
    /// value. `lane` must be in 0..=7. `results[0]` is V128.
    V8I16InsertLane {
        lane: u8,
    },

    // -- Packed floating-point arithmetic (`<4 x f32>` / `<2 x f64>`) --
    //
    // Each consumes two V128 operands holding the named packed FP shape and
    // produces a V128 result. The operation is applied independently per lane
    // as an IEEE-754 binary operation under the default MXCSR rounding mode
    // (round-to-nearest-even). x86-64 lowers these to the SSE/SSE2 ADDPS/ADDPD
    // instruction families; AArch64 would use the NEON FADD/FSUB/FMUL/FDIV
    // vector forms. Unlike the integer packed ops, the element type (f32 vs
    // f64) is encoded in the opcode because the V128 LIR type erases the lane
    // width and the two precisions select different machine instructions.
    /// Add two `<4 x f32>` V128 values lane-wise (four parallel binary32 adds).
    V4F32Fadd,
    /// Subtract two `<4 x f32>` V128 values lane-wise.
    V4F32Fsub,
    /// Multiply two `<4 x f32>` V128 values lane-wise.
    V4F32Fmul,
    /// Divide two `<4 x f32>` V128 values lane-wise.
    V4F32Fdiv,
    /// Add two `<2 x f64>` V128 values lane-wise (two parallel binary64 adds).
    V2F64Fadd,
    /// Subtract two `<2 x f64>` V128 values lane-wise.
    V2F64Fsub,
    /// Multiply two `<2 x f64>` V128 values lane-wise.
    V2F64Fmul,
    /// Divide two `<2 x f64>` V128 values lane-wise.
    V2F64Fdiv,

    // Conditional select
    Select {
        cond: IntCC,
    }, // csel(cond, lhs, rhs, cc_val) -> result

    // Comparisons
    Icmp {
        cond: IntCC,
    },

    // -- Checked integer arithmetic (#474) --
    //
    // Each of these consumes two same-typed integer operands and produces two
    // results: `[value, overflow_b1]`. The value result is the wrapping
    // (two's-complement) arithmetic result; the overflow result is a 1-bit
    // boolean indicating whether overflow occurred.
    //
    // These opcodes correspond to LLVM's signed and unsigned
    // `llvm.{s,u}{add,sub,mul}.with.overflow.iN` intrinsics. They exist as
    // first-class LIR ops so that instruction selection can lower directly to
    // AArch64's native flag/high-half idioms without pattern-matching bit-level
    // workarounds.
    //
    // Layout:
    //   args:    [lhs, rhs]
    //   results: [value, overflow_b1]
    //
    // The adapter maps `trust_ir::Inst::Overflow{AddOverflow|SubOverflow|MulOverflow}`
    // on I64/U64 directly to these opcodes. Narrower widths still use fallback
    // sequences until the ISel patterns are extended.
    CheckedSadd,
    CheckedSsub,
    CheckedSmul,
    CheckedUadd,
    CheckedUsub,
    CheckedUmul,

    // Floating-point arithmetic
    Fadd,
    Fsub,
    Fmul,
    Fdiv,
    /// Strict scalar fused multiply-add: `Fma(a, b, c) = a*b + c` with a
    /// SINGLE rounding (NOT round(a*b) then round(+c)). The adapter emits this
    /// for the IEEE `llvm.fma.f{32,64}` intrinsic. It must never be split into
    /// `Fmul` + `Fadd`. Lowers to AArch64 `FMADD`.
    /// Args: [a, b, c]; result: [dst].
    Fma,
    /// Fusion-licensed scalar multiply-add from `llvm.fmuladd.f{32,64}`.
    /// LLVM permits either fused single rounding or separate multiply/add
    /// rounding for this carrier. ISel initially emits AArch64 `FMADD` and
    /// records that the machine instruction may subsequently be unfused by a
    /// profitability pass. This is deliberately distinct from strict [`Self::Fma`].
    /// Args: [a, b, c]; result: [dst].
    Fmuladd,
    // Floating-point NaN-propagating-away minimum/maximum (Rust f{32,64}::
    // min/max). NOT IEEE fp.min/fp.max: if exactly one operand is NaN the
    // result is the OTHER operand; both NaN -> NaN; numerically lesser/greater
    // otherwise; signed-zero follows the hardware MINSD/MAXSD operand order.
    Fmin,
    Fmax,
    Fcmp {
        cond: FloatCC,
    },
    FcvtToInt {
        dst_ty: Type,
    }, // Float -> signed Int conversion (FCVTZS)
    FcvtToUint {
        dst_ty: Type,
    }, // Float -> unsigned Int conversion (FCVTZU)
    FcvtFromInt {
        src_ty: Type,
    }, // Signed Int -> Float conversion (SCVTF)
    FcvtFromUint {
        src_ty: Type,
    }, // Unsigned Int -> Float conversion (UCVTF)
    FPExt,   // Float precision widen (f32 -> f64)
    FPTrunc, // Float precision narrow (f64 -> f32)

    // Type conversions
    Trunc {
        to_ty: Type,
    }, // Integer truncation (narrow: i64->i32, etc.)
    Bitcast {
        to_ty: Type,
    }, // Reinterpret bits between same-size types

    // Addressing
    GlobalRef {
        name: String,
    }, // Reference to a local global symbol (ADRP + ADD)
    ExternRef {
        name: String,
    }, // Reference to an external symbol via GOT (ADRP + LDR from GOT)
    TlsRef {
        name: String,
        /// TLS access model. When `LocalExec`, `local_exec_offset` carries
        /// the pre-resolved TPREL byte offset (JIT owns layout).
        model: TlsModel,
        /// Pre-resolved TPREL offset for `LocalExec`. Required when
        /// `model == LocalExec`; ignored otherwise. Must be >= 0 and
        /// representable as 24-bit unsigned (two imm12 fields: hi12 << 12 | lo12).
        local_exec_offset: Option<u32>,
    },
    StackAddr {
        slot: u32,
    }, // Address of a stack slot (SP + offset)

    // Control flow
    Jump {
        dest: Block,
    },
    Brif {
        cond: Value,
        then_dest: Block,
        else_dest: Block,
    },
    /// Synchronous trap. Used for source-language assertions that must not be
    /// erased before a runnable artifact is produced.
    Trap,
    Return,
    Call {
        name: String,
    }, // Direct function call by symbol name
    /// Indirect function call via a register-held function pointer.
    ///
    /// `args[0]` is the function pointer (I64 address).
    /// `args[1..]` are the call arguments, classified per ABI.
    /// Lowered to BLR on AArch64.
    CallIndirect,
    /// Variadic function call (e.g., printf, NSLog).
    ///
    /// Apple AArch64 ABI: fixed args use normal register/stack classification,
    /// ALL variadic args are placed on the stack (8-byte aligned).
    /// `fixed_args` is the count of non-variadic parameters.
    CallVariadic {
        name: String,
        fixed_args: u32,
    },
    /// Invoke — call that may throw an exception.
    ///
    /// Like `Call`, but has two successors: a normal continuation block and
    /// an unwind landing pad block. If the callee returns normally, control
    /// transfers to `normal_dest`. If the callee throws an exception that
    /// is caught by a landing pad in this function, control transfers to
    /// `unwind_dest`.
    ///
    /// `args` are the call arguments, classified per ABI (same as Call).
    /// Results are the call return values (same as Call).
    ///
    /// Lowered to BL on AArch64, but with EH metadata: the call site
    /// gets an entry in the LSDA call site table pointing to the
    /// landing pad at `unwind_dest`.
    ///
    /// Reference: LLVM IR `invoke` instruction
    Invoke {
        name: String,
        normal_dest: Block,
        unwind_dest: Block,
    },

    /// Landing pad — exception handler entry point.
    ///
    /// Marks the beginning of an exception handler block. When the unwinder
    /// dispatches to this landing pad, it provides:
    /// - The exception object pointer (args[0] result, I64)
    /// - The type selector value (args[1] result, I32)
    ///
    /// The type selector is used by downstream code to determine which
    /// catch clause matched (if any), or whether this is a cleanup-only
    /// handler.
    ///
    /// `is_cleanup`: If true, this landing pad runs cleanup code (destructors)
    /// and then resumes unwinding. If false, it catches specific exception types.
    ///
    /// `catch_type_indices`: 1-based indices into the type table for catch
    /// clauses. Index 0 means catch-all. Empty for cleanup-only pads.
    ///
    /// Reference: LLVM IR `landingpad` instruction
    LandingPad {
        is_cleanup: bool,
        catch_type_indices: Vec<u32>,
    },

    /// Resume unwinding — re-throw the current exception.
    ///
    /// Used at the end of a cleanup landing pad to continue unwinding
    /// after executing cleanup code. `args[0]` is the exception object
    /// pointer. Lowered to a call to `_Unwind_Resume`.
    Resume,

    /// Multi-way branch (switch statement).
    ///
    /// `args[0]` is the selector value (integer).
    /// `cases` maps integer values to target blocks.
    /// `default` is the fallthrough block when no case matches.
    /// Lowered as a cascading CMP+B.EQ chain with default fallthrough.
    Switch {
        cases: Vec<(i64, Block)>,
        default: Block,
    },

    // Memory
    Load {
        ty: Type,
        align: Option<u32>,
    },
    Store {
        ty: Type,
        align: Option<u32>,
    },
    /// Volatile load — an observable memory access (MMIO / signal visibility).
    /// Identical machine encoding to `Load`, but lowered to a distinct machine
    /// opcode classified as a memory barrier so the optimizer never elides,
    /// CSEs, forwards, hoists, or reorders it (each `read_volatile` must
    /// re-read). Additive: it does not touch the 245 existing `Load` sites.
    VolatileLoad {
        ty: Type,
        align: Option<u32>,
    },
    /// Volatile store — the write counterpart of [`Opcode::VolatileLoad`].
    VolatileStore {
        ty: Type,
        align: Option<u32>,
    },

    // Atomic memory operations
    /// Atomic load with acquire semantics: result = atomic_load(ptr).
    /// args[0] = ptr. Lowered to LDAR on AArch64.
    AtomicLoad {
        ty: Type,
        ordering: AtomicOrdering,
    },
    /// Atomic store with release semantics: atomic_store(ptr, value).
    /// args[0] = value, args[1] = ptr. Lowered to STLR on AArch64.
    AtomicStore {
        ty: Type,
        ordering: AtomicOrdering,
    },
    /// Atomic read-modify-write: result (old value) = atomic_rmw(op, ptr, val).
    /// args[0] = val, args[1] = ptr. Lowered to target atomic RMW instructions or CAS loops.
    AtomicRmw {
        op: AtomicRmwOp,
        ty: Type,
        ordering: AtomicOrdering,
    },
    /// Compare-and-swap: result (old value) = cmpxchg(ptr, expected, desired).
    /// args[0] = expected, args[1] = desired, args[2] = ptr.
    /// Lowered to CAS (LSE) or LDAXR/STLXR loop (non-LSE).
    CmpXchg {
        ty: Type,
        success: AtomicOrdering,
        failure: AtomicOrdering,
    },
    /// Memory fence. No args, no results. Lowered to DMB.
    Fence {
        ordering: AtomicOrdering,
    },

    // Aggregate operations
    /// Compute address of a struct field: base_ptr + offset_of(struct_ty, field_index).
    /// args[0] = base pointer (pointer to struct), result = pointer to field.
    StructGep {
        struct_ty: Type,
        field_index: u32,
    },
    /// Compute address of an array element: base + index * sizeof(elem_ty).
    ///
    /// args[0] = base pointer (I64 address of the array),
    /// args[1] = index (I64). Result is a pointer to the element (I64).
    ///
    /// ISel lowers this to `LSL + ADD` when `elem_ty.bytes()` is a power of
    /// two, otherwise `MOVZ + MUL + ADD` (materialise size, multiply, add).
    ArrayGep {
        elem_ty: Type,
    },

    // Memory intrinsics
    /// memcpy intrinsic — bulk memory copy (non-overlapping).
    ///
    /// Compiler-generated for struct copies, array initialization, etc.
    /// args[0] = dest ptr (I64), args[1] = src ptr (I64), args[2] = length (I64).
    /// No results (void). Lowered to a call to libc `memcpy`.
    ///
    /// LLVM intrinsic names: `memcpy`, `llvm.memcpy.*`
    Memcpy,
    /// memmove intrinsic — bulk memory copy (handles overlapping regions).
    ///
    /// args[0] = dest ptr (I64), args[1] = src ptr (I64), args[2] = length (I64).
    /// No results (void). Lowered to a call to libc `memmove`.
    ///
    /// LLVM intrinsic names: `memmove`, `llvm.memmove.*`
    Memmove,
    /// memset intrinsic — bulk memory fill.
    ///
    /// args[0] = dest ptr (I64), args[1] = fill value (I32), args[2] = length (I64).
    /// No results (void). Lowered to a call to libc `memset`.
    ///
    /// LLVM intrinsic names: `memset`, `llvm.memset.*`
    Memset,
}

/// Floating-point comparison conditions.
///
/// IEEE 754 defines both ordered and unordered comparison predicates:
/// - **Ordered** comparisons return false when either operand is NaN.
/// - **Unordered** comparisons return true when either operand is NaN.
///
/// The relationship is: `Unordered_X(a,b) = Ordered_X(a,b) || isNaN(a) || isNaN(b)`.
/// Equivalently: `Unordered_X(a,b) = !Ordered_NOT_X(a,b)`.
///
/// On AArch64, FCMP sets NZCV=0011 (C=1,V=1) for NaN inputs. Ordered predicates
/// use condition codes that exclude V=1; unordered predicates use inverted ordered
/// condition codes so that V=1 (NaN) falls through as true.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum FloatCC {
    // Ordered comparisons (false when NaN)
    Equal,
    NotEqual,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
    Ordered,   // Neither operand is NaN
    Unordered, // At least one operand is NaN
    // Unordered comparisons (true when NaN)
    UnorderedEqual,
    UnorderedNotEqual,
    UnorderedLessThan,
    UnorderedLessThanOrEqual,
    UnorderedGreaterThan,
    UnorderedGreaterThanOrEqual,
}

/// Integer comparison conditions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum IntCC {
    Equal,
    NotEqual,
    SignedLessThan,
    SignedGreaterThanOrEqual,
    SignedGreaterThan,
    SignedLessThanOrEqual,
    UnsignedLessThan,
    UnsignedGreaterThanOrEqual,
    UnsignedGreaterThan,
    UnsignedLessThanOrEqual,
}

/// Memory ordering for atomic operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AtomicOrdering {
    /// No ordering constraint.
    Relaxed,
    /// Acquire: subsequent reads/writes cannot be reordered before this.
    Acquire,
    /// Release: preceding reads/writes cannot be reordered after this.
    Release,
    /// Acquire + Release combined.
    AcqRel,
    /// Sequential consistency (strongest).
    SeqCst,
}

impl AtomicOrdering {
    /// THE compare-exchange failure-ordering validity rule (Rust/LLVM,
    /// C++17-and-later): the failure (load-only) ordering must not be
    /// `Release` or `AcqRel` — a failed compare-exchange performs no store,
    /// so a release constraint on it is meaningless. Modern LLVM (and Rust
    /// since 1.64) imposes NO other constraint: the failure ordering MAY be
    /// STRONGER than the success ordering (`compare_exchange(.., AcqRel,
    /// SeqCst)` in std's mutex/rwlock is legal).
    ///
    /// Every cmpxchg admission gate (the trust_ir adapter, the AArch64 ISel,
    /// the x86-64 ISel) must use exactly this predicate — one rule, all
    /// places. A backend whose opcode choice assumes `failure <= success`
    /// lifts the success side via [`Self::lift_for_cmpxchg_failure`] instead
    /// of rejecting.
    pub fn is_valid_cmpxchg_failure(self) -> bool {
        !matches!(self, AtomicOrdering::Release | AtomicOrdering::AcqRel)
    }

    /// Lift `self` (a cmpxchg SUCCESS ordering) minimally so it covers a
    /// legal-but-stronger `failure` ordering.
    ///
    /// Rust/C++17 allow the failure ordering to exceed the success ordering,
    /// but the ISels' opcode choice assumes `failure <= success`. Lifting
    /// yields a strictly STRONGER single ordering, never weaker, so the
    /// emitted machine sequence over-satisfies both paths (on AArch64 LSE the
    /// AcqRel and SeqCst mappings are the same `CASAL` family anyway; on
    /// x86-64 `LOCK CMPXCHG` is a full barrier regardless).
    ///
    /// `failure` must satisfy [`Self::is_valid_cmpxchg_failure`]; validity is
    /// the caller's gate, this only resolves relative strength.
    #[must_use]
    pub fn lift_for_cmpxchg_failure(self, failure: AtomicOrdering) -> AtomicOrdering {
        if self.allows_cmpxchg_failure(failure) {
            return self;
        }
        // failure is Relaxed/Acquire/SeqCst and stronger than the success
        // ceiling: lift success minimally to admit it.
        match failure {
            AtomicOrdering::SeqCst => AtomicOrdering::SeqCst,
            AtomicOrdering::Acquire => match self {
                AtomicOrdering::Relaxed => AtomicOrdering::Acquire,
                AtomicOrdering::Release => AtomicOrdering::AcqRel,
                other => other,
            },
            _ => self,
        }
    }

    pub fn allows_cmpxchg_failure(self, failure: AtomicOrdering) -> bool {
        if matches!(failure, AtomicOrdering::Release | AtomicOrdering::AcqRel) {
            return false;
        }

        failure.strength_rank() <= self.failure_ceiling_rank()
    }

    fn strength_rank(self) -> u8 {
        match self {
            AtomicOrdering::Relaxed => 0,
            AtomicOrdering::Release => 1,
            AtomicOrdering::Acquire => 2,
            AtomicOrdering::AcqRel => 3,
            AtomicOrdering::SeqCst => 4,
        }
    }

    fn failure_ceiling_rank(self) -> u8 {
        match self {
            AtomicOrdering::Release => AtomicOrdering::Relaxed.strength_rank(),
            AtomicOrdering::AcqRel => AtomicOrdering::Acquire.strength_rank(),
            other => other.strength_rank(),
        }
    }
}

/// Atomic read-modify-write operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AtomicRmwOp {
    /// Atomic add.
    Add,
    /// Atomic subtract.
    Sub,
    /// Atomic AND.
    And,
    /// Atomic OR.
    Or,
    /// Atomic XOR.
    Xor,
    /// Atomic exchange (swap).
    Xchg,
    /// Atomic signed maximum.
    Max,
    /// Atomic signed minimum.
    Min,
    /// Atomic unsigned maximum.
    UMax,
    /// Atomic unsigned minimum.
    UMin,
}

/// An instruction in the IR.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Instruction {
    pub opcode: Opcode,
    pub args: Vec<Value>,
    pub results: Vec<Value>,
}

impl Instruction {
    /// TV-1: compact lowering-provenance digest of this instruction.
    ///
    /// Shared by BOTH instruction selectors (x86-64 and AArch64) so the
    /// stamped [`trust_cg_ir::provenance::SourceInstDigest`] is arch-uniform
    /// and reproducible by any verifier holding the same LIR instruction:
    /// FNV-1a/64 over the opcode's `Debug` rendering (which embeds the
    /// opcode's type/width payload where the opcode structurally carries one)
    /// plus the argument/result arities (operand shape). See the
    /// LoweringProvenance schema comment in `trust_cg_ir::provenance`.
    pub fn lowering_digest(&self) -> trust_cg_ir::provenance::SourceInstDigest {
        trust_cg_ir::provenance::SourceInstDigest::compute(
            &format!("{:?}", self.opcode),
            self.args.len(),
            self.results.len(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::AtomicOrdering;

    const ALL: [AtomicOrdering; 5] = [
        AtomicOrdering::Relaxed,
        AtomicOrdering::Acquire,
        AtomicOrdering::Release,
        AtomicOrdering::AcqRel,
        AtomicOrdering::SeqCst,
    ];

    /// THE rule (Rust/LLVM): a cmpxchg failure ordering is invalid iff it is
    /// Release or AcqRel — a failed exchange performs no store. No other
    /// constraint exists; in particular a failure ordering STRONGER than the
    /// success ordering is legal.
    #[test]
    fn cmpxchg_failure_validity_is_exactly_not_release_acqrel() {
        assert!(AtomicOrdering::Relaxed.is_valid_cmpxchg_failure());
        assert!(AtomicOrdering::Acquire.is_valid_cmpxchg_failure());
        assert!(AtomicOrdering::SeqCst.is_valid_cmpxchg_failure());
        assert!(!AtomicOrdering::Release.is_valid_cmpxchg_failure());
        assert!(!AtomicOrdering::AcqRel.is_valid_cmpxchg_failure());
    }

    /// For every legal (success, failure) pair, lifting yields a success
    /// ordering that (a) covers the failure ordering under the ISel
    /// `failure <= success` opcode assumption and (b) is never weaker than
    /// the requested success ordering.
    #[test]
    fn cmpxchg_lift_covers_failure_and_never_weakens() {
        for success in ALL {
            for failure in ALL {
                if !failure.is_valid_cmpxchg_failure() {
                    continue;
                }
                let lifted = success.lift_for_cmpxchg_failure(failure);
                assert!(
                    lifted.allows_cmpxchg_failure(failure),
                    "lift({success:?}, {failure:?}) = {lifted:?} does not cover the failure side"
                );
                // Already-covering success orderings are untouched.
                if success.allows_cmpxchg_failure(failure) {
                    assert_eq!(lifted, success, "covering pair must not be lifted");
                }
            }
        }
    }

    /// Pin the exact lift table for the stronger-failure pairs (the
    /// std-mutex/rwlock shapes).
    #[test]
    fn cmpxchg_lift_table_for_stronger_failure() {
        use AtomicOrdering::*;
        assert_eq!(Relaxed.lift_for_cmpxchg_failure(Acquire), Acquire);
        assert_eq!(Release.lift_for_cmpxchg_failure(Acquire), AcqRel);
        assert_eq!(Relaxed.lift_for_cmpxchg_failure(SeqCst), SeqCst);
        assert_eq!(Acquire.lift_for_cmpxchg_failure(SeqCst), SeqCst);
        assert_eq!(Release.lift_for_cmpxchg_failure(SeqCst), SeqCst);
        assert_eq!(AcqRel.lift_for_cmpxchg_failure(SeqCst), SeqCst);
    }
}
