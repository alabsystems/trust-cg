// trust-cg-verify/x86_64_semantics.rs - x86-64 instruction semantics as SMT formulas
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Encodes x86-64 instruction semantics as bitvector SMT expressions.
// Each instruction maps to a pure function from input bitvectors to output
// bitvectors, modeling the instruction's effect on destination registers.
//
// Key difference from AArch64: x86-64 is a two-operand ISA where the
// destination is typically the same as the first source (dst = dst op src).
// However, for verification purposes, we model the semantics as pure
// functions from inputs to outputs, abstracting away the destructive update.
//
// Reference: Intel 64 and IA-32 Architectures Software Developer's Manual
// Reference: designs/2026-04-13-verification-architecture.md

//! x86-64 instruction semantics encoded as [`SmtExpr`] bitvector formulas.
//!
//! Key difference from AArch64: x86-64 division uses implicit RDX:RAX
//! register pair. For verification, we model the quotient result (RAX)
//! as a simple division operation since the trust_ir division semantic is
//! also a simple division. The RDX:RAX widening is an ABI detail that
//! doesn't affect the semantic equivalence of the quotient.

use crate::smt::SmtExpr;
use trust_cg_ir::X86CondCode;
use trust_cg_lower::X86FloatCmpStrategy;

/// Operand size for x86-64 instructions.
///
/// Maps to the REX.W prefix and operand-size override behavior.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum X86OperandSize {
    /// 32-bit operand (no REX.W prefix, default in 64-bit mode for most insns)
    S32,
    /// 64-bit operand (REX.W prefix)
    S64,
}

/// Width in bits for an X86OperandSize.
pub fn x86_operand_size_bits(size: X86OperandSize) -> u32 {
    match size {
        X86OperandSize::S32 => 32,
        X86OperandSize::S64 => 64,
    }
}

// ---------------------------------------------------------------------------
// Integer arithmetic instruction semantics
// ---------------------------------------------------------------------------

/// Encode `ADD r/m64, r64` or `ADD r/m32, r32` -- register-register add.
///
/// Semantics: `dst = src1 + src2` (wrapping).
/// Reference: Intel SDM Vol 2A, ADD instruction.
pub fn encode_add_rr(_size: X86OperandSize, src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    src1.bvadd(src2)
}

/// Encode `SUB r/m64, r64` or `SUB r/m32, r32` -- register-register subtract.
///
/// Semantics: `dst = src1 - src2` (wrapping).
/// Reference: Intel SDM Vol 2B, SUB instruction.
pub fn encode_sub_rr(_size: X86OperandSize, src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    src1.bvsub(src2)
}

// ---------------------------------------------------------------------------
// 128-bit add/sub via the ADD+ADC / SUB+SBB carry-chain idiom.
//
// The x86-64 backend carries an i128 value as a (lo, hi) GPR pair and lowers a
// 128-bit add to `ADD lo; ADC hi` and a 128-bit sub to `SUB lo; SBB hi`. The
// composition proofs (`x86_64_lowering_proofs::proof_x86_iadd_i128_add_adc` /
// `proof_x86_isub_i128_sub_sbb`) model the FULL two-instruction sequence as a
// single 128-bit value and check it against the trust_ir 128-bit `bvadd`/`bvsub`.
// The carry/borrow flag is modeled FAITHFULLY from the 65-bit extended add/sub
// (NOT assumed), so a wrong carry derivation refutes the obligation.
//
// This complements `proof_x86_adc_i128_hi` / `proof_x86_sbb_i128_hi`, which
// certify only the high-limb ADC/SBB in isolation; the helpers below certify the
// WHOLE i128 value (both halves + the carry/borrow that crosses the 64-bit
// boundary between them).
// ---------------------------------------------------------------------------

/// Carry-out (1-bit) of the unsigned 64-bit add `a + b`: bit 64 of the 65-bit
/// extended sum `zext65(a) + zext65(b)`.
fn add_carry_out_64(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    let a65 = a.zero_ext(1);
    let b65 = b.zero_ext(1);
    a65.bvadd(b65).extract(64, 64)
}

/// Borrow-out (1-bit) of the unsigned 64-bit sub `a - b`: bit 64 of the 65-bit
/// extended difference `zext65(a) - zext65(b)` (x86 SUB sets CF=1 iff a <u b).
fn sub_borrow_out_64(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    let a65 = a.zero_ext(1);
    let b65 = b.zero_ext(1);
    a65.bvsub(b65).extract(64, 64)
}

/// Encode the 128-bit result of `ADD dst_lo, a_lo, b_lo; ADC dst_hi, a_hi, b_hi`.
///
/// `dst_lo = a_lo + b_lo` (64-bit wrap), setting CF to the unsigned carry-out;
/// `dst_hi = a_hi + b_hi + CF` (64-bit wrap). The 128-bit value is
/// `concat(dst_hi, dst_lo)`. The carry CF is derived from the 65-bit extended
/// low-half add, exactly as the hardware computes it.
pub fn encode_add_adc_i128(a_lo: SmtExpr, a_hi: SmtExpr, b_lo: SmtExpr, b_hi: SmtExpr) -> SmtExpr {
    let dst_lo = a_lo.clone().bvadd(b_lo.clone());
    let cf = add_carry_out_64(a_lo, b_lo); // 1-bit carry
    let cf64 = cf.zero_ext(63); // widen CF to 64 bits
    let dst_hi = a_hi.bvadd(b_hi).bvadd(cf64);
    dst_hi.concat(dst_lo) // hi in upper 64, lo in lower 64
}

/// Encode the 128-bit result of `SUB dst_lo, a_lo, b_lo; SBB dst_hi, a_hi, b_hi`.
///
/// `dst_lo = a_lo - b_lo` (64-bit wrap), setting CF to the unsigned borrow-out;
/// `dst_hi = a_hi - b_hi - CF` (64-bit wrap). The 128-bit value is
/// `concat(dst_hi, dst_lo)`. The borrow CF is derived from the 65-bit extended
/// low-half subtraction, exactly as the hardware computes it.
pub fn encode_sub_sbb_i128(a_lo: SmtExpr, a_hi: SmtExpr, b_lo: SmtExpr, b_hi: SmtExpr) -> SmtExpr {
    let dst_lo = a_lo.clone().bvsub(b_lo.clone());
    let cf = sub_borrow_out_64(a_lo, b_lo); // 1-bit borrow
    let cf64 = cf.zero_ext(63);
    let dst_hi = a_hi.bvsub(b_hi).bvsub(cf64);
    dst_hi.concat(dst_lo)
}

/// Encode `IMUL r64, r/m64` -- two-operand signed multiply.
///
/// Semantics: `dst = src1 * src2` (wrapping, lower bits).
/// The two-operand IMUL form stores the lower half of the product in dst,
/// which is equivalent to wrapping multiplication.
/// Reference: Intel SDM Vol 2A, IMUL instruction.
pub fn encode_imul_rr(_size: X86OperandSize, src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    src1.bvmul(src2)
}

/// Encode the full `2N`-bit unsigned product of one-operand `MUL r/m`.
///
/// Semantics: `MUL src` computes `RDX:RAX := RAX * src` as an UNSIGNED widening
/// multiply. For an `N`-bit operand the result is the `2N`-bit product, with the
/// low `N` bits in RAX (the wrapped product) and the high `N` bits in RDX. CF/OF
/// are set iff the high half (RDX) is nonzero — i.e. the product did not fit in
/// `N` bits. Modeled as the zero-extended `2N`-bit product
/// `zext(a) *_2N zext(src)`.
///
/// Reference: Intel SDM Vol 2A, MUL instruction.
pub fn encode_mul_full(acc: SmtExpr, src: SmtExpr) -> SmtExpr {
    let width = acc.bv_width();
    let a = acc.zero_ext(width);
    let b = src.zero_ext(width);
    a.bvmul(b)
}

/// Low `N` bits of `MUL` (the RAX result): the wrapped unsigned product.
pub fn encode_mul_low(acc: SmtExpr, src: SmtExpr) -> SmtExpr {
    let width = acc.bv_width();
    encode_mul_full(acc, src).extract(width - 1, 0)
}

/// High `N` bits of `MUL` (the RDX result): the overflow half.
pub fn encode_mul_high(acc: SmtExpr, src: SmtExpr) -> SmtExpr {
    let width = acc.bv_width();
    encode_mul_full(acc, src).extract(2 * width - 1, width)
}

/// Encode `IDIV r/m64` -- signed divide (quotient).
///
/// On x86-64, IDIV divides RDX:RAX by the source operand. The quotient
/// goes to RAX and the remainder to RDX. For verification of trust_ir Sdiv,
/// we model only the quotient (RAX result).
///
/// Semantics: `RAX = (RDX:RAX) /s src` (truncation toward zero).
/// Since trust_ir Sdiv operates on single-width values (not double-width),
/// and the ISel zeros RDX (via CDQ/CQO sign-extension), the effective
/// semantic is: `dst = src1 /s src2`.
///
/// Precondition: `src2 != 0` (division by zero raises #DE).
/// Reference: Intel SDM Vol 2A, IDIV instruction.
pub fn encode_idiv_quotient(_size: X86OperandSize, src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    src1.bvsdiv(src2)
}

/// Encode `IDIV r/m64` -- signed divide (remainder).
///
/// The x86-64 remainder result is materialized from RDX/EDX. trust_ir signed
/// remainder is encoded as `a - (a /s b) * b`, matching truncation toward zero.
pub fn encode_idiv_remainder(_size: X86OperandSize, src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    let quotient = src1.clone().bvsdiv(src2.clone());
    src1.bvsub(quotient.bvmul(src2))
}

/// Encode `DIV r/m64` -- unsigned divide (quotient).
///
/// Similar to IDIV but unsigned. The quotient goes to RAX.
///
/// Semantics: `dst = src1 /u src2`.
/// Precondition: `src2 != 0` (division by zero raises #DE).
/// Reference: Intel SDM Vol 2A, DIV instruction.
pub fn encode_div_quotient(_size: X86OperandSize, src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    src1.bvudiv(src2)
}

/// Encode `DIV r/m64` -- unsigned divide (remainder).
///
/// The x86-64 remainder result is materialized from RDX/EDX.
pub fn encode_div_remainder(_size: X86OperandSize, src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    let quotient = src1.clone().bvudiv(src2.clone());
    src1.bvsub(quotient.bvmul(src2))
}

/// Encode `NEG r/m64` -- two's complement negate.
///
/// Semantics: `dst = 0 - src` (two's complement negation).
/// Reference: Intel SDM Vol 2B, NEG instruction.
pub fn encode_neg(_size: X86OperandSize, src: SmtExpr) -> SmtExpr {
    src.bvneg()
}

// ---------------------------------------------------------------------------
// Bitwise instruction semantics
// ---------------------------------------------------------------------------

/// Encode `AND r/m64, r64` -- bitwise AND.
///
/// Semantics: `dst = src1 & src2`.
/// Reference: Intel SDM Vol 2A, AND instruction.
pub fn encode_and_rr(_size: X86OperandSize, src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    src1.bvand(src2)
}

/// Encode `OR r/m64, r64` -- bitwise OR.
///
/// Semantics: `dst = src1 | src2`.
/// Reference: Intel SDM Vol 2B, OR instruction.
pub fn encode_or_rr(_size: X86OperandSize, src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    src1.bvor(src2)
}

/// Encode `XOR r/m64, r64` -- bitwise XOR.
///
/// Semantics: `dst = src1 ^ src2`.
/// Reference: Intel SDM Vol 2B, XOR instruction.
pub fn encode_xor_rr(_size: X86OperandSize, src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    src1.bvxor(src2)
}

/// Encode `NOT r/m64` -- bitwise complement.
///
/// Semantics: `dst = ~src` (one's complement).
/// Reference: Intel SDM Vol 2B, NOT instruction.
pub fn encode_not(_size: X86OperandSize, src: SmtExpr) -> SmtExpr {
    let width = src.bv_width();
    let all_ones = SmtExpr::bv_const(crate::smt::mask(u64::MAX, width), width);
    src.bvxor(all_ones)
}

// ---------------------------------------------------------------------------
// Atomic memory instruction semantics
// ---------------------------------------------------------------------------

/// Operation selector for the x86 `AtomicRmwCasLoop*` pseudo family.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum X86AtomicRmwCasLoopOp {
    Add,
    Sub,
    And,
    Or,
    Xor,
    Xchg,
    Max,
    Min,
    UMax,
    UMin,
}

/// Encode the new value computed by an x86 atomic RMW CAS retry loop.
///
/// The lowered loop copies the loaded accumulator into a scratch register,
/// applies the selected operation against the source operand, then retries a
/// locked `CMPXCHG` until memory still contains the accumulator value.
pub fn encode_atomic_rmw_cas_loop_new_value(
    op: X86AtomicRmwCasLoopOp,
    old: SmtExpr,
    operand: SmtExpr,
) -> SmtExpr {
    match op {
        X86AtomicRmwCasLoopOp::Add => old.bvadd(operand),
        X86AtomicRmwCasLoopOp::Sub => old.bvsub(operand),
        X86AtomicRmwCasLoopOp::And => old.bvand(operand),
        X86AtomicRmwCasLoopOp::Or => old.bvor(operand),
        X86AtomicRmwCasLoopOp::Xor => old.bvxor(operand),
        X86AtomicRmwCasLoopOp::Xchg => operand,
        X86AtomicRmwCasLoopOp::Max => {
            SmtExpr::ite(old.clone().bvslt(operand.clone()), operand, old)
        }
        X86AtomicRmwCasLoopOp::Min => {
            SmtExpr::ite(old.clone().bvsgt(operand.clone()), operand, old)
        }
        X86AtomicRmwCasLoopOp::UMax => {
            SmtExpr::ite(old.clone().bvult(operand.clone()), operand, old)
        }
        X86AtomicRmwCasLoopOp::UMin => {
            SmtExpr::ite(old.clone().bvugt(operand.clone()), operand, old)
        }
    }
}

/// Encode x86 `AtomicRmwCasLoop{8,16,32,64}` data-flow semantics.
///
/// In the single-threaded proof model, the successful locked `CMPXCHG` path is:
/// `old = mem[addr]`, `mem[addr] = old OP operand`, and the returned value is
/// `old`. Intervening failed CAS iterations only reload a newer old value and
/// retry, so the successful iteration has the same atomic RMW relation.
pub fn encode_atomic_rmw_cas_loop(
    mem: &SmtExpr,
    addr: &SmtExpr,
    operand: &SmtExpr,
    size_bytes: u32,
    op: X86AtomicRmwCasLoopOp,
) -> (SmtExpr, SmtExpr) {
    assert!(
        size_bytes == 1 || size_bytes == 2 || size_bytes == 4 || size_bytes == 8,
        "atomic RMW size must be 1, 2, 4, or 8 bytes"
    );

    let old = crate::memory_proofs::encode_load_le(mem, addr, size_bytes);
    let new_value = encode_atomic_rmw_cas_loop_new_value(op, old.clone(), operand.clone());
    let mem_after = crate::memory_proofs::encode_store_le(mem, addr, &new_value, size_bytes);
    (old, mem_after)
}

/// Encode x86 `LOCK CMPXCHG r/m, reg` (`F0 0F B1`) single-thread data-flow.
///
/// This is the CONDITIONAL compare-and-swap primitive that backs Rust's
/// `AtomicT::compare_exchange`. Unlike the unconditional RMW CAS loop (which
/// always writes `old OP operand`), CMPXCHG's write is GATED on an equality
/// comparison, and it produces TWO observable outputs — the returned old value
/// AND a success flag. Intel SDM (Vol. 2A, CMPXCHG):
///
/// ```text
///   old = mem[addr];                 // the current memory value
///   if (RAX == old) {                // implicit accumulator == memory
///       mem[addr] = src;             // ZF := 1 (success)
///   } else {
///       RAX = old;                   // ZF := 0 (failure); memory UNCHANGED
///   }
///   // In BOTH cases RAX holds `old` afterwards (on success it already did,
///   // since RAX == old; on failure it is loaded from memory).
/// ```
///
/// The ISel (`select_cmpxchg`) copies `expected` into RAX and `desired` into the
/// source register, emits `LOCK CMPXCHG [addr], desired`, then reads RAX into the
/// destination as the returned OLD value. The success bool is NOT taken from ZF
/// here; the adapter re-derives it as `Icmp Equal(old, expected)`, which is
/// EXACTLY the flag CMPXCHG sets (`ZF == (old == expected)`) — a proven ICMP over
/// the same values, so no ZF plumbing is needed.
///
/// Parameters model that state: `mem` seeded with the current value at `addr`,
/// the 64-bit `expected` (RAX) and `desired` (source) narrowed to the op width.
/// `size_bytes` selects the memory width (4 or 8; the ISel restricts CMPXCHG to
/// i32/i64). Returns `(ret, mem_after, success_flag)` where:
///   * `ret` is the returned old value (always `old`),
///   * `mem_after` is memory with the CONDITIONAL store applied,
///   * `success_flag` is a 1-bit `(old == expected)` predicate reified to a bv.
///
/// The conditional store and dual outputs are what make this a GENUINELY new
/// soundness primitive (not the identity fence, not the unconditional RMW). The
/// LOCK-serialization / cross-thread ordering CMPXCHG also provides is the same
/// Intel-SDM architectural axiom the atomic load/store/RMW proofs already rest
/// on — deliberately not dressed up as this SMT theorem.
pub fn encode_cmpxchg(
    mem: &SmtExpr,
    addr: &SmtExpr,
    expected: &SmtExpr,
    desired: &SmtExpr,
    size_bytes: u32,
) -> (SmtExpr, SmtExpr, SmtExpr) {
    assert!(
        size_bytes == 4 || size_bytes == 8,
        "x86 CMPXCHG (compare_exchange) size must be 4 or 8 bytes"
    );

    let width_bits = size_bytes * 8;
    let old = crate::memory_proofs::encode_load_le(mem, addr, size_bytes);
    // The equality the hardware tests: RAX(expected) == the loaded memory value.
    let is_equal = expected.clone().eq_expr(old.clone());
    // CONDITIONAL store: on equality write `desired`, otherwise leave memory as it
    // was (write `old` back — a functional no-op that keeps the same byte value).
    let new_value = SmtExpr::ite(is_equal.clone(), desired.clone(), old.clone());
    let mem_after = crate::memory_proofs::encode_store_le(mem, addr, &new_value, size_bytes);
    // RAX AFTER the instruction. On the SUCCESS branch (expected == old) RAX is
    // UNCHANGED — it still holds `expected`, which equals `old`. On the FAILURE
    // branch CMPXCHG LOADS the current memory into RAX, so RAX = `old`. Modeling
    // BOTH branches (rather than collapsing to bare `old`) mirrors the real dual
    // data path AND keeps this obligation structurally distinct from the trust-ir
    // spec's bare `old` — so it is a GENUINE theorem (a lowering that returned
    // `expected` unconditionally would refute on the failure branch), not a
    // degenerate X==X. It is nonetheless equal to `old` at every point: on
    // equality `expected == old`, on inequality the else-arm is `old`.
    let ret = SmtExpr::ite(is_equal.clone(), expected.clone(), old.clone());
    // The success flag (ZF) reified as a width-wide 0/1 bitvector so proofs can
    // compare it against the adapter's `Icmp Equal(returned_old, expected)`
    // without a separate Bool sort.
    let success_flag = SmtExpr::ite(
        is_equal,
        SmtExpr::bv_const(1, width_bits),
        SmtExpr::bv_const(0, width_bits),
    );
    (ret, mem_after, success_flag)
}

/// Encode the SINGLE-THREAD data-flow effect of `MFENCE` (`0F AE F0`).
///
/// MFENCE is a full memory-ordering barrier: it serializes the *ordering* of
/// prior against subsequent loads/stores. Ordering is a CROSS-THREAD,
/// architectural property (Intel SDM 8.2.2/8.2.5) — it is NOT expressible as a
/// single-thread data-flow relation and is trusted as an axiom, exactly like
/// the LOCK-serialization and MOV single-copy-atomicity axioms the atomic
/// load/store proofs already rest on.
///
/// What IS a genuine single-thread data-flow obligation — and what this encoder
/// models — is the DUAL fact: MFENCE writes NO architectural register and NO
/// memory location. Its transition function on the (register, memory) pair is
/// the IDENTITY. That is the property this transition must satisfy so the ISel
/// choice to leave every surrounding value untouched (and to emit MFENCE only as
/// an ordering marker) is faithful. The obligation is non-vacuous: a wrong
/// "fence" that clobbered a register or a byte of memory would violate this
/// identity and REFUTE (see `proof_x86_mfence_*_refutes`).
///
/// Returns the post-MFENCE (register, memory) pair.
pub fn encode_mfence(reg_before: &SmtExpr, mem_before: &SmtExpr) -> (SmtExpr, SmtExpr) {
    // MFENCE's register/memory transition is the identity: it neither reads nor
    // writes any GPR/XMM/flag and touches no memory byte. The barrier is purely
    // an ordering fence between memory accesses, modeled cross-thread by the SDM
    // axiom, not by any data value produced here.
    (reg_before.clone(), mem_before.clone())
}

// ---------------------------------------------------------------------------
// Shift instruction semantics
// ---------------------------------------------------------------------------

/// Encode `SHL r/m64, CL` -- logical shift left by register.
///
/// Semantics: `dst = src1 << (src2 mod width)`.
/// On x86-64, the shift amount is masked to 5 bits (mod 32) for 32-bit
/// operations and 6 bits (mod 64) for 64-bit operations.
/// Reference: Intel SDM Vol 2B, SHL instruction.
pub fn encode_shl_rr(_size: X86OperandSize, src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    src1.bvshl(src2)
}

/// Encode `ROL r/m{32,64}, imm8` -- rotate left by a constant amount.
///
/// Semantics: `dst = (src << k) | (src >>u (width - k))` for `k` in
/// `[1, width)`. Reference: Intel SDM Vol 2B, ROL/ROR.
///
/// ⚑ THE OR HALVES ARE DELIBERATELY EMITTED IN THE OPPOSITE ORDER from the
/// frontend idiom this instruction replaces (`(x << k) | (x >>u (w-k))`). The
/// two are equal because OR commutes, but they are STRUCTURALLY DISTINCT, so
/// the lowering obligation that ties them is not the vacuous `X == X` that
/// `ProofObligation::is_degenerate` exists to catch. Writing this side in the
/// "natural" order would produce a proof that discharges, passes its tests, and
/// establishes nothing — see the identical construction on the AArch64 side in
/// `lowering_proof::proof_eor_ror_shift`.
pub fn encode_rol_ri(size: X86OperandSize, src: SmtExpr, k: u32) -> SmtExpr {
    let width = x86_operand_size_bits(size);
    debug_assert!(k >= 1 && k < width, "ROL amount must be in [1, width)");
    let hi = src
        .clone()
        .bvlshr(SmtExpr::bv_const(u64::from(width - k), width));
    let lo = src.bvshl(SmtExpr::bv_const(u64::from(k), width));
    hi.bvor(lo)
}

/// The FRONTEND rotate idiom `(x << k) | (x >>u (width - k))`, in its natural
/// OR order — the shape `rotate_left(k)` lowers to before the peephole runs.
/// Paired with [`encode_rol_ri`] to state the lowering obligation.
pub fn encode_rotl_source(size: X86OperandSize, src: SmtExpr, k: u32) -> SmtExpr {
    let width = x86_operand_size_bits(size);
    debug_assert!(k >= 1 && k < width, "rotate amount must be in [1, width)");
    let lo = src.clone().bvshl(SmtExpr::bv_const(u64::from(k), width));
    let hi = src.bvlshr(SmtExpr::bv_const(u64::from(width - k), width));
    lo.bvor(hi)
}

/// Encode `SHR r/m64, CL` -- logical shift right by register.
///
/// Semantics: `dst = src1 >> (src2 mod width)` (zero-fill).
/// Reference: Intel SDM Vol 2B, SHR instruction.
pub fn encode_shr_rr(_size: X86OperandSize, src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    src1.bvlshr(src2)
}

/// Encode `SAR r/m64, CL` -- arithmetic shift right by register.
///
/// Semantics: `dst = src1 >>_s (src2 mod width)` (sign-extending).
/// Reference: Intel SDM Vol 2B, SAR instruction.
pub fn encode_sar_rr(_size: X86OperandSize, src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    src1.bvashr(src2)
}

// ---------------------------------------------------------------------------
// SHL/SHR/SAR — FAITHFUL hardware-amount-masked encoders (task #66 / #57)
// ---------------------------------------------------------------------------
//
// Operand-reconstruction (task #66, x86-64) rebuilds the machine side of a shift
// obligation from the REAL emitted opcode over shared symbols, paired with a
// LOAD-BEARING `count < width` precondition. For that precondition to be
// genuinely required (not cosmetic), the machine side must model the x86 hardware
// count mask (`count & (width - 1)`, i.e. `& 0x3F` at 64-bit and `& 0x1F` at
// 32-bit), NOT the unmasked `bvshl`/`bvlshr`/`bvashr` of [`encode_shl_rr`] /
// [`encode_shr_rr`] / [`encode_sar_rr`].
//
// Mirrors `aarch64_semantics::encode_lsl_rr_masked` / `riscv_semantics::
// encode_sll_masked` (#57): IN range the mask is the identity so the masked
// machine side agrees with the trust_ir clamp-to-0 spec side; OUT of range
// (count >= width) the masked hardware result and the clamp-to-0 spec DIVERGE, so
// the `count < width` precondition is load-bearing — strip it and a shift by
// exactly `width` REFUTES. The width is taken from the OPERAND sort
// (`count.bv_width()`), not the `X86OperandSize`, so the encoder composes at any
// bitvector width (the exhaustive reconstruction test uses i8). x86 SHL/SHR/SAR
// by `count >= width` masks `count & (width-1)` in hardware (Intel SDM: SHL/SHR
// mask CL to 5 bits at 32-bit, 6 bits at 64-bit); Rust/trust_ir shift-by->=width
// is UB, so scoping it out with the precondition is the faithful contract.

/// The x86 hardware shift-amount mask `(width - 1)` as a `width`-bit constant.
///
/// x86 SHL/SHR/SAR mask the count with the low `log2(width)` bits (`& 0x1F` at
/// 32-bit, `& 0x3F` at 64-bit); `width` is a power of two so `width - 1` is
/// exactly that low-bits mask. The width is taken from the OPERAND sort, so the
/// encoder composes at any bitvector width.
fn x86_shift_amount_mask(width: u32) -> SmtExpr {
    SmtExpr::bv_const((width as u64).wrapping_sub(1), width)
}

/// Encode `SHL r/m, CL` with the FAITHFUL x86 hardware amount mask
/// (`dst = src1 << (count & (width - 1))`). See the module note above; the masked
/// form is what makes the reconstruction `count < width` precondition load-bearing.
/// Reference: Intel SDM Vol 2B, SHL (count masked to CL[5:0] at 64-bit, CL[4:0] at 32-bit).
pub fn encode_shl_rr_masked(_size: X86OperandSize, src1: SmtExpr, count: SmtExpr) -> SmtExpr {
    let width = count.bv_width();
    src1.bvshl(count.bvand(x86_shift_amount_mask(width)))
}

/// Encode `SHR r/m, CL` with the FAITHFUL x86 hardware amount mask
/// (`dst = (unsigned)src1 >> (count & (width - 1))`, zero-fill). See
/// [`encode_shl_rr_masked`]. Reference: Intel SDM Vol 2B, SHR.
pub fn encode_shr_rr_masked(_size: X86OperandSize, src1: SmtExpr, count: SmtExpr) -> SmtExpr {
    let width = count.bv_width();
    src1.bvlshr(count.bvand(x86_shift_amount_mask(width)))
}

/// Encode `SAR r/m, CL` with the FAITHFUL x86 hardware amount mask
/// (`dst = (signed)src1 >> (count & (width - 1))`, sign-fill). See
/// [`encode_shl_rr_masked`]. Reference: Intel SDM Vol 2B, SAR.
pub fn encode_sar_rr_masked(_size: X86OperandSize, src1: SmtExpr, count: SmtExpr) -> SmtExpr {
    let width = count.bv_width();
    src1.bvashr(count.bvand(x86_shift_amount_mask(width)))
}

// ---------------------------------------------------------------------------
// SIMD integer instruction semantics
// ---------------------------------------------------------------------------

fn encode_packed_binary<F>(
    arrangement: crate::smt::VectorArrangement,
    src1: SmtExpr,
    src2: SmtExpr,
    op: F,
) -> SmtExpr
where
    F: Fn(SmtExpr, SmtExpr) -> SmtExpr,
{
    crate::smt::map_lanes_binary(&src1, &src2, arrangement, op)
}

/// Encode `PADDB xmm, xmm` -- packed byte add.
///
/// Semantics: `dst[i] = src1[i] + src2[i]` for sixteen 8-bit lanes.
/// Reference: Intel SDM Vol 2B, PADDB/PADDW/PADDD/PADDQ instructions.
pub fn encode_paddb(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    encode_packed_binary(crate::smt::VectorArrangement::B16, src1, src2, |a, b| {
        a.bvadd(b)
    })
}

/// Encode `PADDW xmm, xmm` -- packed word add.
pub fn encode_paddw(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    encode_packed_binary(crate::smt::VectorArrangement::H8, src1, src2, |a, b| {
        a.bvadd(b)
    })
}

/// Encode `PADDD xmm, xmm` -- packed dword add.
pub fn encode_paddd(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    encode_packed_binary(crate::smt::VectorArrangement::S4, src1, src2, |a, b| {
        a.bvadd(b)
    })
}

/// Encode `PADDQ xmm, xmm` -- packed qword add.
///
/// Semantics: `dst[i] = src1[i] + src2[i]` for two 64-bit lanes.
/// Reference: Intel SDM Vol 2B, PADDQ instruction.
pub fn encode_paddq(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    encode_packed_binary(crate::smt::VectorArrangement::D2, src1, src2, |a, b| {
        a.bvadd(b)
    })
}

/// Encode `PSADBW xmm, xmm` -- sum of absolute differences of unsigned bytes.
///
/// Semantics (Intel SDM Vol 2B, PSADBW): the 16 byte lanes are split into two
/// groups of 8; for each 64-bit output lane `j` in {0,1},
///   `dst.qword[j] = Σ_{i=0..8} |src1.byte[8j+i] - src2.byte[8j+i]|`
/// with each absolute difference and the running sum computed in 64 bits (a
/// group sum is ≤ 8·255 = 2040 < 2^64, so it never wraps and the upper bits of
/// each qword lane are the true zero-extended sum). This is the ONLY x86 op the
/// verifier models HORIZONTALLY (the sum crosses lanes), unlike the lane-wise
/// PADD*/PSUB* family. `|x-y|` is `ite(x >=u y, x-y, y-x)` on the zero-extended
/// (hence non-negative) byte values.
pub fn encode_psadbw(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    let mut lanes: Vec<SmtExpr> = Vec::with_capacity(2);
    for j in 0..2u32 {
        let mut acc = SmtExpr::bv_const(0, 64);
        for i in 0..8u32 {
            let byte = j * 8 + i;
            let hi = byte * 8 + 7;
            let lo = byte * 8;
            let a = src1.clone().extract(hi, lo).zero_ext(56); // 8 -> 64
            let b = src2.clone().extract(hi, lo).zero_ext(56);
            let diff = SmtExpr::ite(
                a.clone().bvuge(b.clone()),
                a.clone().bvsub(b.clone()),
                b.bvsub(a),
            );
            acc = acc.bvadd(diff);
        }
        lanes.push(acc);
    }
    // 128-bit result: high qword (lane j=1, bytes 8..16) : low qword (j=0).
    lanes[1].clone().concat(lanes[0].clone())
}

/// Encode `PSUBB xmm, xmm` -- packed byte subtract.
///
/// Semantics: `dst[i] = src1[i] - src2[i]` for sixteen 8-bit lanes.
/// Reference: Intel SDM Vol 2B, PSUBB/PSUBW/PSUBD/PSUBQ instructions.
pub fn encode_psubb(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    encode_packed_binary(crate::smt::VectorArrangement::B16, src1, src2, |a, b| {
        a.bvsub(b)
    })
}

/// Encode `PSUBW xmm, xmm` -- packed word subtract.
pub fn encode_psubw(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    encode_packed_binary(crate::smt::VectorArrangement::H8, src1, src2, |a, b| {
        a.bvsub(b)
    })
}

/// Encode `PSUBD xmm, xmm` -- packed dword subtract.
pub fn encode_psubd(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    encode_packed_binary(crate::smt::VectorArrangement::S4, src1, src2, |a, b| {
        a.bvsub(b)
    })
}

/// Encode `PSUBQ xmm, xmm` -- packed qword subtract.
///
/// Semantics: `dst[i] = src1[i] - src2[i]` for two 64-bit lanes.
/// Reference: Intel SDM Vol 2B, PSUBQ instruction.
pub fn encode_psubq(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    encode_packed_binary(crate::smt::VectorArrangement::D2, src1, src2, |a, b| {
        a.bvsub(b)
    })
}

/// Encode `PMULLD xmm, xmm` -- packed dword low multiply.
///
/// Semantics: each 32-bit lane receives the low 32 bits of the product.
/// Signed and unsigned low-half multiplication agree modulo 2^32.
/// Reference: Intel SDM Vol 2B, PMULLD instruction.
pub fn encode_pmulld(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    encode_packed_binary(crate::smt::VectorArrangement::S4, src1, src2, |a, b| {
        a.bvmul(b)
    })
}

/// Encode `PMULLW xmm, xmm` -- packed word low multiply.
///
/// Semantics: each 16-bit lane receives the low 16 bits of the product.
/// Signed and unsigned low-half multiplication agree modulo 2^16.
/// Reference: Intel SDM Vol 2B, PMULLW instruction.
pub fn encode_pmullw(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    encode_packed_binary(crate::smt::VectorArrangement::H8, src1, src2, |a, b| {
        a.bvmul(b)
    })
}

/// Encode `PMULUDQ xmm, xmm` -- packed unsigned dword multiply to qword products.
///
/// Semantics (Intel SDM Vol 2B, PMULUDQ, 128-bit legacy SSE version):
///   `DEST[63:0]   = ZeroExtend64(SRC1[31:0])  * ZeroExtend64(SRC2[31:0])`
///   `DEST[127:64] = ZeroExtend64(SRC1[95:64]) * ZeroExtend64(SRC2[95:64])`
///
/// Modeled structurally from the SDM: extract the EVEN dwords (S4 lanes 0 and
/// 2), zero-extend each to 64 bits, and take the full 64-bit products. This is
/// deliberately a DIFFERENT construction from the trust-ir-side spec (a D2
/// `map_lanes` of `lo32(a) * lo32(b)` masking within the qword lanes) so that
/// their SMT equivalence is a genuine theorem: an odd-dword extract, a
/// sign-extending model, or a low-half-only product all REFUTE.
pub fn encode_pmuludq(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    let lanes: Vec<SmtExpr> = [0u32, 2u32]
        .iter()
        .map(|&dword_lane| {
            let a = crate::smt::lane_extract(&src1, crate::smt::VectorArrangement::S4, dword_lane)
                .zero_ext(32);
            let b = crate::smt::lane_extract(&src2, crate::smt::VectorArrangement::S4, dword_lane)
                .zero_ext(32);
            a.bvmul(b)
        })
        .collect();
    crate::smt::concat_lanes(&lanes, crate::smt::VectorArrangement::D2)
}

fn packed_lane_mask(cond: SmtExpr, lane_bits: u32) -> SmtExpr {
    SmtExpr::ite(
        cond,
        SmtExpr::bv_const(crate::smt::mask(u64::MAX, lane_bits), lane_bits),
        SmtExpr::bv_const(0, lane_bits),
    )
}

fn v128_all_ones() -> SmtExpr {
    let lanes = vec![SmtExpr::bv_const(u8::MAX.into(), 8); 16];
    crate::smt::concat_lanes(&lanes, crate::smt::VectorArrangement::B16)
}

fn encode_packed_eq(
    arrangement: crate::smt::VectorArrangement,
    src1: SmtExpr,
    src2: SmtExpr,
) -> SmtExpr {
    let lane_bits = arrangement.lane_bits();
    crate::smt::map_lanes_binary(&src1, &src2, arrangement, |a, b| {
        packed_lane_mask(a.eq_expr(b), lane_bits)
    })
}

fn encode_packed_signed_gt(
    arrangement: crate::smt::VectorArrangement,
    src1: SmtExpr,
    src2: SmtExpr,
) -> SmtExpr {
    let lane_bits = arrangement.lane_bits();
    crate::smt::map_lanes_binary(&src1, &src2, arrangement, |a, b| {
        packed_lane_mask(a.bvsgt(b), lane_bits)
    })
}

/// Encode `PCMPEQB xmm, xmm` -- packed byte equality compare.
///
/// Semantics: each 8-bit lane is all-ones when equal, otherwise all-zero.
/// Reference: Intel SDM Vol 2B, PCMPEQB/PCMPEQW/PCMPEQD instructions.
pub fn encode_pcmpeqb(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    encode_packed_eq(crate::smt::VectorArrangement::B16, src1, src2)
}

/// Encode `PCMPEQW xmm, xmm` -- packed word equality compare.
pub fn encode_pcmpeqw(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    encode_packed_eq(crate::smt::VectorArrangement::H8, src1, src2)
}

/// Encode `PCMPEQD xmm, xmm` -- packed dword equality compare.
pub fn encode_pcmpeqd(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    encode_packed_eq(crate::smt::VectorArrangement::S4, src1, src2)
}

/// Encode `PCMPEQQ xmm, xmm` -- packed qword equality compare.
pub fn encode_pcmpeqq(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    encode_packed_eq(crate::smt::VectorArrangement::D2, src1, src2)
}

/// Encode `PCMPGTB xmm, xmm` -- packed signed byte greater-than compare.
///
/// Semantics: each lane is all-ones when `src1[i] >s src2[i]`, otherwise
/// all-zero. Reference: Intel SDM Vol 2B, PCMPGTB/PCMPGTW/PCMPGTD.
pub fn encode_pcmpgtb(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    encode_packed_signed_gt(crate::smt::VectorArrangement::B16, src1, src2)
}

/// Encode `PCMPGTW xmm, xmm` -- packed signed word greater-than compare.
pub fn encode_pcmpgtw(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    encode_packed_signed_gt(crate::smt::VectorArrangement::H8, src1, src2)
}

/// Encode `PCMPGTD xmm, xmm` -- packed signed dword greater-than compare.
pub fn encode_pcmpgtd(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    encode_packed_signed_gt(crate::smt::VectorArrangement::S4, src1, src2)
}

/// Encode `PCMPGTQ xmm, xmm` -- packed signed qword greater-than compare.
pub fn encode_pcmpgtq(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    encode_packed_signed_gt(crate::smt::VectorArrangement::D2, src1, src2)
}

/// Encode `PAND xmm, xmm` -- packed bitwise AND.
pub fn encode_pand(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    src1.bvand(src2)
}

/// Encode `PANDN xmm, xmm` -- packed bitwise AND NOT.
///
/// Intel two-operand semantics are `dst = (~dst) & src`.
pub fn encode_pandn(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    src1.bvxor(v128_all_ones()).bvand(src2)
}

/// Encode `POR xmm, xmm` -- packed bitwise OR.
pub fn encode_por(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    src1.bvor(src2)
}

/// Encode `PXOR xmm, xmm` -- packed bitwise XOR.
pub fn encode_pxor(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    src1.bvxor(src2)
}

/// Encode `PMOVMSKB r32, xmm` -- extract packed byte sign bits.
///
/// Semantics: result bit `i` is bit 7 of byte lane `i`; result bits 16..31
/// are zero.
pub fn encode_pmovmskb(src: SmtExpr) -> SmtExpr {
    let bits: Vec<SmtExpr> = (0..16)
        .map(|i| {
            crate::smt::lane_extract(&src, crate::smt::VectorArrangement::B16, i).extract(7, 7)
        })
        .collect();
    let mut packed = bits[0].clone();
    for bit in &bits[1..] {
        packed = bit.clone().concat(packed);
    }
    SmtExpr::bv_const(0, 16).concat(packed)
}

/// Encode `PSHUFD xmm, xmm, imm8` -- packed dword shuffle.
///
/// The immediate selects the source dword for each destination lane using
/// two bits per lane: bits 1:0 for lane 0, bits 3:2 for lane 1, etc.
/// Reference: Intel SDM Vol 2B, PSHUFD instruction.
pub fn encode_pshufd(src: SmtExpr, imm: u8) -> SmtExpr {
    let lanes: Vec<SmtExpr> = (0..4_u32)
        .map(|dst_lane| {
            let src_lane = (u32::from(imm) >> (dst_lane * 2)) & 0b11;
            crate::smt::lane_extract(&src, crate::smt::VectorArrangement::S4, src_lane)
        })
        .collect();
    crate::smt::concat_lanes(&lanes, crate::smt::VectorArrangement::S4)
}

fn encode_punpckbw(src1: SmtExpr, src2: SmtExpr, start_lane: u32) -> SmtExpr {
    let lanes: Vec<SmtExpr> = (start_lane..start_lane + 8)
        .flat_map(|lane| {
            [
                crate::smt::lane_extract(&src1, crate::smt::VectorArrangement::B16, lane),
                crate::smt::lane_extract(&src2, crate::smt::VectorArrangement::B16, lane),
            ]
        })
        .collect();
    crate::smt::concat_lanes(&lanes, crate::smt::VectorArrangement::B16)
}

/// Encode `PUNPCKLBW xmm, xmm` -- unpack/interleave low packed bytes.
///
/// For 128-bit operands this consumes byte lanes 0..7 from each source and
/// produces byte lanes `[src1.0, src2.0, ..., src1.7, src2.7]`.
/// Reference: Intel SDM Vol 2B, PUNPCKLBW instruction.
pub fn encode_punpcklbw(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    encode_punpckbw(src1, src2, 0)
}

/// Encode `PUNPCKHBW xmm, xmm` -- unpack/interleave high packed bytes.
///
/// For 128-bit operands this consumes byte lanes 8..15 from each source and
/// produces byte lanes `[src1.8, src2.8, ..., src1.15, src2.15]`.
/// Reference: Intel SDM Vol 2B, PUNPCKHBW instruction.
pub fn encode_punpckhbw(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    encode_punpckbw(src1, src2, 8)
}

/// Encode `PACKUSWB xmm, xmm` -- pack signed words to unsigned bytes.
///
/// For 128-bit operands this saturates the eight signed 16-bit word lanes
/// from `src1` followed by the eight word lanes from `src2` into unsigned
/// byte lanes.
/// Reference: Intel SDM Vol 2B, PACKUSWB instruction.
pub fn encode_packuswb(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    let zero = SmtExpr::bv_const(0, 16);
    let max_u8 = SmtExpr::bv_const(u8::MAX.into(), 16);
    let lanes: Vec<SmtExpr> =
        (0..8_u32)
            .map(|lane| crate::smt::lane_extract(&src1, crate::smt::VectorArrangement::H8, lane))
            .chain((0..8_u32).map(|lane| {
                crate::smt::lane_extract(&src2, crate::smt::VectorArrangement::H8, lane)
            }))
            .map(|word| {
                let clamped = SmtExpr::ite(
                    word.clone().bvslt(zero.clone()),
                    zero.clone(),
                    SmtExpr::ite(word.clone().bvsgt(max_u8.clone()), max_u8.clone(), word),
                );
                clamped.extract(7, 0)
            })
            .collect();
    crate::smt::concat_lanes(&lanes, crate::smt::VectorArrangement::B16)
}

/// Encode `PUNPCKLDQ xmm, xmm` -- unpack/interleave low packed dwords.
///
/// For 128-bit operands this consumes the low two dwords from each source and
/// produces lanes `[src1.0, src2.0, src1.1, src2.1]`.
/// Reference: Intel SDM Vol 2B, PUNPCKLDQ instruction.
pub fn encode_punpckldq(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    let lanes = [
        crate::smt::lane_extract(&src1, crate::smt::VectorArrangement::S4, 0),
        crate::smt::lane_extract(&src2, crate::smt::VectorArrangement::S4, 0),
        crate::smt::lane_extract(&src1, crate::smt::VectorArrangement::S4, 1),
        crate::smt::lane_extract(&src2, crate::smt::VectorArrangement::S4, 1),
    ];
    crate::smt::concat_lanes(&lanes, crate::smt::VectorArrangement::S4)
}

/// Encode `PUNPCKLQDQ xmm, xmm` -- unpack/interleave low packed qwords.
///
/// For 128-bit operands this produces qword lanes `[src1.0, src2.0]`.
/// Reference: Intel SDM Vol 2B, PUNPCKLQDQ instruction.
pub fn encode_punpcklqdq(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    let lanes = [
        crate::smt::lane_extract(&src1, crate::smt::VectorArrangement::D2, 0),
        crate::smt::lane_extract(&src2, crate::smt::VectorArrangement::D2, 0),
    ];
    crate::smt::concat_lanes(&lanes, crate::smt::VectorArrangement::D2)
}

/// Encode `PBLENDVB xmm, xmm` -- byte-wise select with implicit XMM0 mask.
///
/// `false_val` models the old destination, `true_val` models the explicit
/// source operand, and `mask` models XMM0. Each byte is selected from
/// `true_val` when the corresponding mask byte's high bit is set; otherwise
/// it is selected from `false_val`.
pub fn encode_pblendvb(false_val: SmtExpr, true_val: SmtExpr, mask: SmtExpr) -> SmtExpr {
    let lanes: Vec<SmtExpr> = (0..16)
        .map(|i| {
            let false_lane =
                crate::smt::lane_extract(&false_val, crate::smt::VectorArrangement::B16, i);
            let true_lane =
                crate::smt::lane_extract(&true_val, crate::smt::VectorArrangement::B16, i);
            let mask_lane = crate::smt::lane_extract(&mask, crate::smt::VectorArrangement::B16, i);
            let take_true = mask_lane.extract(7, 7).eq_expr(SmtExpr::bv_const(1, 1));
            SmtExpr::ite(take_true, true_lane, false_lane)
        })
        .collect();
    crate::smt::concat_lanes(&lanes, crate::smt::VectorArrangement::B16)
}

/// Encode the generic SSE2 expansion of `V128BoolSelect`.
///
/// Sequence: `(mask & true_val) | (~mask & false_val)`.
pub fn encode_v128_sse2_bool_select(
    mask: SmtExpr,
    true_val: SmtExpr,
    false_val: SmtExpr,
) -> SmtExpr {
    let true_masked = encode_pand(mask.clone(), true_val);
    let false_masked = encode_pandn(mask, false_val);
    encode_por(true_masked, false_masked)
}

fn zext_shift_count_to_i32(count: SmtExpr) -> SmtExpr {
    let width = count.bv_width();
    assert!(
        width <= 32,
        "packed dword shift count must be at most 32 bits"
    );
    if width == 32 {
        count
    } else {
        count.zero_ext(32 - width)
    }
}

fn encode_v4i32_packed_imm_shift(
    src: SmtExpr,
    count: SmtExpr,
    shift: fn(SmtExpr, SmtExpr) -> SmtExpr,
) -> SmtExpr {
    let count = zext_shift_count_to_i32(count);
    crate::smt::map_lanes_unary(&src, crate::smt::VectorArrangement::S4, |lane| {
        shift(lane, count.clone())
    })
}

/// Encode `PSLLD xmm, imm8` -- packed dword logical shift left.
///
/// Semantics: each 32-bit lane shifts left by the same immediate count.
/// Counts greater than 31 produce zero in each lane.
/// Reference: Intel SDM Vol 2B, PSLLD instruction.
pub fn encode_pslld_imm(src: SmtExpr, count: SmtExpr) -> SmtExpr {
    encode_v4i32_packed_imm_shift(src, count, |lane, count| lane.bvshl(count))
}

/// Encode `PSRLD xmm, imm8` -- packed dword logical shift right.
///
/// Semantics: each 32-bit lane shifts right by the same immediate count with
/// zero fill. Counts greater than 31 produce zero in each lane.
/// Reference: Intel SDM Vol 2B, PSRLD instruction.
pub fn encode_psrld_imm(src: SmtExpr, count: SmtExpr) -> SmtExpr {
    encode_v4i32_packed_imm_shift(src, count, |lane, count| lane.bvlshr(count))
}

/// Encode `PSRAD xmm, imm8` -- packed dword arithmetic shift right.
///
/// Semantics: each 32-bit lane shifts right by the same immediate count with
/// sign extension. Counts greater than 31 fill each lane with its sign bit.
/// Reference: Intel SDM Vol 2B, PSRAD instruction.
pub fn encode_psrad_imm(src: SmtExpr, count: SmtExpr) -> SmtExpr {
    encode_v4i32_packed_imm_shift(src, count, |lane, count| lane.bvashr(count))
}

fn zext_shift_count_to_i64(count: SmtExpr) -> SmtExpr {
    let width = count.bv_width();
    assert!(
        width <= 64,
        "packed qword shift count must be at most 64 bits"
    );
    if width == 64 {
        count
    } else {
        count.zero_ext(64 - width)
    }
}

fn encode_v2i64_packed_imm_shift(
    src: SmtExpr,
    count: SmtExpr,
    shift: fn(SmtExpr, SmtExpr) -> SmtExpr,
) -> SmtExpr {
    let count = zext_shift_count_to_i64(count);
    crate::smt::map_lanes_unary(&src, crate::smt::VectorArrangement::D2, |lane| {
        shift(lane, count.clone())
    })
}

/// Encode `PSLLQ xmm, imm8` -- packed qword logical shift left.
///
/// Semantics: each 64-bit lane shifts left by the same immediate count.
/// Counts greater than 63 produce zero in each lane.
/// Reference: Intel SDM Vol 2B, PSLLQ instruction.
pub fn encode_psllq_imm(src: SmtExpr, count: SmtExpr) -> SmtExpr {
    encode_v2i64_packed_imm_shift(src, count, |lane, count| lane.bvshl(count))
}

/// Encode `PSRLQ xmm, imm8` -- packed qword logical shift right.
///
/// Semantics: each 64-bit lane shifts right by the same immediate count with
/// zero fill. Counts greater than 63 produce zero in each lane.
/// Reference: Intel SDM Vol 2B, PSRLQ instruction.
pub fn encode_psrlq_imm(src: SmtExpr, count: SmtExpr) -> SmtExpr {
    encode_v2i64_packed_imm_shift(src, count, |lane, count| lane.bvlshr(count))
}

/// Encode x86-64's scalarized `<4 x i32>` lane-wise shift lowering.
///
/// The current x86-64 lowering extracts each i32 lane from both V128 operands,
/// applies a scalar GPR shift, then reassembles the four shifted lanes with
/// MOVD/PUNPCKLDQ/PUNPCKLQDQ. This helper models that dataflow directly.
pub fn encode_v4i32_scalarized_shift(
    lhs: SmtExpr,
    rhs: SmtExpr,
    shift: fn(X86OperandSize, SmtExpr, SmtExpr) -> SmtExpr,
) -> SmtExpr {
    let lanes: Vec<SmtExpr> = (0..4)
        .map(|lane| {
            let lhs_lane = crate::smt::lane_extract(&lhs, crate::smt::VectorArrangement::S4, lane);
            let rhs_lane = crate::smt::lane_extract(&rhs, crate::smt::VectorArrangement::S4, lane);
            shift(X86OperandSize::S32, lhs_lane, rhs_lane)
        })
        .collect();
    crate::smt::concat_lanes(&lanes, crate::smt::VectorArrangement::S4)
}

// ---------------------------------------------------------------------------
// Move instruction semantics
// ---------------------------------------------------------------------------

/// Encode `MOV r64, r64` or `MOV r32, r32` -- register-to-register move.
///
/// Semantics: `dst = src` (identity).
/// Reference: Intel SDM Vol 2B, MOV instruction.
pub fn encode_mov_rr(_size: X86OperandSize, src: SmtExpr) -> SmtExpr {
    src
}

/// Encode `MOVD xmm, r/m32` -- move 32 GPR bits into the low XMM lane.
///
/// Semantics: bits [31:0] of the destination XMM register are `src[31:0]`;
/// upper XMM bits are cleared. The verifier's scalar-FP bitcast proofs compare
/// the low lane against the source bits.
/// Reference: Intel SDM Vol 2B, MOVD/MOVQ instruction.
pub fn encode_movd_to_xmm(src: SmtExpr) -> SmtExpr {
    src.extract(31, 0).zero_ext(96)
}

/// Encode `MOVD r/m32, xmm` -- move the low 32 XMM bits to a GPR.
///
/// Semantics: `dst = src[31:0]`.
/// Reference: Intel SDM Vol 2B, MOVD/MOVQ instruction.
pub fn encode_movd_from_xmm(src: SmtExpr) -> SmtExpr {
    src.extract(31, 0)
}

/// Encode `MOVQ xmm, r/m64` -- move 64 GPR bits into the low XMM lane.
///
/// Semantics: bits [63:0] of the destination XMM register are `src[63:0]`;
/// upper XMM bits are cleared.
/// Reference: Intel SDM Vol 2B, MOVD/MOVQ instruction.
pub fn encode_movq_to_xmm(src: SmtExpr) -> SmtExpr {
    src.extract(63, 0).zero_ext(64)
}

/// Encode `MOVQ r/m64, xmm` -- move the low 64 XMM bits to a GPR.
///
/// Semantics: `dst = src[63:0]`.
/// Reference: Intel SDM Vol 2B, MOVD/MOVQ instruction.
pub fn encode_movq_from_xmm(src: SmtExpr) -> SmtExpr {
    src.extract(63, 0)
}

/// Encode `CMOVcc r64, r64` or `CMOVcc r32, r32`.
///
/// `condition` is the Bool-sorted result of evaluating the requested x86
/// condition code against EFLAGS. CMOV preserves the old destination when the
/// condition is false and copies the source when it is true.
/// Reference: Intel SDM Vol 2A, CMOVcc instruction.
pub fn encode_cmovcc(
    _size: X86OperandSize,
    condition: SmtExpr,
    old_dst: SmtExpr,
    src: SmtExpr,
) -> SmtExpr {
    SmtExpr::ite(condition, src, old_dst)
}

// ---------------------------------------------------------------------------
// Extension instruction semantics (MOVZX, MOVSX)
// ---------------------------------------------------------------------------

/// Encode `MOVZX r64, r/m32` or `MOVZX r32, r/m16` -- zero-extension move.
///
/// Semantics: extract the low `from_width` bits from `src`, then zero-extend
/// to `to_width` bits.
/// Reference: Intel SDM Vol 2B, MOVZX instruction.
pub fn encode_movzx(from_width: u32, to_width: u32, src: SmtExpr) -> SmtExpr {
    src.extract(from_width - 1, 0)
        .zero_ext(to_width - from_width)
}

/// Encode `MOVSX r64, r/m32` or `MOVSXD r64, r/m32` -- sign-extension move.
///
/// Semantics: extract the low `from_width` bits from `src`, then sign-extend
/// to `to_width` bits.
/// Reference: Intel SDM Vol 2B, MOVSX/MOVSXD instructions.
pub fn encode_movsx(from_width: u32, to_width: u32, src: SmtExpr) -> SmtExpr {
    src.extract(from_width - 1, 0)
        .sign_ext(to_width - from_width)
}

// ---------------------------------------------------------------------------
// LEA (Load Effective Address)
// ---------------------------------------------------------------------------

/// Encode `LEA dst, [base + index*scale]` -- compute effective address.
///
/// Semantics: `dst = base + (index * scale)`.
/// Reference: Intel SDM Vol 2A, LEA instruction.
pub fn encode_lea_base_index_scale(base: SmtExpr, index: SmtExpr, scale: u32) -> SmtExpr {
    let width = base.bv_width();
    base.bvadd(index.bvmul(SmtExpr::bv_const(scale as u64, width)))
}

/// Encode `LEA dst, [base + disp]` -- compute effective address with displacement.
///
/// Semantics: `dst = base + displacement`.
/// Reference: Intel SDM Vol 2A, LEA instruction.
pub fn encode_lea_base_disp(base: SmtExpr, disp: i64, width: u32) -> SmtExpr {
    base.bvadd(SmtExpr::bv_const(disp as u64, width))
}

/// Encode `LEA dst, [base + index*scale + disp]` -- compute effective address.
///
/// Semantics: `dst = base + index*scale + displacement`.
/// Reference: Intel SDM Vol 2A, LEA instruction.
pub fn encode_lea_base_index_scale_disp(
    base: SmtExpr,
    index: SmtExpr,
    scale: u32,
    disp: i64,
) -> SmtExpr {
    let width = base.bv_width();
    base.bvadd(index.bvmul(SmtExpr::bv_const(scale as u64, width)))
        .bvadd(SmtExpr::bv_const(disp as u64, width))
}

// ---------------------------------------------------------------------------
// Three-operand IMUL
// ---------------------------------------------------------------------------

/// Encode `IMUL r64, r/m64, imm` or `IMUL r32, r/m32, imm` -- signed multiply.
///
/// Semantics: `dst = src * sign_extend(imm)` (wrapping, lower bits).
/// The three-operand IMUL form stores the lower half of the product in dst,
/// which is equivalent to wrapping multiplication.
/// Reference: Intel SDM Vol 2A, IMUL instruction (three-operand form).
pub fn encode_imul_rri(size: X86OperandSize, src: SmtExpr, imm: i64) -> SmtExpr {
    let width = x86_operand_size_bits(size);
    // ONE multiply encoder: an ImulRRI is IMUL by a constant operand, i.e.
    // encode_imul_rr with the immediate materialized as a same-width bv const.
    // Output-identical to `src.bvmul(bv_const(imm,width))`; unifying the
    // encoder makes any future multiply-semantics change move BOTH this
    // instance obligation AND the ImulRR canonical key together (drift-robust).
    encode_imul_rr(size, src, SmtExpr::bv_const(imm as u64, width))
}

// ---------------------------------------------------------------------------
// Floating-point instruction semantics (SSE)
// ---------------------------------------------------------------------------

/// Floating-point precision selector for x86-64 SSE instructions.
///
/// Maps to SSE scalar single (SS) and scalar double (SD) instruction variants.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum X86FPSize {
    /// Single-precision (32-bit, XMM lower 32 bits). IEEE 754 binary32.
    /// Uses ADDSS, SUBSS, MULSS, DIVSS instructions.
    Single,
    /// Double-precision (64-bit, XMM lower 64 bits). IEEE 754 binary64.
    /// Uses ADDSD, SUBSD, MULSD, DIVSD instructions.
    Double,
}

impl X86FPSize {
    /// Exponent bits for this FP size.
    pub fn eb(self) -> u32 {
        match self {
            X86FPSize::Single => 8,
            X86FPSize::Double => 11,
        }
    }

    /// Significand bits (including implicit bit) for this FP size.
    pub fn sb(self) -> u32 {
        match self {
            X86FPSize::Single => 24,
            X86FPSize::Double => 53,
        }
    }
}

/// Encode `ADDSD xmm, xmm` or `ADDSS xmm, xmm` -- scalar FP add.
///
/// Semantics: `dst = src1 + src2` using RNE rounding mode (default MXCSR).
/// Reference: Intel SDM Vol 2A, ADDSD/ADDSS instructions.
pub fn encode_fp_add_rr(_size: X86FPSize, src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_add(RoundingMode::RNE, src1, src2)
}

/// Encode `SUBSD xmm, xmm` or `SUBSS xmm, xmm` -- scalar FP subtract.
///
/// Semantics: `dst = src1 - src2` using RNE rounding mode.
/// Reference: Intel SDM Vol 2B, SUBSD/SUBSS instructions.
pub fn encode_fp_sub_rr(_size: X86FPSize, src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_sub(RoundingMode::RNE, src1, src2)
}

/// Encode `MULSD xmm, xmm` or `MULSS xmm, xmm` -- scalar FP multiply.
///
/// Semantics: `dst = src1 * src2` using RNE rounding mode.
/// Reference: Intel SDM Vol 2B, MULSD/MULSS instructions.
pub fn encode_fp_mul_rr(_size: X86FPSize, src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_mul(RoundingMode::RNE, src1, src2)
}

/// Encode `DIVSD xmm, xmm` or `DIVSS xmm, xmm` -- scalar FP divide.
///
/// Semantics: `dst = src1 / src2` using RNE rounding mode.
/// Reference: Intel SDM Vol 2B, DIVSD/DIVSS instructions.
pub fn encode_fp_div_rr(_size: X86FPSize, src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_div(RoundingMode::RNE, src1, src2)
}

// ---------------------------------------------------------------------------
// Unary floating-point instruction semantics (SSE)
// ---------------------------------------------------------------------------

/// Encode scalar FP negation via `XORPS`/`XORPD` with sign-bit mask.
///
/// On x86-64, scalar FP negation is typically implemented by XOR-ing the
/// sign bit with a constant mask (0x80000000 for single, 0x8000000000000000
/// for double). The semantic effect is `fp.neg(src)`.
///
/// Reference: Intel SDM Vol 2B, XORPS/XORPD instructions.
pub fn encode_fp_neg(_size: X86FPSize, src: SmtExpr) -> SmtExpr {
    src.fp_neg()
}

/// Encode scalar FP absolute value via `ANDPS`/`ANDPD` with sign-bit mask.
///
/// On x86-64, scalar FP absolute value is typically implemented by AND-ing
/// with a constant mask that clears the sign bit (0x7FFFFFFF for single,
/// 0x7FFFFFFFFFFFFFFF for double). The semantic effect is `fp.abs(src)`.
///
/// Reference: Intel SDM Vol 2A, ANDPS/ANDPD instructions.
pub fn encode_fp_abs(_size: X86FPSize, src: SmtExpr) -> SmtExpr {
    src.fp_abs()
}

/// Encode `SQRTSS xmm, xmm` or `SQRTSD xmm, xmm` -- scalar FP square root.
///
/// Semantics: `dst = sqrt(src)` using RNE rounding mode (default MXCSR).
/// Reference: Intel SDM Vol 2B, SQRTSS/SQRTSD instructions.
pub fn encode_fp_sqrt(_size: X86FPSize, src: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_sqrt(RoundingMode::RNE, src)
}

/// Encode `ROUNDSD xmm, xmm, imm8` or `ROUNDSS xmm, xmm, imm8` -- scalar FP
/// round-to-integral (SSE4.1).
///
/// The instruction rounds `src` to an integral floating-point value. When
/// imm8 bit 2 (0x04) is clear, the rounding direction comes from imm8 bits
/// [1:0] (rounding-select); when set, MXCSR.RC is used. The backend always
/// emits a static rounding-select (bit 2 clear) with bit 3 (0x08) set to
/// suppress the precision (inexact) exception, so we decode the imm8[1:0]
/// selector EXACTLY as the hardware does:
///   00 = round to nearest (even)  -> RNE
///   01 = round down (toward -inf)  -> RTN  (floor)
///   10 = round up (toward +inf)    -> RTP  (ceil)
///   11 = round toward zero         -> RTZ  (trunc)
/// The IEEE roundToIntegral operation never raises overflow/underflow and (with
/// the suppress bit) no precision exception; it preserves NaN, signed zeros and
/// infinities. Modeling the imm8 decode here means the proof certifies that the
/// SPECIFIC imm8 the ISel emits realizes the trust_ir spec's rounding mode — not
/// a hand-chosen mode independent of the encoding.
///
/// Reference: Intel SDM Vol 2B, ROUNDSD/ROUNDSS; Table "Rounding Modes and
/// Encoding of Rounding Control (RC) Field".
pub fn encode_fp_round(_size: X86FPSize, imm8: u8, src: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    let rm = match imm8 & 0b11 {
        0b00 => RoundingMode::RNE,
        0b01 => RoundingMode::RTN,
        0b10 => RoundingMode::RTP,
        // 0b11
        _ => RoundingMode::RTZ,
    };
    SmtExpr::fp_round_to_integral(rm, src)
}

/// Encode `MINSD xmm, xmm` / `MINSS xmm, xmm` -- scalar FP minimum, modeling
/// the EXACT Intel-SDM hardware semantics (NOT IEEE `fp.min`).
///
/// SDM (MINSD/MINSS, "Operation"): the result is the SECOND operand `src`
/// whenever the inputs are unordered (either is NaN) or equal, OR when
/// `dest >= src`; the result is `dest` only when `dest < src` (ordered). All
/// of those cases collapse to the single conditional `dest < src ? dest : src`,
/// because IEEE `<` is false for unordered, equal, and greater pairs alike.
/// This is exactly why MINSD alone is WRONG for `min(x, NaN)` (returns NaN, the
/// src) and for some signed-zero orderings — the bridge wraps it in a NaN-fixup
/// blend (see `select_fminmax`). Reference: Intel SDM Vol 2B, MINSD/MINSS.
pub fn encode_fp_minsd(dest: SmtExpr, src: SmtExpr) -> SmtExpr {
    // dest < src (ordered) ? dest : src
    let lt = dest.clone().fp_lt(src.clone());
    SmtExpr::ite(lt, dest, src)
}

/// Encode `MAXSD xmm, xmm` / `MAXSS xmm, xmm` -- scalar FP maximum, modeling
/// the EXACT Intel-SDM hardware semantics (NOT IEEE `fp.max`).
///
/// Mirror of `encode_fp_minsd`: the result is `dest` only when `dest > src`
/// (ordered); in every other case (unordered, equal, or `dest < src`) the
/// result is the SECOND operand `src`. Reference: Intel SDM Vol 2B,
/// MAXSD/MAXSS.
pub fn encode_fp_maxsd(dest: SmtExpr, src: SmtExpr) -> SmtExpr {
    // dest > src (ordered) ? dest : src
    let gt = dest.clone().fp_gt(src.clone());
    SmtExpr::ite(gt, dest, src)
}

/// Encode `CMPSD xmm, xmm, imm8=3` / `CMPSS ..., imm8=3` -- scalar FP UNORD
/// compare-to-mask in the low lane.
///
/// With predicate 3 (CMP_UNORD_Q) the instruction writes an all-ones mask of
/// the operand width when EITHER operand is NaN (the operands are unordered),
/// and an all-zero mask otherwise. The bridge issues it as a self-compare
/// (`CMPSD t, t, 3`), so the mask is all-ones iff `t` is NaN. We model the
/// general two-operand form here (`isNaN(a) OR isNaN(b)`), which the self-
/// compare specializes. `width` is the lane width (64 for SD, 32 for SS).
/// Reference: Intel SDM Vol 2A, CMPSD/CMPSS, Table "Comparison Predicate".
pub fn encode_fp_cmp_unord_mask(width: u32, a: SmtExpr, b: SmtExpr) -> SmtExpr {
    let unord = a.fp_is_nan().or_expr(b.fp_is_nan());
    let all_ones = SmtExpr::bv_const(u64::MAX, width);
    let zero = SmtExpr::bv_const(0, width);
    SmtExpr::ite(unord, all_ones, zero)
}

/// Encode `CMPSS xmm, xmm, imm8` / `CMPSD xmm, xmm, imm8` -- scalar FP
/// compare-to-mask in the low lane, for the EIGHT basic predicates the
/// (non-AVX) immediate selects, modeling the EXACT Intel-SDM hardware semantics.
///
/// The instruction writes an all-ones mask of the lane width (`width` = 32 for
/// SS, 64 for SD) when the predicate HOLDS, and an all-zero mask otherwise. The
/// imm8 predicate field [2:0] selects (Intel SDM Vol 2A, CMPSS/CMPSD, Table
/// "Comparison Predicate for CMPPD/CMPPS/CMPSD/CMPSS Instructions"):
///
///   0 EQ   (ordered, non-signaling)  : a == b   AND ordered
///   1 LT   (ordered, signaling)      : a <  b
///   2 LE   (ordered, signaling)      : a <= b
///   3 UNORD (non-signaling)          : isNaN(a) OR isNaN(b)
///   4 NEQ  (unordered, non-signaling): NOT(a == b)   [true if unordered or a!=b]
///   5 NLT  (unordered, signaling)    : NOT(a <  b)   [true if unordered or a>=b]
///   6 NLE  (unordered, signaling)    : NOT(a <= b)   [true if unordered or a>b]
///   7 ORD  (non-signaling)           : NOT(isNaN(a) OR isNaN(b))
///
/// The crucial x86 semantics (NOT ARM / NOT IEEE minNum): predicates 0..2 are the
/// ORDERED forms — they are FALSE whenever either operand is NaN (because the
/// IEEE relations `==`/`<`/`<=` are all false for an unordered pair). Predicates
/// 4..6 are their negations, so they are TRUE whenever the pair is unordered.
/// Modeling the negations as `NOT(ordered relation)` — rather than e.g. `a > b`
/// for NLE — is exactly the hardware: `CMPNLESS` of `(NaN, 1.0)` yields all-ones
/// (the pair is unordered, so `<=` is false, so its negation is true), whereas
/// `a > b` would yield all-zero. The bridge validates this against Rosetta.
///
/// `imm8 & 0b111` is the predicate; the high bits (and the AVX-only predicates
/// 8..31) are not emitted by the trust-cg backend and are out of scope here.
/// Reference: Intel SDM Vol 2A, CMPSS/CMPSD.
pub fn encode_fp_cmp_mask(width: u32, imm8: u8, a: SmtExpr, b: SmtExpr) -> SmtExpr {
    let all_ones = SmtExpr::bv_const(u64::MAX, width);
    let zero = SmtExpr::bv_const(0, width);
    let unord = || a.clone().fp_is_nan().or_expr(b.clone().fp_is_nan());
    let cond = match imm8 & 0b111 {
        0 => a.clone().fp_eq(b.clone()),            // EQ (ordered)
        1 => a.clone().fp_lt(b.clone()),            // LT (ordered)
        2 => a.clone().fp_le(b.clone()),            // LE (ordered)
        3 => unord(),                               // UNORD
        4 => a.clone().fp_eq(b.clone()).not_expr(), // NEQ (unordered)
        5 => a.clone().fp_lt(b.clone()).not_expr(), // NLT (unordered)
        6 => a.clone().fp_le(b.clone()).not_expr(), // NLE (unordered)
        // 7
        _ => unord().not_expr(), // ORD
    };
    SmtExpr::ite(cond, all_ones, zero)
}

// ---------------------------------------------------------------------------
// Packed floating-point instruction semantics (SSE/SSE2)
// ---------------------------------------------------------------------------
//
// ADDPS/SUBPS/MULPS/DIVPS operate on four binary32 lanes; ADDPD/SUBPD/MULPD/
// DIVPD on two binary64 lanes. Each lane is an independent IEEE-754 binary
// operation. The Intel SDM specifies that packed FP arithmetic uses the same
// rounding control as the scalar forms: MXCSR.RC, whose ABI-mandated default
// is round-to-nearest-even (RNE). As with the scalar FP arithmetic proofs in
// this module (ADDSD/MULSD/...), the trust-cg backend never reprograms MXCSR.RC
// away from RNE, so the packed lanes are modeled under RNE.
//
// Because each lane is independent and identical in form, the per-lane
// semantic functions below capture the complete behavior of one lane. The
// packed instruction's correctness obligation decomposes into proving that one
// representative lane equals the trust_ir per-lane FP operation; the encoder
// applies the same operation to every lane, so per-lane equivalence implies
// full-vector equivalence. This mirrors how the packed-integer encoders
// (`encode_paddd` = `map_lanes_binary(... bvadd)`) reduce to a single lane op.

/// Encode one lane of `ADDPS`/`ADDPD` -- packed FP add.
///
/// Semantics: `lane = src1 + src2` using RNE rounding (default MXCSR). The
/// packed instruction applies this independently to each of its 4 (PS) or 2
/// (PD) lanes. Reference: Intel SDM Vol 2A, ADDPS/ADDPD instructions.
pub fn encode_packed_fp_add_lane(_size: X86FPSize, src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_add(RoundingMode::RNE, src1, src2)
}

/// Encode one lane of `SUBPS`/`SUBPD` -- packed FP subtract.
///
/// Semantics: `lane = src1 - src2` using RNE rounding (default MXCSR).
/// Reference: Intel SDM Vol 2B, SUBPS/SUBPD instructions.
pub fn encode_packed_fp_sub_lane(_size: X86FPSize, src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_sub(RoundingMode::RNE, src1, src2)
}

/// Encode one lane of `MULPS`/`MULPD` -- packed FP multiply.
///
/// Semantics: `lane = src1 * src2` using RNE rounding (default MXCSR).
/// Reference: Intel SDM Vol 2B, MULPS/MULPD instructions.
pub fn encode_packed_fp_mul_lane(_size: X86FPSize, src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_mul(RoundingMode::RNE, src1, src2)
}

/// Encode one lane of `DIVPS`/`DIVPD` -- packed FP divide.
///
/// Semantics: `lane = src1 / src2` using RNE rounding (default MXCSR).
/// Reference: Intel SDM Vol 2B, DIVPS/DIVPD instructions.
pub fn encode_packed_fp_div_lane(_size: X86FPSize, src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_div(RoundingMode::RNE, src1, src2)
}

/// x86-64 UCOMISS/UCOMISD comparison flags used by FP SETcc lowering.
///
/// UCOMI sets the condition flags consumed by the current lowering: CF, ZF,
/// and PF. Ordered finite comparisons clear PF; unordered comparisons set
/// CF=ZF=PF=1.
#[derive(Debug, Clone)]
pub struct UcomiFlags {
    pub cf: SmtExpr,
    pub zf: SmtExpr,
    pub pf: SmtExpr,
}

/// Encode scalar `UCOMISS`/`UCOMISD` flag semantics for FP comparisons.
///
/// Intel defines the relevant flag outcomes as:
/// - unordered: CF=1, ZF=1, PF=1
/// - greater: CF=0, ZF=0, PF=0
/// - less: CF=1, ZF=0, PF=0
/// - equal: CF=0, ZF=1, PF=0
pub fn encode_ucomi_flags(_size: X86FPSize, lhs: SmtExpr, rhs: SmtExpr) -> UcomiFlags {
    let unordered = lhs.clone().fp_is_nan().or_expr(rhs.clone().fp_is_nan());
    let less = lhs.clone().fp_lt(rhs.clone());
    let equal = lhs.fp_eq(rhs);

    UcomiFlags {
        cf: unordered.clone().or_expr(less),
        zf: unordered.clone().or_expr(equal),
        pf: unordered,
    }
}

/// Evaluate the x86 condition codes reachable from UCOMISS/UCOMISD.
pub fn eval_ucomi_condition(cc: X86CondCode, flags: &UcomiFlags) -> SmtExpr {
    match cc {
        X86CondCode::B => flags.cf.clone(),
        X86CondCode::AE => flags.cf.clone().not_expr(),
        X86CondCode::E => flags.zf.clone(),
        X86CondCode::NE => flags.zf.clone().not_expr(),
        X86CondCode::BE => flags.cf.clone().or_expr(flags.zf.clone()),
        X86CondCode::A => flags
            .cf
            .clone()
            .not_expr()
            .and_expr(flags.zf.clone().not_expr()),
        X86CondCode::P => flags.pf.clone(),
        X86CondCode::NP => flags.pf.clone().not_expr(),
        other => panic!("unsupported UCOMI condition code in FP compare proof: {other:?}"),
    }
}

/// Encode `UCOMIS{S,D}` followed by one `SETcc`.
pub fn encode_ucomi_setcc(size: X86FPSize, lhs: SmtExpr, rhs: SmtExpr, cc: X86CondCode) -> SmtExpr {
    let flags = encode_ucomi_flags(size, lhs, rhs);
    let cond = eval_ucomi_condition(cc, &flags);
    SmtExpr::ite(cond, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1))
}

/// Encode the NaN-correct x86-64 FP compare sequence selected by ISel.
///
/// This models `UCOMISS`/`UCOMISD` plus the exact SETcc combination selected
/// by `trust_cg_lower::x86_float_cmp_strategy`: a single SETcc, SETcc&SETNP, or
/// SETcc|SETP.
pub fn encode_fp_cmp_strategy(
    size: X86FPSize,
    lhs: SmtExpr,
    rhs: SmtExpr,
    strategy: X86FloatCmpStrategy,
) -> SmtExpr {
    let flags = encode_ucomi_flags(size, lhs, rhs);
    let cond =
        match strategy {
            X86FloatCmpStrategy::SingleCC(cc) => eval_ucomi_condition(cc, &flags),
            X86FloatCmpStrategy::AndNotParity(cc) => eval_ucomi_condition(cc, &flags)
                .and_expr(eval_ucomi_condition(X86CondCode::NP, &flags)),
            X86FloatCmpStrategy::OrParity(cc) => eval_ucomi_condition(cc, &flags)
                .or_expr(eval_ucomi_condition(X86CondCode::P, &flags)),
        };
    SmtExpr::ite(cond, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1))
}

// ---------------------------------------------------------------------------
// Integer RFLAGS model for CMP + Setcc/Jcc/CMOVcc
// ---------------------------------------------------------------------------
//
// The x86 conditional families (SETcc, Jcc, CMOVcc) read the RFLAGS bits a
// prior CMP/SUB set. CMP `a, b` computes the difference `d = a - b` (wrapping at
// the operand width) and sets ZF/SF/CF/OF/PF from it. To reconstruct a CMOVcc
// FAITHFULLY (so a WRONG condition code REFUTES) we model the five flag bits as
// the genuine hardware functions of `(a, b)`, then express each condition code
// as the textbook boolean over those bits (`X86CondCode` documents the formula
// in its variant comments). Composing `cc_formula(flags_of(a,b))` then yields
// exactly the matching signed/unsigned comparison of `(a, b)` — but ONLY if the
// cc formula is correct: an E-for-NE or L-for-GE bug produces the complementary
// boolean and diverges. NOTHING here collapses the cc to a single abstract
// boolean (which would make every cc equivalent = vacuous); each cc is a
// distinct formula over distinct flag bits.

/// The five x86 RFLAGS bits a `CMP a, b` (i.e. `SUB`) sets, as boolean
/// `SmtExpr`s over the operand width.
#[derive(Debug, Clone)]
pub struct IntCmpFlags {
    /// Zero flag: the difference is zero (`a == b`).
    pub zf: SmtExpr,
    /// Sign flag: the difference's high bit is set (result is negative-signed).
    pub sf: SmtExpr,
    /// Carry flag: unsigned borrow out of the subtraction (`a <u b`).
    pub cf: SmtExpr,
    /// Overflow flag: signed overflow of `a - b`.
    pub of: SmtExpr,
    /// Parity flag: even number of set bits in the low byte of the difference.
    pub pf: SmtExpr,
}

/// Encode the RFLAGS a `CMP a, b` sets at `width` bits, as the GENUINE hardware
/// functions of `(a, b)`.
///
/// `d = a - b` (wrapping). Then:
/// - ZF = `a == b`
/// - SF = `msb(d)` (the difference is negative as a signed value)
/// - CF = `a <u b` (unsigned borrow)
/// - OF = `(msb(a) != msb(b)) && (msb(d) != msb(a))` — the textbook signed
///   overflow condition for subtraction. With this OF, `SF != OF` is exactly
///   `a <s b` (signed less-than), so the L/GE/LE/G condition codes are correct.
/// - PF = even parity of the low 8 bits of `d`.
pub fn encode_int_cmp_flags(width: u32, a: SmtExpr, b: SmtExpr) -> IntCmpFlags {
    let d = a.clone().bvsub(b.clone());

    // Most significant (sign) bit of a width-bit value: extract bit [width-1].
    let msb = |v: SmtExpr| {
        v.extract(width - 1, width - 1)
            .eq_expr(SmtExpr::bv_const(1, 1))
    };

    let zf = a.clone().eq_expr(b.clone());
    let sf = msb(d.clone());
    let cf = a.clone().bvult(b.clone());

    // OF (subtraction): operands differ in sign AND the result sign differs from
    // the minuend's sign.
    let msb_a = msb(a);
    let msb_b = msb(b);
    let msb_d = msb(d.clone());
    let signs_differ = msb_a.clone().eq_expr(msb_b).not_expr();
    let result_sign_flips = msb_d.eq_expr(msb_a).not_expr();
    let of = signs_differ.and_expr(result_sign_flips);

    // PF: parity of the low byte of the difference. PF = 1 iff the low 8 bits
    // contain an EVEN number of set bits. Build it as the XNOR-reduction of the
    // 8 low bits (sum of bits is even).
    let low8 = if width >= 8 {
        d.clone().extract(7, 0)
    } else {
        d.clone().zero_ext(8 - width)
    };
    // Parity = NOT(xor of all 8 bits). xor of bit i = extract(i,i).
    let mut xor_acc = low8.clone().extract(0, 0);
    for i in 1..8u32 {
        xor_acc = xor_acc.bvxor(low8.clone().extract(i, i));
    }
    let pf = xor_acc.eq_expr(SmtExpr::bv_const(0, 1));

    IntCmpFlags { zf, sf, cf, of, pf }
}

/// Evaluate an x86 condition code as a boolean over [`IntCmpFlags`].
///
/// Each variant is the textbook formula documented on [`X86CondCode`]. A wrong
/// cc (e.g. `E` instead of `NE`, or `L` instead of `GE`) yields the
/// complementary boolean and so DIVERGES from the intended predicate ⇒ REFUTE.
pub fn eval_int_condition(cc: X86CondCode, flags: &IntCmpFlags) -> SmtExpr {
    let zf = || flags.zf.clone();
    let sf = || flags.sf.clone();
    let cf = || flags.cf.clone();
    let of = || flags.of.clone();
    let pf = || flags.pf.clone();
    match cc {
        X86CondCode::O => of(),
        X86CondCode::NO => of().not_expr(),
        X86CondCode::B => cf(),
        X86CondCode::AE => cf().not_expr(),
        X86CondCode::E => zf(),
        X86CondCode::NE => zf().not_expr(),
        X86CondCode::BE => cf().or_expr(zf()),
        X86CondCode::A => cf().not_expr().and_expr(zf().not_expr()),
        X86CondCode::S => sf(),
        X86CondCode::NS => sf().not_expr(),
        X86CondCode::P => pf(),
        X86CondCode::NP => pf().not_expr(),
        // L = SF != OF
        X86CondCode::L => sf().eq_expr(of()).not_expr(),
        // GE = SF == OF
        X86CondCode::GE => sf().eq_expr(of()),
        // LE = ZF || (SF != OF)
        X86CondCode::LE => zf().or_expr(sf().eq_expr(of()).not_expr()),
        // G = !ZF && (SF == OF)
        X86CondCode::G => zf().not_expr().and_expr(sf().eq_expr(of())),
    }
}

// ---------------------------------------------------------------------------
// SSE floating-point conversion instruction semantics
// ---------------------------------------------------------------------------
//
// These model the IEEE 754 conversion semantics of the SSE scalar CVT* family.
//
// MXCSR rounding-mode assumption: the non-truncating int<->FP and FP<->FP
// conversions (CVTSI2SD/SS, CVTSD2SI/CVTSS2SI, CVTSD2SS) honor the dynamic
// rounding control in MXCSR.RC. As with the existing scalar FP arithmetic
// proofs (ADDSD/MULSD/... in this module, which document the same RNE
// assumption), the trust-cg backend never reprograms MXCSR.RC away from its
// ABI-mandated default of round-to-nearest-even (RNE). We therefore model
// these conversions under RNE.
//
// The truncating variants (CVTTSD2SI/CVTTSS2SI) ignore MXCSR.RC and always
// round toward zero (RTZ) by definition of the instruction; they are modeled
// with RTZ unconditionally.
//
// CVTSS2SD (single -> double) widens and is exact for every finite single,
// so the rounding mode is immaterial; RNE is used for uniformity.
//
// Reference: Intel SDM Vol 2A, CVTSI2SD/CVTSI2SS/CVTSD2SI/CVTSS2SI;
//            Vol 2A CVTTSD2SI/CVTTSS2SI; Vol 2A CVTSD2SS/CVTSS2SD.

/// Integer source width for an int->FP conversion (CVTSI2SD/CVTSI2SS).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum X86CvtIntWidth {
    /// 32-bit signed integer source/destination (`r/m32`).
    I32,
    /// 64-bit signed integer source/destination (`r/m64`, REX.W).
    I64,
}

impl X86CvtIntWidth {
    /// Width in bits.
    pub fn bits(self) -> u32 {
        match self {
            X86CvtIntWidth::I32 => 32,
            X86CvtIntWidth::I64 => 64,
        }
    }
}

/// Encode `CVTSI2SD xmm, r/m{32,64}` -- signed integer to scalar double.
///
/// Semantics: interpret `src` as a two's-complement signed integer and convert
/// to the nearest IEEE 754 binary64 value using MXCSR rounding (RNE default).
/// The result fills the low 64 bits of the destination XMM register.
///
/// Reference: Intel SDM Vol 2A, CVTSI2SD instruction.
pub fn encode_cvtsi2sd(_width: X86CvtIntWidth, src: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::bv_to_fp(RoundingMode::RNE, src, 11, 53)
}

/// Encode `CVTSI2SS xmm, r/m{32,64}` -- signed integer to scalar single.
///
/// Semantics: interpret `src` as a two's-complement signed integer and convert
/// to the nearest IEEE 754 binary32 value using MXCSR rounding (RNE default).
///
/// Reference: Intel SDM Vol 2A, CVTSI2SS instruction.
pub fn encode_cvtsi2ss(_width: X86CvtIntWidth, src: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::bv_to_fp(RoundingMode::RNE, src, 8, 24)
}

/// Encode `CVTSD2SI r/m{32,64}, xmm` -- scalar double to signed integer.
///
/// Semantics: convert `src` (binary64) to a `dst_bits`-wide signed integer
/// using MXCSR rounding (RNE default, i.e. round-to-nearest-even). This is
/// the *non-truncating* form (contrast `encode_cvttsd2si`).
///
/// Reference: Intel SDM Vol 2A, CVTSD2SI instruction.
pub fn encode_cvtsd2si(dst_bits: u32, src: SmtExpr) -> SmtExpr {
    use crate::smt::{OutOfRangeMode, RoundingMode};
    SmtExpr::fp_to_sbv_mode(
        RoundingMode::RNE,
        src,
        dst_bits,
        OutOfRangeMode::IntegerIndefinite,
    )
}

/// Encode `CVTSS2SI r/m{32,64}, xmm` -- scalar single to signed integer.
///
/// Semantics: convert `src` (binary32) to a `dst_bits`-wide signed integer
/// using MXCSR rounding (RNE default). Non-truncating form.
///
/// Reference: Intel SDM Vol 2A, CVTSS2SI instruction.
pub fn encode_cvtss2si(dst_bits: u32, src: SmtExpr) -> SmtExpr {
    use crate::smt::{OutOfRangeMode, RoundingMode};
    SmtExpr::fp_to_sbv_mode(
        RoundingMode::RNE,
        src,
        dst_bits,
        OutOfRangeMode::IntegerIndefinite,
    )
}

/// Encode `CVTTSD2SI r/m{32,64}, xmm` -- scalar double to signed integer,
/// truncating.
///
/// Semantics: convert `src` (binary64) to a `dst_bits`-wide signed integer
/// rounding toward zero (RTZ). This is the variant emitted by the ISel for
/// trust_ir `FcvtToInt` (C cast semantics).
///
/// Reference: Intel SDM Vol 2A, CVTTSD2SI instruction.
pub fn encode_cvttsd2si(dst_bits: u32, src: SmtExpr) -> SmtExpr {
    use crate::smt::{OutOfRangeMode, RoundingMode};
    SmtExpr::fp_to_sbv_mode(
        RoundingMode::RTZ,
        src,
        dst_bits,
        OutOfRangeMode::IntegerIndefinite,
    )
}

/// Encode `CVTTSS2SI r/m{32,64}, xmm` -- scalar single to signed integer,
/// truncating.
///
/// Semantics: convert `src` (binary32) to a `dst_bits`-wide signed integer
/// rounding toward zero (RTZ).
///
/// Reference: Intel SDM Vol 2A, CVTTSS2SI instruction.
pub fn encode_cvttss2si(dst_bits: u32, src: SmtExpr) -> SmtExpr {
    use crate::smt::{OutOfRangeMode, RoundingMode};
    SmtExpr::fp_to_sbv_mode(
        RoundingMode::RTZ,
        src,
        dst_bits,
        OutOfRangeMode::IntegerIndefinite,
    )
}

/// Encode `CVTSD2SS xmm, xmm` -- scalar double to scalar single (narrowing).
///
/// Semantics: round `src` (binary64) to the nearest binary32 value using MXCSR
/// rounding (RNE default). This is the precision-reducing FpTrunc conversion.
///
/// Reference: Intel SDM Vol 2A, CVTSD2SS instruction.
pub fn encode_cvtsd2ss(src: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_to_fp(RoundingMode::RNE, src, 8, 24)
}

/// Encode `CVTSS2SD xmm, xmm` -- scalar single to scalar double (widening).
///
/// Semantics: convert `src` (binary32) to binary64. Every finite binary32
/// value is exactly representable in binary64, so this is exact and the
/// rounding mode is immaterial (RNE used for uniformity). This is the
/// precision-extending FpExt conversion.
///
/// Reference: Intel SDM Vol 2A, CVTSS2SD instruction.
pub fn encode_cvtss2sd(src: SmtExpr) -> SmtExpr {
    use crate::smt::RoundingMode;
    SmtExpr::fp_to_fp(RoundingMode::RNE, src, 11, 53)
}

// ---------------------------------------------------------------------------
// Bit manipulation instruction semantics (BSF/BSR/TZCNT/LZCNT/POPCNT)
// ---------------------------------------------------------------------------
//
// These model the bit-counting instructions as pure bitvector functions of the
// source operand. The result width equals the operand width (the destination
// GPR holds a value in [0, width]).
//
// Zero-input behavior differs across the family and is modeled precisely:
//   - TZCNT(0) = width, LZCNT(0) = width   (defined; ZF set as a side effect)
//   - POPCNT(0) = 0
//   - BSF(0) / BSR(0): destination is ARCHITECTURALLY UNDEFINED, and ZF=1 flags
//     the zero input. The proofs for BSF/BSR therefore carry a `src != 0`
//     precondition; under that precondition BSF == TZCNT and
//     BSR == (width - 1) - LZCNT.
//
// Reference: Intel SDM Vol 2A, BSF/BSR; Vol 2B/2A, TZCNT/LZCNT/POPCNT.

/// Bit `i` of `src` as a Bool-sorted predicate (`src[i] == 1`).
fn bit_is_set(src: &SmtExpr, i: u32) -> SmtExpr {
    src.clone().extract(i, i).eq_expr(SmtExpr::bv_const(1, 1))
}

/// Encode `POPCNT r, r/m` -- population count (number of set bits).
///
/// Semantics: `dst = popcount(src)`, a value in `[0, width]`, materialized as
/// a sum of the `width` individual source bits zero-extended to the result
/// width. Reference: Intel SDM Vol 2B, POPCNT instruction.
pub fn encode_popcnt(src: SmtExpr) -> SmtExpr {
    let width = src.bv_width();
    let mut acc = SmtExpr::bv_const(0, width);
    for i in 0..width {
        let bit = src.clone().extract(i, i);
        let bit_w = if width == 1 {
            bit
        } else {
            bit.zero_ext(width - 1)
        };
        acc = acc.bvadd(bit_w);
    }
    acc
}

/// Encode `TZCNT r, r/m` -- count trailing (least-significant) zero bits.
///
/// Semantics: number of contiguous zero bits starting from bit 0. If `src`
/// is zero the defined result is `width`. Equivalent to trust_ir `Cttz`
/// (count-trailing-zeros) with the well-defined zero-input convention.
///
/// The expression scans from the most-significant bit downward, so the
/// innermost (else) value is `width` (taken when every bit is zero) and each
/// set bit `i` overrides the running count with `i`.
///
/// Reference: Intel SDM Vol 2B, TZCNT instruction.
pub fn encode_tzcnt(src: SmtExpr) -> SmtExpr {
    let width = src.bv_width();
    // Default (all bits zero): result = width.
    let mut result = SmtExpr::bv_const(u64::from(width), width);
    // Iterate from MSB to LSB so the lowest set bit wins (it is applied last).
    for i in (0..width).rev() {
        result = SmtExpr::ite(
            bit_is_set(&src, i),
            SmtExpr::bv_const(u64::from(i), width),
            result,
        );
    }
    result
}

/// Encode `LZCNT r, r/m` -- count leading (most-significant) zero bits.
///
/// Semantics: number of contiguous zero bits starting from the most-
/// significant bit. If `src` is zero the defined result is `width`.
/// Equivalent to trust_ir `Ctlz` with the well-defined zero-input convention.
///
/// The expression scans from the least-significant bit upward, so the highest
/// set bit `i` wins and contributes `width - 1 - i` leading zeros.
///
/// Reference: Intel SDM Vol 2A, LZCNT instruction.
pub fn encode_lzcnt(src: SmtExpr) -> SmtExpr {
    let width = src.bv_width();
    let mut result = SmtExpr::bv_const(u64::from(width), width);
    // Iterate from LSB to MSB so the highest set bit wins (applied last).
    for i in 0..width {
        let leading = width - 1 - i;
        result = SmtExpr::ite(
            bit_is_set(&src, i),
            SmtExpr::bv_const(u64::from(leading), width),
            result,
        );
    }
    result
}

/// Encode `BSF r, r/m` -- bit scan forward (index of lowest set bit).
///
/// Semantics: when `src != 0`, returns the bit index of the least-significant
/// set bit (identical to TZCNT). When `src == 0` the destination is
/// architecturally undefined and ZF is set; this function returns the
/// `src != 0` value (TZCNT) and the zero-input case is excluded by the
/// BSF proof's precondition.
///
/// Reference: Intel SDM Vol 2A, BSF instruction.
pub fn encode_bsf(src: SmtExpr) -> SmtExpr {
    // For src != 0, BSF == TZCNT (lowest set bit index).
    encode_tzcnt(src)
}

/// Encode `BSR r, r/m` -- bit scan reverse (index of highest set bit).
///
/// Semantics: when `src != 0`, returns the bit index of the most-significant
/// set bit. For an `n`-bit operand this equals `(n - 1) - LZCNT(src)`. When
/// `src == 0` the destination is architecturally undefined and ZF is set; this
/// function returns the `src != 0` value and the zero-input case is excluded
/// by the BSR proof's precondition.
///
/// Reference: Intel SDM Vol 2A, BSR instruction.
pub fn encode_bsr(src: SmtExpr) -> SmtExpr {
    let width = src.bv_width();
    // Default (no set bit): width. For nonzero inputs the highest set bit wins.
    let mut result = SmtExpr::bv_const(u64::from(width), width);
    for i in 0..width {
        result = SmtExpr::ite(
            bit_is_set(&src, i),
            SmtExpr::bv_const(u64::from(i), width),
            result,
        );
    }
    result
}

/// Encode the carry flag (`CF`) written by `BT r, imm8` -- bit test.
///
/// Semantics: `BT r, k` copies bit `k` of the operand `r` into `CF` and leaves
/// `r` (and OF/SF/ZF/AF/PF, which are architecturally undefined) unchanged.
/// This function returns the 1-bit CF value as the Intel SDM defines it via a
/// logical shift: `CF := (r >> k) & 1`. The bit index `k` is a static immediate
/// (`0 <= k < width`), matching the `BtRI` encoding (`0F BA /4 ib`) the x86
/// peephole emits.
///
/// Reference: Intel SDM Vol 2A, BT instruction.
pub fn encode_bt_cf(src: SmtExpr, k: u32) -> SmtExpr {
    let width = src.bv_width();
    debug_assert!(k < width, "BT bit index {k} out of range for width {width}");
    // SDM definition: CF <- (src >> k) AND 1. Take the low bit of the shifted
    // operand. Modeled as a shift-then-extract so the obligation's x86 side is
    // structurally distinct from the AND-mask reference predicate it proves
    // equal to (a wrong model therefore refutes rather than matching trivially).
    let shifted = src.bvlshr(SmtExpr::bv_const(u64::from(k), width));
    shifted.extract(0, 0)
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::EvalResult;
    use std::collections::HashMap;

    fn env(pairs: &[(&str, u64)]) -> HashMap<String, u64> {
        pairs.iter().map(|(k, v)| (k.to_string(), *v)).collect()
    }

    fn sym32() -> (SmtExpr, SmtExpr) {
        (SmtExpr::var("a", 32), SmtExpr::var("b", 32))
    }

    fn sym64() -> (SmtExpr, SmtExpr) {
        (SmtExpr::var("a", 64), SmtExpr::var("b", 64))
    }

    // -----------------------------------------------------------------------
    // Integer arithmetic tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_add_rr_32() {
        let (a, b) = sym32();
        let expr = encode_add_rr(X86OperandSize::S32, a, b);
        let result = expr.eval(&env(&[("a", 100), ("b", 200)]));
        assert_eq!(result, EvalResult::Bv(300));
    }

    #[test]
    fn test_add_rr_64() {
        let (a, b) = sym64();
        let expr = encode_add_rr(X86OperandSize::S64, a, b);
        let result = expr.eval(&env(&[("a", 0x1_0000_0000), ("b", 0x2_0000_0000)]));
        assert_eq!(result, EvalResult::Bv(0x3_0000_0000));
    }

    #[test]
    fn test_sub_rr_32() {
        let (a, b) = sym32();
        let expr = encode_sub_rr(X86OperandSize::S32, a, b);
        let result = expr.eval(&env(&[("a", 10), ("b", 3)]));
        assert_eq!(result, EvalResult::Bv(7));
    }

    #[test]
    fn test_imul_rr_32() {
        let (a, b) = sym32();
        let expr = encode_imul_rr(X86OperandSize::S32, a, b);
        let result = expr.eval(&env(&[("a", 6), ("b", 7)]));
        assert_eq!(result, EvalResult::Bv(42));
    }

    #[test]
    fn test_neg_32() {
        let a = SmtExpr::var("a", 32);
        let expr = encode_neg(X86OperandSize::S32, a);
        let result = expr.eval(&env(&[("a", 1)]));
        assert_eq!(result, EvalResult::Bv(0xFFFF_FFFF));
    }

    #[test]
    fn test_neg_zero() {
        let a = SmtExpr::var("a", 32);
        let expr = encode_neg(X86OperandSize::S32, a);
        let result = expr.eval(&env(&[("a", 0)]));
        assert_eq!(result, EvalResult::Bv(0));
    }

    // -----------------------------------------------------------------------
    // Bitwise instruction tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_and_rr_32() {
        let (a, b) = sym32();
        let expr = encode_and_rr(X86OperandSize::S32, a, b);
        let result = expr.eval(&env(&[("a", 0xFF00_FF00), ("b", 0x0F0F_0F0F)]));
        assert_eq!(result, EvalResult::Bv(0x0F00_0F00));
    }

    #[test]
    fn test_or_rr_32() {
        let (a, b) = sym32();
        let expr = encode_or_rr(X86OperandSize::S32, a, b);
        let result = expr.eval(&env(&[("a", 0xFF00_0000), ("b", 0x00FF_0000)]));
        assert_eq!(result, EvalResult::Bv(0xFFFF_0000));
    }

    #[test]
    fn test_xor_rr_32() {
        let (a, b) = sym32();
        let expr = encode_xor_rr(X86OperandSize::S32, a, b);
        let result = expr.eval(&env(&[("a", 0xAAAA_AAAA), ("b", 0x5555_5555)]));
        assert_eq!(result, EvalResult::Bv(0xFFFF_FFFF));
    }

    #[test]
    fn test_not_32() {
        let a = SmtExpr::var("a", 32);
        let expr = encode_not(X86OperandSize::S32, a);
        let result = expr.eval(&env(&[("a", 0)]));
        assert_eq!(result, EvalResult::Bv(0xFFFF_FFFF));
    }

    #[test]
    fn test_not_32_all_ones() {
        let a = SmtExpr::var("a", 32);
        let expr = encode_not(X86OperandSize::S32, a);
        let result = expr.eval(&env(&[("a", 0xFFFF_FFFF)]));
        assert_eq!(result, EvalResult::Bv(0));
    }

    // -----------------------------------------------------------------------
    // Shift instruction tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_shl_rr_32() {
        let (a, b) = sym32();
        let expr = encode_shl_rr(X86OperandSize::S32, a, b);
        let result = expr.eval(&env(&[("a", 1), ("b", 4)]));
        assert_eq!(result, EvalResult::Bv(16));
    }

    #[test]
    fn test_shr_rr_32() {
        let (a, b) = sym32();
        let expr = encode_shr_rr(X86OperandSize::S32, a, b);
        let result = expr.eval(&env(&[("a", 0x8000_0000), ("b", 4)]));
        assert_eq!(result, EvalResult::Bv(0x0800_0000));
    }

    #[test]
    fn test_sar_rr_32() {
        let (a, b) = sym32();
        let expr = encode_sar_rr(X86OperandSize::S32, a, b);
        // Arithmetic shift right of 0x80000000 by 4 = 0xF8000000 (sign-extends)
        let result = expr.eval(&env(&[("a", 0x8000_0000), ("b", 4)]));
        assert_eq!(result, EvalResult::Bv(0xF800_0000));
    }

    #[test]
    fn test_sar_rr_32_positive() {
        let (a, b) = sym32();
        let expr = encode_sar_rr(X86OperandSize::S32, a, b);
        // Positive value: 0x7FFFFFFF >> 4 = 0x07FFFFFF (zero-fills)
        let result = expr.eval(&env(&[("a", 0x7FFF_FFFF), ("b", 4)]));
        assert_eq!(result, EvalResult::Bv(0x07FF_FFFF));
    }

    // -----------------------------------------------------------------------
    // Masked-shift tests (the reconstruction machine side, #57 / #66)
    // -----------------------------------------------------------------------

    #[test]
    fn test_shl_rr_masked_in_range_matches_unmasked() {
        // In range (count < width) the mask is the identity: same as encode_shl_rr.
        let (a, b) = sym32();
        let masked = encode_shl_rr_masked(X86OperandSize::S32, a, b);
        assert_eq!(masked.eval(&env(&[("a", 1), ("b", 4)])), EvalResult::Bv(16));
    }

    #[test]
    fn test_shl_rr_masked_wraps_count_mod_32() {
        // At 32-bit the count is masked & 0x1F: a shift by 32 masks to 0 (identity)
        // on hardware, NOT the SMT clamp-to-0 of the unmasked bvshl.
        let (a, b) = sym32();
        let masked = encode_shl_rr_masked(X86OperandSize::S32, a, b);
        assert_eq!(masked.eval(&env(&[("a", 7), ("b", 32)])), EvalResult::Bv(7));
        // shift by 33 masks to 1.
        assert_eq!(masked.eval(&env(&[("a", 1), ("b", 33)])), EvalResult::Bv(2));
    }

    #[test]
    fn test_shl_rr_masked_wraps_count_mod_64() {
        // At 64-bit the count is masked & 0x3F: a shift by 64 masks to 0 (identity).
        let (a, b) = sym64();
        let masked = encode_shl_rr_masked(X86OperandSize::S64, a, b);
        assert_eq!(masked.eval(&env(&[("a", 7), ("b", 64)])), EvalResult::Bv(7));
        assert_eq!(masked.eval(&env(&[("a", 1), ("b", 65)])), EvalResult::Bv(2));
    }

    #[test]
    fn test_shr_rr_masked_logical() {
        let (a, b) = sym32();
        let masked = encode_shr_rr_masked(X86OperandSize::S32, a, b);
        assert_eq!(
            masked.eval(&env(&[("a", 0x8000_0000), ("b", 4)])),
            EvalResult::Bv(0x0800_0000)
        );
    }

    #[test]
    fn test_sar_rr_masked_arithmetic() {
        let (a, b) = sym32();
        let masked = encode_sar_rr_masked(X86OperandSize::S32, a, b);
        assert_eq!(
            masked.eval(&env(&[("a", 0x8000_0000), ("b", 4)])),
            EvalResult::Bv(0xF800_0000)
        );
    }

    // -----------------------------------------------------------------------
    // Floating-point instruction tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_fp_add_single() {
        let a = SmtExpr::fp32_const(1.5f32);
        let b = SmtExpr::fp32_const(2.5f32);
        let expr = encode_fp_add_rr(X86FPSize::Single, a, b);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(4.0));
    }

    #[test]
    fn test_fp_add_double() {
        let a = SmtExpr::fp64_const(100.0);
        let b = SmtExpr::fp64_const(200.0);
        let expr = encode_fp_add_rr(X86FPSize::Double, a, b);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(300.0));
    }

    #[test]
    fn test_fp_sub_double() {
        let a = SmtExpr::fp64_const(100.0);
        let b = SmtExpr::fp64_const(42.0);
        let expr = encode_fp_sub_rr(X86FPSize::Double, a, b);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(58.0));
    }

    #[test]
    fn test_fp_mul_double() {
        let a = SmtExpr::fp64_const(6.0);
        let b = SmtExpr::fp64_const(7.0);
        let expr = encode_fp_mul_rr(X86FPSize::Double, a, b);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(42.0));
    }

    #[test]
    fn test_fp_div_double() {
        let a = SmtExpr::fp64_const(84.0);
        let b = SmtExpr::fp64_const(2.0);
        let expr = encode_fp_div_rr(X86FPSize::Double, a, b);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(42.0));
    }

    // -----------------------------------------------------------------------
    // Unary floating-point instruction tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_fp_neg_single() {
        let a = SmtExpr::fp32_const(3.0f32);
        let expr = encode_fp_neg(X86FPSize::Single, a);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(-3.0));
    }

    #[test]
    fn test_fp_neg_double() {
        let a = SmtExpr::fp64_const(42.0);
        let expr = encode_fp_neg(X86FPSize::Double, a);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(-42.0));
    }

    #[test]
    fn test_fp_abs_single() {
        let a = SmtExpr::fp32_const(-5.0f32);
        let expr = encode_fp_abs(X86FPSize::Single, a);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(5.0));
    }

    #[test]
    fn test_fp_abs_double() {
        let a = SmtExpr::fp64_const(-100.0);
        let expr = encode_fp_abs(X86FPSize::Double, a);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(100.0));
    }

    #[test]
    fn test_fp_sqrt_single() {
        let a = SmtExpr::fp32_const(4.0f32);
        let expr = encode_fp_sqrt(X86FPSize::Single, a);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(2.0));
    }

    #[test]
    fn test_fp_sqrt_double() {
        let a = SmtExpr::fp64_const(9.0);
        let expr = encode_fp_sqrt(X86FPSize::Double, a);
        let result = expr.try_eval(&env(&[])).unwrap();
        assert_eq!(result, EvalResult::Float(3.0));
    }

    #[test]
    fn test_ucomi_flags_for_unordered_nan() {
        let flags = encode_ucomi_flags(
            X86FPSize::Double,
            SmtExpr::fp64_const(f64::NAN),
            SmtExpr::fp64_const(1.0),
        );

        assert_eq!(flags.cf.eval(&HashMap::new()), EvalResult::Bool(true));
        assert_eq!(flags.zf.eval(&HashMap::new()), EvalResult::Bool(true));
        assert_eq!(flags.pf.eval(&HashMap::new()), EvalResult::Bool(true));
    }

    #[test]
    fn test_fp_cmp_and_not_parity_excludes_nan_for_ordered_equal() {
        let finite = encode_fp_cmp_strategy(
            X86FPSize::Double,
            SmtExpr::fp64_const(1.0),
            SmtExpr::fp64_const(1.0),
            X86FloatCmpStrategy::AndNotParity(X86CondCode::E),
        );
        let nan = encode_fp_cmp_strategy(
            X86FPSize::Double,
            SmtExpr::fp64_const(f64::NAN),
            SmtExpr::fp64_const(1.0),
            X86FloatCmpStrategy::AndNotParity(X86CondCode::E),
        );

        assert_eq!(finite.eval(&HashMap::new()), EvalResult::Bv(1));
        assert_eq!(nan.eval(&HashMap::new()), EvalResult::Bv(0));
    }

    #[test]
    fn test_fp_cmp_or_parity_includes_nan_for_unordered_equal() {
        let finite_not_equal = encode_fp_cmp_strategy(
            X86FPSize::Single,
            SmtExpr::fp32_const(1.0),
            SmtExpr::fp32_const(2.0),
            X86FloatCmpStrategy::OrParity(X86CondCode::E),
        );
        let nan = encode_fp_cmp_strategy(
            X86FPSize::Single,
            SmtExpr::fp32_const(f32::NAN),
            SmtExpr::fp32_const(2.0),
            X86FloatCmpStrategy::OrParity(X86CondCode::E),
        );

        assert_eq!(finite_not_equal.eval(&HashMap::new()), EvalResult::Bv(0));
        assert_eq!(nan.eval(&HashMap::new()), EvalResult::Bv(1));
    }

    #[test]
    fn test_fp_cmp_single_parity_predicates_model_ordering() {
        let ordered = encode_fp_cmp_strategy(
            X86FPSize::Double,
            SmtExpr::fp64_const(1.0),
            SmtExpr::fp64_const(2.0),
            X86FloatCmpStrategy::SingleCC(X86CondCode::NP),
        );
        let unordered = encode_fp_cmp_strategy(
            X86FPSize::Double,
            SmtExpr::fp64_const(f64::NAN),
            SmtExpr::fp64_const(2.0),
            X86FloatCmpStrategy::SingleCC(X86CondCode::P),
        );

        assert_eq!(ordered.eval(&HashMap::new()), EvalResult::Bv(1));
        assert_eq!(unordered.eval(&HashMap::new()), EvalResult::Bv(1));
    }

    #[test]
    fn test_fp_size_parameters() {
        assert_eq!(X86FPSize::Single.eb(), 8);
        assert_eq!(X86FPSize::Single.sb(), 24);
        assert_eq!(X86FPSize::Double.eb(), 11);
        assert_eq!(X86FPSize::Double.sb(), 53);
    }

    // -----------------------------------------------------------------------
    // SSE conversion tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_cvtsi2sd_signed() {
        // -5 (i32, sign-extended through BvToFP) -> -5.0
        let expr = encode_cvtsi2sd(X86CvtIntWidth::I32, SmtExpr::var("a", 32));
        let result = expr.eval(&env(&[("a", (-5i32) as u32 as u64)]));
        assert_eq!(result, EvalResult::Float(-5.0));
    }

    #[test]
    fn test_cvttsd2si_truncates_toward_zero() {
        // 1.9 -> 1 and -1.9 -> -1 (truncation, RTZ).
        let pos = encode_cvttsd2si(32, SmtExpr::fp64_const(1.9));
        assert_eq!(pos.eval(&HashMap::new()), EvalResult::Bv(1));
        let neg = encode_cvttsd2si(32, SmtExpr::fp64_const(-1.9));
        assert_eq!(neg.eval(&HashMap::new()), EvalResult::Bv(0xFFFF_FFFF));
    }

    #[test]
    fn test_cvtss2sd_is_exact_widen() {
        let val = std::f32::consts::PI;
        let expr = encode_cvtss2sd(SmtExpr::fp32_const(val));
        assert_eq!(expr.eval(&HashMap::new()), EvalResult::Float(val as f64));
    }

    #[test]
    fn test_cvtsd2ss_narrows() {
        let expr = encode_cvtsd2ss(SmtExpr::fp64_const(1.0));
        assert_eq!(expr.eval(&HashMap::new()), EvalResult::Float(1.0f32 as f64));
    }

    // -----------------------------------------------------------------------
    // Bit-manipulation tests (validated against Rust's native operations)
    // -----------------------------------------------------------------------

    #[test]
    fn test_popcnt_matches_count_ones_i8() {
        let expr = encode_popcnt(SmtExpr::var("a", 8));
        for a in 0u64..256 {
            let expected = (a as u8).count_ones() as u64;
            assert_eq!(
                expr.clone().eval(&env(&[("a", a)])),
                EvalResult::Bv(expected),
                "popcnt mismatch for {a}"
            );
        }
    }

    #[test]
    fn test_popcnt_i32_known_values() {
        let expr = encode_popcnt(SmtExpr::var("a", 32));
        for a in [0u64, 1, 0xFFFF_FFFF, 0xAAAA_AAAA, 0x8000_0001] {
            let expected = (a as u32).count_ones() as u64;
            assert_eq!(
                expr.clone().eval(&env(&[("a", a)])),
                EvalResult::Bv(expected)
            );
        }
    }

    #[test]
    fn test_tzcnt_matches_trailing_zeros_i8() {
        let expr = encode_tzcnt(SmtExpr::var("a", 8));
        for a in 0u64..256 {
            let expected = (a as u8).trailing_zeros() as u64; // (0u8).trailing_zeros() == 8 == width
            assert_eq!(
                expr.clone().eval(&env(&[("a", a)])),
                EvalResult::Bv(expected),
                "tzcnt mismatch for {a}"
            );
        }
    }

    #[test]
    fn test_lzcnt_matches_leading_zeros_i8() {
        let expr = encode_lzcnt(SmtExpr::var("a", 8));
        for a in 0u64..256 {
            let expected = (a as u8).leading_zeros() as u64; // (0u8).leading_zeros() == 8 == width
            assert_eq!(
                expr.clone().eval(&env(&[("a", a)])),
                EvalResult::Bv(expected),
                "lzcnt mismatch for {a}"
            );
        }
    }

    #[test]
    fn test_bsf_matches_lowest_set_bit_for_nonzero_i8() {
        let expr = encode_bsf(SmtExpr::var("a", 8));
        for a in 1u64..256 {
            let expected = (a as u8).trailing_zeros() as u64;
            assert_eq!(
                expr.clone().eval(&env(&[("a", a)])),
                EvalResult::Bv(expected)
            );
        }
    }

    #[test]
    fn test_bsr_matches_highest_set_bit_for_nonzero_i8() {
        let expr = encode_bsr(SmtExpr::var("a", 8));
        for a in 1u64..256 {
            let expected = (7 - (a as u8).leading_zeros()) as u64;
            assert_eq!(
                expr.clone().eval(&env(&[("a", a)])),
                EvalResult::Bv(expected)
            );
        }
    }

    #[test]
    fn test_tzcnt_lzcnt_zero_input_is_width() {
        assert_eq!(
            encode_tzcnt(SmtExpr::var("a", 32)).eval(&env(&[("a", 0)])),
            EvalResult::Bv(32)
        );
        assert_eq!(
            encode_lzcnt(SmtExpr::var("a", 32)).eval(&env(&[("a", 0)])),
            EvalResult::Bv(32)
        );
    }

    // -----------------------------------------------------------------------
    // Integer RFLAGS model for CMP + Setcc/Jcc/CMOVcc
    // -----------------------------------------------------------------------

    /// Each integer condition code over `flags_of(a, b)` must equal the
    /// corresponding signed/unsigned comparison of `(a, b)`. This is the
    /// soundness floor for the CMOVcc reconstruction: a wrong cc formula here
    /// would let a wrong-cc lowering pass.
    #[test]
    fn int_condition_codes_match_their_comparisons() {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let flags = encode_int_cmp_flags(32, a.clone(), b.clone());

        // (a, b, expected per cc).
        let cases: &[(u64, u64)] = &[
            (5, 5),
            (5, 7),
            (7, 5),
            // signed negatives (as 32-bit): -1 = 0xFFFF_FFFF, -5 = 0xFFFF_FFFB.
            (0xFFFF_FFFF, 1),
            (1, 0xFFFF_FFFF),
            (0xFFFF_FFFB, 0xFFFF_FFFF),
            (0x8000_0000, 0x7FFF_FFFF), // INT_MIN vs INT_MAX
        ];
        for &(av, bv) in cases {
            let e = env(&[("a", av), ("b", bv)]);
            let sa = av as i32;
            let sb = bv as i32;
            let ua = av as u32;
            let ub = bv as u32;
            let want = |b: bool| EvalResult::Bool(b);
            assert_eq!(
                eval_int_condition(X86CondCode::E, &flags).eval(&e),
                want(av == bv),
                "E a={av:#x} b={bv:#x}"
            );
            assert_eq!(
                eval_int_condition(X86CondCode::NE, &flags).eval(&e),
                want(av != bv),
                "NE"
            );
            assert_eq!(
                eval_int_condition(X86CondCode::L, &flags).eval(&e),
                want(sa < sb),
                "L a={sa} b={sb}"
            );
            assert_eq!(
                eval_int_condition(X86CondCode::GE, &flags).eval(&e),
                want(sa >= sb),
                "GE"
            );
            assert_eq!(
                eval_int_condition(X86CondCode::G, &flags).eval(&e),
                want(sa > sb),
                "G"
            );
            assert_eq!(
                eval_int_condition(X86CondCode::LE, &flags).eval(&e),
                want(sa <= sb),
                "LE"
            );
            assert_eq!(
                eval_int_condition(X86CondCode::B, &flags).eval(&e),
                want(ua < ub),
                "B"
            );
            assert_eq!(
                eval_int_condition(X86CondCode::AE, &flags).eval(&e),
                want(ua >= ub),
                "AE"
            );
            assert_eq!(
                eval_int_condition(X86CondCode::A, &flags).eval(&e),
                want(ua > ub),
                "A"
            );
            assert_eq!(
                eval_int_condition(X86CondCode::BE, &flags).eval(&e),
                want(ua <= ub),
                "BE"
            );
        }
    }

    /// E and NE must be EXACT complements (sanity that ccs are not collapsed).
    #[test]
    fn int_condition_e_and_ne_are_complements() {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let flags = encode_int_cmp_flags(32, a, b);
        for &(av, bv) in &[(3u64, 3u64), (3, 4), (4, 3)] {
            let e = env(&[("a", av), ("b", bv)]);
            let zf = eval_int_condition(X86CondCode::E, &flags).eval(&e);
            let nzf = eval_int_condition(X86CondCode::NE, &flags).eval(&e);
            assert_ne!(zf, nzf, "E and NE must differ at a={av} b={bv}");
        }
    }
}
