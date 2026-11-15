// trust-cg-verify/nzcv.rs - AArch64 NZCV flag model and condition code evaluation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Models AArch64 NZCV flags as boolean SMT expressions derived from
// subtraction results. Used to verify comparison and branch lowering rules.
//
// Reference: ARM Architecture Reference Manual (DDI 0487), Section C5.2.9

//! AArch64 NZCV flag model and condition code evaluation.
//!
//! The AArch64 processor status register contains four condition flags:
//! - **N** (Negative): set to the MSB of the result
//! - **Z** (Zero): set if the result is zero
//! - **C** (Carry): set if unsigned carry out occurred
//! - **V** (oVerflow): set if signed overflow occurred
//!
//! These flags are set by CMP (which is SUBS with result discarded),
//! ADDS, SUBS, and a few other instructions. They are consumed by
//! conditional branches (B.cond), conditional select (CSEL), and
//! conditional set (CSET).

use crate::smt::SmtExpr;
use trust_cg_lower::isel::AArch64CC;

/// NZCV flags as boolean SMT expressions.
///
/// Each field is a Bool-sorted `SmtExpr` representing whether that flag is set.
#[derive(Debug, Clone)]
pub struct NzcvFlags {
    /// N: Negative flag = result MSB.
    pub n: SmtExpr,
    /// Z: Zero flag = (result == 0).
    pub z: SmtExpr,
    /// C: Carry flag = unsigned carry out of the adder (for subtraction this
    /// equals Rn >=_u Rm — a theorem the proofs establish, see `encode_cmp`).
    pub c: SmtExpr,
    /// V: oVerflow flag = signed overflow.
    pub v: SmtExpr,
}

/// Encode CMP semantics: `CMP Rn, Rm` computes `Rn - Rm` and sets NZCV.
///
/// CMP is an alias for SUBS with the result register being XZR/WZR (discarded).
/// The flags reflect the subtraction `Rn - Rm`.
///
/// # Flag definitions (ARM DDI 0487, C5.2.9)
///
/// For a subtraction `result = Rn - Rm`:
/// - N = result[MSB]
/// - Z = (result == 0)
/// - C = carry-out of `AddWithCarry(Rn, NOT Rm, 1)` (unsigned borrow is the
///   inverted carry; architecturally C == (Rn >=_u Rm), but see below)
/// - V = (sign(Rn) != sign(Rm)) AND (sign(Rn) != sign(result))
///
/// # Why C is derived from the adder and not written as `Rn >=_u Rm`
///
/// The C flag used to be encoded as `bvuge(Rn, Rm)` outright. That is the
/// right VALUE, but it made `Icmp_UGE -> CMP+CSET_HS` the tautology
/// `bvuge(a, b) == bvuge(a, b)` (retracted as degenerate, #62) and left the
/// other unsigned predicates (LO/HI/LS) one negation away from their spec.
/// The ARM pseudocode (DDI 0487, `AddWithCarry`) defines C as the carry-out
/// of `Rn + NOT(Rm) + 1`; this model follows it with the full-adder carry-out
/// identity at the most significant bit, entirely at the operand width:
///
/// ```text
///   x = Rn, y = NOT Rm, s = x + y + 1 (= Rn - Rm mod 2^w)
///   C = ((x & y) | ((x ^ y) & NOT s))[w-1]
/// ```
///
/// `C == (Rn >=_u Rm)` is then a theorem about the adder that every
/// unsigned comparison/branch proof establishes, not a definition.
///
/// # Arguments
///
/// - `rn`, `rm`: operand expressions (must be same bit-width)
/// - `width`: bitvector width (32 or 64)
pub fn encode_cmp(rn: SmtExpr, rm: SmtExpr, width: u32) -> NzcvFlags {
    let result = rn.clone().bvsub(rm.clone());
    let zero = SmtExpr::bv_const(0, width);

    // N: sign bit of result
    let n = result
        .clone()
        .extract(width - 1, width - 1)
        .eq_expr(SmtExpr::bv_const(1, 1));

    // Z: result == 0
    let z = result.clone().eq_expr(zero);

    // C: carry-out of AddWithCarry(Rn, NOT Rm, 1) — the full-adder carry-out
    // at the MSB (see the doc comment). `result` is exactly x + y + 1.
    let ones = SmtExpr::bv_const(
        if width >= 64 {
            u64::MAX
        } else {
            (1u64 << width) - 1
        },
        width,
    );
    let x = rn.clone();
    let y = rm.clone().bvxor(ones.clone()); // NOT Rm
    let not_s = result.clone().bvxor(ones);
    let carry_chain = x.clone().bvand(y.clone()).bvor(x.bvxor(y).bvand(not_s));
    let c = carry_chain
        .extract(width - 1, width - 1)
        .eq_expr(SmtExpr::bv_const(1, 1));

    // V: signed overflow of subtraction.
    // Overflow when: operand signs differ AND result sign differs from Rn sign.
    let rn_msb = rn.extract(width - 1, width - 1);
    let rm_msb = rm.extract(width - 1, width - 1);
    let res_msb = result.extract(width - 1, width - 1);
    let v = rn_msb
        .clone()
        .eq_expr(rm_msb)
        .not_expr()
        .and_expr(rn_msb.eq_expr(res_msb).not_expr());

    NzcvFlags { n, z, c, v }
}

/// Evaluate a condition code against NZCV flags.
///
/// Returns a Bool-sorted `SmtExpr` that is true iff the condition holds.
///
/// # Condition code definitions (ARM DDI 0487, Table C5-1)
///
/// | CC | Meaning            | Flags         |
/// |----|--------------------|---------------|
/// | EQ | Equal              | Z==1          |
/// | NE | Not Equal          | Z==0          |
/// | HS | Unsigned >=        | C==1          |
/// | LO | Unsigned <         | C==0          |
/// | MI | Negative           | N==1          |
/// | PL | Positive or zero   | N==0          |
/// | VS | Overflow           | V==1          |
/// | VC | No overflow        | V==0          |
/// | HI | Unsigned >         | C==1 AND Z==0 |
/// | LS | Unsigned <=        | C==0 OR Z==1  |
/// | GE | Signed >=          | N==V          |
/// | LT | Signed <           | N!=V          |
/// | GT | Signed >           | Z==0 AND N==V |
/// | LE | Signed <=          | Z==1 OR N!=V  |
pub fn eval_condition(cc: AArch64CC, flags: &NzcvFlags) -> SmtExpr {
    match cc {
        AArch64CC::EQ => flags.z.clone(),
        AArch64CC::NE => flags.z.clone().not_expr(),
        AArch64CC::HS => flags.c.clone(),
        AArch64CC::LO => flags.c.clone().not_expr(),
        AArch64CC::MI => flags.n.clone(),
        AArch64CC::PL => flags.n.clone().not_expr(),
        AArch64CC::VS => flags.v.clone(),
        AArch64CC::VC => flags.v.clone().not_expr(),
        AArch64CC::HI => flags.c.clone().and_expr(flags.z.clone().not_expr()),
        AArch64CC::LS => flags.c.clone().not_expr().or_expr(flags.z.clone()),
        AArch64CC::GE => flags.n.clone().eq_expr(flags.v.clone()),
        AArch64CC::LT => flags.n.clone().eq_expr(flags.v.clone()).not_expr(),
        AArch64CC::GT => flags
            .z
            .clone()
            .not_expr()
            .and_expr(flags.n.clone().eq_expr(flags.v.clone())),
        AArch64CC::LE => flags
            .z
            .clone()
            .or_expr(flags.n.clone().eq_expr(flags.v.clone()).not_expr()),
    }
}

/// Encode TST semantics: `TST Rn, Rm` computes `Rn & Rm` and sets NZCV.
///
/// TST is an alias for ANDS with the destination register discarded (XZR/WZR).
///
/// # Flag definitions (ARM DDI 0487, C6.2.x — logical instructions)
///
/// For `result = Rn AND Rm`:
/// - N = result[MSB]
/// - Z = (result == 0)
/// - **C = 0** — the logical instructions CLEAR the carry flag
/// - **V = 0** — and clear the overflow flag
///
/// The two constant flags are load-bearing for the focused model check.
/// `SUBS`/`CMP` produce a data-dependent C
/// (`Rn >=u Rm`), so a rewrite that turns `AND` + `CMP #0` into a single `TST`
/// is only valid when NO consumer observes C. `trust_cg_opt::and_cmp_fuse`
/// enforces exactly that. Obligations built directly from this helper are not
/// registered for coverage because several collapse under the structural
/// non-degeneracy audit; an independent machine-side reconstruction is still
/// required before TST can leave the deferred RED inventory.
pub fn encode_tst(rn: SmtExpr, rm: SmtExpr, width: u32) -> NzcvFlags {
    let result = rn.bvand(rm);
    let zero = SmtExpr::bv_const(0, width);

    let n = result
        .clone()
        .extract(width - 1, width - 1)
        .eq_expr(SmtExpr::bv_const(1, 1));
    let z = result.eq_expr(zero);
    // Logical operations write 0 to both, unconditionally.
    let c = SmtExpr::bool_const(false);
    let v = SmtExpr::bool_const(false);

    NzcvFlags { n, z, c, v }
}

/// Encode `CSET Wd, cc` — conditional set.
///
/// Produces a 1-bit bitvector: `bv1(1)` if condition holds, `bv1(0)` otherwise.
/// This matches the trust_ir comparison result type `B1`.
pub fn encode_cset(cc: AArch64CC, flags: &NzcvFlags) -> SmtExpr {
    let cond = eval_condition(cc, flags);
    SmtExpr::ite(cond, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1))
}

/// Encode the full AArch64 comparison lowering sequence:
///   `CMP Rn, Rm` ; `CSET Wd, cc`
///
/// Returns a 1-bit bitvector result (same type as trust_ir Icmp output).
pub fn encode_cmp_cset(rn: SmtExpr, rm: SmtExpr, width: u32, cc: AArch64CC) -> SmtExpr {
    let flags = encode_cmp(rn, rm, width);
    encode_cset(cc, &flags)
}

/// The Arm ARM `AddWithCarry(x, y, carry_in)` pseudo-code (DDI 0487,
/// J1.1.3 shared/functions/integer/AddWithCarry), returning the `width`-bit
/// result and the NZCV it produces.
///
/// This is a separate transcription from [`encode_cmp`]: C and V come from a
/// `width + 1`-bit unsigned and signed sum, exactly as the pseudo-code states
/// them (`C = UInt(result) != unsigned_sum`, `V = SInt(result) != signed_sum`),
/// not from the full-adder carry identity `encode_cmp` uses. The flag-setting
/// producers ADDS/SUBS/CMP/ADCS/SBCS and the carry readers ADC/SBC are all
/// instances; `tests/aarch64_nzcv_silicon_bridge.rs` replays them against
/// facts recorded natively on Apple silicon.
///
/// `carry_in` must be a 1-bit bitvector. `width` must be 32 or 64.
pub fn add_with_carry(
    x: SmtExpr,
    y: SmtExpr,
    carry_in: SmtExpr,
    width: u32,
) -> (SmtExpr, NzcvFlags) {
    let carry = carry_in.zero_ext(width);
    let unsigned_sum = x
        .clone()
        .zero_ext(1)
        .bvadd(y.clone().zero_ext(1))
        .bvadd(carry.clone());
    let signed_sum = x.sign_ext(1).bvadd(y.sign_ext(1)).bvadd(carry);
    let result = unsigned_sum.clone().extract(width - 1, 0);
    let one = SmtExpr::bv_const(1, 1);
    let n = result
        .clone()
        .extract(width - 1, width - 1)
        .eq_expr(one.clone());
    let z = result.clone().eq_expr(SmtExpr::bv_const(0, width));
    // C: the width+1-bit unsigned sum differs from the zero-extended result
    // exactly when its top bit is set.
    let c = unsigned_sum.extract(width, width).eq_expr(one);
    // V: the width+1-bit signed sum differs from the sign-extended result
    // exactly when its top two bits disagree.
    let v = signed_sum
        .clone()
        .extract(width, width)
        .eq_expr(signed_sum.extract(width - 1, width - 1))
        .not_expr();
    (result, NzcvFlags { n, z, c, v })
}

fn all_ones(width: u32) -> SmtExpr {
    SmtExpr::bv_const(
        if width >= 64 {
            u64::MAX
        } else {
            (1u64 << width) - 1
        },
        width,
    )
}

/// The C flag of `flags` as a 1-bit bitvector (`PSTATE.C` as an adder input).
pub fn carry_bit(flags: &NzcvFlags) -> SmtExpr {
    SmtExpr::ite(
        flags.c.clone(),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    )
}

/// `ADDS Rd, Rn, Rm`: `AddWithCarry(Rn, Rm, 0)`.
pub fn encode_adds(rn: SmtExpr, rm: SmtExpr, width: u32) -> (SmtExpr, NzcvFlags) {
    add_with_carry(rn, rm, SmtExpr::bv_const(0, 1), width)
}

/// `SUBS Rd, Rn, Rm` (and `CMP Rn, Rm` with the result discarded):
/// `AddWithCarry(Rn, NOT(Rm), 1)`.
pub fn encode_subs(rn: SmtExpr, rm: SmtExpr, width: u32) -> (SmtExpr, NzcvFlags) {
    add_with_carry(
        rn,
        rm.bvxor(all_ones(width)),
        SmtExpr::bv_const(1, 1),
        width,
    )
}

/// `ADCS Rd, Rn, Rm`: `AddWithCarry(Rn, Rm, PSTATE.C)`. `carry_in` is the
/// incoming C flag as a 1-bit bitvector (see [`carry_bit`]).
pub fn encode_adcs(
    rn: SmtExpr,
    rm: SmtExpr,
    carry_in: SmtExpr,
    width: u32,
) -> (SmtExpr, NzcvFlags) {
    add_with_carry(rn, rm, carry_in, width)
}

/// `SBCS Rd, Rn, Rm`: `AddWithCarry(Rn, NOT(Rm), PSTATE.C)`.
pub fn encode_sbcs(
    rn: SmtExpr,
    rm: SmtExpr,
    carry_in: SmtExpr,
    width: u32,
) -> (SmtExpr, NzcvFlags) {
    add_with_carry(rn, rm.bvxor(all_ones(width)), carry_in, width)
}

/// `ADC Rd, Rn, Rm`: the `ADCS` value; NZCV is not written.
pub fn encode_adc(rn: SmtExpr, rm: SmtExpr, carry_in: SmtExpr, width: u32) -> SmtExpr {
    encode_adcs(rn, rm, carry_in, width).0
}

/// `SBC Rd, Rn, Rm`: the `SBCS` value; NZCV is not written.
pub fn encode_sbc(rn: SmtExpr, rm: SmtExpr, carry_in: SmtExpr, width: u32) -> SmtExpr {
    encode_sbcs(rn, rm, carry_in, width).0
}

/// Pack Bool flags into the architectural 4-bit `N:Z:C:V` value (N = bit 3),
/// the layout `MRS Xt, NZCV` returns in bits 31:28.
pub fn pack_nzcv(flags: &NzcvFlags) -> SmtExpr {
    let bit = |flag: &SmtExpr| {
        SmtExpr::ite(
            flag.clone(),
            SmtExpr::bv_const(1, 1),
            SmtExpr::bv_const(0, 1),
        )
    };
    bit(&flags.n)
        .concat(bit(&flags.z))
        .concat(bit(&flags.c))
        .concat(bit(&flags.v))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::EvalResult;
    use std::collections::HashMap;

    fn env(pairs: &[(&str, u64)]) -> HashMap<String, u64> {
        pairs.iter().map(|(k, v)| (k.to_string(), *v)).collect()
    }

    // -----------------------------------------------------------------------
    // NZCV flag unit tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_n_flag_positive_result() {
        let rn = SmtExpr::var("rn", 32);
        let rm = SmtExpr::var("rm", 32);
        let flags = encode_cmp(rn, rm, 32);
        // 10 - 3 = 7, MSB=0 -> N=false
        let result = flags.n.eval(&env(&[("rn", 10), ("rm", 3)]));
        assert_eq!(result, EvalResult::Bool(false));
    }

    #[test]
    fn test_n_flag_negative_result() {
        let rn = SmtExpr::var("rn", 32);
        let rm = SmtExpr::var("rm", 32);
        let flags = encode_cmp(rn, rm, 32);
        // 3 - 10 = -7 (0xFFFFFFF9), MSB=1 -> N=true
        let result = flags.n.eval(&env(&[("rn", 3), ("rm", 10)]));
        assert_eq!(result, EvalResult::Bool(true));
    }

    #[test]
    fn test_z_flag_zero_result() {
        let rn = SmtExpr::var("rn", 32);
        let rm = SmtExpr::var("rm", 32);
        let flags = encode_cmp(rn, rm, 32);
        // 5 - 5 = 0 -> Z=true
        let result = flags.z.eval(&env(&[("rn", 5), ("rm", 5)]));
        assert_eq!(result, EvalResult::Bool(true));
    }

    #[test]
    fn test_z_flag_nonzero_result() {
        let rn = SmtExpr::var("rn", 32);
        let rm = SmtExpr::var("rm", 32);
        let flags = encode_cmp(rn, rm, 32);
        // 5 - 3 = 2 -> Z=false
        let result = flags.z.eval(&env(&[("rn", 5), ("rm", 3)]));
        assert_eq!(result, EvalResult::Bool(false));
    }

    #[test]
    fn test_c_flag_no_borrow() {
        let rn = SmtExpr::var("rn", 32);
        let rm = SmtExpr::var("rm", 32);
        let flags = encode_cmp(rn, rm, 32);
        // 10 >= 3 (unsigned) -> C=true (no borrow)
        let result = flags.c.eval(&env(&[("rn", 10), ("rm", 3)]));
        assert_eq!(result, EvalResult::Bool(true));
    }

    #[test]
    fn test_c_flag_borrow() {
        let rn = SmtExpr::var("rn", 32);
        let rm = SmtExpr::var("rm", 32);
        let flags = encode_cmp(rn, rm, 32);
        // 3 < 10 (unsigned) -> C=false (borrow needed)
        let result = flags.c.eval(&env(&[("rn", 3), ("rm", 10)]));
        assert_eq!(result, EvalResult::Bool(false));
    }

    /// The adder-derived C equals `Rn >=_u Rm` on every 8-bit operand pair
    /// (exhaustive), and on the width-32/64 edges (equal operands, zero, MAX,
    /// the sign boundary) where the carry chain has to be exactly right.
    #[test]
    fn test_c_flag_is_unsigned_ge_exhaustively_at_8_bits_and_at_the_edges() {
        let flags8 = encode_cmp(SmtExpr::var("rn", 8), SmtExpr::var("rm", 8), 8);
        for a in 0u64..256 {
            for b in 0u64..256 {
                let got = flags8.c.eval(&env(&[("rn", a), ("rm", b)]));
                assert_eq!(got, EvalResult::Bool(a >= b), "8-bit C for rn={a} rm={b}");
            }
        }
        for width in [32u32, 64] {
            let flags = encode_cmp(SmtExpr::var("rn", width), SmtExpr::var("rm", width), width);
            let max = if width == 64 {
                u64::MAX
            } else {
                u32::MAX as u64
            };
            let sign = 1u64 << (width - 1);
            let pts = [0u64, 1, 2, sign - 1, sign, sign + 1, max - 1, max];
            for &a in &pts {
                for &b in &pts {
                    let got = flags.c.eval(&env(&[("rn", a), ("rm", b)]));
                    assert_eq!(
                        got,
                        EvalResult::Bool(a >= b),
                        "{width}-bit C for rn={a:#x} rm={b:#x}"
                    );
                }
            }
        }
    }

    /// The machine-side flag model must not contain the spec predicate itself:
    /// a CMP+CSET.HS obligation is only a theorem if C is not spelled `bvuge`.
    #[test]
    fn test_c_flag_is_not_spelled_as_bvuge() {
        let flags = encode_cmp(SmtExpr::var("rn", 64), SmtExpr::var("rm", 64), 64);
        let text = format!("{:?}", flags.c);
        assert!(
            !text.contains("BvUge") && !text.contains("BvUlt"),
            "C is degenerate: {text}"
        );
    }

    #[test]
    fn test_v_flag_no_overflow() {
        let rn = SmtExpr::var("rn", 32);
        let rm = SmtExpr::var("rm", 32);
        let flags = encode_cmp(rn, rm, 32);
        // 10 - 3: same-sign operands (both positive), no overflow
        let result = flags.v.eval(&env(&[("rn", 10), ("rm", 3)]));
        assert_eq!(result, EvalResult::Bool(false));
    }

    #[test]
    fn test_v_flag_overflow() {
        let rn = SmtExpr::var("rn", 32);
        let rm = SmtExpr::var("rm", 32);
        let flags = encode_cmp(rn, rm, 32);
        // INT_MAX - (-1) = INT_MAX + 1 = overflow
        // 0x7FFFFFFF - 0xFFFFFFFF: rn is positive, rm is negative,
        // result is 0x80000000 (negative) -> sign(rn) != sign(result) -> V=true
        let result = flags
            .v
            .eval(&env(&[("rn", 0x7FFF_FFFF), ("rm", 0xFFFF_FFFF)]));
        assert_eq!(result, EvalResult::Bool(true));
    }

    // -----------------------------------------------------------------------
    // Condition code evaluation tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_eq_condition_equal() {
        let rn = SmtExpr::var("rn", 32);
        let rm = SmtExpr::var("rm", 32);
        let flags = encode_cmp(rn, rm, 32);
        let cond = eval_condition(AArch64CC::EQ, &flags);
        // 5 == 5
        let result = cond.eval(&env(&[("rn", 5), ("rm", 5)]));
        assert_eq!(result, EvalResult::Bool(true));
    }

    #[test]
    fn test_eq_condition_not_equal() {
        let rn = SmtExpr::var("rn", 32);
        let rm = SmtExpr::var("rm", 32);
        let flags = encode_cmp(rn, rm, 32);
        let cond = eval_condition(AArch64CC::EQ, &flags);
        // 5 != 3
        let result = cond.eval(&env(&[("rn", 5), ("rm", 3)]));
        assert_eq!(result, EvalResult::Bool(false));
    }

    #[test]
    fn test_lt_condition_signed_less() {
        let rn = SmtExpr::var("rn", 32);
        let rm = SmtExpr::var("rm", 32);
        let flags = encode_cmp(rn, rm, 32);
        let cond = eval_condition(AArch64CC::LT, &flags);
        // -1 < 0 (signed)
        let result = cond.eval(&env(&[("rn", 0xFFFF_FFFF), ("rm", 0)]));
        assert_eq!(result, EvalResult::Bool(true));
    }

    #[test]
    fn test_lo_condition_unsigned_less() {
        let rn = SmtExpr::var("rn", 32);
        let rm = SmtExpr::var("rm", 32);
        let flags = encode_cmp(rn, rm, 32);
        let cond = eval_condition(AArch64CC::LO, &flags);
        // 3 <_u 10
        let result = cond.eval(&env(&[("rn", 3), ("rm", 10)]));
        assert_eq!(result, EvalResult::Bool(true));
    }

    #[test]
    fn test_lo_condition_not_unsigned_less() {
        let rn = SmtExpr::var("rn", 32);
        let rm = SmtExpr::var("rm", 32);
        let flags = encode_cmp(rn, rm, 32);
        let cond = eval_condition(AArch64CC::LO, &flags);
        // 10 is NOT <_u 3
        let result = cond.eval(&env(&[("rn", 10), ("rm", 3)]));
        assert_eq!(result, EvalResult::Bool(false));
    }

    #[test]
    fn test_hi_condition_unsigned_greater() {
        let rn = SmtExpr::var("rn", 32);
        let rm = SmtExpr::var("rm", 32);
        let flags = encode_cmp(rn, rm, 32);
        let cond = eval_condition(AArch64CC::HI, &flags);
        // 10 >_u 3
        let result = cond.eval(&env(&[("rn", 10), ("rm", 3)]));
        assert_eq!(result, EvalResult::Bool(true));
    }

    #[test]
    fn test_gt_condition_signed_greater() {
        let rn = SmtExpr::var("rn", 32);
        let rm = SmtExpr::var("rm", 32);
        let flags = encode_cmp(rn, rm, 32);
        let cond = eval_condition(AArch64CC::GT, &flags);
        // 0 > -1 (signed)
        let result = cond.eval(&env(&[("rn", 0), ("rm", 0xFFFF_FFFF)]));
        assert_eq!(result, EvalResult::Bool(true));
    }

    // -----------------------------------------------------------------------
    // CSET tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_cset_eq_equal() {
        let rn = SmtExpr::var("rn", 32);
        let rm = SmtExpr::var("rm", 32);
        let cset = encode_cmp_cset(rn, rm, 32, AArch64CC::EQ);
        let result = cset.eval(&env(&[("rn", 42), ("rm", 42)]));
        assert_eq!(result, EvalResult::Bv(1));
    }

    #[test]
    fn test_cset_eq_not_equal() {
        let rn = SmtExpr::var("rn", 32);
        let rm = SmtExpr::var("rm", 32);
        let cset = encode_cmp_cset(rn, rm, 32, AArch64CC::EQ);
        let result = cset.eval(&env(&[("rn", 42), ("rm", 43)]));
        assert_eq!(result, EvalResult::Bv(0));
    }

    #[test]
    fn test_cset_lt_negative() {
        let rn = SmtExpr::var("rn", 32);
        let rm = SmtExpr::var("rm", 32);
        let cset = encode_cmp_cset(rn, rm, 32, AArch64CC::LT);
        // -5 < 5 -> CSET produces 1
        let neg5 = 0xFFFF_FFFBu64;
        let result = cset.eval(&env(&[("rn", neg5), ("rm", 5)]));
        assert_eq!(result, EvalResult::Bv(1));
    }

    #[test]
    fn test_cset_lo_unsigned() {
        let rn = SmtExpr::var("rn", 32);
        let rm = SmtExpr::var("rm", 32);
        let cset = encode_cmp_cset(rn, rm, 32, AArch64CC::LO);
        // 3 <_u 10 -> CSET produces 1
        let result = cset.eval(&env(&[("rn", 3), ("rm", 10)]));
        assert_eq!(result, EvalResult::Bv(1));
    }

    // -----------------------------------------------------------------------
    // 64-bit tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_cmp_64bit_zero() {
        let rn = SmtExpr::var("rn", 64);
        let rm = SmtExpr::var("rm", 64);
        let flags = encode_cmp(rn, rm, 64);
        // Equal values -> Z=true
        let result = flags.z.eval(&env(&[
            ("rn", 0x1234_5678_9ABC_DEF0),
            ("rm", 0x1234_5678_9ABC_DEF0),
        ]));
        assert_eq!(result, EvalResult::Bool(true));
    }

    #[test]
    fn test_cmp_64bit_negative() {
        let rn = SmtExpr::var("rn", 64);
        let rm = SmtExpr::var("rm", 64);
        let flags = encode_cmp(rn, rm, 64);
        // 0 - 1 = max (negative in signed) -> N=true
        let result = flags.n.eval(&env(&[("rn", 0), ("rm", 1)]));
        assert_eq!(result, EvalResult::Bool(true));
    }

    // -----------------------------------------------------------------------
    // AddWithCarry producers (ADDS/SUBS/ADCS/SBCS, ADC/SBC values)
    // -----------------------------------------------------------------------

    fn packed(flags: &NzcvFlags, bindings: &HashMap<String, u64>) -> u64 {
        match pack_nzcv(flags).eval(bindings) {
            EvalResult::Bv(value) => value,
            other => panic!("packed NZCV evaluated to {other:?}"),
        }
    }

    /// Independent integer oracle for AddWithCarry at `width` bits.
    fn oracle(x: u64, y: u64, carry: u64, width: u32) -> (u64, u64) {
        let mask = (1u128 << width) - 1;
        let (x, y) = (u128::from(x) & mask, u128::from(y) & mask);
        let unsigned = x + y + u128::from(carry);
        let result = unsigned & mask;
        let signed = |v: u128| -> i128 {
            if v >> (width - 1) & 1 == 1 {
                v as i128 - (1i128 << width)
            } else {
                v as i128
            }
        };
        let signed_sum = signed(x) + signed(y) + carry as i128;
        let n = (result >> (width - 1)) as u64;
        let z = u64::from(result == 0);
        let c = u64::from(unsigned != result);
        let v = u64::from(signed_sum != signed(result));
        (result as u64, (n << 3) | (z << 2) | (c << 1) | v)
    }

    #[test]
    fn add_with_carry_matches_an_integer_oracle_exhaustively_at_8_bits() {
        let mut cases = 0;
        let x = SmtExpr::var("x", 8);
        let y = SmtExpr::var("y", 8);
        let c = SmtExpr::var("c", 1);
        let (result, flags) = add_with_carry(x, y, c, 8);
        for a in 0..=255u64 {
            for b in 0..=255u64 {
                for carry in 0..=1u64 {
                    let bindings = env(&[("x", a), ("y", b), ("c", carry)]);
                    let (want_result, want_flags) = oracle(a, b, carry, 8);
                    assert_eq!(result.eval(&bindings), EvalResult::Bv(want_result));
                    assert_eq!(packed(&flags, &bindings), want_flags, "{a} {b} {carry}");
                    cases += 1;
                }
            }
        }
        assert_eq!(cases, 131_072);
    }

    /// SUBS/CMP via AddWithCarry(Rn, NOT Rm, 1) and the full-adder `encode_cmp`
    /// are separate transcriptions; they must agree on every 8-bit pair.
    #[test]
    fn subs_and_encode_cmp_agree_exhaustively_at_8_bits() {
        let rn = SmtExpr::var("rn", 8);
        let rm = SmtExpr::var("rm", 8);
        let (result, subs) = encode_subs(rn.clone(), rm.clone(), 8);
        let cmp = encode_cmp(rn, rm, 8);
        for a in 0..=255u64 {
            for b in 0..=255u64 {
                let bindings = env(&[("rn", a), ("rm", b)]);
                assert_eq!(packed(&subs, &bindings), packed(&cmp, &bindings));
                assert_eq!(
                    result.eval(&bindings),
                    EvalResult::Bv(a.wrapping_sub(b) & 0xff)
                );
            }
        }
    }

    #[test]
    fn carry_readers_use_the_incoming_c_flag_and_wide_values() {
        let rn = SmtExpr::var("rn", 64);
        let rm = SmtExpr::var("rm", 64);
        let carry = SmtExpr::var("c", 1);
        let adc = encode_adc(rn.clone(), rm.clone(), carry.clone(), 64);
        let sbc = encode_sbc(rn.clone(), rm.clone(), carry.clone(), 64);
        let (_, adcs) = encode_adcs(rn.clone(), rm.clone(), carry.clone(), 64);
        let (_, sbcs) = encode_sbcs(rn, rm, carry, 64);
        for (a, b) in [
            (u64::MAX, 0),
            (u64::MAX, u64::MAX),
            (0x7fff_ffff_ffff_ffff, 0),
            (0, 0),
            (0x8000_0000_0000_0000, 1),
        ] {
            for c in 0..=1u64 {
                let bindings = env(&[("rn", a), ("rm", b), ("c", c)]);
                let (want_adc, want_adcs) = oracle(a, b, c, 64);
                let (want_sbc, want_sbcs) = oracle(a, !b, c, 64);
                assert_eq!(adc.eval(&bindings), EvalResult::Bv(want_adc));
                assert_eq!(sbc.eval(&bindings), EvalResult::Bv(want_sbc));
                assert_eq!(packed(&adcs, &bindings), want_adcs);
                assert_eq!(packed(&sbcs, &bindings), want_sbcs);
            }
        }
        // The C flag round-trips as a 1-bit adder input.
        let flags = NzcvFlags {
            n: SmtExpr::bool_const(false),
            z: SmtExpr::bool_const(false),
            c: SmtExpr::bool_const(true),
            v: SmtExpr::bool_const(false),
        };
        assert_eq!(carry_bit(&flags).eval(&env(&[])), EvalResult::Bv(1));
        assert_eq!(packed(&flags, &env(&[])), 0b0010);
    }
}
