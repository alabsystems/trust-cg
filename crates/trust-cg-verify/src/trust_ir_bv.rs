// trust-cg-verify/src/trust_ir_bv.rs - trust-ir's bit-vector statement of
// integer compare, printed in this crate's SMT terms.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! [`SmtAlgebra`] instantiates trust-ir's one QF_BV statement of `ICmp`
//! (`trust_ir::bv_meaning`: `icmp_holds`, `vector_icmp`, `concat_lanes`; and
//! `trust_ir::chc_x86_vector_icmp_spec` / `physical_mask_lane` for the x86-64
//! vector-compare cells) over [`SmtExpr`], so this backend's spec side of a
//! compare obligation is trust-ir's statement and not a restatement of it.
//!
//! It is a PRINTING instance in the sense of trust-ir's instance contract
//! (`bv_meaning` module docs; `docs/SPEC_RATIFICATIONS.md`, "Integer compare
//! has one bit-vector statement"): every method is exactly one `SmtExpr`
//! constructor, and none rewrites an operator, so the term it builds is the
//! statement node for node. `smt_algebra_reads_as_trust_irs_concrete_algebra`
//! holds the evaluation of what it prints equal to trust-ir's `Concrete`
//! instance (test rung).
//!
//! Independence (design §3.5): this backend's x86 INSTRUCTION models
//! (`x86_64_semantics.rs`: `packed_lane_mask`, `encode_pcmp*`, `encode_p*`)
//! never route through this module or through `physical_mask_lane` /
//! `chc_x86_vector_icmp_spec`; otherwise the eight instruction-model cells
//! (`icmp.eq` / `icmp.sgt`) would be degenerate by shared code rather than
//! because the instruction model equals the format's meaning.
//! `x86_instruction_models_do_not_share_the_spec_statement` holds that by scan.

use trust_ir::bv_meaning::{BvCompare, BvVector};

use crate::smt::SmtExpr;

/// trust-ir's bit-vector statement over [`SmtExpr`]: one node per method.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct SmtAlgebra;

impl BvCompare for SmtAlgebra {
    type Bv = SmtExpr;
    type Bool = SmtExpr;

    fn eq(&mut self, a: SmtExpr, b: SmtExpr) -> SmtExpr {
        a.eq_expr(b)
    }

    fn not(&mut self, b: SmtExpr) -> SmtExpr {
        b.not_expr()
    }

    fn ult(&mut self, a: SmtExpr, b: SmtExpr) -> SmtExpr {
        a.bvult(b)
    }

    fn ule(&mut self, a: SmtExpr, b: SmtExpr) -> SmtExpr {
        a.bvule(b)
    }

    fn ugt(&mut self, a: SmtExpr, b: SmtExpr) -> SmtExpr {
        a.bvugt(b)
    }

    fn uge(&mut self, a: SmtExpr, b: SmtExpr) -> SmtExpr {
        a.bvuge(b)
    }

    fn slt(&mut self, a: SmtExpr, b: SmtExpr) -> SmtExpr {
        a.bvslt(b)
    }

    fn sle(&mut self, a: SmtExpr, b: SmtExpr) -> SmtExpr {
        a.bvsle(b)
    }

    fn sgt(&mut self, a: SmtExpr, b: SmtExpr) -> SmtExpr {
        a.bvsgt(b)
    }

    fn sge(&mut self, a: SmtExpr, b: SmtExpr) -> SmtExpr {
        a.bvsge(b)
    }
}

impl BvVector for SmtAlgebra {
    /// `SmtExpr::BvConst` holds a `u64`. The statement asks only for lane
    /// constants (`physical_mask_lane`: all-ones and zero at the lane width),
    /// and every lane this backend states is at most 64 bits wide, so a wider
    /// constant is a caller error, not a value to truncate.
    fn bv_const(&mut self, value: u128, width: u32) -> SmtExpr {
        assert!(
            width <= 64,
            "SmtAlgebra::bv_const: a {width}-bit constant; SmtExpr constants are at most 64 bits"
        );
        let value = u64::try_from(value).expect("a constant of at most 64 bits fits u64");
        SmtExpr::bv_const(value, width)
    }

    fn extract(&mut self, v: SmtExpr, high: u32, low: u32) -> SmtExpr {
        v.extract(high, low)
    }

    fn concat(&mut self, high: SmtExpr, low: SmtExpr) -> SmtExpr {
        high.concat(low)
    }

    fn ite(&mut self, c: SmtExpr, t: SmtExpr, e: SmtExpr) -> SmtExpr {
        SmtExpr::ite(c, t, e)
    }
}

/// trust-ir's spec side of the x86-64 vector-compare cell `icmp.<op>` over
/// `<lane_count x i<lane_bits>>` (`trust_ir::chc_x86_vector_icmp_spec`),
/// printed over [`SmtExpr`]: `None` exactly where no `chc_x86` descriptor
/// governs the shape.
#[must_use]
pub fn chc_x86_vector_icmp_spec(
    lane_bits: u32,
    lane_count: u32,
    op: trust_ir::ICmpOp,
    lhs: &SmtExpr,
    rhs: &SmtExpr,
) -> Option<SmtExpr> {
    trust_ir::chc_x86_vector_icmp_spec(&mut SmtAlgebra, lane_bits, lane_count, op, lhs, rhs)
}

/// trust-ir's lane-wise compare of two `lane_count x lane_bits` vectors, each
/// lane carried as the hardware contracts' physical mask lane
/// (`trust_ir::physical_mask_lane`: all-ones where the predicate holds, zero
/// where it fails) and the lanes recomposed lane 0 least significant. Unlike
/// [`chc_x86_vector_icmp_spec`] it is not keyed on a governed descriptor, so it
/// also states the shapes the `chc_x86` manifest does not cover.
#[must_use]
pub fn vector_icmp_physical_mask(
    op: trust_ir::ICmpOp,
    lane_bits: u32,
    lane_count: u32,
    lhs: &SmtExpr,
    rhs: &SmtExpr,
) -> SmtExpr {
    let mut algebra = SmtAlgebra;
    let holds =
        trust_ir::bv_meaning::vector_icmp(&mut algebra, op, lane_bits, lane_count, lhs, rhs);
    let lanes = holds
        .into_iter()
        .map(|held| trust_ir::physical_mask_lane(&mut algebra, held, lane_bits))
        .collect();
    trust_ir::bv_meaning::concat_lanes(&mut algebra, lanes)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::{EvalEnv, EvalResult};
    use trust_ir::ICmpOp;
    use trust_ir::bv_meaning::{Concrete, icmp_holds};

    const OPS: [ICmpOp; 10] = [
        ICmpOp::Eq,
        ICmpOp::Ne,
        ICmpOp::Ult,
        ICmpOp::Ule,
        ICmpOp::Ugt,
        ICmpOp::Uge,
        ICmpOp::Slt,
        ICmpOp::Sle,
        ICmpOp::Sgt,
        ICmpOp::Sge,
    ];

    /// `(lane bits, lanes)` of every `chc_x86` descriptor.
    const SHAPES: [(u32, u32); 4] = [(8, 16), (16, 8), (32, 4), (64, 2)];

    fn bool_of(result: EvalResult) -> bool {
        match result {
            EvalResult::Bool(value) => value,
            other => panic!("expected a Bool, got {other:?}"),
        }
    }

    fn bv128_of(result: EvalResult) -> u128 {
        match result {
            EvalResult::Bv128(value) => value,
            EvalResult::Bv(value) => u128::from(value),
            other => panic!("expected a bit-vector, got {other:?}"),
        }
    }

    /// `lhs`/`rhs` as the obligations spell a 128-bit operand: two 64-bit
    /// variables, high half first.
    fn operand(prefix: &str) -> SmtExpr {
        SmtExpr::var(format!("{prefix}_hi"), 64).concat(SmtExpr::var(format!("{prefix}_lo"), 64))
    }

    fn bind(env: &mut EvalEnv, prefix: &str, value: u128) {
        env.insert(format!("{prefix}_lo"), value as u64);
        env.insert(format!("{prefix}_hi"), (value >> 64) as u64);
    }

    /// Edge values of a `width`-bit lane: zero, one, the signed extremes and
    /// their neighbours, all-ones.
    fn edges(width: u32) -> Vec<u128> {
        let ones = trust_ir::bv_meaning::all_ones(width);
        let sign = 1u128 << (width - 1);
        vec![0, 1, 2, sign - 1, sign, sign + 1, ones - 1, ones]
    }

    /// A deterministic lane stream (splitmix64), so the sampled pairs are the
    /// same on every run.
    fn next(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// The scalar statement at 8 bits, exhaustively: what `SmtAlgebra` prints
    /// evaluates to `Concrete`'s answer on every pair.
    #[test]
    fn smt_algebra_scalar_compare_is_concretes_at_8_bits() {
        let env = EvalEnv::default();
        for op in OPS {
            for a in 0..=u8::MAX {
                for b in 0..=u8::MAX {
                    let printed = icmp_holds(
                        &mut SmtAlgebra,
                        op,
                        SmtExpr::bv_const(u64::from(a), 8),
                        SmtExpr::bv_const(u64::from(b), 8),
                    );
                    let want =
                        icmp_holds(&mut Concrete, op, (u128::from(a), 8), (u128::from(b), 8));
                    assert_eq!(
                        bool_of(printed.try_eval(&env).expect("evaluates")),
                        want,
                        "{op:?} {a:#04x} {b:#04x}"
                    );
                }
            }
        }
    }

    /// B-T3b: the x86-64 cells' spec side printed by `SmtAlgebra` reads as
    /// trust-ir's `Concrete` algebra on the same operand images, for every
    /// descriptor and predicate: every `<16 x i8>` byte pair (sixteen pairs per
    /// vector, rotated through the lanes) and, at 16/32/64 bits, every pair of
    /// edge values plus seeded pairs. Test rung, not proof. Mutation (measured
    /// in the commit that adds it): `SmtAlgebra::uge` printed as `bvugt` turns
    /// it red.
    #[test]
    fn smt_algebra_reads_as_trust_irs_concrete_algebra() {
        let (lhs, rhs) = (operand("lhs"), operand("rhs"));
        let mut env = EvalEnv::default();
        let mut checked = 0usize;
        for (lane_bits, lane_count) in SHAPES {
            let mut pairs: Vec<(u128, u128)> = Vec::new();
            if lane_bits == 8 {
                for a in 0..=255u128 {
                    for b in 0..=255u128 {
                        pairs.push((a, b));
                    }
                }
            } else {
                for a in edges(lane_bits) {
                    for b in edges(lane_bits) {
                        pairs.push((a, b));
                    }
                }
                let mut state = 0x7472_7573_742d_6367_u64 ^ u64::from(lane_bits);
                let mask = trust_ir::bv_meaning::all_ones(lane_bits);
                for _ in 0..512 {
                    let a = u128::from(next(&mut state)) & mask;
                    let b = u128::from(next(&mut state)) & mask;
                    pairs.push((a, b));
                }
            }
            for op in OPS {
                let printed = chc_x86_vector_icmp_spec(lane_bits, lane_count, op, &lhs, &rhs)
                    .expect("every chc_x86 descriptor governs every ICmpOp");
                for (chunk_index, chunk) in pairs.chunks(lane_count as usize).enumerate() {
                    let (mut l, mut r) = (0u128, 0u128);
                    for lane in 0..lane_count as usize {
                        // Rotate the chunk through the lanes so each pair
                        // visits a different lane position across chunks.
                        let (a, b) = chunk[(lane + chunk_index) % chunk.len()];
                        l |= a << (lane as u32 * lane_bits);
                        r |= b << (lane as u32 * lane_bits);
                    }
                    bind(&mut env, "lhs", l);
                    bind(&mut env, "rhs", r);
                    let want = trust_ir::chc_x86_vector_icmp_spec(
                        &mut Concrete,
                        lane_bits,
                        lane_count,
                        op,
                        &(l, 128),
                        &(r, 128),
                    )
                    .expect("governed")
                    .0;
                    let got = bv128_of(printed.try_eval(&env).expect("evaluates"));
                    assert_eq!(
                        got, want,
                        "<{lane_count} x i{lane_bits}> {op:?}: lhs {l:#034x} rhs {r:#034x}"
                    );
                    checked += 1;
                }
            }
        }
        assert!(checked > 40_000, "only {checked} vectors checked");
    }

    /// The ungoverned-shape twin states the same tree as the cell spec on a
    /// governed shape.
    #[test]
    fn vector_icmp_physical_mask_is_the_cell_spec_on_governed_shapes() {
        let (lhs, rhs) = (operand("lhs"), operand("rhs"));
        for (lane_bits, lane_count) in SHAPES {
            for op in OPS {
                assert_eq!(
                    vector_icmp_physical_mask(op, lane_bits, lane_count, &lhs, &rhs),
                    chc_x86_vector_icmp_spec(lane_bits, lane_count, op, &lhs, &rhs)
                        .expect("governed"),
                    "<{lane_count} x i{lane_bits}> {op:?}"
                );
            }
        }
    }
}
