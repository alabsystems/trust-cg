// trust-cg-verify/src/derived_operator_lowering.rs - derived BV operators spelled by their SMT-LIB definitions
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Spell the DERIVED bit-vector operators by their SMT-LIB definitions.
//!
//! ## Why
//!
//! Clean's Carcara bit-blasts `bvult` and `bvslt` (`bitblast_ult`,
//! `bitblast_slt`) and `bvudiv`/`bvurem`, but it has no rule for `bvule`,
//! `bvuge`, `bvugt`, `bvsle`, `bvsge`, `bvsgt` or `bvsdiv`: its parser only
//! sort-checks them, and no rewrite relates them to the operators it blasts
//! (Clean `5390f432b8` loads no RARE rules). A certificate over a query that
//! mentions one of them can therefore never reach the empty clause, whatever
//! the solver does — 26 strict-gate obligations measured 2026-09-28 (UBFM/
//! SBFM/BFM encodings, the i128 shift pairs, FCVT half, the conversion round
//! trips, and every SDIV/IDIV lowering).
//!
//! ## What
//!
//! Each such operator is replaced by the definition SMT-LIB itself gives it
//! (the `FixedSizeBitVectors` theory / `QF_BV` logic):
//!
//! * `(bvule s t)` = `(not (bvult t s))`, `(bvuge s t)` = `(not (bvult s t))`,
//!   `(bvugt s t)` = `(bvult t s)`, and the signed three over `bvslt` alike;
//! * `(bvsdiv s t)` = the sign-bit case split over `bvudiv` and `bvneg`;
//! * `(bvashr s t)` = the sign-bit case split over `bvlshr` and complement,
//!   because Clean admits `bitblast_ashr` only inside a narrow domain.
//!
//! The rewrite is an EQUIVALENCE of the serialized query — the same formula
//! under SMT-LIB semantics, including division by zero, since it is the
//! standard's own definition — so an UNSAT certificate of the lowered query
//! is an UNSAT certificate of the original. It is used only as a later
//! attempt: see `ay_bridge::verify_with_ay_attributed`.

use crate::smt::SmtExpr;
use std::convert::Infallible;
use std::sync::Arc;

/// `formula` with every derived operator spelled by its definition, or
/// `None` when it mentions none.
pub fn lower_derived_operators(formula: &SmtExpr) -> Option<SmtExpr> {
    match formula.try_rewrite_dag::<Infallible>(&mut |node| Ok(definition(node))) {
        Ok(lowered) => lowered,
        Err(never) => match never {},
    }
}

/// The SMT-LIB definition of one derived node, or `None` for any other.
fn definition(node: &SmtExpr) -> Option<SmtExpr> {
    use SmtExpr as S;
    let ult = |lhs: &Arc<SmtExpr>, rhs: &Arc<SmtExpr>, width: u32| S::BvUlt {
        lhs: Arc::clone(lhs),
        rhs: Arc::clone(rhs),
        width,
    };
    let slt = |lhs: &Arc<SmtExpr>, rhs: &Arc<SmtExpr>, width: u32| S::BvSlt {
        lhs: Arc::clone(lhs),
        rhs: Arc::clone(rhs),
        width,
    };
    Some(match node {
        S::BvUle { lhs, rhs, width } => ult(rhs, lhs, *width).not_expr(),
        S::BvUge { lhs, rhs, width } => ult(lhs, rhs, *width).not_expr(),
        S::BvUgt { lhs, rhs, width } => ult(rhs, lhs, *width),
        S::BvSle { lhs, rhs, width } => slt(rhs, lhs, *width).not_expr(),
        S::BvSge { lhs, rhs, width } => slt(lhs, rhs, *width).not_expr(),
        S::BvSgt { lhs, rhs, width } => slt(rhs, lhs, *width),
        S::BvSDiv { lhs, rhs, width } => signed_division(lhs, rhs, *width)?,
        S::BvAshr { lhs, rhs, width } => arithmetic_shift(lhs, rhs, *width)?,
        _ => return None,
    })
}

/// SMT-LIB's `bvsdiv`:
///
/// ```text
/// (ite (and (= msb_s #b0) (= msb_t #b0)) (bvudiv s t)
/// (ite (and (= msb_s #b1) (= msb_t #b0)) (bvneg (bvudiv (bvneg s) t))
/// (ite (and (= msb_s #b0) (= msb_t #b1)) (bvneg (bvudiv s (bvneg t)))
///      (bvudiv (bvneg s) (bvneg t)))))
/// ```
fn signed_division(s: &Arc<SmtExpr>, t: &Arc<SmtExpr>, width: u32) -> Option<SmtExpr> {
    if width == 0 {
        return None;
    }
    let msb = |operand: &Arc<SmtExpr>| SmtExpr::Extract {
        high: width - 1,
        low: width - 1,
        operand: Arc::clone(operand),
        width: 1,
    };
    let bit = |value: u64| SmtExpr::BvConst { value, width: 1 };
    let is = |operand: &Arc<SmtExpr>, value: u64| msb(operand).eq_expr(bit(value));
    let neg = |operand: &Arc<SmtExpr>| SmtExpr::BvNeg {
        operand: Arc::clone(operand),
        width,
    };
    let udiv = |lhs: SmtExpr, rhs: SmtExpr| SmtExpr::BvUDiv {
        lhs: Arc::new(lhs),
        rhs: Arc::new(rhs),
        width,
    };
    let negate = |value: SmtExpr| SmtExpr::BvNeg {
        operand: Arc::new(value),
        width,
    };
    let (s_value, t_value) = ((**s).clone(), (**t).clone());
    Some(SmtExpr::ite(
        is(s, 0).and_expr(is(t, 0)),
        udiv(s_value.clone(), t_value.clone()),
        SmtExpr::ite(
            is(s, 1).and_expr(is(t, 0)),
            negate(udiv(neg(s), t_value.clone())),
            SmtExpr::ite(
                is(s, 0).and_expr(is(t, 1)),
                negate(udiv(s_value, neg(t))),
                udiv(neg(s), neg(t)),
            ),
        ),
    ))
}

/// SMT-LIB's `bvashr`:
///
/// ```text
/// (ite (= ((_ extract |m-1| |m-1|) s) #b0)
///      (bvlshr s t)
///      (bvnot (bvlshr (bvnot s) t)))
/// ```
///
/// Clean admits `bitblast_ashr` only when the operand is provably
/// non-negative or the amount provably below the width (its
/// `carcara_verify/ashr.rs`), so a shift by a symbolic amount — wasm's
/// `i32.shr_s` — is refused however it is guarded; `bitblast_lshr` has no
/// such domain. Overshift is the standard's too: `0` for a non-negative `s`,
/// all ones for a negative one.
fn arithmetic_shift(s: &Arc<SmtExpr>, t: &Arc<SmtExpr>, width: u32) -> Option<SmtExpr> {
    if width == 0 {
        return None;
    }
    let lshr = |lhs: SmtExpr| SmtExpr::BvLshr {
        lhs: Arc::new(lhs),
        rhs: Arc::clone(t),
        width,
    };
    let not = |operand: SmtExpr| bv_not(operand, width);
    let sign = SmtExpr::Extract {
        high: width - 1,
        low: width - 1,
        operand: Arc::clone(s),
        width: 1,
    };
    Some(SmtExpr::ite(
        sign.eq_expr(SmtExpr::BvConst { value: 0, width: 1 }),
        lshr((**s).clone()),
        not(lshr(not((**s).clone()))),
    ))
}

/// `(bvnot x)`: `SmtExpr` has no complement node, so it is `(bvxor x #b1…1)`
/// up to 64 bits and `(bvsub (bvneg x) 1)` — the same word, `-x - 1` — above,
/// where a `u64` literal cannot spell the mask.
fn bv_not(operand: SmtExpr, width: u32) -> SmtExpr {
    if width <= 64 {
        let ones = if width == 64 {
            u64::MAX
        } else {
            (1_u64 << width) - 1
        };
        return SmtExpr::BvXor {
            lhs: Arc::new(operand),
            rhs: Arc::new(SmtExpr::BvConst { value: ones, width }),
            width,
        };
    }
    SmtExpr::BvSub {
        lhs: Arc::new(SmtExpr::BvNeg {
            operand: Arc::new(operand),
            width,
        }),
        rhs: Arc::new(SmtExpr::BvConst { value: 1, width }),
        width,
    }
}

#[cfg(test)]
#[path = "derived_operator_lowering_tests.rs"]
mod tests;
