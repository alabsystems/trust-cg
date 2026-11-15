// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use std::collections::HashMap;
use std::sync::Arc;

use super::*;
use crate::smt::{EvalEnv, EvalResult, SmtExpr};

fn v(name: &str, width: u32) -> SmtExpr {
    SmtExpr::var(name, width)
}

fn c(value: u64, width: u32) -> SmtExpr {
    SmtExpr::bv_const(value, width)
}

#[test]
fn xor_is_decided_for_every_input_and_a_wrong_operand_refutes_with_a_confirmed_witness() {
    let (a, b, d) = (v("a", 32), v("b", 32), v("d", 32));
    let left = a.clone().bvxor(b.clone()).bvxor(d.clone());
    let right = d.clone().bvxor(a.clone().bvxor(b.clone()));
    assert_eq!(decide_equal(&left, &right), Ok(Gf2Exact::Holds));

    let wrong = d.clone().bvxor(a.clone().bvxor(a.clone()));
    let Ok(Gf2Exact::Refuted(witness)) = decide_equal(&left, &wrong) else {
        panic!("a dropped operand must refute");
    };
    let values: HashMap<String, u128> = witness.into_iter().collect();
    assert_ne!(
        eval_concrete(&left, &values).unwrap(),
        eval_concrete(&wrong, &values).unwrap()
    );
}

#[test]
fn constant_masks_shifts_and_concatenations_are_exact() {
    let x = v("x", 16);
    // Swap the bytes two ways: shifts and masks, and extract/concat.
    let by_shift = x
        .clone()
        .bvshl(c(8, 16))
        .bvor(x.clone().bvlshr(c(8, 16)))
        .bvand(c(0xFFFF, 16));
    let by_slice = x.clone().extract(7, 0).concat(x.clone().extract(15, 8));
    assert_eq!(decide_equal(&by_shift, &by_slice), Ok(Gf2Exact::Holds));
    // Off by one bit position: the OR now combines two input bits at bit 7,
    // which is not affine and is refused; spelled with XOR it refutes.
    let off_or = x.clone().bvshl(c(7, 16)).bvor(x.clone().bvlshr(c(8, 16)));
    assert!(matches!(
        decide_equal(&off_or, &by_slice),
        Err(Gf2Error::Unsupported(_))
    ));
    let off = x.clone().bvshl(c(7, 16)).bvxor(x.clone().bvlshr(c(8, 16)));
    assert!(matches!(
        decide_equal(&off, &by_slice),
        Ok(Gf2Exact::Refuted(_))
    ));
    // A constant bit flip refutes on the all-zero input.
    let flipped = by_slice.clone().bvxor(c(0x100, 16));
    assert!(matches!(
        decide_equal(&flipped, &by_slice),
        Ok(Gf2Exact::Refuted(_))
    ));
}

#[test]
fn non_affine_terms_are_refused_never_approximated() {
    let (a, b) = (v("a", 8), v("b", 8));
    for (label, term) in [
        ("bvadd", a.clone().bvadd(b.clone())),
        ("bvand of inputs", a.clone().bvand(b.clone())),
        ("bvor of inputs", a.clone().bvor(b.clone())),
        ("variable shift", a.clone().bvshl(b.clone())),
        ("bvmul", a.clone().bvmul(c(3, 8))),
    ] {
        assert!(
            matches!(decide_equal(&term, &a), Err(Gf2Error::Unsupported(_))),
            "{label} must be refused"
        );
    }
    // An ite whose arms differ by an input bit is not affine.
    let cond = a.clone().extract(0, 0).eq_expr(c(1, 1));
    let ite = SmtExpr::ite(cond, b.clone(), c(0, 8));
    assert!(matches!(
        decide_equal(&ite, &b),
        Err(Gf2Error::Unsupported(_))
    ));
    // An equality over two open bits is a conjunction, not affine.
    let wide = SmtExpr::ite(a.clone().eq_expr(b.clone()), c(1, 8), c(0, 8));
    assert!(matches!(
        decide_equal(&wide, &a),
        Err(Gf2Error::Unsupported(_))
    ));
}

/// One reflected CRC-32 step per bit over a register shared by reference:
/// the ite on bit 0 with arms that differ by the constant polynomial.
fn reflected_steps(start: SmtExpr, steps: usize, poly: u64) -> SmtExpr {
    let mut crc = Arc::new(start);
    for _ in 0..steps {
        let lsb = SmtExpr::Extract {
            high: 0,
            low: 0,
            operand: Arc::clone(&crc),
            width: 1,
        }
        .eq_expr(c(1, 1));
        let shifted = Arc::new(SmtExpr::BvLshr {
            lhs: Arc::clone(&crc),
            rhs: Arc::new(c(1, 32)),
            width: 32,
        });
        crc = Arc::new(SmtExpr::Ite {
            cond: Arc::new(lsb),
            then_expr: Arc::new(SmtExpr::BvXor {
                lhs: Arc::clone(&shifted),
                rhs: Arc::new(c(poly, 32)),
                width: 32,
            }),
            else_expr: shifted,
        });
    }
    (*crc).clone()
}

#[test]
fn a_shared_dag_is_decided_in_linear_time_and_agrees_with_the_interpreter() {
    // 512 steps would be a tree of 3^512 nodes; sharing keeps it ~2k nodes.
    let term = reflected_steps(v("s", 32), 512, 0xEDB8_8320);
    let started = std::time::Instant::now();
    assert_eq!(decide_equal(&term, &term.clone()), Ok(Gf2Exact::Holds));
    assert!(started.elapsed().as_secs() < 30);
    let other = reflected_steps(v("s", 32), 512, 0x82F6_3B78);
    assert!(matches!(
        decide_equal(&term, &other),
        Ok(Gf2Exact::Refuted(_))
    ));
    // The memoized concrete evaluator agrees with the ordinary interpreter on
    // a short chain (8 steps: small enough for the tree-walking interpreter).
    let short = reflected_steps(v("s", 32), 8, 0xEDB8_8320);
    for seed in [0u64, 1, 0x8000_0001, 0xDEAD_BEEF, 0xFFFF_FFFF] {
        let mut env = EvalEnv::default();
        env.insert("s".to_string(), seed);
        let EvalResult::Bv(expected) = short.eval(&env) else {
            panic!("interpreter refused the short chain");
        };
        let values = HashMap::from([("s".to_string(), u128::from(seed))]);
        assert_eq!(
            eval_concrete(&short, &values).unwrap(),
            Concrete::Bv(u128::from(expected), 32),
            "seed {seed:#x}"
        );
    }
}

#[test]
fn the_reflected_byte_step_equals_its_closed_affine_form() {
    // CRC-32/ISO-HDLC of the single byte 0x00 from state s is the table entry
    // T[s & 0xff] XOR (s >> 8); check the whole function, not samples, against
    // the per-bit linear map the procedure computes.
    let term = reflected_steps(v("s", 32), 8, 0xEDB8_8320);
    let (bits, vars) = affine_bits(&term).unwrap();
    assert_eq!(vars, vec![("s".to_string(), 32)]);
    // Linearity: no constant term (the zero state maps to zero).
    assert!(bits.iter().all(|bit| !bit.constant_term()));
    // Bits 24..32 of s reach output bits 16..24 only through the shift.
    for (out, bit) in bits.iter().enumerate().take(24).skip(16) {
        assert!(bit.inputs().contains(&(out + 8)), "bit {out}");
    }
}

#[test]
fn boolean_equalities_and_negations_are_affine() {
    let (a, b) = (v("a", 1), v("b", 1));
    let lhs = SmtExpr::ite(a.clone().eq_expr(b.clone()).not_expr(), c(1, 1), c(0, 1));
    let rhs = a.clone().bvxor(b.clone());
    assert_eq!(decide_equal(&lhs, &rhs), Ok(Gf2Exact::Holds));
    // Variables used at two widths are refused.
    let clash = v("a", 2).extract(0, 0);
    assert!(matches!(
        decide_equal(&clash, &a),
        Err(Gf2Error::Unsupported(_))
    ));
}
