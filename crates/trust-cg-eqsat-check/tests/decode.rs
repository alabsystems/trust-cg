// trust-cg-eqsat-check/tests/decode.rs - section 7.2 decoding and canonicity refusals
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A hand-encoded canonical derivation is accepted; each byte-level fault and
//! each canonicity rule of docs/eqsat-tier-e.md section 7.2, broken one at a
//! time, is rejected with its class (`decode` or `non_canonical`, with the
//! specific kind).

mod common;

use common::*;
use trust_cg_eqsat_check::{DecodeError, NonCanonicalKind, Rejection};

fn non_canonical(r: &Result<trust_cg_eqsat_check::Verdict, Rejection>) -> NonCanonicalKind {
    match r {
        Err(Rejection::NonCanonical { kind, .. }) => *kind,
        other => panic!("expected non_canonical, got {other:?}"),
    }
}

fn decode_err(r: &Result<trust_cg_eqsat_check::Verdict, Rejection>) -> DecodeError {
    match r {
        Err(Rejection::Decode { detail, .. }) => detail.clone(),
        other => panic!("expected decode, got {other:?}"),
    }
}

#[test]
fn canonical_derivations_are_accepted() {
    let reg = registry();
    let a = run(A_IN, A_OUT, &a_deriv(&reg), &reg).expect("A accepted");
    assert_eq!(a.claims, 1);
    assert_eq!(a.proof_steps, 1);
    assert_eq!(a.rules_used, vec!["mul_one".to_owned()]);
    assert_eq!(a.skeleton_operands, 3);
    assert_eq!(a.changed_operands, 1);
    let b = run(B_IN, B_OUT, &b_deriv(&reg), &reg).expect("B accepted");
    assert_eq!(b.proof_steps, 3);
    assert_eq!(
        b.rules_used,
        vec!["add_zero".to_owned(), "mul_one".to_owned()]
    );
    let c = run(C_IN, C_OUT, &c_deriv(&reg), &reg).expect("C accepted");
    assert_eq!(c.claims, 1);
}

#[test]
fn byte_level_faults() {
    let reg = registry();
    let good = a_deriv(&reg).encode();

    let truncated = &good[..good.len() - 1];
    let r = run_bytes(A_IN, A_OUT, truncated, &reg);
    assert!(
        matches!(decode_err(&r), DecodeError::Truncated { .. }),
        "{r:?}"
    );

    let r = run_bytes(A_IN, A_OUT, &[], &reg);
    assert!(
        matches!(decode_err(&r), DecodeError::Truncated { .. }),
        "{r:?}"
    );

    let mut bad_magic = good.clone();
    bad_magic[0] = b'X';
    let r = run_bytes(A_IN, A_OUT, &bad_magic, &reg);
    assert_eq!(decode_err(&r), DecodeError::BadMagic);

    let mut bad_version = good.clone();
    bad_version[8] = 2;
    let r = run_bytes(A_IN, A_OUT, &bad_version, &reg);
    assert_eq!(decode_err(&r), DecodeError::BadVersion { version: 2 });

    let mut trailing = good.clone();
    trailing.push(0);
    let r = run_bytes(A_IN, A_OUT, &trailing, &reg);
    assert_eq!(decode_err(&r), DecodeError::TrailingBytes { count: 1 });

    // Bad term tag: rebuild with a raw term byte patched.
    let mut d = a_deriv(&reg);
    d.terms = vec![T::Param(0, 0)];
    let mut bytes = d.encode();
    let tag_at = bytes.len() - (4 + 1 + 4 + 4 + (1 + 4 + 1 + 4 + 4 + 1 + 4 + 4) + 4 + 4);
    assert_eq!(bytes[tag_at], 0x01, "located the term tag");
    bytes[tag_at] = 0x09;
    let r = run_bytes(A_IN, A_OUT, &bytes, &reg);
    assert!(
        matches!(decode_err(&r), DecodeError::BadTag { tag: 0x09, .. }),
        "{r:?}"
    );

    // Bad type code (instance type).
    let mut d = a_deriv(&reg);
    d.proofs = vec![rule(0, 0x99, &[("x", 0)], &[])];
    let r = run(A_IN, A_OUT, &d, &reg);
    assert!(
        matches!(decode_err(&r), DecodeError::BadCode { code: 0x99, .. }),
        "{r:?}"
    );

    // Bad operator code (bin op 12).
    let mut d = b_deriv(&reg);
    d.terms[2] = T::Op(OpD::Bin(12, U32), vec![0, 1]);
    let r = run(B_IN, B_OUT, &d, &reg);
    assert!(
        matches!(decode_err(&r), DecodeError::BadCode { code: 12, .. }),
        "{r:?}"
    );

    // Bad proof tag.
    let mut bytes = a_deriv(&reg).encode();
    let proof_tag_at = bytes.len() - (1 + 4 + 1 + 4 + 4 + 1 + 4 + 4 + 4 + 4);
    assert_eq!(bytes[proof_tag_at], 0x05, "located the proof tag");
    bytes[proof_tag_at] = 0x06;
    let r = run_bytes(A_IN, A_OUT, &bytes, &reg);
    assert!(
        matches!(decode_err(&r), DecodeError::BadTag { tag: 0x06, .. }),
        "{r:?}"
    );

    // A claim naming no proof.
    let mut d = a_deriv(&reg);
    d.claims = vec![5];
    let r = run(A_IN, A_OUT, &d, &reg);
    assert!(
        matches!(
            decode_err(&r),
            DecodeError::IndexOutOfRange { index: 5, .. }
        ),
        "{r:?}"
    );

    // A function name that is not UTF-8.
    let mut bytes = a_deriv(&reg).encode();
    bytes[16] = 0xff; // the single byte of "f"
    let r = run_bytes(A_IN, A_OUT, &bytes, &reg);
    assert_eq!(decode_err(&r), DecodeError::BadUtf8);
}

#[test]
fn function_name_must_match() {
    let reg = registry();
    let mut d = a_deriv(&reg);
    d.function = "g".to_owned();
    let r = run(A_IN, A_OUT, &d, &reg);
    assert_eq!(class(&r), "function_name_mismatch");
}

#[test]
fn term_order() {
    let reg = registry();
    let mut d = b_deriv(&reg);
    d.terms[2] = T::Op(OpD::Bin(ADD, U32), vec![0, 2]);
    assert_eq!(
        non_canonical(&run(B_IN, B_OUT, &d, &reg)),
        NonCanonicalKind::TermOrder
    );
}

#[test]
fn proof_order() {
    let reg = registry();
    let mut d = b_deriv(&reg);
    d.proofs[2] = P::Trans(0, 2);
    assert_eq!(
        non_canonical(&run(B_IN, B_OUT, &d, &reg)),
        NonCanonicalKind::ProofOrder
    );
}

#[test]
fn duplicate_term() {
    let reg = registry();
    let mut d = b_deriv(&reg);
    d.terms.push(T::Const(U32, 0));
    assert_eq!(
        non_canonical(&run(B_IN, B_OUT, &d, &reg)),
        NonCanonicalKind::DuplicateTerm
    );
}

#[test]
fn duplicate_proof() {
    let reg = registry();
    let mut d = b_deriv(&reg);
    d.proofs.push(rule(0, U32, &[("x", 0)], &[]));
    assert_eq!(
        non_canonical(&run(B_IN, B_OUT, &d, &reg)),
        NonCanonicalKind::DuplicateProof
    );
}

#[test]
fn unreachable_term() {
    let reg = registry();
    let mut d = b_deriv(&reg);
    d.terms.push(T::Const(U32, 7));
    assert_eq!(
        non_canonical(&run(B_IN, B_OUT, &d, &reg)),
        NonCanonicalKind::UnreachableTerm
    );
}

#[test]
fn unreachable_proof() {
    let reg = registry();
    let mut d = b_deriv(&reg);
    d.proofs.push(P::Refl(0));
    assert_eq!(
        non_canonical(&run(B_IN, B_OUT, &d, &reg)),
        NonCanonicalKind::UnreachableProof
    );
}

#[test]
fn unreachable_rule() {
    let reg = registry();
    let d = b_deriv(&reg).with_rule(&reg, "rotl_full");
    assert_eq!(
        non_canonical(&run(B_IN, B_OUT, &d, &reg)),
        NonCanonicalKind::UnreachableRule
    );
}

#[test]
fn claims_order() {
    let reg = registry();
    let mut d = b_deriv(&reg);
    d.claims = vec![2, 1];
    assert_eq!(
        non_canonical(&run(B_IN, B_OUT, &d, &reg)),
        NonCanonicalKind::ClaimsOrder
    );
    d.claims = vec![2, 2];
    assert_eq!(
        non_canonical(&run(B_IN, B_OUT, &d, &reg)),
        NonCanonicalKind::ClaimsOrder
    );
}

#[test]
fn unsorted_rule_table() {
    let reg = registry();
    let mut d = b_deriv(&reg);
    d.rules.swap(0, 1);
    d.proofs = vec![
        rule(0, U32, &[("x", 2)], &[]),
        rule(1, U32, &[("x", 0)], &[]),
        P::Trans(0, 1),
    ];
    assert_eq!(
        non_canonical(&run(B_IN, B_OUT, &d, &reg)),
        NonCanonicalKind::UnsortedRuleTable
    );
    let mut d = b_deriv(&reg);
    let dup = d.rules[0].clone();
    d.rules.insert(1, dup);
    assert_eq!(
        non_canonical(&run(B_IN, B_OUT, &d, &reg)),
        NonCanonicalKind::UnsortedRuleTable
    );
}

#[test]
fn unsorted_bindings() {
    let reg = registry();
    let mut d = c_deriv(&reg);
    d.proofs = vec![rule(0, U32, &[("y", 1), ("x", 0)], &[])];
    assert_eq!(
        non_canonical(&run(C_IN, C_OUT, &d, &reg)),
        NonCanonicalKind::UnsortedBindings
    );
    d.proofs = vec![rule(0, U32, &[("x", 0), ("x", 1)], &[])];
    assert_eq!(
        non_canonical(&run(C_IN, C_OUT, &d, &reg)),
        NonCanonicalKind::UnsortedBindings
    );
}
