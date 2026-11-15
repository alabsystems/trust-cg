// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Solver-free tests of the split-conjunct proof bridge: the exact rewrite
//! for recorded AY output, and every shape it must decline. Whether the
//! checker accepts the rewrite is tested against the real checker in
//! `ay_subprocess_tests.rs`
//! (`an_and_pos_refusal_certifies_through_the_split_retry_against_the_original`).

use super::*;

/// The committed x86-64 body snapshot `Ident` (the register-to-register copy,
/// `tests/fixtures/x86_source_bound_body/snapshots.smt2`), as the replay
/// renders it.
pub(crate) const IDENT_QUERY: &str = "(set-option :timeout 30000)
(set-option :produce-models true)
(set-logic QF_BV)
(declare-const e_rdi (_ BitVec 64))
(declare-const p0 (_ BitVec 64))
(declare-const m0 (_ BitVec 64))
(declare-const m1 (_ BitVec 64))
(assert (and (and (= p0 e_rdi) (= m0 e_rdi)) (and (= m1 m0) (not (= p0 m1)))))
(check-sat)
(exit)";

/// The proof AY 0.26.0 build 9624 (Trust package 9192, SHA-256 `40e852cc…`)
/// publishes for `split_assert_conjuncts(IDENT_QUERY)`, byte for byte
/// (measured 2026-10-14). Its proof of `IDENT_QUERY` itself is refused by AY:
/// `invalid surface proof step t1: and_pos indexed conjunct is absent from its
/// effective source`.
pub(crate) const IDENT_SPLIT_PROOF_AY_9624: &str = "(assume t0 (= p0 e_rdi))
(assume t1 (= m0 e_rdi))
(assume t2 (= m1 m0))
(assume t3 (not (= p0 m1)))
(step t4 (cl (not (= p0 e_rdi)) (not (= m0 e_rdi)) (not (= m1 m0)) (= p0 m1)) :rule eq_transitive)
(step t5 (cl (not (= m0 e_rdi)) (not (= m1 m0)) (= p0 m1)) :rule th_resolution :premises (t4 t0))
(step t6 (cl (not (= m1 m0)) (= p0 m1)) :rule th_resolution :premises (t5 t1))
(step t7 (cl (= p0 m1)) :rule th_resolution :premises (t6 t2))
(step t8 (cl) :rule th_resolution :premises (t7 t3))
";

/// The bridged proof of `IDENT_QUERY`: the original conjunction assumed
/// verbatim, its two nested conjunctions derived, and each split assumption
/// derived by index. Clean (Carcara) fully verifies it against `IDENT_QUERY`
/// (aterm Clean 8606 and a current Clean, measured 2026-10-14).
pub(crate) const IDENT_BRIDGED: &str = "(assume tcg_split_and0 (and (and (= p0 e_rdi) (= m0 e_rdi)) (and (= m1 m0) (not (= p0 m1)))))
(step tcg_split_and1 (cl (and (= p0 e_rdi) (= m0 e_rdi))) :rule and :premises (tcg_split_and0) :args (0))
(step tcg_split_and2 (cl (and (= m1 m0) (not (= p0 m1)))) :rule and :premises (tcg_split_and0) :args (1))
(step t0 (cl (= p0 e_rdi)) :rule and :premises (tcg_split_and1) :args (0))
(step t1 (cl (= m0 e_rdi)) :rule and :premises (tcg_split_and1) :args (1))
(step t2 (cl (= m1 m0)) :rule and :premises (tcg_split_and2) :args (0))
(step t3 (cl (not (= p0 m1))) :rule and :premises (tcg_split_and2) :args (1))
(step t4 (cl (not (= p0 e_rdi)) (not (= m0 e_rdi)) (not (= m1 m0)) (= p0 m1)) :rule eq_transitive)
(step t5 (cl (not (= m0 e_rdi)) (not (= m1 m0)) (= p0 m1)) :rule th_resolution :premises (t4 t0))
(step t6 (cl (not (= m1 m0)) (= p0 m1)) :rule th_resolution :premises (t5 t1))
(step t7 (cl (= p0 m1)) :rule th_resolution :premises (t6 t2))
(step t8 (cl) :rule th_resolution :premises (t7 t3))
";

#[test]
fn bridges_the_recorded_ident_split_proof_exactly() {
    assert_eq!(
        bridge_split_conjunct_proof(IDENT_QUERY, IDENT_SPLIT_PROOF_AY_9624),
        Ok(IDENT_BRIDGED.to_string())
    );
}

/// The right-nested shape (`split_assert_tests::splits_the_right_nested_ident_shape`)
/// derives each nested conjunction from its parent at argument 1, and leaves
/// at argument 0, so every index names the conjunct's real position.
#[test]
fn indexes_a_right_nested_conjunction_by_position() {
    let original = "(declare-const a Bool)\n(declare-const b Bool)\n(declare-const c Bool)\n\
                    (assert (and a (and (not b) (and b c))))\n(check-sat)";
    let proof = "(assume s0 (and b c))\n(assume s1 (not b))\n(assume s2 a)\n\
                 (step s3 (cl) :rule resolution :premises (s0 s1))";
    let bridged = bridge_split_conjunct_proof(original, proof).unwrap();
    assert_eq!(
        bridged,
        "(assume tcg_split_and0 (and a (and (not b) (and b c))))\n\
         (step tcg_split_and1 (cl (and (not b) (and b c))) :rule and :premises (tcg_split_and0) :args (1))\n\
         (step tcg_split_and2 (cl (and b c)) :rule and :premises (tcg_split_and1) :args (1))\n\
         (step s0 (cl (and b c)) :rule and :premises (tcg_split_and1) :args (1))\n\
         (step s1 (cl (not b)) :rule and :premises (tcg_split_and1) :args (0))\n\
         (step s2 (cl a) :rule and :premises (tcg_split_and0) :args (0))\n\
         (step s3 (cl) :rule resolution :premises (s0 s1))\n",
        "a bare-atom conjunct counts toward the indices"
    );
}

/// Whitespace and comments do not decide a match; the assumption is rewritten
/// with AY's own spelling of the term.
#[test]
fn matches_assumptions_up_to_whitespace() {
    let proof = "; produced by a fixture\n(assume  t0   (=  m1\n m0 ))\n(step t1 (cl) :rule hole)";
    let bridged = bridge_split_conjunct_proof(IDENT_QUERY, proof).unwrap();
    assert!(
        bridged.contains(
            "(step t0 (cl (=  m1\n m0 )) :rule and :premises (tcg_split_and2) :args (0))"
        ),
        "{bridged}"
    );
}

/// A subproof's own assumption is local to it and passes through unchanged;
/// only top-level assumptions name problem premises.
#[test]
fn leaves_subproof_assumptions_alone() {
    let proof = "(assume t0 (= m1 m0))\n\
                 (anchor :step t1 :args ((x (_ BitVec 64))))\n\
                 (assume t1.a0 (= x x))\n\
                 (step t1 (cl (= x x)) :rule subproof :discharge (t1.a0))\n\
                 (step t2 (cl) :rule hole)";
    let bridged = bridge_split_conjunct_proof(IDENT_QUERY, proof).unwrap();
    assert!(bridged.contains("\n(assume t1.a0 (= x x))\n"), "{bridged}");
    assert!(
        bridged.contains("(step t0 (cl (= m1 m0)) :rule and :premises (tcg_split_and2) :args (0))"),
        "{bridged}"
    );
}

/// FAIL CLOSED: every shape the bridge cannot map with certainty declines,
/// so the retry keeps the original refusal.
#[test]
fn declines_what_it_cannot_map_with_certainty() {
    let flat = "(assert (not (= a a)))\n(check-sat)";
    let two = "(assert (and a b))\n(assert (and b c))\n(check-sat)";
    for (original, proof, why) in [
        (flat, "(assume t0 (not (= a a)))", "no conjunctive assert"),
        (two, "(assume t0 a)", "more than one conjunctive assert"),
        (
            IDENT_QUERY,
            "(assume t0 (= m1 p0))\n(step t1 (cl) :rule hole)",
            "not an argument of the original conjunction",
        ),
        (
            IDENT_QUERY,
            "(assume t0 (and (and (= p0 e_rdi) (= m0 e_rdi)) (and (= m1 m0) (not (= p0 m1)))))",
            "not an argument of the original conjunction",
        ),
        (
            IDENT_QUERY,
            "(assume tcg_split_and7 (= m1 m0))",
            "already uses the identifier prefix",
        ),
        (IDENT_QUERY, "(assume t0 (= m1 m0)", "unbalanced `(`"),
        (IDENT_QUERY, "(assume t0 (= m1 m0)))", "unbalanced `)`"),
        (
            IDENT_QUERY,
            "t0 (assume t0 (= m1 m0))",
            "stray top-level atom",
        ),
        (
            IDENT_QUERY,
            "(assume t0 |m1 (= m1 m0))",
            "unterminated quoted symbol",
        ),
        (
            IDENT_QUERY,
            "(anchor :step t1)\n(assume t1.a0 (= m1 m0))",
            "an unclosed anchor",
        ),
        (IDENT_QUERY, "(assume t0)", "is not `(assume id term)`"),
    ] {
        let Err(declined) = bridge_split_conjunct_proof(original, proof) else {
            panic!("must decline: {why}");
        };
        assert!(declined.contains(why), "{why}: {declined}");
    }
}
