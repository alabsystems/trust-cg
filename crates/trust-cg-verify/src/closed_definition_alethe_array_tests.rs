// Copyright 2026 Andrew Yates | Apache-2.0
//! Genuine unchanged-query checking of bounded literal array derivations.
use super::*;
use crate::lowering_proof::MachineSideProvenance;
use sha2::{Digest, Sha256};

fn query(left: E, right: E, preconditions: Vec<E>) -> ProofObligation {
    ProofObligation {
        name: "original bounded array observation".into(),
        trust_ir_expr: left,
        aarch64_expr: right,
        inputs: vec![],
        preconditions,
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::StaticDb,
    }
}
fn with_checker(test: impl FnOnce(&dyn Fn(&str, &str) -> bool, &str)) {
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let solver =
        crate::ay_bridge::admitted_proof_solver().expect("genuine admitted AY/checker authority");
    let authority = crate::verification_authority::VerificationAuthority::capture(&solver);
    let checker = authority.checker().expect("genuine captured Clean image");
    let check = |raw: &str, proof: &str| {
        let checked = crate::obligation_cert_store::carcara_verify_with_expected_checker_with_env(
            checker.path(),
            checker.sha256(),
            raw,
            proof,
            authority.child_env(),
            crate::obligation_cert_store::proof_check_timeout_ms(30_000),
        )
        .unwrap();
        if !checked {
            // Diagnostic replay uses the same fixed checker, original input
            // and sanitized environment; it creates no alternative verdict.
            eprintln!(
                "ARRAY_REJECTED_QUERY_BEGIN\n{raw}ARRAY_REJECTED_QUERY_END\nARRAY_REJECTED_PROOF_BEGIN\n{proof}ARRAY_REJECTED_PROOF_END"
            );
            let dir = tempfile::tempdir().unwrap();
            let cert = dir.path().join("cert.json");
            std::fs::write(
                &cert,
                serde_json::to_vec(&serde_json::json!({
                    "type": "alethe_certificate", "version": "1.0", "problem": raw, "proof": proof
                }))
                .unwrap(),
            )
            .unwrap();
            let mut command =
                crate::obligation_cert_store::clean_verify_external_command(checker.path(), &cert);
            authority.child_env().apply_to_command(&mut command);
            let result = crate::subprocess::run(
                &mut command,
                Some(std::time::Duration::from_millis(
                    crate::obligation_cert_store::proof_check_timeout_ms(30_000),
                )),
            )
            .unwrap();
            eprintln!(
                "ARRAY_FIXED_CHECKER_REJECTION status={} stdout={} stderr={}",
                result.status,
                String::from_utf8_lossy(&result.stdout),
                String::from_utf8_lossy(&result.stderr)
            );
        }
        checked
    };
    test(&check, checker.sha256());
}
fn raw(query: &ProofObligation) -> String {
    crate::ay_bridge::generate_smt2_query_raw(
        query,
        &crate::ay_bridge::AYConfig {
            solver: None,
            timeout_ms: 30_000,
            produce_models: true,
        },
    )
}
fn rebound(candidate: &str, original: &ProofObligation, changed: &ProofObligation) -> String {
    let old = format!("(assume cd0 {})", original.negated_equivalence());
    assert_eq!(candidate.matches(&old).count(), 1);
    candidate.replacen(
        &old,
        &format!("(assume cd0 {})", changed.negated_equivalence()),
        1,
    )
}

#[test]
fn captured_physical_word_original_geometry_and_byte_queries_independently_replay() {
    with_checker(|check, checker| {
        for (label, original, digest) in [
            (
                "geometry",
                include_str!("../tests/fixtures/closed_definition_owned_word_geometry.smt2"),
                "e456d86e855db8da722f4873b116af44cd8180db943a2c9911678f590bdf5af1",
            ),
            (
                "context-byte",
                include_str!("../tests/fixtures/closed_definition_owned_word_context_byte.smt2"),
                "48ab0a505df084da3933dab8a89b3c103aa88806dc5211078419de0d2add5042",
            ),
            (
                "four-pointer-status",
                include_str!("../tests/fixtures/closed_definition_four_pointer_status.smt2"),
                "1d4af9ae855ee2ca101d80fb24129628b029ba5852ae628ae019c6d4882604b7",
            ),
        ] {
            assert_eq!(format!("{:x}", Sha256::digest(original.as_bytes())), digest);
            let query = super::fixture::captured(original, label);
            assert_eq!(raw(&query), original);
            let before = query.clone();
            let candidate = compose(&query).unwrap();
            assert_eq!(query, before);
            let start = std::time::Instant::now();
            assert!(check(original, &candidate.text));
            println!(
                "ORIGINAL_PHYSICAL_WORD_CHECKED label={label} query_sha256={digest} proof_sha256={:x} proof_bytes={} steps={} checker_sha256={checker} checker_wall_seconds={:.9} native_credit=false",
                Sha256::digest(candidate.text.as_bytes()),
                candidate.text.len(),
                candidate.steps,
                start.elapsed().as_secs_f64()
            );
            println!(
                "ORIGINAL_PHYSICAL_WORD_PROOF_BEGIN {label}\n{}ORIGINAL_PHYSICAL_WORD_PROOF_END",
                candidate.text
            );
            if label == "context-byte" {
                assert!(candidate.text.contains(":rule arrays_idx"));
                assert!(candidate.text.contains(":rule arrays_row"));
                let E::Eq { lhs, .. } = &query.aarch64_expr else {
                    panic!("original byte conclusion")
                };
                let mut wrong = query.clone();
                wrong.aarch64_expr = lhs.as_ref().clone().eq_expr(E::bv_const(18, 8));
                assert!(
                    !check(&raw(&wrong), &rebound(&candidate.text, &query, &wrong)),
                    "wrong observed byte remains false with the sole assumption rebound too"
                );
            }
        }
    });
}

#[test]
fn same_and_different_literal_array_indices_keep_their_original_guards() {
    with_checker(|check, checker| {
        let memory = E::uf("unowned", vec![], crate::memory_proofs::memory_sort());
        let first = E::uf("actual_index", vec![], SmtSort::BitVec(64));
        let read = E::uf("read_index", vec![], SmtSort::BitVec(64));
        let a = E::uf("first_memory", vec![], crate::memory_proofs::memory_sort());
        let b = E::uf("second_memory", vec![], crate::memory_proofs::memory_sort());
        let observed = E::select(b.clone(), read.clone());
        let query = query(
            observed.clone(),
            E::bv_const(128, 8),
            vec![
                first.clone().eq_expr(
                    E::bv_const(4096, 64).bvadd(E::bv_const(8, 64).bvmul(E::bv_const(1, 64))),
                ),
                read.clone()
                    .eq_expr(E::bv_const(4096, 64).bvadd(E::bv_const(8, 64))),
                a.clone()
                    .eq_expr(E::store(memory, first.clone(), E::bv_const(128, 8))),
                b.clone().eq_expr(E::store(
                    a,
                    first.bvadd(E::bv_const(8, 64)),
                    E::bv_const(127, 8),
                )),
            ],
        );
        let candidate = compose(&query).unwrap();
        assert!(check(&raw(&query), &candidate.text));
        assert!(candidate.text.contains(":rule arrays_idx"));
        assert!(candidate.text.contains(":rule arrays_row"));
        let mut wrong = query.clone();
        wrong.aarch64_expr = E::bv_const(129, 8);
        assert!(!check(
            &raw(&wrong),
            &rebound(&candidate.text, &query, &wrong)
        ));
        let mut outside = query.clone();
        outside.trust_ir_expr = E::select(b, E::bv_const(9000, 64));
        assert!(
            compose(&outside).is_err(),
            "an unowned array byte cannot acquire a default literal"
        );
        // A plausible array rule name must not turn a false byte/value or an
        // omitted index guard into fully checked evidence. These SAT queries
        // and their sole original assumptions are constructed independently
        // of `compose`, so later proof endpoints cannot mask the rule check.
        for (read_index, alleged_value) in [(4096, 129), (4104, 128)] {
            let selected = E::select(
                E::store(
                    E::uf("unowned", vec![], crate::memory_proofs::memory_sort()),
                    E::bv_const(4096, 64),
                    E::bv_const(128, 8),
                ),
                E::bv_const(read_index, 64),
            );
            let wrong = self::query(selected.clone(), E::bv_const(alleged_value, 8), vec![]);
            let alleged = selected.eq_expr(E::bv_const(alleged_value, 8));
            let bad = format!(
                "(assume cd0 {})\n(step cd1 (cl {alleged}) :rule arrays_idx)\n(step cd2 (cl) :rule resolution :premises (cd0 cd1))\n",
                wrong.negated_equivalence()
            );
            assert!(
                !check(&raw(&wrong), &bad),
                "a malformed array axiom cannot be semantic proof evidence"
            );
        }
        println!(
            "GENERIC_LITERAL_ARRAY_GUARDS_CHECKED checker_sha256={checker} wrong_value=rejected unowned_byte=refused"
        );
    });
}

#[test]
fn ground_bound_shift_and_extract_candidates_require_real_original_query_checking() {
    with_checker(|check, checker| {
        for shift in [0, 7, 63, 64] {
            let value = E::uf("defined_word", vec![], SmtSort::BitVec(64));
            let expected = if shift == 64 { 0 } else { 1u64 << shift };
            let query = query(
                value.clone(),
                E::bv_const(expected, 64),
                vec![
                    value.eq_expr(
                        E::bv_const(1, 64)
                            .bvshl(E::bv_const(shift, 64))
                            .extract(63, 0),
                    ),
                ],
            );
            let candidate = compose(&query).unwrap();
            assert!(check(&raw(&query), &candidate.text));
        }
        println!(
            "GROUND_SHIFT_EXTRACT_CHECKED checker_sha256={checker} includes_shift_equal_width=true"
        );
    });
}
