// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Exact captured Core-to-machine read demand; parsing is test fixture intake
//! only. Every replay checks the unchanged original SMT-LIB problem.
use super::*;
use crate::lowering_proof::MachineSideProvenance;
use sha2::{Digest, Sha256};

const ORIGINAL: &str = include_str!("../tests/fixtures/closed_definition_core_mach_read1.smt2");
const ORIGINAL_SHA256: &str = "5b4f151d252e77de9a3892c8e3f8c7d84be4a97d0bcd994dac0094e9fe5d8d2c";

fn captured_read() -> ProofObligation {
    assert_eq!(
        format!("{:x}", Sha256::digest(ORIGINAL.as_bytes())),
        ORIGINAL_SHA256
    );
    let query = super::fixture::captured(ORIGINAL, "captured actual CoreToMachine read1");
    assert_eq!(query.preconditions.len(), 54);
    let config = crate::ay_bridge::AYConfig {
        solver: None,
        timeout_ms: 30_000,
        produce_models: true,
    };
    assert_eq!(
        crate::ay_bridge::generate_smt2_query_raw(&query, &config),
        ORIGINAL
    );
    query
}

#[test]
fn projected_guarded_bounds_transport_only_genuine_positive_units() {
    let source = E::uf("original_pointer", vec![], SmtSort::BitVec(64));
    let target = E::uf("lowered_pointer", vec![], SmtSort::BitVec(64));
    let base = E::var("base", 64);
    let bound = |pointer: E| pointer.bvule(E::bv_const(u64::MAX - 7, 64));
    let fixture = |guard: E, offset: u64| ProofObligation {
        name: "projected original guarded bound".into(),
        trust_ir_expr: E::BoolConst(true),
        aarch64_expr: bound(target.clone()),
        inputs: vec![("base".into(), 64)],
        preconditions: vec![
            source.clone().eq_expr(
                base.clone()
                    .bvadd(E::bv_const(8, 64).bvmul(E::bv_const(1, 64))),
            ),
            target
                .clone()
                .eq_expr(base.clone().bvadd(E::bv_const(offset, 64))),
            guard.not_expr().or_expr(
                bound(source.clone()).and_expr(
                    source
                        .clone()
                        .bvand(E::bv_const(7, 64))
                        .eq_expr(E::bv_const(0, 64)),
                ),
            ),
        ],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::StaticDb,
    };
    let query = fixture(E::BoolConst(true), 8);
    let before = query.clone();
    let proof = compose(&query).unwrap();
    assert_eq!(query, before);
    assert!(proof.text.contains(":rule evaluate"));
    assert!(proof.text.contains(":rule cong"));
    assert!(proof.text.contains(":rule equiv1"));
    // A source guarded by an UNKNOWN condition supplies no unconditional
    // bound. An actual changed address likewise supplies no correspondence.
    for mutant in [
        fixture(E::uf("unproved_guard", vec![], SmtSort::Bool), 8),
        fixture(E::BoolConst(true), 9),
    ] {
        assert!(matches!(
            compose(&mutant),
            Err(ClosedDefinitionRefusal::Unsupported(_))
        ));
    }
}

#[test]
fn captured_read1_replays_original_and_rejects_a_false_changed_address() {
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let query = captured_read();
    let before = query.clone();
    let candidate = compose(&query).unwrap();
    assert_eq!(query, before);
    assert_eq!(candidate.premises, 54);
    assert_eq!(candidate.definitions, 36);
    assert_eq!(candidate.text.matches("(assume ").count(), 1);
    let solver = crate::ay_bridge::admitted_proof_solver().expect("genuine installed AY authority");
    let authority = crate::verification_authority::VerificationAuthority::capture(&solver);
    let checker = authority.checker().expect("genuine captured Clean checker");
    let check = |raw: &str, proof: &str| {
        crate::obligation_cert_store::carcara_verify_with_expected_checker_with_env(
            checker.path(),
            checker.sha256(),
            raw,
            proof,
            authority.child_env(),
            crate::obligation_cert_store::proof_check_timeout_ms(30_000),
        )
    };
    assert!(check(ORIGINAL, &candidate.text).unwrap());
    println!(
        "CAPTURED_READ1_POSITIVE query_sha256={ORIGINAL_SHA256} proof_sha256={:x} proof_bytes={} premises={} definitions={} steps={} checker_sha256={} solver_authority={} ay_ran=false native_credit=false",
        Sha256::digest(candidate.text.as_bytes()),
        candidate.text.len(),
        candidate.premises,
        candidate.definitions,
        candidate.steps,
        checker.sha256(),
        solver.describe()
    );
    println!(
        "CAPTURED_READ1_PROOF_BEGIN\n{}CAPTURED_READ1_PROOF_END",
        candidate.text
    );
    let old = "(= scalar_memory_machine_d1 (bvadd abi_x0 (_ bv8 64)))";
    let new = "(= scalar_memory_machine_d1 (bvadd abi_x0 (_ bv40 64)))";
    assert_eq!(ORIGINAL.matches(old).count(), 1);
    let false_query = ORIGINAL.replacen(old, new, 1);
    // Bind the sole assumption to the changed problem as well: rejection is
    // not merely a mismatched assumption string. At base=0, observe=40 this
    // demand is outside the original five source reads [0,40).
    let false_proof = candidate.text.replacen(old, new, 1);
    assert_ne!(false_proof, candidate.text);
    assert!(!check(&false_query, &false_proof).unwrap());
    // A real original-premise projection cannot omit its parent unit. Merely
    // replacing a reflexive congruence with refl would still be a valid proof.
    let damaged = candidate
        .text
        .replacen(":premises (cd0)", ":premises ()", 1);
    assert_ne!(damaged, candidate.text);
    assert!(!check(ORIGINAL, &damaged).unwrap());
    println!(
        "CAPTURED_READ1_CHECKED query_sha256={ORIGINAL_SHA256} proof_sha256={:x} proof_bytes={} premises={} definitions={} steps={} checker_sha256={} solver_authority={} ay_ran=false negative_false_address=rejected negative_derivation=rejected native_credit=false",
        Sha256::digest(candidate.text.as_bytes()),
        candidate.text.len(),
        candidate.premises,
        candidate.definitions,
        candidate.steps,
        checker.sha256(),
        solver.describe()
    );
}
