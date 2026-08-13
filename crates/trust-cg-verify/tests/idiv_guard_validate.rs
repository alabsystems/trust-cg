//! Forward-port validation for the branchless-guarded signed-division proofs
//! (sdiv/srem x i32/i64). Exercises the crate's PUBLIC API only, so it is
//! unaffected by unrelated bit-rot in the crate's in-source `#[cfg(test)]`
//! modules (which currently fail to compile against the drifted trust_ir
//! `Inst`/`SwitchCase`/`Block` shapes on origin/main).

use trust_cg_verify::lowering_proof::verify_by_evaluation;
use trust_cg_verify::verify::VerificationResult;
use trust_cg_verify::x86_64_lowering_proofs::{
    all_x86_64_proofs, proof_x86_sdiv_i32_guarded, proof_x86_sdiv_i64_guarded,
    proof_x86_srem_i32_guarded, proof_x86_srem_i64_guarded,
};

#[test]
fn guarded_idiv_proofs_validate() {
    let cases = [
        ("Sdiv_I32", proof_x86_sdiv_i32_guarded()),
        ("Sdiv_I64", proof_x86_sdiv_i64_guarded()),
        ("Srem_I32", proof_x86_srem_i32_guarded()),
        ("Srem_I64", proof_x86_srem_i64_guarded()),
    ];
    for (name, ob) in cases {
        let result = verify_by_evaluation(&ob);
        assert!(
            matches!(result, VerificationResult::Valid),
            "guarded {name} proof did not validate: {result:?}"
        );
    }
}

#[test]
fn x86_64_proof_count_is_531_after_forward_port() {
    assert_eq!(
        all_x86_64_proofs().len(),
        531,
        "x86-64 proof registration count drifted from expected 531 \
         (518 through slice 3 + 10 slice-4 CMPXCHG conditional-data-flow proofs \
         + 3 v2i64 SSE2 lane proofs: uniform PSLLQ/PSRLQ immediate shifts and \
         the PMULUDQ low-32 multiply, 16ab91cb)"
    );
}
