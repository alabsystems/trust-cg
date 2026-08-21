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
fn x86_64_proof_count_is_543_after_rol_and_saxpy() {
    assert_eq!(
        all_x86_64_proofs().len(),
        543,
        "x86-64 proof registration count drifted from expected 543 \
         (531 through the slice-4/SSE2 forward port, 16ab91cb; \
         + the ROL rotate-left-by-constant obligation family, 732de1f5; \
         + the scalar-IMUL/PUNPCKLQDQ/PADDQ saxpy sequence proofs, 0bfe4e1e \
         — reviewed 2026-08-19 while re-pinning: both commits added real \
         registered obligations and forgot this fence)"
    );
}
