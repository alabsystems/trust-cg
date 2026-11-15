// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! The Formal-only rule on the single-instruction atomic rows
//! (`X-OPCODES-P2`): every emitted atomic form is credited per instruction
//! only by a replayed certificate of its atomic form theorem, only when its
//! word-bound decomposition held, and only when that word is the bound form.

use super::*;
use crate::aarch64_atomic_forms::{
    ATOMIC_MEMORY_OPCODES, AtomicForm, AtomicOp, atomic_opcode_forms, representative_instruction,
};
use crate::function_verifier::{FunctionVerifier, InstructionVerificationResult};
use crate::lowering_proof::VerificationConfig;
use crate::verify::VerificationStrength;
use trust_cg_ir::{AArch64Opcode as O, InstId, MachFunction, MachOperand, Signature, SpecialReg};

fn function(insts: Vec<MachInst>) -> MachFunction {
    let mut func = MachFunction::new(
        "atomic_memory_rows".to_string(),
        Signature::new(vec![], vec![]),
    );
    for (index, inst) in insts.into_iter().enumerate() {
        func.insts.push(inst);
        func.blocks[0].insts.push(InstId(index as u32));
    }
    func
}

fn promotion_config() -> VerificationConfig {
    let mut config = VerificationConfig::for_proof_promotion();
    config.sample_count = 64;
    config
}

/// The row's own held atomic decomposition.
fn atomic_check(inst: &MachInst) -> BoundMemoryRefutation {
    let decomposition = crate::aarch64_atomic_effect::atomic_effect(inst)
        .unwrap_or_else(|| panic!("{inst:?}: the atomic lane admits it"));
    let verdict = crate::aarch64_atomic_effect::judge(&decomposition);
    BoundMemoryRefutation::atomic_effect(&decomposition, &verdict)
        .unwrap_or_else(|| panic!("{inst:?}: its decomposition holds: {verdict:?}"))
}

/// Every emitted (opcode, width) is credited `Formal` by the walk under the
/// proof-promotion policy, citing exactly its form theorem; on a host whose
/// checker the atomic manifest does not qualify, every row is a fail-closed
/// checker-identity miss instead.
#[test]
fn every_emitted_atomic_form_is_credited_only_by_its_form_certificate() {
    let qualified = atomic_memory_checker_qualification();
    let verifier = FunctionVerifier::with_config(promotion_config());
    let mut credited = 0;
    for opcode in ATOMIC_MEMORY_OPCODES {
        for form in atomic_opcode_forms(opcode).unwrap() {
            let inst = representative_instruction(opcode, form.bytes, 9, 10, 11).unwrap();
            let report = verifier.verify(&function(vec![inst.clone()]));
            let query = form.query().unwrap();
            match (&qualified, &report.instructions[0].result) {
                (
                    Ok(()),
                    InstructionVerificationResult::Verified {
                        proof_name,
                        category: crate::proof_database::ProofCategory::Memory,
                        strength: VerificationStrength::Formal,
                        degenerate: false,
                    },
                ) => {
                    assert!(
                        proof_name.to_lowercase().contains(query),
                        "{inst:?}: {proof_name} must cite {query}"
                    );
                    credited += 1;
                }
                (Err(_), InstructionVerificationResult::Unverified { reason }) => assert!(
                    reason.contains(BOUND_MEMORY_FORMAL_ONLY)
                        && reason.contains(CHECKER_IDENTITY_MISS),
                    "{inst:?}: {reason}"
                ),
                (qualification, other) => {
                    panic!("{inst:?}: {other:?} under qualification {qualification:?}")
                }
            }
        }
    }
    if qualified.is_ok() {
        // 6 LDAR/STLR opcodes x their widths (8) + 40 LSE/CAS opcodes x 4.
        assert_eq!(credited, 8 + 40 * 4);
    }
}

/// An evaluation-only walk replays nothing, so it credits no atomic row; a
/// shape the binder refuses (the `ST<op>` alias, a CAS discarding its old
/// value) binds no form and is never credited.
#[test]
fn evaluation_walks_and_refused_shapes_credit_nothing() {
    let inst = representative_instruction(O::Ldaddal, 8, 1, 2, 3).unwrap();
    let mut config = promotion_config();
    config.proof_replay_policy = crate::lowering_proof::ProofReplayPolicy::EvaluationOnly;
    let report = FunctionVerifier::with_config(config).verify(&function(vec![inst]));
    match &report.instructions[0].result {
        InstructionVerificationResult::Unverified { reason } => assert!(
            reason.contains(crate::function_verifier::ATOMIC_EFFECT_IS_NOT_CREDIT)
                && reason.contains(CERTIFICATE_REPLAY_OFF),
            "{reason}"
        ),
        other => panic!("an evaluation-only walk must not credit: {other:?}"),
    }
    let verifier = FunctionVerifier::with_config(promotion_config());
    for refused in [
        MachInst::new(
            O::Ldaddal,
            vec![
                MachOperand::PReg(trust_cg_ir::aarch64_regs::X1),
                MachOperand::Special(SpecialReg::XZR),
                MachOperand::PReg(trust_cg_ir::aarch64_regs::X2),
            ],
        ),
        MachInst::new(
            O::Casal,
            vec![
                MachOperand::Special(SpecialReg::XZR),
                MachOperand::PReg(trust_cg_ir::aarch64_regs::X1),
                MachOperand::PReg(trust_cg_ir::aarch64_regs::X2),
            ],
        ),
    ] {
        let report = verifier.verify(&function(vec![refused.clone()]));
        match &report.instructions[0].result {
            InstructionVerificationResult::Unverified { reason } => {
                assert!(
                    reason.contains(BOUND_MEMORY_FORMAL_ONLY),
                    "{refused:?}: {reason}"
                )
            }
            other => panic!("{refused:?} must not be credited: {other:?}"),
        }
        assert_eq!(report.formally_credited_count(), 0);
    }
}

/// Clause 2: no held decomposition, no credit. Clause 3: a row attributed to
/// another form (another width, another operation), or judged on another
/// form's word, is refused before any certificate is consulted; with the
/// binding check skipped the same attribution WOULD be credited through the
/// wrong form's replaying certificate, so each refusal is the check's doing.
#[test]
fn unrefuted_and_misbound_atomic_rows_are_refused() {
    let inst = representative_instruction(O::Ldaddal, 8, 1, 2, 3).unwrap();
    let own = match bind_bound_memory_row(&inst) {
        Some(Ok(binding)) => binding,
        other => panic!("{other:?}"),
    };
    let check = atomic_check(&inst);
    assert!(matches!(
        credit_bound_form(&inst, &own, None, true, None),
        BoundMemoryCredit::Unrefuted { .. }
    ));
    let BoundMemoryBinding::Atomic(binding) = own else {
        panic!("an atomic row binds an atomic form");
    };
    let wrong_forms = [
        AtomicForm {
            op: AtomicOp::Add,
            bytes: 4,
        },
        AtomicForm {
            op: AtomicOp::Eor,
            bytes: 8,
        },
        AtomicForm {
            op: AtomicOp::Swp,
            bytes: 8,
        },
    ];
    for wrong in wrong_forms {
        let claimed = BoundMemoryBinding::Atomic(crate::aarch64_atomic_forms::AtomicBinding {
            form: wrong,
            ..binding
        });
        match credit_bound_form(&inst, &claimed, Some(&check), true, None) {
            BoundMemoryCredit::Misbound { reason, .. } => {
                assert!(reason.contains(BOUND_MEMORY_BINDING_MISMATCH), "{reason}")
            }
            other => panic!("{wrong:?}: {other:?}"),
        }
        let _skip = binding_check_seam::skip();
        let credited = credit_bound_form(&inst, &claimed, Some(&check), true, None);
        if atomic_memory_checker_qualification().is_ok() {
            assert!(
                matches!(credited, BoundMemoryCredit::Certified { .. }),
                "without the check {wrong:?} would be credited: {credited:?}"
            );
        }
    }
    // Judged on another form's word: the LDEOR word for LDADD operands.
    let other_word =
        atomic_check(&representative_instruction(O::Ldeoral, 8, 1, 2, 3).unwrap()).word();
    let foreign =
        BoundMemoryRefutation::assumed_for_test(RefutationCheck::AtomicEffect, other_word);
    assert!(matches!(
        credit_bound_form(&inst, &own, Some(&foreign), true, None),
        BoundMemoryCredit::Misbound { .. }
    ));
    // A pair or scalar check never judges an atomic row.
    let scalar =
        BoundMemoryRefutation::assumed_for_test(RefutationCheck::InstructionWord, check.word());
    assert!(matches!(
        credit_bound_form(&inst, &own, Some(&scalar), true, None),
        BoundMemoryCredit::Misbound { .. }
    ));
    // The faithful attribution with its own held check is credited.
    if atomic_memory_checker_qualification().is_ok() {
        assert!(matches!(
            credit_bound_form(&inst, &own, Some(&check), true, None),
            BoundMemoryCredit::Certified { .. }
        ));
    }
}

/// A deliberately wrong atomic theorem wearing a faithful name is not
/// credited by the atomic set, and an atomic form theorem is never credited by
/// the bound-memory set (each set names only its own exact queries).
#[test]
fn the_atomic_set_credits_only_its_own_exact_queries() {
    let wrong = crate::aarch64_atomic_forms::representative_wrong_atomic_theorem();
    assert!(form_certificate_status(&wrong).is_err());
    let faithful = crate::aarch64_atomic_forms::proof_atomic_form(&AtomicForm {
        op: AtomicOp::Add,
        bytes: 8,
    })
    .unwrap();
    let smt2 = crate::verdict_db::db_obligation_smt2(&faithful);
    assert!(!crate::canary_cert::bound_memory::BOUND_MEMORY_SET.cert_verified(&smt2));
    match atomic_memory_checker_qualification() {
        Ok(()) => assert_eq!(form_certificate_status(&faithful), Ok(())),
        Err(_) => assert!(
            form_certificate_status(&faithful)
                .is_err_and(|miss| miss.contains(CHECKER_IDENTITY_MISS))
        ),
    }
}
