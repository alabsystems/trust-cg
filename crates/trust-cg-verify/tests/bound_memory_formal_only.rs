// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Adversarial controls for the Formal-only bound-memory rule (owner ruling
//! 2026-09-29, `trust_cg_verify::bound_memory_authority`).
//!
//! * Every WRONG form theorem — each applicable machine-side defect of every
//!   pair and scalar form, renamed to the FAITHFUL form's name (a mis-modelled
//!   theorem) — is never credited: the committed certificate of the faithful
//!   form binds its exact query, which a defect changes. With AY present,
//!   every pair defect and one form per scalar (transfer, addressing) family
//!   is also REFUTED by a solver counterexample that the evaluator confirms.
//!   (The in-module structured-grid tests refute every defect in process.)
//! * Every RIGHT form theorem is credited, and only through its committed
//!   certificate: each certifiable exact query has one, and a cosmetic change
//!   to the obligation (a renamed input) is refused.
//! * At the function walk, a frame pair and a spill reload are credited
//!   `Formal` citing their FORM theorem, never the sampled concrete-word
//!   obligation, and an unbound bound-memory row stays unverified with the
//!   rule's note.
//!
//! The credit legs hold on a host whose `drat-trim` bytes the bound-memory
//! manifest qualifies. Elsewhere they assert the fail-closed outcome (every
//! row a checker-identity miss) and the library's
//! `bound_memory_set_binds_the_exact_runtime_checker_bytes` is the one red
//! test, naming the host's identity and how to qualify it.

use trust_cg_ir::aarch64_regs::{SP, X0, X1, X19, X20, X29, X30};
use trust_cg_ir::{AArch64Opcode as O, MachFunction, MachInst, MachOperand, Signature};
use trust_cg_verify::aarch64_pair_memory_forms::{
    PAIR_MEMORY_FORMS, PairMachineMutation, proof_pair_memory_form,
    proof_pair_memory_form_with_mutation,
};
use trust_cg_verify::aarch64_scalar_memory_proofs::{
    SCALAR_MEMORY_FORMS, ScalarMachineMutation, proof_scalar_memory,
    proof_scalar_memory_with_mutation,
};
use trust_cg_verify::ay_bridge::{AYConfig, AYResult, ay_available, verify_with_ay};
use trust_cg_verify::bound_memory_authority::{
    BOUND_MEMORY_FORMAL_ONLY, CHECKER_IDENTITY_MISS, bound_memory_checker_qualification,
    certifiable_bound_memory_queries, form_certificate_status,
};
use trust_cg_verify::function_verifier::{FunctionVerifier, InstructionVerificationResult};
use trust_cg_verify::lowering_proof::{ProofObligation, VerificationConfig};
use trust_cg_verify::smt::{EvalEnv, EvalResult};
use trust_cg_verify::verify::VerificationStrength;

/// A solver counterexample for `obligation`, confirmed by the evaluator: the
/// preconditions hold under AY's model (unassigned inputs are zero) and the
/// two sides evaluate differently.
fn ay_refutes(obligation: &ProofObligation) -> Result<(), String> {
    let model = match verify_with_ay(obligation, &AYConfig::default()) {
        AYResult::CounterExample(model) => model,
        other => return Err(format!("no counterexample: {other:?}")),
    };
    let mut env = EvalEnv::default();
    for (name, width) in &obligation.inputs {
        let value = model
            .iter()
            .find(|(var, _)| var == name)
            .map_or(0, |(_, value)| *value);
        let mask = if *width >= 64 {
            u64::MAX
        } else {
            (1u64 << width) - 1
        };
        env.insert(name.clone(), value & mask);
    }
    let holds = obligation
        .preconditions
        .iter()
        .all(|p| matches!(p.try_eval(&env), Ok(EvalResult::Bool(true))));
    let differs = match (
        obligation.trust_ir_expr.try_eval(&env),
        obligation.aarch64_expr.try_eval(&env),
    ) {
        (Ok(intent), Ok(machine)) => intent != machine,
        _ => false,
    };
    if holds && differs {
        Ok(())
    } else {
        Err(format!("model not confirmed by the evaluator: {model:?}"))
    }
}

#[test]
fn every_wrong_pair_form_theorem_is_uncredited_and_refuted() {
    let live_ay = ay_available();
    let (mut total, mut refuted) = (0usize, 0usize);
    let mut wrong = Vec::new();
    for (form, query) in PAIR_MEMORY_FORMS {
        let faithful = proof_pair_memory_form(&form).expect("table form");
        for mutation in PairMachineMutation::DEFECTS {
            let Some(mut defect) = proof_pair_memory_form_with_mutation(&form, mutation) else {
                continue;
            };
            total += 1;
            defect.name = faithful.name.clone();
            if form_certificate_status(&defect).is_ok() {
                wrong.push(format!("{query} {mutation:?}: CREDITED"));
            }
            if live_ay {
                match ay_refutes(&defect) {
                    Ok(()) => refuted += 1,
                    Err(why) => wrong.push(format!("{query} {mutation:?}: {why}")),
                }
            }
        }
    }
    eprintln!(
        "PAIR_FORMAL_ONLY defects={total} uncredited={total} ay_refuted={refuted} live_ay={live_ay}"
    );
    assert_eq!(total, 21 * 6 + 11 + 6);
    assert!(wrong.is_empty(), "{wrong:#?}");
}

#[test]
fn every_wrong_scalar_form_theorem_is_uncredited_and_representatives_refute() {
    let live_ay = ay_available();
    let mut families = std::collections::HashSet::new();
    let (mut total, mut refuted) = (0usize, 0usize);
    let mut wrong = Vec::new();
    for (form, query) in SCALAR_MEMORY_FORMS {
        let faithful = proof_scalar_memory(&form).expect("table form");
        let ay_leg = live_ay && families.insert((form.transfer, form.addressing));
        for mutation in ScalarMachineMutation::DEFECTS {
            let Some(mut defect) = proof_scalar_memory_with_mutation(&form, mutation) else {
                continue;
            };
            total += 1;
            defect.name = faithful.name.clone();
            if form_certificate_status(&defect).is_ok() {
                wrong.push(format!("{query} {mutation:?}: CREDITED"));
            }
            if ay_leg {
                match ay_refutes(&defect) {
                    Ok(()) => refuted += 1,
                    Err(why) => wrong.push(format!("{query} {mutation:?}: {why}")),
                }
            }
        }
    }
    eprintln!(
        "SCALAR_FORMAL_ONLY defects={total} uncredited={total} ay_refuted={refuted} \
         ay_families={} live_ay={live_ay}",
        families.len()
    );
    assert_eq!(total, 139 + 139 + 28 + 28 + 139 + 5);
    assert!(wrong.is_empty(), "{wrong:#?}");
    if live_ay {
        // One form per (load|store) x (ui, unscaled, pre, post, ro) plus the
        // literal load.
        assert_eq!(families.len(), 11);
        assert!(refuted > 0);
    }
}

#[test]
fn every_right_form_theorem_is_credited_only_by_its_certificate() {
    let queries = certifiable_bound_memory_queries();
    let mut uncredited = Vec::new();
    for query in &queries {
        if let Err(why) = form_certificate_status(&query.obligation) {
            uncredited.push(format!("{}: {why}", query.file));
        }
        // Exact-query binding: a cosmetically different obligation (one more,
        // unused, input: the same meaning) is not the certified query.
        let mut widened = query.obligation.clone();
        widened.inputs.push(("bound_memory_unused".to_string(), 8));
        assert!(
            form_certificate_status(&widened).is_err(),
            "{}: a different query must not borrow the certificate",
            query.file
        );
    }
    eprintln!(
        "RIGHT_FORMS queries={} credited={}",
        queries.len(),
        queries.len() - uncredited.len()
    );
    // Every certifiable query has a committed certificate (72 queries, 85
    // forms; measured 2026-09-29 with AY 0.26.0 build 9624). A host whose
    // checker the manifest does not qualify credits none of them, each as a
    // checker-identity miss (`bound_memory_set_binds_the_exact_runtime_checker_bytes`
    // is that host's one red test).
    assert_eq!(queries.len(), 72);
    match bound_memory_checker_qualification() {
        Ok(()) => assert!(uncredited.is_empty(), "{uncredited:#?}"),
        Err(_) => assert!(
            uncredited.len() == queries.len()
                && uncredited
                    .iter()
                    .all(|miss| miss.contains(CHECKER_IDENTITY_MISS)),
            "{uncredited:#?}"
        ),
    }
}

fn function(insts: Vec<MachInst>) -> MachFunction {
    let mut func = MachFunction::new("bound_memory".to_string(), Signature::new(vec![], vec![]));
    for inst in insts {
        let id = func.push_inst(inst);
        func.append_inst(func.entry, id);
    }
    func
}

#[test]
fn the_walk_credits_bound_rows_only_through_their_form_certificate() {
    let sp = || MachOperand::Special(trust_cg_ir::SpecialReg::SP);
    let p = MachOperand::PReg;
    let func = function(vec![
        // 0: stp x29, x30, [sp, #-16]!
        MachInst::new(
            O::StpPreIndex,
            vec![p(X29), p(X30), sp(), MachOperand::Imm(-16)],
        ),
        // 1: stp x19, x20, [sp, #16]
        MachInst::new(O::StpRI, vec![p(X19), p(X20), p(SP), MachOperand::Imm(16)]),
        // 2: ldur x0, [x29, #-8] (post-frame spill reload spelling)
        MachInst::new(
            O::LdrRI,
            vec![
                p(X0),
                MachOperand::MemOp {
                    base: X29,
                    offset: -8,
                },
            ],
        ),
        // 3: ldr x1, [x1, #8] (load overwrites its base: bound by no form)
        MachInst::new(O::LdrRI, vec![p(X1), p(X1), MachOperand::Imm(8)]),
        // 4: ldp x0, x1, [x0, #16] (signed-offset GPR pair load overwrites
        //    its base: admitted by the pair lane, bound by no form)
        MachInst::new(O::LdpRI, vec![p(X0), p(X1), p(X0), MachOperand::Imm(16)]),
        // 5: ldp x29, x30, [sp], #16
        MachInst::new(
            O::LdpPostIndex,
            vec![p(X29), p(X30), sp(), MachOperand::Imm(16)],
        ),
    ]);
    // The compiler's proof-promotion policy: the one that replays
    // certificates (an evaluation-only walk credits no bound row).
    let mut config = VerificationConfig::for_proof_promotion();
    config.sample_count = 64;
    let report = FunctionVerifier::with_config(config).verify(&func);
    let rows: Vec<&InstructionVerificationResult> =
        report.instructions.iter().map(|row| &row.result).collect();
    let qualified = bound_memory_checker_qualification();
    for (index, form) in [
        (0, "PairMem[stp.pre.gpr.w8]"),
        (1, "PairMem[stp.offset.gpr.w8]"),
        (2, "ScalarMem[ldr.unscaled.gpr.w8.zx]"),
        (5, "PairMem[ldp.post.gpr.w8]"),
    ] {
        match (&qualified, rows[index]) {
            (
                Ok(()),
                InstructionVerificationResult::Verified {
                    proof_name,
                    strength: VerificationStrength::Formal,
                    degenerate: false,
                    ..
                },
            ) => assert!(proof_name.starts_with(form), "{index}: {proof_name}"),
            // An unqualified host: the certificate exists, the checker is not
            // authorized, and the row misses fail closed.
            (Err(_), InstructionVerificationResult::Unverified { reason }) => assert!(
                reason.contains(BOUND_MEMORY_FORMAL_ONLY)
                    && reason.contains(form)
                    && reason.contains(CHECKER_IDENTITY_MISS),
                "{index}: {reason}"
            ),
            (qualified, other) => {
                panic!("row {index} must be credited by {form} ({qualified:?}): {other:?}")
            }
        }
    }
    for index in [3, 4] {
        match rows[index] {
            InstructionVerificationResult::Unverified { reason } => assert!(
                reason.contains(BOUND_MEMORY_FORMAL_ONLY)
                    && reason.contains("no form theorem binds this instruction"),
                "{index}: {reason}"
            ),
            other => panic!("row {index} must stay unverified: {other:?}"),
        }
    }
    assert_eq!(
        report.formally_credited_count(),
        if qualified.is_ok() { 4 } else { 0 }
    );
}
