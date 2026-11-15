// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
use super::*;
use crate::smt::EvalEnv;
use crate::source_bound_frame::source_bound_frame;
use trust_cg_ir::regs::PReg;
use trust_cg_ir::{MachFunction, MachInst};
use trust_cg_lower::Function;

// Actual scratch-register copies before arithmetic, a return copy afterwards,
// and an unrelated dead copy. No provenance stamp supplies any query term.
fn fixture(bits: u32, opcode: M, operand: O) -> (Function, MachFunction, [InstId; 4]) {
    let (source, mut machine) = crate::source_bound_alu::tests::fixture(bits, opcode, operand);
    let r = |n: u16| O::PReg(PReg::new(n + if bits == 32 { 32 } else { 0 }));
    let copy = if bits == 32 { M::MOVWrr } else { M::MOVXrr };
    let copies = [
        machine.push_inst(MachInst::new(copy, vec![r(9), r(0)])),
        machine.push_inst(MachInst::new(copy, vec![r(10), r(1)])),
        machine.push_inst(MachInst::new(copy, vec![r(0), r(9)])),
        machine.push_inst(MachInst::new(copy, vec![r(11), r(1)])),
    ];
    machine.insts[2].operands[0] = r(9);
    machine.insts[2].operands[1] = r(9);
    if machine.insts[2].operands[2] == r(1) {
        machine.insts[2].operands[2] = r(10);
    }
    if machine.insts[2].operands[2] == r(0) {
        machine.insts[2].operands[2] = r(9);
    }
    machine.blocks[0].insts = vec![
        InstId(0),
        InstId(1),
        copies[0],
        copies[1],
        copies[3],
        InstId(2),
        copies[2],
        InstId(3),
        InstId(4),
    ];
    (source, machine, copies)
}

fn matches(obligation: &ProofObligation, a: u64, b: u64) -> bool {
    let mut env = EvalEnv::default();
    env.insert("abi_x0".into(), a);
    env.insert("abi_x1".into(), b);
    obligation.trust_ir_expr.eval(&env) == obligation.aarch64_expr.eval(&env)
}

fn independently_refuted(obligation: &ProofObligation) {
    use crate::ay_bridge::{AYConfig, AYResult, verify_with_cli_raw_attributed};
    crate::env_lock::with_env_overrides(
        &[
            ("TCG_NO_PROOF_CACHE", "1"),
            ("TCG_NO_SOLVER_SERVER", "1"),
            ("TCG_BLOCKING_IDENTITY", "1"),
        ],
        || {
            let outcome = verify_with_cli_raw_attributed(obligation, &AYConfig::default());
            assert!(
                matches!(outcome.result, AYResult::CounterExample(_)),
                "wrong raw body needs a solver counterexample: {:?}",
                outcome.result
            );
            println!(
                "A64_RAW_BODY_REFUTATION result={} provenance={:?}",
                outcome.result,
                outcome.provenance()
            );
        },
    );
}

#[test]
fn source_bound_body_preserves_raw_operations_and_credits_only_return_slice_copies() {
    let inputs = [
        0,
        1,
        4095,
        4096,
        u32::MAX as u64,
        1 << 32,
        i64::MAX as u64,
        1 << 63,
        u64::MAX,
    ];
    let mut cases = 0;
    for bits in [32, 64] {
        let r = |n: u16| O::PReg(PReg::new(n + if bits == 32 { 32 } else { 0 }));
        for (opcode, operand) in [
            (M::AddRR, r(1)),
            (M::SubRR, r(1)),
            (M::AddRI, O::Imm(4095)),
            (M::SubRI, O::Imm(3)),
            (M::AddRIShift12, O::Imm(1)),
            (M::LslRI, O::Imm(1)),
        ] {
            let uses_b = operand == r(1);
            let (source, machine, copies) = fixture(bits, opcode, operand);
            let frame = source_bound_frame(&source, &machine).expect("exact frame/body pair");
            let body = SourceBoundBody::bind(&frame).expect("raw body owner");
            assert!(!body.obligation().is_degenerate());
            assert!(body.credits(copies[0]) && body.credits(copies[2]));
            assert_eq!(body.credits(copies[1]), uses_b);
            assert!(!body.credits(copies[3]));
            for id in [0, 1, 2, 3, 4, 99] {
                assert!(!body.credits(InstId(id)));
            }
            for a in inputs {
                for b in inputs {
                    assert!(
                        matches(body.obligation(), a, b),
                        "{bits}/{opcode:?}/{a}/{b}"
                    );
                }
            }
            let query = crate::serialize_to_smt2(body.obligation());
            assert!(
                query.contains("zero_extend 1"),
                "source arithmetic was normalized"
            );
            assert!(query.contains("abi_x0") && query.contains("abi_x1"));
            if bits == 32 {
                assert!(
                    query.contains("zero_extend 32"),
                    "W writes must clear X upper bits"
                );
            }
            cases += 1;
        }
    }
    assert_eq!(cases, 12);
}

#[test]
fn source_bound_body_raw_query_refutes_wrong_routes_operations_and_copy_width() {
    for bits in [32, 64] {
        let (source, machine, copies) = fixture(
            bits,
            M::SubRR,
            O::PReg(PReg::new(if bits == 32 { 33 } else { 1 })),
        );
        let frame = source_bound_frame(&source, &machine).unwrap();
        let correct = SourceBoundBody::bind(&frame).unwrap();
        let correct_query = crate::serialize_to_smt2(correct.obligation());
        for mutation in 0..5 {
            let mut wrong = machine.clone();
            let r = |n: u16| O::PReg(PReg::new(n + if bits == 32 { 32 } else { 0 }));
            match mutation {
                0 => wrong.insts[copies[0].0 as usize].operands[1] = r(1),
                1 => wrong.insts[copies[2].0 as usize].operands[1] = r(10),
                2 => wrong.insts[2].operands[0] = r(10),
                3 => wrong.insts[2].opcode = M::AddRR,
                _ => wrong.insts[2].operands.swap(1, 2),
            }
            assert!(source_bound_frame(&source, &wrong).is_err());
            let (obligation, _) = raw_body(
                &source,
                &wrong,
                frame.raw_chain().unwrap(),
                frame.envelope_instructions(),
            )
            .expect("well-formed but wrong raw model");
            assert_ne!(crate::serialize_to_smt2(&obligation), correct_query);
            assert!(
                !matches(&obligation, 23, 7),
                "{bits}/mutation{mutation} query laundered the Rust result"
            );
            independently_refuted(&obligation);
        }
    }
    let (source, machine, copies) = fixture(64, M::SubRI, O::Imm(3));
    let frame = source_bound_frame(&source, &machine).unwrap();
    let mut wrong = machine.clone();
    // Typed W copies resolve register indices from either alias spelling.
    wrong.insts[copies[0].0 as usize].opcode = M::MOVWrr;
    assert!(source_bound_frame(&source, &wrong).is_err());
    let (obligation, _) = raw_body(
        &source,
        &wrong,
        frame.raw_chain().unwrap(),
        frame.envelope_instructions(),
    )
    .unwrap();
    assert!(!matches(&obligation, (1 << 32) + 23, 7));
    independently_refuted(&obligation);
}

#[test]
fn source_bound_body_refuses_identity_bodies_and_unbounded_raw_expansion() {
    for bits in [32, 64] {
        // Semantic identity expressed as arithmetic, with real live copies.
        let (source, machine, _) = fixture(bits, M::AddRI, O::Imm(0));
        let frame = source_bound_frame(&source, &machine).unwrap();
        assert!(SourceBoundBody::bind(&frame).is_none());
        let (source, machine, _) = fixture(bits, M::LslRI, O::Imm(13));
        let frame = source_bound_frame(&source, &machine).unwrap();
        assert!(
            SourceBoundBody::bind(&frame).is_none(),
            "decline expansion beyond the raw-tree budget"
        );
    }
}

#[test]
fn source_bound_body_overwritten_copies_get_no_credit_and_uninitialized_reads_refuse() {
    let (source, mut machine, copies) = fixture(64, M::AddRR, O::PReg(PReg::new(1)));
    let overwritten = machine.push_inst(MachInst::new(
        M::MOVXrr,
        vec![O::PReg(PReg::new(9)), O::PReg(PReg::new(1))],
    ));
    machine.blocks[0].insts.insert(2, overwritten);
    let frame = source_bound_frame(&source, &machine).unwrap();
    let body = SourceBoundBody::bind(&frame).unwrap();
    assert!(!body.credits(overwritten));
    assert!(body.credits(copies[0]));
    let mut wrong = machine.clone();
    wrong.insts[copies[0].0 as usize].operands[1] = O::PReg(PReg::new(12));
    assert!(source_bound_frame(&source, &wrong).is_err());
    assert!(
        raw_body(
            &source,
            &wrong,
            frame.raw_chain().unwrap(),
            frame.envelope_instructions()
        )
        .is_none()
    );
}

#[test]
fn source_bound_body_requires_independent_replay_and_raw_queries_replay_at_both_widths() {
    use crate::function_request::FunctionDischargeContext;
    use crate::provenance_xcheck::ProvenanceXCheckMode;
    use crate::verify::VerificationResult;
    use crate::{FunctionVerifier, VerificationConfig};
    crate::env_lock::with_env_overrides(
        &[("TCG_REFINE_SOLVER", "1"), ("TCG_BLOCKING_IDENTITY", "1")],
        || {
            for bits in [32, 64] {
                let (source, machine, _) = fixture(bits, M::SubRI, O::Imm(3));
                let frame = source_bound_frame(&source, &machine).unwrap();
                let body = SourceBoundBody::bind(&frame).unwrap();
                println!(
                    "A64_BODY_QUERY bits={bits} smt2={}",
                    serde_json::to_string(&crate::serialize_to_smt2(body.obligation())).unwrap()
                );
                let verifier =
                    FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
                let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
                let result = FunctionDischargeContext::new(&request).a64_body(&body);
                assert!(
                    matches!(result, Some(VerificationResult::Valid)),
                    "required AY/Clean raw replay at i{bits}: {result:?}"
                );
                for (key, value) in [
                    ("TCG_REFINE_SOLVER", "0"),
                    ("AY_SOLVER_PATH", "/nonexistent/body-ay"),
                    ("TCG_EXTERNAL_CLEAN_CHECKER", "/nonexistent/body-clean"),
                ] {
                    crate::env_lock::with_env_overrides(&[(key, value)], || {
                        let changed =
                            verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
                        assert!(
                            !matches!(
                                FunctionDischargeContext::new(&changed).a64_body(&body),
                                Some(VerificationResult::Valid)
                            ),
                            "withdrawn authority {key}"
                        );
                        assert!(
                            matches!(
                                FunctionDischargeContext::new(&request).a64_body(&body),
                                Some(VerificationResult::Valid)
                            ),
                            "captured authority must remain immutable"
                        );
                    });
                }
            }
        },
    );
}
