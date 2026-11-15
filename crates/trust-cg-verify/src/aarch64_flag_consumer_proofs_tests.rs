// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use crate::lowering_proof::{
    VerificationConfig, uses_checked_scalar_fp_evaluation, verify_by_evaluation_with_config,
};
use crate::verify::VerificationResult;
use std::collections::HashSet;
use trust_cg_ir::Signature;

// ---------------------------------------------------------------------------
// Independent references
// ---------------------------------------------------------------------------

/// Packed NZCV of FCMP from host floating point (N = bit 3).
fn host_fcmp(width: u32, a: u64, b: u64) -> u64 {
    let (x, y) = if width == 32 {
        (
            f64::from(f32::from_bits(a as u32)),
            f64::from(f32::from_bits(b as u32)),
        )
    } else {
        (f64::from_bits(a), f64::from_bits(b))
    };
    if x.is_nan() || y.is_nan() {
        0b0011
    } else if x == y {
        0b0110
    } else if x < y {
        0b1000
    } else {
        0b0010
    }
}

fn eval_bv(expr: &SmtExpr, bindings: &[(&str, u64)]) -> u64 {
    let mut env = EvalEnv::default();
    for (name, value) in bindings {
        env.insert((*name).to_string(), *value);
    }
    match expr.try_eval(&env) {
        Ok(EvalResult::Bv(value)) => value,
        other => panic!("expected a bitvector, got {other:?}"),
    }
}

fn eval_bool(expr: &SmtExpr, bindings: &[(&str, u64)]) -> bool {
    let mut env = EvalEnv::default();
    for (name, value) in bindings {
        env.insert((*name).to_string(), *value);
    }
    match expr.try_eval(&env) {
        Ok(EvalResult::Bool(value)) => value,
        other => panic!("expected a Bool, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Decoder
// ---------------------------------------------------------------------------

#[test]
fn fp_compare_decoder_checks_every_fixed_bit_and_the_unallocated_rows() {
    for (width, word) in FCMP_WORDS {
        let decoded = decode_fp_compare(word).unwrap();
        assert_eq!(
            decoded,
            DecodedFpCompare {
                width,
                rn: 1,
                rm: 2,
                against_zero: false,
                signaling: false
            }
        );
        // Bits 31, 30, 29, 28..24, 21, 15..10 and 2..0 are fixed.
        for bit in [
            31, 30, 29, 28, 27, 26, 25, 24, 21, 15, 14, 13, 12, 11, 10, 2, 1, 0,
        ] {
            assert!(
                decode_fp_compare(word ^ (1 << bit)).is_err(),
                "bit {bit} of {word:#x}"
            );
        }
        assert!(matches!(
            decode_fp_compare(set_field(word, 23, 22, 0b10)),
            Err(FlagWordRefusal::Unallocated { .. })
        ));
        assert_eq!(
            decode_fp_compare(set_field(word, 23, 22, 0b11))
                .unwrap()
                .width,
            16
        );
        // Compare-with-zero requires Rm = 0.
        assert!(decode_fp_compare(set_field(word, 4, 3, 0b01)).is_err());
        let zero = decode_fp_compare(set_field(set_field(word, 20, 16, 0), 4, 3, 0b01)).unwrap();
        assert!(zero.against_zero && !zero.signaling);
        let signaling = decode_fp_compare(set_field(word, 4, 3, 0b10)).unwrap();
        assert!(signaling.signaling && !signaling.against_zero);
    }
    // Neighbouring classes never decode as FP compare.
    for other in [0x1E20_4020u32, 0x1E22_0C20, 0x9A82_0020, 0xD65F_03C0, 0] {
        assert!(decode_fp_compare(other).is_err(), "{other:#x}");
    }
}

// ---------------------------------------------------------------------------
// Integer-only FPCompare against host floating point
// ---------------------------------------------------------------------------

#[test]
fn integer_fpcompare_matches_host_fp_over_the_edge_grid_and_random_bits() {
    for width in [32u32, 64] {
        let a = SmtExpr::var("a", width);
        let b = SmtExpr::var("b", width);
        let relation = fp_compare_relation(&a, &b, width).unwrap();
        let packed = relation.packed();
        let flags = relation.flags();
        let edges: &[u64] = if width == 32 { &F32_EDGES } else { &F64_EDGES };
        let mut pairs: Vec<(u64, u64)> = edges
            .iter()
            .flat_map(|&x| edges.iter().map(move |&y| (x, y)))
            .collect();
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        for _ in 0..4096 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let x = state;
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let y = state;
            let mask = crate::smt::mask(u64::MAX, width);
            pairs.push((x & mask, y & mask));
            // Nearby magnitudes and sign-only differences exercise ordering.
            pairs.push((x & mask, (x & mask) ^ 1));
            pairs.push((x & mask, (x & mask) ^ (1 << (width - 1))));
        }
        for (x, y) in pairs {
            let bindings = [("a", x), ("b", y)];
            let want = host_fcmp(width, x, y);
            assert_eq!(eval_bv(&packed, &bindings), want, "w{width} {x:#x} {y:#x}");
            let from_flags = (u64::from(eval_bool(&flags.n, &bindings)) << 3)
                | (u64::from(eval_bool(&flags.z, &bindings)) << 2)
                | (u64::from(eval_bool(&flags.c, &bindings)) << 1)
                | u64::from(eval_bool(&flags.v, &bindings));
            assert_eq!(from_flags, want, "flags w{width} {x:#x} {y:#x}");
        }
    }
    assert!(fp_compare_relation(&SmtExpr::var("a", 16), &SmtExpr::var("b", 16), 16).is_err());
}

// ---------------------------------------------------------------------------
// Registered obligations
// ---------------------------------------------------------------------------

#[test]
fn registered_family_is_complete_unique_and_non_degenerate() {
    let proofs = all_flag_consumer_proofs();
    // 2 FCMP packed + 2 x 14 FCMP -> CSET + 3 ops x 2 widths x (2x10 CMP + 2x8 TST + 2x14 FCMP).
    assert_eq!(proofs.len(), 2 + 28 + 384);
    let mut names = HashSet::new();
    for (category, ob) in &proofs {
        assert_eq!(*category, FLAG_CONSUMER_CATEGORY);
        assert!(!ob.is_degenerate(), "{}", ob.name);
        assert!(names.insert(ob.name.clone()), "duplicate {}", ob.name);
        assert!(ob.preconditions.is_empty() && ob.fp_inputs.is_empty());
    }
    let lowered: Vec<String> = proofs
        .iter()
        .map(|(_, ob)| ob.name.to_lowercase())
        .collect();
    let mut queries = Vec::new();
    for width in [32, 64] {
        queries.push(fcmp_packed_query(width).unwrap());
        for cc in 0..14 {
            queries.push(fcmp_cset_query(width, cc).unwrap());
        }
    }
    queries.extend(SelectForm::all().into_iter().map(SelectForm::query));
    assert_eq!(queries.len(), proofs.len());
    for query in queries {
        let hits = lowered.iter().filter(|name| name.contains(query)).count();
        assert_eq!(hits, 1, "{query} must name exactly one obligation");
    }
    assert!(fcmp_packed_query(16).is_none());
    assert!(fcmp_cset_query(32, 14).is_none());
}

#[test]
fn fcmp_families_route_through_the_checked_scalar_fp_evaluator() {
    for width in [32, 64] {
        let packed = fcmp_packed_obligation(width).unwrap();
        assert!(
            uses_checked_scalar_fp_evaluation(&packed),
            "{}",
            packed.name
        );
        for cc in 0..14 {
            let cset = fcmp_cset_obligation(width, cc).unwrap();
            assert!(uses_checked_scalar_fp_evaluation(&cset), "{}", cset.name);
        }
    }
    // Selects carry integer arms and use the ordinary evaluator.
    let select = select_obligation(SelectForm {
        op: SelectOp::Csel,
        width: 64,
        producer: ProducerForm::new(ProducerKind::Fcmp, 64),
        cond: 10,
    })
    .unwrap();
    assert!(!uses_checked_scalar_fp_evaluation(&select));
}

#[test]
fn every_registered_obligation_agrees_on_the_boundary_battery() {
    let mut points = 0;
    for (_, ob) in all_flag_consumer_proofs() {
        match battery_check(&ob).unwrap() {
            BatteryOutcome::Agreed(n) => points += n,
            BatteryOutcome::Counterexample(detail) => panic!("{detail}"),
        }
    }
    // FCMP packed/CSET: 30 x 484; selects: 3 x 2 x (36 x 225..196 + 28 x 1452).
    assert!(points > 250_000, "{points}");
}

#[test]
fn small_sample_standard_evaluation_accepts_representative_forms() {
    // Finite evaluation, NOT formal discharge: 256 random samples plus the
    // evaluators' own edge points. The coverage gate runs the full default.
    let config = VerificationConfig::with_sample_count(256);
    let mut obligations = vec![
        fcmp_packed_obligation(32).unwrap(),
        fcmp_packed_obligation(64).unwrap(),
        fcmp_cset_obligation(32, 1).unwrap(),
        fcmp_cset_obligation(64, 10).unwrap(),
    ];
    for producer in ProducerForm::ALL {
        for op in SelectOp::ALL {
            for width in [32, 64] {
                obligations.push(
                    select_obligation(SelectForm {
                        op,
                        width,
                        producer,
                        cond: control_condition(producer),
                    })
                    .unwrap(),
                );
            }
        }
    }
    for ob in obligations {
        assert!(
            matches!(
                verify_by_evaluation_with_config(&ob, &config),
                VerificationResult::Valid
            ),
            "{}",
            ob.name
        );
    }
}

#[test]
fn fcmp_cset_ne_is_unordered_and_the_ordered_claim_refutes_on_nan() {
    // NE after FCMP holds on an unordered result: it is `une`, not `one`.
    let ne = fcmp_cset_obligation(32, 1).unwrap();
    let nan = [("a_bits", 0x7fc0_0000), ("b_bits", 0x3f80_0000)];
    assert_eq!(eval_bv(&ne.aarch64_expr, &nan), 1);
    assert_eq!(eval_bv(&ne.trust_ir_expr, &nan), 1);
    let ordered = fcmp_cset_obligation_with(
        32,
        1,
        Some(FlagMutation::ClaimedPredicate(FloatCC::NotEqual)),
    )
    .unwrap();
    assert_eq!(eval_bv(&ordered.trust_ir_expr, &nan), 0);
    assert!(matches!(
        battery_check(&ordered).unwrap(),
        BatteryOutcome::Counterexample(_)
    ));
    assert!(matches!(
        verify_by_evaluation_with_config(&ordered, &VerificationConfig::with_sample_count(0)),
        VerificationResult::Invalid { .. }
    ));
}

// ---------------------------------------------------------------------------
// Captured words, controls and the credit hook
// ---------------------------------------------------------------------------

#[test]
fn captured_words_decode_back_to_their_instructions() {
    let corpus = captured_flag_words();
    assert_eq!(corpus.len(), 3 * 2 * 14 + 2 * 14 + 2);
    for entry in &corpus {
        check_captured_flag_word(entry).unwrap_or_else(|error| panic!("{entry:?}: {error}"));
    }
    // A stale word is refused.
    let mut stale = corpus[0].clone();
    stale.word = with_condition(stale.word, 1);
    assert!(check_captured_flag_word(&stale).is_err());
}

#[test]
fn every_control_is_refuted_for_its_stated_reason() {
    let controls = flag_controls();
    let mut per_opcode: HashMap<AArch64Opcode, usize> = HashMap::new();
    for control in &controls {
        run_control(control).unwrap_or_else(|error| panic!("{error}"));
        *per_opcode.entry(control.opcode).or_default() += 1;
    }
    // Per select op: 2 widths x 6 producers x (7, +1 for CSINC/CSNEG).
    assert_eq!(per_opcode[&AArch64Opcode::Csel], 2 * 6 * 7);
    assert_eq!(per_opcode[&AArch64Opcode::Csinc], 2 * 6 * 8);
    assert_eq!(per_opcode[&AArch64Opcode::Csneg], 2 * 6 * 8);
    assert_eq!(per_opcode[&AArch64Opcode::Fcmp], 2 * 9);
    assert_eq!(per_opcode[&AArch64Opcode::CSet], 2 * 8);
}

#[test]
fn credit_hook_accepts_all_five_rows_and_refuses_stale_inputs() {
    for opcode in [
        AArch64Opcode::Fcmp,
        AArch64Opcode::CSet,
        AArch64Opcode::Csel,
        AArch64Opcode::Csinc,
        AArch64Opcode::Csneg,
    ] {
        let credit = flag_consumer_credit(opcode).unwrap_or_else(|error| panic!("{error}"));
        assert!(credit.captured_words > 0 && credit.controls_refuted > 0);
        match opcode {
            AArch64Opcode::Fcmp => assert_eq!((credit.own_forms, credit.borrowed_forms), (2, 0)),
            AArch64Opcode::CSet => {
                assert_eq!((credit.own_forms, credit.borrowed_forms), (28, 44));
            }
            _ => assert_eq!((credit.own_forms, credit.borrowed_forms), (128, 0)),
        }
    }
    assert!(flag_consumer_credit(AArch64Opcode::Csinv).is_err());

    // A stale captured word and a surviving control are both refused.
    let mut corpus = captured_flag_words();
    let index = corpus
        .iter()
        .position(|entry| entry.inst.opcode == AArch64Opcode::Fcmp)
        .unwrap();
    corpus[index].word = set_field(corpus[index].word, 20, 16, 3);
    assert!(flag_consumer_credit_with(AArch64Opcode::Fcmp, &corpus, &flag_controls()).is_err());
    let surviving = FlagControl {
        opcode: AArch64Opcode::Fcmp,
        label: "the canonical word itself".into(),
        target: ControlTarget::FcmpPacked(32),
        mutation: FlagMutation::Word(canonical_fcmp_word(32).unwrap()),
        expected: ControlExpectation::Counterexample,
    };
    let error =
        flag_consumer_credit_with(AArch64Opcode::Fcmp, &captured_flag_words(), &[surviving])
            .unwrap_err();
    assert!(error.contains("survived"), "{error}");
    assert!(
        flag_consumer_credit_with(AArch64Opcode::Fcmp, &captured_flag_words(), &[]).is_err(),
        "an opcode without controls must not be credited"
    );
}

// ---------------------------------------------------------------------------
// Producer walk and consumer binding
// ---------------------------------------------------------------------------

fn function(insts: Vec<MachInst>) -> MachFunction {
    let mut func = MachFunction::new(
        "flag_consumer_test".to_string(),
        Signature::new(vec![], vec![]),
    );
    for (index, inst) in insts.into_iter().enumerate() {
        func.insts.push(inst);
        func.blocks[0].insts.push(InstId(index as u32));
    }
    func
}

fn csel(op: AArch64Opcode, width: u32, cc: i64) -> MachInst {
    MachInst::new(
        op,
        vec![
            gpr(width, 0),
            gpr(width, 1),
            gpr(width, 2),
            MachOperand::Imm(cc),
        ],
    )
}

fn cmp(width: u32) -> MachInst {
    MachInst::new(AArch64Opcode::CmpRR, vec![gpr(width, 3), gpr(width, 4)])
}

#[test]
fn select_binding_names_its_reaching_producer_width_and_condition() {
    let func = function(vec![
        cmp(32),
        MachInst::new(
            AArch64Opcode::AddRR,
            vec![gpr(64, 5), gpr(64, 6), gpr(64, 7)],
        ),
        csel(AArch64Opcode::Csinc, 64, 11),
    ]);
    let insts = func.blocks[0].insts.clone();
    assert_eq!(
        select_query(&func, &insts, 2),
        Some(("a64 nzcv csinc x over cmp w32 lt:", FLAG_CONSUMER_CATEGORY))
    );
    // The nearest producer wins: an intervening TST replaces the CMP's flags.
    let func = function(vec![
        cmp(64),
        MachInst::new(AArch64Opcode::Tst, vec![gpr(32, 3), gpr(32, 4)]),
        csel(AArch64Opcode::Csel, 32, 1),
    ]);
    let insts = func.blocks[0].insts.clone();
    assert_eq!(
        select_query(&func, &insts, 2),
        Some(("a64 nzcv csel w over tst w32 ne:", FLAG_CONSUMER_CATEGORY))
    );
    // FCMP producers bind by their S/D width.
    let func = function(vec![
        MachInst::new(AArch64Opcode::Fcmp, vec![fpr(64, 1), fpr(64, 2)]),
        csel(AArch64Opcode::Csneg, 32, 10),
    ]);
    let insts = func.blocks[0].insts.clone();
    assert_eq!(
        select_query(&func, &insts, 1),
        Some(("a64 nzcv csneg w over fcmp f64 ge:", FLAG_CONSUMER_CATEGORY))
    );
}

#[test]
fn select_binding_fails_closed_without_a_modeled_reaching_producer() {
    let refused = |insts: Vec<MachInst>| {
        let func = function(insts);
        let block = func.blocks[0].insts.clone();
        select_query(&func, &block, block.len() - 1)
    };
    // No producer in the block.
    assert_eq!(refused(vec![csel(AArch64Opcode::Csel, 64, 0)]), None);
    // A call between producer and consumer.
    assert_eq!(
        refused(vec![
            cmp(64),
            MachInst::new(AArch64Opcode::Bl, vec![MachOperand::Imm(0)]),
            csel(AArch64Opcode::Csel, 64, 0),
        ]),
        None
    );
    // A call or a flag-writing pseudo whose INSTANCE flags were rebuilt empty
    // is still opaque: the opcode's declared control transfer, or its pseudo
    // expansion, may write NZCV.
    for opcode in [
        AArch64Opcode::Bl,
        AArch64Opcode::Blr,
        AArch64Opcode::TlsDescCall,
        AArch64Opcode::TrapBoundsCheck,
    ] {
        let stripped =
            MachInst::with_flags(opcode, vec![gpr(64, 9)], trust_cg_ir::InstFlags::EMPTY);
        assert!(!stripped.is_call() && !stripped.is_branch());
        assert_eq!(
            refused(vec![cmp(64), stripped, csel(AArch64Opcode::Csel, 64, 0)]),
            None,
            "{opcode:?} with stripped instance flags"
        );
    }
    // An implicit NZCV definition.
    let mut clobber = MachInst::new(
        AArch64Opcode::AddRR,
        vec![gpr(64, 5), gpr(64, 6), gpr(64, 7)],
    );
    clobber.implicit_defs = &[trust_cg_ir::aarch64_regs::NZCV];
    assert_eq!(
        refused(vec![cmp(64), clobber, csel(AArch64Opcode::Csel, 64, 0)]),
        None
    );
    // Unmodeled producer kinds and conditions without a predicate.
    assert_eq!(
        refused(vec![
            MachInst::new(
                AArch64Opcode::AddsRR,
                vec![gpr(64, 0), gpr(64, 1), gpr(64, 2)]
            ),
            csel(AArch64Opcode::Csel, 64, 6),
        ]),
        None
    );
    assert_eq!(
        refused(vec![cmp(64), csel(AArch64Opcode::Csel, 64, 4)]),
        None
    ); // MI after CMP
    assert_eq!(
        refused(vec![
            MachInst::new(AArch64Opcode::Tst, vec![gpr(64, 3), gpr(64, 4)]),
            csel(AArch64Opcode::Csel, 64, 2), // HS after TST is constant
        ]),
        None
    );
    // Malformed producers and consumers.
    assert_eq!(
        refused(vec![
            MachInst::new(AArch64Opcode::CmpRR, vec![gpr(64, 3), gpr(32, 4)]),
            csel(AArch64Opcode::Csel, 64, 0),
        ]),
        None
    );
    assert_eq!(
        refused(vec![
            MachInst::new(
                AArch64Opcode::Fcmp,
                vec![
                    MachOperand::PReg(PReg::new(165)),
                    MachOperand::PReg(PReg::new(166))
                ]
            ),
            csel(AArch64Opcode::Csel, 64, 0),
        ]),
        None
    );
    for cc in [14, 15, -1, 16] {
        assert_eq!(
            refused(vec![cmp(64), csel(AArch64Opcode::Csel, 64, cc)]),
            None
        );
    }
    assert_eq!(
        refused(vec![
            cmp(64),
            MachInst::new(
                AArch64Opcode::Csel,
                vec![gpr(64, 0), gpr(32, 1), gpr(64, 2), MachOperand::Imm(0)]
            ),
        ]),
        None
    );
    // CSINV is not a bound select.
    assert_eq!(
        refused(vec![cmp(64), csel(AArch64Opcode::Csinv, 64, 0)]),
        None
    );
    // A zero-register destination discards the value.
    assert_eq!(
        refused(vec![
            cmp(64),
            MachInst::new(
                AArch64Opcode::Csel,
                vec![
                    MachOperand::PReg(PReg::new(160)),
                    gpr(64, 1),
                    gpr(64, 2),
                    MachOperand::Imm(0)
                ]
            ),
        ]),
        None
    );
}

#[test]
fn source_bound_policy_admits_only_the_scalar_body_instructions() {
    let func = function(vec![
        cmp(64),
        MachInst::new(
            AArch64Opcode::LdrRI,
            vec![gpr(64, 5), gpr(64, 6), MachOperand::Imm(0)],
        ),
        MachInst::new(AArch64Opcode::CSet, vec![gpr(64, 0), MachOperand::Imm(0)]),
    ]);
    let insts = func.blocks[0].insts.clone();
    assert!(reaching_flag_producer(&func, &insts, 2, TransparencyPolicy::TargetFlagModel).is_ok());
    assert_eq!(
        reaching_flag_producer(&func, &insts, 2, TransparencyPolicy::SourceBoundScalarBody).err(),
        Some(ProducerRefusal::Opaque(AArch64Opcode::LdrRI))
    );
    assert_eq!(
        reaching_flag_producer(&func, &insts, 3, TransparencyPolicy::TargetFlagModel).err(),
        Some(ProducerRefusal::OutOfBlock)
    );
    assert_eq!(
        reaching_flag_producer(&func, &insts, 0, TransparencyPolicy::TargetFlagModel).err(),
        Some(ProducerRefusal::BlockStart)
    );
}

#[test]
fn fcmp_binding_requires_matching_s_or_d_operands() {
    let fcmp = |operands| MachInst::new(AArch64Opcode::Fcmp, operands);
    assert_eq!(
        fcmp_query(&fcmp(vec![fpr(32, 0), fpr(32, 1)])),
        Some(("a64 nzcv fcmp f32 packed:", FLAG_CONSUMER_CATEGORY))
    );
    assert_eq!(
        fcmp_query(&fcmp(vec![fpr(64, 0), fpr(64, 31)])),
        Some(("a64 nzcv fcmp f64 packed:", FLAG_CONSUMER_CATEGORY))
    );
    for operands in [
        vec![],
        vec![fpr(32, 0)],
        vec![fpr(32, 0), fpr(64, 1)],
        vec![fpr(32, 0), fpr(32, 1), MachOperand::Imm(0)],
        vec![fpr(32, 0), MachOperand::Imm(0)],
        vec![gpr(64, 0), gpr(64, 1)],
        vec![
            MachOperand::PReg(PReg::new(165)),
            MachOperand::PReg(PReg::new(166)),
        ],
        vec![
            MachOperand::PReg(PReg::new(64)),
            MachOperand::PReg(PReg::new(65)),
        ],
    ] {
        assert_eq!(fcmp_query(&fcmp(operands.clone())), None, "{operands:?}");
    }
}
