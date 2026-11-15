// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use trust_cg_ir::regs::VReg;

fn vreg(id: u32, class: RegClass) -> MachOperand {
    MachOperand::VReg(VReg::new(id, class))
}

fn x_reg(n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(n))
}

fn w_reg(n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(32 + n))
}

fn holds(carrier: &TrapCarrier, words: &[u32]) -> Decision {
    let ob = trap_expansion_obligation(carrier, words).expect("an expansion");
    decide(&ob)
}

fn refuted_either_way(carrier: &TrapCarrier, words: &[u32]) -> bool {
    match trap_expansion_obligation(carrier, words) {
        Err(TrapRefusal::Refuted(_)) => true,
        Err(other) => panic!("{other}"),
        Ok(ob) => matches!(decide(&ob), Decision::Refuted { .. }),
    }
}

#[test]
fn every_battery_form_holds_and_every_control_is_refuted() {
    let credit = trap_expansion_credit().expect("credit");
    assert_eq!(credit.forms, trap_battery().len());
    let controls: usize = trap_battery().iter().map(|c| trap_controls(c).len()).sum();
    assert_eq!(credit.controls_refuted, controls);
    // Pinned: a change to the battery or the controls is deliberate. 42/397
    // since the five wide-immediate bounds on a 32-bit index (W16 scratch)
    // joined the 37/337 (L04-P12 landing).
    assert_eq!((credit.forms, credit.controls_refuted), (42, 397));
    // Every conditional carrier opcode has forms in the battery.
    for &opcode in CONDITIONAL_TRAP_OPCODES {
        assert!(
            trap_battery().iter().any(|c| c.opcode == opcode),
            "{opcode:?}"
        );
    }
}

#[test]
fn the_decision_method_is_the_automaton_except_for_the_multiplications() {
    for carrier in trap_battery() {
        let words = stated_words(&carrier).unwrap();
        let method = match holds(&carrier, &words) {
            Decision::Holds { method } => method,
            other => panic!("{carrier:?}: {other:?}"),
        };
        let is_mul = matches!(
            carrier.kind,
            TrapKind::Overflow {
                op: OverflowOp::SignedMul | OverflowOp::UnsignedMul,
                ..
            }
        );
        assert_eq!(
            method,
            if is_mul {
                METHOD_NORMALIZATION
            } else {
                METHOD_BITSERIAL
            },
            "{carrier:?}"
        );
    }
}

/// The four controls the ledger row names, on every conditional form.
#[test]
fn named_corruptions_refute_on_every_conditional_form() {
    for carrier in trap_battery()
        .into_iter()
        .filter(TrapCarrier::is_conditional)
    {
        let controls = trap_controls(&carrier);
        for label in [
            "BRK #2 instead of the trap code",
            "branch past the next word (around the trap)",
        ] {
            assert!(
                controls.iter().any(|c| c.label == label),
                "{carrier:?} lacks {label}"
            );
        }
        assert!(
            controls
                .iter()
                .any(|c| c.label == "inverted branch condition" || c.label == "CBZ instead of CBNZ"),
            "{carrier:?} lacks an inverted condition"
        );
        if let TrapKind::Bounds {
            bound: Bound::Imm(k @ 1..=0xFFE),
            ..
        } = carrier.kind
        {
            for label in ["bound one too large", "bound one too small"] {
                assert!(
                    controls.iter().any(|c| c.label == label),
                    "{carrier:?} (bound {k}) lacks {label}"
                );
            }
        }
        for control in &controls {
            assert!(
                refuted_either_way(&carrier, &control.words),
                "{carrier:?}: {}",
                control.label
            );
        }
    }
}

#[test]
fn an_off_by_one_bound_is_refuted_with_the_boundary_counterexample() {
    let carrier = TrapCarrier {
        opcode: O::TrapBoundsCheckExact,
        kind: TrapKind::Bounds {
            index: Gpr {
                number: 2,
                width: 64,
            },
            bound: Bound::Imm(10),
        },
    };
    let words = stated_words(&carrier).unwrap();
    // CMP x2, #11 instead of #10: index 10 must trap and does not.
    let wrong = with_word(&words, 0, (words[0] & !(0xFFF << 10)) | (11 << 10));
    match holds(&carrier, &wrong) {
        Decision::Refuted { reason } => assert!(reason.contains("(\"x2\", 10)"), "{reason}"),
        other => panic!("{other:?}"),
    }
    // A shift range off by one (CMP #63 for a 64-bit shift) is refuted too.
    let shift = TrapCarrier {
        opcode: O::TrapShiftRangeIfOOB,
        kind: TrapKind::ShiftRange {
            amount: Gpr {
                number: 5,
                width: 64,
            },
            bitwidth: 64,
        },
    };
    let words = stated_words(&shift).unwrap();
    let wrong = with_word(&words, 0, (words[0] & !(0xFFF << 10)) | (63 << 10));
    assert!(matches!(holds(&shift, &wrong), Decision::Refuted { .. }));
}

#[test]
fn structural_violations_are_refuted_by_name() {
    let carrier = TrapCarrier {
        opcode: O::TrapDivZeroIfZero,
        kind: TrapKind::DivZero {
            divisor: Gpr {
                number: 3,
                width: 64,
            },
        },
    };
    let words = stated_words(&carrier).unwrap();
    assert_eq!(words, vec![0xB500_0043, 0xD420_0020]);
    let refusal = |words: &[u32]| match trap_expansion_obligation(&carrier, words) {
        Err(TrapRefusal::Refuted(why)) => why,
        other => panic!("{other:?}"),
    };
    assert!(refusal(&[words[0], 0xD420_0040]).contains("BRK #2"));
    assert!(refusal(&[0xB500_0063, words[1]]).contains("moves 3 words"));
    // CMP x0, x1 in the trap's place, and a NOP, which no expansion uses.
    assert!(refusal(&[words[0], 0xEB01_001F]).contains("not BRK"));
    assert!(refusal(&[words[0], 0xD503_201F]).contains("no instruction class"));
    assert!(refusal(&[]).contains("empty"));
    // A MOVZ into a live register before the branch.
    let bounds = TrapCarrier {
        opcode: O::TrapBoundsCheckExact,
        kind: TrapKind::Bounds {
            index: Gpr {
                number: 2,
                width: 64,
            },
            bound: Bound::Imm(0x1_2345),
        },
    };
    let words = stated_words(&bounds).unwrap();
    let clobber = with_word(&words, 0, (words[0] & !0x1F) | 4);
    match trap_expansion_obligation(&bounds, &clobber) {
        Err(TrapRefusal::Refuted(why)) => assert!(why.contains("writes x4"), "{why}"),
        other => panic!("{other:?}"),
    }
    // A B.cond with no flag-setting word reads incoming flags: refuted.
    let flags_in = [0x5400_0043, 0xD420_0020];
    assert!(refuted_either_way(&bounds, &flags_in));
}

#[test]
fn pre_allocation_carriers_take_distinct_role_registers() {
    let g64 = RegClass::Gpr64;
    let g32 = RegClass::Gpr32;
    let cases = [
        MachInst::new(O::TrapNullIfZero, vec![vreg(9, g64)]),
        MachInst::new(O::TrapDivZeroIfZero, vec![vreg(9, g32)]),
        MachInst::new(
            O::TrapBoundsCheckExact,
            vec![vreg(1, g64), vreg(2, g64), MachOperand::Imm(77)],
        ),
        MachInst::new(
            O::TrapBoundsCheckExact,
            vec![vreg(1, g64), vreg(2, g64), MachOperand::Imm(0x7FFF_FFFF)],
        ),
        MachInst::new(
            O::TrapBoundsCheckExact,
            vec![vreg(1, g64), vreg(2, g64), vreg(3, g64)],
        ),
        MachInst::new(
            O::TrapShiftRangeIfOOB,
            vec![vreg(4, g32), MachOperand::Imm(32)],
        ),
        MachInst::new(
            O::TrapOverflowExact,
            vec![
                vreg(5, g64),
                vreg(5, g64),
                MachOperand::Imm(trust_cg_ir::overflow_tag::pack_overflow_tag(
                    OverflowOp::SignedMul,
                    64,
                )),
            ],
        ),
        MachInst::new(
            O::TrapOverflowExact,
            vec![
                vreg(5, g32),
                vreg(6, g32),
                MachOperand::Imm(trust_cg_ir::overflow_tag::pack_overflow_tag(
                    OverflowOp::UnsignedSub,
                    32,
                )),
            ],
        ),
    ];
    for inst in cases {
        match carrier_verdict(&inst) {
            TrapVerdict::Holds {
                conditional: true,
                replay: Some(replay),
                ..
            } => assert!(
                replay.obligation().name.ends_with("registers renamed"),
                "{replay:?}"
            ),
            other => panic!("{inst:?}: {other:?}"),
        }
    }
    // Role registers never collide with the expansion's scratch registers.
    let carrier = trap_carrier(&MachInst::new(
        O::TrapBoundsCheckExact,
        vec![vreg(1, g64), vreg(2, g64), vreg(3, g64)],
    ))
    .unwrap();
    assert_eq!(
        carrier.kind,
        TrapKind::Bounds {
            index: Gpr {
                number: 1,
                width: 64
            },
            bound: Bound::Reg(Gpr {
                number: 2,
                width: 64
            }),
        }
    );
}

#[test]
fn unmodeled_carriers_are_refused_by_name() {
    let bad_tag = MachInst::new(
        O::TrapOverflowExact,
        vec![x_reg(0), x_reg(1), MachOperand::Imm(9999)],
    );
    let mul32 = MachInst::new(
        O::TrapOverflowExact,
        vec![
            w_reg(0),
            w_reg(1),
            MachOperand::Imm(trust_cg_ir::overflow_tag::pack_overflow_tag(
                OverflowOp::SignedMul,
                32,
            )),
        ],
    );
    let cases = [
        (MachInst::new(O::TrapDivZeroIfZero, vec![]), "0 operands"),
        (bad_tag, "tag does not decode"),
        (mul32, "64-bit only"),
        (
            MachInst::new(
                O::TrapBoundsCheckExact,
                vec![x_reg(0), x_reg(1), MachOperand::Imm(1 << 31)],
            ),
            "outside [0, i32::MAX]",
        ),
        (
            MachInst::new(O::TrapBoundsCheckExact, vec![x_reg(0), x_reg(1), w_reg(2)]),
            "differ in width",
        ),
        (
            MachInst::new(O::TrapShiftRangeIfOOB, vec![x_reg(0), MachOperand::Imm(0)]),
            "[1, 4095]",
        ),
        (
            MachInst::new(O::Brk, vec![MachOperand::Imm(1), MachOperand::Imm(2)]),
            "BRK takes",
        ),
        (MachInst::new(O::TrapNull, vec![x_reg(0)]), "expected 0"),
        (
            MachInst::new(O::TrapNullIfZero, vec![vreg(1, RegClass::Fpr64)]),
            "operand class",
        ),
    ];
    for (inst, needle) in cases {
        match carrier_verdict(&inst) {
            TrapVerdict::Refused { reason } => assert!(
                reason.contains(needle) && reason.contains("not a modeled trap carrier"),
                "{inst:?}: {reason}"
            ),
            other => panic!("{inst:?}: {other:?}"),
        }
    }
}

#[test]
fn unconditional_traps_hold_only_as_their_own_brk() {
    for opcode in [
        O::Brk,
        O::TrapOverflow,
        O::TrapBoundsCheck,
        O::TrapNull,
        O::TrapDivZero,
        O::TrapShiftRange,
    ] {
        let verdict = carrier_verdict(&MachInst::new(opcode, vec![]));
        assert!(
            matches!(
                verdict,
                TrapVerdict::Holds {
                    conditional: false,
                    replay: None,
                    ..
                }
            ),
            "{opcode:?}: {verdict:?}"
        );
    }
    // A named immediate is its own code.
    let stack_limit = MachInst::new(O::Brk, vec![MachOperand::Imm(0x534C)]);
    let carrier = trap_carrier(&stack_limit).unwrap();
    assert_eq!(stated_words(&carrier).unwrap(), vec![0xD42A_6980]);
    assert!(matches!(
        carrier_verdict(&stack_limit),
        TrapVerdict::Holds { .. }
    ));
    let one = trap_carrier(&MachInst::new(O::TrapNull, vec![])).unwrap();
    assert!(refuted_either_way(&one, &[0xD420_0000]));
    assert!(refuted_either_way(&one, &[0xD420_0020, 0xD420_0020]));
}

#[test]
fn emitted_words_bind_through_the_enc5_entry_point() {
    for carrier in trap_battery() {
        let words = stated_words(&carrier).unwrap();
        let inst = carrier_instruction(&carrier);
        assert_eq!(
            check_emitted_trap_expansion(&inst, &words),
            Ok(()),
            "{carrier:?}"
        );
        for control in trap_controls(&carrier) {
            assert!(
                check_emitted_trap_expansion(&inst, &control.words).is_err(),
                "{carrier:?}: {}",
                control.label
            );
        }
    }
    // A recorded carrier outside the model is refused by name, not passed on
    // the per-word checks alone: a missing operand, the zero register as the
    // guarded operand, mixed index and bound widths, a shift width outside
    // [1, 4095].
    let faithful_cbnz_xzr = [0xB500_005F, 0xD420_0020];
    let cases = [
        (
            MachInst::new(O::TrapDivZeroIfZero, vec![]),
            vec![0xD420_0020],
        ),
        (
            MachInst::new(
                O::TrapNullIfZero,
                vec![MachOperand::Special(SpecialReg::XZR)],
            ),
            faithful_cbnz_xzr.to_vec(),
        ),
        (
            MachInst::new(O::TrapBoundsCheckExact, vec![x_reg(0), x_reg(1), w_reg(2)]),
            vec![0xEB02_003F, 0x5400_0043, 0xD420_0020],
        ),
        (
            MachInst::new(O::TrapShiftRangeIfOOB, vec![x_reg(0), MachOperand::Imm(0)]),
            vec![0xF100_001F, 0x5400_0043, 0xD420_0020],
        ),
    ];
    for (bad, words) in cases {
        let error = check_emitted_trap_expansion(&bad, &words).expect_err("refused by name");
        assert!(
            error.contains("not a modeled trap carrier") && error.contains("outside the model"),
            "{bad:?}: {error}"
        );
    }
}

#[test]
fn the_rewrites_the_multiplication_decision_uses_are_sound() {
    use crate::bitserial_decide::decide_equal;
    // `x + ~y + 1 == 0` is `x == y`, at every width the expansions use.
    for width in [8u32, 32, 64] {
        let (x, y) = (E::var("x", width), E::var("y", width));
        let sum = x
            .clone()
            .bvadd(y.clone().bvxor(konst(u64::MAX, width)))
            .bvadd(konst(1, width));
        let rewritten = rewrite(sum.clone().eq_expr(konst(0, width)));
        assert_eq!(rewritten, canonical_eq(x.clone().eq_expr(y.clone())));
        assert_eq!(
            decide_equal(&sum.eq_expr(konst(0, width)), &x.eq_expr(y)),
            Ok(Exact::Holds)
        );
    }
    // Truncation of a product is the product of the truncations, and an
    // extension is a concatenation: exhaustively at 8 bits.
    let (a, b) = (E::var("a", 8), E::var("b", 8));
    let wide = a.clone().sign_ext(8).bvmul(b.clone().sign_ext(8));
    let low = normal_form(&wide.clone().extract(7, 0)).unwrap();
    assert_eq!(low, a.clone().bvmul(b.clone()));
    let sext = normal_form(&a.clone().sign_ext(8)).unwrap();
    for va in 0..=255u64 {
        let mut env = EvalEnv::default();
        env.insert("a".into(), va);
        assert!(evaluations_equal(
            &sext.eval(&env),
            &a.clone().sign_ext(8).eval(&env)
        ));
        for vb in (0..=255u64).step_by(7) {
            env.insert("b".into(), vb);
            assert!(evaluations_equal(
                &low.eval(&env),
                &wide.clone().extract(7, 0).eval(&env)
            ));
        }
    }
}

#[test]
fn the_obligation_is_a_replayable_bit_vector_query() {
    let carrier = TrapCarrier {
        opcode: O::TrapOverflowExact,
        kind: TrapKind::Overflow {
            lhs: Gpr {
                number: 0,
                width: 32,
            },
            rhs: Gpr {
                number: 1,
                width: 32,
            },
            op: OverflowOp::SignedAdd,
            width: 32,
        },
    };
    let ob = trap_expansion_obligation(&carrier, &stated_words(&carrier).unwrap()).unwrap();
    assert_eq!(ob.obligation.trust_ir_expr.bv_width(), 1);
    assert_eq!(ob.obligation.aarch64_expr.bv_width(), 1);
    assert_eq!(
        ob.obligation.inputs,
        vec![("x0".to_string(), 64), ("x1".to_string(), 64)]
    );
    assert!(ob.obligation.is_genuinely_proven());
    // The sampled evaluator agrees with the exact decision.
    assert!(matches!(
        crate::lowering_proof::verify_by_evaluation(&ob.obligation),
        crate::verify::VerificationResult::Valid
    ));
}

fn promotion_request() -> crate::FunctionVerificationRequest {
    crate::FunctionVerificationRequest::capture(
        crate::lowering_proof::VerificationConfig::for_proof_promotion(),
        crate::provenance_xcheck::ProvenanceXCheckMode::Enforce,
    )
}

fn holding_replay(carrier: &TrapCarrier) -> TrapExpansionReplay {
    match carrier_verdict(&carrier_instruction(carrier)) {
        TrapVerdict::Holds {
            replay: Some(replay),
            ..
        } => replay,
        other => panic!("{carrier:?}: {other:?}"),
    }
}

/// With explicit proof authority (`TCG_EXTERNAL_CLEAN_CHECKER` and the
/// admitted AY), every conditional form's obligation is replayed through one
/// verification request: an answer that is not a Clean-checked proof stays
/// uncredited, a counterexample would contradict the in-process decision and
/// fails, and no corruption control may ever be certified. Prints the census
/// of what this host's tools check (`TRAP_EXPANSION_REPLAY`).
#[test]
fn live_replay_is_clean_checked_or_fails_closed() {
    use crate::verify::VerificationResult;
    if std::env::var_os("TCG_EXTERNAL_CLEAN_CHECKER").is_none() {
        crate::formal_gap::skip_test(
            "live_replay_is_clean_checked_or_fails_closed",
            crate::formal_gap::NO_EXPLICIT_AUTHORITY_ENV,
        );
        return;
    }
    let _solver_lock = crate::ay_bridge::formal_solver_test_lock();
    let request = promotion_request();
    let context = crate::function_request::FunctionDischargeContext::new(&request);
    let (mut checked, mut not_checked) = (0usize, Vec::new());
    for carrier in trap_battery()
        .into_iter()
        .filter(TrapCarrier::is_conditional)
    {
        match context.trap_expansion(&holding_replay(&carrier)) {
            (Some(VerificationResult::Valid), _) => checked += 1,
            (Some(VerificationResult::Invalid { counterexample }), _) => panic!(
                "{carrier:?}: the solver contradicts the in-process decision: {counterexample}"
            ),
            (other, why) => not_checked.push(format!("{carrier:?}: {other:?} {why:?}")),
        }
        // One control per form: never certified.
        if let Some(control) = trap_controls(&carrier)
            .into_iter()
            .find(|c| c.label == "inverted branch condition" || c.label == "CBZ instead of CBNZ")
        {
            let control_ob = trap_expansion_obligation(&carrier, &control.words).unwrap();
            assert!(
                !matches!(
                    context
                        .trap_expansion(&TrapExpansionReplay::for_test(&control_ob))
                        .0,
                    Some(VerificationResult::Valid)
                ),
                "{carrier:?}: a corrupted expansion was certified"
            );
        }
    }
    eprintln!(
        "TRAP_EXPANSION_REPLAY checked={checked} not_checked={}",
        not_checked.len()
    );
    for line in &not_checked {
        eprintln!("TRAP_EXPANSION_REPLAY not checked: {line}");
    }
}

/// The replay is the request's, never the process's: the same query under two
/// requests in one process gets each request's own answer, in either order
/// (a request captured while the tier-0 recorder is armed refuses; one whose
/// AY identity rule admitted no AY, or that froze `TCG_REFINE_SOLVER=0`,
/// cannot certify). Needs no tools.
#[test]
fn replay_is_bound_to_the_request_not_the_process() {
    let carrier = trap_battery()
        .into_iter()
        .find(|carrier| carrier.opcode == O::TrapDivZeroIfZero)
        .expect("a division guard");
    let replay = holding_replay(&carrier);
    let recording = promotion_request().captured_while_recording();
    let (no_ay, no_refine) = trust_cg_process_env::with_env_edits(|env| {
        env.set("AY_SOLVER_PATH", "/nonexistent/trap-expansion-ay");
        env.set(
            "TCG_EXTERNAL_CLEAN_CHECKER",
            "/nonexistent/trap-expansion-clean",
        );
        env.remove("TCG_REFINE_SOLVER");
        let no_ay = promotion_request();
        env.set("TCG_REFINE_SOLVER", "0");
        (no_ay, promotion_request())
    });
    assert!(no_ay.ay_solver().is_none(), "{:?}", no_ay.ay_refusal());
    let answer = |request: &crate::FunctionVerificationRequest| {
        let (verdict, why) =
            crate::function_request::FunctionDischargeContext::new(request).trap_expansion(&replay);
        assert!(verdict.is_none(), "{verdict:?}");
        why.unwrap_or_default()
    };
    let recorder = "tier-0 recorder is armed";
    let unadmitted = "no AY solver was admitted";
    for _ in 0..2 {
        let why = answer(&recording);
        assert!(why.contains(recorder), "{why}");
        let why = answer(&no_ay);
        assert!(why.contains(unadmitted) && !why.contains(recorder), "{why}");
        let why = answer(&no_refine);
        assert!(why.contains("TCG_REFINE_SOLVER=0"), "{why}");
    }
}

#[test]
fn replay_queries_do_not_depend_on_the_registers() {
    let carrier_at = |a: u8, b: u8| TrapCarrier {
        opcode: O::TrapOverflowExact,
        kind: TrapKind::Overflow {
            lhs: Gpr {
                number: a,
                width: 64,
            },
            rhs: Gpr {
                number: b,
                width: 64,
            },
            op: OverflowOp::UnsignedAdd,
            width: 64,
        },
    };
    let query = |carrier: TrapCarrier| {
        let ob = trap_expansion_obligation(&carrier, &stated_words(&carrier).unwrap()).unwrap();
        replay_obligation(&ob)
    };
    let (first, second) = (query(carrier_at(0, 1)), query(carrier_at(9, 3)));
    assert_eq!(first, second);
    assert_eq!(
        first.inputs,
        vec![("v0".to_string(), 64), ("v1".to_string(), 64)]
    );
    // The renamed query is still the statement: it holds by evaluation.
    assert!(matches!(
        crate::lowering_proof::verify_by_evaluation(&first),
        crate::verify::VerificationResult::Valid
    ));
    // Equal registers are a different form.
    assert_ne!(query(carrier_at(7, 7)), first);
}
