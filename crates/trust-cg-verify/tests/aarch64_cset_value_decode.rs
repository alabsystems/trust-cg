// trust-cg-verify/tests/aarch64_cset_value_decode.rs - the decoded-word CSET family against the live encoder
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The `CSET` decoded-word value family, tied to the LIVE encoder and to its
//! own negative controls.
//!
//! `CSET Rd, <cc>` is the architectural alias for
//! `CSINC Rd, ZR, ZR, invert(<cc>)`. The family's machine side is obtained by
//! DECODING the word, so it is only evidence about the compiler if the word is
//! the compiler's: this target re-encodes all twenty-eight forms with
//! `trust_cg_codegen::aarch64::encode::encode_instruction` and fails on any
//! difference — the same discipline `CAPTURED_A64_VALUE_WORDS` is held to.
//!
//! It also runs the whole negative-control battery and PRINTS each verdict, so
//! the claim "a proof that cannot fail is not a proof" is measured rather than
//! asserted, and it mutation-proves the battery itself by handing the credit
//! hook a control that survives.
//!
//! What is NOT claimed here: that any emitted CSET implements the source
//! operation its lowering came from (that is the source-bound binding's job, and
//! the decoded-word row deliberately says nothing about it), nor agreement with
//! silicon.

use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_ir::{AArch64Opcode, MachInst, MachOperand, PReg};
use trust_cg_lower::isel::AArch64CC;
use trust_cg_verify::aarch64_value_decode_proofs::{
    A64_CSET_FORMS, A64CSetControl, A64CSetControlMutation, A64CSetForm, A64CSetIntentMutation,
    A64RefusalClass, A64ValueCheckError, a64_cset_bound_form, a64_cset_controls, a64_cset_credit,
    a64_cset_credit_with, a64_cset_form_obligation_for, all_a64_cset_value_decode_proofs,
    cset_word, decide_a64_cset_form,
};
use trust_cg_verify::lowering_proof::VerificationConfig;
use trust_cg_verify::nzcv::{NzcvFlags, eval_condition};
use trust_cg_verify::smt::{EvalEnv, EvalResult, SmtExpr};
use trust_cg_verify::verify::VerificationStrength;

/// The machine-IR instruction for one form, with `Rd` = 0 at the form's width.
/// `PReg` encodings: X0.. at base 0, W0.. at base 32.
fn inst_for(form: A64CSetForm) -> MachInst {
    let base = if form.width == 64 { 0 } else { 32 };
    MachInst::new(
        AArch64Opcode::CSet,
        vec![
            MachOperand::PReg(PReg::new(base)),
            MachOperand::Imm(form.cc as i64),
        ],
    )
}

/// Every form's word is the word the LIVE encoder emits for that form's
/// machine-IR instruction. Without this, `cset_word`'s layout could drift into
/// describing an instruction the compiler never produces.
#[test]
fn every_cset_form_word_is_the_live_encoder_word() {
    assert_eq!(A64_CSET_FORMS.len(), 28, "14 conditions x {{Wd, Xd}}");
    for form in A64_CSET_FORMS {
        let emitted = encode_instruction(&inst_for(form))
            .unwrap_or_else(|error| panic!("{form:?} does not encode: {error:?}"));
        assert_eq!(
            emitted,
            form.word(),
            "{:?}/{}: modeled word {:#010x} is not the encoder's {:#010x}",
            form.cc,
            form.width,
            form.word(),
            emitted
        );
    }
}

/// The alias's inversion is REAL in the encoder's output, not an assumption of
/// the model: every form's emitted word carries the complement of the
/// machine-IR condition, with `Rn` = `Rm` = 31 and `op:o2` = `0:1` (CSINC).
#[test]
fn the_live_encoder_really_inverts_the_condition_and_uses_both_zero_registers() {
    for form in A64_CSET_FORMS {
        let w = encode_instruction(&inst_for(form)).unwrap();
        assert_eq!((w >> 12) & 0xF, (form.cc as u32) ^ 1, "{form:?} cond field");
        assert_eq!((w >> 16) & 0x1F, 31, "{form:?} Rm is not ZR");
        assert_eq!((w >> 5) & 0x1F, 31, "{form:?} Rn is not ZR");
        assert_eq!((w >> 30) & 1, 0, "{form:?} op is not 0");
        assert_eq!((w >> 10) & 3, 0b01, "{form:?} op2 is not CSINC");
        assert_eq!((w >> 29) & 1, 0, "{form:?} S is set");
        assert_eq!(w >> 31, u32::from(form.width == 64), "{form:?} sf");
    }
}

/// All twenty-eight obligations mint, hold, and are decided EXHAUSTIVELY —
/// complete over the whole input domain, because the only free input is the
/// four-bit packed NZCV. None is degenerate.
#[test]
fn every_cset_form_holds_exhaustively_and_is_non_degenerate() {
    let config = VerificationConfig::default();
    for form in A64_CSET_FORMS {
        let obligation = a64_cset_form_obligation_for(form, form.word(), None)
            .unwrap_or_else(|error| panic!("{form:?}: {error}"));
        assert!(
            obligation.is_genuinely_proven(),
            "{form:?} is X==X — a restatement, not a lowering proof"
        );
        assert_eq!(
            obligation.inputs,
            vec![("nzcv".to_string(), 4)],
            "{form:?} must quantify over the packed NZCV and nothing else"
        );
        assert!(
            obligation.preconditions.is_empty(),
            "{form:?} must hold unconditionally"
        );
        let strength = decide_a64_cset_form(form, form.word(), None, &config)
            .unwrap_or_else(|error| panic!("{form:?} obligation does not hold: {error}"));
        assert_eq!(
            strength,
            VerificationStrength::Exhaustive,
            "{form:?} is not decided over its whole input domain"
        );
    }
    let lane = all_a64_cset_value_decode_proofs();
    assert_eq!(lane.len(), 28);
}

/// EVERY negative control must be refuted, for exactly its stated class, and
/// the verdicts are PRINTED per mutation class so the battery's coverage can be
/// read rather than assumed.
#[test]
fn every_negative_control_is_refuted_for_its_stated_class() {
    use std::collections::BTreeMap;
    let config = VerificationConfig::default();
    let controls = a64_cset_controls();
    assert_eq!(controls.len(), A64_CSET_FORMS.len() * 14);
    let mut per_label: BTreeMap<(&str, String), usize> = BTreeMap::new();
    for control in &controls {
        let outcome = match control.mutation {
            A64CSetControlMutation::Word(mutate) => {
                decide_a64_cset_form(control.form, mutate(control.form.word()), None, &config)
            }
            A64CSetControlMutation::Intent(mutation) => {
                decide_a64_cset_form(control.form, control.form.word(), Some(mutation), &config)
            }
        };
        match outcome {
            Err(A64ValueCheckError::Refuted(refutation))
                if refutation.class == control.expected =>
            {
                *per_label
                    .entry((control.label, format!("{:?}", control.expected)))
                    .or_default() += 1;
            }
            other => panic!(
                "CSET {:?}/{} control `{}` must be refuted for {:?}, got {other:?}",
                control.form.cc, control.form.width, control.label, control.expected
            ),
        }
    }
    for ((label, class), count) in &per_label {
        println!("CSET_CONTROL refuted={count:2} class={class} `{label}`");
    }
    assert_eq!(per_label.len(), 14, "one row per control, all refuted");
    assert_eq!(
        per_label.values().sum::<usize>(),
        controls.len(),
        "every control must be accounted for"
    );
}

/// The credit hook, and the proof that the hook is not vacuous: a control that
/// SURVIVES must make it refuse. Without this the battery could be silently
/// empty and every report above would still read green.
#[test]
fn the_credit_hook_refuses_a_surviving_control_and_an_empty_battery() {
    let credit = a64_cset_credit().unwrap_or_else(|error| panic!("{error}"));
    println!(
        "CSET_CREDIT forms={} exhaustive={} controls_refuted={}",
        credit.forms, credit.exhaustive_forms, credit.controls_refuted
    );
    assert_eq!(credit.forms, 28);
    assert_eq!(credit.exhaustive_forms, 28);
    assert_eq!(credit.controls_refuted, 28 * 14);

    let config = VerificationConfig::default();
    // A "control" that does not change anything survives, so the hook must
    // refuse rather than count it.
    let surviving = A64CSetControl {
        form: A64_CSET_FORMS[0],
        label: "the identity mutation: nothing is changed",
        mutation: A64CSetControlMutation::Word(|w| w),
        expected: A64RefusalClass::Value,
    };
    let mut battery = a64_cset_controls();
    battery.push(surviving);
    assert!(
        a64_cset_credit_with(&A64_CSET_FORMS, &battery, &config).is_err(),
        "a surviving control was counted as refuted"
    );
    // A form with no Value-class control at all earns nothing.
    let no_value: Vec<A64CSetControl> = a64_cset_controls()
        .into_iter()
        .filter(|control| control.expected != A64RefusalClass::Value)
        .collect();
    assert!(
        a64_cset_credit_with(&A64_CSET_FORMS, &no_value, &config).is_err(),
        "a form with no Value-class control was credited"
    );
}

/// The intent mutations are refuted by the form's OWN, unmodified word — which
/// is the sharpest statement that the two sides are not the same computation.
#[test]
fn the_form_word_refutes_every_wrong_statement_of_its_own_intent() {
    let config = VerificationConfig::default();
    for form in A64_CSET_FORMS {
        for mutation in [
            A64CSetIntentMutation::PolaritySwapped,
            A64CSetIntentMutation::AlwaysOne,
            A64CSetIntentMutation::AlwaysZero,
        ] {
            let outcome = decide_a64_cset_form(form, form.word(), Some(mutation), &config);
            assert!(
                matches!(
                    outcome,
                    Err(A64ValueCheckError::Refuted(ref refutation))
                        if refutation.class == A64RefusalClass::Value
                ),
                "{form:?} accepted the wrong intent {mutation:?}: {outcome:?}"
            );
        }
    }
}

/// The per-instruction BINDING: it fires for exactly the shapes the family
/// covers and fails closed on every other one, so an uncovered CSET keeps
/// blocking promotion instead of inheriting a theorem about a different word.
#[test]
fn the_binding_fires_only_for_covered_shapes() {
    for form in A64_CSET_FORMS {
        assert_eq!(
            a64_cset_bound_form(&inst_for(form)),
            Some(form),
            "{form:?} does not bind to itself"
        );
    }
    let x0 = MachOperand::PReg(PReg::new(0));
    let refused: Vec<MachInst> = vec![
        // AL and NV: the alias cannot carry them and the encoder refuses them.
        MachInst::new(AArch64Opcode::CSet, vec![x0.clone(), MachOperand::Imm(14)]),
        MachInst::new(AArch64Opcode::CSet, vec![x0.clone(), MachOperand::Imm(15)]),
        MachInst::new(AArch64Opcode::CSet, vec![x0.clone(), MachOperand::Imm(-1)]),
        // Wrong arity.
        MachInst::new(AArch64Opcode::CSet, vec![x0.clone()]),
        MachInst::new(
            AArch64Opcode::CSet,
            vec![x0.clone(), MachOperand::Imm(0), MachOperand::Imm(0)],
        ),
        // A condition that is not an immediate.
        MachInst::new(AArch64Opcode::CSet, vec![x0.clone(), x0.clone()]),
        // A zero-register or stack-pointer destination: no value claim.
        MachInst::new(
            AArch64Opcode::CSet,
            vec![
                MachOperand::Special(trust_cg_ir::SpecialReg::XZR),
                MachOperand::Imm(0),
            ],
        ),
        MachInst::new(
            AArch64Opcode::CSet,
            vec![
                MachOperand::Special(trust_cg_ir::SpecialReg::SP),
                MachOperand::Imm(0),
            ],
        ),
        // Other opcodes of the same encoding family stay unbound.
        MachInst::new(
            AArch64Opcode::Csinc,
            vec![x0.clone(), x0.clone(), x0.clone(), MachOperand::Imm(0)],
        ),
        MachInst::new(
            AArch64Opcode::Csinv,
            vec![x0.clone(), x0.clone(), x0.clone(), MachOperand::Imm(0)],
        ),
        MachInst::new(
            AArch64Opcode::Csneg,
            vec![x0.clone(), x0.clone(), x0.clone(), MachOperand::Imm(0)],
        ),
        MachInst::new(
            AArch64Opcode::Csel,
            vec![x0.clone(), x0.clone(), x0, MachOperand::Imm(0)],
        ),
    ];
    for inst in refused {
        assert_eq!(
            a64_cset_bound_form(&inst),
            None,
            "{inst:?} acquired a decoded-word CSET binding"
        );
    }
}

/// A word from a DIFFERENT form must not discharge this form's obligation. This
/// is the cross-form substitution control: it is what stops twenty-eight rows
/// from collapsing into one representative.
#[test]
fn no_form_accepts_another_forms_word() {
    let config = VerificationConfig::default();
    let mut refuted = 0;
    for form in A64_CSET_FORMS {
        for other in A64_CSET_FORMS {
            if other == form {
                continue;
            }
            let outcome = decide_a64_cset_form(form, other.word(), None, &config);
            assert!(
                matches!(outcome, Err(A64ValueCheckError::Refuted(_))),
                "{:?}/{} accepted {:?}/{}'s word: {outcome:?}",
                form.cc,
                form.width,
                other.cc,
                other.width
            );
            refuted += 1;
        }
    }
    assert_eq!(refuted, 28 * 27);
}

/// The (width, condition) pairs the AArch64 selector actually emits are all
/// covered. Measured on `library/core` at this revision, every emitted CSET is
/// `sf = 1` (ISel allocates `RegClass::Gpr64` at every emission site), with
/// twelve distinct conditions; the family covers all fourteen at both widths, so
/// the emitted set is a strict subset. This test pins the reverse direction: a
/// condition the emitter can produce must never fall outside the family.
#[test]
fn every_condition_the_emitter_can_carry_is_covered_at_both_widths() {
    for encoding in 0..=13i64 {
        for width in [32u32, 64] {
            let base = if width == 64 { 0 } else { 32 };
            let inst = MachInst::new(
                AArch64Opcode::CSet,
                vec![
                    MachOperand::PReg(PReg::new(base)),
                    MachOperand::Imm(encoding),
                ],
            );
            // The encoder accepts it, so the family must too.
            let word = encode_instruction(&inst)
                .unwrap_or_else(|error| panic!("cc={encoding} width={width}: {error:?}"));
            let form = a64_cset_bound_form(&inst)
                .unwrap_or_else(|| panic!("cc={encoding} width={width} is not covered"));
            assert_eq!(word, form.word());
            assert_eq!(word, cset_word(width, form.cc));
        }
    }
    // The two the alias cannot carry stay outside, in BOTH directions.
    for encoding in [14i64, 15] {
        let inst = MachInst::new(
            AArch64Opcode::CSet,
            vec![MachOperand::PReg(PReg::new(0)), MachOperand::Imm(encoding)],
        );
        assert!(encode_instruction(&inst).is_err(), "cc={encoding} encoded");
        assert_eq!(a64_cset_bound_form(&inst), None, "cc={encoding} bound");
    }
}

// ---------------------------------------------------------------------------
// A THIRD, INDEPENDENT SPELLING OF THE CONDITION
// ---------------------------------------------------------------------------
//
// `is_genuinely_proven()` is only `trust_ir_expr != aarch64_expr`, which is
// necessary and not sufficient: two different-looking transcriptions of the SAME
// Arm ARM table, by the same hand, agree for the wrong reason as readily as for
// the right one. The obligation's two sides are
//
//   * INTENT:  `nzcv::eval_condition` — a table keyed on the MNEMONIC;
//   * MACHINE: `aarch64_csel_semantics`'s `ConditionHolds` — a switch on the
//     raw `cond<3:1>` field with a `cond<0>` inversion,
//
// and the second is already checked against a hand-transcribed truth table in
// its own module. The first is not. So this section transcribes the condition
// predicates a THIRD time, directly from Arm DDI 0487 Table C1-1, in plain Rust
// booleans, and checks BOTH the intent side and the whole assembled machine side
// against it over the complete 14 x 16 domain. If all three agree everywhere,
// the obligation's discharge is not an artefact of one shared transcription.

/// `cond` holds for these NZCV bits, transcribed from the Arm ARM condition
/// table as plain boolean algebra. Deliberately NOT a bitmask and NOT a switch
/// on the encoding: one arm per mnemonic, spelled the way the manual reads.
fn oracle_condition(cc: AArch64CC, n: bool, z: bool, c: bool, v: bool) -> bool {
    match cc {
        AArch64CC::EQ => z,
        AArch64CC::NE => !z,
        AArch64CC::HS => c,
        AArch64CC::LO => !c,
        AArch64CC::MI => n,
        AArch64CC::PL => !n,
        AArch64CC::VS => v,
        AArch64CC::VC => !v,
        AArch64CC::HI => c && !z,
        AArch64CC::LS => !c || z,
        AArch64CC::GE => n == v,
        AArch64CC::LT => n != v,
        AArch64CC::GT => !z && n == v,
        AArch64CC::LE => z || n != v,
    }
}

/// The evaluation environment for one packed NZCV value.
fn nzcv_env(flags: u64) -> EvalEnv {
    let mut env = EvalEnv::default();
    env.insert("nzcv".into(), flags);
    env
}

/// The INTENT side's per-mnemonic table agrees with the third spelling at every
/// one of the 224 points.
#[test]
fn the_intent_sides_condition_table_matches_an_independent_transcription() {
    let mut checked = 0;
    for form in A64_CSET_FORMS {
        if form.width != 64 {
            continue; // the condition does not depend on the width
        }
        let flags = NzcvFlags {
            n: SmtExpr::var("nzcv", 4).extract(3, 3).eq_expr(one_bit()),
            z: SmtExpr::var("nzcv", 4).extract(2, 2).eq_expr(one_bit()),
            c: SmtExpr::var("nzcv", 4).extract(1, 1).eq_expr(one_bit()),
            v: SmtExpr::var("nzcv", 4).extract(0, 0).eq_expr(one_bit()),
        };
        let predicate = eval_condition(form.cc, &flags);
        for packed in 0..16u64 {
            let expected = oracle_condition(
                form.cc,
                packed & 8 != 0,
                packed & 4 != 0,
                packed & 2 != 0,
                packed & 1 != 0,
            );
            assert_eq!(
                predicate.eval(&nzcv_env(packed)),
                EvalResult::Bool(expected),
                "{:?} at NZCV={packed:04b}",
                form.cc
            );
            checked += 1;
        }
    }
    assert_eq!(checked, 14 * 16);
}

/// And the assembled MACHINE side — decode, generic conditional-select
/// semantics, `Xd[63:32]` clearing and all — writes exactly the third
/// spelling's 0/1 at every one of the 448 (form, NZCV) points.
///
/// This is the end-to-end concrete check: it does not consult the intent side at
/// all, so it cannot be satisfied by the two transcriptions agreeing with each
/// other.
#[test]
fn the_machine_side_writes_the_independent_transcriptions_bit_at_every_nzcv() {
    let mut checked = 0;
    for form in A64_CSET_FORMS {
        let obligation = a64_cset_form_obligation_for(form, form.word(), None).unwrap();
        for packed in 0..16u64 {
            let expected = u64::from(oracle_condition(
                form.cc,
                packed & 8 != 0,
                packed & 4 != 0,
                packed & 2 != 0,
                packed & 1 != 0,
            ));
            assert_eq!(
                obligation.aarch64_expr.eval(&nzcv_env(packed)),
                EvalResult::Bv(expected),
                "machine side of {:?}/{} at NZCV={packed:04b}",
                form.cc,
                form.width
            );
            checked += 1;
        }
    }
    assert_eq!(checked, 28 * 16);
}

fn one_bit() -> SmtExpr {
    SmtExpr::bv_const(1, 1)
}
