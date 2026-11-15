// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use crate::smt::{EvalEnv, EvalResult};
use trust_cg_ir::{MachInst, MachOperand, PReg, RegClass, SpecialReg, VReg};

/// Deterministic 64-bit LCG so every run samples the same states.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 ^ (self.0 >> 29)
    }
}

fn value_bits(result: EvalResult) -> u128 {
    match result {
        EvalResult::Bv(value) => u128::from(value),
        EvalResult::Bv128(value) => value,
        other => panic!("non-bitvector result {other:?}"),
    }
}

fn eval(expr: &SmtExpr, env: &EvalEnv) -> u128 {
    value_bits(expr.try_eval(env).expect("evaluates"))
}

/// Evaluate a routing under `env`.
fn eval_routing(bits: &[RouteBit], env: &EvalEnv) -> u128 {
    bits.iter().enumerate().fold(0u128, |acc, (i, bit)| {
        let set = match bit {
            RouteBit::Zero => false,
            RouteBit::One => true,
            RouteBit::Input(name, b) => (env.get(name).copied().expect("bound") >> b) & 1 == 1,
        };
        acc | (u128::from(set) << i)
    })
}

fn inst(opcode: AArch64Opcode, operands: Vec<MachOperand>) -> MachInst {
    MachInst::new(opcode, operands)
}

fn x(n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(n))
}

fn w(n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(32 + n))
}

fn s(n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(128 + n))
}

fn d(n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(96 + n))
}

fn vreg(id: u32, class: RegClass) -> MachOperand {
    MachOperand::VReg(VReg::new(id, class))
}

#[test]
fn decoder_reads_the_canonical_words_by_field() {
    assert_eq!(
        decode_a64_value_word(0x2A07_03E3),
        Ok(A64ValueWord::LogicalShiftedReg {
            sf: 0,
            opc: 0b01,
            shift: 0,
            n: 0,
            rm: 7,
            imm6: 0,
            rn: 31,
            rd: 3,
        })
    );
    assert_eq!(
        decode_a64_value_word(0x9100_03E3),
        Ok(A64ValueWord::AddSubImm {
            sf: 1,
            op: 0,
            s: 0,
            sh: 0,
            imm12: 0,
            rn: 31,
            rd: 3,
        })
    );
    assert_eq!(
        decode_a64_value_word(0x9B2C_7CE3),
        Ok(A64ValueWord::Dp3 {
            sf: 1,
            op54: 0,
            op31: 0b001,
            rm: 12,
            o0: 0,
            ra: 31,
            rn: 7,
            rd: 3,
        })
    );
    assert_eq!(
        decode_a64_value_word(0xD53B_D043),
        Ok(A64ValueWord::SysRegMove {
            l: 1,
            op0: 3,
            op1: 3,
            crn: 13,
            crm: 0,
            op2: 2,
            rt: 3,
        })
    );
    assert_eq!(
        decode_a64_value_word(0x9E66_00E3),
        Ok(A64ValueWord::FpIntMove {
            sf: 1,
            ftype: 0b01,
            rmode: 0,
            to_general: true,
            rn: 7,
            rd: 3,
        })
    );
    // FMOV Wd, Dn (sf=0, ftype=01) and FMOV Sd, Xn (sf=1, ftype=00) do not
    // exist: the cross-class width refusal is the decoder's, not a table's.
    for word in [0x1E66_00E3, 0x9E27_00E3] {
        assert!(matches!(
            decode_a64_value_word(word),
            Err(A64DecodeRefusal::Unallocated { .. })
        ));
    }
    // A neighbouring class never decodes as a modeled one: NOP, RET, B.
    for word in [0xD503_201F, 0xD65F_03C0, 0x1400_0000] {
        assert!(matches!(
            decode_a64_value_word(word),
            Err(A64DecodeRefusal::NotModeled { .. })
        ));
    }
    assert_eq!(TPIDR_EL0_KEY, 0xDE82);
}

#[test]
fn every_form_obligation_is_non_degenerate_and_holds_with_its_stated_strength() {
    let config = VerificationConfig::default();
    for &form in A64ValueForm::ALL {
        let obligation = a64_value_form_obligation(form).expect("form obligation");
        assert!(
            !obligation.is_degenerate(),
            "{form:?}: machine side must be structurally distinct from the intent"
        );
        assert!(
            obligation.name.to_lowercase().contains(form.query()),
            "{form:?}: the query must name the obligation"
        );
        let canonical = form.canonical().expect("canonical word");
        let decision = decide_a64_value_form(form, canonical.word, None, &config);
        let expected = match form {
            A64ValueForm::Smull
            | A64ValueForm::BfmInsertW
            | A64ValueForm::BfmInsertX
            | A64ValueForm::AddLsl12W
            | A64ValueForm::AddLsl12X
            | A64ValueForm::FcvtSFromH
            | A64ValueForm::FcvtDFromH
            | A64ValueForm::FcvtHFromS
            | A64ValueForm::FcvtHFromD => A64FormDecision::Evaluated,
            _ => A64FormDecision::Exact,
        };
        assert_eq!(decision, Ok(expected), "{form:?}");
        // Whatever the in-process decision, the evaluator agrees.
        assert!(
            matches!(
                verify_by_evaluation_with_config(&obligation, &config),
                VerificationResult::Valid
            ),
            "{form:?}"
        );
    }
    let registered = all_a64_value_decode_proofs();
    assert_eq!(registered.len(), A64ValueForm::ALL.len());
    for ((category, obligation), &form) in registered.iter().zip(A64ValueForm::ALL) {
        assert_eq!(*category, form.category());
        assert_eq!(obligation.name, form.obligation_name());
    }
}

#[test]
fn every_query_names_exactly_one_form() {
    for &form in A64ValueForm::ALL {
        let hits: Vec<_> = A64ValueForm::ALL
            .iter()
            .filter(|other| {
                other.category() == form.category()
                    && other
                        .obligation_name()
                        .to_lowercase()
                        .contains(form.query())
            })
            .collect();
        assert_eq!(hits, vec![&form], "{form:?} query is ambiguous");
    }
}

#[test]
fn every_captured_word_is_its_form_and_passes_the_per_instance_check() {
    for entry in CAPTURED_A64_VALUE_WORDS {
        let intent = a64_value_intent(&entry.inst()).expect("captured intent");
        assert_eq!(intent.form, Some(entry.form), "{entry:?}");
        assert!(
            check_emitted_a64_value_word(&entry.inst(), entry.word).is_ok(),
            "{entry:?}: {:?}",
            check_emitted_a64_value_word(&entry.inst(), entry.word)
        );
    }
    for &form in A64ValueForm::ALL {
        assert!(form.canonical().is_some(), "{form:?} has no captured word");
    }
}

#[test]
fn every_decoded_value_opcode_earns_credit_with_every_control_refuted() {
    let mut forms = 0;
    for opcode in [
        AArch64Opcode::MovR,
        AArch64Opcode::MOVWrr,
        AArch64Opcode::MOVXrr,
        AArch64Opcode::FmovFprFpr,
        AArch64Opcode::FmovFprGpr,
        AArch64Opcode::FmovGprFpr,
        AArch64Opcode::Smull,
        AArch64Opcode::Bfm,
        AArch64Opcode::Rbit,
        AArch64Opcode::AddRIShift12,
        AArch64Opcode::Mrs,
        AArch64Opcode::FcvtHS,
        AArch64Opcode::FcvtHD,
        AArch64Opcode::FcvtSH,
        AArch64Opcode::FcvtDH,
        AArch64Opcode::NeonOrrV,
    ] {
        assert!(
            A64_VALUE_OPCODES_BOUND_PER_INSTRUCTION.contains(&opcode),
            "{opcode:?} must bind per instruction"
        );
        let credit = a64_value_credit(opcode).unwrap_or_else(|error| panic!("{opcode:?}: {error}"));
        assert!(credit.controls_refuted >= credit.forms, "{credit:?}");
        forms += credit.forms;
    }
    assert_eq!(forms, A64ValueForm::ALL.len());
    assert!(a64_value_credit(AArch64Opcode::AddRR).is_err());
}

#[test]
fn credit_hook_refuses_surviving_misattributed_missing_and_stale_evidence() {
    let config = VerificationConfig::default();
    let battery = a64_value_controls();

    // A control that survives: the canonical word itself.
    let mut surviving = battery.clone();
    surviving.push(A64ValueControl {
        form: A64ValueForm::MovW,
        label: "identity mutation survives",
        mutation: A64ControlMutation::Word(|word| word),
        expected: A64RefusalClass::Value,
    });
    assert!(
        a64_value_credit_with(
            AArch64Opcode::MovR,
            CAPTURED_A64_VALUE_WORDS,
            &surviving,
            &config
        )
        .is_err()
    );

    // A control refuted for the wrong reason: sf=1 is a Value refutation.
    let mut misattributed = battery.clone();
    misattributed.push(A64ValueControl {
        form: A64ValueForm::MovW,
        label: "sf=1 claimed as a flags refutation",
        mutation: A64ControlMutation::Word(|word| set_field(word, 31, 31, 1)),
        expected: A64RefusalClass::Flags,
    });
    assert!(
        a64_value_credit_with(
            AArch64Opcode::MovR,
            CAPTURED_A64_VALUE_WORDS,
            &misattributed,
            &config
        )
        .is_err()
    );

    // A form without a Value-class control.
    let without_value: Vec<_> = battery
        .iter()
        .copied()
        .filter(|control| {
            control.form != A64ValueForm::RbitX || control.expected != A64RefusalClass::Value
        })
        .collect();
    assert!(
        a64_value_credit_with(
            AArch64Opcode::Rbit,
            CAPTURED_A64_VALUE_WORDS,
            &without_value,
            &config
        )
        .is_err()
    );

    // A stale captured word: a W copy recorded as the X-width ORR.
    let mut stale = CAPTURED_A64_VALUE_WORDS.to_vec();
    let index = stale
        .iter()
        .rposition(|entry| entry.form == A64ValueForm::MovW)
        .unwrap();
    stale[index].word |= 1 << 31;
    assert!(a64_value_credit_with(AArch64Opcode::MovR, &stale, &battery, &config).is_err());

    // A missing form.
    let missing: Vec<_> = CAPTURED_A64_VALUE_WORDS
        .iter()
        .copied()
        .filter(|entry| entry.form != A64ValueForm::MovXFromSp)
        .collect();
    assert!(a64_value_credit_with(AArch64Opcode::MovR, &missing, &battery, &config).is_err());
}

#[test]
fn exact_routing_agrees_with_the_evaluator() {
    // Grouped to spell the seed mnemonic, not by byte width.
    #[allow(clippy::unusual_byte_groupings)]
    let mut rng = Lcg(0x5eed_a64);
    let mut checked = 0;
    for &form in A64ValueForm::ALL {
        let obligation = a64_value_form_obligation(form).unwrap();
        for side in [&obligation.trust_ir_expr, &obligation.aarch64_expr] {
            let Some(bits) = exact_routing(side) else {
                continue;
            };
            for _ in 0..256 {
                let mut env = EvalEnv::default();
                for (name, width) in &obligation.inputs {
                    env.insert(name.clone(), crate::smt::mask(rng.next(), *width));
                }
                assert_eq!(eval_routing(&bits, &env), eval(side, &env), "{form:?}");
                checked += 1;
            }
        }
    }
    assert!(checked > 0);
    // Non-routings are reported as such, never guessed.
    let x = SmtExpr::var("x", 8);
    let y = SmtExpr::var("y", 8);
    assert_eq!(exact_routing(&x.clone().bvor(y.clone())), None);
    assert_eq!(exact_routing(&x.clone().bvxor(bv(1, 8))), None);
    assert_eq!(exact_routing(&x.clone().bvadd(y)), None);
    assert_eq!(exact_routing(&x.clone().bvadd(bv(0, 8))), exact_routing(&x));
    assert_eq!(
        exact_routing(&x.clone().bvshl(bv(8, 8))),
        Some(vec![RouteBit::Zero; 8])
    );
}

#[test]
fn symbolic_bit_masks_match_the_concrete_decode_for_every_field_pair() {
    for datasize in [32u32, 64] {
        let symbolic = decode_bit_masks(
            &Field::Symbolic(SmtExpr::var("immr", 6)),
            &Field::Symbolic(SmtExpr::var("imms", 6)),
            datasize,
        );
        for immr in 0..datasize {
            for imms in 0..datasize {
                let concrete =
                    decode_bit_masks(&Field::Concrete(immr), &Field::Concrete(imms), datasize);
                let mut env = EvalEnv::default();
                env.insert("immr".to_string(), u64::from(immr));
                env.insert("imms".to_string(), u64::from(imms));
                for (sym, conc) in [
                    (&symbolic.0, &concrete.0),
                    (&symbolic.1, &concrete.1),
                    (&symbolic.2, &concrete.2),
                    (&symbolic.3, &concrete.3),
                ] {
                    assert_eq!(
                        eval(sym, &env),
                        eval(conc, &env),
                        "w{datasize} immr={immr} imms={imms}"
                    );
                }
            }
        }
    }
}

#[test]
fn bitfield_insert_semantics_match_a_plain_model_for_every_legal_field() {
    // Every (lsb, width) the lowering can emit, decided exactly per instance.
    for datasize in [32u32, 64] {
        let reg = |n: u16| if datasize == 32 { w(n) } else { x(n) };
        let sf = u32::from(datasize == 64);
        for lsb in 0..datasize {
            for width in 1..=datasize - lsb {
                let immr = (datasize - lsb) % datasize;
                let imms = width - 1;
                let word = (sf << 31)
                    | (0b01 << 29)
                    | (0b100110 << 23)
                    | (sf << 22)
                    | (immr << 16)
                    | (imms << 10)
                    | (7 << 5)
                    | 3;
                let bfm = inst(
                    AArch64Opcode::Bfm,
                    vec![
                        reg(3),
                        reg(7),
                        MachOperand::Imm(i64::from(immr)),
                        MachOperand::Imm(i64::from(imms)),
                    ],
                );
                assert_eq!(
                    check_emitted_a64_value_word(&bfm, word),
                    Ok(A64ValueVerdict::Exact),
                    "w{datasize} lsb={lsb} width={width}"
                );
                // The same word under the UBFM opcode bits must refute unless
                // the field covers the whole register, where no destination
                // bit survives and BFM and UBFM write the same value.
                if width == datasize {
                    assert_eq!(
                        check_emitted_a64_value_word(&bfm, set_field(word, 30, 29, 0b10)),
                        Ok(A64ValueVerdict::Exact)
                    );
                    continue;
                }
                assert!(matches!(
                    check_emitted_a64_value_word(&bfm, set_field(word, 30, 29, 0b10)),
                    Err(A64ValueCheckError::Refuted(A64ValueRefutation {
                        class: A64RefusalClass::Value,
                        ..
                    }))
                ));
            }
        }
    }
}

#[test]
fn cross_class_fmov_width_mismatch_is_ill_formed() {
    for shape in [
        inst(AArch64Opcode::FmovFprGpr, vec![w(3), d(7)]),
        inst(AArch64Opcode::FmovFprGpr, vec![x(3), s(7)]),
        inst(AArch64Opcode::FmovGprFpr, vec![d(3), w(7)]),
        inst(AArch64Opcode::FmovGprFpr, vec![s(3), x(7)]),
        // Bank-direction mismatches: operands in the other opcode's banks.
        inst(AArch64Opcode::FmovFprGpr, vec![s(3), w(7)]),
        inst(AArch64Opcode::FmovGprFpr, vec![w(3), s(7)]),
    ] {
        assert!(
            matches!(
                a64_value_intent(&shape),
                Err(A64ValueCheckError::IllFormed(_))
            ),
            "{shape:?}"
        );
    }
}

#[test]
fn register_31_aliasing_is_refuted_per_instance() {
    // PReg(31) is SP; ORR reads register 31 as XZR, so an ORR spelling of a
    // copy FROM SP writes zero.
    let from_sp = inst(
        AArch64Opcode::MovR,
        vec![x(3), MachOperand::PReg(PReg::new(31))],
    );
    assert!(matches!(
        check_emitted_a64_value_word(&from_sp, 0xAA1F_03E3),
        Err(A64ValueCheckError::Refuted(A64ValueRefutation {
            class: A64RefusalClass::Value,
            ..
        }))
    ));
    assert_eq!(
        check_emitted_a64_value_word(&from_sp, 0x9100_03E3),
        Ok(A64ValueVerdict::Exact)
    );
    // An ORR spelling of a copy TO SP writes XZR, discarding the value.
    let to_sp = inst(
        AArch64Opcode::MovR,
        vec![MachOperand::Special(SpecialReg::SP), x(7)],
    );
    assert!(matches!(
        check_emitted_a64_value_word(&to_sp, 0xAA07_03FF),
        Err(A64ValueCheckError::Refuted(A64ValueRefutation {
            class: A64RefusalClass::Destination,
            ..
        }))
    ));
    // ADD (immediate) cannot name a zero register at all.
    let add_zr = inst(
        AArch64Opcode::AddRIShift12,
        vec![
            x(3),
            MachOperand::Special(SpecialReg::XZR),
            MachOperand::Imm(1),
        ],
    );
    assert!(matches!(
        a64_value_intent(&add_zr),
        Err(A64ValueCheckError::IllFormed(_))
    ));
}

/// SMULL and the shifted ADD are decided per instance as INSTANCES of their
/// form: only the register and immediate FIELDS are compared, and the value
/// register 31 denotes is never evaluated on that path. Register 31 is the
/// zero register in SMADDL and SP in ADD (immediate), so an operand naming the
/// OTHER register 31 must be refused by the intent itself, in every register
/// slot; otherwise the field comparison (31 == 31) accepts a word that reads
/// or writes a different register than the instruction names. Dropping the
/// SMULL SP refusal left every other test green; this pins it, and the ADD
/// zero-register refusal, slot by slot and for every spelling.
#[test]
fn instance_forms_refuse_the_other_register_31_in_every_slot() {
    let sp_spellings = [
        MachOperand::PReg(PReg::new(31)),
        MachOperand::PReg(PReg::new(63)),
        MachOperand::Special(SpecialReg::SP),
    ];
    let zr64_spellings = [
        MachOperand::PReg(PReg::new(160)),
        MachOperand::Special(SpecialReg::XZR),
    ];
    let zr32_spellings = [
        MachOperand::PReg(PReg::new(161)),
        MachOperand::Special(SpecialReg::WZR),
    ];
    let refused = |shape: &MachInst, word: u32| {
        let verdict = check_emitted_a64_value_word(shape, word);
        assert!(
            matches!(
                verdict,
                Err(A64ValueCheckError::IllFormed(_) | A64ValueCheckError::Refuted(_))
            ),
            "{shape:?} = {word:#010x} must fail closed, got {verdict:?}"
        );
    };

    // SMULL Xd, Wn, Wm (SMADDL ..., XZR): fields Rd = 4:0, Rn = 9:5, Rm = 20:16.
    let smull_canonical = A64ValueForm::Smull.canonical().unwrap().word;
    let smull_fields = [(4, 0), (9, 5), (20, 16)];
    for slot in 0..3 {
        let (hi, lo) = smull_fields[slot];
        let word = set_field(smull_canonical, hi, lo, 31);
        for sp in &sp_spellings {
            let mut operands = vec![x(3), w(7), w(12)];
            operands[slot] = sp.clone();
            refused(&inst(AArch64Opcode::Smull, operands), word);
        }
        // Control: the zero register IS register 31 here, so it is accepted.
        let zeros: &[MachOperand] = if slot == 0 {
            &zr64_spellings
        } else {
            &[
                zr64_spellings[0].clone(),
                zr64_spellings[1].clone(),
                zr32_spellings[0].clone(),
                zr32_spellings[1].clone(),
            ]
        };
        for zr in zeros {
            let mut operands = vec![x(3), w(7), w(12)];
            operands[slot] = zr.clone();
            let shape = inst(AArch64Opcode::Smull, operands);
            assert_eq!(
                check_emitted_a64_value_word(&shape, word),
                Ok(A64ValueVerdict::InstanceOf(A64ValueForm::Smull)),
                "{shape:?} = {word:#010x}"
            );
        }
    }

    // ADD Xd|SP, Xn|SP, #imm12, LSL #12: fields Rd = 4:0, Rn = 9:5.
    let add_canonical = A64ValueForm::AddLsl12X.canonical().unwrap().word;
    for (slot, (hi, lo)) in [(4, 0), (9, 5)].into_iter().enumerate() {
        let word = set_field(add_canonical, hi, lo, 31);
        for zr in zr64_spellings.iter().chain(&zr32_spellings) {
            let mut operands = vec![x(3), x(7), MachOperand::Imm(0x123)];
            operands[slot] = zr.clone();
            refused(&inst(AArch64Opcode::AddRIShift12, operands), word);
        }
        // Control: SP IS register 31 here, so a 64-bit SP operand is accepted.
        for sp in [
            MachOperand::PReg(PReg::new(31)),
            MachOperand::Special(SpecialReg::SP),
        ] {
            let mut operands = vec![x(3), x(7), MachOperand::Imm(0x123)];
            operands[slot] = sp;
            let shape = inst(AArch64Opcode::AddRIShift12, operands);
            assert_eq!(
                check_emitted_a64_value_word(&shape, word),
                Ok(A64ValueVerdict::InstanceOf(A64ValueForm::AddLsl12X)),
                "{shape:?} = {word:#010x}"
            );
        }
    }
}

#[test]
fn per_instance_decisions_cover_shapes_outside_the_gate_forms() {
    // A discarded copy to XZR and an H-register FMOV belong to no gate form
    // but are still decided exactly; MOV Xd, XZR binds its own zero form.
    let mov_zero = inst(
        AArch64Opcode::MovR,
        vec![x(5), MachOperand::Special(SpecialReg::XZR)],
    );
    assert_eq!(
        a64_value_intent(&mov_zero).unwrap().form,
        Some(A64ValueForm::MovXFromZr)
    );
    assert_eq!(
        check_emitted_a64_value_word(&mov_zero, 0xAA1F_03E5),
        Ok(A64ValueVerdict::Exact)
    );
    let discard = inst(
        AArch64Opcode::MovR,
        vec![MachOperand::Special(SpecialReg::XZR), x(5)],
    );
    assert_eq!(a64_value_intent(&discard).unwrap().form, None);
    assert_eq!(
        check_emitted_a64_value_word(&discard, 0xAA05_03FF),
        Ok(A64ValueVerdict::Exact)
    );
    let h = |n: u16| MachOperand::PReg(PReg::new(165 + n));
    let fmov_h = inst(AArch64Opcode::FmovFprFpr, vec![h(3), h(7)]);
    assert_eq!(
        check_emitted_a64_value_word(&fmov_h, 0x1EE0_40E3),
        Ok(A64ValueVerdict::Exact)
    );
    // An X-width copy from a W-class source copies the whole root register.
    let widening = inst(AArch64Opcode::MovR, vec![x(3), w(7)]);
    assert_eq!(
        check_emitted_a64_value_word(&widening, 0xAA07_03E3),
        Ok(A64ValueVerdict::Exact)
    );
    // Shapes outside the model make no claim either way.
    let bfxil = inst(
        AArch64Opcode::Bfm,
        vec![x(3), x(7), MachOperand::Imm(4), MachOperand::Imm(10)],
    );
    assert!(matches!(
        check_emitted_a64_value_word(&bfxil, 0xB344_28E3),
        Err(A64ValueCheckError::OutOfModel(_))
    ));
}

#[test]
fn function_verifier_binding_selects_one_form_or_refuses() {
    use AArch64Opcode as O;
    let gpr64 = |id| vreg(id, RegClass::Gpr64);
    let gpr32 = |id| vreg(id, RegClass::Gpr32);
    let imm = MachOperand::Imm;
    let cases = [
        (
            inst(O::Smull, vec![gpr64(0), gpr32(1), gpr32(2)]),
            Some(Some(A64ValueForm::Smull)),
        ),
        (
            inst(O::Smull, vec![gpr32(0), gpr32(1), gpr32(2)]),
            Some(None),
        ),
        (
            inst(O::Bfm, vec![gpr32(0), gpr32(1), imm(24), imm(4)]),
            Some(Some(A64ValueForm::BfmInsertW)),
        ),
        (
            inst(O::Bfm, vec![gpr64(0), gpr64(1), imm(0), imm(63)]),
            Some(Some(A64ValueForm::BfmInsertX)),
        ),
        (
            inst(O::Bfm, vec![gpr64(0), gpr64(1), imm(4), imm(10)]),
            Some(None),
        ),
        (
            inst(O::Bfm, vec![gpr32(0), gpr32(1), imm(32), imm(4)]),
            Some(None),
        ),
        (
            inst(O::Bfm, vec![gpr32(0), gpr64(1), imm(24), imm(4)]),
            Some(None),
        ),
        (
            inst(O::Rbit, vec![gpr64(0), gpr64(1)]),
            Some(Some(A64ValueForm::RbitX)),
        ),
        (inst(O::Rbit, vec![gpr64(0), gpr32(1)]), Some(None)),
        (
            inst(O::AddRIShift12, vec![gpr64(0), gpr64(0), imm(0xFFF)]),
            Some(Some(A64ValueForm::AddLsl12X)),
        ),
        (
            inst(
                O::AddRIShift12,
                vec![gpr64(0), MachOperand::Special(SpecialReg::SP), imm(1)],
            ),
            Some(Some(A64ValueForm::AddLsl12X)),
        ),
        (
            inst(O::AddRIShift12, vec![gpr64(0), gpr64(1), imm(0x1000)]),
            Some(None),
        ),
        (
            inst(O::Mrs, vec![gpr64(0), imm(i64::from(TPIDR_EL0_KEY))]),
            Some(Some(A64ValueForm::MrsTpidrEl0)),
        ),
        (
            inst(
                O::Mrs,
                vec![gpr64(0), imm(i64::from(sysreg_key(3, 3, 13, 0, 3)))],
            ),
            Some(None),
        ),
        (
            inst(O::Mrs, vec![gpr32(0), imm(i64::from(TPIDR_EL0_KEY))]),
            Some(None),
        ),
        (inst(O::Smull, vec![]), Some(None)),
        // The register copies bind per instruction (L04-P11).
        (
            inst(O::MovR, vec![gpr64(0), gpr64(1)]),
            Some(Some(A64ValueForm::MovX)),
        ),
        (
            inst(O::MovR, vec![gpr32(0), gpr32(1)]),
            Some(Some(A64ValueForm::MovW)),
        ),
        (
            inst(
                O::MovR,
                vec![gpr64(0), MachOperand::Special(SpecialReg::SP)],
            ),
            Some(Some(A64ValueForm::MovXFromSp)),
        ),
        (
            inst(
                O::MovR,
                vec![MachOperand::Special(SpecialReg::SP), gpr64(0)],
            ),
            Some(None),
        ),
        (
            inst(
                O::MovR,
                vec![gpr64(0), MachOperand::Special(SpecialReg::XZR)],
            ),
            Some(Some(A64ValueForm::MovXFromZr)),
        ),
        (
            inst(O::MOVWrr, vec![gpr32(0), gpr32(1)]),
            Some(Some(A64ValueForm::MovWrr)),
        ),
        (
            inst(O::MOVWrr, vec![gpr64(0), gpr64(1)]),
            Some(Some(A64ValueForm::MovWrr)),
        ),
        (
            inst(O::MOVXrr, vec![gpr32(0), gpr32(1)]),
            Some(Some(A64ValueForm::MovXrr)),
        ),
        (
            inst(
                O::MOVXrr,
                vec![MachOperand::Special(SpecialReg::SP), gpr64(1)],
            ),
            Some(None),
        ),
        (inst(O::MOVXrr, vec![gpr64(0)]), Some(None)),
        (
            inst(O::FmovFprGpr, vec![gpr64(0), vreg(1, RegClass::Fpr64)]),
            Some(Some(A64ValueForm::FmovXFromD)),
        ),
        (
            inst(O::FmovFprGpr, vec![gpr64(0), vreg(1, RegClass::Fpr32)]),
            Some(None),
        ),
        // Zero-register sources bind their zero forms; a zero-register
        // destination and FMOVs naming the zero register bind none.
        (
            inst(
                O::MovR,
                vec![gpr32(0), MachOperand::Special(SpecialReg::WZR)],
            ),
            Some(Some(A64ValueForm::MovWFromZr)),
        ),
        (
            inst(O::MOVXrr, vec![gpr64(0), MachOperand::PReg(PReg::new(160))]),
            Some(Some(A64ValueForm::MovXrrFromZr)),
        ),
        (
            inst(O::MOVWrr, vec![gpr64(0), MachOperand::PReg(PReg::new(160))]),
            Some(Some(A64ValueForm::MovWrrFromZr)),
        ),
        (
            inst(
                O::MovR,
                vec![MachOperand::Special(SpecialReg::XZR), gpr64(1)],
            ),
            Some(None),
        ),
        (
            inst(
                O::FmovGprFpr,
                vec![
                    vreg(0, RegClass::Fpr64),
                    MachOperand::Special(SpecialReg::XZR),
                ],
            ),
            Some(None),
        ),
        // W<->H FMOVs (FEAT_FP16) bind; X<->H do not.
        (
            inst(O::FmovFprGpr, vec![gpr32(0), vreg(1, RegClass::Fpr16)]),
            Some(Some(A64ValueForm::FmovWFromH)),
        ),
        (
            inst(O::FmovGprFpr, vec![vreg(0, RegClass::Fpr16), gpr32(1)]),
            Some(Some(A64ValueForm::FmovHFromW)),
        ),
        (
            inst(O::FmovFprGpr, vec![gpr64(0), vreg(1, RegClass::Fpr16)]),
            Some(None),
        ),
        (
            inst(
                O::FmovFprFpr,
                vec![vreg(0, RegClass::Fpr16), vreg(1, RegClass::Fpr16)],
            ),
            Some(None),
        ),
        (inst(O::AddRR, vec![gpr64(0), gpr64(1), gpr64(2)]), None),
    ];
    for (shape, expected) in cases {
        assert_eq!(a64_value_bound_form(&shape), expected, "{shape:?}");
    }
}

// ---------------------------------------------------------------------------
// Half-precision FCVT (X-OPCODES-P7)
// ---------------------------------------------------------------------------

const FCVT_FORMS: [A64ValueForm; 4] = [
    A64ValueForm::FcvtSFromH,
    A64ValueForm::FcvtDFromH,
    A64ValueForm::FcvtHFromS,
    A64ValueForm::FcvtHFromD,
];

/// Each FCVT obligation's only input is the source scalar, so the widening
/// forms are exhaustive and the narrowing forms sampled; both sides write the
/// whole 128-bit destination.
#[test]
fn fcvt_obligations_quantify_over_the_source_scalar_alone() {
    use crate::verify::VerificationStrength;
    let config = VerificationConfig::default();
    for form in FCVT_FORMS {
        let conv = form.half_conversion().unwrap();
        let obligation = a64_value_form_obligation(form).unwrap();
        assert_eq!(
            obligation.inputs.len(),
            1,
            "{form:?}: {:?}",
            obligation.inputs
        );
        assert_eq!(obligation.inputs[0].1, conv.source().bits());
        assert_eq!(obligation.trust_ir_expr.bv_width(), 128);
        assert_eq!(obligation.aarch64_expr.bv_width(), 128);
        let strength = VerificationStrength::for_obligation_with_config(&obligation, &config);
        if conv.widens() {
            assert!(
                matches!(strength, VerificationStrength::Exhaustive),
                "{form:?}: {strength}"
            );
        } else {
            assert!(
                matches!(strength, VerificationStrength::Statistical { .. }),
                "{form:?}: {strength}"
            );
        }
    }
}

/// Every FCVT form has a control of each kind the gap names: wrong
/// direction, wrong format and (for the rounded forms) wrong rounding; each
/// is refuted for its stated reason by the credit hook's battery.
#[test]
fn fcvt_controls_cover_direction_format_and_rounding() {
    let controls = a64_value_controls();
    for form in FCVT_FORMS {
        let labels: Vec<&str> = controls
            .iter()
            .filter(|control| control.form == form)
            .map(|control| control.label)
            .collect();
        let has = |needle: &str| labels.iter().any(|label| label.contains(needle));
        assert!(has("wrong direction"), "{form:?}: {labels:?}");
        assert!(has("format"), "{form:?}: {labels:?}");
        assert!(has("default NaN"), "{form:?}: {labels:?}");
        if !form.half_conversion().unwrap().widens() {
            assert!(has("round toward zero"), "{form:?}: {labels:?}");
            assert!(has("ties away"), "{form:?}: {labels:?}");
        }
    }
}

/// Ties-away differs from ties-to-even only on exact ties, which random
/// sampling of a binary32/binary64 source does not reach: the battery does.
#[test]
fn fcvt_ties_away_is_refuted_by_the_battery_not_by_luck() {
    let config = VerificationConfig::default();
    for form in [A64ValueForm::FcvtHFromS, A64ValueForm::FcvtHFromD] {
        let canonical = form.canonical().unwrap();
        let outcome = decide_a64_value_form(
            form,
            canonical.word,
            Some(A64IntentMutation::FcvtRoundTiesAway),
            &config,
        );
        match outcome {
            Err(A64ValueCheckError::Refuted(refutation)) => {
                assert_eq!(refutation.class, A64RefusalClass::Value);
                assert!(refutation.detail.starts_with("source "), "{refutation}");
            }
            other => panic!("{form:?}: {other:?}"),
        }
    }
}

/// The FCVT rows of FP data-processing (1 source): same-precision and
/// `opc == 10` rows are unallocated, `ftype = 01, opc = 10` is BFCVT (not
/// modeled), and single<->double FCVT is decoded but outside the model.
#[test]
fn fcvt_decode_refuses_unallocated_and_foreign_rows() {
    let fcvt = |ftype: u32, opc: u32| 0x1E22_4000 | (ftype << 22) | (opc << 15) | (7 << 5) | 3;
    assert_eq!(fcvt(0b11, 0b00), 0x1EE2_40E3);
    for ftype in [0b00, 0b01, 0b11] {
        assert!(matches!(
            decode_a64_value_word(fcvt(ftype, ftype)),
            Err(A64DecodeRefusal::Unallocated { .. })
        ));
    }
    for ftype in [0b00, 0b11] {
        assert!(matches!(
            decode_a64_value_word(fcvt(ftype, 0b10)),
            Err(A64DecodeRefusal::Unallocated { .. })
        ));
    }
    assert!(matches!(
        decode_a64_value_word(fcvt(0b01, 0b10)),
        Err(A64DecodeRefusal::NotModeled { .. })
    ));
    for (ftype, opc) in [(0b00, 0b01), (0b01, 0b00)] {
        let decoded = decode_a64_value_word(fcvt(ftype, opc)).unwrap();
        assert!(matches!(
            denote_a64_value_word(&decoded, &FieldOverrides::default()),
            Err(A64DenoteRefusal::UnmodeledInstruction(_))
        ));
    }
}

/// The per-instance check names the conversion by register widths: a
/// wrong-width operand pairing is ill-formed, and a word for another
/// conversion is refuted.
#[test]
fn fcvt_instances_bind_width_and_direction() {
    let h = |n: u16| MachOperand::PReg(PReg::new(165 + n));
    let s = |n: u16| MachOperand::PReg(PReg::new(128 + n));
    let d = |n: u16| MachOperand::PReg(PReg::new(96 + n));
    let inst = MachInst::new(AArch64Opcode::FcvtHS, vec![s(3), h(7)]);
    assert!(check_emitted_a64_value_word(&inst, 0x1EE2_40E3).is_ok());
    // FCVT D3, H7 for an S destination.
    assert!(matches!(
        check_emitted_a64_value_word(&inst, 0x1EE2_C0E3),
        Err(A64ValueCheckError::Refuted(_))
    ));
    // FCVT H3, S7: the opposite direction.
    assert!(matches!(
        check_emitted_a64_value_word(&inst, 0x1E23_C0E3),
        Err(A64ValueCheckError::Refuted(_))
    ));
    // Operand widths that name no FcvtHS instance.
    for operands in [vec![d(3), h(7)], vec![s(3), s(7)], vec![h(3), s(7)]] {
        assert!(matches!(
            a64_value_intent(&MachInst::new(AArch64Opcode::FcvtHS, operands)),
            Err(A64ValueCheckError::IllFormed(_))
        ));
    }
}

/// ORR (vector): the Vn == Vm register copy is a decoded-value form checked on
/// its word; the three-register 16B OR is field-checked (Q/U/size and the
/// three register numbers); no other shape is either.
#[test]
fn orr_vector_binds_the_16b_copy_and_the_16b_or_by_exact_shape() {
    let q = |n: u16| MachOperand::PReg(PReg::new(64 + n));
    let orr = AArch64Opcode::NeonOrrV;
    assert_eq!(
        decode_a64_value_word(0x4EA7_1CE3),
        Ok(A64ValueWord::SimdLogical {
            q: 1,
            u: 0,
            size: 0b10,
            rm: 7,
            rn: 7,
            rd: 3,
        })
    );

    let copy = inst(orr, vec![q(3), q(7), q(7)]);
    assert_eq!(
        a64_value_intent(&copy).expect("copy intent").form,
        Some(A64ValueForm::MovV16B)
    );
    assert!(check_emitted_a64_value_word(&copy, 0x4EA7_1CE3).is_ok());
    // ORR V3.16B, V7.16B, V8.16B; ORR V3.8B (upper half zeroed); EOR (zero);
    // BSL (reads the destination): none of them is the copy.
    for word in [0x4EA8_1CE3, 0x0EA7_1CE3, 0x6E27_1CE3, 0x6E67_1CE3] {
        assert!(
            matches!(
                check_emitted_a64_value_word(&copy, word),
                Err(A64ValueCheckError::Refuted(_))
            ),
            "{word:#010x}: {:?}",
            check_emitted_a64_value_word(&copy, word)
        );
    }
    assert_eq!(check_neon_bitwise_16b_word(&copy, 0x4EA7_1CE3), None);

    // A D copy with no selector is the 8B ORR: its low half copies, its
    // upper half is zeroed. The word is still checked; no form credits it.
    let low_copy = inst(orr, vec![d(3), d(7), d(7)]);
    assert_eq!(
        a64_value_intent(&low_copy).expect("8B copy intent").form,
        None
    );
    assert!(check_emitted_a64_value_word(&low_copy, 0x0EA7_1CE3).is_ok());
    assert!(matches!(
        check_emitted_a64_value_word(&low_copy, 0x4EA7_1CE3),
        Err(A64ValueCheckError::Refuted(_))
    ));

    let vector_or = inst(orr, vec![q(0), q(1), q(2)]);
    assert_eq!(
        neon_bitwise_16b_bound_query(&vector_or),
        Some("orrv.16b lanewise-intent")
    );
    assert!(matches!(
        a64_value_intent(&vector_or),
        Err(A64ValueCheckError::OutOfModel(_))
    ));
    assert_eq!(
        check_neon_bitwise_16b_word(&vector_or, 0x4EA2_1C20),
        Some(Ok(()))
    );
    // Swapped Vn/Vm, AND, the 8B arrangement, a different Vd.
    for word in [0x4EA1_1C40, 0x4E22_1C20, 0x0EA2_1C20, 0x4EA2_1C24] {
        assert!(
            matches!(check_neon_bitwise_16b_word(&vector_or, word), Some(Err(_))),
            "{word:#010x}"
        );
    }
    let vq = |id: u32| vreg(id, RegClass::Fpr128);
    assert!(neon_bitwise_16b_bound_query(&inst(orr, vec![vq(0), vq(1), vq(2)])).is_some());
    for operands in [
        vec![vq(0), vq(1), vq(1)],
        vec![d(0), d(1), d(2)],
        vec![q(0), q(1), q(2), MachOperand::Imm(1)],
        vec![q(0), q(1)],
        vec![x(0), x(1), x(2)],
    ] {
        let shape = inst(orr, operands);
        assert_eq!(neon_bitwise_16b_bound_query(&shape), None, "{shape:?}");
        assert_eq!(
            check_neon_bitwise_16b_word(&shape, 0x4EA2_1C20),
            None,
            "{shape:?}"
        );
    }
}

/// NEON AND, EOR, BIC and NOT bind their lanewise obligation only in the 16B
/// shape (Q registers, no selector), whose word is field-checked; the 8B
/// shapes (V64 operands, Q = 0) bind nothing and are refused by shape.
#[test]
fn neon_bitwise_binds_only_the_16b_shape() {
    use AArch64Opcode as O;
    let q = |n: u16| MachOperand::PReg(PReg::new(64 + n));
    let vq = |id: u32| vreg(id, RegClass::Fpr128);
    let vd = |id: u32| vreg(id, RegClass::Fpr64);
    // (opcode, query, the 16B word for V0, V1, V2; its 8B word, another
    // operation, and Vn/Vm swapped)
    for (opcode, query, word, wrong) in [
        (
            O::NeonAndV,
            "andv.16b lanewise-intent",
            0x4E22_1C20,
            [0x0E22_1C20, 0x4E62_1C20, 0x4E21_1C40],
        ),
        (
            O::NeonBicV,
            "bicv.16b lanewise-intent",
            0x4E62_1C20,
            [0x0E62_1C20, 0x4E22_1C20, 0x4E61_1C40],
        ),
        (
            O::NeonEorV,
            "eorv.16b lanewise-intent",
            0x6E22_1C20,
            [0x2E22_1C20, 0x4EA2_1C20, 0x6E21_1C40],
        ),
    ] {
        let bound = inst(opcode, vec![q(0), q(1), q(2)]);
        assert_eq!(neon_bitwise_16b_query(opcode), Some(query));
        assert_eq!(neon_bitwise_16b_bound_query(&bound), Some(query));
        assert_eq!(neon_bitwise_unbound_reason(&bound), None);
        assert_eq!(check_neon_bitwise_16b_word(&bound, word), Some(Ok(())));
        for w in wrong {
            assert!(
                matches!(check_neon_bitwise_16b_word(&bound, w), Some(Err(_))),
                "{opcode:?} {w:#010x}"
            );
        }
        for operands in [vec![q(0), q(1), q(1)], vec![vq(0), vq(1), vq(2)]] {
            assert_eq!(
                neon_bitwise_16b_bound_query(&inst(opcode, operands)),
                Some(query)
            );
        }
        for operands in [
            vec![d(0), d(1), d(2)],
            vec![vd(0), vd(1), vd(2)],
            vec![q(0), q(1), q(2), MachOperand::Imm(1)],
            vec![q(0), q(1)],
            vec![],
        ] {
            let shape = inst(opcode, operands);
            assert_eq!(neon_bitwise_16b_bound_query(&shape), None, "{shape:?}");
            assert!(
                neon_bitwise_unbound_reason(&shape)
                    .is_some_and(|r| r.starts_with(&format!("no bound shape for {opcode:?} "))),
                "{shape:?}"
            );
            assert_eq!(check_neon_bitwise_16b_word(&shape, word), None, "{shape:?}");
        }
    }

    let not = inst(O::NeonNotV, vec![q(3), q(7)]);
    assert_eq!(
        neon_bitwise_16b_bound_query(&not),
        Some("notv.16b lanewise-intent")
    );
    assert_eq!(check_neon_bitwise_16b_word(&not, 0x6E20_58E3), Some(Ok(())));
    // The 8B NOT, another Vd, another Vn, CNT.
    for w in [0x2E20_58E3, 0x6E20_58E4, 0x6E20_5903, 0x4E20_58E3] {
        assert!(
            matches!(check_neon_bitwise_16b_word(&not, w), Some(Err(_))),
            "{w:#010x}"
        );
    }
    for operands in [
        vec![d(3), d(7)],
        vec![vd(0), vd(1)],
        vec![q(3), q(7), q(8)],
        vec![q(3)],
    ] {
        let shape = inst(O::NeonNotV, operands);
        assert_eq!(neon_bitwise_16b_bound_query(&shape), None, "{shape:?}");
        assert!(neon_bitwise_unbound_reason(&shape).is_some(), "{shape:?}");
    }
    // ORR's refusals are the decoded-value binding's.
    assert_eq!(
        neon_bitwise_unbound_reason(&inst(O::NeonOrrV, vec![d(0), d(1), d(2)])),
        None
    );
    assert_eq!(neon_bitwise_16b_query(O::AddRR), None);
}

/// A virtual register is numbered apart from every physical operand of the
/// same bank, so a two-source OR mixing them is never read as a copy, and a
/// copy of a physical register into a virtual one still is.
#[test]
fn virtual_registers_never_alias_physical_operands() {
    let q = |n: u16| MachOperand::PReg(PReg::new(64 + n));
    let vq = |id: u32| vreg(id, RegClass::Fpr128);
    let orr = AArch64Opcode::NeonOrrV;
    for operands in [
        vec![vq(10), q(1), vq(20)],
        vec![q(1), vq(20), q(0)],
        vec![vq(10), vq(11), q(1)],
        vec![vq(10), q(0), vq(20)],
        vec![vq(0), q(0), vq(1)],
    ] {
        let shape = inst(orr, operands);
        assert_eq!(
            neon_bitwise_16b_bound_query(&shape),
            Some("orrv.16b lanewise-intent"),
            "{shape:?}"
        );
        assert_ne!(
            a64_value_bound_form(&shape),
            Some(Some(A64ValueForm::MovV16B)),
            "{shape:?}"
        );
    }
    for operands in [vec![vq(10), q(1), q(1)], vec![q(1), vq(20), vq(20)]] {
        let shape = inst(orr, operands);
        assert_eq!(
            a64_value_bound_form(&shape),
            Some(Some(A64ValueForm::MovV16B)),
            "{shape:?}"
        );
        assert_eq!(neon_bitwise_16b_bound_query(&shape), None, "{shape:?}");
    }
    // General-purpose copies: a virtual source never reads as the physical
    // destination, and W/X views share one bank.
    let vx = |id: u32| vreg(id, RegClass::Gpr64);
    let numbered = with_virtual_registers_numbered(&inst(
        AArch64Opcode::MOVXrr,
        vec![x(0), vx(9), w(1), vx(9)],
    ))
    .expect("numbered");
    assert_eq!(
        numbered.operands,
        vec![x(0), x(2), w(1), x(2)],
        "the virtual register takes the lowest hardware number no physical operand uses"
    );
}

/// `exact_routing` as it shipped before the borrowed-name routing, verbatim
/// (owned `Arc<str>` names), as the oracle for the rewrite.
fn reference_exact_routing(expr: &SmtExpr) -> Option<Vec<RouteBit>> {
    use RouteBit::{Input, One, Zero};
    fn constant_of(bits: &[RouteBit]) -> Option<u128> {
        if bits.len() > 128 {
            return None;
        }
        bits.iter()
            .enumerate()
            .try_fold(0u128, |acc, (i, bit)| match bit {
                RouteBit::Zero => Some(acc),
                RouteBit::One => Some(acc | (1u128 << i)),
                RouteBit::Input(..) => None,
            })
    }
    fn routing_bool(expr: &SmtExpr) -> Option<bool> {
        match expr {
            SmtExpr::BoolConst(value) => Some(*value),
            SmtExpr::Not { operand } => routing_bool(operand).map(|value| !value),
            SmtExpr::Eq { lhs, rhs } => Some(
                constant_of(&reference_exact_routing(lhs)?)?
                    == constant_of(&reference_exact_routing(rhs)?)?,
            ),
            _ => None,
        }
    }
    let binary =
        |lhs: &SmtExpr, rhs: &SmtExpr, op: fn(&RouteBit, &RouteBit) -> Option<RouteBit>| {
            let (a, b) = (reference_exact_routing(lhs)?, reference_exact_routing(rhs)?);
            if a.len() != b.len() {
                return None;
            }
            a.iter().zip(&b).map(|(x, y)| op(x, y)).collect()
        };
    match expr {
        SmtExpr::Var { name, width } => {
            let name: std::sync::Arc<str> = std::sync::Arc::from(name.as_str());
            Some((0..*width).map(|b| Input(name.clone(), b)).collect())
        }
        SmtExpr::BvConst { value, width } => Some(
            (0..*width)
                .map(|b| {
                    if b < 64 && (value >> b) & 1 == 1 {
                        One
                    } else {
                        Zero
                    }
                })
                .collect(),
        ),
        SmtExpr::Concat { hi, lo, .. } => {
            let mut bits = reference_exact_routing(lo)?;
            bits.extend(reference_exact_routing(hi)?);
            Some(bits)
        }
        SmtExpr::Extract {
            high, low, operand, ..
        } => {
            let bits = reference_exact_routing(operand)?;
            bits.get(*low as usize..=*high as usize).map(<[_]>::to_vec)
        }
        SmtExpr::ZeroExtend {
            operand,
            extra_bits,
            ..
        } => {
            let mut bits = reference_exact_routing(operand)?;
            bits.extend(std::iter::repeat_n(Zero, *extra_bits as usize));
            Some(bits)
        }
        SmtExpr::SignExtend {
            operand,
            extra_bits,
            ..
        } => {
            let mut bits = reference_exact_routing(operand)?;
            let sign = bits.last()?.clone();
            bits.extend(std::iter::repeat_n(sign, *extra_bits as usize));
            Some(bits)
        }
        SmtExpr::BvAnd { lhs, rhs, .. } => binary(lhs, rhs, |a, b| match (a, b) {
            (Zero, _) | (_, Zero) => Some(Zero),
            (One, x) | (x, One) => Some(x.clone()),
            (x, y) if x == y => Some(x.clone()),
            _ => None,
        }),
        SmtExpr::BvOr { lhs, rhs, .. } => binary(lhs, rhs, |a, b| match (a, b) {
            (One, _) | (_, One) => Some(One),
            (Zero, x) | (x, Zero) => Some(x.clone()),
            (x, y) if x == y => Some(x.clone()),
            _ => None,
        }),
        SmtExpr::BvXor { lhs, rhs, .. } => binary(lhs, rhs, |a, b| match (a, b) {
            (Zero, x) | (x, Zero) => Some(x.clone()),
            (One, One) => Some(Zero),
            (x, y) if x == y => Some(Zero),
            _ => None,
        }),
        SmtExpr::BvShl { lhs, rhs, width }
        | SmtExpr::BvLshr { lhs, rhs, width }
        | SmtExpr::BvAshr { lhs, rhs, width } => {
            let bits = reference_exact_routing(lhs)?;
            let amount = constant_of(&reference_exact_routing(rhs)?)?;
            let width = *width as usize;
            let amount = usize::try_from(amount).unwrap_or(usize::MAX);
            Some(
                (0..width)
                    .map(|i| match expr {
                        SmtExpr::BvShl { .. } => {
                            if amount < width && i >= amount {
                                bits[i - amount].clone()
                            } else {
                                Zero
                            }
                        }
                        SmtExpr::BvLshr { .. } => {
                            if amount < width && i + amount < width {
                                bits[i + amount].clone()
                            } else {
                                Zero
                            }
                        }
                        _ => {
                            if amount < width && i + amount < width {
                                bits[i + amount].clone()
                            } else {
                                bits[width - 1].clone()
                            }
                        }
                    })
                    .collect(),
            )
        }
        SmtExpr::BvAdd { lhs, rhs, width } | SmtExpr::BvSub { lhs, rhs, width } => {
            let (a, b) = (reference_exact_routing(lhs)?, reference_exact_routing(rhs)?);
            let is_zero = |bits: &[RouteBit]| bits.iter().all(|bit| *bit == Zero);
            if is_zero(&b) {
                return Some(a);
            }
            if matches!(expr, SmtExpr::BvAdd { .. }) && is_zero(&a) {
                return Some(b);
            }
            let (x, y) = (constant_of(&a)?, constant_of(&b)?);
            let folded = if matches!(expr, SmtExpr::BvAdd { .. }) {
                x.wrapping_add(y)
            } else {
                x.wrapping_sub(y)
            };
            Some(
                (0..*width)
                    .map(|b| {
                        if b < 128 && (folded >> b) & 1 == 1 {
                            One
                        } else {
                            Zero
                        }
                    })
                    .collect(),
            )
        }
        SmtExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            if routing_bool(cond)? {
                reference_exact_routing(then_expr)
            } else {
                reference_exact_routing(else_expr)
            }
        }
        _ => None,
    }
}

/// A random bit-vector expression of `width` over the routing grammar (and a
/// few shapes outside it), for the rewrite's differential test.
fn random_routing_expr(rng: &mut Lcg, width: u32, depth: u32) -> SmtExpr {
    let names = ["x", "y", "z"];
    if depth == 0 || rng.next().is_multiple_of(5) {
        return if rng.next().is_multiple_of(3) {
            SmtExpr::bv_const(
                rng.next()
                    & if rng.next().is_multiple_of(2) {
                        0xff
                    } else {
                        u64::MAX
                    },
                width,
            )
        } else {
            SmtExpr::var(names[(rng.next() % 3) as usize], width)
        };
    }
    let sub = |rng: &mut Lcg, w: u32| random_routing_expr(rng, w, depth - 1);
    match rng.next() % 12 {
        0 if width >= 2 => {
            let lo = 1 + (rng.next() % u64::from(width - 1)) as u32;
            sub(rng, width - lo).concat(sub(rng, lo))
        }
        1 => {
            let extra = (rng.next() % 9) as u32;
            let low = (rng.next() % u64::from(extra + 1)) as u32;
            sub(rng, width + extra).extract(low + width - 1, low)
        }
        2 if width >= 2 => sub(rng, width - 1).zero_ext(1),
        3 if width >= 2 => sub(rng, width / 2 + width % 2).sign_ext(width / 2),
        4 => sub(rng, width).bvand(sub(rng, width)),
        5 => sub(rng, width).bvor(sub(rng, width)),
        6 => sub(rng, width).bvxor(sub(rng, width)),
        7 => sub(rng, width).bvshl(SmtExpr::bv_const(rng.next() % u64::from(width + 2), width)),
        8 => sub(rng, width).bvlshr(sub(rng, width)),
        9 => sub(rng, width).bvashr(SmtExpr::bv_const(rng.next() % u64::from(width + 2), width)),
        10 => {
            if rng.next().is_multiple_of(2) {
                sub(rng, width).bvadd(sub(rng, width))
            } else {
                sub(rng, width).bvsub(sub(rng, width))
            }
        }
        _ => {
            let c =
                SmtExpr::bv_const(rng.next() % 3, 4).eq_expr(SmtExpr::bv_const(rng.next() % 3, 4));
            SmtExpr::ite(c, sub(rng, width), sub(rng, width))
        }
    }
}

#[test]
fn borrowed_routing_equals_the_owned_routing() {
    let mut rng = Lcg(0x0b0e_d4a1_0071_4e5e);
    let mut routings = 0;
    for _ in 0..40_000 {
        let width = [1u32, 4, 8, 16, 32, 64][(rng.next() % 6) as usize];
        let a = random_routing_expr(&mut rng, width, 4);
        let b = if rng.next().is_multiple_of(2) {
            a.clone().bvor(SmtExpr::bv_const(0, width))
        } else {
            random_routing_expr(&mut rng, width, 4)
        };
        let (ra, rb) = (reference_exact_routing(&a), reference_exact_routing(&b));
        assert_eq!(exact_routing(&a), ra, "{a:?}");
        routings += usize::from(ra.is_some());
        // The equality decision and its first mismatch, as the reference
        // implementation computed them.
        let expected = match (ra, rb) {
            (Some(x), Some(y)) if x.len() != y.len() => Some(Err(RoutingMismatch {
                bit: x.len().min(y.len()) as u32,
                intended: RouteBit::Zero,
                emitted: RouteBit::Zero,
            })),
            (Some(x), Some(y)) => match x.iter().zip(&y).position(|(p, q)| p != q) {
                None => Some(Ok(())),
                Some(i) => Some(Err(RoutingMismatch {
                    bit: i as u32,
                    intended: x[i].clone(),
                    emitted: y[i].clone(),
                })),
            },
            _ => None,
        };
        assert_eq!(exact_routing_equality(&a, &b), expected, "{a:?}\n{b:?}");
    }
    assert!(routings > 10_000, "{routings}");
    for &form in A64ValueForm::ALL {
        let obligation = a64_value_form_obligation(form).unwrap();
        for side in [&obligation.trust_ir_expr, &obligation.aarch64_expr] {
            assert_eq!(
                exact_routing(side),
                reference_exact_routing(side),
                "{form:?}"
            );
        }
    }
}

/// The table-spelled register variables are the formatted ones.
#[test]
fn xvar_spells_the_formatted_name() {
    for n in 0..40 {
        match xvar(n) {
            SmtExpr::Var { name, width } => {
                assert_eq!(name, format!("x{n}"));
                assert_eq!(width, 64);
            }
            other => panic!("x{n}: {other:?}"),
        }
    }
}
