use super::*;
use crate::aarch64_value_decode_proofs::{A64Dest, denote_a64_value_word};
use crate::smt::{EvalEnv, EvalResult};
use trust_cg_ir::PReg;

fn reg(field: u16, wide: bool) -> MachOperand {
    MachOperand::PReg(PReg::new(field + if wide { 0 } else { 32 }))
}

fn fixture(op: Op, wide: bool, rd: u16, rn: u16, imm: u32) -> (MachInst, u32) {
    let word = 0x1100_0000
        | (u32::from(wide) << 31)
        | (u32::from(op == Op::SubRI) << 30)
        | (u32::from(op == Op::AddRIShift12) << 22)
        | (imm << 10)
        | (u32::from(rn) << 5)
        | u32::from(rd);
    (
        MachInst::new(
            op,
            vec![
                reg(rd, wide),
                reg(rn, wide),
                MachOperand::Imm(i64::from(imm)),
            ],
        ),
        word,
    )
}

#[test]
fn add_sub_immediate_binding_checks_every_word_bit_and_register_role() {
    for op in [Op::AddRI, Op::SubRI, Op::AddRIShift12] {
        for wide in [false, true] {
            for (rd, rn) in [(0, 1), (29, 31), (31, 29), (31, 31)] {
                for imm in [0, 1, 4095] {
                    let (intent, word) = fixture(op, wide, rd, rn, imm);
                    let bound = bind_add_sub_immediate_word(&intent, word).unwrap();
                    assert_eq!(bound.width(), if wide { 64 } else { 32 });
                    assert_eq!(
                        bound.immediate(),
                        u64::from(imm) << if op == Op::AddRIShift12 { 12 } else { 0 }
                    );
                    assert_eq!(bound.subtracts(), op == Op::SubRI);
                    assert_eq!(
                        bound.source(),
                        if rn == 31 {
                            AddSubImmediateRegister::Sp
                        } else {
                            AddSubImmediateRegister::Gpr(rn as u8)
                        }
                    );
                    assert_eq!(
                        bound.destination(),
                        if rd == 31 {
                            AddSubImmediateRegister::Sp
                        } else {
                            AddSubImmediateRegister::Gpr(rd as u8)
                        }
                    );
                    for bit in 0..32 {
                        assert!(
                            bind_add_sub_immediate_word(&intent, word ^ (1 << bit)).is_err(),
                            "{op:?} wide={wide} bit={bit}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn add_sub_immediate_rejects_zr_banks_widths_arity_and_immediates() {
    let (intent, word) = fixture(Op::AddRI, true, 0, 1, 64);
    for at in [0, 1] {
        for operand in [
            reg(1, false),
            reg(64, true),
            reg(96, true),
            reg(160, true),
            reg(161, true),
            MachOperand::Special(SpecialReg::XZR),
            MachOperand::Special(SpecialReg::WZR),
            MachOperand::Imm(0),
        ] {
            let mut bad = intent.clone();
            bad.operands[at] = operand;
            assert!(bind_add_sub_immediate_word(&bad, word).is_err());
        }
    }
    for immediate in [-1, 4096, i64::MAX] {
        let mut bad = intent.clone();
        bad.operands[2] = MachOperand::Imm(immediate);
        assert!(bind_add_sub_immediate_word(&bad, word).is_err());
    }
    for count in [0, 1, 2, 4] {
        let mut bad = intent.clone();
        bad.operands.resize(count, MachOperand::Imm(0));
        assert!(bind_add_sub_immediate_word(&bad, word).is_err());
    }
    let (mut sp, word) = fixture(Op::AddRI, true, 29, 31, 64);
    sp.operands[1] = MachOperand::Special(SpecialReg::SP);
    assert!(bind_add_sub_immediate_word(&sp, word).is_ok());
    sp.operands[1] = MachOperand::Special(SpecialReg::XZR);
    assert!(bind_add_sub_immediate_word(&sp, word).is_err());
}

#[test]
fn add_sub_effect_uses_supplied_state_and_preserves_existing_denotation() {
    let mut env = EvalEnv::default();
    for op in [Op::AddRI, Op::SubRI, Op::AddRIShift12] {
        for wide in [false, true] {
            for rn in [1, 31] {
                let (intent, word) = fixture(op, wide, 31, rn, 4095);
                let bound = bind_add_sub_immediate_word(&intent, word).unwrap();
                let canonical = if rn == 31 { "sp" } else { "x1" };
                let generic =
                    denote_a64_value_word(&bound.decoded, &FieldOverrides::default()).unwrap();
                let canonical_effect = bound
                    .effect(
                        &SmtExpr::var("sp", 64),
                        &BTreeMap::from([(1, SmtExpr::var("x1", 64))]),
                    )
                    .unwrap();
                assert_eq!(canonical_effect.value, generic.value);
                let registers = BTreeMap::from([
                    (1, SmtExpr::var("actual_x1", 64)),
                    (7, SmtExpr::var("unaffected", 64)),
                ]);
                let before = registers.clone();
                let effect = bound
                    .effect(&SmtExpr::var("actual_sp", 64), &registers)
                    .unwrap();
                assert_eq!(registers, before);
                assert_eq!(effect.dest, A64Dest::Sp);
                assert!(!effect.writes_nzcv);
                for input in [0, 1, u32::MAX as u64, 1 << 32, 1 << 63, u64::MAX] {
                    env.insert("actual_sp".into(), if rn == 31 { input } else { 17 });
                    env.insert("actual_x1".into(), if rn == 1 { input } else { 23 });
                    // Conflicting canonical values expose accidental fallback
                    // to the generic decoder's named state variables.
                    env.insert(canonical.into(), !input);
                    let wanted = if op == Op::SubRI {
                        input.wrapping_sub(bound.immediate())
                    } else {
                        input.wrapping_add(bound.immediate())
                    };
                    let wanted = if wide {
                        wanted
                    } else {
                        u64::from(wanted as u32)
                    };
                    assert_eq!(effect.value.try_eval(&env).unwrap(), EvalResult::Bv(wanted));
                }
            }
        }
    }
}

#[test]
fn add_sub_effect_refuses_missing_and_non_full_register_state() {
    let (intent, word) = fixture(Op::AddRI, false, 0, 1, 1);
    let bound = bind_add_sub_immediate_word(&intent, word).unwrap();
    let sp = SmtExpr::var("sp", 64);
    assert!(bound.effect(&sp, &BTreeMap::new()).is_err());
    for bad in [SmtExpr::var("narrow", 32), SmtExpr::bool_const(false)] {
        assert!(bound.effect(&sp, &BTreeMap::from([(1, bad)])).is_err());
    }
    let (intent, word) = fixture(Op::SubRI, true, 31, 31, 16);
    let bound = bind_add_sub_immediate_word(&intent, word).unwrap();
    assert!(
        bound
            .effect(&SmtExpr::var("narrow", 32), &BTreeMap::new())
            .is_err()
    );
}

#[test]
fn add_sub_actual_state_raw_equations_require_standard_proof_and_wrong_value_refutes() {
    use crate::ay_bridge::{
        AYConfig, AYResult, generate_smt2_query_raw, verify_with_cli_raw_attributed,
    };
    use crate::lowering_proof::{MachineSideProvenance, ProofObligation};
    let directory = tempfile::Builder::new()
        .prefix("trust-cg-add-sub-")
        .tempdir()
        .unwrap()
        .keep();
    let config = AYConfig::default();
    for (index, (op, wide, rn, immediate)) in [
        (Op::AddRI, true, 31, 64),
        (Op::SubRI, true, 1, 16),
        (Op::AddRIShift12, false, 1, 4095),
    ]
    .into_iter()
    .enumerate()
    {
        let (intent, word) = fixture(op, wide, 0, rn, immediate);
        let bound = bind_add_sub_immediate_word(&intent, word).unwrap();
        let input = SmtExpr::var("actual_input", 64);
        let effect = bound
            .effect(&input, &BTreeMap::from([(1, input.clone())]))
            .unwrap();
        let expected = if op == Op::SubRI {
            input
                .clone()
                .bvsub(SmtExpr::bv_const(bound.immediate(), 64))
        } else {
            input
                .clone()
                .bvadd(SmtExpr::bv_const(bound.immediate(), 64))
        };
        let expected = if wide {
            expected
        } else {
            expected.extract(31, 0).zero_ext(32)
        };
        let obligation = ProofObligation {
            name: format!("strict ADD/SUB explicit state {index}"),
            trust_ir_expr: expected,
            aarch64_expr: effect.value,
            inputs: vec![("actual_input".into(), 64)],
            fp_inputs: vec![],
            preconditions: vec![],
            category: None,
            machine_side_provenance: MachineSideProvenance::StaticDb,
        };
        let mut wrong = obligation.clone();
        wrong.name.push_str(" wrong result");
        wrong.trust_ir_expr = wrong.trust_ir_expr.bvadd(SmtExpr::bv_const(1, 64));
        for (name, obligation, positive) in [
            (format!("case-{index}"), &obligation, true),
            (format!("case-{index}-wrong"), &wrong, false),
        ] {
            std::fs::write(
                directory.join(format!("{name}.smt2")),
                generate_smt2_query_raw(obligation, &config),
            )
            .unwrap();
            let verdict = verify_with_cli_raw_attributed(obligation, &config);
            std::fs::write(
                directory.join(format!("{name}.verdict")),
                format!("{verdict:?}\n{}\n", verdict.provenance()),
            )
            .unwrap();
            if positive {
                assert_eq!(verdict.result, AYResult::Verified);
            } else {
                assert!(matches!(verdict.result, AYResult::CounterExample(_)));
            }
        }
    }
    println!("ADD_SUB_ARTIFACT_DIR={directory:?}");
}
