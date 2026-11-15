// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use crate::smt::{EvalEnv, EvalResult};

/// Host `AddWithCarry(a, NOT imm, 1)` flags at `width`.
fn host_flags(a: u64, imm: u64, width: u32) -> (u64, [bool; 4]) {
    let mask = if width == 64 {
        u64::MAX
    } else {
        (1 << width) - 1
    };
    let a = a & mask;
    let result = a.wrapping_sub(imm) & mask;
    let sign = |x: u64| (x >> (width - 1)) & 1 == 1;
    let n = sign(result);
    let z = result == 0;
    let c = a >= imm;
    let v = sign(a) != sign(imm) && sign(result) != sign(a);
    (result, [n, z, c, v])
}

fn eval_bool(term: &SmtExpr, env: &EvalEnv) -> bool {
    match term.eval(env) {
        EvalResult::Bool(b) => b,
        other => panic!("not a Boolean: {other:?}"),
    }
}

fn eval_bv(term: &SmtExpr, env: &EvalEnv) -> u64 {
    match term.eval(env) {
        EvalResult::Bv(v) => v,
        other => panic!("not a bit-vector: {other:?}"),
    }
}

#[test]
fn llvm_mc_words_decode_and_both_sides_match_the_host_reference() {
    // llvm-mc: subs x16, x16, #1 = 0xf1000610; subs w0, w1, #4095 = 0x713ffc20.
    assert_eq!(subs_imm_word(SubsImmForm::X, 16, 16, 1), 0xF100_0610);
    assert_eq!(subs_imm_word(SubsImmForm::W, 0, 1, 4095), 0x713F_FC20);
    let grid = [
        0u64,
        1,
        2,
        0x7FF,
        0xFFF,
        0x1000,
        0x7FFF_FFFF,
        0x8000_0000,
        0x8000_0001,
        0xFFFF_FFFF,
        0x7FFF_FFFF_FFFF_FFFF,
        0x8000_0000_0000_0000,
        0x8000_0000_0000_0001,
        u64::MAX,
    ];
    for form in SubsImmForm::ALL {
        for imm in [0u32, 1, 2048, 4095] {
            let inst = representative_instruction(form, 0, 1, imm);
            let intent = subs_imm_intent(&inst).unwrap();
            let word = subs_imm_word(form, 0, 1, imm);
            let effect = denote_add_sub_imm(&decode_add_sub_imm_word(word).unwrap());
            let machine_flags = effect.flags.clone().expect("SUBS sets flags");
            for &a in &grid {
                let mut env = EvalEnv::default();
                env.insert("x1".into(), a);
                let (result, flags) = host_flags(a, u64::from(imm), form.width());
                assert_eq!(
                    eval_bv(&effect.value, &env),
                    result,
                    "{form:?} {a:#x} - {imm}"
                );
                assert_eq!(eval_bv(&intent.value, &env), result, "{form:?} intent");
                for (i, ((name, m), (_, t))) in machine_flags
                    .parts()
                    .into_iter()
                    .zip(intent.flags.parts())
                    .enumerate()
                {
                    assert_eq!(eval_bool(m, &env), flags[i], "{form:?} {name} {a:#x}-{imm}");
                    assert_eq!(eval_bool(t, &env), flags[i], "{form:?} intent {name}");
                }
            }
        }
    }
}

#[test]
fn both_forms_hold_and_every_control_refutes_for_its_reason() {
    let credit = subs_imm_credit().expect("the SUBS #imm row holds");
    assert_eq!(credit.forms, 2);
    assert_eq!(credit.instances, 2 * INSTANCE_BATTERY.len());
    // Per form: 32 flips, 9 neighbouring words, 7 intent mutations.
    assert_eq!(credit.controls_refuted, 2 * (32 + 9 + 7));
}

#[test]
fn enc5_binding_accepts_the_probe_word_only() {
    let inst = representative_instruction(SubsImmForm::X, 16, 16, 1);
    assert_eq!(
        check_emitted_subs_imm_word(&inst, 0xF100_0610),
        Some(Ok(()))
    );
    for bit in 0..32 {
        assert!(matches!(
            check_emitted_subs_imm_word(&inst, 0xF100_0610 ^ (1 << bit)),
            Some(Err(_))
        ));
    }
    // Other opcodes make no claim; mixed views are outside the model.
    assert_eq!(
        check_emitted_subs_imm_word(&MachInst::new(O::SubRI, vec![]), 0),
        None
    );
    let mixed = MachInst::new(
        O::SubsRI,
        vec![
            MachOperand::PReg(PReg::new(16)),
            MachOperand::PReg(PReg::new(48)),
            MachOperand::Imm(1),
        ],
    );
    assert_eq!(check_emitted_subs_imm_word(&mixed, 0xF100_0610), None);
    // An immediate outside imm12, a ZR source and an SP destination fail
    // closed.
    for operands in [
        vec![
            MachOperand::PReg(PReg::new(16)),
            MachOperand::PReg(PReg::new(16)),
            MachOperand::Imm(4096),
        ],
        vec![
            MachOperand::PReg(PReg::new(16)),
            MachOperand::Special(SpecialReg::XZR),
            MachOperand::Imm(1),
        ],
        vec![
            MachOperand::Special(SpecialReg::SP),
            MachOperand::PReg(PReg::new(16)),
            MachOperand::Imm(1),
        ],
        vec![],
    ] {
        let inst = MachInst::new(O::SubsRI, operands);
        assert!(
            matches!(
                check_emitted_subs_imm_word(&inst, 0xF100_0610),
                Some(Err(_))
            ),
            "{inst:?}"
        );
    }
}

#[test]
fn virtual_registers_hold_and_the_walk_never_credits_them() {
    use crate::function_verifier::{InstructionVerificationResult, verify_function};
    use trust_cg_ir::{MachFunction, Signature};
    let x = |n| MachOperand::VReg(VReg::new(n, RegClass::Gpr64));
    let pre_ra = MachInst::new(O::SubsRI, vec![x(1), x(1), MachOperand::Imm(1)]);
    assert!(matches!(subs_imm_verdict(&pre_ra), Some(Ok(_))));
    let mut function = MachFunction::new("subs_walk".into(), Signature::new(vec![], vec![]));
    for inst in [
        representative_instruction(SubsImmForm::X, 16, 16, 1),
        representative_instruction(SubsImmForm::W, 3, 4, 4095),
        pre_ra,
    ] {
        let id = function.push_inst(inst);
        function.append_inst(function.entry, id);
    }
    let report = verify_function(&function);
    assert_eq!(report.instructions.len(), 3);
    for row in &report.instructions {
        match &row.result {
            InstructionVerificationResult::Unverified { reason } => {
                assert!(
                    reason.starts_with(SUBS_IMM_DECIDED_IS_NOT_CREDIT),
                    "{reason}"
                );
                assert!(reason.contains("holds"), "{reason}");
            }
            other => panic!("a holding SUBS #imm must stay unverified: {other:?}"),
        }
    }
}
