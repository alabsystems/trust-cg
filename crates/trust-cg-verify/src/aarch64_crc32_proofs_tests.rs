// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use std::collections::HashMap;

use super::*;
use crate::gf2_affine_decide::{Concrete, eval_concrete};

/// The bitwise reflected CRC update on host integers.
fn host_crc(mut crc: u32, data: u64, bytes: u32, reflected_poly: u32) -> u32 {
    for byte in 0..bytes {
        crc ^= ((data >> (8 * byte)) & 0xff) as u32;
        for _ in 0..8 {
            crc = if crc & 1 == 1 {
                (crc >> 1) ^ reflected_poly
            } else {
                crc >> 1
            };
        }
    }
    crc
}

fn eval64(term: &SmtExpr, regs: &[(u32, u64)]) -> u64 {
    let values: HashMap<String, u128> = regs
        .iter()
        .map(|&(n, value)| (format!("x{n}"), u128::from(value)))
        .collect();
    match eval_concrete(term, &values).expect("the term evaluates") {
        Concrete::Bv(value, 64) => value as u64,
        other => panic!("not a 64-bit value: {other:?}"),
    }
}

/// The machine side of `form` with `Wd = W0, Wn = W1, Rm = 2`.
fn machine(form: Crc32Form) -> SmtExpr {
    let word = crc32_word(form, 0, 1, 2);
    denote_crc32(&decode_crc32_word(word).expect("decodes")).value
}

#[test]
fn both_sides_compute_the_published_check_values() {
    // CRC-32/ISO-HDLC and CRC-32/ISCSI of "123456789" (init and final XOR
    // 0xFFFFFFFF), one byte per CRC32B/CRC32CB step, on BOTH sides' terms.
    for (castagnoli, check) in [(false, 0xCBF4_3926u32), (true, 0xE306_9283)] {
        let form = Crc32Form { castagnoli, sz: 0 };
        let intent = crc32_intent(&representative_instruction(form, 0, 1, 2))
            .unwrap()
            .value;
        let machine = machine(form);
        let (mut by_machine, mut by_intent) = (u32::MAX, u32::MAX);
        for byte in b"123456789" {
            let regs = |crc: u32| [(1, u64::from(crc)), (2, u64::from(*byte))];
            by_machine = eval64(&machine, &regs(by_machine)) as u32;
            by_intent = eval64(&intent, &regs(by_intent)) as u32;
        }
        assert_eq!(!by_machine, check, "machine side, castagnoli={castagnoli}");
        assert_eq!(!by_intent, check, "intent side, castagnoli={castagnoli}");
    }
}

#[test]
fn every_form_matches_the_host_reference_on_a_grid() {
    let values = [
        0u64,
        1,
        0x80,
        0xFF,
        0x8000_0000,
        0xFFFF_FFFF,
        0x1234_5678_9ABC_DEF0,
        u64::MAX,
        0x8000_0000_0000_0000,
    ];
    for form in Crc32Form::ALL {
        let reflected = if form.castagnoli {
            REFLECTED_CASTAGNOLI
        } else {
            REFLECTED_IEEE
        };
        let machine = machine(form);
        let intent = crc32_intent(&representative_instruction(form, 0, 1, 2))
            .unwrap()
            .value;
        for &acc in &values {
            for &data in &values {
                // Upper register bits are garbage the instruction must ignore.
                let regs = [(1, acc | 0xABCD_0000_0000_0000), (2, data)];
                let masked = if form.sz == 3 {
                    data
                } else {
                    data & ((1u64 << form.data_bits()) - 1)
                };
                let want = u64::from(host_crc(acc as u32, masked, 1 << form.sz, reflected));
                assert_eq!(eval64(&machine, &regs), want, "{} machine", form.mnemonic());
                assert_eq!(eval64(&intent, &regs), want, "{} intent", form.mnemonic());
            }
        }
    }
}

#[test]
fn every_form_holds_over_the_battery_and_every_control_refutes_for_its_reason() {
    let credit = crc32_credit().expect("the CRC32 family holds");
    assert_eq!(credit.forms, 8);
    assert_eq!(credit.instances, 8 * REGISTER_BATTERY.len());
    // Per form: 32 flips, 3 widths, 1 polynomial, 1 swapped word, 1
    // destination, 1 sf, and 8 intent mutations; the byte forms have no byte
    // order or truncation mutation, the word forms no exchanged operands
    // (they are symmetric, see below).
    assert_eq!(
        credit.controls_refuted,
        2 * (39 + 6) + 2 * (39 + 8) + 2 * (38 + 7) + 2 * (39 + 8)
    );
    assert_eq!(crc32_controls().len(), credit.controls_refuted);
}

#[test]
fn the_decoder_refuses_other_words_and_undefined_rows() {
    assert!(matches!(
        decode_crc32_word(0x1AC2_0820), // UDIV W0, W1, W2
        Err(Crc32DecodeRefusal::OtherInstruction { .. })
    ));
    assert!(matches!(
        decode_crc32_word(0xD503_201F), // NOP
        Err(Crc32DecodeRefusal::NotDataProcessing2Source)
    ));
    for form in Crc32Form::ALL {
        let word = crc32_word(form, 0, 1, 2);
        let decoded = decode_crc32_word(word).unwrap();
        assert_eq!(decoded.form(), form);
        assert_eq!((decoded.rd, decoded.rn, decoded.rm), (0, 1, 2));
        assert!(matches!(
            decode_crc32_word(word ^ (1 << 31)),
            Err(Crc32DecodeRefusal::Unallocated(_))
        ));
    }
    // llvm-mc: crc32b w0, w1, w2 = 0x1ac24020; crc32cx w3, w4, x5 = 0x9ac55c83.
    assert_eq!(crc32_word(Crc32Form::ALL[0], 0, 1, 2), 0x1AC2_4020);
    assert_eq!(crc32_word(Crc32Form::ALL[7], 3, 4, 5), 0x9AC5_5C83);
}

#[test]
fn enc5_binding_accepts_the_verified_word_only() {
    for form in Crc32Form::ALL {
        let inst = representative_instruction(form, 4, 5, 6);
        let word = crc32_word(form, 4, 5, 6);
        assert_eq!(check_emitted_crc32_word(&inst, word), Some(Ok(())));
        for bit in 0..32 {
            assert!(
                matches!(
                    check_emitted_crc32_word(&inst, word ^ (1 << bit)),
                    Some(Err(_))
                ),
                "{} bit {bit}",
                form.mnemonic()
            );
        }
    }
    // Other opcodes make no claim.
    let other = MachInst::new(O::UDiv, vec![]);
    assert_eq!(check_emitted_crc32_word(&other, 0), None);
    // An X view of the accumulator is outside the model: no claim.
    let x_acc = MachInst::new(
        O::Crc32B,
        vec![
            MachOperand::PReg(PReg::new(32)),
            MachOperand::PReg(PReg::new(1)),
            MachOperand::PReg(PReg::new(34)),
        ],
    );
    assert_eq!(check_emitted_crc32_word(&x_acc, 0x1AC2_4020), None);
    // The stack pointer is ill-formed and fails closed.
    let sp = MachInst::new(
        O::Crc32B,
        vec![
            MachOperand::PReg(PReg::new(32)),
            MachOperand::Special(SpecialReg::SP),
            MachOperand::PReg(PReg::new(34)),
        ],
    );
    assert!(matches!(check_emitted_crc32_word(&sp, 0), Some(Err(_))));
}

#[test]
fn virtual_registers_are_numbered_apart_and_keep_their_aliasing() {
    let w = |n| MachOperand::VReg(VReg::new(n, RegClass::Gpr32));
    let x = |n| MachOperand::VReg(VReg::new(n, RegClass::Gpr64));
    for (form, data) in [
        (Crc32Form::ALL[1], w(7)),
        (Crc32Form::ALL[3], x(7)),
        (Crc32Form::ALL[6], w(5)),
    ] {
        let inst = MachInst::new(form.opcode(), vec![w(5), w(6), data]);
        assert_eq!(crc32_verdict(&inst).map(|v| v.map(|_| ())), Some(Ok(())));
    }
    let aliased = MachInst::new(O::Crc32Cw, vec![w(1), w(1), w(1)]);
    let (intent, word) = crc32_instance(&aliased).unwrap();
    assert_eq!((intent.rd, intent.rn, intent.rm), (0, 0, 0));
    assert_eq!(check_word_against_intent(&intent, word), Ok(()));
    // A floating-point virtual register is ill-formed.
    let fp = MachInst::new(
        O::Crc32B,
        vec![w(1), w(2), MachOperand::VReg(VReg::new(3, RegClass::Fpr32))],
    );
    assert!(matches!(
        crc32_verdict(&fp),
        Some(Err(Crc32CheckError::IllFormed(_)))
    ));
}

#[test]
fn a_discarded_write_holds_only_against_a_discarded_intent() {
    let form = Crc32Form::ALL[2];
    let inst = representative_instruction(form, 31, 1, 2);
    let intent = crc32_intent(&inst).unwrap();
    assert_eq!(intent.dest, None);
    assert_eq!(
        check_word_against_intent(&intent, crc32_word(form, 31, 1, 2)),
        Ok(())
    );
    assert!(matches!(
        check_word_against_intent(&intent, crc32_word(form, 0, 1, 2)),
        Err(Crc32CheckError::Refuted {
            class: Crc32RefusalClass::Destination,
            ..
        })
    ));
}

#[test]
fn the_word_forms_are_symmetric_in_their_registers_and_the_others_are_not() {
    // Not a control: an exact fact about CRC32W/CRC32CW. Both registers are
    // padded to BitReverse(x):Zeros(32) and XOR-ed, so exchanging Rn and Rm
    // cannot change the result, and the decision proves it for every value.
    for form in Crc32Form::ALL {
        let inst = representative_instruction(form, 0, 1, 2);
        let intent = crc32_intent(&inst).unwrap();
        let swapped = check_word_against_intent(&intent, crc32_word(form, 0, 2, 1));
        if form.sz == 2 {
            assert_eq!(swapped, Ok(()), "{}", form.mnemonic());
        } else {
            assert!(
                matches!(
                    swapped,
                    Err(Crc32CheckError::Refuted {
                        class: Crc32RefusalClass::Value,
                        ..
                    })
                ),
                "{}",
                form.mnemonic()
            );
        }
    }
}

#[test]
fn the_walk_reports_a_holding_crc32_unverified_and_never_credits_it() {
    use crate::function_verifier::{InstructionVerificationResult, verify_function};
    use trust_cg_ir::{MachFunction, Signature};
    let mut function = MachFunction::new("crc32_walk".into(), Signature::new(vec![], vec![]));
    for form in Crc32Form::ALL {
        let id = function.push_inst(representative_instruction(form, 0, 1, 2));
        function.append_inst(function.entry, id);
    }
    let ill_formed = function.push_inst(MachInst::new(
        O::Crc32Cb,
        vec![
            MachOperand::PReg(PReg::new(32)),
            MachOperand::Special(SpecialReg::SP),
            MachOperand::PReg(PReg::new(34)),
        ],
    ));
    function.append_inst(function.entry, ill_formed);
    let report = verify_function(&function);
    assert_eq!(report.instructions.len(), 9);
    for row in &report.instructions[..8] {
        match &row.result {
            InstructionVerificationResult::Unverified { reason } => {
                assert!(reason.starts_with(CRC32_DECIDED_IS_NOT_CREDIT), "{reason}");
                assert!(reason.contains("holds"), "{reason}");
            }
            other => panic!("a holding CRC32 row must stay unverified: {other:?}"),
        }
    }
    assert!(
        matches!(
            report.instructions[8].result,
            InstructionVerificationResult::Failed { .. }
        ),
        "{:?}",
        report.instructions[8].result
    );
}
