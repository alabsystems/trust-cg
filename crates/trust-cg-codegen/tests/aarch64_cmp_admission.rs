// Copyright 2026 Andrew Yates | Apache-2.0
//! Exact CMP operand admission and independent byte checks, not source proofs.
//! Register CMP is SUBS ZR,Rn,Rm (Rn/Rm 31 mean ZR); immediate CMP is
//! SUBS ZR,Rn,#imm (Rn 31 means SP). Typed aliases additionally own sf.

use trust_cg_codegen::{
    aarch64::{decode_check::A64DecodeCheck, encode::encode_instruction},
    decode_check::{DecodeCheck, DecodeCheckOutcome},
};
use trust_cg_ir::{
    AArch64Opcode as Op, MachInst, MachOperand as Arg, RegClass, VReg,
    regs::{self, PReg, SpecialReg},
};

fn register(width: u32, index: u16) -> Arg {
    assert!(index < 31);
    Arg::PReg(PReg::new(index + if width == 32 { 32 } else { 0 }))
}

fn register_ops(width: u32) -> [Op; 2] {
    [Op::CmpRR, if width == 32 { Op::CMPWrr } else { Op::CMPXrr }]
}

fn immediate_ops(width: u32) -> [Op; 2] {
    [Op::CmpRI, if width == 32 { Op::CMPWri } else { Op::CMPXri }]
}

fn register_operands(width: u32) -> Vec<(Arg, u32)> {
    let mut result: Vec<_> = (0..31)
        .map(|n| (register(width, n), u32::from(n)))
        .collect();
    result.push((
        Arg::PReg(if width == 32 { regs::WZR } else { regs::XZR }),
        31,
    ));
    result.push((
        Arg::Special(if width == 32 {
            SpecialReg::WZR
        } else {
            SpecialReg::XZR
        }),
        31,
    ));
    result
}

fn immediate_bases(width: u32) -> Vec<(Arg, u32)> {
    let mut result: Vec<_> = (0..31)
        .map(|n| (register(width, n), u32::from(n)))
        .collect();
    result.push((
        Arg::PReg(if width == 32 { regs::WSP } else { regs::SP }),
        31,
    ));
    if width == 64 {
        result.push((Arg::Special(SpecialReg::SP), 31));
    }
    result
}

// Independent literal encoding layout; never call encoder field helpers.
fn rr_word(width: u32, rn: u32, rm: u32) -> u32 {
    0x6b00_001f | (u32::from(width == 64) << 31) | (rm << 16) | (rn << 5)
}

fn ri_word(width: u32, rn: u32, immediate: u32) -> u32 {
    0x7100_001f | (u32::from(width == 64) << 31) | (immediate << 10) | (rn << 5)
}

fn check(inst: &MachInst, word: u32) -> DecodeCheckOutcome {
    A64DecodeCheck.check_one(inst, &word.to_le_bytes(), None)
}

fn all_register_forms(mut visit: impl FnMut(MachInst, u32)) {
    for width in [32, 64] {
        for op in register_ops(width) {
            for (lhs, rn) in register_operands(width) {
                for (rhs, rm) in register_operands(width) {
                    visit(
                        MachInst::new(op, vec![lhs.clone(), rhs]),
                        rr_word(width, rn, rm),
                    );
                }
            }
        }
    }
}

fn all_immediate_forms(mut visit: impl FnMut(MachInst, u32)) {
    for width in [32, 64] {
        for op in immediate_ops(width) {
            for (base, rn) in immediate_bases(width) {
                for immediate in 0..=4095 {
                    visit(
                        MachInst::new(op, vec![base.clone(), Arg::Imm(i64::from(immediate))]),
                        ri_word(width, rn, immediate),
                    );
                }
            }
        }
    }
}

#[test]
fn cmp_register_encoder_preserves_every_gpr_and_zero_register_form() {
    let mut count = 0;
    all_register_forms(|inst, expected| {
        assert_eq!(encode_instruction(&inst).unwrap(), expected, "{inst:?}");
        count += 1;
    });
    assert_eq!(count, 4356);
}

#[test]
fn cmp_immediate_encoder_preserves_every_gpr_stack_pointer_and_imm12() {
    let mut count = 0;
    all_immediate_forms(|inst, expected| {
        assert_eq!(encode_instruction(&inst).unwrap(), expected, "{inst:?}");
        count += 1;
    });
    assert_eq!(count, 532480);
}

#[test]
fn cmp_decoder_accepts_every_supported_form_including_typed_aliases() {
    let mut count = 0;
    let mut visit = |inst: MachInst, expected| {
        assert!(
            matches!(check(&inst, expected), DecodeCheckOutcome::Match),
            "{inst:?}"
        );
        count += 1;
    };
    all_register_forms(&mut visit);
    all_immediate_forms(visit);
    assert_eq!(count, 536836);
}

fn other_operands() -> Vec<Arg> {
    vec![
        Arg::PReg(regs::S0),
        Arg::PReg(regs::D0),
        Arg::PReg(regs::V0),
        Arg::PReg(regs::H0),
        Arg::PReg(regs::B0),
        Arg::PReg(regs::NZCV),
        Arg::PReg(PReg::new(229)),
        Arg::PReg(PReg::new(u16::MAX)),
        Arg::VReg(VReg::new(0, RegClass::Gpr64)),
        Arg::Imm(0),
    ]
}

fn malformed_register_forms() -> Vec<(MachInst, u32)> {
    let mut cases = Vec::new();
    for width in [32, 64] {
        for op in register_ops(width) {
            let valid = MachInst::new(op, vec![register(width, 0), register(width, 1)]);
            let word = rr_word(width, 0, 1);
            for position in 0..2 {
                for bad in other_operands().into_iter().chain([
                    Arg::PReg(regs::SP),
                    Arg::PReg(regs::WSP),
                    Arg::Special(SpecialReg::SP),
                    register(if width == 32 { 64 } else { 32 }, 1),
                    Arg::Special(if width == 32 {
                        SpecialReg::XZR
                    } else {
                        SpecialReg::WZR
                    }),
                ]) {
                    let mut inst = valid.clone();
                    inst.operands[position] = bad;
                    cases.push((inst, word));
                }
            }
            for length in 0..2 {
                let mut inst = valid.clone();
                inst.operands.truncate(length);
                cases.push((inst, word));
            }
            for tail in [Arg::Imm(0), Arg::Imm(1), register(width, 2)] {
                let mut inst = valid.clone();
                inst.operands.push(tail);
                cases.push((inst, word));
            }
            if op != Op::CmpRR {
                let opposite = if width == 32 { 64 } else { 32 };
                cases.push((
                    MachInst::new(op, vec![register(opposite, 0), register(opposite, 1)]),
                    rr_word(opposite, 0, 1),
                ));
            }
        }
    }
    cases
}

fn malformed_immediate_forms() -> Vec<(MachInst, u32)> {
    let mut cases = Vec::new();
    for width in [32, 64] {
        for op in immediate_ops(width) {
            let valid = MachInst::new(op, vec![register(width, 0), Arg::Imm(42)]);
            let word = ri_word(width, 0, 42);
            for bad in other_operands().into_iter().chain([
                Arg::PReg(regs::XZR),
                Arg::PReg(regs::WZR),
                Arg::Special(SpecialReg::XZR),
                Arg::Special(SpecialReg::WZR),
            ]) {
                let mut inst = valid.clone();
                inst.operands[0] = bad;
                cases.push((inst, word));
            }
            for bad in [
                Arg::Imm(-1),
                Arg::Imm(4096),
                Arg::Imm(i64::MIN),
                Arg::Imm(i64::MAX),
                register(width, 1),
                Arg::VReg(VReg::new(0, RegClass::Gpr32)),
            ] {
                let mut inst = valid.clone();
                inst.operands[1] = bad;
                cases.push((inst, word));
            }
            for length in 0..2 {
                let mut inst = valid.clone();
                inst.operands.truncate(length);
                cases.push((inst, word));
            }
            let mut extra = valid;
            extra.operands.push(Arg::Imm(0));
            cases.push((extra, word));
            if op != Op::CmpRI {
                let opposite = if width == 32 { 64 } else { 32 };
                for (base, rn) in immediate_bases(opposite) {
                    cases.push((
                        MachInst::new(op, vec![base, Arg::Imm(42)]),
                        ri_word(opposite, rn, 42),
                    ));
                }
            }
        }
    }
    cases
}

#[test]
fn cmp_register_encoder_refuses_malformed_intents() {
    let cases = malformed_register_forms();
    assert_eq!(cases.len(), 142);
    let admitted: Vec<_> = cases
        .iter()
        .filter(|(inst, _)| encode_instruction(inst).is_ok())
        .map(|(inst, _)| inst)
        .collect();
    assert!(
        admitted.is_empty(),
        "{} malformed register forms admitted; first={:?}",
        admitted.len(),
        admitted.first()
    );
}

#[test]
fn cmp_immediate_encoder_refuses_malformed_intents() {
    let cases = malformed_immediate_forms();
    assert_eq!(cases.len(), 157);
    let admitted: Vec<_> = cases
        .iter()
        .filter(|(inst, _)| encode_instruction(inst).is_ok())
        .map(|(inst, _)| inst)
        .collect();
    assert!(
        admitted.is_empty(),
        "{} malformed immediate forms admitted; first={:?}",
        admitted.len(),
        admitted.first()
    );
}

#[test]
fn cmp_decoder_refuses_malformed_intents_never_allowlists_them() {
    let cases: Vec<_> = malformed_register_forms()
        .into_iter()
        .chain(malformed_immediate_forms())
        .collect();
    assert_eq!(cases.len(), 299);
    let admitted: Vec<_> = cases
        .iter()
        .filter(|(inst, word)| !matches!(check(inst, *word), DecodeCheckOutcome::Mismatch(_)))
        .map(|(inst, word)| (inst, check(inst, *word)))
        .collect();
    assert!(
        admitted.is_empty(),
        "{} malformed intents not rejected; first={:?}",
        admitted.len(),
        admitted.first()
    );
}

#[test]
fn cmp_decoder_refutes_every_word_bit_and_nonword_length() {
    let mut words = Vec::new();
    for width in [32, 64] {
        for op in register_ops(width) {
            for (lhs, rhs, rn, rm) in [
                (register(width, 3), register(width, 27), 3, 27),
                (
                    register_operands(width)[31].0.clone(),
                    register_operands(width)[32].0.clone(),
                    31,
                    31,
                ),
            ] {
                words.push((MachInst::new(op, vec![lhs, rhs]), rr_word(width, rn, rm)));
            }
        }
        for op in immediate_ops(width) {
            for immediate in [0, 4095] {
                for index in [0, 31] {
                    let (base, rn) = immediate_bases(width)[index].clone();
                    words.push((
                        MachInst::new(op, vec![base, Arg::Imm(i64::from(immediate))]),
                        ri_word(width, rn, immediate),
                    ));
                }
            }
        }
    }
    assert_eq!(words.len(), 24);
    let mut bit_checks = 0;
    let mut length_checks = 0;
    for (inst, word) in words {
        assert!(
            matches!(check(&inst, word), DecodeCheckOutcome::Match),
            "positive control {inst:?}"
        );
        for bit in 0..32 {
            assert!(
                matches!(
                    check(&inst, word ^ (1 << bit)),
                    DecodeCheckOutcome::Mismatch(_)
                ),
                "word mutation {inst:?} bit={bit}"
            );
            bit_checks += 1;
        }
        let mut bytes = word.to_le_bytes().repeat(2);
        for length in [0, 1, 2, 3, 5, 8] {
            assert!(
                matches!(
                    A64DecodeCheck.check_one(&inst, &bytes[..length], None),
                    DecodeCheckOutcome::Mismatch(_)
                ),
                "length={length} {inst:?}"
            );
            length_checks += 1;
        }
        bytes.clear();
    }
    assert_eq!((bit_checks, length_checks), (768, 144));
}
