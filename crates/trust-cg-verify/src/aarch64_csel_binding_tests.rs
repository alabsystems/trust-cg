use super::*;
use crate::aarch64_csel_semantics::{ConditionalSelectOperation, RegisterState};
use trust_cg_ir::{AArch64Opcode as M, PReg};

fn register(index: u16, wide: bool) -> MachOperand {
    MachOperand::PReg(PReg::new(index + if wide { 0 } else { 32 }))
}

fn select(op: M, wide: bool, condition: u32) -> (MachInst, u32) {
    let (a, b) = match op {
        M::Csel => (0, 0),
        M::Csinc => (0, 1),
        M::Csinv => (1, 0),
        M::Csneg => (1, 1),
        _ => panic!(),
    };
    (
        MachInst::new(
            op,
            vec![
                register(0, wide),
                register(1, wide),
                register(2, wide),
                MachOperand::Imm(i64::from(condition)),
            ],
        ),
        0x1a80_0000
            | (u32::from(wide) << 31)
            | (a << 30)
            | (b << 10)
            | (2 << 16)
            | (condition << 12)
            | (1 << 5),
    )
}

#[test]
fn shared_select_binding_keeps_all_fields_widths_and_conditions() {
    for opcode in [M::Csel, M::Csinc, M::Csinv, M::Csneg] {
        for wide in [false, true] {
            for condition in 0..16 {
                let (intent, word) = select(opcode, wide, condition);
                let decoded = bind_conditional_select_word(&intent, word).unwrap();
                assert_eq!(decoded.width().bits(), if wide { 64 } else { 32 });
                assert_eq!(decoded.registers(), (0, 1, 2));
                assert_eq!(u32::from(decoded.condition()), condition);
                for bit in [0, 5, 10, 11, 12, 16, 29, 30, 31] {
                    assert!(
                        bind_conditional_select_word(&intent, word ^ (1 << bit)).is_err(),
                        "{opcode:?} wide={wide} condition={condition} bit={bit}"
                    );
                }
            }
        }
    }
}

#[test]
fn select_intent_cannot_disguise_sp_wrong_bank_width_or_extra_operand() {
    let (intent, word) = select(M::Csel, true, 0);
    for operand in [
        MachOperand::Special(SpecialReg::SP),
        MachOperand::PReg(PReg::new(31)),
        MachOperand::PReg(PReg::new(63)),
        MachOperand::PReg(PReg::new(64)),
        register(1, false),
    ] {
        let mut bad = intent.clone();
        bad.operands[1] = operand;
        assert!(bind_conditional_select_word(&bad, word).is_err());
    }
    let mut bad = intent.clone();
    bad.operands.push(MachOperand::Imm(0));
    assert!(bind_conditional_select_word(&bad, word).is_err());
    for condition in [-1, 16] {
        let mut bad = intent.clone();
        bad.operands[3] = MachOperand::Imm(condition);
        assert!(bind_conditional_select_word(&bad, word).is_err());
    }
}

#[test]
fn cset_alias_keeps_inverse_condition_and_refuses_al_nv() {
    for wide in [false, true] {
        for condition in 0..14 {
            let intent = MachInst::new(
                M::CSet,
                vec![register(0, wide), MachOperand::Imm(condition)],
            );
            let word = 0x1a9f_07e0 | (u32::from(wide) << 31) | (((condition as u32) ^ 1) << 12);
            let decoded = bind_conditional_select_word(&intent, word).unwrap();
            assert!(
                bind_conditional_select_word(&intent, word ^ (1 << 12)).is_err(),
                "CSET inverse condition must match"
            );
            assert_eq!(decoded.operation(), ConditionalSelectOperation::Csinc);
            assert_eq!(decoded.registers(), (0, 31, 31));
            assert_eq!(i64::from(decoded.condition()), condition ^ 1);
        }
        for condition in [14, 15] {
            let intent = MachInst::new(
                M::CSet,
                vec![register(0, wide), MachOperand::Imm(condition)],
            );
            assert!(
                bind_conditional_select_word(&intent, 0x1a9f_07e0 | (u32::from(wide) << 31))
                    .is_err()
            );
        }
    }
}

#[test]
fn decoded_select_footprint_keeps_sp_flags_other_registers_and_zr_discard() {
    for opcode in [M::Csel, M::Csinc, M::Csinv, M::Csneg] {
        for wide in [false, true] {
            for destination in [0, 18, 19, 29, 30, 31] {
                for flags in 0..16 {
                    let (mut intent, word) = select(opcode, wide, 1);
                    intent.operands[0] = if destination == 31 {
                        MachOperand::Special(if wide {
                            SpecialReg::XZR
                        } else {
                            SpecialReg::WZR
                        })
                    } else {
                        register(destination as u16, wide)
                    };
                    let decoded =
                        bind_conditional_select_word(&intent, word | destination).unwrap();
                    let before = RegisterState {
                        x: std::array::from_fn(|i| u64::MAX - i as u64),
                        sp: 0x1000,
                        nzcv: flags,
                    };
                    let after = decoded.execute(&before).unwrap();
                    assert_eq!(after.sp, before.sp);
                    assert_eq!(after.nzcv, before.nzcv);
                    for register in 0..31 {
                        if register != destination as usize {
                            assert_eq!(after.x[register], before.x[register]);
                        }
                    }
                    if !wide && destination < 31 {
                        assert_eq!(after.x[destination as usize] >> 32, 0);
                    }
                }
            }
        }
    }
}
