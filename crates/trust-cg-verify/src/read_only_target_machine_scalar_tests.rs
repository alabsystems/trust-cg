// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Allocated scalar-memory shape/effect controls, not an independent proof.

use super::*;
use crate::smt::EvalEnv;
use trust_cg_ir::regs::{NZCV, W0, W1, W2, W3, WZR, X0, X1, X2, X3, X18, X30, XZR};
use trust_cg_ir::{InstFlags, PReg, ProofAnnotation, RegClass, Signature, VReg};

fn p(reg: PReg) -> O {
    O::PReg(reg)
}

fn machine(body: Vec<MachInst>) -> MachFunction {
    let mut machine = MachFunction::new(
        "scalar_memory_machine_control".into(),
        Signature::new(vec![Type::I64; 4], vec![Type::I64]),
    );
    let mut ret = MachInst::new(M::Ret, vec![p(X30)]);
    ret.implicit_uses = &[X0];
    for inst in body.into_iter().chain([ret]) {
        let id = machine.push_inst(inst);
        machine.append_inst(machine.entry, id);
    }
    machine
}

fn steps(inst: MachInst) -> Vec<Step> {
    adapt_profile(&machine(vec![inst]), Profile::ScalarMemory).unwrap()
}

fn refused(inst: MachInst, reason: &'static str) {
    assert_eq!(
        adapt_profile(&machine(vec![inst]), Profile::ScalarMemory).err(),
        Some(invalid(reason))
    );
}

fn eval(expr: &E, values: [u64; 4]) -> u64 {
    let mut env = EvalEnv::default();
    for (i, value) in values.into_iter().enumerate() {
        env.insert(format!("x{i}"), value);
    }
    expr.try_eval(&env).unwrap().as_u64()
}

#[test]
fn immediate_memory_uses_existing_exact_grammar_and_four_or_eight_byte_effects() {
    for (data, width) in [(W0, 4), (X0, 8), (WZR, 4), (XZR, 8)] {
        for op in [M::LdrRI, M::StrRI] {
            for offset in [-256, -1, 0, 1, 255, 4095 * i64::from(width)] {
                let effect = steps(MachInst::new(op, vec![p(data), p(X1), O::Imm(offset)]));
                assert_eq!(effect.len(), 2);
                match &effect[0] {
                    Step::MemoryLoad {
                        destination,
                        address,
                        byte_width,
                        alignment,
                    } => {
                        assert_eq!(
                            *destination,
                            if data == WZR || data == XZR { 31 } else { 0 }
                        );
                        assert_eq!((*byte_width, *alignment), (width, 1));
                        assert_eq!(
                            eval(address, [0, 0x1000, 0, 0]),
                            0x1000u64.wrapping_add(offset as u64)
                        );
                    }
                    Step::MemoryStore {
                        address,
                        value,
                        byte_width,
                        alignment,
                    } => {
                        assert_eq!((*byte_width, *alignment), (width, 1));
                        assert_eq!(value.try_bv_width().unwrap(), width * 8);
                        assert_eq!(
                            eval(address, [0, 0x1000, 0, 0]),
                            0x1000u64.wrapping_add(offset as u64)
                        );
                        let expected = if data == WZR || data == XZR {
                            0
                        } else if width == 4 {
                            0x7654_3210
                        } else {
                            0xfedc_ba98_7654_3210
                        };
                        assert_eq!(eval(value, [0xfedc_ba98_7654_3210, 0, 0, 0]), expected);
                    }
                    _ => panic!("memory effect required"),
                }
            }
            for tail in [
                vec![p(X1)],
                vec![O::MemOp {
                    base: X1,
                    offset: 8,
                }],
            ] {
                let mut operands = vec![p(data)];
                operands.extend(tail);
                assert_eq!(steps(MachInst::new(op, operands)).len(), 2);
            }
        }
    }
    // Preserve the original readonly endpoint and its historical W refusal.
    let readonly = adapt(&machine(vec![MachInst::new(
        M::LdrRI,
        vec![p(X0), p(X1), O::Imm(0)],
    )]))
    .unwrap();
    assert!(matches!(readonly[0], Step::Load { .. }));
    assert_eq!(
        adapt(&machine(vec![MachInst::new(
            M::LdrRI,
            vec![p(W0), p(X1), O::Imm(0)]
        )]))
        .err(),
        Some(invalid("requires 64-bit X load destination"))
    );
}

#[test]
fn register_memory_reads_exact_index_extension_and_access_size_scale() {
    for data in [W0, X0] {
        let width = if data == W0 { 4 } else { 8 };
        for mode in [4, 5, 6, 7, 12, 13, 14, 15] {
            for index_value in [
                0,
                1,
                0xffff_ffff,
                0x8000_0000,
                u64::MAX,
                0x1234_5678_9abc_def0,
            ] {
                for op in [M::LdrRO, M::StrRO] {
                    let effect =
                        steps(MachInst::new(op, vec![p(data), p(X1), p(X2), O::Imm(mode)]));
                    let address = match &effect[0] {
                        Step::MemoryLoad {
                            address,
                            byte_width,
                            ..
                        }
                        | Step::MemoryStore {
                            address,
                            byte_width,
                            ..
                        } => {
                            assert_eq!(*byte_width, width);
                            address
                        }
                        _ => panic!("register memory effect"),
                    };
                    let extended = match mode >> 1 {
                        2 => u64::from(index_value as u32),
                        6 => index_value as u32 as i32 as i64 as u64,
                        _ => index_value,
                    };
                    let scaled = if mode & 1 == 0 {
                        extended
                    } else {
                        extended.wrapping_mul(u64::from(width))
                    };
                    assert_eq!(
                        eval(address, [0, 0x1000, index_value, 0]),
                        0x1000u64.wrapping_add(scaled),
                        "{data:?}/{op:?}/{mode}/{index_value}"
                    );
                }
            }
        }
        // Unspecified mode is the existing unscaled full-X index form.
        let effect = steps(MachInst::new(M::LdrRO, vec![p(data), p(X1), p(X2)]));
        let Step::MemoryLoad { address, .. } = &effect[0] else {
            panic!("load")
        };
        assert_eq!(eval(address, [0, 0x1000, 7, 0]), 0x1007);
        for mode in [4, 5, 12, 13] {
            assert_eq!(
                steps(MachInst::new(
                    M::LdrRO,
                    vec![p(data), p(X1), p(W2), O::Imm(mode)]
                ))
                .len(),
                2
            );
        }
        for zero in [WZR, XZR] {
            let effect = steps(MachInst::new(
                M::LdrRO,
                vec![p(data), p(X1), p(zero), O::Imm(7)],
            ));
            let Step::MemoryLoad { address, .. } = &effect[0] else {
                panic!("load")
            };
            assert_eq!(eval(address, [0, 0x1000, 7, 0]), 0x1000);
        }
    }
}

#[test]
fn load_pair_is_one_step_and_snapshots_aliasing_base_before_both_writes() {
    for (first, second, zero, width) in [(W1, W0, WZR, 4), (X1, X0, XZR, 8)] {
        for destinations in [[first, second], [first, zero], [zero, second]] {
            for offset in [-64 * i64::from(width), 0, 63 * i64::from(width)] {
                let effect = steps(MachInst::new(
                    M::LdpRI,
                    vec![
                        p(destinations[0]),
                        p(destinations[1]),
                        p(X1),
                        O::Imm(offset),
                    ],
                ));
                assert_eq!(effect.len(), 2);
                let Step::LoadPair {
                    destinations: slots,
                    address,
                    byte_width,
                    alignment,
                } = &effect[0]
                else {
                    panic!("one pair effect")
                };
                assert_eq!(*byte_width, width);
                assert_eq!(*alignment, 1);
                assert_eq!(slots[0], if destinations[0] == zero { 31 } else { 1 });
                assert_eq!(slots[1], if destinations[1] == zero { 31 } else { 0 });
                assert_eq!(
                    eval(address, [0xdead, 0x1000, 0, 0]),
                    0x1000u64.wrapping_add(offset as u64)
                );
            }
        }
        assert_eq!(
            steps(MachInst::new(M::LdpRI, vec![p(first), p(second), p(X1)])).len(),
            2
        );
        for duplicate in [first, zero] {
            refused(
                MachInst::new(M::LdpRI, vec![p(duplicate), p(duplicate), p(X1), O::Imm(0)]),
                "load-pair destinations repeat",
            );
        }
        for offset in [-65 * i64::from(width), 64 * i64::from(width), 1] {
            refused(
                MachInst::new(M::LdpRI, vec![p(first), p(second), p(X1), O::Imm(offset)]),
                "load-pair signed scaled displacement",
            );
        }
    }
}

#[test]
fn scalar_arithmetic_uses_existing_semantics_and_full_x_w_zeroing() {
    for (dst, a, b, c, bits) in [(W0, W1, W2, W3, 32), (X0, X1, X2, X3, 64)] {
        for values in [
            [7, 3, 4, 5],
            [u64::MAX, u64::MAX, 2, 3],
            [0, 0x8000_0000_0000_0000, 2, u64::MAX],
        ] {
            let effect = steps(MachInst::new(M::Madd, vec![p(dst), p(a), p(b), p(c)]));
            let Step::Scalar {
                destination: Some(0),
                value,
                flags: None,
            } = &effect[0]
            else {
                panic!("MADD")
            };
            let mask = if bits == 32 {
                u64::from(u32::MAX)
            } else {
                u64::MAX
            };
            assert_eq!(value.try_bv_width().unwrap(), 64);
            assert_eq!(
                eval(value, values),
                values[1].wrapping_mul(values[2]).wrapping_add(values[3]) & mask
            );
            for shift in [1, bits - 1] {
                let effect = steps(MachInst::new(
                    M::AddRRShift,
                    vec![p(dst), p(a), p(b), O::Imm(i64::from(shift))],
                ));
                let Step::Scalar {
                    value, flags: None, ..
                } = &effect[0]
                else {
                    panic!("shifted ADD")
                };
                assert_eq!(
                    eval(value, values),
                    values[1].wrapping_add(values[2].wrapping_shl(shift)) & mask
                );
            }
        }
    }
    for dst in [W0, X0, WZR, XZR] {
        for source in [W1, X1, WZR, XZR] {
            let effect = steps(MachInst::new(M::Uxtw, vec![p(dst), p(source)]));
            let Step::Scalar {
                destination,
                value,
                flags: None,
            } = &effect[0]
            else {
                panic!("UXTW")
            };
            assert_eq!(
                *destination,
                if dst == WZR || dst == XZR {
                    None
                } else {
                    Some(0)
                }
            );
            assert_eq!(
                eval(value, [0, 0xffff_ffff_8000_0001, 0, 0]),
                if source == WZR || source == XZR {
                    0
                } else {
                    0x8000_0001
                }
            );
        }
    }
    for inst in [
        MachInst::new(M::Madd, vec![p(X0), p(X1), p(X2), p(X3)]),
        MachInst::new(M::Uxtw, vec![p(X0), p(X1)]),
        MachInst::new(M::AddRRShift, vec![p(X0), p(X1), p(X2), O::Imm(2)]),
        MachInst::new(M::StrRI, vec![p(X0), p(X1), O::Imm(0)]),
    ] {
        assert!(matches!(
            adapt(&machine(vec![inst])),
            Err(ReadOnlyTargetError::Machine(_))
        ));
    }
}

#[test]
fn malformed_new_shapes_carriers_displacements_and_metadata_stay_refused() {
    for inst in [
        MachInst::new(M::LdrRI, vec![p(W0), p(X1), O::Imm(257)]),
        MachInst::new(M::StrRI, vec![p(X0), p(X1), O::Imm(32768)]),
        MachInst::new(M::LdrRI, vec![p(X0), p(W1), O::Imm(0)]),
        MachInst::new(M::StrRI, vec![p(W0), p(XZR), O::Imm(0)]),
    ] {
        refused(inst, "unsupported scalar immediate memory shape");
    }
    for mode in [-1, 0, 3, 8, 16, i64::MAX] {
        refused(
            MachInst::new(M::LdrRO, vec![p(X0), p(X1), p(X2), O::Imm(mode)]),
            "unsupported scalar register memory shape",
        );
    }
    for mode in [6, 7, 14, 15] {
        refused(
            MachInst::new(M::StrRO, vec![p(W0), p(X1), p(W2), O::Imm(mode)]),
            "full-width memory index requires X or known zero",
        );
    }
    refused(
        MachInst::new(M::LdpRI, vec![p(W0), p(X1), p(X2), O::Imm(0)]),
        "load-pair transfer widths differ",
    );
    for source in [
        p(X18),
        O::Special(SpecialReg::SP),
        O::VReg(VReg::new(0, RegClass::Gpr64)),
    ] {
        let reason = if matches!(source, O::PReg(_)) {
            "reserved or noninteger physical register"
        } else {
            "fully allocated caller integer carrier required"
        };
        refused(
            MachInst::new(M::Madd, vec![p(X0), source, p(X2), p(X3)]),
            reason,
        );
    }
    for inst in [
        MachInst::new(M::Madd, vec![p(X0), p(W1), p(X2), p(X3)]),
        MachInst::new(M::AddRRShift, vec![p(W0), p(W1), p(X2), O::Imm(1)]),
    ] {
        refused(inst, "mixed register widths");
    }
    for (dst, src, bits) in [(W0, W1, 32), (X0, X1, 64)] {
        for shift in [-1, 0, bits, 64] {
            refused(
                MachInst::new(M::AddRRShift, vec![p(dst), p(src), p(src), O::Imm(shift)]),
                "unsupported scalar-memory arithmetic shape",
            );
        }
    }
    for baseline in [
        MachInst::new(M::LdrRI, vec![p(W0), p(X1), O::Imm(0)]),
        MachInst::new(M::StrRO, vec![p(W0), p(X1), p(X2), O::Imm(7)]),
        MachInst::new(M::LdpRI, vec![p(W0), p(W1), p(X2), O::Imm(0)]),
        MachInst::new(M::Madd, vec![p(X0), p(X1), p(X2), p(X3)]),
    ] {
        for mutation in 0..4 {
            let mut inst = baseline.clone();
            match mutation {
                0 => {
                    inst.flags |= InstFlags::HAS_SIDE_EFFECTS
                        | InstFlags::READS_MEMORY
                        | InstFlags::WRITES_MEMORY
                }
                1 => inst.implicit_defs = &[NZCV],
                2 => inst.implicit_uses = &[X3],
                3 => inst.proof = Some(ProofAnnotation::InBounds),
                _ => unreachable!(),
            }
            refused(inst, "noncanonical effects/implicit operands/proof");
        }
        let mut extra = baseline;
        extra.operands.push(O::Imm(99));
        assert!(matches!(
            adapt_profile(&machine(vec![extra]), Profile::ScalarMemory),
            Err(ReadOnlyTargetError::Machine(_))
        ));
    }
}

#[test]
fn scalar_profile_does_not_bypass_complete_arena_ownership_or_old_effect_refusals() {
    for inst in [
        MachInst::new(M::StrRI, vec![p(W0), p(X1), O::Imm(0)]),
        MachInst::new(M::LdpRI, vec![p(W0), p(W1), p(X2), O::Imm(0)]),
        MachInst::new(M::Madd, vec![p(X0), p(X1), p(X2), p(X3)]),
    ] {
        let mut orphan = machine(vec![]);
        orphan.push_inst(inst.clone());
        assert_eq!(
            adapt_profile(&orphan, Profile::ScalarMemory).err(),
            Some(invalid("unowned non-inert instruction"))
        );
        let mut shared = machine(vec![inst]);
        let first = shared.blocks[0].insts[0];
        shared.blocks[0].insts.insert(1, first);
        assert_eq!(
            adapt_profile(&shared, Profile::ScalarMemory).err(),
            Some(invalid("instruction has duplicate live ownership"))
        );
    }
    for opcode in [M::StrPreIndex, M::LdrPostIndex, M::StpRI] {
        assert!(matches!(
            adapt_profile(
                &machine(vec![MachInst::new(opcode, vec![p(X0), p(X1), O::Imm(0)])]),
                Profile::ScalarMemory
            ),
            Err(ReadOnlyTargetError::Machine(_))
        ));
    }
}
