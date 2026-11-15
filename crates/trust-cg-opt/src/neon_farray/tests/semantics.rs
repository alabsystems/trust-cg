//! Semantic admission controls. The guard evaluator below checks path selection,
//! not native execution or the semantics of the vector body.
use super::*;

fn negate(
    func: &mut MachFunction,
    source: MachOperand,
    dest: MachOperand,
    consumer: AArch64Opcode,
) {
    let id = func
        .insts
        .iter()
        .position(|inst| inst.opcode == consumer && inst.operands.contains(&source))
        .expect("consumer");
    let id = InstId(u32::try_from(id).unwrap());
    let block = block_of_inst(func, id).unwrap();
    for operand in &mut func.inst_mut(id).operands {
        if *operand == source {
            *operand = dest.clone();
        }
    }
    let neg = func.push_inst(MachInst::new(AArch64Opcode::FnegRR, vec![dest, source]));
    let body = &mut func.block_mut(block).insts;
    let pos = body.iter().position(|&inst| inst == id).unwrap();
    body.insert(pos, neg);
}

#[test]
fn reduction_in_loop_negation_requires_exact_lowering() {
    for widen in [false, true] {
        let mut func = build_loop(Kind::PlainSum, 1, if widen { 4 } else { 8 }, widen, false);
        negate(&mut func, f(23), f(150), AArch64Opcode::FaddRR);
        for full in [false, true] {
            let mut func = func.clone();
            let mut pass = if full {
                NeonFArrayPass::new()
            } else {
                NeonFArrayPass::default()
            };
            crate::candidate::tests::support::assert_refusal(&mut func, |func| pass.run(func));
            assert_eq!(pass.fired(), 0);
        }
    }
}

#[test]
fn fill_in_loop_negation_requires_exact_lowering() {
    let mut func = build_fill(false, false, false, 100, false, false);
    negate(&mut func, s(7), s(150), AArch64Opcode::StrRI);
    crate::candidate::tests::support::assert_refusal(&mut func, |func| {
        NeonFArrayPass::default().run(func)
    });
    // The old zero-minus lowering loses the sign required for the j=0 lane.
    assert_ne!((0.0_f32 - 0.0_f32).to_bits(), (-0.0_f32).to_bits());
}

#[test]
fn repeated_store_base_must_not_advance_one_pointer_twice() {
    let mut func = build_fill(true, true, false, 100, false, false);
    let address = func
        .insts
        .iter_mut()
        .find(|inst| inst.opcode == AArch64Opcode::Madd && inst.operands.first() == Some(&g(24)))
        .unwrap();
    address.operands[3] = g(1);
    crate::candidate::tests::support::assert_refusal(&mut func, |func| {
        NeonFArrayPass::default().run(func)
    });
}

fn value(operand: &MachOperand, regs: &HashMap<u32, u64>) -> u64 {
    match operand {
        MachOperand::VReg(v) => *regs.get(&v.id).expect("defined GPR"),
        MachOperand::Imm(i) => *i as u64,
        other => panic!("not a value: {other:?}"),
    }
}

fn setup(inst: &MachInst, regs: &mut HashMap<u32, u64>) {
    use AArch64Opcode::*;
    let ops = &inst.operands;
    let result = match inst.opcode {
        Movz => value(&ops[1], regs),
        Madd => value(&ops[1], regs)
            .wrapping_mul(value(&ops[2], regs))
            .wrapping_add(value(&ops[3], regs)),
        SubRI => value(&ops[1], regs).wrapping_sub(value(&ops[2], regs)),
        AddRR => value(&ops[1], regs).wrapping_add(value(&ops[2], regs)),
        LslRI => value(&ops[1], regs) << value(&ops[2], regs),
        // These operations cannot change GPRs or control flow in this fixture.
        FmovGprFpr | NeonDupGen | NeonDupElem | NeonMovi | NeonInsGen | NeonAddV => return,
        other => panic!("unmodeled setup opcode: {other:?}"),
    };
    let dest = ops[0].as_vreg().unwrap();
    assert_eq!(dest.class, RegClass::Gpr64);
    regs.insert(dest.id, result);
}

fn selects_vector(
    func: &MachFunction,
    original: &MachFunction,
    start: i64,
    base_x: u64,
    base_y: u64,
    base_z: u64,
) -> bool {
    use AArch64Opcode::*;
    // Existing fixture's scalar setup is represented by the supplied live-ins.
    let mut regs = HashMap::from_iter([(1, base_x), (2, base_y), (55, base_z), (10, start as u64)]);
    for &id in &func.block(func.entry).insts {
        if id.0 as usize >= original.insts.len() {
            setup(func.inst(id), &mut regs);
        }
    }
    let mut at = branch_targets(func.inst(*func.block(func.entry).insts.last().unwrap()))[0];
    let mut comparison = None;
    for _ in 0..32 {
        if (at.0 as usize) < original.blocks.len() {
            return false;
        }
        let mut target = None;
        for &id in &func.block(at).insts {
            let inst = func.inst(id);
            let ops = &inst.operands;
            match inst.opcode {
                NeonStpQPost => return true,
                CmpRI | CmpRR => comparison = Some((value(&ops[0], &regs), value(&ops[1], &regs))),
                BCond => {
                    let (a, b) = comparison.expect("dominating compare");
                    let taken = match value(&ops[0], &regs) as i64 {
                        CC_LT => (a as i64) < (b as i64),
                        CC_LS => a <= b,
                        cc => panic!("unmodeled condition {cc}"),
                    };
                    if taken {
                        target = Some(branch_targets(inst)[0]);
                        break;
                    }
                }
                B => {
                    target = Some(branch_targets(inst)[0]);
                    break;
                }
                // Reaching the vector body's convert is sufficient; it is not executed.
                NeonUcvtfV | NeonScvtfV => return true,
                _ => setup(inst, &mut regs),
            }
        }
        at = target.expect("explicit terminator");
    }
    panic!("guard path did not terminate");
}

#[test]
fn alias_guards_cover_actual_start_for_negative_and_positive_indices() {
    let mut original = build_fill(true, true, false, 12, false, false);
    // Make the initial induction a live-in rather than the builder's zero.
    let iv_init = original
        .insts
        .iter_mut()
        .find(|inst| inst.opcode == AArch64Opcode::MovR && inst.operands.first() == Some(&g(10)))
        .unwrap();
    iv_init.operands[1] = g(84);
    let mut func = original.clone();
    assert!(NeonFArrayPass::default().run(&mut func));
    let mut checked = 0;
    for start in [-8_i64, -1, 0, 4] {
        for delta in (-80_i64..=80).step_by(4) {
            let x = 1000_i64;
            let y = x + delta;
            let disjoint = x + 12 * 4 <= y + start * 4 || y + 12 * 4 <= x + start * 4;
            assert_eq!(
                selects_vector(&func, &original, start, x as u64, y as u64, 2000),
                disjoint,
                "start={start}, delta={delta}: ranges must include the actual first address"
            );
            checked += 1;
        }
    }
    assert_eq!(checked, 164);
}

#[test]
fn alias_guards_check_every_pair_with_three_streams() {
    let mut original = super::candidate::three_stream_fill();
    let iv_init = original
        .insts
        .iter_mut()
        .find(|inst| inst.opcode == AArch64Opcode::MovR && inst.operands.first() == Some(&g(10)))
        .unwrap();
    iv_init.operands[1] = g(84);
    let mut func = original.clone();
    assert!(NeonFArrayPass::default().run(&mut func));
    for start in [-8_i64, 0, 4] {
        for bases in [
            [1000_i64, 1200, 1400],
            [1000, 1004, 1400],
            [1000, 1200, 1004],
            [1000, 1200, 1204],
            [1000, 1032, 1064],
        ] {
            let disjoint = (0..3).all(|i| {
                ((i + 1)..3).all(|j| {
                    bases[i] + 48 <= bases[j] + start * 4 || bases[j] + 48 <= bases[i] + start * 4
                })
            });
            assert_eq!(
                selects_vector(
                    &func,
                    &original,
                    start,
                    bases[0] as u64,
                    bases[1] as u64,
                    bases[2] as u64
                ),
                disjoint,
                "start={start}, bases={bases:?}"
            );
        }
    }
}
