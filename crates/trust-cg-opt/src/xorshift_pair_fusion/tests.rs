// trust-cg-opt - xorshift pair fusion unit tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use trust_cg_ir::{MachInst, MachOperand as MO, Signature};

fn g64(id: u32) -> VReg {
    VReg::new(id, RegClass::Gpr64)
}
fn g32(id: u32) -> VReg {
    VReg::new(id, RegClass::Gpr32)
}
fn push(func: &mut MachFunction, b: BlockId, inst: MachInst) -> InstId {
    let id = func.push_inst(inst);
    func.append_inst(b, id);
    id
}
fn step(op: AArch64Opcode, d: VReg, s: VReg, k: i64) -> MachInst {
    MachInst::new(op, vec![MO::VReg(d), MO::VReg(s), MO::VReg(s), MO::Imm(k)])
}

/// The ARM ARM semantics of the four 64-bit opcodes the rewrite reads and
/// writes, written independently of the pass: `EOR Xd, Xn, Xm, LSL/LSR #k`,
/// `EOR Xd, Xn, Xm` and `UBFM Xd, Xn, #immr, #imms` (`DecodeBitMasks` with
/// `N = 1`: `imms >= immr` extracts bits `[immr, imms]` to the bottom,
/// otherwise the low `imms + 1` bits move up to `64 - immr`).
fn eval(func: &MachFunction, block: BlockId, regs: &mut HashMap<VReg, u64>) {
    for &id in &func.block(block).insts {
        let inst = func.inst(id);
        let r = |regs: &HashMap<VReg, u64>, i: usize| match inst.operands[i] {
            MO::VReg(v) => regs[&v],
            _ => panic!("register operand"),
        };
        let imm = |i: usize| match inst.operands[i] {
            MO::Imm(v) => v,
            _ => panic!("immediate operand"),
        };
        let value = match inst.opcode {
            AArch64Opcode::EorRRLsl => r(regs, 1) ^ (r(regs, 2) << imm(3)),
            AArch64Opcode::EorRRLsr => r(regs, 1) ^ (r(regs, 2) >> imm(3)),
            AArch64Opcode::EorRR => r(regs, 1) ^ r(regs, 2),
            AArch64Opcode::Ubfm => {
                let (immr, imms, x) = (imm(2) as u32, imm(3) as u32, r(regs, 1));
                let mask = |w: u32| if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
                if imms >= immr {
                    (x >> immr) & mask(imms - immr + 1)
                } else {
                    (x & mask(imms + 1)) << (64 - immr)
                }
            }
            AArch64Opcode::AddRI => r(regs, 1).wrapping_add(imm(2) as u64),
            AArch64Opcode::MovR => r(regs, 1),
            AArch64Opcode::B | AArch64Opcode::BCond | AArch64Opcode::CmpRR => continue,
            other => panic!("unexpected opcode {other:?}"),
        };
        let MO::VReg(d) = inst.operands[0] else {
            panic!("register destination")
        };
        regs.insert(d, value);
    }
}

/// `x` is the loop's carried state: the p1 xorshift loop
///
/// ```text
///   bb0: x=MovR seed ; B header
///   bb1 header: CmpRR i, n ; BCond LO body ; B exit
///   bb2 body:   t=x^(x<<a) ; y=t^(t>>b) ; z=y^(y<<c) ; i+=1 ; x=MovR z ; B header
///   bb3 exit:   Ret
/// ```
///
/// Returns `(func, body, y_step)`.
fn xorshift_loop(a: i64, b: i64, c: i64) -> (MachFunction, BlockId, InstId) {
    let mut f = MachFunction::new("p1".into(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    let header = f.create_block();
    let body = f.create_block();
    let exit = f.create_block();
    let (seed, x, t, y, z, i, n) = (g64(1), g64(2), g64(3), g64(4), g64(5), g64(6), g64(7));
    push(
        &mut f,
        entry,
        MachInst::new(AArch64Opcode::MovR, vec![MO::VReg(x), MO::VReg(seed)]),
    );
    push(
        &mut f,
        entry,
        MachInst::new(AArch64Opcode::B, vec![MO::Block(header)]),
    );
    push(
        &mut f,
        header,
        MachInst::new(AArch64Opcode::CmpRR, vec![MO::VReg(i), MO::VReg(n)]),
    );
    push(
        &mut f,
        header,
        MachInst::new(AArch64Opcode::BCond, vec![MO::Imm(3), MO::Block(body)]),
    );
    push(
        &mut f,
        header,
        MachInst::new(AArch64Opcode::B, vec![MO::Block(exit)]),
    );
    push(&mut f, body, step(AArch64Opcode::EorRRLsl, t, x, a));
    let y_step = push(&mut f, body, step(AArch64Opcode::EorRRLsr, y, t, b));
    push(&mut f, body, step(AArch64Opcode::EorRRLsl, z, y, c));
    push(
        &mut f,
        body,
        MachInst::new(
            AArch64Opcode::AddRI,
            vec![MO::VReg(i), MO::VReg(i), MO::Imm(1)],
        ),
    );
    push(
        &mut f,
        body,
        MachInst::new(AArch64Opcode::MovR, vec![MO::VReg(x), MO::VReg(z)]),
    );
    push(
        &mut f,
        body,
        MachInst::new(AArch64Opcode::B, vec![MO::Block(header)]),
    );
    push(&mut f, exit, MachInst::new(AArch64Opcode::Ret, vec![]));
    f.add_edge(entry, header);
    f.add_edge(header, body);
    f.add_edge(header, exit);
    f.add_edge(body, header);
    (f, body, y_step)
}

fn run(f: &mut MachFunction) -> bool {
    XorshiftPairFusion.run(f)
}

#[test]
fn fuses_the_xorshift64_step_pair_on_the_loop_recurrence() {
    let (mut f, body, y_step) = xorshift_loop(13, 7, 17);
    assert!(run(&mut f));
    let ops: Vec<AArch64Opcode> = f
        .block(body)
        .insts
        .iter()
        .map(|&id| f.inst(id).opcode)
        .collect();
    assert_eq!(
        ops,
        vec![
            AArch64Opcode::EorRRLsl,
            AArch64Opcode::Ubfm,
            AArch64Opcode::EorRRLsr,
            AArch64Opcode::EorRR,
            AArch64Opcode::EorRRLsl,
            AArch64Opcode::AddRI,
            AArch64Opcode::MovR,
            AArch64Opcode::B,
        ]
    );
    assert_eq!(f.inst(y_step).opcode, AArch64Opcode::EorRR);
    // `(x << 13) >> 7` is `UBFIZ x, #6, #51`: immr = 64 - 6, imms = 50.
    let ubfm = f.inst(f.block(body).insts[1]);
    assert_eq!(ubfm.operands[2], MO::Imm(58));
    assert_eq!(ubfm.operands[3], MO::Imm(50));
    // Idempotent: the rewritten step is a plain EOR.
    assert!(!run(&mut f));
}

#[test]
fn fused_steps_compute_the_same_state_for_every_shift_pair() {
    // A small deterministic generator for the inputs (xorshift itself).
    let mut s = 0x9E37_79B9_7F4A_7C15u64;
    let mut next = || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };
    for a in 1..=63 {
        for b in 1..=63 {
            let (orig, body, _) = xorshift_loop(a, b, 17);
            let mut fused = orig.clone();
            assert!(run(&mut fused), "a={a} b={b}");
            for _ in 0..8 {
                let x0 = next();
                let mut r0: HashMap<VReg, u64> = HashMap::default();
                r0.insert(g64(2), x0);
                r0.insert(g64(6), 0);
                let mut r1 = r0.clone();
                eval(&orig, body, &mut r0);
                eval(&fused, body, &mut r1);
                assert_eq!(r0[&g64(4)], r1[&g64(4)], "y: a={a} b={b} x={x0:#x}");
                assert_eq!(r0[&g64(2)], r1[&g64(2)], "next x: a={a} b={b} x={x0:#x}");
            }
        }
    }
}

#[test]
fn keeps_a_pair_outside_any_loop() {
    // The same three steps in straight-line code: no recurrence to shorten.
    let mut f = MachFunction::new("once".into(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    push(
        &mut f,
        entry,
        step(AArch64Opcode::EorRRLsl, g64(3), g64(2), 13),
    );
    push(
        &mut f,
        entry,
        step(AArch64Opcode::EorRRLsr, g64(4), g64(3), 7),
    );
    push(&mut f, entry, MachInst::new(AArch64Opcode::Ret, vec![]));
    assert!(!run(&mut f));
}

/// A named mutation of the loop body.
type Mutation = (&'static str, Box<dyn Fn(&mut MachFunction, BlockId)>);

#[test]
fn keeps_shapes_that_are_not_a_left_right_step_pair() {
    // Each mutation of the loop body is refused.
    let cases: Vec<Mutation> = vec![
        (
            "x redefined between the steps",
            Box::new(|f, body| {
                let id = f.push_inst(MachInst::new(
                    AArch64Opcode::AddRI,
                    vec![MO::VReg(g64(2)), MO::VReg(g64(2)), MO::Imm(1)],
                ));
                f.block_mut(body).insts.insert(1, id);
            }),
        ),
        (
            "t redefined between the steps",
            Box::new(|f, body| {
                let id = f.push_inst(MachInst::new(
                    AArch64Opcode::AddRI,
                    vec![MO::VReg(g64(3)), MO::VReg(g64(3)), MO::Imm(1)],
                ));
                f.block_mut(body).insts.insert(1, id);
            }),
        ),
        (
            "two-source right step",
            Box::new(|f, body| {
                let id = f.block(body).insts[1];
                f.inst_mut(id).operands[2] = MO::VReg(g64(9));
            }),
        ),
        (
            "two-source left step",
            Box::new(|f, body| {
                let id = f.block(body).insts[0];
                f.inst_mut(id).operands[2] = MO::VReg(g64(9));
            }),
        ),
        (
            "the left step overwrites its own source",
            Box::new(|f, body| {
                let id = f.block(body).insts[0];
                f.inst_mut(id).operands[0] = MO::VReg(g64(2));
                let y = f.block(body).insts[1];
                f.inst_mut(y).operands[1] = MO::VReg(g64(2));
                f.inst_mut(y).operands[2] = MO::VReg(g64(2));
            }),
        ),
        (
            "right then left (no single bitfield move)",
            Box::new(|f, body| {
                let l = f.block(body).insts[0];
                f.inst_mut(l).opcode = AArch64Opcode::EorRRLsr;
                let r = f.block(body).insts[1];
                f.inst_mut(r).opcode = AArch64Opcode::EorRRLsl;
                // A third step right after the left one would form a new
                // left-right pair; keep it a left step.
            }),
        ),
        (
            "32-bit registers",
            Box::new(|f, body| {
                for pos in 0..3 {
                    let id = f.block(body).insts[pos];
                    for op in f.inst_mut(id).operands.iter_mut() {
                        if let MO::VReg(v) = op {
                            *op = MO::VReg(g32(v.id));
                        }
                    }
                }
            }),
        ),
        (
            "a shift of 64",
            Box::new(|f, body| {
                let id = f.block(body).insts[0];
                f.inst_mut(id).operands[3] = MO::Imm(64);
            }),
        ),
    ];
    for (what, mutate) in cases {
        let (mut f, body, _) = xorshift_loop(13, 7, 17);
        mutate(&mut f, body);
        let before = f.block(body).insts.clone();
        assert!(!run(&mut f), "{what}");
        assert_eq!(f.block(body).insts, before, "{what}");
    }
}

#[test]
fn keeps_a_loop_that_does_not_define_the_shifted_value() {
    // x is defined only before the loop: the steps recompute the same value
    // every iteration and are not on a recurrence.
    let (mut f, body, _) = xorshift_loop(13, 7, 17);
    let wb = f.block(body).insts[4];
    f.inst_mut(wb).operands[0] = MO::VReg(g64(8));
    assert!(!run(&mut f));
}

#[test]
fn fuses_a_left_step_whose_shifted_operand_is_a_copy_of_the_state() {
    // `c = MovR x ; t = EorRRLsl t, x, c, #13`: the lowering's copy of the
    // carried state (b1_mispredict, p6_branch_match).
    let (mut f, body, y_step) = xorshift_loop(13, 7, 17);
    let left = f.block(body).insts[0];
    f.inst_mut(left).operands[2] = MO::VReg(g64(9));
    let copy = f.push_inst(MachInst::new(
        AArch64Opcode::MovR,
        vec![MO::VReg(g64(9)), MO::VReg(g64(2))],
    ));
    f.block_mut(body).insts.insert(0, copy);
    let orig = f.clone();
    assert!(run(&mut f));
    assert_eq!(f.inst(y_step).opcode, AArch64Opcode::EorRR);
    let mut s = 0x2545_F491_4F6C_DD1Du64;
    for _ in 0..64 {
        s = s.rotate_left(17) ^ 0x9E37_79B9_7F4A_7C15;
        let mut r0: HashMap<VReg, u64> = HashMap::default();
        r0.insert(g64(2), s);
        r0.insert(g64(6), 0);
        let mut r1 = r0.clone();
        eval(&orig, body, &mut r0);
        eval(&f, body, &mut r1);
        assert_eq!(r0[&g64(2)], r1[&g64(2)]);
    }
}

#[test]
fn keeps_a_left_step_whose_copy_is_stale() {
    // The copy was taken, then the state changed: `c` no longer equals `x`.
    let (mut f, body, _) = xorshift_loop(13, 7, 17);
    let left = f.block(body).insts[0];
    f.inst_mut(left).operands[2] = MO::VReg(g64(9));
    let copy = f.push_inst(MachInst::new(
        AArch64Opcode::MovR,
        vec![MO::VReg(g64(9)), MO::VReg(g64(2))],
    ));
    let bump = f.push_inst(MachInst::new(
        AArch64Opcode::AddRI,
        vec![MO::VReg(g64(2)), MO::VReg(g64(2)), MO::Imm(1)],
    ));
    f.block_mut(body).insts.splice(0..0, [copy, bump]);
    assert!(!run(&mut f));
}

#[test]
fn fuses_every_lane_of_an_unrolled_recurrence() {
    // Two verbatim lanes (`scalar-unroll` SERIAL mode): lane 1's state is
    // lane 0's result, a register defined in the loop but not carried.
    let (mut f, body, _) = xorshift_loop(13, 7, 17);
    let (t1, y1, z1) = (g64(30), g64(31), g64(32));
    let lane1 = [
        f.push_inst(step(AArch64Opcode::EorRRLsl, t1, g64(5), 13)),
        f.push_inst(step(AArch64Opcode::EorRRLsr, y1, t1, 7)),
        f.push_inst(step(AArch64Opcode::EorRRLsl, z1, y1, 17)),
    ];
    f.block_mut(body).insts.splice(3..3, lane1);
    let wb = f.block(body).insts[7];
    f.inst_mut(wb).operands[1] = MO::VReg(z1);
    let orig = f.clone();
    assert!(run(&mut f));
    let fused = f
        .block(body)
        .insts
        .iter()
        .filter(|&&id| f.inst(id).opcode == AArch64Opcode::Ubfm)
        .count();
    assert_eq!(fused, 2, "both lanes");
    let mut r0: HashMap<VReg, u64> = HashMap::default();
    r0.insert(g64(2), 0x0123_4567_89AB_CDEF);
    r0.insert(g64(6), 0);
    let mut r1 = r0.clone();
    eval(&orig, body, &mut r0);
    eval(&f, body, &mut r1);
    assert_eq!(r0[&g64(2)], r1[&g64(2)]);
}

#[test]
fn keeps_a_pair_whose_state_is_clobbered_through_its_32_bit_view() {
    // `w2 = AddRI w2, #1` between the steps writes x's numeric ID through
    // the W view (zero-extending into X): `u` would read a different `x`
    // than `t` did. The same write to another ID still fuses.
    for (id, fuses) in [(2, false), (8, true)] {
        let (mut f, body, _) = xorshift_loop(13, 7, 17);
        let clobber = f.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![MO::VReg(g32(id)), MO::VReg(g32(id)), MO::Imm(1)],
        ));
        f.block_mut(body).insts.insert(1, clobber);
        let before = f.block(body).insts.clone();
        assert_eq!(run(&mut f), fuses, "W write of id {id}");
        if !fuses {
            assert_eq!(f.block(body).insts, before);
        }
    }
}

#[test]
fn keeps_a_pair_with_metadata_beyond_its_operands() {
    use trust_cg_ir::regs::{NZCV, X0};
    use trust_cg_ir::{InstFlags, ProofAnnotation};
    // Each step, each kind of extra metadata: the original is kept whole and
    // nothing is allocated.
    for pos in [0usize, 1] {
        for mutation in 0..4 {
            let (mut f, body, _) = xorshift_loop(13, 7, 17);
            let id = f.block(body).insts[pos];
            let inst = f.inst_mut(id);
            match mutation {
                0 => inst.flags |= InstFlags::IS_PSEUDO,
                1 => inst.implicit_defs = &[NZCV],
                2 => inst.implicit_uses = &[X0],
                _ => inst.proof = Some(ProofAnnotation::InBounds),
            }
            let before = f.clone();
            assert!(!run(&mut f), "step {pos} mutation {mutation}");
            assert_eq!(format!("{f:?}"), format!("{before:?}"));
        }
    }
}

#[test]
fn keeps_a_right_step_another_block_also_links() {
    // The right step's arena entry is also linked from a block outside the
    // layout: rewriting it in place would change that block too. With the
    // extra link removed the same loop fuses.
    for shared in [true, false] {
        let (mut f, body, y_step) = xorshift_loop(13, 7, 17);
        let hidden = f.create_block();
        if shared {
            f.append_inst(hidden, y_step);
        }
        f.block_order.retain(|&b| b != hidden);
        let before = format!("{f:?}");
        assert_eq!(run(&mut f), !shared, "shared={shared}");
        if shared {
            assert_eq!(format!("{f:?}"), before);
        } else {
            assert_eq!(f.inst(y_step).opcode, AArch64Opcode::EorRR);
            assert_eq!(f.block(body).insts.len(), 8);
        }
    }
}

#[test]
fn a_counter_left_stale_before_the_pass_is_refused_not_repaired() {
    // L10-P5: at a pass boundary the pass admits the function before it
    // synchronizes the counter, so a counter left one below a live register
    // (the near miss that would issue `v7` again) is refused, not repaired.
    let (mut f, _, _) = xorshift_loop(13, 7, 17);
    f.try_sync_vreg_counter()
        .expect("fixture registers fit the counter");
    assert_eq!(f.next_vreg, 8);
    f.next_vreg = 7;
    f.require_id_admission_before_allocation();
    let before = format!("{f:?}");
    assert!(!run(&mut f));
    assert_eq!(format!("{f:?}"), before);
    assert_eq!(f.next_vreg, 7, "the counter is not repaired");
    assert!(
        matches!(
            f.id_admission_refusal(),
            Some(trust_cg_ir::MachIdAdmissionError::StaleCounter {
                domain: trust_cg_ir::MachIdDomain::VReg,
                counter: 7,
                live_id: 7,
                ..
            })
        ),
        "{:?}",
        f.id_admission_refusal()
    );

    // An admitted boundary fuses as before, allocating from the counter.
    let (mut clean, body_clean, y_clean) = xorshift_loop(13, 7, 17);
    clean
        .try_sync_vreg_counter()
        .expect("fixture registers fit the counter");
    clean.require_id_admission_before_allocation();
    assert!(run(&mut clean));
    assert_eq!(clean.id_admission_refusal(), None);
    assert_eq!(clean.next_vreg, 10);
    assert_eq!(clean.inst(y_clean).opcode, AArch64Opcode::EorRR);
    assert_eq!(clean.block(body_clean).insts.len(), 8);
}
