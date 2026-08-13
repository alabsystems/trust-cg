// trust-cg-opt - AND+CMP -> TST fusion tests
//
// The negative controls are the point of this file. The rewrite itself is
// trivial; what makes it safe is refusing to fire when any flag consumer can
// observe C, because ANDS clears C while SUBS #0 sets it.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use trust_cg_ir::{BlockId, RegClass, Signature, VReg};

fn vreg64(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}

fn vreg32(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
}

fn imm(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}

/// AND t,s,#m ; CMP t,#0 ; <consumer> ; <flag killer>
fn seq_with(consumer: MachInst, mask: i64) -> (MachFunction, BlockId) {
    single_block_func(vec![
        MachInst::new(AArch64Opcode::AndRI, vec![vreg64(2), vreg64(0), imm(mask)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(2), imm(0)]),
        consumer,
        // Kills the flags inside the block so `flags_safe_after` terminates
        // without needing successors.
        MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(9), imm(3)]),
    ])
}

fn single_block_func(insts: Vec<MachInst>) -> (MachFunction, BlockId) {
    let mut func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    for i in insts {
        let id = func.push_inst(i);
        func.append_inst(entry, id);
    }
    (func, entry)
}

/// CSINC d, a, b, <cond> — cond is operand 3.
fn csinc(cond: i64) -> MachInst {
    MachInst::new(
        AArch64Opcode::Csinc,
        vec![vreg64(5), vreg64(6), vreg64(7), imm(cond)],
    )
}

const EQ: i64 = 0b0000;
const NE: i64 = 0b0001;
const HS: i64 = 0b0010;
const LO: i64 = 0b0011;
const HI: i64 = 0b1000;
const LS: i64 = 0b1001;
const GE: i64 = 0b1010;

fn fused(func: &MachFunction) -> bool {
    func.block_order.iter().any(|&b| {
        func.block(b)
            .insts
            .iter()
            .any(|&i| func.inst(i).opcode == AArch64Opcode::Tst)
    })
}

#[test]
fn fuses_when_consumer_does_not_read_carry() {
    for cond in [EQ, NE, GE] {
        let (mut func, _) = seq_with(csinc(cond), 1);
        let mut pass = AndCmpFuse;
        assert!(pass.run(&mut func), "cond {cond:#06b} should fuse");
        assert!(fused(&func), "cond {cond:#06b}: expected a Tst");
    }
}

/// THE CRITICAL NEGATIVE CONTROL. ANDS clears C, SUBS #0 sets it, so any
/// consumer reading C would see a different value after the rewrite.
#[test]
fn refuses_when_consumer_reads_carry() {
    for cond in [HS, LO, HI, LS] {
        let (mut func, _) = seq_with(csinc(cond), 1);
        let mut pass = AndCmpFuse;
        pass.run(&mut func);
        assert!(
            !fused(&func),
            "cond {cond:#06b} READS C — fusing here is a miscompile"
        );
    }
}

/// `Bcc` is the LLVM-style alias of `BCond` and consumes the same NZCV state.
/// Missing the alias from the guard would let a carry-reading branch observe
/// C=0 after TST where the original CMP #0 produced C=1.
#[test]
fn bcc_alias_observes_the_same_carry_guard_as_bcond() {
    for (cond, should_fuse) in [
        (EQ, true),
        (HS, false),
        (LO, false),
        (HI, false),
        (LS, false),
    ] {
        let branch = MachInst::new(AArch64Opcode::Bcc, vec![imm(cond), imm(4)]);
        let (mut func, _) = seq_with(branch, 1);
        let mut pass = AndCmpFuse;
        pass.run(&mut func);
        assert_eq!(
            fused(&func),
            should_fuse,
            "Bcc condition {cond:#06b} has the wrong carry-safety classification"
        );
    }
}

/// ADC/SBC consume C arithmetically and carry no condition code, so they must
/// be rejected outright rather than inspected for a safe condition.
#[test]
fn refuses_when_consumer_is_adc_or_sbc() {
    for opcode in [AArch64Opcode::Adc, AArch64Opcode::Sbc] {
        let (mut func, _) = seq_with(
            MachInst::new(opcode, vec![vreg64(5), vreg64(6), vreg64(7)]),
            1,
        );
        let mut pass = AndCmpFuse;
        pass.run(&mut func);
        assert!(!fused(&func), "{opcode:?} reads C directly — must not fuse");
    }
}

/// Flags live out of the block with no successor killing them first.
#[test]
fn refuses_when_flags_escape_the_block() {
    let (mut func, _) = single_block_func(vec![
        MachInst::new(AArch64Opcode::AndRI, vec![vreg64(2), vreg64(0), imm(1)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(2), imm(0)]),
        // no consumer, no flag killer, block just ends
    ]);
    let mut pass = AndCmpFuse;
    pass.run(&mut func);
    assert!(
        !fused(&func),
        "flags may be live-out; cannot prove no C reader downstream"
    );
}

/// A conditional branch names only its taken target in the instruction; the
/// authoritative CFG also contains the fallthrough. Ignoring that edge would
/// miss the HS consumer and silently change C from 1 (CMP #0) to 0 (TST).
#[test]
fn refuses_when_carry_reader_is_on_cfg_only_fallthrough_edge() {
    let mut func = MachFunction::new("cfg_fallthrough".into(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    let safe = func.create_block();
    let carry_reader = func.create_block();

    for inst in [
        MachInst::new(AArch64Opcode::AndRI, vec![vreg64(2), vreg64(0), imm(1)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(2), imm(0)]),
        // Only the taken target is explicit. `carry_reader` is the CFG-only
        // fallthrough edge.
        MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(EQ), MachOperand::Block(safe)],
        ),
    ] {
        let id = func.push_inst(inst);
        func.append_inst(entry, id);
    }
    for (block, insts) in [
        (
            safe,
            vec![
                MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(9), imm(3)]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        ),
        (
            carry_reader,
            vec![
                csinc(HS),
                MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(9), imm(3)]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        ),
    ] {
        for inst in insts {
            let id = func.push_inst(inst);
            func.append_inst(block, id);
        }
    }
    func.add_edge(entry, safe);
    func.add_edge(entry, carry_reader);

    let mut pass = AndCmpFuse;
    pass.run(&mut func);
    assert!(
        !fused(&func),
        "the CFG-only fallthrough reads C and must block fusion"
    );
}

#[test]
fn refuses_when_masked_value_has_other_uses() {
    let (mut func, _) = single_block_func(vec![
        MachInst::new(AArch64Opcode::AndRI, vec![vreg64(2), vreg64(0), imm(1)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(2), imm(0)]),
        csinc(EQ),
        // second reader of t: the AND result is live, so it must be kept
        MachInst::new(AArch64Opcode::AddRR, vec![vreg64(8), vreg64(2), vreg64(3)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(9), imm(3)]),
    ]);
    let mut pass = AndCmpFuse;
    pass.run(&mut func);
    assert!(!fused(&func), "t is multi-use; AND must survive");
}

/// MOVK preserves all destination bits outside its inserted halfword, so its
/// operand zero is a real use as well as a def. A destination-only liveness
/// scan would miss this and delete the AND value that MOVK consumes.
#[test]
fn refuses_when_masked_value_is_used_by_tied_def_use() {
    let (mut func, _) = single_block_func(vec![
        MachInst::new(AArch64Opcode::AndRI, vec![vreg64(2), vreg64(0), imm(1)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(2), imm(0)]),
        csinc(EQ),
        MachInst::new(AArch64Opcode::Movk, vec![vreg64(2), imm(7), imm(0)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(9), imm(3)]),
    ]);
    let mut pass = AndCmpFuse;
    pass.run(&mut func);
    assert!(!fused(&func), "MOVK reads t through its tied def-use");
}

/// LSE RMW atomics define the old-value result at operand 1, not operand 0.
/// Moving the TST read of `src` across that definition would test a different
/// value, so the shared operand-role table must see and reject it.
#[test]
fn refuses_when_source_is_redefined_at_nonzero_def_operand() {
    let (mut func, _) = single_block_func(vec![
        MachInst::new(AArch64Opcode::AndRI, vec![vreg64(2), vreg64(0), imm(1)]),
        MachInst::new(AArch64Opcode::Ldadd, vec![vreg64(7), vreg64(0), vreg64(8)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(2), imm(0)]),
        csinc(EQ),
        MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(9), imm(3)]),
    ]);
    let mut pass = AndCmpFuse;
    pass.run(&mut func);
    assert!(
        !fused(&func),
        "operand-1 LSE destination redefines the TST source"
    );
}

#[test]
fn refuses_cross_width_and_cmp_pair() {
    let (mut func, _) = single_block_func(vec![
        MachInst::new(AArch64Opcode::AndRI, vec![vreg32(2), vreg64(0), imm(1)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![vreg32(2), imm(0)]),
        MachInst::new(AArch64Opcode::CSet, vec![vreg32(5), imm(EQ)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(9), imm(3)]),
    ]);
    let mut pass = AndCmpFuse;
    pass.run(&mut func);
    assert!(!fused(&func), "malformed cross-width pair must fail closed");
}

#[test]
fn refuses_when_compare_immediate_is_nonzero() {
    let (mut func, _) = single_block_func(vec![
        MachInst::new(AArch64Opcode::AndRI, vec![vreg64(2), vreg64(0), imm(1)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(2), imm(1)]),
        csinc(EQ),
        MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(9), imm(3)]),
    ]);
    let mut pass = AndCmpFuse;
    pass.run(&mut func);
    assert!(!fused(&func), "TST only implements a compare against zero");
}

#[test]
fn refuses_unencodable_mask() {
    // 0 and all-ones have no logical-immediate encoding.
    for bad in [0i64, -1] {
        let (mut func, _) = seq_with(csinc(EQ), bad);
        let mut pass = AndCmpFuse;
        pass.run(&mut func);
        assert!(!fused(&func), "mask {bad:#x} is not encodable as TST #imm");
    }
}

#[test]
fn logical_immediate_acceptance_matches_expectation() {
    // Encodable: single bits, byte masks, repeating patterns, rotations.
    for m in [1i64, 2, 0xFF, 0xFFFF, 0x5555_5555_5555_5555, i64::MIN, 0xF0] {
        assert!(is_logical_immediate(m, 64), "{m:#x} should be encodable");
    }
    // Not encodable: zero and all-ones.
    assert!(!is_logical_immediate(0, 64));
    assert!(!is_logical_immediate(-1, 64));
}

#[test]
fn carry_reading_condition_set_is_exactly_hs_lo_hi_ls() {
    for c in 0..16i64 {
        let expected = matches!(c, 0b0010 | 0b0011 | 0b1000 | 0b1001);
        assert_eq!(cond_reads_carry(c), expected, "cond {c:#06b}");
    }
}
