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

/// FCSEL d, a, b, <cond> — the scalar-FP conditional select. Its condition is
/// operand 3, exactly like CSEL/CSINC; the encoder reads `imm_val(inst, 3)`.
fn fcsel(cond: i64) -> MachInst {
    MachInst::new(
        AArch64Opcode::FcselRR,
        vec![fpr64(5), fpr64(6), fpr64(7), imm(cond)],
    )
}

fn fpr64(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Fpr64))
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

/// `FcselRR` is an NZCV reader per `effects::reads_flags`, so leaving it out of
/// `cond_operand_index` did not make the pass wrong — it made it INERT wherever
/// the flags reach a scalar-FP select. That is the whole of Misc/perlin's hot
/// loop: 16 fusible AND/CMP pairs, every one declined, worth 2.2% of the
/// program's cycles. Losing this arm again would silently cost that back.
#[test]
fn fuses_when_the_flag_consumer_is_a_scalar_fp_select() {
    for cond in [EQ, NE, GE] {
        let (mut func, _) = seq_with(fcsel(cond), 1);
        let mut pass = AndCmpFuse;
        assert!(pass.run(&mut func), "FCSEL cond {cond:#06b} should fuse");
        assert!(fused(&func), "FCSEL cond {cond:#06b}: expected a Tst");
    }
}

/// ...and the C-flag guard must still bite through the FP select.
#[test]
fn refuses_when_the_scalar_fp_select_reads_carry() {
    for cond in [HS, LO, HI, LS] {
        let (mut func, _) = seq_with(fcsel(cond), 1);
        let mut pass = AndCmpFuse;
        pass.run(&mut func);
        assert!(
            !fused(&func),
            "FCSEL cond {cond:#06b} READS C — fusing here is a miscompile"
        );
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

// ---------------------------------------------------------------------------
// The REGISTER-operand arm (`AND Rd,Rn,Rm` + `CMP Rd,#0` -> `TST Rn,Rm`).
//
// OPT-IN: `TCG_AND_CMP_FUSE_RR=1`. Default OFF because it measured at the
// instrument's null corpus-wide -- see the switch's doc comment. These tests pin
// the BEHAVIOUR so the arm cannot rot while it is parked, and pin the guard that
// the immediate arm never needed: `AndRR` has TWO source reads to move down to
// the CMP, not one.

fn rr_seq(consumer: MachInst) -> (MachFunction, BlockId) {
    single_block_func(vec![
        MachInst::new(AArch64Opcode::AndRR, vec![vreg64(2), vreg64(0), vreg64(1)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(2), imm(0)]),
        consumer,
        // trailing flag WRITER: kills the definition so `flags_safe_after`
        // is deciding on the consumer, not on flags escaping the block. Without
        // it every one of these tests would pass for the wrong reason.
        MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(9), imm(3)]),
    ])
}

fn with_rr_arm<T>(f: impl FnOnce() -> T) -> T {
    trust_cg_process_env::with_env_overrides(&[("TCG_AND_CMP_FUSE_RR", "1")], f)
}

#[test]
fn rr_arm_is_off_by_default() {
    let (mut func, _) = rr_seq(csinc(EQ));
    let mut pass = AndCmpFuse;
    assert!(
        !pass.run(&mut func),
        "register arm must be inert by default"
    );
    assert!(
        !fused(&func),
        "default build must not emit a register-form Tst"
    );
}

#[test]
fn rr_arm_fuses_when_enabled_and_no_consumer_reads_carry() {
    with_rr_arm(|| {
        for cond in [EQ, NE, GE] {
            let (mut func, _) = rr_seq(csinc(cond));
            let mut pass = AndCmpFuse;
            assert!(pass.run(&mut func), "cond {cond:#06b} should fuse");
            assert!(fused(&func), "cond {cond:#06b}: expected a Tst");
        }
    });
}

#[test]
fn rr_arm_obeys_the_same_carry_guard() {
    with_rr_arm(|| {
        for cond in [HS, LO, HI, LS] {
            let (mut func, _) = rr_seq(csinc(cond));
            let mut pass = AndCmpFuse;
            assert!(
                !pass.run(&mut func),
                "cond {cond:#06b} reads C: must refuse"
            );
            assert!(!fused(&func), "cond {cond:#06b}: must not emit a Tst");
        }
    });
}

/// THE GUARD THE IMMEDIATE ARM NEVER NEEDED. `TST Rn,Rm` reads BOTH sources at
/// the CMP's position, so a write to EITHER between the AND and the CMP would
/// make the fused form read a different value. The immediate arm only ever had
/// one source to check; missing the second here is a silent miscompile.
#[test]
fn rr_arm_refuses_when_either_source_is_redefined_before_the_cmp() {
    for clobbered in [0u32, 1u32] {
        with_rr_arm(|| {
            let (mut func, _) = single_block_func(vec![
                MachInst::new(AArch64Opcode::AndRR, vec![vreg64(2), vreg64(0), vreg64(1)]),
                // redefine one of the AND's sources between the AND and the CMP
                MachInst::new(
                    AArch64Opcode::AddRI,
                    vec![vreg64(clobbered), vreg64(8), imm(1)],
                ),
                MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(2), imm(0)]),
                csinc(EQ),
                MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(9), imm(3)]),
            ]);
            let mut pass = AndCmpFuse;
            assert!(
                !pass.run(&mut func),
                "v{clobbered} redefined before the CMP: must refuse"
            );
            assert!(!fused(&func), "v{clobbered}: must not emit a Tst");
        });
    }
}

/// The AND result must be dead after the CMP; if the mask is still live the
/// fused form (which discards it into XZR) would lose it.
#[test]
fn rr_arm_refuses_when_the_and_result_is_still_live() {
    with_rr_arm(|| {
        let (mut func, _) = single_block_func(vec![
            MachInst::new(AArch64Opcode::AndRR, vec![vreg64(2), vreg64(0), vreg64(1)]),
            MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(2), imm(0)]),
            csinc(EQ),
            // a second reader of the masked value
            MachInst::new(AArch64Opcode::AddRI, vec![vreg64(4), vreg64(2), imm(1)]),
            MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(9), imm(3)]),
        ]);
        let mut pass = AndCmpFuse;
        assert!(!pass.run(&mut func), "masked value still live: must refuse");
        assert!(!fused(&func));
    });
}
