// trust-cg-opt - AND+CMP -> TST fusion tests
//
// The negative controls are the point of this file. The rewrite itself is
// trivial; what makes it safe is refusing to fire when any flag consumer can
// observe C, because ANDS clears C while SUBS #0 sets it.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use trust_cg_ir::llsc::{LlscOrdering, LlscRmwOp};
use trust_cg_ir::regs::NZCV;
use trust_cg_ir::{
    BlockId, InstFlags, LoweringProvenance, RegClass, Signature, SourceInstDigest, SourceInstId,
    SourceLoc, TransformKind, TrustIrInstId, VReg,
};

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

// These controls exercise the public pass, not just the effects classifier.
// Their annotations are custody bookkeeping, not checked semantic evidence.
fn nzcv_observer_fixture(
    observers: Vec<MachInst>,
    successor: bool,
    condition: i64,
) -> (MachFunction, Vec<InstId>) {
    let mut func = MachFunction::new("nzcv_observer".into(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    let mut ids = Vec::new();
    for inst in [
        MachInst::new(AArch64Opcode::AndRI, vec![vreg64(2), vreg64(0), imm(1)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(2), imm(0)]),
    ] {
        let id = func.push_inst(inst);
        func.append_inst(entry, id);
        ids.push(id);
    }
    let observer_block = if successor {
        let block = func.create_block();
        let id = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(block)],
        ));
        func.append_inst(entry, id);
        ids.push(id);
        func.add_edge(entry, block);
        block
    } else {
        entry
    };
    for inst in observers.into_iter().chain([
        MachInst::new(AArch64Opcode::CSet, vec![vreg32(5), imm(condition)]),
        // A genuine architectural writer bounds the observation interval.
        MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(9), imm(3)]),
        MachInst::new(AArch64Opcode::Ret, vec![]),
    ]) {
        let id = func.push_inst(inst);
        func.append_inst(observer_block, id);
        ids.push(id);
    }
    func.try_sync_vreg_counter().expect("bounded fixture arena");
    (func, ids)
}

fn nzcv_annotate(func: &mut MachFunction, ids: &[InstId]) -> ProvenanceMap {
    let mut provenance = ProvenanceMap::new();
    for (index, &id) in ids.iter().enumerate() {
        let index = index as u32;
        let block = func
            .block_order
            .iter()
            .copied()
            .find(|&block| func.block(block).insts.contains(&id))
            .expect("every fixture instruction has one block owner");
        func.set_inst_lowering_provenance(
            id,
            LoweringProvenance::SourceInst {
                id: SourceInstId {
                    block: block.0,
                    index,
                },
                digest: SourceInstDigest::compute_debug(
                    &func.inst(id).opcode,
                    func.inst(id).operands.len(),
                    0,
                ),
                trust_ir_inst: Some(TrustIrInstId(100 + index)),
            },
        );
        func.inst_mut(id).source_loc = Some(SourceLoc {
            file: 7,
            line: 20 + index,
            col: 2,
        });
        provenance.record_lowering(
            TrustIrInstId(100 + index),
            &[id],
            PassId::new("original-isel"),
        );
    }
    provenance
}

fn nzcv_same_provenance(actual: &ProvenanceMap, before: &ProvenanceMap, ids: &[InstId]) {
    assert_eq!(actual.num_trust_ir_entries(), before.num_trust_ir_entries());
    assert_eq!(actual.num_mach_entries(), before.num_mach_entries());
    assert_eq!(actual.num_encoded(), before.num_encoded());
    for (index, &id) in ids.iter().enumerate() {
        assert_eq!(
            format!("{:?}", actual.get_entry(id)),
            format!("{:?}", before.get_entry(id))
        );
        assert_eq!(actual.get_offset(id), before.get_offset(id));
        let origin = TrustIrInstId(100 + index as u32);
        assert_eq!(actual.get_mach_insts(origin), before.get_mach_insts(origin));
    }
}

fn nzcv_refused_unchanged(mut func: MachFunction, ids: &[InstId]) {
    let mut provenance = nzcv_annotate(&mut func, ids);
    let before = format!("{func:?}");
    let before_provenance = provenance.clone();
    let mut plain = func.clone();
    assert!(!AndCmpFuse.run(&mut plain));
    assert!(!fused(&plain));
    assert_eq!(format!("{plain:?}"), before);
    assert!(!AndCmpFuse.run_with_provenance(&mut func, &mut provenance));
    assert!(!fused(&func));
    // Includes arena, links, CFG, VReg counter, source locations and lowering
    // histories; an observer refusal must not partially retire the candidate.
    assert_eq!(format!("{func:?}"), before);
    nzcv_same_provenance(&provenance, &before_provenance, ids);
}

#[test]
fn public_pass_refuses_mrs_nzcv_and_tpidr_in_same_or_successor_block() {
    for successor in [false, true] {
        // NZCV observes the changed carry directly. TPIDR_EL0 does not, but
        // MRS remains conservatively opaque rather than interpreting sysregs.
        for system_register in [0xda10, 0xde82] {
            for stripped_flags in [false, true] {
                let mut observer =
                    MachInst::new(AArch64Opcode::Mrs, vec![vreg64(6), imm(system_register)]);
                if stripped_flags {
                    observer.flags = InstFlags::EMPTY;
                }
                // Keep the MRS result observable through an actual memory
                // effect, rather than an unused destination. In the NZCV
                // case the stored C bit would differ after unsafe fusion.
                let store =
                    MachInst::new(AArch64Opcode::StrRI, vec![vreg64(6), vreg64(15), imm(0)]);
                let (func, ids) = nzcv_observer_fixture(vec![observer, store], successor, EQ);
                nzcv_refused_unchanged(func, &ids);
            }
        }
    }
}

#[test]
fn public_pass_never_treats_llsc_add_may_write_as_a_definite_kill() {
    for successor in [false, true] {
        for stripped_flags in [false, true] {
            let mut observer = MachInst::new(
                AArch64Opcode::LlscRmw64,
                vec![
                    vreg64(10),
                    vreg64(11),
                    vreg32(12),
                    vreg64(13),
                    vreg64(14),
                    imm(LlscRmwOp::Add.to_imm()),
                    imm(LlscOrdering::ACQ_REL.to_imm()),
                ],
            );
            if stripped_flags {
                observer.flags = InstFlags::EMPTY;
            }
            assert!(crate::effects::writes_flags(observer.opcode));
            assert!(!crate::effects::definitely_writes_flags(observer.opcode));
            let (func, ids) = nzcv_observer_fixture(vec![observer], successor, HS);
            nzcv_refused_unchanged(func, &ids);
        }
    }
}

#[test]
fn public_pass_refuses_implicit_nzcv_reads_and_defs_before_killers() {
    for successor in [false, true] {
        for observer in [
            MachInst::new(AArch64Opcode::AddRR, vec![vreg64(6), vreg64(7), vreg64(8)])
                .with_implicit_uses(&[NZCV]),
            // A definite writer still reads its incoming flags through this
            // explicit metadata; the writer classification cannot bypass it.
            MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(6), imm(1)])
                .with_implicit_uses(&[NZCV]),
            MachInst::new(AArch64Opcode::AddRR, vec![vreg64(6), vreg64(7), vreg64(8)])
                .with_implicit_defs(&[NZCV]),
            // Opaque metadata also precedes the definite-writer exit.
            MachInst::new(AArch64Opcode::CmpRI, vec![vreg64(6), imm(1)])
                .with_implicit_defs(&[NZCV]),
        ] {
            let (func, ids) = nzcv_observer_fixture(vec![observer], successor, EQ);
            nzcv_refused_unchanged(func, &ids);
        }
    }
}

#[test]
fn public_pass_fuses_paired_eq_controls_with_exact_provenance() {
    for successor in [false, true] {
        for observers in [
            vec![],
            vec![MachInst::new(
                AArch64Opcode::AddRR,
                vec![vreg64(6), vreg64(7), vreg64(8)],
            )],
        ] {
            let (mut func, ids) = nzcv_observer_fixture(observers, successor, EQ);
            let mut provenance = nzcv_annotate(&mut func, &ids);
            let before_provenance = provenance.clone();
            let mut expected = func.clone();
            let mut tst = MachInst::new(AArch64Opcode::Tst, vec![vreg64(0), imm(1)]);
            tst.source_loc = expected.inst(ids[1]).source_loc;
            *expected.inst_mut(ids[0]) = MachInst::new(AArch64Opcode::Nop, vec![]);
            *expected.inst_mut(ids[1]) = tst;
            let mut plain = func.clone();
            // Mandatory positives catch a disabled pass or blanket refusal.
            assert!(AndCmpFuse.run(&mut plain));
            assert_eq!(format!("{plain:?}"), format!("{expected:?}"));
            assert!(AndCmpFuse.run_with_provenance(&mut func, &mut provenance));
            assert_eq!(format!("{func:?}"), format!("{expected:?}"));
            for origin in [TrustIrInstId(100), TrustIrInstId(101)] {
                assert_eq!(provenance.get_mach_insts(origin), Some([ids[1]].as_slice()));
            }
            assert!(provenance.get_entry(ids[0]).is_none());
            let merged = provenance.get_entry(ids[1]).expect("merged CMP origin");
            assert!(merged.is_active());
            assert_eq!(
                merged.trust_ir_origins,
                [TrustIrInstId(100), TrustIrInstId(101)]
            );
            let transform = merged.transforms.last().expect("fusion history");
            assert_eq!(transform.pass, PassId::new("and-cmp-fuse"));
            assert_eq!(
                transform.kind,
                TransformKind::Merged {
                    sources: vec![ids[0], ids[1]],
                }
            );
            assert_eq!(provenance.num_trust_ir_entries(), ids.len());
            assert_eq!(provenance.num_mach_entries(), ids.len() - 1);
            for (index, &id) in ids.iter().enumerate().skip(2) {
                assert_eq!(
                    format!("{:?}", provenance.get_entry(id)),
                    format!("{:?}", before_provenance.get_entry(id))
                );
                assert_eq!(
                    provenance.get_mach_insts(TrustIrInstId(100 + index as u32)),
                    Some([id].as_slice())
                );
            }
        }
    }
}
