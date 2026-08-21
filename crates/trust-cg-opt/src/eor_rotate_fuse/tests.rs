// trust-cg-opt - EOR-with-rotate fusion peephole tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use trust_cg_ir::{BlockId, RegClass, Signature, VReg};

fn vreg(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
}

fn vreg64(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
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

/// A "use" of a vreg so its read-count is realistic (an EOR whose result must be
/// consumed to stay live). Returns a store-like consumer that only READS.
fn consume(v: MachOperand) -> MachInst {
    // CmpRR reads both operands and defines nothing — a pure reader.
    MachInst::new(AArch64Opcode::CmpRR, vec![v.clone(), v])
}

#[test]
fn fuse_basic_ror_then_eor() {
    // t(2) = ROR s(0), #25 ; d(3) = EOR x(1), t(2)
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::RorRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(25)],
        ),
        MachInst::new(AArch64Opcode::EorRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
    ]);
    let mut pass = EorRotateFuse;
    assert!(pass.run(&mut func));

    let insts = &func.block(entry).insts;
    // RorRI became Nop.
    assert_eq!(func.inst(insts[0]).opcode, AArch64Opcode::Nop);
    // EorRR became EorRRShift [d, Rn=x, Rm=s, Imm(25)].
    let fused = func.inst(insts[1]);
    assert_eq!(fused.opcode, AArch64Opcode::EorRRShift);
    assert_eq!(fused.operands[0], vreg(3)); // dst
    assert_eq!(fused.operands[1], vreg(1)); // Rn (un-shifted = x)
    assert_eq!(fused.operands[2], vreg(0)); // Rm (rotated source = s)
    assert_eq!(fused.operands[3], MachOperand::Imm(25));
}

#[test]
fn fuse_commuted_operand_order() {
    // d(3) = EOR t(2), x(1)  — rotated operand FIRST (EOR commutes).
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::RorRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(7)],
        ),
        MachInst::new(AArch64Opcode::EorRR, vec![vreg(3), vreg(2), vreg(1)]),
        consume(vreg(3)),
    ]);
    let mut pass = EorRotateFuse;
    assert!(pass.run(&mut func));

    let fused = func.inst(func.block(entry).insts[1]);
    assert_eq!(fused.opcode, AArch64Opcode::EorRRShift);
    assert_eq!(fused.operands[1], vreg(1)); // Rn = x
    assert_eq!(fused.operands[2], vreg(0)); // Rm = s
    assert_eq!(fused.operands[3], MachOperand::Imm(7));
}

#[test]
fn fuse_x_form_64bit() {
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::RorRI,
            vec![vreg64(2), vreg64(0), MachOperand::Imm(40)],
        ),
        MachInst::new(AArch64Opcode::EorRR, vec![vreg64(3), vreg64(1), vreg64(2)]),
        consume(vreg64(3)),
    ]);
    let mut pass = EorRotateFuse;
    assert!(pass.run(&mut func));
    let fused = func.inst(func.block(entry).insts[1]);
    assert_eq!(fused.opcode, AArch64Opcode::EorRRShift);
    assert_eq!(fused.operands[3], MachOperand::Imm(40));
}

#[test]
fn no_fuse_when_rotate_result_multi_use() {
    // t(2) read by the EOR AND by a second consumer -> NOT single-use.
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::RorRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(25)],
        ),
        MachInst::new(AArch64Opcode::EorRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(2)), // extra reader of t
        consume(vreg(3)),
    ]);
    let mut pass = EorRotateFuse;
    assert!(!pass.run(&mut func));
    assert_eq!(
        func.inst(func.block(entry).insts[0]).opcode,
        AArch64Opcode::RorRI
    );
    assert_eq!(
        func.inst(func.block(entry).insts[1]).opcode,
        AArch64Opcode::EorRR
    );
}

#[test]
fn no_fuse_cross_block() {
    // RorRI in the entry block, EorRR in a successor block: the per-block def-map
    // deliberately does not carry `t` across, so no fusion (fail-closed).
    let mut func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    let b1 = func.create_block();
    let ror = func.push_inst(MachInst::new(
        AArch64Opcode::RorRI,
        vec![vreg(2), vreg(0), MachOperand::Imm(25)],
    ));
    func.append_inst(entry, ror);
    let eor = func.push_inst(MachInst::new(
        AArch64Opcode::EorRR,
        vec![vreg(3), vreg(1), vreg(2)],
    ));
    func.append_inst(b1, eor);
    let c = func.push_inst(consume(vreg(3)));
    func.append_inst(b1, c);

    let mut pass = EorRotateFuse;
    assert!(!pass.run(&mut func));
    assert_eq!(func.inst(ror).opcode, AArch64Opcode::RorRI);
    assert_eq!(func.inst(eor).opcode, AArch64Opcode::EorRR);
}

#[test]
fn no_fuse_non_rotate_source() {
    // The EOR's second operand is defined by an ADD, not a ROR.
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(4)]),
        MachInst::new(AArch64Opcode::EorRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
    ]);
    let mut pass = EorRotateFuse;
    assert!(!pass.run(&mut func));
    assert_eq!(
        func.inst(func.block(entry).insts[1]).opcode,
        AArch64Opcode::EorRR
    );
}

#[test]
fn no_fuse_zero_rotate_amount() {
    // k == 0 is a plain move, never a real rotate — fail-closed (also unencodable
    // as EorRRShift).
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::RorRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(0)],
        ),
        MachInst::new(AArch64Opcode::EorRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
    ]);
    let mut pass = EorRotateFuse;
    assert!(!pass.run(&mut func));
    assert_eq!(
        func.inst(func.block(entry).insts[1]).opcode,
        AArch64Opcode::EorRR
    );
}

/// The salsa20 quarter-round shape: `add; ror; eor` chained. Each `eor` fuses its
/// own rotate; the (independent) add stays.
#[test]
fn fuse_salsa_arx_triple() {
    // w20 = add w19, w17 ; t = ror w20, #25 ; x[b] ^= t
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(AArch64Opcode::AddRR, vec![vreg(20), vreg(19), vreg(17)]),
        MachInst::new(
            AArch64Opcode::RorRI,
            vec![vreg(21), vreg(20), MachOperand::Imm(25)],
        ),
        MachInst::new(AArch64Opcode::EorRR, vec![vreg(4), vreg(4), vreg(21)]),
        consume(vreg(4)),
    ]);
    let mut pass = EorRotateFuse;
    assert!(pass.run(&mut func));
    let insts = &func.block(entry).insts;
    assert_eq!(func.inst(insts[0]).opcode, AArch64Opcode::AddRR); // add survives
    assert_eq!(func.inst(insts[1]).opcode, AArch64Opcode::Nop); // ror folded
    let fused = func.inst(insts[2]);
    assert_eq!(fused.opcode, AArch64Opcode::EorRRShift);
    assert_eq!(fused.operands[1], vreg(4)); // Rn = x[b]
    assert_eq!(fused.operands[2], vreg(20)); // Rm = add result
    assert_eq!(fused.operands[3], MachOperand::Imm(25));
}

// ---------------------------------------------------------------------------
// Reaching-definition guards (audit regressions).
//
// The fusion MOVES the read of the rotate source `s` forward from the `RorRI`
// position to the `EorRR` position, and it deletes the `RorRI`. Both are only
// sound when the matched `RorRI` is the REACHING def of `t` at the `EorRR` and
// `s` is unchanged across the window. Before these guards the pass tracked no
// def positions at all and never invalidated `ror_defs`, so both shapes fused.
// ---------------------------------------------------------------------------

/// `s` (v0) is redefined between the `RorRI` and the `EorRR`. Fusing computes
/// `x ^ ROR(NEW s, k)` instead of `x ^ ROR(OLD s, k)`.
#[test]
fn no_fuse_when_rotate_source_redefined_before_consumer() {
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::RorRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(7)],
        ),
        MachInst::new(AArch64Opcode::MovI, vec![vreg(0), MachOperand::Imm(1)]),
        MachInst::new(AArch64Opcode::EorRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
        consume(vreg(0)),
    ]);
    let mut pass = EorRotateFuse;
    assert!(!pass.run(&mut func));
    assert_eq!(
        func.inst(func.block(entry).insts[0]).opcode,
        AArch64Opcode::RorRI
    );
    assert_eq!(
        func.inst(func.block(entry).insts[2]).opcode,
        AArch64Opcode::EorRR
    );
}

/// `t` (v2) is redefined by a later `MovI`, so the `RorRI` is DEAD and the
/// reaching def of `t` at the `EorRR` is the `MovI`. Fusing against the stale
/// entry computes `x ^ ROR(s, k)` instead of `x ^ 5`.
#[test]
fn no_fuse_against_stale_rotate_def() {
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::RorRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(7)],
        ),
        MachInst::new(AArch64Opcode::MovI, vec![vreg(2), MachOperand::Imm(5)]),
        MachInst::new(AArch64Opcode::EorRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
    ]);
    let mut pass = EorRotateFuse;
    assert!(!pass.run(&mut func));
    assert_eq!(
        func.inst(func.block(entry).insts[0]).opcode,
        AArch64Opcode::RorRI
    );
}

/// `t` (v2) is read by `Movk`'s TIED def-use operand 0. The old
/// `produces_value() && idx == 0` oracle skipped that position and reported
/// `t` single-use, authorizing deletion of a still-read `RorRI`; the shared
/// `effects::aarch64_for_each_use_position` oracle counts it.
#[test]
fn no_fuse_when_tied_def_use_still_reads_rotate_result() {
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::RorRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(7)],
        ),
        MachInst::new(AArch64Opcode::EorRR, vec![vreg(3), vreg(1), vreg(2)]),
        MachInst::new(
            AArch64Opcode::Movk,
            vec![vreg(2), MachOperand::Imm(9), MachOperand::Imm(16)],
        ),
        consume(vreg(3)),
    ]);
    let mut pass = EorRotateFuse;
    assert!(!pass.run(&mut func));
    assert_eq!(
        func.inst(func.block(entry).insts[0]).opcode,
        AArch64Opcode::RorRI
    );
}

/// A def of `s` BEFORE the `RorRI` is fine — only a def in the window between
/// the producer and the consumer moves the read past a write.
#[test]
fn fuse_when_source_defined_before_the_rotate() {
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(AArch64Opcode::MovI, vec![vreg(0), MachOperand::Imm(3)]),
        MachInst::new(
            AArch64Opcode::RorRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(7)],
        ),
        MachInst::new(AArch64Opcode::EorRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
    ]);
    let mut pass = EorRotateFuse;
    assert!(pass.run(&mut func));
    assert_eq!(
        func.inst(func.block(entry).insts[2]).opcode,
        AArch64Opcode::EorRRShift
    );
}

/// Sibling controls: `shift-alu-fuse` already declines both shapes, which is
/// what made the absence in this pass an anomaly rather than a design choice.
#[test]
fn sibling_shift_alu_fuse_declines_the_same_shapes() {
    use crate::shift_alu_fuse::ShiftAluFuse;

    let (mut redefined, _) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::LslRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(7)],
        ),
        MachInst::new(AArch64Opcode::MovI, vec![vreg(0), MachOperand::Imm(1)]),
        MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
        consume(vreg(0)),
    ]);
    assert!(!ShiftAluFuse.run(&mut redefined));

    let (mut stale, _) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::LslRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(7)],
        ),
        MachInst::new(AArch64Opcode::MovI, vec![vreg(2), MachOperand::Imm(5)]),
        MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
    ]);
    assert!(!ShiftAluFuse.run(&mut stale));
}
