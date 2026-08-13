// trust-cg-opt - shift-into-ADD/SUB fusion peephole tests
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

/// A pure reader of a vreg so its read-count is realistic (CmpRR reads both
/// operands and defines nothing).
fn consume(v: MachOperand) -> MachInst {
    MachInst::new(AArch64Opcode::CmpRR, vec![v.clone(), v])
}

#[test]
fn fuse_basic_lsl_then_add() {
    // t(2) = LSL s(0), #1 ; d(3) = ADD x(1), t(2)
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::LslRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(1)],
        ),
        MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(pass.run(&mut func));

    let insts = &func.block(entry).insts;
    assert_eq!(func.inst(insts[0]).opcode, AArch64Opcode::Nop); // LslRI folded
    let fused = func.inst(insts[1]);
    assert_eq!(fused.opcode, AArch64Opcode::AddRRShift);
    assert_eq!(fused.operands[0], vreg(3)); // dst
    assert_eq!(fused.operands[1], vreg(1)); // Rn (un-shifted base = x)
    assert_eq!(fused.operands[2], vreg(0)); // Rm (shifted source = s)
    assert_eq!(fused.operands[3], MachOperand::Imm(1));
}

#[test]
fn fuse_commuted_add_order() {
    // d(3) = ADD t(2), x(1)  — shifted operand FIRST (ADD commutes).
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::LslRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(3)],
        ),
        MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(2), vreg(1)]),
        consume(vreg(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(pass.run(&mut func));

    let fused = func.inst(func.block(entry).insts[1]);
    assert_eq!(fused.opcode, AArch64Opcode::AddRRShift);
    assert_eq!(fused.operands[1], vreg(1)); // Rn = x (un-shifted)
    assert_eq!(fused.operands[2], vreg(0)); // Rm = s (shifted source)
    assert_eq!(fused.operands[3], MachOperand::Imm(3));
}

#[test]
fn fuse_x_form_64bit() {
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::LslRI,
            vec![vreg64(2), vreg64(0), MachOperand::Imm(40)],
        ),
        MachInst::new(AArch64Opcode::AddRR, vec![vreg64(3), vreg64(1), vreg64(2)]),
        consume(vreg64(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(pass.run(&mut func));
    let fused = func.inst(func.block(entry).insts[1]);
    assert_eq!(fused.opcode, AArch64Opcode::AddRRShift);
    assert_eq!(fused.operands[3], MachOperand::Imm(40));
}

#[test]
fn fuse_sub_subtrahend() {
    // d(3) = SUB x(1), t(2) with t = s<<k in the SUBTRAHEND (operand 2) — fuses.
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::LslRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(2)],
        ),
        MachInst::new(AArch64Opcode::SubRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(pass.run(&mut func));

    let insts = &func.block(entry).insts;
    assert_eq!(func.inst(insts[0]).opcode, AArch64Opcode::Nop); // LslRI folded
    let fused = func.inst(insts[1]);
    assert_eq!(fused.opcode, AArch64Opcode::SubRRShift);
    assert_eq!(fused.operands[1], vreg(1)); // Rn = minuend x
    assert_eq!(fused.operands[2], vreg(0)); // Rm = shifted subtrahend s
    assert_eq!(fused.operands[3], MachOperand::Imm(2));
}

/// CRITICAL non-commutativity BAIL: a shifted temp in the SUB MINUEND position
/// (operand 1) must NOT fuse — `SUB Rd,Rn,Rm,LSL#k` shifts only Rm, so folding
/// the minuend would silently compute the wrong `x - (s<<k)` for `(s<<k) - x`.
#[test]
fn no_fuse_sub_minuend() {
    // d(3) = SUB t(2), x(1)  — t = s<<k is the MINUEND (operand 1). BAIL.
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::LslRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(2)],
        ),
        MachInst::new(AArch64Opcode::SubRR, vec![vreg(3), vreg(2), vreg(1)]),
        consume(vreg(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(!pass.run(&mut func), "SUB minuend shift must NOT fuse");
    let insts = &func.block(entry).insts;
    assert_eq!(func.inst(insts[0]).opcode, AArch64Opcode::LslRI); // LslRI kept
    assert_eq!(func.inst(insts[1]).opcode, AArch64Opcode::SubRR); // SubRR kept
}

#[test]
fn no_fuse_when_shift_result_multi_use() {
    // t(2) read by the ADD AND a second consumer -> NOT single-use.
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::LslRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(1)],
        ),
        MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(2)), // extra reader of t
        consume(vreg(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(!pass.run(&mut func));
    assert_eq!(
        func.inst(func.block(entry).insts[1]).opcode,
        AArch64Opcode::AddRR
    );
}

#[test]
fn no_fuse_cross_block() {
    // LslRI in the entry block, AddRR in a successor: the per-block def-map does
    // not carry `t` across, so no fusion (fail-closed).
    let mut func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    let b1 = func.create_block();
    let lsl = func.push_inst(MachInst::new(
        AArch64Opcode::LslRI,
        vec![vreg(2), vreg(0), MachOperand::Imm(1)],
    ));
    func.append_inst(entry, lsl);
    let add = func.push_inst(MachInst::new(
        AArch64Opcode::AddRR,
        vec![vreg(3), vreg(1), vreg(2)],
    ));
    func.append_inst(b1, add);
    let c = func.push_inst(consume(vreg(3)));
    func.append_inst(b1, c);

    let mut pass = ShiftAluFuse;
    assert!(!pass.run(&mut func));
    assert_eq!(func.inst(lsl).opcode, AArch64Opcode::LslRI);
    assert_eq!(func.inst(add).opcode, AArch64Opcode::AddRR);
}

#[test]
fn no_fuse_non_lsl_lsr_source() {
    // The ADD's second operand is defined by an ASR (neither LSL nor LSR) — not
    // foldable (no ADD+ASR opcode is modeled; MINIMAL SURFACE).
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::AsrRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(1)],
        ),
        MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(!pass.run(&mut func));
    assert_eq!(
        func.inst(func.block(entry).insts[1]).opcode,
        AArch64Opcode::AddRR
    );
}

// ---------------------------------------------------------------------------
// LSR-into-ADD fusion (AddRRShiftLsr) — the srem/sdiv magic sign-bit correction
// and udiv magic add-back shapes.
// ---------------------------------------------------------------------------

/// The srem/sdiv-by-constant sign-bit correction shape:
/// `t = LSR x, #31 ; r = ADD q, t` -> `ADD r, q, x, LSR #31`.
#[test]
fn fuse_lsr_then_add() {
    // t(2) = LSR s(0), #31 ; d(3) = ADD x(1), t(2)
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::LsrRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(31)],
        ),
        MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(pass.run(&mut func));

    let insts = &func.block(entry).insts;
    assert_eq!(func.inst(insts[0]).opcode, AArch64Opcode::Nop); // LsrRI folded
    let fused = func.inst(insts[1]);
    assert_eq!(fused.opcode, AArch64Opcode::AddRRShiftLsr);
    assert_eq!(fused.operands[0], vreg(3)); // dst
    assert_eq!(fused.operands[1], vreg(1)); // Rn (un-shifted base = x)
    assert_eq!(fused.operands[2], vreg(0)); // Rm (shifted source = s)
    assert_eq!(fused.operands[3], MachOperand::Imm(31));
}

#[test]
fn fuse_lsr_commuted_add_order() {
    // d(3) = ADD t(2), x(1)  — shifted operand FIRST (ADD commutes).
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::LsrRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(1)],
        ),
        MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(2), vreg(1)]),
        consume(vreg(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(pass.run(&mut func));

    let fused = func.inst(func.block(entry).insts[1]);
    assert_eq!(fused.opcode, AArch64Opcode::AddRRShiftLsr);
    assert_eq!(fused.operands[1], vreg(1)); // Rn = x (un-shifted)
    assert_eq!(fused.operands[2], vreg(0)); // Rm = s (shifted source)
    assert_eq!(fused.operands[3], MachOperand::Imm(1));
}

#[test]
fn fuse_lsr_x_form_64bit() {
    // The 64-bit sign-bit correction (`lsr x, #63`).
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::LsrRI,
            vec![vreg64(2), vreg64(0), MachOperand::Imm(63)],
        ),
        MachInst::new(AArch64Opcode::AddRR, vec![vreg64(3), vreg64(1), vreg64(2)]),
        consume(vreg64(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(pass.run(&mut func));
    let fused = func.inst(func.block(entry).insts[1]);
    assert_eq!(fused.opcode, AArch64Opcode::AddRRShiftLsr);
    assert_eq!(fused.operands[3], MachOperand::Imm(63));
}

/// LSR into SUB must NOT fuse in EITHER position — no `SubRRShiftLsr` opcode
/// exists (MINIMAL SURFACE), so the subtrahend slot is not a candidate, and the
/// minuend never is (non-commutativity).
#[test]
fn no_fuse_lsr_into_sub() {
    for operands in [
        vec![vreg(3), vreg(1), vreg(2)], // t in the subtrahend slot
        vec![vreg(3), vreg(2), vreg(1)], // t in the minuend slot
    ] {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(
                AArch64Opcode::LsrRI,
                vec![vreg(2), vreg(0), MachOperand::Imm(2)],
            ),
            MachInst::new(AArch64Opcode::SubRR, operands),
            consume(vreg(3)),
        ]);
        let mut pass = ShiftAluFuse;
        assert!(!pass.run(&mut func), "LSR into SUB must NOT fuse");
        let insts = &func.block(entry).insts;
        assert_eq!(func.inst(insts[0]).opcode, AArch64Opcode::LsrRI); // kept
        assert_eq!(func.inst(insts[1]).opcode, AArch64Opcode::SubRR); // kept
    }
}

#[test]
fn no_fuse_lsr_multi_use() {
    // t(2) read by the ADD AND a second consumer -> NOT single-use.
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::LsrRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(31)],
        ),
        MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(2)), // extra reader of t
        consume(vreg(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(!pass.run(&mut func));
    assert_eq!(
        func.inst(func.block(entry).insts[1]).opcode,
        AArch64Opcode::AddRR
    );
}

#[test]
fn no_fuse_lsr_out_of_range() {
    // W form, k == 32 == width — unencodable (imm6 bit 5 must be 0); fail-closed.
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::LsrRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(32)],
        ),
        MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(!pass.run(&mut func));
    assert_eq!(
        func.inst(func.block(entry).insts[1]).opcode,
        AArch64Opcode::AddRR
    );
}

/// DETERMINISM: when BOTH an LSL temp and an LSR temp feed the same ADD, the
/// LSL fuses (tried first — pre-existing LSL output is byte-identical) and the
/// LSR temp survives.
#[test]
fn lsl_preferred_over_lsr_when_both_feed_add() {
    // tl(2) = LSL a(0), #1 ; tr(3) = LSR b(1), #2 ; d(4) = ADD tl(2), tr(3)
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::LslRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(1)],
        ),
        MachInst::new(
            AArch64Opcode::LsrRI,
            vec![vreg(3), vreg(1), MachOperand::Imm(2)],
        ),
        MachInst::new(AArch64Opcode::AddRR, vec![vreg(4), vreg(2), vreg(3)]),
        consume(vreg(4)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(pass.run(&mut func));
    let insts = &func.block(entry).insts;
    assert_eq!(func.inst(insts[0]).opcode, AArch64Opcode::Nop); // LSL folded
    assert_eq!(func.inst(insts[1]).opcode, AArch64Opcode::LsrRI); // LSR kept
    let fused = func.inst(insts[2]);
    assert_eq!(fused.opcode, AArch64Opcode::AddRRShift); // the LSL form
    assert_eq!(fused.operands[1], vreg(3)); // Rn = the (unfused) LSR temp
    assert_eq!(fused.operands[2], vreg(0)); // Rm = a (LSL-shifted source)
}

#[test]
fn fuse_eor_with_lsl_and_lsr_in_both_operand_orders() {
    for (shift_op, fused_op) in [
        (AArch64Opcode::LslRI, AArch64Opcode::EorRRLsl),
        (AArch64Opcode::LsrRI, AArch64Opcode::EorRRLsr),
    ] {
        for shifted_first in [false, true] {
            let eor_operands = if shifted_first {
                vec![vreg(3), vreg(2), vreg(1)]
            } else {
                vec![vreg(3), vreg(1), vreg(2)]
            };
            let (mut func, entry) = single_block_func(vec![
                MachInst::new(shift_op, vec![vreg(2), vreg(0), MachOperand::Imm(7)]),
                MachInst::new(AArch64Opcode::EorRR, eor_operands),
                consume(vreg(3)),
            ]);

            assert!(ShiftAluFuse.run(&mut func));
            let insts = &func.block(entry).insts;
            assert_eq!(func.inst(insts[0]).opcode, AArch64Opcode::Nop);
            let fused = func.inst(insts[1]);
            assert_eq!(fused.opcode, fused_op);
            assert_eq!(fused.operands[1], vreg(1));
            assert_eq!(fused.operands[2], vreg(0));
            assert_eq!(fused.operands[3], MachOperand::Imm(7));
        }
    }
}

#[test]
fn eor_shift_fusion_keeps_temp_read_by_tied_def_use() {
    // MOVK reads and writes operand 0. A naive "operand 0 is always only a
    // def" use counter would delete the LSL and silently change MOVK's input.
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::LslRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(3)],
        ),
        MachInst::new(AArch64Opcode::EorRR, vec![vreg(3), vreg(1), vreg(2)]),
        MachInst::new(
            AArch64Opcode::Movk,
            vec![vreg(2), MachOperand::Imm(0x1234), MachOperand::Imm(0)],
        ),
        consume(vreg(3)),
        consume(vreg(2)),
    ]);
    assert!(!ShiftAluFuse.run(&mut func));
    assert_eq!(
        func.inst(func.block(entry).insts[0]).opcode,
        AArch64Opcode::LslRI
    );
}

#[test]
fn eor_shift_fusion_rejects_redefined_source_and_mixed_width() {
    let (mut redefined, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::LslRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(3)],
        ),
        MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(0), vreg(0), MachOperand::Imm(1)],
        ),
        MachInst::new(AArch64Opcode::EorRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
        consume(vreg(0)),
    ]);
    assert!(!ShiftAluFuse.run(&mut redefined));
    assert_eq!(
        redefined.inst(redefined.block(entry).insts[2]).opcode,
        AArch64Opcode::EorRR
    );

    let (mut mixed, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::LsrRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(3)],
        ),
        MachInst::new(AArch64Opcode::EorRR, vec![vreg64(3), vreg64(1), vreg(2)]),
        consume(vreg64(3)),
    ]);
    assert!(!ShiftAluFuse.run(&mut mixed));
    assert_eq!(
        mixed.inst(mixed.block(entry).insts[1]).opcode,
        AArch64Opcode::EorRR
    );
}

// NOTE: the LSR-fusion kill switch (`TCG_NO_LSR_ADD_FUSE`) is validated
// out-of-band via object-code identity (kill-switch on vs off) in the
// mini-sweep harness, not here — an in-process `set_var` would race the
// parallel test threads that also read the var through the pass.

#[test]
fn no_fuse_zero_shift_amount() {
    // k == 0 is a plain move, never a real shift — fail-closed (also unencodable
    // as AddRRShift).
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::LslRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(0)],
        ),
        MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(!pass.run(&mut func));
    assert_eq!(
        func.inst(func.block(entry).insts[1]).opcode,
        AArch64Opcode::AddRR
    );
}

#[test]
fn no_fuse_out_of_range_shift() {
    // W form, k == 32 == width — unencodable in imm6 bit-5-must-be-0; fail-closed.
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::LslRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(32)],
        ),
        MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(!pass.run(&mut func));
    assert_eq!(
        func.inst(func.block(entry).insts[1]).opcode,
        AArch64Opcode::AddRR
    );
}

/// Flag-setting ADDS must NEVER fuse — it is not `AddRR`, so the pass never even
/// considers it (fusing a flags-consumer's producer would drop the NZCV effect).
#[test]
fn no_fuse_flag_setting_adds() {
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::LslRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(1)],
        ),
        MachInst::new(AArch64Opcode::AddsRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(!pass.run(&mut func));
    assert_eq!(
        func.inst(func.block(entry).insts[1]).opcode,
        AArch64Opcode::AddsRR
    );
}

/// The mul-by-constant strength-reduction shape (`x * 3 = x + (x << 1)`):
/// `t = LSL x, #1 ; d = ADD x, t`. Collapses to one `AddRRShift`.
#[test]
fn fuse_mul_shift_reduce_shape() {
    // t(2) = LSL x(0), #1 ; d(3) = ADD x(0), t(2)  — the `x*3` decomposition.
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::LslRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(1)],
        ),
        MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(0), vreg(2)]),
        consume(vreg(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(pass.run(&mut func));
    let insts = &func.block(entry).insts;
    assert_eq!(func.inst(insts[0]).opcode, AArch64Opcode::Nop);
    let fused = func.inst(insts[1]);
    assert_eq!(fused.opcode, AArch64Opcode::AddRRShift);
    assert_eq!(fused.operands[1], vreg(0)); // Rn = x
    assert_eq!(fused.operands[2], vreg(0)); // Rm = x (shifted)
    assert_eq!(fused.operands[3], MachOperand::Imm(1));
}

// ---------------------------------------------------------------------------
// Variable-shift amount-mask elision (`AndRI t, amt, #(W-1)` + `LslRR d, x, t`)
// ---------------------------------------------------------------------------

#[test]
fn elide_and31_before_lslrr_w() {
    // t(2) = AND amt(0), #31 ; d(3) = LSL x(1), t(2)  →  d = LSL x, amt
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::AndRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(31)],
        ),
        MachInst::new(AArch64Opcode::LslRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(pass.run(&mut func));
    let insts = &func.block(entry).insts;
    assert_eq!(func.inst(insts[0]).opcode, AArch64Opcode::Nop); // AndRI elided
    let shift = func.inst(insts[1]);
    assert_eq!(shift.opcode, AArch64Opcode::LslRR);
    assert_eq!(shift.operands[2], vreg(0)); // amount = raw amt
}

#[test]
fn elide_and31_before_lsrrr_and_asrrr_w() {
    for opcode in [AArch64Opcode::LsrRR, AArch64Opcode::AsrRR] {
        let (mut func, entry) = single_block_func(vec![
            MachInst::new(
                AArch64Opcode::AndRI,
                vec![vreg(2), vreg(0), MachOperand::Imm(31)],
            ),
            MachInst::new(opcode, vec![vreg(3), vreg(1), vreg(2)]),
            consume(vreg(3)),
        ]);
        let mut pass = ShiftAluFuse;
        assert!(pass.run(&mut func));
        let insts = &func.block(entry).insts;
        assert_eq!(func.inst(insts[0]).opcode, AArch64Opcode::Nop);
        assert_eq!(func.inst(insts[1]).opcode, opcode);
        assert_eq!(func.inst(insts[1]).operands[2], vreg(0));
    }
}

#[test]
fn elide_and63_before_lslrr_x() {
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::AndRI,
            vec![vreg64(2), vreg64(0), MachOperand::Imm(63)],
        ),
        MachInst::new(AArch64Opcode::LslRR, vec![vreg64(3), vreg64(1), vreg64(2)]),
        consume(vreg64(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(pass.run(&mut func));
    let insts = &func.block(entry).insts;
    assert_eq!(func.inst(insts[0]).opcode, AArch64Opcode::Nop);
    assert_eq!(func.inst(insts[1]).operands[2], vreg64(0));
}

/// A WIDER mask that still keeps all low log2(W) bits is equally dead:
/// `(amt & 63) mod 32 == amt mod 32`.
#[test]
fn elide_and63_before_lslrr_w_wider_mask() {
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::AndRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(63)],
        ),
        MachInst::new(AArch64Opcode::LslRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(pass.run(&mut func));
    assert_eq!(
        func.inst(func.block(entry).insts[0]).opcode,
        AArch64Opcode::Nop
    );
}

/// `#31` on a 64-bit shift REALLY masks (31 & 63 != 63) — must NOT fire.
#[test]
fn no_elide_and31_on_x_shift() {
    let (mut func, entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::AndRI,
            vec![vreg64(2), vreg64(0), MachOperand::Imm(31)],
        ),
        MachInst::new(AArch64Opcode::LslRR, vec![vreg64(3), vreg64(1), vreg64(2)]),
        consume(vreg64(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(!pass.run(&mut func));
    assert_eq!(
        func.inst(func.block(entry).insts[0]).opcode,
        AArch64Opcode::AndRI
    );
}

/// A mask missing low bits (`#15`) changes the amount — must NOT fire.
#[test]
fn no_elide_narrow_mask() {
    let (mut func, _entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::AndRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(15)],
        ),
        MachInst::new(AArch64Opcode::LslRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(!pass.run(&mut func));
}

/// Mixed register widths between the AND and the shift — must NOT fire.
#[test]
fn no_elide_mixed_width() {
    let (mut func, _entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::AndRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(31)],
        ),
        MachInst::new(AArch64Opcode::LslRR, vec![vreg64(3), vreg64(1), vreg(2)]),
        consume(vreg64(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(!pass.run(&mut func));
}

/// The masked value has a SECOND reader — the AndRI is live, must NOT fire.
#[test]
fn no_elide_multi_use_masked_amount() {
    let (mut func, _entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::AndRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(31)],
        ),
        MachInst::new(AArch64Opcode::LslRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
        consume(vreg(2)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(!pass.run(&mut func));
}

/// `amt` is REDEFINED between the AndRI and the shift: the elision would read
/// the NEW amt — must NOT fire (reaching-def guard).
#[test]
fn no_elide_amt_redefined_between() {
    let (mut func, _entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::AndRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(31)],
        ),
        MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(0), vreg(0), MachOperand::Imm(1)],
        ),
        MachInst::new(AArch64Opcode::LslRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
        consume(vreg(0)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(!pass.run(&mut func));
}

/// `t` is REDEFINED between the AndRI and the shift: the AndRI is no longer
/// the reaching def of the shift amount — must NOT fire (map invalidation).
#[test]
fn no_elide_t_redefined_between() {
    let (mut func, _entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::AndRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(31)],
        ),
        MachInst::new(AArch64Opcode::MovI, vec![vreg(2), MachOperand::Imm(5)]),
        MachInst::new(AArch64Opcode::LslRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(!pass.run(&mut func));
}

/// Kill switch: `TCG_NO_SHIFT_AMT_MASK_ELIDE` disables ONLY the mask elision.
#[test]
fn mask_elide_kill_switch() {
    let (func, fired) =
        crate::env_lock::with_env_overrides(&[("TCG_NO_SHIFT_AMT_MASK_ELIDE", "1")], || {
            let (mut func, _entry) = single_block_func(vec![
                MachInst::new(
                    AArch64Opcode::AndRI,
                    vec![vreg(2), vreg(0), MachOperand::Imm(31)],
                ),
                MachInst::new(AArch64Opcode::LslRR, vec![vreg(3), vreg(1), vreg(2)]),
                consume(vreg(3)),
            ]);
            let fired = ShiftAluFuse.run(&mut func);
            (func, fired)
        });
    assert!(!fired);
    let entry = func.entry;
    assert_eq!(
        func.inst(func.block(entry).insts[0]).opcode,
        AArch64Opcode::AndRI
    );
}

/// The existing LSL-into-ADD fusion declines when the shift SOURCE is
/// redefined between the LslRI and the ADD (reaching-def hardening).
#[test]
fn no_fuse_lsl_source_redefined_between() {
    // t(2) = LSL s(0), #1 ; s(0) = ADD s(0), #1 ; d(3) = ADD x(1), t(2)
    let (mut func, _entry) = single_block_func(vec![
        MachInst::new(
            AArch64Opcode::LslRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(1)],
        ),
        MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(0), vreg(0), MachOperand::Imm(1)],
        ),
        MachInst::new(AArch64Opcode::AddRR, vec![vreg(3), vreg(1), vreg(2)]),
        consume(vreg(3)),
        consume(vreg(0)),
    ]);
    let mut pass = ShiftAluFuse;
    assert!(!pass.run(&mut func));
}
