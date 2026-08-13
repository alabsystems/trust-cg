// trust-cg-opt - xorshift demanded-bits tests
//
// The NEGATIVE cases are the point: reading a bit at or above the shift amount
// from `x` instead of `y` is a wrong value.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use trust_cg_ir::{BlockId, MachInst, RegClass, Signature};

fn v(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn imm(x: i64) -> MachOperand {
    MachOperand::Imm(x)
}

/// y(2) = x(1) ^ (x(1) << k), then `consumer` reading y.
fn seq(k: i64, consumer: MachInst) -> (MachFunction, BlockId) {
    let mut func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    for i in [
        MachInst::new(AArch64Opcode::EorRRLsl, vec![v(2), v(1), v(1), imm(k)]),
        consumer,
    ] {
        let id = func.push_inst(i);
        func.append_inst(entry, id);
    }
    (func, entry)
}

/// Does the consumer (last inst) now read x(1) instead of y(2)?
fn reads_x(func: &MachFunction, op_idx: usize) -> bool {
    let b = func.block_order[0];
    let last = *func.block(b).insts.last().unwrap();
    func.inst(last).operands[op_idx] == v(1)
}

#[test]
fn tbz_below_shift_is_rewritten() {
    // s3 = s2 ^ (s2 << 17); `tbz y, #0` reads bit 0 < 17 — b1's exact shape.
    let (mut func, _) = seq(
        17,
        MachInst::new(AArch64Opcode::Tbz, vec![v(2), imm(0), imm(0)]),
    );
    assert!(XorshiftDemandedBits.run(&mut func));
    assert!(reads_x(&func, 0), "bit 0 < 17 must read the shift's source");
}

/// THE CRITICAL NEGATIVE CONTROL. Bit >= k is NOT preserved by `x ^ (x << k)`.
#[test]
fn tbz_at_or_above_shift_is_not_rewritten() {
    for bit in [17i64, 18, 63] {
        let (mut func, _) = seq(
            17,
            MachInst::new(AArch64Opcode::Tbz, vec![v(2), imm(bit), imm(0)]),
        );
        XorshiftDemandedBits.run(&mut func);
        assert!(
            !reads_x(&func, 0),
            "bit {bit} >= 17 differs between y and x — rewriting is a wrong value"
        );
    }
}

#[test]
fn ubfx_within_low_bits_is_rewritten_and_beyond_is_not() {
    // UBFM Rd, Rn, #immr, #imms — highest bit read is imms.
    let (mut func, _) = seq(
        17,
        MachInst::new(AArch64Opcode::Ubfm, vec![v(3), v(2), imm(8), imm(11)]),
    );
    assert!(XorshiftDemandedBits.run(&mut func));
    assert!(reads_x(&func, 1), "bits 8..11 all below 17");

    let (mut func, _) = seq(
        17,
        MachInst::new(AArch64Opcode::Ubfm, vec![v(3), v(2), imm(8), imm(20)]),
    );
    XorshiftDemandedBits.run(&mut func);
    assert!(!reads_x(&func, 1), "imms=20 reaches above the shift");
}

#[test]
fn and_mask_within_low_bits_is_rewritten_and_beyond_is_not() {
    // `s & 6` — bits 1..2, well below 17.
    let (mut func, _) = seq(
        17,
        MachInst::new(AArch64Opcode::AndRI, vec![v(3), v(2), imm(6)]),
    );
    assert!(XorshiftDemandedBits.run(&mut func));
    assert!(reads_x(&func, 1));

    // A mask whose top set bit is at or above k must NOT be rewritten.
    let (mut func, _) = seq(
        17,
        MachInst::new(AArch64Opcode::AndRI, vec![v(3), v(2), imm(1 << 17)]),
    );
    XorshiftDemandedBits.run(&mut func);
    assert!(!reads_x(&func, 1), "bit 17 is not preserved");
}

/// A two-source EOR that merely carries a shift is NOT `x ^ (x << k)`.
#[test]
fn distinct_sources_are_not_a_xorshift() {
    let (mut func, _) = {
        let mut func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        for i in [
            // note: operands 1 and 2 differ
            MachInst::new(AArch64Opcode::EorRRLsl, vec![v(2), v(1), v(9), imm(17)]),
            MachInst::new(AArch64Opcode::Tbz, vec![v(2), imm(0), imm(0)]),
        ] {
            let id = func.push_inst(i);
            func.append_inst(entry, id);
        }
        (func, entry)
    };
    XorshiftDemandedBits.run(&mut func);
    assert!(
        !reads_x(&func, 0),
        "y = a ^ (b << k) preserves nothing of a"
    );
}
