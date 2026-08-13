// trust-cg-opt - Multiply-by-small-constant strength-reduction tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::HashMap;

use super::*;
use trust_cg_ir::{BlockId, RegClass, Signature};

// ---------------------------------------------------------------------------
// `decompose` — the arithmetic core
// ---------------------------------------------------------------------------

fn terms(pos_shift: &[(bool, u32)]) -> Vec<Term> {
    pos_shift
        .iter()
        .map(|&(positive, shift)| Term { positive, shift })
        .collect()
}

/// The integer value a term list evaluates to (independent re-derivation of the
/// decomposition, used to cross-check every `decompose` result).
fn value_of(ts: &[Term]) -> i128 {
    ts.iter()
        .map(|t| {
            let m = 1i128 << t.shift;
            if t.positive { m } else { -m }
        })
        .sum()
}

#[test]
fn decompose_powers_and_pm_one() {
    assert_eq!(decompose(2, 64), Some(terms(&[(true, 1)])));
    assert_eq!(decompose(4, 64), Some(terms(&[(true, 2)])));
    assert_eq!(decompose(8, 64), Some(terms(&[(true, 3)])));
    assert_eq!(decompose(16, 64), Some(terms(&[(true, 4)])));
    // 3 = 2 + 1
    assert_eq!(decompose(3, 64), Some(terms(&[(true, 1), (true, 0)])));
    // 5 = 4 + 1, 9 = 8 + 1, 17 = 16 + 1
    assert_eq!(decompose(5, 64), Some(terms(&[(true, 2), (true, 0)])));
    assert_eq!(decompose(9, 64), Some(terms(&[(true, 3), (true, 0)])));
    assert_eq!(decompose(17, 64), Some(terms(&[(true, 4), (true, 0)])));
    // 7 = 8 - 1, 15 = 16 - 1
    assert_eq!(decompose(7, 64), Some(terms(&[(true, 3), (false, 0)])));
    assert_eq!(decompose(15, 64), Some(terms(&[(true, 4), (false, 0)])));
}

#[test]
fn decompose_bails_on_two_shift_forms() {
    // Two-shift forms (both powers >= 2) are throughput-risky and BAIL:
    // 6=4+2, 10=8+2, 12=8+4, 24=16+8, 96=64+32, 20=16+4, 18=16+2.
    for c in [6i128, 10, 12, 14, 18, 20, 24, 96] {
        assert_eq!(decompose(c, 64), None, "two-shift {c} must bail");
    }
}

#[test]
fn decompose_negative_via_minus_form() {
    // -3 = 1 - 4  (leading positive: x - (x<<2))
    let ts = decompose(-3, 64).expect("-3 must decompose");
    assert_eq!(value_of(&ts), -3);
    assert!(
        ts.iter().any(|t| t.positive),
        "must keep a leading positive"
    );
    // -7 = 1 - 8
    let ts = decompose(-7, 64).expect("-7 must decompose");
    assert_eq!(value_of(&ts), -7);
    assert!(ts.iter().any(|t| t.positive));
}

#[test]
fn decompose_bails_on_three_term_and_degenerate() {
    // 11 = 8+2+1, 13 = 8+4+1 — three nonzero terms, cannot be ≤2 signed powers.
    assert_eq!(decompose(11, 64), None);
    assert_eq!(decompose(13, 64), None);
    assert_eq!(decompose(19, 64), None);
    assert_eq!(decompose(23, 64), None);
    // Degenerate multipliers are left to const-fold, not this pass.
    assert_eq!(decompose(0, 64), None);
    assert_eq!(decompose(1, 64), None);
    assert_eq!(decompose(-1, 64), None);
    // `-6 = 2 - 8` and `-10 = -(8+2)` are two-shift / (-,-) — both bail.
    assert_eq!(decompose(-6, 64), None);
    assert_eq!(decompose(-10, 64), None);
    // `-11 = -(8+2+1)` is a three-term negative — bails.
    assert_eq!(decompose(-11, 64), None);
}

#[test]
fn decompose_respects_width_shift_range() {
    // For a 32-bit op every shift must be < 32.
    for c in [3i128, 5, 6, 7, 9, 10, 15, 17, -3] {
        if let Some(ts) = decompose(c, 32) {
            assert!(ts.iter().all(|t| t.shift < 32));
            assert_eq!(value_of(&ts), c);
        }
    }
}

// ---------------------------------------------------------------------------
// End-to-end rewrite: build a MulRR/Madd, evaluate before and after the pass,
// assert bit-exact equality (a differential correctness oracle) and that the
// hardware multiply is gone.
// ---------------------------------------------------------------------------

fn v(id: u32, class: RegClass) -> MachOperand {
    MachOperand::VReg(VReg::new(id, class))
}

fn mask(x: u64, width: u32) -> u64 {
    if width == 32 { x & 0xFFFF_FFFF } else { x }
}

/// Emit a constant materialization into `dst` (id) — `Movz` for a small
/// non-negative value, `Movn` for a small negative — mirroring isel.
fn emit_const(func: &mut MachFunction, block: BlockId, dst: MachOperand, value: i64) {
    let inst = if (0..=0xFFFF).contains(&value) {
        MachInst::new(AArch64Opcode::Movz, vec![dst, MachOperand::Imm(value)])
    } else {
        let n = (!value) & 0xFFFF;
        assert!(
            (0..=0xFFFF).contains(&n),
            "test only materializes constants whose Movn imm fits"
        );
        MachInst::new(AArch64Opcode::Movn, vec![dst, MachOperand::Imm(n)])
    };
    let id = func.push_inst(inst);
    func.append_inst(block, id);
}

fn push(func: &mut MachFunction, block: BlockId, inst: MachInst) {
    let id = func.push_inst(inst);
    func.append_inst(block, id);
}

/// Evaluate a straight-line block for the subset of opcodes this pass produces
/// or consumes. `inputs` seeds registers with no in-block definition (the
/// multiplicand `x`).
fn eval(
    func: &MachFunction,
    block: BlockId,
    inputs: &HashMap<u32, u64>,
    width: u32,
) -> HashMap<u32, u64> {
    let mut vals = inputs.clone();
    let rd = |o: &MachOperand, vals: &HashMap<u32, u64>| -> u64 {
        match o {
            MachOperand::VReg(reg) => *vals
                .get(&reg.id)
                .unwrap_or_else(|| panic!("read of undefined v{}", reg.id)),
            _ => panic!("expected register operand"),
        }
    };
    let imm = |o: &MachOperand| -> i64 {
        match o {
            MachOperand::Imm(k) => *k,
            _ => panic!("expected imm operand"),
        }
    };
    for &iid in &func.block(block).insts {
        let inst = func.inst(iid);
        let ops = &inst.operands;
        let (dst_id, val) = match inst.opcode {
            AArch64Opcode::Movz => {
                let shift = ops.get(2).map(&imm).unwrap_or(0);
                let val = (imm(&ops[1]) as u64) << shift;
                (vreg_id(&ops[0]), mask(val, width))
            }
            AArch64Opcode::Movn => {
                let shift = ops.get(2).map(&imm).unwrap_or(0);
                let val = !((imm(&ops[1]) as u64) << shift);
                (vreg_id(&ops[0]), mask(val, width))
            }
            AArch64Opcode::LslRI => {
                let val = rd(&ops[1], &vals) << (imm(&ops[2]) as u32);
                (vreg_id(&ops[0]), mask(val, width))
            }
            AArch64Opcode::AddRR => {
                let val = rd(&ops[1], &vals).wrapping_add(rd(&ops[2], &vals));
                (vreg_id(&ops[0]), mask(val, width))
            }
            AArch64Opcode::SubRR => {
                let val = rd(&ops[1], &vals).wrapping_sub(rd(&ops[2], &vals));
                (vreg_id(&ops[0]), mask(val, width))
            }
            AArch64Opcode::MulRR => {
                let val = rd(&ops[1], &vals).wrapping_mul(rd(&ops[2], &vals));
                (vreg_id(&ops[0]), mask(val, width))
            }
            AArch64Opcode::Madd => {
                let prod = rd(&ops[1], &vals).wrapping_mul(rd(&ops[2], &vals));
                let val = rd(&ops[3], &vals).wrapping_add(prod);
                (vreg_id(&ops[0]), mask(val, width))
            }
            _ => continue,
        };
        vals.insert(dst_id, val);
    }
    vals
}

fn vreg_id(o: &MachOperand) -> u32 {
    match o {
        MachOperand::VReg(r) => r.id,
        _ => panic!("expected vreg dst"),
    }
}

fn new_func() -> (MachFunction, BlockId) {
    let func = MachFunction::new("t".into(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    (func, entry)
}

/// Fixed multiplicand test vectors exercising sign, small, and high bits.
const X_VECS: [u64; 6] = [
    0,
    1,
    7,
    0x0000_0000_DEAD_BEEF,
    0xFFFF_FFFF_FFFF_FFFD,
    0x8000_0000_0000_0001,
];

fn opcodes(func: &MachFunction, block: BlockId) -> Vec<AArch64Opcode> {
    func.block(block)
        .insts
        .iter()
        .map(|&i| func.inst(i).opcode)
        .collect()
}

/// Build `dst = x * c (+ y)` and assert the rewrite is bit-exact for every
/// multiplicand, and that the hardware multiply disappeared.
fn check_fires(class: RegClass, c: i64, addend: Option<i64>) {
    let width = class.size_bits();
    // ids: x=0, cReg=1, yReg=2, dst=3.
    let x = v(0, class);
    let creg = v(1, class);
    let yreg = v(2, class);
    let dst = v(3, class);

    let (mut func, entry) = new_func();
    emit_const(&mut func, entry, creg.clone(), c);
    if let Some(y) = addend {
        emit_const(&mut func, entry, yreg.clone(), y);
    }
    let mul = match addend {
        None => MachInst::new(
            AArch64Opcode::MulRR,
            vec![dst.clone(), x.clone(), creg.clone()],
        ),
        Some(_) => MachInst::new(
            AArch64Opcode::Madd,
            vec![dst.clone(), x.clone(), creg.clone(), yreg.clone()],
        ),
    };
    push(&mut func, entry, mul);
    // Fresh vregs must not alias the test ids.
    func.next_vreg = 1000;

    for &xv in &X_VECS {
        let mut inputs = HashMap::new();
        inputs.insert(0u32, mask(xv, width));

        // Snapshot the reference value from the ORIGINAL mul/madd.
        let before = eval(&func, entry, &inputs, width);
        let expected = before[&3];

        // Sanity: the reference equals x*c (+y) mod 2^W (independent formula).
        let indep = {
            let xw = mask(xv, width);
            let prod = xw.wrapping_mul(c as u64);
            let base = addend.map(|y| mask(y as u64, width)).unwrap_or(0);
            mask(base.wrapping_add(prod), width)
        };
        assert_eq!(expected, indep, "reference formula mismatch for c={c}");

        // Run the pass on a fresh clone so opcode assertions see one rewrite.
        let mut f2 = func.clone();
        let mut pass = MulShiftReduce;
        assert!(
            pass.run(&mut f2),
            "pass must fire for c={c} addend={addend:?}"
        );
        let after = eval(&f2, entry, &inputs, width);
        assert_eq!(
            after[&3], expected,
            "rewrite changed the value for c={c} addend={addend:?} x={xv:#x}"
        );

        let ops = opcodes(&f2, entry);
        assert!(
            !ops.contains(&AArch64Opcode::MulRR) && !ops.contains(&AArch64Opcode::Madd),
            "hardware multiply must be gone for c={c} addend={addend:?}: {ops:?}"
        );
        assert!(
            ops.iter().all(|o| matches!(
                o,
                AArch64Opcode::Movz
                    | AArch64Opcode::Movn
                    | AArch64Opcode::LslRI
                    | AArch64Opcode::AddRR
                    | AArch64Opcode::SubRR
            )),
            "only shift/add/sub + const-materialize may remain: {ops:?}"
        );
    }
}

#[test]
fn mulrr_fires_all_small_constants_64() {
    for c in [2i64, 3, 4, 5, 7, 8, 9, 15, 16, 17, -3] {
        check_fires(RegClass::Gpr64, c, None);
    }
}

#[test]
fn mulrr_fires_all_small_constants_32() {
    for c in [2i64, 3, 4, 5, 7, 8, 9, 15, 16, 17, -3] {
        check_fires(RegClass::Gpr32, c, None);
    }
}

#[test]
fn madd_fires_all_small_constants_64() {
    // Madd(x, c, y) = y + x*c — the p2_collatz `c*3 + 1` shape included.
    for c in [2i64, 3, 4, 5, 7, 8, 9, 15, 16, 17, -3] {
        check_fires(RegClass::Gpr64, c, Some(1));
    }
}

#[test]
fn madd_fires_all_small_constants_32() {
    for c in [2i64, 3, 5, 7, 9, 15, 17, -3] {
        check_fires(RegClass::Gpr32, c, Some(1));
    }
}

#[test]
fn collatz_madd_by_3_lowers_to_shift_add() {
    // MADD dst, x, #3, #1  (dst = x*3 + 1) -> LslRI + AddRR + AddRR, NO madd.
    let class = RegClass::Gpr64;
    let x = v(0, class);
    let creg = v(1, class);
    let yreg = v(2, class);
    let dst = v(3, class);
    let (mut func, entry) = new_func();
    emit_const(&mut func, entry, creg.clone(), 3);
    emit_const(&mut func, entry, yreg.clone(), 1);
    push(
        &mut func,
        entry,
        MachInst::new(AArch64Opcode::Madd, vec![dst, x, creg, yreg]),
    );
    func.next_vreg = 1000;

    let mut pass = MulShiftReduce;
    assert!(pass.run(&mut func));
    let ops = opcodes(&func, entry);
    assert!(!ops.contains(&AArch64Opcode::Madd), "madd gone: {ops:?}");
    assert_eq!(
        ops.iter().filter(|o| **o == AArch64Opcode::LslRI).count(),
        1,
        "one shift (x<<1): {ops:?}"
    );
    assert_eq!(
        ops.iter().filter(|o| **o == AArch64Opcode::AddRR).count(),
        2,
        "two adds ((x+1) + (x<<1)): {ops:?}"
    );
    // The single shift is by 1 (x*3 = x + x<<1).
    let shift_amt = func
        .block(entry)
        .insts
        .iter()
        .map(|&i| func.inst(i))
        .find(|i| i.opcode == AArch64Opcode::LslRI)
        .and_then(|i| i.operands[2].as_imm())
        .unwrap();
    assert_eq!(shift_amt, 1);
}

// ---------------------------------------------------------------------------
// BAIL controls — the multiply MUST survive unchanged.
// ---------------------------------------------------------------------------

fn assert_bails(build: impl FnOnce(&mut MachFunction, BlockId)) {
    let (mut func, entry) = new_func();
    build(&mut func, entry);
    func.next_vreg = 1000;
    let before = opcodes(&func, entry);
    let mut pass = MulShiftReduce;
    let changed = pass.run(&mut func);
    assert!(!changed, "pass must not fire");
    assert_eq!(opcodes(&func, entry), before, "block must be unchanged");
}

#[test]
fn bails_on_three_term_constant_11() {
    let class = RegClass::Gpr64;
    assert_bails(|func, e| {
        emit_const(func, e, v(1, class), 11);
        push(
            func,
            e,
            MachInst::new(
                AArch64Opcode::MulRR,
                vec![v(3, class), v(0, class), v(1, class)],
            ),
        );
    });
}

#[test]
fn bails_on_three_term_constant_13() {
    let class = RegClass::Gpr64;
    assert_bails(|func, e| {
        emit_const(func, e, v(1, class), 13);
        push(
            func,
            e,
            MachInst::new(
                AArch64Opcode::MulRR,
                vec![v(3, class), v(0, class), v(1, class)],
            ),
        );
    });
}

#[test]
fn bails_when_multiplier_is_runtime_value() {
    // The multiplier v1 is produced by an ADD, not a constant materialization.
    let class = RegClass::Gpr64;
    assert_bails(|func, e| {
        push(
            func,
            e,
            MachInst::new(
                AArch64Opcode::AddRR,
                vec![v(1, class), v(4, class), v(5, class)],
            ),
        );
        push(
            func,
            e,
            MachInst::new(
                AArch64Opcode::MulRR,
                vec![v(3, class), v(0, class), v(1, class)],
            ),
        );
    });
}

#[test]
fn bails_when_neither_operand_is_constant() {
    // Both multiply operands are plain (undefined) registers.
    let class = RegClass::Gpr64;
    assert_bails(|func, e| {
        push(
            func,
            e,
            MachInst::new(
                AArch64Opcode::MulRR,
                vec![v(3, class), v(0, class), v(1, class)],
            ),
        );
    });
}

#[test]
fn bails_on_ambiguous_two_reaching_defs() {
    // Two different Movz values reach the multiply on merging paths → the sound
    // reaching-const query returns None → BAIL (no miscompile of the wrong K).
    let class = RegClass::Gpr64;
    let (mut func, entry) = new_func();
    let (b1, b2, b3) = (
        func.create_block(),
        func.create_block(),
        func.create_block(),
    );
    func.block_order = vec![entry, b1, b2, b3];
    func.add_edge(entry, b1);
    func.add_edge(entry, b2);
    func.add_edge(b1, b3);
    func.add_edge(b2, b3);
    emit_const(&mut func, b1, v(1, class), 3);
    push(
        &mut func,
        b1,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(b3)]),
    );
    emit_const(&mut func, b2, v(1, class), 5);
    push(
        &mut func,
        b2,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(b3)]),
    );
    push(
        &mut func,
        b3,
        MachInst::new(
            AArch64Opcode::MulRR,
            vec![v(3, class), v(0, class), v(1, class)],
        ),
    );
    func.next_vreg = 1000;
    let before = opcodes(&func, b3);
    let mut pass = MulShiftReduce;
    assert!(!pass.run(&mut func), "ambiguous constant must bail");
    assert_eq!(opcodes(&func, b3), before);
}
