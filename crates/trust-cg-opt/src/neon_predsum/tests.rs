// Unit tests for the `neon-predsum` predicated-sum array-reduction vectorizer.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use trust_cg_ir::Signature;

fn v(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
}
fn v64(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn i(x: i64) -> MachOperand {
    MachOperand::Imm(x)
}
fn b(x: BlockId) -> MachOperand {
    MachOperand::Block(x)
}
fn count(func: &MachFunction, op: AArch64Opcode) -> usize {
    func.blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .filter(|&id| func.inst(id).opcode == op)
        .count()
}

/// What predicate the built select uses (mirrors the materialised `CmpRR; CSet;
/// CmpRI(_,0); Csel(NE)` chain ISel emits for `select(icmp)`).
#[derive(Clone, Copy)]
enum Sel {
    /// `(a[i] > 0) ? a[i] : 0`  (cc_real = GT, arms = load / 0).
    ClampPos,
    /// `(a[i] > b[i]) ? a[i] : b[i]`  (cc_real = GT, two arrays, arms = a / b).
    TwoMax,
    /// `(a[i] < 0) ? -a[i] : a[i]`  (abs-sum; arms are NOT the compare operands,
    /// so it exercises the CMGT + EOR/AND bitselect path, not min/max).
    Abs,
    /// `(a[i] > 0) ? 1 : 0`  (count positives) — the term ROOT is a counting
    /// select, so it exercises the root-select COUNTING fusion (CMGT + one SUB
    /// of the mask straight into the accumulator; clang's CMEQ+SUB shape).
    MaskConst,
    /// `(a[i] > 0) ? 5 : 0` — ELSE arm 0 but K != 1, so the counting fusion does
    /// NOT fire; exercises the masked-constant `mask & K` path (CMGT + one AND).
    MaskConstK,
    /// pure `s += a[i]` — NO select (must BAIL to neon-array).
    PureSum,
    /// min/max reduction `m = (a[i] > m) ? a[i] : m` — Csel-ROOTED acc (must BAIL
    /// to neon-minmax; the reduction root is the select itself, not an AddRR).
    MinMaxRoot,
}

/// Build the rotated predicated-sum loop in the exact shape `loop-latch-layout`
/// emits (guard / header / latch), for the given select flavour.
///
/// Register map: v0=base_a(ptr), v1=n, v2=base_b(ptr). v3=0, v4=1, v40=4(es).
/// iv=v5, acc=v6.
fn build_predsum_loop(sel: Sel) -> MachFunction {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let guard = func.create_block();
    let header = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;
    // Preheader: base pointers + constants; iv=0, acc=0.
    push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base_a
    push(&mut func, bb0, Copy, vec![v(1), v(1)]); // n
    push(&mut func, bb0, Copy, vec![v64(2), v64(2)]); // base_b
    push(&mut func, bb0, Movz, vec![v(3), i(0)]);
    push(&mut func, bb0, Movz, vec![v(4), i(1)]);
    push(&mut func, bb0, Movz, vec![v64(40), i(4)]); // element size
    push(&mut func, bb0, MovR, vec![v(5), v(3)]); // iv = 0
    push(&mut func, bb0, MovR, vec![v(6), v(3)]); // acc = 0
    if matches!(sel, Sel::MaskConstK) {
        push(&mut func, bb0, Movz, vec![v(41), i(5)]); // K = 5
    }
    push(&mut func, bb0, B, vec![b(guard)]);
    // Guard: cmp iv,n; b.lt header; b exit.
    push(&mut func, guard, CmpRR, vec![v(5), v(1)]);
    push(&mut func, guard, BCond, vec![i(CC_LT), b(header)]);
    push(&mut func, guard, B, vec![b(exit)]);
    // Header: address + load a[i].
    push(&mut func, header, Sxtw, vec![v64(10), v(5)]);
    push(
        &mut func,
        header,
        Madd,
        vec![v64(11), v64(10), v64(40), v64(0)],
    ); // a + iv*4
    push(&mut func, header, LdrRI, vec![v(12), v64(11), i(0)]); // load a[i]

    // The reduction / select body.
    match sel {
        Sel::ClampPos => {
            // (a[i] > 0) ? a[i] : 0
            push(&mut func, header, CmpRR, vec![v(12), v(3)]); // cmp a[i], 0
            push(&mut func, header, CSet, vec![v64(13), i(CC_GT)]);
            push(&mut func, header, CmpRI, vec![v64(13), i(0)]);
            push(&mut func, header, Csel, vec![v(14), v(12), v(3), i(CC_NE)]);
            push(&mut func, header, AddRR, vec![v(16), v(6), v(14)]); // acc + sel
        }
        Sel::TwoMax => {
            // (a[i] > b[i]) ? a[i] : b[i]
            push(&mut func, header, Sxtw, vec![v64(20), v(5)]);
            push(
                &mut func,
                header,
                Madd,
                vec![v64(21), v64(20), v64(40), v64(2)],
            ); // b + iv*4
            push(&mut func, header, LdrRI, vec![v(22), v64(21), i(0)]); // load b[i]
            push(&mut func, header, CmpRR, vec![v(12), v(22)]); // cmp a[i], b[i]
            push(&mut func, header, CSet, vec![v64(13), i(CC_GT)]);
            push(&mut func, header, CmpRI, vec![v64(13), i(0)]);
            push(&mut func, header, Csel, vec![v(14), v(12), v(22), i(CC_NE)]);
            push(&mut func, header, AddRR, vec![v(16), v(6), v(14)]); // acc + sel
        }
        Sel::Abs => {
            // (a[i] < 0) ? -a[i] : a[i]  — arms are -a[i] and a[i] (not the
            // compare operands a[i], 0), so this is a genuine bitselect.
            push(&mut func, header, SubRR, vec![v(18), v(3), v(12)]); // -a[i] = 0 - a[i]
            push(&mut func, header, CmpRR, vec![v(12), v(3)]); // cmp a[i], 0
            push(&mut func, header, CSet, vec![v64(13), i(CC_LT)]);
            push(&mut func, header, CmpRI, vec![v64(13), i(0)]);
            push(&mut func, header, Csel, vec![v(14), v(18), v(12), i(CC_NE)]);
            push(&mut func, header, AddRR, vec![v(16), v(6), v(14)]); // acc + sel
        }
        Sel::MaskConst => {
            // (a[i] > 0) ? 1 : 0 — a ROOT counting select (arms are the
            // constants 1 and 0) -> counting fusion `acc -= mask`.
            push(&mut func, header, CmpRR, vec![v(12), v(3)]); // cmp a[i], 0
            push(&mut func, header, CSet, vec![v64(13), i(CC_GT)]);
            push(&mut func, header, CmpRI, vec![v64(13), i(0)]);
            push(&mut func, header, Csel, vec![v(14), v(4), v(3), i(CC_NE)]); // 1 : 0
            push(&mut func, header, AddRR, vec![v(16), v(6), v(14)]); // acc + sel
        }
        Sel::MaskConstK => {
            // (a[i] > 0) ? 5 : 0 — K != 1, counting fusion must NOT fire;
            // stays on the masked-const `mask & K` path. (K=5 in v41, preheader.)
            push(&mut func, header, CmpRR, vec![v(12), v(3)]); // cmp a[i], 0
            push(&mut func, header, CSet, vec![v64(13), i(CC_GT)]);
            push(&mut func, header, CmpRI, vec![v64(13), i(0)]);
            push(&mut func, header, Csel, vec![v(14), v(41), v(3), i(CC_NE)]); // 5 : 0
            push(&mut func, header, AddRR, vec![v(16), v(6), v(14)]); // acc + sel
        }
        Sel::PureSum => {
            push(&mut func, header, AddRR, vec![v(16), v(6), v(12)]); // acc + a[i], no select
        }
        Sel::MinMaxRoot => {
            // m = (a[i] > m) ? a[i] : m  — the select IS the reduction (acc-rooted)
            push(&mut func, header, CmpRR, vec![v(12), v(6)]); // cmp a[i], acc
            push(&mut func, header, CSet, vec![v64(13), i(CC_GT)]);
            push(&mut func, header, CmpRI, vec![v64(13), i(0)]);
            push(&mut func, header, Csel, vec![v(16), v(12), v(6), i(CC_NE)]); // acc' = sel
        }
    }
    push(&mut func, header, AddRR, vec![v(17), v(5), v(4)]); // iv+1
    push(&mut func, header, B, vec![b(latch)]);
    push(&mut func, latch, AddRI, vec![v(5), v(17), i(0)]);
    push(&mut func, latch, AddRI, vec![v(6), v(16), i(0)]);
    push(&mut func, latch, CmpRR, vec![v(5), v(1)]);
    push(&mut func, latch, BCond, vec![i(CC_LT), b(header)]);
    // Exit.
    push(&mut func, exit, MovR, vec![v(30), v(6)]);
    push(&mut func, exit, Ret, vec![]);

    func.add_edge(bb0, guard);
    func.add_edge(guard, header);
    func.add_edge(guard, exit);
    func.add_edge(header, latch);
    func.add_edge(latch, header);
    func.add_edge(latch, exit);
    func.next_vreg = 128;
    func
}

#[test]
fn vectorizes_clamp_pos() {
    let mut func = build_predsum_loop(Sel::ClampPos);
    let mut pass = NeonPredSumPass::new();
    assert!(pass.run(&mut func), "should fire on `s += (a[i]>0)?a[i]:0`");
    assert_eq!(pass.fired(), 1);
    // 4 accumulators × 1 array = 2 LDP Q-pair loads.
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        UNROLL / 2,
        "2 LDP q,q"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLd1Post),
        0,
        "LD1 replaced by LDP"
    );
    // `(a>0)?a:0` = max(a,0): the min/max fast path emits one SMAX per
    // accumulator (no compare mask / bitselect).
    assert_eq!(count(&func, AArch64Opcode::NeonSmaxV), UNROLL, "4 SMAX");
    assert_eq!(count(&func, AArch64Opcode::NeonCmgtV), 0, "no compare mask");
    assert_eq!(count(&func, AArch64Opcode::NeonEorV), 0, "no bitselect");
    // Add-reduction: 4 accumulate + 3 combine.
    assert!(
        count(&func, AArch64Opcode::NeonAddV) >= UNROLL,
        "accumulate"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonUmovGen),
        4,
        "reduce 4 lanes"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonMovi), UNROLL, "zeroed accs");
}

#[test]
fn vectorizes_counting_select_via_sub() {
    // `(a[i] > 0) ? 1 : 0` at the term ROOT — the counting fusion accumulates
    // by SUBTRACTING the compare mask (one CMGT + one SUB per accumulator;
    // clang's compare+SUB counting shape). No AND, no bitselect, and no
    // per-accumulator term ADD (the remaining NeonAddV are the combine tree).
    let mut func = build_predsum_loop(Sel::MaskConst);
    let mut pass = NeonPredSumPass::new();
    assert!(pass.run(&mut func), "should fire on `s += (a[i]>0)?1:0`");
    assert_eq!(pass.fired(), 1);
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        UNROLL / 2,
        "2 LDP q,q"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmgtV),
        UNROLL,
        "4 CMGT masks"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonSubV),
        UNROLL,
        "4 acc-=mask SUB"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonAndV), 0, "no mask&K AND");
    assert_eq!(count(&func, AArch64Opcode::NeonEorV), 0, "no bitselect EOR");
    assert_eq!(count(&func, AArch64Opcode::NeonSmaxV), 0, "not a min/max");
    assert_eq!(
        count(&func, AArch64Opcode::NeonAddV),
        UNROLL - 1,
        "only the accumulator-combine adds remain"
    );
}

#[test]
fn vectorizes_masked_const_via_and() {
    // `(a[i] > 0) ? 5 : 0` — ELSE arm 0 but K != 1, so the counting fusion must
    // NOT fire; the select lowers to `mask & K` (one CMGT + one proven AND per
    // accumulator) and accumulates via the normal ADD.
    let mut func = build_predsum_loop(Sel::MaskConstK);
    let mut pass = NeonPredSumPass::new();
    assert!(pass.run(&mut func), "should fire on `s += (a[i]>0)?5:0`");
    assert_eq!(pass.fired(), 1);
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        UNROLL / 2,
        "2 LDP q,q"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmgtV),
        UNROLL,
        "4 CMGT masks"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonAndV),
        UNROLL,
        "4 mask&K AND"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonSubV), 0, "no counting SUB");
    assert_eq!(count(&func, AArch64Opcode::NeonEorV), 0, "no bitselect EOR");
    assert_eq!(count(&func, AArch64Opcode::NeonSmaxV), 0, "not a min/max");
}

#[test]
fn vectorizes_two_array_max() {
    let mut func = build_predsum_loop(Sel::TwoMax);
    let mut pass = NeonPredSumPass::new();
    assert!(
        pass.run(&mut func),
        "should fire on `s += (a[i]>b[i])?a[i]:b[i]`"
    );
    assert_eq!(pass.fired(), 1);
    // 4 accumulators × 2 arrays = 4 LDP Q-pair loads.
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        UNROLL,
        "4 LDP q,q"
    );
    // `(a>b)?a:b` = max(a,b): one SMAX per accumulator.
    assert_eq!(count(&func, AArch64Opcode::NeonSmaxV), UNROLL, "4 SMAX");
}

#[test]
fn vectorizes_abs_via_neon_abs() {
    // `(a[i]<0)?-a[i]:a[i]` = |a[i]| — the abs fast path recognizes `neg = 0-a`
    // + sign-test and lowers to a SINGLE proven `ABS.4S` (`NeonAbsV`) per
    // accumulator, replacing BOTH the old negating SUB + SMAX pair AND the 5-op
    // CMGT + EOR/AND bitselect.
    let mut func = build_predsum_loop(Sel::Abs);
    let mut pass = NeonPredSumPass::new();
    assert!(pass.run(&mut func), "should fire on abs-sum");
    assert_eq!(pass.fired(), 1);
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        UNROLL / 2,
        "2 LDP q,q"
    );
    // One ABS.4S per accumulator; NO SMAX, NO negate SUB, NO compare mask, NO bitselect.
    assert_eq!(
        count(&func, AArch64Opcode::NeonAbsV),
        UNROLL,
        "4 ABS.4S (abs)"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonSmaxV),
        0,
        "no SMAX (abs is one op)"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonSubV),
        0,
        "no negate SUB for abs"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonCmgtV), 0, "no compare mask");
    assert_eq!(count(&func, AArch64Opcode::NeonEorV), 0, "no bitselect");
    assert_eq!(count(&func, AArch64Opcode::NeonAndV), 0, "no bitselect");
}

#[test]
fn bails_on_pure_sum_no_select() {
    // Pure `s += a[i]` (no select) must BAIL — that belongs to neon-array.
    let mut func = build_predsum_loop(Sel::PureSum);
    let mut pass = NeonPredSumPass::new();
    assert!(
        !pass.run(&mut func),
        "pure add reduction must BAIL (no select)"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLd1Post),
        0,
        "no NEON emitted"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        0,
        "no NEON emitted"
    );
}

#[test]
fn bails_on_minmax_root() {
    // `m = (a[i] > m) ? a[i] : m` is a Csel-ROOTED reduction (acc appears in the
    // select) — that belongs to neon-minmax; the root is not an AddRR.
    let mut func = build_predsum_loop(Sel::MinMaxRoot);
    let mut pass = NeonPredSumPass::new();
    assert!(
        !pass.run(&mut func),
        "Csel-rooted min/max reduction must BAIL"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLd1Post),
        0,
        "no NEON emitted"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        0,
        "no NEON emitted"
    );
}

/// i64 clamp-sum `s += (a[i] > 0) ? a[i] : 0` now VECTORIZES on the `.2D` path
/// (this was the `bails_on_i64` fail-closed pin before the width
/// parameterization): the compare mask is `CMGT.2D` and the masked-constant
/// zero-else fast path emits ONE proven `AND`; the guard is the i64 precheck +
/// unsigned-compare pair. The single-op SMAX/ABS fast paths must NOT appear
/// (no `.2D` form exists).
#[test]
fn vectorizes_i64_clamp_sum_on_2d() {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let guard = func.create_block();
    let header = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();
    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;
    push(&mut func, bb0, Copy, vec![v64(0), v64(0)]);
    push(&mut func, bb0, Copy, vec![v64(1), v64(1)]); // n (i64)
    push(&mut func, bb0, Movz, vec![v64(3), i(0)]);
    push(&mut func, bb0, Movz, vec![v64(4), i(1)]);
    push(&mut func, bb0, Movz, vec![v64(40), i(8)]);
    push(&mut func, bb0, MovR, vec![v64(5), v64(3)]);
    push(&mut func, bb0, MovR, vec![v64(6), v64(3)]);
    push(&mut func, bb0, B, vec![b(guard)]);
    push(&mut func, guard, CmpRR, vec![v64(5), v64(1)]);
    push(&mut func, guard, BCond, vec![i(CC_LT), b(header)]);
    push(&mut func, guard, B, vec![b(exit)]);
    push(
        &mut func,
        header,
        Madd,
        vec![v64(11), v64(5), v64(40), v64(0)],
    ); // a + iv*8
    push(&mut func, header, LdrRI, vec![v64(12), v64(11), i(0)]);
    push(&mut func, header, CmpRR, vec![v64(12), v64(3)]);
    push(&mut func, header, CSet, vec![v64(13), i(CC_GT)]);
    push(&mut func, header, CmpRI, vec![v64(13), i(0)]);
    push(
        &mut func,
        header,
        Csel,
        vec![v64(14), v64(12), v64(3), i(CC_NE)],
    );
    push(&mut func, header, AddRR, vec![v64(16), v64(6), v64(14)]);
    push(&mut func, header, AddRR, vec![v64(17), v64(5), v64(4)]);
    push(&mut func, header, B, vec![b(latch)]);
    push(&mut func, latch, AddRI, vec![v64(5), v64(17), i(0)]);
    push(&mut func, latch, AddRI, vec![v64(6), v64(16), i(0)]);
    push(&mut func, latch, CmpRR, vec![v64(5), v64(1)]);
    push(&mut func, latch, BCond, vec![i(CC_LT), b(header)]);
    push(&mut func, exit, Ret, vec![]);
    func.add_edge(bb0, guard);
    func.add_edge(guard, header);
    func.add_edge(guard, exit);
    func.add_edge(header, latch);
    func.add_edge(latch, header);
    func.add_edge(latch, exit);
    func.next_vreg = 128;
    let mut pass = NeonPredSumPass::new();
    assert!(pass.run(&mut func), "i64 clamp-sum must vectorize on `.2D`");
    assert_eq!(pass.fired(), 1);
    // 4 accumulators over 1 stream = 2 LDP Q-pair loads.
    assert_eq!(count(&func, AArch64Opcode::NeonLdpQPost), 2, "2 LDP q,q");
    // Per accumulator: CMGT.2D mask + AND (masked-const zero-else) + ADD.2D
    // accumulate; NO single-op SMAX/ABS (no `.2D` form exists).
    assert_eq!(count(&func, AArch64Opcode::NeonCmgtV), 4, "4 CMGT.2D masks");
    assert!(
        count(&func, AArch64Opcode::NeonAndV) >= 4,
        "mask & value per acc"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonSmaxV),
        0,
        "no SMAX.2D exists"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonAbsV), 0, "no .2D ABS proof");
    // Every arrangement-carrying vector op must be `.2D` (imm code 6), never
    // `.4S` — the wrong-lane-width trap this test pins shut.
    for blk in &func.blocks {
        for &id in &blk.insts {
            let inst = func.inst(id);
            if matches!(
                inst.opcode,
                AArch64Opcode::NeonCmgtV | AArch64Opcode::NeonAddV | AArch64Opcode::NeonSubV
            ) {
                let arr = inst.operands.last().and_then(|op| match op {
                    MachOperand::Imm(v) => Some(*v),
                    _ => None,
                });
                assert_eq!(arr, Some(6), "i64 path must emit .2D (code 6), got {arr:?}");
            }
        }
    }
}

/// i64 count-eq `s += (a[i] == k) ? 1 : 0` vectorizes via the root-select
/// COUNTING fusion at `.2D`: one `CMEQ.2D` mask + one `SUB.2D` of the mask per
/// accumulator — exactly clang's shape. `k` is a loop-invariant `Gpr64`
/// broadcast (DUP.2D).
#[test]
fn vectorizes_i64_count_eq_cmeq_sub_2d() {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let guard = func.create_block();
    let header = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();
    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;
    push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base
    push(&mut func, bb0, Copy, vec![v64(1), v64(1)]); // n (i64)
    push(&mut func, bb0, Copy, vec![v64(2), v64(2)]); // k (loop-invariant)
    push(&mut func, bb0, Movz, vec![v64(3), i(0)]);
    push(&mut func, bb0, Movz, vec![v64(4), i(1)]);
    push(&mut func, bb0, Movz, vec![v64(40), i(8)]);
    push(&mut func, bb0, MovR, vec![v64(5), v64(3)]); // iv = 0
    push(&mut func, bb0, MovR, vec![v64(6), v64(3)]); // acc = 0
    push(&mut func, bb0, B, vec![b(guard)]);
    push(&mut func, guard, CmpRR, vec![v64(5), v64(1)]);
    push(&mut func, guard, BCond, vec![i(CC_LT), b(header)]);
    push(&mut func, guard, B, vec![b(exit)]);
    push(
        &mut func,
        header,
        Madd,
        vec![v64(11), v64(5), v64(40), v64(0)],
    );
    push(&mut func, header, LdrRI, vec![v64(12), v64(11), i(0)]);
    push(&mut func, header, CmpRR, vec![v64(12), v64(2)]);
    push(&mut func, header, CSet, vec![v64(13), i(CC_EQ)]);
    push(&mut func, header, CmpRI, vec![v64(13), i(0)]);
    push(
        &mut func,
        header,
        Csel,
        vec![v64(14), v64(4), v64(3), i(CC_NE)],
    ); // ?1:0
    push(&mut func, header, AddRR, vec![v64(16), v64(6), v64(14)]);
    push(&mut func, header, AddRR, vec![v64(17), v64(5), v64(4)]);
    push(&mut func, header, B, vec![b(latch)]);
    push(&mut func, latch, AddRI, vec![v64(5), v64(17), i(0)]);
    push(&mut func, latch, AddRI, vec![v64(6), v64(16), i(0)]);
    push(&mut func, latch, CmpRR, vec![v64(5), v64(1)]);
    push(&mut func, latch, BCond, vec![i(CC_LT), b(header)]);
    push(&mut func, exit, Ret, vec![]);
    func.add_edge(bb0, guard);
    func.add_edge(guard, header);
    func.add_edge(guard, exit);
    func.add_edge(header, latch);
    func.add_edge(latch, header);
    func.add_edge(latch, exit);
    func.next_vreg = 128;
    let mut pass = NeonPredSumPass::new();
    assert!(pass.run(&mut func), "i64 count-eq must vectorize on .2D");
    assert_eq!(pass.fired(), 1);
    // Counting fusion: 4 CMEQ.2D masks + 4 SUB.2D accumulates (no AND path).
    assert_eq!(count(&func, AArch64Opcode::NeonCmeqV), 4, "4 CMEQ.2D masks");
    assert_eq!(
        count(&func, AArch64Opcode::NeonSubV),
        4,
        "acc -= mask per acc"
    );
    // The invariant k is DUP-broadcast at the D element size (code 8).
    let dup_d = func
        .blocks
        .iter()
        .flat_map(|blk| blk.insts.iter())
        .map(|&id| func.inst(id))
        .filter(|inst| inst.opcode == AArch64Opcode::NeonDupGen)
        .filter(|inst| matches!(inst.operands.last(), Some(MachOperand::Imm(8))))
        .count();
    assert!(dup_d >= 1, "loop-invariant k must DUP at .D element size");
}

// ---------------------------------------------------------------------------
// Forward-chain (branch-diamond) recognition — the `if a[i] > t { s += a[i] }`
// condsum over a LOCAL fixed-size array (bounds checks elided to pass-throughs).
// This is the multi-block CFG family the bridge emits (mirrors e01_condsum), a
// near-clone of the just-landed neon_minmax forward chain.
// ---------------------------------------------------------------------------

/// Build the forward-chain condsum loop in the exact shape the bridge emits for
/// a local fixed-size array (`while i < N { if a[i] > t { s += a[i] } }`):
/// header (const-bound `iv <u N` guard) -> pass-through (elided bounds check) ->
/// compare diamond -> {then pass-through -> then body `s += a[i]`, else `+0`} ->
/// latch. Mixed width: `iv` is `Gpr64`, `acc`/`t` are `Gpr32`, elements `.4S`,
/// address `base + iv*4` with `iv` used directly.
///
/// `iv_i64` picks the induction width (the recognizer requires `Gpr64`; passing
/// `false` exercises the fail-closed `Gpr32` BAIL). A DETACHED
/// `TrapBoundsCheckExact` reading the iv-copy is left in `func.insts` (not wired
/// into any block) to pin the `build_live_def_map` "key fix".
fn build_chain_condsum(n: i64, iv_i64: bool) -> MachFunction {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    let header = func.create_block();
    let pass = func.create_block();
    let cmp = func.create_block();
    let then1 = func.create_block();
    let then2 = func.create_block();
    let els = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;
    let ivc = if iv_i64 { v64 } else { v };

    // Preheader: base ptr v0, es v40=4, t v7, iv v5 = 0, acc v6 = 0.
    push(&mut func, entry, Copy, vec![v64(0), v64(0)]); // base
    push(&mut func, entry, Movz, vec![v64(40), i(4)]); // element size
    push(&mut func, entry, Copy, vec![v(7), v(7)]); // t (loop-invariant Gpr32)
    push(&mut func, entry, Movz, vec![ivc(5), i(0)]); // iv = 0
    push(&mut func, entry, Movz, vec![v(6), i(0)]); // acc = 0
    push(&mut func, entry, B, vec![b(header)]);

    // Header guard: MovR ivcopy; CmpRI(ivcopy, N); b.lo pass; b exit.
    push(&mut func, header, MovR, vec![ivc(10), ivc(5)]);
    push(&mut func, header, CmpRI, vec![ivc(10), i(n)]);
    push(&mut func, header, BCond, vec![i(CC_LO), b(pass)]);
    push(&mut func, header, B, vec![b(exit)]);

    // Pass-through (its TrapBoundsCheckExact was elided to a detached carrier).
    push(&mut func, pass, MovR, vec![ivc(11), ivc(5)]);
    push(&mut func, pass, B, vec![b(cmp)]);

    // Compare diamond: addr = base + iv*4; a = load; cmp a, t; b.gt then1; b els.
    push(
        &mut func,
        cmp,
        Madd,
        vec![v64(12), ivc(11), v64(40), v64(0)],
    );
    push(&mut func, cmp, LdrRI, vec![v(13), v64(12), i(0)]);
    push(&mut func, cmp, CmpRR, vec![v(13), v(7)]);
    push(&mut func, cmp, BCond, vec![i(CC_GT), b(then1)]);
    push(&mut func, cmp, B, vec![b(els)]);

    // Then side: pass-through then the `s += a[i]` body.
    push(&mut func, then1, MovR, vec![ivc(14), ivc(5)]);
    push(&mut func, then1, B, vec![b(then2)]);
    push(
        &mut func,
        then2,
        Madd,
        vec![v64(15), ivc(14), v64(40), v64(0)],
    );
    push(&mut func, then2, LdrRI, vec![v(16), v64(15), i(0)]);
    push(&mut func, then2, AddRR, vec![v(17), v(6), v(16)]); // acc + a[i]
    push(&mut func, then2, MovR, vec![v(18), v(17)]); // result = acc + a[i]
    push(&mut func, then2, B, vec![b(latch)]);

    // Else side: result = acc (+0).
    push(&mut func, els, MovR, vec![v(18), v(6)]);
    push(&mut func, els, B, vec![b(latch)]);

    // Latch: iv+1; acc = result; iv = iv+1; back-edge to header.
    push(&mut func, latch, AddRI, vec![ivc(19), ivc(5), i(1)]);
    push(&mut func, latch, MovR, vec![v(6), v(18)]);
    push(&mut func, latch, MovR, vec![ivc(5), ivc(19)]);
    push(&mut func, latch, B, vec![b(header)]);

    // Exit.
    push(&mut func, exit, MovR, vec![v(30), v(6)]);
    push(&mut func, exit, Ret, vec![]);

    // DETACHED bounds-check carrier: a TrapBoundsCheckExact reading the iv-copy
    // v11 that bounds-check-elim unhooked but left in `func.insts`. With the flat
    // build_def_map it would shadow v11's real (block `pass`) def and break the
    // address / same_as_iv walks; build_live_def_map skips it (not in any block).
    let _detached = func.push_inst(MachInst::new(
        TrapBoundsCheckExact,
        vec![v64(11), v64(11), i(n)],
    ));

    func.add_edge(entry, header);
    func.add_edge(header, pass);
    func.add_edge(header, exit);
    func.add_edge(pass, cmp);
    func.add_edge(cmp, then1);
    func.add_edge(cmp, els);
    func.add_edge(then1, then2);
    func.add_edge(then2, latch);
    func.add_edge(els, latch);
    func.add_edge(latch, header);
    func.next_vreg = 128;
    func
}

#[test]
fn vectorizes_forward_chain_condsum() {
    // `while i<N { if a[i] > t { s += a[i] } }` over a local array — the
    // multi-block forward chain the strict two-block gate cannot match. Must
    // fire on the WIDE chain shape ([`UNROLL_CHAIN`] accumulators,
    // single-block bottom-tested loop) and lower the accumulate as NEGATED
    // MLA.4S-BY-MASK: the CMGT mask lane is exactly -1/0, so
    // `acc.4s[i] += a[i]*mask[i]` contributes `-a mod 2^32` on TRUE lanes and
    // 0 on FALSE lanes — no masking AND and no separate accumulate ADD (2
    // vector ops per Q-block) — and the drain folds the negated sum into the
    // scalar accumulator with a wrapping SubRR.
    let mut func = build_chain_condsum(64, true);
    let mut pass = NeonPredSumPass::new();
    assert!(pass.run(&mut func), "forward-chain condsum must vectorize");
    assert_eq!(pass.fired(), 1);
    // 8 accumulators × 1 array = 4 LDP Q-pair loads.
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        UNROLL_CHAIN / 2,
        "4 LDP q,q"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLd1Post),
        0,
        "LD1 replaced by LDP"
    );
    // Per accumulator: CMGT.4S mask + ONE MLA-by-mask accumulate.
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmgtV),
        UNROLL_CHAIN,
        "8 CMGT masks"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonMlaV),
        UNROLL_CHAIN,
        "8 MLA-by-mask"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonAndV),
        0,
        "no AND: the mask IS the multiplier"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonEorV),
        0,
        "no bitselect (else arm 0)"
    );
    // The only NeonAddVs are the balanced `.4S` accumulator combines.
    assert_eq!(
        count(&func, AArch64Opcode::NeonAddV),
        UNROLL_CHAIN - 1,
        "combines only"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonUmovGen),
        4,
        "reduce 4 lanes"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonMovi),
        UNROLL_CHAIN,
        "zeroed accs"
    );
    // NEGATED drain: one wrapping SubRR folds the negated sum into the acc.
    assert_eq!(
        count(&func, AArch64Opcode::SubRR),
        1,
        "negated drain SubRR fold"
    );
    // Every MLA carries the fixed `.4S` arrangement; its multiplier operand
    // (Vm, operand 2) is the mask — NOT the accumulator and NOT the
    // multiplicand (operand 1, the raw lane vector).
    for blk in &func.blocks {
        for &id in &blk.insts {
            let inst = func.inst(id);
            if inst.opcode == AArch64Opcode::NeonMlaV {
                assert!(
                    matches!(inst.operands.last(), Some(MachOperand::Imm(a)) if *a == ARR_S4),
                    "MLA arrangement must be .4S"
                );
                assert_ne!(
                    inst.operands[0], inst.operands[2],
                    "MLA multiplier Vm (op 2) must be the mask, not the accumulator"
                );
                assert_ne!(
                    inst.operands[1], inst.operands[2],
                    "MLA multiplier Vm (op 2) must be the mask, not the multiplicand"
                );
            }
        }
    }
    // The scalar loop is untouched (still present for the tail).
    assert!(
        count(&func, AArch64Opcode::LdrRI) >= 2,
        "scalar loads preserved"
    );
}

#[test]
fn chain_bails_on_gpr32_iv() {
    // Same forward-chain shape but a Gpr32 induction — the recognizer requires
    // the Gpr64 `usize` counter (mixed i64-index / i32-element shape), so this
    // fails closed to the scalar loop (no NEON emitted).
    let mut func = build_chain_condsum(64, false);
    let mut pass = NeonPredSumPass::new();
    assert!(!pass.run(&mut func), "Gpr32 induction must BAIL");
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        0,
        "no NEON emitted"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonCmgtV), 0, "no NEON emitted");
}

#[test]
fn chain_bails_on_small_bound() {
    // N < WIDTH (16): the recognizer still fires (bound is a valid const), but
    // the compile-time `main_bound` is 0 so the UNSIGNED `iv <u 0` guard never
    // admits a vector iteration — every element is handled by the scalar loop.
    // The transform stays sound (purely additive); this pins the N<WIDTH arm.
    let mut func = build_chain_condsum(8, true);
    let mut pass = NeonPredSumPass::new();
    assert!(pass.run(&mut func), "small-bound chain still recognized");
    assert_eq!(pass.fired(), 1);
    // main_bound materialized as 0 (single Movz 0); vector guard never passes.
    let movz0 = func
        .blocks
        .iter()
        .flat_map(|blk| blk.insts.iter())
        .map(|&id| func.inst(id))
        .filter(|inst| {
            inst.opcode == AArch64Opcode::Movz
                && matches!(inst.operands.get(1), Some(MachOperand::Imm(0)))
        })
        .count();
    assert!(movz0 >= 1, "main_bound 0 materialized for N<WIDTH");
}

/// Build the EXACT inner-loop shape the bridge emits for the ground-truth
/// statement-if condsum (`while i<N { if a[i]>t { s = s.wrapping_add(a[i]) } }`
/// over a local `[i32; N]`) — the two features the idealized
/// [`build_chain_condsum`] lacked, which kept this pass from ever firing on the
/// real benchmark:
///
/// 1. the loop bound is a REGISTER holding a `Movz` constant (`cmp iv, Nreg`),
///    not a folded `CmpRI` immediate;
/// 2. the `then` arm carries a REDUNDANT un-elided bounds guard
///    (`cmp iv, Nreg; b.lo then_body; b oob`) BETWEEN the condition split and
///    the `s += a[i]` tail, so the two diamond arms do not converge on one
///    2-successor split unless the walker treats that guard as a pass-through.
///
/// CFG: header(guard, reg bound) -> pass(guard) -> cmp(split `a[iv] > t`) ->
/// { then_guard(redundant) -> then_body(`s+=a[iv]` reload) | else(`+0`) } ->
/// latch. Register map mirrors the real dump: base v0, N v3 (Movz 4096),
/// t v33 (Gpr32 invariant), iv v38 (Gpr64), acc v39 (Gpr32), es v51 (Movz 4).
fn build_bridge_condsum_with_then_guard(n: i64) -> MachFunction {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    let header = func.create_block();
    let pass = func.create_block();
    let cmp = func.create_block();
    let then_guard = func.create_block();
    let then_body = func.create_block();
    let els = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();
    let oob = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;

    // Preheader: base v0, N v3 = Movz n (the REGISTER bound), t v33, es v51,
    // iv v38 = 0, acc v39 = 0.
    push(&mut func, entry, Copy, vec![v64(0), v64(0)]); // base
    push(&mut func, entry, Movz, vec![v64(3), i(n)]); // N (register!)
    push(&mut func, entry, Copy, vec![v(33), v(33)]); // t (loop-invariant Gpr32)
    push(&mut func, entry, Movz, vec![v64(51), i(4)]); // element size
    push(&mut func, entry, Movz, vec![v64(38), i(0)]); // iv = 0
    push(&mut func, entry, Movz, vec![v(39), i(0)]); // acc = 0
    push(&mut func, entry, B, vec![b(header)]);

    // Header guard: MovR ivcopy; CmpRR(ivcopy, Nreg); b.lo pass; b exit.
    push(&mut func, header, MovR, vec![v64(42), v64(38)]);
    push(&mut func, header, CmpRR, vec![v64(42), v64(3)]);
    push(&mut func, header, BCond, vec![i(CC_LO), b(pass)]);
    push(&mut func, header, B, vec![b(exit)]);

    // Surviving bounds guard (pass-through classified by walk_chain).
    push(&mut func, pass, MovR, vec![v64(45), v64(38)]);
    push(&mut func, pass, CmpRR, vec![v64(45), v64(3)]);
    push(&mut func, pass, BCond, vec![i(CC_LO), b(cmp)]);
    push(&mut func, pass, B, vec![b(oob)]);

    // Condition split: a = a[iv]; cmp a, t; b.gt then_guard; b els.
    push(
        &mut func,
        cmp,
        Madd,
        vec![v64(52), v64(45), v64(51), v64(0)],
    );
    push(&mut func, cmp, LdrRI, vec![v(54), v64(52), i(0)]);
    push(&mut func, cmp, CmpRR, vec![v(54), v(33)]);
    push(&mut func, cmp, BCond, vec![i(CC_GT), b(then_guard)]);
    push(&mut func, cmp, B, vec![b(els)]);

    // REDUNDANT then-arm bounds guard (same iv, same Nreg): the un-elided
    // reload check the bridge leaves between the split and the then tail.
    push(&mut func, then_guard, MovR, vec![v64(56), v64(38)]);
    push(&mut func, then_guard, CmpRR, vec![v64(56), v64(3)]);
    push(&mut func, then_guard, BCond, vec![i(CC_LO), b(then_body)]);
    push(&mut func, then_guard, B, vec![b(oob)]);

    // Then tail: reload a[iv]; result = acc + a[iv].
    push(
        &mut func,
        then_body,
        Madd,
        vec![v64(63), v64(56), v64(51), v64(0)],
    );
    push(&mut func, then_body, LdrRI, vec![v(65), v64(63), i(0)]);
    push(&mut func, then_body, AddRR, vec![v(66), v(39), v(65)]);
    push(&mut func, then_body, MovR, vec![v(68), v(66)]);
    push(&mut func, then_body, B, vec![b(latch)]);

    // Else tail: result = acc (+0).
    push(&mut func, els, MovR, vec![v(68), v(39)]);
    push(&mut func, els, B, vec![b(latch)]);

    // Latch: iv+1; acc = result; iv writeback; back-edge.
    push(&mut func, latch, AddRI, vec![v64(70), v64(38), i(1)]);
    push(&mut func, latch, MovR, vec![v(39), v(68)]);
    push(&mut func, latch, MovR, vec![v64(38), v64(70)]);
    push(&mut func, latch, B, vec![b(header)]);

    push(&mut func, exit, MovR, vec![v(30), v(39)]);
    push(&mut func, exit, Ret, vec![]);
    push(&mut func, oob, Ret, vec![]);

    func.add_edge(entry, header);
    func.add_edge(header, pass);
    func.add_edge(header, exit);
    func.add_edge(pass, cmp);
    func.add_edge(pass, oob);
    func.add_edge(cmp, then_guard);
    func.add_edge(cmp, els);
    func.add_edge(then_guard, then_body);
    func.add_edge(then_guard, oob);
    func.add_edge(then_body, latch);
    func.add_edge(els, latch);
    func.add_edge(latch, header);
    func.next_vreg = 128;
    func
}

#[test]
fn vectorizes_bridge_condsum_with_then_arm_guard_and_reg_bound() {
    // The GROUND-TRUTH bridge shape (csI): register `Movz` bound + redundant
    // then-arm bounds guard. Must fire on the WIDE chain shape and lower to
    // the NEGATED MLA-by-mask form (CMGT mask + ONE MLA per accumulator, the
    // 2-op/Q form below LLVM's cmgt+and+add issue floor; wrapping SubRR
    // drain).
    let mut func = build_bridge_condsum_with_then_guard(4096);
    let mut pass = NeonPredSumPass::new();
    assert!(
        pass.run(&mut func),
        "real bridge condsum shape must vectorize"
    );
    assert_eq!(pass.fired(), 1);
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        UNROLL_CHAIN / 2,
        "4 LDP q,q"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmgtV),
        UNROLL_CHAIN,
        "8 CMGT masks"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonMlaV),
        UNROLL_CHAIN,
        "8 MLA-by-mask"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonAndV),
        0,
        "no AND: the mask IS the multiplier"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonEorV),
        0,
        "no bitselect (else arm 0)"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonAddV),
        UNROLL_CHAIN - 1,
        "combines only"
    );
    assert_eq!(
        count(&func, AArch64Opcode::SubRR),
        1,
        "negated drain SubRR fold"
    );
    // The scalar loop (and both its bounds guards) survives untouched for the
    // tail — the transform is purely additive.
    assert!(
        count(&func, AArch64Opcode::LdrRI) >= 2,
        "scalar loads preserved"
    );
}

#[test]
fn chain_bails_on_then_arm_guard_with_disagreeing_bound() {
    // Same shape but the then-arm guard tests a DIFFERENT bound register
    // (`M != N`): the walker must NOT elide it (bound agreement is the
    // soundness condition), so the arms never converge and the loop stays
    // scalar. Fail-closed pin for the guard-elision rule.
    let mut func = build_bridge_condsum_with_then_guard(4096);
    // Rewrite the then-guard's compare to a fresh Movz 64 bound (M != N).
    let then_guard_cmp = func
        .blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .find(|&id| {
            let inst = func.inst(id);
            inst.opcode == AArch64Opcode::CmpRR
                && matches!(inst.operands.first(),
                    Some(MachOperand::VReg(d)) if d.id == 56)
        })
        .expect("then-guard cmp present");
    // New disagreeing bound register defined in the entry block.
    let m = func.push_inst(MachInst::new(AArch64Opcode::Movz, vec![v64(90), i(64)]));
    let entry = func.entry;
    let at = func.block(entry).insts.len() - 1; // before the terminator B
    func.blocks[entry.0 as usize].insts.insert(at, m);
    func.inst_mut(then_guard_cmp).operands[1] = v64(90);
    let mut pass = NeonPredSumPass::new();
    assert!(
        !pass.run(&mut func),
        "disagreeing then-arm guard bound must BAIL"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        0,
        "no NEON emitted"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonCmgtV), 0, "no NEON emitted");
}

// ---------------------------------------------------------------------------
// WIDENING i64-accumulator forward chain — `s: i64 += a_i32[iv] as i64`
// (mirrors e01_condsum: Gpr64 acc, `Sxtw` on the then-arm reload feeding the
// i64 AddRR; lowered as CMGT.4S + AND.16B + SMLAL/SMLAL2-by-ones into .2D).
// ---------------------------------------------------------------------------

/// How the then-arm produces the i64 addend for the `Gpr64` accumulator.
#[derive(Clone, Copy, PartialEq)]
enum WidenAddend {
    /// `Sxtw(a[iv])` — the `as i64` sign-extension (the ONLY accepted form).
    Sxtw,
    /// `Uxtw(a[iv])` — a ZERO-extension (`u32 as u64` sibling). `Uxtw` is not
    /// in [`allowed_loop_op`], so the loop BAILS at the opcode whitelist —
    /// the sign axes can never be crossed.
    Uxtw,
    /// A widening `MovR` copy (no explicit extension) — not `Sxtw`-rooted, so
    /// the diamond recognizer BAILS fail-closed.
    WideCopy,
}

/// Build the e01-shaped forward-chain condsum with an i64 (`Gpr64`) accumulator:
/// header (`iv <u N`, folded `CmpRI` bound) -> pass-through (elided bounds
/// check) -> compare diamond `a[iv] > t` -> { then pass-through -> then body
/// `s += sxtw(a[iv])` (reload) | else `+0` } -> latch. `iv` `Gpr64`, elements
/// i32 `.4S`, acc `Gpr64`. Register map mirrors the real e01 dump.
fn build_chain_condsum_i64_acc(n: i64, addend: WidenAddend) -> MachFunction {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    let header = func.create_block();
    let pass = func.create_block();
    let cmp = func.create_block();
    let then1 = func.create_block();
    let then2 = func.create_block();
    let els = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;

    // Preheader: base v0, t v33 (Gpr32 invariant), es v51 = 4, iv v38 = 0,
    // acc v39 (Gpr64) = 0.
    push(&mut func, entry, Copy, vec![v64(0), v64(0)]); // base
    push(&mut func, entry, Copy, vec![v(33), v(33)]); // t (loop-invariant Gpr32)
    push(&mut func, entry, Movz, vec![v64(51), i(4)]); // element size
    push(&mut func, entry, Movz, vec![v64(38), i(0)]); // iv = 0
    push(&mut func, entry, Movz, vec![v64(39), i(0)]); // acc (i64!) = 0
    push(&mut func, entry, B, vec![b(header)]);

    // Header guard: MovR ivcopy; CmpRI(ivcopy, N); b.lo pass; b exit.
    push(&mut func, header, MovR, vec![v64(42), v64(38)]);
    push(&mut func, header, CmpRI, vec![v64(42), i(n)]);
    push(&mut func, header, BCond, vec![i(CC_LO), b(pass)]);
    push(&mut func, header, B, vec![b(exit)]);

    // Pass-through (elided bounds check), carrying the addressing iv-copy.
    push(&mut func, pass, MovR, vec![v64(45), v64(38)]);
    push(&mut func, pass, B, vec![b(cmp)]);

    // Compare split: addr = base + iv*4; a = load; cmp a, t; b.gt then1; b els.
    push(
        &mut func,
        cmp,
        Madd,
        vec![v64(52), v64(45), v64(51), v64(0)],
    );
    push(&mut func, cmp, LdrRI, vec![v(54), v64(52), i(0)]);
    push(&mut func, cmp, CmpRR, vec![v(54), v(33)]);
    push(&mut func, cmp, BCond, vec![i(CC_GT), b(then1)]);
    push(&mut func, cmp, B, vec![b(els)]);

    // Then side: pass-through, then the widening `s += ext(a[iv])` body.
    push(&mut func, then1, MovR, vec![v64(56), v64(38)]);
    push(&mut func, then1, B, vec![b(then2)]);
    push(
        &mut func,
        then2,
        Madd,
        vec![v64(63), v64(56), v64(51), v64(0)],
    );
    push(&mut func, then2, LdrRI, vec![v(65), v64(63), i(0)]);
    match addend {
        WidenAddend::Sxtw => push(&mut func, then2, Sxtw, vec![v64(66), v(65)]),
        WidenAddend::Uxtw => push(&mut func, then2, Uxtw, vec![v64(66), v(65)]),
        WidenAddend::WideCopy => push(&mut func, then2, MovR, vec![v64(66), v(65)]),
    }
    push(&mut func, then2, AddRR, vec![v64(67), v64(39), v64(66)]);
    push(&mut func, then2, MovR, vec![v64(68), v64(67)]);
    push(&mut func, then2, B, vec![b(latch)]);

    // Else side: result = acc (+0).
    push(&mut func, els, MovR, vec![v64(68), v64(39)]);
    push(&mut func, els, B, vec![b(latch)]);

    // Latch: iv+1; acc = result; iv writeback; back-edge.
    push(&mut func, latch, AddRI, vec![v64(70), v64(38), i(1)]);
    push(&mut func, latch, MovR, vec![v64(39), v64(68)]);
    push(&mut func, latch, MovR, vec![v64(38), v64(70)]);
    push(&mut func, latch, B, vec![b(header)]);

    push(&mut func, exit, MovR, vec![v64(30), v64(39)]);
    push(&mut func, exit, Ret, vec![]);

    func.add_edge(entry, header);
    func.add_edge(header, pass);
    func.add_edge(header, exit);
    func.add_edge(pass, cmp);
    func.add_edge(cmp, then1);
    func.add_edge(cmp, els);
    func.add_edge(then1, then2);
    func.add_edge(then2, latch);
    func.add_edge(els, latch);
    func.add_edge(latch, header);
    func.next_vreg = 128;
    func
}

#[test]
fn vectorizes_widening_i64_acc_condsum() {
    // `while i<N { if a[i] > t { s(i64) += a[i] as i64 } }` — the e01 shape.
    // Must fire on the WIDE chain shape ([`UNROLL_CHAIN`] accumulators,
    // single-block bottom-tested loop) and lower the widening accumulate as
    // NEGATED SMLAL/SMLAL2-BY-MASK into `.2D` accumulators: the CMGT mask
    // lane is exactly -1/0, so `acc.d[j] += sext64(a)*sext64(mask)`
    // contributes `-sext64(a)` on TRUE lanes and 0 on FALSE lanes — no
    // masking AND at all (3 vector ops per Q-block) — and the drain folds
    // the negated sum into the scalar accumulator with a wrapping SubRR.
    let mut func = build_chain_condsum_i64_acc(2048, WidenAddend::Sxtw);
    let mut pass = NeonPredSumPass::new();
    assert!(
        pass.run(&mut func),
        "widening i64-acc condsum must vectorize"
    );
    assert_eq!(pass.fired(), 1);
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        UNROLL_CHAIN / 2,
        "4 LDP q,q"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmgtV),
        UNROLL_CHAIN,
        "8 CMGT masks"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonAndV),
        0,
        "no AND: the mask IS the multiplier"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonEorV),
        0,
        "no bitselect (else arm 0)"
    );
    // The widening accumulate: one SMLAL (.4S lanes {0,1}) + one SMLAL2
    // (lanes {2,3}) per accumulator with the RAW lane vector as multiplicand
    // and the COMPARE MASK as multiplier; ZERO SADDW (the masked wide-add
    // shape is fully replaced on this arm) and ZERO ones-splat (no dup(1)).
    assert_eq!(
        count(&func, AArch64Opcode::NeonSmlalV),
        UNROLL_CHAIN,
        "8 SMLAL-by-mask"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonSmlal2V),
        UNROLL_CHAIN,
        "8 SMLAL2-by-mask"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonSaddwV),
        0,
        "SADDW replaced by SMLAL-by-mask"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonSaddw2V),
        0,
        "SADDW2 replaced by SMLAL2-by-mask"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonDupGen),
        1,
        "only the t broadcast (no ones splat)"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonAddV),
        UNROLL_CHAIN - 1,
        ".2D combines only"
    );
    // `.2D` drain: 2 UMOV D-lane extracts (not 4 `.4S` ones), and the NEGATED
    // sum folds into the scalar accumulator via a wrapping SubRR.
    assert_eq!(
        count(&func, AArch64Opcode::NeonUmovGen),
        2,
        "2 D-lane extracts"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonMovi),
        UNROLL_CHAIN,
        "zeroed accs"
    );
    assert_eq!(
        count(&func, AArch64Opcode::SubRR),
        1,
        "negated drain SubRR fold"
    );
    // Every SMLAL/SMLAL2 carries the fixed `.4S` INPUT arrangement, and its
    // multiplier operand (Vm, operand 2) is the mask — NOT the accumulator
    // and NOT the multiplicand (operand 1, the raw lane vector).
    for blk in &func.blocks {
        for &id in &blk.insts {
            let inst = func.inst(id);
            if matches!(
                inst.opcode,
                AArch64Opcode::NeonSmlalV | AArch64Opcode::NeonSmlal2V
            ) {
                assert!(
                    matches!(inst.operands.last(), Some(MachOperand::Imm(a)) if *a == ARR_S4),
                    "SMLAL input arrangement must be .4S"
                );
                assert_ne!(
                    inst.operands[0], inst.operands[2],
                    "SMLAL multiplier Vm (op 2) must be the mask, not the accumulator"
                );
                assert_ne!(
                    inst.operands[1], inst.operands[2],
                    "SMLAL multiplier Vm (op 2) must be the mask, not the multiplicand"
                );
            }
        }
    }
    // The scalar loop is untouched (still present for the tail).
    assert!(
        count(&func, AArch64Opcode::LdrRI) >= 2,
        "scalar loads preserved"
    );
    assert_eq!(
        count(&func, AArch64Opcode::Sxtw),
        1,
        "scalar Sxtw untouched"
    );
}

#[test]
fn widening_bails_on_zext_uxtw() {
    // The u32->u64 ZERO-extension sibling (`s += a[i] as u64` over `[u32]`):
    // `Uxtw` is not a whitelisted loop opcode, so the loop BAILS fail-closed —
    // the SIGNED SMLAL path can never be applied across the sign axis.
    let mut func = build_chain_condsum_i64_acc(2048, WidenAddend::Uxtw);
    let mut pass = NeonPredSumPass::new();
    assert!(!pass.run(&mut func), "zext (Uxtw) widening must BAIL");
    assert_eq!(
        count(&func, AArch64Opcode::NeonSaddwV),
        0,
        "no NEON emitted"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonSmlalV),
        0,
        "no NEON emitted"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        0,
        "no NEON emitted"
    );
}

#[test]
fn widening_bails_on_non_sxtw_addend() {
    // A `Gpr64` accumulator whose addend is NOT `Sxtw`-rooted (a widening MovR
    // copy with no explicit extension): the diamond recognizer must BAIL —
    // only the proven sign-extension form is vectorized.
    let mut func = build_chain_condsum_i64_acc(2048, WidenAddend::WideCopy);
    let mut pass = NeonPredSumPass::new();
    assert!(!pass.run(&mut func), "non-Sxtw i64 addend must BAIL");
    assert_eq!(
        count(&func, AArch64Opcode::NeonSaddwV),
        0,
        "no NEON emitted"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonSmlalV),
        0,
        "no NEON emitted"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        0,
        "no NEON emitted"
    );
}
