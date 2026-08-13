// Unit tests for the neon-minmax vectorizer.
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
fn gpr32(id: u32) -> VReg {
    VReg::new(id, RegClass::Gpr32)
}
fn count(func: &MachFunction, op: AArch64Opcode) -> usize {
    func.blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .filter(|&id| func.inst(id).opcode == op)
        .count()
}

/// How the reduction is expressed in the header.
enum Red {
    /// min/max via the materialised select chain (CSet cc_real, Csel NE).
    MinMaxIndirect(i64),
    /// min/max via a direct `CmpRR; Csel(cc)`.
    MinMaxDirect(i64),
    /// bitwise `acc OP load`.
    Bitwise(AArch64Opcode),
    /// add reduction (must BAIL — belongs to neon_array).
    Add,
    /// AFFINE IOTA term: `acc ^= (iv + 1) ^ a[i]` (the `puzzle` shape). Fires.
    XorIvAffine,
    /// AFFINE IOTA term: `acc ^= (iv*3) ^ a[i]` (iv * constant). Fires.
    XorIvMulConst,
    /// NON-AFFINE iv term: `acc ^= (iv*iv) ^ a[i]` (quadratic). Must BAIL.
    XorIvSquare,
}

/// Build the rotated `for i in 0..n: acc = REDUCE(acc, a[i])` loop in the exact
/// shape `loop-latch-layout` emits (guard / header / latch).
///
/// Registers: v64(0)=base, v(1)=n, v(3)=0, v(4)=1, v64(40)=4(es). iv=v(5),
/// acc=v(6). Header temps start at v(10).
fn build_loop(red: Red) -> MachFunction {
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

    // Preheader.
    push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base
    push(&mut func, bb0, Copy, vec![v(1), v(1)]); // n
    push(&mut func, bb0, Movz, vec![v(3), i(0)]);
    push(&mut func, bb0, Movz, vec![v(4), i(1)]);
    push(&mut func, bb0, Movz, vec![v64(40), i(4)]); // element size
    push(&mut func, bb0, MovR, vec![v(5), v(3)]); // iv = 0
    push(&mut func, bb0, MovR, vec![v(6), v(3)]); // acc = 0 (init irrelevant)
    push(&mut func, bb0, B, vec![b(guard)]);
    // Guard.
    push(&mut func, guard, CmpRR, vec![v(5), v(1)]);
    push(&mut func, guard, BCond, vec![i(CC_LT), b(header)]);
    push(&mut func, guard, B, vec![b(exit)]);
    // Header: address + load + reduction + step.
    push(&mut func, header, Sxtw, vec![v64(10), v(5)]);
    push(
        &mut func,
        header,
        Madd,
        vec![v64(11), v64(10), v64(40), v64(0)],
    );
    push(&mut func, header, LdrRI, vec![v(12), v64(11), i(0)]); // load a[i]
    // reduction: define the writeback source `acc_src` = v(20).
    match red {
        Red::MinMaxIndirect(cc_real) => {
            push(&mut func, header, CmpRR, vec![v(12), v(6)]); // cmp load, acc
            push(&mut func, header, CSet, vec![v64(13), i(cc_real)]);
            push(&mut func, header, CmpRI, vec![v64(13), i(0)]);
            push(&mut func, header, Csel, vec![v(20), v(12), v(6), i(CC_NE)]);
        }
        Red::MinMaxDirect(cc) => {
            push(&mut func, header, CmpRR, vec![v(12), v(6)]);
            push(&mut func, header, Csel, vec![v(20), v(12), v(6), i(cc)]);
        }
        Red::Bitwise(op) => {
            push(&mut func, header, op, vec![v(20), v(6), v(12)]); // acc OP load
        }
        Red::Add => {
            push(&mut func, header, AddRR, vec![v(20), v(6), v(12)]);
        }
        Red::XorIvAffine => {
            // term = (iv + 1) ^ a[i];  acc ^= term.
            push(&mut func, header, AddRI, vec![v(14), v(5), i(1)]); // iv+1
            push(&mut func, header, EorRR, vec![v(15), v(14), v(12)]); // (iv+1)^a[i]
            push(&mut func, header, EorRR, vec![v(20), v(6), v(15)]); // acc ^ term
        }
        Red::XorIvMulConst => {
            // term = (iv * 3) ^ a[i];  acc ^= term.
            push(&mut func, header, Movz, vec![v(13), i(3)]);
            push(&mut func, header, MulRR, vec![v(14), v(5), v(13)]); // iv*3
            push(&mut func, header, EorRR, vec![v(15), v(14), v(12)]); // (iv*3)^a[i]
            push(&mut func, header, EorRR, vec![v(20), v(6), v(15)]); // acc ^ term
        }
        Red::XorIvSquare => {
            // term = (iv * iv) ^ a[i];  acc ^= term.  NON-AFFINE ⇒ must BAIL.
            push(&mut func, header, MulRR, vec![v(14), v(5), v(5)]); // iv*iv
            push(&mut func, header, EorRR, vec![v(15), v(14), v(12)]); // (iv*iv)^a[i]
            push(&mut func, header, EorRR, vec![v(20), v(6), v(15)]); // acc ^ term
        }
    }
    push(&mut func, header, AddRR, vec![v(21), v(5), v(4)]); // iv+1
    push(&mut func, header, B, vec![b(latch)]);
    // Latch: writebacks + compare + branch.
    push(&mut func, latch, AddRI, vec![v(5), v(21), i(0)]);
    push(&mut func, latch, AddRI, vec![v(6), v(20), i(0)]);
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

fn fires(red: Red) -> (bool, MachFunction) {
    let mut func = build_loop(red);
    let mut pass = NeonMinMaxPass::new();
    let changed = pass.run(&mut func);
    (changed, func)
}

#[test]
fn vectorizes_array_smax_indirect() {
    let (changed, func) = fires(Red::MinMaxIndirect(CC_GT));
    assert!(changed, "smax array reduction should vectorize");
    assert!(
        count(&func, AArch64Opcode::NeonSmaxV) >= UNROLL,
        "SMAX.4S per accumulator"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonUmovGen),
        4,
        "reduce 4 lanes"
    );
    // IntMin identity: Movz(1) + DUP + SHL per accumulator.
    assert!(
        count(&func, AArch64Opcode::NeonShlVImm) >= UNROLL,
        "INT_MIN via SHL"
    );
    // horizontal fold uses CMP+CSEL: 4 fold steps (+ the untouched scalar
    // loop's own reduction CSEL, which the additive transform leaves intact).
    assert_eq!(
        count(&func, AArch64Opcode::Csel),
        5,
        "4 CSEL fold steps + 1 scalar"
    );
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
}

#[test]
fn vectorizes_array_smin_indirect() {
    let (changed, func) = fires(Red::MinMaxIndirect(CC_LT));
    assert!(changed, "smin array reduction should vectorize");
    assert!(count(&func, AArch64Opcode::NeonSminV) >= UNROLL, "SMIN.4S");
    // IntMax identity: MOVI(0xFF) + USHR.
    assert!(
        count(&func, AArch64Opcode::NeonUshrVImm) >= UNROLL,
        "INT_MAX via USHR"
    );
}

#[test]
fn vectorizes_array_umax_indirect() {
    let (changed, func) = fires(Red::MinMaxIndirect(CC_HI));
    assert!(changed, "umax array reduction should vectorize");
    assert!(count(&func, AArch64Opcode::NeonUmaxV) >= UNROLL, "UMAX.4S");
    // Zero identity: MOVI 0.
    assert!(
        count(&func, AArch64Opcode::NeonMovi) >= UNROLL,
        "zero identity via MOVI"
    );
}

#[test]
fn vectorizes_array_umin_indirect() {
    let (changed, func) = fires(Red::MinMaxIndirect(CC_LO));
    assert!(changed, "umin array reduction should vectorize");
    assert!(count(&func, AArch64Opcode::NeonUminV) >= UNROLL, "UMIN.4S");
}

#[test]
fn vectorizes_array_minmax_direct() {
    // Direct `CmpRR; Csel(GT)` = smax (cmp load, acc).
    let (changed, func) = fires(Red::MinMaxDirect(CC_GT));
    assert!(changed, "direct-select smax should vectorize");
    assert!(count(&func, AArch64Opcode::NeonSmaxV) >= UNROLL, "SMAX.4S");
}

#[test]
fn vectorizes_array_and() {
    let (changed, func) = fires(Red::Bitwise(AArch64Opcode::AndRR));
    assert!(changed, "and reduction should vectorize");
    assert!(
        count(&func, AArch64Opcode::NeonAndV) >= UNROLL,
        "AND.16B accumulate"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonSmaxV), 0, "no min/max op");
    assert_eq!(
        count(&func, AArch64Opcode::Csel),
        0,
        "bitwise fold uses scalar op"
    );
    // AllOnes identity: MOVI 0xFF per accumulator.
    assert!(
        count(&func, AArch64Opcode::NeonMovi) >= UNROLL,
        "all-ones via MOVI 0xFF"
    );
}

#[test]
fn vectorizes_array_or() {
    let (changed, func) = fires(Red::Bitwise(AArch64Opcode::OrrRR));
    assert!(changed, "or reduction should vectorize");
    assert!(
        count(&func, AArch64Opcode::NeonOrrV) >= UNROLL,
        "ORR accumulate"
    );
}

#[test]
fn vectorizes_array_xor() {
    let (changed, func) = fires(Red::Bitwise(AArch64Opcode::EorRR));
    assert!(changed, "xor reduction should vectorize");
    assert!(
        count(&func, AArch64Opcode::NeonEorV) >= UNROLL,
        "EOR accumulate"
    );
}

#[test]
fn bails_on_add_reduction() {
    // ADD is neon_array's job — neon_minmax must NOT touch it.
    let (changed, func) = fires(Red::Add);
    assert!(!changed, "add reduction must BAIL (left to neon_array)");
    assert_eq!(count(&func, AArch64Opcode::NeonSmaxV), 0);
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

// ------------------------------------------------------------------
// GAP 1 — affine iota terms: `r ^= (iv+K) ^ a[i]` (the puzzle shape).
// ------------------------------------------------------------------

#[test]
fn vectorizes_xor_iv_affine() {
    // `r ^= (iv + 1) ^ a[i]` — the Shootout `puzzle` findDuplicate kernel.
    let (changed, func) = fires(Red::XorIvAffine);
    assert!(
        changed,
        "XOR reduction with an affine iv term should vectorize"
    );
    // The iota machinery fired: iv is DUP-splatted, iota built via MOVI+INS.
    assert!(
        count(&func, AArch64Opcode::NeonDupGen) >= 1,
        "iv splat (DUP)"
    );
    assert!(
        count(&func, AArch64Opcode::NeonInsGen) >= 1,
        "iota lanes via INS"
    );
    assert!(
        count(&func, AArch64Opcode::NeonMovi) >= 1,
        "iota lane-0 via MOVI"
    );
    // The term XOR + the reduction accumulate are both vector EORs.
    assert!(
        count(&func, AArch64Opcode::NeonEorV) >= 2 * UNROLL,
        "term ^ + accumulate ^"
    );
    // The `iv+1` per lane is a vector ADD (per accumulator) plus the iota
    // advance (per accumulator) and the iota construction adds.
    assert!(
        count(&func, AArch64Opcode::NeonAddV) >= 2 * UNROLL,
        "iv+1 + iota advance"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        UNROLL / 2,
        "2 LDP q,q"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonUmovGen),
        4,
        "reduce 4 lanes"
    );
}

#[test]
fn vectorizes_xor_iv_mul_const() {
    // `r ^= (iv * 3) ^ a[i]` — affine (iv times a constant) ⇒ fires.
    let (changed, func) = fires(Red::XorIvMulConst);
    assert!(
        changed,
        "XOR reduction with `iv*const` term should vectorize"
    );
    assert!(
        count(&func, AArch64Opcode::NeonMulV) >= UNROLL,
        "iv*3 per accumulator"
    );
    assert!(
        count(&func, AArch64Opcode::NeonDupGen) >= 1,
        "iv splat (DUP)"
    );
    assert!(
        count(&func, AArch64Opcode::NeonEorV) >= 2 * UNROLL,
        "term ^ + accumulate ^"
    );
}

#[test]
fn bails_on_xor_iv_square_nonaffine() {
    // `r ^= (iv * iv) ^ a[i]` — a quadratic (NON-AFFINE) iv term. Deliberately
    // scoped out: must BAIL and emit no NEON (fail-closed).
    let (changed, func) = fires(Red::XorIvSquare);
    assert!(!changed, "non-affine iv*iv term must BAIL");
    assert_eq!(
        count(&func, AArch64Opcode::NeonDupGen),
        0,
        "no iota emitted"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonEorV),
        0,
        "no vector EOR emitted"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        0,
        "no NEON emitted"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLd1Post),
        0,
        "no NEON emitted"
    );
}

#[test]
fn bails_on_eq_select() {
    // A `Csel` gated on equality (CSet EQ) is not an ordering ⇒ BAIL.
    let (changed, func) = fires(Red::MinMaxIndirect(CC_EQ));
    assert!(!changed, "equality select must BAIL");
    assert_eq!(count(&func, AArch64Opcode::NeonLd1Post), 0);
    assert_eq!(count(&func, AArch64Opcode::NeonLdpQPost), 0);
}

// ------------------------------------------------------------------
// decode_relation: the soundness core, exhaustively probed.
// ------------------------------------------------------------------

#[test]
fn decode_relation_canonical_forms() {
    let cand = gpr32(100);
    let acc = gpr32(200);
    // cmp(cand, acc) ? cand : acc  — canonical isel shape.
    assert_eq!(
        decode_relation(cand, acc, CC_GT, cand, acc, acc),
        Some((ReduceOp::Smax, cand))
    );
    assert_eq!(
        decode_relation(cand, acc, CC_GE, cand, acc, acc),
        Some((ReduceOp::Smax, cand))
    );
    assert_eq!(
        decode_relation(cand, acc, CC_LT, cand, acc, acc),
        Some((ReduceOp::Smin, cand))
    );
    assert_eq!(
        decode_relation(cand, acc, CC_LE, cand, acc, acc),
        Some((ReduceOp::Smin, cand))
    );
    assert_eq!(
        decode_relation(cand, acc, CC_HI, cand, acc, acc),
        Some((ReduceOp::Umax, cand))
    );
    assert_eq!(
        decode_relation(cand, acc, CC_HS, cand, acc, acc),
        Some((ReduceOp::Umax, cand))
    );
    assert_eq!(
        decode_relation(cand, acc, CC_LO, cand, acc, acc),
        Some((ReduceOp::Umin, cand))
    );
    assert_eq!(
        decode_relation(cand, acc, CC_LS, cand, acc, acc),
        Some((ReduceOp::Umin, cand))
    );
}

#[test]
fn decode_relation_swapped_compare_operands() {
    let cand = gpr32(100);
    let acc = gpr32(200);
    // cmp(acc, cand) ? cand : acc.  acc < cand ? cand : acc = smax.
    assert_eq!(
        decode_relation(acc, cand, CC_LT, cand, acc, acc),
        Some((ReduceOp::Smax, cand))
    );
    // acc > cand ? cand : acc = smin.
    assert_eq!(
        decode_relation(acc, cand, CC_GT, cand, acc, acc),
        Some((ReduceOp::Smin, cand))
    );
    // acc >u cand ? cand : acc = umin.
    assert_eq!(
        decode_relation(acc, cand, CC_HI, cand, acc, acc),
        Some((ReduceOp::Umin, cand))
    );
}

#[test]
fn decode_relation_swapped_select_operands() {
    let cand = gpr32(100);
    let acc = gpr32(200);
    // cmp(cand, acc) ? acc : cand.  picks acc when cand>acc ⇒ smin.
    assert_eq!(
        decode_relation(cand, acc, CC_GT, acc, cand, acc),
        Some((ReduceOp::Smin, cand))
    );
    // picks acc when cand<acc ⇒ smax.
    assert_eq!(
        decode_relation(cand, acc, CC_LT, acc, cand, acc),
        Some((ReduceOp::Smax, cand))
    );
    // unsigned: picks acc when cand>u acc ⇒ umin.
    assert_eq!(
        decode_relation(cand, acc, CC_HI, acc, cand, acc),
        Some((ReduceOp::Umin, cand))
    );
}

#[test]
fn decode_relation_rejects_ambiguous() {
    let cand = gpr32(100);
    let acc = gpr32(200);
    let other = gpr32(300);
    // EQ / NE are not orderings.
    assert_eq!(decode_relation(cand, acc, CC_EQ, cand, acc, acc), None);
    assert_eq!(decode_relation(cand, acc, CC_NE, cand, acc, acc), None);
    // Compare operands not exactly {cand, acc}.
    assert_eq!(decode_relation(cand, other, CC_GT, cand, acc, acc), None);
    // Select operands not exactly {cand, acc}.
    assert_eq!(decode_relation(cand, acc, CC_GT, cand, other, acc), None);
    // Neither select operand is acc.
    assert_eq!(decode_relation(cand, other, CC_GT, cand, other, acc), None);
}

/// Model-check `decode_relation` against a concrete semantics on boundary
/// values: for the recognized `(cc, operand orders)` the decoded op's
/// scalar min/max must equal the select `(x cc y) ? t : f` for every probe
/// pair — including INT_MIN/INT_MAX/0/-1 where signed and unsigned diverge.
#[test]
fn decode_relation_matches_concrete_semantics() {
    let cand = gpr32(1);
    let acc = gpr32(2);
    let probes: [i32; 7] = [i32::MIN, i32::MAX, 0, -1, 1, 100, -100];

    // Evaluate a condition code on (l, r) as the hardware would (l - r flags).
    fn cc_holds(cc: i64, l: i32, r: i32) -> bool {
        match cc {
            CC_GT => l > r,
            CC_GE => l >= r,
            CC_LT => l < r,
            CC_LE => l <= r,
            CC_HI => (l as u32) > (r as u32),
            CC_HS => (l as u32) >= (r as u32),
            CC_LO => (l as u32) < (r as u32),
            CC_LS => (l as u32) <= (r as u32),
            _ => unreachable!(),
        }
    }
    fn apply_op(op: ReduceOp, a: i32, b: i32) -> i32 {
        match op {
            ReduceOp::Smax => a.max(b),
            ReduceOp::Smin => a.min(b),
            ReduceOp::Umax => (a as u32).max(b as u32) as i32,
            ReduceOp::Umin => (a as u32).min(b as u32) as i32,
            _ => unreachable!(),
        }
    }

    let ccs = [CC_GT, CC_GE, CC_LT, CC_LE, CC_HI, CC_HS, CC_LO, CC_LS];
    // All 4 combinations of (compare order) x (select order).
    let orders: [(bool, bool); 4] = [(true, true), (true, false), (false, true), (false, false)];
    for cc in ccs {
        for (cmp_cand_first, sel_cand_true) in orders {
            let (x, y) = if cmp_cand_first {
                (cand, acc)
            } else {
                (acc, cand)
            };
            let (t, f) = if sel_cand_true {
                (cand, acc)
            } else {
                (acc, cand)
            };
            let decoded = decode_relation(x, y, cc, t, f, acc);
            let Some((op, got_cand)) = decoded else {
                panic!("decode_relation returned None for a recognized form cc={cc}");
            };
            assert_eq!(got_cand, cand, "cand must be identified");
            // Concrete check across boundary probes.
            for &cv in &probes {
                for &av in &probes {
                    // The select computes `(x cc y) ? t : f` with x/y/t/f bound
                    // to cand=cv, acc=av.
                    let lv = if cmp_cand_first { cv } else { av };
                    let rv = if cmp_cand_first { av } else { cv };
                    let tv = if sel_cand_true { cv } else { av };
                    let fv = if sel_cand_true { av } else { cv };
                    let select_result = if cc_holds(cc, lv, rv) { tv } else { fv };
                    let op_result = apply_op(op, cv, av);
                    assert_eq!(
                        select_result, op_result,
                        "cc={cc} cmp_cand_first={cmp_cand_first} sel_cand_true={sel_cand_true} \
                         cand={cv} acc={av}: select={select_result} {op:?}={op_result}"
                    );
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// i64 (`.2D`) width parameterization
// ---------------------------------------------------------------------------

/// Build the i64 sibling of [`build_loop`]: `for i in 0..n (i64): acc =
/// REDUCE(acc, a[i])` with `Gpr64` iv/acc/bound and the i64 address shape
/// `Madd(iv, 8, base)` (no sign extension — the induction is already 64-bit).
fn build_loop_i64(red: Red) -> MachFunction {
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

    // Preheader.
    push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base
    push(&mut func, bb0, Copy, vec![v64(1), v64(1)]); // n (i64)
    push(&mut func, bb0, Movz, vec![v64(3), i(0)]);
    push(&mut func, bb0, Movz, vec![v64(4), i(1)]);
    push(&mut func, bb0, Movz, vec![v64(40), i(8)]); // element size 8
    push(&mut func, bb0, MovR, vec![v64(5), v64(3)]); // iv = 0
    push(&mut func, bb0, MovR, vec![v64(6), v64(3)]); // acc = 0
    push(&mut func, bb0, B, vec![b(guard)]);
    // Guard.
    push(&mut func, guard, CmpRR, vec![v64(5), v64(1)]);
    push(&mut func, guard, BCond, vec![i(CC_LT), b(header)]);
    push(&mut func, guard, B, vec![b(exit)]);
    // Header: i64 address + load + reduction + step.
    push(
        &mut func,
        header,
        Madd,
        vec![v64(11), v64(5), v64(40), v64(0)],
    ); // base + iv*8
    push(&mut func, header, LdrRI, vec![v64(12), v64(11), i(0)]); // load a[i]
    match red {
        Red::MinMaxIndirect(cc_real) => {
            push(&mut func, header, CmpRR, vec![v64(12), v64(6)]);
            push(&mut func, header, CSet, vec![v64(13), i(cc_real)]);
            push(&mut func, header, CmpRI, vec![v64(13), i(0)]);
            push(
                &mut func,
                header,
                Csel,
                vec![v64(20), v64(12), v64(6), i(CC_NE)],
            );
        }
        Red::MinMaxDirect(cc) => {
            push(&mut func, header, CmpRR, vec![v64(12), v64(6)]);
            push(
                &mut func,
                header,
                Csel,
                vec![v64(20), v64(12), v64(6), i(cc)],
            );
        }
        Red::Bitwise(op) => {
            push(&mut func, header, op, vec![v64(20), v64(6), v64(12)]);
        }
        Red::Add => {
            push(&mut func, header, AddRR, vec![v64(20), v64(6), v64(12)]);
        }
        Red::XorIvAffine => {
            push(&mut func, header, AddRI, vec![v64(14), v64(5), i(1)]); // iv+1
            push(&mut func, header, EorRR, vec![v64(15), v64(14), v64(12)]);
            push(&mut func, header, EorRR, vec![v64(20), v64(6), v64(15)]);
        }
        Red::XorIvMulConst => {
            // (iv*3) — on i64 this BAILS (no MUL.2D); builder kept for symmetry.
            push(&mut func, header, Movz, vec![v64(13), i(3)]);
            push(&mut func, header, MulRR, vec![v64(14), v64(5), v64(13)]);
            push(&mut func, header, EorRR, vec![v64(15), v64(14), v64(12)]);
            push(&mut func, header, EorRR, vec![v64(20), v64(6), v64(15)]);
        }
        Red::XorIvSquare => {
            push(&mut func, header, MulRR, vec![v64(14), v64(5), v64(5)]);
            push(&mut func, header, EorRR, vec![v64(15), v64(14), v64(12)]);
            push(&mut func, header, EorRR, vec![v64(20), v64(6), v64(15)]);
        }
    }
    push(&mut func, header, AddRR, vec![v64(21), v64(5), v64(4)]); // iv+1
    push(&mut func, header, B, vec![b(latch)]);
    // Latch.
    push(&mut func, latch, AddRI, vec![v64(5), v64(21), i(0)]);
    push(&mut func, latch, AddRI, vec![v64(6), v64(20), i(0)]);
    push(&mut func, latch, CmpRR, vec![v64(5), v64(1)]);
    push(&mut func, latch, BCond, vec![i(CC_LT), b(header)]);
    // Exit.
    push(&mut func, exit, MovR, vec![v64(30), v64(6)]);
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

/// Every arrangement-carrying compare/add/sub in `func` must be `.2D` (code 6).
fn assert_all_2d(func: &MachFunction) {
    for blk in &func.blocks {
        for &id in &blk.insts {
            let inst = func.inst(id);
            if matches!(
                inst.opcode,
                AArch64Opcode::NeonCmgtV
                    | AArch64Opcode::NeonCmhiV
                    | AArch64Opcode::NeonAddV
                    | AArch64Opcode::NeonSubV
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

/// i64 SMAX reduction vectorizes via the `.2D` compare + bitselect (NO
/// `SMAX.2D` exists — the encoder rejects it; the reduce is CMGT.2D +
/// EOR/AND/EOR per accumulate).
#[test]
fn vectorizes_i64_smax_via_cmgt_bitselect() {
    let mut func = build_loop_i64(Red::MinMaxIndirect(CC_GT));
    let mut pass = NeonMinMaxPass::new();
    assert!(pass.run(&mut func), "i64 smax must vectorize on .2D");
    assert_eq!(pass.fired(), 1);
    assert_eq!(count(&func, AArch64Opcode::NeonLdpQPost), 2, "2 LDP q,q");
    // 4 accumulates + 3 in-place combines = 7 reduces, each 1 CMGT.2D + 1
    // tied-destination BIT (clang's exact cmgt+bit shape; the EOR/AND chain is
    // the retained fail-closed path behind MINMAX_BIT_ENABLED).
    assert_eq!(count(&func, AArch64Opcode::NeonCmgtV), 7, "7 CMGT.2D masks");
    assert_eq!(count(&func, AArch64Opcode::NeonBitV), 7, "1 BIT per reduce");
    assert_eq!(
        count(&func, AArch64Opcode::NeonEorV),
        0,
        "BIT replaces the EOR chain"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonAndV),
        0,
        "BIT replaces the AND"
    );
    // The single-op forms must NOT be emitted (no `.2D` allocation in the ISA).
    assert_eq!(
        count(&func, AArch64Opcode::NeonSmaxV),
        0,
        "SMAX.2D does not exist"
    );
    assert_all_2d(&func);
}

/// i64 UMIN (direct Csel shape) vectorizes via CMHI.2D + bitselect.
#[test]
fn vectorizes_i64_umin_direct() {
    let mut func = build_loop_i64(Red::MinMaxDirect(CC_LO));
    let mut pass = NeonMinMaxPass::new();
    assert!(pass.run(&mut func), "i64 umin must vectorize on .2D");
    assert_eq!(count(&func, AArch64Opcode::NeonCmhiV), 7, "7 CMHI.2D masks");
    assert_eq!(count(&func, AArch64Opcode::NeonBitV), 7, "1 BIT per reduce");
    assert_eq!(
        count(&func, AArch64Opcode::NeonUminV),
        0,
        "UMIN.2D does not exist"
    );
    assert_all_2d(&func);
}

/// i64 bitwise XOR reduction vectorizes (whole-register ops are lane-width
/// agnostic; only the identity/fold widths change).
#[test]
fn vectorizes_i64_bitwise_xor() {
    let mut func = build_loop_i64(Red::Bitwise(AArch64Opcode::EorRR));
    let mut pass = NeonMinMaxPass::new();
    assert!(pass.run(&mut func), "i64 xor must vectorize");
    assert!(count(&func, AArch64Opcode::NeonEorV) >= 7, "vector EORs");
}

/// i64 `.2D` affine iota term: `r ^= (iv + 1) ^ a[i]` vectorizes with the
/// D-element iota (`[0,1]`) — width-parametric with the `.4S` path.
#[test]
fn vectorizes_i64_xor_iv_affine() {
    let mut func = build_loop_i64(Red::XorIvAffine);
    let mut pass = NeonMinMaxPass::new();
    assert!(
        pass.run(&mut func),
        "i64 affine-iv XOR must vectorize on .2D"
    );
    assert!(
        count(&func, AArch64Opcode::NeonDupGen) >= 1,
        "iv splat (DUP .2D)"
    );
    assert!(
        count(&func, AArch64Opcode::NeonEorV) >= 2 * UNROLL,
        "term ^ + accumulate ^"
    );
    assert_all_2d(&func);
}

/// i64 PRODUCT reduction must BAIL: `MUL.2D` is UNALLOCATED in the ISA — there
/// is nothing sound to emit, so the loop stays scalar (fail-closed).
#[test]
fn i64_product_bails_no_mul_2d() {
    let mut func = build_loop_i64(Red::Bitwise(AArch64Opcode::MulRR));
    let mut pass = NeonMinMaxPass::new();
    assert!(!pass.run(&mut func), "i64 product must BAIL (no MUL.2D)");
    assert_eq!(
        count(&func, AArch64Opcode::NeonMulV),
        0,
        "no vector MUL emitted"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        0,
        "no NEON loads"
    );
}

// ---------------------------------------------------------------------------
// argmin / argmax index-tracking (3 carried vars, dual select)
// ---------------------------------------------------------------------------

/// How the second (non-iv, non-best_val) carried var is written.
enum IdxSel {
    /// Proper argmin/argmax: `bi' = (v cmp bv) ? iv : bi` (index tracking).
    PicksIv,
    /// The second select picks the LOAD, not the iv — a second value reduction,
    /// NOT an index. Must BAIL.
    PicksLoad,
}

/// Build the rotated `for i in 0..n: if a[i] <cc_real> bv { bv=a[i]; bi=i; }`
/// argmin/argmax loop (guard / header / latch), with THREE carried vars
/// (iv=v(5), best_val=v(6), best_idx=v(7)). The value + index selects share one
/// materialised compare (`CSet cc_real`, two `Csel NE`), the shape neon_minmax
/// sees before if-conversion.
fn build_argminmax_loop(cc_real: i64, sel: IdxSel) -> MachFunction {
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
    // Preheader.
    push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base
    push(&mut func, bb0, Copy, vec![v(1), v(1)]); // n
    push(&mut func, bb0, Movz, vec![v(2), i(0x7fff)]); // seed (value irrelevant)
    push(&mut func, bb0, Movz, vec![v(3), i(0)]);
    push(&mut func, bb0, Movz, vec![v(4), i(1)]);
    push(&mut func, bb0, Movz, vec![v64(40), i(4)]); // element size
    push(&mut func, bb0, MovR, vec![v(5), v(3)]); // iv = 0
    push(&mut func, bb0, MovR, vec![v(6), v(2)]); // best_val = seed
    push(&mut func, bb0, MovR, vec![v(7), v(3)]); // best_idx = 0
    push(&mut func, bb0, B, vec![b(guard)]);
    // Guard.
    push(&mut func, guard, CmpRR, vec![v(5), v(1)]);
    push(&mut func, guard, BCond, vec![i(CC_LT), b(header)]);
    push(&mut func, guard, B, vec![b(exit)]);
    // Header: address + load + dual select (materialised) + step.
    push(&mut func, header, Sxtw, vec![v64(10), v(5)]);
    push(
        &mut func,
        header,
        Madd,
        vec![v64(11), v64(10), v64(40), v64(0)],
    );
    push(&mut func, header, LdrRI, vec![v(12), v64(11), i(0)]); // v = a[i]
    push(&mut func, header, CmpRR, vec![v(12), v(6)]); // cmp v, best_val
    push(&mut func, header, CSet, vec![v64(13), i(cc_real)]);
    // value select: bv' = (v cc bv) ? v : bv.
    push(&mut func, header, CmpRI, vec![v64(13), i(0)]);
    push(&mut func, header, Csel, vec![v(20), v(12), v(6), i(CC_NE)]);
    // index (or second-value) select: bi' = (v cc bv) ? {iv|v} : bi.
    let idx_true = match sel {
        IdxSel::PicksIv => v(5),
        IdxSel::PicksLoad => v(12),
    };
    push(&mut func, header, CmpRI, vec![v64(13), i(0)]);
    push(
        &mut func,
        header,
        Csel,
        vec![v(21), idx_true, v(7), i(CC_NE)],
    );
    push(&mut func, header, AddRR, vec![v(22), v(5), v(4)]); // iv+1
    push(&mut func, header, B, vec![b(latch)]);
    // Latch: 3 writebacks + compare + branch.
    push(&mut func, latch, AddRI, vec![v(5), v(22), i(0)]); // iv
    push(&mut func, latch, AddRI, vec![v(6), v(20), i(0)]); // best_val
    push(&mut func, latch, AddRI, vec![v(7), v(21), i(0)]); // best_idx
    push(&mut func, latch, CmpRR, vec![v(5), v(1)]);
    push(&mut func, latch, BCond, vec![i(CC_LT), b(header)]);
    // Exit.
    push(&mut func, exit, MovR, vec![v(30), v(7)]);
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

fn fires_arg(cc_real: i64, sel: IdxSel) -> (bool, MachFunction) {
    let mut func = build_argminmax_loop(cc_real, sel);
    let mut pass = NeonMinMaxPass::new();
    let changed = pass.run(&mut func);
    (changed, func)
}

/// Signed argmin (`slt`) vectorizes with the index-tracking structure: one
/// `CMGT.4S` mask + one value `BIT` + one index `BIT` per accumulator, 32 UMOV
/// lane extracts (16 value + 16 index) at the lexicographic exit fold.
#[test]
fn vectorizes_argmin_signed() {
    let (changed, func) = fires_arg(CC_LT, IdxSel::PicksIv);
    assert!(changed, "signed argmin must vectorize");
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmgtV),
        UNROLL,
        "1 CMGT.4S mask / accum"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmhiV),
        0,
        "signed uses CMGT not CMHI"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonBitV),
        2 * UNROLL,
        "value + index BIT / accum"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        UNROLL / 2,
        "2 LDP q,q"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonUmovGen),
        2 * UNROLL * VF as usize,
        "16 value + 16 index lane extracts"
    );
    // MOVI-zero iota base + all 4 accumulators' identity/index setup use INS.
    assert!(
        count(&func, AArch64Opcode::NeonInsGen) >= 3,
        "iota built via INS"
    );
}

/// Signed argmax (`sgt`) mirrors argmin (same CMGT compare, opposite orient).
#[test]
fn vectorizes_argmax_signed() {
    let (changed, func) = fires_arg(CC_GT, IdxSel::PicksIv);
    assert!(changed, "signed argmax must vectorize");
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmgtV),
        UNROLL,
        "CMGT.4S mask / accum"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonBitV),
        2 * UNROLL,
        "value + index BIT"
    );
}

/// Unsigned argmin (`ult`) uses the unsigned compare `CMHI.4S`.
#[test]
fn vectorizes_argmin_unsigned() {
    let (changed, func) = fires_arg(CC_LO, IdxSel::PicksIv);
    assert!(changed, "unsigned argmin must vectorize");
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmhiV),
        UNROLL,
        "CMHI.4S mask / accum"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmgtV),
        0,
        "unsigned uses CMHI not CMGT"
    );
}

/// Unsigned argmax (`ugt`) uses `CMHI.4S` too (opposite orientation).
#[test]
fn vectorizes_argmax_unsigned() {
    let (changed, func) = fires_arg(CC_HI, IdxSel::PicksIv);
    assert!(changed, "unsigned argmax must vectorize");
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmhiV),
        UNROLL,
        "CMHI.4S mask / accum"
    );
}

/// A NON-STRICT select (`sle`) is a LAST-occurrence loop — a different monoid
/// than the strict first-occurrence one the vector path reproduces. Must BAIL.
#[test]
fn bails_argmin_nonstrict_last_occurrence() {
    let (changed, func) = fires_arg(CC_LE, IdxSel::PicksIv);
    assert!(
        !changed,
        "non-strict (<=) argmin must BAIL (last-occurrence)"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        0,
        "no NEON emitted"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonBitV), 0);
}

/// When the second carried var is NOT an index (its select picks the LOAD, i.e.
/// a second value reduction), this is not an argmin — must BAIL.
#[test]
fn bails_second_carried_var_not_index() {
    let (changed, func) = fires_arg(CC_LT, IdxSel::PicksLoad);
    assert!(!changed, "second value reduction (not an index) must BAIL");
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        0,
        "no NEON emitted"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonCmgtV), 0);
}

/// `cc_true_on_equal` must classify strict vs non-strict correctly — the
/// strictness gate the argmin soundness rests on.
#[test]
fn cc_true_on_equal_classification() {
    for cc in [CC_GT, CC_LT, CC_HI, CC_LO, CC_NE] {
        assert!(!cc_true_on_equal(cc), "cc={cc} is strict (false on equal)");
    }
    for cc in [CC_GE, CC_LE, CC_HS, CC_LS, CC_EQ] {
        assert!(
            cc_true_on_equal(cc),
            "cc={cc} is non-strict (true on equal)"
        );
    }
}

// ---------------------------------------------------------------------------
// i64 (`.2D`) argmin / argmax mirror
// ---------------------------------------------------------------------------

/// All `Imm` operands of every instance of `op`, in program order.
fn imms_of(func: &MachFunction, op: AArch64Opcode) -> Vec<Vec<i64>> {
    func.blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .filter(|&id| func.inst(id).opcode == op)
        .map(|id| {
            func.inst(id)
                .operands
                .iter()
                .filter_map(|o| match o {
                    MachOperand::Imm(x) => Some(*x),
                    _ => None,
                })
                .collect()
        })
        .collect()
}

/// Build the i64 argmin/argmax loop: THREE `Gpr64` carried vars (iv=v64(5),
/// best_val=v64(6), best_idx=v64(7)), `a[i] = *(base + iv*8)`, dual select
/// under one materialised strict compare — the `.2D` mirror of
/// [`build_argminmax_loop`].
fn build_argminmax_loop_i64(cc_real: i64, sel: IdxSel) -> MachFunction {
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
    // Preheader.
    push(&mut func, bb0, Copy, vec![v64(0), v64(0)]); // base
    push(&mut func, bb0, Copy, vec![v64(1), v64(1)]); // n
    push(&mut func, bb0, Movz, vec![v64(2), i(0x7fff)]); // seed (value irrelevant)
    push(&mut func, bb0, Movz, vec![v64(3), i(0)]);
    push(&mut func, bb0, Movz, vec![v64(4), i(1)]);
    push(&mut func, bb0, Movz, vec![v64(40), i(8)]); // element size
    push(&mut func, bb0, MovR, vec![v64(5), v64(3)]); // iv = 0
    push(&mut func, bb0, MovR, vec![v64(6), v64(2)]); // best_val = seed
    push(&mut func, bb0, MovR, vec![v64(7), v64(3)]); // best_idx = 0
    push(&mut func, bb0, B, vec![b(guard)]);
    // Guard.
    push(&mut func, guard, CmpRR, vec![v64(5), v64(1)]);
    push(&mut func, guard, BCond, vec![i(CC_LT), b(header)]);
    push(&mut func, guard, B, vec![b(exit)]);
    // Header: i64 address (iv directly, no sxtw) + load + dual select + step.
    push(
        &mut func,
        header,
        Madd,
        vec![v64(11), v64(5), v64(40), v64(0)],
    );
    push(&mut func, header, LdrRI, vec![v64(12), v64(11), i(0)]); // v = a[i]
    push(&mut func, header, CmpRR, vec![v64(12), v64(6)]); // cmp v, best_val
    push(&mut func, header, CSet, vec![v64(13), i(cc_real)]);
    // value select: bv' = (v cc bv) ? v : bv.
    push(&mut func, header, CmpRI, vec![v64(13), i(0)]);
    push(
        &mut func,
        header,
        Csel,
        vec![v64(20), v64(12), v64(6), i(CC_NE)],
    );
    // index (or second-value) select: bi' = (v cc bv) ? {iv|v} : bi.
    let idx_true = match sel {
        IdxSel::PicksIv => v64(5),
        IdxSel::PicksLoad => v64(12),
    };
    push(&mut func, header, CmpRI, vec![v64(13), i(0)]);
    push(
        &mut func,
        header,
        Csel,
        vec![v64(21), idx_true, v64(7), i(CC_NE)],
    );
    push(&mut func, header, AddRR, vec![v64(22), v64(5), v64(4)]); // iv+1
    push(&mut func, header, B, vec![b(latch)]);
    // Latch: 3 writebacks + compare + branch.
    push(&mut func, latch, AddRI, vec![v64(5), v64(22), i(0)]); // iv
    push(&mut func, latch, AddRI, vec![v64(6), v64(20), i(0)]); // best_val
    push(&mut func, latch, AddRI, vec![v64(7), v64(21), i(0)]); // best_idx
    push(&mut func, latch, CmpRR, vec![v64(5), v64(1)]);
    push(&mut func, latch, BCond, vec![i(CC_LT), b(header)]);
    // Exit.
    push(&mut func, exit, MovR, vec![v64(30), v64(7)]);
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

fn fires_arg_i64(cc_real: i64, sel: IdxSel) -> (bool, MachFunction) {
    let mut func = build_argminmax_loop_i64(cc_real, sel);
    let mut pass = NeonMinMaxPass::new();
    let changed = pass.run(&mut func);
    (changed, func)
}

/// Signed i64 argmin vectorizes on `.2D`: one `CMGT.2D` mask + value/index
/// `BIT` per accumulator, `2 * UNROLL * 2` UMOV.D lane extracts at the exit
/// fold, D-element iota/DUP, and the i64 precheck + unsigned guard.
#[test]
fn vectorizes_argmin_signed_i64() {
    let (changed, func) = fires_arg_i64(CC_LT, IdxSel::PicksIv);
    assert!(changed, "signed i64 argmin must vectorize");
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmgtV),
        UNROLL,
        "1 CMGT.2D mask / accum"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmhiV),
        0,
        "signed uses CMGT not CMHI"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonBitV),
        2 * UNROLL,
        "value + index BIT / accum"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        UNROLL / 2,
        "2 LDP q,q"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonUmovGen),
        2 * UNROLL * VF_I64 as usize,
        "8 value + 8 index lane extracts"
    );
    // Every arrangement-carrying compare/add is `.2D`; every UMOV/INS/DUP is a
    // D element.
    for imms in imms_of(&func, AArch64Opcode::NeonCmgtV) {
        assert_eq!(imms, vec![ARR_D2], "mask compare at .2D");
    }
    for imms in imms_of(&func, AArch64Opcode::NeonAddV) {
        assert_eq!(imms, vec![ARR_D2], "index adds at .2D");
    }
    for imms in imms_of(&func, AArch64Opcode::NeonUmovGen) {
        assert_eq!(imms.last(), Some(&ELEM_D), "UMOV extracts D lanes");
    }
    for imms in imms_of(&func, AArch64Opcode::NeonDupGen) {
        assert_eq!(imms, vec![ELEM_D], "DUP broadcasts D elements");
    }
    // The iota is [0, 1]: exactly one INS (lane 1) at the D element code.
    assert_eq!(
        count(&func, AArch64Opcode::NeonInsGen),
        1,
        ".2D iota has one INS"
    );
    assert_eq!(
        imms_of(&func, AArch64Opcode::NeonInsGen),
        vec![vec![1, ELEM_D]],
        "INS lane 1, D element"
    );
    // The i64 precheck (`n < 8 -> scalar`) exists: a CmpRI against the width.
    assert!(
        imms_of(&func, AArch64Opcode::CmpRI)
            .iter()
            .any(|imms| imms == &vec![UNROLL as i64 * VF_I64]),
        "i64 precheck compares the bound against width 8"
    );
}

/// Unsigned i64 argmax uses `CMHI.2D` (opposite orientation, same structure).
#[test]
fn vectorizes_argmax_unsigned_i64() {
    let (changed, func) = fires_arg_i64(CC_HI, IdxSel::PicksIv);
    assert!(changed, "unsigned i64 argmax must vectorize");
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmhiV),
        UNROLL,
        "CMHI.2D mask / accum"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonCmgtV),
        0,
        "unsigned uses CMHI not CMGT"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonBitV),
        2 * UNROLL,
        "value + index BIT"
    );
}

/// The strictness gate is width-independent: a non-strict i64 select (`<=`,
/// LAST occurrence) must BAIL exactly as on i32.
#[test]
fn bails_argmin_nonstrict_i64() {
    let (changed, func) = fires_arg_i64(CC_LE, IdxSel::PicksIv);
    assert!(
        !changed,
        "non-strict (<=) i64 argmin must BAIL (last-occurrence)"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        0,
        "no NEON emitted"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonBitV), 0);
}

/// The not-an-index bail is width-independent too.
#[test]
fn bails_second_carried_var_not_index_i64() {
    let (changed, func) = fires_arg_i64(CC_LT, IdxSel::PicksLoad);
    assert!(
        !changed,
        "i64 second value reduction (not an index) must BAIL"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        0,
        "no NEON emitted"
    );
}

/// Shape pin: the i32 argmin still lowers at `.4S`/S-element codes with the
/// 3-INS iota and 32 S-lane extracts — the i64 mirror must not perturb the
/// shipped width (the fuzzer additionally diffs object bytes against the
/// pre-mirror goldens).
#[test]
fn i32_argmin_untouched_by_i64_mirror() {
    let (changed, func) = fires_arg(CC_LT, IdxSel::PicksIv);
    assert!(changed);
    for imms in imms_of(&func, AArch64Opcode::NeonCmgtV) {
        assert_eq!(imms, vec![ARR_S4], "i32 mask compare stays at .4S");
    }
    for imms in imms_of(&func, AArch64Opcode::NeonAddV) {
        assert_eq!(imms, vec![ARR_S4], "i32 index adds stay at .4S");
    }
    for imms in imms_of(&func, AArch64Opcode::NeonUmovGen) {
        assert_eq!(imms.last(), Some(&ELEM_S), "i32 UMOV stays at S lanes");
    }
    assert_eq!(
        count(&func, AArch64Opcode::NeonInsGen),
        3,
        "i32 iota keeps 3 INS"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonUmovGen),
        2 * UNROLL * VF as usize,
        "i32 exit fold keeps 32 extracts"
    );
}

// ---------------------------------------------------------------------------
// Forward bounds-guarded CHAIN (branch-diamond min/max) tests
// ---------------------------------------------------------------------------

/// One min/max reduction expressed as a control-flow BRANCH DIAMOND inside a
/// forward `while iv <u N` (const `N`) chain, as the bridge emits for
/// `for i in 0..N { if a[i] REL acc { acc = a[i] } }` after bounds-check-elim.
struct DiamondSpec {
    /// The `b.<cc>` taken condition of the compare (CC_GT/CC_LT/CC_HI/CC_LO).
    cc: i64,
    /// Distinct base register id for the loaded array (`a`, `b`, ...).
    base: u32,
}

/// Build a K-reduction forward-chain min/max loop (mixed `Gpr64` iv / `Gpr32`
/// element, const bound `N = 100`). Layout per reduction `r`: a compare block
/// `cmp a[iv], acc_r; b.<cc> cand_r; b else_r`, a candidate tail `cand_r` that
/// RELOADS `a[iv]` and sets `res_r = a[iv]`, and an else tail `else_r` that sets
/// `res_r = acc_r`; both converge at the next compare (or the latch). The latch
/// writes `iv += 1` and each `acc_r = res_r`.
fn build_chain(specs: &[DiamondSpec]) -> MachFunction {
    use AArch64Opcode::*;
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    // Per reduction: (compare, cand_tail, else_tail).
    let dblocks: Vec<(BlockId, BlockId, BlockId)> = specs
        .iter()
        .map(|_| {
            (
                func.create_block(),
                func.create_block(),
                func.create_block(),
            )
        })
        .collect();
    let latch = func.create_block();
    let exit = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };

    let iv = 5u32; // Gpr64 induction
    let es = 40u32; // Gpr64 element-size constant (4)
    let mut vid = 60u32; // fresh vreg cursor
    let fresh = |c: &mut u32| {
        let x = *c;
        *c += 1;
        x
    };

    // Preheader: base pointers, es const, iv=0, per-reduction acc seed.
    for spec in specs {
        push(&mut func, bb0, Movz, vec![v64(spec.base), i(0)]); // base def (dominates)
    }
    push(&mut func, bb0, Movz, vec![v64(es), i(4)]);
    push(&mut func, bb0, Movz, vec![v64(iv), i(0)]);
    for (ri, _) in specs.iter().enumerate() {
        push(&mut func, bb0, Movz, vec![v(6 + ri as u32), i(0)]); // acc_r seed
    }
    push(&mut func, bb0, B, vec![b(header)]);

    // Header: const-N loop-continue diamond `cmp ivc, #100; b.lo <first>; b exit`.
    let ivc = fresh(&mut vid);
    push(&mut func, header, MovR, vec![v64(ivc), v64(iv)]);
    push(&mut func, header, CmpRI, vec![v64(ivc), i(100)]);
    let first_body = dblocks[0].0;
    push(&mut func, header, BCond, vec![i(CC_LO), b(first_body)]);
    push(&mut func, header, B, vec![b(exit)]);

    func.add_edge(bb0, header);
    func.add_edge(header, first_body);
    func.add_edge(header, exit);

    // Each reduction diamond; the join is the next compare block, or the latch.
    for (ri, spec) in specs.iter().enumerate() {
        let (cmp_blk, cand_blk, else_blk) = dblocks[ri];
        let acc_r = 6 + ri as u32;
        let res_r = 20 + ri as u32; // the phi result (two defs)
        let join = if ri + 1 < specs.len() {
            dblocks[ri + 1].0
        } else {
            latch
        };

        // compare: load a[iv], copy acc, cmp, branch.
        let addr = fresh(&mut vid);
        let ld = fresh(&mut vid);
        let accc = fresh(&mut vid);
        push(
            &mut func,
            cmp_blk,
            Madd,
            vec![v64(addr), v64(iv), v64(es), v64(spec.base)],
        );
        push(&mut func, cmp_blk, LdrRI, vec![v(ld), v64(addr), i(0)]);
        push(&mut func, cmp_blk, MovR, vec![v(accc), v(acc_r)]);
        push(&mut func, cmp_blk, CmpRR, vec![v(ld), v(accc)]);
        push(&mut func, cmp_blk, BCond, vec![i(spec.cc), b(cand_blk)]);
        push(&mut func, cmp_blk, B, vec![b(else_blk)]);
        // cand tail: RELOAD a[iv], res = a[iv].
        let addr2 = fresh(&mut vid);
        let ld2 = fresh(&mut vid);
        push(
            &mut func,
            cand_blk,
            Madd,
            vec![v64(addr2), v64(iv), v64(es), v64(spec.base)],
        );
        push(&mut func, cand_blk, LdrRI, vec![v(ld2), v64(addr2), i(0)]);
        push(&mut func, cand_blk, MovR, vec![v(res_r), v(ld2)]);
        push(&mut func, cand_blk, B, vec![b(join)]);
        // else tail: res = acc.
        push(&mut func, else_blk, MovR, vec![v(res_r), v(acc_r)]);
        push(&mut func, else_blk, B, vec![b(join)]);

        func.add_edge(cmp_blk, cand_blk);
        func.add_edge(cmp_blk, else_blk);
        func.add_edge(cand_blk, join);
        func.add_edge(else_blk, join);
    }

    // Latch: iv += 1; writeback each acc; back-edge.
    let ivn = fresh(&mut vid);
    push(&mut func, latch, AddRI, vec![v64(ivn), v64(iv), i(1)]);
    push(&mut func, latch, MovR, vec![v64(iv), v64(ivn)]);
    for (ri, _) in specs.iter().enumerate() {
        push(
            &mut func,
            latch,
            MovR,
            vec![v(6 + ri as u32), v(20 + ri as u32)],
        );
    }
    push(&mut func, latch, B, vec![b(header)]);
    push(&mut func, exit, Ret, vec![]);

    func.add_edge(latch, header);
    func.next_vreg = 256;
    func
}

fn fires_chain(specs: &[DiamondSpec]) -> (bool, MachFunction) {
    let mut func = build_chain(specs);
    let mut pass = NeonMinMaxPass::new();
    let changed = pass.run(&mut func);
    (changed, func)
}

#[test]
fn chain_vectorizes_single_smax() {
    let (changed, func) = fires_chain(&[DiamondSpec { cc: CC_GT, base: 0 }]);
    assert!(changed, "single branch-diamond smax chain should vectorize");
    assert!(
        count(&func, AArch64Opcode::NeonSmaxV) >= UNROLL,
        "SMAX.4S per accumulator"
    );
    assert_eq!(
        count(&func, AArch64Opcode::NeonSminV),
        0,
        "no SMIN for a max reduction"
    );
    assert!(
        count(&func, AArch64Opcode::NeonLdpQPost) >= UNROLL / 2,
        "paired vector loads"
    );
    // IntMin identity seeding: Movz(1)+DUP+SHL per accumulator.
    assert!(
        count(&func, AArch64Opcode::NeonShlVImm) >= UNROLL,
        "INT_MIN via SHL"
    );
}

#[test]
fn chain_vectorizes_single_umin() {
    let (changed, func) = fires_chain(&[DiamondSpec { cc: CC_LO, base: 0 }]);
    assert!(changed, "single branch-diamond umin chain should vectorize");
    assert!(
        count(&func, AArch64Opcode::NeonUminV) >= UNROLL,
        "UMIN.4S per accumulator"
    );
}

#[test]
fn chain_vectorizes_dual_smax_smin() {
    // Two independent reductions over the SAME array in one loop (the d10 shape).
    let (changed, func) = fires_chain(&[
        DiamondSpec { cc: CC_GT, base: 0 },
        DiamondSpec { cc: CC_LT, base: 0 },
    ]);
    assert!(changed, "dual smax+smin chain should vectorize");
    assert!(
        count(&func, AArch64Opcode::NeonSmaxV) >= UNROLL,
        "SMAX.4S for the max"
    );
    assert!(
        count(&func, AArch64Opcode::NeonSminV) >= UNROLL,
        "SMIN.4S for the min"
    );
    // Two accumulators => two horizontal drains of VF lanes each.
    assert_eq!(
        count(&func, AArch64Opcode::NeonUmovGen),
        2 * VF as usize,
        "one 4-lane drain per reduction"
    );
    // Both reductions share ONE array => a single stream of paired loads.
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        UNROLL / 2,
        "one shared load stream"
    );
}

#[test]
fn chain_vectorizes_dual_two_arrays() {
    // max of a[], min of b[]: two distinct streams.
    let (changed, func) = fires_chain(&[
        DiamondSpec { cc: CC_GT, base: 0 },
        DiamondSpec { cc: CC_LT, base: 1 },
    ]);
    assert!(changed, "dual two-array chain should vectorize");
    assert_eq!(
        count(&func, AArch64Opcode::NeonLdpQPost),
        UNROLL,
        "two independent load streams"
    );
}

#[test]
fn chain_preserves_scalar_loop() {
    // The transform is ADDITIVE: the vector loop is spliced in FRONT and the
    // original scalar diamond block is left byte-identical.
    let before = build_chain(&[DiamondSpec { cc: CC_GT, base: 0 }]);
    let cmp_blk = BlockId(2);
    let scalar_ops: Vec<AArch64Opcode> = before
        .block(cmp_blk)
        .insts
        .iter()
        .map(|&id| before.inst(id).opcode)
        .collect();
    let (changed, func) = fires_chain(&[DiamondSpec { cc: CC_GT, base: 0 }]);
    assert!(changed);
    let after_ops: Vec<AArch64Opcode> = func
        .block(cmp_blk)
        .insts
        .iter()
        .map(|&id| func.inst(id).opcode)
        .collect();
    assert_eq!(after_ops, scalar_ops, "scalar diamond block left untouched");
    // The scalar loop header still exists and the SMAX vector loop was added.
    assert!(count(&func, AArch64Opcode::NeonSmaxV) >= UNROLL);
}

/// A `CmpRR(iv, N_reg)` register bound (not the folded constant) must BAIL: the
/// chain path only vectorizes a compile-time constant bound.
#[test]
fn chain_bails_on_register_bound() {
    let mut func = build_chain(&[DiamondSpec { cc: CC_GT, base: 0 }]);
    // Rewrite the header loop-continue from `CmpRI(ivc, #100)` to `CmpRR(ivc, n)`.
    let header = BlockId(1);
    let hinsts = func.block(header).insts.clone();
    for id in hinsts {
        if func.inst(id).opcode == AArch64Opcode::CmpRI {
            let ivc = func.inst(id).operands[0].clone();
            *func.inst_mut(id) = MachInst::new(AArch64Opcode::CmpRR, vec![ivc, v64(1)]);
        }
    }
    let mut pass = NeonMinMaxPass::new();
    let changed = pass.run(&mut func);
    assert!(
        !changed,
        "a register loop bound must BAIL (const-only chain)"
    );
    assert_eq!(count(&func, AArch64Opcode::NeonSmaxV), 0, "no SIMD on bail");
}

/// A shifted index `a[iv+1]` in the compare candidate must BAIL (not `a[iv]`).
#[test]
fn chain_bails_on_shifted_index() {
    let mut func = build_chain(&[DiamondSpec { cc: CC_GT, base: 0 }]);
    // In the compare block (BlockId(2)), replace the load-address index `iv`
    // with `iv+1` so the candidate is no longer `a[iv]`.
    let cmp_blk = BlockId(2);
    let cinsts = func.block(cmp_blk).insts.clone();
    // Insert `AddRI ivp1 = iv + 1` and point the Madd's index at it.
    let ivp1 = VReg::new(200, RegClass::Gpr64);
    let addid = func.push_inst(MachInst::new(
        AArch64Opcode::AddRI,
        vec![MachOperand::VReg(ivp1), v64(5), i(1)],
    ));
    // Prepend by rebuilding the block insts.
    let madd = cinsts[0];
    debug_assert_eq!(func.inst(madd).opcode, AArch64Opcode::Madd);
    *func.inst_mut(madd) = MachInst::new(
        AArch64Opcode::Madd,
        vec![
            func.inst(madd).operands[0].clone(),
            MachOperand::VReg(ivp1),
            v64(40),
            v64(0),
        ],
    );
    func.block_mut(cmp_blk).insts.insert(0, addid);
    let mut pass = NeonMinMaxPass::new();
    let changed = pass.run(&mut func);
    assert!(!changed, "a shifted `a[iv+1]` candidate must BAIL");
    assert_eq!(count(&func, AArch64Opcode::NeonSmaxV), 0, "no SIMD on bail");
}
