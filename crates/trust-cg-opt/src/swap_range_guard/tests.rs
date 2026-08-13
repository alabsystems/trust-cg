// Unit tests for the `swap-range-guard` hoisted-range-guard swap fast path.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use trust_cg_ir::Signature;

fn x(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn w(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
}
fn i(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}
fn bl(b: BlockId) -> MachOperand {
    MachOperand::Block(b)
}
fn count_op(func: &MachFunction, op: AArch64Opcode) -> usize {
    func.blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .filter(|&id| func.inst(id).opcode == op)
        .count()
}

/// Negative-control mutations of the canonical transpose swap loop.
#[derive(Clone, Copy, PartialEq)]
enum Variant {
    Good,
    /// `Madd i1, S, y, x` factor order (still `y*S + x`) -> FIRE.
    SwappedFactors,
    /// Phi-copy latch induction (`t = x+1; x = MovR t`) -> FIRE.
    PhiLatch,
    /// Stores NOT crosswise (each store writes back its own load) -> BAIL.
    NotCrosswise,
    /// One bounds check uses a different K -> BAIL.
    DifferingK,
    /// The second index expression uses a different S -> BAIL.
    DifferingS,
    /// `y` is (re)defined inside the loop -> BAIL.
    YInLoop,
    /// `y` is an OUTER-loop induction: dominating init + a second def in a
    /// non-dominating later block (the outer latch) -> FIRE (the d08 shape).
    OuterIvY,
    /// `S*es` exceeds the AddRI pointer-bump range -> BAIL.
    HugeS,
    /// Trip bound C below the minimum -> BAIL.
    TinyC,
    /// A non-whitelisted op (`AddRR`) in the body -> BAIL.
    ExtraOp,
    /// An extra whitelisted-but-ungrammatical op (spare `AddRI`) -> BAIL.
    ExtraAddRI,
    /// A load at a non-zero immediate offset -> BAIL.
    OffsetLoad,
    /// The four checks do not share one abort target -> BAIL.
    SplitAbort,
    /// The latch ends in a conditional branch (extra successor) -> BAIL.
    BranchyLatch,
    /// The header compares a Gpr32 truncation of the iv -> BAIL.
    Cmp32,
    /// A stray non-iv compare between the iv compare and the BCond -> BAIL.
    StrayCmp,
}

/// Build the canonical 6-block bounds-checked crosswise swap loop mirroring
/// the bridge lowering of `while x < 32 { a.swap(y*32+x, x*32+y) }` with
/// per-access expanded checks (`cmp idx,#1024; b.lo next; b abort`):
/// ```text
/// bb0:    base=x0, y=x4 (invariant), S=Movz 32, es=Movz 4, x3=0; B header
/// header: CmpRI x3,#C; BCond LO c1; B exit
/// c1:     i1=Madd(y,S,x3);   CmpRI i1,#K;  BCond LO c2; B abt
/// c2:     a1=Madd(i1,es,x0); w8=Ldr[a1];  i2=Madd(x3,S,y);  CmpRI i2,#K;  BCond LO c3; B abt
/// c3:     a2=Madd(i2,es,x0); w11=Ldr[a2]; i3=Madd(y,S,x3);  CmpRI i3,#K;  BCond LO c4; B abt
/// c4:     a3=Madd(i3,es,x0); Str w11,[a3]; i4=Madd(x3,S,y); CmpRI i4,#K;  BCond LO lt; B abt
/// lt:     a4=Madd(i4,es,x0); Str w8,[a4]; x3+=1; B header
/// abt:    B exit   (shared abort join, outside the loop)
/// exit:   reads only invariants
/// ```
fn build_swap(variant: Variant) -> MachFunction {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    let c1 = func.create_block();
    let c2 = func.create_block();
    let c3 = func.create_block();
    let c4 = func.create_block();
    let lt = func.create_block();
    let abt = func.create_block();
    let abt2 = func.create_block();
    let exit = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;

    let k: i64 = 1024;
    let k3: i64 = if variant == Variant::DifferingK {
        1023
    } else {
        1024
    };
    let s: i64 = if variant == Variant::HugeS { 2000 } else { 32 };
    let c: i64 = if variant == Variant::TinyC { 1 } else { 32 };

    // --- bb0: invariants + iv init.
    push(&mut func, bb0, Copy, vec![x(0), x(0)]); // base
    push(&mut func, bb0, Copy, vec![x(4), x(4)]); // y
    push(&mut func, bb0, Movz, vec![x(30), i(s)]); // S
    if variant == Variant::DifferingS {
        push(&mut func, bb0, Movz, vec![x(31), i(16)]); // rogue S'
    }
    push(&mut func, bb0, Movz, vec![x(28), i(4)]); // es
    push(&mut func, bb0, Movz, vec![x(40), i(0)]);
    push(&mut func, bb0, MovR, vec![x(3), x(40)]); // iv init
    push(&mut func, bb0, B, vec![bl(header)]);
    func.add_edge(bb0, header);

    // --- header.
    if variant == Variant::Cmp32 {
        push(&mut func, header, MovR, vec![w(15), x(3)]);
        push(&mut func, header, CmpRI, vec![w(15), i(c)]);
    } else {
        push(&mut func, header, CmpRI, vec![x(3), i(c)]);
    }
    if variant == Variant::StrayCmp {
        push(&mut func, header, CmpRI, vec![x(0), i(0)]);
    }
    push(&mut func, header, BCond, vec![i(3), bl(c1)]);
    push(&mut func, header, B, vec![bl(exit)]);
    func.add_edge(header, c1);
    func.add_edge(header, exit);

    // --- c1: i1 = y*S + x, check.
    if variant == Variant::YInLoop {
        push(&mut func, c1, MovR, vec![x(4), x(44)]); // y redefined in body
    }
    if variant == Variant::SwappedFactors {
        push(&mut func, c1, Madd, vec![x(5), x(30), x(4), x(3)]);
    } else {
        push(&mut func, c1, Madd, vec![x(5), x(4), x(30), x(3)]);
    }
    if variant == Variant::ExtraOp {
        push(&mut func, c1, AddRR, vec![x(70), x(0), x(0)]);
    }
    if variant == Variant::ExtraAddRI {
        push(&mut func, c1, AddRI, vec![x(71), x(0), i(8)]);
    }
    push(&mut func, c1, CmpRI, vec![x(5), i(k)]);
    push(&mut func, c1, BCond, vec![i(3), bl(c2)]);
    push(&mut func, c1, B, vec![bl(abt)]);
    func.add_edge(c1, c2);
    func.add_edge(c1, abt);

    // --- c2: a1 = i1*es + base; w8 = load; i2 = x*S + y; check.
    push(&mut func, c2, Madd, vec![x(7), x(5), x(28), x(0)]);
    if variant == Variant::OffsetLoad {
        push(&mut func, c2, LdrRI, vec![w(8), x(7), i(4)]);
    } else {
        push(&mut func, c2, LdrRI, vec![w(8), x(7), i(0)]);
    }
    push(&mut func, c2, Madd, vec![x(9), x(3), x(30), x(4)]);
    push(&mut func, c2, CmpRI, vec![x(9), i(k)]);
    push(&mut func, c2, BCond, vec![i(3), bl(c3)]);
    if variant == Variant::SplitAbort {
        push(&mut func, c2, B, vec![bl(abt2)]);
        func.add_edge(c2, abt2);
    } else {
        push(&mut func, c2, B, vec![bl(abt)]);
        func.add_edge(c2, abt);
    }
    func.add_edge(c2, c3);

    // --- c3: a2 = i2*es + base; w11 = load; i3 = y*S + x; check.
    push(&mut func, c3, Madd, vec![x(10), x(9), x(28), x(0)]);
    push(&mut func, c3, LdrRI, vec![w(11), x(10), i(0)]);
    push(&mut func, c3, Madd, vec![x(12), x(4), x(30), x(3)]);
    push(&mut func, c3, CmpRI, vec![x(12), i(k3)]);
    push(&mut func, c3, BCond, vec![i(3), bl(c4)]);
    push(&mut func, c3, B, vec![bl(abt)]);
    func.add_edge(c3, c4);
    func.add_edge(c3, abt);

    // --- c4: a3 = i3*es + base; store crosswise; i4 = x*S + y; check.
    push(&mut func, c4, Madd, vec![x(14), x(12), x(28), x(0)]);
    if variant == Variant::NotCrosswise {
        push(&mut func, c4, StrRI, vec![w(8), x(14), i(0)]);
    } else {
        push(&mut func, c4, StrRI, vec![w(11), x(14), i(0)]);
    }
    let s2 = if variant == Variant::DifferingS {
        x(31)
    } else {
        x(30)
    };
    push(&mut func, c4, Madd, vec![x(16), x(3), s2, x(4)]);
    push(&mut func, c4, CmpRI, vec![x(16), i(k)]);
    push(&mut func, c4, BCond, vec![i(3), bl(lt)]);
    push(&mut func, c4, B, vec![bl(abt)]);
    func.add_edge(c4, lt);
    func.add_edge(c4, abt);

    // --- latch: a4 = i4*es + base; store crosswise; x += 1; back-edge.
    push(&mut func, lt, Madd, vec![x(18), x(16), x(28), x(0)]);
    if variant == Variant::NotCrosswise {
        push(&mut func, lt, StrRI, vec![w(11), x(18), i(0)]);
    } else {
        push(&mut func, lt, StrRI, vec![w(8), x(18), i(0)]);
    }
    if variant == Variant::PhiLatch {
        push(&mut func, lt, AddRI, vec![x(33), x(3), i(1)]);
        push(&mut func, lt, MovR, vec![x(3), x(33)]);
    } else {
        push(&mut func, lt, AddRI, vec![x(3), x(3), i(1)]);
    }
    if variant == Variant::BranchyLatch {
        push(&mut func, lt, CmpRI, vec![x(3), i(64)]);
        push(&mut func, lt, BCond, vec![i(3), bl(header)]);
        push(&mut func, lt, B, vec![bl(exit)]);
        func.add_edge(lt, exit);
    } else {
        push(&mut func, lt, B, vec![bl(header)]);
    }
    func.add_edge(lt, header);

    // --- abort join(s) + exit.
    push(&mut func, abt, B, vec![bl(exit)]);
    func.add_edge(abt, exit);
    push(&mut func, abt2, B, vec![bl(exit)]);
    func.add_edge(abt2, exit);
    if variant == Variant::OuterIvY {
        // The outer-latch-style second def of y: outside the loop, in a block
        // that does NOT dominate the preheader.
        push(&mut func, exit, AddRI, vec![x(4), x(4), i(1)]);
    }
    push(&mut func, exit, MovR, vec![x(50), x(0)]);

    func
}

fn run(variant: Variant) -> (MachFunction, bool) {
    let mut func = build_swap(variant);
    let changed = SwapRangeGuardPass::new().run(&mut func);
    (func, changed)
}

// ---------------------------------------------------------------------------
// Positive cases
// ---------------------------------------------------------------------------

#[test]
fn fires_on_canonical_transpose_swap() {
    let (func, changed) = run(Variant::Good);
    assert!(changed, "the canonical d08 swap loop must be rewritten");
    // Scalar loop untouched: its 2 loads + 2 stores remain, plus the fast
    // path's 2 + 2.
    assert_eq!(count_op(&func, AArch64Opcode::LdrRI), 4);
    assert_eq!(count_op(&func, AArch64Opcode::StrRI), 4);
    // Guards: three CmpRR (y, m1, m2) + the original header CmpRI + fast-path
    // x<C entry/bottom CmpRI + 4 scalar checks.
    assert_eq!(count_op(&func, AArch64Opcode::CmpRR), 3);
    // Madd: 8 scalar + m1 + i1/i2/p1/p2 = 13.
    assert_eq!(count_op(&func, AArch64Opcode::Madd), 13);
}

#[test]
fn fires_on_swapped_madd_factors_and_phi_latch() {
    for v in [Variant::SwappedFactors, Variant::PhiLatch] {
        let (func, changed) = run(v);
        assert!(changed, "factor order / phi-copy latch variants must fire");
        assert_eq!(count_op(&func, AArch64Opcode::LdrRI), 4);
    }
}

#[test]
fn fires_on_outer_induction_y() {
    // y has a dominating init AND a non-dominating outer-latch increment —
    // invariant IN this loop; the dominating init makes the guard read safe.
    let (func, changed) = run(Variant::OuterIvY);
    assert!(changed, "outer-iv y (the d08 shape) must fire");
    assert_eq!(count_op(&func, AArch64Opcode::CmpRR), 3);
}

// ---------------------------------------------------------------------------
// Negative controls (every one must BAIL and leave the function unchanged)
// ---------------------------------------------------------------------------

fn assert_bails(variant: Variant, why: &str) {
    let (func, changed) = run(variant);
    assert!(!changed, "must BAIL: {why}");
    assert_eq!(count_op(&func, AArch64Opcode::CmpRR), 0, "{why}");
}

#[test]
fn bails_on_non_crosswise_stores() {
    assert_bails(
        Variant::NotCrosswise,
        "stores write back their own loads (not a swap)",
    );
}

#[test]
fn bails_on_differing_bounds_limits() {
    assert_bails(Variant::DifferingK, "one check uses a different K");
}

#[test]
fn bails_on_differing_strides() {
    assert_bails(Variant::DifferingS, "index expressions disagree on S");
}

#[test]
fn bails_on_y_defined_in_loop() {
    assert_bails(Variant::YInLoop, "y must be loop-invariant");
}

#[test]
fn bails_on_huge_stride() {
    assert_bails(Variant::HugeS, "S*es exceeds the AddRI bump range");
}

#[test]
fn bails_on_tiny_trip_bound() {
    assert_bails(Variant::TinyC, "C below the minimum");
}

#[test]
fn bails_on_non_whitelisted_body_op() {
    assert_bails(Variant::ExtraOp, "AddRR in the body");
}

#[test]
fn bails_on_extra_ungrammatical_op() {
    assert_bails(Variant::ExtraAddRI, "spare AddRI breaks the 16-op grammar");
}

#[test]
fn bails_on_offset_load() {
    assert_bails(Variant::OffsetLoad, "load at non-zero offset");
}

#[test]
fn bails_on_split_abort_targets() {
    assert_bails(Variant::SplitAbort, "checks lack one shared abort target");
}

#[test]
fn bails_on_branchy_latch() {
    assert_bails(
        Variant::BranchyLatch,
        "latch must end in the plain back-edge",
    );
}

#[test]
fn bails_on_32bit_header_compare() {
    assert_bails(Variant::Cmp32, "header compares trunc32(iv)");
}

#[test]
fn bails_on_stray_cmp_before_bcond() {
    assert_bails(Variant::StrayCmp, "stray compare clobbers the BCond flags");
}
