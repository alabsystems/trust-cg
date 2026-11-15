// Unit tests for the loop-state contract's iteration-coverage clause.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Each row builds a scalar counted loop and a rewrite of it by hand, in the
// shapes the trust-cg rewrites take: an IN-PLACE vectorizer (`vectorize`: the
// loop itself runs `vf` iterations per trip), a VECTOR LOOP IN FRONT of the
// scalar loop that stays as the remainder (`neon_fill` and its siblings), and a
// FULL UNROLL (`loop_unroll`). The refused rows are the coverage defects
// `vectorize` shipped and fixed privately: 4b1fb93c7 (an induction plan that
// also divided its own trip bound: 16 of 64 lanes) and a0603f3bc (remainder
// lanes in blocks nothing branched to; an undivided bound past an odd trip
// count, a nonzero start, an inclusive test, a run-time bound).

use std::cell::Cell;

use super::*;
use crate::loop_contract::{ExitPlan, Handoff, LoopExit, LoopLocality};
use trust_cg_ir::X86Opcode;
use trust_cg_ir::{
    AArch64Opcode, BlockId, MachFunction, MachInst, MachOperand, RegClass, Signature, VReg,
};
use trust_cg_lower::function::Signature as X86Signature;
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

thread_local! {
    /// Tests set this to run every loop one iteration at a time.
    pub(super) static NO_ACCELERATION: Cell<bool> = const { Cell::new(false) };
}

const IV: u32 = 10;
const N: u32 = 12;
const OUT: u32 = 20;
const BASE: u32 = 21;
const MB: u32 = 30;
const LOADED: u32 = 40;
const LOADED_V: u32 = 41;

const LO: i64 = 3;
const LS: i64 = 9;
const NE: i64 = 1;
const LT: i64 = 11;

fn x(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn w(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
}
fn imm(value: i64) -> MachOperand {
    MachOperand::Imm(value)
}
fn blk(block: BlockId) -> MachOperand {
    MachOperand::Block(block)
}

fn push(f: &mut MachFunction, block: BlockId, opcode: AArch64Opcode, operands: Vec<MachOperand>) {
    let id = f.push_inst(MachInst::new(opcode, operands));
    f.append_inst(block, id);
}

/// Materialize a 64-bit constant into `reg` (`Movz` + `Movk`s).
fn constant(f: &mut MachFunction, block: BlockId, reg: MachOperand, value: u64) {
    push(
        f,
        block,
        AArch64Opcode::Movz,
        vec![reg.clone(), imm((value & 0xffff) as i64)],
    );
    for shift in [16u32, 32, 48] {
        let part = (value >> shift) & 0xffff;
        if part != 0 {
            push(
                f,
                block,
                AArch64Opcode::Movk,
                vec![reg.clone(), imm(part as i64), imm(i64::from(shift))],
            );
        }
    }
}

#[derive(Clone, Copy)]
enum Start {
    Const(u64),
    /// Live into the loop: an input the clause samples.
    Input,
}

#[derive(Clone, Copy)]
enum Bound {
    /// `cmp iv, #imm`.
    Imm(i64),
    /// `mov n, #value` in the header, then `cmp iv, n` (the O2 shape
    /// `vectorize` reads).
    Header(u64),
    /// `cmp iv, n` with `n` live into the loop.
    Input,
    /// `mov n, #value` in the preheader, then `cmp iv, n`.
    Pre(u64),
}

/// `for (iv = start; iv <cond> bound; iv += step)`, top-tested.
#[derive(Clone, Copy)]
struct Counted {
    start: Start,
    bound: Bound,
    cond: i64,
    step: i64,
    /// Registers as `Gpr32` (`w`) instead of `Gpr64`.
    narrow: bool,
}

impl Counted {
    fn new(start: Start, bound: Bound) -> Self {
        Counted {
            start,
            bound,
            cond: LO,
            step: 1,
            narrow: false,
        }
    }
    fn reg(&self, id: u32) -> MachOperand {
        if self.narrow { w(id) } else { x(id) }
    }
}

struct Built {
    func: MachFunction,
    pre: BlockId,
    header: BlockId,
    body: BlockId,
    exit: BlockId,
    /// A block outside the loop a data exit leaves to, if any.
    early: Option<BlockId>,
    /// The registers' class.
    class: RegClass,
}

fn counted(c: Counted) -> Built {
    counted_with(c, false)
}

/// The scalar loop. With `data_exit`, the body loads a value and leaves to
/// a block of its own when it is nonzero (a `break` on data).
fn counted_with(c: Counted, data_exit: bool) -> Built {
    use AArch64Opcode::*;
    let mut f = MachFunction::new("counted".into(), Signature::new(vec![], vec![]));
    let pre = f.entry;
    let header = f.create_block();
    let body = f.create_block();
    let exit = f.create_block();
    if let Start::Const(start) = c.start {
        constant(&mut f, pre, c.reg(IV), start);
    }
    if let Bound::Pre(value) = c.bound {
        constant(&mut f, pre, c.reg(N), value);
    }
    push(&mut f, pre, B, vec![blk(header)]);
    f.add_edge(pre, header);
    match c.bound {
        Bound::Imm(value) => push(&mut f, header, CmpRI, vec![c.reg(IV), imm(value)]),
        Bound::Header(value) => {
            constant(&mut f, header, c.reg(N), value);
            push(&mut f, header, CmpRR, vec![c.reg(IV), c.reg(N)]);
        }
        Bound::Input | Bound::Pre(_) => push(&mut f, header, CmpRR, vec![c.reg(IV), c.reg(N)]),
    }
    push(&mut f, header, BCond, vec![imm(c.cond), blk(body)]);
    push(&mut f, header, B, vec![blk(exit)]);
    f.add_edge(header, body);
    f.add_edge(header, exit);
    let early = data_exit.then(|| {
        let early = f.create_block();
        push(&mut f, body, LdrRI, vec![x(LOADED), x(BASE), imm(0)]);
        push(&mut f, body, Cbnz, vec![x(LOADED), blk(early)]);
        f.add_edge(body, early);
        push(&mut f, early, MovR, vec![x(OUT), x(IV)]);
        push(&mut f, early, Ret, vec![]);
        early
    });
    push(&mut f, body, AddRI, vec![c.reg(IV), c.reg(IV), imm(c.step)]);
    push(&mut f, body, B, vec![blk(header)]);
    f.add_edge(body, header);
    push(&mut f, exit, MovR, vec![x(OUT), x(IV)]);
    push(&mut f, exit, Ret, vec![]);
    Built {
        func: f,
        pre,
        header,
        body,
        exit,
        early,
        class: if c.narrow {
            RegClass::Gpr32
        } else {
            RegClass::Gpr64
        },
    }
}

/// The loop's scope. The induction is always reproduced (the register clause
/// requires it of every rewrite that hands back to the header); `carried`
/// names the registers compared at the exit beyond it.
fn scope(b: &Built, carried: &[u32]) -> CoveredLoop<BlockId> {
    let mut carried: Vec<VReg> = carried.iter().map(|&id| VReg::new(id, b.class)).collect();
    if !carried.iter().any(|v| v.id == IV) {
        carried.push(VReg::new(IV, b.class));
    }
    let mut plan = ExitPlan::loop_test(b.header, b.exit);
    if let Some(early) = b.early {
        plan = plan.and_reproduces(LoopExit::Edge {
            from: b.body,
            to: early,
        });
    }
    LoopLocality::check_covered(
        &b.func,
        [b.header, b.body],
        b.header,
        b.pre,
        &plan,
        Handoff::HeaderOrExit,
        &carried,
    )
    .expect("the scalar loop passes the control and register clauses")
}

/// Find the first instruction of `block` with `opcode`.
fn find(f: &MachFunction, block: BlockId, opcode: AArch64Opcode) -> trust_cg_ir::InstId {
    *f.block(block)
        .insts
        .iter()
        .find(|&&id| f.inst(id).opcode == opcode)
        .unwrap_or_else(|| panic!("no {opcode:?} in {block:?}"))
}

/// The in-place rewrite `vectorize` makes: the step scaled to `step`, and
/// optionally the trip bound replaced.
fn in_place(b: &Built, step: i64, bound: Option<u64>) -> MachFunction {
    let mut f = b.func.clone();
    let add = find(&f, b.body, AArch64Opcode::AddRI);
    f.inst_mut(add).operands[2] = imm(step);
    if let Some(bound) = bound {
        if let Some(&cmp) = f
            .block(b.header)
            .insts
            .iter()
            .find(|&&id| f.inst(id).opcode == AArch64Opcode::CmpRI)
        {
            f.inst_mut(cmp).operands[1] = imm(bound as i64);
        } else {
            let movz = find(&f, b.header, AArch64Opcode::Movz);
            f.inst_mut(movz).operands[1] = imm(bound as i64);
        }
    }
    f
}

fn in_place_lanes(b: &Built, vf: u64) -> Lanes<BlockId> {
    Lanes {
        blocks: vec![(b.body, vf)],
        remainder: Remainder::None,
        copies: Vec::new(),
    }
}

fn verdict(
    b: &Built,
    after: &MachFunction,
    carried: &[u32],
    lanes: &Lanes<BlockId>,
) -> Result<IterationCoverage, CoverageEscape<BlockId>> {
    check_coverage(&b.func, after, &scope(b, carried), lanes)
}

/// The scalar and rewritten iteration counts of a mismatch.
fn counts(escape: CoverageEscape<BlockId>) -> (u128, u128) {
    match escape {
        CoverageEscape::Mismatch {
            scalar, rewritten, ..
        } => (scalar.iterations, rewritten.iterations),
        other => panic!("expected a mismatch, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// In place (`vectorize`)
// ---------------------------------------------------------------------------

#[test]
fn in_place_vectorize_running_every_lane_is_admitted() {
    // `for (i = 0; i < 64; i++)`, the step scaled to 4 under the untouched
    // bound: 16 trips of 4 lanes.
    let b = counted(Counted::new(Start::Const(0), Bound::Header(64)));
    let after = in_place(&b, 4, None);
    verdict(&b, &after, &[IV], &in_place_lanes(&b, 4)).expect("64 of 64 lanes");
}

#[test]
fn in_place_vectorize_dividing_its_own_bound_is_refused() {
    // 4b1fb93c7: the induction's step scaled by VF AND its own bound divided
    // by VF: 4 trips of 4 lanes, 16 of 64.
    for bound in [Bound::Imm(64), Bound::Header(64)] {
        let b = counted(Counted::new(Start::Const(0), bound));
        let after = in_place(&b, 4, Some(16));
        let escape = verdict(&b, &after, &[], &in_place_lanes(&b, 4)).unwrap_err();
        assert_eq!(counts(escape), (64, 16));
    }
}

#[test]
fn in_place_vectorize_with_remainder_lanes_is_refused() {
    // a0603f3bc: trip count 10, VF 4, the trip compare divided to 2 and the
    // remainder left to blocks nothing branches to: 8 of 10 lanes.
    let b = counted(Counted::new(Start::Const(0), Bound::Imm(10)));
    let mut after = in_place(&b, 1, Some(2));
    // A separate counter would keep the step; here the bound alone divides.
    let unreachable = after.create_block();
    push(&mut after, unreachable, AArch64Opcode::Ret, vec![]);
    let escape = verdict(&b, &after, &[], &in_place_lanes(&b, 4)).unwrap_err();
    assert_eq!(counts(escape), (10, 8));
}

#[test]
fn in_place_vectorize_past_an_odd_bound_is_refused() {
    // a0603f3bc: step 2 under the untouched `i < 65`: 33 trips, 66 lanes.
    let b = counted(Counted::new(Start::Const(0), Bound::Header(65)));
    let escape = verdict(&b, &in_place(&b, 2, None), &[], &in_place_lanes(&b, 2)).unwrap_err();
    assert_eq!(counts(escape), (65, 66));
}

#[test]
fn in_place_vectorize_from_a_nonzero_start_is_refused() {
    // a0603f3bc: `i = 1; i < 64`, step 2: 32 trips, 64 lanes for 63.
    let b = counted(Counted::new(Start::Const(1), Bound::Header(64)));
    let escape = verdict(&b, &in_place(&b, 2, None), &[], &in_place_lanes(&b, 2)).unwrap_err();
    assert_eq!(counts(escape), (63, 64));
}

#[test]
fn in_place_vectorize_under_an_inclusive_bound_is_refused() {
    // a0603f3bc: `i <= 64`, step 2: 33 trips, 66 lanes for 65.
    let mut c = Counted::new(Start::Const(0), Bound::Header(64));
    c.cond = LS;
    let b = counted(c);
    let escape = verdict(&b, &in_place(&b, 2, None), &[], &in_place_lanes(&b, 2)).unwrap_err();
    assert_eq!(counts(escape), (65, 66));
}

#[test]
fn in_place_vectorize_under_a_runtime_bound_is_refused() {
    // a0603f3bc: a bound known only at run time: some sampled `n` is not a
    // multiple of the step.
    let b = counted(Counted::new(Start::Const(0), Bound::Input));
    let escape = verdict(&b, &in_place(&b, 2, None), &[], &in_place_lanes(&b, 2)).unwrap_err();
    let CoverageEscape::Mismatch { inputs, .. } = &escape else {
        panic!("expected a mismatch, got {escape:?}");
    };
    assert_eq!(inputs.len(), 1, "the bound is the one input: {inputs:?}");
}

#[test]
fn in_place_vectorize_from_an_unknown_start_is_refused() {
    let b = counted(Counted::new(Start::Input, Bound::Header(64)));
    assert!(verdict(&b, &in_place(&b, 4, None), &[], &in_place_lanes(&b, 4)).is_err());
}

#[test]
fn an_exact_long_loop_is_decided_in_one_step() {
    // revertBits' trip count: 16777216 iterations, 8388608 trips of 2.
    let b = counted(Counted::new(Start::Const(0), Bound::Header(16_777_216)));
    verdict(&b, &in_place(&b, 2, None), &[IV], &in_place_lanes(&b, 2)).expect("every lane");
    // One past it: the last trip runs a lane past the bound.
    let b = counted(Counted::new(Start::Const(0), Bound::Header(16_777_217)));
    let escape = verdict(&b, &in_place(&b, 2, None), &[], &in_place_lanes(&b, 2)).unwrap_err();
    assert_eq!(counts(escape), (16_777_217, 16_777_218));
}

#[test]
fn a_loop_that_never_leaves_is_undecided() {
    // `i != 1` from 0 stepping by 2 never ends, for any width.
    let mut c = Counted::new(Start::Const(0), Bound::Imm(1));
    c.cond = NE;
    c.step = 2;
    let b = counted(c);
    let escape = verdict(&b, &b.func.clone(), &[], &in_place_lanes(&b, 1)).unwrap_err();
    assert!(
        matches!(escape, CoverageEscape::Undecided { .. }),
        "{escape:?}"
    );
}

#[test]
fn a_rewrite_that_can_cycle_without_counting_is_undecided() {
    use AArch64Opcode::*;
    // `for (i = 0; i < 64; i++)` vectorized in place with the step scaled to
    // 4, but the body's back edge goes to a new block that branches to
    // itself: a run that reaches it comes back in the state it had and never
    // leaves. Before the cycle rule the explorer merged that run into its own
    // past and dropped it without an outcome, so with no run left to compare
    // the rewrite was admitted.
    let b = counted(Counted::new(Start::Const(0), Bound::Header(64)));
    let mut spin_after = in_place(&b, 4, None);
    let spin = spin_after.create_block();
    push(&mut spin_after, spin, B, vec![blk(spin)]);
    spin_after.add_edge(spin, spin);
    let back = *spin_after.block(b.body).insts.last().unwrap();
    spin_after.inst_mut(back).operands = vec![blk(spin)];
    let escape = verdict(&b, &spin_after, &[], &in_place_lanes(&b, 4)).unwrap_err();
    assert!(
        matches!(escape, CoverageEscape::Undecided { .. }),
        "{escape:?}"
    );

    // The same cycle on one side of a data-dependent branch only: the other
    // side leaves as the scalar loop does, and the spinning side, dropped,
    // used to leave that outcome unopposed.
    let mut fork_after = in_place(&b, 4, None);
    let spin = fork_after.create_block();
    push(&mut fork_after, spin, B, vec![blk(spin)]);
    fork_after.add_edge(spin, spin);
    let back = fork_after.block_mut(b.body).insts.pop().unwrap();
    push(
        &mut fork_after,
        b.body,
        LdrRI,
        vec![x(LOADED), x(BASE), imm(0)],
    );
    push(&mut fork_after, b.body, Cbnz, vec![x(LOADED), blk(spin)]);
    fork_after.append_inst(b.body, back);
    fork_after.add_edge(b.body, spin);
    let escape = verdict(&b, &fork_after, &[], &in_place_lanes(&b, 4)).unwrap_err();
    assert!(
        matches!(escape, CoverageEscape::Undecided { .. }),
        "{escape:?}"
    );

    // The control: the same rewrite without the cycle is admitted.
    verdict(&b, &in_place(&b, 4, None), &[], &in_place_lanes(&b, 4)).expect("64 of 64 lanes");
}

// ---------------------------------------------------------------------------
// A vector loop in front of the scalar loop (`neon_fill` and its siblings)
// ---------------------------------------------------------------------------

/// How the front loop is built.
#[derive(Clone, Copy)]
struct Front {
    width: i64,
    /// Subtracted from `n` for the vector loop's bound (`width - 1` is exact).
    slack: i64,
    /// Skip the vector loop when `n < width`.
    precheck: bool,
    /// Where the vector loop's exit goes: the scalar header, or the scalar
    /// loop's exit.
    to_header: bool,
    /// What the rewrite claims each vector trip runs.
    claimed: u64,
    /// Compare the vector bound signed.
    signed: bool,
}

const FRONT: Front = Front {
    width: 4,
    slack: 3,
    precheck: true,
    to_header: true,
    claimed: 4,
    signed: false,
};

/// The blocks [`front_blocks`] adds.
struct FrontBlocks {
    pv: BlockId,
    vb: BlockId,
    vx: BlockId,
}

/// `pv`: `mb = n - slack; if n < width goto header`; `vh`: `if iv < mb goto
/// vb else vx`; `vb`: the trip's work; `vl` (counted, the trip done): `iv +=
/// width`; `vx`: to the header.
fn front(b: &Built, f: Front) -> (MachFunction, Lanes<BlockId>) {
    let (after, lanes, _) = front_blocks(b, f);
    (after, lanes)
}

/// [`front`], and the blocks it added.
fn front_blocks(b: &Built, f: Front) -> (MachFunction, Lanes<BlockId>, FrontBlocks) {
    use AArch64Opcode::*;
    let mut after = b.func.clone();
    let (pv, vh, vb, vl, vx) = (
        after.create_block(),
        after.create_block(),
        after.create_block(),
        after.create_block(),
        after.create_block(),
    );
    let jump = find(&after, b.pre, B);
    after.inst_mut(jump).operands[0] = blk(pv);
    push(&mut after, pv, SubRI, vec![x(MB), x(N), imm(f.slack)]);
    if f.precheck {
        push(&mut after, pv, CmpRI, vec![x(N), imm(f.width)]);
        push(&mut after, pv, BCond, vec![imm(LO), blk(b.header)]);
    }
    push(&mut after, pv, B, vec![blk(vh)]);
    push(&mut after, vh, CmpRR, vec![x(IV), x(MB)]);
    push(
        &mut after,
        vh,
        BCond,
        vec![imm(if f.signed { LT } else { LO }), blk(vb)],
    );
    push(&mut after, vh, B, vec![blk(vx)]);
    if let Some(early) = b.early {
        // The vector trip evaluates the data exit for its lanes and gives
        // control back to the scalar loop at the trip's start when it fires.
        push(&mut after, vb, LdrRI, vec![x(LOADED_V), x(BASE), imm(0)]);
        push(&mut after, vb, Cbnz, vec![x(LOADED_V), blk(b.header)]);
        let _ = early;
    }
    push(&mut after, vb, B, vec![blk(vl)]);
    push(&mut after, vl, AddRI, vec![x(IV), x(IV), imm(f.width)]);
    push(&mut after, vl, B, vec![blk(vh)]);
    push(
        &mut after,
        vx,
        B,
        vec![blk(if f.to_header { b.header } else { b.exit })],
    );
    let lanes = Lanes {
        blocks: vec![(vl, f.claimed)],
        remainder: Remainder::ScalarLoop,
        copies: Vec::new(),
    };
    (after, lanes, FrontBlocks { pv, vb, vx })
}

#[test]
fn a_front_loop_over_every_sampled_bound_is_admitted() {
    // neon_fill's shape: `mb = n - 3`, skipped for `n < 4`, the scalar loop
    // the remainder. Every sampled `n`, from 0 to 2^64 - 1.
    let b = counted(Counted::new(Start::Const(0), Bound::Input));
    let (after, lanes) = front(&b, FRONT);
    verdict(&b, &after, &[IV], &lanes).expect("vector prefix + scalar remainder");
}

#[test]
fn a_front_loop_past_its_bound_is_refused() {
    // `mb = n`: the last vector trip runs up to 3 lanes past `n`.
    let b = counted(Counted::new(Start::Const(0), Bound::Input));
    let (after, lanes) = front(&b, Front { slack: 0, ..FRONT });
    let escape = verdict(&b, &after, &[IV], &lanes).unwrap_err();
    let (scalar, rewritten) = counts(escape);
    assert!(rewritten > scalar, "{rewritten} lanes for {scalar}");
}

#[test]
fn a_front_loop_without_its_small_bound_precheck_is_refused() {
    // `n < 4` makes `n - 3` wrap: the vector loop runs far past `n`.
    let b = counted(Counted::new(Start::Const(0), Bound::Input));
    let (after, lanes) = front(
        &b,
        Front {
            precheck: false,
            ..FRONT
        },
    );
    assert!(verdict(&b, &after, &[IV], &lanes).is_err());
}

#[test]
fn a_front_loop_comparing_signed_is_refused() {
    // An unsigned `n` at or above 2^63 reads negative.
    let b = counted(Counted::new(Start::Const(0), Bound::Input));
    let (after, lanes) = front(
        &b,
        Front {
            signed: true,
            ..FRONT
        },
    );
    assert!(verdict(&b, &after, &[IV], &lanes).is_err());
}

#[test]
fn a_front_loop_that_skips_its_remainder_is_refused() {
    // The vector exit goes to the loop's exit: `n % 4` lanes never run.
    let b = counted(Counted::new(Start::Const(0), Bound::Input));
    let (after, lanes) = front(
        &b,
        Front {
            to_header: false,
            ..FRONT
        },
    );
    let (scalar, rewritten) = counts(verdict(&b, &after, &[IV], &lanes).unwrap_err());
    assert!(rewritten < scalar, "{rewritten} lanes for {scalar}");
}

#[test]
fn a_front_loop_claiming_more_lanes_than_it_advances_is_refused() {
    let b = counted(Counted::new(Start::Const(0), Bound::Input));
    let (after, lanes) = front(
        &b,
        Front {
            claimed: 8,
            ..FRONT
        },
    );
    assert!(verdict(&b, &after, &[IV], &lanes).is_err());
}

#[test]
fn a_front_loop_from_an_unknown_start_is_checked_over_both_inputs() {
    // `iv` live in: start and bound both sampled, 43 x 43 runs.
    let b = counted(Counted::new(Start::Input, Bound::Input));
    let (after, lanes) = front(&b, FRONT);
    verdict(&b, &after, &[IV], &lanes).expect("any start, any bound");
}

#[test]
fn a_front_loop_whose_remainder_was_edited_is_refused() {
    // The hand-off is in sync, but the rewrite also changed the scalar
    // loop's step: the remainder is not the scalar loop any more. Running an
    // edited remainder by the scalar loop's counting rule is not safe (see
    // `an_edited_scalar_remainder_is_refused`), so it is refused outright.
    let b = counted(Counted::new(Start::Const(0), Bound::Input));
    let (mut after, lanes) = front(&b, FRONT);
    let add = find(&after, b.body, AArch64Opcode::AddRI);
    after.inst_mut(add).operands[2] = imm(2);
    assert!(undecided_because(
        &verdict(&b, &after, &[IV], &lanes),
        "is not the scalar loop unchanged"
    ));
}

#[test]
fn a_front_loop_reproducing_a_data_exit_is_admitted() {
    // The body leaves on a loaded value; each vector trip tests it and hands
    // control back to the scalar loop at the trip's start. Every outcome of
    // the unknown test covers. A trip that can give control back forks the
    // run, so the vector loop is stepped, not accelerated: a constant trip
    // count keeps it within the budget.
    let b = counted_with(Counted::new(Start::Const(0), Bound::Pre(103)), true);
    let (after, lanes) = front(&b, FRONT);
    verdict(&b, &after, &[IV], &lanes).expect("found or not, every lane once");
    // Over a run-time bound some sampled `n` needs 2^62 trips: undecided,
    // so refused.
    let b = counted_with(Counted::new(Start::Const(0), Bound::Input), true);
    let (after, lanes) = front(&b, FRONT);
    assert!(matches!(
        verdict(&b, &after, &[IV], &lanes),
        Err(CoverageEscape::Undecided { .. })
    ));
}

// ---------------------------------------------------------------------------
// Full unroll (`loop_unroll`)
// ---------------------------------------------------------------------------

/// The loop unrolled into `copies` straight-line iterations, each counted
/// once, the last one falling into the exit.
fn unrolled(b: &Built, copies: u64, trip: u64) -> (MachFunction, Lanes<BlockId>) {
    use AArch64Opcode::*;
    let mut after = b.func.clone();
    let blocks: Vec<BlockId> = (0..copies).map(|_| after.create_block()).collect();
    let jump = find(&after, b.pre, B);
    after.inst_mut(jump).operands[0] = blk(blocks.first().copied().unwrap_or(b.exit));
    for (k, &block) in blocks.iter().enumerate() {
        // The IV of each copy is its constant.
        constant(&mut after, block, x(IV), (k as u64 + 1).min(trip));
        let next = blocks.get(k + 1).copied().unwrap_or(b.exit);
        push(&mut after, block, B, vec![blk(next)]);
    }
    let lanes = Lanes {
        blocks: blocks.iter().map(|&block| (block, 1)).collect(),
        remainder: Remainder::None,
        copies: Vec::new(),
    };
    (after, lanes)
}

#[test]
fn a_full_unroll_runs_exactly_the_trip_count() {
    let b = counted(Counted::new(Start::Const(0), Bound::Imm(8)));
    let (after, lanes) = unrolled(&b, 8, 8);
    verdict(&b, &after, &[IV], &lanes).expect("8 copies of 8 iterations");
    let (after, lanes) = unrolled(&b, 7, 8);
    assert_eq!(
        counts(verdict(&b, &after, &[], &lanes).unwrap_err()),
        (8, 7)
    );
    let (after, lanes) = unrolled(&b, 9, 8);
    assert_eq!(
        counts(verdict(&b, &after, &[], &lanes).unwrap_err()),
        (8, 9)
    );
}

// ---------------------------------------------------------------------------
// Exits, hand-offs and stops the scalar loop does not have
//
// Each rewrite below is wrong, and was admitted before the clause checked the
// shape (review of 95660b90e: an exit or conditional trap only the new code
// has, a hand-off into the scalar body, an edited remainder, a trap rewritten
// into a return; and `MOVWrr` read as a 64-bit copy). A MachIR interpreter run
// of each, by the reviewers, showed the behaviour that differs.
// ---------------------------------------------------------------------------

const T: u32 = 50;
const M: u32 = 52;
const HS: i64 = 2;

/// Instructions to insert, as `(opcode, operands)`.
type Insts = Vec<(AArch64Opcode, Vec<MachOperand>)>;

/// Insert `insts` at the top of `block`, with a CFG edge to every block they
/// name.
fn prepend(f: &mut MachFunction, block: BlockId, insts: Insts) {
    for (k, (opcode, operands)) in insts.into_iter().enumerate() {
        for operand in &operands {
            if let MachOperand::Block(target) = operand {
                f.add_edge(block, *target);
            }
        }
        let id = f.push_inst(MachInst::new(opcode, operands));
        f.block_mut(block).insts.insert(k, id);
    }
}

/// The front loop with `extra` at the top of its vector trip.
fn front_with_trip(b: &Built, extra: Insts) -> (MachFunction, Lanes<BlockId>) {
    let (mut after, lanes, blocks) = front_blocks(b, FRONT);
    prepend(&mut after, blocks.vb, extra);
    (after, lanes)
}

/// Whether the clause refused undecided, for a reason that names `why`.
fn undecided_because(
    verdict: &Result<IterationCoverage, CoverageEscape<BlockId>>,
    why: &str,
) -> bool {
    matches!(verdict, Err(CoverageEscape::Undecided { why: reason }) if reason.contains(why))
}

#[test]
fn an_exit_only_the_new_code_has_is_refused() {
    use AArch64Opcode::*;
    // The vector trip leaves for the loop's exit on a value the trip model
    // does not compute: `rbit` (unmodeled) of the induction, nonzero from the
    // second trip on, or a loaded value. The scalar loop has no such exit, so
    // the control clause never saw it; taking it as not taken admitted a
    // rewrite that returns 4 (or 0) where the scalar loop returns `n`.
    for bound in [Bound::Pre(64), Bound::Input] {
        let b = counted(Counted::new(Start::Const(0), bound));
        let (control, lanes) = front_with_trip(&b, vec![]);
        verdict(&b, &control, &[IV], &lanes).expect("the same front loop without the exit");
        for condition in [
            (Rbit, vec![x(T), x(IV)]),
            (LdrRI, vec![x(T), x(BASE), imm(0)]),
        ] {
            let opcode = condition.0;
            let (after, lanes) =
                front_with_trip(&b, vec![condition, (Cbnz, vec![x(T), blk(b.exit)])]);
            let got = verdict(&b, &after, &[IV], &lanes);
            assert!(
                undecided_because(&got, "on undecided data"),
                "{opcode:?}: {got:?}"
            );
        }
    }
    // In place: the rewritten body itself gains the exit.
    let b = counted(Counted::new(Start::Const(0), Bound::Imm(64)));
    let mut after = in_place(&b, 4, None);
    prepend(
        &mut after,
        b.body,
        vec![(Rbit, vec![x(T), x(IV)]), (Cbnz, vec![x(T), blk(b.exit)])],
    );
    let got = verdict(&b, &after, &[IV], &in_place_lanes(&b, 4));
    assert!(undecided_because(&got, "on undecided data"), "{got:?}");
}

#[test]
fn a_data_exit_to_another_block_than_the_scalar_loops_is_refused() {
    use AArch64Opcode::*;
    // The scalar loop leaves for `early` on a loaded value (the exit its plan
    // reproduces); the new code's loaded exit goes to the loop's exit
    // instead, which no exit of the scalar loop on undecided data reaches.
    let b = counted_with(Counted::new(Start::Const(0), Bound::Pre(103)), true);
    let (after, lanes) = front_with_trip(
        &b,
        vec![
            (LdrRI, vec![x(T), x(BASE), imm(0)]),
            (Cbnz, vec![x(T), blk(b.exit)]),
        ],
    );
    let got = verdict(&b, &after, &[IV], &lanes);
    assert!(undecided_because(&got, "on undecided data"), "{got:?}");
}

/// `t = 2^64 - 5` at the top of a block: `iv + t` carries from `iv = 5` on.
fn near_max(reg: u32) -> Insts {
    use AArch64Opcode::*;
    vec![
        (Movz, vec![x(reg), imm(0xfffb)]),
        (Movk, vec![x(reg), imm(0xffff), imm(16)]),
        (Movk, vec![x(reg), imm(0xffff), imm(32)]),
        (Movk, vec![x(reg), imm(0xffff), imm(48)]),
    ]
}

/// What a guard at the top of the front loop's vector trip must give.
enum Guarded {
    /// The rewritten run traps after this many lanes, where the scalar loop
    /// leaves after 64.
    TrapsAfter(u128),
    /// The clause refuses undecided, for a reason that names this.
    Refused(&'static str),
}

/// Each guard `(name, expected, instructions)` at the top of the vector trip
/// of a front loop over `b`: the rows whose verdict is not the expected one.
fn misjudged_guards(b: &Built, guards: Vec<(&str, Guarded, Insts)>) -> Vec<String> {
    guards
        .into_iter()
        .filter_map(|(name, expected, guard)| {
            let (after, lanes) = front_with_trip(b, guard);
            let got = verdict(b, &after, &[IV], &lanes);
            let right = match (expected, &got) {
                (
                    Guarded::TrapsAfter(lanes),
                    Err(CoverageEscape::Mismatch {
                        scalar, rewritten, ..
                    }),
                ) => {
                    rewritten.end == RunEnd::Stops(StopKind::Trap)
                        && scalar.end != rewritten.end
                        && rewritten.iterations == lanes
                }
                (Guarded::Refused(why), got) => undecided_because(got, why),
                _ => false,
            };
            (!right).then(|| format!("{name}: {got:?}"))
        })
        .collect()
}

#[test]
fn a_conditional_trap_only_the_new_code_has_is_refused() {
    use AArch64Opcode::*;
    use Guarded::*;
    use trust_cg_ir::{OverflowOp, pack_overflow_tag};
    // Over `i < 64` the vector trips run at iv = 0, 4, 8, ...; each guard
    // below traps on one of them on hardware, and the scalar loop has no
    // trap. Every falls-through trap pseudo was modeled as flags clobbered
    // only, never taken. A guard whose test the model computes now traps in
    // the run (after `iv` lanes, where the scalar loop leaves after 64), as
    // does a carrier the expansion degrades to a bare trap; one whose test it
    // does not compute is refused undecided: on a value the run does not
    // know, as an exit only the new code has, and on values it knows, as a
    // trap whose outcome those values fix.
    let b = counted(Counted::new(Start::Const(0), Bound::Pre(64)));
    let iv_minus_4 = (SubRI, vec![x(T), x(IV), imm(4)]);
    let tag = |op| imm(pack_overflow_tag(op, 64));
    let mut carry = near_max(T);
    carry.push((
        TrapOverflowExact,
        vec![x(IV), x(T), tag(OverflowOp::UnsignedAdd)],
    ));
    let guards: Vec<(&str, Guarded, Insts)> = vec![
        (
            "div-zero on iv - 4",
            TrapsAfter(4),
            vec![iv_minus_4.clone(), (TrapDivZeroIfZero, vec![x(T)])],
        ),
        (
            "null on iv - 4",
            TrapsAfter(4),
            vec![iv_minus_4, (TrapNullIfZero, vec![x(T)])],
        ),
        (
            "shift range: iv >= 8",
            TrapsAfter(8),
            vec![(TrapShiftRangeIfOOB, vec![x(IV), imm(8)])],
        ),
        ("unsigned add overflow: iv + 2^64 - 5", TrapsAfter(8), carry),
        (
            "a bounds carrier missing its bound (expanded to a bare trap)",
            TrapsAfter(0),
            vec![(TrapBoundsCheckExact, vec![x(BASE), x(IV)])],
        ),
        (
            "null on rbit(iv) (unmodeled)",
            Refused("on undecided data"),
            vec![(Rbit, vec![x(T), x(IV)]), (TrapNullIfZero, vec![x(T)])],
        ),
        (
            "unsigned mul overflow (test unmodeled, operands known)",
            Refused("on values it knows"),
            vec![(
                TrapOverflowExact,
                vec![x(IV), x(IV), tag(OverflowOp::UnsignedMul)],
            )],
        ),
    ];
    let wrong = misjudged_guards(&b, guards);
    assert!(wrong.is_empty(), "{wrong:#?}");
}

#[test]
fn each_overflow_carrier_traps_on_its_own_lane_at_32_and_64_bits() {
    use AArch64Opcode::*;
    use Guarded::*;
    use trust_cg_ir::{OverflowOp, pack_overflow_tag};
    // `TrapOverflowExact a, b, tag` expands to `ADDS/SUBS ZR, a, b` at the
    // tag's width and traps on V for a signed add or subtract, on C (carry)
    // for an unsigned add, and on !C (borrow) for an unsigned subtract. Each
    // row below traps from iv = 5 on (or above 5), so the vector trips at iv
    // = 0, 4, 8 trap after 8 lanes; the wrong flag, polarity or width traps
    // after 0 lanes or never. A 32-bit row's constant is chosen so that its
    // 64-bit reading would not trap.
    let b = counted(Counted::new(Start::Const(0), Bound::Pre(64)));
    let row = |op: OverflowOp, width: u16, value: u64, iv_first: bool| -> Insts {
        let mut insts = vec![(Movz, vec![x(T), imm((value & 0xffff) as i64)])];
        for shift in [16u32, 32, 48] {
            let part = (value >> shift) & 0xffff;
            if part != 0 {
                insts.push((Movk, vec![x(T), imm(part as i64), imm(i64::from(shift))]));
            }
        }
        let (a, c) = if iv_first {
            (x(IV), x(T))
        } else {
            (x(T), x(IV))
        };
        insts.push((
            TrapOverflowExact,
            vec![a, c, imm(pack_overflow_tag(op, width))],
        ));
        insts
    };
    let guards: Vec<(&str, Guarded, Insts)> = vec![
        (
            "signed add @64: iv + (2^63 - 5)",
            TrapsAfter(8),
            row(OverflowOp::SignedAdd, 64, (1 << 63) - 5, true),
        ),
        (
            "signed add @32: iv + (2^31 - 5)",
            TrapsAfter(8),
            row(OverflowOp::SignedAdd, 32, (1 << 31) - 5, true),
        ),
        (
            "signed sub @64: iv - (MIN + 5)",
            TrapsAfter(8),
            row(OverflowOp::SignedSub, 64, (1 << 63) + 5, true),
        ),
        (
            "signed sub @32: iv - (MIN + 5)",
            TrapsAfter(8),
            row(OverflowOp::SignedSub, 32, (1 << 31) + 5, true),
        ),
        (
            "unsigned add @64: iv + 2^64 - 5",
            TrapsAfter(8),
            row(OverflowOp::UnsignedAdd, 64, u64::MAX - 4, true),
        ),
        (
            "unsigned add @32: iv + 2^32 - 5",
            TrapsAfter(8),
            row(OverflowOp::UnsignedAdd, 32, (1 << 32) - 5, true),
        ),
        (
            "unsigned sub @64: 5 - iv borrows",
            TrapsAfter(8),
            row(OverflowOp::UnsignedSub, 64, 5, false),
        ),
        (
            "unsigned sub @32: low half 5 - iv borrows",
            TrapsAfter(8),
            row(OverflowOp::UnsignedSub, 32, (1 << 32) + 5, false),
        ),
    ];
    let wrong = misjudged_guards(&b, guards);
    assert!(wrong.is_empty(), "{wrong:#?}");
}

#[test]
fn a_hand_off_into_the_scalar_body_is_refused() {
    use AArch64Opcode::*;
    // The vector exit re-runs the last vector lane in the scalar body
    // (`iv -= 1; b body`): 65 iterations for 64. Only header entries counted
    // the remainder, and the unchanged loop's first header entry was in sync
    // with the scalar run, so the repeat went uncounted.
    for bound in [Bound::Pre(64), Bound::Pre(66), Bound::Input] {
        let b = counted(Counted::new(Start::Const(0), bound));
        let (mut after, lanes, blocks) = front_blocks(&b, FRONT);
        after.block_mut(blocks.vx).insts.clear();
        push(&mut after, blocks.vx, SubRI, vec![x(IV), x(IV), imm(1)]);
        push(&mut after, blocks.vx, B, vec![blk(b.body)]);
        after.add_edge(blocks.vx, b.body);
        let got = verdict(&b, &after, &[IV], &lanes);
        assert!(
            undecided_because(&got, "other than at its header"),
            "{got:?}"
        );
    }
    // The small-bound precheck enters the body one lane early instead of
    // the header: `a[-1]` for `n < 4`.
    let b = counted(Counted::new(Start::Const(0), Bound::Input));
    let (mut after, lanes, blocks) = front_blocks(&b, FRONT);
    let ps = after.create_block();
    push(&mut after, ps, SubRI, vec![x(IV), x(IV), imm(1)]);
    push(&mut after, ps, B, vec![blk(b.body)]);
    after.add_edge(ps, b.body);
    let precheck = find(&after, blocks.pv, BCond);
    after.inst_mut(precheck).operands[1] = blk(ps);
    after.add_edge(blocks.pv, ps);
    let got = verdict(&b, &after, &[IV], &lanes);
    assert!(
        undecided_because(&got, "other than at its header"),
        "{got:?}"
    );
}

#[test]
fn an_edited_scalar_remainder_is_refused() {
    use AArch64Opcode::*;
    let lanes = Lanes {
        blocks: vec![],
        remainder: Remainder::ScalarLoop,
        copies: Vec::new(),
    };
    // Start at 1 (iteration 0 never runs) and leave the header through a
    // trampoline instead of the named test edge, so the final, iteration-free
    // header entry counted as an iteration: 63 body runs admitted for 64.
    let b = counted(Counted::new(Start::Const(0), Bound::Imm(64)));
    let mut after = b.func.clone();
    let start = find(&after, b.pre, Movz);
    after.inst_mut(start).operands[1] = imm(1);
    let y = after.create_block();
    push(&mut after, y, B, vec![blk(b.exit)]);
    after.add_edge(y, b.exit);
    let leave = *after.block(b.header).insts.last().unwrap();
    after.inst_mut(leave).operands[0] = blk(y);
    after.add_edge(b.header, y);
    let got = verdict(&b, &after, &[IV], &lanes);
    assert!(
        undecided_because(&got, "is not the scalar loop unchanged"),
        "{got:?}"
    );
    // The header tests `i < 63` and the trampoline runs `iv += 1` without
    // the body: iteration 63's work is skipped.
    let mut after = b.func.clone();
    let test = find(&after, b.header, CmpRI);
    after.inst_mut(test).operands[1] = imm(63);
    let y = after.create_block();
    push(&mut after, y, AddRI, vec![x(IV), x(IV), imm(1)]);
    push(&mut after, y, B, vec![blk(b.exit)]);
    after.add_edge(y, b.exit);
    let leave = *after.block(b.header).insts.last().unwrap();
    after.inst_mut(leave).operands[0] = blk(y);
    after.add_edge(b.header, y);
    let got = verdict(&b, &after, &[IV], &lanes);
    assert!(
        undecided_because(&got, "is not the scalar loop unchanged"),
        "{got:?}"
    );
}

/// `for (i = 0; i < 64; i++) { a[i] with bound check against bound }`, and
/// its scope: the trap reproduced.
fn bounds_checked(bound: MachOperand) -> (Built, CoveredLoop<BlockId>) {
    let mut b = counted(Counted::new(Start::Const(0), Bound::Imm(64)));
    prepend(
        &mut b.func,
        b.body,
        vec![(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![x(BASE), x(IV), bound],
        )],
    );
    let plan = ExitPlan::loop_test(b.header, b.exit).and_reproduces(LoopExit::Stop {
        block: b.body,
        index: 0,
    });
    let scope = LoopLocality::check_covered(
        &b.func,
        [b.header, b.body],
        b.header,
        b.pre,
        &plan,
        Handoff::HeaderOrExit,
        &[VReg::new(IV, RegClass::Gpr64)],
    )
    .expect("the scalar loop passes the control and register clauses");
    (b, scope)
}

#[test]
fn a_trap_rewritten_into_a_return_is_refused() {
    use AArch64Opcode::*;
    // The scalar loop's bounds trap fires at `i = bound`; the rewrite spells
    // it `cmp; b.hs r` with `r: ret`, so it returns where the scalar loop
    // traps. Both used to be one outcome, "stops".
    for bound in [imm(5), x(M)] {
        let (b, scope) = bounds_checked(bound.clone());
        let lanes = Lanes {
            blocks: vec![(b.body, 1)],
            remainder: Remainder::None,
            copies: Vec::new(),
        };
        check_coverage(&b.func, &b.func.clone(), &scope, &lanes).expect("the identity rewrite");
        let mut after = b.func.clone();
        let r = after.create_block();
        push(&mut after, r, MovR, vec![x(OUT), x(IV)]);
        push(&mut after, r, Ret, vec![]);
        after.block_mut(b.body).insts.remove(0);
        let compare = if matches!(bound, MachOperand::Imm(_)) {
            CmpRI
        } else {
            CmpRR
        };
        let compare = (compare, vec![x(IV), bound]);
        prepend(
            &mut after,
            b.body,
            vec![compare, (BCond, vec![imm(HS), blk(r)])],
        );
        match check_coverage(&b.func, &after, &scope, &lanes) {
            Err(CoverageEscape::Mismatch {
                scalar, rewritten, ..
            }) => assert_ne!(scalar.end, rewritten.end),
            other => panic!("expected the trap and the return to differ, got {other:?}"),
        }
    }
}

#[test]
fn a_movwrr_bound_reads_32_bits() {
    use AArch64Opcode::*;
    // `n = MOVWrr wide` with `wide = 0x8000_0000_0000_0005`: the encoder
    // gives MOVWrr sf = 0, so `n` is 5 on hardware, odd, and a step-2
    // in-place rewrite of the signed `i < n` loop runs lane 5 as well. Read as
    // a 64-bit copy, `n` was negative and both loops ran no iteration.
    const WIDE: u32 = 51;
    let built = |opcode: AArch64Opcode| {
        let mut c = Counted::new(Start::Const(0), Bound::Input);
        c.cond = LT;
        let mut b = counted(c);
        let jump = b.func.block_mut(b.pre).insts.pop().unwrap();
        constant(&mut b.func, b.pre, x(WIDE), 0x8000_0000_0000_0005);
        push(&mut b.func, b.pre, opcode, vec![x(N), x(WIDE)]);
        b.func.append_inst(b.pre, jump);
        b
    };
    let b = built(MOVWrr);
    let escape = verdict(&b, &in_place(&b, 2, None), &[], &in_place_lanes(&b, 2)).unwrap_err();
    assert_eq!(counts(escape), (5, 6));
    // `MOVXrr` copies all 64 bits: `n` is negative, no iteration, admitted.
    let b = built(MOVXrr);
    verdict(&b, &in_place(&b, 2, None), &[], &in_place_lanes(&b, 2)).expect("no iteration");
}

// ---------------------------------------------------------------------------
// What a data exit of the new code stands for, and what a kept loop and the
// preheader must keep
//
// Review of `f2788e9ab` (the rows above) found each of these admitted: a
// data exit matched by its target block alone, any undecided trap matched by
// any trap of the scalar loop, a kept loop compared by its effects, and a
// preheader whose unmodeled result was run on the scalar preheader's value.
// A MachIR interpreter run of each, by the reviewers, showed the behaviour
// that differs.
// ---------------------------------------------------------------------------

const D: u32 = 55;
const K: u32 = 56;

#[test]
fn a_data_exit_of_the_new_code_stands_only_for_its_own_instruction() {
    use AArch64Opcode::*;
    // The scalar loop leaves for `early` on a loaded value. A new exit to
    // `early` on `rbit(iv)` (an unmodeled operation, not data: nonzero from
    // iv = 1 on) is not that exit. Matched by its target block alone it was
    // admitted, and the rewrite returned 4 where the scalar loop returns 64
    // in place, or 103 in front of the kept loop.
    let rbit_exit =
        |early| -> Insts { vec![(Rbit, vec![x(T), x(IV)]), (Cbnz, vec![x(T), blk(early)])] };
    let b = counted_with(Counted::new(Start::Const(0), Bound::Imm(64)), true);
    let early = b.early.expect("a data exit");
    verdict(&b, &in_place(&b, 4, None), &[IV], &in_place_lanes(&b, 4))
        .expect("the scalar loop's own exit, in the body rewritten in place");
    let mut after = in_place(&b, 4, None);
    prepend(&mut after, b.body, rbit_exit(early));
    let got = verdict(&b, &after, &[IV], &in_place_lanes(&b, 4));
    assert!(
        undecided_because(&got, "on undecided data"),
        "in place: {got:?}"
    );
    // A second loaded exit to `early`: the same target, another instruction.
    let mut after = in_place(&b, 4, None);
    prepend(
        &mut after,
        b.body,
        vec![
            (LdrRI, vec![x(T), x(BASE), imm(8)]),
            (Cbnz, vec![x(T), blk(early)]),
        ],
    );
    let got = verdict(&b, &after, &[IV], &in_place_lanes(&b, 4));
    assert!(
        undecided_because(&got, "on undecided data"),
        "second load: {got:?}"
    );

    let b = counted_with(Counted::new(Start::Const(0), Bound::Pre(103)), true);
    let early = b.early.expect("a data exit");
    let (after, lanes) = front_with_trip(&b, rbit_exit(early));
    let got = verdict(&b, &after, &[IV], &lanes);
    assert!(
        undecided_because(&got, "on undecided data"),
        "front loop: {got:?}"
    );
}

/// `for (i = 0; i < 64; i++)` with `guard` at the top of its body, and its
/// scope: the trap at `trap` in the body reproduced.
fn guarded(guard: Insts, trap: usize) -> (Built, CoveredLoop<BlockId>) {
    let mut b = counted(Counted::new(Start::Const(0), Bound::Imm(64)));
    prepend(&mut b.func, b.body, guard);
    let plan = ExitPlan::loop_test(b.header, b.exit).and_reproduces(LoopExit::Stop {
        block: b.body,
        index: trap,
    });
    let scope = LoopLocality::check_covered(
        &b.func,
        [b.header, b.body],
        b.header,
        b.pre,
        &plan,
        Handoff::HeaderOrExit,
        &[VReg::new(IV, RegClass::Gpr64)],
    )
    .expect("the scalar loop passes the control and register clauses");
    (b, scope)
}

#[test]
fn an_undecided_trap_of_the_new_code_stands_only_for_its_own_instruction() {
    use AArch64Opcode::*;
    use trust_cg_ir::{OverflowOp, pack_overflow_tag};
    let umul = || imm(pack_overflow_tag(OverflowOp::UnsignedMul, 64));
    // `k = 2^62`: `iv * k` overflows from iv = 4 on.
    let mul_trap: Insts = vec![
        (Movz, vec![x(K), imm(0)]),
        (Movk, vec![x(K), imm(0x4000), imm(48)]),
        (TrapOverflowExact, vec![x(IV), x(K), umul()]),
    ];
    let rewritten = |b: &Built, extra: Insts| {
        let mut after = in_place(b, 4, None);
        prepend(&mut after, b.body, extra);
        after
    };
    let lanes = |b: &Built| in_place_lanes(b, 4);

    // The scalar loop's trap divides by a loaded value. Any undecided trap
    // of the new code used to stand for it: a null check on `rbit(iv)`
    // (traps at iv = 0) and the multiply-overflow carrier above (at iv = 4)
    // were admitted where the scalar loop returns 64. The carrier's operands
    // are in the trip slice, so the run knows `iv` and `k` and refuses it on
    // them; on `rbit(iv)` it is undecided, and no instruction of the scalar
    // loop.
    let (b, scope) = guarded(
        vec![
            (LdrRI, vec![x(D), x(BASE), imm(8)]),
            (TrapDivZeroIfZero, vec![x(D)]),
        ],
        1,
    );
    check_coverage(&b.func, &in_place(&b, 4, None), &scope, &lanes(&b))
        .expect("the scalar loop's own trap, in the body rewritten in place");
    for (name, extra, why) in [
        (
            "null on rbit(iv)",
            vec![(Rbit, vec![x(T), x(IV)]), (TrapNullIfZero, vec![x(T)])],
            "on undecided data",
        ),
        (
            "iv * 2^62 overflows",
            mul_trap.clone(),
            "on values it knows",
        ),
        (
            "rbit(iv) squared overflows",
            vec![
                (Rbit, vec![x(T), x(IV)]),
                (TrapOverflowExact, vec![x(T), x(T), umul()]),
            ],
            "on undecided data",
        ),
    ] {
        let got = check_coverage(&b.func, &rewritten(&b, extra), &scope, &lanes(&b));
        assert!(undecided_because(&got, why), "{name}: {got:?}");
    }

    // The scalar loop's trap is a multiply-overflow carrier on `iv * iv`,
    // which never fires below 64 but whose test the model does not compute.
    // It stood for the new code's `iv * 2^62` carrier, with no data at all.
    // On values the run knows (the induction, and the constant `k`), neither
    // carrier is an exit on undecided data: each is refused on them, the
    // rewritten loop's own copy of the scalar one, run on every fourth value
    // only, as well.
    let (b, scope) = guarded(vec![(TrapOverflowExact, vec![x(IV), x(IV), umul()])], 0);
    for (name, extra, why) in [
        ("iv * 2^62 overflows", mul_trap, "on values it knows"),
        ("unchanged", vec![], "on values it knows"),
    ] {
        let got = check_coverage(&b.func, &rewritten(&b, extra), &scope, &lanes(&b));
        assert!(undecided_because(&got, why), "{name}: {got:?}");
    }
    // The same carrier on a loaded value is an exit on undecided data, and
    // the body's own copy of it stands for it.
    let (b, scope) = guarded(
        vec![
            (LdrRI, vec![x(D), x(BASE), imm(8)]),
            (TrapOverflowExact, vec![x(D), x(D), umul()]),
        ],
        1,
    );
    check_coverage(&b.func, &in_place(&b, 4, None), &scope, &lanes(&b))
        .expect("the scalar loop's own carrier on a loaded value");
}

#[test]
fn a_copy_stands_for_the_block_it_copies_only_where_the_rewrite_names_it() {
    use AArch64Opcode::*;
    // `for (i = 0; i < 4; i++) if (a[0] != 0) return i;` fully unrolled into
    // four copies of the body, each keeping the loaded exit (the shape of
    // `loop_unroll`'s bounded-early-exit tier).
    let b = counted_with(Counted::new(Start::Const(0), Bound::Imm(4)), true);
    let early = b.early.expect("a data exit");
    let unroll = |exit_of: &dyn Fn(usize) -> Insts| -> (MachFunction, Vec<BlockId>) {
        let mut after = b.func.clone();
        let copies: Vec<BlockId> = (0..4).map(|_| after.create_block()).collect();
        let jump = find(&after, b.pre, B);
        after.inst_mut(jump).operands[0] = blk(copies[0]);
        after.add_edge(b.pre, copies[0]);
        for (k, &copy) in copies.iter().enumerate() {
            for (opcode, operands) in exit_of(k) {
                push(&mut after, copy, opcode, operands);
            }
            after.add_edge(copy, early);
            constant(&mut after, copy, x(IV), k as u64 + 1);
            let next = copies.get(k + 1).copied().unwrap_or(b.exit);
            push(&mut after, copy, B, vec![blk(next)]);
            after.add_edge(copy, next);
        }
        (after, copies)
    };
    let loaded = |_: usize| -> Insts {
        vec![
            (LdrRI, vec![x(LOADED), x(BASE), imm(0)]),
            (Cbnz, vec![x(LOADED), blk(early)]),
        ]
    };
    let lanes = |copies: &[BlockId], named: bool| Lanes {
        blocks: copies.iter().map(|&copy| (copy, 1)).collect(),
        remainder: Remainder::None,
        copies: if named {
            copies.iter().map(|&copy| (copy, b.body)).collect()
        } else {
            Vec::new()
        },
    };
    let (after, copies) = unroll(&loaded);
    verdict(&b, &after, &[IV], &lanes(&copies, true)).expect("each copy's exit is the body's");
    let got = verdict(&b, &after, &[IV], &lanes(&copies, false));
    assert!(
        undecided_because(&got, "on undecided data"),
        "copies not named: {got:?}"
    );
    // The second copy leaves on `rbit(iv)` instead: named as a copy, it is
    // still not the body's instruction.
    let (after, copies) = unroll(&|k| {
        if k == 1 {
            vec![(Rbit, vec![x(T), x(IV)]), (Cbnz, vec![x(T), blk(early)])]
        } else {
            loaded(k)
        }
    });
    let got = verdict(&b, &after, &[IV], &lanes(&copies, true));
    assert!(
        undecided_because(&got, "on undecided data"),
        "an edited copy: {got:?}"
    );
}

#[test]
fn a_kept_loop_with_an_instruction_of_equal_effects_swapped_is_refused() {
    use AArch64Opcode::*;
    let lanes = Lanes {
        blocks: vec![],
        remainder: Remainder::ScalarLoop,
        copies: Vec::new(),
    };
    // `ldr t, [base]` and `rbit t, iv` are both an unknown write of `t`, so
    // the kept loop's effects were equal; on hardware the edited loop leaves
    // for `early` after 1 iteration, the scalar one after 64 when a[0] == 0.
    let b = counted_with(Counted::new(Start::Const(0), Bound::Pre(64)), true);
    let mut after = b.func.clone();
    let load = find(&after, b.body, LdrRI);
    *after.inst_mut(load) = MachInst::new(Rbit, vec![x(LOADED), x(IV)]);
    let got = verdict(&b, &after, &[IV], &lanes);
    assert!(
        undecided_because(&got, "is not the scalar loop unchanged"),
        "ldr -> rbit: {got:?}"
    );
    // A store deleted from the kept loop: no effect on the trip slice.
    let mut b = counted(Counted::new(Start::Const(0), Bound::Pre(64)));
    prepend(
        &mut b.func,
        b.body,
        vec![(StrRI, vec![x(IV), x(BASE), imm(16)])],
    );
    verdict(&b, &b.func.clone(), &[IV], &lanes).expect("the kept loop unchanged");
    let mut after = b.func.clone();
    after.block_mut(b.body).insts.remove(0);
    let got = verdict(&b, &after, &[IV], &lanes);
    assert!(
        undecided_because(&got, "is not the scalar loop unchanged"),
        "store deleted: {got:?}"
    );
}

#[test]
fn a_kept_loop_block_that_falls_through_elsewhere_is_refused() {
    use AArch64Opcode::*;
    // The header leaves on `b.hs exit` and falls through to the body, which
    // stores. A trampoline laid out between them (`iv += 1; b header`) skips
    // every store with the header's instructions unchanged.
    let mut b = counted(Counted::new(Start::Const(0), Bound::Imm(64)));
    let test = find(&b.func, b.header, BCond);
    b.func.inst_mut(test).operands = vec![imm(HS), blk(b.exit)];
    b.func.block_mut(b.header).insts.pop();
    prepend(
        &mut b.func,
        b.body,
        vec![(StrRI, vec![x(IV), x(BASE), imm(16)])],
    );
    let lanes = Lanes {
        blocks: vec![],
        remainder: Remainder::ScalarLoop,
        copies: Vec::new(),
    };
    verdict(&b, &b.func.clone(), &[IV], &lanes).expect("the kept loop unchanged");
    let mut after = b.func.clone();
    let y = after.create_block();
    push(&mut after, y, AddRI, vec![x(IV), x(IV), imm(1)]);
    push(&mut after, y, B, vec![blk(b.header)]);
    after.add_edge(b.header, y);
    after.add_edge(y, b.header);
    after.block_order.retain(|&block| block != y);
    let at = after
        .block_order
        .iter()
        .position(|&block| block == b.header)
        .expect("header");
    after.block_order.insert(at + 1, y);
    let got = verdict(&b, &after, &[IV], &lanes);
    assert!(
        undecided_because(&got, "is not the scalar loop unchanged"),
        "{got:?}"
    );
}

#[test]
fn a_preheader_that_computes_an_input_another_way_gives_the_rewrite_no_input() {
    use AArch64Opcode::*;
    // The bound `n` is loaded in the preheader, an input the clause samples.
    // A rewrite that loads it from another address used to run on the scalar
    // preheader's sample: with a[0] = 64 and a[1] = 6 the identity rewrite
    // below runs 6 iterations where the scalar loop runs 64.
    let mut b = counted(Counted::new(Start::Const(0), Bound::Pre(0)));
    let bound = *b
        .func
        .block(b.pre)
        .insts
        .iter()
        .find(|&&id| b.func.inst(id).operands.first() == Some(&x(N)))
        .expect("the bound's definition");
    *b.func.inst_mut(bound) = MachInst::new(LdrRI, vec![x(N), x(BASE), imm(0)]);
    let lanes = in_place_lanes(&b, 1);
    let edited = |edit: &dyn Fn(&mut MachFunction)| {
        let mut after = in_place(&b, 1, None);
        edit(&mut after);
        verdict(&b, &after, &[IV], &lanes)
    };
    edited(&|_| {}).expect("the same preheader");
    edited(&|after| {
        let jump = after.block_mut(b.pre).insts.pop().expect("the jump");
        push(after, b.pre, Movz, vec![x(T), imm(1)]);
        after.append_inst(b.pre, jump);
    })
    .expect("an instruction after the load");
    for (name, edit) in [
        (
            "the load moved to a[1]",
            &(|after: &mut MachFunction| {
                after.inst_mut(bound).operands[2] = imm(8);
            }) as &dyn Fn(&mut MachFunction),
        ),
        ("rbit in place of the load", &|after: &mut MachFunction| {
            *after.inst_mut(bound) = MachInst::new(Rbit, vec![x(N), x(BASE)]);
        }),
        (
            "the base advanced before the load",
            &|after: &mut MachFunction| {
                let id = after.push_inst(MachInst::new(AddRI, vec![x(BASE), x(BASE), imm(8)]));
                after.block_mut(b.pre).insts.insert(0, id);
            },
        ),
    ] {
        let got = edited(edit);
        assert!(
            matches!(got, Err(CoverageEscape::Undecided { .. })),
            "{name}: {got:?}"
        );
    }
}

#[test]
fn an_undecided_exit_of_the_preheader_is_refused() {
    use AArch64Opcode::*;
    use trust_cg_ir::{OverflowOp, pack_overflow_tag};
    // The preheader is not the scalar loop: the control clause accounts for
    // none of its exits. Each scalar preheader below has one the model does
    // not decide; the rewrite drops it, so only the scalar run meets it.
    let umul = imm(pack_overflow_tag(OverflowOp::UnsignedMul, 64));
    let shapes: [(&str, &dyn Fn(BlockId) -> Insts); 2] = [
        ("a trap whose test the model does not compute", &|_| {
            vec![(TrapOverflowExact, vec![x(BASE), x(BASE), umul.clone()])]
        }),
        (
            "a branch on a register written twice unmodeled (the first is an input)",
            &|exit| {
                vec![
                    (LdrRI, vec![x(T), x(BASE), imm(0)]),
                    (LdrRI, vec![x(T), x(BASE), imm(8)]),
                    (Cbnz, vec![x(T), blk(exit)]),
                ]
            },
        ),
    ];
    for (name, shape) in shapes {
        let mut b = counted(Counted::new(Start::Const(0), Bound::Imm(64)));
        let extra = shape(b.exit);
        let count = extra.len();
        prepend(&mut b.func, b.pre, extra);
        let mut after = in_place(&b, 4, None);
        after.block_mut(b.pre).insts.drain(..count);
        let got = verdict(&b, &after, &[IV], &in_place_lanes(&b, 4));
        assert!(
            undecided_because(&got, "the preheader has an exit"),
            "{name}: {got:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// One rewritten exit for one scalar exit, and the operands a trap the model
// does not compute reads
//
// Review of `23ed4a3e0` found each of these admitted. A rewritten exit was
// tied to every scalar exit of its text, so a NEW exit of that text was
// taken as the scalar loop's own: a flag reader's `b.ne early` names its
// condition code and target, not the compare behind it, and a `cbnz` can
// reuse the scalar exit's register. And the operands of a trap whose test
// the model does not compute were not in the trip slice, so one computed by
// modeled instructions was undecided data to the run. A MachIR interpreter
// run of each, by the reviewers, showed the behaviour that differs.
// ---------------------------------------------------------------------------

const U: u32 = 60;
const L: u32 = 61;
const L2: u32 = 62;
const P: u32 = 63;

/// Insert `insts` into `block` before its instruction `at`, with a CFG edge
/// to every block they name.
fn insert_at(f: &mut MachFunction, block: BlockId, at: usize, insts: Insts) {
    for (k, (opcode, operands)) in insts.into_iter().enumerate() {
        for operand in &operands {
            if let MachOperand::Block(target) = operand {
                f.add_edge(block, *target);
            }
        }
        let id = f.push_inst(MachInst::new(opcode, operands));
        f.block_mut(block).insts.insert(at + k, id);
    }
}

/// `ldr reg, [base, #offset]; cmp reg, #0; b.ne early`: a `break` on data in
/// flag form.
fn flag_break_on(reg: u32, offset: i64, early: BlockId) -> Insts {
    use AArch64Opcode::*;
    vec![
        (LdrRI, vec![x(reg), x(BASE), imm(offset)]),
        (CmpRI, vec![x(reg), imm(0)]),
        (BCond, vec![imm(NE), blk(early)]),
    ]
}

/// `rbit u, iv; cmp u, #0; b.ne early`: nonzero from iv = 1 on, and of the
/// same text, at its `b.ne`, as a flag-form `break` to `early`.
fn rbit_flag_exit(early: BlockId) -> Insts {
    use AArch64Opcode::*;
    vec![
        (Rbit, vec![x(U), x(IV)]),
        (CmpRI, vec![x(U), imm(0)]),
        (BCond, vec![imm(NE), blk(early)]),
    ]
}

/// `for (i = 0; i < trip; i++) if (a[0] != 0) return i;` with the `break` in
/// flag form.
fn flag_break(trip: i64) -> Built {
    use AArch64Opcode::*;
    let mut b = counted(Counted::new(Start::Const(0), Bound::Imm(trip)));
    let early = b.func.create_block();
    prepend(&mut b.func, b.body, flag_break_on(L, 0, early));
    push(&mut b.func, early, MovR, vec![x(OUT), x(IV)]);
    push(&mut b.func, early, Ret, vec![]);
    b.early = Some(early);
    b
}

#[test]
fn a_new_exit_of_the_text_of_the_scalar_loops_own_ties_neither() {
    use AArch64Opcode::*;
    let lanes = |b: &Built| in_place_lanes(b, 4);
    // Flag form, in place: the new exit on `rbit(iv)` before or after the
    // `break`'s own was assumed not taken as that `break` (4 iterations for
    // 64). With two instructions of the `break`'s text and one in the scalar
    // block, neither is tied.
    let b = flag_break(64);
    let early = b.early.expect("a data exit");
    verdict(&b, &in_place(&b, 4, None), &[IV], &lanes(&b))
        .expect("the break alone, in the body rewritten in place");
    for at in [0, 3] {
        let mut after = in_place(&b, 4, None);
        insert_at(&mut after, b.body, at, rbit_flag_exit(early));
        let got = verdict(&b, &after, &[IV], &lanes(&b));
        assert!(
            undecided_because(&got, "on undecided data"),
            "flag form at {at}: {got:?}"
        );
    }
    // Register form: a new exit that reuses the `break`'s register is the
    // `break`'s instruction as well.
    let b = counted_with(Counted::new(Start::Const(0), Bound::Imm(64)), true);
    let early = b.early.expect("a data exit");
    let mut after = in_place(&b, 4, None);
    prepend(
        &mut after,
        b.body,
        vec![
            (Rbit, vec![x(LOADED), x(IV)]),
            (Cbnz, vec![x(LOADED), blk(early)]),
        ],
    );
    let got = verdict(&b, &after, &[IV], &lanes(&b));
    assert!(
        undecided_because(&got, "on undecided data"),
        "register reused: {got:?}"
    );
    // A conditional trap the same way: a second null check of `d`, on
    // `rbit(iv)` (zero at iv = 0), ahead of the scalar loop's own on a
    // loaded `d`.
    let (b, scope) = guarded(
        vec![
            (LdrRI, vec![x(D), x(BASE), imm(8)]),
            (TrapNullIfZero, vec![x(D)]),
        ],
        1,
    );
    check_coverage(&b.func, &in_place(&b, 4, None), &scope, &lanes(&b))
        .expect("the scalar loop's own trap, in the body rewritten in place");
    let mut after = in_place(&b, 4, None);
    prepend(
        &mut after,
        b.body,
        vec![(Rbit, vec![x(D), x(IV)]), (TrapNullIfZero, vec![x(D)])],
    );
    let got = check_coverage(&b.func, &after, &scope, &lanes(&b));
    assert!(
        undecided_because(&got, "on undecided data"),
        "a second trap: {got:?}"
    );
    // Two traps of one text in the scalar block (null checks of `a[1]` and
    // `a[2]`, both loaded into `d`) stand, in order, for two of that text in
    // the rewritten one. A rewritten block that drops one of them ties
    // neither: which one it kept is not in the text. (The control clause
    // admits one transfer per exit edge, so two branches of one text cannot
    // both leave a scalar block.)
    let mut b = counted(Counted::new(Start::Const(0), Bound::Imm(64)));
    prepend(
        &mut b.func,
        b.body,
        vec![
            (LdrRI, vec![x(D), x(BASE), imm(8)]),
            (TrapNullIfZero, vec![x(D)]),
            (LdrRI, vec![x(D), x(BASE), imm(16)]),
            (TrapNullIfZero, vec![x(D)]),
        ],
    );
    let plan = ExitPlan::loop_test(b.header, b.exit)
        .and_reproduces(LoopExit::Stop {
            block: b.body,
            index: 1,
        })
        .and_reproduces(LoopExit::Stop {
            block: b.body,
            index: 3,
        });
    let scope = LoopLocality::check_covered(
        &b.func,
        [b.header, b.body],
        b.header,
        b.pre,
        &plan,
        Handoff::HeaderOrExit,
        &[VReg::new(IV, RegClass::Gpr64)],
    )
    .expect("the scalar loop passes the control and register clauses");
    check_coverage(&b.func, &in_place(&b, 4, None), &scope, &lanes(&b))
        .expect("both traps, in the body rewritten in place");
    let mut after = in_place(&b, 4, None);
    for _ in 0..2 {
        after.block_mut(b.body).insts.remove(2);
    }
    let got = check_coverage(&b.func, &after, &scope, &lanes(&b));
    assert!(
        undecided_because(&got, "on undecided data"),
        "a trap dropped: {got:?}"
    );
}

#[test]
fn a_new_exit_in_a_named_copy_ties_neither() {
    use AArch64Opcode::*;
    // The four-trip flag-form search loop fully unrolled into four copies of
    // the body, each keeping its `break` (the shape of `loop_unroll`'s
    // bounded-early-exit tier, which re-points its compare and clones its
    // `b.ne`). A new exit of the `break`'s text in one copy, beside the
    // copy's own, was assumed not taken as the body's `break` (1 iteration
    // for 4); each copy is one instance of the body, and in it the two tie
    // neither.
    let b = flag_break(4);
    let early = b.early.expect("a data exit");
    let unroll = |extra_in: Option<usize>| -> (MachFunction, Lanes<BlockId>) {
        let mut after = b.func.clone();
        let copies: Vec<BlockId> = (0..4).map(|_| after.create_block()).collect();
        let jump = find(&after, b.pre, B);
        after.inst_mut(jump).operands[0] = blk(copies[0]);
        after.add_edge(b.pre, copies[0]);
        for (k, &copy) in copies.iter().enumerate() {
            let mut exits = Vec::new();
            if extra_in == Some(k) {
                exits.extend(rbit_flag_exit(early));
            }
            exits.extend(flag_break_on(L, 0, early));
            for (opcode, operands) in exits {
                push(&mut after, copy, opcode, operands);
            }
            after.add_edge(copy, early);
            constant(&mut after, copy, x(IV), k as u64 + 1);
            let next = copies.get(k + 1).copied().unwrap_or(b.exit);
            push(&mut after, copy, B, vec![blk(next)]);
            after.add_edge(copy, next);
        }
        let lanes = Lanes {
            blocks: copies.iter().map(|&copy| (copy, 1)).collect(),
            remainder: Remainder::None,
            copies: copies.iter().map(|&copy| (copy, b.body)).collect(),
        };
        (after, lanes)
    };
    let (after, lanes) = unroll(None);
    verdict(&b, &after, &[IV], &lanes).expect("each copy's break is the body's");
    let (after, lanes) = unroll(Some(1));
    let got = verdict(&b, &after, &[IV], &lanes);
    assert!(
        undecided_because(&got, "on undecided data"),
        "a new exit in a copy: {got:?}"
    );
}

#[test]
fn a_trap_the_model_does_not_compute_is_known_through_modeled_values() {
    use AArch64Opcode::*;
    use trust_cg_ir::{OverflowOp, pack_overflow_tag};
    let umul = || imm(pack_overflow_tag(OverflowOp::UnsignedMul, 64));
    let lanes = |b: &Built| in_place_lanes(b, 4);
    let redefine_t = |b: &Built, def: Option<(AArch64Opcode, Vec<MachOperand>)>| {
        let mut after = in_place(b, 4, None);
        if let Some((opcode, operands)) = def {
            let mov = find(&after, b.body, MovR);
            *after.inst_mut(mov) = MachInst::new(opcode, operands);
        }
        after
    };
    // The scalar loop's multiply-overflow carrier tests `t * t` with
    // `t = iv`, which never overflows below 64. `t` was not in the trip
    // slice, which held only what a branch or a modeled trap reads, so the
    // run took it as undecided, and the rewritten loop's carrier, tied to
    // the scalar one, was assumed not taken: `t = iv << 30` (trapping at
    // iv = 4) and `t = iv + 2^33` (at iv = 0) were admitted where the
    // scalar loop returns 64. The run computes `t` now, and a carrier on
    // values it knows is refused, the unchanged one too, as the carrier
    // read on `iv` itself always was.
    let (b, scope) = guarded(
        vec![
            (MovR, vec![x(T), x(IV)]),
            (TrapOverflowExact, vec![x(T), x(T), umul()]),
        ],
        1,
    );
    for (name, def) in [
        ("unchanged", None),
        ("t = iv << 30", Some((LslRI, vec![x(T), x(IV), imm(30)]))),
        (
            "t = iv + 2^33",
            Some((AddRI, vec![x(T), x(IV), imm(1i64 << 33)])),
        ),
    ] {
        let got = check_coverage(&b.func, &redefine_t(&b, def), &scope, &lanes(&b));
        assert!(
            undecided_because(&got, "on values it knows"),
            "{name}: {got:?}"
        );
    }
    // An operand live into the loop that only the carrier reads is an input
    // the run samples, so it is known as well; read as undecided, it would
    // admit `t = iv << 30` beside `p` (`(iv << 30) * p` overflows at
    // p = 2^34, `iv * p` does not).
    let (b, scope) = guarded(
        vec![
            (MovR, vec![x(T), x(IV)]),
            (TrapOverflowExact, vec![x(T), x(P), umul()]),
        ],
        1,
    );
    let def = Some((LslRI, vec![x(T), x(IV), imm(30)]));
    let got = check_coverage(&b.func, &redefine_t(&b, def), &scope, &lanes(&b));
    assert!(
        undecided_because(&got, "on values it knows"),
        "beside an input: {got:?}"
    );
    // A loaded operand stays undecided, through a copy too: the carrier on a
    // copy of a loaded value, unchanged, stands for the scalar loop's own.
    let (b, scope) = guarded(
        vec![
            (LdrRI, vec![x(D), x(BASE), imm(8)]),
            (MovR, vec![x(T), x(D)]),
            (TrapOverflowExact, vec![x(T), x(T), umul()]),
        ],
        2,
    );
    check_coverage(&b.func, &redefine_t(&b, None), &scope, &lanes(&b))
        .expect("the scalar loop's own carrier on a copy of a loaded value");
}

// ---------------------------------------------------------------------------
// Inputs only a carrier reads
//
// A carrier's named operands are in the trip slice (fbdb55042), so one live
// into the loop, or computed by an unmodeled preheader instruction, is an
// input the run samples. Counted with the inputs the branches read, it moved
// a loop with two of those from every pair of samples to the sparse selection
// of three or more, and a wrong trip count at a pair outside that selection,
// refused before, was admitted (review of the merged fbdb55042). A MachIR
// interpreter run, by the reviewer, showed the behaviour that differs:
// n = 3, m = 5 returns 3 from the scalar loop and 4 from the rewrite.
// ---------------------------------------------------------------------------

const MM: u32 = 70;
const DN: u32 = 71;
const DM: u32 = 72;
const HIT: u32 = 73;
const B2: u32 = 74;
const Q: u32 = 75;
const ACC: u32 = 76;
const EQ: i64 = 0;

/// `for (iv = 0; iv < n; iv++)` (`n` live in) with `pre` before the
/// preheader's jump and `body` at the top of the body, and its scope: the
/// trap at each of `traps` in the body reproduced, and `carried` beside the
/// induction.
fn carried_by(
    pre: Insts,
    body: Insts,
    traps: &[usize],
    carried: &[u32],
) -> (Built, CoveredLoop<BlockId>) {
    let mut b = counted(Counted::new(Start::Const(0), Bound::Input));
    let jump = b.func.block(b.pre).insts.len() - 1;
    insert_at(&mut b.func, b.pre, jump, pre);
    prepend(&mut b.func, b.body, body);
    let mut plan = ExitPlan::loop_test(b.header, b.exit);
    for &index in traps {
        plan = plan.and_reproduces(LoopExit::Stop {
            block: b.body,
            index,
        });
    }
    let scope = LoopLocality::check_covered(
        &b.func,
        [b.header, b.body],
        b.header,
        b.pre,
        &plan,
        Handoff::HeaderOrExit,
        &[IV]
            .iter()
            .chain(carried)
            .map(|&id| VReg::new(id, RegClass::Gpr64))
            .collect::<Vec<_>>(),
    )
    .expect("the scalar loop passes the control and register clauses");
    (b, scope)
}

/// The rewrite: the header's bound becomes `n + ((n - 3) | (m - 5) == 0)`
/// (`m` live in), one iteration too many exactly at n = 3, m = 5, a pair
/// that only every pair of samples runs.
fn one_more_at_3_5(b: &Built) -> MachFunction {
    use AArch64Opcode::*;
    let mut f = b.func.clone();
    let cmp = find(&f, b.header, CmpRR);
    f.inst_mut(cmp).operands[1] = x(B2);
    prepend(
        &mut f,
        b.header,
        vec![
            (SubRI, vec![x(DN), x(N), imm(3)]),
            (SubRI, vec![x(DM), x(MM), imm(5)]),
            (OrrRR, vec![x(DN), x(DN), x(DM)]),
            (CmpRI, vec![x(DN), imm(0)]),
            (CSet, vec![x(HIT), imm(EQ)]),
            (AddRR, vec![x(B2), x(N), x(HIT)]),
        ],
    );
    f
}

/// Whether `verdict` is a mismatch found at n = 3, m = 5.
fn mismatch_at_3_5(verdict: &Result<IterationCoverage, CoverageEscape<BlockId>>) -> bool {
    matches!(
        verdict,
        Err(CoverageEscape::Mismatch { inputs, scalar, rewritten })
            if inputs.contains(&(N, 3))
                && inputs.contains(&(MM, 5))
                && (scalar.iterations, rewritten.iterations) == (3, 4)
    )
}

#[test]
fn an_input_only_a_carrier_reads_thins_no_other_inputs_sampling() {
    use AArch64Opcode::*;
    use trust_cg_ir::{OverflowOp, pack_overflow_tag};
    let umul = || imm(pack_overflow_tag(OverflowOp::UnsignedMul, 64));
    let lanes = |b: &Built| Lanes {
        blocks: vec![(b.body, 1)],
        remainder: Remainder::None,
        copies: Vec::new(),
    };
    // Without a carrier the inputs are n and m, every pair of samples runs,
    // and the rewrite is refused at n = 3, m = 5.
    let (b, scope) = carried_by(vec![], vec![], &[], &[]);
    let got = check_coverage(&b.func, &one_more_at_3_5(&b), &scope, &lanes(&b));
    assert!(mismatch_at_3_5(&got), "no carrier: {got:?}");
    // With a carrier on a loaded value and an input only it reads, the same
    // rewrite was admitted: n and m were sampled sparsely beside it. The
    // carrier's input reaches the slice by the carrier's own operand, by a
    // modeled value the operand reads, as a register the loop reads only
    // after writing it but the carrier (or a value it reads) reads first,
    // and as the result of an unmodeled preheader instruction.
    let shapes: Vec<(&str, Insts, Insts, usize, &[u32])> = vec![
        (
            "the carrier's operand",
            vec![],
            vec![
                (LdrRI, vec![x(LOADED), x(BASE), imm(0)]),
                (TrapOverflowExact, vec![x(LOADED), x(P), umul()]),
            ],
            1,
            &[],
        ),
        (
            "a modeled value of it",
            vec![],
            vec![
                (LdrRI, vec![x(LOADED), x(BASE), imm(0)]),
                (AddRI, vec![x(T), x(P), imm(1)]),
                (TrapOverflowExact, vec![x(LOADED), x(T), umul()]),
            ],
            2,
            &[],
        ),
        (
            "read by the carrier before the loop writes it",
            vec![],
            vec![
                (LdrRI, vec![x(LOADED), x(BASE), imm(0)]),
                (TrapOverflowExact, vec![x(LOADED), x(Q), umul()]),
                (Movz, vec![x(Q), imm(0)]),
                (AddRR, vec![x(IV), x(IV), x(Q)]),
            ],
            1,
            &[Q],
        ),
        (
            "read by a modeled value of it before the loop writes it",
            vec![],
            vec![
                (LdrRI, vec![x(LOADED), x(BASE), imm(0)]),
                (AddRI, vec![x(T), x(Q), imm(1)]),
                (TrapOverflowExact, vec![x(LOADED), x(T), umul()]),
                (Movz, vec![x(Q), imm(0)]),
                (AddRR, vec![x(IV), x(IV), x(Q)]),
            ],
            2,
            &[Q],
        ),
        (
            "an unmodeled preheader result",
            vec![(Rbit, vec![x(P), x(BASE)])],
            vec![
                (LdrRI, vec![x(LOADED), x(BASE), imm(0)]),
                (TrapOverflowExact, vec![x(LOADED), x(P), umul()]),
            ],
            1,
            &[],
        ),
    ];
    let mut wrong = Vec::new();
    for (name, pre, body, trap, carried) in shapes {
        let (b, scope) = carried_by(pre, body, &[trap], carried);
        let got = check_coverage(&b.func, &one_more_at_3_5(&b), &scope, &lanes(&b));
        if !mismatch_at_3_5(&got) {
            wrong.push(format!("{name}: {got:?}"));
        }
        let unchanged = check_coverage(&b.func, &b.func.clone(), &scope, &lanes(&b));
        if unchanged.is_err() {
            wrong.push(format!("{name}, the unchanged loop: {unchanged:?}"));
        }
    }
    // Two inputs only carriers read beside n and m take the runs past their
    // bound (every pair of n's and m's samples for each pair of their
    // pivots): refused undecided, never sampled sparsely. Beside n alone (the
    // unchanged loop reads no m) they fit, and run.
    let (b, scope) = carried_by(
        vec![],
        vec![
            (LdrRI, vec![x(LOADED), x(BASE), imm(0)]),
            (TrapOverflowExact, vec![x(LOADED), x(P), umul()]),
            (TrapOverflowExact, vec![x(LOADED), x(Q), umul()]),
        ],
        &[1, 2],
        &[],
    );
    let got = check_coverage(&b.func, &one_more_at_3_5(&b), &scope, &lanes(&b));
    if !undecided_because(&got, "inputs only a carrier reads") {
        wrong.push(format!("two carrier inputs beside n and m: {got:?}"));
    }
    let unchanged = check_coverage(&b.func, &b.func.clone(), &scope, &lanes(&b));
    if unchanged.is_err() {
        wrong.push(format!("two carrier inputs beside n: {unchanged:?}"));
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}

#[test]
fn an_input_only_a_carrier_reads_keeps_the_runs_it_had_when_counted() {
    use AArch64Opcode::*;
    use trust_cg_ir::{OverflowOp, pack_overflow_tag};
    let umul = || imm(pack_overflow_tag(OverflowOp::UnsignedMul, 64));
    // `acc += p` each iteration, and a carrier on a loaded value reads `acc`:
    // `acc` and `p` are inputs only that carrier makes, and `acc` is
    // reproduced. The rewrite adds 1 more where `p`'s low 16 bits are 3,
    // without a compare: `((p ^ 3) & 0xffff) - 1 >> 63`. Counted with `n`,
    // `p` ran over every sample and the rewrite was refused; over the pivots
    // alone it would not be, so the combinations of all three counted
    // together still run.
    let (b, scope) = carried_by(
        vec![],
        vec![
            (LdrRI, vec![x(LOADED), x(BASE), imm(0)]),
            (AddRR, vec![x(ACC), x(ACC), x(P)]),
            (TrapOverflowExact, vec![x(LOADED), x(ACC), umul()]),
        ],
        &[2],
        &[ACC],
    );
    let mut after = b.func.clone();
    // After `acc += p`, the body's instruction 1.
    insert_at(
        &mut after,
        b.body,
        2,
        vec![
            (EorRI, vec![x(DN), x(P), imm(3)]),
            (AndRI, vec![x(DN), x(DN), imm(0xffff)]),
            (SubRI, vec![x(DN), x(DN), imm(1)]),
            (LsrRI, vec![x(HIT), x(DN), imm(63)]),
            (AddRR, vec![x(ACC), x(ACC), x(HIT)]),
        ],
    );
    let lanes = Lanes {
        blocks: vec![(b.body, 1)],
        remainder: Remainder::None,
        copies: Vec::new(),
    };
    let got = check_coverage(&b.func, &after, &scope, &lanes);
    assert!(
        matches!(&got, Err(CoverageEscape::Mismatch { inputs, .. })
            if inputs.iter().any(|&(reg, value)| reg == P && value & 0xffff == 3)),
        "{got:?}"
    );
    check_coverage(&b.func, &b.func.clone(), &scope, &lanes).expect("the unchanged loop");
}

#[test]
fn inputs_only_a_carrier_reads_add_runs_and_replace_none() {
    // The other inputs take exactly the combinations they take alone, each
    // with every pick of the carrier-only inputs' pivots, wherever those
    // stand in the list; and every combination of all the inputs counted
    // together runs too. Nothing else runs, and nothing twice. With no
    // carrier-only input the selection is the one of all, in order. Past
    // the bound, an error.
    let input = |reg: u32, width: u8, carrier_only: bool| Input {
        reg,
        width,
        clobbered: false,
        carrier_only,
    };
    let pivots = |width: u8| {
        let mut values: Vec<u64> = PIVOTS.iter().map(|&v| v & mask(width)).collect();
        values.sort_unstable();
        values.dedup();
        values
    };
    let bases: Vec<Vec<Input>> = vec![
        vec![],
        vec![input(1, 64, false)],
        vec![input(1, 64, false), input(2, 32, false)],
        vec![input(1, 64, false), input(2, 64, false), input(3, 8, false)],
    ];
    let carriers: Vec<Vec<Input>> = vec![
        vec![],
        vec![input(7, 64, true)],
        vec![input(7, 8, true), input(8, 64, true)],
        vec![input(7, 64, true), input(8, 64, true)],
    ];
    for base in &bases {
        let alone = sampled_combos(base);
        for carrier in &carriers {
            for carrier_first in [false, true] {
                let inputs: Vec<Input> = if carrier_first {
                    carrier.iter().chain(base).copied().collect()
                } else {
                    base.iter().chain(carrier).copied().collect()
                };
                let picks: usize = carrier.iter().map(|c| pivots(c.width).len()).product();
                let shape = format!(
                    "{} + {} carrier-only, carriers first: {carrier_first}",
                    base.len(),
                    carrier.len()
                );
                let combos = match input_combos(&inputs) {
                    Ok(combos) => combos,
                    Err(why) => {
                        assert!(
                            alone.len() * picks > CARRIER_COMBO_BUDGET,
                            "{shape}: refused within the bound: {why}"
                        );
                        continue;
                    }
                };
                let together = sampled_combos(&inputs);
                if carrier.is_empty() {
                    assert_eq!(combos, together, "{shape}");
                    continue;
                }
                let run: HashSet<Vec<u64>> = combos.iter().cloned().collect();
                assert_eq!(run.len(), combos.len(), "{shape}: a repeated run");
                // The crossed combinations, built independently.
                let of_base: Vec<usize> = (0..inputs.len())
                    .filter(|&i| !inputs[i].carrier_only)
                    .collect();
                let of_carrier: Vec<usize> = (0..inputs.len())
                    .filter(|&i| inputs[i].carrier_only)
                    .collect();
                let mut crossed: HashSet<Vec<u64>> = HashSet::default();
                for combo in &alone {
                    let mut partial: Vec<Vec<u64>> = vec![vec![0; inputs.len()]];
                    for (&i, &value) in of_base.iter().zip(combo) {
                        partial[0][i] = value;
                    }
                    for &i in &of_carrier {
                        partial = partial
                            .iter()
                            .flat_map(|values| {
                                pivots(inputs[i].width).into_iter().map(move |v| {
                                    let mut next = values.clone();
                                    next[i] = v;
                                    next
                                })
                            })
                            .collect();
                    }
                    crossed.extend(partial);
                }
                assert_eq!(crossed.len(), alone.len() * picks, "{shape}");
                let expected: HashSet<Vec<u64>> =
                    crossed.iter().chain(&together).cloned().collect();
                assert_eq!(run, expected, "{shape}");
            }
        }
    }
    // One carrier-only input beside two full-width inputs fits the bound,
    // and every pair of all three's samples is not among its runs.
    let two = [input(1, 64, false), input(2, 64, false), input(7, 64, true)];
    let combos = input_combos(&two).expect("within the bound");
    assert!(combos.len() >= 43 * 43 * 6, "{}", combos.len());
    assert!(combos.contains(&vec![3, 5, 0]));
    assert!(!sampled_combos(&two).contains(&vec![3, 5, 0]));
}

// ---------------------------------------------------------------------------
// x86-64: the same rows in the x86 selector's dialect (tied two-operand ALU
// forms, `Jcc` + `Jmp` terminators)
// ---------------------------------------------------------------------------

fn xv(id: u32) -> X86ISelOperand {
    X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn xi(value: i64) -> X86ISelOperand {
    X86ISelOperand::Imm(value)
}
fn xb(block: Block) -> X86ISelOperand {
    X86ISelOperand::Block(block)
}
fn xpush(f: &mut X86ISelFunction, block: Block, opcode: X86Opcode, operands: Vec<X86ISelOperand>) {
    f.push_inst(block, X86ISelInst::new(opcode, operands));
}
fn jb(target: Block) -> Vec<X86ISelOperand> {
    vec![X86ISelOperand::CondCode(X86CondCode::B), xb(target)]
}

struct XBuilt {
    func: X86ISelFunction,
    pre: Block,
    header: Block,
    body: Block,
    exit: Block,
}

/// `for (iv = 0; iv <u bound; iv += 1)`: an immediate bound, or `n` live in.
fn x86_counted(bound: Option<i64>) -> XBuilt {
    use X86Opcode::*;
    let mut f = X86ISelFunction::new(
        "x86_counted".into(),
        X86Signature {
            params: vec![],
            returns: vec![],
        },
    );
    let (pre, header, body, exit) = (Block(0), Block(1), Block(2), Block(3));
    for block in [pre, header, body, exit] {
        f.ensure_block(block);
    }
    xpush(&mut f, pre, MovRI, vec![xv(IV), xi(0)]);
    xpush(&mut f, pre, Jmp, vec![xb(header)]);
    f.add_successor(pre, header);
    match bound {
        Some(value) => xpush(&mut f, header, CmpRI, vec![xv(IV), xi(value)]),
        None => xpush(&mut f, header, CmpRR, vec![xv(IV), xv(N)]),
    }
    xpush(&mut f, header, Jcc, jb(body));
    xpush(&mut f, header, Jmp, vec![xb(exit)]);
    f.add_successor(header, body);
    f.add_successor(header, exit);
    xpush(&mut f, body, AddRI, vec![xv(IV), xi(1)]);
    xpush(&mut f, body, Jmp, vec![xb(header)]);
    f.add_successor(body, header);
    xpush(&mut f, exit, MovRR, vec![xv(OUT), xv(IV)]);
    xpush(&mut f, exit, Ret, vec![]);
    XBuilt {
        func: f,
        pre,
        header,
        body,
        exit,
    }
}

fn x86_verdict(
    b: &XBuilt,
    after: &X86ISelFunction,
    lanes: &Lanes<Block>,
) -> Result<IterationCoverage, CoverageEscape<Block>> {
    let scope = LoopLocality::check_covered(
        &b.func,
        [b.header, b.body],
        b.header,
        b.pre,
        &ExitPlan::loop_test(b.header, b.exit),
        Handoff::HeaderOrExit,
        &[VReg::new(IV, RegClass::Gpr64)],
    )
    .expect("the scalar loop passes the control and register clauses");
    check_coverage(&b.func, after, &scope, lanes)
}

fn x86_counts(escape: CoverageEscape<Block>) -> (u128, u128) {
    match escape {
        CoverageEscape::Mismatch {
            scalar, rewritten, ..
        } => (scalar.iterations, rewritten.iterations),
        other => panic!("expected a mismatch, got {other:?}"),
    }
}

/// The in-place rewrite: the step and, optionally, the immediate bound.
fn x86_in_place(b: &XBuilt, step: i64, bound: Option<i64>) -> X86ISelFunction {
    let mut f = b.func.clone();
    f.blocks.get_mut(&b.body).expect("body").insts[0].operands[1] = xi(step);
    if let Some(bound) = bound {
        f.blocks.get_mut(&b.header).expect("header").insts[0].operands[1] = xi(bound);
    }
    f
}

#[test]
fn x86_in_place_vectorize_is_checked_like_aarch64() {
    let b = x86_counted(Some(64));
    let lanes = Lanes {
        blocks: vec![(b.body, 4)],
        remainder: Remainder::None,
        copies: Vec::new(),
    };
    x86_verdict(&b, &x86_in_place(&b, 4, None), &lanes).expect("16 trips of 4");
    // 4b1fb93c7's class: its own bound divided as well.
    let escape = x86_verdict(&b, &x86_in_place(&b, 4, Some(16)), &lanes).unwrap_err();
    assert_eq!(x86_counts(escape), (64, 16));
    // a0603f3bc's class: past an odd bound.
    let b = x86_counted(Some(65));
    let lanes = Lanes {
        blocks: vec![(b.body, 2)],
        remainder: Remainder::None,
        copies: Vec::new(),
    };
    let escape = x86_verdict(&b, &x86_in_place(&b, 2, None), &lanes).unwrap_err();
    assert_eq!(x86_counts(escape), (65, 66));
}

/// The front loop in x86 forms: `mb = n - slack` (tied `SubRI`), skipped for
/// `n <u 4`; `iv <u mb` to the trip; the latch `iv += 4`, counted.
fn x86_front(b: &XBuilt, slack: i64) -> (X86ISelFunction, Lanes<Block>) {
    use X86Opcode::*;
    let mut f = b.func.clone();
    let (pv, vh, vb, vl, vx) = (Block(10), Block(11), Block(12), Block(13), Block(14));
    for block in [pv, vh, vb, vl, vx] {
        f.ensure_block(block);
    }
    let jump = f
        .blocks
        .get_mut(&b.pre)
        .expect("pre")
        .insts
        .last_mut()
        .expect("jmp");
    jump.operands[0] = xb(pv);
    xpush(&mut f, pv, MovRR, vec![xv(MB), xv(N)]);
    xpush(&mut f, pv, SubRI, vec![xv(MB), xi(slack)]);
    xpush(&mut f, pv, CmpRI, vec![xv(N), xi(4)]);
    xpush(&mut f, pv, Jcc, jb(b.header));
    xpush(&mut f, pv, Jmp, vec![xb(vh)]);
    xpush(&mut f, vh, CmpRR, vec![xv(IV), xv(MB)]);
    xpush(&mut f, vh, Jcc, jb(vb));
    xpush(&mut f, vh, Jmp, vec![xb(vx)]);
    xpush(&mut f, vb, Jmp, vec![xb(vl)]);
    xpush(&mut f, vl, AddRI, vec![xv(IV), xi(4)]);
    xpush(&mut f, vl, Jmp, vec![xb(vh)]);
    xpush(&mut f, vx, Jmp, vec![xb(b.header)]);
    let lanes = Lanes {
        blocks: vec![(vl, 4)],
        remainder: Remainder::ScalarLoop,
        copies: Vec::new(),
    };
    (f, lanes)
}

#[test]
fn x86_front_loop_is_checked_like_aarch64() {
    let b = x86_counted(None);
    let (after, lanes) = x86_front(&b, 3);
    x86_verdict(&b, &after, &lanes).expect("vector prefix + scalar remainder");
    let (after, lanes) = x86_front(&b, 0);
    let (scalar, rewritten) = x86_counts(x86_verdict(&b, &after, &lanes).unwrap_err());
    assert!(rewritten > scalar, "{rewritten} lanes for {scalar}");
}

#[test]
fn x86_a_conditional_trap_only_the_new_code_has_is_refused() {
    use X86Opcode::*;
    // The x86 guard carriers whose condition the model does not compute were
    // flags clobbered only, never taken, wherever they stood. On values the
    // run knows (the induction, or `base`, live into the loop and sampled),
    // each is a trap whose outcome those values fix; on a loaded value, an
    // exit only the new code has.
    let b = x86_counted(None);
    let load = X86ISelInst::new(
        MovRM,
        vec![
            xv(L),
            X86ISelOperand::MemAddr {
                base: Box::new(xv(BASE)),
                disp: 0,
            },
        ],
    );
    for (guard, operand, why) in [
        (TrapNullIfZeroExact, IV, "on values it knows"),
        (TrapDivZeroExact, IV, "on values it knows"),
        (TrapNullIfZeroExact, BASE, "on values it knows"),
        (TrapDivZeroExact, BASE, "on values it knows"),
        (TrapNullIfZeroExact, L, "on undecided data"),
        (TrapDivZeroExact, L, "on undecided data"),
    ] {
        let (mut after, lanes) = x86_front(&b, 3);
        let vb = after.blocks.get_mut(&Block(12)).expect("vb");
        vb.insts
            .insert(0, X86ISelInst::new(guard, vec![xv(operand)]));
        vb.insts.insert(0, load.clone());
        let got = x86_verdict(&b, &after, &lanes);
        assert!(
            matches!(got, Err(CoverageEscape::Undecided { why: reason }) if reason.contains(why)),
            "{guard:?} on {operand}: {got:?}"
        );
    }
}

#[test]
fn x86_a_new_exit_of_the_text_of_the_scalar_loops_own_ties_neither() {
    use X86Opcode::*;
    // `jne early` names its condition code and target, not the compare
    // behind it: a second loaded `break` (on `a[1]`) to the block the scalar
    // loop's (on `a[0]`) leaves to was assumed not taken as that `break`.
    let mut b = x86_counted(Some(64));
    let early = Block(7);
    b.func.ensure_block(early);
    let jne_break = |reg: u32, disp: i32| {
        vec![
            X86ISelInst::new(
                MovRM,
                vec![
                    xv(reg),
                    X86ISelOperand::MemAddr {
                        base: Box::new(xv(BASE)),
                        disp,
                    },
                ],
            ),
            X86ISelInst::new(CmpRI, vec![xv(reg), xi(0)]),
            X86ISelInst::new(
                Jcc,
                vec![X86ISelOperand::CondCode(X86CondCode::NE), xb(early)],
            ),
        ]
    };
    let body = b.func.blocks.get_mut(&b.body).expect("body");
    for (k, inst) in jne_break(L, 0).into_iter().enumerate() {
        body.insts.insert(k, inst);
    }
    b.func.add_successor(b.body, early);
    xpush(&mut b.func, early, MovRR, vec![xv(OUT), xv(IV)]);
    xpush(&mut b.func, early, Ret, vec![]);
    let plan = ExitPlan::loop_test(b.header, b.exit).and_reproduces(LoopExit::Edge {
        from: b.body,
        to: early,
    });
    let scope = LoopLocality::check_covered(
        &b.func,
        [b.header, b.body],
        b.header,
        b.pre,
        &plan,
        Handoff::HeaderOrExit,
        &[VReg::new(IV, RegClass::Gpr64)],
    )
    .expect("the scalar loop passes the control and register clauses");
    let lanes = Lanes {
        blocks: vec![(b.body, 4)],
        remainder: Remainder::None,
        copies: Vec::new(),
    };
    let in_place = |extra: Vec<X86ISelInst>| {
        let mut f = b.func.clone();
        let body = f.blocks.get_mut(&b.body).expect("body");
        let step = body
            .insts
            .iter()
            .position(|inst| inst.opcode == AddRI)
            .expect("the step");
        body.insts[step].operands[1] = xi(4);
        for (k, inst) in extra.into_iter().enumerate() {
            body.insts.insert(k, inst);
        }
        f
    };
    check_coverage(&b.func, &in_place(vec![]), &scope, &lanes)
        .expect("the break alone, in the body rewritten in place");
    let got = check_coverage(&b.func, &in_place(jne_break(L2, 8)), &scope, &lanes);
    assert!(
        matches!(&got, Err(CoverageEscape::Undecided { why }) if why.contains("on undecided data")),
        "a second break: {got:?}"
    );
}

// ---------------------------------------------------------------------------
// The model itself
// ---------------------------------------------------------------------------

/// Run `f` with acceleration off, then on, and require the same verdict.
fn same_both_ways<T: PartialEq + Debug>(f: impl Fn() -> T) -> T {
    NO_ACCELERATION.with(|off| off.set(true));
    let stepped = f();
    NO_ACCELERATION.with(|off| off.set(false));
    let accelerated = f();
    assert_eq!(stepped, accelerated, "acceleration changed the verdict");
    accelerated
}

#[test]
fn acceleration_agrees_with_stepping() {
    // Every combination of start, bound, compare and step whose loop ends
    // within the stepping budget, 64- and 32-bit, in place by 1, 2 and 3.
    let mut decided = 0;
    for narrow in [false, true] {
        for start in [0u64, 1, 2, 5] {
            for bound in [0i64, 1, 2, 3, 4, 7, 8, 9, 31, 64, 100, 257] {
                for (cond, step) in [
                    (LO, 1),
                    (LO, 2),
                    (LO, 3),
                    (LS, 1),
                    (LS, 4),
                    (NE, 1),
                    (LT, 2),
                ] {
                    if cond == NE && (bound as u64) < start {
                        continue;
                    }
                    let c = Counted {
                        start: Start::Const(start),
                        bound: Bound::Imm(bound),
                        cond,
                        step,
                        narrow,
                    };
                    let b = counted(c);
                    for vf in [1, 2, 3] {
                        let after = in_place(&b, step * vf, None);
                        let lanes = in_place_lanes(&b, vf as u64);
                        same_both_ways(|| verdict(&b, &after, &[], &lanes).is_ok());
                        decided += 1;
                    }
                }
            }
        }
    }
    assert!(decided > 1000);
}

#[test]
fn a_narrow_induction_wraps_at_32_bits() {
    // `w` registers: `n` sampled up to 2^32 - 1, the vector loop at 32 bits.
    let mut c = Counted::new(Start::Const(0), Bound::Input);
    c.narrow = true;
    let b = counted(c);
    let after = in_place(&b, 1, None);
    verdict(&b, &after, &[], &in_place_lanes(&b, 1)).expect("an unchanged loop covers");
}

#[test]
fn an_unchanged_loop_covers_itself() {
    for bound in [
        Bound::Imm(0),
        Bound::Imm(70),
        Bound::Header(70),
        Bound::Input,
    ] {
        for start in [Start::Const(0), Start::Const(9), Start::Input] {
            let b = counted(Counted::new(start, bound));
            verdict(&b, &b.func.clone(), &[IV], &in_place_lanes(&b, 1))
                .expect("the identity rewrite");
        }
    }
}

// ---------------------------------------------------------------------------
// The clause's boundary
// ---------------------------------------------------------------------------

/// Every `.rs` file under `dir` other than a `tests.rs` or a file under a
/// `tests/` directory, as `(path relative to src/, contents)`.
fn crate_sources(dir: &std::path::Path, root: &std::path::Path, out: &mut Vec<(String, String)>) {
    let mut entries: Vec<_> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read {dir:?}: {e}"))
        .map(|entry| entry.expect("directory entry").path())
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            if path.file_name().is_some_and(|name| name == "tests") {
                continue;
            }
            crate_sources(&path, root, out);
        } else if path.extension().is_some_and(|ext| ext == "rs")
            && path.file_name().is_some_and(|name| name != "tests.rs")
        {
            let relative = path
                .strip_prefix(root)
                .expect("under src")
                .to_string_lossy()
                .replace('\\', "/");
            let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path:?}: {e}"));
            out.push((relative, text));
        }
    }
}

#[test]
fn coverage_routes_list_every_uncovered_rewrite() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut sources = Vec::new();
    crate_sources(&root, &root, &mut sources);
    let mut counted: Vec<(String, usize)> = sources
        .iter()
        .map(|(path, text)| {
            // `check_in` is `check` over a shared index: the same two clauses.
            let uncovered = text.matches("LoopLocality::check(").count()
                + text.matches("LoopLocality::check_in(").count();
            (path.clone(), uncovered)
        })
        .filter(|(_, count)| *count > 0)
        .collect();
    counted.sort();
    let listed: Vec<(String, usize)> = include_str!("../coverage_routes.txt")
        .lines()
        .filter(|line| !line.starts_with('#') && !line.trim().is_empty())
        .map(|line| {
            let (path, count) = line.rsplit_once(' ').expect("`<path> <count>`");
            (path.to_owned(), count.parse().expect("a count"))
        })
        .collect();
    assert_eq!(
        counted, listed,
        "loop_contract/coverage_routes.txt must list exactly the files that admit a rewrite with \
         `LoopLocality::check(` or `LoopLocality::check_in(` (outside the iteration-coverage \
         clause), with their counts"
    );
    // The routed rewrites publish through the clause.
    for (path, needle) in [
        ("vectorize.rs", "publish_covered("),
        ("loop_unroll.rs", "publish_covered("),
        ("neon_fill.rs", "commit_covered("),
    ] {
        let text = &sources
            .iter()
            .find(|(p, _)| p == path)
            .unwrap_or_else(|| panic!("no {path}"))
            .1;
        assert!(text.contains(needle), "{path} no longer calls {needle}");
    }
}
