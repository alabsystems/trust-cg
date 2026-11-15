// trust-cg-verify/post_ra_value_flow/tests.rs - unit tests and corruption controls
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Hand-built specification/implementation pairs: each faithful rewrite a
//! post-allocation stage performs validates, and each corruption of it is
//! refused with the expected kind.

use trust_cg_ir::aarch64_regs::{X0, X1, X30};
use trust_cg_ir::function::{JumpTableData, StackSlot};
use trust_cg_ir::regs::VReg;
use trust_cg_ir::types::StackSlotId;
use trust_cg_ir::{
    AArch64Opcode as Op, BlockId, InstFlags, InstId, MachFunction, MachInst, MachOperand as O,
    PReg, RegClass, Signature, SpecialReg,
};

use super::{FrameFacts, Report, Stage, StageInputs, Verdict, ViolationKind, compare};

static RET_X0: [PReg; 1] = [X0];
static USES_X0: [PReg; 1] = [X0];
static USES_X0_X1: [PReg; 2] = [X0, X1];

fn func(name: &str) -> MachFunction {
    MachFunction::new(name.into(), Signature::new(vec![], vec![]))
}

fn push(f: &mut MachFunction, b: BlockId, inst: MachInst) -> InstId {
    let id = f.push_inst(inst);
    f.append_inst(b, id);
    id
}

fn i(op: Op, ops: Vec<O>) -> MachInst {
    MachInst::new(op, ops)
}

fn x(n: u16) -> O {
    O::PReg(PReg::new(n))
}

fn v(id: u32) -> O {
    O::VReg(VReg::new(id, RegClass::Gpr64))
}

fn imm(k: i64) -> O {
    O::Imm(k)
}

fn blk(b: BlockId) -> O {
    O::Block(b)
}

fn slot(s: u32) -> O {
    O::StackSlot(StackSlotId(s))
}

fn sp() -> O {
    O::Special(SpecialReg::SP)
}

fn mem(base: u16, offset: i64) -> O {
    O::MemOp {
        base: PReg::new(base),
        offset,
    }
}

fn ret() -> MachInst {
    MachInst::new(Op::Ret, vec![x(30)]).with_implicit_uses(&RET_X0)
}

fn ret_void() -> MachInst {
    MachInst::new(Op::Ret, vec![x(30)])
}

fn call(name: &str, uses: &'static [PReg]) -> MachInst {
    MachInst::new(Op::Bl, vec![O::Symbol(name.into())]).with_implicit_uses(uses)
}

fn spill(mut inst: MachInst) -> MachInst {
    inst.flags.insert(InstFlags::SPILL_SLOT_ACCESS);
    inst
}

fn alloc(spec: &MachFunction, implementation: &MachFunction) -> Report {
    compare(StageInputs {
        spec,
        implementation,
        stage: Stage::Allocation,
        allocator_slot_start: spec.stack_slots.len() as u32,
        frame: None,
        inserted_from: None,
        reserved_x18: true,
    })
}

fn frame(
    spec: &MachFunction,
    implementation: &MachFunction,
    facts: &FrameFacts,
    start: u32,
) -> Report {
    compare(StageInputs {
        spec,
        implementation,
        stage: Stage::FrameLayout,
        allocator_slot_start: start,
        frame: Some(facts),
        inserted_from: None,
        reserved_x18: true,
    })
}

#[track_caller]
fn validated(report: &Report) {
    assert_eq!(report.verdict, Verdict::Validated, "{}", report.line("t"));
}

#[track_caller]
fn refused(report: &Report, kind: ViolationKind) {
    match &report.verdict {
        Verdict::Violation { kind: got, .. } => {
            assert_eq!(*got, kind, "{}", report.line("t"))
        }
        other => panic!("expected a {kind:?} violation, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Straight-line values
// ---------------------------------------------------------------------------

/// `(x0 + x1) * x0` with virtual registers.
fn arith_spec() -> MachFunction {
    let mut f = func("arith");
    let b = f.entry;
    push(&mut f, b, i(Op::Copy, vec![v(0), x(0)]));
    push(&mut f, b, i(Op::Copy, vec![v(1), x(1)]));
    push(&mut f, b, i(Op::AddRR, vec![v(2), v(0), v(1)]));
    push(&mut f, b, i(Op::MulRR, vec![v(3), v(2), v(0)]));
    push(&mut f, b, i(Op::Copy, vec![x(0), v(3)]));
    push(&mut f, b, ret());
    f
}

fn arith_impl(tmp: u16, mul_rhs: u16) -> MachFunction {
    let mut f = func("arith");
    let b = f.entry;
    push(&mut f, b, i(Op::AddRR, vec![x(tmp), x(0), x(1)]));
    push(&mut f, b, i(Op::MulRR, vec![x(0), x(tmp), x(mul_rhs)]));
    push(&mut f, b, ret());
    f
}

#[test]
fn allocated_arithmetic_validates() {
    validated(&alloc(&arith_spec(), &arith_impl(9, 0)));
}

#[test]
fn an_altered_use_is_refused() {
    refused(
        &alloc(&arith_spec(), &arith_impl(9, 1)),
        ViolationKind::ValueMismatch,
    );
}

#[test]
fn an_altered_definition_is_refused() {
    let mut f = arith_impl(9, 0);
    // The add now defines x10, which nothing reads; the multiply reads a
    // stale x9.
    f.insts[0].operands[0] = x(10);
    refused(&alloc(&arith_spec(), &f), ViolationKind::ValueMismatch);
}

#[test]
fn a_write_of_x18_is_refused() {
    refused(
        &alloc(&arith_spec(), &arith_impl(18, 0)),
        ViolationKind::ReservedRegister,
    );
}

#[test]
fn a_phi_is_unmodeled() {
    let mut spec = arith_spec();
    spec.insts.insert(0, i(Op::Phi, vec![v(7)]));
    // The inserted instruction shifted the arena: rebuild the block list.
    spec.blocks[0].insts = (0..spec.insts.len() as u32).map(InstId).collect();
    match alloc(&spec, &arith_impl(9, 0)).verdict {
        Verdict::Unmodeled(why) => assert!(why.contains("phi"), "{why}"),
        other => panic!("expected unmodeled, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Calls, spills and rematerialization
// ---------------------------------------------------------------------------

/// `ext(x0) + x1`: `x1` must survive the call.
fn call_spec() -> MachFunction {
    let mut f = func("callsum");
    let b = f.entry;
    push(&mut f, b, i(Op::Copy, vec![v(0), x(0)]));
    push(&mut f, b, i(Op::Copy, vec![v(1), x(1)]));
    push(&mut f, b, i(Op::Copy, vec![x(0), v(0)]));
    push(&mut f, b, call("ext", &USES_X0));
    push(&mut f, b, i(Op::Copy, vec![v(2), x(0)]));
    push(&mut f, b, i(Op::AddRR, vec![v(3), v(2), v(1)]));
    push(&mut f, b, i(Op::Copy, vec![x(0), v(3)]));
    push(&mut f, b, ret());
    f
}

fn call_impl_in(keep: u16) -> MachFunction {
    let mut f = func("callsum");
    let b = f.entry;
    push(&mut f, b, i(Op::MOVXrr, vec![x(keep), x(1)]));
    push(&mut f, b, call("ext", &USES_X0));
    push(&mut f, b, i(Op::AddRR, vec![x(0), x(0), x(keep)]));
    push(&mut f, b, ret());
    f
}

#[test]
fn a_callee_saved_value_across_a_call_validates() {
    validated(&alloc(&call_spec(), &call_impl_in(19)));
}

#[test]
fn a_caller_saved_register_live_across_a_call_is_refused() {
    refused(
        &alloc(&call_spec(), &call_impl_in(9)),
        ViolationKind::ValueMismatch,
    );
}

/// The value spilled to slot 0 around the call; `reload` names the slot the
/// reload reads (slot 1 holds the argument).
fn call_impl_spilled(reload: u32) -> MachFunction {
    let mut f = func("callsum");
    f.alloc_stack_slot(StackSlot::new(8, 8));
    f.alloc_stack_slot(StackSlot::new(8, 8));
    let b = f.entry;
    push(&mut f, b, spill(i(Op::StrRI, vec![x(1), slot(0)])));
    push(&mut f, b, spill(i(Op::StrRI, vec![x(0), slot(1)])));
    push(&mut f, b, call("ext", &USES_X0));
    push(&mut f, b, spill(i(Op::LdrRI, vec![x(16), slot(reload)])));
    push(&mut f, b, i(Op::AddRR, vec![x(0), x(0), x(16)]));
    push(&mut f, b, ret());
    f
}

#[test]
fn a_spill_and_reload_around_a_call_validates() {
    validated(&alloc(&call_spec(), &call_impl_spilled(0)));
}

#[test]
fn a_reload_from_the_wrong_slot_is_refused() {
    refused(
        &alloc(&call_spec(), &call_impl_spilled(1)),
        ViolationKind::ValueMismatch,
    );
}

#[test]
fn a_dropped_spill_store_is_refused() {
    let mut f = call_impl_spilled(0);
    f.blocks[0].insts.remove(0);
    refused(&alloc(&call_spec(), &f), ViolationKind::ValueMismatch);
}

/// `ext(x0) + c`, with `c` a constant (`#42`) or a load from `x1`.
fn remat_spec(loaded: bool) -> MachFunction {
    let mut f = func("remat");
    let b = f.entry;
    push(&mut f, b, i(Op::Copy, vec![v(0), x(0)]));
    push(&mut f, b, i(Op::Copy, vec![v(5), x(1)]));
    if loaded {
        push(&mut f, b, i(Op::LdrRI, vec![v(1), v(5), imm(0)]));
    } else {
        push(&mut f, b, i(Op::Movz, vec![v(1), imm(42)]));
    }
    push(&mut f, b, i(Op::Copy, vec![x(0), v(0)]));
    push(&mut f, b, call("ext", &USES_X0));
    push(&mut f, b, i(Op::Copy, vec![v(2), x(0)]));
    push(&mut f, b, i(Op::AddRR, vec![v(3), v(2), v(1)]));
    push(&mut f, b, i(Op::Copy, vec![x(0), v(3)]));
    push(&mut f, b, ret());
    f
}

/// The value recomputed after the call instead of kept: `MOVZ #k`, or the
/// load re-executed.
fn remat_impl(loaded: bool, k: i64) -> MachFunction {
    let mut f = func("remat");
    let b = f.entry;
    if loaded {
        push(&mut f, b, i(Op::LdrRI, vec![x(9), x(1), imm(0)]));
        push(&mut f, b, i(Op::MOVXrr, vec![x(19), x(1)]));
    }
    push(&mut f, b, call("ext", &USES_X0));
    if loaded {
        push(&mut f, b, i(Op::LdrRI, vec![x(9), x(19), imm(0)]));
    } else {
        push(&mut f, b, i(Op::Movz, vec![x(9), imm(k)]));
    }
    push(&mut f, b, i(Op::AddRR, vec![x(0), x(0), x(9)]));
    push(&mut f, b, ret());
    f
}

#[test]
fn a_rematerialized_constant_validates() {
    validated(&alloc(&remat_spec(false), &remat_impl(false, 42)));
}

#[test]
fn a_rematerialized_wrong_constant_is_refused() {
    refused(
        &alloc(&remat_spec(false), &remat_impl(false, 43)),
        ViolationKind::ValueMismatch,
    );
}

#[test]
fn a_rematerialized_load_is_refused() {
    // Memory may have changed across the call: re-executing the load is an
    // extra effect, not the spilled value.
    refused(
        &alloc(&remat_spec(true), &remat_impl(true, 0)),
        ViolationKind::EffectMismatch,
    );
}

// ---------------------------------------------------------------------------
// Effects
// ---------------------------------------------------------------------------

/// `*(x0 + 8) = x1`.
fn store_spec() -> MachFunction {
    let mut f = func("store");
    let b = f.entry;
    push(&mut f, b, i(Op::Copy, vec![v(0), x(0)]));
    push(&mut f, b, i(Op::Copy, vec![v(1), x(1)]));
    push(&mut f, b, i(Op::StrRI, vec![v(1), v(0), imm(8)]));
    push(&mut f, b, ret_void());
    f
}

fn store_impl(stores: &[i64]) -> MachFunction {
    let mut f = func("store");
    let b = f.entry;
    for &offset in stores {
        push(&mut f, b, i(Op::StrRI, vec![x(1), x(0), imm(offset)]));
    }
    push(&mut f, b, ret_void());
    f
}

#[test]
fn a_store_validates() {
    validated(&alloc(&store_spec(), &store_impl(&[8])));
}

#[test]
fn a_deleted_store_is_refused() {
    refused(
        &alloc(&store_spec(), &store_impl(&[])),
        ViolationKind::EffectMismatch,
    );
}

#[test]
fn a_duplicated_store_is_refused() {
    refused(
        &alloc(&store_spec(), &store_impl(&[8, 8])),
        ViolationKind::EffectMismatch,
    );
}

#[test]
fn a_store_to_a_shifted_address_is_refused() {
    refused(
        &alloc(&store_spec(), &store_impl(&[16])),
        ViolationKind::ValueMismatch,
    );
}

/// Load `[x0]` and `[x0 + 8]`, add them; the specification forms the second
/// address with an add, `LDP` in `pair`.
fn loads_spec(pair: bool) -> MachFunction {
    let mut f = func("loads");
    let b = f.entry;
    push(&mut f, b, i(Op::Copy, vec![v(0), x(0)]));
    if pair {
        push(&mut f, b, i(Op::LdpRI, vec![v(1), v(3), v(0), imm(0)]));
    } else {
        push(&mut f, b, i(Op::LdrRI, vec![v(1), v(0), imm(0)]));
        push(&mut f, b, i(Op::AddRI, vec![v(2), v(0), imm(8)]));
        push(&mut f, b, i(Op::LdrRI, vec![v(3), v(2), imm(0)]));
    }
    push(&mut f, b, i(Op::AddRR, vec![v(4), v(1), v(3)]));
    push(&mut f, b, i(Op::Copy, vec![x(0), v(4)]));
    push(&mut f, b, ret());
    f
}

#[test]
fn a_post_index_load_validates() {
    let mut f = func("loads");
    let b = f.entry;
    push(&mut f, b, i(Op::LdrPostIndex, vec![x(1), x(0), imm(8)]));
    push(&mut f, b, i(Op::LdrRI, vec![x(2), x(0), imm(0)]));
    push(&mut f, b, i(Op::AddRR, vec![x(0), x(1), x(2)]));
    push(&mut f, b, ret());
    validated(&alloc(&loads_spec(false), &f));
}

#[test]
fn a_split_load_pair_validates_in_address_order_only() {
    let split = |first: i64, second: i64| {
        let mut f = func("loads");
        let b = f.entry;
        let (r1, r2) = if first == 0 { (1, 2) } else { (2, 1) };
        push(&mut f, b, i(Op::LdrRI, vec![x(r1), x(0), imm(first)]));
        push(&mut f, b, i(Op::LdrRI, vec![x(r2), x(0), imm(second)]));
        push(&mut f, b, i(Op::AddRR, vec![x(0), x(1), x(2)]));
        push(&mut f, b, ret());
        f
    };
    validated(&alloc(&loads_spec(true), &split(0, 8)));
    refused(
        &alloc(&loads_spec(true), &split(8, 0)),
        ViolationKind::ValueMismatch,
    );
}

// ---------------------------------------------------------------------------
// Loops: the inferred location relation
// ---------------------------------------------------------------------------

/// `acc = 0; for (i = 0; i < n; i++) acc += i; return acc`.
fn loop_spec() -> MachFunction {
    let mut f = func("sum");
    let b0 = f.entry;
    let b1 = f.create_block();
    let b2 = f.create_block();
    let b3 = f.create_block();
    push(&mut f, b0, i(Op::Copy, vec![v(0), x(0)]));
    push(&mut f, b0, i(Op::Movz, vec![v(1), imm(0)]));
    push(&mut f, b0, i(Op::Movz, vec![v(2), imm(0)]));
    push(&mut f, b0, i(Op::B, vec![blk(b1)]));
    push(&mut f, b1, i(Op::CmpRR, vec![v(1), v(0)]));
    push(&mut f, b1, i(Op::BCond, vec![imm(3), blk(b2)]));
    push(&mut f, b1, i(Op::B, vec![blk(b3)]));
    push(&mut f, b2, i(Op::AddRR, vec![v(3), v(2), v(1)]));
    push(&mut f, b2, i(Op::AddRI, vec![v(4), v(1), imm(1)]));
    push(&mut f, b2, i(Op::MovR, vec![v(2), v(3)]));
    push(&mut f, b2, i(Op::MovR, vec![v(1), v(4)]));
    push(&mut f, b2, i(Op::B, vec![blk(b1)]));
    push(&mut f, b3, i(Op::Copy, vec![x(0), v(2)]));
    push(&mut f, b3, ret());
    f
}

/// The loop with `i` in x9 and `acc` in `acc` (x9 too: an interfering
/// coalesce); `exit` is where `B.LO` goes, `inverted` tests `B.HS` instead.
fn loop_impl(acc: u16, taken: u32, inverted: bool) -> MachFunction {
    let mut f = func("sum");
    let b0 = f.entry;
    let b1 = f.create_block();
    let b2 = f.create_block();
    let b3 = f.create_block();
    push(&mut f, b0, i(Op::Movz, vec![x(9), imm(0)]));
    push(&mut f, b0, i(Op::Movz, vec![x(acc), imm(0)]));
    push(&mut f, b0, i(Op::B, vec![blk(b1)]));
    push(&mut f, b1, i(Op::CmpRR, vec![x(9), x(0)]));
    let target = BlockId(taken);
    let other = if taken == b2.0 { b3 } else { b2 };
    if inverted {
        push(&mut f, b1, i(Op::BCond, vec![imm(2), blk(other)]));
        push(&mut f, b1, i(Op::B, vec![blk(target)]));
    } else {
        push(&mut f, b1, i(Op::BCond, vec![imm(3), blk(target)]));
        push(&mut f, b1, i(Op::B, vec![blk(other)]));
    }
    push(&mut f, b2, i(Op::AddRR, vec![x(acc), x(acc), x(9)]));
    push(&mut f, b2, i(Op::AddRI, vec![x(9), x(9), imm(1)]));
    push(&mut f, b2, i(Op::B, vec![blk(b1)]));
    push(&mut f, b3, i(Op::MOVXrr, vec![x(0), x(acc)]));
    push(&mut f, b3, ret());
    f
}

#[test]
fn an_allocated_loop_validates() {
    validated(&alloc(&loop_spec(), &loop_impl(10, 2, false)));
}

#[test]
fn an_inverted_branch_with_swapped_targets_validates() {
    validated(&alloc(&loop_spec(), &loop_impl(10, 2, true)));
}

#[test]
fn a_coalesce_of_interfering_values_is_refused() {
    // The merged register feeds the loop compare: the branch decision is the
    // first place the two functions provably part.
    refused(
        &alloc(&loop_spec(), &loop_impl(9, 2, false)),
        ViolationKind::ControlMismatch,
    );
}

#[test]
fn a_retargeted_branch_is_refused() {
    refused(
        &alloc(&loop_spec(), &loop_impl(10, 3, false)),
        ViolationKind::ControlMismatch,
    );
}

/// `s8 = 0; ext(); x2 = 0; for (x1 = 0; x1 < 64; x1++) {}`, then `x2 < 64`
/// decides between returning `s8` and returning 7. After the call only the
/// low half of V8 is known (a widened value, never entry-rooted), and x2's
/// per-edge zeros at the loop head are also that low half's: the head must
/// keep x2 the constant, as the implementation side does, not the low half
/// of V8's block leaf (the false control mismatch of the `s01_fill_f32` and
/// `s02_fill_f64` bridge mains at the frame stage, 2026-10-12).
fn constant_beside_a_widened_loop_value(target_x: u16) -> MachFunction {
    let mut f = func("constant_beside_a_widened_loop_value");
    let b0 = f.entry;
    let head = f.create_block();
    let body = f.create_block();
    let after = f.create_block();
    let small = f.create_block();
    let large = f.create_block();
    push(&mut f, b0, i(Op::Movz, vec![x(32), imm(0)]));
    push(&mut f, b0, i(Op::FmovGprFpr, vec![x(136), x(32)]));
    push(&mut f, b0, call("ext", &[]));
    push(&mut f, b0, i(Op::Movz, vec![x(target_x), imm(0)]));
    push(&mut f, b0, i(Op::Movz, vec![x(1), imm(0)]));
    push(&mut f, b0, i(Op::B, vec![blk(head)]));
    push(&mut f, head, i(Op::CmpRI, vec![x(1), imm(64)]));
    push(&mut f, head, i(Op::BCond, vec![imm(11), blk(body)]));
    push(&mut f, head, i(Op::B, vec![blk(after)]));
    push(&mut f, body, i(Op::AddRI, vec![x(1), x(1), imm(1)]));
    push(&mut f, body, i(Op::B, vec![blk(head)]));
    push(&mut f, after, i(Op::CmpRI, vec![x(target_x), imm(64)]));
    push(&mut f, after, i(Op::BCond, vec![imm(11), blk(small)]));
    push(&mut f, after, i(Op::B, vec![blk(large)]));
    push(&mut f, small, i(Op::FmovFprGpr, vec![x(32), x(136)]));
    push(&mut f, small, ret());
    push(&mut f, large, i(Op::Movz, vec![x(0), imm(7)]));
    push(&mut f, large, ret());
    f
}

#[test]
fn a_loop_invariant_constant_beside_a_widened_value_validates() {
    let f = constant_beside_a_widened_loop_value(2);
    validated(&alloc(&f, &f));
    // The constant moved to another register is the same program.
    validated(&alloc(&f, &constant_beside_a_widened_loop_value(3)));
}

// ---------------------------------------------------------------------------
// Switch dispatch
// ---------------------------------------------------------------------------

fn switch_fn(vregs: bool, swap: bool) -> MachFunction {
    let mut f = func("switch");
    let b0 = f.entry;
    let b1 = f.create_block();
    let b2 = f.create_block();
    let b3 = f.create_block();
    let r = |n: u32, p: u16| if vregs { v(n) } else { x(p) };
    if vregs {
        push(&mut f, b0, i(Op::Copy, vec![v(0), x(0)]));
    }
    push(&mut f, b0, i(Op::CmpRI, vec![r(0, 0), imm(1)]));
    push(&mut f, b0, i(Op::BCond, vec![imm(8), blk(b3)]));
    push(&mut f, b0, i(Op::Adr, vec![r(1, 9), O::JumpTableIndex(0)]));
    push(&mut f, b0, i(Op::LdrswRO, vec![r(2, 10), r(1, 9), r(0, 0)]));
    push(&mut f, b0, i(Op::AddRR, vec![r(3, 9), r(1, 9), r(2, 10)]));
    push(&mut f, b0, i(Op::Br, vec![r(3, 9)]));
    for (b, k) in [(b1, 10), (b2, 20), (b3, 30)] {
        push(&mut f, b, i(Op::Movz, vec![x(0), imm(k)]));
        push(&mut f, b, ret());
    }
    let targets = if swap { vec![b2, b1] } else { vec![b1, b2] };
    f.jump_tables.push(JumpTableData {
        min_val: 0,
        targets,
    });
    f
}

#[test]
fn a_switch_dispatch_validates() {
    validated(&alloc(&switch_fn(true, false), &switch_fn(false, false)));
}

#[test]
fn a_swapped_jump_table_is_refused() {
    refused(
        &alloc(&switch_fn(true, false), &switch_fn(false, true)),
        ViolationKind::ControlMismatch,
    );
}

// ---------------------------------------------------------------------------
// Frame lowering and resolved branches
// ---------------------------------------------------------------------------

/// After allocation: `x1` spilled to allocator slot 0 around a call to
/// `ext(x0)`, then `ext(x0) + x1`.
fn framed_spec() -> MachFunction {
    let mut f = func("framed");
    f.alloc_stack_slot(StackSlot::new(8, 8));
    let b = f.entry;
    push(&mut f, b, spill(i(Op::StrRI, vec![x(1), slot(0)])));
    push(&mut f, b, call("ext", &USES_X0));
    push(&mut f, b, spill(i(Op::LdrRI, vec![x(9), slot(0)])));
    push(&mut f, b, i(Op::AddRR, vec![x(0), x(0), x(9)]));
    push(&mut f, b, ret());
    f
}

/// Slot 0 at CFA-24; FP/LR saved at CFA-16; a 32-byte frame.
fn framed_facts() -> FrameFacts {
    FrameFacts {
        slot_cfa_offsets: vec![Some(-24)],
        slot_sizes: vec![8],
        total_frame_size: 32,
        callee_saved_area_size: 16,
        outgoing_arg_area_size: 0,
    }
}

/// The lowered frame: `stp x29, x30, [sp, #-16]!; mov x29, sp; sub sp,
/// sp, #16`, the slot at `[x29, #-8]` (`reload_offset` for the reload),
/// and the epilogue (without the FP/LR restore when `restore` is false).
fn framed_impl(reload_offset: i64, restore: bool) -> MachFunction {
    let mut f = func("framed");
    f.alloc_stack_slot(StackSlot::new(8, 8));
    let b = f.entry;
    push(
        &mut f,
        b,
        i(Op::StpPreIndex, vec![x(29), x(30), sp(), imm(-16)]),
    );
    push(&mut f, b, i(Op::AddRI, vec![x(29), sp(), imm(0)]));
    push(&mut f, b, i(Op::SubRI, vec![sp(), sp(), imm(16)]));
    push(&mut f, b, spill(i(Op::StrRI, vec![x(1), mem(29, -8)])));
    push(&mut f, b, call("ext", &USES_X0));
    push(
        &mut f,
        b,
        spill(i(Op::LdrRI, vec![x(9), mem(29, reload_offset)])),
    );
    push(&mut f, b, i(Op::AddRR, vec![x(0), x(0), x(9)]));
    push(&mut f, b, i(Op::AddRI, vec![sp(), sp(), imm(16)]));
    if restore {
        push(
            &mut f,
            b,
            i(Op::LdpPostIndex, vec![x(29), x(30), sp(), imm(16)]),
        );
    } else {
        push(&mut f, b, i(Op::AddRI, vec![sp(), sp(), imm(16)]));
    }
    push(&mut f, b, ret());
    f
}

#[test]
fn a_lowered_frame_validates() {
    validated(&frame(
        &framed_spec(),
        &framed_impl(-8, true),
        &framed_facts(),
        0,
    ));
}

#[test]
fn a_frame_offset_off_by_eight_is_refused() {
    refused(
        &frame(&framed_spec(), &framed_impl(-16, true), &framed_facts(), 0),
        ViolationKind::ValueMismatch,
    );
}

#[test]
fn an_unrestored_return_address_is_refused() {
    refused(
        &frame(&framed_spec(), &framed_impl(-8, false), &framed_facts(), 0),
        ViolationKind::FrameMismatch,
    );
}

#[test]
fn overlapping_frame_slots_are_refused() {
    // Two slots the specification names, laid out overlapping.
    let mut spec = framed_spec();
    spec.alloc_stack_slot(StackSlot::new(8, 8));
    let b = spec.entry;
    let store = spec.push_inst(spill(i(Op::StrRI, vec![x(2), slot(1)])));
    spec.blocks[b.0 as usize].insts.insert(0, store);
    let mut facts = framed_facts();
    facts.slot_cfa_offsets = vec![Some(-24), Some(-28)];
    facts.slot_sizes = vec![8, 8];
    refused(
        &frame(&spec, &framed_impl(-8, true), &facts, 0),
        ViolationKind::FrameMismatch,
    );
    // A slot laid out over the callee-save area.
    let mut facts = framed_facts();
    facts.slot_cfa_offsets = vec![Some(-12)];
    refused(
        &frame(&framed_spec(), &framed_impl(-8, true), &facts, 0),
        ViolationKind::FrameMismatch,
    );
    // A program slot no instruction names needs no storage; a slot register
    // allocation created is checked whether or not the specification names
    // it (the composed specification names none).
    let mut facts = framed_facts();
    facts.slot_cfa_offsets.push(Some(8));
    facts.slot_sizes.push(8);
    validated(&frame(
        &local_address_spec(),
        &local_address_impl(8),
        &facts,
        2,
    ));
    refused(
        &frame(&local_address_spec(), &local_address_impl(8), &facts, 1),
        ViolationKind::FrameMismatch,
    );
}

/// `ext(&local)` with `local` a program stack slot.
fn local_address_spec() -> MachFunction {
    let mut f = func("local");
    f.alloc_stack_slot(StackSlot::new(8, 8));
    let b = f.entry;
    push(&mut f, b, i(Op::AddPCRel, vec![x(0), sp(), slot(0)]));
    push(&mut f, b, call("ext", &USES_X0));
    push(&mut f, b, ret());
    f
}

fn local_address_impl(fp_offset: i64) -> MachFunction {
    let mut f = func("local");
    f.alloc_stack_slot(StackSlot::new(8, 8));
    let b = f.entry;
    push(
        &mut f,
        b,
        i(Op::StpPreIndex, vec![x(29), x(30), sp(), imm(-16)]),
    );
    push(&mut f, b, i(Op::AddRI, vec![x(29), sp(), imm(0)]));
    push(&mut f, b, i(Op::SubRI, vec![sp(), sp(), imm(16)]));
    push(&mut f, b, i(Op::SubRI, vec![x(0), x(29), imm(fp_offset)]));
    push(&mut f, b, call("ext", &USES_X0));
    push(&mut f, b, i(Op::AddRI, vec![sp(), sp(), imm(16)]));
    push(
        &mut f,
        b,
        i(Op::LdpPostIndex, vec![x(29), x(30), sp(), imm(16)]),
    );
    push(&mut f, b, ret());
    f
}

#[test]
fn a_frame_slot_address_validates_and_an_offset_shift_is_refused() {
    let facts = framed_facts();
    // The program slot (id 0, below the allocator's first slot 1).
    validated(&frame(
        &local_address_spec(),
        &local_address_impl(8),
        &facts,
        1,
    ));
    refused(
        &frame(&local_address_spec(), &local_address_impl(16), &facts, 1),
        ViolationKind::ValueMismatch,
    );
}

/// The loop after frame lowering and branch resolution: resolved branch
/// immediates in instruction units, laid out `b0 b1 b2 b3`.
fn resolved_loop(taken_offset: i64) -> MachFunction {
    let mut f = func("sum");
    let b0 = f.entry;
    let b1 = f.create_block();
    let b2 = f.create_block();
    let b3 = f.create_block();
    // b0: 0..2, b1: 2..5, b2: 5..8, b3: 8..
    push(&mut f, b0, i(Op::Movz, vec![x(9), imm(0)]));
    push(&mut f, b0, i(Op::Movz, vec![x(10), imm(0)]));
    push(&mut f, b1, i(Op::CmpRR, vec![x(9), x(0)]));
    push(&mut f, b1, i(Op::BCond, vec![imm(3), imm(taken_offset)]));
    push(&mut f, b1, i(Op::B, vec![imm(4)]));
    push(&mut f, b2, i(Op::AddRR, vec![x(10), x(10), x(9)]));
    push(&mut f, b2, i(Op::AddRI, vec![x(9), x(9), imm(1)]));
    push(&mut f, b2, i(Op::B, vec![imm(-5)]));
    push(&mut f, b3, i(Op::MOVXrr, vec![x(0), x(10)]));
    push(&mut f, b3, ret());
    f
}

#[test]
fn resolved_branches_validate_and_a_wrong_displacement_is_refused() {
    let spec = loop_impl(10, 2, false);
    let facts = FrameFacts::default();
    validated(&frame(&spec, &resolved_loop(2), &facts, 0));
    // A relaxation or resolution that lands the taken edge on b3 instead.
    refused(
        &frame(&spec, &resolved_loop(5), &facts, 0),
        ViolationKind::ControlMismatch,
    );
    // A displacement into the middle of a block.
    refused(
        &frame(&spec, &resolved_loop(3), &facts, 0),
        ViolationKind::Structure,
    );
}

#[test]
fn two_register_arguments_reach_a_call() {
    // A call reading x0 and x1 judges both argument values.
    let spec = {
        let mut f = func("args");
        let b = f.entry;
        push(&mut f, b, i(Op::Copy, vec![v(0), x(0)]));
        push(&mut f, b, i(Op::Copy, vec![v(1), x(1)]));
        push(&mut f, b, i(Op::Copy, vec![x(0), v(1)]));
        push(&mut f, b, i(Op::Copy, vec![x(1), v(0)]));
        push(&mut f, b, call("ext2", &USES_X0_X1));
        push(&mut f, b, ret());
        f
    };
    let swap = |through: u16, broken: bool| {
        let mut f = func("args");
        let b = f.entry;
        push(&mut f, b, i(Op::MOVXrr, vec![x(through), x(0)]));
        push(&mut f, b, i(Op::MOVXrr, vec![x(0), x(1)]));
        let src = if broken { 0 } else { through };
        push(&mut f, b, i(Op::MOVXrr, vec![x(1), x(src)]));
        push(&mut f, b, call("ext2", &USES_X0_X1));
        push(&mut f, b, ret());
        f
    };
    validated(&alloc(&spec, &swap(16, false)));
    // The parallel move read as a sequential one (the call-argument clobber
    // class): x1 receives the new x0.
    refused(&alloc(&spec, &swap(16, true)), ViolationKind::ValueMismatch);
}

#[test]
fn x18_is_only_reserved_on_darwin() {
    let report = compare(StageInputs {
        spec: &arith_spec(),
        implementation: &arith_impl(18, 0),
        stage: Stage::Allocation,
        allocator_slot_start: 0,
        frame: None,
        inserted_from: None,
        reserved_x18: false,
    });
    validated(&report);
}

// ---------------------------------------------------------------------------
// Exception edges
// ---------------------------------------------------------------------------

/// `may_throw(x0)`; on unwind the landing pad passes the exception object
/// (X0 from the unwinder) to `__cxa_begin_catch` and returns 7.
fn eh_fn(vregs: bool, pad_reads: u16, with_site: bool) -> MachFunction {
    use trust_cg_ir::function::{EhCallSiteEntry, LandingPadEntry};
    let mut f = func("eh");
    let b0 = f.entry;
    let b1 = f.create_block();
    let b2 = f.create_block();
    if vregs {
        push(&mut f, b0, i(Op::Copy, vec![v(0), x(0)]));
        push(&mut f, b0, i(Op::Copy, vec![x(0), v(0)]));
    }
    push(&mut f, b0, call("may_throw", &USES_X0));
    push(&mut f, b0, i(Op::B, vec![blk(b1)]));
    push(&mut f, b1, ret());
    if vregs {
        push(&mut f, b2, i(Op::MovR, vec![v(2), x(pad_reads)]));
        push(&mut f, b2, i(Op::Copy, vec![x(0), v(2)]));
    } else if pad_reads != 0 {
        push(&mut f, b2, i(Op::MOVXrr, vec![x(0), x(pad_reads)]));
    }
    push(&mut f, b2, call("__cxa_begin_catch", &USES_X0));
    push(&mut f, b2, i(Op::Movz, vec![x(0), imm(7)]));
    push(&mut f, b2, ret());
    f.eh_metadata.personality = Some("__gxx_personality_v0".into());
    f.eh_metadata.add_landing_pad(LandingPadEntry {
        block: b2,
        offset: 0,
        catch_type_indices: vec![0],
        is_cleanup: false,
    });
    if with_site {
        f.eh_metadata.add_call_site(EhCallSiteEntry {
            call_block: b0,
            start_offset: 0,
            length: 0,
            landing_pad_block: Some(b2),
        });
    }
    f
}

#[test]
fn a_landing_pad_reached_by_unwinding_validates() {
    validated(&alloc(&eh_fn(true, 0, true), &eh_fn(false, 0, true)));
}

#[test]
fn a_landing_pad_reading_the_selector_for_the_exception_is_refused() {
    // The pad passes X1 (the selector) where the specification passes X0.
    refused(
        &alloc(&eh_fn(true, 0, true), &eh_fn(false, 1, true)),
        ViolationKind::ValueMismatch,
    );
}

#[test]
fn a_dropped_call_site_is_refused() {
    refused(
        &alloc(&eh_fn(true, 0, true), &eh_fn(false, 0, false)),
        ViolationKind::Structure,
    );
}

// ---------------------------------------------------------------------------
// Address arithmetic: lo12 fusion, register offsets, induction pointers
// ---------------------------------------------------------------------------

/// `return *(u64 *)&g` through `ADRP v0, g; ADD v1, v0, #:lo12:g; LDR v2,
/// [v1]`.
fn global_load_spec() -> MachFunction {
    let mut f = func("global_load");
    let b = f.entry;
    push(&mut f, b, i(Op::Adrp, vec![v(0), O::Symbol("g".into())]));
    push(
        &mut f,
        b,
        i(Op::AddPCRel, vec![v(1), v(0), O::Symbol("g".into())]),
    );
    push(&mut f, b, i(Op::LdrRI, vec![v(2), v(1), imm(0)]));
    push(&mut f, b, i(Op::Copy, vec![x(0), v(2)]));
    push(&mut f, b, ret());
    f
}

/// The late lo12 fusion: `ADRP x0, page; LDR x0, [x0, #:lo12:offset]`.
fn global_load_fused(page: &str, offset: O) -> MachFunction {
    let mut f = func("global_load");
    let b = f.entry;
    push(&mut f, b, i(Op::Adrp, vec![x(0), O::Symbol(page.into())]));
    push(&mut f, b, i(Op::LdrRI, vec![x(0), x(0), offset]));
    push(&mut f, b, ret());
    f
}

#[test]
fn a_fused_lo12_access_validates() {
    validated(&alloc(
        &global_load_spec(),
        &global_load_fused("g", O::Symbol("g".into())),
    ));
}

#[test]
fn a_fused_lo12_access_of_another_symbol_or_without_the_offset_is_refused() {
    refused(
        &alloc(
            &global_load_spec(),
            &global_load_fused("g", O::Symbol("h".into())),
        ),
        ViolationKind::ValueMismatch,
    );
    refused(
        &alloc(&global_load_spec(), &global_load_fused("g", imm(0))),
        ViolationKind::ValueMismatch,
    );
}

#[test]
fn a_symbol_offset_on_both_sides_is_part_of_the_address() {
    // Both functions spell the access `[base, #:lo12:sym]`: the symbol is
    // part of the address, never an ignored operand.
    let spec = |name: &str| {
        let mut f = func("folded");
        let b = f.entry;
        push(&mut f, b, i(Op::Adrp, vec![v(0), O::Symbol("g".into())]));
        push(
            &mut f,
            b,
            i(Op::LdrRI, vec![v(1), v(0), O::Symbol(name.into())]),
        );
        push(&mut f, b, i(Op::Copy, vec![x(0), v(1)]));
        push(&mut f, b, ret());
        f
    };
    validated(&alloc(
        &spec("g"),
        &global_load_fused("g", O::Symbol("g".into())),
    ));
    refused(
        &alloc(&spec("g"), &global_load_fused("g", O::Symbol("h".into()))),
        ViolationKind::ValueMismatch,
    );
    // An operand past the address is outside the model, never skipped.
    let mut extra = global_load_fused("g", O::Symbol("g".into()));
    extra.insts[1].operands.push(imm(8));
    match alloc(&spec("g"), &extra).verdict {
        Verdict::Unmodeled(_) => {}
        other => panic!("expected unmodeled, got {other:?}"),
    }
}

/// `(a + b) + c` against `a + (b + c)`: one affine sum.
#[test]
fn reassociated_sums_validate() {
    let mut spec = func("sum3");
    let b = spec.entry;
    push(&mut spec, b, i(Op::Copy, vec![v(0), x(0)]));
    push(&mut spec, b, i(Op::Copy, vec![v(1), x(1)]));
    push(&mut spec, b, i(Op::Copy, vec![v(2), x(2)]));
    push(&mut spec, b, i(Op::AddRR, vec![v(3), v(0), v(1)]));
    push(&mut spec, b, i(Op::AddRR, vec![v(4), v(3), v(2)]));
    push(&mut spec, b, i(Op::StrRI, vec![v(4), v(0), imm(0)]));
    push(&mut spec, b, ret_void());
    let imp = |shift: i64| {
        let mut f = func("sum3");
        let b = f.entry;
        push(&mut f, b, i(Op::AddRR, vec![x(9), x(1), x(2)]));
        push(
            &mut f,
            b,
            i(Op::AddRRShift, vec![x(9), x(9), x(0), imm(shift)]),
        );
        push(&mut f, b, i(Op::StrRI, vec![x(9), x(0), imm(0)]));
        push(&mut f, b, ret_void());
        f
    };
    // `ADD x9, x9, x0, LSL #0` is `x9 + x0`.
    validated(&alloc(&spec, &imp(0)));
    refused(&alloc(&spec, &imp(1)), ViolationKind::ValueMismatch);
}

/// A chain of twelve adds outgrows the affine cap: past it the adds stay
/// uninterpreted operations, on both sides alike.
#[test]
fn a_long_add_chain_past_the_affine_cap_validates() {
    let mut spec = func("chain");
    let b = spec.entry;
    for k in 0..12u32 {
        push(&mut spec, b, i(Op::Copy, vec![v(k), x(k as u16)]));
    }
    let mut acc = 0u32;
    for k in 1..12u32 {
        push(&mut spec, b, i(Op::AddRR, vec![v(100 + k), v(acc), v(k)]));
        acc = 100 + k;
    }
    push(&mut spec, b, i(Op::StrRI, vec![v(acc), v(0), imm(0)]));
    push(&mut spec, b, ret_void());
    let mut imp = func("chain");
    let b = imp.entry;
    push(&mut imp, b, i(Op::MOVXrr, vec![x(15), x(0)]));
    for k in 1..12u16 {
        push(&mut imp, b, i(Op::AddRR, vec![x(15), x(15), x(k)]));
    }
    push(&mut imp, b, i(Op::StrRI, vec![x(15), x(0), imm(0)]));
    push(&mut imp, b, ret_void());
    validated(&alloc(&spec, &imp));
}

/// `for (i = 0; i < n; i++) acc += a[i]` over 32-bit elements, the access
/// spelled `LDR w, [a, i << 2]` (`LSL` then a register-offset load).
fn indexed_sum_spec() -> MachFunction {
    let mut f = func("indexed_sum");
    let b0 = f.entry;
    let head = f.create_block();
    let body = f.create_block();
    let exit = f.create_block();
    let w = |id: u32| O::VReg(VReg::new(id, RegClass::Gpr32));
    push(&mut f, b0, i(Op::Copy, vec![v(0), x(0)]));
    push(&mut f, b0, i(Op::Copy, vec![v(1), x(1)]));
    push(&mut f, b0, i(Op::Movz, vec![v(2), imm(0)]));
    push(&mut f, b0, i(Op::Movz, vec![v(3), imm(0)]));
    push(&mut f, b0, i(Op::B, vec![blk(head)]));
    push(&mut f, head, i(Op::CmpRR, vec![v(2), v(1)]));
    push(&mut f, head, i(Op::BCond, vec![imm(11), blk(body)]));
    push(&mut f, head, i(Op::B, vec![blk(exit)]));
    push(&mut f, body, i(Op::LslRI, vec![v(4), v(2), imm(2)]));
    push(&mut f, body, i(Op::LdrRO, vec![w(5), v(0), v(4)]));
    push(&mut f, body, i(Op::Sxtw, vec![v(6), w(5)]));
    push(&mut f, body, i(Op::AddRR, vec![v(7), v(3), v(6)]));
    push(&mut f, body, i(Op::AddRI, vec![v(8), v(2), imm(1)]));
    push(&mut f, body, i(Op::MovR, vec![v(3), v(7)]));
    push(&mut f, body, i(Op::MovR, vec![v(2), v(8)]));
    push(&mut f, body, i(Op::B, vec![blk(head)]));
    push(&mut f, exit, i(Op::Copy, vec![x(0), v(3)]));
    push(&mut f, exit, ret());
    f
}

/// The same loop after late post-index formation: a pointer `x16 = base +
/// (i << shift)` seeded before the loop and advanced by `stride` by a
/// post-indexed load.
fn indexed_sum_post_index(base: u16, shift: i64, stride: i64) -> MachFunction {
    let mut f = func("indexed_sum");
    let b0 = f.entry;
    let head = f.create_block();
    let body = f.create_block();
    let exit = f.create_block();
    push(&mut f, b0, i(Op::Movz, vec![x(2), imm(0)]));
    push(&mut f, b0, i(Op::Movz, vec![x(3), imm(0)]));
    push(&mut f, b0, i(Op::LslRI, vec![x(16), x(2), imm(shift)]));
    push(&mut f, b0, i(Op::AddRR, vec![x(16), x(base), x(16)]));
    push(&mut f, b0, i(Op::B, vec![blk(head)]));
    push(&mut f, head, i(Op::CmpRR, vec![x(2), x(1)]));
    push(&mut f, head, i(Op::BCond, vec![imm(11), blk(body)]));
    push(&mut f, head, i(Op::B, vec![blk(exit)]));
    push(
        &mut f,
        body,
        i(Op::LdrPostIndex, vec![x(32 + 5), x(16), imm(stride)]),
    );
    push(&mut f, body, i(Op::Sxtw, vec![x(6), x(32 + 5)]));
    push(&mut f, body, i(Op::AddRR, vec![x(3), x(3), x(6)]));
    push(&mut f, body, i(Op::AddRI, vec![x(2), x(2), imm(1)]));
    push(&mut f, body, i(Op::B, vec![blk(head)]));
    push(&mut f, exit, i(Op::MOVXrr, vec![x(0), x(3)]));
    push(&mut f, exit, ret());
    f
}

#[test]
fn a_late_post_index_pointer_validates() {
    validated(&alloc(
        &indexed_sum_spec(),
        &indexed_sum_post_index(0, 2, 4),
    ));
}

#[test]
fn a_late_post_index_pointer_with_a_wrong_stride_or_base_is_refused() {
    // Advancing 8 bytes per 4-byte element reads every other element.
    refused(
        &alloc(&indexed_sum_spec(), &indexed_sum_post_index(0, 2, 8)),
        ViolationKind::ValueMismatch,
    );
    // Seeded from the bound instead of the base.
    refused(
        &alloc(&indexed_sum_spec(), &indexed_sum_post_index(1, 2, 4)),
        ViolationKind::ValueMismatch,
    );
}

/// An infinite loop entered by falling through an empty entry block: a
/// resolved branch to the loop's own first instruction is that block, not
/// the empty block laid out at the same address.
#[test]
fn a_resolved_self_loop_behind_an_empty_block_validates() {
    let shape = |resolved: bool| {
        let mut f = func("spin");
        let entry = f.entry;
        let spin = f.create_block();
        f.block_order = vec![entry, spin];
        if !resolved {
            push(&mut f, entry, i(Op::B, vec![blk(spin)]));
        }
        let target = if resolved { imm(0) } else { blk(spin) };
        push(&mut f, spin, i(Op::B, vec![target]));
        f.blocks[entry.0 as usize].succs = vec![spin];
        f.blocks[spin.0 as usize].succs = vec![spin];
        f
    };
    validated(&frame(
        &shape(false),
        &shape(true),
        &FrameFacts::default(),
        0,
    ));
}

// ---------------------------------------------------------------------------
// ELF TLS descriptors
// ---------------------------------------------------------------------------

static TLSDESC_DEFS: [PReg; 3] = [X0, X1, X30];
static TLSDESC_USES: [PReg; 2] = [X0, X1];

/// After allocation: `return &tv` through a TLSDESC call (the address is
/// the thread pointer plus the descriptor's result; here the call alone).
fn tlsdesc_spec() -> MachFunction {
    let mut f = func("tls_address");
    let b = f.entry;
    let mut call = i(Op::TlsDescCall, vec![O::Symbol("tv".into())]);
    call.flags = Op::TlsDescCall.default_flags();
    call.implicit_defs = &TLSDESC_DEFS;
    push(&mut f, b, call);
    push(&mut f, b, ret());
    f
}

/// The frame-lowered function with the TLSDESC sequence expanded:
/// `ADRP x0, page; LDR x1, [x0, #:tlsdesc_lo12:slot]; ADD x0, x0,
/// #:tlsdesc_lo12:add; BLR x1`, saving and restoring FP/LR.
fn tlsdesc_impl(page: &str, slot: &str, add: bool) -> MachFunction {
    let mut f = tlsdesc_spec();
    let b = f.entry;
    let call = f.blocks[b.0 as usize].insts[0];
    let ret_id = f.blocks[b.0 as usize].insts[1];
    let save = f.push_inst(i(Op::StpPreIndex, vec![x(29), x(30), sp(), imm(-16)]));
    let fp = f.push_inst(i(Op::AddRI, vec![x(29), sp(), imm(0)]));
    let adrp = f.push_inst(i(Op::Adrp, vec![x(0), O::Symbol(page.into())]));
    let ldr = f.push_inst(i(Op::LdrTlsdesc, vec![x(1), x(0), O::Symbol(slot.into())]));
    let lo12 = f.push_inst(i(
        Op::AddTlsdescLo12,
        vec![x(0), x(0), O::Symbol("tv".into())],
    ));
    let restore = f.push_inst(i(Op::LdpPostIndex, vec![x(29), x(30), sp(), imm(16)]));
    let blr = f.inst_mut(call);
    blr.opcode = Op::BlrTlsdesc;
    blr.flags = Op::BlrTlsdesc.default_flags();
    blr.operands = vec![x(1), O::Symbol("tv".into())];
    blr.implicit_uses = &TLSDESC_USES;
    let mut order = vec![save, fp, adrp, ldr];
    if add {
        order.push(lo12);
    }
    order.extend([call, restore, ret_id]);
    f.blocks[b.0 as usize].insts = order;
    f
}

fn tlsdesc_facts() -> FrameFacts {
    FrameFacts {
        slot_cfa_offsets: Vec::new(),
        slot_sizes: Vec::new(),
        total_frame_size: 16,
        callee_saved_area_size: 16,
        outgoing_arg_area_size: 0,
    }
}

#[test]
fn an_expanded_tlsdesc_call_validates() {
    let spec = tlsdesc_spec();
    validated(&frame(
        &spec,
        &tlsdesc_impl("tv", "tv", true),
        &tlsdesc_facts(),
        0,
    ));
}

#[test]
fn a_tlsdesc_sequence_for_another_symbol_or_without_its_add_is_refused() {
    let spec = tlsdesc_spec();
    for imp in [
        tlsdesc_impl("tv", "other", true),
        tlsdesc_impl("other", "tv", true),
        tlsdesc_impl("tv", "tv", false),
    ] {
        refused(
            &frame(&spec, &imp, &tlsdesc_facts(), 0),
            ViolationKind::EffectMismatch,
        );
    }
}

/// The indexed sum with a diamond inside the loop (`if a[i] != 0 { acc +=
/// a[i] }`): the post-indexed pointer reaches the loop's latch through a
/// join where the index is the same on every edge but not entry-rooted, so
/// the pointer's relation there is to that join's own leaf.
fn guarded_sum(post_index: Option<i64>) -> MachFunction {
    let mut f = func("guarded_sum");
    let b0 = f.entry;
    let head = f.create_block();
    let body = f.create_block();
    let add = f.create_block();
    let skip = f.create_block();
    let latch = f.create_block();
    let exit = f.create_block();
    let w = |id: u32| O::VReg(VReg::new(id, RegClass::Gpr32));
    match post_index {
        None => {
            push(&mut f, b0, i(Op::Copy, vec![v(0), x(0)]));
            push(&mut f, b0, i(Op::Copy, vec![v(1), x(1)]));
            push(&mut f, b0, i(Op::Movz, vec![v(2), imm(0)]));
            push(&mut f, b0, i(Op::Movz, vec![v(3), imm(0)]));
            push(&mut f, b0, i(Op::B, vec![blk(head)]));
            push(&mut f, head, i(Op::CmpRR, vec![v(2), v(1)]));
            push(&mut f, head, i(Op::BCond, vec![imm(11), blk(body)]));
            push(&mut f, head, i(Op::B, vec![blk(exit)]));
            push(&mut f, body, i(Op::LslRI, vec![v(4), v(2), imm(2)]));
            push(&mut f, body, i(Op::LdrRO, vec![w(5), v(0), v(4)]));
            push(&mut f, body, i(Op::Cbz, vec![w(5), blk(skip)]));
            push(&mut f, body, i(Op::B, vec![blk(add)]));
            push(&mut f, add, i(Op::Sxtw, vec![v(6), w(5)]));
            push(&mut f, add, i(Op::AddRR, vec![v(7), v(3), v(6)]));
            push(&mut f, add, i(Op::MovR, vec![v(3), v(7)]));
            push(&mut f, add, i(Op::B, vec![blk(latch)]));
            push(&mut f, skip, i(Op::B, vec![blk(latch)]));
            push(&mut f, latch, i(Op::AddRI, vec![v(8), v(2), imm(1)]));
            push(&mut f, latch, i(Op::MovR, vec![v(2), v(8)]));
            push(&mut f, latch, i(Op::B, vec![blk(head)]));
            push(&mut f, exit, i(Op::Copy, vec![x(0), v(3)]));
        }
        Some(stride) => {
            push(&mut f, b0, i(Op::Movz, vec![x(2), imm(0)]));
            push(&mut f, b0, i(Op::Movz, vec![x(3), imm(0)]));
            push(&mut f, b0, i(Op::LslRI, vec![x(16), x(2), imm(2)]));
            push(&mut f, b0, i(Op::AddRR, vec![x(16), x(0), x(16)]));
            push(&mut f, b0, i(Op::B, vec![blk(head)]));
            push(&mut f, head, i(Op::CmpRR, vec![x(2), x(1)]));
            push(&mut f, head, i(Op::BCond, vec![imm(11), blk(body)]));
            push(&mut f, head, i(Op::B, vec![blk(exit)]));
            push(
                &mut f,
                body,
                i(Op::LdrPostIndex, vec![x(32 + 5), x(16), imm(stride)]),
            );
            push(&mut f, body, i(Op::Cbz, vec![x(32 + 5), blk(skip)]));
            push(&mut f, body, i(Op::B, vec![blk(add)]));
            push(&mut f, add, i(Op::Sxtw, vec![x(6), x(32 + 5)]));
            push(&mut f, add, i(Op::AddRR, vec![x(3), x(3), x(6)]));
            push(&mut f, add, i(Op::B, vec![blk(latch)]));
            push(&mut f, skip, i(Op::B, vec![blk(latch)]));
            push(&mut f, latch, i(Op::AddRI, vec![x(2), x(2), imm(1)]));
            push(&mut f, latch, i(Op::B, vec![blk(head)]));
            push(&mut f, exit, i(Op::MOVXrr, vec![x(0), x(3)]));
        }
    }
    push(&mut f, exit, ret());
    f
}

#[test]
fn a_post_index_pointer_through_a_join_inside_the_loop_validates() {
    validated(&alloc(&guarded_sum(None), &guarded_sum(Some(4))));
    refused(
        &alloc(&guarded_sum(None), &guarded_sum(Some(8))),
        ViolationKind::ValueMismatch,
    );
}

/// `x0 == 0 ? 1 : 2` where the implementation branches past an anchor it
/// left empty (laid out right before the block it falls into): the two
/// targets are one program point of the implementation.
#[test]
fn a_branch_past_an_empty_anchor_validates() {
    let shape = |bypass: bool, empty: bool| {
        let mut f = func("pick");
        let b0 = f.entry;
        let e = f.create_block();
        let t = f.create_block();
        let other = f.create_block();
        f.block_order = vec![b0, e, t, other];
        push(&mut f, b0, i(Op::CmpRI, vec![x(0), imm(0)]));
        let target = if bypass { t } else { e };
        push(&mut f, b0, i(Op::BCond, vec![imm(0), blk(target)]));
        push(&mut f, b0, i(Op::B, vec![blk(other)]));
        if !empty {
            push(&mut f, e, i(Op::B, vec![blk(t)]));
        }
        push(&mut f, t, i(Op::Movz, vec![x(0), imm(1)]));
        push(&mut f, t, ret());
        push(&mut f, other, i(Op::Movz, vec![x(0), imm(2)]));
        push(&mut f, other, ret());
        f
    };
    validated(&alloc(&shape(false, false), &shape(true, true)));
    // An anchor the implementation does not leave empty is not bypassed.
    let mut busy = shape(true, true);
    let e = BlockId(1);
    push(&mut busy, e, i(Op::Movz, vec![x(0), imm(3)]));
    refused(
        &alloc(&shape(false, false), &busy),
        ViolationKind::ControlMismatch,
    );
}

// ---------------------------------------------------------------------------
// SP at calls, private frame storage, clobbered registers
// ---------------------------------------------------------------------------

/// `framed_impl` with SP lowered by `delta` bytes from just before the call
/// to just after it (a callee then finds its stack arguments `delta` bytes
/// below where the caller stored them).
fn framed_impl_sp_moved(delta: i64) -> MachFunction {
    let mut f = framed_impl(-8, true);
    let b = f.entry;
    let call_at = f.blocks[b.0 as usize]
        .insts
        .iter()
        .position(|&id| f.inst(id).opcode == Op::Bl)
        .expect("the call");
    let lower = f.push_inst(i(Op::SubRI, vec![sp(), sp(), imm(delta)]));
    let raise = f.push_inst(i(Op::AddRI, vec![sp(), sp(), imm(delta)]));
    f.blocks[b.0 as usize].insts.insert(call_at + 1, raise);
    f.blocks[b.0 as usize].insts.insert(call_at, lower);
    f
}

#[test]
fn sp_moved_around_a_call_is_refused() {
    // SP is restored before the exit, so only the call sees the moved SP.
    for delta in [16, 8] {
        refused(
            &frame(
                &framed_spec(),
                &framed_impl_sp_moved(delta),
                &framed_facts(),
                0,
            ),
            ViolationKind::ValueMismatch,
        );
    }
    // Before frame lowering: a call and an exit both read SP.
    let mut moved = call_impl_in(19);
    let b = moved.entry;
    let lower = moved.push_inst(i(Op::SubRI, vec![sp(), sp(), imm(16)]));
    moved.blocks[b.0 as usize].insts.insert(1, lower);
    let raise = moved.push_inst(i(Op::AddRI, vec![sp(), sp(), imm(16)]));
    moved.blocks[b.0 as usize].insts.insert(3, raise);
    refused(&alloc(&call_spec(), &moved), ViolationKind::ValueMismatch);
    let mut unrestored = call_impl_in(19);
    let lower = unrestored.push_inst(i(Op::SubRI, vec![sp(), sp(), imm(16)]));
    unrestored.blocks[b.0 as usize].insts.insert(3, lower);
    refused(
        &alloc(&call_spec(), &unrestored),
        ViolationKind::ValueMismatch,
    );
}

/// After allocation: `local = x2` (program slot 0), `x1` spilled to
/// allocator slot 1 around `ext(x0)`, then `ext(x0) + x1 + local`.
fn private_spec() -> MachFunction {
    let mut f = func("private");
    f.alloc_stack_slot(StackSlot::new(8, 8));
    f.alloc_stack_slot(StackSlot::new(8, 8));
    let b = f.entry;
    push(&mut f, b, i(Op::StrRI, vec![x(2), slot(0)]));
    push(&mut f, b, spill(i(Op::StrRI, vec![x(1), slot(1)])));
    push(&mut f, b, call("ext", &USES_X0));
    push(&mut f, b, spill(i(Op::LdrRI, vec![x(9), slot(1)])));
    push(&mut f, b, i(Op::LdrRI, vec![x(10), slot(0)]));
    push(&mut f, b, i(Op::AddRR, vec![x(0), x(0), x(9)]));
    push(&mut f, b, i(Op::AddRR, vec![x(0), x(0), x(10)]));
    push(&mut f, b, ret());
    f
}

/// Program slot 0 at CFA-32, spill slot 1 at CFA-24, FP/LR at CFA-16.
fn private_facts() -> FrameFacts {
    FrameFacts {
        slot_cfa_offsets: vec![Some(-32), Some(-24)],
        slot_sizes: vec![8, 8],
        total_frame_size: 32,
        callee_saved_area_size: 16,
        outgoing_arg_area_size: 0,
    }
}

/// The lowered frame with the spill store and reload at `[x29, #spill]`
/// (CFA - 16 + `spill`) and the program slot at `[x29, #-16]`; `probe`
/// adds frame lowering's `STR XZR, [SP]` after the SP adjustment.
fn private_impl(spill_at: i64, probe: bool) -> MachFunction {
    let mut f = func("private");
    f.alloc_stack_slot(StackSlot::new(8, 8));
    f.alloc_stack_slot(StackSlot::new(8, 8));
    let b = f.entry;
    // The body keeps the specification's instruction ids (0..8); frame
    // lowering's instructions are appended after them.
    let body = [
        i(Op::StrRI, vec![x(2), mem(29, -16)]),
        spill(i(Op::StrRI, vec![x(1), mem(29, spill_at)])),
        call("ext", &USES_X0),
        spill(i(Op::LdrRI, vec![x(9), mem(29, spill_at)])),
        i(Op::LdrRI, vec![x(10), mem(29, -16)]),
        i(Op::AddRR, vec![x(0), x(0), x(9)]),
        i(Op::AddRR, vec![x(0), x(0), x(10)]),
        ret(),
    ];
    let body: Vec<InstId> = body.into_iter().map(|inst| f.push_inst(inst)).collect();
    let mut prologue = vec![
        f.push_inst(i(Op::StpPreIndex, vec![x(29), x(30), sp(), imm(-16)])),
        f.push_inst(i(Op::AddRI, vec![x(29), sp(), imm(0)])),
        f.push_inst(i(Op::SubRI, vec![sp(), sp(), imm(16)])),
    ];
    if probe {
        prologue.push(f.push_inst(i(Op::StrRI, vec![O::Special(SpecialReg::XZR), sp()])));
    }
    let epilogue = [
        f.push_inst(i(Op::AddRI, vec![sp(), sp(), imm(16)])),
        f.push_inst(i(Op::LdpPostIndex, vec![x(29), x(30), sp(), imm(16)])),
    ];
    let mut insts = prologue;
    insts.extend_from_slice(&body[..7]);
    insts.extend_from_slice(&epilogue);
    insts.push(body[7]);
    f.blocks[b.0 as usize].insts = insts;
    f
}

#[test]
fn spill_storage_on_a_program_slot_is_refused() {
    let facts = private_facts();
    validated(&frame(&private_spec(), &private_impl(-8, false), &facts, 1));
    // A spill slot moved by eight, consistently (store and reload), onto
    // the program slot: the reload still reads what the spill stored, but
    // the store overwrote the program's value.
    refused(
        &frame(&private_spec(), &private_impl(-16, false), &facts, 1),
        ViolationKind::FrameMismatch,
    );
    // Storage in the caller's frame.
    refused(
        &frame(&private_spec(), &private_impl(16, false), &facts, 1),
        ViolationKind::FrameMismatch,
    );
    // Frame lowering's stack probe of the new SP may touch a program slot.
    validated(&frame(&private_spec(), &private_impl(-8, true), &facts, 1));
}

#[test]
fn a_stack_probe_after_a_program_store_is_not_exempt() {
    // The probe at the post-prologue SP (program slot 0, CFA-32) placed
    // after the body's store to that slot zeroes the program's value; the
    // load after it still matches the specification's load, so only the
    // probe's own privacy check can see it.
    let facts = private_facts();
    let mut corrupted = private_impl(-8, false);
    let b = corrupted.entry;
    let probe = corrupted.push_inst(i(Op::StrRI, vec![O::Special(SpecialReg::XZR), sp()]));
    let at = corrupted.blocks[b.0 as usize]
        .insts
        .iter()
        .position(|&id| id == InstId(0))
        .expect("the program store");
    corrupted.blocks[b.0 as usize].insts.insert(at + 1, probe);
    refused(
        &frame(&private_spec(), &corrupted, &facts, 1),
        ViolationKind::FrameMismatch,
    );
}

/// After allocation: `x1` spilled to allocator slot 0, `ext(x0)` called with
/// `x2` as its stack-passed argument at `[sp]`, then `ext(x0) + x1`.
fn outgoing_spec() -> MachFunction {
    let mut f = func("outgoing");
    f.alloc_stack_slot(StackSlot::new(8, 8));
    let b = f.entry;
    push(&mut f, b, spill(i(Op::StrRI, vec![x(1), slot(0)])));
    push(&mut f, b, i(Op::StrRI, vec![x(2), sp(), imm(0)]));
    push(&mut f, b, call("ext", &USES_X0));
    push(&mut f, b, spill(i(Op::LdrRI, vec![x(9), slot(0)])));
    push(&mut f, b, i(Op::AddRR, vec![x(0), x(0), x(9)]));
    push(&mut f, b, ret());
    f
}

/// Spill slot 0 at CFA-24, FP/LR at CFA-16, a 16-byte outgoing-argument
/// area at the bottom of a 48-byte frame: `[CFA-48, CFA-32)`.
fn outgoing_facts() -> FrameFacts {
    FrameFacts {
        slot_cfa_offsets: vec![Some(-24)],
        slot_sizes: vec![8],
        total_frame_size: 48,
        callee_saved_area_size: 16,
        outgoing_arg_area_size: 16,
    }
}

/// The lowered frame of [`outgoing_spec`] with the spill store and reload
/// at `[x29, #spill]` (CFA - 16 + `spill`) or, with `spill_sp`, at `[sp,
/// #spill_sp]`; `probe` adds frame lowering's `STR XZR, [SP]` after the SP
/// adjustment; `extra` is inserted between the stack-argument store and the
/// call.
fn outgoing_impl(
    spill_at: i64,
    spill_sp: Option<i64>,
    probe: bool,
    extra: Option<MachInst>,
) -> MachFunction {
    let mut f = func("outgoing");
    f.alloc_stack_slot(StackSlot::new(8, 8));
    let b = f.entry;
    let spill_mem = |reg: u16| match spill_sp {
        Some(off) => vec![x(reg), sp(), imm(off)],
        None => vec![x(reg), mem(29, spill_at)],
    };
    // The body keeps the specification's instruction ids (0..6).
    let body = [
        spill(i(Op::StrRI, spill_mem(1))),
        i(Op::StrRI, vec![x(2), sp(), imm(0)]),
        call("ext", &USES_X0),
        spill(i(Op::LdrRI, spill_mem(9))),
        i(Op::AddRR, vec![x(0), x(0), x(9)]),
        ret(),
    ];
    let body: Vec<InstId> = body.into_iter().map(|inst| f.push_inst(inst)).collect();
    let mut insts = vec![
        f.push_inst(i(Op::StpPreIndex, vec![x(29), x(30), sp(), imm(-16)])),
        f.push_inst(i(Op::AddRI, vec![x(29), sp(), imm(0)])),
        f.push_inst(i(Op::SubRI, vec![sp(), sp(), imm(32)])),
    ];
    if probe {
        insts.push(f.push_inst(i(Op::StrRI, vec![O::Special(SpecialReg::XZR), sp()])));
    }
    insts.extend_from_slice(&body[..2]);
    if let Some(extra) = extra {
        insts.push(f.push_inst(extra));
    }
    insts.extend_from_slice(&body[2..5]);
    insts.push(f.push_inst(i(Op::AddRI, vec![sp(), sp(), imm(32)])));
    insts.push(f.push_inst(i(Op::LdpPostIndex, vec![x(29), x(30), sp(), imm(16)])));
    insts.push(body[5]);
    f.blocks[b.0 as usize].insts = insts;
    f
}

#[test]
fn storage_on_the_outgoing_argument_area_is_refused() {
    let facts = outgoing_facts();
    let check = |implementation: &MachFunction| frame(&outgoing_spec(), implementation, &facts, 0);
    validated(&check(&outgoing_impl(-8, None, false, None)));
    // Frame lowering's probe of the new SP lands on the outgoing area
    // before anything has written there.
    validated(&check(&outgoing_impl(-8, None, true, None)));
    // Between the stack-argument store and the call, a spill store over the
    // argument (the callee reads the spill's value), an inserted store of
    // zero at SP (shaped like a probe, but after the program wrote there)
    // and a spill store into the area's other word: each changes what the
    // callee may read, and none is a program effect.
    for extra in [
        spill(i(Op::StrRI, vec![x(3), sp(), imm(0)])),
        i(Op::StrRI, vec![O::Special(SpecialReg::XZR), sp(), imm(0)]),
        i(Op::StrRI, vec![x(3), sp(), imm(0)]),
        spill(i(Op::StrRI, vec![x(3), sp(), imm(8)])),
    ] {
        refused(
            &check(&outgoing_impl(-8, None, false, Some(extra))),
            ViolationKind::FrameMismatch,
        );
    }
    // The spill slot moved, consistently, onto the outgoing area: the
    // reload still reads what the spill stored, but the callee owns its
    // incoming argument area and may overwrite it during the call.
    for at in [0, 8] {
        refused(
            &check(&outgoing_impl(-8, Some(at), false, None)),
            ViolationKind::FrameMismatch,
        );
    }
}

/// `*slot0 = x2; return *slot0` over an 8 KiB program slot at the bottom of
/// the frame; the lowered frame allocates it with a counted probe loop (two
/// 4 KiB steps) in its own block, and `store_first` runs the program store
/// before the loop instead of after it.
fn probe_loop_pair(store_first: bool) -> (MachFunction, MachFunction, FrameFacts) {
    let mut spec = func("probed");
    spec.alloc_stack_slot(StackSlot::new(8192, 16));
    let b = spec.entry;
    push(&mut spec, b, i(Op::StrRI, vec![x(2), slot(0)]));
    push(&mut spec, b, i(Op::LdrRI, vec![x(0), slot(0)]));
    push(&mut spec, b, ret());

    let mut f = func("probed");
    f.alloc_stack_slot(StackSlot::new(8192, 16));
    let b0 = f.entry;
    let b1 = f.create_block();
    let b2 = f.create_block();
    let store = f.push_inst(i(Op::StrRI, vec![x(2), mem(29, -8192)]));
    let load = f.push_inst(i(Op::LdrRI, vec![x(0), mem(29, -8192)]));
    let exit = f.push_inst(ret());
    let mut head = vec![
        f.push_inst(i(Op::StpPreIndex, vec![x(29), x(30), sp(), imm(-16)])),
        f.push_inst(i(Op::AddRI, vec![x(29), sp(), imm(0)])),
        f.push_inst(i(Op::Movz, vec![x(16), imm(2)])),
    ];
    let looped = vec![
        f.push_inst(i(Op::SubRI, vec![sp(), sp(), imm(4096)])),
        f.push_inst(i(Op::StrRI, vec![x(160), sp(), imm(0)])),
        f.push_inst(i(Op::SubsRI, vec![x(16), x(16), imm(1)])),
        f.push_inst(i(Op::BCond, vec![imm(1), blk(b1)])),
    ];
    let mut tail = Vec::new();
    if store_first {
        head.push(store);
    } else {
        tail.push(store);
    }
    tail.push(load);
    tail.push(f.push_inst(i(Op::AddRI, vec![sp(), sp(), imm(4096)])));
    tail.push(f.push_inst(i(Op::AddRI, vec![sp(), sp(), imm(4096)])));
    tail.push(f.push_inst(i(Op::LdpPostIndex, vec![x(29), x(30), sp(), imm(16)])));
    tail.push(exit);
    f.blocks[b0.0 as usize].insts = head;
    f.blocks[b1.0 as usize].insts = looped;
    f.blocks[b2.0 as usize].insts = tail;
    let facts = FrameFacts {
        slot_cfa_offsets: vec![Some(-8208)],
        slot_sizes: vec![8192],
        total_frame_size: 8208,
        callee_saved_area_size: 16,
        outgoing_arg_area_size: 0,
    };
    (spec, f, facts)
}

#[test]
fn a_stack_probe_loop_over_written_memory_is_refused() {
    let (spec, implementation, facts) = probe_loop_pair(false);
    validated(&frame(&spec, &implementation, &facts, 1));
    // The loop run after the program's store zeroes it (the last probe is
    // at CFA-8208); the load still matches the specification's load.
    let (spec, implementation, facts) = probe_loop_pair(true);
    refused(
        &frame(&spec, &implementation, &facts, 1),
        ViolationKind::FrameMismatch,
    );
}

#[test]
fn the_composed_comparison_checks_allocator_slots_and_private_storage() {
    // The function entering allocation: the program slot only.
    let spec = {
        let mut f = func("private");
        f.alloc_stack_slot(StackSlot::new(8, 8));
        let b = f.entry;
        push(&mut f, b, i(Op::Copy, vec![v(0), x(0)]));
        push(&mut f, b, i(Op::Copy, vec![v(1), x(1)]));
        push(&mut f, b, i(Op::Copy, vec![v(2), x(2)]));
        push(&mut f, b, i(Op::StrRI, vec![v(2), slot(0)]));
        push(&mut f, b, i(Op::Copy, vec![x(0), v(0)]));
        push(&mut f, b, call("ext", &USES_X0));
        push(&mut f, b, i(Op::Copy, vec![v(3), x(0)]));
        push(&mut f, b, i(Op::LdrRI, vec![v(4), slot(0)]));
        push(&mut f, b, i(Op::AddRR, vec![v(5), v(3), v(1)]));
        push(&mut f, b, i(Op::AddRR, vec![v(6), v(5), v(4)]));
        push(&mut f, b, i(Op::Copy, vec![x(0), v(6)]));
        push(&mut f, b, ret());
        f
    };
    let composed = |implementation: &MachFunction, facts: &FrameFacts| {
        compare(StageInputs {
            spec: &spec,
            implementation,
            stage: Stage::Composed,
            allocator_slot_start: 1,
            frame: Some(facts),
            inserted_from: Some(8),
            reserved_x18: true,
        })
    };
    let facts = private_facts();
    validated(&composed(&private_impl(-8, false), &facts));
    refused(
        &composed(&private_impl(-16, false), &facts),
        ViolationKind::FrameMismatch,
    );
    // The allocator's slot laid out over the program slot: the composed
    // specification names no allocator slot, its offset is checked anyway.
    let mut overlapping = private_facts();
    overlapping.slot_cfa_offsets[1] = Some(-28);
    refused(
        &composed(&private_impl(-8, false), &overlapping),
        ViolationKind::FrameMismatch,
    );
}

/// `call_impl_in(19)` with a branch on `x9 == x10` after the call to a block
/// returning 7, in the body (`terminator` false) or as the terminator;
/// `rhs` names the register compared with x9.
fn clobber_compare_impl(terminator: bool, rhs: u16) -> MachFunction {
    let mut f = func("callsum");
    let b = f.entry;
    let seven = f.create_block();
    push(&mut f, b, i(Op::MOVXrr, vec![x(19), x(1)]));
    push(&mut f, b, call("ext", &USES_X0));
    if !terminator {
        push(&mut f, b, i(Op::CmpRR, vec![x(9), x(rhs)]));
        push(&mut f, b, i(Op::BCond, vec![imm(1), blk(seven)]));
    }
    push(&mut f, b, i(Op::AddRR, vec![x(0), x(0), x(19)]));
    if terminator {
        push(&mut f, b, i(Op::CmpRR, vec![x(9), x(rhs)]));
        push(&mut f, b, i(Op::BCond, vec![imm(1), blk(seven)]));
    }
    push(&mut f, b, ret());
    push(&mut f, seven, i(Op::Movz, vec![x(0), imm(7)]));
    push(&mut f, seven, ret());
    if !f.block_order.contains(&seven) {
        f.block_order.push(seven);
    }
    f
}

#[test]
fn a_compare_of_two_clobbered_registers_decides_nothing() {
    // Each caller-saved register holds its own unknown after the call: the
    // compare of x9 with x10 is not "equal", so the branch to the block
    // returning 7 is a path the specification does not have (an early exit
    // with no counterpart, or an exit returning 7), as it is for x9 against
    // x19.
    for (terminator, kind) in [
        (false, ViolationKind::ControlMismatch),
        (true, ViolationKind::ValueMismatch),
    ] {
        for rhs in [10, 19] {
            refused(
                &alloc(&call_spec(), &clobber_compare_impl(terminator, rhs)),
                kind,
            );
        }
    }
}

#[test]
fn a_spill_below_sp_does_not_survive_a_call() {
    // The spill store and reload agree on a cell 8 bytes below SP: the
    // callee's frame starts at SP and overwrites it.
    let mut below = framed_impl(-24, true);
    let store = below.blocks[0]
        .insts
        .iter()
        .copied()
        .find(|&id| below.inst(id).opcode == Op::StrRI)
        .expect("the spill store");
    below.inst_mut(store).operands[1] = mem(29, -24);
    refused(
        &frame(&framed_spec(), &below, &framed_facts(), 0),
        ViolationKind::ValueMismatch,
    );
}
