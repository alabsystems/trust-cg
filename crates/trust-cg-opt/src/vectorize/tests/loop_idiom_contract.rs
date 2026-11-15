// trust-cg-opt - Loop-idiom admission tests for the vectorizer's CFG rewrites
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Differential and admission tests for the i32 induction-store rewrite and
//! the reverse-accumulation rewrite.
//!
//! Each rewrite is run through its own driver (the functions the production
//! pass calls), and both the scalar fixture and the rewritten function are
//! executed by `mach_interp` on the same inputs. A test passes only when the
//! rewritten function returns with the scalar function's memory and observed
//! registers; the interpreter fails outright on an undefined register or an
//! unmapped access. Fixtures that are *not* the idiom — but that an
//! instruction-membership check admits — must be declined, and where their
//! scalar semantics terminate the differential run shows what a rewrite
//! would have done to them.

use std::collections::HashMap;

use super::mach_interp::{self, MachState, Region};
use super::*;

const STEP_BUDGET: usize = 200_000;
const ARRAY_START: u64 = 0x1000_0000;
const SRC_START: u64 = 0x2000_0000;
const DST_START: u64 = 0x3000_0000;
const COUNTER_START: u64 = 0x4000_0000;
/// Unmapped address used for a stale register value.
const STALE_POINTER: u128 = 0xDEAD_0000;
/// Mapped i32 guard elements on each side of an array.
const GUARD: i64 = 8;

fn v32(id: u32) -> VReg {
    VReg::new(id, RegClass::Gpr32)
}

fn v64(id: u32) -> VReg {
    VReg::new(id, RegClass::Gpr64)
}

fn inst(opcode: AArch64Opcode, operands: Vec<MachOperand>) -> MachInst {
    MachInst::new(opcode, operands)
}

fn reg(vreg: VReg) -> MachOperand {
    MachOperand::VReg(vreg)
}

fn only_loop(func: &MachFunction) -> NaturalLoop {
    let dom = DomTree::compute(func);
    let loops = LoopAnalysis::compute(func, &dom);
    let mut all = loops.all_loops().cloned();
    let lp = all.next().expect("fixture has a loop");
    assert!(all.next().is_none(), "fixture has exactly one loop");
    lp
}

/// Run `original` and `rewritten` on `state`; require equal memory and equal
/// `observed` registers, and require the rewritten function to run wherever
/// the scalar one does.
fn assert_refines(
    original: &MachFunction,
    rewritten: &MachFunction,
    state: &MachState,
    observed: &[VReg],
    label: &str,
) {
    let expected = mach_interp::run(original, state.clone(), STEP_BUDGET)
        .unwrap_or_else(|err| panic!("{label}: the scalar fixture itself must run: {err}"));
    let actual = mach_interp::run(rewritten, state.clone(), STEP_BUDGET).unwrap_or_else(|err| {
        panic!("{label}: the rewritten loop fails where the scalar loop runs: {err}")
    });
    for (want, got) in expected.regions.iter().zip(&actual.regions) {
        assert_eq!(
            got.read_i32s(),
            want.read_i32s(),
            "{label}: memory at {:#x} differs from the scalar loop",
            want.start
        );
    }
    for &vreg in observed {
        assert_eq!(
            actual.reg(vreg),
            expected.reg(vreg),
            "{label}: v{} differs from the scalar loop",
            vreg.id
        );
    }
}

fn append_to_block(func: &mut MachFunction, block: BlockId, new: MachInst) -> InstId {
    let id = func.push_inst(new);
    func.append_inst(block, id);
    id
}

fn insert_in_block(func: &mut MachFunction, block: BlockId, at: usize, new: MachInst) -> InstId {
    let id = func.push_inst(new);
    func.block_mut(block).insts.insert(at, id);
    id
}

/// Retarget the header's exit branch into the loop and keep the CFG edges in
/// step with it.
fn retarget_exit_into_loop(
    func: &mut MachFunction,
    header: BlockId,
    exit: BlockId,
    target: BlockId,
) {
    let exit_branch = *func.block(header).insts.last().expect("header branch");
    assert_eq!(branch_target(func.inst(exit_branch)), Some(exit));
    func.inst_mut(exit_branch).operands = vec![MachOperand::Block(target)];
    remove_cfg_edge(func, header, exit);
    func.add_edge(header, target);
}

/// Retarget the header's exit branch to the body its loop test enters. Both
/// header branches then name the body, and the CFG keeps its one header ->
/// body edge, so every edge list the shape check compares stays exact.
fn retarget_exit_to_body(func: &mut MachFunction, header: BlockId, exit: BlockId, body: BlockId) {
    let exit_branch = *func.block(header).insts.last().expect("header branch");
    assert_eq!(branch_target(func.inst(exit_branch)), Some(exit));
    func.inst_mut(exit_branch).operands = vec![MachOperand::Block(body)];
    remove_cfg_edge(func, header, exit);
    assert_eq!(func.block(header).succs, [body]);
}

/// A block after everything else in the layout, which no edge reaches, that
/// defines `vreg` as `value`. The shared def map is last-wins over the
/// layout, so it names this definition, while the loop only ever sees the
/// reachable one.
fn append_unreachable_constant(func: &mut MachFunction, vreg: VReg, value: i64) {
    let block = func.create_block();
    append_to_block(
        func,
        block,
        inst(
            AArch64Opcode::Movz,
            vec![reg(vreg), MachOperand::Imm(value)],
        ),
    );
    append_to_block(func, block, inst(AArch64Opcode::Ret, vec![]));
}

// ---------------------------------------------------------------------------
// i32 induction store: `for (i = entry; i < bound; i++) a[i] = i + 1`
// ---------------------------------------------------------------------------

const I32_STORE_HEADER: BlockId = BlockId(1);
const I32_STORE_BODY: BlockId = BlockId(2);
const I32_STORE_EXIT: BlockId = BlockId(3);
const I32_STORE_LATCH: BlockId = BlockId(4);

/// Store-loop fixtures seed `v0 = 0` in the preheader; drop that constant so
/// each scenario supplies its own entry index.
fn i32_store_fixture(mut func: MachFunction) -> MachFunction {
    let entry = func.entry;
    let seed = func
        .block(entry)
        .insts
        .iter()
        .copied()
        .find(|&inst_id| movz_i32_imm(func.inst(inst_id)).is_some_and(|(dst, _)| dst == v32(0)))
        .expect("entry index constant");
    func.block_mut(entry)
        .insts
        .retain(|&inst_id| inst_id != seed);
    func
}

/// The array base that puts `a[entry]` just past the leading guard.
fn i32_store_base(entry: i32) -> u128 {
    let first = ARRAY_START + GUARD as u64 * 4;
    u128::from(first.wrapping_sub((i64::from(entry) * 4) as u64))
}

/// `a[entry - GUARD .. max(entry, bound) + GUARD]` mapped with a pattern,
/// plus the stack frame, with `v0 = entry`, `v1 = bound`, `v6 = base`.
fn i32_store_state(entry: i32, bound: i32) -> MachState {
    let trip = (i64::from(bound) - i64::from(entry)).max(0);
    let values: Vec<i32> = (0..trip + 2 * GUARD)
        .map(|k| 0x5A00_0000 | k as i32)
        .collect();
    MachState::new(vec![Region::i32s(ARRAY_START, &values), Region::frame(1)])
        .with_reg(v32(0), u128::from(entry as u32))
        .with_reg(v32(1), u128::from(bound as u32))
        .with_reg(v64(6), i32_store_base(entry))
}

const ZERO_ENTRY_RANGES: &[(i32, i32)] = &[
    (0, 0),
    (0, 1),
    (0, 3),
    (0, 4),
    (0, 5),
    (0, 8),
    (0, 9),
    (0, 17),
];
const NONZERO_ENTRY_RANGES: &[(i32, i32)] = &[
    (1, 9),
    (4, 8),
    (5, 23),
    (-3, 9),
    (-9, -1),
    (100, 117),
    (7, 3),
];
const I32_EDGE_RANGES: &[(i32, i32)] = &[
    (i32::MAX - 1, i32::MAX),
    (i32::MAX - 2, i32::MAX),
    (i32::MAX - 3, i32::MAX),
    (i32::MAX - 4, i32::MAX),
    (i32::MAX - 8, i32::MAX - 1),
    (i32::MIN, i32::MIN + 9),
];

fn rewrite_i32_store_loops(func: &MachFunction) -> (MachFunction, usize) {
    let mut rewritten = func.clone();
    let dom = DomTree::compute(&rewritten);
    let loops = LoopAnalysis::compute(&rewritten, &dom);
    let mut maps = VecMaps::build(&rewritten);
    let count = rewrite_i32_induction_store_loops(&mut rewritten, &loops, None, &mut maps).len();
    (rewritten, count)
}

fn i32_store_matches(func: &MachFunction) -> bool {
    match_i32_induction_store_loop(func, &only_loop(func), &build_def_map(func)).is_some()
}

fn assert_i32_store_rewrite_refines(
    func: &MachFunction,
    ranges: &[(i32, i32)],
    state_for: impl Fn(i32, i32) -> MachState,
    observed: &[VReg],
) {
    let (rewritten, count) = rewrite_i32_store_loops(func);
    assert_eq!(count, 1, "the fixture is the i32 induction-store idiom");
    for &(entry, bound) in ranges {
        assert_refines(
            func,
            &rewritten,
            &state_for(entry, bound),
            observed,
            &format!("a[{entry}..{bound}]"),
        );
    }
}

/// A loop that is not the idiom must stay scalar. Any rewrite that did fire
/// is first run against the scalar loop, so a failure shows its effect.
fn assert_i32_store_declined(
    func: &MachFunction,
    ranges: &[(i32, i32)],
    state_for: impl Fn(i32, i32) -> MachState,
    observed: &[VReg],
) {
    let (rewritten, count) = rewrite_i32_store_loops(func);
    for &(entry, bound) in ranges {
        assert_refines(
            func,
            &rewritten,
            &state_for(entry, bound),
            observed,
            &format!("a[{entry}..{bound}]"),
        );
    }
    assert_eq!(count, 0, "a loop that is not the idiom must stay scalar");
    assert!(!i32_store_matches(func));
}

#[test]
fn i32_induction_store_rewrite_matches_scalar_from_zero_entry() {
    let func = i32_store_fixture(make_imported_o0_i32_induction_store_loop());
    assert_i32_store_rewrite_refines(&func, ZERO_ENTRY_RANGES, i32_store_state, &[v32(0)]);
}

/// `for i in 4..8 { a[i] = i + 1 }` must store `a[4..8]`: the vector stores
/// start at the entry index, not at `a[0]`.
#[test]
fn i32_induction_store_rewrite_matches_scalar_from_nonzero_entry() {
    let func = i32_store_fixture(make_imported_o0_i32_induction_store_loop());
    assert_i32_store_rewrite_refines(&func, NONZERO_ENTRY_RANGES, i32_store_state, &[v32(0)]);
}

/// `index + 3 < bound` must not wrap: entry `i32::MAX - 1` with bound
/// `i32::MAX` is one scalar iteration, never a four-lane store.
#[test]
fn i32_induction_store_rewrite_matches_scalar_near_i32_max() {
    let func = i32_store_fixture(make_imported_o0_i32_induction_store_loop());
    assert_i32_store_rewrite_refines(&func, I32_EDGE_RANGES, i32_store_state, &[v32(0)]);
}

#[test]
fn i32_induction_store_stack_slot_rewrite_matches_scalar() {
    let func = i32_store_fixture(make_stack_slot_backed_i32_induction_store_loop());
    for ranges in [ZERO_ENTRY_RANGES, NONZERO_ENTRY_RANGES, I32_EDGE_RANGES] {
        assert_i32_store_rewrite_refines(&func, ranges, i32_store_state, &[]);
    }
}

#[test]
fn i32_induction_store_post_sroa_rewrite_matches_scalar() {
    let func = i32_store_fixture(make_post_sroa_alias_i32_induction_store_loop());
    for ranges in [ZERO_ENTRY_RANGES, NONZERO_ENTRY_RANGES, I32_EDGE_RANGES] {
        assert_i32_store_rewrite_refines(&func, ranges, i32_store_state, &[v32(22)]);
    }
}

/// The production pass — not only the rewrite's driver — takes the fixed
/// rewrite for every store-loop fixture, and each result matches the scalar
/// loop from zero, nonzero, negative and `i32::MAX`-adjacent entries. With
/// `I32_INDUCTION_STORE_REWRITE_AUTHORITY_AVAILABLE` false the pass leaves
/// every loop scalar and this test fails at `pass.run`.
#[test]
fn i32_induction_store_production_pass_matches_scalar() {
    for (fixture, observed) in [
        (make_imported_o0_i32_induction_store_loop(), Some(v32(0))),
        (make_stack_slot_backed_i32_induction_store_loop(), None),
        (
            make_post_sroa_alias_i32_induction_store_loop(),
            Some(v32(22)),
        ),
    ] {
        let func = i32_store_fixture(fixture);
        let mut rewritten = func.clone();
        let mut pass = VectorizationPass::new();
        assert!(pass.run(&mut rewritten));
        assert_eq!(pass.results().len(), 1);
        assert_eq!(count_opcode(&rewritten, AArch64Opcode::NeonSt1Post), 1);
        let observed: Vec<VReg> = observed.into_iter().collect();
        for ranges in [ZERO_ENTRY_RANGES, NONZERO_ENTRY_RANGES, I32_EDGE_RANGES] {
            for &(entry, bound) in ranges {
                assert_refines(
                    &func,
                    &rewritten,
                    &i32_store_state(entry, bound),
                    &observed,
                    &format!("{}: a[{entry}..{bound}]", func.name),
                );
            }
        }
    }
}

/// The header recomputes the base every iteration. The vector loop runs
/// before the header, so reusing that register reads the stale preheader
/// value.
#[test]
fn i32_induction_store_rejects_base_written_in_the_header() {
    let mut func = i32_store_fixture(make_imported_o0_i32_induction_store_loop());
    let real_base = v64(40);
    insert_in_block(
        &mut func,
        I32_STORE_HEADER,
        0,
        inst(AArch64Opcode::MovR, vec![reg(v64(6)), reg(real_base)]),
    );
    assert_i32_store_declined(
        &func,
        &[(0, 8), (4, 12)],
        |entry, bound| {
            i32_store_state(entry, bound)
                .with_reg(real_base, i32_store_base(entry))
                .with_reg(v64(6), STALE_POINTER)
        },
        &[v32(0)],
    );
}

/// The compared bound is a header copy of a register the header itself
/// rewrites every iteration, so the bound is not loop-invariant.
#[test]
fn i32_induction_store_rejects_bound_written_in_the_header() {
    let mut func = i32_store_fixture(make_imported_o0_i32_induction_store_loop());
    let (stale, fresh, header_bound) = (v32(41), v32(42), v32(43));
    insert_in_block(
        &mut func,
        I32_STORE_HEADER,
        0,
        inst(AArch64Opcode::MovR, vec![reg(stale), reg(fresh)]),
    );
    insert_in_block(
        &mut func,
        I32_STORE_HEADER,
        1,
        inst(AArch64Opcode::MovR, vec![reg(header_bound), reg(stale)]),
    );
    let compare = func.block(I32_STORE_HEADER).insts[2];
    func.inst_mut(compare).operands[1] = reg(header_bound);
    assert_i32_store_declined(
        &func,
        &[(0, 8), (3, 7)],
        |entry, bound| {
            i32_store_state(entry, bound)
                .with_reg(fresh, u128::from(bound as u32))
                .with_reg(stale, u128::from((bound + 64) as u32))
        },
        &[v32(0)],
    );
}

/// The store runs before the add, so each iteration stores the previous
/// iteration's value: set membership holds, datapath order does not.
#[test]
fn i32_induction_store_rejects_store_before_value() {
    let mut func = i32_store_fixture(make_imported_o0_i32_induction_store_loop());
    let body = func.block(I32_STORE_BODY).insts.clone();
    // [one, add, sxtw, madd, str, b] -> [one, sxtw, madd, str, add, b]
    func.block_mut(I32_STORE_BODY).insts =
        vec![body[0], body[2], body[3], body[4], body[1], body[5]];
    assert_i32_store_declined(
        &func,
        &[(0, 8), (2, 11)],
        |entry, bound| i32_store_state(entry, bound).with_reg(v32(3), 77),
        &[v32(0)],
    );
}

/// A leftover `Movz #1` the matcher admits into the body overwrites the value
/// before the store, so every iteration stores 1. Each instruction is in the
/// allowed set and every value is defined before its use; only the store's
/// reaching definition is wrong.
#[test]
fn i32_induction_store_rejects_value_overwritten_before_store() {
    let mut func = i32_store_fixture(make_imported_o0_i32_induction_store_loop());
    let (index, one, value) = (v32(0), v32(2), v32(3));
    let body = func.block(I32_STORE_BODY).insts.clone();
    // [movz one, add value, sxtw, madd, str, b] -> [add #1, movz value #1, sxtw, madd, str, b]
    *func.inst_mut(body[1]) = inst(
        AArch64Opcode::AddRI,
        vec![reg(value), reg(index), MachOperand::Imm(1)],
    );
    *func.inst_mut(body[0]) = inst(AArch64Opcode::Movz, vec![reg(value), MachOperand::Imm(1)]);
    func.block_mut(I32_STORE_BODY).insts =
        vec![body[1], body[0], body[2], body[3], body[4], body[5]];
    let step = func.block(I32_STORE_LATCH).insts[0];
    *func.inst_mut(step) = inst(
        AArch64Opcode::AddRI,
        vec![reg(v32(8)), reg(index), MachOperand::Imm(1)],
    );
    assert!(
        func.insts
            .iter()
            .all(|inst| !inst.operands.contains(&reg(one))),
        "the fixture no longer uses the register-form unit"
    );
    assert_i32_store_declined(&func, &[(0, 8), (3, 11)], i32_store_state, &[index]);
}

/// The header counts its own executions in memory. The vector loop runs
/// fewer header executions, so the header must hold nothing but the loop
/// test.
#[test]
fn i32_induction_store_rejects_side_effect_in_header() {
    let mut func = i32_store_fixture(make_imported_o0_i32_induction_store_loop());
    let counter = v64(51);
    insert_header_counter(&mut func, I32_STORE_HEADER, counter);
    assert_i32_store_declined(
        &func,
        &[(0, 8), (1, 13)],
        |entry, bound| with_counter(i32_store_state(entry, bound), counter),
        &[v32(0)],
    );
}

/// Insert `[counter] += 1` at the top of `block`.
fn insert_header_counter(func: &mut MachFunction, block: BlockId, counter: VReg) {
    let (count, next_count) = (v32(50), v32(52));
    for (at, new) in [
        inst(
            AArch64Opcode::LdrRI,
            vec![reg(count), reg(counter), MachOperand::Imm(0)],
        ),
        inst(
            AArch64Opcode::AddRI,
            vec![reg(next_count), reg(count), MachOperand::Imm(1)],
        ),
        inst(
            AArch64Opcode::StrRI,
            vec![reg(next_count), reg(counter), MachOperand::Imm(0)],
        ),
    ]
    .into_iter()
    .enumerate()
    {
        insert_in_block(func, block, at, new);
    }
}

/// Map a zeroed i32 counter at `COUNTER_START` and point `counter` at it.
fn with_counter(mut state: MachState, counter: VReg) -> MachState {
    state.regions.push(Region::i32s(COUNTER_START, &[0]));
    state.with_reg(counter, u128::from(COUNTER_START))
}

/// The stored value is read after the loop. When the scalar tail runs no
/// iteration, the vector loop leaves it stale.
#[test]
fn i32_induction_store_defs_are_not_live_out() {
    let mut func = i32_store_fixture(make_imported_o0_i32_induction_store_loop());
    let observed = v32(44);
    insert_in_block(
        &mut func,
        I32_STORE_EXIT,
        0,
        inst(AArch64Opcode::MovR, vec![reg(observed), reg(v32(3))]),
    );
    assert_i32_store_declined(
        &func,
        &[(0, 8), (4, 12), (0, 5)],
        |entry, bound| i32_store_state(entry, bound).with_reg(v32(3), 77),
        &[v32(0), observed],
    );
}

/// A branch ahead of the datapath skips it on every iteration.
#[test]
fn i32_induction_store_rejects_branch_before_datapath() {
    let mut func = i32_store_fixture(make_imported_o0_i32_induction_store_loop());
    // Hoist the unit so the latch still sees it, then branch over the body.
    let one = func.block(I32_STORE_BODY).insts[0];
    func.block_mut(I32_STORE_BODY).insts.remove(0);
    let entry = func.entry;
    let branch_pos = func.block(entry).insts.len() - 1;
    func.block_mut(entry).insts.insert(branch_pos, one);
    insert_in_block(
        &mut func,
        I32_STORE_BODY,
        0,
        inst(AArch64Opcode::B, vec![MachOperand::Block(I32_STORE_LATCH)]),
    );
    assert_i32_store_declined(&func, &[(0, 8), (1, 9)], i32_store_state, &[v32(0)]);
}

/// The header's exit branch targets the latch: the loop has no exit.
#[test]
fn i32_induction_store_rejects_header_exit_inside_loop() {
    let mut func = i32_store_fixture(make_imported_o0_i32_induction_store_loop());
    retarget_exit_into_loop(&mut func, I32_STORE_HEADER, I32_STORE_EXIT, I32_STORE_LATCH);
    assert!(!i32_store_matches(&func));
    assert_eq!(rewrite_i32_store_loops(&func).1, 0);
}

/// The header's exit branch also enters the body, and the CFG lists that edge
/// once: the header, body and latch edge lists are exact, but the loop has no
/// exit. Only the rule that the exit lies outside the loop declines it.
#[test]
fn i32_induction_store_rejects_header_exit_into_its_body() {
    let mut func = i32_store_fixture(make_imported_o0_i32_induction_store_loop());
    retarget_exit_to_body(&mut func, I32_STORE_HEADER, I32_STORE_EXIT, I32_STORE_BODY);
    assert!(!i32_store_matches(&func));
    assert_eq!(rewrite_i32_store_loops(&func).1, 0);
}

/// The array is the index's own stack slot, so an in-bounds store writes the
/// index. The vector loop keeps the index in a register and diverges.
#[test]
fn i32_induction_store_rejects_index_slot_that_escapes() {
    let mut func = i32_store_fixture(make_stack_slot_backed_i32_induction_store_loop());
    let slot_address = v64(30);
    let madd = func
        .block(I32_STORE_BODY)
        .insts
        .iter()
        .copied()
        .find(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::Madd)
        .expect("address computation");
    func.inst_mut(madd).operands[3] = reg(slot_address);
    assert_i32_store_declined(&func, &[(0, 8)], i32_store_state, &[]);
}

/// The unit the body adds is a header copy of another register; the last-wins
/// def map instead names an unreachable `Movz #1` later in the layout.
#[test]
fn i32_induction_store_rejects_unit_without_one_dominating_definition() {
    let mut func = i32_store_fixture(make_imported_o0_i32_induction_store_loop());
    let (one, step) = (v32(2), v32(45));
    func.block_mut(I32_STORE_BODY).insts.remove(0);
    insert_in_block(
        &mut func,
        I32_STORE_HEADER,
        0,
        inst(AArch64Opcode::MovR, vec![reg(one), reg(step)]),
    );
    append_unreachable_constant(&mut func, one, 1);
    assert_i32_store_declined(
        &func,
        &[(0, 8), (1, 13)],
        |entry, bound| i32_store_state(entry, bound).with_reg(step, 3),
        &[v32(0)],
    );
}

/// The body's add writes the index itself, so with the latch's `+ 1` each
/// iteration advances the index by two and the scalar loop stores only every
/// other element. Order, exactness and escape all hold; only the rule that
/// the latch is the index's one writer in the loop declines it.
#[test]
fn i32_induction_store_rejects_datapath_write_of_the_index() {
    let mut func = i32_store_fixture(make_imported_o0_i32_induction_store_loop());
    let index = v32(0);
    let body = func.block(I32_STORE_BODY).insts.clone();
    // [one, add value, sxtw, madd, str value, b] -> [one, sxtw, madd, add index, str index, b]
    func.inst_mut(body[1]).operands[0] = reg(index);
    func.inst_mut(body[4]).operands[0] = reg(index);
    func.block_mut(I32_STORE_BODY).insts =
        vec![body[0], body[2], body[3], body[1], body[4], body[5]];
    assert_i32_store_declined(&func, &[(0, 8), (1, 13)], i32_store_state, &[index]);
}

/// Two preheader instructions name the header; retargeting one leaves the
/// CFG edge list disagreeing with the other.
#[test]
fn i32_induction_store_rejects_second_preheader_branch_to_header() {
    let mut func = i32_store_fixture(make_imported_o0_i32_induction_store_loop());
    let entry = func.entry;
    let branch_pos = func.block(entry).insts.len() - 1;
    insert_in_block(
        &mut func,
        entry,
        branch_pos,
        inst(AArch64Opcode::CmpRI, vec![reg(v64(5)), MachOperand::Imm(0)]),
    );
    insert_in_block(
        &mut func,
        entry,
        branch_pos + 1,
        inst(
            AArch64Opcode::BCond,
            vec![MachOperand::Imm(0), MachOperand::Block(I32_STORE_HEADER)],
        ),
    );
    func.add_edge(entry, I32_STORE_HEADER);
    assert!(!i32_store_matches(&func));
    assert_eq!(rewrite_i32_store_loops(&func).1, 0);
}

// ---------------------------------------------------------------------------
// Reverse accumulation: `for (i = n - 1; i >= 0; i--) dst[i] += src[i]`
// ---------------------------------------------------------------------------

const REVERSE_HEADER: BlockId = BlockId(1);
const REVERSE_BODY: BlockId = BlockId(2);
const REVERSE_EXIT: BlockId = BlockId(3);
const REVERSE_LATCH: BlockId = BlockId(4);

/// Register-form fixture registers.
const REGISTER_INDEX: u32 = 0;
const REGISTER_SOURCE_BASE: u32 = 3;
const REGISTER_DEST_BASE: u32 = 4;
/// Stack-slot fixture registers.
const STACK_INDEX: u32 = 0;
const STACK_SOURCE_BASE: u32 = 5;
const STACK_DEST_BASE: u32 = 6;

const REVERSE_TRIPS: &[i64] = &[0, 1, 2, 15, 16, 17, 31, 32, 33, 48, 50];

/// `src` and `dst` of `stride_elements * n` i32s plus guards, with the index
/// at `n - 1` and the bases pointing past the leading guards.
fn reverse_state(
    n: i64,
    stride_elements: i64,
    index: VReg,
    source_base: VReg,
    dest_base: VReg,
) -> MachState {
    let len = stride_elements * n.max(0) + 2 * GUARD;
    let src: Vec<i32> = (0..len).map(|k| 1000 + 7 * k as i32).collect();
    let dst: Vec<i32> = (0..len).map(|k| 50 - 3 * k as i32).collect();
    let first = GUARD as u64 * 4;
    MachState::new(vec![
        Region::i32s(SRC_START, &src),
        Region::i32s(DST_START, &dst),
        Region::frame(1),
    ])
    .with_reg(index, u128::from((n - 1) as i32 as u32))
    .with_reg(source_base, u128::from(SRC_START + first))
    .with_reg(dest_base, u128::from(DST_START + first))
}

fn register_reverse_state(n: i64) -> MachState {
    reverse_state(
        n,
        1,
        v32(REGISTER_INDEX),
        v64(REGISTER_SOURCE_BASE),
        v64(REGISTER_DEST_BASE),
    )
}

fn stack_reverse_state(n: i64) -> MachState {
    reverse_state(
        n,
        1,
        v32(STACK_INDEX),
        v64(STACK_SOURCE_BASE),
        v64(STACK_DEST_BASE),
    )
}

/// Run the reverse-accumulation driver with NoAlias/InBounds facts on both
/// address computations.
fn rewrite_reverse_loops(func: &MachFunction, facts_on: [InstId; 2]) -> (MachFunction, usize) {
    let mut rewritten = func.clone();
    let proof_facts: HashMap<InstId, Vec<ProofFact>> = facts_on
        .into_iter()
        .map(|inst_id| (inst_id, vec![ProofFact::NoAlias, ProofFact::InBounds]))
        .collect();
    let dom = DomTree::compute(&rewritten);
    let loops = LoopAnalysis::compute(&rewritten, &dom);
    let mut maps = VecMaps::build(&rewritten);
    let count =
        rewrite_reverse_accumulation_loops(&mut rewritten, &loops, &proof_facts, None, &mut maps)
            .len();
    (rewritten, count)
}

fn reverse_matches(func: &MachFunction) -> bool {
    match_reverse_accumulation_loop(func, &only_loop(func), &build_def_map(func)).is_some()
}

fn assert_reverse_rewrite_refines(
    func: &MachFunction,
    facts_on: [InstId; 2],
    trips: &[i64],
    state_for: impl Fn(i64) -> MachState,
    observed: &[VReg],
) {
    let (rewritten, count) = rewrite_reverse_loops(func, facts_on);
    assert_eq!(count, 1, "the fixture is the reverse-accumulation idiom");
    for &n in trips {
        assert_refines(
            func,
            &rewritten,
            &state_for(n),
            observed,
            &format!("n = {n}"),
        );
    }
}

fn assert_reverse_declined(
    func: &MachFunction,
    facts_on: [InstId; 2],
    trips: &[i64],
    state_for: impl Fn(i64) -> MachState,
    observed: &[VReg],
) {
    let (rewritten, count) = rewrite_reverse_loops(func, facts_on);
    for &n in trips {
        assert_refines(
            func,
            &rewritten,
            &state_for(n),
            observed,
            &format!("n = {n}"),
        );
    }
    assert_eq!(count, 0, "a loop that is not the idiom must stay scalar");
    assert!(!reverse_matches(func));
}

/// Stack-slot index, separate latch block:
///
/// ```text
/// bb0: v16 = &slot0; v4 = 4; v14 = 0; v15 = -1; [v16] = v0; b bb1
/// bb1: v1 = [v16]; cmp v1, v14; b.ge bb2; b bb3
/// bb2: v2 = [v16]; v3 = sxtw v2; v7 = v3 * v4 + v5; v8 = v3 * v4 + v6
///      v9 = [v7]; v10 = [v8]; v11 = v10 + v9; [v8] = v11; b bb4
/// bb3: ret
/// bb4: v12 = [v16]; v13 = v12 + v15; [v16] = v13; b bb1
/// ```
fn make_split_latch_stack_backed_reverse_accumulation_loop() -> (MachFunction, InstId, InstId) {
    let mut func = MachFunction::new(
        "split_latch_stack_backed_reverse_accumulation_loop".to_string(),
        Signature::new(vec![], vec![]),
    );
    let preheader = func.entry;
    let header = func.create_block();
    let body = func.create_block();
    let exit = func.create_block();
    let latch = func.create_block();
    let slot = v64(16);
    let slot_operand = || reg(slot);
    let zero_offset = || MachOperand::Imm(0);

    for new in [
        inst(
            AArch64Opcode::AddPCRel,
            vec![
                slot_operand(),
                MachOperand::PReg(trust_cg_ir::aarch64_regs::SP),
                MachOperand::StackSlot(StackSlotId(0)),
            ],
        ),
        inst(AArch64Opcode::Movz, vec![reg(v64(4)), MachOperand::Imm(4)]),
        inst(AArch64Opcode::Movz, vec![reg(v32(14)), MachOperand::Imm(0)]),
        inst(AArch64Opcode::Movn, vec![reg(v32(15)), MachOperand::Imm(0)]),
        inst(
            AArch64Opcode::StrRI,
            vec![reg(v32(0)), slot_operand(), zero_offset()],
        ),
        inst(AArch64Opcode::B, vec![MachOperand::Block(header)]),
    ] {
        append_to_block(&mut func, preheader, new);
    }
    for new in [
        inst(
            AArch64Opcode::LdrRI,
            vec![reg(v32(1)), slot_operand(), zero_offset()],
        ),
        inst(AArch64Opcode::CmpRR, vec![reg(v32(1)), reg(v32(14))]),
        inst(
            AArch64Opcode::BCond,
            vec![MachOperand::Imm(10), MachOperand::Block(body)],
        ),
        inst(AArch64Opcode::B, vec![MachOperand::Block(exit)]),
    ] {
        append_to_block(&mut func, header, new);
    }
    let mut source_madd = None;
    let mut dest_madd = None;
    for new in [
        inst(
            AArch64Opcode::LdrRI,
            vec![reg(v32(2)), slot_operand(), zero_offset()],
        ),
        inst(AArch64Opcode::Sxtw, vec![reg(v64(3)), reg(v32(2))]),
        inst(
            AArch64Opcode::Madd,
            vec![reg(v64(7)), reg(v64(3)), reg(v64(4)), reg(v64(5))],
        ),
        inst(
            AArch64Opcode::Madd,
            vec![reg(v64(8)), reg(v64(3)), reg(v64(4)), reg(v64(6))],
        ),
        inst(
            AArch64Opcode::LdrRI,
            vec![reg(v32(9)), reg(v64(7)), zero_offset()],
        ),
        inst(
            AArch64Opcode::LdrRI,
            vec![reg(v32(10)), reg(v64(8)), zero_offset()],
        ),
        inst(
            AArch64Opcode::AddRR,
            vec![reg(v32(11)), reg(v32(10)), reg(v32(9))],
        ),
        inst(
            AArch64Opcode::StrRI,
            vec![reg(v32(11)), reg(v64(8)), zero_offset()],
        ),
        inst(AArch64Opcode::B, vec![MachOperand::Block(latch)]),
    ] {
        let is_madd = new.opcode == AArch64Opcode::Madd;
        let id = append_to_block(&mut func, body, new);
        if is_madd {
            if source_madd.is_none() {
                source_madd = Some(id);
            } else {
                dest_madd = Some(id);
            }
        }
    }
    append_to_block(&mut func, exit, inst(AArch64Opcode::Ret, vec![]));
    for new in [
        inst(
            AArch64Opcode::LdrRI,
            vec![reg(v32(12)), slot_operand(), zero_offset()],
        ),
        inst(
            AArch64Opcode::AddRR,
            vec![reg(v32(13)), reg(v32(12)), reg(v32(15))],
        ),
        inst(
            AArch64Opcode::StrRI,
            vec![reg(v32(13)), slot_operand(), zero_offset()],
        ),
        inst(AArch64Opcode::B, vec![MachOperand::Block(header)]),
    ] {
        append_to_block(&mut func, latch, new);
    }
    func.add_edge(preheader, header);
    func.add_edge(header, body);
    func.add_edge(header, exit);
    func.add_edge(body, latch);
    func.add_edge(latch, header);
    (
        func,
        source_madd.expect("source address"),
        dest_madd.expect("destination address"),
    )
}

#[test]
fn reverse_accumulation_rewrite_matches_scalar_register_index() {
    let (func, source, dest) = make_imported_o0_reverse_accumulation_loop();
    assert_reverse_rewrite_refines(
        &func,
        [source, dest],
        REVERSE_TRIPS,
        register_reverse_state,
        &[v32(REGISTER_INDEX)],
    );
}

#[test]
fn reverse_accumulation_rewrite_matches_scalar_merged_stack_latch() {
    let (func, source, dest) = make_merged_latch_stack_backed_reverse_accumulation_loop();
    assert_reverse_rewrite_refines(
        &func,
        [source, dest],
        REVERSE_TRIPS,
        stack_reverse_state,
        &[],
    );
}

#[test]
fn reverse_accumulation_rewrite_matches_scalar_split_stack_latch() {
    let (func, source, dest) = make_split_latch_stack_backed_reverse_accumulation_loop();
    assert_reverse_rewrite_refines(
        &func,
        [source, dest],
        REVERSE_TRIPS,
        stack_reverse_state,
        &[],
    );
}

/// The madds read body-local copies of the bases. The vector loop runs before
/// the body, so it must address through the copies' loop-invariant sources.
#[test]
fn reverse_accumulation_rewrite_reads_invariant_bases_not_body_copies() {
    let (func, source, dest) = make_cset_header_stack_backed_reverse_accumulation_loop();
    assert_reverse_rewrite_refines(
        &func,
        [source, dest],
        REVERSE_TRIPS,
        stack_reverse_state,
        &[],
    );
}

/// Reordered datapath: the store runs before the add, so each iteration
/// stores the previous iteration's sum.
#[test]
fn reverse_accumulation_rejects_store_before_add() {
    let (mut func, source, dest) = make_imported_o0_reverse_accumulation_loop();
    let body = func.block(REVERSE_BODY).insts.clone();
    // [sxtw, madd_s, ldr_s, madd_d, ldr_d, add, str, b] -> [.., ldr_d, str, add, b]
    func.block_mut(REVERSE_BODY).insts = vec![
        body[0], body[1], body[2], body[3], body[4], body[6], body[5], body[7],
    ];
    assert_reverse_declined(
        &func,
        [source, dest],
        &[16, 33],
        |n| register_reverse_state(n).with_reg(v32(9), 0),
        &[v32(REGISTER_INDEX)],
    );
}

/// The sum is read after the loop; when the scalar tail runs no iteration the
/// vector loop would leave it stale.
#[test]
fn reverse_accumulation_defs_are_not_live_out() {
    let (mut func, source, dest) = make_imported_o0_reverse_accumulation_loop();
    let observed = v32(40);
    insert_in_block(
        &mut func,
        REVERSE_EXIT,
        0,
        inst(AArch64Opcode::MovR, vec![reg(observed), reg(v32(9))]),
    );
    assert_reverse_declined(
        &func,
        [source, dest],
        &[16, 32, 33],
        |n| register_reverse_state(n).with_reg(v32(9), 0),
        &[v32(REGISTER_INDEX), observed],
    );
}

/// The source load writes the index register, so each iteration continues
/// from `src[i] - 1`; with `src[k] = k - 1` the scalar loop updates only
/// every other element. Order, exactness and escape all hold; only the rule
/// that the latch is the index's one writer in the loop declines it.
#[test]
fn reverse_accumulation_rejects_datapath_write_of_the_index() {
    let (mut func, source, dest) = make_imported_o0_reverse_accumulation_loop();
    let index = v32(REGISTER_INDEX);
    let body = func.block(REVERSE_BODY).insts.clone();
    // [sxtw, madd_s, ldr_s, madd_d, ldr_d, add, str, b]: ldr_s loads into the
    // index and the add reads it from there.
    func.inst_mut(body[2]).operands[0] = reg(index);
    func.inst_mut(body[5]).operands[2] = reg(index);
    // Lay the latch out before the body, so the shared last-wins def map
    // names the body's load of the index rather than the latch's writeback.
    func.block_order = vec![
        func.entry,
        REVERSE_HEADER,
        REVERSE_LATCH,
        REVERSE_BODY,
        REVERSE_EXIT,
    ];
    assert_reverse_declined(
        &func,
        [source, dest],
        &[16, 33],
        |n| {
            let mut state = register_reverse_state(n);
            let src: Vec<i32> = (0..n.max(0) + 2 * GUARD)
                .map(|slot| (slot - GUARD - 1) as i32)
                .collect();
            state.regions[0] = Region::i32s(SRC_START, &src);
            state
        },
        &[index],
    );
}

/// A branch ahead of the datapath skips it on every iteration.
#[test]
fn reverse_accumulation_rejects_branch_before_datapath() {
    let (mut func, source, dest) = make_imported_o0_reverse_accumulation_loop();
    insert_in_block(
        &mut func,
        REVERSE_BODY,
        0,
        inst(AArch64Opcode::B, vec![MachOperand::Block(REVERSE_LATCH)]),
    );
    assert_reverse_declined(
        &func,
        [source, dest],
        &[16, 20],
        register_reverse_state,
        &[v32(REGISTER_INDEX)],
    );
}

/// The separate latch also counts iterations in memory. The vector loop
/// would skip that side effect.
#[test]
fn reverse_accumulation_rejects_extra_latch_side_effect() {
    let (mut func, source, dest) = make_split_latch_stack_backed_reverse_accumulation_loop();
    let (counter, count, next_count) = (v64(51), v32(50), v32(52));
    let zero_offset = MachOperand::Imm(0);
    for (at, new) in [
        inst(
            AArch64Opcode::LdrRI,
            vec![reg(count), reg(counter), zero_offset.clone()],
        ),
        inst(
            AArch64Opcode::AddRI,
            vec![reg(next_count), reg(count), MachOperand::Imm(1)],
        ),
        inst(
            AArch64Opcode::StrRI,
            vec![reg(next_count), reg(counter), zero_offset.clone()],
        ),
    ]
    .into_iter()
    .enumerate()
    {
        insert_in_block(&mut func, REVERSE_LATCH, at, new);
    }
    assert_reverse_declined(
        &func,
        [source, dest],
        &[16, 33],
        |n| {
            let mut state = stack_reverse_state(n).with_reg(counter, u128::from(COUNTER_START));
            state.regions.push(Region::i32s(COUNTER_START, &[0]));
            state
        },
        &[],
    );
}

/// An element stride of 8 bytes is not the contiguous i32 array the vector
/// loop's paired Q loads assume.
#[test]
fn reverse_accumulation_rejects_non_i32_element_stride() {
    let (mut func, source, dest) = make_imported_o0_reverse_accumulation_loop();
    let stride = func.block(func.entry).insts[0];
    func.inst_mut(stride).operands[1] = MachOperand::Imm(8);
    assert_reverse_declined(
        &func,
        [source, dest],
        &[16, 17],
        |n| {
            reverse_state(
                n,
                2,
                v32(REGISTER_INDEX),
                v64(REGISTER_SOURCE_BASE),
                v64(REGISTER_DEST_BASE),
            )
        },
        &[v32(REGISTER_INDEX)],
    );
}

/// `cmp zero, index; b.ge` runs while `index <= 0`: not the idiom's test.
#[test]
fn reverse_accumulation_rejects_swapped_zero_compare() {
    let (mut func, source, dest) = make_merged_latch_stack_backed_reverse_accumulation_loop();
    let compare = func
        .block(REVERSE_HEADER)
        .insts
        .iter()
        .copied()
        .find(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::CmpRR)
        .expect("register-form compare");
    func.inst_mut(compare).operands.swap(0, 1);
    assert_reverse_declined(&func, [source, dest], &[20, 33], stack_reverse_state, &[]);
}

/// The header recomputes the source base every iteration. The vector loop
/// runs before the header, so reusing that register reads a stale value.
#[test]
fn reverse_accumulation_rejects_base_written_in_the_header() {
    let (mut func, source, dest) = make_imported_o0_reverse_accumulation_loop();
    let real_base = v64(41);
    insert_in_block(
        &mut func,
        REVERSE_HEADER,
        0,
        inst(
            AArch64Opcode::MovR,
            vec![reg(v64(REGISTER_SOURCE_BASE)), reg(real_base)],
        ),
    );
    assert_reverse_declined(
        &func,
        [source, dest],
        &[16, 33],
        |n| {
            let state = register_reverse_state(n);
            let base = state
                .reg(v64(REGISTER_SOURCE_BASE))
                .expect("seeded source base");
            state
                .with_reg(real_base, base)
                .with_reg(v64(REGISTER_SOURCE_BASE), STALE_POINTER)
        },
        &[v32(REGISTER_INDEX)],
    );
}

/// The header's exit branch targets the latch: the loop has no exit.
#[test]
fn reverse_accumulation_rejects_header_exit_inside_loop() {
    let (mut func, source, dest) = make_imported_o0_reverse_accumulation_loop();
    retarget_exit_into_loop(&mut func, REVERSE_HEADER, REVERSE_EXIT, REVERSE_LATCH);
    assert!(!reverse_matches(&func));
    assert_eq!(rewrite_reverse_loops(&func, [source, dest]).1, 0);
}

/// The header's exit branch also enters the body, and the CFG lists that edge
/// once: the edge lists are exact, but the loop has no exit. Only the rule
/// that the exit lies outside the loop declines it.
#[test]
fn reverse_accumulation_rejects_header_exit_into_its_body() {
    let (mut func, source, dest) = make_imported_o0_reverse_accumulation_loop();
    retarget_exit_to_body(&mut func, REVERSE_HEADER, REVERSE_EXIT, REVERSE_BODY);
    assert!(!reverse_matches(&func));
    assert_eq!(rewrite_reverse_loops(&func, [source, dest]).1, 0);
}

/// The header counts its own executions in memory; the vector loop would
/// skip most of them.
#[test]
fn reverse_accumulation_rejects_side_effect_in_header() {
    let (mut func, source, dest) = make_imported_o0_reverse_accumulation_loop();
    let counter = v64(51);
    insert_header_counter(&mut func, REVERSE_HEADER, counter);
    assert_reverse_declined(
        &func,
        [source, dest],
        &[16, 33],
        |n| with_counter(register_reverse_state(n), counter),
        &[v32(REGISTER_INDEX)],
    );
}

/// The preheader writes the compared register twice, 0 and then 20. Both
/// writes dominate the loop test, but only the second reaches it; a lookup
/// that stops at the first definition would take the bound for 0.
#[test]
fn reverse_accumulation_rejects_zero_redefined_before_the_loop() {
    let (mut func, source, dest) = make_merged_latch_stack_backed_reverse_accumulation_loop();
    let zero = v32(14);
    let entry = func.entry;
    let zero_pos = func
        .block(entry)
        .insts
        .iter()
        .position(|&inst_id| movz_i32_imm(func.inst(inst_id)) == Some((zero, 0)))
        .expect("zero constant");
    insert_in_block(
        &mut func,
        entry,
        zero_pos + 1,
        inst(AArch64Opcode::Movz, vec![reg(zero), MachOperand::Imm(20)]),
    );
    assert_reverse_declined(&func, [source, dest], &[40, 50], stack_reverse_state, &[]);
}

/// Move the merged-latch fixture's zero out of its preheader into a new
/// block `zero_block` that the returned new preheader follows.
fn split_zero_ahead_of_new_preheader(func: &mut MachFunction) -> (BlockId, InstId) {
    let entry = func.entry;
    let zero = v32(14);
    let zero_def = func
        .block(entry)
        .insts
        .iter()
        .copied()
        .find(|&inst_id| movz_i32_imm(func.inst(inst_id)) == Some((zero, 0)))
        .expect("zero constant");
    func.block_mut(entry)
        .insts
        .retain(|&inst_id| inst_id != zero_def);
    let preheader = func.create_block();
    append_to_block(
        func,
        preheader,
        inst(AArch64Opcode::B, vec![MachOperand::Block(REVERSE_HEADER)]),
    );
    remove_cfg_edge(func, entry, REVERSE_HEADER);
    func.add_edge(preheader, REVERSE_HEADER);
    (preheader, zero_def)
}

/// The zero is defined once, but only on one arm of a diamond ahead of the
/// preheader, so it does not dominate the loop test.
#[test]
fn reverse_accumulation_rejects_zero_that_does_not_dominate_the_loop() {
    let (mut func, source, dest) = make_merged_latch_stack_backed_reverse_accumulation_loop();
    let entry = func.entry;
    let (preheader, zero_def) = split_zero_ahead_of_new_preheader(&mut func);
    let left = func.create_block();
    let right = func.create_block();
    func.append_inst(left, zero_def);
    for block in [left, right] {
        append_to_block(
            &mut func,
            block,
            inst(AArch64Opcode::B, vec![MachOperand::Block(preheader)]),
        );
        func.add_edge(block, preheader);
    }
    let entry_branch = *func.block(entry).insts.last().expect("entry branch");
    *func.inst_mut(entry_branch) = inst(AArch64Opcode::B, vec![MachOperand::Block(right)]);
    let branch_pos = func.block(entry).insts.len() - 1;
    insert_in_block(
        &mut func,
        entry,
        branch_pos,
        inst(AArch64Opcode::CmpRI, vec![reg(v32(0)), MachOperand::Imm(7)]),
    );
    insert_in_block(
        &mut func,
        entry,
        branch_pos + 1,
        inst(
            AArch64Opcode::BCond,
            vec![MachOperand::Imm(0), MachOperand::Block(left)],
        ),
    );
    func.add_edge(entry, left);
    func.add_edge(entry, right);
    assert!(!reverse_matches(&func));
    assert_eq!(rewrite_reverse_loops(&func, [source, dest]).1, 0);
}

/// The zero is defined once, in a block that dominates the loop, but after a
/// branch that can leave that block without executing it.
#[test]
fn reverse_accumulation_rejects_zero_defined_after_a_branch_that_skips_it() {
    let (mut func, source, dest) = make_merged_latch_stack_backed_reverse_accumulation_loop();
    let entry = func.entry;
    let (preheader, zero_def) = split_zero_ahead_of_new_preheader(&mut func);
    let entry_branch = *func.block(entry).insts.last().expect("entry branch");
    *func.inst_mut(entry_branch) = inst(AArch64Opcode::B, vec![MachOperand::Block(preheader)]);
    let branch_pos = func.block(entry).insts.len() - 1;
    for (offset, new) in [
        inst(AArch64Opcode::CmpRI, vec![reg(v32(0)), MachOperand::Imm(7)]),
        inst(
            AArch64Opcode::BCond,
            vec![MachOperand::Imm(0), MachOperand::Block(preheader)],
        ),
    ]
    .into_iter()
    .enumerate()
    {
        insert_in_block(&mut func, entry, branch_pos + offset, new);
    }
    let branch_pos = func.block(entry).insts.len() - 1;
    func.block_mut(entry).insts.insert(branch_pos, zero_def);
    func.add_edge(entry, preheader);
    assert!(!reverse_matches(&func));
    assert_eq!(rewrite_reverse_loops(&func, [source, dest]).1, 0);
}

/// The header's exit branch targets the header itself.
#[test]
fn reverse_accumulation_rejects_header_exit_to_itself() {
    let (mut func, source, dest) = make_imported_o0_reverse_accumulation_loop();
    retarget_exit_into_loop(&mut func, REVERSE_HEADER, REVERSE_EXIT, REVERSE_HEADER);
    let dom = DomTree::compute(&func);
    let loops = LoopAnalysis::compute(&func, &dom);
    for lp in loops.all_loops() {
        assert!(match_reverse_accumulation_loop(&func, lp, &build_def_map(&func)).is_none());
    }
    assert_eq!(rewrite_reverse_loops(&func, [source, dest]).1, 0);
}

/// The compared "zero" really holds 20 on the only path into the loop; the
/// last-wins def map names an unreachable `Movz #0` instead.
#[test]
fn reverse_accumulation_rejects_zero_without_one_dominating_definition() {
    let (mut func, source, dest) = make_merged_latch_stack_backed_reverse_accumulation_loop();
    let zero = v32(14);
    let zero_def = func
        .block(func.entry)
        .insts
        .iter()
        .copied()
        .find(|&inst_id| movz_i32_imm(func.inst(inst_id)) == Some((zero, 0)))
        .expect("zero constant");
    func.inst_mut(zero_def).operands[1] = MachOperand::Imm(20);
    append_unreachable_constant(&mut func, zero, 0);
    assert_reverse_declined(&func, [source, dest], &[40, 50], stack_reverse_state, &[]);
}

/// Two preheader instructions name the header; retargeting one leaves the
/// CFG edge list disagreeing with the other.
#[test]
fn reverse_accumulation_rejects_second_preheader_branch_to_header() {
    let (mut func, source, dest) = make_imported_o0_reverse_accumulation_loop();
    let entry = func.entry;
    let branch_pos = func.block(entry).insts.len() - 1;
    insert_in_block(
        &mut func,
        entry,
        branch_pos,
        inst(AArch64Opcode::CmpRI, vec![reg(v64(2)), MachOperand::Imm(0)]),
    );
    insert_in_block(
        &mut func,
        entry,
        branch_pos + 1,
        inst(
            AArch64Opcode::BCond,
            vec![MachOperand::Imm(0), MachOperand::Block(REVERSE_HEADER)],
        ),
    );
    func.add_edge(entry, REVERSE_HEADER);
    assert!(!reverse_matches(&func));
    assert_eq!(rewrite_reverse_loops(&func, [source, dest]).1, 0);
}
