// Tests for scalar post-index formation.
//
// The pass turns a header-resident `LdrRO` whose index is `base + (inv<<k) +
// (V<<s)` into `LdrPostIndex [P], #elem`. Its soundness rests on the LOAD and
// the IV each running exactly once per iteration, so the refusals below pin the
// shapes where that stops being true.

use super::*;
use trust_cg_ir::Signature;

const BASE: u32 = 1;
const INV: u32 = 2;
const IV: u32 = 3;
const IDX: u32 = 4;
const T: u32 = 5;
const XFER: u32 = 6;
const LIMIT: u32 = 7;

fn g64(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn g32(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
}
fn imm(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}
fn append(func: &mut MachFunction, block: BlockId, inst: MachInst) {
    let id = func.push_inst(inst);
    func.append_inst(block, id);
}

fn folded(func: &MachFunction) -> bool {
    func.block_order.iter().any(|&b| {
        func.block(b)
            .insts
            .iter()
            .any(|&i| func.inst(i).opcode == AArch64Opcode::LdrPostIndex)
    })
}

/// ```text
/// bb0 (preheader): defs of BASE/INV/LIMIT, IV = 0 ; b bb1
/// bb1 (header):    LslRI  T,   IV, #shift
///                  AddRRShift IDX, T, INV, #11
///                  LdrRO  XFER, [BASE, IDX]
///                  AddRI  IV, IV, #step
///                  CmpRR  IV, LIMIT ; BCond bb2 ; B bb1
/// bb2 (exit):      Ret
/// ```
fn make_loop(shift: i64, dst32: bool, step: i64) -> (MachFunction, BlockId) {
    let mut func = MachFunction::new(
        "post_index_test".to_string(),
        Signature::new(vec![], vec![]),
    );
    while func.next_vreg <= 20 {
        func.alloc_vreg();
    }
    let bb0 = func.entry;
    let bb1 = func.create_block();
    let bb2 = func.create_block();

    for r in [BASE, INV, LIMIT] {
        append(
            &mut func,
            bb0,
            MachInst::new(AArch64Opcode::Movz, vec![g64(r), imm(0)]),
        );
    }
    append(
        &mut func,
        bb0,
        MachInst::new(AArch64Opcode::Movz, vec![g64(IV), imm(0)]),
    );
    append(
        &mut func,
        bb0,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
    );

    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::LslRI, vec![g64(T), g64(IV), imm(shift)]),
    );
    append(
        &mut func,
        bb1,
        MachInst::new(
            AArch64Opcode::AddRRShift,
            vec![g64(IDX), g64(T), g64(INV), imm(11)],
        ),
    );
    let dst = if dst32 { g32(XFER) } else { g64(XFER) };
    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::LdrRO, vec![dst, g64(BASE), g64(IDX)]),
    );
    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::AddRI, vec![g64(IV), g64(IV), imm(step)]),
    );
    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::CmpRR, vec![g64(IV), g64(LIMIT)]),
    );
    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::BCond, vec![imm(0), MachOperand::Block(bb2)]),
    );
    append(
        &mut func,
        bb1,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
    );
    append(&mut func, bb2, MachInst::new(AArch64Opcode::Ret, vec![]));

    // The CFG is stored on the blocks, not derived from terminators.
    func.block_mut(bb0).succs = vec![bb1];
    func.block_mut(bb1).preds = vec![bb0, bb1];
    func.block_mut(bb1).succs = vec![bb2, bb1];
    func.block_mut(bb2).preds = vec![bb1];
    (func, bb1)
}

#[test]
fn folds_a_header_load_whose_index_is_affine_in_a_unit_stride_iv() {
    let (mut f, _) = make_loop(2, true, 1);
    assert!(PostIndexForm.run(&mut f), "expected the fold to fire");
    assert!(folded(&f), "expected an LdrPostIndex");
}

/// The pointer advances by the LOAD's transfer width, so a shift that does not
/// match the element size would desynchronise `P` from the index.
#[test]
fn refuses_when_the_shift_does_not_match_the_transfer_width() {
    let (mut f, _) = make_loop(3, true, 1); // 1<<3 = 8, but the load moves 4
    assert!(
        !PostIndexForm.run(&mut f),
        "shift/width mismatch must refuse"
    );
    assert!(!folded(&f));
}

/// A step != 1 moves the index by more than one element per iteration, which a
/// single post-index writeback cannot track.
#[test]
fn refuses_a_non_unit_iv_step() {
    let (mut f, _) = make_loop(2, true, 2);
    assert!(!PostIndexForm.run(&mut f), "non-unit IV step must refuse");
    assert!(!folded(&f));
}

/// The packed-extend `LdrRO` forms carry SXTW/UXTW, where extending a
/// loop-variant 32-bit index does not commute with the 64-bit step — the
/// historic matrix-multiply miscompile. Never fold those.
#[test]
fn refuses_the_packed_extend_ldrro_form() {
    let (mut f, hdr) = make_loop(2, true, 1);
    let load = f.block(hdr).insts[2];
    f.inst_mut(load).operands.push(imm(0b0111));
    assert!(!PostIndexForm.run(&mut f), "packed-extend must refuse");
    assert!(!folded(&f));
}

/// If the index feeds anything besides the load, deleting the chain would drop
/// a live value.
#[test]
fn refuses_when_the_index_has_another_use() {
    let (mut f, hdr) = make_loop(2, true, 1);
    append(
        &mut f,
        hdr,
        MachInst::new(AArch64Opcode::AddRI, vec![g64(19), g64(IDX), imm(1)]),
    );
    assert!(!PostIndexForm.run(&mut f), "extra use must refuse");
    assert!(!folded(&f));
}

/// A base redefined inside the loop is not loop-invariant, so `P0` seeded in
/// the preheader would not track it.
#[test]
fn refuses_when_the_base_is_not_loop_invariant() {
    let (mut f, hdr) = make_loop(2, true, 1);
    append(
        &mut f,
        hdr,
        MachInst::new(AArch64Opcode::AddRI, vec![g64(BASE), g64(BASE), imm(8)]),
    );
    assert!(!PostIndexForm.run(&mut f), "variant base must refuse");
    assert!(!folded(&f));
}

#[test]
fn kill_switch_makes_the_pass_inert() {
    trust_cg_process_env::with_env_overrides(&[("TCG_NO_POST_INDEX", "1")], || {
        let (mut f, _) = make_loop(2, true, 1);
        assert!(!PostIndexForm.run(&mut f), "kill switch must disable");
        assert!(!folded(&f));
    });
}

fn link(func: &mut MachFunction, from: BlockId, to: BlockId) {
    func.block_mut(from).succs.push(to);
    func.block_mut(to).preds.push(from);
}

/// The IV's preheader value seeds `P`, so the first load must observe it: an
/// increment that runs ahead of the chain in the same block makes the first
/// load read `base + ((V0 + 1) << s)` while `P` starts at `base + (V0 << s)`.
#[test]
fn refuses_when_the_iv_steps_before_the_load_in_its_block() {
    let (mut f, hdr) = make_loop(2, true, 1);
    let step = f.block_mut(hdr).insts.remove(3);
    f.block_mut(hdr).insts.insert(0, step);
    assert_eq!(
        f.inst(f.block(hdr).insts[0]).opcode,
        AArch64Opcode::AddRI,
        "fixture: the step now leads the header"
    );
    assert!(
        !PostIndexForm.run(&mut f),
        "an IV stepped before the load must refuse"
    );
    assert!(!folded(&f));
}

/// ```text
/// bb0 (preheader): defs of BASE/INV/LIMIT, IV = 0 ; b bb1
/// bb1 (header):    AddRI IV, IV, #1 ; CmpRR IV, LIMIT ; BCond bb3 ; B bb2
/// bb2 (body):      LslRI T, IV, #2 ; AddRRShift IDX, T, INV, #11
///                  LdrRO XFER, [BASE, IDX] ; B bb1
/// bb3 (exit):      Ret
/// ```
///
/// Both blocks run once per iteration, but the header's increment runs
/// before the body's load in every iteration.
#[test]
fn refuses_when_the_iv_steps_in_a_block_that_runs_before_the_load() {
    let mut f = MachFunction::new(
        "post_index_test".to_string(),
        Signature::new(vec![], vec![]),
    );
    while f.next_vreg <= 20 {
        f.alloc_vreg();
    }
    let bb0 = f.entry;
    let bb1 = f.create_block();
    let bb2 = f.create_block();
    let bb3 = f.create_block();
    for r in [BASE, INV, LIMIT, IV] {
        append(
            &mut f,
            bb0,
            MachInst::new(AArch64Opcode::Movz, vec![g64(r), imm(0)]),
        );
    }
    append(
        &mut f,
        bb0,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
    );
    append(
        &mut f,
        bb1,
        MachInst::new(AArch64Opcode::AddRI, vec![g64(IV), g64(IV), imm(1)]),
    );
    append(
        &mut f,
        bb1,
        MachInst::new(AArch64Opcode::CmpRR, vec![g64(IV), g64(LIMIT)]),
    );
    append(
        &mut f,
        bb1,
        MachInst::new(AArch64Opcode::BCond, vec![imm(0), MachOperand::Block(bb3)]),
    );
    append(
        &mut f,
        bb1,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb2)]),
    );
    append(
        &mut f,
        bb2,
        MachInst::new(AArch64Opcode::LslRI, vec![g64(T), g64(IV), imm(2)]),
    );
    append(
        &mut f,
        bb2,
        MachInst::new(
            AArch64Opcode::AddRRShift,
            vec![g64(IDX), g64(T), g64(INV), imm(11)],
        ),
    );
    append(
        &mut f,
        bb2,
        MachInst::new(AArch64Opcode::LdrRO, vec![g32(XFER), g64(BASE), g64(IDX)]),
    );
    append(
        &mut f,
        bb2,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
    );
    append(&mut f, bb3, MachInst::new(AArch64Opcode::Ret, vec![]));
    link(&mut f, bb0, bb1);
    link(&mut f, bb1, bb3);
    link(&mut f, bb1, bb2);
    link(&mut f, bb2, bb1);

    assert!(
        !PostIndexForm.run(&mut f),
        "an IV stepped in a block that runs before the load must refuse"
    );
    assert!(!folded(&f));
}

const COUNTER: u32 = 8;
const HITS: u32 = 9;

/// ```text
/// bb0 (preheader): defs of BASE/INV/LIMIT, IV = 0, COUNTER = 0, HITS = 0
/// bb1 (header):    LslRI T, IV, #2 ; AddRRShift IDX, T, INV, #11
///                  LdrRO XFER, [BASE, IDX]
///                  CmpRI XFER, #0 ; BCond bb2 ; B bb3
/// bb2 (arm):       AddRI <arm_reg>, <arm_reg>, #1 ; B bb3
/// bb3 (latch):     AddRI <latch_reg>, <latch_reg>, #1
///                  AddRI COUNTER, COUNTER, #1 ; CmpRR COUNTER, LIMIT
///                  BCond bb4 ; B bb1
/// bb4 (exit):      Ret
/// ```
///
/// With `iv_on_arm`, the arm steps IV and the latch steps HITS; otherwise the
/// two are swapped and IV steps in the latch on every iteration.
fn make_arm_loop(iv_on_arm: bool) -> MachFunction {
    let (arm_reg, latch_reg) = if iv_on_arm { (IV, HITS) } else { (HITS, IV) };
    let mut f = MachFunction::new(
        "post_index_test".to_string(),
        Signature::new(vec![], vec![]),
    );
    while f.next_vreg <= 20 {
        f.alloc_vreg();
    }
    let bb0 = f.entry;
    let bb1 = f.create_block();
    let bb2 = f.create_block();
    let bb3 = f.create_block();
    let bb4 = f.create_block();
    for r in [BASE, INV, LIMIT, IV, COUNTER, HITS] {
        append(
            &mut f,
            bb0,
            MachInst::new(AArch64Opcode::Movz, vec![g64(r), imm(0)]),
        );
    }
    append(
        &mut f,
        bb0,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
    );
    append(
        &mut f,
        bb1,
        MachInst::new(AArch64Opcode::LslRI, vec![g64(T), g64(IV), imm(2)]),
    );
    append(
        &mut f,
        bb1,
        MachInst::new(
            AArch64Opcode::AddRRShift,
            vec![g64(IDX), g64(T), g64(INV), imm(11)],
        ),
    );
    append(
        &mut f,
        bb1,
        MachInst::new(AArch64Opcode::LdrRO, vec![g32(XFER), g64(BASE), g64(IDX)]),
    );
    append(
        &mut f,
        bb1,
        MachInst::new(AArch64Opcode::CmpRI, vec![g32(XFER), imm(0)]),
    );
    append(
        &mut f,
        bb1,
        MachInst::new(AArch64Opcode::BCond, vec![imm(1), MachOperand::Block(bb2)]),
    );
    append(
        &mut f,
        bb1,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb3)]),
    );
    append(
        &mut f,
        bb2,
        MachInst::new(
            AArch64Opcode::AddRI,
            vec![g64(arm_reg), g64(arm_reg), imm(1)],
        ),
    );
    append(
        &mut f,
        bb2,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb3)]),
    );
    append(
        &mut f,
        bb3,
        MachInst::new(
            AArch64Opcode::AddRI,
            vec![g64(latch_reg), g64(latch_reg), imm(1)],
        ),
    );
    append(
        &mut f,
        bb3,
        MachInst::new(
            AArch64Opcode::AddRI,
            vec![g64(COUNTER), g64(COUNTER), imm(1)],
        ),
    );
    append(
        &mut f,
        bb3,
        MachInst::new(AArch64Opcode::CmpRR, vec![g64(COUNTER), g64(LIMIT)]),
    );
    append(
        &mut f,
        bb3,
        MachInst::new(AArch64Opcode::BCond, vec![imm(0), MachOperand::Block(bb4)]),
    );
    append(
        &mut f,
        bb3,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
    );
    append(&mut f, bb4, MachInst::new(AArch64Opcode::Ret, vec![]));
    link(&mut f, bb0, bb1);
    link(&mut f, bb1, bb2);
    link(&mut f, bb1, bb3);
    link(&mut f, bb2, bb3);
    link(&mut f, bb3, bb4);
    link(&mut f, bb3, bb1);
    f
}

/// The load runs on every iteration but the IV steps only on iterations that
/// take the arm, so a post-indexed pointer would run ahead of the index.
#[test]
fn refuses_when_the_iv_steps_only_on_a_conditional_arm() {
    let mut f = make_arm_loop(true);
    assert!(
        !PostIndexForm.run(&mut f),
        "an IV stepped on a conditional arm must refuse"
    );
    assert!(!folded(&f));
}

/// Positive control for the arm loop: with the IV stepped in the latch, after
/// the load and on every iteration, the fold is admissible.
#[test]
fn folds_when_the_iv_steps_in_the_latch_past_an_arm() {
    let mut f = make_arm_loop(false);
    assert!(
        PostIndexForm.run(&mut f),
        "a latch-stepped IV past an arm must fold"
    );
    assert!(folded(&f));
}

/// `LslRI T, IV, #2 ; AddRRShift IDX, T, INV, #11 ; LdrRO XFER, [BASE, IDX]`.
fn append_chain(f: &mut MachFunction, b: BlockId) {
    append(
        f,
        b,
        MachInst::new(AArch64Opcode::LslRI, vec![g64(T), g64(IV), imm(2)]),
    );
    append(
        f,
        b,
        MachInst::new(
            AArch64Opcode::AddRRShift,
            vec![g64(IDX), g64(T), g64(INV), imm(11)],
        ),
    );
    append(
        f,
        b,
        MachInst::new(AArch64Opcode::LdrRO, vec![g32(XFER), g64(BASE), g64(IDX)]),
    );
}

/// `AddRI IV, IV, #1`.
fn append_iv_step(f: &mut MachFunction, b: BlockId) {
    append(
        f,
        b,
        MachInst::new(AArch64Opcode::AddRI, vec![g64(IV), g64(IV), imm(1)]),
    );
}

/// ```text
/// bb0 (preheader): defs of BASE/INV/LIMIT, IV = 0, COUNTER = 0, HITS = 0
/// bb1 (header):    [chain, unless `load_in_cycle`]
///                  CmpRI HITS, #0 ; BCond bb2 ; B bb3
/// bb2 (arm):       AddRI HITS, HITS, #1 ; B bb3
/// bb3 (step):      [chain, if `load_in_cycle`] [IV step, if `step_in_cycle`]
///                  CmpRI HITS, #1 ; BCond bb2 (only if `cycle`) ; B bb4
/// bb4 (latch):     [IV step, unless `step_in_cycle`]
///                  AddRI COUNTER, COUNTER, #1 ; CmpRR COUNTER, LIMIT
///                  BCond bb5 ; B bb1
/// bb5 (exit):      Ret
/// ```
///
/// With `cycle`, {bb2, bb3} is a two-entry cycle: the header enters both, and
/// neither dominates the other, so it has no dominator back-edge and the loop
/// at bb1 is still the only, innermost, loop. bb3 dominates the only latch, so
/// it is in `once_per_iter`, yet it runs twice on an iteration that takes
/// bb1 -> bb3 -> bb2 -> bb3. Without `cycle` the same blocks form a plain
/// triangle and bb3 runs exactly once per iteration.
fn make_two_entry_cycle_loop(
    load_in_cycle: bool,
    step_in_cycle: bool,
    cycle: bool,
) -> MachFunction {
    let mut f = MachFunction::new(
        "post_index_test".to_string(),
        Signature::new(vec![], vec![]),
    );
    while f.next_vreg <= 20 {
        f.alloc_vreg();
    }
    let bb0 = f.entry;
    let bb1 = f.create_block();
    let bb2 = f.create_block();
    let bb3 = f.create_block();
    let bb4 = f.create_block();
    let bb5 = f.create_block();
    for r in [BASE, INV, LIMIT, IV, COUNTER, HITS] {
        append(
            &mut f,
            bb0,
            MachInst::new(AArch64Opcode::Movz, vec![g64(r), imm(0)]),
        );
    }
    append(
        &mut f,
        bb0,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
    );

    if !load_in_cycle {
        append_chain(&mut f, bb1);
    }
    append(
        &mut f,
        bb1,
        MachInst::new(AArch64Opcode::CmpRI, vec![g64(HITS), imm(0)]),
    );
    append(
        &mut f,
        bb1,
        MachInst::new(AArch64Opcode::BCond, vec![imm(0), MachOperand::Block(bb2)]),
    );
    append(
        &mut f,
        bb1,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb3)]),
    );

    append(
        &mut f,
        bb2,
        MachInst::new(AArch64Opcode::AddRI, vec![g64(HITS), g64(HITS), imm(1)]),
    );
    append(
        &mut f,
        bb2,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb3)]),
    );

    if load_in_cycle {
        append_chain(&mut f, bb3);
    }
    if step_in_cycle {
        append_iv_step(&mut f, bb3);
    }
    append(
        &mut f,
        bb3,
        MachInst::new(AArch64Opcode::CmpRI, vec![g64(HITS), imm(1)]),
    );
    if cycle {
        append(
            &mut f,
            bb3,
            MachInst::new(AArch64Opcode::BCond, vec![imm(0), MachOperand::Block(bb2)]),
        );
    }
    append(
        &mut f,
        bb3,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb4)]),
    );

    if !step_in_cycle {
        append_iv_step(&mut f, bb4);
    }
    append(
        &mut f,
        bb4,
        MachInst::new(
            AArch64Opcode::AddRI,
            vec![g64(COUNTER), g64(COUNTER), imm(1)],
        ),
    );
    append(
        &mut f,
        bb4,
        MachInst::new(AArch64Opcode::CmpRR, vec![g64(COUNTER), g64(LIMIT)]),
    );
    append(
        &mut f,
        bb4,
        MachInst::new(AArch64Opcode::BCond, vec![imm(0), MachOperand::Block(bb5)]),
    );
    append(
        &mut f,
        bb4,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
    );
    append(&mut f, bb5, MachInst::new(AArch64Opcode::Ret, vec![]));

    link(&mut f, bb0, bb1);
    link(&mut f, bb1, bb2);
    link(&mut f, bb1, bb3);
    link(&mut f, bb2, bb3);
    if cycle {
        link(&mut f, bb3, bb2);
    }
    link(&mut f, bb3, bb4);
    link(&mut f, bb4, bb5);
    link(&mut f, bb4, bb1);
    f
}

/// The header's load runs once per iteration, but the IV's increment sits on
/// the irreducible cycle and runs twice on some iterations, so the index moves
/// two elements while a post-indexed pointer would move one.
#[test]
fn refuses_when_an_irreducible_cycle_runs_the_iv_step_twice() {
    let mut f = make_two_entry_cycle_loop(false, true, true);
    assert!(
        !PostIndexForm.run(&mut f),
        "an IV stepped on an irreducible cycle must refuse"
    );
    assert!(!folded(&f));
}

/// The load sits on the irreducible cycle and runs twice on some iterations
/// with the same index, while the IV steps once in the latch, so a
/// post-indexed pointer would move two elements per iteration.
#[test]
fn refuses_when_an_irreducible_cycle_runs_the_load_twice() {
    let mut f = make_two_entry_cycle_loop(true, false, true);
    assert!(
        !PostIndexForm.run(&mut f),
        "a load on an irreducible cycle must refuse"
    );
    assert!(!folded(&f));
}

/// Positive control for the two refusals above: the same loops without the
/// `bb3 -> bb2` edge fold, so each refusal is caused by the cycle.
#[test]
fn folds_the_two_entry_shapes_once_the_cycle_is_gone() {
    for (load_in_cycle, step_in_cycle) in [(false, true), (true, false)] {
        let mut f = make_two_entry_cycle_loop(load_in_cycle, step_in_cycle, false);
        assert!(
            PostIndexForm.run(&mut f),
            "load_in_cycle={load_in_cycle} step_in_cycle={step_in_cycle} must fold"
        );
        assert!(folded(&f));
    }
}
