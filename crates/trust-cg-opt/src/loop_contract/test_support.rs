// Test support for the loop-state contract: inject the state a pre-loop rewrite
// must not skip into any pass's AArch64 loop fixture.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Every pass that runs new code instead of scalar iterations gets the same
// failing-first rows from these helpers, applied to a fixture it vectorizes:
//
// * `add_second_accumulator`: `t = t + iv` every trip through the header, `t`
//   read after the loop. The p09 sieve's `sum += i` beside `count += 1`.
// * `add_live_out`: `last = iv + 1` every iteration, read only after the loop.
//   Wrong whenever the rewrite consumes every iteration.
// * `add_early_exit`: `if iv == 40 { break }` at the top of the latch, to a
//   block of its own. The control clause: the measured `neon_fill` shape.
// * `add_exit_read`: a register the loop carries read at every exit (a loop
//   that returns `i`, or stores its accumulator). A rewrite that lists it as
//   reproduced but leaves straight to an exit holding a different value than
//   the scalar loop would must refuse it.
//
// Each leaves the recognized loop unchanged in every other respect, so a pass
// that fires on the plain fixture and ignores the rule fires here too.

use trust_cg_ir::{AArch64Opcode, BlockId, MachFunction, MachInst, MachOperand, VReg};

use crate::dom::DomTree;
use crate::loops::{LoopAnalysis, NaturalLoop};

/// Register numbers the helpers use; far above every fixture's own.
const SECOND: u32 = 9_001;
const SECOND_NEXT: u32 = 9_002;
const LAST: u32 = 9_003;
const SINK: u32 = 9_004;

/// The fixture's single innermost loop.
fn innermost_loop(func: &MachFunction) -> NaturalLoop {
    let dom = DomTree::compute(func);
    let loops = LoopAnalysis::compute(func, &dom);
    let innermost: Vec<&NaturalLoop> = loops
        .all_loops()
        .filter(|lp| {
            loops
                .all_loops()
                .all(|other| other.header == lp.header || !lp.body.contains(&other.header))
        })
        .collect();
    assert_eq!(
        innermost.len(),
        1,
        "fixture {} must have exactly one innermost loop",
        func.name
    );
    innermost[0].clone()
}

/// The loop's exits in layout order: blocks outside it that a loop block
/// branches to, excluding blocks that only trap.
fn exits(func: &MachFunction, lp: &NaturalLoop) -> Vec<BlockId> {
    let mut exits = Vec::new();
    for &block in &func.block_order {
        if lp.body.contains(&block) {
            continue;
        }
        let entered_from_loop = func
            .block(block)
            .preds
            .iter()
            .any(|pred| lp.body.contains(pred));
        let only_traps = func.block(block).insts.iter().all(|&id| {
            let opcode = func.inst(id).opcode;
            opcode == AArch64Opcode::Brk || opcode.is_trap_pseudo() || opcode == AArch64Opcode::Nop
        });
        if entered_from_loop && !only_traps && !func.block(block).insts.is_empty() {
            exits.push(block);
        }
    }
    assert!(!exits.is_empty(), "fixture {} has no loop exit", func.name);
    exits
}

fn insert_before_terminator(func: &mut MachFunction, block: BlockId, inst: MachInst) {
    let id = func.push_inst(inst);
    let insts = &func.block(block).insts;
    let position = insts
        .iter()
        .position(|&candidate| {
            let opcode = func.inst(candidate).opcode;
            opcode.is_unconditional_branch()
                || opcode.is_conditional_branch()
                || opcode == AArch64Opcode::Ret
        })
        .unwrap_or(insts.len());
    func.block_mut(block).insts.insert(position, id);
}

fn insert_first(func: &mut MachFunction, block: BlockId, inst: MachInst) {
    let id = func.push_inst(inst);
    func.block_mut(block).insts.insert(0, id);
}

fn vreg(id: u32, like: VReg) -> MachOperand {
    MachOperand::VReg(VReg::new(id, like.class))
}

/// Add `t = t + iv` at the top of the loop header, seed `t` in the preheader,
/// and read `t` at every exit. `iv` is the fixture's induction register.
pub(crate) fn add_second_accumulator(func: &mut MachFunction, iv: VReg) {
    let lp = innermost_loop(func);
    let preheader = lp.preheader.expect("fixture loop has a preheader");
    insert_before_terminator(
        func,
        preheader,
        MachInst::new(
            AArch64Opcode::Movz,
            vec![vreg(SECOND, iv), MachOperand::Imm(3)],
        ),
    );
    // At the top of the header, where no matcher's latch-writeback scan looks:
    // the update must be refused by the loop-state rule, not by a shape
    // coincidence.
    insert_first(
        func,
        lp.header,
        MachInst::new(
            AArch64Opcode::MovR,
            vec![vreg(SECOND, iv), vreg(SECOND_NEXT, iv)],
        ),
    );
    insert_first(
        func,
        lp.header,
        MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                vreg(SECOND_NEXT, iv),
                vreg(SECOND, iv),
                MachOperand::VReg(iv),
            ],
        ),
    );
    for exit in exits(func, &lp) {
        insert_first(
            func,
            exit,
            MachInst::new(AArch64Opcode::MovR, vec![vreg(SINK, iv), vreg(SECOND, iv)]),
        );
    }
}

/// Add `last = iv + 1` to the loop's latch, seed `last` in the preheader, and
/// read it at every exit. Nothing in the loop reads `last`: it is live-out
/// only.
pub(crate) fn add_live_out(func: &mut MachFunction, iv: VReg) {
    let lp = innermost_loop(func);
    let preheader = lp.preheader.expect("fixture loop has a preheader");
    insert_before_terminator(
        func,
        preheader,
        MachInst::new(
            AArch64Opcode::Movz,
            vec![vreg(LAST, iv), MachOperand::Imm(0)],
        ),
    );
    // `last = iv + 1`, not a copy: a latch COPY is what matchers scan for
    // writebacks, and the row must test the rule, not that scan.
    insert_before_terminator(
        func,
        lp.latch,
        MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(LAST, iv), MachOperand::VReg(iv), MachOperand::Imm(1)],
        ),
    );
    for exit in exits(func, &lp) {
        insert_first(
            func,
            exit,
            MachInst::new(AArch64Opcode::MovR, vec![vreg(SINK, iv), vreg(LAST, iv)]),
        );
    }
}

/// Read `reg` at the top of every exit of the loop, as a loop that returns
/// its induction, or stores its accumulator, does.
pub(crate) fn add_exit_read(func: &mut MachFunction, reg: VReg) {
    let lp = innermost_loop(func);
    for exit in exits(func, &lp) {
        insert_first(
            func,
            exit,
            MachInst::new(
                AArch64Opcode::MovR,
                vec![vreg(SINK, reg), MachOperand::VReg(reg)],
            ),
        );
    }
}

/// Add `if iv == 40 { break }` at the top of the loop's latch, leaving to a
/// new block that reads `iv` and returns. The loop then has an exit its
/// rewrite does not decide.
pub(crate) fn add_early_exit(func: &mut MachFunction, iv: VReg) {
    let lp = innermost_loop(func);
    let brk = func.create_block();
    let read = func.push_inst(MachInst::new(
        AArch64Opcode::MovR,
        vec![vreg(SINK, iv), MachOperand::VReg(iv)],
    ));
    func.append_inst(brk, read);
    let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(brk, ret);
    insert_first(
        func,
        lp.latch,
        MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Imm(0), MachOperand::Block(brk)],
        ),
    );
    insert_first(
        func,
        lp.latch,
        MachInst::new(
            AArch64Opcode::CmpRI,
            vec![MachOperand::VReg(iv), MachOperand::Imm(40)],
        ),
    );
    func.add_edge(lp.latch, brk);
}

// ---------------------------------------------------------------------------
// x86-64: the same two injections into an `X86ISelFunction` fixture.
// ---------------------------------------------------------------------------

use trust_cg_ir::X86Opcode;
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::mach_view::{CfgAnalysis, GenericLoop};

/// The fixture's single innermost loop.
fn x86_innermost_loop(func: &X86ISelFunction) -> GenericLoop<Block> {
    let loops = CfgAnalysis::compute(func).loops;
    let innermost: Vec<&GenericLoop<Block>> = loops
        .iter()
        .filter(|lp| {
            loops
                .iter()
                .all(|other| other.header == lp.header || !lp.body.contains(&other.header))
        })
        .collect();
    assert_eq!(
        innermost.len(),
        1,
        "fixture {} must have exactly one innermost loop",
        func.name
    );
    innermost[0].clone()
}

/// The loop's exits: blocks outside it that a loop block names as a successor,
/// excluding blocks that only trap (`Ud2`) or are empty.
fn x86_exits(func: &X86ISelFunction, lp: &GenericLoop<Block>) -> Vec<Block> {
    let mut exits = Vec::new();
    for &block in &func.block_order {
        if lp.body.contains(&block) {
            continue;
        }
        let entered_from_loop = lp
            .body
            .iter()
            .any(|&b| func.blocks[&b].successors.contains(&block));
        let insts = &func.blocks[&block].insts;
        let only_traps = insts.iter().all(|inst| inst.opcode == X86Opcode::Ud2);
        if entered_from_loop && !insts.is_empty() && !only_traps {
            exits.push(block);
        }
    }
    assert!(!exits.is_empty(), "fixture {} has no loop exit", func.name);
    exits
}

fn x86_vreg(id: u32, like: VReg) -> X86ISelOperand {
    X86ISelOperand::VReg(VReg::new(id, like.class))
}

/// The preheader: the loop's unique outside predecessor, else the header's
/// first outside predecessor in layout order.
fn x86_preheader(func: &X86ISelFunction, lp: &GenericLoop<Block>) -> Block {
    lp.preheader.unwrap_or_else(|| {
        *func
            .block_order
            .iter()
            .find(|&&b| !lp.body.contains(&b) && func.blocks[&b].successors.contains(&lp.header))
            .expect("fixture loop has an entering block")
    })
}

fn x86_insert_before_terminator(func: &mut X86ISelFunction, block: Block, inst: X86ISelInst) {
    let insts = &mut func.blocks.get_mut(&block).expect("block").insts;
    let position = insts
        .iter()
        .position(|candidate| {
            matches!(
                candidate.opcode,
                X86Opcode::Jmp | X86Opcode::Jcc | X86Opcode::Ret | X86Opcode::JmpR
            )
        })
        .unwrap_or(insts.len());
    insts.insert(position, inst);
}

fn x86_insert_first(func: &mut X86ISelFunction, block: Block, inst: X86ISelInst) {
    func.blocks
        .get_mut(&block)
        .expect("block")
        .insts
        .insert(0, inst);
}

/// x86 twin of [`add_second_accumulator`]: `t = t + iv` (a copy plus the tied
/// `AddRR`, the selector's two-address form) at the top of the header, `t`
/// seeded in the preheader and read at every exit.
pub(crate) fn x86_add_second_accumulator(func: &mut X86ISelFunction, iv: VReg) {
    let lp = x86_innermost_loop(func);
    let preheader = x86_preheader(func, &lp);
    x86_insert_before_terminator(
        func,
        preheader,
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![x86_vreg(SECOND, iv), X86ISelOperand::Imm(3)],
        ),
    );
    x86_insert_first(
        func,
        lp.header,
        X86ISelInst::new(
            X86Opcode::AddRR,
            vec![x86_vreg(SECOND, iv), X86ISelOperand::VReg(iv)],
        ),
    );
    for exit in x86_exits(func, &lp) {
        x86_insert_first(
            func,
            exit,
            X86ISelInst::new(
                X86Opcode::MovRR,
                vec![x86_vreg(SINK, iv), x86_vreg(SECOND, iv)],
            ),
        );
    }
}

/// x86 twin of [`add_live_out`]: `last = iv + 1` in every latch, seeded in the
/// preheader and read at every exit.
pub(crate) fn x86_add_live_out(func: &mut X86ISelFunction, iv: VReg) {
    let lp = x86_innermost_loop(func);
    let preheader = x86_preheader(func, &lp);
    x86_insert_before_terminator(
        func,
        preheader,
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![x86_vreg(LAST, iv), X86ISelOperand::Imm(0)],
        ),
    );
    for &latch in &lp.latches {
        x86_insert_before_terminator(
            func,
            latch,
            X86ISelInst::new(
                X86Opcode::MovRR,
                vec![x86_vreg(LAST, iv), X86ISelOperand::VReg(iv)],
            ),
        );
        x86_insert_before_terminator(
            func,
            latch,
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![x86_vreg(LAST, iv), X86ISelOperand::Imm(1)],
            ),
        );
    }
    for exit in x86_exits(func, &lp) {
        x86_insert_first(
            func,
            exit,
            X86ISelInst::new(
                X86Opcode::MovRR,
                vec![x86_vreg(SINK, iv), x86_vreg(LAST, iv)],
            ),
        );
    }
}
