// trust-cg-opt - OPT-1 spike: generic branch-layout analysis over the facade
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! OPT-1 decision-spike: ONE genuinely useful pass instantiated generically
//! for BOTH machine-IR universes through [`crate::mach_view::MachIrView`].
//!
//! **STATUS: prototype for `docs/adr-opt-ir-universe-2026-07-02.md`. ZERO
//! production wiring — no pipeline, pass manager, or gate calls this.**
//!
//! Per the binding OPT-2 amendment (`docs/opt-2-design-correction-2026-07-02.md`),
//! the pass prototyped here is the branch-layout / fall-through analysis that
//! feeds OPT-8 — the lever pulled FORWARD of unroll work — rather than the
//! originally-suggested loop unroll (trip<=4 full unroll never fires on the
//! benchmark suite; partial unroll-by-K is a mutation-heavy transform the ADR
//! costs on paper instead).
//!
//! # What it computes (the emitted-code deficits measured on b03/collatz)
//!
//! 1. **Redundant terminal jumps**: a block ending in an unconditional jump
//!    to its layout successor (`jmp <next>`) — elidable once the encoder
//!    emits fall-through.
//! 2. **Cond-then-jump exits**: a block ending `jcc T; jmp F` (the observed
//!    "`jcc +5; jmp far`" shape). When `T` is the layout successor, inverting
//!    the condition (`jcc' F`, fall through to `T`) removes the second
//!    branch. Arch-neutral: an AArch64 block ending `BCond T; B F` matches
//!    identically.
//! 3. **Per-loop layout facts**: whether each natural loop is rotated (latch
//!    conditionally branches back to the header, one branch per iteration)
//!    or unrotated (header cond-exit + latch unconditional back-jump, two),
//!    plus the branch-instruction count inside the body.
//!
//! The report is ANALYSIS ONLY. The one mutation offered,
//! [`elide_redundant_jumps`], exists to measure the facade's mutation-surface
//! cost for the ADR; landing it for real is OPT-8's job (the encoder must be
//! shown to emit fall-through on the target arch first, and cc-inversion must
//! go through the eval_int_condition-backed validator channel per the
//! roadmap's #3-trap-carriers correction).

use crate::mach_view::{CfgAnalysis, MachIrEdit, MachIrView, TermKind};

/// A block ending in an unconditional jump to its layout successor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RedundantJump<B> {
    pub block: B,
    /// Index of the jump instruction inside the block (always the last).
    pub inst_idx: usize,
    pub target: B,
}

/// A block ending in the two-instruction `cond-branch; jump` exit shape.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CondThenJump<B> {
    pub block: B,
    /// Index of the conditional branch (second-to-last instruction).
    pub cond_idx: usize,
    /// Index of the unconditional jump (last instruction).
    pub jump_idx: usize,
    /// Explicit target(s) of the conditional branch.
    pub cond_targets: Vec<B>,
    /// Target of the trailing unconditional jump.
    pub jump_target: B,
    /// True when a cond target IS the layout successor: inverting the
    /// condition lets it fall through and deletes the trailing jump
    /// (OPT-8's fall-through elision opportunity).
    pub invertible_to_fallthrough: bool,
    /// True when the trailing jump already targets the layout successor
    /// (then the jump itself is redundant, reported in `redundant_jumps`).
    pub jump_is_layout_next: bool,
}

/// Layout facts for one natural loop.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopLayoutFact<B> {
    pub header: B,
    /// First latch (block-index order); loops here are single-latch in
    /// practice, multi-latch loops report the full list length.
    pub latch: B,
    pub num_latches: usize,
    /// True when the latch ends in a conditional branch whose CFG successors
    /// include the header: the rotated (do-while) shape, one branch per
    /// iteration.
    pub rotated: bool,
    /// True when the header's terminator is a conditional branch with a
    /// successor outside the loop body (the unrotated exit-test-at-top shape).
    pub header_has_cond_exit: bool,
    /// Number of branch instructions across all body blocks — the static
    /// control-flow overhead the loop pays per iteration.
    pub branch_insts_in_body: usize,
}

/// Whole-function branch-layout report.
#[derive(Debug, Clone)]
pub struct BranchLayoutReport<B> {
    pub redundant_jumps: Vec<RedundantJump<B>>,
    pub cond_then_jump_exits: Vec<CondThenJump<B>>,
    pub loops: Vec<LoopLayoutFact<B>>,
}

impl<B> BranchLayoutReport<B> {
    /// True when the function already has optimal branch layout by these
    /// three measures.
    pub fn is_clean(&self) -> bool {
        self.redundant_jumps.is_empty()
            && self
                .cond_then_jump_exits
                .iter()
                .all(|c| !c.invertible_to_fallthrough && !c.jump_is_layout_next)
            && self.loops.iter().all(|l| l.rotated)
    }
}

/// Run the branch-layout analysis generically over either machine IR.
pub fn analyze_branch_layout<V: MachIrView>(view: &V) -> BranchLayoutReport<V::Block> {
    let order = view.layout_order();
    let layout_next = |i: usize| order.get(i + 1).copied();

    let mut redundant_jumps = Vec::new();
    let mut cond_then_jump_exits = Vec::new();

    for (i, &block) in order.iter().enumerate() {
        let n = view.inst_count(block);
        if n == 0 {
            continue;
        }

        // 1. Redundant terminal jump: `jmp <layout-next>`.
        if let TermKind::Jump { target } = view.classify_terminator(block)
            && Some(target) == layout_next(i)
        {
            redundant_jumps.push(RedundantJump {
                block,
                inst_idx: n - 1,
                target,
            });
        }

        // 2. Cond-then-jump exit shape: [.., jcc T, jmp F].
        if n >= 2
            && view.is_conditional_branch(block, n - 2)
            && view.is_unconditional_branch(block, n - 1)
        {
            let cond_targets = view.branch_targets(block, n - 2);
            let jump_targets = view.branch_targets(block, n - 1);
            if let [jump_target] = jump_targets.as_slice() {
                let next = layout_next(i);
                cond_then_jump_exits.push(CondThenJump {
                    block,
                    cond_idx: n - 2,
                    jump_idx: n - 1,
                    invertible_to_fallthrough: cond_targets.iter().any(|t| Some(*t) == next),
                    jump_is_layout_next: Some(*jump_target) == next,
                    cond_targets,
                    jump_target: *jump_target,
                });
            }
        }
    }

    // 3. Per-loop facts.
    let cfg = CfgAnalysis::compute(view);
    let loops = cfg
        .loops
        .iter()
        .map(|lp| {
            let latch = lp.latches[0];
            let rotated = matches!(view.classify_terminator(latch), TermKind::CondBranch { .. })
                && view.successors(latch).contains(&lp.header);

            let header_has_cond_exit = matches!(
                view.classify_terminator(lp.header),
                TermKind::CondBranch { .. }
            ) && view
                .successors(lp.header)
                .iter()
                .any(|s| !lp.body.contains(s));

            let mut branch_insts_in_body = 0usize;
            for &b in &order {
                if !lp.body.contains(&b) {
                    continue;
                }
                for idx in 0..view.inst_count(b) {
                    if view.is_branch(b, idx) {
                        branch_insts_in_body += 1;
                    }
                }
            }

            LoopLayoutFact {
                header: lp.header,
                latch,
                num_latches: lp.latches.len(),
                rotated,
                header_has_cond_exit,
                branch_insts_in_body,
            }
        })
        .collect();

    BranchLayoutReport {
        redundant_jumps,
        cond_then_jump_exits,
        loops,
    }
}

/// PROTOTYPE transform (measures the facade's mutation cost for the ADR):
/// remove every terminal unconditional jump whose target is the layout
/// successor. CFG successor sets are untouched — the edge stays, the
/// transfer becomes fall-through.
///
/// NOT wired anywhere: real elision belongs to OPT-8 and requires the
/// target arch's encoder to emit contiguous fall-through blocks.
pub fn elide_redundant_jumps<V: MachIrEdit>(func: &mut V) -> usize {
    let report = analyze_branch_layout(func);
    // Each redundant jump is the LAST instruction of its own block, so
    // removals never invalidate other recorded indices.
    for rj in &report.redundant_jumps {
        func.remove_inst(rj.block, rj.inst_idx);
    }
    report.redundant_jumps.len()
}

// ===========================================================================
// Tests: same pass, hand-built functions of BOTH IRs
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::regs::RegClass;
    use trust_cg_ir::x86_64_ops::X86CondCode;
    use trust_cg_ir::{
        AArch64Opcode, MachFunction, MachInst, MachOperand, Signature as A64Signature, VReg,
        X86Opcode,
    };
    use trust_cg_lower::function::Signature as X86Signature;
    use trust_cg_lower::instructions::Block;
    use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

    // ---- twin counted loop (same shape as mach_view tests) --------------

    fn a64_counted_loop() -> MachFunction {
        let mut f = MachFunction::new("a64_loop".to_string(), A64Signature::new(vec![], vec![]));
        let b0 = f.entry;
        let b1 = f.create_block();
        let b2 = f.create_block();
        let b3 = f.create_block();
        let v0 = VReg::new(f.alloc_vreg(), RegClass::Gpr64);

        let mov = f.push_inst(MachInst::new(
            AArch64Opcode::MovI,
            vec![MachOperand::VReg(v0), MachOperand::Imm(0)],
        ));
        f.append_inst(b0, mov);
        let br0 = f.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(b1)],
        ));
        f.append_inst(b0, br0);

        let cmp = f.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![MachOperand::VReg(v0), MachOperand::Imm(10)],
        ));
        f.append_inst(b1, cmp);
        let bcond = f.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(b2), MachOperand::Block(b3)],
        ));
        f.append_inst(b1, bcond);

        let add = f.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                MachOperand::VReg(v0),
                MachOperand::VReg(v0),
                MachOperand::Imm(1),
            ],
        ));
        f.append_inst(b2, add);
        let br2 = f.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(b1)],
        ));
        f.append_inst(b2, br2);

        let ret = f.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        f.append_inst(b3, ret);

        f.add_edge(b0, b1);
        f.add_edge(b1, b2);
        f.add_edge(b1, b3);
        f.add_edge(b2, b1);
        f
    }

    fn x86_counted_loop() -> X86ISelFunction {
        let sig = X86Signature {
            params: vec![],
            returns: vec![],
        };
        let mut f = X86ISelFunction::new("x86_loop".to_string(), sig);
        let (b0, b1, b2, b3) = (Block(0), Block(1), Block(2), Block(3));
        for b in [b0, b1, b2, b3] {
            f.ensure_block(b);
        }
        let v0 = VReg::new(0, RegClass::Gpr64);
        f.next_vreg = 1;

        f.push_inst(
            b0,
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(0)],
            ),
        );
        f.push_inst(
            b0,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(b1)]),
        );
        f.push_inst(
            b1,
            X86ISelInst::new(
                X86Opcode::CmpRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(10)],
            ),
        );
        f.push_inst(
            b1,
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::GE),
                    X86ISelOperand::Block(b3),
                ],
            ),
        );
        f.push_inst(
            b2,
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(1)],
            ),
        );
        f.push_inst(
            b2,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(b1)]),
        );
        f.push_inst(b3, X86ISelInst::new(X86Opcode::Ret, vec![]));

        f.blocks.get_mut(&b0).unwrap().successors = vec![b1];
        f.blocks.get_mut(&b1).unwrap().successors = vec![b3, b2];
        f.blocks.get_mut(&b2).unwrap().successors = vec![b1];
        f
    }

    /// The unrotated counted loop must report the same facts on both IRs:
    /// entry jump is redundant (b1 is layout-next), the loop is NOT rotated,
    /// the header holds the cond exit, and the body pays 2 branch insts.
    fn assert_unrotated_loop_report<V: MachIrView>(view: &V) {
        let order = view.layout_order();
        let (b0, b1, b2) = (order[0], order[1], order[2]);

        let report = analyze_branch_layout(view);

        assert_eq!(report.redundant_jumps.len(), 1, "{}", view.ir_name());
        assert_eq!(report.redundant_jumps[0].block, b0, "{}", view.ir_name());
        assert_eq!(report.redundant_jumps[0].target, b1, "{}", view.ir_name());

        assert_eq!(report.loops.len(), 1, "{}", view.ir_name());
        let lp = &report.loops[0];
        assert_eq!(lp.header, b1, "{}", view.ir_name());
        assert_eq!(lp.latch, b2, "{}", view.ir_name());
        assert_eq!(lp.num_latches, 1, "{}", view.ir_name());
        assert!(!lp.rotated, "unrotated shape: {}", view.ir_name());
        assert!(lp.header_has_cond_exit, "{}", view.ir_name());
        // Header cond-branch + latch back-jump.
        assert_eq!(lp.branch_insts_in_body, 2, "{}", view.ir_name());

        assert!(!report.is_clean(), "{}", view.ir_name());
    }

    #[test]
    fn unrotated_loop_reported_identically_on_aarch64() {
        assert_unrotated_loop_report(&a64_counted_loop());
    }

    #[test]
    fn unrotated_loop_reported_identically_on_x86() {
        assert_unrotated_loop_report(&x86_counted_loop());
    }

    // ---- cond-then-jump ("jcc +5; jmp far") detection --------------------

    /// x86 diamond entry: b0 ends `jcc b1; jmp b2` with b1 = layout next.
    /// The exact deficit shape from the b03/collatz disassembly.
    #[test]
    fn cond_then_jump_invertible_detected_on_x86() {
        let sig = X86Signature {
            params: vec![],
            returns: vec![],
        };
        let mut f = X86ISelFunction::new("x86_diamond".to_string(), sig);
        let (b0, b1, b2) = (Block(0), Block(1), Block(2));
        for b in [b0, b1, b2] {
            f.ensure_block(b);
        }
        f.push_inst(
            b0,
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::E),
                    X86ISelOperand::Block(b1),
                ],
            ),
        );
        f.push_inst(
            b0,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(b2)]),
        );
        f.push_inst(b1, X86ISelInst::new(X86Opcode::Ret, vec![]));
        f.push_inst(b2, X86ISelInst::new(X86Opcode::Ret, vec![]));
        f.blocks.get_mut(&b0).unwrap().successors = vec![b1, b2];

        let report = analyze_branch_layout(&f);
        assert_eq!(report.cond_then_jump_exits.len(), 1);
        let c = &report.cond_then_jump_exits[0];
        assert_eq!(c.block, b0);
        assert_eq!(c.cond_targets, vec![b1]);
        assert_eq!(c.jump_target, b2);
        assert!(c.invertible_to_fallthrough, "jcc target is layout-next");
        assert!(!c.jump_is_layout_next);
        assert!(!report.is_clean());
    }

    /// The same two-instruction shape hand-built on the AArch64 IR proves
    /// the detector is arch-neutral (single-target BCond followed by B).
    #[test]
    fn cond_then_jump_invertible_detected_on_aarch64() {
        let mut f = MachFunction::new("a64_diamond".to_string(), A64Signature::new(vec![], vec![]));
        let b0 = f.entry;
        let b1 = f.create_block();
        let b2 = f.create_block();

        let bcond = f.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(b1)],
        ));
        f.append_inst(b0, bcond);
        let b = f.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(b2)],
        ));
        f.append_inst(b0, b);
        let r1 = f.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        f.append_inst(b1, r1);
        let r2 = f.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        f.append_inst(b2, r2);
        f.add_edge(b0, b1);
        f.add_edge(b0, b2);

        let report = analyze_branch_layout(&f);
        assert_eq!(report.cond_then_jump_exits.len(), 1);
        let c = &report.cond_then_jump_exits[0];
        assert!(c.invertible_to_fallthrough);
        assert_eq!(c.jump_target, b2);
    }

    // ---- rotated loop ----------------------------------------------------

    /// Rotated (do-while) loop on x86: latch conditionally branches back.
    #[test]
    fn rotated_loop_reported_on_x86() {
        let sig = X86Signature {
            params: vec![],
            returns: vec![],
        };
        let mut f = X86ISelFunction::new("x86_rotated".to_string(), sig);
        let (b0, b1, b2, b3) = (Block(0), Block(1), Block(2), Block(3));
        for b in [b0, b1, b2, b3] {
            f.ensure_block(b);
        }
        let v0 = VReg::new(0, RegClass::Gpr64);
        f.next_vreg = 1;

        // b0: iv init, falls through to the header (no terminator — also
        // exercises the Fallthrough classification inside loop analysis).
        f.push_inst(
            b0,
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(0)],
            ),
        );
        // b1: body work, falls through to b2 (no terminator).
        f.push_inst(
            b1,
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(1)],
            ),
        );
        // b2: latch — cmp; jcc back to header; fall through to exit b3.
        f.push_inst(
            b2,
            X86ISelInst::new(
                X86Opcode::CmpRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(10)],
            ),
        );
        f.push_inst(
            b2,
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::L),
                    X86ISelOperand::Block(b1),
                ],
            ),
        );
        f.push_inst(b3, X86ISelInst::new(X86Opcode::Ret, vec![]));

        f.blocks.get_mut(&b0).unwrap().successors = vec![b1];
        f.blocks.get_mut(&b1).unwrap().successors = vec![b2];
        f.blocks.get_mut(&b2).unwrap().successors = vec![b1, b3];

        let report = analyze_branch_layout(&f);
        assert_eq!(report.loops.len(), 1);
        let lp = &report.loops[0];
        assert_eq!(lp.header, b1);
        assert_eq!(lp.latch, b2);
        assert!(lp.rotated, "latch cond-branches back to header");
        assert!(!lp.header_has_cond_exit);
        // Only the latch Jcc is a branch inside the body.
        assert_eq!(lp.branch_insts_in_body, 1);
        assert_eq!(report.redundant_jumps.len(), 0);
        assert!(report.is_clean());
    }

    // ---- the mutation prototype -------------------------------------------

    #[test]
    fn elide_redundant_jumps_on_both_irs() {
        // aarch64.
        let mut a64 = a64_counted_loop();
        let removed = elide_redundant_jumps(&mut a64);
        assert_eq!(removed, 1);
        let b0 = a64.entry;
        // Only the iv init remains; CFG edge preserved (fall-through).
        assert_eq!(MachIrView::inst_count(&a64, b0), 1);
        assert_eq!(a64.classify_terminator(b0), TermKind::Fallthrough);
        assert_eq!(
            MachIrView::successors(&a64, b0),
            vec![a64.layout_order()[1]]
        );
        // Idempotent: nothing left to elide.
        assert_eq!(elide_redundant_jumps(&mut a64), 0);

        // x86.
        let mut x86 = x86_counted_loop();
        let removed = elide_redundant_jumps(&mut x86);
        assert_eq!(removed, 1);
        let b0 = Block(0);
        assert_eq!(MachIrView::inst_count(&x86, b0), 1);
        assert_eq!(x86.classify_terminator(b0), TermKind::Fallthrough);
        assert_eq!(MachIrView::successors(&x86, b0), vec![Block(1)]);
        assert_eq!(elide_redundant_jumps(&mut x86), 0);
    }
}
