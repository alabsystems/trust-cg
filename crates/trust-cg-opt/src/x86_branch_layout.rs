// trust-cg-opt - x86-64 branch layout (OPT-8): fallthrough + latch preference
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! OPT-8: x86-64 branch-layout optimization over the terminal
//! `jcc T; jmp F` block shape.
//!
//! # The measured deficit (b03/collatz disassembly, roadmap OPT-2 amendment)
//!
//! The x86 ISel ends every two-way block with the pair `jcc T; jmp F`:
//! the hot path frequently *takes* the `jcc` over the adjacent `jmp`
//! ("`jcc +5; jmp far`"), and loop latches pay two branch instructions per
//! iteration where LLVM pays one. This pass rewrites the PAIR IN PLACE:
//!
//! ```text
//!   jcc  cc, T          jcc  invert(cc), F
//!   jmp  F         =>   jmp  T
//! ```
//!
//! choosing the direction so that the trailing `jmp` targets the block that
//! the layout (or the loop shape) makes cheap:
//!
//! * **Latch rule** (DEFAULT ON — profile-independent) — when the block is a
//!   natural-loop latch whose *unconditional* `jmp` is the back-edge
//!   (`F == header`), the swap puts the back-edge on the conditional branch:
//!   the hot path executes ONE taken `jcc` per iteration instead of a
//!   not-taken `jcc` plus a taken `jmp`. A loop body runs many times by
//!   definition, so this saves a branch on every iteration regardless of
//!   edge probabilities — a strict win (measured: p2_collatz -32%,
//!   b1_mispredict -13%). The exit `jmp T` still elides whenever `T` is the
//!   layout successor (the common case).
//! * **Fallthrough rule** (DEFAULT OFF — profile-dependent heuristic) — when
//!   `T` is the layout successor (and `F` is not), the swap makes the
//!   trailing `jmp` target the layout successor, which the encoder elides to
//!   ZERO bytes. This only *helps* if `T` is the hot successor; with no
//!   profile data the pass assumes layout-successor == hot, which is WRONG
//!   for match-heavy code (measured: p6_branch_match +4.3% — a real
//!   regression). DEFERRED off in [`X86BranchLayoutConfig::default`] pending
//!   profile data / a static hotness estimator; opt in for A/B experiments.
//!
//! # Why this is safe by construction (and what is proven anyway)
//!
//! The rewrite mutates ONLY the two terminator instructions of a block, in
//! place: same opcodes, same block, swapped explicit targets, inverted
//! condition code. The CFG successor SET is unchanged, `block_order` is
//! unchanged, no instruction is added, removed, or moved, and no value
//! computation is touched (a `jcc` reads RFLAGS, writes nothing). Every
//! downstream fail-closed stage (carrier hygiene, glue-pass validator,
//! regalloc + its validators, per-instruction certs, the encoder gates)
//! re-checks the rewritten function exactly as it would any ISel output.
//!
//! The ONE semantic step — that `invert(cc)` branches on EXACTLY the
//! complement of `cc` — is the #3-trap-carriers wrong-cc class (a wrong
//! inversion silently inverts a bounds/null/div0 or user branch). It is NOT
//! assumed: every applied inversion must first be admitted by the
//! [`CcInversionAdmit`] callback the embedder supplies. The production
//! wiring (trust-cg-codegen `x86_64/pipeline.rs`) backs this callback with
//! `trust_cg_verify::pass_validators::CondCodeInversionValidator` — an
//! exhaustive equivalence proof over all 32 RFLAGS states, minted and
//! checked through the fail-closed `CertifiedPassChain` machinery, memoized
//! per condition code. **Admission is an optimization gate, not a
//! soundness gate**: a rejected inversion simply leaves the (correct,
//! two-branch) original in place; it never fails the compile.
//!
//! # What this pass consumes from the OPT-1 generic core
//!
//! Candidate discovery is [`crate::generic_branch_layout::analyze_branch_layout`]
//! (the `CondThenJump` exit shape + layout-successor facts) and loop/latch
//! facts come from [`crate::mach_view::CfgAnalysis`] natural-loop discovery —
//! both written once against the [`crate::mach_view::MachIrView`] facade per
//! the ADR (`docs/adr-opt-ir-universe-2026-07-02.md`). Only the ~100-line
//! x86 mutation kernel below is IR-specific.
//!
//! # Deferred (with reason)
//!
//! Loop-body ROTATION (duplicating the header exit test into the latch so
//! unrotated `while`-shaped loops pay one branch per iteration) requires
//! cloning value computations across blocks — a mutation-heavy transform in
//! exactly the loop-carried-value territory the ADR marks port-first and the
//! project's miscompile history marks hazardous. It is NOT attempted here;
//! the rotation FACTS (`LoopLayoutFact::rotated`) remain available from the
//! generic core for the future task. Block reordering (`block_order`
//! mutation) is likewise deferred: the two in-place rules above capture the
//! measured deficits without perturbing any layout-sensitive invariant.

use std::collections::HashMap;

use trust_cg_ir::x86_64_ops::{X86CondCode, X86Opcode};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelFunction, X86ISelOperand};

use crate::generic_branch_layout::analyze_branch_layout;
use crate::mach_view::CfgAnalysis;
use crate::x86_pass_manager::X86MachinePass;

/// Admission callback for a condition-code inversion: `admit(original,
/// inverted)` must return `true` iff the embedder has PROVEN that `inverted`
/// branches on exactly the complement of `original` (for every RFLAGS
/// state). The production callback is validator-backed and memoized; tests
/// may supply table-driven or rejecting callbacks.
///
/// A `false` return skips the rewrite for that block (the original
/// two-branch form is kept) — it never fails the compile.
pub type CcInversionAdmit = fn(X86CondCode, X86CondCode) -> bool;

/// Which of the two independent layout rewrites the pass applies.
///
/// The two rules have very different risk profiles, so they are toggled
/// separately (the production default enables only the profile-independent
/// latch rule — see [`X86BranchLayoutConfig::default`]):
///
/// * **`latch_rule`** — profile-INDEPENDENT. A natural-loop latch whose
///   back-edge rides the unconditional `jmp` executes two branches per
///   iteration; putting the back-edge on the (taken) `jcc` saves one branch
///   on EVERY iteration of the loop. A loop body runs many times by
///   definition, so this is a strict win regardless of edge probabilities.
///   Measured: p2_collatz -32%, b1_mispredict -13%.
/// * **`fallthrough_rule`** — profile-DEPENDENT (a heuristic guess). For a
///   non-loop `jcc T; jmp F` where `T` is the layout successor, inverting so
///   the fall-through lands on `T` only helps if `T` is actually the hot
///   successor; without profile data the pass assumes layout-successor ==
///   hot, which is WRONG for match-heavy code (measured: p6_branch_match
///   +4.3%, a real regression). DEFERRED OFF by default until profile data
///   (or a static hotness estimator) is available; opt in with the pipeline
///   env override for A/B experiments.
#[derive(Clone, Copy, Debug)]
pub struct X86BranchLayoutConfig {
    /// Apply the loop-latch rewrite (back-edge onto the conditional branch).
    pub latch_rule: bool,
    /// Apply the fall-through inversion for non-loop two-way exits.
    pub fallthrough_rule: bool,
    /// Apply the COLD-TRAP fall-through inversion: for a `jcc T; jmp F` whose
    /// `jmp` target `F` is a provably-cold trap block (a `Ud2`-only block,
    /// e.g. a bounds-check / panic=abort failure exit that a correct program
    /// never reaches) and whose `jcc` target `T` is the layout successor,
    /// invert so the never-taken trap moves onto the (never-taken) conditional
    /// branch and the hot path FALLS THROUGH to `T`. Unlike `fallthrough_rule`
    /// this is profile-FREE-CORRECT, not a heuristic guess: `F` is genuinely
    /// never taken, so the swap strictly improves BOTH paths — the hot path's
    /// always-taken `jcc` becomes a never-taken fall-through, and the trap
    /// path drops from two branches (`jcc` not-taken + `jmp` taken) to one.
    /// The `p6_branch_match` regression that deferred `fallthrough_rule` came
    /// from a data-dependent branch where the "cold" side was actually hot;
    /// a `Ud2` sink cannot be hot. Default ON.
    pub cold_trap_rule: bool,
}

impl Default for X86BranchLayoutConfig {
    /// Production default: latch rule ON (profile-independent win), cold-trap
    /// rule ON (profile-free-correct — the jmp sink is a never-taken `Ud2`),
    /// generic fall-through rule OFF (profile-free heuristic that regressed a
    /// real match-heavy program).
    fn default() -> Self {
        Self {
            latch_rule: true,
            fallthrough_rule: false,
            cold_trap_rule: true,
        }
    }
}

/// x86-64 branch-layout pass (OPT-8). See the module docs.
pub struct X86BranchLayout {
    admit_inversion: CcInversionAdmit,
    config: X86BranchLayoutConfig,
    /// Number of `jcc/jmp` pairs swapped by the most recent [`run`]
    /// invocation (diagnostics/tests only).
    ///
    /// [`run`]: X86MachinePass::run
    pub last_run_swaps: usize,
}

impl X86BranchLayout {
    /// Create the pass with the given inversion-admission callback and BOTH
    /// rules enabled. Retained for unit tests that exercise each rule; the
    /// production pipeline uses [`X86BranchLayout::with_config`] with the
    /// [`X86BranchLayoutConfig::default`] policy (latch-only).
    pub fn new(admit_inversion: CcInversionAdmit) -> Self {
        Self::with_config(
            admit_inversion,
            X86BranchLayoutConfig {
                latch_rule: true,
                fallthrough_rule: true,
                cold_trap_rule: true,
            },
        )
    }

    /// Create the pass with an explicit rule configuration.
    pub fn with_config(admit_inversion: CcInversionAdmit, config: X86BranchLayoutConfig) -> Self {
        Self {
            admit_inversion,
            config,
            last_run_swaps: 0,
        }
    }
}

/// The planned rewrite for one block's terminal `jcc T; jmp F` pair.
struct PlannedSwap {
    block: Block,
    cond_idx: usize,
    jump_idx: usize,
    original_cc: X86CondCode,
    inverted_cc: X86CondCode,
    /// Original `jcc` target (becomes the `jmp` target).
    cond_target: Block,
    /// Original `jmp` target (becomes the `jcc` target).
    jump_target: Block,
}

impl X86MachinePass for X86BranchLayout {
    fn name(&self) -> &str {
        "x86-branch-layout"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        self.last_run_swaps = 0;
        if func.block_order.len() < 2 {
            return false;
        }

        // Facts from the OPT-1 generic core: candidate `jcc T; jmp F` exits
        // (with layout-successor classification) and natural loops.
        let report = analyze_branch_layout(func);
        if report.cond_then_jump_exits.is_empty() {
            return false;
        }
        let cfg = CfgAnalysis::compute(func);

        // Innermost loop header for each latch block: when one block is a
        // latch of several nested loops, prefer the deepest (hottest)
        // back-edge.
        let mut latch_header: HashMap<Block, (Block, u32)> = HashMap::new();
        for lp in &cfg.loops {
            for &latch in &lp.latches {
                let entry = latch_header.entry(latch).or_insert((lp.header, lp.depth));
                if lp.depth > entry.1 {
                    *entry = (lp.header, lp.depth);
                }
            }
        }

        let mut planned: Vec<PlannedSwap> = Vec::new();
        for exit in &report.cond_then_jump_exits {
            // x86 `Jcc` carries exactly one explicit target; anything else is
            // not the shape this pass understands — skip conservatively.
            let [cond_target] = exit.cond_targets.as_slice() else {
                continue;
            };
            let (cond_target, jump_target) = (*cond_target, exit.jump_target);
            if cond_target == jump_target {
                // Degenerate two-way branch to one block: nothing to gain.
                continue;
            }

            // Decide the desired direction. The latch rule dominates: a
            // latch whose back-edge rides the unconditional `jmp` pays two
            // executed branches per iteration; swapping puts the hot
            // back-edge on the (taken) `jcc` regardless of layout.
            let should_swap = match latch_header.get(&exit.block) {
                Some(&(header, _)) if cond_target == header => {
                    // Back-edge already on the conditional branch: the hot
                    // path is already one taken `jcc` per iteration. Never
                    // swap it away (also guards fixpoint re-runs against
                    // rule oscillation).
                    false
                }
                // Latch rule (profile-independent): back-edge on the JMP ->
                // move it onto the taken JCC, saving one branch per iteration.
                Some(&(header, _)) if jump_target == header => self.config.latch_rule,
                // Non-latch two-way exit. Two rules can fire here:
                //
                //  * Cold-trap rule (profile-FREE-correct, default ON): the
                //    `jmp` target is a `Ud2`-only trap block (never reached in
                //    a correct program) and the `jcc` target is the layout
                //    successor. Inverting moves the never-taken trap onto the
                //    conditional branch and lets the hot path fall through —
                //    strictly better on both paths, no profile assumption.
                //  * Generic fallthrough rule (profile-dependent heuristic,
                //    default OFF): same shape but with an arbitrary (possibly
                //    hot) `jmp` sink. Requires the `jmp` target NOT already be
                //    the layout successor (else the encoder already elides it
                //    and swapping would regress).
                _ => {
                    (self.config.cold_trap_rule
                        && exit.invertible_to_fallthrough
                        && block_is_cold_trap(func, jump_target))
                        || (self.config.fallthrough_rule
                            && exit.invertible_to_fallthrough
                            && !exit.jump_is_layout_next)
                }
            };
            if !should_swap {
                continue;
            }

            // Re-verify the concrete instruction shape at the mutation site
            // (defensive against any drift between the analysis view and the
            // block contents; skip — never touch — anything unexpected).
            let Some(block) = func.blocks.get(&exit.block) else {
                continue;
            };
            let (Some(cond_inst), Some(jump_inst)) = (
                block.insts.get(exit.cond_idx),
                block.insts.get(exit.jump_idx),
            ) else {
                continue;
            };
            if exit.jump_idx != block.insts.len() - 1 || exit.cond_idx + 1 != exit.jump_idx {
                continue;
            }
            if cond_inst.opcode != X86Opcode::Jcc || jump_inst.opcode != X86Opcode::Jmp {
                continue;
            }
            let [
                X86ISelOperand::CondCode(original_cc),
                X86ISelOperand::Block(t),
            ] = cond_inst.operands.as_slice()
            else {
                continue;
            };
            let [X86ISelOperand::Block(f)] = jump_inst.operands.as_slice() else {
                continue;
            };
            if *t != cond_target || *f != jump_target {
                continue;
            }

            // The one semantic step: the inverted cc must be PROVEN to be
            // the exact complement (validator-backed in production). A
            // rejection skips the rewrite — never fails the compile.
            let inverted_cc = original_cc.invert();
            if !(self.admit_inversion)(*original_cc, inverted_cc) {
                continue;
            }

            planned.push(PlannedSwap {
                block: exit.block,
                cond_idx: exit.cond_idx,
                jump_idx: exit.jump_idx,
                original_cc: *original_cc,
                inverted_cc,
                cond_target,
                jump_target,
            });
        }

        if planned.is_empty() {
            return false;
        }

        // Apply the swaps. Structural self-check per rewrite: the block's
        // successor edge SET and instruction count must be untouched, and the
        // pair must still be `jcc; jmp` with the swapped targets. The
        // mutation below guarantees this by construction (operand vectors are
        // replaced in place; `successors` is never written), so a violation
        // indicates memory-safety-level corruption — assert loudly rather
        // than emit.
        for swap in &planned {
            let block = func
                .blocks
                .get_mut(&swap.block)
                .expect("planned swap block exists (checked during planning)");
            let succs_before: Vec<Block> = block.successors.clone();
            let insts_before = block.insts.len();

            // In-place operand rewrite ONLY: preserves flags, provenance,
            // proof_origin and every other instruction field.
            block.insts[swap.cond_idx].operands = vec![
                X86ISelOperand::CondCode(swap.inverted_cc),
                X86ISelOperand::Block(swap.jump_target),
            ];
            block.insts[swap.jump_idx].operands = vec![X86ISelOperand::Block(swap.cond_target)];

            debug_assert_eq!(swap.inverted_cc, swap.original_cc.invert());
            assert_eq!(
                block.insts.len(),
                insts_before,
                "x86-branch-layout: instruction count changed"
            );
            assert_eq!(
                block.successors, succs_before,
                "x86-branch-layout: successor edges changed"
            );
        }

        self.last_run_swaps = planned.len();
        true
    }
}

/// True iff `block` is a provably-COLD trap sink: it exists and every one of
/// its non-pseudo instructions is `Ud2`, with at least one such instruction.
/// These are the bounds-check / null-check / panic=abort failure exits (a
/// correct program never transfers control into them), so a layout that puts
/// the trap on a never-taken conditional branch is a pure win — the cold-trap
/// rule's soundness rests on this being a genuine dead-end sink, not on any
/// profile estimate. A `Ud2` block has no successors (it faults), so no edge
/// probability is being assumed away.
fn block_is_cold_trap(func: &X86ISelFunction, block: Block) -> bool {
    let Some(b) = func.blocks.get(&block) else {
        return false;
    };
    let mut saw_ud2 = false;
    for inst in &b.insts {
        match inst.opcode {
            X86Opcode::Nop | X86Opcode::Phi | X86Opcode::StackAlloc => continue,
            X86Opcode::Ud2 => saw_ud2 = true,
            // Any other real instruction means the block does work — not a
            // pure trap sink. Fail closed (do not treat as cold).
            _ => return false,
        }
    }
    saw_ud2
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::VReg;
    use trust_cg_ir::regs::RegClass;
    use trust_cg_lower::X86ISelInst;
    use trust_cg_lower::function::Signature;

    fn admit_all(_original: X86CondCode, _inverted: X86CondCode) -> bool {
        true
    }

    fn admit_none(_original: X86CondCode, _inverted: X86CondCode) -> bool {
        false
    }

    /// Admission that mimics the production contract: accept only the true
    /// complement.
    fn admit_exact(original: X86CondCode, inverted: X86CondCode) -> bool {
        original.invert() == inverted
    }

    fn empty_sig() -> Signature {
        Signature {
            params: vec![],
            returns: vec![],
        }
    }

    fn jcc(cc: X86CondCode, target: Block) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::Jcc,
            vec![X86ISelOperand::CondCode(cc), X86ISelOperand::Block(target)],
        )
    }

    fn jmp(target: Block) -> X86ISelInst {
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(target)])
    }

    fn terminator_shape(func: &X86ISelFunction, b: Block) -> (X86CondCode, Block, Block) {
        let block = &func.blocks[&b];
        let n = block.insts.len();
        let [X86ISelOperand::CondCode(cc), X86ISelOperand::Block(t)] =
            block.insts[n - 2].operands.as_slice()
        else {
            panic!("expected jcc shape");
        };
        let [X86ISelOperand::Block(f)] = block.insts[n - 1].operands.as_slice() else {
            panic!("expected jmp shape");
        };
        (*cc, *t, *f)
    }

    /// Diamond entry, the exact "jcc +5; jmp far" deficit shape:
    /// b0 ends `jcc E b1; jmp b2` with b1 the layout successor.
    fn diamond() -> X86ISelFunction {
        let mut f = X86ISelFunction::new("diamond".to_string(), empty_sig());
        let (b0, b1, b2) = (Block(0), Block(1), Block(2));
        for b in [b0, b1, b2] {
            f.ensure_block(b);
        }
        f.push_inst(b0, jcc(X86CondCode::E, b1));
        f.push_inst(b0, jmp(b2));
        f.push_inst(b1, X86ISelInst::new(X86Opcode::Ret, vec![]));
        f.push_inst(b2, X86ISelInst::new(X86Opcode::Ret, vec![]));
        f.blocks.get_mut(&b0).unwrap().successors = vec![b1, b2];
        f
    }

    #[test]
    fn fallthrough_rule_swaps_and_inverts() {
        let mut f = diamond();
        let succs_before = f.blocks[&Block(0)].successors.clone();

        let mut pass = X86BranchLayout::new(admit_exact);
        assert!(pass.run(&mut f));
        assert_eq!(pass.last_run_swaps, 1);

        // jcc NE b2 (far target on the inverted cond), jmp b1 (layout next,
        // elided by the encoder).
        let (cc, t, jf) = terminator_shape(&f, Block(0));
        assert_eq!(cc, X86CondCode::NE);
        assert_eq!(t, Block(2));
        assert_eq!(jf, Block(1));
        // Successor edges untouched.
        assert_eq!(f.blocks[&Block(0)].successors, succs_before);
    }

    #[test]
    fn fallthrough_rule_is_idempotent() {
        let mut f = diamond();
        let mut pass = X86BranchLayout::new(admit_exact);
        assert!(pass.run(&mut f));
        let shape_after_first = terminator_shape(&f, Block(0));
        // Second run: the jmp now targets the layout successor
        // (`jump_is_layout_next`), so nothing further to do.
        assert!(!pass.run(&mut f));
        assert_eq!(pass.last_run_swaps, 0);
        assert_eq!(terminator_shape(&f, Block(0)), shape_after_first);
    }

    #[test]
    fn jmp_already_layout_next_is_left_alone() {
        // b0 ends `jcc E b2 (far); jmp b1 (layout next)` — already optimal:
        // the encoder elides the jmp. Swapping would regress.
        let mut f = X86ISelFunction::new("clean".to_string(), empty_sig());
        let (b0, b1, b2) = (Block(0), Block(1), Block(2));
        for b in [b0, b1, b2] {
            f.ensure_block(b);
        }
        f.push_inst(b0, jcc(X86CondCode::E, b2));
        f.push_inst(b0, jmp(b1));
        f.push_inst(b1, X86ISelInst::new(X86Opcode::Ret, vec![]));
        f.push_inst(b2, X86ISelInst::new(X86Opcode::Ret, vec![]));
        f.blocks.get_mut(&b0).unwrap().successors = vec![b2, b1];

        let mut pass = X86BranchLayout::new(admit_all);
        assert!(!pass.run(&mut f));
    }

    /// Loop whose latch ends `jcc GE exit; jmp header` — the two-branch
    /// latch. Layout: b0 (preheader), b1 (header+body), b2 (latch), b3
    /// (exit).
    fn two_branch_latch_loop() -> X86ISelFunction {
        let mut f = X86ISelFunction::new("latch".to_string(), empty_sig());
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
        f.push_inst(b0, jmp(b1));
        // b1: body, falls through to the latch.
        f.push_inst(
            b1,
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(1)],
            ),
        );
        // b2: latch — cmp; jcc GE exit; jmp header (back-edge on the JMP).
        f.push_inst(
            b2,
            X86ISelInst::new(
                X86Opcode::CmpRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(10)],
            ),
        );
        f.push_inst(b2, jcc(X86CondCode::GE, b3));
        f.push_inst(b2, jmp(b1));
        f.push_inst(b3, X86ISelInst::new(X86Opcode::Ret, vec![]));

        f.blocks.get_mut(&b0).unwrap().successors = vec![b1];
        f.blocks.get_mut(&b1).unwrap().successors = vec![b2];
        f.blocks.get_mut(&b2).unwrap().successors = vec![b3, b1];
        f
    }

    #[test]
    fn latch_rule_puts_back_edge_on_the_jcc() {
        let mut f = two_branch_latch_loop();
        let mut pass = X86BranchLayout::new(admit_exact);
        assert!(pass.run(&mut f));
        assert_eq!(pass.last_run_swaps, 1);

        // Latch now: jcc L header (taken back-edge, one branch per
        // iteration); jmp exit — and the exit IS the layout successor, so
        // the encoder elides it to zero bytes.
        let (cc, t, jf) = terminator_shape(&f, Block(2));
        assert_eq!(cc, X86CondCode::L);
        assert_eq!(t, Block(1), "back-edge rides the jcc");
        assert_eq!(jf, Block(3), "exit rides the (elidable) jmp");

        // Idempotent: the back-edge is now on the conditional branch.
        assert!(!pass.run(&mut f));
    }

    #[test]
    fn rotated_latch_is_never_swapped_away() {
        // Latch already ends `jcc L header; jmp exit` — optimal. The
        // fallthrough rule must NOT swap it back even though the jcc target
        // (header) is not the layout successor and the jmp target (exit) is.
        let mut f = X86ISelFunction::new("rotated".to_string(), empty_sig());
        let (b0, b1, b2) = (Block(0), Block(1), Block(2));
        for b in [b0, b1, b2] {
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
        // b1: header + latch (self-shaped rotated loop body).
        f.push_inst(
            b1,
            X86ISelInst::new(
                X86Opcode::CmpRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(10)],
            ),
        );
        f.push_inst(b1, jcc(X86CondCode::L, b1));
        f.push_inst(b1, jmp(b2));
        f.push_inst(b2, X86ISelInst::new(X86Opcode::Ret, vec![]));
        f.blocks.get_mut(&b0).unwrap().successors = vec![b1];
        f.blocks.get_mut(&b1).unwrap().successors = vec![b1, b2];

        let mut pass = X86BranchLayout::new(admit_all);
        assert!(!pass.run(&mut f), "rotated latch must be left alone");
    }

    #[test]
    fn rejected_admission_skips_the_rewrite() {
        let mut f = diamond();
        let before = terminator_shape(&f, Block(0));
        let mut pass = X86BranchLayout::new(admit_none);
        assert!(!pass.run(&mut f), "no admission => no rewrite");
        assert_eq!(terminator_shape(&f, Block(0)), before);
    }

    #[test]
    fn degenerate_same_target_pair_is_skipped() {
        let mut f = X86ISelFunction::new("degen".to_string(), empty_sig());
        let (b0, b1) = (Block(0), Block(1));
        for b in [b0, b1] {
            f.ensure_block(b);
        }
        f.push_inst(b0, jcc(X86CondCode::E, b1));
        f.push_inst(b0, jmp(b1));
        f.push_inst(b1, X86ISelInst::new(X86Opcode::Ret, vec![]));
        f.blocks.get_mut(&b0).unwrap().successors = vec![b1];

        let mut pass = X86BranchLayout::new(admit_all);
        assert!(!pass.run(&mut f));
    }

    #[test]
    fn non_terminal_jcc_jmp_pairs_are_untouched() {
        // An instruction AFTER the jmp (malformed/unexpected shape): the
        // analysis only reports terminal pairs, so nothing may change.
        let mut f = X86ISelFunction::new("shape".to_string(), empty_sig());
        let (b0, b1, b2) = (Block(0), Block(1), Block(2));
        for b in [b0, b1, b2] {
            f.ensure_block(b);
        }
        f.push_inst(b0, jcc(X86CondCode::E, b1));
        f.push_inst(b0, jmp(b2));
        f.push_inst(b0, X86ISelInst::new(X86Opcode::Nop, vec![]));
        f.push_inst(b1, X86ISelInst::new(X86Opcode::Ret, vec![]));
        f.push_inst(b2, X86ISelInst::new(X86Opcode::Ret, vec![]));
        f.blocks.get_mut(&b0).unwrap().successors = vec![b1, b2];

        let mut pass = X86BranchLayout::new(admit_all);
        assert!(!pass.run(&mut f));
    }

    #[test]
    fn all_sixteen_condition_codes_invert_through_admission() {
        // The pass always pairs `cc` with `cc.invert()`; the exact-admission
        // callback (production contract) must accept every pair.
        use X86CondCode::*;
        for cc in [O, NO, B, AE, E, NE, BE, A, S, NS, P, NP, L, GE, LE, G] {
            assert!(admit_exact(cc, cc.invert()), "{cc:?}");
            assert!(!admit_exact(cc, cc), "{cc:?} must not admit itself");
        }
    }

    #[test]
    fn default_config_is_latch_plus_cold_trap() {
        // The production policy: profile-independent latch rule ON, cold-trap
        // fall-through inversion ON (profile-free-correct), the generic
        // profile-free fall-through heuristic (regressed p6_branch_match)
        // DEFERRED off.
        let c = X86BranchLayoutConfig::default();
        assert!(c.latch_rule, "latch rule is the default-on win");
        assert!(c.cold_trap_rule, "cold-trap inversion is default-on");
        assert!(
            !c.fallthrough_rule,
            "generic fall-through rule is deferred off pending profile data"
        );
    }

    /// A `jcc E b1(hot); jmp b2(Ud2 trap)` diamond where b1 is the layout
    /// successor: the exact bounds-check exit shape from b06/b18.
    fn cold_trap_diamond() -> X86ISelFunction {
        let mut f = X86ISelFunction::new("cold_trap".to_string(), empty_sig());
        let (b0, b1, b2) = (Block(0), Block(1), Block(2));
        for b in [b0, b1, b2] {
            f.ensure_block(b);
        }
        f.push_inst(b0, jcc(X86CondCode::E, b1)); // in-bounds -> continue
        f.push_inst(b0, jmp(b2)); // else -> trap
        f.push_inst(b1, X86ISelInst::new(X86Opcode::Ret, vec![]));
        f.push_inst(b2, X86ISelInst::new(X86Opcode::Ud2, vec![])); // cold trap sink
        f.blocks.get_mut(&b0).unwrap().successors = vec![b1, b2];
        f
    }

    #[test]
    fn cold_trap_rule_inverts_so_trap_is_the_branch_target() {
        // Default (production) config must invert: jcc NE b2(trap) on the
        // never-taken branch, jmp b1(hot, layout-next -> elided by encoder).
        let mut f = cold_trap_diamond();
        let succs_before = f.blocks[&Block(0)].successors.clone();
        let mut pass = X86BranchLayout::with_config(admit_exact, X86BranchLayoutConfig::default());
        assert!(pass.run(&mut f), "cold-trap inversion must fire by default");
        assert_eq!(pass.last_run_swaps, 1);
        let (cc, t, jf) = terminator_shape(&f, Block(0));
        assert_eq!(cc, X86CondCode::NE, "condition inverted");
        assert_eq!(t, Block(2), "trap moved onto the (never-taken) jcc");
        assert_eq!(jf, Block(1), "hot path is now the fall-through jmp");
        assert_eq!(f.blocks[&Block(0)].successors, succs_before);
    }

    #[test]
    fn cold_trap_rule_off_leaves_trap_diamond_alone() {
        // With cold_trap_rule and fallthrough_rule both off, the trap diamond
        // is untouched (isolates the new rule as the sole cause).
        let mut f = cold_trap_diamond();
        let before = terminator_shape(&f, Block(0));
        let mut pass = X86BranchLayout::with_config(
            admit_exact,
            X86BranchLayoutConfig {
                latch_rule: true,
                fallthrough_rule: false,
                cold_trap_rule: false,
            },
        );
        assert!(!pass.run(&mut f), "no rule enabled for this shape");
        assert_eq!(terminator_shape(&f, Block(0)), before);
    }

    #[test]
    fn cold_trap_rule_ignores_non_trap_sink() {
        // Same shape but the jmp sink is a Ret block (does real work, could be
        // hot): the cold-trap rule must NOT fire (that is the profile-guess
        // case reserved for fallthrough_rule).
        let mut f = cold_trap_diamond();
        // Replace b2's Ud2 with a Ret -> no longer a cold trap.
        f.blocks.get_mut(&Block(2)).unwrap().insts = vec![X86ISelInst::new(X86Opcode::Ret, vec![])];
        let before = terminator_shape(&f, Block(0));
        let mut pass = X86BranchLayout::with_config(admit_exact, X86BranchLayoutConfig::default());
        assert!(
            !pass.run(&mut f),
            "cold-trap rule must not fire on a non-trap (possibly hot) sink"
        );
        assert_eq!(terminator_shape(&f, Block(0)), before);
    }

    #[test]
    fn block_is_cold_trap_recognizes_ud2_only() {
        let f = cold_trap_diamond();
        assert!(block_is_cold_trap(&f, Block(2)), "Ud2-only block is cold");
        assert!(!block_is_cold_trap(&f, Block(1)), "Ret block is not cold");
        assert!(
            !block_is_cold_trap(&f, Block(99)),
            "absent block is not cold"
        );
    }

    #[test]
    fn latch_only_config_applies_latch_but_skips_fallthrough() {
        // The fall-through diamond must be LEFT ALONE under the default
        // (latch-only) config — this is precisely the profile-free rewrite
        // that regressed match-heavy code.
        let mut d = diamond();
        let before = terminator_shape(&d, Block(0));
        let mut pass = X86BranchLayout::with_config(admit_exact, X86BranchLayoutConfig::default());
        assert!(
            !pass.run(&mut d),
            "latch-only config must skip the fall-through diamond"
        );
        assert_eq!(terminator_shape(&d, Block(0)), before);

        // The latch rule still fires under the default config.
        let mut l = two_branch_latch_loop();
        let mut pass = X86BranchLayout::with_config(admit_exact, X86BranchLayoutConfig::default());
        assert!(
            pass.run(&mut l),
            "latch rule fires under the default config"
        );
        let (cc, t, jf) = terminator_shape(&l, Block(2));
        assert_eq!(cc, X86CondCode::L);
        assert_eq!(t, Block(1), "back-edge rides the jcc");
        assert_eq!(jf, Block(3), "exit rides the elidable jmp");
    }

    #[test]
    fn fallthrough_only_config_skips_the_latch() {
        // Symmetric guard: a two-branch latch is classified by the latch arm
        // (its `jmp` back-edge targets the header), so with `latch_rule` off
        // it is left untouched even though `fallthrough_rule` is on — the
        // fall-through arm never sees a latch block.
        let mut l = two_branch_latch_loop();
        let before = terminator_shape(&l, Block(2));
        let mut pass = X86BranchLayout::with_config(
            admit_exact,
            X86BranchLayoutConfig {
                latch_rule: false,
                fallthrough_rule: true,
                cold_trap_rule: false,
            },
        );
        assert!(!pass.run(&mut l), "latch rule off => latch untouched");
        assert_eq!(terminator_shape(&l, Block(2)), before);
    }
}
