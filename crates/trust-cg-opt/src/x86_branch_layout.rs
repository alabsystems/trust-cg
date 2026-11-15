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
//! * **Loop-exit rule** (DEFAULT ON — profile-independent) — when the block
//!   `B` and its `jcc` target `T` both lie inside a natural loop that the
//!   `jmp` target `F` is OUTSIDE of (the `jmp` rides a genuine loop-exit
//!   edge), and `T` is the layout successor, the swap puts the exit edge on
//!   the (rarely-taken) conditional branch and lets the in-loop edge fall
//!   through — the `jmp T` to the layout successor elides to ZERO bytes.
//!   Per entry into the loop the in-loop edge executes at least n−1 times
//!   for n executions of `B` while the exit edge executes at most once, so
//!   the swap converts n−1 taken branches into at most one — the same
//!   justification class as the latch rule ("a loop body runs many times by
//!   definition"), no profile guess. This is the p6-SAFE SUBSET of the
//!   refuted fallthrough rule below: a match dispatch inside a loop keeps
//!   BOTH targets in the loop body (no loop-exit edge), so the `F ∉ loop`
//!   condition excludes exactly the shape that regressed p6_branch_match.
//! * **Fallthrough rule** (DEFAULT OFF — profile-dependent heuristic) — when
//!   `T` is the layout successor (and `F` is not), the swap makes the
//!   trailing `jmp` target the layout successor, which the encoder elides to
//!   ZERO bytes. This only *helps* if `T` is the hot successor; with no
//!   profile data the pass assumes layout-successor == hot, which is WRONG
//!   for match-heavy code (measured: p6_branch_match +4.3% — a real
//!   regression). DEFERRED off in [`X86BranchLayoutConfig::default`] pending
//!   profile data / a static hotness estimator; opt in for A/B experiments.
//! * **Cold-arm sink rule** (DEFAULT OFF — opt-in soak) — the fourth rule and
//!   the first `block_order` mutation in the x86 lane. For an intra-loop
//!   diamond `B: ...; jcc cc, T; jmp F` where `T` is `B`'s layout successor,
//!   `F` follows `T`, the `jcc` arm `T` contains a CALL and the `jmp` arm `F`
//!   contains none, move `T` out of line (immediately after the loop's last
//!   laid-out body block): `B`'s `jmp F` becomes a jump to the layout
//!   successor — elided to ZERO bytes — so the call-free arm falls through
//!   on every iteration while the call arm pays one extra taken `jmp` when
//!   (rarely) executed. NO condition-code inversion, NO successor mutation:
//!   a pure `block_order` permutation plus at most ONE materialized
//!   `jmp <old fall-through>` at the seam the move opens. The hotness
//!   assumption is the NEGATION of the refuted fallthrough rule, justified
//!   ONLY by the call-evidence gate (a call-bearing arm inside a hot loop is
//!   the grow-on-push / slow-path shape), so the two rules must never fire on
//!   the same block. See [`X86BranchLayoutConfig::cold_arm_sink_rule`].
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
//! generic core for the future task. General block reordering remains
//! deferred; the ONE `block_order` mutation this pass performs is the
//! narrowly-gated cold-arm sink above, which is self-checked against a
//! mirror of the pipeline's fall-through layout validator and rolled back
//! on any doubt.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::InstFlags;
use trust_cg_ir::x86_64_ops::{X86CondCode, X86Opcode};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelBlock, X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::x86_trap_block::is_pure_trap_block;

use crate::generic_branch_layout::analyze_branch_layout;
use crate::mach_view::{CfgAnalysis, GenericLoop};
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
/// * **`loop_exit_rule`** — profile-INDEPENDENT. A `jcc T; jmp F` whose `jmp`
///   rides a genuine loop-exit edge (`B` and `T` in a natural-loop body, `F`
///   outside it) with `T` the layout successor: inverting lets the in-loop
///   edge (executed ≥ n−1 times per loop entry) fall through and puts the
///   exit edge (executed ≤ 1 time per loop entry) on the conditional branch.
///   Same justification class as the latch rule; see the field docs.
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
    /// Apply the LOOP-EXIT fall-through inversion: for a terminal
    /// `jcc T; jmp F` in block `B`, invert iff some natural loop `L` has
    /// `B ∈ L.body`, `T ∈ L.body` and `F ∉ L.body` (the unconditional `jmp`
    /// rides a genuine loop-exit edge while the conditional branch stays in
    /// the loop) AND `T` is the layout successor — so after the swap the
    /// in-loop edge is the elided-to-zero-bytes `jmp <layout-next>` and the
    /// exit rides the (rarely-taken) `jcc`.
    ///
    /// Profitability is profile-FREE, the same justification class as
    /// `latch_rule` ("a loop body runs many times by definition"): per entry
    /// into `L` the in-loop edge `B → T` executes at least n−1 times for n
    /// executions of `B`, while the exit edge `B → F` executes at most once.
    /// The swap converts those n−1 taken `jcc`s into fall-throughs at the
    /// cost of at most one taken branch on exit — a strict win with no
    /// profile assumption.
    ///
    /// This is the p6-SAFE SUBSET of the refuted `fallthrough_rule`: that
    /// rule assumed layout-next == hot with NO loop evidence and regressed
    /// p6_branch_match +4.3%. A match dispatch inside a loop keeps both
    /// targets in the loop body — there is no loop-exit edge — so the
    /// `F ∉ L.body` condition excludes exactly that shape. Default ON
    /// (kill switch: `TCG_NO_X86_LOOP_EXIT_LAYOUT` in the pipeline).
    pub loop_exit_rule: bool,
    /// Apply COLD-ARM SINKING (rule 4): for an intra-loop diamond
    /// `B: ...; jcc cc, T; jmp F` where `T` is `B`'s layout successor and
    /// `F` follows `T`, move `T` out of line — immediately after the loop's
    /// last laid-out body block — so `B`'s trailing `jmp F` targets the new
    /// layout successor and the encoder elides it to ZERO bytes: the kept arm
    /// `F` falls through on every iteration and the sunk arm `T` pays one
    /// extra taken `jmp` when (rarely) executed.
    ///
    /// This is a pure `block_order` permutation plus at most ONE materialized
    /// `jmp` (when the block that newly precedes the sunk arm's destination
    /// relied on implicit fall-through) — NO condition-code inversion, NO
    /// successor mutation, no instruction is otherwise touched. The hotness
    /// assumption ("the `jcc` arm is cold") is the NEGATION of the refuted
    /// `fallthrough_rule` heuristic and is justified ONLY by CALL EVIDENCE:
    /// the sunk arm must contain a call and the kept arm none (the
    /// grow-on-push / slow-path shape), so the rule never fires on the
    /// data-dependent p6 match-dispatch diamond (no call in its arms), and
    /// its `F ∈ loop` requirement makes it structurally disjoint from
    /// `loop_exit_rule` (`F ∉ loop`). Every applied sink is self-checked
    /// against a mirror of the pipeline's fall-through layout validator and
    /// ROLLED BACK (never a compile failure) on any violation.
    ///
    /// Default OFF — opt-in soak (`TCG_X86_COLD_ARM_SINK=1` in the pipeline;
    /// this is the first `block_order` mutation in the x86 lane and its win
    /// is a ratio argument, not strict dominance). The post-A/B flip shape is
    /// a `TCG_NO_X86_COLD_ARM_SINK` kill switch.
    pub cold_arm_sink_rule: bool,
}

impl Default for X86BranchLayoutConfig {
    /// Production default: latch rule ON (profile-independent win), cold-trap
    /// rule ON (profile-free-correct — the jmp sink is a never-taken `Ud2`),
    /// loop-exit rule ON (profile-independent — the loop structure itself is
    /// the hotness evidence), generic fall-through rule OFF (profile-free
    /// heuristic that regressed a real match-heavy program), cold-arm sink
    /// OFF (opt-in soak — the first `block_order` mutation in the x86 lane;
    /// `TCG_X86_COLD_ARM_SINK=1` in the pipeline enables it).
    fn default() -> Self {
        Self {
            latch_rule: true,
            fallthrough_rule: false,
            cold_trap_rule: true,
            loop_exit_rule: true,
            cold_arm_sink_rule: false,
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
    /// Number of cold arms sunk out of line by the most recent [`run`]
    /// invocation (diagnostics/tests only — the zero-fire-trap accept
    /// counter; `TCG_X86_COLD_ARM_SINK_LOG=1` prints one stderr line per
    /// accepted sink).
    ///
    /// [`run`]: X86MachinePass::run
    pub last_run_sinks: usize,
}

impl X86BranchLayout {
    /// Create the pass with the given inversion-admission callback and ALL
    /// rules enabled. Retained for unit tests that exercise each rule; the
    /// production pipeline uses [`X86BranchLayout::with_config`] with the
    /// [`X86BranchLayoutConfig::default`] policy.
    pub fn new(admit_inversion: CcInversionAdmit) -> Self {
        Self::with_config(
            admit_inversion,
            X86BranchLayoutConfig {
                latch_rule: true,
                fallthrough_rule: true,
                cold_trap_rule: true,
                loop_exit_rule: true,
                cold_arm_sink_rule: true,
            },
        )
    }

    /// Create the pass with an explicit rule configuration.
    pub fn with_config(admit_inversion: CcInversionAdmit, config: X86BranchLayoutConfig) -> Self {
        Self {
            admit_inversion,
            config,
            last_run_swaps: 0,
            last_run_sinks: 0,
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
        self.last_run_sinks = 0;
        if func.block_order.len() < 2 {
            return false;
        }

        // Facts from the OPT-1 generic core: candidate `jcc T; jmp F` exits
        // (with layout-successor classification) and natural loops.
        let report = analyze_branch_layout(func);
        if report.cond_then_jump_exits.is_empty() && !self.config.cold_arm_sink_rule {
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
                //
                // ⚑ UNLESS the `jmp` back-edge is already the layout successor.
                // The rule's whole premise is that a back-edge riding the
                // unconditional `jmp` costs a taken branch; when the header is
                // the NEXT laid-out block the encoder elides that `jmp`, so the
                // back-edge costs ZERO and swapping would turn a free
                // fall-through into a taken `jcc` — strictly worse on every
                // path. This is the same guard the generic fall-through rule
                // below already carries, for the same reason.
                //
                // That layout was unreachable until `x86_loop_top` began
                // placing a latch immediately before its header, which is why
                // the omission never bit: at O3 the pass manager runs to
                // FIXPOINT, so without this the two rules flip the same pair
                // every iteration and the emitted orientation is decided by
                // the parity of the iteration budget, not by either rule.
                Some(&(header, _)) if jump_target == header => {
                    self.config.latch_rule && !exit.jump_is_layout_next
                }
                // Non-latch two-way exit. Three rules can fire here:
                //
                //  * Cold-trap rule (profile-FREE-correct, default ON): the
                //    `jmp` target is a `Ud2`-only trap block (never reached in
                //    a correct program) and the `jcc` target is the layout
                //    successor. Inverting moves the never-taken trap onto the
                //    conditional branch and lets the hot path fall through —
                //    strictly better on both paths, no profile assumption.
                //  * Loop-exit rule (profile-INDEPENDENT, default ON): the
                //    `jmp` rides a genuine loop-exit edge (block and `jcc`
                //    target inside a natural-loop body, `jmp` target outside
                //    it) and the `jcc` target is the layout successor. Per
                //    loop entry the in-loop edge runs ≥ n−1 times and the
                //    exit edge ≤ 1 time, so putting the in-loop edge on the
                //    (elided) fall-through wins with no profile guess — the
                //    p6-safe subset of the fallthrough rule below. Note the
                //    `jcc`-target-is-layout-next requirement makes the swap
                //    self-limiting: afterwards the `jcc` targets the exit,
                //    so the rule cannot re-fire (no oscillation).
                //  * Generic fallthrough rule (profile-dependent heuristic,
                //    default OFF): same shape but with an arbitrary (possibly
                //    hot) `jmp` sink and NO loop evidence. Requires the `jmp`
                //    target NOT already be the layout successor (else the
                //    encoder already elides it and swapping would regress).
                _ => {
                    (self.config.cold_trap_rule
                        && exit.invertible_to_fallthrough
                        && block_is_cold_trap(func, jump_target))
                        || (self.config.loop_exit_rule
                            && exit.invertible_to_fallthrough
                            && jmp_rides_a_loop_exit_edge(
                                &cfg,
                                exit.block,
                                cond_target,
                                jump_target,
                            ))
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

        // Rule 4 — COLD-ARM SINKING. Runs STRICTLY AFTER the swap-application
        // loop above and derives every layout fact from the LIVE
        // `func.block_order` (the `analyze_branch_layout` report is stale
        // once swaps have been applied — its layout-successor facts describe
        // the pre-swap terminators). The swap rules never touch
        // `block_order`, and the sink phase never touches `successors`, so
        // the loop facts in `cfg` (successor-derived) stay valid throughout.
        //
        // Disjointness: the sink phase must never fire on a block one of the
        // three swap rules rewrote this run — the swapped set is passed in
        // and every candidate touching it is declined. (`loop_exit_rule` is
        // additionally structurally disjoint: it requires `F` OUTSIDE the
        // loop, the sink requires `F` inside it.)
        if self.config.cold_arm_sink_rule {
            let swapped_blocks: HashSet<Block> = planned.iter().map(|s| s.block).collect();
            self.last_run_sinks = apply_cold_arm_sinks(func, &cfg, &swapped_blocks);
        }

        self.last_run_swaps > 0 || self.last_run_sinks > 0
    }
}

/// True iff some natural loop in `cfg` contains `block` and `cond_target` but
/// NOT `jump_target` — i.e. the terminal `jmp` rides a genuine loop-exit edge
/// while the conditional branch stays inside the loop (the loop-exit rule's
/// structural hotness evidence).
///
/// Nested loops: ANY containing loop suffices. An edge cannot exit an outer
/// loop while staying inside an inner one (an inner body is a subset of every
/// enclosing body, so `F ∈ inner ⇒ F ∈ outer`); therefore when the edge exits
/// only the innermost loop, that loop is the unique witness, and when it
/// exits several nested loops every exited one qualifies — the "in-loop edge
/// executes ≥ n−1 times per loop entry" argument holds for the innermost
/// witness regardless of which one is found first.
fn jmp_rides_a_loop_exit_edge(
    cfg: &CfgAnalysis<Block>,
    block: Block,
    cond_target: Block,
    jump_target: Block,
) -> bool {
    cfg.loops.iter().any(|lp| {
        lp.body.contains(&block)
            && lp.body.contains(&cond_target)
            && !lp.body.contains(&jump_target)
    })
}

/// True iff `block` is a provably-COLD trap sink: the shared pure-trap
/// predicate (`crate::x86_trap_block`) — a no-successor block that is exactly
/// `[Ud2]` or `[Call abort, Ud2]` modulo pseudo padding. These are the
/// bounds-check / null-check / panic=abort failure exits (a correct program
/// never transfers control into them), so a layout that puts the trap on a
/// never-taken conditional branch is a pure win — the cold-trap rule's
/// soundness rests on this being a genuine dead-end sink, not on any profile
/// estimate. Both shapes have no successors (they die), so no edge
/// probability is being assumed away. Any other real instruction means the
/// block does work — not a pure trap sink — and fails closed (not cold).
fn block_is_cold_trap(func: &X86ISelFunction, block: Block) -> bool {
    is_pure_trap_block(func, block)
}

// ===========================================================================
// Rule 4 — cold-arm sinking (block_order permutation; opt-in)
// ===========================================================================

/// Minimum number of encoded (non-trailing-pseudo-class) instructions the
/// sunk arm must contain (firing conjunct F10). Sinking a tiny arm perturbs
/// layout for negligible out-of-line benefit; a genuine call arm carries at
/// least arg setup + the call + result handling + its `jmp`.
const COLD_ARM_SINK_MIN_INSTS: usize = 4;

/// The ENCODER's trailing-pseudo class — the exact opcode set the encoder
/// skips when deciding whether a block-trailing `jmp <layout-next>` elides
/// (`trust-cg-codegen` x86_64/pipeline.rs, fall-through elision: "only
/// skipped pseudos after it in the block", matching `{Nop, Phi, StackAlloc}`).
///
/// Deliberately NOT [`X86Opcode::is_pseudo`]: that predicate is WIDER (it
/// also covers mask-extract/select and the Trap*Exact carriers, which expand
/// to real code at encode time), so using it here would claim an elision the
/// encoder will not perform. And deliberately not a terminator
/// classification: the mach-view classifier does not skip pseudos at all.
/// The firing rule must mirror the consumer that cashes the win — the
/// encoder — or the sink fires on shapes whose `jmp` still encodes.
fn is_encoder_trailing_pseudo(op: X86Opcode) -> bool {
    matches!(op, X86Opcode::Nop | X86Opcode::Phi | X86Opcode::StackAlloc)
}

/// Index of the last instruction the encoder would EMIT (i.e. the last one
/// outside the trailing-pseudo class), or `None` for an all-pseudo block.
fn last_encoded_inst_idx(block: &X86ISelBlock) -> Option<usize> {
    block
        .insts
        .iter()
        .rposition(|inst| !is_encoder_trailing_pseudo(inst.opcode))
}

/// True iff `inst` is a call — the cold-evidence predicate (F9). Checks the
/// instruction's stamped flags AND the opcode set (belt and braces: for the
/// kept arm a MISSED call would fire the rule on a possibly-hot call arm, so
/// the union errs conservative on both sides).
fn inst_is_call(inst: &X86ISelInst) -> bool {
    inst.flags.contains(InstFlags::IS_CALL)
        || matches!(
            inst.opcode,
            X86Opcode::Call | X86Opcode::CallR | X86Opcode::CallM
        )
}

/// The VALIDATOR's hard-terminator predicate — mirrors
/// `validate_x86_function_layout_impl` (`trust-cg-codegen`
/// x86_64/pipeline.rs): the last non-pseudo instruction (by
/// [`X86Opcode::is_pseudo`], the validator's notion) is an unconditional
/// control transfer, so the block contributes NO implicit fall-through edge.
/// Used to decide whether a block whose layout successor the sink changes
/// needs a materialized `jmp` — this must be the validator's predicate, not
/// the encoder's, because it is the validator's implicit-edge simulation the
/// moved layout has to satisfy.
fn validator_hard_terminated(block: &X86ISelBlock) -> bool {
    block
        .insts
        .iter()
        .rev()
        .find(|inst| !inst.opcode.is_pseudo())
        .is_some_and(|inst| {
            matches!(
                inst.opcode,
                X86Opcode::Jmp | X86Opcode::Ret | X86Opcode::Ud2 | X86Opcode::JmpR
            )
        })
}

/// One planned cold-arm sink. Every field is computed from the LIVE function
/// state BEFORE any mutation (in particular `anchor_jmp` captures the
/// anchor's OLD layout successor).
struct PlannedSink {
    /// The diamond entry `B` (kept in place; its `jmp F` becomes elidable).
    block: Block,
    /// The sunk call arm `T` (`B`'s `jcc` target and current layout
    /// successor).
    arm: Block,
    /// The kept call-free arm `F` (`B`'s `jmp` target; falls through after
    /// the move).
    kept: Block,
    /// The witness loop's LAST laid-out body block; `arm` is re-inserted
    /// immediately after it (never at the raw end of `block_order` — the
    /// tail block may lack a layout successor).
    anchor: Block,
    /// `Some(X)` iff the anchor is not hard-terminated and therefore reaches
    /// its OLD layout successor `X` by implicit fall-through: a `jmp X` must
    /// be materialized at the anchor's end (the ONE instruction this rule may
    /// add; `X` is already in the anchor's successor set). `None` when the
    /// anchor is hard-terminated and no seam repair is needed.
    anchor_jmp: Option<Block>,
}

/// Plan one cold-arm sink for `candidate` (the diamond entry `B`), or `None`
/// if ANY firing conjunct fails. All layout indices come from the LIVE
/// `func.block_order`; nothing is mutated here.
fn plan_cold_arm_sink(
    func: &X86ISelFunction,
    cfg: &CfgAnalysis<Block>,
    swapped_blocks: &HashSet<Block>,
    candidate: Block,
) -> Option<PlannedSink> {
    let order = &func.block_order;
    let pos_b = order.iter().position(|&b| b == candidate)?;
    let b_blk = func.blocks.get(&candidate)?;

    // F1 + F3 — exact shape at the (future) mutation site: the block ends
    // `jcc cc, T; jmp F` with the `jmp` LAST per the ENCODER's
    // trailing-pseudo predicate (only {Nop, Phi, StackAlloc} may follow it),
    // the `jcc` immediately before it, and the successor metadata exactly
    // {T, F}. Anything unexpected is skipped, never touched.
    let jump_idx = last_encoded_inst_idx(b_blk)?;
    let jump_inst = &b_blk.insts[jump_idx];
    if jump_inst.opcode != X86Opcode::Jmp || jump_idx == 0 {
        return None;
    }
    let [X86ISelOperand::Block(kept)] = jump_inst.operands.as_slice() else {
        return None;
    };
    let kept = *kept;
    let cond_inst = &b_blk.insts[jump_idx - 1];
    if cond_inst.opcode != X86Opcode::Jcc {
        return None;
    }
    let [X86ISelOperand::CondCode(_), X86ISelOperand::Block(arm)] = cond_inst.operands.as_slice()
    else {
        return None;
    };
    let arm = *arm;
    if arm == kept {
        return None;
    }
    if b_blk.successors.len() != 2
        || !b_blk.successors.contains(&arm)
        || !b_blk.successors.contains(&kept)
    {
        return None;
    }

    // F2 — the arm is B's layout successor and the kept arm follows it, so
    // after the move B's layout successor IS the `jmp` target and the
    // encoder elides the `jmp` to zero bytes. (Without `F` directly behind
    // `T` the move would change nothing on the hot path — pure churn.)
    if order.get(pos_b + 1) != Some(&arm) || order.get(pos_b + 2) != Some(&kept) {
        return None;
    }
    let pos_arm = pos_b + 1;

    // Disjointness — never fire on a block one of the swap rules rewrote in
    // this same run (the sink's hotness assumption is the NEGATION of the
    // fallthrough rule's; the two must never compose on one diamond).
    if swapped_blocks.contains(&candidate)
        || swapped_blocks.contains(&arm)
        || swapped_blocks.contains(&kept)
    {
        return None;
    }

    // F4 — {B, T, F} all inside one natural-loop body (the loop is the
    // hotness carrier: `B` executes per iteration, so the elided `jmp` pays
    // every iteration while the sunk arm's extra `jmp` pays only when the
    // cold arm actually runs). Innermost witness wins for the placement.
    let mut witness: Option<&GenericLoop<Block>> = None;
    for lp in &cfg.loops {
        if lp.body.contains(&candidate)
            && lp.body.contains(&arm)
            && lp.body.contains(&kept)
            && witness.is_none_or(|best| lp.depth > best.depth)
        {
            witness = Some(lp);
        }
    }
    let lp = witness?;

    // F5 — B is not a latch and neither arm is a header (of ANY loop):
    // latches and headers are the anchors of the latch/loop-exit rules and
    // of loop-shape recognizers downstream; their layout is not this rule's
    // to perturb. (Largely shadowed by F2/F6 in well-formed layouts —
    // defense in depth.)
    for l in &cfg.loops {
        if l.latches.contains(&candidate) || l.header == arm || l.header == kept {
            return None;
        }
    }

    // F6 — the arm's ONLY CFG predecessor is B: sinking a shared block would
    // stretch other predecessors' paths. (`cfg.preds` is derived from
    // successor metadata, which neither the swap rules nor this phase ever
    // write, so the phase-entry analysis stays valid.)
    if cfg.preds.get(&arm).map(Vec::as_slice) != Some(&[candidate]) {
        return None;
    }

    // F7 — the arm is a single-block region: it ends `jmp J` (last encoded
    // instruction), carries exactly that one control transfer, its successor
    // metadata is exactly [J], and J stays inside the witness loop. A block
    // that could fall through, or branch anywhere else, cannot be moved
    // alone.
    let arm_blk = func.blocks.get(&arm)?;
    let arm_jmp_idx = last_encoded_inst_idx(arm_blk)?;
    let arm_jmp = &arm_blk.insts[arm_jmp_idx];
    if arm_jmp.opcode != X86Opcode::Jmp {
        return None;
    }
    let [X86ISelOperand::Block(join)] = arm_jmp.operands.as_slice() else {
        return None;
    };
    if arm_blk.successors.as_slice() != [*join] || !lp.body.contains(join) {
        return None;
    }
    let control_transfers = arm_blk
        .insts
        .iter()
        .filter(|inst| {
            matches!(
                inst.opcode,
                X86Opcode::Jmp | X86Opcode::Jcc | X86Opcode::JmpR | X86Opcode::Ret | X86Opcode::Ud2
            )
        })
        .count();
    if control_transfers != 1 {
        return None;
    }

    // F8 — the arm is not the entry block (entry-first is a validator
    // invariant; unreachable here since `arm` sits at layout index ≥ 1, kept
    // as defense in depth), not a jump-table target, and not part of any EH
    // structure (landing pad or protected call site) — those blocks'
    // addresses/ranges carry meaning beyond the plain CFG.
    if Some(&arm) == order.first() {
        return None;
    }
    if func.jump_tables.iter().any(|jt| jt.targets.contains(&arm)) {
        return None;
    }
    if func.eh_info.landing_pads.iter().any(|pad| pad.block == arm)
        || func
            .eh_info
            .call_sites
            .iter()
            .any(|cs| cs.call_block == arm || cs.landing_pad_block == arm)
    {
        return None;
    }

    // F9 — COLD EVIDENCE, the entire justification: the sunk arm contains at
    // least one call and the kept arm contains NONE. This is the negation of
    // the refuted profile-free "layout-next == hot" guess, grounded in the
    // one static fact the corpus supports (a call-bearing arm inside a hot
    // integer loop is the slow path: grow-on-push, error exits, refill).
    if !arm_blk.insts.iter().any(inst_is_call) {
        return None;
    }
    let kept_blk = func.blocks.get(&kept)?;
    if kept_blk.insts.iter().any(inst_is_call) {
        return None;
    }

    // F10 — size floor on the sunk arm.
    let arm_encoded_insts = arm_blk
        .insts
        .iter()
        .filter(|inst| !is_encoder_trailing_pseudo(inst.opcode))
        .count();
    if arm_encoded_insts < COLD_ARM_SINK_MIN_INSTS {
        return None;
    }

    // F11 — progress guard: some loop-body block is laid out AFTER the arm,
    // so the move is a genuine displacement (and cannot re-fire — after the
    // sink the arm is no longer B's layout successor, failing F2 forever).
    // The LAST such block is the anchor: the arm lands immediately after the
    // loop's laid-out span.
    let anchor_pos = (pos_arm + 1..order.len())
        .filter(|&i| lp.body.contains(&order[i]))
        .max()?;
    let anchor = order[anchor_pos];

    // F12 — the move must actually REMOVE the arm from the hot path. When the
    // anchor IS the kept arm, the arm is merely swapped with its immediate
    // neighbour and stays inside the loop's laid-out span: measured on h1/h3/
    // h4 (2026-08-30 objdump A/B), that degenerate case ADDS one in-loop `jmp`
    // per program (h3 also +32 bytes of `main`), while the one genuine sink
    // (h2, anchor != kept) removed 5 instructions, 4 of them in-loop. The
    // pass's own ACCEPT log cannot see this — it reports `anchor_jmp=None`
    // (the rule materialized nothing) while the ENCODER stops eliding a
    // fall-through `jmp` that the permutation made non-adjacent. Only
    // disassembly shows it, which is why this guard is structural rather than
    // a cost model: an arm whose landing site is the very block it branches
    // past has not been sunk out of anything.
    if anchor == kept {
        return None;
    }

    // Seam repair, decided from OLD layout facts before any mutation: after
    // inserting the arm behind the anchor, the anchor's layout successor
    // changes. If the anchor is hard-terminated (validator's predicate) no
    // implicit edge existed and nothing is owed. Otherwise the anchor reached
    // its old layout successor X by fall-through and a `jmp X` must be
    // materialized (X is necessarily already in its successor metadata — the
    // function validated with that implicit edge). The sunk arm itself ends
    // in `jmp` (F7), and B ends in `jmp` (F1), so no other block's implicit
    // edges change: at most this ONE instruction is added.
    let anchor_blk = func.blocks.get(&anchor)?;
    let anchor_jmp = if validator_hard_terminated(anchor_blk) {
        None
    } else {
        let old_next = order.get(anchor_pos + 1).copied()?;
        if !anchor_blk.successors.contains(&old_next) {
            return None;
        }
        Some(old_next)
    };

    Some(PlannedSink {
        block: candidate,
        arm,
        kept,
        anchor,
        anchor_jmp,
    })
}

/// Mirror of the pipeline's fall-through layout simulation
/// (`validate_x86_function_layout_impl`, symbolic-authority arm, trust-cg-
/// codegen x86_64/pipeline.rs): entry-first, `block_order` free of
/// duplicates and closed over the block map, and — the load-bearing part —
/// every laid-out block's successor METADATA equal to its semantic control
/// edges: explicit `jmp`/`jcc` block targets, the jump-table target set of a
/// `JmpR` dispatch, the implicit fall-through edge of a
/// non-hard-terminated block, and EH unwind edges. Run over the function
/// AFTER a sink is applied; any violation rolls the sink back (strictly more
/// conservative than the real validator, which would fail the compile).
fn layout_fallthrough_integrity(func: &X86ISelFunction) -> Result<(), String> {
    if func.block_order.first() != Some(&Block(0)) {
        return Err(format!(
            "block_order must start with the entry block, got {:?}",
            func.block_order.first()
        ));
    }
    let mut seen: HashSet<Block> = HashSet::with_capacity(func.block_order.len());
    for &block_id in &func.block_order {
        if !func.blocks.contains_key(&block_id) {
            return Err(format!("block_order contains unmapped block {block_id:?}"));
        }
        if !seen.insert(block_id) {
            return Err(format!("block_order duplicates block {block_id:?}"));
        }
    }

    // One entry per laid-out block, keyed exactly by `block_order`. Each
    // block's edge set is built locally and inserted ONCE: `block_order` is
    // duplicate-free (rejected above), so no key is ever inserted twice and
    // every block reaches the comparison loop below with a populated entry
    // — the same map the old "pre-seed empty sets, then get_mut" shape
    // produced, without a lookup that could fail.
    let mut expected: HashMap<Block, HashSet<Block>> =
        HashMap::with_capacity(func.block_order.len());
    for (layout_index, &block_id) in func.block_order.iter().enumerate() {
        let block = &func.blocks[&block_id];
        let mut edges: HashSet<Block> = HashSet::new();
        for inst in &block.insts {
            if matches!(inst.opcode, X86Opcode::Jmp | X86Opcode::Jcc) {
                for operand in &inst.operands {
                    if let X86ISelOperand::Block(target) = operand {
                        edges.insert(*target);
                    }
                }
            }
            // An indirect jump-table dispatch (JmpR) carries no Block
            // operand; its control edges are the targets of the jump table
            // its LeaRip references — mirror the validator's cross-check.
            if inst.opcode == X86Opcode::JmpR {
                let jt_idx = block.insts.iter().find_map(|i| {
                    if i.opcode == X86Opcode::LeaRip {
                        i.operands.iter().find_map(|op| match op {
                            X86ISelOperand::JumpTableIndex(idx) => Some(*idx),
                            _ => None,
                        })
                    } else {
                        None
                    }
                });
                if let Some(idx) = jt_idx
                    && let Some(jt) = func.jump_tables.get(idx as usize)
                {
                    for &tgt in &jt.targets {
                        edges.insert(tgt);
                    }
                }
            }
        }
        if !validator_hard_terminated(block)
            && let Some(&fallthrough) = func.block_order.get(layout_index + 1)
        {
            edges.insert(fallthrough);
        }
        expected.insert(block_id, edges);
    }
    for call_site in &func.eh_info.call_sites {
        // The real validator unwraps here; the mirror fails soft (=> the
        // sink rolls back) on an un-laid-out EH call block.
        let Some(edges) = expected.get_mut(&call_site.call_block) else {
            return Err(format!(
                "EH call site block {:?} is not laid out",
                call_site.call_block
            ));
        };
        edges.insert(call_site.landing_pad_block);
    }
    for &block_id in &func.block_order {
        let block = &func.blocks[&block_id];
        let actual: HashSet<Block> = block.successors.iter().copied().collect();
        if actual.len() != block.successors.len() {
            return Err(format!(
                "block {:?} contains duplicate successor metadata: {:?}",
                block_id, block.successors
            ));
        }
        if actual != expected[&block_id] {
            return Err(format!(
                "block {:?} successor metadata {:?} does not match semantic control edges {:?}",
                block_id, actual, expected[&block_id]
            ));
        }
    }
    Ok(())
}

/// Apply every admissible cold-arm sink: plan → snapshot → apply →
/// mirror-check → commit | ROLLBACK. Returns the number of committed sinks.
/// A failed self-check restores the snapshot and silently declines — an
/// optimization gate, never a compile failure, never a panic.
fn apply_cold_arm_sinks(
    func: &mut X86ISelFunction,
    cfg: &CfgAnalysis<Block>,
    swapped_blocks: &HashSet<Block>,
) -> usize {
    let log_accepts = crate::env_lock::var_os("TCG_X86_COLD_ARM_SINK_LOG").is_some();

    // Candidate ids from the phase-entry order (ids are stable; positions are
    // re-derived from the live order inside each plan).
    let candidates: Vec<Block> = func.block_order.clone();
    let mut sinks = 0usize;
    for candidate in candidates {
        let Some(plan) = plan_cold_arm_sink(func, cfg, swapped_blocks, candidate) else {
            continue;
        };

        // Snapshot exactly what the apply below may touch: the layout and
        // (iff a seam jmp is owed) the anchor's instruction vector.
        let order_before = func.block_order.clone();
        let anchor_insts_before = plan
            .anchor_jmp
            .map(|_| func.blocks[&plan.anchor].insts.clone());

        if let Some(target) = plan.anchor_jmp {
            // Invariant: `plan_cold_arm_sink` resolved this very anchor with
            // `func.blocks.get(&anchor)?` (returning None otherwise), and
            // `func` is only READ between that plan and this apply (the two
            // snapshot clones above) — so the anchor is still mapped here.
            // Not softened to `if let`: a missing anchor here is a plan/apply
            // desynchronisation bug, and silently skipping the seam jmp would
            // hide it behind the mirror's rollback instead of surfacing it.
            func.blocks
                .get_mut(&plan.anchor)
                .expect("planned anchor exists (checked during planning)")
                .insts
                .push(X86ISelInst::new(
                    X86Opcode::Jmp,
                    vec![X86ISelOperand::Block(target)],
                ));
        }
        // The move itself: retain + insert immediately after the anchor
        // (`move_block_after` precedent, loop_latch_layout).
        func.block_order.retain(|&b| b != plan.arm);
        let inserted = match func.block_order.iter().position(|&b| b == plan.anchor) {
            Some(pos) => {
                func.block_order.insert(pos + 1, plan.arm);
                true
            }
            None => false,
        };

        // Self-check: the permuted layout must satisfy the same fall-through
        // simulation the pipeline validator enforces. On ANY doubt, restore
        // the snapshot and decline this sink.
        let intact = inserted
            && func.block_order.len() == order_before.len()
            && layout_fallthrough_integrity(func).is_ok();
        if !intact {
            func.block_order = order_before;
            if let Some(insts) = anchor_insts_before
                && let Some(anchor_blk) = func.blocks.get_mut(&plan.anchor)
            {
                anchor_blk.insts = insts;
            }
            continue;
        }

        sinks += 1;
        if log_accepts {
            eprintln!(
                "x86-cold-arm-sink: ACCEPT fn={} entry={:?} arm={:?} kept={:?} anchor={:?} anchor_jmp={:?}",
                func.name, plan.block, plan.arm, plan.kept, plan.anchor, plan.anchor_jmp
            );
        }
    }
    sinks
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
    fn latch_rule_declines_a_back_edge_that_already_falls_through() {
        // The layout `x86_loop_top` produces: the latch sits immediately
        // BEFORE its header, so the latch's `jmp header` is the layout
        // successor and the encoder elides it — the back-edge already costs
        // ZERO branches. Swapping would put it on a TAKEN `jcc`, which is
        // strictly worse, and at O3 (fixpoint) the two rules would flip the
        // same pair every iteration.
        let mut f = two_branch_latch_loop();
        f.block_order = vec![Block(0), Block(2), Block(1), Block(3)];

        let mut pass = X86BranchLayout::new(admit_exact);
        assert!(
            !pass.run(&mut f),
            "the latch rule must decline a back-edge that is already a fall-through"
        );
        assert_eq!(pass.last_run_swaps, 0);

        let (cc, t, jf) = terminator_shape(&f, Block(2));
        assert_eq!(cc, X86CondCode::GE, "condition untouched");
        assert_eq!(t, Block(3), "exit stays on the jcc");
        assert_eq!(jf, Block(1), "the back-edge stays on the elidable jmp");
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
    fn default_config_is_latch_cold_trap_and_loop_exit() {
        // The production policy: profile-independent latch rule ON, cold-trap
        // fall-through inversion ON (profile-free-correct), loop-exit
        // inversion ON (profile-independent — the loop is the hotness
        // evidence), the generic profile-free fall-through heuristic
        // (regressed p6_branch_match) DEFERRED off.
        let c = X86BranchLayoutConfig::default();
        assert!(c.latch_rule, "latch rule is the default-on win");
        assert!(c.cold_trap_rule, "cold-trap inversion is default-on");
        assert!(
            c.loop_exit_rule,
            "loop-exit inversion is default-on (profile-independent)"
        );
        assert!(
            !c.fallthrough_rule,
            "generic fall-through rule is deferred off pending profile data"
        );
        assert!(
            !c.cold_arm_sink_rule,
            "cold-arm sinking is opt-in (soak) — default OFF"
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
    fn cold_trap_rule_fires_on_abort_call_trap() {
        // The bridge's `[Call abort, Ud2]` panic=abort assert block is as cold
        // as a bare `Ud2`: the rule inverts so the trap rides the never-taken
        // jcc.
        let mut f = cold_trap_diamond();
        f.blocks.get_mut(&Block(2)).unwrap().insts = vec![
            X86ISelInst::new(
                X86Opcode::Call,
                vec![X86ISelOperand::Symbol("abort".to_string())],
            ),
            X86ISelInst::new(X86Opcode::Ud2, vec![]),
        ];
        assert!(block_is_cold_trap(&f, Block(2)));
        let mut pass = X86BranchLayout::with_config(admit_exact, X86BranchLayoutConfig::default());
        assert!(
            pass.run(&mut f),
            "cold-trap inversion must fire on the abort block"
        );
        assert_eq!(pass.last_run_swaps, 1);
        let (cc, t, jf) = terminator_shape(&f, Block(0));
        assert_eq!(cc, X86CondCode::NE);
        assert_eq!(t, Block(2), "trap moved onto the (never-taken) jcc");
        assert_eq!(jf, Block(1));
    }

    #[test]
    fn cold_trap_rule_ignores_other_call_sink() {
        // `[Call exit, Ud2]`: a call to any other symbol is real work — not a
        // cold trap sink. The rule must not fire.
        let mut f = cold_trap_diamond();
        f.blocks.get_mut(&Block(2)).unwrap().insts = vec![
            X86ISelInst::new(
                X86Opcode::Call,
                vec![X86ISelOperand::Symbol("exit".to_string())],
            ),
            X86ISelInst::new(X86Opcode::Ud2, vec![]),
        ];
        assert!(!block_is_cold_trap(&f, Block(2)));
        let before = terminator_shape(&f, Block(0));
        let mut pass = X86BranchLayout::with_config(admit_exact, X86BranchLayoutConfig::default());
        assert!(
            !pass.run(&mut f),
            "cold-trap rule must not fire on a non-abort call sink"
        );
        assert_eq!(terminator_shape(&f, Block(0)), before);
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
                loop_exit_rule: false,
                cold_arm_sink_rule: false,
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
                loop_exit_rule: false,
                cold_arm_sink_rule: false,
            },
        );
        assert!(!pass.run(&mut l), "latch rule off => latch untouched");
        assert_eq!(terminator_shape(&l, Block(2)), before);
    }

    /// Top-tested loop, the loop-exit rule's target shape: b0 preheader ->
    /// b1 header (`cmp; jcc B b2; jmp b3` — the conditional edge stays in
    /// the loop and is the layout successor, the unconditional `jmp` rides
    /// the loop-exit edge) -> b2 body+latch (`add; jmp b1`) -> b3 exit.
    fn top_tested_header_loop() -> X86ISelFunction {
        let mut f = X86ISelFunction::new("top_tested".to_string(), empty_sig());
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
        // b1: header — the trip test. Exit edge on the JMP, in-loop edge on
        // the (layout-next) JCC target.
        f.push_inst(
            b1,
            X86ISelInst::new(
                X86Opcode::CmpRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(10)],
            ),
        );
        f.push_inst(b1, jcc(X86CondCode::B, b2));
        f.push_inst(b1, jmp(b3));
        // b2: body + latch, back-edge to the header.
        f.push_inst(
            b2,
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(1)],
            ),
        );
        f.push_inst(b2, jmp(b1));
        f.push_inst(b3, X86ISelInst::new(X86Opcode::Ret, vec![]));

        f.blocks.get_mut(&b0).unwrap().successors = vec![b1];
        f.blocks.get_mut(&b1).unwrap().successors = vec![b2, b3];
        f.blocks.get_mut(&b2).unwrap().successors = vec![b1];
        f
    }

    #[test]
    fn loop_exit_rule_inverts_top_tested_header() {
        // Default (production) config must invert the header: the loop-exit
        // edge moves onto the (rarely-taken) jcc and the in-loop edge rides
        // the jmp to the layout successor, which the encoder elides — one
        // fall-through per iteration instead of a taken jcc.
        let mut f = top_tested_header_loop();
        let succs_before = f.blocks[&Block(1)].successors.clone();
        let mut pass = X86BranchLayout::with_config(admit_exact, X86BranchLayoutConfig::default());
        assert!(pass.run(&mut f), "loop-exit inversion must fire by default");
        assert_eq!(pass.last_run_swaps, 1);
        let (cc, t, jf) = terminator_shape(&f, Block(1));
        assert_eq!(cc, X86CondCode::AE, "condition inverted (B -> AE)");
        assert_eq!(t, Block(3), "loop exit rides the (rarely-taken) jcc");
        assert_eq!(jf, Block(2), "in-loop edge rides the elidable jmp");
        assert_eq!(f.blocks[&Block(1)].successors, succs_before);
    }

    #[test]
    fn loop_exit_rule_is_idempotent() {
        let mut f = top_tested_header_loop();
        let mut pass = X86BranchLayout::with_config(admit_exact, X86BranchLayoutConfig::default());
        assert!(pass.run(&mut f));
        let shape_after_first = terminator_shape(&f, Block(1));
        // Second run: the jcc now targets the exit (outside every loop body,
        // and no longer the layout successor), so the rule's conditions fail
        // and no other rule wants the post-swap shape.
        assert!(!pass.run(&mut f), "second run must be a no-op");
        assert_eq!(pass.last_run_swaps, 0);
        assert_eq!(terminator_shape(&f, Block(1)), shape_after_first);
    }

    /// Loop whose header ends in an INTRA-loop diamond — BOTH branch targets
    /// stay inside the loop body (the match-dispatch shape that made the
    /// generic fallthrough rule regress p6_branch_match +4.3%). Layout:
    /// b0 preheader, b1 diamond entry, b2/b3 arms, b4 rotated latch, b5 exit.
    fn intra_loop_diamond_loop() -> X86ISelFunction {
        let mut f = X86ISelFunction::new("intra_diamond".to_string(), empty_sig());
        let (b0, b1, b2, b3, b4, b5) = (Block(0), Block(1), Block(2), Block(3), Block(4), Block(5));
        for b in [b0, b1, b2, b3, b4, b5] {
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
        // b1: data-dependent diamond INSIDE the loop — both targets in-loop.
        f.push_inst(
            b1,
            X86ISelInst::new(
                X86Opcode::CmpRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(3)],
            ),
        );
        f.push_inst(b1, jcc(X86CondCode::E, b2));
        f.push_inst(b1, jmp(b3));
        f.push_inst(b2, jmp(b4));
        f.push_inst(b3, jmp(b4));
        // b4: rotated latch — back-edge already on the jcc (the latch arm
        // leaves it alone), exit on the elidable jmp.
        f.push_inst(
            b4,
            X86ISelInst::new(
                X86Opcode::CmpRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(10)],
            ),
        );
        f.push_inst(b4, jcc(X86CondCode::L, b1));
        f.push_inst(b4, jmp(b5));
        f.push_inst(b5, X86ISelInst::new(X86Opcode::Ret, vec![]));

        f.blocks.get_mut(&b0).unwrap().successors = vec![b1];
        f.blocks.get_mut(&b1).unwrap().successors = vec![b2, b3];
        f.blocks.get_mut(&b2).unwrap().successors = vec![b4];
        f.blocks.get_mut(&b3).unwrap().successors = vec![b4];
        f.blocks.get_mut(&b4).unwrap().successors = vec![b1, b5];
        f
    }

    #[test]
    fn loop_exit_rule_ignores_intra_loop_diamond() {
        // The p6 guard: a data-dependent diamond inside a loop has NO
        // loop-exit edge — the jmp target stays in the body — so the
        // loop-exit rule must not touch it. This is exactly the shape whose
        // profile-free inversion regressed p6_branch_match and got the
        // generic fallthrough rule deferred off.
        let mut f = intra_loop_diamond_loop();
        let entry_before = terminator_shape(&f, Block(1));
        let latch_before = terminator_shape(&f, Block(4));
        let mut pass = X86BranchLayout::with_config(admit_exact, X86BranchLayoutConfig::default());
        assert!(
            !pass.run(&mut f),
            "no default rule may fire on the intra-loop diamond"
        );
        assert_eq!(terminator_shape(&f, Block(1)), entry_before);
        assert_eq!(terminator_shape(&f, Block(4)), latch_before);
    }

    #[test]
    fn loop_exit_rule_ignores_non_loop_diamond() {
        // No loop anywhere: the rule's hotness evidence is loop membership,
        // so a plain diamond is left alone even with ONLY this rule enabled
        // (isolates the rule from the cold-trap/fallthrough disjuncts).
        let mut f = diamond();
        let before = terminator_shape(&f, Block(0));
        let mut pass = X86BranchLayout::with_config(
            admit_exact,
            X86BranchLayoutConfig {
                latch_rule: false,
                fallthrough_rule: false,
                cold_trap_rule: false,
                loop_exit_rule: true,
                cold_arm_sink_rule: false,
            },
        );
        assert!(!pass.run(&mut f), "no loop evidence => no rewrite");
        assert_eq!(terminator_shape(&f, Block(0)), before);
    }

    #[test]
    fn loop_exit_rule_requires_in_loop_layout_successor() {
        // Mirrored, already-optimal header: `jcc AE exit; jmp body` — the
        // exit already rides the conditional branch and the in-loop jmp
        // target IS the layout successor (elided by the encoder). The jcc
        // target is NOT the layout successor, so the rule's fall-through
        // condition fails and nothing may fire — swapping would recreate the
        // per-iteration taken branch the rule exists to remove.
        let mut f = X86ISelFunction::new("optimal_header".to_string(), empty_sig());
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
        f.push_inst(
            b1,
            X86ISelInst::new(
                X86Opcode::CmpRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(10)],
            ),
        );
        f.push_inst(b1, jcc(X86CondCode::AE, b3));
        f.push_inst(b1, jmp(b2));
        f.push_inst(
            b2,
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(1)],
            ),
        );
        f.push_inst(b2, jmp(b1));
        f.push_inst(b3, X86ISelInst::new(X86Opcode::Ret, vec![]));
        f.blocks.get_mut(&b0).unwrap().successors = vec![b1];
        f.blocks.get_mut(&b1).unwrap().successors = vec![b3, b2];
        f.blocks.get_mut(&b2).unwrap().successors = vec![b1];

        let before = terminator_shape(&f, Block(1));
        let mut pass = X86BranchLayout::with_config(admit_exact, X86BranchLayoutConfig::default());
        assert!(
            !pass.run(&mut f),
            "already-optimal header must be left alone"
        );
        assert_eq!(terminator_shape(&f, Block(1)), before);
    }

    #[test]
    fn loop_exit_rejected_admission_skips_the_rewrite() {
        // The loop-exit rule routes through the SAME admission gate as every
        // other rule: no admitted inversion, no rewrite (and no compile
        // failure — the correct two-branch original stays).
        let mut f = top_tested_header_loop();
        let before = terminator_shape(&f, Block(1));
        let mut pass = X86BranchLayout::with_config(admit_none, X86BranchLayoutConfig::default());
        assert!(!pass.run(&mut f), "no admission => no rewrite");
        assert_eq!(terminator_shape(&f, Block(1)), before);
    }

    // =======================================================================
    // Rule 4 — cold-arm sinking
    // =======================================================================

    /// Loop containing an intra-loop diamond whose `jcc` arm (the LAYOUT
    /// successor) performs a CALL and whose `jmp` arm is call-free — the
    /// cold-arm sink shape (h2's grow-on-push diamond). Layout: b0 preheader,
    /// b1 diamond entry (`cmp; jcc E b2; jmp b3`), b2 COLD call arm
    /// (`mov; call; add; jmp b4` — exactly the 4-instruction size floor),
    /// b3 hot arm (`add; jmp b4`), b4 join + rotated latch
    /// (`cmp; jcc L b1` [+ `jmp b5`]), b5 exit.
    ///
    /// With `latch_has_exit_jmp` the latch is hard-terminated and the sink is
    /// a PURE `block_order` permutation; without it the latch reaches the
    /// exit by implicit fall-through, so the sink must materialize the seam
    /// `jmp b5` at the latch (the anchor).
    fn build_call_arm_diamond(latch_has_exit_jmp: bool) -> X86ISelFunction {
        let mut f = X86ISelFunction::new("call_arm_diamond".to_string(), empty_sig());
        let (b0, b1, b2, b3, b4, b5) = (Block(0), Block(1), Block(2), Block(3), Block(4), Block(5));
        for b in [b0, b1, b2, b3, b4, b5] {
            f.ensure_block(b);
        }
        let v0 = VReg::new(0, RegClass::Gpr64);
        let v1 = VReg::new(1, RegClass::Gpr64);
        f.next_vreg = 2;

        f.push_inst(
            b0,
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(0)],
            ),
        );
        f.push_inst(b0, jmp(b1));
        // b1: the diamond entry B — the cold arm rides the jcc (and is the
        // layout successor), the hot call-free arm rides the jmp.
        f.push_inst(
            b1,
            X86ISelInst::new(
                X86Opcode::CmpRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(3)],
            ),
        );
        f.push_inst(b1, jcc(X86CondCode::E, b2));
        f.push_inst(b1, jmp(b3));
        // b2: T — the cold call arm.
        f.push_inst(
            b2,
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![X86ISelOperand::VReg(v1), X86ISelOperand::Imm(7)],
            ),
        );
        f.push_inst(b2, X86ISelInst::new(X86Opcode::Call, vec![]));
        f.push_inst(
            b2,
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(2)],
            ),
        );
        f.push_inst(b2, jmp(b4));
        // b3: F — the kept call-free arm.
        f.push_inst(
            b3,
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(1)],
            ),
        );
        f.push_inst(b3, jmp(b4));
        // b4: join + rotated latch (back-edge already on the jcc, so the
        // latch rule leaves it alone).
        f.push_inst(
            b4,
            X86ISelInst::new(
                X86Opcode::CmpRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(10)],
            ),
        );
        f.push_inst(b4, jcc(X86CondCode::L, b1));
        if latch_has_exit_jmp {
            f.push_inst(b4, jmp(b5));
        }
        f.push_inst(b5, X86ISelInst::new(X86Opcode::Ret, vec![]));

        f.blocks.get_mut(&b0).unwrap().successors = vec![b1];
        f.blocks.get_mut(&b1).unwrap().successors = vec![b2, b3];
        f.blocks.get_mut(&b2).unwrap().successors = vec![b4];
        f.blocks.get_mut(&b3).unwrap().successors = vec![b4];
        f.blocks.get_mut(&b4).unwrap().successors = vec![b1, b5];
        f
    }

    fn intra_loop_call_arm_diamond() -> X86ISelFunction {
        build_call_arm_diamond(true)
    }

    /// Only the sink rule enabled — isolates rule 4 as the sole cause.
    fn sink_only_config() -> X86BranchLayoutConfig {
        X86BranchLayoutConfig {
            latch_rule: false,
            fallthrough_rule: false,
            cold_trap_rule: false,
            loop_exit_rule: false,
            cold_arm_sink_rule: true,
        }
    }

    /// The soak configuration: the production default plus the opted-in sink.
    fn default_plus_sink_config() -> X86BranchLayoutConfig {
        X86BranchLayoutConfig {
            cold_arm_sink_rule: true,
            ..X86BranchLayoutConfig::default()
        }
    }

    /// `(opcode, operands)` signature of every instruction of `b` — the
    /// byte-identity comparator for "the sink permutes layout but never
    /// rewrites instructions" (`X86ISelInst` does not derive `PartialEq`).
    fn inst_sigs(func: &X86ISelFunction, b: Block) -> Vec<(X86Opcode, Vec<X86ISelOperand>)> {
        func.blocks[&b]
            .insts
            .iter()
            .map(|i| (i.opcode, i.operands.clone()))
            .collect()
    }

    #[test]
    fn cold_arm_sink_moves_call_arm_out_of_line() {
        let mut f = intra_loop_call_arm_diamond();
        let sigs_before: Vec<_> = (0u32..=5).map(|i| inst_sigs(&f, Block(i))).collect();
        let succs_before: Vec<_> = (0u32..=5)
            .map(|i| f.blocks[&Block(i)].successors.clone())
            .collect();

        let mut pass = X86BranchLayout::with_config(admit_exact, default_plus_sink_config());
        assert!(pass.run(&mut f));
        assert_eq!(pass.last_run_sinks, 1);
        assert_eq!(
            pass.last_run_swaps, 0,
            "no swap rule may co-fire on the call-arm diamond"
        );

        // The call arm is out of line after the loop's last laid-out body
        // block (b4); the kept arm b3 is now b1's layout successor, so b1's
        // `jmp b3` is elided by the encoder and the hot path falls through.
        assert_eq!(
            f.block_order,
            vec![Block(0), Block(1), Block(3), Block(4), Block(2), Block(5)],
            "pure permutation: the call arm sinks past the loop span"
        );
        // Hard-terminated anchor => NOT ONE instruction changed anywhere,
        // and successor metadata is untouched everywhere.
        for i in 0u32..=5 {
            assert_eq!(
                inst_sigs(&f, Block(i)),
                sigs_before[i as usize],
                "block {i}: instructions must be byte-identical"
            );
            assert_eq!(
                f.blocks[&Block(i)].successors,
                succs_before[i as usize],
                "block {i}: successors must be untouched"
            );
        }
    }

    #[test]
    fn cold_arm_sink_declines_when_the_anchor_is_the_kept_arm() {
        // F12: an arm whose landing site is the very block it branches past
        // has not been sunk out of anything — it is swapped with its
        // neighbour and stays in the loop span. Measured on h1/h3/h4
        // (2026-08-30): that shape ADDS one in-loop `jmp` per program
        // (h3 also +32 bytes) because the encoder stops eliding a
        // fall-through the permutation made non-adjacent. Only the genuine
        // case (h2, anchor != kept) removed instructions.
        let mut f = intra_loop_call_arm_diamond();
        // Lay the latch (b4) BEFORE the diamond so the kept arm (b3) is the
        // last in-loop block after the cold arm (b2): the anchor and the kept
        // arm coincide and nothing remains to sink past. Loop membership is
        // successor-derived, so the loop is unchanged; only layout moves.
        f.block_order = vec![Block(0), Block(4), Block(1), Block(2), Block(3), Block(5)];
        let before = f.block_order.clone();
        let mut pass = X86BranchLayout::with_config(admit_exact, default_plus_sink_config());
        pass.run(&mut f);
        assert_eq!(pass.last_run_sinks, 0, "degenerate swap must not sink");
        assert_eq!(f.block_order, before, "layout must be untouched");
    }

    #[test]
    fn cold_arm_sink_is_idempotent() {
        let mut f = intra_loop_call_arm_diamond();
        let mut pass = X86BranchLayout::with_config(admit_exact, default_plus_sink_config());
        assert!(pass.run(&mut f));
        let order_after_first = f.block_order.clone();
        let entry_sigs = inst_sigs(&f, Block(1));

        // Second run: the arm is no longer B's layout successor (F2 fails
        // forever for this diamond), and no swap rule wants the post-sink
        // shape — the fixpoint terminates.
        assert!(!pass.run(&mut f), "second run must be a no-op");
        assert_eq!(pass.last_run_sinks, 0);
        assert_eq!(pass.last_run_swaps, 0);
        assert_eq!(f.block_order, order_after_first);
        assert_eq!(inst_sigs(&f, Block(1)), entry_sigs);
    }

    #[test]
    fn cold_arm_sink_requires_call_evidence() {
        // Same diamond, but the arm's call is replaced by a plain mov (still
        // at the size floor): the hotness evidence is gone and the rule must
        // decline — this is precisely what separates it from the REFUTED
        // profile-free fallthrough heuristic.
        let mut f = intra_loop_call_arm_diamond();
        f.blocks.get_mut(&Block(2)).unwrap().insts[1] = X86ISelInst::new(
            X86Opcode::MovRI,
            vec![
                X86ISelOperand::VReg(VReg::new(1, RegClass::Gpr64)),
                X86ISelOperand::Imm(9),
            ],
        );
        let order_before = f.block_order.clone();
        let mut pass = X86BranchLayout::with_config(admit_exact, default_plus_sink_config());
        assert!(!pass.run(&mut f), "no call evidence => no sink");
        assert_eq!(pass.last_run_sinks, 0);
        assert_eq!(f.block_order, order_before);
    }

    #[test]
    fn cold_arm_sink_declines_when_kept_arm_also_calls() {
        // Both arms call: no cold/hot asymmetry, no evidence — decline.
        let mut f = intra_loop_call_arm_diamond();
        f.blocks
            .get_mut(&Block(3))
            .unwrap()
            .insts
            .insert(1, X86ISelInst::new(X86Opcode::Call, vec![]));
        let order_before = f.block_order.clone();
        let mut pass = X86BranchLayout::with_config(admit_exact, default_plus_sink_config());
        assert!(!pass.run(&mut f), "kept arm calls too => no sink");
        assert_eq!(pass.last_run_sinks, 0);
        assert_eq!(f.block_order, order_before);
    }

    #[test]
    fn cold_arm_sink_declines_multi_pred_arm() {
        // Give the arm a second predecessor (the preheader branches straight
        // into it): sinking a shared block would stretch the other
        // predecessor's path — F6 must decline. Every LATER conjunct would
        // pass on this fixture, so this pins F6 as load-bearing.
        let mut f = intra_loop_call_arm_diamond();
        {
            let b0 = f.blocks.get_mut(&Block(0)).unwrap();
            b0.insts.pop(); // drop `jmp b1`
            b0.successors = vec![Block(2), Block(1)];
        }
        f.push_inst(Block(0), jcc(X86CondCode::E, Block(2)));
        f.push_inst(Block(0), jmp(Block(1)));
        let order_before = f.block_order.clone();
        let mut pass = X86BranchLayout::with_config(admit_exact, sink_only_config());
        assert!(!pass.run(&mut f), "multi-pred arm => no sink");
        assert_eq!(pass.last_run_sinks, 0);
        assert_eq!(f.block_order, order_before);
    }

    #[test]
    fn cold_arm_sink_never_disturbs_the_entry_block() {
        // Entry-first is a hard validator invariant. The sunk arm sits at
        // layout index >= 1 by construction (it is B's layout successor), so
        // the F8 `arm != entry` conjunct is structurally unreachable — kept
        // in the code as defense in depth. What must hold observably: after
        // a successful sink the entry still leads the layout and the full
        // fall-through mirror accepts the function.
        let mut f = intra_loop_call_arm_diamond();
        let mut pass = X86BranchLayout::with_config(admit_exact, sink_only_config());
        assert!(pass.run(&mut f));
        assert_eq!(pass.last_run_sinks, 1);
        assert_eq!(
            f.block_order.first(),
            Some(&Block(0)),
            "entry block stays first"
        );
        assert!(layout_fallthrough_integrity(&f).is_ok());
    }

    /// A loop laid out with its HEADER LAST — `[b0, b2, b3, b1, b5]`, b1 the
    /// header, b2 the diamond entry (which is also a LATCH: its `jmp b1` is a
    /// back-edge), b3 the call arm (also a latch via its own `jmp b1`). The
    /// diamond matches F1/F2 and carries the F9 call evidence, and every
    /// conjunct AFTER F5 would pass (single pred, in-loop jmp, size floor,
    /// body block after the arm) — so a fire here would prove F5 dead. F5
    /// must decline: B is a latch and the kept arm is the header.
    fn header_last_latch_diamond() -> X86ISelFunction {
        let mut f = X86ISelFunction::new("header_last".to_string(), empty_sig());
        let (b0, b1, b2, b3, b5) = (Block(0), Block(1), Block(2), Block(3), Block(5));
        // ensure_block order IS the layout order.
        for b in [b0, b2, b3, b1, b5] {
            f.ensure_block(b);
        }
        let v0 = VReg::new(0, RegClass::Gpr64);
        let v1 = VReg::new(1, RegClass::Gpr64);
        f.next_vreg = 2;

        f.push_inst(
            b0,
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(0)],
            ),
        );
        f.push_inst(b0, jmp(b1));
        // b2: B — diamond entry AND latch (`jmp b1` is the back-edge).
        f.push_inst(
            b2,
            X86ISelInst::new(
                X86Opcode::CmpRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(3)],
            ),
        );
        f.push_inst(b2, jcc(X86CondCode::E, b3));
        f.push_inst(b2, jmp(b1));
        // b3: the call arm (floor-sized), back to the header.
        f.push_inst(
            b3,
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![X86ISelOperand::VReg(v1), X86ISelOperand::Imm(7)],
            ),
        );
        f.push_inst(b3, X86ISelInst::new(X86Opcode::Call, vec![]));
        f.push_inst(
            b3,
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(2)],
            ),
        );
        f.push_inst(b3, jmp(b1));
        // b1: header — trip test, into the body or out to the exit.
        f.push_inst(
            b1,
            X86ISelInst::new(
                X86Opcode::CmpRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(10)],
            ),
        );
        f.push_inst(b1, jcc(X86CondCode::L, b2));
        f.push_inst(b1, jmp(b5));
        f.push_inst(b5, X86ISelInst::new(X86Opcode::Ret, vec![]));

        f.blocks.get_mut(&b0).unwrap().successors = vec![b1];
        f.blocks.get_mut(&b2).unwrap().successors = vec![b3, b1];
        f.blocks.get_mut(&b3).unwrap().successors = vec![b1];
        f.blocks.get_mut(&b1).unwrap().successors = vec![b2, b5];
        f
    }

    #[test]
    fn cold_arm_sink_declines_latch_entry_and_header_arm() {
        let mut f = header_last_latch_diamond();
        let order_before = f.block_order.clone();
        let mut pass = X86BranchLayout::with_config(admit_exact, sink_only_config());
        assert!(
            !pass.run(&mut f),
            "latch diamond entry / header kept-arm => no sink (F5)"
        );
        assert_eq!(pass.last_run_sinks, 0);
        assert_eq!(f.block_order, order_before);
    }

    #[test]
    fn cold_arm_sink_is_disjoint_from_the_loop_exit_shape() {
        // The loop-exit rule's target shape (top-tested header: the `jmp`
        // rides the loop-EXIT edge) is structurally invisible to the sink —
        // F4 requires the kept arm INSIDE the loop body, the loop-exit rule
        // requires it OUTSIDE — and a block the loop-exit rule swapped this
        // run is additionally excluded by the swapped-set gate. Pin both
        // directions.
        let mut f = top_tested_header_loop();
        let mut pass = X86BranchLayout::with_config(admit_exact, default_plus_sink_config());
        assert!(pass.run(&mut f));
        assert_eq!(pass.last_run_swaps, 1, "loop-exit rule fires");
        assert_eq!(
            pass.last_run_sinks, 0,
            "the sink must never fire on the loop-exit shape"
        );

        let mut f2 = top_tested_header_loop();
        let mut sink_pass = X86BranchLayout::with_config(admit_exact, sink_only_config());
        assert!(
            !sink_pass.run(&mut f2),
            "alone, the sink declines the loop-exit shape outright"
        );
        assert_eq!(sink_pass.last_run_sinks, 0);
    }

    #[test]
    fn cold_arm_sink_enforces_the_size_floor() {
        // Below the floor (drop the arm's add: mov; call; jmp = 3 encoded
        // instructions): decline, even with a trailing Nop — the floor counts
        // ENCODED instructions, mirroring the encoder's pseudo class.
        let mut f = intra_loop_call_arm_diamond();
        f.blocks.get_mut(&Block(2)).unwrap().insts.remove(2);
        f.push_inst(Block(2), X86ISelInst::new(X86Opcode::Nop, vec![]));
        let order_before = f.block_order.clone();
        let mut pass = X86BranchLayout::with_config(admit_exact, sink_only_config());
        assert!(!pass.run(&mut f), "below the size floor => no sink");
        assert_eq!(pass.last_run_sinks, 0);
        assert_eq!(f.block_order, order_before);

        // Positive control: the unmodified fixture sits exactly AT the floor
        // and fires — the floor is the sole decliner above.
        let mut f2 = intra_loop_call_arm_diamond();
        let mut pass2 = X86BranchLayout::with_config(admit_exact, sink_only_config());
        assert!(pass2.run(&mut f2));
        assert_eq!(pass2.last_run_sinks, 1);
    }

    #[test]
    fn cold_arm_sink_materializes_the_anchor_jmp() {
        // Latch variant WITHOUT the explicit exit jmp: the anchor (b4)
        // reaches the exit by implicit fall-through, so the sink owes the
        // seam exactly ONE materialized `jmp <old layout successor>`.
        let mut f = build_call_arm_diamond(false);
        let latch_len_before = f.blocks[&Block(4)].insts.len();
        let mut pass = X86BranchLayout::with_config(admit_exact, sink_only_config());
        assert!(pass.run(&mut f));
        assert_eq!(pass.last_run_sinks, 1);
        assert_eq!(
            f.block_order,
            vec![Block(0), Block(1), Block(3), Block(4), Block(2), Block(5)]
        );

        let latch = &f.blocks[&Block(4)].insts;
        assert_eq!(
            latch.len(),
            latch_len_before + 1,
            "exactly ONE materialized instruction"
        );
        let seam = latch.last().unwrap();
        assert_eq!(seam.opcode, X86Opcode::Jmp);
        assert_eq!(
            seam.operands,
            vec![X86ISelOperand::Block(Block(5))],
            "the seam jmp targets the anchor's OLD layout successor"
        );
        assert_eq!(
            f.blocks[&Block(4)].successors,
            vec![Block(1), Block(5)],
            "successor metadata untouched — the target was already an edge"
        );
        assert!(layout_fallthrough_integrity(&f).is_ok());
    }

    #[test]
    fn cold_arm_sink_declines_jump_table_targets_and_eh_arms() {
        // Arm referenced by a jump table: its address carries meaning beyond
        // the plain CFG — decline (F8).
        let mut f = intra_loop_call_arm_diamond();
        f.jump_tables
            .push(trust_cg_lower::x86_64_isel::X86JumpTableData {
                min_val: 0,
                targets: vec![Block(2)],
            });
        let order_before = f.block_order.clone();
        let mut pass = X86BranchLayout::with_config(admit_exact, sink_only_config());
        assert!(!pass.run(&mut f), "jump-table target arm => no sink");
        assert_eq!(f.block_order, order_before);

        // Arm that is an EH-protected call site: decline (F8).
        let mut f2 = intra_loop_call_arm_diamond();
        f2.eh_info
            .call_sites
            .push(trust_cg_lower::function::EhCallSite {
                call_block: Block(2),
                landing_pad_block: Block(5),
            });
        let order_before2 = f2.block_order.clone();
        let mut pass2 = X86BranchLayout::with_config(admit_exact, sink_only_config());
        assert!(!pass2.run(&mut f2), "EH call-site arm => no sink");
        assert_eq!(f2.block_order, order_before2);
    }

    #[test]
    fn cold_arm_sink_rolls_back_on_self_check_failure() {
        // A pre-existing layout-integrity violation OUTSIDE the loop: an
        // unreachable tail block that relies on implicit fall-through but
        // records no successor metadata. Planning cannot see it; the
        // post-move mirror must; and the sink must roll back LOSSLESSLY —
        // block_order restored and the materialized anchor jmp removed —
        // reporting no change (optimization gate, never a compile failure).
        let mut f = build_call_arm_diamond(false);
        let (b6, b7) = (Block(6), Block(7));
        f.ensure_block(b6);
        f.ensure_block(b7);
        f.push_inst(
            b6,
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![
                    X86ISelOperand::VReg(VReg::new(2, RegClass::Gpr64)),
                    X86ISelOperand::Imm(1),
                ],
            ),
        );
        f.push_inst(b7, X86ISelInst::new(X86Opcode::Ret, vec![]));
        assert!(
            layout_fallthrough_integrity(&f).is_err(),
            "fixture: the mirror must reject the corrupt tail"
        );

        let order_before = f.block_order.clone();
        let latch_sigs_before = inst_sigs(&f, Block(4));
        let mut pass = X86BranchLayout::with_config(admit_exact, sink_only_config());
        assert!(
            !pass.run(&mut f),
            "self-check failure => no change reported"
        );
        assert_eq!(pass.last_run_sinks, 0);
        assert_eq!(f.block_order, order_before, "block_order restored");
        assert_eq!(
            inst_sigs(&f, Block(4)),
            latch_sigs_before,
            "the materialized anchor jmp is rolled back"
        );
    }

    #[test]
    fn default_config_excludes_cold_arm_sink() {
        // The production default is soak-OFF: the shape that fires under the
        // opt-in must be left completely alone by the default policy.
        assert!(!X86BranchLayoutConfig::default().cold_arm_sink_rule);
        let mut f = intra_loop_call_arm_diamond();
        let order_before = f.block_order.clone();
        let mut pass = X86BranchLayout::with_config(admit_exact, X86BranchLayoutConfig::default());
        assert!(!pass.run(&mut f), "default config must not sink");
        assert_eq!(pass.last_run_sinks, 0);
        assert_eq!(f.block_order, order_before);
    }

    #[test]
    fn layout_integrity_mirror_accepts_every_fixture_and_post_sink_state() {
        // The self-check mirror must accept every well-formed fixture in this
        // module (pre-state)…
        for f in [
            diamond(),
            two_branch_latch_loop(),
            top_tested_header_loop(),
            intra_loop_diamond_loop(),
            cold_trap_diamond(),
            intra_loop_call_arm_diamond(),
            build_call_arm_diamond(false),
            header_last_latch_diamond(),
        ] {
            assert!(
                layout_fallthrough_integrity(&f).is_ok(),
                "fixture {} must satisfy the layout mirror",
                f.name
            );
        }
        // …and both post-sink states (pure permutation AND materialized seam).
        let mut permuted = intra_loop_call_arm_diamond();
        let mut pass = X86BranchLayout::with_config(admit_exact, sink_only_config());
        assert!(pass.run(&mut permuted));
        assert!(layout_fallthrough_integrity(&permuted).is_ok());

        let mut seamed = build_call_arm_diamond(false);
        let mut pass2 = X86BranchLayout::with_config(admit_exact, sink_only_config());
        assert!(pass2.run(&mut seamed));
        assert!(layout_fallthrough_integrity(&seamed).is_ok());
    }
}
